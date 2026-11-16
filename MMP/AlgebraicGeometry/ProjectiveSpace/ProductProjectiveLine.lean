module

public import MMP.AlgebraicGeometry.MMP.Models
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.Basic
import StacksFrontier.AlgebraicGeometry.Curves.ProjectiveLineCriterion.SmoothGeometricallyIntegral
import StacksFrontier.AlgebraicGeometry.WeilDeRham.TraceAxiomAlgClosedProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.ClosedImmersion

/-!
# Products with `ℙ¹`, Serre's criterion, and lifting curves

Three foundational facts used by the minimal model program.

**Products with the projective line.** Let `S` be a normal projective variety of dimension `n`
over a field `k`. Then `S × ℙ¹ = S ×_{Spec k} ℙ¹_k` is a normal projective variety of dimension
`n + 1`: it is smooth over the normal scheme `S`, hence normal; it is integral because `ℙ¹_k` is
geometrically integral; its structure morphism is the projective projection `S × ℙ¹ ⟶ S`
followed by the structure morphism of `S`; and dimensions add in products. For a projective
birational morphism `q : S ⟶ T` the square formed by `q × id` and the first projections is
cartesian, so `q × id` is a base change of `q`: it is projective, it is an open immersion over
the preimage of a dense open on which `q` is one, hence birational, and it maps `P × ℙ¹` onto
`q(P) × ℙ¹`, because points of a fibre product are given by compatible pairs and `ℙ¹_k ⟶ Spec k`
is surjective.

**Serre's criterion.** A locally Noetherian scheme is normal if and only if it satisfies `(R₁)`
and `(S₂)`.

**Lifting curves.** Let `p : W ⟶ X` be a surjective morphism of projective varieties over `k`
and `C ⊆ X` an integral curve with generic point `η`. Since `W` is a Noetherian space, the fibre
`p⁻¹(η)` has a point `w` whose closure meets the fibre only in `w`; let `Γ` be the closure of `w`
with its reduced structure. Then `Γ ⟶ X` is quasi-finite at `w`, so `κ(η) ⊆ κ(w)` is finite and
`dim Γ = trdeg_k κ(w) = trdeg_k κ(η) = 1`. Every other point of `Γ` has smaller transcendence
degree and is closed, so `Γ ⟶ C` is a proper morphism with finite fibres, hence finite; its image
is closed and contains `η`, so it is surjective.

## Main results

* `MMP.Fourfold.isNormalProjectiveVariety_product_projectiveSpace_one`: `S × ℙ¹` and `q × id`.
* `MMP.isNormal_iff_isRegularLocalRing_and_min_two_le_depth`: Serre's criterion for normality.
* `MMP.Mori.IsCurveIn.exists_isCurveIn_isFinite_surjective`: a curve lifts through a surjection
  of projective varieties, finitely and surjectively.

## Implementation notes

* `ℙ¹_k` is `Proj k[T₀, T₁]` (`AlgebraicGeometry.Proj (polyGrading k 1)`) with structure
  morphism `projToSpecCoeff k 1`, and `S × ℙ¹` is
  `pullback (S ↘ Spec (.of k)) (projToSpecCoeff k 1)`, with structure morphism
  `pullback.snd _ _ ≫ projToSpecCoeff k 1` (equal to `pullback.fst _ _ ≫ S ↘ Spec (.of k)`);
  `P × ℙ¹` is the preimage of `P` under `pullback.fst`, and `q × id` is `pullback.map` of `q`
  and `𝟙 ℙ¹`. Dimension is `topologicalKrullDim` of the underlying space.
* In Serre's criterion depth is `Module.depth` of the local ring over itself along its maximal
  ideal, and the inequality is read in `WithBot ℕ∞`, where `ringKrullDim` takes its values.
* Curves are integral closed subschemes of dimension one presented by their ideal sheaves
  (`MMP.Mori.IsCurveIn`); the restriction `Γ ⟶ C` is pinned by
  `q ≫ C.subschemeι = Γ.subschemeι ≫ p`. The source cuts the dominating component of `p⁻¹(C)`
  with general hyperplanes; here `Γ` is the closure of a point of the generic fibre that is
  closed in that fibre, and its dimension is computed through residue-field transcendence
  degrees.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori]
* [W. Fulton, *Intersection Theory*][fulton1998], §19.1
* [Stacks Project, Tag 031S](https://stacks.math.columbia.edu/tag/031S)
* [Stacks Project, Tag 033P](https://stacks.math.columbia.edu/tag/033P)
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace MMP.Fourfold

open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)

section

variable (k : Type u) [Field k]

/-- The product of a normal projective variety of dimension `n` with `ℙ¹` is a normal
projective variety of dimension `n + 1`. -/
private lemma product_projectiveSpace_one {n : ℕ} (S : Scheme.{u}) [S.Over (Spec (.of k))]
    (hS : MMP.Mori.IsNormalVariety k (S ↘ Spec (.of k)))
    (hSp : IsProjectiveVariety k (S ↘ Spec (.of k))) (hSd : topologicalKrullDim S = n) :
    MMP.Mori.IsNormalVariety k
        (pullback.snd (S ↘ Spec (.of k)) (projToSpecCoeff k 1) ≫ projToSpecCoeff k 1) ∧
      IsProjectiveVariety k
        (pullback.snd (S ↘ Spec (.of k)) (projToSpecCoeff k 1) ≫ projToSpecCoeff k 1) ∧
      topologicalKrullDim (pullback (S ↘ Spec (.of k)) (projToSpecCoeff k 1) : Scheme) =
        (n + 1 : ℕ) := by
  have hSv : AlgebraicGeometry.IsVariety k (S ↘ Spec (.of k)) := hS.1
  have : IsNormal S := hS.2
  have := hSv.toIsIntegral
  have := hSv.toLocallyOfFiniteType
  have := Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff k 1
  have : Smooth (projToSpecCoeff k 1) :=
    Stacks.AlgebraicGeometry.ProjPolyChart.smooth_projToSpecCoeff k 1
  have := isIso_globalSections_projToSpecCoeff (k := k) 1
  have : GeometricallyIntegral (projToSpecCoeff k 1) :=
    ProjectiveLineCriterion.geometricallyIntegral_of_smooth_of_isIso _
  have : QuasiCompact (S ↘ Spec (.of k)) := hSv.toQuasiCompact
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian (S ↘ Spec (.of k))
  have : IsIntegral (pullback (S ↘ Spec (.of k)) (projToSpecCoeff k 1) : Scheme) :=
    GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (pullback.fst _ _)
  have : Smooth (pullback.fst (S ↘ Spec (.of k)) (projToSpecCoeff k 1)) :=
    MorphismProperty.of_isPullback (P := @Smooth) (IsPullback.of_hasPullback _ _).flip ‹_›
  have hnorm : IsNormal (pullback (S ↘ Spec (.of k)) (projToSpecCoeff k 1) : Scheme) :=
    isNormal_of_smooth (pullback.fst (S ↘ Spec (.of k)) (projToSpecCoeff k 1))
  have hproj : AlgebraicGeometry.IsProjective
      (pullback.snd (S ↘ Spec (.of k)) (projToSpecCoeff k 1) ≫ projToSpecCoeff k 1) := by
    rw [← pullback.condition]
    exact IsProjective.comp
      (IsProjective.of_isPullback (IsPullback.of_hasPullback _ _)
        (Stacks.WeilDeRham.isProjective_projToSpecCoeff k 1))
      ((isProjectiveVariety_iff_isProjective' k _).1 hSp).2
  have := hproj.isSeparated
  have := hproj.locallyOfFiniteType
  have := hproj.quasiCompact
  have hvar : AlgebraicGeometry.IsVariety k
      (pullback.snd (S ↘ Spec (.of k)) (projToSpecCoeff k 1) ≫ projToSpecCoeff k 1) :=
    ⟨⟩
  refine ⟨⟨hvar, hnorm⟩, (isProjectiveVariety_iff_isProjective' k _).2 ⟨hvar, hproj⟩, ?_⟩
  have hP1 : topologicalKrullDim (AlgebraicGeometry.Proj (polyGrading k 1)) = 1 := by
    change topologicalKrullDim
      (AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) k)) = 1
    rw [Stacks.ProjectiveSpace.topologicalKrullDim_proj]
    simp
  rw [topologicalKrullDim_pullback k, hSd, hP1]
  push_cast
  rfl

/-- A morphism of irreducible schemes that is an open immersion on a nonempty open subset of
its source is birational. -/
private lemma isBirationalMorphism_of_isOpenImmersion {X Y : Scheme.{u}} [IrreducibleSpace X]
    [IrreducibleSpace Y] (f : X ⟶ Y) (W : X.Opens) (hW : (W : Set X).Nonempty)
    [IsOpenImmersion (W.ι ≫ f)] : MMP.Mori.IsBirationalMorphism f := by
  have hWd : Dense (W : Set X) := W.2.dense hW
  have hRd : Dense ((W.ι ≫ f).opensRange : Set Y) := by
    refine (W.ι ≫ f).opensRange.2.dense ?_
    obtain ⟨x, hx⟩ := hW
    exact ⟨_, ⟨⟨x, hx⟩, rfl⟩⟩
  refine ⟨⟨W, hWd, (W.ι ≫ f).opensRange, hRd, (W.ι ≫ f).isoOpensRange⟩, ?_⟩
  rw [Scheme.PartialIso.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨W, hWd, le_rfl, le_top, ?_⟩
  simp only [Scheme.PartialMap.restrict, Scheme.PartialIso.toPartialMap_hom,
    Scheme.Hom.toPartialMap_hom, Scheme.Hom.isoOpensRange_hom_ι]
  exact (Scheme.homOfLE_ι_assoc _ _ _).trans (Scheme.homOfLE_ι_assoc _ _ _).symm

variable {k} in
/-- The square formed by `q × id` and the first projections of `S × ℙ¹` and `T × ℙ¹` is
cartesian. -/
private lemma isPullback_pullbackMap_projToSpecCoeff {S T : Scheme.{u}} [S.Over (Spec (.of k))]
    [T.Over (Spec (.of k))] (q : S ⟶ T) [q.IsOver (Spec (.of k))] :
    IsPullback (pullback.fst (S ↘ Spec (.of k)) (projToSpecCoeff k 1))
      (pullback.map _ _ _ _ q (𝟙 _) (𝟙 _) (by simp) (by simp) :
        (pullback (S ↘ Spec (.of k)) (projToSpecCoeff k 1) : Scheme) ⟶
          (pullback (T ↘ Spec (.of k)) (projToSpecCoeff k 1) : Scheme)) q
      (pullback.fst (T ↘ Spec (.of k)) (projToSpecCoeff k 1)) := by
  refine IsPullback.of_bot (v₂₁ := pullback.snd _ _) (v₂₂ := T ↘ Spec (.of k)) ?_
    (by simp) (IsPullback.of_hasPullback _ _)
  simpa using IsPullback.of_hasPullback (S ↘ Spec (.of k)) (projToSpecCoeff k 1)

end

/-- Let `S` be a normal projective variety of dimension `n` over a field `k`. Then `S × ℙ¹_k` is
a normal projective variety of dimension `n + 1`. If `q : S ⟶ T` is a projective birational
morphism over `k` to a normal projective variety `T` of dimension `n`, then
`q × id : S × ℙ¹ ⟶ T × ℙ¹` is a projective birational morphism of normal projective varieties of
dimension `n + 1`, and it maps `P × ℙ¹` onto `q(P) × ℙ¹` for every closed irreducible
`P ⊆ S`. -/
@[mmp "lem_mmp_indexd_surface_product"]
theorem isNormalProjectiveVariety_product_projectiveSpace_one (k : Type u) [Field k]
    {n : ℕ} {S : Scheme.{u}} [S.Over (Spec (.of k))]
    (hS : MMP.Mori.IsNormalVariety k (S ↘ Spec (.of k)))
    (hSp : IsProjectiveVariety k (S ↘ Spec (.of k))) (hSd : topologicalKrullDim S = n) :
    (MMP.Mori.IsNormalVariety k
        (pullback.snd (S ↘ Spec (.of k)) (projToSpecCoeff k 1) ≫ projToSpecCoeff k 1) ∧
      IsProjectiveVariety k
        (pullback.snd (S ↘ Spec (.of k)) (projToSpecCoeff k 1) ≫ projToSpecCoeff k 1) ∧
      topologicalKrullDim (pullback (S ↘ Spec (.of k)) (projToSpecCoeff k 1) : Scheme) =
        (n + 1 : ℕ)) ∧
    ∀ {T : Scheme.{u}} [T.Over (Spec (.of k))] (q : S ⟶ T) [q.IsOver (Spec (.of k))],
      MMP.Mori.IsNormalVariety k (T ↘ Spec (.of k)) →
      IsProjectiveVariety k (T ↘ Spec (.of k)) → topologicalKrullDim T = n →
      IsProjective q → MMP.Mori.IsBirationalMorphism q →
      let Q : (pullback (S ↘ Spec (.of k)) (projToSpecCoeff k 1) : Scheme) ⟶
          (pullback (T ↘ Spec (.of k)) (projToSpecCoeff k 1) : Scheme) :=
        pullback.map _ _ _ _ q (𝟙 _) (𝟙 _) (by simp)
          ((Category.comp_id _).trans (Category.id_comp _).symm)
      (MMP.Mori.IsNormalVariety k
          (pullback.snd (T ↘ Spec (.of k)) (projToSpecCoeff k 1) ≫ projToSpecCoeff k 1) ∧
        IsProjectiveVariety k
          (pullback.snd (T ↘ Spec (.of k)) (projToSpecCoeff k 1) ≫ projToSpecCoeff k 1) ∧
        topologicalKrullDim (pullback (T ↘ Spec (.of k)) (projToSpecCoeff k 1) : Scheme) =
          (n + 1 : ℕ)) ∧
      IsProjective Q ∧ MMP.Mori.IsBirationalMorphism Q ∧
      ∀ P : Set S, IsClosed P → IsIrreducible P →
        Q '' (pullback.fst (S ↘ Spec (.of k)) (projToSpecCoeff k 1) ⁻¹' P) =
          pullback.fst (T ↘ Spec (.of k)) (projToSpecCoeff k 1) ⁻¹' (q '' P) := by
  have hSP := product_projectiveSpace_one k S hS hSp hSd
  refine ⟨hSP, ?_⟩
  intro T _ q _ hT hTp hTd hq hqb Q
  have hTP := product_projectiveSpace_one k T hT hTp hTd
  have sq := isPullback_pullbackMap_projToSpecCoeff (k := k) q
  refine ⟨hTP, IsProjective.of_isPullback sq.flip hq, ?_, ?_⟩
  · have := hSP.1.1.toIsIntegral
    have := hTP.1.1.toIsIntegral
    have : Surjective (projToSpecCoeff k 1) :=
      ⟨fun _ ↦ ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩
    obtain ⟨W, ⟨x, hx⟩, hWo⟩ := hqb.exists_isOpenImmersion
    let fS := pullback.fst (S ↘ Spec (.of k)) (projToSpecCoeff k 1)
    have h := (isPullback_morphismRestrict fS W).paste_vert sq
    have : IsOpenImmersion ((fS ⁻¹ᵁ W).ι ≫ Q) :=
      MorphismProperty.of_isPullback (P := @IsOpenImmersion) h hWo
    obtain ⟨z, hz⟩ := fS.surjective x
    exact isBirationalMorphism_of_isOpenImmersion Q (fS ⁻¹ᵁ W)
      ⟨z, show fS z ∈ W by rwa [hz]⟩
  · exact fun P _ _ ↦ Scheme.image_preimage_eq_of_isPullback sq P

end MMP.Fourfold

namespace MMP

open IsLocalRing

/-- **Serre's criterion for normality.** A locally Noetherian scheme `X` is normal if and only if
every local ring `𝒪_{X,x}` of Krull dimension at most one is a regular local ring and
`depth 𝒪_{X,x} ≥ min (2, dim 𝒪_{X,x})` for every point `x : X`. -/
@[mmp "lem_mmp_noetherian_serre_normality"]
theorem isNormal_iff_isRegularLocalRing_and_min_two_le_depth (X : Scheme)
    [IsLocallyNoetherian X] :
    IsNormal X ↔
      (∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 1 →
          IsRegularLocalRing (X.presheaf.stalk x)) ∧
        ∀ x : X, min 2 (ringKrullDim (X.presheaf.stalk x)) ≤
          (Module.depth (X.presheaf.stalk x) (maximalIdeal (X.presheaf.stalk x))
            (X.presheaf.stalk x) : WithBot ℕ∞) := by
  rw [isNormal_iff_hasPropertySk_two_and_isRegularInCodimension_one, and_comm,
    hasPropertySk_iff]
  rfl

end MMP

namespace MMP.Mori

/-- In a Noetherian `T₀` space every nonempty set `S` has a point whose closure meets `S` only
in that point. -/
private lemma exists_closure_singleton_inter_eq {α : Type*} [TopologicalSpace α]
    [NoetherianSpace α] [T0Space α] {S : Set α} (hS : S.Nonempty) :
    ∃ s ∈ S, closure {s} ∩ S = {s} := by
  obtain ⟨_, ⟨s, hs, rfl⟩, hmin⟩ := (wellFounded_lt (α := Closeds α)).has_min
    ((fun s => Closeds.closure ({s} : Set α)) '' S) (hS.image _)
  refine ⟨s, hs, Set.eq_singleton_iff_unique_mem.mpr ⟨⟨subset_closure rfl, hs⟩, ?_⟩⟩
  rintro z ⟨hz, hzS⟩
  have hle : Closeds.closure ({z} : Set α) ≤ Closeds.closure {s} := by
    change closure {z} ⊆ closure {s}
    exact closure_minimal (Set.singleton_subset_iff.mpr hz) isClosed_closure
  have heq : Closeds.closure ({z} : Set α) = Closeds.closure {s} := by
    by_contra hne
    exact hmin _ ⟨z, hzS, rfl⟩ (lt_of_le_of_ne hle hne)
  exact (inseparable_iff_closure_eq.mpr (congrArg SetLike.coe heq)).eq

/-- In a Noetherian quasi-sober space a closed set all of whose points are closed is finite. -/
private lemma finite_of_isClosed_of_forall_isClosed_singleton {α : Type*} [TopologicalSpace α]
    [NoetherianSpace α] [QuasiSober α] {s : Set α} (hs : IsClosed s)
    (h : ∀ x ∈ s, IsClosed ({x} : Set α)) : s.Finite := by
  obtain ⟨T, hT, hTc, hTi, rfl⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hs
  refine hT.sUnion fun t ht => ?_
  have hg := (hTi t ht).isGenericPoint_genericPoint_closure
  rw [(hTc t ht).closure_eq] at hg
  have hmem : (hTi t ht).genericPoint ∈ t := hg.mem
  have hcl := h _ (Set.mem_sUnion_of_mem hmem ht)
  rw [← hg.def, hcl.closure_eq]
  exact Set.finite_singleton _

/-- Along a morphism with integral residue field extension at a point, the transcendence
degree over a base field does not grow. -/
private lemma trdeg_residueField_le_of_isIntegral (K : Type u) [Field K] {X W : Scheme.{u}}
    (gX : X ⟶ Spec (.of K)) (i : W ⟶ X) (w : W) (hw : (i.residueFieldMap w).hom.IsIntegral) :
    letI : Algebra K (X.residueField (i w)) :=
      ((Scheme.ΓSpecIso (.of K)).inv ≫ gX.appTop ≫ X.Γevaluation (i w)).hom.toAlgebra
    letI : Algebra K (W.residueField w) :=
      ((Scheme.ΓSpecIso (.of K)).inv ≫ (i ≫ gX).appTop ≫ W.Γevaluation w).hom.toAlgebra
    Algebra.trdeg K (W.residueField w) ≤ Algebra.trdeg K (X.residueField (i w)) := by
  let : Algebra K (X.residueField (i w)) :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ gX.appTop ≫ X.Γevaluation (i w)).hom.toAlgebra
  let : Algebra K (W.residueField w) :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ (i ≫ gX).appTop ≫ W.Γevaluation w).hom.toAlgebra
  let : Algebra (X.residueField (i w)) (W.residueField w) := (i.residueFieldMap w).hom.toAlgebra
  have : IsScalarTower K (X.residueField (i w)) (W.residueField w) := by
    apply IsScalarTower.of_algebraMap_eq'
    change ((Scheme.ΓSpecIso (.of K)).inv ≫ (i ≫ gX).appTop ≫ W.Γevaluation w).hom =
      (i.residueFieldMap w).hom.comp
        ((Scheme.ΓSpecIso (.of K)).inv ≫ gX.appTop ≫ X.Γevaluation (i w)).hom
    have hcat : (Scheme.ΓSpecIso (.of K)).inv ≫ (i ≫ gX).appTop ≫ W.Γevaluation w =
        (Scheme.ΓSpecIso (.of K)).inv ≫ gX.appTop ≫ X.Γevaluation (i w) ≫
          i.residueFieldMap w := by
      rw [Scheme.Hom.comp_appTop, Category.assoc, Scheme.Γevaluation_naturality i w]
    simpa [CommRingCat.hom_comp, RingHom.comp_assoc] using congrArg CommRingCat.Hom.hom hcat
  have : Algebra.IsIntegral (X.residueField (i w)) (W.residueField w) := ⟨hw⟩
  have : Algebra.IsAlgebraic (X.residueField (i w)) (W.residueField w) :=
    Algebra.IsIntegral.isAlgebraic
  have : FaithfulSMul K (X.residueField (i w)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (RingHom.injective (algebraMap K (X.residueField (i w))))
  have : FaithfulSMul (X.residueField (i w)) (W.residueField w) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (RingHom.injective (algebraMap (X.residueField (i w)) (W.residueField w)))
  have h := trdeg_add_eq (R := K) (S := X.residueField (i w)) (A := W.residueField w)
  rw [trdeg_eq_zero (R := X.residueField (i w)) (A := W.residueField w), add_zero] at h
  exact h.symm.le

/-- The dimension of the closure of a point of a scheme locally of finite type over a field is
the transcendence degree of its residue field. -/
private lemma topologicalKrullDim_closure_singleton_eq_natTrdeg (K : Type u) [Field K]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] (x : X) :
    topologicalKrullDim (closure {x} : Set X) = natTrdegResidueField K X f x := by
  let : Algebra K (X.residueField x) :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
  have := residueField_finTrdeg K f x
  rw [topologicalKrullDim_closure_singleton_eq_trdeg K X f x, natTrdegResidueField]
  obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.mp (trdeg_lt_aleph0 K (X.residueField x))
  simp [hn]

/-- An irreducible scheme over `X` that is quasi-finite at its generic point `y` has dimension
at most the transcendence degree of the residue field at the image of `y`. -/
private lemma topologicalKrullDim_le_natTrdeg_of_quasiFiniteAt (K : Type u) [Field K]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of K)) [LocallyOfFiniteType sX] (f : Y ⟶ X)
    [LocallyOfFiniteType f] [IrreducibleSpace Y] {y : Y} (hy : IsGenericPoint y Set.univ)
    (hf : f.QuasiFiniteAt y) :
    topologicalKrullDim Y ≤ natTrdegResidueField K X sX (f y) := by
  set U := f.quasiFiniteLocus
  have hyU : y ∈ U := Scheme.Hom.mem_quasiFiniteLocus.mpr hf
  let u : U.toScheme := ⟨y, hyU⟩
  let g : U.toScheme ⟶ X := U.ι ≫ f
  have hint : (g.residueFieldMap u).hom.IsIntegral := by
    let := (g.residueFieldMap u).hom.toAlgebra
    have := residueField_module_finite_of_locallyQuasiFinite g u
    exact (Algebra.IsIntegral.of_finite (X.residueField (g u)) _).isIntegral
  have hgen : IsGenericPoint u (Set.univ : Set U.toScheme) := by
    rw [isGenericPoint_iff_specializes]
    intro z
    simp only [Set.mem_univ, iff_true]
    rw [← U.ι.isEmbedding.isInducing.specializes_iff]
    exact (isGenericPoint_iff_specializes.mp hy _).mpr trivial
  have : IrreducibleSpace U.toScheme := by
    rw [irreducibleSpace_def]
    exact hgen.isIrreducible
  let : Algebra K (X.residueField (g u)) :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ sX.appTop ≫ X.Γevaluation (g u)).hom.toAlgebra
  have := residueField_finTrdeg K sX (g u)
  obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.mp (trdeg_lt_aleph0 K (X.residueField (g u)))
  have hle := trdeg_residueField_le_of_isIntegral K sX g u hint
  rw [topologicalKrullDim_eq_of_isOpen K Y (f ≫ sX) U U.isOpen ⟨y, hyU⟩,
    show topologicalKrullDim (U : Set Y) = topologicalKrullDim U.toScheme from rfl,
    topologicalKrullDim_eq_trdeg_residueField K U.toScheme (g ≫ sX) u hgen]
  change _ ≤ ((Cardinal.toNat (Algebra.trdeg K (X.residueField (g u))) : ℕ∞) : WithBot ℕ∞)
  rw [hn] at hle ⊢
  exact WithBot.coe_le_coe.mpr (by simpa using Cardinal.toENat.monotone' hle)

/-- A point of a closed subscheme is closed as soon as it is closed in the ambient scheme. -/
private lemma isClosed_singleton_of_isClosed_val {X : Scheme.{u}} {Z : X.IdealSheafData}
    {x : Z.subscheme} (h : IsClosed ({x.1} : Set X)) : IsClosed ({x} : Set Z.subscheme) := by
  have : ({x} : Set Z.subscheme) = Z.subschemeι ⁻¹' {x.1} := by
    ext y
    simp only [Set.mem_singleton_iff, Set.mem_preimage, Scheme.IdealSheafData.subschemeι_apply]
    exact ⟨fun h => h ▸ rfl, Subtype.ext⟩
  rw [this]
  exact h.preimage Z.subschemeι.continuous

/-- A curve has a generic point, and its residue field has transcendence degree one. -/
private lemma IsCurveIn.exists_isGenericPoint {K : Type u} [Field K] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of K)) [LocallyOfFiniteType sX] {C : X.IdealSheafData} (hC : IsCurveIn C) :
    ∃ η, IsGenericPoint η (C.support : Set X) ∧ natTrdegResidueField K X sX η = 1 := by
  obtain ⟨_, hCdim⟩ := hC
  have hCirr : IsIrreducible (C.support : Set X) := by
    simpa [Set.image_univ, C.range_subschemeι] using
      (IrreducibleSpace.isIrreducible_univ C.subscheme).image C.subschemeι
        C.subschemeι.continuous.continuousOn
  have hη := hCirr.isGenericPoint_genericPoint_closure
  rw [C.support.isClosed.closure_eq] at hη
  refine ⟨_, hη, ?_⟩
  have h := topologicalKrullDim_closure_singleton_eq_natTrdeg K X sX hCirr.genericPoint
  rw [hη.def, show topologicalKrullDim (C.support : Set X) = 1 from hCdim] at h
  exact_mod_cast h.symm

/-- A scheme quasi-compact and locally of finite type over a field is Noetherian. -/
private lemma isNoetherian_of_locallyOfFiniteType {K : Type u} [Field K] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of K)) [LocallyOfFiniteType s] [QuasiCompact s] : IsNoetherian X :=
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  ⟨⟩

/-- The reduced closed subscheme on the closure of a point is integral. -/
private lemma isIntegral_subscheme_vanishingIdeal_closure {X : Scheme.{u}} (x : X) :
    IsIntegral (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {x})).subscheme := by
  have hZ : ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {x})).support : Set X) =
      closure {x} := Scheme.IdealSheafData.coe_support_vanishingIdeal _
  have := Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal (Closeds.closure {x})
  have : IrreducibleSpace (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {x})).subscheme :=
    Subtype.irreducibleSpace (by rw [hZ]; exact isIrreducible_singleton.closure)
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- The closure of a point `w` maps into a closed subscheme `C` whose generic point is `p w`. -/
private lemma le_ker_subschemeι_comp {W X : Scheme.{u}} (p : W ⟶ X) {C : X.IdealSheafData}
    {w : W} (hw : IsGenericPoint (p w) (C.support : Set X)) :
    C ≤ ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {w})).subschemeι ≫ p).ker := by
  change C ≤ (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {w})).map p
  rw [Scheme.IdealSheafData.map_vanishingIdeal,
    ← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal, Closeds.closure_le]
  rintro _ ⟨x, hx, rfl⟩
  have hx' : p x ∈ closure {p w} := by
    have := image_closure_subset_closure_image p.continuous ⟨x, hx, rfl⟩
    rwa [Set.image_singleton] at this
  rwa [hw.def] at hx'

/-- A morphism is quasi-finite at a point that is the only point of its fibre. -/
private lemma quasiFiniteAt_of_forall_eq {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (x : X) (h : ∀ a, f a = f x → a = x) : f.QuasiFiniteAt x := by
  rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber]
  have : Subsingleton (f.fiber (f x)) := ⟨fun a b => (f.fiberHomeo (f x)).injective <|
    Subtype.ext <| (h _ (f.fiberHomeo (f x) a).2).trans (h _ (f.fiberHomeo (f x) b).2).symm⟩
  rw [show ({f.asFiber x} : Set (f.fiber (f x))) = Set.univ from
    Set.eq_univ_of_forall fun b => Subsingleton.elim b _]
  exact isOpen_univ

/-- A point is the generic point of the closed subscheme supported on its closure. -/
private lemma isGenericPoint_univ_of_support_eq {X : Scheme.{u}} {Z : X.IdealSheafData}
    (z : Z.subscheme) (hZ : (Z.support : Set X) = closure {z.1}) :
    IsGenericPoint z (Set.univ : Set Z.subscheme) := by
  rw [isGenericPoint_iff_specializes]
  intro y
  simp only [Set.mem_univ, iff_true]
  rw [← Z.subschemeι.isEmbedding.isInducing.specializes_iff]
  exact specializes_iff_mem_closure.mpr (hZ ▸ y.2)

/-- The closed subscheme supported on the closure of a point has dimension the transcendence
degree of that point. -/
private lemma topologicalKrullDim_subscheme_eq_natTrdeg {K : Type u} [Field K] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of K)) [LocallyOfFiniteType s] {Z : X.IdealSheafData} (z : Z.subscheme)
    (hZ : (Z.support : Set X) = closure {z.1}) :
    topologicalKrullDim Z.subscheme = natTrdegResidueField K X s z.1 := by
  rw [← topologicalKrullDim_closure_singleton_eq_natTrdeg, ← hZ]
  rfl

/-- If the closed subscheme on the closure of `w` maps to `X` quasi-finitely at `w`, the
transcendence degree at `w` is at most that at its image. -/
private lemma natTrdegResidueField_le_of_quasiFiniteAt {K : Type u} [Field K] {W X : Scheme.{u}}
    (sW : W ⟶ Spec (.of K)) (sX : X ⟶ Spec (.of K)) [LocallyOfFiniteType sW]
    [LocallyOfFiniteType sX] (p : W ⟶ X) [LocallyOfFiniteType p] {Z : W.IdealSheafData}
    [IrreducibleSpace Z.subscheme] (w : Z.subscheme) (hZ : (Z.support : Set W) = closure {w.1})
    (hp : (Z.subschemeι ≫ p).QuasiFiniteAt w) :
    natTrdegResidueField K W sW w.1 ≤ natTrdegResidueField K X sX (p w.1) := by
  have h := topologicalKrullDim_le_natTrdeg_of_quasiFiniteAt K sX _
    (isGenericPoint_univ_of_support_eq w hZ) hp
  rw [topologicalKrullDim_subscheme_eq_natTrdeg sW w hZ] at h
  exact_mod_cast h

/-- If `p w` has positive transcendence degree and `p` is a closed map, so has `w`. -/
private lemma natTrdegResidueField_ne_zero_of_isClosedMap {K : Type u} [Field K]
    {W X : Scheme.{u}} (sW : W ⟶ Spec (.of K)) (sX : X ⟶ Spec (.of K)) [LocallyOfFiniteType sW]
    [LocallyOfFiniteType sX] (p : W ⟶ X) (hp : IsClosedMap p) {w : W}
    (h : natTrdegResidueField K X sX (p w) ≠ 0) : natTrdegResidueField K W sW w ≠ 0 := fun h0 => by
  have hcl := hp _ (isClosed_singleton_of_natTrdegResidueField_eq_zero K W sW w h0)
  rw [Set.image_singleton] at hcl
  exact h (natTrdegResidueField_eq_zero_of_isClosed K X sX _ hcl)

/-- In a closed subscheme whose generic point has residue-field transcendence degree one, every
other point is closed. -/
private lemma isClosed_singleton_of_ne_genericPoint {K : Type u} [Field K] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of K)) [LocallyOfFiniteType s] {Z : X.IdealSheafData} {η : X}
    (hη : IsGenericPoint η (Z.support : Set X)) (h1 : natTrdegResidueField K X s η = 1)
    {z : Z.subscheme} (hz : z.1 ≠ η) : IsClosed ({z} : Set Z.subscheme) :=
  isClosed_singleton_of_isClosed_val <| by
    apply isClosed_singleton_of_natTrdegResidueField_eq_zero K X s
    have := natTrdegResidueField_lt_of_specializes K X s
      (specializes_iff_mem_closure.mpr (hη.def ▸ z.2)) (fun h => hz h.symm)
    omega

/-- A proper morphism from a Noetherian scheme is finite and surjective when the image of a
point `y` is generic, `y` is the whole fibre over it, and every other point of the source and
of the target is closed. -/
private lemma isFinite_surjective_of_isGenericPoint {Y Z : Scheme.{u}} [IsNoetherian Y]
    (q : Y ⟶ Z) [IsProper q] (y : Y) (hfib : ∀ x, q x = q y → x = y)
    (hY : ∀ x, x ≠ y → IsClosed ({x} : Set Y)) (hZ : ∀ z, z ≠ q y → IsClosed ({z} : Set Z))
    (hgen : IsGenericPoint (q y) Set.univ) : IsFinite q ∧ Surjective q := by
  have : LocallyQuasiFinite q := by
    rw [locallyQuasiFinite_iff_finite_preimage_singleton]
    intro z
    by_cases hz : z = q y
    · subst hz
      exact (Set.finite_singleton y).subset fun x hx => hfib x hx
    · refine finite_of_isClosed_of_forall_isClosed_singleton ((hZ z hz).preimage q.continuous)
        fun x (hx : q x = z) => hY x ?_
      rintro rfl
      exact hz hx.symm
  refine ⟨IsFinite.of_isProper_of_locallyQuasiFinite q, ⟨fun z => ?_⟩⟩
  exact q.isClosedMap.isClosed_range.closure_subset_iff.mpr
    (Set.singleton_subset_iff.mpr ⟨y, rfl⟩)
    (specializes_iff_mem_closure.mp (hgen.specializes (Set.mem_univ z)))

/-- Let `p : W ⟶ X` be a surjective morphism of projective varieties over `k` and `C ⊆ X` an
integral curve. Then there is an integral curve `Γ ⊆ W` and a finite surjective morphism
`q : Γ ⟶ C` with `q ≫ C.subschemeι = Γ.subschemeι ≫ p`. -/
@[mmp "lem_mmp_projective_surjection_lifts_curve"]
theorem IsCurveIn.exists_isCurveIn_isFinite_surjective {k : Type u} [Field k]
    {W X : Scheme.{u}} {sW : W ⟶ Spec (.of k)} {sX : X ⟶ Spec (.of k)}
    (hW : MMP.Mori.IsProjectiveVariety k sW) (hX : MMP.Mori.IsProjectiveVariety k sX)
    (p : W ⟶ X) (hpk : p ≫ sX = sW) [Surjective p] {C : X.IdealSheafData} (hC : IsCurveIn C) :
    ∃ (Γ : W.IdealSheafData) (q : Γ.subscheme ⟶ C.subscheme),
      IsCurveIn Γ ∧ q ≫ C.subschemeι = Γ.subschemeι ≫ p ∧ IsFinite q ∧ Surjective q := by
  have : IsVariety k sW := hW.toIsVariety
  have : IsVariety k sX := hX.toIsVariety
  have : IsProper sW := isProper_of_isProjectiveMorphism sW hW.isProjective
  have : IsProper (p ≫ sX) := hpk ▸ inferInstance
  have : IsProper p := IsProper.of_comp p sX
  have := isNoetherian_of_locallyOfFiniteType sW
  obtain ⟨η, hη, hηnat⟩ := IsCurveIn.exists_isGenericPoint sX hC
  obtain ⟨w, hpw, hwmin⟩ := exists_closure_singleton_inter_eq (S := p ⁻¹' {η}) (p.surjective η)
  obtain rfl : p w = η := hpw
  set Γ : W.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {w})
  have hΓsupp : (Γ.support : Set W) = closure {w} :=
    Scheme.IdealSheafData.coe_support_vanishingIdeal _
  have hΓgen : IsGenericPoint w (Γ.support : Set W) := hΓsupp ▸ isGenericPoint_closure
  have : IsIntegral Γ.subscheme := isIntegral_subscheme_vanishingIdeal_closure w
  have := isNoetherian_of_locallyOfFiniteType (Γ.subschemeι ≫ sW)
  let w' : Γ.subscheme := ⟨w, hΓgen.mem⟩
  let f : Γ.subscheme ⟶ X := Γ.subschemeι ≫ p
  let q : Γ.subscheme ⟶ C.subscheme :=
    f.toImage ≫ Scheme.IdealSheafData.inclusion (le_ker_subschemeι_comp p hη : C ≤ f.ker)
  have hq : q ≫ C.subschemeι = Γ.subschemeι ≫ p := by
    simp only [q, Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]
    exact f.toImage_imageι
  have hqx : ∀ x : Γ.subscheme, (q x).1 = p x.1 := fun x => by
    simpa only [Scheme.Hom.comp_apply, Scheme.IdealSheafData.subschemeι_apply] using
      congrArg (fun φ => φ x) hq
  have hqw : (q w').1 = p w := hqx w'
  have hfib : ∀ x : Γ.subscheme, p x.1 = p w → x = w' := fun x hx => by
    have hx₁ : x.1 ∈ closure {w} ∩ p ⁻¹' {p w} := ⟨hΓsupp ▸ x.2, hx⟩
    rw [hwmin] at hx₁
    exact Subtype.ext hx₁
  have hwnat : natTrdegResidueField k W sW w = 1 := by
    have h₁ : natTrdegResidueField k W sW w ≤ natTrdegResidueField k X sX (p w) :=
      natTrdegResidueField_le_of_quasiFiniteAt sW sX p w' hΓsupp
        (quasiFiniteAt_of_forall_eq f w' hfib)
    have := natTrdegResidueField_ne_zero_of_isClosedMap sW sX p p.isClosedMap (w := w) (by omega)
    omega
  have : IsProper (q ≫ C.subschemeι) := hq ▸ inferInstance
  have : IsProper q := IsProper.of_comp q C.subschemeι
  obtain ⟨_, hqs⟩ := isFinite_surjective_of_isGenericPoint q w'
    (fun x hx => hfib x ((hqx x).symm.trans ((congrArg Subtype.val hx).trans hqw)))
    (fun x hx => isClosed_singleton_of_ne_genericPoint sW hΓgen hwnat
      fun h => hx (Subtype.ext h))
    (fun c hc => isClosed_singleton_of_ne_genericPoint sX hη hηnat
      fun h => hc (Subtype.ext (h.trans hqw.symm)))
    (isGenericPoint_univ_of_support_eq (q w') (by rw [hqw, hη.def]))
  refine ⟨Γ, q, ⟨inferInstance, ?_⟩, hq, inferInstance, hqs⟩
  rw [topologicalKrullDim_subscheme_eq_natTrdeg sW w' hΓsupp, hwnat]
  rfl

end MMP.Mori

end
