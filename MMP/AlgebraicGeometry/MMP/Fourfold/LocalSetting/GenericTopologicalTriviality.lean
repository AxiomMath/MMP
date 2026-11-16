module
import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.AffineSpaceBundleSmooth

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Analytic.IsolatedPointLink
public import MMP.AlgebraicGeometry.Resolution.BlowupSequence
public import MMP.AlgebraicGeometry.MMP.Fourfold.PuncturedLocalSystem
import MMP.AlgebraicGeometry.MMP.Fourfold.LocalSetting.GenericRelativeSNCResolution
import MMP.AlgebraicGeometry.Analytic.SchemeManifoldSlice
import MMP.AlgebraicGeometry.Resolution.BlowupSequence.PushforwardSmooth
import MMP.AlgebraicGeometry.Analytic.AnalyticMapOpenSubscheme
public import MMP.AlgebraicGeometry.Chow.FieldSituation
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme

/-!
# Generic topological triviality along a singular curve

Let `(Y, Θ, T, π)` be a local setting (`MMP.Fourfold.IsLocalSetting`). Over a Zariski open
`X ⊆ Y` meeting `T`, the curve `T° = T ∩ X` is smooth and finite étale over a smooth curve `B`
through a morphism `t : X ⟶ B`, and the resolution `π`, followed by finitely many blow-ups of
smooth varieties along smooth centres, gives a smooth projective `f : Z ⟶ X`, an isomorphism off
`T°`. Analytically, `f` is a topological product over small disks `W ⊆ T°`, the pair `(X, T°)`
is locally the product of a slice `(X_b, {x})` with a disk, and every point of `T°` over
`b ∈ B(ℂ)` is an isolated point of `S_b = (P_b ∖ X_b) ∪ T_b` in the closure `P_b` of the slice,
in the sense of `MMP.Fourfold.exists_cofinal_isIso_punctured_cohomology_of_isolated`.

## Main results

* `MMP.Fourfold.IsLocalSetting.exists_generic_trivializations`.

## Implementation notes

* The analytic space of a scheme `S` over `ℂ` is its complex realization
  `MMP.Analytic.ComplexPoints`; `X`, `T°` and `Z` are `ℂ`-schemes through `X ↪ Y`, `T° ↪ X` and
  `f`, and the realized maps are `MMP.Analytic.ComplexPoints.analyticMap`.
* `T°` is the open `T ∩ X` of the reduced curve `MMP.Fourfold.curveScheme T`, mapping to `X` by
  the restriction of `T ↪ Y`. Its smoothness is `T° ≤ smoothLocus T`.
* `β` is a `MMP.Resolution.ClosedBlowupSequence` on `π⁻¹(X)` which is smooth
  (`MMP.Resolution.ClosedBlowupSequence.IsSmooth`): every scheme and every centre is smooth over
  `ℂ`. Then `Z` is its last scheme and `f = π_X ∘ β`.
* An open disk is `Metric.ball (0 : ℂ) 1`; every open disk is homeomorphic to it. A slice is
  `X_b = t⁻¹(b)` for a `ℂ`-point `b` of `B`, an open of the slice being the trace of an open of
  `X^an`. The reduced closure `P_b` of `X_b` is the closed subscheme of `Y` cut out by the
  vanishing ideal of the Zariski closure of `X_b`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][kollarmori1998]
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace
open MMP.Fourfold MMP.Mori MMP.Analytic MMP.Analytic.ComplexPoints MMP.Resolution

namespace MMP.Fourfold.GenericTopologicalTriviality

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open Scheme.IdealSheafData in
/-- The kernel of a morphism out of a reduced scheme is the vanishing ideal of the closure of its
range. -/
private lemma ker_eq_vanishingIdeal_closure_range {X Y : Scheme.{0}} [IsReduced X] (f : X ⟶ Y) :
    f.ker = vanishingIdeal ⟨closure (Set.range f), isClosed_closure⟩ := by
  rw [← Scheme.IdealSheafData.map_bot, ← Scheme.nilradical_eq_bot,
    ← vanishingIdeal_top, map_vanishingIdeal]
  congr 1
  ext1
  simp

open Scheme.IdealSheafData in
/-- The trace on an open `X` of the reduced closed subscheme on `Z` is the reduced closed
subscheme of `X` on `X ∩ Z`. -/
private lemma exists_iso_restrict_subschemeι_vanishingIdeal {Y : Scheme.{0}} (Z : Closeds Y)
    (X : Y.Opens) :
    ∃ e : ((vanishingIdeal Z).subschemeι ⁻¹ᵁ X : Scheme.{0}) ≅
      (vanishingIdeal (⟨X.ι ⁻¹' Z, Z.isClosed.preimage X.ι.continuous⟩ :
        Closeds (X : Scheme.{0}))).subscheme,
      e.hom ≫ (vanishingIdeal (⟨X.ι ⁻¹' Z, Z.isClosed.preimage X.ι.continuous⟩ :
        Closeds (X : Scheme.{0}))).subschemeι = (vanishingIdeal Z).subschemeι ∣_ X := by
  set i := (vanishingIdeal Z).subschemeι ∣_ X
  set j := (vanishingIdeal (⟨X.ι ⁻¹' Z, Z.isClosed.preimage X.ι.continuous⟩ :
        Closeds (X : Scheme.{0}))).subschemeι
  have hker : i.ker = j.ker := by
    rw [ker_subschemeι, ker_eq_vanishingIdeal_closure_range]
    congr 1
    ext1
    simp only [Closeds.coe_mk, i]
    rw [range_morphismRestrict, range_subschemeι, coe_support_vanishingIdeal,
      IsClosed.closure_eq (Z.isClosed.preimage X.ι.continuous)]
  have := IsClosedImmersion.isIso_lift j i hker.symm
  exact ⟨asIso (IsClosedImmersion.lift j i hker.ge), IsClosedImmersion.lift_fac _ _ _⟩

/-- The affine line over `ℂ` is smooth of relative dimension one. -/
private lemma smoothOfRelativeDimension_affineLine :
    SmoothOfRelativeDimension 1 (𝔸(Unit; Spec (.of ℂ)) ↘ Spec (.of ℂ)) := by
  have := Stacks.Chow.smoothOfRelativeDimension_affineSpaceOver (Spec (.of ℂ)) 1
  let i : ULift.{0} (Fin 1) ⟶ Unit := TypeCat.ofHom fun _ ↦ ()
  let j : Unit ⟶ ULift.{0} (Fin 1) := TypeCat.ofHom fun _ ↦ ⟨0⟩
  have hij : AffineSpace.reindex i (Spec (.of ℂ)) ≫ AffineSpace.reindex j (Spec (.of ℂ)) =
      𝟙 _ := by
    rw [← AffineSpace.reindex_comp]
    exact AffineSpace.reindex_id (S := Spec (.of ℂ)) (n := Unit)
  have hji : AffineSpace.reindex j (Spec (.of ℂ)) ≫ AffineSpace.reindex i (Spec (.of ℂ)) =
      𝟙 _ := by
    rw [← AffineSpace.reindex_comp]
    convert AffineSpace.reindex_id (S := Spec (.of ℂ)) (n := ULift.{0} (Fin 1))
    funext x; exact Subsingleton.elim _ _
  have : IsIso (AffineSpace.reindex i (Spec (.of ℂ))) := ⟨_, hij, hji⟩
  rw [← AffineSpace.reindex_over i]
  simpa using (inferInstance : SmoothOfRelativeDimension (0 + 1)
    (AffineSpace.reindex i (Spec (.of ℂ)) ≫ 𝔸(ULift.{0} (Fin 1); Spec (.of ℂ)) ↘ Spec (.of ℂ)))

/-- An open of the affine line over `ℂ` is smooth of relative dimension one. -/
private lemma smoothOfRelativeDimension_opens_affineLine (B : (𝔸(Unit; Spec (.of ℂ))).Opens) :
    SmoothOfRelativeDimension 1 (B.ι ≫ (𝔸(Unit; Spec (.of ℂ)) ↘ Spec (.of ℂ))) := by
  have := smoothOfRelativeDimension_affineLine
  simpa using (inferInstance : SmoothOfRelativeDimension (0 + 1)
    (B.ι ≫ (𝔸(Unit; Spec (.of ℂ)) ↘ Spec (.of ℂ))))

/-- A nonempty open of the affine line over `ℂ` is a smooth curve. -/
private lemma isVariety_isSmoothScheme_opens_affineLine (B : (𝔸(Unit; Spec (.of ℂ))).Opens)
    [Nonempty B] :
    MMP.Mori.IsVariety ℂ (B.ι ≫ (𝔸(Unit; Spec (.of ℂ)) ↘ Spec (.of ℂ))) ∧
      IsSmoothScheme (B.ι ≫ (𝔸(Unit; Spec (.of ℂ)) ↘ Spec (.of ℂ))) ∧
      topologicalKrullDim B = 1 := by
  have : IsLocallyNoetherian 𝔸(Unit; Spec (.of ℂ)) :=
    LocallyOfFiniteType.isLocallyNoetherian (𝔸(Unit; Spec (.of ℂ)) ↘ Spec (.of ℂ))
  have : CompactSpace 𝔸(Unit; Spec (.of ℂ)) := Scheme.compactSpace_of_isAffine _
  have := smoothOfRelativeDimension_opens_affineLine B
  refine ⟨(isVariety_iff ℂ _).2 ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩,
    MMP.Mori.isSmoothScheme_of_smooth (SmoothOfRelativeDimension.smooth 1 _), ?_⟩
  exact_mod_cast topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field 1
    (B.ι ≫ (𝔸(Unit; Spec (.of ℂ)) ↘ Spec (.of ℂ)))

/-- The source of a smooth resolution of an integral scheme over `ℂ` is integral. -/
private lemma isIntegral_of_isSmoothResolution {X Z : Scheme.{0}} [IsIntegral X]
    {sX : X ⟶ Spec (.of ℂ)} {f : Z ⟶ X} (hf : IsSmoothResolution sX f) : IsIntegral Z := by
  have : Smooth (f ≫ sX) := hf.isSmoothScheme.smooth
  have : IsReduced Z := by
    have : ∀ x : Z, _root_.IsReduced (Z.presheaf.stalk x) := fun x ↦ by
      have := isRegularLocalRing_stalk_of_smooth_over_field (f ≫ sX) x
      have := IsRegularLocalRing.isDomain (Z.presheaf.stalk x)
      infer_instance
    exact isReduced_of_isReduced_stalk Z
  obtain ⟨e, -⟩ := hf.isBirationalMorphism
  have : Nonempty e.target := by
    obtain ⟨x, hx⟩ := e.dense_target.nonempty
    exact ⟨⟨x, hx⟩⟩
  have : IrreducibleSpace e.source :=
    (Homeomorph.irreducibleSpace_iff (Scheme.homeoOfIso e.iso).symm).mp inferInstance
  have hirr : IsIrreducible (e.source : Set Z) := isIrreducible_iff_irreducibleSpace.mpr ‹_›
  have : IrreducibleSpace Z := by
    have := hirr.closure
    rw [e.dense_source.closure_eq] at this
    exact (irreducibleSpace_def Z).2 this
  exact isIntegral_of_irreducibleSpace_of_isReduced Z

/-- If `f : Z ⟶ X` restricts to an isomorphism over an open `V` of an open `X ⊆ Y` and `Z` is
smooth over the base, then `V` lies in the smooth locus of `Y`. -/
private lemma mem_smoothLocus_of_isIso_restrict {Y Z S : Scheme.{0}} {sY : Y ⟶ S} (X : Y.Opens)
    (f : Z ⟶ X) (hZ : Smooth (f ≫ X.ι ≫ sY)) (V : (X : Scheme.{0}).Opens) [IsIso (f ∣_ V)]
    {y : X} (hy : y ∈ V) : X.ι y ∈ smoothLocus sY := by
  have hV : Smooth (V.ι ≫ X.ι ≫ sY) := by
    have : V.ι = inv (f ∣_ V) ≫ (f ⁻¹ᵁ V).ι ≫ f := by
      rw [← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
    rw [this, Category.assoc, Category.assoc]
    infer_instance
  have hU : Smooth ((X.ι ''ᵁ V).ι ≫ sY) := by
    have : (X.ι ''ᵁ V).ι = (X.ι.isoImage V).inv ≫ V.ι ≫ X.ι := by
      rw [Iso.eq_inv_comp, Scheme.Hom.isoImage_hom_ι]
    rw [this, Category.assoc, Category.assoc]
    infer_instance
  exact le_smoothLocus sY hU ⟨y, hy, rfl⟩

/-- In a space charted on `ℂ`, every neighbourhood of a point contains an open neighbourhood
homeomorphic to the unit disk. -/
private lemma exists_isOpen_homeomorph_ball_subset {M : Type*} [TopologicalSpace M]
    [ChartedSpace ℂ M] (b : M) {N : Set M} (hN : N ∈ 𝓝 b) :
    ∃ D ⊆ N, IsOpen D ∧ b ∈ D ∧ Nonempty (D ≃ₜ Metric.ball (0 : ℂ) 1) := by
  set ψ := chartAt ℂ b
  have hT : ψ.target ∩ ψ.symm ⁻¹' N ∈ 𝓝 (ψ b) := by
    refine Filter.inter_mem (ψ.open_target.mem_nhds (ψ.map_source (mem_chart_source ℂ b))) ?_
    refine (ψ.continuousAt_symm (ψ.map_source (mem_chart_source ℂ b))).preimage_mem_nhds ?_
    rwa [ψ.left_inv (mem_chart_source ℂ b)]
  obtain ⟨ε, hε, hεT⟩ := Metric.mem_nhds_iff.mp hT
  refine ⟨ψ.source ∩ ψ ⁻¹' Metric.ball (ψ b) ε, fun x hx ↦ ?_,
    ψ.isOpen_inter_preimage Metric.isOpen_ball, ⟨mem_chart_source ℂ b, Metric.mem_ball_self hε⟩,
    ⟨?_⟩⟩
  · have := (hεT hx.2).2
    rwa [Set.mem_preimage, ψ.left_inv hx.1] at this
  · have himg : ψ '' (ψ.source ∩ ψ ⁻¹' Metric.ball (ψ b) ε) = Metric.ball (ψ b) ε := by
      rw [ψ.image_source_inter_eq']
      ext y
      constructor
      · rintro ⟨hy, hy'⟩
        rwa [Set.mem_preimage, Set.mem_preimage, ψ.right_inv hy] at hy'
      · intro hy
        refine ⟨(hεT hy).1, ?_⟩
        rwa [Set.mem_preimage, Set.mem_preimage, ψ.right_inv (hεT hy).1]
    let e₁ := ψ.homeomorphOfImageSubsetSource Set.inter_subset_left himg
    let e₂ := (OpenPartialHomeomorph.unitBallBall (ψ b) ε hε).toHomeomorphSourceTarget
    exact e₁.trans ((Homeomorph.setCongr
      (OpenPartialHomeomorph.unitBallBall_target (ψ b) ε hε).symm).trans
      (e₂.symm.trans (Homeomorph.setCongr (OpenPartialHomeomorph.unitBallBall_source (ψ b) ε hε))))

/-- A product structure `U_b × Δ ≃ₜ U` over `Δ` near `E` restricts to one over an open
`D ⊆ Δ`. -/
private lemma exists_homeomorph_prod_restrict {Zs Bs : Type*} [TopologicalSpace Zs]
    [TopologicalSpace Bs] {G : Zs → Bs} {E : Set Zs} {b : Bs} {Δ D : Set Bs} (hD : IsOpen D)
    (hDΔ : D ⊆ Δ) (hbD : b ∈ D) (hbΔ : b ∈ Δ) {Ub U : Set Zs} (hUo : IsOpen U)
    (hEU : E ∩ G ⁻¹' Δ ⊆ U) (Φ : Ub × Δ ≃ₜ U) (hΦg : ∀ p, G (Φ p) = p.2)
    (hΦb : ∀ z : Ub, (Φ (z, ⟨b, hbΔ⟩) : Zs) = z) (hΦE : ∀ p, (Φ p : Zs) ∈ E ↔ (p.1 : Zs) ∈ E) :
    ∃ U' : Set Zs, IsOpen U' ∧ E ∩ G ⁻¹' D ⊆ U' ∧ ∃ Φ' : Ub × D ≃ₜ U',
      (∀ p, G (Φ' p) = p.2) ∧ (∀ z : Ub, (Φ' (z, ⟨b, hbD⟩) : Zs) = z) ∧
      ∀ p, (Φ' p : Zs) ∈ E ↔ (p.1 : Zs) ∈ E := by
  let ι : Ub × D → Zs := fun p ↦ Φ (p.1, Set.inclusion hDΔ p.2)
  have hι : IsOpenEmbedding ι :=
    hUo.isOpenEmbedding_subtypeVal.comp (Φ.isOpenEmbedding.comp
      (IsOpenEmbedding.id.prodMap (IsOpenEmbedding.inclusion hDΔ
        (hD.preimage continuous_subtype_val))))
  refine ⟨Set.range ι, hι.isOpen_range, ?_, hι.isEmbedding.toHomeomorph, fun p ↦ ?_,
    fun z ↦ ?_, fun p ↦ ?_⟩
  · rintro z ⟨hzE, hzD⟩
    set q := Φ.symm ⟨z, hEU ⟨hzE, hDΔ hzD⟩⟩ with hq
    have hΦq : (Φ q : Zs) = z := by rw [hq, Homeomorph.apply_symm_apply]
    have hq2 : (q.2 : Bs) ∈ D := by rwa [← hΦg q, hΦq]
    refine ⟨(q.1, ⟨q.2, hq2⟩), ?_⟩
    change (Φ (q.1, ⟨q.2, _⟩) : Zs) = z
    rw [← hΦq]
  · rw [IsEmbedding.toHomeomorph_apply_coe]
    exact hΦg _
  · rw [IsEmbedding.toHomeomorph_apply_coe]
    exact hΦb z
  · rw [IsEmbedding.toHomeomorph_apply_coe]
    exact hΦE _

/-- A continuous section of a continuous map over a subset is an embedding. -/
lemma isEmbedding_of_comp_eq_val {Ts Bs : Type*} [TopologicalSpace Ts] [TopologicalSpace Bs]
    {q : Ts → Bs} (hq : Continuous q) {D : Set Bs} {σ : D → Ts} (hσ : Continuous σ)
    (hqσ : ∀ s, q (σ s) = s) : IsEmbedding σ :=
  IsEmbedding.of_comp hσ hq (by
    convert IsEmbedding.subtypeVal (p := (· ∈ D)) using 1
    exact funext hqσ)

/-- **Uniqueness of horizontal lifts.** Let `q : T → B` be a covering map, `ι : T → X` an
embedding over `B`, and `σ : D → T` a continuous section of `q` over a preconnected `D`. If
`U_b × D ≃ₜ U` is a product over `D` preserving `π⁻¹(ι T)`, then a horizontal sheet through a
point of `π⁻¹(ι T)` which meets `π⁻¹(ι σ(D))` lies over `ι ∘ σ`. -/
private lemma horizontal_eq_section_of_eq {Zs Xs Ts Bs : Type*} [TopologicalSpace Zs]
    [TopologicalSpace Xs] [TopologicalSpace Ts] [TopologicalSpace Bs]
    {π : Zs → Xs} (hπ : Continuous π) {h : Xs → Bs} {ι : Ts → Xs} (hι : IsEmbedding ι)
    {q : Ts → Bs} (hq : IsCoveringMap q) (hqι : ∀ t, h (ι t) = q t) {D : Set Bs}
    [PreconnectedSpace D] (σ : D → Ts) (hσ : Continuous σ) (hqσ : ∀ s, q (σ s) = s)
    {Ub U : Set Zs} (Φz : Ub × D ≃ₜ U) (hΦg : ∀ p, h (π (Φz p)) = p.2)
    (hΦE : ∀ p, π (Φz p) ∈ Set.range ι ↔ π p.1 ∈ Set.range ι) (z : Ub)
    (hz : π z ∈ Set.range ι) (s₀ : D) (h₀ : π (Φz (z, s₀)) = ι (σ s₀)) (s : D) :
    π (Φz (z, s)) = ι (σ s) := by
  let eι := hι.toHomeomorph
  have hmem : ∀ s' : D, π (Φz (z, s')) ∈ Set.range ι := fun s' ↦ (hΦE _).2 hz
  let γ : D → Ts := fun s' ↦ eι.symm ⟨π (Φz (z, s')), hmem s'⟩
  have hγ : ∀ s', ι (γ s') = π (Φz (z, s')) := fun s' ↦
    congrArg Subtype.val (eι.apply_symm_apply ⟨π (Φz (z, s')), hmem s'⟩)
  have hγc : Continuous γ := eι.symm.continuous.comp
    ((hπ.comp (continuous_subtype_val.comp
      (Φz.continuous.comp (continuous_const.prodMk continuous_id)))).subtype_mk _)
  have hqγ : q ∘ γ = q ∘ σ := by
    funext s'
    simp only [Function.comp_apply, hqσ, ← hqι, hγ, hΦg]
  have hγσ := hq.eq_of_comp_eq hγc hσ hqγ s₀ (hι.injective ((hγ s₀).trans h₀))
  rw [← hγ, hγσ]

/-- **The fibre over a sheet.** Let `q : T → B` be a covering map, `ι : T → X` an embedding
over `B`, and `σ : D → T` a continuous section of `q` over a preconnected `D` through `x`. If a
neighbourhood of `E = π⁻¹(ι T)` over `D` is a product `U_b × D` over `D` preserving `E`, then
`π⁻¹(ι σ(D))` is homeomorphic to `π⁻¹(ι x) × σ(D)` over `σ(D)`. -/
private lemma exists_homeomorph_fibre_prod_sheet {Zs Xs Ts Bs : Type*} [TopologicalSpace Zs]
    [TopologicalSpace Xs] [TopologicalSpace Ts] [TopologicalSpace Bs]
    {π : Zs → Xs} (hπ : Continuous π) {h : Xs → Bs} {ι : Ts → Xs} (hι : IsEmbedding ι)
    {q : Ts → Bs} (hq : IsCoveringMap q) (hqι : ∀ t, h (ι t) = q t) (x : Ts) {D : Set Bs}
    (hDc : IsPreconnected D) (hxD : q x ∈ D) (σ : D → Ts) (hσ : Continuous σ)
    (hqσ : ∀ s, q (σ s) = s) (hσx : σ ⟨q x, hxD⟩ = x) {Ub U : Set Zs} (Φz : Ub × D ≃ₜ U)
    (hΦg : ∀ p, h (π (Φz p)) = p.2) (hΦb : ∀ z : Ub, (Φz (z, ⟨q x, hxD⟩) : Zs) = z)
    (hΦE : ∀ p, π (Φz p) ∈ Set.range ι ↔ π p.1 ∈ Set.range ι)
    (hEb : π ⁻¹' Set.range ι ∩ (h ∘ π) ⁻¹' {q x} ⊆ Ub)
    (hEU : π ⁻¹' Set.range ι ∩ (h ∘ π) ⁻¹' D ⊆ U) :
    ∃ Φ : (π ⁻¹' {ι x}) × Set.range σ ≃ₜ (π ⁻¹' (ι '' Set.range σ)),
      ∀ p, π (Φ p) = ι p.2 := by
  haveI : PreconnectedSpace D := Subtype.preconnectedSpace hDc
  let b : D := ⟨q x, hxD⟩
  have hlift := horizontal_eq_section_of_eq hπ hι hq hqι σ hσ hqσ Φz hΦg hΦE
  have hzU : ∀ z ∈ π ⁻¹' {ι x}, z ∈ Ub := fun z hz ↦
    hEb ⟨⟨x, hz.symm⟩, show h (π z) = q x by rw [hz]; exact hqι x⟩
  let ι₁ : (π ⁻¹' {ι x}) × D → Zs := fun p ↦ Φz (Set.inclusion hzU p.1, p.2)
  have hι₁ : IsEmbedding ι₁ :=
    IsEmbedding.subtypeVal.comp (Φz.isEmbedding.comp
      ((IsEmbedding.inclusion hzU).prodMap IsEmbedding.id))
  have hι₁π : ∀ p, π (ι₁ p) = ι (σ p.2) := by
    rintro ⟨⟨z, hz⟩, s⟩
    refine hlift _ ⟨x, hz.symm⟩ b ?_ s
    change π (Φz (⟨z, hzU z hz⟩, b) : Zs) = ι (σ b)
    rwa [hΦb, hσx]
  have hrange : Set.range ι₁ = π ⁻¹' (ι '' Set.range σ) := by
    ext u
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨σ p.2, ⟨p.2, rfl⟩, (hι₁π p).symm⟩
    · rintro ⟨_, ⟨s₁, rfl⟩, hu⟩
      have huE : u ∈ π ⁻¹' Set.range ι := ⟨σ s₁, hu⟩
      have hus : h (π u) = s₁ := by rw [← hu, hqι, hqσ]
      have huU : u ∈ U := hEU ⟨huE, show h (π u) ∈ D by rw [hus]; exact s₁.2⟩
      set p := Φz.symm ⟨u, huU⟩ with hp
      have hΦp : (Φz p : Zs) = u := by rw [hp, Homeomorph.apply_symm_apply]
      have hp2 : p.2 = s₁ := Subtype.ext ((hΦg p).symm.trans (by rw [hΦp, hus]))
      have hpE : π p.1 ∈ Set.range ι := (hΦE p).1 (by rwa [hΦp])
      have hall := hlift p.1 hpE p.2 (by
        have e : ((p.1, p.2) : Ub × D) = p := rfl
        rw [e, hΦp, ← hu, hp2])
      have hpx : π p.1 = ι x := by
        have := hall b
        rwa [hΦb, hσx] at this
      refine ⟨(⟨p.1, hpx⟩, p.2), ?_⟩
      change (Φz (⟨p.1, _⟩, p.2) : Zs) = u
      rw [← hΦp]
  let eσ : D ≃ₜ Set.range σ :=
    (isEmbedding_of_comp_eq_val hq.continuous hσ hqσ).toHomeomorph
  refine ⟨((Homeomorph.refl _).prodCongr eσ.symm).trans
    (hι₁.toHomeomorph.trans (Homeomorph.setCongr hrange)), fun p ↦ ?_⟩
  change π (ι₁ (p.1, eσ.symm p.2)) = ι p.2
  rw [hι₁π]
  congr 1
  exact congrArg Subtype.val (eσ.apply_symm_apply p.2)

/-- The `ℂ`-points of the relative-dimension loci of a smooth scheme over `ℂ` have pairwise
disjoint images. -/
private lemma pairwise_disjoint_range_realize_relativeDimensionLocus {Z : Scheme.{0}}
    {sW : Z ⟶ Spec (.of ℂ)} [Smooth sW] :
    Pairwise fun d d' : ℕ ↦ Disjoint
      (Set.range (realize (sX := (relativeDimensionLocus sW d).ι ≫ sW) (sY := sW)
        (relativeDimensionLocus sW d).ι rfl))
      (Set.range (realize (sX := (relativeDimensionLocus sW d').ι ≫ sW) (sY := sW)
        (relativeDimensionLocus sW d').ι rfl)) := by
  intro d d' hdd
  rw [Set.disjoint_left]
  rintro _ ⟨m, rfl⟩ ⟨m', hm'⟩
  have h1 : (relativeDimensionLocus sW d').ι (toScheme m') =
      (relativeDimensionLocus sW d).ι (toScheme m) := congrArg toScheme hm'
  have hm1 : (relativeDimensionLocus sW d').ι (toScheme m') ∈ relativeDimensionLocus sW d' :=
    (Scheme.Opens.range_ι _).le ⟨_, rfl⟩
  have hm2 : (relativeDimensionLocus sW d).ι (toScheme m) ∈ relativeDimensionLocus sW d :=
    (Scheme.Opens.range_ι _).le ⟨_, rfl⟩
  rw [h1] at hm1
  exact hdd (eq_of_mem_relativeDimensionLocus hm2 hm1)

open scoped ContDiff Manifold in
/-- **A product near the exceptional set.** Let `f : Z ⟶ X` be proper with `Z` smooth over `ℂ`,
`T ⊆ X` closed and proper over a smooth curve `B`, and suppose `f⁻¹(T)` is the support of a
simple normal crossing divisor all of whose strata are smooth over `B`. Then over a preconnected
open `Δ ∋ b` of `B^an`, a neighbourhood of `E_Δ` in `Z^an` is the product of a neighbourhood
`U_b` of `E_b` in the fibre over `b` with `Δ`, over `Δ`, the identity at `b` and preserving `E`. -/
private lemma exists_homeomorph_prod_near_preimage
    {Z X T B : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sB : B ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sX] [IsSeparated sX] [QuasiCompact sX]
    [LocallyOfFiniteType sB] [IsSeparated sB] [QuasiCompact sB] [SmoothOfRelativeDimension 1 sB]
    (f : Z ⟶ X) [IsProper f] [Smooth (f ≫ sX)]
    (iT : T ⟶ X) [IsClosedImmersion iT] (h : X ⟶ B) (hh : h ≫ sB = sX) [IsProper (iT ≫ h)]
    (s : Finset (MMP.Mori.PrimeDivisor Z))
    (hEs : (⋃ E ∈ s, (E.support : Set Z)) = f ⁻¹' Set.range iT)
    (hsnc : MMP.Mori.DivisorWithCoeffs.IsSNC (f ≫ sX) (∑ E ∈ s, Finsupp.single E (1 : ℤ)))
    (hstr : ∀ J ⊆ s, Smooth ((⨆ E ∈ J, E.idealSheaf).subschemeι ≫ f ≫ h))
    (b : ComplexPoints sB) :
    ∃ Δ : Set (ComplexPoints sB), IsOpen Δ ∧ IsPreconnected Δ ∧ ∃ hbΔ : b ∈ Δ,
      ∃ O Ub U : Set (ComplexPoints (f ≫ sX)),
      IsOpen O ∧ Ub = O ∩ (realize h hh ∘ realize f rfl) ⁻¹' {b} ∧
      realize f rfl ⁻¹' Set.range (realize (sX := iT ≫ sX) iT rfl) ∩
        (realize h hh ∘ realize f rfl) ⁻¹' {b} ⊆ Ub ∧ IsOpen U ∧
      realize f rfl ⁻¹' Set.range (realize (sX := iT ≫ sX) iT rfl) ∩
        (realize h hh ∘ realize f rfl) ⁻¹' Δ ⊆ U ∧
      ∃ Φ : Ub × Δ ≃ₜ U, (∀ p, realize h hh (realize f rfl (Φ p)) = p.2) ∧
        (∀ z : Ub, (Φ (z, ⟨b, hbΔ⟩) : ComplexPoints (f ≫ sX)) = z) ∧
        ∀ p, realize f rfl (Φ p : ComplexPoints (f ≫ sX)) ∈
            Set.range (realize (sX := iT ≫ sX) iT rfl) ↔
          realize f rfl (p.1 : ComplexPoints (f ≫ sX)) ∈
            Set.range (realize (sX := iT ≫ sX) iT rfl) := by
  classical
  have : Smooth sB := SmoothOfRelativeDimension.smooth 1 sB
  set τ : Set (ComplexPoints sX) := Set.range (realize (sX := iT ≫ sX) iT rfl) with hτ
  let π := realize (sX := f ≫ sX) f rfl
  let hB := realize h hh
  let G : ComplexPoints (f ≫ sX) → ComplexPoints sB := hB ∘ π
  let Eset : Set (ComplexPoints (f ≫ sX)) := π ⁻¹' τ
  have hπp := (isSeparatedMap_and_isProperMap_realize (sX := f ≫ sX) (sS := sX) f rfl).2
  have hTp := (isSeparatedMap_and_isProperMap_realize (sX := iT ≫ sX) (sS := sX) iT rfl).2
  have hτc : IsClosed τ := hTp.isClosedMap.isClosed_range
  have hEc : IsClosed Eset := hτc.preimage hπp.continuous
  have hGE : IsProperMap (Eset.domRestrict G) := by
    have H := isProperMap_restrict_realize_preimage_range f iT h hh
    have hG : realize (sX := f ≫ sX) (sY := sB) (f ≫ h) (by rw [Category.assoc, hh]) = G :=
      realize_comp f rfl h hh
    rwa [hG] at H
  let sW := f ≫ sX
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  let Y : ℕ → Z.Opens := fun d ↦ relativeDimensionLocus sW d
  let M : ℕ → Type := fun d ↦ ComplexPoints ((Y d).ι ≫ sW)
  let ρ : ∀ d, M d → ComplexPoints (f ≫ sX) := fun d ↦
    realize (sX := (Y d).ι ≫ sW) (sY := f ≫ sX) (Y d).ι rfl
  have hρ : ∀ d, IsOpenEmbedding (ρ d) := fun d ↦
    isOpenEmbedding_realize_of_isOpenImmersion _ _
  have hρpt : ∀ d (m : M d), toScheme (ρ d m) = (Y d).ι (toScheme m) := fun _ _ ↦ rfl
  have hdisj : Pairwise fun d d' ↦ Disjoint (Set.range (ρ d)) (Set.range (ρ d')) :=
    pairwise_disjoint_range_realize_relativeDimensionLocus (sW := sW)
  have hmemE : ∀ z, z ∈ Eset ↔ f (toScheme z) ∈ Set.range iT := fun z ↦
    mem_range_realize_iff_of_isClosedImmersion iT (π z)
  have hcov : Eset ⊆ ⋃ d, Set.range (ρ d) := by
    intro z _
    obtain ⟨d, hd⟩ := exists_mem_relativeDimensionLocus (sX := sW) (toScheme z)
    refine Set.mem_iUnion.2 ⟨d, ?_⟩
    rwa [range_realize_of_isOpenImmersion, Scheme.Opens.opensRange_ι]
  have : QuasiCompact sW := inferInstanceAs (QuasiCompact (f ≫ sX))
  have : IsSeparated sW := inferInstanceAs (IsSeparated (f ≫ sX))
  have hg : (f ≫ h) ≫ sB = sW := by simp only [sW, Category.assoc, hh]
  have hflow : ∀ d, ∃ Δi ∈ 𝓝 b, ∃ (Ubi Ui : Set (M d)) (hb : b ∈ Δi),
      (∃ O, IsOpen O ∧ Ubi = O ∩ (G ∘ ρ d) ⁻¹' {b}) ∧ ρ d ⁻¹' Eset ∩ (G ∘ ρ d) ⁻¹' {b} ⊆ Ubi ∧
      IsOpen Ui ∧ ρ d ⁻¹' Eset ∩ (G ∘ ρ d) ⁻¹' Δi ⊆ Ui ∧ ∃ Φ : Ubi × Δi ≃ₜ Ui,
        (∀ p, G (ρ d (Φ p)) = p.2) ∧ (∀ z, (Φ (z, ⟨b, hb⟩) : M d) = z) ∧
        ∀ p, ρ d (Φ p) ∈ Eset ↔ ρ d p.1 ∈ Eset := by
    intro d
    obtain ⟨pick, hcmd, hD, hsub, hstrata⟩ :=
      exists_pick_relativeSNC_relativeDimensionLocus (sX := sW) d (f ≫ h) hg s hsnc hstr
    let := etaleChartedSpaceOf ((Y d).ι ≫ sW) d (EuclideanSpace.equiv (Fin d) ℂ).symm pick
    have := isManifold_etaleChartedSpaceOf ((Y d).ι ≫ sW) d
      (EuclideanSpace.equiv (Fin d) ℂ).symm pick ∞
    have : T2Space (M d) := t2Space
    have : SecondCountableTopology (M d) := secondCountableTopology d
    let D : s → Set (M d) := fun E ↦ {y | (Y d).ι (toScheme y) ∈ E.1.support}
    let gY := realize (sX := (Y d).ι ≫ sW) (sY := sB) ((Y d).ι ≫ (f ≫ h))
      (by rw [Category.assoc, hg])
    have hgY : gY = G ∘ ρ d := by
      funext y
      ext1
      simp only [gY, G, π, hB, ρ, Function.comp_apply, realize_hom, Category.assoc]
    have hDE : (⋃ i, D i) = ρ d ⁻¹' Eset := by
      ext y
      rw [Set.mem_preimage, hmemE, Set.mem_iUnion]
      have := congrArg (fun S : Set Z ↦ (Y d).ι (toScheme y) ∈ S) hEs
      simp only [Set.mem_iUnion, Set.mem_preimage, eq_iff_iff, exists_prop] at this
      rw [hρpt, ← this]
      exact ⟨fun ⟨i, hi⟩ ↦ ⟨i.1, i.2, hi⟩, fun ⟨E, hE, hi⟩ ↦ ⟨⟨E, hE⟩, hi⟩⟩
    have hEcl : IsClosed (⋃ i, D i) := by
      rw [hDE]
      exact hEc.preimage (hρ d).continuous
    have hprop : IsProperMap fun y : (⋃ i, D i : Set (M d)) ↦ gY y := by
      have H := (hGE.comp (isClosedEmbedding_restrictPreimage_of_pairwise_disjoint hρ hdisj
        hcov d).isProperMap).comp (Homeomorph.setCongr hDE).isProperMap
      convert H using 1
      funext y
      exact congrFun hgY y.1
    obtain ⟨ψ, -, -, r, -, -, -, Ub, Ui, hb, -, ⟨O, hO, hUbO⟩, hEb, hUo, -, hEU, Φ, hΦg, hΦb,
        hΦD⟩ :=
      MMP.Analytic.exists_homeomorph_prod_of_relativeSNC ((hcmd ∞).mdifferentiable (by simp))
        (hD ∞) hEcl hprop ⟨Set.univ, isOpen_univ, Set.subset_univ _, fun y _ ↦ hsub y⟩
        (fun y _ ↦ hstrata y) b Filter.univ_mem
    rw [hDE] at hEb hEU
    change ρ d ⁻¹' Eset ∩ gY ⁻¹' {b} ⊆ Ub at hEb
    change ρ d ⁻¹' Eset ∩ gY ⁻¹' (ψ.source ∩ ψ ⁻¹' Metric.ball (ψ b) r) ⊆ Ui at hEU
    change Ub = O ∩ gY ⁻¹' {b} at hUbO
    change ∀ p, gY (Φ p) = p.2 at hΦg
    rw [hgY] at hEb hEU hUbO hΦg
    refine ⟨_, (ψ.isOpen_inter_preimage Metric.isOpen_ball).mem_nhds hb, Ub, Ui, hb,
      ⟨O, hO, hUbO⟩, hEb, hUo, hEU, Φ, hΦg, hΦb, fun p ↦ ?_⟩
    rw [← Set.mem_preimage (f := ρ d), ← Set.mem_preimage (f := ρ d), ← hDE]
    simp only [Set.mem_iUnion]
    exact exists_congr fun i ↦ hΦD i p
  exact exists_homeomorph_prod_of_isOpenEmbedding_family hGE
    (fun _ ↦ exists_isOpen_isPreconnected_subset_of_mem_nhds) hρ hdisj hcov hflow

/-- The union of the coordinate hyperplanes of `ℂⁿ` has empty interior. -/
private lemma interior_iUnion_coordinate_hyperplane_eq_empty (d : ℕ) :
    interior (⋃ j : Fin d, {y : EuclideanSpace ℂ (Fin d) | y j = 0}) = ∅ := by
  have hH : ∀ j : Fin d, IsClosed {y : EuclideanSpace ℂ (Fin d) | y j = 0} ∧
      interior {y : EuclideanSpace ℂ (Fin d) | y j = 0} = ∅ := by
    intro j
    let L : EuclideanSpace ℂ (Fin d) →L[ℂ] ℂ := EuclideanSpace.proj j
    have hker : {y : EuclideanSpace ℂ (Fin d) | y j = 0} =
        (LinearMap.ker L.toLinearMap : Set _) := by
      ext y
      simp [L]
    rw [hker]
    refine ⟨L.isClosed_ker, ?_⟩
    by_contra hne
    have htop := Submodule.eq_top_of_nonempty_interior' _ (Set.nonempty_iff_ne_empty.2 hne)
    have : EuclideanSpace.single j (1 : ℂ) ∈ LinearMap.ker L.toLinearMap := by rw [htop]; trivial
    simp [L] at this
  have key : ∀ S : Finset (Fin d),
      interior (⋃ j ∈ S, {y : EuclideanSpace ℂ (Fin d) | y j = 0}) = ∅ := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | insert j S _ ih =>
      rw [Finset.set_biUnion_insert, Set.union_comm,
        interior_union_isClosed_of_interior_empty
          (isClosed_biUnion_finset fun i _ ↦ (hH i).1) (hH j).2, ih]
  simpa using key Finset.univ

open scoped ContDiff Manifold in
/-- **The exceptional set is nowhere dense analytically.** If `f⁻¹(T)` is the support of a simple
normal crossing divisor on `Z` smooth over `ℂ`, with strata smooth over a smooth curve, then
`f^an⁻¹(T^an)` has empty interior in `Z^an`. -/
private lemma interior_preimage_range_realize_eq_empty
    {Z X T B : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sB : B ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sX] [LocallyOfFiniteType sB] [SmoothOfRelativeDimension 1 sB]
    (f : Z ⟶ X) [LocallyOfFiniteType f] [Smooth (f ≫ sX)]
    (iT : T ⟶ X) [IsClosedImmersion iT] (h : X ⟶ B) (hh : h ≫ sB = sX)
    (s : Finset (MMP.Mori.PrimeDivisor Z))
    (hEs : (⋃ E ∈ s, (E.support : Set Z)) = f ⁻¹' Set.range iT)
    (hsnc : MMP.Mori.DivisorWithCoeffs.IsSNC (f ≫ sX) (∑ E ∈ s, Finsupp.single E (1 : ℤ)))
    (hstr : ∀ J ⊆ s, Smooth ((⨆ E ∈ J, E.idealSheaf).subschemeι ≫ f ≫ h)) :
    interior (realize (sX := f ≫ sX) f rfl ⁻¹' Set.range (realize (sX := iT ≫ sX) iT rfl)) =
      ∅ := by
  classical
  by_contra hne
  obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.2 hne
  let sW := f ≫ sX
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  obtain ⟨d, hd⟩ := exists_mem_relativeDimensionLocus (sX := sW) (toScheme z)
  let Yd := relativeDimensionLocus sW d
  let ρ := realize (sX := Yd.ι ≫ sW) (sY := f ≫ sX) Yd.ι rfl
  have hρ : IsOpenEmbedding ρ := isOpenEmbedding_realize_of_isOpenImmersion _ _
  obtain ⟨m, hm⟩ : z ∈ Set.range ρ := by
    rwa [range_realize_of_isOpenImmersion, Scheme.Opens.opensRange_ι]
  have hg : (f ≫ h) ≫ sB = sW := by simp only [sW, Category.assoc, hh]
  obtain ⟨pick, -, hD, -, -⟩ :=
    exists_pick_relativeSNC_relativeDimensionLocus (sX := sW) d (f ≫ h) hg s hsnc hstr
  let := etaleChartedSpaceOf (Yd.ι ≫ sW) d (EuclideanSpace.equiv (Fin d) ℂ).symm pick
  obtain ⟨φ, -, hmφ, s', c, hout, hin⟩ := hD ∞ m
  set G' := ρ ⁻¹' interior (realize (sX := f ≫ sX) f rfl ⁻¹'
    Set.range (realize (sX := iT ≫ sX) iT rfl))
  have hG'o : IsOpen G' := isOpen_interior.preimage hρ.continuous
  have hmG' : m ∈ G' := by
    show m ∈ ρ ⁻¹' interior _
    rwa [Set.mem_preimage, hm]
  have hU0o : IsOpen (φ '' (G' ∩ φ.source)) :=
    φ.isOpen_image_of_subset_source (hG'o.inter φ.open_source) Set.inter_subset_right
  have hU0sub : φ '' (G' ∩ φ.source) ⊆ ⋃ j : Fin d, {y : EuclideanSpace ℂ (Fin d) | y j = 0} := by
    rintro _ ⟨y, ⟨hyG, hyφ⟩, rfl⟩
    have hyE := interior_subset hyG
    rw [Set.mem_preimage, mem_range_realize_iff_of_isClosedImmersion] at hyE
    have hyE' : Yd.ι (toScheme y) ∈ ⋃ E ∈ s, (E.support : Set Z) := by
      rwa [hEs]
    obtain ⟨E, hE, hyE''⟩ := Set.mem_iUnion₂.1 hyE'
    by_cases hi : (⟨E, hE⟩ : s) ∈ s'
    · have hmem : φ y ∈ φ '' ({y | Yd.ι (toScheme y) ∈ (⟨E, hE⟩ : s).1.support} ∩ φ.source) :=
        ⟨y, ⟨hyE'', hyφ⟩, rfl⟩
      rw [hin ⟨⟨E, hE⟩, hi⟩] at hmem
      exact Set.mem_iUnion.2 ⟨c ⟨⟨E, hE⟩, hi⟩, hmem.2⟩
    · exact (Set.eq_empty_iff_forall_notMem.1 (hout ⟨E, hE⟩ hi) y ⟨hyE'', hyφ⟩).elim
  have := interior_maximal hU0sub hU0o
  rw [interior_iUnion_coordinate_hyperplane_eq_empty] at this
  exact this ⟨m, ⟨hmG', hmφ⟩, rfl⟩

/-- **The slice of a local product.** If a neighbourhood `N` of `x` is a product `U₀ × D` over
`D`, sending `τ ∩ N` to `{x} × D` and restricting to the identity on the slice over `b = h x`,
then `U₀` is an open slice `V` of the fibre with `V ∩ τ = {x}`, and `N ≃ₜ V × D`. -/
private lemma exists_slice_of_homeomorph_prod {Xs Bs Y : Type*} [TopologicalSpace Xs]
    [TopologicalSpace Bs] [TopologicalSpace Y] {h : Xs → Bs} {τ : Set Xs} {x : Xs} {b : Bs}
    (hxb : h x = b) (hxτ : x ∈ τ) {D : Set Bs} (hbD : b ∈ D) (eD : D ≃ₜ Y) {N : Set Xs}
    {U₀ : Set (h ⁻¹' {b})} (hU₀o : IsOpen U₀) (hx₀ : (⟨x, hxb⟩ : h ⁻¹' {b}) ∈ U₀)
    (φ : N ≃ₜ U₀ × D) (h2 : ∀ y : N, ((φ y).2 : Bs) = h y)
    (h3 : ∀ y : N, (y : Xs) ∈ τ ↔ (φ y).1 = ⟨⟨x, hxb⟩, hx₀⟩)
    (h4 : ∀ (y : N) (hy : h y = b), ((φ y).1 : h ⁻¹' {b}) = ⟨y, hy⟩) :
    ∃ V : Set Xs, (∃ O : Set Xs, IsOpen O ∧ V = O ∩ h ⁻¹' {h x}) ∧ x ∈ V ∧ V ∩ τ = {x} ∧
      ∃ Φ : N ≃ₜ V × Y, ∀ n : N, (n : Xs) ∈ τ ↔ ((Φ n).1 : Xs) = x := by
  obtain ⟨O', hO'o, hO'⟩ := isOpen_induced_iff.1 hU₀o
  let V : Set Xs := Set.range fun u : U₀ ↦ ((u : h ⁻¹' {b}) : Xs)
  have hVemb : IsEmbedding fun u : U₀ ↦ ((u : h ⁻¹' {b}) : Xs) :=
    IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal
  have hV : V = O' ∩ h ⁻¹' {h x} := by
    rw [hxb]
    ext y
    constructor
    · rintro ⟨u, rfl⟩
      have hu : (u : h ⁻¹' {b}) ∈ Subtype.val ⁻¹' O' := by rw [hO']; exact u.2
      exact ⟨hu, (u : h ⁻¹' {b}).2⟩
    · rintro ⟨hyO, hyb⟩
      have hu : (⟨y, hyb⟩ : h ⁻¹' {b}) ∈ U₀ := by rwa [← hO']
      exact ⟨⟨⟨y, hyb⟩, hu⟩, rfl⟩
  refine ⟨V, ⟨O', hO'o, hV⟩, ⟨⟨⟨x, hxb⟩, hx₀⟩, rfl⟩, ?_,
    φ.trans (hVemb.toHomeomorph.prodCongr eD), fun n ↦ ?_⟩
  · ext y
    constructor
    · rintro ⟨⟨u, rfl⟩, hyτ⟩
      set n := φ.symm (u, ⟨b, hbD⟩) with hn
      have hφn : φ n = (u, ⟨b, hbD⟩) := by rw [hn, Homeomorph.apply_symm_apply]
      have hnb : h n = b := by rw [← h2 n, hφn]
      have hun : (u : h ⁻¹' {b}) = ⟨n, hnb⟩ := by rw [← h4 n hnb, hφn]
      have hyn : ((u : h ⁻¹' {b}) : Xs) = n := by rw [hun]
      change ((u : h ⁻¹' {b}) : Xs) ∈ τ at hyτ
      change ((u : h ⁻¹' {b}) : Xs) = x
      rw [hyn] at hyτ
      have : u = ⟨⟨x, hxb⟩, hx₀⟩ := by
        have := (h3 n).1 hyτ
        rwa [hφn] at this
      rw [this]
    · rintro rfl
      exact ⟨⟨⟨⟨_, hxb⟩, hx₀⟩, rfl⟩, hxτ⟩
  · rw [h3 n]
    change _ ↔ (((φ n).1 : h ⁻¹' {b}) : Xs) = x
    exact ⟨fun hn ↦ by rw [hn], fun hn ↦ Subtype.ext (Subtype.ext hn)⟩

/-- If `g ∘ ι = q` with `ι` an embedding and `q` a covering map, then `g` restricted to the
range of `ι` is a covering map. -/
private lemma isCoveringMap_restrict_range {Ts Xs Bs : Type*} [TopologicalSpace Ts]
    [TopologicalSpace Xs] [TopologicalSpace Bs] {ι : Ts → Xs} (hι : IsEmbedding ι)
    {g : Xs → Bs} {q : Ts → Bs} (hq : IsCoveringMap q) (hgq : ∀ t, g (ι t) = q t) :
    IsCoveringMap (fun t : Set.range ι ↦ g t) := by
  let eT := hι.toHomeomorph
  have : (fun t : Set.range ι ↦ g t) = q ∘ eT.symm := by
    funext t
    obtain ⟨t', rfl⟩ := eT.surjective t
    rw [Function.comp_apply, eT.symm_apply_apply, IsEmbedding.toHomeomorph_apply_coe]
    exact hgq t'
  rw [this]
  exact hq.comp_homeomorph eT.symm

/-- **Generic trivializations at a point of the centre.** In the situation of
`exists_homeomorph_prod_near_preimage`, with `f` surjective and an isomorphism off `T`, and
`T ⟶ B` finite étale, at every `x ∈ T(ℂ)`: there is an open disk `W ∋ x` of `T^an` over which
`f^an` is the product `f⁻¹(x) × W`, and the pair `(X^an, T^an)` is near `x` the product of the
slice germ `(V, {x})` with a disk. -/
private lemma exists_trivializations_at
    {Z X T B : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sB : B ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sX] [IsSeparated sX] [QuasiCompact sX]
    [LocallyOfFiniteType sB] [IsSeparated sB] [QuasiCompact sB] [SmoothOfRelativeDimension 1 sB]
    (f : Z ⟶ X) [IsProper f] [Surjective f] [Smooth (f ≫ sX)]
    (iT : T ⟶ X) [IsClosedImmersion iT] (U : X.Opens) (hU : (U : Set X) = (Set.range iT)ᶜ)
    [IsIso (f ∣_ U)] (h : X ⟶ B) (hh : h ≫ sB = sX) [IsFinite (iT ≫ h)] [Etale (iT ≫ h)]
    (s : Finset (MMP.Mori.PrimeDivisor Z))
    (hEs : (⋃ E ∈ s, (E.support : Set Z)) = f ⁻¹' Set.range iT)
    (hsnc : MMP.Mori.DivisorWithCoeffs.IsSNC (f ≫ sX) (∑ E ∈ s, Finsupp.single E (1 : ℤ)))
    (hstr : ∀ J ⊆ s, Smooth ((⨆ E ∈ J, E.idealSheaf).subschemeι ≫ f ≫ h))
    (x : ComplexPoints (iT ≫ sX)) :
    (∃ W : Set (ComplexPoints (iT ≫ sX)), IsOpen W ∧ x ∈ W ∧
        Nonempty (W ≃ₜ Metric.ball (0 : ℂ) 1) ∧
        ∃ Φ : (realize (sX := f ≫ sX) f rfl ⁻¹' {realize (sX := iT ≫ sX) iT rfl x}) × W ≃ₜ
            (realize (sX := f ≫ sX) f rfl ⁻¹' (realize (sX := iT ≫ sX) iT rfl '' W)),
          ∀ p, realize (sX := f ≫ sX) f rfl (Φ p) = realize (sX := iT ≫ sX) iT rfl p.2) ∧
    (∃ N : Set (ComplexPoints sX), IsOpen N ∧ realize (sX := iT ≫ sX) iT rfl x ∈ N ∧
        ∃ V : Set (ComplexPoints sX),
          (∃ O : Set (ComplexPoints sX), IsOpen O ∧
            V = O ∩ realize h hh ⁻¹' {realize h hh (realize (sX := iT ≫ sX) iT rfl x)}) ∧
          realize (sX := iT ≫ sX) iT rfl x ∈ V ∧
          V ∩ Set.range (realize (sX := iT ≫ sX) iT rfl) = {realize (sX := iT ≫ sX) iT rfl x} ∧
          ∃ Φ : N ≃ₜ V × Metric.ball (0 : ℂ) 1,
            ∀ n : N, (n : ComplexPoints sX) ∈ Set.range (realize (sX := iT ≫ sX) iT rfl) ↔
              ((Φ n).1 : ComplexPoints sX) = realize (sX := iT ≫ sX) iT rfl x) := by
  classical
  let π := realize (sX := f ≫ sX) f rfl
  let ι := realize (sX := iT ≫ sX) iT rfl
  let hB := realize h hh
  let q := realize (sX := iT ≫ sX) (sY := sB) (iT ≫ h) (by rw [Category.assoc, hh])
  have hq : IsCoveringMap q := isCoveringMap_realize_of_isFinite_of_etale (iT ≫ h) _
  have hqι : ∀ t, hB (ι t) = q t := fun t ↦ (congrFun (realize_comp iT rfl h hh) t)
  have hπp := (isSeparatedMap_and_isProperMap_realize (sX := f ≫ sX) (sS := sX) f rfl).2
  have hTp := (isSeparatedMap_and_isProperMap_realize (sX := iT ≫ sX) (sS := sX) iT rfl).2
  have hTe : IsClosedEmbedding ι :=
    IsClosedEmbedding.of_continuous_injective_isClosedMap hTp.continuous
      (fun t t' htt ↦ ComplexPoints.ext
        ((cancel_mono iT).1 (congrArg (fun y : ComplexPoints sX ↦ y.hom) htt)))
      hTp.isClosedMap
  -- the product near `E` over a preconnected `Δ ∋ q x`
  obtain ⟨Δ, hΔo, -, hbΔ, O, Ub, Uz, hOo, hUb, hEb, hUo, hEU, Φ, hΦg, hΦb, hΦE⟩ :=
    exists_homeomorph_prod_near_preimage f iT h hh s hEs hsnc hstr (q x)
  -- a local section of `q` through `x` and a disk in its domain
  obtain ⟨e, hxe, he⟩ := hq.isLocalHomeomorph x
  have hN : Δ ∩ e.target ∈ 𝓝 (q x) := Filter.inter_mem (hΔo.mem_nhds hbΔ)
    (e.open_target.mem_nhds (by rw [he]; exact e.map_source hxe))
  obtain ⟨D, hDN, hDo, hxD, ⟨eD⟩⟩ := exists_isOpen_homeomorph_ball_subset (q x) hN
  have hDt : D ⊆ e.target := fun y hy ↦ (hDN hy).2
  have hDc : IsPreconnected D := by
    haveI : PreconnectedSpace (Metric.ball (0 : ℂ) 1) :=
      Subtype.preconnectedSpace (convex_ball (0 : ℂ) 1).isPreconnected
    have : D = Set.range (Subtype.val ∘ eD.symm) := by
      rw [Set.range_comp, eD.symm.range_coe, Set.image_univ, Subtype.range_coe]
    rw [this]
    exact isPreconnected_range (continuous_subtype_val.comp eD.symm.continuous)
  -- restrict the product to `D`
  obtain ⟨U', hU'o, hEU', Φ', hΦ'g, hΦ'b, hΦ'E⟩ :=
    exists_homeomorph_prod_restrict (G := hB ∘ π) hDo (fun y hy ↦ (hDN hy).1) hxD hbΔ hUo hEU
      Φ hΦg hΦb hΦE
  refine ⟨?_, ?_⟩
  · -- (3): the sheet through `x` over `D`
    let σ : D → ComplexPoints (iT ≫ sX) := D.restrict e.symm
    have hσc : Continuous σ := (e.continuousOn_symm.mono hDt).restrict
    have hqσ : ∀ s', q (σ s') = s' := fun s' ↦ by
      rw [he]; exact e.right_inv (hDt s'.2)
    have hσx : σ ⟨q x, hxD⟩ = x := by
      change e.symm (q x) = x
      rw [he]; exact e.left_inv hxe
    obtain ⟨Φ3, hΦ3⟩ := exists_homeomorph_fibre_prod_sheet hπp.continuous hTe.isEmbedding hq
      hqι x hDc hxD σ hσc hqσ hσx Φ' hΦ'g hΦ'b hΦ'E
      hEb hEU'
    have hσemb : IsEmbedding σ := isEmbedding_of_comp_eq_val hq.continuous hσc hqσ
    have hrange : Set.range σ = e.source ∩ e ⁻¹' D := by
      ext w
      constructor
      · rintro ⟨s', rfl⟩
        exact ⟨e.map_target (hDt s'.2), by
          change e (e.symm s') ∈ D; rw [e.right_inv (hDt s'.2)]; exact s'.2⟩
      · rintro ⟨hw, hwD⟩
        exact ⟨⟨e w, hwD⟩, e.left_inv hw⟩
    refine ⟨Set.range σ, ?_, ⟨⟨q x, hxD⟩, hσx⟩, ⟨hσemb.toHomeomorph.symm.trans eD⟩, Φ3, hΦ3⟩
    rw [hrange]
    exact e.isOpen_inter_preimage hDo
  · -- (4): descent of the product to `X`
    set τ : Set (ComplexPoints sX) := Set.range ι with hτ
    have hcovτ : IsCoveringMap (fun t : τ ↦ hB t) :=
      isCoveringMap_restrict_range hTe.isEmbedding hq hqι
    have hπs : Function.Surjective π := surjective_realize_of_surjective f
    have hinj : ∀ z z', π z ∉ τ → π z = π z' → z = z' := fun z z' hz hzz ↦ by
      refine eq_of_realize_eq_of_isIso_restrict f U ?_ hzz
      rw [← SetLike.mem_coe, hU]
      exact fun hmem ↦ hz ((mem_range_realize_iff_of_isClosedImmersion iT _).2 hmem)
    have hxτ : ι x ∈ τ := ⟨x, rfl⟩
    obtain ⟨N, U₀, hNo, hU₀o, hxN, hx₀, φ, -, h2, h3, h4⟩ :=
      exists_homeomorph_prod_of_isProperMap hπp hπs hinj hcovτ hxτ (hqι x) hDc hxD hOo hUb hEb
        hU'o hEU' Φ' hΦ'g hΦ'b hΦ'E
    obtain ⟨V, hV, hxV, hVτ, Φ, hΦ⟩ :=
      exists_slice_of_homeomorph_prod (hqι x) hxτ hxD eD hU₀o hx₀ φ h2 h3 h4
    exact ⟨N, hNo, hxN, V, hV, hxV, hVτ, Φ, hΦ⟩

/-- A nonempty open of an irreducible space is not contained in a closed subset of different
dimension. -/
private lemma exists_mem_notMem_of_topologicalKrullDim_ne {Y : Type*} [TopologicalSpace Y]
    [IrreducibleSpace Y] {T : Set Y} (hT : IsClosed T)
    (hdim : topologicalKrullDim T ≠ topologicalKrullDim Y) {X : Set Y} (hX : IsOpen X)
    (hXne : X.Nonempty) : ∃ y ∈ X, y ∉ T := by
  by_contra hcon
  push Not at hcon
  have hTu : T = Set.univ := by
    refine Set.eq_univ_of_univ_subset ?_
    rw [← (hX.dense hXne).closure_eq]
    exact closure_minimal hcon hT
  subst hTu
  exact hdim (Homeomorph.Set.univ Y).isHomeomorph.topologicalKrullDim_eq

/-- A proper morphism to an irreducible scheme which is an isomorphism over a nonempty open is
surjective. -/
private lemma surjective_of_isIso_morphismRestrict {Z X : Scheme.{0}} [IrreducibleSpace X]
    (f : Z ⟶ X) [IsProper f] (V : X.Opens) (hV : (V : Set X).Nonempty) [IsIso (f ∣_ V)] :
    Surjective f := by
  have hsub : (V : Set X) ⊆ Set.range f := by
    intro v hv
    obtain ⟨w, hw⟩ := (f ∣_ V).homeomorph.surjective ⟨v, hv⟩
    refine ⟨(f ⁻¹ᵁ V).ι w, ?_⟩
    have := congrArg (fun y : V ↦ (y : X)) hw
    simp only at this
    rw [← this]
    change ((f ⁻¹ᵁ V).ι ≫ f) w = V.ι ((f ∣_ V) w)
    rw [← morphismRestrict_ι]
    rfl
  refine ⟨fun x ↦ ?_⟩
  have : closure (V : Set X) ⊆ Set.range f := closure_minimal hsub f.isClosedMap.isClosed_range
  rw [(V.isOpen.dense hV).closure_eq] at this
  exact this (Set.mem_univ x)

/-- A `ℂ`-point takes the value `toScheme` at the point of `Spec ℂ`. -/
private lemma val_apply_eq_toScheme {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    (z : ComplexPoints sX) (a : Spec (.of ℂ)) : z.1 a = z.toScheme := by
  unfold toScheme
  exact congrArg z.1 (Subsingleton.elim a _)

/-- Over `ℂ`, a `ℂ`-point is determined by its point. -/
private lemma toScheme_injective {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sX] : Function.Injective (toScheme : ComplexPoints sX → X) := by
  intro x y hxy
  refine (pointEquivClosedPoint sX).injective (Subtype.ext ?_)
  change x.1 (IsLocalRing.closedPoint ℂ) = y.1 (IsLocalRing.closedPoint ℂ)
  exact (val_apply_eq_toScheme x _).trans (hxy.trans (val_apply_eq_toScheme y _).symm)

/-- The point of a `ℂ`-point is closed. -/
private lemma isClosed_singleton_toScheme' {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    (x : ComplexPoints sX) : IsClosed ({x.toScheme} : Set X) := by
  have : IsClosedImmersion x.hom := isClosedImmersion_of_comp_eq_id sX x.hom x.2
  convert x.hom.isClosedEmbedding.isClosed_range using 1
  ext y
  constructor
  · rintro rfl; exact ⟨default, val_apply_eq_toScheme x _⟩
  · rintro ⟨q, rfl⟩; exact val_apply_eq_toScheme x q

/-- Every closed point of a scheme locally of finite type over `ℂ` is the point of a `ℂ`-point. -/
private lemma exists_toScheme_eq {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sX] {p : X} (hp : IsClosed ({p} : Set X)) :
    ∃ x : ComplexPoints sX, x.toScheme = p := by
  obtain ⟨x, hx⟩ := (pointEquivClosedPoint sX).surjective ⟨p, hp⟩
  refine ⟨x, ?_⟩
  have := congrArg Subtype.val hx
  change x.1 (IsLocalRing.closedPoint ℂ) = p at this
  exact (val_apply_eq_toScheme x _).symm.trans this

/-- For a `ℂ`-point `b` of `B`, the residue field `κ(b)` is `ℂ`: the composite
`Spec κ(b) ⟶ B ⟶ Spec ℂ` is an isomorphism. -/
private lemma isIso_fromSpecResidueField_toScheme_comp {B : Scheme.{0}}
    {sB : B ⟶ Spec (.of ℂ)} (b : ComplexPoints sB) :
    IsIso (B.fromSpecResidueField b.toScheme ≫ sB) := by
  rw [← val_apply_eq_toScheme b (IsLocalRing.closedPoint ℂ)]
  set φ := B.descResidueField (Scheme.stalkClosedPointTo b.hom)
  have key : Spec.map φ ≫ B.fromSpecResidueField (b.1 (IsLocalRing.closedPoint ℂ)) = b.hom :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField ℂ B b.hom
  set g := B.fromSpecResidueField (b.1 (IsLocalRing.closedPoint ℂ)) ≫ sB
  have hφg : Spec.map φ ≫ g = 𝟙 _ := by
    rw [← Category.assoc, key]; exact b.2
  have hψ : Spec.map φ ≫ Spec.map (Spec.preimage g) = 𝟙 _ := by rwa [Spec.map_preimage]
  have hψφ : Spec.preimage g ≫ φ = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hψ, Spec.map_id]
  have hbij : Function.Bijective φ.hom := by
    refine ⟨φ.hom.injective, fun c ↦ ⟨(Spec.preimage g).hom c, ?_⟩⟩
    change (Spec.preimage g ≫ φ).hom c = c
    rw [hψφ]; rfl
  have : IsIso φ := (ConcreteCategory.isIso_iff_bijective φ).2 hbij
  have : IsIso (Spec.map φ ≫ g) := by rw [hφg]; infer_instance
  exact IsIso.of_isIso_comp_left (Spec.map φ) g

/-- The image of an open immersion `k` with `k ≫ s` smooth lies in the smooth locus of `s`. -/
private lemma range_subset_smoothLocus {W P S : Scheme.{0}} (k : W ⟶ P) [IsOpenImmersion k]
    {s : P ⟶ S} (hk : Smooth (k ≫ s)) : Set.range k ⊆ smoothLocus s := by
  have : k.opensRange.ι = k.isoOpensRange.inv ≫ k := by
    rw [Iso.eq_inv_comp, Scheme.Hom.isoOpensRange_hom_ι]
  have h2 : Smooth (k.opensRange.ι ≫ s) := by rw [this, Category.assoc]; infer_instance
  exact fun _ hx ↦ le_smoothLocus s h2 hx

/-- **Smoothness of the closure of a slice off the centre.** Let `t : X ⟶ B` be a morphism over
`ℂ` from an open `X ⊆ Y`, `b` a `ℂ`-point of `B`, and suppose the fibre `X_b` is reduced and
smooth over `κ(b)` off `T`. Then a reduced closed subscheme `P ⊆ Y` whose trace on `X` is `X_b` is
smooth over `ℂ` at every point lying in `X` and off `T`. -/
private lemma mem_smoothLocus_of_preimage_range_eq_fiber {Y B : Scheme.{0}}
    {sY : Y ⟶ Spec (.of ℂ)} {sB : B ⟶ Spec (.of ℂ)} (X : Y.Opens) (t : (X : Scheme.{0}) ⟶ B)
    (ht : t ≫ sB = X.ι ≫ sY) (b : ComplexPoints sB) (T : Set Y) [IsReduced (t.fiber b.toScheme)]
    (hFsing : (singularLocus (t.fiberToSpecResidueField b.toScheme) : Set (t.fiber b.toScheme)) ⊆
      t.fiberι b.toScheme ⁻¹' (X.ι ⁻¹' T))
    (I : Y.IdealSheafData) [IsReduced I.subscheme]
    (hI : X.ι ⁻¹' Set.range I.subschemeι = t ⁻¹' {b.toScheme})
    (z : I.subscheme) (hzX : I.subschemeι z ∈ (X : Set Y)) (hzT : I.subschemeι z ∉ T) :
    z ∈ smoothLocus (I.subschemeι ≫ sY) := by
  have : IsClosedImmersion (t.fiberι b.toScheme) := .of_isPreimmersion _ (by
    rw [Scheme.Hom.range_fiberι]
    exact (isClosed_singleton_toScheme' b).preimage t.continuous)
  let J := I.subschemeι ∣_ X
  have hker : J.ker = (t.fiberι b.toScheme).ker := by
    rw [ker_eq_vanishingIdeal_closure_range, ker_eq_vanishingIdeal_closure_range]
    congr 2
    rw [Scheme.Hom.range_fiberι, range_morphismRestrict, hI]
  have := IsClosedImmersion.isIso_lift J (t.fiberι b.toScheme) hker
  set e := IsClosedImmersion.lift J (t.fiberι b.toScheme) hker.le
  have he : e ≫ J = t.fiberι b.toScheme := IsClosedImmersion.lift_fac _ _ _
  let z0 : (I.subschemeι ⁻¹ᵁ X : Scheme.{0}) := ⟨z, hzX⟩
  obtain ⟨w, hw⟩ := e.homeomorph.surjective z0
  have hwz : (I.subschemeι ⁻¹ᵁ X).ι (e w) = z := by rw [show e w = z0 from hw]; rfl
  have hJw : X.ι (t.fiberι b.toScheme w) = I.subschemeι z := by
    rw [← he, Scheme.Hom.comp_apply, ← hwz, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
      morphismRestrict_ι]
    rfl
  have hws : w ∈ smoothLocus (t.fiberToSpecResidueField b.toScheme) := by
    by_contra hws
    exact hzT (by rw [← hJw]; exact hFsing hws)
  obtain ⟨U, hwU, hU⟩ := mem_smoothLocus_iff.1 hws
  have hgiso := isIso_fromSpecResidueField_toScheme_comp b
  have hk : Smooth ((U.ι ≫ e ≫ (I.subschemeι ⁻¹ᵁ X).ι) ≫ I.subschemeι ≫ sY) := by
    have : (U.ι ≫ e ≫ (I.subschemeι ⁻¹ᵁ X).ι) ≫ I.subschemeι ≫ sY =
        (U.ι ≫ t.fiberToSpecResidueField b.toScheme) ≫
          (B.fromSpecResidueField b.toScheme ≫ sB) := by
      calc (U.ι ≫ e ≫ (I.subschemeι ⁻¹ᵁ X).ι) ≫ I.subschemeι ≫ sY =
            U.ι ≫ (e ≫ J) ≫ X.ι ≫ sY := by
            simp only [J, Category.assoc, morphismRestrict_ι_assoc]
        _ = U.ι ≫ t.fiberι b.toScheme ≫ t ≫ sB := by rw [he, ht]
        _ = _ := by rw [Scheme.Hom.fiber_fac_assoc]; simp only [Category.assoc]
    rw [this]
    infer_instance
  refine range_subset_smoothLocus (U.ι ≫ e ≫ (I.subschemeι ⁻¹ᵁ X).ι) hk
    ⟨(⟨w, hwU⟩ : (U : Scheme.{0})), ?_⟩
  change (I.subschemeι ⁻¹ᵁ X).ι (e w) = z
  exact hwz

/-- **The centre is nowhere the whole slice.** In the situation of `exists_trivializations_at`,
no open `Ω ∋ x` of `X^an` meets the fibre of `h^an` through `x ∈ T(ℂ)` only in `T^an`. -/
private lemma not_inter_fiber_subset_range_realize
    {Z X T B : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sB : B ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sX] [IsSeparated sX] [QuasiCompact sX]
    [LocallyOfFiniteType sB] [IsSeparated sB] [QuasiCompact sB] [SmoothOfRelativeDimension 1 sB]
    (f : Z ⟶ X) [IsProper f] [Surjective f] [Smooth (f ≫ sX)]
    (iT : T ⟶ X) [IsClosedImmersion iT] (U : X.Opens) (hU : (U : Set X) = (Set.range iT)ᶜ)
    [IsIso (f ∣_ U)] (h : X ⟶ B) (hh : h ≫ sB = sX) [IsFinite (iT ≫ h)] [Etale (iT ≫ h)]
    (s : Finset (MMP.Mori.PrimeDivisor Z))
    (hEs : (⋃ E ∈ s, (E.support : Set Z)) = f ⁻¹' Set.range iT)
    (hsnc : MMP.Mori.DivisorWithCoeffs.IsSNC (f ≫ sX) (∑ E ∈ s, Finsupp.single E (1 : ℤ)))
    (hstr : ∀ J ⊆ s, Smooth ((⨆ E ∈ J, E.idealSheaf).subschemeι ≫ f ≫ h))
    (x : ComplexPoints (iT ≫ sX)) {Ω : Set (ComplexPoints sX)} (hΩo : IsOpen Ω)
    (hxΩ : realize (sX := iT ≫ sX) iT rfl x ∈ Ω) :
    ¬ Ω ∩ realize h hh ⁻¹' {realize h hh (realize (sX := iT ≫ sX) iT rfl x)} ⊆
      Set.range (realize (sX := iT ≫ sX) iT rfl) := by
  intro hΩ
  obtain ⟨-, N, hNo, -, V, ⟨OV, -, hV⟩, hxV, hVτ, Φ, hΦ⟩ :=
    exists_trivializations_at f iT U hU h hh s hEs hsnc hstr x
  have hVΩ : ∀ y ∈ V, y ∈ Ω → y = realize (sX := iT ≫ sX) iT rfl x := fun y hyV hyΩ ↦
    hVτ.subset ⟨hyV, hΩ ⟨hyΩ, (hV ▸ hyV).2⟩⟩
  let N' : Set N := {n | ((Φ n).1 : ComplexPoints sX) ∈ Ω}
  have hN'o : IsOpen N' :=
    hΩo.preimage (continuous_subtype_val.comp (continuous_fst.comp Φ.continuous))
  let n0 : N := Φ.symm (⟨_, hxV⟩, ⟨0, Metric.mem_ball_self one_pos⟩)
  have hn0 : n0 ∈ N' := by
    change ((Φ (Φ.symm _)).1 : ComplexPoints sX) ∈ Ω
    rw [Homeomorph.apply_symm_apply]
    exact hxΩ
  have hW0τ : Subtype.val '' N' ⊆ Set.range (realize (sX := iT ≫ sX) iT rfl) := by
    rintro _ ⟨n, hn, rfl⟩
    exact (hΦ n).2 (hVΩ _ (Φ n).1.2 hn)
  obtain ⟨u, hu⟩ := surjective_realize_of_surjective (sX := sX) f (n0 : ComplexPoints sX)
  have hu' : u ∈ interior (realize (sX := f ≫ sX) f rfl ⁻¹'
      Set.range (realize (sX := iT ≫ sX) iT rfl)) :=
    interior_maximal (Set.preimage_mono hW0τ)
      ((hNo.isOpenMap_subtype_val _ hN'o).preimage (continuous_realize f rfl))
      (by rw [Set.mem_preimage, hu]; exact ⟨n0, hn0, rfl⟩)
  rwa [interior_preimage_range_realize_eq_empty f iT h hh s hEs hsnc hstr] at hu'

/-- If every nonempty subfamily of `s` has smooth intersection over `g`, so does every
subfamily: the empty intersection is the whole of `Z`. -/
private lemma smooth_subschemeι_iSup_comp {Z W : Scheme.{0}} (g : Z ⟶ W) (hg : Smooth g)
    (s : Finset (MMP.Mori.PrimeDivisor Z))
    (hstr : ∀ J ⊆ s, J.Nonempty → Smooth ((⨆ E ∈ J, E.idealSheaf).subschemeι ≫ g)) :
    ∀ J ⊆ s, Smooth ((⨆ E ∈ J, E.idealSheaf).subschemeι ≫ g) := by
  intro J hJ
  rcases J.eq_empty_or_nonempty with rfl | hJne
  · have : IsIso (⨆ E ∈ (∅ : Finset (MMP.Mori.PrimeDivisor Z)), E.idealSheaf).subschemeι := by
      rw [IsClosedImmersion.isIso_iff_ker_eq_bot, Scheme.IdealSheafData.ker_subschemeι]
      simp
    infer_instance
  · exact hstr J hJ hJne

/-- On a map into `C` with `C ∩ X = Xb ⊆ X`, the preimage of `Xbᶜ ∪ (T ∩ Xb)` is the complement
of the preimage of `X \ T`. -/
private lemma preimage_compl_union_inter_eq {P Y : Type*} (ι : P → Y) {C X Xb T : Set Y}
    (hXbX : Xb ⊆ X) (hC : C ∩ X = Xb) (hmem : ∀ z, ι z ∈ C) :
    ι ⁻¹' (Xbᶜ ∪ (T ∩ Xb)) = (ι ⁻¹' (X ∩ Tᶜ))ᶜ := by
  ext z
  have hz := hmem z
  simp only [Set.mem_preimage, Set.mem_union, Set.mem_compl_iff, Set.mem_inter_iff]
  constructor
  · rintro (hz' | ⟨hzT, -⟩) ⟨hzX, hzT'⟩
    · exact hz' (hC ▸ ⟨hz, hzX⟩)
    · exact hzT' hzT
  · intro H
    by_cases hzX : ι z ∈ X
    · exact Or.inr ⟨not_not.1 fun hzT ↦ H ⟨hzX, hzT⟩, hC ▸ ⟨hz, hzX⟩⟩
    · exact Or.inl fun hzb ↦ hzX (hXbX hzb)

/-- Let `ι : P ⟶ Y` be a closed immersion landing in the closure of `Xb ⊆ X`, with
`closure Xb ∩ X = Xb` and `T ∩ Xb` finite. Then every `ℂ`-point of `P` over `T ∩ Xb` is isolated
in the `ℂ`-points of `ι⁻¹(Xbᶜ ∪ (T ∩ Xb))`. -/
private lemma nhdsWithin_preimage_diff_eq_bot {Y P : Scheme.{0}} {sP : P ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sP] [IsSeparated sP] (ι : P ⟶ Y) [IsClosedImmersion ι] (X : Y.Opens)
    {Xb T : Set Y}
    (hXbX : Xb ⊆ X) (hclX : closure Xb ∩ X = Xb) (hmem : ∀ z, ι z ∈ closure Xb)
    (hfin : (T ∩ Xb).Finite) (x : ComplexPoints sP) (hx : ι x.toScheme ∈ T ∩ Xb) :
    𝓝[toScheme ⁻¹' (ι ⁻¹' (Xbᶜ ∪ (T ∩ Xb))) \ {x}] x = ⊥ := by
  have hAfin : (toScheme ⁻¹' (ι ⁻¹' (T ∩ Xb)) : Set (ComplexPoints sP)).Finite :=
    (hfin.preimage ι.isClosedEmbedding.injective.injOn).preimage toScheme_injective.injOn
  rw [← Filter.empty_mem_iff_bot, mem_nhdsWithin]
  refine ⟨toScheme ⁻¹' (ι ⁻¹' (X : Set Y)) ∩ (toScheme ⁻¹' (ι ⁻¹' (T ∩ Xb)) \ {x})ᶜ,
    ((X.isOpen.preimage ι.continuous).preimage continuous_toScheme).inter
      hAfin.diff.isClosed.isOpen_compl, ⟨hXbX hx.2, fun h' ↦ h'.2 rfl⟩, ?_⟩
  rintro y ⟨⟨hyX, hyA⟩, hyS, hyx⟩
  refine hyA ⟨?_, hyx⟩
  change ι y.toScheme ∈ T ∩ Xb
  rcases hyS with hyS | hyS
  · exact (hyS (hclX ▸ ⟨hmem _, hyX⟩)).elim
  · exact hyS

/-- **No component of the closure of a slice lies in `S_b`.** In the situation of
`not_inter_fiber_subset_range_realize`, let `P ⊆ Y` be a closed subscheme with underlying set the
closure of the slice `Xb = t⁻¹(b)`. No irreducible component of `P` lies in
`Xbᶜ ∪ (T ∩ Xb)`. -/
private lemma not_subset_preimage_of_mem_irreducibleComponents
    {Y Z W B : Scheme.{0}} (X : Y.Opens) {sX : (X : Scheme.{0}) ⟶ Spec (.of ℂ)}
    {sB : B ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sX] [IsSeparated sX] [QuasiCompact sX]
    [LocallyOfFiniteType sB] [IsSeparated sB] [QuasiCompact sB] [SmoothOfRelativeDimension 1 sB]
    (f : Z ⟶ X) [IsProper f] [Surjective f] [Smooth (f ≫ sX)]
    (iT : W ⟶ X) [IsClosedImmersion iT] (U : (X : Scheme.{0}).Opens)
    (hU : (U : Set X) = (Set.range iT)ᶜ) [IsIso (f ∣_ U)] (t : (X : Scheme.{0}) ⟶ B)
    (ht : t ≫ sB = sX) [IsFinite (iT ≫ t)] [Etale (iT ≫ t)]
    (s : Finset (MMP.Mori.PrimeDivisor Z))
    (hEs : (⋃ E ∈ s, (E.support : Set Z)) = f ⁻¹' Set.range iT)
    (hsnc : MMP.Mori.DivisorWithCoeffs.IsSNC (f ≫ sX) (∑ E ∈ s, Finsupp.single E (1 : ℤ)))
    (hstr : ∀ J ⊆ s, Smooth ((⨆ E ∈ J, E.idealSheaf).subschemeι ≫ f ≫ t))
    {TY : Set Y} (hrange : Set.range iT = X.ι ⁻¹' TY) (b : ComplexPoints sB) {Xb : Set Y}
    (hXb : Xb = X.ι '' (t ⁻¹' {b.toScheme})) (hXbX : Xb ⊆ X) (hclX : closure Xb ∩ X = Xb)
    (I : Y.IdealSheafData) (sP : I.subscheme ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sP]
    [QuasiCompact sP] (hrangeI : Set.range I.subschemeι = closure Xb)
    {C : Set I.subscheme} (hC : C ∈ irreducibleComponents I.subscheme) :
    ¬ C ⊆ I.subschemeι ⁻¹' (Xbᶜ ∪ (TY ∩ Xb)) := by
  intro hCS
  have hmemI : ∀ z, I.subschemeι z ∈ closure Xb := fun z ↦ hrangeI ▸ ⟨z, rfl⟩
  have : IsLocallyNoetherian I.subscheme := LocallyOfFiniteType.isLocallyNoetherian sP
  have : CompactSpace I.subscheme := QuasiCompact.compactSpace_of_compactSpace sP
  have : IsNoetherian I.subscheme := ⟨⟩
  obtain ⟨o, hoo, hone, hoC⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent C hC
  have hdense : Dense (I.subschemeι ⁻¹' Xb) := by
    rw [dense_iff_closure_eq,
      I.subschemeι.isClosedEmbedding.isInducing.closure_eq_preimage_closure_image,
      Set.image_preimage_eq_of_subset (by rw [hrangeI]; exact subset_closure), ← hrangeI,
      Set.preimage_range]
  obtain ⟨z0, hz0o, hz0Xb⟩ := hdense.inter_open_nonempty o hoo hone
  set O' := o ∩ I.subschemeι ⁻¹' (X : Set Y)
  have hO'o : IsOpen O' := hoo.inter (X.isOpen.preimage I.subschemeι.continuous)
  have hO'T : ∀ z ∈ O', I.subschemeι z ∈ TY ∩ Xb := by
    intro z hz
    rcases hCS (hoC hz.1) with h1 | h1
    · exact (h1 (hclX ▸ ⟨hmemI z, hz.2⟩)).elim
    · exact h1
  have : JacobsonSpace I.subscheme := LocallyOfFiniteType.jacobsonSpace sP
  obtain ⟨z1, hz1O', hz1c⟩ :=
    nonempty_inter_closedPoints (Z := O') ⟨z0, hz0o, hXbX hz0Xb⟩ hO'o.isLocallyClosed
  have hz1X : I.subschemeι z1 ∈ (X : Set Y) := hz1O'.2
  have hz1cX : IsClosed ({⟨I.subschemeι z1, hz1X⟩} : Set X) := by
    have h1 : IsClosed ({I.subschemeι z1} : Set Y) := by
      have := I.subschemeι.isClosedEmbedding.isClosedMap _ hz1c
      rwa [Set.image_singleton] at this
    convert h1.preimage X.ι.continuous using 1
    ext y
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    exact ⟨fun h ↦ h ▸ rfl, fun h ↦ Subtype.ext h⟩
  obtain ⟨xX, hxX⟩ := exists_toScheme_eq (sX := sX) hz1cX
  obtain ⟨xT, hxT⟩ : xX ∈ Set.range (realize (sX := iT ≫ sX) iT rfl) := by
    rw [mem_range_realize_iff_of_isClosedImmersion, hxX, hrange]
    exact (hO'T z1 hz1O').1
  obtain ⟨Oy, hOyo, hOy⟩ := I.subschemeι.isClosedEmbedding.isInducing.isOpen_iff.1 hO'o
  have hxΩ : X.ι (realize (sX := iT ≫ sX) iT rfl xT).toScheme ∈ Oy := by
    rw [hxT, hxX]
    exact (Set.ext_iff.1 hOy z1).2 hz1O'
  refine not_inter_fiber_subset_range_realize f iT U hU t ht s hEs hsnc hstr xT
    ((hOyo.preimage X.ι.continuous).preimage continuous_toScheme) hxΩ ?_
  rintro y ⟨hyΩ, hyb⟩
  have hytb : t y.toScheme = b.toScheme := by
    have hxb : t xX.toScheme = b.toScheme := by
      rw [hxX]
      obtain ⟨w, hw, hw'⟩ : I.subschemeι z1 ∈ X.ι '' (t ⁻¹' {b.toScheme}) :=
        hXb ▸ (hO'T z1 hz1O').2
      rwa [← show w = ⟨I.subschemeι z1, hz1X⟩ from Subtype.ext hw']
    rw [← toScheme_realize t ht, hyb, hxT]
    exact (toScheme_realize t ht xX).trans hxb
  obtain ⟨p, hp⟩ : X.ι y.toScheme ∈ Set.range I.subschemeι := by
    rw [hrangeI, hXb]
    exact subset_closure ⟨_, hytb, rfl⟩
  have hpO : p ∈ O' := by
    rwa [← hOy, Set.mem_preimage, hp]
  rw [mem_range_realize_iff_of_isClosedImmersion, hrange, Set.mem_preimage, ← hp]
  exact (hO'T p hpO).1

/-- **The closure of a slice.** In the situation of `not_inter_fiber_subset_range_realize`, over a
projective variety `Y ⊇ X`, let `P_b` be the reduced closure in `Y` of the slice `X_b = t⁻¹(b)`,
reduced and smooth off the finite set `T ∩ X_b`. Then `P_b` is projective and
`S_b = (P_b ∖ X_b) ∪ (T ∩ X_b)` is closed, contains the singular locus of `P_b` and no
irreducible component of it, and isolates every `ℂ`-point of `P_b` over `T ∩ X_b`. -/
private lemma closure_slice_conditions
    {Y Z W B : Scheme.{0}} [IsLocallyNoetherian Y] {sY : Y ⟶ Spec (.of ℂ)}
    (hY : AlgebraicGeometry.IsProjectiveVariety ℂ sY) {TY : Set Y} (hTY : IsClosed TY)
    (X : Y.Opens) {sX : (X : Scheme.{0}) ⟶ Spec (.of ℂ)} (hsX : sX = X.ι ≫ sY)
    {sB : B ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sX] [IsSeparated sX] [QuasiCompact sX]
    [LocallyOfFiniteType sB] [IsSeparated sB] [QuasiCompact sB] [SmoothOfRelativeDimension 1 sB]
    (f : Z ⟶ X) [IsProper f] [Surjective f] [Smooth (f ≫ sX)]
    (iT : W ⟶ X) [IsClosedImmersion iT] (hrange : Set.range iT = X.ι ⁻¹' TY)
    (U : (X : Scheme.{0}).Opens) (hU : (U : Set X) = (Set.range iT)ᶜ) [IsIso (f ∣_ U)]
    (t : (X : Scheme.{0}) ⟶ B) (ht : t ≫ sB = sX) [IsFinite (iT ≫ t)] [Etale (iT ≫ t)]
    (s : Finset (MMP.Mori.PrimeDivisor Z))
    (hEs : (⋃ E ∈ s, (E.support : Set Z)) = f ⁻¹' Set.range iT)
    (hsnc : MMP.Mori.DivisorWithCoeffs.IsSNC (f ≫ sX) (∑ E ∈ s, Finsupp.single E (1 : ℤ)))
    (hstr : ∀ J ⊆ s, Smooth ((⨆ E ∈ J, E.idealSheaf).subschemeι ≫ f ≫ t))
    (b : ComplexPoints sB)
    (hslice : IsNormal (t.fiber b.toScheme) ∧
      (t.fiberι b.toScheme ⁻¹' (X.ι ⁻¹' TY)).Finite ∧
      (singularLocus (t.fiberToSpecResidueField b.toScheme) : Set (t.fiber b.toScheme)) ⊆
        t.fiberι b.toScheme ⁻¹' (X.ι ⁻¹' TY)) :
    let Xb : Set Y := X.ι '' (t ⁻¹' {b.toScheme})
    let I := Scheme.IdealSheafData.vanishingIdeal ⟨closure Xb, isClosed_closure⟩
    let sP : I.subscheme ⟶ Spec (.of ℂ) := I.subschemeι ≫ sY
    IsReduced I.subscheme ∧ IsProjective sP ∧
    ∃ S : Closeds I.subscheme,
      (S : Set I.subscheme) = I.subschemeι ⁻¹' (Xbᶜ ∪ (TY ∩ Xb)) ∧
      singularLocus sP ≤ S ∧
      (∀ C ∈ irreducibleComponents I.subscheme, ¬ C ⊆ (S : Set I.subscheme)) ∧
      ∀ x : ComplexPoints sP, I.subschemeι x.toScheme ∈ TY ∩ Xb →
        x.toScheme ∈ S ∧
          𝓝[ComplexPoints.toScheme ⁻¹' (S : Set I.subscheme) \ {x}] x = ⊥ := by
  intro Xb I sP
  have : AlgebraicGeometry.IsVariety ℂ sY := hY.toIsVariety
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  obtain ⟨hFn, hFfin, hFsing⟩ := hslice
  have hpre : X.ι ⁻¹' closure Xb = t ⁻¹' {b.toScheme} := by
    rw [← X.ι.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image,
      ((isClosed_singleton_toScheme' b).preimage t.continuous).closure_eq]
  have hclX : closure Xb ∩ (X : Set Y) = Xb := by
    calc closure Xb ∩ (X : Set Y) = X.ι '' (X.ι ⁻¹' closure Xb) := by
          rw [Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι]
      _ = Xb := by rw [hpre]
  have hXbX : Xb ⊆ X := by rintro _ ⟨y, -, rfl⟩; exact y.2
  have hrangeI : Set.range I.subschemeι = closure Xb := by
    rw [Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hmemI : ∀ z, I.subschemeι z ∈ closure Xb := fun z ↦ hrangeI ▸ ⟨z, rfl⟩
  have hSeq := preimage_compl_union_inter_eq I.subschemeι (T := TY) hXbX hclX hmemI
  have hSc : IsClosed (I.subschemeι ⁻¹' (Xbᶜ ∪ (TY ∩ Xb))) := by
    rw [hSeq]
    exact ((X.isOpen.inter hTY.isOpen_compl).preimage I.subschemeι.continuous).isClosed_compl
  have hTbfin : (TY ∩ Xb).Finite := by
    refine ((hFfin.image (t.fiberι b.toScheme)).image X.ι).subset ?_
    rintro _ ⟨hyT, ⟨y, hy, rfl⟩⟩
    obtain ⟨w, rfl⟩ : y ∈ Set.range (t.fiberι b.toScheme) := by
      rwa [Scheme.Hom.range_fiberι]
    exact ⟨_, ⟨w, hyT, rfl⟩, rfl⟩
  refine ⟨inferInstance, (isProjective_iff_isProjectiveMorphism_of_isAffine _).2
      (isProjectiveMorphism_isClosedImmersion_comp _ _ hY.isProjective), ⟨_, hSc⟩, rfl, ?_,
    fun C hC ↦ not_subset_preimage_of_mem_irreducibleComponents X f iT U hU t ht s hEs hsnc hstr
      hrange b rfl hXbX hclX I sP hrangeI hC,
    fun x hx ↦ ⟨Or.inr hx, nhdsWithin_preimage_diff_eq_bot I.subschemeι X hXbX hclX hmemI
      hTbfin x hx⟩⟩
  intro z hz
  by_contra hzS
  have hzS' : I.subschemeι z ∈ (X : Set Y) ∩ TYᶜ := by
    have : z ∉ (I.subschemeι ⁻¹' ((X : Set Y) ∩ TYᶜ))ᶜ := by
      rwa [← hSeq]
    simpa using this
  exact (mem_singularLocus_iff.1 hz) (mem_smoothLocus_of_preimage_range_eq_fiber X t
    (ht.trans hsX) b TY hFsing I (by rwa [hrangeI]) z hzS'.1 hzS'.2)

end MMP.Fourfold.GenericTopologicalTriviality

end

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace

namespace MMP.Fourfold

open MMP.Mori MMP.Analytic MMP.Analytic.ComplexPoints MMP.Resolution

open GenericTopologicalTriviality in
attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral in
/-- **Generic topological triviality along a singular curve.** For a local setting
`(Y, Θ, T, π)` there are a Zariski open `X ⊆ Y`, a smooth curve `B` with `t : X ⟶ B` over `ℂ`,
and a smooth blow-up sequence `β` on `π⁻¹(X)` with `f = π_X ∘ β : Z ⟶ X` such that:
1. `T° = T ∩ X` is nonempty, smooth, finite étale over `B`, and `X ∩ Y_reg = X ∖ T`;
2. `Z` is a smooth variety, `f` is projective and an isomorphism over `X ∖ T`;
3. every `x ∈ T°(ℂ)` has an open neighbourhood `W ≅ Δ` in `T°` with
   `f⁻¹(x) × W ≅ f⁻¹(W)` over `W`;
4. every `x ∈ T°(ℂ)`, `b = t(x)`, has an open neighbourhood `N` in `X^an`, an open neighbourhood
   `V` of `x` in `X_b` with `V ∩ T = {x}`, and `(N, N ∩ T) ≅ (V × Δ, {x} × Δ)`;
5. for every `b ∈ B(ℂ)`, the reduced closure `P_b` of `X_b` in `Y` and
   `S_b = (P_b ∖ X_b) ∪ T_b` satisfy the hypotheses of
   `MMP.Fourfold.exists_cofinal_isIso_punctured_cohomology_of_isolated` at every point of `T_b`.
-/
@[mmp "lem_mmp_curvels_generic_trivializations"]
public theorem IsLocalSetting.exists_generic_trivializations {Y Yt : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)} {Θ : QDivisor Y}
    {T : IrreducibleCloseds Y} {π : Yt ⟶ Y} (h : IsLocalSetting sY Θ T π) :
    ∃ (X : Y.Opens) (B : Scheme.{0}) (sB : B ⟶ Spec (.of ℂ)) (t : (X : Scheme.{0}) ⟶ B)
      (ht : t ≫ sB = X.ι ≫ sY) (β : ClosedBlowupSequence.{0} (π ⁻¹ᵁ X : Scheme.{0})),
      let sX : (X : Scheme.{0}) ⟶ Spec (.of ℂ) := X.ι ≫ sY
      let To : (curveScheme T).Opens := curveι T ⁻¹ᵁ X
      let iT : (To : Scheme.{0}) ⟶ X := curveι T ∣_ X
      let f : β.target ⟶ X := β.toBase ≫ π ∣_ X
      let Tc : Y.Opens := ⟨(T : Set Y)ᶜ, T.isClosed.isOpen_compl⟩
      let fan : analyticSpace (f ≫ sX) ⟶ analyticSpace sX := analyticMap f rfl
      let iTan : analyticSpace (iT ≫ sX) ⟶ analyticSpace sX := analyticMap iT rfl
      let tan : analyticSpace sX ⟶ analyticSpace sB := analyticMap t ht
      -- `B` is a smooth curve and `Z` a smooth variety, projective over `X`
      (MMP.Mori.IsVariety ℂ sB ∧ IsSmoothScheme sB ∧ topologicalKrullDim B = 1) ∧
      (MMP.Mori.IsVariety ℂ (f ≫ sX) ∧ IsSmoothScheme (f ≫ sX) ∧ IsProjectiveMorphism f) ∧
      -- (1)
      ((To : Set (curveScheme T)).Nonempty ∧ To ≤ smoothLocus (curveι T ≫ sY) ∧
        IsFinite (iT ≫ t) ∧ Etale (iT ≫ t) ∧
        (X : Set Y) ∩ smoothLocus sY = (X : Set Y) \ T) ∧
      -- (2)
      (β.IsSmooth (π ∣_ X ≫ sX) ∧ IsBiregular f (X.ι ⁻¹ᵁ Tc)) ∧
      -- (3)
      (∀ x : ComplexPoints (iT ≫ sX), ∃ W : Set (ComplexPoints (iT ≫ sX)),
        IsOpen W ∧ x ∈ W ∧ Nonempty (W ≃ₜ Metric.ball (0 : ℂ) 1) ∧
        ∃ Φ : (fan ⁻¹' {iTan x}) × W ≃ₜ (fan ⁻¹' (iTan '' W)),
          ∀ p, fan (Φ p) = iTan p.2) ∧
      -- (4)
      (∀ x : ComplexPoints (iT ≫ sX), ∃ N : Set (ComplexPoints sX), IsOpen N ∧ iTan x ∈ N ∧
        ∃ V : Set (ComplexPoints sX),
          (∃ O : Set (ComplexPoints sX), IsOpen O ∧ V = O ∩ tan ⁻¹' {tan (iTan x)}) ∧
          iTan x ∈ V ∧ V ∩ Set.range iTan = {iTan x} ∧
          ∃ Φ : N ≃ₜ V × Metric.ball (0 : ℂ) 1,
            ∀ n : N, (n : ComplexPoints sX) ∈ Set.range iTan ↔
              ((Φ n).1 : ComplexPoints sX) = iTan x) ∧
      -- (5)
      (∀ b : ComplexPoints sB,
        let Xb : Set Y := X.ι '' (t ⁻¹' {b.toScheme})
        let I := Scheme.IdealSheafData.vanishingIdeal ⟨closure Xb, isClosed_closure⟩
        let sP : I.subscheme ⟶ Spec (.of ℂ) := I.subschemeι ≫ sY
        IsReduced I.subscheme ∧ IsProjective sP ∧
        ∃ S : Closeds I.subscheme,
          (S : Set I.subscheme) = I.subschemeι ⁻¹' (Xbᶜ ∪ ((T : Set Y) ∩ Xb)) ∧
          singularLocus sP ≤ S ∧
          (∀ C ∈ irreducibleComponents I.subscheme, ¬ C ⊆ (S : Set I.subscheme)) ∧
          ∀ x : ComplexPoints sP, I.subschemeι x.toScheme ∈ (T : Set Y) ∩ Xb →
            x.toScheme ∈ S ∧
              𝓝[ComplexPoints.toScheme ⁻¹' (S : Set I.subscheme) \ {x}] x = ⊥) := by
  obtain ⟨X, B, t, hXT, ht, hfin, het, hslice, β, hβ, hproj, hres, hiso, hsm, s, hs, hsnc,
    hstr, hEp⟩ := h.exists_relativeSNC_resolution
  obtain ⟨p, hpX, hpT⟩ := hXT
  have : Nonempty B := ⟨t ⟨p, hpX⟩⟩
  have : Nonempty X := ⟨⟨p, hpX⟩⟩
  refine ⟨X, B, B.ι ≫ (𝔸(Unit; Spec (.of ℂ)) ↘ Spec (.of ℂ)), t, ht, β, ?_⟩
  intro sX To iT f Tc fan iTan tan
  have : AlgebraicGeometry.IsVariety ℂ sY := h.isProjectiveVariety.toIsVariety
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  obtain ⟨e, he⟩ := exists_iso_restrict_subschemeι_vanishingIdeal ⟨T, T.isClosed⟩ X
  have he' : e.hom ≫ _ = iT := he
  have hfinT : IsFinite (iT ≫ t) := by rw [← he', Category.assoc]; infer_instance
  have hetT : Etale (iT ≫ t) := by rw [← he', Category.assoc]; infer_instance
  obtain ⟨hBv, hBsm, hBdim⟩ := isVariety_isSmoothScheme_opens_affineLine B
  have hsmT : Smooth (iT ≫ sX) := by
    have : Smooth (B.ι ≫ 𝔸(Unit; Spec (.of ℂ)) ↘ Spec (.of ℂ)) := hBsm.smooth
    have heq : iT ≫ sX = (iT ≫ t) ≫ B.ι ≫ 𝔸(Unit; Spec (.of ℂ)) ↘ Spec (.of ℂ) := by
      rw [Category.assoc, ht]
    rw [heq]
    infer_instance
  have : IsProper f := hres.isProper
  have : Smooth (f ≫ sX) := hres.isSmoothScheme.smooth
  have : IsLocallyNoetherian 𝔸(Unit; Spec (.of ℂ)) :=
    LocallyOfFiniteType.isLocallyNoetherian (𝔸(Unit; Spec (.of ℂ)) ↘ Spec (.of ℂ))
  have : CompactSpace 𝔸(Unit; Spec (.of ℂ)) := Scheme.compactSpace_of_isAffine _
  have := smoothOfRelativeDimension_opens_affineLine B
  have hrange : Set.range iT = X.ι ⁻¹' (T : Set Y) := by
    rw [range_morphismRestrict, Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hU : ((X.ι ⁻¹ᵁ Tc : (X : Scheme.{0}).Opens) : Set X) = (Set.range iT)ᶜ := by
    rw [hrange]; rfl
  have : IsIso (f ∣_ X.ι ⁻¹ᵁ Tc) := hiso _ rfl
  have hTne : ((X.ι ⁻¹ᵁ Tc : (X : Scheme.{0}).Opens) : Set X).Nonempty := by
    obtain ⟨y, hyX, hyT⟩ := exists_mem_notMem_of_topologicalKrullDim_ne T.isClosed
      (by rw [h.topologicalKrullDim_curve, h.topologicalKrullDim_eq]; decide) X.isOpen
      ⟨p, hpX⟩
    exact ⟨⟨y, hyX⟩, hyT⟩
  have : Surjective f := surjective_of_isIso_morphismRestrict f _ hTne
  have hEs : (⋃ E ∈ s, (E.support : Set β.target)) = f ⁻¹' Set.range iT := by
    rwa [hrange]
  have hstr' := smooth_subschemeι_iSup_comp (f ≫ t) hsm s hstr
  have Htriv := fun x ↦ exists_trivializations_at f iT _ hU t ht s hEs hsnc hstr' x
  refine ⟨⟨hBv, hBsm, hBdim⟩, ⟨?_, hres.isSmoothScheme, hproj⟩, ⟨?_, ?_, hfinT, hetT, ?_⟩,
    ⟨?_, hiso _ rfl⟩, fun x ↦ (Htriv x).1, fun x ↦ (Htriv x).2, ?_⟩
  · exact (isVariety_iff ℂ _).2
      ⟨isIntegral_of_isSmoothResolution hres, inferInstance, inferInstance, inferInstance⟩
  · obtain ⟨q, hq⟩ : p ∈ Set.range (curveι T) := by
      rw [Scheme.IdealSheafData.range_subschemeι,
        Scheme.IdealSheafData.coe_support_vanishingIdeal]
      exact hpT
    exact ⟨q, show curveι T q ∈ X from hq ▸ hpX⟩
  · apply le_smoothLocus
    have : To.ι ≫ curveι T ≫ sY = iT ≫ sX := by
      simp only [sX, iT, To, ← Category.assoc, morphismRestrict_ι]
    rwa [this]
  · ext y
    constructor
    · rintro ⟨hyX, hysm⟩
      exact ⟨hyX, fun hyT ↦ (mem_singularLocus_iff.1 (h.subset_singularLocus hyT)) hysm⟩
    · rintro ⟨hyX, hyT⟩
      exact ⟨hyX, mem_smoothLocus_of_isIso_restrict (sY := sY) X f hres.isSmoothScheme.smooth
        (X.ι ⁻¹ᵁ Tc) (y := ⟨y, hyX⟩) hyT⟩
  · simpa only [sX, ← Category.assoc, morphismRestrict_ι] using hβ
  · exact fun b ↦ closure_slice_conditions h.isProjectiveVariety T.isClosed X rfl f iT hrange _
      hU t ht s hEs hsnc hstr' b (hslice b.toScheme (isClosed_singleton_toScheme' b))

end MMP.Fourfold
