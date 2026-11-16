module

public import MMP.RingTheory.RegularLocalRing.QuotientRegularIff
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.Basic
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineProjModel
import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ZeroCycleDegree
import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineSmooth
import StacksFrontier.AlgebraicGeometry.Variety.Defs.Product
public import MMP.AlgebraicGeometry.MMP.Fourfold.Defs
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentThree.DerivedChowFourierMukai

/-!
# Products with a line

Let `Y` be a normal variety over a field `k` and `L` the affine line `𝔸¹_k` or the projective
line `ℙ¹_k`. The first projection `pr : Y × L ⟶ Y` is the base change of the smooth, surjective
structure morphism of `L`, so it is smooth and surjective, and `Y × L` is again a normal variety,
of dimension `dim Y + 1`. Base change along `pr` carries `q : Y₁ ⟶ Y` to `q × id_L`, so étale,
projective, birational and small morphisms to `Y` give morphisms of the same kind to `Y × L`.

## Main results

* `MMP.Fourfold.smooth_geometricallyIrreducible_isVariety_dim_line`: the line is a smooth,
  geometrically irreducible variety of dimension one.
* `MMP.Fourfold.product_line_basic`: smoothness and surjectivity of `pr`, normality, dimension,
  (quasi-)projectivity and singular locus of `Y × L`, and the behaviour of `q × id_L`.

## Implementation notes

* The line is any `k`-scheme `L` with a `k`-isomorphism to `AlgebraicGeometry.projectiveLine k`
  or to `𝔸(PUnit; Spec k)`, and `Y × L` is the pull-back of the two structure morphisms, a
  `k`-scheme through `pr ≫ s_Y`.
* The source works over `ℂ`; the statements hold over an arbitrary field `k`.
-/

open CategoryTheory AlgebraicGeometry Limits MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Fourfold

/-- The projective line over `k` is geometrically irreducible. -/
private theorem geometricallyIrreducible_projectiveLine' (k : Type u) [Field k] :
    GeometricallyIrreducible (projectiveLine k ↘ Spec (.of k)) := by
  let σ : Spec (.of k) ⟶ projectiveLine k :=
    Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))) ≫ projectiveLineXChart k
  have hσ : σ ≫ (projectiveLine k ↘ Spec (.of k)) = 𝟙 _ := by
    simp only [σ, Category.assoc]
    erw [projectiveLineChart_comp_structureMorphism_algebraMap k (projectiveLineXIndex k)]
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext x
    simp
  exact geometricallyIrreducible_of_geometricallyConnected_of_smooth _
    (geometricallyConnected_of_connectedSpace_of_section _ σ hσ)

/-- The structure morphism of `𝔸¹_k` is `Spec` of the constant embedding `k → k[X]`. -/
private theorem specIso_hom_comp_C (k : Type u) [Field k] :
    (AffineSpace.SpecIso PUnit.{u + 1} (.of k)).hom ≫
      Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial PUnit.{u + 1} k)) =
      𝔸(PUnit.{u + 1}; Spec (.of k)) ↘ Spec (.of k) := by
  rw [← Iso.eq_inv_comp]
  exact (AffineSpace.SpecIso_inv_over _).symm

/-- A `k`-scheme isomorphic over `k` to `ℙ¹_k` or `𝔸¹_k` is a smooth, geometrically irreducible
variety of dimension one. -/
public theorem smooth_geometricallyIrreducible_isVariety_dim_line {k : Type u} [Field k]
    {L : Scheme.{u}} (sL : L ⟶ Spec (.of k))
    (hL : (∃ e : L ≅ projectiveLine k, e.hom ≫ (projectiveLine k ↘ Spec (.of k)) = sL) ∨
      ∃ e : L ≅ 𝔸(PUnit.{u + 1}; Spec (.of k)),
        e.hom ≫ (𝔸(PUnit.{u + 1}; Spec (.of k)) ↘ Spec (.of k)) = sL) :
    Smooth sL ∧ GeometricallyIrreducible sL ∧ AlgebraicGeometry.IsVariety k sL ∧
      topologicalKrullDim L = 1 := by
  obtain ⟨M, s₀, e, rfl, hM⟩ : ∃ (M : Scheme.{u}) (s₀ : M ⟶ Spec (.of k)) (e : L ≅ M),
      sL = e.hom ≫ s₀ ∧ (Smooth s₀ ∧ GeometricallyIrreducible s₀ ∧
        AlgebraicGeometry.IsVariety k s₀ ∧ topologicalKrullDim M = 1) := by
    rcases hL with ⟨e, rfl⟩ | ⟨e, rfl⟩
    · exact ⟨_, _, e, rfl, inferInstance, geometricallyIrreducible_projectiveLine' k,
        inferInstance, topologicalKrullDim_projectiveLine k⟩
    · have hs : Smooth (Spec.map
          (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial PUnit.{u + 1} k))) := by
        rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
        exact RingHom.smooth_algebraMap.mpr
          (⟨inferInstance, inferInstance⟩ : Algebra.Smooth k (MvPolynomial PUnit.{u + 1} k))
      refine ⟨_, _, e, rfl, specIso_hom_comp_C k ▸ inferInstance, inferInstance, ⟨⟩, ?_⟩
      rw [(AffineSpace.SpecIso PUnit (.of k)).hom.homeomorph.isHomeomorph.topologicalKrullDim_eq]
      change topologicalKrullDim (PrimeSpectrum (MvPolynomial PUnit.{u + 1} k)) = 1
      rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
        MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
      simp
  obtain ⟨h₁, h₂, h₃, h₄⟩ := hM
  have : IsIntegral M := h₃.toIsIntegral
  have : Nonempty L := ⟨e.inv.base (Nonempty.some inferInstance)⟩
  refine ⟨inferInstance,
    (MorphismProperty.cancel_left_of_respectsIso @GeometricallyIrreducible e.hom s₀).2 h₂,
    @AlgebraicGeometry.IsVariety.mk _ _ _ _ (isIntegral_of_isOpenImmersion e.hom) inferInstance
      inferInstance inferInstance, ?_⟩
  rw [e.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq, h₄]

/-- H-projectivity is invariant under precomposition with an isomorphism. -/
private theorem isProjectiveMorphism_iso_comp {X X' S : Scheme.{u}} (e : X' ≅ X) {f : X ⟶ S}
    (hf : IsProjectiveMorphism f) : IsProjectiveMorphism (e.hom ≫ f) := by
  obtain ⟨n, i, hi, rfl⟩ := hf
  exact ⟨n, e.hom ≫ i, inferInstance, by simp⟩

/-- `q × id_L` is the base change of `q` along the projection `Y × L ⟶ Y`. -/
private theorem isPullback_map_fst {k : Type u} [Field k] {Y L Y₁ : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) (sL : L ⟶ Spec (.of k)) (q : Y₁ ⟶ Y) :
    IsPullback (pullback.map (q ≫ sY) sL sY sL q (𝟙 L) (𝟙 _) (by simp) (by simp))
      (pullback.fst (q ≫ sY) sL) (pullback.fst sY sL) q := by
  refine IsPullback.of_right ?_ (by simp) (IsPullback.of_hasPullback sY sL).flip
  simpa using (IsPullback.of_hasPullback (q ≫ sY) sL).flip

/-- The product of a normal variety with a smooth geometrically irreducible variety is a normal
variety. -/
private theorem isNormalVariety_pullback {k : Type u} [Field k] {Z L : Scheme.{u}}
    (sZ : Z ⟶ Spec (.of k)) (sL : L ⟶ Spec (.of k)) [Smooth sL] [GeometricallyIrreducible sL]
    [AlgebraicGeometry.IsVariety k sL] (hZ : IsNormalVariety k sZ) :
    IsNormalVariety k (pullback.fst sZ sL ≫ sZ) := by
  obtain ⟨hvZ, hnZ⟩ := hZ
  have hIZ : IsIntegral Z := hvZ.toIsIntegral
  have hnP : IsNormal (pullback sZ sL : Scheme.{u}) := isNormal_of_smooth (pullback.fst sZ sL)
  have hirr : IrreducibleSpace (pullback sZ sL : Scheme.{u}) :=
    GeometricallyIrreducible.irreducibleSpace (pullback.fst sZ sL)
      (pullback.fst sZ sL).isOpenMap
  have hIP : IsIntegral (pullback sZ sL : Scheme.{u}) :=
    isIntegral_of_irreducibleSpace_of_isReduced _
  exact ⟨⟨⟩, hnP⟩

/-- A morphism of irreducible schemes which is an open immersion on a nonempty open is
birational. -/
private theorem isBirationalMorphism_of_isOpenImmersion_ι_comp {X Y : Scheme.{u}}
    [IrreducibleSpace X] [IrreducibleSpace Y] (f : X ⟶ Y) (U : X.Opens)
    (hU : (U : Set X).Nonempty) [IsOpenImmersion (U.ι ≫ f)] : IsBirationalMorphism f := by
  have hle : U ≤ f ⁻¹ᵁ (U.ι ≫ f).opensRange := fun x hx => ⟨⟨x, hx⟩, rfl⟩
  have hoi : IsOpenImmersion (f.resLE (U.ι ≫ f).opensRange U hle) := by
    have : IsOpenImmersion (f.resLE (U.ι ≫ f).opensRange U hle ≫ ((U.ι ≫ f).opensRange).ι) := by
      rw [Scheme.Hom.resLE_comp_ι]
      infer_instance
    exact IsOpenImmersion.of_comp _ ((U.ι ≫ f).opensRange).ι
  have hsurj : Surjective (f.resLE (U.ι ≫ f).opensRange U hle) := by
    refine ⟨fun ⟨y, ⟨x, hx⟩⟩ => ⟨x, Subtype.ext ?_⟩⟩
    erw [Scheme.Hom.coe_resLE_apply]
    exact hx
  obtain ⟨x, hx⟩ := hU
  exact MMP.Flips.isBirationalMorphism_of_isIso_resLE f U _ ⟨x, hx⟩ ⟨f x, hle hx⟩ hle
    ((isIso_iff_isOpenImmersion_and_surjective _).2 ⟨hoi, hsurj⟩)

/-- Biregularity over `V` is inherited by a base change, over the preimage of `V`. -/
private theorem isBiregular_preimage_of_isPullback {P' P Y₁ Y : Scheme.{u}} {m : P' ⟶ P}
    {p' : P' ⟶ Y₁} {p : P ⟶ Y} {g : Y₁ ⟶ Y} (H : IsPullback m p' p g) {V : Y.Opens}
    (hV : IsBiregular g V) : IsBiregular m (p ⁻¹ᵁ V) := by
  have hUY : m ⁻¹ᵁ (p ⁻¹ᵁ V) = m ⁻¹ᵁ (p ⁻¹ᵁ V) ⊓ p' ⁻¹ᵁ (g ⁻¹ᵁ V) := by
    refine (inf_eq_left.2 ?_).symm
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, H.w]
  have H' := Scheme.Hom.isPullback_resLE H (US := V) (UT := g ⁻¹ᵁ V) (UX := p ⁻¹ᵁ V)
    le_rfl le_rfl hUY
  have hg : IsIso (g.resLE V (g ⁻¹ᵁ V) le_rfl) := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    exact hV
  rw [IsBiregular, ← Scheme.Hom.resLE_eq_morphismRestrict]
  exact MorphismProperty.of_isPullback (P := MorphismProperty.isomorphisms Scheme) H'.flip hg

/-- The exceptional set of a base change lies over the exceptional set. -/
private theorem exceptionalSet_subset_preimage_of_isPullback {P' P Y₁ Y : Scheme.{u}}
    {m : P' ⟶ P} {p' : P' ⟶ Y₁} {p : P ⟶ Y} {g : Y₁ ⟶ Y} (H : IsPullback m p' p g) :
    (exceptionalSet m : Set P') ⊆ p' ⁻¹' (exceptionalSet g : Set Y₁) := by
  intro x hx hgx
  apply hx
  apply le_biregularLocus (isBiregular_preimage_of_isPullback H (isBiregular_biregularLocus g))
  change p (m x) ∈ biregularLocus g
  rwa [← Scheme.Hom.comp_apply, H.w, Scheme.Hom.comp_apply]

/-- An open immersion `W ⟶ Y` through `g` base changes to an open immersion. -/
private theorem isOpenImmersion_ι_comp_of_isPullback {P' P Y₁ Y : Scheme.{u}}
    {m : P' ⟶ P} {p' : P' ⟶ Y₁} {p : P ⟶ Y} {g : Y₁ ⟶ Y} (H : IsPullback m p' p g)
    (W : Y₁.Opens) [IsOpenImmersion (W.ι ≫ g)] : IsOpenImmersion ((p' ⁻¹ᵁ W).ι ≫ m) := by
  have hUY : p' ⁻¹ᵁ W = m ⁻¹ᵁ ⊤ ⊓ p' ⁻¹ᵁ W := by rw [Scheme.Hom.preimage_top, top_inf_eq]
  have H' := Scheme.Hom.isPullback_resLE H (US := ⊤) (UT := W) (UX := ⊤) le_top le_top hUY
  have hg : IsOpenImmersion (g.resLE ⊤ W le_top) := by
    have e := Scheme.Hom.resLE_comp_ι g (U := ⊤) (V := W) le_top
    have : IsOpenImmersion (g.resLE ⊤ W le_top ≫ (⊤ : Y.Opens).ι) := by
      rw [e]
      infer_instance
    exact IsOpenImmersion.of_comp _ (⊤ : Y.Opens).ι
  have := MorphismProperty.of_isPullback (P := @IsOpenImmersion) H'.flip hg
  rw [← Scheme.Hom.resLE_comp_ι m (U := ⊤) (V := p' ⁻¹ᵁ W) le_top]
  infer_instance

/-- Generizations lift along a generalizing map, so the coheight of a point bounds that of
its image. -/
private theorem le_coheight_of_le_coheight_apply {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : GeneralizingMap f) (n : ℕ) :
    ∀ x : X, (n : ℕ∞) ≤ Order.coheight (f x) → (n : ℕ∞) ≤ Order.coheight x := by
  induction n with
  | zero => simp
  | succ n ih =>
    intro x hx
    have h1 : ¬ Order.coheight (f x) ≤ n := fun h => by
      have := hx.trans h
      norm_cast at this
      omega
    rw [Order.coheight_le_coe_iff] at h1
    push Not at h1
    obtain ⟨b, hb, hnb⟩ := h1
    obtain ⟨x', hx'x, hfx'⟩ := hf (show b ⤳ f x from hb.le)
    have hlt : x < x' := by
      refine lt_of_le_not_ge (show x ≤ x' from hx'x) fun h => hb.not_ge ?_
      rw [← hfx']
      exact (show x ⤳ x' from h).map f.continuous
    calc ((n + 1 : ℕ) : ℕ∞) = (n : ℕ∞) + 1 := by norm_cast
      _ ≤ Order.coheight x' + 1 := add_le_add_left (ih x' (hfx' ▸ hnb)) 1
      _ ≤ Order.coheight x := Order.coheight_add_one_le hlt

/-- The line embeds in `ℙ¹_k` over `k` by a quasi-compact immersion. -/
private theorem exists_immersion_line {k : Type u} [Field k] {L : Scheme.{u}}
    (sL : L ⟶ Spec (.of k))
    (hL : (∃ e : L ≅ projectiveLine k, e.hom ≫ (projectiveLine k ↘ Spec (.of k)) = sL) ∨
      ∃ e : L ≅ 𝔸(PUnit.{u + 1}; Spec (.of k)),
        e.hom ≫ (𝔸(PUnit.{u + 1}; Spec (.of k)) ↘ Spec (.of k)) = sL) :
    ∃ j : L ⟶ projectiveSpaceOver 1 (Spec (.of k)), IsImmersion j ∧ QuasiCompact j ∧
      j ≫ (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k)) = sL := by
  rcases hL with ⟨e, rfl⟩ | ⟨e, rfl⟩
  · exact ⟨e.hom ≫ (projectiveLineIsoProjectiveSpaceOver k).hom, inferInstance, inferInstance,
      by rw [Category.assoc, projectiveLineIsoProjectiveSpaceOver_hom_fst]⟩
  · let φ : Polynomial k ≃ₐ[k] MvPolynomial PUnit.{u + 1} k :=
      (MvPolynomial.pUnitAlgEquiv k).symm
    let c : 𝔸(PUnit.{u + 1}; Spec (.of k)) ⟶ Spec (.of (Polynomial k)) :=
      (AffineSpace.SpecIso PUnit.{u + 1} (.of k)).hom ≫
        Spec.map (CommRingCat.ofHom φ.toRingEquiv.toRingHom)
    have hφ : (CommRingCat.ofHom (algebraMap k (Polynomial k)) ≫
        CommRingCat.ofHom φ.toRingEquiv.toRingHom : CommRingCat.of k ⟶ _) =
        CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial PUnit.{u + 1} k) := by
      ext x
      simp [φ]
    have hcover : c ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) =
        𝔸(PUnit.{u + 1}; Spec (.of k)) ↘ Spec (.of k) := by
      rw [← specIso_hom_comp_C k, ← hφ, Spec.map_comp]
      rfl
    have hc : IsIso (Spec.map (CommRingCat.ofHom φ.toRingEquiv.toRingHom)) :=
      inferInstanceAs (IsIso (Spec.map (φ.toRingEquiv.toCommRingCatIso.hom)))
    refine ⟨e.hom ≫ c ≫ projectiveLineXChart k ≫ (projectiveLineIsoProjectiveSpaceOver k).hom,
      inferInstance, inferInstance, ?_⟩
    simp only [Category.assoc, projectiveLineIsoProjectiveSpaceOver_hom_fst]
    erw [projectiveLineChart_comp_structureMorphism_algebraMap k (projectiveLineXIndex k)]
    rw [hcover]

/-- The product of a quasi-projective variety with a line is quasi-projective. -/
private theorem isQuasiProjectiveVariety_pullback_line {k : Type u} [Field k] {Y L : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) (sL : L ⟶ Spec (.of k))
    (hL : (∃ e : L ≅ projectiveLine k, e.hom ≫ (projectiveLine k ↘ Spec (.of k)) = sL) ∨
      ∃ e : L ≅ 𝔸(PUnit.{u + 1}; Spec (.of k)),
        e.hom ≫ (𝔸(PUnit.{u + 1}; Spec (.of k)) ↘ Spec (.of k)) = sL)
    (hvP : AlgebraicGeometry.IsVariety k (pullback.fst sY sL ≫ sY))
    (hQ : IsQuasiProjectiveVariety k sY) :
    IsQuasiProjectiveVariety k (pullback.fst sY sL ≫ sY) := by
  obtain ⟨-, hqY⟩ := (isQuasiProjectiveVariety_iff k sY).1 hQ
  rw [isQuasiProjective_iff_isHQuasiProjective_of_isAffine] at hqY
  obtain ⟨n, i, hi, hiq, hio⟩ := hqY
  obtain ⟨j, hj, hjq, hjo⟩ := exists_immersion_line sL hL
  obtain ⟨s, hs, hsover⟩ :=
    Stacks.AlgebraicGeometry.SegreProdIso.exists_segreEmbedding n 1 (Spec (.of k))
  have : MorphismProperty.IsStableUnderComposition @IsImmersion :=
    ⟨fun a c ha hc => @IsImmersion.comp _ _ _ a c ha hc⟩
  have hij := MorphismProperty.pullbackMap (P := @IsImmersion) hi hj hio.symm hjo.symm
  have hijq := MorphismProperty.pullbackMap (P := @QuasiCompact) hiq hjq hio.symm hjo.symm
  refine (isQuasiProjectiveVariety_iff k _).2 ⟨hvP, ?_⟩
  rw [isQuasiProjective_iff_isHQuasiProjective_of_isAffine]
  refine ⟨_, _ ≫ s, @IsImmersion.comp _ _ _ _ _ hij inferInstance,
    @quasiCompact_comp _ _ _ _ _ hijq inferInstance, ?_⟩
  rw [Category.assoc, hsover, pullback.lift_fst_assoc, Category.assoc, hio]

/-- **Basic properties of products with a line.** Let `Y` be a normal variety over `k` and `L`
a `k`-scheme isomorphic over `k` to `ℙ¹_k` or `𝔸¹_k`, with `pr : Y × L ⟶ Y` the first projection.
1. `pr` is smooth and surjective, `Y × L` is a normal variety of dimension `dim Y + 1`, projective
   if `Y` is and `L ≅ ℙ¹_k`, and quasi-projective if `Y` is.
2. `Sing (Y × L) = pr⁻¹ (Sing Y)`.
3. If `q : Y₁ ⟶ Y` is étale, so is `q × id_L`. If `g : Y₁ ⟶ Y` is a projective birational
   morphism of normal varieties, then `g × id_L` is projective and birational, its exceptional
   set lies over `Ex g`, and it is small when `g` is. -/
@[mmp "lem_mmp_indexb_product_basic"]
public theorem product_line_basic {k : Type u} [Field k] {Y L : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) (sL : L ⟶ Spec (.of k)) (hY : IsNormalVariety k sY)
    (hL : (∃ e : L ≅ projectiveLine k, e.hom ≫ (projectiveLine k ↘ Spec (.of k)) = sL) ∨
      ∃ e : L ≅ 𝔸(PUnit.{u + 1}; Spec (.of k)),
        e.hom ≫ (𝔸(PUnit.{u + 1}; Spec (.of k)) ↘ Spec (.of k)) = sL) :
    -- (1)
    (Smooth (pullback.fst sY sL) ∧ Surjective (pullback.fst sY sL) ∧
      IsNormalVariety k (pullback.fst sY sL ≫ sY) ∧
      topologicalKrullDim ↥(pullback sY sL : Scheme.{u}) = topologicalKrullDim Y + 1 ∧
      ((∃ e : L ≅ projectiveLine k, e.hom ≫ (projectiveLine k ↘ Spec (.of k)) = sL) →
        Mori.IsProjectiveVariety k sY → Mori.IsProjectiveVariety k (pullback.fst sY sL ≫ sY)) ∧
      (IsQuasiProjectiveVariety k sY →
        IsQuasiProjectiveVariety k (pullback.fst sY sL ≫ sY))) ∧
    -- (2)
    ((Mori.singularLocus (pullback.fst sY sL ≫ sY) : Set ↥(pullback sY sL : Scheme.{u})) =
      pullback.fst sY sL ⁻¹' (Mori.singularLocus sY : Set Y)) ∧
    -- (3)
    (∀ {Y₁ : Scheme.{u}} (q : Y₁ ⟶ Y), Etale q →
      Etale (pullback.map (q ≫ sY) sL sY sL q (𝟙 L) (𝟙 _) (by simp) (by simp))) ∧
    (∀ {Y₁ : Scheme.{u}} (g : Y₁ ⟶ Y), IsNormalVariety k (g ≫ sY) →
      IsProjectiveMorphism g → IsBirationalMorphism g →
      IsProjectiveMorphism (pullback.map (g ≫ sY) sL sY sL g (𝟙 L) (𝟙 _) (by simp) (by simp)) ∧
      IsBirationalMorphism
        (pullback.map (g ≫ sY) sL sY sL g (𝟙 L) (𝟙 _) (by simp) (by simp)) ∧
      (exceptionalSet
          (pullback.map (g ≫ sY) sL sY sL g (𝟙 L) (𝟙 _) (by simp) (by simp)) :
          Set ↥(pullback (g ≫ sY) sL : Scheme.{u})) ⊆
        pullback.fst (g ≫ sY) sL ⁻¹' (exceptionalSet g : Set Y₁) ∧
      (IsSmallMorphism (g ≫ sY) sY g →
        IsSmallMorphism (pullback.fst (g ≫ sY) sL ≫ g ≫ sY) (pullback.fst sY sL ≫ sY)
          (pullback.map (g ≫ sY) sL sY sL g (𝟙 L) (𝟙 _) (by simp) (by simp)))) := by
  obtain ⟨hsm, hgi, hvL, hdL⟩ := smooth_geometricallyIrreducible_isVariety_dim_line sL hL
  have hnvP := isNormalVariety_pullback sY sL hY
  have hvY := hY.1
  have hIY : IsIntegral Y := hvY.toIsIntegral
  have hvP : AlgebraicGeometry.IsVariety k (pullback.fst sY sL ≫ sY) := hnvP.1
  refine ⟨⟨inferInstance, inferInstance, hnvP, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [topologicalKrullDim_pullback_of_isVariety k sY sL, hdL]
  · rintro ⟨e, rfl⟩ hPY
    have hpL := isProjectiveMorphism_iso_comp e
      ⟨1, (projectiveLineIsoProjectiveSpaceOver k).hom, inferInstance,
        projectiveLineIsoProjectiveSpaceOver_hom_fst k⟩
    have hfst : IsProjectiveMorphism
        (pullback.fst sY (e.hom ≫ (projectiveLine k ↘ Spec (.of k)))) := by
      rw [← pullbackSymmetry_hom_comp_snd]
      exact isProjectiveMorphism_iso_comp _ (hpL.baseChange sY)
    exact (AlgebraicGeometry.isProjectiveVariety_iff k _).2 ⟨hvP, hfst.comp hPY.isProjective⟩
  · exact isQuasiProjectiveVariety_pullback_line sY sL hL hvP
  · exact (smoothLocus_comp_of_smooth sY (pullback.fst sY sL)).2
  · intro Y₁ q hq
    exact MorphismProperty.of_isPullback (isPullback_map_fst sY sL q).flip hq
  · intro Y₁ g hg hpg hbg
    have hpm : IsProjectiveMorphism
        (pullback.map (g ≫ sY) sL sY sL g (𝟙 L) (𝟙 _) (by simp) (by simp)) := by
      rw [← (isPullback_map_fst sY sL g).flip.isoPullback_hom_snd]
      exact isProjectiveMorphism_iso_comp _ (hpg.baseChange _)
    have hnv₁ := isNormalVariety_pullback (g ≫ sY) sL hg
    have hI₁ : IsIntegral Y₁ := hg.1.toIsIntegral
    have hbm : IsBirationalMorphism
        (pullback.map (g ≫ sY) sL sY sL g (𝟙 L) (𝟙 _) (by simp) (by simp)) := by
      obtain ⟨W, ⟨w, hw⟩, hWo⟩ := hbg.exists_isOpenImmersion
      have := isOpenImmersion_ι_comp_of_isPullback (isPullback_map_fst sY sL g) W
      obtain ⟨x, hx⟩ := (pullback.fst (g ≫ sY) sL).surjective w
      exact isBirationalMorphism_of_isOpenImmersion_ι_comp _
        (pullback.fst (g ≫ sY) sL ⁻¹ᵁ W) ⟨x, show _ ∈ W from hx ▸ hw⟩
    have hex := exceptionalSet_subset_preimage_of_isPullback (isPullback_map_fst sY sL g)
    refine ⟨hpm, hbm, hex, fun hsm => ⟨hnv₁, hnvP, ?_, ?_, hbm, ?_⟩⟩
    · rw [← Category.assoc, (isPullback_map_fst sY sL g).w, Category.assoc]
    · exact isProper_of_isProjectiveMorphism _ hpm
    · rw [MMP.Flips.le_closedsCodimension_iff_le_coheight]
      intro x hx
      exact le_coheight_of_le_coheight_apply (pullback.fst (g ≫ sY) sL)
        (Flat.generalizingMap _) 2 x
        (MMP.Positivity.two_le_coheight_of_mem_exceptionalSet hsm.two_le_codimension (hex hx))

end MMP.Fourfold
