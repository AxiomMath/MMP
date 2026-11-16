module

public import MMP.AlgebraicGeometry.Resolution.BlowupSequence
public import MMP.AlgebraicGeometry.MMP.Fourfold.PuncturedLocalSystem
import MMP.AlgebraicGeometry.Resolution.Blowup.SmoothGeometry
import MMP.AlgebraicGeometry.Morphisms.Smooth.IrreducibleComponents
import StacksFrontier.AlgebraicGeometry.Blowup.CartierCentre
import StacksFrontier.AlgebraicGeometry.Blowup.RegularSurfaceBlowupGlobal
import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.CodimensionOne
import StacksFrontier.AlgebraicGeometry.Variety.Smooth.RegularStalk
import StacksFrontier.RingTheory.RegularLocalRing.UniqueFactorization
import StacksFrontier.AlgebraicGeometry.TwistedSheaf.Dimension
import StacksFrontier.AlgebraicGeometry.Curves.InseparableGenusChangeFunctionField
import MMP.AlgebraicGeometry.Resolution.Blowup.SmoothCanonical
import MMP.AlgebraicGeometry.Analytic.BlowupRetraction.PureCodimension

/-!
# The blowup retraction along a smooth centre, from the pure-codimension case

Let `V` be a smooth integral complex scheme, separated and of finite type, and `b : Bl_Z V ⟶ V`
the blowup of a nonzero ideal sheaf `Z` whose closed subscheme is smooth. The presheaf
`U ↦ H^q(U; ℚ)` on `V^an` is a retract of `U ↦ H^q(b⁻¹U; ℚ)`, provided this holds for every smooth
centre of pure codimension `c ≥ 2`.

The closed subscheme `Z` is smooth over `ℂ`, so its irreducible components are open and pairwise
disjoint, and finite in number. For a union `W` of some of them, the kernel `K_W` of `W ⟶ Z ⟶ V`
is a smooth centre with support the image of `W`; it is radical, so `K_{W ⊔ W'} = K_W * K_{W'}`
for disjoint `W` and `W'`. Blowing up `K_W * K_C` is blowing up `K_W` and then the pullback of
`K_C` ([Stacks, Tag 080A]), and since `b_{K_W}` is an isomorphism away from the support of
`K_W` ([Stacks, Tag 02OS]), the pullback of `K_C` is again a smooth irreducible centre on the
smooth scheme `Bl_{K_W} V`. An irreducible smooth centre has a single codimension: if it is at
least two the pure case applies, and if it is one the centre is an effective Cartier divisor (the
local rings of `V` being regular, hence factorial), whose blowup is an isomorphism
([Stacks, Tag 0807]). Retracts compose along the tower by pushing forward along the first
blowup.

## Main results

* `MMP.Fourfold.nonempty_retract_directImagePresheaf_blowUp_of_pure`: the retraction for a general
  smooth centre, granting the pure-codimension case.
* `MMP.Fourfold.nonempty_retract_directImagePresheaf_blowUp`: the retraction for a general smooth
  centre, the pure case being
  `MMP.Fourfold.nonempty_retract_directImagePresheaf_blowUp_of_codimension`.

## References

* [Stacks Project, Tag 080A](https://stacks.math.columbia.edu/tag/080A)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 0807](https://stacks.math.columbia.edu/tag/0807)
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open MMP.Fourfold MMP.Mori MMP.Analytic MMP.Analytic.ComplexPoints

namespace MMP.Fourfold

section TopRetract

variable {X Y Z : TopCat.{0}}

private lemma directImageRestriction_comp {W : TopCat.{0}} (p : X ⟶ Y) (g : Z ⟶ X) {j : Z ⟶ Y}
    (h : g ≫ p = j) (g' : W ⟶ Z) {j' : W ⟶ Y} (h' : g' ≫ j = j') (q : ℕ) :
    directImageRestriction p g h q ≫ directImageRestriction j g' h' q =
      directImageRestriction p (g' ≫ g) (by rw [Category.assoc, h, h']) q := by
  refine NatTrans.ext (funext fun V ↦ ?_)
  change rationalCohomologyMap (preimageRestrict p g h V.unop) q ≫
      rationalCohomologyMap (preimageRestrict j g' h' V.unop) q =
    rationalCohomologyMap (preimageRestrict p (g' ≫ g) _ V.unop) q
  rw [← rationalCohomologyMap_comp]
  rfl

private lemma directImageRestriction_id (p : X ⟶ Y) (q : ℕ) :
    directImageRestriction p (𝟙 X) (Category.id_comp p) q = 𝟙 _ := by
  refine NatTrans.ext (funext fun V ↦ ?_)
  change rationalCohomologyMap (preimageRestrict p (𝟙 X) _ V.unop) q = 𝟙 _
  rw [← rationalCohomologyMap_id]
  rfl

/-- Precomposing with a homeomorphism does not change the presheaf `V ↦ H^q(f⁻¹V; ℚ)`. -/
private noncomputable def directImagePresheafIsoOfIsIso (e : Z ⟶ X) [IsIso e] (f : X ⟶ Y)
    (q : ℕ) : directImagePresheaf f q ≅ directImagePresheaf (e ≫ f) q where
  hom := directImageRestriction f e rfl q
  inv := directImageRestriction (e ≫ f) (inv e) (by simp) q
  hom_inv_id := by
    rw [directImageRestriction_comp]
    convert directImageRestriction_id f q using 2
    simp
  inv_hom_id := by
    rw [directImageRestriction_comp]
    convert directImageRestriction_id (e ≫ f) q using 2
    simp

/-- The pushforward of `V' ↦ H^q(g⁻¹V'; ℚ)` along `f` is `V ↦ H^q((g ≫ f)⁻¹V; ℚ)`. -/
private noncomputable def pushforwardDirectImagePresheafIso (g : Z ⟶ X) (f : X ⟶ Y) (q : ℕ) :
    (TopCat.Presheaf.pushforward (ModuleCat.{0} ℚ) f).obj (directImagePresheaf g q) ≅
      directImagePresheaf (g ≫ f) q :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)

/-- Retracts of direct-image presheaves compose along a composite of maps. -/
private theorem nonempty_retract_comp (f : X ⟶ Y) (g : Z ⟶ X) (q : ℕ)
    (r₁ : Retract (directImagePresheaf (𝟙 Y) q) (directImagePresheaf f q))
    (r₂ : Retract (directImagePresheaf (𝟙 X) q) (directImagePresheaf g q)) :
    Nonempty (Retract (directImagePresheaf (𝟙 Y) q) (directImagePresheaf (g ≫ f) q)) := by
  let r₃ := r₂.map (TopCat.Presheaf.pushforward (ModuleCat.{0} ℚ) f)
  let e₁ := pushforwardDirectImagePresheafIso (𝟙 X) f q
  let e₂ := pushforwardDirectImagePresheafIso g f q
  let r₄ : Retract (directImagePresheaf (𝟙 X ≫ f) q) (directImagePresheaf (g ≫ f) q) :=
    ⟨e₁.inv ≫ r₃.i ≫ e₂.hom, e₂.inv ≫ r₃.r ≫ e₁.hom, by simp [r₃.retract_assoc]⟩
  rw [Category.id_comp] at r₄
  exact ⟨r₁.trans r₄⟩

end TopRetract

section AnalyticIso

variable {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)}

private lemma analyticMap_congr {g g' : X ⟶ Y} (h : g = g') (hg : g ≫ sY = sX)
    (hg' : g' ≫ sY = sX) : analyticMap g hg = analyticMap g' hg' := by
  subst h
  rfl

private lemma analyticMap_id (h : 𝟙 X ≫ sX = sX) :
    analyticMap (𝟙 X) h = 𝟙 (analyticSpace sX) := by
  ext x
  change x.hom ≫ 𝟙 X = x.hom
  exact Category.comp_id _

private lemma isIso_analyticMap (g : X ⟶ Y) [IsIso g] (hg : g ≫ sY = sX) :
    IsIso (analyticMap g hg) :=
  ⟨⟨analyticMap (inv g) (by rw [← hg, IsIso.inv_hom_id_assoc]), by
      rw [analyticMap_comp, analyticMap_congr (IsIso.hom_inv_id g) _ (Category.id_comp _),
        analyticMap_id], by
      rw [analyticMap_comp, analyticMap_congr (IsIso.inv_hom_id g) _ (Category.id_comp _),
        analyticMap_id]⟩⟩

/-- Along an isomorphism of schemes over `ℂ`, `U ↦ H^q(U; ℚ)` is a retract of
`U ↦ H^q(g⁻¹U; ℚ)`. -/
private theorem nonempty_retract_of_isIso (g : X ⟶ Y) [IsIso g] (hg : g ≫ sY = sX) (q : ℕ) :
    Nonempty (Retract (directImagePresheaf (𝟙 (analyticSpace sY)) q)
      (directImagePresheaf (analyticMap g hg) q)) := by
  have := isIso_analyticMap g hg
  have e := directImagePresheafIsoOfIsIso (analyticMap g hg) (𝟙 _) q
  rw [Category.comp_id] at e
  exact ⟨Retract.ofIso e⟩

end AnalyticIso

section Geometry

open Scheme Limits

/-- The hypothesis of the pure-codimension case, for a centre of pure codimension `c ≥ 2`. -/
private abbrev PureCase : Prop :=
  ∀ {V : Scheme.{0}} [IsIntegral V] (s : V ⟶ Spec (.of ℂ)) [IsSeparated s]
    [LocallyOfFiniteType s] [QuasiCompact s] (Z : V.IdealSheafData),
    MMP.Mori.IsSmoothScheme s → MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ s) → ∀ c : ℕ, 2 ≤ c →
    (∀ W : IrreducibleCloseds V,
      Maximal (fun W' : IrreducibleCloseds V ↦ (W' : Set V) ⊆ Z.support) W → codimension W = c) →
    ∀ q : ℕ, Nonempty (Retract (directImagePresheaf (𝟙 (analyticSpace s)) q)
      (directImagePresheaf (analyticMap (sY := s) (blowUpToBase Z) rfl) q))

/-- An irreducible smooth centre: codimension `≥ 2` is the pure case, codimension one is an
effective Cartier divisor, whose blowup is an isomorphism. -/
private theorem nonempty_retract_of_isIrreducible (hpure : PureCase) {V : Scheme.{0}}
    [IsIntegral V] (s : V ⟶ Spec (.of ℂ)) [IsSeparated s] [LocallyOfFiniteType s]
    [QuasiCompact s] (C : V.IdealSheafData) (hC0 : C ≠ ⊥) (hs : MMP.Mori.IsSmoothScheme s)
    (hC : MMP.Mori.IsSmoothScheme (C.subschemeι ≫ s))
    (hirr : IsIrreducible (C.support : Set V)) (q : ℕ) :
    Nonempty (Retract (directImagePresheaf (𝟙 (analyticSpace s)) q)
      (directImagePresheaf (analyticMap (sY := s) (blowUpToBase C) rfl) q)) := by
  let S : IrreducibleCloseds V := ⟨C.support, hirr, C.support.isClosed⟩
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace s
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian s
  have hfin : codimension S ≠ ⊤ := by
    intro htop
    have h2 : ((codimension S : ℕ∞) : WithBot ℕ∞) ≤ topologicalKrullDim V :=
      Order.coheight_le_krullDim S
    rw [htop] at h2
    exact topologicalKrullDim_ne_top_of_locallyOfFiniteType ℂ s (eq_top_iff.mpr h2)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
  match n, hn with
  | 0, hn =>
    exfalso
    have hmax : IsMax S := Order.coheight_eq_zero.mp (by rw [← codimension_eq_coheight, ← hn]; rfl)
    let T : IrreducibleCloseds V := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ V, isClosed_univ⟩
    have hTS : T ≤ S := hmax (show S ≤ T from fun _ _ ↦ Set.mem_univ _)
    have hsupp : C.support = ⊤ := by
      ext x
      exact ⟨fun _ ↦ trivial, fun _ ↦ hTS (Set.mem_univ x)⟩
    exact hC0 (IdealSheafData.support_eq_top_iff.mp hsupp)
  | 1, hn =>
    have : Smooth s := MMP.Threefold.Resolution.smooth_of_isSmoothScheme hs
    have : IsIntegral C.subscheme :=
      MMP.Resolution.isIntegral_subscheme_of_isIrreducible s C hC hirr
    have hcodim : codimension (IrreducibleCloseds.closureSingleton
        (C.subschemeι (_root_.genericPoint C.subscheme))) = 1 := by
      have : IrreducibleCloseds.closureSingleton
          (C.subschemeι (_root_.genericPoint C.subscheme)) = S :=
        IrreducibleCloseds.ext (MMP.Resolution.closure_subschemeι_genericPoint C)
      rw [this, ← hn]
      rfl
    have hcart := isEffectiveCartierDivisor_of_codimension_one_of_uniqueFactorizationMonoid C hcodim
      fun x _ ↦
        have := isRegularLocalRing_stalk_of_smooth_over_field s x
        IsRegularLocalRing.uniqueFactorizationMonoid _
    have := Stacks.Blowup.isIso_blowUpToBase_of_isEffectiveCartierDivisor C hcart
    exact nonempty_retract_of_isIso _ _ q
  | n + 2, hn =>
    refine hpure s C hs hC (n + 2) (by omega) (fun W hW ↦ ?_) q
    have hWS : W ≤ S := hW.1
    have hSW : S ≤ W := hW.2 (show (S : Set V) ⊆ C.support from subset_rfl) hWS
    rw [le_antisymm hWS hSW, ← hn]

/-- Pulling a centre back along a blowup whose centre is disjoint from it changes nothing: the
projection from the fibre product to the centre is an isomorphism. -/
private theorem isIso_pullback_snd_blowUpToBase {V : Scheme.{0}} (I J : V.IdealSheafData)
    (h : Disjoint (I.support : Set V) (J.support : Set V)) :
    IsIso (pullback.snd (blowUpToBase I) J.subschemeι) := by
  let O : V.Opens := ⟨(I.support : Set V)ᶜ, I.support.isClosed.isOpen_compl⟩
  have : IsIso (blowUpToBase I ∣_ O) := isIso_blowUp_restrict_compl_support I
  have hr : Set.range J.subschemeι ⊆ Set.range O.ι := by
    rw [J.range_subschemeι, Scheme.Opens.range_ι]
    exact h.subset_compl_left
  let j := IsOpenImmersion.lift O.ι J.subschemeι hr
  have hj : j ≫ O.ι = J.subschemeι := IsOpenImmersion.lift_fac _ _ _
  have hP : IsPullback (pullback.fst (blowUpToBase I ∣_ O) j ≫ (blowUpToBase I ⁻¹ᵁ O).ι)
      (pullback.snd (blowUpToBase I ∣_ O) j) (blowUpToBase I) J.subschemeι := by
    rw [← hj]
    exact (IsPullback.of_hasPullback _ _).paste_horiz (isPullback_morphismRestrict _ O).flip
  rw [← hP.isoPullback_inv_snd]
  infer_instance

/-- A smooth irreducible centre disjoint from the centre of a blowup pulls back to a smooth
irreducible centre. -/
private theorem isSmoothScheme_and_isIrreducible_comap_blowUpToBase {V : Scheme.{0}}
    (s : V ⟶ Spec (.of ℂ)) (I J : V.IdealSheafData) (h : Disjoint (I.support : Set V) (J.support : Set V))
    (hJ : MMP.Mori.IsSmoothScheme (J.subschemeι ≫ s)) (hirr : IsIrreducible (J.support : Set V)) :
    MMP.Mori.IsSmoothScheme ((J.comap (blowUpToBase I)).subschemeι ≫ blowUpToBase I ≫ s) ∧
      IsIrreducible ((J.comap (blowUpToBase I)).support : Set (blowUp I)) := by
  have := isIso_pullback_snd_blowUpToBase I J h
  let e : (J.comap (blowUpToBase I)).subscheme ≅ J.subscheme :=
    J.comapIso (blowUpToBase I) ≪≫ asIso (pullback.snd (blowUpToBase I) J.subschemeι)
  have he : (J.comap (blowUpToBase I)).subschemeι ≫ blowUpToBase I = e.hom ≫ J.subschemeι := by
    simp [e]
  have : Smooth (J.subschemeι ≫ s) := MMP.Threefold.Resolution.smooth_of_isSmoothScheme hJ
  refine ⟨?_, ?_⟩
  · rw [← Category.assoc, he, Category.assoc]
    exact MMP.Resolution.isSmoothScheme_of_smooth _
  · have : IsIntegral J.subscheme :=
      MMP.Resolution.isIntegral_subscheme_of_isIrreducible s J hJ hirr
    rw [← (J.comap (blowUpToBase I)).range_subschemeι]
    have hrange : Set.range (e.inv ≫ (J.comap (blowUpToBase I)).subschemeι) =
        Set.range (J.comap (blowUpToBase I)).subschemeι := by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
        e.inv.surjective.range_eq, Set.image_univ]
    rw [← hrange, ← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ (Scheme.Hom.continuous _).continuousOn

/-- If the blowup of `I * J` is integral, the pullback of `J` to the blowup of `I` is nonzero. -/
private lemma comap_blowUpToBase_ne_bot {V : Scheme.{0}} (I J : V.IdealSheafData)
    [IsIntegral (blowUp (I * J))] : J.comap (blowUpToBase I) ≠ ⊥ := by
  intro h0
  have hem : IsEmpty (blowUp (J.comap (blowUpToBase I))) := by
    rw [h0]
    exact isEmpty_blowUp_bot _
  obtain ⟨x⟩ := (inferInstance : Nonempty (blowUp (I * J)))
  exact hem.false ((blowUpMulIso I J).inv.left x)

/-- Blowing up `I * J` is blowing up `I` and then the pullback of `J`, so the retracts of the two
steps compose to a retract for the blowup of `I * J`. -/
private theorem nonempty_retract_blowUp_mul {V : Scheme.{0}} (s : V ⟶ Spec (.of ℂ))
    (I J : V.IdealSheafData) (q : ℕ)
    (r₁ : Retract (directImagePresheaf (𝟙 (analyticSpace s)) q)
      (directImagePresheaf (analyticMap (sY := s) (blowUpToBase I) rfl) q))
    (r₂ : Retract (directImagePresheaf (𝟙 (analyticSpace (blowUpToBase I ≫ s))) q)
      (directImagePresheaf (analyticMap (sY := blowUpToBase I ≫ s)
        (blowUpToBase (J.comap (blowUpToBase I))) rfl) q)) :
    Nonempty (Retract (directImagePresheaf (𝟙 (analyticSpace s)) q)
      (directImagePresheaf (analyticMap (sY := s) (blowUpToBase (I * J)) rfl) q)) := by
  let e := blowUpMulIso I J
  obtain ⟨r⟩ := nonempty_retract_comp (analyticMap (sY := s) (blowUpToBase I) rfl)
    (analyticMap (sY := blowUpToBase I ≫ s) (blowUpToBase (J.comap (blowUpToBase I))) rfl)
    q r₁ r₂
  have hw : e.hom.left ≫ blowUpToBase (I * J) =
      blowUpToBase (J.comap (blowUpToBase I)) ≫ blowUpToBase I := by
    simpa [e] using Over.w e.hom
  have hφ : e.hom.left ≫ blowUpToBase (I * J) ≫ s =
      blowUpToBase (J.comap (blowUpToBase I)) ≫ blowUpToBase I ≫ s := by
    rw [reassoc_of% hw]
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget V).map e.hom))
  have := isIso_analyticMap e.hom.left hφ
  have hcomp : analyticMap (sY := blowUpToBase I ≫ s)
        (blowUpToBase (J.comap (blowUpToBase I))) rfl ≫
        analyticMap (sY := s) (blowUpToBase I) rfl =
      analyticMap e.hom.left hφ ≫ analyticMap (sY := s) (blowUpToBase (I * J)) rfl := by
    rw [analyticMap_comp, analyticMap_comp]
    exact analyticMap_congr hw.symm _ _
  rw [hcomp] at r
  exact ⟨r.trans (Retract.ofIso (directImagePresheafIsoOfIsIso _ _ q).symm)⟩

/-! ### Open and closed parts of a smooth centre -/

variable {V : Scheme.{0}} {Z : V.IdealSheafData}

/-- The ideal sheaf on `V` of an open part `W` of the closed subscheme `Z = V(Z)`: the kernel of
`W ⟶ Z ⟶ V`. -/
private noncomputable def clopenIdeal (Z : V.IdealSheafData) (W : Z.subscheme.Opens) :
    V.IdealSheafData :=
  (W.ι ≫ Z.subschemeι).ker

private lemma range_ι_comp_subschemeι (W : Z.subscheme.Opens) :
    Set.range (W.ι ≫ Z.subschemeι) = Z.subschemeι '' (W : Set Z.subscheme) := by
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]

private lemma isClosedImmersion_ι_comp_subschemeι {W : Z.subscheme.Opens}
    (hW : IsClosed (W : Set Z.subscheme)) : IsClosedImmersion (W.ι ≫ Z.subschemeι) := by
  refine IsClosedImmersion.of_isPreimmersion _ ?_
  rw [range_ι_comp_subschemeι]
  exact Z.subschemeι.isClosedEmbedding.isClosedMap _ hW

private lemma coe_support_clopenIdeal {W : Z.subscheme.Opens}
    (hW : IsClosed (W : Set Z.subscheme)) :
    ((clopenIdeal Z W).support : Set V) = Z.subschemeι '' (W : Set Z.subscheme) := by
  have := isClosedImmersion_ι_comp_subschemeι hW
  rw [clopenIdeal, Scheme.Hom.support_ker, range_ι_comp_subschemeι]
  exact (Z.subschemeι.isClosedEmbedding.isClosedMap _ hW).closure_eq

private lemma isSmoothScheme_clopenIdeal (s : V ⟶ Spec (.of ℂ)) [Smooth (Z.subschemeι ≫ s)]
    {W : Z.subscheme.Opens} (hW : IsClosed (W : Set Z.subscheme)) :
    MMP.Mori.IsSmoothScheme ((clopenIdeal Z W).subschemeι ≫ s) := by
  have := isClosedImmersion_ι_comp_subschemeι hW
  have h : (W.ι ≫ Z.subschemeι).imageι =
      inv (W.ι ≫ Z.subschemeι).toImage ≫ (W.ι ≫ Z.subschemeι) := by
    rw [IsIso.eq_inv_comp]
    exact (W.ι ≫ Z.subschemeι).toImage_imageι
  change MMP.Mori.IsSmoothScheme ((W.ι ≫ Z.subschemeι).imageι ≫ s)
  rw [h]
  simp only [Category.assoc]
  exact MMP.Resolution.isSmoothScheme_of_smooth _

private lemma radical_clopenIdeal [IsReduced Z.subscheme] {W : Z.subscheme.Opens}
    (hW : IsClosed (W : Set Z.subscheme)) : (clopenIdeal Z W).radical = clopenIdeal Z W := by
  have := isClosedImmersion_ι_comp_subschemeι hW
  ext U : 2
  rw [IdealSheafData.radical_ideal, clopenIdeal, Scheme.Hom.ker_apply]
  refine Ideal.IsRadical.radical fun x ⟨n, hn⟩ ↦ ?_
  rw [RingHom.mem_ker, map_pow] at hn
  rw [RingHom.mem_ker]
  exact IsReduced.eq_zero _ ⟨n, hn⟩

private lemma clopenIdeal_sup_eq_mul [IsReduced Z.subscheme] {W₁ W₂ : Z.subscheme.Opens}
    (h₁ : IsClosed (W₁ : Set Z.subscheme)) (h₂ : IsClosed (W₂ : Set Z.subscheme))
    (hd : Disjoint (W₁ : Set Z.subscheme) (W₂ : Set Z.subscheme)) :
    clopenIdeal Z (W₁ ⊔ W₂) = clopenIdeal Z W₁ * clopenIdeal Z W₂ := by
  have h₁₂ : IsClosed ((W₁ ⊔ W₂ : Z.subscheme.Opens) : Set Z.subscheme) := h₁.union h₂
  have htop : clopenIdeal Z W₁ ⊔ clopenIdeal Z W₂ = ⊤ := by
    rw [← IdealSheafData.support_eq_bot_iff, IdealSheafData.support_sup, ← SetLike.coe_set_eq,
      Closeds.coe_inf, coe_support_clopenIdeal h₁, coe_support_clopenIdeal h₂, Closeds.coe_bot,
      ← Set.image_inter Z.subschemeι.isClosedEmbedding.injective, hd.inter_eq, Set.image_empty]
  have hmul : clopenIdeal Z W₁ * clopenIdeal Z W₂ = clopenIdeal Z W₁ ⊓ clopenIdeal Z W₂ := by
    ext U : 2
    simp only [IdealSheafData.ideal_mul, IdealSheafData.ideal_inf, Pi.mul_apply, Pi.inf_apply]
    apply Ideal.mul_eq_inf_of_coprime
    simpa [IdealSheafData.ideal_sup] using congrArg (fun I : V.IdealSheafData ↦ I.ideal U) htop
  calc clopenIdeal Z (W₁ ⊔ W₂)
      = IdealSheafData.vanishingIdeal (clopenIdeal Z (W₁ ⊔ W₂)).support := by
        rw [IdealSheafData.vanishingIdeal_support, radical_clopenIdeal h₁₂]
    _ = IdealSheafData.vanishingIdeal
          ((clopenIdeal Z W₁).support ⊔ (clopenIdeal Z W₂).support) := by
        congr 1
        apply SetLike.coe_injective
        rw [Closeds.coe_sup, coe_support_clopenIdeal h₁₂, coe_support_clopenIdeal h₁,
          coe_support_clopenIdeal h₂, Opens.coe_sup, Set.image_union]
    _ = clopenIdeal Z W₁ ⊓ clopenIdeal Z W₂ := by
        rw [IdealSheafData.vanishingIdeal_sup, IdealSheafData.vanishingIdeal_support,
          IdealSheafData.vanishingIdeal_support, radical_clopenIdeal h₁, radical_clopenIdeal h₂]
    _ = clopenIdeal Z W₁ * clopenIdeal Z W₂ := hmul.symm

private lemma clopenIdeal_bot : clopenIdeal Z ⊥ = ⊤ := by
  have : IsEmpty (⊥ : Z.subscheme.Opens).toScheme := ⟨fun x ↦ by simpa using x.2⟩
  exact Scheme.ker_eq_top_of_isEmpty _

private lemma clopenIdeal_top : clopenIdeal Z ⊤ = Z := by
  rw [clopenIdeal, ← Scheme.topIso_hom, Scheme.Hom.ker_comp_of_isIso,
    IdealSheafData.ker_subschemeι]

private lemma clopenIdeal_ne_bot [IsReduced V] (hZ0 : Z ≠ ⊥) {W : Z.subscheme.Opens}
    (hW : IsClosed (W : Set Z.subscheme)) : clopenIdeal Z W ≠ ⊥ := by
  have hZtop : (Z.support : Set V) ≠ Set.univ := fun h ↦
    hZ0 (IdealSheafData.support_eq_top_iff.mp
      (SetLike.coe_injective (h.trans Closeds.coe_top.symm)))
  intro h0
  apply hZtop
  have h := coe_support_clopenIdeal hW
  rw [h0, IdealSheafData.support_bot, Closeds.coe_top] at h
  refine Set.eq_univ_of_univ_subset (h ▸ ?_)
  rw [← Z.range_subschemeι]
  exact Set.image_subset_range _ _

/-- A finite union of irreducible components of a smooth centre is open and closed. -/
private lemma isClopen_biUnion_irreducibleComponents (s : V ⟶ Spec (.of ℂ))
    [Smooth (Z.subschemeι ≫ s)] (T : Finset (Set Z.subscheme))
    (hT : ∀ C ∈ T, C ∈ irreducibleComponents Z.subscheme) :
    IsClopen (⋃ C ∈ T, C) :=
  ⟨T.finite_toSet.isClosed_biUnion fun C h ↦ isClosed_of_mem_irreducibleComponents C (hT C h),
    isOpen_biUnion fun C h ↦
      MMP.Flips.ResolutionInputs.isOpen_of_mem_irreducibleComponents_of_smooth
        (Z.subschemeι ≫ s) (hT C h)⟩

/-- Adding an irreducible part `W₂` of a smooth centre, disjoint from `W₁`, preserves the
retraction: blow up `W₁` first, then the pullback of `W₂`. -/
private theorem nonempty_retract_clopenIdeal_sup (hpure : PureCase) [IsIntegral V]
    (s : V ⟶ Spec (.of ℂ)) [IsSeparated s] [LocallyOfFiniteType s] [QuasiCompact s]
    (hZ0 : Z ≠ ⊥) (hs : MMP.Mori.IsSmoothScheme s) [Smooth (Z.subschemeι ≫ s)]
    [IsReduced Z.subscheme] {W₁ W₂ : Z.subscheme.Opens}
    (h₁ : IsClosed (W₁ : Set Z.subscheme)) (h₂ : IsClosed (W₂ : Set Z.subscheme))
    (hd : Disjoint (W₁ : Set Z.subscheme) (W₂ : Set Z.subscheme))
    (hirr : IsIrreducible (W₂ : Set Z.subscheme)) (q : ℕ)
    (r₁ : Retract (directImagePresheaf (𝟙 (analyticSpace s)) q)
      (directImagePresheaf (analyticMap (sY := s) (blowUpToBase (clopenIdeal Z W₁)) rfl) q)) :
    Nonempty (Retract (directImagePresheaf (𝟙 (analyticSpace s)) q)
      (directImagePresheaf
        (analyticMap (sY := s) (blowUpToBase (clopenIdeal Z (W₁ ⊔ W₂))) rfl) q)) := by
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian s
  rw [clopenIdeal_sup_eq_mul h₁ h₂ hd]
  have : IsIntegral (blowUp (clopenIdeal Z W₁ * clopenIdeal Z W₂)) := isIntegral_blowUp _ (by
    rw [← clopenIdeal_sup_eq_mul h₁ h₂ hd]
    exact clopenIdeal_ne_bot hZ0 (h₁.union h₂))
  set I := clopenIdeal Z W₁
  set J := clopenIdeal Z W₂
  have hdisj : Disjoint (I.support : Set V) (J.support : Set V) := by
    rw [coe_support_clopenIdeal h₁, coe_support_clopenIdeal h₂,
      Set.disjoint_image_iff Z.subschemeι.isClosedEmbedding.injective]
    exact hd
  have hJirr : IsIrreducible (J.support : Set V) := by
    rw [coe_support_clopenIdeal h₂]
    exact hirr.image _ (Scheme.Hom.continuous _).continuousOn
  have : IsIntegral (blowUp I) := isIntegral_blowUp I (clopenIdeal_ne_bot hZ0 h₁)
  have : IsProper (blowUpToBase I) := TwoStepTower.isProper_blowUpToBase
    (TwoStepTower.isFiniteType_of_isLocallyNoetherian I)
  have hs' : MMP.Mori.IsSmoothScheme (blowUpToBase I ≫ s) := by
    have := (MMP.Resolution.Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup s I
      ⟨hs, isSmoothScheme_clopenIdeal s h₁⟩).1
    exact MMP.Resolution.isSmoothScheme_of_smooth _
  obtain ⟨hC'sm, hC'irr⟩ := isSmoothScheme_and_isIrreducible_comap_blowUpToBase s I J hdisj
    (isSmoothScheme_clopenIdeal s h₂) hJirr
  obtain ⟨r₂⟩ := nonempty_retract_of_isIrreducible hpure (blowUpToBase I ≫ s)
    (J.comap (blowUpToBase I)) (comap_blowUpToBase_ne_bot I J) hs' hC'sm hC'irr q
  exact nonempty_retract_blowUp_mul s I J q r₁ r₂

/-- A union `W` of finitely many irreducible components of a smooth centre has the retraction
for the blowup of `clopenIdeal Z W`, by induction on the components. -/
private theorem nonempty_retract_clopenIdeal_biUnion (hpure : PureCase) [IsIntegral V]
    (s : V ⟶ Spec (.of ℂ)) [IsSeparated s] [LocallyOfFiniteType s] [QuasiCompact s]
    (hZ0 : Z ≠ ⊥) (hs : MMP.Mori.IsSmoothScheme s) [Smooth (Z.subschemeι ≫ s)]
    [IsReduced Z.subscheme] (q : ℕ) (T : Finset (Set Z.subscheme)) :
    (∀ C ∈ T, C ∈ irreducibleComponents Z.subscheme) →
      ∀ W : Z.subscheme.Opens, (W : Set Z.subscheme) = ⋃ C ∈ T, C →
      Nonempty (Retract (directImagePresheaf (𝟙 (analyticSpace s)) q)
        (directImagePresheaf (analyticMap (sY := s) (blowUpToBase (clopenIdeal Z W)) rfl) q)) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro _ W hW
    have hW0 : W = ⊥ := by
      apply SetLike.coe_injective
      rw [hW, Opens.coe_bot]
      simp
    rw [hW0, clopenIdeal_bot]
    have := Stacks.Blowup.isIso_blowUpToBase_of_isEffectiveCartierDivisor _
      (Stacks.Divisors.isEffectiveCartierDivisor_top (X := V))
    exact nonempty_retract_of_isIso _ _ q
  | insert C T hCT ih =>
    intro hT W hW
    have hC : C ∈ irreducibleComponents Z.subscheme := hT C (Finset.mem_insert_self C T)
    have hT' : ∀ C' ∈ T, C' ∈ irreducibleComponents Z.subscheme :=
      fun C' h ↦ hT C' (Finset.mem_insert_of_mem h)
    have hcl := isClopen_biUnion_irreducibleComponents s T hT'
    let W₁ : Z.subscheme.Opens := ⟨⋃ C' ∈ T, C', hcl.isOpen⟩
    let W₂ : Z.subscheme.Opens := ⟨C,
      MMP.Flips.ResolutionInputs.isOpen_of_mem_irreducibleComponents_of_smooth
        (Z.subschemeι ≫ s) hC⟩
    have hd : Disjoint (W₁ : Set Z.subscheme) (W₂ : Set Z.subscheme) := by
      change Disjoint (⋃ C' ∈ T, C') C
      simp only [Set.disjoint_iUnion_left]
      intro C' hC'
      exact MMP.Flips.ResolutionInputs.disjoint_of_mem_irreducibleComponents_of_smooth
        (Z.subschemeι ≫ s) (hT' C' hC') hC (fun h ↦ hCT (h ▸ hC'))
    have hWeq : W = W₁ ⊔ W₂ := by
      apply SetLike.coe_injective
      rw [hW, Opens.coe_sup, Finset.set_biUnion_insert, Set.union_comm]
      rfl
    obtain ⟨r₁⟩ := ih hT' W₁ rfl
    rw [hWeq]
    exact nonempty_retract_clopenIdeal_sup hpure s hZ0 hs hcl.isClosed
      (isClosed_of_mem_irreducibleComponents C hC) hd hC.1 q r₁

end Geometry

open Scheme Limits in
/-- **The blowup retraction, general smooth centre.** Granting the case of a smooth centre of pure
codimension `c ≥ 2`: for the blowup `b : Bl_Z V ⟶ V` of a smooth complex variety along a nonzero
ideal with smooth centre, `U ↦ H^q(U; ℚ)` is a retract of `U ↦ H^q(b⁻¹U; ℚ)`, naturally in the
analytic open `U`. -/
public theorem nonempty_retract_directImagePresheaf_blowUp_of_pure
    (hpure : ∀ {V : Scheme.{0}} [IsIntegral V] (s : V ⟶ Spec (.of ℂ)) [IsSeparated s]
      [LocallyOfFiniteType s] [QuasiCompact s] (Z : V.IdealSheafData),
      MMP.Mori.IsSmoothScheme s → MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ s) → ∀ c : ℕ, 2 ≤ c →
      (∀ W : IrreducibleCloseds V,
        Maximal (fun W' : IrreducibleCloseds V ↦ (W' : Set V) ⊆ Z.support) W → codimension W = c) →
      ∀ q : ℕ, Nonempty (Retract (directImagePresheaf (𝟙 (analyticSpace s)) q)
        (directImagePresheaf (analyticMap (sY := s) (blowUpToBase Z) rfl) q)))
    {V : Scheme.{0}} [IsIntegral V] (s : V ⟶ Spec (.of ℂ)) [IsSeparated s]
    [LocallyOfFiniteType s] [QuasiCompact s] (Z : V.IdealSheafData) (hZ0 : Z ≠ ⊥)
    (hs : MMP.Mori.IsSmoothScheme s) (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ s)) (q : ℕ) :
    Nonempty (Retract (directImagePresheaf (𝟙 (analyticSpace s)) q)
      (directImagePresheaf (analyticMap (sY := s) (blowUpToBase Z) rfl) q)) := by
  have : Smooth (Z.subschemeι ≫ s) := MMP.Threefold.Resolution.smooth_of_isSmoothScheme hZ
  have : IsReduced Z.subscheme :=
    isReduced_of_isRegular (isRegular_of_smooth_over_field (Z.subschemeι ≫ s))
  have : IsLocallyNoetherian Z.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (Z.subschemeι ≫ s)
  have : CompactSpace Z.subscheme := QuasiCompact.compactSpace_of_compactSpace (Z.subschemeι ≫ s)
  have : IsNoetherian Z.subscheme := {}
  have hfin : (irreducibleComponents Z.subscheme).Finite :=
    NoetherianSpace.finite_irreducibleComponents
  obtain ⟨r⟩ := nonempty_retract_clopenIdeal_biUnion hpure s hZ0 hs q hfin.toFinset
    (fun C hC ↦ hfin.mem_toFinset.mp hC) ⊤ (by
      rw [Opens.coe_top]
      exact (Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion₂.mpr ⟨irreducibleComponent x,
        hfin.mem_toFinset.mpr (irreducibleComponent_mem_irreducibleComponents x),
        mem_irreducibleComponent⟩).symm)
  rw [clopenIdeal_top] at r
  exact ⟨r⟩

/-- **The blowup retraction.** For the blowup `b : Bl_Z V ⟶ V` of a smooth complex variety along a
nonzero ideal with smooth centre, `U ↦ H^q(U; ℚ)` is a retract of `U ↦ H^q(b⁻¹U; ℚ)`, naturally in
the analytic open `U`. -/
public theorem nonempty_retract_directImagePresheaf_blowUp {V : Scheme.{0}} [IsIntegral V]
    (s : V ⟶ Spec (.of ℂ)) [IsSeparated s] [LocallyOfFiniteType s] [QuasiCompact s]
    (Z : V.IdealSheafData) (hZ0 : Z ≠ ⊥) (hs : MMP.Mori.IsSmoothScheme s)
    (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ s)) (q : ℕ) :
    Nonempty (Retract (directImagePresheaf (𝟙 (analyticSpace s)) q)
      (directImagePresheaf (analyticMap (sY := s) (blowUpToBase Z) rfl) q)) :=
  nonempty_retract_directImagePresheaf_blowUp_of_pure
    nonempty_retract_directImagePresheaf_blowUp_of_codimension s Z hZ0 hs hZ q

end MMP.Fourfold
