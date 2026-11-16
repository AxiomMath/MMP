module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Resolution.Principalization
public import MMP.AlgebraicGeometry.Resolution.Principalization.CanonicalFunctor
public import MMP.AlgebraicGeometry.Resolution.OrderReduction.MonomialPart
public import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.ConstructionFunctorial
public import MMP.AlgebraicGeometry.Resolution.BlowupSequence.FlatBaseChange
public import MMP.AlgebraicGeometry.Resolution.BlowupSequence.EntryIndex
public import MMP.AlgebraicGeometry.Resolution.MaximalContact.DerivativeIdealTransform

/-!
# Embedded resolution commutes with change of fields

Let `X ⊆ A` be an admissible embedding over a field `K` of characteristic `0` and `σ : K ↪ L` a
field extension such that `X_{L,σ} = X ×_{Spec K} Spec L` is again a disjoint union of varieties.
Then the base-changed embedding `X_{L,σ} ⊆ A_{L,σ}` is admissible, and the embedded resolution of
`X_{L,σ}` in `A_{L,σ}` is the field change of the embedded resolution of `X` in `A`, i.e. its
pull-back along the projection `p_σ : X_{L,σ} → X` (Kollár, *Lectures on resolution of
singularities*, p. 146).

## Main results

* `MMP.Resolution.isAdmissibleEmbedding_fieldChange_and_embeddedResolution_eq`: the base change
  `X_{L,σ} ⟶ A_{L,σ}` is an admissible embedding and `𝓑𝓡_{A_{L,σ}}(X_{L,σ}) = p_σ^* 𝓑𝓡_A(X)`.

## Implementation notes

`X_{L,σ}` and `A_{L,σ}` are the fibre products `Limits.pullback (i ≫ s_A) (Spec.map σ)` and
`Limits.pullback s_A (Spec.map σ)`, over `L` by the second projections; the embedding
`X_{L,σ} → A_{L,σ}` is `Limits.pullback.map` of `i` over the identities. The field change of a
blow-up sequence is its pull-back `MMP.Resolution.ClosedBlowupSequence.pullback` along `p_σ`.

The projections `p_X`, `p_A` are flat and surjective, being base changes of `Spec L → Spec K`.
`A_{L,σ}` is smooth and affine over `L`; local dimensions are preserved by the base change, so
`A_{L,σ}` is equidimensional, and codimension `≥ 2` is carried over by going-down along the flat
`p_A`, the local rings of `A_{L,σ}` being regular, hence domains. So `X_{L,σ} ⊆ A_{L,σ}` is
admissible, and its triple is the field change of `(A, I_X, ∅)`. By Kollár 3.72(4),
`𝓑𝓟^can` commutes with the field change; the sequence induced on `X_{L,σ}` agrees with `p_X^*` of
the one induced on `X` up to empty blow-ups
(`MMP.Resolution.Kollar.reduction_embeddedResolutionSequence_pullback_of_flat_of_comm`), and
deleting empty blow-ups commutes with pull-back along the flat surjective `p_X`. The auxiliary
lemmas live in the namespace `Proof_lem_kr3f_embedded_resolution_field_change`.

## References

* [J. Kollár, *Lectures on resolution of singularities*, 3.34.2, 3.72, p. 146]
-/

@[expose] public section

namespace Proof_lem_kr3f_embedded_resolution_field_change

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MMP.Resolution
open MMP.Resolution.ClosedBlowupSequence

universe u

attribute [local instance 2000] AlgebraicGeometry.IsNoetherian.toIsLocallyNoetherian

/-- Deleting empty blow-ups commutes with pull-back along a flat surjective morphism. -/
private theorem reduction_pullback_eq_pullback_reduction {X Y : Scheme.{u}}
    (S : ClosedBlowupSequence X) (f : Y ⟶ X) [Flat f] [Surjective f] :
    (S.pullback f).reduction = S.reduction.pullback f := by
  rw [← reduction_pullback_reduction,
    reduction_eq_self (hasNoEmptyBlowups_pullback _ (hasNoEmptyBlowups_reduction S) f)]

/-- `𝓑𝓟^can` evaluated at equal triples. -/
private theorem canonicalPrincipalization_heq {t₁ t₂ : FieldBlowupTriple.{u}} (e : t₁ = t₂)
    (h₁ : t₁ ∈ sncTriples) (h₂ : t₂ ∈ sncTriples) :
    canonicalPrincipalization t₁ h₁ ≍ canonicalPrincipalization t₂ h₂ := by
  subst e
  rfl

/-! ### `Spec L → Spec K` -/

/-- `Spec L → Spec K` is flat. -/
private theorem flat_spec_map {K L : Type u} [Field K] [Field L] (σ : K →+* L) :
    Flat (Spec.map (CommRingCat.ofHom σ)) := by
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  let : Algebra K L := σ.toAlgebra
  exact (inferInstance : Module.Flat K L)

/-- `Spec L → Spec K` is surjective. -/
private theorem surjective_spec_map {K L : Type u} [Field K] [Field L] (σ : K →+* L) :
    Surjective (Spec.map (CommRingCat.ofHom σ)) := by
  constructor
  intro x
  obtain ⟨y⟩ : Nonempty (Spec (.of L)) := inferInstance
  haveI : Subsingleton (Spec (.of K)) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  exact ⟨y, Subsingleton.elim _ _⟩

/-! ### Dimension -/

/-- The dimension of an irreducible component of a scheme locally of finite type over a field is
the local dimension at its generic point. -/
private theorem topologicalKrullDim_eq_topologicalKrullDimAt_genericPoint {k : Type u} [Field k]
    {Y : Scheme.{u}} (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s] {Z : Set Y}
    (hZ : Z ∈ irreducibleComponents Y) :
    topologicalKrullDim Z = topologicalKrullDimAt Y hZ.1.genericPoint := by
  have hη := hZ.1.isGenericPoint_genericPoint_closure
  rw [(isClosed_of_mem_irreducibleComponents Z hZ).closure_eq] at hη
  have hηZ : hZ.1.genericPoint ∈ Z := hη.mem
  rw [topologicalKrullDimAt_eq_iSup_irreducibleComponents k Y s]
  refine le_antisymm
    (le_iSup₂ (f := fun Z' (_ : Z' ∈ {Z' | Z' ∈ irreducibleComponents Y ∧
      hZ.1.genericPoint ∈ Z'}) => topologicalKrullDim Z') Z ⟨hZ, hηZ⟩) (iSup₂_le fun Z' hZ' => ?_)
  have hle : Z ⊆ Z' := by
    rw [← (show closure {hZ.1.genericPoint} = Z from hη)]
    exact (isClosed_of_mem_irreducibleComponents Z' hZ'.1).closure_subset_iff.2
      (Set.singleton_subset_iff.2 hZ'.2)
  rw [(hZ.2 hZ'.1.1 hle).antisymm hle]

/-- In an equidimensional scheme locally of finite type over a field, the local dimension at
every point is the dimension of every irreducible component. -/
private theorem topologicalKrullDimAt_eq_of_mem_irreducibleComponents {k : Type u} [Field k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (hX : TopologicalSpace.Equidimensional X) (x : X) {C : Set X}
    (hC : C ∈ irreducibleComponents X) : topologicalKrullDimAt X x = topologicalKrullDim C := by
  rw [topologicalKrullDimAt_eq_iSup_irreducibleComponents k X s x]
  refine le_antisymm (iSup₂_le fun D hD => (hX D hD.1 C hC).le) ?_
  exact (hX _ (irreducibleComponent_mem_irreducibleComponents x) C hC).symm.le.trans
    (le_iSup₂ (f := fun D (_ : D ∈ {D | D ∈ irreducibleComponents X ∧ x ∈ D}) =>
      topologicalKrullDim D) _ ⟨irreducibleComponent_mem_irreducibleComponents x,
        mem_irreducibleComponent⟩)

/-- A smooth morphism is smooth of some relative dimension near every point of the source. -/
private theorem exists_smoothOfRelativeDimension_nbhd {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f]
    (x : X) : ∃ V : X.Opens, x ∈ V ∧ ∃ n : ℕ, SmoothOfRelativeDimension n (V.ι ≫ f) := by
  obtain ⟨U, hU, V, hV, hx, e, hf⟩ := Smooth.exists_isStandardSmooth f x
  obtain ⟨n, hn⟩ : ∃ n, (f.appLE U V e).hom.IsStandardSmoothOfRelativeDimension n := by
    letI := (f.appLE U V e).hom.toAlgebra
    obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := hf.toAlgebra.out
    exact ⟨P.dimension, P.isStandardSmoothOfRelativeDimension rfl⟩
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  have : (RingHom.toMorphismProperty
      (RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n))).RespectsIso :=
    RingHom.toMorphismProperty_respectsIso_iff.mp
      (HasRingHomProperty.isLocal_ringHomProperty (@SmoothOfRelativeDimension n)).respectsIso
  have h : SmoothOfRelativeDimension n (f.resLE U V e) := by
    rw [HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension n)]
    exact (MorphismProperty.arrow_mk_iso_iff (RingHom.toMorphismProperty
      (RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n)))
      (arrowResLEAppIso f U V e)).mpr
      (RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ hn)
  refine ⟨V, hx, n, ?_⟩
  rw [← Scheme.Hom.resLE_comp_ι f e]
  exact inferInstanceAs (SmoothOfRelativeDimension (n + 0) _)

/-- A scheme smooth of relative dimension `N` over a field has local dimension `N` everywhere. -/
private theorem topologicalKrullDimAt_eq_of_smoothOfRelativeDimension {k : Type u} [Field k]
    {T : Scheme.{u}} (s : T ⟶ Spec (.of k)) (N : ℕ) [SmoothOfRelativeDimension N s] (t : T) :
    topologicalKrullDimAt T t = N := by
  have : Subsingleton (Spec (.of k)) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  have hpre : s.base ⁻¹' {s.base t} = (Set.univ : Set T) := by
    ext y
    simp [Subsingleton.elim (s.base y) (s.base t)]
  let e : s.fiber (s.base t) ≃ₜ T :=
    (s.fiberHomeo _).trans ((Homeomorph.setCongr hpre).trans (Homeomorph.Set.univ T))
  have he : e (s.asFiber t) = t := s.fiberι_asFiber t
  rw [← he, e.isOpenEmbedding.topologicalKrullDimAt_eq]
  exact fiberDimensionAt_eq_of_smoothOfRelativeDimension s N t

/-- Along a base change `q : Y → X` of `Spec L → Spec k`, `X` smooth over `k`, local dimensions
are preserved: `dim_y Y = dim_{q y} X`. -/
private theorem topologicalKrullDimAt_eq_of_isPullback {k L : Type u} [Field k] [Field L]
    (σ : k →+* L) {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [Smooth sX] (q : Y ⟶ X)
    (sY : Y ⟶ Spec (.of L)) (sq : IsPullback q sY sX (Spec.map (CommRingCat.ofHom σ))) (y : Y) :
    topologicalKrullDimAt Y y = topologicalKrullDimAt X (q y) := by
  obtain ⟨V, hxV, d, hd⟩ := exists_smoothOfRelativeDimension_nbhd sX (q y)
  have sqV : IsPullback (q ∣_ V) ((q ⁻¹ᵁ V).ι ≫ sY) (V.ι ≫ sX)
      (Spec.map (CommRingCat.ofHom σ)) := (isPullback_morphismRestrict q V).paste_vert sq
  have hdL : SmoothOfRelativeDimension d ((q ⁻¹ᵁ V).ι ≫ sY) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange d).of_isPullback sqV hd
  obtain ⟨zY, hzY⟩ : y ∈ Set.range (q ⁻¹ᵁ V).ι := by rwa [Scheme.Opens.range_ι]
  obtain ⟨zX, hzX⟩ : q y ∈ Set.range V.ι := by rwa [Scheme.Opens.range_ι]
  rw [← hzX, ← hzY, (q ⁻¹ᵁ V).ι.isOpenEmbedding.topologicalKrullDimAt_eq zY,
    V.ι.isOpenEmbedding.topologicalKrullDimAt_eq zX,
    topologicalKrullDimAt_eq_of_smoothOfRelativeDimension ((q ⁻¹ᵁ V).ι ≫ sY) d zY,
    topologicalKrullDimAt_eq_of_smoothOfRelativeDimension (V.ι ≫ sX) d zX]

/-- A base change along `Spec L → Spec k` of an equidimensional scheme smooth over `k` is
equidimensional. -/
private theorem equidimensional_of_isPullback {k L : Type u} [Field k] [Field L]
    (σ : k →+* L) {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [Smooth sX] (q : Y ⟶ X)
    (sY : Y ⟶ Spec (.of L)) (sq : IsPullback q sY sX (Spec.map (CommRingCat.ofHom σ)))
    (hX : TopologicalSpace.Equidimensional X) : TopologicalSpace.Equidimensional Y := by
  haveI : LocallyOfFiniteType sY :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) sq inferInstance
  have key : ∀ Z ∈ irreducibleComponents Y, ∀ C ∈ irreducibleComponents X,
      topologicalKrullDim Z = topologicalKrullDim C := fun Z hZ C hC => by
    rw [topologicalKrullDim_eq_topologicalKrullDimAt_genericPoint sY hZ,
      topologicalKrullDimAt_eq_of_isPullback σ sX q sY sq,
      topologicalKrullDimAt_eq_of_mem_irreducibleComponents sX hX _ hC]
  intro Z hZ W hW
  have hC := irreducibleComponent_mem_irreducibleComponents (q hZ.1.genericPoint)
  rw [key Z hZ _ hC, key W hW _ hC]

/-! ### Codimension under flat base change -/

/-- If the local ring at `a` is a domain, every generalization of `a` lies on every irreducible
component through `a`. -/
private theorem mem_of_specializes_of_isDomain {Y : Scheme.{u}} {a : Y}
    [IsDomain (Y.presheaf.stalk a)] {T : Set Y} (hT : T ∈ irreducibleComponents Y) (ha : a ∈ T)
    {y : Y} (hy : y ⤳ a) : y ∈ T := by
  have hξ : closure {hT.1.genericPoint} = T :=
    hT.1.closure_genericPoint (isClosed_of_mem_irreducibleComponents T hT)
  have hξa : hT.1.genericPoint ⤳ a := specializes_iff_mem_closure.mpr (by rwa [hξ])
  obtain ⟨p, hp⟩ : hT.1.genericPoint ∈ Set.range (Y.fromSpecStalk a) := by
    rwa [Scheme.range_fromSpecStalk]
  obtain ⟨q, hq⟩ : y ∈ Set.range (Y.fromSpecStalk a) := by
    rwa [Scheme.range_fromSpecStalk]
  haveI : IrreducibleSpace (Spec (Y.presheaf.stalk a)) :=
    inferInstanceAs (IrreducibleSpace (PrimeSpectrum (Y.presheaf.stalk a)))
  have hg : ∀ z, genericPoint (Spec (Y.presheaf.stalk a)) ⤳ z := fun z =>
    (genericPoint_spec _).specializes (Set.mem_univ z)
  have h1 := (hg p).map (Y.fromSpecStalk a).continuous
  have h2 := (hg q).map (Y.fromSpecStalk a).continuous
  rw [hp] at h1
  rw [hq] at h2
  have hsub : T ⊆ closure {Y.fromSpecStalk a (genericPoint (Spec (Y.presheaf.stalk a)))} :=
    hξ ▸ h1.closure_subset
  exact hT.2 isIrreducible_singleton.closure hsub (specializes_iff_mem_closure.mp h2)

/-- A flat morphism maps the generic point of an irreducible component of the source to the
generic point of an irreducible component of the target. -/
private theorem closure_apply_genericPoint_mem_irreducibleComponents {X X' : Scheme.{u}}
    (f : X' ⟶ X) [Flat f] {W : Set X'} (hW : W ∈ irreducibleComponents X') :
    closure {f hW.1.genericPoint} ∈ irreducibleComponents X := by
  have hw := hW.1.closure_genericPoint (isClosed_of_mem_irreducibleComponents W hW)
  obtain ⟨W0, hW0, hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _
    (isIrreducible_singleton (x := f hW.1.genericPoint)).closure
  have h0 := hW0.1.closure_genericPoint (isClosed_of_mem_irreducibleComponents W0 hW0)
  obtain ⟨w', hw'w, hfw'⟩ := Flat.generalizingMap f
    (specializes_iff_mem_closure.mpr (h0 ▸ hsub (subset_closure rfl)))
  have h2 : closure {w'} ⊆ W := hW.2 isIrreducible_singleton.closure (hw ▸ hw'w.closure_subset)
  have hww' : hW.1.genericPoint ⤳ w' :=
    specializes_iff_mem_closure.mpr (by rw [hw]; exact h2 (subset_closure rfl))
  rw [← (hw'w.antisymm hww').eq, hfw', h0]
  exact hW0

/-- **Codimension `≥ 2` under flat base change.** Let `i' ≫ p_A = f ≫ i` with `i` a closed
immersion, `f`, `p_A` flat and the local rings of `A'` domains. If every irreducible component of
`X` has codimension `≥ 2` in the components of `A` containing it, the same holds for `X' ⊆ A'`. -/
private theorem codim_of_flat {X A X' A' : Scheme.{u}} (i : X ⟶ A) [IsClosedImmersion i]
    (pA : A' ⟶ A) [Flat pA] (f : X' ⟶ X) [Flat f] (i' : X' ⟶ A')
    (hsq : i' ≫ pA = f ≫ i) (hdom : ∀ a : A', IsDomain (A'.presheaf.stalk a))
    (hcod : ∀ W ∈ irreducibleComponents X, ∀ T ∈ irreducibleComponents A, i.base '' W ⊆ T →
      ∃ Y₁ Y₂ : IrreducibleCloseds A,
        i.base '' W ⊂ (Y₁ : Set A) ∧ (Y₁ : Set A) ⊂ Y₂ ∧ (Y₂ : Set A) ⊆ T) :
    ∀ W ∈ irreducibleComponents X', ∀ T ∈ irreducibleComponents A', i'.base '' W ⊆ T →
      ∃ Y₁ Y₂ : IrreducibleCloseds A',
        i'.base '' W ⊂ (Y₁ : Set A') ∧ (Y₁ : Set A') ⊂ Y₂ ∧ (Y₂ : Set A') ⊆ T := by
  intro W hW T hT hWT
  have hw : closure {hW.1.genericPoint} = W :=
    hW.1.closure_genericPoint (isClosed_of_mem_irreducibleComponents W hW)
  set w := hW.1.genericPoint
  have hfw := closure_apply_genericPoint_mem_irreducibleComponents f hW
  obtain ⟨T0, hT0, hsub0⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (i.base '' closure {f w}) (hfw.1.image _ i.base.hom.continuous.continuousOn)
  obtain ⟨Y1, Y2, h1, h2, h3⟩ := hcod _ hfw T0 hT0 hsub0
  have hy1 : closure {Y1.isIrreducible'.genericPoint} = (Y1 : Set A) :=
    Y1.isIrreducible'.closure_genericPoint Y1.isClosed'
  have hy2 : closure {Y2.isIrreducible'.genericPoint} = (Y2 : Set A) :=
    Y2.isIrreducible'.closure_genericPoint Y2.isClosed'
  set y1 := Y1.isIrreducible'.genericPoint
  set y2 := Y2.isIrreducible'.genericPoint
  have haW0 : i (f w) ∈ i.base '' closure {f w} := ⟨_, subset_closure rfl, rfl⟩
  have hW0cl : IsClosed (i.base '' closure {f w}) :=
    i.isClosedEmbedding.isClosedMap _ isClosed_closure
  have hy1a : y1 ⤳ i (f w) := specializes_iff_mem_closure.mpr (hy1 ▸ h1.subset haW0)
  have hy2y1 : y2 ⤳ y1 := by
    refine specializes_iff_mem_closure.mpr (hy2 ▸ h2.subset ?_)
    rw [← hy1]
    exact subset_closure rfl
  have haL : pA (i' w) = i (f w) := by
    rw [← Scheme.Hom.comp_apply, hsq, Scheme.Hom.comp_apply]
  obtain ⟨y1', hy1'aL, hy1'e⟩ := Flat.generalizingMap pA (show y1 ⤳ pA (i' w) from haL ▸ hy1a)
  obtain ⟨y2', hy2'y1', hy2'e⟩ := Flat.generalizingMap pA (show y2 ⤳ pA y1' from hy1'e ▸ hy2y1)
  have hWsub : i'.base '' W ⊆ closure {i' w} := by
    rw [← hw]
    refine (image_closure_subset_closure_image i'.continuous).trans ?_
    rw [Set.image_singleton]
  refine ⟨⟨closure {y1'}, isIrreducible_singleton.closure, isClosed_closure⟩,
    ⟨closure {y2'}, isIrreducible_singleton.closure, isClosed_closure⟩, ?_, ?_, ?_⟩
  · refine HasSubset.Subset.ssubset_of_not_subset (hWsub.trans hy1'aL.closure_subset)
      fun hc => h1.not_subset ?_
    have hm : y1' ∈ closure {i' w} := hWsub (hc (subset_closure rfl))
    have : i (f w) ⤳ y1 := by
      rw [← haL, ← hy1'e]
      exact (specializes_iff_mem_closure.mpr hm).map pA.continuous
    rw [← hy1]
    exact hW0cl.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr
      (hW0cl.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr haW0)
        (specializes_iff_mem_closure.mp this)))
  · refine HasSubset.Subset.ssubset_of_not_subset hy2'y1'.closure_subset fun hc => h2.not_subset ?_
    have : y1' ⤳ y2' := specializes_iff_mem_closure.mpr (hc (subset_closure rfl))
    have h' : y1 ⤳ y2 := by
      rw [← hy1'e, ← hy2'e]
      exact this.map pA.continuous
    rw [← hy2, ← hy1]
    exact h'.closure_subset
  · have hTc := isClosed_of_mem_irreducibleComponents T hT
    have hwW : w ∈ W := by
      rw [← hw]
      exact subset_closure rfl
    have haLT : i' w ∈ T := hWT ⟨w, hwW, rfl⟩
    haveI := hdom (i' w)
    have : y2' ∈ T := mem_of_specializes_of_isDomain hT haLT (hy2'y1'.trans hy1'aL)
    exact hTc.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr this)

/-! ### The field-changed embedding -/

/-- The base change `X ×_S S' → A ×_S S'` of `i : X → A` along `g : S' → S` sits in a cartesian
square over `i`. -/
private theorem isPullback_pullbackMap {X A S S' : Scheme.{u}} (s : A ⟶ S) (i : X ⟶ A)
    (g : S' ⟶ S) :
    IsPullback (pullback.map (i ≫ s) g s g i (𝟙 _) (𝟙 _) (by simp) (by simp))
      (pullback.fst (i ≫ s) g) (pullback.fst s g) i := by
  refine (IsPullback.of_bot ?_ (by simp) (IsPullback.of_hasPullback s g)).flip
  rw [show pullback.map (i ≫ s) g s g i (𝟙 _) (𝟙 _) (by simp) (by simp) ≫ pullback.snd s g =
    pullback.snd (i ≫ s) g by simp]
  exact IsPullback.of_hasPullback _ _

/-- **Admissibility under change of fields.** If `X ⊆ A` is admissible over `K` and `X_{L,σ}` is a
disjoint union of varieties, then `X_{L,σ} ⊆ A_{L,σ}` is admissible over `L`. -/
private theorem isAdmissibleEmbedding_fieldChange {K L : Type u} [Field K] [Field L]
    (σ : K →+* L) {X A : Scheme.{u}} (sA : A ⟶ Spec (.of K)) (i : X ⟶ A)
    (h : IsAdmissibleEmbedding sA i)
    (hXL : IsDisjointUnionOfVarieties
      (pullback.snd (i ≫ sA) (Spec.map (CommRingCat.ofHom σ)))) :
    IsAdmissibleEmbedding (pullback.snd sA (Spec.map (CommRingCat.ofHom σ)))
      (pullback.map (i ≫ sA) (Spec.map (CommRingCat.ofHom σ)) sA
        (Spec.map (CommRingCat.ofHom σ)) i (𝟙 _) (𝟙 _) (by simp) (by simp)) := by
  set φ := Spec.map (CommRingCat.ofHom σ)
  set iL := pullback.map (i ≫ sA) φ sA φ i (𝟙 _) (𝟙 _) (by simp) (by simp)
  haveI := flat_spec_map σ
  haveI : CharZero K := h.1
  haveI : IsClosedImmersion i := h.2.2.2.1
  haveI : IsAffine A := h.2.2.2.2.1
  haveI : LocallyOfFiniteType sA := (embeddingTriple_mem_sncTriples h).2.2.1
  haveI : Smooth sA := (MMP.Mori.isSmoothScheme_iff sA).mp h.2.2.2.2.2.1
  have sqA : IsPullback (pullback.fst sA φ) (pullback.snd sA φ) sA φ := .of_hasPullback _ _
  have sqX := isPullback_pullbackMap sA i φ
  haveI : Flat (pullback.fst sA φ) := MorphismProperty.of_isPullback sqA.flip inferInstance
  haveI : Flat (pullback.fst (i ≫ sA) φ) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback (i ≫ sA) φ).flip inferInstance
  haveI := MorphismProperty.of_isPullback (P := @IsClosedImmersion) sqX.flip inferInstance
  haveI : Smooth (pullback.snd sA φ) := MorphismProperty.of_isPullback sqA inferInstance
  refine ⟨charZero_of_injective_ringHom σ.injective, isAffine_of_isAffineHom iL,
    by simpa [iL] using hXL, inferInstance, inferInstance,
    (MMP.Mori.isSmoothScheme_iff _).mpr inferInstance,
    equidimensional_of_isPullback σ sA _ _ sqA h.2.2.2.2.2.2.1,
    codim_of_flat i _ _ _ sqX.w (fun a ↦ ?_) h.2.2.2.2.2.2.2⟩
  haveI := isRegularLocalRing_stalk_of_smooth_over_field (pullback.snd sA φ) a
  exact IsRegularLocalRing.isDomain _

/-- The triple `(A_{L,σ}, I_{X_{L,σ}}, ∅)` is the field change of `(A, I_X, ∅)`. -/
private theorem embeddingTriple_fieldChange {K L : Type u} [Field K] [Field L]
    (σ : K →+* L) {X A : Scheme.{u}} (sA : A ⟶ Spec (.of K)) (i : X ⟶ A) [IsClosedImmersion i] :
    embeddingTriple (pullback.snd sA (Spec.map (CommRingCat.ofHom σ)))
        (pullback.map (i ≫ sA) (Spec.map (CommRingCat.ofHom σ)) sA
          (Spec.map (CommRingCat.ofHom σ)) i (𝟙 _) (𝟙 _) (by simp) (by simp)) =
      (embeddingTriple sA i).fieldChange σ := by
  have hE : (OrderedDivisor.empty A).comap (pullback.fst sA (Spec.map (CommRingCat.ofHom σ))) =
      OrderedDivisor.empty _ := by
    unfold OrderedDivisor.comap OrderedDivisor.empty
    congr 1
    funext j
    exact j.elim0
  unfold embeddingTriple FieldBlowupTriple.fieldChange
  rw [Kollar.ker_eq_comap_of_isPullback (isPullback_pullbackMap sA i _)]
  erw [hE]

/-- `𝓑𝓡_A(X)` unfolded at an snc triple. -/
private theorem embeddedResolution_eq_of_mem_sncTriples {k : Type u} [Field k] {X A : Scheme.{u}}
    (sA : A ⟶ Spec (.of k)) (i : X ⟶ A) (hs : embeddingTriple sA i ∈ sncTriples) :
    embeddedResolution sA i =
      (embeddedResolutionSequence (canonicalPrincipalization _ hs) i).reduction := by
  unfold embeddedResolution
  rw [dif_pos hs]

end Proof_lem_kr3f_embedded_resolution_field_change

namespace MMP.Resolution

open CategoryTheory AlgebraicGeometry Limits
open MMP.Resolution.ClosedBlowupSequence
open Proof_lem_kr3f_embedded_resolution_field_change

universe u

/-- Embedded resolution commutes with change of fields (Kollár p. 146): for an admissible
embedding `i : X ⟶ A` over `K` and a field extension `σ : K →+* L` such that `X_{L,σ}` is a
disjoint union of varieties, the base change `X_{L,σ} ⟶ A_{L,σ}` is an admissible embedding and
`𝓑𝓡_{A_{L,σ}}(X_{L,σ}) = p_σ^* 𝓑𝓡_A(X)`. -/
@[mmp "lem_kr3f_embedded_resolution_field_change"]
public theorem isAdmissibleEmbedding_fieldChange_and_embeddedResolution_eq
    {K L : Type u} [Field K] [Field L] (σ : K →+* L) {X A : Scheme.{u}}
    (sA : A ⟶ Spec (.of K)) (i : X ⟶ A) (h : IsAdmissibleEmbedding sA i)
    (hXL : IsDisjointUnionOfVarieties
      (Limits.pullback.snd (i ≫ sA) (Spec.map (CommRingCat.ofHom σ)))) :
    IsAdmissibleEmbedding (Limits.pullback.snd sA (Spec.map (CommRingCat.ofHom σ)))
        (Limits.pullback.map (i ≫ sA) (Spec.map (CommRingCat.ofHom σ)) sA
          (Spec.map (CommRingCat.ofHom σ)) i (𝟙 _) (𝟙 _) (by simp) (by simp)) ∧
      embeddedResolution (Limits.pullback.snd sA (Spec.map (CommRingCat.ofHom σ)))
          (Limits.pullback.map (i ≫ sA) (Spec.map (CommRingCat.ofHom σ)) sA
            (Spec.map (CommRingCat.ofHom σ)) i (𝟙 _) (𝟙 _) (by simp) (by simp)) =
        (embeddedResolution sA i).pullback
          (Limits.pullback.fst (i ≫ sA) (Spec.map (CommRingCat.ofHom σ))) := by
  have h' := isAdmissibleEmbedding_fieldChange σ sA i h hXL
  refine ⟨h', ?_⟩
  haveI := flat_spec_map σ
  haveI := surjective_spec_map σ
  haveI : IsClosedImmersion i := h.2.2.2.1
  have sqX := IsPullback.of_hasPullback (i ≫ sA) (Spec.map (CommRingCat.ofHom σ))
  haveI := MorphismProperty.of_isPullback (P := @Flat)
    (IsPullback.of_hasPullback sA (Spec.map (CommRingCat.ofHom σ))).flip inferInstance
  haveI := MorphismProperty.of_isPullback (P := @Flat) sqX.flip inferInstance
  haveI := MorphismProperty.of_isPullback (P := @Surjective) sqX.flip inferInstance
  have hs := embeddingTriple_mem_sncTriples h
  have hs' := embeddingTriple_mem_sncTriples h'
  have he := embeddingTriple_fieldChange σ sA i
  have htL : (embeddingTriple sA i).fieldChange σ ∈ triples :=
    he ▸ mem_triples_iff.2 ⟨hs', h'.2.2.2.2.2.2.1⟩
  -- Kollár 3.72(4): `𝓑𝓟^can` commutes with the change of fields.
  have hB : canonicalPrincipalization _ hs' =
      (canonicalPrincipalization (embeddingTriple sA i) hs).pullback
        (pullback.fst sA (Spec.map (CommRingCat.ofHom σ))) :=
    (eq_of_heq (canonicalPrincipalization_heq he hs' (triples_subset_sncTriples htL))).trans
      ((canonicalPrincipalization_properties.{u, u, u}).2.2.2.2.2.1 _
        (mem_triples_iff.2 ⟨hs, h.2.2.2.2.2.2.1⟩) L σ htL)
  rw [embeddedResolution_eq_of_mem_sncTriples _ _ hs', hB,
    embeddedResolution_eq_of_mem_sncTriples _ _ hs]
  exact (Kollar.reduction_embeddedResolutionSequence_pullback_of_flat_of_comm sA i h.2.2.1 _ _ _ _
    _ (isPullback_pullbackMap sA i _).w h'.2.2.1).trans
    (reduction_pullback_eq_pullback_reduction _ _)

end MMP.Resolution
