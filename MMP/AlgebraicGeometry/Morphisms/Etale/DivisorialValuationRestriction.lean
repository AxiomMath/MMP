module
public import MMP.AlgebraicGeometry.Singularities.DivisorialValuationFiniteRestriction
public import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram.GraphDivisorBranchCounts
public import MMP.AlgebraicGeometry.Resolution.StrongResolution.QuasiProjective

/-!
# Restriction of divisorial valuations along étale maps

Let `q : Y_e ⟶ Y_0` be a dominant étale morphism of normal varieties over a field `k` of
characteristic zero and `η' ∈ Y_e` a point with `κ(q η') → κ(η')` an isomorphism. A normalized
divisorial valuation `w` of `k(Y_e)` with centre `closure {η'}` restricts to a normalized
divisorial valuation of `k(Y_0)` with centre `closure {q η'}`, and this restriction is injective
on such valuations. The morphism `q` need not be finite.

## Main results

* `MMP.Intersection.isCentre_comap_functionFieldMap_of_etale`: the restriction is divisorial
  with centre `closure {q η'}`.
* `MMP.Intersection.injOn_comap_functionFieldMap_of_etale`: the restriction is injective on the
  valuations centred at `closure {η'}`.

## Implementation notes

The restriction is `w.comap (functionFieldMap q)`. It is first written as `v ^ e` with `v`
divisorial; realizing `v` by a prime divisor `E` on a smooth projective model `W` of `Y_0`
(`MMP.Resolution.exists_isSmoothScheme_isProjectiveMorphism_forall_valuation_eq`), the étale base
change of `W` shows `e = 1`. For injectivity, each valuation is `ord_{E'}` for a prime divisor of
`W ×_{Y_0} Y_e` over the generic point of `E` and over `η'`, and since `κ(q η') ≅ κ(η')` there is
only one such point. The auxiliary lemmas live in the namespaces `Proof_<tag>`.

## References

* [OpenAI, *Projective lc fourfolds*], restriction of divisorial valuations along étale maps.
-/

@[expose] public section

universe u

namespace Proof_lem_oai4_local_restriction_injective_b

open CategoryTheory TopologicalSpace AlgebraicGeometry MMP.Intersection

/-- A proper divisor over a normal variety has a nonempty centre. -/
private lemma hasNonemptyCenter_valuation {k : Type u} [Field k] {Y : Scheme.{u}}
    [IsIntegral Y] {s : Y ⟶ Spec (.of k)} [IsVariety k s] [IsNormal Y]
    (F : MMP.Mori.DivisorOver k s) (hF : IsProper F.f) :
    MMP.Flips.HasNonemptyCenter k s F.valuation := by
  haveI := F.isIntegral
  haveI := F.isNormal
  haveI := F.isLocallyNoetherian
  haveI := F.isDominant
  exact ⟨⟨F.Y, F.f ≫ s, F.isNormalVariety, F.E,
    MMP.Mori.functionFieldAlgEquiv s F.f F.isBirationalMorphism.functionFieldMap_bijective, rfl⟩,
    ⟨F, hF⟩, rfl⟩

/-- The restriction of a normalized divisorial valuation along an étale dominant morphism of
normal varieties is a normalized divisorial valuation (the ramification index is `1`). -/
private lemma isNormalizedDivisorialValuation_comap_of_etale {k : Type u} [Field k] [CharZero k]
    {Y₀ Yₑ : Scheme.{u}} [IsIntegral Y₀] [IsIntegral Yₑ]
    (s₀ : Y₀ ⟶ Spec (.of k)) (q : Yₑ ⟶ Y₀) [Etale q] [IsDominant q]
    (h₀ : MMP.Mori.IsNormalVariety k s₀) (hₑ : MMP.Mori.IsNormalVariety k (q ≫ s₀))
    {w : Valuation Yₑ.functionField (WithZero (Multiplicative ℤ))}
    (hw : IsNormalizedDivisorialValuation k (q ≫ s₀) w) :
    IsNormalizedDivisorialValuation k s₀ (w.comap (functionFieldMap q)) := by
  haveI : IsVariety k s₀ := h₀.1
  haveI : IsNormal Y₀ := h₀.2
  haveI : IsVariety k (q ≫ s₀) := hₑ.1
  haveI : IsNormal Yₑ := hₑ.2
  obtain ⟨v, ⟨F, hFp, rfl⟩, e, he, hve⟩ :=
    MMP.Fourfold.exists_isNormalizedDivisorialValuation_comap_eq_pow k s₀ q h₀.1 hₑ.1 w hw
  haveI : ∀ i : Empty, IsProper ((fun i => i.elim : ∀ i : Empty, Empty.elim i ⟶ Y₀) i) :=
    fun i => i.elim
  obtain ⟨W, μ, hW, hμb, -, hWsm, hμp, -, hE, -⟩ :=
    MMP.Resolution.exists_isSmoothScheme_isProjectiveMorphism_forall_valuation_eq (S := Y₀) s₀
      (ι := Empty) (X := Empty.elim) (fun i => i.elim) (fun i => i.elim) (fun i => i.elim)
      (κ := Unit) (fun _ => F.valuation) (fun _ => hasNonemptyCenter_valuation F hFp)
  obtain ⟨E, hEv⟩ := hE ()
  haveI : IsVariety k (μ ≫ s₀) := hW.1
  haveI : IsNormal W := hW.2
  haveI : IsLocallyNoetherian W :=
    haveI := hW.1.toLocallyOfFiniteType
    LocallyOfFiniteType.isLocallyNoetherian (μ ≫ s₀)
  haveI : Smooth (μ ≫ s₀) := hWsm.smooth
  haveI : IsDominant μ := hμb.isDominant
  haveI : IsLocallyNoetherian Y₀ :=
    haveI := h₀.1.toLocallyOfFiniteType
    LocallyOfFiniteType.isLocallyNoetherian s₀
  haveI : CompactSpace Y₀ := QuasiCompact.compactSpace_of_compactSpace s₀
  haveI : IsNoetherian Y₀ := {}
  haveI : IsProper μ := isProper_of_isProjectiveMorphism μ hμp
  obtain ⟨U, hU, hμU⟩ := exists_dense_open_isIso_morphismRestrict_of_isBirational_of_isNoetherian μ
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hμb)
  obtain ⟨-, -, -, -, -, -, -, rfl⟩ :=
    MMP.Fourfold.exists_primeDivisor_valuationOver_eq_of_etale q rfl μ rfl hμp U hU hμU E
      w hw e he (fun g => by rw [hve g, ← hEv]; rfl)
  exact ⟨F, hFp, by ext g; simpa using hve g⟩

/-- If the restriction of `ord_{D'}` along a dominant `q` is `ord_F`, then `q` maps the centre
point of `D'` to the centre point of `F`: both local rings are dominated by `ord_F`. -/
private lemma map_genericPoint_eq_of_comap_valuation_eq {k : Type u} [Field k]
    {Y₀ Yₑ : Scheme.{u}} [IsIntegral Y₀] [IsIntegral Yₑ]
    (s₀ : Y₀ ⟶ Spec (.of k)) [IsSeparated s₀] (q : Yₑ ⟶ Y₀) [IsDominant q]
    (D' : MMP.Mori.DivisorOver k (q ≫ s₀)) (F : MMP.Mori.DivisorOver k s₀)
    (h : D'.valuation.comap (functionFieldMap q) = F.valuation) :
    q.base (D'.f D'.E.genericPoint) = F.f F.E.genericPoint := by
  haveI : IsDominant D'.f := D'.isDominant
  refine MMP.Positivity.DivisorOver.eq_of_dominates s₀ F.valuation (fun a => ?_) (fun a ha => ?_)
    (MMP.Positivity.DivisorOver.valuation_algebraMap_le_one F _ rfl)
    (MMP.Positivity.DivisorOver.valuation_algebraMap_lt_one F _ rfl)
  · rw [← h, Valuation.comap_apply, MMP.Mori.functionFieldMap_algebraMap_stalk]
    exact MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D' _ rfl _
  · rw [← h, Valuation.comap_apply, MMP.Mori.functionFieldMap_algebraMap_stalk]
    refine MMP.Positivity.DivisorOver.valuation_algebraMap_lt_one D' _ rfl _ ?_
    exact (IsLocalRing.mem_maximalIdeal _).2 fun hu =>
      (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit _ _ hu)

end Proof_lem_oai4_local_restriction_injective_b

namespace MMP.Intersection

open CategoryTheory TopologicalSpace AlgebraicGeometry
open Proof_lem_oai4_local_restriction_injective_b

/-- **Restriction of a divisorial valuation along an étale map.** Let `q : Y_e ⟶ Y_0` be a
dominant étale morphism of normal varieties over a field `k` of characteristic zero, and let
`η' ∈ Y_e` be a point with `κ(q η') → κ(η')` an isomorphism. If `w` is a normalized divisorial
valuation of `k(Y_e)` with centre `closure {η'}`, then `w.comap (functionFieldMap q)` is a
normalized divisorial valuation of `k(Y_0)` with centre `closure {q η'}`. -/
@[mmp "lem_oai4_local_restriction_injective_b"]
public theorem isCentre_comap_functionFieldMap_of_etale {k : Type u} [Field k] [CharZero k]
    {Y₀ Yₑ : Scheme.{u}} [IsIntegral Y₀] [IsIntegral Yₑ]
    (s₀ : Y₀ ⟶ Spec (.of k)) (q : Yₑ ⟶ Y₀) [Etale q] [IsDominant q]
    (h₀ : MMP.Mori.IsNormalVariety k s₀) (hₑ : MMP.Mori.IsNormalVariety k (q ≫ s₀))
    (η' : Yₑ) (hκ : IsIso (q.residueFieldMap η'))
    (Zₑ : IrreducibleCloseds Yₑ) (hZₑ : (Zₑ : Set Yₑ) = closure {η'})
    (Z₀ : IrreducibleCloseds Y₀) (hZ₀ : (Z₀ : Set Y₀) = closure {q.base η'})
    (w : Valuation Yₑ.functionField (WithZero (Multiplicative ℤ)))
    (hw : IsCentre k (q ≫ s₀) w Zₑ) :
    IsCentre k s₀ (w.comap (functionFieldMap q)) Z₀ := by
  obtain ⟨D', hD'p, rfl, rfl⟩ := hw
  have hη' : D'.f D'.E.genericPoint = η' := by
    have h := D'.center_eq_closure_genericPoint
    rw [hZₑ] at h
    exact (inseparable_iff_closure_eq.2 h.symm).eq
  obtain ⟨F, hFp, hF⟩ := isNormalizedDivisorialValuation_comap_of_etale s₀ q h₀ hₑ ⟨D', hD'p, rfl⟩
  haveI : IsVariety k s₀ := h₀.1
  refine ⟨F, hFp, hF, IrreducibleCloseds.ext ?_⟩
  rw [hZ₀, F.center_eq_closure_genericPoint, ← hη',
    map_genericPoint_eq_of_comap_valuation_eq s₀ q D' F hF]

end MMP.Intersection

namespace Proof_lem_oai4_local_restriction_injective

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry MMP.Intersection

/-- Two points of `X ×_S Y` with the same images in `X` and in `Y` agree when
`κ(s) → κ(y)` is an isomorphism: the points over `(x, y)` are those of
`Spec (κ(x) ⊗_{κ(s)} κ(y)) = Spec κ(x)`. -/
private lemma eq_of_fst_eq_of_snd_eq {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    {t₁ t₂ : ↑(pullback f g)}
    (h₁ : pullback.fst f g t₁ = pullback.fst f g t₂)
    (h₂ : pullback.snd f g t₁ = pullback.snd f g t₂)
    (hκ : IsIso (g.residueFieldMap (pullback.snd f g t₁))) : t₁ = t₂ := by
  have hT : Scheme.Pullback.Triplet.ofPoint t₁ = Scheme.Pullback.Triplet.ofPoint t₂ :=
    Scheme.Pullback.Triplet.ext h₁ h₂
  set T := Scheme.Pullback.Triplet.ofPoint t₁
  have : IsIso ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y) := by
    have : IsIso (g.residueFieldMap T.y) := hκ
    infer_instance
  have : IsIso T.tensorInl := (IsPushout.of_hasPushout _ _).isIso_inl_of_isIso
  have hfield : IsField T.tensor :=
    MulEquiv.isField (Field.toIsField (X.residueField T.x))
      (asIso T.tensorInl).symm.commRingCatIsoToRingEquiv.toMulEquiv
  letI := hfield.toField
  have hsub : Subsingleton (Spec T.tensor) := by
    change Subsingleton (PrimeSpectrum T.tensor)
    infer_instance
  have hsub₂ : Subsingleton (Spec (Scheme.Pullback.Triplet.ofPoint t₂).tensor) := hT ▸ hsub
  exact Scheme.Pullback.carrierEquiv.injective <|
    Scheme.Pullback.carrierEquiv_eq_iff.2 ⟨hT, @Subsingleton.elim _ hsub₂ _ _⟩

/-- Let `μ : W ⟶ Y₀` be a smooth projective birational model and `E` a prime divisor of `W`. A
valuation `w` of `k(Yₑ)` centred at `closure {η'}` whose restriction along the étale `q` is
`ord_E` is `ord_{E'}` for a prime divisor `E'` of `W ×_{Y₀} Yₑ` whose generic point lies over
`η_E` and over `η'`. -/
private lemma exists_primeDivisor_pullback_of_isCentre {k : Type u} [Field k]
    {Y₀ Yₑ W : Scheme.{u}} [IsIntegral Y₀] [IsIntegral Yₑ] {s₀ : Y₀ ⟶ Spec (.of k)}
    (q : Yₑ ⟶ Y₀) [Etale q] [IsDominant q]
    [IsVariety k s₀] [IsVariety k (q ≫ s₀)] [IsNormal Y₀] [IsNormal Yₑ]
    (μ : W ⟶ Y₀) [IsVariety k (μ ≫ s₀)] [Smooth (μ ≫ s₀)] [IsIntegral W] [IsNormal W]
    [IsLocallyNoetherian W] [IsDominant μ] (hμp : IsProjectiveMorphism μ)
    {U : Y₀.Opens} (hU : Dense (U : Set Y₀)) (hμU : IsIso (μ ∣_ U))
    (E : MMP.Mori.PrimeDivisor W) {η' : Yₑ} {Zₑ : IrreducibleCloseds Yₑ}
    (hZₑ : (Zₑ : Set Yₑ) = closure {η'})
    {w : Valuation Yₑ.functionField (WithZero (Multiplicative ℤ))}
    (hw : IsCentre k (q ≫ s₀) w Zₑ) (hwE : ∀ g, w (functionFieldMap q g) = E.valuationOver μ g) :
    ∃ (_ : IsIntegral (pullback μ q)) (_ : IsNormal (pullback μ q))
      (_ : IsLocallyNoetherian (pullback μ q)) (_ : IsDominant (pullback.snd μ q))
      (E' : MMP.Mori.PrimeDivisor (pullback μ q)),
      pullback.fst μ q E'.genericPoint = E.genericPoint ∧
        pullback.snd μ q E'.genericPoint = η' ∧ w = E'.valuationOver (pullback.snd μ q) := by
  obtain ⟨D, hDp, rfl, hDc⟩ := hw
  have hη' : D.f D.E.genericPoint = η' := by
    have h := D.center_eq_closure_genericPoint
    rw [← hDc, hZₑ] at h
    exact (inseparable_iff_closure_eq.2 h.symm).eq
  obtain ⟨i1, i2, i3, i4, E', hE'1, hE'2, -⟩ :=
    MMP.Fourfold.exists_primeDivisor_valuationOver_eq_of_etale q rfl μ rfl hμp U hU hμU E
      D.valuation ⟨D, hDp, rfl⟩ 1 le_rfl (fun g => by rw [pow_one, hwE])
  refine ⟨i1, i2, i3, i4, E', hE'1, ?_, hE'2⟩
  refine MMP.Positivity.DivisorOver.eq_of_dominates (q ≫ s₀) D.valuation (fun a => ?_)
    (fun a ha => ?_) (MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D η' hη'.symm)
    (MMP.Positivity.DivisorOver.valuation_algebraMap_lt_one D η' hη'.symm)
  · rw [hE'2, MMP.Mori.PrimeDivisor.valuationOver_apply,
      MMP.Mori.functionFieldMap_algebraMap_stalk]
    exact (E'.divisorialValuation_le_one_iff _).2 ⟨_, rfl⟩
  · rw [hE'2, MMP.Mori.PrimeDivisor.valuationOver_apply,
      MMP.Mori.functionFieldMap_algebraMap_stalk]
    exact (E'.divisorialValuation_algebraMap_lt_one_iff _).2
      (map_nonunit ((pullback.snd μ q).stalkMap E'.genericPoint).hom a ha)

end Proof_lem_oai4_local_restriction_injective

namespace MMP.Intersection

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
open Proof_lem_oai4_local_restriction_injective

/-- **Restriction of divisorial valuations along an étale map is injective.** Let
`q : Y_e ⟶ Y_0` be a dominant étale morphism of normal varieties over a field `k` of
characteristic zero, and let `η' ∈ Y_e` be a point with `κ(q η') → κ(η')` an isomorphism. Then
`w ↦ w.comap (functionFieldMap q)` is injective on the normalized divisorial valuations of
`k(Y_e)` with centre `closure {η'}`. The morphism `q` need not be finite. -/
@[mmp "lem_oai4_local_restriction_injective"]
public theorem injOn_comap_functionFieldMap_of_etale {k : Type u} [Field k] [CharZero k]
    {Y₀ Yₑ : Scheme.{u}} [IsIntegral Y₀] [IsIntegral Yₑ]
    (s₀ : Y₀ ⟶ Spec (.of k)) (q : Yₑ ⟶ Y₀) [Etale q] [IsDominant q]
    (h₀ : MMP.Mori.IsNormalVariety k s₀) (hₑ : MMP.Mori.IsNormalVariety k (q ≫ s₀))
    (η' : Yₑ) (hκ : IsIso (q.residueFieldMap η'))
    (Zₑ : IrreducibleCloseds Yₑ) (hZₑ : (Zₑ : Set Yₑ) = closure {η'}) :
    Set.InjOn (fun w : Valuation Yₑ.functionField (WithZero (Multiplicative ℤ)) ↦
        w.comap (functionFieldMap q))
      {w | IsCentre k (q ≫ s₀) w Zₑ} := by
  intro w₁ hw₁ w₂ hw₂ h12
  simp only at h12
  haveI : IsVariety k s₀ := h₀.1
  haveI : IsNormal Y₀ := h₀.2
  haveI : IsVariety k (q ≫ s₀) := hₑ.1
  haveI : IsNormal Yₑ := hₑ.2
  obtain ⟨F, hFp, hFv, -⟩ :=
    MMP.Intersection.isCentre_comap_functionFieldMap_of_etale s₀ q h₀ hₑ η' hκ Zₑ hZₑ
      ⟨closure {q.base η'}, isIrreducible_singleton.closure, isClosed_closure⟩ rfl w₁ hw₁
  have hvc : MMP.Flips.HasNonemptyCenter k s₀ (w₁.comap (functionFieldMap q)) := by
    rw [hFv]
    exact Proof_lem_oai4_local_restriction_injective_b.hasNonemptyCenter_valuation F hFp
  haveI : ∀ i : Empty, IsProper ((fun i => i.elim : ∀ i : Empty, Empty.elim i ⟶ Y₀) i) :=
    fun i => i.elim
  obtain ⟨W, μ, hW, hμb, -, hWsm, hμp, -, hE, -⟩ :=
    MMP.Resolution.exists_isSmoothScheme_isProjectiveMorphism_forall_valuation_eq (S := Y₀) s₀
      (ι := Empty) (X := Empty.elim) (fun i => i.elim) (fun i => i.elim) (fun i => i.elim)
      (κ := Unit) (fun _ => w₁.comap (functionFieldMap q)) (fun _ => hvc)
  obtain ⟨E, hEv⟩ := hE ()
  haveI : IsVariety k (μ ≫ s₀) := hW.1
  haveI : IsIntegral W := hW.1.toIsIntegral
  haveI : IsNormal W := hW.2
  haveI : IsLocallyNoetherian W :=
    haveI := hW.1.toLocallyOfFiniteType
    LocallyOfFiniteType.isLocallyNoetherian (μ ≫ s₀)
  haveI : Smooth (μ ≫ s₀) := hWsm.smooth
  haveI : IsDominant μ := hμb.isDominant
  haveI : IsLocallyNoetherian Y₀ :=
    haveI := h₀.1.toLocallyOfFiniteType
    LocallyOfFiniteType.isLocallyNoetherian s₀
  haveI : CompactSpace Y₀ := QuasiCompact.compactSpace_of_compactSpace s₀
  haveI : IsNoetherian Y₀ := {}
  haveI : IsProper μ := isProper_of_isProjectiveMorphism μ hμp
  obtain ⟨U, hU, hμU⟩ := exists_dense_open_isIso_morphismRestrict_of_isBirational_of_isNoetherian μ
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hμb)
  have hE₁ : ∀ g, w₁ (functionFieldMap q g) = E.valuationOver μ g := fun g => by
    rw [← Valuation.comap_apply, ← hEv]; rfl
  have hE₂ : ∀ g, w₂ (functionFieldMap q g) = E.valuationOver μ g := fun g => by
    rw [← Valuation.comap_apply, ← h12, Valuation.comap_apply, hE₁]
  obtain ⟨-, -, -, -, E₁, h11, h12', rfl⟩ :=
    exists_primeDivisor_pullback_of_isCentre q μ hμp hU hμU E hZₑ hw₁ hE₁
  obtain ⟨-, -, -, -, E₂, h21, h22, rfl⟩ :=
    exists_primeDivisor_pullback_of_isCentre q μ hμp hU hμU E hZₑ hw₂ hE₂
  obtain rfl : E₁ = E₂ := AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (eq_of_fst_eq_of_snd_eq μ q (h11.trans h21.symm) (h12'.trans h22.symm) (h12' ▸ hκ))
  rfl

end MMP.Intersection

end
