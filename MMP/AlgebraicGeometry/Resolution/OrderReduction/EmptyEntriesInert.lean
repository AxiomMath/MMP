module
public import MMP.AlgebraicGeometry.Resolution.Blowup.PointBlowupIsoOff
public import MMP.RingTheory.DiscreteValuationRing.DVRNormalization
public import MMP.AlgebraicGeometry.Curves.DegreeEuler
public import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
public import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
public import MMP.AlgebraicGeometry.Resolution.OrderRestriction
public import MMP.AlgebraicGeometry.Resolution.SNCHypersurfaceCentres
public import MMP.AlgebraicGeometry.Resolution.OrderReduction.Functor
public import MMP.AlgebraicGeometry.Resolution.MaximalOrderAttained
public import MMP.AlgebraicGeometry.Resolution.BirationalTransformTriple
public import MMP.AlgebraicGeometry.MMP.Steps
public import MMP.AlgebraicGeometry.Resolution.BlowupSequence.FlatDescent
public import MMP.AlgebraicGeometry.Resolution.Blowup.StrictTransform

/-!
# Kollár, *Lectures on resolution of singularities*: auxiliary results

This file collects lemmas from Kollár's lectures used along the resolution of singularities:
the factorization of a composite of point blow-ups through the blow-up of a point (1.48), the
DVR-normalization of a polynomial ring (1.24), separabilization of a finite extension by a finite
purely inseparable one (proof of 1.33), the projection formula for intersection numbers with
curves (2.9–2.16), the local agreement of closed subschemes with the same formal germ, the bound of
the order of a polynomial by its degree (3.61), simple normal crossings inside a hypersurface,
the inertness of empty entries of ordered divisors along blow-up sequences and under
`𝓑𝓜𝓞` (3.72, 3.111), the locality of commuting with a morphism (3.34, 3.104), and the
preservation of simple normal crossings when blowing up a centre inside a hypersurface
(3.103–3.104).

## Main results

* `MMP.Resolution.exists_isCompositeOfPointBlowups_comp_blowUpToBase`
* `MMP.Resolution.Kollar.dvrNormalization_mvPolynomial_eq_range`
* `MMP.Resolution.Kollar.exists_finiteDimensional_pow_mem_isSeparable_sup`
* `MMP.Resolution.lineBundleCurveIntersection_pullback`
* `MMP.Resolution.exists_eq_of_map_adicCompletion_eq`
* `MMP.Resolution.Kollar.mult_localization_le_of_totalDegree_le`
* `MMP.Resolution.Kollar.hasSNCWith_iff_hasSNCWith_comap`
* `MMP.Resolution.ClosedBlowupSequence.deleteEmpty_orderedTotalTransform_eq`
* `MMP.Resolution.ignoresEmptyEntriesMarked_bmoFunctor`
* `MMP.Resolution.BlowupSequenceFunctor.eq_pullback_reduction_of_isOpenCoverMap`
* `MMP.Resolution.isOrderedSNC_cons_birationalTransform_totalTransform`
* `MMP.Resolution.ker_restrictHom_cons_nil_eq_vanishingIdeal`

## References

* [Kollár, *Lectures on resolution of singularities*][kollar2007]
-/

@[expose] public section

universe u

/-!
## A composite of point blow-ups factors through the blow-up of a point it does not leave alone

Let `S` be a regular surface, `g : S' → S` a composite of point blow-ups and `p ∈ S` a closed
point over no open neighbourhood of which `g` is an isomorphism. Then `g` factors as
`S' → B_pS → S`, the second map the blow-up `σ_p` of `p` and the first again a composite of point
blow-ups (Kollár 1.48).

### References

* [Kollár, *Lectures on resolution of singularities*, 1.48][kollar2007]
-/

section

open CategoryTheory AlgebraicGeometry MMP.Resolution

namespace MMP.Resolution.FoldAux.kr1b_factorization_through_blowup

/-!
### The proof of Kollár 1.48

Let `g : S' → S` be a composite of point blow-ups and `p ∈ S` a closed point over no open
neighbourhood of which `g` is an isomorphism. Then `g = h ≫ σ_p`, with `σ_p : B_pS → S` the
blow-up of `p` and `h` again a composite of point blow-ups (Kollár 1.48).

The proof is by induction on the number of blow-ups. Peel off the first blow-up `σ₀ : B_{p₀}S → S`.
If `p₀ = p` there is nothing to do. Otherwise `p` has a unique preimage `p'` on `B_{p₀}S`, whose
reduced ideal is the pull-back of that of `p`. The remaining composite is not an isomorphism near
`p'`, so by induction it factors through `B_{p'}B_{p₀}S`. The two towers `B_{p'}B_{p₀}S` and
`B_{p₀'}B_pS` over `S` are isomorphic, since both are the blow-up of `S` in the product of the two
point ideals ([Stacks, Tag 080A], `AlgebraicGeometry.TwoStepTower.totalTowerIso`).

### Implementation notes

The regularity of `S` is not used: the argument works for point blow-ups of an arbitrary scheme,
which is the form the induction needs, since it passes to the blow-up `B_{p₀}S`. Where the source
glues two local isomorphisms over `S ∖ {p}` and `S ∖ {p₀}`, the isomorphism of the two towers is
taken from the universal property of the blow-up in the product ideal instead.

### References

* [Kollár, *Lectures on resolution of singularities*, 1.48][kollar2007]
-/

private theorem isCompositeOfPointBlowupsOfLength_iso_comp :
    ∀ (m : ℕ) {S'' S' S : Scheme.{u}} (e : S'' ⟶ S') [IsIso e] (g : S' ⟶ S),
      IsCompositeOfPointBlowupsOfLength m g → IsCompositeOfPointBlowupsOfLength m (e ≫ g)
  | 0, _, _, _, e, _, g, hg => by
      have : IsIso g := hg
      change IsIso (e ≫ g)
      infer_instance
  | m + 1, _, _, _, e, _, g, hg => by
      obtain ⟨W, h, w, hw, hh, φ, rfl⟩ := hg
      exact ⟨W, h, w, hw, hh, asIso e ≪≫ φ, by rw [Iso.trans_hom, asIso_hom, Category.assoc]⟩

private theorem isCompositeOfPointBlowupsOfLength_comp :
    ∀ (k : ℕ) {m : ℕ} {S'' S' S : Scheme.{u}} {f : S'' ⟶ S'} {g : S' ⟶ S},
      IsCompositeOfPointBlowupsOfLength k f → IsCompositeOfPointBlowupsOfLength m g →
        IsCompositeOfPointBlowupsOfLength (m + k) (f ≫ g)
  | 0, m, _, _, _, f, g, hf, hg => by
      have : IsIso f := hf
      exact isCompositeOfPointBlowupsOfLength_iso_comp m f g hg
  | k + 1, m, _, _, _, f, g, hf, hg => by
      obtain ⟨W, h, w, hw, hh, φ, rfl⟩ := hf
      exact ⟨W, h ≫ g, w, hw, isCompositeOfPointBlowupsOfLength_comp k hh hg, φ,
        by simp only [Category.assoc]⟩

private theorem exists_blowUp_iso_of_comap_eq {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
    (I : Y.IdealSheafData) (J : X.IdealSheafData) (h : I.comap f = J) :
    ∃ d : blowUp J ≅ blowUp I, d.hom ≫ blowUpToBase I = blowUpToBase J ≫ f := by
  subst h
  exact exists_blowUp_iso_comap_of_isIso f I

private theorem exists_eq_comp_blowUpToBase :
    ∀ (m : ℕ) {S' S : Scheme.{u}} {g : S' ⟶ S}, IsCompositeOfPointBlowupsOfLength (m + 1) g →
      ∃ (p₀ : S) (hp₀ : IsClosed ({p₀} : Set S))
        (g' : S' ⟶ blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p₀}, hp₀⟩)),
          IsCompositeOfPointBlowupsOfLength m g' ∧ g = g' ≫ blowUpToBase _
  | 0, S', S, g, hg => by
      obtain ⟨W, h, w, hw, hh, φ, rfl⟩ := hg
      have : IsIso h := hh
      obtain ⟨hz, -⟩ := vanishingIdeal_singleton_comap_of_isIso (inv h) w hw (h w) (by
        rw [← Scheme.Hom.comp_apply, IsIso.hom_inv_id]; rfl)
      obtain ⟨hw', hJ⟩ := vanishingIdeal_singleton_comap_of_isIso h (h w) hz w rfl
      obtain ⟨d, hd⟩ := exists_blowUp_iso_of_comap_eq h _ _ hJ
      refine ⟨h w, hz, φ.hom ≫ d.hom, ?_, ?_⟩
      · change IsIso _
        infer_instance
      · rw [Category.assoc, hd]
  | m + 1, S', S, g, hg => by
      obtain ⟨W, h, w, hw, hh, φ, rfl⟩ := hg
      obtain ⟨p₀, hp₀, g', hg', rfl⟩ := exists_eq_comp_blowUpToBase m hh
      exact ⟨p₀, hp₀, φ.hom ≫ blowUpToBase _ ≫ g', ⟨W, g', w, hw, hg', φ, rfl⟩,
        by simp only [Category.assoc]⟩

private theorem vanishingIdeal_singleton_comap_of_isOpenImmersion {W X : Scheme.{u}}
    (ι : W ⟶ X) [IsOpenImmersion ι] (w : W) (hx : IsClosed ({ι w} : Set X)) :
    ∃ hw : IsClosed ({w} : Set W),
      (Scheme.IdealSheafData.vanishingIdeal (⟨{ι w}, hx⟩ : TopologicalSpace.Closeds X)).comap ι =
        Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : TopologicalSpace.Closeds W) := by
  let M := Scheme.IdealSheafData.vanishingIdeal (⟨{ι w}, hx⟩ : TopologicalSpace.Closeds X)
  refine vanishingIdeal_singleton_comap ι (ι w) hx ι.isEmbedding.injective ?_ w rfl
  rw [isIso_iff_isOpenImmersion_and_surjective]
  refine ⟨inferInstance, ⟨fun p => ?_⟩⟩
  have hp : M.subschemeι p ∈ (M.support : Set X) := by
    rw [← M.range_subschemeι]
    exact ⟨p, rfl⟩
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal] at hp
  have : p ∈ Set.range (Limits.pullback.snd ι M.subschemeι) := by
    rw [Scheme.Pullback.range_snd]
    exact ⟨w, hp.symm⟩
  exact this

private theorem vanishingIdeal_singleton_comap_eq_top {U X : Scheme.{u}} (j : U ⟶ X)
    (z : X) (hz : IsClosed ({z} : Set X)) (hzj : z ∉ Set.range j.base) :
    (Scheme.IdealSheafData.vanishingIdeal (⟨{z}, hz⟩ : TopologicalSpace.Closeds X)).comap j =
      ⊤ := by
  rw [← Scheme.IdealSheafData.support_eq_bot_iff]
  ext y
  simp only [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage,
    Scheme.IdealSheafData.coe_support_vanishingIdeal, Set.mem_preimage, Set.mem_singleton_iff,
    TopologicalSpace.Closeds.coe_bot, Set.mem_empty_iff_false, iff_false]
  intro hy
  exact hzj ⟨y, hy⟩

private theorem idealSheafData_eq_of_comap_eq_of_sup_eq_top {X : Scheme.{u}} (U₁ U₂ : X.Opens)
    (hU : ∀ x : X, x ∈ U₁ ∨ x ∈ U₂) {I J : X.IdealSheafData}
    (h₁ : I.comap U₁.ι = J.comap U₁.ι) (h₂ : I.comap U₂.ι = J.comap U₂.ι) : I = J := by
  refine Stacks.GenericFlatness.idealSheafData_eq_of_comap_eq
    (Z := fun i : Bool => (bif i then U₁ else U₂ : X.Opens).toScheme)
    (fun i => (bif i then U₁ else U₂ : X.Opens).ι) (fun i => inferInstance) ?_ ?_
  · refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.mpr ?_
    rcases hU x with hx | hx
    · exact ⟨true, (⟨⟨x, hx⟩, rfl⟩ : x ∈ Set.range U₁.ι.base)⟩
    · exact ⟨false, (⟨⟨x, hx⟩, rfl⟩ : x ∈ Set.range U₂.ι.base)⟩
  · rintro (_ | _)
    · exact h₂
    · exact h₁

/-- Off the centre, the inverse image of a closed point under the blow-up of another closed point
is a single closed point, and the pull-back of its reduced ideal is the reduced ideal of that
point. -/
private theorem exists_comap_vanishingIdeal_blowUpToBase {X : Scheme.{u}} {a b : X}
    (ha : IsClosed ({a} : Set X)) (hb : IsClosed ({b} : Set X)) (hab : a ≠ b) :
    ∃ (b' : blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{a}, ha⟩))
      (hb' : IsClosed ({b'} : Set (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{a}, ha⟩)))),
      blowUpToBase _ b' = b ∧
        (Scheme.IdealSheafData.vanishingIdeal ⟨{b}, hb⟩).comap (blowUpToBase _) =
          Scheme.IdealSheafData.vanishingIdeal ⟨{b'}, hb'⟩ ∧
        ∀ y, blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{a}, ha⟩) y = b → y = b' := by
  set σ := blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{a}, ha⟩)
  let U : X.Opens := MMP.Resolution.Kollar.complPoint ha
  have : IsIso (σ ∣_ U) := MMP.Resolution.Kollar.isIso_blowUpToBase_restrict_compl_point ha
  let e := σ ∣_ U
  have hbU : b ∈ U := fun h => hab (Set.mem_singleton_iff.mp h).symm
  let bU : U := ⟨b, hbU⟩
  let z : (σ ⁻¹ᵁ U : _) := (inv e) bU
  have hez : e z = bU := by
    change (inv e ≫ e) bU = bU
    rw [IsIso.inv_hom_id]
    rfl
  have hσ : ∀ t : (σ ⁻¹ᵁ U : _), σ ((σ ⁻¹ᵁ U).ι t) = U.ι (e t) := fun t =>
    (congrArg (fun φ => φ.base t) (morphismRestrict_ι σ U)).symm
  have hσz : σ ((σ ⁻¹ᵁ U).ι z) = b := by
    rw [hσ, hez]
    rfl
  have huniq : ∀ y, σ y = b → y = (σ ⁻¹ᵁ U).ι z := by
    intro y hy
    have hyU : y ∈ σ ⁻¹ᵁ U := by
      change σ y ∈ U
      rw [hy]
      exact hbU
    let yU : (σ ⁻¹ᵁ U : _) := ⟨y, hyU⟩
    have h1 : U.ι (e yU) = U.ι (e z) := by
      rw [← hσ, ← hσ]
      exact hy.trans hσz.symm
    have h2 : yU = z := e.isEmbedding.injective (U.ι.isEmbedding.injective h1)
    rw [← h2]
    rfl
  have hb' : IsClosed ({(σ ⁻¹ᵁ U).ι z} : Set _) := by
    have : ({(σ ⁻¹ᵁ U).ι z} : Set _) = σ.base ⁻¹' {b} := by
      ext y
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      exact ⟨fun h => h ▸ hσz, huniq y⟩
    rw [this]
    exact hb.preimage σ.base.hom.continuous
  refine ⟨(σ ⁻¹ᵁ U).ι z, hb', hσz, ?_, huniq⟩
  refine idealSheafData_eq_of_comap_eq_of_sup_eq_top (σ ⁻¹ᵁ U)
    (σ ⁻¹ᵁ MMP.Resolution.Kollar.complPoint hb) ?_ ?_ ?_
  · intro y
    by_cases hy : σ y = a
    · right
      change σ y ∉ ({b} : Set X)
      rw [hy]
      exact hab
    · left
      exact hy
  · rw [← Scheme.IdealSheafData.comap_comp, ← morphismRestrict_ι, Scheme.IdealSheafData.comap_comp]
    have hU' : IsClosed ({U.ι bU} : Set X) := hb
    obtain ⟨hbU', h1⟩ := vanishingIdeal_singleton_comap_of_isOpenImmersion U.ι bU hU'
    obtain ⟨hz, h2⟩ := vanishingIdeal_singleton_comap_of_isIso e bU hbU' z hez
    obtain ⟨hz', h3⟩ := vanishingIdeal_singleton_comap_of_isOpenImmersion (σ ⁻¹ᵁ U).ι z hb'
    rw [h3, ← h2, ← h1]
    rfl
  · rw [vanishingIdeal_singleton_comap_eq_top _ _ hb', ← Scheme.IdealSheafData.comap_comp,
      ← morphismRestrict_ι, Scheme.IdealSheafData.comap_comp,
      vanishingIdeal_singleton_comap_eq_top _ _ hb, Scheme.IdealSheafData.comap_top]
    · rintro ⟨t, ht⟩
      apply t.2
      change (Scheme.Opens.ι _) t ∈ ({b} : Set X)
      rw [ht]
      rfl
    · rintro ⟨t, ht⟩
      apply t.2
      change σ ((σ ⁻¹ᵁ _).ι t) ∈ ({b} : Set X)
      rw [ht]
      exact hσz

private theorem exists_iso_blowUp_comap_comm {W : Scheme.{u}} (I J : W.IdealSheafData)
    (K : (blowUp I).IdealSheafData) (K' : (blowUp J).IdealSheafData)
    (hK : J.comap (blowUpToBase I) = K) (hK' : I.comap (blowUpToBase J) = K') :
    ∃ Φ : blowUp K ≅ blowUp K',
      Φ.hom ≫ blowUpToBase K' ≫ blowUpToBase J = blowUpToBase K ≫ blowUpToBase I := by
  subst hK hK'
  let e := TwoStepTower.totalTowerIso I J
  exact ⟨(Over.forget W).mapIso e, Over.w e.hom⟩

private theorem isIso_morphismRestrict_of_le {Y Z : Scheme.{u}} (g : Y ⟶ Z) {W W' : Z.Opens}
    (hle : W' ≤ W) (h : IsIso (g ∣_ W)) : IsIso (g ∣_ W') := by
  have h1 : MorphismProperty.isomorphisms Scheme ((g ∣_ W) ∣_ (W.ι ⁻¹ᵁ W')) :=
    IsZariskiLocalAtTarget.restrict (P := MorphismProperty.isomorphisms Scheme) h _
  have h2 := ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict g W (W.ι ⁻¹ᵁ W'))).mp h1
  have h3 : W.ι ''ᵁ (W.ι ⁻¹ᵁ W') = W' := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hle]
  rwa [h3] at h2

/-- If `g'` is an isomorphism over an open neighbourhood of a point `p'` off the exceptional curve
of `σ : B_{p₀}S → S`, then `g' ≫ σ` is an isomorphism over an open neighbourhood of `σ p'`. -/
private theorem exists_isIso_comp_blowUpToBase {S S' : Scheme.{u}} {p₀ : S}
    (hp₀ : IsClosed ({p₀} : Set S))
    (g' : S' ⟶ blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p₀}, hp₀⟩))
    {p' : blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p₀}, hp₀⟩)}
    (hp' : blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p₀}, hp₀⟩) p' ≠ p₀)
    (V' : (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p₀}, hp₀⟩)).Opens) (hV' : p' ∈ V')
    (hiso : IsIso (g' ∣_ V')) :
    ∃ V : S.Opens, blowUpToBase _ p' ∈ V ∧
      IsIso ((g' ≫ blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p₀}, hp₀⟩)) ∣_ V) := by
  set σ := blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p₀}, hp₀⟩)
  let U : S.Opens := MMP.Resolution.Kollar.complPoint hp₀
  have : IsIso (σ ∣_ U) := MMP.Resolution.Kollar.isIso_blowUpToBase_restrict_compl_point hp₀
  let j := (σ ⁻¹ᵁ U).ι ≫ σ
  have hj : j = σ ∣_ U ≫ U.ι := (morphismRestrict_ι σ U).symm
  have : IsOpenImmersion j := by
    rw [hj]
    infer_instance
  let V : S.Opens := ⟨j.base '' ((σ ⁻¹ᵁ U).ι ⁻¹ᵁ V' : Set _),
    j.isOpenEmbedding.isOpenMap _ ((σ ⁻¹ᵁ U).ι ⁻¹ᵁ V').2⟩
  have hp'U : p' ∈ σ ⁻¹ᵁ U := hp'
  refine ⟨V, ⟨⟨p', hp'U⟩, hV', rfl⟩, ?_⟩
  have hVU : V ≤ U := by
    rintro _ ⟨t, -, rfl⟩
    exact t.2
  have hσV : σ ⁻¹ᵁ V ≤ V' := by
    intro y hy
    obtain ⟨t, ht, hjt⟩ := hy
    have hyU : y ∈ σ ⁻¹ᵁ U := by
      change σ y ∈ U
      rw [← hjt]
      exact hVU ⟨t, ht, rfl⟩
    have : t = ⟨y, hyU⟩ := j.isOpenEmbedding.injective hjt
    subst this
    exact ht
  rw [morphismRestrict_comp]
  have h1 : IsIso (g' ∣_ σ ⁻¹ᵁ V) := isIso_morphismRestrict_of_le g' hσV hiso
  have h2 : IsIso (σ ∣_ V) := isIso_morphismRestrict_of_le σ hVU inferInstance
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 h2

private theorem exists_comp_blowUpToBase_of_isCompositeOfPointBlowupsOfLength :
    ∀ (m : ℕ) {S S' : Scheme.{u}} {g : S' ⟶ S},
    IsCompositeOfPointBlowupsOfLength m g → ∀ {p : S} (hp : IsClosed ({p} : Set S)),
      (∀ V : S.Opens, p ∈ V → ¬ IsIso (g ∣_ V)) →
        ∃ h : S' ⟶ blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩),
          IsCompositeOfPointBlowups h ∧
            g = h ≫ blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)
  | 0, S, S', g, hg, p, hp, hiso => by
      have hg' : IsIso g := hg
      exact absurd (IsZariskiLocalAtTarget.restrict (P := MorphismProperty.isomorphisms Scheme)
        hg' ⊤) (hiso ⊤ trivial)
  | m + 1, S, S', g, hg, p, hp, hiso => by
      obtain ⟨p₀, hp₀, g', hg', rfl⟩ := exists_eq_comp_blowUpToBase m hg
      by_cases hpp : p₀ = p
      · subst hpp
        exact ⟨g', ⟨m, hg'⟩, rfl⟩
      · obtain ⟨p', hp', hσp', hcomap, -⟩ :=
          exists_comap_vanishingIdeal_blowUpToBase hp₀ hp hpp
        have hiso' : ∀ V' : (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p₀}, hp₀⟩)).Opens,
            p' ∈ V' → ¬ IsIso (g' ∣_ V') := by
          intro V' hV' hV'iso
          have hne : blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p₀}, hp₀⟩) p' ≠ p₀ := by
            rw [hσp']
            exact Ne.symm hpp
          obtain ⟨V, hV, hVi⟩ := exists_isIso_comp_blowUpToBase hp₀ g' hne V' hV' hV'iso
          rw [hσp'] at hV
          exact hiso V hV hVi
        obtain ⟨h', ⟨k, hk⟩, rfl⟩ :=
          exists_comp_blowUpToBase_of_isCompositeOfPointBlowupsOfLength m hg' hp' hiso'
        obtain ⟨p₀', hp₀', -, hcomap', -⟩ :=
          exists_comap_vanishingIdeal_blowUpToBase hp hp₀ (Ne.symm hpp)
        obtain ⟨Φ, hΦ⟩ := exists_iso_blowUp_comap_comm _ _ _ _ hcomap hcomap'
        have h1 : IsCompositeOfPointBlowupsOfLength 1
            (Φ.hom ≫ blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p₀'}, hp₀'⟩)) :=
          ⟨_, 𝟙 _, p₀', hp₀', (inferInstance : IsIso (𝟙 _)), Φ, by rw [Category.comp_id]⟩
        refine ⟨h' ≫ Φ.hom ≫ blowUpToBase _,
          ⟨1 + k, isCompositeOfPointBlowupsOfLength_comp k hk h1⟩,
          ?_⟩
        rw [Category.assoc, Category.assoc, Category.assoc, hΦ]

end MMP.Resolution.FoldAux.kr1b_factorization_through_blowup

namespace MMP.Resolution

open MMP.Resolution.FoldAux.kr1b_factorization_through_blowup in
/-- **Kollár 1.48.** If `g : S' ⟶ S` is a composite of point blow-ups of a scheme and
`g` is not an isomorphism over any open neighbourhood of the closed point `p`, then
`g = h ≫ σ_p` with `σ_p : B_pS ⟶ S` the blow-up of `p` and `h : S' ⟶ B_pS` a composite of point
blow-ups. -/
@[mmp "lem_kr1b_factorization_through_blowup"]
public theorem exists_isCompositeOfPointBlowups_comp_blowUpToBase {S S' : Scheme.{u}}
    {g : S' ⟶ S} (hg : IsCompositeOfPointBlowups g)
    {p : S} (hp : IsClosed ({p} : Set S))
    (hiso : ∀ V : S.Opens, p ∈ V → ¬ IsIso (g ∣_ V)) :
    ∃ h : S' ⟶ blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩),
      IsCompositeOfPointBlowups h ∧
        g = h ≫ blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) :=
  hg.elim fun m hm =>
    exists_comp_blowUpToBase_of_isCompositeOfPointBlowupsOfLength m hm hp hiso

end MMP.Resolution

end

/-!
## The DVR-normalization of a polynomial ring over a field (Kollár 1.24)

For a field `k`, the DVR-normalization of the polynomial ring `k[x_i : i ∈ σ]` is the ring
itself, i.e. the image of `MvPolynomial σ k` in its fraction field.

### Implementation notes

The set of variables `σ` is arbitrary; finiteness is not needed, since a polynomial ring over a
field in any number of variables is a unique factorization domain, and the DVR-normalization of
a unique factorization domain is the ring itself.

### References

* [Kollár, *Lectures on resolution of singularities*, Lemma 1.24][kollar2007]
-/

namespace MMP.Resolution.Kollar

/-- **Kollár, Lemma 1.24, second sentence.** For a field `k`, the DVR-normalization of the
polynomial ring `k[x_i : i ∈ σ]` is the ring itself. -/
@[mmp "lem_kr1b_polynomial_ring_dvr_normal"]
public theorem dvrNormalization_mvPolynomial_eq_range (σ : Type*) (k : Type*) [Field k] :
    MMP.Resolution.dvrNormalization (MvPolynomial σ k) =
      Set.range (algebraMap (MvPolynomial σ k) (FractionRing (MvPolynomial σ k))) :=
  MMP.Resolution.Kollar.dvrNormalization_eq_range

end MMP.Resolution.Kollar

/-!
## A finite purely inseparable extension separabilizes a finite extension

Let `K` be a field of characteristic `p > 0`, `L` a perfect field containing `K` (for instance an
algebraic closure of `K`), and `F` an intermediate field of `L / K` that is finite over `K`.
Then there is an intermediate field `E` of `L / K`, finite over `K` and purely inseparable over
`K` (every `α ∈ E` has some `α ^ p ^ e` in `K`), such that every element of the compositum
`E ⊔ F` is separable over `E`.

### Implementation notes

The ambient field is only assumed perfect, rather than algebraically closed: the construction
adjoins to `K` finitely many `p ^ e`-th roots of elements of `K`, which exist in any perfect
field containing `K`. An algebraically closed field is perfect, so the case of an algebraic
closure is a special case. Pure inseparability is stated in the literal form
`∀ α ∈ E, ∃ e, α ^ p ^ e ∈ K`, which is equivalent to `IsPurelyInseparable K E` by
`isPurelyInseparable_iff_pow_mem`.

Where the source writes the separable part `F_s` as `K(F_s^q)` and adjoins `q`-th roots of the
coefficients of the `γ_j^q`, the field `E` here is generated by `p`-power roots of the coefficients
of the separable contractions of the minimal polynomials of a `K`-basis `γ_j` of `F`.

### References

* [Kollár, *Lectures on resolution of singularities*, proof of Theorem 1.33][kollar2007]
-/

section

open Polynomial IntermediateField

namespace MMP.Resolution.FoldAux.kr1b_purely_inseparable_separabilizes

/-- In a perfect field `L` of characteristic `p`, an element `γ` integral over `K` is a root of a
separable polynomial over `L`, and some `p`-power of each coefficient of that polynomial lies
in `K`. -/
private theorem exists_separable_eval_eq_zero_pow_coeff_mem {K L : Type*} [Field K] [Field L]
    [Algebra K L] (p : ℕ) [Fact p.Prime] [CharP K p] [CharP L p] [PerfectRing L p]
    (γ : L) (hγ : IsIntegral K γ) :
    ∃ h : L[X], h.Separable ∧ h.eval γ = 0 ∧
      ∀ i, ∃ e : ℕ, h.coeff i ^ p ^ e ∈ (algebraMap K L).range := by
  obtain ⟨n, g, hg, hgf⟩ := exists_separable_of_irreducible p (minpoly.irreducible hγ)
    (Fact.out : p.Prime).ne_zero
  let φ : K →+* L := ((iterateFrobeniusEquiv L p n).symm : L →+* L).comp (algebraMap K L)
  have hφ : ∀ c, φ c ^ p ^ n = algebraMap K L c := fun c => by
    rw [← iterateFrobenius_def, ← coe_iterateFrobeniusEquiv]
    simp [φ]
  refine ⟨g.map φ, hg.map, ?_, fun i => ⟨n, ?_⟩⟩
  · have : (g.map φ).eval γ ^ p ^ n = 0 := by
      have : (iterateFrobenius L p n).comp φ = algebraMap K L := by
        ext c
        simp [iterateFrobenius_def, hφ]
      rw [← iterateFrobenius_def, eval_map, Polynomial.hom_eval₂, this,
        iterateFrobenius_def, ← aeval_def, ← expand_aeval, hgf, minpoly.aeval]
    exact pow_eq_zero_iff (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) |>.mp this
  · rw [coeff_map, hφ]
    exact ⟨_, rfl⟩

/-- A root of a separable polynomial over `L` whose nonzero coefficients come from `E` is
separable over `E`. -/
private theorem mem_separableClosure_of_separable_of_coeff_mem {E L : Type*} [Field E] [Field L]
    [Algebra E L] {h : L[X]} (hsep : h.Separable) {x : L} (hx : h.eval x = 0)
    (hE : ∀ n, h.coeff n ≠ 0 → h.coeff n ∈ (algebraMap E L).range) :
    x ∈ separableClosure E L := by
  obtain ⟨g, rfl⟩ := (Polynomial.mem_lifts _).mp <| (Polynomial.lifts_iff_coeff_lifts h).mpr
    fun n => (eq_or_ne (h.coeff n) 0).elim (fun hn => ⟨0, by simp [hn]⟩) (hE n)
  rw [mem_separableClosure_iff]
  exact ((separable_map _).mp hsep).of_dvd <| minpoly.dvd _ _ <| by
    rwa [aeval_def, eval₂_eq_eval_map]

end MMP.Resolution.FoldAux.kr1b_purely_inseparable_separabilizes

namespace MMP.Resolution.Kollar

open MMP.Resolution.FoldAux.kr1b_purely_inseparable_separabilizes in
/-- **Kollár, proof of Theorem 1.33.** Let `K` be a field of characteristic `p > 0`, `L` a perfect
field containing `K` (e.g. an algebraic closure), and `F` an intermediate field finite over `K`.
Then there is an intermediate field `E`, finite over `K` with `α ^ p ^ e ∈ K` for every `α ∈ E`
and some `e`, such that every element of `E ⊔ F` is separable over `E`. -/
@[mmp "lem_kr1b_purely_inseparable_separabilizes"]
public theorem exists_finiteDimensional_pow_mem_isSeparable_sup
    {K L : Type*} [Field K] [Field L] [Algebra K L] [PerfectField L]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (F : IntermediateField K L) [FiniteDimensional K F] :
    ∃ E : IntermediateField K L, FiniteDimensional K E ∧
      (∀ α ∈ E, ∃ e : ℕ, α ^ p ^ e ∈ (algebraMap K L).range) ∧
      ∀ x ∈ E ⊔ F, IsSeparable E x := by
  haveI : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  let b := Module.finBasis K F
  choose h hsep hroot hcoeff using fun i => exists_separable_eval_eq_zero_pow_coeff_mem p (b i : L)
    ((IsIntegral.of_finite K (b i)).map F.val)
  let C : Set L := ⋃ i, ((h i).coeffs : Set L)
  have hCpow : ∀ c ∈ C, ∃ e : ℕ, c ^ p ^ e ∈ (algebraMap K L).range := by
    intro c hc
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hc
    obtain ⟨n, -, rfl⟩ := Polynomial.mem_coeffs_iff.mp hi
    exact hcoeff i n
  haveI : Finite C := (Set.finite_iUnion fun i => (h i).coeffs.finite_toSet).to_subtype
  let E := adjoin K C
  have hpi : IsPurelyInseparable K E :=
    (isPurelyInseparable_adjoin_iff_pow_mem K L p).mpr hCpow
  refine ⟨E, finiteDimensional_adjoin fun c hc => ?_, fun α hα => ?_, fun x hx => ?_⟩
  · obtain ⟨e, a, ha⟩ := hCpow c hc
    exact IsIntegral.of_pow (pow_pos (Fact.out : p.Prime).pos e)
      (ha ▸ isIntegral_algebraMap)
  · obtain ⟨e, a, ha⟩ := (isPurelyInseparable_iff_pow_mem K p).mp hpi ⟨α, hα⟩
    exact ⟨e, a, by simpa using congrArg (algebraMap E L) ha⟩
  · have hT : ∀ i, (b i : L) ∈ separableClosure E L := fun i =>
      mem_separableClosure_of_separable_of_coeff_mem (hsep i) (hroot i) fun n hn =>
        ⟨⟨_, subset_adjoin K C (Set.mem_iUnion.mpr ⟨i, coeff_mem_coeffs hn⟩)⟩, rfl⟩
    have hle : E ⊔ F ≤ (separableClosure E L).restrictScalars K := by
      refine sup_le (fun y hy => ?_) (fun y hy => ?_)
      · exact (separableClosure E L).algebraMap_mem ⟨y, hy⟩
      · rw [← show ((⟨y, hy⟩ : F) : L) = y from rfl, ← b.sum_repr ⟨y, hy⟩]
        simp only [IntermediateField.coe_sum, IntermediateField.coe_smul]
        exact sum_mem fun i _ => ((separableClosure E L).restrictScalars K).smul_mem
          ((IntermediateField.mem_restrictScalars _).mpr (hT i))
    exact (mem_separableClosure_iff).mp (hle hx)

end MMP.Resolution.Kollar

end

/-!
## The projection formula for intersection numbers with curves

Let `g : X' ⟶ X` be a morphism of `k`-schemes of finite type, `L` an invertible sheaf on `X` and
`C' ⊆ X'` an integral projective curve with generic point `η`. If `g(C')` is a point, then
`(g^*L · C') = 0`. Otherwise, if `X` is quasi-projective over `k`, the image `g(C')`, with its
reduced structure, is the integral projective curve `Γ = {g(η)}⁻`, the extension
`k(Γ) = κ(g(η)) ⊆ κ(η) = k(C')` is finite, and
`(g^*L · C') = [k(C') : k(Γ)] · (L · Γ)`.

### Implementation notes

A curve `C' ⊆ X'` is a `MMP.Mori.ProperCurve`, recorded by its generic point; its integral
scheme structure is the reduced induced one on the closure of that point, so the reduced image
`g(C')` is `MMP.Mori.curveSubschemeAt (g η)`, and its underlying set is pinned by
`closure {g η} = g '' closure {η}`. The field degree `[k(C') : k(g(C'))]` is
`MMP.Mori.residueFieldDegree g η`, the degree of the residue field extension at the generic
point. Quasi-projectivity over `k` is `Stacks.HProjective.IsQuasiProjective`, which contains
finite type. The image curve `Γ` is not an existentially quantified curve but the one determined
by `g η`: the conclusion provides a proof of `MMP.Mori.IsProperCurve sX (g η)` together with the
projectivity of `Γ`, so that the formula is about that curve.

### References

* [J. Kollár, *Lectures on resolution of singularities*][Kollar2007], 2.9, 2.13, 2.16
-/

section

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Resolution

namespace MMP.Resolution.FoldAux.kr2a_projection_formula

section

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

variable {k : Type u} [Field k] {X' X : Scheme.{u}} {sX' : X' ⟶ Spec (.of k)}

/-- A projective proper curve is a projective curve over `k`. -/
private theorem isCurve_scheme (C : ProperCurve sX') (hC : IsProjectiveMorphism (C.ι ≫ sX')) :
    MMP.Mori.IsCurve k (C.ι ≫ sX') ∧ MMP.Mori.IsProjectiveVariety k (C.ι ≫ sX') := by
  have hv : AlgebraicGeometry.IsVariety k (C.ι ≫ sX') :=
    { toIsIntegral := inferInstance
      toIsSeparated := C.isProper_ι_comp.toIsSeparated
      toLocallyOfFiniteType := C.isProper_ι_comp.toLocallyOfFiniteType
      toQuasiCompact := by haveI := C.isProper_ι_comp.toUniversallyClosed; exact inferInstance }
  exact ⟨{ toIsVariety := hv, topologicalKrullDim_eq_one := C.dim_eq },
    { toIsVariety := hv, isProjective := hC }⟩

/-- The intersection number with a projective curve is the Euler-characteristic degree of the
restriction. -/
private theorem lineBundleCurveIntersection_eq_degree (C : ProperCurve sX')
    (hC : IsProjectiveMorphism (C.ι ≫ sX')) (M : X'.Modules)
    [Stacks.Ample.IsInvertibleModule X' M] :
    lineBundleCurveIntersection M C = C.degree k M := by
  obtain ⟨h1, h2⟩ := isCurve_scheme C hC
  exact degree_eq_invertibleCurveDegree _ _ C.dim_le

/-- Part (1): a contracted curve has intersection number zero. -/
private theorem lineBundleCurveIntersection_pullback_eq_zero (g : X' ⟶ X) (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (C : ProperCurve sX')
    (hC : IsProjectiveMorphism (C.ι ≫ sX')) (hcon : C.IsContractedBy g) :
    lineBundleCurveIntersection ((Scheme.Modules.pullback g).obj L) C = 0 := by
  rw [lineBundleCurveIntersection_eq_degree C hC, ProperCurve.degree,
    degreeOn_eq_invertibleCurveDegree,
    invertibleCurveDegree_eq_of_iso k (C.ι ≫ sX') C.dim_le
      (L := (Scheme.Modules.pullback C.ι).obj ((Scheme.Modules.pullback g).obj L))
      (L' := (Scheme.Modules.pullback (C.ι ≫ g)).obj L)
      ((Scheme.Modules.pullbackComp C.ι g).app L)]
  exact invertibleCurveDegree_pullback_eq_zero_of_forall_eq k _ C.dim_le (C.ι ≫ g) L (g C.point)
    fun z => hcon _ (C.range_ι.subset ⟨z, rfl⟩)

/-- A quasi-projective scheme over a field is separated. -/
private theorem isSeparated_of_isQuasiProjective {sX : X ⟶ Spec (.of k)}
    (h : Stacks.HProjective.IsQuasiProjective sX) : IsSeparated sX := by
  obtain ⟨Y, i, q, hi, hq, hiq⟩ :=
    Stacks.QuasiProjectiveCompactification.exists_isImmersion_isProjective_of_qcqs sX h
  haveI := hi
  haveI : IsSeparated q := hq.isSeparated
  rw [← hiq]
  infer_instance

/-- Finiteness of a field extension is invariant under compatible ring isomorphisms of base and
extension. -/
private theorem finite_iff_of_ringEquiv {A₁ B₁ A₂ B₂ : Type u} [Field A₁] [Field B₁] [Field A₂]
    [Field B₂] (f₁ : A₁ →+* B₁) (f₂ : A₂ →+* B₂) (e₁ : A₁ ≃+* A₂) (e₂ : B₁ ≃+* B₂)
    (h : f₂.comp e₁ = (e₂ : B₁ →+* B₂).comp f₁) :
    letI := f₁.toAlgebra
    letI := f₂.toAlgebra
    Module.Finite A₁ B₁ ↔ Module.Finite A₂ B₂ := by
  letI := f₁.toAlgebra
  letI := f₂.toAlgebra
  have h' : f₁.comp (e₁.symm : A₂ →+* A₁) = (e₂.symm : B₂ →+* B₁).comp f₂ := by
    ext x
    simpa using (congrArg (fun φ => e₂.symm (φ (e₁.symm x))) h).symm
  exact ⟨fun _ => Module.Finite.of_equiv_equiv e₁ e₂ h,
    fun _ => Module.Finite.of_equiv_equiv e₁.symm e₂.symm h'⟩

/-- The residue field extension at the generic point of a curve not contracted by `g` is finite:
it is the function field extension along the map to the reduced image. -/
private theorem finite_residueField {sX : X ⟶ Spec (.of k)} [IsSeparated sX]
    [LocallyOfFiniteType sX] (g : X' ⟶ X) (C : ProperCurve sX')
    [MMP.Mori.IsCurve k ((C.ι ≫ g) ≫ sX)] [IsProper ((C.ι ≫ g) ≫ sX)] [IsProper (C.ι ≫ g)]
    [LocallyOfFiniteType (C.ι ≫ g)] (hnc : ¬ ∃ x : X, Set.range (C.ι ≫ g) = {x}) :
    letI := (g.residueFieldMap C.point).hom.toAlgebra
    Module.Finite (X.residueField (g C.point)) (X'.residueField C.point) := by
  set φ := C.ι ≫ g
  set c := genericPoint C.scheme
  set h := φ.toImage
  haveI := residueFieldMap_isIso_of_isClosedImmersion C.ι c
  haveI := residueFieldMap_isIso_of_isClosedImmersion φ.imageι (h c)
  -- the residue field extension of `g` at `ι c` is that of `φ` at `c`
  have hA := finite_iff_of_ringEquiv (g.residueFieldMap (C.ι c)).hom (φ.residueFieldMap c).hom
    (RingEquiv.refl _) (asIso (C.ι.residueFieldMap c)).commRingCatIsoToRingEquiv (by
      ext x
      simp [φ] <;> rfl)
  -- `φ` may be replaced by `h ≫ imageι`
  have hB : ∀ ψ : C.scheme ⟶ X, ψ = φ →
      (letI := (ψ.residueFieldMap c).hom.toAlgebra
       letI := (φ.residueFieldMap c).hom.toAlgebra
       Module.Finite (X.residueField (ψ c)) (C.scheme.residueField c) ↔
          Module.Finite (X.residueField (φ c)) (C.scheme.residueField c)) := by
    rintro _ rfl
    exact Iff.rfl
  -- `h ≫ imageι` at `c` versus `h` at `c`
  have hC := finite_iff_of_ringEquiv ((h ≫ φ.imageι).residueFieldMap c).hom
    (h.residueFieldMap c).hom
    (asIso (φ.imageι.residueFieldMap (h c))).commRingCatIsoToRingEquiv (RingEquiv.refl _) (by
      ext x
      simp <;> rfl)
  -- `h` at `c` versus the function field extension
  have hD := finite_iff_of_ringEquiv (functionFieldMap h) (h.residueFieldMap c).hom
    (genericResidueEquivOfDominant h) (genericResidueEquiv C.scheme)
    (residueFieldMap_comp_genericResidueEquivOfDominant h)
  have key : letI := (g.residueFieldMap (C.ι c)).hom.toAlgebra
      Module.Finite (X.residueField (g (C.ι c))) (X'.residueField (C.ι c)) :=
    hA.2 ((hB _ φ.toImage_imageι).1 (hC.2 (hD.1 (finite_functionField_image sX φ hnc))))
  rwa [C.ι_genericPoint] at key

/-- Part (2): the image of a non-contracted curve and the projection formula. -/
private theorem lineBundleCurveIntersection_pullback_of_not_isContractedBy
    {sX : X ⟶ Spec (.of k)} [IsSeparated sX] [LocallyOfFiniteType sX] (g : X' ⟶ X)
    (hg : g ≫ sX = sX') (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    (C : ProperCurve sX') (hC : IsProjectiveMorphism (C.ι ≫ sX')) (hnc : ¬ C.IsContractedBy g) :
    ∃ hΓ : IsProperCurve sX (g C.point),
      closure ({g C.point} : Set X) = g '' closure ({C.point} : Set X') ∧
      IsProjectiveMorphism (curveSubschemeAtι (g C.point) ≫ sX) ∧
      (letI := (g.residueFieldMap C.point).hom.toAlgebra;
        Module.Finite (X.residueField (g C.point)) (X'.residueField C.point)) ∧
      lineBundleCurveIntersection ((Scheme.Modules.pullback g).obj L) C =
        (residueFieldDegree g C.point : ℤ) *
          lineBundleCurveIntersection L (⟨g C.point, hΓ⟩ : ProperCurve sX) := by
  subst hg
  obtain ⟨h1, -⟩ := isCurve_scheme C hC
  haveI : MMP.Mori.IsCurve k ((C.ι ≫ g) ≫ sX) := by rwa [Category.assoc]
  haveI : IsProper ((C.ι ≫ g) ≫ sX) := by rw [Category.assoc]; exact C.isProper_ι_comp
  haveI : IsProper (C.ι ≫ g) := IsProper.of_comp _ sX
  have hcl : closure ({g C.point} : Set X) = g '' closure {C.point} := by
    rw [← C.range_ι_comp g, ← C.range_ι, ← Set.range_comp]
    rfl
  have hnc' : ¬ ∃ x : X, Set.range (C.ι ≫ g) = {x} := by
    rintro ⟨x, hx⟩
    rw [C.range_ι_comp g, hcl] at hx
    exact hnc fun y hy =>
      (hx.subset ⟨y, hy, rfl⟩).trans (hx.subset ⟨_, subset_closure rfl, rfl⟩).symm
  have hker : (C.ι ≫ g).ker = Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure {g C.point}) := by
    rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range]
    congr 1
    ext1
    exact C.closure_range_comp g
  obtain ⟨-, -, hcases⟩ := range_eq_singleton_or_isCurve_image sX (C.ι ≫ g)
  -- `curveSubschemeAt (g C.point)` is the scheme-theoretic image of `C.ι ≫ g`
  obtain ⟨hcurveΓ, hpropΓ⟩ : MMP.Mori.IsCurve k (curveSubschemeAtι (g C.point) ≫ sX) ∧
      IsProper (curveSubschemeAtι (g C.point) ≫ sX) := by
    have key : ∀ J, (C.ι ≫ g).ker = J →
        MMP.Mori.IsCurve k (J.subschemeι ≫ sX) ∧ IsProper (J.subschemeι ≫ sX) := by
      rintro J rfl
      exact hcases.resolve_left hnc'
    exact key _ hker
  have hΓ : IsProperCurve sX (g C.point) := ⟨hcurveΓ.topologicalKrullDim_eq_one, hpropΓ⟩
  haveI : IsIntegral (curveSubschemeAt (g C.point)) := hcurveΓ.toIsVariety.toIsIntegral
  have hprojΓ : IsProjectiveMorphism (curveSubschemeAtι (g C.point) ≫ sX) :=
    (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper (f := _)).mpr
      ⟨Stacks.HQuasiProjectiveDimensionOne.isHQuasiProjective_of_isIntegral _
        hcurveΓ.topologicalKrullDim_eq_one, inferInstance⟩
  haveI : LocallyOfFiniteType (C.ι ≫ g) := IsProper.toLocallyOfFiniteType
  refine ⟨hΓ, hcl, hprojΓ, finite_residueField (sX := sX) g C hnc', ?_⟩
  rw [lineBundleCurveIntersection_eq_degree C hC,
    lineBundleCurveIntersection_eq_degree (⟨g C.point, hΓ⟩ : ProperCurve sX) hprojΓ,
    C.degree_pullback g rfl L, dif_pos hΓ]

end

end MMP.Resolution.FoldAux.kr2a_projection_formula

namespace MMP.Resolution

open MMP.Resolution.FoldAux.kr2a_projection_formula in
/-- **The projection formula.** Let `g : X' ⟶ X` be a morphism of `k`-schemes of finite type,
`L` an invertible sheaf on `X` and `C' ⊆ X'` a projective curve. If `g(C')` is a point, then
`(g^*L · C') = 0`. If `g(C')` is not a point and `X` is quasi-projective over `k`, then `g(C')`
with its reduced structure is the projective curve `Γ = {g(η)}⁻` (`η` the generic point of `C'`),
`k(C')` is finite over `k(Γ)`, and `(g^*L · C') = [k(C') : k(Γ)] · (L · Γ)`. -/
@[mmp "lem_kr2a_projection_formula"]
public theorem lineBundleCurveIntersection_pullback {k : Type u} [Field k]
    {X' X : Scheme.{u}} {sX' : X' ⟶ Spec (.of k)} {sX : X ⟶ Spec (.of k)}
    [LocallyOfFiniteType sX'] [QuasiCompact sX'] [LocallyOfFiniteType sX] [QuasiCompact sX]
    (g : X' ⟶ X) (hg : g ≫ sX = sX') (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    (C' : ProperCurve sX') (hC' : IsProjectiveMorphism (C'.ι ≫ sX')) :
    (C'.IsContractedBy g →
      lineBundleCurveIntersection ((Scheme.Modules.pullback g).obj L) C' = 0) ∧
    (¬ C'.IsContractedBy g → Stacks.HProjective.IsQuasiProjective sX →
      ∃ hΓ : IsProperCurve sX (g C'.point),
        closure ({g C'.point} : Set X) = g '' closure ({C'.point} : Set X') ∧
        IsProjectiveMorphism (curveSubschemeAtι (g C'.point) ≫ sX) ∧
        (letI := (g.residueFieldMap C'.point).hom.toAlgebra;
          Module.Finite (X.residueField (g C'.point)) (X'.residueField C'.point)) ∧
        lineBundleCurveIntersection ((Scheme.Modules.pullback g).obj L) C' =
          (residueFieldDegree g C'.point : ℤ) *
            lineBundleCurveIntersection L (⟨g C'.point, hΓ⟩ : ProperCurve sX)) := by
  refine ⟨lineBundleCurveIntersection_pullback_eq_zero g L C' hC', fun hnc hqp => ?_⟩
  haveI := isSeparated_of_isQuasiProjective hqp
  exact lineBundleCurveIntersection_pullback_of_not_isContractedBy g hg L C' hC' hnc

end MMP.Resolution

end

/-!
## Closed subschemes with the same formal germ agree near the point

Let `X` be a locally Noetherian scheme, `x ∈ X`, and let `Z, W ⊆ X` be closed subschemes, given by
their ideal sheaves `I J : X.IdealSheafData`. If the ideals `I_Z` and `I_W` generate the same ideal
of the `𝔪_x`-adic completion `𝒪̂_{X,x}` of the local ring at `x`, then `Z` and `W` coincide on an
open neighbourhood of `x`: the two ideal sheaves have the same sections on every affine open
contained in that neighbourhood.

### Implementation notes

A closed subscheme is recorded by its ideal sheaf `X.IdealSheafData` (the closed subscheme itself
is `IdealSheafData.subscheme`). The ideal `I_Z 𝒪̂_{X,x}` is the extension of `I.ideal V` along
`Γ(X, V) → 𝒪_{X,x} → 𝒪̂_{X,x}` for an affine open `V ∋ x`; it does not depend on `V`, and the
hypothesis is asked for a single such `V`. Equality of `Z ∩ U` and `W ∩ U` as closed subschemes
of `U` is expressed as equality of `I.ideal V` and `J.ideal V` for all affine opens `V ⊆ U`.

### References

* [Kollár, *Lectures on resolution of singularities*][kollar2007]
-/

section

open CategoryTheory IsLocalRing AlgebraicGeometry

namespace MMP.Resolution.FoldAux.kr3c_formally_equal_subschemes_locally_equal

/-- If a finitely generated ideal `I` maps into `J S` in a localization `S = M⁻¹A`, then some
`m ∈ M` satisfies `m • I ≤ J`. -/
private lemma exists_mem_mul_mem_of_map_le {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]
    (M : Submonoid A) [IsLocalization M S] {I J : Ideal A} (hI : I.FG)
    (h : I.map (algebraMap A S) ≤ J.map (algebraMap A S)) :
    ∃ m ∈ M, ∀ a ∈ I, m * a ∈ J := by
  classical
  obtain ⟨T, rfl⟩ := hI
  have key : ∀ t ∈ T, ∃ m ∈ M, m * t ∈ J := fun t ht ↦
    (IsLocalization.algebraMap_mem_map_algebraMap_iff M (S := S) J t).mp
      (h (Ideal.mem_map_of_mem _ (Ideal.subset_span ht)))
  choose! m hmM hmJ using key
  refine ⟨∏ t ∈ T, m t, prod_mem fun t ht ↦ hmM t ht, fun a ha ↦ ?_⟩
  induction ha using Submodule.span_induction with
  | mem t ht =>
    rw [← Finset.mul_prod_erase T m ht, mul_comm (m t), mul_assoc]
    exact J.mul_mem_left _ (hmJ t ht)
  | zero => simp
  | add a b _ _ ha hb => rw [mul_add]; exact J.add_mem ha hb
  | smul c a _ ha => rw [smul_eq_mul, mul_left_comm]; exact J.mul_mem_left c ha

/-- If `s • I ≤ J`, `t • J ≤ I` and `s * t` becomes a unit in `S`, then `I S = J S`. -/
private lemma map_eq_map_of_mul_mem {A S : Type*} [CommRing A] [CommRing S] (φ : A →+* S)
    {I J : Ideal A} {s t : A} (hst : IsUnit (φ (s * t))) (hs : ∀ a ∈ I, s * a ∈ J)
    (ht : ∀ a ∈ J, t * a ∈ I) : I.map φ = J.map φ := by
  have key : ∀ {I J : Ideal A} {s : A}, IsUnit (φ s) → (∀ a ∈ I, s * a ∈ J) →
      I.map φ ≤ J.map φ := fun {I J s} hu h ↦ Ideal.map_le_iff_le_comap.mpr fun a ha ↦ by
    rw [Ideal.mem_comap, ← Ideal.unit_mul_mem_iff_mem _ hu, ← map_mul]
    exact Ideal.mem_map_of_mem _ (h a ha)
  rw [map_mul] at hst
  exact (key (isUnit_of_mul_isUnit_left hst) hs).antisymm (key (isUnit_of_mul_isUnit_right hst) ht)

/-- Ideals of a Noetherian local ring with the same extension to the `𝔪`-adic completion are
equal: the completion is faithfully flat. -/
private lemma eq_of_map_adicCompletion_eq {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {I J : Ideal R}
    (h : I.map (algebraMap R (AdicCompletion (maximalIdeal R) R)) =
      J.map (algebraMap R (AdicCompletion (maximalIdeal R) R))) : I = J := by
  have := AdicCompletion.flat_of_isNoetherian (maximalIdeal R) (R := R)
  have : Module.FaithfullyFlat R (AdicCompletion (maximalIdeal R) R) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := AdicCompletion (maximalIdeal R) R) I, h,
    Ideal.comap_map_eq_self_of_faithfullyFlat]

end MMP.Resolution.FoldAux.kr3c_formally_equal_subschemes_locally_equal

namespace MMP.Resolution

open MMP.Resolution.FoldAux.kr3c_formally_equal_subschemes_locally_equal in
/-- If two closed subschemes of a locally Noetherian scheme have ideals generating the same ideal
of the completed local ring `𝒪̂_{X,x}`, they agree on an open neighbourhood of `x`. -/
@[mmp "lem_kr3c_formally_equal_subschemes_locally_equal"]
public theorem exists_eq_of_map_adicCompletion_eq {X : Scheme} [IsLocallyNoetherian X]
    (I J : X.IdealSheafData) (x : X) (V : X.affineOpens) (hx : x ∈ (V : X.Opens))
    (h : (I.ideal V).map ((algebraMap (X.presheaf.stalk x)
        (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))).comp
          (X.presheaf.germ (V : X.Opens) x hx).hom) =
      (J.ideal V).map ((algebraMap (X.presheaf.stalk x)
        (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))).comp
          (X.presheaf.germ (V : X.Opens) x hx).hom)) :
    ∃ U : X.Opens, x ∈ U ∧ ∀ W : X.affineOpens, (W : X.Opens) ≤ U → I.ideal W = J.ideal W := by
  set φ := (X.presheaf.germ (V : X.Opens) x hx).hom
  rw [← Ideal.map_map, ← Ideal.map_map] at h
  have hstalk := eq_of_map_adicCompletion_eq h
  -- spread out to a basic open neighbourhood
  have : IsNoetherianRing Γ(X, (V : X.Opens)) := IsLocallyNoetherian.component_noetherian V
  letI : Algebra Γ(X, (V : X.Opens)) (X.presheaf.stalk x) := φ.toAlgebra
  have := V.2.isLocalization_stalk ⟨x, hx⟩
  set p := (V.2.primeIdealOf ⟨x, hx⟩).asIdeal
  obtain ⟨s, hsM, hs⟩ := exists_mem_mul_mem_of_map_le (S := X.presheaf.stalk x) p.primeCompl
    (IsNoetherian.noetherian (I.ideal V)) hstalk.le
  obtain ⟨t, htM, ht⟩ := exists_mem_mul_mem_of_map_le (S := X.presheaf.stalk x) p.primeCompl
    (IsNoetherian.noetherian (J.ideal V)) hstalk.ge
  refine ⟨X.basicOpen (s * t), (Scheme.mem_basicOpen _ _ _ hx).mpr
    (IsLocalization.map_units _ (⟨s * t, p.primeCompl.mul_mem hsM htM⟩ : p.primeCompl)),
    fun W hW ↦ ?_⟩
  have hWD : W ≤ X.affineBasicOpen (s * t) := hW
  have hDV : X.affineBasicOpen (s * t) ≤ V := X.affineBasicOpen_le (s * t)
  letI := V.2.isLocalization_basicOpen (s * t)
  rw [← I.map_ideal hWD, ← J.map_ideal hWD, ← I.map_ideal hDV, ← J.map_ideal hDV]
  exact congrArg _ (map_eq_map_of_mul_mem _
    (IsLocalization.Away.algebraMap_isUnit (S := Γ(X, X.basicOpen (s * t))) (s * t)) hs ht)

end MMP.Resolution

end

/-!
## The order of a polynomial at a point is at most its degree

Let `K` be a field and `P ∈ K[T_1, …, T_N]` a nonzero polynomial of total degree `≤ d`. At every
point `q` of `𝔸^N_K = Spec K[T_1, …, T_N]`, the order of `P` at `q` — the largest `r` with `P`
in the `r`-th power of the maximal ideal of the local ring `K[T]_q` — is at most `d`.

### Implementation notes

A point `q` of `𝔸^N_K` is a prime of `K[T_1, …, T_N]`, the order of `P` at `q` is
`MMP.Resolution.mult` of its image in `Localization.AtPrime q.asIdeal`, and the degree is
`MvPolynomial.totalDegree`.

The order at `q` is at most the order at an `L`-rational point `c` over an extension field
`L ⊇ K` (`MMP.Resolution.Kollar.exists_mult_le_mult_localization_ker_eval`), and at a rational
point the bound is `MMP.Resolution.Kollar.mult_localization_ker_eval_le_of_totalDegree_le`.

### References

* [J. Kollár, *Lectures on resolution of singularities*, 3.61]
-/

section

open MvPolynomial

namespace MMP.Resolution.Kollar

/-- **Kollár 3.61** (order bounded by degree). Let `K` be a field, `q` a point of
`𝔸^N_K = Spec K[T_1, …, T_N]` and `P ∈ K[T_1, …, T_N]` a nonzero polynomial of total degree at
most `d`. Then the order of `P` at `q` is at most `d`. -/
@[mmp "lem_kr3c_polynomial_order_le_degree"]
public theorem mult_localization_le_of_totalDegree_le {K : Type*} [Field K] {N : ℕ}
    (q : PrimeSpectrum (MvPolynomial (Fin N) K)) {P : MvPolynomial (Fin N) K} (hP : P ≠ 0)
    {d : ℕ} (hd : P.totalDegree ≤ d) :
    mult (algebraMap _ (Localization.AtPrime q.asIdeal) P) ≤ d := by
  obtain ⟨L, _, _, c, h⟩ := exists_mult_le_mult_localization_ker_eval q P
  refine h.trans (mult_localization_ker_eval_le_of_totalDegree_le c ?_ ?_)
  · simpa using (map_injective _ (algebraMap K L).injective).ne hP
  · exact (Finset.sup_mono (support_map_subset (algebraMap K L) P)).trans hd

end MMP.Resolution.Kollar

end

/-!
## Simple normal crossings of a centre may be checked inside a hypersurface

Let `X` be a scheme over a field `k`, `E = (E^1, …, E^s)` an ordered divisor on `X` and `H ⊆ X`
a closed subscheme such that `H + ∑ᵢ E^i` is a simple normal crossing divisor. A closed subscheme
`Z ⊆ H` has simple normal crossings with `E` in `X` if and only if it has simple normal crossings
in `H` with the restriction `E|_H = (E^i ∩ H)ᵢ`.

### Implementation notes

A closed subscheme `Z ⊆ H` is an ideal sheaf `Z` on `X` with `H ≤ Z`; as a closed subscheme of
`H` it is its inverse image along `H → X`, and `E|_H` is `OrderedDivisor.comap` of `E` along that
inclusion. As in `MMP.Resolution.Kollar.hasSNCWith_cons_of_hasSNCWith`, `X` is only assumed
locally Noetherian, and `H` is only assumed to make `H + ∑ᵢ E^i` simple normal crossing; this
already makes `E` simple normal crossing and prevents any `E^i` from containing a component
of `H`.

### References

* [J. Kollár, *Lectures on resolution of singularities*, §3]
-/

section

open CategoryTheory AlgebraicGeometry MMP MMP.Resolution MMP.Resolution.Kollar

variable {X : Scheme.{u}}

namespace MMP.Resolution.FoldAux.kr3d_snc_center_inside_hypersurface

/-- If `φ` kills `z j₀`, the `φ`-image of the ideal spanned by the `z j`, `j ∈ S`, is spanned by
the images of the other coordinates `z (j₀.succAbove k)` with `j₀.succAbove k ∈ S`. -/
private theorem map_span_image_eq_span_image_succAbove {A B : Type*} [CommRing A] [CommRing B]
    (φ : A →+* B) {m : ℕ} {z : Fin (m + 1) → A} {j₀ : Fin (m + 1)} (h0 : φ (z j₀) = 0)
    (S : Set (Fin (m + 1))) :
    Ideal.map φ (Ideal.span (z '' S)) =
      Ideal.span ((fun k => φ (z (j₀.succAbove k))) '' (j₀.succAbove ⁻¹' S)) := by
  rw [Ideal.map_span, Set.image_image]
  refine le_antisymm (Ideal.span_le.2 ?_) (Ideal.span_mono ?_)
  · rintro _ ⟨j, hj, rfl⟩
    by_cases hjj : j = j₀
    · simp [hjj, h0]
    · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hjj
      exact Ideal.subset_span ⟨k, hj, rfl⟩
  · rintro _ ⟨k, hk, rfl⟩
    exact ⟨_, hk, rfl⟩

/-- If `B = A/(z_{j₀})` for a regular system of parameters `z` of a Noetherian local ring `A`,
the images of the other `z_k` are a regular system of parameters of `B`. -/
private theorem isRegularSystemOfParameters_comp_succAbove
    {A B : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [CommRing B] [IsLocalRing B]
    (φ : A →+* B) (hφ : Function.Surjective φ) {m : ℕ} {z : Fin (m + 1) → A}
    (hz : MMP.Mori.IsRegularSystemOfParameters z) (j₀ : Fin (m + 1))
    (hker : RingHom.ker φ = Ideal.span {z j₀}) :
    MMP.Mori.IsRegularSystemOfParameters (fun k => φ (z (j₀.succAbove k))) := by
  haveI : IsNoetherianRing B := isNoetherianRing_of_surjective A B φ hφ
  have h0 : φ (z j₀) = 0 := by
    rw [← RingHom.mem_ker, hker]; exact Ideal.mem_span_singleton_self _
  have hmax : Ideal.span (Set.range fun k => φ (z (j₀.succAbove k))) =
      IsLocalRing.maximalIdeal B := by
    rw [← IsLocalRing.map_maximalIdeal_of_surjective φ hφ, ← hz.1, ← Set.image_univ (f := z),
      map_span_image_eq_span_image_succAbove φ h0, Set.preimage_univ, Set.image_univ]
  have hd : ringKrullDim B ≤ m := by
    refine (ringKrullDim_le_spanFinrank_maximalIdeal (R := B)).trans ?_
    rw [← hmax]
    have : (Set.range fun k => φ (z (j₀.succAbove k))).ncard ≤ m := by
      rw [← Set.image_univ]
      exact (Set.ncard_image_le Set.finite_univ).trans (by simp)
    exact_mod_cast (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range _)).trans this
  refine ⟨hmax, le_antisymm hd ?_⟩
  -- `m + 1 = dim A ≤ dim A/(z_{j₀}) + 1 = dim B + 1`.
  have hjac : RingHom.ker φ ≤ Ring.jacobson A := by
    rw [hker, Ideal.span_singleton_le_iff_mem, IsLocalRing.ringJacobson_eq_maximalIdeal, ← hz.1]
    exact Ideal.subset_span ⟨j₀, rfl⟩
  have h1 := ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank (RingHom.ker φ) hjac
  rw [ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hφ), hz.2] at h1
  have h2 : ((RingHom.ker φ).spanFinrank : WithBot ℕ∞) ≤ 1 := by
    rw [hker]
    exact_mod_cast (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_singleton _)).trans
      (by simp)
  have h4 : ((m + 1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim B + 1 := h1.trans (by gcongr)
  generalize ringKrullDim B = d at h4 ⊢
  induction d using WithBot.recBotCoe with
  | bot => simp at h4
  | coe d =>
    norm_cast at h4 ⊢
    exact (ENat.add_le_add_iff_right ENat.one_ne_top).1 (by simpa using h4)

/-- Snc with a family `E` passes to any subfamily `E ∘ f`, `f` injective. -/
private theorem hasSNCWith_comp {Λ Λ' : Type*} {E : Λ → X.IdealSheafData} {Z : X.IdealSheafData}
    (hZ : HasSNCWith E Z) {f : Λ' → Λ} (hf : Function.Injective f) : HasSNCWith (E ∘ f) Z := by
  intro x hx
  obtain ⟨n, z, c, J, hz, hE, hc, hZx⟩ := hZ x hx
  refine ⟨n, z, fun i => c ⟨f i.1, i.2⟩, J, hz, fun i => hE ⟨f i.1, i.2⟩, fun i j h => ?_, hZx⟩
  exact Subtype.ext (hf (congrArg Subtype.val (hc h)))

/-- **Restricting snc to `H`.** If `Z ⊇ H` has simple normal crossings with `H + ∑ᵢ E^i`, then
`Z|_H` has simple normal crossings in `H` with `E|_H`: at `x ∈ Z`, if `z_{j₀}` is the coordinate
cutting out `H`, the images in `𝒪_{H,x} = 𝒪_{X,x}/(z_{j₀})` of the other coordinates are adapted
to `E|_H` and `Z|_H`. -/
private theorem hasSNCWith_comap_of_hasSNCWith_cons [IsLocallyNoetherian X]
    {E : OrderedDivisor X} {H Z : X.IdealSheafData} (hZH : H ≤ Z)
    (hZ : HasSNCWith (Fin.cons (α := fun _ => X.IdealSheafData) H E.E) Z) :
    HasSNCWith (E.comap H.subschemeι).E (Z.comap H.subschemeι) := by
  classical
  intro y hy
  have hsupp : ∀ I : X.IdealSheafData, y ∈ (I.comap H.subschemeι).support ↔
      H.subschemeι y ∈ I.support := fun I => by
    rw [Scheme.IdealSheafData.support_comap]; rfl
  have hx : H.subschemeι y ∈ Z.support := (hsupp Z).1 hy
  obtain ⟨n, z, c, J, hz, hzE, hzinj, hZst⟩ := hZ _ hx
  have hx0 : H.subschemeι y ∈ (Fin.cons (α := fun _ => X.IdealSheafData) H E.E 0).support := by
    simpa using Scheme.IdealSheafData.support_antitone hZH hx
  set j₀ := c ⟨0, hx0⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := j₀.pos; omega⟩
  set φ := (H.subschemeι.stalkMap y).hom
  have hkerφ : RingHom.ker φ = Ideal.span {z j₀} := by
    rw [Stacks.Divisors.kernel_stalkMap_subscheme_eq_idealStalk H y]
    simpa using hzE ⟨0, hx0⟩
  have hxs : ∀ i : {i : Fin E.s // y ∈ ((E.comap H.subschemeι).E i).support},
      H.subschemeι y ∈ (Fin.cons (α := fun _ => X.IdealSheafData) H E.E i.1.succ).support :=
    fun i => by simpa using (hsupp (E.E i.1)).1 i.2
  have hne : ∀ i, c ⟨i.1.succ, hxs i⟩ ≠ j₀ := fun i h =>
    Fin.succ_ne_zero _ (congrArg Subtype.val (hzinj h))
  choose cB hcB using fun i => Fin.exists_succAbove_eq (hne i)
  refine ⟨m, fun k => φ (z (j₀.succAbove k)), cB, Finset.univ.filter (j₀.succAbove · ∈ J),
    isRegularSystemOfParameters_comp_succAbove φ (H.subschemeι.stalkMap_surjective y) hz j₀ hkerφ,
    fun i => ?_, fun i i' h => ?_, ?_⟩
  · change IdealSheafData.stalk ((E.E i.1).comap H.subschemeι) y =
      Ideal.span {φ (z (j₀.succAbove (cB i)))}
    have h := hzE ⟨i.1.succ, hxs i⟩
    simp only [Fin.cons_succ] at h
    rw [congrArg (fun j => φ (z j)) (hcB i), IdealSheafData.stalk_comap]
    exact (congrArg (Ideal.map φ) h).trans (by rw [Ideal.map_span, Set.image_singleton]; rfl)
  · have h := hzinj ((hcB i).symm.trans ((congrArg j₀.succAbove h).trans (hcB i')))
    exact Subtype.ext (Fin.succ_injective _ (congrArg Subtype.val h))
  · change IdealSheafData.stalk (Z.comap H.subschemeι) y = _
    rw [IdealSheafData.stalk_comap, hZst,
      map_span_image_eq_span_image_succAbove φ (j₀ := j₀)
        (by rw [← RingHom.mem_ker, hkerφ]; exact Ideal.mem_span_singleton_self _)]
    congr 2
    ext; simp

end MMP.Resolution.FoldAux.kr3d_snc_center_inside_hypersurface

namespace MMP.Resolution.Kollar

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsLocallyNoetherian X]

open MMP.Resolution.FoldAux.kr3d_snc_center_inside_hypersurface in
/-- **Simple normal crossings inside a hypersurface** (Kollár §3). Let `E = (E^1, …, E^s)` be an
ordered divisor on `X` over `k` and `H ⊆ X` a closed subscheme such that `H + ∑ᵢ E^i` is a simple
normal crossing divisor. A closed subscheme `Z ⊆ H` has simple normal crossings with `E` if and
only if `Z`, as a closed subscheme of `H`, has simple normal crossings with `E|_H`. -/
@[mmp "lem_kr3d_snc_center_inside_hypersurface"]
public theorem hasSNCWith_iff_hasSNCWith_comap (sX : X ⟶ Spec (.of k)) (E : OrderedDivisor X)
    (H : X.IdealSheafData)
    (hHE : IsSNCFamily sX (Fin.cons (α := fun _ => X.IdealSheafData) H E.E))
    (Z : X.IdealSheafData) (hZH : H ≤ Z) :
    HasSNCWith E.E Z ↔
      HasSNCWith (E.comap H.subschemeι).E (Z.comap H.subschemeι) :=
  ⟨fun hZ => hasSNCWith_comap_of_hasSNCWith_cons hZH
      (hasSNCWith_cons_of_hasSNCWith sX E H hHE Z hZH hZ),
    fun hZ => hasSNCWith_comp (hasSNCWith_cons_of_hasSNCWith_comap sX H E hHE Z hZH hZ)
      (Fin.succ_injective _)⟩

end MMP.Resolution.Kollar

end

/-!
## Empty entries of an ordered divisor are inert along a blow-up sequence

Let `X` be a smooth variety over a field `k` and `E`, `E'` divisors with ordered index set on `X`
whose entries are reduced divisors, with `E^♭ = E'^♭` (the same nonempty entries in the same
order). Along a blow-up sequence `(X_i, Z_i)_{i ≤ r}` starting with `X` whose spaces and centres
are smooth and whose centres have irreducible components of codimension `≥ 1`, the iterated
total transforms `E_i`, `E'_i` (`E_{i+1} = (π_i)⁻¹_tot E_i`) satisfy, for every `i ≤ r`:
`E_i^♭ = E_i'^♭`; `E_i` is an ordered snc divisor iff `E'_i` is; and any closed subscheme of
`X_i` (in particular the centre `Z_i`, `i < r`) has simple normal crossings with `∑_j E_i^j`
iff it has simple normal crossings with `∑_j E_i'^j`.

### Implementation notes

The stage `i` of the sequence is the truncation `B.truncate i`, so that `X_i` is
`(B.truncate i).target` and `E_i` is `(B.truncate i).orderedTotalTransform E`. The comparison of
snc-with conditions is stated for every closed subscheme `Z` of `X_i`, which contains the case
of the centre `Z_i`. The smoothness of `X` and of the sequence, the condition on the
codimension of the centres, and the reducedness of the entries are not needed: the statement
holds for every blow-up sequence and every index `i`.

### References

* [J. Kollár, *Lectures on resolution of singularities*, 3.72]
-/

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Resolution

namespace MMP.Resolution.FoldAux.kr3e_empty_entries_transport

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

section Flat

variable {X : Scheme.{u}}

open Classical in
/-- The list of the nonempty entries of an ordered divisor, in their order. -/
private noncomputable def flat (E : OrderedDivisor X) : List X.IdealSheafData :=
  (List.ofFn E.E).filter fun D => D ≠ ⊤

open Classical in
/-- The indices of the nonempty entries. -/
private noncomputable def flatIdx (E : OrderedDivisor X) : List (Fin E.s) :=
  (List.finRange E.s).filter fun i => E.E i ≠ ⊤

private theorem injective_flatIdx_get (E : OrderedDivisor X) :
    Function.Injective (flatIdx E).get :=
  List.nodup_iff_injective_get.1 ((List.nodup_finRange _).filter _)

private theorem exists_flatIdx_get (E : OrderedDivisor X) (i : Fin E.s) (hi : E.E i ≠ ⊤) :
    ∃ j, (flatIdx E).get j = i :=
  List.mem_iff_get.1 (by simp [flatIdx, hi])

private theorem ofFn_deleteEmpty (E : OrderedDivisor X) :
    List.ofFn E.deleteEmpty.E = flat E := by
  show List.ofFn (E.E ∘ (flatIdx E).get) = flat E
  rw [← List.map_ofFn, List.ofFn_get, flatIdx, flat, List.ofFn_eq_map (f := E.E),
    List.filter_map]
  rfl

private theorem eq_of_ofFn_eq {E F : OrderedDivisor X} (h : List.ofFn E.E = List.ofFn F.E) :
    E = F := by
  obtain ⟨s, e⟩ := E
  obtain ⟨t, f⟩ := F
  rw [List.ofFn_inj'] at h
  cases h
  rfl

private theorem deleteEmpty_eq_iff {E F : OrderedDivisor X} :
    E.deleteEmpty = F.deleteEmpty ↔ flat E = flat F := by
  refine ⟨fun h => ?_, fun h => eq_of_ofFn_eq ?_⟩
  · rw [← ofFn_deleteEmpty, ← ofFn_deleteEmpty, h]
  · rw [ofFn_deleteEmpty, ofFn_deleteEmpty, h]

private theorem mem_support_iff (E : OrderedDivisor X) (x : X) :
    x ∈ E.support ↔ ∃ D ∈ flat E, x ∈ D.support := by
  simp only [OrderedDivisor.support, Set.mem_iUnion, flat, List.mem_filter, List.mem_ofFn,
    decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨E.E i, ⟨⟨i, rfl⟩, fun h => by simp [h] at hi⟩, hi⟩
  · rintro ⟨D, ⟨⟨i, rfl⟩, -⟩, hi⟩
    exact ⟨i, hi⟩

private theorem support_eq_of_flat_eq {E F : OrderedDivisor X} (h : flat E = flat F) :
    E.support = F.support := by
  ext x
  rw [mem_support_iff, mem_support_iff, h]

/-- If `T` maps values failing `p` to values failing `p`, then the filtered image of a list
under `T` depends only on the filtered list. -/
private theorem filter_map_eq_of_filter_eq {α β : Type*} (p : α → Bool) (q : β → Bool)
    (T : α → β) (hT : ∀ a, p a = false → q (T a) = false) {l l' : List α}
    (h : l.filter p = l'.filter p) : (l.map T).filter q = (l'.map T).filter q := by
  have key : ∀ l : List α, (l.map T).filter q = ((l.filter p).map T).filter q := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih =>
      by_cases ha : p a = true
      · simp [List.filter_cons, ha, ih]
      · have ha' : p a = false := by simpa using ha
        simp [List.filter_cons, ha', hT a ha', ih]
  rw [key l, key l', h]

/-- The birational transform `π⁻¹_*D` of an entry, as in `OrderedDivisor.totalTransform`. -/
private noncomputable def entryTransform (Z : X.IdealSheafData) (D : X.IdealSheafData) :
    (blowUp Z).IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
    (blowUpToBase Z ⁻¹' ((D.support : Set X) \ componentsOfCodimAtLeastTwo (Z.support : Set X))))

private theorem entryTransform_top (Z : X.IdealSheafData) : entryTransform Z ⊤ = ⊤ := by
  have : (Closeds.closure (blowUpToBase Z ⁻¹' (((⊤ : X.IdealSheafData).support : Set X) \
      componentsOfCodimAtLeastTwo (Z.support : Set X)))) = ⊥ := by
    ext x
    simp [Scheme.IdealSheafData.support_top]
  rw [entryTransform, this, Scheme.IdealSheafData.vanishingIdeal_bot]

/-- The last entry of `π⁻¹_tot(E)`; it depends only on the support of `E`. -/
private noncomputable def lastEntry (Z : X.IdealSheafData) (S : Set X) :
    (blowUp Z).IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
    (⋃ (W : Set X) (_ : W ∈ componentsOf (Z.support : Set X)) (_ : W ∉ componentsOf S),
      blowUpToBase Z ⁻¹' W))

open Classical in
private theorem flat_totalTransform (E : OrderedDivisor X) (Z : X.IdealSheafData) :
    flat (E.totalTransform Z) =
      ((List.ofFn E.E).map (entryTransform Z)).filter (fun D => D ≠ ⊤) ++
        [lastEntry Z E.support].filter (fun D => D ≠ ⊤) := by
  have h : List.ofFn (E.totalTransform Z).E = List.ofFn (n := E.s + 1)
      (Fin.snoc (α := fun _ => (blowUp Z).IdealSheafData) (fun i => entryTransform Z (E.E i))
        (lastEntry Z E.support)) := rfl
  rw [flat, h, List.ofFn_succ', List.concat_eq_append, List.filter_append, List.map_ofFn]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  rfl

open Classical in
private theorem flat_totalTransform_eq {E F : OrderedDivisor X} (h : flat E = flat F)
    (Z : X.IdealSheafData) : flat (E.totalTransform Z) = flat (F.totalTransform Z) := by
  rw [flat_totalTransform, flat_totalTransform, support_eq_of_flat_eq h]
  congr 1
  refine filter_map_eq_of_filter_eq _ _ _ (fun D hD => ?_) h
  simp only [ne_eq, decide_eq_false_iff_not, not_not] at hD ⊢
  rw [hD, entryTransform_top]

private theorem flat_orderedTotalTransform_truncate_eq :
    ∀ {X : Scheme.{u}} (B : ClosedBlowupSequence X)
    (i : ℕ) {E F : OrderedDivisor X}, flat E = flat F →
      flat ((B.truncate i).orderedTotalTransform E) = flat ((B.truncate i).orderedTotalTransform F)
  | _, .nil _, _, _, _, h => h
  | _, .cons _ _, 0, _, _, h => h
  | _, .cons Z B, i + 1, _, _, h =>
    flat_orderedTotalTransform_truncate_eq B i (flat_totalTransform_eq h Z)

end Flat

section Reindex

variable {X : Scheme.{u}} {Λ Λ' : Type*} (E : Λ → X.IdealSheafData) (g : Λ' → Λ)

/-- A property of all entries may be checked on the nonempty ones. -/
private theorem forall_iff_forall_comp (hg : ∀ i, E i ≠ ⊤ → ∃ j, g j = i)
    (R : X.IdealSheafData → Prop) (hR : R ⊤) :
    (∀ i, R (E i)) ↔ ∀ j, R (E (g j)) := by
  refine ⟨fun h j => h _, fun h i => ?_⟩
  by_cases hi : E i = ⊤
  · rwa [hi]
  · obtain ⟨j, rfl⟩ := hg i hi
    exact h j

/-- The coordinate assignment of an snc family at a point may be taken over the nonempty
entries. -/
private theorem exists_coord_iff (hginj : Function.Injective g)
    (hg : ∀ i, E i ≠ ⊤ → ∃ j, g j = i) (x : X) {n : ℕ} (z : Fin n → X.presheaf.stalk x) :
    (∃ c : {i // x ∈ (E i).support} → Fin n,
        (∀ i, IdealSheafData.stalk (E i.1) x = Ideal.span {z (c i)}) ∧ Function.Injective c) ↔
      ∃ c : {j // x ∈ (E (g j)).support} → Fin n,
        (∀ j, IdealSheafData.stalk (E (g j.1)) x = Ideal.span {z (c j)}) ∧
          Function.Injective c := by
  let φ : {j // x ∈ (E (g j)).support} → {i // x ∈ (E i).support} := fun j => ⟨g j.1, j.2⟩
  have hφ : Function.Bijective φ := by
    refine ⟨fun a b hab => Subtype.ext (hginj (congrArg Subtype.val hab)), fun i => ?_⟩
    obtain ⟨j, hj⟩ := hg i.1 fun h => by
      have := i.2
      rwa [h, Scheme.IdealSheafData.support_top] at this
    exact ⟨⟨j, hj ▸ i.2⟩, Subtype.ext hj⟩
  let e := Equiv.ofBijective φ hφ
  constructor
  · rintro ⟨c, hc, hinj⟩
    exact ⟨c ∘ φ, fun j => hc (φ j), hinj.comp hφ.1⟩
  · rintro ⟨c, hc, hinj⟩
    refine ⟨c ∘ e.symm, fun i => ?_, hinj.comp e.symm.injective⟩
    have h := hc (e.symm i)
    have hi : g (e.symm i).1 = i.1 := congrArg Subtype.val (e.apply_symm_apply i)
    rwa [hi] at h

private theorem hasSNCWith_iff_comp (hginj : Function.Injective g)
    (hg : ∀ i, E i ≠ ⊤ → ∃ j, g j = i) (Z : X.IdealSheafData) :
    HasSNCWith E Z ↔ HasSNCWith (E ∘ g) Z := by
  refine forall₂_congr fun x _ => exists_congr fun n => exists_congr fun z => ?_
  have key := exists_coord_iff E g hginj hg x z
  constructor
  · rintro ⟨c, J, h1, h2, h3, h4⟩
    obtain ⟨c', h2', h3'⟩ := key.1 ⟨c, h2, h3⟩
    exact ⟨c', J, h1, h2', h3', h4⟩
  · rintro ⟨c, J, h1, h2, h3, h4⟩
    obtain ⟨c', h2', h3'⟩ := key.2 ⟨c, h2, h3⟩
    exact ⟨c', J, h1, h2', h3', h4⟩

private theorem isSNCFamily_iff_comp {k : Type u} [Field k] (sX : X ⟶ Spec (.of k))
    (hginj : Function.Injective g) (hg : ∀ i, E i ≠ ⊤ → ∃ j, g j = i) :
    IsSNCFamily sX E ↔ IsSNCFamily sX (E ∘ g) := by
  refine and_congr (forall_iff_forall_comp E g hg (fun D => IsReduced D.subscheme ∧
      MMP.Mori.IsPureCodimOne D.support ∧ MMP.Mori.IsSmoothScheme (D.subschemeι ≫ sX))
      ⟨?_, ?_, ?_⟩)
    (forall_congr' fun x => exists_congr fun n => exists_congr fun z => ?_)
  · exact isReduced_of_isAffine_isReduced _
  · intro W hW
    have h := hW.prop
    rw [Scheme.IdealSheafData.support_top] at h
    obtain ⟨w, hw⟩ := W.isIrreducible.nonempty
    exact (h hw).elim
  · unfold MMP.Mori.IsSmoothScheme
    ext x
    exact isEmptyElim x
  · have key := exists_coord_iff E g hginj hg x z
    constructor
    · rintro ⟨c, h1, h2, h3⟩
      obtain ⟨c', h2', h3'⟩ := key.1 ⟨c, h2, h3⟩
      exact ⟨c', h1, h2', h3'⟩
    · rintro ⟨c, h1, h2, h3⟩
      obtain ⟨c', h2', h3'⟩ := key.2 ⟨c, h2, h3⟩
      exact ⟨c', h1, h2', h3'⟩

end Reindex

section DeleteEmpty

variable {X : Scheme.{u}} (E : OrderedDivisor X)

private theorem hasSNCWith_deleteEmpty_iff (Z : X.IdealSheafData) :
    HasSNCWith E.E Z ↔ HasSNCWith E.deleteEmpty.E Z :=
  hasSNCWith_iff_comp E.E _ (injective_flatIdx_get E) (exists_flatIdx_get E) Z

private theorem isOrderedSNC_deleteEmpty_iff {k : Type u} [Field k] (sX : X ⟶ Spec (.of k)) :
    E.IsOrderedSNC sX ↔ E.deleteEmpty.IsOrderedSNC sX :=
  and_congr
    (forall_iff_forall_comp E.E _ (exists_flatIdx_get E)
      (fun D => IsReduced D.subscheme ∧ Stacks.Divisors.IsEffectiveCartierDivisor D)
      ⟨isReduced_of_isAffine_isReduced _, Stacks.Divisors.isEffectiveCartierDivisor_top⟩)
    (isSNCFamily_iff_comp E.E _ sX (injective_flatIdx_get E) (exists_flatIdx_get E))

end DeleteEmpty

end MMP.Resolution.FoldAux.kr3e_empty_entries_transport

namespace MMP.Resolution

namespace ClosedBlowupSequence

open MMP.Resolution.FoldAux.kr3e_empty_entries_transport in
/-- **Empty entries are inert along a blow-up sequence.** Let `X` be a scheme over `k`,
`E`, `E'` divisors with ordered index set on `X` with `E^♭ = E'^♭`, and `B` a blow-up sequence
starting with `X`. Then for every `i` the total transforms `E_i`, `E'_i` on
`X_i` satisfy `E_i^♭ = E_i'^♭`, `E_i` is an ordered snc divisor iff `E'_i` is, and a closed
subscheme `Z ⊆ X_i` has simple normal crossings with `∑_j E_i^j` iff it has simple normal
crossings with `∑_j E_i'^j`. -/
@[mmp "lem_kr3e_empty_entries_transport"]
public theorem deleteEmpty_orderedTotalTransform_eq {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) {E E' : OrderedDivisor X}
    (hEE' : E.deleteEmpty = E'.deleteEmpty) (B : ClosedBlowupSequence X) (i : ℕ) :
    ((B.truncate i).orderedTotalTransform E).deleteEmpty =
        ((B.truncate i).orderedTotalTransform E').deleteEmpty ∧
      (((B.truncate i).orderedTotalTransform E).IsOrderedSNC ((B.truncate i).toBase ≫ sX) ↔
        ((B.truncate i).orderedTotalTransform E').IsOrderedSNC ((B.truncate i).toBase ≫ sX)) ∧
      ∀ Z : (B.truncate i).target.IdealSheafData,
        HasSNCWith ((B.truncate i).orderedTotalTransform E).E Z ↔
          HasSNCWith ((B.truncate i).orderedTotalTransform E').E Z := by
  have h : ((B.truncate i).orderedTotalTransform E).deleteEmpty =
      ((B.truncate i).orderedTotalTransform E').deleteEmpty :=
    deleteEmpty_eq_iff.2 (flat_orderedTotalTransform_truncate_eq B i (deleteEmpty_eq_iff.1 hEE'))
  refine ⟨h, ?_, fun Z => ?_⟩
  · rw [isOrderedSNC_deleteEmpty_iff, h, ← isOrderedSNC_deleteEmpty_iff]
  · rw [hasSNCWith_deleteEmpty_iff, h, ← hasSNCWith_deleteEmpty_iff]

end ClosedBlowupSequence

end MMP.Resolution

end

/-!
## `𝓑𝓜𝓞_{d,m}[𝓑]` ignores empty entries

Let `𝓑 = (𝓑_{d,μ})` be an unmarked family such that, for every dimension `a ≤ d ≤ b` and every
order `μ ≥ 1`, the assignment `(X, I, E) ↦ 𝓑_{d,μ}(X, I, E)` on the triples with `dim X = d` and
`maxord I ≤ μ` ignores empty entries. Then for `m ≥ 1` and `a ≤ d ≤ b` the functor
`(X, I, m, E) ↦ 𝓑𝓜𝓞_{d,m}[𝓑](X, I, m, E)` on the marked triples of marking `m` with `dim X = d`
ignores empty entries: deleting the empty entries `E^i = ∅` of the ordered divisor does not
change the blow-up sequence.

### Implementation notes

The members `𝓑_{d,μ}` are total assignments; the hypothesis concerns their restrictions to the
classes `idealTriplesOfDim {d} μ`, which are the triples `𝓑𝓜𝓞_{d,m}[𝓑]` feeds to `𝓑_{d,μ}`
(with `μ = maxord N(I) ≥ m` in Step 1 and `μ = m s`, `s ≥ 1`, in Step 2), so only `μ ≥ 1` is
required.

### References

* [J. Kollár, *Lectures on resolution of singularities*, 3.72, 3.111]
-/

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Resolution

namespace MMP.Resolution.FoldAux.kr3e_bmo_ignores_empty_entries

open MMP.Resolution.FoldAux.kr3e_empty_entries_transport

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

section Parts

variable {X : Scheme.{u}}

private theorem flat_orderedTotalTransform_eq : ∀ {X : Scheme.{u}} (B : ClosedBlowupSequence X)
    {E F : OrderedDivisor X}, flat E = flat F →
      flat (B.orderedTotalTransform E) = flat (B.orderedTotalTransform F)
  | _, .nil _, _, _, h => h
  | _, .cons Z B, _, _, h => flat_orderedTotalTransform_eq B (flat_totalTransform_eq h Z)

open Classical in
private theorem flat_comap_eq {Y : Scheme.{u}} {E F : OrderedDivisor X} (h : flat E = flat F)
    (f : Y ⟶ X) : flat (E.comap f) = flat (F.comap f) := by
  have hE : List.ofFn (E.comap f).E = (List.ofFn E.E).map (·.comap f) := by
    rw [List.map_ofFn]; rfl
  have hF : List.ofFn (F.comap f).E = (List.ofFn F.E).map (·.comap f) := by
    rw [List.map_ofFn]; rfl
  rw [MMP.Resolution.FoldAux.kr3e_empty_entries_transport.flat,
    MMP.Resolution.FoldAux.kr3e_empty_entries_transport.flat, hE, hF]
  refine filter_map_eq_of_filter_eq _ _ _ (fun D hD => ?_) h
  simp only [ne_eq, decide_eq_false_iff_not, not_not] at hD ⊢
  rw [hD, Scheme.IdealSheafData.comap_top]

private theorem flat_deleteEmpty (E : OrderedDivisor X) : flat E.deleteEmpty = flat E := by
  rw [MMP.Resolution.FoldAux.kr3e_empty_entries_transport.flat, ofFn_deleteEmpty,
    MMP.Resolution.FoldAux.kr3e_empty_entries_transport.flat, List.filter_filter]
  simp

private theorem notMem_componentsOf_top (W : Set X) :
    W ∉ componentsOf (((⊤ : X.IdealSheafData).support : Set X)) := by
  intro h
  obtain ⟨⟨hirr, hsub⟩, -⟩ := h
  obtain ⟨x, hx⟩ := hirr.nonempty
  simpa [Scheme.IdealSheafData.support_top] using hsub hx

private theorem isComponent_iff {E F : OrderedDivisor X} (h : flat E = flat F)
    (D : AlgebraicGeometry.PrimeDivisor X) : E.IsComponent D ↔ F.IsComponent D := by
  have key : ∀ E : OrderedDivisor X, E.IsComponent D ↔
      ∃ D' ∈ flat E, D.support ∈ componentsOf (D'.support : Set X) := by
    intro E
    simp only [OrderedDivisor.IsComponent, MMP.Resolution.FoldAux.kr3e_empty_entries_transport.flat,
      List.mem_filter, List.mem_ofFn,
      decide_eq_true_eq]
    constructor
    · rintro ⟨i, hi⟩
      refine ⟨E.E i, ⟨⟨i, rfl⟩, fun ht => ?_⟩, hi⟩
      rw [ht] at hi
      exact notMem_componentsOf_top _ hi
    · rintro ⟨_, ⟨⟨i, rfl⟩, -⟩, hi⟩
      exact ⟨i, hi⟩
  rw [key, key, h]

private theorem monomialPartCoeff_eq {E F : OrderedDivisor X} (h : flat E = flat F)
    (I : X.IdealSheafData) : monomialPartCoeff I E = monomialPartCoeff I F := by
  funext D
  have := isComponent_iff h D
  unfold monomialPartCoeff
  split_ifs <;> first | rfl | (exfalso; tauto)

private theorem nonmonomialPart_eq {E F : OrderedDivisor X} (h : flat E = flat F)
    (I : X.IdealSheafData) : nonmonomialPart I E = nonmonomialPart I F := by
  simp only [nonmonomialPart, monomialPart, monomialPartCoeff_eq h I]

private theorem mixedIdeal_eq {E F : OrderedDivisor X} (h : flat E = flat F)
    (I : X.IdealSheafData) (m s : ℕ) : mixedIdeal I E m s = mixedIdeal I F m s := by
  simp only [mixedIdeal, nonmonomialPart_eq h I]

private theorem isTriple_iff {k : Type u} [Field k] (sX : X ⟶ Spec (.of k))
    {E F : OrderedDivisor X} (h : flat E = flat F) (I : X.IdealSheafData) :
    IsTriple sX I E ↔ IsTriple sX I F := by
  have : E.IsOrderedSNC sX ↔ F.IsOrderedSNC sX := by
    rw [isOrderedSNC_deleteEmpty_iff E, isOrderedSNC_deleteEmpty_iff F,
      deleteEmpty_eq_iff.2 h]
  simp only [IsTriple, this]

private theorem maxOrder_of_isEmpty [IsEmpty X] (I : X.IdealSheafData) : maxOrder I = 0 := by
  simp [maxOrder, maxOrderAlong]

private theorem maxOrderAlong_of_isEmpty [IsEmpty X] (I : X.IdealSheafData) (Z : Set X) :
    maxOrderAlong I Z = 0 := by
  simp [maxOrderAlong]

end Parts

/-! ### The comparison along `𝓑𝓜𝓞` -/

/-- The marked triple `(X, I, m, E')` obtained by replacing the divisor. -/
private abbrev withE (t : MarkedTriple.{u}) (E : OrderedDivisor t.X) : MarkedTriple.{u} :=
  { t with E := E }

private theorem withE_mem_markedTriples_iff (t : MarkedTriple.{u}) {E : OrderedDivisor t.X}
    (h : flat E = flat t.E) : withE t E ∈ markedTriples ↔ t ∈ markedTriples :=
  isTriple_iff t.sX h t.I

/-- The marked triples met along `𝓑𝓜𝓞_{d,m}`: marked triples of dimension `d`, or empty. -/
private def Good (d : ℕ) (t : MarkedTriple.{u}) : Prop :=
  t ∈ markedTriples ∧ (HasDimensionIn t.X {d} ∨ IsEmpty t.X)

/- Geometric inputs. -/

/-- The points of a subspace `T` lying over an irreducible `Z ⊆ T` form an irreducible set. -/
private theorem isIrreducible_preimage_val {X : Type*} [TopologicalSpace X] {T Z : Set X}
    (hZ : IsIrreducible Z) (hZT : Z ⊆ T) : IsIrreducible (Subtype.val ⁻¹' Z : Set T) := by
  obtain ⟨z, hz⟩ := hZ.nonempty
  refine ⟨⟨⟨z, hZT hz⟩, hz⟩, ?_⟩
  rintro U V hU hV ⟨a, haZ, haU⟩ ⟨b, hbZ, hbV⟩
  obtain ⟨U', hU', rfl⟩ := isOpen_induced_iff.1 hU
  obtain ⟨V', hV', rfl⟩ := isOpen_induced_iff.1 hV
  obtain ⟨c, hcZ, hcU, hcV⟩ := hZ.2 U' V' hU' hV' ⟨a.1, haZ, haU⟩ ⟨b.1, hbZ, hbV⟩
  exact ⟨⟨c, hZT hcZ⟩, hcZ, hcU, hcV⟩

/-- A chain of irreducible closed subsets of `X` inside `T` has length at most `dim T`. -/
private theorem length_le_topologicalKrullDim_of_subset {X : Type*} [TopologicalSpace X]
    (p : LTSeries (IrreducibleCloseds X)) {T : Set X} (hpT : ∀ i, (p.toFun i : Set X) ⊆ T) :
    (p.length : WithBot ℕ∞) ≤ topologicalKrullDim T := by
  rw [topologicalKrullDim, Order.krullDim]
  let F : Fin (p.length + 1) → IrreducibleCloseds T := fun i =>
    ⟨Subtype.val ⁻¹' (p.toFun i : Set X),
      isIrreducible_preimage_val (p.toFun i).isIrreducible (hpT i),
      (p.toFun i).isClosed.preimage continuous_subtype_val⟩
  have hFmono : StrictMono F := by
    refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
    have hlt : p.toFun i.castSucc < p.toFun i.succ := p.step i
    have hsub : (p.toFun i.castSucc : Set X) ⊆ (p.toFun i.succ : Set X) :=
      SetLike.coe_subset_coe.2 hlt.le
    refine lt_of_le_of_ne (SetLike.coe_subset_coe.1 fun z hz => hsub hz) fun hEq => hlt.ne ?_
    refine SetLike.coe_injective (Set.ext fun a => ⟨fun ha => ?_, fun ha => ?_⟩)
    · have hmem : (⟨a, hpT _ ha⟩ : T) ∈ (F i.castSucc : Set T) := ha
      rwa [hEq] at hmem
    · have hmem : (⟨a, hpT _ ha⟩ : T) ∈ (F i.succ : Set T) := ha
      rwa [← hEq] at hmem
  exact le_iSup_of_le (LTSeries.mk p.length F hFmono) le_rfl

/-- A space all of whose irreducible components have dimension `n` has dimension `n`, if it is
nonempty. -/
private theorem topologicalKrullDim_eq_of_forall_mem_irreducibleComponents {Y : Type*}
    [TopologicalSpace Y] [Nonempty Y] {n : WithBot ℕ∞}
    (h : ∀ C ∈ irreducibleComponents Y, topologicalKrullDim C = n) :
    topologicalKrullDim Y = n := by
  refine le_antisymm ?_ ?_
  · rw [topologicalKrullDim, Order.krullDim]
    refine iSup_le fun p => ?_
    obtain ⟨C, hC, hpC⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _
      (p.toFun (Fin.last p.length)).isIrreducible
    refine le_trans (length_le_topologicalKrullDim_of_subset p fun j => ?_) (h C hC).le
    exact (SetLike.coe_subset_coe.2 (LTSeries.monotone p (Fin.le_last j))).trans hpC
  · obtain ⟨y⟩ := ‹Nonempty Y›
    rw [← h _ (irreducibleComponent_mem_irreducibleComponents y)]
    exact topologicalKrullDim_subspace_le _ _

/-- Every irreducible component of the end of a blow-up sequence has the dimension of an
irreducible component of the start. -/
private theorem exists_topologicalKrullDim_eq_of_mem_irreducibleComponents_target
    {k : Type u} [Field k] {X : Scheme.{u}} (S : ClosedBlowupSequence X) :
    ∀ (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] {C : Set S.target},
      C ∈ irreducibleComponents S.target →
        ∃ D ∈ irreducibleComponents X, topologicalKrullDim C = topologicalKrullDim D := by
  induction S with
  | nil X => exact fun _ _ C hC => ⟨C, hC, rfl⟩
  | cons Z B ih =>
    intro sX _ C hC
    haveI : IsLocallyNoetherian _ := LocallyOfFiniteType.isLocallyNoetherian sX
    haveI : IsProper (blowUpToBase Z) := AlgebraicGeometry.isProper_blowUpToBase (I := Z)
    haveI : LocallyOfFiniteType (blowUpToBase Z ≫ sX) := inferInstance
    obtain ⟨D, hD, h⟩ := ih (blowUpToBase Z ≫ sX) hC
    obtain ⟨D', hD', h'⟩ :=
      exists_topologicalKrullDim_eq_of_mem_irreducibleComponents_blowUp sX Z hD
    exact ⟨D', hD', h.trans h'⟩

/-- A blow-up of an equidimensional scheme of dimension `d` whose end is again a marked triple
(hence equidimensional) has dimension `d` or is empty. -/
private theorem good_endOf (d m : ℕ) (t : MarkedTriple.{u}) (S : ClosedBlowupSequence t.X)
    (ht : Good d t) (hS : t.endOf m S ∈ markedTriples) : Good d (t.endOf m S) := by
  refine ⟨hS, ?_⟩
  haveI : LocallyOfFiniteType t.sX := ht.1.2.2.1
  have hEq : Equidimensional t.X := ht.1.2.2.2.2.1
  by_cases hne : IsEmpty S.target
  · exact Or.inr hne
  left
  rw [not_isEmpty_iff] at hne
  obtain ⟨y⟩ := hne
  obtain ⟨D₀, hD₀, -⟩ := exists_topologicalKrullDim_eq_of_mem_irreducibleComponents_target S t.sX
    (irreducibleComponent_mem_irreducibleComponents y)
  have hXne : Nonempty t.X := by
    obtain ⟨x, -⟩ := hD₀.1.nonempty
    exact ⟨x⟩
  have hX : ∀ D ∈ irreducibleComponents t.X, topologicalKrullDim D = ((d : ℕ∞) : WithBot ℕ∞) := by
    obtain ⟨n, hn, hdim⟩ := ht.2.resolve_right (not_isEmpty_of_nonempty _)
    rw [Set.mem_singleton_iff] at hn
    subst hn
    rw [← hdim]
    refine fun D hD => (topologicalKrullDim_eq_of_forall_mem_irreducibleComponents
      fun D' hD' => ?_).symm
    exact hEq D' hD' D hD
  haveI : Nonempty (t.endOf m S).X := ⟨y⟩
  refine ⟨d, rfl, topologicalKrullDim_eq_of_forall_mem_irreducibleComponents fun C hC => ?_⟩
  obtain ⟨D, hD, h⟩ := exists_topologicalKrullDim_eq_of_mem_irreducibleComponents_target S t.sX hC
  exact h.trans (hX D hD)

/-- The nonmonomial part of the ideal of a triple is nonzero at the generic points. -/
private theorem isNonzeroAtGenericPoints_nonmonomialPart (t : MarkedTriple.{u})
    (ht : t ∈ markedTriples) : IsNonzeroAtGenericPoints (nonmonomialPart t.I t.E) := by
  intro η hη hN
  apply ht.2.2.2.2.2.1 η hη
  rw [← monomialPart_mul_nonmonomialPart t.sX t.I t.E ht, Aux.stalk_mul, hN, Ideal.mul_bot]

/-- The nonmonomial part of the ideal of a triple has finite maximal order. -/
private theorem maxOrder_nonmonomialPart_ne_top (t : MarkedTriple.{u}) (ht : t ∈ markedTriples) :
    maxOrder (nonmonomialPart t.I t.E) ≠ ⊤ := by
  have hN := isNonzeroAtGenericPoints_nonmonomialPart t ht
  obtain ⟨-, hsm, hlft, hqc, -, -, -⟩ := ht
  haveI : LocallyOfFiniteType t.sX := hlft
  haveI : QuasiCompact t.sX := hqc
  haveI : Smooth t.sX := (MMP.Mori.isSmoothScheme_iff _).1 hsm
  haveI : ∀ x : t.X, _root_.IsReduced (t.X.presheaf.stalk x) := fun x =>
    haveI := isRegularLocalRing_stalk_of_smooth_over_field t.sX x
    haveI := IsRegularLocalRing.isDomain (t.X.presheaf.stalk x)
    inferInstance
  haveI : IsReduced t.X := isReduced_of_isReduced_stalk _
  by_cases hne : IsEmpty t.X
  · rw [maxOrder_of_isEmpty]
    exact ENat.zero_ne_top
  rw [not_isEmpty_iff] at hne
  refine (exists_multAt_eq_maxOrderAlong t.sX _ ?_ (Set.univ_nonempty)).1
  intro W hW hsub
  have hgen := (QuasiSober.sober hW.1 (isClosed_of_mem_irreducibleComponents W hW)).choose_spec
  set η := (QuasiSober.sober hW.1 (isClosed_of_mem_irreducibleComponents W hW)).choose
  have hη : closure ({η} : Set t.X) ∈ irreducibleComponents t.X := by
    rwa [hgen.def]
  have hF := isField_stalk_of_closure_mem_irreducibleComponents t.X η hη
  have hbot := hN η hη
  have htop : IdealSheafData.stalk (nonmonomialPart t.I t.E) η ≠ ⊤ := fun h =>
    (IdealSheafData.stalk_eq_top_iff_notMem_support _ η).1 h (hsub hgen.mem)
  letI := hF.toField
  exact (Ideal.eq_bot_or_top _).elim hbot htop

private theorem nonmonomialPart_pow_le_mixedIdeal {X : Scheme.{u}} (I : X.IdealSheafData)
    (E : OrderedDivisor X) (m s : ℕ) : nonmonomialPart I E ^ m ≤ mixedIdeal I E m s :=
  le_self_add

private theorem pow_le_mixedIdeal {X : Scheme.{u}} (I : X.IdealSheafData)
    (E : OrderedDivisor X) (m s : ℕ) : I ^ s ≤ mixedIdeal I E m s :=
  le_add_self

/-- `K_s(I, m) = N(I)^m + I^s` is nonzero at the generic points of a triple. -/
private theorem isNonzeroAtGenericPoints_mixedIdeal (m s : ℕ) (t : MarkedTriple.{u})
    (ht : t ∈ markedTriples) : IsNonzeroAtGenericPoints (mixedIdeal t.I t.E m s) := by
  intro η hη h0
  have hN := isNonzeroAtGenericPoints_nonmonomialPart t ht η hη
  obtain ⟨-, hsm, hlft, -, -, -, -⟩ := ht
  haveI : LocallyOfFiniteType t.sX := hlft
  haveI : Smooth t.sX := (MMP.Mori.isSmoothScheme_iff _).1 hsm
  haveI := isRegularLocalRing_stalk_of_smooth_over_field t.sX η
  haveI := IsRegularLocalRing.isDomain (t.X.presheaf.stalk η)
  have h1 := MMP.Flips.ResolutionInputs.stalk_mono (nonmonomialPart_pow_le_mixedIdeal t.I t.E m s) η
  rw [h0, Aux.stalk_pow, le_bot_iff] at h1
  exact hN (eq_zero_of_pow_eq_zero h1)

/-- The unit ideal has order `0`. -/
private theorem idealOrder_top {R : Type*} [CommRing R] [IsLocalRing R] :
    idealOrder (⊤ : Ideal R) = 0 := by
  refine le_antisymm (iSup₂_le fun j hj => ?_) bot_le
  rcases j with _ | j
  · simp
  · exact absurd (top_le_iff.1 (hj.trans (Ideal.pow_le_self (Nat.succ_ne_zero j))))
      (IsLocalRing.maximalIdeal.isMaximal R).ne_top

/-- In a regular local ring, `ord(Jⁿ) ≤ n · ord(J)`: the `n`-th power of an element of `J` of
order `ord J` has order `n · ord J`, since the associated graded ring is a domain. -/
private theorem idealOrder_pow_le {R : Type*} [CommRing R] [IsRegularLocalRing R] (J : Ideal R)
    {k : ℕ} (hk : idealOrder J = k) (n : ℕ) : idealOrder (J ^ n) ≤ ((n * k : ℕ) : ℕ∞) := by
  have hJ : J ≤ IsLocalRing.maximalIdeal R ^ k := le_pow_of_le_idealOrder hk.ge
  have hJ' : ¬ J ≤ IsLocalRing.maximalIdeal R ^ (k + 1) := by
    intro h
    have : ((k + 1 : ℕ) : ℕ∞) ≤ idealOrder J :=
      le_iSup₂_of_le (f := fun (j : ℕ) (_ : J ≤ IsLocalRing.maximalIdeal R ^ j) => (j : ℕ∞))
        (k + 1) h le_rfl
    rw [hk] at this
    exact absurd (by exact_mod_cast this : k + 1 ≤ k) (by omega)
  obtain ⟨f, hfJ, hf⟩ := Set.not_subset.1 hJ'
  have hfk : f ∈ IsLocalRing.maximalIdeal R ^ k := hJ hfJ
  have key : ∀ n : ℕ, f ^ n ∈ IsLocalRing.maximalIdeal R ^ (n * k) ∧
      f ^ n ∉ IsLocalRing.maximalIdeal R ^ (n * k + 1) := by
    intro n
    induction n with
    | zero =>
      refine ⟨by simp, fun h => ?_⟩
      rw [zero_mul, zero_add, pow_zero, pow_one] at h
      exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 h)
    | succ n ih =>
      have e : (n + 1) * k = n * k + k := by ring
      rw [e, pow_succ]
      exact ⟨by rw [pow_add]; exact Ideal.mul_mem_mul ih.1 hfk,
        MMP.Flips.mul_notMem_maximalIdeal_pow_add_succ ih.1 ih.2 hfk hf⟩
  refine iSup₂_le fun j hj => ?_
  by_contra hlt
  have hlt' : n * k + 1 ≤ j := by
    have : n * k < j := by exact_mod_cast not_le.1 hlt
    omega
  exact (key n).2 (Ideal.pow_le_pow_right hlt' (hj (Ideal.pow_mem_pow hfJ n)))

/-- `maxord K_s(I, m) ≤ m s` for `s = s(X, I)` (Kollár 3.111, Step 2): off `cosupp(I, m)` the
order of `I^s` is `< m s`, and on it the order of `N(I)^m` is `≤ m s`. -/
private theorem maxOrder_mixedIdeal_le (m : ℕ) (t : MarkedTriple.{u}) (ht : t ∈ markedTriples) :
    maxOrder (mixedIdeal t.I t.E m (bmoStepTwoOrder m t)) ≤
      ((m * bmoStepTwoOrder m t : ℕ) : ℕ∞) := by
  obtain ⟨-, hsm, hlft, -, -, -, -⟩ := ht
  haveI : LocallyOfFiniteType t.sX := hlft
  haveI : Smooth t.sX := (MMP.Mori.isSmoothScheme_iff _).1 hsm
  set s := bmoStepTwoOrder m t with hs_def
  refine iSup₂_le fun x _ => ?_
  haveI := isRegularLocalRing_stalk_of_smooth_over_field t.sX x
  have h1 : multAt (mixedIdeal t.I t.E m s) x ≤
      idealOrder (IdealSheafData.stalk (nonmonomialPart t.I t.E) x ^ m) := by
    rw [← Aux.stalk_pow]
    exact Kollar.idealOrder_antitone (MMP.Flips.ResolutionInputs.stalk_mono
      (nonmonomialPart_pow_le_mixedIdeal _ _ m s) x)
  have h2 : multAt (mixedIdeal t.I t.E m s) x ≤
      idealOrder (IdealSheafData.stalk t.I x ^ s) := by
    rw [← Aux.stalk_pow]
    exact Kollar.idealOrder_antitone (MMP.Flips.ResolutionInputs.stalk_mono
      (pow_le_mixedIdeal _ _ m s) x)
  by_cases hx : x ∈ (⟨t.I, m⟩ : MarkedIdeal t.X).cosupport
  · by_cases hs0 : s = 0
    · refine h2.trans ?_
      rw [hs0, pow_zero, Ideal.one_eq_top, idealOrder_top]
      exact bot_le
    have hfin : maxOrderAlong (nonmonomialPart t.I t.E)
        (⟨t.I, m⟩ : MarkedIdeal t.X).cosupport ≠ ⊤ := by
      intro h
      apply hs0
      rw [hs_def, bmoStepTwoOrder, h]
      rfl
    have hNs : multAt (nonmonomialPart t.I t.E) x ≤ (s : ℕ∞) := by
      rw [hs_def, bmoStepTwoOrder, ENat.coe_toNat hfin]
      exact le_iSup₂_of_le (f := fun z (_ : z ∈ (⟨t.I, m⟩ : MarkedIdeal t.X).cosupport) =>
        multAt (nonmonomialPart t.I t.E) z) x hx le_rfl
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_le_ne_top (ENat.coe_ne_top s) hNs)
    refine h1.trans ((idealOrder_pow_le _ hk.symm m).trans ?_)
    have : k ≤ s := by rw [← hk] at hNs; exact_mod_cast hNs
    exact_mod_cast Nat.mul_le_mul_left m this
  · have hlt : multAt t.I x < m := not_le.1 hx
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_lt hlt)
    refine h2.trans ((idealOrder_pow_le _ hk.symm s).trans ?_)
    have : k ≤ m := by rw [← hk] at hlt; exact_mod_cast hlt.le
    rw [mul_comm m s]
    exact_mod_cast Nat.mul_le_mul_left s this

section Monomial

variable {X : Scheme.{u}}

/-- Monomial data with the divisor replaced. -/
private abbrev withEm (C : MonomialData X) (E : OrderedDivisor X) : MonomialData X :=
  { C with E := E }

private theorem strictMono_flatIdx_get (E : OrderedDivisor X) : StrictMono (flatIdx E).get :=
  List.SortedLT.strictMono_get ((List.sortedLT_finRange _).pairwise.filter _).sortedLT

private theorem map_lt_map_of_lex {n s : ℕ} {g : Fin n → Fin s} (hg : StrictMono g)
    {l₁ l₂ : List (Fin n)} (h : List.Lex (· < ·) l₁ l₂) :
    List.Lex (· < ·) (l₁.map g) (l₂.map g) := by
  induction h with
  | nil => exact List.Lex.nil
  | cons h ih => exact List.Lex.cons ih
  | rel h => exact List.Lex.rel (hg h)

private theorem map_le_map_of_le {n s : ℕ} {g : Fin n → Fin s} (hg : StrictMono g)
    {l₁ l₂ : List (Fin n)} (h : l₁ ≤ l₂) : l₁.map g ≤ l₂.map g := by
  rcases le_iff_lt_or_eq.1 h with h | rfl
  · exact le_of_lt (List.lex_lt.1 (map_lt_map_of_lex hg (List.lex_lt.2 h)))
  · exact le_rfl

open Classical in
private theorem stepIndex_spec (D : MonomialData X) (r : ℕ) (h : ∃ J P, D.IsMaxPiece r J P) :
    (∃ P, D.IsMaxPiece r (D.stepIndex r) P) ∧
      ∀ J P, D.IsMaxPiece r J P → (D.stepIndex r).sort (· ≤ ·) ≤ J.sort (· ≤ ·) := by
  unfold MonomialData.stepIndex
  dsimp only
  split
  · next hS =>
    obtain ⟨h1, h2⟩ :=
      (Finset.exists_min_image _ (fun J : Finset (Fin D.E.s) => J.sort (· ≤ ·)) hS).choose_spec
    exact ⟨(Finset.mem_filter.1 h1).2,
      fun J P hP => h2 J (Finset.mem_filter.2 ⟨Finset.mem_univ _, P, hP⟩)⟩
  · next hS =>
    obtain ⟨J, P, hP⟩ := h
    exact absurd ⟨J, Finset.mem_filter.2 ⟨Finset.mem_univ _, P, hP⟩⟩ hS

open Classical in
private theorem stepIndex_of_not (D : MonomialData X) (r : ℕ) (h : ¬ ∃ J P, D.IsMaxPiece r J P) :
    D.stepIndex r = ∅ := by
  unfold MonomialData.stepIndex
  dsimp only
  split
  · next hS =>
    obtain ⟨J, hJ⟩ := hS
    exact absurd ⟨J, (Finset.mem_filter.1 hJ).2⟩ h
  · rfl

section Reindex

variable (C : MonomialData X) {n : ℕ} {g : Fin n → Fin C.E.s} (hg : StrictMono g)
  (hgr : ∀ i, C.E.E i ≠ ⊤ → ∃ j, g j = i)

/-- The monomial data with the entries of the divisor reindexed along `g`. -/
private abbrev reindex (g : Fin n → Fin C.E.s) : MonomialData X := withEm C ⟨n, C.E.E ∘ g⟩

include hg in
private theorem reindex_stratum (J : Finset (Fin n)) :
    (reindex C g).stratum J = C.stratum (J.map ⟨g, hg.injective⟩) := by
  ext x
  simp [MonomialData.stratum]

include hg in
private theorem reindex_stratumWeight (J : Finset (Fin n)) (x : X) :
    (reindex C g).stratumWeight J x = C.stratumWeight (J.map ⟨g, hg.injective⟩) x := by
  simp only [MonomialData.stratumWeight, Finset.sum_map]
  rfl

include hg hgr in
private theorem exists_map_eq_of_mem_stratum {J : Finset (Fin C.E.s)} {x : X}
    (hx : x ∈ C.stratum J) : ∃ J' : Finset (Fin n), J'.map ⟨g, hg.injective⟩ = J := by
  classical
  refine ⟨Finset.univ.filter fun j => g j ∈ J, ?_⟩
  ext i
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact hj
  · intro hi
    have hxi : x ∈ ((C.E.E i).support : Set X) := by
      simp only [MonomialData.stratum, Set.mem_iInter] at hx
      exact hx i hi
    obtain ⟨j, rfl⟩ := hgr i fun h => by rwa [h, Scheme.IdealSheafData.support_top] at hxi
    exact ⟨j, hi, rfl⟩

include hg hgr in
private theorem reindex_maxStratumWeight (r : ℕ) :
    (reindex C g).maxStratumWeight r = C.maxStratumWeight r := by
  let F : Finset (Fin C.E.s) → ℕ := fun J =>
    ⨆ (_ : J.card = r) (x : X) (_ : x ∈ C.stratum J), C.stratumWeight J x
  have hF : ∀ J' : Finset (Fin n),
      (⨆ (_ : J'.card = r) (x : X) (_ : x ∈ (reindex C g).stratum J'),
        (reindex C g).stratumWeight J' x) = F (J'.map ⟨g, hg.injective⟩) := by
    intro J'
    simp only [F, Finset.card_map, reindex_stratum C hg, reindex_stratumWeight C hg]
  have h0 : ∀ J, (∀ J' : Finset (Fin n), J'.map ⟨g, hg.injective⟩ ≠ J) → F J = 0 := by
    intro J hJ
    refine Nat.eq_zero_of_le_zero (ciSup_le' fun _ => ciSup_le' fun x => ciSup_le' fun hx => ?_)
    obtain ⟨J', hJ'⟩ := exists_map_eq_of_mem_stratum C hg hgr hx
    exact absurd hJ' (hJ J')
  show (⨆ J' : Finset (Fin n), ⨆ (_ : J'.card = r) (x : X) (_ : x ∈ (reindex C g).stratum J'),
      (reindex C g).stratumWeight J' x) = ⨆ J, F J
  simp only [hF]
  refine le_antisymm (ciSup_le' fun J' => le_ciSup (Finite.bddAbove_range F) _)
    (ciSup_le' fun J => ?_)
  by_cases hJ : ∃ J' : Finset (Fin n), J'.map ⟨g, hg.injective⟩ = J
  · obtain ⟨J', rfl⟩ := hJ
    exact le_ciSup (Finite.bddAbove_range
      (fun J' : Finset (Fin n) => F (J'.map ⟨g, hg.injective⟩))) J'
  · push Not at hJ
    rw [h0 J hJ]
    exact Nat.zero_le _

include hg hgr in
private theorem reindex_isMaxPiece (r : ℕ) (J : Finset (Fin n)) (P : Set X) :
    (reindex C g).IsMaxPiece r J P ↔ C.IsMaxPiece r (J.map ⟨g, hg.injective⟩) P := by
  simp only [MonomialData.IsMaxPiece, Finset.card_map, reindex_stratum C hg,
    reindex_stratumWeight C hg, reindex_maxStratumWeight C hg hgr]

include hg hgr in
private theorem reindex_stepIndex (r : ℕ) :
    C.stepIndex r = ((reindex C g).stepIndex r).map ⟨g, hg.injective⟩ := by
  have hsort : ∀ J' : Finset (Fin n), (J'.map ⟨g, hg.injective⟩).sort (· ≤ ·) =
      (J'.sort (· ≤ ·)).map g := fun J' =>
    (Finset.map_sort _ _ _ _ fun a _ b _ => hg.le_iff_le.symm).symm
  by_cases h : ∃ J P, (reindex C g).IsMaxPiece r J P
  · have h' : ∃ J P, C.IsMaxPiece r J P := by
      obtain ⟨J, P, hP⟩ := h
      exact ⟨_, P, (reindex_isMaxPiece C hg hgr r J P).1 hP⟩
    obtain ⟨⟨P₀, hP₀⟩, h₀⟩ := stepIndex_spec (reindex C g) r h
    obtain ⟨⟨P₁, hP₁⟩, h₁⟩ := stepIndex_spec C r h'
    obtain ⟨x, hx, -⟩ := hP₁.2.1
    obtain ⟨J₁', hJ₁'⟩ := exists_map_eq_of_mem_stratum C hg hgr hx
    have ha := h₁ _ P₀ ((reindex_isMaxPiece C hg hgr r _ P₀).1 hP₀)
    have hb := h₀ J₁' P₁ ((reindex_isMaxPiece C hg hgr r J₁' P₁).2 (hJ₁' ▸ hP₁))
    have hb' := map_le_map_of_le hg hb
    rw [← hsort, ← hsort, hJ₁'] at hb'
    have heq := le_antisymm ha hb'
    classical
    have := congrArg List.toFinset heq
    rwa [Finset.sort_toFinset, Finset.sort_toFinset] at this
  · have h' : ¬ ∃ J P, C.IsMaxPiece r J P := by
      rintro ⟨J, P, hP⟩
      obtain ⟨x, hx, -⟩ := hP.2.1
      obtain ⟨J', rfl⟩ := exists_map_eq_of_mem_stratum C hg hgr hx
      exact h ⟨J', P, (reindex_isMaxPiece C hg hgr r J' P).2 hP⟩
    rw [stepIndex_of_not C r h', stepIndex_of_not _ r h, Finset.map_empty]

include hg hgr in
private theorem reindex_stepCenter (r : ℕ) :
    (reindex C g).stepCenter r = C.stepCenter r := by
  unfold MonomialData.stepCenter
  have : {P | (reindex C g).IsMaxPiece r ((reindex C g).stepIndex r) P} =
      {P | C.IsMaxPiece r (C.stepIndex r) P} := by
    ext P
    rw [reindex_stepIndex C hg hgr r]
    exact reindex_isMaxPiece C hg hgr r _ P
  rw [this]

end Reindex

private theorem deleteEmpty_stepCenter (C : MonomialData X) (r : ℕ) :
    (withEm C C.E.deleteEmpty).stepCenter r = C.stepCenter r :=
  reindex_stepCenter C (strictMono_flatIdx_get C.E) (exists_flatIdx_get C.E) r

private theorem deleteEmpty_maxStratumWeight (C : MonomialData X) (r : ℕ) :
    (withEm C C.E.deleteEmpty).maxStratumWeight r = C.maxStratumWeight r :=
  reindex_maxStratumWeight C (strictMono_flatIdx_get C.E) (exists_flatIdx_get C.E) r

/-- The centre of a Step-3.`r` blow-up only sees the nonempty entries of the divisor. -/
private theorem stepCenter_congr (C : MonomialData X) (E : OrderedDivisor X)
    (h : flat E = flat C.E) (r : ℕ) : (withEm C E).stepCenter r = C.stepCenter r := by
  rw [← deleteEmpty_stepCenter (withEm C E), ← deleteEmpty_stepCenter C]
  show (withEm C E.deleteEmpty).stepCenter r = (withEm C C.E.deleteEmpty).stepCenter r
  rw [deleteEmpty_eq_iff.2 h]

/-- `m_r(E, A)` only sees the nonempty entries of the divisor. -/
private theorem maxStratumWeight_congr (C : MonomialData X) (E : OrderedDivisor X)
    (h : flat E = flat C.E) (r : ℕ) : (withEm C E).maxStratumWeight r = C.maxStratumWeight r := by
  rw [← deleteEmpty_maxStratumWeight (withEm C E), ← deleteEmpty_maxStratumWeight C]
  show (withEm C E.deleteEmpty).maxStratumWeight r = (withEm C C.E.deleteEmpty).maxStratumWeight r
  rw [deleteEmpty_eq_iff.2 h]

/-- The Step-3.`r` blow-up of `C` along a given centre `Z`. -/
private noncomputable def stepAt (C : MonomialData X) (m : ℕ) (Z : X.IdealSheafData) :
    MonomialData (blowUp Z) where
  k := C.k
  sX := blowUpToBase Z ≫ C.sX
  E := C.E.totalTransform Z
  A D' :=
    (multAt ((divisorIdeal C.A).comap (blowUpToBase Z)) D'.genericPoint).toNat -
      m * (multAt (Z.comap (blowUpToBase Z)) D'.genericPoint).toNat

private theorem step_eq_stepAt (C : MonomialData X) (m r : ℕ) :
    C.step m r = stepAt C m (C.stepCenter r) := rfl

private theorem iterate_maxStratumWeight_congr (m r : ℕ) : ∀ (N : ℕ) {X : Scheme.{u}}
    (C : MonomialData X) (E : OrderedDivisor X), flat E = flat C.E →
      ((withEm C E).iterate m r N).2.maxStratumWeight r = (C.iterate m r N).2.maxStratumWeight r
  | 0, _, C, E, h => maxStratumWeight_congr C E h r
  | N + 1, _, C, E, h => by
    simp only [MonomialData.iterate]
    rw [step_eq_stepAt, step_eq_stepAt, stepCenter_congr C E h r]
    exact iterate_maxStratumWeight_congr m r N (stepAt C m (C.stepCenter r)) _
      (flat_totalTransform_eq h _)

private theorem stepPhase_congr (m r : ℕ)
    (K : ∀ {Y : Scheme.{u}}, MonomialData Y → ClosedBlowupSequence Y)
    (hK : ∀ {Y : Scheme.{u}} (D : MonomialData Y) (E : OrderedDivisor Y), flat E = flat D.E →
      K (withEm D E) = K D) : ∀ (q : ℕ) {X : Scheme.{u}}
    (C : MonomialData X) (E : OrderedDivisor X), flat E = flat C.E →
      MonomialData.stepPhase m r K q (withEm C E) = MonomialData.stepPhase m r K q C
  | 0, _, C, E, h => hK C E h
  | q + 1, _, C, E, h => by
    simp only [MonomialData.stepPhase]
    rw [step_eq_stepAt, step_eq_stepAt, stepCenter_congr C E h r]
    exact congrArg _ (stepPhase_congr m r K hK q (stepAt C m (C.stepCenter r)) _
      (flat_totalTransform_eq h _))

private theorem monomialOrderReductionFrom_congr (m : ℕ) : ∀ (j r : ℕ) {X : Scheme.{u}}
    (C : MonomialData X) (E : OrderedDivisor X), flat E = flat C.E →
      MonomialData.monomialOrderReductionFrom m j r (withEm C E) =
        MonomialData.monomialOrderReductionFrom m j r C
  | 0, _, _, _, _, _ => rfl
  | j + 1, r, _, C, E, h => by
    have hiter : ∀ N, ((withEm C E).iterate m r N).2.maxStratumWeight r =
        (C.iterate m r N).2.maxStratumWeight r :=
      fun N => iterate_maxStratumWeight_congr m r N C E h
    have hK := fun {Y : Scheme.{u}} (D : MonomialData Y) (E : OrderedDivisor Y)
      (hD : flat E = flat D.E) => monomialOrderReductionFrom_congr m j (r + 1) D E hD
    have hp : ∀ {N}, ((withEm C E).iterate m r N).2.maxStratumWeight r < m ↔
        (C.iterate m r N).2.maxStratumWeight r < m := by
      intro N; rw [hiter N]
    simp only [MonomialData.monomialOrderReductionFrom]
    by_cases hex : ∃ N, (C.iterate m r N).2.maxStratumWeight r < m
    · have hex' : ∃ N, ((withEm C E).iterate m r N).2.maxStratumWeight r < m :=
        hex.imp fun _ => hp.2
      rw [dif_pos hex, dif_pos hex', Nat.find_congr' hp]
      exact stepPhase_congr m r _ hK _ C E h
    · have hex' : ¬ ∃ N, ((withEm C E).iterate m r N).2.maxStratumWeight r < m :=
        fun ⟨N, hN⟩ => hex ⟨N, hp.1 hN⟩
      rw [dif_neg hex, dif_neg hex']
      exact hK C E h

/-- The monomial order reduction only sees the nonempty entries of the divisor. -/
private theorem monomialOrderReduction_congr (C : MonomialData X)
    (E : OrderedDivisor X) (h : flat E = flat C.E) (m : ℕ) :
    MonomialData.monomialOrderReduction ({ C with E := E } : MonomialData X) m =
      C.monomialOrderReduction m :=
  monomialOrderReductionFrom_congr m _ 1 C E h

end Monomial

/- The induction. -/

section Induction

variable (B : UnmarkedFamily.{u}) {d : ℕ}
  (hB : ∀ μ : ℕ, 1 ≤ μ → IgnoresEmptyEntries (idealTriplesOfDim {d} μ) (fun t _ => B d μ t))

include hB in
/-- `𝓑_{d,μ}` takes the same value on `(X, J, E)` and `(X, J, E')` when these are triples of
dimension `d` with `maxord J ≤ μ` and `E ∼ E'`. -/
private theorem B_congr {μ : ℕ} (hμ : 1 ≤ μ) (u : FieldBlowupTriple.{u})
    (hu : u ∈ idealTriplesOfDim {d} μ) (E : OrderedDivisor u.X) (h : flat E = flat u.E) :
    B d μ { u with E := E } = B d μ u := by
  have hu' : ({ u with E := E } : FieldBlowupTriple.{u}) ∈ idealTriplesOfDim {d} μ :=
    ⟨(isTriple_iff u.sX h u.I).2 hu.1, hu.2⟩
  obtain ⟨_, h1⟩ := hB μ hμ u hu
  obtain ⟨_, h2⟩ := hB μ hμ _ hu'
  have h1' : B d μ { u with E := u.E.deleteEmpty } = B d μ u := h1
  have h2' : B d μ { u with E := E.deleteEmpty } = B d μ { u with E := E } := h2
  rw [← h2', ← h1', deleteEmpty_eq_iff.2 h]

variable (m : ℕ) (hm : 1 ≤ m)

include hB hm in
private theorem bmoStepOneAux_withE : ∀ (q : ℕ) (t : MarkedTriple.{u}) (E : OrderedDivisor t.X),
    Good d t → flat E = flat t.E →
      bmoStepOneAux B d m q (withE t E) = bmoStepOneAux B d m q t
  | 0, _, _, _, _ => rfl
  | q + 1, t, E, ht, h => by
    simp only [bmoStepOneAux]
    rw [nonmonomialPart_eq h t.I]
    by_cases hlt : maxOrder (nonmonomialPart t.I t.E) < m
    · rw [if_pos hlt, if_pos hlt]
    · rw [if_neg hlt, if_neg hlt]
      have hne : ¬ IsEmpty t.X := by
        intro hX
        exact hlt (by rw [maxOrder_of_isEmpty]; exact_mod_cast hm)
      have hfin := maxOrder_nonmonomialPart_ne_top t ht.1
      have hμ : 1 ≤ (maxOrder (nonmonomialPart t.I t.E)).toNat := by
        have : (m : ℕ∞) ≤ maxOrder (nonmonomialPart t.I t.E) := not_lt.1 hlt
        rw [← ENat.coe_toNat hfin] at this
        exact hm.trans (by exact_mod_cast this)
      have hu : (⟨⟨t.X, nonmonomialPart t.I t.E, t.E⟩, t.k, t.sX⟩ : FieldBlowupTriple.{u}) ∈
          idealTriplesOfDim {d} (maxOrder (nonmonomialPart t.I t.E)).toNat := by
        obtain ⟨h1, h2, h3, h4, h5, -, h7⟩ := ht.1
        refine ⟨⟨h1, h2, h3, h4, h5, isNonzeroAtGenericPoints_nonmonomialPart t ht.1, h7⟩,
          ht.2.resolve_right hne, ?_⟩
        exact (ENat.coe_toNat hfin).ge
      rw [B_congr B hB hμ _ hu E h]
      generalize B d (maxOrder (nonmonomialPart t.I t.E)).toNat
        ⟨⟨t.X, nonmonomialPart t.I t.E, t.E⟩, t.k, t.sX⟩ = S
      have hS := flat_orderedTotalTransform_eq S h
      have hmem := withE_mem_markedTriples_iff (t.endOf m S) hS
      by_cases h1 : t.endOf m S ∈ markedTriples
      · have h1' : (withE t E).endOf m S ∈ markedTriples := hmem.2 h1
        simp only [h1, h1', ↓reduceIte]
        exact congrArg S.append
          (bmoStepOneAux_withE q (t.endOf m S) _ (good_endOf d m t S ht h1) hS)
      · have h1' : ¬ ((withE t E).endOf m S ∈ markedTriples) := fun h' => h1 (hmem.1 h')
        simp only [h1, h1', ↓reduceIte]

private theorem bmoStepTwoOrder_withE (t : MarkedTriple.{u}) {E : OrderedDivisor t.X}
    (h : flat E = flat t.E) : bmoStepTwoOrder m (withE t E) = bmoStepTwoOrder m t := by
  simp only [bmoStepTwoOrder, nonmonomialPart_eq h t.I]

include hB hm in
private theorem bmoStepTwoAux_withE : ∀ (q : ℕ) (t : MarkedTriple.{u}) (E : OrderedDivisor t.X),
    Good d t → flat E = flat t.E →
      bmoStepTwoAux B d m q (withE t E) = bmoStepTwoAux B d m q t
  | 0, _, _, _, _ => rfl
  | q + 1, t, E, ht, h => by
    simp only [bmoStepTwoAux]
    rw [bmoStepTwoOrder_withE m t h]
    by_cases hs : bmoStepTwoOrder m t = 0
    · rw [if_pos hs, if_pos hs]
    · rw [if_neg hs, if_neg hs]
      have hne : ¬ IsEmpty t.X := by
        intro hX
        exact hs (by simp [bmoStepTwoOrder, maxOrderAlong_of_isEmpty])
      have hμ : 1 ≤ m * bmoStepTwoOrder m t := Nat.one_le_iff_ne_zero.2 (by positivity)
      have hu : (⟨⟨t.X, mixedIdeal t.I t.E m (bmoStepTwoOrder m t), t.E⟩, t.k, t.sX⟩ :
          FieldBlowupTriple.{u}) ∈ idealTriplesOfDim {d} (m * bmoStepTwoOrder m t) := by
        obtain ⟨h1, h2, h3, h4, h5, -, h7⟩ := ht.1
        exact ⟨⟨h1, h2, h3, h4, h5, isNonzeroAtGenericPoints_mixedIdeal m _ t ht.1, h7⟩,
          ht.2.resolve_right hne, maxOrder_mixedIdeal_le m t ht.1⟩
      rw [mixedIdeal_eq h t.I, B_congr B hB hμ _ hu E h]
      generalize B d (m * bmoStepTwoOrder m t)
        ⟨⟨t.X, mixedIdeal t.I t.E m (bmoStepTwoOrder m t), t.E⟩, t.k, t.sX⟩ = S
      have hS := flat_orderedTotalTransform_eq S h
      have hmem := withE_mem_markedTriples_iff (t.endOf m S) hS
      by_cases h1 : t.endOf m S ∈ markedTriples
      · have h1' : (withE t E).endOf m S ∈ markedTriples := hmem.2 h1
        simp only [h1, h1', ↓reduceIte]
        exact congrArg S.append
          (bmoStepTwoAux_withE q (t.endOf m S) _ (good_endOf d m t S ht h1) hS)
      · have h1' : ¬ ((withE t E).endOf m S ∈ markedTriples) := fun h' => h1 (hmem.1 h')
        simp only [h1, h1', ↓reduceIte]

/-- Step 3 of `𝓑𝓜𝓞`: the extension by closure of the monomial order reduction on
`U = X ∖ cosupp N(I)`. -/
private noncomputable def monoTail (t : MarkedTriple.{u}) : ClosedBlowupSequence t.X :=
  let U : t.X.Opens := (nonmonomialPart t.I t.E).support.compl
  let C : MonomialData U :=
    ⟨t.k, U.ι ≫ t.sX, t.E.comap U.ι, monomialPartCoeff (t.I.comap U.ι) (t.E.comap U.ι)⟩
  (C.monomialOrderReduction m).extendByClosure U.ι

open Classical in
/-- Steps 2 and 3 of `𝓑𝓜𝓞`, from the end of Step 1. -/
private noncomputable def stepTwoTail (t : MarkedTriple.{u}) : ClosedBlowupSequence t.X :=
  let S₂ := if t ∈ markedTriples then bmoStepTwo B d m t else .nil t.X
  S₂.append (monoTail m (t.endOf m S₂))

open Classical in
private theorem bmoFunctor_eq (t : MarkedTriple.{u}) :
    bmoFunctor B d m t =
      ((if t ∈ markedTriples then bmoStepOne B d m t else .nil t.X).append
        (@stepTwoTail B d m (t.endOf m (if t ∈ markedTriples then bmoStepOne B d m t
          else .nil t.X)))).reduction := rfl

private theorem monoTail_withE (t : MarkedTriple.{u}) (E : OrderedDivisor t.X)
    (h : flat E = flat t.E) : monoTail m (withE t E) = monoTail m t := by
  simp only [monoTail]
  rw [nonmonomialPart_eq h t.I]
  set ι := Scheme.Opens.ι (nonmonomialPart t.I t.E).support.compl
  have hc := flat_comap_eq h ι
  rw [monomialPartCoeff_eq hc]
  exact congrArg (·.extendByClosure ι) (monomialOrderReduction_congr
    ⟨t.k, ι ≫ t.sX, t.E.comap ι, monomialPartCoeff (t.I.comap ι) (t.E.comap ι)⟩ _ hc m)

include hB hm in
private theorem stepTwoTail_withE (t : MarkedTriple.{u}) (E : OrderedDivisor t.X)
    (ht : t ∈ markedTriples → Good d t) (h : flat E = flat t.E) :
    @stepTwoTail B d m (withE t E) = @stepTwoTail B d m t := by
  have hmem := withE_mem_markedTriples_iff t h
  by_cases h1 : t ∈ markedTriples
  · have h1' : withE t E ∈ markedTriples := hmem.2 h1
    have h2 : bmoStepTwo B d m (withE t E) = bmoStepTwo B d m t := by
      simp only [bmoStepTwo]
      rw [bmoStepTwoOrder_withE m t h]
      exact bmoStepTwoAux_withE B hB m hm _ t E (ht h1) h
    simp only [stepTwoTail]
    rw [if_pos h1, if_pos h1', h2]
    exact congrArg (ClosedBlowupSequence.append (bmoStepTwo B d m t))
      (monoTail_withE m (t.endOf m (bmoStepTwo B d m t)) _ (flat_orderedTotalTransform_eq _ h))
  · have h1' : withE t E ∉ markedTriples := fun h' => h1 (hmem.1 h')
    simp only [stepTwoTail]
    rw [if_neg h1, if_neg h1']
    exact congrArg (ClosedBlowupSequence.append (.nil t.X))
      (monoTail_withE m (t.endOf m (.nil t.X)) _ (flat_orderedTotalTransform_eq _ h))

include hB hm in
private theorem bmoFunctor_withE (t : MarkedTriple.{u}) (ht : t ∈ markedTriplesOfDim {d} m)
    (E : OrderedDivisor t.X) (h : flat E = flat t.E) :
    bmoFunctor B d m (withE t E) = bmoFunctor B d m t := by
  have hgood : Good d t := ⟨ht.1, Or.inl ht.2.2⟩
  have hmem : withE t E ∈ markedTriples := (withE_mem_markedTriples_iff t h).2 ht.1
  have h1 : bmoStepOne B d m (withE t E) = bmoStepOne B d m t := by
    simp only [bmoStepOne]
    rw [nonmonomialPart_eq h t.I]
    exact bmoStepOneAux_withE B hB m hm _ t E hgood h
  rw [bmoFunctor_eq, bmoFunctor_eq, if_pos ht.1, if_pos hmem, h1]
  generalize bmoStepOne B d m t = S
  exact congrArg (fun T => (S.append T).reduction)
    (stepTwoTail_withE B hB m hm (t.endOf m S) _ (good_endOf d m t S hgood)
      (flat_orderedTotalTransform_eq S h))

end Induction

end MMP.Resolution.FoldAux.kr3e_bmo_ignores_empty_entries

namespace MMP.Resolution

open MMP.Resolution.FoldAux.kr3e_empty_entries_transport
    MMP.Resolution.FoldAux.kr3e_bmo_ignores_empty_entries in
/-- **`𝓑𝓜𝓞_{d,m}[𝓑]` ignores empty entries** (needed for Kollár 3.72). If every member
`𝓑_{d',μ}` of an unmarked family, `a ≤ d' ≤ b`, `μ ≥ 1`, ignores empty entries on the triples of
dimension `d'` with `maxord ≤ μ`, then for `m ≥ 1` and `a ≤ d ≤ b`, `bmoFunctor B d m` ignores
empty entries on the marked triples of marking `m` and dimension `d`. -/
@[mmp "lem_kr3e_bmo_ignores_empty_entries"]
public theorem ignoresEmptyEntriesMarked_bmoFunctor {a b : ℕ} (B : UnmarkedFamily.{u})
    (hB : ∀ d' ∈ Set.Icc a b, ∀ μ : ℕ, 1 ≤ μ →
      IgnoresEmptyEntries (idealTriplesOfDim {d'} μ) (fun t _ => B d' μ t))
    {m d : ℕ} (hm : 1 ≤ m) (hd : d ∈ Set.Icc a b) :
    IgnoresEmptyEntriesMarked (markedTriplesOfDim {d} m) (fun t _ => bmoFunctor B d m t) := by
  intro t ht
  have hflat : flat t.E.deleteEmpty = flat t.E := flat_deleteEmpty _
  exact ⟨⟨(withE_mem_markedTriples_iff t hflat).2 ht.1, ht.2.1, ht.2.2⟩,
    bmoFunctor_withE B (fun μ hμ => hB d hd μ hμ) m hm t ht _ hflat⟩

end MMP.Resolution

end

/-!
## Commuting with a morphism is local on the base

Let `𝒯` be a class of triples `(X, I, E)` over fields, closed under pull-back along open cover
maps, and `𝐁` a blow-up sequence functor on `𝒯` commuting with every surjective open cover map.
Let `h : Y → X` be a morphism with `(X, I, E)` and `(Y, h^*I, h⁻¹E)` in `𝒯`, and
`g : X^* → X` a surjective open cover map, with `Y^* = Y ×_X X^*` and projection
`h^* : Y^* → X^*`. If `𝐁(Y^*) = (h^{*\,*}𝐁(X^*))^red`, then `𝐁(Y) = (h^*𝐁(X))^red`: the
identity `𝐁(Y) = (h^*𝐁(X))^red` may be checked after a surjective open cover of `X`.

### Implementation notes

The triples of `𝒯` are `FieldBlowupTriple`s, and the triple on `Y^*` is the pull-back of the
triple on `X^*` along `h^*`. The hypothesis on `Y^*` is required for every proof that the triples
on `X^*` and `Y^*` lie in `𝒯`; both memberships follow from the closure of `𝒯` under open cover
maps, `Y^* → Y` being the base change of `g`. The morphism `h` is arbitrary and the values of `𝐁`
need not be free of empty blow-ups: the argument only uses that `Y^* → Y` is a flat surjective
open cover map, so that a blow-up sequence on `Y` is determined by its pull-back to `Y^*`, and
that pull-back along a surjection commutes with deleting empty blow-ups.

### References

* [J. Kollár, *Lectures on resolution of singularities*, 3.34 and 3.104 Step 2.3]
-/

section

open CategoryTheory AlgebraicGeometry Limits MMP.Resolution
open ClosedBlowupSequence

namespace MMP.Resolution.FoldAux.kr3e_functoriality_is_local

private theorem pullback_heq {X Y Y' : Scheme.{u}} (B : ClosedBlowupSequence X) (e : Y = Y')
    (f : Y ⟶ X) (f' : Y' ⟶ X) (hf : f = eqToHom e ≫ f') : B.pullback f ≍ B.pullback f' := by
  subst e; simp at hf; subst hf; rfl

private theorem pullbackReduced_heq {X Y Y' : Scheme.{u}} (B : ClosedBlowupSequence X)
    (e : Y = Y') (f : Y ⟶ X) (f' : Y' ⟶ X) (hf : f = eqToHom e ≫ f') :
    B.pullbackReduced f ≍ B.pullbackReduced f' := by
  subst e; simp at hf; subst hf; rfl

private theorem eqToHom_blowUpToBase' {Y : Scheme.{u}} {I I' : Y.IdealSheafData} (e : I = I') :
    eqToHom (congrArg blowUp e) ≫ blowUpToBase I' = blowUpToBase I := by
  subst e; simp

private theorem canonicalLift_comp {W Y X : Scheme.{u}} (k : W ⟶ Y) (h : Y ⟶ X)
    (Z : X.IdealSheafData) :
    canonicalLift k (Z.comap h) ≫ canonicalLift h Z =
      eqToHom (congrArg blowUp (Scheme.IdealSheafData.comap_comp Z k h).symm) ≫
        canonicalLift (k ≫ h) Z := by
  have hc : Stacks.Blowup.IsCartierOver Z
      (Over.mk (blowUpToBase ((Z.comap h).comap k) ≫ k ≫ h)) := by
    change Stacks.Divisors.IsEffectiveCartierDivisor
      (Z.comap (blowUpToBase ((Z.comap h).comap k) ≫ k ≫ h))
    rw [Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp]
    exact Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal _
  refine (blowUpLift_unique Z _ hc _ ?_).trans (blowUpLift_unique Z _ hc _ ?_).symm
  · rw [Category.assoc, canonicalLift_comp_blowUpToBase, ← Category.assoc,
      canonicalLift_comp_blowUpToBase, Category.assoc]
  · rw [Category.assoc, canonicalLift_comp_blowUpToBase, ← Category.assoc,
      eqToHom_blowUpToBase']
    exact (Scheme.IdealSheafData.comap_comp Z k h).symm

/-- `k^*(h^*𝐁) = (h ∘ k)^*𝐁`. -/
private theorem pullback_pullback {X : Scheme.{u}} (B : ClosedBlowupSequence X) :
    ∀ {Y W : Scheme.{u}} (h : Y ⟶ X) (k : W ⟶ Y),
      (B.pullback h).pullback k = B.pullback (k ≫ h) := by
  induction B with
  | nil X => intros; rfl
  | cons Z B ih =>
    intro Y W h k
    refine cons_eq_cons_iff.2 ⟨(Scheme.IdealSheafData.comap_comp Z k h).symm, ?_⟩
    rw [ih]
    exact pullback_heq _ _ _ _ (canonicalLift_comp k h Z)

/-- `f^*` of a pulled-back sequence with empty blow-ups deleted: `(k^*𝐁)` reduced along `f` is
`𝐁` reduced along `k ∘ f`. -/
private theorem pullbackReduced_pullback {X : Scheme.{u}} (B : ClosedBlowupSequence X) :
    ∀ {Y W : Scheme.{u}} (k : Y ⟶ X) (f : W ⟶ Y),
      (B.pullback k).pullbackReduced f = B.pullbackReduced (f ≫ k) := by
  induction B with
  | nil X => intros; rfl
  | cons Z B ih =>
    intro Y W k f
    by_cases hZ : (Z.comap k).comap f = ⊤
    · have hZ' : Z.comap (f ≫ k) = ⊤ := by rwa [Scheme.IdealSheafData.comap_comp]
      simp only [ClosedBlowupSequence.pullback, ClosedBlowupSequence.pullbackReduced, hZ, hZ',
        dite_true]
      rw [ih]
      congr 1
      refine blowUpLift_unique _ _ _ _ ?_
      rw [Category.assoc, canonicalLift_comp_blowUpToBase, ← Category.assoc, blowUpLift_comp]
    · have hZ' : ¬ Z.comap (f ≫ k) = ⊤ := by rwa [Scheme.IdealSheafData.comap_comp]
      simp only [ClosedBlowupSequence.pullback, ClosedBlowupSequence.pullbackReduced, hZ, hZ',
        dite_false]
      refine cons_eq_cons_iff.2 ⟨(Scheme.IdealSheafData.comap_comp Z f k).symm, ?_⟩
      rw [ih]
      exact pullbackReduced_heq _ _ _ _ (canonicalLift_comp f k Z)

/-- Pull-back along a flat surjection commutes with deleting empty blow-ups. -/
private theorem pullback_pullbackReduced {X : Scheme.{u}} (B : ClosedBlowupSequence X) :
    ∀ {Y W : Scheme.{u}} (f : Y ⟶ X) (k : W ⟶ Y) [Flat k] [Surjective k],
      (B.pullbackReduced f).pullback k = B.pullbackReduced (k ≫ f) := by
  induction B with
  | nil X => intros; rfl
  | cons Z B ih =>
    intro Y W f k _ _
    by_cases hZ : Z.comap f = ⊤
    · have hZ' : Z.comap (k ≫ f) = ⊤ := by
        rw [Scheme.IdealSheafData.comap_comp, hZ, Scheme.IdealSheafData.comap_top]
      simp only [ClosedBlowupSequence.pullbackReduced, hZ, hZ', dite_true]
      rw [ih]
      congr 1
      refine blowUpLift_unique _ _ _ _ ?_
      rw [Category.assoc, blowUpLift_comp]
    · have hZ' : ¬ Z.comap (k ≫ f) = ⊤ := by
        intro e
        refine hZ (MMP.Resolution.Kollar.eq_of_comap_eq_of_flat_of_surjective k ?_)
        rw [← Scheme.IdealSheafData.comap_comp, e, Scheme.IdealSheafData.comap_top]
      simp only [ClosedBlowupSequence.pullback, ClosedBlowupSequence.pullbackReduced, hZ, hZ',
        dite_false]
      have := MMP.Resolution.Kollar.flat_canonicalLift k (Z.comap f)
      have := MMP.Resolution.Kollar.surjective_canonicalLift k (Z.comap f)
      refine cons_eq_cons_iff.2 ⟨(Scheme.IdealSheafData.comap_comp Z k f).symm, ?_⟩
      rw [ih]
      exact pullbackReduced_heq _ _ _ _ (canonicalLift_comp k f Z)

/-- `k^*(𝐁^red) = (k^*𝐁)^red` for a flat surjection `k`. -/
private theorem reduction_pullback {X W : Scheme.{u}} (B : ClosedBlowupSequence X) (k : W ⟶ X)
    [Flat k] [Surjective k] : (B.pullback k).reduction = B.reduction.pullback k := by
  rw [reduction, reduction, pullbackReduced_pullback, pullback_pullbackReduced]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- An open cover map is flat. -/
private theorem flat_of_isOpenCoverMap {X' X : Scheme.{u}} {g : X' ⟶ X}
    (hg : IsOpenCoverMap g) : Flat g := by
  obtain ⟨n, U, -, hU, hi⟩ := hg
  exact IsZariskiLocalAtSource.of_iSup_eq_top U hU fun a => inferInstance

/-- The base change `Y ×_X X^* → Y` of an open cover map `X^* → X` is an open cover map. -/
private theorem isOpenCoverMap_pullback_fst {X' X Y : Scheme.{u}} {g : X' ⟶ X}
    (hg : IsOpenCoverMap g) (h : Y ⟶ X) : IsOpenCoverMap (pullback.fst h g) := by
  obtain ⟨n, U, hd, hU, hi⟩ := hg
  refine ⟨n, fun a => pullback.snd h g ⁻¹ᵁ U a, fun a b hab => ?_, ?_, fun a => ?_⟩
  · show Disjoint _ _
    rw [disjoint_iff, ← Scheme.Hom.preimage_inf, disjoint_iff.1 (hd hab),
      Scheme.Hom.preimage_bot]
  · rw [← Scheme.Hom.preimage_iSup, hU, Scheme.Hom.preimage_top]
  · have hpb := (isPullback_morphismRestrict (pullback.snd h g) (U a)).flip.paste_horiz
      (IsPullback.of_hasPullback h g)
    exact MorphismProperty.of_isPullback (P := @IsOpenImmersion) hpb.flip (hi a)

/-- Pulling back along `a` then `b` is pulling back along `b ≫ a`. -/
private theorem fieldBlowupTriple_pullback_pullback (t : FieldBlowupTriple.{u})
    {Y W : Scheme.{u}} (a : Y ⟶ t.X) (b : W ⟶ Y) :
    (t.pullback a).pullback b = t.pullback (b ≫ a) := by
  have h1 : (t.I.comap a).comap b = t.I.comap (b ≫ a) :=
    (Scheme.IdealSheafData.comap_comp _ _ _).symm
  have h2 : (fun i => ((t.E.E i).comap a).comap b) = fun i => (t.E.E i).comap (b ≫ a) :=
    funext fun i => (Scheme.IdealSheafData.comap_comp _ _ _).symm
  unfold FieldBlowupTriple.pullback OrderedDivisor.comap
  dsimp only
  rw [h1, h2, Category.assoc]

private theorem functor_heq {𝒯 : Set FieldBlowupTriple.{u}}
    (B : BlowupSequenceFunctor FieldBlowupTriple.toBlowupTriple 𝒯) {a b : FieldBlowupTriple.{u}}
    (e : a = b) (ha : a ∈ 𝒯) (hb : b ∈ 𝒯) : B a ha ≍ B b hb := by
  subst e; rfl

/-- A blow-up sequence `C` on `Y` is `(h^*𝐁)^red` as soon as its pull-back along a flat
surjection `k : W → Y` is `(k'^*g^*𝐁)^red` for some `k'` with `h ∘ k = g ∘ k'`. -/
private theorem eq_pullback_reduction_of_pullback_eq {X Y X' W : Scheme.{u}}
    (B : ClosedBlowupSequence X) {h : Y ⟶ X} {g : X' ⟶ X} {k : W ⟶ Y} {k' : W ⟶ X'}
    [Flat k] [Surjective k] (w : k ≫ h = k' ≫ g) {C : ClosedBlowupSequence Y}
    (hC : C.pullback k = ((B.pullback g).pullback k').reduction) :
    C = (B.pullback h).reduction := by
  apply MMP.Resolution.Kollar.eq_of_pullback_eq_of_flat_of_surjective k
  rw [← reduction_pullback, pullback_pullback, hC, pullback_pullback, w]

end MMP.Resolution.FoldAux.kr3e_functoriality_is_local

namespace MMP.Resolution

namespace BlowupSequenceFunctor

open MMP.Resolution.FoldAux.kr3e_functoriality_is_local in
/-- **Kollár 3.104 Step 2.3, 3.34.** Let `𝒯` be a class of triples closed under pull-back along
open cover maps and `𝐁` a blow-up sequence functor on `𝒯` commuting with every surjective open
cover map. Let `h : Y → X` be a morphism with `t = (X, I, E) ∈ 𝒯` and `(Y, h^*I, h⁻¹E) ∈ 𝒯`, and
`g : X^* → X` a surjective open cover map. If `𝐁(Y^*) = (h^{*\,*}𝐁(X^*))^red` for
`Y^* = Y ×_X X^*` and the projection `h^* : Y^* → X^*`, then `𝐁(Y) = (h^*𝐁(X))^red`. -/
@[mmp "lem_kr3e_functoriality_is_local"]
public theorem eq_pullback_reduction_of_isOpenCoverMap {𝒯 : Set FieldBlowupTriple.{u}}
    (B : BlowupSequenceFunctor FieldBlowupTriple.toBlowupTriple 𝒯)
    (h𝒯 : ∀ t ∈ 𝒯, ∀ (X' : Scheme.{u}) (g : X' ⟶ t.X), IsOpenCoverMap g → t.pullback g ∈ 𝒯)
    (hcomm : ∀ (t : FieldBlowupTriple.{u}) (ht : t ∈ 𝒯) (X' : Scheme.{u}) (g : X' ⟶ t.X),
      IsOpenCoverMap g → Surjective g →
        ∀ ht' : t.pullback g ∈ 𝒯, B (t.pullback g) ht' = (B t ht).pullback g)
    (t : FieldBlowupTriple.{u}) (ht : t ∈ 𝒯) {Y : Scheme.{u}} (h : Y ⟶ t.X)
    (hY : t.pullback h ∈ 𝒯) {X' : Scheme.{u}} (g : X' ⟶ t.X) (hg : IsOpenCoverMap g)
    (hgs : Surjective g)
    (hstar : ∀ (hX' : t.pullback g ∈ 𝒯)
      (hY' : (t.pullback g).pullback (pullback.snd h g) ∈ 𝒯),
        B ((t.pullback g).pullback (pullback.snd h g)) hY' =
          ((B (t.pullback g) hX').pullback (pullback.snd h g)).reduction) :
    B (t.pullback h) hY = ((B t ht).pullback h).reduction := by
  have hgY := isOpenCoverMap_pullback_fst hg h
  have : Flat (pullback.fst h g) := flat_of_isOpenCoverMap hgY
  have hsY : Surjective (pullback.fst h g) :=
    MorphismProperty.of_isPullback (P := @Surjective) (IsPullback.of_hasPullback h g).flip hgs
  have hYs := h𝒯 _ hY _ _ hgY
  have e : (t.pullback h).pullback (pullback.fst h g) =
      (t.pullback g).pullback (pullback.snd h g) := by
    rw [fieldBlowupTriple_pullback_pullback, fieldBlowupTriple_pullback_pullback,
      pullback.condition]
  have hX' := h𝒯 t ht X' g hg
  refine eq_pullback_reduction_of_pullback_eq (k := pullback.fst h g) (k' := pullback.snd h g) _
    pullback.condition ?_
  exact (hcomm _ hY _ _ hgY hsY hYs).symm.trans <|
    (eq_of_heq (functor_heq B e hYs (e ▸ hYs))).trans <| (hstar hX' _).trans <|
      congrArg (fun C => (C.pullback (pullback.snd h g)).reduction) (hcomm t ht X' g hg hgs hX')

end BlowupSequenceFunctor

end MMP.Resolution

end

/-!
## Blowing up a centre inside a hypersurface preserves simple normal crossings

Let `X` be a smooth quasi-compact scheme locally of finite type over a field `k` of characteristic
zero, `H ⊆ X` a smooth hypersurface, `D = (D^1, …, D^t)` a divisor with ordered index set and
`V ⊆ X` an open subset on which `(H, D^1, …, D^t)` is an ordered simple normal crossing divisor.
Let `Z ⊆ H` be a smooth closed subscheme which has simple normal crossings with `∑ᵢ D^i` and none
of whose irreducible components is an irreducible component of `H`, and let `π : B_ZX → X` be the
blow-up. Then `(H', π⁻¹_tot D)` is an ordered simple normal crossing divisor on `π⁻¹(V)`, where
`H'` is the birational transform of `H`, the reduced closure of `π⁻¹(H ∖ Z)`.

### Implementation notes

A closed subscheme `Z ⊆ H` is an ideal sheaf `Z` on `X` with `H ≤ Z`. The ordered divisor
`(H, D^1, …, D^t)` is `Fin.cons H D.E`, and its restriction to an open `V` is its inverse image
`OrderedDivisor.comap` along `V.ι`, over `k` by `V.ι ≫ sX`; likewise on `π⁻¹(V)`. The total
transform is `MMP.Resolution.OrderedDivisor.totalTransform`. The birational transform `H'` is
written out as the reduced closure of `π⁻¹(H ∖ Z)`. The base field has characteristic zero, the
standing convention of Kollár's §3, which the snc property of total transforms uses. Where the
source asks `X` to be a variety, `X` is only assumed quasi-compact and locally of finite type
over `k`: the snc property is checked in local coordinates at each point, and the blow-up and the
birational and total transforms are local on `X`, so neither irreducibility nor separatedness
is used. Nor are the smoothness of `X`, `H` and `Z`, nor that `D` is a divisor: the snc
hypothesis on `V` already provides regular coordinates there. The birational transform `H'` is
also the closed subscheme cut out by the restriction of the one-step blow-up sequence `(X, Z)`
to `H`, `ker_restrictHom_cons_nil_eq_vanishingIdeal`.

### References

* [J. Kollár, *Lectures on resolution of singularities*, 3.103 Step 2.1 and 3.104 Step 2.1]
-/

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Resolution

namespace MMP.Resolution.FoldAux.kr3e_snc_with_maximal_contact_preserved

open IsLocalRing MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

section Coordinates

/-- Local coordinates adapted to a family of ideals and to one more ideal are carried along a ring
isomorphism. -/
private theorem coords_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R]
    [IsLocalRing S] (e : R ≃+* S) {ι κ : Type*} (σ : ι ≃ κ) (IR : ι → Ideal R)
    (IS : κ → Ideal S) (hI : ∀ i, IS (σ i) = (IR i).map e) (ZR : Ideal R) (ZS : Ideal S)
    (hZ : ZS = ZR.map e)
    (h : ∃ (n : ℕ) (z : Fin n → R) (c : ι → Fin n) (J : Finset (Fin n)),
      IsRegularSystemOfParameters z ∧ (∀ i, IR i = Ideal.span {z (c i)}) ∧
        Function.Injective c ∧ ZR = Ideal.span (z '' (J : Set (Fin n)))) :
    ∃ (n : ℕ) (w : Fin n → S) (c : κ → Fin n) (J : Finset (Fin n)),
      IsRegularSystemOfParameters w ∧ (∀ i, IS i = Ideal.span {w (c i)}) ∧
        Function.Injective c ∧ ZS = Ideal.span (w '' (J : Set (Fin n))) := by
  obtain ⟨n, z, c, J, hz, hc, hinj, hJ⟩ := h
  refine ⟨n, fun i => e (z i), c ∘ σ.symm, J, isRegularSystemOfParameters_map_ringEquiv e hz,
    fun i => ?_, hinj.comp σ.symm.injective, ?_⟩
  · rw [← σ.apply_symm_apply i, hI, hc, Ideal.map_span, Set.image_singleton]
    simp
  · rw [hZ, hJ, Ideal.map_span, Set.image_image]

/-- The stalk isomorphism of an open immersion `j` carries the stalk of an ideal sheaf at `j u`
to the stalk of its inverse image at `u`. -/
private theorem exists_ringEquiv_stalk_comap {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (u : U) : ∃ e : X.presheaf.stalk (j u) ≃+* U.presheaf.stalk u, ∀ I : X.IdealSheafData,
      IdealSheafData.stalk (I.comap j) u = (IdealSheafData.stalk I (j u)).map e := by
  letI := IsOpenImmersion.instIsIsoCommRingCatStalkMap j u
  exact ⟨(asIso (j.stalkMap u)).commRingCatIsoToRingEquiv,
    fun I => by rw [IdealSheafData.stalk_comap]; rfl⟩

/-- The members of a family through `u` are those of its inverse image along `j` through `j u`. -/
private def comapSupportEquiv {X U : Scheme.{u}} (j : U ⟶ X) {Λ : Type*}
    (F : Λ → X.IdealSheafData) (u : U) :
    {i // u ∈ ((F i).comap j).support} ≃ {i // j u ∈ (F i).support} :=
  Equiv.subtypeEquivRight fun i => by
    rw [← SetLike.mem_coe, Scheme.IdealSheafData.support_comap]; rfl

/-- Local coordinates at `x` adapted to the family `F` and to `T`. -/
private def CoordsAt {X : Scheme.{u}} {Λ : Type*} (F : Λ → X.IdealSheafData)
    (T : X.IdealSheafData) (x : X) : Prop :=
  ∃ (n : ℕ) (z : Fin n → X.presheaf.stalk x) (c : {i // x ∈ (F i).support} → Fin n)
    (J : Finset (Fin n)),
    IsRegularSystemOfParameters z ∧ (∀ i, IdealSheafData.stalk (F i.1) x = Ideal.span {z (c i)}) ∧
      Function.Injective c ∧ IdealSheafData.stalk T x = Ideal.span (z '' (J : Set (Fin n)))

/-- Coordinates adapted to `F` and `T` at `j u`, for an open immersion `j`, are the same as
coordinates adapted to their inverse images at `u`. -/
private theorem coordsAt_comap_iff {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {Λ : Type*} (F : Λ → X.IdealSheafData) (T : X.IdealSheafData) (u : U) :
    CoordsAt (fun i => (F i).comap j) (T.comap j) u ↔ CoordsAt F T (j u) := by
  obtain ⟨e, he⟩ := exists_ringEquiv_stalk_comap j u
  have he' (I : X.IdealSheafData) :
      IdealSheafData.stalk I (j u) = (IdealSheafData.stalk (I.comap j) u).map e.symm := by
    rw [he]; exact (Ideal.map_of_equiv e).symm
  exact ⟨coords_of_ringEquiv e.symm (comapSupportEquiv j F u) _ _
      (fun _ => he' _) _ _ (he' T),
    coords_of_ringEquiv e (comapSupportEquiv j F u).symm _ _ (fun _ => he _) _ _ (he T)⟩

/-- Local coordinates adapted to a family of ideals are carried along a ring isomorphism. -/
private theorem coords0_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R]
    [IsLocalRing S] (e : R ≃+* S) {ι κ : Type*} (σ : ι ≃ κ) (IR : ι → Ideal R)
    (IS : κ → Ideal S) (hI : ∀ i, IS (σ i) = (IR i).map e)
    (h : ∃ (n : ℕ) (z : Fin n → R) (c : ι → Fin n),
      IsRegularSystemOfParameters z ∧ (∀ i, IR i = Ideal.span {z (c i)}) ∧ Function.Injective c) :
    ∃ (n : ℕ) (w : Fin n → S) (c : κ → Fin n),
      IsRegularSystemOfParameters w ∧ (∀ i, IS i = Ideal.span {w (c i)}) ∧
        Function.Injective c := by
  obtain ⟨n, z, c, hz, hc, hinj⟩ := h
  obtain ⟨n, w, c, -, hw, hc, hinj, -⟩ := coords_of_ringEquiv e σ IR IS hI ⊥ ⊥
    (Ideal.map_bot).symm ⟨n, z, c, ∅, hz, hc, hinj, by simp⟩
  exact ⟨n, w, c, hw, hc, hinj⟩

/-- Coordinates adapted to `F` at `j u`, for an open immersion `j`, are the same as coordinates
adapted to the inverse image of `F` at `u`. -/
private theorem coords0_comap_iff {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {Λ : Type*} (F : Λ → X.IdealSheafData) (u : U) :
    (∃ (n : ℕ) (z : Fin n → U.presheaf.stalk u)
      (c : {i // u ∈ ((F i).comap j).support} → Fin n),
      IsRegularSystemOfParameters z ∧
        (∀ i, IdealSheafData.stalk ((F i.1).comap j) u = Ideal.span {z (c i)}) ∧
          Function.Injective c) ↔
    (∃ (n : ℕ) (z : Fin n → X.presheaf.stalk (j u)) (c : {i // j u ∈ (F i).support} → Fin n),
      IsRegularSystemOfParameters z ∧
        (∀ i, IdealSheafData.stalk (F i.1) (j u) = Ideal.span {z (c i)}) ∧
          Function.Injective c) := by
  obtain ⟨e, he⟩ := exists_ringEquiv_stalk_comap j u
  have he' (I : X.IdealSheafData) :
      IdealSheafData.stalk I (j u) = (IdealSheafData.stalk (I.comap j) u).map e.symm := by
    rw [he]; exact (Ideal.map_of_equiv e).symm
  exact ⟨coords0_of_ringEquiv e.symm (comapSupportEquiv j F u) _ _
      (fun _ => he' _),
    coords0_of_ringEquiv e (comapSupportEquiv j F u).symm _ _ (fun _ => he _)⟩

/-- A point of an open set `O` lies in the closure of `A` iff it lies in the closure of `B`,
when `A ⊆ B` and `B ∩ O ⊆ A`. -/
private theorem mem_closure_iff_of_subset_of_inter_subset {T : Type*} [TopologicalSpace T]
    {A B O : Set T} (hO : IsOpen O) (hAB : A ⊆ B) (hBA : B ∩ O ⊆ A) {y : T} (hy : y ∈ O) :
    y ∈ closure A ↔ y ∈ closure B := by
  refine ⟨fun h => closure_mono hAB h, fun h => ?_⟩
  have : y ∈ closure (O ∩ B) := hO.inter_closure ⟨hy, h⟩
  exact closure_mono (fun t ht => hBA ⟨ht.2, ht.1⟩) this

end Coordinates

section Components

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

omit [IsLocallyNoetherian X] in
/-- The components of codimension `≥ 2` of `Z` lie in `Z`. -/
private theorem componentsOfCodimAtLeastTwo_subset (Z : Set X) :
    componentsOfCodimAtLeastTwo Z ⊆ Z := by
  intro y hy
  simp only [componentsOfCodimAtLeastTwo, Set.mem_iUnion] at hy
  obtain ⟨W, hW, -, hyW⟩ := hy
  exact hW.1.2 hyW

/-- If the members of `E` through `π x'` are cut out at `π x'` by `z (c i)`, a point of
`Spec 𝒪_{Y,x'}` lies over `E^i` iff its prime contains the image of `z (c i)`. -/
private theorem mem_support_iff_of_coords {Y : Scheme.{u}} (π : Y ⟶ X) (x' : Y) {Λ : Type*}
    (E : Λ → X.IdealSheafData) {n : ℕ} {z : Fin n → X.presheaf.stalk (π x')}
    {c : {i // π x' ∈ (E i).support} → Fin n}
    (hc : ∀ i, IdealSheafData.stalk (E i.1) (π x') = Ideal.span {z (c i)}) (i : Λ)
    (q : PrimeSpectrum (Y.presheaf.stalk x')) :
    π (Y.fromSpecStalk x' q) ∈ ((E i).support : Set X) ↔
      ∃ h : π x' ∈ (E i).support, (π.stalkMap x').hom (z (c ⟨i, h⟩)) ∈ q.asIdeal := by
  rw [apply_fromSpecStalk]
  constructor
  · intro h
    have hxi := (fromSpecStalk_specializes_self _ _).mem_closed (E i).support.isClosed h
    refine ⟨hxi, ?_⟩
    rw [fromSpecStalk_mem_support_iff_stalk_le, hc ⟨i, hxi⟩] at h
    exact h (Ideal.subset_span rfl)
  · rintro ⟨hxi, h⟩
    rwa [fromSpecStalk_mem_support_iff_stalk_le, hc ⟨i, hxi⟩, Ideal.span_le,
      Set.singleton_subset_iff]

/-- An irreducible component of `Z` through `x` is the closure of a point of `Spec 𝒪_{X,x}`
whose prime contains the stalk of `Z`. -/
private theorem exists_fromSpecStalk_of_mem_componentsOf {Z : X.IdealSheafData} {W : Set X}
    (hW : W ∈ componentsOf (Z.support : Set X)) {x : X} (hxW : x ∈ W) :
    ∃ q : PrimeSpectrum (X.presheaf.stalk x), W = closure {X.fromSpecStalk x q} ∧
      IdealSheafData.stalk Z x ≤ q.asIdeal := by
  obtain ⟨η, hηZ, rfl⟩ := Aux.exists_eq_closure_of_mem_componentsOf Z.support.isClosed hW
  obtain ⟨q, rfl⟩ := exists_fromSpecStalk_eq_of_specializes (specializes_iff_mem_closure.2 hxW)
  exact ⟨q, rfl, (fromSpecStalk_mem_support_iff_stalk_le Z x q).1 hηZ⟩

/-- If `H + ∑ᵢ D^i` has local coordinates at `x` and `Z ⊇ H`, no irreducible component of `Z`
through `x` is an irreducible component of `Supp D`. -/
private theorem notMem_componentsOf_support_of_coords {H Z : X.IdealSheafData} (hZH : H ≤ Z)
    (D : OrderedDivisor X) {x : X} {n : ℕ} {z : Fin n → X.presheaf.stalk x}
    (hz : IsRegularSystemOfParameters z)
    (c : {i // x ∈ (Fin.cons (α := fun _ => X.IdealSheafData) H D.E i).support} → Fin n)
    (hc : ∀ i, IdealSheafData.stalk ((Fin.cons (α := fun _ => X.IdealSheafData) H D.E) i.1) x =
      Ideal.span {z (c i)})
    (hinj : Function.Injective c)
    {W : Set X} (hW : W ∈ componentsOf (Z.support : Set X)) (hxW : x ∈ W) :
    W ∉ componentsOf D.support := by
  intro hWD
  have hxH : x ∈ H.support := Scheme.IdealSheafData.support_antitone hZH (hW.1.2 hxW)
  obtain ⟨q, rfl, hq⟩ := exists_fromSpecStalk_of_mem_componentsOf hW hxW
  obtain ⟨i, hi⟩ : ∃ i, X.fromSpecStalk x q ∈ ((D.E i).support : Set X) := by
    have := hWD.1.2 (subset_closure rfl)
    simpa [OrderedDivisor.support] using this
  have hxi : x ∈ (D.E i).support :=
    (fromSpecStalk_specializes_self x q).mem_closed (D.E i).support.isClosed hi
  let k0 : {j // x ∈ (Fin.cons (α := fun _ => X.IdealSheafData) H D.E j).support} :=
    ⟨0, by simpa using hxH⟩
  let ki : {j // x ∈ (Fin.cons (α := fun _ => X.IdealSheafData) H D.E j).support} :=
    ⟨i.succ, by simpa using hxi⟩
  have hne : c k0 ≠ c ki := fun h => Fin.succ_ne_zero i (congrArg Subtype.val (hinj h)).symm
  have h0 := hc k0
  have hi' := hc ki
  simp only [k0, ki, Fin.cons_zero, Fin.cons_succ] at h0 hi'
  let P : PrimeSpectrum (X.presheaf.stalk x) :=
    ⟨Ideal.span {z (c ki)}, span_singleton_isPrime_of_isRegularSystemOfParameters hz _⟩
  have hPq : P.asIdeal < q.asIdeal := by
    refine lt_of_le_of_ne ?_ fun h => ?_
    · change Ideal.span {z (c ki)} ≤ _
      rw [← hi']
      exact (fromSpecStalk_mem_support_iff_stalk_le _ x q).1 hi
    · have : z (c k0) ∈ q.asIdeal :=
        hq (MMP.Flips.ResolutionInputs.stalk_mono hZH x (h0 ▸ Ideal.subset_span rfl))
      rw [← h] at this
      exact notMem_span_singleton_of_ne_of_isRegularSystemOfParameters hz hne.symm this
  have hsub := closure_fromSpecStalk_ssubset hPq
  have hPD : closure {X.fromSpecStalk x P} ⊆ D.support := by
    refine (closure_minimal ?_ (D.E i).support.isClosed).trans
      (Set.subset_iUnion (fun j => ((D.E j).support : Set X)) i)
    exact Set.singleton_subset_iff.2 ((fromSpecStalk_mem_support_iff_stalk_le _ x P).2 hi'.le)
  exact hsub.2 (hWD.2 ⟨isIrreducible_singleton.closure, hPD⟩ hsub.1)

/-- If `H` is cut out at `x` by a member of a regular system of parameters and `Z ⊇ H`, an
irreducible component of `Z` through `x` which is no irreducible component of `H` has
codimension `≥ 2`. -/
private theorem two_le_codimension_of_mem_componentsOf {H Z : X.IdealSheafData} (hZH : H ≤ Z)
    {x : X} {n : ℕ} {z : Fin n → X.presheaf.stalk x} (hz : IsRegularSystemOfParameters z)
    (a : Fin n) (ha : IdealSheafData.stalk H x = Ideal.span {z a})
    {W : Set X} (hW : W ∈ componentsOf (Z.support : Set X)) (hxW : x ∈ W)
    (hWH : W ∉ componentsOf (H.support : Set X)) :
    2 ≤ codimension (irreducibleClosure hW.1.1) := by
  have := isRegularLocalRing_of_isRegularSystemOfParameters hz
  have := IsRegularLocalRing.isDomain (X.presheaf.stalk x)
  obtain ⟨q, rfl, hq⟩ := exists_fromSpecStalk_of_mem_componentsOf hW hxW
  let P₀ : PrimeSpectrum (X.presheaf.stalk x) :=
    ⟨Ideal.span {z a}, span_singleton_isPrime_of_isRegularSystemOfParameters hz a⟩
  let P₁ : PrimeSpectrum (X.presheaf.stalk x) := ⟨⊥, Ideal.isPrime_bot⟩
  have hHq : P₀.asIdeal ≤ q.asIdeal := by
    change Ideal.span {z a} ≤ _
    rw [← ha]
    exact (MMP.Flips.ResolutionInputs.stalk_mono hZH x).trans hq
  have h01 : P₁.asIdeal < P₀.asIdeal := by
    refine bot_lt_iff_ne_bot.2 fun h => ?_
    have : z a ∈ P₀.asIdeal := Ideal.subset_span rfl
    rw [h] at this
    exact ne_zero_of_isRegularSystemOfParameters hz a ((Submodule.mem_bot _).1 this)
  have h12 : P₀.asIdeal < q.asIdeal := by
    refine lt_of_le_of_ne hHq fun h => hWH ?_
    have hq' : q = P₀ := PrimeSpectrum.ext h.symm
    rw [hq']
    refine ⟨⟨isIrreducible_singleton.closure, closure_minimal (Set.singleton_subset_iff.2
      ((fromSpecStalk_mem_support_iff_stalk_le H x P₀).2 ha.le)) H.support.isClosed⟩, ?_⟩
    rintro W' ⟨hW'irr, hW'H⟩ hle
    obtain ⟨ξ, hξ⟩ := QuasiSober.sober hW'irr.closure isClosed_closure
    have hP₀W' : X.fromSpecStalk x P₀ ∈ closure W' := subset_closure (hle (subset_closure rfl))
    have hxW' : x ∈ closure W' :=
      (fromSpecStalk_specializes_self x P₀).mem_closed isClosed_closure hP₀W'
    obtain ⟨q', rfl⟩ := exists_fromSpecStalk_eq_of_specializes (hξ.specializes hxW')
    have h1 : P₀.asIdeal ≤ q'.asIdeal := by
      change Ideal.span {z a} ≤ _
      rw [← ha]
      exact (fromSpecStalk_mem_support_iff_stalk_le H x q').1
        (closure_minimal hW'H H.support.isClosed hξ.mem)
    have h2 : q'.asIdeal ≤ P₀.asIdeal := by
      refine (fromSpecStalk_mem_closure_iff x q' P₀).1 ?_
      rw [isGenericPoint_def.1 hξ]
      exact hP₀W'
    have : q' = P₀ := PrimeSpectrum.ext (le_antisymm h2 h1)
    rw [this] at hξ
    exact subset_closure.trans (isGenericPoint_def.1 hξ).symm.subset
  let C₁ : IrreducibleCloseds X :=
    ⟨closure {X.fromSpecStalk x P₀}, isIrreducible_singleton.closure, isClosed_closure⟩
  let C₂ : IrreducibleCloseds X :=
    ⟨closure {X.fromSpecStalk x P₁}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hl1 : irreducibleClosure hW.1.1 < C₁ := by
    change closure (closure {X.fromSpecStalk x q}) ⊂ _
    rw [closure_closure]
    exact closure_fromSpecStalk_ssubset h12
  have hl2 : C₁ < C₂ := closure_fromSpecStalk_ssubset h01
  have e2 := Order.coheight_add_one_le hl2
  unfold codimension
  calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
    _ ≤ Order.coheight C₂ + 1 + 1 := by gcongr; exact bot_le
    _ ≤ Order.coheight C₁ + 1 := by gcongr
    _ ≤ _ := Order.coheight_add_one_le hl1

end Components

section Pointwise

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X]

private theorem fromSpecStalk_mem_closure_totalTransformSet_castSucc_iff (E : OrderedDivisor X)
    {Z : X.IdealSheafData} (x' : blowUp Z) (i : Fin E.s)
    (p : PrimeSpectrum ((blowUp Z).presheaf.stalk x')) :
    (blowUp Z).fromSpecStalk x' p ∈ closure (totalTransformSet E Z (Fin.castSucc i)) ↔
      ∃ q : PrimeSpectrum ((blowUp Z).presheaf.stalk x'), q.asIdeal ≤ p.asIdeal ∧
        blowUpToBase Z ((blowUp Z).fromSpecStalk x' q) ∈ ((E.E i).support : Set X) ∧
          blowUpToBase Z ((blowUp Z).fromSpecStalk x' q) ∉
            componentsOfCodimAtLeastTwo (Z.support : Set X) := by
  have : IsNoetherian X := {}
  have : IsLocallyNoetherian (blowUp Z) :=
    LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase Z)
  simp only [totalTransformSet, Fin.snoc_castSucc]
  exact fromSpecStalk_mem_closure_preimage_diff_iff x' (E.E i).support.isClosed
    (isClosed_componentsOfCodimAtLeastTwo Z.support.isClosed) p

omit [IsLocallyNoetherian X] [CompactSpace X] in
private theorem totalTransformSet_last_subset (E : OrderedDivisor X) (Z : X.IdealSheafData) :
    totalTransformSet E Z (Fin.last E.s) ⊆ blowUpToBase Z ⁻¹' (Z.support : Set X) := by
  intro y hy
  simp only [totalTransformSet, Fin.snoc_last, Set.mem_iUnion] at hy
  obtain ⟨W, hW, -, hyW⟩ := hy
  exact hW.1.2 hyW

private theorem exists_assignment_totalTransformSet_of_notMem (E : OrderedDivisor X)
    {Z : X.IdealSheafData} (x' : blowUp Z)
    (hE : ∃ (n : ℕ) (z : Fin n → X.presheaf.stalk (blowUpToBase Z x'))
      (c : {i // blowUpToBase Z x' ∈ (E.E i).support} → Fin n),
      IsRegularSystemOfParameters z ∧
        (∀ i, IdealSheafData.stalk (E.E i.1) (blowUpToBase Z x') = Ideal.span {z (c i)}) ∧
          Function.Injective c)
    (hx : blowUpToBase Z x' ∉ (Z.support : Set X)) :
    ∃ (N : ℕ) (w : Fin N → (blowUp Z).presheaf.stalk x') (d : Fin (E.s + 1) → Option (Fin N)),
      IsRegularSystemOfParameters w ∧
      (∀ i (p : PrimeSpectrum ((blowUp Z).presheaf.stalk x')),
        (blowUp Z).fromSpecStalk x' p ∈ closure (totalTransformSet E Z i) ↔
          ∃ c, d i = some c ∧ w c ∈ p.asIdeal) ∧
      (∀ i j c, d i = some c → d j = some c → i = j) := by
  classical
  have : IsNoetherian X := {}
  have : IsLocallyNoetherian (blowUp Z) :=
    LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase Z)
  set π := blowUpToBase Z
  set x := π x'
  set φ := (π.stalkMap x').hom
  set f' := (blowUp Z).fromSpecStalk x'
  have key : ∀ p : PrimeSpectrum ((blowUp Z).presheaf.stalk x'),
      π (f' p) = X.fromSpecStalk x (PrimeSpectrum.comap φ p) :=
    fun p => apply_fromSpecStalk π x' p
  have hspec : ∀ p : PrimeSpectrum ((blowUp Z).presheaf.stalk x'), π (f' p) ⤳ x := fun p => by
    rw [key]; exact fromSpecStalk_specializes_self x _
  have hCL : ∀ (i : Fin E.s) (p : PrimeSpectrum ((blowUp Z).presheaf.stalk x')),
      f' p ∈ closure (totalTransformSet E Z (Fin.castSucc i)) ↔
        ∃ q : PrimeSpectrum ((blowUp Z).presheaf.stalk x'), q.asIdeal ≤ p.asIdeal ∧
          π (f' q) ∈ ((E.E i).support : Set X) ∧
            π (f' q) ∉ componentsOfCodimAtLeastTwo (Z.support : Set X) :=
    fun i p => fromSpecStalk_mem_closure_totalTransformSet_castSucc_iff E x' i p
  obtain ⟨n, z, c, hz, hc, hinj⟩ := hE
  have hiso : IsIso (π.stalkMap x') :=
    isIso_stalkMap_of_isIso_morphismRestrict π (isIso_blowUpToBase_restrict_compl_support Z)
      (show x' ∈ π ⁻¹ᵁ Z.support.compl from hx)
  let e := (asIso (π.stalkMap x')).commRingCatIsoToRingEquiv
  have hw : IsRegularSystemOfParameters fun i => φ (z i) :=
    isRegularSystemOfParameters_map_ringEquiv e hz
  have hnZ : ∀ q : PrimeSpectrum ((blowUp Z).presheaf.stalk x'),
      π (f' q) ∉ (Z.support : Set X) := fun q h =>
    hx ((hspec q).mem_closed Z.support.isClosed h)
  have mE := mem_support_iff_of_coords π x' E.E hc
  let dE : Fin E.s → Option (Fin n) := fun i =>
    if h : x ∈ (E.E i).support then some (c ⟨i, h⟩) else none
  let d : Fin (E.s + 1) → Option (Fin n) := Fin.snoc (α := fun _ => Option (Fin n)) dE none
  refine ⟨n, fun i => φ (z i), d, hw, ?_, ?_⟩
  · intro i p
    induction i using Fin.lastCases with
    | last =>
      simp only [d, Fin.snoc_last, reduceCtorEq, false_and, exists_false, iff_false]
      exact fun h => hnZ p (closure_minimal (totalTransformSet_last_subset E Z)
        (Z.support.isClosed.preimage π.continuous) h)
    | cast i =>
      rw [hCL]
      simp only [d, Fin.snoc_castSucc, dE]
      by_cases hxi : x ∈ (E.E i).support
      · simp only [hxi, dite_true, Option.some.injEq, exists_eq_left']
        constructor
        · rintro ⟨q, hq, h1, -⟩
          obtain ⟨_, h1⟩ := (mE i q).1 h1
          exact hq h1
        · intro h
          exact ⟨p, le_rfl, (mE i p).2 ⟨hxi, h⟩, fun h' =>
            hnZ p (componentsOfCodimAtLeastTwo_subset _ h')⟩
      · simp only [hxi, dite_false, reduceCtorEq, false_and, exists_false, iff_false]
        rintro ⟨q, -, h1, -⟩
        exact hxi ((hspec q).mem_closed (E.E i).support.isClosed h1)
  · intro i j c₀ hi hj
    induction i using Fin.lastCases with
    | last => simp [d] at hi
    | cast i =>
      induction j using Fin.lastCases with
      | last => simp [d] at hj
      | cast j =>
        simp only [d, Fin.snoc_castSucc, dE] at hi hj
        split_ifs at hi hj with hxi hxj
        congr 1
        exact congrArg Subtype.val (hinj ((Option.some_inj.1 hi).trans
          (Option.some_inj.1 hj).symm))

/-- In blow-up chart coordinates, distinct indices outside `U ∪ {m}` have distinct chart
coordinates. -/
private theorem eq_of_chart_coord_eq {R S : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [CommRing S] {n N : ℕ} {z : Fin n → R}
    (hz : IsRegularSystemOfParameters z) {φ : R →+* S} (hφ : Function.Injective φ)
    {w : Fin N → S} {m : Fin n} {i₀ : Fin N} {σ : Fin n → Fin N} {J U : Finset (Fin n)}
    (hwi₀ : w i₀ = φ (z m)) (hout : ∀ j ∉ J, w (σ j) = φ (z j))
    (hin : ∀ j ∈ J, j ≠ m → j ∉ U → φ (z j) = w (σ j) * w i₀) {a a' : Fin n} (ham : a ≠ m)
    (haU : a ∉ U) (ham' : a' ≠ m) (haU' : a' ∉ U) (hσ : σ a = σ a') : a = a' := by
  have hval : ∀ a, a ≠ m → a ∉ U → φ (z a) = w (σ a) ∨ φ (z a) = w (σ a) * w i₀ := by
    intro a ham haU
    by_cases haJ : a ∈ J
    · exact Or.inr (hin a haJ ham haU)
    · exact Or.inl (hout a haJ).symm
  by_contra hne
  rcases hval a ham haU with ha | ha <;> rcases hval a' ham' haU' with ha' | ha'
  · exact ne_of_isRegularSystemOfParameters hz hne (hφ (by rw [ha, ha', hσ]))
  · have : z a' = z a * z m := hφ (by rw [ha', map_mul, ha, hσ, hwi₀])
    exact notMem_span_singleton_of_ne_of_isRegularSystemOfParameters hz hne
      (this ▸ Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
  · have : z a = z a' * z m := hφ (by rw [ha, map_mul, ha', hσ, hwi₀])
    exact notMem_span_singleton_of_ne_of_isRegularSystemOfParameters hz (Ne.symm hne)
      (this ▸ Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
  · exact ne_of_isRegularSystemOfParameters hz hne (hφ (by rw [ha, ha', hσ]))

/-- **The entries of `π⁻¹_tot(E)` at a point of the blow-up**, from coordinates at its image only.
If at `x = π(x')` there are local coordinates in which the `E^i` through `x` are distinct
coordinate hyperplanes, and, when `x ∈ Z`, coordinates adapted to `E` and `Z`, then at `x'` there
are local coordinates `w` and an assignment `d` of at most one coordinate to every entry of
`π⁻¹_tot(E)`, distinct entries getting distinct coordinates, such that on `Spec 𝒪_{B,x'}` the
entry is `(w_{d(i)} = 0)`. This is `MMP.Resolution.exists_assignment_totalTransformSet` with
its hypotheses only at `x`. -/
private theorem exists_assignment_totalTransformSet_of_coords (E : OrderedDivisor X)
    {Z : X.IdealSheafData} (x' : blowUp Z)
    (hE : ∃ (n : ℕ) (z : Fin n → X.presheaf.stalk (blowUpToBase Z x'))
      (c : {i // blowUpToBase Z x' ∈ (E.E i).support} → Fin n),
      IsRegularSystemOfParameters z ∧
        (∀ i, IdealSheafData.stalk (E.E i.1) (blowUpToBase Z x') = Ideal.span {z (c i)}) ∧
          Function.Injective c)
    (hZ : blowUpToBase Z x' ∈ (Z.support : Set X) → ∃ (n : ℕ)
      (z : Fin n → X.presheaf.stalk (blowUpToBase Z x'))
      (c : {i // blowUpToBase Z x' ∈ (E.E i).support} → Fin n) (J : Finset (Fin n)),
      IsRegularSystemOfParameters z ∧
        (∀ i, IdealSheafData.stalk (E.E i.1) (blowUpToBase Z x') = Ideal.span {z (c i)}) ∧
          Function.Injective c ∧
          IdealSheafData.stalk Z (blowUpToBase Z x') = Ideal.span (z '' (J : Set (Fin n)))) :
    ∃ (N : ℕ) (w : Fin N → (blowUp Z).presheaf.stalk x') (d : Fin (E.s + 1) → Option (Fin N)),
      IsRegularSystemOfParameters w ∧
      (∀ i (p : PrimeSpectrum ((blowUp Z).presheaf.stalk x')),
        (blowUp Z).fromSpecStalk x' p ∈ closure (totalTransformSet E Z i) ↔
          ∃ c, d i = some c ∧ w c ∈ p.asIdeal) ∧
      (∀ i j c, d i = some c → d j = some c → i = j) := by
  classical
  by_cases hx : blowUpToBase Z x' ∈ (Z.support : Set X)
  swap
  · exact exists_assignment_totalTransformSet_of_notMem E x' hE hx
  have : IsNoetherian X := {}
  have : IsLocallyNoetherian (blowUp Z) :=
    LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase Z)
  set π := blowUpToBase Z
  set x := π x'
  set φ := (π.stalkMap x').hom
  set f' := (blowUp Z).fromSpecStalk x'
  have key : ∀ p : PrimeSpectrum ((blowUp Z).presheaf.stalk x'),
      π (f' p) = X.fromSpecStalk x (PrimeSpectrum.comap φ p) :=
    fun p => apply_fromSpecStalk π x' p
  have hspec : ∀ p : PrimeSpectrum ((blowUp Z).presheaf.stalk x'), π (f' p) ⤳ x := fun p => by
    rw [key]; exact fromSpecStalk_specializes_self x _
  have hCL : ∀ (i : Fin E.s) (p : PrimeSpectrum ((blowUp Z).presheaf.stalk x')),
      f' p ∈ closure (totalTransformSet E Z (Fin.castSucc i)) ↔
        ∃ q : PrimeSpectrum ((blowUp Z).presheaf.stalk x'), q.asIdeal ≤ p.asIdeal ∧
          π (f' q) ∈ ((E.E i).support : Set X) ∧
            π (f' q) ∉ componentsOfCodimAtLeastTwo (Z.support : Set X) :=
    fun i p => fromSpecStalk_mem_closure_totalTransformSet_castSucc_iff E x' i p
  obtain ⟨n, z, c, J, hz, hc, hinj, hJ⟩ := hZ hx
  obtain ⟨N, w, m, i₀, σ, U, hw, hmJ, hU, hwi₀, hout, hin, hunit, hσ₀⟩ :=
    exists_chart_coordinates Z x' hx hz hJ
  have hwi₀' : w i₀ = φ (z m) := hwi₀
  have hout' : ∀ j ∉ J, w (σ j) = φ (z j) := hout
  have hin' : ∀ j ∈ J, j ≠ m → j ∉ U → φ (z j) = w (σ j) * w i₀ := hin
  have hunit' : ∀ j ∈ U, ∃ u, IsUnit u ∧ φ (z j) = u * w i₀ := hunit
  have := isRegularLocalRing_of_isRegularSystemOfParameters hz
  have := IsRegularLocalRing.isDomain (X.presheaf.stalk x)
  have := isRegularLocalRing_of_isRegularSystemOfParameters hw
  have := IsRegularLocalRing.isDomain ((blowUp Z).presheaf.stalk x')
  have hφinj : Function.Injective φ := injective_stalkMap_blowUpToBase Z x'
  have hJ' : IdealSheafData.stalk Z x = (coordPrime hz J).asIdeal := hJ
  set W₀ := closure {X.fromSpecStalk x (coordPrime hz J)}
  set b : Prop := ∃ hW : IsIrreducible W₀, 2 ≤ codimension (irreducibleClosure hW)
  set b' : Prop := W₀ ∉ componentsOf E.support
  have hUJ : ∀ j ∈ U, j ∈ J ∧ j ≠ m := fun j hj =>
    ⟨(Finset.mem_erase.1 (hU hj)).2, (Finset.mem_erase.1 (hU hj)).1⟩
  have hJm : ¬ b → ∀ j ∈ J, j = m := by
    intro hnb j hj
    by_contra hjm
    exact hnb ⟨isIrreducible_singleton.closure,
      two_le_codimension_closure_coordPrime hz hj hmJ hjm _⟩
  -- membership in `Z`, `Z^{≥2}`, `E^i` and the last entry, on `Spec 𝒪_{B,x'}`
  have mZ : ∀ q : PrimeSpectrum ((blowUp Z).presheaf.stalk x'),
      (coordPrime hz J).asIdeal ≤ (PrimeSpectrum.comap φ q).asIdeal ↔ w i₀ ∈ q.asIdeal := by
    intro q
    change Ideal.span (z '' (J : Set (Fin n))) ≤ _ ↔ _
    rw [Ideal.span_le]
    constructor
    · intro h
      rw [hwi₀]
      exact h ⟨m, hmJ, rfl⟩
    · rintro h _ ⟨j, hj, rfl⟩
      change φ (z j) ∈ q.asIdeal
      by_cases hjm : j = m
      · rwa [hjm, ← hwi₀]
      by_cases hjU : j ∈ U
      · obtain ⟨u, -, hu⟩ := hunit j hjU
        rw [hu]; exact Ideal.mul_mem_left _ _ h
      · rw [hin j hj hjm hjU]; exact Ideal.mul_mem_left _ _ h
  have mZ2 : ∀ q : PrimeSpectrum ((blowUp Z).presheaf.stalk x'),
      π (f' q) ∈ componentsOfCodimAtLeastTwo (Z.support : Set X) ↔
      b ∧ w i₀ ∈ q.asIdeal := by
    intro q
    rw [key, componentsOfCodimAtLeastTwo_eq,
      fromSpecStalk_mem_biUnion_componentsOf_iff hz hJ' hx _ _, mZ]
  have mL : ∀ p : PrimeSpectrum ((blowUp Z).presheaf.stalk x'),
      f' p ∈ closure (totalTransformSet E Z (Fin.last E.s)) ↔
      b' ∧ w i₀ ∈ p.asIdeal := by
    have hLeq : totalTransformSet E Z (Fin.last E.s) = π ⁻¹'
        (⋃ (W : Set X) (_ : W ∈ componentsOf (Z.support : Set X))
          (_ : W ∉ componentsOf E.support), W) := by
      simp only [totalTransformSet, Fin.snoc_last, Set.preimage_iUnion]
      rfl
    have hLc : IsClosed (totalTransformSet E Z (Fin.last E.s)) := by
      rw [hLeq]
      exact (isClosed_biUnion_componentsOf Z.support.isClosed _).preimage π.continuous
    intro p
    rw [hLc.closure_eq, hLeq, Set.mem_preimage, key,
      fromSpecStalk_mem_biUnion_componentsOf_iff hz hJ' hx _ _, mZ]
  have mE := mem_support_iff_of_coords π x' E.E hc
  -- the coordinate hyperplane `(w_j = 0)`
  let P₀ : Fin N → PrimeSpectrum ((blowUp Z).presheaf.stalk x') := fun j =>
    ⟨Ideal.span {w j}, span_singleton_isPrime_of_isRegularSystemOfParameters hw j⟩
  have hP₀ : ∀ j, j ≠ i₀ → w i₀ ∉ (P₀ j).asIdeal := fun j hj =>
    notMem_span_singleton_of_ne_of_isRegularSystemOfParameters hw hj
  have hσinj : ∀ a a', a ≠ m → a ∉ U → a' ≠ m → a' ∉ U → σ a = σ a' → a = a' :=
    fun _ _ ham haU ham' haU' => eq_of_chart_coord_eq hz hφinj hwi₀' hout' hin' ham haU ham' haU'
  let dE : Fin E.s → Option (Fin N) := fun i =>
    if h : x ∈ (E.E i).support then
      (if c ⟨i, h⟩ = m then (if b then none else some i₀)
        else if c ⟨i, h⟩ ∈ U then none else some (σ (c ⟨i, h⟩)))
    else none
  let d : Fin (E.s + 1) → Option (Fin N) :=
    Fin.snoc (α := fun _ => Option (Fin N)) dE (if b' then some i₀ else none)
  have hdE : ∀ i c₀, dE i = some c₀ → ∃ h : x ∈ (E.E i).support,
      (c ⟨i, h⟩ = m ∧ ¬ b ∧ c₀ = i₀) ∨
        (c ⟨i, h⟩ ≠ m ∧ c ⟨i, h⟩ ∉ U ∧ c₀ = σ (c ⟨i, h⟩)) := by
    intro i c₀ h
    simp only [dE] at h
    split_ifs at h with h1 h2 h3 h4
    · exact ⟨h1, Or.inl ⟨h2, h3, (Option.some_inj.1 h).symm⟩⟩
    · exact ⟨h1, Or.inr ⟨h2, h4, (Option.some_inj.1 h).symm⟩⟩
  refine ⟨N, w, d, hw, ?_, ?_⟩
  · intro i p
    induction i using Fin.lastCases with
    | last =>
      rw [mL]
      simp only [d, Fin.snoc_last]
      split_ifs with h <;> simp [h]
    | cast i =>
      rw [hCL]
      simp only [d, Fin.snoc_castSucc, dE]
      by_cases hxi : x ∈ (E.E i).support
      · rw [dite_eq_left hxi]
        set a := c ⟨i, hxi⟩
        have hEq : ∀ q : PrimeSpectrum ((blowUp Z).presheaf.stalk x'),
            π (f' q) ∈ ((E.E i).support : Set X) ↔ φ (z a) ∈ q.asIdeal := fun q =>
          (mE i q).trans ⟨fun ⟨_, h⟩ => h, fun h => ⟨hxi, h⟩⟩
        have key2 : (∃ q : PrimeSpectrum ((blowUp Z).presheaf.stalk x'),
            q.asIdeal ≤ p.asIdeal ∧ π (f' q) ∈ ((E.E i).support : Set X) ∧
              π (f' q) ∉ componentsOfCodimAtLeastTwo (Z.support : Set X)) ↔
            ∃ q : PrimeSpectrum ((blowUp Z).presheaf.stalk x'),
              q.asIdeal ≤ p.asIdeal ∧ φ (z a) ∈ q.asIdeal ∧ ¬ (b ∧ w i₀ ∈ q.asIdeal) :=
          exists_congr fun q => and_congr_right fun _ => and_congr (hEq q) (not_congr (mZ2 q))
        rw [key2]
        by_cases ham : a = m
        · rw [ite_eq_left ham]
          have hza : φ (z a) = w i₀ := by rw [ham]; exact hwi₀'.symm
          rw [hza]
          by_cases hbb : b
          · rw [ite_eq_left hbb]
            constructor
            · rintro ⟨q, -, h1, h2⟩
              exact absurd ⟨hbb, h1⟩ h2
            · rintro ⟨c', hc', -⟩
              exact absurd hc' (by simp)
          · rw [ite_eq_right hbb]
            constructor
            · rintro ⟨q, hq, h1, -⟩; exact ⟨i₀, rfl, hq h1⟩
            · rintro ⟨c', hc', h⟩
              obtain rfl := Option.some_inj.1 hc'
              exact ⟨p, le_rfl, h, fun h' => hbb h'.1⟩
        rw [ite_eq_right ham]
        by_cases haU : a ∈ U
        · rw [ite_eq_left haU]
          constructor
          · rintro ⟨q, -, h1, h2⟩
            obtain ⟨haJ, -⟩ := hUJ a haU
            by_cases hbb : b
            · obtain ⟨u, hu, hu'⟩ := hunit' a haU
              rw [hu'] at h1
              refine absurd ⟨hbb, (q.isPrime.mem_or_mem h1).resolve_left fun h' => ?_⟩ h2
              exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h' hu)
            · exact absurd (hJm hbb a haJ) ham
          · rintro ⟨c', hc', -⟩
            exact absurd hc' (by simp)
        rw [ite_eq_right haU]
        have hσ : σ a ≠ i₀ := hσ₀ a ham haU
        constructor
        · rintro ⟨q, hq, h1, h2⟩
          refine ⟨σ a, rfl, hq ?_⟩
          by_cases haJ : a ∈ J
          · rw [hin' a haJ ham haU] at h1
            by_cases hbb : b
            · exact (q.isPrime.mem_or_mem h1).resolve_right fun h' => h2 ⟨hbb, h'⟩
            · exact absurd (hJm hbb a haJ) ham
          · rwa [hout' a haJ]
        · rintro ⟨c', hc', h⟩
          obtain rfl := Option.some_inj.1 hc'
          refine ⟨P₀ (σ a), (Ideal.span_singleton_le_iff_mem _).2 h, ?_,
            fun h' => hP₀ (σ a) hσ h'.2⟩
          by_cases haJ : a ∈ J
          · rw [hin' a haJ ham haU]
            exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
          · rw [← hout' a haJ]
            exact Ideal.subset_span rfl
      · rw [dite_eq_right hxi]
        constructor
        · rintro ⟨q, -, h1, -⟩
          exact absurd ((hspec q).mem_closed (E.E i).support.isClosed h1) hxi
        · rintro ⟨c', hc', -⟩
          exact absurd hc' (by simp)
  · -- distinct entries get distinct coordinates
    have hlast : ∀ c₀, d (Fin.last E.s) = some c₀ → b' ∧ c₀ = i₀ := by
      intro c₀ h
      simp only [d, Fin.snoc_last] at h
      split_ifs at h with hb'
      exact ⟨hb', (Option.some_inj.1 h).symm⟩
    have hcross : ∀ i c₀, dE i = some c₀ → b' → c₀ ≠ i₀ := by
      intro i c₀ hi hbb' hc₀
      obtain ⟨hxi, ⟨ham, hnb, -⟩ | ⟨ham, haU, hc₀'⟩⟩ := hdE i c₀ hi
      · have hJc : J = {c ⟨i, hxi⟩} := by
          rw [ham]
          exact Finset.eq_singleton_iff_unique_mem.2 ⟨hmJ, hJm hnb⟩
        exact hbb' (closure_coordPrime_mem_componentsOf_iUnion hz E.E c hc ⟨i, hxi⟩ hJc)
      · exact hσ₀ _ ham haU (hc₀' ▸ hc₀)
    intro i j c₀ hi hj
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => rfl
      | cast j =>
        obtain ⟨hbb', rfl⟩ := hlast _ hi
        simp only [d, Fin.snoc_castSucc] at hj
        exact absurd rfl (hcross j _ hj hbb')
    | cast i =>
      simp only [d, Fin.snoc_castSucc] at hi
      induction j using Fin.lastCases with
      | last =>
        obtain ⟨hbb', rfl⟩ := hlast _ hj
        exact absurd rfl (hcross i _ hi hbb')
      | cast j =>
        simp only [d, Fin.snoc_castSucc] at hj
        congr 1
        obtain ⟨hxi, hi'⟩ := hdE i c₀ hi
        obtain ⟨hxj, hj'⟩ := hdE j c₀ hj
        have hcij : c ⟨i, hxi⟩ = c ⟨j, hxj⟩ := by
          rcases hi' with ⟨hai, -, hci⟩ | ⟨hai, haU, hci⟩ <;>
            rcases hj' with ⟨haj, -, hcj⟩ | ⟨haj, haU', hcj⟩
          · rw [hai, haj]
          · exact absurd (hcj ▸ hci) (hσ₀ _ haj haU')
          · exact absurd (hci ▸ hcj) (hσ₀ _ hai haU)
          · exact hσinj _ _ hai haU haj haU' (hci ▸ hcj)
        exact congrArg Subtype.val (hinj hcij)

end Pointwise

section Transform

open MMP.Resolution.Kollar

/-- The complement of an effective Cartier divisor is dense. -/
private theorem dense_compl_support_of_isEffectiveCartierDivisor {Y : Scheme.{u}}
    (D : Y.IdealSheafData) (hD : Stacks.Divisors.IsEffectiveCartierDivisor D) :
    Dense (D.support.compl : Set Y) := by
  have : IsAffineHom (Scheme.Opens.ι D.support.compl) :=
    Stacks.Divisors.isAffineHom_compl_of_isEffectiveCartierDivisor D hD
  have : IsSchemeTheoreticallyDominant (Scheme.Opens.ι D.support.compl) :=
    (Scheme.Opens.isSchemeTheoreticallyDense_iff_isSchemeTheoreticallyDominant
      D.support.compl).mp
      (Stacks.Divisors.isSchemeTheoreticallyDense_compl_of_isEffectiveCartierDivisor D hD)
  have hdense := (Scheme.Opens.ι D.support.compl).denseRange
  rwa [DenseRange, Scheme.Opens.range_ι] at hdense

/-- For a closed immersion `j : S ⟶ X` of a reduced scheme and a closed subscheme `Z ⊆ X`, the
canonical lift `B_{j⁻¹Z}S ⟶ B_ZX` cuts out the closure of `π⁻¹(S ∖ Z)` with its reduced
structure. -/
private theorem ker_canonicalLift_eq_vanishingIdeal {X S : Scheme.{u}} (j : S ⟶ X)
    [IsClosedImmersion j] [IsReduced S] (Z : X.IdealSheafData) :
    (canonicalLift j Z).ker = Scheme.IdealSheafData.vanishingIdeal
        (.closure (blowUpToBase Z ⁻¹' (Set.range j \ (Z.support : Set X)))) := by
  set f := canonicalLift j Z with hf
  set T : Set (blowUp Z) := blowUpToBase Z ⁻¹' (Set.range j \ (Z.support : Set X))
  have hsq : ∀ v, blowUpToBase Z (f v) = j (blowUpToBase (Z.comap j) v) := fun v ↦ by
    rw [← Scheme.Hom.comp_apply, hf, canonicalLift_comp_blowUpToBase, Scheme.Hom.comp_apply]
  have : IsReduced (blowUp (Z.comap j)) := isReduced_blowUp (Z.comap j)
  have : IsClosedImmersion f := Bridges.isClosedImmersion_canonicalLift j Z
  set V : Set (blowUp (Z.comap j)) :=
    blowUpToBase (Z.comap j) ⁻¹' ((Z.comap j).support : Set S)ᶜ with hV
  have hVdense : closure V = Set.univ := by
    have h := dense_compl_support_of_isEffectiveCartierDivisor
      ((Z.comap j).comap (blowUpToBase (Z.comap j)))
      (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal (Z.comap j))
    have hV' : (((Z.comap j).comap (blowUpToBase (Z.comap j))).support.compl :
        Set (blowUp (Z.comap j))) = V := by
      ext v
      simp [hV, Scheme.IdealSheafData.support_comap]
    rw [← hV']
    exact h.closure_eq
  have himage : f '' V = T := by
    ext y
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨⟨_, (hsq v).symm⟩, ?_⟩
      rw [hsq v]
      simpa [hV] using hv
    · rintro ⟨⟨s, hs⟩, hyZ⟩
      have hs' : s ∉ ((Z.comap j).support : Set S) := by
        simpa [hs] using hyZ
      obtain ⟨v, hv⟩ := exists_blowUpToBase_eq_of_notMem_support (Z.comap j) hs'
      refine ⟨v, by simpa [hV, hv] using hs', ?_⟩
      have hfv : blowUpToBase Z (f v) = blowUpToBase Z y := by rw [hsq v, hv, hs]
      exact blowUpToBase_injective_of_notMem_support Z (by rwa [hfv]) hfv
  have hrange : Set.range f = closure T := by
    apply subset_antisymm
    · rw [← Set.image_univ, ← hVdense, ← himage]
      exact image_closure_subset_closure_image f.continuous
    · rw [← himage]
      exact closure_minimal (Set.image_subset_range _ _) f.isClosedEmbedding.isClosed_range
  rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range f, hrange]
  congr 1
  exact Closeds.ext (by rw [Closeds.coe_closure, Closeds.coe_closure, closure_closure])

end Transform

end MMP.Resolution.FoldAux.kr3e_snc_with_maximal_contact_preserved

namespace MMP.Resolution

open MMP.Resolution.FoldAux.kr3e_snc_with_maximal_contact_preserved in
/-- **Blowing up a centre inside a hypersurface preserves snc** (Kollár 3.103–3.104, Step 2.1).
Let `X` be a quasi-compact scheme locally of finite type over `k`, `H ⊆ X` a closed
subscheme, `D` an ordered family of closed subschemes and `V ⊆ X` open with `(H, D)|_V` an
ordered snc divisor. If `Z ⊆ H` is a closed subscheme having simple normal crossings with
`∑ᵢ D^i`, no irreducible component of which is an irreducible component of `H`, then with
`π : B_ZX → X` the blow-up, `H'` the birational transform of `H` and `D' = π⁻¹_tot D`, the
ordered divisor `(H', D')|_{π⁻¹(V)}` is an ordered snc divisor on `π⁻¹(V)`. -/
@[mmp "lem_kr3e_snc_with_maximal_contact_preserved"]
public theorem isOrderedSNC_cons_birationalTransform_totalTransform {k : Type u} [Field k]
    [CharZero k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX]
    [QuasiCompact sX] (H : X.IdealSheafData) (D : OrderedDivisor X) (V : X.Opens)
    (hV : (OrderedDivisor.comap ⟨D.s + 1, Fin.cons (α := fun _ => X.IdealSheafData) H D.E⟩
      V.ι).IsOrderedSNC (V.ι ≫ sX))
    (Z : X.IdealSheafData) (hZH : H ≤ Z) (hZD : HasSNCWith D.E Z)
    (hZc : ∀ W ∈ componentsOf (Z.support : Set X), W ∉ componentsOf (H.support : Set X)) :
    (OrderedDivisor.comap
      ⟨(D.totalTransform Z).s + 1, Fin.cons (α := fun _ => (blowUp Z).IdealSheafData)
        (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
          (blowUpToBase Z ⁻¹' ((H.support : Set X) \ (Z.support : Set X)))))
        (D.totalTransform Z).E⟩
      (blowUpToBase Z ⁻¹ᵁ V).ι).IsOrderedSNC ((blowUpToBase Z ⁻¹ᵁ V).ι ≫ blowUpToBase Z ≫ sX) := by
  classical
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : IsNoetherian X := {}
  let E' : OrderedDivisor X := ⟨D.s + 1, Fin.cons (α := fun _ => X.IdealSheafData) H D.E⟩
  have hfam : Fin.cons (α := fun _ => (V : Scheme).IdealSheafData) (H.comap V.ι)
      (D.comap V.ι).E = fun i => (E'.E i).comap V.ι := by
    funext i; exact Fin.cases rfl (fun i => rfl) i
  -- coordinates for `H + ∑ᵢ D^i` at the points of `V`
  have hcV : ∀ v : V, ∃ (n : ℕ) (z : Fin n → X.presheaf.stalk (V.ι v))
      (c : {i // V.ι v ∈ (E'.E i).support} → Fin n),
      MMP.Mori.IsRegularSystemOfParameters z ∧
        (∀ i, IdealSheafData.stalk (E'.E i.1) (V.ι v) = Ideal.span {z (c i)}) ∧
          Function.Injective c := fun v =>
    (coords0_comap_iff V.ι E'.E v).1 (hV.2.2 v)
  -- `Z` has snc with `H + ∑ᵢ D^i` on `V`
  have hV' : IsSNCFamily (V.ι ≫ sX)
      (Fin.cons (α := fun _ => (V : Scheme).IdealSheafData) (H.comap V.ι) (D.comap V.ι).E) := by
    rw [hfam]; exact hV.2
  have hZDV : HasSNCWith (D.comap V.ι).E (Z.comap V.ι) := by
    intro v hv
    rw [Scheme.IdealSheafData.support_comap] at hv
    exact (coordsAt_comap_iff V.ι D.E Z v).2 (hZD _ hv)
  have hZHV := Kollar.hasSNCWith_cons_of_hasSNCWith (V.ι ≫ sX) (D.comap V.ι) (H.comap V.ι) hV'
    (Z.comap V.ι) (Scheme.IdealSheafData.comap_mono V.ι hZH) hZDV
  rw [hfam] at hZHV
  have hcZ : ∀ v : V, V.ι v ∈ (Z.support : Set X) → CoordsAt E'.E Z (V.ι v) := by
    intro v hv
    refine (coordsAt_comap_iff V.ι E'.E Z v).1 (hZHV v ?_)
    rwa [Scheme.IdealSheafData.support_comap]
  -- every component of `Z` meeting `V` has codimension `≥ 2`
  have hHE : ∀ v : V, V.ι v ∈ (H.support : Set X) → ∃ (n : ℕ)
      (z : Fin n → X.presheaf.stalk (V.ι v)) (a : Fin n),
      MMP.Mori.IsRegularSystemOfParameters z ∧
        IdealSheafData.stalk H (V.ι v) = Ideal.span {z a} := by
    intro v hv
    obtain ⟨n, z, c, hz, hc, -⟩ := hcV v
    have h0 : V.ι v ∈ (E'.E 0).support := by simpa [E'] using hv
    exact ⟨n, z, c ⟨0, h0⟩, hz, by simpa [E'] using hc ⟨0, h0⟩⟩
  have hZ2 : ∀ v : V, V.ι v ∈ (Z.support : Set X) →
      V.ι v ∈ componentsOfCodimAtLeastTwo (Z.support : Set X) := by
    intro v hv
    obtain ⟨W, hW, hvW⟩ :=
      Set.mem_sUnion.1 ((Aux.finite_and_cover_componentsOf Z.support.isClosed).2 hv)
    obtain ⟨n, z, a, hz, ha⟩ := hHE v (Scheme.IdealSheafData.support_antitone hZH hv)
    simp only [componentsOfCodimAtLeastTwo, Set.mem_iUnion]
    exact ⟨W, hW, two_le_codimension_of_mem_componentsOf hZH hz a ha hW hvW (hZc W hW), hvW⟩
  -- components of `Z` and of the supports
  have hlast1 : ∀ W ∈ componentsOf (Z.support : Set X), W ∉ componentsOf E'.support := by
    intro W hW hWE
    have hWH : W ⊆ H.support := fun y hy => Scheme.IdealSheafData.support_antitone hZH (hW.1.2 hy)
    have hHE' : (H.support : Set X) ⊆ E'.support :=
      Set.subset_iUnion_of_subset 0 (by simp [E'])
    exact hZc W hW ⟨⟨hWE.1.1, hWH⟩, fun W' hW' hle => hWE.2 ⟨hW'.1, hW'.2.trans hHE'⟩ hle⟩
  have hlast2 : ∀ W ∈ componentsOf (Z.support : Set X), ∀ v : V, V.ι v ∈ W →
      W ∉ componentsOf D.support := by
    intro W hW v hvW
    obtain ⟨n, z, c, hz, hc, hinj⟩ := hcV v
    exact notMem_componentsOf_support_of_coords hZH D hz c hc hinj hW hvW
  -- coordinates on the blow-up over `V`
  haveI : IsLocallyNoetherian (blowUp Z) :=
    LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase Z)
  let G : Fin ((D.totalTransform Z).s + 1) → (blowUp Z).IdealSheafData :=
    Fin.cons (α := fun _ => (blowUp Z).IdealSheafData)
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
        (blowUpToBase Z ⁻¹' ((H.support : Set X) \ (Z.support : Set X)))))
      (D.totalTransform Z).E
  have hGc : ∀ x' : blowUp Z, blowUpToBase Z x' ∈ V → ∃ (N : ℕ)
      (w : Fin N → (blowUp Z).presheaf.stalk x') (c : {i // x' ∈ (G i).support} → Fin N),
      MMP.Mori.IsRegularSystemOfParameters w ∧
        (∀ i, IdealSheafData.stalk (G i.1) x' = Ideal.span {w (c i)}) ∧
          Function.Injective c := by
    intro x' hx'
    obtain ⟨v, hv⟩ : ∃ v : V, V.ι v = blowUpToBase Z x' := ⟨⟨_, hx'⟩, rfl⟩
    have hE1 := hv ▸ hcV v
    have hZ1 : blowUpToBase Z x' ∈ (Z.support : Set X) → CoordsAt E'.E Z (blowUpToBase Z x') :=
      fun h => hv ▸ hcZ v (hv ▸ h)
    obtain ⟨N, w, d, hw, h1, h2⟩ := exists_assignment_totalTransformSet_of_coords E' x' hE1 hZ1
    let T' : Fin (E'.s + 1) → Set (blowUp Z) :=
      Fin.cons (α := fun _ => Set (blowUp Z))
        (blowUpToBase Z ⁻¹' ((H.support : Set X) \ (Z.support : Set X))) (totalTransformSet D Z)
    have hGT : G = fun i => Scheme.IdealSheafData.vanishingIdeal (Closeds.closure (T' i)) := by
      funext i
      refine Fin.cases rfl (fun j => ?_) i
      simp only [G, T', Fin.cons_succ]
      exact totalTransform_E_eq D Z j
    have hO : IsOpen (blowUpToBase Z ⁻¹' (V : Set X)) :=
      V.isOpen.preimage (blowUpToBase Z).continuous
    have hT : ∀ (i : Fin (E'.s + 1)) (p : PrimeSpectrum ((blowUp Z).presheaf.stalk x')),
        (blowUp Z).fromSpecStalk x' p ∈ closure (T' i) ↔
          (blowUp Z).fromSpecStalk x' p ∈ closure (totalTransformSet E' Z i) := by
      intro i p
      have hp : (blowUp Z).fromSpecStalk x' p ∈ blowUpToBase Z ⁻¹' (V : Set X) :=
        (fromSpecStalk_specializes_self x' p).mem_open hO hx'
      refine Fin.cases ?_ (fun j => Fin.lastCases ?_ (fun l => ?_) j) i
      · have e1 : T' 0 = blowUpToBase Z ⁻¹' ((H.support : Set X) \ (Z.support : Set X)) := by
          simp only [T', Fin.cons_zero]
        have e2 : totalTransformSet E' Z 0 = blowUpToBase Z ⁻¹'
            ((H.support : Set X) \ componentsOfCodimAtLeastTwo (Z.support : Set X)) := by
          rw [← Fin.castSucc_zero]
          simp [totalTransformSet, E']
        rw [e1, e2]
        refine mem_closure_iff_of_subset_of_inter_subset hO ?_ ?_ hp
        · rintro y ⟨hy1, hy2⟩
          exact ⟨hy1, fun h => hy2 (componentsOfCodimAtLeastTwo_subset _ h)⟩
        · rintro y ⟨⟨hy1, hy2⟩, hyV⟩; exact ⟨hy1, fun h => hy2 (hZ2 ⟨_, hyV⟩ h)⟩
      · have e1 : T' (Fin.last D.s).succ = ⋃ (W : Set X) (_ : W ∈ componentsOf (Z.support : Set X))
            (_ : W ∉ componentsOf D.support), blowUpToBase Z ⁻¹' W := by
          simp only [T', Fin.cons_succ, totalTransformSet, Fin.snoc_last]
        have e2 : totalTransformSet E' Z (Fin.last D.s).succ = ⋃ (W : Set X)
            (_ : W ∈ componentsOf (Z.support : Set X))
            (_ : W ∉ componentsOf E'.support), blowUpToBase Z ⁻¹' W := by
          have h3 : ((Fin.last D.s).succ : Fin (E'.s + 1)) = Fin.last E'.s := Fin.succ_last _
          rw [h3]
          exact Fin.snoc_last (α := fun _ => Set (blowUp Z)) _ _
        rw [e1, e2]
        refine mem_closure_iff_of_subset_of_inter_subset hO ?_ ?_ hp
        · intro y hy
          simp only [Set.mem_iUnion] at hy ⊢
          obtain ⟨W, hW, -, hyW⟩ := hy
          exact ⟨W, hW, hlast1 W hW, hyW⟩
        · rintro y ⟨hy, hyV⟩
          simp only [Set.mem_iUnion] at hy ⊢
          obtain ⟨W, hW, -, hyW⟩ := hy
          exact ⟨W, hW, hlast2 W hW ⟨_, hyV⟩ hyW, hyW⟩
      · have e : totalTransformSet E' Z l.castSucc.succ = T' l.castSucc.succ := by
          have h3 : (l.castSucc.succ : Fin (E'.s + 1)) = Fin.castSucc (n := E'.s) l.succ :=
            Fin.succ_castSucc l
          rw [h3]
          unfold totalTransformSet
          rw [Fin.snoc_castSucc]
          simp [T', E', totalTransformSet]
        rw [e]
    obtain ⟨c, hc, hinj⟩ := exists_stalk_eq_of_assignment T' x' hw d
      (fun i p => (hT i p).trans (h1 i p)) h2
    rw [hGT]
    exact ⟨N, w, c, hw, hc, hinj⟩
  -- conclusion on `π⁻¹(V)`
  have hcoordU : ∀ y : ((blowUpToBase Z ⁻¹ᵁ V : (blowUp Z).Opens) : Scheme.{u}), ∃ (N : ℕ)
      (w : Fin N → ((blowUpToBase Z ⁻¹ᵁ V : (blowUp Z).Opens) : Scheme.{u}).presheaf.stalk y)
      (c : {i // y ∈ ((G i).comap (blowUpToBase Z ⁻¹ᵁ V).ι).support} → Fin N),
      MMP.Mori.IsRegularSystemOfParameters w ∧
        (∀ i, IdealSheafData.stalk ((G i.1).comap (blowUpToBase Z ⁻¹ᵁ V).ι) y =
          Ideal.span {w (c i)}) ∧ Function.Injective c := fun y =>
    (coords0_comap_iff (blowUpToBase Z ⁻¹ᵁ V).ι G y).2 (hGc _ y.2)
  have hpar : ∀ i, ∀ y ∈ ((G i).comap (blowUpToBase Z ⁻¹ᵁ V).ι).support, ∃ (m : ℕ)
      (w : Fin m → ((blowUpToBase Z ⁻¹ᵁ V : (blowUp Z).Opens) : Scheme.{u}).presheaf.stalk y)
      (j : Fin m), MMP.Mori.IsRegularSystemOfParameters w ∧
        IdealSheafData.stalk ((G i).comap (blowUpToBase Z ⁻¹ᵁ V).ι) y = Ideal.span {w j} := by
    intro i y hy
    obtain ⟨N, w, c, hw, hc, -⟩ := hcoordU y
    exact ⟨N, w, c ⟨i, hy⟩, hw, hc ⟨i, hy⟩⟩
  exact ⟨fun i => ⟨isReduced_subscheme_of_stalk_eq_span_parameter _ (hpar i),
    isEffectiveCartierDivisor_of_stalk_eq_span_parameter _ (hpar i)⟩,
    ⟨fun i => ⟨isReduced_subscheme_of_stalk_eq_span_parameter _ (hpar i),
      isPureCodimOne_support_of_stalk_eq_span_parameter _ (hpar i),
      isSmoothScheme_subscheme_of_stalk_eq_span_parameter _ _ (hpar i)⟩, hcoordU⟩⟩

open MMP.Resolution.FoldAux.kr3e_snc_with_maximal_contact_preserved in
/-- **The birational transform as the restriction of a one-step blow-up sequence.** For a reduced
closed subscheme `H ⊆ X` and a centre `Z ⊆ X`, the closed subscheme of `B_ZX` cut out by the
restriction to `H` of the one-step blow-up sequence `(X, Z)` (that is, by the canonical lift
`B_{Z·𝒪_H}H → B_ZX`) is the reduced closure of `π⁻¹(H ∖ Z)`. -/
public theorem ker_restrictHom_cons_nil_eq_vanishingIdeal {X : Scheme.{u}}
    (H : X.IdealSheafData) [IsReduced H.subscheme] (Z : X.IdealSheafData) :
    ((ClosedBlowupSequence.cons Z (.nil _)).restrictHom H).ker =
      Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
        (blowUpToBase Z ⁻¹' ((H.support : Set X) \ (Z.support : Set X)))) :=
  (ker_canonicalLift_eq_vanishingIdeal H.subschemeι Z).trans (by rw [H.range_subschemeι])

end MMP.Resolution

end

end
