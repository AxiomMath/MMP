module
public import MMP.AlgebraicGeometry.Resolution.EtaleEquivalenceBlowup
public import MMP.AlgebraicGeometry.Resolution.OrderReduction.MaxOrderControlledTransform
public import MMP.AlgebraicGeometry.Resolution.OrderReduction.MonomialStepTermination

/-!
# Going up for `D`-balanced ideals, and uniqueness of maximal contact

This file collects Kollár's results on logarithmic derivatives along smooth blow-up sequences
whose centres lie in a smooth hypersurface `S`, and their consequences.

* One blow-up (3.87.3) and the whole sequence: transforms of logarithmic derivatives
  `D^j(-log S)(K)` are contained in the logarithmic derivatives of the transform.
* The logarithmic decomposition `D^s(I_r) = ∑_j D^{s-j}(-log S_r)(T_r(D^j I, m - j))`
  (Thm. 3.88), its restriction to `S_r` (3.89.1) and the resulting description of
  `S_r ∩ cosupp(I_r, m)` (Cor. 3.89).
* Going up for `D`-balanced ideals (3.90, Thm. 3.84): a push-forward of a sequence of order
  `≥ m` on `S` is a sequence of order `m` on `X`.
* Étale equivalent sequences are equal (Thm. 3.97), and any two smooth hypersurfaces whose
  ideals lie in the maximal contact ideal are étale equivalent (Thm. 3.92).

## Main results

* `MMP.Resolution.comap_logDerivativeIdeal_le_logDerivativeIdeal_birationalTransform_mul`
* `MMP.Resolution.ClosedBlowupSequence.derivedTransform_higherLogDerivativeIdeal_le`
* `MMP.Resolution.ClosedBlowupSequence.higherDerivativeIdeal_markedTransform_eq_iSup`
* `MMP.Resolution.ClosedBlowupSequence.restrictHom_preimage_cosupport_markedTransform_eq_iInter`
* `MMP.Resolution.ClosedBlowupSequence.image_cosupport_restrict_subset_of_isDBalanced`
* `MMP.Resolution.ClosedBlowupSequence.IsPushforward.isOrderMPlainSeq_of_isDBalanced`
* `MMP.Resolution.ClosedBlowupSequence.eq_of_areEtaleEquivalent`
* `MMP.Resolution.areEtaleEquivalentHypersurfaces_of_le_maximalContactIdeal`

## References

* [J. Kollár, *Lectures on resolution of singularities*][kollar2007], 3.84–3.97
-/

@[expose] public section

/-!
## The logarithmic derivative and one smooth blow-up (Kollár, *Resolution*, (3.87.3))

Let `X` be a smooth equidimensional scheme of finite type over a field `k` of characteristic
zero, all of whose irreducible components have positive dimension, let `S ⊆ X` be a smooth
hypersurface and `Z ⊆ S` a smooth closed subscheme, with blow-up `π : X₁ = B_Z X → X`,
exceptional divisor `F = π⁻¹(Z)` and `S₁ = B_Z S ⊆ X₁` the birational transform of `S`. If `K`
is an ideal sheaf nonzero on every irreducible component with `ord_Z K ≥ a ≥ 1`, then
`𝒪((a-1)F) · π^*D(-log S)(K) ⊆ D(-log S₁)(𝒪(aF) · π^*K)`, where `𝒪(aF) · π^*K` is the ideal of
the birational transform `π⁻¹_*(K, a)`.

## Main results

* `MMP.Resolution.comap_logDerivativeIdeal_le_logDerivativeIdeal_birationalTransform_mul`

## Implementation notes

The subscheme `S₁ = B_Z S` is the image of the canonical lift `B_Z S → B_Z X` of the closed
immersion `S → X`, and its ideal sheaf is the kernel of that lift. Since `𝒪(-F)` is the invertible
ideal `I_F = π^{-1} I_Z · 𝒪_{B_Z X}`, the inclusion of fractional ideals
`𝒪((a-1)F) · π^*D(-log S)(K) ⊆ J` is stated in the equivalent integral form
`π^*D(-log S)(K) ⊆ J · I_F^{a-1}`.

## References

* [J. Kollár, *Lectures on resolution of singularities*][kollar2007], (3.87.3)
-/

section

universe u

open AlgebraicGeometry CategoryTheory MMP.Resolution

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}

namespace Proof_lem_kr3d_transform_log_derivative_one_blowup

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral
  AlgebraicGeometry.instIsProperVarietyOfIsProjectiveVariety

section Transport

variable {k R R' : Type*} [CommRing k] [CommRing R] [CommRing R'] [Algebra k R] [Algebra k R']

/-- A `k`-derivation of `R` transported along a `k`-algebra isomorphism `e : R ≃ R'`. -/
private def derivationTransport (e : R ≃ₐ[k] R') (δ : Derivation k R R) :
    Derivation k R' R' where
  toLinearMap := e.toLinearMap ∘ₗ δ.toLinearMap ∘ₗ e.symm.toLinearMap
  map_one_eq_zero' := by simp
  leibniz' a b := by
    change e (δ (e.symm (a * b))) = a • e (δ (e.symm b)) + b • e (δ (e.symm a))
    rw [map_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul, map_add,
      map_mul, map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]

private theorem map_logSpan_le (e : R ≃ₐ[k] R') (I J : Ideal R) :
    (Ideal.span {g | ∃ δ : Derivation k R R, (∀ s ∈ I, δ s ∈ I) ∧ ∃ f ∈ J, δ f = g}).map e ≤
      Ideal.span {g | ∃ δ : Derivation k R' R', (∀ s ∈ I.map e, δ s ∈ I.map e) ∧
        ∃ f ∈ J.map e, δ f = g} := by
  rw [Ideal.map_span, Ideal.span_le]
  rintro _ ⟨_, ⟨δ, hδ, f, hf, rfl⟩, rfl⟩
  refine Ideal.subset_span ⟨derivationTransport e δ, fun t ht => ?_, e f,
    Ideal.mem_map_of_mem _ hf, ?_⟩
  · obtain ⟨t', ht', rfl⟩ := (Ideal.mem_map_of_equiv e _).1 ht
    change e (δ (e.symm (e t'))) ∈ _
    rw [AlgEquiv.symm_apply_apply]
    exact Ideal.mem_map_of_mem _ (hδ _ ht')
  · change e (δ (e.symm (e f))) = e (δ f)
    rw [AlgEquiv.symm_apply_apply]

private theorem map_symm_map (e : R ≃ₐ[k] R') (I : Ideal R) : (I.map e).map e.symm = I :=
  Ideal.map_of_equiv e.toRingEquiv

private theorem map_map_symm (e : R ≃ₐ[k] R') (I : Ideal R') : (I.map e.symm).map e = I := by
  simpa using map_symm_map e.symm I

/-- The ideal generated by the logarithmic derivatives is transported by a `k`-algebra
isomorphism. -/
private theorem map_logSpan_eq (e : R ≃ₐ[k] R') (I J : Ideal R) :
    (Ideal.span {g | ∃ δ : Derivation k R R, (∀ s ∈ I, δ s ∈ I) ∧ ∃ f ∈ J, δ f = g}).map e =
      Ideal.span {g | ∃ δ : Derivation k R' R', (∀ s ∈ I.map e, δ s ∈ I.map e) ∧
        ∃ f ∈ J.map e, δ f = g} := by
  refine le_antisymm (map_logSpan_le e I J) ?_
  have h := Ideal.map_mono (f := e) (map_logSpan_le e.symm (I.map e) (J.map e))
  rw [map_symm_map, map_symm_map, map_map_symm] at h
  exact h

end Transport

section OpenImmersion

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The logarithmic derivative commutes with restriction along an open immersion. -/
private theorem comap_logDerivativeIdeal_of_isOpenImmersion {Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (j : Y ⟶ X) [IsOpenImmersion j]
    (S K : X.IdealSheafData) :
    (logDerivativeIdeal sX S K).comap j =
      logDerivativeIdeal (j ≫ sX) (S.comap j) (K.comap j) := by
  refine Scheme.IdealSheafData.ext (funext fun W' => ?_)
  let A : X.affineOpens := ⟨j ''ᵁ W'.1, W'.2.image_of_isOpenImmersion j⟩
  letI := MMP.Mori.sectionAlgebra sX A.1
  letI := MMP.Mori.sectionAlgebra (j ≫ sX) W'.1
  let e : Γ(X, A.1) ≃ₐ[k] Γ(Y, W'.1) :=
    AlgEquiv.ofRingEquiv (f := (j.appIso W'.1).commRingCatIsoToRingEquiv) (fun c => by
      change ((Scheme.ΓSpecIso _).inv ≫ sX.appLE ⊤ A.1 _ ≫ (j.appIso W'.1).hom).hom c = _
      rw [Scheme.Hom.appIso_hom', Scheme.Hom.appLE_comp_appLE]
      rfl)
  have hc : ∀ L : X.IdealSheafData, (L.comap j).ideal W' = (L.ideal A).map e := by
    intro L
    rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
    ext t
    rw [Ideal.mem_comap, Ideal.mem_map_of_equiv]
    refine ⟨fun h => ⟨e.symm t, h, e.apply_symm_apply t⟩, ?_⟩
    rintro ⟨s, hs, rfl⟩
    change e.symm (e s) ∈ _
    rwa [e.symm_apply_apply]
  rw [hc, logDerivativeIdeal_ideal, logDerivativeIdeal_ideal]
  unfold sectionLogDerivativeIdeal
  rw [hc]
  refine (map_logSpan_eq e (S.ideal A) (K.ideal A)).trans ?_
  congr 1
  ext g
  refine exists_congr fun δ => and_congr ?_ Iff.rfl
  show _ ↔ ∀ s ∈ (S.comap j).ideal W', δ s ∈ (S.comap j).ideal W'
  rw [hc S]

end OpenImmersion

section Helpers

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- An inclusion of ideal sheaves is local: if every point of `Y` has an open neighbourhood `V`
with `I(W) ≤ J(W)` for every affine open `W ⊆ V`, then `I ≤ J`. -/
private theorem le_of_forall_exists_nhds {Y : Scheme.{u}} {I J : Y.IdealSheafData}
    (H : ∀ y : Y, ∃ V : Y.Opens, y ∈ V ∧
      ∀ W : Y.affineOpens, W.1 ≤ V → I.ideal W ≤ J.ideal W) : I ≤ J := by
  choose V hyV hV using H
  refine Scheme.IdealSheafData.le_of_iSup_eq_top
    (fun W : {W : Y.affineOpens // ∃ y, W.1 ≤ V y} => W.1) ?_ fun W => ?_
  · refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨_, ⟨W, hW', rfl⟩, hyW, hW⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
      (hyV y) (V y).isOpen
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨W, hW'⟩, y, hW⟩, hyW⟩
  · obtain ⟨y, hy⟩ := W.2
    exact hV y W.1 hy

/-- Over a scheme locally of finite type over a field, an inclusion of ideal sheaves on `Y`, with
`f : Y ⟶ X`, may be checked near the fibres over the closed points of `X`. -/
private theorem le_of_forall_closedPoints {Y : Scheme.{u}} (f : Y ⟶ X)
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] {I J : Y.IdealSheafData}
    (H : ∀ p ∈ closedPoints X, ∃ U : X.Opens, p ∈ U ∧ ∀ q ∈ f ⁻¹ᵁ U, ∃ V : Y.Opens, q ∈ V ∧
      ∀ W : Y.affineOpens, W.1 ≤ V → I.ideal W ≤ J.ideal W) : I ≤ J := by
  let V : X.Opens := sSup {U | ∀ q ∈ f ⁻¹ᵁ U, ∃ V : Y.Opens, q ∈ V ∧
      ∀ W : Y.affineOpens, W.1 ≤ V → I.ideal W ≤ J.ideal W}
  have hV : V = ⊤ := Bridges.eq_top_of_closedPoints_subset sX V fun p hp => by
    obtain ⟨U, hpU, hU⟩ := H p hp
    exact (le_sSup (α := X.Opens) hU : U ≤ V) hpU
  refine le_of_forall_exists_nhds fun q => ?_
  obtain ⟨U, hU, hqU⟩ := TopologicalSpace.Opens.mem_sSup.1 (hV ▸ trivial : f q ∈ V)
  exact hU q hqU

/-- The blow-up of a smooth `k`-scheme along a smooth centre is smooth over `k`. -/
private theorem smooth_blowUpToBase_comp (sX : X ⟶ Spec (.of k)) [Smooth sX]
    (Z : X.IdealSheafData) [Smooth (Z.subschemeι ≫ sX)] : Smooth (blowUpToBase Z ≫ sX) :=
  (Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup sX Z
    ⟨isSmoothScheme_of_smooth sX, isSmoothScheme_of_smooth _⟩).1

/-- An inclusion of ideal sheaves restricted to an open `V` gives the inclusion of their
sections over every affine open contained in `V`. -/
private theorem ideal_le_of_comap_ι_le {Y : Scheme.{u}} (V : Y.Opens) {I J : Y.IdealSheafData}
    (h : I.comap V.ι ≤ J.comap V.ι) (W : Y.affineOpens) (hW : W.1 ≤ V) :
    I.ideal W ≤ J.ideal W := by
  have hW' : IsAffineOpen (V.ι ⁻¹ᵁ W.1) :=
    W.2.preimage_of_isOpenImmersion _ (by simpa using hW)
  have hh := Scheme.IdealSheafData.ideal_mono h ⟨_, hW'⟩
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Ideal.comap_le_comap_iff_of_surjective _ (ConcreteCategory.bijective_of_isIso
      ((V.ι.appIso (V.ι ⁻¹ᵁ W.1)).inv)).2] at hh
  have he : V.ι ''ᵁ (V.ι ⁻¹ᵁ W.1) = W.1 := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.2 hW
  have he' : (⟨V.ι ''ᵁ (V.ι ⁻¹ᵁ W.1), (hW'.image_of_isOpenImmersion _)⟩ : Y.affineOpens) = W :=
    Subtype.ext he
  exact he' ▸ hh

/-- The logarithmic derivative is monotone in the ideal sheaf. -/
private theorem logDerivativeIdeal_mono {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k))
    (S : Y.IdealSheafData) {I J : Y.IdealSheafData} (h : I ≤ J) :
    logDerivativeIdeal sY S I ≤ logDerivativeIdeal sY S J := by
  refine sInf_le_sInf fun K hK W => le_trans ?_ (hK W)
  letI := MMP.Mori.sectionAlgebra sY W.1
  exact Ideal.span_mono fun g ⟨δ, hδ, f, hf, hg⟩ => ⟨δ, hδ, f, h W hf, hg⟩

/-- If `y ∈ J(W)`, then `y^a ∈ (J^a)(W)`. -/
private theorem pow_mem_ideal_pow {Y : Scheme.{u}} {J : Y.IdealSheafData} {W : Y.affineOpens}
    {y : Γ(Y, W)} (hy : y ∈ J.ideal W) (a : ℕ) : y ^ a ∈ (J ^ a).ideal W := by
  induction a with
  | zero => simp [Scheme.IdealSheafData.one_eq_top]
  | succ a ih =>
    rw [pow_succ, pow_succ, Scheme.IdealSheafData.ideal_mul]
    exact Ideal.mul_mem_mul ih hy

end Helpers

/-- Off the centre: over `X ∖ Z` the blow-up is an isomorphism, `I_F = 𝒪` and `S₁` is `π^*S`,
so the inclusion reads `π^*D(-log S)(K) ⊆ D(-log π^*S)(π^*K) ⊆ D(-log S₁)(G)`. -/
private theorem off_center (sX : X ⟶ Spec (.of k)) [Smooth sX]
    (Z : X.IdealSheafData) [Smooth (Z.subschemeι ≫ sX)] {S : X.IdealSheafData}
    (hS₁ : (canonicalLift S.subschemeι Z).ker * Z.comap (blowUpToBase Z) =
      S.comap (blowUpToBase Z))
    (K : X.IdealSheafData) (a : ℕ) (W : (blowUp Z).affineOpens)
    (hW : W.1 ≤ blowUpToBase Z ⁻¹ᵁ ⟨(Z.support : Set X)ᶜ, Z.support.isClosed.isOpen_compl⟩) :
    ((logDerivativeIdeal sX S K).comap (blowUpToBase Z)).ideal W ≤
      (logDerivativeIdeal (blowUpToBase Z ≫ sX) (canonicalLift S.subschemeι Z).ker
          (MarkedIdeal.birationalTransform Z ⟨K, a⟩).I *
        Z.comap (blowUpToBase Z) ^ (a - 1)).ideal W := by
  set π := blowUpToBase Z
  set U : X.Opens := Z.support.compl
  set V : (blowUp Z).Opens := π ⁻¹ᵁ U
  have hiso := isIso_blowUpToBase_restrict_compl_support Z
  have hVπ : V.ι ≫ π = (π ∣_ U) ≫ U.ι := (morphismRestrict_ι π U).symm
  have : IsOpenImmersion (V.ι ≫ π) := hVπ ▸ inferInstance
  have hsm : Smooth (π ≫ sX) := smooth_blowUpToBase_comp sX Z
  have : LocallyOfFiniteType (π ≫ sX) := inferInstance
  have hZU : Z.comap U.ι = ⊤ := by
    rw [← Scheme.IdealSheafData.support_eq_bot_iff, Scheme.IdealSheafData.support_comap]
    ext x
    exact ⟨fun h => (x.2 h).elim, fun h => h.elim⟩
  have hF : (Z.comap π).comap V.ι = ⊤ := by
    rw [← Scheme.IdealSheafData.comap_comp, hVπ, Scheme.IdealSheafData.comap_comp, hZU,
      Scheme.IdealSheafData.comap_top]
  have hS₁V : (canonicalLift S.subschemeι Z).ker.comap V.ι = S.comap (V.ι ≫ π) := by
    have h := congrArg (fun J => Scheme.IdealSheafData.comap J V.ι) hS₁
    rwa [Stacks.IdealSheaf.comap_mul, hF, ← Scheme.IdealSheafData.one_eq_top, mul_one,
      ← Scheme.IdealSheafData.comap_comp] at h
  refine ideal_le_of_comap_ι_le V ?_ W hW
  rw [Stacks.IdealSheaf.comap_mul, Stacks.IdealSheaf.comap_pow, hF,
    ← Scheme.IdealSheafData.one_eq_top, one_pow, mul_one,
    ← Scheme.IdealSheafData.comap_comp,
    comap_logDerivativeIdeal_of_isOpenImmersion sX (V.ι ≫ π),
    comap_logDerivativeIdeal_of_isOpenImmersion (π ≫ sX) V.ι, hS₁V, Category.assoc]
  refine logDerivativeIdeal_mono _ _ ?_
  rw [Scheme.IdealSheafData.comap_comp]
  exact Scheme.IdealSheafData.comap_mono _ (le_idealColon _ _)

/-- If `y` is a non-zero-divisor and `I · (y) = (w y)`, then `I = (w)`. -/
private theorem eq_span_of_mul_span_eq {R : Type*} [CommRing R] {I : Ideal R} {y w : R}
    (hy : ∀ c : R, c * y = 0 → c = 0) (h : I * Ideal.span {y} = Ideal.span {w * y}) :
    I = Ideal.span {w} := by
  ext t
  constructor
  · intro ht
    have h1 : t * y ∈ Ideal.span {w * y} :=
      h ▸ Ideal.mul_mem_mul ht (Ideal.mem_span_singleton_self y)
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 h1
    have h2 : (r * w - t) * y = 0 := by rw [sub_mul, mul_assoc, hr, sub_self]
    rw [← sub_eq_zero.1 (hy _ h2)]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self w)
  · intro ht
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 ht
    have h1 : w * y ∈ I * Ideal.span {y} := h ▸ Ideal.mem_span_singleton_self _
    obtain ⟨t', ht', he⟩ := Ideal.mem_mul_span_singleton.1 h1
    have h2 : (t' - w) * y = 0 := by rw [sub_mul, he, sub_self]
    rw [← sub_eq_zero.1 (hy _ h2)]
    exact Ideal.mul_mem_left _ _ ht'

/-- On a smooth `k`-scheme a local coordinate is a non-zero-divisor on every affine open. -/
private theorem eq_zero_of_mul_restrictSection_eq_zero {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)}
    [Smooth sY] {U : Y.Opens} {n : ℕ} {x : Fin n → Γ(Y, U)}
    (hx : IsLocalCoordinatesOn sY U x) (W : Y.affineOpens) (h : W.1 ≤ U) (i : Fin n)
    {c : Γ(Y, W)} (hc : c * restrictSection W h (x i) = 0) : c = 0 := by
  refine TopCat.Presheaf.section_ext Y.sheaf W.1 c 0 fun p hp => ?_
  have := isRegularLocalRing_stalk_of_smooth_over_field sY p
  have := IsRegularLocalRing.isDomain (Y.presheaf.stalk p)
  have hmul := congrArg (Y.presheaf.germ W.1 p hp).hom hc
  rw [map_mul, map_zero] at hmul
  rcases mul_eq_zero.mp hmul with h0 | h0
  · rw [map_zero]
    exact h0
  · exfalso
    obtain ⟨V, hpV, hVaff, hVW, _, hV⟩ := Y.presheaf.germ_eq_of_isBasis Y.isBasis_affineOpens
      p hp hp (s := restrictSection W h (x i)) (t := 0) (by rw [map_zero]; exact h0)
    let V' : Y.affineOpens := ⟨V, hVaff⟩
    have hres : restrictSection V' (hVW.trans h) (x i) = 0 := by
      have : (Y.presheaf.map (homOfLE hVW).op).hom (restrictSection W h (x i)) =
          restrictSection V' (hVW.trans h) (x i) := by
        unfold restrictSection
        rw [← CommRingCat.comp_apply, ← Functor.map_comp]
        rfl
      rw [← this]
      simpa using hV
    let := MMP.Mori.sectionAlgebra sY V
    have : Nontrivial Γ(Y, V) := (Y.presheaf.germ V p hpV).hom.domain_nontrivial
    refine (hx.basis V' (hVW.trans h)).ne_zero i ?_
    change (hx V' (hVW.trans h)).choose i = 0
    rw [(hx V' (hVW.trans h)).choose_spec i, hres, map_zero]

open MMP.Resolution.Bridges in
/-- With local coordinates `x_0, …, x_n` on an affine open `U`, `S ∩ U = (x_0 = 0)` and
`K|_U = (f_1, …, f_s)`, the sections of `D(-log S)(K)` over `U` lie in every ideal containing
the `f_l`, the `x_0 ∂_0 f_l` and the `∂_i f_l` for `i ≠ 0` (Kollár (3.87)). -/
private theorem logDerivativeIdeal_ideal_le_of_coordinates {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [Smooth sY] {U : Y.affineOpens} {n : ℕ}
    {x : Fin (n + 1) → Γ(Y, U.1)} (hx : IsLocalCoordinatesOn sY U.1 x) {S : Y.IdealSheafData}
    (hS : ∀ (W : Y.affineOpens) (h : W.1 ≤ U.1),
      S.ideal W = Ideal.span {restrictSection W h (x 0)})
    {K : Y.IdealSheafData} {s : ℕ} (f : Fin s → Γ(Y, U.1))
    (hK : K.ideal U = Ideal.span (Set.range fun l => restrictSection U le_rfl (f l)))
    (J : Ideal Γ(Y, U.1)) (h1 : ∀ l, restrictSection U le_rfl (f l) ∈ J)
    (h2 : ∀ l, restrictSection U le_rfl (x 0) *
      partialDerivative hx U le_rfl 0 (restrictSection U le_rfl (f l)) ∈ J)
    (h3 : ∀ l (i : Fin (n + 1)), i ≠ 0 →
      partialDerivative hx U le_rfl i (restrictSection U le_rfl (f l)) ∈ J) :
    (logDerivativeIdeal sY S K).ideal U ≤ J := by
  letI := MMP.Mori.sectionAlgebra sY U.1
  obtain ⟨e, he⟩ := Kollar.exists_basis_logDerivations hx S hS U le_rfl
  have hKJ : K.ideal U ≤ J := by
    rw [hK, Ideal.span_le]
    rintro _ ⟨l, rfl⟩
    exact h1 l
  have hδf : ∀ (d : logDerivations sY S U) (l : Fin s),
      (d : Derivation k Γ(Y, U.1) Γ(Y, U.1)) (restrictSection U le_rfl (f l)) ∈ J := by
    intro d l
    have hd : d ∈ Submodule.span Γ(Y, U.1) (Set.range e) := by rw [e.span_eq]; trivial
    induction hd using Submodule.span_induction with
    | mem d hd =>
      obtain ⟨i, rfl⟩ := hd
      rw [he i]
      by_cases hi : i = 0
      · subst hi
        rw [if_pos rfl, Derivation.smul_apply, smul_eq_mul, partialDerivation_apply]
        exact h2 l
      · rw [if_neg hi, partialDerivation_apply]
        exact h3 l i hi
    | zero => simp
    | add d d' _ _ hd hd' =>
      rw [Submodule.coe_add, Derivation.add_apply]
      exact add_mem hd hd'
    | smul c d _ hd =>
      rw [Submodule.coe_smul, Derivation.smul_apply, smul_eq_mul]
      exact Ideal.mul_mem_left _ _ hd
  rw [logDerivativeIdeal_ideal]
  unfold sectionLogDerivativeIdeal
  rw [Ideal.span_le]
  rintro _ ⟨δ, hδ, t, ht, rfl⟩
  have ht' := ht
  rw [hK] at ht'
  induction ht' using Submodule.span_induction with
  | mem t ht'' =>
    obtain ⟨l, rfl⟩ := ht''
    exact hδf ⟨δ, hδ⟩ l
  | zero => simp
  | add t t' h h' iht iht' =>
    rw [map_add]
    exact add_mem (iht (hK ▸ h)) (iht' (hK ▸ h'))
  | smul c t h iht =>
    rw [smul_eq_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact add_mem (Ideal.mul_mem_left _ _ (iht (hK ▸ h)))
      (Ideal.mul_mem_right _ _ (hKJ (hK ▸ h)))

/-- Étale coordinates `x_1, …, x_n` on an affine open `U` (an étale morphism `U → 𝔸ⁿ_k`) make
`Γ(X, U)` an étale `k[X_1, …, X_n]`-algebra with `X_i ↦ x_i`. -/
private theorem exists_etale_mvPolynomial (sX : X ⟶ Spec (.of k)) {U : X.Opens}
    (hU : IsAffineOpen U) {n : ℕ} {x : Fin n → Γ(X, U)} (hx : IsLocalCoordinates sX U x) :
    letI := MMP.Mori.sectionAlgebra sX U
    ∃ φ : MvPolynomial (ULift.{u} (Fin n)) k →+* Γ(X, U), φ.Etale ∧
      (∀ i, φ (MvPolynomial.X i) = x i.down) ∧
      ∀ a, φ (MvPolynomial.C a) = algebraMap k Γ(X, U) a := by
  have : IsAffine U.toScheme := hU
  set g := AffineSpace.homOfVector (n := ULift.{u} (Fin n)) (U.ι ≫ sX)
    fun i => U.topIso.inv.hom (x i.down) with hg
  have : Etale g := hx
  have hgE : RingHom.Etale g.appTop.hom := HasRingHomProperty.appTop @Etale g inferInstance
  let E : Γ(AffineSpace (ULift.{u} (Fin n)) (Spec (.of k)), ⊤) ≃+*
      MvPolynomial (ULift.{u} (Fin n)) k :=
    ((Scheme.Γ.mapIso (AffineSpace.SpecIso (ULift.{u} (Fin n)) (.of k)).op).symm ≪≫
      Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv
  let EU := U.topIso.commRingCatIsoToRingEquiv
  let φ : MvPolynomial (ULift.{u} (Fin n)) k →+* Γ(X, U) :=
    EU.toRingHom.comp (g.appTop.hom.comp E.symm.toRingHom)
  have hEX : ∀ i, E.symm (MvPolynomial.X i) = AffineSpace.coord (Spec (.of k)) i := by
    intro i
    apply E.injective
    rw [RingEquiv.apply_symm_apply]
    change _ = (Scheme.ΓSpecIso _).hom.hom
      ((AffineSpace.SpecIso _ (.of k)).inv.appTop.hom (AffineSpace.coord (Spec (.of k)) i))
    rw [AffineSpace.SpecIso_inv_appTop_coord, ← CommRingCat.comp_apply, Iso.inv_hom_id,
      CommRingCat.id_apply]
  have hEC : ∀ a, E.symm (MvPolynomial.C a) =
      (AffineSpace (ULift.{u} (Fin n)) (Spec (.of k)) ↘ Spec (.of k)).appTop.hom
        ((Scheme.ΓSpecIso (.of k)).inv.hom a) := by
    intro a
    change (AffineSpace.SpecIso _ (.of k)).hom.appTop.hom
      ((Scheme.ΓSpecIso (.of (MvPolynomial _ k))).inv.hom (MvPolynomial.C a)) = _
    have hover : (AffineSpace.SpecIso (ULift.{u} (Fin n)) (.of k)).hom ≫
        Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial _ k)) =
        AffineSpace _ (Spec (.of k)) ↘ Spec (.of k) :=
      (Iso.eq_inv_comp _).mp (AffineSpace.SpecIso_inv_over (n := ULift.{u} (Fin n)) (.of k)).symm
    have key : (Scheme.ΓSpecIso (.of (MvPolynomial (ULift.{u} (Fin n)) k))).inv.hom
        (MvPolynomial.C a) =
        (Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial _ k))).appTop.hom
          ((Scheme.ΓSpecIso (.of k)).inv.hom a) := by
      rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]
      rfl
    rw [key, ← hover, Scheme.Hom.comp_appTop]
    rfl
  let := MMP.Mori.sectionAlgebra sX U
  refine ⟨φ, RingHom.Etale.respectsIso.1 _ _ (RingHom.Etale.respectsIso.2 _ _ hgE),
    fun i => ?_, fun a => ?_⟩
  · change U.topIso.hom.hom (g.appTop.hom (E.symm (MvPolynomial.X i))) = _
    rw [hEX, hg, AffineSpace.homOfVector_appTop_coord, ← CommRingCat.comp_apply,
      Iso.inv_hom_id, CommRingCat.id_apply]
  · change U.topIso.hom.hom (g.appTop.hom (E.symm (MvPolynomial.C a))) = _
    rw [hEC]
    have e1 : (AffineSpace (ULift.{u} (Fin n)) (Spec (.of k)) ↘ Spec (.of k)).appTop ≫
        g.appTop ≫ U.topIso.hom = sX.appLE ⊤ U le_top := by
      rw [← Category.assoc, ← Scheme.Hom.comp_appTop, hg, AffineSpace.homOfVector_over,
        Scheme.Hom.comp_appTop, Category.assoc, Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom]
      erw [← Functor.map_comp]
      rfl
    exact congrArg (fun f => f.hom ((Scheme.ΓSpecIso (.of k)).inv.hom a)) e1

/-- Étale coordinates on an affine open are local coordinates on it: their differentials form a
basis of `Ω_{𝒪(W)/k}` on every affine open `W ⊆ U`. -/
private theorem isLocalCoordinatesOn_of_isLocalCoordinates (sX : X ⟶ Spec (.of k))
    {U : X.Opens} (hU : IsAffineOpen U) {n : ℕ} {x : Fin n → Γ(X, U)}
    (hx : IsLocalCoordinates sX U x) : IsLocalCoordinatesOn sX U x := by
  let := MMP.Mori.sectionAlgebra sX U
  obtain ⟨φ, hφ, hφX, hφC⟩ := exists_etale_mvPolynomial sX hU hx
  let : Algebra (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, U) := φ.toAlgebra
  have : IsScalarTower k (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, U) :=
    IsScalarTower.of_algebraMap_eq' (by ext a; exact (hφC a).symm)
  have : Algebra.Etale (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, U) := hφ
  have hbc := KaehlerDifferential.isBaseChange_of_formallyEtale k
    (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, U)
  let b : Module.Basis (Fin n) Γ(X, U) (KaehlerDifferential k Γ(X, U)) :=
    (hbc.basis (KaehlerDifferential.mvPolynomialBasis k _)).reindex Equiv.ulift
  have hb : ∀ i, b i = KaehlerDifferential.D k Γ(X, U) (x i) := by
    intro i
    simp only [b, Module.Basis.reindex_apply, IsBaseChange.basis_apply,
      KaehlerDifferential.mvPolynomialBasis_apply, KaehlerDifferential.map_D]
    exact congrArg _ (hφX _)
  intro W h
  obtain ⟨b', hb'⟩ := MMP.Flips.ResolutionInputs.exists_basis_res sX hU W.2 h x b hb
  exact ⟨b', hb'⟩

/-- An étale coordinate on an affine open is a nonzerodivisor there. -/
private theorem mem_nonZeroDivisors_of_isLocalCoordinates (sX : X ⟶ Spec (.of k))
    {U : X.Opens} (hU : IsAffineOpen U) {n : ℕ} {x : Fin n → Γ(X, U)}
    (hx : IsLocalCoordinates sX U x) (i : Fin n) : x i ∈ nonZeroDivisors Γ(X, U) := by
  obtain ⟨φ, hφ, hφX, -⟩ := exists_etale_mvPolynomial sX hU hx
  let : Algebra (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, U) := φ.toAlgebra
  have : Algebra.Etale (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, U) := hφ
  have hreg : IsSMulRegular Γ(X, U) (MvPolynomial.X (ULift.up i) : MvPolynomial _ k) :=
    Module.Flat.isSMulRegular_of_isRegular (isRegular_iff_ne_zero.mpr (MvPolynomial.X_ne_zero _))
  have hmul : ∀ t : Γ(X, U), (MvPolynomial.X (ULift.up i) : MvPolynomial _ k) • t = x i * t :=
    fun t => by rw [Algebra.smul_def]; exact congrArg (· * t) (hφX _)
  refine mem_nonZeroDivisors_iff.mpr ⟨fun t ht => hreg ?_, fun t ht => hreg ?_⟩
  · show _ • t = _ • (0 : Γ(X, U))
    rw [hmul, hmul, mul_zero, ht]
  · show _ • t = _ • (0 : Γ(X, U))
    rw [hmul, hmul, mul_zero, mul_comm, ht]

/-- The logarithmic derivative is contained in the derivative. -/
private theorem logDerivativeIdeal_le_derivativeIdeal (sX : X ⟶ Spec (.of k))
    (S I : X.IdealSheafData) : logDerivativeIdeal sX S I ≤ derivativeIdeal sX I := by
  refine sInf_le_sInf fun K hK W => le_trans ?_ (hK W)
  letI := MMP.Mori.sectionAlgebra sX W.1
  exact Ideal.span_mono fun g ⟨δ, _, f, hf, hg⟩ => ⟨δ, f, hf, hg⟩

open MMP.Flips.ResolutionInputs MMP.Resolution.Bridges in
/-- The chart computation (Kollár (3.87.3)): on an affine open `W` of the chart `U_ℓ`, the
generators `π^*f_l`, `π^*(x_0 ∂_0 f_l)` and `π^*(∂_j f_l)` (`j ≠ 0`) of `π^*D(-log S)(K)` are
`y_ℓ^{a-1}` times elements of `D(-log S₁)(G)`. On the chart `U_0`, `S₁` is empty and the
statement is the one without logarithmic poles. -/
private theorem ideal_le_of_le_chart {Z : X.IdealSheafData} (sX : X ⟶ Spec (.of k)) [Smooth sX]
    [Smooth (blowUpToBase Z ≫ sX)]
    (c : BlowupChartData Z) (hU : IsAffineOpen c.U) {N : ℕ} (x : Fin N → Γ(X, c.U))
    (hx : IsLocalCoordinates sX c.U x) (hrn : c.r ≤ N) (hcx : ∀ i, c.x i = x (Fin.castLE hrn i))
    (ℓ : Fin c.r) {S : X.IdealSheafData}
    (hS : ∀ (V : X.affineOpens) (h : V.1 ≤ c.U),
      S.ideal V = Ideal.span {restrictSection V h (c.x ⟨0, ℓ.pos⟩)})
    (hS₁ : (canonicalLift S.subschemeι Z).ker * Z.comap (blowUpToBase Z) =
      S.comap (blowUpToBase Z))
    {K : X.IdealSheafData} {a : ℕ} (ha : 1 ≤ a)
    (hKF : K.comap (blowUpToBase Z) ≤ Z.comap (blowUpToBase Z) ^ a)
    (hD : (derivativeIdeal sX K).comap (blowUpToBase Z) ≤
      derivativeIdeal (blowUpToBase Z ≫ sX) (MarkedIdeal.birationalTransform Z ⟨K, a⟩).I *
        Z.comap (blowUpToBase Z) ^ (a - 1))
    {s : ℕ} (f : Fin s → Γ(X, c.U))
    (hf : ∀ (V : X.affineOpens) (h : V.1 ≤ c.U),
      K.ideal V = Ideal.span (Set.range fun i => (X.presheaf.map (homOfLE h).op).hom (f i)))
    (W : (blowUp Z).affineOpens) (hW : W.1 ≤ c.chart ℓ) :
    ((logDerivativeIdeal sX S K).comap (blowUpToBase Z)).ideal W ≤
      (logDerivativeIdeal (blowUpToBase Z ≫ sX) (canonicalLift S.subschemeι Z).ker
          (MarkedIdeal.birationalTransform Z ⟨K, a⟩).I *
        Z.comap (blowUpToBase Z) ^ (a - 1)).ideal W := by
  classical
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by have := ℓ.2; omega⟩
  set π := blowUpToBase Z
  set S₁ := (canonicalLift S.subschemeι Z).ker
  set G := (MarkedIdeal.birationalTransform Z ⟨K, a⟩).I
  set L₁ := logDerivativeIdeal (π ≫ sX) S₁ G
  set i0 : Fin c.r := ⟨0, ℓ.pos⟩ with hi0def
  have hi0 : Fin.castLE hrn i0 = 0 := Fin.ext rfl
  have hxOn := isLocalCoordinatesOn_of_isLocalCoordinates sX hU hx
  have hU' := isAffineOpen_chart c hU ℓ
  have hz := isLocalCoordinates_chartCoordinates c sX hU x hx hrn hcx ℓ
  have hy := isLocalCoordinatesOn_of_isLocalCoordinates (π ≫ sX) hU' hz
  have hzℓ : chartCoordinates c x ℓ (Fin.castLE hrn ℓ) = c.chartPullback ℓ (c.x ℓ) := by
    have h : ((Fin.castLE hrn ℓ : Fin (n + 1)) : ℕ) < c.r := ℓ.2
    rw [chartCoordinates, dite_eq_left h]
    have hℓ' : (⟨_, h⟩ : Fin c.r) = ℓ := Fin.ext rfl
    rw [ite_eq_left hℓ', ← hcx]
  have hreg : c.chartPullback ℓ (c.x ℓ) ∈ nonZeroDivisors Γ(blowUp Z, c.chart ℓ) :=
    hzℓ ▸ mem_nonZeroDivisors_of_isLocalCoordinates (π ≫ sX) hU' hz _
  have hregV : ∀ (V : (blowUp Z).affineOpens) (hV : V.1 ≤ c.chart ℓ) (t : Γ(blowUp Z, V)),
      t * restrictSection V hV (c.chartPullback ℓ (c.x ℓ)) = 0 → t = 0 := fun V hV t ht =>
    eq_zero_of_mul_restrictSection_eq_zero hy V hV (Fin.castLE hrn ℓ) (by rw [hzℓ]; exact ht)
  obtain ⟨g, hg, hgen⟩ := c.exists_birationalTransform_ideal_eq_span_chartTransform ℓ ⟨K, a⟩ hKF
    f hf
  have hfg : ∀ i, c.chartPullback ℓ (f i) = c.chartPullback ℓ (c.x ℓ) ^ a * g i := by
    intro i
    have hinj := IsLocalization.injective (Localization.Away (c.chartPullback ℓ (c.x ℓ)))
      ((Submonoid.powers_le).2 hreg)
    apply hinj
    have := hg i
    rw [BlowupChartData.chartTransform, Localization.mk_eq_mk',
      IsLocalization.eq_mk'_iff_mul_eq] at this
    rw [map_mul, ← this, mul_comm]
  have happ : ∀ (V : (blowUp Z).affineOpens) (hV : V.1 ≤ c.chart ℓ) (t : Γ(X, c.U)),
      (π.appLE c.U V.1 (hV.trans (c.chart_le ℓ))).hom
          (restrictSection ⟨c.U, hU⟩ le_rfl t) = restrictSection V hV (c.chartPullback ℓ t) := by
    intro V hV t
    rw [restrictSection, BlowupChartData.chartPullback, restrictSection, ← CommRingCat.comp_apply,
      ← CommRingCat.comp_apply, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  have hFV : ∀ (V : (blowUp Z).affineOpens) (hV : V.1 ≤ c.chart ℓ),
      (Z.comap π).ideal V = Ideal.span {restrictSection V hV (c.chartPullback ℓ (c.x ℓ))} := by
    intro V hV
    rw [Stacks.IdealSheaf.ideal_comap_appLE Z π ⟨c.U, hU⟩ V (hV.trans (c.chart_le ℓ)),
      c.generates ⟨c.U, hU⟩ le_rfl, Ideal.map_span]
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      change (π.appLE c.U V.1 _).hom (restrictSection ⟨c.U, hU⟩ le_rfl (c.x i)) ∈ _
      rw [happ V hV, chartPullback_eq_chartFraction_mul c ℓ i]
      exact Ideal.mem_span_singleton.2 ⟨restrictSection V hV (chartFraction c ℓ i), by
        rw [restrictSection, restrictSection, restrictSection, map_mul, mul_comm]⟩
    · rw [Ideal.span_singleton_le_iff_mem, ← happ V hV]
      exact Ideal.subset_span ⟨_, ⟨ℓ, rfl⟩, rfl⟩
  have hSV : ∀ (V : (blowUp Z).affineOpens) (hV : V.1 ≤ c.chart ℓ),
      (S.comap π).ideal V = Ideal.span {restrictSection V hV (c.chartPullback ℓ (c.x i0))} := by
    intro V hV
    rw [Stacks.IdealSheaf.ideal_comap_appLE S π ⟨c.U, hU⟩ V (hV.trans (c.chart_le ℓ)),
      hS ⟨c.U, hU⟩ le_rfl, Ideal.map_span, Set.image_singleton, happ]
  have hS₁V : ∀ (V : (blowUp Z).affineOpens) (hV : V.1 ≤ c.chart ℓ),
      S₁.ideal V * Ideal.span {restrictSection V hV (c.chartPullback ℓ (c.x ℓ))} =
        Ideal.span {restrictSection V hV (c.chartPullback ℓ (c.x i0))} := by
    intro V hV
    rw [← hFV V hV, ← hSV V hV, ← hS₁, Scheme.IdealSheafData.ideal_mul, Pi.mul_apply]
  set y := restrictSection W hW (c.chartPullback ℓ (c.x ℓ)) with hydef
  have hWU : W.1 ≤ π ⁻¹ᵁ c.U := hW.trans (c.chart_le ℓ)
  have hyF : y ∈ (Z.comap π).ideal W := by
    rw [hFV W hW]; exact Ideal.mem_span_singleton_self _
  have key : ∀ t ∈ L₁.ideal W, y ^ (a - 1) * t ∈ (L₁ * Z.comap π ^ (a - 1)).ideal W := by
    intro t ht
    rw [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply]
    exact mul_comm t _ ▸ Ideal.mul_mem_mul ht (pow_mem_ideal_pow hyF _)
  have hym : y ^ a = y ^ (a - 1) * y := by rw [← pow_succ, Nat.sub_add_cancel ha]
  by_cases hℓ : ℓ = i0
  · -- on the chart `U_0` the transform `S₁` is empty
    have hS₁W : S₁.ideal W = ⊤ := by
      have h := eq_span_of_mul_span_eq (hregV W hW) (I := S₁.ideal W) (w := 1)
        (by rw [one_mul, hS₁V W hW, ← hℓ])
      rw [h, Ideal.span_singleton_one]
    refine (Scheme.IdealSheafData.ideal_mono (Scheme.IdealSheafData.comap_mono π
      (logDerivativeIdeal_le_derivativeIdeal sX S K)) W).trans
      ((Scheme.IdealSheafData.ideal_mono hD W).trans ?_)
    rw [Scheme.IdealSheafData.ideal_mul, Scheme.IdealSheafData.ideal_mul, Pi.mul_apply,
      Pi.mul_apply]
    refine Ideal.mul_mono_left ?_
    rw [derivativeIdeal_ideal, logDerivativeIdeal_ideal]
    letI := MMP.Mori.sectionAlgebra (π ≫ sX) W.1
    unfold sectionDerivativeIdeal derivativeIdealOfRing sectionLogDerivativeIdeal
    refine Ideal.span_mono ?_
    rintro _ ⟨δ, t, ht, rfl⟩
    exact ⟨δ, fun _ _ => by rw [hS₁W]; trivial, t, ht, rfl⟩
  · -- on the chart `U_ℓ`, `ℓ ≠ 0`, `S₁ = (y_0 = 0)` with `y_0 = x_0 / x_ℓ`
    have hi0ℓ : i0 ≠ ℓ := Ne.symm hℓ
    have hz0 : ∀ (V : (blowUp Z).affineOpens) (hV : V.1 ≤ c.chart ℓ),
        restrictSection V hV (c.chartPullback ℓ (c.x i0)) =
          restrictSection V hV (chartCoordinates c x ℓ 0) *
            restrictSection V hV (c.chartPullback ℓ (c.x ℓ)) := by
      intro V hV
      rw [← hi0, chartCoordinates_castLE_of_ne c x hrn hi0ℓ,
        chartPullback_eq_chartFraction_mul c ℓ i0, restrictSection, restrictSection,
        restrictSection, map_mul]
    have hS₁' : ∀ (V : (blowUp Z).affineOpens) (hV : V.1 ≤ c.chart ℓ),
        S₁.ideal V = Ideal.span {restrictSection V hV (chartCoordinates c x ℓ 0)} :=
      fun V hV => eq_span_of_mul_span_eq (hregV V hV) (by rw [hS₁V V hV, hz0 V hV])
    letI := MMP.Mori.sectionAlgebra (π ≫ sX) W.1
    obtain ⟨eB, heB⟩ := Kollar.exists_basis_logDerivations hy S₁ hS₁' W hW
    have hlog : ∀ d ∈ logDerivations (π ≫ sX) S₁ W, ∀ t ∈ G.ideal W, d t ∈ L₁.ideal W := by
      intro d hd t ht
      rw [logDerivativeIdeal_ideal]
      exact Ideal.subset_span ⟨d, hd, t, ht, rfl⟩
    have hA : ∀ i : Fin (n + 1), i ≠ 0 → ∀ t ∈ G.ideal W,
        partialDerivative hy W hW i t ∈ L₁.ideal W := by
      intro i hi t ht
      have h := hlog _ (eB i).2 t ht
      rwa [heB i, if_neg hi, partialDerivation_apply] at h
    have hB : ∀ t ∈ G.ideal W, restrictSection W hW (chartCoordinates c x ℓ 0) *
        partialDerivative hy W hW 0 t ∈ L₁.ideal W := by
      intro t ht
      have h := hlog _ (eB 0).2 t ht
      rwa [heB 0, if_pos rfl, Derivation.smul_apply, smul_eq_mul,
        partialDerivation_apply] at h
    have hgG : ∀ l, restrictSection W hW (g l) ∈ G.ideal W := fun l => by
      rw [hgen W hW]; exact Ideal.subset_span ⟨l, rfl⟩
    have hne0 : ∀ i : Fin c.r, i ≠ i0 → Fin.castLE hrn i ≠ 0 := fun i hi h =>
      hi (Fin.ext (by simpa using congrArg Fin.val h))
    have hℓ0 := hne0 ℓ hℓ
    have hC : ∀ l, restrictSection W hW (g l) ∈ L₁.ideal W := by
      intro l
      have hyg : y * restrictSection W hW (g l) ∈ G.ideal W := Ideal.mul_mem_left _ _ (hgG l)
      have h1 := hA _ hℓ0 _ hyg
      have h2 := Ideal.mul_mem_left _ y (hA _ hℓ0 _ (hgG l))
      have hDy : partialDerivative hy W hW (Fin.castLE hrn ℓ) y = 1 := by
        rw [hydef, ← hzℓ, partialDerivative_restrictSection_coordinate, if_pos rfl]
      have he : restrictSection W hW (g l) =
          partialDerivative hy W hW (Fin.castLE hrn ℓ) (y * restrictSection W hW (g l)) -
            y * partialDerivative hy W hW (Fin.castLE hrn ℓ) (restrictSection W hW (g l)) := by
        rw [← partialDerivation_apply hy W hW _ (y * restrictSection W hW (g l)),
          Derivation.leibniz, partialDerivation_apply, partialDerivation_apply, hDy,
          smul_eq_mul, smul_eq_mul]
        ring
      rw [he]
      exact sub_mem h1 h2
    rw [Stacks.IdealSheaf.ideal_comap_appLE _ π ⟨c.U, hU⟩ W hWU, Ideal.map_le_iff_le_comap]
    refine logDerivativeIdeal_ideal_le_of_coordinates sX (U := ⟨c.U, hU⟩) hxOn
      (fun V h => by rw [hS V h, hcx, hi0]) f (hf ⟨c.U, hU⟩ le_rfl) _ (fun l => ?_)
      (fun l => ?_) (fun l j hj0 => ?_)
    · rw [Ideal.mem_comap, happ W hW, hfg, restrictSection, map_mul, map_pow, ← restrictSection,
        ← restrictSection, ← hydef, hym, mul_assoc]
      exact key _ (Ideal.mul_mem_left _ _ (hC l))
    · have e := Kollar.appLE_mul_partialDerivative_eq_pow_mul_mul_partialDerivative_of_ne c hxOn
        hrn hcx ℓ hy (hfg l) hi0ℓ ⟨c.U, hU⟩ le_rfl W hW hWU
      rw [hi0] at e
      rw [Ideal.mem_comap]
      refine (congrArg (· ∈ _) e).mpr ?_
      rw [← hydef, hym, mul_assoc]
      exact key _ (Ideal.mul_mem_left _ _ (hB _ (hgG l)))
    · rw [Ideal.mem_comap]
      by_cases hj : (j : ℕ) < c.r
      · obtain ⟨j', rfl⟩ : ∃ j' : Fin c.r, Fin.castLE hrn j' = j := ⟨⟨j, hj⟩, Fin.ext rfl⟩
        by_cases hjℓ : j' = ℓ
        · rw [hjℓ] at hj0 ⊢
          rw [Kollar.appLE_partialDerivative_self_eq_pow_mul c hxOn hrn hcx ℓ hy (by omega)
            (hfg l) ⟨c.U, hU⟩ le_rfl W hW hWU, ← hydef]
          refine key _ (add_mem (sub_mem (Ideal.mul_mem_left _ _ (hA _ hj0 _ (hgG l)))
            (sum_mem fun i _ => ?_)) (Ideal.mul_mem_left _ _ (hC l)))
          by_cases hii0 : i = i0
          · rw [hii0, hi0]
            exact hB _ (hgG l)
          · exact Ideal.mul_mem_left _ _ (hA _ (hne0 i hii0) _ (hgG l))
        · rw [Kollar.appLE_partialDerivative_eq_pow_mul_partialDerivative_of_ne c hxOn hrn hcx ℓ
            hy (by omega) (hfg l) hjℓ ⟨c.U, hU⟩ le_rfl W hW hWU, ← hydef]
          exact key _ (hA _ hj0 _ (hgG l))
      · rw [BlowupChartData.appLE_partialDerivative_eq_pow_mul_of_le c hxOn hrn hcx ℓ hy (f l) a
          (g l) (hfg l) ⟨c.U, hU⟩ le_rfl W hW hWU j (not_lt.1 hj), ← hydef, hym, mul_assoc]
        exact key _ (Ideal.mul_mem_left _ _ (hA _ hj0 _ (hgG l)))

/-- The quotient of `𝒪_{X,p}` by the stalk of a closed subscheme `D` smooth over `k` is formally
smooth over the stalk of the base. -/
private theorem formallySmooth_quotient_stalk (f : X ⟶ Spec (.of k)) (D : X.IdealSheafData)
    [Smooth (D.subschemeι ≫ f)]
    (d : D.subscheme) :
    letI := (f.stalkMap (D.subschemeι d)).hom.toAlgebra
    Algebra.FormallySmooth ((Spec (.of k)).presheaf.stalk (f (D.subschemeι d)))
      (X.presheaf.stalk (D.subschemeι d) ⧸
        AlgebraicGeometry.IdealSheafData.stalk D (D.subschemeι d)) := by
  have : LocallyOfFinitePresentation (D.subschemeι ≫ f) :=
    instLocallyOfFinitePresentationOfSmooth _
  let _ := (f.stalkMap (D.subschemeι d)).hom.toAlgebra
  let _ : Algebra ((Spec (.of k)).presheaf.stalk (f (D.subschemeι d)))
    (D.subscheme.presheaf.stalk d) := ((D.subschemeι ≫ f).stalkMap d).hom.toAlgebra
  have hfs : Algebra.FormallySmooth ((Spec (.of k)).presheaf.stalk (f (D.subschemeι d)))
      (D.subscheme.presheaf.stalk d) := by
    have : d ∈ (D.subschemeι ≫ f).smoothLocus := by
      rw [Scheme.Hom.smoothLocus_eq_top]
      trivial
    exact this
  let e : (X.presheaf.stalk (D.subschemeι d) ⧸
      AlgebraicGeometry.IdealSheafData.stalk D (D.subschemeι d)) ≃ₐ[
        (Spec (.of k)).presheaf.stalk (f (D.subschemeι d))] D.subscheme.presheaf.stalk d :=
    AlgEquiv.ofRingEquiv (f := MMP.Flips.ResolutionInputs.stalkQuotientEquiv D d) (fun a => by
      show (D.subschemeι.stalkMap d).hom ((f.stalkMap (D.subschemeι d)).hom a) =
        ((D.subschemeι ≫ f).stalkMap d).hom a
      rw [Scheme.Hom.stalkMap_comp]; rfl)
  exact Algebra.FormallySmooth.of_equiv e.symm

open MMP.Flips.ResolutionInputs MMP.Resolution.Bridges in
/-- At a point `p` of the centre: on a neighbourhood `U` of `p` with étale coordinates
`S ∩ U = (x_0 = 0)`, `Z ∩ U = (x_0 = ⋯ = x_{r-1} = 0)` and `K|_U = (f_1, …, f_s)`, the inclusion
holds near every point of `π⁻¹ U`, which the standard charts `U_ℓ` cover (Kollár (3.87.3)). -/
private theorem exists_nhds_of_mem_support
    (sX : X ⟶ Spec (.of k)) [Smooth sX]
    (Z : X.IdealSheafData) [Smooth (Z.subschemeι ≫ sX)]
    {S : X.IdealSheafData} (hS : IsSmoothHypersurface sX S) (hZS : S ≤ Z)
    {K : X.IdealSheafData} {a : ℕ} (ha : 1 ≤ a)
    (hord : OrderAlongGE K (Z.support : Set X) a)
    (hD : (derivativeIdeal sX K).comap (blowUpToBase Z) ≤
      derivativeIdeal (blowUpToBase Z ≫ sX) (MarkedIdeal.birationalTransform Z ⟨K, a⟩).I *
        Z.comap (blowUpToBase Z) ^ (a - 1))
    {p : X} (hpZ : p ∈ (Z.support : Set X)) :
    ∃ U : X.Opens, p ∈ U ∧ ∀ q ∈ blowUpToBase Z ⁻¹ᵁ U, ∃ V : (blowUp Z).Opens, q ∈ V ∧
      ∀ W : (blowUp Z).affineOpens, W.1 ≤ V →
      ((logDerivativeIdeal sX S K).comap (blowUpToBase Z)).ideal W ≤
        (logDerivativeIdeal (blowUpToBase Z ≫ sX) (canonicalLift S.subschemeι Z).ker
            (MarkedIdeal.birationalTransform Z ⟨K, a⟩).I *
          Z.comap (blowUpToBase Z) ^ (a - 1)).ideal W := by
  classical
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have := smooth_blowUpToBase_comp sX Z
  have hX : MMP.Mori.IsSmoothScheme sX := isSmoothScheme_of_smooth sX
  have hS₁ := (ker_canonicalLift_subschemeι_mul_comap_eq_comap sX hX S Z hS
    (isSmoothScheme_of_smooth _) hZS).2.1
  have hKF : K.comap (blowUpToBase Z) ≤ Z.comap (blowUpToBase Z) ^ a :=
    comap_le_comap_pow_of_stalk_le _ _ _ _ (stalk_le_pow_of_orderAlongGE sX
      (isSmoothScheme_of_smooth sX) Z (isSmoothScheme_of_smooth _) K a hord)
  have hdata : ∀ (T : X.IdealSheafData) (q : X), MMP.Mori.IsSmoothScheme (T.subschemeι ≫ sX) →
      q ∈ T.support →
      IsRegularLocalRing (X.presheaf.stalk q ⧸ IdealSheafData.stalk T q) ∧
      (letI := (sX.stalkMap q).hom.toAlgebra;
        Algebra.FormallySmooth ((Spec (.of k)).presheaf.stalk (sX q))
          (X.presheaf.stalk q ⧸ IdealSheafData.stalk T q)) ∧
      ∃ r : ℕ, ringKrullDim (X.presheaf.stalk q) =
        ringKrullDim (X.presheaf.stalk q ⧸ IdealSheafData.stalk T q) + r := by
    intro T q hT hq
    have hreg := isRegularLocalRing_quotient_stalk sX T hT hq
    refine ⟨hreg, ?_, ?_⟩
    · obtain ⟨z, rfl⟩ : ∃ z, T.subschemeι z = q := by
        rwa [← SetLike.mem_coe, ← T.range_subschemeι] at hq
      have : Smooth (T.subschemeι ≫ sX) := hT.smooth
      exact formallySmooth_quotient_stalk sX T z
    · have : IsRegularLocalRing (X.presheaf.stalk q) :=
        (smooth_iff_forall_isRegularLocalRing_stalk sX).mp inferInstance q
      have d1 := IsRegularLocalRing.spanFinrank_maximalIdeal (R := X.presheaf.stalk q)
      have d2 := IsRegularLocalRing.spanFinrank_maximalIdeal
        (R := X.presheaf.stalk q ⧸ IdealSheafData.stalk T q)
      have hle := ringKrullDim_quotient_le (IdealSheafData.stalk T q)
      rw [← d1, ← d2] at hle
      have hle'' : Submodule.spanFinrank (IsLocalRing.maximalIdeal
          (X.presheaf.stalk q ⧸ IdealSheafData.stalk T q)) ≤
          Submodule.spanFinrank (IsLocalRing.maximalIdeal (X.presheaf.stalk q)) := by
        exact_mod_cast (WithBot.coe_le_coe.mp hle)
      refine ⟨Submodule.spanFinrank (IsLocalRing.maximalIdeal (X.presheaf.stalk q)) -
        Submodule.spanFinrank (IsLocalRing.maximalIdeal
          (X.presheaf.stalk q ⧸ IdealSheafData.stalk T q)), ?_⟩
      rw [← d1, ← d2, ← Nat.cast_add, Nat.add_sub_cancel' hle'']
  have hpS : p ∈ S.support := Scheme.IdealSheafData.support_antitone hZS hpZ
  have hSreg := isRegularLocalRing_quotient_stalk sX S hS.1 hpS
  have hs : ringKrullDim (X.presheaf.stalk p) =
      ringKrullDim (X.presheaf.stalk p ⧸ IdealSheafData.stalk S p) + ((1 : ℕ) : WithBot ℕ∞) := by
    have : IsRegularLocalRing (X.presheaf.stalk p) :=
      (smooth_iff_forall_isRegularLocalRing_stalk sX).mp inferInstance p
    have : IsDomain (X.presheaf.stalk p ⧸ IdealSheafData.stalk S p) :=
      IsRegularLocalRing.isDomain _
    have : (IdealSheafData.stalk S p).IsPrime := (Ideal.Quotient.isDomain_iff_prime _).mp this
    have hht := height_stalk_eq_one_of_isPureCodimOne S hS.2 (x := p)
    rw [← ringKrullDim_quotient_add_one_of_height_eq_one _ hht, Nat.cast_one]
  obtain ⟨hZreg, hZsm, r, hr⟩ := hdata Z p (isSmoothScheme_of_smooth _) hpZ
  obtain ⟨hrN, U, hU, hpU, x, hx, hcutS, hcutZ⟩ :=
    exists_isLocalCoordinates_isCutOutByFirst_of_stalk sX S Z hZS p hSreg hZreg hZsm hs hr
  refine ⟨U, hpU, fun q hq => ?_⟩
  let cd : BlowupChartData Z :=
    { U := U
      r := r
      x := fun i => x (Fin.castLE hrN i)
      generates := fun V hV => by
        rw [hcutZ V hV]
        congr 1
        ext s
        constructor
        · rintro ⟨i, hi, rfl⟩
          exact ⟨⟨i, hi⟩, rfl⟩
        · rintro ⟨j, rfl⟩
          exact ⟨Fin.castLE hrN j, j.2, rfl⟩ }
  -- `K(U)` is finitely generated, and its generators generate `K` on every affine `V ⊆ U`.
  haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  obtain ⟨s, f, hfU⟩ := Submodule.fg_iff_exists_fin_generating_family.1
    (IsNoetherian.noetherian (K.ideal ⟨U, hU⟩))
  have hf : ∀ (V : X.affineOpens) (h : V.1 ≤ cd.U),
      K.ideal V = Ideal.span (Set.range fun i => (X.presheaf.map (homOfLE h).op).hom (f i)) := by
    intro V h
    rw [← K.map_ideal (U := V) (V := ⟨U, hU⟩) h, ← hfU, Ideal.map_span, ← Set.range_comp]
    rfl
  have hqU : q ∈ blowUpToBase Z ⁻¹ᵁ cd.U := hq
  rw [← iSup_chart_eq_preimage cd] at hqU
  obtain ⟨ℓ, hqℓ⟩ := TopologicalSpace.Opens.mem_iSup.mp hqU
  have hS' : ∀ (V : X.affineOpens) (h : V.1 ≤ cd.U),
      S.ideal V = Ideal.span {restrictSection V h (cd.x ⟨0, ℓ.pos⟩)} := by
    intro V h
    rw [hcutS V h]
    congr 1
    ext t
    simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, hi, rfl⟩
      have : i = Fin.castLE hrN ⟨0, ℓ.pos⟩ := Fin.ext (Nat.lt_one_iff.mp hi)
      rw [this]
      rfl
    · rintro rfl
      exact ⟨Fin.castLE hrN ⟨0, ℓ.pos⟩, by simp, rfl⟩
  exact ⟨cd.chart ℓ, hqℓ, ideal_le_of_le_chart sX cd hU x hx hrN (fun _ => rfl) ℓ hS' hS₁ ha
    hKF hD f hf⟩

end Proof_lem_kr3d_transform_log_derivative_one_blowup

namespace MMP.Resolution

open Proof_lem_kr3d_transform_log_derivative_one_blowup in
/-- **Kollár (3.87.3), one blow-up.** Let `X` be smooth, equidimensional and of finite type over a
field `k` of characteristic zero, with irreducible components of positive dimension, `S ⊆ X` a
smooth hypersurface, `Z ⊆ S` a smooth closed subscheme with blow-up `π = blowUpToBase Z`,
exceptional ideal `I_F = Z.comap π`, and `S₁ ⊆ B_Z X` the birational transform of `S`, cut out by
the kernel of `canonicalLift S.subschemeι Z`. Let `K` be an ideal sheaf nonzero at the generic
points of `X` with `ord_Z K ≥ a ≥ 1`. Then `π^*D(-log S)(K) ⊆ D(-log S₁)(G) · I_F^{a-1}`,
i.e. `𝒪((a-1)F) · π^*D(-log S)(K) ⊆ D(-log S₁)(G)`, where `G = 𝒪(aF) · π^*K` is the ideal of the
birational transform of the marked ideal `(K, a)`. -/
@[mmp "lem_kr3d_transform_log_derivative_one_blowup"]
public theorem comap_logDerivativeIdeal_le_logDerivativeIdeal_birationalTransform_mul
    {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [Smooth sX] [QuasiCompact sX]
    (hX : TopologicalSpace.Equidimensional X)
    (hdim : ∀ C ∈ irreducibleComponents X, 0 < topologicalKrullDim C)
    {S : X.IdealSheafData} (hS : IsSmoothHypersurface sX S)
    (Z : X.IdealSheafData) (hZ : Smooth (Z.subschemeι ≫ sX)) (hZS : S ≤ Z)
    {K : X.IdealSheafData} (hK : IsNonzeroAtGenericPoints K) {a : ℕ} (ha : 1 ≤ a)
    (hord : OrderAlongGE K (Z.support : Set X) a) :
    (logDerivativeIdeal sX S K).comap (blowUpToBase Z) ≤
      logDerivativeIdeal (blowUpToBase Z ≫ sX) (canonicalLift S.subschemeι Z).ker
          (MarkedIdeal.birationalTransform Z ⟨K, a⟩).I *
        Z.comap (blowUpToBase Z) ^ (a - 1) := by
  have := hZ
  have hD := comap_derivativeIdeal_le_derivativeIdeal_birationalTransform_mul sX hX hdim Z hZ hK
    ha hord
  have hS₁ := (ker_canonicalLift_subschemeι_mul_comap_eq_comap sX (isSmoothScheme_of_smooth sX)
    S Z hS (isSmoothScheme_of_smooth _) hZS).2.1
  refine le_of_forall_closedPoints (blowUpToBase Z) sX fun p _ => ?_
  by_cases hpZ : p ∈ (Z.support : Set X)
  · exact exists_nhds_of_mem_support sX Z hS hZS ha hord hD hpZ
  · exact ⟨_, hpZ, fun q hq => ⟨_, hq, off_center sX Z hS₁ K a⟩⟩

end MMP.Resolution

end

/-!
## Transforms of logarithmic derivatives along a blow-up sequence (Kollár (3.87.3))

Let `X` be a smooth equidimensional scheme of finite type over a field `k` of characteristic
`0`, with every irreducible component of positive dimension, let `(K, a)` be a marked ideal sheaf
with `K` nonzero on every irreducible component, and let `Π = (X_i, Z_i)_{i ≤ r}` be a smooth
blow-up sequence of order `≥ a` starting with `(X, K, a)`, with marked ideals `(K_i, a)`. Let
`S ⊆ X` be a smooth hypersurface whose restriction `(S_i)` contains every centre, `Z_i ⊆ S_i`.
Then for every `0 ≤ j ≤ a` the transform `T_r(D^j(-log S)(K), a - j)` is an ideal sheaf on `X_r`
contained in `D^j(-log S_r)(K_r)`; that is,
`Π⁻¹_*(D^j(-log S)(K, a)) ⊆ D^j(-log S_r)(Π⁻¹_*(K, a))`.

## Main results

* `MMP.Resolution.ClosedBlowupSequence.derivedTransform_higherLogDerivativeIdeal_le`

## Implementation notes

The hypersurface `S_r ⊆ X_r` is the closed subscheme cut out by the kernel of the morphism
`Π.restrictHom S : S_r → X_r` of the restriction `Π|_S`, and the containment of the centres in
the `S_i` is `Π.CentersContainedIn S.subschemeι`, stated scheme-theoretically on ideal sheaves.
The transform `T_r(·, a - j)` is `derivedTransform`, whose value `some J` records that it is an
ideal sheaf `J`.

## References

* [J. Kollár, *Lectures on resolution of singularities*, (3.87.3)][kollar2007]
-/

section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Resolution

namespace Proof_lem_kr3d_transform_log_derivative_inclusion

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

section Ideals

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))

/-- The first derivative is monotone. -/
private theorem derivativeIdeal_mono {I J : X.IdealSheafData} (h : I ≤ J) :
    derivativeIdeal sX I ≤ derivativeIdeal sX J := by
  refine sInf_le_sInf fun K hK W => le_trans ?_ (hK W)
  letI := MMP.Mori.sectionAlgebra sX W.1
  exact Ideal.span_mono fun g ⟨δ, f, hf, hg⟩ => ⟨δ, f, h W hf, hg⟩

/-- The logarithmic derivative is contained in the derivative. -/
private theorem logDerivativeIdeal_le_derivativeIdeal (S I : X.IdealSheafData) :
    logDerivativeIdeal sX S I ≤ derivativeIdeal sX I := by
  refine sInf_le_sInf fun K hK W => le_trans ?_ (hK W)
  letI := MMP.Mori.sectionAlgebra sX W.1
  exact Ideal.span_mono fun g ⟨δ, _, f, hf, hg⟩ => ⟨δ, f, hf, hg⟩

/-- `D^j(-log S)(I) ⊆ D^j(I)`. -/
private theorem higherLogDerivativeIdeal_le_higherDerivativeIdeal (S I : X.IdealSheafData)
    (j : ℕ) : higherLogDerivativeIdeal sX S I j ≤ higherDerivativeIdeal sX I j := by
  induction j with
  | zero => exact (higherDerivativeIdeal_zero ..).ge
  | succ j ih =>
    rw [higherLogDerivativeIdeal_succ, higherDerivativeIdeal_succ]
    exact (logDerivativeIdeal_le_derivativeIdeal sX S _).trans (derivativeIdeal_mono sX ih)

/-- `𝒪(-S) · D(A) ⊆ D(-log S)(A)`: for `s ∈ 𝒪(-S)` and any derivation `δ`, `s δ` is
logarithmic along `S`. -/
private theorem mul_derivativeIdeal_le_logDerivativeIdeal [LocallyOfFiniteType sX]
    (S A : X.IdealSheafData) : S * derivativeIdeal sX A ≤ logDerivativeIdeal sX S A := by
  refine le_sInf fun J hJ W => ?_
  rw [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, derivativeIdeal_ideal]
  letI := MMP.Mori.sectionAlgebra sX W.1
  refine Ideal.mul_le.2 fun s hs g hg => ?_
  refine Submodule.span_induction (p := fun g _ => s * g ∈ J.ideal W) ?_ ?_ ?_ ?_ hg
  · rintro _ ⟨δ, f, hf, rfl⟩
    refine hJ W (Ideal.subset_span ⟨s • δ, fun t _ => ?_, f, hf, by simp⟩)
    rw [Derivation.smul_apply, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ hs
  · simp
  · intro x y _ _ hx hy
    rw [mul_add]
    exact add_mem hx hy
  · intro c x _ hx
    rw [smul_eq_mul, mul_left_comm]
    exact Ideal.mul_mem_left _ c hx

/-- A closed subset of pure codimension one contains no generic point of an irreducible
component. -/
private theorem notMem_support_of_isPureCodimOne {S : X.IdealSheafData}
    (hS : MMP.Mori.IsPureCodimOne S.support) {η : X}
    (hη : closure ({η} : Set X) ∈ irreducibleComponents X) : η ∉ S.support := by
  intro hηS
  let W : IrreducibleCloseds X :=
    ⟨closure {η}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hWS : (W : Set X) ⊆ S.support :=
    closure_minimal (Set.singleton_subset_iff.2 hηS) S.support.isClosed
  have hmax : ∀ W' : IrreducibleCloseds X, W ≤ W' → W' ≤ W := fun W' hle =>
    hη.2 W'.isIrreducible hle
  have h1 := hS W ⟨hWS, fun W' _ hle => hmax W' hle⟩
  have h0 : codimension W = 0 := Order.coheight_eq_zero.mpr fun W' hle => hmax W' hle
  exact zero_ne_one (h0 ▸ h1)

/-- On a smooth scheme all of whose components have positive dimension, the logarithmic
derivative along a smooth hypersurface of an ideal nonzero at the generic points is nonzero at
the generic points. -/
private theorem isNonzeroAtGenericPoints_logDerivativeIdeal [Smooth sX]
    (hdim : ∀ Z ∈ irreducibleComponents X, 0 < topologicalKrullDim Z)
    {S : X.IdealSheafData} (hS : IsSmoothHypersurface sX S) {A : X.IdealSheafData}
    (hA : IsNonzeroAtGenericPoints A) : IsNonzeroAtGenericPoints (logDerivativeIdeal sX S A) := by
  intro η hη hbot
  have hle : S * A ≤ logDerivativeIdeal sX S A :=
    (mul_le_mul' le_rfl (le_derivativeIdeal sX hdim A)).trans
      (mul_derivativeIdeal_le_logDerivativeIdeal sX S A)
  have h := stalk_le_stalk_of_le hle η
  rw [hbot, Aux.stalk_mul, (IdealSheafData.stalk_eq_top_iff_notMem_support S η).2
    (notMem_support_of_isPureCodimOne hS.2 hη), Ideal.top_mul] at h
  exact hA η hη (eq_bot_iff.2 h)

private theorem isNonzeroAtGenericPoints_higherLogDerivativeIdeal [Smooth sX]
    (hdim : ∀ Z ∈ irreducibleComponents X, 0 < topologicalKrullDim Z)
    {S : X.IdealSheafData} (hS : IsSmoothHypersurface sX S) {A : X.IdealSheafData}
    (hA : IsNonzeroAtGenericPoints A) (j : ℕ) :
    IsNonzeroAtGenericPoints (higherLogDerivativeIdeal sX S A j) := by
  induction j with
  | zero => exact hA
  | succ j ih =>
    rw [higherLogDerivativeIdeal_succ]
    exact isNonzeroAtGenericPoints_logDerivativeIdeal sX hdim hS ih

end Ideals

/-- Multiplication by an effective Cartier divisor is cancellative on inclusions. -/
private theorem le_of_mul_le_mul_right {X : Scheme.{u}} {A B L : X.IdealSheafData}
    (hL : Stacks.Divisors.IsEffectiveCartierDivisor L) (h : A * L ≤ B * L) : A ≤ B := by
  choose U hU hxU b hb hgen using
    fun x : X => Stacks.Divisors.exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor L hL x
  refine Scheme.IdealSheafData.le_of_iSup_eq_top (fun x : X => (⟨U x, hU x⟩ : X.affineOpens))
    (top_unique fun z _ => TopologicalSpace.Opens.mem_iSup.2 ⟨z, hxU z⟩) fun x a ha => ?_
  have h' : A.ideal ⟨U x, hU x⟩ * L.ideal ⟨U x, hU x⟩ ≤
      B.ideal ⟨U x, hU x⟩ * L.ideal ⟨U x, hU x⟩ := h ⟨U x, hU x⟩
  rw [hgen x] at h'
  obtain ⟨c, hc, hcb⟩ := Ideal.mem_mul_span_singleton.1
    (h' (Ideal.mem_mul_span_singleton.2 ⟨a, ha, rfl⟩))
  exact (hb x).right hcb ▸ hc

/-- The kernel of a canonical lift does not change under precomposition with an isomorphism. -/
private theorem ker_canonicalLift_comp_of_isIso {X W Y : Scheme.{u}} (h : Y ⟶ W) [IsIso h]
    (g : W ⟶ X) (Z : X.IdealSheafData) :
    (canonicalLift (h ≫ g) Z).ker = (canonicalLift g Z).ker := by
  have e := ClosedBlowupSequence.canonicalLift_comp_canonicalLift g h Z
  have : IsIso (canonicalLift h (Z.comap g)) := Kollar.isIso_canonicalLift h _
  rw [← Scheme.Hom.ker_comp_of_isIso
    (eqToHom (congrArg blowUp (Scheme.IdealSheafData.comap_comp Z h g).symm))
    (canonicalLift (h ≫ g) Z), ← e,
    Scheme.Hom.ker_comp_of_isIso]

/-- The kernel of the canonical lift of a closed immersion `i` is that of the canonical lift of
the closed subscheme cut out by `i`. -/
private theorem ker_canonicalLift_eq_subschemeι {X Y : Scheme.{u}} (i : Y ⟶ X)
    [IsClosedImmersion i] (Z : X.IdealSheafData) :
    (canonicalLift i Z).ker = (canonicalLift i.ker.subschemeι Z).ker := by
  have := ker_canonicalLift_comp_of_isIso i.toImage i.imageι Z
  rwa [Scheme.Hom.toImage_imageι] at this

/-- The blow-up morphism preserves the dimension of the closure of a point lying over the
complement of the centre. -/
private theorem topologicalKrullDim_closure_blowUpToBase {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (Z : X.IdealSheafData)
    [LocallyOfFiniteType (blowUpToBase Z ≫ sX)] {η : blowUp Z}
    (hη : blowUpToBase Z η ∉ (Z.support : Set X)) :
    topologicalKrullDim (closure ({η} : Set (blowUp Z))) =
      topologicalKrullDim (closure ({blowUpToBase Z η} : Set X)) := by
  rw [topologicalKrullDim_closure_eq_toNat_relativeDimension k (blowUpToBase Z ≫ sX),
    topologicalKrullDim_closure_eq_toNat_relativeDimension k sX]
  let U : X.Opens := ⟨(Z.support : Set X)ᶜ, Z.support.isClosed.isOpen_compl⟩
  have : IsIso (blowUpToBase Z ∣_ U) := isIso_blowUp_restrict_compl_support Z
  let z : (blowUpToBase Z ⁻¹ᵁ U).toScheme := ⟨η, hη⟩
  have h1 := Stacks.Chow.relativeDimension_comp_isOpenImmersion
    (Stacks.Chow.fieldChowSituation k).dimensionFunction (blowUpToBase Z ⁻¹ᵁ U).ι
    (blowUpToBase Z ≫ sX) z
  rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc,
    Stacks.Chow.relativeDimension_comp_isOpenImmersion,
    Stacks.Chow.relativeDimension_comp_isOpenImmersion] at h1
  have h2 : U.ι ((blowUpToBase Z ∣_ U) z) = blowUpToBase Z η :=
    morphismRestrict_base_coe (blowUpToBase Z) U z
  rw [h2] at h1
  change _ = (Stacks.Chow.relativeDimension _ (blowUpToBase Z ≫ sX) η) at h1
  rw [h1]

/-- Every irreducible component of the blow-up has the dimension of an irreducible component of
the base. -/
private theorem exists_irreducibleComponent_dim_eq {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (Z : X.IdealSheafData)
    [LocallyOfFiniteType (blowUpToBase Z ≫ sX)] {C : Set (blowUp Z)}
    (hC : C ∈ irreducibleComponents (blowUp Z)) :
    ∃ C' ∈ irreducibleComponents X, topologicalKrullDim C = topologicalKrullDim C' := by
  obtain ⟨η, hη⟩ := QuasiSober.sober hC.1 (isClosed_of_mem_irreducibleComponents C hC)
  have hgen : η ∈ genericPoints (blowUp Z) := show closure {η} ∈ _ by rwa [hη.def]
  obtain ⟨hπ, hπZ⟩ := (bijOn_genericPoints_blowUpToBase Z).mapsTo hgen
  refine ⟨_, hπ, ?_⟩
  rw [← hη.def, topologicalKrullDim_closure_blowUpToBase sX Z
    (fun h => hπZ (Scheme.IdealSheafData.mem_supportSet_iff_mem_support.mpr h))]

/-- (ST) passes to the blow-up: it is equidimensional with components of positive dimension. -/
private theorem equidimensional_blowUp {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (Z : X.IdealSheafData)
    [LocallyOfFiniteType (blowUpToBase Z ≫ sX)] (hX : Equidimensional X)
    (hdim : ∀ C ∈ irreducibleComponents X, 0 < topologicalKrullDim C) :
    Equidimensional (blowUp Z) ∧
      ∀ C ∈ irreducibleComponents (blowUp Z), 0 < topologicalKrullDim C := by
  refine ⟨fun C hC W hW => ?_, fun C hC => ?_⟩
  · obtain ⟨C', hC', e⟩ := exists_irreducibleComponent_dim_eq sX Z hC
    obtain ⟨W', hW', e'⟩ := exists_irreducibleComponent_dim_eq sX Z hW
    rw [e, e']
    exact hX C' hC' W' hW'
  · obtain ⟨C', hC', e⟩ := exists_irreducibleComponent_dim_eq sX Z hC
    rw [e]
    exact hdim C' hC'

/-- One blow-up along a centre `Z` contained in the hypersurface cut out by a closed immersion
`i`: `π^*D^j(-log S)(I) ⊆ D^j(-log S_1)(I_1) · I_F^{m-j}` for `j ≤ m`, where `S_1` is cut out by
the canonical lift of `i` and `I_1 = 𝒪(mF)·π^*I`. -/
private theorem comap_higherLogDerivativeIdeal_le {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [Smooth sX] [QuasiCompact sX]
    (hX : Equidimensional X)
    (hdim : ∀ C ∈ irreducibleComponents X, 0 < topologicalKrullDim C)
    {Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i] (hS : IsSmoothHypersurface sX i.ker)
    (Z : X.IdealSheafData) (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ sX))
    (hcodim : HasComponentsOfPositiveCodim (Z.support : Set X)) (hiZ : i.ker ≤ Z)
    (a : MarkedIdeal X) (ha : IsNonzeroAtGenericPoints a.I)
    (hord : OrderAlongGE a.I (Z.support : Set X) a.m) (j : ℕ) (hj : j ≤ a.m) :
    (higherLogDerivativeIdeal sX i.ker a.I j).comap (blowUpToBase Z) ≤
      higherLogDerivativeIdeal (blowUpToBase Z ≫ sX) (canonicalLift i Z).ker
        (a.birationalTransform Z).I j * Z.comap (blowUpToBase Z) ^ (a.m - j) := by
  have hXs : MMP.Mori.IsSmoothScheme sX := (MMP.Mori.isSmoothScheme_iff sX).2 inferInstance
  have hZs : Smooth (Z.subschemeι ≫ sX) := (MMP.Mori.isSmoothScheme_iff _).1 hZ
  have hL : Stacks.Divisors.IsEffectiveCartierDivisor (Z.comap (blowUpToBase Z)) :=
    Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal Z
  rw [ker_canonicalLift_eq_subschemeι i Z]
  induction j with
  | zero =>
    change a.I.comap (blowUpToBase Z) ≤ (a.birationalTransform Z).I * _ ^ (a.m - 0)
    rw [Nat.sub_zero]
    exact (MarkedIdeal.birationalTransform_mul_eq sX hXs Z hZ hcodim a hord).ge
  | succ j ih =>
    set A := higherLogDerivativeIdeal sX i.ker a.I j
    have hA : IsNonzeroAtGenericPoints A :=
      isNonzeroAtGenericPoints_higherLogDerivativeIdeal sX hdim hS ha j
    have hIK := le_higherDerivativeIdeal_and_multAt sX hX hdim ha j
    have hordA : OrderAlongGE A (Z.support : Set X) ((a.m - j : ℕ) : ℕ∞) := by
      intro W hW
      change _ ≤ multAt A _
      refine le_trans ?_ (Kollar.multAt_antitone
        (higherLogDerivativeIdeal_le_higherDerivativeIdeal sX i.ker a.I j) _)
      rw [(hIK _).2, ENat.coe_sub]
      exact tsub_le_tsub_right (hord W hW) _
    have h1 := comap_logDerivativeIdeal_le_logDerivativeIdeal_birationalTransform_mul sX hX hdim
      hS Z hZs hiZ hA (a := a.m - j) (by omega) hordA
    have hA1 : (MarkedIdeal.birationalTransform Z ⟨A, a.m - j⟩).I ≤
        higherLogDerivativeIdeal (blowUpToBase Z ≫ sX)
          (canonicalLift i.ker.subschemeι Z).ker (a.birationalTransform Z).I j := by
      refine le_of_mul_le_mul_right (Stacks.Divisors.isEffectiveCartierDivisor_pow hL (a.m - j)) ?_
      rw [MarkedIdeal.birationalTransform_mul_eq sX hXs Z hZ hcodim ⟨A, a.m - j⟩ hordA]
      exact ih (by omega)
    rw [higherLogDerivativeIdeal_succ, higherLogDerivativeIdeal_succ,
      show a.m - (j + 1) = a.m - j - 1 by omega]
    exact h1.trans
      (mul_le_mul'
        (Proof_lem_kr3d_transform_log_derivative_one_blowup.logDerivativeIdeal_mono _ _ hA1)
        le_rfl)

/-- The induction along the sequence, carrying the hypersurface as a closed immersion `i`, for
every ideal `T ⊆ D^j(-log S)(I)` in place of `D^j(-log S)(I)`. -/
private theorem derivedTransform_le {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}
    (B : ClosedBlowupSequence X) (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX]
    [QuasiCompact sX] (hX : Equidimensional X)
    (hdim : ∀ C ∈ irreducibleComponents X, 0 < topologicalKrullDim C)
    (a : MarkedIdeal X) (hB : ClosedBlowupSequence.IsOrderGePlainSeq sX a B)
    {Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i] (hS : IsSmoothHypersurface sX i.ker)
    (hZS : B.CentersContainedIn i)
    (j : ℕ) (hj : j ≤ a.m) (T : X.IdealSheafData)
    (hT : T ≤ higherLogDerivativeIdeal sX i.ker a.I j) :
    ∃ J, B.derivedTransform (some T) (a.m - j) = some J ∧
      J ≤ higherLogDerivativeIdeal (B.toBase ≫ sX) (B.pullbackHom i).ker
        (B.markedTransform a).I j := by
  induction B generalizing Y with
  | nil X =>
    refine ⟨T, rfl, ?_⟩
    change T ≤ higherLogDerivativeIdeal (𝟙 X ≫ sX) i.ker a.I j
    rwa [Category.id_comp]
  | @cons X Z B ih =>
    obtain ⟨hsm, hnz, hZsm, hcodim, hord, hB'⟩ := hB
    obtain ⟨hiZ, hZS'⟩ := hZS
    have : Smooth sX := (MMP.Mori.isSmoothScheme_iff sX).1 hsm
    have hC := comap_higherLogDerivativeIdeal_le sX hX hdim i hS Z hZsm hcodim hiZ a hnz hord j hj
    have hL : Stacks.Divisors.IsEffectiveCartierDivisor (Z.comap (blowUpToBase Z)) :=
      Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal Z
    have hle := (Scheme.IdealSheafData.comap_mono (blowUpToBase Z) hT).trans hC
    obtain ⟨T', hstep⟩ : ∃ T', ClosedBlowupSequence.derivedTransformStep Z (a.m - j) (some T) =
        some T' := by
      classical
      simp only [ClosedBlowupSequence.derivedTransformStep]
      rw [if_pos (hle.trans (mul_le_of_le_one_left' le_top))]
      exact ⟨_, rfl⟩
    have hT' : T' ≤ higherLogDerivativeIdeal (blowUpToBase Z ≫ sX) (canonicalLift i Z).ker
        (a.birationalTransform Z).I j := by
      refine le_of_mul_le_mul_right
        (Stacks.Divisors.isEffectiveCartierDivisor_pow hL (a.m - j)) ?_
      rw [ClosedBlowupSequence.derivedTransformStep_mul_eq Z _ T T' hstep hL]
      exact hle
    have hs : Smooth (blowUpToBase Z ≫ sX) :=
      (Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup sX Z ⟨hsm, hZsm⟩).1
    have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    obtain ⟨hX', hdim'⟩ := equidimensional_blowUp sX Z hX hdim
    have : IsClosedImmersion (canonicalLift i Z) := Bridges.isClosedImmersion_canonicalLift i Z
    have hS' : IsSmoothHypersurface (blowUpToBase Z ≫ sX) (canonicalLift i Z).ker := by
      rw [ker_canonicalLift_eq_subschemeι i Z]
      exact (ker_canonicalLift_subschemeι_mul_comap_eq_comap sX hsm i.ker Z hS hZsm hiZ).2.2
    obtain ⟨J, hJ, hJle⟩ := ih (blowUpToBase Z ≫ sX) hX' hdim' (a.birationalTransform Z) hB'
      (canonicalLift i Z) hS' hZS' hj T' hT'
    refine ⟨J, ?_, ?_⟩
    · change B.derivedTransform (ClosedBlowupSequence.derivedTransformStep Z (a.m - j) (some T))
        (a.m - j) = some J
      rw [hstep]
      exact hJ
    · change J ≤ higherLogDerivativeIdeal ((B.toBase ≫ blowUpToBase Z) ≫ sX)
        (B.pullbackHom (canonicalLift i Z)).ker
        (B.markedTransform (a.birationalTransform Z)).I j
      rwa [Category.assoc]

end Proof_lem_kr3d_transform_log_derivative_inclusion

namespace MMP.Resolution.ClosedBlowupSequence

open Proof_lem_kr3d_transform_log_derivative_inclusion in
/-- **Transforms of logarithmic derivatives** (Kollár (3.87.3), corrected). Let `X` be smooth,
equidimensional and of finite type over a field `k` of characteristic `0`, with every irreducible
component of positive dimension, let `a = (K, a)` be a marked ideal with `K` nonzero on every
irreducible component, `B` a smooth blow-up sequence of order `≥ a` starting with `(X, K, a)`,
and `S ⊆ X` a smooth hypersurface such that every centre of `B` lies in the corresponding term
of the restriction `B|_S`. Then for `j ≤ a` the transform `T_r(D^j(-log S)(K), a - j)` along `B`
is an ideal sheaf `J` on `X_r` with `J ≤ D^j(-log S_r)(K_r)`, where `S_r` is cut out by the
kernel of `B.restrictHom S` and `K_r` is the marked transform of `(K, a)`. -/
@[mmp "lem_kr3d_transform_log_derivative_inclusion"]
public theorem derivedTransform_higherLogDerivativeIdeal_le {k : Type u} [Field k]
    [CharZero k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX]
    [QuasiCompact sX] (hX : Equidimensional X)
    (hdim : ∀ Z ∈ irreducibleComponents X, 0 < topologicalKrullDim Z)
    (a : MarkedIdeal X) (ha : IsNonzeroAtGenericPoints a.I)
    (B : ClosedBlowupSequence X) (hB : IsOrderGePlainSeq sX a B)
    {S : X.IdealSheafData} (hS : IsSmoothHypersurface sX S)
    (hZS : B.CentersContainedIn S.subschemeι)
    (j : ℕ) (hj : j ≤ a.m) :
    ∃ J, B.derivedTransform (some (higherLogDerivativeIdeal sX S a.I j)) (a.m - j) = some J ∧
      J ≤ higherLogDerivativeIdeal (B.toBase ≫ sX) (B.restrictHom S).ker
        (B.markedTransform a).I j :=
  derivedTransform_le B sX hX hdim a hB S.subschemeι (by rwa [S.ker_subschemeι]) hZS j hj _
    (by rw [S.ker_subschemeι])

end MMP.Resolution.ClosedBlowupSequence

end

/-!
## Logarithmic decomposition of derivatives of a transformed marked ideal

Let `X` be a smooth equidimensional scheme of finite type over a field `k` of characteristic
`0`, with every irreducible component of positive dimension, let `(I, m)` be a marked ideal sheaf
with `I` nonzero on every irreducible component, and let `Π = (X_i, Z_i)_{i ≤ r}` be a smooth
blow-up sequence of order `≥ m` starting with `(X, I, m)`, with marked ideals `(I_i, m)`. Let
`S ⊆ X` be a smooth hypersurface whose restriction `(S_i)` contains every centre, `Z_i ⊆ S_i`.
Then for `0 ≤ s ≤ m` every transform `T_r(D^j I, m - j)`, `j ≤ s`, is an ideal sheaf on `X_r`
and
`D^s(I_r) = ∑_{j=0}^s D^{s-j}(-log S_r)(T_r(D^j I, m - j))`.

## Main results

* `MMP.Resolution.ClosedBlowupSequence.higherDerivativeIdeal_markedTransform_eq_iSup`

## Implementation notes

The hypersurface `S_r ⊆ X_r` is the closed subscheme cut out by the kernel of the morphism
`Π.restrictHom S : S_r → X_r` of the restriction `Π|_S`, and the containment of the centres in
the `S_i` is `Π.CentersContainedIn S.subschemeι`. The transform `T_r(D^j I, m - j)` is
`derivedTransformJ`, whose value `some J` records that it is an ideal sheaf `J`; since the
logarithmic derivative can only be applied to ideal sheaves, the statement provides the family
`J` of these ideal sheaves together with the decomposition. The sum of ideal sheaves is their
supremum.

## References

* [J. Kollár, *Lectures on resolution of singularities*, Thm. 3.88][kollar2007]
-/

section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Resolution

namespace Proof_thm_kr3d_log_decomposition_of_derivatives

open MMP.Resolution.ClosedBlowupSequence

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

section LogDerivative

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))

/-- `D(-log S)(A + B) ⊆ D(-log S)(A) + D(-log S)(B)`. -/
private theorem logDerivativeIdeal_sup_le [LocallyOfFiniteType sX] (S A B : X.IdealSheafData) :
    logDerivativeIdeal sX S (A ⊔ B) ≤ logDerivativeIdeal sX S A ⊔ logDerivativeIdeal sX S B := by
  refine sInf_le fun W => ?_
  letI := MMP.Mori.sectionAlgebra sX W.1
  change sectionLogDerivativeIdeal sX S (A ⊔ B) W ≤
    (logDerivativeIdeal sX S A).ideal W ⊔ (logDerivativeIdeal sX S B).ideal W
  rw [logDerivativeIdeal_ideal, logDerivativeIdeal_ideal]
  refine Ideal.span_le.2 ?_
  rintro _ ⟨δ, hδ, f, hf, rfl⟩
  change f ∈ A.ideal W ⊔ B.ideal W at hf
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hf
  rw [map_add]
  exact add_mem (Ideal.mem_sup_left (Ideal.subset_span ⟨δ, hδ, x, hx, rfl⟩))
    (Ideal.mem_sup_right (Ideal.subset_span ⟨δ, hδ, y, hy, rfl⟩))

open Proof_lem_kr3d_transform_log_derivative_inclusion in
private theorem higherLogDerivativeIdeal_mono (S : X.IdealSheafData) {I J : X.IdealSheafData}
    (h : I ≤ J) (n : ℕ) :
    higherLogDerivativeIdeal sX S I n ≤ higherLogDerivativeIdeal sX S J n := by
  induction n with
  | zero => exact h
  | succ n ih =>
    simp only [higherLogDerivativeIdeal, Function.iterate_succ_apply'] at ih ⊢
    exact Proof_lem_kr3d_transform_log_derivative_one_blowup.logDerivativeIdeal_mono sX S ih

open Proof_lem_kr3d_transform_log_derivative_inclusion in
private theorem higherLogDerivativeIdeal_sup_le [LocallyOfFiniteType sX]
    (S A B : X.IdealSheafData) (n : ℕ) :
    higherLogDerivativeIdeal sX S (A ⊔ B) n ≤
      higherLogDerivativeIdeal sX S A n ⊔ higherLogDerivativeIdeal sX S B n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    simp only [higherLogDerivativeIdeal, Function.iterate_succ_apply'] at ih ⊢
    exact (Proof_lem_kr3d_transform_log_derivative_one_blowup.logDerivativeIdeal_mono sX S ih).trans
      (logDerivativeIdeal_sup_le sX S _ _)

/-- `D^n(-log S)` is subadditive on finite sums. -/
private theorem higherLogDerivativeIdeal_biSup_le [LocallyOfFiniteType sX]
    (S : X.IdealSheafData) (f : ℕ → X.IdealSheafData) (n j : ℕ) :
    higherLogDerivativeIdeal sX S (⨆ (l : ℕ) (_ : l ≤ j), f l) n ≤
      ⨆ (l : ℕ) (_ : l ≤ j), higherLogDerivativeIdeal sX S (f l) n := by
  induction j with
  | zero => simp only [Nat.le_zero, iSup_iSup_eq_left]; exact le_rfl
  | succ j ih =>
    rw [Nat.iSup_le_succ, Nat.iSup_le_succ]
    exact (higherLogDerivativeIdeal_sup_le sX S _ _ n).trans (sup_le_sup_right ih _)

private theorem higherLogDerivativeIdeal_higherLogDerivativeIdeal (S I : X.IdealSheafData)
    (a b : ℕ) :
    higherLogDerivativeIdeal sX S (higherLogDerivativeIdeal sX S I b) a =
      higherLogDerivativeIdeal sX S I (a + b) :=
  (Function.iterate_add_apply _ a b I).symm

/-- If `K ⊆ ∑_{l ≤ j} D^{j-l}(-log S)(J_l)` and `j ≤ s`, then
`D^{s-j}(-log S)(K) ⊆ ∑_{l ≤ s} D^{s-l}(-log S)(J_l)`. -/
private theorem higherLogDerivativeIdeal_le_iSup_of_le_iSup [LocallyOfFiniteType sX]
    (S : X.IdealSheafData) (J : ℕ → X.IdealSheafData) {K : X.IdealSheafData} {j s : ℕ}
    (hj : j ≤ s) (hK : K ≤ ⨆ (l : ℕ) (_ : l ≤ j), higherLogDerivativeIdeal sX S (J l) (j - l)) :
    higherLogDerivativeIdeal sX S K (s - j) ≤
      ⨆ (l : ℕ) (_ : l ≤ s), higherLogDerivativeIdeal sX S (J l) (s - l) := by
  refine (higherLogDerivativeIdeal_mono sX S hK _).trans
    ((higherLogDerivativeIdeal_biSup_le sX S _ _ _).trans (iSup₂_le fun l hl => ?_))
  rw [higherLogDerivativeIdeal_higherLogDerivativeIdeal, show s - j + (j - l) = s - l by omega]
  exact le_iSup₂_of_le (f := fun l (_ : l ≤ s) => higherLogDerivativeIdeal sX S (J l) (s - l))
    l (hl.trans hj) le_rfl

end LogDerivative

section Transform

variable {X : Scheme.{u}}

private theorem isEffectiveCartierDivisor_exceptional_pow (Z : X.IdealSheafData) (b : ℕ) :
    Stacks.Divisors.IsEffectiveCartierDivisor (Z.comap (blowUpToBase Z) ^ b) :=
  Stacks.Divisors.isEffectiveCartierDivisor_pow
    (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal Z) b

open Proof_lem_kr3d_transform_log_derivative_inclusion in
private theorem eq_of_derivedTransformStep_mul {Z : X.IdealSheafData} {b : ℕ}
    {A B : (blowUp Z).IdealSheafData}
    (h : A * Z.comap (blowUpToBase Z) ^ b = B * Z.comap (blowUpToBase Z) ^ b) : A = B :=
  le_antisymm (le_of_mul_le_mul_right (isEffectiveCartierDivisor_exceptional_pow Z b) h.le)
    (le_of_mul_le_mul_right (isEffectiveCartierDivisor_exceptional_pow Z b) h.ge)

private theorem mul_eq_of_derivedTransformStep {Z : X.IdealSheafData} {b : ℕ}
    {K : X.IdealSheafData} {T : (blowUp Z).IdealSheafData}
    (h : derivedTransformStep Z b (some K) = some T) :
    T * Z.comap (blowUpToBase Z) ^ b = K.comap (blowUpToBase Z) :=
  derivedTransformStep_mul_eq Z b K T h (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal Z)

private theorem comap_le_of_derivedTransformStep {Z : X.IdealSheafData} {b : ℕ}
    {K : X.IdealSheafData} {T : (blowUp Z).IdealSheafData}
    (h : derivedTransformStep Z b (some K) = some T) :
    K.comap (blowUpToBase Z) ≤ Z.comap (blowUpToBase Z) ^ b := by
  rw [← mul_eq_of_derivedTransformStep h]
  exact mul_le_of_le_one_left' le_top

private theorem exists_derivedTransformStep_eq_some {Z : X.IdealSheafData} {b : ℕ}
    {K : X.IdealSheafData} (h : K.comap (blowUpToBase Z) ≤ Z.comap (blowUpToBase Z) ^ b) :
    ∃ T, derivedTransformStep Z b (some K) = some T := by
  classical
  simp only [derivedTransformStep]
  rw [if_pos h]
  exact ⟨_, rfl⟩

private theorem derivedTransformStep_bot (Z : X.IdealSheafData) (b : ℕ) :
    derivedTransformStep Z b (some ⊥) = some ⊥ := by
  obtain ⟨T, hT⟩ := exists_derivedTransformStep_eq_some (Z := Z) (b := b) (K := ⊥)
    (by rw [Scheme.IdealSheafData.comap_bot]; exact bot_le)
  rw [hT]
  refine congrArg some (eq_of_derivedTransformStep_mul (b := b) ?_)
  rw [mul_eq_of_derivedTransformStep hT, Scheme.IdealSheafData.comap_bot,
    Scheme.IdealSheafData.bot_mul]

private theorem derivedTransformStep_sup {Z : X.IdealSheafData} {b : ℕ}
    {K₁ K₂ : X.IdealSheafData} {T₁ T₂ : (blowUp Z).IdealSheafData}
    (h₁ : derivedTransformStep Z b (some K₁) = some T₁)
    (h₂ : derivedTransformStep Z b (some K₂) = some T₂) :
    derivedTransformStep Z b (some (K₁ ⊔ K₂)) = some (T₁ ⊔ T₂) := by
  have hle : (K₁ ⊔ K₂).comap (blowUpToBase Z) ≤ Z.comap (blowUpToBase Z) ^ b := by
    rw [Scheme.IdealSheafData.comap_sup]
    exact sup_le (comap_le_of_derivedTransformStep h₁) (comap_le_of_derivedTransformStep h₂)
  obtain ⟨T, hT⟩ := exists_derivedTransformStep_eq_some hle
  rw [hT]
  refine congrArg some (eq_of_derivedTransformStep_mul (b := b) ?_)
  rw [mul_eq_of_derivedTransformStep hT, Scheme.IdealSheafData.inf_mul,
    mul_eq_of_derivedTransformStep h₁, mul_eq_of_derivedTransformStep h₂,
    Scheme.IdealSheafData.comap_sup]

private theorem derivedTransformStep_sup_eq_none {Z : X.IdealSheafData} {b : ℕ}
    {K₁ K₂ : X.IdealSheafData}
    (h : derivedTransformStep Z b (some K₁) = none ∨ derivedTransformStep Z b (some K₂) = none) :
    derivedTransformStep Z b (some (K₁ ⊔ K₂)) = none := by
  by_contra hne
  obtain ⟨T, hT⟩ := Option.ne_none_iff_exists'.1 hne
  have hle := comap_le_of_derivedTransformStep hT
  rw [Scheme.IdealSheafData.comap_sup] at hle
  rcases h with h | h
  · obtain ⟨T', hT'⟩ := exists_derivedTransformStep_eq_some (le_sup_left.trans hle)
    rw [hT'] at h; cases h
  · obtain ⟨T', hT'⟩ := exists_derivedTransformStep_eq_some (le_sup_right.trans hle)
    rw [hT'] at h; cases h

/-- Along a blow-up sequence, the transform of a sum is either `0`, or not an ideal sheaf
together with one of the summands, or the sum of the transforms. -/
private theorem derivedTransform_sup_aux (B : ClosedBlowupSequence X) (b : ℕ) :
    ∀ o o₁ o₂ : Option X.IdealSheafData,
      (o = some ⊥ ∨ (o = none ∧ (o₁ = none ∨ o₂ = none)) ∨
        ∃ T₁ T₂, o₁ = some T₁ ∧ o₂ = some T₂ ∧ o = some (T₁ ⊔ T₂)) →
      (B.derivedTransform o b = some ⊥ ∨
        (B.derivedTransform o b = none ∧
          (B.derivedTransform o₁ b = none ∨ B.derivedTransform o₂ b = none)) ∨
        ∃ T₁ T₂, B.derivedTransform o₁ b = some T₁ ∧ B.derivedTransform o₂ b = some T₂ ∧
          B.derivedTransform o b = some (T₁ ⊔ T₂)) := by
  induction B with
  | nil X => intro o o₁ o₂ h; exact h
  | cons Z B ih =>
    intro o o₁ o₂ h
    refine ih (derivedTransformStep Z b o) (derivedTransformStep Z b o₁)
      (derivedTransformStep Z b o₂) ?_
    rcases h with rfl | ⟨rfl, -⟩ | ⟨T₁, T₂, rfl, rfl, rfl⟩
    · exact Or.inl (derivedTransformStep_bot Z b)
    · exact Or.inl rfl
    · rcases h₁ : derivedTransformStep Z b (some T₁) with _ | T₁'
      · exact Or.inr (Or.inl ⟨derivedTransformStep_sup_eq_none (Or.inl h₁), Or.inl rfl⟩)
      · rcases h₂ : derivedTransformStep Z b (some T₂) with _ | T₂'
        · exact Or.inr (Or.inl ⟨derivedTransformStep_sup_eq_none (Or.inr h₂), Or.inr rfl⟩)
        · exact Or.inr (Or.inr ⟨T₁', T₂', rfl, rfl, derivedTransformStep_sup h₁ h₂⟩)

/-- The transform `T(·, b)` along a blow-up sequence is subadditive on finite sums of ideal
sheaves whose transforms are ideal sheaves. -/
private theorem derivedTransform_biSup_le (B : ClosedBlowupSequence X) (b : ℕ)
    (K : ℕ → X.IdealSheafData) (g : ℕ → B.target.IdealSheafData) (j : ℕ)
    (hK : ∀ l ≤ j, B.derivedTransform (some (K l)) b = some (g l))
    {T : B.target.IdealSheafData}
    (h : B.derivedTransform (some (⨆ (l : ℕ) (_ : l ≤ j), K l)) b = some T) :
    T ≤ ⨆ (l : ℕ) (_ : l ≤ j), g l := by
  induction j generalizing T with
  | zero =>
    simp only [Nat.le_zero, iSup_iSup_eq_left] at h ⊢
    rw [hK 0 le_rfl, Option.some_inj] at h
    exact h.ge
  | succ j ih =>
    rw [Nat.iSup_le_succ] at h ⊢
    rcases derivedTransform_sup_aux B b _ (some (⨆ (l : ℕ) (_ : l ≤ j), K l)) (some (K (j + 1)))
      (Or.inr (Or.inr ⟨_, _, rfl, rfl, rfl⟩)) with h' | ⟨h', -⟩ | ⟨T₁, T₂, h₁, h₂, h'⟩
    · rw [h, Option.some_inj] at h'
      rw [h']
      exact bot_le
    · rw [h] at h'
      cases h'
    · rw [h, Option.some_inj] at h'
      rw [hK (j + 1) le_rfl, Option.some_inj] at h₂
      rw [h', ← h₂]
      exact sup_le_sup_right (ih (fun l hl => hK l (hl.trans (Nat.le_succ j))) h₁) _

end Transform

section Sequence

/-- The kernel of `Π.pullbackHom ι`, and whether the centres lie in the restriction, only depend
on `ι` up to an isomorphism of its source. -/
private theorem ker_pullbackHom_eq_of_isIso {X : Scheme.{u}} (B : ClosedBlowupSequence X) :
    ∀ {Y Y' : Scheme.{u}} (ι : Y ⟶ X) (ι' : Y' ⟶ X) (t : Y ⟶ Y') [IsIso t], t ≫ ι' = ι →
      (B.pullbackHom ι).ker = (B.pullbackHom ι').ker ∧
        (B.CentersContainedIn ι ↔ B.CentersContainedIn ι') := by
  induction B with
  | nil X =>
    intro Y Y' ι ι' t _ h
    subst h
    exact ⟨Scheme.Hom.ker_comp_of_isIso t ι', Iff.rfl⟩
  | cons Z B ih =>
    intro Y Y' ι ι' t _ h
    subst h
    have : IsIso (canonicalLift t (Z.comap ι')) := MMP.Resolution.Kollar.isIso_canonicalLift t _
    have key := ih (canonicalLift (t ≫ ι') Z) (canonicalLift ι' Z)
      (eqToHom (congrArg blowUp (Scheme.IdealSheafData.comap_comp Z t ι')) ≫
        canonicalLift t (Z.comap ι'))
      (by simp [ClosedBlowupSequence.canonicalLift_comp_canonicalLift])
    refine ⟨key.1, ?_⟩
    change ((t ≫ ι').ker ≤ Z ∧ B.CentersContainedIn (canonicalLift (t ≫ ι') Z)) ↔
      (ι'.ker ≤ Z ∧ B.CentersContainedIn (canonicalLift ι' Z))
    rw [Scheme.Hom.ker_comp_of_isIso, key.2]

/-- For a closed immersion `ι`, pulling a blow-up sequence back along `ι` or along the closed
subscheme cut out by `ker ι` gives the same final ideal sheaf and the same containments. -/
private theorem ker_pullbackHom_subschemeι {X : Scheme.{u}} (B : ClosedBlowupSequence X)
    {Y : Scheme.{u}} (ι : Y ⟶ X) [IsClosedImmersion ι] :
    (B.pullbackHom ι).ker = (B.pullbackHom ι.ker.subschemeι).ker ∧
      (B.CentersContainedIn ι ↔ B.CentersContainedIn ι.ker.subschemeι) := by
  have : IsIso ι.toImage :=
    IsClosedImmersion.isIso_of_ker_eq ι ι.imageι ι.toImage ι.toImage_imageι (by simp)
  exact ker_pullbackHom_eq_of_isIso B ι ι.ker.subschemeι ι.toImage ι.toImage_imageι

private theorem truncate_length {X : Scheme.{u}} (B : ClosedBlowupSequence X) :
    B.truncate B.length = B := by
  induction B with
  | nil _ => rfl
  | cons Z B ih =>
    change ClosedBlowupSequence.cons Z (B.truncate B.length) = _
    rw [ih]

variable {k : Type u} [Field k]

private theorem isNonzeroAtGenericPoints_of_isOrderGePlainSeq {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {a : MarkedIdeal X} {B : ClosedBlowupSequence X}
    (h : IsOrderGePlainSeq sX a B) : IsNonzeroAtGenericPoints a.I := by
  cases B with
  | nil => exact h.2
  | cons Z B => exact h.2.1

private theorem locallyOfFiniteType_toBase {X : Scheme.{u}} (B : ClosedBlowupSequence X) :
    ∀ (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX], LocallyOfFiniteType (B.toBase ≫ sX) := by
  induction B with
  | nil X =>
    intro sX _
    change LocallyOfFiniteType (𝟙 X ≫ sX)
    rw [Category.id_comp]
    infer_instance
  | @cons X Z B ih =>
    intro sX _
    have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    have : IsProper (blowUpToBase Z) := isProper_blowUpToBase Z
    change LocallyOfFiniteType ((B.toBase ≫ blowUpToBase Z) ≫ sX)
    rw [Category.assoc]
    exact ih _

end Sequence

/-- The inclusion `D^s(I_r) ⊆ ∑_{j ≤ s} D^{s-j}(-log S_r)(T_r(D^j I, m - j))`, by induction along
the sequence. -/
private theorem higherDerivativeIdeal_markedTransform_le {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} (B : ClosedBlowupSequence X) :
    ∀ (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] [QuasiCompact sX],
      Equidimensional X → (∀ C ∈ irreducibleComponents X, 0 < topologicalKrullDim C) →
      ∀ (a : MarkedIdeal X), IsNonzeroAtGenericPoints a.I → IsOrderGePlainSeq sX a B →
      ∀ {S : X.IdealSheafData}, IsSmoothHypersurface sX S → B.CentersContainedIn S.subschemeι →
      ∀ {s : ℕ}, s ≤ a.m → ∀ J : ℕ → B.target.IdealSheafData,
        (∀ j ≤ s, derivedTransformJ sX B a j = some (J j)) →
        higherDerivativeIdeal (B.toBase ≫ sX) (B.markedTransform a).I s ≤
          ⨆ (j : ℕ) (_ : j ≤ s),
            higherLogDerivativeIdeal (B.toBase ≫ sX) (B.restrictHom S).ker (J j) (s - j) := by
  induction B with
  | nil X =>
    intro sX _ _ hX hdim a ha hB S hS hZS s hs J hJ
    have h : higherDerivativeIdeal sX a.I s = J s := Option.some_inj.1 (hJ s le_rfl)
    refine le_iSup₂_of_le s le_rfl ?_
    rw [Nat.sub_self]
    change higherDerivativeIdeal (𝟙 X ≫ sX) a.I s ≤ J s
    rw [Category.id_comp, h]
    exact le_rfl
  | @cons X Z B ih =>
    intro sX _ _ hX hdim a ha hB S hS hZS s hs J hJ
    have hB0 := hB
    obtain ⟨hsm, -, hZsm, -, hord, hB'⟩ := hB
    obtain ⟨hSZ, hZS'⟩ := hZS
    rw [Scheme.IdealSheafData.ker_subschemeι] at hSZ
    have : Smooth sX := (MMP.Mori.isSmoothScheme_iff sX).1 hsm
    have hZs : Smooth (Z.subschemeι ≫ sX) := (MMP.Mori.isSmoothScheme_iff _).1 hZsm
    have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    have : IsProper (blowUpToBase Z) := isProper_blowUpToBase Z
    have : Smooth (blowUpToBase Z ≫ sX) :=
      (Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup sX Z ⟨hsm, hZsm⟩).1
    have hX' := equidimensional_blowUp sX Z hX
    have hdim' : ∀ C ∈ irreducibleComponents (blowUp Z), 0 < topologicalKrullDim C :=
      fun C hC => by
        obtain ⟨D, hD, e⟩ :=
          exists_topologicalKrullDim_eq_of_mem_irreducibleComponents_blowUp sX Z hC
        rw [e]; exact hdim D hD
    have ha1 := isNonzeroAtGenericPoints_of_isOrderGePlainSeq hB'
    obtain ⟨hι1, -, hS1⟩ := ker_canonicalLift_subschemeι_mul_comap_eq_comap sX hsm S Z hS hZsm hSZ
    have hker := ker_pullbackHom_subschemeι B (canonicalLift S.subschemeι Z)
    have hZS1 : B.CentersContainedIn (canonicalLift S.subschemeι Z).ker.subschemeι :=
      hker.2.1 hZS'
    have hSr : ((ClosedBlowupSequence.cons Z B).restrictHom S).ker =
        (B.restrictHom (canonicalLift S.subschemeι Z).ker).ker := hker.1
    have hbase : (ClosedBlowupSequence.cons Z B).toBase ≫ sX = B.toBase ≫ blowUpToBase Z ≫ sX :=
      Category.assoc _ _ _
    have : LocallyOfFiniteType (B.toBase ≫ blowUpToBase Z ≫ sX) :=
      locallyOfFiniteType_toBase B (blowUpToBase Z ≫ sX)
    -- the transforms `T(D^j I_1, m - j)` along the remaining sequence
    have hJ1 : ∀ j ≤ s, ∃ T, derivedTransformJ (blowUpToBase Z ≫ sX) B
        (a.birationalTransform Z) j = some T := fun j hj => by
      obtain ⟨T, hT, -⟩ := higherLogDerivativeIdeal_derivedTransformJ_le (blowUpToBase Z ≫ sX)
        hX' hdim' _ ha1 B hB' hS1 hZS1 hj hs
      exact ⟨T, hT⟩
    choose! J1 hJ1 using hJ1
    have hIH := ih (blowUpToBase Z ≫ sX) hX' hdim' _ ha1 hB' hS1 hZS1 hs J1 hJ1
    rw [hSr, hbase]
    refine hIH.trans (iSup₂_le fun j hj =>
      higherLogDerivativeIdeal_le_iSup_of_le_iSup (B.toBase ≫ blowUpToBase Z ≫ sX) _ J hj ?_)
    -- `T(D^j I_1, m - j) ⊆ ∑_{l ≤ j} D^{j-l}(-log S_r)(T_r(D^l I, m - l))`
    have h1 := higherDerivativeIdeal_birationalTransform_eq_iSup sX hX hdim hS Z hZs hSZ ha
      hord (hj.trans hs)
    have h2 : B.derivedTransform (some (⨆ (l : ℕ) (_ : l ≤ j),
        higherLogDerivativeIdeal (blowUpToBase Z ≫ sX) (canonicalLift S.subschemeι Z).ker
          (MarkedIdeal.birationalTransform Z ⟨higherDerivativeIdeal sX a.I l, a.m - l⟩).I
          (j - l))) (a.m - j) = some (J1 j) := by
      rw [← h1]
      exact hJ1 j hj
    have hT : ∀ l ≤ j, ∃ T, B.derivedTransform (some (higherLogDerivativeIdeal
        (blowUpToBase Z ≫ sX) (canonicalLift S.subschemeι Z).ker
        (MarkedIdeal.birationalTransform Z ⟨higherDerivativeIdeal sX a.I l, a.m - l⟩).I
          (j - l))) (a.m - j) = some T ∧
        T ≤ higherLogDerivativeIdeal (B.toBase ≫ blowUpToBase Z ≫ sX)
          (B.restrictHom (canonicalLift S.subschemeι Z).ker).ker (J l) (j - l) := by
      intro l hl
      have hlm : l ≤ a.m := hl.trans (hj.trans hs)
      have hO := isOrderGePlainSeq_higherDerivativeIdeal sX hX hdim a ha _ hB0 l hlm
      have hOB' := hO.1.2.2.2.2.2
      obtain ⟨T, hT, hTle⟩ := derivedTransform_higherLogDerivativeIdeal_le
        (blowUpToBase Z ≫ sX) hX' hdim' _ (isNonzeroAtGenericPoints_of_isOrderGePlainSeq hOB')
        B hOB' hS1 hZS1 (j - l) (show j - l ≤ a.m - l by omega)
      have hJl := hO.2 _ le_rfl
      rw [truncate_length, hJ l (hl.trans hj), Option.some_inj] at hJl
      refine ⟨T, ?_, ?_⟩
      · rw [← hT]
        congr 1
        change a.m - j = a.m - l - (j - l)
        omega
      · rw [hJl]
        exact hTle
    choose! g hg hgle using hT
    exact (derivedTransform_biSup_le B (a.m - j) _ g j hg h2).trans (iSup₂_mono hgle)

end Proof_thm_kr3d_log_decomposition_of_derivatives

namespace MMP.Resolution.ClosedBlowupSequence

open Proof_thm_kr3d_log_decomposition_of_derivatives in
/-- **Logarithmic decomposition of derivatives** (Kollár Thm. 3.88). Let `X` be smooth,
equidimensional and of finite type over a field `k` of characteristic `0`, with every irreducible
component of positive dimension, let `a = (I, m)` be a marked ideal with `I` nonzero on every
irreducible component, `B` a smooth blow-up sequence of order `≥ m` starting with `(X, I, m)`,
and `S ⊆ X` a smooth hypersurface such that every centre of `B` lies in the corresponding term
of the restriction `B|_S`. Then for `s ≤ m` each transform `T_r(D^j I, m - j)`, `j ≤ s`, is an
ideal sheaf `J j` on `X_r`, and `D^s(I_r)` is the supremum over `j ≤ s` of
`D^{s-j}(-log S_r)(J j)`, where `S_r` is cut out by the kernel of `B.restrictHom S` and `I_r` is
the marked transform of `(I, m)`. -/
@[mmp "thm_kr3d_log_decomposition_of_derivatives"]
public theorem higherDerivativeIdeal_markedTransform_eq_iSup {k : Type u} [Field k]
    [CharZero k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX]
    [QuasiCompact sX] (hX : Equidimensional X)
    (hdim : ∀ Z ∈ irreducibleComponents X, 0 < topologicalKrullDim Z)
    (a : MarkedIdeal X) (ha : IsNonzeroAtGenericPoints a.I)
    (B : ClosedBlowupSequence X) (hB : IsOrderGePlainSeq sX a B)
    {S : X.IdealSheafData} (hS : IsSmoothHypersurface sX S)
    (hZS : B.CentersContainedIn S.subschemeι)
    {s : ℕ} (hs : s ≤ a.m) :
    ∃ J : ℕ → B.target.IdealSheafData,
      (∀ j ≤ s, derivedTransformJ sX B a j = some (J j)) ∧
      higherDerivativeIdeal (B.toBase ≫ sX) (B.markedTransform a).I s =
        ⨆ (j : ℕ) (_ : j ≤ s),
          higherLogDerivativeIdeal (B.toBase ≫ sX) (B.restrictHom S).ker (J j) (s - j) := by
  have hJ : ∀ j ≤ s, ∃ T, derivedTransformJ sX B a j = some T ∧
      higherLogDerivativeIdeal (B.toBase ≫ sX) (B.restrictHom S).ker T (s - j) ≤
        higherDerivativeIdeal (B.toBase ≫ sX) (B.markedTransform a).I s := fun j hj =>
    higherLogDerivativeIdeal_derivedTransformJ_le sX hX hdim a ha B hB hS hZS hj hs
  choose! J hJ hJle using hJ
  exact ⟨J, hJ, le_antisymm
    (higherDerivativeIdeal_markedTransform_le B sX hX hdim a ha hB hS hZS hs J hJ)
    (iSup₂_le hJle)⟩

end MMP.Resolution.ClosedBlowupSequence

end

/-!
## Restriction of the logarithmic decomposition of derivatives to the hypersurface

In the setting of
`MMP.Resolution.ClosedBlowupSequence.higherDerivativeIdeal_markedTransform_eq_iSup`
(a smooth blow-up sequence `Π = (X_i, Z_i)_{i ≤ r}` of order `≥ m` starting with `(X, I, m)` and a
smooth hypersurface `S ⊆ X` whose transforms `S_i` contain the centres `Z_i`), assume moreover
`m ≥ 1` and that `I|_S` is nonzero on every irreducible component of `S`. Then for `0 ≤ s ≤ m`
every transform `T^S_r((D^j I)|_S, m - j)`, `j ≤ s`, along the restricted sequence `Π|_S` is an
ideal sheaf on `S_r`, and
`(D^s(I_r))|_{S_r} = ∑_{j=0}^s D^{s-j}(T^S_r((D^j I)|_S, m - j))`,
the derivatives on the right being taken on `S_r`.

## Main results

* `ClosedBlowupSequence.higherDerivativeIdeal_markedTransform_comap_restrictHom_eq_iSup`

## Implementation notes

The restricted sequence is `Π.restrict S`, with `S_r → X_r` the morphism `Π.restrictHom S`;
restriction of ideal sheaves along it is the inverse image `Scheme.IdealSheafData.comap`. The
transform `T^S_r(K, a)` along `Π|_S` is `derivedTransform` applied to `some K`; it is
`Option`-valued, so the statement provides the family `J` of ideal sheaves it takes. The scheme
`S_r` lies over `k` through `(Π.restrict S).toBase ≫ S.subschemeι ≫ sX`. The sum of ideal sheaves
is their supremum.

## References

* [J. Kollár, *Lectures on resolution of singularities*, (3.89.1)][kollar2007]
-/

section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Resolution
open ClosedBlowupSequence

namespace Proof_lem_kr3d_restricted_log_decomposition

/-- The ideal quotient by the unit ideal is the ideal itself. -/
private theorem idealColon_top {X : Scheme.{u}} (A : X.IdealSheafData) : idealColon A ⊤ = A := by
  unfold idealColon
  convert Scheme.IdealSheafData.ofIdeals_ideal A using 2
  funext V
  ext x
  simp only [Scheme.IdealSheafData.ideal_top, Submodule.mem_colon]
  exact ⟨fun h => by simpa using h 1 (by simp), fun h y _ => (A.ideal V).mul_mem_right y h⟩

/-- With marking `0` the transform is the pull-back: `T_r(K, 0) = Π_r^* K`. -/
private theorem derivedTransform_zero {X : Scheme.{u}} (B : ClosedBlowupSequence X)
    (K : X.IdealSheafData) : B.derivedTransform (some K) 0 = some (K.comap B.toBase) := by
  induction B with
  | nil X => exact congrArg some (Scheme.IdealSheafData.comap_id K).symm
  | cons Z B ih =>
    classical
    change B.derivedTransform (derivedTransformStep Z 0 (some K)) 0 = _
    have : derivedTransformStep Z 0 (some K) = some (K.comap (blowUpToBase Z)) := by
      simp only [derivedTransformStep, pow_zero]
      rw [show (1 : (blowUp Z).IdealSheafData) = ⊤ from rfl, idealColon_top, if_pos le_top]
    rw [this, ih]
    change _ = some (K.comap (B.toBase ≫ blowUpToBase Z))
    rw [Scheme.IdealSheafData.comap_comp]

/-- Along a sequence of order `≥ a` for `(K, a)`, the transform `T_r(K, a)` is the ideal of the
iterated birational transform `Π⁻¹_*(K, a)`. -/
private theorem derivedTransform_eq_markedTransform {k : Type u} [Field k] {X : Scheme.{u}}
    {s : X ⟶ Spec (.of k)} {K : X.IdealSheafData} {a : ℕ} {B : ClosedBlowupSequence X}
    (hB : B.IsOrderGePlainSeq s ⟨K, a⟩) :
    B.derivedTransform (some K) a = some (B.markedTransform ⟨K, a⟩).I := by
  induction B with
  | nil X => rfl
  | cons Z B ih =>
    obtain ⟨hsm, -, hZsm, hcodim, hord, hB'⟩ := hB
    have hmul := MarkedIdeal.birationalTransform_mul_eq s hsm Z hZsm hcodim ⟨K, a⟩ hord
    have hstep : derivedTransformStep Z a (some K) =
        some (MarkedIdeal.birationalTransform Z ⟨K, a⟩).I := by
      classical
      simp only [derivedTransformStep]
      rw [if_pos (hmul.symm.le.trans (mul_le_of_le_one_left' le_top))]
      rfl
    change B.derivedTransform (derivedTransformStep Z a (some K)) a = _
    rw [hstep]
    exact ih hB'

/-- The last scheme of a smooth sequence of order `≥ m` starting with a smooth `X` is smooth. -/
private theorem IsOrderGePlainSeq.smooth_toBase {k : Type u} [Field k] {X : Scheme.{u}}
    {s : X ⟶ Spec (.of k)} [Smooth s] {a : MarkedIdeal X} {B : ClosedBlowupSequence X}
    (hB : B.IsOrderGePlainSeq s a) : Smooth (B.toBase ≫ s) := by
  induction B with
  | nil X =>
    change Smooth (𝟙 X ≫ s)
    rw [Category.id_comp]
    infer_instance
  | cons Z B ih =>
    obtain ⟨hsm, -, hZsm, -, -, hB'⟩ := hB
    have : Smooth (blowUpToBase Z ≫ s) :=
      (Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup s Z ⟨hsm, hZsm⟩).1
    have := ih hB'
    change Smooth ((B.toBase ≫ blowUpToBase Z) ≫ s)
    rwa [Category.assoc]

/-- If the centres of `B' ++ (Z, C)` lie in the transforms of `Y ↪ X`, then `Z` lies in the image
of `Y_i → X_i`. -/
private theorem support_subset_range_pullbackHom {X Y : Scheme.{u}} (j : Y ⟶ X)
    [IsClosedImmersion j] (B' : ClosedBlowupSequence X) (Z : B'.target.IdealSheafData)
    (C : ClosedBlowupSequence (blowUp Z)) (h : (B'.append (.cons Z C)).CentersContainedIn j) :
    (Z.support : Set B'.target) ⊆ Set.range (B'.pullbackHom j) := by
  induction B' generalizing Y with
  | nil X =>
    have h1 : j.ker ≤ Z := h.1
    intro x hx
    have hx' : x ∈ (j.ker.support : Set X) := Scheme.IdealSheafData.support_antitone h1 hx
    rw [Scheme.Hom.support_ker, j.isClosedEmbedding.isClosed_range.closure_eq] at hx'
    exact hx'
  | cons Z₀ B' ih =>
    have := Bridges.isClosedImmersion_canonicalLift j Z₀
    exact ih (canonicalLift j Z₀) Z C h.2

/-- An equidimensional scheme of finite type over a field whose components have positive
dimension has all components of the same finite positive dimension. -/
private theorem exists_nat_topologicalKrullDim_eq {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] [QuasiCompact sX]
    (hX : TopologicalSpace.Equidimensional X)
    (hdim : ∀ Z ∈ irreducibleComponents X, 0 < topologicalKrullDim Z) :
    ∃ n : ℕ, 0 < n ∧ ∀ C ∈ irreducibleComponents X, topologicalKrullDim C = n := by
  by_cases h : ∃ C, C ∈ irreducibleComponents X
  · obtain ⟨C, hC⟩ := h
    have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
    have hle : topologicalKrullDim C ≤ topologicalKrullDim X := topologicalKrullDim_subspace_le X C
    have hne := topologicalKrullDim_ne_top_of_locallyOfFiniteType k sX
    have hpos := hdim C hC
    obtain ⟨n, hn⟩ : ∃ n : ℕ, topologicalKrullDim C = n := by
      generalize topologicalKrullDim C = d at hle hpos
      generalize topologicalKrullDim X = e at hle hne
      induction d using WithBot.recBotCoe with
      | bot => exact absurd hpos (not_lt_bot)
      | coe d =>
        induction d using ENat.recTopCoe with
        | top => exact absurd (le_antisymm le_top hle) hne
        | coe d => exact ⟨d, rfl⟩
    refine ⟨n, ?_, fun D hD => (hX D hD C hC).trans hn⟩
    rw [hn] at hpos
    exact_mod_cast hpos
  · push Not at h
    exact ⟨1, one_pos, fun C hC => absurd hC (h C)⟩

/-- Being nonzero at the generic points is inherited by larger ideals. -/
private theorem isNonzeroAtGenericPoints_mono {X : Scheme.{u}} {I J : X.IdealSheafData}
    (hI : IsNonzeroAtGenericPoints I) (h : I ≤ J) : IsNonzeroAtGenericPoints J :=
  fun η hη hJ => hI η hη (eq_bot_iff.2 (hJ ▸ stalk_le_stalk_of_le h η))

/-- With marking `0` restriction commutes with the transform, since both sides are pull-backs:
`(Π_r^* K)|_{S_r} = Π^S_r{}^* (K|_S)`. -/
private theorem derivedTransform_zero_restrict {X : Scheme.{u}} (B : ClosedBlowupSequence X)
    (S : X.IdealSheafData) (K : X.IdealSheafData) :
    (B.restrict S).derivedTransform (some (K.comap S.subschemeι)) 0 =
      some ((K.comap B.toBase).comap (B.restrictHom S)) := by
  rw [derivedTransform_zero, ← Scheme.IdealSheafData.comap_comp,
    ← Scheme.IdealSheafData.comap_comp]
  exact congrArg (fun f => some (K.comap f)) (Kollar.pullbackHom_toBase_comm B S.subschemeι).symm

/-- `T_r(D^j I, m - j)|_{S_r} = T^S_r((D^j I)|_S, m - j)`: restriction to `S_r` commutes with
the transforms of Cor. 3.77. For `j < m` this is Kollár 3.62 along the sequence; for `j = m`
both sides are pull-backs. -/
private theorem derivedTransform_restrict {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [Smooth sX] [LocallyOfFiniteType sX] [QuasiCompact sX]
    (hX : Equidimensional X) (hdim : ∀ Z ∈ irreducibleComponents X, 0 < topologicalKrullDim Z)
    (a : MarkedIdeal X) (ha : IsNonzeroAtGenericPoints a.I) (B : ClosedBlowupSequence X)
    (hB : IsOrderGePlainSeq sX a B) {S : X.IdealSheafData} (hS : IsSmoothHypersurface sX S)
    (hZS : B.CentersContainedIn S.subschemeι)
    (haS : IsNonzeroAtGenericPoints (a.I.comap S.subschemeι)) {j : ℕ} (hj : j ≤ a.m)
    {T : B.target.IdealSheafData} (hT : derivedTransformJ sX B a j = some T) :
    (B.restrict S).derivedTransform
        (some ((higherDerivativeIdeal sX a.I j).comap S.subschemeι)) (a.m - j) =
      some (T.comap (B.restrictHom S)) := by
  obtain hjm | rfl := lt_or_eq_of_le hj
  · obtain ⟨n, hn, hdimn⟩ := exists_nat_topologicalKrullDim_eq sX hX hdim
    obtain ⟨hord, -⟩ := isOrderGePlainSeq_higherDerivativeIdeal sX hX hdim a ha B hB j hj
    have hres := IsOrderGePlainSeq.restrict sX ⟨n, hn, hdimn⟩ hS (Nat.sub_pos_of_lt hjm)
      (Proof_thm_kr3d_log_decomposition_of_derivatives.isNonzeroAtGenericPoints_of_isOrderGePlainSeq
        hord)
      (fun η => isNonzeroAtGenericPoints_mono haS (Scheme.IdealSheafData.comap_mono _
        (le_higherDerivativeIdeal_and_multAt sX hX hdim ha j (S.subschemeι η)).1) η) hord
      (by rintro B' Z C rfl; exact support_subset_range_pullbackHom S.subschemeι B' Z C hZS)
    have h2 := hres.2 B.length
    rw [Proof_thm_kr3d_log_decomposition_of_derivatives.truncate_length] at h2
    rw [derivedTransform_eq_markedTransform hres.1, h2,
      ← Option.some.inj (hT.symm.trans (derivedTransform_eq_markedTransform hord))]
  · unfold derivedTransformJ at hT
    rw [Nat.sub_self] at hT ⊢
    rw [derivedTransform_zero_restrict, ← Option.some.inj (hT.symm.trans
      (derivedTransform_zero B _))]

end Proof_lem_kr3d_restricted_log_decomposition

namespace MMP.Resolution.ClosedBlowupSequence

open Proof_lem_kr3d_restricted_log_decomposition in
/-- **Restricted logarithmic decomposition of derivatives** (Kollár (3.89.1)). In the setting of
`higherDerivativeIdeal_markedTransform_eq_iSup`, assume moreover `1 ≤ m` and that `I|_S` is
nonzero at the generic points of `S`. Then for `s ≤ m` each transform
`T^S_r((D^j I)|_S, m - j)`, `j ≤ s`, along the restricted sequence `B.restrict S` is an ideal
sheaf `J j` on `S_r`, and the restriction of `D^s(I_r)` to `S_r` along `B.restrictHom S` is the
supremum over `j ≤ s` of `D^{s-j}(J j)`, derivatives taken on `S_r` over `k`. -/
@[mmp "lem_kr3d_restricted_log_decomposition"]
public theorem higherDerivativeIdeal_markedTransform_comap_restrictHom_eq_iSup {k : Type u}
    [Field k] [CharZero k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX]
    [QuasiCompact sX] (hX : Equidimensional X)
    (hdim : ∀ Z ∈ irreducibleComponents X, 0 < topologicalKrullDim Z)
    (a : MarkedIdeal X) (ha : IsNonzeroAtGenericPoints a.I) (hm : 1 ≤ a.m)
    (B : ClosedBlowupSequence X) (hB : IsOrderGePlainSeq sX a B)
    {S : X.IdealSheafData} (hS : IsSmoothHypersurface sX S)
    (hZS : B.CentersContainedIn S.subschemeι)
    (haS : IsNonzeroAtGenericPoints (a.I.comap S.subschemeι))
    {s : ℕ} (hs : s ≤ a.m) :
    ∃ J : ℕ → (B.restrict S).target.IdealSheafData,
      (∀ j ≤ s, (B.restrict S).derivedTransform
          (some ((higherDerivativeIdeal sX a.I j).comap S.subschemeι)) (a.m - j) = some (J j)) ∧
      (higherDerivativeIdeal (B.toBase ≫ sX) (B.markedTransform a).I s).comap (B.restrictHom S) =
        ⨆ (j : ℕ) (_ : j ≤ s),
          higherDerivativeIdeal ((B.restrict S).toBase ≫ S.subschemeι ≫ sX) (J j) (s - j) := by
  have hsm : MMP.Mori.IsSmoothScheme sX := by cases B <;> exact hB.1
  have : Smooth sX := (MMP.Mori.isSmoothScheme_iff sX).1 hsm
  obtain ⟨J, hJ, hdec⟩ :=
    higherDerivativeIdeal_markedTransform_eq_iSup sX hX hdim a ha B hB hS hZS hs
  have : Smooth (B.toBase ≫ sX) := IsOrderGePlainSeq.smooth_toBase hB
  have : IsClosedImmersion (B.restrictHom S) :=
    Kollar.isClosedImmersion_pullbackHom B S.subschemeι
  refine ⟨fun j => (J j).comap (B.restrictHom S), fun j hj =>
    derivedTransform_restrict sX hX hdim a ha B hB hS hZS haS (hj.trans hs) (hJ j hj), ?_⟩
  rw [hdec, (Scheme.IdealSheafData.map_gc (B.restrictHom S)).l_iSup₂]
  refine iSup_congr fun j => iSup_congr fun _ => ?_
  rw [comap_higherLogDerivativeIdeal_ker, ← Category.assoc,
    show B.restrictHom S ≫ B.toBase = (B.restrict S).toBase ≫ S.subschemeι from
      Kollar.pullbackHom_toBase_comm B S.subschemeι, Category.assoc]

end MMP.Resolution.ClosedBlowupSequence

end

/-!
## Cosupport of the restricted transform via derivatives

In the setting of
`ClosedBlowupSequence.higherDerivativeIdeal_markedTransform_comap_restrictHom_eq_iSup`
(a smooth blow-up sequence `Π = (X_i, Z_i)_{i ≤ r}` of order `≥ m ≥ 1` starting with `(X, I, m)`,
a smooth hypersurface `S ⊆ X` whose transforms `S_i` contain the centres `Z_i`, and `I|_S`
nonzero on every irreducible component of `S`), every transform `A_j = T^S_r((D^j I)|_S, m - j)`,
`j < m`, along the restricted sequence `Π|_S` is an ideal sheaf on `S_r`, and
`S_r ∩ cosupp(I_r, m) = ⋂_{j < m} cosupp(A_j, m - j)`.

## Main results

* `MMP.Resolution.ClosedBlowupSequence.restrictHom_preimage_cosupport_markedTransform_eq_iInter`

## Implementation notes

The intersection `S_r ∩ cosupp(I_r, m)` is expressed on `S_r` as the preimage of
`cosupp(I_r, m)` under the closed immersion `S_r → X_r`, `Π.restrictHom S`. The transform
`T^S_r(K, a)` is `derivedTransform` along `Π.restrict S` applied to `some K`; it is
`Option`-valued, so the statement provides the family `J` of ideal sheaves it takes.

## References

* [J. Kollár, *Lectures on resolution of singularities*, Cor. 3.89][kollar2007]
-/

section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Resolution IsLocalRing
open ClosedBlowupSequence

namespace Proof_lem_kr3d_cosupport_restriction_via_derivatives

section LocalAlgebra

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A] [IsLocalRing A]

/-- A derivation maps `𝔪^(n+1)` into `𝔪^n` (Leibniz rule). -/
private theorem derivation_mem_maximalIdeal_pow (δ : Derivation k A A) :
    ∀ {n : ℕ} {f : A}, f ∈ maximalIdeal A ^ (n + 1) → δ f ∈ maximalIdeal A ^ n
  | 0, _, _ => by simp
  | n + 1, f, hf => by
    rw [pow_succ] at hf
    refine Submodule.mul_induction_on hf (fun a ha b hb => ?_) (fun x y hx hy => ?_)
    · rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      refine add_mem (Ideal.mul_mem_right _ _ ha) ?_
      rw [pow_succ]
      exact mul_comm (δ a) b ▸ Ideal.mul_mem_mul (derivation_mem_maximalIdeal_pow δ ha) hb
    · rw [map_add]; exact add_mem hx hy

/-- If `J ⊆ 𝔪^(n+1)` then `D(J) ⊆ 𝔪^n`. -/
private theorem derivativeIdealOfRing_le_pow {J : Ideal A} {n : ℕ}
    (h : J ≤ maximalIdeal A ^ (n + 1)) : derivativeIdealOfRing k J ≤ maximalIdeal A ^ n :=
  Ideal.span_le.mpr (by rintro _ ⟨δ, f, hf, rfl⟩; exact derivation_mem_maximalIdeal_pow δ (h hf))

/-- A derivative lowers the order of an ideal of a local ring by at most one. -/
private theorem idealOrder_sub_one_le (J : Ideal A) :
    idealOrder J - 1 ≤ idealOrder (derivativeIdealOfRing k J) := by
  refine ENat.forall_natCast_le_iff_le.mp fun n hn => ?_
  rcases n with _ | n
  · simp
  · rw [natCast_le_idealOrder_iff']
    refine derivativeIdealOfRing_le_pow ((natCast_le_idealOrder_iff' _ _).mp ?_)
    have h1 : 1 ≤ idealOrder J := by
      by_contra h
      push Not at h
      rw [ENat.lt_one_iff_eq_zero] at h
      rw [h] at hn
      simp at hn
    calc ((n + 1 + 1 : ℕ) : ℕ∞) = ((n + 1 : ℕ) : ℕ∞) + 1 := by push_cast; rfl
      _ ≤ idealOrder J - 1 + 1 := by gcongr
      _ = idealOrder J := tsub_add_cancel_of_le h1

end LocalAlgebra

/-- For `1 ≤ m`, `1 ≤ a - (m - 1)` iff `m ≤ a` in `ℕ∞`. -/
private lemma one_le_sub_pred_iff {m : ℕ} (hm : 1 ≤ m) (a : ℕ∞) :
    1 ≤ a - ((m - 1 : ℕ) : ℕ∞) ↔ (m : ℕ∞) ≤ a := by
  induction a using ENat.recTopCoe with
  | top => simp only [ENat.top_sub_coe, le_top]
  | coe a =>
    rw [← ENat.coe_sub, ← Nat.cast_one, Nat.cast_le, Nat.cast_le]
    omega

private theorem idealOrder_le_of_map {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S]
    [IsLocalRing S] (φ : R →+* S) [IsLocalHom φ] (I : Ideal R) :
    idealOrder I ≤ idealOrder (I.map φ) := by
  unfold idealOrder
  refine iSup₂_le fun j hj => le_iSup₂_of_le j ?_ le_rfl
  calc I.map φ ≤ (IsLocalRing.maximalIdeal R ^ j).map φ := Ideal.map_mono hj
    _ = ((IsLocalRing.maximalIdeal R).map φ) ^ j := Ideal.map_pow _ _ _
    _ ≤ IsLocalRing.maximalIdeal S ^ j := by
      refine Ideal.pow_right_mono ?_ j
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      exact fun h => ha (isUnit_of_map_unit φ a h)

section Scheme

/-- Orders do not drop under pull-back of ideal sheaves. -/
private theorem multAt_le_multAt_comap {X Y : Scheme.{u}} (f : Y ⟶ X) (K : X.IdealSheafData)
    (y : Y) : multAt K (f y) ≤ multAt (K.comap f) y := by
  unfold multAt
  rw [IdealSheafData.stalk_comap]
  exact idealOrder_le_of_map _ _

/-- `x ∈ V(K)` iff `ord_x K ≥ 1`. -/
private lemma mem_support_iff_one_le_multAt {X : Scheme} (K : X.IdealSheafData) (x : X) :
    x ∈ (K.support : Set X) ↔ 1 ≤ multAt K x := by
  rw [show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) by simp, multAt, natCast_le_idealOrder_iff', pow_one]
  refine ⟨fun hx => IsLocalRing.le_maximalIdeal fun h =>
    ((IdealSheafData.stalk_eq_top_iff_notMem_support K x).1 h) hx, fun h => ?_⟩
  by_contra hx
  rw [(IdealSheafData.stalk_eq_top_iff_notMem_support K x).2 hx] at h
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.mp h)

/-- On a scheme locally of finite type over a field, the first derivative lowers the order of an
ideal sheaf at a point by at most one. -/
private theorem multAt_sub_one_le_multAt_derivativeIdeal {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (I : X.IdealSheafData) (x : X) :
    multAt I x - 1 ≤ multAt (derivativeIdeal sX I) x := by
  classical
  obtain ⟨W, hW, hxW, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)
  let := MMP.Mori.sectionAlgebra sX W
  let := MMP.Mori.stalkAlgebra sX x
  let : Algebra Γ(X, W) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxW⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk x) (hW.primeIdealOf ⟨x, hxW⟩).asIdeal :=
    hW.isLocalization_stalk ⟨x, hxW⟩
  have : IsScalarTower k Γ(X, W) (X.presheaf.stalk x) :=
    MMP.Mori.isScalarTower_section_stalk sX W ⟨x, hxW⟩
  have : Algebra.FinitePresentation k Γ(X, W) :=
    Algebra.FinitePresentation.of_finiteType.mp (MMP.Mori.finiteType_sectionAlgebra sX hW)
  have hstalk : ∀ J : X.IdealSheafData, IdealSheafData.stalk J x =
      (J.ideal ⟨W, hW⟩).map (algebraMap Γ(X, W) (X.presheaf.stalk x)) := fun J =>
    IdealSheafData.stalk_eq_map_germ J x ⟨W, hW⟩ hxW
  have hD : IdealSheafData.stalk (derivativeIdeal sX I) x =
      derivativeIdealOfRing k (IdealSheafData.stalk I x) := by
    rw [hstalk, hstalk, derivativeIdeal_ideal, sectionDerivativeIdeal]
    exact derivativeIdealOfRing_map_localization (hW.primeIdealOf ⟨x, hxW⟩).asIdeal.primeCompl _
  unfold multAt
  rw [hD]
  exact idealOrder_sub_one_le _

/-- On a scheme locally of finite type over a field, `ord_x D^t(I) ≥ ord_x I - t`. -/
private theorem multAt_sub_le_multAt_higherDerivativeIdeal {k : Type u} [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (I : X.IdealSheafData)
    (x : X) (t : ℕ) : multAt I x - t ≤ multAt (higherDerivativeIdeal sX I t) x := by
  induction t with
  | zero => simp [higherDerivativeIdeal_zero]
  | succ t ih =>
    rw [higherDerivativeIdeal_succ, Nat.cast_succ, ← tsub_tsub]
    exact (tsub_le_tsub_right ih 1).trans (multAt_sub_one_le_multAt_derivativeIdeal sX _ x)

end Scheme

section Sequence

/-- The last ideal of a sequence of order `≥ m` is nonzero at the generic points. -/
private theorem IsOrderGePlainSeq.isNonzeroAtGenericPoints_markedTransform {k : Type u}
    [Field k] {X : Scheme.{u}} {s : X ⟶ Spec (.of k)} {a : MarkedIdeal X}
    {B : ClosedBlowupSequence X} (hB : B.IsOrderGePlainSeq s a) :
    IsNonzeroAtGenericPoints (B.markedTransform a).I := by
  induction B with
  | nil X => exact hB.2
  | cons Z B ih => exact ih hB.2.2.2.2.2

/-- A smooth sequence of order `≥ m` is a smooth blow-up sequence. -/
private theorem IsOrderGePlainSeq.isSmooth {k : Type u} [Field k] {X : Scheme.{u}}
    {s : X ⟶ Spec (.of k)} {a : MarkedIdeal X} {B : ClosedBlowupSequence X}
    (hB : B.IsOrderGePlainSeq s a) : B.IsSmooth s := by
  induction B with
  | nil X => trivial
  | cons Z B ih => exact ⟨hB.1, hB.2.2.1, ih hB.2.2.2.2.2⟩

/-- The last scheme of a blow-up sequence starting with a scheme of finite type over `k` is of
finite type over `k`. -/
private theorem finiteType_toBase {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s] [QuasiCompact s] (B : ClosedBlowupSequence X) :
    LocallyOfFiniteType (B.toBase ≫ s) ∧ QuasiCompact (B.toBase ≫ s) := by
  induction B with
  | nil X =>
    change LocallyOfFiniteType (𝟙 X ≫ s) ∧ QuasiCompact (𝟙 X ≫ s)
    rw [Category.id_comp]
    exact ⟨inferInstance, inferInstance⟩
  | cons Z B ih =>
    have : IsLocallyNoetherian _ := LocallyOfFiniteType.isLocallyNoetherian s
    have : IsProper (blowUpToBase Z) := AlgebraicGeometry.isProper_blowUpToBase (I := Z)
    obtain ⟨h1, h2⟩ := ih (blowUpToBase Z ≫ s)
    change LocallyOfFiniteType ((B.toBase ≫ blowUpToBase Z) ≫ s) ∧
      QuasiCompact ((B.toBase ≫ blowUpToBase Z) ≫ s)
    rw [Category.assoc]
    exact ⟨h1, h2⟩

end Sequence

open ClosedBlowupSequence in
/-- Along a sequence of order `≥ m` for `(I, m)`, the transform of `(D^j I, m - j)` is contained
in `D^j` of the transform `I_r` of `I`. -/
private theorem markedTransform_higherDerivativeIdeal_le {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] [QuasiCompact sX]
    (hX : Equidimensional X) (hdim : ∀ Z ∈ irreducibleComponents X, 0 < topologicalKrullDim Z)
    (a : MarkedIdeal X) (ha : IsNonzeroAtGenericPoints a.I) (B : ClosedBlowupSequence X)
    (hB : B.IsOrderGePlainSeq sX a) {j : ℕ} (hj : j ≤ a.m) :
    (B.markedTransform ⟨higherDerivativeIdeal sX a.I j, a.m - j⟩).I ≤
      higherDerivativeIdeal (B.toBase ≫ sX) (B.markedTransform a).I j := by
  have key : ((B.truncate B.length).markedTransform ⟨higherDerivativeIdeal sX a.I j, a.m - j⟩).I ≤
      higherDerivativeIdeal ((B.truncate B.length).toBase ≫ sX)
        ((B.truncate B.length).markedTransform a).I j := by
    obtain ⟨T, hT, hTle⟩ :=
      derivedTransformJ_truncate_le_higherDerivativeIdeal sX hX hdim a ha B hB _ le_rfl j hj
    have h2 := (isOrderGePlainSeq_higherDerivativeIdeal sX hX hdim a ha B hB j hj).2 _ le_rfl
    rw [hT] at h2
    rwa [← Option.some.inj h2]
  rwa [Proof_thm_kr3d_log_decomposition_of_derivatives.truncate_length] at key

end Proof_lem_kr3d_cosupport_restriction_via_derivatives

namespace MMP.Resolution.ClosedBlowupSequence

open Proof_lem_kr3d_cosupport_restriction_via_derivatives
    Proof_lem_kr3d_restricted_log_decomposition in
/-- **Cosupport of the restricted transform via derivatives** (Kollár Cor. 3.89). In the setting
of `higherDerivativeIdeal_markedTransform_comap_restrictHom_eq_iSup`, each transform
`T^S_r((D^j I)|_S, m - j)`, `j < m`, along `B.restrict S` is an ideal sheaf `J j` on `S_r`, and
the preimage under `B.restrictHom S : S_r → X_r` of the cosupport of the marked transform
`(I_r, m)` is the intersection over `j < m` of the cosupports of `(J j, m - j)`. -/
@[mmp "lem_kr3d_cosupport_restriction_via_derivatives"]
public theorem restrictHom_preimage_cosupport_markedTransform_eq_iInter {k : Type u}
    [Field k] [CharZero k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX]
    [QuasiCompact sX] (hX : Equidimensional X)
    (hdim : ∀ Z ∈ irreducibleComponents X, 0 < topologicalKrullDim Z)
    (a : MarkedIdeal X) (ha : IsNonzeroAtGenericPoints a.I) (hm : 1 ≤ a.m)
    (B : ClosedBlowupSequence X) (hB : IsOrderGePlainSeq sX a B)
    {S : X.IdealSheafData} (hS : IsSmoothHypersurface sX S)
    (hZS : B.CentersContainedIn S.subschemeι)
    (haS : IsNonzeroAtGenericPoints (a.I.comap S.subschemeι)) :
    ∃ J : ℕ → (B.restrict S).target.IdealSheafData,
      (∀ j < a.m, (B.restrict S).derivedTransform
          (some ((higherDerivativeIdeal sX a.I j).comap S.subschemeι)) (a.m - j) = some (J j)) ∧
      (B.restrictHom S).base ⁻¹' (B.markedTransform a).cosupport =
        ⋂ (j : ℕ) (_ : j < a.m), (⟨J j, a.m - j⟩ : MarkedIdeal _).cosupport := by
  have hsm : MMP.Mori.IsSmoothScheme sX := by cases B <;> exact hB.1
  have : Smooth sX := (MMP.Mori.isSmoothScheme_iff sX).1 hsm
  obtain ⟨n, hn, hdimn⟩ := exists_nat_topologicalKrullDim_eq sX hX hdim
  obtain ⟨J, hJ, hdec⟩ := higherDerivativeIdeal_markedTransform_comap_restrictHom_eq_iSup sX hX
    hdim a ha hm B hB hS hZS haS (s := a.m - 1) (Nat.sub_le _ _)
  refine ⟨J, fun j hj => hJ j (by omega), ?_⟩
  have : Smooth (B.toBase ≫ sX) := IsOrderGePlainSeq.smooth_toBase hB
  have hXr := (IsSmooth.truncate_target_equidimensional sX hdimn
    (IsOrderGePlainSeq.isSmooth hB) B.length).2
  rw [Proof_thm_kr3d_log_decomposition_of_derivatives.truncate_length] at hXr
  have hXr' : Equidimensional B.target := fun C hC W hW => by
    rw [(hXr C hC).1, (hXr W hW).1]
  have hdimr : ∀ C ∈ irreducibleComponents B.target, 0 < topologicalKrullDim C := fun C hC => by
    rw [(hXr C hC).1]
    exact_mod_cast hn
  have : QuasiCompact (B.toBase ≫ sX) := (finiteType_toBase sX B).2
  have : LocallyOfFiniteType ((B.restrict S).toBase ≫ S.subschemeι ≫ sX) :=
    (finiteType_toBase (S.subschemeι ≫ sX) (B.restrict S)).1
  have hIr := IsOrderGePlainSeq.isNonzeroAtGenericPoints_markedTransform hB
  -- `A_j = (D^j I)_r|_{S_r}` for `j < m`.
  have hJj : ∀ j < a.m, J j = (B.markedTransform
      ⟨higherDerivativeIdeal sX a.I j, a.m - j⟩).I.comap (B.restrictHom S) := by
    intro j hjm
    obtain ⟨hord, -⟩ := isOrderGePlainSeq_higherDerivativeIdeal sX hX hdim a ha B hB j hjm.le
    have hnzS : IsNonzeroAtGenericPoints
        ((higherDerivativeIdeal sX a.I j).comap S.subschemeι) := fun η hη hbot =>
      haS η hη (eq_bot_iff.2 (hbot ▸ stalk_le_stalk_of_le (Scheme.IdealSheafData.comap_mono
        S.subschemeι (le_higherDerivativeIdeal_and_multAt sX hX hdim ha j
          (S.subschemeι η)).1) η))
    have hres := IsOrderGePlainSeq.restrict sX ⟨n, hn, hdimn⟩ hS (Nat.sub_pos_of_lt hjm)
      (Proof_thm_kr3d_log_decomposition_of_derivatives.isNonzeroAtGenericPoints_of_isOrderGePlainSeq
        hord) hnzS hord
      (by rintro B' Z C rfl; exact support_subset_range_pullbackHom S.subschemeι B' Z C hZS)
    have h2 := hres.2 B.length
    rw [Proof_thm_kr3d_log_decomposition_of_derivatives.truncate_length] at h2
    have h3 := (hJ j (by omega)).symm.trans (derivedTransform_eq_markedTransform hres.1)
    rw [h2] at h3
    exact Option.some.inj h3
  have hmult : ∀ (j : ℕ) (y : B.target),
      multAt (higherDerivativeIdeal (B.toBase ≫ sX) (B.markedTransform a).I j) y =
        multAt (B.markedTransform a).I y - j :=
    fun j y => (le_higherDerivativeIdeal_and_multAt (B.toBase ≫ sX) hXr' hdimr hIr j y).2
  ext x
  simp only [Set.mem_preimage, Set.mem_iInter, MarkedIdeal.cosupport, Set.mem_setOf_eq,
    markedTransform_m]
  constructor
  · intro hx j hj
    rw [hJj j hj]
    calc ((a.m - j : ℕ) : ℕ∞) ≤ multAt (B.markedTransform a).I (B.restrictHom S x) - j := by
          rw [ENat.coe_sub]
          exact tsub_le_tsub_right hx _
      _ = multAt (higherDerivativeIdeal (B.toBase ≫ sX) (B.markedTransform a).I j)
          (B.restrictHom S x) := (hmult j _).symm
      _ ≤ multAt (B.markedTransform ⟨higherDerivativeIdeal sX a.I j, a.m - j⟩).I
          (B.restrictHom S x) := Kollar.multAt_antitone
            (markedTransform_higherDerivativeIdeal_le sX hX hdim a ha B hB hj.le) _
      _ ≤ _ := multAt_le_multAt_comap (B.restrictHom S) _ x
  · intro hx
    have hmem : x ∈ (((higherDerivativeIdeal (B.toBase ≫ sX) (B.markedTransform a).I
        (a.m - 1)).comap (B.restrictHom S)).support : Set _) := by
      rw [hdec]
      simp only [Scheme.IdealSheafData.support_iSup, Closeds.coe_iInf, Set.mem_iInter]
      intro j hj
      rw [mem_support_iff_one_le_multAt]
      refine le_trans ?_ (multAt_sub_le_multAt_higherDerivativeIdeal _ (J j) x (a.m - 1 - j))
      rw [show a.m - 1 - j = a.m - j - 1 by omega]
      exact (one_le_sub_pred_iff (by omega) _).2 (hx j (by omega))
    rw [Scheme.IdealSheafData.support_comap] at hmem
    have hρ := (mem_support_iff_one_le_multAt _ _).1 hmem
    rw [hmult] at hρ
    exact (one_le_sub_pred_iff hm _).1 hρ

end MMP.Resolution.ClosedBlowupSequence

end

/-!
## The inductive step of the going-up property of `D`-balanced ideals

Let `X` be smooth, equidimensional of positive dimension and of finite type over a field `k` of
characteristic `0`, `I` a `D`-balanced ideal sheaf nonzero on every irreducible component of `X`
with `m = maxord I ≥ 1`, and `S ⊆ X` a smooth hypersurface none of whose irreducible components
lies in `cosupp(I, m)`. Let `𝐁^X = (X_i, Z_i)_{i ≤ r + 1}` be a push-forward of a smooth
blow-up sequence `𝐁(S) = (S_i, Z_i)` of order `≥ m` starting with `(S, I|_S, m)`, with marked
ideals `(J_i, m)`, and suppose the first `r` blow-ups of `𝐁^X` form a smooth blow-up sequence
of order `≥ m` starting with `(X, I, m)`, with marked ideals `(I_i, m)`. Then
`cosupp(J_r, m) ⊆ S_r ∩ cosupp(I_r, m)`, i.e. the image of `cosupp(J_r, m)` under the
closed immersion `j_r : S_r → X_r` lies in `cosupp(I_r, m)`.

## Main results

* `MMP.Resolution.ClosedBlowupSequence.image_cosupport_restrict_subset_of_isDBalanced`

## Implementation notes

Since a push-forward `𝐁^X` of `𝐁(S)` along `S ↪ X` restricts back to `𝐁(S)`
(`MMP.Resolution.ClosedBlowupSequence.restrict_eq_of_isPushforward`), the sequence `𝐁(S)` is
written as the restriction `𝐁^X|_S`; its `i`-th scheme, morphism `j_i : S_i → X_i` and marked
ideal are read on the truncation `𝐁^X.truncate i`. The containment `cosupp(J_r, m) ⊆ S_r` is
the statement that the cosupport is taken on `S_r`; the content is its image under `j_r`.

## References

* [J. Kollár, *Lectures on resolution of singularities*, 3.84, 3.90]
-/

section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace
open MMP MMP.Resolution MMP.Resolution.ClosedBlowupSequence

variable {k : Type u} [Field k]

namespace Proof_lem_kr3d_going_up_inductive_step

/-- The centres of a push-forward along `j` lie in the image of `j`. -/
private theorem centersContainedIn_of_isPushforward :
    ∀ {S X : Scheme.{u}} (j : S ⟶ X) (BS : ClosedBlowupSequence S)
      (BX : ClosedBlowupSequence X), IsPushforward j BS BX → BX.CentersContainedIn j
  | _, _, _, .nil _, .nil _, _ => trivial
  | _, _, j, .cons ZS BS, .cons ZX BX, h => by
    obtain ⟨rfl, hmap, hP⟩ := h
    simp only [eqToHom_refl, Category.id_comp] at hP
    refine ⟨?_, centersContainedIn_of_isPushforward _ BS BX hP⟩
    rw [hmap, ← Scheme.IdealSheafData.map_bot]
    exact (Scheme.IdealSheafData.map_gc j).monotone_u bot_le
  | _, _, _, .nil _, .cons _ _, h => h.elim
  | _, _, _, .cons _ _, .nil _, h => h.elim

private theorem centersContainedIn_truncate :
    ∀ {X S : Scheme.{u}} (B : ClosedBlowupSequence X) (j : S ⟶ X) (i : ℕ),
      B.CentersContainedIn j → (B.truncate i).CentersContainedIn j
  | _, _, .nil _, _, _, _ => trivial
  | _, _, .cons _ _, _, 0, _ => trivial
  | _, _, .cons _ B, _, i + 1, h => ⟨h.1, centersContainedIn_truncate B _ i h.2⟩

private theorem isOrderGePlainSeq_truncate :
    ∀ {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) (a : MarkedIdeal X) (B : ClosedBlowupSequence X)
      (i : ℕ), B.IsOrderGePlainSeq s a → (B.truncate i).IsOrderGePlainSeq s a
  | _, _, _, .nil _, _, h => h
  | _, _, _, .cons _ _, 0, h => ⟨h.1, h.2.1⟩
  | _, _, _, .cons _ B, i + 1, h =>
    ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, isOrderGePlainSeq_truncate _ _ B i h.2.2.2.2.2⟩

/-- Multiplication by an effective Cartier divisor reflects the order on ideal sheaves. -/
private theorem le_of_mul_le_mul_left_of_isEffectiveCartierDivisor {X : Scheme.{u}}
    {E A B : X.IdealSheafData} (hE : Stacks.Divisors.IsEffectiveCartierDivisor E)
    (h : E * A ≤ E * B) : A ≤ B := by
  have h' : E * (A ⊔ B) = E * B := by
    rw [Scheme.IdealSheafData.mul_inf, sup_eq_right.mpr h]
  exact sup_eq_right.mp (Stacks.Divisors.eq_of_mul_eq_mul_of_isEffectiveCartierDivisor hE h')

/-- Along a smooth blow-up sequence of order `≥ m` starting with `(X, I, m)`, if `K ^ p ⊆ I ^ q`
with `c p = m q` and `p, q ≠ 0`, and the transform `T_r(K, c)` is an ideal sheaf `J`, then
`cosupp(I_r, m) ⊆ cosupp(J, c)`. The transform is allowed to start at `none`. -/
private theorem cosupport_markedTransform_subset_of_pow_le {c p q : ℕ} (hp : p ≠ 0)
    (hq : q ≠ 0) :
    ∀ {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) (a : MarkedIdeal X) (B : ClosedBlowupSequence X),
      B.IsOrderGePlainSeq s a → c * p = a.m * q →
      ∀ (T : Option X.IdealSheafData), (∀ t, T = some t → t ^ p ≤ a.I ^ q) →
      ∀ J, B.derivedTransform T c = some J →
        (B.markedTransform a).cosupport ⊆ (⟨J, c⟩ : MarkedIdeal _).cosupport
  | X, s, a, .nil _, hB, hpq, T, hT, J, hJ => by
    have hJp : J ^ p ≤ a.I ^ q := hT J hJ
    have : Smooth s := hB.1.smooth
    have : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x) :=
      isRegularLocalRing_stalk_of_smooth_over_field s
    -- `J` lives on `(nil X).target`; retype it as an ideal sheaf on `X`.
    obtain ⟨J', rfl⟩ : ∃ J' : X.IdealSheafData, J' = J := ⟨J, rfl⟩
    change (⟨a.I, a.m⟩ : MarkedIdeal X).cosupport ⊆ (⟨J', c⟩ : MarkedIdeal X).cosupport
    rw [MarkedIdeal.cosupport_pow a.I a.m hq, MarkedIdeal.cosupport_pow J' c hp, hpq]
    exact Kollar.cosupport_subset_of_le hJp _
  | X, s, a, .cons Z B, hB, hpq, T, hT, J, hJ => by
    obtain ⟨hs, -, hZs, hcodim, hord, hB'⟩ := hB
    refine cosupport_markedTransform_subset_of_pow_le hp hq _ (a.birationalTransform Z) B hB'
      hpq (derivedTransformStep Z c T) ?_ J hJ
    have hF : Stacks.Divisors.IsEffectiveCartierDivisor (Z.comap (blowUpToBase Z)) :=
      Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal Z
    have hb := MarkedIdeal.birationalTransform_mul_eq s hs Z hZs hcodim a hord
    intro t' ht'
    cases T with
    | none =>
      cases ht'
      rw [← Scheme.IdealSheafData.zero_eq_bot, zero_pow hp]
      exact bot_le
    | some t =>
      refine le_of_mul_le_mul_left_of_isEffectiveCartierDivisor
        (Stacks.Divisors.isEffectiveCartierDivisor_pow hF (c * p)) ?_
      calc Z.comap (blowUpToBase Z) ^ (c * p) * t' ^ p
          = (t' * Z.comap (blowUpToBase Z) ^ c) ^ p := by rw [mul_pow, ← pow_mul, mul_comm]
        _ = (t ^ p).comap (blowUpToBase Z) := by
          rw [derivedTransformStep_mul_eq Z c t t' ht' hF, Stacks.IdealSheaf.comap_pow]
        _ ≤ (a.I ^ q).comap (blowUpToBase Z) := Scheme.IdealSheafData.comap_mono _ (hT t rfl)
        _ = ((a.birationalTransform Z).I * Z.comap (blowUpToBase Z) ^ a.m) ^ q := by
          rw [Stacks.IdealSheaf.comap_pow, hb]
        _ = Z.comap (blowUpToBase Z) ^ (c * p) * (a.birationalTransform Z).I ^ q := by
          rw [mul_pow, ← pow_mul, hpq, mul_comm]

end Proof_lem_kr3d_going_up_inductive_step

namespace MMP.Resolution.ClosedBlowupSequence

open Proof_lem_kr3d_going_up_inductive_step
    Proof_lem_kr3d_restricted_log_decomposition in
/-- **Inductive step of the going-up property** (Kollár 3.90). Let `X` be smooth, equidimensional
of positive dimension and of finite type over a field `k` of characteristic `0`, `I` a
`D`-balanced ideal sheaf on `X`, nonzero on every irreducible component, with `maxord I = m ≥ 1`,
and `S ⊆ X` a smooth hypersurface no irreducible component of which lies in `cosupp(I, m)`. Let
`BX` be a blow-up sequence of length `r + 1` which is a push-forward of its restriction `BX|_S`
along `S ↪ X`, such that `BX|_S` is a smooth blow-up sequence of order `≥ m` starting with
`(S, I|_S, m)` and the truncation `BX.truncate r` is one starting with `(X, I, m)`. Then the
`r`-th morphism `j_r : S_r → X_r` maps the cosupport of the `r`-th marked ideal `(J_r, m)` of
`BX|_S` into the cosupport of the `r`-th marked ideal `(I_r, m)` of `BX`. -/
@[mmp "lem_kr3d_going_up_inductive_step"]
public theorem image_cosupport_restrict_subset_of_isDBalanced {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [Smooth sX] [QuasiCompact sX]
    (hdim : ∃ n : ℕ, 0 < n ∧ ∀ C ∈ irreducibleComponents X, topologicalKrullDim C = n)
    {I : X.IdealSheafData} (hDB : IsDBalanced sX I) (hI : IsNonzeroAtGenericPoints I)
    {m : ℕ} (hm : maxOrder I = m) (hm1 : 1 ≤ m)
    {S : X.IdealSheafData} (hS : IsSmoothHypersurface sX S)
    (hSC : ∀ C ∈ irreducibleComponents S.subscheme,
      ¬ S.subschemeι '' C ⊆ (⟨I, m⟩ : MarkedIdeal X).cosupport)
    {r : ℕ} {BX : ClosedBlowupSequence X} (hr : BX.length = r + 1)
    (hP : IsPushforward S.subschemeι (BX.restrict S) BX)
    (hBS : (BX.restrict S).IsOrderGePlainSeq (S.subschemeι ≫ sX) ⟨I.comap S.subschemeι, m⟩)
    (hBX : (BX.truncate r).IsOrderGePlainSeq sX ⟨I, m⟩) :
    (BX.truncate r).restrictHom S ''
        (((BX.truncate r).restrict S).markedTransform ⟨I.comap S.subschemeι, m⟩).cosupport ⊆
      ((BX.truncate r).markedTransform ⟨I, m⟩).cosupport := by
  obtain ⟨n, hn0, hn⟩ := hdim
  have hEq : Equidimensional X := fun W hW Z hZ => (hn W hW).trans (hn Z hZ).symm
  have hpos : ∀ Z ∈ irreducibleComponents X, 0 < topologicalKrullDim Z := fun Z hZ => by
    rw [hn Z hZ]; exact_mod_cast hn0
  have hZS : (BX.truncate r).CentersContainedIn S.subschemeι :=
    centersContainedIn_truncate BX _ r (centersContainedIn_of_isPushforward _ _ BX hP)
  have hBS' : ((BX.truncate r).restrict S).IsOrderGePlainSeq (S.subschemeι ≫ sX)
      ⟨I.comap S.subschemeι, m⟩ := by
    have h := isOrderGePlainSeq_truncate _ _ _ r hBS
    rwa [ClosedBlowupSequence.restrict, Kollar.pullback_truncate] at h
  have haS :=
    Proof_thm_kr3d_log_decomposition_of_derivatives.isNonzeroAtGenericPoints_of_isOrderGePlainSeq
      hBS'
  obtain ⟨A, hA, heq⟩ := restrictHom_preimage_cosupport_markedTransform_eq_iInter sX hEq hpos
    (⟨I, m⟩ : MarkedIdeal X) hI hm1 (BX.truncate r) hBX hS hZS haS
  rintro _ ⟨x, hx, rfl⟩
  rw [← Set.mem_preimage, heq, Set.mem_iInter₂]
  intro j hj
  change j < m at hj
  have hDBj : higherDerivativeIdeal sX I j ^ m ≤ I ^ (m - j) := by
    simpa only [hm, ENat.toNat_coe] using hDB j (by rw [hm]; exact hj)
  refine cosupport_markedTransform_subset_of_pow_le (c := m - j) (p := m) (q := m - j)
    (by omega) (by omega) _ _ _ hBS' (mul_comm _ _) _ ?_ (A j) (hA j hj) hx
  rintro t ⟨⟩
  rw [← Stacks.IdealSheaf.comap_pow, ← Stacks.IdealSheaf.comap_pow]
  exact Scheme.IdealSheafData.comap_mono _ hDBj

end MMP.Resolution.ClosedBlowupSequence

end

/-!
## Étale equivalent blow-up sequences are equal

Let `X` be a separated, smooth, equidimensional scheme of finite type over a field `k` of
characteristic `0`, every irreducible component of positive dimension, and `I` an ideal sheaf
nonzero at the generic points with `m = maxord I ≥ 1`. Two smooth blow-up sequences `𝐁`, `𝐁'` of
order `m` starting with `(X, I)` which are étale equivalent with respect to `I` are equal: they
have the same length and the same centres, hence the same blown-up schemes and, the ideals of
an order-`m` sequence being determined by its centres, the same ideals.

## Main results

* `MMP.Resolution.ClosedBlowupSequence.eq_of_areEtaleEquivalent`: étale equivalent smooth
  blow-up sequences of order `maxord I` starting with `(X, I)` are equal.

## Implementation notes

A blow-up sequence `ClosedBlowupSequence X` is the list of its centres, each an ideal sheaf on
the previous blow-up, so the equality `𝐁 = 𝐁'` of sequences is the equality of the lengths and
of all centres; the schemes `X_i` and the ideals `I_i` (the controlled transforms recorded in
`IsOrderMPlainSeq`) are functions of `(X, I)` and the centres.

## References

* [Kollár, *Lectures on resolution of singularities*, Theorem 3.97][kollar2007]
-/

section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace
open MMP.Resolution MMP.Resolution.ClosedBlowupSequence

namespace Proof_thm_kr3d_etale_equivalent_sequences_equal

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

private theorem truncate_of_length_le {X : Scheme.{u}} (B : ClosedBlowupSequence X) {n : ℕ}
    (h : B.length ≤ n) : B.truncate n = B := by
  induction B generalizing n with
  | nil _ => rfl
  | cons Z B ih =>
    cases n with
    | zero => simp [length] at h
    | succ n => simp only [truncate, ih (by simp [length] at h; omega)]

private theorem length_pullback {X Y : Scheme.{u}} (B : ClosedBlowupSequence X) (h : Y ⟶ X) :
    (B.pullback h).length = B.length := by
  induction B generalizing Y with
  | nil _ => rfl
  | cons Z B ih => simp only [ClosedBlowupSequence.pullback, length, ih]

/-- The derived transform `T_n(K, a)` is the iterated marked transform of `(K, a)` as long as
every `T_l(K, a)`, `l ≤ n`, is an ideal sheaf. -/
private theorem derivedTransform_truncate_eq {X : Scheme.{u}} (B : ClosedBlowupSequence X)
    (K : X.IdealSheafData) (a n : ℕ)
    (h : ∀ l ≤ n, ∃ M, (B.truncate l).derivedTransform (some K) a = some M) :
    (B.truncate n).derivedTransform (some K) a =
      some ((B.truncate n).markedTransform ⟨K, a⟩).I := by
  induction B generalizing n with
  | nil _ => rfl
  | cons Z B ih =>
    cases n with
    | zero => rfl
    | succ n =>
      have hstep : derivedTransformStep Z a (some K) =
          some (MarkedIdeal.birationalTransform Z ⟨K, a⟩).I := by
        obtain ⟨M1, hM1⟩ : ∃ M, derivedTransformStep Z a (some K) = some M := by
          have h1 := h 1 (by omega)
          cases B <;> exact h1
        classical
        change (if _ then _ else none) = _ at hM1
        change (if _ then _ else none) = _
        split_ifs at hM1 ⊢
        rfl
      simp only [truncate, derivedTransform, markedTransform, hstep]
      refine ih _ n fun l hl => ?_
      obtain ⟨M, hM⟩ := h (l + 1) (by omega)
      simp only [truncate, derivedTransform, hstep] at hM
      exact ⟨M, hM⟩

/-- Along the pulled-back sequence `(B.truncate i).pullback ψ`, the derived transform of
`(K, a)` is the iterated marked transform of `(K, a)` as long as every derived transform along
`(B.truncate l).pullback ψ`, `l ≤ i`, is an ideal sheaf. -/
private theorem derivedTransform_pullback_truncate_eq {X Y : Scheme.{u}}
    (B : ClosedBlowupSequence X) (ψ : Y ⟶ X) (K : Y.IdealSheafData) (a i : ℕ)
    (h : ∀ l ≤ i, ∃ M, ((B.truncate l).pullback ψ).derivedTransform (some K) a = some M) :
    ((B.truncate i).pullback ψ).derivedTransform (some K) a =
      some (((B.truncate i).pullback ψ).markedTransform ⟨K, a⟩).I := by
  rw [← Kollar.pullback_truncate]
  exact derivedTransform_truncate_eq _ _ _ _ fun l hl => Kollar.pullback_truncate B ψ l ▸ h l hl

/-- The ideal of the diagonal pulled back along a pair of maps depends only on the base map and
the two maps, not on the proofs that they agree over the base. -/
private theorem ker_diagonal_comap_lift_congr {X S T : Scheme.{u}} {f g : X ⟶ S} (hfg : f = g)
    {a a' b b' : T ⟶ X} (ha : a = a') (hb : b = b') (hk : a ≫ f = b ≫ f)
    (hk' : a' ≫ g = b' ≫ g) :
    (Limits.pullback.diagonal f).ker.comap (Limits.pullback.lift a b hk) =
      (Limits.pullback.diagonal g).ker.comap (Limits.pullback.lift a' b' hk') := by
  subst hfg ha hb
  rfl

/-- The induction of Kollár's Theorem 3.97: for `i ≤ r`, the first `i` truncations of `B` and
`B'` agree, every `M_l = T_l(D^{m-1}(ψ^*I), 1)` with `l ≤ i` is an ideal sheaf, and the pair
`(ψ_i, ψ'_i)` pulls the ideal of the diagonal of `X_i ×_k X_i` back into `M_i`. -/
private theorem truncate_eq_and_ker_diagonal_comap_le {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [Smooth sX] [QuasiCompact sX] [IsSeparated sX]
    (hX : Equidimensional X) (hdim : ∀ Z ∈ irreducibleComponents X, 0 < topologicalKrullDim Z)
    {I : X.IdealSheafData} (hI : IsNonzeroAtGenericPoints I) {m : ℕ} (hm1 : 1 ≤ m)
    (hm : maxOrder I = m) {B B' : ClosedBlowupSequence X} (hB : B.IsOrderMPlainSeq sX I m)
    (hB' : B'.IsOrderMPlainSeq sX I m) {U : Scheme.{u}} {sU : U ⟶ Spec (.of k)}
    {ψ ψ' : U ⟶ X} (hψ : IsEtaleChartPair sX I sU ψ ψ') (hBB' : B.pullback ψ = B'.pullback ψ')
    {i : ℕ} (hi : i ≤ B.length) :
    (∀ l ≤ i, B.truncate l = B'.truncate l) ∧
      (∀ l ≤ i, ∃ M, ((B.truncate l).pullback ψ).derivedTransform
        (some (higherDerivativeIdeal sU (I.comap ψ) (m - 1))) 1 = some M) ∧
      ∀ (hU : (B.truncate i).pullback ψ = (B.truncate i).pullback ψ')
        (hk : (B.truncate i).pullbackHom ψ ≫ (B.truncate i).toBase ≫ sX =
          (eqToHom (congrArg ClosedBlowupSequence.target hU) ≫
            (B.truncate i).pullbackHom ψ') ≫ (B.truncate i).toBase ≫ sX),
        (Limits.pullback.diagonal ((B.truncate i).toBase ≫ sX)).ker.comap
            (Limits.pullback.lift _ _ hk) ≤
          (((B.truncate i).pullback ψ).markedTransform
            ⟨higherDerivativeIdeal sU (I.comap ψ) (m - 1), 1⟩).I := by
  induction i with
  | zero =>
    refine ⟨fun l hl => ?_, fun l hl => ?_, ?_⟩
    · obtain rfl : l = 0 := by omega
      rw [Kollar.truncate_zero, Kollar.truncate_zero]
    · obtain rfl : l = 0 := by omega
      rw [Kollar.truncate_zero]
      exact ⟨_, rfl⟩
    · rw [Kollar.truncate_zero]
      intro hU hk
      refine le_of_eq_of_le (ker_diagonal_comap_lift_congr (Category.id_comp sX) rfl
        ((fun h => by simp : ∀ h : U = U, eqToHom h ≫ ψ' = ψ') _) hk
        (hψ.comp_eq.trans hψ.comp_eq'.symm)) ?_
      have hd := hψ.diagonal_le
      rwa [hm] at hd
  | succ i ih =>
    obtain ⟨hZ, hS, hD⟩ := ih (by omega)
    have hi' : i < B.length := by omega
    have hZ' : ∀ l ≤ i + 1, B.truncate l = B'.truncate l := fun l hl =>
      (Nat.lt_or_eq_of_le hl).elim (fun _ => hZ l (by omega)) fun h => h ▸
        truncate_succ_eq_of_isEtaleChartPair sX hX hdim hI hm1 hm hB hB' hψ hBB' hi' rfl
          (hZ i le_rfl).symm hD
    obtain ⟨Mi1, hMi1, hle⟩ := ker_diagonal_comap_le_derivedTransform_succ sX hX hdim I hI m hm
      hm1 B B' hB hB' sU ψ ψ' hψ hBB' i hi' hZ' fun Mi hMi => by
        beta_reduce at hMi ⊢
        have h := derivedTransform_pullback_truncate_eq _ _ _ _ _ hS
        rw [hMi, Option.some_inj] at h
        rw [h]
        exact hD (by rw [← Kollar.pullback_truncate, hBB', Kollar.pullback_truncate,
          hZ i le_rfl]) _
    have hS' : ∀ l ≤ i + 1, ∃ M, ((B.truncate l).pullback ψ).derivedTransform
        (some (higherDerivativeIdeal sU (I.comap ψ) (m - 1))) 1 = some M := fun l hl =>
      (Nat.lt_or_eq_of_le hl).elim (fun _ => hS l (by omega)) fun h => h ▸ ⟨Mi1, hMi1⟩
    refine ⟨hZ', hS', fun hU hk => ?_⟩
    have h := derivedTransform_pullback_truncate_eq _ _ _ _ _ hS'
    beta_reduce at hMi1
    rw [hMi1, Option.some_inj] at h
    exact h ▸ hle

end Proof_thm_kr3d_etale_equivalent_sequences_equal

namespace MMP.Resolution.ClosedBlowupSequence

open Proof_thm_kr3d_etale_equivalent_sequences_equal in
/-- **Étale equivalent sequences are equal** (Kollár, Thm. 3.97). Let `X` be separated, smooth,
equidimensional and of finite type over a field `k` of characteristic `0`, every irreducible
component of positive dimension, `I` nonzero at the generic points with `maxOrder I = m ≥ 1`,
and `B`, `B'` smooth blow-up sequences of order `m` starting with `(X, I)`. If `B` and `B'` are
étale equivalent with respect to `I` (`AreEtaleEquivalent`), then `B = B'`. -/
@[mmp "thm_kr3d_etale_equivalent_sequences_equal"]
public theorem eq_of_areEtaleEquivalent {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [Smooth sX] [QuasiCompact sX] [IsSeparated sX]
    (hX : Equidimensional X)
    (hdim : ∀ Z ∈ irreducibleComponents X, 0 < topologicalKrullDim Z)
    {I : X.IdealSheafData} (hI : IsNonzeroAtGenericPoints I) {m : ℕ} (hm1 : 1 ≤ m)
    (hm : maxOrder I = m) {B B' : ClosedBlowupSequence X} (hB : B.IsOrderMPlainSeq sX I m)
    (hB' : B'.IsOrderMPlainSeq sX I m) (hE : AreEtaleEquivalent sX I B B') :
    B = B' := by
  obtain ⟨U, sU, ψ, ψ', hψ, hBB'⟩ := hE
  have hlen : B'.length ≤ B.length := by
    rw [← length_pullback B' ψ', ← hBB', length_pullback]
  have h := (truncate_eq_and_ker_diagonal_comap_le sX hX hdim hI hm1 hm hB hB' hψ hBB'
    le_rfl).1 B.length le_rfl
  rwa [truncate_of_length_le B le_rfl, truncate_of_length_le B' hlen] at h

end MMP.Resolution.ClosedBlowupSequence

end

/-!
## Going up for `D`-balanced ideals

Let `X` be a smooth equidimensional scheme of finite type over a field `k` of characteristic `0`,
with every irreducible component of positive dimension, and let `I` be a `D`-balanced ideal sheaf
on `X`, nonzero on every irreducible component, with `m = maxord I ≥ 1`. Let `S ⊆ X` be a smooth
hypersurface none of whose irreducible components lies in `cosupp(I, m)`, and let
`Π^S = (S_i, Z_i)_{i ≤ r}` be a smooth blow-up sequence of order `≥ m` starting with
`(S, I|_S, m)`. Then the push-forward `Π = (X_i, Z_i)_{i ≤ r}` of `Π^S` along `S ↪ X` is a
smooth blow-up sequence of order `m` starting with `(X, I)`.

## Main results

* `MMP.Resolution.ClosedBlowupSequence.IsPushforward.isOrderMPlainSeq_of_isDBalanced`

## Implementation notes

The push-forward is `MMP.Resolution.ClosedBlowupSequence.IsPushforward` along the inclusion
`S.subschemeι`; it determines the centres `Z^X_i = (j_i)_* Z^S_i`. The restriction `I|_S` is the
inverse image ideal `I.comap S.subschemeι`, and the irreducible components of `S` are those of its
support `S.support ⊆ X`.

## References

* [J. Kollár, *Lectures on resolution of singularities*, Thm. 3.84][kollar2007]
-/

section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Resolution

variable {k : Type u} [Field k]

namespace Proof_thm_kr3d_going_up_d_balanced

open MMP.Resolution.ClosedBlowupSequence

/-! ### Truncations -/

private theorem length_truncate {X : Scheme.{u}} (B : ClosedBlowupSequence X) (n : ℕ) :
    (B.truncate n).length = min n B.length := by
  induction B generalizing n with
  | nil => simp [truncate, length]
  | cons Z B ih =>
    cases n with
    | zero => simp [truncate, length]
    | succ n =>
      change (B.truncate n).length + 1 = min (n + 1) (B.length + 1)
      rw [ih]; omega

private theorem truncate_succ_truncate {X : Scheme.{u}} (B : ClosedBlowupSequence X) (n : ℕ) :
    (B.truncate (n + 1)).truncate n = B.truncate n := by
  induction B generalizing n with
  | nil => rfl
  | cons Z B ih =>
    cases n with
    | zero => rfl
    | succ n => exact congrArg (cons Z) (ih n)

private theorem isPushforward_truncate {S X : Scheme.{u}} {j : S ⟶ X}
    {BS : ClosedBlowupSequence S} {BX : ClosedBlowupSequence X} (hP : IsPushforward j BS BX)
    (n : ℕ) : IsPushforward j (BS.truncate n) (BX.truncate n) := by
  induction BS generalizing X n with
  | nil S =>
    cases BX with
    | nil => trivial
    | cons ZX BX => exact hP.elim
  | cons ZS BS ih =>
    cases BX with
    | nil => exact hP.elim
    | cons ZX BX =>
      cases n with
      | zero => trivial
      | succ n =>
        obtain ⟨hc, hm, hP⟩ := hP
        exact ⟨hc, hm, ih hP n⟩

/-- The conditions a blow-up sequence of order `≥ m` imposes at its `n`-th step, beyond those on
its first `n` steps: the centre `Z_n` is smooth, of positive codimension, with
`ord_{Z_n} I_n ≥ m`, and `X_{n+1}` is smooth with `I_{n+1}` nonzero on its components. -/
private def IsOrderGePlainStep : {X : Scheme.{u}} → (X ⟶ Spec (.of k)) → MarkedIdeal X →
    ClosedBlowupSequence X → ℕ → Prop
  | _, _, _, nil _, _ => True
  | X, s, a, cons Z _, 0 => MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ s) ∧
      HasComponentsOfPositiveCodim (Z.support : Set X) ∧
      OrderAlongGE a.I (Z.support : Set X) a.m ∧
      MMP.Mori.IsSmoothScheme (blowUpToBase Z ≫ s) ∧
      IsNonzeroAtGenericPoints (a.birationalTransform Z).I
  | _, s, a, cons Z B, n + 1 =>
    IsOrderGePlainStep (blowUpToBase Z ≫ s) (a.birationalTransform Z) B n

private theorem isOrderGePlainSeq_truncate_succ_iff {X : Scheme.{u}}
    (B : ClosedBlowupSequence X) (s : X ⟶ Spec (.of k)) (a : MarkedIdeal X) (n : ℕ) :
    (B.truncate (n + 1)).IsOrderGePlainSeq s a ↔
      (B.truncate n).IsOrderGePlainSeq s a ∧ IsOrderGePlainStep s a B n := by
  induction B generalizing n with
  | nil => exact ⟨fun h => ⟨h, trivial⟩, fun h => h.1⟩
  | cons Z B ih =>
    cases n with
    | zero =>
      change (cons Z (B.truncate 0)).IsOrderGePlainSeq s a ↔ _
      rw [Kollar.truncate_zero]
      change (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _) ↔ (_ ∧ _) ∧ (_ ∧ _ ∧ _ ∧ _ ∧ _)
      tauto
    | succ n =>
      change (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ (B.truncate (n + 1)).IsOrderGePlainSeq _ _) ↔
        (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ (B.truncate n).IsOrderGePlainSeq _ _) ∧ _
      rw [ih]
      tauto

/-! ### Closed embeddings and irreducible components -/

section Topology

variable {A B : Type*} [TopologicalSpace A] [TopologicalSpace B] {f : A → B}

private theorem isIrreducible_preimage (hf : Topology.IsInducing f) {t : Set B}
    (ht : IsIrreducible t) (htr : t ⊆ Set.range f) : IsIrreducible (f ⁻¹' t) := by
  refine ⟨?_, fun u v hu hv ⟨x, hxt, hxu⟩ ⟨y, hyt, hyv⟩ => ?_⟩
  · obtain ⟨b, hb⟩ := ht.1
    obtain ⟨a, rfl⟩ := htr hb
    exact ⟨a, hb⟩
  obtain ⟨u', hu', rfl⟩ := hf.isOpen_iff.1 hu
  obtain ⟨v', hv', rfl⟩ := hf.isOpen_iff.1 hv
  obtain ⟨b, hbt, hbu, hbv⟩ := ht.2 u' v' hu' hv' ⟨f x, hxt, hxu⟩ ⟨f y, hyt, hyv⟩
  obtain ⟨a, rfl⟩ := htr hbt
  exact ⟨a, hbt, hbu, hbv⟩

private theorem preimage_mem_componentsOf (hf : Topology.IsEmbedding f) {T : Set A} {W : Set B}
    (hW : W ∈ componentsOf (f '' T)) :
    f ⁻¹' W ∈ componentsOf T ∧ f '' (f ⁻¹' W) = W := by
  have hWr : W ⊆ Set.range f := hW.1.2.trans (Set.image_subset_range f T)
  have himg : f '' (f ⁻¹' W) = W := Set.image_preimage_eq_of_subset hWr
  refine ⟨⟨⟨isIrreducible_preimage hf.isInducing hW.1.1 hWr, fun a ha => ?_⟩,
    fun V hV hWV => ?_⟩, himg⟩
  · obtain ⟨a', ha', hfa⟩ := hW.1.2 ha
    rwa [← hf.injective hfa]
  · have hV' : IsIrreducible (f '' V) ∧ f '' V ⊆ f '' T :=
      ⟨hV.1.image f hf.continuous.continuousOn, Set.image_mono hV.2⟩
    have := hW.2 hV' (himg ▸ Set.image_mono hWV)
    exact fun a ha => this ⟨a, ha, rfl⟩

private theorem image_mem_componentsOf (hf : Topology.IsEmbedding f) {T C : Set A}
    (hC : C ∈ componentsOf T) : f '' C ∈ componentsOf (f '' T) := by
  refine ⟨⟨hC.1.1.image f hf.continuous.continuousOn, Set.image_mono hC.1.2⟩, fun V hV hCV => ?_⟩
  have hVr : V ⊆ Set.range f := hV.2.trans (Set.image_subset_range f T)
  have hpre : f ⁻¹' V ⊆ T := fun a ha => by
    obtain ⟨a', ha', hfa⟩ := hV.2 ha
    rwa [← hf.injective hfa]
  have := hC.2 ⟨isIrreducible_preimage hf.isInducing hV.1 hVr, hpre⟩
    (fun a ha => hCV ⟨a, ha, rfl⟩)
  rw [← Set.image_preimage_eq_of_subset hVr]
  exact Set.image_mono this

private theorem genericPoint_image [QuasiSober A] [QuasiSober B] [T0Space B]
    (hf : Continuous f) {W' : Set A}
    (hW' : IsIrreducible W') {W : Set B} (hW : IsIrreducible W) (hWW : f '' W' = W) :
    hW.genericPoint = f hW'.genericPoint := by
  subst hWW
  have h1 := hW'.isGenericPoint_genericPoint_closure.image hf
  rw [closure_image_closure hf] at h1
  exact hW.isGenericPoint_genericPoint_closure.eq h1

end Topology

private theorem one_le_codimension_image {S X : Scheme.{u}} (j : S ⟶ X) [IsClosedImmersion j]
    {W' : Set S} (hW' : IsIrreducible W') {W : Set X} (hW : IsIrreducible W) (hWW : j '' W' = W)
    (h : 1 ≤ codimension (irreducibleClosure hW')) :
    1 ≤ codimension (irreducibleClosure hW) := by
  subst hWW
  have hf := j.isClosedEmbedding
  rw [ENat.one_le_iff_ne_zero, codimension, Ne, Order.coheight_eq_zero] at h ⊢
  obtain ⟨V', hV'⟩ := not_isMax_iff.1 h
  have hle : closure W' ⊆ V' := hV'.le
  refine not_isMax_iff.2 ⟨⟨j '' V', V'.isIrreducible.image j hf.continuous.continuousOn,
    hf.isClosedMap _ V'.isClosed⟩, lt_of_le_not_ge ?_ ?_⟩
  · change closure (j '' W') ⊆ j '' V'
    exact closure_minimal ((Set.image_mono subset_closure).trans (Set.image_mono hle))
      (hf.isClosedMap _ V'.isClosed)
  · intro h'
    change j '' V' ⊆ closure (j '' W') at h'
    have hcl : closure (j '' W') ⊆ j '' closure W' :=
      closure_minimal (Set.image_mono subset_closure) (hf.isClosedMap _ isClosed_closure)
    refine hV'.not_ge fun a ha => ?_
    obtain ⟨a', ha', hfa⟩ := hcl (h' ⟨a, ha, rfl⟩)
    rwa [← hf.injective hfa]

/-! ### The step condition along a push-forward -/

private theorem support_map_eq_image {S X : Scheme.{u}} (j : S ⟶ X) [IsClosedImmersion j]
    (Z : S.IdealSheafData) : ((Z.map j).support : Set X) = j '' Z.support := by
  rw [Scheme.IdealSheafData.support_map]
  exact (j.isClosedEmbedding.isClosedMap _ Z.support.isClosed).closure_eq

private theorem isOrderGePlainStep_of_isPushforward {X : Scheme.{u}} (BX : ClosedBlowupSequence X) :
    ∀ {S : Scheme.{u}} (j : S ⟶ X) [IsClosedImmersion j] (s : X ⟶ Spec (.of k))
      (a : MarkedIdeal X) (b : MarkedIdeal S) (n : ℕ),
      IsPushforward j (BX.pullback j) BX → IsOrderGePlainStep (j ≫ s) b (BX.pullback j) n →
      (BX.truncate n).IsOrderGePlainSeq s a →
      (BX.truncate n).pullbackHom j ''
          (((BX.truncate n).pullback j).markedTransform b).cosupport ⊆
        ((BX.truncate n).markedTransform a).cosupport →
      IsOrderGePlainStep s a BX n := by
  induction BX with
  | nil => intros; trivial
  | cons Z B ih =>
    intro S j _ s a b n hP hB hT hcos
    obtain ⟨hc, hZ, hP⟩ := hP
    rw [eqToHom_refl, Category.id_comp] at hP
    cases n with
    | zero =>
      obtain ⟨hZs, hcod, hord, -⟩ := hB
      obtain ⟨hX, hI⟩ := hT
      change j '' b.cosupport ⊆ a.cosupport at hcos
      have hsupp : (Z.support : Set _) = j '' (Z.comap j).support := by
        conv_lhs => rw [hZ]
        exact support_map_eq_image j _
      have hZsm : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ s) := by
        rw [hZ]
        exact isSmoothScheme_map_subschemeι_comp j s _ hZs
      refine ⟨hZsm, fun W hW => ?_, fun W hW => ?_,
        MMP.Mori.isSmoothScheme_of_smooth
          (Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup s Z ⟨hX, hZsm⟩).1,
        isNonzeroAtGenericPoints_idealColon_comap Z hI _⟩
      · rw [hsupp] at hW
        obtain ⟨hW', himg⟩ := preimage_mem_componentsOf j.isClosedEmbedding.isEmbedding hW
        exact one_le_codimension_image j hW'.1.1 _ himg (hcod _ hW')
      · rw [hsupp] at hW
        obtain ⟨hW', himg⟩ := preimage_mem_componentsOf j.isClosedEmbedding.isEmbedding hW
        change (a.m : ℕ∞) ≤ multAt a.I _
        rw [genericPoint_image j.continuous hW'.1.1 _ himg]
        exact hcos ⟨_, hord _ hW', rfl⟩
    | succ n =>
      have := Bridges.isClosedImmersion_canonicalLift j Z
      have hB' : IsOrderGePlainStep (canonicalLift j Z ≫ blowUpToBase Z ≫ s)
          ((b.birationalTransform (Z.comap j))) (B.pullback (canonicalLift j Z)) n := by
        rw [← Category.assoc, canonicalLift_comp_blowUpToBase, Category.assoc]
        exact hB
      exact ih (canonicalLift j Z) (blowUpToBase Z ≫ s) (a.birationalTransform Z) _ n hP hB'
        hT.2.2.2.2.2 hcos

/-! ### Order `≥ m` versus order `m` -/

/-- The divisor `∑_j m_j F_j` of the controlled transform is `m F` when `ord_Z I = m`. -/
private theorem controlledTransformDivisorIdeal_eq {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (hX : MMP.Mori.IsSmoothScheme sX) [LocallyOfFiniteType sX]
    [QuasiCompact sX] (Z : X.IdealSheafData) (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ sX))
    (I : X.IdealSheafData) (m : ℕ) (hIZ : OrderAlongEq I (Z.support : Set X) m) :
    controlledTransformDivisorIdeal Z I = Z.comap (blowUpToBase Z) ^ m := by
  classical
  haveI := LocallyOfFiniteType.isLocallyNoetherian sX
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : IsNoetherian X := ⟨⟩
  haveI : Finite (componentsOf (Z.support : Set X)) :=
    (finite_componentsOf Z.support.2).to_subtype
  letI := Fintype.ofFinite (componentsOf (Z.support : Set X))
  have key : ∀ y, IdealSheafData.stalk (controlledTransformDivisorIdeal Z I) y =
      IdealSheafData.stalk (Z.comap (blowUpToBase Z) ^ m) y := by
    intro y
    set x := blowUpToBase Z y
    have hD : IdealSheafData.stalk (controlledTransformDivisorIdeal Z I) y =
        ∏ W : componentsOf (Z.support : Set X), Ideal.map ((blowUpToBase Z).stalkMap y).hom
          (IdealSheafData.stalk (componentsFamily (Z.support : Set X) W) x) ^
            (orderAlong I W.2.1.1).toNat := by
      unfold controlledTransformDivisorIdeal
      rw [finprod_eq_prod_of_fintype, stalk_prod]
      exact Finset.prod_congr rfl fun W _ => by
        rw [IdealSheafData.stalk_pow, IdealSheafData.stalk_comap]
    rw [hD, IdealSheafData.stalk_pow, IdealSheafData.stalk_comap]
    by_cases hx : x ∈ (Z.support : Set X)
    · obtain ⟨W0, hW0, hxW0, huniq, hstalk, -⟩ := exists_component_through sX hX Z hZ I x hx
      rw [Finset.prod_eq_single (⟨W0, hW0⟩ : componentsOf (Z.support : Set X))]
      · rw [hstalk, hIZ W0 hW0]
        rfl
      · intro W _ hne
        have : x ∉ (W : Set X) := fun hxW => hne (Subtype.ext (huniq W W.2 hxW))
        rw [stalk_componentsFamily_eq_top Z W.2 this, Ideal.map_top, ← Ideal.one_eq_top, one_pow]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [(IdealSheafData.stalk_eq_top_iff_notMem_support Z x).2 hx, Ideal.map_top,
        ← Ideal.one_eq_top, one_pow]
      refine Finset.prod_eq_one fun W _ => ?_
      have : x ∉ (W : Set X) := fun hxW => hx (W.2.1.2 hxW)
      rw [stalk_componentsFamily_eq_top Z W.2 this, Ideal.map_top, ← Ideal.one_eq_top, one_pow]
  exact le_antisymm (IdealSheafData.le_of_stalk_le _ _ fun y => (key y).le)
    (IdealSheafData.le_of_stalk_le _ _ fun y => (key y).ge)

/-- When `ord_Z I = m`, the birational transform of `(I, m)` is the controlled transform of `I`,
marked by `m`. -/
private theorem birationalTransform_eq {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (hX : MMP.Mori.IsSmoothScheme sX) [LocallyOfFiniteType sX]
    [QuasiCompact sX] (Z : X.IdealSheafData) (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ sX))
    (I : X.IdealSheafData) (m : ℕ) (hIZ : OrderAlongEq I (Z.support : Set X) m) :
    MarkedIdeal.birationalTransform Z ⟨I, m⟩ = ⟨MMP.Resolution.controlledTransform Z I, m⟩ := by
  change (⟨idealColon _ _, m⟩ : MarkedIdeal _) = ⟨idealColon _ _, m⟩
  rw [controlledTransformDivisorIdeal_eq sX hX Z hZ I m hIZ]

/-- A smooth blow-up sequence of order `≥ m` starting with `(X, I, m)`, where `maxord I ≤ m`, is
one of order `m` starting with `(X, I)` (Kollár, Remark 3.67, with `E = ∅`). -/
private theorem isOrderMPlainSeq_of_isOrderGePlainSeq (m : ℕ) {X : Scheme.{u}}
    (B : ClosedBlowupSequence X) :
    ∀ (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s] [QuasiCompact s] (I : X.IdealSheafData),
      maxOrder I ≤ m → B.IsOrderGePlainSeq s ⟨I, m⟩ → B.IsOrderMPlainSeq s I m := by
  induction B with
  | nil X => exact fun s _ _ I _ h => h
  | cons Z B ih =>
    intro s _ _ I hmax h
    obtain ⟨hX, hI, hZ, hc, hGe, hB⟩ := h
    have hEq : OrderAlongEq I (Z.support : Set _) m := fun W hW =>
      le_antisymm ((le_iSup₂ (f := fun z (_ : z ∈ Set.univ) => multAt I z) hW.1.1.genericPoint
        (Set.mem_univ _)).trans hmax) (hGe W hW)
    have hB' : B.IsOrderGePlainSeq (blowUpToBase Z ≫ s)
        ⟨MMP.Resolution.controlledTransform Z I, m⟩ :=
      birationalTransform_eq s hX Z hZ I m hEq ▸ hB
    have hmax' : maxOrder (MMP.Resolution.controlledTransform Z I) ≤ m := by
      haveI : Smooth s := hX.smooth
      haveI : Smooth (Z.subschemeι ≫ s) := hZ.smooth
      refine (maxOrder_controlledTransform_le s Z hc I hI fun W hW => ?_).trans hmax
      exact le_antisymm (le_iSup₂ (f := fun z (_ : z ∈ Set.univ) => multAt I z)
        hW.1.1.genericPoint (Set.mem_univ _)) (hmax.trans (hEq W hW).ge)
    haveI := LocallyOfFiniteType.isLocallyNoetherian s
    haveI : IsProper (blowUpToBase Z) := isProper_blowUpToBase Z
    exact ⟨hX, hI, hZ, hc, hEq, ih _ _ hmax' hB'⟩

end Proof_thm_kr3d_going_up_d_balanced

namespace MMP.Resolution.ClosedBlowupSequence

open Proof_thm_kr3d_going_up_d_balanced in
/-- **Going up for `D`-balanced ideals** (Kollár Thm. 3.84). Let `X` be smooth, equidimensional
and of finite type over a field `k` of characteristic `0`, with every irreducible component of
positive dimension, `I` a `D`-balanced ideal sheaf on `X`, nonzero on every irreducible component,
with `maxord I = m ≥ 1`, and `S ⊆ X` a smooth hypersurface none of whose irreducible components
is contained in `cosupp(I, m)`. If `BS` is a smooth blow-up sequence of order `≥ m` starting with
`(S, I|_S, m)` and `BX` is its push-forward along `S ↪ X`, then `BX` is a smooth blow-up sequence
of order `m` starting with `(X, I)`. -/
@[mmp "thm_kr3d_going_up_d_balanced"]
public theorem IsPushforward.isOrderMPlainSeq_of_isDBalanced {k : Type u} [Field k]
    [CharZero k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX]
    [QuasiCompact sX] (hXs : MMP.Mori.IsSmoothScheme sX) (hX : Equidimensional X)
    (hdim : ∀ Z ∈ irreducibleComponents X, 0 < topologicalKrullDim Z)
    {I : X.IdealSheafData} (hD : IsDBalanced sX I) (hI : IsNonzeroAtGenericPoints I)
    {m : ℕ} (hm : maxOrder I = m) (hm1 : 1 ≤ m)
    {S : X.IdealSheafData} (hS : IsSmoothHypersurface sX S)
    (hSI : ∀ W ∈ componentsOf (S.support : Set X), ¬ W ⊆ MarkedIdeal.cosupport ⟨I, m⟩)
    {BS : ClosedBlowupSequence S.subscheme}
    (hBS : BS.IsOrderGePlainSeq (S.subschemeι ≫ sX) ⟨I.comap S.subschemeι, m⟩)
    {BX : ClosedBlowupSequence X} (hP : IsPushforward S.subschemeι BS BX) :
    BX.IsOrderMPlainSeq sX I m := by
  obtain rfl := Kollar.restrict_eq_of_isPushforward S hP
  set j := S.subschemeι
  change IsPushforward j (BX.pullback j) BX at hP
  change (BX.pullback j).IsOrderGePlainSeq (j ≫ sX) ⟨I.comap j, m⟩ at hBS
  haveI : Smooth sX := hXs.smooth
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have hdim' : ∃ n : ℕ, 0 < n ∧ ∀ C ∈ irreducibleComponents X, topologicalKrullDim C = n := by
    by_cases hne : ∃ C₀, C₀ ∈ irreducibleComponents X
    · obtain ⟨C₀, hC₀⟩ := hne
      have hfin : topologicalKrullDim C₀ ≠ ⊤ := fun h =>
        topologicalKrullDim_ne_top_of_locallyOfFiniteType k sX
          (top_le_iff.1 (h ▸ topologicalKrullDim_subspace_le X C₀))
      have hpos := hdim C₀ hC₀
      obtain ⟨n, hn⟩ : ∃ n : ℕ, topologicalKrullDim C₀ = n := by
        cases h : topologicalKrullDim C₀ with
        | bot => rw [h] at hpos; exact absurd hpos (not_lt_bot)
        | coe e =>
          cases e with
          | top => exact absurd h hfin
          | coe n => exact ⟨n, rfl⟩
      refine ⟨n, ?_, fun C hC => (hX C hC C₀ hC₀).trans hn⟩
      rw [hn] at hpos
      exact_mod_cast hpos
    · exact ⟨1, one_pos, fun C hC => absurd ⟨C, hC⟩ hne⟩
  have hSC : ∀ C ∈ irreducibleComponents S.subscheme,
      ¬ j '' C ⊆ (⟨I, m⟩ : MarkedIdeal X).cosupport := by
    intro C hC
    refine hSI _ ?_
    rw [← Scheme.IdealSheafData.range_subschemeι, ← Set.image_univ]
    refine image_mem_componentsOf j.isClosedEmbedding.isEmbedding ⟨⟨hC.1, Set.subset_univ _⟩,
      fun V hV hCV => hC.2 hV.1 hCV⟩
  have key : ∀ t ≤ BX.length, (BX.truncate t).IsOrderGePlainSeq sX ⟨I, m⟩ := by
    intro t
    induction t with
    | zero => intro _; rw [Kollar.truncate_zero]; exact ⟨hXs, hI⟩
    | succ t ih =>
      intro ht
      have ih := ih (by omega)
      refine (isOrderGePlainSeq_truncate_succ_iff BX sX _ t).2 ⟨ih, ?_⟩
      have hB := ((isOrderGePlainSeq_truncate_succ_iff (BX.pullback j) (j ≫ sX) _ t).1
        (Proof_lem_kr3d_going_up_inductive_step.isOrderGePlainSeq_truncate _ _ _ (t + 1)
          hBS)).2
      refine isOrderGePlainStep_of_isPushforward BX j sX ⟨I, m⟩ ⟨I.comap j, m⟩ t hP hB ih ?_
      have hr : (BX.truncate (t + 1)).length = t + 1 := by
        rw [length_truncate]; omega
      have hP' : IsPushforward j ((BX.truncate (t + 1)).restrict S) (BX.truncate (t + 1)) := by
        change IsPushforward j ((BX.truncate (t + 1)).pullback j) _
        rw [← Kollar.pullback_truncate]
        exact isPushforward_truncate hP _
      have hBS' : ((BX.truncate (t + 1)).restrict S).IsOrderGePlainSeq (j ≫ sX)
          ⟨I.comap j, m⟩ := by
        change ((BX.truncate (t + 1)).pullback j).IsOrderGePlainSeq _ _
        rw [← Kollar.pullback_truncate]
        exact Proof_lem_kr3d_going_up_inductive_step.isOrderGePlainSeq_truncate _ _ _ _ hBS
      have hBX' : ((BX.truncate (t + 1)).truncate t).IsOrderGePlainSeq sX ⟨I, m⟩ := by
        rw [truncate_succ_truncate]; exact ih
      have := image_cosupport_restrict_subset_of_isDBalanced sX hdim' hD hI hm hm1 hS hSC hr
        hP' hBS' hBX'
      rw [truncate_succ_truncate] at this
      exact this
  have hGe := key BX.length le_rfl
  rw [Proof_thm_kr3d_log_decomposition_of_derivatives.truncate_length] at hGe
  exact isOrderMPlainSeq_of_isOrderGePlainSeq m BX sX I hm.le hGe

end MMP.Resolution.ClosedBlowupSequence

end

/-!
## Uniqueness of hypersurfaces of maximal contact

Let `X` be a smooth, equidimensional scheme of finite type over a field `k` of
characteristic zero, all of whose irreducible components have positive dimension. Let `I` be a
maximal contact invariant ideal sheaf, nonzero at the generic point of every irreducible
component, with `m = maxord I ≥ 1`, and let `E = (E^1, …, E^s)` be an ordered snc divisor. Let
`H, H' ⊆ X` be smooth hypersurfaces whose ideal sheaves lie in the maximal contact ideal
`MC(I) = D^{m-1}(I)`, such that `H + ∑ᵢ E^i` and `H' + ∑ᵢ E^i` are snc. Then `H` and `H'` are
étale equivalent with respect to `(X, I, E)`: there are a scheme `U` of finite type over `k` and
étale morphisms `ψ, ψ' : U → X` whose images contain `cosupp(I, m)`, with `ψ⁻¹H = ψ'⁻¹H'`,
`ψ^*I = ψ'^*I`, `ψ⁻¹E^i = ψ'⁻¹E^i` and `(ψ, ψ')^*(I_Δ) ⊆ D^{m-1}(ψ^*I)`.

## Main results

* `MMP.Resolution.areEtaleEquivalentHypersurfaces_of_le_maximalContactIdeal`

## Implementation notes

The source assumes only that `H, H'` are hypersurfaces of maximal contact; the statement here
asks for the stronger `𝒪_X(-H), 𝒪_X(-H') ⊆ MC(I)`, which is what the proof uses (local
equations of `H, H'` lying in `MC(I)`), and which implies maximal contact by
`isHypersurfaceOfMaximalContact_of_le_maximalContactIdeal`. The conclusion is étale
equivalence with images containing the cosupport, not étale surjections. The divisor
`H + ∑ᵢ E^i` is the family `Fin.cons H E.E` indexed by `Fin (E.s + 1)`.

The source works with varieties; separatedness of `X` is not assumed here. The étale
equivalence is built from charts `ψ, ψ'` that land in a common affine open `V ⊆ X`, where the
diagonal of `V` is closed, and the ideal of the diagonal of `X ×_k X` restricts on `V ×_k V` into
that of `V`, so the conclusion holds without a closed diagonal on `X`.

## References

* [J. Kollár, *Lectures on resolution of singularities*, Theorem 3.92][kollar2007]
-/

section

universe u w

open CategoryTheory AlgebraicGeometry Limits MMP.Resolution

namespace Proof_thm_kr3d_uniqueness_of_maximal_contact

/-- An ideal sheaf inclusion can be checked after pull-back along a jointly surjective family of
open immersions. -/
private theorem le_of_forall_comap_le {U : Scheme.{w}} {ι : Type w} {V : ι → Scheme.{w}}
    (f : ∀ i, V i ⟶ U) [∀ i, IsOpenImmersion (f i)] (hf : ∀ x, ∃ i, x ∈ Set.range (f i))
    {J₁ J₂ : U.IdealSheafData} (h : ∀ i, J₁.comap (f i) ≤ J₂.comap (f i)) : J₁ ≤ J₂ := by
  refine Scheme.IdealSheafData.le_of_iSup_eq_top
    (fun a : Σ i, (V i).affineOpens => ⟨f a.1 ''ᵁ a.2.1, a.2.2.image_of_isOpenImmersion _⟩)
    ?_ ?_
  · refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨i, y, rfl⟩ := hf x
    obtain ⟨W, hW, hyW, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1
      (V i).isBasis_affineOpens) (show y ∈ (⊤ : (V i).Opens) from trivial)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨i, ⟨W, hW⟩⟩, ⟨y, hyW, rfl⟩⟩
  · rintro ⟨i, W⟩
    have hi := h i W
    rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
      Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion] at hi
    exact (Ideal.comap_le_comap_iff_of_surjective _
      (ConcreteCategory.bijective_of_isIso ((f i).appIso W).inv).2 _ _).1 hi

private theorem eq_of_forall_comap_eq {U : Scheme.{w}} {ι : Type w} {V : ι → Scheme.{w}}
    (f : ∀ i, V i ⟶ U) [∀ i, IsOpenImmersion (f i)] (hf : ∀ x, ∃ i, x ∈ Set.range (f i))
    {J₁ J₂ : U.IdealSheafData} (h : ∀ i, J₁.comap (f i) = J₂.comap (f i)) : J₁ = J₂ :=
  (le_of_forall_comap_le f hf fun i => (h i).le).antisymm
    (le_of_forall_comap_le f hf fun i => (h i).ge)

section Chart

variable {k : Type w} [Field k] {X : Scheme.{w}} (sX : X ⟶ Spec (.of k))
  (I : X.IdealSheafData) (E : OrderedDivisor X) (H H' : X.IdealSheafData)

/-- The conditions of an étale equivalence on a single chart `ψ, ψ' : U → X`, with the
derivative condition written as `(ψ, ψ')^*(I_Δ) ⊆ ψ^* D^{m-1}(I)`. -/
private structure IsLocalChartPair {U : Scheme.{w}} (ψ ψ' : U ⟶ X) : Prop where
  etale : Etale ψ
  etale' : Etale ψ'
  comp_eq : ψ ≫ sX = ψ' ≫ sX
  comap_H : H.comap ψ = H'.comap ψ'
  comap_I : I.comap ψ = I.comap ψ'
  comap_E : ∀ i, (E.E i).comap ψ = (E.E i).comap ψ'
  diagonal_le : (pullback.diagonal sX).ker.comap (pullback.lift ψ ψ' comp_eq) ≤
    (higherDerivativeIdeal sX I ((maxOrder I).toNat - 1)).comap ψ

variable {sX I E H H'}

private theorem comp_lift_eq {U U' : Scheme.{w}} (j : U' ⟶ U) {ψ ψ' : U ⟶ X}
    (h : ψ ≫ sX = ψ' ≫ sX) :
    j ≫ pullback.lift ψ ψ' h = pullback.lift (j ≫ ψ) (j ≫ ψ') (by simp [h]) := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]

private theorem IsLocalChartPair.comp {U U' : Scheme.{w}} {ψ ψ' : U ⟶ X}
    (h : IsLocalChartPair sX I E H H' ψ ψ') (j : U' ⟶ U) [Etale j] :
    IsLocalChartPair sX I E H H' (j ≫ ψ) (j ≫ ψ') := by
  have := h.etale
  have := h.etale'
  refine ⟨inferInstance, inferInstance, by simp [h.comp_eq], ?_, ?_, fun i => ?_, ?_⟩
  · rw [Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp, h.comap_H]
  · rw [Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp, h.comap_I]
  · rw [Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp, h.comap_E i]
  · rw [← comp_lift_eq j h.comp_eq, Scheme.IdealSheafData.comap_comp,
      Scheme.IdealSheafData.comap_comp]
    exact Scheme.IdealSheafData.comap_mono j h.diagonal_le

/-- Every point of a coproduct of schemes lies in one of the summands. -/
private theorem exists_mem_range_sigmaι {σ : Type w} (U : σ → Scheme.{w})
    (x : (∐ U : Scheme.{w})) :
    ∃ i, x ∈ Set.range (Sigma.ι U i) := by
  obtain ⟨i, y, rfl⟩ := (sigmaOpenCover U).exists_eq x
  exact ⟨i, y, rfl⟩

/-- Pull-backs of ideal sheaves along `Sigma.desc ψ` and `Sigma.desc ψ'` agree when they agree
on every summand. -/
private theorem comap_sigmaDesc_eq {Y : Scheme.{w}} {σ : Type w} {U : σ → Scheme.{w}}
    {ψ ψ' : ∀ i, U i ⟶ Y} {J J' : Y.IdealSheafData} (h : ∀ i, J.comap (ψ i) = J'.comap (ψ' i)) :
    J.comap (Sigma.desc ψ) = J'.comap (Sigma.desc ψ') :=
  eq_of_forall_comap_eq (Sigma.ι U) (exists_mem_range_sigmaι U) fun i => by
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, Sigma.ι_desc,
      Sigma.ι_desc, h i]

private theorem IsLocalChartPair.sigmaDesc {σ : Type w} {U : σ → Scheme.{w}}
    {ψ ψ' : ∀ i, U i ⟶ X} (h : ∀ i, IsLocalChartPair sX I E H H' (ψ i) (ψ' i)) :
    IsLocalChartPair sX I E H H' (Sigma.desc ψ) (Sigma.desc ψ') := by
  have hc : Sigma.desc ψ ≫ sX = Sigma.desc ψ' ≫ sX :=
    Sigma.hom_ext _ _ fun i => by simp [(h i).comp_eq]
  have : IsZariskiLocalAtSource @Etale := HasRingHomProperty.instIsZariskiLocalAtSource
  refine ⟨IsZariskiLocalAtSource.sigmaDesc fun i => (h i).etale,
    IsZariskiLocalAtSource.sigmaDesc fun i => (h i).etale', hc, ?_, ?_, fun e => ?_, ?_⟩
  · exact comap_sigmaDesc_eq fun i => (h i).comap_H
  · exact comap_sigmaDesc_eq fun i => (h i).comap_I
  · exact comap_sigmaDesc_eq fun i => (h i).comap_E e
  · refine le_of_forall_comap_le (Sigma.ι U) (exists_mem_range_sigmaι U) fun i => ?_
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, Sigma.ι_desc,
      comp_lift_eq]
    simp only [Sigma.ι_desc]
    exact (h i).diagonal_le

end Chart

/-- An étale morphism of schemes has open image. -/
private theorem isOpen_range_of_etale {U Y : Scheme.{w}} {f : U ⟶ Y} (hf : Etale f) :
    IsOpen (Set.range f) :=
  (@Scheme.Hom.isOpenMap _ _ f (UniversallyOpen.of_flat _)).isOpen_range

/-- Higher derivative ideals commute with pull-back along a smooth morphism. -/
private theorem higherDerivativeIdeal_comap_of_smooth {k : Type w} [Field k] {X Y : Scheme.{w}}
    (sX : X ⟶ Spec (.of k)) [Smooth sX]
    (hdim : ∀ Z ∈ irreducibleComponents X, 0 < topologicalKrullDim Z)
    (I : X.IdealSheafData) (f : Y ⟶ X) [Smooth f] (j : ℕ) :
    higherDerivativeIdeal (f ≫ sX) (I.comap f) j = (higherDerivativeIdeal sX I j).comap f := by
  induction j with
  | zero => rfl
  | succ r ih =>
    rw [higherDerivativeIdeal_succ, higherDerivativeIdeal_succ, ih,
      derivativeIdeal_comap_of_smooth sX (f ≫ sX) f rfl hdim]

/-- An snc family stays snc after reindexing along an injective map. -/
private theorem IsSNCFamily.comp_injective {k : Type w} [Field k] {X : Scheme.{w}}
    {sX : X ⟶ Spec (.of k)} {Λ Λ' : Type*} {F : Λ → X.IdealSheafData} (hF : IsSNCFamily sX F)
    {σ : Λ' → Λ} (hσ : Function.Injective σ) : IsSNCFamily sX (F ∘ σ) := by
  refine ⟨fun i => hF.1 (σ i), fun x => ?_⟩
  obtain ⟨n, z, c, hz, hc, hinj⟩ := hF.2 x
  exact ⟨n, z, fun i => c ⟨σ i.1, i.2⟩, hz, fun i => hc ⟨σ i.1, i.2⟩,
    fun i j hij => Subtype.ext (hσ (congrArg Subtype.val (hinj hij)))⟩

private theorem isSNCFamily_option_elim {k : Type w} [Field k] {X : Scheme.{w}}
    {sX : X ⟶ Spec (.of k)} {E : OrderedDivisor X} {H : X.IdealSheafData}
    (h : IsSNCFamily sX (Fin.cons H E.E : Fin (E.s + 1) → X.IdealSheafData)) :
    IsSNCFamily sX (fun o : Option (Fin E.s) => o.elim H E.E) := by
  have hσ : Function.Injective (fun o : Option (Fin E.s) => o.elim 0 Fin.succ) := by
    rintro (_ | a) (_ | b) hab
    · rfl
    · exact absurd hab.symm (Fin.succ_ne_zero b)
    · exact absurd hab (Fin.succ_ne_zero a)
    · exact congrArg some (Fin.succ_injective _ hab)
  convert IsSNCFamily.comp_injective h hσ using 1
  funext o
  rcases o with _ | a <;> simp

/-- An étale chart pair on an open `U` of a scheme, with `ψ, ψ'` sending `w ∈ U` to `p`, shrinks
to an affine chart pair through `p`. -/
private theorem exists_affine_isLocalChartPair_of_open {k : Type w} [Field k] {X : Scheme.{w}}
    (sX : X ⟶ Spec (.of k)) [Smooth sX]
    (hdim : ∀ Z ∈ irreducibleComponents X, 0 < topologicalKrullDim Z)
    {I : X.IdealSheafData} {E : OrderedDivisor X} {H H' : X.IdealSheafData} {p : X}
    {W : Scheme.{w}} {ψ ψ' : W ⟶ X} (U : W.Opens) {w : W} (hw : w ∈ U)
    (hcomp : (U.ι ≫ ψ) ≫ sX = (U.ι ≫ ψ') ≫ sX) (hψw : ψ w = p) (hψ'w : ψ' w = p)
    (het : Etale (U.ι ≫ ψ)) (het' : Etale (U.ι ≫ ψ'))
    (hH : H.comap (U.ι ≫ ψ) = H'.comap (U.ι ≫ ψ'))
    (hI : I.comap (U.ι ≫ ψ) = I.comap (U.ι ≫ ψ'))
    (hE : ∀ i, (E.E i).comap (U.ι ≫ ψ) = (E.E i).comap (U.ι ≫ ψ'))
    (hdiag : (pullback.diagonal sX).ker.comap (pullback.lift (U.ι ≫ ψ) (U.ι ≫ ψ') hcomp) ≤
      higherDerivativeIdeal ((U.ι ≫ ψ) ≫ sX) (I.comap (U.ι ≫ ψ)) ((maxOrder I).toNat - 1)) :
    ∃ (U : Scheme.{w}) (_ : IsAffine U) (ψ ψ' : U ⟶ X), IsLocalChartPair sX I E H H' ψ ψ' ∧
      p ∈ Set.range ψ ∩ Set.range ψ' := by
  have base : IsLocalChartPair sX I E H H' (U.ι ≫ ψ) (U.ι ≫ ψ') :=
    ⟨het, het', hcomp, hH, hI, hE, by
      haveI := het
      rw [← higherDerivativeIdeal_comap_of_smooth sX hdim]
      exact hdiag⟩
  obtain ⟨U₀, hU₀, hwU₀, -⟩ : ∃ U₀ ∈ U.toScheme.affineOpens, _ ∧ _ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.1
    U.toScheme.isBasis_affineOpens) (show (⟨w, hw⟩ : U.toScheme) ∈ (⊤ : U.toScheme.Opens) from
      trivial)
  haveI : IsAffine (U₀ : U.toScheme.Opens).toScheme := hU₀
  refine ⟨(U₀ : U.toScheme.Opens).toScheme, inferInstance, Scheme.Opens.ι U₀ ≫ U.ι ≫ ψ,
    Scheme.Opens.ι U₀ ≫ U.ι ≫ ψ', base.comp (Scheme.Opens.ι U₀),
    ⟨⟨⟨w, hw⟩, hwU₀⟩, hψw⟩, ⟨⟨⟨w, hw⟩, hwU₀⟩, hψ'w⟩⟩

/-- At a closed point `p` of `cosupp(I, m)` there is an affine chart pair through `p`. -/
private theorem exists_isLocalChartPair {k : Type w} [Field k]
    [CharZero k] {X : Scheme.{w}} (sX : X ⟶ Spec (.of k)) [Smooth sX] [QuasiCompact sX]
    (hX : TopologicalSpace.Equidimensional X)
    (hdim : ∀ Z ∈ irreducibleComponents X, 0 < topologicalKrullDim Z)
    {I : X.IdealSheafData} (hI : IsMCInvariant sX I) (hIgen : IsNonzeroAtGenericPoints I)
    {m : ℕ} (hm1 : 1 ≤ m) (hm : maxOrder I = m)
    {E : OrderedDivisor X} (hEo : E.IsOrderedDivisor) (hE : E.IsSNC sX)
    {H H' : X.IdealSheafData} (hH : IsSmoothHypersurface sX H) (hH' : IsSmoothHypersurface sX H')
    (hHI : H ≤ maximalContactIdeal sX I) (hH'I : H' ≤ maximalContactIdeal sX I)
    (hHE : IsSNCFamily sX (Fin.cons H E.E : Fin (E.s + 1) → X.IdealSheafData))
    (hH'E : IsSNCFamily sX (Fin.cons H' E.E : Fin (E.s + 1) → X.IdealSheafData))
    {p : X} (hp : IsClosed ({p} : Set X))
    (hpZ : p ∈ (⟨I, (maxOrder I).toNat⟩ : MarkedIdeal X).cosupport) :
    ∃ (U : Scheme.{w}) (_ : IsAffine U) (ψ ψ' : U ⟶ X), IsLocalChartPair sX I E H H' ψ ψ' ∧
      p ∈ Set.range ψ ∩ Set.range ψ' := by
  classical
  have hmt : (maxOrder I).toNat = m := by rw [hm]; rfl
  have hpm : multAt I p = m := le_antisymm
    (hm ▸ le_iSup₂ (f := fun z (_ : z ∈ Set.univ) => multAt I z) p (Set.mem_univ p))
    (by simpa [MarkedIdeal.cosupport, hmt] using hpZ)
  have hpMC : p ∈ ((maximalContactIdeal sX I).support : Set X) := by
    have h1 : (((m - 1 + 1 : ℕ)) : ℕ∞) ≤ multAt I p := by
      rw [Nat.sub_add_cancel hm1, hpm]
    have h2 := (succ_le_multAt_iff_forall_mem_support sX I (m - 1) p).1 h1 (m - 1) le_rfl
    simpa [maximalContactIdeal, hmt] using h2
  have hpH : p ∈ (H.support : Set X) := Scheme.IdealSheafData.support_antitone hHI hpMC
  have hpH' : p ∈ (H'.support : Set X) := Scheme.IdealSheafData.support_antitone hH'I hpMC
  have hF := isSNCFamily_option_elim hHE
  have hF' := isSNCFamily_option_elim hH'E
  obtain ⟨n₀, z, c, hz, hc, -⟩ := hF.2 p
  obtain ⟨n₀', z', c', -, hc', -⟩ := hF'.2 p
  let x₁ := z (c ⟨none, hpH⟩)
  let x₁' := z' (c' ⟨none, hpH'⟩)
  have hx₁ : IdealSheafData.stalk H p = Ideal.span {x₁} := hc ⟨none, hpH⟩
  have hx₁' : IdealSheafData.stalk H' p = Ideal.span {x₁'} := hc' ⟨none, hpH'⟩
  let ε := (Fintype.equivFin {i // p ∈ ((E.E i).support : Set X)}).symm
  let e : Fin _ → X.presheaf.stalk p := fun j => z (c ⟨some (ε j), (ε j).2⟩)
  have he : ∀ j, IdealSheafData.stalk (E.E (ε j)) p = Ideal.span {e j} :=
    fun j => hc ⟨some (ε j), (ε j).2⟩
  haveI : LocallyOfFiniteType sX := inferInstance
  have hn : topologicalKrullDimAt X p = n₀ := by
    rw [topologicalKrullDimAt_eq_krullDimOfRing_stalk k X sX p hp, hz.2]
  obtain ⟨m', -, x, hreg, hreg'⟩ := exists_isRegularSystemOfParameters_cons_append_of_isSNCFamily
    sX ((MMP.Mori.isSmoothScheme_iff sX).2 inferInstance) hX E H H' hF hF' p hp hn hpH hpH'
    x₁ x₁' hx₁ hx₁' ε e he
  obtain ⟨V₁, hpV₁, s₁, hs₁, hloc₁⟩ :=
    MMP.Flips.ResolutionInputs.exists_isLocalCoordinatesAt_of_isRegularSystemOfParameters sX p hp
      _ hreg
  obtain ⟨V₂, hpV₂, s₂, hs₂, hloc₂⟩ :=
    MMP.Flips.ResolutionInputs.exists_isLocalCoordinatesAt_of_isRegularSystemOfParameters sX p hp
      _ hreg'
  have hgerm : ∀ l : Fin (Fintype.card {i // p ∈ ((E.E i).support : Set X)} + m'),
      (X.presheaf.germ V₁ p hpV₁).hom (s₁ l.succ) =
      (X.presheaf.germ V₂ p hpV₂).hom (s₂ l.succ) := fun l => by
    rw [hs₁, hs₂, Fin.cons_succ, Fin.cons_succ]
  choose W hpW iW₁ iW₂ hW using fun l =>
    TopCat.Presheaf.germ_eq X.presheaf p hpV₁ hpV₂ _ _ (hgerm l)
  let W₀ : X.Opens := V₁ ⊓ V₂ ⊓ ⟨⋂ l, (W l : Set X), isOpen_iInter_of_finite fun l => (W l).2⟩
  have hpW₀ : p ∈ W₀ := ⟨⟨hpV₁, hpV₂⟩, Set.mem_iInter.2 hpW⟩
  obtain ⟨V, hVaff, hpV, hVW₀⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1
    X.isBasis_affineOpens) hpW₀
  have hV₁ : V ≤ V₁ := hVW₀.trans (inf_le_left.trans inf_le_left)
  have hV₂ : V ≤ V₂ := hVW₀.trans (inf_le_left.trans inf_le_right)
  have hVW : ∀ l, V ≤ W l := fun l => hVW₀.trans (inf_le_right.trans
    (show (⟨⋂ l, (W l : Set X), _⟩ : X.Opens) ≤ W l from Set.iInter_subset _ l))
  let r₁ := fun a : Γ(X, V₁) => (X.presheaf.map (homOfLE hV₁).op).hom a
  let r₂ := fun a : Γ(X, V₂) => (X.presheaf.map (homOfLE hV₂).op).hom a
  let y : Fin (Fintype.card {i // p ∈ ((E.E i).support : Set X)} + m') → Γ(X, V) :=
    fun l => r₁ (s₁ l.succ)
  have hy : ∀ l, r₂ (s₂ l.succ) = y l := fun l => by
    have := congrArg (X.presheaf.map (homOfLE (hVW l)).op).hom (hW l)
    simp only [r₁, r₂, y]
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp,
      ← Functor.map_comp] at this
    exact this.symm
  have hcons₁ : (fun i => r₁ (s₁ i)) = (Fin.cons (r₁ (s₁ 0)) y : Fin _ → Γ(X, V)) := by
    funext i
    refine Fin.cases ?_ (fun l => ?_) i <;> simp [y]
  have hcons₂ : (fun i => r₂ (s₂ i)) = (Fin.cons (r₂ (s₂ 0)) y : Fin _ → Γ(X, V)) := by
    funext i
    refine Fin.cases ?_ (fun l => ?_) i <;> simp [hy]
  have hl₁ : IsLocalCoordinatesAt sX V (Fin.cons (r₁ (s₁ 0)) y : Fin _ → Γ(X, V)) p hpV := by
    rw [← hcons₁]
    exact MMP.Flips.ResolutionInputs.IsLocalCoordinatesAt.res hV₁ hpV hloc₁
  have hl₂ : IsLocalCoordinatesAt sX V (Fin.cons (r₂ (s₂ 0)) y : Fin _ → Γ(X, V)) p hpV := by
    rw [← hcons₂]
    exact MMP.Flips.ResolutionInputs.IsLocalCoordinatesAt.res hV₂ hpV hloc₂
  have hg₁ : ∀ i, (X.presheaf.germ V p hpV).hom (r₁ (s₁ i)) = _ := fun i =>
    (TopCat.Presheaf.germ_res_apply _ _ _ _ _).trans (hs₁ i)
  have hg₂ : ∀ i, (X.presheaf.germ V p hpV).hom (r₂ (s₂ i)) = _ := fun i =>
    (TopCat.Presheaf.germ_res_apply _ _ _ _ _).trans (hs₂ i)
  have hreg₁ : MMP.Mori.IsRegularSystemOfParameters (fun i => (X.presheaf.germ V p hpV).hom
      ((Fin.cons (r₁ (s₁ 0)) y : Fin _ → Γ(X, V)) i)) := by
    rw [← hcons₁]
    exact (funext hg₁ : _ = _) ▸ hreg
  have hreg₂ : MMP.Mori.IsRegularSystemOfParameters (fun i => (X.presheaf.germ V p hpV).hom
      ((Fin.cons (r₂ (s₂ 0)) y : Fin _ → Γ(X, V)) i)) := by
    rw [← hcons₂]
    exact (funext hg₂ : _ = _) ▸ hreg'
  have hEy : ∀ i, p ∈ ((E.E i).support : Set X) →
      ∃ l, IdealSheafData.stalk (E.E i) p = Ideal.span {(X.presheaf.germ V p hpV).hom (y l)} := by
    intro i hi
    refine ⟨Fin.castAdd m' (ε.symm ⟨i, hi⟩), ?_⟩
    simp only [y]
    rw [hg₁, Fin.cons_succ, Fin.append_left]
    simpa using he (ε.symm ⟨i, hi⟩)
  obtain ⟨Uo, w, hw, hcomp, -, hψw, hψ'w, het, het', hHc, hIc, hEc, hdiag⟩ :=
    exists_etale_realization_of_formalUniqueness sX hX hdim hI hIgen hm1 hm hEo hE hH hH' hHI hH'I
      hp hpm hVaff hpV hl₁ hl₂ (by rw [hg₁, Fin.cons_zero]; exact hx₁)
      (by rw [hg₂, Fin.cons_zero]; exact hx₁') hreg₁ hreg₂ hEy
  exact exists_affine_isLocalChartPair_of_open sX hdim Uo hw hcomp hψw hψ'w het het' hHc hIc hEc
    hdiag

end Proof_thm_kr3d_uniqueness_of_maximal_contact

namespace MMP.Resolution

open Proof_thm_kr3d_uniqueness_of_maximal_contact in
/-- **Uniqueness of maximal contact** (Kollár Thm. 3.92, corrected). Let `X` be
smooth, equidimensional and of finite type over a field `k` of characteristic `0`, with every
irreducible component of positive dimension. Let `I` be a maximal contact invariant ideal sheaf,
nonzero at the generic points, with `m = maxord I ≥ 1`, and `E` an ordered snc divisor. If
`H, H'` are smooth hypersurfaces whose ideal sheaves lie in `maximalContactIdeal sX I` and
`H + ∑ᵢ E^i`, `H' + ∑ᵢ E^i` are snc, then `H` and `H'` are étale equivalent with respect to
`(X, I, E)` (`AreEtaleEquivalentHypersurfaces`). -/
@[mmp "thm_kr3d_uniqueness_of_maximal_contact"]
public theorem areEtaleEquivalentHypersurfaces_of_le_maximalContactIdeal {k : Type u} [Field k]
    [CharZero k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [Smooth sX] [QuasiCompact sX]
    (hX : TopologicalSpace.Equidimensional X)
    (hdim : ∀ Z ∈ irreducibleComponents X, 0 < topologicalKrullDim Z)
    {I : X.IdealSheafData} (hI : IsMCInvariant sX I) (hIgen : IsNonzeroAtGenericPoints I)
    {m : ℕ} (hm1 : 1 ≤ m) (hm : maxOrder I = m)
    {E : OrderedDivisor X} (hEo : E.IsOrderedDivisor) (hE : E.IsSNC sX)
    {H H' : X.IdealSheafData} (hH : IsSmoothHypersurface sX H) (hH' : IsSmoothHypersurface sX H')
    (hHI : H ≤ maximalContactIdeal sX I) (hH'I : H' ≤ maximalContactIdeal sX I)
    (hHE : IsSNCFamily sX (Fin.cons H E.E : Fin (E.s + 1) → X.IdealSheafData))
    (hH'E : IsSNCFamily sX (Fin.cons H' E.E : Fin (E.s + 1) → X.IdealSheafData)) :
    AreEtaleEquivalentHypersurfaces sX I E H H' := by
  classical
  haveI : CompactSpace X := (quasiCompact_iff_compactSpace sX).1 inferInstance
  set Z := (⟨I, (maxOrder I).toNat⟩ : MarkedIdeal X).cosupport with hZdef
  have hZ : IsClosed Z := isClosed_setOf_le_multAt sX I _
  have hchart : ∀ p : {p : X // IsClosed ({p} : Set X) ∧ p ∈ Z}, ∃ (U : Scheme.{u})
      (_ : IsAffine U) (ψ ψ' : U ⟶ X), IsLocalChartPair sX I E H H' ψ ψ' ∧
        p.1 ∈ Set.range ψ ∩ Set.range ψ' := fun p =>
    exists_isLocalChartPair sX hX hdim hI hIgen hm1 hm hEo hE hH hH' hHI hH'I hHE hH'E p.2.1 p.2.2
  choose U hU ψ ψ' hψ hp using hchart
  let O : {p : X // IsClosed ({p} : Set X) ∧ p ∈ Z} → Set X :=
    fun p => Set.range (ψ p) ∩ Set.range (ψ' p)
  have hO : ∀ p, IsOpen (O p) := fun p =>
    (isOpen_range_of_etale (hψ p).etale).inter (isOpen_range_of_etale (hψ p).etale')
  have hZO : Z ⊆ ⋃ p, O p := by
    intro x hx
    obtain ⟨q, hq, hqc⟩ := IsClosed.exists_closed_singleton (isClosed_closure (s := {x}))
      ⟨x, subset_closure rfl⟩
    have hqZ : q ∈ Z := hZ.closure_subset_iff.2 (Set.singleton_subset_iff.2 hx) hq
    obtain ⟨y, hyO, rfl⟩ := mem_closure_iff.1 hq _ (hO ⟨q, hqc, hqZ⟩) (hp ⟨q, hqc, hqZ⟩)
    exact Set.mem_iUnion.2 ⟨_, hyO⟩
  obtain ⟨t, ht⟩ := hZ.isCompact.elim_finite_subcover O hO hZO
  let V : t → Scheme.{u} := fun p => U p.1
  haveI : ∀ p : t, IsAffine (V p) := fun p => hU p.1
  have h := IsLocalChartPair.sigmaDesc (U := V) (ψ := fun p => ψ p.1) (ψ' := fun p => ψ' p.1)
    fun p => hψ p.1
  haveI := h.etale
  haveI := h.etale'
  have hrange : ∀ (χ : ∀ p : t, V p ⟶ X), Z ⊆ (⋃ p : t, Set.range (χ p)) →
      Z ⊆ Set.range (Sigma.desc χ) := by
    intro χ hχ x hx
    obtain ⟨p, y, rfl⟩ := Set.mem_iUnion.1 (hχ hx)
    exact ⟨Sigma.ι V p y, by rw [← Scheme.Hom.comp_apply, Sigma.ι_desc]⟩
  have hZt : ∀ x ∈ Z, ∃ p : t, x ∈ O p.1 := fun x hx => by
    obtain ⟨p, hpt, hxp⟩ := Set.mem_iUnion₂.1 (ht hx)
    exact ⟨⟨p, hpt⟩, hxp⟩
  refine ⟨∐ V, Sigma.desc (fun p => ψ p.1) ≫ sX, Sigma.desc (fun p => ψ p.1),
    Sigma.desc (fun p => ψ' p.1), ⟨inferInstance, (quasiCompact_iff_compactSpace _).2
      inferInstance, h.etale, h.etale', rfl, h.comp_eq.symm, ?_, ?_, h.comap_I, ?_⟩,
    h.comap_H, h.comap_E⟩
  · refine hrange _ fun x hx => ?_
    obtain ⟨p, hxp⟩ := hZt x hx
    exact Set.mem_iUnion.2 ⟨p, hxp.1⟩
  · refine hrange _ fun x hx => ?_
    obtain ⟨p, hxp⟩ := hZt x hx
    exact Set.mem_iUnion.2 ⟨p, hxp.2⟩
  · rw [higherDerivativeIdeal_comap_of_smooth sX hdim]
    exact h.diagonal_le

end MMP.Resolution

end

end
