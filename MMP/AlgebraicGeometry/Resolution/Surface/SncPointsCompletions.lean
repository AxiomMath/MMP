module
public import MMP.AlgebraicGeometry.Resolution.SNCRestriction
public import MMP.AlgebraicGeometry.Resolution.DivisorialPart
public import MMP.RingTheory.PowerSeries.CompleteLocalRing
public import MMP.AlgebraicGeometry.Resolution.BlowupSequence.PushforwardSmooth
public import MMP.AlgebraicGeometry.Resolution.SNCAffineLineExample
public import MMP.AlgebraicGeometry.MMP.Steps

/-!
# Kollár's resolution lemmas: snc points, normalizations, completions and orders

This file collects auxiliary results from Kollár's *Lectures on resolution of singularities*
used in the resolution of singularities of surfaces and in the order-reduction step.

* A morphism `h : T → S` whose composite with `π : S → S₀` makes the reduced total transform of a
  closed subscheme `C₀ ⊆ S₀` an snc divisor is not an isomorphism near a closed point where
  `(π⁻¹ C₀)_red` fails to have simple normal crossings (Kollár 1.48).
* In characteristic `p`, adjoining `p^m`-th roots `ξᵢ` of algebraically independent elements
  `xᵢ` to a finite extension `k'` of `k` gives an integrally closed ring `k'[ξ₁, …, ξₙ]`: the
  `ξᵢ` are algebraically independent over `k'`, so it is a polynomial ring (proof of Thm. 1.33).
* On a regular surface, a curve `C` with principal nonzero ideal `(f)` at a closed point `p` has
  regular local ring at `p` iff `mult_p C = 1`: the cotangent space of `𝒪_{C,p}` is
  `𝔪 / (𝔪² + f 𝒪_{S,p})`, of dimension `1` exactly when `f ∉ 𝔪²` (§1.8).
* A variety `Y` over `k` has a normalization in every finite extension `L` of `k(Y)`: the relative
  normalization of `Spec L → Y`, which is finite because `Y` is Nagata (2.21, 2.22).
* At a closed point `p` of a scheme locally of finite type over a field `k` of characteristic
  zero, the completion `𝒪̂_{p,X}` has a field of representatives containing `k`; if `X` is smooth
  and `x₁, …, xₙ` is a regular system of parameters, then `𝒪̂_{p,X} ≃ κ(p)[[t₁, …, tₙ]]` as
  `k`-algebras with `tᵢ ↦ xᵢ` (Def. 3.55).
* On `𝔸¹_k`, appending the centre `D = (x)` of a smooth blow-up of the marked triple
  `(𝔸¹_k, D, 1, (D))` to `E = (D)` does not give an ordered snc divisor (3.64–3.65).
* At a point with regular local ring, `ord_x (I ^ c) = c · ord_x I`, since initial forms multiply
  in the associated graded ring, a domain (§3).

## Main results

* `MMP.Resolution.not_isIso_morphismRestrict_of_not_hasSNCAt`
* `MMP.Resolution.isIntegrallyClosed_adjoin_pow_roots`
* `MMP.Resolution.Kollar.isRegularLocalRing_stalk_quotient_iff_multAt_eq_one`
* `MMP.Resolution.exists_isNormalizationInExtension`
* `MMP.Resolution.exists_isFieldOfRepresentatives_completion`
* `MMP.Resolution.exists_mvPowerSeries_algEquiv_completion`
* `MMP.Resolution.not_isOrderedSNC_snoc_of_isSmoothBlowupOfMarkedTriple_line`
* `MMP.Resolution.multAt_pow`

## Implementation notes

Closed subschemes are ideal sheaves `Scheme.IdealSheafData`; the reduced structure on a support is
`Scheme.IdealSheafData.vanishingIdeal`, and the order of an ideal sheaf at a point is
`MMP.Resolution.multAt`, with values in `ℕ∞`. In `isIntegrallyClosed_adjoin_pow_roots` the
ambient field is any field `L ⊇ k` containing algebraically independent `x₁, …, xₙ`, rather than
an algebraic closure of `k(x₁, …, xₙ)`. In `multAt_pow` smoothness is weakened to regularity of
the local ring and the hypothesis `I_x ≠ 0` is dropped: when `I_x = 0` both sides are `∞` for
`c ≥ 1` and `0` for `c = 0`. The completion of a local ring is
`AdicCompletion (maximalIdeal 𝒪_{p,X}) 𝒪_{p,X}`, a `k`-algebra through `MMP.Mori.stalkAlgebra`.

## References

* [J. Kollár, *Lectures on resolution of singularities*][kollar2007]
* [H. Matsumura, *Commutative ring theory*, Thm. 14.2][matsumura1989]
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace MMP.Resolution

/-! ### Points without simple normal crossings are blown up -/

section

variable {X Y : Scheme.{u}}

/-- Simple normal crossings at `f x` restrict along an open immersion `f`. -/
private theorem hasSNCAt_comap (f : X ⟶ Y) [IsOpenImmersion f]
    (I : Y.IdealSheafData) (x : X) (h : HasSNCAt I (f x)) : HasSNCAt (I.comap f) x := by
  obtain ⟨d, U, hU, s, m, hreg, hst⟩ := h
  have _ : ∀ q, IsIso (f.stalkMap q) := IsOpenImmersion.instIsIsoCommRingCatStalkMap f
  have hgerm : ∀ (q : X) (hq : q ∈ f ⁻¹ᵁ U) (t : Γ(Y, U)),
      (X.presheaf.germ (f ⁻¹ᵁ U) q hq).hom ((f.app U).hom t) =
        (f.stalkMap q).hom ((Y.presheaf.germ U (f q) hq).hom t) := fun q hq t =>
    (congrArg (fun φ => φ.hom t) (Scheme.Hom.germ_stalkMap f U q hq)).symm
  refine ⟨d, f ⁻¹ᵁ U, hU, fun i => (f.app U).hom (s i), m, ?_, ?_⟩
  · have hfun : (fun i => (X.presheaf.germ (f ⁻¹ᵁ U) x hU).hom ((f.app U).hom (s i))) =
        fun i => (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv
          ((Y.presheaf.germ U (f x) hU).hom (s i)) :=
      funext fun i => hgerm x hU (s i)
    rw [hfun]
    exact hreg.map_ringEquiv _
  · intro q hq
    rw [IdealSheafData.stalk_comap, hst (f q) hq, Ideal.map_span, Set.image_singleton,
      ← hgerm]
    simp [map_prod, map_pow]

/-- Simple normal crossings at `x` extend along an open immersion `f` to `f x`. -/
private theorem hasSNCAt_of_comap (f : X ⟶ Y) [IsOpenImmersion f]
    (I : Y.IdealSheafData) (x : X) (h : HasSNCAt (I.comap f) x) : HasSNCAt I (f x) := by
  obtain ⟨d, U, hU, s, m, hreg, hst⟩ := h
  have _ : ∀ q, IsIso (f.stalkMap q) := IsOpenImmersion.instIsIsoCommRingCatStalkMap f
  have hmem : ∀ q ∈ U, f q ∈ f ''ᵁ U := fun q hq => Set.mem_image_of_mem _ hq
  have hgerm : ∀ (q : X) (hq : q ∈ U) (t : Γ(X, U)),
      (f.stalkMap q).hom ((Y.presheaf.germ (f ''ᵁ U) (f q) (hmem q hq)).hom
        ((f.appIso U).inv.hom t)) = (X.presheaf.germ U q hq).hom t := by
    intro q hq t
    have h2 : Y.presheaf.germ (f ''ᵁ U) (f q) (hmem q hq) ≫ f.stalkMap q =
        (f.appIso U).hom ≫ X.presheaf.germ U q hq := by
      rw [Scheme.Hom.germ_stalkMap f (f ''ᵁ U) q (hmem q hq), Scheme.Hom.appIso_hom,
        Category.assoc, X.presheaf.germ_res]
    simpa using congrArg (fun φ => φ.hom ((f.appIso U).inv.hom t)) h2
  let e : ∀ q : X, Y.presheaf.stalk (f q) ≃+* X.presheaf.stalk q := fun q =>
    (asIso (f.stalkMap q)).commRingCatIsoToRingEquiv
  have he : ∀ (q : X) (hq : q ∈ U) (t : Γ(X, U)),
      (Y.presheaf.germ (f ''ᵁ U) (f q) (hmem q hq)).hom ((f.appIso U).inv.hom t) =
        (e q).symm ((X.presheaf.germ U q hq).hom t) := by
    intro q hq t
    rw [RingEquiv.eq_symm_apply]
    exact hgerm q hq t
  refine ⟨d, f ''ᵁ U, hmem x hU, fun i => (f.appIso U).inv.hom (s i), m, ?_, ?_⟩
  · have hfun : (fun i => (Y.presheaf.germ (f ''ᵁ U) (f x) (hmem x hU)).hom
        ((f.appIso U).inv.hom (s i))) = fun i => (e x).symm ((X.presheaf.germ U x hU).hom (s i)) :=
      funext fun i => he x hU (s i)
    rw [hfun]
    exact hreg.map_ringEquiv _
  · intro y hy
    obtain ⟨q, hq, rfl⟩ := hy
    change IdealSheafData.stalk I (f q) = Ideal.span {((Y.presheaf.germ (f ''ᵁ U) (f q)
      (hmem q hq)).hom (∏ i, ((f.appIso U).inv.hom (s i)) ^ m i))}
    have h1 := hst q hq
    rw [IdealSheafData.stalk_comap] at h1
    have h2 : Ideal.map ((e q) : _ →+* _) (IdealSheafData.stalk I (f q)) =
        Ideal.span {(X.presheaf.germ U q hq).hom (∏ i, s i ^ m i)} := h1
    rw [← Ideal.map_of_equiv (I := IdealSheafData.stalk I (f q)) (e q), h2, Ideal.map_span,
      Set.image_singleton]
    congr 2
    simp only [map_prod, map_pow, he q hq]
    rfl

/-- Along an open immersion, the inverse image of the reduced structure on the support of `I` is
the reduced structure on the support of the inverse image of `I`. -/
private theorem comap_vanishingIdeal_support (f : X ⟶ Y) [IsOpenImmersion f]
    (I : Y.IdealSheafData) :
    (Scheme.IdealSheafData.vanishingIdeal I.support).comap f =
      Scheme.IdealSheafData.vanishingIdeal (I.comap f).support := by
  set J := Scheme.IdealSheafData.vanishingIdeal I.support
  have : IsReduced (J.comap f).subscheme :=
    isReduced_of_isOpenImmersion ((J.comapIso f).hom ≫ Limits.pullback.snd f J.subschemeι)
  refine Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme _ _ ?_
  rw [Scheme.IdealSheafData.support_comap, Scheme.IdealSheafData.support_comap]
  congr 1

/-- If `h` is an isomorphism over an open `V ∋ p`, the fibre of `h` over `p` is the single point
`g p`, where `g : V ≅ h⁻¹ V ⊆ T` is the inverse. -/
private theorem preimage_singleton_eq (h : X ⟶ Y) (V : Y.Opens) [IsIso (h ∣_ V)] (p : Y)
    (hpV : p ∈ V) :
    h ⁻¹' {p} = {(inv (h ∣_ V) ≫ (h ⁻¹ᵁ V).ι) ⟨p, hpV⟩} := by
  set g : (V : Scheme) ⟶ X := inv (h ∣_ V) ≫ (h ⁻¹ᵁ V).ι
  have hgh : ∀ w : (V : Scheme), h (g w) = V.ι w := fun w => by
    rw [← Scheme.Hom.comp_apply, Category.assoc, ← morphismRestrict_ι,
      IsIso.inv_hom_id_assoc]
  ext t
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  refine ⟨fun ht => ?_, by rintro rfl; exact hgh _⟩
  have hw : t = g ((h ∣_ V) ⟨t, show h t ∈ V from ht ▸ hpV⟩) := by
    change t = (h ⁻¹ᵁ V).ι ((h ∣_ V ≫ inv (h ∣_ V)) _)
    rw [IsIso.hom_inv_id]; rfl
  rw [hw]
  congr 1
  apply V.ι.isOpenEmbedding.injective
  rw [← hgh, ← hw, ht]
  rfl

end

/-- If `((π ∘ h)⁻¹ C₀)_red` (the composite `h ≫ π`) is an snc divisor on a regular
Noetherian scheme `T` and `(π⁻¹ C₀)_red` does not have simple normal crossings at a closed
point `p` of `S`, then `h : T → S` is not an isomorphism over any open neighbourhood of `p`
(Kollár 1.48). -/
@[mmp "lem_kr1b_non_snc_point_is_blown_up"]
public theorem not_isIso_morphismRestrict_of_not_hasSNCAt {S₀ S T : Scheme.{u}}
    (C₀ : S₀.IdealSheafData) (π : S ⟶ S₀) (h : T ⟶ S) [IsNoetherian T]
    (hT : ∀ t : T, IsRegularLocalRing (T.presheaf.stalk t))
    (hsnc : IsSNCSubscheme
      (Scheme.IdealSheafData.vanishingIdeal (C₀.comap (h ≫ π)).support))
    (p : S) (hpc : IsClosed ({p} : Set S))
    (hp : ¬ HasSNCAt (Scheme.IdealSheafData.vanishingIdeal (C₀.comap π).support) p)
    (V : S.Opens) (hpV : p ∈ V) : ¬ IsIso (h ∣_ V) := by
  intro _
  let g : (V : Scheme) ⟶ T := inv (h ∣_ V) ≫ (h ⁻¹ᵁ V).ι
  have hg : g ≫ h = V.ι := by
    rw [Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
  have hclosed : IsClosed ({g ⟨p, hpV⟩} : Set T) :=
    preimage_singleton_eq h V p hpV ▸ hpc.preimage h.continuous
  have h1 := hasSNCAt_comap g _ _ (hsnc _ hclosed)
  rw [comap_vanishingIdeal_support, ← Scheme.IdealSheafData.comap_comp, ← Category.assoc, hg,
    Scheme.IdealSheafData.comap_comp, ← comap_vanishingIdeal_support] at h1
  exact hp (hasSNCAt_of_comap V.ι _ ⟨p, hpV⟩ h1)

/-! ### Adjoining `p ^ m`-th roots of independent elements -/

open IsLocalRing Opposite

/-- If a finite family `x` algebraically independent over a field `K` lies in the `K`-subalgebra
`K[ξ]` generated by a family `ξ` indexed by the same type, then `ξ` is algebraically independent:
`K[ξ]` has transcendence degree at least `#ι` and is generated by `#ι` elements. -/
private theorem algebraicIndependent_of_mem_adjoin {K L ι : Type*} [Field K] [Field L]
    [Algebra K L] [Finite ι] {x ξ : ι → L} (hx : AlgebraicIndependent K x)
    (hmem : ∀ i, x i ∈ Algebra.adjoin K (Set.range ξ)) : AlgebraicIndependent K ξ := by
  set A := Algebra.adjoin K (Set.range ξ)
  let ξ' : ι → A := fun i => ⟨ξ i, Algebra.subset_adjoin (Set.mem_range_self i)⟩
  have htop : Algebra.adjoin K (Set.range ξ') = ⊤ := by
    rw [show Set.range ξ' = Subtype.val ⁻¹' Set.range ξ by
      ext a
      exact ⟨by rintro ⟨i, rfl⟩; exact ⟨i, rfl⟩, by rintro ⟨i, hi⟩; exact ⟨i, Subtype.ext hi⟩⟩]
    exact Algebra.adjoin_adjoin_coe_preimage
  have : Algebra.IsAlgebraic (Algebra.adjoin K (Set.range ξ')) A :=
    ⟨fun a => isAlgebraic_algebraMap
      (⟨a, htop ▸ Algebra.mem_top⟩ : Algebra.adjoin K (Set.range ξ'))⟩
  have hx' : AlgebraicIndependent K (fun i => (⟨x i, hmem i⟩ : A)) := .of_comp A.val hx
  exact (Algebra.IsAlgebraic.isTranscendenceBasis_of_lift_le_trdeg_of_finite K ξ'
    hx'.lift_cardinalMk_le_trdeg).1.map' (f := A.val) Subtype.val_injective

/-- Let `k` be a field of characteristic `p`, `x₁, …, xₙ` algebraically independent elements of a
field `L ⊇ k`, `ξᵢ ∈ L` with `ξᵢ ^ (p ^ m) = xᵢ`, and `k'` an intermediate field of `L / k` that is
finite over `k`. Then `k'[ξ₁, …, ξₙ] ⊆ L` is integrally closed. -/
@[mmp "lem_kr1b_normalization_in_root_field"]
public theorem isIntegrallyClosed_adjoin_pow_roots {k L : Type*} [Field k] [Field L]
    [Algebra k L] (p : ℕ) [Fact p.Prime] [CharP k p] {n : ℕ} {x : Fin n → L}
    (hx : AlgebraicIndependent k x) (m : ℕ) {ξ : Fin n → L} (hξ : ∀ i, ξ i ^ p ^ m = x i)
    (k' : IntermediateField k L) [FiniteDimensional k k'] :
    IsIntegrallyClosed (Algebra.adjoin k' (Set.range ξ)) := by
  have hξind := algebraicIndependent_of_mem_adjoin (hx.extendScalars (S := k')) fun i =>
    hξ i ▸ pow_mem (Algebra.subset_adjoin (Set.mem_range_self i)) _
  exact .of_equiv hξind.aevalEquiv.toRingEquiv

/-! ### Regular points of a curve on a regular surface -/

/-- If `A → B` is a surjection of Noetherian local rings whose kernel lies in `𝔪_A²`, then
`𝔪_A` needs no more generators than `𝔪_B`. -/
private theorem spanFinrank_le_of_surjective {A B : Type*} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] [CommRing B] [IsLocalRing B] (f : A →+* B)
    (hf : Function.Surjective f) (hker : RingHom.ker f ≤ maximalIdeal A ^ 2) :
    (maximalIdeal A).spanFinrank ≤ (maximalIdeal B).spanFinrank := by
  have : IsLocalHom f := IsLocalHom.of_surjective f hf
  have hBn : IsNoetherianRing B := isNoetherianRing_of_surjective _ _ f hf
  obtain ⟨s, hcard, hs⟩ := Submodule.FG.exists_span_set_encard_eq_spanFinrank
    (maximalIdeal B).fg_of_isNoetherianRing
  have hsfin : s.Finite := Set.finite_of_encard_eq_coe hcard
  let t : Set A := Function.surjInv hf '' s
  have hft : f '' t = s := by
    rw [Set.image_image]; simp [Function.surjInv_eq hf]
  have htfin : t.Finite := hsfin.image _
  have hsm : s ⊆ maximalIdeal B := fun x hx => by
    have : x ∈ Submodule.span B s := Submodule.subset_span hx
    rwa [hs] at this
  have htm : Ideal.span t ≤ maximalIdeal A := by
    rw [Ideal.span_le]
    intro a ha
    have : f a ∈ maximalIdeal B := hsm (hft ▸ Set.mem_image_of_mem f ha)
    change a ∈ maximalIdeal A
    rw [mem_maximalIdeal, mem_nonunits_iff] at this ⊢
    exact fun h => this (h.map f)
  have hle : maximalIdeal A ≤ Ideal.span t ⊔ maximalIdeal A • maximalIdeal A := by
    intro a ha
    have h1 : f a ∈ Ideal.map f (Ideal.span t) := by
      rw [Ideal.map_span, hft]
      change f a ∈ Submodule.span B s
      rw [hs, ← map_maximalIdeal_of_surjective f hf]
      exact Ideal.mem_map_of_mem f ha
    obtain ⟨b, hb, hab⟩ := (Ideal.mem_map_iff_of_surjective f hf).mp h1
    have : a - b ∈ RingHom.ker f := by simp [RingHom.mem_ker, hab]
    have h2 : a - b ∈ maximalIdeal A • maximalIdeal A := by
      have := hker this
      rw [pow_two] at this
      exact this
    simpa using Submodule.add_mem_sup hb h2
  have heq : Ideal.span t = maximalIdeal A :=
    le_antisymm htm (Submodule.le_of_le_smul_of_le_jacobson_bot
      (maximalIdeal A).fg_of_isNoetherianRing (maximalIdeal_le_jacobson _) hle)
  calc (maximalIdeal A).spanFinrank = (Ideal.span t).spanFinrank := by rw [heq]
    _ ≤ t.ncard := Submodule.spanFinrank_span_le_ncard_of_finite htfin
    _ ≤ s.ncard := Set.ncard_image_le hsfin
    _ = _ := by rw [Set.ncard_def, hcard]; simp

/-- In a regular local ring of dimension `2`, an element `f ∈ 𝔪 \ 𝔪²` is part of a system of
two generators of `𝔪`. -/
private theorem exists_span_pair_eq_maximalIdeal {A : Type*} [CommRing A] [IsRegularLocalRing A]
    (hdim : ringKrullDim A = 2) {f : A} (hfm : f ∈ maximalIdeal A)
    (hf2 : f ∉ maximalIdeal A ^ 2) :
    ∃ g : A, Ideal.span {f, g} = maximalIdeal A := by
  have hfin : Module.finrank (ResidueField A) (CotangentSpace A) = 2 := by
    have := (IsRegularLocalRing.iff_finrank_cotangentSpace A).mp inferInstance
    rw [hdim] at this
    exact_mod_cast this
  set v := (maximalIdeal A).toCotangent ⟨f, hfm⟩
  have hv : v ≠ 0 := by
    rwa [Ne, Ideal.toCotangent_eq_zero]
  set N := Submodule.span (ResidueField A) {v}
  have hN : Module.finrank (ResidueField A) N = 1 := finrank_span_singleton hv
  have hQ : Module.finrank (ResidueField A) ((maximalIdeal A).Cotangent ⧸ N) = 1 := by
    have h := Submodule.finrank_quotient_add_finrank N
    rw [hN, hfin] at h
    omega
  obtain ⟨wq, -, hwq⟩ := finrank_eq_one_iff'.mp hQ
  obtain ⟨w, rfl⟩ := N.mkQ_surjective wq
  obtain ⟨⟨g, hgm⟩, hgw⟩ := (maximalIdeal A).toCotangent_surjective w
  refine ⟨g, ?_⟩
  have htop : Submodule.span (ResidueField A)
      ((maximalIdeal A).toCotangent '' {⟨f, hfm⟩, ⟨g, hgm⟩}) = ⊤ := by
    rw [Set.image_pair, hgw, eq_top_iff]
    intro x _
    obtain ⟨c, hc⟩ := hwq (N.mkQ x)
    have hx : x - c • w ∈ N := by
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul]
      simpa [sub_eq_zero] using hc.symm
    obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp hx
    have : x = d • v + c • w := by rw [hd]; abel
    rw [this]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert_of_mem _ rfl)))
  rw [CotangentSpace.span_image_eq_top_iff] at htop
  have := congrArg (Submodule.map (maximalIdeal A).subtype) htop
  rwa [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, Set.image_pair] at this

/-- In a local ring, an element `f ∈ 𝔪` has multiplicity `1` iff `f ∉ 𝔪²`. -/
private theorem mult_eq_one_iff {R : Type*} [CommRing R] [IsLocalRing R] {f : R}
    (hfm : f ∈ maximalIdeal R) :
    MMP.Resolution.mult f = 1 ↔ f ∉ maximalIdeal R ^ 2 := by
  have h1 := (MMP.Resolution.natCast_le_idealOrder_iff' (Ideal.span {f}) 1).2
    (by rwa [pow_one, Ideal.span_singleton_le_iff_mem])
  rw [MMP.Resolution.mult, ← Ideal.span_singleton_le_iff_mem,
    ← MMP.Resolution.natCast_le_idealOrder_iff']
  generalize MMP.Resolution.idealOrder (Ideal.span {f}) = x at h1 ⊢
  induction x using ENat.recTopCoe with
  | top => simp
  | coe n => norm_cast at h1 ⊢; omega

/-- A Krull dimension `d` with `d + 1 = 2` is `1`. -/
private theorem eq_one_of_add_one_eq_two {x : WithBot ℕ∞} (h : x + 1 = 2) : x = 1 := by
  induction x using WithBot.recBotCoe with
  | bot => simp at h
  | coe e =>
    have h' : e + 1 = 2 := WithBot.coe_injective h
    induction e using ENat.recTopCoe with
    | top => simp at h'
    | coe n => norm_cast at h' ⊢; omega

/-- Let `(A, 𝔪)` be a regular local ring of dimension `2` and `0 ≠ f ∈ 𝔪`. Then `A ⧸ (f)` is a
regular local ring iff `f ∉ 𝔪²`. -/
private theorem isRegularLocalRing_quotient_span_singleton_iff {A : Type*} [CommRing A]
    [IsRegularLocalRing A] (hdim : ringKrullDim A = 2) {f : A} (hfm : f ∈ maximalIdeal A)
    (hf0 : f ≠ 0) :
    IsRegularLocalRing (A ⧸ Ideal.span {f}) ↔ f ∉ maximalIdeal A ^ 2 := by
  haveI := IsRegularLocalRing.isDomain A
  have hnt : Ideal.span {f} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact (mem_maximalIdeal f).mp hfm
  haveI : Nontrivial (A ⧸ Ideal.span {f}) := Ideal.Quotient.nontrivial_iff.mpr hnt
  haveI : IsLocalRing (A ⧸ Ideal.span {f}) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have hd : ringKrullDim (A ⧸ Ideal.span {f}) = 1 := eq_one_of_add_one_eq_two <| hdim ▸
    ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hf0) hfm
  constructor
  · intro hreg hf2
    have hA : ((maximalIdeal A).spanFinrank : WithBot ℕ∞) = 2 :=
      hdim ▸ IsRegularLocalRing.spanFinrank_maximalIdeal
    have hB : ((maximalIdeal (A ⧸ Ideal.span {f})).spanFinrank : WithBot ℕ∞) = 1 :=
      hd ▸ IsRegularLocalRing.spanFinrank_maximalIdeal
    have := spanFinrank_le_of_surjective (Ideal.Quotient.mk (Ideal.span {f}))
      Ideal.Quotient.mk_surjective
      (by rwa [Ideal.mk_ker, Ideal.span_singleton_le_iff_mem])
    norm_cast at hA hB
    omega
  · intro hf2
    obtain ⟨g, hg⟩ := exists_span_pair_eq_maximalIdeal hdim hfm hf2
    refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ ?_
    have hm : maximalIdeal (A ⧸ Ideal.span {f}) =
        Ideal.span {Ideal.Quotient.mk (Ideal.span {f}) g} := by
      rw [← map_maximalIdeal_of_surjective (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective,
        ← hg, Ideal.map_span, Set.image_pair,
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self f),
        Ideal.span_insert_zero]
    rw [hd, hm]
    exact_mod_cast (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_singleton _)).trans
      (Set.ncard_singleton _).le

namespace Kollar

/-- **Regular points of a curve on a regular surface.** Let `p` be a closed point of a Noetherian
scheme `S` with `𝒪_{S,p}` regular of dimension `2`, and `C ⊆ S` a closed subscheme through `p`
whose ideal at `p` is generated by a single nonzero `f`. Then `𝒪_{C,p} = 𝒪_{S,p} / I_{C,p}` is a
regular local ring if and only if `MMP.Resolution.multAt C p = 1`. -/
@[mmp "lem_kr1c_curve_point_regular_iff_mult_one"]
public theorem isRegularLocalRing_stalk_quotient_iff_multAt_eq_one {S : Scheme.{u}}
    [IsNoetherian S] {p : S} (hp : IsClosed ({p} : Set S))
    (hreg : IsRegularLocalRing (S.presheaf.stalk p))
    (hdim : ringKrullDim (S.presheaf.stalk p) = 2)
    (C : S.IdealSheafData) (hpC : p ∈ C.support) (f : S.presheaf.stalk p)
    (hf : IdealSheafData.stalk C p = Ideal.span {f}) (hf0 : f ≠ 0) :
    IsRegularLocalRing (S.presheaf.stalk p ⧸ IdealSheafData.stalk C p) ↔
      MMP.Resolution.multAt C p = 1 := by
  have hne : IdealSheafData.stalk C p ≠ ⊤ := fun h =>
    ((IdealSheafData.stalk_eq_top_iff_notMem_support C p).1 h) hpC
  have hfm : f ∈ maximalIdeal (S.presheaf.stalk p) := by
    rw [hf, Ne, Ideal.span_singleton_eq_top] at hne
    exact (mem_maximalIdeal f).mpr hne
  have hmult : MMP.Resolution.multAt C p = MMP.Resolution.mult f := by
    rw [MMP.Resolution.multAt, MMP.Resolution.mult, hf]
  rw [hmult, mult_eq_one_iff hfm, hf]
  exact isRegularLocalRing_quotient_span_singleton_iff hdim hfm hf0

end Kollar

/-! ### The normalization of a variety in a finite extension of its function field -/

/-- The morphism from the spectrum of the function field of an integral scheme sends every point
to the generic point. -/
private theorem fromSpecStalk_genericPoint_apply (Z : Scheme.{u}) [IsIntegral Z]
    (y : Spec Z.functionField) : Z.fromSpecStalk (genericPoint Z) y = genericPoint Z := by
  have : Subsingleton ↥(Spec Z.functionField) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum Z.functionField))
  rw [Subsingleton.elim y (IsLocalRing.closedPoint _), Scheme.fromSpecStalk_closedPoint]

/-- A field map out of the function field gives a morphism landing in every open containing the
generic point. -/
private theorem top_le_preimage_fromSpecStalk_genericPoint (Z : Scheme.{u}) [IsIntegral Z]
    {L : CommRingCat.{u}} (φ : Z.functionField ⟶ L) {U : Z.Opens} (hU : genericPoint Z ∈ U) :
    ⊤ ≤ (Spec.map φ ≫ Z.fromSpecStalk (genericPoint Z)) ⁻¹ᵁ U := fun y _ => by
  change Z.fromSpecStalk (genericPoint Z) (Spec.map φ y) ∈ U
  rwa [fromSpecStalk_genericPoint_apply]

/-- Restricting a section over a nonempty open of an integral scheme to the spectrum of a field
through the generic point is the germ at the generic point followed by the field map. -/
private theorem appLE_fromSpecStalk_genericPoint_ΓSpecIso (Z : Scheme.{u}) [IsIntegral Z]
    {L : CommRingCat.{u}} (φ : Z.functionField ⟶ L) (U : Z.Opens) [Nonempty U]
    (e : ⊤ ≤ (Spec.map φ ≫ Z.fromSpecStalk (genericPoint Z)) ⁻¹ᵁ U) :
    (Spec.map φ ≫ Z.fromSpecStalk (genericPoint Z)).appLE U ⊤ e ≫ (Scheme.ΓSpecIso L).hom =
      Z.germToFunctionField U ≫ φ := by
  have hU : genericPoint Z ∈ U :=
    ((genericPoint_spec Z).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  have htop : ⊤ ≤ Z.fromSpecStalk (genericPoint Z) ⁻¹ᵁ U := fun y _ => by
    change Z.fromSpecStalk (genericPoint Z) y ∈ U
    rwa [fromSpecStalk_genericPoint_apply]
  have h₁ : (Spec.map φ ≫ Z.fromSpecStalk (genericPoint Z)).appLE U ⊤ e =
      (Z.fromSpecStalk (genericPoint Z)).appLE U ⊤ htop ≫ (Spec.map φ).appTop := by
    rw [Scheme.Hom.comp_appLE, Scheme.Hom.appLE, Category.assoc]
    congr 1
  rw [h₁, Category.assoc, Scheme.ΓSpecIso_naturality, Scheme.Hom.appLE,
    Scheme.fromSpecStalk_app hU]
  simp only [Category.assoc, ← Functor.map_comp_assoc, ← op_comp, homOfLE_comp, homOfLE_refl,
    op_id, CategoryTheory.Functor.map_id, Category.id_comp]
  exact congrArg (fun t => Z.presheaf.germ U (genericPoint Z) hU ≫ t)
    (Iso.inv_hom_id_assoc (Scheme.ΓSpecIso (Z.presheaf.stalk (genericPoint Z))) φ)

/-- `appLE` of two equal morphisms. -/
private theorem appLE_eq_of_eq {X Y : Scheme.{u}} {h₁ h₂ : X ⟶ Y} (h : h₁ = h₂) (U : Y.Opens)
    (V : X.Opens) (e₁ : V ≤ h₁ ⁻¹ᵁ U) (e₂ : V ≤ h₂ ⁻¹ᵁ U) :
    h₁.appLE U V e₁ = h₂.appLE U V e₂ := by
  subst h
  rfl

/-- If a morphism from the spectrum of a field lands in `U`, so does its map to the
normalization, into the preimage of `U`. -/
private theorem top_le_preimage_toNormalization {Z : Scheme.{u}} {L : Type u} [Field L]
    (j : Spec (.of L) ⟶ Z) [QuasiCompact j] [QuasiSeparated j] {U : Z.Opens}
    (hjtop : ⊤ ≤ j ⁻¹ᵁ U) : ⊤ ≤ j.toNormalization ⁻¹ᵁ (j.fromNormalization ⁻¹ᵁ U) :=
  fun y hy => by
    change j.fromNormalization (j.toNormalization y) ∈ U
    rw [← Scheme.Hom.comp_apply, j.toNormalization_fromNormalization]
    exact hjtop hy

/-- Evaluating a section of `Z` pulled back to the normalization at the point of `Spec L` is
evaluating it along `j`. -/
private theorem appLE_toNormalization_fromNormalization_app_apply {Z : Scheme.{u}} {L : Type u}
    [Field L] (j : Spec (.of L) ⟶ Z) [QuasiCompact j] [QuasiSeparated j] {U : Z.Opens}
    (hjtop : ⊤ ≤ j ⁻¹ᵁ U) (a : Γ(Z, U)) :
    (j.toNormalization.appLE _ ⊤ (top_le_preimage_toNormalization j hjtop) ≫
      (Scheme.ΓSpecIso (.of L)).hom).hom ((j.fromNormalization.app U).hom a) =
      (j.appLE U ⊤ hjtop ≫ (Scheme.ΓSpecIso (.of L)).hom).hom a := by
  have h : j.fromNormalization.app U ≫
      j.toNormalization.appLE _ ⊤ (top_le_preimage_toNormalization j hjtop) =
      j.appLE U ⊤ hjtop :=
    (Scheme.Hom.comp_appLE _ _ U ⊤ _).symm.trans
      (appLE_eq_of_eq j.toNormalization_fromNormalization _ _ _ _)
  rw [← h]
  rfl

/-- Over an affine open `U` of `Z` that `j : Spec L ⟶ Z` lands in, evaluating sections of the
normalization at the point of `Spec L` is injective with image the integral closure of `Γ(Z, U)`
in `L`; and the integral closure of `Γ(Z, U)` in `Γ(Spec L, j⁻¹ U)` is finite as soon as the one
in `L` is. -/
private theorem appLE_toNormalization_integralClosure {Z : Scheme.{u}}
    {L : Type u} [Field L] (j : Spec (.of L) ⟶ Z) [QuasiCompact j] [QuasiSeparated j] {U : Z.Opens}
    (hU : IsAffineOpen U) (hjtop : ⊤ ≤ j ⁻¹ᵁ U) (χ : Γ(Z, U) ⟶ .of L)
    (hχ : j.appLE U ⊤ hjtop ≫ (Scheme.ΓSpecIso (.of L)).hom = χ) :
    letI := χ.hom.toAlgebra
    Function.Injective (j.toNormalization.appLE _ ⊤ (top_le_preimage_toNormalization j hjtop) ≫
        (Scheme.ΓSpecIso (.of L)).hom).hom ∧
      (∀ ℓ : L, _root_.IsIntegral Γ(Z, U) ℓ → ∃ x, (j.toNormalization.appLE _ ⊤
        (top_le_preimage_toNormalization j hjtop) ≫ (Scheme.ΓSpecIso (.of L)).hom).hom x = ℓ) ∧
      (∀ x, _root_.IsIntegral Γ(Z, U) ((j.toNormalization.appLE _ ⊤
        (top_le_preimage_toNormalization j hjtop) ≫ (Scheme.ΓSpecIso (.of L)).hom).hom x)) ∧
      (Module.Finite Γ(Z, U) (integralClosure Γ(Z, U) L) →
        letI := (j.app U).hom.toAlgebra
        Module.Finite Γ(Z, U) (integralClosure Γ(Z, U) Γ(Spec (.of L), j ⁻¹ᵁ U))) := by
  subst hχ
  let algL : Algebra Γ(Z, U) L :=
    (j.appLE U ⊤ hjtop ≫ (Scheme.ΓSpecIso (.of L)).hom).hom.toAlgebra
  have hgtop := top_le_preimage_toNormalization j hjtop
  let algB : Algebra Γ(Z, U) Γ(Spec (.of L), j ⁻¹ᵁ U) := (j.app U).hom.toAlgebra
  let iso := j.normalizationObjIso hU
  have hjeq : j ⁻¹ᵁ U = ⊤ := le_antisymm le_top hjtop
  let eR : Γ(Spec (.of L), j ⁻¹ᵁ U) ≃+* L :=
    ((Spec (.of L)).presheaf.mapIso (eqToIso hjeq.symm).op ≪≫
      Scheme.ΓSpecIso (.of L)).commRingCatIsoToRingEquiv
  have heR : ∀ a, eR (algebraMap Γ(Z, U) _ a) = algebraMap Γ(Z, U) L a := fun a => by
    change ((Spec (.of L)).presheaf.map (eqToIso hjeq.symm).op.hom ≫
      (Scheme.ΓSpecIso (.of L)).hom).hom ((j.app U).hom a) = _
    rw [show (eqToIso hjeq.symm).op.hom = (homOfLE hjtop).op from Subsingleton.elim _ _]
    rfl
  have hψ : ∀ x, (j.toNormalization.appLE _ ⊤ hgtop ≫ (Scheme.ΓSpecIso (.of L)).hom).hom x =
      eR (iso.hom x).1 := fun x => by
    change ((j.toNormalization.app _ ≫ (Spec (.of L)).presheaf.map (homOfLE hgtop).op) ≫
      (Scheme.ΓSpecIso (.of L)).hom).hom x = _
    rw [j.toNormalization_app_preimage ⟨U, hU⟩]
    simp only [Category.assoc, ← Functor.map_comp]
    rfl
  let eA : Γ(Spec (.of L), j ⁻¹ᵁ U) ≃ₐ[Γ(Z, U)] L := { eR with commutes' := heR }
  refine ⟨fun x y hxy => ?_, fun ℓ hℓ => ?_, fun x => ?_, fun hfin => ?_⟩
  · rw [hψ, hψ] at hxy
    exact iso.commRingCatIsoToRingEquiv.injective (Subtype.ext (eR.injective hxy))
  · have hb : _root_.IsIntegral Γ(Z, U) (eR.symm ℓ) := by
      rw [← isIntegral_algHom_iff eA.toAlgHom eR.injective]
      change _root_.IsIntegral Γ(Z, U) (eR (eR.symm ℓ))
      rwa [RingEquiv.apply_symm_apply]
    refine ⟨iso.inv ⟨eR.symm ℓ, hb⟩, ?_⟩
    rw [hψ]
    change eR ((iso.inv ≫ iso.hom) ⟨eR.symm ℓ, hb⟩).1 = ℓ
    rw [Iso.inv_hom_id]
    exact RingEquiv.apply_symm_apply eR ℓ
  · rw [hψ]
    exact (iso.hom x).2.map eA.toAlgHom
  · exact Module.Finite.equiv (eA.mapIntegralClosure.symm.toLinearEquiv)

/-- The generic point of the normalization of a morphism from the spectrum of a field is the
image of the unique point. -/
private theorem genericPoint_normalization_eq_toNormalization {Z : Scheme.{u}} {L : Type u}
    [Field L] (j : Spec (.of L) ⟶ Z) [QuasiCompact j] [QuasiSeparated j] :
    genericPoint j.normalization = j.toNormalization (IsLocalRing.closedPoint L) := by
  have : Subsingleton ↥(Spec (CommRingCat.of L)) := inferInstanceAs (Subsingleton (PrimeSpectrum L))
  have hr : Set.range j.toNormalization = {j.toNormalization (IsLocalRing.closedPoint L)} := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      rw [Subsingleton.elim w (IsLocalRing.closedPoint L)]
      rfl
    · rintro rfl
      exact ⟨_, rfl⟩
  refine (genericPoint_spec _).eq (isGenericPoint_iff_specializes.2 fun y => ?_)
  refine iff_of_true (specializes_iff_mem_closure.mpr ?_) trivial
  rw [← hr, j.toNormalization.denseRange.closure_range]
  trivial

/-- Over an affine open `U` of an integral Nagata scheme containing the generic point, the integral
closure of `Γ(Z, U)` in a finite extension `L` of the function field is a finite `Γ(Z, U)`-module:
`Γ(Z, U)` is a Nagata domain with fraction field `Z.functionField`, hence N-2. -/
private theorem integralClosure_finite_of_isNagataScheme {Z : Scheme.{u}} [IsIntegral Z]
    (hZ : IsNagataScheme Z) (L : Type u) [Field L] [Algebra Z.functionField L]
    [FiniteDimensional Z.functionField L] {U : Z.Opens} (hU : IsAffineOpen U)
    (hηU : genericPoint Z ∈ U) :
    letI :=
      (Z.presheaf.germ U _ hηU ≫ CommRingCat.ofHom (algebraMap Z.functionField L)).hom.toAlgebra
    Module.Finite Γ(Z, U) (integralClosure Γ(Z, U) L) := by
  have : Nonempty U := ⟨⟨_, hηU⟩⟩
  letI :=
    (Z.presheaf.germ U _ hηU ≫ CommRingCat.ofHom (algebraMap Z.functionField L)).hom.toAlgebra
  have : IsScalarTower Γ(Z, U) Z.functionField L := .of_algebraMap_eq fun _ => rfl
  have : IsFractionRing Γ(Z, U) Z.functionField :=
    functionField_isFractionRing_of_isAffineOpen Z U hU
  have hJ : IsJapaneseRing Γ(Z, U) :=
    .of_ringEquiv (RingEquiv.quotientBot _)
      ((hZ.isNagataRing_sections ⟨U, hU⟩).isJapaneseRing_quotient ⊥)
  exact isN2_apply_of_isFractionRing Γ(Z, U) (fun L' _ _ _ _ _ => hJ.finite L') Z.functionField L

private theorem isFinite_fromNormalization_functionField {k : Type u} [Field k] {Y : Scheme.{u}}
    [IsIntegral Y] (sY : Y ⟶ Spec (.of k)) [IsVariety k sY] (L : Type u) [Field L]
    [Algebra Y.functionField L] [FiniteDimensional Y.functionField L] :
    letI : QuasiSeparated (Spec.map (CommRingCat.ofHom (algebraMap Y.functionField L)) ≫
      Y.fromSpecStalk (genericPoint Y)) := .of_comp _ sY
    IsFinite (Spec.map (CommRingCat.ofHom (algebraMap Y.functionField L)) ≫
      Y.fromSpecStalk (genericPoint Y)).fromNormalization := by
  set φ := CommRingCat.ofHom (algebraMap Y.functionField L)
  set j := Spec.map φ ≫ Y.fromSpecStalk (genericPoint Y)
  have : QuasiSeparated j := .of_comp j sY
  refine isFinite_fromNormalization_of_module_finite j fun U => ?_
  by_cases hηU : genericPoint Y ∈ U.1
  · have hjtop := top_le_preimage_fromSpecStalk_genericPoint Y φ hηU
    have : Nonempty U.1 := ⟨⟨_, hηU⟩⟩
    exact (appLE_toNormalization_integralClosure j U.2 hjtop _
      (appLE_fromSpecStalk_genericPoint_ΓSpecIso Y φ U.1 hjtop)).2.2.2
      (integralClosure_finite_of_isNagataScheme
        (isNagataScheme_of_locallyOfFiniteType_over_field k sY) L U.2 hηU)
  · obtain ⟨U, hUa⟩ := U
    have hU : U = ⊥ := by
      by_contra h
      exact hηU (((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr
        (by simpa [Set.nonempty_iff_ne_empty] using h))
    subst hU
    letI := (j.app ⊥).hom.toAlgebra
    have : Subsingleton (integralClosure Γ(Y, ⊥) Γ(Spec (.of L), j ⁻¹ᵁ ⊥)) :=
      Module.subsingleton Γ(Y, ⊥) _
    exact Module.Finite.of_finite

/-- A ring map from the function field of the normalization of `Y` in `L` to `L` that agrees
with the sections of `Spec L ⟶ j.normalization` on every open containing the generic point is
surjective. -/
private theorem surjective_of_germ_eq_appLE {Y : Scheme.{u}} [IsIntegral Y] (L : Type u)
    [Field L] [Algebra Y.functionField L] [FiniteDimensional Y.functionField L]
    {j : Spec (.of L) ⟶ Y} [QuasiCompact j] [QuasiSeparated j]
    (hj : j = Spec.map (CommRingCat.ofHom (algebraMap Y.functionField L)) ≫
      Y.fromSpecStalk (genericPoint Y))
    (Φ : j.normalization.functionField →+* L)
    (hle : ∀ V : j.normalization.Opens, genericPoint j.normalization ∈ V →
      ⊤ ≤ j.toNormalization ⁻¹ᵁ V)
    (hΦ : ∀ (V : j.normalization.Opens) (hV : genericPoint j.normalization ∈ V)
      (t : Γ(j.normalization, V)), Φ (j.normalization.presheaf.germ V _ hV t) =
        (j.toNormalization.appLE V ⊤ (hle V hV) ≫ (Scheme.ΓSpecIso (.of L)).hom).hom t) :
    Function.Surjective Φ := by
  subst hj
  set φ := CommRingCat.ofHom (algebraMap Y.functionField L)
  set j := Spec.map φ ≫ Y.fromSpecStalk (genericPoint Y)
  obtain ⟨_, ⟨U₀, hU₀, rfl⟩, hηU₀, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (genericPoint Y)) isOpen_univ
  intro ℓ
  have : Nonempty U₀ := ⟨⟨_, hηU₀⟩⟩
  have hjtop := top_le_preimage_fromSpecStalk_genericPoint Y φ hηU₀
  letI := (Y.germToFunctionField U₀ ≫ φ).hom.toAlgebra
  have : IsScalarTower Γ(Y, U₀) Y.functionField L :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsFractionRing Γ(Y, U₀) Y.functionField :=
    functionField_isFractionRing_of_isAffineOpen Y U₀ hU₀
  have : Algebra.IsAlgebraic Γ(Y, U₀) L :=
    (IsFractionRing.comap_isAlgebraic_iff (K := Y.functionField)).mpr inferInstance
  obtain ⟨-, hint, -, -⟩ := appLE_toNormalization_integralClosure j hU₀ hjtop _
    (appLE_fromSpecStalk_genericPoint_ΓSpecIso Y φ U₀ hjtop)
  obtain ⟨a, ha, hℓ⟩ :=
    (Algebra.IsAlgebraic.isAlgebraic (R := Γ(Y, U₀)) ℓ).exists_integral_multiple
  obtain ⟨c, hc⟩ := hint _ hℓ
  have hηX : genericPoint j.normalization ∈ j.fromNormalization ⁻¹ᵁ U₀ := by
    rw [genericPoint_normalization_eq_toNormalization j]
    exact top_le_preimage_toNormalization j hjtop trivial
  have ha' : (j.toNormalization.appLE _ ⊤ (top_le_preimage_toNormalization j hjtop) ≫
      (Scheme.ΓSpecIso (.of L)).hom).hom ((j.fromNormalization.app U₀).hom a) =
        algebraMap Γ(Y, U₀) L a := by
    rw [appLE_toNormalization_fromNormalization_app_apply j hjtop a,
      appLE_fromSpecStalk_genericPoint_ΓSpecIso Y φ U₀ hjtop]
    rfl
  have hane : algebraMap Γ(Y, U₀) L a ≠ 0 := by
    intro h
    apply ha
    apply germ_injective_of_isIntegral (X := Y) _ hηU₀
    apply (algebraMap Y.functionField L).injective
    rw [map_zero, map_zero]
    exact h
  refine ⟨j.normalization.presheaf.germ _ _ hηX c /
    j.normalization.presheaf.germ _ _ hηX ((j.fromNormalization.app U₀).hom a), ?_⟩
  rw [map_div₀, hΦ, hΦ, ha', hc, Algebra.smul_def, mul_div_cancel_left₀ _ hane]

/-- Let `Y` be a variety over `k` and `L` a finite field extension of its function field `k(Y)`.
Then there is a normalization of `Y` in `L`: an integral `k`-scheme `X`, a morphism `g : X ⟶ Y`
and an isomorphism `ι : k(X) ≃+* L` with
`MMP.Resolution.IsNormalizationInExtension sX sY L g ι`. -/
@[mmp "lem_kr2b_normalization_in_extension_exists"]
public theorem exists_isNormalizationInExtension {k : Type u} [Field k] {Y : Scheme.{u}}
    [IsIntegral Y] (sY : Y ⟶ Spec (.of k)) [IsVariety k sY] (L : Type u) [Field L]
    [Algebra Y.functionField L] [FiniteDimensional Y.functionField L] :
    ∃ (X : Scheme.{u}) (_ : IsIntegral X) (sX : X ⟶ Spec (.of k)) (g : X ⟶ Y)
      (ι : X.functionField ≃+* L), IsNormalizationInExtension sX sY L g ι := by
  set φ := CommRingCat.ofHom (algebraMap Y.functionField L)
  set j := Spec.map φ ≫ Y.fromSpecStalk (genericPoint Y)
  have : QuasiSeparated j := .of_comp j sY
  let X := j.normalization
  let g : X ⟶ Y := j.fromNormalization
  let pt : Spec (.of L) := IsLocalRing.closedPoint L
  have hgen : genericPoint X = j.toNormalization pt :=
    genericPoint_normalization_eq_toNormalization j
  have hsp : j.toNormalization pt ⤳ genericPoint X := hgen ▸ specializes_refl _
  let Φ : X.functionField →+* L := (X.presheaf.stalkSpecializes hsp ≫
    j.toNormalization.stalkMap pt ≫ (stalkClosedPointIso (.of L)).hom).hom
  have hle : ∀ (V : X.Opens) (hV : genericPoint X ∈ V), ⊤ ≤ j.toNormalization ⁻¹ᵁ V := by
    intro V hV y _
    have : Subsingleton ↥(Spec (CommRingCat.of L)) :=
      inferInstanceAs (Subsingleton (PrimeSpectrum L))
    rw [Subsingleton.elim y pt]
    change j.toNormalization pt ∈ V
    rwa [← hgen]
  have hΦ : ∀ (V : X.Opens) (hV : genericPoint X ∈ V) (t : Γ(X, V)),
      Φ (X.presheaf.germ V _ hV t) =
        (j.toNormalization.appLE V ⊤ (hle V hV) ≫ (Scheme.ΓSpecIso (.of L)).hom).hom t := by
    intro V hV t
    change (stalkClosedPointIso (.of L)).hom.hom (j.toNormalization.stalkMap pt
      (X.presheaf.stalkSpecializes hsp (X.presheaf.germ V _ hV t))) = _
    rw [TopCat.Presheaf.germ_stalkSpecializes_apply, Scheme.Hom.germ_stalkMap_apply,
      ← TopCat.Presheaf.germ_res_apply _ (homOfLE (hle V hV)) pt trivial,
      ← germ_stalkClosedPointIso_hom]
    rfl
  have hfin : IsFinite g := isFinite_fromNormalization_functionField sY L
  have hsurj : Function.Surjective Φ := surjective_of_germ_eq_appLE L rfl Φ hle hΦ
  let ι : X.functionField ≃+* L := RingEquiv.ofBijective Φ ⟨Φ.injective, hsurj⟩
  have hιΦ : ∀ x, ι x = Φ x := fun _ => rfl
  refine ⟨X, inferInstance, g ≫ sY, g, ι, ?_, inferInstance, rfl, ?_, inferInstance, ?_, ?_⟩
  · constructor <;> infer_instance
  · have hmem : genericPoint Y ∈ Set.range g := ⟨j.toNormalization pt, by
      rw [← Scheme.Hom.comp_apply, j.toNormalization_fromNormalization]
      exact fromSpecStalk_genericPoint_apply Y _⟩
    exact ⟨dense_iff_closure_eq.mpr (Set.eq_univ_of_univ_subset
      (genericPoint_closure Y ▸ closure_mono (Set.singleton_subset_iff.mpr hmem)))⟩
  · intro Y₀ hY₀ hX s
    have hjtop := top_le_preimage_fromSpecStalk_genericPoint Y φ hY₀
    have : Nonempty Y₀ := ⟨⟨_, hY₀⟩⟩
    rw [hιΦ, hΦ]
    exact (appLE_toNormalization_fromNormalization_app_apply j hjtop s).trans
      (congrArg (fun t => t.hom s) (appLE_fromSpecStalk_genericPoint_ΓSpecIso Y φ Y₀ hjtop))
  · intro Y₀ hY₀a hY₀ hX
    have hjtop := top_le_preimage_fromSpecStalk_genericPoint Y φ hY₀
    have : Nonempty Y₀ := ⟨⟨_, hY₀⟩⟩
    obtain ⟨-, hint, hintegral, -⟩ := appLE_toNormalization_integralClosure j hY₀a hjtop _
      (appLE_fromSpecStalk_genericPoint_ΓSpecIso Y φ Y₀ hjtop)
    ext ℓ
    simp only [Set.mem_range, hιΦ, hΦ]
    exact ⟨fun ⟨x, hx⟩ => hx ▸ hintegral x, fun h => hint ℓ h⟩

/-! ### Fields of representatives and completed local rings in characteristic zero -/

/-- **A coefficient field exists in characteristic zero.** Let `k` be a field of characteristic
zero, `X` a scheme locally of finite type over `k` and `p ∈ X` a closed point. Then the completed
local ring `𝒪̂_{p,X}` has a field of representatives containing the image of `k`. -/
@[mmp "lem_kr3c_field_of_representatives_exists_char_zero"]
public theorem exists_isFieldOfRepresentatives_completion {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] [IsLocallyNoetherian X]
    (p : X) (hp : IsClosed ({p} : Set X)) :
    letI := MMP.Mori.stalkAlgebra sX p
    ∃ K : Subring (AdicCompletion (maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p)),
      Set.range (algebraMap k
        (AdicCompletion (maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p))) ⊆ K ∧
      IsFieldOfRepresentatives K :=
  (MMP.Flips.ResolutionInputs.existsUnique_isFieldOfRepresentatives_completion sX p hp).exists

/-- A ring isomorphism of coefficients induces one of multivariate power series rings. -/
private noncomputable def mvPowerSeriesCongr {σ R S : Type*} [Semiring R] [Semiring S]
    (e : R ≃+* S) :
    MvPowerSeries σ R ≃+* MvPowerSeries σ S where
  __ := MvPowerSeries.map (σ := σ) e.toRingHom
  invFun := MvPowerSeries.map e.symm.toRingHom
  left_inv f := by ext; simp
  right_inv f := by ext; simp

private lemma mvPowerSeriesCongr_apply {σ R S : Type*} [Semiring R] [Semiring S] (e : R ≃+* S)
    (f : MvPowerSeries σ R) : mvPowerSeriesCongr e f = MvPowerSeries.map e.toRingHom f := rfl

/-- **The residue field of a Noetherian local ring is identified with any field of
representatives `K` of its completion `Â`**, through `κ(R) ≃ κ(Â) ≃ K`; an element of `R` whose
image in `Â` lies in `K` is sent by this identification to that image. -/
private lemma exists_residueField_equiv_fieldOfRepresentatives {R : Type*} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] {K : Subring (AdicCompletion (maximalIdeal R) R)}
    (hK : MMP.Resolution.IsFieldOfRepresentatives K) :
    ∃ φ : ResidueField R ≃+* K, ∀ (r : R) (hr : algebraMap R _ r ∈ K),
      φ (residue R r) = ⟨algebraMap R _ r, hr⟩ := by
  let σ := RingEquiv.ofBijective ((residue _).comp K.subtype) hK.2
  let τ := RingEquiv.ofBijective _ (AdicCompletion.residueField_map_bijective R)
  refine ⟨τ.trans σ.symm, fun r hr => σ.injective ?_⟩
  simp only [RingEquiv.coe_trans, Function.comp_apply, RingEquiv.apply_symm_apply]
  exact ResidueField.map_residue _ r

/-- **The completed local ring of a smooth scheme is a power series ring.** Let `k` be a field of
characteristic zero, `X` a smooth scheme over `k`, `p ∈ X` a closed point and `x₁, …, xₙ` a regular
system of parameters of `𝒪_{p,X}`. Then there is an isomorphism of `k`-algebras
`κ(p)[[t₁, …, tₙ]] ≃ 𝒪̂_{p,X}` sending each `tᵢ` to the image of `xᵢ` in the completion. -/
@[mmp "lem_kr3c_completion_power_series_char_zero"]
public theorem exists_mvPowerSeries_algEquiv_completion {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (hX : MMP.Mori.IsSmoothScheme sX)
    (p : X) (hp : IsClosed ({p} : Set X)) {n : ℕ} {x : Fin n → X.presheaf.stalk p}
    (hx : MMP.Mori.IsRegularSystemOfParameters x) :
    letI := MMP.Mori.stalkAlgebra sX p
    ∃ F : MvPowerSeries (Fin n) (ResidueField (X.presheaf.stalk p)) ≃ₐ[k]
        AdicCompletion (maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p),
      ∀ i, F (MvPowerSeries.X i) =
        algebraMap (X.presheaf.stalk p)
          (AdicCompletion (maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p)) (x i) := by
  have := hX.smooth
  have := LocallyOfFiniteType.isLocallyNoetherian sX
  letI := MMP.Mori.stalkAlgebra sX p
  obtain ⟨K, hk, hK⟩ := MMP.Resolution.exists_isFieldOfRepresentatives_completion sX p hp
  obtain ⟨F, ⟨hFX, hFb⟩, -⟩ :=
    MMP.Flips.ResolutionInputs.existsUnique_algHom_X_eq_bijective_stalk p hx K hK
  obtain ⟨φ, hφ⟩ := exists_residueField_equiv_fieldOfRepresentatives hK
  refine ⟨.ofRingEquiv (f := (mvPowerSeriesCongr φ).trans (.ofBijective F hFb)) fun c => ?_,
    fun i => ?_⟩
  · have hc := hφ (algebraMap k _ c) <| by
      rw [← IsScalarTower.algebraMap_apply]; exact hk ⟨c, rfl⟩
    simp only [RingEquiv.coe_trans, Function.comp_apply, mvPowerSeriesCongr_apply,
      MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      MvPowerSeries.map_C, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      RingEquiv.ofBijective_apply]
    rw [IsScalarTower.algebraMap_apply k (X.presheaf.stalk p) (ResidueField _),
      ResidueField.algebraMap_eq, hc, MMP.Flips.ResolutionInputs.mvPowerSeries_C_eq_algebraMap,
      AlgHom.commutes]
    rfl
  · simp [mvPowerSeriesCongr_apply, hFX]

/-! ### A smooth blow-up centre that breaks simple normal crossings -/

section

open Polynomial

variable (k : Type u) [Field k]

/-- The germ of a polynomial on `𝔸¹_k` is its image in the localization at the point. -/
private theorem germ_ΓSpecIso_inv_eq (x : Spec (.of k[X])) (f : k[X]) :
    (Spec (.of k[X])).presheaf.germ ⊤ x trivial ((Scheme.ΓSpecIso (.of k[X])).inv.hom f) =
        (Spec.stalkIso (.of k[X]) x).commRingCatIsoToRingEquiv.symm
          (algebraMap k[X] (Localization.AtPrime (show PrimeSpectrum k[X] from x).asIdeal)
            f) :=
  (ConcreteCategory.congr_hom (Spec.algebraMap_stalkIso_inv (R := CommRingCat.of k[X]) x) f).symm

/-- The stalk of the ideal of the origin is generated by the germ of `X`. -/
private theorem stalk_affineLineOriginIdeal (x : Spec (.of k[X])) :
    IdealSheafData.stalk (affineLineOriginIdeal k) x =
      Ideal.span {((Spec (.of k[X])).presheaf.germ ⊤ x trivial
        ((Scheme.ΓSpecIso (.of k[X])).inv.hom Polynomial.X))} := by
  rw [IdealSheafData.stalk_eq_map_germ _ x ⟨⊤, isAffineOpen_top _⟩ trivial, affineLineOriginIdeal,
    Stacks.Divisors.ideal_ofIdealTop_top (isAffineOpen_top _), Ideal.map_span, Set.image_singleton]

/-- The stalks of the ideal of the origin are nonzero. -/
private theorem stalk_ne_bot (x : Spec (.of k[X])) :
    IdealSheafData.stalk (affineLineOriginIdeal k) x ≠ ⊥ := by
  have : x.asIdeal.IsPrime := x.isPrime
  rw [stalk_affineLineOriginIdeal, Ne, Ideal.span_singleton_eq_bot, germ_ΓSpecIso_inv_eq,
    map_eq_zero_iff _ (RingEquiv.injective _)]
  intro h
  have hinj := IsLocalization.injective (Localization.AtPrime x.asIdeal)
    x.asIdeal.primeCompl_le_nonZeroDivisors
  exact Polynomial.X_ne_zero (hinj (h.trans (map_zero _).symm))

/-- The local rings of `𝔸¹_k` have dimension at most one. -/
private theorem ringKrullDim_stalk_le (x : Spec (.of k[X])) :
    ringKrullDim ((Spec (.of k[X])).presheaf.stalk x) ≤ 1 := by
  have : x.asIdeal.IsPrime := x.isPrime
  let e := (Spec.stalkIso (.of k[X]) x).commRingCatIsoToRingEquiv
  rw [ringKrullDim_eq_of_ringEquiv e,
    IsLocalization.AtPrime.ringKrullDim_eq_height x.asIdeal (Localization.AtPrime x.asIdeal)]
  exact (Ideal.height_le_ringKrullDim_of_ne_top x.isPrime.ne_top).trans
    (IsPrincipalIdealRing.ringKrullDim_eq_one _ (Polynomial.not_isField k)).le

/-- The origin `(x)` of `𝔸¹_k`. -/
private noncomputable def origin : Spec (.of k[X]) :=
  (⟨Ideal.span {Polynomial.X},
    (PrincipalIdealRing.isMaximal_of_irreducible Polynomial.irreducible_X).isPrime⟩ :
      PrimeSpectrum k[X])

/-- The origin lies on `D`. -/
private theorem origin_mem_support : origin k ∈ (affineLineOriginIdeal k).support := by
  have : (show PrimeSpectrum k[X] from origin k).asIdeal.IsPrime :=
    (show PrimeSpectrum k[X] from origin k).isPrime
  by_contra h
  have := (IdealSheafData.stalk_eq_top_iff_notMem_support _ _).mpr h
  rw [stalk_affineLineOriginIdeal, Ideal.span_singleton_eq_top, germ_ΓSpecIso_inv_eq,
    MulEquiv.isUnit_map] at this
  exact ((IsLocalization.AtPrime.isUnit_to_map_iff _
    (show PrimeSpectrum k[X] from origin k).asIdeal _).mp this) (Ideal.subset_span rfl)

/-- The one-member family `(D)` is a simple normal crossing family. -/
private theorem isSNCFamily_fin_one :
    IsSNCFamily (Spec.map (CommRingCat.ofHom (C : k →+* k[X])))
      (fun _ : Fin 1 => affineLineOriginIdeal k) := by
  obtain ⟨h1, h2⟩ := isSNCFamily_affineLine_origin k
  refine ⟨fun _ => h1 (), fun x => ?_⟩
  obtain ⟨n, z, c, hz, hc, -⟩ := h2 x
  exact ⟨n, z, fun i => c ⟨(), i.2⟩, hz, fun i => hc ⟨(), i.2⟩,
    fun a b _ => Subtype.ext (Subsingleton.elim _ _)⟩

/-- The origin is an effective Cartier divisor on `𝔸¹_k`. -/
private theorem isEffectiveCartierDivisor_origin :
    Stacks.Divisors.IsEffectiveCartierDivisor (affineLineOriginIdeal k) := by
  refine Stacks.Divisors.isEffectiveCartierDivisor_of_forall_exists_affineOpen _ fun x =>
    ⟨⊤, isAffineOpen_top _, trivial, (Scheme.ΓSpecIso (.of k[X])).inv.hom Polynomial.X, ?_,
      Stacks.Divisors.ideal_ofIdealTop_top (isAffineOpen_top _) _⟩
  refine IsRegular.of_ne_zero (R := Γ(Spec (.of k[X]), ⊤)) ?_
  intro h
  exact Polynomial.X_ne_zero (R := k)
    (by simpa using congrArg (Scheme.ΓSpecIso (.of k[X])).hom.hom h)

/-- The irreducible components of the support of `D` have codimension one. -/
private theorem codim_components (W : Set (Spec (.of k[X])))
    (hW : W ∈ componentsOf ((affineLineOriginIdeal k).support : Set (Spec (.of k[X])))) :
    codimension (irreducibleClosure hW.1.1) = 1 := by
  have hcl : IsClosed W :=
    isClosed_of_mem_componentsOf (affineLineOriginIdeal k).support.isClosed hW
  obtain ⟨h, -⟩ := isSNCFamily_affineLine_origin k
  refine (h ()).2.1 _
    ⟨by simpa [irreducibleClosure, hcl.closure_eq] using hW.1.2, fun W' hW' hle => ?_⟩
  have := hW.2 ⟨W'.isIrreducible, hW'⟩ (subset_closure.trans hle)
  change (W' : Set _) ⊆ closure W
  rw [hcl.closure_eq]
  exact this

/-- `𝔸¹_k` is smooth over `k`. -/
private theorem smooth_line :
    Smooth (Spec.map (CommRingCat.ofHom (C : k →+* k[X]))) := by
  rw [HasRingHomProperty.Spec_iff (P := @Smooth), ← Polynomial.algebraMap_eq]
  have : Algebra.FinitePresentation k k[X] := inferInstance
  exact RingHom.smooth_algebraMap.mpr ⟨Algebra.FormallySmooth.polynomial k, this⟩

/-- `𝔸¹_k` is locally of finite type over `k`. -/
private theorem locallyOfFiniteType_line :
    LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (C : k →+* k[X]))) := by
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), ← Polynomial.algebraMap_eq]
  exact RingHom.finiteType_algebraMap.mpr inferInstance

/-- `D` has order at least one along its support. -/
private theorem orderAlongGE_origin :
    OrderAlongGE (affineLineOriginIdeal k)
      ((affineLineOriginIdeal k).support : Set (Spec (.of k[X]))) 1 := by
  intro W hW
  have hcl : IsClosed W :=
    isClosed_of_mem_componentsOf (affineLineOriginIdeal k).support.isClosed hW
  have hξ : hW.1.1.genericPoint ∈ (affineLineOriginIdeal k).support := by
    have := hW.1.1.isGenericPoint_genericPoint_closure.mem
    rw [hcl.closure_eq] at this
    exact hW.1.2 this
  have hle : IdealSheafData.stalk (affineLineOriginIdeal k) hW.1.1.genericPoint ≤
      IsLocalRing.maximalIdeal _ := IsLocalRing.le_maximalIdeal
    ((IdealSheafData.stalk_eq_top_iff_notMem_support _ _).not.mpr (not_not.mpr hξ))
  exact le_iSup₂_of_le (f := fun (j : ℕ) (_ : IdealSheafData.stalk (affineLineOriginIdeal k)
    hW.1.1.genericPoint ≤ IsLocalRing.maximalIdeal _ ^ j) => (j : ℕ∞)) 1 (by rwa [pow_one])
    (by simp)

/-- A family of divisors in which two distinct members pass through a point whose local ring
has dimension at most one is not a simple normal crossing family: the regular system of
parameters at that point has at most one element, so it cannot carry two distinct members. -/
private theorem not_isSNCFamily_of_ringKrullDim_stalk_le_one {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) {Λ : Type*} {E : Λ → X.IdealSheafData} {x : X} {i j : Λ}
    (hij : i ≠ j) (hi : x ∈ (E i).support) (hj : x ∈ (E j).support)
    (hx : ringKrullDim (X.presheaf.stalk x) ≤ 1) : ¬ IsSNCFamily sX E := by
  rintro ⟨-, h⟩
  obtain ⟨n, z, c, hz, -, hinj⟩ := h x
  rw [hz.2] at hx
  have hne : (c ⟨i, hi⟩ : ℕ) ≠ c ⟨j, hj⟩ :=
    Fin.val_ne_of_ne fun h => hij (congrArg Subtype.val (hinj h))
  have : n ≤ 1 := by exact_mod_cast hx
  have := (c ⟨i, hi⟩).isLt
  have := (c ⟨j, hj⟩).isLt
  omega

end

open Polynomial in
/-- On `𝔸¹_k`, with `D` the ideal sheaf of `(x)`, the centre `D` defines a smooth blow-up of the
marked triple `(𝔸¹_k, D, 1, (D))`, yet appending it to `E = (D)` gives `(D, D)`, which is not an
ordered simple normal crossing divisor. -/
@[mmp "lem_kr3c_ex_trivial_blowup_breaks_snc"]
public theorem not_isOrderedSNC_snoc_of_isSmoothBlowupOfMarkedTriple_line
    (k : Type u) [Field k] [CharZero k] :
    let X := Spec (.of (Polynomial k))
    let sX : X ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k)))
    let D : X.IdealSheafData := Scheme.IdealSheafData.ofIdealTop
      ((Ideal.span {Polynomial.X}).map (Scheme.ΓSpecIso (.of (Polynomial k))).inv.hom)
    let t : MarkedTriple.{u} := { X := X, I := D, E := ⟨1, ![D]⟩, k := k, sX := sX, m := 1 }
    t ∈ markedTriples ∧ IsSmoothBlowupOfMarkedTriple t D ∧
      ¬ (⟨2, Fin.snoc t.E.E D⟩ : OrderedDivisor X).IsOrderedSNC sX := by
  intro X sX D t
  have hD : D = affineLineOriginIdeal k := by
    simp only [D, affineLineOriginIdeal, Ideal.map_span, Set.image_singleton]
    rfl
  have hs : sX = Spec.map (CommRingCat.ofHom (C : k →+* k[X])) := by
    simp only [sX, Polynomial.algebraMap_eq]
  have h1 : (![D] : Fin 1 → X.IdealSheafData) = fun _ => D := by
    funext i; fin_cases i; rfl
  have h2 : (Fin.snoc ![D] D : Fin 2 → X.IdealSheafData) = fun _ => D := by
    funext i; fin_cases i <;> rfl
  change IsTriple sX D ⟨1, ![D]⟩ ∧ (HasComponentsOfPositiveCodim (D.support : Set X) ∧
      HasSNCWith ![D] D ∧ OrderAlongGE D (D.support : Set X) ((1 : ℕ) : ℕ∞)) ∧
    ¬ (⟨2, Fin.snoc ![D] D⟩ : OrderedDivisor X).IsOrderedSNC sX
  rw [h2, h1]
  clear_value sX D
  subst hD hs
  have hsnc := isSNCFamily_fin_one k
  have := smooth_line k
  refine ⟨⟨‹_›, (MMP.Mori.isSmoothScheme_iff _).2 (smooth_line k), locallyOfFiniteType_line k,
    inferInstance, TopologicalSpace.Equidimensional.of_preirreducibleSpace _,
    fun x _ => stalk_ne_bot k x,
    ⟨fun _ => ⟨(hsnc.1 0).1, isEffectiveCartierDivisor_origin k⟩, hsnc⟩⟩,
    ⟨fun W hW => (codim_components k W hW).ge, fun x hx => ?_,
      by simpa using orderAlongGE_origin k⟩,
    ?_⟩
  · obtain ⟨n, z, c, hz, hc, hinj⟩ := hsnc.2 x
    refine ⟨n, z, c, {c ⟨0, hx⟩}, hz, hc, hinj, ?_⟩
    rw [Finset.coe_singleton, Set.image_singleton]
    exact hc ⟨0, hx⟩
  · exact fun h => not_isSNCFamily_of_ringKrullDim_stalk_le_one k _ (i := (0 : Fin 2)) (j := 1)
      (by decide) (origin_mem_support k) (origin_mem_support k)
      (ringKrullDim_stalk_le k (origin k)) h.2

/-! ### The order of a power of an ideal sheaf -/

/-- In a regular local ring, if `g ∈ 𝔪ᵈ ∖ 𝔪ᵈ⁺¹` then `g ^ c ∉ 𝔪^{cd+1}`: initial forms multiply
in the associated graded ring, which is a domain. -/
private theorem pow_notMem_maximalIdeal_pow {S : Type*} [CommRing S] [IsRegularLocalRing S]
    {d : ℕ} {g : S} (h1 : g ∈ maximalIdeal S ^ d) (h2 : g ∉ maximalIdeal S ^ (d + 1)) :
    ∀ c : ℕ, g ^ c ∉ maximalIdeal S ^ (c * d + 1)
  | 0 => by simpa using (maximalIdeal.isMaximal S).ne_top
  | c + 1 => by
    rw [pow_succ g, add_one_mul]
    exact MMP.Flips.mul_notMem_maximalIdeal_pow_add_succ
      (by rw [mul_comm, pow_mul]; exact Ideal.pow_mem_pow h1 _)
      (pow_notMem_maximalIdeal_pow h1 h2 c) h1 h2

/-- If `I ⊆ 𝔪ⁿ` and `I ⊄ 𝔪ⁿ⁺¹` then `ord I = n`. -/
private theorem idealOrder_eq_of {R : Type*} [CommRing R] [IsLocalRing R] {I : Ideal R} {n : ℕ}
    (h1 : I ≤ maximalIdeal R ^ n) (h2 : ¬ I ≤ maximalIdeal R ^ (n + 1)) :
    idealOrder I = n := by
  refine le_antisymm (not_lt.mp fun h => h2 ?_) ((natCast_le_idealOrder_iff' I n).2 h1)
  exact (natCast_le_idealOrder_iff' I (n + 1)).1 (by exact_mod_cast Order.add_one_le_of_lt h)

/-- In a regular local ring, `ord (J ^ c) = c * ord J`. -/
private theorem idealOrder_pow {S : Type*} [CommRing S] [IsRegularLocalRing S] (J : Ideal S)
    (c : ℕ) : idealOrder (J ^ c) = c * idealOrder J := by
  rcases eq_or_ne (idealOrder J) ⊤ with hJ | hJ
  · rcases eq_or_ne c 0 with rfl | hc
    · simpa using idealOrder_eq_of (I := (⊤ : Ideal S)) (n := 0) (by simp)
        (by simpa using (maximalIdeal.isMaximal S).ne_top)
    rw [hJ, ENat.mul_top (by exact_mod_cast hc), ENat.eq_top_iff_forall_ge]
    exact fun n => (natCast_le_idealOrder_iff' _ n).2 <|
      (Ideal.pow_le_self hc).trans ((natCast_le_idealOrder_iff' J n).1 (hJ ▸ le_top))
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp hJ
  have h1 : J ≤ maximalIdeal S ^ d := (natCast_le_idealOrder_iff' J d).1 hd.le
  obtain ⟨g, hgJ, hg⟩ := Set.not_subset.mp fun h : J ≤ maximalIdeal S ^ (d + 1) => by
    have := (natCast_le_idealOrder_iff' J (d + 1)).2 h
    rw [← hd] at this
    norm_cast at this
    omega
  rw [← hd, idealOrder_eq_of (n := c * d)
    (by rw [mul_comm, pow_mul]; exact Ideal.pow_right_mono h1 _)
    fun h => pow_notMem_maximalIdeal_pow (h1 hgJ) hg c (h (Ideal.pow_mem_pow hgJ _))]
  push_cast; rfl

/-- **Order of a power.** At a point `x` of a scheme `X` with regular local ring `𝒪_{X,x}`
(e.g. `X` smooth over a field), the order of `I ^ c` is `c` times the order of `I`, for every
ideal sheaf `I` and `c : ℕ`. -/
@[mmp "lem_kr3c_order_power"]
public theorem multAt_pow {X : Scheme.{u}} (x : X) [IsRegularLocalRing (X.presheaf.stalk x)]
    (I : X.IdealSheafData) (c : ℕ) :
    multAt (I ^ c) x = c * multAt I x := by
  rw [multAt, multAt, MMP.Resolution.Aux.stalk_pow]
  exact idealOrder_pow _ c

end MMP.Resolution
