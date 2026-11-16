module

public import MMP.AlgebraicGeometry.Vanishing.RelativeKawamataViehweg
public import MMP.AlgebraicGeometry.Divisor.SmoothDivisorRestriction
public import MMP.AlgebraicGeometry.Divisor.SmoothDivisorAdjunction
public import MMP.AlgebraicGeometry.Resolution.BlowupChartClosedImmersion

/-!
# Relative vanishing for a birational morphism that is an isomorphism over the floor strata

Let `f : V ⟶ W` be a projective birational morphism of projective varieties over an
algebraically closed field `k` of characteristic zero, with `V` smooth, let `K_V` be a canonical
divisor of `V`, and let `B` be a `ℚ`-divisor with simple normal crossing support and coefficients
in `[0, 1]`. Assume that every stratum of the reduced divisor `⌊B⌋` (an irreducible component of
an intersection of its components) meets the complement of the exceptional set of `f`, that is,
`f` is an isomorphism at its generic point. If `M` is a Cartier divisor on `V` with
`M - (K_V + B)` nef, then `R^i f_* 𝒪_V(M) = 0` for every `i > 0`.

The proof inducts on the dimension and on the number of components of `⌊B⌋`: with `⌊B⌋ = 0`
this is relative Kawamata–Viehweg vanishing
(`MMP.Mori.isZero_rightDerived_pushforward_exteriorPower_tensor_divisorialSheaf`), and a
component `T` of `⌊B⌋` is removed with the sequence `0 → 𝒪_V(M - T) → 𝒪_V(M) → 𝒪_T(M) → 0`.

## Main results

* `MMP.Mori.isZero_rightDerived_pushforward_divisorialSheaf_of_isNef_sub_canonical_add`: the
  vanishing above.

## Implementation notes

* `V` and `W` carry structure morphisms `sV`, `sW` to `Spec k`, and `f ≫ sW = sV` says that `f`
  is a morphism over `k`. The source works over `ℂ`; only algebraic closedness and
  characteristic zero are used, through Kawamata–Viehweg vanishing.
* "`f` is an isomorphism at the generic point of `S`" is `¬ S ⊆ Ex(f)` for the exceptional set
  `MMP.Mori.exceptionalSet` of Kollár–Mori: `Ex(f)` is closed and `S` is irreducible and closed,
  so this says that the generic point of `S` lies outside `Ex(f)`.
* The strata of `⌊B⌋` are `MMP.Fourfold.IsSNCStratum` of `MMP.Mori.DivisorWithCoeffs.roundDown`;
  the empty intersection gives `V` itself, on which the condition is birationality.
* `R^i f_*` is the `i`-th right derived functor of `Scheme.Modules.pushforward f`, and
  `𝒪_V(M)` is `MMP.Mori.Divisor.divisorialSheaf`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori]
* [O. Fujino, *Fundamental theorems for the log minimal model program*][Fujino2011]
-/

@[expose] public section

section

/-!
## Proof: Relative vanishing over the floor strata (Reid–Fukuda)

Let `f : V ⟶ W` be a projective birational morphism of projective varieties over an
algebraically closed field `k` of characteristic zero, with `V` smooth, `K` a canonical divisor
of `V` and `B` a `ℚ`-divisor with snc support and coefficients in `[0, 1]` such that `f` is an
isomorphism at the generic point of every stratum of `⌊B⌋`. If `M` is a Cartier divisor with
`M - (K + B)` nef, then `R^i f_* 𝒪_V(M) = 0` for `i > 0`.

The proof inducts on the dimension and, in a fixed dimension, on the number of components of
`⌊B⌋`. Without floor this is relative Kawamata–Viehweg vanishing. A component `T` of `⌊B⌋` is
removed with the restriction sequence `0 → 𝒪_V(M - T) → 𝒪_V(M) → 𝒪_T(M) → 0`: the first term
has boundary `B - T` and the same nef difference, and `𝒪_T(M)` is handled on the smooth divisor
`T`, mapped birationally onto its image in `W`, by adjunction and the induction on the dimension;
the direct image along the closed immersion `T ⟶ V` and along the image `f(T) ⟶ W` does not
change higher direct images.

## Implementation notes

Inside the induction the condition on the strata of `⌊B⌋` is replaced by its consequence that
at a point `y` of the exceptional set of `f`, fewer components of `⌊B⌋` pass through `y` than
the dimension of `𝒪_{V,y}`: at a point where as many components pass as the dimension, the
closure of the point is a stratum. This form passes to `B - T` and to the restriction of `B - T`
to `T` by counting.

The map from `T` is taken onto the scheme-theoretic image `f(T) ⊆ W`, a closed projective
subvariety, rather than onto the normalization of `f(T)`: the vanishing in lower dimension does
not ask the target to be normal, and `f(T) ⟶ W` is a closed immersion, so higher direct images
along `T ⟶ f(T) ⟶ W` are those along `T ⟶ f(T)`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori]
* [O. Fujino, *Fundamental theorems for the log minimal model program*][Fujino2011]
-/

namespace MMP.FourfoldProofs.MmpLcBpfReidFukudaProof

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MMP.Mori

open scoped Classical

universe u

/-! ### Higher direct images -/

/-- In a short exact sequence, vanishing of `R^i f_*` at the outer terms gives vanishing at the
middle term. -/
private theorem isZero_rightDerived_obj_X₂ {X Y : Scheme.{u}} (f : X ⟶ Y)
    {S : ShortComplex X.Modules} (hS : S.ShortExact) (i : ℕ)
    (h₁ : IsZero (((Scheme.Modules.pushforward f).rightDerived i).obj S.X₁))
    (h₃ : IsZero (((Scheme.Modules.pushforward f).rightDerived i).obj S.X₃)) :
    IsZero (((Scheme.Modules.pushforward f).rightDerived i).obj S.X₂) := by
  letI := HasDerivedCategory.standard X.Modules
  letI := HasDerivedCategory.standard Y.Modules
  exact ((Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
    (Scheme.Modules.pushforward f)).exact_map hS i).isZero_X₂ (h₁.eq_of_src _ _)
    (h₃.eq_of_tgt _ _)

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
  Stacks.AlgebraicGeometry.AffinePushforwardTExactness in
/-- **Vanishing of a higher direct image ascends along an affine second leg.** For `g`
quasi-compact and quasi-separated, `c` affine and `M` quasi-coherent, `R^n g_* M = 0` implies
`R^n (g ≫ c)_* M = 0`, since `R^n (g ≫ c)_* M = c_* R^n g_* M`. -/
private theorem isZero_rightDerived_pushforward_comp_of_isAffineHom {A B C : Scheme.{u}}
    (g : A ⟶ B) [QuasiCompact g] [QuasiSeparated g] (c : B ⟶ C) [IsAffineHom c]
    (M : A.Modules) [M.IsQuasicoherent] (n : ℕ)
    (h : IsZero (((Scheme.Modules.pushforward g).rightDerived n).obj M)) :
    IsZero (((Scheme.Modules.pushforward (g ≫ c)).rightDerived n).obj M) := by
  letI := HasDerivedCategory.standard A.Modules
  letI := HasDerivedCategory.standard B.Modules
  letI := HasDerivedCategory.standard C.Modules
  have h₁ : IsZero (((Scheme.Modules.pushforward g).rightDerivedPlus (n : ℤ)).obj M) :=
    (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff (Scheme.Modules.pushforward g) n M).1 h
  obtain ⟨e⟩ := Stacks.AffineHigherDirectImage.nonempty_homologyFunctor_derivedPushforward_iso
    g M (n : ℤ)
  have h₂ := isZero_homology_derivedPushforward_of_isZero_homology c _
    (fun i => Stacks.AffineHigherDirectImage.isQuasicoherent_homologyFunctor_derivedPushforward
      g M i) (h₁.of_iso e)
  have h₃ := h₂.of_iso ((DerivedCategory.homologyFunctor C.Modules (n : ℤ)).mapIso
      ((derivedPushforwardCompIso g.toLRSHom.toShHom c.toLRSHom.toShHom).app
        ((DerivedCategory.singleFunctor A.Modules 0).obj M))).symm
  obtain ⟨e'⟩ := Stacks.AffineHigherDirectImage.nonempty_homologyFunctor_derivedPushforward_iso
    (g ≫ c) M (n : ℤ)
  exact (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff
    (Scheme.Modules.pushforward (g ≫ c)) n M).2 (h₃.of_iso e'.symm)

/-! ### The case without floor -/

/-- **No floor.** With coefficients of `B` in `[0, 1)` the vanishing is relative
Kawamata–Viehweg vanishing for `M - K ≡ (M - (K + B)) + B`, with `ω_V ⊗ 𝒪_V(M - K) ≅ 𝒪_V(M)`. -/
private theorem isZero_rightDerived_of_lt_one
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {W : Scheme.{0}} (sW : W ⟶ Spec (.of k)) [MMP.Mori.IsProjectiveVariety k sW]
    {V : Scheme.{0}} (sV : V ⟶ Spec (.of k)) [MMP.Mori.IsProjectiveVariety k sV]
    (hVsm : IsSmoothScheme sV)
    [IsLocallyNoetherian V] [IsNormal V] (f : V ⟶ W) (hfs : f ≫ sW = sV)
    (hf : IsBirationalMorphism f)
    {n : ℕ} (K : Divisor V) (hK : K.IsCanonicalDivisor sV n)
    (B : QDivisor V) (hB : B.IsSNC sV) (hB0 : ∀ E, 0 ≤ B E) (hB1 : ∀ E, B E < 1)
    (M : Divisor V)
    (hnef : (Divisor.toQDivisor M - (Divisor.toQDivisor K + B)).IsNef k sV)
    (i : ℕ) (hi : 0 < i) :
    IsZero (((Scheme.Modules.pushforward f).rightDerived i).obj M.divisorialSheaf) := by
  haveI : IsSmoothVariety k sV :=
    { toIsVariety := inferInstance, toSmooth := (isSmoothScheme_iff _).mp hVsm }
  haveI : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace sV
  obtain ⟨hcart, -⟩ := Divisor.cartier_weil_dictionary_of_isSmoothVariety k sV
  have hKV := isZero_rightDerived_pushforward_exteriorPower_tensor_divisorialSheaf sW sV hVsm f
    hfs hf hK.1 (M - K) _ B hnef hB hB0 hB1 (by
      have e : Divisor.toQDivisor (M - K) =
          Divisor.toQDivisor M - (Divisor.toQDivisor K + B) + B := by
        rw [map_sub]; abel
      rw [e]
      exact QDivisor.NumericallyEquivalent.refl (e ▸ QDivisor.isQCartier_toQDivisor (hcart _)))
    i hi
  obtain ⟨eK⟩ := nonempty_divisorialSheaf_iso_of_isCanonicalDivisor hVsm hK
  refine hKV.of_iso (((Scheme.Modules.pushforward f).rightDerived i).mapIso ?_).symm
  exact ((Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0} V.toRingedSpace.sheaf).mapIso
      eK.symm).app _ ≪≫ (hcart K).divisorialSheafTensorIso (hcart (M - K)) ≪≫
    eqToIso (congrArg Divisor.divisorialSheaf (add_sub_cancel K M))

/-! ### The strata of the floor -/

/-- At a point `y` of the exceptional set, fewer components of `⌊B⌋` pass through `y` than the
dimension of `𝒪_{V,y}`: otherwise the closure of `y` is a stratum of `⌊B⌋` inside `Ex(f)`. -/
private theorem card_lt_ringKrullDim_of_forall_isSNCStratum
    {k : Type u} [Field k] {W V : Scheme.{u}} (sV : V ⟶ Spec (.of k))
    [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] (f : V ⟶ W)
    (B : QDivisor V) (hB : B.IsSNC sV)
    (hstrata : ∀ S : Set V, MMP.Fourfold.IsSNCStratum B.roundDown S →
      ¬ S ⊆ (exceptionalSet f : Set V)) :
    ∀ y ∈ (exceptionalSet f : Set V),
      ((((B.roundDown.support.filter fun E => y ∈ E.support).card : ℕ∞) : WithBot ℕ∞) <
        ringKrullDim (V.presheaf.stalk y)) := by
  intro y hy
  by_contra hlt
  rw [not_lt] at hlt
  set J := B.roundDown.support.filter fun E => y ∈ E.support with hJ
  obtain ⟨n₀, z, j, hz, hj, hI⟩ := hB.2 y
  have hJB : ∀ E ∈ J, E ∈ B.support ∧ y ∈ E.support := fun E hE => by
    rw [hJ, Finset.mem_filter] at hE
    refine ⟨?_, hE.2⟩
    have h := hE.1
    rw [Finsupp.mem_support_iff] at h ⊢
    intro h0
    apply h
    change B.roundDown.coeff E = 0
    rw [DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_apply, h0, Int.floor_zero]
  -- the indices of the components through `y` exhaust the regular system of parameters
  let jJ : J → Fin n₀ := fun E => j ⟨E.1, hJB E.1 E.2⟩
  have hjJ : Function.Injective jJ := fun a b h => Subtype.ext (Subtype.mk.inj (hj h))
  have hcard : n₀ ≤ J.card := by
    rw [hz.2] at hlt
    exact_mod_cast hlt
  have hsurj : Function.Surjective jJ := by
    refine ((Fintype.bijective_iff_injective_and_card jJ).mpr ⟨hjJ, ?_⟩).2
    have h1 := Fintype.card_le_of_injective jJ hjJ
    rw [Fintype.card_coe, Fintype.card_fin] at h1 ⊢
    omega
  -- the closure of `y` is a stratum inside `Ex(f)`
  refine hstrata (closure {y}) ⟨J, Finset.filter_subset _ _, ⟨isIrreducible_singleton.closure, ?_⟩,
    fun S' hS' hle => ?_⟩ ((isClosed_exceptionalSet f).closure_subset_iff.mpr
      (Set.singleton_subset_iff.mpr hy))
  · refine Set.subset_iInter₂ fun E hE => ?_
    exact (E.idealSheaf.support.isClosed).closure_subset_iff.mpr
      (Set.singleton_subset_iff.mpr (hJB E hE).2)
  obtain ⟨hirr, hsub⟩ := hS'
  set η := hirr.genericPoint
  have hη : closure {η} = closure S' := hirr.isGenericPoint_genericPoint_closure
  have hyS' : y ∈ S' := hle (subset_closure rfl)
  have hyη : η ⤳ y := by
    rw [specializes_iff_mem_closure, hη]
    exact subset_closure hyS'
  have hηE : ∀ E ∈ J, η ∈ E.support := fun E hE => by
    have h1 : closure S' ⊆ E.idealSheaf.support :=
      (E.idealSheaf.support.isClosed).closure_subset_iff.mpr
        (hsub.trans (Set.biInter_subset_of_mem hE))
    exact h1 (hη ▸ subset_closure rfl)
  -- every parameter lies in the prime of `η`
  have hstalk : ∀ E ∈ J, AlgebraicGeometry.IdealSheafData.stalk E.idealSheaf y ≤
      MMP.Intersection.primeOfSpecializes hyη := fun E hE => by
    have h1 : E.idealSheaf ≤ Scheme.IdealSheafData.vanishingIdeal
        (TopologicalSpace.Closeds.closure ({η} : Set V)) := by
      refine Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp fun x hx => ?_
      have hx' : x ∈ closure ({η} : Set V) := hx
      exact (E.idealSheaf.support.isClosed).closure_subset_iff.mpr
        (Set.singleton_subset_iff.mpr (hηE E hE)) hx'
    have h2 := MMP.Resolution.stalk_le_stalk_of_le h1 y
    have e := Stacks.Chow.idealStalk_vanishingIdeal_closure_fromSpecStalk y
      ⟨MMP.Intersection.primeOfSpecializes hyη, inferInstance⟩
    rw [MMP.Intersection.fromSpecStalk_primeOfSpecializes] at e
    rwa [e] at h2
  have hp : IsLocalRing.maximalIdeal (V.presheaf.stalk y) ≤
      MMP.Intersection.primeOfSpecializes hyη := by
    rw [← hz.1, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨E, rfl⟩ := hsurj i
    refine hstalk E.1 E.2 ?_
    rw [hI ⟨E.1, hJB E.1 E.2⟩]
    exact Ideal.mem_span_singleton_self _
  have hsp : y ⤳ η := MMP.Intersection.specializes_of_primeOfSpecializes_le specializes_rfl hyη
    ((IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)).trans hp)
  intro s hs
  have hs' : s ∈ closure {η} := hη ▸ subset_closure hs
  exact closure_minimal (Set.singleton_subset_iff.2 (specializes_iff_mem_closure.mp hsp))
    isClosed_closure hs'

/-! ### Floor components -/

/-- The coefficient of `B - F` along `E`. -/
private theorem sub_single_apply {V : Scheme.{u}} (B : QDivisor V) (F E : MMP.Mori.PrimeDivisor V) :
    (B - Finsupp.single F 1 : QDivisor V) E = B E - if E = F then 1 else 0 := by
  rw [Finsupp.sub_apply, Finsupp.single_apply]
  simp only [eq_comm]

/-- A prime divisor lies in `⌊B⌋` exactly when its coefficient in `B` is at least one. -/
private theorem mem_roundDown_support_iff {V : Scheme.{u}} (B : QDivisor V)
    (hB0 : ∀ E, 0 ≤ B E) (hB1 : ∀ E, B E ≤ 1) (E : MMP.Mori.PrimeDivisor V) :
    E ∈ B.roundDown.support ↔ B E = 1 := by
  rw [Finsupp.mem_support_iff]
  change B.roundDown.coeff E ≠ 0 ↔ _
  rw [DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_apply]
  constructor
  · intro h
    by_contra hne
    exact h (Int.floor_eq_zero_iff.mpr ⟨hB0 E, lt_of_le_of_ne (hB1 E) hne⟩)
  · intro h
    rw [h, Int.floor_one]
    exact one_ne_zero

/-! ### The image of a floor component -/

/-- If `g ≫ c = ι ≫ f` with `ι`, `c` closed immersions, `g` surjective onto the reduced `W'`, then
`g` is an isomorphism over the preimage of every `f`-biregular open. -/
private theorem isBiregular_preimage_of_comp_eq {T V W W' : Scheme.{u}} {ι : T ⟶ V}
    [IsClosedImmersion ι] {f : V ⟶ W} {c : W' ⟶ W} [IsClosedImmersion c] {g : T ⟶ W'}
    [Surjective g] [IsReduced W'] (hgc : g ≫ c = ι ≫ f) {U : W.Opens} (hU : IsBiregular f U) :
    IsBiregular g (c ⁻¹ᵁ U) := by
  haveI hU' : IsIso (f ∣_ U) := hU
  haveI : IsClosedImmersion (ι ∣_ f ⁻¹ᵁ U) := IsZariskiLocalAtTarget.restrict ‹_› _
  haveI : IsClosedImmersion (c ∣_ U) := IsZariskiLocalAtTarget.restrict ‹_› _
  haveI : Surjective (g ∣_ c ⁻¹ᵁ U) := IsZariskiLocalAtTarget.restrict ‹_› _
  have h1 : IsClosedImmersion ((ι ≫ f) ∣_ U) := by
    have := IsClosedImmersion.comp (ι ∣_ f ⁻¹ᵁ U) (f ∣_ U)
    rwa [← morphismRestrict_comp] at this
  rw [← hgc, morphismRestrict_comp] at h1
  haveI := @IsClosedImmersion.of_comp_isClosedImmersion _ _ _ (g ∣_ c ⁻¹ᵁ U) (c ∣_ U) _ h1
  exact isIso_of_isClosedImmersion_of_surjective (g ∣_ c ⁻¹ᵁ U)

/-- `f` restricted to a closed integral subscheme `T ⟶ V` factors as a projective surjection onto
its scheme-theoretic image `W'`, a closed projective subvariety of `W`. -/
private theorem exists_factorization_image {k : Type u} [Field k] {W V T : Scheme.{u}}
    (sW : W ⟶ Spec (.of k)) [MMP.Mori.IsProjectiveVariety k sW] (f : V ⟶ W)
    (hfp : IsProjective f) (ι : T ⟶ V) [IsClosedImmersion ι] [IsIntegral T] :
    ∃ (W' : Scheme.{u}) (c : W' ⟶ W) (g : T ⟶ W'), IsClosedImmersion c ∧ g ≫ c = ι ≫ f ∧
      MMP.Mori.IsProjectiveVariety k (c ≫ sW) ∧ IsProjective g ∧ Surjective g ∧ IsReduced W' := by
  have hp : IsProjective (ι ≫ f) :=
    Stacks.QuasiProjectiveCompactification.isProjective_comp_of_isClosedImmersion ι f
      inferInstance hfp
  haveI hpr : IsProper (ι ≫ f) := hp.isProper
  haveI : QuasiCompact (ι ≫ f) :=
    @instQuasiCompactOfUniversallyClosed _ _ (ι ≫ f) hpr.toUniversallyClosed
  have hgp : IsProjective (ι ≫ f).toImage := by
    refine IsProjective.of_comp _ (ι ≫ f).imageι ?_
    rw [(ι ≫ f).toImage_imageι]
    exact hp
  haveI hgpr : IsProper (ι ≫ f).toImage := hgp.isProper
  haveI := Scheme.Hom.isIntegral_image (ι ≫ f)
  haveI : IsReduced T := inferInstance
  haveI := Scheme.Hom.isReduced_image (ι ≫ f)
  refine ⟨(ι ≫ f).image, (ι ≫ f).imageι, (ι ≫ f).toImage, inferInstance,
    (ι ≫ f).toImage_imageι, ?_, hgp, ?_, inferInstance⟩
  · haveI : AlgebraicGeometry.IsVariety k ((ι ≫ f).imageι ≫ sW) := ⟨⟩
    exact ⟨isProjectiveMorphism_isClosedImmersion_comp _ sW
      (AlgebraicGeometry.IsProjectiveVariety.isProjective)⟩
  · refine ⟨Set.range_eq_univ.mp ?_⟩
    rw [← (ι ≫ f).toImage.isClosedMap.isClosed_range.closure_eq,
      (ι ≫ f).toImage.denseRange.closure_eq]

/-- With `g ≫ c = ι ≫ f` as above, `g` is birational as soon as some point of `T` maps outside
`Ex(f)`, and `Ex(g)` lies over `Ex(f)`. -/
private theorem isBirationalMorphism_and_exceptionalSet_subset {T V W W' : Scheme.{u}}
    [IrreducibleSpace T] [IrreducibleSpace W'] {ι : T ⟶ V} [IsClosedImmersion ι] {f : V ⟶ W}
    {c : W' ⟶ W} [IsClosedImmersion c] {g : T ⟶ W'} [Surjective g] [IsReduced W']
    (hgc : g ≫ c = ι ≫ f) (t : T) (ht : ι t ∉ (exceptionalSet f : Set V)) :
    IsBirationalMorphism g ∧
      ∀ x ∈ (exceptionalSet g : Set T), ι x ∈ (exceptionalSet f : Set V) := by
  have hB := isBiregular_preimage_of_comp_eq hgc (isBiregular_biregularLocus f)
  have hpt : ∀ x : T, c (g x) = f (ι x) := fun x => by
    rw [← Scheme.Hom.comp_apply, hgc, Scheme.Hom.comp_apply]
  have hmem : ∀ x : T, ι x ∉ (exceptionalSet f : Set V) → g x ∈ c ⁻¹ᵁ biregularLocus f :=
    fun x hx => by
      change c (g x) ∈ biregularLocus f
      rw [hpt]
      exact not_not.mp hx
  refine ⟨?_, fun x hx => ?_⟩
  · refine MMP.Flips.isBirationalMorphism_of_isIso_resLE g (g ⁻¹ᵁ c ⁻¹ᵁ biregularLocus f)
      (c ⁻¹ᵁ biregularLocus f) ⟨t, hmem t ht⟩ ⟨g t, hmem t ht⟩ le_rfl ?_
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    exact hB
  · by_contra hx'
    exact hx (show g x ∈ biregularLocus g from le_biregularLocus hB (hmem x hx'))

/-! ### Divisors on a smooth prime divisor -/

/-- In `WithBot ℕ∞`, `e + 1 = n + 1` forces `e = n`. -/
private theorem eq_natCast_of_add_one_eq {e : WithBot ℕ∞} {n : ℕ}
    (h : e + 1 = ((n + 1 : ℕ) : WithBot ℕ∞)) :
    e = (n : WithBot ℕ∞) := by
  induction e using WithBot.recBotCoe with
  | bot =>
    exfalso
    rw [WithBot.bot_add, ← WithBot.coe_natCast] at h
    exact WithBot.bot_ne_coe h
  | coe m =>
    induction m using ENat.recTopCoe with
    | top =>
      exfalso
      have : ((⊤ : ℕ∞) : WithBot ℕ∞) + 1 = ((⊤ + 1 : ℕ∞) : WithBot ℕ∞) := rfl
      rw [this, top_add] at h
      refine absurd (WithBot.coe_injective h) fun h => ?_
      have := ENat.top_ne_coe (n + 1)
      push_cast at this
      exact this h
    | coe m =>
      have h' : m + 1 = n + 1 := by exact_mod_cast h
      obtain rfl : m = n := by omega
      rfl

/-- A prime divisor of a variety of dimension `m + 1` has dimension `m`. -/
private theorem topologicalKrullDim_subscheme_eq {k : Type u} [Field k] {V : Scheme.{u}}
    (sV : V ⟶ Spec (.of k)) [IsIntegral V] [LocallyOfFiniteType sV] [IsLocallyNoetherian V]
    [IsNormal V] {m : ℕ} (hdim : topologicalKrullDim V = (m + 1 : ℕ))
    (F : MMP.Mori.PrimeDivisor V) : topologicalKrullDim F.idealSheaf.subscheme = m := by
  have hPP := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sV F.genericPoint
  rw [F.coheight_genericPoint, hdim] at hPP
  have hT : topologicalKrullDim F.idealSheaf.subscheme =
      topologicalKrullDim (closure {F.genericPoint} : Set V) := by
    have e : (closure {F.genericPoint} : Set V) = Set.range F.idealSheaf.subschemeι.base := by
      rw [Scheme.IdealSheafData.range_subschemeι,
        ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    rw [e]
    exact (IsHomeomorph.topologicalKrullDim_eq _
      (Topology.IsEmbedding.toHomeomorph F.idealSheaf.subschemeι.isEmbedding).isHomeomorph)
  rw [hT]
  exact eq_natCast_of_add_one_eq (by simpa using hPP)

/-- **Linear equivalence implies numerical equivalence** for Cartier divisors. -/
private theorem numericallyEquivalent_toQDivisor_of_linearlyEquivalent {k : Type u} [Field k]
    {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] {D₁ D₂ : Divisor X}
    (h : D₁.LinearlyEquivalent D₂) (h₁ : D₁.IsCartier) (h₂ : D₂.IsCartier) :
    (Divisor.toQDivisor D₁).NumericallyEquivalent k sX (Divisor.toQDivisor D₂) := by
  have hq₁ := QDivisor.isQCartier_toQDivisor h₁
  have hq₂ := QDivisor.isQCartier_toQDivisor h₂
  refine ⟨hq₁, hq₂, fun C i _ _ _ hC => ?_⟩
  rw [QDivisor.intersectionNumber_eq_of_smul k sX i hC.le _ hq₁ one_pos D₁ h₁
      (by rw [Nat.cast_one, one_smul]),
    QDivisor.intersectionNumber_eq_of_smul k sX i hC.le _ hq₂ one_pos D₂ h₂
      (by rw [Nat.cast_one, one_smul])]
  haveI := h₁.isInvertibleModule_divisorialSheaf
  haveI := h₂.isInvertibleModule_divisorialSheaf
  rw [Divisor.degreeOn, Divisor.degreeOn, degreeOn_eq_of_iso k sX i _ h.divisorialSheafIso]

/-- A divisor is linearly equivalent to one without the component `F`. -/
private theorem exists_linearlyEquivalent_coeff_eq_zero {V : Scheme.{u}} [IsIntegral V]
    [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V] (D : Divisor V)
    (F : MMP.Mori.PrimeDivisor V) :
    ∃ D' : Divisor V, D'.coeff F = 0 ∧ D'.LinearlyEquivalent D := by
  obtain ⟨t, ht⟩ := MMP.Flips.exists_primeDivisor_ord_eq F (-(D.coeff F))
  refine ⟨D + MMP.Mori.principalDivisor t, ?_, ⟨t, by abel⟩⟩
  rw [DivisorWithCoeffs.coeff_add, MMP.Mori.coeff_principalDivisor, ht]
  ring

section Restriction

variable {Y : Scheme.{u}} [IsLocallyNoetherian Y] [CompactSpace Y]

/-- Restriction to a prime divisor `F` is subtractive on divisors of which `F` is not a
component. -/
private theorem restrictPrimeDivisor_sub {R : Type*} [AddCommGroup R]
    (D E : DivisorWithCoeffs R Y) (F : MMP.Mori.PrimeDivisor Y)
    (hD : D.coeff F = 0) (hE : E.coeff F = 0) :
    (D - E).restrictPrimeDivisor F = D.restrictPrimeDivisor F - E.restrictPrimeDivisor F := by
  rw [sub_eq_add_neg, ← neg_one_zsmul, DivisorWithCoeffs.restrictPrimeDivisor_add _ _ F hD
      (by rw [DivisorWithCoeffs.coeff_smul, hE, smul_zero]),
    DivisorWithCoeffs.restrictPrimeDivisor_zsmul _ F hE, neg_one_zsmul, ← sub_eq_add_neg]

end Restriction

section Smooth

variable {k : Type u} [Field k] {V : Scheme.{u}} (sV : V ⟶ Spec (.of k)) [IsSmoothVariety k sV]
  [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V] (F : MMP.Mori.PrimeDivisor V)
  [Smooth (F.idealSheaf.subschemeι ≫ sV)] [IsLocallyNoetherian F.idealSheaf.subscheme]
  [IsNormal F.idealSheaf.subscheme]

/-- **Projection formula for the restriction to a smooth prime divisor.** For a `ℚ`-divisor `D`
of which `F` is not a component, `D|_F` is `ℚ`-Cartier and `(D|_F · C)_F = (D · C)_V` for every
curve `C ⊆ F`. -/
private theorem exists_isQCartier_restrictPrimeDivisor_intersectionNumber_eq
    {D : QDivisor V} (hD : D.IsQCartier) (h0 : D.coeff F = 0) :
    ∃ hq : QDivisor.IsQCartier (D.restrictPrimeDivisor F),
      ∀ (C : Scheme.{u}) (j : C ⟶ F.idealSheaf.subscheme)
        [IsProper (j ≫ F.idealSheaf.subschemeι ≫ sV)]
        [IsProper ((j ≫ F.idealSheaf.subschemeι) ≫ sV)]
        (hdim : topologicalKrullDim C ≤ 1),
        QDivisor.intersectionNumber k (F.idealSheaf.subschemeι ≫ sV) j hdim
          (D.restrictPrimeDivisor F) hq =
          D.intersectionNumber k sV (j ≫ F.idealSheaf.subschemeι) hdim hD := by
  obtain ⟨m, hm, E, hE, hEc⟩ := QDivisor.isQCartier_iff_exists_pos.mp hD
  have hEF : E.coeff F = 0 := by
    have := congrArg (fun G : QDivisor V => G.coeff F) hE
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, h0, smul_zero] at this
    exact_mod_cast this
  obtain ⟨hEFc, ⟨eE⟩, -⟩ := Divisor.isCartier_restrictPrimeDivisor_of_isSmoothVariety k sV F E hEF
  have hres : Divisor.toQDivisor (E.restrictPrimeDivisor F) =
      (m : ℤ) • D.restrictPrimeDivisor F := by
    rw [← Divisor.restrictPrimeDivisor_toQDivisor E F hEF, hE,
      DivisorWithCoeffs.restrictPrimeDivisor_zsmul D F h0]
  have hq : QDivisor.IsQCartier (D.restrictPrimeDivisor F) :=
    ⟨m, by exact_mod_cast hm.ne', (⟨E.restrictPrimeDivisor F, hres, hEFc⟩ :
      QDivisor.IsCartierDivisor _)⟩
  refine ⟨hq, ?_⟩
  intro C j _ _ hdim
  haveI : IsIntegral F.idealSheaf.subscheme := F.integral
  haveI := QuasiCompact.compactSpace_of_compactSpace F.idealSheaf.subschemeι
  haveI := hEc.isInvertibleModule_divisorialSheaf
  haveI := hEFc.isInvertibleModule_divisorialSheaf
  rw [QDivisor.intersectionNumber_eq_of_smul k _ j _ _ _ hm _ hEFc hres,
    QDivisor.intersectionNumber_eq_of_smul k sV (j ≫ F.idealSheaf.subschemeι) _ _ _ hm E hEc hE,
    Divisor.degreeOn, Divisor.degreeOn,
    degreeOn_eq_of_iso k _ j _ eE,
    degreeOn_pullback_eq_degreeOn_comp (sX := F.idealSheaf.subschemeι ≫ sV) sV
      F.idealSheaf.subschemeι j rfl]

/-- **Nefness restricts to a smooth prime divisor.** If `D` is nef and `F` is not a component of
`D`, then `D|_F` is nef on `F`. -/
private theorem isNef_restrictPrimeDivisor {D : QDivisor V} (hD : D.IsNef k sV)
    (h0 : D.coeff F = 0) :
    QDivisor.IsNef k (F.idealSheaf.subschemeι ≫ sV) (D.restrictPrimeDivisor F) := by
  obtain ⟨hq, hproj⟩ := exists_isQCartier_restrictPrimeDivisor_intersectionNumber_eq sV F hD.1 h0
  refine ⟨hq, fun C j _ _ _ hC => ?_⟩
  haveI : IsProper ((j ≫ F.idealSheaf.subschemeι) ≫ sV) :=
    (Category.assoc j F.idealSheaf.subschemeι sV).symm ▸
      ‹IsProper (j ≫ F.idealSheaf.subschemeι ≫ sV)›
  rw [hproj C j hC.le]
  exact hD.2 C _ hC

open MonoidalCategory in
/-- **Adjunction for a smooth prime divisor.** There is a divisor `G ∼ K + F` of which `F` is
not a component with `G|_F ∼ K_F`. -/
private theorem exists_linearlyEquivalent_canonical_add_restrictPrimeDivisor {m : ℕ}
    [CompactSpace F.idealSheaf.subscheme] {K : Divisor V} (hK : K.IsCanonicalDivisor sV (m + 1))
    {KF : Divisor F.idealSheaf.subscheme}
    (hKF : KF.IsCanonicalDivisor (F.idealSheaf.subschemeι ≫ sV) m) :
    ∃ G : Divisor V, G.coeff F = 0 ∧ G.LinearlyEquivalent (K + Finsupp.single F 1) ∧
      Divisor.LinearlyEquivalent (G.restrictPrimeDivisor F) KF := by
  haveI : IsIntegral V := inferInstance
  have hsmY : IsSmoothScheme sV := (isSmoothScheme_iff _).mpr inferInstance
  have hsmF : IsSmoothScheme (F.idealSheaf.subschemeι ≫ sV) :=
    (isSmoothScheme_iff _).mpr inferInstance
  haveI : IsIntegral F.idealSheaf.subscheme := F.integral
  haveI : IsNoetherian V := ⟨⟩
  obtain ⟨hcart, -, -, hiso, -, -⟩ := Divisor.cartier_weil_dictionary_of_isSmoothVariety k sV
  haveI : SmoothOfRelativeDimension (m + 1) sV :=
    MMP.Intersection.smoothOfRelativeDimension_of_isVariety sV (m + 1) hK.1
  obtain ⟨τ, hτe, hτs, hτW⟩ :=
    PrimeDivisor.exists_isEffective_isSubschemeOfEffective_of_isSmoothVariety k sV F
  have hτW' := hτW ⟨⟩
  obtain ⟨⟨eAdj⟩, -⟩ :=
    MMP.Intersection.nonempty_pullback_lineBundle_iso_of_smooth_divisor sV (n := m)
      F.idealSheaf τ hτe hτs
  obtain ⟨G₀, hG₀P, hlin⟩ := exists_linearlyEquivalent_coeff_eq_zero (K + Finsupp.single F 1) F
  obtain ⟨-, ⟨eres⟩, -⟩ := Divisor.isCartier_restrictPrimeDivisor_of_isSmoothVariety k sV F G₀ hG₀P
  obtain ⟨eKY⟩ := nonempty_divisorialSheaf_iso_of_isCanonicalDivisor hsmY hK
  obtain ⟨eKF⟩ := nonempty_divisorialSheaf_iso_of_isCanonicalDivisor hsmF hKF
  have eτ : Nonempty (Divisor.divisorialSheaf (Finsupp.single F 1 : Divisor V) ≅
      MMP.CartierDivisor.sheaf τ) := by
    rw [← hτW']; exact hiso τ
  obtain ⟨eτ⟩ := eτ
  have eY : G₀.divisorialSheaf ≅
      Scheme.Hom.relativeDifferentialForms sV ((m : ℤ) + 1) ⊗ MMP.CartierDivisor.sheaf τ :=
    hlin.divisorialSheafIso ≪≫
      ((hcart K).divisorialSheafTensorIso (hcart (Finsupp.single F 1))).symm ≪≫
      whiskerRightIso (eKY ≪≫ eqToIso (by push_cast; rfl)) _ ≪≫ whiskerLeftIso _ eτ
  have α : Divisor.divisorialSheaf (DivisorWithCoeffs.restrictPrimeDivisor G₀ F) ≅
      KF.divisorialSheaf :=
    eres ≪≫ (Scheme.Modules.pullback F.idealSheaf.subschemeι).mapIso eY ≪≫ eAdj ≪≫ eKF.symm
  exact ⟨G₀, hG₀P, hlin, MMP.Flips.linearlyEquivalent_of_divisorialSheaf_iso α⟩

end Smooth

section Numerical

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]
  [IsLocallyNoetherian X] [IsNormal X]

private theorem isQCartier_neg {D : QDivisor X} (h : D.IsQCartier) : (-D).IsQCartier := by
  obtain ⟨m, hm, hD⟩ := h
  exact ⟨m, hm, by rw [smul_neg]; exact hD.neg⟩

private theorem intersectionNumber_congr {C : Scheme.{u}} (i : C ⟶ X) [IsProper (i ≫ sX)]
    (hdim : topologicalKrullDim C ≤ 1) {D D' : QDivisor X} (h : D = D') (hD : D.IsQCartier)
    (hD' : D'.IsQCartier) :
    D.intersectionNumber k sX i hdim hD = D'.intersectionNumber k sX i hdim hD' := by
  subst h; rfl

private theorem intersectionNumber_neg {C : Scheme.{u}} (i : C ⟶ X) [IsProper (i ≫ sX)]
    (hdim : topologicalKrullDim C ≤ 1) (D : QDivisor X) (hD : D.IsQCartier)
    (hD' : (-D).IsQCartier) :
    (-D).intersectionNumber k sX i hdim hD' = -D.intersectionNumber k sX i hdim hD := by
  have h0 : (0 : QDivisor X).intersectionNumber k sX i hdim QDivisor.isQCartier_zero = 0 := by
    have := QDivisor.intersectionNumber_add' k sX i hdim 0 0 QDivisor.isQCartier_zero
      QDivisor.isQCartier_zero (QDivisor.isQCartier_zero.add QDivisor.isQCartier_zero)
    rw [intersectionNumber_congr i hdim (add_zero 0) _ QDivisor.isQCartier_zero] at this
    linarith
  have := QDivisor.intersectionNumber_add' k sX i hdim D (-D) hD hD' (hD.add hD')
  rw [intersectionNumber_congr i hdim (add_neg_cancel D) _ QDivisor.isQCartier_zero, h0] at this
  linarith

private theorem numericallyEquivalent_add {D₁ D₂ E₁ E₂ : QDivisor X}
    (hD : D₁.NumericallyEquivalent k sX D₂) (hE : E₁.NumericallyEquivalent k sX E₂) :
    (D₁ + E₁).NumericallyEquivalent k sX (D₂ + E₂) := by
  obtain ⟨h₁, h₂, hD⟩ := hD
  obtain ⟨h₁', h₂', hE⟩ := hE
  refine ⟨h₁.add h₁', h₂.add h₂', fun C i _ _ _ hC => ?_⟩
  rw [QDivisor.intersectionNumber_add' k sX i hC.le _ _ h₁ h₁',
    QDivisor.intersectionNumber_add' k sX i hC.le _ _ h₂ h₂', hD C i hC, hE C i hC]

private theorem numericallyEquivalent_neg {D₁ D₂ : QDivisor X}
    (hD : D₁.NumericallyEquivalent k sX D₂) :
    (-D₁).NumericallyEquivalent k sX (-D₂) := by
  obtain ⟨h₁, h₂, hD⟩ := hD
  refine ⟨isQCartier_neg h₁, isQCartier_neg h₂, fun C i _ _ _ hC => ?_⟩
  rw [intersectionNumber_neg i hC.le _ h₁, intersectionNumber_neg i hC.le _ h₂, hD C i hC]

private theorem numericallyEquivalent_sub {D₁ D₂ E₁ E₂ : QDivisor X}
    (hD : D₁.NumericallyEquivalent k sX D₂) (hE : E₁.NumericallyEquivalent k sX E₂) :
    (D₁ - E₁).NumericallyEquivalent k sX (D₂ - E₂) := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  exact numericallyEquivalent_add hD (numericallyEquivalent_neg hE)

end Numerical

/-! ### The restricted boundary -/

private lemma stalkIdeal_eq_stalk {X : Scheme.{u}} (I : X.IdealSheafData) (x : X) :
    I.stalkIdeal x = AlgebraicGeometry.IdealSheafData.stalk I x :=
  le_antisymm
    (iSup_le fun U => le_iSup_of_le U.1 (le_iSup_of_le U.2 le_rfl))
    (iSup_le fun U => iSup_le fun hx => le_iSup_of_le ⟨U, hx⟩ le_rfl)

/-- In `Fin n` with `n ≤ 2`, two elements both different from a third are equal. -/
private lemma fin_eq_of_ne_of_ne {n : ℕ} (hn : n ≤ 2) {a b c : Fin n} (ha : a ≠ c)
    (hb : b ≠ c) : a = b := by
  rw [Ne, Fin.ext_iff] at ha hb
  ext
  omega

/-- If `F + ∑_{E ∈ S} E` is snc, with `F ∉ S`, then along every prime divisor `Q` of `F` the local
intersection lengths of the `E ∈ S` sum to at most one. -/
private lemma sum_intersectionLength_le_one {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : Y ⟶ X) (F : MMP.Mori.PrimeDivisor Y) (S : Finset (MMP.Mori.PrimeDivisor Y))
    (hF : F ∉ S)
    (hsnc : DivisorWithCoeffs.IsSNC f
      (Finsupp.single F (1 : ℤ) + ∑ E ∈ S, Finsupp.single E (1 : ℤ)))
    (Q : MMP.Mori.PrimeDivisor F.idealSheaf.subscheme) :
    ∑ E ∈ S, E.intersectionLength F.idealSheaf.subschemeι Q ≤ 1 := by
  classical
  set ι := F.idealSheaf.subschemeι with hι
  set η := Q.genericPoint with hη
  set y := ι η with hy
  set D : Divisor Y := Finsupp.single F (1 : ℤ) + ∑ E ∈ S, Finsupp.single E (1 : ℤ) with hD
  have hDapp : ∀ E, D E = (if E = F then 1 else 0) + (if E ∈ S then 1 else 0) := by
    intro E; simp [hD, Finsupp.finset_sum_apply, Finsupp.single_apply, eq_comm]
  have hFD : F ∈ D.support := by simp [hDapp, hF]
  have hSD : ∀ E ∈ S, E ∈ D.support := fun E hE => by
    simp [hDapp, hE, ne_of_mem_of_not_mem hE hF]
  have hyF : y ∈ F.support := by
    change y ∈ (F.idealSheaf.support : Set Y)
    rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨η, rfl⟩
  obtain ⟨n, z, j, hz, hj, hI⟩ := hsnc.2 y
  set φ := (ι.stalkMap η).hom with hφ
  have hφs : Function.Surjective φ := ι.stalkMap_surjective η
  have hstalk : ∀ E (h : E ∈ D.support ∧ y ∈ E.support),
      E.idealSheaf.stalkIdeal y = Ideal.span {z (j ⟨E, h⟩)} := by
    intro E h
    rw [stalkIdeal_eq_stalk]
    exact hI ⟨E, h⟩
  have hker : RingHom.ker φ = Ideal.span {z (j ⟨F, hFD, hyF⟩)} :=
    (Scheme.IdealSheafData.ker_stalkMap_subschemeι F.idealSheaf η).trans
      (hstalk F ⟨hFD, hyF⟩)
  have hdimA : ringKrullDim (F.idealSheaf.subscheme.presheaf.stalk η) = 1 := by
    rw [ringKrullDim_stalk_eq_coheight, hη,
      AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]; rfl
  have hmemB : ∀ i, z i ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y) := fun i =>
    hz.1 ▸ Ideal.subset_span ⟨i, rfl⟩
  have hn : n ≤ 2 := by
    have h1 := Ideal.height_le_ringKrullDim_quotient_add_one
      (p := IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) (hmemB (j ⟨F, hFD, hyF⟩))
    rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim, hz.2, ← hker,
      ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hφs), hdimA,
      one_add_one_eq_two] at h1
    exact_mod_cast h1
  have hjne : ∀ E (h : E ∈ D.support ∧ y ∈ E.support), E ≠ F →
      j ⟨E, h⟩ ≠ j ⟨F, hFD, hyF⟩ := fun E h hEF hjj => hEF (congrArg Subtype.val (hj hjj))
  have hlen : ∀ E ∈ S, y ∈ E.support → E.intersectionLength ι Q ≤ 1 := by
    intro E hE hyE
    have hEF : E ≠ F := ne_of_mem_of_not_mem hE hF
    set i0 := j ⟨E, hSD E hE, hyE⟩
    set iF := j ⟨F, hFD, hyF⟩
    have hi : i0 ≠ iF := hjne E _ hEF
    have hmax : (E.idealSheaf.stalkIdeal (ι η)).map φ =
        IsLocalRing.maximalIdeal (F.idealSheaf.subscheme.presheaf.stalk η) := by
      rw [hstalk E ⟨hSD E hE, hyE⟩, Ideal.map_span, Set.image_singleton]
      apply le_antisymm
      · rw [Ideal.span_le, Set.singleton_subset_iff, ←
          IsLocalRing.map_maximalIdeal_of_surjective φ hφs]
        exact Ideal.mem_map_of_mem _ (hmemB i0)
      · rw [← IsLocalRing.map_maximalIdeal_of_surjective φ hφs, ← hz.1, Ideal.map_span,
          Ideal.span_le]
        rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
        by_cases hiF : i = iF
        · have : z i ∈ RingHom.ker φ := hker ▸ hiF ▸ Ideal.mem_span_singleton_self _
          rw [RingHom.mem_ker.mp this]
          exact Ideal.zero_mem _
        · rw [fin_eq_of_ne_of_ne hn hiF hi]
          exact Ideal.mem_span_singleton_self _
    have h1 : Module.length (F.idealSheaf.subscheme.presheaf.stalk η)
        ((F.idealSheaf.subscheme.presheaf.stalk η) ⧸
          (E.idealSheaf.stalkIdeal (ι η)).map φ) = 1 := by
      rw [Module.length_eq_one_iff, hmax, isSimpleModule_iff_isCoatom]
      exact (IsLocalRing.maximalIdeal.isMaximal _).out
    unfold MMP.Mori.PrimeDivisor.intersectionLength
    rw [h1]
    rfl
  have hzero : ∀ E ∈ S, y ∉ E.support → E.intersectionLength ι Q = 0 := fun E _ h =>
    MMP.Mori.PrimeDivisor.intersectionLength_eq_zero_of_notMem ι E h
  have hcard : (S.filter fun E => y ∈ E.support).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [Finset.mem_filter] at ha hb
    exact congrArg Subtype.val (hj (fin_eq_of_ne_of_ne hn
      (hjne a ⟨hSD a ha.1, ha.2⟩ (ne_of_mem_of_not_mem ha.1 hF))
      (hjne b ⟨hSD b hb.1, hb.2⟩ (ne_of_mem_of_not_mem hb.1 hF))))
  calc ∑ E ∈ S, E.intersectionLength ι Q
      = ∑ E ∈ S.filter fun E => y ∈ E.support, E.intersectionLength ι Q := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun E hE => ?_
        split_ifs with h
        · rfl
        · exact hzero E hE h
    _ ≤ (S.filter fun E => y ∈ E.support).card • 1 :=
        Finset.sum_le_card_nsmul _ _ _ fun E hE =>
          hlen E (Finset.mem_filter.mp hE).1 (Finset.mem_filter.mp hE).2
    _ ≤ 1 := by simpa using hcard

/-- In a domain, a nonzero prime contained in a prime of height one is equal to it. -/
private lemma eq_of_le_of_height_eq_one {A : Type*} [CommRing A] [IsDomain A] {I q : Ideal A}
    [I.IsPrime] [q.IsPrime] (hI : I ≠ ⊥) (hle : I ≤ q) (hq : q.height = 1) : I = q := by
  by_contra hne
  have : q.FiniteHeight := Ideal.finiteHeight_iff_lt.mpr (Or.inr (by rw [hq]; simp))
  have h1 := Ideal.height_strict_mono_of_isPrime_of_isPrime (lt_of_le_of_ne hle hne)
  rw [hq, ENat.lt_one_iff_eq_zero, Ideal.height_eq_zero_iff_eq_bot] at h1
  exact hI h1

/-- Let `J` be an ideal sheaf contained in the ideal of a prime divisor `P`, and `y ∈ P` a point
at which `J` is cut out by a member of a regular system of parameters. Then `P` and `J` have the
same ideal at `y`. -/
private lemma stalk_idealSheaf_eq_of_le {X : Scheme.{u}} [IsLocallyNoetherian X]
    (P : MMP.Mori.PrimeDivisor X) {J : X.IdealSheafData} (hle : J ≤ P.idealSheaf) {y : X}
    (hy : y ∈ P.support) {m : ℕ} {w : Fin m → X.presheaf.stalk y}
    (hw : IsRegularSystemOfParameters w) (j0 : Fin m)
    (hst : AlgebraicGeometry.IdealSheafData.stalk J y = Ideal.span {w j0}) :
    AlgebraicGeometry.IdealSheafData.stalk P.idealSheaf y =
      AlgebraicGeometry.IdealSheafData.stalk J y := by
  obtain ⟨q, -, hPq, hq1⟩ := MMP.Intersection.exists_stalk_idealSheaf_eq_of_mem_support P hy
  have := isRegularLocalRing_of_isRegularSystemOfParameters hw
  have := IsRegularLocalRing.isDomain (X.presheaf.stalk y)
  have := MMP.Resolution.isPrime_span_singleton_of_isRegularSystemOfParameters hw j0
  rw [hPq, hst]
  refine (eq_of_le_of_height_eq_one ?_ ?_ hq1).symm
  · rw [Ne, Ideal.span_singleton_eq_bot]
    exact MMP.Resolution.ne_zero_of_isRegularSystemOfParameters hw j0
  · rw [← hst, ← hPq]
    exact MMP.Resolution.stalk_le_stalk_of_le hle y

/-- Along a prime divisor `P` of `F` lying in some `E ∈ S`, the ideal of `P` is the ideal of
`E ∩ F` at every point of `P`. -/
private lemma stalk_idealSheaf_eq_stalk_comap {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : Y ⟶ X) (F : MMP.Mori.PrimeDivisor Y) (S : Finset (MMP.Mori.PrimeDivisor Y))
    (hF : F ∉ S)
    (hsnc : DivisorWithCoeffs.IsSNC f
      (Finsupp.single F (1 : ℤ) + ∑ E ∈ S, Finsupp.single E (1 : ℤ)))
    [IsLocallyNoetherian F.idealSheaf.subscheme]
    (P : MMP.Mori.PrimeDivisor F.idealSheaf.subscheme) {E : MMP.Mori.PrimeDivisor Y}
    (hE : E ∈ S) (hPE : F.idealSheaf.subschemeι P.genericPoint ∈ E.support)
    {y : F.idealSheaf.subscheme} (hy : y ∈ P.support) :
    AlgebraicGeometry.IdealSheafData.stalk P.idealSheaf y =
      AlgebraicGeometry.IdealSheafData.stalk (E.idealSheaf.comap F.idealSheaf.subschemeι) y := by
  classical
  set ι := F.idealSheaf.subschemeι with hι
  have hDapp : ∀ E, (Finsupp.single F (1 : ℤ) + ∑ E ∈ S, Finsupp.single E (1 : ℤ)) E =
      (if E = F then 1 else 0) + (if E ∈ S then 1 else 0) := by
    intro E; simp [Finsupp.finset_sum_apply, Finsupp.single_apply, eq_comm]
  have hFD : F ∈ (Finsupp.single F (1 : ℤ) + ∑ E ∈ S, Finsupp.single E (1 : ℤ)).support := by
    rw [Finsupp.mem_support_iff, hDapp, if_pos rfl, if_neg hF]; exact one_ne_zero
  have hSD : ∀ E ∈ S,
      E ∈ (Finsupp.single F (1 : ℤ) + ∑ E ∈ S, Finsupp.single E (1 : ℤ)).support := by
    intro E hE
    rw [Finsupp.mem_support_iff, hDapp, if_pos hE, if_neg (fun h : E = F => hF (h ▸ hE))]
    exact one_ne_zero
  let Efam : S → Y.IdealSheafData := fun E => E.1.idealSheaf
  have hZ : MMP.Resolution.HasSNCWith Efam F.idealSheaf := by
    intro x hx
    obtain ⟨n, z, j, hz, hj, hI⟩ := hsnc.2 x
    have hxF : x ∈ F.support := hx
    let c : {i // x ∈ (Efam i).support} → Fin n := fun i => j ⟨i.1.1, hSD i.1.1 i.1.2, i.2⟩
    refine ⟨n, z, c, {j ⟨F, hFD, hxF⟩}, hz, fun i => hI ⟨i.1.1, hSD i.1.1 i.1.2, i.2⟩,
      fun a b hab => ?_, ?_⟩
    · have := congrArg Subtype.val (hj hab)
      exact Subtype.ext (Subtype.ext this)
    · rw [hI ⟨F, hFD, hxF⟩]; simp
  have hcomp : ∀ i, ∀ W ∈ MMP.Resolution.componentsOf (F.idealSheaf.support : Set Y),
      ¬ W ⊆ (Efam i).support := by
    intro i W hW hWE
    have hcl : (F.idealSheaf.support : Set Y) = closure {F.genericPoint} :=
      AlgebraicGeometry.PrimeDivisor.support_eq_closure F
    have hirr : IsIrreducible (F.idealSheaf.support : Set Y) := by
      rw [hcl]; exact isIrreducible_singleton.closure
    have hW' : Maximal (fun W' : Set Y => IsIrreducible W' ∧ W' ⊆ F.idealSheaf.support) W := hW
    have hWF : W = F.idealSheaf.support := (hW'.eq_of_ge ⟨hirr, le_rfl⟩ hW'.prop.2).symm
    have hmem : F.genericPoint ∈ i.1.support :=
      hWE (by rw [hWF, hcl]; exact subset_closure rfl)
    have hEF := i.1.eq_genericPoint_of_mem_support hmem F.coheight_genericPoint
    have : F = i.1 := AlgebraicGeometry.PrimeDivisor.genericPoint_injective hEF
    exact hF (this ▸ i.2)
  have hcoord := MMP.Resolution.exists_coordinates_comap_subschemeι_of_hasSNCWith hZ hcomp
  have hmemc : ∀ y ∈ P.support, y ∈ ((Efam ⟨E, hE⟩).comap ι).support := by
    intro y hy
    have hsp : P.genericPoint ⤳ y := by
      rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact hy
    exact hsp.mem_closed ((Efam ⟨E, hE⟩).comap ι).support.isClosed
      ((MMP.Resolution.mem_support_comap_iff _ _ _).2 hPE)
  obtain ⟨n, w, c', hw, hc', -⟩ := hcoord y
  have hst := hc' ⟨⟨E, hE⟩, hmemc y hy⟩
  refine stalk_idealSheaf_eq_of_le P ?_ hy hw _ hst
  rw [← MMP.Intersection.vanishingIdeal_support_idealSheaf P]
  exact Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp fun x hx => hmemc x hx

/-- The snc divisor `F + ∑_{E ∈ S} E` for `S` the components of `B - F`. -/
private theorem isSNC_single_add_sum_single {X V : Scheme.{u}} {sV : V ⟶ X} (B : QDivisor V)
    (hB : B.IsSNC sV) (F : MMP.Mori.PrimeDivisor V) (hF : F ∈ B.support)
    {S : Finset (MMP.Mori.PrimeDivisor V)} (hS : S ⊆ B.support) :
    DivisorWithCoeffs.IsSNC sV (Finsupp.single F (1 : ℤ) + ∑ E ∈ S, Finsupp.single E (1 : ℤ)) := by
  classical
  refine hB.of_support_subset fun E hE => ?_
  rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.finset_sum_apply] at hE
  by_cases hEF : E = F
  · exact hEF ▸ hF
  · rw [Finsupp.single_apply, if_neg (Ne.symm hEF), zero_add] at hE
    obtain ⟨E', hE', hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hE
    rw [Finsupp.single_apply] at hne
    split_ifs at hne with h
    · exact h ▸ hS hE'
    · exact absurd rfl hne

section Boundary

variable {X V : Scheme.{u}} [IsLocallyNoetherian V] [CompactSpace V] {sV : V ⟶ X}

/-- The coefficients of the restriction of `D` to `F`, for `F` not a component of `D`. -/
private theorem coeff_restrictPrimeDivisor_eq_sum (D : QDivisor V) (F : MMP.Mori.PrimeDivisor V)
    (hDF : D F = 0) (Q : MMP.Mori.PrimeDivisor F.idealSheaf.subscheme) :
    (D.restrictPrimeDivisor F) Q =
      ∑ E ∈ D.support, (E.intersectionLength F.idealSheaf.subschemeι Q : ℚ) * D E := by
  haveI : IsNoetherian V := ⟨⟩
  change (D.restrictPrimeDivisor F).coeff Q = _
  rw [DivisorWithCoeffs.coeff_restrictPrimeDivisor _ F hDF Q]
  simp only [Finsupp.sum, nsmul_eq_mul]

/-- **The restricted boundary.** For a boundary `D` with coefficients in `[0, 1]` of which `F` is
not a component, with `F + Supp D` snc, the restriction `D|_F` has coefficients in `[0, 1]`, and a
coefficient `1` of `D|_F` comes from a component `E` of `D` with coefficient `1` meeting `F` along
it with intersection length one. -/
private theorem restrictPrimeDivisor_bounds (D : QDivisor V) (F : MMP.Mori.PrimeDivisor V)
    (hD0 : ∀ E, 0 ≤ D E) (hD1 : ∀ E, D E ≤ 1) (hDF : D F = 0)
    (hsnc : DivisorWithCoeffs.IsSNC sV
      (Finsupp.single F (1 : ℤ) + ∑ E ∈ D.support, Finsupp.single E (1 : ℤ)))
    (Q : MMP.Mori.PrimeDivisor F.idealSheaf.subscheme) :
    0 ≤ (D.restrictPrimeDivisor F) Q ∧ (D.restrictPrimeDivisor F) Q ≤ 1 ∧
      ((D.restrictPrimeDivisor F) Q = 1 → ∃ E ∈ D.support, D E = 1 ∧
        E.intersectionLength F.idealSheaf.subschemeι Q = 1) := by
  have hFS : F ∉ D.support := by rwa [Finsupp.mem_support_iff, not_not]
  have hle := sum_intersectionLength_le_one sV F D.support hFS hsnc Q
  have hleQ : (∑ E ∈ D.support, (E.intersectionLength F.idealSheaf.subschemeι Q : ℚ)) ≤ 1 := by
    exact_mod_cast hle
  rw [coeff_restrictPrimeDivisor_eq_sum D F hDF Q]
  have hterm : ∀ E ∈ D.support,
      (E.intersectionLength F.idealSheaf.subschemeι Q : ℚ) * D E ≤
        (E.intersectionLength F.idealSheaf.subschemeι Q : ℚ) := fun E _ =>
    mul_le_of_le_one_right (Nat.cast_nonneg _) (hD1 E)
  refine ⟨Finset.sum_nonneg fun E _ => mul_nonneg (Nat.cast_nonneg _) (hD0 E),
    (Finset.sum_le_sum hterm).trans hleQ, fun h1 => ?_⟩
  -- every term has `len · (1 - d) = 0`, and some length is nonzero
  have hzero : ∑ E ∈ D.support,
      ((E.intersectionLength F.idealSheaf.subschemeι Q : ℚ) -
        (E.intersectionLength F.idealSheaf.subschemeι Q : ℚ) * D E) = 0 := by
    rw [Finset.sum_sub_distrib, h1]
    exact le_antisymm (by linarith) (by linarith [Finset.sum_le_sum hterm])
  have hz := (Finset.sum_eq_zero_iff_of_nonneg fun E hE => sub_nonneg.mpr (hterm E hE)).mp hzero
  obtain ⟨E, hE, hne⟩ : ∃ E ∈ D.support,
      (E.intersectionLength F.idealSheaf.subschemeι Q : ℚ) * D E ≠ 0 := by
    by_contra hall
    push Not at hall
    rw [Finset.sum_eq_zero hall] at h1
    exact zero_ne_one h1
  have hlen0 : E.intersectionLength F.idealSheaf.subschemeι Q ≠ 0 := by
    intro h; rw [h, Nat.cast_zero, zero_mul] at hne; exact hne rfl
  have hlen1 : E.intersectionLength F.idealSheaf.subschemeι Q = 1 := by
    have : E.intersectionLength F.idealSheaf.subschemeι Q ≤
        ∑ E ∈ D.support, E.intersectionLength F.idealSheaf.subschemeι Q :=
      Finset.single_le_sum (f := fun E => E.intersectionLength F.idealSheaf.subschemeι Q)
        (fun _ _ => Nat.zero_le _) hE
    omega
  refine ⟨E, hE, ?_, hlen1⟩
  have := hz E hE
  rw [hlen1, Nat.cast_one, one_mul] at this
  linarith

/-- The support of the restriction of `D` to `F` lies in the restriction of `Supp D`. -/
private theorem support_restrictPrimeDivisor_subset (D : QDivisor V) (F : MMP.Mori.PrimeDivisor V)
    (hD0 : ∀ E, 0 ≤ D E) (hDF : D F = 0) :
    (D.restrictPrimeDivisor F).support ⊆
      (DivisorWithCoeffs.restrictPrimeDivisor
        (∑ E ∈ D.support, Finsupp.single E (1 : ℤ)) F).support := by
  classical
  haveI : IsNoetherian V := ⟨⟩
  have hT0 : DivisorWithCoeffs.coeff (∑ E ∈ D.support, Finsupp.single E (1 : ℤ)) F = 0 := by
    rw [DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply]
    refine Finset.sum_eq_zero fun E hE => ?_
    rw [Finsupp.single_apply, if_neg]
    rintro rfl
    exact (Finsupp.mem_support_iff.mp hE) hDF
  intro Q hQ
  rw [Finsupp.mem_support_iff] at hQ ⊢
  rw [coeff_restrictPrimeDivisor_eq_sum D F hDF Q] at hQ
  obtain ⟨E, hE, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hQ
  have hlen0 : E.intersectionLength F.idealSheaf.subschemeι Q ≠ 0 := by
    intro h; rw [h, Nat.cast_zero, zero_mul] at hne; exact hne rfl
  change (DivisorWithCoeffs.restrictPrimeDivisor _ F).coeff Q ≠ 0
  rw [DivisorWithCoeffs.coeff_restrictPrimeDivisor _ F hT0 Q]
  rw [← Finsupp.sum_finset_sum_index (fun _ => smul_zero _) (fun _ _ _ => smul_add _ _ _)]
  have hs : ∀ i ∈ D.support, ((Finsupp.single i (1 : ℤ)).sum fun x d =>
      (x.intersectionLength F.idealSheaf.subschemeι Q) • d) =
        (i.intersectionLength F.idealSheaf.subschemeι Q : ℤ) := fun i _ => by
    rw [Finsupp.sum_single_index] <;> simp
  rw [Finset.sum_congr rfl hs]
  have hpos : 0 < ∑ i ∈ D.support, (i.intersectionLength F.idealSheaf.subschemeι Q : ℤ) :=
    lt_of_lt_of_le (by exact_mod_cast Nat.pos_of_ne_zero hlen0)
      (Finset.single_le_sum (f := fun i => (i.intersectionLength F.idealSheaf.subschemeι Q : ℤ))
        (fun _ _ => Nat.cast_nonneg _) hE)
  exact hpos.ne'

end Boundary

section Count

variable {X V : Scheme.{u}} [IsLocallyNoetherian V] [CompactSpace V] {sV : V ⟶ X}

/-- **Counting floor components on `F`.** At a point `x` of `F`, the components of `⌊D|_F⌋`
through `x` inject into the components of `⌊B⌋` other than `F` through `x`, by the component
`E` of `D` with `D|_F` supported on `E ∩ F`. -/
private theorem card_floor_restrictPrimeDivisor_add_one_le (B : QDivisor V)
    (F : MMP.Mori.PrimeDivisor V) (hBF : B F = 1) (hB0 : ∀ E, 0 ≤ B E) (hB1 : ∀ E, B E ≤ 1)
    (D : QDivisor V) (hD0 : ∀ E, 0 ≤ D E) (hD1 : ∀ E, D E ≤ 1) (hDF : D F = 0)
    (hDB : ∀ E, E ≠ F → D E = B E)
    (hsnc : DivisorWithCoeffs.IsSNC sV
      (Finsupp.single F (1 : ℤ) + ∑ E ∈ D.support, Finsupp.single E (1 : ℤ)))
    [IsLocallyNoetherian F.idealSheaf.subscheme] (x : F.idealSheaf.subscheme) :
    ((D.restrictPrimeDivisor F).roundDown.support.filter fun Q => x ∈ Q.support).card + 1 ≤
      (B.roundDown.support.filter fun E => F.idealSheaf.subschemeι x ∈ E.support).card := by
  classical
  set ι := F.idealSheaf.subschemeι with hι
  set FT := (D.restrictPrimeDivisor F).roundDown.support.filter fun Q => x ∈ Q.support with hFT
  set FV := B.roundDown.support.filter fun E => ι x ∈ E.support with hFV
  have hb := restrictPrimeDivisor_bounds D F hD0 hD1 hDF hsnc
  have hE : ∀ Q ∈ FT, ∃ E ∈ D.support, D E = 1 ∧ E.intersectionLength ι Q = 1 := by
    intro Q hQ
    rw [hFT, Finset.mem_filter, mem_roundDown_support_iff _ (fun Q => (hb Q).1)
      (fun Q => (hb Q).2.1)] at hQ
    exact (hb Q).2.2 hQ.1
  haveI : Nonempty (MMP.Mori.PrimeDivisor V) := ⟨F⟩
  choose! e he using hE
  have hxι : ι x ∈ F.support := by
    change ι x ∈ (F.idealSheaf.support : Set V)
    rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨x, rfl⟩
  have hFFV : F ∈ FV := by
    rw [hFV, Finset.mem_filter, mem_roundDown_support_iff B hB0 hB1]
    exact ⟨hBF, hxι⟩
  have hgen : ∀ Q ∈ FT, ι Q.genericPoint ∈ (e Q).support := by
    intro Q hQ
    by_contra h
    have := MMP.Mori.PrimeDivisor.intersectionLength_eq_zero_of_notMem ι (e Q) h (P := Q)
    rw [(he Q hQ).2.2] at this
    exact one_ne_zero this
  have hxQ : ∀ Q ∈ FT, x ∈ Q.support := fun Q hQ => (Finset.mem_filter.mp hQ).2
  have hmaps : ∀ Q ∈ FT, e Q ∈ FV.erase F := by
    intro Q hQ
    have hne : e Q ≠ F := by
      intro h
      have := (he Q hQ).2.1
      rw [h, hDF] at this
      exact zero_ne_one this
    rw [Finset.mem_erase, hFV, Finset.mem_filter, mem_roundDown_support_iff B hB0 hB1]
    refine ⟨hne, ?_, ?_⟩
    · rw [← hDB _ hne]; exact (he Q hQ).2.1
    · have hsp : Q.genericPoint ⤳ x := by
        rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact hxQ Q hQ
      exact (hsp.map ι.continuous).mem_closed (e Q).idealSheaf.support.isClosed (hgen Q hQ)
  have hinj : Set.InjOn e FT := by
    intro Q hQ Q' hQ' h
    have h1 := stalk_idealSheaf_eq_stalk_comap sV F D.support
      (by rwa [Finsupp.mem_support_iff, not_not]) hsnc Q (he Q hQ).1 (hgen Q hQ)
      (hxQ Q hQ)
    have h2 := stalk_idealSheaf_eq_stalk_comap sV F D.support
      (by rwa [Finsupp.mem_support_iff, not_not]) hsnc Q' (he Q' hQ').1 (hgen Q' hQ')
      (hxQ Q' hQ')
    rw [h] at h1
    exact MMP.Intersection.eq_of_stalk_idealSheaf_eq (hxQ Q hQ) (hxQ Q' hQ') (h1.trans h2.symm)
  have hle := Finset.card_le_card_of_injOn e hmaps hinj
  rw [Finset.card_erase_of_mem hFFV] at hle
  have hpos : 0 < FV.card := Finset.card_pos.mpr ⟨F, hFFV⟩
  omega

/-- The local ring of `V` at a point of the smooth component `F` of an snc divisor has dimension
at most one more than the local ring of `F`. -/
private theorem ringKrullDim_stalk_le_add_one (B : QDivisor V) (hB : B.IsSNC sV)
    (F : MMP.Mori.PrimeDivisor V) (hF : F ∈ B.support) (x : F.idealSheaf.subscheme) :
    ringKrullDim (V.presheaf.stalk (F.idealSheaf.subschemeι x)) ≤
      ringKrullDim (F.idealSheaf.subscheme.presheaf.stalk x) + 1 := by
  set ι := F.idealSheaf.subschemeι with hι
  have hyF : ι x ∈ F.support := by
    change ι x ∈ (F.idealSheaf.support : Set V)
    rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨x, rfl⟩
  obtain ⟨n, z, j, hz, hj, hI⟩ := hB.2 (ι x)
  set φ := (ι.stalkMap x).hom with hφ
  have hφs : Function.Surjective φ := ι.stalkMap_surjective x
  have hker : RingHom.ker φ = Ideal.span {z (j ⟨F, hF, hyF⟩)} := by
    refine (Scheme.IdealSheafData.ker_stalkMap_subschemeι F.idealSheaf x).trans ?_
    rw [stalkIdeal_eq_stalk]
    exact hI ⟨F, hF, hyF⟩
  have hmem : z (j ⟨F, hF, hyF⟩) ∈ IsLocalRing.maximalIdeal (V.presheaf.stalk (ι x)) :=
    hz.1 ▸ Ideal.subset_span ⟨_, rfl⟩
  have h1 := Ideal.height_le_ringKrullDim_quotient_add_one
    (p := IsLocalRing.maximalIdeal (V.presheaf.stalk (ι x))) hmem
  rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim, ← hker,
    ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hφs)] at h1
  exact h1

end Count

/-- The boundary `B - F` for a component `F` of `⌊B⌋` keeps the hypotheses, with one floor
component less. -/
private theorem floor_sub_single {V : Scheme.{u}} (B : QDivisor V) (hB0 : ∀ E, 0 ≤ B E)
    (hB1 : ∀ E, B E ≤ 1) (F : MMP.Mori.PrimeDivisor V) (hF : F ∈ B.roundDown.support) :
    B F = 1 ∧ (∀ E, 0 ≤ (B - Finsupp.single F 1 : QDivisor V) E) ∧
      (∀ E, (B - Finsupp.single F 1 : QDivisor V) E ≤ 1) ∧
      (B - Finsupp.single F 1 : QDivisor V).support ⊆ B.support ∧
      (B - Finsupp.single F 1 : QDivisor V).roundDown.support = B.roundDown.support.erase F := by
  have hBF : B F = 1 := (mem_roundDown_support_iff B hB0 hB1 F).mp hF
  have h0 : ∀ E, 0 ≤ (B - Finsupp.single F 1 : QDivisor V) E := by
    intro E
    rw [sub_single_apply]
    split_ifs with h
    · rw [h, hBF, sub_self]
    · rw [sub_zero]; exact hB0 E
  have h1 : ∀ E, (B - Finsupp.single F 1 : QDivisor V) E ≤ 1 := by
    intro E
    rw [sub_single_apply]
    split_ifs
    · linarith [hB1 E]
    · rw [sub_zero]; exact hB1 E
  refine ⟨hBF, h0, h1, fun E hE => ?_, ?_⟩
  · rw [Finsupp.mem_support_iff] at hE ⊢
    rw [sub_single_apply] at hE
    split_ifs at hE with h
    · exact absurd (by rw [h, hBF, sub_self]) hE
    · rwa [sub_zero] at hE
  · ext E
    rw [Finset.mem_erase, mem_roundDown_support_iff _ h0 h1, mem_roundDown_support_iff B hB0 hB1,
      sub_single_apply]
    split_ifs with h
    · subst h
      simp [hBF]
    · simp [h]

/-- A component of `⌊B⌋` exists unless all coefficients are less than one. -/
private theorem lt_one_of_roundDown_support_eq_empty {V : Scheme.{u}} (B : QDivisor V)
    (hB0 : ∀ E, 0 ≤ B E) (hB1 : ∀ E, B E ≤ 1) (h : B.roundDown.support = ∅)
    (E : MMP.Mori.PrimeDivisor V) : B E < 1 := by
  refine lt_of_le_of_ne (hB1 E) fun hE => ?_
  have := (mem_roundDown_support_iff B hB0 hB1 E).mpr hE
  rw [h] at this
  exact Finset.notMem_empty E this

/-- `F`, regarded as a `ℚ`-divisor. -/
private theorem toQDivisor_single {V : Scheme.{u}} (F : MMP.Mori.PrimeDivisor V) :
    Divisor.toQDivisor (Finsupp.single F 1 : Divisor V) = Finsupp.single F 1 := by
  ext E
  change (Divisor.toQDivisor (Finsupp.single F 1 : Divisor V)).coeff E = _
  rw [Divisor.coeff_toQDivisor]
  simp only [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply]
  split_ifs <;> simp

/-- A variety with a prime divisor has positive dimension. -/
private theorem exists_eq_add_one_of_primeDivisor {k : Type u} [Field k] {V : Scheme.{u}}
    (sV : V ⟶ Spec (.of k)) [IsIntegral V] [LocallyOfFiniteType sV] [IsLocallyNoetherian V]
    [IsNormal V] {n : ℕ} (hn : topologicalKrullDim V = n) (F : MMP.Mori.PrimeDivisor V) :
    ∃ m, n = m + 1 := by
  refine Nat.exists_eq_add_one_of_ne_zero fun hn0 => ?_
  subst hn0
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sV F.genericPoint
  rw [F.coheight_genericPoint, hn] at h
  have hne : topologicalKrullDim (closure {F.genericPoint} : Set V) ≠ ⊥ :=
    (Order.krullDim_ne_bot_iff
      (α := TopologicalSpace.IrreducibleCloseds (closure {F.genericPoint} : Set V))).mpr
      ⟨TopologicalSpace.IrreducibleCloseds.closureSingleton ⟨F.genericPoint, subset_closure rfl⟩⟩
  obtain ⟨b, hb⟩ := WithBot.ne_bot_iff_exists.mp hne
  rw [← hb] at h
  norm_cast at h
  simp at h

/-- Counting in `WithBot ℕ∞`: from `a + 1 ≤ b < d ≤ e + 1` follows `a < e`. -/
private theorem lt_of_add_one_le_of_lt_of_le_add_one {a b : ℕ} {d e : WithBot ℕ∞}
    (h₁ : a + 1 ≤ b) (h₂ : ((b : ℕ∞) : WithBot ℕ∞) < d) (h₃ : d ≤ e + 1) :
    ((a : ℕ∞) : WithBot ℕ∞) < e := by
  have h := lt_of_lt_of_le h₂ h₃
  induction e using WithBot.recBotCoe with
  | bot => exact absurd h (by rw [WithBot.bot_add]; exact not_lt_bot)
  | coe e =>
    induction e using ENat.recTopCoe with
    | top => exact WithBot.coe_lt_coe.mpr (ENat.coe_lt_top a)
    | coe e =>
      have h' : ((b : ℕ∞) : WithBot ℕ∞) < (((e + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
        simpa using h
      have h'' : b < e + 1 := by exact_mod_cast h'
      have : a < e := by omega
      exact_mod_cast this

/-! ### The restriction to a floor component -/

/-- **The restriction step.** For a component `F` of `⌊B⌋`, with closed immersion
`ι : F ⟶ V`, the higher direct images of `ι_* ι^* 𝒪_V(M)` vanish, granted the vanishing in
dimension one less. -/
private theorem isZero_rightDerived_pushforward_restriction
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {m : ℕ}
    (ih : ∀ {W V : Scheme.{0}} (sW : W ⟶ Spec (.of k)) [MMP.Mori.IsProjectiveVariety k sW]
      (sV : V ⟶ Spec (.of k)) [MMP.Mori.IsProjectiveVariety k sV] (_ : IsSmoothScheme sV)
      [IsLocallyNoetherian V] [IsNormal V] (f : V ⟶ W) (_ : f ≫ sW = sV)
      (_ : IsProjective f) (_ : IsBirationalMorphism f)
      (K : Divisor V) (_ : K.IsCanonicalDivisor sV m)
      (B : QDivisor V) (_ : B.IsSNC sV) (_ : ∀ E, 0 ≤ B E) (_ : ∀ E, B E ≤ 1)
      (_ : ∀ y ∈ (exceptionalSet f : Set V),
        ((((B.roundDown.support.filter fun E => y ∈ E.support).card : ℕ∞) : WithBot ℕ∞) <
          ringKrullDim (V.presheaf.stalk y)))
      (M : Divisor V) (_ : M.IsCartier)
      (_ : (Divisor.toQDivisor M - (Divisor.toQDivisor K + B)).IsNef k sV)
      (i : ℕ) (_ : 0 < i),
      IsZero (((Scheme.Modules.pushforward f).rightDerived i).obj M.divisorialSheaf))
    {W : Scheme.{0}} (sW : W ⟶ Spec (.of k)) [MMP.Mori.IsProjectiveVariety k sW]
    {V : Scheme.{0}} (sV : V ⟶ Spec (.of k)) [MMP.Mori.IsProjectiveVariety k sV]
    (hVsm : IsSmoothScheme sV)
    [IsLocallyNoetherian V] [IsNormal V] (f : V ⟶ W) (hfs : f ≫ sW = sV)
    (hfp : IsProjective f) (hf : IsBirationalMorphism f)
    (K : Divisor V) (hK : K.IsCanonicalDivisor sV (m + 1))
    (B : QDivisor V) (hB : B.IsSNC sV) (hB0 : ∀ E, 0 ≤ B E) (hB1 : ∀ E, B E ≤ 1)
    (hcount : ∀ y ∈ (exceptionalSet f : Set V),
      ((((B.roundDown.support.filter fun E => y ∈ E.support).card : ℕ∞) : WithBot ℕ∞) <
        ringKrullDim (V.presheaf.stalk y)))
    (F : MMP.Mori.PrimeDivisor V) (hF : B F = 1)
    (M : Divisor V)
    (hnef : (Divisor.toQDivisor M - (Divisor.toQDivisor K + B)).IsNef k sV)
    (i : ℕ) (hi : 0 < i) :
    IsZero (((Scheme.Modules.pushforward f).rightDerived i).obj
      ((Scheme.Modules.pullback F.idealSheaf.subschemeι ⋙
        Scheme.Modules.pushforward F.idealSheaf.subschemeι).obj M.divisorialSheaf)) := by
  set T := F.idealSheaf.subscheme with hT
  set ι := F.idealSheaf.subschemeι with hι
  -- `V` and the smooth prime divisor `T`
  haveI : IsSmoothVariety k sV :=
    { toIsVariety := inferInstance, toSmooth := (isSmoothScheme_iff _).mp hVsm }
  haveI : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace sV
  obtain ⟨hcartV, -, -, -, -, hqcV⟩ := Divisor.cartier_weil_dictionary_of_isSmoothVariety k sV
  have hFB : F ∈ B.support := by rw [Finsupp.mem_support_iff, hF]; exact one_ne_zero
  have hsmT : IsSmoothScheme (ι ≫ sV) := hB.1 F hFB
  haveI : Smooth (ι ≫ sV) := (isSmoothScheme_iff _).mp hsmT
  haveI : IsIntegral T := F.integral
  haveI : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian (ι ≫ sV)
  haveI : IsNormal T := isNormal_of_smooth_over_field (ι ≫ sV)
  haveI : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace ι
  haveI : AlgebraicGeometry.IsVariety k (ι ≫ sV) := ⟨⟩
  haveI : MMP.Mori.IsProjectiveVariety k (ι ≫ sV) :=
    ⟨isProjectiveMorphism_isClosedImmersion_comp ι sV
      AlgebraicGeometry.IsProjectiveVariety.isProjective⟩
  haveI : IsSmoothVariety k (ι ≫ sV) :=
    { toIsVariety := inferInstance, toSmooth := inferInstance }
  obtain ⟨hcartT, -, -, -, -, hqcT⟩ :=
    Divisor.cartier_weil_dictionary_of_isSmoothVariety k (ι ≫ sV)
  have hdimT : topologicalKrullDim T = m := topologicalKrullDim_subscheme_eq sV hK.1 F
  obtain ⟨KT, hKT⟩ := exists_isCanonicalDivisor_of_isSmoothScheme (ι ≫ sV) hsmT hdimT
  -- the boundary `B_T = (B - F)|_T`
  obtain ⟨-, hD0, hD1, hDsupp, -⟩ :=
    floor_sub_single B hB0 hB1 F ((mem_roundDown_support_iff B hB0 hB1 F).mpr hF)
  set D : QDivisor V := B - Finsupp.single F 1 with hD
  have hDF : D F = 0 := by rw [hD, sub_single_apply, if_pos rfl, hF, sub_self]
  have hDB : ∀ E, E ≠ F → D E = B E := fun E hE => by
    rw [hD, sub_single_apply, if_neg hE, sub_zero]
  have hsnc := isSNC_single_add_sum_single B hB F hFB hDsupp
  have hFS : F ∉ D.support := by rwa [Finsupp.mem_support_iff, not_not]
  set BT : QDivisor T := D.restrictPrimeDivisor F with hBT
  have hbT := restrictPrimeDivisor_bounds D F hD0 hD1 hDF hsnc
  have hBTsnc : BT.IsSNC (ι ≫ sV) :=
    (DivisorWithCoeffs.isSNC_restrictPrimeDivisor_sum_single sV F D.support hFS
      hsnc).1.of_support_subset
      (support_restrictPrimeDivisor_subset D F hD0 hDF)
  -- the image `W'` of `T` in `W`
  obtain ⟨W', c, g, hc, hgc, hW', hgp, hgs, hW'red⟩ := exists_factorization_image sW f hfp ι
  haveI := hc
  haveI := hW'
  haveI := hgs
  haveI := hW'red
  haveI : IsIntegral W' := inferInstance
  have hgen : ι (genericPoint T) ∉ (exceptionalSet f : Set V) := by
    intro hmem
    have h1 := hcount _ hmem
    have h2 := ringKrullDim_stalk_le_add_one B hB F hFB (genericPoint T)
    have h3 : ringKrullDim (T.presheaf.stalk (genericPoint T)) = 0 :=
      ringKrullDim_eq_zero_of_field T.functionField
    have hF' : F ∈ B.roundDown.support.filter fun E => ι (genericPoint T) ∈ E.support := by
      rw [Finset.mem_filter, mem_roundDown_support_iff B hB0 hB1]
      refine ⟨hF, ?_⟩
      change ι (genericPoint T) ∈ (F.idealSheaf.support : Set V)
      rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨_, rfl⟩
    have hc1 := Finset.card_pos.mpr ⟨F, hF'⟩
    rw [h3, zero_add] at h2
    have h4 := lt_of_lt_of_le h1 h2
    have h5 : (B.roundDown.support.filter fun E => ι (genericPoint T) ∈ E.support).card < 1 := by
      exact_mod_cast h4
    omega
  obtain ⟨hgbir, hExg⟩ := isBirationalMorphism_and_exceptionalSet_subset hgc (genericPoint T) hgen
  -- the counting condition for `g`
  have hcountT : ∀ x ∈ (exceptionalSet g : Set T),
      ((((BT.roundDown.support.filter fun Q => x ∈ Q.support).card : ℕ∞) : WithBot ℕ∞) <
        ringKrullDim (T.presheaf.stalk x)) := fun x hx =>
    lt_of_add_one_le_of_lt_of_le_add_one
      (card_floor_restrictPrimeDivisor_add_one_le B F hF hB0 hB1 D hD0 hD1 hDF hDB hsnc x)
      (hcount (ι x) (hExg x hx)) (ringKrullDim_stalk_le_add_one B hB F hFB x)
  -- `M|_T`, after moving `M` off `T`
  obtain ⟨M', hM'F, hM'lin⟩ := exists_linearlyEquivalent_coeff_eq_zero M F
  obtain ⟨hMTc, ⟨eMT⟩, -⟩ :=
    Divisor.isCartier_restrictPrimeDivisor_of_isSmoothVariety k sV F M' hM'F
  -- adjunction
  obtain ⟨G, hGF, hGlin, hGT⟩ :=
    exists_linearlyEquivalent_canonical_add_restrictPrimeDivisor sV F hK hKT
  -- the nef difference on `T`
  have hnefT : (Divisor.toQDivisor (M'.restrictPrimeDivisor F) -
      (Divisor.toQDivisor KT + BT)).IsNef k (ι ≫ sV) := by
    set DV : QDivisor V := Divisor.toQDivisor M' - (Divisor.toQDivisor G + D) with hDV
    have hM'F' : (Divisor.toQDivisor M').coeff F = 0 := by
      rw [Divisor.coeff_toQDivisor, hM'F, Int.cast_zero]
    have hGF' : (Divisor.toQDivisor G).coeff F = 0 := by
      rw [Divisor.coeff_toQDivisor, hGF, Int.cast_zero]
    have hDF' : D.coeff F = 0 := hDF
    have hGDF : (Divisor.toQDivisor G + D).coeff F = 0 := by
      rw [DivisorWithCoeffs.coeff_add, hGF', hDF', add_zero]
    have hDVF : DV.coeff F = 0 := by
      rw [hDV, DivisorWithCoeffs.coeff_sub, hM'F', hGDF, sub_zero]
    have hDVeq : DV.NumericallyEquivalent k sV
        (Divisor.toQDivisor M - (Divisor.toQDivisor K + B)) := by
      have e : Divisor.toQDivisor M - (Divisor.toQDivisor K + B) =
          Divisor.toQDivisor M - (Divisor.toQDivisor (K + Finsupp.single F 1) + D) := by
        rw [map_add, toQDivisor_single, hD]; abel
      rw [e]
      exact numericallyEquivalent_sub
        (numericallyEquivalent_toQDivisor_of_linearlyEquivalent hM'lin (hcartV _) (hcartV _))
        (numericallyEquivalent_add
          (numericallyEquivalent_toQDivisor_of_linearlyEquivalent hGlin (hcartV _) (hcartV _))
          (QDivisor.NumericallyEquivalent.refl (hqcV D)))
    have hres : DV.restrictPrimeDivisor F = Divisor.toQDivisor (M'.restrictPrimeDivisor F) -
        (Divisor.toQDivisor (G.restrictPrimeDivisor F) + BT) := by
      rw [hDV, restrictPrimeDivisor_sub _ _ F hM'F' hGDF,
        DivisorWithCoeffs.restrictPrimeDivisor_add _ _ F hGF' hDF',
        Divisor.restrictPrimeDivisor_toQDivisor M' F hM'F,
        Divisor.restrictPrimeDivisor_toQDivisor G F hGF]
    have hequiv : (Divisor.toQDivisor (M'.restrictPrimeDivisor F) -
        (Divisor.toQDivisor KT + BT)).NumericallyEquivalent k (ι ≫ sV)
          (DV.restrictPrimeDivisor F) := by
      rw [hres]
      exact numericallyEquivalent_sub (QDivisor.NumericallyEquivalent.refl (hqcT _))
        (numericallyEquivalent_add
          (numericallyEquivalent_toQDivisor_of_linearlyEquivalent hGT (hcartT _)
            (hcartT _)).symm
          (QDivisor.NumericallyEquivalent.refl (hqcT BT)))
    exact (QDivisor.NumericallyEquivalent.isNef_iff hequiv).mpr
      (isNef_restrictPrimeDivisor sV F ((QDivisor.NumericallyEquivalent.isNef_iff hDVeq).mpr hnef)
        hDVF)
  -- the vanishing on `T`, by the induction on the dimension
  have hT := ih (c ≫ sW) (ι ≫ sV) hsmT g (by rw [← Category.assoc, hgc, Category.assoc, hfs])
    hgp hgbir KT hKT BT hBTsnc (fun Q => (hbT Q).1) (fun Q => (hbT Q).2.1) hcountT
    (M'.restrictPrimeDivisor F) hMTc hnefT i hi
  -- transport along `T ⟶ W' ⟶ W` and `T ⟶ V`
  haveI : IsProper g := hgp.isProper
  haveI : QuasiCompact g := @instQuasiCompactOfUniversallyClosed _ _ g inferInstance
  haveI : QuasiSeparated g := IsSeparated.instQuasiSeparated g
  have h1 := isZero_rightDerived_pushforward_comp_of_isAffineHom g c _ i hT
  rw [hgc] at h1
  have eG : (Scheme.Modules.pullback ι).obj M.divisorialSheaf ≅
      Divisor.divisorialSheaf (M'.restrictPrimeDivisor F) :=
    (Scheme.Modules.pullback ι).mapIso hM'lin.divisorialSheafIso.symm ≪≫ eMT.symm
  have h2 := h1.of_iso (((Scheme.Modules.pushforward (ι ≫ f)).rightDerived i).mapIso eG)
  exact h2.of_iso
    (Stacks.AlgebraicGeometry.ClosedImmersionRelativeLeray.rightDerivedPushforwardObjIso
      ι f _ i).symm

/-! ### The induction -/

/-- **The induction.** The vanishing holds in every dimension `n`, with the condition on the
strata of `⌊B⌋` in its counting form. -/
private theorem main {k : Type} [Field k] [IsAlgClosed k] [CharZero k] (n : ℕ) :
    ∀ {W V : Scheme.{0}} (sW : W ⟶ Spec (.of k)) [MMP.Mori.IsProjectiveVariety k sW]
      (sV : V ⟶ Spec (.of k)) [MMP.Mori.IsProjectiveVariety k sV] (_ : IsSmoothScheme sV)
      [IsLocallyNoetherian V] [IsNormal V] (f : V ⟶ W) (_ : f ≫ sW = sV)
      (_ : IsProjective f) (_ : IsBirationalMorphism f)
      (K : Divisor V) (_ : K.IsCanonicalDivisor sV n)
      (B : QDivisor V) (_ : B.IsSNC sV) (_ : ∀ E, 0 ≤ B E) (_ : ∀ E, B E ≤ 1)
      (_ : ∀ y ∈ (exceptionalSet f : Set V),
        ((((B.roundDown.support.filter fun E => y ∈ E.support).card : ℕ∞) : WithBot ℕ∞) <
          ringKrullDim (V.presheaf.stalk y)))
      (M : Divisor V) (_ : M.IsCartier)
      (_ : (Divisor.toQDivisor M - (Divisor.toQDivisor K + B)).IsNef k sV)
      (i : ℕ) (_ : 0 < i),
      IsZero (((Scheme.Modules.pushforward f).rightDerived i).obj M.divisorialSheaf) := by
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro W V sW _ sV _ hVsm _ _ f hfs hfp hf K hK B hB hB0 hB1 hcount M hM hnef i hi
  -- induction on the number of floor components
  generalize hN : B.roundDown.support.card = N
  induction N using Nat.strong_induction_on generalizing B M with
  | _ N ihN =>
  rcases Finset.eq_empty_or_nonempty B.roundDown.support with h0 | ⟨F, hF⟩
  · exact isZero_rightDerived_of_lt_one sW sV hVsm f hfs hf K hK B hB hB0
      (lt_one_of_roundDown_support_eq_empty B hB0 hB1 h0) M hnef i hi
  obtain ⟨hBF, hB0', hB1', hsupp, hfloor⟩ := floor_sub_single B hB0 hB1 F hF
  haveI : IsSmoothVariety k sV :=
    { toIsVariety := inferInstance, toSmooth := (isSmoothScheme_iff _).mp hVsm }
  haveI : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace sV
  obtain ⟨hcart, -⟩ := Divisor.cartier_weil_dictionary_of_isSmoothVariety k sV
  obtain ⟨N', rfl⟩ : ∃ N' : Divisor V, M = N' + Finsupp.single F 1 :=
    ⟨M - Finsupp.single F 1, (sub_add_cancel M _).symm⟩
  obtain ⟨hz, hS⟩ := Divisor.IsCartier.shortExact_divisorialSheafInclusion_restriction sV
    (inferInstance : MMP.Mori.IsVariety k sV) hVsm F (hcart N')
  refine isZero_rightDerived_obj_X₂ f hS i ?_ ?_
  · -- the first term `𝒪_V(M - F)`, with boundary `B - F`
    have hcard : (B - Finsupp.single F 1 : QDivisor V).roundDown.support.card < N := by
      rw [hfloor, Finset.card_erase_of_mem hF, ← hN]
      exact Nat.sub_lt (Finset.card_pos.mpr ⟨F, hF⟩) one_pos
    refine ihN _ hcard (B - Finsupp.single F 1 : QDivisor V) (hB.of_support_subset hsupp) hB0'
      hB1' (fun y hy => lt_of_le_of_lt ?_ (hcount y hy)) N' (hcart N') ?_ rfl
    · rw [hfloor]
      exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ (Finset.erase_subset F _))
    · have e : Divisor.toQDivisor N' - (Divisor.toQDivisor K + (B - Finsupp.single F 1)) =
          Divisor.toQDivisor (N' + Finsupp.single F 1) - (Divisor.toQDivisor K + B) := by
        rw [map_add, toQDivisor_single]; abel
      rw [e]; exact hnef
  · -- the third term `ι_* ι^* 𝒪_V(M)`
    obtain ⟨m, rfl⟩ := exists_eq_add_one_of_primeDivisor sV hK.1 F
    exact isZero_rightDerived_pushforward_restriction
      (fun sW _ sV _ h1 _ _ f h2 h3 h4 K h5 B h6 h7 h8 h9 M h10 h11 i h12 =>
        ihn m (Nat.lt_succ_self m) sW sV h1 f h2 h3 h4 K h5 B h6 h7 h8 h9 M h10 h11 i h12)
      sW sV hVsm f hfs hfp hf K hK B hB hB0 hB1 hcount F hBF _ hnef i hi

end MMP.FourfoldProofs.MmpLcBpfReidFukudaProof

end

section

public section

open CategoryTheory AlgebraicGeometry

namespace MMP.Mori

/-- **Relative vanishing over the floor strata** (Reid–Fukuda type vanishing). Let `f : V ⟶ W`
be a projective birational morphism of projective varieties over an algebraically closed field
`k` of characteristic zero, with `V` smooth of dimension `n` and canonical divisor `K`, and let
`B` be a `ℚ`-divisor with snc support and coefficients in `[0, 1]` such that no stratum of `⌊B⌋`
is contained in the exceptional set of `f`. If `M` is a Cartier divisor with `M - (K + B)` nef,
then `R^i f_* 𝒪_V(M) = 0` for every `i > 0`. -/
@[mmp "lem_mmp_lc_bpf_reid_fukuda"]
public theorem isZero_rightDerived_pushforward_divisorialSheaf_of_isNef_sub_canonical_add
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {W : Scheme.{0}} (sW : W ⟶ Spec (.of k)) [IsProjectiveVariety k sW]
    {V : Scheme.{0}} (sV : V ⟶ Spec (.of k)) [IsProjectiveVariety k sV] (hVsm : IsSmoothScheme sV)
    [IsLocallyNoetherian V] [IsNormal V] (f : V ⟶ W) (hfs : f ≫ sW = sV)
    (hfp : IsProjective f) (hf : IsBirationalMorphism f)
    {n : ℕ} (K : Divisor V) (hK : K.IsCanonicalDivisor sV n)
    (B : QDivisor V) (hB : B.IsSNC sV) (hB0 : ∀ E, 0 ≤ B E) (hB1 : ∀ E, B E ≤ 1)
    (hstrata : ∀ S : Set V, Fourfold.IsSNCStratum B.roundDown S →
      ¬ S ⊆ (exceptionalSet f : Set V))
    (M : Divisor V) (hM : M.IsCartier)
    (hnef : (Divisor.toQDivisor M - (Divisor.toQDivisor K + B)).IsNef k sV)
    (i : ℕ) (hi : 0 < i) :
    Limits.IsZero (((Scheme.Modules.pushforward f).rightDerived i).obj M.divisorialSheaf) :=
  MMP.FourfoldProofs.MmpLcBpfReidFukudaProof.main n sW sV hVsm f hfs hfp hf K hK B hB hB0 hB1
    (MMP.FourfoldProofs.MmpLcBpfReidFukudaProof.card_lt_ringKrullDim_of_forall_isSNCStratum
      sV f B hB hstrata) M hM hnef i hi

end MMP.Mori

end

end
