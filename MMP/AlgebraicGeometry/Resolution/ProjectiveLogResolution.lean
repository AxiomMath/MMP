module
import StacksFrontier.AlgebraicGeometry.Limits.ChowLemmaAffineBase
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Models
import MMP.AlgebraicGeometry.Resolution.Principalization.ResolutionPrincipalization
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Resolution.OrderReduction.RegularStalkComponents
import MMP.AlgebraicGeometry.Resolution.DivisorTuple.TransformationSequence
import MMP.AlgebraicGeometry.Resolution.Blowup.SmoothGeometry
import MMP.AlgebraicGeometry.Morphisms.ChowLemma

/-!
# Projective log resolutions

Let `k` be an algebraically closed field of characteristic zero, `X` a normal variety over `k`
and `Δ` an `ℝ`-divisor on `X`. Then the pair `(X, Δ)` has a log resolution `f : Y ⟶ X` which is
a projective morphism in the sense of Hartshorne: a closed immersion into some `ℙⁿ_X` followed
by the projection.

## Main results

* `MMP.Mori.exists_isLogResolution_isProjectiveMorphism`: projective log resolutions exist.

## Implementation notes

A log resolution is `MMP.Mori.IsLogResolution`; a projective morphism is
`AlgebraicGeometry.IsProjectiveMorphism`, a closed immersion into some `ℙⁿ` over the base, as in
Hartshorne. This is the stronger of the two usual notions of projectivity, and resolution with
principalization only produces a morphism projective in the sense of EGA, so the proof runs as
follows.

1. Chow's lemma gives a variety `X₂`, quasi-projective over `k`, and a proper morphism
   `q : X₂ ⟶ X` which is an isomorphism over a dense open of `X`.
2. Let `V = V_q ∩ X_sm`, with `V_q` the biregular locus of `q`. Resolution with principalization
   of the ideal `I = q⁻¹ I_{X ∖ V} · q⁻¹ I_{Supp Δ}` on `X₂` gives `g : Y ⟶ X₂`, projective in
   the sense of EGA, with `Y` smooth, an isomorphism over `q⁻¹(V ∖ Supp Δ)`, with `I 𝒪_Y`
   invertible and `Ex(g) ∪ Supp(I 𝒪_Y)` an snc divisor, and `Ex(g)` of pure codimension one.
3. For `f = q ∘ g` one has `V ∖ Supp Δ ⊆ V_f ⊆ V`, and `Ex(f) = f⁻¹(X ∖ V) ∪ Ex(g)`. So
   `Ex(f) ∪ f⁻¹(Supp Δ) = Ex(g) ∪ Supp(I 𝒪_Y)` is an snc divisor. The ideal `q⁻¹ I_{X ∖ V} 𝒪_Y`
   is a factor of the invertible ideal `I 𝒪_Y` in the local domains of `Y`, hence invertible, so
   `f⁻¹(X ∖ V)` is of pure codimension one by Krull's principal ideal theorem, and so is `Ex(f)`.
4. `Y` is quasi-projective over `k`, being projective over the quasi-projective `X₂`; so it
   immerses into some `ℙⁿ_k`, and the proper morphism `f` is a closed immersion into `ℙⁿ_X`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Notation 0.4(10),
  Theorem 0.2
* [H. Hironaka, *Resolution of singularities of an algebraic variety over a field of
  characteristic zero*][Hir64]
* [Stacks Project, Tag 0200](https://stacks.math.columbia.edu/tag/0200)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Resolution

universe u

namespace MMP.Mori

/-! ### Topology -/

/-- A union of two closed sets of pure codimension one is of pure codimension one. -/
private theorem isPureCodimOne_sup {T : Type*} [TopologicalSpace T] {S S' : Closeds T}
    (hS : IsPureCodimOne S) (hS' : IsPureCodimOne S') : IsPureCodimOne (S ⊔ S') := by
  intro W hW
  have hsub : (W : Set T) ⊆ (S : Set T) ∪ S' := by simpa using hW.prop
  rcases (isPreirreducible_iff_isClosed_union_isClosed.1 W.isIrreducible.isPreirreducible)
    _ _ S.isClosed S'.isClosed hsub with h | h
  · exact hS W ⟨h, fun W' hW' hle => hW.2 (hW'.trans (by simp)) hle⟩
  · exact hS' W ⟨h, fun W' hW' hle => hW.2 (hW'.trans (by simp)) hle⟩

/-! ### Isomorphisms over opens and biregular loci -/

/-- The biregular locus of a morphism from a smooth scheme lies in the smooth locus. -/
private theorem biregularLocus_le_smoothLocus {k : Type u} [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (f : Y ⟶ X) [LocallyOfFiniteType (f ≫ sX)]
    (hY : IsSmoothScheme (f ≫ sX)) : biregularLocus f ≤ smoothLocus sX := by
  set V := biregularLocus f
  have : IsIso (f ∣_ V) := isBiregular_biregularLocus f
  have : LocallyOfFinitePresentation (f ≫ sX) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := f ≫ sX)).mpr inferInstance
  have : Smooth (f ≫ sX) := (isSmoothScheme_iff _).1 hY
  have h : Smooth ((f ∣_ V) ≫ V.ι ≫ sX) := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
    infer_instance
  refine le_smoothLocus _ ?_
  rw [show V.ι ≫ sX = inv (f ∣_ V) ≫ ((f ∣_ V) ≫ V.ι ≫ sX) by simp]
  infer_instance

/-- If `q` is an isomorphism over an open `V ⊆ X_sm`, then `q⁻¹ V` lies in the smooth locus of
`Y`. -/
private theorem preimage_le_smoothLocus {k : Type u} [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (q : Y ⟶ X) (V : X.Opens) [IsIso (q ∣_ V)]
    (hV : V ≤ smoothLocus sX) : q ⁻¹ᵁ V ≤ smoothLocus (q ≫ sX) := by
  have : LocallyOfFinitePresentation sX :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := sX)).mpr inferInstance
  have : Smooth (V.ι ≫ sX) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq,
      ← smoothLocus_eq_smoothLocus]
    exact top_le_iff.1 fun x _ => hV x.2
  refine le_smoothLocus _ ?_
  rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
  infer_instance

/-- For `g : Y₂ ⟶ X` with `Y₂` irreducible, the inverse image under `g ∣_ W` of `V ∩ W` is dense
in `g ⁻¹ᵁ W`, as soon as `g ⁻¹ᵁ V` is nonempty. -/
private theorem isDominant_ι_preimage_restrict {X Y₂ : Scheme.{u}} (g : Y₂ ⟶ X)
    [IrreducibleSpace Y₂] (W V : X.Opens) (hne : ((g ⁻¹ᵁ V : Y₂.Opens) : Set Y₂).Nonempty) :
    IsDominant ((g ∣_ W) ⁻¹ᵁ (W.ι ⁻¹ᵁ V)).ι := by
  constructor
  have : PreirreducibleSpace (g ⁻¹ᵁ W).toScheme := Subtype.preirreducibleSpace
    ((IrreducibleSpace.isIrreducible_univ Y₂).isPreirreducible.open_subset (g ⁻¹ᵁ W).isOpen
      (Set.subset_univ _))
  rcases isEmpty_or_nonempty (g ⁻¹ᵁ W).toScheme with _ | hN
  · exact isEmptyElim
  obtain ⟨z₀⟩ := hN
  rw [DenseRange, Scheme.Opens.range_ι]
  refine ((g ∣_ W) ⁻¹ᵁ (W.ι ⁻¹ᵁ V)).isOpen.dense ?_
  obtain ⟨y₁, hy₁⟩ := hne
  obtain ⟨y, -, hyW, hyV⟩ := (IrreducibleSpace.isIrreducible_univ Y₂).isPreirreducible _ _
    (g ⁻¹ᵁ W).isOpen (g ⁻¹ᵁ V).isOpen ⟨z₀.1, trivial, z₀.2⟩ ⟨y₁, trivial, hy₁⟩
  refine ⟨⟨y, hyW⟩, ?_⟩
  have hbase : ∀ z : (g ⁻¹ᵁ W).toScheme, W.ι ((g ∣_ W) z) = g ((g ⁻¹ᵁ W).ι z) := fun z => by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
  change W.ι ((g ∣_ W) _) ∈ V
  rw [hbase ⟨y, hyW⟩]
  exact hyV

/-- **Composing on the source does not enlarge the biregular locus.** Let `g : Y₂ ⟶ X` be
separated, with `Y₂` reduced and irreducible and `g` an isomorphism over an open with nonempty
inverse image. If `h ≫ g` is an isomorphism over `W`, so is `g`. -/
private theorem biregularLocus_comp_le {X Y Y₂ : Scheme.{u}} (h : Y ⟶ Y₂) (g : Y₂ ⟶ X)
    [IsSeparated g] [IsReduced Y₂] [IrreducibleSpace Y₂]
    (hne : ((g ⁻¹ᵁ biregularLocus g : Y₂.Opens) : Set Y₂).Nonempty) :
    biregularLocus (h ≫ g) ≤ biregularLocus g := by
  set W := biregularLocus (h ≫ g)
  have hW : IsIso ((h ≫ g) ∣_ W) := isBiregular_biregularLocus _
  refine le_biregularLocus (show IsIso (g ∣_ W) from ?_)
  rw [morphismRestrict_comp] at hW
  set a := h ∣_ g ⁻¹ᵁ W
  set b := g ∣_ W
  have : IsIso (a ≫ b) := hW
  set s := inv (a ≫ b) ≫ a with hs
  have hsb : s ≫ b = 𝟙 _ := by rw [hs, Category.assoc, IsIso.inv_hom_id]
  set W' : W.toScheme.Opens := W.ι ⁻¹ᵁ biregularLocus g
  have : IsIso (g ∣_ biregularLocus g) := isBiregular_biregularLocus g
  have : IsIso (g ∣_ W.ι ''ᵁ W') := TupleResolutionAux.isIso_restrict_of_le g
    (V := biregularLocus g) (by
      rintro _ ⟨y, hy, rfl⟩
      exact hy)
  have hc : IsIso (b ∣_ W') := ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict g W W')).2 (inferInstanceAs (IsIso (g ∣_ W.ι ''ᵁ W')))
  have : IsSeparated b := IsZariskiLocalAtTarget.restrict ‹IsSeparated g› W
  set ι := (b ⁻¹ᵁ W').ι with hι
  have : IsDominant ι := isDominant_ι_preimage_restrict g W _ hne
  have hbs : b ≫ s = 𝟙 _ := by
    refine ext_of_isDominant_of_isSeparated b
      (by rw [Category.assoc, hsb, Category.comp_id, Category.id_comp]) ι ?_
    have hrange : Set.range (ι ≫ b ≫ s) ⊆ Set.range ι := by
      rintro _ ⟨z, rfl⟩
      rw [hι, Scheme.Opens.range_ι]
      change b ((ι ≫ b ≫ s) z) ∈ W'
      rw [← Scheme.Hom.comp_apply, Category.assoc, Category.assoc, hsb, Category.comp_id]
      exact z.2
    set m := IsOpenImmersion.lift ι (ι ≫ b ≫ s) hrange
    have hm : m ≫ ι = ι ≫ b ≫ s := IsOpenImmersion.lift_fac _ _ _
    have key : ι ≫ b = (b ∣_ W') ≫ W'.ι := (morphismRestrict_ι b W').symm
    have h1 : m ≫ (b ∣_ W') = b ∣_ W' := by
      rw [← cancel_mono W'.ι, Category.assoc, ← key, ← Category.assoc, hm, Category.assoc,
        Category.assoc, hsb, Category.comp_id]
    have h2 : m = 𝟙 _ := by rw [← cancel_mono (b ∣_ W'), h1, Category.id_comp]
    rw [← hm, h2, Category.id_comp, Category.comp_id]
  exact ⟨⟨s, hbs, hsb⟩⟩

/-- If `q` is an isomorphism over `V` and the biregular locus of `g ≫ q` lies in `V`, then `g` is
an isomorphism over the inverse image of the biregular locus of `g ≫ q`. -/
private theorem preimage_biregularLocus_comp_le {W Y X : Scheme.{u}} (g : W ⟶ Y) (q : Y ⟶ X)
    (V : X.Opens) [IsIso (q ∣_ V)] (hV : biregularLocus (g ≫ q) ≤ V) :
    q ⁻¹ᵁ biregularLocus (g ≫ q) ≤ biregularLocus g := by
  set B := biregularLocus (g ≫ q)
  have h : IsIso ((g ≫ q) ∣_ B) := isBiregular_biregularLocus (g ≫ q)
  rw [morphismRestrict_comp] at h
  have : IsIso (q ∣_ B) := TupleResolutionAux.isIso_restrict_of_le q hV
  exact le_biregularLocus (@IsIso.of_isIso_comp_right _ _ _ _ _ _ (q ∣_ B) _ h)

/-- If `q` is an isomorphism over `V`, a point `y` of `Y` with `q y ∈ V` at which `g` is biregular
has `q y` in the biregular locus of `g ≫ q`. -/
private theorem mem_biregularLocus_comp {W Y X : Scheme.{u}} (g : W ⟶ Y) (q : Y ⟶ X)
    (V : X.Opens) [IsIso (q ∣_ V)] {y : Y} (hyV : q y ∈ V) (hy : y ∈ biregularLocus g) :
    q y ∈ biregularLocus (g ≫ q) := by
  set N := q ⁻¹ᵁ V
  set j : N.toScheme ⟶ X := (q ∣_ V) ≫ V.ι with hj
  have hjapp : ∀ z : N.toScheme, j z = q z.1 := fun z => by
    rw [hj, morphismRestrict_ι, Scheme.Hom.comp_apply]
    rfl
  set O : X.Opens := j ''ᵁ (N.ι ⁻¹ᵁ biregularLocus g)
  have hOV : O ≤ V := by
    rintro _ ⟨z, -, rfl⟩
    exact hjapp z ▸ z.2
  have hqO : q ⁻¹ᵁ O ≤ biregularLocus g := by
    intro y' hy'
    obtain ⟨z, hz, hzy⟩ := hy'
    have hzq : q z.1 = q y' := (hjapp z).symm.trans hzy
    have hy'N : y' ∈ N := by
      change q y' ∈ V
      rw [← hzq]
      exact z.2
    have : z = (⟨y', hy'N⟩ : N.toScheme) :=
      j.isOpenEmbedding.injective (hzy.trans (hjapp ⟨y', hy'N⟩).symm)
    rwa [this] at hz
  have : IsIso (q ∣_ O) := TupleResolutionAux.isIso_restrict_of_le q hOV
  have : IsIso (g ∣_ biregularLocus g) := isBiregular_biregularLocus g
  have : IsIso (g ∣_ q ⁻¹ᵁ O) := TupleResolutionAux.isIso_restrict_of_le g hqO
  exact le_biregularLocus (isIso_restrict_comp g q O) ⟨⟨y, hyV⟩, hy, hjapp _⟩

/-- **The exceptional set of a composite.** If `q` is an isomorphism over `V` and `g ≫ q` is
biregular only over `V`, then the exceptional set of `g ≫ q` is the inverse image of `X ∖ V`
together with the exceptional set of `g`. -/
private theorem coe_exceptionalSet_comp {W Y X : Scheme.{u}} (g : W ⟶ Y) (q : Y ⟶ X)
    (V : X.Opens) [IsIso (q ∣_ V)] (hV : biregularLocus (g ≫ q) ≤ V) :
    (exceptionalSet (g ≫ q) : Set W) = (g ≫ q) ⁻¹' (V.compl : Set X) ∪ exceptionalSet g := by
  ext y
  change q (g y) ∉ biregularLocus (g ≫ q) ↔ q (g y) ∉ V ∨ g y ∉ biregularLocus g
  refine ⟨fun hy => not_and_or.1 fun hc => hy (mem_biregularLocus_comp g q V hc.1 hc.2), ?_⟩
  rintro (hy | hy) hy'
  · exact hy (hV hy')
  · exact hy (preimage_biregularLocus_comp_le g q V hV hy')

/-- The support of the pulled-back ideal of a closed subset is its inverse image. -/
private theorem coe_support_comap_vanishingIdeal {X Y : Scheme.{u}} (q : Y ⟶ X) (Z : Closeds X) :
    (((Scheme.IdealSheafData.vanishingIdeal Z).comap q).support : Set Y) = q ⁻¹' Z := by
  rw [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage,
    Scheme.IdealSheafData.coe_support_vanishingIdeal]

/-! ### Invertible ideals -/

/-- In a local domain, a factor of a nonzero principal ideal is a nonzero principal ideal. -/
private theorem exists_eq_span_of_mul_eq_span {R : Type*} [CommRing R] [IsDomain R]
    [IsLocalRing R] {I J : Ideal R} {t : R} (ht : t ≠ 0) (h : I * J = Ideal.span {t}) :
    ∃ a : R, a ≠ 0 ∧ I = Ideal.span {a} := by
  have hmem : ∀ a ∈ I, ∀ b ∈ J, ∃ c, a * b = t * c := fun a ha b hb => by
    have : a * b ∈ Ideal.span {t} := h ▸ Ideal.mul_mem_mul ha hb
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 this
    exact ⟨c, by rw [← hc, mul_comm]⟩
  have hex : ∃ a ∈ I, ∃ b ∈ J, ∃ u : R, IsUnit u ∧ a * b = t * u := by
    by_contra hne
    push Not at hne
    have hle : I * J ≤ Ideal.span {t} * IsLocalRing.maximalIdeal R := by
      refine Ideal.mul_le.2 fun a ha b hb => ?_
      obtain ⟨c, hc⟩ := hmem a ha b hb
      have hcu : ¬ IsUnit c := fun hu => hne a ha b hb c hu hc
      rw [hc]
      exact Ideal.mem_span_singleton_mul.2 ⟨c, (IsLocalRing.mem_maximalIdeal c).2 hcu, rfl⟩
    rw [h] at hle
    obtain ⟨z, hz, htz⟩ := Ideal.mem_span_singleton_mul.1 (hle (Ideal.mem_span_singleton_self t))
    have hz1 : z = 1 := mul_left_cancel₀ ht (htz.trans (mul_one t).symm)
    exact (IsLocalRing.mem_maximalIdeal z).1 hz (hz1 ▸ isUnit_one)
  obtain ⟨a₀, ha₀, b₀, hb₀, u, hu, hab⟩ := hex
  refine ⟨a₀, fun h0 => ?_, le_antisymm (fun a ha => ?_) (Ideal.span_le.2 (by simpa using ha₀))⟩
  · rw [h0, zero_mul] at hab
    exact (mul_ne_zero ht hu.ne_zero) hab.symm
  · obtain ⟨s, hs⟩ := hmem a ha b₀ hb₀
    have h2 : a * u = a₀ * s := mul_left_cancel₀ ht (by linear_combination a₀ * hs - a * hab)
    exact Ideal.mem_span_singleton'.2
      ⟨s * ↑hu.unit⁻¹, by linear_combination a * hu.mul_val_inv - ↑hu.unit⁻¹ * h2⟩

/-- **Krull's height theorem, geometric form.** On a locally noetherian scheme, if
`closure {η}` is an irreducible component of the support of `I`, then the coheight of `η` is at
most the number of generators of `I` on any affine open containing `η`. -/
private theorem coheight_le_spanRank_ideal {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) {η : X}
    (hη : Maximal (fun s : Set X => IsIrreducible s ∧ s ⊆ (I.support : Set X)) (closure {η}))
    (W : X.affineOpens) (hηW : η ∈ W.1) :
    Order.coheight η ≤ Cardinal.toENat (Submodule.spanRank (I.ideal W)) := by
  have hW : IsAffineOpen W.1 := W.2
  have : IsNoetherianRing Γ(X, W.1) := IsLocallyNoetherian.component_noetherian W
  set x := hW.primeIdealOf ⟨η, hηW⟩
  have hx : hW.fromSpec x = η := hW.fromSpec_primeIdealOf ⟨η, hηW⟩
  have hsupp : ∀ y : Spec Γ(X, W.1),
      hW.fromSpec y ∈ (I.support : Set X) ↔ (I.ideal W : Set Γ(X, W.1)) ⊆ y.asIdeal := by
    intro y
    have hyW : hW.fromSpec y ∈ W.1 := by
      rw [← SetLike.mem_coe, ← hW.range_fromSpec]
      exact ⟨y, rfl⟩
    rw [SetLike.mem_coe, Scheme.IdealSheafData.mem_support_iff_of_mem hyW, ← Set.mem_preimage,
      hW.fromSpec_preimage_zeroLocus]
    rfl
  have hηsupp : η ∈ (I.support : Set X) := hη.prop.2 (subset_closure rfl)
  have hmin : x.asIdeal ∈ (I.ideal W).minimalPrimes := by
    refine ⟨⟨x.isPrime, (hsupp x).mp (hx ▸ hηsupp)⟩, ?_⟩
    rintro q ⟨hq, hJq⟩ hqx
    let y : Spec Γ(X, W.1) := ⟨q, hq⟩
    have hyx : y ⤳ x := (PrimeSpectrum.le_iff_specializes y x).mp hqx
    have hyη : hW.fromSpec y ⤳ η := hx ▸ hyx.map (hW.fromSpec).continuous
    have hysupp : hW.fromSpec y ∈ (I.support : Set X) := (hsupp y).mpr hJq
    have hcl : closure {hW.fromSpec y} ⊆ closure {η} := by
      refine hη.2 ⟨isIrreducible_singleton.closure, ?_⟩
        (specializes_iff_closure_subset.mp hyη)
      exact (I.support.isClosed.closure_subset_iff).mpr (Set.singleton_subset_iff.mpr hysupp)
    have hηy : η ⤳ hW.fromSpec y := specializes_iff_closure_subset.mpr hcl
    rw [← hx] at hηy
    have hxy : x ⤳ y := hW.fromSpec.isOpenEmbedding.isInducing.specializes_iff.mp hηy
    exact (PrimeSpectrum.le_iff_specializes x y).mpr hxy
  have hle := Ideal.height_le_spanRank_toENat_of_mem_minimalPrimes _ _ hmin
  rwa [idealHeight_eq_coheight _ x,
    show Order.coheight (α := Spec Γ(X, W.1)) x = Order.coheight η from
      (coheight_eq_of_isOpenImmersion (x := x) hW.fromSpec).symm.trans (congrArg _ hx)] at hle

/-- **The support of an effective Cartier divisor is of pure codimension one** (Krull's principal
ideal theorem), on an integral locally noetherian scheme, when it misses the generic point. -/
private theorem isPureCodimOne_support_of_isEffectiveCartierDivisor {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) (hgen : genericPoint X ∉ I.support) :
    IsPureCodimOne I.support := by
  intro W hW
  set η := W.isIrreducible.genericPoint
  have hηW : closure {η} = (W : Set X) := by
    have := W.isIrreducible.isGenericPoint_genericPoint_closure
    rwa [W.isClosed.closure_eq] at this
  have hWeq : W = IrreducibleCloseds.closureSingleton η :=
    IrreducibleCloseds.ext (by rw [IrreducibleCloseds.coe_closureSingleton, hηW])
  have hmax : Maximal (fun s : Set X => IsIrreducible s ∧ s ⊆ (I.support : Set X))
      (closure {η}) := by
    rw [hηW]
    refine ⟨⟨W.isIrreducible, hW.prop⟩, fun s ⟨hs, hsI⟩ hWs => ?_⟩
    have hle := hW.2 (y := ⟨closure s, hs.closure, isClosed_closure⟩)
      (closure_minimal hsI I.support.isClosed) (hWs.trans subset_closure)
    exact subset_closure.trans hle
  have hηI : η ∈ (I.support : Set X) := hmax.prop.2 (subset_closure rfl)
  rw [hWeq, Stacks.AlgebraicGeometry.CodimensionOneDivisor.codimension_closureSingleton_eq_coheight]
  obtain ⟨U, hU, hηU, f, -, hf⟩ :=
    Stacks.Divisors.exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor I hI η
  have h1 := coheight_le_spanRank_ideal I hmax ⟨U, hU⟩ hηU
  have hrank : Cardinal.toENat (Submodule.spanRank (I.ideal ⟨U, hU⟩)) ≤ 1 := by
    rw [hf]
    have := Submodule.spanRank_span_le_card (R := Γ(X, U)) ({f} : Set Γ(X, U))
    rw [Cardinal.mk_singleton] at this
    exact (Cardinal.toENat.monotone' this).trans (by simp)
  have h0 : Order.coheight η ≠ 0 := by
    intro h0
    rw [Order.coheight_eq_zero] at h0
    have hle : η ≤ genericPoint X := by
      rw [Scheme.le_iff_specializes]
      exact genericPoint_specializes η
    have h2 := h0 hle
    rw [Scheme.le_iff_specializes] at h2
    exact hgen (h2.mem_closed I.support.isClosed hηI)
  exact le_antisymm (h1.trans hrank) (Order.one_le_iff_pos.2 (pos_iff_ne_zero.2 h0))

/-- On an integral locally noetherian scheme, if `P * Q = R` stalkwise with `R` an effective
Cartier divisor, then `P` is an effective Cartier divisor. -/
private theorem isEffectiveCartierDivisor_of_stalk_mul {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] (P Q R : X.IdealSheafData)
    (hR : Stacks.Divisors.IsEffectiveCartierDivisor R)
    (h : ∀ x, IdealSheafData.stalk P x * IdealSheafData.stalk Q x = IdealSheafData.stalk R x) :
    Stacks.Divisors.IsEffectiveCartierDivisor P := by
  refine isEffectiveCartierDivisor_of_stalk_regular_principal P fun x _ => ?_
  obtain ⟨U, hU, hxU, t, ht, hRt⟩ :=
    Stacks.Divisors.exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor R hR x
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  have hstalk : IdealSheafData.stalk R x = Ideal.span {(X.presheaf.germ U x hxU).hom t} := by
    rw [IdealSheafData.stalk_eq_map_germ _ x ⟨U, hU⟩ hxU, hRt, Ideal.map_span,
      Set.image_singleton]
  have ht0 : (X.presheaf.germ U x hxU).hom t ≠ 0 := by
    intro h0
    refine ht.ne_zero (germ_injective_of_isIntegral X x hxU ?_)
    rw [h0, map_zero]
  obtain ⟨a, ha, hPa⟩ := exists_eq_span_of_mul_eq_span ht0 ((h x).trans hstalk)
  exact ⟨a, IsRegular.of_ne_zero ha, hPa⟩

/-! ### Projectivity -/

/-- A proper morphism from a scheme which immerses into some `ℙⁿ_k` over `k` is H-projective. -/
private theorem isProjectiveMorphism_of_isHQuasiProjective_comp {k : Type u} [Field k]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (f : Y ⟶ X) [IsProper f]
    (h : IsHQuasiProjective (f ≫ sX)) : IsProjectiveMorphism f := by
  obtain ⟨n, i, hi, -, hcomm⟩ := h
  have hfst : IsImmersion (Limits.pullback.lift i f hcomm ≫
      Limits.pullback.fst (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) sX) := by
    rwa [Limits.pullback.lift_fst]
  have hmid : IsImmersion (Limits.pullback.lift i f hcomm) :=
    IsImmersion.of_comp _ (Limits.pullback.fst _ _)
  have hover : (Limits.pullback.lift i f hcomm ≫ (projectiveSpaceOverBaseChangeIso n sX).hom) ≫
      (projectiveSpaceOver n X ↘ X) = f := by
    rw [Category.assoc, projectiveSpaceOverBaseChangeIso_hom_over, Limits.pullback.lift_snd]
  exact isProjectiveMorphism_of_isImmersion_projectiveSpaceOver _ hover

/-- If `g` is projective, `q` is proper and `q ≫ sX` is quasi-projective, then `g ≫ q` is
H-projective. -/
private theorem isProjectiveMorphism_comp_of_isProjective {k : Type u} [Field k]
    {X X₂ Y : Scheme.{u}} [CompactSpace X₂] [QuasiSeparatedSpace X₂] (sX : X ⟶ Spec (.of k))
    (q : X₂ ⟶ X) [IsProper q] (g : Y ⟶ X₂) (hg : AlgebraicGeometry.IsProjective g)
    (hq : IsQuasiProjective (q ≫ sX)) :
    IsProjectiveMorphism (g ≫ q) := by
  have : IsProper g := hg.isProper
  have h : IsQuasiProjective ((g ≫ q) ≫ sX) := by
    rw [Category.assoc]
    exact IsQuasiProjective.comp g (q ≫ sX) (isQuasiProjective_of_isProjective hg) hq
  exact isProjectiveMorphism_of_isHQuasiProjective_comp sX _
    (Stacks.HProjective.isHQuasiProjective_of_isQuasiProjective_of_exists_isAmple _
      (Stacks.HProjective.exists_isAmple_of_isAffine _) h)

/-! ### Chow's lemma -/

/-- **Chow's lemma for a variety.** A variety `X` over `k` admits a proper morphism `q : X₂ ⟶ X`
from a variety quasi-projective over `k` which is an isomorphism over a nonempty open. -/
private theorem exists_isQuasiProjective_isIso_restrict {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (hX : AlgebraicGeometry.IsVariety k sX) :
    ∃ (X₂ : Scheme.{u}) (q : X₂ ⟶ X) (U : X.Opens), AlgebraicGeometry.IsVariety k (q ≫ sX) ∧
      IsProper q ∧ (U : Set X).Nonempty ∧ IsIso (q ∣_ U) ∧ IsQuasiProjective (q ≫ sX) := by
  have : IsIntegral X := hX.toIsIntegral
  have := hX.toIsSeparated
  have := hX.toLocallyOfFiniteType
  have := hX.toQuasiCompact
  obtain ⟨n, X₁, p₁, i, U, hp₁, -, hi, hcomm, hdense, hiso⟩ :=
    AlgebraicGeometry.hasChowModificationIsoOnDenseOpen_of_isAffine sX
  have : IsProper p₁ := hp₁
  have : IsImmersion i := hi
  have : IsLocallyNoetherian X₁ := LocallyOfFiniteType.isLocallyNoetherian (p₁ ≫ sX)
  have : CompactSpace X₁ := QuasiCompact.compactSpace_of_compactSpace (p₁ ≫ sX)
  have : Nonempty U := hdense.nonempty.to_subtype
  have : Nonempty (p₁ ⁻¹ᵁ U) := ⟨(inv (p₁ ∣_ U)) (Classical.arbitrary U)⟩
  have : IsIntegral (p₁ ⁻¹ᵁ U) := isIntegral_of_isOpenImmersion (p₁ ∣_ U)
  have hi1 : IsIso ((p₁ ⁻¹ᵁ U).ι.imageι ∣_ (p₁ ⁻¹ᵁ U)) :=
    Stacks.SchemeTheoreticImage.isIso_imageι_restrict _
  refine ⟨(p₁ ⁻¹ᵁ U).ι.image, (p₁ ⁻¹ᵁ U).ι.imageι ≫ p₁, U, ?_, inferInstance,
    hdense.nonempty, ?_, ?_⟩
  · rw [Category.assoc]
    exact Scheme.Hom.isVariety_image k _ (p₁ ≫ sX)
  · rw [morphismRestrict_comp]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ hi1 hiso
  · refine Stacks.HProjective.isQuasiProjective_of_isHQuasiProjective _
      ⟨n, (p₁ ⁻¹ᵁ U).ι.imageι ≫ i, inferInstance, inferInstance, ?_⟩
    rw [Category.assoc, ← hcomm, Category.assoc]

/-! ### The log resolution `q ∘ g` -/

/-- If `q` is an isomorphism over `V` and `g ≫ q` is biregular only over `V`, then the exceptional
set of `g ≫ q` together with the inverse image of `Z` is the exceptional set of `g` together with
the support of the pulled-back ideal `q⁻¹ I_{X ∖ V} · q⁻¹ I_Z`. -/
private theorem exceptionalSet_comp_sup_preimage {W Y X : Scheme.{u}} (g : W ⟶ Y) (q : Y ⟶ X)
    (V : X.Opens) [IsIso (q ∣_ V)] (hV : biregularLocus (g ≫ q) ≤ V) (Z : Closeds X) :
    exceptionalSet (g ≫ q) ⊔ Z.preimage (g ≫ q).continuous = exceptionalSet g ⊔
      (((Scheme.IdealSheafData.vanishingIdeal V.compl).comap q *
        (Scheme.IdealSheafData.vanishingIdeal Z).comap q).comap g).support := by
  refine Closeds.ext ?_
  rw [Closeds.coe_sup, Closeds.coe_sup, coe_exceptionalSet_comp g q V hV,
    Scheme.IdealSheafData.support_comap]
  simp only [Closeds.coe_preimage]
  rw [Scheme.IdealSheafData.support_mul, Closeds.coe_sup, coe_support_comap_vanishingIdeal,
    coe_support_comap_vanishingIdeal]
  ext y
  simp only [Set.mem_union, Set.mem_preimage, Scheme.Hom.comp_apply]
  tauto

/-- If `q` is an isomorphism over `V ⊆ X_sm`, then `q⁻¹(V ∖ Z)` lies in the smooth locus of `X₂`
and misses the support of `q⁻¹ I_{X ∖ V} · q⁻¹ I_Z`. -/
private theorem preimage_le_smoothLocus_inf_compl_support {k : Type u} [Field k]
    {X X₂ : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (q : X₂ ⟶ X)
    (V : X.Opens) [IsIso (q ∣_ V)] (hV : V ≤ smoothLocus sX) (Z : Closeds X) :
    q ⁻¹ᵁ (V ⊓ Z.compl) ≤ smoothLocus (q ≫ sX) ⊓
      ((Scheme.IdealSheafData.vanishingIdeal V.compl).comap q *
        (Scheme.IdealSheafData.vanishingIdeal Z).comap q).support.compl := by
  refine le_inf (fun y hy => preimage_le_smoothLocus sX q V hV hy.1) fun y hy h => ?_
  have h' : y ∈ ((_ * _ : X₂.IdealSheafData).support : Set X₂) := h
  rw [Scheme.IdealSheafData.support_mul, Closeds.coe_sup, coe_support_comap_vanishingIdeal,
    coe_support_comap_vanishingIdeal] at h'
  exact h'.elim (· hy.1) hy.2

/-- If the pullback of `A * B` is an effective Cartier divisor and the generic point of `Y` misses
the support of the pullback of `A`, then this support together with a closed subset of pure
codimension one is of pure codimension one. -/
private theorem isPureCodimOne_support_comap_sup {X₂ Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] (g : Y ⟶ X₂) (A B : X₂.IdealSheafData)
    (hcart : Stacks.Divisors.IsEffectiveCartierDivisor ((A * B).comap g))
    (hgen : genericPoint Y ∉ (A.comap g).support) {E : Closeds Y} (hE : IsPureCodimOne E) :
    IsPureCodimOne ((A.comap g).support ⊔ E) :=
  isPureCodimOne_sup (isPureCodimOne_support_of_isEffectiveCartierDivisor (A.comap g)
    (isEffectiveCartierDivisor_of_stalk_mul (A.comap g) (B.comap g) ((A * B).comap g) hcart
      fun y => by
        rw [IdealSheafData.stalk_comap (A * B) g, Aux.stalk_mul, Ideal.map_mul,
          IdealSheafData.stalk_comap A g, IdealSheafData.stalk_comap B g]) hgen) hE

/-- Let `q : X₂ ⟶ X` be proper, `V = V_q ∩ X_sm` and `O = V ∖ Supp Δ` with the generic point of `X`
in `O`. If `g : Y ⟶ X₂` principalizes `q⁻¹ I_{X ∖ V} · q⁻¹ I_{Supp Δ}`, then `g ≫ q` is a log
resolution of `(X, Δ)`. -/
private theorem isLogResolution_comp_of_principalization {k : Type u} [Field k]
    {X X₂ Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k sX]
    (Δ : RDivisor X) (q : X₂ ⟶ X) [AlgebraicGeometry.IsVariety k (q ≫ sX)] [IsProper q]
    (hgenO : genericPoint X ∈ (biregularLocus q ⊓ smoothLocus sX) ⊓ Δ.supp.compl)
    (g : Y ⟶ X₂) (hYv : AlgebraicGeometry.IsVariety k (g ≫ q ≫ sX))
    (hgP : AlgebraicGeometry.IsProjective g) (hgS : IsSmoothScheme (g ≫ q ≫ sX))
    [IsIso (g ∣_ (smoothLocus (q ≫ sX) ⊓
      ((Scheme.IdealSheafData.vanishingIdeal (biregularLocus q ⊓ smoothLocus sX).compl).comap q *
        (Scheme.IdealSheafData.vanishingIdeal Δ.supp).comap q).support.compl))]
    (hcart : Stacks.Divisors.IsEffectiveCartierDivisor
      (((Scheme.IdealSheafData.vanishingIdeal (biregularLocus q ⊓ smoothLocus sX).compl).comap q *
        (Scheme.IdealSheafData.vanishingIdeal Δ.supp).comap q).comap g))
    (hsnc : IsSNCSubset (g ≫ q ≫ sX) (exceptionalSet g ⊔
      (((Scheme.IdealSheafData.vanishingIdeal (biregularLocus q ⊓ smoothLocus sX).compl).comap q *
        (Scheme.IdealSheafData.vanishingIdeal Δ.supp).comap q).comap g).support))
    (hpure : IsPureCodimOne (exceptionalSet g)) :
    IsLogResolution sX Δ (g ≫ q) := by
  have : IsIntegral X₂ := ‹AlgebraicGeometry.IsVariety k (q ≫ sX)›.toIsIntegral
  have : IsIso (q ∣_ biregularLocus q) := isBiregular_biregularLocus q
  set V : X.Opens := biregularLocus q ⊓ smoothLocus sX
  have : IsIso (q ∣_ V) := TupleResolutionAux.isIso_restrict_of_le q inf_le_left
  set O : X.Opens := V ⊓ Δ.supp.compl
  have : IsIso (q ∣_ O) :=
    TupleResolutionAux.isIso_restrict_of_le q (inf_le_left.trans inf_le_left)
  have hOne : (O : Set X).Nonempty := ⟨_, hgenO⟩
  set A : X₂.IdealSheafData := (Scheme.IdealSheafData.vanishingIdeal V.compl).comap q
  set B : X₂.IdealSheafData := (Scheme.IdealSheafData.vanishingIdeal Δ.supp).comap q
  have hAsupp : (A.support : Set X₂) = q ⁻¹' (V.compl : Set X) :=
    coe_support_comap_vanishingIdeal q _
  set f : Y ⟶ X := g ≫ q
  have : IsIntegral Y := hYv.toIsIntegral
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (g ≫ q ≫ sX)
  have hfs : f ≫ sX = g ≫ q ≫ sX := Category.assoc _ _ _
  have : IsProper g := hgP.isProper
  /- `f` is an isomorphism over `O`, and `O ⊆ V_f ⊆ V`. -/
  have : IsIso (g ∣_ q ⁻¹ᵁ O) := TupleResolutionAux.isIso_restrict_of_le g
    (preimage_le_smoothLocus_inf_compl_support sX q V inf_le_right Δ.supp)
  have hfO : IsIso (f ∣_ O) := isIso_restrict_comp g q O
  have hsm : IsSmoothScheme (f ≫ sX) := hfs ▸ hgS
  have : LocallyOfFiniteType (f ≫ sX) := by
    rw [hfs]
    infer_instance
  have hfV : biregularLocus f ≤ V := le_inf
    (biregularLocus_comp_le g q (nonempty_preimage_of_isIso_restrict q _ ⟨_, hgenO.1.1⟩))
    (biregularLocus_le_smoothLocus sX f hsm)
  set P : Y.IdealSheafData := A.comap g with hP
  have hPsupp : (P.support : Set Y) = f ⁻¹' (V.compl : Set X) := by
    rw [hP, Scheme.IdealSheafData.support_comap, Closeds.coe_preimage, hAsupp]
    rfl
  have hgenP : genericPoint Y ∉ P.support := fun h => by
    rw [← SetLike.mem_coe, hPsupp] at h
    exact h (genericPoint_mem_preimage_of_isIso_restrict f O hOne).1
  /- `Ex(f) = f⁻¹(X ∖ V) ∪ Ex(g)`. -/
  have hExeq : exceptionalSet f = P.support ⊔ exceptionalSet g :=
    Closeds.ext (by rw [Closeds.coe_sup, coe_exceptionalSet_comp g q V hfV, hPsupp])
  refine ⟨⟨inferInstance, isBirationalMorphism_of_isIso_restrict f O hOne, hsm⟩, ?_, ?_⟩
  · rw [hExeq]
    exact isPureCodimOne_support_comap_sup g A B hcart hgenP hpure
  · rwa [exceptionalSet_comp_sup_preimage g q V hfV Δ.supp, hfs]

/-! ### The theorem -/

/-- Let `X` be a normal variety over an algebraically closed field `k` of characteristic zero and
`Δ` an `ℝ`-divisor on `X`. Then `(X, Δ)` has a log resolution `f : Y ⟶ X` with `f` projective. -/
@[mmp "lem_km2c_projective_log_resolution"]
theorem exists_isLogResolution_isProjectiveMorphism {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (hX : IsNormalVariety k sX)
    (Δ : RDivisor X) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X), IsLogResolution sX Δ f ∧ IsProjectiveMorphism f := by
  obtain ⟨hXv, -⟩ := hX
  have : IsIntegral X := hXv.toIsIntegral
  /- Step 1: a quasi-projective Chow model `q : X₂ ⟶ X`. -/
  obtain ⟨X₂, q, U, hX₂, hq, hUne, hqU, hqp⟩ := exists_isQuasiProjective_isIso_restrict sX hXv
  have : IsIntegral X₂ := hX₂.toIsIntegral
  have : IsLocallyNoetherian X₂ := LocallyOfFiniteType.isLocallyNoetherian (q ≫ sX)
  have : CompactSpace X₂ := QuasiCompact.compactSpace_of_compactSpace (q ≫ sX)
  /- Step 2: the opens `V = V_q ∩ X_sm` and `O = V ∖ Supp Δ`. -/
  have : IsIso (q ∣_ biregularLocus q) := isBiregular_biregularLocus q
  set V : X.Opens := biregularLocus q ⊓ smoothLocus sX
  have : IsIso (q ∣_ V) := TupleResolutionAux.isIso_restrict_of_le q inf_le_left
  set O : X.Opens := V ⊓ Δ.supp.compl
  have : IsIso (q ∣_ O) :=
    TupleResolutionAux.isIso_restrict_of_le q (inf_le_left.trans inf_le_left)
  have : LocallyOfFinitePresentation sX :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := sX)).mpr inferInstance
  have hgenO : genericPoint X ∈ O := by
    refine ⟨⟨((genericPoint_spec X).mem_open_set_iff (biregularLocus q).isOpen).2
      (by simpa using hUne.mono (le_biregularLocus hqU)), ?_⟩,
      MMP.Fourfold.genericPoint_notMem_supp Δ⟩
    rw [smoothLocus_eq_smoothLocus]
    exact Scheme.Hom.genericPoint_mem_smoothLocus_of_perfectField sX
  /- Step 3: principalization of `q⁻¹ I_{X ∖ V} · q⁻¹ I_{Supp Δ}` on `X₂`. -/
  set A : X₂.IdealSheafData := (Scheme.IdealSheafData.vanishingIdeal V.compl).comap q
  set B : X₂.IdealSheafData := (Scheme.IdealSheafData.vanishingIdeal Δ.supp).comap q
  have hgen₂ : q (genericPoint X₂) ∈ O :=
    genericPoint_mem_preimage_of_isIso_restrict q O ⟨_, hgenO⟩
  have hK : A * B ≠ ⊥ := fun h0 =>
    (preimage_le_smoothLocus_inf_compl_support sX q V inf_le_right Δ.supp hgen₂).2
      (by rw [h0]; simp)
  obtain ⟨Y, g, hYv, hgP, -, hgS, hgiso, hcart, hsnc, hpure⟩ :=
    exists_isResolutionOfVariety_isEffectiveCartierDivisor_comap (q ≫ sX) hX₂ (A * B) hK
  exact ⟨Y, g ≫ q, isLogResolution_comp_of_principalization sX Δ q hgenO g hYv hgP hgS hcart
    hsnc hpure, isProjectiveMorphism_comp_of_isProjective sX q g hgP hqp⟩

end MMP.Mori

end
