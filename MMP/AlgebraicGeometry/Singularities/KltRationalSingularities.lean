module
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.Singularities
public import MMP.AlgebraicGeometry.Singularities.LogResolution.Basic
import MMP.AlgebraicGeometry.Vanishing.KltRationalSingularities
import StacksFrontier.AlgebraicGeometry.Duality.FiniteTwistedTraceComp
import MMP.AlgebraicGeometry.MMP.Models
import MMP.AlgebraicGeometry.Resolution.Principalization.ResolutionPrincipalization
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Resolution.OrderReduction.RegularStalkComponents
import MMP.AlgebraicGeometry.Resolution.DivisorTuple.TransformationSequence
import MMP.AlgebraicGeometry.Resolution.Blowup.SmoothGeometry
import MMP.AlgebraicGeometry.Morphisms.ChowLemma
import MMP.AlgebraicGeometry.Singularities.KltDiscrepancyBasics
import MMP.AlgebraicGeometry.Resolution.BlowupExceptionalAmple
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.SpreadingOut.CartesianFibres

/-!
# Klt singularities are rational: vanishing for projective resolutions

For a projective klt pair `(X, Δ)` over `ℂ` and a projective resolution `π : V ⟶ X`, we prove that
`𝒪_X ⟶ π_* 𝒪_V` is an isomorphism and `R^i π_* 𝒪_V = 0` for `i > 0`. We construct a projective log
resolution of `(X, Δ)` factoring through `π`, and use that the derived units compose to show that
the unit of `π` is a split monomorphism.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits

namespace MMP.Fold06.ThmMmpProjectiveKltResolutionVanishing

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

section LogResolution

open MMP.Mori MMP.Resolution

/-! ### Topology -/

/-- On an irreducible space, the generic point lies in every nonempty open. -/
private theorem genericPoint_mem_of_nonempty {X : Scheme.{u}} [IrreducibleSpace X] (V : X.Opens)
    (hV : (V : Set X).Nonempty) : genericPoint X ∈ V :=
  ((genericPoint_spec X).mem_open_set_iff V.isOpen).2 (by simpa using hV)

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

/-- A morphism which is an isomorphism over a nonempty open has points over it. -/
private theorem nonempty_preimage_of_isIso_restrict {X Y : Scheme.{u}} (g : Y ⟶ X) (V : X.Opens)
    [IsIso (g ∣_ V)] (hV : (V : Set X).Nonempty) : ((g ⁻¹ᵁ V : Y.Opens) : Set Y).Nonempty := by
  obtain ⟨x, hx⟩ := hV
  exact ⟨((inv (g ∣_ V)) ⟨x, hx⟩).1, ((inv (g ∣_ V)) ⟨x, hx⟩).2⟩

/-- On an irreducible scheme, the generic point lies over every nonempty open over which a
morphism is an isomorphism. -/
private theorem genericPoint_mem_preimage {X Y : Scheme.{u}} [IrreducibleSpace Y] (g : Y ⟶ X)
    (V : X.Opens) [IsIso (g ∣_ V)] (hV : (V : Set X).Nonempty) :
    genericPoint Y ∈ g ⁻¹ᵁ V :=
  genericPoint_mem_of_nonempty _ (nonempty_preimage_of_isIso_restrict g V hV)

/-- A morphism of irreducible schemes which is an isomorphism over a nonempty open is
birational. -/
private theorem isBirationalMorphism_of_isIso_restrict {X Y : Scheme.{u}} [IrreducibleSpace X]
    [IrreducibleSpace Y] (g : Y ⟶ X) (V : X.Opens) [IsIso (g ∣_ V)]
    (hV : (V : Set X).Nonempty) : IsBirationalMorphism g := by
  refine MMP.Flips.isBirationalMorphism_of_isIso_resLE g _ _
    (nonempty_preimage_of_isIso_restrict g V hV) hV le_rfl ?_
  rwa [Scheme.Hom.resLE_eq_morphismRestrict]

/-- A composite of isomorphisms over `V` and over its inverse image is an isomorphism over `V`. -/
private theorem isIso_restrict_comp {X Y W : Scheme.{u}} (h : W ⟶ Y) (g : Y ⟶ X) (V : X.Opens)
    [IsIso (g ∣_ V)] [IsIso (h ∣_ g ⁻¹ᵁ V)] : IsIso ((h ≫ g) ∣_ V) := by
  rw [morphismRestrict_comp]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ ‹_› ‹_›

/-- The biregular locus of a morphism from a smooth scheme lies in the smooth locus. -/
private theorem biregularLocus_le_smoothLocus {k : Type u} [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (f : Y ⟶ X) [LocallyOfFiniteType (f ≫ sX)]
    (hY : IsSmoothScheme (f ≫ sX)) : biregularLocus f ≤ smoothLocus sX := by
  set V := biregularLocus f
  haveI : IsIso (f ∣_ V) := isBiregular_biregularLocus f
  have : LocallyOfFinitePresentation (f ≫ sX) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := f ≫ sX)).mpr inferInstance
  haveI : Smooth (f ≫ sX) := (isSmoothScheme_iff _).1 hY
  haveI h : Smooth ((f ∣_ V) ≫ V.ι ≫ sX) := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
    infer_instance
  have e : V.ι ≫ sX = inv (f ∣_ V) ≫ ((f ∣_ V) ≫ V.ι ≫ sX) := by simp
  refine le_smoothLocus _ ?_
  rw [e]
  infer_instance

/-- The inverse image of the smooth locus under a morphism which is an isomorphism over an open
`V ⊆ X_sm` contains the inverse image of `V`. -/
private theorem preimage_le_smoothLocus {k : Type u} [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (q : Y ⟶ X) (V : X.Opens) [IsIso (q ∣_ V)]
    (hV : V ≤ smoothLocus sX) : q ⁻¹ᵁ V ≤ smoothLocus (q ≫ sX) := by
  have : LocallyOfFinitePresentation sX :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := sX)).mpr inferInstance
  haveI : Smooth (V.ι ≫ sX) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq,
      ← smoothLocus_eq_smoothLocus]
    exact top_le_iff.1 fun x _ => hV x.2
  refine le_smoothLocus _ ?_
  rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
  infer_instance

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
  set b := g ∣_ W with hb
  haveI : IsIso (a ≫ b) := hW
  set s := inv (a ≫ b) ≫ a with hs
  have hsb : s ≫ b = 𝟙 _ := by rw [hs, Category.assoc, IsIso.inv_hom_id]
  set W' : W.toScheme.Opens := W.ι ⁻¹ᵁ biregularLocus g
  haveI : IsIso (g ∣_ biregularLocus g) := isBiregular_biregularLocus g
  haveI : IsIso (g ∣_ W.ι ''ᵁ W') := MMP.Resolution.TupleResolutionAux.isIso_restrict_of_le g
    (V := biregularLocus g) (by rintro _ ⟨y, hy, rfl⟩; exact hy)
  haveI hc : IsIso (b ∣_ W') := ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict g W W')).2 (inferInstanceAs (IsIso (g ∣_ W.ι ''ᵁ W')))
  haveI : IsSeparated b := IsZariskiLocalAtTarget.restrict ‹IsSeparated g› W
  set ι := (b ⁻¹ᵁ W').ι with hι
  have hbase : ∀ z : (g ⁻¹ᵁ W).toScheme, W.ι (b z) = g ((g ⁻¹ᵁ W).ι z) := fun z => by
    rw [← Scheme.Hom.comp_apply, hb, morphismRestrict_ι, Scheme.Hom.comp_apply]
  haveI : IsDominant ι := by
    constructor
    have hpre : IsPreirreducible ((g ⁻¹ᵁ W : Y₂.Opens) : Set Y₂) :=
      (IrreducibleSpace.isIrreducible_univ Y₂).isPreirreducible.open_subset (g ⁻¹ᵁ W).isOpen
        (Set.subset_univ _)
    haveI : PreirreducibleSpace (g ⁻¹ᵁ W).toScheme := Subtype.preirreducibleSpace hpre
    rcases isEmpty_or_nonempty (g ⁻¹ᵁ W).toScheme with _ | hN
    · exact isEmptyElim
    · obtain ⟨z₀⟩ := hN
      rw [DenseRange, Scheme.Opens.range_ι]
      refine (b ⁻¹ᵁ W').isOpen.dense ?_
      obtain ⟨y₁, hy₁⟩ := hne
      obtain ⟨y, -, hyW, hyV⟩ := (IrreducibleSpace.isIrreducible_univ Y₂).isPreirreducible _ _
        (g ⁻¹ᵁ W).isOpen (g ⁻¹ᵁ biregularLocus g).isOpen ⟨z₀.1, trivial, z₀.2⟩
        ⟨y₁, trivial, hy₁⟩
      refine ⟨⟨y, hyW⟩, ?_⟩
      change W.ι (b _) ∈ biregularLocus g
      rw [hbase ⟨y, hyW⟩]
      exact hyV
  have hbs : b ≫ s = 𝟙 _ := by
    refine ext_of_isDominant_of_isSeparated b
      (by rw [Category.assoc, hsb, Category.comp_id, Category.id_comp]) ι ?_
    have hrange : Set.range (ι ≫ b ≫ s) ⊆ Set.range ι := by
      rintro _ ⟨z, rfl⟩
      rw [hι, Scheme.Opens.range_ι]
      show b ((ι ≫ b ≫ s) z) ∈ W'
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
  haveI : IsIso (q ∣_ B) := MMP.Resolution.TupleResolutionAux.isIso_restrict_of_le q hV
  haveI : IsIso (g ∣_ q ⁻¹ᵁ B) := @IsIso.of_isIso_comp_right _ _ _ _ _ _ (q ∣_ B) _ h
  exact le_biregularLocus this

/-- If `q` is an isomorphism over `V`, a point of `W` over `V` at which `g` is biregular lies over
the biregular locus of `g ≫ q`. -/
private theorem mem_biregularLocus_comp {W Y X : Scheme.{u}} (g : W ⟶ Y) (q : Y ⟶ X)
    (V : X.Opens) [IsIso (q ∣_ V)] (y : Y) (hyV : q y ∈ V) (hy : y ∈ biregularLocus g) :
    q y ∈ biregularLocus (g ≫ q) := by
  set N := q ⁻¹ᵁ V
  set j : N.toScheme ⟶ X := (q ∣_ V) ≫ V.ι with hj
  have hjapp : ∀ z : N.toScheme, j z = q z.1 := fun z => by
    rw [hj, morphismRestrict_ι, Scheme.Hom.comp_apply]
    rfl
  set O : X.Opens := j ''ᵁ (N.ι ⁻¹ᵁ biregularLocus g)
  have hOV : O ≤ V := by
    rintro _ ⟨z, -, rfl⟩
    have hz : q z.1 ∈ V := z.2
    exact Eq.mpr (congrArg (· ∈ V) (hjapp z)) hz
  have hqO : q ⁻¹ᵁ O ≤ biregularLocus g := by
    intro y' hy'
    obtain ⟨z, hz, hzy⟩ := hy'
    have hzq : q z.1 = q y' := (hjapp z).symm.trans hzy
    have hy'N : y' ∈ N := by
      show q y' ∈ V
      rw [← hzq]
      exact z.2
    have : z = (⟨y', hy'N⟩ : N.toScheme) :=
      j.isOpenEmbedding.injective (hzy.trans (hjapp ⟨y', hy'N⟩).symm)
    rw [this] at hz
    exact hz
  haveI : IsIso (q ∣_ O) := MMP.Resolution.TupleResolutionAux.isIso_restrict_of_le q hOV
  haveI : IsIso (g ∣_ biregularLocus g) := isBiregular_biregularLocus g
  haveI : IsIso (g ∣_ q ⁻¹ᵁ O) := MMP.Resolution.TupleResolutionAux.isIso_restrict_of_le g hqO
  haveI := isIso_restrict_comp g q O
  exact le_biregularLocus this ⟨⟨y, hyV⟩, hy, hjapp _⟩

/-- **The exceptional set of a composite.** If `q` is an isomorphism over `V` and `g ≫ q` is
biregular only over `V`, then the exceptional set of `g ≫ q` is the inverse image of `X ∖ V`
together with the exceptional set of `g`. -/
private theorem coe_exceptionalSet_comp {W Y X : Scheme.{u}} (g : W ⟶ Y) (q : Y ⟶ X)
    (V : X.Opens) [IsIso (q ∣_ V)] (hV : biregularLocus (g ≫ q) ≤ V) :
    (exceptionalSet (g ≫ q) : Set W) = (g ≫ q) ⁻¹' (V.compl : Set X) ∪ exceptionalSet g := by
  ext y
  change q (g y) ∉ biregularLocus (g ≫ q) ↔ q (g y) ∉ V ∨ g y ∉ biregularLocus g
  refine ⟨fun hy => ?_, ?_⟩
  · by_contra hc
    push Not at hc
    exact hy (mem_biregularLocus_comp g q V (g y) hc.1 hc.2)
  · rintro (hy | hy) hy'
    · exact hy (hV hy')
    · exact hy (preimage_biregularLocus_comp_le g q V hV hy')

/-- The support of the pulled-back ideal of a closed subset is its inverse image. -/
private theorem coe_support_comap_vanishingIdeal {X Y : Scheme.{u}} (q : Y ⟶ X) (Z : Closeds X) :
    (((Scheme.IdealSheafData.vanishingIdeal Z).comap q).support : Set Y) = q ⁻¹' Z := by
  rw [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage,
    Scheme.IdealSheafData.coe_support_vanishingIdeal]

/-- A point over `V ∖ Z` lies outside an ideal whose support is the inverse image of
`(X ∖ V) ∪ Z`. -/
private theorem notMem_support_of_mem_inf {X Y : Scheme.{u}} (q : Y ⟶ X) (V : X.Opens)
    (Z : Closeds X) (K : Y.IdealSheafData)
    (hK : (K.support : Set Y) = q ⁻¹' (V.compl : Set X) ∪ q ⁻¹' (Z : Set X)) {y : Y}
    (hy : q y ∈ V ⊓ Z.compl) : y ∉ K.support := by
  intro h
  have h' : y ∈ (K.support : Set Y) := h
  rw [hK] at h'
  rcases h' with h' | h'
  · exact h' hy.1
  · exact hy.2 h'

/-- **The exceptional set of a composite, together with a boundary.** If `q` is an isomorphism
over `V`, `g ≫ q` is biregular only over `V` and `K` has support `q⁻¹((X ∖ V) ∪ Z)`, then
`Ex(g ≫ q) ∪ (g ≫ q)⁻¹ Z = Ex(g) ∪ Supp(g⁻¹ K)`. -/
private theorem exceptionalSet_comp_sup_preimage {W Y X : Scheme.{u}} (g : W ⟶ Y) (q : Y ⟶ X)
    (V : X.Opens) [IsIso (q ∣_ V)] (hV : biregularLocus (g ≫ q) ≤ V) (Z : Closeds X)
    (K : Y.IdealSheafData)
    (hK : (K.support : Set Y) = q ⁻¹' (V.compl : Set X) ∪ q ⁻¹' (Z : Set X)) :
    exceptionalSet (g ≫ q) ⊔ Z.preimage (g ≫ q).continuous =
      exceptionalSet g ⊔ (K.comap g).support := by
  refine Closeds.ext ?_
  rw [Closeds.coe_sup, Closeds.coe_sup, coe_exceptionalSet_comp g q V hV,
    Scheme.IdealSheafData.support_comap]
  simp only [Closeds.coe_preimage]
  rw [hK]
  ext y
  simp only [Set.mem_union, Set.mem_preimage, Scheme.Hom.comp_apply]
  tauto

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
    have hz1 : z = 1 := by
      have : t * (z - 1) = 0 := by rw [mul_sub, htz, mul_one, sub_self]
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left ht)
    exact (IsLocalRing.mem_maximalIdeal z).1 hz (hz1 ▸ isUnit_one)
  obtain ⟨a₀, ha₀, b₀, hb₀, u, hu, hab⟩ := hex
  refine ⟨a₀, fun h0 => ?_, le_antisymm (fun a ha => ?_) (Ideal.span_le.2 (by simpa using ha₀))⟩
  · rw [h0, zero_mul] at hab
    exact (mul_ne_zero ht hu.ne_zero) hab.symm
  · obtain ⟨s, hs⟩ := hmem a ha b₀ hb₀
    have h2 : a * u = a₀ * s := mul_left_cancel₀ ht (by linear_combination a₀ * hs - a * hab)
    rw [Ideal.mem_span_singleton']
    refine ⟨s * ↑hu.unit⁻¹, ?_⟩
    calc s * ↑hu.unit⁻¹ * a₀ = (a₀ * s) * ↑hu.unit⁻¹ := by ring
      _ = (a * u) * ↑hu.unit⁻¹ := by rw [h2]
      _ = a := by rw [mul_assoc, IsUnit.mul_val_inv, mul_one]

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
  have hle := Ideal.height_le_spanRank_toENat_of_mem_minimal_primes _ _ hmin
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
  haveI : Nonempty U := ⟨⟨x, hxU⟩⟩
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

/-- A proper morphism `f` such that `f ≫ sX` is H-quasi-projective over `k` is projective. -/
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

/-- If `g` is projective and `q ≫ sX` is quasi-projective over a field, then the proper composite
`g ≫ q` is projective. -/
private theorem isProjectiveMorphism_comp_of_isProjective {k : Type u} [Field k]
    {X X₂ Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (g : Y ⟶ X₂) (q : X₂ ⟶ X) [IsProper q]
    [CompactSpace X₂] [QuasiSeparatedSpace X₂] (hg : IsProjective g)
    (hq : IsQuasiProjective (q ≫ sX)) : IsProjectiveMorphism (g ≫ q) := by
  haveI : IsProper g := hg.isProper
  have h : IsQuasiProjective ((g ≫ q) ≫ sX) := by
    rw [Category.assoc]
    exact IsQuasiProjective.comp g (q ≫ sX) (isQuasiProjective_of_isProjective hg) hq
  exact isProjectiveMorphism_of_isHQuasiProjective_comp sX (g ≫ q)
    (Stacks.HProjective.isHQuasiProjective_of_isQuasiProjective_of_exists_isAmple _
      (Stacks.HProjective.exists_isAmple_of_isAffine _) h)

/-- **The exceptional set of a principalized composite is of pure codimension one.** If `g ≫ q` is
biregular only over `V`, where `q` is an isomorphism, and the pull-back along `g` of an ideal `A`
with support `q⁻¹(X ∖ V)` is an effective Cartier divisor, then `Ex(g ≫ q)` is of pure
codimension one as soon as `Ex(g)` is. -/
private theorem isPureCodimOne_exceptionalSet_comp {X X₂ Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] (g : Y ⟶ X₂) (q : X₂ ⟶ X) (V : X.Opens) [IsIso (q ∣_ V)]
    (hV : biregularLocus (g ≫ q) ≤ V) (A : X₂.IdealSheafData)
    (hA : (A.support : Set X₂) = q ⁻¹' (V.compl : Set X))
    (hAc : Stacks.Divisors.IsEffectiveCartierDivisor (A.comap g))
    (hgen : (g ≫ q) (genericPoint Y) ∈ V) (hpure : IsPureCodimOne (exceptionalSet g)) :
    IsPureCodimOne (exceptionalSet (g ≫ q)) := by
  have hP : ((A.comap g).support : Set Y) = (g ≫ q) ⁻¹' (V.compl : Set X) := by
    rw [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage, hA]
    rfl
  rw [show exceptionalSet (g ≫ q) = (A.comap g).support ⊔ exceptionalSet g from
    Closeds.ext (by rw [Closeds.coe_sup, coe_exceptionalSet_comp g q V hV, hP])]
  refine isPureCodimOne_sup
    (isPureCodimOne_support_of_isEffectiveCartierDivisor _ hAc fun h => ?_) hpure
  have h' : genericPoint Y ∈ ((A.comap g).support : Set Y) := h
  rw [hP] at h'
  exact h' hgen

/-- **A principalization of the boundary gives a log resolution.** Let `q : X₂ ⟶ X` be proper and
an isomorphism over an open `V` of the smooth locus meeting `X ∖ Supp Δ`, and let `g : Y ⟶ X₂` be
a projective resolution which is an isomorphism away from the support of `A * B`, where
`Supp A = q⁻¹(X ∖ V)` and `Supp B = q⁻¹ Supp Δ`, principalizing `A * B` with snc exceptional
set. Then `g ≫ q` is a log resolution of `(X, Δ)`. -/
private theorem isLogResolution_comp_of_principalization {k : Type u} [Field k]
    {X X₂ Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] [IrreducibleSpace X]
    (Δ : RDivisor X) (q : X₂ ⟶ X) [IsProper q] [IsIntegral X₂] (V : X.Opens) [IsIso (q ∣_ V)]
    (hV : V = biregularLocus q ⊓ smoothLocus sX)
    (hO : ((V ⊓ Δ.supp.compl : X.Opens) : Set X).Nonempty) (A B : X₂.IdealSheafData)
    (hA : (A.support : Set X₂) = q ⁻¹' (V.compl : Set X))
    (hK : ((A * B).support : Set X₂) = q ⁻¹' (V.compl : Set X) ∪ q ⁻¹' (Δ.supp : Set X))
    (g : Y ⟶ X₂) (hYv : AlgebraicGeometry.IsVariety k (g ≫ q ≫ sX)) (hgP : IsProjective g)
    (hgS : IsSmoothScheme (g ≫ q ≫ sX))
    (hgiso : IsIso (g ∣_ (smoothLocus (q ≫ sX) ⊓ (A * B).support.compl)))
    (hcart : Stacks.Divisors.IsEffectiveCartierDivisor ((A * B).comap g))
    (hsnc : IsSNCSubset (g ≫ q ≫ sX) (exceptionalSet g ⊔ ((A * B).comap g).support))
    (hpure : IsPureCodimOne (exceptionalSet g)) : IsLogResolution sX Δ (g ≫ q) := by
  haveI := hYv
  haveI : IsIntegral Y := hYv.toIsIntegral
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (g ≫ q ≫ sX)
  haveI : IsProper g := hgP.isProper
  haveI : IsIso (q ∣_ biregularLocus q) := isBiregular_biregularLocus q
  set O : X.Opens := V ⊓ Δ.supp.compl
  haveI : IsIso (q ∣_ O) := MMP.Resolution.TupleResolutionAux.isIso_restrict_of_le q inf_le_left
  have hfs : (g ≫ q) ≫ sX = g ≫ q ≫ sX := Category.assoc _ _ _
  have hqOsm : q ⁻¹ᵁ O ≤ smoothLocus (q ≫ sX) ⊓ (A * B).support.compl :=
    le_inf (fun y hy => preimage_le_smoothLocus sX q V (hV.le.trans inf_le_right) hy.1)
      fun y hy => notMem_support_of_mem_inf q V Δ.supp (A * B) hK hy
  haveI := hgiso
  haveI : IsIso (g ∣_ q ⁻¹ᵁ O) := MMP.Resolution.TupleResolutionAux.isIso_restrict_of_le g hqOsm
  haveI : IsIso ((g ≫ q) ∣_ O) := isIso_restrict_comp g q O
  have hsm : IsSmoothScheme ((g ≫ q) ≫ sX) := hfs ▸ hgS
  haveI : LocallyOfFiniteType ((g ≫ q) ≫ sX) := by
    rw [hfs]
    infer_instance
  obtain ⟨x, hx⟩ := hO
  have hfV : biregularLocus (g ≫ q) ≤ V := hV ▸ le_inf
    (biregularLocus_comp_le g q
      (nonempty_preimage_of_isIso_restrict q _ ⟨x, (hV.le.trans inf_le_left) hx.1⟩))
    (biregularLocus_le_smoothLocus sX (g ≫ q) hsm)
  have hPcart : Stacks.Divisors.IsEffectiveCartierDivisor (A.comap g) :=
    isEffectiveCartierDivisor_of_stalk_mul _ (B.comap g) ((A * B).comap g) hcart fun y => by
      rw [IdealSheafData.stalk_comap (A * B) g, Aux.stalk_mul, Ideal.map_mul,
        IdealSheafData.stalk_comap A g, IdealSheafData.stalk_comap B g]
  have hgenY : (g ≫ q) (genericPoint Y) ∈ O := genericPoint_mem_preimage (g ≫ q) O ⟨x, hx⟩
  refine ⟨⟨inferInstance, isBirationalMorphism_of_isIso_restrict (g ≫ q) O ⟨x, hx⟩, hsm⟩,
    isPureCodimOne_exceptionalSet_comp g q V hfV A hA hPcart hgenY.1 hpure, ?_⟩
  rw [exceptionalSet_comp_sup_preimage g q V hfV Δ.supp (A * B) hK, hfs]
  exact hsnc

/-- **A log resolution factoring through a quasi-projective model.** Let `X` be a normal variety
over an algebraically closed field of characteristic zero, `Δ` an `ℝ`-divisor on `X` and
`q : X₂ ⟶ X` a proper morphism from a variety quasi-projective over `k` which is an isomorphism
over a nonempty open. Then there is `g : Y ⟶ X₂` with `g ≫ q` a projective log resolution of
`(X, Δ)`. -/
private theorem exists_isLogResolution_comp {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] {X X₂ : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (hX : IsNormalVariety k sX)
    (Δ : RDivisor X) (q : X₂ ⟶ X) (hX₂ : AlgebraicGeometry.IsVariety k (q ≫ sX)) [IsProper q]
    (hUne : ((biregularLocus q : X.Opens) : Set X).Nonempty) (hqp : IsQuasiProjective (q ≫ sX)) :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ X₂), IsLogResolution sX Δ (g ≫ q) ∧
      IsProjectiveMorphism (g ≫ q) := by
  obtain ⟨hXv, -⟩ := hX
  haveI := hXv
  haveI : IsIntegral X := hXv.toIsIntegral
  haveI := hX₂
  haveI : IsIntegral X₂ := hX₂.toIsIntegral
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : IsLocallyNoetherian X₂ := LocallyOfFiniteType.isLocallyNoetherian (q ≫ sX)
  haveI : CompactSpace X₂ := QuasiCompact.compactSpace_of_compactSpace (q ≫ sX)
  /- Step 2: the opens `V = V_q ∩ X_sm` and `O = V ∖ Supp Δ`. -/
  haveI : IsIso (q ∣_ biregularLocus q) := isBiregular_biregularLocus q
  set V : X.Opens := biregularLocus q ⊓ smoothLocus sX
  haveI : IsIso (q ∣_ V) := MMP.Resolution.TupleResolutionAux.isIso_restrict_of_le q inf_le_left
  set O : X.Opens := V ⊓ Δ.supp.compl
  haveI : IsIso (q ∣_ O) :=
    MMP.Resolution.TupleResolutionAux.isIso_restrict_of_le q (inf_le_left.trans inf_le_left)
  have : LocallyOfFinitePresentation sX :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := sX)).mpr inferInstance
  have hgenO : genericPoint X ∈ O := by
    refine ⟨⟨genericPoint_mem_of_nonempty _ hUne, ?_⟩, ?_⟩
    · rw [smoothLocus_eq_smoothLocus]
      exact Scheme.Hom.genericPoint_mem_smoothLocus_of_perfectField sX
    · exact MMP.Fourfold.genericPoint_notMem_supp Δ
  have hOne : (O : Set X).Nonempty := ⟨_, hgenO⟩
  /- Step 3: principalization of `q⁻¹ I_{X ∖ V} · q⁻¹ I_{Supp Δ}` on `X₂`. -/
  set A : X₂.IdealSheafData := (Scheme.IdealSheafData.vanishingIdeal V.compl).comap q
  set B : X₂.IdealSheafData := (Scheme.IdealSheafData.vanishingIdeal Δ.supp).comap q
  have hAsupp : (A.support : Set X₂) = q ⁻¹' (V.compl : Set X) :=
    coe_support_comap_vanishingIdeal q _
  have hKsupp : ((A * B).support : Set X₂) = q ⁻¹' (V.compl : Set X) ∪ q ⁻¹' (Δ.supp : Set X) := by
    rw [Scheme.IdealSheafData.support_mul, Closeds.coe_sup, hAsupp,
      coe_support_comap_vanishingIdeal]
  have hK : A * B ≠ ⊥ := fun h0 =>
    notMem_support_of_mem_inf q V Δ.supp (A * B) hKsupp (genericPoint_mem_preimage q O hOne)
      (show genericPoint X₂ ∈ ((A * B).support : Set X₂) by rw [h0]; simp)
  obtain ⟨Y, g, hYv, hgP, -, hgS, hgiso, hcart, hsnc, hpure⟩ :=
    MMP.Resolution.exists_isResolutionOfVariety_isEffectiveCartierDivisor_comap (q ≫ sX) hX₂
      (A * B) hK
  exact ⟨Y, g, isLogResolution_comp_of_principalization sX Δ q V rfl hOne A B
    hAsupp hKsupp g hYv hgP hgS hgiso hcart hsnc hpure,
    isProjectiveMorphism_comp_of_isProjective sX g q hgP hqp⟩

end LogResolution

section DerivedUnit

open Stacks.Duality
open scoped Stacks.SmallDerivedModel

/-- The map `𝒪_X[0] ⟶ f_* 𝒪_Y[0]` in the homotopy category of `𝒪_X`-modules, for a morphism of
schemes `f : Y ⟶ X`. -/
private noncomputable abbrev homotopyUnit {X Y : Scheme.{0}} (f : Y ⟶ X) :
    (HomotopyCategory.singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf) ⟶
      ((Scheme.Modules.pushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.singleFunctor Y.Modules 0).obj (SheafOfModules.unit Y.ringCatSheaf)) :=
  (HomotopyCategory.singleFunctor X.Modules 0).map
      (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
    (HomotopyCategory.quotient _ _).map
      ((HomologicalComplex.singleMapHomologicalComplex
        (Scheme.Modules.pushforward f) _ 0).inv.app _)

/-- The structural unit `𝒪_X ⟶ Rf_* 𝒪_Y` of a morphism of schemes `f : Y ⟶ X`: the unit
`𝒪_X ⟶ f_* 𝒪_Y` followed by the comparison of `f_*` with `Rf_*`. -/
private noncomputable abbrev structureUnit {X Y : Scheme.{0}} (f : Y ⟶ X) :
    (DerivedCategory.singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf) ⟶
      (derivedPushforward f).obj
        ((DerivedCategory.singleFunctor Y.Modules 0).obj (SheafOfModules.unit Y.ringCatSheaf)) :=
  (DerivedCategory.singleFunctorIsoCompQh X.Modules 0).hom.app _ ≫
    DerivedCategory.Qh.map (homotopyUnit f) ≫
    ((homotopyPushforward f).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso Y.Modules (ComplexShape.up ℤ))).app
        ((HomotopyCategory.singleFunctor Y.Modules 0).obj (SheafOfModules.unit Y.ringCatSheaf)) ≫
    (derivedPushforward f).map ((DerivedCategory.singleFunctorIsoCompQh Y.Modules 0).inv.app _)

/-- The homotopy-category units of `π`, `q` and `q ≫ π` are compatible with
`π_* ∘ q_* ≅ (q ≫ π)_*`. -/
private theorem homotopyUnit_comp {X V W : Scheme.{0}} (q : W ⟶ V) (π : V ⟶ X) :
    homotopyUnit π ≫ ((Scheme.Modules.pushforward π).mapHomotopyCategory
        (ComplexShape.up ℤ)).map (homotopyUnit q) =
      homotopyUnit (q ≫ π) ≫ (Functor.mapHomotopyCategoryCompIso
        (Scheme.Modules.pushforwardComp q π) (ComplexShape.up ℤ)).inv.app
          ((HomotopyCategory.singleFunctor W.Modules 0).obj
            (SheafOfModules.unit W.ringCatSheaf)) := by
  have h1 : ∀ {Y Z : Scheme.{0}} (f : Y ⟶ Z), homotopyUnit f =
      (HomotopyCategory.quotient _ _).map
        ((HomologicalComplex.single Z.Modules (ComplexShape.up ℤ) 0).map
            (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
          (HomologicalComplex.singleMapHomologicalComplex (Scheme.Modules.pushforward f)
            (ComplexShape.up ℤ) 0).inv.app (SheafOfModules.unit Y.ringCatSheaf)) := by
    intro Y Z f
    exact ((HomotopyCategory.quotient Z.Modules (ComplexShape.up ℤ)).map_comp _ _).symm
  have h3 : (Functor.mapHomotopyCategoryCompIso (Scheme.Modules.pushforwardComp q π)
      (ComplexShape.up ℤ)).inv.app
        ((HomotopyCategory.singleFunctor W.Modules 0).obj (SheafOfModules.unit W.ringCatSheaf)) =
      (HomotopyCategory.quotient _ _).map
        ((Functor.mapHomologicalComplexCompIso (Scheme.Modules.pushforwardComp q π)
          (ComplexShape.up ℤ)).inv.app
          ((HomologicalComplex.single W.Modules (ComplexShape.up ℤ) 0).obj
            (SheafOfModules.unit W.ringCatSheaf))) := rfl
  erw [h1, h1, h1, h3, Functor.mapHomotopyCategory_map, ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  refine HomologicalComplex.from_single_hom_ext ?_
  ext U x
  rfl

/-- **The structural units compose**: under `Rπ_* ∘ Rq_* ≅ R(q ≫ π)_*`, the unit of `q ≫ π` is the
unit of `π` followed by `Rπ_*` of the unit of `q`. -/
private theorem structureUnit_comp {X V W : Scheme.{0}} (q : W ⟶ V) (π : V ⟶ X) :
    structureUnit π ≫ (derivedPushforward π).map (structureUnit q) ≫
        (derivedPushforwardCompIso q π).hom.app _ = structureUnit (q ≫ π) := by
  set K := (HomotopyCategory.singleFunctor W.Modules 0).obj (SheafOfModules.unit W.ringCatSheaf)
  have key := derivedPushforwardUnit_comp_derivedPushforwardCompIso_hom q π K
  have hnat := (Stacks.Duality.derivedPushforwardUnit π).naturality (homotopyUnit q)
  have hcomp := (derivedPushforwardCompIso q π).hom.naturality
    ((DerivedCategory.singleFunctorIsoCompQh W.Modules 0).inv.app
      (SheafOfModules.unit W.ringCatSheaf))
  have hH := congrArg DerivedCategory.Qh.map (homotopyUnit_comp q π)
  simp only [Functor.map_comp] at hH
  simp only [structureUnit, Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc (derivedPushforward π)]
  erw [Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp, ← reassoc_of% hnat,
    hcomp, reassoc_of% hH]
  simp only [Category.assoc] at key
  erw [reassoc_of% key]

/-- If the structural unit of `g ≫ π` is invertible, the structural unit of `π` is a split
monomorphism: a left inverse is `Rπ_*(u_g)` followed by the inverse of `u_{g ≫ π}`. -/
private theorem isSplitMono_structureUnit_of_isIso_comp {X V W : Scheme.{0}} (g : W ⟶ V)
    (π : V ⟶ X) [IsIso (structureUnit (g ≫ π))] : IsSplitMono (structureUnit π) := by
  refine IsSplitMono.mk' ⟨(derivedPushforward π).map (structureUnit g) ≫
    (derivedPushforwardCompIso g π).hom.app _ ≫ inv (structureUnit (g ≫ π)), ?_⟩
  rw [← Category.assoc, ← Category.assoc, Category.assoc (structureUnit π),
    structureUnit_comp, IsIso.hom_inv_id]

end DerivedUnit

end MMP.Fold06.ThmMmpProjectiveKltResolutionVanishing

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori
open scoped Stacks.SmallDerivedModel

variable {X V : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)} {Δ : QDivisor X} {π : V ⟶ X}

/-- **Vanishing for every projective resolution of a projective klt pair.** Let `(X, Δ)` be an
effective klt pair with rational boundary on a normal projective complex variety and
`π : V ⟶ X` a projective birational morphism with `V` smooth. Then the canonical map
`𝒪_X ⟶ π_* 𝒪_V` is an isomorphism and `R^i π_* 𝒪_V = 0` for every `i > 0`; that is,
`𝒪_X ⟶ Rπ_* 𝒪_V` is an isomorphism. -/
@[mmp "thm_mmp_projective_klt_resolution_vanishing"]
public theorem IsKltPair.isIso_unitToPushforwardObjUnit_and_isZero_rightDerived
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hΔ : IsKltPair sX Δ)
    (hπ : MMP.Intersection.IsResolution sX π) :
    IsIso (SheafOfModules.unitToPushforwardObjUnit π.toRingCatSheafHom) ∧
      ∀ i : ℕ, 0 < i → IsZero (((Scheme.Modules.pushforward π).rightDerived i).obj
        (SheafOfModules.unit V.ringCatSheaf)) := by
  obtain ⟨hXv, hVv, hVsm, hπp, hπb⟩ := hπ
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sX := hX
  haveI := hVv
  haveI : IsIntegral V := hVv.toIsIntegral
  haveI : IsProper π := isProper_of_isProjectiveMorphism π hπp
  obtain ⟨-, -, hPair, hnonneg⟩ := hΔ.1
  obtain ⟨hXn, n, K, hK, -⟩ := hPair
  have hklt : MMP.Mori.IsKltPair sX n K Δ :=
    (MMP.Fourfold.isKltPair_iff_mori_isKltPair sX hK hΔ.1).1 hΔ
  have hdim : topologicalKrullDim X = n := hK.topologicalKrullDim_eq
  /- A projective log resolution `g ≫ π` of `(X, Δ)`. -/
  haveI : IsIso (π ∣_ biregularLocus π) := isBiregular_biregularLocus π
  have hUne : ((biregularLocus π : X.Opens) : Set X).Nonempty := by
    refine ⟨genericPoint X,
      MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal π hπb ?_⟩
    rw [Order.coheight_eq_zero.mpr fun y _ => by
      rw [Scheme.le_iff_specializes]; exact genericPoint_specializes y]
    exact zero_le_one
  have hVp : IsProjectiveMorphism (π ≫ sX) := hπp.comp hX.isProjective
  have hqp : IsQuasiProjective (π ≫ sX) :=
    Stacks.HProjective.isQuasiProjective_of_isHQuasiProjective _ hVp.isHQuasiProjective
  obtain ⟨W, g, hlog, hfp⟩ :=
    MMP.Fold06.ThmMmpProjectiveKltResolutionVanishing.exists_isLogResolution_comp sX hXn
      (QDivisor.toRDivisor Δ) π hVv hUne hqp
  /- The unit of `g ≫ π` is invertible, so the unit of `π` is a split monomorphism. -/
  haveI : IsIso (MMP.Fold06.ThmMmpProjectiveKltResolutionVanishing.structureUnit (g ≫ π)) :=
    MMP.Duality.isIso_unit_of_isKltPair_of_isLogResolution sX hklt hnonneg (g ≫ π) hlog hfp
  have hsplit :=
    MMP.Fold06.ThmMmpProjectiveKltResolutionVanishing.isSplitMono_structureUnit_of_isIso_comp g π
  /- The split-unit criterion for `π`. -/
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ (π ≫ sX) := ⟨hVp⟩
  haveI : IsNormal V := MMP.Mori.IsSmoothResolution.isNormal (sX := sX) ⟨inferInstance, hπb, hVsm⟩
  haveI : LocallyOfFinitePresentation (π ≫ sX) :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  haveI : Smooth (π ≫ sX) := (MMP.Mori.isSmoothScheme_iff _).mp hVsm
  have hdimV : topologicalKrullDim V = n :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (π ≫ sX) hπb).symm.trans
      hdim
  haveI : SmoothOfRelativeDimension n (π ≫ sX) :=
    MMP.Intersection.smoothOfRelativeDimension_of_isVariety (π ≫ sX) n hdimV
  obtain ⟨-, hvan⟩ := MMP.Duality.isIso_unit_of_isSplitMono sX (π ≫ sX) π n hdim rfl hπp hπb hsplit
  refine ⟨?_, fun i hi => ?_⟩
  · /- Degree zero: `π_* 𝒪_V = 𝒪_X`, `π` being proper birational onto the normal `X`. -/
    refine isIso_unitToPushforwardObjUnit_of_isIso_c π ?_
    haveI : ∀ U, IsIso (π.c.app U) := fun U =>
      MMP.Mori.isIso_app_of_isProper_of_isBirationalMorphism (π ≫ sX) sX hVv ⟨hXv, inferInstance⟩
        π hπb U.unop
    exact NatIso.isIso_of_isIso_app _
  · /- Positive degrees: the cohomology sheaves of `Rπ_* 𝒪_V` are the higher direct images. -/
    exact ((Stacks.Duality.DerivedPushforward.singleCompDerivedPushforwardHomologyIso π 0 i i
      (by simp)).app (SheafOfModules.unit V.ringCatSheaf)).isZero_iff.mp
        (hvan i (by exact_mod_cast hi))

end MMP.Fourfold
