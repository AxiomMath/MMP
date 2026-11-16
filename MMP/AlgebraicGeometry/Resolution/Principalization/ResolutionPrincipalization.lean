module

public import MMP.AlgebraicGeometry.Resolution.StrongResolution.Functorial
public import MMP.AlgebraicGeometry.Resolution.DivisorTuple.TransformationSequence
import MMP.AlgebraicGeometry.Resolution.OrderReduction.Existence
import MMP.AlgebraicGeometry.Morphisms.ValuativeCentre

/-!
# Resolution with principalization of an ideal in characteristic zero

Let `X` be a variety over a field `k` of characteristic zero and `I ⊆ 𝒪_X` a nonzero ideal sheaf
with vanishing scheme `Z`. There is a resolution `f : Y ⟶ X` (a projective birational morphism
from a smooth variety) which is an isomorphism over `X_sm ∖ Z`, such that `I 𝒪_Y` is the ideal
of an effective Cartier divisor, the union of its support with the exceptional set `Ex(f)` is an
snc divisor, and `Ex(f)` is empty or of pure codimension one.

## Main results

* `MMP.Resolution.exists_isResolutionOfVariety_isEffectiveCartierDivisor_comap`: resolution
  together with principalization of a nonzero ideal sheaf.
* `MMP.Resolution.ClosedBlowupSequence.isIso_toBase_restrict_of_disjoint_cosupport`: a smooth
  blow-up sequence of order `≥ m` for `(X, I, m, E)` is an isomorphism over every open missing
  `cosupp(I, m)`.
* `MMP.Resolution.ClosedBlowupSequence.support_orderedTotalTransform_subset`: along such a
  sequence the final boundary lies over `Supp E ∪ cosupp(I, m)`.
* `MMP.Resolution.MarkedIdeal.cosupport_one_subset_support`: `cosupp(I, 1) ⊆ Supp I`.
* `MMP.Resolution.OrderedDivisor.exists_isOrderedSNC_support_eq`: the components of an snc
  divisor, in some order, form an ordered snc divisor.
* `MMP.Resolution.isSNCSubset_of_isSNCClosedSubset`: an snc closed subset is an snc divisor in
  the sense of `MMP.Mori.IsSNCSubset`.

## Implementation notes

The morphism is the composite of three blow-up sequences: Kollár's strong resolution
`p : X₁ ⟶ X` (`MMP.Resolution.exists_strongResolution_blowupSequenceFunctor`); marked order-one
reduction `𝓑𝓜𝓞_1` of `(I 𝒪_{X₁}, 1)` with boundary `p⁻¹(Sing X)`, giving `g : X₂ ⟶ X`; and
marked order-one reduction of `(I_{Z'} 𝒪_{X₂}, 1)`, `Z'` the complement of the biregular locus of
`g`, which makes `Ex(f)` the support of an invertible ideal (of pure codimension one by Krull's
principal ideal theorem). The source applies the canonical principalization functor `𝓑𝓟^can`;
the proof uses its second part `𝓑𝓜𝓞_1` directly, because its pull-back of the ideal is the
exceptional ideal of the sequence, which places `Supp(I 𝒪_Y)` inside the final snc boundary.

The inverse image ideal sheaf `I 𝒪_Y` is `I.comap f`, the ideal of the scheme-theoretic
preimage of `Z`; its support is `f⁻¹(Z)`. "Isomorphism over `X_sm ∖ Z`" is `IsIso` of the
restriction of `f` to the open `smoothLocus sX ⊓ (I.support)ᶜ`. A coherent ideal sheaf on the
Noetherian scheme `X` is an arbitrary `Scheme.IdealSheafData`, all of which are quasi-coherent
and hence coherent here. "Projective" is projectivity in the sense of EGA II 5.5.2
(`AlgebraicGeometry.IsProjective`: proper, with a relatively ample line bundle), not the
stronger condition of being a closed subscheme of some `ℙⁿ_X`: for a variety `X` with no
nontrivial nef line bundles and a non-Cartier singular point, no resolution factors through a
closed immersion into `ℙⁿ_X` while staying an isomorphism off that point. The empty set
counts as an snc divisor and as being of pure codimension one (`MMP.Mori.IsSNCSubset`,
`MMP.Mori.IsPureCodimOne`).

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Theorems 0.2,
  0.3, Notation 0.4(10)
* [J. Kollár, *Lectures on resolution of singularities*], 3.26, 3.36, 3.69, 3.72
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori MMP.Resolution

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Resolution

/-! ### Varieties and blow-up sequences -/

/-- A variety is a disjoint union of varieties, with one component. -/
private theorem isDisjointUnionOfVarieties_of_isVariety {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [hX : AlgebraicGeometry.IsVariety k sX] :
    IsDisjointUnionOfVarieties sX := by
  haveI : IsIntegral X := hX.toIsIntegral
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, fun C hC C' hC' hne => ?_⟩
  rw [irreducibleComponents_eq_singleton] at hC hC'
  exact absurd (hC.trans hC'.symm) hne

/-- If the end result of a blow-up sequence of a variety is nonempty, it is a variety. -/
theorem ClosedBlowupSequence.isVariety_toBase {k : Type u} [Field k] :
    ∀ {X : Scheme.{u}} (B : ClosedBlowupSequence X) (sX : X ⟶ Spec (.of k)),
      AlgebraicGeometry.IsVariety k sX → Nonempty B.target →
        AlgebraicGeometry.IsVariety k (B.toBase ≫ sX)
  | X, .nil _, sX, hX, _ => by
    change AlgebraicGeometry.IsVariety k (𝟙 X ≫ sX)
    rwa [Category.id_comp]
  | X, .cons Z B, sX, hX, hne => by
    haveI := hX
    have hZ : Z ≠ ⊥ := by
      rintro rfl
      haveI := isEmpty_blowUp_bot X
      obtain ⟨y⟩ := hne
      exact isEmptyElim (B.toBase y)
    have h := (MMP.Flips.ResolutionInputs.isVariety_blowUp_and_isProjective_and_isBirational
      sX Z hZ).1
    have := ClosedBlowupSequence.isVariety_toBase B _ h hne
    change AlgebraicGeometry.IsVariety k ((B.toBase ≫ blowUpToBase Z) ≫ sX)
    rwa [Category.assoc]

/-! ### Isomorphisms over opens -/

/-- A morphism which is an isomorphism over a nonempty open has points over it. -/
theorem nonempty_preimage_of_isIso_restrict {X Y : Scheme.{u}} (g : Y ⟶ X) (V : X.Opens)
    [IsIso (g ∣_ V)] (hV : (V : Set X).Nonempty) : ((g ⁻¹ᵁ V : Y.Opens) : Set Y).Nonempty := by
  obtain ⟨x, hx⟩ := hV
  exact ⟨((inv (g ∣_ V)) ⟨x, hx⟩).1, ((inv (g ∣_ V)) ⟨x, hx⟩).2⟩

/-- The source of a morphism which is an isomorphism over a nonempty open is nonempty. -/
theorem nonempty_of_isIso_restrict {X Y : Scheme.{u}} (g : Y ⟶ X) (V : X.Opens)
    [IsIso (g ∣_ V)] (hV : (V : Set X).Nonempty) : Nonempty Y :=
  let ⟨y, _⟩ := nonempty_preimage_of_isIso_restrict g V hV; ⟨y⟩

/-- A morphism of irreducible schemes which is an isomorphism over a nonempty open is
birational. -/
theorem isBirationalMorphism_of_isIso_restrict {X Y : Scheme.{u}} [IrreducibleSpace X]
    [IrreducibleSpace Y] (g : Y ⟶ X) (V : X.Opens) [IsIso (g ∣_ V)]
    (hV : (V : Set X).Nonempty) : IsBirationalMorphism g := by
  refine MMP.Flips.isBirationalMorphism_of_isIso_resLE g _ _
    (nonempty_preimage_of_isIso_restrict g V hV) hV le_rfl ?_
  rwa [Scheme.Hom.resLE_eq_morphismRestrict]

/-- A composite of isomorphisms over `V` and over its inverse image is an isomorphism over `V`. -/
theorem isIso_restrict_comp {X Y W : Scheme.{u}} (h : W ⟶ Y) (g : Y ⟶ X) (V : X.Opens)
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
  haveI : Smooth ((f ∣_ V) ≫ V.ι ≫ sX) := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
    infer_instance
  refine le_smoothLocus _ ?_
  rw [show V.ι ≫ sX = inv (f ∣_ V) ≫ ((f ∣_ V) ≫ V.ι ≫ sX) by simp]
  infer_instance

/-- A section `s` of a separated morphism `b` which is an isomorphism over an open `W'` with
dense inverse image is an inverse of `b`. -/
theorem comp_eq_id_of_isIso_restrict_of_isDominant {X Y : Scheme.{u}} [IsReduced Y]
    (b : Y ⟶ X) [IsSeparated b] (s : X ⟶ Y) (hsb : s ≫ b = 𝟙 _) (W' : X.Opens) [IsIso (b ∣_ W')]
    [IsDominant (b ⁻¹ᵁ W').ι] : b ≫ s = 𝟙 _ := by
  set ι := (b ⁻¹ᵁ W').ι with hι
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
  haveI : IsIso (b ∣_ W') := ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict g W W')).2 (inferInstanceAs (IsIso (g ∣_ W.ι ''ᵁ W')))
  haveI : IsSeparated b := IsZariskiLocalAtTarget.restrict ‹IsSeparated g› W
  have hbase : ∀ z : (g ⁻¹ᵁ W).toScheme, W.ι (b z) = g ((g ⁻¹ᵁ W).ι z) := fun z => by
    rw [← Scheme.Hom.comp_apply, hb, morphismRestrict_ι, Scheme.Hom.comp_apply]
  haveI : IsDominant (b ⁻¹ᵁ W').ι := by
    constructor
    have hpre : IsPreirreducible ((g ⁻¹ᵁ W : Y₂.Opens) : Set Y₂) :=
      (IrreducibleSpace.isIrreducible_univ Y₂).isPreirreducible.open_subset (g ⁻¹ᵁ W).isOpen
        (Set.subset_univ _)
    haveI : PreirreducibleSpace (g ⁻¹ᵁ W).toScheme := Subtype.preirreducibleSpace hpre
    rcases isEmpty_or_nonempty (g ⁻¹ᵁ W).toScheme with hE | hN
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
  exact ⟨⟨s, comp_eq_id_of_isIso_restrict_of_isDominant b s hsb W', hsb⟩⟩

/-! ### Marked order-one reduction -/

/-- The cosupport of a marked ideal of marking one lies in the support of the ideal. -/
theorem MarkedIdeal.cosupport_one_subset_support {X : Scheme.{u}} (I : X.IdealSheafData) :
    MarkedIdeal.cosupport ⟨I, 1⟩ ⊆ (I.support : Set X) := by
  intro x hx
  change ((1 : ℕ) : ℕ∞) ≤ idealOrder (IdealSheafData.stalk I x) at hx
  by_contra h
  rw [(IdealSheafData.stalk_eq_top_iff_notMem_support _ _).2 h] at hx
  have h0 : idealOrder (⊤ : Ideal (X.presheaf.stalk x)) ≤ 0 := by
    unfold idealOrder
    refine iSup₂_le fun j hj => ?_
    rcases j with _ | j
    · simp
    · exact absurd (top_le_iff.1 (hj.trans (Ideal.pow_le_self (Nat.succ_ne_zero j))))
        (IsLocalRing.maximalIdeal.isMaximal _).ne_top
  exact absurd (hx.trans h0) (by norm_num)

/-- The centre of a blow-up along which `ord I ≥ m` lies in the cosupport of `(I, m)`. -/
theorem support_subset_cosupport_of_orderAlongGE {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) (hX : MMP.Mori.IsSmoothScheme s) (Z : X.IdealSheafData)
    (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ s)) (I : X.IdealSheafData) (m : ℕ)
    (ha : OrderAlongGE I (Z.support : Set X) m) :
    (Z.support : Set X) ⊆ MarkedIdeal.cosupport ⟨I, m⟩ := by
  intro x hx
  change (m : ℕ∞) ≤ idealOrder (IdealSheafData.stalk I x)
  refine (natCast_le_idealOrder_iff' _ _).2 <|
    (stalk_le_pow_of_orderAlongGE s hX Z hZ I m ha _).trans (Ideal.pow_right_mono ?_ _)
  exact IsLocalRing.le_maximalIdeal ((IdealSheafData.stalk_eq_top_iff_notMem_support _ _).not.2
    (not_not.2 hx))

/-- The cosupport of the first birational transform along a smooth blow-up sequence of order
`≥ m` lies over the cosupport of the marked ideal. -/
theorem ClosedBlowupSequence.cosupport_birationalTransform_subset {k : Type u} [Field k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) (a : MarkedIdeal X) (E : OrderedDivisor X)
    (Z : X.IdealSheafData) (B : ClosedBlowupSequence (blowUp Z))
    (hB : (ClosedBlowupSequence.cons Z B).IsOrderGeMarkedTripleSeq s a E) :
    (a.birationalTransform Z).cosupport ⊆ blowUpToBase Z ⁻¹' a.cosupport := by
  have h := ClosedBlowupSequence.cosupport_markedTransform_truncate_subset s a E
    (.cons Z B) hB 1
  cases B <;> exact fun y hy => by
    have h' := h hy
    simp only [ClosedBlowupSequence.toBase, Set.mem_preimage, Scheme.Hom.comp_apply] at h'
    exact h'

/-- Along a smooth blow-up sequence of order `≥ m` starting with `(X, I, m, E)`, the final
boundary lies over `Supp E ∪ cosupp(I, m)`. -/
theorem ClosedBlowupSequence.support_orderedTotalTransform_subset {k : Type u} [Field k] :
    ∀ {X : Scheme.{u}} (B : ClosedBlowupSequence X) (s : X ⟶ Spec (.of k)) (a : MarkedIdeal X)
      (E : OrderedDivisor X), B.IsOrderGeMarkedTripleSeq s a E →
      (B.orderedTotalTransform E).support ⊆ B.toBase ⁻¹' (E.support ∪ a.cosupport) := by
  intro X B
  induction B with
  | nil X =>
    intro s a E _ x hx
    exact Or.inl hx
  | @cons X Z B ih =>
    intro s a E hB x hx
    have hcos := ClosedBlowupSequence.cosupport_birationalTransform_subset s a E Z B hB
    obtain ⟨hT, hZ, -, -, hord, hB''⟩ := hB
    have hEc : IsClosed E.support := isClosed_iUnion_of_finite fun i => (E.E i).support.isClosed
    rcases ih _ _ _ hB'' hx with h | h
    · rw [OrderedDivisor.support_totalTransform E (fun i => (hT.2.2.2.2.2.2.2.1 i).2.1) Z] at h
      rcases h with h | h
      · have h' : closure (blowUpToBase Z ⁻¹' (E.support \ (Z.support : Set X))) ⊆
            blowUpToBase Z ⁻¹' E.support := closure_minimal
          (Set.preimage_mono Set.diff_subset) (hEc.preimage (blowUpToBase Z).continuous)
        exact Or.inl (h' h)
      · exact Or.inr (support_subset_cosupport_of_orderAlongGE s hT.2.1 Z hZ a.I a.m hord h)
    · exact Or.inr (hcos h)

/-- A smooth blow-up sequence of order `≥ m` starting with `(X, I, m, E)` is an isomorphism over
every open missing `cosupp(I, m)`. -/
theorem ClosedBlowupSequence.isIso_toBase_restrict_of_disjoint_cosupport {k : Type u} [Field k] :
    ∀ {X : Scheme.{u}} (B : ClosedBlowupSequence X) (s : X ⟶ Spec (.of k)) (a : MarkedIdeal X)
      (E : OrderedDivisor X), B.IsOrderGeMarkedTripleSeq s a E → ∀ W : X.Opens,
      Disjoint a.cosupport (W : Set X) → IsIso (B.toBase ∣_ W) := by
  intro X B
  induction B with
  | nil X =>
    intro s a E _ W _
    change IsIso (𝟙 X ∣_ W)
    infer_instance
  | @cons X Z B ih =>
    intro s a E hB W hW
    have hcos := ClosedBlowupSequence.cosupport_birationalTransform_subset s a E Z B hB
    obtain ⟨hT, hZ, -, -, hord, hB''⟩ := hB
    have hZW : (W : Set X) ⊆ (Z.support : Set X)ᶜ := fun x hxW hxZ =>
      hW.notMem_of_mem_right hxW
        (support_subset_cosupport_of_orderAlongGE s hT.2.1 Z hZ a.I a.m hord hxZ)
    haveI : IsIso (blowUpToBase Z ∣_ W) :=
      isIso_blowUpToBase_restrict_of_subset_compl_support Z W hZW
    haveI : IsIso (B.toBase ∣_ blowUpToBase Z ⁻¹ᵁ W) := ih _ _ _ hB'' _
      (Set.disjoint_left.2 fun y hy hyW => hW.notMem_of_mem_right hyW (hcos hy))
    exact isIso_restrict_comp B.toBase (blowUpToBase Z) W

/-- A smooth blow-up sequence of order `≥ 1` starting with `(X, I, 1, E)` is an isomorphism over
every open missing `Supp I`. -/
theorem ClosedBlowupSequence.isIso_toBase_restrict_of_disjoint_support {k : Type u} [Field k]
    {X : Scheme.{u}} (B : ClosedBlowupSequence X) (s : X ⟶ Spec (.of k)) (I : X.IdealSheafData)
    (E : OrderedDivisor X) (hB : B.IsOrderGeMarkedTripleSeq s ⟨I, 1⟩ E) (W : X.Opens)
    (hW : Disjoint (I.support : Set X) W) : IsIso (B.toBase ∣_ W) :=
  B.isIso_toBase_restrict_of_disjoint_cosupport s _ E hB W
    (hW.mono_left (MarkedIdeal.cosupport_one_subset_support I))

namespace ClosedBlowupSequence

/-- After a smooth blow-up sequence of order `≥ 1` reducing the order of `(I, 1)` below one, the
pull-back of `I` is the exceptional ideal. -/
private theorem comap_toBase_eq_exceptionalIdeal_of_maxOrder_lt_one
    {k : Type u} [Field k] {X : Scheme.{u}} (B : ClosedBlowupSequence X) (s : X ⟶ Spec (.of k))
    (I : X.IdealSheafData) (E : OrderedDivisor X) (hB : B.IsOrderGeMarkedTripleSeq s ⟨I, 1⟩ E)
    (h : maxOrder (B.markedTransform ⟨I, 1⟩).I < 1) : I.comap B.toBase = B.exceptionalIdeal := by
  rw [ClosedBlowupSequence.comap_toBase_eq_markedTransform_mul_exceptionalIdeal B s ⟨I, 1⟩ E rfl
    hB, eq_top_of_maxOrder_lt_one h, ← Scheme.IdealSheafData.one_eq_top, one_mul]

end ClosedBlowupSequence

/-! ### Krull's principal ideal theorem on schemes -/

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
    have hcl : closure {hW.fromSpec y} ⊆ closure {η} := by
      refine hη.2 ⟨isIrreducible_singleton.closure, ?_⟩
        (specializes_iff_closure_subset.mp hyη)
      exact (I.support.isClosed.closure_subset_iff).mpr
        (Set.singleton_subset_iff.mpr ((hsupp y).mpr hJq))
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

/-- On a smooth scheme with an snc divisor `F`, an ideal sheaf whose support lies in `Supp F`
has no zero stalk. -/
private theorem stalk_ne_bot_of_support_subset {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (h : MMP.Mori.IsSmoothScheme sX)
    (F : OrderedDivisor X) (hF : F.IsSNC sX) (K : X.IdealSheafData)
    (hK : (K.support : Set X) ⊆ F.support) (x : X) : IdealSheafData.stalk K x ≠ ⊥ := by
  have := Aux.smooth_of_isSmoothScheme' sX h
  have := isRegularLocalRing_stalk_of_smooth_over_field sX x
  have := IsRegularLocalRing.isDomain (X.presheaf.stalk x)
  intro h0
  let p₀ : PrimeSpectrum (X.presheaf.stalk x) := ⟨⊥, Ideal.isPrime_bot⟩
  have hξ : X.fromSpecStalk x p₀ ∈ (K.support : Set X) :=
    (fromSpecStalk_mem_support_iff_stalk_le K x p₀).2 h0.le
  obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (hK hξ)
  have hxj : x ∈ ((F.E j).support : Set X) :=
    (fromSpecStalk_specializes_self x p₀).mem_closed (F.E j).support.isClosed hj
  have hle := (fromSpecStalk_mem_support_iff_stalk_le _ x p₀).1 hj
  obtain ⟨n, z, c, hz, hc, -⟩ := hF.2 x
  rw [hc ⟨j, hxj⟩] at hle
  exact (prime_of_isRegularSystemOfParameters hz (c ⟨j, hxj⟩)).ne_zero
    (Ideal.mem_bot.1 (hle (Ideal.mem_span_singleton_self _)))

/-- On a smooth scheme with an snc divisor `F`, an ideal sheaf with principal stalks whose
support lies in `Supp F` is an effective Cartier divisor. -/
private theorem isEffectiveCartierDivisor_of_support_subset {k : Type u} [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX]
    (h : MMP.Mori.IsSmoothScheme sX) (F : OrderedDivisor X) (hF : F.IsSNC sX)
    (K : X.IdealSheafData) (hK : (K.support : Set X) ⊆ F.support)
    (hprin : ∀ x, ∃ g, IdealSheafData.stalk K x = Ideal.span {g}) :
    Stacks.Divisors.IsEffectiveCartierDivisor K := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have := Aux.smooth_of_isSmoothScheme' sX h
  refine isEffectiveCartierDivisor_of_stalk_regular_principal K fun x _ => ?_
  obtain ⟨g, hg⟩ := hprin x
  have := isRegularLocalRing_stalk_of_smooth_over_field sX x
  have := IsRegularLocalRing.isDomain (X.presheaf.stalk x)
  have hne := stalk_ne_bot_of_support_subset sX h F hF K hK x
  have hg0 : g ≠ 0 := fun h0 => hne (by rw [hg, h0, Ideal.span_singleton_eq_bot])
  exact ⟨g, IsRegular.of_ne_zero hg0, hg⟩

/-! ### Ordered snc divisors from snc closed subsets -/

/-- An empty family on a smooth scheme over a field is an snc family. -/
theorem isSNCFamily_of_isEmpty {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (hsm : IsSmoothScheme sX) {ι : Type*}
    [IsEmpty ι] (E : ι → X.IdealSheafData) : IsSNCFamily sX E := by
  have := Aux.smooth_of_isSmoothScheme' sX hsm
  refine ⟨isEmptyElim, fun x => ?_⟩
  have := isRegularLocalRing_stalk_of_smooth_over_field sX x
  obtain ⟨n, z, hz⟩ := MMP.Mori.exists_isRegularSystemOfParameters (X.presheaf.stalk x)
  exact ⟨n, z, fun i => isEmptyElim i.1, hz, fun i => isEmptyElim i.1,
    fun i => isEmptyElim i.1⟩

/-- The irreducible components of a divisor with simple normal crossings, in some order, form an
ordered snc divisor with support the divisor. -/
theorem OrderedDivisor.exists_isOrderedSNC_support_eq {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] [CompactSpace X]
    (hsm : IsSmoothScheme sX) {D : Set X} (hD : IsSNCClosedSubset sX D) :
    ∃ E : OrderedDivisor X, E.IsOrderedSNC sX ∧ E.support = D := by
  classical
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : AlgebraicGeometry.IsNoetherian X := {}
  obtain ⟨hcl, hD⟩ := hD
  obtain ⟨hfin, hcov⟩ := Aux.finite_and_cover_componentsOf hcl
  have hfam : IsSNCFamily sX (componentsFamily D) := by
    rcases hD with rfl | ⟨-, -, h⟩
    · have : IsEmpty (componentsOf (∅ : Set X)) :=
        ⟨fun W => W.2.1.1.nonempty.ne_empty (Set.subset_empty_iff.1 W.2.1.2)⟩
      exact isSNCFamily_of_isEmpty sX hsm _
    · exact h
  have : Fintype (componentsOf D) := hfin.fintype
  let e := Fintype.equivFin (componentsOf D)
  have hfam' : IsSNCFamily sX (componentsFamily D ∘ e.symm) :=
    MMP.Resolution.Internal.TupleRestrictionLift.isSNCFamily_comp hfam _ e.symm.injective
  refine ⟨⟨Fintype.card (componentsOf D), componentsFamily D ∘ e.symm⟩, ⟨fun i => ⟨(hfam'.1 i).1,
    isEffectiveCartierDivisor_of_stalk_eq_span_parameter _ fun y hy => ?_⟩, hfam'⟩, ?_⟩
  · obtain ⟨n, z, c, hz, hc, -⟩ := hfam'.2 y
    exact ⟨n, z, c ⟨i, hy⟩, hz, hc ⟨i, hy⟩⟩
  · apply Set.Subset.antisymm
    · refine Set.iUnion_subset fun i => ?_
      change ((componentsFamily D (e.symm i)).support : Set X) ⊆ D
      rw [coe_support_componentsFamily hcl]
      exact (e.symm i).2.1.2
    · intro x hx
      obtain ⟨W, hW, hxW⟩ := Set.mem_sUnion.1 (hcov hx)
      refine Set.mem_iUnion.2 ⟨e ⟨W, hW⟩, ?_⟩
      change x ∈ ((componentsFamily D (e.symm (e ⟨W, hW⟩))).support : Set X)
      rw [Equiv.symm_apply_apply, coe_support_componentsFamily hcl]
      exact hxW

/-- A member of an snc family with irreducible support is a prime divisor. -/
theorem IsSNCFamily.exists_primeDivisor {k : Type u} [Field k] {X : Scheme.{u}}
    {s : X ⟶ Spec (.of k)} {ι : Type*} {F : ι → X.IdealSheafData} (hF : IsSNCFamily s F)
    (i : ι) (hirr : IsIrreducible ((F i).support : Set X)) :
    ∃ P : MMP.Mori.PrimeDivisor X, P.idealSheaf = F i := by
  have hint := isIntegral_subscheme_of_isIrreducible s (F i) (hF.1 i).2.2 hirr
  refine ⟨⟨F i, hint, ?_⟩, rfl⟩
  have hcl := closure_subschemeι_genericPoint (F i)
  refine (hF.1 i).2.1 _ ⟨show closure _ ⊆ _ from hcl.le, fun V hV _ => ?_⟩
  exact show (V : Set X) ⊆ closure _ from hcl ▸ hV

/-- A divisor whose components are members of an snc family is snc. -/
theorem IsSNCFamily.isSNC {k : Type u} [Field k] {X : Scheme.{u}}
    {s : X ⟶ Spec (.of k)} {ι : Type*} {F : ι → X.IdealSheafData} (hF : IsSNCFamily s F)
    (D : MMP.Mori.DivisorWithCoeffs ℤ X) (hD : ∀ P ∈ D.support, ∃ i, F i = P.idealSheaf) :
    MMP.Mori.DivisorWithCoeffs.IsSNC s D := by
  choose g hg using hD
  refine ⟨fun P hP => ?_, fun x => ?_⟩
  · rw [← hg P hP]; exact (hF.1 _).2.2
  · obtain ⟨n, w, c, hw, hc, hinj⟩ := hF.2 x
    have hmem : ∀ P : {P : MMP.Mori.PrimeDivisor X // P ∈ D.support ∧ x ∈ P.support},
        x ∈ (F (g P.1 P.2.1)).support := fun P => by rw [hg]; exact P.2.2
    refine ⟨n, w, fun P => c ⟨_, hmem P⟩, hw, fun P Q hPQ => ?_, fun P => ?_⟩
    · have h : g P.1 P.2.1 = g Q.1 Q.2.1 := congrArg Subtype.val (hinj hPQ)
      have : P.1.idealSheaf = Q.1.idealSheaf := by
        rw [← hg P.1 P.2.1, ← hg Q.1 Q.2.1, h]
      exact Subtype.ext (MMP.Mori.PrimeDivisor.ext_idealSheaf this)
    · have := hc ⟨_, hmem P⟩
      rwa [hg] at this

/-- A divisor with simple normal crossings in the sense of `IsSNCClosedSubset` is one in the
sense of `MMP.Mori.IsSNCSubset`. -/
theorem isSNCSubset_of_isSNCClosedSubset {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [NoetherianSpace X] {S : Closeds X}
    (hS : IsSNCClosedSubset sX (S : Set X)) : IsSNCSubset sX S := by
  classical
  obtain ⟨-, h | ⟨-, hfin, hfam⟩⟩ := hS
  · exact Or.inl (Closeds.ext (by rw [h]; rfl))
  · right
    have : Fintype (componentsOf (S : Set X)) := hfin.fintype
    have hP : ∀ W : componentsOf (S : Set X), ∃ P : MMP.Mori.PrimeDivisor X,
        P.idealSheaf = componentsFamily (S : Set X) W := fun W =>
      IsSNCFamily.exists_primeDivisor hfam W (by
        rw [coe_support_componentsFamily S.isClosed W]; exact W.2.1.1)
    choose P hP using hP
    have hPs : ∀ W, (P W).support = (W : Set X) := fun W => by
      change ((P W).idealSheaf.support : Set X) = _
      rw [hP, coe_support_componentsFamily S.isClosed W]
    refine ⟨Finset.univ.image P, ?_, ?_⟩
    · apply Set.Subset.antisymm
      · simp only [Finset.mem_image, Finset.mem_univ, true_and, Set.iUnion_exists,
          Set.iUnion_iUnion_eq', Set.iUnion_subset_iff]
        intro W
        rw [hPs]
        exact W.2.1.2
      · intro x hx
        obtain ⟨-, hcov⟩ := Aux.finite_and_cover_componentsOf S.isClosed
        obtain ⟨W, hW, hxW⟩ := Set.mem_sUnion.1 (hcov hx)
        refine Set.mem_biUnion (x := P ⟨W, hW⟩) (Finset.mem_image_of_mem _ (Finset.mem_univ _)) ?_
        rw [hPs]
        exact hxW
    · refine IsSNCFamily.isSNC hfam _ fun Q hQ => ?_
      obtain ⟨E, hE, hQE⟩ := Finset.mem_biUnion.1 (Finsupp.support_finset_sum hQ)
      have hQ' : Q = E := Finset.mem_singleton.1 (Finsupp.support_single_subset hQE)
      obtain ⟨W, -, rfl⟩ := Finset.mem_image.1 hE
      exact ⟨W, by rw [hQ', hP]⟩

/-! ### Marked triples -/

/-- A nonempty scheme of finite type over a field has finite dimension. -/
theorem hasDimensionIn_univ_of_locallyOfFiniteType {k : Type u} [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] [QuasiCompact sY] [Nonempty Y] :
    HasDimensionIn Y Set.univ := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have htop := topologicalKrullDim_ne_top_of_locallyOfFiniteType k sY
  obtain ⟨x⟩ : Nonempty Y := inferInstance
  have : Nonempty (TopologicalSpace.IrreducibleCloseds Y) :=
    ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  have hbot : topologicalKrullDim Y ≠ ⊥ := Order.krullDim_ne_bot_iff.2 inferInstance
  generalize hd : topologicalKrullDim Y = d at htop hbot
  induction d using WithBot.recBotCoe with
  | bot => exact absurd rfl hbot
  | coe n =>
    induction n using ENat.recTopCoe with
    | top => exact absurd rfl htop
    | coe n => exact ⟨n, trivial, hd⟩

/-- On an integral scheme, an ideal sheaf whose support misses the generic point is nonzero at
the generic points. -/
theorem isNonzeroAtGenericPoints_of_genericPoint_notMem {Y : Scheme.{u}} [IsIntegral Y]
    (K : Y.IdealSheafData) (h : genericPoint Y ∉ K.support) : IsNonzeroAtGenericPoints K := by
  intro η hη
  rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hη
  have hηgen : η = genericPoint Y := (show IsGenericPoint η ⊤ from hη).eq (genericPoint_spec _)
  rw [hηgen, (IdealSheafData.stalk_eq_top_iff_notMem_support _ _).2 h]
  exact top_ne_bot

/-- On an irreducible scheme, the generic point lies over every open over which a morphism is
an isomorphism, when that open is nonempty. -/
theorem genericPoint_mem_preimage_of_isIso_restrict {X Y : Scheme.{u}} [IrreducibleSpace Y]
    (g : Y ⟶ X) (V : X.Opens) [IsIso (g ∣_ V)] (hV : (V : Set X).Nonempty) :
    genericPoint Y ∈ g ⁻¹ᵁ V :=
  ((genericPoint_spec Y).mem_open_set_iff (g ⁻¹ᵁ V).isOpen).2
    (by simpa using nonempty_preimage_of_isIso_restrict g V hV)

/-- On an irreducible scheme, the generic point misses every closed set lying outside the inverse
image of a nonempty open over which a morphism is an isomorphism. -/
theorem genericPoint_notMem_of_isIso_restrict {X Y : Scheme.{u}} [IrreducibleSpace Y]
    (g : Y ⟶ X) (V : X.Opens) [IsIso (g ∣_ V)] (hV : (V : Set X).Nonempty) {S : Closeds Y}
    (hS : (S : Set Y) ⊆ g ⁻¹' (V : Set X)ᶜ) : genericPoint Y ∉ S :=
  fun h => hS h (genericPoint_mem_preimage_of_isIso_restrict g V hV)

/-- **Resolution and principalization.** Let `X` be a variety over a field `k` of characteristic
zero and `I ≠ 0` an ideal sheaf on `X`. There is a resolution `f : Y ⟶ X` (projective
in the sense of EGA, birational, `Y` a smooth variety) which is an isomorphism over
`X_sm ∖ V(I)`, such that `I 𝒪_Y` is an effective Cartier divisor, `Ex(f) ∪ Supp(I 𝒪_Y)` is an
snc divisor, and `Ex(f)` is empty or of pure codimension one. -/
@[mmp "thm_mmp_km_resolution_principalization"]
public theorem exists_isResolutionOfVariety_isEffectiveCartierDivisor_comap {k : Type u}
    [Field k] [CharZero k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (hX : AlgebraicGeometry.IsVariety k sX) (I : X.IdealSheafData) (hI : I ≠ ⊥) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X), AlgebraicGeometry.IsVariety k (f ≫ sX) ∧
      AlgebraicGeometry.IsProjective f ∧ IsBirationalMorphism f ∧ IsSmoothScheme (f ≫ sX) ∧
      IsIso (f ∣_ (smoothLocus sX ⊓ I.support.compl)) ∧
      Stacks.Divisors.IsEffectiveCartierDivisor (I.comap f) ∧
      IsSNCSubset (f ≫ sX) (exceptionalSet f ⊔ (I.comap f).support) ∧
      IsPureCodimOne (exceptionalSet f) := by
  haveI := hX
  haveI : IsIntegral X := hX.toIsIntegral
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : AlgebraicGeometry.IsNoetherian X := {}
  obtain ⟨BR, hBR, -⟩ := MMP.Resolution.exists_strongResolution_blowupSequenceFunctor.{u}
  have hDU := isDisjointUnionOfVarieties_of_isVariety sX
  obtain ⟨hsm₁, hiso₁, hsnc₁⟩ := hBR sX hDU
  set B₁ := BR sX hDU
  set p := B₁.toBase
  haveI := hiso₁
  have hsmne : ((smoothLocus sX : X.Opens) : Set X).Nonempty := by
    rw [smoothLocus_eq_smoothLocus]
    exact (Scheme.Hom.dense_smoothLocus_of_perfectField sX).nonempty
  set U₀ : X.Opens := smoothLocus sX ⊓ I.support.compl
  have hgenI : genericPoint X ∉ (I.support : Set X) := by
    intro h
    refine hI (Scheme.IdealSheafData.support_eq_top_iff.mp (eq_top_iff.mpr fun x _ => ?_))
    exact ((genericPoint_spec X).mem_closed_set_iff I.support.isClosed).mp h (Set.mem_univ x)
  have hU₀ne : (U₀ : Set X).Nonempty := ⟨genericPoint X,
    ((genericPoint_spec X).mem_open_set_iff (smoothLocus sX).isOpen).2 (by simpa using hsmne),
    hgenI⟩
  haveI : IsIso (p ∣_ U₀) := MMP.Resolution.TupleResolutionAux.isIso_restrict_of_le p inf_le_left
  have hX₁ : AlgebraicGeometry.IsVariety k (p ≫ sX) :=
    B₁.isVariety_toBase sX hX (nonempty_of_isIso_restrict p U₀ hU₀ne)
  haveI := hX₁
  haveI : IsIntegral B₁.target := hX₁.toIsIntegral
  haveI : IsLocallyNoetherian B₁.target := LocallyOfFiniteType.isLocallyNoetherian (p ≫ sX)
  haveI : CompactSpace B₁.target := QuasiCompact.compactSpace_of_compactSpace (p ≫ sX)
  haveI : AlgebraicGeometry.IsNoetherian B₁.target := {}
  obtain ⟨E, hE, hEsupp⟩ := OrderedDivisor.exists_isOrderedSNC_support_eq (p ≫ sX) hsm₁ hsnc₁
  set J : B₁.target.IdealSheafData := I.comap p with hJ
  have hJsupp : (J.support : Set B₁.target) = p ⁻¹' (I.support : Set X) := by
    rw [hJ, Scheme.IdealSheafData.support_comap, Closeds.coe_preimage]
  have hgenJ : genericPoint B₁.target ∉ J.support :=
    genericPoint_notMem_of_isIso_restrict p U₀ hU₀ne fun y hy hyU => by
      rw [hJsupp] at hy
      exact hyU.2 hy
  obtain ⟨F, -, hFR⟩ := exists_isOrderReductionFunctorMarked_bmoFamily.{u} 1 le_rfl
  let t₁ : MarkedTriple.{u} := ⟨⟨⟨B₁.target, J, E⟩, k, p ≫ sX⟩, 1⟩
  have ht₁ : t₁ ∈ markedTriplesOfDim Set.univ 1 :=
    ⟨⟨inferInstance, hsm₁, (inferInstance : LocallyOfFiniteType (p ≫ sX)),
      (inferInstance : QuasiCompact (p ≫ sX)),
      TopologicalSpace.Equidimensional.of_preirreducibleSpace _,
      isNonzeroAtGenericPoints_of_genericPoint_notMem J hgenJ, hE⟩, rfl,
      hasDimensionIn_univ_of_locallyOfFiniteType (p ≫ sX)⟩
  set B₂ : ClosedBlowupSequence B₁.target := F.toFun t₁ ht₁
  have hB₂ : B₂.IsOrderGeMarkedTripleSeq (p ≫ sX) ⟨J, 1⟩ E := F.isOrderGeMarkedTripleSeq t₁ ht₁
  have hexc₂ : J.comap B₂.toBase = B₂.exceptionalIdeal :=
    B₂.comap_toBase_eq_exceptionalIdeal_of_maxOrder_lt_one _ _ _ hB₂ (hFR.1 t₁ ht₁)
  haveI : IsIso (B₂.toBase ∣_ p ⁻¹ᵁ U₀) :=
    B₂.isIso_toBase_restrict_of_disjoint_support _ _ _ hB₂ _
      (Set.disjoint_left.2 fun y hy hyU => by
        rw [hJsupp] at hy
        exact hyU.2 hy)
  set g : B₂.target ⟶ X := B₂.toBase ≫ p with hg
  haveI hgU₀ : IsIso (g ∣_ U₀) := isIso_restrict_comp B₂.toBase p U₀
  obtain ⟨-, hsm₂, -, -, -, -, hE₂⟩ :=
    ClosedBlowupSequence.isTriple_target_of_isOrderGeMarkedTripleSeq B₂ _ _ _ hB₂
  have hgs : g ≫ sX = B₂.toBase ≫ p ≫ sX := Category.assoc _ _ _
  have hX₂ : AlgebraicGeometry.IsVariety k (g ≫ sX) := by
    rw [hgs]
    exact ClosedBlowupSequence.isVariety_toBase B₂ _ hX₁ (nonempty_of_isIso_restrict g U₀ hU₀ne)
  haveI := hX₂
  haveI : IsIntegral B₂.target := hX₂.toIsIntegral
  haveI : IsLocallyNoetherian B₂.target := LocallyOfFiniteType.isLocallyNoetherian (g ≫ sX)
  haveI : CompactSpace B₂.target := QuasiCompact.compactSpace_of_compactSpace (g ≫ sX)
  haveI : AlgebraicGeometry.IsNoetherian B₂.target := {}
  have hgproj : AlgebraicGeometry.IsProjective g :=
    (ClosedBlowupSequence.isProjective_toBase B₂).comp (ClosedBlowupSequence.isProjective_toBase B₁)
  haveI : IsProper g := hgproj.isProper
  set V : X.Opens := biregularLocus g
  haveI : IsIso (g ∣_ V) := isBiregular_biregularLocus g
  have hU₀V : U₀ ≤ V := le_biregularLocus hgU₀
  have hVne : (V : Set X).Nonempty := hU₀ne.mono hU₀V
  set Z' : Closeds X := V.compl
  set I₃ : B₂.target.IdealSheafData := (Scheme.IdealSheafData.vanishingIdeal Z').comap g with hI₃
  have hI₃supp : (I₃.support : Set B₂.target) = g ⁻¹' (Z' : Set X) := by
    rw [hI₃, Scheme.IdealSheafData.support_comap, Closeds.coe_preimage,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
  have hgenI₃ : genericPoint B₂.target ∉ I₃.support :=
    genericPoint_notMem_of_isIso_restrict g V hVne hI₃supp.subset
  set E₂ := B₂.orderedTotalTransform E
  let t₂ : MarkedTriple.{u} := ⟨⟨⟨B₂.target, I₃, E₂⟩, k, B₂.toBase ≫ p ≫ sX⟩, 1⟩
  have ht₂ : t₂ ∈ markedTriplesOfDim Set.univ 1 :=
    ⟨⟨inferInstance, hsm₂, (hgs ▸ inferInstance : LocallyOfFiniteType (B₂.toBase ≫ p ≫ sX)),
      (hgs ▸ inferInstance : QuasiCompact (B₂.toBase ≫ p ≫ sX)),
      TopologicalSpace.Equidimensional.of_preirreducibleSpace _,
      isNonzeroAtGenericPoints_of_genericPoint_notMem I₃ hgenI₃, hE₂⟩, rfl,
      hasDimensionIn_univ_of_locallyOfFiniteType (g ≫ sX)⟩
  set B₃ : ClosedBlowupSequence B₂.target := F.toFun t₂ ht₂
  have hB₃ : B₃.IsOrderGeMarkedTripleSeq (B₂.toBase ≫ p ≫ sX) ⟨I₃, 1⟩ E₂ :=
    F.isOrderGeMarkedTripleSeq t₂ ht₂
  have hexc₃ : I₃.comap B₃.toBase = B₃.exceptionalIdeal :=
    B₃.comap_toBase_eq_exceptionalIdeal_of_maxOrder_lt_one _ _ _ hB₃ (hFR.1 t₂ ht₂)
  haveI : IsIso (B₃.toBase ∣_ g ⁻¹ᵁ V) :=
    B₃.isIso_toBase_restrict_of_disjoint_support _ _ _ hB₃ _
      (Set.disjoint_left.2 fun y hy hyV => by
        rw [hI₃supp] at hy
        exact hy hyV)
  set f : B₃.target ⟶ X := B₃.toBase ≫ g with hf
  haveI hfV : IsIso (f ∣_ V) := isIso_restrict_comp B₃.toBase g V
  haveI : IsIso (f ∣_ U₀) := MMP.Resolution.TupleResolutionAux.isIso_restrict_of_le f hU₀V
  obtain ⟨-, hsm₃, -, -, -, -, hE₃⟩ :=
    ClosedBlowupSequence.isTriple_target_of_isOrderGeMarkedTripleSeq B₃ _ _ _ hB₃
  have hfs : f ≫ sX = B₃.toBase ≫ B₂.toBase ≫ p ≫ sX := by
    simp only [hf, hg, Category.assoc]
  rw [← hfs] at hsm₃ hE₃
  have hY : AlgebraicGeometry.IsVariety k (f ≫ sX) := by
    rw [hf, Category.assoc]
    exact ClosedBlowupSequence.isVariety_toBase B₃ _ hX₂ (nonempty_of_isIso_restrict f U₀ hU₀ne)
  haveI := hY
  haveI : IsIntegral B₃.target := hY.toIsIntegral
  haveI : IsLocallyNoetherian B₃.target := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  haveI : CompactSpace B₃.target := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  haveI : AlgebraicGeometry.IsNoetherian B₃.target := {}
  have hVf : biregularLocus f = V := le_antisymm
    (biregularLocus_comp_le B₃.toBase g (nonempty_preimage_of_isIso_restrict g V hVne))
    (le_biregularLocus hfV)
  have hEx : (exceptionalSet f : Set B₃.target) = f ⁻¹' (Z' : Set X) := by
    ext y
    change f y ∉ biregularLocus f ↔ f y ∉ V
    rw [hVf]
  have hexcsupp : (B₃.exceptionalIdeal.support : Set B₃.target) = f ⁻¹' (Z' : Set X) := by
    rw [← hexc₃, Scheme.IdealSheafData.support_comap, Closeds.coe_preimage, hI₃supp]
    rfl
  set E₃ := B₃.orderedTotalTransform E₂
  have hIf : I.comap f = B₂.exceptionalIdeal.comap B₃.toBase := by
    rw [hf, hg, Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp, ← hJ, hexc₂]
  have hIfsupp : ((I.comap f).support : Set B₃.target) = f ⁻¹' (I.support : Set X) := by
    rw [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage]
  have hsing : f ⁻¹' (singularLocus sX : Set X) ⊆ exceptionalSet f := fun y hy hyV =>
    hy (biregularLocus_le_smoothLocus sX f hsm₃ hyV)
  have hS : (exceptionalSet f : Set B₃.target) ∪ ((I.comap f).support : Set B₃.target) =
      E₃.support := by
    apply Set.Subset.antisymm
    · rintro y (hy | hy)
      · rw [hEx, ← hexcsupp] at hy
        exact ClosedBlowupSequence.support_exceptionalIdeal_subset B₃ _ _ _ hB₃ hy
      · rw [hIf, Scheme.IdealSheafData.support_comap, Closeds.coe_preimage] at hy
        exact ClosedBlowupSequence.preimage_support_subset_support_orderedTotalTransform
          B₃ _ _ _ hB₃ (ClosedBlowupSequence.support_exceptionalIdeal_subset B₂ _ _ _ hB₂ hy)
    · intro y hy
      rcases ClosedBlowupSequence.support_orderedTotalTransform_subset B₃ _ _ _ hB₃ hy with h | h
      · rcases ClosedBlowupSequence.support_orderedTotalTransform_subset B₂ _ _ _ hB₂ h with h' | h'
        · left
          rw [hEsupp] at h'
          exact hsing h'
        · right
          have h'' := MarkedIdeal.cosupport_one_subset_support J h'
          rw [hJsupp] at h''
          rwa [hIfsupp]
      · left
        have h' := MarkedIdeal.cosupport_one_subset_support I₃ h
        rw [hI₃supp] at h'
        rwa [hEx]
  have hcart : ∀ K : B₃.target.IdealSheafData, (K.support : Set B₃.target) ⊆ E₃.support →
      (∀ y, ∃ a, IdealSheafData.stalk K y = Ideal.span {a}) →
      Stacks.Divisors.IsEffectiveCartierDivisor K := fun K hK hprin =>
    isEffectiveCartierDivisor_of_support_subset (f ≫ sX) hsm₃ E₃ hE₃.2 K hK hprin
  refine ⟨B₃.target, f, hY, (ClosedBlowupSequence.isProjective_toBase B₃).comp hgproj,
    isBirationalMorphism_of_isIso_restrict f U₀ hU₀ne, hsm₃, inferInstance, ?_, ?_, ?_⟩
  · refine hcart _ (fun y hy => hS ▸ Or.inr hy) fun y => ?_
    rw [hIf]
    obtain ⟨a, ha⟩ := ClosedBlowupSequence.exists_stalk_exceptionalIdeal_eq_span B₂ (B₃.toBase y)
    refine ⟨(B₃.toBase.stalkMap y).hom a, ?_⟩
    rw [IdealSheafData.stalk_comap, ha, Ideal.map_span, Set.image_singleton]
  · refine isSNCSubset_of_isSNCClosedSubset (f ≫ sX) ?_
    rw [Closeds.coe_sup, hS]
    exact hE₃.2.isSNCClosedSubset_iUnion
  · have hexcart := hcart B₃.exceptionalIdeal
      (ClosedBlowupSequence.support_exceptionalIdeal_subset B₃ _ _ _ hB₃)
      (ClosedBlowupSequence.exists_stalk_exceptionalIdeal_eq_span B₃)
    rw [show exceptionalSet f = B₃.exceptionalIdeal.support from
      Closeds.ext (hEx.trans hexcsupp.symm)]
    exact isPureCodimOne_support_of_isEffectiveCartierDivisor _ hexcart
      (genericPoint_notMem_of_isIso_restrict f V hVne hexcsupp.subset)

end MMP.Resolution

end
