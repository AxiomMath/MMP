module
public import MMP.Attr
public import MMP.AlgebraicGeometry.Resolution.Basic
public import MMP.AlgebraicGeometry.Resolution.BlowupSequence
public import MMP.AlgebraicGeometry.Morphisms.Birational.RationalMap
import MMP.AlgebraicGeometry.Resolution.StrongResolution.Functorial
import MMP.AlgebraicGeometry.Resolution.DivisorTuple.SncResolution
import MMP.AlgebraicGeometry.Morphisms.ValuativeCentre
import MMP.AlgebraicGeometry.Resolution.OrderReduction.OrderMSequenceCosupport
import MMP.AlgebraicGeometry.Morphisms.ProjectiveFieldExtension
import MMP.AlgebraicGeometry.Resolution.Blowup.VarietyProjective
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.OrderOnePullback
import MMP.AlgebraicGeometry.Resolution.OneBlowupTotalTransform
import MMP.AlgebraicGeometry.Resolution.SNCPullback
import MMP.AlgebraicGeometry.Resolution.DivisorialPart
import MMP.AlgebraicGeometry.Divisor.SectionAlgebra.Cartier
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Resolution.OrderReduction.Existence

/-!
# Log resolutions preserving the simple normal crossing locus

Let `k` be a field of characteristic zero, `X` a normal variety over `k` and `D` a reduced Weil
divisor on `X`, that is, a finite set of prime divisors `D₁, …, D_r` (the divisor
`D₁ + ⋯ + D_r`). There is a projective birational morphism `f : Y ⟶ X` from a variety `Y` smooth
over `k` whose exceptional set `Ex(f)` is of pure codimension one, such that `Ex(f) ∪ f⁻¹(Supp D)`
is a divisor with simple normal crossings, and which is an isomorphism over every open `U ⊆ X`
which is smooth over `k` and on which `D ∩ U` is a divisor with simple normal crossings.

The morphism is the composite of three blow-up sequences.

1. Kollár's strong resolution `f₁ : X₁ ⟶ X`: `X₁` is smooth and `f₁` is an isomorphism over the
   smooth locus `X^ns` of `X`.
2. On `X₁`, the strict transforms of the `Dⱼ` are prime divisors; their ideals, together with the
   empty boundary, form an ordered divisor tuple whose snc locus contains `f₁⁻¹(U)` for every
   open `U` as above. The snc-preserving resolution of ordered divisor tuples gives
   `f₂ : X₂ ⟶ X₁`, an isomorphism over a neighbourhood of that snc locus, after which the tuple
   is snc everywhere. Its centres lie over the support of the tuple, so the support of the final
   tuple is `(f₁f₂)⁻¹` of the support of the first one.
3. Let `Z ⊆ X` be the complement of the biregular locus of `g = f₁f₂`; as `X` is normal, it has
   codimension at least two. Marked order-one reduction of `(I_Z 𝒪_{X₂}, 1)`, with the entries
   of the final tuple as ordered boundary, gives `f₃ : Y ⟶ X₂` whose centres lie over `Z`, with
   `f₃^*(I_Z 𝒪_{X₂})` the exceptional ideal of the sequence and the final boundary snc.

Then `f = f₃f₂f₁` is an isomorphism over `X ∖ Z`; conversely every point of `f⁻¹(Z)` is a
specialization of a point of codimension at most one of `f⁻¹(Z)` (Krull's principal ideal
theorem for the invertible ideal `f^* I_Z`), which cannot lie over the biregular locus of `f`
since `Z` has codimension `≥ 2`. Hence `Ex(f) = f⁻¹(Z)`, of pure codimension one, and
`Ex(f) ∪ f⁻¹(Supp D)` is the support of the final snc boundary.

## Main results

* `MMP.Resolution.exists_isLogResolution_isIso_restrict_of_isSNCClosedSubset`: existence of a
  projective log resolution of `(X, D)` which is an isomorphism over the snc locus of `(X, D)`.

## Implementation notes

"Projective" is projectivity in the sense of EGA II (Stacks, Tag 01W8): `f` is proper and
carries an `f`-ample line bundle, which is what `IsResolutionOfVariety` asks
(`AlgebraicGeometry.IsProjective f`), and what every composite of blow-ups satisfies. The
stronger requirement of a closed immersion `Y ⟶ ℙᴺ_X` would make the statement false: on a
complete toric threefold with a single non-smooth point and no nontrivial nef line bundles, such
an `f` that is an isomorphism over the smooth locus is forced to be an isomorphism.

The union `Ex(f) ∪ f⁻¹_* D` of the exceptional set and the strict transform of `D` is written
`Ex(f) ∪ f⁻¹(Supp D)`: the two closed sets agree, since `f⁻¹(Supp D) ∖ Ex(f)` is dense in the
strict transform and its closure is contained in `f⁻¹(Supp D)`.

"An isomorphism over the locus where `X` is smooth and `D` has simple normal crossings" is
stated for every open `U ⊆ X` with `U` smooth over `k` and `D ∩ U` snc in `U`; that locus is the
union of these opens, and isomorphy over an open is local on it.

The strict transforms of the components of `D` on `X₁` enter the tuple as its ideals, the
boundary of the tuple being empty: the inverse image of the singular locus need not be part of
the tuple, since it lies over `Z` and is taken care of by the third step. The auxiliary lemmas of
the proof live in the namespace `Proof_thm_mmp_snc_preserving_log_resolution`.

## References

* [J. Kollár, *Lectures on resolution of singularities*, Thm. 3.36, Def. 3.24, Thm. 3.69, 3.72]
* [J. Kollár, *Semi log resolutions*, arXiv:0812.3592, Proposition 6]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori MMP.Resolution

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace Proof_thm_mmp_snc_preserving_log_resolution

/-! ### Varieties and blow-up sequences -/

/-- A variety is a disjoint union of varieties. -/
private theorem isDisjointUnionOfVarieties_of_isVariety {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (hX : AlgebraicGeometry.IsVariety k sX) :
    IsDisjointUnionOfVarieties sX := by
  haveI := hX
  haveI : IsIntegral X := hX.toIsIntegral
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  intro C hC C' hC' hne
  rw [irreducibleComponents_eq_singleton] at hC hC'
  exact absurd (hC.trans hC'.symm) hne

/-- If the end result of a blow-up sequence of a variety is nonempty, it is a variety. -/
private theorem isVariety_toBase {k : Type u} [Field k] :
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
    have := isVariety_toBase B _ h hne
    change AlgebraicGeometry.IsVariety k ((B.toBase ≫ blowUpToBase Z) ≫ sX)
    rwa [Category.assoc]

/-! ### Isomorphisms over opens -/

/-- A morphism which is an isomorphism over a nonempty open has points over it. -/
private theorem nonempty_preimage_of_isIso_restrict {X Y : Scheme.{u}} (g : Y ⟶ X) (V : X.Opens)
    [IsIso (g ∣_ V)] (hV : (V : Set X).Nonempty) : ((g ⁻¹ᵁ V : Y.Opens) : Set Y).Nonempty := by
  obtain ⟨x, hx⟩ := hV
  obtain ⟨y, -⟩ := (g ∣_ V).surjective ⟨x, hx⟩
  exact ⟨y.1, y.2⟩

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

/-- A point over `V` is carried by `f ∣_ V` to its image. -/
private theorem ι_morphismRestrict_apply {X Y : Scheme.{u}} (f : Y ⟶ X) (V : X.Opens)
    (y : ((f ⁻¹ᵁ V : Y.Opens) : Scheme.{u})) : V.ι ((f ∣_ V) y) = f ((f ⁻¹ᵁ V).ι y) := by
  rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]

/-- An isomorphism over `V` preserves the coheight of the points over `V`. -/
private theorem coheight_apply_of_isIso_restrict {X Y : Scheme.{u}} (f : Y ⟶ X) (V : X.Opens)
    [IsIso (f ∣_ V)] {y : Y} (hy : f y ∈ V) : Order.coheight (f y) = Order.coheight y := by
  let y' : ((f ⁻¹ᵁ V : Y.Opens) : Scheme.{u}) := ⟨y, hy⟩
  have e : V.ι ((f ∣_ V) y') = f y := ι_morphismRestrict_apply f V y'
  have h1 := coheight_eq_of_isOpenImmersion (f ⁻¹ᵁ V).ι (x := y')
  rw [← e, coheight_eq_of_isOpenImmersion, coheight_eq_of_isOpenImmersion (f ∣_ V), ← h1]
  rfl

/-- The inverse of an isomorphism over `V` is a section of `f` over `V`. -/
private theorem apply_ι_inv_morphismRestrict {X Y : Scheme.{u}} (f : Y ⟶ X) (V : X.Opens)
    [IsIso (f ∣_ V)] (x : (V : Scheme.{u})) :
    f ((f ⁻¹ᵁ V).ι (inv (f ∣_ V) x)) = V.ι x := by
  rw [← ι_morphismRestrict_apply]
  congr 1
  rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
  rfl

/-- An open of `X` which is smooth over `k` lies in the smooth locus. -/
private theorem le_smoothLocus_of_isSmoothScheme {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] {U : X.Opens}
    (hU : IsSmoothScheme (U.ι ≫ sX)) : U ≤ smoothLocus sX := by
  have : LocallyOfFinitePresentation (U.ι ≫ sX) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := U.ι ≫ sX)).mpr inferInstance
  exact le_smoothLocus _ ((isSmoothScheme_iff _).1 hU)

/-- An open in the smooth locus is smooth over `k`. -/
private theorem isSmoothScheme_of_le_smoothLocus {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) {U : X.Opens} (hU : U ≤ smoothLocus sX) :
    IsSmoothScheme (U.ι ≫ sX) := by
  refine top_le_iff.1 fun x' _ => ?_
  obtain ⟨V, hxV, hV⟩ := mem_smoothLocus_iff.1 (hU x'.2)
  refine mem_smoothLocus_iff.2 ⟨U.ι ⁻¹ᵁ V, hxV, ?_⟩
  haveI := hV
  rw [← Category.assoc, ← Scheme.Hom.resLE_comp_ι U.ι (le_refl (U.ι ⁻¹ᵁ V)), Category.assoc]
  infer_instance

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

/-! ### Krull's principal ideal theorem on schemes -/

/-- A point of the support of an ideal sheaf with principal stalks which has no proper
generization in the support has coheight at most one. -/
private theorem coheight_le_one_of_principal {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (I : Y.IdealSheafData) (hI : ∀ y, ∃ h, IdealSheafData.stalk I y = Ideal.span {h})
    {η : Y} (hη : η ∈ I.support) (hmax : ∀ η' ∈ I.support, η' ⤳ η → η ⤳ η') :
    Order.coheight η ≤ 1 := by
  obtain ⟨h, hh⟩ := hI η
  have hmin : IsLocalRing.maximalIdeal _ ∈ (Ideal.span {h}).minimalPrimes := by
    refine ⟨⟨inferInstance, ?_⟩, fun P hP _ => ?_⟩
    · rw [← hh]
      exact IsLocalRing.le_maximalIdeal
        ((IdealSheafData.stalk_eq_top_iff_notMem_support _ _).not.2 (not_not.2 hη))
    · obtain ⟨hPp, hPh⟩ := hP
      let p : PrimeSpectrum (Y.presheaf.stalk η) := ⟨P, hPp⟩
      have hp1 : Y.fromSpecStalk η p ∈ I.support := by
        change p ∈ Y.fromSpecStalk η ⁻¹' (I.support : Set Y)
        rw [preimage_fromSpecStalk_support, hh]
        exact (PrimeSpectrum.mem_zeroLocus _ _).2 fun x hx => hPh hx
      have hp2 := fromSpecStalk_specializes_self η p
      have heq : Y.fromSpecStalk η p = η := (hp2.antisymm (hmax _ hp1 hp2)).eq
      have hpc : p = IsLocalRing.closedPoint _ := (Y.fromSpecStalk η).isEmbedding.injective
        (heq.trans Scheme.fromSpecStalk_closedPoint.symm)
      exact (congrArg PrimeSpectrum.asIdeal hpc).ge
  haveI : (Ideal.span {h}).IsPrincipal := ⟨⟨h, rfl⟩⟩
  have h2 : (Order.coheight η : WithBot ℕ∞) ≤ 1 := by
    rw [← ringKrullDim_stalk_eq_coheight, ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
    exact_mod_cast Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes_of_isLocalRing _ hmin
  exact_mod_cast h2

/-- In a Noetherian space every point of a closed set specializes from a maximal point of it. -/
private theorem exists_maximal_generization {Y : Type*} [TopologicalSpace Y] [NoetherianSpace Y]
    [QuasiSober Y] (S : Closeds Y) {y : Y} (hy : y ∈ S) :
    ∃ η ∈ S, η ⤳ y ∧ ∀ η' ∈ S, η' ⤳ η → η ⤳ η' := by
  obtain ⟨-, hcov⟩ := Aux.finite_and_cover_componentsOf S.isClosed
  obtain ⟨W, hW, hyW⟩ := Set.mem_sUnion.1 (hcov hy)
  have hWc : IsClosed W := Aux.isClosed_of_mem_componentsOf S.isClosed hW
  have hgen := hW.1.1.isGenericPoint_genericPoint_closure
  rw [hWc.closure_eq] at hgen
  refine ⟨hW.1.1.genericPoint, hW.1.2 hgen.mem, hgen.specializes hyW, fun η' hη' hsp => ?_⟩
  have h1 : W ⊆ closure {η'} := by
    rw [← hgen.def]
    exact closure_minimal (Set.singleton_subset_iff.2 (specializes_iff_mem_closure.1 hsp))
      isClosed_closure
  have h2 := hW.2 ⟨isIrreducible_singleton.closure, closure_minimal
    (Set.singleton_subset_iff.2 hη') S.isClosed⟩ h1
  rw [specializes_iff_mem_closure, hgen.def]
  exact h2 (subset_closure rfl)

/-- The support of an ideal sheaf with principal stalks on an integral locally Noetherian scheme
which misses the generic point is of pure codimension one. -/
private theorem isPureCodimOne_support_of_principal {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [NoetherianSpace Y] (I : Y.IdealSheafData)
    (hI : ∀ y, ∃ h, IdealSheafData.stalk I y = Ideal.span {h})
    (hgen : genericPoint Y ∉ I.support) : IsPureCodimOne I.support := by
  intro W hW
  set e := irreducibleSetEquivPoints (α := Y)
  have hWη : (W : Set Y) = closure {e W} := by
    conv_lhs => rw [← e.symm_apply_apply W]
    rfl
  have hηW : e W ∈ (W : Set Y) := by
    rw [hWη]
    exact subset_closure rfl
  have hηI : e W ∈ I.support := hW.1 hηW
  have h1 : codimension W = Order.coheight (e W) := by
    change Order.coheight W = _
    rw [← Order.coheight_orderIso e W]
  rw [h1]
  have hle := coheight_le_one_of_principal I hI hηI fun η' hη' hsp => by
    let W' : IrreducibleCloseds Y :=
      ⟨closure {η'}, isIrreducible_singleton.closure, isClosed_closure⟩
    have hWW' : W ≤ W' := by
      change (W : Set Y) ⊆ closure {η'}
      rw [hWη]
      exact closure_minimal (Set.singleton_subset_iff.2 (specializes_iff_mem_closure.1 hsp))
        isClosed_closure
    have h2 := hW.2 (y := W') (closure_minimal (Set.singleton_subset_iff.2 hη') I.support.isClosed)
      hWW'
    rw [specializes_iff_mem_closure, ← hWη]
    exact h2 (subset_closure rfl)
  have hne : Order.coheight (e W) ≠ 0 := by
    intro h0
    have hmax := Order.coheight_eq_zero.1 h0
    have h3 : e W ≤ genericPoint Y := by
      rw [Scheme.le_iff_specializes]
      exact genericPoint_specializes _
    have h4 := hmax h3
    rw [Scheme.le_iff_specializes] at h4
    have : e W = genericPoint Y := (h4.antisymm (genericPoint_specializes _)).eq
    exact hgen (this ▸ hηI)
  exact le_antisymm hle (ENat.one_le_iff_ne_zero.2 hne)

/-! ### Simple normal crossings at a point -/

/-- The union of the members of a finite family whose members through every point are distinct
coordinate hyperplanes is snc at every point. -/
private theorem isSNCAt_iUnion_of_isSNCFamily {Y : Scheme.{u}} {ι : Type*} [Finite ι]
    (E : ι → Y.IdealSheafData)
    (h : ∀ x : Y, ∃ (n : ℕ) (z : Fin n → Y.presheaf.stalk x)
      (c : {i // x ∈ (E i).support} → Fin n), IsRegularSystemOfParameters z ∧
        (∀ i, IdealSheafData.stalk (E i.1) x = Ideal.span {z (c i)}) ∧ Function.Injective c)
    (y : Y) : MMP.Resolution.IsSNCAt (⋃ i, ((E i).support : Set Y)) y := by
  classical
  obtain ⟨n, z, c, hz, hc, -⟩ := h y
  refine ⟨n, z, (Set.finite_range c).toFinset, hz, ?_⟩
  ext (p : PrimeSpectrum (Y.presheaf.stalk y))
  have hmem : ∀ i (hyi : y ∈ (E i).support),
      Y.fromSpecStalk y p ∈ ((E i).support : Set Y) ↔
        p ∈ PrimeSpectrum.zeroLocus {z (c ⟨i, hyi⟩)} := fun i hyi => by
    have h1 := Set.ext_iff.1 (preimage_fromSpecStalk_support (E i) y) p
    rwa [hc ⟨i, hyi⟩, PrimeSpectrum.zeroLocus_span] at h1
  constructor
  · intro hp
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1
      (show Y.fromSpecStalk y p ∈ ⋃ i, ((E i).support : Set Y) from hp)
    have hyi : y ∈ (E i).support :=
      (fromSpecStalk_specializes_self y p).mem_closed (E i).support.isClosed hi
    exact Set.mem_iUnion₂.2
      ⟨c ⟨i, hyi⟩, (Set.Finite.mem_toFinset _).2 ⟨⟨i, hyi⟩, rfl⟩, (hmem i hyi).1 hi⟩
  · intro hp
    obtain ⟨j, hj, hpj⟩ := Set.mem_iUnion₂.1 hp
    obtain ⟨⟨i, hyi⟩, rfl⟩ := (Set.Finite.mem_toFinset _).1 hj
    change Y.fromSpecStalk y p ∈ ⋃ i, ((E i).support : Set Y)
    exact Set.mem_iUnion.2 ⟨i, (hmem i hyi).2 hpj⟩

/-- A closed subset with simple normal crossings is snc at every point. -/
private theorem isSNCAt_of_isSNCClosedSubset {k : Type u} [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] [NoetherianSpace Y]
    (hsm : IsSmoothScheme sY) {T : Set Y} (hT : IsSNCClosedSubset sY T) (y : Y) :
    MMP.Resolution.IsSNCAt T y := by
  obtain ⟨hTc, rfl | ⟨-, hfin, hfam⟩⟩ := hT
  · haveI : Smooth sY := Aux.smooth_of_isSmoothScheme' sY hsm
    haveI := isRegularLocalRing_stalk_of_smooth_over_field sY y
    obtain ⟨n, z, hz⟩ := MMP.Mori.exists_isRegularSystemOfParameters (Y.presheaf.stalk y)
    refine ⟨n, z, ∅, hz, ?_⟩
    ext (x : PrimeSpectrum (Y.presheaf.stalk y))
    refine ⟨fun h => h.elim, fun h => ?_⟩
    simp only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty] at h
    exact h.elim
  · haveI : Finite (componentsOf T) := hfin.to_subtype
    have hsupp : ∀ V : componentsOf T, ((componentsFamily T V).support : Set Y) = V := fun V => by
      unfold componentsFamily
      rw [Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_closure,
        (Aux.isClosed_of_mem_componentsOf hTc V.2).closure_eq]
    have hT : T = ⋃ V : componentsOf T, ((componentsFamily T V).support : Set Y) := by
      simp_rw [hsupp]
      refine Set.Subset.antisymm (fun x hx => ?_) (Set.iUnion_subset fun V => V.2.1.2)
      obtain ⟨W, hW, hxW⟩ := Set.mem_sUnion.1 ((Aux.finite_and_cover_componentsOf hTc).2 hx)
      exact Set.mem_iUnion.2 ⟨⟨W, hW⟩, hxW⟩
    rw [hT]
    exact isSNCAt_iUnion_of_isSNCFamily _ hfam.2 y

/-- Snc of a set at a point is carried along a morphism whose stalk map there is an isomorphism:
if `g⁻¹(T)` is snc at `y`, then `T` is snc at `g(y)`. -/
private theorem isSNCAt_apply_of_isSNCAt_preimage {Y Y' : Scheme.{u}} (g : Y ⟶ Y') (y : Y)
    [IsIso (g.stalkMap y)] {T : Set Y'} (h : MMP.Resolution.IsSNCAt (g ⁻¹' T) y) :
    MMP.Resolution.IsSNCAt T (g y) := by
  obtain ⟨n, w, C, hw, hT⟩ := h
  let e : Y'.presheaf.stalk (g y) ≃+* Y.presheaf.stalk y :=
    (asIso (g.stalkMap y)).commRingCatIsoToRingEquiv
  refine ⟨n, fun c => e.symm (w c), C, isRegularSystemOfParameters_map_ringEquiv e.symm hw, ?_⟩
  ext (q : PrimeSpectrum (Y'.presheaf.stalk (g y)))
  let p : PrimeSpectrum (Y.presheaf.stalk y) :=
    PrimeSpectrum.comap (e.symm : Y.presheaf.stalk y →+* Y'.presheaf.stalk (g y)) q
  have hq : PrimeSpectrum.comap (g.stalkMap y).hom p = q := by
    ext x
    change e.symm (e x) ∈ q.asIdeal ↔ x ∈ q.asIdeal
    rw [RingEquiv.symm_apply_apply]
  have key : Y'.fromSpecStalk (g y) q = g (Y.fromSpecStalk y p) := by
    rw [apply_fromSpecStalk, hq]
  have h1 := Set.ext_iff.1 hT p
  have hz : ∀ c, p ∈ PrimeSpectrum.zeroLocus {w c} ↔
      q ∈ PrimeSpectrum.zeroLocus {e.symm (w c)} := fun c => by
    simp only [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe]
    rfl
  refine ⟨fun hq' => ?_, fun hq' => ?_⟩
  · obtain ⟨c, hc, hpc⟩ := Set.mem_iUnion₂.1 (h1.1 (key ▸ hq' : g (Y.fromSpecStalk y p) ∈ T))
    exact Set.mem_iUnion₂.2 ⟨c, hc, (hz c).1 hpc⟩
  · obtain ⟨c, hc, hqc⟩ := Set.mem_iUnion₂.1 hq'
    change Y'.fromSpecStalk (g y) q ∈ T
    rw [key]
    exact h1.2 (Set.mem_iUnion₂.2 ⟨c, hc, (hz c).2 hqc⟩)

/-- At a point `y` where the closed set `T` is snc with coordinates `w` and indices `C`, the stalk
at `y` of the ideal of an irreducible component `V ∋ y` of `T` is `(w_c)` for some `c ∈ C`, the
prime of `𝒪_{Y,y}` corresponding to the generic point of `V`. -/
private theorem exists_stalk_componentsFamily_eq {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    {T : Set Y} (hT : IsClosed T) {y : Y} {n : ℕ}
    {w : Fin n → Y.presheaf.stalk y} {C : Finset (Fin n)} (hw : IsRegularSystemOfParameters w)
    (hTy : Y.fromSpecStalk y ⁻¹' T = ⋃ c ∈ C, PrimeSpectrum.zeroLocus {w c})
    (V : componentsOf T) (hyV : y ∈ (V : Set Y)) :
    ∃ c ∈ C, IdealSheafData.stalk (componentsFamily T V) y = Ideal.span {w c} ∧
      ∃ q : PrimeSpectrum (Y.presheaf.stalk y), (V : Set Y) = closure {Y.fromSpecStalk y q} ∧
        q.asIdeal = Ideal.span {w c} := by
  obtain ⟨ξ, hξT, hVξ⟩ := Aux.exists_eq_closure_of_mem_componentsOf hT V.2
  have hξy : ξ ⤳ y := specializes_iff_mem_closure.mpr (hVξ ▸ hyV)
  obtain ⟨q, hq⟩ : ξ ∈ Set.range (Y.fromSpecStalk y) := by
    rw [Scheme.range_fromSpecStalk]
    exact hξy
  have hstalk : IdealSheafData.stalk (componentsFamily T V) y = q.asIdeal := by
    have : componentsFamily T V = Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({Y.fromSpecStalk y q} : Set Y)) := by
      unfold componentsFamily
      congr 1
      ext1
      rw [Closeds.coe_closure, Closeds.coe_closure, hq, ← hVξ,
        (Aux.isClosed_of_mem_componentsOf hT V.2).closure_eq]
    rw [this]
    exact Stacks.Chow.idealStalk_vanishingIdeal_closure_fromSpecStalk y q
  have hqT : q ∈ Y.fromSpecStalk y ⁻¹' T := by
    rwa [Set.mem_preimage, hq]
  rw [hTy] at hqT
  obtain ⟨c, hc, hwc⟩ := Set.mem_iUnion₂.1 hqT
  replace hwc : w c ∈ q.asIdeal := (PrimeSpectrum.mem_zeroLocus _ _).1 hwc (Set.mem_singleton _)
  let p' : PrimeSpectrum (Y.presheaf.stalk y) :=
    ⟨Ideal.span {w c}, span_singleton_isPrime_of_isRegularSystemOfParameters hw c⟩
  have hp'q : p' ≤ q := (Ideal.span_singleton_le_iff_mem _).2 hwc
  have hp'T : Y.fromSpecStalk y p' ∈ T := by
    have : p' ∈ Y.fromSpecStalk y ⁻¹' T := by
      rw [hTy]
      refine Set.mem_biUnion hc ?_
      rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff]
      exact Ideal.subset_span rfl
    exact this
  have hsp : Y.fromSpecStalk y p' ⤳ ξ :=
    hq ▸ ((PrimeSpectrum.le_iff_specializes _ _).1 hp'q).map (Y.fromSpecStalk y).continuous
  have hsub : (V : Set Y) ⊆ closure {Y.fromSpecStalk y p'} := by
    rw [hVξ]
    exact closure_minimal (Set.singleton_subset_iff.2 (specializes_iff_mem_closure.1 hsp))
      isClosed_closure
  have hcl : closure {Y.fromSpecStalk y p'} = (V : Set Y) :=
    (V.2.2 ⟨isIrreducible_singleton.closure,
      closure_minimal (Set.singleton_subset_iff.2 hp'T) hT⟩ hsub).antisymm hsub
  have hpq : p' = q := by
    apply (Y.fromSpecStalk y).isEmbedding.injective
    rw [hq]
    refine Inseparable.eq ?_
    rw [inseparable_iff_closure_eq, hcl, hVξ]
  refine ⟨c, hc, hstalk.trans (by rw [← hpq]), q, hq ▸ hVξ, by rw [← hpq]⟩

/-- At a point where a closed set is snc, its irreducible components through the point are
distinct coordinate hyperplanes. -/
private theorem isSNCAt_componentsFamily_of_isSNCAt {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    {T : Set Y} (hT : IsClosed T) {y : Y} (h : MMP.Resolution.IsSNCAt T y) :
    TupleResolutionAux.IsSNCAt (componentsFamily T) y := by
  obtain ⟨n, w, C, hw, hTy⟩ := h
  have hmem : ∀ V : {V // y ∈ (componentsFamily T V).support}, y ∈ (V.1 : Set Y) := fun V => by
    have := V.2
    rwa [← SetLike.mem_coe, componentsFamily, Scheme.IdealSheafData.coe_support_vanishingIdeal,
      Closeds.coe_closure, (Aux.isClosed_of_mem_componentsOf hT V.1.2).closure_eq] at this
  choose c _ hc q hq hqc using fun V : {V // y ∈ (componentsFamily T V).support} =>
    exists_stalk_componentsFamily_eq hT hw hTy V.1 (hmem V)
  refine ⟨n, w, c, hw, fun V V' hVV' => ?_, hc⟩
  have hqq : q V = q V' := PrimeSpectrum.ext ((hqc V).trans (by rw [hVV', hqc V']))
  apply Subtype.ext; apply Subtype.ext
  rw [hq V, hq V', hqq]

/-- The union of the members of a finite snc family is a closed subset with simple normal
crossings. -/
private theorem isSNCClosedSubset_iUnion_of_isSNCFamily {k : Type u} [Field k] [PerfectField k]
    {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] [CompactSpace Y]
    {ι : Type*} [Finite ι] (E : ι → Y.IdealSheafData) (h : IsSNCFamily sY E) :
    IsSNCClosedSubset sY (⋃ i, ((E i).support : Set Y)) :=
  isSNCClosedSubset_of_forall_isSNCAt sY (isClosed_iUnion_of_finite fun i => (E i).support.isClosed)
    (isSNCAt_iUnion_of_isSNCFamily E h.2)

/-! ### Supports of transforms of ordered divisor tuples -/

/-- The union of the supports of the ideals and boundary entries of a tuple. -/
private def tupleSupport {V : Scheme.{u}} (T : OrderedDivisorTuple V) : Set V :=
  ⋃ p, ((T.divisors p).support : Set V)

/-- The support of a tuple is the union of the supports of its ideals and of its boundary. -/
private theorem tupleSupport_eq {V : Scheme.{u}} (T : OrderedDivisorTuple V) :
    tupleSupport T = (⋃ j, ((T.I j).support : Set V)) ∪ T.E.support := by
  ext x
  simp [tupleSupport, OrderedDivisor.support, OrderedDivisorTuple.divisors, Sum.exists]

/-- **One order-one transformation.** If the entries of the boundary are of pure codimension one
and the centre lies in the support of the tuple, the support of the transformed tuple is the
inverse image of the support of the tuple. -/
private theorem tupleSupport_transform {V : Scheme.{u}} (T : OrderedDivisorTuple V)
    (C : V.IdealSheafData) (hE : ∀ i, IsPureCodimOne (T.E.E i).support)
    (hC : (C.support : Set V) ⊆ tupleSupport T) :
    tupleSupport (T.transform C) = blowUpToBase C ⁻¹' tupleSupport T := by
  classical
  set π := blowUpToBase C
  have hEtot := OrderedDivisor.support_totalTransform T.E hE C
  have hpre := preimage_union_subset_support_totalTransform T.E hE C
  have hEc : IsClosed T.E.support := isClosed_iUnion_of_finite fun i => (T.E.E i).support.isClosed
  rw [tupleSupport_eq, tupleSupport_eq] at *
  apply Set.Subset.antisymm
  · rintro x (hx | hx)
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hx
      have hj' : x ∈ ((TupleResolutionAux.transformIdeal C (T.I j)).support : Set _) := by
        rwa [TupleResolutionAux.transform_I_eq_transformIdeal T C j] at hj
      unfold TupleResolutionAux.transformIdeal at hj'
      have hcomap : x ∈ (((T.I j).comap π).support : Set _) := by
        split_ifs at hj'
        · exact Scheme.IdealSheafData.support_antitone (le_idealColon _ _) hj'
        · exact hj'
      rw [Scheme.IdealSheafData.support_comap] at hcomap
      exact Or.inl (Set.mem_iUnion.2 ⟨j, hcomap⟩)
    · change x ∈ (T.E.totalTransform C).support at hx
      rw [hEtot] at hx
      rcases hx with hx | hx
      · have h' : closure (π ⁻¹' (T.E.support \ (C.support : Set V))) ⊆ π ⁻¹' T.E.support :=
          closure_minimal (Set.preimage_mono Set.diff_subset) (hEc.preimage π.continuous)
        exact Or.inr (h' hx)
      · exact hC hx
  · rintro x (hx | hx)
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hx
      by_cases hxC : π x ∈ (C.support : Set V)
      · exact Or.inr (hpre (Or.inl hxC))
      · left
        refine Set.mem_iUnion.2 ⟨j, ?_⟩
        change x ∈ (((T.transform C).I j).support : Set _)
        rw [TupleResolutionAux.transform_I_eq_transformIdeal]
        unfold TupleResolutionAux.transformIdeal
        have hcomap : x ∈ (((T.I j).comap π).support : Set _) := by
          rwa [Scheme.IdealSheafData.support_comap]
        split_ifs
        · have h1 := Scheme.IdealSheafData.support_antitone
            (TupleResolutionAux.idealColon_mul_le ((T.I j).comap π) (C.comap π)) hcomap
          rw [Scheme.IdealSheafData.support_mul] at h1
          rcases h1 with h1 | h1
          · exact h1
          · rw [Scheme.IdealSheafData.support_comap] at h1
            exact absurd h1 hxC
        · exact hcomap
    · exact Or.inr (hpre (Or.inr hx))

/-- Along a valid sequence of order-one transformations whose admissible set `N` contains the
complement of the support of the tuple, the support of the final tuple is the inverse image of the
support of the original one. -/
private theorem tupleSupport_finalTuple {k : Type u} [Field k] [CharZero k] :
    ∀ {S : Scheme.{u}} (B : ClosedBlowupSequence S) (s : S ⟶ Spec (.of k))
      [LocallyOfFiniteType s] [QuasiCompact s] (N : Set S) (T : OrderedDivisorTuple S),
      T.E.IsSNC s → (tupleSupport T)ᶜ ⊆ N → TupleResolutionAux.Valid s N B T →
      tupleSupport (TupleResolutionAux.finalTuple B T) = B.toBase ⁻¹' tupleSupport T := by
  intro S B
  induction B with
  | nil S =>
    intro s _ _ N T _ _ _
    rfl
  | @cons S Z B ih =>
    intro s _ _ N T hE hN hV
    haveI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian s
    haveI : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace s
    obtain ⟨hcent, hdisj, hB⟩ := hV
    have hZ : (Z.support : Set S) ⊆ tupleSupport T := fun x hx => by
      by_contra h
      exact hdisj.notMem_of_mem_left hx (hN h)
    have hstep := tupleSupport_transform T Z (fun i => (hE.1 i).2.1) hZ
    have hE' : (T.transform Z).E.IsSNC (blowUpToBase Z ≫ s) :=
      (isOrderedSNC_totalTransform s hE hcent.2).2
    have hN' : (tupleSupport (T.transform Z))ᶜ ⊆ blowUpToBase Z ⁻¹' N := by
      rw [hstep, ← Set.preimage_compl]
      exact Set.preimage_mono hN
    change tupleSupport (TupleResolutionAux.finalTuple B (T.transform Z)) =
      (B.toBase ≫ blowUpToBase Z) ⁻¹' tupleSupport T
    rw [ih _ _ _ hE' hN' hB, hstep]
    rfl

/-! ### Marked order-one reduction -/

/-- The cosupport of a marked ideal of marking one lies in the support of the ideal. -/
private theorem cosupport_one_subset {X : Scheme.{u}} (I : X.IdealSheafData) :
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
private theorem support_subset_cosupport' {k : Type u} [Field k] {X : Scheme.{u}}
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
private theorem cosupport_birationalTransform_subset' {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) (a : MarkedIdeal X) (E : OrderedDivisor X) (Z : X.IdealSheafData)
    (B : ClosedBlowupSequence (blowUp Z))
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
private theorem support_orderedTotalTransform_subset {k : Type u} [Field k] :
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
    have hB' := hB
    obtain ⟨hT, hZ, -, -, hord, hB''⟩ := hB'
    have hcos := cosupport_birationalTransform_subset' s a E Z B hB
    have hEc : IsClosed E.support := isClosed_iUnion_of_finite fun i => (E.E i).support.isClosed
    rcases ih _ _ _ hB'' hx with h | h
    · rw [OrderedDivisor.support_totalTransform E (fun i => (hT.2.2.2.2.2.2.2.1 i).2.1) Z] at h
      rcases h with h | h
      · have h' : closure (blowUpToBase Z ⁻¹' (E.support \ (Z.support : Set X))) ⊆
            blowUpToBase Z ⁻¹' E.support := closure_minimal
          (Set.preimage_mono Set.diff_subset) (hEc.preimage (blowUpToBase Z).continuous)
        exact Or.inl (h' h)
      · exact Or.inr (support_subset_cosupport' s hT.2.1 Z hZ a.I a.m hord h)
    · exact Or.inr (hcos h)

/-- A smooth blow-up sequence of order `≥ m` starting with `(X, I, m, E)` is an isomorphism over
every open missing `cosupp(I, m)`. -/
private theorem isIso_restrict_of_disjoint_cosupport {k : Type u} [Field k] :
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
    have hB' := hB
    obtain ⟨hT, hZ, -, -, hord, hB''⟩ := hB'
    have hZW : (W : Set X) ⊆ (Z.support : Set X)ᶜ := fun x hxW hxZ =>
      hW.notMem_of_mem_right hxW (support_subset_cosupport' s hT.2.1 Z hZ a.I a.m hord hxZ)
    haveI : IsIso (blowUpToBase Z ∣_ W) :=
      isIso_blowUpToBase_restrict_of_subset_compl_support Z W hZW
    have hcos := cosupport_birationalTransform_subset' s a E Z B hB
    haveI : IsIso (B.toBase ∣_ blowUpToBase Z ⁻¹ᵁ W) := ih _ _ _ hB'' _
      (Set.disjoint_left.2 fun y hy hyW => hW.notMem_of_mem_right hyW (hcos hy))
    exact isIso_restrict_comp B.toBase (blowUpToBase Z) W

/-- A tuple whose snc locus is everything: its ideals and boundary entries, listed in one ordered
divisor, form an ordered snc divisor. -/
private theorem isOrderedSNC_of_sncLocus_eq_univ {k : Type u} [Field k] [PerfectField k]
    {V : Scheme.{u}} (s : V ⟶ Spec (.of k)) [LocallyOfFiniteType s] (T : OrderedDivisorTuple V)
    (h : T.sncLocus = Set.univ) :
    (⟨T.m + T.E.s, fun i => T.divisors (finSumFinEquiv.symm i)⟩ : OrderedDivisor V).IsOrderedSNC
      s := by
  haveI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian s
  have hmem : ∀ y, y ∈ T.sncLocus := fun y => h ▸ Set.mem_univ y
  have hpar : ∀ p, ∀ y ∈ (T.divisors p).support, ∃ (m : ℕ) (w : Fin m → V.presheaf.stalk y)
      (j : Fin m), IsRegularSystemOfParameters w ∧
        IdealSheafData.stalk (T.divisors p) y = Ideal.span {w j} := fun p y hy => by
    obtain ⟨n, z, c, hz, -, hzc⟩ := hmem y
    exact ⟨n, z, c ⟨p, hy⟩, hz, hzc ⟨p, hy⟩⟩
  have hfam : IsSNCFamily s T.divisors := by
    refine ⟨fun p => ⟨isReduced_subscheme_of_stalk_eq_span_parameter _ (hpar p),
      isPureCodimOne_support_of_stalk_eq_span_parameter _ (hpar p),
      isSmoothScheme_subscheme_of_stalk_eq_span_parameter s _ (hpar p)⟩, fun x => ?_⟩
    obtain ⟨n, z, c, hz, hc, hzc⟩ := hmem x
    exact ⟨n, z, c, hz, hzc, hc⟩
  exact ⟨fun i => ⟨(hfam.1 _).1, isEffectiveCartierDivisor_of_stalk_eq_span_parameter _
    (hpar _)⟩, MMP.Resolution.Internal.TupleRestrictionLift.isSNCFamily_comp hfam _
      finSumFinEquiv.symm.injective⟩

/-- A nonempty quasi-compact scheme locally of finite type over a field has finite dimension. -/
private theorem hasDimensionIn_univ_of_locallyOfFiniteType {k : Type u} [Field k]
    {Y : Scheme.{u}} (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s] [CompactSpace Y]
    [Nonempty Y] : HasDimensionIn Y Set.univ := by
  have htop := topologicalKrullDim_ne_top_of_locallyOfFiniteType k s
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

/-- The generic point of an integral scheme lies on no prime divisor. -/
private theorem genericPoint_notMem_sup_support {X : Scheme.{u}} [IsIntegral X]
    (D : Finset (MMP.Mori.PrimeDivisor X)) :
    genericPoint X ∉ D.sup fun E => (E.idealSheaf.support : Set X) := by
  rw [Finset.sup_set_eq_biUnion]
  simp only [Set.mem_iUnion, not_exists]
  intro E _ hE
  have h3 := AlgebraicGeometry.PrimeDivisor.coheight_genericPoint E
  rw [((Aux.genericPoint_specializes_of_mem_support E hE).antisymm
    (genericPoint_specializes _)).eq, Order.coheight_eq_zero.2] at h3
  · exact absurd h3 (by norm_num)
  · intro b hb
    rw [Scheme.le_iff_specializes] at hb ⊢
    exact genericPoint_specializes _

/-! ### The tuple of strict transforms -/

/-- Every irreducible component of a finite union of closures of points is one of them. -/
private theorem exists_mem_eq_closure_of_mem_componentsOf_biUnion {Y : Type*}
    [TopologicalSpace Y] {ι : Type*} (D : Finset ι) (ξ : ι → Y) {V : Set Y}
    (hV : V ∈ componentsOf (⋃ E ∈ D, closure {ξ E})) : ∃ E ∈ D, V = closure {ξ E} := by
  classical
  obtain ⟨z, hz, hVz⟩ := isIrreducible_iff_sUnion_isClosed.mp hV.1.1
    (D.image fun E => closure {ξ E})
    (fun z hz => by obtain ⟨E, -, rfl⟩ := Finset.mem_image.1 hz; exact isClosed_closure)
    (fun x hx => by
      obtain ⟨E, hE, hxE⟩ := Set.mem_iUnion₂.1 (hV.1.2 hx)
      exact Set.mem_sUnion.2 ⟨_, Finset.mem_coe.2 (Finset.mem_image_of_mem _ hE), hxE⟩)
  obtain ⟨E, hE, rfl⟩ := Finset.mem_image.1 hz
  exact ⟨E, hE, hVz.antisymm (hV.2 ⟨isIrreducible_singleton.closure,
    Set.subset_biUnion_of_mem (u := fun E => closure {ξ E}) hE⟩ hVz)⟩

/-- The tuple listing the irreducible components of a closed set `S`, with empty boundary, has
support `S`. -/
private theorem tupleSupport_componentsFamily {Y : Scheme.{u}} [NoetherianSpace Y] {S : Set Y}
    (hSc : IsClosed S) {n : ℕ} (e : componentsOf S ≃ Fin n) :
    tupleSupport (⟨n, fun j => componentsFamily S (e.symm j), OrderedDivisor.empty Y⟩ :
      OrderedDivisorTuple Y) = S := by
  have hsuppV : ∀ V : componentsOf S, ((componentsFamily S V).support : Set Y) = V := fun V => by
    rw [componentsFamily, Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_closure,
      (Aux.isClosed_of_mem_componentsOf hSc V.2).closure_eq]
  rw [tupleSupport_eq]
  have hE0 : (OrderedDivisor.empty Y).support = ∅ := by
    simp [OrderedDivisor.support, OrderedDivisor.empty]
  change (⋃ j, ((componentsFamily S (e.symm j)).support : Set Y)) ∪
    (OrderedDivisor.empty Y).support = S
  rw [hE0, Set.union_empty]
  apply Set.Subset.antisymm
  · refine Set.iUnion_subset fun j => ?_
    rw [hsuppV]
    exact (e.symm j).2.1.2
  · intro x hx
    obtain ⟨W, hW, hxW⟩ := Set.mem_sUnion.1 ((Aux.finite_and_cover_componentsOf hSc).2 hx)
    refine Set.mem_iUnion.2 ⟨e ⟨W, hW⟩, ?_⟩
    rw [Equiv.symm_apply_apply, hsuppV]
    exact hxW

/-- A point where a closed set `S` is snc lies in the snc locus of the tuple listing the
irreducible components of `S`. -/
private theorem mem_sncLocus_componentsFamily {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    {S : Set Y} (hSc : IsClosed S) {n : ℕ} (e : componentsOf S ≃ Fin n) {y : Y}
    (h : MMP.Resolution.IsSNCAt S y) :
    y ∈ (⟨n, fun j => componentsFamily S (e.symm j), OrderedDivisor.empty Y⟩ :
      OrderedDivisorTuple Y).sncLocus := by
  let T : OrderedDivisorTuple Y := ⟨n, fun j => componentsFamily S (e.symm j),
    OrderedDivisor.empty Y⟩
  let F : {p // y ∈ (T.divisors p).support} → {V // y ∈ (componentsFamily S V).support} :=
    fun p => ⟨e.symm (Sum.elim id (fun i => i.elim0) p.1), by
      rcases p with ⟨j | i, hp⟩
      exacts [hp, i.elim0]⟩
  refine (TupleResolutionAux.mem_sncLocus_iff T y).2
    ((isSNCAt_componentsFamily_of_isSNCAt hSc h).of_injective F ?_ ?_)
  · rintro ⟨j | i, hj⟩ ⟨j' | i', hj'⟩ h
    · exact Subtype.ext (congrArg Sum.inl (e.symm.injective (congrArg Subtype.val h)))
    · exact i'.elim0
    · exact i.elim0
    · exact i.elim0
  · rintro ⟨j | i, hj⟩
    · rfl
    · exact i.elim0

/-- If `f₁` is an isomorphism over `U`, `S` lies over `SD` and contains everything over
`SD ∩ U`, and `U ∩ SD` is snc in `U`, then `S` is snc at every point over `U`. -/
private theorem isSNCAt_of_isIso_restrict {X X₁ : Scheme.{u}} (f₁ : X₁ ⟶ X) (U : X.Opens)
    [IsIso (f₁ ∣_ U)] {S : Set X₁} {SD : Set X} (hsup : S ⊆ f₁ ⁻¹' SD)
    (hsub : ∀ a, f₁ a ∈ SD → f₁ a ∈ U → a ∈ S)
    (hU : ∀ x : (U : Scheme.{u}), MMP.Resolution.IsSNCAt (U.ι ⁻¹' SD) x) {y : X₁}
    (hy : y ∈ f₁ ⁻¹' (U : Set X)) : MMP.Resolution.IsSNCAt S y := by
  set ψ := f₁ ∣_ U
  let y' : ((f₁ ⁻¹ᵁ U : X₁.Opens) : Scheme.{u}) := ⟨y, hy⟩
  let x' : (U : Scheme.{u}) := ⟨f₁ y, hy⟩
  have hψy : ψ y' = x' := Subtype.ext (ι_morphismRestrict_apply f₁ U y')
  have hinv : inv ψ x' = y' := by
    rw [← hψy, ← Scheme.Hom.comp_apply, IsIso.hom_inv_id]
    rfl
  have hpre : inv ψ ⁻¹' ((f₁ ⁻¹ᵁ U).ι ⁻¹' S) = U.ι ⁻¹' SD := by
    ext x
    simp only [Set.mem_preimage]
    have hfx := apply_ι_inv_morphismRestrict f₁ U x
    refine ⟨fun h => ?_, fun h => hsub _ (by rw [hfx]; exact h) (by rw [hfx]; exact x.2)⟩
    have := hsup h
    rwa [Set.mem_preimage, hfx] at this
  have h1 : MMP.Resolution.IsSNCAt ((f₁ ⁻¹ᵁ U).ι ⁻¹' S) y' := by
    have := isSNCAt_apply_of_isSNCAt_preimage (inv ψ) x' (T := (f₁ ⁻¹ᵁ U).ι ⁻¹' S)
      (by rw [hpre]; exact hU x')
    rwa [hinv] at this
  exact isSNCAt_apply_of_isSNCAt_preimage (f₁ ⁻¹ᵁ U).ι y' h1

/-- If `f₁` is an isomorphism over `U` and the generic point of the prime divisor `E` lies in
`U`, its strict transform is a point `ξ` of coheight one over that generic point which specializes
to every point over `Supp E ∩ U`. -/
private theorem exists_strictTransform_point {X X₁ : Scheme.{u}} (f₁ : X₁ ⟶ X) (U : X.Opens)
    [IsIso (f₁ ∣_ U)] (E : MMP.Mori.PrimeDivisor X)
    (hE : AlgebraicGeometry.PrimeDivisor.genericPoint E ∈ U) :
    ∃ ξ : X₁, f₁ ξ = AlgebraicGeometry.PrimeDivisor.genericPoint E ∧ Order.coheight ξ = 1 ∧
      ∀ a, f₁ a ∈ U → f₁ a ∈ (E.idealSheaf.support : Set X) → ξ ⤳ a := by
  set φ := f₁ ∣_ U
  have hfξ : f₁ ((f₁ ⁻¹ᵁ U).ι (inv φ ⟨_, hE⟩)) = AlgebraicGeometry.PrimeDivisor.genericPoint E :=
    apply_ι_inv_morphismRestrict f₁ U _
  refine ⟨_, hfξ, ?_, fun a ha haE => ?_⟩
  · rw [← coheight_apply_of_isIso_restrict f₁ U (by rw [hfξ]; exact hE), hfξ]
    exact AlgebraicGeometry.PrimeDivisor.coheight_genericPoint E
  · let a' : ((f₁ ⁻¹ᵁ U : X₁.Opens) : Scheme.{u}) := ⟨a, ha⟩
    have h1 : φ a' = ⟨f₁ a, ha⟩ := Subtype.ext (ι_morphismRestrict_apply f₁ U a')
    have h2 : (⟨_, hE⟩ : (U : Scheme.{u})) ⤳ ⟨f₁ a, ha⟩ :=
      (subtype_specializes_iff _ _).2 (Aux.genericPoint_specializes_of_mem_support E haE)
    have h3 := h2.map (inv φ).continuous
    rw [← h1, ← Scheme.Hom.comp_apply, IsIso.hom_inv_id] at h3
    exact h3.map (f₁ ⁻¹ᵁ U).ι.continuous

/-- On the strong resolution `f₁ : X₁ ⟶ X` of a normal variety, an isomorphism over the smooth
locus, the strict transforms of the components of `D` form an ordered divisor tuple (with empty
boundary) whose support lies between `f₁⁻¹(Supp D ∩ X^ns)` and `f₁⁻¹(Supp D)` and whose snc
locus contains `f₁⁻¹(U)` for every open `U ⊆ X^ns` on which `Supp D` has simple normal
crossings. -/
private theorem exists_orderedDivisorTuple_strictTransform {k : Type u} [Field k] [CharZero k]
    {X X₁ : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (hX : IsNormalVariety k sX)
    (D : Finset (MMP.Mori.PrimeDivisor X))
    (f₁ : X₁ ⟶ X) (hX₁ : AlgebraicGeometry.IsVariety k (f₁ ≫ sX))
    (hsm₁ : IsSmoothScheme (f₁ ≫ sX)) [IsIso (f₁ ∣_ smoothLocus sX)] :
    ∃ T : OrderedDivisorTuple X₁, IsOrderedDivisorTuple (f₁ ≫ sX) T ∧
      f₁ ⁻¹' ((D.sup fun E => (E.idealSheaf.support : Set X)) ∩ smoothLocus sX) ⊆
        tupleSupport T ∧
      tupleSupport T ⊆ f₁ ⁻¹' (D.sup fun E => (E.idealSheaf.support : Set X)) ∧
      ∀ U : X.Opens, U ≤ smoothLocus sX →
        IsSNCClosedSubset (U.ι ≫ sX) (U.ι ⁻¹' (D.sup fun E => E.idealSheaf.support)) →
        f₁ ⁻¹' (U : Set X) ⊆ T.sncLocus := by
  classical
  haveI : AlgebraicGeometry.IsVariety k sX := hX.1
  haveI := hX₁
  haveI : IsIntegral X₁ := hX₁.toIsIntegral
  haveI := isNoetherian_of_locallyOfFiniteType (f₁ ≫ sX)
  haveI := isNoetherian_of_locallyOfFiniteType sX
  set SD : Set X := D.sup fun E => (E.idealSheaf.support : Set X) with hSD
  have hmemSD : ∀ x, x ∈ SD ↔ ∃ E ∈ D, x ∈ (E.idealSheaf.support : Set X) := fun x => by
    rw [hSD, Finset.sup_set_eq_biUnion]
    simp
  set Xns := smoothLocus sX
  have hη : ∀ E : MMP.Mori.PrimeDivisor X, AlgebraicGeometry.PrimeDivisor.genericPoint E ∈ Xns :=
    fun E => MMP.Positivity.PrimeDivisor.genericPoint_mem_smoothLocus hX E
  choose ξ hfξ hξcoh hξsp using fun E => exists_strictTransform_point f₁ Xns E (hη E)
  set S : Set X₁ := ⋃ E ∈ D, closure {ξ E}
  have hSc : IsClosed S := isClosed_biUnion_finset fun E _ => isClosed_closure
  have hSsub : f₁ ⁻¹' (SD ∩ Xns) ⊆ S := by
    rintro a ⟨haD, haX⟩
    obtain ⟨E, hE, haE⟩ := (hmemSD _).1 haD
    exact Set.mem_biUnion hE (specializes_iff_mem_closure.1 (hξsp E a haX haE))
  have hSDc : IsClosed SD := by
    rw [hSD, Finset.sup_set_eq_biUnion]
    exact isClosed_biUnion_finset fun E _ => E.idealSheaf.support.isClosed
  have hSsup : S ⊆ f₁ ⁻¹' SD := by
    refine Set.iUnion₂_subset fun E hE => closure_minimal ?_ (hSDc.preimage f₁.continuous)
    rw [Set.singleton_subset_iff, Set.mem_preimage, hfξ, hmemSD]
    refine ⟨E, hE, ?_⟩
    change _ ∈ (E.support : Set X)
    rw [Aux.support_eq_closure_genericPoint E]
    exact subset_closure rfl
  haveI : Finite (componentsOf S) := (Aux.finite_and_cover_componentsOf hSc).1.to_subtype
  let e := Finite.equivFin (componentsOf S)
  let T : OrderedDivisorTuple X₁ := ⟨Nat.card (componentsOf S),
    fun j => componentsFamily S (e.symm j), OrderedDivisor.empty X₁⟩
  have hTsupp : tupleSupport T = S := tupleSupport_componentsFamily hSc e
  have hRSOP : ∀ x : X₁, ∃ (n : ℕ) (z : Fin n → X₁.presheaf.stalk x),
      IsRegularSystemOfParameters z := fun x => by
    haveI : Smooth (f₁ ≫ sX) := Aux.smooth_of_isSmoothScheme' _ hsm₁
    haveI := isRegularLocalRing_stalk_of_smooth_over_field (f₁ ≫ sX) x
    exact MMP.Mori.exists_isRegularSystemOfParameters _
  refine ⟨T, ⟨inferInstance, hX₁, hsm₁, fun j => ?_, ?_⟩, ?_, ?_, ?_⟩
  · obtain ⟨E, -, hVE⟩ := exists_mem_eq_closure_of_mem_componentsOf_biUnion D ξ (e.symm j).2
    have hI : T.I j =
        (AlgebraicGeometry.PrimeDivisor.ofCoheightOne (ξ E) (hξcoh E)).idealSheaf := by
      change componentsFamily S (e.symm j) = Stacks.Chow.integralComponentAt (ξ E)
      rw [componentsFamily, Stacks.Chow.integralComponentAt]
      congr 1
      ext1
      rw [Closeds.coe_closure, Closeds.coe_closure, hVE, closure_closure]
    have hc := Aux.isEffectiveCartierDivisor_idealSheaf (f₁ ≫ sX) hsm₁
      (AlgebraicGeometry.PrimeDivisor.ofCoheightOne (ξ E) (hξcoh E))
    rw [← hI] at hc
    exact ⟨AlgebraicGeometry.ne_bot_of_isEffectiveCartierDivisor hc, hc⟩
  · refine ⟨fun i => i.elim0, fun i => i.elim0, fun x => ?_⟩
    obtain ⟨n, z, hz⟩ := hRSOP x
    exact ⟨n, z, fun i => i.1.elim0, hz, fun i => i.1.elim0, fun i => i.1.elim0⟩
  · rwa [hTsupp]
  · rwa [hTsupp]
  · intro U hU hUsnc y hy
    haveI : IsIso (f₁ ∣_ U) := TupleResolutionAux.isIso_restrict_of_le f₁ hU
    exact mem_sncLocus_componentsFamily hSc e (isSNCAt_of_isIso_restrict f₁ U hSsup
      (fun a ha haU => hSsub ⟨ha, hU haU⟩)
      (isSNCAt_of_isSNCClosedSubset (U.ι ≫ sX) (isSmoothScheme_of_le_smoothLocus sX hU) hUsnc)
      hy)

/-! ### The resolution of the tuple of strict transforms -/

/-- **Steps 1–2.** A normal variety `X` with a reduced divisor `D` has a projective morphism
`g : Y ⟶ X` from a smooth variety with an snc tuple on `Y` whose support lies between
`g⁻¹(Supp D ∩ X^ns)` and `g⁻¹(Supp D)`, and `g` is an isomorphism over every open `U ⊆ X^ns` on
which `Supp D` has simple normal crossings. -/
private theorem exists_resolution_tuple {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (hX : IsNormalVariety k sX) (D : Finset (MMP.Mori.PrimeDivisor X)) :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ X) (T : OrderedDivisorTuple Y),
      AlgebraicGeometry.IsVariety k (g ≫ sX) ∧ IsSmoothScheme (g ≫ sX) ∧ IsProjective g ∧
      T.sncLocus = Set.univ ∧
      g ⁻¹' ((D.sup fun E => (E.idealSheaf.support : Set X)) ∩ smoothLocus sX) ⊆
        tupleSupport T ∧
      tupleSupport T ⊆ g ⁻¹' (D.sup fun E => (E.idealSheaf.support : Set X)) ∧
      ∀ U : X.Opens, U ≤ smoothLocus sX →
        IsSNCClosedSubset (U.ι ≫ sX) (U.ι ⁻¹' (D.sup fun E => E.idealSheaf.support)) →
        IsIso (g ∣_ U) := by
  have hXv : AlgebraicGeometry.IsVariety k sX := hX.1
  haveI := hXv
  haveI : IsIntegral X := hXv.toIsIntegral
  haveI := isNoetherian_of_locallyOfFiniteType sX
  obtain ⟨BR, hBR, -⟩ := MMP.Resolution.exists_strongResolution_blowupSequenceFunctor.{u}
  have hDU := isDisjointUnionOfVarieties_of_isVariety sX hXv
  obtain ⟨hsm₁, hiso₁, -⟩ := hBR sX hDU
  set B₁ := BR sX hDU
  set f₁ := B₁.toBase
  haveI := hiso₁
  have hsmne : ((smoothLocus sX : X.Opens) : Set X).Nonempty := by
    rw [smoothLocus_eq_smoothLocus]
    exact (Scheme.Hom.dense_smoothLocus_of_perfectField sX).nonempty
  have hX₁ : AlgebraicGeometry.IsVariety k (f₁ ≫ sX) := isVariety_toBase B₁ sX hXv
    (let ⟨y, _⟩ := nonempty_preimage_of_isIso_restrict f₁ (smoothLocus sX) hsmne; ⟨y⟩)
  haveI := hX₁
  haveI := isNoetherian_of_locallyOfFiniteType (f₁ ≫ sX)
  obtain ⟨T, hT, hTsub, hTsup, hTsnc⟩ :=
    exists_orderedDivisorTuple_strictTransform sX hX D f₁ hX₁ hsm₁
  obtain ⟨B₂, hB₂⟩ := OrderedDivisorTuple.exists_transform_sncLocus_eq_univ (f₁ ≫ sX) T hT
  rw [TupleResolutionAux.rec_iff (f₁ ≫ sX) T.sncLocus (fun p T' => T'.sncLocus = Set.univ ∧
    ∃ U : B₁.target.Opens, T.sncLocus ⊆ U ∧ IsIso (p ∣_ U)) B₂ (𝟙 _) T] at hB₂
  simp only [Category.id_comp, Category.comp_id, Scheme.Hom.id_base, TopCat.coe_id,
    Set.preimage_id] at hB₂
  obtain ⟨hval, hfin, U₂, hU₂, hiso₂⟩ := hB₂
  rw [Category.comp_id] at hiso₂
  set f₂ := B₂.toBase
  obtain ⟨hT₂, -⟩ := TupleResolutionAux.isOrderedDivisorTuple_finalTuple B₂ hT hval
    ⟨_, TupleResolutionAux.genericPoint_mem_sncLocus hT⟩
  have hsupp₂ : tupleSupport (TupleResolutionAux.finalTuple B₂ T) = f₂ ⁻¹' tupleSupport T := by
    refine tupleSupport_finalTuple B₂ (f₁ ≫ sX) T.sncLocus T hT.2.2.2.2.2 ?_ hval
    intro x hx
    haveI : Smooth (f₁ ≫ sX) := Aux.smooth_of_isSmoothScheme' _ hsm₁
    haveI := isRegularLocalRing_stalk_of_smooth_over_field (f₁ ≫ sX) x
    obtain ⟨n, z, hz⟩ := MMP.Mori.exists_isRegularSystemOfParameters (B₁.target.presheaf.stalk x)
    exact OrderedDivisorTuple.mem_sncLocus_of_notMem_support T hz fun p hp =>
      hx (Set.mem_iUnion.2 ⟨p, hp⟩)
  refine ⟨B₂.target, f₂ ≫ f₁, TupleResolutionAux.finalTuple B₂ T, ?_, ?_,
    (ClosedBlowupSequence.isProjective_toBase B₂).comp
      (ClosedBlowupSequence.isProjective_toBase B₁), hfin, ?_, ?_, fun U hU hUsnc => ?_⟩
  · rw [Category.assoc]
    exact hT₂.2.1
  · rw [Category.assoc]
    exact hT₂.2.2.1
  · rw [hsupp₂]
    exact fun y hy => hTsub hy
  · rw [hsupp₂]
    exact fun y hy => hTsup hy
  · haveI : IsIso (f₁ ∣_ U) := TupleResolutionAux.isIso_restrict_of_le f₁ hU
    haveI := hiso₂
    haveI : IsIso (f₂ ∣_ f₁ ⁻¹ᵁ U) := TupleResolutionAux.isIso_restrict_of_le f₂ (V := U₂)
      fun y hy => hU₂ (hTsnc U hU hUsnc hy)
    exact isIso_restrict_comp f₂ f₁ U

/-- A morphism which is an isomorphism over every smooth open on which `Supp D` is snc has a
nonempty biregular locus. -/
private theorem nonempty_biregularLocus {k : Type u} [Field k] [CharZero k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (hXv : AlgebraicGeometry.IsVariety k sX)
    (D : Finset (MMP.Mori.PrimeDivisor X)) (g : Y ⟶ X)
    (key : ∀ U : X.Opens, U ≤ smoothLocus sX →
      IsSNCClosedSubset (U.ι ≫ sX) (U.ι ⁻¹' (D.sup fun E => E.idealSheaf.support)) →
      IsIso (g ∣_ U)) :
    ((biregularLocus g : X.Opens) : Set X).Nonempty := by
  haveI := hXv
  haveI : IsIntegral X := hXv.toIsIntegral
  set SD : Set X := D.sup fun E => (E.idealSheaf.support : Set X) with hSD
  have hSDc : IsClosed SD := by
    rw [hSD, Finset.sup_set_eq_biUnion]
    exact isClosed_biUnion_finset fun E _ => E.idealSheaf.support.isClosed
  have hsmne : ((smoothLocus sX : X.Opens) : Set X).Nonempty := by
    rw [smoothLocus_eq_smoothLocus]
    exact (Scheme.Hom.dense_smoothLocus_of_perfectField sX).nonempty
  set U₀ : X.Opens := smoothLocus sX ⊓ ⟨SDᶜ, hSDc.isOpen_compl⟩
  have hU₀ne : (U₀ : Set X).Nonempty :=
    ⟨genericPoint X, ((genericPoint_spec X).mem_open_set_iff (smoothLocus sX).isOpen).2
      (by simpa using hsmne), genericPoint_notMem_sup_support D⟩
  refine hU₀ne.mono (le_biregularLocus (key U₀ inf_le_left ?_))
  have : (U₀.ι ⁻¹' SD) = ∅ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
    exact x.2.2
  rw [this]
  exact ⟨isClosed_empty, Or.inl rfl⟩

/-! ### Step 3: the exceptional set -/

/-- If `g` is an isomorphism over `V`, the generic point of `Y` misses every ideal sheaf
supported on `g⁻¹(X ∖ V)`. -/
private theorem genericPoint_notMem_of_support_eq_preimage {X Y : Scheme.{u}} [IsIntegral Y]
    (g : Y ⟶ X) (V : X.Opens) (I : Y.IdealSheafData)
    (hI : (I.support : Set Y) = g ⁻¹' (V.compl : Set X))
    (hV : ((g ⁻¹ᵁ V : Y.Opens) : Set Y).Nonempty) : genericPoint Y ∉ I.support := fun h =>
  (Set.ext_iff.1 hI _).1 h
    (((genericPoint_spec Y).mem_open_set_iff (g ⁻¹ᵁ V).isOpen).2 (by simpa using hV))

/-- An ideal sheaf supported on `g⁻¹(X ∖ V)`, with `g ⁻¹ V` nonempty, is nonzero at the generic
point. -/
private theorem isNonzeroAtGenericPoints_of_support_eq_preimage {X Y : Scheme.{u}}
    [IsIntegral Y] (g : Y ⟶ X) (V : X.Opens) (I : Y.IdealSheafData)
    (hI : (I.support : Set Y) = g ⁻¹' (V.compl : Set X))
    (hV : ((g ⁻¹ᵁ V : Y.Opens) : Set Y).Nonempty) : IsNonzeroAtGenericPoints I := by
  intro η hη
  rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hη
  rw [(show IsGenericPoint η ⊤ from hη).eq (genericPoint_spec _),
    (IdealSheafData.stalk_eq_top_iff_notMem_support _ _).2
      (genericPoint_notMem_of_support_eq_preimage g V I hI hV)]
  exact top_ne_bot

/-- The support of the ordered divisor listing the ideals and boundary of a tuple is the support
of the tuple. -/
private theorem support_divisors_finSumFinEquiv {V : Scheme.{u}} (T : OrderedDivisorTuple V) :
    (⟨T.m + T.E.s, fun i => T.divisors (finSumFinEquiv.symm i)⟩ : OrderedDivisor V).support =
      tupleSupport T := by
  ext x
  simp only [OrderedDivisor.support, tupleSupport, Set.mem_iUnion]
  refine ⟨fun ⟨i, hi⟩ => ⟨_, hi⟩, fun ⟨p, hp⟩ => ⟨finSumFinEquiv p, ?_⟩⟩
  change x ∈ (T.divisors (finSumFinEquiv.symm (finSumFinEquiv p))).support
  rwa [Equiv.symm_apply_apply]

/-- **Exceptional set of a principalization.** If `f` is an isomorphism over `V`, the complement
`Z = X ∖ V` has codimension at least two, and an ideal sheaf with principal stalks has support
`f⁻¹(Z)`, then `Ex(f) = f⁻¹(Z)`. -/
private theorem exceptionalSet_eq_preimage_of_two_le_closedsCodimension {X Y : Scheme.{u}}
    [IsLocallyNoetherian Y] [NoetherianSpace Y] (f : Y ⟶ X) (V : X.Opens) [IsIso (f ∣_ V)]
    (I : Y.IdealSheafData) (hI : ∀ y, ∃ h, IdealSheafData.stalk I y = Ideal.span {h})
    (hsupp : (I.support : Set Y) = f ⁻¹' (V.compl : Set X))
    (hcodim : 2 ≤ closedsCodimension V.compl) :
    (exceptionalSet f : Set Y) = f ⁻¹' (V.compl : Set X) := by
  refine Set.Subset.antisymm (fun y hy hyZ => hy (le_biregularLocus ‹IsIso (f ∣_ V)› hyZ)) ?_
  intro y hy hyV
  rw [← hsupp] at hy
  obtain ⟨η, hηS, hηy, hηmax⟩ := exists_maximal_generization I.support hy
  have h1 := coheight_le_one_of_principal I hI hηS hηmax
  haveI : IsIso (f ∣_ biregularLocus f) := isBiregular_biregularLocus f
  have hηV : f η ∈ biregularLocus f := (hηy.map f.continuous).mem_open
    (biregularLocus f).isOpen hyV
  have h3 := (MMP.Flips.le_closedsCodimension_iff_le_coheight.1 hcodim) _
    ((Set.ext_iff.1 hsupp η).1 hηS)
  rw [coheight_apply_of_isIso_restrict f (biregularLocus f) hηV] at h3
  exact absurd (h3.trans h1) (by norm_num)

/-- After an order-one reduction `B` of an ideal `I` with support `g⁻¹(X ∖ V)`, the preimage of
`(X ∖ V) ∪ S` is the support of the final boundary, provided the initial boundary lies between
`g⁻¹(S) ∩ g⁻¹(V)` and `g⁻¹(S)`. -/
private theorem preimage_compl_union_preimage_eq_support {k : Type u} [Field k]
    {X Y : Scheme.{u}} (g : Y ⟶ X) (V : X.Opens) (B : ClosedBlowupSequence Y)
    (s : Y ⟶ Spec (.of k)) (I : Y.IdealSheafData) (E : OrderedDivisor Y)
    (hB : B.IsOrderGeMarkedTripleSeq s ⟨I, 1⟩ E) (S : Set X)
    (hI : (I.support : Set Y) = g ⁻¹' (V.compl : Set X))
    (hexc : (B.exceptionalIdeal.support : Set B.target) = (B.toBase ≫ g) ⁻¹' (V.compl : Set X))
    (hsub : ∀ y, g y ∈ S → g y ∈ V → y ∈ E.support) (hsup : E.support ⊆ g ⁻¹' S) :
    (B.toBase ≫ g) ⁻¹' (V.compl : Set X) ∪ (B.toBase ≫ g) ⁻¹' S =
      (B.orderedTotalTransform E).support := by
  refine Set.Subset.antisymm (Set.union_subset ?_ fun y hy => ?_) fun y hy => ?_
  · rw [← hexc]
    exact ClosedBlowupSequence.support_exceptionalIdeal_subset B _ _ _ hB
  · by_cases hyZ : (B.toBase ≫ g) y ∈ (V.compl : Set X)
    · exact ClosedBlowupSequence.support_exceptionalIdeal_subset B _ _ _ hB
        ((Set.ext_iff.1 hexc y).2 hyZ)
    · exact ClosedBlowupSequence.preimage_support_subset_support_orderedTotalTransform
        B _ _ _ hB (hsub _ hy (not_not.1 hyZ))
  · rcases support_orderedTotalTransform_subset B _ _ _ hB hy with h | h
    · exact Or.inr (hsup h)
    · exact Or.inl ((Set.ext_iff.1 hI _).1 (cosupport_one_subset I h))

/-- The pullback `g^* I_Z` of the ideal of a closed set `Z` is supported on `g⁻¹(Z)`. -/
private theorem coe_support_comap_vanishingIdeal {X Y : Scheme.{u}} (g : Y ⟶ X)
    (Z : Closeds X) :
    (((Scheme.IdealSheafData.vanishingIdeal Z).comap g).support : Set Y) = g ⁻¹' (Z : Set X) := by
  rw [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage,
    Scheme.IdealSheafData.coe_support_vanishingIdeal]

/-- **Step 3: principalization.** If `g` is an isomorphism over a nonempty open `V`, from a smooth
variety carrying a tuple `T` with snc locus everything, a marked order-one reduction of
`g^* I_{X ∖ V}` with boundary the divisors of `T` is an isomorphism over `g⁻¹(V)`, and its
exceptional ideal is supported on the preimage of `X ∖ V`. -/
private theorem exists_principalization {k : Type u} [Field k] [CharZero k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (g : Y ⟶ X) (hY : AlgebraicGeometry.IsVariety k (g ≫ sX))
    (hsm : IsSmoothScheme (g ≫ sX)) (T : OrderedDivisorTuple Y) (hT : T.sncLocus = Set.univ)
    (V : X.Opens) [IsIso (g ∣_ V)] (hV : (V : Set X).Nonempty) :
    ∃ (B : ClosedBlowupSequence Y) (E : OrderedDivisor Y), E.support = tupleSupport T ∧
      B.IsOrderGeMarkedTripleSeq (g ≫ sX)
        ⟨(Scheme.IdealSheafData.vanishingIdeal V.compl).comap g, 1⟩ E ∧
      IsIso (B.toBase ∣_ (g ⁻¹ᵁ V)) ∧
      (B.exceptionalIdeal.support : Set B.target) = (B.toBase ≫ g) ⁻¹' (V.compl : Set X) := by
  haveI := hY
  haveI : IsIntegral Y := hY.toIsIntegral
  haveI := isNoetherian_of_locallyOfFiniteType (g ≫ sX)
  set I : Y.IdealSheafData := (Scheme.IdealSheafData.vanishingIdeal V.compl).comap g
  have hI : (I.support : Set Y) = g ⁻¹' (V.compl : Set X) :=
    coe_support_comap_vanishingIdeal g V.compl
  set E : OrderedDivisor Y := ⟨T.m + T.E.s, fun i => T.divisors (finSumFinEquiv.symm i)⟩
  let t : MarkedTriple.{u} := ⟨⟨⟨Y, I, E⟩, k, g ≫ sX⟩, 1⟩
  have ht : t ∈ markedTriplesOfDim Set.univ 1 :=
    ⟨⟨inferInstance, hsm, (inferInstance : LocallyOfFiniteType (g ≫ sX)),
      (inferInstance : QuasiCompact (g ≫ sX)),
      TopologicalSpace.Equidimensional.of_preirreducibleSpace _,
      isNonzeroAtGenericPoints_of_support_eq_preimage g V I hI
        (nonempty_preimage_of_isIso_restrict g V hV),
      isOrderedSNC_of_sncLocus_eq_univ _ T hT⟩, rfl,
      hasDimensionIn_univ_of_locallyOfFiniteType (g ≫ sX)⟩
  obtain ⟨F, -, hFR⟩ := exists_isOrderReductionFunctorMarked_bmoFamily.{u} 1 le_rfl
  set B : ClosedBlowupSequence Y := F.toFun t ht
  have hB : B.IsOrderGeMarkedTripleSeq (g ≫ sX) ⟨I, 1⟩ E := F.isOrderGeMarkedTripleSeq t ht
  have hmax : maxOrder (B.markedTransform ⟨I, 1⟩).I < 1 := hFR.1 t ht
  have hexc : I.comap B.toBase = B.exceptionalIdeal := by
    rw [ClosedBlowupSequence.comap_toBase_eq_markedTransform_mul_exceptionalIdeal B _
      ⟨I, 1⟩ E rfl hB, eq_top_of_maxOrder_lt_one hmax,
      ← Scheme.IdealSheafData.one_eq_top, one_mul]
  refine ⟨B, E, support_divisors_finSumFinEquiv T, hB,
    isIso_restrict_of_disjoint_cosupport B _ _ _ hB _ (Set.disjoint_left.2 fun y hy hyV =>
      (Set.ext_iff.1 hI y).1 (cosupport_one_subset I hy) hyV), ?_⟩
  rw [← hexc, Scheme.IdealSheafData.support_comap, Closeds.coe_preimage, hI]
  rfl

end Proof_thm_mmp_snc_preserving_log_resolution

namespace MMP.Resolution

open Proof_thm_mmp_snc_preserving_log_resolution

/-- **Log resolution preserving the snc locus.** For a normal variety `X` over a field `k` of
characteristic zero and a reduced divisor `D = D₁ + ⋯ + D_r` on `X` (given by its prime
components), there is a projective birational morphism `f : Y ⟶ X` from a smooth variety such
that `Ex(f)` is of pure codimension one, `Ex(f) ∪ f⁻¹(Supp D)` is a divisor with simple normal
crossings on `Y`, and `f` is an isomorphism over every open `U ⊆ X` smooth over `k` on which
`D ∩ U` has simple normal crossings. -/
@[mmp "thm_mmp_snc_preserving_log_resolution"]
public theorem exists_isLogResolution_isIso_restrict_of_isSNCClosedSubset {k : Type u} [Field k]
    [CharZero k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (hX : MMP.Mori.IsNormalVariety k sX)
    (D : Finset (MMP.Mori.PrimeDivisor X)) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X),
      IsResolutionOfVariety sX f ∧
      MMP.Mori.IsPureCodimOne (MMP.Mori.exceptionalSet f) ∧
      IsSNCClosedSubset (f ≫ sX)
        ((MMP.Mori.exceptionalSet f : Set Y) ∪ f ⁻¹' (D.sup fun E => E.idealSheaf.support)) ∧
      ∀ U : X.Opens, MMP.Mori.IsSmoothScheme (U.ι ≫ sX) →
        IsSNCClosedSubset (U.ι ≫ sX) (U.ι ⁻¹' (D.sup fun E => E.idealSheaf.support)) →
        IsIso (f ∣_ U) := by
  have hXv : AlgebraicGeometry.IsVariety k sX := hX.1
  haveI := hXv
  haveI : IsIntegral X := hXv.toIsIntegral
  haveI : IsNormal X := hX.2
  haveI := isNoetherian_of_locallyOfFiniteType sX
  obtain ⟨Y₂, g, T₂, hX₂, hsm₂, hgproj, hfin, hTsub, hTsup, key⟩ :=
    exists_resolution_tuple sX hX D
  set SD : Set X := D.sup fun E => (E.idealSheaf.support : Set X)
  haveI := hX₂
  haveI : IsIntegral Y₂ := hX₂.toIsIntegral
  haveI := isNoetherian_of_locallyOfFiniteType (g ≫ sX)
  set V : X.Opens := biregularLocus g
  haveI : IsIso (g ∣_ V) := isBiregular_biregularLocus g
  have hVne : (V : Set X).Nonempty := nonempty_biregularLocus sX hXv D g key
  haveI : IsProper g := hgproj.isProper
  have hcodim : 2 ≤ closedsCodimension V.compl := two_le_closedsCodimension_compl_biregularLocus
    sX g (isBirationalMorphism_of_isIso_restrict g V hVne)
  obtain ⟨B₃, E₂, hE₂supp, hB₃, hB₃V, hexcsupp⟩ :=
    exists_principalization sX g hX₂ hsm₂ T₂ hfin V hVne
  haveI := hB₃V
  set f : B₃.target ⟶ X := B₃.toBase ≫ g with hf
  haveI : IsIso (f ∣_ V) := isIso_restrict_comp B₃.toBase g V
  have hfin₃ := ClosedBlowupSequence.isTriple_target_of_isOrderGeMarkedTripleSeq B₃ _ _ _ hB₃
  have hfVne := nonempty_preimage_of_isIso_restrict f V hVne
  have hY : AlgebraicGeometry.IsVariety k (f ≫ sX) := by
    rw [hf, Category.assoc]
    exact isVariety_toBase B₃ _ hX₂ (let ⟨y, _⟩ := hfVne; ⟨y⟩)
  haveI := hY
  haveI : IsIntegral B₃.target := hY.toIsIntegral
  haveI := isNoetherian_of_locallyOfFiniteType (f ≫ sX)
  have hprin := ClosedBlowupSequence.exists_stalk_exceptionalIdeal_eq_span B₃
  have hEx : (exceptionalSet f : Set B₃.target) = f ⁻¹' (V.compl : Set X) :=
    exceptionalSet_eq_preimage_of_two_le_closedsCodimension f V _ hprin hexcsupp hcodim
  refine ⟨B₃.target, f, ⟨hXv, hY, (ClosedBlowupSequence.isProjective_toBase B₃).comp hgproj,
    isBirationalMorphism_of_isIso_restrict f V hVne, ?_⟩, ?_, ?_, fun U hU hUsnc => ?_⟩
  · rw [hf, Category.assoc]
    exact hfin₃.2.1
  · rw [show exceptionalSet f = B₃.exceptionalIdeal.support from
      Closeds.ext (hEx.trans hexcsupp.symm)]
    exact isPureCodimOne_support_of_principal B₃.exceptionalIdeal hprin
      (genericPoint_notMem_of_support_eq_preimage f V _ hexcsupp hfVne)
  · have hEf : (B₃.orderedTotalTransform E₂).IsSNC (f ≫ sX) := by
      rw [hf, Category.assoc]
      exact hfin₃.2.2.2.2.2.2.2
    have hS : (exceptionalSet f : Set B₃.target) ∪ f ⁻¹' SD =
        (B₃.orderedTotalTransform E₂).support := by
      rw [hEx]
      refine preimage_compl_union_preimage_eq_support g V B₃ _ _ E₂ hB₃ SD
        (coe_support_comap_vanishingIdeal g V.compl) hexcsupp
        (fun y hy hyV => ?_) (by rw [hE₂supp]; exact hTsup)
      rw [hE₂supp]
      exact hTsub ⟨hy, biregularLocus_le_smoothLocus sX g hsm₂ hyV⟩
    rw [hS]
    exact isSNCClosedSubset_iUnion_of_isSNCFamily (f ≫ sX) _ hEf
  · exact TupleResolutionAux.isIso_restrict_of_le f
      (le_biregularLocus (key U (le_smoothLocus_of_isSmoothScheme sX hU) hUsnc))

end MMP.Resolution
