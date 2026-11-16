module

public import MMP.AlgebraicGeometry.Resolution.DivisorTupleRestrictionLift
public import MMP.AlgebraicGeometry.Resolution.DivisorTuple.FirstDivisorSmooth

/-!
# Sequences of order-one transformations of ordered divisor tuples

Auxiliary results for the snc-preserving resolution of ordered divisor tuples
(`(V, (I_1, …, I_m), E)` over a field of characteristic zero). A sequence of order-one
transformations is a `MMP.Resolution.ClosedBlowupSequence`; its final tuple and final ideals are
computed stage by stage. A sequence is *valid* away from a set `N` when every centre is a centre
of an order-one transformation of the current tuple and misses the inverse image of `N`, and
*strongly valid* when every centre misses the snc locus of the tuple it transforms.

The results here: valid sequences compose and are isomorphisms over the complement of the
inverse image of `N`; a transformation does not change the tuple near a point off its centre;
order-one transforms of ordered divisor tuples are ordered divisor tuples; snc of a tuple at
a point of a smooth divisor `H` transverse to the boundary is equivalent to snc of the
restricted tuple on `H`; sequences on `H` lift to the ambient variety carrying a stage
predicate; and a smooth divisor splits into its components, along which tuples restrict.

## Main definitions

* `MMP.Resolution.TupleResolutionAux.finalTuple`: the tuple at the end of a blow-up sequence.
* `MMP.Resolution.TupleResolutionAux.Valid`, `MMP.Resolution.TupleResolutionAux.ValidS`:
  sequences valid away from `N`, and strongly valid ones (centres miss the snc locus).
* `MMP.Resolution.TupleResolutionAux.Resolvable`: a tuple has a valid sequence ending snc.

## Main results

* `MMP.Resolution.TupleResolutionAux.exists_isIso_of_valid`.
* `MMP.Resolution.TupleResolutionAux.mem_sncLocus_transform_of_notMem`.
* `MMP.Resolution.TupleResolutionAux.exists_lift_gen`.
* `MMP.Resolution.TupleResolutionAux.exists_validS_restriction_step`.

## Implementation notes

The lifting of sequences from a smooth divisor `H` uses the construction behind
`MMP.Resolution.OrderedDivisorTuple.exists_isPushforward_transform_restrict`
(namespace `MMP.Resolution.Internal.TupleRestrictionLift`), with the additional fact
`isSNCFamily_transform_of_le` that the strict transform of `H` stays snc with the boundary for
any centre containing `H`'s ideal.

## References

* [J. Kollár, *Semi log resolutions*, arXiv:0812.3592, Proposition 6]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MMP.Resolution
open MMP.Resolution.Internal.TupleRestrictionLift

universe u

namespace MMP.Resolution.TupleResolutionAux

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-! ### Sequences of order-one transformations -/

/-- The tuple at the end of a blow-up sequence, transformed stage by stage. -/
noncomputable def finalTuple : {S : Scheme.{u}} → (B : ClosedBlowupSequence S) →
    OrderedDivisorTuple S → OrderedDivisorTuple B.target
  | _, .nil _, T => T
  | _, .cons Z B, T => finalTuple B (T.transform Z)

/-- The final tuple has as many ideals as the original one. -/
theorem finalTuple_m : ∀ {S : Scheme.{u}} (B : ClosedBlowupSequence S)
    (T : OrderedDivisorTuple S), (finalTuple B T).m = T.m := by
  intro S B
  induction B with
  | nil S => intro T; rfl
  | cons Z B ih => intro T; exact ih (T.transform Z)

/-- The order-one transform of a single ideal along the blow-up of `C`. -/
noncomputable def transformIdeal {X : Scheme.{u}} (C K : X.IdealSheafData) :
    (blowUp C).IdealSheafData := by
  classical
  exact if (C.support : Set X) ⊆ K.support then
    idealColon (K.comap (blowUpToBase C)) (C.comap (blowUpToBase C))
  else K.comap (blowUpToBase C)

/-- The order-one transform of a single ideal along a blow-up sequence. -/
noncomputable def finalIdeal : {S : Scheme.{u}} → (B : ClosedBlowupSequence S) →
    S.IdealSheafData → B.target.IdealSheafData
  | _, .nil _, K => K
  | _, .cons Z B, K => finalIdeal B (transformIdeal Z K)

/-- The ideals of the order-one transform of a tuple are the order-one transforms of its ideals. -/
theorem transform_I_eq_transformIdeal {X : Scheme.{u}} (T : OrderedDivisorTuple X)
    (C : X.IdealSheafData) (j : Fin T.m) : (T.transform C).I j = transformIdeal C (T.I j) := by
  classical
  by_cases h : (C.support : Set X) ⊆ (T.I j).support
  · rw [OrderedDivisorTuple.transform_I_of_le _ _ _ h, transformIdeal, if_pos h]
  · rw [OrderedDivisorTuple.transform_I_of_not_le _ _ _ h, transformIdeal, if_neg h]

/-- The ideals of the final tuple are the final transforms of the original ideals. -/
theorem finalTuple_I : ∀ {S : Scheme.{u}} (B : ClosedBlowupSequence S)
    (T : OrderedDivisorTuple S) (j : Fin T.m),
    (finalTuple B T).I ⟨j, by rw [finalTuple_m]; exact j.2⟩ = finalIdeal B (T.I j) := by
  intro S B
  induction B with
  | nil S => intro T j; rfl
  | cons Z B ih =>
    intro T j
    exact (ih (T.transform Z) j).trans (congrArg (finalIdeal B)
      (transform_I_eq_transformIdeal T Z j))

/-- `B` is a sequence of order-one transformations of `T` whose centres miss the inverse
images of `N ⊆ S`. -/
def Valid {k : Type u} [Field k] : {S : Scheme.{u}} → (S ⟶ Spec (.of k)) → Set S →
    ClosedBlowupSequence S → OrderedDivisorTuple S → Prop
  | _, _, _, .nil _, _ => True
  | _, s, N, .cons Z B, T => T.IsTransformCentre s Z ∧ Disjoint (Z.support : Set _) N ∧
      Valid (blowUpToBase Z ≫ s) (blowUpToBase Z ⁻¹' N) B (T.transform Z)

/-- Unfolding the recursive admissibility condition of a sequence into `Valid` together with the
condition at the last stage. -/
theorem rec_iff {k : Type u} [Field k] {V : Scheme.{u}} (sV : V ⟶ Spec (.of k))
    (N : Set V) (P : ∀ {S : Scheme.{u}}, (S ⟶ V) → OrderedDivisorTuple S → Prop) :
    ∀ {S : Scheme.{u}} (B : ClosedBlowupSequence S) (p : S ⟶ V) (T' : OrderedDivisorTuple S),
      ClosedBlowupSequence.rec
        (motive := fun S _ => (S ⟶ V) → OrderedDivisorTuple S → Prop)
        (fun _ p T' => P p T')
        (fun Z _ ih p T' => T'.IsTransformCentre (p ≫ sV) Z ∧
          Disjoint (Z.support : Set _) (p ⁻¹' N) ∧
          ih (blowUpToBase Z ≫ p) (T'.transform Z))
        B p T' ↔ Valid (p ≫ sV) (p ⁻¹' N) B T' ∧ P (B.toBase ≫ p) (finalTuple B T') := by
  intro S B
  induction B with
  | nil S =>
    intro p T'
    simp only [Valid, finalTuple, ClosedBlowupSequence.toBase, true_and]
    change P p T' ↔ P (𝟙 S ≫ p) T'
    rw [Category.id_comp]
  | cons Z B ih =>
    intro p T'
    refine (and_congr_right fun _ => and_congr_right fun _ => ih _ _).trans ?_
    simp only [Valid, finalTuple, ClosedBlowupSequence.toBase, Category.assoc,
      Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp]
    tauto

/-- `B` is a sequence of order-one transformations of `T` each of whose centres misses the snc
locus of the tuple it transforms. -/
def ValidS {k : Type u} [Field k] : {S : Scheme.{u}} → (S ⟶ Spec (.of k)) →
    ClosedBlowupSequence S → OrderedDivisorTuple S → Prop
  | _, _, .nil _, _ => True
  | _, s, .cons Z B, T => T.IsTransformCentre s Z ∧ Disjoint (Z.support : Set _) T.sncLocus ∧
      ValidS (blowUpToBase Z ≫ s) B (T.transform Z)

/-- A sequence whose centres miss both the inverse images of `N` and the snc loci of the tuples
they transform is strongly valid. -/
theorem validS_of_rec {k : Type u} [Field k] {V : Scheme.{u}} (sV : V ⟶ Spec (.of k))
    (N : Set V) (P : ∀ {S : Scheme.{u}}, (S ⟶ V) → OrderedDivisorTuple S → Prop) :
    ∀ {S : Scheme.{u}} (B : ClosedBlowupSequence S) (p : S ⟶ V) (T' : OrderedDivisorTuple S),
      ClosedBlowupSequence.rec
        (motive := fun S _ => (S ⟶ V) → OrderedDivisorTuple S → Prop)
        (fun _ p T' => P p T')
        (fun Z _ ih p T' => T'.IsTransformCentre (p ≫ sV) Z ∧
          Disjoint (Z.support : Set _) (p ⁻¹' N) ∧
          Disjoint (Z.support : Set _) T'.sncLocus ∧
          ih (blowUpToBase Z ≫ p) (T'.transform Z))
        B p T' → ValidS (p ≫ sV) B T' ∧ P (B.toBase ≫ p) (finalTuple B T') := by
  intro S B
  induction B with
  | nil S =>
    intro p T' h
    refine ⟨trivial, ?_⟩
    change P (𝟙 S ≫ p) T'
    rwa [Category.id_comp]
  | cons Z B ih =>
    intro p T' h
    obtain ⟨hc, -, hd, h⟩ := h
    obtain ⟨h1, h2⟩ := ih _ _ h
    simp only [ValidS, finalTuple, ClosedBlowupSequence.toBase, Category.assoc] at h1 h2 ⊢
    exact ⟨⟨hc, hd, h1⟩, h2⟩

/-- The strict transform of a set along a blow-up sequence: stage by stage the closure of the
preimage of the part off the centre. -/
noncomputable def strictTransformSet : {S : Scheme.{u}} → (B : ClosedBlowupSequence S) → Set S →
    Set B.target
  | _, .nil _, A => A
  | _, .cons Z B, A => strictTransformSet B (closure (blowUpToBase Z ⁻¹' (A \ Z.support)))

/-- Over an open on which a morphism is an isomorphism, every point has a preimage. -/
theorem mem_range_of_isIso_restrict {X Y : Scheme.{u}} (p : Y ⟶ X) (U : X.Opens)
    [IsIso (p ∣_ U)] {x : X} (hx : x ∈ U) : x ∈ Set.range p := by
  have : Surjective (p ∣_ U) := inferInstance
  obtain ⟨y', hy'⟩ := (p ∣_ U).surjective ⟨x, hx⟩
  refine ⟨(p ⁻¹ᵁ U).ι y', ?_⟩
  rw [← Scheme.Hom.comp_apply, ← morphismRestrict_ι, Scheme.Hom.comp_apply, hy']
  rfl

/-- An isomorphism over an open restricts to an isomorphism over every smaller open. -/
theorem isIso_restrict_of_le {X Y : Scheme.{u}} (f : X ⟶ Y) {U V : Y.Opens} (h : U ≤ V)
    [IsIso (f ∣_ V)] : IsIso (f ∣_ U) := by
  have e1 := morphismRestrictRestrict f V (V.ι ⁻¹ᵁ U)
  have hU : V.ι ''ᵁ (V.ι ⁻¹ᵁ U) = U := by
    ext x
    simp only [Scheme.Hom.coe_image, Scheme.Hom.coe_preimage, Scheme.Opens.range_ι,
      Set.image_preimage_eq_inter_range, Set.mem_inter_iff, SetLike.mem_coe]
    exact ⟨fun h => h.1, fun hx => ⟨hx, h hx⟩⟩
  exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (e1.trans (morphismRestrictEq f hU))).1 (inferInstanceAs (IsIso _))

/-- The composite of a sequence whose centres miss the inverse images of `N` is an isomorphism
over an open neighbourhood of `N`. -/
theorem exists_isIso_of_valid {k : Type u} [Field k] :
    ∀ {S : Scheme.{u}} (B : ClosedBlowupSequence S) [IsLocallyNoetherian S]
      (s : S ⟶ Spec (.of k)) (N : Set S) (T : OrderedDivisorTuple S), Valid s N B T →
      ∃ U : S.Opens, N ⊆ U ∧ IsIso (B.toBase ∣_ U) := by
  intro S B
  induction B with
  | nil S =>
    intro _ s N T _
    refine ⟨⊤, fun x _ => trivial, ?_⟩
    change IsIso (𝟙 S ∣_ ⊤)
    infer_instance
  | @cons X Z B ih =>
    intro _ s N T h
    obtain ⟨-, hZ, hB⟩ := h
    have : IsLocallyNoetherian (blowUp Z) :=
      LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase Z)
    obtain ⟨U', hU', hiso⟩ := ih (blowUpToBase Z ≫ s) _ _ hB
    set π := blowUpToBase Z
    have hC : IsClosed (π '' (U' : Set (blowUp Z))ᶜ) :=
      π.isClosedMap _ U'.isOpen.isClosed_compl
    let W : X.Opens := ⟨((Z.support : Set X))ᶜ, Z.support.isClosed.isOpen_compl⟩
    let U : X.Opens := W ⊓ ⟨(π '' (U' : Set (blowUp Z))ᶜ)ᶜ, hC.isOpen_compl⟩
    refine ⟨U, fun x hx => ⟨hZ.notMem_of_mem_right hx, ?_⟩, ?_⟩
    · rintro ⟨y, hy, rfl⟩
      exact hy (hU' hx)
    · have : IsIso (π ∣_ W) := isIso_blowUp_restrict_compl_support Z
      have h1 : IsIso (π ∣_ U) := isIso_restrict_of_le π inf_le_left
      have h2 : IsIso (B.toBase ∣_ (π ⁻¹ᵁ U)) := by
        refine isIso_restrict_of_le B.toBase (V := U') fun y hy => ?_
        by_contra hy'
        exact hy.2 ⟨y, hy', rfl⟩
      change IsIso ((B.toBase ≫ π) ∣_ U)
      rw [morphismRestrict_comp]
      exact @IsIso.comp_isIso _ _ _ _ _ _ _ h2 h1

/-! ### Simple normal crossings of a family at a point -/

section SNCAt

variable {X : Scheme.{u}}

/-- A family of ideal sheaves is *snc at `x`*: the members through `x` are distinct coordinate
hyperplanes of a regular system of parameters of `𝒪_{X,x}`. -/
def IsSNCAt {Λ : Type*} (D : Λ → X.IdealSheafData) (x : X) : Prop :=
  ∃ (n : ℕ) (z : Fin n → X.presheaf.stalk x) (c : {i // x ∈ (D i).support} → Fin n),
    MMP.Mori.IsRegularSystemOfParameters z ∧ Function.Injective c ∧
      ∀ i, IdealSheafData.stalk (D i.1) x = Ideal.span {z (c i)}

/-- A point lies in the snc locus of a tuple exactly when the tuple's divisors are snc at it. -/
theorem mem_sncLocus_iff (T : OrderedDivisorTuple X) (x : X) :
    x ∈ T.sncLocus ↔ IsSNCAt T.divisors x := Iff.rfl

/-- Snc at a point passes to a family whose members through the point are, injectively, members
of the given family through it, with the same stalks. -/
theorem IsSNCAt.of_injective {Λ Λ' : Type*} {D : Λ → X.IdealSheafData}
    {D' : Λ' → X.IdealSheafData} {x : X} (h : IsSNCAt D x)
    (f : {i' // x ∈ (D' i').support} → {i // x ∈ (D i).support}) (hf : Function.Injective f)
    (hst : ∀ i', IdealSheafData.stalk (D' i'.1) x = IdealSheafData.stalk (D (f i').1) x) :
    IsSNCAt D' x := by
  obtain ⟨n, z, c, hz, hc, hzc⟩ := h
  exact ⟨n, z, c ∘ f, hz, hc.comp hf, fun i' => (hst i').trans (hzc _)⟩

/-- Snc at a point transported along a morphism whose stalk map there is an isomorphism. -/
theorem IsSNCAt.of_stalkMap {Y : Scheme.{u}} (g : Y ⟶ X) (y : Y) [IsIso (g.stalkMap y)]
    {Λ Λ' : Type*} {D : Λ → X.IdealSheafData} {D' : Λ' → Y.IdealSheafData}
    (h : IsSNCAt D (g y))
    (f : {i' // y ∈ (D' i').support} → {i // g y ∈ (D i).support}) (hf : Function.Injective f)
    (hst : ∀ i', IdealSheafData.stalk (D' i'.1) y =
      (IdealSheafData.stalk (D (f i').1) (g y)).map (g.stalkMap y).hom) :
    IsSNCAt D' y := by
  obtain ⟨n, z, c, hz, hc, hzc⟩ := h
  let e : X.presheaf.stalk (g y) ≃+* Y.presheaf.stalk y :=
    (asIso (g.stalkMap y)).commRingCatIsoToRingEquiv
  refine ⟨n, fun j => e (z j), c ∘ f, hz.map_ringEquiv e, hc.comp hf, fun i' => ?_⟩
  rw [hst, hzc, Ideal.map_span, Set.image_singleton]
  rfl

end SNCAt

/-! ### Stalks of the transformed tuple away from the centre -/

section AwayFromCentre

variable {X : Scheme.{u}}

/-- `(A : B)·B ≤ A`. -/
theorem idealColon_mul_le (A B : X.IdealSheafData) : idealColon A B * B ≤ A := by
  intro U
  rw [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply]
  refine (Ideal.mul_mono_left (Scheme.IdealSheafData.ideal_ofIdeals_le _ U)).trans ?_
  rw [Ideal.mul_le]
  intro a ha b hb
  simpa [mul_comm] using Submodule.mem_colon.1 ha b hb

/-- Away from the cosupport of `B`, the ideal quotient `(A : B)` has the stalks of `A`. -/
theorem stalk_idealColon_of_notMem (A B : X.IdealSheafData) {x : X}
    (hx : x ∉ B.support) : IdealSheafData.stalk (idealColon A B) x = IdealSheafData.stalk A x := by
  refine le_antisymm ?_ (MMP.Resolution.stalk_le_stalk_of_le (le_idealColon A B) x)
  have h := MMP.Resolution.stalk_le_stalk_of_le (idealColon_mul_le A B) x
  rwa [IdealSheafData.stalk_mul, (IdealSheafData.stalk_eq_top_iff_notMem_support B x).2 hx,
    Ideal.mul_top] at h

/-- On `Spec 𝒪_{B,y}`, `y` off the exceptional locus of `B = B_ZX`, the closure of `π⁻¹(A ∖ C)`
(`A` closed, `C ⊆ Z` closed) is the inverse image of `A`. -/
theorem fromSpecStalk_mem_closure_preimage_diff_iff_of_notMem [IsLocallyNoetherian X]
    [CompactSpace X] {Z : X.IdealSheafData} (y : blowUp Z)
    (hy : blowUpToBase Z y ∉ Z.support) {A C : Set X} (hA : IsClosed A) (hC : IsClosed C)
    (hCZ : C ⊆ Z.support) (p : PrimeSpectrum ((blowUp Z).presheaf.stalk y)) :
    (blowUp Z).fromSpecStalk y p ∈ closure (blowUpToBase Z ⁻¹' (A \ C)) ↔
      X.fromSpecStalk (blowUpToBase Z y)
        (PrimeSpectrum.comap ((blowUpToBase Z).stalkMap y).hom p) ∈ A := by
  rw [fromSpecStalk_mem_closure_preimage_diff_iff y hA hC]
  simp only [apply_fromSpecStalk]
  constructor
  · rintro ⟨q, hqp, hqA, -⟩
    have hsp : PrimeSpectrum.comap ((blowUpToBase Z).stalkMap y).hom q ⤳
        PrimeSpectrum.comap ((blowUpToBase Z).stalkMap y).hom p :=
      (PrimeSpectrum.le_iff_specializes _ _).1 (Ideal.comap_mono hqp)
    exact (hsp.map (X.fromSpecStalk (blowUpToBase Z y)).continuous).mem_closed hA hqA
  · intro h
    refine ⟨p, le_rfl, h, fun hC' => hy ?_⟩
    exact (fromSpecStalk_specializes_self _ _).mem_closed Z.support.isClosed (hCZ hC')

/-- Off the exceptional locus, `y ∈ closure (π⁻¹(A ∖ C))` exactly when `π y ∈ A`. -/
theorem mem_closure_preimage_diff_iff_of_notMem [IsLocallyNoetherian X]
    [CompactSpace X] {Z : X.IdealSheafData} (y : blowUp Z)
    (hy : blowUpToBase Z y ∉ Z.support) {A C : Set X} (hA : IsClosed A) (hC : IsClosed C)
    (hCZ : C ⊆ Z.support) :
    y ∈ closure (blowUpToBase Z ⁻¹' (A \ C)) ↔ blowUpToBase Z y ∈ A := by
  have h := fromSpecStalk_mem_closure_preimage_diff_iff_of_notMem y hy hA hC hCZ
    (IsLocalRing.closedPoint _)
  rwa [Scheme.fromSpecStalk_closedPoint, IsLocalRing.comap_closedPoint,
    Scheme.fromSpecStalk_closedPoint] at h

/-- Off the exceptional locus, the reduced closure of `π⁻¹(cosupp K ∖ C)` has, at `y`, the stalk
of `K` at `π y` carried over, when that stalk is a principal prime. -/
theorem stalk_vanishingIdeal_closure_preimage_of_notMem [IsLocallyNoetherian X]
    [CompactSpace X] {Z : X.IdealSheafData} (y : blowUp Z)
    (hy : blowUpToBase Z y ∉ Z.support) (K : X.IdealSheafData) {C : Set X} (hC : IsClosed C)
    (hCZ : C ⊆ Z.support) [IsIso ((blowUpToBase Z).stalkMap y)]
    {a : X.presheaf.stalk (blowUpToBase Z y)}
    (ha : IdealSheafData.stalk K (blowUpToBase Z y) = Ideal.span {a})
    (hprime : (Ideal.span {a}).IsPrime) :
    IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal
        (TopologicalSpace.Closeds.closure (blowUpToBase Z ⁻¹' ((K.support : Set X) \ C)))) y =
      Ideal.span {((blowUpToBase Z).stalkMap y).hom a} := by
  set φ := ((blowUpToBase Z).stalkMap y).hom
  let e : X.presheaf.stalk (blowUpToBase Z y) ≃+* (blowUp Z).presheaf.stalk y :=
    (asIso ((blowUpToBase Z).stalkMap y)).commRingCatIsoToRingEquiv
  have hprime' : (Ideal.span {φ a}).IsPrime := by
    have := Ideal.map_isPrime_of_equiv (I := Ideal.span {a}) e
    rwa [Ideal.map_span, Set.image_singleton] at this
  refine stalk_vanishingIdeal_eq_span_singleton _ y hprime' fun p => ?_
  rw [TopologicalSpace.Closeds.coe_closure,
    fromSpecStalk_mem_closure_preimage_diff_iff_of_notMem y hy K.support.isClosed hC hCZ]
  refine (fromSpecStalk_mem_support_iff_stalk_le K (blowUpToBase Z y)
    (PrimeSpectrum.comap φ p)).trans ?_
  rw [ha, Ideal.span_singleton_le_iff_mem]
  rfl

/-- Off the exceptional locus, the order-one transform of an ideal has the stalks of the ideal,
carried over. -/
theorem stalk_transform_I_of_notMem (T : OrderedDivisorTuple X) {Z : X.IdealSheafData}
    (y : blowUp Z) (hy : blowUpToBase Z y ∉ Z.support) (j : Fin T.m) :
    IdealSheafData.stalk ((T.transform Z).I j) y =
      (IdealSheafData.stalk (T.I j) (blowUpToBase Z y)).map
        ((blowUpToBase Z).stalkMap y).hom := by
  by_cases h : (Z.support : Set X) ⊆ (T.I j).support
  · rw [OrderedDivisorTuple.transform_I_of_le _ _ _ h, stalk_idealColon_of_notMem,
      idealStalk_comap_eq_map]
    rwa [← SetLike.mem_coe, Scheme.IdealSheafData.support_comap]
  · rw [OrderedDivisorTuple.transform_I_of_not_le _ _ _ h, idealStalk_comap_eq_map]

/-- The union of the components of codimension at least two of a set lies in the set. -/
theorem componentsOfCodimAtLeastTwo_subset (Z : Set X) :
    componentsOfCodimAtLeastTwo Z ⊆ Z := by
  intro x hx
  simp only [componentsOfCodimAtLeastTwo, Set.mem_iUnion] at hx
  obtain ⟨W, hW, -, hxW⟩ := hx
  exact hW.1.2 hxW

/-- The boundary entries of the total transform carried by the old entries. -/
theorem totalTransform_E_castSucc (E : OrderedDivisor X) (Z : X.IdealSheafData) (i : Fin E.s) :
    (E.totalTransform Z).E (Fin.castSucc i) = Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure (blowUpToBase Z ⁻¹'
        ((E.E i).support \ componentsOfCodimAtLeastTwo (Z.support : Set X)))) := by
  rw [totalTransform_E_eq]
  simp [totalTransformSet]

/-- The new boundary entry of the total transform lies over the centre. -/
theorem support_totalTransform_E_last_subset (E : OrderedDivisor X) (Z : X.IdealSheafData) :
    (((E.totalTransform Z).E (Fin.last E.s)).support : Set (blowUp Z)) ⊆
      blowUpToBase Z ⁻¹' (Z.support : Set X) := by
  rw [totalTransform_E_eq]
  simp only [totalTransformSet, Fin.snoc_last, Scheme.IdealSheafData.coe_support_vanishingIdeal,
    TopologicalSpace.Closeds.coe_closure]
  refine closure_minimal ?_ (Z.support.isClosed.preimage (blowUpToBase Z).continuous)
  simp only [Set.iUnion_subset_iff]
  intro W hW _
  exact Set.preimage_mono hW.1.2

/-- **Nothing changes off the centre.** A point of `B_ZX` off the exceptional locus lying over a
point of the snc locus of `T` is in the snc locus of the transformed tuple. -/
theorem mem_sncLocus_transform_of_notMem [IsLocallyNoetherian X] [CompactSpace X]
    (T : OrderedDivisorTuple X) {Z : X.IdealSheafData} (y : blowUp Z)
    (hy : blowUpToBase Z y ∉ Z.support) (hx : blowUpToBase Z y ∈ T.sncLocus) :
    y ∈ (T.transform Z).sncLocus := by
  classical
  let W : X.Opens := ⟨(Z.support : Set X)ᶜ, Z.support.isClosed.isOpen_compl⟩
  haveI : IsIso (blowUpToBase Z ∣_ W) := isIso_blowUp_restrict_compl_support Z
  haveI : IsIso ((blowUpToBase Z).stalkMap y) :=
    Stacks.AlgebraicGeometry.IsoOverOpen.isIso_stalkMap (blowUpToBase Z) W (y := y) hy
  have : IsNoetherian X := {}
  have hZ2 := isClosed_componentsOfCodimAtLeastTwo (X := X) Z.support.isClosed
  have hZ2sub := componentsOfCodimAtLeastTwo_subset (X := X) (Z.support : Set X)
  have hsnc := hx
  obtain ⟨n, z, c, hz, hc, hzc⟩ := hx
  have hprime : ∀ q, (Ideal.span {z (c q)}).IsPrime := fun q =>
    span_singleton_isPrime_of_isRegularSystemOfParameters hz _
  -- the index map
  have key : ∀ p : {p // y ∈ ((T.transform Z).divisors p).support},
      ∃ q : {q // blowUpToBase Z y ∈ (T.divisors q).support},
        p.1 = Sum.map id Fin.castSucc q.1 ∧
        IdealSheafData.stalk ((T.transform Z).divisors p.1) y =
          (IdealSheafData.stalk (T.divisors q.1) (blowUpToBase Z y)).map
            ((blowUpToBase Z).stalkMap y).hom := by
    rintro ⟨p, hp⟩
    rcases p with j | i
    · have hst := stalk_transform_I_of_notMem T y hy j
      have hxj : blowUpToBase Z y ∈ (T.I j).support := by
        by_contra hxj
        rw [(IdealSheafData.stalk_eq_top_iff_notMem_support _ _).2 hxj, Ideal.map_top] at hst
        exact (IdealSheafData.stalk_eq_top_iff_notMem_support _ _).1 hst hp
      exact ⟨⟨.inl j, hxj⟩, rfl, hst⟩
    · have hs : (T.transform Z).E.s = T.E.s + 1 := rfl
      by_cases hi : (i : ℕ) < T.E.s
      · obtain ⟨i0, rfl⟩ : ∃ i0 : Fin T.E.s, i = Fin.castSucc i0 := ⟨⟨i, hi⟩, rfl⟩
        change y ∈ ((T.E.totalTransform Z).E (Fin.castSucc i0)).support at hp
        rw [totalTransform_E_castSucc, ← SetLike.mem_coe,
          Scheme.IdealSheafData.coe_support_vanishingIdeal, TopologicalSpace.Closeds.coe_closure,
          mem_closure_preimage_diff_iff_of_notMem y hy (T.E.E _).support.isClosed hZ2
            hZ2sub] at hp
        refine ⟨⟨.inr i0, hp⟩, rfl, ?_⟩
        have hq := hzc ⟨.inr i0, hp⟩
        change IdealSheafData.stalk ((T.E.totalTransform Z).E (Fin.castSucc i0)) y = _
        rw [totalTransform_E_castSucc, stalk_vanishingIdeal_closure_preimage_of_notMem y hy
          (T.E.E i0) hZ2 hZ2sub hq (hprime _)]
        have hq' : IdealSheafData.stalk (T.E.E i0) (blowUpToBase Z y) =
            Ideal.span {z (c ⟨.inr i0, hp⟩)} := hq
        change _ = (IdealSheafData.stalk (T.E.E i0) (blowUpToBase Z y)).map _
        rw [hq', Ideal.map_span, Set.image_singleton]
      · exfalso
        have h1 : (i : ℕ) < T.E.s + 1 := i.isLt
        obtain rfl : i = Fin.last T.E.s := Fin.ext (by simp only [Fin.val_last]; omega)
        exact hy (support_totalTransform_E_last_subset T.E Z hp)
  choose f hf using key
  refine IsSNCAt.of_stalkMap (blowUpToBase Z) y hsnc f ?_ fun p => (hf p).2
  intro p p' hpp'
  exact Subtype.ext ((hf p).1.trans ((congrArg (fun q => Sum.map id Fin.castSucc q.1) hpp').trans
    (hf p').1.symm))

end AwayFromCentre

/-! ### Lifting order-one transformations from a transverse divisor

Complements to the construction behind
`MMP.Resolution.OrderedDivisorTuple.exists_isPushforward_transform_restrict`. -/

section TupleRestrictionLift

open MMP.Resolution.OrderedDivisorTuple

/-- An snc family indexed by `Option (Fin n)` is one indexed by `Fin (n + 1)`. -/
theorem isSNCFamily_cons_of_elim {k : Type u} [Field k] {X : Scheme.{u}}
    {s : X ⟶ Spec (.of k)} {n : ℕ} {K : X.IdealSheafData} {E : Fin n → X.IdealSheafData}
    (h : IsSNCFamily s fun o : Option (Fin n) => o.elim K E) :
    IsSNCFamily s (Fin.cons (α := fun _ => X.IdealSheafData) K E) := by
  convert isSNCFamily_comp h (finSuccEquiv n) (finSuccEquiv n).injective using 1
  funext i
  refine Fin.cases ?_ (fun i => ?_) i <;> simp

/-- The order-one transform of an ordered divisor tuple along a centre of an order-one
transformation which is not everything is again an ordered divisor tuple. -/
theorem isOrderedDivisorTuple_transform {k : Type u} [Field k] {X : Scheme.{u}}
    {s : X ⟶ Spec (.of k)} {T : OrderedDivisorTuple X} (hT : IsOrderedDivisorTuple s T)
    {Z : X.IdealSheafData} (hZ : T.IsTransformCentre s Z) (hne : Z ≠ ⊥) :
    IsOrderedDivisorTuple (blowUpToBase Z ≫ s) (T.transform Z) := by
  obtain ⟨hchar, hvar, hsm, hI, hE⟩ := hT
  have : AlgebraicGeometry.IsVariety k s := hvar
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  have hvar' := (MMP.Flips.ResolutionInputs.isVariety_blowUp_and_isProjective_and_isBirational
    s Z hne).1
  have : AlgebraicGeometry.IsVariety k (blowUpToBase Z ≫ s) := hvar'
  have : IsIntegral (blowUp Z) := hvar'.toIsIntegral
  refine ⟨hchar, hvar', MMP.Mori.isSmoothScheme_of_smooth
    (Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup s Z ⟨hsm, hZ.1⟩).1,
    fun j => ?_, isOrderedSNC_totalTransform s hE.2 hZ.2⟩
  have hpb : Stacks.Divisors.IsEffectiveCartierDivisor ((T.I j).comap (blowUpToBase Z)) :=
    AlgebraicGeometry.isPullbackDefined_blowUpToBase _ _ (hI j).2
  have hcart : Stacks.Divisors.IsEffectiveCartierDivisor ((T.transform Z).I j) := by
    by_cases hle : (Z.support : Set X) ⊆ (T.I j).support
    · rw [OrderedDivisorTuple.transform_I_of_le _ _ _ hle]
      have hF := Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal Z
      have hIC : T.I j ≤ Z := le_of_hasSNCWith_of_support_subset hZ.2 hle
      obtain ⟨E, hE, hEq⟩ := AlgebraicGeometry.exists_isEffectiveCartierDivisor_mul_eq_of_le
        _ _ hF hpb (Scheme.IdealSheafData.comap_mono _ hIC)
      rw [hEq, idealColon_mul_cancel _ _ hF]
      exact hE
    · rw [OrderedDivisorTuple.transform_I_of_not_le _ _ _ hle]
      exact hpb
  exact ⟨AlgebraicGeometry.ne_bot_of_isEffectiveCartierDivisor hcart, hcart⟩

/-- The strict transform of `H` together with the transformed boundary is snc, for any centre
`C` of an order-one transformation containing `H`. -/
theorem isSNCFamily_transform_of_le {k : Type u} [Field k] {S W : Scheme.{u}}
    {ι : S ⟶ W} {s : W ⟶ Spec (.of k)} {T : OrderedDivisorTuple W} (hinv : LiftInvariant ι s T)
    (C : W.IdealSheafData) (hHC : ι.ker ≤ C) (hc : T.IsTransformCentre s C) :
    IsSNCFamily (blowUpToBase C ≫ s) fun o : Option (Fin (T.transform C).E.s) =>
      o.elim (canonicalLift ι C).ker (T.transform C).E.E := by
  have : IsClosedImmersion ι := hinv.1
  have : AlgebraicGeometry.IsVariety k s := hinv.2.1.2.1
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian s
  have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace s
  have : CharZero k := hinv.2.1.1
  have hHE := hinv.2.2
  have hred : IsReduced ι.ker.subscheme := (hinv.2.2.1 none).1
  have : IsReduced S := isReduced_of_isOpenImmersion ι.toImage
  have hcons := isSNCFamily_cons_of_elim hHE
  have hZcons := Kollar.hasSNCWith_cons_of_hasSNCWith s T.E ι.ker hcons C hHC hc.2
  have hHZ : (C.support : Set W) ⊆ ι.ker.support := Scheme.IdealSheafData.support_antitone hHC
  have : IsLocallyNoetherian (blowUp C) :=
    LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase C ≫ s)
  have hr : Set.range ι = (ι.ker.support : Set W) := by
    rw [Scheme.Hom.support_ker, ι.isClosedEmbedding.isClosed_range.closure_eq]
  let Tset : Option (Fin (T.E.s + 1)) → Set (blowUp C) := fun o =>
    o.elim (blowUpToBase C ⁻¹' ((ι.ker.support : Set W) \ C.support)) (totalTransformSet T.E C)
  have hfam : (fun o : Option (Fin (T.transform C).E.s) =>
      o.elim (canonicalLift ι C).ker (T.transform C).E.E) = fun o =>
        Scheme.IdealSheafData.vanishingIdeal (TopologicalSpace.Closeds.closure (Tset o)) := by
    funext o
    cases o with
    | none =>
      show (canonicalLift ι C).ker = _
      rw [ker_canonicalLift_eq_vanishingIdeal, hr]
      rfl
    | some i => exact totalTransform_E_eq T.E C i
  rw [hfam]
  have hcoord : ∀ x' : blowUp C, ∃ (N : ℕ) (w : Fin N → (blowUp C).presheaf.stalk x')
      (c : {o // x' ∈ (Scheme.IdealSheafData.vanishingIdeal
        (TopologicalSpace.Closeds.closure (Tset o))).support} → Fin N),
      MMP.Mori.IsRegularSystemOfParameters w ∧
        (∀ o, IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal
          (TopologicalSpace.Closeds.closure (Tset o.1))) x' = Ideal.span {w (c o)}) ∧
        Function.Injective c := by
    intro x'
    obtain ⟨N, w, d, hw, h1, h2⟩ :=
      exists_assignment_strictTransform T.E ι.ker hcons.2 hZcons hHZ x'
    obtain ⟨c, hc, hinj⟩ := exists_stalk_eq_of_assignment Tset x' hw d h1 h2
    exact ⟨N, w, c, hw, hc, hinj⟩
  have hpar : ∀ o, ∀ y ∈ (Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure (Tset o))).support,
      ∃ (m : ℕ) (w : Fin m → (blowUp C).presheaf.stalk y) (j : Fin m),
        MMP.Mori.IsRegularSystemOfParameters w ∧
          IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal
            (TopologicalSpace.Closeds.closure (Tset o))) y = Ideal.span {w j} := by
    intro o y hy
    obtain ⟨N, w, c, hw, hc, -⟩ := hcoord y
    exact ⟨N, w, c ⟨o, hy⟩, hw, hc ⟨o, hy⟩⟩
  exact ⟨fun o => ⟨isReduced_subscheme_of_stalk_eq_span_parameter _ (hpar o),
    isPureCodimOne_support_of_stalk_eq_span_parameter _ (hpar o),
    isSmoothScheme_subscheme_of_stalk_eq_span_parameter _ _ (hpar o)⟩, hcoord⟩

end TupleRestrictionLift

/-! ### Transforms of ordered divisor tuples are ordered divisor tuples -/

section TupleTransform

/-- Along a sequence of order-one transformations missing the inverse images of a nonempty set,
every stage is an ordered divisor tuple, and the inverse image of the set stays nonempty. -/
theorem isOrderedDivisorTuple_finalTuple {k : Type u} [Field k] :
    ∀ {S : Scheme.{u}} (B : ClosedBlowupSequence S) {s : S ⟶ Spec (.of k)} {N : Set S}
      {T : OrderedDivisorTuple S}, IsOrderedDivisorTuple s T → Valid s N B T → N.Nonempty →
      IsOrderedDivisorTuple (B.toBase ≫ s) (finalTuple B T) ∧ (B.toBase ⁻¹' N).Nonempty := by
  intro S B
  induction B with
  | nil S =>
    intro s N T hT _ hN
    refine ⟨?_, hN⟩
    change IsOrderedDivisorTuple (𝟙 S ≫ s) T
    rwa [Category.id_comp]
  | @cons X Z B ih =>
    intro s N T hT h hN
    obtain ⟨x, hx⟩ := hN
    have hxZ : x ∉ Z.support := h.2.1.notMem_of_mem_right hx
    have hne : Z ≠ ⊥ := by
      rintro rfl
      exact hxZ (by rw [Scheme.IdealSheafData.support_bot]; trivial)
    let W : X.Opens := ⟨(Z.support : Set X)ᶜ, Z.support.isClosed.isOpen_compl⟩
    haveI : IsIso (blowUpToBase Z ∣_ W) := isIso_blowUp_restrict_compl_support Z
    obtain ⟨y, rfl⟩ := mem_range_of_isIso_restrict (blowUpToBase Z) W (x := x) hxZ
    have := ih (isOrderedDivisorTuple_transform hT h.1 hne) h.2.2 ⟨y, hx⟩
    refine ⟨?_, this.2⟩
    change IsOrderedDivisorTuple ((B.toBase ≫ blowUpToBase Z) ≫ s) (finalTuple B (T.transform Z))
    rw [Category.assoc]
    exact this.1

end TupleTransform

/-! ### Composing sequences -/

section Compose

/-- A sequence whose centres miss the inverse images of `N` also misses those of any `N' ⊆ N`. -/
theorem Valid.mono {k : Type u} [Field k] :
    ∀ {S : Scheme.{u}} (B : ClosedBlowupSequence S) {s : S ⟶ Spec (.of k)} {N N' : Set S}
      {T : OrderedDivisorTuple S}, N' ⊆ N → Valid s N B T → Valid s N' B T := by
  intro S B
  induction B with
  | nil S => intros; trivial
  | cons Z B ih =>
    intro s N N' T hN h
    exact ⟨h.1, h.2.1.mono_right hN, ih (Set.preimage_mono hN) h.2.2⟩

/-- **Unchanged over the snc locus.** Along a sequence whose centres miss the inverse images of a
part `N` of the snc locus, the inverse image of `N` stays in the snc locus. -/
theorem preimage_subset_sncLocus_of_valid {k : Type u} [Field k] :
    ∀ {S : Scheme.{u}} (B : ClosedBlowupSequence S) [IsLocallyNoetherian S] [CompactSpace S]
      {s : S ⟶ Spec (.of k)} {N : Set S} {T : OrderedDivisorTuple S}, Valid s N B T →
      N ⊆ T.sncLocus → B.toBase ⁻¹' N ⊆ (finalTuple B T).sncLocus := by
  intro S B
  induction B with
  | nil S => intro _ _ s N T _ hN; exact hN
  | @cons X Z B ih =>
    intro _ _ s N T h hN
    have : IsLocallyNoetherian (blowUp Z) :=
      LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase Z)
    have : CompactSpace (blowUp Z) := QuasiCompact.compactSpace_of_compactSpace (blowUpToBase Z)
    have h' := ih h.2.2 (fun y hy => mem_sncLocus_transform_of_notMem T y
      (h.2.1.notMem_of_mem_right hy) (hN hy))
    intro y hy
    exact h' hy

/-- Missing the current snc loci implies missing the inverse images of any part of the original
snc locus. -/
theorem ValidS.valid {k : Type u} [Field k] :
    ∀ {S : Scheme.{u}} (B : ClosedBlowupSequence S) [IsLocallyNoetherian S] [CompactSpace S]
      {s : S ⟶ Spec (.of k)} {T : OrderedDivisorTuple S} {N : Set S}, ValidS s B T →
      N ⊆ T.sncLocus → Valid s N B T := by
  intro S B
  induction B with
  | nil S => intros; trivial
  | @cons X Z B ih =>
    intro _ _ s T N h hN
    have : IsLocallyNoetherian (blowUp Z) :=
      LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase Z)
    have : CompactSpace (blowUp Z) := QuasiCompact.compactSpace_of_compactSpace (blowUpToBase Z)
    exact ⟨h.1, h.2.1.mono_right hN, ih h.2.2 fun y hy => mem_sncLocus_transform_of_notMem T y
      (h.2.1.notMem_of_mem_right (hN hy)) (hN hy)⟩

/-- Strong validity of a concatenation. -/
theorem validS_append {k : Type u} [Field k] :
    ∀ {S : Scheme.{u}} (B₁ : ClosedBlowupSequence S) (B₂ : ClosedBlowupSequence B₁.target)
      (s : S ⟶ Spec (.of k)) (T : OrderedDivisorTuple S),
      ValidS s B₁ T → ValidS (B₁.toBase ≫ s) B₂ (finalTuple B₁ T) →
        ValidS s (B₁.append B₂) T := by
  intro S B₁
  induction B₁ with
  | nil S =>
    intro B₂ s T _ h
    change ValidS (𝟙 S ≫ s) B₂ T at h
    rw [Category.id_comp] at h
    exact h
  | cons Z B ih =>
    intro B₂ s T h1 h2
    refine ⟨h1.1, h1.2.1, ih B₂ _ _ h1.2.2 ?_⟩
    change ValidS ((B.toBase ≫ blowUpToBase Z) ≫ s) B₂ (finalTuple B (T.transform Z)) at h2
    rw [Category.assoc] at h2
    exact h2

/-- The snc locus of the final tuple of a concatenation. -/
theorem sncLocus_finalTuple_append_eq_univ_iff :
    ∀ {S : Scheme.{u}} (B₁ : ClosedBlowupSequence S) (B₂ : ClosedBlowupSequence B₁.target)
      (T : OrderedDivisorTuple S),
      (finalTuple (B₁.append B₂) T).sncLocus = Set.univ ↔
        (finalTuple B₂ (finalTuple B₁ T)).sncLocus = Set.univ := by
  intro S B₁
  induction B₁ with
  | nil S => intro B₂ T; rfl
  | cons Z B ih => intro B₂ T; exact ih B₂ (T.transform Z)

end Compose

/-! ### The total transform of the strict transform's divisor -/

/-- A member of a regular system of parameters lying in the ideal generated by some members is
one of them. -/
theorem mem_of_mem_span_image_of_isRegularSystemOfParameters {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] {m : ℕ} {w : Fin m → R}
    (hw : MMP.Mori.IsRegularSystemOfParameters w) {J : Finset (Fin m)} {j : Fin m}
    (hmem : w j ∈ Ideal.span (w '' (J : Set (Fin m)))) : j ∈ J := by
  classical
  by_contra hjJ
  have := MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hw
  set s : Set R := w '' ({j}ᶜ : Set (Fin m)) with hs
  have hspan : Ideal.span s = IsLocalRing.maximalIdeal R := by
    rw [← hw.1]
    refine le_antisymm (Ideal.span_mono ?_) (Ideal.span_le.2 ?_)
    · rintro _ ⟨l, -, rfl⟩; exact ⟨l, rfl⟩
    · rintro _ ⟨l, rfl⟩
      by_cases hl : l = j
      · subst hl
        refine Ideal.span_mono ?_ hmem
        rintro _ ⟨i, hi, rfl⟩
        exact ⟨i, fun h => hjJ (by rw [Set.mem_singleton_iff.1 h] at hi; exact hi), rfl⟩
      · exact Ideal.subset_span ⟨l, hl, rfl⟩
  have hfin : s.Finite := Set.toFinite _
  have hle := Submodule.spanFinrank_span_le_ncard_of_finite (R := R) hfin
  rw [show Submodule.span R s = IsLocalRing.maximalIdeal R from hspan] at hle
  have hcard : s.ncard ≤ m - 1 := by
    rw [hs]
    refine (Set.ncard_image_le (Set.toFinite _)).trans ?_
    rw [Set.ncard_eq_toFinset_card']
    simp [Finset.card_compl]
  have hrank := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
  rw [hw.2] at hrank
  have : (IsLocalRing.maximalIdeal R).spanFinrank = m := by exact_mod_cast hrank
  have := j.2
  omega

/-- **The total transform of a smooth divisor containing the centre.** If `H = ι(S)` together with
the boundary is snc and the centre `C ⊆ H` has snc with the boundary, then `π^*I_H` is the product
of the ideal of the exceptional divisor and the ideal of the strict transform `B_{ι⁻¹C}S`. -/
theorem comap_ker_eq_mul_ker_canonicalLift_of_le {k : Type u} [Field k]
    {S W : Scheme.{u}} {ι : S ⟶ W} {s : W ⟶ Spec (.of k)} {T : OrderedDivisorTuple W}
    (hinv : LiftInvariant ι s T) (C : W.IdealSheafData) (hHC : ι.ker ≤ C)
    (hc : T.IsTransformCentre s C) :
    ι.ker.comap (blowUpToBase C) = C.comap (blowUpToBase C) * (canonicalLift ι C).ker := by
  have : IsClosedImmersion ι := hinv.1
  have : AlgebraicGeometry.IsVariety k s := hinv.2.1.2.1
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian s
  have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace s
  have hHE := hinv.2.2
  have hred : IsReduced ι.ker.subscheme := (hinv.2.2.1 none).1
  have : IsReduced S := isReduced_of_isOpenImmersion ι.toImage
  have hcons := isSNCFamily_cons_of_elim hHE
  have hZcons := Kollar.hasSNCWith_cons_of_hasSNCWith s T.E ι.ker hcons C hHC hc.2
  have hr : Set.range ι = (ι.ker.support : Set W) := by
    rw [Scheme.Hom.support_ker, ι.isClosedEmbedding.isClosed_range.closure_eq]
  rw [ker_canonicalLift_eq_vanishingIdeal, hr]
  refine IdealSheafData.eq_of_stalk_eq _ _ fun y => ?_
  rw [IdealSheafData.stalk_mul, idealStalk_comap_eq_map, idealStalk_comap_eq_map]
  have : IsLocallyNoetherian (blowUp C) :=
    LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase C)
  set π := blowUpToBase C
  set K := ι.ker
  have hKC : (C.support : Set W) ⊆ K.support := Scheme.IdealSheafData.support_antitone hHC
  have hvsupp : ((Scheme.IdealSheafData.vanishingIdeal (TopologicalSpace.Closeds.closure
      (π ⁻¹' ((K.support : Set W) \ C.support)))).support : Set (blowUp C)) =
      closure (π ⁻¹' ((K.support : Set W) \ C.support)) := by
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal, TopologicalSpace.Closeds.coe_closure]
  by_cases hyC : π y ∈ (C.support : Set W)
  · -- over the centre: a chart computation
    obtain ⟨n, z, c, J, hz, hzE, -, hJ⟩ := hZcons (π y) hyC
    have hx0 : π y ∈ ((Fin.cons (α := fun _ => W.IdealSheafData) K T.E.E) 0).support := by
      simpa using hKC hyC
    set c0 := c ⟨0, hx0⟩
    have hK : IdealSheafData.stalk K (π y) = Ideal.span {z c0} := by
      simpa using hzE ⟨0, hx0⟩
    have hc0J : c0 ∈ J := by
      refine mem_of_mem_span_image_of_isRegularSystemOfParameters hz ?_
      rw [← hJ]
      exact MMP.Resolution.stalk_le_stalk_of_le hHC (π y) (hK ▸ Ideal.mem_span_singleton_self _)
    obtain ⟨N, w, m, i0, σ, U, hw, hm, hU, hwi0, -, hJm, hUu, hσ⟩ :=
      exists_chart_coordinates C y hyC hz hJ
    set φ := (π.stalkMap y).hom
    have hmult : ∀ j ∈ J, φ (z j) ∈ Ideal.span {w i0} := by
      intro j hj
      by_cases hjm : j = m
      · rw [hjm, ← hwi0]; exact Ideal.mem_span_singleton_self _
      by_cases hjU : j ∈ U
      · obtain ⟨u, -, hu⟩ := hUu j hjU
        rw [hu]; exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
      · rw [hJm j hj hjm hjU]; exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    have hCst : (IdealSheafData.stalk C (π y)).map φ = Ideal.span {w i0} := by
      rw [hJ, Ideal.map_span]
      refine le_antisymm (Ideal.span_le.2 ?_) ?_
      · rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
        exact hmult j hj
      · rw [Ideal.span_singleton_le_iff_mem, hwi0]
        exact Ideal.subset_span ⟨z m, ⟨m, hm, rfl⟩, rfl⟩
    -- the points of `Spec 𝒪_{B,y}` over `C` and over `H`
    have hoverC : ∀ q : PrimeSpectrum ((blowUp C).presheaf.stalk y),
        π ((blowUp C).fromSpecStalk y q) ∈ (C.support : Set W) ↔ w i0 ∈ q.asIdeal := by
      intro q
      rw [apply_fromSpecStalk]
      refine (fromSpecStalk_mem_support_iff_stalk_le C (π y) (PrimeSpectrum.comap φ q)).trans ?_
      show IdealSheafData.stalk C (π y) ≤ Ideal.comap φ q.asIdeal ↔ _
      rw [← Ideal.map_le_iff_le_comap, hCst, Ideal.span_singleton_le_iff_mem]
    have hoverK : ∀ q : PrimeSpectrum ((blowUp C).presheaf.stalk y),
        π ((blowUp C).fromSpecStalk y q) ∈ (K.support : Set W) ↔ φ (z c0) ∈ q.asIdeal := by
      intro q
      rw [apply_fromSpecStalk]
      refine (fromSpecStalk_mem_support_iff_stalk_le K (π y) (PrimeSpectrum.comap φ q)).trans ?_
      rw [hK, Ideal.span_singleton_le_iff_mem]
      rfl
    have hchar : ∀ p : PrimeSpectrum ((blowUp C).presheaf.stalk y),
        (blowUp C).fromSpecStalk y p ∈ closure (π ⁻¹' ((K.support : Set W) \ C.support)) ↔
          ∃ q : PrimeSpectrum ((blowUp C).presheaf.stalk y), q.asIdeal ≤ p.asIdeal ∧
            φ (z c0) ∈ q.asIdeal ∧ w i0 ∉ q.asIdeal := by
      intro p
      rw [fromSpecStalk_mem_closure_preimage_diff_iff y K.support.isClosed C.support.isClosed]
      exact exists_congr fun q => and_congr_right fun _ =>
        and_congr (hoverK q) (not_congr (hoverC q))
    have hKst : (IdealSheafData.stalk K (π y)).map φ = Ideal.span {φ (z c0)} := by
      rw [hK, Ideal.map_span, Set.image_singleton]
    by_cases hc0 : c0 = m ∨ c0 ∈ U
    · -- the strict transform does not pass through `y`
      obtain ⟨u, hu, hzu⟩ : ∃ u, IsUnit u ∧ φ (z c0) = u * w i0 := by
        rcases hc0 with hc0 | hc0
        · exact ⟨1, isUnit_one, by rw [one_mul, hc0, ← hwi0]⟩
        · exact hUu c0 hc0
      have hnot : y ∉ closure (π ⁻¹' ((K.support : Set W) \ C.support)) := by
        intro hy
        rw [← Scheme.fromSpecStalk_closedPoint (x := y), hchar] at hy
        obtain ⟨q, -, hq1, hq2⟩ := hy
        rw [hzu] at hq1
        exact hq2 ((Ideal.IsPrime.mem_or_mem q.2 hq1).resolve_left
          fun h => q.2.ne_top ((Ideal.eq_top_iff_one _).2 (by
            obtain ⟨v, hv⟩ := hu.exists_left_inv; rw [← hv]; exact Ideal.mul_mem_left _ _ h)))
      have hnot' : y ∉ (Scheme.IdealSheafData.vanishingIdeal (TopologicalSpace.Closeds.closure
          (π ⁻¹' ((K.support : Set W) \ C.support)))).support := by
        rwa [← SetLike.mem_coe, hvsupp]
      rw [(IdealSheafData.stalk_eq_top_iff_notMem_support _ _).2 hnot', Ideal.mul_top, hCst, hKst,
        hzu, Ideal.span_singleton_mul_left_unit hu]
    · -- the strict transform is `(w_{σ c₀} = 0)`
      simp only [not_or] at hc0
      have hzσ := hJm c0 hc0J hc0.1 hc0.2
      have hσi : σ c0 ≠ i0 := hσ c0 hc0.1 hc0.2
      have hprime := span_singleton_isPrime_of_isRegularSystemOfParameters hw (σ c0)
      have hv : IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal
          (TopologicalSpace.Closeds.closure (π ⁻¹' ((K.support : Set W) \ C.support)))) y =
          Ideal.span {w (σ c0)} := by
        refine stalk_vanishingIdeal_eq_span_singleton _ y hprime fun p => ?_
        rw [TopologicalSpace.Closeds.coe_closure, hchar]
        constructor
        · rintro ⟨q, hqp, hq1, hq2⟩
          rw [hzσ] at hq1
          exact hqp ((Ideal.IsPrime.mem_or_mem q.2 hq1).resolve_right hq2)
        · intro hp
          refine ⟨⟨_, hprime⟩, (Ideal.span_singleton_le_iff_mem _).2 hp, ?_, ?_⟩
          · rw [hzσ]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
          · exact notMem_span_singleton_of_ne_of_isRegularSystemOfParameters hw hσi
      rw [hv, hCst, hKst, hzσ, Ideal.span_singleton_mul_span_singleton, mul_comm]
  · -- off the centre
    let Wc : W.Opens := ⟨(C.support : Set W)ᶜ, C.support.isClosed.isOpen_compl⟩
    haveI : IsIso (π ∣_ Wc) := isIso_blowUp_restrict_compl_support C
    haveI : IsIso (π.stalkMap y) :=
      Stacks.AlgebraicGeometry.IsoOverOpen.isIso_stalkMap π Wc (y := y) hyC
    rw [(IdealSheafData.stalk_eq_top_iff_notMem_support C (π y)).2 hyC, Ideal.map_top,
      Ideal.top_mul]
    by_cases hyK : π y ∈ (K.support : Set W)
    · obtain ⟨n, z, c, hz, hzE, -⟩ := hcons.2 (π y)
      have hx0 : π y ∈ ((Fin.cons (α := fun _ => W.IdealSheafData) K T.E.E) 0).support := by
        simpa using hyK
      have hK : IdealSheafData.stalk K (π y) = Ideal.span {z (c ⟨0, hx0⟩)} := by
        simpa using hzE ⟨0, hx0⟩
      rw [stalk_vanishingIdeal_closure_preimage_of_notMem y hyC K C.support.isClosed
        subset_rfl hK (span_singleton_isPrime_of_isRegularSystemOfParameters hz _), hK,
        Ideal.map_span, Set.image_singleton]
    · rw [(IdealSheafData.stalk_eq_top_iff_notMem_support K (π y)).2 hyK, Ideal.map_top,
        eq_comm, IdealSheafData.stalk_eq_top_iff_notMem_support, ← SetLike.mem_coe, hvsupp,
        mem_closure_preimage_diff_iff_of_notMem y hyC K.support.isClosed C.support.isClosed
          subset_rfl]
      exact hyK

/-- The pullback of the ideal of `H` to the blow-up along the pushed-forward centre is the
exceptional ideal times the ideal of the strict transform of `H`. -/
theorem comap_ker_eq_mul_ker_canonicalLift {k : Type u} [Field k] {S W : Scheme.{u}}
    {ι : S ⟶ W} {s : W ⟶ Spec (.of k)} {T : OrderedDivisorTuple W} (hinv : LiftInvariant ι s T)
    {Z : S.IdealSheafData} (hc : T.IsTransformCentre s (Z.map ι)) (h : (Z.map ι).comap ι = Z) :
    ι.ker.comap (blowUpToBase (Z.map ι)) = (Z.map ι).comap (blowUpToBase (Z.map ι)) *
      (eqToHom (congrArg blowUp h.symm) ≫ canonicalLift ι (Z.map ι)).ker := by
  have hHC : ι.ker ≤ Z.map ι := Scheme.Hom.le_ker_comp Z.subschemeι ι
  generalize Z.map ι = C at hc h hHC ⊢
  subst h
  simp only [eqToHom_refl, Category.id_comp]
  exact comap_ker_eq_mul_ker_canonicalLift_of_le hinv C hHC hc

/-! ### Restriction of snc to a divisor and back -/

/-- **Restriction.** If `ι(S)` together with a family `D` is snc at a point of `ι(S)`, the
restricted family `D|_S` is snc there. -/
theorem isSNCAt_comap_of_isSNCAt_elim {X S : Scheme.{u}} [IsLocallyNoetherian X]
    (ι : S ⟶ X) [IsClosedImmersion ι] {Λ : Type*} (D : Λ → X.IdealSheafData) (y : S)
    (h : IsSNCAt (fun o : Option Λ => o.elim ι.ker D) (ι y)) :
    IsSNCAt (fun i => (D i).comap ι) y := by
  classical
  obtain ⟨n, z, c, hz, hc, hzc⟩ := h
  have hxH : ι y ∈ ι.ker.support := by
    rw [← SetLike.mem_coe, Scheme.Hom.support_ker, ι.isClosedEmbedding.isClosed_range.closure_eq]
    exact ⟨y, rfl⟩
  have := MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hz
  set cH := c ⟨none, hxH⟩
  let J : Finset (Fin n) := {cH}
  obtain ⟨hreg, -, hq⟩ := MMP.Flips.ResolutionInputs.isRegularSystemOfParameters_quotient_image hz J
  set φ := (ι.stalkMap y).hom
  have hsurj : Function.Surjective φ := SurjectiveOnStalks.stalkMap_surjective ι y
  have hker : Ideal.span (z '' (J : Set (Fin n))) = RingHom.ker φ := by
    rw [ker_stalkMap_eq_stalk_ker, show IdealSheafData.stalk ι.ker (ι y) = Ideal.span {z cH} from
      hzc ⟨none, hxH⟩]
    simp [J]
  let e : (X.presheaf.stalk (ι y) ⧸ Ideal.span (z '' (J : Set (Fin n)))) ≃+* S.presheaf.stalk y :=
    (Ideal.quotEquivOfEq hker).trans (RingHom.quotientKerEquivOfSurjective hsurj)
  have he : ∀ a, e (Ideal.Quotient.mk _ a) = φ a := fun a => rfl
  have hmem : ∀ i : {i // y ∈ ((D i).comap ι).support}, ι y ∈ (D i.1).support := fun i =>
    (mem_support_comap_iff _ _ y).1 i.2
  have hnot : ∀ i : {i // y ∈ ((D i).comap ι).support}, c ⟨some i.1, hmem i⟩ ∈ Jᶜ := by
    intro i
    rw [Finset.mem_compl, Finset.mem_singleton]
    intro h
    exact Option.some_ne_none _ (congrArg Subtype.val (hc h))
  let o := Jᶜ.orderIsoOfFin rfl
  refine ⟨Jᶜ.card, fun j => e (Ideal.Quotient.mk _ (z (Jᶜ.orderEmbOfFin rfl j))),
    fun i => o.symm ⟨c ⟨some i.1, hmem i⟩, hnot i⟩, hq.map_ringEquiv e, ?_, fun i => ?_⟩
  · intro i j hij
    exact Subtype.ext (Option.some_injective _
      (congrArg Subtype.val (hc (congrArg Subtype.val (o.symm.injective hij)))))
  · dsimp only
    rw [idealStalk_comap_eq_map, show IdealSheafData.stalk (D i.1) (ι y) =
      Ideal.span {z (c ⟨some i.1, hmem i⟩)} from hzc ⟨some i.1, hmem i⟩, Ideal.map_span,
      Set.image_singleton, he, ← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]

/-- The stalks of an effective Cartier divisor are principal. -/
theorem exists_stalk_eq_span_of_isEffectiveCartierDivisor {X : Scheme.{u}}
    (I : X.IdealSheafData) (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) (x : X) :
    ∃ e, IdealSheafData.stalk I x = Ideal.span {e} := by
  obtain ⟨U, hU, hxU, f, -, hf⟩ :=
    Stacks.Divisors.exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor I hI x
  exact ⟨_, IdealSheafData.stalk_eq_span_germ_of_ideal_eq_span (U := ⟨U, hU⟩) hxU hf⟩

/-- **Lifting.** If the restriction of a family `D` to a closed subscheme `S` is snc at `z`, the
ideal of `S` is a coordinate at `ι z` and the members of `D` through `ι z` are principal there,
then `ι(S)` together with `D` is snc at `ι z`. -/
theorem isSNCAt_elim_ker_of_isSNCAt_comap {X S : Scheme.{u}} [IsLocallyNoetherian X]
    (ι : S ⟶ X) [IsClosedImmersion ι] {Λ : Type*} (D : Λ → X.IdealSheafData) (z : S)
    (hK : ∃ (n₀ : ℕ) (z₀ : Fin n₀ → X.presheaf.stalk (ι z)) (c₀ : Fin n₀),
      MMP.Mori.IsRegularSystemOfParameters z₀ ∧
        IdealSheafData.stalk ι.ker (ι z) = Ideal.span {z₀ c₀})
    (hD : ∀ i, ι z ∈ (D i).support → ∃ e, IdealSheafData.stalk (D i) (ι z) = Ideal.span {e})
    (h : IsSNCAt (fun i => (D i).comap ι) z) :
    IsSNCAt (fun o : Option Λ => o.elim ι.ker D) (ι z) := by
  classical
  obtain ⟨n₀, z₀, c₀, hz₀, hker⟩ := hK
  obtain ⟨n, w, c', hw, hinj, hw'⟩ := h
  set φ := (ι.stalkMap z).hom
  have hsurj : Function.Surjective φ := SurjectiveOnStalks.stalkMap_surjective ι z
  have hkerφ : RingHom.ker φ = Ideal.span {z₀ c₀} := (ker_stalkMap_eq_stalk_ker ι z).trans hker
  have hact : ∀ i, z ∈ ((D i).comap ι).support ↔ ι z ∈ (D i).support := fun i =>
    mem_support_comap_iff _ _ z
  let ee : {i // z ∈ ((D i).comap ι).support} → X.presheaf.stalk (ι z) := fun a =>
    (hD a.1 ((hact a.1).1 a.2)).choose
  have hee : ∀ a, IdealSheafData.stalk (D a.1) (ι z) = Ideal.span {ee a} := fun a =>
    (hD a.1 ((hact a.1).1 a.2)).choose_spec
  obtain ⟨t, ht, ht0, -, htD⟩ := MMP.Mori.exists_lift_isRegularSystemOfParameters φ hsurj hz₀ c₀
    hkerφ hw c' ee Set.univ
    (fun a _ => by rw [← hw' a, idealStalk_comap_eq_map, hee a])
    (fun a _ a' _ h => hinj h)
  refine ⟨n + 1, t, fun o => match o with
    | ⟨none, _⟩ => 0
    | ⟨some i, hi⟩ => (c' ⟨i, (hact i).2 hi⟩).succ, ht, ?_, ?_⟩
  · rintro ⟨_ | i, hi⟩ ⟨_ | i', hi'⟩ h
    · rfl
    · exact absurd h (Fin.succ_ne_zero _).symm
    · exact absurd h (Fin.succ_ne_zero _)
    · have h' := congrArg Subtype.val (hinj (Fin.succ_injective _ h))
      simp only at h'
      subst h'
      rfl
  · rintro ⟨_ | i, hi⟩
    · change IdealSheafData.stalk ι.ker (ι z) = Ideal.span {t 0}
      rw [hker, ht0]
    · change IdealSheafData.stalk (D i) (ι z) = Ideal.span {t (c' ⟨i, (hact i).2 hi⟩).succ}
      rw [htD _ (Set.mem_univ _), hee ⟨i, (hact i).2 hi⟩]

/-- Two regular parameters, one in the ideal of the other, generate the same ideal. -/
theorem span_singleton_eq_of_mem {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {n n' : ℕ} {w : Fin n → R} {w' : Fin n' → R}
    (hw : MMP.Mori.IsRegularSystemOfParameters w) (hw' : MMP.Mori.IsRegularSystemOfParameters w')
    (i : Fin n) (i' : Fin n') (h : w' i' ∈ Ideal.span {w i}) :
    Ideal.span {w' i'} = Ideal.span {w i} := by
  have := MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hw
  have hP := span_singleton_isPrime_of_isRegularSystemOfParameters hw' i'
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1 h
  have hmem : u * w i ∈ Ideal.span {w' i'} := hu ▸ Ideal.mem_span_singleton_self _
  rcases hP.mem_or_mem hmem with hu' | hwi
  · exfalso
    obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 hu'
    have hwi : w i ∈ IsLocalRing.maximalIdeal R := by
      rw [← hw.1]; exact Ideal.subset_span ⟨i, rfl⟩
    have hunit : IsUnit (1 - v * w i) := by
      by_contra hnu
      have h1 : 1 - v * w i ∈ IsLocalRing.maximalIdeal R := hnu
      have h2 : v * w i ∈ IsLocalRing.maximalIdeal R := Ideal.mul_mem_left _ _ hwi
      exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top
        ((Ideal.eq_top_iff_one _).2 (by simpa using Ideal.add_mem _ h1 h2))
    have h1 : w' i' * (v * w i) = w' i' := by
      calc w' i' * (v * w i) = (v * w' i') * w i := by ring
        _ = u * w i := by rw [hv]
        _ = w' i' := hu
    have h0 : w' i' * (1 - v * w i) = 0 := by
      rw [mul_sub, mul_one, h1, sub_self]
    have := MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hw'
    exact ne_zero_of_isRegularSystemOfParameters hw' i' (by
      simpa using (hunit.mul_left_eq_zero).1 h0)
  · exact le_antisymm ((Ideal.span_singleton_le_iff_mem _).2 h)
      ((Ideal.span_singleton_le_iff_mem _).2 hwi)

/-- **Matching boundaries by support.** If a family `A` is snc at `z`, the family `I ⊕ B` is snc
at `z`, and `A` and `B` have the same total support, then `I ⊕ A` is snc at `z`. -/
theorem isSNCAt_sumElim_of_iUnion_support_eq {X : Scheme.{u}} [IsLocallyNoetherian X]
    {Λ Λ' Γ Γ' : Type*} (I : Γ → X.IdealSheafData) (I' : Γ' → X.IdealSheafData) (eI : Γ ≃ Γ')
    (hI : ∀ g, I' (eI g) = I g) (A : Λ → X.IdealSheafData)
    (Bf : Λ' → X.IdealSheafData) (z : X)
    (hsupp : (⋃ i, ((A i).support : Set X)) = ⋃ i, ((Bf i).support : Set X))
    (hA : IsSNCAt A z) (hB : IsSNCAt (Sum.elim I' Bf) z) : IsSNCAt (Sum.elim I A) z := by
  classical
  obtain ⟨n, w, c, hw, hc, hwc⟩ := hA
  obtain ⟨n', w', c', hw', hc', hwc'⟩ := hB
  have key : ∀ a : {i // z ∈ (A i).support}, ∃ b : {k // z ∈ (Bf k).support},
      IdealSheafData.stalk (A a.1) z = IdealSheafData.stalk (Bf b.1) z := by
    intro a
    let P : PrimeSpectrum (X.presheaf.stalk z) :=
      ⟨_, span_singleton_isPrime_of_isRegularSystemOfParameters hw (c a)⟩
    have hPA : X.fromSpecStalk z P ∈ ((A a.1).support : Set X) :=
      (fromSpecStalk_mem_support_iff_stalk_le _ z P).2 (hwc a).le
    have hPB : X.fromSpecStalk z P ∈ ⋃ i, ((Bf i).support : Set X) :=
      hsupp ▸ Set.mem_iUnion.2 ⟨a.1, hPA⟩
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hPB
    have hzk : z ∈ ((Bf k).support : Set X) :=
      (fromSpecStalk_specializes_self z P).mem_closed (Bf k).support.isClosed hk
    have hle := (fromSpecStalk_mem_support_iff_stalk_le _ z P).1 hk
    have hb := hwc' ⟨.inr k, hzk⟩
    refine ⟨⟨k, hzk⟩, ?_⟩
    change _ = IdealSheafData.stalk (Sum.elim I' Bf (.inr k)) z
    rw [hwc a, hb]
    refine (span_singleton_eq_of_mem hw hw' (c a) _ ?_).symm
    have hb' : IdealSheafData.stalk (Bf k) z = Ideal.span {w' (c' ⟨.inr k, hzk⟩)} := hb
    exact hle (hb' ▸ Ideal.mem_span_singleton_self _)
  choose f hf using key
  refine IsSNCAt.of_injective ⟨n', w', c', hw', hc', hwc'⟩ (fun p => match p with
    | ⟨.inl j, hj⟩ => ⟨.inl (eI j), by show z ∈ (I' (eI j)).support; rw [hI j]; exact hj⟩
    | ⟨.inr i, hi⟩ => ⟨.inr (f ⟨i, hi⟩).1, (f ⟨i, hi⟩).2⟩) ?_ ?_
  · rintro ⟨j | i, hi⟩ ⟨j' | i', hi'⟩ h
    · have := congrArg Subtype.val h; simp only [Sum.inl.injEq] at this
      have := eI.injective this; subst this; rfl
    · exact absurd (congrArg Subtype.val h) Sum.inl_ne_inr
    · exact absurd (congrArg Subtype.val h) Sum.inr_ne_inl
    · have h1 : (f ⟨i, hi⟩).1 = (f ⟨i', hi'⟩).1 := by
        have := congrArg Subtype.val h; simpa using this
      have h2 : IdealSheafData.stalk (A i) z = IdealSheafData.stalk (A i') z := by
        rw [hf ⟨i, hi⟩, hf ⟨i', hi'⟩, h1]
      rw [hwc ⟨i, hi⟩, hwc ⟨i', hi'⟩] at h2
      have := MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hw
      have h3 := hc (span_singleton_injective_of_isRegularSystemOfParameters hw h2)
      have := congrArg Subtype.val h3
      simp only at this
      subst this
      rfl
  · rintro ⟨j | i, hi⟩
    · exact congrArg (fun J => IdealSheafData.stalk J z) (hI j).symm
    · exact hf ⟨i, hi⟩

/-! ### The lifting, with the invariant at the last stage -/

/-- The ideals of the final tuple depend only on the tuple, up to the index identification. -/
theorem finalTuple_I_congr {S : Scheme.{u}} (B : ClosedBlowupSequence S)
    {T₁ T₂ : OrderedDivisorTuple S} (e : T₁ = T₂) (j : ℕ) (h₁ : j < (finalTuple B T₁).m)
    (h₂ : j < (finalTuple B T₂).m) : (finalTuple B T₁).I ⟨j, h₁⟩ = (finalTuple B T₂).I ⟨j, h₂⟩ := by
  subst e; rfl

/-- `φ ≫ π = π_S ≫ ι` for the canonical lift `φ` of the pushed-forward centre. -/
theorem canonicalLift_comp_blowUpToBase_map {S W : Scheme.{u}} (ι : S ⟶ W)
    {Z : S.IdealSheafData} (h : (Z.map ι).comap ι = Z) :
    (eqToHom (congrArg blowUp h.symm) ≫ canonicalLift ι (Z.map ι)) ≫ blowUpToBase (Z.map ι) =
      blowUpToBase Z ≫ ι := by
  rw [Category.assoc, canonicalLift_comp_blowUpToBase, ← Category.assoc,
    eqToHom_comp_blowUpToBase h]

/-- **Snc at the strict transform from snc on it.** With the invariant, the restriction of the
ideals agreeing with those of a tuple on `S` and the restricted boundary having the support of its
boundary, snc of that tuple at `z` gives snc of `ι(S)` together with the tuple at `ι z`. -/
theorem isSNCAt_elim_ker_of_mem_sncLocus {k : Type u} [Field k] {S W : Scheme.{u}}
    {ι : S ⟶ W} {s : W ⟶ Spec (.of k)} {T : OrderedDivisorTuple W} (hinv : LiftInvariant ι s T)
    (TS : OrderedDivisorTuple S) (hm : T.m = TS.m)
    (hI : ∀ j : Fin T.m, TS.I (finCongr hm j) = (T.I j).comap ι)
    (hE : (T.E.comap ι).support = TS.E.support) (z : S) (hz : z ∈ TS.sncLocus) :
    IsSNCAt (fun o : Option (Fin T.m ⊕ Fin T.E.s) => o.elim ι.ker T.divisors) (ι z) := by
  have : IsClosedImmersion ι := hinv.1
  have : AlgebraicGeometry.IsVariety k s := hinv.2.1.2.1
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian s
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian (ι ≫ s)
  obtain ⟨n, w, c, hw, hwc, hc⟩ := hinv.2.2.2 (ι z)
  have hinvz : IsSNCAt (fun o : Option (Fin T.E.s) => o.elim ι.ker T.E.E) (ι z) :=
    ⟨n, w, c, hw, hc, hwc⟩
  have hzK : ι z ∈ ι.ker.support := by
    rw [← SetLike.mem_coe, Scheme.Hom.support_ker, ι.isClosedEmbedding.isClosed_range.closure_eq]
    exact ⟨z, rfl⟩
  have hA := isSNCAt_comap_of_isSNCAt_elim ι T.E.E z hinvz
  have hR := isSNCAt_sumElim_of_iUnion_support_eq (fun j => (T.I j).comap ι) TS.I
    (finCongr hm) hI (fun i => (T.E.E i).comap ι) TS.E.E z hE hA hz
  have hR' : IsSNCAt (fun p => (T.divisors p).comap ι) z := by
    convert hR using 2 with p
    rcases p with j | i <;> rfl
  refine isSNCAt_elim_ker_of_isSNCAt_comap ι T.divisors z
    ⟨n, w, c ⟨none, hzK⟩, hw, hwc ⟨none, hzK⟩⟩ (fun p hp => ?_) hR'
  rcases p with j | i
  · exact exists_stalk_eq_span_of_isEffectiveCartierDivisor _ (hinv.2.1.2.2.2.1 j).2 _
  · exact ⟨_, hwc ⟨some i, hp⟩⟩

/-! ### The resolution -/

/-- `T` is resolvable: some strongly valid sequence of order-one transformations of `T` ends with
a tuple that is snc everywhere. -/
def Resolvable {k : Type u} [Field k] {V : Scheme.{u}} (sV : V ⟶ Spec (.of k))
    (T : OrderedDivisorTuple V) : Prop :=
  ∃ B : ClosedBlowupSequence V, ValidS sV B T ∧ (finalTuple B T).sncLocus = Set.univ

/-- It suffices to resolve the tuple reached by a sequence whose centres miss the snc loci. -/
theorem resolvable_of_valid {k : Type u} [Field k] {V : Scheme.{u}}
    {sV : V ⟶ Spec (.of k)} {T : OrderedDivisorTuple V} (B : ClosedBlowupSequence V)
    (hB : ValidS sV B T) (h : Resolvable (B.toBase ≫ sV) (finalTuple B T)) : Resolvable sV T := by
  obtain ⟨B₂, hB₂, hsnc⟩ := h
  exact ⟨B.append B₂, validS_append B B₂ sV T hB hB₂,
    (sncLocus_finalTuple_append_eq_univ_iff B B₂ T).2 hsnc⟩

/-- The snc locus of an ordered divisor tuple contains the generic point. -/
theorem genericPoint_mem_sncLocus {k : Type u} [Field k] {V : Scheme.{u}}
    {sV : V ⟶ Spec (.of k)} {T : OrderedDivisorTuple V} (hT : IsOrderedDivisorTuple sV T) :
    haveI : IsIntegral V := (show AlgebraicGeometry.IsVariety k sV from hT.2.1).toIsIntegral
    genericPoint V ∈ T.sncLocus := by
  haveI : IsIntegral V := (show AlgebraicGeometry.IsVariety k sV from hT.2.1).toIsIntegral
  have hempty : ∀ p : T.indicesAt (genericPoint V), False := by
    rintro ⟨p | p, hp⟩
    · exact notMem_support_of_mem_genericPoints_of_isEffectiveCartierDivisor _ (hT.2.2.2.1 p).2
        (Stacks.Chow.genericPoint_mem_genericPoints V) hp
    · exact notMem_support_of_mem_genericPoints_of_isEffectiveCartierDivisor _
        (hT.2.2.2.2.1 p).2 (Stacks.Chow.genericPoint_mem_genericPoints V) hp
  have hfield : IsField (V.presheaf.stalk (genericPoint V)) :=
    Field.toIsField V.functionField
  refine ⟨0, Fin.elim0, fun p => (hempty p).elim, ⟨?_, ?_⟩, fun p => (hempty p).elim,
    fun p => (hempty p).elim⟩
  · rw [Set.range_eq_empty, Ideal.span_empty]
    exact ((IsLocalRing.isField_iff_maximalIdeal_eq).1 hfield).symm
  · exact ringKrullDim_eq_zero_of_isField hfield

/-! ### Lifting with a parallel tuple -/

/-- A predicate on the stages of a lifted sequence: the closed immersion, the structure map, the
map to the original variety, the lifted tuple, the restricted boundary and a parallel tuple. -/
abbrev LiftPred (k : Type u) [Field k] (W₀ : Scheme.{u}) : Type (u + 1) :=
  ∀ {S' W' : Scheme.{u}}, (S' ⟶ W') → (W' ⟶ Spec (.of k)) → (W' ⟶ W₀) →
    OrderedDivisorTuple W' → OrderedDivisor S' → OrderedDivisorTuple W' → Prop

/-- Every lifted centre carries the stage predicate to the next stage and is a centre of an
order-one transformation of the parallel tuple missing its snc locus. -/
def LiftStep {k : Type u} [Field k] {W₀ : Scheme.{u}} (Q : LiftPred k W₀) : Prop :=
  ∀ {S' W' : Scheme.{u}} (ι : S' ⟶ W') (s : W' ⟶ Spec (.of k)) (p : W' ⟶ W₀)
    (T : OrderedDivisorTuple W') (ES : OrderedDivisor S') (Tx : OrderedDivisorTuple W')
    (Z : S'.IdealSheafData),
    LiftInvariant ι s T → ES.support = (T.E.comap ι).support →
    IsOrderedDivisorTuple (ι ≫ s) ⟨T.m, fun j => (T.I j).comap ι, ES⟩ → Q ι s p T ES Tx →
    (⟨T.m, fun j => (T.I j).comap ι, ES⟩ : OrderedDivisorTuple S').IsTransformCentre (ι ≫ s) Z →
    Disjoint (Z.support : Set S')
      (⟨T.m, fun j => (T.I j).comap ι, ES⟩ : OrderedDivisorTuple S').sncLocus →
    T.IsTransformCentre s (Z.map ι) → ∀ h : (Z.map ι).comap ι = Z,
    Tx.IsTransformCentre s (Z.map ι) ∧ Disjoint ((Z.map ι).support : Set W') Tx.sncLocus ∧
      Q (eqToHom (congrArg blowUp h.symm) ≫ canonicalLift ι (Z.map ι))
        (blowUpToBase (Z.map ι) ≫ s) (blowUpToBase (Z.map ι) ≫ p) (T.transform (Z.map ι))
        (ES.totalTransform Z) (Tx.transform (Z.map ι))

/-- Precomposing with an `eqToHom` does not change the range of a morphism. -/
theorem range_eqToHom_comp {X Y Y' : Scheme.{u}} (e : X = Y) (f : Y ⟶ Y') :
    Set.range (eqToHom e ≫ f) = Set.range f := by
  subst e
  simp

/-- **Lifting with a parallel tuple.** The lift of a strongly valid sequence on `S` carries a
stage predicate `Q` preserved by every lifted centre; the lifted centres are centres of
order-one transformations of the parallel tuple missing its snc loci, and lie over the image of
`ι`. -/
theorem exists_lift_gen {k : Type u} [Field k] {W₀ : Scheme.{u}} (Q : LiftPred k W₀)
    (hQ : LiftStep Q) {S : Scheme.{u}} (B : ClosedBlowupSequence S) :
    ∀ (W : Scheme.{u}) (ι : S ⟶ W) (s : W ⟶ Spec (.of k)) (p : W ⟶ W₀)
      (T : OrderedDivisorTuple W) (ES : OrderedDivisor S) (Tx : OrderedDivisorTuple W),
      LiftInvariant ι s T → ES.support = (T.E.comap ι).support →
      IsOrderedDivisorTuple (ι ≫ s) ⟨T.m, fun j => (T.I j).comap ι, ES⟩ → Q ι s p T ES Tx →
      ValidS (ι ≫ s) B ⟨T.m, fun j => (T.I j).comap ι, ES⟩ →
      ∃ (B' : ClosedBlowupSequence W) (ι' : B.target ⟶ B'.target),
        ValidS s B' Tx ∧ Valid s (Set.range ι)ᶜ B' T ∧
        LiftInvariant ι' (B'.toBase ≫ s) (finalTuple B' T) ∧
        ι' ≫ B'.toBase = B.toBase ≫ ι ∧ Set.range ι' = strictTransformSet B' (Set.range ι) ∧
        (∀ j : Fin T.m, ((finalTuple B' T).I ⟨j, by rw [finalTuple_m]; exact j.2⟩).comap ι' =
          (finalTuple B ⟨T.m, fun j => (T.I j).comap ι, ES⟩).I
            ⟨j, by rw [finalTuple_m]; exact j.2⟩) ∧
        ((finalTuple B' T).E.comap ι').support =
          (finalTuple B ⟨T.m, fun j => (T.I j).comap ι, ES⟩).E.support ∧
        Q ι' (B'.toBase ≫ s) (B'.toBase ≫ p) (finalTuple B' T)
          (finalTuple B ⟨T.m, fun j => (T.I j).comap ι, ES⟩).E (finalTuple B' Tx) := by
  induction B with
  | nil S =>
    intro W ι s p T ES Tx hinv hES _ hQ0 _
    refine ⟨.nil W, ι, trivial, trivial, ?_, ?_, rfl, fun j => rfl, hES.symm, ?_⟩
    · change LiftInvariant ι (𝟙 W ≫ s) T
      rwa [Category.id_comp]
    · change ι ≫ 𝟙 W = 𝟙 S ≫ ι
      simp
    · change Q ι (𝟙 W ≫ s) (𝟙 W ≫ p) T ES Tx
      rwa [Category.id_comp, Category.id_comp]
  | cons Z B ih =>
    intro W ι s p T ES Tx hinv hES hTS hQ0 hB
    have : IsClosedImmersion ι := hinv.1
    have h := comap_map_of_isClosedImmersion ι Z
    have hc := isTransformCentre_map hinv hES hB.1
    obtain ⟨hcx, hdx, hQ1⟩ := hQ ι s p T ES Tx Z hinv hES hTS hQ0 hB.1 hB.2.1 hc h
    have hI := comap_transform_I hinv hc h
    have hE := support_comap_transform_E hinv hc h
    set φ := eqToHom (congrArg blowUp h.symm) ≫ canonicalLift ι (Z.map ι) with hφ
    have hφπ : φ ≫ blowUpToBase (Z.map ι) = blowUpToBase Z ≫ ι :=
      canonicalLift_comp_blowUpToBase_map ι h
    have hbase : φ ≫ blowUpToBase (Z.map ι) ≫ s = blowUpToBase Z ≫ ι ≫ s := by
      rw [← Category.assoc, hφπ, Category.assoc]
    have htuple : (⟨(T.transform (Z.map ι)).m, fun j => ((T.transform (Z.map ι)).I j).comap φ,
        ES.totalTransform Z⟩ : OrderedDivisorTuple (blowUp Z)) =
        (⟨T.m, fun j => (T.I j).comap ι, ES⟩ : OrderedDivisorTuple _).transform Z := by
      simp only [OrderedDivisorTuple.transform]
      congr 1
      funext j
      exact (hI j).trans rfl
    have hZne : Z ≠ ⊥ := by
      rintro rfl
      obtain ⟨x, hx⟩ :
          (⟨T.m, fun j => (T.I j).comap ι, ES⟩ : OrderedDivisorTuple _).sncLocus.Nonempty :=
        ⟨_, genericPoint_mem_sncLocus hTS⟩
      exact hB.2.1.notMem_of_mem_right hx (by rw [Scheme.IdealSheafData.support_bot]; trivial)
    have hTS' : IsOrderedDivisorTuple (φ ≫ blowUpToBase (Z.map ι) ≫ s)
        ⟨(T.transform (Z.map ι)).m, fun j => ((T.transform (Z.map ι)).I j).comap φ,
          ES.totalTransform Z⟩ := by
      rw [hbase, htuple]
      exact isOrderedDivisorTuple_transform hTS hB.1 hZne
    have hB2 : ValidS (φ ≫ blowUpToBase (Z.map ι) ≫ s) B
        ⟨(T.transform (Z.map ι)).m, fun j => ((T.transform (Z.map ι)).I j).comap φ,
          ES.totalTransform Z⟩ := by
      rw [hbase, htuple]; exact hB.2.2
    obtain ⟨B', ι', hVS, hV, hinv', hcomm, hrange, hI', hE', hQf⟩ := ih (blowUp (Z.map ι)) φ
      (blowUpToBase (Z.map ι) ≫ s) (blowUpToBase (Z.map ι) ≫ p) (T.transform (Z.map ι))
      (ES.totalTransform Z) (Tx.transform (Z.map ι)) (liftInvariant_transform hinv hc h)
      ((support_totalTransform_congr hES Z).trans hE.symm) hTS' hQ1 hB2
    have hsupp : ((Z.map ι).support : Set W) = ι '' Z.support := by
      rw [Scheme.IdealSheafData.support_map, TopologicalSpace.Closeds.coe_closure,
        (ι.isClosedEmbedding.isClosedMap _ Z.support.isClosed).closure_eq]
    have hrφ : Set.range φ =
        closure (blowUpToBase (Z.map ι) ⁻¹' (Set.range ι \ (Z.map ι).support)) := by
      rw [hφ, range_eqToHom_comp, range_canonicalLift_eq_closure]
    refine ⟨.cons (Z.map ι) B', ι', ⟨hcx, hdx, hVS⟩, ⟨hc, ?_, hV.mono B' ?_⟩, hinv', ?_, ?_,
      fun j => (hI' j).trans (finalTuple_I_congr B htuple _ _ _),
      hE'.trans (congrArg (fun T' => (finalTuple B T').E.support) htuple), ?_⟩
    · rw [Set.disjoint_left, hsupp]
      rintro _ ⟨z, -, rfl⟩ hx
      exact hx ⟨z, rfl⟩
    · intro x' hx' hr
      obtain ⟨z', rfl⟩ := hr
      have hx'' : (φ ≫ blowUpToBase (Z.map ι)) z' ∈ (Set.range ι)ᶜ := hx'
      rw [hφπ, Scheme.Hom.comp_apply] at hx''
      exact hx'' ⟨_, rfl⟩
    · change ι' ≫ B'.toBase ≫ blowUpToBase (Z.map ι) = (B.toBase ≫ blowUpToBase Z) ≫ ι
      rw [← Category.assoc, hcomm, Category.assoc, hφπ, Category.assoc]
    · change Set.range ι' =
        strictTransformSet B'
          (closure (blowUpToBase (Z.map ι) ⁻¹' (Set.range ι \ (Z.map ι).support)))
      rw [hrange, hrφ]
    · change Q ι' ((B'.toBase ≫ blowUpToBase (Z.map ι)) ≫ s)
        ((B'.toBase ≫ blowUpToBase (Z.map ι)) ≫ p) (finalTuple B' (T.transform (Z.map ι)))
        (finalTuple B ((⟨T.m, fun j => (T.I j).comap ι, ES⟩ : OrderedDivisorTuple _).transform
          Z)).E (finalTuple B' (Tx.transform (Z.map ι)))
      rw [Category.assoc, Category.assoc, ← htuple]
      exact hQf

/-- **The restriction step.** Let `D` be a smooth divisor such that `D` together with the
boundary of `T` is snc, and suppose the restricted tuple on `D` can be resolved. Then there is a
sequence of order-one transformations of `T`, with centres over `D`, after which the strict
transform `D'` of `D` together with the transformed tuple is snc at every point of `D'`; a stage
predicate preserved by the lifted centres holds at the end, and the lifted centres miss the snc
loci of a parallel tuple. -/
theorem exists_validS_restriction_step {k : Type u} [Field k] {V : Scheme.{u}}
    (sV : V ⟶ Spec (.of k)) (T : OrderedDivisorTuple V) (hT : IsOrderedDivisorTuple sV T)
    (D : V.IdealSheafData) (hD : IsSNCFamily sV fun o : Option (Fin T.E.s) => o.elim D T.E.E)
    (hTD : IsOrderedDivisorTuple (D.subschemeι ≫ sV) (restrictTuple D.subschemeι T))
    (hres : Resolvable (D.subschemeι ≫ sV) (restrictTuple D.subschemeι T))
    (Q : LiftPred k V) (hQ : LiftStep Q) (Tx : OrderedDivisorTuple V)
    (hQ0 : Q D.subschemeι sV (𝟙 V) T (T.E.comap D.subschemeι) Tx) :
    ∃ (B' : ClosedBlowupSequence V) (S' : Scheme.{u}) (ι' : S' ⟶ B'.target),
      IrreducibleSpace S' ∧
      (∀ j : Fin (finalTuple B' T).m, ∃ z : S', ι' z ∉ ((finalTuple B' T).I j).support) ∧
      ValidS sV B' Tx ∧ Valid sV (Set.range D.subschemeι)ᶜ B' T ∧
      LiftInvariant ι' (B'.toBase ≫ sV) (finalTuple B' T) ∧
      (∀ z : S', IsSNCAt (fun o : Option (Fin (finalTuple B' T).m ⊕ Fin (finalTuple B' T).E.s) =>
        o.elim ι'.ker (finalTuple B' T).divisors) (ι' z)) ∧
      Set.range (ι' ≫ B'.toBase) ⊆ Set.range D.subschemeι ∧
      Set.range ι' = strictTransformSet B' (Set.range D.subschemeι) ∧
      ∃ ES : OrderedDivisor S',
        Q ι' (B'.toBase ≫ sV) (B'.toBase ≫ 𝟙 V) (finalTuple B' T) ES (finalTuple B' Tx) := by
  obtain ⟨B, hBv, hBsnc⟩ := hres
  have hinv : LiftInvariant D.subschemeι sV T :=
    ⟨inferInstance, hT, by rwa [Scheme.IdealSheafData.ker_subschemeι]⟩
  obtain ⟨B', ι', hVS, hV, hinv', hcomm, hrange, hI', hE', hQf⟩ :=
    exists_lift_gen Q hQ B V D.subschemeι sV (𝟙 V) T (T.E.comap D.subschemeι) Tx hinv rfl hTD
      hQ0 hBv
  have hSvar : AlgebraicGeometry.IsVariety k (D.subschemeι ≫ sV) := hTD.2.1
  have : IsIntegral D.subscheme := hSvar.toIsIntegral
  have : IsLocallyNoetherian D.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (D.subschemeι ≫ sV)
  have : CompactSpace D.subscheme :=
    QuasiCompact.compactSpace_of_compactSpace (D.subschemeι ≫ sV)
  obtain ⟨hTS, -⟩ := isOrderedDivisorTuple_finalTuple B hTD (ValidS.valid B hBv subset_rfl)
    ⟨_, genericPoint_mem_sncLocus hTD⟩
  have hSvar' : AlgebraicGeometry.IsVariety k (B.toBase ≫ D.subschemeι ≫ sV) := hTS.2.1
  have : IsIntegral B.target := hSvar'.toIsIntegral
  refine ⟨B', B.target, ι', inferInstance, fun j => ⟨genericPoint B.target, fun hz => ?_⟩, hVS,
    hV, hinv', fun z => ?_, ?_, hrange, _, hQf⟩
  · have hj : (j : ℕ) < T.m := lt_of_lt_of_eq j.2 (finalTuple_m B' T)
    have h1 : ((finalTuple B' T).I j).comap ι' = _ := hI' ⟨j, hj⟩
    have hz' : genericPoint B.target ∈ (((finalTuple B' T).I j).comap ι').support :=
      (mem_support_comap_iff _ _ _).2 hz
    rw [h1] at hz'
    exact notMem_support_of_mem_genericPoints_of_isEffectiveCartierDivisor _
      (hTS.2.2.2.1 _).2 (Stacks.Chow.genericPoint_mem_genericPoints _) hz'
  · have hm : (finalTuple B' T).m = (finalTuple B (restrictTuple D.subschemeι T)).m := by
      rw [finalTuple_m, finalTuple_m]
    refine isSNCAt_elim_ker_of_mem_sncLocus hinv' _ hm (fun j => ?_) hE' z
      (hBsnc ▸ Set.mem_univ z)
    have := hI' ⟨j, by rw [← finalTuple_m B' T]; exact j.2⟩
    exact this.symm
  · rintro _ ⟨z, rfl⟩
    rw [Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hcomm, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩

/-! ### Components of a smooth divisor -/

section Components

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X]

/-- A divisor whose stalks at the points of its support are generated by a regular parameter. -/
def IsParamDivisor (S : X.IdealSheafData) : Prop :=
  ∀ x ∈ (S.support : Set X), ∃ (n : ℕ) (z : Fin n → X.presheaf.stalk x) (j : Fin n),
    MMP.Mori.IsRegularSystemOfParameters z ∧ IdealSheafData.stalk S x = Ideal.span {z j}

/-- A point of a component `W` of a parameter divisor `S` sees on `Spec 𝒪_{X,x}` exactly the
component through it: `W` there is the zero locus of the parameter. -/
theorem fromSpecStalk_mem_component_iff {S : X.IdealSheafData} {W : Set X}
    (hW : W ∈ componentsOf (S.support : Set X)) {x : X} (hxW : x ∈ W) {n : ℕ}
    {z : Fin n → X.presheaf.stalk x} {j : Fin n} (hz : MMP.Mori.IsRegularSystemOfParameters z)
    (hSx : IdealSheafData.stalk S x = Ideal.span {z j})
    (p : PrimeSpectrum (X.presheaf.stalk x)) : X.fromSpecStalk x p ∈ W ↔ z j ∈ p.asIdeal := by
  have : IsNoetherian X := {}
  have hJ : IdealSheafData.stalk S x = (coordPrime hz {j}).asIdeal := by
    rw [hSx]; simp [coordPrime]
  rw [eq_closure_coordPrime_of_mem_componentsOf hz hJ hW hxW, fromSpecStalk_mem_closure_iff]
  simp [coordPrime, Ideal.span_singleton_le_iff_mem]

/-- Distinct components of a parameter divisor are disjoint. -/
theorem disjoint_of_mem_componentsOf {S : X.IdealSheafData} (hS : IsParamDivisor S)
    {W W' : Set X} (hW : W ∈ componentsOf (S.support : Set X))
    (hW' : W' ∈ componentsOf (S.support : Set X)) (hne : W ≠ W') : Disjoint W W' := by
  have : IsNoetherian X := {}
  rw [Set.disjoint_left]
  intro x hxW hxW'
  have hxS : x ∈ (S.support : Set X) := hW.1.2 hxW
  obtain ⟨n, z, j, hz, hSx⟩ := hS x hxS
  have hJ : IdealSheafData.stalk S x = (coordPrime hz {j}).asIdeal := by
    rw [hSx]; simp [coordPrime]
  exact hne ((eq_closure_coordPrime_of_mem_componentsOf hz hJ hW hxW).trans
    (eq_closure_coordPrime_of_mem_componentsOf hz hJ hW' hxW').symm)

/-- If on `Spec 𝒪_{X,x}` the closed set `A` is the zero locus of the regular parameter `z j`, then
the stalk at `x` of the reduced ideal of `A` is `(z j)`. -/
theorem stalk_vanishingIdeal_of_iff {A : TopologicalSpace.Closeds X} {x : X} {n : ℕ}
    {z : Fin n → X.presheaf.stalk x} {j : Fin n} (hz : MMP.Mori.IsRegularSystemOfParameters z)
    (h : ∀ p : PrimeSpectrum (X.presheaf.stalk x), X.fromSpecStalk x p ∈ (A : Set X) ↔
      z j ∈ p.asIdeal) :
    IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal A) x = Ideal.span {z j} :=
  stalk_vanishingIdeal_eq_span_singleton A x
    (span_singleton_isPrime_of_isRegularSystemOfParameters hz j) h

/-- **Splitting off a component.** For a component `W` of a parameter divisor `S`, the reduced
ideal `D` of `W` and the reduced ideal `J` of the other components satisfy `S = D·J`, `D` has the
stalks of `S` along `W`, and `J` is a unit along `W`. -/
theorem exists_split_component {S : X.IdealSheafData} (hS : IsParamDivisor S)
    {W : Set X} (hW : W ∈ componentsOf (S.support : Set X)) :
    ∃ hWc : IsClosed W, ∃ hJc : IsClosed ((S.support : Set X) \ W),
      S = Scheme.IdealSheafData.vanishingIdeal ⟨W, hWc⟩ *
        Scheme.IdealSheafData.vanishingIdeal ⟨_, hJc⟩ ∧
      (∀ x ∈ W, IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal ⟨W, hWc⟩) x =
        IdealSheafData.stalk S x) ∧
      Disjoint W ((S.support : Set X) \ W) := by
  have : IsNoetherian X := {}
  have hWc : IsClosed W := Aux.isClosed_of_mem_componentsOf S.support.isClosed hW
  obtain ⟨hfin, hcov⟩ := Aux.finite_and_cover_componentsOf (T := X) S.support.isClosed
  have hrest : (S.support : Set X) \ W = ⋃ W' ∈ {W' | W' ∈ componentsOf (S.support : Set X) ∧
      W' ≠ W}, W' := by
    ext x
    simp only [Set.mem_diff, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
    constructor
    · rintro ⟨hx, hxW⟩
      obtain ⟨W', hW', hxW'⟩ := Set.mem_sUnion.1 (hcov hx)
      exact ⟨W', ⟨hW', fun h => hxW (h ▸ hxW')⟩, hxW'⟩
    · rintro ⟨W', ⟨hW', hne⟩, hxW'⟩
      exact ⟨hW'.1.2 hxW', fun hxW =>
        (disjoint_of_mem_componentsOf hS hW hW' hne.symm).notMem_of_mem_left hxW hxW'⟩
  have hJc : IsClosed ((S.support : Set X) \ W) := by
    rw [hrest]
    exact (hfin.subset fun W' h => h.1).isClosed_biUnion fun W' h =>
      Aux.isClosed_of_mem_componentsOf S.support.isClosed h.1
  have hdisj : Disjoint W ((S.support : Set X) \ W) := Set.disjoint_sdiff_right
  have hD : ∀ x ∈ W, IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal ⟨W, hWc⟩) x =
      IdealSheafData.stalk S x := by
    intro x hxW
    obtain ⟨n, z, j, hz, hSx⟩ := hS x (hW.1.2 hxW)
    rw [hSx]
    exact stalk_vanishingIdeal_of_iff hz (fromSpecStalk_mem_component_iff hW hxW hz hSx)
  set D := Scheme.IdealSheafData.vanishingIdeal ⟨W, hWc⟩
  set J := Scheme.IdealSheafData.vanishingIdeal ⟨_, hJc⟩
  have hDsupp : (D.support : Set X) = W := Scheme.IdealSheafData.coe_support_vanishingIdeal _
  have hJsupp : (J.support : Set X) = (S.support : Set X) \ W :=
    Scheme.IdealSheafData.coe_support_vanishingIdeal _
  refine ⟨hWc, hJc, IdealSheafData.eq_of_stalk_eq _ _ fun x => ?_, hD, hdisj⟩
  rw [IdealSheafData.stalk_mul]
  by_cases hxW : x ∈ W
  · rw [hD x hxW, (IdealSheafData.stalk_eq_top_iff_notMem_support J x).2 (by
      rw [← SetLike.mem_coe, hJsupp]; exact hdisj.notMem_of_mem_left hxW), Ideal.mul_top]
  · rw [(IdealSheafData.stalk_eq_top_iff_notMem_support D x).2 (by
      rwa [← SetLike.mem_coe, hDsupp]), Ideal.top_mul]
    by_cases hxS : x ∈ (S.support : Set X)
    · obtain ⟨n, z, j, hz, hSx⟩ := hS x hxS
      rw [hSx]
      refine (stalk_vanishingIdeal_of_iff hz fun p => ?_).symm
      change X.fromSpecStalk x p ∈ (S.support : Set X) \ W ↔ _
      constructor
      · rintro ⟨h1, -⟩
        have h2 := (fromSpecStalk_mem_support_iff_stalk_le S x p).1 h1
        rw [hSx] at h2
        exact h2 (Ideal.mem_span_singleton_self _)
      · intro h
        refine ⟨(fromSpecStalk_mem_support_iff_stalk_le S x p).2 (by
          rwa [hSx, Ideal.span_singleton_le_iff_mem]), fun hW' => hxW ?_⟩
        exact (fromSpecStalk_specializes_self x p).mem_closed hWc hW'
    · rw [(IdealSheafData.stalk_eq_top_iff_notMem_support S x).2 hxS,
        (IdealSheafData.stalk_eq_top_iff_notMem_support J x).2 (by
          rw [← SetLike.mem_coe, hJsupp]; exact fun h => hxS h.1)]

/-- The first member of an snc family `S + E` is a parameter divisor. -/
theorem isParamDivisor_of_isSNCFamily_cons {k : Type u} [Field k]
    {s : X ⟶ Spec (.of k)} {S : X.IdealSheafData} {E : OrderedDivisor X}
    (h : IsSNCFamily s (Fin.cons (α := fun _ => X.IdealSheafData) S E.E)) : IsParamDivisor S := by
  intro x hx
  obtain ⟨n, z, c, hz, hst, -⟩ := h.2 x
  have hx0 : x ∈ ((Fin.cons (α := fun _ => X.IdealSheafData) S E.E) 0).support := by simpa using hx
  exact ⟨n, z, c ⟨0, hx0⟩, hz, by simpa using hst ⟨0, hx0⟩⟩

/-- A component of `S`, with its reduced structure, together with `E` is snc when `S + E` is. -/
theorem isSNCFamily_elim_component {k : Type u} [Field k] [PerfectField k]
    {s : X ⟶ Spec (.of k)} [LocallyOfFiniteType s] {S : X.IdealSheafData} {E : OrderedDivisor X}
    (h : IsSNCFamily s (Fin.cons (α := fun _ => X.IdealSheafData) S E.E))
    {W : Set X} (hW : W ∈ componentsOf (S.support : Set X)) (hWc : IsClosed W) :
    IsSNCFamily s fun o : Option (Fin E.s) =>
      o.elim (Scheme.IdealSheafData.vanishingIdeal ⟨W, hWc⟩) E.E := by
  classical
  have hP := isParamDivisor_of_isSNCFamily_cons h
  obtain ⟨hWc', hJc', heq', hDst, hdisj'⟩ := exists_split_component hP hW
  set D := Scheme.IdealSheafData.vanishingIdeal ⟨W, hWc⟩
  have hDsupp : (D.support : Set X) = W := Scheme.IdealSheafData.coe_support_vanishingIdeal _
  have hpt : ∀ x, ∃ (n : ℕ) (z : Fin n → X.presheaf.stalk x)
      (c : {o // x ∈ ((fun o : Option (Fin E.s) => o.elim D E.E) o).support} → Fin n),
      MMP.Mori.IsRegularSystemOfParameters z ∧
        (∀ o, IdealSheafData.stalk ((fun o : Option (Fin E.s) => o.elim D E.E) o.1) x =
          Ideal.span {z (c o)}) ∧ Function.Injective c := by
    intro x
    obtain ⟨n, z, c, hz, hst, hinj⟩ := h.2 x
    have hmem : ∀ o : {o // x ∈ ((fun o : Option (Fin E.s) => o.elim D E.E) o).support},
        x ∈ ((Fin.cons (α := fun _ => X.IdealSheafData) S E.E)
          (o.1.elim 0 Fin.succ)).support := by
      rintro ⟨_ | i, hi⟩
      · have hxW : x ∈ W := by rwa [← hDsupp]
        change x ∈ ((Fin.cons (α := fun _ => X.IdealSheafData) S E.E) 0).support
        rw [Fin.cons_zero]
        exact hW.1.2 hxW
      · change x ∈ ((Fin.cons (α := fun _ => X.IdealSheafData) S E.E) i.succ).support
        rwa [Fin.cons_succ]
    refine ⟨n, z, fun o => c ⟨_, hmem o⟩, hz, fun o => ?_, ?_⟩
    · rcases o with ⟨_ | i, hi⟩
      · have hxW : x ∈ W := by rwa [← hDsupp]
        change IdealSheafData.stalk D x = _
        rw [hDst x hxW]
        simpa using hst ⟨_, hmem ⟨none, hi⟩⟩
      · simpa using hst ⟨_, hmem ⟨some i, hi⟩⟩
    · rintro ⟨_ | i, hi⟩ ⟨_ | i', hi'⟩ hc
      · rfl
      · exact absurd (congrArg Subtype.val (hinj hc)) (Fin.succ_ne_zero _).symm
      · exact absurd (congrArg Subtype.val (hinj hc)) (Fin.succ_ne_zero _)
      · obtain rfl := Fin.succ_injective _ (congrArg Subtype.val (hinj hc))
        rfl
  have hpar : ∀ o, ∀ y ∈ ((fun o : Option (Fin E.s) => o.elim D E.E) o).support,
      ∃ (m : ℕ) (w : Fin m → X.presheaf.stalk y) (j : Fin m),
        MMP.Mori.IsRegularSystemOfParameters w ∧
          IdealSheafData.stalk ((fun o : Option (Fin E.s) => o.elim D E.E) o) y =
            Ideal.span {w j} := by
    intro o y hy
    obtain ⟨n, z, c, hz, hc, -⟩ := hpt y
    exact ⟨n, z, c ⟨o, hy⟩, hz, hc ⟨o, hy⟩⟩
  refine ⟨fun o => ?_, hpt⟩
  rcases o with _ | i
  · exact ⟨Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _,
      isPureCodimOne_support_of_stalk_eq_span_parameter _ (hpar none),
      isSmoothScheme_subscheme_of_stalk_eq_span_parameter _ _ (hpar none)⟩
  · have := h.1 i.succ
    rw [Fin.cons_succ] at this
    exact this

end Components

/-! ### Restricting to a component -/

/-- A proper irreducible closed subset of a finite-dimensional irreducible space has smaller
dimension. -/
theorem topologicalKrullDim_lt_of_ne_univ {X : Type*} [TopologicalSpace X]
    [IrreducibleSpace X] {W : Set X} (hWc : IsClosed W) (hWi : IsIrreducible W)
    (hne : W ≠ Set.univ) (hfin : topologicalKrullDim X < ⊤) :
    topologicalKrullDim W < topologicalKrullDim X := by
  let W' : TopologicalSpace.IrreducibleCloseds X := ⟨W, hWi, hWc⟩
  let top : TopologicalSpace.IrreducibleCloseds X :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  have hlt : W' < top := lt_of_le_of_ne (fun x _ => Set.mem_univ x) (fun h => hne
    (congrArg (fun C : TopologicalSpace.IrreducibleCloseds X => (C : Set X)) h))
  let f : TopologicalSpace.IrreducibleCloseds W → Set.Iic W' := fun C =>
    ⟨⟨Subtype.val '' (C : Set W), C.isIrreducible.image _ continuous_subtype_val.continuousOn,
      (hWc.isClosedEmbedding_subtypeVal.isClosedMap _ C.isClosed)⟩,
      fun x ⟨y, _, hy⟩ => hy ▸ y.2⟩
  have hf : StrictMono f := by
    intro C C' h
    have h' : (C : Set W) ⊂ C' := h
    change (Subtype.val '' (C : Set W)) ⊂ Subtype.val '' (C' : Set W)
    refine ⟨Set.image_mono h'.1, fun hsub => h'.2 ?_⟩
    intro y hy
    obtain ⟨y', hy', he⟩ := hsub ⟨y, hy, rfl⟩
    rwa [Subtype.val_injective he] at hy'
  have h1 : topologicalKrullDim W ≤ Order.height W' := by
    rw [Order.height_eq_krullDim_Iic]
    exact Order.krullDim_le_of_strictMono f hf
  have h2 : Order.height W' < ⊤ := by
    have := (Order.height_le_krullDim W').trans_lt hfin
    exact WithBot.coe_lt_coe.1 (by simpa using this)
  calc topologicalKrullDim W ≤ Order.height W' := h1
    _ < Order.height top := WithBot.coe_lt_coe.2 (Order.height_strictMono hlt h2)
    _ ≤ topologicalKrullDim X := Order.height_le_krullDim top

/-- The irreducible component of an irreducible closed set is itself. -/
theorem eq_of_mem_componentsOf_of_isIrreducible {X : Type*} [TopologicalSpace X]
    {W W' : Set X} (hWi : IsIrreducible W) (hW' : W' ∈ componentsOf W) : W' = W :=
  le_antisymm hW'.1.2 (hW'.2 ⟨hWi, le_rfl⟩ hW'.1.2)

/-- **The restricted tuple on a component.** Let `W` be an irreducible closed subset whose reduced
ideal `D` together with the boundary of `T` is snc, and no ideal of `T` vanishes on `W`. Then
`(D, T|_D)` is an ordered divisor tuple of smaller dimension. -/
theorem isOrderedDivisorTuple_restrictTuple {k : Type u} [Field k] {V : Scheme.{u}}
    {sV : V ⟶ Spec (.of k)} {T : OrderedDivisorTuple V} (hT : IsOrderedDivisorTuple sV T)
    {W : Set V} (hWc : IsClosed W) (hWi : IsIrreducible W)
    (hD : IsSNCFamily sV fun o : Option (Fin T.E.s) =>
      o.elim (Scheme.IdealSheafData.vanishingIdeal ⟨W, hWc⟩) T.E.E)
    (hI : ∀ j, ¬ W ⊆ ((T.I j).support : Set V)) :
    IsOrderedDivisorTuple ((Scheme.IdealSheafData.vanishingIdeal ⟨W, hWc⟩).subschemeι ≫ sV)
      (restrictTuple (Scheme.IdealSheafData.vanishingIdeal ⟨W, hWc⟩).subschemeι T) := by
  set D := Scheme.IdealSheafData.vanishingIdeal ⟨W, hWc⟩
  set ι := D.subschemeι
  have : CharZero k := hT.1
  have : AlgebraicGeometry.IsVariety k sV := hT.2.1
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian sV
  have : IsLocallyNoetherian D.subscheme := LocallyOfFiniteType.isLocallyNoetherian (ι ≫ sV)
  have hDsupp : (D.support : Set V) = W := Scheme.IdealSheafData.coe_support_vanishingIdeal _
  have hrange : Set.range ι = W := by rw [Scheme.IdealSheafData.range_subschemeι, hDsupp]
  have : IsReduced D.subscheme := Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  have : IrreducibleSpace D.subscheme := by
    have e := ι.isClosedEmbedding.isEmbedding.toHomeomorph
    rw [e.irreducibleSpace_iff, hrange]
    exact Subtype.irreducibleSpace hWi
  have : IsIntegral D.subscheme := isIntegral_of_irreducibleSpace_of_isReduced _
  have hvar : AlgebraicGeometry.IsVariety k (ι ≫ sV) := ⟨⟩
  have hcompW : ∀ W' ∈ componentsOf (D.support : Set V), W' = W := fun W' hW' => by
    rw [hDsupp] at hW'; exact eq_of_mem_componentsOf_of_isIrreducible hWi hW'
  have hkerι : ∀ z : D.subscheme, RingHom.ker (ι.stalkMap z).hom =
      IdealSheafData.stalk D (ι z) := fun z => by
    rw [ker_stalkMap_eq_stalk_ker ι z, Scheme.IdealSheafData.ker_subschemeι]
  refine ⟨hT.1, hvar, (hD.1 none).2.2, fun j => ?_, ?_⟩
  · -- the restricted ideals are effective Cartier divisors
    have hcart : Stacks.Divisors.IsEffectiveCartierDivisor ((T.I j).comap ι) := by
      refine Stacks.Divisors.isEffectiveCartierDivisor_of_stalk_isPrincipal_nonZeroDivisor _
        fun z _ => ?_
      obtain ⟨e, he⟩ := exists_stalk_eq_span_of_isEffectiveCartierDivisor _ (hT.2.2.2.1 j).2 (ι z)
      refine ⟨(ι.stalkMap z).hom e, mem_nonZeroDivisors_of_ne_zero fun h0 => ?_, ?_⟩
      · have hmem : e ∈ IdealSheafData.stalk D (ι z) := by
          rwa [← hkerι z]
        have hle : IdealSheafData.stalk (T.I j) (ι z) ≤ IdealSheafData.stalk D (ι z) := by
          rwa [he, Ideal.span_singleton_le_iff_mem]
        have hzD : ι z ∈ D.support := by
          rw [← SetLike.mem_coe, ← D.range_subschemeι]; exact ⟨z, rfl⟩
        obtain ⟨W', hW', -, hW'I⟩ :=
          exists_mem_componentsOf_subset_support_of_stalk_le (T.I j) D hzD hle
        exact hI j (hcompW W' hW' ▸ hW'I)
      · rw [idealStalk_comap_eq_map, he, Ideal.map_span, Set.image_singleton]
    exact ⟨AlgebraicGeometry.ne_bot_of_isEffectiveCartierDivisor hcart, hcart⟩
  · -- the restricted boundary is an ordered snc divisor
    have hHas : HasSNCWith T.E.E D := by
      intro x hx
      obtain ⟨n, z, c, hz, hzc, hc⟩ := hD.2 x
      refine ⟨n, z, fun i => c ⟨some i.1, i.2⟩, {c ⟨none, hx⟩}, hz, fun i => hzc ⟨some i.1, i.2⟩,
        fun i i' h => ?_, ?_⟩
      · exact Subtype.ext (Option.some_injective _ (congrArg Subtype.val (hc h)))
      · rw [show IdealSheafData.stalk D x = Ideal.span {z (c ⟨none, hx⟩)} from hzc ⟨none, hx⟩]
        simp
    have hcomp : ∀ i, ∀ W' ∈ componentsOf (D.support : Set V), ¬ W' ⊆ (T.E.E i).support := by
      intro i W' hW' hsub
      rw [hcompW W' hW'] at hsub
      obtain ⟨x, hxW⟩ := hWi.nonempty
      have hxD : x ∈ D.support := by rwa [← SetLike.mem_coe, hDsupp]
      have hxE : x ∈ (T.E.E i).support := hsub hxW
      obtain ⟨n, z, c, hz, hzc, hc⟩ := hD.2 x
      have hDx : IdealSheafData.stalk D x = Ideal.span {z (c ⟨none, hxD⟩)} := hzc ⟨none, hxD⟩
      have hEx : IdealSheafData.stalk (T.E.E i) x = Ideal.span {z (c ⟨some i, hxE⟩)} :=
        hzc ⟨some i, hxE⟩
      let P : PrimeSpectrum (V.presheaf.stalk x) :=
        ⟨_, span_singleton_isPrime_of_isRegularSystemOfParameters hz (c ⟨none, hxD⟩)⟩
      have hPW : V.fromSpecStalk x P ∈ W := by
        rw [← hDsupp]; exact (fromSpecStalk_mem_support_iff_stalk_le D x P).2 hDx.le
      have hle := (fromSpecStalk_mem_support_iff_stalk_le (T.E.E i) x P).1 (hsub hPW)
      rw [hEx, Ideal.span_singleton_le_iff_mem] at hle
      have hne : c ⟨none, hxD⟩ ≠ c ⟨some i, hxE⟩ := fun h =>
        Option.some_ne_none i (congrArg Subtype.val (hc h)).symm
      exact notMem_span_singleton_of_ne_of_isRegularSystemOfParameters hz hne hle
    have hsnc := isSNCFamily_comap_subschemeι_of_hasSNCWith sV hT.2.2.1 hT.2.2.2.2.2 hHas hcomp
    refine ⟨fun i => ⟨(hsnc.1 i).1, isEffectiveCartierDivisor_of_stalk_eq_span_parameter _
      fun y hy => ?_⟩, hsnc⟩
    obtain ⟨m, w, c, hw, hwc, -⟩ := hsnc.2 y
    exact ⟨m, w, c ⟨i, hy⟩, hw, hwc ⟨i, hy⟩⟩

/-- The ordered divisor tuple without its first ideal. -/
def dropFirst {V : Scheme.{u}} (T : OrderedDivisorTuple V) : OrderedDivisorTuple V :=
  ⟨T.m - 1, fun j => T.I ⟨j + 1, by have := j.isLt; omega⟩, T.E⟩

/-- The index map from the tuple without its first ideal to the tuple. -/
def dropFirstIndex {V : Scheme.{u}} (T : OrderedDivisorTuple V) :
    Fin (dropFirst T).m ⊕ Fin (dropFirst T).E.s → Fin T.m ⊕ Fin T.E.s :=
  Sum.map (fun j => ⟨j + 1, by have := j.isLt; simp only [dropFirst] at this; omega⟩) id

/-- The index map from the tuple without its first ideal is injective. -/
theorem dropFirstIndex_injective {V : Scheme.{u}} (T : OrderedDivisorTuple V) :
    Function.Injective (dropFirstIndex T) :=
  Sum.map_injective.2 ⟨fun a b h => Fin.ext (by
    have := congrArg Fin.val h; simp only at this; omega), Function.injective_id⟩

/-- The divisors of the tuple without its first ideal are those of the tuple, reindexed. -/
theorem divisors_dropFirst {V : Scheme.{u}} (T : OrderedDivisorTuple V)
    (p : Fin (dropFirst T).m ⊕ Fin (dropFirst T).E.s) :
    (dropFirst T).divisors p = T.divisors (dropFirstIndex T p) := by
  rcases p with j | i <;> rfl

/-- The index map from the tuple without its first ideal misses the first ideal. -/
theorem dropFirstIndex_ne_zero {V : Scheme.{u}} (T : OrderedDivisorTuple V) (h0 : 0 < T.m)
    (p : Fin (dropFirst T).m ⊕ Fin (dropFirst T).E.s) : dropFirstIndex T p ≠ Sum.inl ⟨0, h0⟩ := by
  rcases p with j | i
  · intro he
    have := congrArg (fun q => Sum.elim (fun a : Fin T.m => (a : ℕ)) (fun _ => 0) q) he
    change (j : ℕ) + 1 = 0 at this
    omega
  · intro he
    exact Sum.inr_ne_inl he

/-- Dropping the first ideal commutes with transforming along a sequence. -/
theorem finalTuple_dropFirst : ∀ {S : Scheme.{u}} (B : ClosedBlowupSequence S)
    (T : OrderedDivisorTuple S), finalTuple B (dropFirst T) = dropFirst (finalTuple B T) := by
  intro S B
  induction B with
  | nil S => intro T; rfl
  | cons Z B ih => intro T; exact ih (T.transform Z)

/-- Every ordered divisor tuple on a `k`-variety of dimension at most `n` is resolvable. -/
def ResolvableUpTo (k : Type u) [Field k] (n : ℕ) : Prop :=
  ∀ {V : Scheme.{u}} (sV : V ⟶ Spec (.of k)) (T : OrderedDivisorTuple V),
    IsOrderedDivisorTuple sV T → topologicalKrullDim V ≤ n → Resolvable sV T

/-- The blow-up of a variety along a nonzero ideal has at most its dimension. -/
theorem topologicalKrullDim_blowUp_le {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k s] {Z : X.IdealSheafData}
    (hne : Z ≠ ⊥) : topologicalKrullDim (blowUp Z) ≤ topologicalKrullDim X := by
  have hvar := (MMP.Flips.ResolutionInputs.isVariety_blowUp_and_isProjective_and_isBirational
    s Z hne).1
  have : IsIntegral (blowUp Z) := hvar.toIsIntegral
  have huniv : (Set.univ : Set (blowUp Z)) ∈ irreducibleComponents (blowUp Z) :=
    ⟨IrreducibleSpace.isIrreducible_univ _, fun _ _ _ => Set.subset_univ _⟩
  obtain ⟨D, -, hD⟩ :=
    exists_topologicalKrullDim_eq_of_mem_irreducibleComponents_blowUp s Z huniv
  rw [← IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ (blowUp Z)).isHomeomorph, hD]
  exact topologicalKrullDim_subspace_le _ _

/-- Blowing up preserves the dimension bound. -/
theorem topologicalKrullDim_target_le {k : Type u} [Field k] :
    ∀ {V : Scheme.{u}} (B : ClosedBlowupSequence V) {sV : V ⟶ Spec (.of k)}
      {T : OrderedDivisorTuple V}, IsOrderedDivisorTuple sV T → ∀ {N : Set V}, N.Nonempty →
      Valid sV N B T → topologicalKrullDim B.target ≤ topologicalKrullDim V := by
  intro V B
  induction B with
  | nil V => intros; exact le_rfl
  | @cons X Z B ih =>
    intro sV T hT N hN h
    have hne : Z ≠ ⊥ := by
      rintro rfl
      obtain ⟨x, hx⟩ := hN
      exact h.2.1.notMem_of_mem_right hx (by rw [Scheme.IdealSheafData.support_bot]; trivial)
    have hvar : AlgebraicGeometry.IsVariety k sV := hT.2.1
    have h1 := isOrderedDivisorTuple_finalTuple (.cons Z (.nil _)) hT
      ⟨h.1, h.2.1, trivial⟩ hN
    obtain ⟨y, hy⟩ := h1.2
    exact (ih (isOrderedDivisorTuple_transform hT h.1 hne) (N := blowUpToBase Z ⁻¹' N) ⟨y, hy⟩
      h.2.2).trans (topologicalKrullDim_blowUp_le sV hne)

/-- A tuple without ideals is snc everywhere. -/
theorem sncLocus_eq_univ_of_m_eq_zero {k : Type u} [Field k] {V : Scheme.{u}}
    {sV : V ⟶ Spec (.of k)} {T : OrderedDivisorTuple V} (hT : IsOrderedDivisorTuple sV T)
    (hm : T.m = 0) : T.sncLocus = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  obtain ⟨n, z, c, hz, hst, hinj⟩ := hT.2.2.2.2.2.2 x
  have h : IsSNCAt T.E.E x := ⟨n, z, c, hz, hinj, hst⟩
  refine IsSNCAt.of_injective h (fun p => match p with
    | ⟨.inl j, _⟩ => absurd j.isLt (by omega)
    | ⟨.inr i, hi⟩ => ⟨i, hi⟩) ?_ ?_
  · rintro ⟨j | i, hi⟩ ⟨j' | i', hi'⟩ h
    · exact absurd j.isLt (by omega)
    · exact absurd j.isLt (by omega)
    · exact absurd j'.isLt (by omega)
    · have h' := congrArg Subtype.val h
      simp only at h'
      subst h'
      rfl
  · rintro ⟨j | i, hi⟩
    · exact absurd j.isLt (by omega)
    · rfl

/-- The first ideal of `T` is reduced and its stalks along its cosupport are generated by
regular parameters. -/
structure FirstIdealData {k : Type u} [Field k] {V : Scheme.{u}}
    (sV : V ⟶ Spec (.of k)) (T : OrderedDivisorTuple V) (h0 : 0 < T.m) : Prop where
  /-- The first ideal is reduced. -/
  reduced : T.I ⟨0, h0⟩ = Scheme.IdealSheafData.vanishingIdeal (T.I ⟨0, h0⟩).support
  /-- Its stalks at the points of its cosupport are generated by regular parameters. -/
  param : ∀ x ∈ ((T.I ⟨0, h0⟩).support : Set V), ∃ (n : ℕ) (z : Fin n → V.presheaf.stalk x)
    (j : Fin n), MMP.Mori.IsRegularSystemOfParameters z ∧
      IdealSheafData.stalk (T.I ⟨0, h0⟩) x = Ideal.span {z j}

/-- `FirstIdealData` from an ideal equal to the first ideal that is reduced with stalks
generated by regular parameters. -/
theorem FirstIdealData.of_eq {k : Type u} [Field k] {V : Scheme.{u}}
    {s : V ⟶ Spec (.of k)} {T : OrderedDivisorTuple V} {h0 : 0 < T.m} {K : V.IdealSheafData}
    (hK : T.I ⟨0, h0⟩ = K) (hred : K = Scheme.IdealSheafData.vanishingIdeal K.support)
    (hpar : ∀ x ∈ (K.support : Set V), ∃ (n : ℕ) (z : Fin n → V.presheaf.stalk x) (j : Fin n),
      MMP.Mori.IsRegularSystemOfParameters z ∧ IdealSheafData.stalk K x = Ideal.span {z j}) :
    FirstIdealData s T h0 := by
  subst hK
  exact ⟨hred, hpar⟩

/-- The first ideal can be made reduced with smooth cosupport. -/
theorem exists_valid_firstIdealData {k : Type u} [Field k] {V : Scheme.{u}}
    (sV : V ⟶ Spec (.of k)) (T : OrderedDivisorTuple V) (hT : IsOrderedDivisorTuple sV T)
    (h0 : 0 < T.m) :
    ∃ B : ClosedBlowupSequence V, ValidS sV B T ∧ ∃ h : 0 < (finalTuple B T).m,
      FirstIdealData (B.toBase ≫ sV) (finalTuple B T) h := by
  obtain ⟨B, hB⟩ := OrderedDivisorTuple.exists_transform_isSmoothScheme_support sV T hT ⟨0, h0⟩
  replace hB := validS_of_rec sV T.sncLocus
    (fun {S} (p : S ⟶ V) (T' : OrderedDivisorTuple S) =>
    ∀ h : 0 < T'.m, MMP.Mori.IsSmoothScheme
      ((Scheme.IdealSheafData.vanishingIdeal (T'.I ⟨0, h⟩).support).subschemeι ≫ p ≫ sV) ∧
      T'.I ⟨0, h⟩ = Scheme.IdealSheafData.vanishingIdeal (T'.I ⟨0, h⟩).support ∧
      ∀ x ∈ ((T'.I ⟨0, h⟩).support : Set S), ∃ (n : ℕ) (z : Fin n → S.presheaf.stalk x)
        (j : Fin n), MMP.Mori.IsRegularSystemOfParameters z ∧
          IdealSheafData.stalk (T'.I ⟨0, h⟩) x = Ideal.span {z j}) B (𝟙 V) T hB
  simp only [Category.comp_id, Category.id_comp] at hB
  have h : 0 < (finalTuple B T).m := by rw [finalTuple_m]; exact h0
  exact ⟨B, hB.1, h, ⟨(hB.2 h).2.1, (hB.2 h).2.2⟩⟩

/-- A proper irreducible closed subset `W` of a variety of dimension `≤ n`, with its reduced
structure, has dimension `≤ n'` for some `n' < n`. -/
theorem exists_lt_topologicalKrullDim_subscheme_le {k : Type u} [Field k] {V : Scheme.{u}}
    (sV : V ⟶ Spec (.of k)) [hvar : AlgebraicGeometry.IsVariety k sV] {W : Set V}
    (hWc : IsClosed W) (hWi : IsIrreducible W) (hne : W ≠ Set.univ) {n : ℕ}
    (hdim : topologicalKrullDim V ≤ n) :
    ∃ n' < n,
      topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal ⟨W, hWc⟩).subscheme ≤ n' := by
  set D := Scheme.IdealSheafData.vanishingIdeal ⟨W, hWc⟩
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace sV
  have : IsIntegral V := hvar.toIsIntegral
  have hrange : Set.range D.subschemeι ⊆ W := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have h1 : topologicalKrullDim D.subscheme ≤ topologicalKrullDim W :=
    (D.subschemeι.isClosedEmbedding.isInducing.codRestrict
      (fun z => hrange ⟨z, rfl⟩)).topologicalKrullDim_le
  have hfin : topologicalKrullDim V < ⊤ :=
    lt_top_iff_ne_top.2 (topologicalKrullDim_ne_top_of_locallyOfFiniteType k sV)
  have h2 := topologicalKrullDim_lt_of_ne_univ hWc hWi hne hfin
  obtain ⟨x, hx⟩ := hWi.nonempty
  have h0 : 0 ≤ topologicalKrullDim W := by
    haveI : Nonempty (TopologicalSpace.IrreducibleCloseds W) :=
      ⟨⟨closure {⟨x, hx⟩}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
    exact Order.krullDim_nonneg
  have h3 : topologicalKrullDim W < n := lt_of_lt_of_le h2 hdim
  obtain ⟨m, hm, hle⟩ : ∃ m : ℕ, m < n ∧ topologicalKrullDim W ≤ m := by
    generalize topologicalKrullDim W = d at h0 h3
    induction d using WithBot.recBotCoe with
    | bot => exact absurd h0 (by simp)
    | coe e =>
      induction e using ENat.recTopCoe with
      | top => exact absurd h3 (by simp)
      | coe m => exact ⟨m, by exact_mod_cast h3, le_rfl⟩
  exact ⟨m, hm, h1.trans hle⟩

/-- Validity of a sequence depends only on the boundary of the tuple, not on its ideals: tuples
with the same boundary have the same valid sequences. -/
theorem valid_congr_E {k : Type u} [Field k] : ∀ {S : Scheme.{u}}
    (B : ClosedBlowupSequence S) (s : S ⟶ Spec (.of k)) (N : Set S) (T T' : OrderedDivisorTuple S),
    T.E = T'.E → (Valid s N B T ↔ Valid s N B T') := by
  intro S B
  induction B with
  | nil S => intros; exact Iff.rfl
  | cons Z B ih =>
    intro s N T T' hE
    refine and_congr
      (by rw [OrderedDivisorTuple.IsTransformCentre, OrderedDivisorTuple.IsTransformCentre, hE])
      (and_congr_right fun _ => ih _ _ _ _ ?_)
    rw [OrderedDivisorTuple.transform_E, OrderedDivisorTuple.transform_E, hE]

/-- The final boundary depends only on the original boundary. -/
theorem finalTuple_E_congr : ∀ {S : Scheme.{u}} (B : ClosedBlowupSequence S)
    (T T' : OrderedDivisorTuple S), T.E = T'.E → (finalTuple B T).E = (finalTuple B T').E := by
  intro S B
  induction B with
  | nil S => intro T T' h; exact h
  | cons Z B ih =>
    intro T T' h
    exact ih _ _ (by rw [OrderedDivisorTuple.transform_E, OrderedDivisorTuple.transform_E, h])

/-- A family snc at every point is an snc family. -/
theorem isSNCFamily_of_forall_isSNCAt {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} [IsLocallyNoetherian X] {s : X ⟶ Spec (.of k)} [LocallyOfFiniteType s]
    {Λ : Type*} {F : Λ → X.IdealSheafData} (h : ∀ y, IsSNCAt F y) : IsSNCFamily s F := by
  have hpar : ∀ i, ∀ y ∈ (F i).support, ∃ (m : ℕ) (w : Fin m → X.presheaf.stalk y) (j : Fin m),
      MMP.Mori.IsRegularSystemOfParameters w ∧ IdealSheafData.stalk (F i) y = Ideal.span {w j} := by
    intro i y hy
    obtain ⟨n, z, c, hz, -, hc⟩ := h y
    exact ⟨n, z, c ⟨i, hy⟩, hz, hc ⟨i, hy⟩⟩
  refine ⟨fun i => ⟨isReduced_subscheme_of_stalk_eq_span_parameter _ (hpar i),
    isPureCodimOne_support_of_stalk_eq_span_parameter _ (hpar i),
    isSmoothScheme_subscheme_of_stalk_eq_span_parameter _ _ (hpar i)⟩, fun y => ?_⟩
  obtain ⟨n, z, c, hz, hc, hzc⟩ := h y
  exact ⟨n, z, c, hz, hzc, hc⟩

/-- Adding a member that is a unit at `y` to a family snc at `y` keeps it snc at `y`. -/
theorem isSNCAt_cons_of_notMem {X : Scheme.{u}} {Λ : Type*} {F₀ : X.IdealSheafData}
    {F : Λ → X.IdealSheafData} {y : X} (hy : y ∉ F₀.support) (h : IsSNCAt F y) {n : ℕ}
    (G : Fin (n + 1) → X.IdealSheafData) (hG0 : G 0 = F₀) (e : Fin n → Λ)
    (he : Function.Injective e) (hGs : ∀ i, G i.succ = F (e i)) : IsSNCAt G y := by
  refine IsSNCAt.of_injective h (fun p => ⟨e (p.1.pred (fun h0 => by
      have := p.2; rw [h0, hG0] at this; exact hy this)), by
      have := p.2; rw [← Fin.succ_pred p.1 (fun h0 => by
        have := p.2; rw [h0, hG0] at this; exact hy this), hGs] at this; exact this⟩) ?_ ?_
  · intro p q hpq
    have := he (congrArg Subtype.val hpq)
    exact Subtype.ext (Fin.pred_inj.1 this)
  · intro p
    dsimp only
    conv_lhs => rw [← Fin.succ_pred p.1 (fun h0 => by
      have := p.2; rw [h0, hG0] at this; exact hy this)]
    rw [hGs]

/-- Snc of `K` together with `I ⊕ E` at `y` gives snc of `F₀` together with `E` when `F₀` has the
stalk of `K` there. -/
theorem isSNCAt_cons_of_isSNCAt_elim {X : Scheme.{u}} {Λ : Type*} {s : ℕ}
    {K F₀ : X.IdealSheafData} {I : Λ → X.IdealSheafData} {E : Fin s → X.IdealSheafData} {y : X}
    (h : IsSNCAt (fun o : Option (Λ ⊕ Fin s) => o.elim K (Sum.elim I E)) y)
    (hK : IdealSheafData.stalk F₀ y = IdealSheafData.stalk K y) :
    IsSNCAt (Fin.cons (α := fun _ => X.IdealSheafData) F₀ E) y := by
  let g : Fin (s + 1) → Option (Λ ⊕ Fin s) :=
    Fin.cons (α := fun _ => Option (Λ ⊕ Fin s)) none fun e => some (.inr e)
  have hg : Function.Injective g := by
    intro a b hab
    induction a using Fin.cases <;> induction b using Fin.cases <;>
      simp_all [g, Fin.cons_zero, Fin.cons_succ]
  have hst : ∀ a, IdealSheafData.stalk ((fun o : Option (Λ ⊕ Fin s) =>
      o.elim K (Sum.elim I E)) (g a)) y =
      IdealSheafData.stalk ((Fin.cons (α := fun _ => X.IdealSheafData) F₀ E) a) y := by
    intro a
    induction a using Fin.cases with
    | zero => simp [g, hK]
    | succ e => simp [g]
  have hsupp : ∀ a, y ∈ ((Fin.cons (α := fun _ => X.IdealSheafData) F₀ E) a).support →
      y ∈ ((fun o : Option (Λ ⊕ Fin s) => o.elim K (Sum.elim I E)) (g a)).support := by
    intro a ha
    rw [← (IdealSheafData.stalk_eq_top_iff_notMem_support _ _).not_left] at ha ⊢
    rwa [hst]
  refine IsSNCAt.of_injective h (fun p => ⟨g p.1, hsupp p.1 p.2⟩) ?_ fun p => (hst p.1).symm
  intro p q hpq
  exact Subtype.ext (hg (congrArg Subtype.val hpq))

/-- A tuple snc at `y` makes its first ideal together with its boundary snc there. -/
theorem isSNCAt_cons_of_mem_sncLocus {X : Scheme.{u}} (R : OrderedDivisorTuple X)
    (h0 : 0 < R.m) {y : X} (hy : y ∈ R.sncLocus) {F₀ : X.IdealSheafData}
    (hF : F₀ = R.I ⟨0, h0⟩) {E : OrderedDivisor X} (hE : R.E = E) :
    IsSNCAt (Fin.cons (α := fun _ => X.IdealSheafData) F₀ E.E) y := by
  subst hF hE
  let g : Fin (R.E.s + 1) → Fin R.m ⊕ Fin R.E.s :=
    Fin.cons (α := fun _ => Fin R.m ⊕ Fin R.E.s) (.inl ⟨0, h0⟩) .inr
  have hg : Function.Injective g := by
    intro a b hab
    induction a using Fin.cases <;> induction b using Fin.cases <;>
      simp_all [g, Fin.cons_zero, Fin.cons_succ]
  have hst : ∀ a, R.divisors (g a) = (Fin.cons (α := fun _ => X.IdealSheafData)
      (R.I ⟨0, h0⟩) R.E.E) a := by
    intro a
    induction a using Fin.cases with
    | zero => simp [g]
    | succ e => simp [g]
  refine IsSNCAt.of_injective hy (fun p => ⟨g p.1, by rw [hst]; exact p.2⟩) ?_
    fun p => by rw [hst]
  intro p q hpq
  exact Subtype.ext (hg (congrArg Subtype.val hpq))

/-- Over an open on which a morphism is an isomorphism, preimages of irreducible sets are
irreducible. -/
theorem isIrreducible_preimage_of_isIso_restrict {X Y : Scheme.{u}} (p : Y ⟶ X)
    (U : X.Opens) [IsIso (p ∣_ U)] {A : Set X} (hA : IsIrreducible A) (hAU : A ⊆ U) :
    IsIrreducible (p ⁻¹' A) := by
  set g := p ∣_ U
  let e := TopCat.homeoOfIso (Scheme.forgetToTop.mapIso (asIso g))
  have hval : ∀ y, U.ι (g y) = p ((p ⁻¹ᵁ U).ι y) := fun y => by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
  have hB : IsIrreducible (U.ι ⁻¹' A) := by
    obtain ⟨x, hx⟩ := hA.nonempty
    refine ⟨?_, hA.2.preimage U.ι.isOpenEmbedding⟩
    obtain ⟨u, rfl⟩ : x ∈ Set.range U.ι := by rw [Scheme.Opens.range_ι]; exact hAU hx
    exact ⟨u, hx⟩
  have hC : IsIrreducible (g ⁻¹' (U.ι ⁻¹' A)) := by
    have : g ⁻¹' (U.ι ⁻¹' A) = e.symm '' (U.ι ⁻¹' A) := by
      rw [e.image_symm]; rfl
    rw [this]
    exact hB.image _ e.symm.continuous.continuousOn
  have heq : p ⁻¹' A = (p ⁻¹ᵁ U).ι '' (g ⁻¹' (U.ι ⁻¹' A)) := by
    ext y
    constructor
    · intro hy
      obtain ⟨y', rfl⟩ : y ∈ Set.range (p ⁻¹ᵁ U).ι := by
        rw [Scheme.Opens.range_ι]; exact hAU hy
      exact ⟨y', by simpa [Set.mem_preimage, hval] using hy, rfl⟩
    · rintro ⟨y', hy', rfl⟩
      simpa [Set.mem_preimage, hval] using hy'
  rw [heq]
  exact hC.image _ (p ⁻¹ᵁ U).ι.continuous.continuousOn

/-- Snc of `K` together with the tuple without its first ideal, the first ideal having the stalk
of `K`, gives snc of the tuple. -/
theorem mem_sncLocus_of_isSNCAt_elim_dropFirst {X : Scheme.{u}} (T : OrderedDivisorTuple X)
    (h0 : 0 < T.m) {K : X.IdealSheafData} {y : X}
    (h : IsSNCAt (fun o : Option (Fin (dropFirst T).m ⊕ Fin (dropFirst T).E.s) =>
      o.elim K (dropFirst T).divisors) y)
    (hK : IdealSheafData.stalk (T.I ⟨0, h0⟩) y = IdealSheafData.stalk K y) : y ∈ T.sncLocus := by
  let g : Fin T.m ⊕ Fin T.E.s → Option (Fin (dropFirst T).m ⊕ Fin (dropFirst T).E.s) :=
    Sum.elim (fun j => if hj : (j : ℕ) = 0 then none else
      some (.inl ⟨(j : ℕ) - 1, by have := j.isLt; simp only [dropFirst]; omega⟩))
      (fun e => some (.inr e))
  have hg : Function.Injective g := by
    rintro (j | e) (j' | e') h <;> simp only [g, Sum.elim_inl, Sum.elim_inr] at h
    · by_cases hj : (j : ℕ) = 0 <;> by_cases hj' : (j' : ℕ) = 0 <;> simp [hj, hj'] at h
      · exact congrArg Sum.inl (Fin.ext (hj.trans hj'.symm))
      · exact congrArg Sum.inl (Fin.ext (by omega))
    · split_ifs at h <;> simp at h
    · split_ifs at h <;> simp at h
    · simp only [Option.some.injEq] at h; exact congrArg Sum.inr (Sum.inr.inj h)
  have hst : ∀ p, IdealSheafData.stalk ((fun o : Option (Fin (dropFirst T).m ⊕
      Fin (dropFirst T).E.s) => o.elim K (dropFirst T).divisors) (g p)) y =
      IdealSheafData.stalk (T.divisors p) y := by
    rintro (j | e)
    · by_cases hj : (j : ℕ) = 0
      · simp only [g, Sum.elim_inl, hj, dite_true, Option.elim_none]
        rw [show j = ⟨0, h0⟩ from Fin.ext hj]; exact hK.symm
      · simp only [g, Sum.elim_inl, hj, dite_false, Option.elim_some]
        change IdealSheafData.stalk (T.I _) y = IdealSheafData.stalk (T.I j) y
        congr 2; exact Fin.ext (by simp only; omega)
    · rfl
  have hmem : ∀ p, y ∈ (T.divisors p).support → y ∈ ((fun o : Option (Fin (dropFirst T).m ⊕
      Fin (dropFirst T).E.s) => o.elim K (dropFirst T).divisors) (g p)).support := by
    intro p hp
    by_contra hn
    rw [← IdealSheafData.stalk_eq_top_iff_notMem_support, hst,
      IdealSheafData.stalk_eq_top_iff_notMem_support] at hn
    exact hn hp
  refine IsSNCAt.of_injective h (fun p => ⟨g p.1, hmem p.1 p.2⟩) ?_
    fun p => (hst p.1).symm
  intro p q hpq
  exact Subtype.ext (hg (congrArg Subtype.val hpq))

/-- The supports of the ideals of the final tuple lie over the supports of the original ideals. -/
theorem support_finalTuple_subset : ∀ {S : Scheme.{u}} (B : ClosedBlowupSequence S)
    (T : OrderedDivisorTuple S) (j : Fin T.m),
    (((finalTuple B T).I ⟨j, by rw [finalTuple_m]; exact j.isLt⟩).support : Set B.target) ⊆
      B.toBase ⁻¹' ((T.I j).support : Set S) := by
  intro S B
  induction B with
  | nil S => intro T j; exact le_rfl
  | @cons X Z B ih =>
    intro T j
    refine (ih (T.transform Z) j).trans ?_
    intro y hy
    change (B.toBase ≫ blowUpToBase Z) y ∈ ((T.I j).support : Set X)
    rw [Scheme.Hom.comp_apply]
    have h1 : ((T.transform Z).I j).support ≤ ((T.I j).comap (blowUpToBase Z)).support := by
      by_cases h : (Z.support : Set X) ⊆ (T.I j).support
      · rw [OrderedDivisorTuple.transform_I_of_le _ _ _ h]
        exact Scheme.IdealSheafData.support_antitone (le_idealColon _ _)
      · rw [OrderedDivisorTuple.transform_I_of_not_le _ _ _ h]
    have h2 := h1 hy
    rwa [← SetLike.mem_coe, Scheme.IdealSheafData.support_comap] at h2

/-- **Components of a cosupport after resolving along one component.** Let `p : Y → X` be
continuous, a homeomorphism-like map over the complement of a closed set `W` (it is surjective
there, and preimages of irreducible subsets of `Wᶜ` are irreducible), `J ⊆ Wᶜ` closed, and
`A ⊆ Y` closed. A component `W''` of `A ∪ p⁻¹J` not contained in a set `P' ⊇ A` maps onto a
component `p(W'')` of `W ∪ J` other than `W`, with `p⁻¹(p(W'')) = W''`, and `p(W'')` is not
contained in any `Q` whose points off `W` have their preimages in `P'`. -/
theorem image_mem_componentsOf_of_isIrreducible_preimage {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (p : Y → X) (hp : Continuous p) {W J : Set X}
    (hW : IsClosed W) (hJ : IsClosed J) (hWJ : Disjoint W J) (hsurj : ∀ x ∉ W, x ∈ Set.range p)
    (hirr : ∀ Y' ⊆ Wᶜ, IsIrreducible Y' → IsIrreducible (p ⁻¹' Y')) {A P' : Set Y}
    {Q : Set X} (hA : IsClosed A) (hAP : A ⊆ P') (hQ : ∀ y, p y ∉ W → p y ∈ Q → y ∈ P')
    {W'' : Set Y} (hW'' : W'' ∈ componentsOf (A ∪ p ⁻¹' J)) (hbad : ¬ W'' ⊆ P') :
    p '' W'' ∈ componentsOf (W ∪ J) ∧ ¬ p '' W'' ⊆ Q ∧ p '' W'' ≠ W ∧
      p ⁻¹' (p '' W'') = W'' := by
  obtain ⟨⟨hirr'', hsub⟩, hmax⟩ := hW''
  have hJc : IsClosed (p ⁻¹' J) := hJ.preimage hp
  rcases (isPreirreducible_iff_isClosed_union_isClosed.1 hirr''.2) _ _ hA hJc hsub with h | h
  · exact absurd (h.trans hAP) hbad
  have hYJ : p '' W'' ⊆ J := Set.image_subset_iff.2 h
  have hYW : p '' W'' ⊆ Wᶜ := fun x hx => hWJ.notMem_of_mem_right (hYJ hx)
  have hYirr : IsIrreducible (p '' W'') := hirr''.image p hp.continuousOn
  have hYne : (p '' W'').Nonempty := hYirr.nonempty
  have hpre : ∀ Y', p '' W'' ⊆ Y' → Y' ⊆ J → IsIrreducible Y' → p ⁻¹' Y' = W'' := by
    intro Y' h1 h2 h3
    have hle : W'' ⊆ p ⁻¹' Y' := Set.image_subset_iff.1 h1
    refine le_antisymm (hmax ⟨hirr Y' (fun x hx => hWJ.notMem_of_mem_right (h2 hx)) h3,
      fun y hy => Or.inr (h2 hy)⟩ hle) hle
  refine ⟨⟨⟨hYirr, hYJ.trans Set.subset_union_right⟩, fun Y' ⟨hY'irr, hY'sub⟩ hle => ?_⟩, ?_, ?_,
    hpre _ le_rfl hYJ hYirr⟩
  · rcases (isPreirreducible_iff_isClosed_union_isClosed.1 hY'irr.2) _ _ hW hJ hY'sub with h' | h'
    · obtain ⟨x, hx⟩ := hYne
      exact absurd (h' (hle hx)) (hYW hx)
    · have e := hpre Y' hle h' hY'irr
      intro x hx
      obtain ⟨y, rfl⟩ := hsurj x (fun hxW => hWJ.notMem_of_mem_left hxW (h' hx))
      exact ⟨y, e ▸ hx, rfl⟩
  · exact fun hQ' => hbad fun y hy => hQ y (hYW ⟨y, hy, rfl⟩) (hQ' ⟨y, hy, rfl⟩)
  · intro he
    obtain ⟨x, hx⟩ := hYne
    exact hYW hx (he ▸ hx)

/-- Snc at a point passes to a family whose members through the point have the stalks of members
of the given family, distinct members through the point going to distinct members. -/
theorem IsSNCAt.of_forall {X : Scheme.{u}} {Λ Λ' : Type*} {D : Λ → X.IdealSheafData}
    {D' : Λ' → X.IdealSheafData} {x : X} (h : IsSNCAt D x) (f : Λ' → Λ)
    (hst : ∀ i', x ∈ (D' i').support → IdealSheafData.stalk (D' i') x =
      IdealSheafData.stalk (D (f i')) x)
    (hinj : ∀ i' j', x ∈ (D' i').support → x ∈ (D' j').support → f i' = f j' → i' = j') :
    IsSNCAt D' x := by
  have hsupp : ∀ i', x ∈ (D' i').support → x ∈ (D (f i')).support := fun i' hi => by
    by_contra hn
    rw [← IdealSheafData.stalk_eq_top_iff_notMem_support, ← hst i' hi,
      IdealSheafData.stalk_eq_top_iff_notMem_support] at hn
    exact hn hi
  refine IsSNCAt.of_injective h (fun p => ⟨f p.1, hsupp p.1 p.2⟩) ?_ fun p => hst p.1 p.2
  intro p q hpq
  exact Subtype.ext (hinj p.1 q.1 p.2 q.2 (congrArg Subtype.val hpq))

/-- Snc at a point is transported along an isomorphism. -/
theorem IsSNCAt.comap_of_isIso {X Y : Scheme.{u}} (g : Y ⟶ X) [IsIso g] {Λ : Type*}
    {D : Λ → X.IdealSheafData} {y : Y} (h : IsSNCAt D (g y)) :
    IsSNCAt (fun i => (D i).comap g) y := by
  haveI : IsIso (g.stalkMap y) := ((isIso_iff_isIso_stalkMap g).1 inferInstance).2 y
  refine IsSNCAt.of_stalkMap g y h (fun i => ⟨i.1, (mem_support_comap_iff g _ y).1 i.2⟩)
    (fun i j hij => by have h' := congrArg Subtype.val hij; exact Subtype.ext h') fun i => ?_
  rw [IdealSheafData.stalk_comap]

end MMP.Resolution.TupleResolutionAux

end
