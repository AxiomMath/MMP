/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Resolution.DisjoiningSequence
public import MMP.AlgebraicGeometry.Resolution.SNCRestriction
public import MMP.AlgebraicGeometry.Resolution.BlowupSequence.EntryIndex

/-!
# The centres of the principalization construction (Kollár, *Resolution*, 3.72 ⇒ 3.35)

Let `𝓑` be a smooth blow-up sequence functor of order `≥ 1` on the marked triples of marking `1`,
and `(X, I, E) ∈ 𝒯^snc`. The construction `𝓑𝓟_𝓑(X, I, E)` of Kollár 3.72 concatenates the
disjoining sequence `X' → X` of `(X, E)` with `𝓑(X', π^*I, 1, E_{X'})` (when this is a marked
triple) and deletes the empty blow-ups. This file proves three of the properties of 3.35 for it.

* (1) Its centres are smooth and have simple normal crossings with `E`. The disjoining part is
  `isSmooth_disjoiningSequence_and_centersHaveSNCWith`. Along `𝓑(X', π^*I, 1, E_{X'})` the
  support of the `i`-th divisor `E'_i` is the total transform of `Supp E` in the sense of
  Kollár Def. 3.25: this holds for `E_{X'}`, whose support is the total divisor `D_{k-1}`, and one
  step of the total transform of an ordered divisor replaces the support by
  `π⁻¹(Supp E'_i ∖ Z_i)‾ ∪ π⁻¹(Z_i)`, the omitted exceptional divisors `π⁻¹(W)`, for the
  components `W` of `Z_i` that are components of `Supp E'_i`, lying in the union of the others.
  Since `Z_i` has simple normal crossings with `∑_j E'^j_i`, it has simple normal crossings with
  the components of that support.
* (3″) The image in `X` of every centre lies in `cosupp I ∪ E^{(2)}`: a centre of the disjoining
  sequence lies on at least two of the transforms `E_i^{(j)}`, each over `E_i`; a centre `Z'_i`
  of `𝓑` lies in `cosupp I'_i` because `ord_{Z'_i} I'_i ≥ 1`, and the birational transform
  `I'_{i+1} ⊇ π_i^*I'_i` has cosupport over that of `I'_i`.
* (5) For `E = ∅` the disjoining sequence is empty, and the closed embedding property (3.71.2) of
  `𝓑` gives `𝓑𝓟_𝓑(X, I_X, ∅) = j_*𝓑𝓟_𝓑(Y, I_Y, ∅)`.

Deleting the empty blow-ups replaces the later centres by their inverse images along
isomorphisms; smoothness, simple normal crossings and the images of the centres are invariant
under isomorphisms.

## Main results

* `MMP.Resolution.isSmooth_principalizationConstruction_and_centersHaveSNCWith`: 3.35(1).
* `MMP.Resolution.centersLieOver_principalizationConstruction`: 3.35(3″).
* `MMP.Resolution.commutesWithClosedEmbeddings_principalizationConstruction`: 3.35(5).
* `MMP.Resolution.OrderedDivisor.support_totalTransform`: the support of the total transform of
  an ordered divisor is the total transform of its support.
* `MMP.Resolution.totalTransform_disjoiningSequence`: `Supp E_{X'}` is the total transform of
  `Supp E` under the disjoining sequence.
* `MMP.Resolution.ClosedBlowupSequence.isSmooth_and_centersHaveSNCWith_reduction`,
  `MMP.Resolution.ClosedBlowupSequence.centersLieOver_pullbackReduced`: deleting empty blow-ups.

## Implementation notes

The construction is defined on all of `𝒯^snc`, whose schemes need not be equidimensional. If `X`
is not equidimensional, `(X, I, 1, ())` is not a marked triple and `𝓑𝓟_𝓑(X, I, ∅)` is the empty
sequence. A closed embedding `Y ↪ X` of smooth schemes with exactly one of `X`, `Y`
equidimensional (a line and a point disjoint from it in the plane, inside the plane) then
compares `𝓑` on one side with the empty sequence on the other. Property (5) is therefore stated
for the closed embeddings with `E = ∅` along which `X` and `Y` are both equidimensional or both
not; this contains the closed embeddings of triples of Kollár 3.64 with `E = ∅`.

## References

* [J. Kollár, *Lectures on resolution of singularities*, 3.25, 3.35, 3.65, 3.66, 3.71, 3.72]
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Resolution

open Kollar

/-! ### Simple normal crossings along isomorphisms -/

section Transport

variable {X Y : Scheme.{u}}

/-- In the coordinates `φ(w)` at `y`, `φ = 𝒪_{X,h(y)} → 𝒪_{Y,y}`, the inverse image along `h` of
a set which is a union of coordinate hyperplanes `(w_c = 0)` at `h(y)` is the union of the
hyperplanes `(φ(w_c) = 0)`. -/
theorem preimage_fromSpecStalk_preimage (h : Y ⟶ X) (y : Y) {T : Set X} {n : ℕ}
    {w : Fin n → X.presheaf.stalk (h y)} {C : Finset (Fin n)}
    (hT : X.fromSpecStalk (h y) ⁻¹' T = ⋃ c ∈ C, PrimeSpectrum.zeroLocus {w c}) :
    Y.fromSpecStalk y ⁻¹' (h ⁻¹' T) =
      ⋃ c ∈ C, PrimeSpectrum.zeroLocus {(h.stalkMap y).hom (w c)} := by
  have h1 : Y.fromSpecStalk y ⁻¹' (h ⁻¹' T) =
      PrimeSpectrum.comap (h.stalkMap y).hom ⁻¹' (X.fromSpecStalk (h y) ⁻¹' T) := by
    ext p
    exact Iff.of_eq (congrArg (· ∈ T) (apply_fromSpecStalk h y p))
  refine h1.trans ((congrArg (fun S : Set (PrimeSpectrum (X.presheaf.stalk (h y))) =>
    PrimeSpectrum.comap (h.stalkMap y).hom ⁻¹' S) hT).trans ?_)
  simp only [Set.preimage_iUnion₂, PrimeSpectrum.preimage_comap_zeroLocus, Set.image_singleton]

/-- Being snc at a point is invariant under isomorphisms. -/
theorem IsSNCAt.preimage (ψ : Y ⟶ X) [IsIso ψ] {T : Set X} {y : Y} (h : IsSNCAt T (ψ y)) :
    IsSNCAt (ψ ⁻¹' T) y := by
  obtain ⟨n, w, C, hw, hT⟩ := h
  exact ⟨n, fun i => (ψ.stalkMap y).hom (w i), C,
    isRegularSystemOfParameters_map_ringEquiv
      (asIso (ψ.stalkMap y)).commRingCatIsoToRingEquiv hw,
    preimage_fromSpecStalk_preimage ψ y hT⟩

/-- On a Noetherian scheme a closed set is the union of its irreducible components, each with its
reduced structure. -/
theorem iUnion_support_componentsFamily [NoetherianSpace X] {T : Set X} (hT : IsClosed T) :
    ⋃ V, ((componentsFamily T V).support : Set X) = T := by
  refine subset_antisymm (Set.iUnion_subset fun V => ?_) fun x hx => ?_
  · rw [coe_support_componentsFamily hT]
    exact V.2.1.2
  · obtain ⟨V, hV, hxV⟩ := Set.mem_sUnion.1 ((Aux.finite_and_cover_componentsOf hT).2 hx)
    exact Set.mem_iUnion.2 ⟨⟨V, hV⟩, by rwa [coe_support_componentsFamily hT]⟩

/-- A divisor with simple normal crossings is snc at every point. -/
theorem IsSNCClosedSubset.isSNCAt_of_nonempty {k : Type u} [Field k] {sX : X ⟶ Spec (.of k)}
    [NoetherianSpace X] {T : Set X} (hT : IsClosed T)
    (hfam : IsSNCFamily sX (componentsFamily T)) (x : X) : IsSNCAt T x := by
  obtain ⟨n, z, c, hz, hc, -⟩ := hfam.2 x
  obtain ⟨C, hC⟩ := isSNCAt_iUnion_support (componentsFamily T) x hc
  rw [iUnion_support_componentsFamily hT] at hC
  exact ⟨n, z, C, hz, hC⟩

/-- **Divisors with simple normal crossings are invariant under isomorphisms.** -/
theorem IsSNCClosedSubset.preimage_of_isIso {k : Type u} [Field k] [PerfectField k]
    {sX : X ⟶ Spec (.of k)} [LocallyOfFiniteType sX] [QuasiCompact sX] (ψ : Y ⟶ X) [IsIso ψ]
    {T : Set X} (h : IsSNCClosedSubset sX T) : IsSNCClosedSubset (ψ ≫ sX) (ψ ⁻¹' T) := by
  obtain ⟨hT, hT0 | ⟨-, -, hfam⟩⟩ := h
  · exact ⟨hT.preimage ψ.continuous, Or.inl (by rw [hT0, Set.preimage_empty])⟩
  · have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
    have : IsNoetherian X := {}
    have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (ψ ≫ sX)
    exact isSNCClosedSubset_of_forall_isSNCAt (ψ ≫ sX) (hT.preimage ψ.continuous) fun y =>
      (IsSNCClosedSubset.isSNCAt_of_nonempty hT hfam (ψ y)).preimage ψ

/-- A centre having simple normal crossings with (the components of) a closed set `T` is, at each
of its points, a coordinate subspace in coordinates in which `T` is a union of coordinate
hyperplanes. -/
theorem HasSNCWith.exists_coordinates_componentsFamily [NoetherianSpace X] {T : Set X}
    (hT : IsClosed T) {Z : X.IdealSheafData} (hZ : HasSNCWith (componentsFamily T) Z) {x : X}
    (hx : x ∈ (Z.support : Set X)) :
    ∃ (n : ℕ) (w : Fin n → X.presheaf.stalk x) (C J : Finset (Fin n)),
      IsRegularSystemOfParameters w ∧
        X.fromSpecStalk x ⁻¹' T = ⋃ c ∈ C, PrimeSpectrum.zeroLocus {w c} ∧
        IdealSheafData.stalk Z x = Ideal.span (w '' (J : Set (Fin n))) := by
  obtain ⟨n, z, c, J, hz, hc, -, hJ⟩ := hZ x hx
  obtain ⟨C, hC⟩ := isSNCAt_iUnion_support (componentsFamily T) x hc
  rw [iUnion_support_componentsFamily hT] at hC
  exact ⟨n, z, C, J, hz, hC, hJ⟩

/-- Conversely, a centre which at each of its points is a coordinate subspace in coordinates in
which the closed set `T` is a union of coordinate hyperplanes has simple normal crossings with
the components of `T`. -/
theorem hasSNCWith_componentsFamily_of_exists_coordinates [IsLocallyNoetherian X] {T : Set X}
    (hT : IsClosed T) {Z : X.IdealSheafData}
    (h : ∀ x ∈ (Z.support : Set X), ∃ (n : ℕ) (w : Fin n → X.presheaf.stalk x)
      (C J : Finset (Fin n)), IsRegularSystemOfParameters w ∧
        X.fromSpecStalk x ⁻¹' T = ⋃ c ∈ C, PrimeSpectrum.zeroLocus {w c} ∧
        IdealSheafData.stalk Z x = Ideal.span (w '' (J : Set (Fin n)))) :
    HasSNCWith (componentsFamily T) Z := by
  intro x hx
  obtain ⟨n, z, C, J, hz, hC, hJ⟩ := h x hx
  have hmem : ∀ V : {V // x ∈ (componentsFamily T V).support}, x ∈ (V.1 : Set X) := fun V => by
    have := V.2
    rwa [← SetLike.mem_coe, coe_support_componentsFamily hT] at this
  choose c' _ hc' q hq hqc using fun V : {V // x ∈ (componentsFamily T V).support} =>
    exists_stalk_componentsFamily_eq_span hT hz hC V.1 (hmem V)
  refine ⟨n, z, c', J, hz, hc', fun V V' hVV' => ?_, hJ⟩
  have hqq : q V = q V' := PrimeSpectrum.ext ((hqc V).trans (by rw [hVV', hqc V']))
  apply Subtype.ext; apply Subtype.ext
  rw [hq V, hq V', hqq]

/-- **Having simple normal crossings with a divisor is invariant under isomorphisms.** -/
theorem HasSNCWith.componentsFamily_preimage_of_isIso [NoetherianSpace X] [IsLocallyNoetherian Y]
    (ψ : Y ⟶ X) [IsIso ψ] {T : Set X} (hT : IsClosed T) {Z : X.IdealSheafData}
    (hZ : HasSNCWith (componentsFamily T) Z) :
    HasSNCWith (componentsFamily (ψ ⁻¹' T)) (Z.comap ψ) := by
  refine hasSNCWith_componentsFamily_of_exists_coordinates (hT.preimage ψ.continuous)
    fun y hy => ?_
  rw [SetLike.mem_coe, ← SetLike.mem_coe, Scheme.IdealSheafData.support_comap] at hy
  obtain ⟨n, w, C, J, hw, hC, hJ⟩ := hZ.exists_coordinates_componentsFamily hT hy
  refine ⟨n, fun i => (ψ.stalkMap y).hom (w i), C, J,
    isRegularSystemOfParameters_map_ringEquiv
      (asIso (ψ.stalkMap y)).commRingCatIsoToRingEquiv hw,
    preimage_fromSpecStalk_preimage ψ y hC, ?_⟩
  rw [IdealSheafData.stalk_comap, hJ, Ideal.map_span, ← Set.image_comp]
  rfl

end Transport

/-! ### The support of the total transform of an ordered divisor -/

section TotalTransformSupport

variable {X : Scheme.{u}}

/-- A point lies in `Z^{≥2}` if and only if it lies in an irreducible component `W` of `Z` whose
closure has codimension `≥ 2`. -/
theorem mem_componentsOfCodimAtLeastTwo (Z : Set X) (x : X) :
    x ∈ componentsOfCodimAtLeastTwo Z ↔ ∃ W, ∃ hW : W ∈ componentsOf Z,
      2 ≤ codimension (irreducibleClosure hW.1.1) ∧ x ∈ W := by
  simp only [componentsOfCodimAtLeastTwo, Set.mem_iUnion]
  exact ⟨fun ⟨W, hW, h2, hx⟩ => ⟨W, hW, h2, hx⟩, fun ⟨W, hW, h2, hx⟩ => ⟨W, hW, h2, hx⟩⟩

/-- An irreducible component of the support of an ordered divisor whose entries are of pure
codimension one has codimension one; in particular it is not of codimension `≥ 2`. -/
theorem OrderedDivisor.not_two_le_codimension_of_mem_componentsOf (E : OrderedDivisor X)
    (hE : ∀ i, IsPureCodimOne (E.E i).support) {W : Set X} (hW : W ∈ componentsOf E.support) :
    ¬ 2 ≤ codimension (irreducibleClosure hW.1.1) := by
  classical
  have hEc : IsClosed E.support := isClosed_iUnion_of_finite fun i => (E.E i).support.isClosed
  have hWc : IsClosed W := Aux.isClosed_of_mem_componentsOf hEc hW
  obtain ⟨_, hz, hWz⟩ := isIrreducible_iff_sUnion_isClosed.mp hW.1.1
    (Finset.univ.image fun i => ((E.E i).support : Set X))
    (fun z hz => by
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hz
      exact (E.E i).support.isClosed)
    (by
      intro x hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hW.1.2 hx)
      exact Set.mem_sUnion.2 ⟨_, Finset.mem_coe.2 (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩),
        hi⟩)
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hz
  let W₀ : IrreducibleCloseds X := ⟨W, hW.1.1, hWc⟩
  have hmax : Maximal (fun W' : IrreducibleCloseds X => (W' : Set X) ⊆ (E.E i).support) W₀ :=
    ⟨hWz, fun V hV hWV => hW.2 ⟨V.isIrreducible,
      hV.trans (Set.subset_iUnion (fun i => ((E.E i).support : Set X)) i)⟩ hWV⟩
  have he : irreducibleClosure hW.1.1 = W₀ := by
    ext1
    exact hWc.closure_eq
  rw [he, hE i W₀ hmax]
  decide

/-- The support of the `i`-th entry of the total transform `π⁻¹_tot(E)` is the closure of the
`i`-th set `totalTransformSet E Z i`. -/
theorem support_entry_totalTransform (E : OrderedDivisor X) (Z : X.IdealSheafData)
    (i : Fin (E.s + 1)) :
    (((E.totalTransform Z).E i).support : Set (blowUp Z)) = closure (totalTransformSet E Z i) := by
  rw [totalTransform_E_eq, Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_closure]

/-- The support of the total transform of an ordered divisor is contained in its total
transform as a set. -/
theorem OrderedDivisor.support_totalTransform_subset (E : OrderedDivisor X)
    (Z : X.IdealSheafData) :
    (E.totalTransform Z).support ⊆ ClosedBlowupSequence.totalTransformStep Z E.support := by
  classical
  refine Set.iUnion_subset fun (i : Fin (E.s + 1)) => ?_
  rw [support_entry_totalTransform]
  refine closure_minimal ?_ (isClosed_closure.union
    ((Z.support.isClosed).preimage (blowUpToBase Z).continuous))
  induction i using Fin.lastCases with
  | last =>
    rw [totalTransformSet, Fin.snoc_last]
    intro x hx
    obtain ⟨W, hW, hx⟩ := Set.mem_iUnion₂.1 hx
    obtain ⟨-, hx⟩ := Set.mem_iUnion.1 hx
    exact Or.inr (hW.1.2 hx)
  | cast j =>
    rw [totalTransformSet, Fin.snoc_castSucc]
    rintro x ⟨hxE, -⟩
    by_cases hxZ : blowUpToBase Z x ∈ (Z.support : Set X)
    · exact Or.inr hxZ
    · exact Or.inl (subset_closure ⟨Set.mem_iUnion.2 ⟨j, hxE⟩, hxZ⟩)

/-- **The support of the total transform of an ordered divisor is its total transform as a
set**: if the entries of `E` are of pure codimension one, then
`Supp π⁻¹_tot(E) = π⁻¹(Supp E ∖ Z)‾ ∪ π⁻¹(Z)`. The entries `π⁻¹(Z_j)` omitted from `π⁻¹_tot(E)`,
for the components `Z_j` of `Z` that are components of `Supp E`, lie in the union of the
others. -/
theorem OrderedDivisor.support_totalTransform (E : OrderedDivisor X)
    (hE : ∀ i, IsPureCodimOne (E.E i).support) (Z : X.IdealSheafData) :
    (E.totalTransform Z).support = ClosedBlowupSequence.totalTransformStep Z E.support := by
  classical
  set π := blowUpToBase Z
  have hlast : ∀ x : blowUp Z, ∀ W ∈ componentsOf (Z.support : Set X), W ∉ componentsOf E.support →
      π x ∈ W → x ∈ (E.totalTransform Z).support := fun x W hW hWE hx => by
    refine Set.mem_iUnion.2 ⟨Fin.last _, ?_⟩
    rw [support_entry_totalTransform]
    refine subset_closure ?_
    rw [totalTransformSet, Fin.snoc_last]
    exact Set.mem_iUnion₂.2 ⟨W, hW, Set.mem_iUnion.2 ⟨hWE, hx⟩⟩
  have hcast : ∀ x : blowUp Z, ∀ j, π x ∈ (E.E j).support →
      π x ∉ componentsOfCodimAtLeastTwo (Z.support : Set X) →
      x ∈ (E.totalTransform Z).support := fun x j hj hA => by
    refine Set.mem_iUnion.2 ⟨Fin.castSucc j, ?_⟩
    rw [support_entry_totalTransform]
    refine subset_closure ?_
    rw [totalTransformSet, Fin.snoc_castSucc]
    exact ⟨hj, hA⟩
  have hA : componentsOfCodimAtLeastTwo (Z.support : Set X) ⊆ Z.support := by
    intro x hx
    obtain ⟨W, hW, -, hxW⟩ := (mem_componentsOfCodimAtLeastTwo _ _).1 hx
    exact hW.1.2 hxW
  refine subset_antisymm (E.support_totalTransform_subset Z) ?_
  rintro x (hx | hx)
  · refine closure_minimal (fun y hy => ?_) (isClosed_iUnion_of_finite fun i =>
      ((E.totalTransform Z).E i).support.isClosed) hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hy.1
    exact hcast y j hj fun h => hy.2 (hA h)
  · by_cases hxA : π x ∈ componentsOfCodimAtLeastTwo (Z.support : Set X)
    · obtain ⟨W, hW, h2, hxW⟩ := (mem_componentsOfCodimAtLeastTwo _ _).1 hxA
      exact hlast x W hW (fun hWE => E.not_two_le_codimension_of_mem_componentsOf hE hWE h2)
        hxW
    · obtain ⟨W, hW, hxW⟩ := exists_mem_componentsOf (D := (Z.support : Set X)) (x := π x) hx
      by_cases hWE : W ∈ componentsOf E.support
      · obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (hWE.1.2 hxW)
        exact hcast x j hj hxA
      · exact hlast x W hW hWE hxW

end TotalTransformSupport

/-! ### The divisor at the end of the disjoining sequence -/

namespace DisjoiningStage

variable {k : ℕ}

/-- The support of the ordered divisor at the end of `n` disjoining steps from stage `j` is the
total transform of the total divisor `D_j`. -/
theorem totalTransform_sequence (n : ℕ) : ∀ {j : ℕ} (st : DisjoiningStage.{u} k j),
    (st.sequence n).totalTransform (⋃ i, ((Sum.elim st.Es st.Fs i).support : Set st.X)) =
      (st.divisor n).support := by
  induction n with
  | zero =>
    intro j st
    change (⋃ i, ((Sum.elim st.Es st.Fs i).support : Set st.X)) =
      ⋃ i, ((Fin.cons (α := fun _ => st.X.IdealSheafData) st.unionEs st.Fs i).support : Set st.X)
    rw [Set.iUnion_sum]
    ext x
    simp only [Set.mem_union, Set.mem_iUnion, Sum.elim_inl, Sum.elim_inr]
    constructor
    · rintro (⟨i, hi⟩ | ⟨l, hl⟩)
      · refine ⟨0, ?_⟩
        rw [Fin.cons_zero, coe_support_unionEs]
        exact Set.mem_iUnion.2 ⟨i, hi⟩
      · exact ⟨l.succ, by rwa [Fin.cons_succ]⟩
    · rintro ⟨i, hi⟩
      induction i using Fin.cases with
      | zero =>
        rw [Fin.cons_zero, coe_support_unionEs] at hi
        exact Or.inl (Set.mem_iUnion.1 hi)
      | succ l =>
        rw [Fin.cons_succ] at hi
        exact Or.inr ⟨l, hi⟩
  | succ n ih =>
    intro j st
    change (st.step.sequence n).totalTransform (ClosedBlowupSequence.totalTransformStep st.center
      (⋃ i, ((Sum.elim st.Es st.Fs i).support : Set st.X))) = (st.step.divisor n).support
    rw [← st.iUnion_support_step]
    exact ih st.step

end DisjoiningStage

/-- The total divisor `D_0` of the disjoining construction is `E`, as a set. -/
theorem iUnion_support_disjoiningStart {X : Scheme.{u}} (E : OrderedDivisor X) :
    ⋃ i, ((Sum.elim (disjoiningStart E).Es (disjoiningStart E).Fs i).support :
      Set (disjoiningStart E).X) = E.support := by
  rw [Set.iUnion_sum]
  ext x
  constructor
  · rintro (h | h)
    · exact h
    · obtain ⟨l, -⟩ := Set.mem_iUnion.1 h
      exact l.elim0
  · exact Or.inl

/-- **The support of `E_{X'}` is the total transform of `E` under the disjoining sequence**
(Kollár 3.72): `Supp E_{X'} = D_{k-1}`, the total transform of `Supp E` in the sense of
Def. 3.25. -/
theorem totalTransform_disjoiningSequence {X : Scheme.{u}} (E : OrderedDivisor X) :
    (disjoiningSequence X E).totalTransform E.support = (disjoiningDivisor X E).support := by
  obtain ⟨s, E⟩ := E
  match s, E with
  | 0, E =>
    ext x
    exact ⟨fun h => (Set.mem_iUnion.1 h).choose.elim0,
      fun h => (Set.mem_iUnion.1 h).choose.elim0⟩
  | 1, E => rfl
  | k + 2, E =>
    have h := (disjoiningStart (X := X) ⟨k + 2, E⟩).totalTransform_sequence (k + 1)
    rwa [iUnion_support_disjoiningStart] at h

namespace ClosedBlowupSequence

variable {k : Type u} [Field k]

/-! ### Concatenation -/

/-- The concatenation of a smooth blow-up sequence `D` of `X` with a smooth blow-up sequence of
its end `X_r` is smooth. -/
theorem isSmooth_append {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) (D : ClosedBlowupSequence X)
    (C : ClosedBlowupSequence D.target) (hD : D.IsSmooth s) (hC : C.IsSmooth (D.toBase ≫ s)) :
    (D.append C).IsSmooth s := by
  induction D with
  | nil X =>
    change C.IsSmooth (𝟙 X ≫ s) at hC
    rwa [Category.id_comp] at hC
  | cons Z D ih =>
    refine ⟨hD.1, hD.2.1, ih _ C hD.2.2 ?_⟩
    change C.IsSmooth ((D.toBase ≫ blowUpToBase Z) ≫ s) at hC
    rwa [Category.assoc] at hC

/-- If the centres of `D` have simple normal crossings with `E` and those of a blow-up sequence
`C` of the end of `D` have simple normal crossings with the total transform of `E` under `D`, then
the centres of the concatenation `D.append C` have simple normal crossings with `E`. -/
theorem centersHaveSNCWith_append {X : Scheme.{u}} (s : X ⟶ Spec (.of k))
    (D : ClosedBlowupSequence X) (C : ClosedBlowupSequence D.target) (E : Set X)
    (hD : D.CentersHaveSNCWith s E)
    (hC : C.CentersHaveSNCWith (D.toBase ≫ s) (D.totalTransform E)) :
    (D.append C).CentersHaveSNCWith s E := by
  induction D with
  | nil X =>
    change C.CentersHaveSNCWith (𝟙 X ≫ s) E at hC
    rwa [Category.id_comp] at hC
  | cons Z D ih =>
    refine ⟨hD.1, hD.2.1, ih _ C _ hD.2.2 ?_⟩
    change C.CentersHaveSNCWith ((D.toBase ≫ blowUpToBase Z) ≫ s) _ at hC
    rwa [Category.assoc] at hC

/-- If the centres of `D` and those of a blow-up sequence `C` of the end of `D` lie over
`S ⊆ X₀`, then so do the centres of the concatenation `D.append C`. -/
theorem centersLieOver_append {X X₀ : Scheme.{u}} (f : X ⟶ X₀) (S : Set X₀)
    (D : ClosedBlowupSequence X) (C : ClosedBlowupSequence D.target)
    (hD : D.CentersLieOver f S) (hC : C.CentersLieOver (D.toBase ≫ f) S) :
    (D.append C).CentersLieOver f S := by
  induction D with
  | nil X =>
    exact (congrArg (fun g => C.CentersLieOver g S) (Category.id_comp f)).mp hC
  | cons Z D ih =>
    refine ⟨hD.1, ih _ C hD.2 ?_⟩
    exact (congrArg (fun g => C.CentersLieOver g S)
      (Category.assoc D.toBase (blowUpToBase Z) f)).mp hC

/-! ### Deleting empty blow-ups -/

/-- If the centres of `B` lie over `S ⊆ X₀` along `f : X → X₀`, then the centres of the
pull-back `h^*B` with its empty blow-ups deleted lie over `S` along `h ≫ f`. -/
theorem centersLieOver_pullbackReduced {X X₀ Y : Scheme.{u}} (B : ClosedBlowupSequence X)
    (f : X ⟶ X₀) (S : Set X₀) (h : Y ⟶ X) (hB : B.CentersLieOver f S) :
    (B.pullbackReduced h).CentersLieOver (h ≫ f) S := by
  induction B generalizing Y with
  | nil X => trivial
  | cons Z B ih =>
    by_cases hZ : Z.comap h = ⊤
    · simp only [pullbackReduced, hZ, dite_true]
      have := ih (blowUpToBase Z ≫ f) (blowUpLift Z h (isCartierOver_of_comap_eq_top h Z hZ))
        hB.2
      rwa [← Category.assoc, blowUpLift_comp] at this
    · simp only [pullbackReduced, hZ, dite_false]
      refine ⟨?_, ?_⟩
      · rintro _ ⟨y, hy, rfl⟩
        rw [Scheme.IdealSheafData.support_comap] at hy
        exact hB.1 ⟨h y, hy, rfl⟩
      · have := ih (blowUpToBase Z ≫ f) (canonicalLift h Z) hB.2
        rwa [← Category.assoc, canonicalLift_comp_blowUpToBase, Category.assoc] at this

/-- If `X` is smooth over `k` and `ψ : Y → X` is an isomorphism, then `Y` is smooth over `k`. -/
theorem _root_.MMP.Resolution.isSmoothScheme_iso_comp {X Y : Scheme.{u}} (ψ : Y ⟶ X) [IsIso ψ]
    {s : X ⟶ Spec (.of k)} [LocallyOfFiniteType s] (hs : IsSmoothScheme s) :
    IsSmoothScheme (ψ ≫ s) := by
  have : LocallyOfFinitePresentation s :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := s)).mpr inferInstance
  have : LocallyOfFinitePresentation (ψ ≫ s) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := ψ ≫ s)).mpr inferInstance
  rw [isSmoothScheme_iff] at hs ⊢
  infer_instance

/-- If the closed subscheme `Z ⊆ X` is smooth over `k` and `ψ : Y → X` is an isomorphism, then the
closed subscheme `ψ⁻¹Z ⊆ Y` is smooth over `k`. -/
theorem _root_.MMP.Resolution.isSmoothScheme_comap_subschemeι {X Y : Scheme.{u}} (ψ : Y ⟶ X)
    [IsIso ψ] (Z : X.IdealSheafData) {s : X ⟶ Spec (.of k)} [LocallyOfFiniteType s]
    (hs : IsSmoothScheme (Z.subschemeι ≫ s)) :
    IsSmoothScheme ((Z.comap ψ).subschemeι ≫ ψ ≫ s) := by
  have e : (Z.comap ψ).subschemeι ≫ ψ ≫ s =
      ((Z.comapIso ψ).hom ≫ Limits.pullback.snd ψ Z.subschemeι) ≫ Z.subschemeι ≫ s := by
    rw [← Z.comapIso_hom_fst ψ, Category.assoc, Category.assoc, ← Category.assoc _ ψ,
      Limits.pullback.condition, Category.assoc]
  rw [e]
  exact isSmoothScheme_iso_comp _ hs

/-- If `B` is a smooth blow-up sequence of `X` over `k` and `ψ : Y → X` is an isomorphism, then the
pull-back `ψ^*B` with its empty blow-ups deleted is a smooth blow-up sequence of `Y` over `k`. -/
theorem isSmooth_pullbackReduced {X Y : Scheme.{u}} (B : ClosedBlowupSequence X)
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s] (ψ : Y ⟶ X) [IsIso ψ] (hB : B.IsSmooth s) :
    (B.pullbackReduced ψ).IsSmooth (ψ ≫ s) := by
  induction B generalizing Y with
  | nil X => trivial
  | cons Z B ih =>
    have : IsLocallyNoetherian _ := LocallyOfFiniteType.isLocallyNoetherian s
    by_cases hZ : Z.comap ψ = ⊤
    · simp only [pullbackReduced, hZ, dite_true]
      have := isIso_blowUpLift_of_eq_top ((comap_eq_top_iff_of_isIso ψ Z).1 hZ) ψ
        (isCartierOver_of_comap_eq_top ψ Z hZ)
      have h := ih (blowUpToBase Z ≫ s) (blowUpLift Z ψ (isCartierOver_of_comap_eq_top ψ Z hZ))
        hB.2.2
      rwa [← Category.assoc, blowUpLift_comp] at h
    · simp only [pullbackReduced, hZ, dite_false]
      have := isIso_canonicalLift ψ Z
      refine ⟨isSmoothScheme_iso_comp ψ hB.1, isSmoothScheme_comap_subschemeι ψ Z hB.2.1, ?_⟩
      have h := ih (blowUpToBase Z ≫ s) (canonicalLift ψ Z) hB.2.2
      rwa [← Category.assoc, canonicalLift_comp_blowUpToBase, Category.assoc] at h

/-- The total transform commutes with an isomorphism of the base. -/
theorem totalTransformStep_comap_of_isIso {X Y : Scheme.{u}} (ψ : Y ⟶ X) [IsIso ψ]
    (Z : X.IdealSheafData) (E : Set X) :
    totalTransformStep (Z.comap ψ) (ψ ⁻¹' E) = canonicalLift ψ Z ⁻¹' totalTransformStep Z E := by
  have := isIso_canonicalLift ψ Z
  have hc : ∀ A : Set X, blowUpToBase (Z.comap ψ) ⁻¹' (ψ ⁻¹' A) =
      canonicalLift ψ Z ⁻¹' (blowUpToBase Z ⁻¹' A) := fun A => by
    ext x
    simp only [Set.mem_preimage]
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, canonicalLift_comp_blowUpToBase]
  have hs : ((Z.comap ψ).support : Set Y) = ψ ⁻¹' (Z.support : Set X) := by
    rw [Scheme.IdealSheafData.support_comap]
    rfl
  unfold totalTransformStep
  rw [hs, ← Set.preimage_sdiff, hc, hc, Set.preimage_union,
    (canonicalLift ψ Z).isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
      (canonicalLift ψ Z).continuous]

/-- The total transform of a closed set under the blow-up of the empty subscheme is its inverse
image. -/
theorem totalTransformStep_top {X : Scheme.{u}} {E : Set X} (hE : IsClosed E) :
    totalTransformStep (⊤ : X.IdealSheafData) E = blowUpToBase ⊤ ⁻¹' E := by
  unfold totalTransformStep
  rw [Scheme.IdealSheafData.support_top]
  simp only [TopologicalSpace.Closeds.coe_bot, Set.sdiff_empty, Set.preimage_empty,
    Set.union_empty]
  exact (hE.preimage (blowUpToBase _).continuous).closure_eq

/-- Deleting the empty blow-ups after an isomorphism keeps the centres having simple normal
crossings with (the transform of) a divisor. -/
theorem centersHaveSNCWith_pullbackReduced [PerfectField k] {X Y : Scheme.{u}}
    (B : ClosedBlowupSequence X) (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s] [QuasiCompact s]
    (ψ : Y ⟶ X) [IsIso ψ] (E : Set X) (hB : B.CentersHaveSNCWith s E) :
    (B.pullbackReduced ψ).CentersHaveSNCWith (ψ ≫ s) (ψ ⁻¹' E) := by
  induction B generalizing Y with
  | nil X => trivial
  | @cons X Z B ih =>
    have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
    have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
    have : IsNoetherian X := {}
    have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (ψ ≫ s)
    obtain ⟨hE, hZ, hB⟩ := hB
    have hEc : IsClosed E := hE.1
    by_cases hZ' : Z.comap ψ = ⊤
    · simp only [pullbackReduced, hZ', dite_true]
      have hZt := (comap_eq_top_iff_of_isIso ψ Z).1 hZ'
      have := isIso_blowUpLift_of_eq_top hZt ψ (isCartierOver_of_comap_eq_top ψ Z hZ')
      have h := ih (blowUpToBase Z ≫ s) (blowUpLift Z ψ (isCartierOver_of_comap_eq_top ψ Z hZ'))
        _ hB
      have e1 : blowUpLift Z ψ (isCartierOver_of_comap_eq_top ψ Z hZ') ≫ blowUpToBase Z ≫ s =
          ψ ≫ s := by
        rw [← Category.assoc, blowUpLift_comp]
      have e2 : blowUpLift Z ψ (isCartierOver_of_comap_eq_top ψ Z hZ') ⁻¹'
          totalTransformStep Z E = ψ ⁻¹' E := by
        subst hZt
        rw [totalTransformStep_top hEc]
        ext x
        simp only [Set.mem_preimage]
        rw [← Scheme.Hom.comp_apply, blowUpLift_comp]
      rwa [e1, e2] at h
    · simp only [pullbackReduced, hZ', dite_false]
      have := isIso_canonicalLift ψ Z
      refine ⟨hE.preimage_of_isIso ψ, hZ.componentsFamily_preimage_of_isIso ψ hEc, ?_⟩
      have h := ih (blowUpToBase Z ≫ s) (canonicalLift ψ Z) _ hB
      rwa [← Category.assoc, canonicalLift_comp_blowUpToBase, Category.assoc,
        ← totalTransformStep_comap_of_isIso] at h

/-- **A smooth blow-up sequence of order `≥ m` starting with a marked triple is a smooth blow-up
sequence whose centres have simple normal crossings with the divisor of the triple** (Kollár
Def. 3.25, 3.66): along the sequence, the support of `E_i` is the total transform of `Supp E` in
the sense of Def. 3.25, and `Z_i` has snc with `∑_j E_i^j`, hence with the components of that
support. -/
theorem IsOrderGeMarkedTripleSeq.isSmooth_and_centersHaveSNCWith {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) (a : MarkedIdeal X) (E : OrderedDivisor X)
    (C : ClosedBlowupSequence X) (hC : C.IsOrderGeMarkedTripleSeq s a E) :
    C.IsSmooth s ∧ C.CentersHaveSNCWith s E.support := by
  induction C with
  | nil X => exact ⟨trivial, trivial⟩
  | @cons X Z C ih =>
    obtain ⟨htr, hZsm, -, hZ, -, hC⟩ := hC
    obtain ⟨hchar, hsm, hlft, hqc, -, -, -, hsnc⟩ := htr
    have : CharZero k := hchar
    have : LocallyOfFiniteType s := hlft
    have : QuasiCompact s := hqc
    have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
    have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
    obtain ⟨ih1, ih2⟩ := ih (blowUpToBase Z ≫ s) _ _ hC
    refine ⟨⟨hsm, hZsm, ih1⟩, IsSNCFamily.isSNCClosedSubset_iUnion hsnc,
      hZ.componentsFamily_iUnion, ?_⟩
    rwa [← OrderedDivisor.support_totalTransform E (fun i => (hsnc.1 i).2.1) Z]

end ClosedBlowupSequence

open ClosedBlowupSequence

/-- Deleting the empty blow-ups keeps a smooth blow-up sequence smooth and its centres having
simple normal crossings with a divisor. -/
theorem ClosedBlowupSequence.isSmooth_and_centersHaveSNCWith_reduction {k : Type u} [Field k]
    [PerfectField k] {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    [QuasiCompact s] (B : ClosedBlowupSequence X) (E : Set X)
    (hB : B.IsSmooth s ∧ B.CentersHaveSNCWith s E) :
    B.reduction.IsSmooth s ∧ B.reduction.CentersHaveSNCWith s E := by
  have h1 := B.isSmooth_pullbackReduced s (𝟙 X) hB.1
  have h2 := B.centersHaveSNCWith_pullbackReduced s (𝟙 X) E hB.2
  rw [Category.id_comp] at h1 h2
  exact ⟨h1, h2⟩

/-- **Kollár 3.72 ⇒ 3.35(1): the centres of `𝓑𝓟_𝓑(X, I, E)` are smooth and have simple normal
crossings with `E`.** Let `𝓑` be a smooth blow-up sequence functor of order `≥ 1` on the marked
triples of marking `1`, and `(X, I, E) ∈ 𝒯^snc`. Then `𝓑𝓟_𝓑(X, I, E)` is a smooth blow-up sequence
(every `X_i` and every centre is smooth) and its centres have simple normal crossings with `E`
(Kollár Def. 3.25). -/
@[mmp "lem_kr3c_bp_construction_centers_snc"]
theorem isSmooth_principalizationConstruction_and_centersHaveSNCWith
    (B : OrderGeBlowupSequenceFunctor.{u} (markedTriplesOfMarking 1))
    (t : FieldBlowupTriple.{u}) (ht : t ∈ sncTriples) :
    (principalizationConstruction B.toFun t ht).IsSmooth t.sX ∧
      (principalizationConstruction B.toFun t ht).CentersHaveSNCWith t.sX t.E.support := by
  obtain ⟨hchar, -, hlft, hqc, -, -, hsnc⟩ := ht
  have : CharZero t.k := hchar
  have : LocallyOfFiniteType t.sX := hlft
  have : QuasiCompact t.sX := hqc
  have hD := isSmooth_disjoiningSequence_and_centersHaveSNCWith t.sX t.E hsnc
  unfold principalizationConstruction
  dsimp only
  split_ifs with h
  · have hC := IsOrderGeMarkedTripleSeq.isSmooth_and_centersHaveSNCWith _ _ _ _
      (B.isOrderGeMarkedTripleSeq _ h)
    refine isSmooth_and_centersHaveSNCWith_reduction t.sX _ _
      ⟨isSmooth_append t.sX _ _ hD.1 hC.1, centersHaveSNCWith_append t.sX _ _ _ hD.2 ?_⟩
    rw [totalTransform_disjoiningSequence]
    exact hC.2
  · exact isSmooth_and_centersHaveSNCWith_reduction t.sX _ _ hD

/-! ### Where the centres lie -/

/-- `CentersLieOver` is monotone in the set. -/
theorem ClosedBlowupSequence.CentersLieOver.mono {X X₀ : Scheme.{u}} {B : ClosedBlowupSequence X}
    {f : X ⟶ X₀} {S S' : Set X₀} (h : B.CentersLieOver f S) (hS : S ⊆ S') :
    B.CentersLieOver f S' := by
  induction B with
  | nil X => trivial
  | cons Z B ih => exact ⟨h.1.trans hS, ih h.2⟩

/-- A point at which an ideal sheaf has order `≥ 1` lies on its cosupport. -/
theorem mem_support_of_one_le_multAt {X : Scheme.{u}} (I : X.IdealSheafData) {x : X}
    (h : 1 ≤ multAt I x) : x ∈ (I.support : Set X) := by
  by_contra hx
  have htop : IdealSheafData.stalk I x = ⊤ :=
    (IdealSheafData.stalk_eq_top_iff_notMem_support I x).2 hx
  have h0 : multAt I x ≤ 0 := by
    unfold multAt idealOrder
    rw [htop]
    refine iSup₂_le fun j hj => ?_
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact le_rfl
    · exact absurd (top_le_iff.1 (hj.trans (Ideal.pow_le_self hj0.ne')))
        (IsLocalRing.maximalIdeal.isMaximal _).ne_top
  exact absurd (h.trans h0) (by decide)

/-- A closed subset along which an ideal sheaf has order `≥ 1` lies in its cosupport. -/
theorem subset_support_of_orderAlongGE {X : Scheme.{u}} {I : X.IdealSheafData} {Z : Set X}
    {m : ℕ∞} (hm : 1 ≤ m) (h : OrderAlongGE I Z m) : Z ⊆ I.support := by
  intro z hz
  obtain ⟨W, hW, hzW⟩ := exists_mem_componentsOf hz
  have hη := mem_support_of_one_le_multAt I (hm.trans (h W hW))
  have hgen := hW.1.1.isGenericPoint_genericPoint_closure
  exact subset_closure.trans (hgen.symm ▸ closure_minimal
    (Set.singleton_subset_iff.2 hη) I.support.isClosed) hzW

/-- The cosupport of the birational transform of a marked ideal lies over the cosupport of the
ideal. -/
theorem MarkedIdeal.support_birationalTransform_subset {X : Scheme.{u}} (Z : X.IdealSheafData)
    (a : MarkedIdeal X) :
    ((a.birationalTransform Z).I.support : Set (blowUp Z)) ⊆
      blowUpToBase Z ⁻¹' (a.I.support : Set X) := by
  have h := Scheme.IdealSheafData.support_antitone (le_idealColon (a.I.comap (blowUpToBase Z))
    (Z.comap (blowUpToBase Z) ^ a.m))
  intro x hx
  have := h hx
  rwa [Scheme.IdealSheafData.support_comap] at this

/-- **The centres of a smooth blow-up sequence of order `≥ m ≥ 1` lie over the cosupport of the
ideal** (Kollár 3.72): `Z_i ⊆ cosupp I_i` since `ord_{Z_i} I_i ≥ 1`, and the cosupport of `I_{i+1}`
lies over that of `I_i`. -/
theorem ClosedBlowupSequence.IsOrderGeMarkedTripleSeq.centersLieOver {k : Type u} [Field k]
    {X X₀ : Scheme.{u}} (s : X ⟶ Spec (.of k)) (a : MarkedIdeal X) (E : OrderedDivisor X)
    (C : ClosedBlowupSequence X) (hC : C.IsOrderGeMarkedTripleSeq s a E) (hm : 1 ≤ a.m)
    (g : X ⟶ X₀) (S : Set X₀) (hg : g '' (a.I.support : Set X) ⊆ S) :
    C.CentersLieOver g S := by
  induction C generalizing X₀ with
  | nil X => trivial
  | @cons X Z C ih =>
    obtain ⟨-, -, -, -, hord, hC⟩ := hC
    refine ⟨(Set.image_mono (subset_support_of_orderAlongGE (by exact_mod_cast hm) hord)).trans
      hg, ih (blowUpToBase Z ≫ s) _ _ hC hm _ S ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hg ⟨blowUpToBase Z x, MarkedIdeal.support_birationalTransform_subset Z a hx, rfl⟩

namespace DisjoiningStage

variable {k : ℕ}

/-- The centres of the disjoining sequence lie over the double locus: a point of `Z_j` lies on
`k - j ≥ 2` of the `E_i^{(j)}`, each lying over `E_i`. -/
theorem centersLieOver_sequence {X : Scheme.{u}} (E : Fin k → X.IdealSheafData) (n : ℕ) :
    ∀ {j : ℕ} (st : DisjoiningStage.{u} k j) (f : st.X ⟶ X),
      (∀ i, f '' ((st.Es i).support : Set st.X) ⊆ (E i).support) → j + n + 1 ≤ k →
      (st.sequence n).CentersLieOver f
        {x | ∃ i i', i ≠ i' ∧ x ∈ ((E i).support : Set X) ∧ x ∈ ((E i').support : Set X)} := by
  induction n with
  | zero => intro j st f _ _; trivial
  | succ n ih =>
    intro j st f hf hn
    refine ⟨?_, ih st.step (blowUpToBase st.center ≫ f) (fun i => ?_) (by omega)⟩
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨S, hS, hxS⟩ := (st.mem_support_center_iff x).1 hx
      obtain ⟨i, hi, i', hi', hii'⟩ := Finset.one_lt_card.1 (by omega : 1 < S.card)
      exact ⟨i, i', hii', hf i ⟨x, hxS i hi, rfl⟩, hf i' ⟨x, hxS i' hi', rfl⟩⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact hf i ⟨blowUpToBase st.center x, st.support_transform_subset (st.Es i) hx, rfl⟩

end DisjoiningStage

/-- **The centres of the disjoining sequence lie over the double locus `E^{(2)}`** (Kollár
3.72). -/
theorem centersLieOver_disjoiningSequence {X : Scheme.{u}} (E : OrderedDivisor X) :
    (disjoiningSequence X E).CentersLieOver (𝟙 X) E.doubleLocus := by
  obtain ⟨s, E⟩ := E
  match s, E with
  | 0, E => trivial
  | 1, E => trivial
  | k + 2, E =>
    exact (disjoiningStart (X := X) ⟨k + 2, E⟩).centersLieOver_sequence E (k + 1) (𝟙 X)
      (fun i => by rintro _ ⟨x, hx, rfl⟩; exact hx) (by omega)

/-- **What the construction of Kollár 3.72 gives for 3.35(3): the centres lie over
`cosupp I ∪ E^{(2)}`.** Let `𝓑` be a smooth blow-up sequence functor of order `≥ 1` on the marked
triples of marking `1`, and `(X, I, E) ∈ 𝒯^snc`. Then the image in `X` of every centre of
`𝓑𝓟_𝓑(X, I, E)` lies in `cosupp I ∪ E^{(2)}`. -/
@[mmp "lem_kr3c_bp_construction_centers_over_cosupport"]
theorem centersLieOver_principalizationConstruction
    (B : OrderGeBlowupSequenceFunctor.{u} (markedTriplesOfMarking 1))
    (t : FieldBlowupTriple.{u}) (ht : t ∈ sncTriples) :
    (principalizationConstruction B.toFun t ht).CentersLieOver (𝟙 t.X)
      ((t.I.support : Set t.X) ∪ t.E.doubleLocus) := by
  have hred : ∀ D : ClosedBlowupSequence t.X,
      D.CentersLieOver (𝟙 t.X) ((t.I.support : Set t.X) ∪ t.E.doubleLocus) →
      D.reduction.CentersLieOver (𝟙 t.X) ((t.I.support : Set t.X) ∪ t.E.doubleLocus) :=
    fun D hD => by
      have := D.centersLieOver_pullbackReduced _ _ (𝟙 t.X) hD
      rwa [Category.id_comp] at this
  have hD : (disjoiningSequence t.X t.E).CentersLieOver (𝟙 t.X)
      ((t.I.support : Set t.X) ∪ t.E.doubleLocus) :=
    (centersLieOver_disjoiningSequence t.E).mono Set.subset_union_right
  unfold principalizationConstruction
  dsimp only
  split_ifs with h
  · refine hred _ (centersLieOver_append _ _ _ _ hD ?_)
    refine IsOrderGeMarkedTripleSeq.centersLieOver _ _ _ _ (B.isOrderGeMarkedTripleSeq _ h)
      le_rfl _ _ ?_
    rintro _ ⟨x, hx, rfl⟩
    change x ∈ ((t.I.comap (disjoiningSequence t.X t.E).toBase).support : Set _) at hx
    rw [Scheme.IdealSheafData.support_comap] at hx
    rw [Category.comp_id]
    exact Or.inl hx
  · exact hred _ hD

/-! ### Closed embeddings -/

/-- A blow-up sequence functor takes equal values on equal triples. -/
theorem BlowupSequenceFunctor.heq_of_eq {T : Type*} {toTriple : T → BlowupTriple.{u}}
    {𝒞 : Set T} (B : BlowupSequenceFunctor toTriple 𝒞) {t₁ t₂ : T} (e : t₁ = t₂) (h₁ : t₁ ∈ 𝒞)
    (h₂ : t₂ ∈ 𝒞) : B t₁ h₁ ≍ B t₂ h₂ := by
  subst e
  rfl

/-- A triple of `𝒯^snc` with marking `1` is a marked triple exactly when its scheme is
equidimensional. -/
theorem mk_mem_markedTriplesOfMarking_one_iff {t : FieldBlowupTriple.{u}} (ht : t ∈ sncTriples) :
    (⟨t, 1⟩ : MarkedTriple.{u}) ∈ markedTriplesOfMarking 1 ↔ Equidimensional t.X := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := ht
  exact ⟨fun h => h.1.2.2.2.2.1, fun h => ⟨⟨h1, h2, h3, h4, h, h5, h6, h7⟩, rfl⟩⟩

open Classical in
/-- For `E = ∅` the disjoining sequence is empty, and `𝓑𝓟_𝓑(X, I, ∅)` is `𝓑(X, I, 1, ())` if
`(X, I, 1, ())` is a marked triple and the empty sequence otherwise. -/
theorem principalizationConstruction_of_s_eq_zero
    (B : OrderGeBlowupSequenceFunctor.{u} (markedTriplesOfMarking 1))
    (t : FieldBlowupTriple.{u}) (ht : t ∈ sncTriples) (h0 : t.E.s = 0) :
    principalizationConstruction B.toFun t ht =
      if h : (⟨t, 1⟩ : MarkedTriple.{u}) ∈ markedTriplesOfMarking 1 then B.toFun ⟨t, 1⟩ h
      else .nil t.X := by
  obtain ⟨⟨X, I, ⟨s, E⟩⟩, k, sX⟩ := t
  change s = 0 at h0
  subst h0
  have e : (⟨⟨⟨(disjoiningSequence X ⟨0, E⟩).target,
      I.comap (disjoiningSequence X ⟨0, E⟩).toBase, disjoiningDivisor X ⟨0, E⟩⟩, k,
      (disjoiningSequence X ⟨0, E⟩).toBase ≫ sX⟩, 1⟩ : MarkedTriple.{u}) =
      ⟨⟨⟨X, I, ⟨0, E⟩⟩, k, sX⟩, 1⟩ := by
    have hE : E = Fin.elim0 := funext fun i => i.elim0
    subst hE
    change (⟨⟨⟨X, I.comap (𝟙 X), OrderedDivisor.empty X⟩, k, 𝟙 X ≫ sX⟩, 1⟩ : MarkedTriple.{u}) = _
    rw [Scheme.IdealSheafData.comap_id, Category.id_comp]
    rfl
  unfold principalizationConstruction
  dsimp only
  split_ifs with h₁ h₂ h₂
  · exact (reduction_eq_self (B.hasNoEmptyBlowups _ h₁)).trans
      (eq_of_heq (B.toFun.heq_of_eq e h₁ h₂))
  · exact absurd (e ▸ h₁) h₂
  · exact absurd (e.symm ▸ h₂) h₁
  · rfl

/-- **Kollár 3.72 ⇒ 3.35(5): `𝓑𝓟_𝓑` commutes with closed embeddings for `E = ∅`**, from the closed
embedding property (3.71.2) of `𝓑`. Let `𝓑` be a smooth blow-up sequence functor of order `≥ 1` on
the marked triples of marking `1` with the closed embedding property of (3.71.2). Then for every
closed embedding `j : Y ↪ X` with ideal sheaves `I_Y`, `I_X = ker(𝒪_X → j_*(𝒪_Y/I_Y))`, `E = ∅`,
`(X, I_X, ∅), (Y, I_Y, ∅) ∈ 𝒯^snc`, and `X`, `Y` both equidimensional or both not,
`𝓑𝓟_𝓑(X, I_X, ∅) = j_*𝓑𝓟_𝓑(Y, I_Y, ∅)`. -/
@[mmp "lem_kr3c_bp_construction_closed_embeddings"]
theorem commutesWithClosedEmbeddings_principalizationConstruction
    (B : OrderGeBlowupSequenceFunctor.{u} (markedTriplesOfMarking 1))
    (hB : HasClosedEmbeddingProperty B.toFun) :
    (principalizationConstruction B.toFun).CommutesWithClosedEmbeddings
      {d | d.E.s = 0 ∧ (Equidimensional d.X ↔ Equidimensional d.Y)} := by
  rintro d ⟨hd, hXY⟩ hX hY
  rw [principalizationConstruction_of_s_eq_zero B _ hX hd,
    principalizationConstruction_of_s_eq_zero B _ hY hd]
  by_cases hXe : Equidimensional d.X
  · rw [dite_eq_left ((mk_mem_markedTriplesOfMarking_one_iff hX).2 hXe),
      dite_eq_left ((mk_mem_markedTriplesOfMarking_one_iff hY).2 (hXY.1 hXe))]
    exact hB d hd _ _
  · rw [dite_eq_right (fun h => hXe ((mk_mem_markedTriplesOfMarking_one_iff hX).1 h)),
      dite_eq_right (fun h => hXe (hXY.2 ((mk_mem_markedTriplesOfMarking_one_iff hY).1 h)))]
    trivial

end MMP.Resolution
