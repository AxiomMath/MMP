/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Resolution.BirationalTransformTriple
public import MMP.AlgebraicGeometry.Resolution.DisjoiningCenter
public import MMP.AlgebraicGeometry.Resolution.TotalTransformSNC
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityRamificationLocus.Generizations
public import StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.KeyLemma
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.LocalizationSequence
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.BlowUpResidueField

/-!
# The disjoining sequence (Kollár, *Resolution*, 3.72)

Let `X` be a scheme of finite type over a field `K` of characteristic `0` and `E = (E_1, …, E_k)`
an ordered divisor whose sum is a simple normal crossing divisor. The disjoining sequence of
`(X, E)` blows up, for `j = 0, …, k - 2`, the reduced centre `Z_j ⊆ X_j` of the points lying on at
least `k - j` of the transforms `E_i^{(j)}`; write `D_j = ∑_i E_i^{(j)} + ∑_{l ≤ j} F^{l,(j)}` for
the total divisor on `X_j`.

The induction runs on two conditions: (a) `D_j` is a simple normal crossing divisor, and (b) no
point of `X_j` lies on `k - j + 1` of the `E_i^{(j)}`. Under (a) and (b) the centre `Z_j` has
simple normal crossings with `D_j`, and one blow-up removes the `(k - j)`-fold intersections, which
is (b) for `j + 1`. Condition (a) for `j + 1` is the general fact that blowing up a centre having
simple normal crossings with an snc divisor `D = ∑_λ D_λ` gives the snc divisor formed by the
transforms `π⁻¹(D_λ ∖ Z)‾` and the exceptional divisor `π⁻¹(Z)`: at a point over `Z`, in the
coordinates `w` of a chart of the blow-up, the transform of `(z_c = 0)` is `(w_{σ(c)} = 0)` or
misses the point, and the exceptional divisor is `(w_{i₀} = 0)`. Two distinct transforms never
share a coordinate hyperplane: the generic point of `(w_t = 0)` has a local ring of dimension one
and lies off the centre, where the blow-up is a local isomorphism and two members of `D` through a
point force a local ring of dimension at least two.

As a set, `D_{j+1}` is the total transform `π_j⁻¹(D_j ∖ Z_j)‾ ∪ π_j⁻¹(Z_j)` of `D_j`, so the
centres of the disjoining sequence have simple normal crossings with `E` in the sense of
Kollár Def. 3.25. At the end, `j = k - 1`, the `E_i^{(k-1)}` are pairwise disjoint, so their
union `E^0` is, near each point, one of them, and `(E^0, F^1, …, F^{k-1})` is an ordered snc
divisor. No generic point of an irreducible component of `X_{j+1}` lies on the exceptional
divisor, so each component of `X_{j+1}` is birational to one of `X_j`, of the same dimension, and
a pulled-back ideal stays nonzero at the generic points.

## Main definitions

* `MMP.Resolution.blowUpTransformFamily`: the transforms `π⁻¹(D_λ ∖ Z)‾` of the members of a
  family together with the exceptional divisor `π⁻¹(Z)`.
* `MMP.Resolution.DisjoiningStage.iterateToBase`, `MMP.Resolution.disjoiningToBase`: the
  composite `X_j → X` of the first `j` disjoining blow-ups.

## Main results

* `MMP.Resolution.isSNCFamily_blowUpTransformFamily`: blowing up a centre having snc with an snc
  divisor gives an snc divisor.
* `MMP.Resolution.isSNCFamily_disjoiningTotalDivisor_and_exists_notMem`: the invariant (a), (b)
  of the disjoining sequence for `0 ≤ j ≤ k - 1`.
* `MMP.Resolution.isSmooth_disjoiningSequence_and_centersHaveSNCWith`: the disjoining sequence is
  a smooth blow-up sequence whose centres have snc with `E`.
* `MMP.Resolution.isTriple_disjoiningSequence`: `(X', π^*I, E_{X'})` is a triple.

## Implementation notes

The base field is only assumed perfect where characteristic `0` is not needed (the invariant and
the centres); a triple asks characteristic `0`. The schemes are assumed quasi-compact, as schemes
of finite type over a field are; this is used to find, for a point of the closure of
`π⁻¹(D_λ ∖ Z)`, a generization in `π⁻¹(D_λ ∖ Z)` itself. The invariant is stated for all
`j < k`, without the source's standing assumption `k ≥ 2`. The smoothness of `X_{j+1}` is read off
(a) for `j + 1` (a regular system of parameters at every point) rather than from the smoothness of
blow-ups along smooth centres.

## References

* [J. Kollár, *Lectures on resolution of singularities*, 3.25, 3.64, 3.72]
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Resolution

/-! ### Preliminaries -/

section Prelim

/-- In a Noetherian quasi-sober space, every point of the closure of a locally closed set
`S = C ∩ O` is a specialization of a point of `S`. -/
theorem exists_mem_specializes_of_mem_closure {α : Type*} [TopologicalSpace α]
    [NoetherianSpace α] [QuasiSober α] {C O : Set α} (hC : IsClosed C) (hO : IsOpen O) {y : α}
    (hy : y ∈ closure (C ∩ O)) : ∃ s ∈ C ∩ O, s ⤳ y := by
  classical
  obtain ⟨F, hF, hFeq⟩ := NoetherianSpace.exists_finset_irreducible (Closeds.closure (C ∩ O))
  have hcov : closure (C ∩ O) = ⋃ V ∈ F, (V : Set α) := by
    have := congrArg (fun T : Closeds α => (T : Set α)) hFeq
    simpa [Closeds.coe_finset_sup] using this
  set F' := F.filter fun V : Closeds α => ((V : Set α) ∩ (C ∩ O)).Nonempty
  have hsub : closure (C ∩ O) ⊆ ⋃ V ∈ F', (V : Set α) := by
    refine closure_minimal (fun s hs => ?_) ?_
    · have : s ∈ ⋃ V ∈ F, (V : Set α) := hcov ▸ subset_closure hs
      obtain ⟨V, hV, hsV⟩ := Set.mem_iUnion₂.1 this
      exact Set.mem_iUnion₂.2 ⟨V, Finset.mem_filter.2 ⟨hV, s, hsV, hs⟩, hsV⟩
    · exact isClosed_biUnion_finset fun V _ => V.isClosed
  obtain ⟨V, hV, hyV⟩ := Set.mem_iUnion₂.1 (hsub hy)
  obtain ⟨hVF, t, htV, htS⟩ := Finset.mem_filter.1 hV
  have hirr : IsIrreducible (V : Set α) := hF ⟨V, hVF⟩
  have hgen := hirr.isGenericPoint_genericPoint_closure
  rw [V.isClosed.closure_eq] at hgen
  refine ⟨hirr.genericPoint, ⟨?_, ?_⟩, ?_⟩
  · have hVC : (V : Set α) ⊆ C := by
      intro v hv
      have : v ∈ ⋃ V ∈ F, (V : Set α) := Set.mem_iUnion₂.2 ⟨V, hVF, hv⟩
      rw [← hcov] at this
      exact closure_minimal Set.inter_subset_left hC this
    exact hVC hgen.mem
  · exact (hgen.mem_open_set_iff hO).2 ⟨t, htV, htS.2⟩
  · exact hgen.specializes hyV

end Prelim

section Parameters

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- The ideal generated by a member of a regular system of parameters is the vanishing ideal of
its zero locus. -/
theorem _root_.MMP.Mori.IsRegularSystemOfParameters.vanishingIdeal_zeroLocus_singleton {m : ℕ}
    {w : Fin m → R} (hw : IsRegularSystemOfParameters w) (j : Fin m) :
    PrimeSpectrum.vanishingIdeal (PrimeSpectrum.zeroLocus {w j}) = Ideal.span {w j} := by
  have := span_singleton_isPrime_of_isRegularSystemOfParameters hw j
  rw [← PrimeSpectrum.zeroLocus_span, PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical,
    Ideal.IsPrime.radical this]

/-- The ideal generated by a member of a regular system of parameters has height at most one. -/
theorem _root_.MMP.Mori.IsRegularSystemOfParameters.height_span_singleton_le_one {m : ℕ}
    {w : Fin m → R} (hw : IsRegularSystemOfParameters w) (j : Fin m) :
    (Ideal.span {w j}).height ≤ 1 :=
  Ideal.height_span_singleton_le_one fun h =>
    (span_singleton_isPrime_of_isRegularSystemOfParameters hw j).ne_top
      (Ideal.span_singleton_eq_top.2 h)

end Parameters

section Stalks

variable {Y : Scheme.{u}}

/-- The stalk at `y` of the reduced ideal sheaf of a closed set `T` is the vanishing ideal of the
inverse image of `T` in `Spec 𝒪_{Y,y}`. -/
theorem stalk_vanishingIdeal_eq (T : Closeds Y) (y : Y) :
    IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal T) y =
      PrimeSpectrum.vanishingIdeal (Y.fromSpecStalk y ⁻¹' (T : Set Y)) := by
  set V := Scheme.IdealSheafData.vanishingIdeal T
  have hV : V.support = T :=
    SetLike.coe_injective (by rw [Scheme.IdealSheafData.coe_support_vanishingIdeal])
  have h1 : V.radical = V := by
    rw [← Scheme.IdealSheafData.vanishingIdeal_support, hV]
  calc IdealSheafData.stalk V y = IdealSheafData.stalk V.radical y := by rw [h1]
    _ = (IdealSheafData.stalk V y).radical := stalk_radical V y
    _ = PrimeSpectrum.vanishingIdeal (PrimeSpectrum.zeroLocus (IdealSheafData.stalk V y)) :=
        (PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical _).symm
    _ = _ := by
      rw [← preimage_fromSpecStalk_support, hV]
      rfl

end Stalks

section SNC

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}

/-- An snc family stays an snc family along an injective reindexing. -/
theorem IsSNCFamily.comp {Λ Λ' : Type*} {E : Λ → X.IdealSheafData} (hE : IsSNCFamily sX E)
    (e : Λ' → Λ) (he : Function.Injective e) : IsSNCFamily sX (E ∘ e) := by
  refine ⟨fun i => hE.1 (e i), fun x => ?_⟩
  obtain ⟨n, z, c, hz, hc, hinj⟩ := hE.2 x
  refine ⟨n, z, fun i => c ⟨e i.1, i.2⟩, hz, fun i => hc ⟨e i.1, i.2⟩, fun i i' h => ?_⟩
  exact Subtype.ext (he (congrArg Subtype.val (hinj h)))

end SNC

/-! ### From an snc family to the snc divisor of its union -/

section Union

variable {Y : Scheme.{u}}

/-- In coordinates in which every `D_λ ∋ y` is `(z_{c(λ)} = 0)`, the inverse image of `⋃_λ D_λ`
in `Spec 𝒪_{Y,y}` is the union of the coordinate hyperplanes `(z_{c(λ)} = 0)`. -/
theorem preimage_fromSpecStalk_iUnion_support {Λ : Type*} (D : Λ → Y.IdealSheafData) (y : Y)
    {n : ℕ} (z : Fin n → Y.presheaf.stalk y) (c : {i // y ∈ (D i).support} → Fin n)
    (hc : ∀ i, IdealSheafData.stalk (D i.1) y = Ideal.span {z (c i)}) :
    Y.fromSpecStalk y ⁻¹' (⋃ i, ((D i).support : Set Y)) =
      ⋃ i, PrimeSpectrum.zeroLocus {z (c i)} := by
  ext p
  constructor
  · intro hp
    obtain ⟨i, hp⟩ := Set.mem_iUnion.1 (Set.mem_preimage.1 hp)
    have hy : y ∈ (D i).support :=
      (Scheme.range_fromSpecStalk.subset ⟨p, rfl⟩ : Y.fromSpecStalk y p ⤳ y).mem_closed
        (D i).support.isClosed hp
    have := (fromSpecStalk_mem_support_iff_stalk_le (D i) y p).1 hp
    rw [hc ⟨i, hy⟩, Ideal.span_singleton_le_iff_mem] at this
    exact Set.mem_iUnion.2 ⟨⟨i, hy⟩,
      (PrimeSpectrum.mem_zeroLocus _ _).2 (Set.singleton_subset_iff.2 this)⟩
  · intro hp
    obtain ⟨i, hp⟩ := Set.mem_iUnion.1 hp
    replace hp : z (c i) ∈ p.asIdeal :=
      (PrimeSpectrum.mem_zeroLocus _ _).1 hp (Set.mem_singleton _)
    refine Set.mem_preimage.2 (Set.mem_iUnion.2 ⟨i.1, ?_⟩)
    refine (fromSpecStalk_mem_support_iff_stalk_le (D i.1) y p).2 ?_
    rwa [hc i, Ideal.span_singleton_le_iff_mem]

/-- In coordinates `z` in which every `D_λ ∋ y` is `(z_{c(λ)} = 0)`, the inverse image of
`⋃_λ D_λ` in `Spec 𝒪_{Y,y}` is the union of the hyperplanes `(z_t = 0)` over some finite set `C`
of indices. -/
theorem isSNCAt_iUnion_support {Λ : Type*} (D : Λ → Y.IdealSheafData) (y : Y)
    {n : ℕ} {z : Fin n → Y.presheaf.stalk y} {c : {i // y ∈ (D i).support} → Fin n}
    (hc : ∀ i, IdealSheafData.stalk (D i.1) y = Ideal.span {z (c i)}) :
    ∃ C : Finset (Fin n), Y.fromSpecStalk y ⁻¹' (⋃ i, ((D i).support : Set Y)) =
      ⋃ t ∈ C, PrimeSpectrum.zeroLocus {z t} := by
  classical
  refine ⟨Finset.univ.filter (· ∈ Set.range c), ?_⟩
  rw [preimage_fromSpecStalk_iUnion_support D y z c hc]
  ext p
  simp only [Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_range,
    exists_prop]
  constructor
  · rintro ⟨i, hp⟩; exact ⟨c i, ⟨i, rfl⟩, hp⟩
  · rintro ⟨_, ⟨i, rfl⟩, hp⟩; exact ⟨i, hp⟩

/-- At a point `y` where the closed set `T` is snc with coordinates `w` and indices `C`, the
stalk at `y` of the ideal of an irreducible component `V ∋ y` of `T` is `(w_c)` for some
`c ∈ C`, the prime of `𝒪_{Y,y}` corresponding to the generic point of `V`. -/
theorem exists_stalk_componentsFamily_eq_span [IsLocallyNoetherian Y] {T : Set Y}
    (hT : IsClosed T) {y : Y} {n : ℕ}
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

/-- The ideal of an irreducible component of a closed set `T` cuts out that component. -/
theorem coe_support_componentsFamily {T : Set Y} (hT : IsClosed T) (V : componentsOf T) :
    ((componentsFamily T V).support : Set Y) = (V : Set Y) := by
  unfold componentsFamily
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_closure,
    (Aux.isClosed_of_mem_componentsOf hT V.2).closure_eq]

/-- **An snc family gives an snc divisor.** On a quasi-compact scheme locally of finite type over
a perfect field, the union of the members of a finite simple normal crossing family is a divisor
with simple normal crossings. -/
theorem IsSNCFamily.isSNCClosedSubset_iUnion {k : Type u} [Field k] [PerfectField k]
    {sY : Y ⟶ Spec (.of k)} [LocallyOfFiniteType sY] [CompactSpace Y] {Λ : Type*} [Finite Λ]
    {D : Λ → Y.IdealSheafData} (hD : IsSNCFamily sY D) :
    IsSNCClosedSubset sY (⋃ i, ((D i).support : Set Y)) := by
  refine isSNCClosedSubset_of_forall_isSNCAt sY (isClosed_iUnion_of_finite fun i =>
    (D i).support.isClosed) fun y => ?_
  obtain ⟨n, z, c, hz, hc, -⟩ := hD.2 y
  obtain ⟨C, hC⟩ := isSNCAt_iUnion_support D y hc
  exact ⟨n, z, C, hz, hC⟩

/-- **A centre having snc with an snc family has snc with the components of its union.** -/
theorem HasSNCWith.componentsFamily_iUnion [IsLocallyNoetherian Y] {Λ : Type*} [Finite Λ]
    {D : Λ → Y.IdealSheafData} {Z : Y.IdealSheafData} (hZ : HasSNCWith D Z) :
    HasSNCWith (componentsFamily (⋃ i, ((D i).support : Set Y))) Z := by
  classical
  set T := ⋃ i, ((D i).support : Set Y)
  have hT : IsClosed T := isClosed_iUnion_of_finite fun i => (D i).support.isClosed
  intro x hx
  obtain ⟨n, z, c, J, hz, hc, -, hJ⟩ := hZ x hx
  obtain ⟨C, hC⟩ := isSNCAt_iUnion_support D x hc
  have hmem : ∀ V : {V // x ∈ (componentsFamily T V).support}, x ∈ (V.1 : Set Y) := fun V => by
    have := V.2
    rwa [← SetLike.mem_coe, coe_support_componentsFamily hT] at this
  choose c' _ hc' q hq hqc using fun V : {V // x ∈ (componentsFamily T V).support} =>
    exists_stalk_componentsFamily_eq_span hT hz hC V.1 (hmem V)
  refine ⟨n, z, c', J, hz, hc', fun V V' hVV' => ?_, hJ⟩
  have hqq : q V = q V' := PrimeSpectrum.ext ((hqc V).trans (by rw [hVV', hqc V']))
  apply Subtype.ext; apply Subtype.ext
  rw [hq V, hq V', hqq]

end Union

/-! ### One blow-up of a centre having snc with an snc family -/

section Transform

variable {Y : Scheme.{u}}

/-- The family on `B_ZY` of the reduced closures `π⁻¹(D_λ ∖ Z)‾` of the inverse images of the
`D_λ ∖ Z`, together with the exceptional divisor `π⁻¹(Z)`, `π : B_ZY → Y` the blow-up. -/
def blowUpTransformFamily {Λ : Type*} (D : Λ → Y.IdealSheafData) (Z : Y.IdealSheafData) :
    Λ ⊕ Unit → (blowUp Z).IdealSheafData :=
  Sum.elim (fun l => Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
    (blowUpToBase Z ⁻¹' (((D l).support : Set Y) \ (Z.support : Set Y)))))
    fun _ => Z.comap (blowUpToBase Z)

/-- The member of `blowUpTransformFamily D Z` indexed by `Sum.inl l` has support the closure
`π⁻¹(D_l ∖ Z)‾`. -/
theorem coe_support_blowUpTransformFamily_inl {Λ : Type*} (D : Λ → Y.IdealSheafData)
    (Z : Y.IdealSheafData) (l : Λ) :
    ((blowUpTransformFamily D Z (Sum.inl l)).support : Set (blowUp Z)) =
      closure (blowUpToBase Z ⁻¹' (((D l).support : Set Y) \ (Z.support : Set Y))) := by
  rw [blowUpTransformFamily, Sum.elim_inl, Scheme.IdealSheafData.coe_support_vanishingIdeal,
    Closeds.coe_closure]

/-- The member of `blowUpTransformFamily D Z` indexed by `Sum.inr u` has support the exceptional
locus `π⁻¹(Z)`. -/
theorem coe_support_blowUpTransformFamily_inr {Λ : Type*} (D : Λ → Y.IdealSheafData)
    (Z : Y.IdealSheafData) (u : Unit) :
    ((blowUpTransformFamily D Z (Sum.inr u)).support : Set (blowUp Z)) =
      blowUpToBase Z ⁻¹' (Z.support : Set Y) := by
  change ((Z.comap (blowUpToBase Z)).support : Set (blowUp Z)) = _
  rw [Scheme.IdealSheafData.support_comap]
  rfl

/-- As a set, the union of the family of the transforms and the exceptional divisor is the total
transform `π⁻¹(D ∖ Z)‾ ∪ π⁻¹(Z)` of `D = ⋃_λ D_λ`. -/
theorem iUnion_support_blowUpTransformFamily {Λ : Type*} [Finite Λ]
    (D : Λ → Y.IdealSheafData) (Z : Y.IdealSheafData) :
    ⋃ i, ((blowUpTransformFamily D Z i).support : Set (blowUp Z)) =
      ClosedBlowupSequence.totalTransformStep Z (⋃ l, ((D l).support : Set Y)) := by
  rw [Set.iUnion_sum]
  simp only [coe_support_blowUpTransformFamily_inl, coe_support_blowUpTransformFamily_inr,
    Set.iUnion_const]
  unfold ClosedBlowupSequence.totalTransformStep
  rw [Set.iUnion_sdiff, Set.preimage_iUnion, closure_iUnion_of_finite]

/-- A point of `Spec 𝒪_{X,x}` lies over a closed set `I` of `Y` cut out at `π x` by `g` exactly
when its prime contains the image of `g` under `π^# : 𝒪_{Y,π x} → 𝒪_{X,x}`. -/
theorem fromSpecStalk_mem_support_iff_stalkMap_mem {X : Scheme.{u}} (π : X ⟶ Y) (x : X)
    (I : Y.IdealSheafData) {g : Y.presheaf.stalk (π x)}
    (hg : IdealSheafData.stalk I (π x) = Ideal.span {g}) (p : PrimeSpectrum (X.presheaf.stalk x)) :
    π (X.fromSpecStalk x p) ∈ I.support ↔ (π.stalkMap x).hom g ∈ p.asIdeal := by
  have key : X.fromSpecStalk x ⁻¹' (π ⁻¹' (I.support : Set Y)) =
      PrimeSpectrum.comap (π.stalkMap x).hom ⁻¹' (Y.fromSpecStalk (π x) ⁻¹' I.support) := by
    refine Set.ext fun q => ?_
    change π (X.fromSpecStalk x q) ∈ (I.support : Set Y) ↔
      Y.fromSpecStalk (π x) (PrimeSpectrum.comap (π.stalkMap x).hom q) ∈ (I.support : Set Y)
    rw [← Scheme.Hom.comp_apply, ← Scheme.SpecMap_stalkMap_fromSpecStalk π (x := x)]
    rfl
  change π (X.fromSpecStalk x p) ∈ (I.support : Set Y) ↔ _
  refine (Set.ext_iff.1 key p).trans ?_
  change Y.fromSpecStalk (π x) (PrimeSpectrum.comap (π.stalkMap x).hom p) ∈
    (I.support : Set Y) ↔ _
  rw [fromSpecStalk_mem_support_iff_stalk_le, hg, Ideal.span_singleton_le_iff_mem]
  rfl

/-- A point of `Spec 𝒪_{X,x}` lying in the closure of `π⁻¹(S ∖ Z)` is a specialization of a
point of `Spec 𝒪_{X,x}` lying in `π⁻¹(S ∖ Z)` itself. -/
theorem exists_le_fromSpecStalk_mem_of_mem_closure {X : Scheme.{u}} [NoetherianSpace X]
    (π : X ⟶ Y) {x : X} {S Z : Set Y} (hS : IsClosed S) (hZ : IsClosed Z)
    {p : PrimeSpectrum (X.presheaf.stalk x)}
    (hp : X.fromSpecStalk x p ∈ closure (π ⁻¹' (S \ Z))) :
    ∃ q : PrimeSpectrum (X.presheaf.stalk x), q.asIdeal ≤ p.asIdeal ∧
      X.fromSpecStalk x q ∈ π ⁻¹' (S \ Z) := by
  have hp' : X.fromSpecStalk x p ∈ closure (π ⁻¹' S ∩ (π ⁻¹' Z)ᶜ) := by
    rwa [← Set.preimage_compl, ← Set.preimage_inter, ← Set.sdiff_eq]
  obtain ⟨s, hs, hsp⟩ := exists_mem_specializes_of_mem_closure (hS.preimage π.continuous)
    (hZ.preimage π.continuous).isOpen_compl hp'
  obtain ⟨q, rfl⟩ : s ∈ Set.range (X.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]
    exact hsp.trans (Scheme.range_fromSpecStalk.subset ⟨p, rfl⟩)
  exact ⟨q, (PrimeSpectrum.le_iff_specializes q p).2
    ((X.fromSpecStalk x).isEmbedding.isInducing.specializes_iff.1 hsp), hs⟩

/-- If `P` is the least prime of `𝒪_{X,x}` whose point lies in `π⁻¹(S ∖ Z)`, then a point of
`Spec 𝒪_{X,x}` lies in the closure of `π⁻¹(S ∖ Z)` exactly when its prime contains `P`. -/
theorem fromSpecStalk_mem_closure_iff_of_forall {X : Scheme.{u}} [NoetherianSpace X]
    (π : X ⟶ Y) {x : X} {S Z : Set Y} (hS : IsClosed S) (hZ : IsClosed Z)
    {P : PrimeSpectrum (X.presheaf.stalk x)} (hP : X.fromSpecStalk x P ∈ π ⁻¹' (S \ Z))
    (hle : ∀ q : PrimeSpectrum (X.presheaf.stalk x), X.fromSpecStalk x q ∈ π ⁻¹' (S \ Z) →
      P.asIdeal ≤ q.asIdeal) (p : PrimeSpectrum (X.presheaf.stalk x)) :
    X.fromSpecStalk x p ∈ closure (π ⁻¹' (S \ Z)) ↔ P.asIdeal ≤ p.asIdeal := by
  refine ⟨fun hp => ?_, fun hp => ?_⟩
  · obtain ⟨q, hqp, hq⟩ := exists_le_fromSpecStalk_mem_of_mem_closure π hS hZ hp
    exact (hle q hq).trans hqp
  · exact (((PrimeSpectrum.le_iff_specializes P p).1 hp).map
      (X.fromSpecStalk x).continuous).mem_closed isClosed_closure (subset_closure hP)

/-- Two members of an snc family meet only at points whose local ring has dimension at least
two. -/
theorem IsSNCFamily.eq_of_ringKrullDim_le_one {k : Type u} [Field k] {sY : Y ⟶ Spec (.of k)}
    {Λ : Type*} {D : Λ → Y.IdealSheafData} (hD : IsSNCFamily sY D) {y : Y}
    (hy : ringKrullDim (Y.presheaf.stalk y) ≤ 1) {a b : Λ} (ha : y ∈ (D a).support)
    (hb : y ∈ (D b).support) : a = b := by
  obtain ⟨n, z, c, hz, -, hinj⟩ := hD.2 y
  rw [hz.2] at hy
  have hn : n ≤ 1 := by exact_mod_cast hy
  have := (c ⟨a, ha⟩).2
  have := (c ⟨b, hb⟩).2
  exact congrArg Subtype.val (@hinj ⟨a, ha⟩ ⟨b, hb⟩ (Fin.ext (by omega)))

/-- The chart relations of `exists_chart_coordinates` send the ideal `(z_j : j ∈ J)` of the
centre to the ideal `(w_{i₀})` of the exceptional divisor. -/
theorem map_span_image_eq_span_of_chart {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
    {n N : ℕ} {z : Fin n → A} {w : Fin N → B} {J U : Finset (Fin n)} {m : Fin n} {i₀ : Fin N}
    {σ : Fin n → Fin N} (hmJ : m ∈ J) (hwi₀ : w i₀ = φ (z m))
    (hin : ∀ j ∈ J, j ≠ m → j ∉ U → φ (z j) = w (σ j) * w i₀)
    (hunit : ∀ j ∈ U, ∃ u, IsUnit u ∧ φ (z j) = u * w i₀) :
    Ideal.map φ (Ideal.span (z '' J)) = Ideal.span {w i₀} := by
  rw [Ideal.map_span]
  refine le_antisymm (Ideal.span_le.2 ?_) ?_
  · rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    change φ (z j) ∈ Ideal.span {w i₀}
    by_cases hjm : j = m
    · rw [hjm, ← hwi₀]
      exact Ideal.subset_span rfl
    by_cases hjU : j ∈ U
    · obtain ⟨v, -, hv⟩ := hunit j hjU
      rw [hv]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
    · rw [hin j hj hjm hjU]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  · rw [Ideal.span_singleton_le_iff_mem, hwi₀]
    exact Ideal.subset_span ⟨z m, ⟨m, hmJ, rfl⟩, rfl⟩

/-- By the chart relations of `exists_chart_coordinates`, `w_{σ(j)} ∈ P` gives `φ(z_j) ∈ P` for
`j ∉ U ∪ {m}`. -/
theorem map_mem_of_chart {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) {n N : ℕ}
    {z : Fin n → A} {w : Fin N → B} {J U : Finset (Fin n)} {m : Fin n} {i₀ : Fin N}
    {σ : Fin n → Fin N} (hout : ∀ j ∉ J, w (σ j) = φ (z j))
    (hin : ∀ j ∈ J, j ≠ m → j ∉ U → φ (z j) = w (σ j) * w i₀) {P : Ideal B} {j : Fin n}
    (hjm : j ≠ m) (hjU : j ∉ U) (h : w (σ j) ∈ P) : φ (z j) ∈ P := by
  by_cases hjJ : j ∈ J
  · rw [hin j hjJ hjm hjU]
    exact Ideal.mul_mem_right _ _ h
  · rwa [← hout j hjJ]

/-- Off the exceptional divisor `(w_{i₀} = 0)`, by the chart relations of
`exists_chart_coordinates`, `φ(z_j) ∈ P` forces `j ∉ U ∪ {m}` and `w_{σ(j)} ∈ P`. -/
theorem ne_and_mem_of_chart {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) {n N : ℕ}
    {z : Fin n → A} {w : Fin N → B} {J U : Finset (Fin n)} {m : Fin n} {i₀ : Fin N}
    {σ : Fin n → Fin N} (hwi₀ : w i₀ = φ (z m)) (hout : ∀ j ∉ J, w (σ j) = φ (z j))
    (hin : ∀ j ∈ J, j ≠ m → j ∉ U → φ (z j) = w (σ j) * w i₀)
    (hunit : ∀ j ∈ U, ∃ u, IsUnit u ∧ φ (z j) = u * w i₀) {P : Ideal B} (hP : P.IsPrime)
    (h0 : w i₀ ∉ P) {j : Fin n} (h : φ (z j) ∈ P) : (j ≠ m ∧ j ∉ U) ∧ w (σ j) ∈ P := by
  have hgood : j ≠ m ∧ j ∉ U := by
    refine ⟨fun hjm => h0 (by subst hjm; rwa [hwi₀]), fun hjU => ?_⟩
    obtain ⟨u, hu, hu'⟩ := hunit j hjU
    rw [hu'] at h
    exact h0 ((hP.mem_or_mem h).resolve_left fun h' =>
      hP.ne_top (Ideal.eq_top_of_isUnit_mem _ h' hu))
  refine ⟨hgood, ?_⟩
  by_cases hjJ : j ∈ J
  · rw [hin j hjJ hgood.1 hgood.2] at h
    exact (hP.mem_or_mem h).resolve_right h0
  · rwa [hout j hjJ]

/-- A point of the transform `π⁻¹(D_l ∖ Z)‾` lies over `D_l`. -/
theorem mem_support_of_mem_blowUpTransformFamily_inl {Λ : Type*} {D : Λ → Y.IdealSheafData}
    {Z : Y.IdealSheafData} {l : Λ} {x' : blowUp Z}
    (h : x' ∈ (blowUpTransformFamily D Z (Sum.inl l)).support) :
    blowUpToBase Z x' ∈ (D l).support := by
  rw [← SetLike.mem_coe, coe_support_blowUpTransformFamily_inl] at h
  exact closure_minimal (fun _ h => h.1)
    ((D l).support.isClosed.preimage (blowUpToBase Z).continuous) h

/-- A point off the centre does not lie on the exceptional divisor. -/
theorem notMem_support_blowUpTransformFamily_inr {Λ : Type*} (D : Λ → Y.IdealSheafData)
    {Z : Y.IdealSheafData} {x' : blowUp Z} (hx : blowUpToBase Z x' ∉ Z.support) (u : Unit) :
    x' ∉ (blowUpTransformFamily D Z (Sum.inr u)).support := by
  rw [← SetLike.mem_coe, coe_support_blowUpTransformFamily_inr]
  exact hx

/-- Two transforms through the generic point of `(w_t = 0)`, which lies off the centre, are the
same member of the family: the blow-up is a local isomorphism there, and the local ring there has
dimension at most one. -/
theorem IsSNCFamily.eq_of_mem_preimage_sdiff {k : Type u} [Field k] {sY : Y ⟶ Spec (.of k)}
    {Λ : Type*} {D : Λ → Y.IdealSheafData} (hD : IsSNCFamily sY D) (Z : Y.IdealSheafData)
    {x' : blowUp Z} {P : PrimeSpectrum ((blowUp Z).presheaf.stalk x')} {a b : Λ}
    (ha : (blowUp Z).fromSpecStalk x' P ∈
      blowUpToBase Z ⁻¹' (((D a).support : Set Y) \ (Z.support : Set Y)))
    (hb : (blowUp Z).fromSpecStalk x' P ∈
      blowUpToBase Z ⁻¹' (((D b).support : Set Y) \ (Z.support : Set Y)))
    (hP : P.asIdeal.height ≤ 1) : a = b := by
  set g := (blowUp Z).fromSpecStalk x' P
  have : IsIso ((blowUpToBase Z).stalkMap g) :=
    isIso_stalkMap_of_isIso_morphismRestrict _ (isIso_blowUpToBase_restrict_compl_support Z)
      (show g ∈ blowUpToBase Z ⁻¹ᵁ Z.support.compl from ha.2)
  refine hD.eq_of_ringKrullDim_le_one (y := blowUpToBase Z g) ?_ ha.1 hb.1
  have h₁ : ringKrullDim ((blowUp Z).presheaf.stalk g) = (P.asIdeal.height : WithBot ℕ∞) :=
    ringKrullDim_stalk_fromSpecStalk (blowUp Z) x' P
  rw [ringKrullDim_eq_of_ringEquiv (asIso ((blowUpToBase Z).stalkMap g)).commRingCatIsoToRingEquiv,
    h₁]
  exact_mod_cast hP

/-- **Local coordinates on the blow-up, away from the centre**, where the blow-up is a local
isomorphism. -/
theorem exists_coordinates_blowUpTransformFamily_of_notMem {k : Type u} [Field k]
    {sY : Y ⟶ Spec (.of k)} [IsLocallyNoetherian Y] {Λ : Type*}
    {D : Λ → Y.IdealSheafData} (hD : IsSNCFamily sY D) (Z : Y.IdealSheafData) {x' : blowUp Z}
    (hx : blowUpToBase Z x' ∉ Z.support) :
    ∃ (N : ℕ) (w : Fin N → (blowUp Z).presheaf.stalk x')
      (c : {i // x' ∈ (blowUpTransformFamily D Z i).support} → Fin N),
      IsRegularSystemOfParameters w ∧
        (∀ i, IdealSheafData.stalk (blowUpTransformFamily D Z i.1) x' = Ideal.span {w (c i)}) ∧
        Function.Injective c := by
  have : IsLocallyNoetherian (blowUp Z) :=
    LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase Z)
  have hnotE := notMem_support_blowUpTransformFamily_inr D hx
  set π := blowUpToBase Z
  set φ := (π.stalkMap x').hom
  obtain ⟨n, z, c, hz, hc, hinj⟩ := hD.2 (π x')
  have hiso : IsIso (π.stalkMap x') :=
    isIso_stalkMap_of_isIso_morphismRestrict π (isIso_blowUpToBase_restrict_compl_support Z)
      (show x' ∈ π ⁻¹ᵁ Z.support.compl from hx)
  have hw : IsRegularSystemOfParameters fun i => φ (z i) :=
    isRegularSystemOfParameters_map_ringEquiv (asIso (π.stalkMap x')).commRingCatIsoToRingEquiv hz
  let c' : {i // x' ∈ (blowUpTransformFamily D Z i).support} → Fin n := fun i =>
    match i with
    | ⟨Sum.inl l, h⟩ => c ⟨l, mem_support_of_mem_blowUpTransformFamily_inl h⟩
    | ⟨Sum.inr u, h⟩ => absurd h (hnotE u)
  refine ⟨n, fun i => φ (z i), c', hw, ?_, ?_⟩
  · rintro ⟨(l | u), h⟩
    · have hl := mem_support_of_mem_blowUpTransformFamily_inl h
      refine stalk_vanishingIdeal_eq_span_singleton _ _
        (span_singleton_isPrime_of_isRegularSystemOfParameters hw _) fun p =>
          ⟨fun hp => ?_, fun hp => ?_⟩
      · exact (fromSpecStalk_mem_support_iff_stalkMap_mem π x' (D l) (hc ⟨l, hl⟩) p).1
          (closure_minimal (fun _ h => h.1) ((D l).support.isClosed.preimage π.continuous) hp)
      · refine subset_closure ⟨(fromSpecStalk_mem_support_iff_stalkMap_mem π x' (D l)
          (hc ⟨l, hl⟩) p).2 hp, fun hZ' => ?_⟩
        exact (Scheme.range_fromSpecStalk.subset ⟨p, rfl⟩ :
          (blowUp Z).fromSpecStalk x' p ⤳ x').mem_open
          ((Z.support.isClosed.isOpen_compl).preimage π.continuous) hx hZ'
    · exact absurd h (hnotE u)
  · rintro ⟨(a | u), ha⟩ ⟨(b | v), hb⟩ hab
    · obtain rfl : a = b := congrArg Subtype.val (hinj hab)
      rfl
    · exact absurd hb (hnotE v)
    · exact absurd ha (hnotE u)
    · exact absurd ha (hnotE u)

/-- **The chart hyperplanes at a point over the centre.** At `x'` over a point of the centre `Z`,
which has snc with `D`, there are a regular system of parameters `w` of `𝒪_{B_ZY,x'}`, an index
`i₀` with `(w_{i₀}) = I_{π⁻¹(Z),x'}`, and indices `τ(l)` for the members `D_l ∋ π(x')`, such that
off `(w_{i₀} = 0)` the inverse image of `D_l` is `(w_{τ(l)} = 0)` when `G(l)` holds and is empty
otherwise; `τ(l) ≠ i₀` when `G(l)` holds. -/
theorem exists_chart_hyperplanes [IsLocallyNoetherian Y] {Λ : Type*} {D : Λ → Y.IdealSheafData}
    {Z : Y.IdealSheafData} (hZ : HasSNCWith D Z) {x' : blowUp Z}
    (hx : blowUpToBase Z x' ∈ Z.support) :
    ∃ (N : ℕ) (w : Fin N → (blowUp Z).presheaf.stalk x') (i₀ : Fin N)
      (τ : {l // blowUpToBase Z x' ∈ (D l).support} → Fin N)
      (G : {l // blowUpToBase Z x' ∈ (D l).support} → Prop),
      IsRegularSystemOfParameters w ∧
        IdealSheafData.stalk (Z.comap (blowUpToBase Z)) x' = Ideal.span {w i₀} ∧
        (∀ q : PrimeSpectrum ((blowUp Z).presheaf.stalk x'),
          blowUpToBase Z ((blowUp Z).fromSpecStalk x' q) ∈ Z.support ↔ w i₀ ∈ q.asIdeal) ∧
        (∀ l, G l → τ l ≠ i₀) ∧
        (∀ l (q : PrimeSpectrum ((blowUp Z).presheaf.stalk x')),
          blowUpToBase Z ((blowUp Z).fromSpecStalk x' q) ∈ (D l.1).support →
            w i₀ ∉ q.asIdeal → G l ∧ w (τ l) ∈ q.asIdeal) ∧
        ∀ l, G l → ∀ q : PrimeSpectrum ((blowUp Z).presheaf.stalk x'), w (τ l) ∈ q.asIdeal →
          blowUpToBase Z ((blowUp Z).fromSpecStalk x' q) ∈ (D l.1).support := by
  obtain ⟨n, z, c, J, hz, hc, -, hJ⟩ := hZ (blowUpToBase Z x') hx
  obtain ⟨N, w, m, i₀, σ, U, hw, hmJ, -, hwi₀, hout, hin, hunit, hσ₀⟩ :=
    exists_chart_coordinates Z x' hx hz hJ
  have hEst : IdealSheafData.stalk (Z.comap (blowUpToBase Z)) x' = Ideal.span {w i₀} := by
    rw [IdealSheafData.stalk_comap, hJ]
    exact map_span_image_eq_span_of_chart _ hmJ hwi₀ hin hunit
  refine ⟨N, w, i₀, fun l => σ (c l), fun l => c l ≠ m ∧ c l ∉ U, hw, hEst, fun q => ?_,
    fun l hl => hσ₀ _ hl.1 hl.2, fun l q hq h0 => ?_, fun l hl q hq => ?_⟩
  · refine ((Set.ext_iff.1 (coe_support_blowUpTransformFamily_inr D Z ())
      ((blowUp Z).fromSpecStalk x' q)).symm.trans
        (fromSpecStalk_mem_support_iff_stalk_le _ x' q)).trans ?_
    change IdealSheafData.stalk (Z.comap (blowUpToBase Z)) x' ≤ q.asIdeal ↔ _
    rw [hEst, Ideal.span_singleton_le_iff_mem]
  · exact ne_and_mem_of_chart _ hwi₀ hout hin hunit q.isPrime h0
      ((fromSpecStalk_mem_support_iff_stalkMap_mem _ x' (D l.1) (hc l) q).1 hq)
  · exact (fromSpecStalk_mem_support_iff_stalkMap_mem _ x' (D l.1) (hc l) q).2
      (map_mem_of_chart _ hout hin hl.1 hl.2 hq)

/-- **Local coordinates on the blow-up, over the centre**: the coordinates of a chart. -/
theorem exists_coordinates_blowUpTransformFamily_of_mem {k : Type u} [Field k]
    {sY : Y ⟶ Spec (.of k)} [IsLocallyNoetherian Y] [CompactSpace Y] {Λ : Type*}
    {D : Λ → Y.IdealSheafData} (hD : IsSNCFamily sY D) {Z : Y.IdealSheafData}
    (hZ : HasSNCWith D Z) {x' : blowUp Z} (hx : blowUpToBase Z x' ∈ Z.support) :
    ∃ (N : ℕ) (w : Fin N → (blowUp Z).presheaf.stalk x')
      (c : {i // x' ∈ (blowUpTransformFamily D Z i).support} → Fin N),
      IsRegularSystemOfParameters w ∧
        (∀ i, IdealSheafData.stalk (blowUpTransformFamily D Z i.1) x' = Ideal.span {w (c i)}) ∧
        Function.Injective c := by
  have : IsLocallyNoetherian (blowUp Z) :=
    LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase Z)
  have : CompactSpace (blowUp Z) := QuasiCompact.compactSpace_of_compactSpace (blowUpToBase Z)
  have : IsNoetherian (blowUp Z) := {}
  set π := blowUpToBase Z
  set f' := (blowUp Z).fromSpecStalk x'
  obtain ⟨N, w, i₀, τ, G, hw, hEst, hE, hτ₀, hgood, hτD⟩ := exists_chart_hyperplanes hZ hx
  have hTsub' : ∀ l, x' ∈ (blowUpTransformFamily D Z (Sum.inl l)).support →
      π x' ∈ (D l).support := fun _ => mem_support_of_mem_blowUpTransformFamily_inl
  have hP₀ : ∀ l (hl : π x' ∈ (D l).support), G ⟨l, hl⟩ →
      f' ⟨Ideal.span {w (τ ⟨l, hl⟩)}, span_singleton_isPrime_of_isRegularSystemOfParameters hw _⟩ ∈
        π ⁻¹' (((D l).support : Set Y) \ (Z.support : Set Y)) := fun l hl hG =>
    ⟨hτD _ hG _ (Ideal.subset_span rfl), fun hZ' =>
      notMem_span_singleton_of_ne_of_isRegularSystemOfParameters hw (hτ₀ _ hG) ((hE _).1 hZ')⟩
  have hgoodT : ∀ l (h : x' ∈ (blowUpTransformFamily D Z (Sum.inl l)).support),
      G ⟨l, hTsub' l h⟩ := by
    intro l h
    have h' : f' (IsLocalRing.closedPoint _) ∈
        closure (π ⁻¹' (((D l).support : Set Y) \ (Z.support : Set Y))) := by
      rw [Scheme.fromSpecStalk_closedPoint, ← coe_support_blowUpTransformFamily_inl D Z l]
      exact h
    obtain ⟨q, -, hq⟩ := exists_le_fromSpecStalk_mem_of_mem_closure π (D l).support.isClosed
      Z.support.isClosed h'
    exact (hgood _ q hq.1 fun h => hq.2 ((hE q).2 h)).1
  let c' : {i // x' ∈ (blowUpTransformFamily D Z i).support} → Fin N := fun i =>
    match i with
    | ⟨Sum.inl l, h⟩ => τ ⟨l, hTsub' l h⟩
    | ⟨Sum.inr _, _⟩ => i₀
  refine ⟨N, w, c', hw, ?_, ?_⟩
  · rintro ⟨(l | u), h⟩
    · refine stalk_vanishingIdeal_eq_span_singleton _ _
        (span_singleton_isPrime_of_isRegularSystemOfParameters hw _) fun p =>
        (fromSpecStalk_mem_closure_iff_of_forall π (D l).support.isClosed Z.support.isClosed
          (hP₀ l _ (hgoodT l h)) (fun q hq => (Ideal.span_singleton_le_iff_mem _).2
            (hgood _ q hq.1 fun h => hq.2 ((hE q).2 h)).2) p).trans
          (Ideal.span_singleton_le_iff_mem _)
    · exact hEst
  · rintro ⟨(a | u), ha⟩ ⟨(b | v), hb⟩ hab
    · change τ ⟨a, hTsub' a ha⟩ = τ ⟨b, hTsub' b hb⟩ at hab
      have hPb := hP₀ b (hTsub' b hb) (hgoodT b hb)
      rw [← hab] at hPb
      obtain rfl := hD.eq_of_mem_preimage_sdiff Z (hP₀ a (hTsub' a ha) (hgoodT a ha)) hPb
        (hw.height_span_singleton_le_one _)
      rfl
    · change τ ⟨a, hTsub' a ha⟩ = i₀ at hab
      exact absurd hab (hτ₀ _ (hgoodT a ha))
    · change i₀ = τ ⟨b, hTsub' b hb⟩ at hab
      exact absurd hab.symm (hτ₀ _ (hgoodT b hb))
    · rfl

/-- **Local coordinates on the blow-up of a centre having snc with an snc family.** Let `D` be a
simple normal crossing family on `Y` and `Z` a closed subscheme having simple normal crossings
with it, and let `π : B_ZY → Y` be the blow-up. At every point of `B_ZY` there are local
coordinates in which each member through the point of the family of the transforms
`π⁻¹(D_λ ∖ Z)‾` and of the exceptional divisor `π⁻¹(Z)` is a coordinate hyperplane, distinct
members with distinct coordinates. -/
theorem exists_coordinates_blowUpTransformFamily {k : Type u} [Field k]
    {sY : Y ⟶ Spec (.of k)} [IsLocallyNoetherian Y] [CompactSpace Y] {Λ : Type*}
    {D : Λ → Y.IdealSheafData} (hD : IsSNCFamily sY D) {Z : Y.IdealSheafData}
    (hZ : HasSNCWith D Z) (x' : blowUp Z) :
    ∃ (N : ℕ) (w : Fin N → (blowUp Z).presheaf.stalk x')
      (c : {i // x' ∈ (blowUpTransformFamily D Z i).support} → Fin N),
      IsRegularSystemOfParameters w ∧
        (∀ i, IdealSheafData.stalk (blowUpTransformFamily D Z i.1) x' = Ideal.span {w (c i)}) ∧
        Function.Injective c := by
  by_cases hx : blowUpToBase Z x' ∈ Z.support
  · exact exists_coordinates_blowUpTransformFamily_of_mem hD hZ hx
  · exact exists_coordinates_blowUpTransformFamily_of_notMem hD Z hx

/-- **The blow-up of a centre having snc with an snc divisor.** Let `Y` be a quasi-compact scheme
locally of finite type over a perfect field `k`, `D = ∑_λ D_λ` a simple normal crossing divisor on
`Y` and `Z ⊆ Y` a closed subscheme having simple normal crossings with `D`. Then on the blow-up
`π : B_ZY → Y`, the family of the transforms `π⁻¹(D_λ ∖ Z)‾` and of the exceptional divisor
`π⁻¹(Z)` is a simple normal crossing divisor. -/
theorem isSNCFamily_blowUpTransformFamily {k : Type u} [Field k] [PerfectField k]
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] [CompactSpace Y] {Λ : Type*}
    {D : Λ → Y.IdealSheafData} (hD : IsSNCFamily sY D) {Z : Y.IdealSheafData}
    (hZ : HasSNCWith D Z) : IsSNCFamily (blowUpToBase Z ≫ sY) (blowUpTransformFamily D Z) := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : IsLocallyNoetherian (blowUp Z) :=
    LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase Z)
  have hpar : ∀ i, ∀ y ∈ (blowUpTransformFamily D Z i).support,
      ∃ (m : ℕ) (w : Fin m → (blowUp Z).presheaf.stalk y) (j : Fin m),
        IsRegularSystemOfParameters w ∧
          IdealSheafData.stalk (blowUpTransformFamily D Z i) y = Ideal.span {w j} := by
    intro i y hy
    obtain ⟨N, w, c, hw, hc, -⟩ := exists_coordinates_blowUpTransformFamily hD hZ y
    exact ⟨N, w, c ⟨i, hy⟩, hw, hc ⟨i, hy⟩⟩
  refine ⟨fun i => ⟨isReduced_subscheme_of_stalk_eq_span_parameter _ (hpar i),
    isPureCodimOne_support_of_stalk_eq_span_parameter _ (hpar i),
    isSmoothScheme_subscheme_of_stalk_eq_span_parameter _ _ (hpar i)⟩, fun y => ?_⟩
  exact exists_coordinates_blowUpTransformFamily hD hZ y

end Transform

/-! ### Generic points -/

section Generic

variable {Y : Scheme.{u}}

/-- A point of a scheme is maximal for generization exactly when it is the generic point of an
irreducible component. -/
theorem isMax_iff_closure_singleton_mem_irreducibleComponents (y : Y) :
    IsMax y ↔ closure {y} ∈ irreducibleComponents Y := by
  rw [closure_singleton_mem_irreducibleComponents_iff]
  constructor
  · intro h ξ hξ
    exact Scheme.le_iff_specializes.1 (h (Scheme.le_iff_specializes.2 hξ))
  · intro h b hb
    exact Scheme.le_iff_specializes.2 (h b (Scheme.le_iff_specializes.1 hb))

/-- The local ring at a point is zero-dimensional exactly when the point is the generic point of
an irreducible component. -/
theorem ringKrullDim_stalk_eq_zero_iff (y : Y) :
    ringKrullDim (Y.presheaf.stalk y) = 0 ↔ closure {y} ∈ irreducibleComponents Y := by
  rw [ringKrullDim_stalk_eq_coheight, ← isMax_iff_closure_singleton_mem_irreducibleComponents,
    ← Order.coheight_eq_zero]
  constructor
  · intro h; exact_mod_cast h
  · intro h; rw [h]; rfl

/-- No member of a simple normal crossing family passes through the generic point of an
irreducible component. -/
theorem IsSNCFamily.notMem_support_of_mem_irreducibleComponents {k : Type u} [Field k]
    {sY : Y ⟶ Spec (.of k)} {Λ : Type*} {D : Λ → Y.IdealSheafData} (hD : IsSNCFamily sY D)
    {η : Y} (hη : closure {η} ∈ irreducibleComponents Y) (i : Λ) : η ∉ (D i).support := by
  intro hi
  obtain ⟨N, w, c, hw, -, -⟩ := hD.2 η
  have h0 := (ringKrullDim_stalk_eq_zero_iff η).2 hη
  rw [hw.2] at h0
  have hN : N = 0 := by exact_mod_cast h0
  subst hN
  exact (c ⟨i, hi⟩).elim0

/-- A scheme locally of finite type over a perfect field carrying a simple normal crossing family
is smooth: the family provides a regular system of parameters at every point. -/
theorem IsSNCFamily.isSmoothScheme {k : Type u} [Field k] [PerfectField k]
    {sY : Y ⟶ Spec (.of k)} [LocallyOfFiniteType sY] {Λ : Type*} {D : Λ → Y.IdealSheafData}
    (hD : IsSNCFamily sY D) : IsSmoothScheme sY := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  rw [MMP.Mori.isSmoothScheme_iff,
    MMP.Flips.ResolutionInputs.smooth_iff_forall_isRegularLocalRing_stalk]
  intro y
  obtain ⟨n, z, c, hz, -⟩ := hD.2 y
  exact MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hz

/-- **An ordered divisor whose members are locally members of an snc family.** If at every point
`y` the entries of `G = (G^1, …, G^m)` through `y` are, near `y`, distinct members of a simple
normal crossing family `D`, then `G` is an ordered simple normal crossing divisor. -/
theorem isOrderedSNC_of_exists_rep {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [LocallyOfFiniteType sX] {Λ : Type*} {D : Λ → X.IdealSheafData}
    (hD : IsSNCFamily sX D) {m : ℕ} (G : Fin m → X.IdealSheafData)
    (hrep : ∀ y : X, ∃ r : Fin m → Λ, Function.Injective r ∧ ∀ i, y ∈ (G i).support →
      y ∈ (D (r i)).support ∧ IdealSheafData.stalk (G i) y = IdealSheafData.stalk (D (r i)) y) :
    OrderedDivisor.IsOrderedSNC sX ⟨m, G⟩ := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have hpar : ∀ i, ∀ y ∈ (G i).support, ∃ (n : ℕ) (w : Fin n → X.presheaf.stalk y) (t : Fin n),
      IsRegularSystemOfParameters w ∧ IdealSheafData.stalk (G i) y = Ideal.span {w t} := by
    intro i y hy
    obtain ⟨r, -, hr⟩ := hrep y
    obtain ⟨hy', hst⟩ := hr i hy
    obtain ⟨n, w, t, hw, ht⟩ := hD.exists_stalk_eq_span_parameter (r i) y hy'
    exact ⟨n, w, t, hw, hst.trans ht⟩
  have hcoord : ∀ y : X, ∃ (n : ℕ) (z : Fin n → X.presheaf.stalk y)
      (c : {i // y ∈ (G i).support} → Fin n), IsRegularSystemOfParameters z ∧
        (∀ i, IdealSheafData.stalk (G i.1) y = Ideal.span {z (c i)}) ∧ Function.Injective c := by
    intro y
    obtain ⟨r, hr_inj, hr⟩ := hrep y
    obtain ⟨n, z, c, hz, hc, hinj⟩ := hD.2 y
    refine ⟨n, z, fun i => c ⟨r i.1, (hr i.1 i.2).1⟩, hz,
      fun i => (hr i.1 i.2).2.trans (hc ⟨r i.1, (hr i.1 i.2).1⟩),
      fun a b hab => ?_⟩
    exact Subtype.ext (hr_inj (congrArg Subtype.val (hinj hab)))
  exact ⟨fun i => ⟨isReduced_subscheme_of_stalk_eq_span_parameter _ (hpar i),
      isEffectiveCartierDivisor_of_stalk_eq_span_parameter _ (hpar i)⟩,
    fun i => ⟨isReduced_subscheme_of_stalk_eq_span_parameter _ (hpar i),
      isPureCodimOne_support_of_stalk_eq_span_parameter _ (hpar i),
      isSmoothScheme_subscheme_of_stalk_eq_span_parameter sX _ (hpar i)⟩, hcoord⟩

end Generic

/-! ### The stages of the disjoining construction -/

namespace DisjoiningStage

variable {k j : ℕ}

/-- The indices of the total divisor `D_{j+1}` of the next stage among the transforms of the
members of `D_j` (`Sum.inl`) and the new exceptional divisor (`Sum.inr`). -/
def stepIndex : Fin k ⊕ Fin (j + 1) → (Fin k ⊕ Fin j) ⊕ Unit
  | Sum.inl i => Sum.inl (Sum.inl i)
  | Sum.inr l => Fin.lastCases (Sum.inr ()) (fun l => Sum.inl (Sum.inr l)) l

/-- `stepIndex` is injective. -/
theorem stepIndex_injective : Function.Injective (stepIndex (k := k) (j := j)) := by
  rintro (i | l) (i' | l') h
  · simpa [stepIndex] using h
  · induction l' using Fin.lastCases <;> simp [stepIndex] at h
  · induction l using Fin.lastCases <;> simp [stepIndex] at h
  · induction l using Fin.lastCases <;> induction l' using Fin.lastCases <;>
      simp_all [stepIndex]

/-- `stepIndex` is surjective. -/
theorem stepIndex_surjective : Function.Surjective (stepIndex (k := k) (j := j)) := by
  rintro ((i | l) | u)
  · exact ⟨Sum.inl i, rfl⟩
  · exact ⟨Sum.inr l.castSucc, by simp [stepIndex]⟩
  · exact ⟨Sum.inr (Fin.last j), by simp [stepIndex]⟩

variable (st : DisjoiningStage.{u} k j)

/-- The total divisor of the next stage is the family of the transforms of the members of `D_j`
and the exceptional divisor of `π_j`. -/
theorem sumElim_step_eq :
    (Sum.elim st.step.Es st.step.Fs : Fin k ⊕ Fin (j + 1) → (blowUp st.center).IdealSheafData) =
      blowUpTransformFamily (Sum.elim st.Es st.Fs) st.center ∘ stepIndex := by
  funext i
  rcases i with i | l
  · rfl
  · induction l using Fin.lastCases with
    | last => simp [stepIndex, step, blowUpTransformFamily]
    | cast l => simp [stepIndex, step, blowUpTransformFamily, transform]

/-- As a set, the total divisor of the next stage is the total transform of `D_j`. -/
theorem iUnion_support_step :
    ⋃ i, ((Sum.elim st.step.Es st.step.Fs i).support : Set st.step.X) =
      ClosedBlowupSequence.totalTransformStep st.center
        (⋃ i, ((Sum.elim st.Es st.Fs i).support : Set st.X)) := by
  rw [← iUnion_support_blowUpTransformFamily]
  refine (Set.iUnion_congr fun i => congrArg (fun I => (I.support : Set (blowUp st.center)))
    (congrFun st.sumElim_step_eq i)).trans ?_
  exact stepIndex_surjective.iUnion_comp
    (fun t => ((blowUpTransformFamily (Sum.elim st.Es st.Fs) st.center t).support :
      Set (blowUp st.center)))

/-- **One step of the disjoining construction keeps the total divisor snc.** If (a) `D_j` is a
simple normal crossing divisor and (b) no point of `X_j` lies on `k - j + 1` of the `E_i^{(j)}`,
then `D_{j+1}` is a simple normal crossing divisor. -/
theorem isSNCFamily_step {K : Type u} [Field K] [PerfectField K] (s : st.X ⟶ Spec (.of K))
    [LocallyOfFiniteType s] [CompactSpace st.X] (ha : IsSNCFamily s (Sum.elim st.Es st.Fs))
    (hb : ∀ (x : st.X) (S : Finset (Fin k)), S.card = k - j + 1 →
      ∃ i ∈ S, x ∉ (st.Es i).support) :
    IsSNCFamily (blowUpToBase st.center ≫ s) (Sum.elim st.step.Es st.step.Fs) := by
  have : IsLocallyNoetherian st.X := LocallyOfFiniteType.isLocallyNoetherian s
  exact (congrArg (IsSNCFamily (blowUpToBase st.center ≫ s)) st.sumElim_step_eq).mpr
    ((isSNCFamily_blowUpTransformFamily s ha (st.hasSNCWith_center s ha hb)).comp _
      stepIndex_injective)

/-- The composite `X_{j+n} → X_j` of the next `n` blow-ups of the disjoining construction. -/
def iterateToBase : (n : ℕ) → {j : ℕ} → (st : DisjoiningStage.{u} k j) → (st.iterate n).X ⟶ st.X
  | 0, _, st => 𝟙 st.X
  | n + 1, _, st => blowUpToBase (st.iterate n).center ≫ iterateToBase n st

/-- With no blow-ups, the composite is the identity. -/
@[simp] theorem iterateToBase_zero : st.iterateToBase 0 = 𝟙 st.X := rfl

/-- The composite of `n + 1` blow-ups is the last blow-up followed by the composite of the
first `n`. -/
theorem iterateToBase_succ (n : ℕ) :
    st.iterateToBase (n + 1) = blowUpToBase (st.iterate n).center ≫ st.iterateToBase n := rfl

/-- **The invariant of the disjoining construction**, from an arbitrary stage: if (a) and (b)
hold at stage `j`, they hold at stage `j + n` for `j + n ≤ k`. -/
theorem invariant_iterate {K : Type u} [Field K] [PerfectField K] (s : st.X ⟶ Spec (.of K))
    [LocallyOfFiniteType s] [QuasiCompact s] (ha : IsSNCFamily s (Sum.elim st.Es st.Fs))
    (hb : ∀ (x : st.X) (S : Finset (Fin k)), S.card = k - j + 1 →
      ∃ i ∈ S, x ∉ (st.Es i).support) (n : ℕ) (hn : j + n ≤ k) :
    LocallyOfFiniteType (st.iterateToBase n ≫ s) ∧ QuasiCompact (st.iterateToBase n ≫ s) ∧
      IsSNCFamily (st.iterateToBase n ≫ s) (Sum.elim (st.iterate n).Es (st.iterate n).Fs) ∧
      ∀ (x : (st.iterate n).X) (S : Finset (Fin k)), S.card = k - (j + n) + 1 →
        ∃ i ∈ S, x ∉ ((st.iterate n).Es i).support := by
  induction n with
  | zero =>
    change LocallyOfFiniteType (𝟙 st.X ≫ s) ∧ QuasiCompact (𝟙 st.X ≫ s) ∧
      IsSNCFamily (𝟙 st.X ≫ s) (Sum.elim st.Es st.Fs) ∧ _
    rw [Category.id_comp]
    exact ⟨inferInstance, inferInstance, ha, hb⟩
  | succ n ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih (by omega)
    set st' := st.iterate n
    set s' := st.iterateToBase n ≫ s
    have : IsLocallyNoetherian st'.X := LocallyOfFiniteType.isLocallyNoetherian s'
    have : CompactSpace st'.X := QuasiCompact.compactSpace_of_compactSpace s'
    change LocallyOfFiniteType ((blowUpToBase st'.center ≫ st.iterateToBase n) ≫ s) ∧
      QuasiCompact ((blowUpToBase st'.center ≫ st.iterateToBase n) ≫ s) ∧
      IsSNCFamily ((blowUpToBase st'.center ≫ st.iterateToBase n) ≫ s)
        (Sum.elim st'.step.Es st'.step.Fs) ∧
      ∀ (x : st'.step.X) (S : Finset (Fin k)), S.card = k - (j + (n + 1)) + 1 →
        ∃ i ∈ S, x ∉ (st'.step.Es i).support
    rw [Category.assoc]
    refine ⟨inferInstance, inferInstance, st'.isSNCFamily_step s' h3 h4, fun x S hS => ?_⟩
    exact st'.exists_notMem_support_step_Es s' h3 h4 x S (by omega)

/-- **The disjoining blow-ups are smooth, with centres having snc with the total transform**,
from an arbitrary stage: if (a) and (b) hold at stage `j` and `j + n ≤ k`, the next `n` blow-ups
of the disjoining construction form a smooth blow-up sequence whose centres have simple normal
crossings with `D_j`. -/
theorem sequence_isSmooth_and_centersHaveSNCWith {K : Type u} [Field K] [PerfectField K]
    (n : ℕ) : ∀ {j : ℕ} (st : DisjoiningStage.{u} k j) (s : st.X ⟶ Spec (.of K))
      [LocallyOfFiniteType s] [QuasiCompact s], IsSNCFamily s (Sum.elim st.Es st.Fs) →
      (∀ (x : st.X) (S : Finset (Fin k)), S.card = k - j + 1 →
        ∃ i ∈ S, x ∉ (st.Es i).support) → j + n ≤ k →
      (st.sequence n).IsSmooth s ∧
        (st.sequence n).CentersHaveSNCWith s
          (⋃ i, ((Sum.elim st.Es st.Fs i).support : Set st.X)) := by
  induction n with
  | zero => intro j st s _ _ _ _ _; exact ⟨trivial, trivial⟩
  | succ n ih =>
    intro j st s _ _ ha hb hn
    have : IsLocallyNoetherian st.X := LocallyOfFiniteType.isLocallyNoetherian s
    have : CompactSpace st.X := QuasiCompact.compactSpace_of_compactSpace s
    have hZ := st.hasSNCWith_center s ha hb
    have hX : IsSmoothScheme s := ha.isSmoothScheme
    have ha' := st.isSNCFamily_step s ha hb
    have hb' : ∀ (x : st.step.X) (S : Finset (Fin k)), S.card = k - (j + 1) + 1 →
        ∃ i ∈ S, x ∉ (st.step.Es i).support := fun x S hS =>
      st.exists_notMem_support_step_Es s ha hb x S (by omega)
    have : LocallyOfFiniteType (show st.step.X ⟶ Spec (.of K) from blowUpToBase st.center ≫ s) := by
      change LocallyOfFiniteType (blowUpToBase st.center ≫ s)
      infer_instance
    have : QuasiCompact (show st.step.X ⟶ Spec (.of K) from blowUpToBase st.center ≫ s) := by
      change QuasiCompact (blowUpToBase st.center ≫ s)
      infer_instance
    obtain ⟨ih1, ih2⟩ := ih st.step (blowUpToBase st.center ≫ s) ha' hb' (by omega)
    refine ⟨⟨hX, isSmoothScheme_subscheme_of_hasSNCWith s hX ha hZ, ih1⟩,
      ha.isSNCClosedSubset_iUnion, hZ.componentsFamily_iUnion, ?_⟩
    rwa [← st.iUnion_support_step]

/-! #### The end of the disjoining construction -/

/-- As a set, the supremum in `Closeds` of the supports of the `E_i^{(j)}` is their union. -/
theorem coe_iSup_support_Es :
    ((⨆ i, (st.Es i).support : Closeds st.X) : Set st.X) = ⋃ i, ((st.Es i).support : Set st.X) := by
  rw [← Finset.sup_univ_eq_iSup, Closeds.coe_finset_sup]
  simp

/-- The support of the reduced divisor `⋃_i E_i^{(j)}`. -/
theorem coe_support_unionEs :
    (st.unionEs.support : Set st.X) = ⋃ i, ((st.Es i).support : Set st.X) := by
  unfold unionEs
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal, coe_iSup_support_Es]

/-- If the `E_i^{(j)}` are pairwise disjoint, then near a point of `E_i^{(j)}` the reduced divisor
`⋃_i E_i^{(j)}` is `E_i^{(j)}`. -/
theorem stalk_unionEs {K : Type u} [Field K] {s : st.X ⟶ Spec (.of K)}
    (ha : IsSNCFamily s (Sum.elim st.Es st.Fs))
    (hdisj : ∀ (x : st.X) (i i' : Fin k), x ∈ (st.Es i).support → x ∈ (st.Es i').support →
      i = i') {x : st.X} {i : Fin k} (hx : x ∈ (st.Es i).support) :
    IdealSheafData.stalk st.unionEs x = IdealSheafData.stalk (st.Es i) x := by
  have : IsReduced (st.Es i).subscheme := (ha.1 (Sum.inl i)).1
  have hred : st.Es i = Scheme.IdealSheafData.vanishingIdeal (st.Es i).support :=
    Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme _ _ rfl
  conv_rhs => rw [hred]
  unfold unionEs
  rw [stalk_vanishingIdeal_eq, stalk_vanishingIdeal_eq, coe_iSup_support_Es]
  congr 1
  ext p
  refine ⟨fun hp => ?_, fun hp => Set.mem_preimage.2 (Set.mem_iUnion.2 ⟨i, hp⟩)⟩
  obtain ⟨i', hp⟩ := Set.mem_iUnion.1 (Set.mem_preimage.1 hp)
  have hxi' : x ∈ (st.Es i').support :=
    (Scheme.range_fromSpecStalk.subset ⟨p, rfl⟩ : st.X.fromSpecStalk x p ⤳ x).mem_closed
      (st.Es i').support.isClosed hp
  obtain rfl := hdisj x i' i hxi' hx
  exact hp

/-- At every point, the members of `(⋃_i E_i^{(j)}, F^{1,(j)}, …, F^{j,(j)})` through it are,
near it, distinct members of `D_j`, provided the `E_i^{(j)}` are pairwise disjoint. -/
theorem exists_rep_cons_unionEs {K : Type u} [Field K] {s : st.X ⟶ Spec (.of K)}
    (ha : IsSNCFamily s (Sum.elim st.Es st.Fs))
    (hdisj : ∀ (x : st.X) (i i' : Fin k), x ∈ (st.Es i).support → x ∈ (st.Es i').support →
      i = i') (hk : 0 < k) (y : st.X) :
    ∃ r : Fin (j + 1) → Fin k ⊕ Fin j, Function.Injective r ∧
      ∀ i, y ∈ (Fin.cons (α := fun _ => st.X.IdealSheafData) st.unionEs st.Fs i).support →
        y ∈ (Sum.elim st.Es st.Fs (r i)).support ∧
          IdealSheafData.stalk (Fin.cons (α := fun _ => st.X.IdealSheafData) st.unionEs st.Fs i) y =
            IdealSheafData.stalk (Sum.elim st.Es st.Fs (r i)) y := by
  classical
  obtain ⟨iy, hiy⟩ : ∃ iy : Fin k, ∀ i, y ∈ (st.Es i).support → i = iy := by
    by_cases h : ∃ i, y ∈ (st.Es i).support
    · obtain ⟨i, hi⟩ := h
      exact ⟨i, fun i' hi' => hdisj y i' i hi' hi⟩
    · exact ⟨⟨0, hk⟩, fun i hi => (h ⟨i, hi⟩).elim⟩
  refine ⟨Fin.cons (α := fun _ => Fin k ⊕ Fin j) (Sum.inl iy) Sum.inr, ?_, fun i => ?_⟩
  · intro a b hab
    induction a using Fin.cases with
    | zero =>
      induction b using Fin.cases with
      | zero => rfl
      | succ b => simp at hab
    | succ a =>
      induction b using Fin.cases with
      | zero => simp at hab
      | succ b => simpa using hab
  · induction i using Fin.cases with
    | zero =>
      intro hy
      rw [Fin.cons_zero] at hy ⊢
      have hy' : y ∈ ⋃ i, ((st.Es i).support : Set st.X) := by
        rwa [← coe_support_unionEs]
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy'
      obtain rfl := hiy i hi
      exact ⟨hi, st.stalk_unionEs ha hdisj hi⟩
    | succ l =>
      intro hy
      rw [Fin.cons_succ] at hy ⊢
      exact ⟨hy, rfl⟩

/-- **The ordered divisor at the end of the disjoining construction.** If `D_j` is a simple
normal crossing divisor and the `E_i^{(j)}` are pairwise disjoint, then
`(⋃_i E_i^{(j)}, F^{1,(j)}, …, F^{j,(j)})` is an ordered simple normal crossing divisor. -/
theorem isOrderedSNC_divisor_zero {K : Type u} [Field K] [PerfectField K]
    (s : st.X ⟶ Spec (.of K)) [LocallyOfFiniteType s] (ha : IsSNCFamily s (Sum.elim st.Es st.Fs))
    (hdisj : ∀ (x : st.X) (i i' : Fin k), x ∈ (st.Es i).support → x ∈ (st.Es i').support →
      i = i') (hk : 0 < k) : (st.divisor 0).IsOrderedSNC s :=
  isOrderedSNC_of_exists_rep ha _ (st.exists_rep_cons_unionEs ha hdisj hk)

/-- **The end of the disjoining construction is a triple**, from an arbitrary stage: if `X_j` is
equidimensional, `I` is nonzero at its generic points, (a) and (b) hold at stage `j`, and
`j + n + 1 = k`, then after the next `n` blow-ups, `(X_{k-1}, π^*I, E_{X'})` is a triple. -/
theorem isTriple_sequence {K : Type u} [Field K] [CharZero K] (n : ℕ) :
    ∀ {j : ℕ} (st : DisjoiningStage.{u} k j) (s : st.X ⟶ Spec (.of K))
      [LocallyOfFiniteType s] [QuasiCompact s] (I : st.X.IdealSheafData),
      Equidimensional st.X → IsNonzeroAtGenericPoints I →
      IsSNCFamily s (Sum.elim st.Es st.Fs) →
      (∀ (x : st.X) (S : Finset (Fin k)), S.card = k - j + 1 →
        ∃ i ∈ S, x ∉ (st.Es i).support) → j + n + 1 = k →
      IsTriple ((st.sequence n).toBase ≫ s) (I.comap (st.sequence n).toBase) (st.divisor n) := by
  induction n with
  | zero =>
    intro j st s _ _ I hX hI ha hb hk
    change IsTriple (𝟙 st.X ≫ s) (I.comap (𝟙 st.X)) (st.divisor 0)
    rw [Category.id_comp, Scheme.IdealSheafData.comap_id]
    have hdisj : ∀ (x : st.X) (i i' : Fin k), x ∈ (st.Es i).support →
        x ∈ (st.Es i').support → i = i' := by
      intro x i i' hi hi'
      by_contra hne
      obtain ⟨l, hl, hxl⟩ := hb x {i, i'} (by rw [Finset.card_pair hne]; omega)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with rfl | rfl
      exacts [hxl hi, hxl hi']
    exact ⟨inferInstance, ha.isSmoothScheme, inferInstance, inferInstance, hX, hI,
      st.isOrderedSNC_divisor_zero s ha hdisj (by omega)⟩
  | succ n ih =>
    intro j st s _ _ I hX hI ha hb hk
    have : IsLocallyNoetherian st.X := LocallyOfFiniteType.isLocallyNoetherian s
    have : CompactSpace st.X := QuasiCompact.compactSpace_of_compactSpace s
    have ha' := st.isSNCFamily_step s ha hb
    have hb' : ∀ (x : st.step.X) (S : Finset (Fin k)), S.card = k - (j + 1) + 1 →
        ∃ i ∈ S, x ∉ (st.step.Es i).support := fun x S hS =>
      st.exists_notMem_support_step_Es s ha hb x S (by omega)
    have : LocallyOfFiniteType (show st.step.X ⟶ Spec (.of K) from blowUpToBase st.center ≫ s) := by
      change LocallyOfFiniteType (blowUpToBase st.center ≫ s)
      infer_instance
    have : QuasiCompact (show st.step.X ⟶ Spec (.of K) from blowUpToBase st.center ≫ s) := by
      change QuasiCompact (blowUpToBase st.center ≫ s)
      infer_instance
    have h := ih st.step (blowUpToBase st.center ≫ s) (I.comap (blowUpToBase st.center))
      (equidimensional_blowUp s st.center hX)
      (isNonzeroAtGenericPoints_comap_blowUpToBase st.center hI) ha' hb' (by omega)
    have e1 : (st.sequence (n + 1)).toBase ≫ s =
        (st.step.sequence n).toBase ≫ blowUpToBase st.center ≫ s := Category.assoc _ _ _
    have e2 : I.comap (st.sequence (n + 1)).toBase =
        (I.comap (blowUpToBase st.center)).comap (st.step.sequence n).toBase :=
      Scheme.IdealSheafData.comap_comp _ _ _
    rwa [e1, e2]

end DisjoiningStage

/-! ### The disjoining sequence -/

section Disjoining

variable {X : Scheme.{u}}

/-- The composite `X_j → X` of the first `j` blow-ups of the disjoining construction for
`(X, E)`. -/
def disjoiningToBase (E : OrderedDivisor X) (j : ℕ) : (disjoiningStage E j).X ⟶ X :=
  (disjoiningStart E).iterateToBase j

/-- If the ordered divisor `E` is snc, the total divisor `D_0 = ∑_i E_i` of the first stage of the
disjoining construction is an snc family. -/
theorem isSNCFamily_disjoiningStart {K : Type u} [Field K] {sX : X ⟶ Spec (.of K)}
    {E : OrderedDivisor X} (hE : E.IsSNC sX) :
    IsSNCFamily sX (Sum.elim (disjoiningStart E).Es (disjoiningStart E).Fs) := by
  have h : (Sum.elim (disjoiningStart E).Es (disjoiningStart E).Fs :
      Fin E.s ⊕ Fin 0 → X.IdealSheafData) =
      E.E ∘ Sum.elim id (Fin.elim0 : Fin 0 → Fin E.s) := by
    funext i
    rcases i with i | l
    · rfl
    · exact l.elim0
  refine (congrArg (IsSNCFamily sX) h).mpr (IsSNCFamily.comp hE _ ?_)
  rintro (i | l) (i' | l') h
  · simpa using h
  · exact l'.elim0
  · exact l.elim0
  · exact l.elim0

/-- No point of the first stage of the disjoining construction lies on `s + 1` of the `E_i`. -/
theorem exists_notMem_support_disjoiningStart_Es (E : OrderedDivisor X)
    (x : (disjoiningStart E).X) (S : Finset (Fin E.s)) (hS : S.card = E.s - 0 + 1) :
    ∃ i ∈ S, x ∉ ((disjoiningStart E).Es i).support := by
  have := S.card_le_univ
  simp only [Fintype.card_fin] at this
  omega

/-- **Kollár 3.72, the invariant of the disjoining sequence.** Let `X` be a quasi-compact scheme
locally of finite type over a perfect field `K` (e.g. of characteristic `0`) and
`E = (E_1, …, E_k)` an ordered divisor whose sum is a simple normal crossing divisor. For every
`0 ≤ j ≤ k - 1`, (a) the total divisor `D_j = ∑_i E_i^{(j)} + ∑_{l ≤ j} F^{l,(j)}` on `X_j` is a
simple normal crossing divisor, and (b) no point of `X_j` lies on `k - j + 1` of the
`E_i^{(j)}`. -/
@[mmp "lem_kr3c_disjoining_invariant"]
theorem isSNCFamily_disjoiningTotalDivisor_and_exists_notMem {K : Type u} [Field K]
    [PerfectField K] (sX : X ⟶ Spec (.of K)) [LocallyOfFiniteType sX] [QuasiCompact sX]
    (E : OrderedDivisor X) (hE : E.IsSNC sX) (j : ℕ) (hj : j < E.s) :
    IsSNCFamily (disjoiningToBase E j ≫ sX) (disjoiningTotalDivisor E j) ∧
      ∀ (x : (disjoiningStage E j).X) (S : Finset (Fin E.s)), S.card = E.s - j + 1 →
        ∃ i ∈ S, x ∉ ((disjoiningStage E j).Es i).support := by
  have : LocallyOfFiniteType (show (disjoiningStart E).X ⟶ Spec (.of K) from sX) :=
    ‹LocallyOfFiniteType sX›
  have : QuasiCompact (show (disjoiningStart E).X ⟶ Spec (.of K) from sX) := ‹QuasiCompact sX›
  obtain ⟨-, -, ha, hb⟩ := (disjoiningStart E).invariant_iterate sX
    (isSNCFamily_disjoiningStart hE) (exists_notMem_support_disjoiningStart_Es _) j (by omega)
  exact ⟨ha, fun x S hS => hb x S (by simpa using hS)⟩

/-- **Kollár 3.72: the disjoining sequence is a smooth blow-up sequence whose centres have simple
normal crossings with `E`.** Let `X` be a quasi-compact scheme locally of finite type over a
perfect field `K` (e.g. of characteristic `0`) and `E = (E_1, …, E_k)` an ordered divisor whose
sum is a simple normal crossing divisor. Then the disjoining sequence of `(X, E)` is a smooth
blow-up sequence, and its centres have simple normal crossings with `E` (Kollár Def. 3.25). -/
@[mmp "lem_kr3c_disjoining_centers_snc"]
theorem isSmooth_disjoiningSequence_and_centersHaveSNCWith {K : Type u} [Field K]
    [PerfectField K] (sX : X ⟶ Spec (.of K)) [LocallyOfFiniteType sX] [QuasiCompact sX]
    (E : OrderedDivisor X) (hE : E.IsSNC sX) :
    (disjoiningSequence X E).IsSmooth sX ∧
      (disjoiningSequence X E).CentersHaveSNCWith sX E.support := by
  obtain ⟨s, E⟩ := E
  match s, E, hE with
  | 0, E, _ => exact ⟨trivial, trivial⟩
  | 1, E, _ => exact ⟨trivial, trivial⟩
  | k + 2, E, hE =>
    have : LocallyOfFiniteType
        (show (disjoiningStart (X := X) ⟨k + 2, E⟩).X ⟶ Spec (.of K) from sX) :=
      ‹LocallyOfFiniteType sX›
    have : QuasiCompact (show (disjoiningStart (X := X) ⟨k + 2, E⟩).X ⟶ Spec (.of K) from sX) :=
      ‹QuasiCompact sX›
    have h := (disjoiningStart (X := X) ⟨k + 2, E⟩).sequence_isSmooth_and_centersHaveSNCWith
      (k + 1) sX (isSNCFamily_disjoiningStart hE)
      (exists_notMem_support_disjoiningStart_Es _) (by change 0 + (k + 1) ≤ k + 2; omega)
    have hU : ⋃ i, ((Sum.elim (disjoiningStart (X := X) ⟨k + 2, E⟩).Es
        (disjoiningStart (X := X) ⟨k + 2, E⟩).Fs i).support :
          Set (disjoiningStart (X := X) ⟨k + 2, E⟩).X) =
        OrderedDivisor.support ⟨k + 2, E⟩ := by
      rw [Set.iUnion_sum]
      ext x
      change _ ↔ x ∈ ⋃ i, ((E i).support : Set X)
      simp only [Set.mem_union, Set.mem_iUnion, IsEmpty.exists_iff, or_false]
      exact Set.mem_iUnion.symm
    rwa [hU] at h

/-- **Kollár 3.72, the result of the disjoining sequence (read with 3.69).** Let `X` be an
equidimensional quasi-compact scheme locally of finite type over a field `K` of characteristic
`0`, `I ⊆ 𝒪_X` an ideal sheaf nonzero on every irreducible component of `X`, and
`E = (E_1, …, E_k)` an ordered divisor whose sum is a simple normal crossing divisor. Let
`π : X' → X` be the end of the disjoining sequence of `(X, E)` and `E_{X'}` its ordered divisor.
Then `(X', π^*I, E_{X'})` is a triple; in particular the entry `E^0` of `E_{X'}` is smooth. -/
@[mmp "lem_kr3c_disjoining_sequence_result"]
theorem isTriple_disjoiningSequence {K : Type u} [Field K] [CharZero K]
    (sX : X ⟶ Spec (.of K)) [LocallyOfFiniteType sX] [QuasiCompact sX] (hX : Equidimensional X)
    (I : X.IdealSheafData) (hI : IsNonzeroAtGenericPoints I) (E : OrderedDivisor X)
    (hE : E.IsSNC sX) :
    IsTriple ((disjoiningSequence X E).toBase ≫ sX) (I.comap (disjoiningSequence X E).toBase)
      (disjoiningDivisor X E) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have hsm : IsSmoothScheme sX := IsSNCFamily.isSmoothScheme (D := E.E) hE
  obtain ⟨s, E⟩ := E
  match s, E, hE with
  | 0, E, hE =>
    change IsTriple (𝟙 X ≫ sX) (I.comap (𝟙 X)) (OrderedDivisor.empty X)
    rw [Category.id_comp, Scheme.IdealSheafData.comap_id]
    have h0 : (Fin.elim0 : Fin 0 → X.IdealSheafData) = E ∘ Fin.elim0 := funext fun i => i.elim0
    exact ⟨inferInstance, hsm, inferInstance, inferInstance, hX, hI, fun i => i.elim0,
      (congrArg (IsSNCFamily sX) h0).mpr (IsSNCFamily.comp hE _ fun i => i.elim0)⟩
  | 1, E, hE =>
    change IsTriple (𝟙 X ≫ sX) (I.comap (𝟙 X)) ⟨1, E⟩
    rw [Category.id_comp, Scheme.IdealSheafData.comap_id]
    exact ⟨inferInstance, hsm, inferInstance, inferInstance, hX, hI, fun i =>
      ⟨(hE.1 i).1, isEffectiveCartierDivisor_of_stalk_eq_span_parameter _
        (IsSNCFamily.exists_stalk_eq_span_parameter hE i)⟩, hE⟩
  | k + 2, E, hE =>
    have : LocallyOfFiniteType
        (show (disjoiningStart (X := X) ⟨k + 2, E⟩).X ⟶ Spec (.of K) from sX) :=
      ‹LocallyOfFiniteType sX›
    have : QuasiCompact (show (disjoiningStart (X := X) ⟨k + 2, E⟩).X ⟶ Spec (.of K) from sX) :=
      ‹QuasiCompact sX›
    exact (disjoiningStart (X := X) ⟨k + 2, E⟩).isTriple_sequence (k + 1) sX I hX hI
      (isSNCFamily_disjoiningStart hE)
      (exists_notMem_support_disjoiningStart_Es _) (by change 0 + (k + 1) + 1 = k + 2; omega)

end Disjoining

end MMP.Resolution
