/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Resolution.SNCPullback

/-!
# Restricting a simple normal crossing divisor to a subscheme having snc with it

Let `k` be a field of characteristic zero, `X` a smooth scheme of finite type over `k`,
`E = ∑ᵢ E^i` a simple normal crossing divisor on `X` and `Z ⊆ X` a closed subscheme having simple
normal crossings with `E`. If no `E^i` contains an irreducible component of `Z`, then the
restriction `E|_Z = ∑ᵢ (E^i ∩ Z)`, with scheme-theoretic intersections, is a simple normal
crossing divisor on `Z`.

Let `y ∈ Z`, and let `z_1, …, z_n` be local coordinates at `y` with `E^i = (z_{c(i)} = 0)` for
the `E^i` through `y` and `Z = (z_j = 0 : j ∈ J)` near `y`. Then
`𝒪_{Z,y} = 𝒪_{X,y} / (z_j : j ∈ J)` and the images of the `z_m`, `m ∉ J`, are local coordinates
at `y` on `Z`. If `c(i) ∈ J` for some `E^i ∋ y`, then the stalk of `E^i` at `y` lies in that of
`Z`, so the generic point of any irreducible component `W` of `Z` through `y`, a generization of
`y` lying on `Z`, lies on `E^i`, and `W ⊆ E^i`, which is excluded. Hence `c(i) ∉ J`, and
`E^i ∩ Z = (z̄_{c(i)} = 0)` near `y`. Each `E^i ∩ Z` is then cut out near each of its points by
one member of a regular system of parameters, so it is reduced, of pure codimension one and smooth
over `k`.

## Main results

* `MMP.Resolution.exists_mem_componentsOf`: every point of a subset lies on one of its
  irreducible components.
* `MMP.Resolution.exists_mem_componentsOf_subset_support_of_stalk_le`: if the stalk of `I` at
  a point `x` of `T` lies in that of `T`, some irreducible component of `T` through `x` lies in
  the support of `I`.
* `MMP.Mori.IsRegularSystemOfParameters.map_ringEquiv`: regular systems of parameters
  are transported along ring isomorphisms.
* `MMP.Resolution.exists_coordinates_comap_subschemeι_of_hasSNCWith`: local coordinates on `Z`
  adapted to the `E^i ∩ Z`.
* `MMP.Resolution.isSNCFamily_comap_subschemeι_of_hasSNCWith`: `E|_Z` is a simple normal
  crossing divisor on `Z`.

## Implementation notes

The source assumes that `Z` does not lie in the support of `E`; read as `Z ⊄ Supp E`, this is
false for disconnected `Z` (`X = 𝔸²`, `E = (x = 0)`, `Z = {(0,0), (1,0)}`: `E ∩ Z` is a whole
component of `Z`). The hypothesis used instead is that no `E^i` contains an irreducible
component of the support of `Z`.

The statement is proved over any perfect field. Neither the smoothness of `X` nor the hypothesis
that `E` is an snc divisor is used: the local coordinates at the points of `Z` come with
`MMP.Resolution.HasSNCWith`. Both are kept so that the statement is the source's.

## References

* [J. Kollár, *Lectures on resolution of singularities*, 3.24]
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Resolution

/-! ### Irreducible components of a subset -/

/-- Every point of a subset `D` of a topological space lies on an irreducible component of
`D`. -/
theorem exists_mem_componentsOf {T : Type*} [TopologicalSpace T] {D : Set T} {x : T}
    (hx : x ∈ D) : ∃ W ∈ componentsOf D, x ∈ W := by
  obtain ⟨m, hxm, hm⟩ := zorn_subset_nonempty {t : Set T | IsPreirreducible t ∧ t ⊆ D}
    (fun c hc hcc _ => ⟨⋃₀ c, ⟨fun u v hu hv ⟨y, hy, hyu⟩ ⟨x, hx, hxv⟩ => by
        obtain ⟨p, hpc, hyp⟩ := Set.mem_sUnion.1 hy
        obtain ⟨q, hqc, hxq⟩ := Set.mem_sUnion.1 hx
        rcases hcc.total hpc hqc with hpq | hqp
        · obtain ⟨w, hwq, hwuv⟩ := (hc hqc).1 u v hu hv ⟨y, hpq hyp, hyu⟩ ⟨x, hxq, hxv⟩
          exact ⟨w, Set.mem_sUnion_of_mem hwq hqc, hwuv⟩
        · obtain ⟨w, hwp, hwuv⟩ := (hc hpc).1 u v hu hv ⟨y, hyp, hyu⟩ ⟨x, hqp hxq, hxv⟩
          exact ⟨w, Set.mem_sUnion_of_mem hwp hpc, hwuv⟩,
      Set.sUnion_subset fun t ht => (hc ht).2⟩, fun _ h => Set.subset_sUnion_of_mem h⟩)
    {x} ⟨isPreirreducible_singleton, Set.singleton_subset_iff.2 hx⟩
  have hxm' : x ∈ m := hxm rfl
  refine ⟨m, ?_, hxm'⟩
  change Maximal (fun W' : Set T => IsIrreducible W' ∧ W' ⊆ D) m
  exact ⟨⟨⟨⟨x, hxm'⟩, hm.prop.1⟩, hm.prop.2⟩, fun W hW hmW => hm.2 ⟨hW.1.2, hW.2⟩ hmW⟩

section Scheme

variable {X : Scheme.{u}}

/-- **Containment of stalks at a point spreads to a component.** Let `I`, `T` be ideal sheaves on
a scheme `X` and `x` a point of `T`. If the stalk of `I` at `x` lies in that of `T`, then some
irreducible component of (the support of) `T` through `x` lies in the support of `I`: its
generic point is a generization of `x` lying on `T`, hence on `I`. -/
theorem exists_mem_componentsOf_subset_support_of_stalk_le (I T : X.IdealSheafData) {x : X}
    (hx : x ∈ T.support) (hIT : IdealSheafData.stalk I x ≤ IdealSheafData.stalk T x) :
    ∃ W ∈ componentsOf (T.support : Set X), x ∈ W ∧ W ⊆ I.support := by
  obtain ⟨W, hW, hxW⟩ := exists_mem_componentsOf (D := (T.support : Set X)) hx
  refine ⟨W, hW, hxW, ?_⟩
  have hW' : Maximal (fun W' : Set X => IsIrreducible W' ∧ W' ⊆ T.support) W := hW
  have hirr : IsIrreducible W := hW'.prop.1
  have hgen : IsGenericPoint hirr.genericPoint (closure W) :=
    hirr.isGenericPoint_genericPoint_closure
  have hηx : hirr.genericPoint ⤳ x := hgen.specializes (subset_closure hxW)
  have hηI : hirr.genericPoint ∈ I.support := by
    rw [mem_support_iff_stalk_le_primeOfSpecializes I hηx]
    exact hIT.trans ((mem_support_iff_stalk_le_primeOfSpecializes T hηx).1
      (closure_minimal hW'.prop.2 T.support.isClosed hgen.mem))
  calc W ⊆ closure W := subset_closure
    _ = closure {hirr.genericPoint} := hgen.symm
    _ ⊆ I.support := closure_minimal (Set.singleton_subset_iff.2 hηI) I.support.isClosed

end Scheme

/-! ### Local coordinates on the subscheme -/

/-- A regular system of parameters is carried to a regular system of parameters by a ring
isomorphism. -/
theorem _root_.MMP.Mori.IsRegularSystemOfParameters.map_ringEquiv {A B : Type*} [CommRing A]
    [CommRing B] [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) {n : ℕ} {w : Fin n → A}
    (hw : IsRegularSystemOfParameters w) : IsRegularSystemOfParameters fun j => e (w j) := by
  refine ⟨?_, (ringKrullDim_eq_of_ringEquiv e).symm.trans hw.2⟩
  have h : Ideal.span (Set.range fun j => e (w j)) = (Ideal.span (Set.range w)).map e := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  rw [h, hw.1]
  exact map_maximalIdeal_of_surjective (e : A →+* B) e.surjective

variable {X : Scheme.{u}}

/-- **Local coordinates on a subscheme having snc with a divisor.** Let `Z ⊆ X` be a closed
subscheme having simple normal crossings with `E = ∑ᵢ E^i`, no `E^i` containing an irreducible
component of `Z`. Then at every point `y ∈ Z` there are local coordinates `w_1, …, w_m` of `Z` at
`y` and an injective map `c'` from the `E^i ∩ Z` through `y` to `{1, …, m}` with
`E^i ∩ Z = (w_{c'(i)} = 0)` near `y`. -/
theorem exists_coordinates_comap_subschemeι_of_hasSNCWith [IsLocallyNoetherian X] {Λ : Type*}
    {E : Λ → X.IdealSheafData} {Z : X.IdealSheafData} (hZ : HasSNCWith E Z)
    (hcomp : ∀ i, ∀ W ∈ componentsOf (Z.support : Set X), ¬ W ⊆ (E i).support)
    (y : Z.subscheme) :
    ∃ (m : ℕ) (w : Fin m → Z.subscheme.presheaf.stalk y)
      (c' : {i // y ∈ ((E i).comap Z.subschemeι).support} → Fin m),
      IsRegularSystemOfParameters w ∧
        (∀ i, IdealSheafData.stalk ((E i.1).comap Z.subschemeι) y = Ideal.span {w (c' i)}) ∧
        Function.Injective c' := by
  classical
  have hx : Z.subschemeι y ∈ (Z.support : Set X) := by
    rw [← Z.range_subschemeι]
    exact ⟨y, rfl⟩
  obtain ⟨n, z, c, J, hz, hE, hc, hZx⟩ := hZ _ hx
  have := isRegularLocalRing_of_isRegularSystemOfParameters hz
  obtain ⟨hreg, -, hq⟩ := MMP.Flips.ResolutionInputs.isRegularSystemOfParameters_quotient_image hz J
  let e : (X.presheaf.stalk (Z.subschemeι y) ⧸ Ideal.span (z '' (J : Set (Fin n)))) ≃+*
      Z.subscheme.presheaf.stalk y :=
    (Ideal.quotEquivOfEq hZx.symm).trans (MMP.Flips.ResolutionInputs.stalkQuotientEquiv Z y)
  have he : ∀ a, e (Ideal.Quotient.mk _ a) = (Z.subschemeι.stalkMap y).hom a := fun a => rfl
  have hmem : ∀ i : {i // y ∈ ((E i).comap Z.subschemeι).support},
      Z.subschemeι y ∈ (E i.1).support := fun i => (mem_support_comap_iff _ _ y).1 i.2
  have hnot : ∀ i : {i // y ∈ ((E i).comap Z.subschemeι).support}, c ⟨i.1, hmem i⟩ ∈ Jᶜ := by
    intro i
    refine Finset.mem_compl.2 fun hJ => ?_
    obtain ⟨W, hW, -, hWE⟩ := exists_mem_componentsOf_subset_support_of_stalk_le (E i.1) Z hx (by
      rw [hE ⟨i.1, hmem i⟩, hZx]
      exact Ideal.span_mono (Set.singleton_subset_iff.2 ⟨_, hJ, rfl⟩))
    exact hcomp i.1 W hW hWE
  let o := Jᶜ.orderIsoOfFin rfl
  refine ⟨Jᶜ.card, fun j => e (Ideal.Quotient.mk _ (z (Jᶜ.orderEmbOfFin rfl j))),
    fun i => o.symm ⟨c ⟨i.1, hmem i⟩, hnot i⟩, hq.map_ringEquiv e, fun i => ?_, ?_⟩
  · dsimp only
    rw [stalk_comap, hE ⟨i.1, hmem i⟩, Ideal.map_span, Set.image_singleton, he,
      ← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]
  · intro i j hij
    exact Subtype.ext (Subtype.mk.inj (hc (congrArg Subtype.val (o.symm.injective hij))))

/-- **Kollár Def. 3.24, corrected.** Let `k` be a perfect field (for instance of characteristic
zero), `X` a scheme smooth and locally of finite type over `k`, `E = ∑ᵢ E^i` a simple normal
crossing divisor on `X` and `Z ⊆ X` a closed subscheme having simple normal crossings with `E`.
If no `E^i` contains an irreducible component of `Z`, then the restriction
`E|_Z = ∑ᵢ (E^i ∩ Z)` (scheme-theoretic intersections, the inverse images of the `E^i` along
`Z ↪ X`) is a simple normal crossing divisor on `Z`. -/
theorem isSNCFamily_comap_subschemeι_of_hasSNCWith {k : Type u} [Field k] [PerfectField k]
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (_hX : IsSmoothScheme sX) {Λ : Type*}
    {E : Λ → X.IdealSheafData} (_hE : IsSNCFamily sX E) {Z : X.IdealSheafData}
    (hZ : HasSNCWith E Z)
    (hcomp : ∀ i, ∀ W ∈ componentsOf (Z.support : Set X), ¬ W ⊆ (E i).support) :
    IsSNCFamily (Z.subschemeι ≫ sX) fun i => (E i).comap Z.subschemeι := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsLocallyNoetherian Z.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (Z.subschemeι ≫ sX)
  have hcoord := exists_coordinates_comap_subschemeι_of_hasSNCWith hZ hcomp
  have hD : ∀ i, ∀ y ∈ ((E i).comap Z.subschemeι).support, ∃ (m : ℕ)
      (w : Fin m → Z.subscheme.presheaf.stalk y) (j : Fin m), IsRegularSystemOfParameters w ∧
        IdealSheafData.stalk ((E i).comap Z.subschemeι) y = Ideal.span {w j} := by
    intro i y hy
    obtain ⟨n, z, c, hz, hc, -⟩ := hcoord y
    exact ⟨n, z, c ⟨i, hy⟩, hz, hc ⟨i, hy⟩⟩
  exact ⟨fun i => ⟨isReduced_subscheme_of_stalk_eq_span_parameter _ (hD i),
    isPureCodimOne_support_of_stalk_eq_span_parameter _ (hD i),
    isSmoothScheme_subscheme_of_stalk_eq_span_parameter _ _ (hD i)⟩, hcoord⟩

/-- **Restriction of an snc divisor to a centre** (Kollár Def. 3.24, corrected). Let `X` be smooth
of finite type over a perfect field `k`, `E = ∑ᵢ Eⁱ` a simple normal crossing divisor on `X` and
`Z ⊆ X` a closed subscheme having simple normal crossings with `E`, no `Eⁱ` containing an
irreducible component of `Z`. Then `Z` is smooth over `k` and `E|_Z = ∑ᵢ (Eⁱ ∩ Z)` is a simple
normal crossing divisor on `Z`. -/
@[mmp "lem_kr3b_snc_restriction"]
theorem isSmoothScheme_and_isSNCFamily_comap_subschemeι {k : Type u} [Field k] [PerfectField k]
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (hX : IsSmoothScheme sX) {Λ : Type*}
    {E : Λ → X.IdealSheafData} (hE : IsSNCFamily sX E) {Z : X.IdealSheafData}
    (hZ : HasSNCWith E Z)
    (hcomp : ∀ i, ∀ W ∈ componentsOf (Z.support : Set X), ¬ W ⊆ (E i).support) :
    IsSmoothScheme (Z.subschemeι ≫ sX) ∧
      IsSNCFamily (Z.subschemeι ≫ sX) fun i => (E i).comap Z.subschemeι :=
  ⟨isSmoothScheme_subscheme_of_hasSNCWith sX hX hE hZ,
    isSNCFamily_comap_subschemeι_of_hasSNCWith sX hX hE hZ hcomp⟩

end MMP.Resolution
