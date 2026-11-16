/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Resolution.BlowupSequence
public import MMP.AlgebraicGeometry.Resolution.OrderReduction.RegularStalkComponents
public import MMP.AlgebraicGeometry.Morphisms.Smooth.RegularParameters
public import MMP.AlgebraicGeometry.Morphisms.Smooth.SmoothFlagParameters
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CartierDescent.AffineIdealSheaf
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.StalkPrimes
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormulaMultiplicities.MultiplicityOneSmoothness
public import StacksFrontier.AlgebraicGeometry.Blowup.FiniteOverLocalDimensionOne
public import StacksFrontier.RingTheory.MvPolynomial.VariablesRegularBaseChange
public import StacksFrontier.RingTheory.MvPolynomial.RegularRing
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.ClosedComposition
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.FlatBaseChangeFibre
public import StacksFrontier.RingTheory.RegularLocalRing.Basic
public import StacksFrontier.RingTheory.RegularLocalRing.RegularSequenceQuotient
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CartierDescent.StalkBaseChange
public import MMP.AlgebraicGeometry.Resolution.Blowup.RegularSequenceCharts

/-!
# The total transform of an snc divisor under one blow-up

Let `X` be a smooth scheme of finite type over a field `k` of characteristic `0`, `D ⊆ X` a divisor
with simple normal crossings and `Z ⊆ X` a closed subscheme having simple normal crossings with
the sum of the irreducible components of `D`. Let `π : X' = B_ZX → X` be the blow-up. Then the
total transform `D' = π⁻¹(D ∖ Z)‾ ∪ π⁻¹(Z)` is a divisor with simple normal crossings on `X'`.

Simple normal crossings are checked point by point. A closed subset `T` of a scheme `Y` is snc at
`y` if, for some regular system of parameters `w_1, …, w_n` of `𝒪_{Y,y}`, the inverse image of `T`
in `Spec 𝒪_{Y,y}` is a union of coordinate hyperplanes `(w_c = 0)`. On a quasi-compact scheme
locally of finite type over a perfect field, a closed subset which is snc at every point is a
divisor with simple normal crossings: the ideal of an irreducible component `V ∋ y` has stalk at
`y` the prime of the generic point of `V`, which is one of the `(w_c)`.

Let `x' ∈ X'` and `x = π(x')`. If `x ∉ Z`, then `π` is an isomorphism near `x'` and `D' = π⁻¹(D)`
near `x'`. If `x ∈ Z`, choose local coordinates `z_1, …, z_n` at `x` with `D = ⋃_{c ∈ C} (z_c = 0)`
and `Z = (z_j = 0 : j ∈ J)` near `x`. After the flat base change to `Spec 𝒪_{X,x}`, the point
`x'` lies on a chart `𝒪_{X,x}[T_l : l ∈ J, l ≠ m]/(z_l - T_l z_m)` of the blow-up of the regular
sequence `(z_j)_{j ∈ J}`. In the local ring `R` of the chart at `x'`, the elements `z_m`, the
`z_j` for `j ∉ J` and the `T_l` vanishing at `x'` are part of a regular system of parameters,
while the other `T_l` are units. On `Spec R`, `π⁻¹(Z) = (z_m = 0)`, and the closure of
`π⁻¹(D ∖ Z)` is the union of the hyperplanes `(z_c = 0)`, `c ∉ J`, and `(T_c = 0)`, `c ∈ J`
with `T_c(x') = 0`.

## Main definitions

* `MMP.Resolution.IsSNCAt`: a closed subset is a simple normal crossing divisor at a point.

## Main results

* `MMP.Resolution.isSNCClosedSubset_of_forall_isSNCAt`: a closed subset which is snc at every
  point is a divisor with simple normal crossings.
* `MMP.Resolution.exists_chart_coordinates`: local coordinates on the blow-up at a point over the
  centre, adapted to the coordinates of the centre.
* `MMP.Resolution.isSNCAt_totalTransformStep`: the total transform is snc at every point.
* `MMP.Resolution.isSNCClosedSubset_totalTransformStep`: the total transform is a divisor with
  simple normal crossings.

## Implementation notes

The source reduces to closed points of `X'` and counts dimensions there. Here every point is
treated directly: the regular system of parameters at a point of a chart is produced from the
localized polynomial ring `𝒪_{X,x}[T_l]_{Q}`, in which the parameters of `𝒪_{X,x}` followed by
the variables vanishing at the point form a weakly regular sequence with regular quotient, and
the chart is the quotient of this ring by members `z_l - T_l z_m` of a regular system of
parameters. Smoothness of `X'` is not used; the regularity of its local rings is a consequence.

Characteristic `0` enters only through the perfectness of `k` (smoothness of the components is
regularity of their local rings).

## References

* [J. Kollár, *Lectures on resolution of singularities*, 3.24–3.25]
* [Stacks Project, Tag 0805](https://stacks.math.columbia.edu/tag/0805)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace IsLocalRing MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Resolution

/-! ### Regular systems of parameters -/

section RSOP

variable {R S : Type*} [CommRing R] [CommRing S]

/-- A regular system of parameters is carried to one by a ring isomorphism. -/
theorem isRegularSystemOfParameters_map_ringEquiv [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S)
    {n : ℕ} {w : Fin n → R} (hw : IsRegularSystemOfParameters w) :
    IsRegularSystemOfParameters (fun i => e (w i)) := by
  refine ⟨?_, ?_⟩
  · have h1 : Ideal.span (Set.range fun i => e (w i)) =
        (Ideal.span (Set.range w)).map (e : R →+* S) := by
      rw [Ideal.map_span, ← Set.range_comp]
      rfl
    rw [h1, hw.1]
    exact map_maximalIdeal_of_surjective (e : R →+* S) e.surjective
  · rw [← ringKrullDim_eq_of_ringEquiv e, hw.2]

variable [IsLocalRing R] [IsNoetherianRing R]

private theorem quotient_span_singleton_of_isRegularSystemOfParameters {m : ℕ}
    {w : Fin m → R} (hw : IsRegularSystemOfParameters w) (j : Fin m) :
    IsRegularLocalRing (R ⧸ Ideal.span {w j}) ∧
      ringKrullDim (R ⧸ Ideal.span {w j}) = (m - 1 : ℕ) := by
  have := isRegularLocalRing_of_isRegularSystemOfParameters hw
  obtain ⟨hreg, hdim, -⟩ :=
    MMP.Flips.ResolutionInputs.isRegularSystemOfParameters_quotient_image hw {j}
  have hs : w '' ((({j} : Finset (Fin m))) : Set (Fin m)) = {w j} := by simp
  rw [hs] at hreg hdim
  exact ⟨hreg, by simpa using hdim⟩

/-- A member of a regular system of parameters generates a prime ideal. -/
private theorem isPrime_span_singleton_of_isRegularSystemOfParameters {m : ℕ} {w : Fin m → R}
    (hw : IsRegularSystemOfParameters w) (j : Fin m) : (Ideal.span {w j}).IsPrime := by
  have := (quotient_span_singleton_of_isRegularSystemOfParameters hw j).1
  have := IsRegularLocalRing.isDomain (R ⧸ Ideal.span {w j})
  exact (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance

/-- A member of a regular system of parameters is not a multiple of another member. -/
private theorem notMem_span_singleton_of_isRegularSystemOfParameters {m : ℕ} {w : Fin m → R}
    (hw : IsRegularSystemOfParameters w) {i j : Fin m} (hij : i ≠ j) :
    w j ∉ Ideal.span {w i} := by
  classical
  intro hmem
  have := isRegularLocalRing_of_isRegularSystemOfParameters hw
  set s : Set R := w '' ({j}ᶜ : Set (Fin m)) with hs
  have hspan : Ideal.span s = maximalIdeal R := by
    rw [← hw.1]
    refine le_antisymm (Ideal.span_mono (Set.image_subset_range _ _)) (Ideal.span_le.2 ?_)
    rintro _ ⟨l, rfl⟩
    by_cases hl : l = j
    · subst hl
      exact Ideal.span_mono (Set.singleton_subset_iff.2 (show w i ∈ s from ⟨i, hij, rfl⟩)) hmem
    · exact Ideal.subset_span ⟨l, hl, rfl⟩
  have hfin : s.Finite := Set.toFinite _
  have hle := Submodule.spanFinrank_span_le_ncard_of_finite (R := R) hfin
  rw [show Submodule.span R s = maximalIdeal R from hspan] at hle
  have hcard : s.ncard ≤ m - 1 := by
    rw [hs]
    refine (Set.ncard_image_le (Set.toFinite _)).trans ?_
    rw [Set.ncard_eq_toFinset_card']
    simp [Finset.card_compl]
  have hrank := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
  rw [hw.2] at hrank
  have : (maximalIdeal R).spanFinrank = m := by exact_mod_cast hrank
  have := j.2
  omega

end RSOP

/-! ### Simple normal crossings at a point -/

section Local

variable {Y : Scheme.{u}}

/-- The inverse image of the support of an ideal sheaf in the spectrum of a local ring of `Y` is
the zero locus of the stalk of the ideal sheaf. -/
theorem preimage_fromSpecStalk_support (K : Y.IdealSheafData) (y : Y) :
    Y.fromSpecStalk y ⁻¹' (K.support : Set Y) =
      PrimeSpectrum.zeroLocus (IdealSheafData.stalk K y : Set (Y.presheaf.stalk y)) := by
  have h1 : K.comap (Y.fromSpecStalk y) = Scheme.IdealSheafData.ofIdealTop
      (Ideal.map (Scheme.ΓSpecIso (Y.presheaf.stalk y)).inv.hom (IdealSheafData.stalk K y)) := by
    rw [← AlgebraicGeometry.ideal_comap_fromSpecStalk K y]
    exact (Stacks.ResolutionOfSurfaces.CartierDescent.ofIdealTop_ideal_top _).symm
  have h2 : ((K.comap (Y.fromSpecStalk y)).support : Set _) =
      Y.fromSpecStalk y ⁻¹' (K.support : Set Y) := by
    rw [Scheme.IdealSheafData.support_comap]; rfl
  rw [← h2, h1, Scheme.IdealSheafData.coe_support_ofIdealTop, AlgebraicGeometry.Spec_zeroLocus,
    ← Ideal.coe_comap, Ideal.comap_map_of_bijective _ (ConcreteCategory.bijective_of_isIso _)]

/-- A subset `T` of a scheme `Y` is *a simple normal crossing divisor at* `y ∈ Y`: there are local
coordinates `w_1, …, w_n` at `y` (a regular system of parameters of `𝒪_{Y,y}`) and indices
`C ⊆ {1, …, n}` such that, on `Spec 𝒪_{Y,y}`, the inverse image of `T` is
`⋃_{c ∈ C} (w_c = 0)`. -/
def IsSNCAt (T : Set Y) (y : Y) : Prop :=
  ∃ (n : ℕ) (w : Fin n → Y.presheaf.stalk y) (C : Finset (Fin n)),
    IsRegularSystemOfParameters w ∧
      Y.fromSpecStalk y ⁻¹' T = ⋃ c ∈ C, PrimeSpectrum.zeroLocus {w c}

end Local

/-! ### Components cut out by one parameter -/

section Parameter

variable {Y : Scheme.{u}}

private theorem isRegularLocalRing_stalk_subscheme_of_stalk_eq_span [IsLocallyNoetherian Y]
    (D : Y.IdealSheafData)
    (hD : ∀ y ∈ D.support, ∃ (m : ℕ) (w : Fin m → Y.presheaf.stalk y) (j : Fin m),
      IsRegularSystemOfParameters w ∧ IdealSheafData.stalk D y = Ideal.span {w j})
    (z : D.subscheme) : IsRegularLocalRing (D.subscheme.presheaf.stalk z) := by
  have hz : D.subschemeι z ∈ D.support := by
    rw [← SetLike.mem_coe, ← D.range_subschemeι]
    exact ⟨z, rfl⟩
  obtain ⟨m, w, j, hw, hy'⟩ := hD _ hz
  apply isRegularLocalRing_stalk_subscheme_of_isRegularLocalRing_quotient
  rw [hy']
  exact (quotient_span_singleton_of_isRegularSystemOfParameters hw j).1

private theorem isPureCodimOne_support_of_stalk_eq_span [IsLocallyNoetherian Y]
    (D : Y.IdealSheafData)
    (hD : ∀ y ∈ D.support, ∃ (m : ℕ) (w : Fin m → Y.presheaf.stalk y) (j : Fin m),
      IsRegularSystemOfParameters w ∧ IdealSheafData.stalk D y = Ideal.span {w j}) :
    IsPureCodimOne D.support := by
  intro W hW
  set e := irreducibleSetEquivPoints (α := Y)
  have hWη : (W : Set Y) = closure {e W} := by
    conv_lhs => rw [← e.symm_apply_apply W]
    rfl
  have hηW : e W ∈ (W : Set Y) := hWη ▸ subset_closure rfl
  have hηD : e W ∈ D.support := hW.1 hηW
  obtain ⟨z, hz⟩ : ∃ z, D.subschemeι z = e W := by
    rwa [← SetLike.mem_coe, ← D.range_subschemeι] at hηD
  have h1 : codimension W = Order.coheight (e W) := by
    change Order.coheight W = _
    rw [← Order.coheight_orderIso e W]
  rw [h1, ← hz]
  have hmax : IsMax z := by
    intro b hb
    rw [Scheme.le_iff_specializes] at hb ⊢
    have hcl := D.subschemeι.isClosedEmbedding
    have hb' : D.subschemeι b ⤳ e W := hz ▸ hb.map D.subschemeι.continuous
    have hbD : D.subschemeι b ∈ D.support := by
      rw [← SetLike.mem_coe, ← D.range_subschemeι]; exact ⟨b, rfl⟩
    have hle : W ≤ e.symm (D.subschemeι b) := by
      rw [← e.le_iff_le, e.apply_symm_apply, Scheme.le_iff_specializes]
      exact hb'
    have hsub : ((e.symm (D.subschemeι b) : TopologicalSpace.IrreducibleCloseds Y) : Set Y) ⊆
        D.support := by
      change closure {D.subschemeι b} ⊆ _
      exact closure_minimal (Set.singleton_subset_iff.mpr hbD) D.support.isClosed
    have hge := hW.2 hsub hle
    rw [← e.le_iff_le, e.apply_symm_apply, Scheme.le_iff_specializes, ← hz] at hge
    exact hcl.isInducing.specializes_iff.mp hge
  have hz0 : ringKrullDim (D.subscheme.presheaf.stalk z) = 0 := by
    rw [ringKrullDim_stalk_eq_coheight, Order.coheight_eq_zero.mpr hmax]; rfl
  have hzD : D.subschemeι z ∈ D.support := hz ▸ hηD
  obtain ⟨m, w, j, hw, hy'⟩ := hD _ hzD
  obtain ⟨-, hdim⟩ := quotient_span_singleton_of_isRegularSystemOfParameters hw j
  rw [← hy', ringKrullDim_eq_of_ringEquiv (MMP.Flips.ResolutionInputs.stalkQuotientEquiv D z),
    hz0] at hdim
  have hm : m = 1 := by
    have := j.2
    have : m - 1 = 0 := by exact_mod_cast hdim.symm
    omega
  have h2 := hw.2
  rw [ringKrullDim_stalk_eq_coheight, hm] at h2
  exact_mod_cast h2

private theorem isSmoothScheme_subscheme_of_stalk_eq_span {k : Type u} [Field k]
    [PerfectField k] (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] (D : Y.IdealSheafData)
    (hD : ∀ y ∈ D.support, ∃ (m : ℕ) (w : Fin m → Y.presheaf.stalk y) (j : Fin m),
      IsRegularSystemOfParameters w ∧ IdealSheafData.stalk D y = Ideal.span {w j}) :
    IsSmoothScheme (D.subschemeι ≫ sY) := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : LocallyOfFinitePresentation (D.subschemeι ≫ sY) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := D.subschemeι ≫ sY)).mpr
      inferInstance
  rw [isSmoothScheme_iff, MMP.Flips.ResolutionInputs.smooth_iff_forall_isRegularLocalRing_stalk]
  exact isRegularLocalRing_stalk_subscheme_of_stalk_eq_span D hD

end Parameter

/-! ### From simple normal crossings at every point to an snc divisor -/

section Global

variable {Y : Scheme.{u}}

/-- At a point `y` where `T` is snc with coordinates `w` and indices `C`, the stalk at `y` of the
ideal of an irreducible component `V ∋ y` of the closed set `T` is `(w_c)` for some `c ∈ C`, the
prime of `𝒪_{Y,y}` corresponding to the generic point of `V`. -/
private theorem exists_stalk_componentsFamily_eq [IsLocallyNoetherian Y] {T : Set Y}
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
    rw [Scheme.range_fromSpecStalk]; exact hξy
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
    rw [Set.mem_preimage, hq]; exact hξT
  rw [hTy] at hqT
  obtain ⟨c, hc, hwc⟩ := Set.mem_iUnion₂.1 hqT
  replace hwc : w c ∈ q.asIdeal := (PrimeSpectrum.mem_zeroLocus _ _).1 hwc (Set.mem_singleton _)
  let p' : PrimeSpectrum (Y.presheaf.stalk y) :=
    ⟨Ideal.span {w c}, isPrime_span_singleton_of_isRegularSystemOfParameters hw c⟩
  have hp'q : p' ≤ q := (Ideal.span_singleton_le_iff_mem _).2 hwc
  have hp'T : p' ∈ Y.fromSpecStalk y ⁻¹' T := by
    rw [hTy]
    refine Set.mem_biUnion hc ?_
    rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff]
    exact Ideal.subset_span rfl
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

private theorem coe_support_componentsFamily {D : Set Y} (hD : IsClosed D) (V : componentsOf D) :
    ((componentsFamily D V).support : Set Y) = (V : Set Y) := by
  unfold componentsFamily
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_closure,
    (Aux.isClosed_of_mem_componentsOf hD V.2).closure_eq]

/-- **Simple normal crossings at every point give an snc divisor.** Let `Y` be a quasi-compact
scheme locally of finite type over a perfect field `k` and `T ⊆ Y` a closed subset which is a
simple normal crossing divisor at every point (`MMP.Resolution.IsSNCAt`). Then `T` is a divisor
with simple normal crossings: it has finitely many irreducible components, each reduced, smooth
and of pure codimension one, and they form an snc family. -/
theorem isSNCClosedSubset_of_forall_isSNCAt {k : Type u} [Field k] [PerfectField k]
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] [CompactSpace Y] {T : Set Y}
    (hT : IsClosed T) (h : ∀ y, IsSNCAt T y) : IsSNCClosedSubset sY T := by
  classical
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : IsNoetherian Y := {}
  obtain ⟨hfin, -⟩ := Aux.finite_and_cover_componentsOf hT
  have hsupp := coe_support_componentsFamily hT
  have hpar : ∀ V : componentsOf T, ∀ y ∈ (componentsFamily T V).support,
      ∃ (m : ℕ) (w : Fin m → Y.presheaf.stalk y) (j : Fin m),
        IsRegularSystemOfParameters w ∧
          IdealSheafData.stalk (componentsFamily T V) y = Ideal.span {w j} := by
    intro V y hy
    rw [← SetLike.mem_coe, hsupp] at hy
    obtain ⟨n, w, C, hw, hTy⟩ := h y
    obtain ⟨c, -, hc, -⟩ := exists_stalk_componentsFamily_eq hT hw hTy V hy
    exact ⟨n, w, c, hw, hc⟩
  have hpure : ∀ V : componentsOf T, IsPureCodimOne (componentsFamily T V).support :=
    fun V => isPureCodimOne_support_of_stalk_eq_span _ (hpar V)
  refine ⟨hT, Or.inr ⟨?_, hfin, ⟨fun V =>
    ⟨Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _,
    hpure V, isSmoothScheme_subscheme_of_stalk_eq_span sY _ (hpar V)⟩, fun y => ?_⟩⟩⟩
  · intro W hW
    have hWc : (W : Set Y) ∈ componentsOf T := by
      refine ⟨⟨W.isIrreducible, hW.1⟩, fun S hS hWS => ?_⟩
      have := hW.2 (y := ⟨closure S, hS.1.closure, isClosed_closure⟩)
        (closure_minimal hS.2 hT) (hWS.trans subset_closure)
      exact subset_closure.trans this
    refine hpure ⟨W, hWc⟩ W ⟨?_, fun W' hW' _ => ?_⟩
    · change (W : Set Y) ⊆ ((componentsFamily T ⟨W, hWc⟩).support : Set Y)
      rw [hsupp]
    · change (W' : Set Y) ⊆ ((componentsFamily T ⟨W, hWc⟩).support : Set Y) at hW'
      rw [hsupp] at hW'
      exact hW'
  · obtain ⟨n, w, C, hw, hTy⟩ := h y
    have hmem : ∀ V : {V // y ∈ (componentsFamily T V).support}, y ∈ (V.1 : Set Y) := fun V => by
      have := V.2
      rwa [← SetLike.mem_coe, hsupp] at this
    choose c _ hc q hq hqc using fun V : {V // y ∈ (componentsFamily T V).support} =>
      exists_stalk_componentsFamily_eq hT hw hTy V.1 (hmem V)
    refine ⟨n, w, c, hw, hc, fun V V' hVV' => ?_⟩
    have hqq : q V = q V' := PrimeSpectrum.ext ((hqc V).trans (by rw [hVV', hqc V']))
    apply Subtype.ext
    apply Subtype.ext
    rw [hq V, hq V', hqq]

end Global

/-! ### The divisor downstairs -/

section Downstairs

variable {X : Scheme.{u}}

/-- If the stalks at `x` of the components of a closed set `D` through `x` are the ideals `(z_c)`
of members of a family `z`, then the inverse image of `D` in `Spec 𝒪_{X,x}` is the union of the
loci `z_c = 0`. -/
private theorem preimage_fromSpecStalk_eq_of_stalk_eq [NoetherianSpace X] {D : Set X}
    (hD : IsClosed D) (x : X) {n : ℕ} (z : Fin n → X.presheaf.stalk x)
    (c : {V // x ∈ (componentsFamily D V).support} → Fin n)
    (hc : ∀ V, IdealSheafData.stalk (componentsFamily D V.1) x = Ideal.span {z (c V)})
    [Finite {V // x ∈ (componentsFamily D V).support}] :
    X.fromSpecStalk x ⁻¹' D =
      ⋃ j ∈ (Set.finite_range c).toFinset, PrimeSpectrum.zeroLocus {z j} := by
  obtain ⟨-, hcov⟩ := Aux.finite_and_cover_componentsOf hD
  have hmem : ∀ (V : componentsOf D) (p : PrimeSpectrum (X.presheaf.stalk x)),
      X.fromSpecStalk x p ∈ (V : Set X) ↔
        p ∈ PrimeSpectrum.zeroLocus (IdealSheafData.stalk (componentsFamily D V) x : Set _) := by
    intro V p
    have h := Set.ext_iff.1 (preimage_fromSpecStalk_support (componentsFamily D V) x) p
    have h2 : X.fromSpecStalk x p ∈ ((componentsFamily D V).support : Set X) ↔
        X.fromSpecStalk x p ∈ (V : Set X) := by
      rw [coe_support_componentsFamily hD]
    exact h2.symm.trans h
  refine Set.ext fun (p : PrimeSpectrum (X.presheaf.stalk x)) => ⟨fun hp => ?_, fun hp => ?_⟩
  · change X.fromSpecStalk x p ∈ D at hp
    obtain ⟨V, hV, hpV⟩ := hcov hp
    have hxV : x ∈ V := (Scheme.range_fromSpecStalk.subset ⟨p, rfl⟩ :
      X.fromSpecStalk x p ⤳ x).mem_closed (Aux.isClosed_of_mem_componentsOf hD hV) hpV
    let V' : {V // x ∈ (componentsFamily D V).support} :=
      ⟨⟨V, hV⟩, by rw [← SetLike.mem_coe, coe_support_componentsFamily hD]; exact hxV⟩
    have h1 := (hmem ⟨V, hV⟩ p).1 hpV
    rw [hc V', PrimeSpectrum.zeroLocus_span] at h1
    exact Set.mem_iUnion₂.2 ⟨c V', (Set.Finite.mem_toFinset _).2 ⟨V', rfl⟩, h1⟩
  · obtain ⟨j, hj, hp⟩ := Set.mem_iUnion₂.1 hp
    obtain ⟨V', rfl⟩ := (Set.Finite.mem_toFinset _).1 hj
    have h1 : p ∈ PrimeSpectrum.zeroLocus
        (IdealSheafData.stalk (componentsFamily D V'.1) x : Set _) := by
      rw [hc V', PrimeSpectrum.zeroLocus_span]; exact hp
    exact V'.1.2.1.2 ((hmem V'.1 p).2 h1)

/-- Local coordinates at `x` describing `D` near `x` (and `Z` near `x`, if `x ∈ Z`): a regular
system of parameters `z` of `𝒪_{X,x}` and indices `C` with `D = ⋃_{c ∈ C} (z_c = 0)` on
`Spec 𝒪_{X,x}`, and, if `x ∈ Z`, indices `J` with `I_{Z,x} = (z_j : j ∈ J)`. -/
private theorem exists_coordinates {k : Type u} [Field k] [PerfectField k]
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] [CompactSpace X]
    (hX : IsSmoothScheme sX) {D : Set X} (hD : IsSNCClosedSubset sX D) {Z : X.IdealSheafData}
    (hZ : HasSNCWith (componentsFamily D) Z) (x : X) :
    ∃ (n : ℕ) (z : Fin n → X.presheaf.stalk x) (C : Finset (Fin n)),
      IsRegularSystemOfParameters z ∧
      X.fromSpecStalk x ⁻¹' D = ⋃ c ∈ C, PrimeSpectrum.zeroLocus {z c} ∧
      (x ∈ Z.support → ∃ J : Finset (Fin n), IdealSheafData.stalk Z x = Ideal.span (z '' J)) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsNoetherian X := {}
  obtain ⟨hDc, hD'⟩ := hD
  obtain ⟨hfin, -⟩ := Aux.finite_and_cover_componentsOf hDc
  have : Finite (componentsOf D) := hfin.to_subtype
  by_cases hx : x ∈ Z.support
  · obtain ⟨n, z, c, J, hz, hc, -, hJ⟩ := hZ x hx
    exact ⟨n, z, _, hz, preimage_fromSpecStalk_eq_of_stalk_eq hDc x z c hc, fun _ => ⟨J, hJ⟩⟩
  · rcases hD' with rfl | ⟨-, -, hE⟩
    · have : LocallyOfFinitePresentation sX :=
        (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := sX)).mpr inferInstance
      have hreg := (MMP.Flips.ResolutionInputs.smooth_iff_forall_isRegularLocalRing_stalk sX).1
        ((isSmoothScheme_iff sX).1 hX) x
      obtain ⟨n, z, hz⟩ := exists_isRegularSystemOfParameters (X.presheaf.stalk x)
      refine ⟨n, z, ∅, hz, ?_, fun h => absurd h hx⟩
      rw [Set.preimage_empty]
      exact (by simp : (⋃ c ∈ (∅ : Finset (Fin n)), PrimeSpectrum.zeroLocus {z c}) = ∅).symm
    · obtain ⟨n, z, c, hz, hc, -⟩ := hE.2 x
      exact ⟨n, z, _, hz, preimage_fromSpecStalk_eq_of_stalk_eq hDc x z c hc,
        fun h => absurd h hx⟩

end Downstairs

/-! ### The local algebra of a chart -/

section ChartAlgebra

open MvPolynomial RingTheory.Sequence

/-- A weakly regular sequence in the maximal ideal of a Noetherian local ring with regular
quotient is the beginning of a regular system of parameters. -/
private theorem exists_isRegularSystemOfParameters_of_isWeaklyRegular {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] (fs : List R) (hm : ∀ f ∈ fs, f ∈ maximalIdeal R)
    (hreg : IsWeaklyRegular R fs) (hq : IsRegularLocalRing (R ⧸ Ideal.ofList fs)) :
    ∃ (N : ℕ) (w : Fin N → R) (h : fs.length ≤ N), IsRegularSystemOfParameters w ∧
      ∀ i : Fin fs.length, w (Fin.castLE h i) = fs.get i := by
  obtain ⟨-, rs, hsop, hgen, hlen, htake⟩ :=
    exists_isSystemOfParameters_append_of_isRegular_quotient hm hreg hq
  refine ⟨rs.length, rs.get, hlen, ⟨?_, hsop.2⟩, fun i => ?_⟩
  · rw [← hgen]
    congr 1
    ext x
    simp [List.mem_iff_get]
  · simp only [List.get_eq_getElem, Fin.coe_castLE]
    rw [List.getElem_of_eq htake.symm, List.getElem_take]

/-- Changing the members of a regular system of parameters by multiples of one member which is
kept gives a regular system of parameters. -/
private theorem isRegularSystemOfParameters_of_sub_mem_span {R : Type*} [CommRing R]
    [IsLocalRing R] {N : ℕ} {w w' : Fin N → R} (hw : IsRegularSystemOfParameters w) (i₀ : Fin N)
    (h₀ : w' i₀ = w i₀) (h : ∀ i, w' i - w i ∈ Ideal.span {w i₀}) :
    IsRegularSystemOfParameters w' := by
  refine ⟨le_antisymm ?_ ?_, hw.2⟩
  · rw [← hw.1, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    have h1 : w i ∈ Ideal.span (Set.range w) := Ideal.subset_span ⟨i, rfl⟩
    have h2 : w' i - w i ∈ Ideal.span (Set.range w) :=
      Ideal.span_mono (Set.singleton_subset_iff.2 (show w i₀ ∈ Set.range w from ⟨i₀, rfl⟩)) (h i)
    simpa using add_mem h2 h1
  · rw [← hw.1, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    have hi₀ : w i₀ ∈ Ideal.span (Set.range w') := h₀ ▸ Ideal.subset_span ⟨i₀, rfl⟩
    have h1 : w' i ∈ Ideal.span (Set.range w') := Ideal.subset_span ⟨i, rfl⟩
    have h2 : w' i - w i ∈ Ideal.span (Set.range w') :=
      Ideal.span_le.2 (Set.singleton_subset_iff.2 hi₀) (h i)
    simpa using sub_mem h1 h2

/-- A polynomial ring over a local ring modulo the maximal ideal of the coefficients and some
of the variables is a regular ring: it is a polynomial ring over the residue field. -/
private theorem isRegularRing_quotient_map_maximalIdeal_sup_span_X {A : Type u} [CommRing A]
    [IsLocalRing A] {ι : Type} [Finite ι] (S : Set ι) :
    IsRegularRing (MvPolynomial ι A ⧸
      (Ideal.map (C : A →+* MvPolynomial ι A) (maximalIdeal A) ⊔ Ideal.span (X '' S))) := by
  classical
  set J₀ := Ideal.map (C : A →+* MvPolynomial ι A) (maximalIdeal A) ⊔ Ideal.span (X '' S)
    with hJ₀
  let F : MvPolynomial ι A →+* MvPolynomial {l // l ∉ S} (ResidueField A) :=
    eval₂Hom (C.comp (residue A)) (fun l => if h : l ∈ S then 0 else X ⟨l, h⟩)
  have hJF : J₀ ≤ RingHom.ker F := by
    refine sup_le ?_ ?_
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      simp [F, RingHom.mem_ker, (residue_eq_zero_iff a).2 ha]
    · rw [Ideal.span_le]
      rintro _ ⟨l, hl, rfl⟩
      simp [F, RingHom.mem_ker, hl]
  let F' : MvPolynomial ι A ⧸ J₀ →+* MvPolynomial {l // l ∉ S} (ResidueField A) :=
    Ideal.Quotient.lift J₀ F fun a ha => hJF ha
  have hF' : ∀ p, F' (Ideal.Quotient.mk J₀ p) = F p := fun p => Ideal.Quotient.lift_mk _ _ _
  let g₀ : ResidueField A →+* MvPolynomial ι A ⧸ J₀ :=
    Ideal.Quotient.lift (maximalIdeal A) ((Ideal.Quotient.mk J₀).comp C) fun a ha =>
      Ideal.Quotient.eq_zero_iff_mem.2 (le_sup_left (a := Ideal.map C (maximalIdeal A))
        (Ideal.mem_map_of_mem C ha))
  have hg₀ : ∀ a, g₀ (residue A a) = Ideal.Quotient.mk J₀ (C a) := fun a =>
    Ideal.Quotient.lift_mk _ _ _
  let G : MvPolynomial {l // l ∉ S} (ResidueField A) →+* MvPolynomial ι A ⧸ J₀ :=
    eval₂Hom g₀ fun l => Ideal.Quotient.mk J₀ (X l.1)
  have hGF : G.comp F' = RingHom.id _ := by
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, hF', RingHom.id_apply]
      simp only [F, G, eval₂Hom_C, RingHom.comp_apply, hg₀]
    · intro l
      simp only [RingHom.comp_apply, hF', RingHom.id_apply]
      by_cases hl : l ∈ S
      · simp only [F, G, eval₂Hom_X', hl, dif_pos, map_zero]
        symm
        exact Ideal.Quotient.eq_zero_iff_mem.2 (le_sup_right (a := Ideal.map C (maximalIdeal A))
          (Ideal.subset_span ⟨l, hl, rfl⟩))
      · simp only [F, G, eval₂Hom_X', hl, dif_neg, not_false_eq_true]
  have hFG : F'.comp G = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro c
      obtain ⟨a, rfl⟩ := residue_surjective c
      simp only [RingHom.comp_apply, G, eval₂Hom_C, hg₀, hF', F, RingHom.id_apply]
    · intro l
      simp only [RingHom.comp_apply, G, eval₂Hom_X', hF', F, l.2, dif_neg, not_false_eq_true,
        RingHom.id_apply]
  let e := RingEquiv.ofRingHom F' G hFG hGF
  have :=
    (isRegularRing_and_iSup_projectiveDimension_eq_and_isRegularLocalRing_localization.{u, 0, u}
      (ResidueField A) {l // l ∉ S}).1
  exact IsRegularRing.of_ringEquiv e.symm

/-- In the localization of a polynomial ring over a regular local ring `A` at a prime over the
maximal ideal, a regular system of parameters of `A` followed by some of the variables is a
weakly regular sequence. -/
private theorem isWeaklyRegular_localization_mvPolynomial {A : Type u} [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] {n : ℕ} {z : Fin n → A}
    (hz : IsRegularSystemOfParameters z) {ι' : Type} {e : ℕ} (xS : Fin e → ι')
    (hxS : Function.Injective xS) (Q' : Ideal (MvPolynomial ι' A)) [Q'.IsPrime] :
    IsWeaklyRegular (Localization.AtPrime Q')
      (List.ofFn (Fin.append
        (fun j => algebraMap (MvPolynomial ι' A) (Localization.AtPrime Q') (C (z j)))
        (fun i => algebraMap (MvPolynomial ι' A) (Localization.AtPrime Q') (X (xS i))))) := by
  classical
  set P := MvPolynomial ι' A
  set L := Localization.AtPrime Q'
  have : IsRegularLocalRing A := isRegularLocalRing_of_isRegularSystemOfParameters hz
  have : Module.Flat P L := IsLocalization.flat _ Q'.primeCompl
  have : Module.Flat A L := Module.Flat.trans A P L
  have hzreg : IsWeaklyRegular A (List.ofFn z) := by
    refine ((IsRegularLocalRing.isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay
      A).1 (List.ofFn z) ?_ ?_).1.toIsWeaklyRegular
    · rw [show Ideal.ofList (List.ofFn z) = Ideal.span (Set.range z) by
        simp only [Ideal.ofList, List.mem_ofFn]; rfl, hz.1]
    · have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := A)
      rw [hz.2] at h
      simp only [List.length_ofFn]
      exact_mod_cast h.symm
  set ys : List L := List.ofFn fun j => algebraMap P L (C (z j)) with hys_def
  have hys : IsWeaklyRegular L ys := by
    have h := hzreg.of_flat (S := L)
    rw [List.map_ofFn] at h
    have hl : (⇑(algebraMap A L) ∘ z) = fun j => algebraMap P L (C (z j)) := by
      funext j
      simp only [Function.comp_apply]
      rw [IsScalarTower.algebraMap_apply A P L]; rfl
    rw [hl] at h
    exact h
  rw [List.ofFn_fin_append]
  have hker : RingHom.ker (Ideal.Quotient.mk (Ideal.ofList ys)) = Ideal.ofList ys := Ideal.mk_ker
  refine Stacks.AlgebraicGeometry.isWeaklyRegular_append_of_ker_eq
    (Ideal.Quotient.mk (Ideal.ofList ys)) Ideal.Quotient.mk_surjective hys hker ?_
  let σ := {l : ι' // l ∉ Set.range xS}
  let ε : ι' ≃ Fin e ⊕ σ :=
    (Equiv.sumCompl fun l => l ∈ Set.range xS).symm.trans
      (Equiv.sumCongr (Equiv.ofInjective xS hxS).symm (Equiv.refl _))
  have hε : ∀ j, ε.symm (Sum.inl j) = xS j := fun j => rfl
  let χ : P ≃+* MvPolynomial (Fin e ⊕ σ) A := (renameEquiv A ε).toRingEquiv
  have hχ : ∀ a, χ (C a) = C a := fun a => by
    change rename ε (C a) = C a
    exact rename_C _ _
  have h := isWeaklyRegular_quotient_ofFn_X_inl (S := L) χ C hχ (maximalIdeal A)
  have hI : Ideal.map (algebraMap P L) (Ideal.map C (maximalIdeal A)) = Ideal.ofList ys := by
    rw [hys_def, Ideal.map_map, ← hz.1, Ideal.map_span, ← Set.range_comp]
    simp only [Ideal.ofList, List.mem_ofFn]
    rfl
  rw [hI] at h
  have hl : (fun j => (Ideal.Quotient.mk (Ideal.ofList ys))
      (algebraMap P L (χ.symm (X (Sum.inl j))))) =
      ⇑(Ideal.Quotient.mk _) ∘ fun i => algebraMap P L (X (xS i)) := by
    funext j
    simp only [Function.comp_apply]
    congr 2
    change rename ε.symm (X (Sum.inl j)) = X (xS j)
    rw [rename_X, hε]
  rw [hl] at h
  rw [List.map_ofFn]
  exact h

/-- **Parameters of a localized polynomial ring.** Let `A` be a Noetherian local ring with a
regular system of parameters `z`, and `Q'` a prime of `A[T_l]` over the maximal ideal of `A`
containing some of the variables `T_{l_1}, …, T_{l_e}`. Then `z` followed by these variables is
the beginning of a regular system of parameters of `A[T_l]_{Q'}`. -/
private theorem exists_isRegularSystemOfParameters_localization_mvPolynomial {A : Type u}
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {n : ℕ} {z : Fin n → A}
    (hz : IsRegularSystemOfParameters z) {ι' : Type} [Finite ι'] {e : ℕ}
    (xS : Fin e → ι') (hxS : Function.Injective xS) (Q' : Ideal (MvPolynomial ι' A)) [Q'.IsPrime]
    (hQA : ∀ a ∈ maximalIdeal A, C a ∈ Q') (hQX : ∀ i, X (xS i) ∈ Q') :
    ∃ (N : ℕ) (w : Fin N → Localization.AtPrime Q') (h : n + e ≤ N),
      IsRegularSystemOfParameters w ∧
      (∀ j, w (Fin.castLE h (Fin.castAdd e j)) =
        algebraMap (MvPolynomial ι' A) (Localization.AtPrime Q') (C (z j))) ∧
      (∀ i, w (Fin.castLE h (Fin.natAdd n i)) =
        algebraMap (MvPolynomial ι' A) (Localization.AtPrime Q') (X (xS i))) := by
  classical
  set P := MvPolynomial ι' A
  set L := Localization.AtPrime Q'
  set v : Fin (n + e) → L := Fin.append (fun j => algebraMap P L (C (z j)))
    (fun i => algebraMap P L (X (xS i))) with hv
  set fs := List.ofFn v with hfs
  have hzm : ∀ j, z j ∈ maximalIdeal A := fun j => hz.1 ▸ Ideal.subset_span ⟨j, rfl⟩
  have hm : ∀ f ∈ fs, f ∈ maximalIdeal L := by
    intro f hf
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hf
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [hv, Fin.append_left]
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff L Q' _).2 (hQA _ (hzm j))
    · simp only [hv, Fin.append_right]
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff L Q' _).2 (hQX j)
  set J₀ : Ideal P := Ideal.map (C : A →+* P) (maximalIdeal A) ⊔ Ideal.span (X '' Set.range xS)
    with hJ₀
  have hJQ : J₀ ≤ Q' := by
    refine sup_le ?_ ?_
    · rw [Ideal.map_le_iff_le_comap]; exact fun a ha => hQA a ha
    · rw [Ideal.span_le]; rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩; exact hQX i
  have hfsJ : Ideal.ofList fs = J₀.map (algebraMap P L) := by
    rw [hfs, hv, List.ofFn_fin_append, Ideal.ofList_append, hJ₀, Ideal.map_sup, Ideal.map_map,
      ← hz.1, Ideal.map_span, Ideal.map_span, ← Set.range_comp, ← Set.range_comp,
      ← Set.range_comp]
    simp only [Ideal.ofList, List.mem_ofFn]
    rfl
  have : IsRegularRing (P ⧸ J₀) :=
    isRegularRing_quotient_map_maximalIdeal_sup_span_X (A := A) (Set.range xS)
  let qb : Ideal (P ⧸ J₀) := Q'.map (Ideal.Quotient.mk J₀)
  have : qb.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (by rw [Ideal.mk_ker]; exact hJQ)
  have hqb : qb.comap (Ideal.Quotient.mk J₀) = Q' := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker, sup_eq_left.2 hJQ]
  have := AlgebraicGeometry.TameSymbolPreparation.isLocalization_quotient_atPrime Q' L J₀ qb hqb
  have hreg : IsRegularLocalRing (L ⧸ J₀.map (algebraMap P L)) :=
    IsRegularLocalRing.of_ringEquiv
      (IsLocalization.algEquiv qb.primeCompl (Localization.AtPrime qb)
        (L ⧸ J₀.map (algebraMap P L))).toRingEquiv
  rw [← hfsJ] at hreg
  obtain ⟨N, w, h, hw, hwfs⟩ := exists_isRegularSystemOfParameters_of_isWeaklyRegular fs hm
    (isWeaklyRegular_localization_mvPolynomial hz xS hxS Q') hreg
  have hlen : fs.length = n + e := List.length_ofFn
  refine ⟨N, w, hlen ▸ h, hw, fun j => ?_, fun i => ?_⟩
  · have := hwfs (Fin.cast hlen.symm (Fin.castAdd e j))
    rw [List.get_ofFn] at this
    convert this using 2
    · ext; simp
    · simp [hv]; rfl
  · have := hwfs (Fin.cast hlen.symm (Fin.natAdd n i))
    rw [List.get_ofFn] at this
    convert this using 2
    · ext; simp
    · simp [hv]; rfl

/-- The localization at a prime `Q` of a quotient `B` of a ring `P` is the quotient of the
localization of `P` at the inverse image of `Q`. -/
private theorem exists_ringEquiv_localization_quotient {P B R : Type*} [CommRing P] [CommRing B]
    [CommRing R] (ρ : P →+* B) (hρ : Function.Surjective ρ) (Q : Ideal B) [Q.IsPrime]
    [Algebra B R] [IsLocalization.AtPrime R Q] :
    ∃ E : (Localization.AtPrime (Q.comap ρ) ⧸
        (RingHom.ker ρ).map (algebraMap P (Localization.AtPrime (Q.comap ρ)))) ≃+* R,
      ∀ p, E (Ideal.Quotient.mk _ (algebraMap P _ p)) = algebraMap B R (ρ p) := by
  set K := RingHom.ker ρ
  set Q' := Q.comap ρ
  set L := Localization.AtPrime Q'
  have hKQ : K ≤ Q' := fun p hp => by
    change ρ p ∈ Q
    rw [RingHom.mem_ker.1 hp]; exact Q.zero_mem
  let qb : Ideal (P ⧸ K) := Q'.map (Ideal.Quotient.mk K)
  have : qb.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (by rw [Ideal.mk_ker]; exact hKQ)
  have hqb : qb.comap (Ideal.Quotient.mk K) = Q' := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker, sup_eq_left.2 hKQ]
  have := AlgebraicGeometry.TameSymbolPreparation.isLocalization_quotient_atPrime Q' L K qb hqb
  let ε : P ⧸ K ≃+* B := RingHom.quotientKerEquivOfSurjective hρ
  have hε : ∀ p, ε (Ideal.Quotient.mk K p) = ρ p := fun p =>
    RingHom.quotientKerEquivOfSurjective_apply_mk hρ p
  have hmap : qb.primeCompl.map ε.toMonoidHom = Q.primeCompl := by
    ext b
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
      change ε (Ideal.Quotient.mk K p) ∉ Q
      rw [hε]
      intro hp
      exact hx (Ideal.mem_map_of_mem _ hp)
    · intro hb
      obtain ⟨p, rfl⟩ := hρ b
      refine ⟨Ideal.Quotient.mk K p, fun hp => hb ?_, hε p⟩
      have : p ∈ qb.comap (Ideal.Quotient.mk K) := hp
      rwa [hqb] at this
  refine ⟨IsLocalization.ringEquivOfRingEquiv (L ⧸ K.map (algebraMap P L)) R ε hmap, fun p => ?_⟩
  have h1 : (Ideal.Quotient.mk (K.map (algebraMap P L))) (algebraMap P L p) =
      algebraMap (P ⧸ K) (L ⧸ K.map (algebraMap P L)) (Ideal.Quotient.mk K p) := rfl
  rw [h1, IsLocalization.ringEquivOfRingEquiv_eq, hε]

/-- **Parameters at a point of a chart of the blow-up along a regular system of parameters.**
Let `A` be a Noetherian local ring with a regular system of parameters `z_1, …, z_n`, let
`g : {1, …, s} ↪ {1, …, n}` pick the parameters `z_{g(1)}, …, z_{g(s)}` generating the centre, let
`m₀ ≤ s`, and let `B = A[T_l : l ≠ m₀]/(z_{g(l)} - T_l z_{g(m₀)})` (the chart `D_+(z_{g(m₀)})`,
presented by `ρ`). Let `R` be the localization of `B` at a prime `Q` over the maximal ideal of
`A`. Then `R` has a regular system of parameters `w` containing `z_{g(m₀)}` (index `i₀`), the
`z_j` for `j ∉ g` and the `T_l` lying in `Q` (indices `σ(j)`), the remaining `T_l` being units of
`R`; the indices `j = g(l)` with `T_l` a unit form `U`. -/
private theorem exists_isRegularSystemOfParameters_chart {A : Type u} [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] {B R : Type u} [CommRing B] [CommRing R] [IsLocalRing R]
    {n : ℕ} {z : Fin n → A} (hz : IsRegularSystemOfParameters z) {s : ℕ} (g : Fin s → Fin n)
    (hg : Function.Injective g) (m₀ : Fin s)
    (ρ : MvPolynomial {l : Fin s // l ≠ m₀} A →+* B) (hρ : Function.Surjective ρ)
    (hker : RingHom.ker ρ = Ideal.span (Set.range fun l : {l : Fin s // l ≠ m₀} =>
      C (z (g l.1)) - X l * C (z (g m₀))))
    (Q : Ideal B) [Q.IsPrime] (hQ : ∀ a ∈ maximalIdeal A, ρ (C a) ∈ Q)
    [Algebra B R] [IsLocalization.AtPrime R Q] :
    ∃ (N : ℕ) (w : Fin N → R) (i₀ : Fin N) (σ : Fin n → Fin N) (U : Finset (Fin n)),
      IsRegularSystemOfParameters w ∧
      (∀ j ∈ U, ∃ l : {l : Fin s // l ≠ m₀}, g l.1 = j) ∧
      w i₀ = algebraMap B R (ρ (C (z (g m₀)))) ∧
      (∀ j, (∀ l, g l ≠ j) → w (σ j) = algebraMap B R (ρ (C (z j)))) ∧
      (∀ l : {l : Fin s // l ≠ m₀}, g l.1 ∉ U →
        algebraMap B R (ρ (C (z (g l.1)))) = w (σ (g l.1)) * w i₀) ∧
      (∀ j ∈ U, ∃ u, IsUnit u ∧ algebraMap B R (ρ (C (z j))) = u * w i₀) ∧
      (∀ j, j ≠ g m₀ → j ∉ U → σ j ≠ i₀) := by
  classical
  set Q' := Q.comap ρ
  set L := Localization.AtPrime Q'
  set S : Finset {l : Fin s // l ≠ m₀} := Finset.univ.filter fun l => ρ (X l) ∈ Q with hS
  set e := S.card
  let xS : Fin e → {l : Fin s // l ≠ m₀} := fun i => (S.equivFin.symm i).1
  have hxS : Function.Injective xS := fun i i' h => S.equivFin.symm.injective (Subtype.ext h)
  have hQX : ∀ i, X (xS i) ∈ Q' := fun i => (Finset.mem_filter.1 (S.equivFin.symm i).2).2
  obtain ⟨N, w, hN, hw, hwz, hwx⟩ :=
    exists_isRegularSystemOfParameters_localization_mvPolynomial hz xS hxS Q' hQ hQX
  have : IsRegularLocalRing L := isRegularLocalRing_of_isRegularSystemOfParameters hw
  set iy : Fin n → Fin N := fun j => Fin.castLE hN (Fin.castAdd e j) with hiy
  set ix : Fin e → Fin N := fun i => Fin.castLE hN (Fin.natAdd n i) with hix
  have hiy_inj : Function.Injective iy := fun a b h => by
    simpa [hiy, Fin.ext_iff] using h
  have hixy : ∀ i j, ix i ≠ iy j := fun i j h => by
    have := congrArg Fin.val h
    simp only [hix, hiy, Fin.coe_castLE, Fin.coe_natAdd, Fin.coe_castAdd] at this
    omega
  set i₁ := iy (g m₀) with hi₁
  set T : Finset (Fin N) := Finset.univ.image fun l : {l : Fin s // l ≠ m₀} => iy (g l.1) with hT
  have hmemT : ∀ i, i ∈ T ↔ ∃ l : {l : Fin s // l ≠ m₀}, iy (g l.1) = i := by simp [hT]
  have hi₁T : i₁ ∉ T := by
    rw [hmemT]
    rintro ⟨l, hl⟩
    exact l.2 (hg (hiy_inj hl))
  let coef : Fin N → L := fun i =>
    if h : ∃ l : {l : Fin s // l ≠ m₀}, iy (g l.1) = i then
      algebraMap (MvPolynomial {l : Fin s // l ≠ m₀} A) L (X h.choose) else 0
  have hcoefT : ∀ l : {l : Fin s // l ≠ m₀}, coef (iy (g l.1)) =
      algebraMap (MvPolynomial {l : Fin s // l ≠ m₀} A) L (X l) := by
    intro l
    have h : ∃ l' : {l : Fin s // l ≠ m₀}, iy (g l'.1) = iy (g l.1) := ⟨l, rfl⟩
    simp only [coef, dif_pos h]
    congr 2
    exact Subtype.ext (hg (hiy_inj h.choose_spec))
  have hcoefnT : ∀ i ∉ T, coef i = 0 := by
    intro i hi
    rw [hmemT] at hi
    simp only [coef, dif_neg hi]
  set w' : Fin N → L := fun i => w i - coef i * w i₁ with hw'
  have hw'rsop : IsRegularSystemOfParameters w' := by
    refine isRegularSystemOfParameters_of_sub_mem_span hw i₁ ?_ fun i => ?_
    · simp [hw', hcoefnT i₁ hi₁T]
    · rw [show w' i - w i = -(coef i) * w i₁ by simp only [hw']; ring]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  have hw'T : ∀ l : {l : Fin s // l ≠ m₀}, w' (iy (g l.1)) =
      algebraMap (MvPolynomial {l : Fin s // l ≠ m₀} A) L (C (z (g l.1)) - X l * C (z (g m₀))) := by
    intro l
    have h1 : w' (iy (g l.1)) = w (iy (g l.1)) - coef (iy (g l.1)) * w i₁ := rfl
    rw [h1, hcoefT, hi₁]
    simp only [hiy, hwz, map_sub, map_mul]
    rfl
  have hw'nT : ∀ i ∉ T, w' i = w i := by
    intro i hi
    simp [hw', hcoefnT i hi]
  have hspan : Ideal.span (w' '' T) =
      (RingHom.ker ρ).map (algebraMap (MvPolynomial {l : Fin s // l ≠ m₀} A) L) := by
    rw [hker, Ideal.map_span]
    congr 1
    ext y
    simp only [Set.mem_image, Finset.mem_coe, hmemT, Set.mem_range]
    constructor
    · rintro ⟨_, ⟨l, rfl⟩, rfl⟩
      exact ⟨_, ⟨l, rfl⟩, (hw'T l).symm⟩
    · rintro ⟨_, ⟨l, rfl⟩, rfl⟩
      exact ⟨_, ⟨l, rfl⟩, hw'T l⟩
  obtain ⟨hregq, -, hrsopq⟩ :=
    MMP.Flips.ResolutionInputs.isRegularSystemOfParameters_quotient_image hw'rsop T
  obtain ⟨E, hE⟩ := exists_ringEquiv_localization_quotient (R := R) ρ hρ Q
  let E' : L ⧸ Ideal.span (w' '' T) ≃+* R := (Ideal.quotEquivOfEq hspan).trans E
  have hE' : ∀ p, E' (Ideal.Quotient.mk _ (algebraMap (MvPolynomial {l : Fin s // l ≠ m₀} A) L p)) =
      algebraMap B R (ρ p) := by
    intro p
    simp only [E', RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
    exact hE p
  set o := Tᶜ.orderEmbOfFin rfl with ho
  have hrange : ∀ i ∉ T, ∃ j, o j = i := fun i hi => by
    change i ∈ Set.range o
    rw [ho, Finset.range_orderEmbOfFin]
    simpa using hi
  let pos : Fin N → Fin Tᶜ.card := fun i =>
    if h : i ∉ T then (hrange i h).choose else (hrange i₁ hi₁T).choose
  have hpos : ∀ i ∉ T, o (pos i) = i := fun i hi => by
    simp only [pos, dif_pos hi]
    exact (hrange i hi).choose_spec
  have hpos_inj : ∀ i i', i ∉ T → i' ∉ T → pos i = pos i' → i = i' := fun i i' hi hi' h => by
    rw [← hpos i hi, ← hpos i' hi', h]
  let wR : Fin Tᶜ.card → R := fun j => E' (Ideal.Quotient.mk _ (w' (o j)))
  have hwR : IsRegularSystemOfParameters wR := isRegularSystemOfParameters_map_ringEquiv E' hrsopq
  have hwRpos : ∀ i ∉ T, wR (pos i) = E' (Ideal.Quotient.mk _ (w i)) := fun i hi => by
    simp only [wR, hpos i hi, hw'nT i hi]
  -- the relations of the chart
  have hrel : ∀ l : {l : Fin s // l ≠ m₀}, ρ (C (z (g l.1))) = ρ (X l) * ρ (C (z (g m₀))) := by
    intro l
    have : C (z (g l.1)) - X l * C (z (g m₀)) ∈ RingHom.ker ρ := by
      rw [hker]; exact Ideal.subset_span ⟨l, rfl⟩
    rwa [RingHom.mem_ker, map_sub, map_mul, sub_eq_zero] at this
  let lift : Fin n → Option {l : Fin s // l ≠ m₀} := fun j =>
    if h : ∃ l : {l : Fin s // l ≠ m₀}, g l.1 = j then some h.choose else none
  have hlift : ∀ l : {l : Fin s // l ≠ m₀}, lift (g l.1) = some l := by
    intro l
    have h : ∃ l' : {l : Fin s // l ≠ m₀}, g l'.1 = g l.1 := ⟨l, rfl⟩
    simp only [lift, dif_pos h]
    exact congrArg some (Subtype.ext (hg h.choose_spec))
  have hlift' : ∀ j, (∀ l : {l : Fin s // l ≠ m₀}, g l.1 ≠ j) → lift j = none := by
    intro j hj
    have h : ¬ ∃ l : {l : Fin s // l ≠ m₀}, g l.1 = j := fun ⟨l, hl⟩ => hj l hl
    simp only [lift, dif_neg h]
  let U : Finset (Fin n) :=
    (Finset.univ.filter fun l : {l : Fin s // l ≠ m₀} => l ∉ S).image fun l => g l.1
  let σ : Fin n → Fin Tᶜ.card := fun j =>
    match lift j with
    | none => pos (iy j)
    | some l => if hS' : l ∈ S then pos (ix (S.equivFin ⟨l, hS'⟩)) else pos i₁
  have hσS : ∀ (l : {l : Fin s // l ≠ m₀}) (hl : l ∈ S),
      σ (g l.1) = pos (ix (S.equivFin ⟨l, hl⟩)) := by
    intro l hl
    simp only [σ, hlift l, dif_pos hl]
  have hσn : ∀ j, (∀ l : {l : Fin s // l ≠ m₀}, g l.1 ≠ j) → σ j = pos (iy j) := by
    intro j hj
    simp only [σ, hlift' j hj]
  have hmemU : ∀ l : {l : Fin s // l ≠ m₀}, g l.1 ∈ U ↔ l ∉ S := by
    intro l
    constructor
    · intro h
      obtain ⟨l', hl', hl'l⟩ := Finset.mem_image.1 h
      rw [← Subtype.ext (hg hl'l)]
      exact (Finset.mem_filter.1 hl').2
    · intro h
      exact Finset.mem_image.2 ⟨l, Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩, rfl⟩
  have hwi₀ : wR (pos i₁) = algebraMap B R (ρ (C (z (g m₀)))) := by
    rw [hwRpos i₁ hi₁T, hi₁, hwz]
    exact hE' _
  refine ⟨Tᶜ.card, wR, pos i₁, σ, U, hwR, ?_, hwi₀, ?_, ?_, ?_, ?_⟩
  · intro j hj
    obtain ⟨l, -, rfl⟩ := Finset.mem_image.1 hj
    exact ⟨l, rfl⟩
  · intro j hj
    have hjT : iy j ∉ T := by
      rw [hmemT]
      rintro ⟨l, hl⟩
      exact hj l.1 (hiy_inj hl)
    rw [hσn j (fun l => hj l.1), hwRpos _ hjT, hwz]
    exact hE' _
  · intro l hl
    have hlS : l ∈ S := by
      by_contra h
      exact hl ((hmemU l).2 h)
    rw [hσS l hlS, hwRpos _ (by rw [hmemT]; rintro ⟨l', hl'⟩; exact hixy _ _ hl'.symm), hwx,
      hE', hwi₀, hrel l, map_mul]
    congr 3
    simp [xS]
  · intro j hj
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hj
    have hlQ : ρ (X l) ∉ Q := by
      intro h
      exact (Finset.mem_filter.1 hl).2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
    refine ⟨algebraMap B R (ρ (X l)), IsLocalization.map_units R (⟨ρ (X l), hlQ⟩ : Q.primeCompl),
      ?_⟩
    rw [hwi₀, hrel l, map_mul]
  · intro j hjm hjU heq
    by_cases hj : ∃ l : {l : Fin s // l ≠ m₀}, g l.1 = j
    · obtain ⟨l, rfl⟩ := hj
      have hlS : l ∈ S := by
        by_contra h
        exact hjU ((hmemU l).2 h)
      rw [hσS l hlS] at heq
      exact hixy _ _ (hpos_inj _ _ (by rw [hmemT]; rintro ⟨l', hl'⟩; exact hixy _ _ hl'.symm)
        hi₁T heq)
    · simp only [not_exists] at hj
      have hjT : iy j ∉ T := by
        rw [hmemT]
        rintro ⟨l, hl⟩
        exact hj l (hiy_inj hl)
      rw [hσn j hj] at heq
      exact hjm (hiy_inj (hpos_inj _ _ hjT hi₁T heq))

end ChartAlgebra

/-! ### Coordinates on the blow-up over the centre -/

section Chart

variable {X : Scheme.{u}}

/-- On the blow-up of `Spec 𝒪_{X,y}` along the inverse image of `Z`, the composite stalk map at
`x''` of the projection `q` to `B_ZX` and of `B_ZX → X` sends a germ `a` at `y` to the germ at
`x''` of the pull-back of the global section `a` of `Spec 𝒪_{X,y}`. -/
private theorem stalkMap_comp_of_isPullback (Z : X.IdealSheafData) (y : X)
    {q : blowUp (Z.comap (X.fromSpecStalk y)) ⟶ blowUp Z}
    (sq : IsPullback (blowUpToBase (Z.comap (X.fromSpecStalk y))) q (X.fromSpecStalk y)
      (blowUpToBase Z)) (x'' : blowUp (Z.comap (X.fromSpecStalk y)))
    (h : y = (q ≫ blowUpToBase Z) x'') :
    (X.presheaf.stalkCongr (.of_eq h)).hom ≫ (q ≫ blowUpToBase Z).stalkMap x'' =
      (Scheme.ΓSpecIso (X.presheaf.stalk y)).inv ≫
        (Spec (X.presheaf.stalk y)).presheaf.germ ⊤
          (blowUpToBase (Z.comap (X.fromSpecStalk y)) x'') (Opens.mem_top _) ≫
        (blowUpToBase (Z.comap (X.fromSpecStalk y))).stalkMap x'' := by
  refine TopCat.Presheaf.stalk_hom_ext _ fun U hyU => ?_
  rw [TopCat.Presheaf.stalkCongr_hom]
  erw [TopCat.Presheaf.germ_stalkSpecializes_assoc]
  rw [Scheme.Hom.stalkMap_congr_hom _ _ sq.w.symm, TopCat.Presheaf.stalkCongr_hom]
  erw [TopCat.Presheaf.germ_stalkSpecializes_assoc]
  rw [Scheme.Hom.stalkMap_comp]
  erw [Scheme.Hom.germ_stalkMap_assoc]
  rw [Scheme.fromSpecStalk_app hyU]
  simp only [Category.assoc]
  erw [TopCat.Presheaf.germ_res_assoc]

/-- The stalk map of a blow-up at a point `x''` of an open `V`, on global sections, is the germ
at `x''` of the pull-back to `V`. -/
private theorem germ_top_stalkMap_eq_appLE_germ {S : Scheme.{u}} (I : S.IdealSheafData)
    (V : (blowUp I).Opens) (hV : V ≤ blowUpToBase I ⁻¹ᵁ ⊤) (x'' : blowUp I) (hx : x'' ∈ V) :
    S.presheaf.germ ⊤ (blowUpToBase I x'') (Opens.mem_top _) ≫ (blowUpToBase I).stalkMap x'' =
      (blowUpToBase I).appLE ⊤ V hV ≫ (blowUp I).presheaf.germ V x'' hx := by
  rw [Scheme.Hom.germ_stalkMap, Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]

/-- Members of a regular system of parameters of a Noetherian local ring `A`, carried to a ring
`Γ ≅ A`, form a regular sequence in every localization of `Γ` at a prime containing them. -/
private theorem isRegular_localization_of_isRegularSystemOfParameters {A Γ : Type u} [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] [CommRing Γ] {n : ℕ} {z : Fin n → A}
    (hz : IsRegularSystemOfParameters z) (J : Finset (Fin n)) (e : A ≃+* Γ) (P : Ideal Γ)
    [P.IsPrime] (hP : Ideal.span (Set.range fun i => e (z (J.orderEmbOfFin rfl i))) ≤ P) :
    RingTheory.Sequence.IsRegular (Localization.AtPrime P)
      (List.ofFn fun i =>
        algebraMap Γ (Localization.AtPrime P) (e (z (J.orderEmbOfFin rfl i)))) := by
  classical
  have : IsRegularLocalRing A := isRegularLocalRing_of_isRegularSystemOfParameters hz
  set g := J.orderEmbOfFin rfl
  set gc := Jᶜ.orderEmbOfFin rfl
  have hz' : IsRegularSystemOfParameters (Fin.append (z ∘ g) (z ∘ gc)) := by
    refine ⟨?_, ?_⟩
    · rw [MMP.Flips.ResolutionInputs.range_append, Set.range_comp, Set.range_comp,
        Finset.range_orderEmbOfFin, Finset.range_orderEmbOfFin, ← Set.image_union,
        Finset.coe_compl, Set.union_compl_self, Set.image_univ, hz.1]
    · rw [hz.2, Finset.card_add_card_compl, Fintype.card_fin]
  have hreg :=
    ((IsRegularLocalRing.isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay
      A).1 (List.ofFn (Fin.append (z ∘ g) (z ∘ gc))) ?_ ?_).1
  · rw [List.ofFn_fin_append] at hreg
    have hwr := ((RingTheory.Sequence.isWeaklyRegular_append_iff A _ _).1 hreg.1).1
    have hwr' := (Koszul.isWeaklyRegular_ringEquiv e _).1 hwr
    have h := hwr'.isRegular_of_isLocalization_of_mem (Localization.AtPrime P) P (fun r hr => by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hr
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha
      exact hP (Ideal.subset_span ⟨i, rfl⟩))
    simpa [List.map_ofFn, Function.comp_def] using h
  · rw [show Ideal.ofList (List.ofFn (Fin.append (z ∘ g) (z ∘ gc))) =
        Ideal.span (Set.range (Fin.append (z ∘ g) (z ∘ gc))) by
      simp only [Ideal.ofList, List.mem_ofFn]; rfl, hz'.1]
  · have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := A)
    rw [hz'.2] at h
    simp only [List.length_ofFn]
    exact_mod_cast h.symm

/-- **Local coordinates on the blow-up over a point of the centre.** Let `X` be locally
Noetherian, `π : X' = B_ZX → X` the blow-up of `Z`, `x' ∈ X'` with `x = π(x') ∈ Z`, `z` a regular
system of parameters of `𝒪_{X,x}` and `J` a set of indices with `I_{Z,x} = (z_j : j ∈ J)`, and
write `φ : 𝒪_{X,x} → 𝒪_{X',x'}`. There are a regular system of parameters `w` of `𝒪_{X',x'}`, an
index `m ∈ J`, an index `i₀` and indices `σ(j)` such that `w_{i₀} = φ(z_m)`, `w_{σ(j)} = φ(z_j)`
for `j ∉ J`, and, for `j ∈ J ∖ {m}`, either `φ(z_j) = w_{σ(j)} w_{i₀}` or (for `j ∈ U`)
`φ(z_j)` is a unit multiple of `w_{i₀}`; the `σ(j)`, `j ∉ U ∪ {m}`, differ from `i₀`. -/
theorem exists_chart_coordinates [IsLocallyNoetherian X] (Z : X.IdealSheafData)
    (x' : blowUp Z) (hx : blowUpToBase Z x' ∈ Z.support) {n : ℕ}
    {z : Fin n → X.presheaf.stalk (blowUpToBase Z x')} (hz : IsRegularSystemOfParameters z)
    {J : Finset (Fin n)} (hJ : IdealSheafData.stalk Z (blowUpToBase Z x') = Ideal.span (z '' J)) :
    ∃ (N : ℕ) (w : Fin N → (blowUp Z).presheaf.stalk x') (m : Fin n) (i₀ : Fin N)
      (σ : Fin n → Fin N) (U : Finset (Fin n)),
      IsRegularSystemOfParameters w ∧ m ∈ J ∧ U ⊆ J.erase m ∧
      w i₀ = ((blowUpToBase Z).stalkMap x').hom (z m) ∧
      (∀ j ∉ J, w (σ j) = ((blowUpToBase Z).stalkMap x').hom (z j)) ∧
      (∀ j ∈ J, j ≠ m → j ∉ U →
        ((blowUpToBase Z).stalkMap x').hom (z j) = w (σ j) * w i₀) ∧
      (∀ j ∈ U, ∃ u, IsUnit u ∧ ((blowUpToBase Z).stalkMap x').hom (z j) = u * w i₀) ∧
      (∀ j, j ≠ m → j ∉ U → σ j ≠ i₀) := by
  classical
  obtain ⟨q, sq⟩ :=
    Stacks.ResolutionOfSurfaces.CartierDescent.exists_isPullback_blowUpToBase_comap_fromSpecStalk
      (blowUpToBase Z x') Z
  obtain ⟨x'', hx''⟩ := Stacks.ResolutionOfSurfaces.CartierDescent.fibre_subset_range_of_isPullback
    (blowUpToBase Z x') sq (show x' ∈ (blowUpToBase Z) ⁻¹' {blowUpToBase Z x'} from rfl)
  have := Stacks.ResolutionOfSurfaces.CartierDescent.isIso_stalkMap_of_isPullback
    (blowUpToBase Z x') sq x''
  -- the base `Spec 𝒪_{X,x}` and the centre on it
  let A := X.presheaf.stalk (blowUpToBase Z x')
  let IA := Z.comap (X.fromSpecStalk (blowUpToBase Z x'))
  let e : A ≃+* Γ(Spec A, ⊤) := (Scheme.ΓSpecIso A).symm.commRingCatIsoToRingEquiv
  let g : Fin J.card → Fin n := J.orderEmbOfFin rfl
  have hg : Function.Injective g := (J.orderEmbOfFin rfl).injective
  have hrg : Set.range g = J := Finset.range_orderEmbOfFin _ _
  let f : Fin J.card → Γ(Spec A, ⊤) := fun i => e (z (g i))
  let U₀ : (Spec A).affineOpens := ⟨⊤, isAffineOpen_top _⟩
  have hf : IA.ideal U₀ = Ideal.span (Set.range f) := by
    have h1 := AlgebraicGeometry.ideal_comap_fromSpecStalk Z (blowUpToBase Z x')
    refine h1.trans ?_
    rw [hJ, Ideal.map_span]
    congr 1
    rw [← hrg, ← Set.range_comp, ← Set.range_comp]
    rfl
  have : IsNoetherianRing Γ(Spec A, ⊤) := isNoetherianRing_of_ringEquiv A e
  have hloc : ∀ (P : Ideal Γ(Spec A, ⊤)) [P.IsPrime], Ideal.span (Set.range f) ≤ P →
      RingTheory.Sequence.IsRegular (Localization.AtPrime P)
        (List.ofFn fun i => algebraMap Γ(Spec A, ⊤) (Localization.AtPrime P) (f i)) :=
    fun P _ hP => isRegular_localization_of_isRegularSystemOfParameters hz J e P hP
  -- the chart through `x''`
  have hx''mem : x'' ∈ blowUpToBase IA ⁻¹ᵁ U₀.1 := Opens.mem_top _
  rw [← MMP.Flips.ResolutionInputs.iSup_blowUpChartOpen_eq_preimage IA U₀ f hf] at hx''mem
  obtain ⟨m₀, hm₀⟩ := TopologicalSpace.Opens.mem_iSup.1 hx''mem
  obtain ⟨hsurj, hkerΓ⟩ :=
    MMP.Flips.ResolutionInputs.regularChartPresentation_surjective_and_ker IA U₀ f hf hloc m₀
  set a₀ := MMP.Flips.ResolutionInputs.generatorSection IA U₀ f hf m₀
  set V := blowUpChartOpen IA U₀ a₀ with hV
  let ρ₀ := MMP.Flips.ResolutionInputs.regularChartPresentation IA U₀ f hf m₀
  let Φ : MvPolynomial {l : Fin J.card // l ≠ m₀} A ≃+*
      MvPolynomial {l : Fin J.card // l ≠ m₀} Γ(Spec A, ⊤) := MvPolynomial.mapEquiv _ e
  let ρ := ρ₀.comp Φ.toRingHom
  have hρ : Function.Surjective ρ := hsurj.comp Φ.surjective
  have hρC : ∀ a, ρ (MvPolynomial.C a) = (blowUpChartMap IA U₀ a₀).hom (e a) := by
    intro a
    change ρ₀ (MvPolynomial.map (e : A →+* Γ(Spec A, ⊤)) (MvPolynomial.C a)) = _
    rw [MvPolynomial.map_C]
    exact MMP.Flips.ResolutionInputs.regularChartPresentation_C IA U₀ f hf m₀ _
  have hker : RingHom.ker ρ = Ideal.span (Set.range fun l : {l : Fin J.card // l ≠ m₀} =>
      MvPolynomial.C (z (g l.1)) - MvPolynomial.X l * MvPolynomial.C (z (g m₀))) := by
    rw [← RingHom.comap_ker, hkerΓ]
    have h1 : Ideal.comap Φ.toRingHom = Ideal.comap (Φ.symm.symm : _ ≃+* _) := rfl
    rw [h1, Ideal.comap_symm, Ideal.map_span, ← Set.range_comp]
    refine congrArg Ideal.span (congrArg Set.range (funext fun l => ?_))
    simp only [Function.comp_apply, map_sub, map_mul]
    change MvPolynomial.map (e.symm : Γ(Spec A, ⊤) →+* A) _ -
      MvPolynomial.map (e.symm : Γ(Spec A, ⊤) →+* A) _ *
        MvPolynomial.map (e.symm : Γ(Spec A, ⊤) →+* A) _ = _
    simp only [MvPolynomial.map_C, MvPolynomial.map_X, RingEquiv.coe_toRingHom,
      RingEquiv.symm_apply_apply, f]
  -- the local ring at `x''` is a localization of the chart ring
  let : Algebra Γ(blowUp IA, V.1) ((blowUp IA).presheaf.stalk x'') :=
    (blowUp IA).presheaf.algebra_section_stalk ⟨x'', hm₀⟩
  have : IsLocalization.AtPrime ((blowUp IA).presheaf.stalk x'')
      (V.2.primeIdealOf ⟨x'', hm₀⟩).asIdeal := V.2.isLocalization_stalk ⟨x'', hm₀⟩
  have halg : ∀ b, algebraMap Γ(blowUp IA, V.1) ((blowUp IA).presheaf.stalk x'') b =
      ((blowUp IA).presheaf.germ V.1 x'' hm₀).hom b := fun b => rfl
  -- the local ring at `x'` is the local ring at `x''`
  let χ : (blowUp Z).presheaf.stalk x' ≃+* (blowUp IA).presheaf.stalk x'' :=
    ((blowUp Z).presheaf.stalkCongr (.of_eq hx''.symm) ≪≫
      asIso (q.stalkMap x'')).commRingCatIsoToRingEquiv
  have hkey : (blowUpToBase Z).stalkMap x' ≫
      ((blowUp Z).presheaf.stalkCongr (.of_eq hx''.symm)).hom ≫ q.stalkMap x'' =
      (Scheme.ΓSpecIso A).inv ≫ blowUpChartMap IA U₀ a₀ ≫
        (blowUp IA).presheaf.germ V.1 x'' hm₀ := by
    rw [Scheme.Hom.stalkMap_congr_point_assoc _ x' (q x'') hx''.symm, ← Scheme.Hom.stalkMap_comp]
    erw [stalkMap_comp_of_isPullback Z _ sq x'' (by rw [Scheme.Hom.comp_apply, hx''])]
    erw [germ_top_stalkMap_eq_appLE_germ IA V.1 (blowUpChartOpen_le IA U₀ a₀) x'' hm₀]
  have hχ : ∀ a : A, χ (((blowUpToBase Z).stalkMap x').hom a) =
      algebraMap Γ(blowUp IA, V.1) ((blowUp IA).presheaf.stalk x'') (ρ (MvPolynomial.C a)) := by
    intro a
    rw [halg, hρC]
    have := congrArg (fun φ => φ.hom a) hkey
    simp only [CommRingCat.comp_apply] at this
    exact this
  have hχs : ∀ a : A, χ.symm (algebraMap Γ(blowUp IA, V.1) ((blowUp IA).presheaf.stalk x'')
      (ρ (MvPolynomial.C a))) = ((blowUpToBase Z).stalkMap x').hom a := fun a => by
    rw [← hχ, RingEquiv.symm_apply_apply]
  have hQ : ∀ a ∈ maximalIdeal A, ρ (MvPolynomial.C a) ∈ (V.2.primeIdealOf ⟨x'', hm₀⟩).asIdeal := by
    intro a ha
    rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff ((blowUp IA).presheaf.stalk x'')
      (V.2.primeIdealOf ⟨x'', hm₀⟩).asIdeal, ← hχ]
    have h1 : ((blowUpToBase Z).stalkMap x').hom a ∈ maximalIdeal _ :=
      (IsLocalRing.mem_maximalIdeal _).2 fun hu =>
        (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit _ a hu)
    refine (IsLocalRing.mem_maximalIdeal _).2 fun hu => (IsLocalRing.mem_maximalIdeal _).1 h1 ?_
    simpa using hu.map χ.symm
  obtain ⟨N, w, i₀, σ, U, hw, hU, hwi₀, hout, hin, hunit, hσ₀⟩ :=
    exists_isRegularSystemOfParameters_chart (R := (blowUp IA).presheaf.stalk x'') hz g hg m₀ ρ hρ
      hker (V.2.primeIdealOf ⟨x'', hm₀⟩).asIdeal hQ
  have hmemJ : ∀ j, j ∈ J ↔ ∃ l, g l = j := fun j => by
    rw [← Finset.mem_coe, ← hrg, Set.mem_range]
  refine ⟨N, fun i => χ.symm (w i), g m₀, i₀, σ, U,
    isRegularSystemOfParameters_map_ringEquiv χ.symm hw,
    (hmemJ _).2 ⟨m₀, rfl⟩, ?_, ?_, ?_, ?_, ?_, hσ₀⟩
  · intro j hj
    obtain ⟨l, rfl⟩ := hU j hj
    exact Finset.mem_erase.2 ⟨fun h => l.2 (hg h), (hmemJ _).2 ⟨l.1, rfl⟩⟩
  · simp only
    rw [hwi₀, hχs]
  · intro j hj
    simp only
    rw [hout j fun l hl => hj ((hmemJ j).2 ⟨l, hl⟩), hχs]
  · intro j hj hjm hjU
    obtain ⟨l, rfl⟩ := (hmemJ j).1 hj
    have hlm : l ≠ m₀ := fun h => hjm (h ▸ rfl)
    have := congrArg χ.symm (hin ⟨l, hlm⟩ hjU)
    rwa [hχs, map_mul] at this
  · intro j hj
    obtain ⟨u, hu, hu'⟩ := hunit j hj
    refine ⟨χ.symm u, hu.map _, ?_⟩
    have := congrArg χ.symm hu'
    rwa [hχs, map_mul] at this

end Chart

/-! ### The total transform -/

section TotalTransform

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- A prime lies in a union of loci `w c = 0` iff it contains one of the `w c`. -/
theorem mem_iUnion_zeroLocus_singleton_iff {A ι : Type*} [CommRing A] {w : ι → A}
    {C : Finset ι} {p : PrimeSpectrum A} :
    p ∈ ⋃ c ∈ C, PrimeSpectrum.zeroLocus {w c} ↔ ∃ c ∈ C, w c ∈ p.asIdeal := by
  simp [PrimeSpectrum.mem_zeroLocus]

/-- The total transform `π⁻¹(D ∖ Z)‾ ∪ π⁻¹(Z)` is a simple normal crossing divisor at every point
of the blow-up. -/
theorem isSNCAt_totalTransformStep [PerfectField k] (sX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType sX] [CompactSpace X] (hX : IsSmoothScheme sX) {D : Set X}
    (hD : IsSNCClosedSubset sX D) {Z : X.IdealSheafData} (hZ : HasSNCWith (componentsFamily D) Z)
    (x' : blowUp Z) : IsSNCAt (ClosedBlowupSequence.totalTransformStep Z D) x' := by
  classical
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsLocallyNoetherian (blowUp Z) := LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase Z)
  set π := blowUpToBase Z
  obtain ⟨n, z, C, hz, hDx, hZx⟩ := exists_coordinates sX hX hD hZ (π x')
  set φ := (π.stalkMap x').hom
  set f' := (blowUp Z).fromSpecStalk x' with hf'
  have key : ∀ S : Set X, f' ⁻¹' (π ⁻¹' S) =
      PrimeSpectrum.comap φ ⁻¹' (X.fromSpecStalk (π x') ⁻¹' S) := by
    intro S
    have h := Scheme.SpecMap_stalkMap_fromSpecStalk π (x := x')
    refine Set.ext fun p => ?_
    change π (f' p) ∈ S ↔ X.fromSpecStalk (π x') (PrimeSpectrum.comap φ p) ∈ S
    rw [← Scheme.Hom.comp_apply, hf', ← h]
    rfl
  have hDx' : f' ⁻¹' (π ⁻¹' D) = ⋃ c ∈ C, PrimeSpectrum.zeroLocus {φ (z c)} := by
    refine Set.ext fun (p : PrimeSpectrum _) => ?_
    refine (Set.ext_iff.1 (key D) p).trans ((Set.ext_iff.1 hDx (PrimeSpectrum.comap φ p)).trans ?_)
    exact mem_iUnion_zeroLocus_singleton_iff.trans
      (mem_iUnion_zeroLocus_singleton_iff (w := fun c => φ (z c))).symm
  have hcl : closure (π ⁻¹' (D \ Z.support)) ⊆ π ⁻¹' D :=
    closure_minimal (Set.preimage_mono Set.diff_subset) (hD.1.preimage π.continuous)
  by_cases hx : π x' ∈ Z.support
  · obtain ⟨J, hJ⟩ := hZx hx
    obtain ⟨N, w, m, i₀, σ, U, hw, hmJ, hU, hwi₀, hout, hin, hunit, hσ₀⟩ :=
      exists_chart_coordinates Z x' hx hz hJ
    let C₁ : Finset (Fin n) := C.filter fun j => j ≠ m ∧ j ∉ U
    refine ⟨N, w, insert i₀ (C₁.image σ), hw, ?_⟩
    have hUJ : ∀ j ∈ U, j ∈ J := fun j hj => (Finset.mem_erase.1 (hU hj)).2
    have hE : ∀ p : PrimeSpectrum ((blowUp Z).presheaf.stalk x'),
        π (f' p) ∈ Z.support ↔ w i₀ ∈ p.asIdeal := by
      intro p
      refine (Set.ext_iff.1 (key Z.support) p).trans
        ((Set.ext_iff.1 (preimage_fromSpecStalk_support Z (π x'))
          (PrimeSpectrum.comap φ p)).trans ?_)
      rw [hJ]
      refine (PrimeSpectrum.mem_zeroLocus _ _).trans ?_
      rw [SetLike.coe_subset_coe, Ideal.span_le]
      constructor
      · intro h
        rw [hwi₀]
        exact h ⟨m, hmJ, rfl⟩
      · rintro h _ ⟨j, hj, rfl⟩
        change φ (z j) ∈ p.asIdeal
        by_cases hjm : j = m
        · rw [hjm, ← hwi₀]; exact h
        by_cases hjU : j ∈ U
        · obtain ⟨u, -, hu⟩ := hunit j hjU
          rw [hu]; exact Ideal.mul_mem_left _ _ h
        · rw [hin j hj hjm hjU]; exact Ideal.mul_mem_left _ _ h
    have hDp : ∀ p : PrimeSpectrum ((blowUp Z).presheaf.stalk x'),
        π (f' p) ∈ D ↔ ∃ c ∈ C, φ (z c) ∈ p.asIdeal := fun p =>
      (Set.ext_iff.1 hDx' p).trans mem_iUnion_zeroLocus_singleton_iff
    have hR : ∀ p : PrimeSpectrum ((blowUp Z).presheaf.stalk x'),
        p ∈ (⋃ c ∈ insert i₀ (C₁.image σ), PrimeSpectrum.zeroLocus {w c}) ↔
          w i₀ ∈ p.asIdeal ∨ ∃ j ∈ C₁, w (σ j) ∈ p.asIdeal := fun p => by
      rw [mem_iUnion_zeroLocus_singleton_iff]
      simp
    refine Set.ext fun (p : PrimeSpectrum _) => ?_
    refine Iff.trans ?_ (hR p).symm
    change f' p ∈ ClosedBlowupSequence.totalTransformStep Z D ↔ _
    unfold ClosedBlowupSequence.totalTransformStep
    constructor
    · rintro (h | h)
      · by_cases h0 : w i₀ ∈ p.asIdeal
        · exact Or.inl h0
        · obtain ⟨c, hc, hcp⟩ := (hDp p).1 (hcl h)
          refine Or.inr ⟨c, ?_⟩
          by_cases hcJ : c ∈ J
          · by_cases hcm : c = m
            · subst hcm
              exact (h0 (hwi₀ ▸ hcp)).elim
            · by_cases hcU : c ∈ U
              · obtain ⟨u, hu, hu'⟩ := hunit c hcU
                rw [hu'] at hcp
                refine absurd ((p.isPrime.mem_or_mem hcp).resolve_left fun h' => ?_) h0
                exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h' hu)
              · rw [hin c hcJ hcm hcU] at hcp
                exact ⟨Finset.mem_filter.2 ⟨hc, hcm, hcU⟩,
                  (p.isPrime.mem_or_mem hcp).resolve_right h0⟩
          · have hcm : c ≠ m := fun h' => hcJ (h' ▸ hmJ)
            have hcU : c ∉ U := fun h' => hcJ (hUJ c h')
            refine ⟨Finset.mem_filter.2 ⟨hc, hcm, hcU⟩, ?_⟩
            rwa [hout c hcJ]
      · exact Or.inl ((hE p).1 h)
    · rintro (h0 | ⟨j, hj, hjp⟩)
      · exact Or.inr ((hE p).2 h0)
      · obtain ⟨hjC, hjm, hjU⟩ := Finset.mem_filter.1 hj
        left
        let P₀ : PrimeSpectrum ((blowUp Z).presheaf.stalk x') :=
          ⟨Ideal.span {w (σ j)}, isPrime_span_singleton_of_isRegularSystemOfParameters hw (σ j)⟩
        have hP₀ : f' P₀ ∈ π ⁻¹' (D \ Z.support) := by
          refine ⟨(hDp P₀).2 ⟨j, hjC, ?_⟩, fun hZ' => ?_⟩
          · by_cases hjJ : j ∈ J
            · rw [hin j hjJ hjm hjU]
              exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
            · rw [← hout j hjJ]
              exact Ideal.subset_span rfl
          · exact notMem_span_singleton_of_isRegularSystemOfParameters hw (hσ₀ j hjm hjU)
              ((hE P₀).1 hZ')
        have hle : P₀ ≤ p := (Ideal.span_singleton_le_iff_mem _).2 hjp
        exact (((PrimeSpectrum.le_iff_specializes _ _).1 hle).map f'.continuous).mem_closed
          isClosed_closure (subset_closure hP₀)
  · have hiso : IsIso (π.stalkMap x') :=
      isIso_stalkMap_of_isIso_morphismRestrict π (isIso_blowUpToBase_restrict_compl_support Z)
        (show x' ∈ π ⁻¹ᵁ Z.support.compl from hx)
    have hw : IsRegularSystemOfParameters fun i => φ (z i) :=
      isRegularSystemOfParameters_map_ringEquiv
        (asIso (π.stalkMap x')).commRingCatIsoToRingEquiv hz
    refine ⟨n, fun i => φ (z i), C, hw, ?_⟩
    rw [← hDx']
    refine Set.ext fun p => ?_
    have hp : π (f' p) ∉ Z.support := by
      have hsp : f' p ⤳ x' := Scheme.range_fromSpecStalk.subset ⟨p, rfl⟩
      exact hsp.mem_open ((Z.support.isClosed.isOpen_compl).preimage π.continuous) hx
    change f' p ∈ ClosedBlowupSequence.totalTransformStep Z D ↔ π (f' p) ∈ D
    unfold ClosedBlowupSequence.totalTransformStep
    refine ⟨?_, fun h => Or.inl (subset_closure ⟨h, hp⟩)⟩
    rintro (h | h)
    exacts [hcl h, absurd h hp]

/-- **The total transform of an snc divisor under one blow-up is an snc divisor** (Kollár,
Def. 3.25, for one blow-up). Let `X` be a smooth scheme of finite type over a field `k` of
characteristic `0`, `D ⊆ X` a divisor with simple normal crossings and `Z ⊆ X` a closed subscheme
having simple normal crossings with the sum of the irreducible components of `D`. Let
`π : X' = B_ZX → X` be the blow-up. Then `π⁻¹(D ∖ Z)‾ ∪ π⁻¹(Z) ⊆ X'` is a divisor with simple
normal crossings. -/
@[mmp "lem_kr3b_one_blowup_total_transform_snc"]
theorem isSNCClosedSubset_totalTransformStep [CharZero k] (sX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType sX] [QuasiCompact sX] (hX : IsSmoothScheme sX) {D : Set X}
    (hD : IsSNCClosedSubset sX D) {Z : X.IdealSheafData} (hZ : HasSNCWith (componentsFamily D) Z) :
    IsSNCClosedSubset (blowUpToBase Z ≫ sX) (ClosedBlowupSequence.totalTransformStep Z D) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : CompactSpace (blowUp Z) := QuasiCompact.compactSpace_of_compactSpace (blowUpToBase Z)
  exact isSNCClosedSubset_of_forall_isSNCAt (blowUpToBase Z ≫ sX)
    (isClosed_closure.union (Z.support.isClosed.preimage (blowUpToBase Z).continuous))
    (isSNCAt_totalTransformStep sX hX hD hZ)

end TotalTransform

end MMP.Resolution
