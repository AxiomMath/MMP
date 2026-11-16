module
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
public import MMP.AlgebraicGeometry.Chow.FieldSituation
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Relative
public import MMP.AlgebraicGeometry.Dimension.HeightCoheight

/-!
# The negativity lemma for surfaces (Kollár–Mori, Lemma 3.39)

Let `h : Z ⟶ Y` be a proper birational morphism of normal surfaces over a field `k`, and `B` a
`ℚ`-Cartier `ℚ`-divisor on `Z` such that `-B` is `h`-nef. If the pushforward `h_* B` is
effective, then so is `B`. This is the case `dim Y = 2` of the negativity lemma.

Let `G = mB` be Cartier. A prime divisor of `Z` whose image is not a point has the coefficient
of its image in `h_* B`, so every component `E` with negative coefficient lies over a closed
point `y`. Perturbing `G` by `div ψ`, for `ψ` the pull-back of a function vanishing along a prime
divisor of `Y` through `y`, gives a Cartier divisor whose degree on some proper curve `C` of the
connected fibre over `y` is positive; but `div ψ` is principal and `-B` is `h`-nef, so that degree
is `ord_{E₀} ψ · m (B · C) ≤ 0`.

## Main results

* `MMP.Mori.QDivisor.isEffective_of_isRelativelyNef_neg_of_isEffective_transformDivisor`: the
  negativity lemma for surfaces.

## Implementation notes

The pushforward `h_* B` of a divisor along a birational morphism is its birational transform
`MMP.Mori.RationalMap.transformDivisor` along `h.toRationalMap`. A surface is a normal variety
whose underlying space has Krull dimension two. The argument does not resolve the singularities
of `Z`, so it holds over every field; the negative definiteness of the exceptional curves is
replaced by the principal divisor `div ψ`, which is numerically trivial on every proper curve.
The auxiliary lemmas live in the namespace `MMP.Mori.NegativityLemmaSurface`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Lemma 3.39
-/

@[expose] public section

universe u

namespace MMP.Mori.NegativityLemmaSurface

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori

universe v

section Dimension

variable {k : Type v} [Field k] {Y : Scheme.{v}} (sY : Y ⟶ Spec (.of k)) [IsIntegral Y]
  [LocallyOfFiniteType sY]

include sY

/-- On an integral scheme of finite type over `k`, the dimension is the sum of the height and the
coheight of any point, in the specialization order. -/
private theorem height_add_coheight_eq (x : Y) :
    ((Order.height x + Order.coheight x : ℕ∞) : WithBot ℕ∞) = topologicalKrullDim Y := by
  letI : Y.Over (Spec (.of k)) := ⟨sY⟩
  have : LocallyOfFiniteType (Y ↘ Spec (.of k)) := ‹LocallyOfFiniteType sY›
  rw [MMP.height_add_coheight_eq_krullDim k x]
  exact (Order.krullDim_eq_of_orderIso irreducibleSetEquivPoints).symm

/-- A point of a surface which is not closed has codimension at most one. -/
private theorem coheight_le_one_of_not_isClosed (hdim : topologicalKrullDim Y = 2) {x : Y}
    (hx : ¬ IsClosed ({x} : Set Y)) : Order.coheight x ≤ 1 := by
  have hsum := height_add_coheight_eq (k := k) sY x
  rw [hdim] at hsum
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace sY
  obtain ⟨p, hp, hpc⟩ := nonempty_inter_closedPoints
    (⟨x, subset_closure rfl⟩ : (closure {x}).Nonempty) isClosed_closure.isLocallyClosed
  have hxp : x ⤳ p := specializes_iff_mem_closure.mpr hp
  have hlt : p < x := lt_iff_le_not_ge.mpr ⟨Scheme.le_iff_specializes.mpr hxp, fun h => hx (by
    rw [show x = p from (hxp.antisymm (Scheme.le_iff_specializes.mp h)).eq]
    exact mem_closedPoints_iff.mp hpc)⟩
  have h1 : 1 ≤ Order.height x := le_trans (by simp) (Order.height_add_one_le hlt)
  have hsum' : Order.height x + Order.coheight x = 2 :=
    WithBot.coe_injective (by rw [hsum]; rfl)
  by_contra hc
  have h2 : 2 ≤ Order.coheight x := Order.add_one_le_of_lt (not_le.mp hc)
  exact absurd ((add_le_add h1 h2).trans hsum'.le) (by decide)

/-- A closed point of a surface has codimension two. -/
private theorem coheight_eq_two_of_isClosed (hdim : topologicalKrullDim Y = 2) {x : Y}
    (hx : IsClosed ({x} : Set Y)) : Order.coheight x = 2 := by
  have hsum := height_add_coheight_eq (k := k) sY x
  have hmin : IsMin x := fun y hy => by
    have : y ∈ closure ({x} : Set Y) :=
      specializes_iff_mem_closure.mp (Scheme.le_iff_specializes.mp hy)
    rw [hx.closure_eq, Set.mem_singleton_iff] at this
    exact this ▸ le_rfl
  rw [hdim, Order.height_eq_zero.mpr hmin, zero_add] at hsum
  exact WithBot.coe_injective (by rw [hsum]; rfl)

/-- The generic point of a prime divisor of a surface is not closed. -/
private theorem not_isClosed_genericPoint (hdim : topologicalKrullDim Y = 2)
    (P : MMP.Mori.PrimeDivisor Y) : ¬ IsClosed ({P.genericPoint} : Set Y) := fun hc => by
  have := coheight_eq_two_of_isClosed sY hdim hc
  rw [P.coheight_genericPoint] at this
  exact absurd this (by decide)

/-- On a surface, through every closed point passes a prime divisor. -/
private theorem exists_primeDivisor_specializes (hdim : topologicalKrullDim Y = 2) {x : Y}
    (hx : IsClosed ({x} : Set Y)) :
    ∃ P : MMP.Mori.PrimeDivisor Y, P.genericPoint ⤳ x := by
  obtain ⟨-, ⟨z, hxz, hz⟩, -⟩ := (Order.coheight_eq_coe_add_one_iff (n := 1)).mp
    (coheight_eq_two_of_isClosed sY hdim hx)
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hz, ?_⟩
  rw [show MMP.Mori.PrimeDivisor.genericPoint (AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hz) =
    z from AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hz]
  exact Scheme.le_iff_specializes.mp hxz.le

end Dimension

section Transform

/-- At a point of codimension at most one of a normal locally Noetherian integral scheme, the
local ring is a valuation ring: the function field at the generic point, a discrete valuation ring
at a point of codimension one. -/
private theorem valuationRing_stalk_of_coheight_le_one {X : Scheme.{v}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {y : X} (hy : Order.coheight y ≤ 1) :
    ValuationRing (X.presheaf.stalk y) := by
  rcases hy.lt_or_eq with h0 | h1
  · obtain rfl : y = genericPoint X := (Specializes.antisymm
      (Order.coheight_eq_zero.mp (Order.lt_one_iff.mp h0) (genericPoint_specializes y))
      (genericPoint_specializes y)).eq
    change ValuationRing X.functionField
    infer_instance
  · have := Stacks.AlgebraicGeometry.UnitsNormalProper.isDiscreteValuationRing_stalk h1
    infer_instance

/-- Let `h : Z ⟶ Y` be a proper birational morphism of normal varieties, `Y` a surface, and `B` a
divisor on `Z` with `h_* B` effective. A prime divisor `E` of `Z` whose image is not a point has
nonnegative coefficient in `B`. -/
private theorem coeff_nonneg_of_not_isClosed (k : Type v) [Field k] {Y Z : Scheme.{v}}
    (sY : Y ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k)) (hY : IsNormalVariety k sY)
    (hZ : IsNormalVariety k sZ) (hYdim : topologicalKrullDim Y = 2)
    (h : Z ⟶ Y) (hh : h ≫ sY = sZ) [IsProper h] (hhb : IsBirationalMorphism h)
    {B : QDivisor Z} (heff : (RationalMap.transformDivisor (X := Z) h.toRationalMap B).IsEffective)
    (E : MMP.Mori.PrimeDivisor Z) (hE : ¬ IsClosed ({h E.genericPoint} : Set Y)) :
    0 ≤ B.coeff E := by
  have : IsIntegral Y := hY.1.toIsIntegral
  have : IsIntegral Z := hZ.1.toIsIntegral
  have : IsLocallyNoetherian Z := hZ.isLocallyNoetherian
  have : IsNormal Z := hZ.2
  have : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := hY.isLocallyNoetherian
  have : IsNormal Y := hY.2
  have hco := coheight_le_one_of_not_isClosed sY hYdim hE
  have := valuationRing_stalk_of_coheight_le_one hco
  have : IsDominant h := hhb.isDominant
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing h hhb.functionFieldMap_bijective
    E.genericPoint
  have h1 : Order.coheight (h E.genericPoint) = 1 := by
    have h1 : ringKrullDim (Z.presheaf.stalk E.genericPoint) =
        ringKrullDim (Y.presheaf.stalk (h E.genericPoint)) :=
      (ringKrullDim_eq_of_ringEquiv
        (asIso (h.stalkMap E.genericPoint)).commRingCatIsoToRingEquiv).symm
    rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight,
      E.coheight_genericPoint] at h1
    exact_mod_cast h1.symm
  set P := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ h1
  have hP : MMP.Mori.PrimeDivisor.genericPoint P = h E.genericPoint :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ h1
  obtain ⟨E', -, -, htr⟩ := MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply
    hY (f := h) (by rwa [hh]) hhb P
  have : IsSeparated sY := hY.1.toIsSeparated
  have : IsSeparated (Y ↘ Limits.terminal Scheme) := by
    rw [show (Y ↘ Limits.terminal Scheme) = sY ≫ (Spec (.of k) ↘ Limits.terminal Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  have hEP : RationalMap.transformPrimeDivisor (X := Z) h.toRationalMap E = some P :=
    (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff h E P).2 hP.symm
  have hs := htr (Finsupp.single E (1 : ℤ))
  rw [RationalMap.transformDivisor_single_of_eq_some hEP, Finsupp.single_eq_same] at hs
  have hEE : E = E' := by
    by_contra hne
    simp [Finsupp.single_apply, hne] at hs
  have h2 := heff P
  rwa [DivisorWithCoeffs.coeff, htr B, ← hEE] at h2

end Transform

section Function

/-- On an affine open `V` of a normal integral locally Noetherian scheme containing the generic
point of a prime divisor `P`, some nonzero section over `V` vanishes along `P`. -/
private theorem exists_ne_zero_germ_mem_maximalIdeal {X : Scheme.{v}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {V : X.Opens} (hV : IsAffineOpen V)
    (P : MMP.Mori.PrimeDivisor X) (hP : P.genericPoint ∈ V) :
    ∃ φ : Γ(X, V), φ ≠ 0 ∧ X.presheaf.germ V P.genericPoint hP φ ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk P.genericPoint) := by
  let x : V := ⟨P.genericPoint, hP⟩
  letI : Algebra Γ(X, V) (X.presheaf.stalk P.genericPoint) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf x
  have := hV.isLocalization_stalk x
  have := P.isDiscreteValuationRing_localRing
  have hmax := IsLocalization.AtPrime.map_eq_maximalIdeal (R := Γ(X, V))
    (p := (hV.primeIdealOf x).asIdeal) (Rₚ := X.presheaf.stalk P.genericPoint)
  have hq : (hV.primeIdealOf x).asIdeal ≠ ⊥ := by
    intro hq
    rw [hq, Ideal.map_bot] at hmax
    exact IsDiscreteValuationRing.not_a_field _ hmax.symm
  obtain ⟨φ, hφq, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hq
  refine ⟨φ, hφ0, ?_⟩
  rw [← hmax]
  exact Ideal.mem_map_of_mem (algebraMap Γ(X, V) (X.presheaf.stalk P.genericPoint)) hφq

/-- A section whose germ at `x` lies in the maximal ideal has its germ in the maximal ideal at
every specialization `y` of `x`. -/
private theorem germ_mem_maximalIdeal_of_specializes {X : Scheme.{v}} {V : X.Opens}
    (φ : Γ(X, V)) {x y : X} (hxy : x ⤳ y) (hx : x ∈ V) (hy : y ∈ V)
    (h : X.presheaf.germ V x hx φ ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x)) :
    X.presheaf.germ V y hy φ ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk y) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h ⊢
  intro hu
  apply h
  have := hu.map (X.presheaf.stalkSpecializes hxy).hom
  rwa [TopCat.Presheaf.germ_stalkSpecializes_apply] at this

/-- The germ at `z` of the pull-back of a section whose germ at `h z` lies in the maximal ideal is
not a unit. -/
private theorem not_isUnit_germ_app {Y Z : Scheme.{v}} (h : Z ⟶ Y) {V : Y.Opens} (φ : Γ(Y, V))
    (z : Z) (hz : z ∈ h ⁻¹ᵁ V)
    (hm : Y.presheaf.germ V (h z) hz φ ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk (h z))) :
    ¬ IsUnit (Z.presheaf.germ (h ⁻¹ᵁ V) z hz (h.app V φ)) := by
  rw [← Scheme.Hom.germ_stalkMap_apply h V z hz φ]
  exact fun hu =>
    (IsLocalRing.mem_maximalIdeal _).mp hm (isUnit_of_map_unit (h.stalkMap z).hom _ hu)

/-- The germ at a point over the generic point of the pull-back of a nonzero section is nonzero. -/
private theorem germ_app_ne_zero {Y Z : Scheme.{v}} [IsIntegral Y] (h : Z ⟶ Y)
    {V : Y.Opens} (φ : Γ(Y, V)) (hφ : φ ≠ 0) (z : Z) (hz : z ∈ h ⁻¹ᵁ V)
    (hgen : h z = genericPoint Y) :
    Z.presheaf.germ (h ⁻¹ᵁ V) z hz (h.app V φ) ≠ 0 := by
  rw [← Scheme.Hom.germ_stalkMap_apply h V z hz φ]
  have key : ∀ (y : Y) (hy : y = genericPoint Y) (hyV : y ∈ V),
      IsUnit (Y.presheaf.germ V y hyV φ) := by
    rintro y rfl hyV
    exact Ne.isUnit (G₀ := Y.functionField)
      (fun h0 => hφ (germ_injective_of_isIntegral Y _ hyV (h0.trans (map_zero _).symm)))
  exact ((key _ hgen hz).map (h.stalkMap z).hom).ne_zero

end Function

section FibreCurves

/-- In a Noetherian quasi-sober space, a closed connected set `F` that meets a closed set `S`
without lying in it contains a point outside `S` specializing to a point of `S`. -/
private theorem exists_specializes_of_isConnected {Y : Type*} [TopologicalSpace Y]
    [TopologicalSpace.NoetherianSpace Y] [QuasiSober Y] {F S : Set Y} (hF : IsClosed F)
    (hFc : IsConnected F) (hS : IsClosed S) (hmeet : (F ∩ S).Nonempty) (hsub : ¬ F ⊆ S) :
    ∃ η ∈ F, η ∉ S ∧ ∃ s ∈ S, η ⤳ s := by
  set T := F \ S
  obtain ⟨s, hsT, hsS⟩ : (closure T ∩ S).Nonempty := by
    obtain ⟨y, hyF, hyS⟩ := Set.not_subset.mp hsub
    obtain ⟨w, -, hw⟩ := isPreconnected_closed_iff.mp hFc.isPreconnected _ _
      isClosed_closure hS (fun a ha => (em (a ∈ S)).symm.imp
        (fun haS => subset_closure (show a ∈ T from ⟨ha, haS⟩)) id)
      ⟨y, hyF, subset_closure (show y ∈ T from ⟨hyF, hyS⟩)⟩ hmeet
    exact ⟨w, hw⟩
  obtain ⟨Z, hZfin, hZcl, hZirr, hZeq⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible
      (isClosed_closure : IsClosed (closure T))
  have hsub' : closure T ⊆ ⋃₀ {t ∈ Z | (t ∩ T).Nonempty} := by
    refine closure_minimal (fun y hy => ?_) ?_
    · obtain ⟨z, hz, hyz⟩ : y ∈ ⋃₀ Z := hZeq ▸ subset_closure hy
      exact ⟨z, ⟨hz, y, hyz, hy⟩, hyz⟩
    · exact (hZfin.subset (Set.sep_subset _ _)).isClosed_sUnion fun t ht => hZcl t ht.1
  obtain ⟨z, ⟨hzZ, t, htz, htT⟩, hsz⟩ := hsub' hsT
  obtain ⟨ζ, hζ⟩ := QuasiSober.sober (hZirr z hzZ) (hZcl z hzZ)
  have hzT : z ⊆ closure T := hZeq ▸ Set.subset_sUnion_of_mem hzZ
  exact ⟨ζ, closure_minimal Set.sdiff_subset hF (hzT hζ.mem),
    fun hζS => htT.2 ((hζ.specializes htz).mem_closed hS hζS), s, hsS, hζ.specializes hsz⟩

/-- The fibre of a proper morphism `f` of `k`-schemes of finite type over a closed point is proper
over `k`. -/
private theorem isProper_fiberι_comp (k : Type v) [Field k] {X Y : Scheme.{v}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (f : Y ⟶ X) [IsProper f] (x : X)
    (hx : IsClosed ({x} : Set X)) : IsProper (f.fiberι x ≫ f ≫ sX) := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  have : LocallyOfFiniteType (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_locallyOfFiniteType.mp hx
  have : IsFinite (X.fromSpecResidueField x ≫ sX) :=
    isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance
  have : IsProper (f.fiberToSpecResidueField x) :=
    inferInstanceAs (IsProper (Limits.pullback.snd f (X.fromSpecResidueField x)))
  rw [Scheme.Hom.fiber_fac_assoc]
  infer_instance

/-- An injective morphism `ι : W ⟶ Y` to a separated `k`-scheme of finite type maps a proper curve
of `W` onto a proper curve of `Y`. -/
private theorem isProperCurve_of_injective {k : Type v} [Field k] {W Y : Scheme.{v}}
    (sY : Y ⟶ Spec (.of k)) [IsSeparated sY] [LocallyOfFiniteType sY] (ι : W ⟶ Y)
    (hι : Function.Injective ι) (C : ProperCurve (ι ≫ sY)) : IsProperCurve sY (ι C.point) := by
  have hφsY : (C.ι ≫ ι) ≫ sY = C.ι ≫ ι ≫ sY := Category.assoc _ _ _
  have : AlgebraicGeometry.IsCurve k ((C.ι ≫ ι) ≫ sY) := hφsY ▸ C.isCurve
  have : IsProper ((C.ι ≫ ι) ≫ sY) := by
    rw [hφsY]
    infer_instance
  have hnc : ¬ ∃ z, Set.range (C.ι ≫ ι) = {z} := by
    rintro ⟨z, hz⟩
    have : Subsingleton C.scheme := ⟨fun a b => C.ι.isEmbedding.injective (hι (by
      have ha : (C.ι ≫ ι) a ∈ ({z} : Set Y) := hz ▸ ⟨a, rfl⟩
      have hb : (C.ι ≫ ι) b ∈ ({z} : Set Y) := hz ▸ ⟨b, rfl⟩
      exact (Set.mem_singleton_iff.mp ha).trans (Set.mem_singleton_iff.mp hb).symm))⟩
    have h0 := topologicalKrullDim_zero_of_discreteTopology C.scheme
    rw [C.dim_eq] at h0
    exact absurd h0 (by decide)
  have hker := C.ker_comp ι
  constructor
  · have h1 := (MMP.Mori.isCurve_imageι_comp sY (C.ι ≫ ι) hnc).topologicalKrullDim_eq_one
    change topologicalKrullDim (C.ι ≫ ι).ker.subscheme = 1 at h1
    rwa [hker] at h1
  · have h1 : IsProper ((C.ι ≫ ι).imageι ≫ sY) := isProper_imageι_comp _ sY
    change IsProper ((C.ι ≫ ι).ker.subschemeι ≫ sY) at h1
    rwa [hker] at h1

/-- The fibre of `f` over a closed point is connected and proper, so if it meets a closed set `S`
without lying in it, it contains a proper curve, contracted by `f`, that meets `S` without lying
in it. -/
private theorem exists_properCurve_isContractedBy (k : Type v) [Field k] {X Y : Scheme.{v}}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [QuasiCompact sY]
    (hX : IsNormalVariety k sX) (hY : IsNormalVariety k sY) (f : Y ⟶ X) (hf : f ≫ sX = sY)
    [IsProper f] (hfb : IsBirationalMorphism f)
    (x : X) (hx : IsClosed ({x} : Set X)) {S : Set Y} (hS : IsClosed S)
    (hmeet : (f.base ⁻¹' {x} ∩ S).Nonempty) (hsub : ¬ f.base ⁻¹' {x} ⊆ S) :
    ∃ C : ProperCurve sY, C.IsContractedBy f ∧ closure {C.point} ⊆ f.base ⁻¹' {x} ∧
      ¬ Set.range C.ι ⊆ S ∧ (Set.range C.ι ∩ S).Nonempty := by
  have : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := hY.isLocallyNoetherian
  have : IsSeparated sY := hY.1.toIsSeparated
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace sY
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have : IsNoetherian Y := {}
  have hconn := (MMP.Resolution.Bridges.isIso_app_and_isConnected_of_isBirationalMorphism
    sY sX hY.1 hX f hfb).2 x
  have hFcl : IsClosed (f.base ⁻¹' {x}) := hx.preimage f.continuous
  obtain ⟨η, hηF, hηS, s, hsS, hηs⟩ := exists_specializes_of_isConnected hFcl hconn hS hmeet hsub
  obtain ⟨p, hps, hpc⟩ := nonempty_inter_closedPoints
    ⟨s, (show s ∈ closure {s} from subset_closure rfl)⟩ isClosed_closure.isLocallyClosed
  have hηp : η ⤳ p := hηs.trans (specializes_iff_mem_closure.mpr hps)
  have hpS : p ∈ S := (specializes_iff_mem_closure.mpr hps).mem_closed hS hsS
  have hpF : p ∈ f.base ⁻¹' {x} := hηp.mem_closed hFcl hηF
  let ι := f.fiberι x
  let sF := ι ≫ sY
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : IsProper sF := by simpa [sF, ι, hf] using isProper_fiberι_comp k sX f x hx
  have : IsLocallyNoetherian (f.fiber x) := LocallyOfFiniteType.isLocallyNoetherian sF
  have hrι : Set.range ι = f.base ⁻¹' {x} := f.range_fiberι x
  obtain ⟨η', hη'⟩ : η ∈ Set.range ι := hrι ▸ hηF
  obtain ⟨p', hp'⟩ : p ∈ Set.range ι := hrι ▸ hpF
  have hemb : Topology.IsEmbedding ι := ι.isEmbedding
  have hη'p' : η' ⤳ p' := by rwa [← hemb.isInducing.specializes_iff, hη', hp']
  have hp'c : IsClosed ({p'} : Set (f.fiber x)) := by
    rw [show ({p'} : Set (f.fiber x)) = ι ⁻¹' {p} from Set.ext fun z => by
      simp only [Set.mem_singleton_iff, Set.mem_preimage, ← hp', hemb.injective.eq_iff]]
    exact (mem_closedPoints_iff.mp hpc).preimage ι.continuous
  obtain ⟨y', -, hy'p', hy'S, hy'⟩ := MMP.Fourfold.exists_isProperCurve_of_specializes sF hη'p'
    hp'c (hS.preimage ι.continuous) (by simpa [hp'] using hpS)
    (by simpa [hη'] using hηS)
  let C' : ProperCurve sF := ⟨y', hy'⟩
  let C : ProperCurve sY := ⟨ι y', isProperCurve_of_injective sY ι hemb.injective C'⟩
  have hrC : Set.range C.ι = closure {ι y'} := C.range_ι
  have hclF : closure {ι y'} ⊆ f.base ⁻¹' {x} := by
    rw [← C'.range_comp ι rfl, ← hrι]
    rintro _ ⟨w, rfl⟩
    exact ⟨C'.ι w, by simp⟩
  have hCf : C.IsContractedBy f := fun z hz =>
    Eq.trans (b := x) (hclF hz) (Eq.symm (hclF (subset_closure rfl : ι y' ∈ closure {ι y'})))
  refine ⟨C, hCf, hclF, ?_, ?_⟩
  · rw [hrC]
    exact fun h => hy'S (h (subset_closure rfl))
  · refine ⟨p, ?_, hpS⟩
    rw [hrC, ← hp']
    exact specializes_iff_mem_closure.mp (hy'p'.map ι.continuous)

end FibreCurves

section LocalDegree

variable {k : Type v} [Field k] {X : Scheme.{v}} (sX : X ⟶ Spec (.of k)) [QuasiCompact sX]
  [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X]

/-- No generic point of an irreducible component of an open subscheme of an integral scheme lies on
the support of a divisor. -/
private theorem ι_componentGenericPoint_notMem_supp (D : Divisor X) (U : X.Opens) [Nonempty U]
    (Z : irreducibleComponents U.toScheme) : U.ι (componentGenericPoint U.toScheme Z) ∉ D.supp := by
  intro hZ
  obtain ⟨P, -, hxP⟩ := DivisorWithCoeffs.mem_supp_iff.1 hZ
  rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint,
    genericPoint_eq_of_isOpenImmersion] at hxP
  obtain ⟨Z0⟩ : Nonempty (irreducibleComponents X) :=
    ⟨⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; rfl⟩⟩
  exact MMP.Flips.componentGenericPoint_notMem_support Z0 P
    (by rwa [MMP.Fourfold.componentGenericPoint_eq_genericPoint])

/-- The image of a prime divisor of an open subscheme has its generic point in the open. -/
private theorem genericPoint_primeDivisorMap_mem (U : X.Opens)
    (E : MMP.Mori.PrimeDivisor U.toScheme) :
    MMP.Mori.PrimeDivisor.genericPoint (OpenWeilRestriction.primeDivisorMap U.ι E) ∈ U := by
  rw [show MMP.Mori.PrimeDivisor.genericPoint (OpenWeilRestriction.primeDivisorMap U.ι E) =
    U.ι E.genericPoint from OpenWeilRestriction.genericPoint_primeDivisorMap U.ι E]
  change _ ∈ (U : Set X)
  rw [← Scheme.Opens.range_ι U]
  exact ⟨_, rfl⟩

/-- If the coefficients of `D'` on `U` are those of `D` at the image prime divisors, a point of `U`
lies on `Supp D'` exactly when its image lies on `Supp D`. -/
private theorem mem_supp_iff_ι_mem_supp_of_coeff_eq (D : Divisor X) (U : X.Opens) [Nonempty U]
    (D' : Divisor U.toScheme)
    (hcoeff : ∀ E : MMP.Mori.PrimeDivisor U.toScheme,
      D'.coeff E = D.coeff (OpenWeilRestriction.primeDivisorMap U.ι E)) (v : U.toScheme) :
    v ∈ D'.supp ↔ U.ι v ∈ D.supp := by
  refine ⟨fun hv => ?_, fun hv => ?_⟩
  · obtain ⟨E, hE, hvE⟩ := DivisorWithCoeffs.mem_supp_iff.1 hv
    refine DivisorWithCoeffs.mem_supp_iff.2 ⟨OpenWeilRestriction.primeDivisorMap U.ι E,
      by rwa [← hcoeff], ?_⟩
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hvE ⊢
    rw [OpenWeilRestriction.genericPoint_primeDivisorMap]
    exact specializes_iff_mem_closure.mp
      ((specializes_iff_mem_closure.mpr hvE).map U.ι.continuous)
  · obtain ⟨P, hP, hvP⟩ := DivisorWithCoeffs.mem_supp_iff.1 hv
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hvP
    have hsp : P.genericPoint ⤳ U.ι v := specializes_iff_mem_closure.mpr hvP
    have hPU : MMP.Mori.PrimeDivisor.genericPoint P ∈ U :=
      hsp.mem_open U.isOpen (by
        rw [← Scheme.Opens.range_ι U]
        exact ⟨v, rfl⟩)
    obtain ⟨E, rfl⟩ := MMP.Threefold.Resolution.exists_primeDivisorMap_eq U P hPU
    refine DivisorWithCoeffs.mem_supp_iff.2 ⟨E, by rwa [hcoeff], ?_⟩
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    rw [show MMP.Mori.PrimeDivisor.genericPoint (OpenWeilRestriction.primeDivisorMap U.ι E) =
      U.ι E.genericPoint from OpenWeilRestriction.genericPoint_primeDivisorMap U.ι E] at hsp
    exact specializes_iff_mem_closure.mp (U.ι.isOpenEmbedding.isInducing.specializes_iff.mp hsp)

/-- **Positivity of the degree, locally.** Let `D` be a Cartier divisor on a normal integral
scheme `X` quasi-compact over `k`, effective along the prime divisors meeting an open `U`, and
`C ⊆ U` a proper curve not contained in `Supp D` but meeting it. Then `deg_C 𝒪_X(D) > 0`. -/
private theorem degreeOn_pos_of_nonneg_of_closure_subset (D : Divisor X) (hD : D.IsCartier)
    (U : X.Opens) (hU : ∀ E : MMP.Mori.PrimeDivisor X, E.genericPoint ∈ U → 0 ≤ D.coeff E)
    (C : ProperCurve sX) (hCU : closure {C.point} ⊆ (U : Set X)) (hCD : C.point ∉ D.supp)
    (hmeet : (closure {C.point} ∩ (D.supp : Set X)).Nonempty) :
    0 < D.degreeOn k sX C.ι C.dim_le hD := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : AlgebraicGeometry.IsNoetherian X := {}
  have : Nonempty U := ⟨⟨C.point, hCU (subset_closure rfl)⟩⟩
  have : CompactSpace U := isCompact_iff_compactSpace.mp (NoetherianSpace.isCompact _)
  have : QuasiCompact (U.ι ≫ sX) := inferInstance
  have hB := ι_componentGenericPoint_notMem_supp D U
  set D' := Divisor.pullback (f := U.ι) D hD hB
  have hp := Divisor.isPullback_pullback (f := U.ι) hD hB
  have hD'c : D'.IsCartier := hp.isCartier hD
  have hcoeff : ∀ E : MMP.Mori.PrimeDivisor U.toScheme,
      D'.coeff E = D.coeff (OpenWeilRestriction.primeDivisorMap U.ι E) := fun E =>
    MMP.Positivity.coeff_eq_of_isPullback E _
      (OpenWeilRestriction.genericPoint_primeDivisorMap U.ι E).symm hD hp
  have hD'0 : 0 ≤ D' := fun E => by
    change 0 ≤ D'.coeff E
    rw [hcoeff E]
    exact hU _ (genericPoint_primeDivisorMap_mem U E)
  have hsupp := mem_supp_iff_ι_mem_supp_of_coeff_eq D U D' hcoeff
  obtain ⟨CV, hCV⟩ := MMP.Threefold.Resolution.exists_properCurve_of_closure_subset k U C hCU
  obtain ⟨e, he⟩ := MMP.Threefold.Resolution.exists_curveSubschemeAt_iso U.ι CV.point hCV (by
    rwa [Scheme.Opens.range_ι])
  have : IsProper ((CV.ι ≫ U.ι) ≫ sX) := by
    rw [Category.assoc]
    infer_instance
  have := hD.isInvertibleModule_divisorialSheaf
  have := hD'c.isInvertibleModule_divisorialSheaf
  have h1 := MMP.Threefold.Resolution.degreeOn_eq_of_iso_comp k sX C.ι (CV.ι ≫ U.ι) C.dim_le
    CV.dim_le e.symm (by rw [Iso.symm_hom, Iso.inv_comp_eq]; exact he.symm) D.divisorialSheaf
  have h2 := MMP.Threefold.Resolution.degreeOn_comp k sX U.ι CV.ι CV.dim_le D.divisorialSheaf
  have h3 := MMP.Mori.degreeOn_eq_of_iso k (U.ι ≫ sX) CV.ι CV.dim_le
    (hp.divisorialSheafIso (hBc := hD)).symm
  rw [show D.degreeOn k sX C.ι C.dim_le hD = D'.degreeOn k (U.ι ≫ sX) CV.ι CV.dim_le hD'c from
    h1.trans (h2.trans h3)]
  have hrange : ∀ v : U.toScheme, v ∈ Set.range CV.ι ↔ U.ι v ∈ closure {C.point} := fun v => by
    rw [CV.range_ι, ← hCV, ← specializes_iff_mem_closure, ← specializes_iff_mem_closure,
      U.ι.isOpenEmbedding.isInducing.specializes_iff]
  obtain ⟨c₀, hc₀⟩ := MMP.Threefold.Mori.exists_ι_eq_point CV.point
  have hne : ∃ c, CV.ι c ∉ D'.supp :=
    ⟨c₀, by rwa [show CV.ι c₀ = CV.point from hc₀, hsupp, hCV]⟩
  obtain ⟨hnn, hiff⟩ := MMP.Threefold.Mori.degreeOn_nonneg_and_eq_zero_iff (U.ι ≫ sX) CV.ι
    CV.dim_le D' hD'c hD'0 hne
  refine lt_of_le_of_ne hnn fun h0 => ?_
  obtain ⟨x, hxC, hxD⟩ := hmeet
  obtain ⟨v, rfl⟩ : x ∈ Set.range U.ι := by rw [Scheme.Opens.range_ι]; exact hCU hxC
  obtain ⟨c, hc⟩ := (hrange v).2 hxC
  exact hiff.1 h0.symm c (by rwa [hc, hsupp])

end LocalDegree

section Perturbation

/-- If `g < 0` forces `-g / o ≤ -g₀ / o₀`, then `0 ≤ o₀ g + (-g₀) o` for `o ≥ 0`, `o₀ ≥ 1`,
`g₀ < 0`. -/
private theorem zero_le_mul_add_neg_mul {g o g₀ o₀ : ℤ} (ho₀ : 1 ≤ o₀) (hg₀ : g₀ < 0) (ho : 0 ≤ o)
    (hmax : g < 0 → 1 ≤ o ∧ (-(g : ℚ)) / (o : ℚ) ≤ (-(g₀ : ℚ)) / (o₀ : ℚ)) :
    0 ≤ o₀ * g + (-g₀) * o := by
  rcases lt_or_ge g 0 with hg | hg
  · obtain ⟨ho₁, h1⟩ := hmax hg
    rw [div_le_div_iff₀ (by exact_mod_cast ho₁) (by exact_mod_cast ho₀)] at h1
    have : (0 : ℚ) ≤ o₀ * g + (-g₀) * o := by push_cast; nlinarith
    exact_mod_cast this
  · nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ o₀) hg]

/-- **The perturbed fibre argument.** Let `h : Z ⟶ Y` be a proper birational morphism of normal
varieties over `k`, `y` a closed point of `Y` in an open `V`, and `G` a Cartier divisor on `Z`
whose components meeting `h⁻¹ V` with negative coefficient all lie over `y`, at least one of them
`Γ₀`. Let `ψ` be a rational function on `Z` regular along `h⁻¹ V`, vanishing along every prime
divisor over `y` and along a prime divisor `E₁` with `0 ≤ g_{E₁}` whose closure meets the fibre
over `y`. Then some proper curve `C` contracted by `h` has `deg_C G > 0`. -/
private theorem exists_isContractedBy_degreeOn_pos_of_ord (k : Type v) [Field k] {Y Z : Scheme.{v}}
    (sY : Y ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k)) [QuasiCompact sZ] [IsLocallyNoetherian Z]
    [IsNormal Z] (hY : IsNormalVariety k sY) (hZ : IsNormalVariety k sZ)
    (h : Z ⟶ Y) (hh : h ≫ sY = sZ) [IsProper h] (hhb : IsBirationalMorphism h)
    {G : Divisor Z} (hGc : G.IsCartier) {y : Y} (hycl : IsClosed ({y} : Set Y)) {V : Y.Opens}
    (hyV : y ∈ V)
    (hnegy : ∀ E : MMP.Mori.PrimeDivisor Z, E.genericPoint ∈ h ⁻¹ᵁ V → G.coeff E < 0 →
      h E.genericPoint = y)
    {Γ₀ : MMP.Mori.PrimeDivisor Z} (hΓ₀y : h Γ₀.genericPoint = y) (hΓ₀ : G.coeff Γ₀ < 0)
    (ψ : (RationalFunctions Z)ˣ)
    (hψ : ∀ E : MMP.Mori.PrimeDivisor Z, E.genericPoint ∈ h ⁻¹ᵁ V → 0 ≤ E.ord ψ)
    (hψy : ∀ E : MMP.Mori.PrimeDivisor Z, h E.genericPoint = y → 1 ≤ E.ord ψ)
    {E₁ : MMP.Mori.PrimeDivisor Z} (hg₁ : 0 ≤ G.coeff E₁) (ho₁ : 1 ≤ E₁.ord ψ)
    (hE₁y : y ∈ h.base '' closure {E₁.genericPoint}) :
    ∃ C : ProperCurve sZ, C.IsContractedBy h ∧ 0 < G.degreeOn k sZ C.ι C.dim_le hGc := by
  classical
  have : IsIntegral Z := hZ.1.toIsIntegral
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  -- the most negative ratio `-g_E / o_E` over `y`
  set S := G.support.filter fun E => G.coeff E < 0 ∧ h E.genericPoint = y
  have hS : ∀ E, G.coeff E < 0 → h E.genericPoint = y → E ∈ S := fun E hE hEy =>
    Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hE.ne, hE, hEy⟩
  obtain ⟨E₀, hE₀S, hmax⟩ := S.exists_max_image
    (fun E => (-(G.coeff E : ℚ)) / (E.ord ψ : ℚ)) ⟨Γ₀, hS Γ₀ hΓ₀ hΓ₀y⟩
  obtain ⟨-, hg₀, hE₀y⟩ := Finset.mem_filter.mp hE₀S
  have ho₀ := hψy E₀ hE₀y
  set g₀ := G.coeff E₀
  set o₀ := E₀.ord ψ
  -- `G'' = o₀ G - g₀ div ψ`, effective along `h⁻¹ V`, with no `E₀`
  set G'' : Divisor Z := o₀ • G + (-g₀) • principalDivisor ψ
  have hG''c : G''.IsCartier :=
    (hGc.zsmul o₀).add ((Divisor.isCartier_principalDivisor ψ).zsmul (-g₀))
  have hG''coeff : ∀ E, G''.coeff E = o₀ * G.coeff E + (-g₀) * E.ord ψ := fun E => by
    simp only [G'', DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul,
      coeff_principalDivisor, smul_eq_mul]
  have hU : ∀ E : MMP.Mori.PrimeDivisor Z, E.genericPoint ∈ h ⁻¹ᵁ V → 0 ≤ G''.coeff E :=
    fun E hEV => by
      rw [hG''coeff]
      exact zero_le_mul_add_neg_mul ho₀ hg₀ (hψ E hEV) fun hE =>
        ⟨hψy E (hnegy E hEV hE), hmax E (hS E hE (hnegy E hEV hE))⟩
  -- `E₁` lies in `Supp G''` and meets the fibre `F` over `y`, which `E₀` does not lie in
  set F : Set Z := h.base ⁻¹' {y}
  have hmeet : (F ∩ (G''.supp : Set Z)).Nonempty := by
    obtain ⟨z, hz, hzy⟩ := hE₁y
    refine ⟨z, hzy, DivisorWithCoeffs.mem_supp_iff.mpr ⟨E₁, ?_, ?_⟩⟩
    · rw [hG''coeff]
      nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ o₀) hg₁]
    · rwa [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  have hsub : ¬ F ⊆ (G''.supp : Set Z) := fun hF => by
    obtain ⟨E, hE, hE₀E⟩ := DivisorWithCoeffs.mem_supp_iff.mp
      (hF (show E₀.genericPoint ∈ F from hE₀y))
    rw [MMP.Threefold.Mori.primeDivisor_eq_of_genericPoint_mem_support E E₀ hE₀E, hG''coeff]
      at hE
    exact hE (by ring)
  -- a curve in the fibre meeting `Supp G''` without lying in it
  obtain ⟨C, hCf, hCF, hCS, hCmeet⟩ := exists_properCurve_isContractedBy k sY sZ hY hZ h hh hhb y
    hycl G''.supp.isClosed hmeet hsub
  have hCU : closure {C.point} ⊆ ((h ⁻¹ᵁ V : Z.Opens) : Set Z) := fun z hz => by
    change h z ∈ V
    rwa [show h z = y from hCF hz]
  have hCpt : C.point ∉ G''.supp := fun hc => hCS (by
    rw [C.range_ι]
    exact (G''.supp.isClosed.closure_subset_iff).mpr (Set.singleton_subset_iff.mpr hc))
  have hpos := degreeOn_pos_of_nonneg_of_closure_subset sZ G'' hG''c (h ⁻¹ᵁ V) hU C hCU hCpt
    (C.range_ι ▸ hCmeet)
  -- `deg_C G'' = o₀ deg_C G`, since `div ψ` is principal
  rw [Divisor.degreeOn_add k sZ C.ι C.dim_le _ _ (hGc.zsmul o₀)
      ((Divisor.isCartier_principalDivisor ψ).zsmul (-g₀)),
    MMP.Fourfold.degreeOn_zsmul sZ C.ι C.dim_le G hGc o₀,
    MMP.Fourfold.degreeOn_zsmul sZ C.ι C.dim_le _ (Divisor.isCartier_principalDivisor ψ) (-g₀),
    MMP.Flips.Divisor.degreeOn_eq_zero_of_linearlyEquivalent sZ C.ι C.dim_le _
      (Divisor.linearlyEquivalent_principalDivisor_zero ψ), mul_zero, add_zero] at hpos
  exact ⟨C, hCf, pos_of_mul_pos_right hpos (by omega)⟩

/-- Let `h : Z ⟶ Y` be a proper birational morphism of normal surfaces over `k` and `G` a Cartier
divisor on `Z` with a component of negative coefficient, every such component lying over a closed
point of `Y`. Then some proper curve `C` contracted by `h` has `deg_C G > 0`. -/
private theorem exists_isContractedBy_degreeOn_pos (k : Type v) [Field k] {Y Z : Scheme.{v}}
    (sY : Y ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k)) [QuasiCompact sZ] [IsLocallyNoetherian Z]
    [IsNormal Z] (hY : IsNormalVariety k sY) (hZ : IsNormalVariety k sZ)
    (hYdim : topologicalKrullDim Y = 2) (h : Z ⟶ Y) (hh : h ≫ sY = sZ) [IsProper h]
    (hhb : IsBirationalMorphism h) {G : Divisor Z} (hGc : G.IsCartier)
    (hcl : ∀ E, G.coeff E < 0 → IsClosed ({h E.genericPoint} : Set Y))
    {Γ₀ : MMP.Mori.PrimeDivisor Z} (hΓ₀ : G.coeff Γ₀ < 0) :
    ∃ C : ProperCurve sZ, C.IsContractedBy h ∧ 0 < G.degreeOn k sZ C.ι C.dim_le hGc := by
  classical
  have : IsIntegral Y := hY.1.toIsIntegral
  have : IsIntegral Z := hZ.1.toIsIntegral
  have : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := hY.isLocallyNoetherian
  have : IsNormal Y := hY.2
  have : IsDominant h := hhb.isDominant
  set y := h Γ₀.genericPoint
  have hycl : IsClosed ({y} : Set Y) := hcl Γ₀ hΓ₀
  -- an affine neighbourhood `V` of `y` meeting no other image of a negative component
  set N := G.support.filter fun E => G.coeff E < 0 ∧ h E.genericPoint ≠ y
  set T : Set Y := ⋃ E ∈ (N : Set (MMP.Mori.PrimeDivisor Z)), {h E.genericPoint}
  have hTcl : IsClosed T := Set.Finite.isClosed_biUnion (Finset.finite_toSet N)
    fun E hE => hcl E (Finset.mem_filter.mp hE).2.1
  have hyT : y ∉ T := by
    simp only [T, Set.mem_iUnion, Set.mem_singleton_iff, not_exists]
    exact fun E hE hEy => (Finset.mem_filter.mp hE).2.2 hEy.symm
  obtain ⟨V, hV, hyV, hVT⟩ := exists_isAffineOpen_mem_and_subset
    (U := ⟨Tᶜ, hTcl.isOpen_compl⟩) (show y ∈ (⟨Tᶜ, hTcl.isOpen_compl⟩ : Y.Opens) from hyT)
  have hnegy : ∀ E : MMP.Mori.PrimeDivisor Z, E.genericPoint ∈ h ⁻¹ᵁ V → G.coeff E < 0 →
      h E.genericPoint = y := fun E hEV hE => by_contra fun hne => hVT hEV
    (Set.mem_biUnion (Finset.mem_coe.mpr (Finset.mem_filter.mpr
      ⟨Finsupp.mem_support_iff.mpr hE.ne, hE, hne⟩)) rfl)
  -- a prime divisor `P` through `y` and a section `φ` on `V` vanishing along `P`
  obtain ⟨P, hPy⟩ := exists_primeDivisor_specializes sY hYdim hycl
  have hPV : P.genericPoint ∈ V := hPy.mem_open V.isOpen hyV
  obtain ⟨φ, hφ0, hφP⟩ := exists_ne_zero_germ_mem_maximalIdeal hV P hPV
  -- its pull-back `ψ` to `Z`
  have ha : ∀ (W : irreducibleComponents Z) (hW : componentGenericPoint Z W ∈ h ⁻¹ᵁ V),
      Z.presheaf.germ (h ⁻¹ᵁ V) _ hW (h.app V φ) ≠ 0 := fun W hW =>
    germ_app_ne_zero h φ hφ0 _ hW (by
      rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint]
      exact map_genericPoint_of_isDominant h)
  have hψ1 : ∀ (E : MMP.Mori.PrimeDivisor Z) (x : Y) (hx : x ∈ V), h E.genericPoint = x →
      Y.presheaf.germ V x hx φ ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk x) →
      1 ≤ E.ord (MMP.Threefold.Resolution.sectionUnit _ ha) := by
    rintro E x hx rfl hm
    exact MMP.Threefold.Resolution.one_le_ord_sectionUnit _ ha E hx
      (not_isUnit_germ_app h φ _ hx hm)
  -- the strict transform `E₁` of `P`
  obtain ⟨E₁, hE₁, -, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{v, 0} hY (f := h)
      (by rwa [hh]) hhb P
  have hE₁y : y ∈ h.base '' closure {E₁.genericPoint} :=
    hPy.mem_closed (h.isClosedMap _ isClosed_closure) ⟨E₁.genericPoint, subset_closure rfl, hE₁⟩
  exact exists_isContractedBy_degreeOn_pos_of_ord k sY sZ hY hZ h hh hhb hGc hycl hyV hnegy rfl hΓ₀
    _ (MMP.Threefold.Resolution.ord_sectionUnit_nonneg _ ha)
    (fun E hE => hψ1 E y hyV hE (germ_mem_maximalIdeal_of_specializes φ hPy hPV hyV hφP))
    (not_lt.mp fun h1 => not_isClosed_genericPoint sY hYdim P (hE₁ ▸ hcl E₁ h1))
    (hψ1 E₁ _ hPV hE₁ hφP) hE₁y

/-- If `-B` is `h`-nef and `G = mB` is Cartier with `m > 0`, then `deg_C G ≤ 0` on every proper
curve `C` contracted by `h`. -/
private theorem degreeOn_nonpos_of_isRelativelyNef_neg (k : Type v) [Field k] {Y Z : Scheme.{v}}
    (sZ : Z ⟶ Spec (.of k)) [QuasiCompact sZ] [IsLocallyNoetherian Z] [IsNormal Z] [IsIntegral Z]
    (h : Z ⟶ Y) {B : QDivisor Z} (hB : B.IsQCartier) (hnef : (-B).IsRelativelyNef sZ h)
    {m : ℕ} (hm : 0 < m) {G : Divisor Z} (hGc : G.IsCartier)
    (hGB : Divisor.toQDivisor G = (m : ℤ) • B) (C : ProperCurve sZ) (hC : C.IsContractedBy h) :
    G.degreeOn k sZ C.ι C.dim_le hGc ≤ 0 := by
  have hn := MMP.Fourfold.QDivisor.IsRelativelyNef.intersectionNumber_nonneg sZ hnef hnef.1 C hC
  have hBB := QDivisor.intersectionNumber_add' k sZ C.ι C.dim_le B (-B) hB hnef.1
    (by rw [add_neg_cancel]; exact QDivisor.isQCartier_zero)
  rw [MMP.Fourfold.intersectionNumber_congr sZ C.ι C.dim_le _ QDivisor.isQCartier_zero
    (add_neg_cancel B), MMP.Fourfold.intersectionNumber_zero,
    QDivisor.intersectionNumber_eq_of_smul k sZ C.ι C.dim_le B hB hm G hGc hGB] at hBB
  have : (G.degreeOn k sZ C.ι C.dim_le hGc : ℚ) / m ≤ 0 := by linarith
  rw [div_le_iff₀ (by exact_mod_cast hm), zero_mul] at this
  exact_mod_cast this

end Perturbation

end MMP.Mori.NegativityLemmaSurface

namespace MMP.Mori

open CategoryTheory AlgebraicGeometry TopologicalSpace NegativityLemmaSurface

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- **Negativity lemma for surfaces.** Let `h : Z ⟶ Y` be a proper birational morphism of
normal surfaces over `k` and `B` a `ℚ`-Cartier `ℚ`-divisor on `Z` with `-B` `h`-nef. If the
pushforward `h_* B` is effective, then `B` is effective. -/
@[mmp "lem_km2a_negativity_lemma_surface"]
public theorem QDivisor.isEffective_of_isRelativelyNef_neg_of_isEffective_transformDivisor
    (k : Type u) [Field k] {Y Z : Scheme.{u}} (sY : Y ⟶ Spec (.of k))
    (sZ : Z ⟶ Spec (.of k)) [QuasiCompact sZ] [IsLocallyNoetherian Z] [IsNormal Z]
    (hY : IsNormalVariety k sY) (hZ : IsNormalVariety k sZ)
    (hYdim : topologicalKrullDim Y = 2) (hZdim : topologicalKrullDim Z = 2)
    (h : Z ⟶ Y) (hh : h ≫ sY = sZ) [IsProper h] (hhb : IsBirationalMorphism h)
    {B : QDivisor Z} (hB : B.IsQCartier) (hnef : (-B).IsRelativelyNef sZ h)
    (heff : (RationalMap.transformDivisor (X := Z) h.toRationalMap B).IsEffective) :
    B.IsEffective := by
  have : IsIntegral Z := hZ.1.toIsIntegral
  -- an integral Cartier multiple `G = mB`, with the signs of `B`
  obtain ⟨m, hm, G, hGB, hGc⟩ := hB.exists_pos
  have hneg : ∀ E, G.coeff E < 0 ↔ B.coeff E < 0 := fun E => by
    have h1 := congrArg (fun D : QDivisor Z => D E) hGB
    simp only [Finsupp.smul_apply, zsmul_eq_mul, Int.cast_natCast] at h1
    have hc : (G.coeff E : ℚ) = m * B.coeff E := by rwa [← Divisor.coeff_toQDivisor]
    rw [← Int.cast_lt (R := ℚ), hc, Int.cast_zero,
      Rat.mul_neg_iff_of_pos_left (by exact_mod_cast hm)]
  intro E
  by_contra hE
  obtain ⟨C, hC, hpos⟩ := exists_isContractedBy_degreeOn_pos k sY sZ hY hZ hYdim h hh hhb hGc
    (fun E hE => not_not.mp fun hc => ((hneg E).1 hE).not_ge
      (coeff_nonneg_of_not_isClosed k sY sZ hY hZ hYdim h hh hhb heff E hc))
    ((hneg E).2 (not_le.mp hE))
  exact hpos.not_ge (degreeOn_nonpos_of_isRelativelyNef_neg k sZ h hB hnef hm hGc hGB C hC)

end MMP.Mori
