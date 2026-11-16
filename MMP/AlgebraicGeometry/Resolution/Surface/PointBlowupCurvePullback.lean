module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Resolution.OrderAlongExceptional
public import MMP.AlgebraicGeometry.Divisor.Pullback
public import MMP.AlgebraicGeometry.Divisor.Arithmetic
public import MMP.AlgebraicGeometry.Morphisms.Birational.Transform
public import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
public import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.Corollaries
public import MMP.AlgebraicGeometry.Intersection.Surface.Symmetry
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
public import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
public import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
public import MMP.AlgebraicGeometry.Resolution.Blowup.VarietyProjective
public import MMP.AlgebraicGeometry.MMP.Threefold.SurfaceLocalRings
public import StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.ComponentOrder
public import StacksFrontier.AlgebraicGeometry.Picard.ClosedPointDegreeOne
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.ProperBirationalPointBlowups
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.RegularLocalRingRational
public import MMP.AlgebraicGeometry.Chow.FieldSituation

/-!
# Pulling back a curve through the blow-up of a point of a smooth surface

Let `Y` be a smooth surface over an algebraically closed field `k`, `y ∈ Y` a closed point,
`π : Y' = B_y Y ⟶ Y` the blow-up of the reduced point `y` and `F = π⁻¹(y)` its exceptional
curve. For a curve `C ⊆ Y` with strict transform `C' = π⁻¹_* C`,
`π^*C = C' + (mult_y C) F`, and by linearity `π^*B = π⁻¹_* B + (mult_y B) F` for every
`ℚ`-divisor `B` of `Y`.

The coefficient of a prime divisor `E ⊆ Y'` in `π^*C` is the order `ord((π^*I_C)_{η_E})` of the
stalk of the inverse image ideal of `C` in the discrete valuation ring `𝒪_{Y',E}`
(`MMP.Threefold.Resolution.coeff_isPullback_single_eq_idealOrder`): a local equation `f` of `C`
generates `I_C` near `π(η_E)`, and its pull-back generates `π^*I_C` at `η_E`. Along `F`, this
order is the order of `I_{C,y}` in `𝒪_{Y,y}`, that is `mult_y C`
(`MMP.Resolution.orderAlong_comap_blowUpToBase_eq`, the order along the exceptional divisor of a
smooth blow-up). Away from `F`, `π` is an isomorphism over `π(η_E) ≠ y`, so the stalk of `π^*I_C`
at `η_E` is that of `I_C` at `π(η_E)`, which is the maximal ideal of `𝒪_{Y,C}` if `π(η_E)` is the
generic point of `C` and the unit ideal otherwise; and `π(η_E)` is the generic point of `C`
exactly when `E` is the strict transform of `C`.

## Main results

* `MMP.Threefold.Resolution.coeff_isPullback_single_eq_idealOrder`: the coefficients of the
  pull-back of a prime divisor with invertible ideal sheaf, along any morphism of normal schemes.
* `MMP.Threefold.Resolution.isPullback_single_blowUp_singleton`,
  `MMP.Threefold.Resolution.isPullback_blowUp_singleton`,
  `MMP.Threefold.Resolution.isPullback_qDivisor_blowUp_singleton`: `π^*C = C' + (mult_y C) F`
  for prime divisors, divisors and `ℚ`-divisors, as pull-back relations.
* `MMP.Threefold.Resolution.pullback_single_blowUp_singleton`,
  `MMP.Threefold.Resolution.pullback_qDivisor_blowUp_singleton`: the same as equalities of
  divisors.

## Implementation notes

A *smooth surface* is a variety `Y` over `k` with `MMP.Mori.IsSmoothScheme sY` and
`topologicalKrullDim Y = 2`. The field is algebraically closed, as in the source's standing
hypotheses; a perfect field already makes the reduced point `y` smooth over `k`, so that `π` is a
smooth blow-up. The blow-up is `AlgebraicGeometry.blowUp` of the reduced point
`Scheme.IdealSheafData.vanishingIdeal {y}`, with structure morphism
`AlgebraicGeometry.blowUpToBase`; the exceptional curve is any prime divisor `F` whose ideal
sheaf is `AlgebraicGeometry.exceptionalIdeal` (such a prime divisor exists and is unique,
`MMP.Resolution.exceptionalPrimeDivisor`). The pull-back of (`ℚ`-)Cartier divisors is
`MMP.Mori.Divisor.pullback` (`MMP.Mori.QDivisor.pullback`), the strict transform is
`MMP.Mori.inverseTransformDivisor`, and `mult_y` is `MMP.Mori.PrimeDivisor.multiplicityAt`,
extended linearly (`MMP.Mori.DivisorWithCoeffs.multiplicityAt`). The multiplicity of a curve is
by definition the order of its ideal at `y`; this is the order of a local equation, so the
associated graded ring of `𝒪_{Y,y}`, which identifies it with the multiplicity of `C` in the sense
of Hilbert–Samuel, is not needed here.

## References

* [J. Kollár, *Lectures on resolution of singularities*][KollarResolution], 1.36–1.38, 3.47
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Threefold.Resolution

section Setup

variable {k : Type u} [Field k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k))

/-- The reduced closed point `{y}` is the closure of `y`. -/
theorem closeds_singleton_eq_closure {y : Y} (hy : IsClosed ({y} : Set Y)) :
    (⟨{y}, hy⟩ : Closeds Y) = Closeds.closure ({y} : Set Y) :=
  Closeds.ext (by simp)

/-- Over a perfect field `k`, a closed point `y` of a `k`-scheme locally of finite type is smooth
over `k`: `κ(y)` is a finite extension of `k` (the Nullstellensatz), hence separable, so
`Spec κ(y) ⟶ Spec k` is étale. -/
theorem smooth_fromSpecResidueField_comp [PerfectField k] [LocallyOfFiniteType sY] {y : Y}
    (hy : IsClosed ({y} : Set Y)) : Smooth (Y.fromSpecResidueField y ≫ sY) := by
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace sY
  have := isClosed_singleton_iff_locallyOfFiniteType.mp hy
  have hlft : LocallyOfFiniteType (Y.fromSpecResidueField y ≫ sY) := inferInstance
  rw [← Spec.map_preimage (Y.fromSpecResidueField y ≫ sY)] at hlft ⊢
  letI := (Spec.preimage (Y.fromSpecResidueField y ≫ sY)).hom.toAlgebra
  have : Algebra.FiniteType k (Y.residueField y) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hlft
  have : Module.Finite k (Y.residueField y) := finite_of_finite_type_of_isJacobsonRing _ _
  have : Algebra.Etale k (Y.residueField y) :=
    ⟨Algebra.FormallyEtale.of_isSeparable _ _, Algebra.FinitePresentation.of_finiteType.mp ‹_›⟩
  have : Etale (Spec.map (Spec.preimage (Y.fromSpecResidueField y ≫ sY))) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (RingHom.etale_algebraMap.mpr this)
  infer_instance

/-- Over a perfect field, the blow-up of a closed point of a smooth `k`-scheme is a smooth
blow-up: the reduced point is `Spec κ(y)`, which is smooth over `k`. -/
theorem isSmoothBlowup_vanishingIdeal_singleton [PerfectField k]
    [LocallyOfFiniteType sY] (hYs : IsSmoothScheme sY) {y : Y} (hy : IsClosed ({y} : Set Y)) :
    MMP.Resolution.IsSmoothBlowup sY (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) := by
  refine ⟨hYs, ?_⟩
  have := isClosed_singleton_iff_isClosedImmersion.mp hy
  have hker : (Y.fromSpecResidueField y).ker =
      Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩ := by
    have : IsReduced (Y.fromSpecResidueField y).ker.subscheme :=
      isReduced_of_isOpenImmersion (inv (Y.fromSpecResidueField y).toImage)
    refine Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme _ _ ?_
    apply SetLike.coe_injective
    rw [Scheme.Hom.support_ker, Scheme.range_fromSpecResidueField]
    exact hy.closure_eq
  have := smooth_fromSpecResidueField_comp sY hy
  have e : (Y.fromSpecResidueField y).ker.subschemeι ≫ sY =
      inv (Y.fromSpecResidueField y).toImage ≫ Y.fromSpecResidueField y ≫ sY := by
    rw [IsIso.eq_inv_comp, ← Category.assoc]
    exact congrArg (· ≫ sY) (Scheme.Hom.toImage_imageι _)
  rw [← hker, e]
  exact MMP.Resolution.isSmoothScheme_of_smooth _

/-- The support of the vanishing ideal of a closed point `y` is `{y}`. -/
theorem support_vanishingIdeal_singleton {y : Y} (hy : IsClosed ({y} : Set Y)) :
    ((Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)).support : Set Y) = {y} := by
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl

/-- The support of the vanishing ideal of a closed point is irreducible. -/
theorem isIrreducible_support_vanishingIdeal_singleton {y : Y} (hy : IsClosed ({y} : Set Y)) :
    IsIrreducible ((Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)).support :
      Set Y) := by
  rw [support_vanishingIdeal_singleton hy]
  exact isIrreducible_singleton

/-- A closed point of a scheme of dimension two is not the whole space. -/
theorem singleton_ne_univ_of_topologicalKrullDim_eq_two (hYd : topologicalKrullDim Y = 2)
    (y : Y) : ({y} : Set Y) ≠ Set.univ := by
  intro heq
  have : Subsingleton Y := ⟨fun a b => (heq.symm ▸ Set.mem_univ a : a ∈ ({y} : Set Y)).trans
    (heq.symm ▸ Set.mem_univ b : b ∈ ({y} : Set Y)).symm⟩
  have h0 := topologicalKrullDim_zero_of_discreteTopology Y
  rw [hYd] at h0
  exact absurd h0 (by decide)

/-- In an irreducible scheme of dimension two, a closed point has codimension `≥ 1`. -/
theorem one_le_codimension_vanishingIdeal_singleton [IrreducibleSpace Y]
    (hYd : topologicalKrullDim Y = 2) {y : Y} (hy : IsClosed ({y} : Set Y)) :
    1 ≤ codimension (⟨(Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)).support,
      isIrreducible_support_vanishingIdeal_singleton hy,
      (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)).support.isClosed⟩ :
        IrreducibleCloseds Y) := by
  rw [codimension_eq_coheight, Order.one_le_iff_ne_zero, Order.coheight_ne_zero]
  intro hmax
  have hle : (⟨(Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)).support,
      isIrreducible_support_vanishingIdeal_singleton hy,
      (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)).support.isClosed⟩ :
        IrreducibleCloseds Y) ≤ ⟨Set.univ, IrreducibleSpace.isIrreducible_univ Y, isClosed_univ⟩ :=
    fun _ _ => trivial
  have heq : (Set.univ : Set Y) ⊆ {y} := by
    have h := hmax hle
    intro a ha
    have : a ∈ ((Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)).support :
      Set Y) := h ha
    rwa [support_vanishingIdeal_singleton hy] at this
  exact singleton_ne_univ_of_topologicalKrullDim_eq_two hYd y (Set.eq_univ_of_univ_subset heq)

end Setup

/-! ### The order of an ideal in a discrete valuation ring -/

section IdealOrder

open IsLocalRing MMP.Resolution

/-- The order is invariant under ring isomorphisms of local rings. -/
theorem idealOrder_map_ringEquiv {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S]
    [IsLocalRing S] (e : R ≃+* S) (I : Ideal R) : idealOrder (I.map e) = idealOrder I := by
  have hm : (maximalIdeal R).map e = maximalIdeal S := map_ringEquiv_maximalIdeal e
  have key : ∀ j : ℕ, I.map e ≤ maximalIdeal S ^ j ↔ I ≤ maximalIdeal R ^ j := by
    intro j
    rw [← hm, ← Ideal.map_pow, Ideal.map_le_iff_le_comap, Ideal.comap_map_of_bijective _
      e.bijective]
  simp only [idealOrder, key]

/-- The unit ideal has order `0`. -/
theorem idealOrder_top {R : Type*} [CommRing R] [IsLocalRing R] : idealOrder (⊤ : Ideal R) = 0 := by
  refine le_antisymm (iSup₂_le fun j hj => ?_) bot_le
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp
  · exact absurd (top_le_iff.mp (hj.trans (Ideal.pow_le_self hj0.ne')))
      (maximalIdeal.isMaximal R).ne_top

/-- In a discrete valuation ring with uniformizer `ϖ`, the ideal `(u ϖⁿ)`, `u` a unit, has
order `n`. -/
theorem idealOrder_span_unit_mul_pow {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {ϖ : R} (hϖ : Irreducible ϖ) (u : Rˣ) (n : ℕ) :
    idealOrder (Ideal.span {(u : R) * ϖ ^ n}) = n := by
  have hm : maximalIdeal R = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  have key : ∀ j : ℕ, Ideal.span {(u : R) * ϖ ^ n} ≤ maximalIdeal R ^ j ↔ j ≤ n := by
    intro j
    rw [hm, Ideal.span_singleton_pow, Ideal.span_singleton_le_span_singleton,
      Units.dvd_mul_left]
    exact _root_.pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit
  refine le_antisymm (iSup₂_le fun j hj => by exact_mod_cast (key j).1 hj) ?_
  exact le_iSup₂_of_le (f := fun (j : ℕ) (_ : Ideal.span {(u : R) * ϖ ^ n} ≤
    maximalIdeal R ^ j) => (j : ℕ∞)) n ((key n).2 le_rfl) le_rfl

/-- The maximal ideal of a discrete valuation ring has order `1`. -/
theorem idealOrder_maximalIdeal {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] : idealOrder (maximalIdeal R) = 1 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have := idealOrder_span_unit_mul_pow hϖ 1 1
  rwa [Units.val_one, one_mul, pow_one, ← hϖ.maximalIdeal_eq, Nat.cast_one] at this

end IdealOrder

/-! ### The order along a prime divisor of a regular function -/

section OrderAlongPrimeDivisor

open MMP.Resolution

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]

/-- For a nonzero element `g` of the local ring `𝒪_{X,D}` along a prime divisor `D` of a normal
scheme, `v_D(g) = ord((g))`, the order of the principal ideal `(g)` of the discrete valuation
ring `𝒪_{X,D}`. -/
theorem valuation_toComponent_eq_exp_idealOrder (D : Mori.PrimeDivisor X)
    {g : D.localRing} (hg : g ≠ 0) :
    ∃ n : ℕ, idealOrder (Ideal.span {g}) = n ∧
      D.valuation (D.toComponent.hom g) = WithZero.exp (n : ℤ) := by
  have := D.isDiscreteValuationRing_localRing
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible D.localRing
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hg hϖ
  refine ⟨n, idealOrder_span_unit_mul_pow hϖ u n, ?_⟩
  rw [map_mul, map_mul, map_pow, map_pow, D.valuation_toComponent_of_isUnit u.isUnit,
    D.valuation_toComponent_of_irreducible hϖ, one_mul, ← WithZero.exp_nsmul, nsmul_one]

end OrderAlongPrimeDivisor

/-! ### The coefficients of the pull-back of a locally principal prime divisor -/

section CoeffPullback

open MMP.Resolution DivisorWithCoeffs

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y]
  [IsNormal Y]

omit [IsLocallyNoetherian Y] [IsNormal Y] in
/-- If the generic point of `E` lies on `P`, then `P = E`. -/
theorem eq_of_genericPoint_mem_support {P E : Mori.PrimeDivisor Y}
    (hE : E.genericPoint ∈ P.support) : P = E := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hE
  have hle : E.genericPoint ≤ P.genericPoint := specializes_iff_mem_closure.mpr hE
  by_contra hne
  have hlt : E.genericPoint < P.genericPoint := lt_of_le_not_ge hle fun h =>
    hne (AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (Specializes.antisymm (show E.genericPoint ⤳ P.genericPoint from h)
        (show P.genericPoint ⤳ E.genericPoint from hle)).eq.symm)
  have h2 := Order.coheight_add_one_le hlt
  rw [Mori.PrimeDivisor.coheight_genericPoint, Mori.PrimeDivisor.coheight_genericPoint] at h2
  exact absurd h2 (by decide)

omit [IsLocallyNoetherian Y] [IsNormal Y] in
/-- The germ of a local generator `s` of the ideal of `P` is a unit at a point off `P`. -/
theorem isUnit_germ_of_notMem_support (P : Mori.PrimeDivisor Y) {W : Y.Opens} {s : Γ(Y, W)}
    (hgerm : ∀ z (hz : z ∈ W), IdealSheafData.stalk P.idealSheaf z =
      Ideal.span {(Y.presheaf.germ W z hz).hom s})
    {z : Y} (hz : z ∈ W) (hzP : z ∉ P.support) : IsUnit ((Y.presheaf.germ W z hz).hom s) := by
  have htop := (AlgebraicGeometry.IdealSheafData.stalk_eq_top_iff_notMem_support
    P.idealSheaf _).2 hzP
  rwa [hgerm _ hz, Ideal.span_singleton_eq_top] at htop

omit [IsLocallyNoetherian Y] in
/-- A section that is a nonzerodivisor in every stalk glues to a unit of the rational functions
restricting to its germs at the generic points of the components. -/
theorem exists_units_rationalFunctions_eq_germ {W : Y.Opens} {s : Γ(Y, W)}
    (hnzd : ∀ z (hz : z ∈ W), (Y.presheaf.germ W z hz).hom s ∈
      nonZeroDivisors (Y.presheaf.stalk z)) :
    ∃ φ : (RationalFunctions Y)ˣ, ∀ (Z : irreducibleComponents Y)
      (hZ : componentGenericPoint Y Z ∈ W),
      (φ : RationalFunctions Y) Z = (Y.presheaf.germ W _ hZ).hom s := by
  classical
  let u : ∀ Z : irreducibleComponents Y, (Y.presheaf.stalk (componentGenericPoint Y Z))ˣ :=
    fun Z => if h : componentGenericPoint Y Z ∈ W then
      letI := (RationalFunctions.isField_stalk Y Z).toField
      (isUnit_iff_ne_zero.2 (nonZeroDivisors.ne_zero (hnzd _ h))).unit
    else 1
  refine ⟨(RationalFunctions.unitsEquiv Y).symm u, fun Z hZ => ?_⟩
  change ((u Z : (Y.presheaf.stalk (componentGenericPoint Y Z))ˣ) :
    Y.presheaf.stalk (componentGenericPoint Y Z)) = _
  simp only [u]
  rw [dite_eq_left hZ]
  rfl

/-- A unit `φ` of the rational functions agreeing with the germs of a local generator `s` of the
ideal of `P` on `W` is a local equation of `P` on `W`. -/
theorem isLocalEquation_single_of_stalk_eq_span (P : Mori.PrimeDivisor Y) {W : Y.Opens}
    {s : Γ(Y, W)}
    (hgerm : ∀ z (hz : z ∈ W), IdealSheafData.stalk P.idealSheaf z =
      Ideal.span {(Y.presheaf.germ W z hz).hom s})
    (hnzd : ∀ z (hz : z ∈ W), (Y.presheaf.germ W z hz).hom s ∈
      nonZeroDivisors (Y.presheaf.stalk z))
    {φ : (RationalFunctions Y)ˣ}
    (hφZ : ∀ (Z : irreducibleComponents Y) (hZ : componentGenericPoint Y Z ∈ W),
      (φ : RationalFunctions Y) Z = (Y.presheaf.germ W _ hZ).hom s) :
    Divisor.IsLocalEquation (Finsupp.single P 1 : Divisor Y) W φ := by
  classical
  rintro D ⟨z, hzD, hzW⟩
  have hηW : D.genericPoint ∈ W := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hzD
    exact (specializes_iff_mem_closure.mpr hzD).mem_open W.isOpen hzW
  have key : D.toComponent.hom ((Y.presheaf.germ W _ hηW).hom s) =
      (φ : RationalFunctions Y) D.component := by
    rw [hφZ _ (D.specializes_genericPoint.mem_open W.isOpen hηW)]
    exact TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _
  by_cases hPD : P = D
  · subst hPD
    have := P.integral
    rw [coeff_single_self]
    have hprime : Prime ((Y.presheaf.germ W _ hηW).hom s) := by
      rw [← Ideal.span_singleton_prime (nonZeroDivisors.ne_zero (hnzd _ hηW)), ← hgerm _ hηW]
      have hmem : P.genericPoint ∈ P.support := by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact subset_closure rfl
      have hxr : P.genericPoint ∈ Set.range P.idealSheaf.subschemeι := by
        rw [Scheme.IdealSheafData.range_subschemeι]
        exact hmem
      obtain ⟨y', hy'⟩ := hxr
      rw [← hy', ← Stacks.Divisors.kernel_stalkMap_subscheme_eq_idealStalk]
      exact RingHom.ker_isPrime _
    exact (P.ord_eq_one_of_irreducible hprime.irreducible key).symm
  · rw [coeff_single_of_ne hPD]
    exact (D.ord_eq_zero_of_isUnit (isUnit_germ_of_notMem_support P hgerm hηW
      fun h => hPD (eq_of_genericPoint_mem_support h)) key).symm

/-- **The coefficients of the pull-back of a prime divisor with invertible ideal.** Let
`f : X ⟶ Y` be a morphism of locally Noetherian normal schemes and `P` a prime divisor of `Y`
whose ideal sheaf `I_P` is invertible. Then the coefficient of a prime divisor `E` of `X` in
`f^*P` is the order `ord((f^*I_P)_{η_E})` of the stalk of the inverse image ideal `f^*I_P` in the
discrete valuation ring `𝒪_{X,E}`. -/
theorem coeff_isPullback_single_eq_idealOrder {f : X ⟶ Y} (P : Mori.PrimeDivisor Y)
    (hP : Stacks.Divisors.IsEffectiveCartierDivisor P.idealSheaf)
    {hB : ∀ Z : irreducibleComponents X,
      f (componentGenericPoint X Z) ∉ supp (Finsupp.single P 1 : Divisor Y)}
    {B' : Divisor X} (h : Divisor.IsPullback f (Finsupp.single P 1 : Divisor Y) hB B')
    (E : Mori.PrimeDivisor X) :
    ∃ n : ℕ, idealOrder (IdealSheafData.stalk (P.idealSheaf.comap f) E.genericPoint) = n ∧
      B'.coeff E = n := by
  classical
  set x := f E.genericPoint with hxdef
  obtain ⟨W, hW, hxW, s, hs, hspan⟩ :=
    Stacks.Divisors.exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor
      P.idealSheaf hP x
  have hgerm : ∀ z (hz : z ∈ W), IdealSheafData.stalk P.idealSheaf z =
      Ideal.span {(Y.presheaf.germ W z hz).hom s} := by
    intro z hz
    rw [AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ P.idealSheaf z ⟨W, hW⟩ hz, hspan,
      Ideal.map_span, Set.image_singleton]
  have hnzd : ∀ z (hz : z ∈ W), (Y.presheaf.germ W z hz).hom s ∈
      nonZeroDivisors (Y.presheaf.stalk z) := fun z hz =>
    Stacks.Divisors.germ_mem_nonZeroDivisors hW hs z hz
  obtain ⟨φ, hφZ⟩ := exists_units_rationalFunctions_eq_germ hnzd
  have hφ := isLocalEquation_single_of_stalk_eq_span P hgerm hnzd hφZ
  have hE : (E.support ∩ f ⁻¹ᵁ W).Nonempty := (E.genericPoint_mem_iff (f ⁻¹ᵁ W)).mp hxW
  rw [h W φ hφ E hE]
  have hsp : componentGenericPoint X E.component ⤳ E.genericPoint := E.specializes_genericPoint
  have hsp' : f (componentGenericPoint X E.component) ⤳ x := f.base.hom.map_specializes hsp
  set W' := pointComponent (f (componentGenericPoint X E.component))
  have hW' : f (componentGenericPoint X E.component) ∈ W'.1 := mem_pointComponent _
  have hcW : f (componentGenericPoint X E.component) ∈ W := hsp'.mem_open W.isOpen hxW
  have hunit := isUnit_germ_of_notMem_support P hgerm hcW fun hm =>
    hB E.component (support_subset_supp (by rw [coeff_single_self]; exact one_ne_zero) hm)
  have hW'W : componentGenericPoint Y W' ∈ W :=
    ((isGenericPoint_componentGenericPoint Y W').specializes hW').mem_open W.isOpen hcW
  have ha : (stalkToRationalFunctions Y hW').hom (hunit.unit : Y.presheaf.stalk _) =
      (φ : RationalFunctions Y) W' := by
    rw [hφZ W' hW'W, IsUnit.unit_spec]
    exact TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _
  rw [pullbackComponent_eq hB hφ _ hW' hunit.unit ha]
  set g : E.localRing := (f.stalkMap E.genericPoint).hom ((Y.presheaf.germ W x hxW).hom s)
    with hgdef
  have hg : E.toComponent.hom g = (Units.map (f.stalkMap (componentGenericPoint X
      E.component)).hom.toMonoidHom hunit.unit : X.presheaf.stalk _) := by
    change (X.presheaf.stalkSpecializes hsp).hom ((f.stalkMap E.genericPoint).hom
      ((Y.presheaf.germ W x hxW).hom s)) = (f.stalkMap _).hom ((Y.presheaf.germ W _ hcW).hom s)
    rw [← Scheme.Hom.stalkSpecializes_stalkMap_apply, TopCat.Presheaf.germ_stalkSpecializes_apply]
  have hg0 : g ≠ 0 := fun h0 => (Units.map (f.stalkMap (componentGenericPoint X
    E.component)).hom.toMonoidHom hunit.unit).ne_zero (by rw [← hg, h0, map_zero])
  obtain ⟨n, hn, hv⟩ := valuation_toComponent_eq_exp_idealOrder E hg0
  have hspan_g : IdealSheafData.stalk (P.idealSheaf.comap f) E.genericPoint =
      Ideal.span {g} := by
    rw [AlgebraicGeometry.IdealSheafData.stalk_comap, hgerm x hxW, Ideal.map_span,
      Set.image_singleton]
  refine ⟨n, hspan_g ▸ hn, ?_⟩
  have h1 := E.valuation_eq_exp_ordUnit (Units.map (f.stalkMap (componentGenericPoint X
      E.component)).hom.toMonoidHom hunit.unit)
  rw [← hg, hv] at h1
  exact (WithZero.exp_injective h1).symm

end CoeffPullback

/-! ### Birational transforms of prime divisors over the biregular locus -/

section InverseTransform

variable {X Y : Scheme.{u}}

/-- Over the biregular locus `V_g` of `g : X ⟶ Y`, `g` reflects specializations. -/
theorem specializes_of_mem_biregularLocus (g : X ⟶ Y) {a b : X}
    (ha : g a ∈ biregularLocus g) (hb : g b ∈ biregularLocus g) (h : g a ⤳ g b) : a ⤳ b := by
  set V := biregularLocus g
  have : IsIso (g ∣_ V) := isBiregular_biregularLocus g
  let pa : (g ⁻¹ᵁ V).toScheme := ⟨a, ha⟩
  let pb : (g ⁻¹ᵁ V).toScheme := ⟨b, hb⟩
  have e : ∀ p : (g ⁻¹ᵁ V).toScheme, V.ι ((g ∣_ V) p) = g ((g ⁻¹ᵁ V).ι p) := fun p => by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
  have h1 : V.ι ((g ∣_ V) pa) ⤳ V.ι ((g ∣_ V) pb) := by
    rw [e, e]
    exact h
  have h2 : (g ∣_ V) pa ⤳ (g ∣_ V) pb := V.ι.isOpenEmbedding.isInducing.specializes_iff.mp h1
  have h3 : pa ⤳ pb := (g ∣_ V).isOpenEmbedding.isInducing.specializes_iff.mp h2
  exact (g ⁻¹ᵁ V).ι.isOpenEmbedding.isInducing.specializes_iff.mpr h3

/-- If `g⁻¹_* D = E`, then `g` maps the generic point of `E` to that of `D`, inside the biregular
locus. -/
theorem map_genericPoint_of_inverseTransformPrimeDivisor_eq_some {g : X ⟶ Y}
    {D : Mori.PrimeDivisor Y} {E : Mori.PrimeDivisor X}
    (h : inverseTransformPrimeDivisor g D = some E) :
    g E.genericPoint = D.genericPoint ∧ g E.genericPoint ∈ biregularLocus g := by
  have hsupp := support_inverseTransformPrimeDivisor h
  obtain ⟨⟨z, hzD, hzV⟩, -⟩ := inverseTransformPrimeDivisor_eq_some_iff.mp h
  have hηE : E.genericPoint ∈ (inverseTransform g D.idealSheaf.support : Set X) := by
    rw [← hsupp, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  have hne : (g ⁻¹' ((D.idealSheaf.support : Set Y) ∩ biregularLocus g)).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have : (inverseTransform g D.idealSheaf.support : Set X) = ∅ := by
      change closure _ = _; rw [hemp, closure_empty]
    rw [this] at hηE
    exact hηE
  obtain ⟨w, hwD, hwV⟩ := hne
  have hwE : w ∈ E.support := by
    rw [hsupp]
    exact subset_closure ⟨hwD, hwV⟩
  have hsp : E.genericPoint ⤳ w := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hwE
    exact specializes_iff_mem_closure.mpr hwE
  have hV : g E.genericPoint ∈ biregularLocus g :=
    (g.base.hom.map_specializes hsp).mem_open (biregularLocus g).isOpen hwV
  have hmemD : g E.genericPoint ∈ D.support := by
    have hcl : (inverseTransform g D.idealSheaf.support : Set X) ⊆
        g ⁻¹' (D.idealSheaf.support : Set Y) :=
      closure_minimal (fun _ hx => hx.1) (D.idealSheaf.support.isClosed.preimage g.continuous)
    exact hcl hηE
  have hcoh : Order.coheight (g E.genericPoint) = 1 := by
    rw [MMP.Positivity.coheight_map_of_mem_biregularLocus g hV]
    exact E.coheight_genericPoint
  exact ⟨D.eq_genericPoint_of_mem_support hmemD hcoh, hV⟩

/-- Conversely, if `g` maps the generic point of `E` to that of `D` inside the biregular locus,
then `g⁻¹_* D = E`. -/
theorem inverseTransformPrimeDivisor_eq_some_of_map_genericPoint {g : X ⟶ Y}
    {D : Mori.PrimeDivisor Y} {E : Mori.PrimeDivisor X}
    (hη : g E.genericPoint = D.genericPoint) (hV : g E.genericPoint ∈ biregularLocus g) :
    inverseTransformPrimeDivisor g D = some E := by
  have hDmem : D.genericPoint ∈ D.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  have hEmem : E.genericPoint ∈ (g ⁻¹' ((D.idealSheaf.support : Set Y) ∩ biregularLocus g)) :=
    ⟨hη ▸ hDmem, hV⟩
  have hsupp : E.idealSheaf.support = inverseTransform g D.idealSheaf.support := by
    apply Closeds.ext
    change (E.support : Set X) = closure _
    apply subset_antisymm
    · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact closure_mono (Set.singleton_subset_iff.mpr hEmem)
    · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      refine closure_minimal ?_ isClosed_closure
      rintro w ⟨hwD, hwV⟩
      have hDw : D.genericPoint ⤳ g w := by
        have : g w ∈ D.support := hwD
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at this
        exact specializes_iff_mem_closure.mpr this
      rw [← hη] at hDw
      exact specializes_iff_mem_closure.mp (specializes_of_mem_biregularLocus g hV hwV hDw)
  refine inverseTransformPrimeDivisor_eq_some_iff.mpr ⟨⟨D.genericPoint, hDmem, hη ▸ hV⟩, ?_⟩
  have := E.integral
  exact Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme _ _ hsupp

end InverseTransform

/-! ### The blow-up of a closed point of a smooth surface -/

section Blowup

variable {k : Type u} [Field k] [IsAlgClosed k] {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)}

/-- The blow-up of a closed point of a smooth surface is smooth. -/
theorem isSmoothScheme_blowUp_singleton (hY : Mori.IsVariety k sY) (hYs : IsSmoothScheme sY)
    (hYd : topologicalKrullDim Y = 2) {y : Y} (hy : IsClosed ({y} : Set Y)) :
    IsSmoothScheme (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) ≫ sY) :=
  have : LocallyOfFiniteType sY := hY.toLocallyOfFiniteType
  have : IsIntegral Y := hY.toIsIntegral
  (MMP.Resolution.isSmoothScheme_blowUp_and_exists_primeDivisor_exceptionalIdeal sY _
    (isSmoothBlowup_vanishingIdeal_singleton sY hYs hy)
    (isIrreducible_support_vanishingIdeal_singleton hy)
    (one_le_codimension_vanishingIdeal_singleton hYd hy)).1

omit [IsAlgClosed k] in
/-- The blow-up of a closed point of a surface variety is a variety. -/
theorem isVariety_blowUp_singleton (hY : Mori.IsVariety k sY) (hYd : topologicalKrullDim Y = 2)
    {y : Y} (hy : IsClosed ({y} : Set Y)) :
    Mori.IsVariety k (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) ≫ sY) :=
  have : AlgebraicGeometry.IsVariety k sY := hY
  have : IsIntegral Y := hY.toIsIntegral
  (MMP.Flips.ResolutionInputs.isVariety_blowUp_and_isProjective_and_isBirational sY _
    (Stacks.ResolutionOfSurfaces.vanishingIdeal_singleton_ne_bot hYd y hy)).1

omit [IsAlgClosed k] in
/-- A scheme smooth over a field is locally Noetherian and normal. -/
theorem isLocallyNoetherian_and_isNormal_of_isSmoothScheme {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} (hsm : IsSmoothScheme sX) : IsLocallyNoetherian X ∧ IsNormal X := by
  obtain ⟨h1, h2⟩ := (isRegular_iff_regular_stalks X).1 (isRegular_of_isSmoothScheme hsm)
  exact ⟨h1, AlgebraicGeometry.isNormal_of_forall_isRegularLocalRing h2⟩

end Blowup

section BlowupGeometry

variable {k : Type u} [Field k] {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)}

/-- The exceptional curve `F = π⁻¹(y)` is the fibre over `y`. -/
theorem mem_support_iff_of_idealSheaf_eq_exceptionalIdeal {y : Y} (hy : IsClosed ({y} : Set Y))
    {F : Mori.PrimeDivisor (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))}
    (hF : F.idealSheaf = exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))
    (q : blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)) :
    q ∈ F.support ↔ blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) q = y := by
  change q ∈ (F.idealSheaf.support : Set _) ↔ _
  rw [hF, exceptionalIdeal, Scheme.IdealSheafData.support_comap]
  change blowUpToBase _ q ∈ ((Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩).support : Set Y) ↔ _
  rw [support_vanishingIdeal_singleton hy, Set.mem_singleton_iff]

/-- A point other than `y` lies in the biregular locus of the blow-up of `y`. -/
theorem mem_biregularLocus_blowUpToBase_singleton {y : Y} (hy : IsClosed ({y} : Set Y)) {x : Y}
    (hx : x ≠ y) :
    x ∈ biregularLocus (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)) := by
  refine le_biregularLocus (V := (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩).support.compl)
    (isIso_blowUpToBase_restrict_compl_support _) ?_
  change x ∉ ((Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩).support : Set Y)
  rw [support_vanishingIdeal_singleton hy]
  exact hx

/-- A closed point of a surface variety over an algebraically closed field has coheight two. -/
theorem coheight_eq_two_of_isClosed [IsAlgClosed k] (hY : Mori.IsVariety k sY)
    (hYd : topologicalKrullDim Y = 2) {y : Y} (hy : IsClosed ({y} : Set Y)) :
    Order.coheight y = 2 := by
  have h := MMP.Mori.SurfaceAux.ringKrullDim_stalk_eq_two sY hY hYd y hy
  rw [ringKrullDim_stalk_eq_coheight] at h
  have h2 : ((Order.coheight y : ℕ∞) : WithBot ℕ∞) = ((2 : ℕ∞) : WithBot ℕ∞) := h
  exact WithBot.coe_injective h2

/-- The blown-up point is not in the biregular locus of the blow-up. -/
theorem notMem_biregularLocus_blowUpToBase_singleton [IsAlgClosed k] (hY : Mori.IsVariety k sY)
    (hYd : topologicalKrullDim Y = 2) {y : Y} (hy : IsClosed ({y} : Set Y))
    {F : Mori.PrimeDivisor (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))}
    (hF : F.idealSheaf = exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)) :
    y ∉ biregularLocus (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)) := by
  intro hyV
  have hξ : blowUpToBase _ F.genericPoint = y :=
    (mem_support_iff_of_idealSheaf_eq_exceptionalIdeal hy hF _).mp (by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl)
  have h := MMP.Positivity.coheight_map_of_mem_biregularLocus
    (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)) (x := F.genericPoint)
    (by rw [hξ]; exact hyV)
  rw [hξ, coheight_eq_two_of_isClosed hY hYd hy, Mori.PrimeDivisor.coheight_genericPoint] at h
  exact absurd h (by decide)

/-- The blow-up of a closed point of a surface is dominant. -/
theorem isDominant_blowUpToBase_singleton [IrreducibleSpace Y] (hYd : topologicalKrullDim Y = 2)
    {y : Y} (hy : IsClosed ({y} : Set Y)) :
    IsDominant (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)) := by
  have hne : genericPoint Y ≠ y := by
    intro h
    apply singleton_ne_univ_of_topologicalKrullDim_eq_two hYd y
    have hcl := hy.closure_eq
    rw [← h] at hcl ⊢
    rw [← hcl]
    exact genericPoint_spec Y
  obtain ⟨q, hq⟩ := exists_blowUpToBase_eq_of_notMem_support
    (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) (x := genericPoint Y) (by
      rw [support_vanishingIdeal_singleton hy]; exact hne)
  refine ⟨?_⟩
  rw [DenseRange, dense_iff_closure_eq, Set.eq_univ_iff_forall]
  intro z
  have hmem : genericPoint Y ∈ Set.range (blowUpToBase
      (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)).base := ⟨q, hq⟩
  exact closure_mono (Set.singleton_subset_iff.mpr hmem)
    ((genericPoint_spec Y).specializes (Set.mem_univ z)).mem_closure

/-- The stalk of the ideal of a prime divisor `P` with invertible ideal sheaf at its generic point
is the maximal ideal of the discrete valuation ring `𝒪_{X,P}`. -/
theorem stalk_idealSheaf_genericPoint_eq_maximalIdeal {X : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] (P : Mori.PrimeDivisor X)
    (hP : Stacks.Divisors.IsEffectiveCartierDivisor P.idealSheaf) :
    IdealSheafData.stalk P.idealSheaf P.genericPoint = IsLocalRing.maximalIdeal P.localRing := by
  have := P.integral
  have := P.isDiscreteValuationRing_localRing
  have hmem : P.genericPoint ∈ P.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  have hprime : (IdealSheafData.stalk P.idealSheaf P.genericPoint).IsPrime := by
    have hxr : P.genericPoint ∈ Set.range P.idealSheaf.subschemeι := by
      rw [Scheme.IdealSheafData.range_subschemeι]
      exact hmem
    obtain ⟨y', hy'⟩ := hxr
    rw [← hy', ← Stacks.Divisors.kernel_stalkMap_subscheme_eq_idealStalk]
    exact RingHom.ker_isPrime _
  have hne : IdealSheafData.stalk P.idealSheaf P.genericPoint ≠ ⊥ := by
    obtain ⟨W, hW, hxW, s, hs, hspan⟩ :=
      Stacks.Divisors.exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor
        P.idealSheaf hP P.genericPoint
    rw [AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ P.idealSheaf _ ⟨W, hW⟩ hxW, hspan,
      Ideal.map_span, Set.image_singleton, Ne, Ideal.span_singleton_eq_bot]
    exact nonZeroDivisors.ne_zero (Stacks.Divisors.germ_mem_nonZeroDivisors hW hs _ hxW)
  exact IsLocalRing.eq_maximalIdeal (hprime.isMaximal hne)

end BlowupGeometry

/-! ### Pulling back a curve -/

section PullbackCurve

open MMP.Resolution DivisorWithCoeffs

variable {k : Type u} [Field k] {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)}

/-- Over the biregular locus, the stalk maps of a morphism are isomorphisms. -/
theorem isIso_stalkMap_of_mem_biregularLocus {X : Scheme.{u}} (g : X ⟶ Y) {x : X}
    (hx : g x ∈ biregularLocus g) : IsIso (g.stalkMap x) := by
  have hiso : IsIso (g ∣_ biregularLocus g) := isBiregular_biregularLocus g
  have hstalk : IsIso ((g ∣_ biregularLocus g).stalkMap ⟨x, hx⟩) :=
    ((isIso_iff_isIso_stalkMap (g ∣_ biregularLocus g)).mp hiso).2 ⟨x, hx⟩
  exact ((MorphismProperty.isomorphisms CommRingCat).arrow_mk_iso_iff
    (morphismRestrictStalkMap g (biregularLocus g) ⟨x, hx⟩)).mp hstalk

/-- The generic point of an irreducible closed set is the generic point of the prime divisor. -/
theorem isIrreducible_genericPoint_eq {X : Scheme.{u}} (P : Mori.PrimeDivisor X)
    (h : IsIrreducible (P.support : Set X)) : h.genericPoint = P.genericPoint := by
  have h1 := h.isGenericPoint_genericPoint_closure
  have h2 : closure (P.support : Set X) = closure {P.genericPoint} := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, closure_closure]
  rw [h2] at h1
  exact h1.eq isGenericPoint_closure

/-- An `Option`-valued prime divisor, as a divisor, vanishes at any prime divisor it is not. -/
theorem elim_single_apply_eq_zero {X : Scheme.{u}} {o : Option (Mori.PrimeDivisor X)}
    {E : Mori.PrimeDivisor X} (h : ∀ E', o = some E' → E' ≠ E) :
    (o.elim 0 (Finsupp.single · (1 : ℤ)) : Divisor X) E = 0 := by
  rcases o with _ | E'
  · rfl
  · exact Finsupp.single_eq_of_ne (h E' rfl).symm

/-- The strict transform of a prime divisor through a point blow-up is not the exceptional
curve. -/
theorem ne_of_inverseTransformPrimeDivisor_blowUp_singleton_eq_some [IsAlgClosed k]
    (hY : Mori.IsVariety k sY) (hYd : topologicalKrullDim Y = 2) {y : Y}
    (hy : IsClosed ({y} : Set Y))
    {F : Mori.PrimeDivisor (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))}
    (hF : F.idealSheaf = exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))
    {C : Mori.PrimeDivisor Y} {E' : Mori.PrimeDivisor (blowUp
      (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))}
    (hE' : inverseTransformPrimeDivisor
      (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)) C = some E') :
    E' ≠ F := by
  rintro rfl
  obtain ⟨-, hV⟩ := map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hE'
  have hξ : blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) E'.genericPoint = y :=
    (mem_support_iff_of_idealSheaf_eq_exceptionalIdeal hy hF _).mp (by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl)
  rw [hξ] at hV
  exact notMem_biregularLocus_blowUpToBase_singleton hY hYd hy hF hV

/-- The multiplicity of a curve at the blown-up point is the order of its pulled-back ideal
along the exceptional curve. -/
theorem multiplicityAt_eq_idealOrder_stalk_comap_exceptional [IsAlgClosed k]
    (hY : Mori.IsVariety k sY) (hYs : IsSmoothScheme sY) (hYd : topologicalKrullDim Y = 2)
    {y : Y} (hy : IsClosed ({y} : Set Y)) [IsLocallyNoetherian Y] [IsNormal Y]
    [IsLocallyNoetherian (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))]
    [IsNormal (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))]
    {F : Mori.PrimeDivisor (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))}
    (hF : F.idealSheaf = exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))
    (C : Mori.PrimeDivisor Y) :
    C.multiplicityAt y = idealOrder (IdealSheafData.stalk (C.idealSheaf.comap
      (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))) F.genericPoint) := by
  have : LocallyOfFiniteType sY := hY.toLocallyOfFiniteType
  have : IsIntegral Y := hY.toIsIntegral
  have hsb := isSmoothBlowup_vanishingIdeal_singleton sY hYs hy
  have hirr := isIrreducible_support_vanishingIdeal_singleton hy
  have hcodim := one_le_codimension_vanishingIdeal_singleton hYd hy
  have hord := orderAlong_comap_blowUpToBase_eq sY _ hsb hirr hcodim C.idealSheaf
  have hE : exceptionalPrimeDivisor sY _ hsb hirr hcodim = F :=
    PrimeDivisor.ext_idealSheaf (by rw [hF]; rfl)
  simp only [orderAlong, multAt] at hord
  rw [isIrreducible_genericPoint_eq _ (isIrreducible_support_exceptionalPrimeDivisor sY _ hsb
    hirr hcodim)] at hord
  have hy' : hirr.genericPoint = y := by
    have h1 := hirr.isGenericPoint_genericPoint_closure
    have h2 : closure ((Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)).support :
        Set Y) = closure {y} := by rw [support_vanishingIdeal_singleton hy]
    rw [h2] at h1
    exact h1.eq isGenericPoint_closure
  rw [hy'] at hord
  have hmult : C.multiplicityAt y = idealOrder (IdealSheafData.stalk C.idealSheaf y) := by
    simp only [PrimeDivisor.multiplicityAt, idealOrder,
      Scheme.IdealSheafData.stalkIdeal_eq_stalk]
  rw [hmult, ← hord, hE]

/-- Away from the exceptional curve, the coefficient of the strict transform of a curve `C` is
the order of the pulled-back ideal of `C`. -/
theorem natCast_eq_elim_inverseTransformPrimeDivisor_apply_of_ne {y : Y}
    (hy : IsClosed ({y} : Set Y)) [IsLocallyNoetherian Y] [IsNormal Y]
    [IsLocallyNoetherian (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))]
    [IsNormal (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))]
    {F : Mori.PrimeDivisor (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))}
    (hF : F.idealSheaf = exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))
    (C : Mori.PrimeDivisor Y) (hCe : Stacks.Divisors.IsEffectiveCartierDivisor C.idealSheaf)
    {E : Mori.PrimeDivisor (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))}
    (hEF : E ≠ F) {n : ℕ}
    (hn : idealOrder (IdealSheafData.stalk (C.idealSheaf.comap
      (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))) E.genericPoint) = n) :
    (n : ℤ) = ((inverseTransformPrimeDivisor (blowUpToBase
      (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)) C).elim 0 (Finsupp.single · (1 : ℤ)) :
        Divisor (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))) E := by
  have hηF : E.genericPoint ∉ F.support := fun h => hEF (eq_of_genericPoint_mem_support h).symm
  have hx : blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) E.genericPoint ≠ y :=
    fun h => hηF ((mem_support_iff_of_idealSheaf_eq_exceptionalIdeal hy hF _).mpr h)
  have hxV := mem_biregularLocus_blowUpToBase_singleton hy hx
  have hiso := isIso_stalkMap_of_mem_biregularLocus _ hxV
  rw [AlgebraicGeometry.IdealSheafData.stalk_comap] at hn
  have hn' : idealOrder (IdealSheafData.stalk C.idealSheaf
      (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) E.genericPoint)) = n := by
    rw [← hn]
    exact (idealOrder_map_ringEquiv
      (asIso (Scheme.Hom.stalkMap _ E.genericPoint)).commRingCatIsoToRingEquiv _).symm
  by_cases hxC : blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) E.genericPoint =
      C.genericPoint
  · rw [inverseTransformPrimeDivisor_eq_some_of_map_genericPoint hxC hxV]
    change (n : ℤ) = (Finsupp.single E (1 : ℤ)) E
    rw [Finsupp.single_eq_same]
    have := C.isDiscreteValuationRing_localRing
    rw [hxC, stalk_idealSheaf_genericPoint_eq_maximalIdeal C hCe, idealOrder_maximalIdeal] at hn'
    exact_mod_cast (Nat.cast_injective (R := ℕ∞) hn'.symm : n = 1)
  · rw [elim_single_apply_eq_zero fun E' hE' h => hxC (by
      subst h
      exact (map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hE').1)]
    have hxnC : blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) E.genericPoint ∉
        C.idealSheaf.support := by
      intro hm
      refine hxC (C.eq_genericPoint_of_mem_support hm ?_)
      rw [MMP.Positivity.coheight_map_of_mem_biregularLocus _ hxV]
      exact E.coheight_genericPoint
    rw [(AlgebraicGeometry.IdealSheafData.stalk_eq_top_iff_notMem_support _ _).2 hxnC,
      idealOrder_top] at hn'
    exact_mod_cast (Nat.cast_injective (R := ℕ∞) hn'.symm : n = 0)

/-- **Pulling back a curve through a point blow-up of a smooth surface.** Let `Y` be a smooth
surface over an algebraically closed field `k`, `y ∈ Y` a closed point,
`π : Y' = B_y Y ⟶ Y` the blow-up of `y` and `F = π⁻¹(y)` its exceptional curve. For every
prime divisor `C` of `Y`, `π^*C = π⁻¹_* C + (mult_y C) F`. -/
theorem isPullback_single_blowUp_singleton [IsAlgClosed k] (hY : Mori.IsVariety k sY)
    (hYs : IsSmoothScheme sY) (hYd : topologicalKrullDim Y = 2) {y : Y}
    (hy : IsClosed ({y} : Set Y)) [IsLocallyNoetherian Y] [IsNormal Y]
    [IsLocallyNoetherian (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))]
    [IsNormal (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))]
    {F : Mori.PrimeDivisor (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))}
    (hF : F.idealSheaf = exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))
    (C : Mori.PrimeDivisor Y)
    (hB : ∀ Z : irreducibleComponents (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)),
      blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)
        (componentGenericPoint _ Z) ∉ supp (Finsupp.single C 1 : Divisor Y)) :
    Divisor.IsPullback (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))
      (Finsupp.single C 1 : Divisor Y) hB
      (inverseTransformDivisor (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))
          (Finsupp.single C 1 : Divisor Y) +
        ((C.multiplicityAt y).toNat : ℤ) • Finsupp.single F 1) := by
  classical
  have : LocallyOfFiniteType sY := hY.toLocallyOfFiniteType
  have : IsIntegral Y := hY.toIsIntegral
  have hvar := isVariety_blowUp_singleton hY hYd hy
  have : CompactSpace (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)) := by
    have : QuasiCompact (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) ≫ sY) :=
      hvar.toQuasiCompact
    exact QuasiCompact.compactSpace_of_compactSpace
      (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) ≫ sY)
  have hCc : Divisor.IsCartier (Finsupp.single C 1 : Divisor Y) :=
    MMP.Threefold.Mori.isCartier_single_of_isSmoothScheme hYs C
  have hCe : Stacks.Divisors.IsEffectiveCartierDivisor C.idealSheaf :=
    isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme hYs C
  obtain ⟨B', hB'⟩ := hCc.exists_isPullback hB
  suffices hBeq : B' = inverseTransformDivisor
      (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))
      (Finsupp.single C 1 : Divisor Y) + ((C.multiplicityAt y).toNat : ℤ) • Finsupp.single F 1 by
    exact hBeq ▸ hB'
  ext E
  obtain ⟨n, hn, hcoef⟩ := coeff_isPullback_single_eq_idealOrder C hCe hB' E
  rw [hcoef, coeff_add, inverseTransformDivisor_single, coeff_smul]
  change (n : ℤ) = ((inverseTransformPrimeDivisor (blowUpToBase
    (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)) C).elim 0 (Finsupp.single · (1 : ℤ)) :
      Divisor _) E + _ • (Finsupp.single F (1 : ℤ)) E
  by_cases hEF : E = F
  · subst hEF
    rw [elim_single_apply_eq_zero fun E' hE' =>
        ne_of_inverseTransformPrimeDivisor_blowUp_singleton_eq_some hY hYd hy hF hE',
      zero_add, Finsupp.single_eq_same, smul_eq_mul, mul_one,
      multiplicityAt_eq_idealOrder_stalk_comap_exceptional hY hYs hYd hy hF C, hn]
    simp
  · rw [Finsupp.single_eq_of_ne hEF, smul_zero, add_zero]
    exact natCast_eq_elim_inverseTransformPrimeDivisor_apply_of_ne hy hF C hCe hEF hn

/-- A dominant morphism from an irreducible scheme maps the generic point outside the support of
every divisor with coefficients. -/
theorem map_componentGenericPoint_notMem_supp_of_isDominant' {R : Type*} [Zero R]
    {X : Scheme.{u}} [IrreducibleSpace X] (f : X ⟶ Y) [IsDominant f] (D : DivisorWithCoeffs R Y)
    (Z : irreducibleComponents X) : f (componentGenericPoint X Z) ∉ D.supp := by
  intro h
  obtain ⟨E, -, hmem⟩ := DivisorWithCoeffs.mem_supp_iff.mp h
  exact MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant f
    (Finsupp.single E 1 : Divisor Y) Z
    (support_subset_supp (by rw [coeff_single_self]; exact one_ne_zero) hmem)

/-- **Pulling back a divisor through a point blow-up of a smooth surface.** For every divisor
`D` on a smooth surface `Y` over an algebraically closed field and the blow-up `π` of a closed
point `y` with exceptional curve `F`, `π^*D = π⁻¹_* D + (mult_y D) F`. -/
theorem isPullback_blowUp_singleton [IsAlgClosed k] (hY : Mori.IsVariety k sY)
    (hYs : IsSmoothScheme sY) (hYd : topologicalKrullDim Y = 2) {y : Y}
    (hy : IsClosed ({y} : Set Y)) [IsLocallyNoetherian Y] [IsNormal Y]
    [IsLocallyNoetherian (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))]
    [IsNormal (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))]
    {F : Mori.PrimeDivisor (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))}
    (hF : F.idealSheaf = exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))
    (D : Divisor Y)
    (hB : ∀ Z : irreducibleComponents (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)),
      blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)
        (componentGenericPoint _ Z) ∉ supp D) :
    Divisor.IsPullback (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)) D hB
      (inverseTransformDivisor (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)) D +
        Finsupp.single F (D.multiplicityAt y)) := by
  have : QuasiCompact sY := hY.toQuasiCompact
  have : IrreducibleSpace Y := by have := hY.toIsIntegral; infer_instance
  have hvar := isVariety_blowUp_singleton hY hYd hy
  have : IrreducibleSpace (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)) := by
    have := hvar.toIsIntegral; infer_instance
  have := isDominant_blowUpToBase_singleton hYd hy
  have hBall : ∀ (D : Divisor Y) Z, blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)
      (componentGenericPoint _ Z) ∉ supp D := fun D Z =>
    map_componentGenericPoint_notMem_supp_of_isDominant' _ D Z
  suffices key : ∀ D : Divisor Y, Divisor.IsPullback
      (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)) D (hBall D)
      (inverseTransformDivisor (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)) D +
        Finsupp.single F (D.multiplicityAt y)) from key D
  intro D
  induction D using Finsupp.induction_linear with
  | zero =>
    rw [map_zero, multiplicityAt, Finsupp.sum_zero_index, Finsupp.single_zero, add_zero]
    exact Divisor.isPullback_zero _
  | add D₁ D₂ h₁ h₂ =>
    have h := Divisor.IsPullback.add (isCartier_of_isSmoothScheme hYs D₁)
      (isCartier_of_isSmoothScheme hYs D₂) (hBall _) h₁ h₂
    rw [map_add, multiplicityAt_add, Finsupp.single_add]
    convert h using 1
    abel
  | single C n =>
    have h := (isPullback_single_blowUp_singleton hY hYs hYd hy hF C (hBall _)).zsmul
      (MMP.Threefold.Mori.isCartier_single_of_isSmoothScheme hYs C) n (hBall _)
    have hs : n • (Finsupp.single C 1 : Divisor Y) = Finsupp.single C n := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hs] at h
    convert h using 1
    rw [smul_add, ← map_zsmul, hs, multiplicityAt_single, Finsupp.smul_single, smul_eq_mul,
      nsmul_eq_mul]
    congr 2
    rw [Finsupp.smul_single, smul_eq_mul, mul_one, mul_comm]

/-- Regarding a single prime divisor as a `ℚ`-divisor. -/
theorem toQDivisor_single {X : Scheme.{u}} (P : Mori.PrimeDivisor X) (n : ℤ) :
    Divisor.toQDivisor (Finsupp.single P n) = Finsupp.single P (n : ℚ) := by
  refine DivisorWithCoeffs.ext' fun E => ?_
  rw [Divisor.coeff_toQDivisor]
  by_cases h : P = E
  · subst h; rw [coeff_single_self, coeff_single_self]
  · rw [coeff_single_of_ne h, coeff_single_of_ne h, Int.cast_zero]

/-- The birational transform commutes with regarding divisors as `ℚ`-divisors. -/
theorem inverseTransformDivisor_toQDivisor {X : Scheme.{u}} (g : X ⟶ Y) (D : Divisor Y) :
    inverseTransformDivisor g (Divisor.toQDivisor D) =
      Divisor.toQDivisor (inverseTransformDivisor g D) := by
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D₁ D₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, map_add, map_add]
  | single P n =>
    rw [toQDivisor_single, inverseTransformDivisor_single, inverseTransformDivisor_single]
    rcases inverseTransformPrimeDivisor g P with _ | E
    · simp
    · exact (toQDivisor_single E n).symm

/-- The multiplicity at a point commutes with regarding divisors as `ℚ`-divisors. -/
theorem multiplicityAt_toQDivisor (D : Divisor Y) (x : Y) :
    (Divisor.toQDivisor D).multiplicityAt x = (D.multiplicityAt x : ℚ) := by
  induction D using Finsupp.induction_linear with
  | zero => simp [multiplicityAt]
  | add D₁ D₂ h₁ h₂ => rw [map_add, multiplicityAt_add, multiplicityAt_add, h₁, h₂, Int.cast_add]
  | single P n =>
    rw [toQDivisor_single, multiplicityAt_single, multiplicityAt_single, nsmul_eq_mul,
      nsmul_eq_mul, Int.cast_mul, Int.cast_natCast]

/-- The multiplicity at a point commutes with `ℤ`-scalar multiplication. -/
theorem multiplicityAt_zsmul (m : ℤ) (B : QDivisor Y) (x : Y) :
    (m • B).multiplicityAt x = m • B.multiplicityAt x := by
  induction B using Finsupp.induction_linear with
  | zero => simp [multiplicityAt]
  | add B₁ B₂ h₁ h₂ => rw [smul_add, multiplicityAt_add, multiplicityAt_add, h₁, h₂, smul_add]
  | single P q =>
    rw [Finsupp.smul_single, multiplicityAt_single, multiplicityAt_single, smul_comm]

/-- **Pulling back a `ℚ`-divisor through a point blow-up of a smooth surface.** For every
`ℚ`-divisor `B` on a smooth surface `Y` over an algebraically closed field and the blow-up `π`
of a closed point `y` with exceptional curve `F`, `π^*B = π⁻¹_* B + (mult_y B) F`. -/
theorem isPullback_qDivisor_blowUp_singleton [IsAlgClosed k] (hY : Mori.IsVariety k sY)
    (hYs : IsSmoothScheme sY) (hYd : topologicalKrullDim Y = 2) {y : Y}
    (hy : IsClosed ({y} : Set Y)) [IsLocallyNoetherian Y] [IsNormal Y]
    [IsLocallyNoetherian (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))]
    [IsNormal (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))]
    {F : Mori.PrimeDivisor (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))}
    (hF : F.idealSheaf = exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))
    (B : QDivisor Y)
    (hB : ∀ Z : irreducibleComponents (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)),
      blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)
        (componentGenericPoint _ Z) ∉ supp B) :
    QDivisor.IsPullback (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)) B hB
      (inverseTransformDivisor (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)) B +
        Finsupp.single F (B.multiplicityAt y)) := by
  intro m hm D hD hDc
  refine ⟨_, ?_, isPullback_blowUp_singleton hY hYs hYd hy hF D _⟩
  rw [map_add, toQDivisor_single, ← inverseTransformDivisor_toQDivisor, hD, smul_add, map_zsmul,
    ← multiplicityAt_toQDivisor, hD, multiplicityAt_zsmul, Finsupp.smul_single]

end PullbackCurve

/-! ### The pull-back as an equality of divisors -/

section PullbackEq

open MMP.Resolution DivisorWithCoeffs

variable {k : Type u} [Field k] {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)}

/-- On a locally Noetherian normal scheme, a prime divisor with invertible ideal sheaf has finite
multiplicity at every point: its local equation is a nonzero element of a Noetherian local
domain, which lies in only finitely many powers of the maximal ideal (Krull). -/
theorem multiplicityAt_ne_top {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    (P : Mori.PrimeDivisor X) (hP : Stacks.Divisors.IsEffectiveCartierDivisor P.idealSheaf)
    (x : X) : P.multiplicityAt x ≠ ⊤ := by
  obtain ⟨W, hW, hxW, s, hs, hspan⟩ :=
    Stacks.Divisors.exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor
      P.idealSheaf hP x
  have hst : P.idealSheaf.stalkIdeal x = Ideal.span {(X.presheaf.germ W x hxW).hom s} := by
    rw [Scheme.IdealSheafData.stalkIdeal_eq_stalk,
      AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ P.idealSheaf x ⟨W, hW⟩ hxW, hspan,
      Ideal.map_span, Set.image_singleton]
  have hg0 : (X.presheaf.germ W x hxW).hom s ≠ 0 :=
    nonZeroDivisors.ne_zero (Stacks.Divisors.germ_mem_nonZeroDivisors hW hs x hxW)
  have hbot := Ideal.iInf_pow_eq_bot_of_isLocalRing (IsLocalRing.maximalIdeal
    (X.presheaf.stalk x)) (IsLocalRing.maximalIdeal.isMaximal _).ne_top
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (X.presheaf.germ W x hxW).hom s ∉
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ N := by
    by_contra hall
    push Not at hall
    exact hg0 (by rw [← Ideal.mem_bot, ← hbot]; exact Ideal.mem_iInf.mpr hall)
  rw [P.multiplicityAt_eq_localMultiplicity hst]
  refine ne_top_of_le_ne_top (ENat.natCast_ne_top N) (iSup₂_le fun j hj => ?_)
  by_contra hlt
  push Not at hlt
  exact hN (Ideal.pow_le_pow_right (by exact_mod_cast hlt.le) hj)

/-- The blow-up of a closed point of a surface variety is quasi-compact. -/
theorem compactSpace_blowUp_singleton (hY : Mori.IsVariety k sY)
    (hYd : topologicalKrullDim Y = 2) {y : Y} (hy : IsClosed ({y} : Set Y)) :
    CompactSpace (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)) := by
  have hvar := isVariety_blowUp_singleton hY hYd hy
  have : QuasiCompact (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) ≫ sY) :=
    hvar.toQuasiCompact
  have : QuasiCompact sY := hY.toQuasiCompact
  exact QuasiCompact.compactSpace_of_compactSpace
    (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) ≫ sY)

/-- The blow-up of a closed point of a surface maps the generic point outside the support of
every divisor (condition `(∗)` of the pull-back). -/
theorem blowUpToBase_componentGenericPoint_notMem_supp {R : Type*} [Zero R]
    (hY : Mori.IsVariety k sY) (hYd : topologicalKrullDim Y = 2) {y : Y}
    (hy : IsClosed ({y} : Set Y)) (D : DivisorWithCoeffs R Y)
    (Z : irreducibleComponents (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))) :
    blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)
      (componentGenericPoint _ Z) ∉ supp D := by
  have : IrreducibleSpace Y := by have := hY.toIsIntegral; infer_instance
  have hvar := isVariety_blowUp_singleton hY hYd hy
  have : IrreducibleSpace (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)) := by
    have := hvar.toIsIntegral; infer_instance
  have := isDominant_blowUpToBase_singleton hYd hy
  exact map_componentGenericPoint_notMem_supp_of_isDominant' _ D Z

/-- **Pulling back a curve through a surface blow-up**, as an equality of divisors. Let `Y` be a
smooth surface over an algebraically closed field `k`, `y ∈ Y` a closed point,
`π : Y' = B_y Y ⟶ Y` the blow-up of `y` and `F = π⁻¹(y)` its exceptional curve. For every curve
(prime divisor) `C` of `Y`, `π^*C = C' + (mult_y C) F`, where `C' = π⁻¹_* C` is the strict
transform; `mult_y C` is finite (`MMP.Threefold.Resolution.multiplicityAt_ne_top`). -/
@[mmp "lem_mmp_threefold_surface_blowup_pullback"]
theorem pullback_single_blowUp_singleton [IsAlgClosed k] (hY : Mori.IsVariety k sY)
    (hYs : IsSmoothScheme sY) (hYd : topologicalKrullDim Y = 2) {y : Y}
    (hy : IsClosed ({y} : Set Y))
    {F : Mori.PrimeDivisor (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))}
    (hF : F.idealSheaf = exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))
    (C : Mori.PrimeDivisor Y) :
    haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hYs).1
    haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hYs).2
    haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme
      (isSmoothScheme_blowUp_singleton hY hYs hYd hy)).1
    haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme
      (isSmoothScheme_blowUp_singleton hY hYs hYd hy)).2
    haveI := compactSpace_blowUp_singleton hY hYd hy
    Divisor.pullback (f := blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))
        (Finsupp.single C 1 : Divisor Y)
        (MMP.Threefold.Mori.isCartier_single_of_isSmoothScheme hYs C)
        (blowUpToBase_componentGenericPoint_notMem_supp hY hYd hy _) =
      inverseTransformDivisor (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))
          (Finsupp.single C 1 : Divisor Y) +
        Finsupp.single F ((C.multiplicityAt y).toNat : ℤ) := by
  have := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hYs).1
  have := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hYs).2
  have := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme
    (isSmoothScheme_blowUp_singleton hY hYs hYd hy)).1
  have := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme
    (isSmoothScheme_blowUp_singleton hY hYs hYd hy)).2
  have := compactSpace_blowUp_singleton hY hYd hy
  refine Divisor.IsPullback.pullback_eq _ ?_
  have h := isPullback_single_blowUp_singleton hY hYs hYd hy hF C
    (blowUpToBase_componentGenericPoint_notMem_supp hY hYd hy _)
  rwa [Finsupp.smul_single, smul_eq_mul, mul_one] at h

/-- **Pulling back a `ℚ`-divisor through a surface blow-up**, as an equality of `ℚ`-divisors:
with `Y`, `y`, `π` and `F` as in `MMP.Threefold.Resolution.pullback_single_blowUp_singleton`,
every `ℚ`-divisor `B` of `Y` satisfies `π^*B = π⁻¹_* B + (mult_y B) F`, the linear extension of
the equality for curves. -/
@[mmp "lem_mmp_threefold_surface_blowup_pullback"]
theorem pullback_qDivisor_blowUp_singleton [IsAlgClosed k] (hY : Mori.IsVariety k sY)
    (hYs : IsSmoothScheme sY) (hYd : topologicalKrullDim Y = 2) {y : Y}
    (hy : IsClosed ({y} : Set Y))
    {F : Mori.PrimeDivisor (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))}
    (hF : F.idealSheaf = exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))
    (B : QDivisor Y) :
    haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hYs).1
    haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hYs).2
    haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme
      (isSmoothScheme_blowUp_singleton hY hYs hYd hy)).1
    haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme
      (isSmoothScheme_blowUp_singleton hY hYs hYd hy)).2
    haveI := compactSpace_blowUp_singleton hY hYd hy
    QDivisor.pullback (f := blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)) B
        (MMP.Fourfold.isQCartier_of_isSmoothScheme hYs B)
        (blowUpToBase_componentGenericPoint_notMem_supp hY hYd hy B) =
      inverseTransformDivisor (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)) B +
        Finsupp.single F (B.multiplicityAt y) := by
  have := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hYs).1
  have := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hYs).2
  have := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme
    (isSmoothScheme_blowUp_singleton hY hYs hYd hy)).1
  have := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme
    (isSmoothScheme_blowUp_singleton hY hYs hYd hy)).2
  have := compactSpace_blowUp_singleton hY hYd hy
  exact QDivisor.IsPullback.pullback_eq _
    (isPullback_qDivisor_blowUp_singleton hY hYs hYd hy hF B _)

end PullbackEq

end MMP.Threefold.Resolution
