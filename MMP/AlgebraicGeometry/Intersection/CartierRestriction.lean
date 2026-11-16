module

public import MMP.AlgebraicGeometry.Intersection.OneCycles
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.EulerPolynomialProper
public import StacksFrontier.Algebra.Polynomial.Numerical
public import StacksFrontier.AlgebraicGeometry.CurveEulerBridge.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.DivisorIntersectionProper
public import MMP.AlgebraicGeometry.Divisor.InvertibleSheafOfEffective
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.Components
public import StacksFrontier.AlgebraicGeometry.Blowup.StructureSheafPushforward
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.Positivity
public import MMP.AlgebraicGeometry.Divisor.SmoothRDivisors
public import MMP.AlgebraicGeometry.Singularities.LogResolution.Basic
public import MMP.AlgebraicGeometry.Divisor.CartierLineBundle
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSheafPullback
public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorPicardClass
public import StacksFrontier.AlgebraicGeometry.Divisors.IdealSheafSections
public import MMP.AlgebraicGeometry.Resolution.SNCRestriction
public import StacksFrontier.AlgebraicGeometry.Properties.NormalConnectedIntegral
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.RegularLocalRing
public import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor

/-!
# Intersection numbers of Cartier divisors: cutting down and isomorphism invariance

The intersection number `(L₁ ⋯ L_d · Z)` of Kollár–Mori, `MMP.Mori.sheafIntersectionNumber`, is
the alternating sum `∑_{I} (-1)^{|I|} χ(Z, 𝒪_Z(-∑_{j ∈ I} L_j))`; the intersection number of the
Stacks project, `AlgebraicGeometry.intersectionNumber`, is the mixed finite difference
`∑_{T} (-1)^{d - |T|} χ(Z, ⨂_{j ∈ T} L_j|_Z)`. Both are the coefficient of `n₁ ⋯ n_d` in the
numerical polynomial `χ(Z, L₁^{n₁} ⊗ ⋯ ⊗ L_d^{n_d}|_Z)`, so they agree
(`MMP.Mori.Snapper.sheafIntersectionNumber_eq_intersectionNumber`). Through this comparison the
library's results on `AlgebraicGeometry.intersectionNumber` (multilinearity, symmetry,
isomorphism invariance, cutting down by an effective Cartier divisor) apply to
`MMP.Mori.sheafIntersectionNumber`.

For an effective Cartier divisor `D` with closed subscheme `MMP.CartierDivisor.subscheme D hD`,
the invertible sheaf `𝒪_X(D)` is the invertible sheaf of the Stacks project of that subscheme,
and cutting down reads `(L₁ ⋯ L_{d+1} · Z) = (L₂ ⋯ L_{d+1} · D)` when `D` is a divisor on the
subscheme `Z` with `L₁|_Z ≅ 𝒪_Z(D)`.

## Main results

* `MMP.Mori.sheafIntersectionNumber_eq_of_isEffective`: cutting down by an effective Cartier
  divisor of the subscheme.
* `MMP.Mori.sheafIntersectionNumber_eq_of_iso`: isomorphic closed subschemes over `X` have the
  same intersection numbers.
* `MMP.Mori.sheafIntersectionNumber_eq_of_ker_eq`: closed subschemes with the same ideal sheaf
  have the same intersection numbers.
* `MMP.Mori.sheafIntersectionNumber_eq_zero_of_iso_unit`: a family with a trivial member has
  intersection number zero.
* `MMP.Fourfold.DoubleSurface.finite`: a divisor on a Noetherian scheme has finitely many double
  surfaces.
* `MMP.Intersection.IsWeilDivisorOfCartier.isEffective`,
  `MMP.Intersection.IsWeilDivisorOfCartier.subscheme_eq_idealSheaf`,
  `MMP.Intersection.IsWeilDivisorOfCartier.isEffective_and_subscheme_eq_of_isSmoothScheme`: on a
  scheme with factorial local rings (a smooth variety), a Cartier divisor whose Weil divisor is a
  prime divisor `E` is effective with closed subscheme `E`.
* `MMP.Mori.PrimeDivisor.mem_ideal_idealSheaf_iff`: the sections of the ideal of a prime divisor.
* `MMP.Mori.nonempty_pullback_cartierSheaf_iso_unit`: `𝒪(D)` restricts trivially to a subscheme
  not meeting `D`.
* `MMP.Mori.eq_vanishingIdeal_mul_vanishingIdeal`: a reduced closed subscheme whose support is
  the disjoint union of two closed sets is the product of their vanishing ideals.
* `MMP.Mori.exists_primeDivisor_support_eq_connectedComponentIn`: the connected components of a
  divisor cut out at each point by one member of a regular system of parameters are prime
  divisors.
* `MMP.Mori.sheafIntersectionNumber_eq_sum_of_support_eq_iUnion`: against a divisor cut out by
  regular parameters whose support is a disjoint union of closed sets, an intersection number is
  the sum of those of the parts.

## Implementation notes

Isomorphism invariance computes
both Euler characteristics on `X`, through the push-forward of `𝒪_Z`.

A Cartier divisor `A` with Weil divisor a prime divisor `E` is compared with `E` stalk by stalk:
the germ of a local equation has order one at the generic point of `E` and zero at the other
points of coheight at most one, so in a factorial local ring it is associated to a generator of
the prime of `E`; the ideals are then compared on affine opens through
`AlgebraicGeometry.IsAffineOpen.mem_ideal_iff`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 1.33–1.34
* [Stacks Project, Tag 0BEP](https://stacks.math.columbia.edu/tag/0BEP)
* [Stacks Project, Tag 0BEU](https://stacks.math.columbia.edu/tag/0BEU)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace MMP.Mori

section Cut

/-- The closed subscheme of an effective Cartier divisor of a closed subscheme `Z` of dimension at
most `d + 1` of a proper `k`-scheme has dimension at most `d`. -/
theorem topologicalKrullDim_subscheme_le_of_isEffective (k : Type u) [Field k]
    {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    (d : ℕ) (hd : topologicalKrullDim Z ≤ (d + 1 : ℕ)) (D : Z.CartierDivisor)
    (hD : MMP.Intersection.IsEffective D) :
    topologicalKrullDim (MMP.CartierDivisor.subscheme D hD).subscheme ≤ (d : WithBot ℕ∞) :=
  haveI := MMP.CartierDivisor.isEffectiveCartierDivisor_subscheme hD
  topologicalKrullDim_subscheme_le_of_isEffectiveCartierDivisor_of_isProper k f i d hd _

/-- **Cutting down by an effective Cartier divisor.** Let `X` be proper over a field `k`,
`i : Z ⟶ X` a closed subscheme of dimension at most `d + 1`, `L₁, …, L_{d+1}` invertible sheaves
on `X`, and `D` an effective Cartier divisor on `Z` with `L₁|_Z ≅ 𝒪_Z(D)`. Then
`(L₁ ⋯ L_{d+1} · Z) = (L₂ ⋯ L_{d+1} · D)`, the right side computed along `D ⟶ Z ⟶ X`. -/
theorem sheafIntersectionNumber_eq_of_isEffective (k : Type u) [Field k]
    {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    (d : ℕ) (hd : topologicalKrullDim Z ≤ (d + 1 : ℕ)) (L : Fin (d + 1) → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)]
    (D : Z.CartierDivisor) (hD : MMP.Intersection.IsEffective D)
    (e : (Scheme.Modules.pullback i).obj (L 0) ≅ MMP.CartierDivisor.sheaf D) :
    sheafIntersectionNumber k f i (d + 1) hd L =
      sheafIntersectionNumber k f ((MMP.CartierDivisor.subscheme D hD).subschemeι ≫ i) d
        (topologicalKrullDim_subscheme_le_of_isEffective k f i d hd D hD)
        fun t : Fin d => L t.succ := by
  have := MMP.CartierDivisor.isEffectiveCartierDivisor_subscheme hD
  rw [Snapper.sheafIntersectionNumber_eq_intersectionNumber,
    Snapper.sheafIntersectionNumber_eq_intersectionNumber]
  exact intersectionNumber_eq_of_isEffectiveCartierDivisor' k f i d hd L _
    (e ≪≫ MMP.CartierDivisor.sheafIsoInvertibleSheaf D hD)

end Cut

section IsoInvariance

attribute [local instance] twistedSheaf_isCoherent isCoherent_pushforward_of_isClosedImmersion
  Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent

/-- The Euler characteristic of a twist of `𝒪_Z` by restrictions, for a closed subscheme
`i : Z ⟶ X` of a proper `k`-scheme, is that of the same twist of `i_*𝒪_Z` on `X`. -/
private theorem eulerCharacteristic_twistedSheaf_unit_eq_pushforward (k : Type u) [Field k]
    {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    {d : ℕ} (L : Fin d → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)] (n : Fin d → ℤ) :
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    @eulerCharacteristic k _ Z (i ≫ f) inferInstance
      (twistedSheaf (SheafOfModules.unit Z.ringCatSheaf)
        (fun j => (Scheme.Modules.pullback i).obj (L j)) n)
      (isCoherent_twistedSheafUnitPullback k f i L n) =
    eulerCharacteristic k f
      (twistedSheaf ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf))
        L n) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsLocallyNoetherian Z := isLocallyNoetherian_of_isClosedImmersion i
  exact (eulerCharacteristic_twistedSheaf_pushforward_of_isClosedImmersion k i f L _ n _ _).symm

/-- **Intersection numbers are invariant under isomorphisms of closed subschemes.** If
`e : Z ≅ Z'` is an isomorphism of schemes over `X` between two closed subschemes `i : Z ⟶ X`,
`i' : Z' ⟶ X` of a proper `k`-scheme, then `(L₁ ⋯ L_d · Z) = (L₁ ⋯ L_d · Z')`. -/
theorem sheafIntersectionNumber_eq_of_iso (k : Type u) [Field k]
    {X Z Z' : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    (i' : Z' ⟶ X) [IsClosedImmersion i'] (e : Z ≅ Z') (he : e.hom ≫ i' = i)
    (d : ℕ) (hd : topologicalKrullDim Z ≤ d) (hd' : topologicalKrullDim Z' ≤ d)
    (L : Fin d → X.Modules) [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)] :
    sheafIntersectionNumber k f i d hd L = sheafIntersectionNumber k f i' d hd' L := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsLocallyNoetherian Z' := isLocallyNoetherian_of_isClosedImmersion i'
  have hunit : (Scheme.Modules.pushforward e.hom).obj (SheafOfModules.unit Z.ringCatSheaf) ≅
      SheafOfModules.unit Z'.ringCatSheaf := by
    have h := isIso_unitToPushforwardObjUnit_of_isIso_c e.hom inferInstance
    exact (@asIso _ _ _ _ _ h).symm
  have hpush : (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf) ≅
      (Scheme.Modules.pushforward i').obj (SheafOfModules.unit Z'.ringCatSheaf) := by
    subst he
    exact ((Scheme.Modules.pushforwardComp e.hom i').app _).symm ≪≫
      (Scheme.Modules.pushforward i').mapIso hunit
  unfold sheafIntersectionNumber
  refine Finset.sum_congr rfl fun I _ => ?_
  congr 1
  rw [eulerCharacteristic_twistedSheaf_unit_eq_pushforward,
    eulerCharacteristic_twistedSheaf_unit_eq_pushforward]
  exact eulerCharacteristic_eq_of_iso k f (twistedSheafIsoOfIso L hpush _)

/-- **Intersection numbers depend only on the ideal sheaf of the closed subscheme.** Two closed
immersions `i : Z ⟶ X`, `i' : Z' ⟶ X` into a proper `k`-scheme with the same kernel give the
same intersection numbers `(L₁ ⋯ L_d · Z) = (L₁ ⋯ L_d · Z')`. -/
theorem sheafIntersectionNumber_eq_of_ker_eq (k : Type u) [Field k]
    {X Z Z' : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    (i' : Z' ⟶ X) [IsClosedImmersion i'] (h : i.ker = i'.ker)
    (d : ℕ) (hd : topologicalKrullDim Z ≤ d) (hd' : topologicalKrullDim Z' ≤ d)
    (L : Fin d → X.Modules) [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)] :
    sheafIntersectionNumber k f i d hd L = sheafIntersectionNumber k f i' d hd' L :=
  haveI := IsClosedImmersion.isIso_lift i' i h.symm
  sheafIntersectionNumber_eq_of_iso k f i i' (asIso (IsClosedImmersion.lift i' i h.symm.le))
    (IsClosedImmersion.lift_fac i' i h.symm.le) d hd hd' L

/-- Equal closed immersions give equal intersection numbers. -/
theorem sheafIntersectionNumber_congr_hom (k : Type u) [Field k]
    {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] {i i' : Z ⟶ X} [IsClosedImmersion i]
    [IsClosedImmersion i'] (h : i = i') (d : ℕ) (hd : topologicalKrullDim Z ≤ d)
    (L : Fin d → X.Modules) [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)] :
    sheafIntersectionNumber k f i d hd L = sheafIntersectionNumber k f i' d hd L := by
  subst h; rfl

/-- Equal families of invertible sheaves give equal intersection numbers. -/
theorem sheafIntersectionNumber_congr_sheaves (k : Type u) [Field k]
    {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    (d : ℕ) (hd : topologicalKrullDim Z ≤ d) {L L' : Fin d → X.Modules}
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)]
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L' j)] (h : L = L') :
    sheafIntersectionNumber k f i d hd L = sheafIntersectionNumber k f i d hd L' := by
  subst h
  rfl

end IsoInvariance

section Trivial

open Stacks.SheafOfModules.Invertible

/-- **A trivial entry kills the intersection number.** If one of the invertible sheaves
`L₁, …, L_d` is isomorphic to `𝒪_X`, then `(L₁ ⋯ L_d · Z) = 0`. -/
theorem sheafIntersectionNumber_eq_zero_of_iso_unit (k : Type u) [Field k]
    {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    (d : ℕ) (hd : topologicalKrullDim Z ≤ d) (L : Fin d → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)] (j : Fin d)
    (e : L j ≅ SheafOfModules.unit X.ringCatSheaf) :
    sheafIntersectionNumber k f i d hd L = 0 := by
  have : ∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (Function.update L j (tensorPower X.presheaf X.ringCatSheaf.2 (L j) 0) q) :=
    isInvertible_update L j _
  rw [Snapper.sheafIntersectionNumber_eq_intersectionNumber,
    intersectionNumber_eq_of_iso_at k f i d hd L
      (Function.update L j (tensorPower X.presheaf X.ringCatSheaf.2 (L j) 0)) j
      (fun q hq => Function.update_of_ne hq _ _)
      (e ≪≫ eqToIso (Function.update_self j _ L).symm)]
  exact intersectionNumber_update_zeroPower k f i d hd L j

end Trivial

end MMP.Mori

namespace MMP.Intersection

open Order

variable {X : Scheme.{u}}

/-- **Orders of a Cartier divisor at a point of coheight one.** If `w` is the Weil divisor of the
Cartier divisor `A` and `a / b` is a local equation of `A` at a point `y` of coheight one, then
`ord_y(a) - ord_y(b)` is the coefficient of `w` at the prime divisor with generic point `y`. -/
theorem IsWeilDivisorOfCartier.ord_sub_ord_eq_coeff [IsLocallyNoetherian X]
    {A : X.CartierDivisor} {w : MMP.Mori.Divisor X} (hA : IsWeilDivisorOfCartier A w) {y : X}
    (hy : coheight y = 1) {f : X.totalQuotientSheaf.presheaf.stalk y}
    (hf : IsLocalEquationAt A y f) {a b : X.presheaf.stalk y} (ha : a ∈ nonZeroDivisors _)
    (hb : b ∈ nonZeroDivisors _) (hab : IsFraction f a b) :
    ((Ring.ord _ a).toNat : ℤ) - (Ring.ord _ b).toNat =
      w.coeff (AlgebraicGeometry.PrimeDivisor.ofCoheightOne y hy) := by
  set P := AlgebraicGeometry.PrimeDivisor.ofCoheightOne y hy
  have hgp : (primeDivisorSubvariety P).genericPoint = y :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne y hy
  have h := hA P
  clear_value P
  subst hgp
  have : Ring.KrullDimLE 1 (X.presheaf.stalk (primeDivisorSubvariety P).genericPoint) :=
    krullDimLE_of_coheight_le (by rw [hy]; rfl)
  exact (isOrderAlong_of_isFraction hf ha hb hab).unique h

/-- A regular local equation of a Cartier divisor on an open `U` of an integral scheme has non-zero
germs at the points of `U`. -/
theorem germ_ne_zero_of_isRegularLocalEquation [IsIntegral X] {A : X.CartierDivisor}
    {U : X.Opens} {g : Γ(X, U)} (hg : MMP.CartierDivisor.IsRegularLocalEquation A g)
    {y : X} (hy : y ∈ U) : X.presheaf.germ U y hy g ≠ 0 := by
  intro h0
  have hg0 : g = 0 := germ_injective_of_isIntegral X y hy (by rw [h0, map_zero])
  have hreg := hg.isRegular
  rw [hg0] at hreg
  have h10 : (1 : Γ(X, U)) = 0 := hreg.1 (by simp)
  have := congrArg (X.presheaf.germ U y hy) h10
  rw [map_one, map_zero] at this
  exact one_ne_zero this

/-- The prime divisor with generic point a coheight-one point `y` is `E` exactly when `y` is the
generic point of `E`. -/
theorem _root_.MMP.Mori.PrimeDivisor.eq_ofCoheightOne_iff (E : MMP.Mori.PrimeDivisor X) {y : X}
    (hy : coheight y = 1) :
    E = AlgebraicGeometry.PrimeDivisor.ofCoheightOne y hy ↔ y = E.genericPoint := by
  constructor
  · rintro rfl
    exact (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne y hy).symm
  · intro hyE
    exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (hyE.symm.trans (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne y hy).symm)

open Classical in
/-- **Orders of a local equation of a prime divisor.** If the Weil divisor of `A` is the prime
divisor `E` and `a / b` is a local equation of `A` at a point `y` of coheight at most one, then
`ord_y(a) = ord_y(b) + 1` if `y` is the generic point of `E`, and `ord_y(a) = ord_y(b)`
otherwise. -/
theorem IsWeilDivisorOfCartier.ord_eq_ord_add_ite [IsIntegral X] [IsLocallyNoetherian X]
    {A : X.CartierDivisor} {E : MMP.Mori.PrimeDivisor X}
    (hA : IsWeilDivisorOfCartier A (Finsupp.single E 1)) {y : X} (hy1 : coheight y ≤ 1)
    {f : X.totalQuotientSheaf.presheaf.stalk y} (hf : IsLocalEquationAt A y f)
    {a b : X.presheaf.stalk y} (ha : a ≠ 0) (hb : b ≠ 0) (hab : IsFraction f a b) :
    Ring.ord _ a = Ring.ord _ b + if y = E.genericPoint then 1 else 0 := by
  have hna := mem_nonZeroDivisors_of_ne_zero ha
  have hnb := mem_nonZeroDivisors_of_ne_zero hb
  rcases Order.le_one_iff.mp hy1 with h0 | h1
  · have : Ring.KrullDimLE 0 (X.presheaf.stalk y) := krullDimLE_of_coheight_le (by rw [h0]; rfl)
    have : IsArtinianRing (X.presheaf.stalk y) := isArtinianRing_iff_krullDimLE_zero.2 this
    have hyE : y ≠ E.genericPoint := by
      rintro rfl
      rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint] at h0
      exact one_ne_zero h0
    rw [Ring.ord_of_isUnit (IsArtinianRing.isUnit_of_mem_nonZeroDivisors hna),
      Ring.ord_of_isUnit (IsArtinianRing.isUnit_of_mem_nonZeroDivisors hnb), ite_eq_right hyE]
    rfl
  · have : Ring.KrullDimLE 1 (X.presheaf.stalk y) := krullDimLE_of_coheight_le (by rw [h1]; rfl)
    have e := hA.ord_sub_ord_eq_coeff h1 hf hna hnb hab
    rw [MMP.Mori.DivisorWithCoeffs.coeff_apply, Finsupp.single_apply] at e
    rw [← ENat.natCast_toNat (Ring.ord_ne_top hna), ← ENat.natCast_toNat (Ring.ord_ne_top hnb)]
    by_cases hyE : y = E.genericPoint
    · rw [ite_eq_left ((E.eq_ofCoheightOne_iff h1).mpr hyE)] at e
      rw [ite_eq_left hyE]
      have : (Ring.ord _ a).toNat = (Ring.ord _ b).toNat + 1 := by omega
      rw [this]
      push_cast
      rfl
    · rw [ite_eq_right fun h => hyE ((E.eq_ofCoheightOne_iff h1).mp h)] at e
      rw [ite_eq_right hyE]
      have : (Ring.ord _ a).toNat = (Ring.ord _ b).toNat := by omega
      rw [this, add_zero]

open Classical in
/-- **Orders of a regular local equation of a prime divisor.** Let `A` be a Cartier divisor on an
integral locally Noetherian scheme whose Weil divisor is a prime divisor `E`, and `g` a regular
local equation of `A` on `U`. At every point `y ∈ U` of coheight at most one, the germ of `g` has
order one if `y` is the generic point of `E` and order zero otherwise. -/
theorem IsWeilDivisorOfCartier.ord_germ_eq_ite [IsIntegral X] [IsLocallyNoetherian X]
    {A : X.CartierDivisor} {E : MMP.Mori.PrimeDivisor X}
    (hA : IsWeilDivisorOfCartier A (Finsupp.single E 1)) {U : X.Opens} {g : Γ(X, U)}
    (hg : MMP.CartierDivisor.IsRegularLocalEquation A g) {y : X} (hy : y ∈ U)
    (hy1 : coheight y ≤ 1) :
    Ring.ord (X.presheaf.stalk y) (X.presheaf.germ U y hy g) =
      if y = E.genericPoint then 1 else 0 := by
  have hne := germ_ne_zero_of_isRegularLocalEquation hg hy
  obtain ⟨hu, hgA⟩ := hg
  have hf : IsLocalEquationAt A y
      (X.totalQuotientSheaf.presheaf.germ U y hy (hu.unit : _)) := ⟨U, hy, hu.unit, hgA, rfl⟩
  have hab : IsFraction (X.totalQuotientSheaf.presheaf.germ U y hy (hu.unit : _))
      (X.presheaf.germ U y hy g) 1 := by
    refine ⟨by rw [map_one]; exact isUnit_one, ?_⟩
    rw [map_one, one_mul, IsUnit.unit_spec]
    exact germ_toTotalQuotient hy g
  rw [hA.ord_eq_ord_add_ite hy1 hf hne one_ne_zero hab, Ring.ord_one, zero_add]

/-- **Sections of the ideal of a prime divisor.** On an affine open `U`, a section `f` lies in the
ideal of the prime divisor `E` exactly when it vanishes at the generic point of `E` whenever that
point lies in `U`. -/
theorem _root_.MMP.Mori.PrimeDivisor.mem_ideal_idealSheaf_iff (E : MMP.Mori.PrimeDivisor X)
    (U : X.affineOpens) (f : Γ(X, U)) :
    f ∈ E.idealSheaf.ideal U ↔ E.genericPoint ∈ U.1 → E.genericPoint ∉ X.basicOpen f := by
  have := E.integral
  rw [Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme E.idealSheaf
    E.idealSheaf.support rfl, Scheme.IdealSheafData.vanishingIdeal_ideal,
    PrimeSpectrum.mem_vanishingIdeal]
  have hsupp : (E.idealSheaf.support : Set X) = closure {E.genericPoint} :=
    AlgebraicGeometry.PrimeDivisor.support_eq_closure E
  have hU : IsAffineOpen U.1 := U.2
  have key : ∀ p : PrimeSpectrum Γ(X, U), f ∉ p.asIdeal ↔ hU.fromSpec p ∈ X.basicOpen f :=
    fun p => by
      have h := congrArg (fun V : (Spec Γ(X, U)).Opens => p ∈ V) (hU.fromSpec_preimage_basicOpen f)
      exact (eq_iff_iff.mp h).symm
  have hr : Set.range hU.fromSpec = U.1 := hU.range_fromSpec
  change (∀ p ∈ hU.fromSpec ⁻¹' (E.idealSheaf.support : Set X), f ∈ p.asIdeal) ↔ _
  rw [hsupp]
  constructor
  · intro H hη hηf
    obtain ⟨p, hp⟩ : E.genericPoint ∈ Set.range hU.fromSpec := hr ▸ hη
    have hpf := H p (by
      change hU.fromSpec p ∈ closure {E.genericPoint}
      rw [hp]
      exact subset_closure rfl)
    exact (key p).mpr (hp ▸ hηf) hpf
  · intro H p hp
    by_contra hpf
    have hpb := (key p).mp hpf
    have hsp : E.genericPoint ⤳ hU.fromSpec p := specializes_iff_mem_closure.2 hp
    have hxU : hU.fromSpec p ∈ U.1 := by
      have h' : hU.fromSpec p ∈ Set.range hU.fromSpec := ⟨p, rfl⟩
      rwa [hr] at h'
    exact H (hsp.mem_open U.1.isOpen hxU) (hsp.mem_open (X.basicOpen f).isOpen hpb)

/-- **A regular local equation of a prime divisor generates its prime.** Let `A` be a Cartier
divisor on an integral locally Noetherian scheme whose Weil divisor is the prime divisor `E`, and
`g` a regular local equation of `A` on `U`. At a point `x ∈ U` with factorial local ring to which
the generic point of `E` specializes, the germ of `g` generates the prime of `𝒪_{X,x}`
corresponding to the generic point. -/
theorem IsWeilDivisorOfCartier.span_germ_eq_primeOfSpecializes [IsIntegral X]
    [IsLocallyNoetherian X] {A : X.CartierDivisor} {E : MMP.Mori.PrimeDivisor X}
    (hA : IsWeilDivisorOfCartier A (Finsupp.single E 1)) {U : X.Opens} {g : Γ(X, U)}
    (hg : MMP.CartierDivisor.IsRegularLocalEquation A g) {x : X} (hx : x ∈ U)
    [UniqueFactorizationMonoid (X.presheaf.stalk x)] (hηx : E.genericPoint ⤳ x) :
    Ideal.span {X.presheaf.germ U x hx g} = primeOfSpecializes hηx := by
  set η := E.genericPoint
  have hη : coheight η = 1 := AlgebraicGeometry.PrimeDivisor.coheight_genericPoint E
  set q := primeOfSpecializes hηx
  have hq1 : q.height = 1 := by
    let := (X.presheaf.stalkSpecializes hηx).hom.toAlgebra
    have := isLocalization_stalkSpecializes hηx
    have e := IsLocalization.AtPrime.ringKrullDim_eq_height q (X.presheaf.stalk η)
    rw [ringKrullDim_stalk_eq_coheight, hη] at e
    exact_mod_cast e.symm
  have hq0 : q ≠ ⊥ := by
    intro h
    rw [h, Ideal.height_bot] at hq1
    exact zero_ne_one hq1
  obtain ⟨π, hπq, hπ⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot inferInstance hq0
  have hqπ : q = Ideal.span {π} := Ideal.eq_span_singleton_of_height_eq_one hq1 hπq hπ
  refine (Ideal.span_singleton_eq_span_singleton.mpr ?_).trans hqπ.symm
  refine associated_of_forall_ord_stalkSpecializes_eq x
    (germ_ne_zero_of_isRegularLocalEquation hg hx) hπ.ne_zero fun y hy hy1 => ?_
  rw [← ConcreteCategory.comp_apply, TopCat.Presheaf.germ_stalkSpecializes,
    hA.ord_germ_eq_ite hg _ hy1]
  by_cases hyη : y = η
  · subst hyη
    rw [ite_eq_left rfl]
    exact (ord_stalkSpecializes_eq_one hy hqπ).symm
  · rw [ite_eq_right hyη]
    refine (ord_stalkSpecializes_of_notMem hy fun hπy => ?_).symm
    have hle : q ≤ primeOfSpecializes hy := by
      rw [hqπ, Ideal.span_singleton_le_iff_mem]
      exact hπy
    have hηy : η ⤳ y := specializes_of_primeOfSpecializes_le hηx hy hle
    have h2 := coheight_add_one_le (lt_of_specializes_of_ne hηy hyη)
    rw [hη] at h2
    exact absurd (h2.trans hy1) (by decide)

/-- **A Cartier divisor with Weil divisor a prime divisor `E` cuts out `E`.** On an integral
locally Noetherian scheme with factorial local rings, let `A` be a Cartier divisor whose Weil
divisor is the prime divisor `E`. On every affine open `U` on which `A` has a regular local
equation `g`, the ideal of `E` is generated by `g`. -/
theorem IsWeilDivisorOfCartier.ideal_idealSheaf_eq_span [IsIntegral X] [IsLocallyNoetherian X]
    (hUFD : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) {A : X.CartierDivisor}
    {E : MMP.Mori.PrimeDivisor X} (hA : IsWeilDivisorOfCartier A (Finsupp.single E 1))
    (U : X.affineOpens) {g : Γ(X, U)}
    (hg : MMP.CartierDivisor.IsRegularLocalEquation A g) :
    E.idealSheaf.ideal U = Ideal.span {g} := by
  set η := E.genericPoint
  have hη : coheight η = 1 := AlgebraicGeometry.PrimeDivisor.coheight_genericPoint E
  have hord := fun y (hy : y ∈ U.1) (hy1 : coheight y ≤ 1) => hA.ord_germ_eq_ite hg hy hy1
  ext f
  rw [E.mem_ideal_idealSheaf_iff]
  constructor
  · intro H
    refine U.2.mem_ideal_iff.mpr fun x hx => ?_
    rw [Ideal.map_span, Set.image_singleton]
    have := hUFD x
    by_cases hηx : η ⤳ x
    · rw [hA.span_germ_eq_primeOfSpecializes hg hx hηx]
      have hηU : η ∈ U.1 := hηx.mem_open U.1.isOpen hx
      change X.presheaf.stalkSpecializes hηx (X.presheaf.germ U.1 x hx f) ∈
        IsLocalRing.maximalIdeal _
      rw [← ConcreteCategory.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
      exact (IsLocalRing.mem_maximalIdeal _).mpr
        fun hu => H hηU ((X.mem_basicOpen f η hηU).mpr hu)
    · have hass : Associated (X.presheaf.germ U.1 x hx g) 1 := by
        refine associated_of_forall_ord_stalkSpecializes_eq x
          (germ_ne_zero_of_isRegularLocalEquation hg hx) one_ne_zero fun y hy hy1 => ?_
        rw [← ConcreteCategory.comp_apply, TopCat.Presheaf.germ_stalkSpecializes,
          hord y _ hy1, map_one, Ring.ord_one, ite_eq_right]
        rintro rfl
        exact hηx hy
      rw [Ideal.span_singleton_eq_top.mpr (hass.isUnit_iff.mpr isUnit_one)]
      exact Submodule.mem_top
  · intro hf hηU hηf
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hf
    have hu := (X.mem_basicOpen _ η hηU).mp hηf
    rw [map_mul] at hu
    have h1 := hord η hηU hη.le
    rw [ite_eq_left rfl, Ring.ord_of_isUnit (isUnit_of_mul_isUnit_right hu)] at h1
    exact zero_ne_one h1

/-- **The subscheme of a Cartier divisor whose Weil divisor is a prime divisor.** On an integral
locally Noetherian scheme with factorial local rings, an effective Cartier divisor whose Weil
divisor is the prime divisor `E` has closed subscheme `E`. -/
theorem IsWeilDivisorOfCartier.subscheme_eq_idealSheaf [IsIntegral X] [IsLocallyNoetherian X]
    (hUFD : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) {A : X.CartierDivisor}
    {E : MMP.Mori.PrimeDivisor X} (hA : IsWeilDivisorOfCartier A (Finsupp.single E 1))
    (hAe : MMP.Intersection.IsEffective A) :
    MMP.CartierDivisor.subscheme A hAe = E.idealSheaf :=
  ((MMP.CartierDivisor.eq_subscheme_iff hAe E.idealSheaf).mpr
    fun U _ hg => hA.ideal_idealSheaf_eq_span hUFD U hg).symm

/-- If a Cartier divisor has a local equation at `x` coming from `𝒪_{X,x}`, then it has a local
equation coming from `𝒪_X` on an open neighbourhood of `x`. -/
theorem IsLocalEquationAt.exists_isEffectiveOn {A : X.CartierDivisor} {x : X}
    {c : X.presheaf.stalk x} (hc : IsLocalEquationAt A x (stalkToTotalQuotient x c)) :
    ∃ U : X.Opens, x ∈ U ∧ MMP.CartierDivisor.IsEffectiveOn A U := by
  obtain ⟨U₁, hxU₁, g₁, hg₁, hgerm⟩ := hc
  obtain ⟨W, hxW, c', rfl⟩ := X.presheaf.exists_germ_eq c
  rw [← germ_toTotalQuotient hxW c'] at hgerm
  obtain ⟨V, hxV, i₁, i₂, heq⟩ := X.totalQuotientSheaf.presheaf.germ_eq x hxU₁ hxW _ _ hgerm
  have e : toTotalQuotient V (X.presheaf.map i₂.op c') = (resUnit i₁ g₁ : _) := by
    have h := toTotalQuotient_res i₂.le c'
    rw [show i₂ = homOfLE i₂.le from rfl, h]
    exact heq.symm
  have hu : IsUnit (toTotalQuotient V (X.presheaf.map i₂.op c')) := e ▸ (resUnit i₁ g₁).isUnit
  refine ⟨V, hxV, X.presheaf.map i₂.op c', hu, ?_⟩
  have hu' : hu.unit = resUnit i₁ g₁ := Units.ext (by rw [IsUnit.unit_spec]; exact e)
  exact hu' ▸ isLocalEquationOn_resUnit i₁ hg₁

/-- **A Cartier divisor whose Weil divisor is a prime divisor is effective.** On an integral
Noetherian scheme with factorial local rings, a Cartier divisor whose Weil divisor is a prime
divisor `E` is effective. -/
theorem IsWeilDivisorOfCartier.isEffective [IsIntegral X] [IsLocallyNoetherian X]
    [TopologicalSpace.NoetherianSpace X]
    (hUFD : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x))
    {A : X.CartierDivisor} {E : MMP.Mori.PrimeDivisor X}
    (hA : IsWeilDivisorOfCartier A (Finsupp.single E 1)) :
    MMP.Intersection.IsEffective A := by
  classical
  intro x
  have := hUFD x
  have hη : coheight E.genericPoint = 1 := AlgebraicGeometry.PrimeDivisor.coheight_genericPoint E
  obtain ⟨U₀, s, hxU₀, hs0, hsord, -⟩ := exists_section_ord_eq_ite hη x (hUFD x)
  obtain ⟨f, hf⟩ := exists_isLocalEquationAt A x
  obtain ⟨a, b, ha, hb, hab⟩ := hf.exists_isFraction
  have hsx0 : X.presheaf.germ U₀ x hxU₀ s ≠ 0 := hs0 x hxU₀
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hass : Associated a (b * X.presheaf.germ U₀ x hxU₀ s) := by
    refine associated_of_forall_ord_stalkSpecializes_eq x ha0 (mul_ne_zero hb0 hsx0)
      fun y hy hy1 => ?_
    rw [ord_stalkSpecializes_mul hy b hsx0,
      ← ConcreteCategory.comp_apply (X.presheaf.germ U₀ x hxU₀),
      TopCat.Presheaf.germ_stalkSpecializes, hsord y (hy.mem_open U₀.isOpen hxU₀) hy1]
    exact hA.ord_eq_ord_add_ite hy1 (hf.stalkSpecializes hy) (stalkSpecializes_ne_zero hy ha0)
      (stalkSpecializes_ne_zero hy hb0) (hab.stalkSpecializes hy)
  obtain ⟨u, hu⟩ := hass
  have hfu : f = stalkToTotalQuotient x
      (X.presheaf.germ U₀ x hxU₀ s * ((u⁻¹ : (X.presheaf.stalk x)ˣ) : X.presheaf.stalk x)) := by
    apply hab.1.mul_left_cancel
    rw [hab.2, ← map_mul, ← mul_assoc, ← hu, mul_assoc, Units.mul_inv, mul_one]
  rw [hfu] at hf
  obtain ⟨U, hxU, g, hg, hloc⟩ := hf.exists_isEffectiveOn
  exact ⟨U, hxU, g, hg, hloc⟩

/-- **Prime divisors on a smooth variety as effective Cartier divisors.** On a smooth variety `X`
over a field, a Cartier divisor `A` whose Weil divisor is a prime divisor `E` is effective, and
its closed subscheme is `E`. -/
theorem IsWeilDivisorOfCartier.isEffective_and_subscheme_eq_of_isSmoothScheme {k : Type u}
    [Field k] (f : X ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k f]
    (hsm : MMP.Mori.IsSmoothScheme f) {A : X.CartierDivisor} {E : MMP.Mori.PrimeDivisor X}
    (hA : IsWeilDivisorOfCartier A (Finsupp.single E 1)) :
    ∃ hAe : MMP.Intersection.IsEffective A,
      MMP.CartierDivisor.subscheme A hAe = E.idealSheaf := by
  let _ : X.Over (Spec (.of k)) := ⟨f⟩
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := ⟨⟩
  have hv : MMP.Mori.IsVariety k (X ↘ Spec (.of k)) := ‹AlgebraicGeometry.IsVariety k f›
  have hUFD : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
    uniqueFactorizationMonoid_stalk_of_isSmoothScheme (k := k) (X := X) hsm
  exact ⟨hA.isEffective hUFD, hA.subscheme_eq_idealSheaf hUFD _⟩

end MMP.Intersection

namespace MMP.Mori

/-- **The invertible sheaf of a divisor restricts trivially away from it.** If the inverse image
of an effective Cartier divisor `D ⊆ Y` along `f : X ⟶ Y` is empty, then `f^*𝒪_Y(D) ≅ 𝒪_X`. -/
theorem nonempty_pullback_invertibleSheaf_iso_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (D : Y.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D] (h : D.comap f = ⊤) :
    Nonempty ((Scheme.Modules.pullback f).obj (Stacks.Divisors.invertibleSheaf' D) ≅
      SheafOfModules.unit X.ringCatSheaf) := by
  have : Stacks.Divisors.IsPullbackDefined f D := by
    change Stacks.Divisors.IsEffectiveCartierDivisor (D.comap f)
    rw [h]; exact Stacks.Divisors.isEffectiveCartierDivisor_top
  exact ⟨Stacks.Divisors.invertibleSheafPullbackIso f D ≪≫ eqToIso (by rw [h]) ≪≫
    Stacks.Divisors.invertibleSheafTopIsoUnit⟩

/-- **`𝒪(D)` restricts trivially away from `D`.** If an effective Cartier divisor `D`
on `Y` does not meet the image of `f : X ⟶ Y`, then `f^*𝒪_Y(D) ≅ 𝒪_X`. -/
theorem nonempty_pullback_cartierSheaf_iso_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (D : Y.CartierDivisor) (hD : MMP.Intersection.IsEffective D)
    (h : Disjoint (Set.range f) (MMP.CartierDivisor.subscheme D hD).support) :
    Nonempty ((Scheme.Modules.pullback f).obj (MMP.CartierDivisor.sheaf D) ≅
      SheafOfModules.unit X.ringCatSheaf) := by
  have := MMP.CartierDivisor.isEffectiveCartierDivisor_subscheme hD
  have htop : (MMP.CartierDivisor.subscheme D hD).comap f = ⊤ := by
    rw [← Scheme.IdealSheafData.support_eq_bot_iff, Scheme.IdealSheafData.support_comap]
    ext x
    simp only [TopologicalSpace.Closeds.coe_preimage, Set.mem_preimage,
      TopologicalSpace.Closeds.coe_bot, Set.mem_empty_iff_false, iff_false]
    exact fun hx => Set.disjoint_left.mp h ⟨x, rfl⟩ hx
  obtain ⟨e⟩ := nonempty_pullback_invertibleSheaf_iso_unit f _ htop
  exact ⟨(Scheme.Modules.pullback f).mapIso
    (MMP.CartierDivisor.sheafIsoInvertibleSheaf D hD) ≪≫ e⟩

end MMP.Mori

namespace MMP.Resolution

variable {X : Scheme.{u}}

/-- **The restriction of an snc divisor component to a subscheme having snc with it.** If `Z`
has simple normal crossings with the family `E` and no `Eⁱ` contains an irreducible component of
`Z`, then every `Eⁱ ∩ Z = (Eⁱ).comap (Z ↪ X)` is, at each of its points, cut out by one member of
a regular system of parameters of `Z`; hence it is an effective Cartier divisor on `Z` and a
reduced closed subscheme. -/
theorem isEffectiveCartierDivisor_and_isReduced_comap_of_hasSNCWith [IsLocallyNoetherian X]
    {Λ : Type*} {E : Λ → X.IdealSheafData} {Z : X.IdealSheafData} (hZ : HasSNCWith E Z)
    (hcomp : ∀ i, ∀ W ∈ componentsOf (Z.support : Set X), ¬ W ⊆ (E i).support) (i : Λ) :
    Stacks.Divisors.IsEffectiveCartierDivisor ((E i).comap Z.subschemeι) ∧
      IsReduced ((E i).comap Z.subschemeι).subscheme := by
  have : IsLocallyNoetherian Z.subscheme := isLocallyNoetherian_of_isClosedImmersion Z.subschemeι
  have hD : ∀ y ∈ ((E i).comap Z.subschemeι).support, ∃ (m : ℕ)
      (w : Fin m → Z.subscheme.presheaf.stalk y) (j : Fin m),
      MMP.Mori.IsRegularSystemOfParameters w ∧
        IdealSheafData.stalk ((E i).comap Z.subschemeι) y = Ideal.span {w j} := by
    intro y hy
    obtain ⟨m, w, c', hw, hc, -⟩ := exists_coordinates_comap_subschemeι_of_hasSNCWith hZ hcomp y
    exact ⟨m, w, c' ⟨i, hy⟩, hw, hc ⟨i, hy⟩⟩
  exact ⟨isEffectiveCartierDivisor_of_stalk_eq_span_parameter _ hD,
    isReduced_subscheme_of_stalk_eq_span_parameter _ hD⟩

end MMP.Resolution

namespace MMP.Mori

open TopologicalSpace

/-! ### Reduced divisors cut out by regular parameters -/

/-- **The stalk of a vanishing ideal is local.** If two closed sets agree on an open
neighbourhood of `y`, their vanishing ideals have the same stalk at `y`. -/
theorem stalk_vanishingIdeal_eq_of_inter_eq {X : Scheme.{u}} (Z₁ Z₂ : Closeds X) {U : X.Opens}
    {y : X} (hy : y ∈ U) (h : (Z₁ : Set X) ∩ U = (Z₂ : Set X) ∩ U) :
    IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal Z₁) y =
      IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal Z₂) y := by
  obtain ⟨V, hV, hyV, hVU⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := y) (U := U) hy
  rw [IdealSheafData.stalk_eq_map_germ _ y ⟨V, hV⟩ hyV,
    IdealSheafData.stalk_eq_map_germ _ y ⟨V, hV⟩ hyV]
  simp only [Scheme.IdealSheafData.vanishingIdeal_ideal]
  congr 2
  ext p
  have hp : hV.fromSpec p ∈ (U : Set X) := by
    apply hVU
    change hV.fromSpec p ∈ (V : Set X)
    rw [← hV.range_fromSpec]
    exact ⟨p, rfl⟩
  change hV.fromSpec p ∈ (Z₁ : Set X) ↔ hV.fromSpec p ∈ (Z₂ : Set X)
  simpa [hp] using Set.ext_iff.mp h (hV.fromSpec p)

private theorem notMem_of_mem_of_disjoint {X : Scheme.{u}} {S T : Closeds X} (hdisj : Disjoint S T)
    {y : X} (hy : y ∈ (S : Set X)) : y ∉ (T : Set X) := fun h => by
  have : y ∈ ((S ⊓ T : Closeds X) : Set X) := ⟨hy, h⟩
  rw [hdisj.eq_bot] at this
  exact this

/-- The stalk of the vanishing ideal of a closed set `T` at a point off `T` is the unit ideal. -/
theorem stalk_vanishingIdeal_eq_top_of_notMem {X : Scheme.{u}} (T : Closeds X) {y : X}
    (hy : y ∉ (T : Set X)) :
    IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal T) y = ⊤ := by
  rw [← MMP.Resolution.Aux.stalk_top y, ← Scheme.IdealSheafData.vanishingIdeal_bot]
  refine stalk_vanishingIdeal_eq_of_inter_eq T ⊥
    (U := ⟨(T : Set X)ᶜ, T.isClosed.isOpen_compl⟩) hy ?_
  ext x
  simp

/-- The stalk of the vanishing ideal of `S` at a point off `T` is that of a reduced closed
subscheme `D` with support `S ∪ T`. -/
theorem stalk_vanishingIdeal_eq_stalk_of_sup_eq {X : Scheme.{u}} (D : X.IdealSheafData)
    [IsReduced D.subscheme] (S T : Closeds X) (hST : S ⊔ T = D.support) {y : X}
    (hy : y ∉ (T : Set X)) :
    IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal S) y =
      IdealSheafData.stalk D y := by
  conv_rhs => rw [Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme D _ rfl]
  refine stalk_vanishingIdeal_eq_of_inter_eq S D.support
    (U := ⟨(T : Set X)ᶜ, T.isClosed.isOpen_compl⟩) hy ?_
  rw [← hST]
  ext x
  simp only [Closeds.coe_sup, Set.mem_inter_iff, Set.mem_union, TopologicalSpace.Opens.coe_mk,
    Set.mem_compl_iff]
  tauto

/-- **Splitting a reduced closed subscheme along a clopen decomposition of its support.** If the
support of a reduced closed subscheme `D` is the disjoint union of the closed sets `S` and `T`,
then `D` is the product of the vanishing ideals of `S` and `T`. -/
theorem eq_vanishingIdeal_mul_vanishingIdeal {X : Scheme.{u}} (D : X.IdealSheafData)
    [IsReduced D.subscheme] (S T : Closeds X) (hST : S ⊔ T = D.support) (hdisj : Disjoint S T) :
    D = Scheme.IdealSheafData.vanishingIdeal S * Scheme.IdealSheafData.vanishingIdeal T := by
  refine IdealSheafData.eq_of_stalk_eq _ _ fun y => ?_
  rw [MMP.Resolution.Aux.stalk_mul]
  by_cases hyS : y ∈ (S : Set X)
  · have hyT := notMem_of_mem_of_disjoint hdisj hyS
    rw [stalk_vanishingIdeal_eq_stalk_of_sup_eq D S T hST hyT,
      stalk_vanishingIdeal_eq_top_of_notMem T hyT, Ideal.mul_top]
  · rw [sup_comm] at hST
    rw [stalk_vanishingIdeal_eq_stalk_of_sup_eq D T S hST hyS,
      stalk_vanishingIdeal_eq_top_of_notMem S hyS, Ideal.top_mul]

open MMP.Resolution in
/-- **A clopen part of a divisor cut out by regular parameters is again one.** If at every point
of its support the ideal of `D` is generated by one member of a regular system of parameters,
and the support of `D` is the disjoint union of the closed sets `S` and `T`, then the vanishing
ideal of `S` has the same property. -/
theorem stalk_vanishingIdeal_eq_span_parameter {X : Scheme.{u}} [IsLocallyNoetherian X]
    (D : X.IdealSheafData)
    (hD : ∀ y ∈ D.support, ∃ (m : ℕ) (w : Fin m → X.presheaf.stalk y) (j : Fin m),
      IsRegularSystemOfParameters w ∧ IdealSheafData.stalk D y = Ideal.span {w j})
    (S T : Closeds X) (hST : S ⊔ T = D.support) (hdisj : Disjoint S T) :
    ∀ y ∈ (Scheme.IdealSheafData.vanishingIdeal S).support, ∃ (m : ℕ)
      (w : Fin m → X.presheaf.stalk y) (j : Fin m), IsRegularSystemOfParameters w ∧
        IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal S) y = Ideal.span {w j} := by
  have := isReduced_subscheme_of_stalk_eq_span_parameter D hD
  intro y hy
  rw [← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal] at hy
  rw [stalk_vanishingIdeal_eq_stalk_of_sup_eq D S T hST (notMem_of_mem_of_disjoint hdisj hy)]
  exact hD y (hST ▸ Or.inl hy)

/-- **Connected components are transported by embeddings.** For an embedding `f` and `x ∈ F`,
the image of the connected component of `x` in `F` is the connected component of `f x` in
`f '' F`. -/
theorem image_connectedComponentIn_of_isEmbedding {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] {f : α → β} (hf : Topology.IsEmbedding f) {F : Set α} {x : α}
    (hx : x ∈ F) : f '' connectedComponentIn F x = connectedComponentIn (f '' F) (f x) := by
  apply subset_antisymm
  · exact hf.continuous.continuousOn.image_connectedComponentIn_subset hx
  · set C := connectedComponentIn (f '' F) (f x)
    have hC : C ⊆ f '' F := connectedComponentIn_subset _ _
    have hCim : f '' (f ⁻¹' C) = C :=
      Set.image_preimage_eq_of_subset (hC.trans (Set.image_subset_range f F))
    have hpc : _root_.IsPreconnected (f ⁻¹' C) := by
      rw [← hf.isInducing.isPreconnected_image, hCim]
      exact isPreconnected_connectedComponentIn
    have hsub : f ⁻¹' C ⊆ F := by
      intro y hy
      obtain ⟨z, hz, hzy⟩ := hC hy
      exact hf.injective hzy ▸ hz
    rw [← hCim]
    exact Set.image_mono (hpc.subset_connectedComponentIn
      (show x ∈ f ⁻¹' C from mem_connectedComponentIn (Set.mem_image_of_mem f hx)) hsub)

/-- In a Noetherian locally Noetherian normal scheme every connected component is irreducible. -/
theorem isIrreducible_connectedComponent_of_isNormal (X : Scheme.{u}) [IsLocallyNoetherian X]
    [NoetherianSpace X] [IsNormal X] (x : X) : IsIrreducible (connectedComponent x) := by
  have hopen : IsOpen (connectedComponent x) := by
    have hc : (connectedComponent x)ᶜ =
        ⋃ Z ∈ {Z ∈ irreducibleComponents X | Disjoint Z (connectedComponent x)}, Z := by
      ext z
      simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
      constructor
      · intro hz
        refine ⟨irreducibleComponent z, ⟨irreducibleComponent_mem_irreducibleComponents z, ?_⟩,
          mem_irreducibleComponent⟩
        have hsub : irreducibleComponent z ⊆ connectedComponent z :=
          isIrreducible_irreducibleComponent.isConnected.isPreconnected.subset_connectedComponent
            mem_irreducibleComponent
        rw [Set.disjoint_left]
        intro w hw hwx
        apply hz
        rw [connectedComponent_eq hwx, ← connectedComponent_eq (hsub hw)]
        exact mem_connectedComponent
      · rintro ⟨Z, ⟨-, hdisj⟩, hzZ⟩ hzx
        exact Set.disjoint_left.mp hdisj hzZ hzx
    rw [← isClosed_compl_iff, hc]
    refine (NoetherianSpace.finite_irreducibleComponents.subset fun Z hZ => hZ.1).isClosed_biUnion
      fun Z hZ => isClosed_of_mem_irreducibleComponents Z hZ.1
  let U : X.Opens := ⟨connectedComponent x, hopen⟩
  have : ConnectedSpace U := isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  have : IsIntegral U := isIntegral_of_isNormal_of_connectedSpace U
  have h := (IrreducibleSpace.isIrreducible_univ (X := U)).image (Subtype.val)
    continuous_subtype_val.continuousOn
  convert h using 1
  ext z
  constructor
  · intro hz
    exact ⟨⟨z, hz⟩, trivial, rfl⟩
  · rintro ⟨w, -, rfl⟩
    exact w.2

open MMP.Resolution in
/-- **Connected components of a divisor cut out by regular parameters are irreducible.** If at
every point of its support the ideal of `D` is generated by one member of a regular system of
parameters, then on a Noetherian scheme each connected component of the support of `D` is
irreducible. -/
theorem isIrreducible_connectedComponentIn_support_of_stalk_eq_span_parameter {Y : Scheme.{u}}
    [IsLocallyNoetherian Y] [NoetherianSpace Y] (D : Y.IdealSheafData)
    (hD : ∀ y ∈ D.support, ∃ (m : ℕ) (w : Fin m → Y.presheaf.stalk y) (j : Fin m),
      IsRegularSystemOfParameters w ∧ IdealSheafData.stalk D y = Ideal.span {w j})
    {y : Y} (hy : y ∈ (D.support : Set Y)) :
    IsIrreducible (connectedComponentIn (D.support : Set Y) y) := by
  have : IsLocallyNoetherian D.subscheme := isLocallyNoetherian_of_isClosedImmersion D.subschemeι
  have : NoetherianSpace D.subscheme :=
    D.subschemeι.isClosedEmbedding.isEmbedding.noetherianSpace
  have : IsNormal D.subscheme := by
    rw [isNormal_iff_stalk_normal]
    intro z
    have := isRegularLocalRing_stalk_subscheme_of_stalk_eq_span_parameter D hD z
    exact ⟨IsRegularLocalRing.isDomain _, isIntegrallyClosed_of_isRegularLocalRing _⟩
  have hrange : Set.range D.subschemeι = (D.support : Set Y) := by
    rw [← D.range_subschemeι]
  obtain ⟨z, rfl⟩ : y ∈ Set.range D.subschemeι := hrange ▸ hy
  have hemb := D.subschemeι.isClosedEmbedding.isEmbedding
  have heq : connectedComponentIn (D.support : Set Y) (D.subschemeι z) =
      D.subschemeι '' connectedComponent z := by
    rw [← connectedComponentIn_univ, image_connectedComponentIn_of_isEmbedding hemb
      (Set.mem_univ z), Set.image_univ, hrange]
  rw [heq]
  exact (isIrreducible_connectedComponent_of_isNormal D.subscheme z).image _
    D.subschemeι.continuous.continuousOn

open MMP.Resolution in
/-- **The connected components of a divisor cut out by regular parameters are prime divisors.**
If at every point of its support the ideal of `D` is generated by one member of a regular system
of parameters, every connected component of the support of `D` is the support of a prime
divisor. -/
theorem exists_primeDivisor_support_eq_connectedComponentIn {Y : Scheme.{u}}
    [IsLocallyNoetherian Y] [NoetherianSpace Y] (D : Y.IdealSheafData)
    (hD : ∀ y ∈ D.support, ∃ (m : ℕ) (w : Fin m → Y.presheaf.stalk y) (j : Fin m),
      IsRegularSystemOfParameters w ∧ IdealSheafData.stalk D y = Ideal.span {w j})
    {y : Y} (hy : y ∈ (D.support : Set Y)) :
    ∃ P : PrimeDivisor Y, P.support = connectedComponentIn (D.support : Set Y) y := by
  set C := connectedComponentIn (D.support : Set Y) y
  have hirr : IsIrreducible C :=
    isIrreducible_connectedComponentIn_support_of_stalk_eq_span_parameter D hD hy
  have hcl : IsClosed C := by
    rw [show C = _ from connectedComponentIn_eq_image hy]
    exact D.support.isClosed.isClosedEmbedding_subtypeVal.isClosedMap _ isClosed_connectedComponent
  have hmax : Maximal (fun W' : IrreducibleCloseds Y ↦ (W' : Set Y) ⊆ D.support)
      ⟨C, hirr, hcl⟩ := by
    refine ⟨connectedComponentIn_subset _ _, fun W hW hle => ?_⟩
    exact W.isIrreducible.isConnected.isPreconnected.subset_connectedComponentIn
      (hle (mem_connectedComponentIn hy)) hW
  have hcod := isPureCodimOne_support_of_stalk_eq_span_parameter D hD _ hmax
  have hgen := hirr.isGenericPoint_genericPoint_closure
  rw [hcl.closure_eq] at hgen
  have hη : Order.coheight hirr.genericPoint = 1 := by
    rw [coheight_eq_codimension_closureSingleton, ← hcod]
    congr 1
    exact IrreducibleCloseds.ext hgen.def
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hη, ?_⟩
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
  exact hgen.def

private theorem disjoint_of_pairwiseDisjoint_insert {X : Scheme.{u}} {ι : Type*} [DecidableEq ι]
    {a : ι} {s : Finset ι} (ha : a ∉ s) {T : ι → Closeds X}
    (hdisj : ((insert a s : Finset ι) : Set ι).PairwiseDisjoint fun b => (T b : Set X))
    (R : Closeds X) (hR : (R : Set X) = ⋃ b ∈ s, (T b : Set X)) : Disjoint (T a) R := by
  have h' : Disjoint (T a : Set X) (R : Set X) := by
    rw [hR, Set.disjoint_iUnion₂_right]
    intro b hb
    exact hdisj (Finset.mem_coe.2 (Finset.mem_insert_self a s))
      (Finset.mem_coe.2 (Finset.mem_insert_of_mem hb)) fun h => ha (h ▸ hb)
  rw [disjoint_iff]
  apply Closeds.ext
  rw [Closeds.coe_inf, Closeds.coe_bot]
  exact Set.disjoint_iff_inter_eq_empty.1 h'

open MMP.Resolution in
/-- **Intersection numbers against a reduced divisor split over a clopen decomposition of its
support.** Let `X` be proper over a field `k` of dimension at most `d + 1`, `L₁, …, L_{d+1}`
invertible sheaves on `X`, and `D ⊆ X` a closed subscheme cut out at each of its points by one
member of a regular system of parameters, with `L₁ ≅ 𝒪_X(D)`. If the support of `D` is the
disjoint union of the closed sets `T_a`, `a ∈ s`, then
`(L₁ ⋯ L_{d+1} · X) = ∑_a (L₂ ⋯ L_{d+1} · T_a)`, each `T_a` with its reduced structure. -/
theorem sheafIntersectionNumber_eq_sum_of_support_eq_iUnion (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (d : ℕ)
    (hd : topologicalKrullDim X ≤ (d + 1 : ℕ)) (L : Fin (d + 1) → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)]
    (D : X.IdealSheafData)
    (hD : ∀ y ∈ D.support, ∃ (m : ℕ) (w : Fin m → X.presheaf.stalk y) (j : Fin m),
      IsRegularSystemOfParameters w ∧ IdealSheafData.stalk D y = Ideal.span {w j})
    (e : L 0 ≅ Stacks.Divisors.invertibleSheaf' D) {ι : Type*} (s : Finset ι)
    (T : ι → Closeds X) (hT : (D.support : Set X) = ⋃ a ∈ s, (T a : Set X))
    (hdisj : (s : Set ι).PairwiseDisjoint fun a => (T a : Set X))
    (hdT : ∀ a, topologicalKrullDim
      (Scheme.IdealSheafData.vanishingIdeal (T a)).subscheme ≤ (d : WithBot ℕ∞)) :
    sheafIntersectionNumber k f (𝟙 X) (d + 1) hd L =
      ∑ a ∈ s, sheafIntersectionNumber k f
        (Scheme.IdealSheafData.vanishingIdeal (T a)).subschemeι d (hdT a)
        fun t => L t.succ := by
  classical
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  induction s using Finset.induction_on generalizing D L with
  | empty =>
    have htop : D = ⊤ := by
      rw [← Scheme.IdealSheafData.support_eq_bot_iff]
      apply Closeds.ext
      simp [hT]
    subst htop
    rw [Finset.sum_empty]
    exact sheafIntersectionNumber_eq_zero_of_iso_unit k f (𝟙 X) (d + 1) hd L 0
      (e ≪≫ Stacks.Divisors.invertibleSheafTopIsoUnit)
  | insert a s ha ih =>
    let R : Closeds X :=
      ⟨⋃ b ∈ s, (T b : Set X), isClosed_biUnion_finset fun b _ => (T b).isClosed⟩
    have := isReduced_subscheme_of_stalk_eq_span_parameter D hD
    have hST : T a ⊔ R = D.support := by
      apply Closeds.ext
      rw [hT, Closeds.coe_sup, Finset.set_biUnion_insert]
      rfl
    have hdj : Disjoint (T a) R := disjoint_of_pairwiseDisjoint_insert ha hdisj R rfl
    have hDeq := eq_vanishingIdeal_mul_vanishingIdeal D (T a) R hST hdj
    have hS := stalk_vanishingIdeal_eq_span_parameter D hD (T a) R hST hdj
    have hR := stalk_vanishingIdeal_eq_span_parameter D hD R (T a) (sup_comm (T a) R ▸ hST)
      hdj.symm
    have := isEffectiveCartierDivisor_of_stalk_eq_span_parameter _ hS
    have := isEffectiveCartierDivisor_of_stalk_eq_span_parameter _ hR
    set VS := Scheme.IdealSheafData.vanishingIdeal (T a)
    set VR := Scheme.IdealSheafData.vanishingIdeal R
    have := isInvertible_update L 0 (Stacks.Divisors.invertibleSheaf' VS)
    have := isInvertible_update L 0 (Stacks.Divisors.invertibleSheaf' VR)
    rw [Snapper.sheafIntersectionNumber_eq_intersectionNumber,
      intersectionNumber_update_tensor k f (𝟙 X) (d + 1) hd 0 L
        (Stacks.Divisors.invertibleSheaf' VS) (Stacks.Divisors.invertibleSheaf' VR)
        (e ≪≫ eqToIso (congrArg Stacks.Divisors.invertibleSheaf' hDeq) ≪≫
          (Stacks.Divisors.invertibleSheafSumIso _ _).symm),
      intersectionNumber_eq_of_isEffectiveCartierDivisor' k f (𝟙 X) d hd
        (Function.update L 0 (Stacks.Divisors.invertibleSheaf' VS)) VS
        ((Scheme.Modules.pullbackId _).app _ ≪≫
          eqToIso (Function.update_self 0 _ L)),
      ← Snapper.sheafIntersectionNumber_eq_intersectionNumber,
      ← Snapper.sheafIntersectionNumber_eq_intersectionNumber,
      sheafIntersectionNumber_congr_hom k f (Category.comp_id VS.subschemeι),
      Finset.sum_insert ha]
    have hsucc : ∀ M : X.Modules, (fun t : Fin d => Function.update L 0 M t.succ) =
        fun t => L t.succ := fun M => funext fun t => Function.update_of_ne (Fin.succ_ne_zero t) _ _
    refine congrArg₂ (· + ·) (sheafIntersectionNumber_congr_sheaves k f _ _ _ (hsucc _)) ?_
    · rw [ih (Function.update L 0 (Stacks.Divisors.invertibleSheaf' VR)) VR hR
        (eqToIso (Function.update_self 0 _ L)) ?_ ?_]
      · exact Finset.sum_congr rfl fun b _ =>
          sheafIntersectionNumber_congr_sheaves k f _ _ _ (hsucc _)
      · exact Scheme.IdealSheafData.coe_support_vanishingIdeal R
      · exact hdisj.subset (Finset.coe_subset.2 (Finset.subset_insert a s))

end MMP.Mori

namespace MMP.Fourfold.DoubleSurface

open TopologicalSpace

variable {Z : Scheme.{u}} {B : MMP.Mori.Divisor Z}

/-- A divisor on a Noetherian scheme has finitely many double surfaces. -/
theorem finite [NoetherianSpace Z] : Finite (DoubleSurface B) := by
  classical
  let S : Set (Set Z) := ⋃ E ∈ (B.support : Set (MMP.Mori.PrimeDivisor Z)),
    ⋃ E' ∈ (B.support : Set (MMP.Mori.PrimeDivisor Z)),
      {S | ∃ σ : DoubleSurface B, σ.fst = E ∧ σ.snd = E' ∧ σ.carrier = S}
  have hS : S.Finite := B.support.finite_toSet.biUnion fun E _ =>
    B.support.finite_toSet.biUnion fun E' _ => finite_setOf_carrier (B := B) E E'
  have := hS.to_subtype
  refine Finite.of_injective (β := B.support × B.support × S)
    (fun σ => (⟨σ.fst, σ.fst_mem⟩, ⟨σ.snd, σ.snd_mem⟩, ⟨σ.carrier, Set.mem_iUnion₂.2
      ⟨σ.fst, σ.fst_mem, Set.mem_iUnion₂.2 ⟨σ.snd, σ.snd_mem, σ, rfl, rfl, rfl⟩⟩⟩)) ?_
  intro σ τ h
  simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
  exact ext h.1 h.2.1 h.2.2

end MMP.Fourfold.DoubleSurface
