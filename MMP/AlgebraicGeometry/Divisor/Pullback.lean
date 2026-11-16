module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Divisor.Principal
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.StalkPrimes
public import StacksFrontier.AlgebraicGeometry.Chow.PointClosureHeightOneCorrespondence
public import StacksFrontier.AlgebraicGeometry.UnitsNormalProper.Hartogs

/-!
# Pull-back of Cartier and `ℚ`-Cartier divisors

Let `f : X ⟶ Y` be a morphism of locally Noetherian normal schemes and `B` a Cartier divisor on
`Y` such that `f` maps the generic point `η_i` of every component `X_i` of `X` outside `Supp B`
(condition `(∗)`; for instance `X`, `Y` integral and `f` dominant). If `φ` is a local equation of
`B` on an open `U` and `y_i = f(η_i) ∈ U`, then `φ` has neither zeros nor poles through `y_i`, so
by algebraic Hartogs for the Noetherian normal domain `𝒪_{Y,y_i}` its component `φ_j` along the
component `Y_j ∋ y_i` is a unit of `𝒪_{Y,y_i}`; its image `f^*_i φ ∈ K(X_i)^×` under the local
homomorphism `𝒪_{Y,y_i} ⟶ 𝒪_{X,η_i} = K(X_i)` is the pull-back of `φ`. A divisor `B'` on `X` is
*the pull-back of `B`*, `B' = f^*B`, if the coefficient of every prime divisor `E ⊆ X_i` meeting
`f⁻¹(U)` is `v_E(f^*_i φ)`, for every local equation `φ` of `B` on every open `U`.

This value does not depend on the local equation: two local equations differ on `U ∩ U'` by a
unit of `𝒪_{Y,f(η_E)}`, whose pull-back is a unit of `𝒪_{X,E}`. Hence, when `X` is moreover
quasi-compact, the pull-back exists and is unique. It is additive, commutes with integral
multiples, and the pull-back of `div(φ)` is `div(f^*φ)`.

A `ℚ`-divisor `B'` is the pull-back of a `ℚ`-Cartier `ℚ`-divisor `B` satisfying `(∗)` if `mB'` is
the pull-back of `mB` for every `m > 0` such that `mB` is a Cartier divisor. It exists and is
unique: `B' = (1/m_B) f^*(m_B B)` for the Cartier index `m_B`.

## Main definitions

* `MMP.Mori.pullbackComponent`: the pull-back `f^*_i φ ∈ K(X_i)^×` of a local equation.
* `MMP.Mori.Divisor.IsPullback`: `B'` is the pull-back `f^*B` of the divisor `B`.
* `MMP.Mori.Divisor.pullback`: the pull-back of a Cartier divisor, for `X` Noetherian.
* `MMP.Mori.QDivisor.IsPullback`, `MMP.Mori.QDivisor.pullback`: the same for `ℚ`-Cartier
  `ℚ`-divisors.
* `MMP.Mori.pullbackRationalFunction`: the pull-back `f^*φ ∈ K(X)^×` of a unit of `K(Y)`.
* `MMP.Mori.PrimeDivisor.ordUnit`: the order of vanishing `v_E` on `K(X_i)^×`.

## Main results

* `MMP.Mori.exists_stalk_eq_of_forall_zero_le_ord`: a unit of `K(Y)` with `v_E ≥ 0` along every
  prime divisor `E` through `y` lies in `𝒪_{Y,y}` (algebraic Hartogs, [Har77, II.6.3A]),
  `MMP.Mori.exists_unit_stalk_of_forall_ord_eq_zero`: with `v_E = 0` it is a unit, and
  `MMP.Mori.Divisor.IsLocalEquation.exists_unit_stalk`: a local equation is a unit off the support.
* `MMP.Mori.ordUnit_pullbackComponent_eq`: independence of the local equation.
* `MMP.Mori.Divisor.IsPullback.eq`, `MMP.Mori.Divisor.IsCartier.exists_isPullback`: uniqueness and
  existence of the pull-back of a Cartier divisor.
* `MMP.Mori.Divisor.isPullback_zero`, `MMP.Mori.Divisor.IsPullback.add`,
  `MMP.Mori.Divisor.IsPullback.zsmul`, `MMP.Mori.Divisor.isPullback_principalDivisor`.
* `MMP.Mori.QDivisor.IsQCartier.existsUnique_isPullback`: existence and uniqueness of the pull-back
  of a `ℚ`-Cartier `ℚ`-divisor, and `MMP.Mori.QDivisor.isPullback_toQDivisor`: compatibility with
  the pull-back of Cartier divisors.

## Implementation notes

The component `Y_j` through `y_i` is `irreducibleComponent y_i` (`MMP.Mori.pointComponent`); on the
normal scheme `Y` it is the only component through `y_i`, and `MMP.Mori.pullbackComponent_eq`
shows that any unit of `𝒪_{Y,y_i}` mapping to `φ_j` along any component through `y_i` has image
`f^*_i φ`. The condition `(∗)` is the hypothesis `hB`, which the predicates take as an argument;
`MMP.Mori.Divisor.IsPullback.of_eq` records that only the divisor matters. The coefficient
`v_E(f^*_i φ)` is read through the valuation `MMP.Mori.PrimeDivisor.valuation` of the discrete
valuation ring `𝒪_{X,E}` on the factor `K(X_i)` of `K(X)`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Notation 0.4(5)
* [R. Hartshorne, *Algebraic geometry*][Har77], II.6
* [Stacks Project, Tag 031T](https://stacks.math.columbia.edu/tag/031T)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Order Topology
open scoped WithZero

universe u

namespace MMP.Mori

variable {X Y : Scheme.{u}}

/-! ### Units of the local ring along a prime divisor -/

namespace PrimeDivisor

variable [IsLocallyNoetherian X] [IsNormal X] (D : PrimeDivisor X)

/-- An element of `𝒪_{X,η_{i(D)}}` on which `v_D` vanishes is the image of a unit of `𝒪_{X,D}`. -/
theorem exists_isUnit_of_valuation_eq_one
    {z : X.presheaf.stalk (componentGenericPoint X D.component)}
    (hz : D.valuation z = 1) : ∃ a : D.localRing, IsUnit a ∧ D.toComponent.hom a = z := by
  let := D.toComponent.hom.toAlgebra
  have := isFractionRing_stalkToRationalFunctions D.genericPoint_mem_component
  have : Ring.KrullDimLE 1 D.localRing := krullDimLE_of_coheight_le D.coheight_genericPoint.le
  have := D.isDiscreteValuationRing_localRing
  let e := IsLocalization.algEquiv (nonZeroDivisors D.localRing)
    (X.presheaf.stalk (componentGenericPoint X D.component)) (FractionRing D.localRing)
  have hmem : e z ∈ MonoidHom.mker (Ring.ordFrac D.localRing) := hz
  rw [Ring.mker_ordFrac_eq_isUnitSubmonoid] at hmem
  obtain ⟨a, ha, hae⟩ := hmem
  exact ⟨a, ha, e.injective ((e.commutes a).trans hae)⟩

/-- If `v_D(φ) ≥ 0`, the component `φ_{i(D)}` lies in the discrete valuation ring `𝒪_{X,D}`. -/
theorem exists_toComponent_eq_of_zero_le_ord {φ : (RationalFunctions X)ˣ} (h : 0 ≤ D.ord φ) :
    ∃ b : D.localRing, D.toComponent.hom b = (φ : RationalFunctions X) D.component := by
  let := D.toComponent.hom.toAlgebra
  have := isFractionRing_stalkToRationalFunctions D.genericPoint_mem_component
  have : Ring.KrullDimLE 1 D.localRing := krullDimLE_of_coheight_le D.coheight_genericPoint.le
  have := D.isDiscreteValuationRing_localRing
  let e := IsLocalization.algEquiv (nonZeroDivisors D.localRing)
    (X.presheaf.stalk (componentGenericPoint X D.component)) (FractionRing D.localRing)
  have hv := D.valuation_component φ
  change Ring.ordFrac D.localRing (e ((φ : RationalFunctions X) D.component)) = _ at hv
  rw [Ring.ordFrac_eq_valuation_inv] at hv
  have hne : (IsDiscreteValuationRing.maximalIdeal D.localRing).valuation
      (FractionRing D.localRing) (e ((φ : RationalFunctions X) D.component)) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr <| (map_ne_zero_iff _ e.injective).mpr
      (φ.isUnit.map (Pi.evalMonoidHom _ D.component)).ne_zero
  obtain ⟨r, hr⟩ := IsDiscreteValuationRing.exists_lift_of_le_one (by
    rwa [← one_le_inv₀ (zero_lt_iff.mpr hne), hv, ← WithZero.exp_zero, WithZero.exp_le_exp])
  exact ⟨r, e.injective <| hr ▸ e.commutes r⟩

end PrimeDivisor

/-! ### Rational functions with no zeros or poles through a point -/

section Hartogs

variable [IsLocallyNoetherian Y] [IsNormal Y]

omit [IsLocallyNoetherian Y] [IsNormal Y] in
/-- The generization `𝒪_{Y,ξ} ⟶ 𝒪_{Y,η_W}` from a prime divisor through `y` to the component
`W ∋ y` factors through `𝒪_{Y,y}`. -/
theorem PrimeDivisor.toComponent_stalkSpecializes (E : PrimeDivisor Y) {y : Y}
    (hspec : E.genericPoint ⤳ y) (hy : y ∈ E.component.1) (t : Y.presheaf.stalk y) :
    E.toComponent.hom (Y.presheaf.stalkSpecializes hspec t) =
      (stalkToRationalFunctions Y hy).hom t := by
  change (Y.presheaf.stalkSpecializes hspec ≫ Y.presheaf.stalkSpecializes _).hom t =
    (Y.presheaf.stalkSpecializes _).hom t
  rw [TopCat.Presheaf.stalkSpecializes_comp]

/-- If `v_E(φ) ≥ 0` for every prime divisor `E` through `y`, then the component `φ_W` along the
component `W ∋ y` lies in `𝒪_{Y,y}`: algebraic Hartogs for the Noetherian normal domain `𝒪_{Y,y}`,
whose height-one primes are the prime divisors through `y` ([Stacks, Tag 031T]). -/
theorem exists_stalk_eq_of_forall_zero_le_ord {y : Y} {W : irreducibleComponents Y}
    (hy : y ∈ W.1) (φ : (RationalFunctions Y)ˣ)
    (h : ∀ E : PrimeDivisor Y, y ∈ E.support → 0 ≤ E.ord φ) :
    ∃ r : Y.presheaf.stalk y,
      (stalkToRationalFunctions Y hy).hom r = (φ : RationalFunctions Y) W := by
  let := (stalkToRationalFunctions Y hy).hom.toAlgebra
  have := isFractionRing_stalkToRationalFunctions hy
  have : IsIntegrallyClosed (Y.presheaf.stalk y) := IsNormal.stalk_normal y
  let : Field (Y.presheaf.stalk (componentGenericPoint Y W)) :=
    (RationalFunctions.isField_stalk Y W).toField
  refine Stacks.AlgebraicGeometry.UnitsNormalProper.exists_algebraMap_eq_of_forall_height_eq_one
    (R := Y.presheaf.stalk y) (Y.presheaf.stalk (componentGenericPoint Y W))
    (z := (φ : RationalFunctions Y) W) fun q hq => ?_
  have hξ1 : coheight (Y.fromSpecStalk y q) = 1 :=
    (Stacks.Chow.coheight_fromSpecStalk_eq_height y q).trans hq
  set E : PrimeDivisor Y := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hξ1
  have hEξ : E.genericPoint = Y.fromSpecStalk y q :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hξ1
  have hspec : E.genericPoint ⤳ y := hEξ ▸ Stacks.Chow.specializes_fromSpecStalk y q
  have hyE : y ∈ E.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact specializes_iff_mem_closure.mp hspec
  obtain rfl : W = E.component :=
    eq_of_mem_irreducibleComponents hy (E.support_subset_component hyE)
  obtain ⟨b, hbz⟩ := E.exists_toComponent_eq_of_zero_le_ord (h E hyE)
  let := (Y.presheaf.stalkSpecializes hspec).hom.toAlgebra
  have := Stacks.Chow.isLocalization_stalk_of_specializes hspec q hEξ.symm
  obtain ⟨⟨a, s⟩, hab⟩ := IsLocalization.mk'_surjective q.asIdeal.primeCompl b
  change IsLocalization.mk' E.localRing a s = b at hab
  refine ⟨a, s, s.2, ?_⟩
  have h2 := congrArg E.toComponent.hom (IsLocalization.mk'_spec E.localRing a s)
  rw [hab, map_mul, hbz] at h2
  change _ * E.toComponent.hom (Y.presheaf.stalkSpecializes hspec s) =
    E.toComponent.hom (Y.presheaf.stalkSpecializes hspec a) at h2
  rwa [E.toComponent_stalkSpecializes hspec hy, E.toComponent_stalkSpecializes hspec hy] at h2

/-- If `v_E(φ) = 0` for every prime divisor `E` through `y`, then the component `φ_W` along the
component `W ∋ y` is a unit of `𝒪_{Y,y}`. -/
theorem exists_unit_stalk_of_forall_ord_eq_zero {y : Y} {W : irreducibleComponents Y}
    (hy : y ∈ W.1) (φ : (RationalFunctions Y)ˣ)
    (h : ∀ E : PrimeDivisor Y, y ∈ E.support → E.ord φ = 0) :
    ∃ a : (Y.presheaf.stalk y)ˣ,
      (stalkToRationalFunctions Y hy).hom a = (φ : RationalFunctions Y) W := by
  obtain ⟨r, hr⟩ := exists_stalk_eq_of_forall_zero_le_ord hy φ fun E hE => (h E hE).ge
  obtain ⟨r', hr'⟩ := exists_stalk_eq_of_forall_zero_le_ord hy φ⁻¹
    fun E hE => by rw [PrimeDivisor.ord_inv, h E hE, neg_zero]
  have h1 : r * r' = 1 := stalkToRationalFunctions_injective hy (by
    rw [map_mul, map_one, hr, hr', ← Pi.mul_apply, Units.mul_inv]
    rfl)
  exact ⟨⟨r, r', h1, mul_comm r' r ▸ h1⟩, hr⟩

/-- **A local equation is a unit off the support.** If `φ` is a local equation of the divisor `B`
on `U` and `y ∈ U ∖ Supp B` lies on the component `W`, then `φ_W` is the image of a unit of
`𝒪_{Y,y}`. -/
theorem Divisor.IsLocalEquation.exists_unit_stalk {B : Divisor Y} {U : Y.Opens}
    {φ : (RationalFunctions Y)ˣ} (hφ : B.IsLocalEquation U φ) {y : Y} (hyU : y ∈ U)
    (hyB : y ∉ B.supp) {W : irreducibleComponents Y} (hy : y ∈ W.1) :
    ∃ a : (Y.presheaf.stalk y)ˣ,
      (stalkToRationalFunctions Y hy).hom a = (φ : RationalFunctions Y) W :=
  exists_unit_stalk_of_forall_ord_eq_zero hy φ fun E hE => by
    rw [← hφ E ⟨y, hE, hyU⟩]
    by_contra hne
    exact hyB (DivisorWithCoeffs.support_subset_supp hne hE)

end Hartogs

/-! ### The order of vanishing on the units of the function field of a component -/

namespace PrimeDivisor

variable [IsLocallyNoetherian X] [IsNormal X] (D : PrimeDivisor X)

/-- `v_D` on the units of the factor `K(X_{i(D)}) = 𝒪_{X,η_{i(D)}}`, as a homomorphism to
`Multiplicative ℤ`. -/
def ordUnitHom : (X.presheaf.stalk (componentGenericPoint X D.component))ˣ →* Multiplicative ℤ :=
  WithZero.unitsWithZeroEquiv.toMonoidHom.comp (Units.map D.valuation.toMonoidHom)

/-- The order of vanishing `v_D(u) ∈ ℤ` of a unit `u` of the function field `K(X_{i(D)})` of the
component of `X` containing `D`. -/
def ordUnit (u : (X.presheaf.stalk (componentGenericPoint X D.component))ˣ) : ℤ :=
  Multiplicative.toAdd (D.ordUnitHom u)

/-- `v_D(uv) = v_D(u) + v_D(v)`. -/
@[simp]
theorem ordUnit_mul (u v : (X.presheaf.stalk (componentGenericPoint X D.component))ˣ) :
    D.ordUnit (u * v) = D.ordUnit u + D.ordUnit v := by
  simp [ordUnit]

/-- `v_D(1) = 0`. -/
@[simp]
theorem ordUnit_one : D.ordUnit 1 = 0 := by
  simp [ordUnit]

/-- `v_D(u^n) = n v_D(u)`. -/
@[simp]
theorem ordUnit_zpow (u : (X.presheaf.stalk (componentGenericPoint X D.component))ˣ) (n : ℤ) :
    D.ordUnit (u ^ n) = n * D.ordUnit u := by
  simp [ordUnit]

/-- The valuation of a unit `u` is `exp (v_D(u))`. -/
theorem valuation_eq_exp_ordUnit (u : (X.presheaf.stalk (componentGenericPoint X D.component))ˣ) :
    D.valuation u = WithZero.exp (D.ordUnit u) := by
  simp [ordUnit, ordUnitHom, WithZero.exp]

/-- `v_D(φ)` is the order of vanishing of the component `φ_{i(D)}`. -/
theorem ord_eq_ordUnit (φ : (RationalFunctions X)ˣ) :
    D.ord φ = D.ordUnit (Units.map (RationalFunctions.component X D.component).toMonoidHom φ) :=
  rfl

/-- A unit of `𝒪_{X,D}` has order zero. -/
theorem ordUnit_eq_zero_of_isUnit {u : (X.presheaf.stalk (componentGenericPoint X D.component))ˣ}
    {a : D.localRing} (ha : IsUnit a) (hu : D.toComponent.hom a = u) : D.ordUnit u = 0 := by
  have h := D.valuation_eq_exp_ordUnit u
  rw [← hu, D.valuation_toComponent_of_isUnit ha] at h
  exact WithZero.exp_eq_one.mp h.symm

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- The generic point of `D` lies in an open `V` exactly when `D` meets `V`. -/
theorem genericPoint_mem_iff (V : X.Opens) :
    D.genericPoint ∈ V ↔ (D.support ∩ V).Nonempty := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact isGenericPoint_closure.mem_open_set_iff V.isOpen

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- If `D` meets an open `V`, so does the component of `X` containing `D`. -/
theorem componentGenericPoint_mem_of_nonempty {V : X.Opens} (h : (D.support ∩ V).Nonempty) :
    componentGenericPoint X D.component ∈ V :=
  (MMP.Mori.genericPoint_mem_iff D.component V).mpr
    (let ⟨x, hxD, hxV⟩ := h; ⟨x, hxV, D.support_subset_component hxD⟩)

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- If `D` meets `f⁻¹(U)`, then `f` maps the generic point of the component of `D` into `U`. -/
theorem map_componentGenericPoint_mem {Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens}
    (h : (D.support ∩ f ⁻¹ᵁ U).Nonempty) : f (componentGenericPoint X D.component) ∈ U :=
  D.componentGenericPoint_mem_of_nonempty h

end PrimeDivisor

/-! ### The pull-back of a local equation -/

/-- The irreducible component `irreducibleComponent y` of `Y` through `y`; on a normal scheme it is
the only one (`MMP.Mori.eq_of_mem_irreducibleComponents`). -/
def pointComponent (y : Y) : irreducibleComponents Y :=
  ⟨irreducibleComponent y, irreducibleComponent_mem_irreducibleComponents y⟩

/-- The point `y` lies on `pointComponent y`. -/
theorem mem_pointComponent (y : Y) : y ∈ (pointComponent y).1 :=
  mem_irreducibleComponent

section PullbackComponent

variable [IsLocallyNoetherian Y] [IsNormal Y] (f : X ⟶ Y) {B : Divisor Y}

/-- The *pull-back* `f^*_i φ ∈ K(X_i)^×` of a local equation `φ` of `B` on `U` to a component
`X_i = Z` of `X` with `y_i = f(η_i) ∈ U`, when `y_i ∉ Supp B`: the image of the unit `φ_j` of
`𝒪_{Y,y_i}` (`MMP.Mori.Divisor.IsLocalEquation.exists_unit_stalk`, `Y_j` the component through
`y_i`) under the local homomorphism `𝒪_{Y,y_i} ⟶ 𝒪_{X,η_i} = K(X_i)`. -/
@[mmp "def_km0_pullback_cartier"]
def pullbackComponent (hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ B.supp)
    {U : Y.Opens} {φ : (RationalFunctions Y)ˣ} (hφ : B.IsLocalEquation U φ)
    (Z : irreducibleComponents X) (hZ : f (componentGenericPoint X Z) ∈ U) :
    (X.presheaf.stalk (componentGenericPoint X Z))ˣ :=
  Units.map (f.stalkMap (componentGenericPoint X Z)).hom.toMonoidHom
    (hφ.exists_unit_stalk hZ (hB Z) (mem_pointComponent _)).choose

variable {f}

/-- `f^*_i φ` is the image of any unit of `𝒪_{Y,y_i}` whose image in `K(Y_j)` is `φ_j`. -/
theorem pullbackComponent_eq (hB : ∀ Z : irreducibleComponents X,
      f (componentGenericPoint X Z) ∉ B.supp)
    {U : Y.Opens} {φ : (RationalFunctions Y)ˣ} (hφ : B.IsLocalEquation U φ)
    {Z : irreducibleComponents X} (hZ : f (componentGenericPoint X Z) ∈ U)
    {W : irreducibleComponents Y} (hW : f (componentGenericPoint X Z) ∈ W.1)
    (a : (Y.presheaf.stalk (f (componentGenericPoint X Z)))ˣ)
    (ha : (stalkToRationalFunctions Y hW).hom a = (φ : RationalFunctions Y) W) :
    pullbackComponent f hB hφ Z hZ =
      Units.map (f.stalkMap (componentGenericPoint X Z)).hom.toMonoidHom a := by
  obtain rfl : W = pointComponent _ := eq_of_mem_irreducibleComponents hW (mem_pointComponent _)
  have hspec := (hφ.exists_unit_stalk hZ (hB Z) (mem_pointComponent _)).choose_spec
  have : (hφ.exists_unit_stalk hZ (hB Z) (mem_pointComponent _)).choose = a :=
    Units.ext (stalkToRationalFunctions_injective hW (hspec.trans ha.symm))
  rw [pullbackComponent, this]

/-- `f^*_i(φψ) = f^*_i φ · f^*_i ψ`. -/
theorem pullbackComponent_mul {B₁ B₂ : Divisor Y}
    (hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ B.supp)
    (hB₁ : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ B₁.supp)
    (hB₂ : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ B₂.supp)
    {U U₁ U₂ : Y.Opens} {φ ψ : (RationalFunctions Y)ˣ} (hφψ : B.IsLocalEquation U (φ * ψ))
    (hφ : B₁.IsLocalEquation U₁ φ) (hψ : B₂.IsLocalEquation U₂ ψ)
    {Z : irreducibleComponents X} (hZ : f (componentGenericPoint X Z) ∈ U)
    (hZ₁ : f (componentGenericPoint X Z) ∈ U₁) (hZ₂ : f (componentGenericPoint X Z) ∈ U₂) :
    pullbackComponent f hB hφψ Z hZ =
      pullbackComponent f hB₁ hφ Z hZ₁ * pullbackComponent f hB₂ hψ Z hZ₂ := by
  have hW := mem_pointComponent (f (componentGenericPoint X Z))
  obtain ⟨a, ha⟩ := hφ.exists_unit_stalk hZ₁ (hB₁ Z) hW
  obtain ⟨b, hb⟩ := hψ.exists_unit_stalk hZ₂ (hB₂ Z) hW
  rw [pullbackComponent_eq hB₁ hφ hZ₁ hW a ha, pullbackComponent_eq hB₂ hψ hZ₂ hW b hb,
    pullbackComponent_eq hB hφψ hZ hW (a * b) (by
      rw [Units.val_mul, map_mul, ha, hb, Units.val_mul, Pi.mul_apply]), map_mul]

/-- `f^*_i(φ^n) = (f^*_i φ)^n`. -/
theorem pullbackComponent_zpow {B₁ : Divisor Y}
    (hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ B.supp)
    (hB₁ : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ B₁.supp)
    {U U₁ : Y.Opens} {φ : (RationalFunctions Y)ˣ} (n : ℤ) (hφn : B.IsLocalEquation U (φ ^ n))
    (hφ : B₁.IsLocalEquation U₁ φ)
    {Z : irreducibleComponents X} (hZ : f (componentGenericPoint X Z) ∈ U)
    (hZ₁ : f (componentGenericPoint X Z) ∈ U₁) :
    pullbackComponent f hB hφn Z hZ = pullbackComponent f hB₁ hφ Z hZ₁ ^ n := by
  have hW := mem_pointComponent (f (componentGenericPoint X Z))
  obtain ⟨a, ha⟩ := hφ.exists_unit_stalk hZ₁ (hB₁ Z) hW
  rw [pullbackComponent_eq hB₁ hφ hZ₁ hW a ha,
    pullbackComponent_eq hB hφn hZ hW (a ^ n) ?_, map_zpow]
  have h1 : Units.map (stalkToRationalFunctions Y hW).hom.toMonoidHom a =
      Units.map (RationalFunctions.component Y (pointComponent _)).toMonoidHom φ := Units.ext ha
  have h2 := congrArg (fun u => (u ^ n : (Y.presheaf.stalk (componentGenericPoint Y _))ˣ).val) h1
  simp only [← map_zpow] at h2
  exact h2

end PullbackComponent

/-! ### Independence of the local equation -/

section Independence

variable [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] {f : X ⟶ Y}
  {B : Divisor Y}

/-- **Independence of the local equation.** If `φ`, `φ'` are local equations of `B` on `U`, `U'`
and the prime divisor `E` of `X` meets both `f⁻¹(U)` and `f⁻¹(U')`, then
`v_E(f^*_i φ) = v_E(f^*_i φ')`: on `U ∩ U'` the quotient `φ/φ'` has no zeros or poles, so it is a
unit of `𝒪_{Y,f(η_E)}`, and its pull-back is a unit of `𝒪_{X,E}`. -/
theorem ordUnit_pullbackComponent_eq
    (hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ B.supp)
    {U U' : Y.Opens} {φ φ' : (RationalFunctions Y)ˣ} (hφ : B.IsLocalEquation U φ)
    (hφ' : B.IsLocalEquation U' φ') (E : PrimeDivisor X)
    (hE : (E.support ∩ f ⁻¹ᵁ U).Nonempty) (hE' : (E.support ∩ f ⁻¹ᵁ U').Nonempty) :
    E.ordUnit (pullbackComponent f hB hφ E.component (E.map_componentGenericPoint_mem f hE)) =
      E.ordUnit
        (pullbackComponent f hB hφ' E.component (E.map_componentGenericPoint_mem f hE')) := by
  have hyU : f E.genericPoint ∈ U := (E.genericPoint_mem_iff (f ⁻¹ᵁ U)).mpr hE
  have hyU' : f E.genericPoint ∈ U' := (E.genericPoint_mem_iff (f ⁻¹ᵁ U')).mpr hE'
  have hsp' : f (componentGenericPoint X E.component) ⤳ f E.genericPoint :=
    f.base.hom.map_specializes E.specializes_genericPoint
  set W := pointComponent (f (componentGenericPoint X E.component))
  have hW : f (componentGenericPoint X E.component) ∈ W.1 := mem_pointComponent _
  have hyW : f E.genericPoint ∈ W.1 :=
    hsp'.mem_closed (isClosed_of_mem_irreducibleComponents _ W.2) hW
  obtain ⟨c, hc⟩ := exists_unit_stalk_of_forall_ord_eq_zero hyW (φ / φ') fun D hD => by
    rw [PrimeDivisor.ord_div, ← hφ D ⟨_, hD, hyU⟩, ← hφ' D ⟨_, hD, hyU'⟩, sub_self]
  obtain ⟨a', ha'⟩ := hφ'.exists_unit_stalk (E.map_componentGenericPoint_mem f hE')
    (hB _) hW
  let c' : (Y.presheaf.stalk (f (componentGenericPoint X E.component)))ˣ :=
    Units.map (Y.presheaf.stalkSpecializes hsp').hom.toMonoidHom c
  have hc' : (stalkToRationalFunctions Y hW).hom c' =
      ((φ / φ' : (RationalFunctions Y)ˣ) : RationalFunctions Y) W := by
    rw [← hc]
    change (Y.presheaf.stalkSpecializes hsp' ≫ Y.presheaf.stalkSpecializes _).hom
        c.val = (Y.presheaf.stalkSpecializes _).hom c.val
    rw [TopCat.Presheaf.stalkSpecializes_comp]
  have hca : (stalkToRationalFunctions Y hW).hom ↑(c' * a') = (φ : RationalFunctions Y) W := by
    rw [Units.val_mul, map_mul, hc', ha', ← Pi.mul_apply, ← Units.val_mul, div_mul_cancel]
  rw [pullbackComponent_eq hB hφ _ hW (c' * a') hca, pullbackComponent_eq hB hφ' _ hW a' ha',
    map_mul, PrimeDivisor.ordUnit_mul, add_eq_right]
  refine E.ordUnit_eq_zero_of_isUnit (c.isUnit.map (f.stalkMap E.genericPoint).hom) ?_
  change (X.presheaf.stalkSpecializes _).hom ((f.stalkMap E.genericPoint).hom c.val) =
    (f.stalkMap _).hom ((Y.presheaf.stalkSpecializes hsp').hom c.val)
  rw [Scheme.Hom.stalkSpecializes_stalkMap_apply]

end Independence

/-! ### The pull-back of a Cartier divisor -/

section Pullback

variable [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] (f : X ⟶ Y)

/-- Let `f : X ⟶ Y` be a morphism of normal schemes and `B` a divisor on `Y` such that `f` maps
the generic point of every component of `X` outside `Supp B` (condition `(∗)`, `hB`). A divisor
`B'` on `X` is *the pull-back of `B`*, `B' = f^*B`, if for every local equation `φ` of `B` on an
open `U ⊆ Y` and every prime divisor `E` of `X` meeting `f⁻¹(U)`, lying on the component `X_i`,
the coefficient of `E` in `B'` is `v_E(f^*_i φ)` (`MMP.Mori.pullbackComponent`). -/
@[mmp "def_km0_pullback_cartier"]
def Divisor.IsPullback (B : Divisor Y)
    (hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ B.supp)
    (B' : Divisor X) : Prop :=
  ∀ (U : Y.Opens) (φ : (RationalFunctions Y)ˣ) (hφ : B.IsLocalEquation U φ) (E : PrimeDivisor X)
    (hE : (E.support ∩ f ⁻¹ᵁ U).Nonempty),
    B'.coeff E =
      E.ordUnit (pullbackComponent f hB hφ E.component (E.map_componentGenericPoint_mem f hE))

variable {f}

namespace Divisor

/-- To be the pull-back it suffices that the coefficient of each `E` be given by one local
equation on an open whose preimage meets `E`. -/
theorem IsPullback.of_forall_exists {B : Divisor Y}
    {hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ B.supp}
    {B' : Divisor X}
    (h : ∀ E : PrimeDivisor X, ∃ (U : Y.Opens) (φ : (RationalFunctions Y)ˣ)
      (hφ : B.IsLocalEquation U φ) (hE : (E.support ∩ f ⁻¹ᵁ U).Nonempty),
      B'.coeff E = E.ordUnit
        (pullbackComponent f hB hφ E.component (E.map_componentGenericPoint_mem f hE))) :
    B.IsPullback f hB B' := by
  intro U φ hφ E hE
  obtain ⟨U', φ', hφ', hE', h'⟩ := h E
  rw [h', ordUnit_pullbackComponent_eq hB hφ' hφ E hE' hE]

/-- A Cartier divisor has at most one pull-back. -/
theorem IsPullback.eq {B : Divisor Y} (hBc : B.IsCartier)
    {hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ B.supp}
    {B₁ B₂ : Divisor X} (h₁ : B.IsPullback f hB B₁) (h₂ : B.IsPullback f hB B₂) : B₁ = B₂ := by
  ext E
  obtain ⟨U, hU, φ, hφ⟩ := hBc (f E.genericPoint)
  have hE : (E.support ∩ f ⁻¹ᵁ U).Nonempty := (E.genericPoint_mem_iff (f ⁻¹ᵁ U)).mp hU
  rw [h₁ U φ hφ E hE, h₂ U φ hφ E hE]

/-- **Existence of the pull-back.** On a Noetherian normal scheme `X`, a Cartier divisor `B` on the
normal scheme `Y` satisfying `(∗)` has a pull-back: the coefficient of `E` is `v_E(f^*_i φ)` for a
local equation `φ` near `f(η_E)`, independent of the choice, and nonzero for only finitely many `E`
since finitely many of the opens `f⁻¹(U)` cover `X`. -/
theorem IsCartier.exists_isPullback [CompactSpace X] {B : Divisor Y} (hBc : B.IsCartier)
    (hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ B.supp) :
    ∃ B' : Divisor X, B.IsPullback f hB B' := by
  classical
  choose U hU φ hφ using hBc
  have hmem : ∀ E : PrimeDivisor X, (E.support ∩ f ⁻¹ᵁ U (f E.genericPoint)).Nonempty :=
    fun E => (E.genericPoint_mem_iff _).mp (hU _)
  let c : PrimeDivisor X → ℤ := fun E => E.ordUnit (pullbackComponent f hB (hφ (f E.genericPoint))
    E.component (E.map_componentGenericPoint_mem f (hmem E)))
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : X => (f ⁻¹ᵁ U (f x) : Set X))
    (fun x => (f ⁻¹ᵁ U (f x)).isOpen) (fun x _ => Set.mem_iUnion.mpr ⟨x, hU (f x)⟩)
  let ψ : X → (RationalFunctions X)ˣ := fun x => (RationalFunctions.unitsEquiv X).symm fun Z =>
    if hZ : f (componentGenericPoint X Z) ∈ U (f x) then pullbackComponent f hB (hφ (f x)) Z hZ
    else 1
  have hψ : ∀ (x : X) (E : PrimeDivisor X) (hE : (E.support ∩ f ⁻¹ᵁ U (f x)).Nonempty),
      E.ord (ψ x) = c E := by
    intro x E hE
    rw [PrimeDivisor.ord_eq_ordUnit]
    have : Units.map (RationalFunctions.component X E.component).toMonoidHom (ψ x) =
        pullbackComponent f hB (hφ (f x)) E.component
          (E.map_componentGenericPoint_mem f hE) := by
      ext
      change (if hZ : f (componentGenericPoint X E.component) ∈ U (f x) then
        pullbackComponent f hB (hφ (f x)) E.component hZ else 1).val = _
      rw [dite_eq_left (E.map_componentGenericPoint_mem f hE)]
    rw [this]
    exact ordUnit_pullbackComponent_eq hB _ _ E hE (hmem E)
  have hfin : {E : PrimeDivisor X | c E ≠ 0}.Finite := by
    refine (Set.Finite.biUnion t.finite_toSet fun x _ => finite_ord_ne_zero (ψ x)).subset ?_
    intro E hE
    obtain ⟨x, hx, hxE⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ E.genericPoint))
    have hE' : (E.support ∩ f ⁻¹ᵁ U (f x)).Nonempty := (E.genericPoint_mem_iff _).mp hxE
    exact Set.mem_iUnion₂.mpr ⟨x, hx, by rwa [Set.mem_ofPred_eq, hψ x E hE']⟩
  refine ⟨Finsupp.ofSupportFinite c hfin, IsPullback.of_forall_exists fun E =>
    ⟨_, _, hφ (f E.genericPoint), hmem E, rfl⟩⟩

/-- The pull-back `f^*B` of a Cartier divisor `B` satisfying `(∗)`, for `X` Noetherian. -/
def pullback [CompactSpace X] (B : Divisor Y) (hBc : B.IsCartier)
    (hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ B.supp) : Divisor X :=
  (hBc.exists_isPullback hB).choose

/-- `Divisor.pullback f B` is the pull-back of `B`. -/
theorem isPullback_pullback [CompactSpace X] {B : Divisor Y} (hBc : B.IsCartier)
    (hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ B.supp) :
    B.IsPullback f hB (B.pullback hBc hB) :=
  (hBc.exists_isPullback hB).choose_spec

/-- Any pull-back of the Cartier divisor `B` equals `Divisor.pullback f B`. -/
theorem IsPullback.pullback_eq [CompactSpace X] {B : Divisor Y} (hBc : B.IsCartier)
    {hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ B.supp}
    {B' : Divisor X} (h : B.IsPullback f hB B') : B.pullback hBc hB = B' :=
  (isPullback_pullback hBc hB).eq hBc h

/-! ### Additivity and principal divisors -/

/-- If `φ` is a local equation of `D` on `U`, then `φ ^ n` is one of `n • D` on `U`. -/
theorem IsLocalEquation.zsmul {D : Divisor Y} {U : Y.Opens} {φ : (RationalFunctions Y)ˣ}
    (h : D.IsLocalEquation U φ) (n : ℤ) : (n • D).IsLocalEquation U (φ ^ n) :=
  fun E hE => by rw [DivisorWithCoeffs.coeff_smul, h E hE, PrimeDivisor.ord_zpow]

/-- The pull-back predicate only depends on the divisor, not on the proof of `(∗)`. -/
theorem IsPullback.of_eq {B₁ B₂ : Divisor Y} (h : B₁ = B₂)
    {hB₁ : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ B₁.supp}
    {hB₂ : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ B₂.supp}
    {B' : Divisor X} (hp : B₁.IsPullback f hB₁ B') : B₂.IsPullback f hB₂ B' := by
  subst h
  exact hp

/-- `f^*0 = 0`. -/
theorem isPullback_zero
    (hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ (0 : Divisor Y).supp) :
    (0 : Divisor Y).IsPullback f hB 0 := by
  refine IsPullback.of_forall_exists fun E =>
    ⟨⊤, 1, isLocalEquation_zero ⊤, (E.genericPoint_mem_iff _).mp trivial, ?_⟩
  rw [pullbackComponent_eq hB _ _ (mem_pointComponent _) 1 (by simp), map_one,
    PrimeDivisor.ordUnit_one, DivisorWithCoeffs.coeff_zero]

/-- **Additivity.** `f^*(B₁ + B₂) = f^*B₁ + f^*B₂` for Cartier divisors `B₁, B₂`. -/
theorem IsPullback.add {B₁ B₂ : Divisor Y} (hB₁c : B₁.IsCartier) (hB₂c : B₂.IsCartier)
    {hB₁ : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ B₁.supp}
    {hB₂ : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ B₂.supp}
    (hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ (B₁ + B₂).supp)
    {B₁' B₂' : Divisor X} (h₁ : B₁.IsPullback f hB₁ B₁') (h₂ : B₂.IsPullback f hB₂ B₂') :
    (B₁ + B₂).IsPullback f hB (B₁' + B₂') := by
  refine IsPullback.of_forall_exists fun E => ?_
  obtain ⟨U₁, hU₁, φ₁, hφ₁⟩ := hB₁c (f E.genericPoint)
  obtain ⟨U₂, hU₂, φ₂, hφ₂⟩ := hB₂c (f E.genericPoint)
  have hE₁ : (E.support ∩ f ⁻¹ᵁ U₁).Nonempty := (E.genericPoint_mem_iff _).mp hU₁
  have hE₂ : (E.support ∩ f ⁻¹ᵁ U₂).Nonempty := (E.genericPoint_mem_iff _).mp hU₂
  have hE : (E.support ∩ f ⁻¹ᵁ (U₁ ⊓ U₂)).Nonempty :=
    (E.genericPoint_mem_iff (f ⁻¹ᵁ (U₁ ⊓ U₂))).mp ⟨hU₁, hU₂⟩
  refine ⟨U₁ ⊓ U₂, φ₁ * φ₂, (hφ₁.mono inf_le_left).add (hφ₂.mono inf_le_right), hE, ?_⟩
  rw [DivisorWithCoeffs.coeff_add, h₁ U₁ φ₁ hφ₁ E hE₁, h₂ U₂ φ₂ hφ₂ E hE₂,
    pullbackComponent_mul hB hB₁ hB₂ _ hφ₁ hφ₂ _ (E.map_componentGenericPoint_mem f hE₁)
      (E.map_componentGenericPoint_mem f hE₂), PrimeDivisor.ordUnit_mul]

/-- `f^*(nB) = n f^*B` for a Cartier divisor `B` and `n ∈ ℤ`. -/
theorem IsPullback.zsmul {B : Divisor Y} (hBc : B.IsCartier)
    {hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ B.supp}
    {B' : Divisor X} (h : B.IsPullback f hB B') (n : ℤ)
    (hBn : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ (n • B).supp) :
    (n • B).IsPullback f hBn (n • B') := by
  refine IsPullback.of_forall_exists fun E => ?_
  obtain ⟨U, hU, φ, hφ⟩ := hBc (f E.genericPoint)
  have hE : (E.support ∩ f ⁻¹ᵁ U).Nonempty := (E.genericPoint_mem_iff _).mp hU
  refine ⟨U, φ ^ n, hφ.zsmul n, hE, ?_⟩
  rw [DivisorWithCoeffs.coeff_smul, h U φ hφ E hE,
    pullbackComponent_zpow hBn hB n _ hφ _ (E.map_componentGenericPoint_mem f hE),
    PrimeDivisor.ordUnit_zpow, smul_eq_mul]

end Divisor

/-- The pull-back `f^*φ ∈ K(X)^×` of a unit `φ` of `K(Y)` whose divisor satisfies `(∗)`: its
component along `X_i` is `f^*_i φ`, `φ` being a local equation of `div(φ)` on all of `Y`. -/
def pullbackRationalFunction [CompactSpace Y] (f : X ⟶ Y) (φ : (RationalFunctions Y)ˣ)
    (hφ : ∀ Z : irreducibleComponents X,
      f (componentGenericPoint X Z) ∉ (principalDivisor φ).supp) :
    (RationalFunctions X)ˣ :=
  (RationalFunctions.unitsEquiv X).symm fun Z =>
    pullbackComponent f hφ (Divisor.isLocalEquation_principalDivisor φ ⊤) Z trivial

/-- **The pull-back of a principal divisor is principal**: `f^* div(φ) = div(f^*φ)`. -/
theorem Divisor.isPullback_principalDivisor [CompactSpace X] [CompactSpace Y]
    (φ : (RationalFunctions Y)ˣ)
    (hφ : ∀ Z : irreducibleComponents X,
      f (componentGenericPoint X Z) ∉ (principalDivisor φ).supp) :
    (principalDivisor φ).IsPullback f hφ (principalDivisor (pullbackRationalFunction f φ hφ)) :=
  IsPullback.of_forall_exists fun E =>
    ⟨⊤, φ, isLocalEquation_principalDivisor φ ⊤, (E.genericPoint_mem_iff _).mp trivial, rfl⟩

end Pullback

/-! ### The pull-back of a `ℚ`-Cartier `ℚ`-divisor -/

section QPullback

variable [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] (f : X ⟶ Y)

omit [IsLocallyNoetherian Y] [IsNormal Y] in
/-- `Supp (mB) = Supp B` for `m ≠ 0`. -/
theorem QDivisor.supp_zsmul {B : QDivisor Y} {m : ℤ} (hm : m ≠ 0) : (m • B).supp = B.supp := by
  ext y
  simp only [SetLike.mem_coe, DivisorWithCoeffs.mem_supp_iff, DivisorWithCoeffs.coeff_smul,
    ne_eq, smul_eq_zero, hm, false_or]

omit [IsLocallyNoetherian Y] [IsNormal Y] in
/-- `Supp (mG) = Supp G` for a divisor `G` and `m ≠ 0`. -/
theorem Divisor.supp_zsmul {G : Divisor Y} {m : ℤ} (hm : m ≠ 0) : (m • G).supp = G.supp := by
  rw [← Divisor.supp_toQDivisor, map_zsmul, QDivisor.supp_zsmul hm, Divisor.supp_toQDivisor]

omit [IsLocallyNoetherian Y] [IsNormal Y] in
/-- If `D` is a divisor with `D = mB` for `m ≠ 0`, then `Supp D = Supp B`. -/
theorem QDivisor.supp_eq_of_toQDivisor_eq {B : QDivisor Y} {D : Divisor Y} {m : ℤ} (hm : m ≠ 0)
    (hD : Divisor.toQDivisor D = m • B) : D.supp = B.supp := by
  rw [← Divisor.supp_toQDivisor, hD, QDivisor.supp_zsmul hm]

/-- Let `f : X ⟶ Y` be a morphism of normal schemes and `B` a `ℚ`-divisor on `Y` such that `f` maps
no generic point of a component of `X` into `Supp B` (condition `(∗)`, `hB`). A `ℚ`-divisor `B'`
on `X` is *the pull-back of `B`*, `B' = f^*B`, if for every integer `m > 0` such that `mB` is a
Cartier divisor `D`, `mB'` is a divisor and is the pull-back of `D`
(`MMP.Mori.Divisor.IsPullback`; `Supp D = Supp B`, so `D` satisfies `(∗)`). -/
@[mmp "def_km0_pullback_q_cartier"]
def QDivisor.IsPullback (B : QDivisor Y)
    (hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ B.supp)
    (B' : QDivisor X) : Prop :=
  ∀ (m : ℕ) (hm : 0 < m) (D : Divisor Y) (hD : Divisor.toQDivisor D = (m : ℤ) • B),
    D.IsCartier → ∃ D' : Divisor X, Divisor.toQDivisor D' = (m : ℤ) • B' ∧
      D.IsPullback f (fun Z hZ => hB Z (by
        rwa [QDivisor.supp_eq_of_toQDivisor_eq (by exact_mod_cast hm.ne') hD] at hZ)) D'

variable {f}

namespace QDivisor

/-- **Existence and uniqueness of the pull-back of a `ℚ`-Cartier `ℚ`-divisor.** With `m_B` the
Cartier index and `F'` the pull-back of the Cartier divisor `m_B B`, `B' = (1/m_B) F'` is the
pull-back; for any other `m` with `mB` Cartier, `m_B(f^*(mB)) = f^*(m_B m B) = m F'`, so
`f^*(mB) = mB'`. It is unique, being determined by `m_B B'`. -/
theorem IsQCartier.existsUnique_isPullback [CompactSpace X] {B : QDivisor Y}
    (hBq : B.IsQCartier)
    (hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ B.supp) :
    ∃! B' : QDivisor X, B.IsPullback f hB B' := by
  set m₀ := B.cartierIndex hBq
  have hm₀ : 0 < m₀ := cartierIndex_pos hBq
  have hm₀' : (m₀ : ℤ) ≠ 0 := by exact_mod_cast hm₀.ne'
  have hm₀q : (m₀ : ℚ) ≠ 0 := by exact_mod_cast hm₀.ne'
  obtain ⟨D₀, hD₀, hD₀c⟩ := isCartierDivisor_cartierIndex_smul hBq
  have hB₀ : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ D₀.supp :=
    fun Z hZ => hB Z (by rwa [supp_eq_of_toQDivisor_eq hm₀' hD₀] at hZ)
  set F := D₀.pullback hD₀c hB₀
  have hF := Divisor.isPullback_pullback (f := f) hD₀c hB₀
  refine ⟨(m₀ : ℚ)⁻¹ • Divisor.toQDivisor F, ?_, ?_⟩
  · intro m hm D hD hDc
    have hm' : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
    have hBD : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ D.supp :=
      fun Z hZ => hB Z (by rwa [supp_eq_of_toQDivisor_eq hm' hD] at hZ)
    refine ⟨D.pullback hDc hBD, ?_, Divisor.isPullback_pullback hDc _⟩
    have key : (m₀ : ℤ) • D = (m : ℤ) • D₀ := by
      apply Divisor.toQDivisor_injective
      rw [map_zsmul, map_zsmul, hD, hD₀, smul_smul, smul_smul, mul_comm]
    have hBD' : ∀ Z : irreducibleComponents X,
        f (componentGenericPoint X Z) ∉ ((m₀ : ℤ) • D).supp := by
      rwa [Divisor.supp_zsmul hm₀']
    have h1 := (Divisor.isPullback_pullback hDc hBD).zsmul hDc (m₀ : ℤ) hBD'
    have h2 := (hF.zsmul hD₀c (m : ℤ) (by rwa [Divisor.supp_zsmul hm'])).of_eq key.symm
      (hB₂ := hBD')
    have h3 : (m₀ : ℤ) • D.pullback hDc hBD = (m : ℤ) • F := h1.eq (hDc.zsmul _) h2
    have h4 := congrArg Divisor.toQDivisor h3
    rw [map_zsmul, map_zsmul, ← Int.cast_smul_eq_zsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ] at h4
    rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul, mul_comm, ← smul_smul, ← h4, smul_smul]
    simp [hm₀q]
  · intro B₁ h₁
    obtain ⟨D₁, hD₁, hp₁⟩ := h₁ m₀ hm₀ D₀ hD₀ hD₀c
    have hD₁F : D₁ = F := hp₁.eq hD₀c hF
    have hq : (m₀ : ℤ) • B₁ = (m₀ : ℤ) • ((m₀ : ℚ)⁻¹ • Divisor.toQDivisor F) := by
      rw [← hD₁, hD₁F, ← Int.cast_smul_eq_zsmul ℚ, smul_smul]
      simp [hm₀q]
    ext E
    have := congrArg (fun G : QDivisor X => G.coeff E) hq
    simp only [DivisorWithCoeffs.coeff_smul, zsmul_eq_mul] at this
    exact mul_left_cancel₀ (by exact_mod_cast hm₀.ne') this

/-- The pull-back `f^*B` of a `ℚ`-Cartier `ℚ`-divisor `B` satisfying `(∗)`, for `X` Noetherian. -/
def pullback [CompactSpace X] (B : QDivisor Y) (hBq : B.IsQCartier)
    (hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ B.supp) : QDivisor X :=
  (hBq.existsUnique_isPullback hB).exists.choose

/-- `QDivisor.pullback f B` is the pull-back of `B`. -/
theorem isPullback_pullback [CompactSpace X] {B : QDivisor Y} (hBq : B.IsQCartier)
    (hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ B.supp) :
    B.IsPullback f hB (B.pullback hBq hB) :=
  (hBq.existsUnique_isPullback hB).exists.choose_spec

/-- Any pull-back of the `ℚ`-Cartier `ℚ`-divisor `B` equals `QDivisor.pullback f B`. -/
theorem IsPullback.pullback_eq [CompactSpace X] {B : QDivisor Y} (hBq : B.IsQCartier)
    {hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ B.supp}
    {B' : QDivisor X} (h : B.IsPullback f hB B') : B.pullback hBq hB = B' :=
  (hBq.existsUnique_isPullback hB).unique (isPullback_pullback hBq hB) h

/-- For a Cartier divisor `B`, the pull-back as a `ℚ`-divisor is the pull-back as a divisor. -/
theorem isPullback_toQDivisor {B : Divisor Y} (hBc : B.IsCartier)
    {hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ B.supp}
    (hBQ : ∀ Z : irreducibleComponents X,
      f (componentGenericPoint X Z) ∉ (Divisor.toQDivisor B).supp)
    {B' : Divisor X} (h : B.IsPullback f hB B') :
    (Divisor.toQDivisor B).IsPullback f hBQ (Divisor.toQDivisor B') := by
  intro m hm D hD hDc
  have hDB : D = (m : ℤ) • B := Divisor.toQDivisor_injective (by rw [hD, map_zsmul])
  exact ⟨(m : ℤ) • B', by rw [map_zsmul], (h.zsmul hBc (m : ℤ) (by
    rwa [Divisor.supp_zsmul (by exact_mod_cast hm.ne')])).of_eq hDB.symm⟩

end QDivisor

end QPullback

end MMP.Mori
