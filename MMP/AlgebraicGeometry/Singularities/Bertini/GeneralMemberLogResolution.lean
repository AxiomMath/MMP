module

public import MMP.AlgebraicGeometry.Singularities.Bertini.GeneralMemberSNC
public import MMP.AlgebraicGeometry.Intersection.CartierRestriction
public import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
public import MMP.AlgebraicGeometry.Morphisms.Birational.BiregularLocusCodimOnePoints

/-!
# The log resolution induced on a general member of a free linear system

Let `(X, Δ = ∑ aⱼ Dⱼ)` be a pair over an algebraically closed field `k` of characteristic zero
with `dim X ≥ 2`, `|V|` a free linear system on `X` spanned by sections `sᵢ` of `𝒪_X(H)`, and
`f : X' ⟶ X` a log resolution of `(X, Δ)` with `f`-exceptional prime divisors `E₁, …, E_s` such
that `∑ⱼ f⁻¹_* Dⱼ` is smooth. For a general member `H_g` of `|V|` and a connected component `H⁰`
of `H_g`, the restriction `f⁰ : H'⁰ = f⁻¹(H⁰) ⟶ H⁰` is a log resolution of `(H⁰, Δ|_{H⁰})`,
its exceptional prime divisors are exactly the irreducible components of the `Eᵢ ∩ H'⁰`, and
`∑ⱼ (f⁰)⁻¹_*(Dⱼ|_{H⁰})` is smooth.

## Proof

A general member `H_g = (σ)₀` of the free system is chosen by
`MMP.Mori.IsLogResolution.exists_polynomial_isSNC_pullback_zeroDivisor_add`: its pull-back
`H' = f^*H_g` has disjoint components and `H' + B` is a reduced snc divisor, `B` the sum of the
components of `f⁻¹_*Δ` and of the `f`-exceptional prime divisors. For a connected component
`H⁰ = Z` of `Supp H_g` with its reduced structure, the base change `f⁰ : W = Y ×_X H⁰ ⟶ H⁰` is
then a log resolution of `(H⁰, Δ|_{H⁰})`.

The member `H_g` is Cartier, the free system giving local equations `φ`. At a point `y` of
`f⁻¹(H⁰)` the pulled-back germ of `φ` has order one along the component `E` of `H'` through `y`
and order zero along the other prime divisors through `y`, so in the factorial ring `𝒪_{Y,y}` it
generates the ideal of `E`; since the ideal of `H⁰` lies between `(φ)` and its radical, `W` is cut
out near `y` by one member of a regular system of parameters, hence is smooth, and the snc
coordinates of `H' + B` at `y` give coordinates on `W` in which the preimages of the components
of `B` are coordinate hyperplanes. The morphism `f⁰` is an isomorphism exactly over the preimage
of the biregular locus of `f`: by Zariski's main theorem the fibres of `f` over the other points
of the normal `X` are positive dimensional. So `Ex(f⁰) = Ex(f) ∩ W`, whose components are the
components of the `E_i ∩ W`; such a component `F` maps to a point of codimension at least three
of `X` lying on `H⁰`, which has codimension at least two in `H⁰` by Krull's principal ideal
theorem, so `F` is `f⁰`-exceptional. The components of `f⁻¹_*D_j ∩ W` meeting the isomorphism
locus are the birational transforms of the components of `D_j ∩ H⁰`, and they are disjoint
because the components of `f⁻¹_*Δ` are.

## Main results

* `MMP.Mori.IsLogResolution.exists_polynomial_isLogResolution_restrict_connectedComponent`

## Implementation notes

"General" is expressed by a nonzero polynomial `Q` in the coefficients `c` of the member
`σ = ∑ cᵢ sᵢ`: the conclusion holds for every `c` with `Q(c) ≠ 0`. The connected component `H⁰`
carries its reduced structure (a general member is normal, so this is the scheme-theoretic one),
and `H'⁰` is the scheme-theoretic preimage `X' ×_X H⁰`.

The base change is `pullback f ι_Z`, which is isomorphic to the closed subscheme of `Y` cut out by
the inverse image of the reduced ideal of `Z`
(`AlgebraicGeometry.Scheme.IdealSheafData.comapIso`); its local rings are the quotients of those
of `Y`. The connected components of the preimage of a component of `B` are irreducible and are the
supports of prime divisors (`MMP.Mori.exists_primeDivisor_support_eq_connectedComponentIn`).

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KM98], proof of Lemma 5.17
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Mori

/-- A germ `a` at `x` of a local equation of `D` lies in the prime of every generization of `x` on
`Supp D`. -/
private theorem mem_primeOfSpecializes_of_mem_supp {X : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X]
    {D : Divisor X} {U : X.Opens} {φ : (RationalFunctions X)ˣ} (hφ : D.IsLocalEquation U φ)
    {x : X} (hxU : x ∈ U) {W : irreducibleComponents X} (hxW : x ∈ W.1)
    {a : X.presheaf.stalk x}
    (ha : (stalkToRationalFunctions X hxW).hom a = (φ : RationalFunctions X) W)
    {x' : X} (h : x' ⤳ x) (hx' : x' ∈ D.supp) :
    a ∈ MMP.Intersection.primeOfSpecializes h := by
  obtain ⟨C, hC, hx'C⟩ := DivisorWithCoeffs.mem_supp_iff.mp hx'
  have hηC : C.genericPoint ⤳ x' := by
    rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact hx'C
  have hxC : x ∈ C.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← specializes_iff_mem_closure]
    exact hηC.trans h
  have hord : C.ord φ ≠ 0 := by
    rwa [← hφ C ⟨x', hx'C, h.mem_open U.isOpen hxU⟩]
  have hW : W = C.component :=
    eq_of_mem_irreducibleComponents hxW (C.support_subset_component hxC)
  subst hW
  refine MMP.Resolution.primeOfSpecializes_trans_le hηC h ?_
  change X.presheaf.stalkSpecializes (hηC.trans h) a ∈ IsLocalRing.maximalIdeal _
  by_contra hna
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hna
  apply hord
  refine C.ord_eq_zero_of_isUnit hna ?_
  rw [C.toComponent_stalkSpecializes (hηC.trans h) hxW]
  exact ha

/-- On the discrete valuation ring `𝒪_{X,D}`, the order `v_D` of the image of `c ≠ 0` is its length
order. -/
private theorem ordUnit_eq_ord {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    (D : PrimeDivisor X)
    {c : D.localRing} (hc : c ≠ 0)
    {u : (X.presheaf.stalk (componentGenericPoint X D.component))ˣ}
    (hu : D.toComponent.hom c = u) : D.ordUnit u = ((Ring.ord D.localRing c).toNat : ℤ) := by
  let := D.toComponent.hom.toAlgebra
  have := isFractionRing_stalkToRationalFunctions D.genericPoint_mem_component
  have : Ring.KrullDimLE 1 D.localRing := krullDimLE_of_coheight_le D.coheight_genericPoint.le
  have := D.isDiscreteValuationRing_localRing
  have hnz : c ∈ nonZeroDivisors D.localRing := mem_nonZeroDivisors_of_ne_zero hc
  have hfin : Ring.ord D.localRing c ≠ ⊤ := Ring.ord_ne_top hnz
  have h := D.valuation_eq_exp_ordUnit u
  have h2 : D.valuation (D.toComponent.hom c) =
      WithZero.exp ((Ring.ord D.localRing c).toNat : ℤ) := by
    change Ring.ordFrac D.localRing (IsLocalization.algEquiv (nonZeroDivisors D.localRing) _
      (FractionRing D.localRing) (algebraMap D.localRing _ c)) = _
    rw [AlgEquiv.commutes, Ring.ordFrac_eq_ord _ hc,
      Ring.ordMonoidWithZeroHom_eq_coe _ hnz (ENat.coe_toNat hfin).symm]
    rfl
  rw [hu, h] at h2
  exact WithZero.exp_injective h2

/-- The coefficient of the pull-back `f^*D` at a prime divisor `E` through `y` is the order along
`E` of the pulled-back germ of a local equation of `D`. -/
private theorem coeff_eq_ord_stalkMap {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y] {f : Y ⟶ X} {D : Divisor X}
    {hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ D.supp}
    {H' : Divisor Y} (hpb : D.IsPullback f hB H') {U : X.Opens} {φ : (RationalFunctions X)ˣ}
    (hφ : D.IsLocalEquation U φ) {y : Y} (hyU : f y ∈ U) {W : irreducibleComponents X}
    (hW : f y ∈ W.1) {a : X.presheaf.stalk (f y)}
    (ha : (stalkToRationalFunctions X hW).hom a = (φ : RationalFunctions X) W)
    {y'' : Y} (h : y'' ⤳ y) (h1 : Order.coheight y'' = 1) :
    Y.presheaf.stalkSpecializes h (f.stalkMap y a) ≠ 0 ∧
    H'.coeff (AlgebraicGeometry.PrimeDivisor.ofCoheightOne y'' h1) =
      ((Ring.ord (Y.presheaf.stalk y'') (Y.presheaf.stalkSpecializes h (f.stalkMap y a))).toNat
        : ℤ) := by
  set E : PrimeDivisor Y := AlgebraicGeometry.PrimeDivisor.ofCoheightOne y'' h1 with hEdef
  have hEg : AlgebraicGeometry.PrimeDivisor.genericPoint E = y'' :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne y'' h1
  have hηy : AlgebraicGeometry.PrimeDivisor.genericPoint E ⤳ y := by rwa [hEg]
  have hyE : y ∈ E.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← specializes_iff_mem_closure]
    exact hηy
  have hE : (E.support ∩ f ⁻¹ᵁ U).Nonempty := ⟨y, hyE, hyU⟩
  have hc := hpb U φ hφ E hE
  set Z := E.component
  set cgp := componentGenericPoint Y Z
  have hZ : f cgp ∈ U := E.map_componentGenericPoint_mem f hE
  have hcgpy : cgp ⤳ y := E.specializes_genericPoint.trans hηy
  have hx0 : f cgp ⤳ f y := f.base.hom.map_specializes hcgpy
  set W' := pointComponent (f cgp)
  have hfyW' : f y ∈ W'.1 := hx0.mem_closed (isClosed_of_mem_irreducibleComponents _ W'.2)
    (mem_pointComponent _)
  have hWW' : W' = W := eq_of_mem_irreducibleComponents hfyW' hW
  have hx0W : f cgp ∈ W.1 := hWW' ▸ mem_pointComponent _
  obtain ⟨a1, ha1⟩ := hφ.exists_unit_stalk hZ (hB Z) hx0W
  have ha0 : X.presheaf.stalkSpecializes hx0 a = (a1 : X.presheaf.stalk (f cgp)) := by
    apply stalkToRationalFunctions_injective hx0W
    rw [ha1, ← ha]
    change (X.presheaf.stalkSpecializes hx0 ≫ X.presheaf.stalkSpecializes _).hom a = _
    rw [TopCat.Presheaf.stalkSpecializes_comp]
    rfl
  rw [pullbackComponent_eq hB hφ hZ hx0W a1 ha1] at hc
  have hcu : E.toComponent.hom (Y.presheaf.stalkSpecializes hηy (f.stalkMap y a)) =
      ((Units.map (f.stalkMap cgp).hom.toMonoidHom a1 : (Y.presheaf.stalk cgp)ˣ) :
        Y.presheaf.stalk cgp) := by
    change (Y.presheaf.stalkSpecializes _ ≫ Y.presheaf.stalkSpecializes _).hom
      (f.stalkMap y a) = _
    rw [TopCat.Presheaf.stalkSpecializes_comp]
    rw [Units.coe_map, ← ha0]
    exact (Scheme.Hom.stalkSpecializes_stalkMap_apply f cgp y hcgpy a).symm
  have hne : Y.presheaf.stalkSpecializes hηy (f.stalkMap y a) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hcu
    exact (Units.ne_zero _) hcu.symm
  rw [hc, ordUnit_eq_ord E hne hcu]
  clear_value E
  subst hEg
  exact ⟨hne, rfl⟩

/-- A local equation of an effective divisor on a normal scheme is regular at each point of its
open. -/
private theorem exists_germ_eq_of_isLocalEquation {X : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X]
    {D : Divisor X} (hD : 0 ≤ D) {U : X.Opens} {φ : (RationalFunctions X)ˣ}
    (hφ : D.IsLocalEquation U φ) {x : X} (hxU : x ∈ U) :
    ∃ a : X.presheaf.stalk x, (stalkToRationalFunctions X (mem_pointComponent x)).hom a =
      (φ : RationalFunctions X) (pointComponent x) :=
  exists_stalk_eq_of_forall_zero_le_ord _ φ fun E hE => by
    rw [← hφ E ⟨x, hE, hxU⟩]
    exact hD E

/-- Off `Supp D`, the germ of a local equation of `D` is a unit. -/
private theorem isUnit_of_isLocalEquation_of_notMem_supp {X : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] {D : Divisor X} {U : X.Opens} {φ : (RationalFunctions X)ˣ}
    (hφ : D.IsLocalEquation U φ) {x : X} (hxU : x ∈ U) {W : irreducibleComponents X}
    (hxW : x ∈ W.1) {a : X.presheaf.stalk x}
    (ha : (stalkToRationalFunctions X hxW).hom a = (φ : RationalFunctions X) W)
    (hx : x ∉ D.supp) : IsUnit a := by
  obtain ⟨a1, ha1⟩ := hφ.exists_unit_stalk hxU hx hxW
  rw [stalkToRationalFunctions_injective hxW (ha.trans ha1.symm)]
  exact a1.isUnit

/-- On `Supp D`, the germ of a local equation of `D` is not a unit. -/
private theorem not_isUnit_of_isLocalEquation_of_mem_supp {X : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] {D : Divisor X} {U : X.Opens} {φ : (RationalFunctions X)ˣ}
    (hφ : D.IsLocalEquation U φ) {x : X} (hxU : x ∈ U) {W : irreducibleComponents X}
    (hxW : x ∈ W.1) {a : X.presheaf.stalk x}
    (ha : (stalkToRationalFunctions X hxW).hom a = (φ : RationalFunctions X) W)
    (hx : x ∈ D.supp) : ¬ IsUnit a := by
  have h := mem_primeOfSpecializes_of_mem_supp hφ hxU hxW ha (specializes_refl x) hx
  change X.presheaf.stalkSpecializes (specializes_refl x) a ∈ IsLocalRing.maximalIdeal _ at h
  rw [TopCat.Presheaf.stalkSpecializes_refl] at h
  exact (IsLocalRing.mem_maximalIdeal _).mp h

/-- The pull-back to an integral `Y` of the germ of a local equation is nonzero. -/
private theorem stalkMap_ne_zero_of_isLocalEquation {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral Y] {f : Y ⟶ X} {D : Divisor X}
    (hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ D.supp)
    {U : X.Opens} {φ : (RationalFunctions X)ˣ}
    (hφ : D.IsLocalEquation U φ) {y : Y} (hyU : f y ∈ U) {W : irreducibleComponents X}
    (hW : f y ∈ W.1) {a : X.presheaf.stalk (f y)}
    (ha : (stalkToRationalFunctions X hW).hom a = (φ : RationalFunctions X) W) :
    f.stalkMap y a ≠ 0 := by
  set Z := pointComponent y
  set cgp := componentGenericPoint Y Z
  have hcgpy : cgp ⤳ y := (isGenericPoint_componentGenericPoint Y Z).specializes
    (mem_pointComponent y)
  have hx0 : f cgp ⤳ f y := f.base.hom.map_specializes hcgpy
  have hZ : f cgp ∈ U := hx0.mem_open U.isOpen hyU
  set W' := pointComponent (f cgp)
  have hfyW' : f y ∈ W'.1 := hx0.mem_closed (isClosed_of_mem_irreducibleComponents _ W'.2)
    (mem_pointComponent _)
  have hWW' : W' = W := eq_of_mem_irreducibleComponents hfyW' hW
  have hx0W : f cgp ∈ W.1 := hWW' ▸ mem_pointComponent _
  have hu : IsUnit (X.presheaf.stalkSpecializes hx0 a) := by
    refine isUnit_of_isLocalEquation_of_notMem_supp hφ hZ hx0W ?_ (hB Z)
    rw [← ha]
    change (X.presheaf.stalkSpecializes hx0 ≫ X.presheaf.stalkSpecializes _).hom a = _
    rw [TopCat.Presheaf.stalkSpecializes_comp]
    rfl
  intro h0
  have h1 := Scheme.Hom.stalkSpecializes_stalkMap_apply f cgp y hcgpy a
  rw [h0, map_zero] at h1
  exact (hu.map (f.stalkMap cgp).hom).ne_zero h1

/-- At a generic point of an integral scheme every nonzero germ is a unit. -/
private theorem isUnit_of_coheight_eq_zero {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    {y : Y} (h0 : Order.coheight y = 0) {c : Y.presheaf.stalk y} (hc : c ≠ 0) : IsUnit c := by
  have : Ring.KrullDimLE 0 (Y.presheaf.stalk y) := krullDimLE_of_coheight_le (by rw [h0]; rfl)
  have : IsArtinianRing (Y.presheaf.stalk y) := isArtinianRing_iff_krullDimLE_zero.2 this
  exact IsArtinianRing.isUnit_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hc)

/-- Set-theoretically, `Supp f^*D = f⁻¹(Supp D)` for an effective Cartier divisor `D` and a
factorial `Y`. -/
private theorem mem_supp_iff_mem_supp_of_isPullback {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y]
    (hUFD : ∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)) {f : Y ⟶ X}
    {D : Divisor X} (hD : 0 ≤ D) (hDc : D.IsCartier)
    {hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ D.supp}
    {H' : Divisor Y} (hpb : D.IsPullback f hB H') (y : Y) :
    f y ∈ D.supp ↔ y ∈ H'.supp := by
  obtain ⟨U, hxU, φ, hφ⟩ := hDc (f y)
  obtain ⟨a, ha⟩ := exists_germ_eq_of_isLocalEquation hD hφ hxU
  have hb0 := stalkMap_ne_zero_of_isLocalEquation hB hφ hxU _ ha
  constructor
  · intro hx
    have hna := not_isUnit_of_isLocalEquation_of_mem_supp hφ hxU _ ha hx
    have hnb : ¬ IsUnit (f.stalkMap y a) := fun hu =>
      hna ((isUnit_map_iff (f.stalkMap y).hom a).mp hu)
    by_contra hy
    apply hnb
    have := hUFD y
    have hass : Associated (f.stalkMap y a) 1 := by
      refine MMP.Intersection.associated_of_forall_ord_stalkSpecializes_eq y hb0 one_ne_zero
        fun y'' h hle => ?_
      rw [map_one, Ring.ord_one]
      have hne : Y.presheaf.stalkSpecializes h (f.stalkMap y a) ≠ 0 := fun h0 =>
        hb0 (MMP.Intersection.stalkSpecializes_injective h (h0.trans (map_zero _).symm))
      rcases ENat.le_one_iff_eq_zero_or_eq_one.mp hle with h0 | h1
      · exact Ring.ord_of_isUnit (isUnit_of_coheight_eq_zero h0 hne)
      · obtain ⟨-, hc⟩ := coeff_eq_ord_stalkMap hpb hφ hxU _ ha h h1
        have hyE : y ∈ (AlgebraicGeometry.PrimeDivisor.ofCoheightOne y'' h1).support := by
          rwa [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
            AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne,
            ← specializes_iff_mem_closure]
        have hc0 : H'.coeff (AlgebraicGeometry.PrimeDivisor.ofCoheightOne y'' h1) = 0 := by
          by_contra hne'
          exact hy (DivisorWithCoeffs.mem_supp_iff.mpr ⟨_, hne', hyE⟩)
        rw [hc0] at hc
        have hfin : Ring.ord (Y.presheaf.stalk y'')
            (Y.presheaf.stalkSpecializes h (f.stalkMap y a)) ≠ ⊤ := by
          have : Ring.KrullDimLE 1 (Y.presheaf.stalk y'') :=
            krullDimLE_of_coheight_le (by rw [h1]; rfl)
          exact Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hne)
        have h0' : (Ring.ord (Y.presheaf.stalk y'')
            (Y.presheaf.stalkSpecializes h (f.stalkMap y a))).toNat = 0 := by exact_mod_cast hc.symm
        rw [← ENat.coe_toNat hfin, h0']
        rfl
    exact hass.isUnit_iff.mpr isUnit_one
  · intro hy
    obtain ⟨E, hE, hyE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hy
    by_contra hx
    have hau := isUnit_of_isLocalEquation_of_notMem_supp hφ hxU _ ha hx
    have hη : AlgebraicGeometry.PrimeDivisor.genericPoint E ⤳ y := by
      rwa [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    have h1 := AlgebraicGeometry.PrimeDivisor.coheight_genericPoint E
    obtain ⟨-, hc⟩ := coeff_eq_ord_stalkMap hpb hφ hxU _ ha hη h1
    have hEq : AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ h1 = E :=
      ((MMP.Mori.PrimeDivisor.eq_ofCoheightOne_iff E h1).mpr rfl).symm
    rw [hEq, Ring.ord_of_isUnit ((hau.map (f.stalkMap y).hom).map _)] at hc
    exact hE hc

/-- Where `f^*D` is the prime divisor `E` with multiplicity one, the pulled-back local equation
generates the ideal of `E`. -/
private theorem associated_stalkMap_of_isPullback {k : Type u} [Field k] {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y]
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] (hsmY : IsSmoothScheme sY)
    (hUFD : ∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)) {f : Y ⟶ X}
    {D : Divisor X}
    {hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ D.supp}
    {H' : Divisor Y} (hpb : D.IsPullback f hB H') {U : X.Opens} {φ : (RationalFunctions X)ˣ}
    (hφ : D.IsLocalEquation U φ) {y : Y} (hyU : f y ∈ U) {W : irreducibleComponents X}
    (hW : f y ∈ W.1) {a : X.presheaf.stalk (f y)}
    (ha : (stalkToRationalFunctions X hW).hom a = (φ : RationalFunctions X) W)
    {E : PrimeDivisor Y} (hyE : y ∈ E.support) (hE1 : H'.coeff E = 1)
    (hE0 : ∀ E' : PrimeDivisor Y, y ∈ E'.support → E' ≠ E → H'.coeff E' = 0)
    {π : Y.presheaf.stalk y} (hπ : IdealSheafData.stalk E.idealSheaf y = Ideal.span {π})
    (hπ0 : π ≠ 0) : Associated (f.stalkMap y a) π := by
  have hb0 := stalkMap_ne_zero_of_isLocalEquation hB hφ hyU hW ha
  have := hUFD y
  have hprime := MMP.Resolution.Aux.primeOfSpecializes_genericPoint sY hsmY E hyE
  have hηE := MMP.Resolution.Aux.genericPoint_specializes_of_mem_support E hyE
  refine MMP.Intersection.associated_of_forall_ord_stalkSpecializes_eq y hb0 hπ0
    fun y'' h hle => ?_
  have hne : Y.presheaf.stalkSpecializes h (f.stalkMap y a) ≠ 0 := fun h0 =>
    hb0 (MMP.Intersection.stalkSpecializes_injective h (h0.trans (map_zero _).symm))
  have hneπ : Y.presheaf.stalkSpecializes h π ≠ 0 := fun h0 =>
    hπ0 (MMP.Intersection.stalkSpecializes_injective h (h0.trans (map_zero _).symm))
  rcases ENat.le_one_iff_eq_zero_or_eq_one.mp hle with h0 | h1
  · rw [Ring.ord_of_isUnit (isUnit_of_coheight_eq_zero h0 hne),
      Ring.ord_of_isUnit (isUnit_of_coheight_eq_zero h0 hneπ)]
  · obtain ⟨-, hc⟩ := coeff_eq_ord_stalkMap hpb hφ hyU hW ha h h1
    have : Ring.KrullDimLE 1 (Y.presheaf.stalk y'') :=
      krullDimLE_of_coheight_le (by rw [h1]; rfl)
    have hfin : Ring.ord (Y.presheaf.stalk y'')
        (Y.presheaf.stalkSpecializes h (f.stalkMap y a)) ≠ ⊤ :=
      Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hne)
    rw [← ENat.coe_toNat hfin]
    by_cases hyη : y'' = AlgebraicGeometry.PrimeDivisor.genericPoint E
    · have hEq : AlgebraicGeometry.PrimeDivisor.ofCoheightOne y'' h1 = E :=
        ((MMP.Mori.PrimeDivisor.eq_ofCoheightOne_iff E h1).mpr hyη).symm
      rw [hEq, hE1] at hc
      have h1' : (Ring.ord (Y.presheaf.stalk y'')
          (Y.presheaf.stalkSpecializes h (f.stalkMap y a))).toNat = 1 := by exact_mod_cast hc.symm
      rw [h1']
      refine (MMP.Intersection.ord_stalkSpecializes_eq_one h ?_).symm
      rw [MMP.Resolution.primeOfSpecializes_congr hyη h hηE, hprime, hπ]
    · have hyE' : y ∈ (AlgebraicGeometry.PrimeDivisor.ofCoheightOne y'' h1).support := by
        rwa [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
          AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne,
          ← specializes_iff_mem_closure]
      have hEne : AlgebraicGeometry.PrimeDivisor.ofCoheightOne y'' h1 ≠ E := fun hEq =>
        hyη ((MMP.Mori.PrimeDivisor.eq_ofCoheightOne_iff E h1).mp hEq.symm)
      rw [hE0 _ hyE' hEne] at hc
      have h0' : (Ring.ord (Y.presheaf.stalk y'')
          (Y.presheaf.stalkSpecializes h (f.stalkMap y a))).toNat = 0 := by exact_mod_cast hc.symm
      rw [h0']
      refine (MMP.Intersection.ord_stalkSpecializes_of_notMem h fun hπy => hyη ?_).symm
      have hle' : MMP.Intersection.primeOfSpecializes hηE ≤
          MMP.Intersection.primeOfSpecializes h := by
        rwa [hprime, hπ, Ideal.span_singleton_le_iff_mem]
      have hsp : AlgebraicGeometry.PrimeDivisor.genericPoint E ⤳ y'' :=
        MMP.Intersection.specializes_of_primeOfSpecializes_le hηE h hle'
      by_contra hne'
      have hlt := Order.coheight_strictAnti (MMP.Intersection.lt_of_specializes_of_ne hsp hne')
      rw [h1, AlgebraicGeometry.PrimeDivisor.coheight_genericPoint] at hlt
      exact lt_irrefl _ (hlt (by decide))

/-- The germ of a local equation of `D` vanishes on every closed set contained in `Supp D`. -/
private theorem germ_mem_stalk_vanishingIdeal {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    {D : Divisor X} {U : X.Opens} {φ : (RationalFunctions X)ˣ} (hφ : D.IsLocalEquation U φ)
    {x : X} (hxU : x ∈ U) {W : irreducibleComponents X} (hxW : x ∈ W.1)
    {a : X.presheaf.stalk x}
    (ha : (stalkToRationalFunctions X hxW).hom a = (φ : RationalFunctions X) W)
    {Z : Closeds X} (hZ : (Z : Set X) ⊆ D.supp) :
    a ∈ IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal Z) x := by
  rw [MMP.Resolution.stalk_vanishingIdeal_eq, PrimeSpectrum.mem_vanishingIdeal]
  intro p hp
  have h := MMP.Intersection.fromSpecStalk_specializes x p
  rw [← MMP.Intersection.comap_maximalIdeal_stalkSpecializes_fromSpecStalk x p]
  exact mem_primeOfSpecializes_of_mem_supp hφ hxU hxW ha h (hZ hp)

/-- Over a connected component `Z` of `Supp D`, the inverse image of the reduced ideal of `Z` is,
at each point, the ideal of the component of `f^*D` through it. -/
private theorem exists_stalk_comap_vanishingIdeal_eq {k : Type u} [Field k] {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y]
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] (hsmY : IsSmoothScheme sY)
    (hUFD : ∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)) {f : Y ⟶ X}
    {D : Divisor X} (hD : 0 ≤ D) (hDc : D.IsCartier)
    {hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ D.supp}
    {H' : Divisor Y} (hpb : D.IsPullback f hB H')
    (hH'1 : ∀ E ∈ H'.support, H'.coeff E = 1)
    (hdisj : ∀ E ∈ H'.support, ∀ E' ∈ H'.support, E ≠ E' → Disjoint E.support E'.support)
    (hgen : ∀ E ∈ H'.support, ∀ y ∈ E.support, ∃ π : Y.presheaf.stalk y, π ≠ 0 ∧
      IdealSheafData.stalk E.idealSheaf y = Ideal.span {π})
    {Z : Closeds X} {x₀ : X} (hZ : connectedComponentIn (D.supp : Set X) x₀ = Z)
    {y : Y} (hy : f y ∈ Z) :
    ∃ E ∈ H'.support, y ∈ E.support ∧ E.support ⊆ f ⁻¹' Z ∧
      IdealSheafData.stalk ((Scheme.IdealSheafData.vanishingIdeal Z).comap f) y =
        IdealSheafData.stalk E.idealSheaf y := by
  classical
  have hZD : (Z : Set X) ⊆ D.supp := hZ ▸ connectedComponentIn_subset _ _
  have hK1 := mem_supp_iff_mem_supp_of_isPullback hUFD hD hDc hpb
  obtain ⟨E, hE, hyE⟩ := DivisorWithCoeffs.mem_supp_iff.mp ((hK1 y).mp (hZD hy))
  have hEs : E ∈ H'.support := Finsupp.mem_support_iff.mpr hE
  have hEZ : E.support ⊆ f ⁻¹' Z := by
    have hirr : _root_.IsPreconnected (f '' E.support) := by
      have : IsIrreducible E.support := by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact isIrreducible_singleton.closure
      have h2 : IsIrreducible (f '' E.support) := this.image _ f.continuous.continuousOn
      exact (IsIrreducible.isConnected h2).isPreconnected
    have hsub : f '' E.support ⊆ D.supp := by
      rintro _ ⟨y', hy', rfl⟩
      exact (hK1 y').mpr (DivisorWithCoeffs.mem_supp_iff.mpr ⟨E, hE, hy'⟩)
    have hcc : connectedComponentIn (D.supp : Set X) (f y) = Z := by
      rw [← hZ]
      exact (connectedComponentIn_eq (hZ ▸ hy)).symm
    intro y' hy'
    have := hirr.subset_connectedComponentIn ⟨y, hyE, rfl⟩ hsub ⟨y', hy', rfl⟩
    rwa [hcc] at this
  refine ⟨E, hEs, hyE, hEZ, le_antisymm ?_ ?_⟩
  · -- upper bound: through the radical
    refine (MMP.Resolution.stalk_le_stalk_of_le
      (Scheme.IdealSheafData.le_radical _) y).trans (le_of_eq ?_)
    rw [← Scheme.IdealSheafData.vanishingIdeal_support,
      ← MMP.Intersection.vanishingIdeal_support_idealSheaf]
    set T : Closeds Y := ⟨⋃ E' ∈ H'.support.erase E, E'.support,
      (H'.support.erase E).finite_toSet.isClosed_biUnion fun E' _ => E'.idealSheaf.support.isClosed⟩
    have hT : ∀ y', y' ∈ (T : Set Y) ↔ ∃ E' ∈ H'.support, E' ≠ E ∧ y' ∈ E'.support := by
      intro y'
      simp only [T, Closeds.coe_mk, Set.mem_iUnion, Finset.mem_erase, exists_prop]
      exact ⟨fun ⟨E', ⟨h1, h2⟩, h3⟩ => ⟨E', h2, h1, h3⟩, fun ⟨E', h2, h1, h3⟩ => ⟨E', ⟨h1, h2⟩, h3⟩⟩
    have hyT : y ∉ (T : Set Y) := by
      rw [hT]
      rintro ⟨E', hE', hne, hyE'⟩
      exact Set.disjoint_left.mp (hdisj E hEs E' hE' hne.symm) hyE hyE'
    refine MMP.Mori.stalk_vanishingIdeal_eq_of_inter_eq _ _
      (U := ⟨(T : Set Y)ᶜ, T.isClosed.isOpen_compl⟩) hyT ?_
    ext y'
    simp only [Scheme.IdealSheafData.support_comap,
      Scheme.IdealSheafData.coe_support_vanishingIdeal,
      Set.mem_inter_iff, Opens.coe_mk, Set.mem_compl_iff]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      obtain ⟨E', hE', hy'E'⟩ := DivisorWithCoeffs.mem_supp_iff.mp ((hK1 y').mp (hZD h1))
      rcases eq_or_ne E' E with rfl | hEE
      · exact hy'E'
      · exact absurd ((hT y').mpr ⟨E', Finsupp.mem_support_iff.mpr hE', hEE, hy'E'⟩) h2
    · rintro ⟨h1, h2⟩
      exact ⟨hEZ h1, h2⟩
  · -- lower bound: the pulled back local equation generates
    obtain ⟨U, hxU, φ, hφ⟩ := hDc (f y)
    obtain ⟨a, ha⟩ := exists_germ_eq_of_isLocalEquation hD hφ hxU
    obtain ⟨π, hπ0, hπ⟩ := hgen E hEs y hyE
    have hass := associated_stalkMap_of_isPullback sY hsmY hUFD hpb hφ hxU _ ha hyE
      (hH'1 E hEs) (fun E' hyE' hne => by
        by_contra hc
        exact Set.disjoint_left.mp (hdisj E hEs E' (Finsupp.mem_support_iff.mpr hc)
          (Ne.symm hne)) hyE hyE') hπ hπ0
    rw [hπ, ← Ideal.span_singleton_eq_span_singleton.mpr hass, Ideal.span_le,
      Set.singleton_subset_iff, AlgebraicGeometry.IdealSheafData.stalk_comap]
    exact Ideal.mem_map_of_mem _
      (germ_mem_stalk_vanishingIdeal hφ hxU _ ha hZD)

/-- The pull-back of an effective Cartier divisor is effective. -/
private theorem coeff_nonneg_of_isPullback {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] {f : Y ⟶ X}
    {D : Divisor X} (hD : 0 ≤ D) (hDc : D.IsCartier)
    {hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ D.supp}
    {H' : Divisor Y} (hpb : D.IsPullback f hB H') (E : PrimeDivisor Y) : 0 ≤ H'.coeff E := by
  obtain ⟨U, hxU, φ, hφ⟩ := hDc (f (AlgebraicGeometry.PrimeDivisor.genericPoint E))
  obtain ⟨a, ha⟩ := exists_germ_eq_of_isLocalEquation hD hφ hxU
  have h1 := AlgebraicGeometry.PrimeDivisor.coheight_genericPoint E
  obtain ⟨-, hc⟩ := coeff_eq_ord_stalkMap hpb hφ hxU _ ha (specializes_refl _) h1
  have hEq : AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ h1 = E :=
    ((MMP.Mori.PrimeDivisor.eq_ofCoheightOne_iff E h1).mpr rfl).symm
  rw [hEq] at hc
  rw [hc]
  exact Nat.cast_nonneg _

open Classical in
private theorem coeff_sum_single {Y : Scheme.{u}} (S : Finset (PrimeDivisor Y))
    (E : PrimeDivisor Y) :
    DivisorWithCoeffs.coeff (∑ F ∈ S, Finsupp.single F (1 : ℤ) : Divisor Y) E =
      if E ∈ S then 1 else 0 := by
  change (∑ F ∈ S, Finsupp.single F (1 : ℤ)) E = _
  rw [Finsupp.finsetSum_apply]
  simp [Finsupp.single_apply]

open Classical in
/-- If `H' + ∑_{F ∈ S} F` is reduced, each component of `H'` has coefficient one and is not in
`S`. -/
private theorem coeff_eq_one_and_notMem_of_mem_support {Y : Scheme.{u}} {H' : Divisor Y}
    (hH' : ∀ E, 0 ≤ H'.coeff E) (S : Finset (PrimeDivisor Y))
    (h01 : ∀ F : PrimeDivisor Y,
      (H' + ∑ F ∈ S, Finsupp.single F (1 : ℤ)).coeff F = 0 ∨
      (H' + ∑ F ∈ S, Finsupp.single F (1 : ℤ)).coeff F = 1)
    {E : PrimeDivisor Y} (hE : E ∈ H'.support) : H'.coeff E = 1 ∧ E ∉ S := by
  have hpos : H'.coeff E ≠ 0 := Finsupp.mem_support_iff.mp hE
  have hnn := hH' E
  have h' := h01 E
  rw [DivisorWithCoeffs.coeff_add, coeff_sum_single] at h'
  by_cases hS : E ∈ S
  · rw [if_pos hS] at h'
    exfalso
    rcases h' with h | h <;> omega
  · rw [if_neg hS] at h'
    refine ⟨?_, hS⟩
    rcases h' with h | h <;> omega

/-- Each component of an snc divisor is cut out at each of its points by a member of a regular
system of parameters. -/
private theorem exists_isRegularSystemOfParameters_of_isSNC {R : Type*} [Zero R] {Y T : Scheme.{u}}
    [IsLocallyNoetherian Y] {s : Y ⟶ T} {D : DivisorWithCoeffs R Y} (hD : D.IsSNC s)
    {E : PrimeDivisor Y} (hE : E ∈ D.support) {y : Y} (hy : y ∈ E.support) :
    ∃ (n : ℕ) (z : Fin n → Y.presheaf.stalk y) (m : Fin n),
      IsRegularSystemOfParameters z ∧ IdealSheafData.stalk E.idealSheaf y = Ideal.span {z m} := by
  obtain ⟨n, z, j, hz, -, hI⟩ := hD.2 y
  exact ⟨n, z, j ⟨E, hE, hy⟩, hz, hI ⟨E, hE, hy⟩⟩

/-- Distinct components of an snc divisor whose union is smooth are disjoint. -/
private theorem disjoint_of_isSmoothScheme_iInf {k : Type u} [Field k] {R : Type*} [Zero R]
    {Y : Scheme.{u}} [IsLocallyNoetherian Y] (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY]
    {D : DivisorWithCoeffs R Y} (hD : D.IsSNC sY) {T : Finset (PrimeDivisor Y)}
    (hT : T ⊆ D.support)
    (hsm : IsSmoothScheme ((⨅ F ∈ T, F.idealSheaf).subschemeι ≫ sY)) :
    ∀ F ∈ T, ∀ F' ∈ T, F ≠ F' → Disjoint F.support F'.support := by
  classical
  intro F hF F' hF' hne
  rw [Set.disjoint_left]
  intro y hyF hyF'
  set K : Y.IdealSheafData := ⨅ F ∈ T, F.idealSheaf
  have hKinf : K = T.inf fun G => G.idealSheaf := by rw [Finset.inf_eq_iInf]
  have hKF : K ≤ F.idealSheaf := iInf₂_le F hF
  have hyK : y ∈ K.support := Scheme.IdealSheafData.support_antitone hKF hyF
  obtain ⟨z, rfl⟩ : ∃ z, K.subschemeι z = y := by
    rwa [← SetLike.mem_coe, ← K.range_subschemeι] at hyK
  have : LocallyOfFinitePresentation (K.subschemeι ≫ sY) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := K.subschemeι ≫ sY)).mpr
      inferInstance
  have : Smooth (K.subschemeι ≫ sY) := (isSmoothScheme_iff _).mp hsm
  have hreg := isRegularLocalRing_stalk_of_smooth_over_field (K.subschemeι ≫ sY) z
  have : IsDomain (K.subscheme.presheaf.stalk z) := IsRegularLocalRing.isDomain _
  have hdom : IsDomain (Y.presheaf.stalk (K.subschemeι z) ⧸
      IdealSheafData.stalk K (K.subschemeι z)) :=
    (IdealSheafData.subschemeStalkQuotEquiv K z).toMulEquiv.isDomain
  have hprime : (IdealSheafData.stalk K (K.subschemeι z)).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime _).mp hdom
  set y := K.subschemeι z
  have hKs : IdealSheafData.stalk K y = T.inf fun G => IdealSheafData.stalk G.idealSheaf y := by
    rw [hKinf, MMP.Intersection.stalk_finsetInf]
  obtain ⟨G, hG, hGK⟩ := (Ideal.IsPrime.inf_le' (s := T)
    (f := fun G : PrimeDivisor Y => IdealSheafData.stalk G.idealSheaf y) hprime).mp hKs.symm.le
  have hyG : y ∈ G.support := by
    by_contra hyG
    rw [MMP.Intersection.stalk_idealSheaf_eq_top_of_notMem_support G hyG, top_le_iff] at hGK
    exact hprime.ne_top hGK
  obtain ⟨n, w, j, hw, hj, hI⟩ := hD.2 y
  have := isRegularLocalRing_of_isRegularSystemOfParameters hw
  have key : ∀ (P : PrimeDivisor Y) (hP : P ∈ T) (hyP : y ∈ P.support),
      j ⟨G, hT hG, hyG⟩ = j ⟨P, hT hP, hyP⟩ := by
    intro P hP hyP
    by_contra hjne
    have h1 : IdealSheafData.stalk G.idealSheaf y ≤ IdealSheafData.stalk P.idealSheaf y :=
      hGK.trans (hKs.le.trans (Finset.inf_le (f := fun G : PrimeDivisor Y =>
        IdealSheafData.stalk G.idealSheaf y) hP))
    rw [hI ⟨G, hT hG, hyG⟩, hI ⟨P, hT hP, hyP⟩, Ideal.span_singleton_le_iff_mem] at h1
    exact MMP.Resolution.notMem_span_singleton_of_isRegularSystemOfParameters hw hjne h1
  have h12 := (key F hF hyF).symm.trans (key F' hF' hyF')
  exact hne (congrArg Subtype.val (hj h12))

/-- The images of the other members of a regular system of parameters form one in the quotient by
one member. -/
private theorem exists_isRegularSystemOfParameters_of_surjective {A B : Type*} [CommRing A]
    [CommRing B] [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] (ψ : A →+* B)
    (hψ : Function.Surjective ψ) {n : ℕ} {z : Fin n → A} (hz : IsRegularSystemOfParameters z)
    {m : Fin n} (hker : RingHom.ker ψ = Ideal.span {z m}) :
    ∃ (n' : ℕ) (z' : Fin n' → B) (σ : {i : Fin n // i ≠ m} → Fin n'),
      IsRegularSystemOfParameters z' ∧ Function.Injective σ ∧ ∀ i, z' (σ i) = ψ (z i.1) := by
  classical
  have := isRegularLocalRing_of_isRegularSystemOfParameters hz
  obtain ⟨hreg, -, hsop⟩ :=
    MMP.Flips.ResolutionInputs.isRegularSystemOfParameters_quotient_image hz {m}
  have hs : Ideal.span (z '' (({m} : Finset (Fin n)) : Set (Fin n))) = RingHom.ker ψ := by
    rw [hker]
    simp
  let e : (A ⧸ Ideal.span (z '' (({m} : Finset (Fin n)) : Set (Fin n)))) ≃+* B :=
    (Ideal.quotEquivOfEq hs).trans (RingHom.quotientKerEquivOfSurjective hψ)
  have he : ∀ a, e (Ideal.Quotient.mk _ a) = ψ a := fun a => rfl
  set emb := (({m} : Finset (Fin n))ᶜ).orderEmbOfFin rfl
  have hrange : ∀ i : {i : Fin n // i ≠ m}, ∃ k, emb k = i.1 := fun i => by
    rw [← Set.mem_range, Finset.range_orderEmbOfFin]
    simpa using i.2
  refine ⟨_, e ∘ fun j => Ideal.Quotient.mk _ (z (emb j)), fun i => (hrange i).choose,
    IsRegularSystemOfParameters.map_ringEquiv e hsop, ?_, ?_⟩
  · intro i i' h
    apply Subtype.ext
    rw [← (hrange i).choose_spec, ← (hrange i').choose_spec]
    exact congrArg emb h
  · intro i
    simp only [Function.comp_apply, he]
    rw [(hrange i).choose_spec]

/-- The kernel of the stalk map of a closed subscheme composed with an isomorphism is the stalk of
its ideal. -/
private theorem ker_stalkMap_comp_subschemeι {W Y : Scheme.{u}} (J : Y.IdealSheafData)
    (e : W ⟶ J.subscheme) [IsIso e] (w : W) :
    RingHom.ker ((e ≫ J.subschemeι).stalkMap w).hom =
      IdealSheafData.stalk J ((e ≫ J.subschemeι) w) := by
  haveI : IsIso (e.stalkMap w) := IsOpenImmersion.instIsIsoCommRingCatStalkMap e w
  have hinj : Function.Injective (e.stalkMap w).hom :=
    (asIso (e.stalkMap w)).commRingCatIsoToRingEquiv.injective
  have key : ∀ a, ((e ≫ J.subschemeι).stalkMap w).hom a =
      (e.stalkMap w).hom ((J.subschemeι.stalkMap (e w)).hom a) := fun a => by
    rw [Scheme.Hom.stalkMap_comp]; rfl
  ext a
  rw [RingHom.mem_ker, key, map_eq_zero_iff _ hinj]
  have h2 := IdealSheafData.ker_stalkMap_subschemeι J (e w)
  exact (SetLike.ext_iff.mp h2 a : _)

/-- The kernel of the stalk map of `X' ×_X Z ⟶ X'` is the stalk of the inverse image of the ideal
of `Z`. -/
private theorem ker_stalkMap_pullback_fst {X Y : Scheme.{u}} (I : X.IdealSheafData) (f : Y ⟶ X)
    (w : ↥(pullback f I.subschemeι)) :
    RingHom.ker ((pullback.fst f I.subschemeι).stalkMap w).hom =
      IdealSheafData.stalk (I.comap f) (pullback.fst f I.subschemeι w) := by
  have h := Scheme.IdealSheafData.comapIso_inv_subschemeι I f
  have key : ∀ q : pullback f I.subschemeι ⟶ Y, (I.comapIso f).inv ≫ (I.comap f).subschemeι = q →
      RingHom.ker (q.stalkMap w).hom = IdealSheafData.stalk (I.comap f) (q w) := by
    rintro q rfl
    exact ker_stalkMap_comp_subschemeι _ _ w
  exact key _ h

/-- The reduced ideal of the inverse image of a principal locus is generated by the pulled-back
generator when that is prime. -/
private theorem stalk_vanishingIdeal_preimage_eq_span {W Y : Scheme.{u}} (p : W ⟶ Y) (w : W)
    (I : Y.IdealSheafData) {c : Y.presheaf.stalk (p w)}
    (hI : IdealSheafData.stalk I (p w) = Ideal.span {c})
    (hc : (Ideal.span {(p.stalkMap w).hom c}).IsPrime) :
    IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal
      ⟨p ⁻¹' I.support, I.support.isClosed.preimage p.continuous⟩) w =
      Ideal.span {(p.stalkMap w).hom c} := by
  refine MMP.Resolution.stalk_vanishingIdeal_eq_span_singleton _ w hc fun q => ?_
  have h : p (W.fromSpecStalk w q) =
      Y.fromSpecStalk (p w) (PrimeSpectrum.comap (p.stalkMap w).hom q) := by
    have := congrArg (fun φ : Spec (W.presheaf.stalk w) ⟶ Y => φ.base q)
      (Scheme.SpecMap_stalkMap_fromSpecStalk p (x := w))
    exact this.symm
  change p (W.fromSpecStalk w q) ∈ I.support ↔ _
  rw [h]
  have h2 := Set.ext_iff.mp (MMP.Resolution.preimage_fromSpecStalk_support I (p w))
    (PrimeSpectrum.comap (p.stalkMap w).hom q)
  refine (h2.trans ?_)
  rw [hI]
  show ((Ideal.span {c} : Ideal (Y.presheaf.stalk (p w))) : Set (Y.presheaf.stalk (p w))) ⊆
    ((PrimeSpectrum.comap (p.stalkMap w).hom q).asIdeal : Set (Y.presheaf.stalk (p w))) ↔ _
  rw [SetLike.coe_subset_coe, Ideal.span_le, Set.singleton_subset_iff]
  rfl

/-- Local coordinates on the base change: the boundary components through the image point are cut
out by distinct coordinates. -/
private theorem exists_coordinates_pullback {R : Type*} [Zero R] {X Y T : Scheme.{u}}
    [IsLocallyNoetherian Y] (I : X.IdealSheafData) (f : Y ⟶ X)
    [IsLocallyNoetherian (pullback f I.subschemeι)] {s : Y ⟶ T}
    {D' : DivisorWithCoeffs R Y} (hD' : D'.IsSNC s) (w : ↥(pullback f I.subschemeι))
    {E : PrimeDivisor Y} (hE : E ∈ D'.support) (hyE : pullback.fst f I.subschemeι w ∈ E.support)
    (hJ : IdealSheafData.stalk (I.comap f) (pullback.fst f I.subschemeι w) =
      IdealSheafData.stalk E.idealSheaf (pullback.fst f I.subschemeι w)) :
    ∃ (n : ℕ) (z : Fin n → (pullback f I.subschemeι).presheaf.stalk w)
      (κ : {G : PrimeDivisor Y // G ∈ D'.support ∧ pullback.fst f I.subschemeι w ∈ G.support ∧
        G ≠ E} → Fin n),
      IsRegularSystemOfParameters z ∧ Function.Injective κ ∧
        ∀ G, IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal
          ⟨pullback.fst f I.subschemeι ⁻¹' G.1.idealSheaf.support,
            G.1.idealSheaf.support.isClosed.preimage (pullback.fst f I.subschemeι).continuous⟩) w =
          Ideal.span {z (κ G)} := by
  set p := pullback.fst f I.subschemeι
  obtain ⟨N, zY, j, hz, hj, hI⟩ := hD'.2 (p w)
  set m := j ⟨E, hE, hyE⟩
  have hsurj : Function.Surjective (p.stalkMap w).hom := p.stalkMap_surjective w
  have hker : RingHom.ker (p.stalkMap w).hom = Ideal.span {zY m} := by
    rw [ker_stalkMap_pullback_fst, hJ]; exact hI ⟨E, hE, hyE⟩
  obtain ⟨n', z', σ, hz', hσ, hσz⟩ :=
    exists_isRegularSystemOfParameters_of_surjective _ hsurj hz hker
  have hreg := isRegularLocalRing_of_isRegularSystemOfParameters hz'
  have hne : ∀ G : {G : PrimeDivisor Y // G ∈ D'.support ∧ p w ∈ G.support ∧ G ≠ E},
      j ⟨G.1, G.2.1, G.2.2.1⟩ ≠ m := fun G h => G.2.2.2 (congrArg Subtype.val (hj h))
  refine ⟨n', z', fun G => σ ⟨j ⟨G.1, G.2.1, G.2.2.1⟩, hne G⟩, hz', ?_, fun G => ?_⟩
  · intro G G' h
    have h1 := hσ h
    simp only [Subtype.mk.injEq] at h1
    have h2 : G.1 = G'.1 := Subtype.mk.inj (hj h1)
    exact Subtype.ext h2
  · rw [hσz]
    refine stalk_vanishingIdeal_preimage_eq_span p w G.1.idealSheaf (hI ⟨G.1, G.2.1, G.2.2.1⟩) ?_
    rw [← hσz ⟨_, hne G⟩]
    exact MMP.Resolution.isPrime_span_singleton_of_isRegularSystemOfParameters hz' _

/-- A reduced scheme birational to an integral scheme is integral. -/
private theorem isIntegral_of_isBirationalMorphism {X Y : Scheme.{u}} [IsIntegral X] [IsReduced Y]
    {f : Y ⟶ X} (hf : IsBirationalMorphism f) : IsIntegral Y := by
  obtain ⟨e, -⟩ := hf
  have hne : (e.target : Set X).Nonempty := e.dense_target.nonempty
  have ht : IsIrreducible (e.target : Set X) :=
    ⟨hne, (IrreducibleSpace.isIrreducible_univ X).2.open_subset e.target.isOpen
      (Set.subset_univ _)⟩
  have h1 : IrreducibleSpace e.target.toScheme := Subtype.irreducibleSpace ht
  have h2 : IrreducibleSpace e.source.toScheme :=
    (Homeomorph.irreducibleSpace_iff e.iso.hom.homeomorph).mpr h1
  have hs : IsIrreducible (e.source : Set Y) := @IsIrreducible.of_subtype _ _ _ h2
  have : IrreducibleSpace Y := by
    rw [irreducibleSpace_def]
    have := hs.closure
    rwa [e.dense_source.closure_eq] at this
  exact isIntegral_of_irreducibleSpace_of_isReduced Y

/-- For a morphism from a reduced scheme to a separated scheme, a prime divisor is exceptional iff
the image of its generic point has coheight at least two. -/
private theorem isExceptional_iff_two_le_coheight {W T : Scheme.{u}} [IsReduced W]
    [IsSeparated (T ↘ ⊤_ Scheme)] (g : W ⟶ T) (E : PrimeDivisor W) :
    RationalMap.IsExceptional (X := W) g.toRationalMap E ↔
      2 ≤ Order.coheight (g (AlgebraicGeometry.PrimeDivisor.genericPoint E)) := by
  have hdef : RationalMap.DefinedAt (X := W) g.toRationalMap
      (AlgebraicGeometry.PrimeDivisor.genericPoint E) := by
    rw [RationalMap.DefinedAt, RationalMap.dom_toRationalMap_hom]
    trivial
  have htr := MMP.Positivity.closure_image_eq_transform g.toPartialMap rfl E.idealSheaf.support
    (by
      change closure ((E.idealSheaf.support : Set W) ∩ ((⊤ : W.Opens) : Set W)) = _
      rw [TopologicalSpace.Opens.coe_top, Set.inter_univ, E.idealSheaf.support.isClosed.closure_eq])
  rw [RationalMap.isExceptional_iff, ← htr, MMP.Positivity.image_toPartialMap_hom]
  have hcl : Closeds.closure (g '' (E.idealSheaf.support : Set W)) =
      ⟨((IrreducibleCloseds.closureSingleton
          (g (AlgebraicGeometry.PrimeDivisor.genericPoint E)) : IrreducibleCloseds T) : Set T),
        (IrreducibleCloseds.closureSingleton
          (g (AlgebraicGeometry.PrimeDivisor.genericPoint E))).isClosed⟩ := by
    ext1
    change closure (g '' E.support) = closure {g (AlgebraicGeometry.PrimeDivisor.genericPoint E)}
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    refine le_antisymm ?_ (closure_mono ?_)
    · refine closure_minimal ?_ isClosed_closure
      refine (image_closure_subset_closure_image g.continuous).trans ?_
      rw [Set.image_singleton]
    · rw [Set.singleton_subset_iff]
      exact ⟨_, subset_closure rfl, rfl⟩
  rw [hcl, closedsCodimension_coe, codimension_eq_coheight,
    show IrreducibleCloseds.closureSingleton (g (AlgebraicGeometry.PrimeDivisor.genericPoint E)) =
      (irreducibleSetEquivPoints (α := T)).symm
        (g (AlgebraicGeometry.PrimeDivisor.genericPoint E)) from rfl,
    Order.coheight_orderIso]
  exact ⟨fun h => h hdef, fun h _ => h⟩

/-- A scheme separated over a field is separated. -/
private theorem isSeparated_terminal_of_isSeparated {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsSeparated sX] : IsSeparated (X ↘ ⊤_ Scheme) := by
  rw [show (X ↘ ⊤_ Scheme) = sX ≫ (Spec (.of k) ↘ ⊤_ Scheme) from
    Limits.terminal.hom_ext _ _]
  infer_instance

/-- Every point of a closed set lies on a maximal irreducible subset of it, which is closed. -/
private theorem exists_maximal_isIrreducible_subset {T : Type*} [TopologicalSpace T] {S : Set T}
    (hS : IsClosed S) {x : T} (hx : x ∈ S) :
    ∃ C, Maximal (fun C => IsIrreducible C ∧ C ⊆ S) C ∧ x ∈ C ∧ IsClosed C := by
  obtain ⟨m, hxm, hm⟩ := zorn_subset_nonempty { t : Set T | IsPreirreducible t ∧ t ⊆ S }
    (fun c hc hcc _ => ⟨⋃₀ c, ⟨fun u v hu hv ⟨y, hy, hyu⟩ ⟨x, hx, hxv⟩ =>
        let ⟨p, hpc, hyp⟩ := Set.mem_sUnion.1 hy
        let ⟨q, hqc, hxq⟩ := Set.mem_sUnion.1 hx
        Or.casesOn (hcc.total hpc hqc)
          (fun hpq : p ⊆ q =>
            let ⟨x, hxp, hxuv⟩ := (hc hqc).1 u v hu hv ⟨y, hpq hyp, hyu⟩ ⟨x, hxq, hxv⟩
            ⟨x, Set.mem_sUnion_of_mem hxp hqc, hxuv⟩)
          fun hqp : q ⊆ p =>
          let ⟨x, hxp, hxuv⟩ := (hc hpc).1 u v hu hv ⟨y, hyp, hyu⟩ ⟨x, hqp hxq, hxv⟩
          ⟨x, Set.mem_sUnion_of_mem hxp hpc, hxuv⟩,
        Set.sUnion_subset fun t ht => (hc ht).2⟩,
        fun _ hxc => Set.subset_sUnion_of_mem hxc⟩)
    {x} ⟨isPreirreducible_singleton, Set.singleton_subset_iff.mpr hx⟩
  have hxm' : x ∈ m := hxm rfl
  have hmax : Maximal (fun C => IsIrreducible C ∧ C ⊆ S) m :=
    ⟨⟨⟨⟨x, hxm'⟩, hm.prop.1⟩, hm.prop.2⟩, fun C hC hmC => hm.2 ⟨hC.1.2, hC.2⟩ hmC⟩
  refine ⟨m, hmax, hxm', ?_⟩
  have hcl : closure m ⊆ m :=
    hmax.2 ⟨hmax.prop.1.closure, closure_minimal hmax.prop.2 hS⟩ subset_closure
  exact closure_subset_iff_isClosed.mp hcl

/-- An integral scheme proper over a variety is a variety. -/
private theorem isVariety_comp_of_isProper {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} (hX : MMP.Mori.IsVariety k sX) (f : Y ⟶ X) [IsIntegral Y] [IsProper f] :
    MMP.Mori.IsVariety k (f ≫ sX) := by
  have := hX.toIsSeparated
  have := hX.toLocallyOfFiniteType
  have := hX.toQuasiCompact
  exact (isVariety_iff k _).mpr ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- For a proper birational morphism onto a normal variety, the points off the biregular locus have
codimension at least two. -/
private theorem two_le_coheight_of_notMem_biregularLocus {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) (f : Y ⟶ X)
    (hY : MMP.Mori.IsVariety k (f ≫ sX)) [IsProper f] (hf : IsBirationalMorphism f) {x : X}
    (hx : x ∉ biregularLocus f) : 2 ≤ Order.coheight x := by
  by_contra h
  apply hx
  refine MMP.Mori.mem_biregularLocus_of_ringKrullDim_stalk_le_one hX f hY hf ?_
  rw [ringKrullDim_stalk_eq_coheight]
  have : Order.coheight x ≤ 1 := by
    have h' : Order.coheight x < 2 := lt_of_not_ge h
    exact Order.le_of_lt_succ h'
  exact_mod_cast this

/-- The exceptional set of a log resolution is the union of its exceptional prime divisors. -/
private theorem exists_mem_of_mem_exceptionalSet {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) [IsReduced Y] {D : RDivisor X}
    {f : Y ⟶ X} (hf : IsLogResolution sX D f) (hY : MMP.Mori.IsVariety k (f ≫ sX))
    (Ex : Finset (PrimeDivisor Y))
    (hEx : ∀ F : PrimeDivisor Y, F ∈ Ex ↔ RationalMap.IsExceptional f.toRationalMap F)
    {y : Y} (hy : y ∈ exceptionalSet f) : ∃ E ∈ Ex, y ∈ E.support := by
  have := hf.isProper
  have := hX.1.toIsSeparated
  have := isSeparated_terminal_of_isSeparated sX
  obtain ⟨C, hC, hyC, hCcl⟩ := exists_maximal_isIrreducible_subset
    (exceptionalSet f).isClosed hy
  set W' : IrreducibleCloseds Y := ⟨C, hC.1.1, hCcl⟩
  have hmaxW : Maximal (fun W'' : IrreducibleCloseds Y => (W'' : Set Y) ⊆ exceptionalSet f) W' :=
    ⟨hC.1.2, fun W'' hW'' hle => hC.2 ⟨W''.isIrreducible, hW''⟩ hle⟩
  have hcod := hf.isPureCodimOne_exceptionalSet W' hmaxW
  have hgen := hC.1.1.isGenericPoint_genericPoint_closure
  rw [hCcl.closure_eq] at hgen
  set η := hC.1.1.genericPoint
  have hη : Order.coheight η = 1 := by
    rw [coheight_eq_codimension_closureSingleton, ← hcod]
    congr 1
    exact IrreducibleCloseds.ext hgen.def
  set P := AlgebraicGeometry.PrimeDivisor.ofCoheightOne η hη
  have hPs : P.support = C := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
    exact hgen.def
  have hηEx : η ∈ exceptionalSet f := hC.1.2 (hgen.mem)
  refine ⟨P, (hEx P).mpr ?_, hPs ▸ hyC⟩
  rw [isExceptional_iff_two_le_coheight, AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
  exact two_le_coheight_of_notMem_biregularLocus hX f hY hf.isBirationalMorphism hηEx

/-- Over a point outside the biregular locus of a proper birational morphism onto a normal variety,
the fibre has more than one point. -/
private theorem not_subsingleton_fiber_of_notMem_biregularLocus {k : Type u} [Field k]
    {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) (f : Y ⟶ X)
    (hY : MMP.Mori.IsVariety k (f ≫ sX)) [IsProper f] (hf : IsBirationalMorphism f) {x : X}
    (hx : x ∉ biregularLocus f) : ¬ (f ⁻¹' {x}).Subsingleton := by
  have := hX.2
  have := hY.toIsIntegral
  have := hX.1.toIsIntegral
  have := hf.isDominant
  obtain ⟨u, rfl⟩ := f.surjective x
  have hu : u ∈ exceptionalSet f := hx
  have key := (MMP.Resolution.Bridges.isIso_finiteFibreLocus_and_exceptionalSet_eq k hY hX.1 f
    rfl (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hf)).2.1
  have hu' : u ∈ (exceptionalSet f : Set Y) := hu
  rw [key] at hu'
  intro hsub
  have : Subsingleton (f ⁻¹' {f u}) := hsub.coe_sort
  have : DiscreteTopology (f ⁻¹' {f u}) := ⟨Subsingleton.elim _ _⟩
  have h0 := topologicalKrullDim_zero_of_discreteTopology (f ⁻¹' {f u})
  have hu'' : 0 < topologicalKrullDim (f ⁻¹' {f u}) := hu'
  exact absurd (lt_of_lt_of_le hu'' h0) (lt_irrefl _)

/-- Being an isomorphism over an open is stable under base change. -/
private theorem isIso_pullback_snd_morphismRestrict {X Y Z : Scheme.{u}} (f : Y ⟶ X) (ι : Z ⟶ X)
    (V : X.Opens) [IsIso (f ∣_ V)] :
    IsIso (pullback.snd f ι ∣_ (ι ⁻¹ᵁ V)) := by
  have hC := (isPullback_morphismRestrict (pullback.snd f ι) (ι ⁻¹ᵁ V)).flip
  have hB := IsPullback.of_hasPullback f ι
  have hs := hC.paste_horiz hB
  rw [← morphismRestrict_ι ι V] at hs
  have hD := IsPullback.of_right' hs (isPullback_morphismRestrict f V).flip
  exact hD.isIso_snd_of_isIso

/-- The base change of `f` is biregular over the preimage of the biregular locus of `f`. -/
private theorem isBiregular_pullback_snd {X Y Z : Scheme.{u}} (f : Y ⟶ X) (ι : Z ⟶ X) :
    IsBiregular (pullback.snd f ι) (ι ⁻¹ᵁ biregularLocus f) := by
  have : IsIso (f ∣_ biregularLocus f) := isBiregular_biregularLocus f
  exact isIso_pullback_snd_morphismRestrict f ι _

/-- A morphism is injective over its biregular locus. -/
private theorem injOn_preimage_biregularLocus {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Set.InjOn f.base (f ⁻¹ᵁ biregularLocus f : Set X) := by
  have : IsIso (f ∣_ biregularLocus f) := isBiregular_biregularLocus f
  have hinj : Function.Injective ((f ⁻¹ᵁ biregularLocus f).ι ≫ f).base := by
    rw [← morphismRestrict_ι]
    exact ((f ∣_ biregularLocus f) ≫ (biregularLocus f).ι).isOpenEmbedding.injective
  exact fun a ha b hb hab ↦ congrArg Subtype.val (@hinj ⟨a, ha⟩ ⟨b, hb⟩ hab)

/-- The biregular locus of the base change is the preimage of the biregular locus of `f`, when the
fibres of `f` over the other points have several points. -/
private theorem mem_biregularLocus_pullback_snd_iff {X Y Z : Scheme.{u}} (f : Y ⟶ X) (ι : Z ⟶ X)
    (hA : ∀ x, x ∉ biregularLocus f → ¬ (f ⁻¹' {x}).Subsingleton) (z : Z) :
    z ∈ biregularLocus (pullback.snd f ι) ↔ ι z ∈ biregularLocus f := by
  constructor
  · intro hz
    by_contra hx
    apply hA _ hx
    intro y₁ hy₁ y₂ hy₂
    obtain ⟨w₁, hw₁, hw₁'⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := ι) y₁ z hy₁
    obtain ⟨w₂, hw₂, hw₂'⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := ι) y₂ z hy₂
    have h12 : w₁ = w₂ := injOn_preimage_biregularLocus (pullback.snd f ι)
      (show pullback.snd f ι w₁ ∈ biregularLocus (pullback.snd f ι) by rwa [hw₁'])
      (show pullback.snd f ι w₂ ∈ biregularLocus (pullback.snd f ι) by rwa [hw₂'])
      (hw₁'.trans hw₂'.symm)
    rw [← hw₁, ← hw₂, h12]
  · intro hz
    exact le_biregularLocus (isBiregular_pullback_snd f ι) hz

/-- A morphism which is an isomorphism over a dense open with dense preimage is birational. -/
private theorem isBirationalMorphism_of_isIso_morphismRestrict {W Z : Scheme.{u}} (g : W ⟶ Z)
    (V : Z.Opens) (hV : Dense (V : Set Z)) (hU : Dense (g ⁻¹ᵁ V : Set W))
    [IsIso (g ∣_ V)] : IsBirationalMorphism g := by
  let e : W.PartialIso Z :=
    { source := g ⁻¹ᵁ V
      dense_source := hU
      target := V
      dense_target := hV
      iso := asIso (g ∣_ V) }
  refine ⟨e, ?_⟩
  rw [Scheme.PartialIso.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨g ⁻¹ᵁ V, hU, le_rfl, le_top, ?_⟩
  simp only [Scheme.PartialMap.restrict, Scheme.PartialIso.toPartialMap_hom,
    Scheme.Hom.toPartialMap_hom, e, asIso_hom, morphismRestrict_ι]
  exact (Scheme.homOfLE_ι_assoc _ _ _).trans
    (by rw [Scheme.topIso_hom]; exact (Scheme.homOfLE_ι_assoc _ _ _).symm)

/-- The exceptional set of the base change is the preimage of the exceptional set of `f`. -/
private theorem mem_exceptionalSet_pullback_snd_iff {X Y Z : Scheme.{u}} (f : Y ⟶ X) (ι : Z ⟶ X)
    (hA : ∀ x, x ∉ biregularLocus f → ¬ (f ⁻¹' {x}).Subsingleton) (w : ↥(pullback f ι)) :
    w ∈ exceptionalSet (pullback.snd f ι) ↔ pullback.fst f ι w ∈ exceptionalSet f := by
  rw [mem_exceptionalSet, mem_exceptionalSet, mem_biregularLocus_pullback_snd_iff f ι hA,
    ← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]

/-- The reduced ideal of a connected component of a locally principal prime locus has the same
generator. -/
private theorem stalk_vanishingIdeal_connectedComponentIn {W : Scheme.{u}} (F : Closeds W) {w : W}
    {a : W.presheaf.stalk w} (ha : (Ideal.span {a}).IsPrime)
    (hT : ∀ q : PrimeSpectrum (W.presheaf.stalk w),
      W.fromSpecStalk w q ∈ (F : Set W) ↔ a ∈ q.asIdeal)
    {x : W} (hC : IsClosed (connectedComponentIn (F : Set W) x))
    (hwx : w ∈ connectedComponentIn (F : Set W) x) :
    IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal
      ⟨connectedComponentIn (F : Set W) x, hC⟩) w = Ideal.span {a} := by
  refine MMP.Resolution.stalk_vanishingIdeal_eq_span_singleton _ w ha fun q => ?_
  change W.fromSpecStalk w q ∈ connectedComponentIn (F : Set W) x ↔ _
  rw [← hT]
  constructor
  · exact fun h => connectedComponentIn_subset _ _ h
  · intro h
    have hsp : W.fromSpecStalk w q ⤳ w := MMP.Intersection.fromSpecStalk_specializes w q
    have hcl : closure {W.fromSpecStalk w q} ⊆ (F : Set W) :=
      closure_minimal (Set.singleton_subset_iff.mpr h) F.isClosed
    have hpc : _root_.IsPreconnected (closure {W.fromSpecStalk w q}) :=
      isPreconnected_singleton.closure
    rw [connectedComponentIn_eq hwx]
    exact hpc.subset_connectedComponentIn (specializes_iff_mem_closure.mp hsp) hcl
      (subset_closure rfl)

/-- If the connected components of `F` are irreducible, they are exactly its maximal irreducible
subsets. -/
private theorem maximal_isIrreducible_iff_connectedComponentIn {T : Type*} [TopologicalSpace T]
    {F : Set T} (hirr : ∀ x ∈ F, IsIrreducible (connectedComponentIn F x)) (C : Set T) :
    Maximal (fun C => IsIrreducible C ∧ C ⊆ F) C ↔ ∃ x ∈ F, C = connectedComponentIn F x := by
  constructor
  · intro hC
    obtain ⟨x, hx⟩ := hC.prop.1.nonempty
    have hxF := hC.prop.2 hx
    have h1 : C ⊆ connectedComponentIn F x :=
      (IsIrreducible.isConnected hC.prop.1).isPreconnected.subset_connectedComponentIn hx hC.prop.2
    exact ⟨x, hxF, le_antisymm h1 (hC.2 ⟨hirr x hxF, connectedComponentIn_subset _ _⟩ h1)⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨hirr x hx, connectedComponentIn_subset _ _⟩, fun T' hT' hle => ?_⟩
    exact (IsIrreducible.isConnected hT'.1).isPreconnected.subset_connectedComponentIn
      (hle (mem_connectedComponentIn hx)) hT'.2

/-- The local rings of a scheme smooth over a field are factorial. -/
private theorem uniqueFactorizationMonoid_stalk_of_isSmoothScheme' {k : Type u} [Field k]
    {Y : Scheme.{u}} (s : Y ⟶ Spec (.of k)) (hsm : IsSmoothScheme s) (y : Y) :
    UniqueFactorizationMonoid (Y.presheaf.stalk y) := by
  have : Smooth s := hsm.smooth
  have := isRegularLocalRing_stalk_of_smooth_over_field s y
  exact IsRegularLocalRing.uniqueFactorizationMonoid _

/-- The base change is smooth when the inverse image ideal is locally cut out by a regular
parameter. -/
private theorem isSmoothScheme_pullback_snd {k : Type u} [Field k] [PerfectField k]
    {X Y : Scheme.{u}}
    (I : X.IdealSheafData) (f : Y ⟶ X) (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType (f ≫ sX)]
    (hJ : ∀ y ∈ (I.comap f).support, ∃ (m : ℕ) (w : Fin m → Y.presheaf.stalk y) (j : Fin m),
      IsRegularSystemOfParameters w ∧ IdealSheafData.stalk (I.comap f) y = Ideal.span {w j}) :
    IsSmoothScheme (pullback.snd f I.subschemeι ≫ I.subschemeι ≫ sX) := by
  have h1 := MMP.Resolution.isSmoothScheme_subscheme_of_stalk_eq_span_parameter (f ≫ sX) _ hJ
  have : Smooth ((I.comap f).subschemeι ≫ f ≫ sX) := h1.smooth
  have : pullback.snd f I.subschemeι ≫ I.subschemeι ≫ sX =
      (I.comapIso f).inv ≫ (I.comap f).subschemeι ≫ f ≫ sX := by
    rw [← Category.assoc, ← pullback.condition, ← Category.assoc,
      Scheme.IdealSheafData.comapIso_inv_subschemeι, Category.assoc]
  rw [this]
  exact isSmoothScheme_of_smooth inferInstance

/-- A member of a free linear system is Cartier. -/
private theorem isCartier_zeroDivisor {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [IsIntegral X] {H : Divisor X} {ι : Type*}
    (s : ι → H.divisorialSubmodule ⊤)
    (hs : ∀ x : X, ∃ (i : ι) (hi : s i ≠ 0), x ∉ (H.zeroDivisor (s i) hi).supp)
    (σ : H.divisorialSubmodule ⊤) (hσ : σ ≠ 0) : (H.zeroDivisor σ hσ).IsCartier := by
  intro x
  obtain ⟨i, hi, hx⟩ := hs x
  set T := (H.zeroDivisor (s i) hi).supp
  refine ⟨⟨(T : Set X)ᶜ, T.isClosed.isOpen_compl⟩, hx,
    (Divisor.isUnit_sectionToRationalFunctions hσ).unit *
      (Divisor.isUnit_sectionToRationalFunctions hi).unit⁻¹,
    fun E hE => ?_⟩
  have h0 : (H.zeroDivisor (s i) hi).coeff E = 0 := by
    by_contra hne
    obtain ⟨y, hyE, hyU⟩ := hE
    exact hyU (DivisorWithCoeffs.support_subset_supp hne hyE)
  rw [Divisor.zeroDivisor_eq, DivisorWithCoeffs.coeff_add, coeff_principalDivisor] at h0 ⊢
  rw [PrimeDivisor.ord_mul, PrimeDivisor.ord_inv]
  omega

/-- The preimage in the base change of a boundary component is cut out by a regular parameter. -/
private theorem exists_isRegularSystemOfParameters_stalk_vanishingIdeal_preimage {R : Type*}
    [Zero R] {X Y T : Scheme.{u}}
    [IsLocallyNoetherian Y] (I : X.IdealSheafData) (f : Y ⟶ X)
    [IsLocallyNoetherian (pullback f I.subschemeι)] {s : Y ⟶ T}
    {D' : DivisorWithCoeffs R Y} (hD' : D'.IsSNC s) (𝔅 : Set (PrimeDivisor Y))
    (hK : ∀ w : ↥(pullback f I.subschemeι), ∃ E ∈ D'.support,
      pullback.fst f I.subschemeι w ∈ E.support ∧ E ∉ 𝔅 ∧
      IdealSheafData.stalk (I.comap f) (pullback.fst f I.subschemeι w) =
        IdealSheafData.stalk E.idealSheaf (pullback.fst f I.subschemeι w))
    {G : PrimeDivisor Y} (hG : G ∈ D'.support) (hG𝔅 : G ∈ 𝔅) :
    ∀ w ∈ (Scheme.IdealSheafData.vanishingIdeal
      ⟨pullback.fst f I.subschemeι ⁻¹' G.idealSheaf.support,
        G.idealSheaf.support.isClosed.preimage (pullback.fst f I.subschemeι).continuous⟩).support,
      ∃ (m : ℕ) (z : Fin m → (pullback f I.subschemeι).presheaf.stalk w) (j : Fin m),
        IsRegularSystemOfParameters z ∧
        IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal
          ⟨pullback.fst f I.subschemeι ⁻¹' G.idealSheaf.support,
            G.idealSheaf.support.isClosed.preimage
              (pullback.fst f I.subschemeι).continuous⟩) w = Ideal.span {z j} := by
  intro w hw
  rw [← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal] at hw
  obtain ⟨E, hE, hyE, hE𝔅, hJ⟩ := hK w
  obtain ⟨n, z, κ, hz, -, hκ⟩ := exists_coordinates_pullback I f hD' w hE hyE hJ
  have hne : G ≠ E := fun h => hE𝔅 (h ▸ hG𝔅)
  exact ⟨n, z, κ ⟨G, hG, hw, hne⟩, hz, hκ ⟨G, hG, hw, hne⟩⟩

/-- A set containing a generization of every point is dense. -/
private theorem dense_of_forall_exists_specializes {T : Type*} [TopologicalSpace T] {S : Set T}
    (h : ∀ t, ∃ t' ∈ S, t' ⤳ t) : Dense S := by
  intro t
  obtain ⟨t', ht', hsp⟩ := h t
  exact closure_mono (Set.singleton_subset_iff.mpr ht') (specializes_iff_mem_closure.mp hsp)

/-- A prime divisor whose generic point lies on a prime divisor `E` is `E`. -/
private theorem eq_of_genericPoint_mem_support {Y : Scheme.{u}} {E F : PrimeDivisor Y}
    (hF : AlgebraicGeometry.PrimeDivisor.genericPoint F ∈ E.support) : F = E := by
  apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hF
  have h1 : AlgebraicGeometry.PrimeDivisor.genericPoint E ⤳
      AlgebraicGeometry.PrimeDivisor.genericPoint F := specializes_iff_mem_closure.mpr hF
  by_contra hne
  have := Order.coheight_strictAnti (MMP.Intersection.lt_of_specializes_of_ne h1 hne)
  rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint,
    AlgebraicGeometry.PrimeDivisor.coheight_genericPoint] at this
  exact lt_irrefl _ (this (by decide))

/-- Arithmetic in `WithBot ℕ∞`: `3 ≤ a + 1` gives `2 ≤ a`. -/
private theorem two_le_of_three_le_add_one {a : WithBot ℕ∞} (h : 3 ≤ a + 1) : 2 ≤ a := by
  induction a using WithBot.recBotCoe with
  | bot => exact absurd h (by decide)
  | coe n =>
    have h' : ((3 : ℕ∞) : WithBot ℕ∞) ≤ ((n + 1 : ℕ∞) : WithBot ℕ∞) := h
    have h'' : (2 : ℕ∞) + 1 ≤ n + 1 := WithBot.coe_le_coe.mp h'
    have : (2 : ℕ∞) ≤ n := (ENat.add_le_add_iff_right ENat.one_ne_top).mp h''
    exact WithBot.coe_le_coe.mpr this

/-- On a connected component of a member, the codimension drops by at most one: a point of
codimension at least three in `X` has codimension at least two in the component. -/
private theorem two_le_coheight_subscheme_vanishingIdeal {X : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral X] {D : Divisor X} (hD : 0 ≤ D) (hDc : D.IsCartier) {Z : Closeds X}
    {x₀ : X} (hZ : connectedComponentIn (D.supp : Set X) x₀ = Z)
    (t : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme)
    (h3 : 3 ≤ Order.coheight ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι t)) :
    2 ≤ Order.coheight t := by
  set x := (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι t
  have hZD : (Z : Set X) ⊆ D.supp := hZ ▸ connectedComponentIn_subset _ _
  have hxZ : x ∈ (Z : Set X) := by
    have : x ∈ Set.range (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι := ⟨t, rfl⟩
    rwa [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
      at this
  obtain ⟨U, hxU, φ, hφ⟩ := hDc x
  obtain ⟨a, ha⟩ := exists_germ_eq_of_isLocalEquation hD hφ hxU
  have hna := not_isUnit_of_isLocalEquation_of_mem_supp hφ hxU _ ha (hZD hxZ)
  have hamax : a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) :=
    (IsLocalRing.mem_maximalIdeal _).mpr hna
  have hsub : IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal Z) x ≤
      (Ideal.span {a}).radical := by
    intro b hb
    rw [MMP.Resolution.stalk_vanishingIdeal_eq, PrimeSpectrum.mem_vanishingIdeal] at hb
    rw [← PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical, PrimeSpectrum.mem_vanishingIdeal]
    intro q hq
    apply hb q
    have haq : a ∈ q.asIdeal := hq (Ideal.subset_span rfl)
    set x' := X.fromSpecStalk x q
    have h : x' ⤳ x := MMP.Intersection.fromSpecStalk_specializes x q
    have hx'D : x' ∈ D.supp := by
      by_contra hx'
      have hW : x' ∈ (pointComponent x).1 :=
        (pointComponent x).2.2 (IrreducibleSpace.isIrreducible_univ X) (Set.subset_univ _)
          (Set.mem_univ x')
      have hu := isUnit_of_isLocalEquation_of_notMem_supp hφ (h.mem_open U.isOpen hxU) hW
        (a := X.presheaf.stalkSpecializes h a) (by
          rw [← ha]
          change (X.presheaf.stalkSpecializes h ≫ X.presheaf.stalkSpecializes _).hom a = _
          rw [TopCat.Presheaf.stalkSpecializes_comp]
          rfl) hx'
      have hmem : a ∈ (IsLocalRing.maximalIdeal (X.presheaf.stalk (X.fromSpecStalk x q))).comap
          (X.presheaf.stalkSpecializes (MMP.Intersection.fromSpecStalk_specializes x q)).hom := by
        rwa [MMP.Intersection.comap_maximalIdeal_stalkSpecializes_fromSpecStalk]
      exact (IsLocalRing.mem_maximalIdeal _).mp hmem hu
    have hcl : closure {x'} ⊆ (D.supp : Set X) :=
      closure_minimal (Set.singleton_subset_iff.mpr hx'D) D.supp.isClosed
    have hcc : connectedComponentIn (D.supp : Set X) x = Z := by
      rw [← hZ]
      exact (connectedComponentIn_eq (hZ ▸ hxZ)).symm
    have := isPreconnected_singleton.closure.subset_connectedComponentIn
      (specializes_iff_mem_closure.mp h) hcl (subset_closure rfl)
    rw [hcc] at this
    exact this
  have e1 : (Order.coheight t : WithBot ℕ∞) =
      ringKrullDim ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme.presheaf.stalk t) :=
    (ringKrullDim_stalk_eq_coheight t).symm
  have e2 := ringKrullDim_eq_of_ringEquiv
    (MMP.Flips.ResolutionInputs.stalkQuotientEquiv (Scheme.IdealSheafData.vanishingIdeal Z) t)
  have hdim1 : ringKrullDim (X.presheaf.stalk x ⧸ (Ideal.span {a}).radical) ≤
      ringKrullDim (X.presheaf.stalk x ⧸
        IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal Z) x) :=
    ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hsub)
  have hdim2 : ringKrullDim (X.presheaf.stalk x ⧸ (Ideal.span {a}).radical) =
      ringKrullDim (X.presheaf.stalk x ⧸ Ideal.span {a}) := by
    rw [ringKrullDim_quotient, ringKrullDim_quotient, PrimeSpectrum.zeroLocus_radical]
  have hdim3 : ringKrullDim (X.presheaf.stalk x) ≤
      ringKrullDim (X.presheaf.stalk x ⧸ Ideal.span {a}) + 1 := by
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
    exact Ideal.height_le_ringKrullDim_quotient_add_one hamax
  have hdimx : (3 : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x) := by
    rw [ringKrullDim_stalk_eq_coheight]; exact WithBot.coe_le_coe.mpr h3
  have key : (2 : WithBot ℕ∞) ≤
      ringKrullDim ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme.presheaf.stalk t) := by
    rw [← e2]
    refine le_trans ?_ (hdim2 ▸ hdim1)
    exact two_le_of_three_le_add_one (hdimx.trans hdim3)
  rw [← e1] at key
  exact WithBot.coe_le_coe.mp key

/-- A prime divisor supported on a connected component of a locally principal prime locus is cut
out by the same generator. -/
private theorem stalk_idealSheaf_eq_of_support_eq_connectedComponentIn {W : Scheme.{u}}
    (F : Closeds W) {w : W} {a : W.presheaf.stalk w} (ha : (Ideal.span {a}).IsPrime)
    (hF : IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal F) w = Ideal.span {a})
    (P : PrimeDivisor W) {x : W} (hP : P.support = connectedComponentIn (F : Set W) x)
    (hwP : w ∈ P.support) : IdealSheafData.stalk P.idealSheaf w = Ideal.span {a} := by
  have hT : ∀ q : PrimeSpectrum (W.presheaf.stalk w),
      W.fromSpecStalk w q ∈ (F : Set W) ↔ a ∈ q.asIdeal := by
    intro q
    have h2 := Set.ext_iff.mp (MMP.Resolution.preimage_fromSpecStalk_support
      (Scheme.IdealSheafData.vanishingIdeal F) w) q
    have h2' : W.fromSpecStalk w q ∈ ((Scheme.IdealSheafData.vanishingIdeal F).support : Set W) ↔
        q ∈ PrimeSpectrum.zeroLocus ((Ideal.span {a} : Ideal _) : Set (W.presheaf.stalk w)) := by
      rwa [← hF]
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal] at h2'
    have h3 : q ∈ PrimeSpectrum.zeroLocus ((Ideal.span {a} : Ideal _) : Set (W.presheaf.stalk w)) ↔
        a ∈ q.asIdeal := by
      rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, Ideal.span_le,
        Set.singleton_subset_iff]
      rfl
    exact h2'.trans h3
  have hC : IsClosed (connectedComponentIn (F : Set W) x) := by
    rw [← hP]; exact P.idealSheaf.support.isClosed
  have h := stalk_vanishingIdeal_connectedComponentIn F ha hT hC (hP ▸ hwP)
  rw [← MMP.Intersection.vanishingIdeal_support_idealSheaf]
  convert h using 3
  exact Closeds.ext hP

/-- The support of `∑_{F ∈ S} F` is `S`. -/
private theorem support_sum_single {W : Scheme.{u}} (S : Finset (PrimeDivisor W)) :
    (∑ F ∈ S, Finsupp.single F (1 : ℤ)).support = S := by
  classical
  ext F
  simp [Finsupp.finsetSum_apply, Finsupp.single_apply]

/-- Two prime divisors that are connected components of preimages of disjoint (or equal) prime
divisors and share a point are equal. -/
private theorem eq_of_mem_support_of_eq_connectedComponentIn {W Y : Scheme.{u}} (g : W ⟶ Y)
    {P P' : PrimeDivisor W} {G G' : PrimeDivisor Y}
    (hGG' : G ≠ G' → Disjoint G.support G'.support)
    (hP : P.support = connectedComponentIn (g ⁻¹' G.support)
      (AlgebraicGeometry.PrimeDivisor.genericPoint P))
    (hP' : P'.support = connectedComponentIn (g ⁻¹' G'.support)
      (AlgebraicGeometry.PrimeDivisor.genericPoint P'))
    {w : W} (hw : w ∈ P.support) (hw' : w ∈ P'.support) : P = P' := by
  have hwG : w ∈ g ⁻¹' G.support := connectedComponentIn_subset _ _ (hP ▸ hw)
  have hwG' : w ∈ g ⁻¹' G'.support := connectedComponentIn_subset _ _ (hP' ▸ hw')
  have hGG : G = G' := by
    by_contra hne
    exact Set.disjoint_left.mp (hGG' hne) hwG hwG'
  apply AlgebraicGeometry.PrimeDivisor.eq_of_support_eq
  have e1 := connectedComponentIn_eq (hP ▸ hw)
  have e2 := connectedComponentIn_eq (hP' ▸ hw')
  rw [hP, hP', e1, e2, hGG]

/-- Connected components of the preimages of boundary components form an snc divisor on the base
change. -/
private theorem isSNC_sum_of_connectedComponents {k : Type u} [Field k] [PerfectField k] {R : Type*}
    [Zero R] {X Y T : Scheme.{u}} [IsLocallyNoetherian Y] (I : X.IdealSheafData) (f : Y ⟶ X)
    [IsLocallyNoetherian (pullback f I.subschemeι)]
    (sW : pullback f I.subschemeι ⟶ Spec (.of k)) [LocallyOfFiniteType sW] {s : Y ⟶ T}
    {D' : DivisorWithCoeffs R Y} (hD' : D'.IsSNC s) (𝔅 : Set (PrimeDivisor Y))
    (h𝔅 : ∀ G ∈ 𝔅, G ∈ D'.support)
    (hK : ∀ w : ↥(pullback f I.subschemeι), ∃ E ∈ D'.support,
      pullback.fst f I.subschemeι w ∈ E.support ∧ E ∉ 𝔅 ∧
      IdealSheafData.stalk (I.comap f) (pullback.fst f I.subschemeι w) =
        IdealSheafData.stalk E.idealSheaf (pullback.fst f I.subschemeι w))
    (𝔉 : Finset (PrimeDivisor (pullback f I.subschemeι)))
    (h𝔉 : ∀ P ∈ 𝔉, ∃ G ∈ 𝔅, ∃ x, P.support =
      connectedComponentIn (pullback.fst f I.subschemeι ⁻¹' G.idealSheaf.support) x) :
    DivisorWithCoeffs.IsSNC sW (∑ P ∈ 𝔉, Finsupp.single P (1 : ℤ)) := by
  classical
  set p := pullback.fst f I.subschemeι
  have hFG : ∀ (G : PrimeDivisor Y), G ∈ 𝔅 → ∀ w, w ∈ p ⁻¹' G.idealSheaf.support →
      ∃ (m : ℕ) (z : Fin m → (pullback f I.subschemeι).presheaf.stalk w) (j : Fin m),
        IsRegularSystemOfParameters z ∧
        IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal
          ⟨p ⁻¹' G.idealSheaf.support, G.idealSheaf.support.isClosed.preimage p.continuous⟩) w =
          Ideal.span {z j} := by
    intro G hG w hw
    refine exists_isRegularSystemOfParameters_stalk_vanishingIdeal_preimage I f hD' 𝔅 hK (h𝔅 G hG)
      hG w ?_
    rwa [← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  unfold DivisorWithCoeffs.IsSNC
  rw [support_sum_single]
  refine ⟨fun P hP => ?_, fun w => ?_⟩
  · obtain ⟨G, hG, x, hPx⟩ := h𝔉 P hP
    refine MMP.Resolution.isSmoothScheme_subscheme_of_stalk_eq_span_parameter sW P.idealSheaf
      fun w hw => ?_
    have hwG : w ∈ p ⁻¹' G.idealSheaf.support :=
      connectedComponentIn_subset _ _ (by rwa [← hPx])
    obtain ⟨m, z, j, hz, hst⟩ := hFG G hG w hwG
    have := isRegularLocalRing_of_isRegularSystemOfParameters hz
    exact ⟨m, z, j, hz, stalk_idealSheaf_eq_of_support_eq_connectedComponentIn
      ⟨p ⁻¹' G.idealSheaf.support, G.idealSheaf.support.isClosed.preimage p.continuous⟩
      (MMP.Resolution.isPrime_span_singleton_of_isRegularSystemOfParameters hz j) hst P hPx hw⟩
  · obtain ⟨E, hE, hyE, hE𝔅, hJ⟩ := hK w
    obtain ⟨n, z, κ, hz, hκinj, hκ⟩ := exists_coordinates_pullback I f hD' w hE hyE hJ
    have := isRegularLocalRing_of_isRegularSystemOfParameters hz
    choose G hG x hx using h𝔉
    have hwG : ∀ P : {P // P ∈ 𝔉 ∧ w ∈ P.support}, w ∈ p ⁻¹' (G P.1 P.2.1).idealSheaf.support :=
      fun P => connectedComponentIn_subset _ _ (hx P.1 P.2.1 ▸ P.2.2)
    have hne : ∀ P : {P // P ∈ 𝔉 ∧ w ∈ P.support}, G P.1 P.2.1 ≠ E :=
      fun P h => hE𝔅 (h ▸ hG P.1 P.2.1)
    let j : {P // P ∈ 𝔉 ∧ w ∈ P.support} → Fin n := fun P =>
      κ ⟨G P.1 P.2.1, h𝔅 _ (hG P.1 P.2.1), hwG P, hne P⟩
    refine ⟨n, z, j, hz, ?_, fun P => ?_⟩
    · intro P P' hPP'
      have h1 := hκinj hPP'
      have hGG : G P.1 P.2.1 = G P'.1 P'.2.1 := Subtype.mk.inj h1
      apply Subtype.ext
      apply AlgebraicGeometry.PrimeDivisor.eq_of_support_eq
      rw [hx P.1 P.2.1, hx P'.1 P'.2.1]
      have e1 := connectedComponentIn_eq (hx P.1 P.2.1 ▸ P.2.2)
      have e2 := connectedComponentIn_eq (hx P'.1 P'.2.1 ▸ P'.2.2)
      rw [e1, e2, hGG]
    · exact stalk_idealSheaf_eq_of_support_eq_connectedComponentIn
        ⟨p ⁻¹' (G P.1 P.2.1).idealSheaf.support,
          (G P.1 P.2.1).idealSheaf.support.isClosed.preimage p.continuous⟩
        (MMP.Resolution.isPrime_span_singleton_of_isRegularSystemOfParameters hz (j P))
        (hκ ⟨G P.1 P.2.1, h𝔅 _ (hG P.1 P.2.1), hwG P, hne P⟩) P.1 (hx P.1 P.2.1) P.2.2

/-- A closed set covered by the preimages of finitely many prime divisors, whose connected
components are prime divisors, is of pure codimension one. -/
private theorem isPureCodimOne_of_subset_union {W Y : Scheme.{u}} (p : W ⟶ Y) (S : Closeds W)
    (Ex : Finset (PrimeDivisor Y))
    (hS : ∀ w, w ∈ (S : Set W) ↔ ∃ E ∈ Ex, p w ∈ E.support)
    (hcomp : ∀ E ∈ Ex, ∀ w ∈ p ⁻¹' E.support, ∃ P : PrimeDivisor W,
      P.support = connectedComponentIn (p ⁻¹' E.support) w) :
    IsPureCodimOne S := by
  intro W' hW'
  set η := W'.isIrreducible.genericPoint
  have hgen := W'.isIrreducible.isGenericPoint_genericPoint_closure
  rw [W'.isClosed.closure_eq] at hgen
  have hηS : η ∈ (S : Set W) := hW'.prop hgen.mem
  obtain ⟨E, hE, hηE⟩ := (hS η).mp hηS
  obtain ⟨P, hP⟩ := hcomp E hE η hηE
  have hPS : P.support ⊆ (S : Set W) := fun w hw =>
    (hS w).mpr ⟨E, hE,
      (connectedComponentIn_subset (p ⁻¹' E.support) η (hP ▸ hw) : w ∈ p ⁻¹' E.support)⟩
  have hW'P : (W' : Set W) ⊆ P.support := by
    rw [← hgen.def, hP]
    refine closure_minimal (Set.singleton_subset_iff.mpr (mem_connectedComponentIn hηE)) ?_
    rw [← hP]; exact P.idealSheaf.support.isClosed
  exact MMP.Resolution.isPureCodimOne_support_primeDivisor P W'
    ⟨hW'P, fun W'' hW'' hle => hW'.2 (hW''.trans hPS) hle⟩

/-- A scheme smooth over a field is reduced. -/
private theorem isReduced_of_isSmoothScheme {k : Type u} [Field k] {W : Scheme.{u}}
    (sW : W ⟶ Spec (.of k)) (h : IsSmoothScheme sW) : IsReduced W := by
  have : Smooth sW := h.smooth
  have hst (w : W) : _root_.IsReduced (W.presheaf.stalk w) := by
    haveI := isRegularLocalRing_stalk_of_smooth_over_field sW w
    haveI : IsDomain (W.presheaf.stalk w) := IsRegularLocalRing.isDomain _
    exact @isReduced_of_noZeroDivisors _ _ (IsDomain.to_noZeroDivisors _)
  exact isReduced_of_isReduced_stalk W

/-- A component of a transformed divisor is the transform of a component. -/
private theorem exists_of_mem_support_mapPrimeDivisors {X Y : Scheme.{u}} {R : Type*}
    [AddCommMonoid R] (φ : PrimeDivisor X → Option (PrimeDivisor Y))
    (D : DivisorWithCoeffs R X) (F : PrimeDivisor Y)
    (hF : F ∈ (DivisorWithCoeffs.mapPrimeDivisors φ D).support) :
    ∃ D' ∈ D.support, φ D' = some F := by
  classical
  rw [DivisorWithCoeffs.mapPrimeDivisors, Finsupp.liftAddHom_apply, Finsupp.sum] at hF
  obtain ⟨D', hD', hF'⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hF)
  refine ⟨D', hD', ?_⟩
  cases h : φ D' with
  | none => simp [h] at hF'
  | some G =>
    simp only [h, Option.elim_some, Finsupp.singleAddHom_apply] at hF'
    have := Finsupp.support_single_subset hF'
    simp only [Finset.mem_singleton] at this
    rw [this]

open Classical in
/-- A component of the restriction of `Δ` lies on a component of `Δ`. -/
private theorem exists_mem_support_of_coeff_restrictComponents_ne_zero {X S : Scheme.{u}}
    (ι : S ⟶ X) (Δ : QDivisor X) {C : PrimeDivisor S}
    (hC : (Δ.restrictComponents ι).coeff C ≠ 0) :
    ∃ E ∈ Δ.support, ι (AlgebraicGeometry.PrimeDivisor.genericPoint C) ∈ E.support := by
  by_cases h : (Function.support (DivisorWithCoeffs.restrictComponentsCoeff ι Δ)).Finite
  · rw [DivisorWithCoeffs.coeff_restrictComponents ι h C, Finsupp.sum] at hC
    obtain ⟨E, hE, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hC
    refine ⟨E, hE, ?_⟩
    by_contra hn
    exact hne (if_neg hn)
  · exfalso
    apply hC
    rw [DivisorWithCoeffs.restrictComponents, dif_neg h]
    rfl

/-- A prime divisor meeting the biregular locus has a prime inverse transform, whose generic point
maps to its generic point. -/
private theorem inverseTransformPrimeDivisor_eq_some_of_mem_biregularLocus {A B : Scheme.{u}}
    (h : A ⟶ B) (D : PrimeDivisor B)
    (hD : AlgebraicGeometry.PrimeDivisor.genericPoint D ∈ biregularLocus h) :
    ∃ F : PrimeDivisor A, inverseTransformPrimeDivisor h D = some F ∧
      h (AlgebraicGeometry.PrimeDivisor.genericPoint F) =
        AlgebraicGeometry.PrimeDivisor.genericPoint D := by
  set V := biregularLocus h
  have : IsIso (h ∣_ V) := isBiregular_biregularLocus h
  set φ := (h ∣_ V).homeomorph
  set a' := φ.symm ⟨AlgebraicGeometry.PrimeDivisor.genericPoint D, hD⟩
  set a : A := a'.1
  have hφ : ∀ x : (h ⁻¹ᵁ V).toScheme, (φ x).1 = h x.1 := fun x =>
    (morphismRestrict_base_coe h V x)
  have ha : h a = AlgebraicGeometry.PrimeDivisor.genericPoint D := by
    have h1 := hφ a'
    have h2 : φ a' = ⟨AlgebraicGeometry.PrimeDivisor.genericPoint D, hD⟩ := φ.apply_symm_apply _
    rw [h2] at h1
    exact h1.symm
  have haV : h a ∈ V := ha ▸ hD
  have hcoh : Order.coheight a = 1 := by
    rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus h haV, ha,
      AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]
  set F := AlgebraicGeometry.PrimeDivisor.ofCoheightOne a hcoh
  have hFg : AlgebraicGeometry.PrimeDivisor.genericPoint F = a :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne a hcoh
  refine ⟨F, ?_, by rw [hFg, ha]⟩
  rw [inverseTransformPrimeDivisor_eq_some_iff]
  refine ⟨⟨_, MMP.Flips.primeDivisor_genericPoint_mem_support D, hD⟩, ?_⟩
  rw [← MMP.Intersection.vanishingIdeal_support_idealSheaf, inverseTransformIdeal]
  congr 1
  apply Closeds.ext
  change F.support = closure (h ⁻¹' ((D.support : Set B) ∩ V))
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, hFg]
  apply le_antisymm
  · exact closure_mono (Set.singleton_subset_iff.mpr
      ⟨ha ▸ MMP.Flips.primeDivisor_genericPoint_mem_support D, haV⟩)
  · refine closure_minimal ?_ isClosed_closure
    rintro y ⟨hyD, hyV⟩
    have hsp : (⟨AlgebraicGeometry.PrimeDivisor.genericPoint D, hD⟩ : V) ⤳ ⟨h y, hyV⟩ := by
      rw [← Topology.IsInducing.subtypeVal.specializes_iff]
      exact MMP.Resolution.Aux.genericPoint_specializes_of_mem_support D hyD
    have hsp' := hsp.map φ.symm.continuous
    have hy' : φ.symm ⟨h y, hyV⟩ = ⟨y, hyV⟩ :=
      φ.symm_apply_eq.mpr (Subtype.ext (hφ ⟨y, hyV⟩).symm)
    rw [hy'] at hsp'
    exact specializes_iff_mem_closure.mp (hsp'.map continuous_subtype_val)

/-- If the inverse transform of `D` is the prime divisor `F`, the generic point of `D` is biregular
and is the image of that of `F`. -/
private theorem genericPoint_mem_biregularLocus_of_inverseTransformPrimeDivisor_eq_some
    {A B : Scheme.{u}}
    {h : A ⟶ B} {D : PrimeDivisor B} {F : PrimeDivisor A}
    (hF : inverseTransformPrimeDivisor h D = some F) :
    AlgebraicGeometry.PrimeDivisor.genericPoint D ∈ biregularLocus h ∧
      h (AlgebraicGeometry.PrimeDivisor.genericPoint F) =
        AlgebraicGeometry.PrimeDivisor.genericPoint D := by
  obtain ⟨⟨x, hxD, hxV⟩, -⟩ := inverseTransformPrimeDivisor_eq_some_iff.mp hF
  have hη : AlgebraicGeometry.PrimeDivisor.genericPoint D ∈ biregularLocus h :=
    (MMP.Resolution.Aux.genericPoint_specializes_of_mem_support D hxD).mem_open
      (biregularLocus h).isOpen hxV
  obtain ⟨F', hF', hF'g⟩ := inverseTransformPrimeDivisor_eq_some_of_mem_biregularLocus h D hη
  rw [hF] at hF'
  cases hF'
  exact ⟨hη, hF'g⟩

/-- The inverse transform of a component of `Δ` meeting the biregular locus is a component of the
inverse transform of `Δ`. -/
private theorem mem_support_inverseTransformDivisor {A B : Scheme.{u}} (h : A ⟶ B) {R : Type*}
    [AddCommMonoid R] (Δ : DivisorWithCoeffs R B) {E : PrimeDivisor B} (hE : E ∈ Δ.support)
    {F : PrimeDivisor A} (hF : inverseTransformPrimeDivisor h E = some F) :
    F ∈ (inverseTransformDivisor h Δ).support := by
  classical
  have hEg := (genericPoint_mem_biregularLocus_of_inverseTransformPrimeDivisor_eq_some hF).2
  rw [Finsupp.mem_support_iff]
  change (DivisorWithCoeffs.mapPrimeDivisors (inverseTransformPrimeDivisor h) Δ) F ≠ 0
  rw [DivisorWithCoeffs.mapPrimeDivisors, Finsupp.liftAddHom_apply, Finsupp.sum,
    Finsupp.finsetSum_apply, Finset.sum_eq_single E]
  · rw [hF]
    simpa using Finsupp.mem_support_iff.mp hE
  · intro D _ hDE
    cases hD : inverseTransformPrimeDivisor h D with
    | none => simp
    | some F' =>
      simp only [Option.elim_some, Finsupp.singleAddHom_apply]
      rw [Finsupp.single_apply, if_neg]
      rintro rfl
      have hDg := (genericPoint_mem_biregularLocus_of_inverseTransformPrimeDivisor_eq_some hD).2
      apply hDE
      apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      rw [← hDg, ← hEg]
  · exact fun hE' => absurd hE hE'

/-- At a point of the support of `⨅ F ∈ T, F.idealSheaf`, where the members of `T` have pairwise
disjoint supports, the stalk is that of the unique member through the point. -/
theorem exists_mem_support_stalk_iInf_eq {W : Scheme.{u}} [IsLocallyNoetherian W]
    (T : Finset (PrimeDivisor W))
    (honly : ∀ P ∈ T, ∀ P' ∈ T, ∀ w, w ∈ P.support → w ∈ P'.support → P = P')
    {w : W} (hw : w ∈ (⨅ F ∈ T, F.idealSheaf).support) :
    ∃ P ∈ T, w ∈ P.support ∧ IdealSheafData.stalk (⨅ F ∈ T, F.idealSheaf) w =
      IdealSheafData.stalk P.idealSheaf w := by
  have hstK : IdealSheafData.stalk (⨅ F ∈ T, F.idealSheaf) w =
      T.inf fun F => IdealSheafData.stalk F.idealSheaf w := by
    rw [← Finset.inf_eq_iInf, MMP.Intersection.stalk_finsetInf]
  obtain ⟨P, hP, hwP⟩ : ∃ P ∈ T, w ∈ P.support := by
    by_contra hno
    simp only [not_exists, not_and] at hno
    have htop : IdealSheafData.stalk (⨅ F ∈ T, F.idealSheaf) w = ⊤ := by
      rw [hstK, Finset.inf_eq_top_iff]
      exact fun P hP => MMP.Intersection.stalk_idealSheaf_eq_top_of_notMem_support P (hno P hP)
    exact ((IdealSheafData.stalk_eq_top_iff_notMem_support _ w).mp htop) hw
  refine ⟨P, hP, hwP, ?_⟩
  rw [hstK]
  refine le_antisymm (Finset.inf_le hP) (Finset.le_inf fun P' hP' => ?_)
  by_cases hwP' : w ∈ P'.support
  · rw [honly P hP P' hP' w hwP hwP']
  · rw [MMP.Intersection.stalk_idealSheaf_eq_top_of_notMem_support P' hwP']
    exact le_top

open Classical in
/-- The restriction step of Kollár–Mori 5.17: once a member `(σ)₀` of the free system is such
that `f` maps no generic point of `Y` into it and `f^*(σ)₀ + ∑ F` (over the components of
`f⁻¹_* Δ` and the `f`-exceptional prime divisors) is a reduced snc divisor, the base change of
`f` to each connected component of `Supp (σ)₀` is a log resolution with the expected
exceptional divisors and smooth birational transform of the boundary. -/
private theorem isLogResolution_pullback_snd_vanishingIdeal_of_isSNC {k : Type u} [Field k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsLocallyNoetherian Y] [IsNormal Y]
    [CharZero k]
    {Δ : QDivisor X} (hΔ : IsPair sX Δ) {f : Y ⟶ X}
    (hf : IsLogResolution sX (QDivisor.toRDivisor Δ) f) (Ex : Finset (PrimeDivisor Y))
    (hEx : ∀ F : PrimeDivisor Y, F ∈ Ex ↔ RationalMap.IsExceptional f.toRationalMap F)
    (hsm : IsSmoothScheme
      ((⨅ F ∈ (inverseTransformDivisor f Δ).support, F.idealSheaf).subschemeι ≫ f ≫ sX))
    {H : Divisor X} {ι : Type*} (s : ι → H.divisorialSubmodule ⊤)
    (hs : ∀ x : X, ∃ (i : ι) (hi : s i ≠ 0), x ∉ (H.zeroDivisor (s i) hi).supp)
    (σ : H.divisorialSubmodule ⊤) (hσ : σ ≠ 0)
    (hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉
      (H.zeroDivisor σ hσ).supp) (H' : Divisor Y)
    (hpb : (H.zeroDivisor σ hσ).IsPullback f hB H')
    (h01 : ∀ F : PrimeDivisor Y,
      (H' + ∑ F ∈ (inverseTransformDivisor f Δ).support ∪ Ex,
        Finsupp.single F (1 : ℤ)).coeff F = 0 ∨
      (H' + ∑ F ∈ (inverseTransformDivisor f Δ).support ∪ Ex,
        Finsupp.single F (1 : ℤ)).coeff F = 1)
    (hsnc : DivisorWithCoeffs.IsSNC (f ≫ sX)
      (H' + ∑ F ∈ (inverseTransformDivisor f Δ).support ∪ Ex, Finsupp.single F (1 : ℤ)))
    (hdisj : ∀ E ∈ H'.support, ∀ E' ∈ H'.support, E ≠ E' → Disjoint E.support E'.support)
    (Z : Closeds X) (x₀ : X)
    (hZ : connectedComponentIn ((H.zeroDivisor σ hσ).supp : Set X) x₀ = (Z : Set X)) :
    IsLogResolution ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ sX)
          (QDivisor.toRDivisor (Δ.restrictComponents
            (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι))
          (pullback.snd f (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι) ∧
        (∀ F : PrimeDivisor (pullback f (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι),
          RationalMap.IsExceptional
              (pullback.snd f (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι).toRationalMap
              F ↔
            ∃ E ∈ Ex, Maximal (fun T ↦ IsIrreducible T ∧ T ⊆
              pullback.fst f (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ⁻¹'
                E.support) F.support) ∧
        (∀ E ∈ Ex, ∀ C, Maximal (fun T ↦ IsIrreducible T ∧ T ⊆
            pullback.fst f (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ⁻¹'
              E.support) C →
          ∃ F : PrimeDivisor (pullback f (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι),
            F.support = C) ∧
        IsSmoothScheme
          ((⨅ F ∈ (inverseTransformDivisor
              (pullback.snd f (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι)
              (Δ.restrictComponents
                (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι)).support,
              F.idealSheaf).subschemeι ≫
            pullback.snd f (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫
            (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ sX) := by
  set D := H.zeroDivisor σ hσ
  set I := Scheme.IdealSheafData.vanishingIdeal Z
  set 𝔅 := (inverseTransformDivisor f Δ).support ∪ Ex
  set D' : Divisor Y := H' + ∑ F ∈ 𝔅, Finsupp.single F (1 : ℤ) with hD'def
  have hXnv : IsNormalVariety k sX := hΔ.isNormalVariety
  have := hXnv.1.toIsSeparated
  have := hXnv.1.toLocallyOfFiniteType
  have : IsProper f := hf.isProper
  have : IsIntegral Y := isIntegral_of_isBirationalMorphism hf.isBirationalMorphism
  have hYvar : MMP.Mori.IsVariety k (f ≫ sX) := isVariety_comp_of_isProper hXnv.1 f
  have : LocallyOfFiniteType (f ≫ sX) := hYvar.toLocallyOfFiniteType
  have hsmY : IsSmoothScheme (f ≫ sX) := hf.isSmoothScheme
  have hUFD := uniqueFactorizationMonoid_stalk_of_isSmoothScheme' (f ≫ sX) hsmY
  have hA := fun x hx => not_subsingleton_fiber_of_notMem_biregularLocus hXnv f hYvar
    hf.isBirationalMorphism (x := x) hx
  have hD0 : 0 ≤ D := Divisor.zeroDivisor_nonneg H σ hσ
  have hDc : D.IsCartier := isCartier_zeroDivisor s hs σ hσ
  have hH'nn : ∀ E, 0 ≤ H'.coeff E := coeff_nonneg_of_isPullback hD0 hDc hpb
  have hH'1 : ∀ E ∈ H'.support, H'.coeff E = 1 ∧ E ∉ 𝔅 := fun E hE =>
    coeff_eq_one_and_notMem_of_mem_support hH'nn 𝔅 h01 hE
  have hD'mem : ∀ E ∈ H'.support, E ∈ D'.support := by
    intro E hE
    rw [Finsupp.mem_support_iff]
    change DivisorWithCoeffs.coeff D' E ≠ 0
    rw [hD'def, DivisorWithCoeffs.coeff_add, coeff_sum_single, if_neg (hH'1 E hE).2, add_zero,
      (hH'1 E hE).1]
    exact one_ne_zero
  have hD'mem𝔅 : ∀ E ∈ 𝔅, E ∈ D'.support := by
    intro E hE
    rw [Finsupp.mem_support_iff]
    change DivisorWithCoeffs.coeff D' E ≠ 0
    have h0 : H'.coeff E = 0 := by
      by_contra hne
      exact (hH'1 E (Finsupp.mem_support_iff.mpr hne)).2 hE
    rw [hD'def, DivisorWithCoeffs.coeff_add, coeff_sum_single, if_pos hE, h0]
    exact one_ne_zero
  have hgen : ∀ E ∈ H'.support, ∀ y ∈ E.support, ∃ π : Y.presheaf.stalk y, π ≠ 0 ∧
      IdealSheafData.stalk E.idealSheaf y = Ideal.span {π} := by
    intro E hE y hy
    obtain ⟨n, z, m, hz, hI⟩ := exists_isRegularSystemOfParameters_of_isSNC hsnc (hD'mem E hE) hy
    have := isRegularLocalRing_of_isRegularSystemOfParameters hz
    exact ⟨z m, MMP.Resolution.ne_zero_of_isRegularSystemOfParameters hz m, hI⟩
  have hK : ∀ y : Y, f y ∈ (Z : Set X) → ∃ E ∈ H'.support, y ∈ E.support ∧
      E.support ⊆ f ⁻¹' Z ∧ IdealSheafData.stalk (I.comap f) y =
        IdealSheafData.stalk E.idealSheaf y := fun y hy =>
    exists_stalk_comap_vanishingIdeal_eq (f ≫ sX) hsmY hUFD hD0 hDc hpb
      (fun E hE => (hH'1 E hE).1) hdisj hgen hZ hy
  -- the base change
  have hιrange : Set.range I.subschemeι = (Z : Set X) := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  have hpZ : ∀ w : ↥(pullback f I.subschemeι),
      f (pullback.fst f I.subschemeι w) ∈ (Z : Set X) := fun w => by
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, ← hιrange]
    exact ⟨_, rfl⟩
  have hKw : ∀ w : ↥(pullback f I.subschemeι), ∃ E ∈ D'.support,
      pullback.fst f I.subschemeι w ∈ E.support ∧ E ∉ (𝔅 : Set (PrimeDivisor Y)) ∧
      IdealSheafData.stalk (I.comap f) (pullback.fst f I.subschemeι w) =
        IdealSheafData.stalk E.idealSheaf (pullback.fst f I.subschemeι w) := by
    intro w
    obtain ⟨E, hE, hwE, -, hst⟩ := hK _ (hpZ w)
    exact ⟨E, hD'mem E hE, hwE, (hH'1 E hE).2, hst⟩
  have : IsLocallyNoetherian (pullback f I.subschemeι) :=
    isLocallyNoetherian_of_isClosedImmersion (pullback.fst f I.subschemeι)
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian Y := {}
  have : NoetherianSpace ↥(pullback f I.subschemeι) :=
    (pullback.fst f I.subschemeι).isClosedEmbedding.isEmbedding.noetherianSpace
  have : LocallyOfFiniteType (pullback.snd f I.subschemeι ≫ I.subschemeι ≫ sX) := by
    rw [← Category.assoc, ← pullback.condition, Category.assoc]; infer_instance
  have hJ : ∀ y ∈ (I.comap f).support, ∃ (m : ℕ) (w : Fin m → Y.presheaf.stalk y) (j : Fin m),
      IsRegularSystemOfParameters w ∧ IdealSheafData.stalk (I.comap f) y = Ideal.span {w j} := by
    intro y hy
    rw [Scheme.IdealSheafData.support_comap] at hy
    have hy' : f y ∈ (Z : Set X) := by
      have : f y ∈ (I.support : Set X) := hy
      rwa [Scheme.IdealSheafData.coe_support_vanishingIdeal] at this
    obtain ⟨E, hE, hyE, -, hst⟩ := hK y hy'
    obtain ⟨n, z, m, hz, hI⟩ := exists_isRegularSystemOfParameters_of_isSNC hsnc (hD'mem E hE) hyE
    exact ⟨n, z, m, hz, hst.trans hI⟩
  have hsmW : IsSmoothScheme (pullback.snd f I.subschemeι ≫ I.subschemeι ≫ sX) :=
    isSmoothScheme_pullback_snd I f sX hJ
  -- the exceptional set of the base change
  have hExset : ∀ w : ↥(pullback f I.subschemeι),
      w ∈ (exceptionalSet (pullback.snd f I.subschemeι) : Set _) ↔
        ∃ E ∈ Ex, pullback.fst f I.subschemeι w ∈ E.support := by
    intro w
    rw [SetLike.mem_coe, mem_exceptionalSet_pullback_snd_iff f I.subschemeι hA w]
    exact ⟨exists_mem_of_mem_exceptionalSet hXnv hf hYvar Ex hEx, fun ⟨E, hE, hwE⟩ =>
      MMP.Positivity.support_subset_exceptionalSet E ((hEx E).mp hE) hwE⟩
  -- components of the preimages of the boundary components
  have hcompG : ∀ G ∈ 𝔅, ∀ w ∈ pullback.fst f I.subschemeι ⁻¹' G.support,
      IsIrreducible (connectedComponentIn (pullback.fst f I.subschemeι ⁻¹' G.support) w) ∧
      ∃ P : PrimeDivisor (pullback f I.subschemeι),
        P.support = connectedComponentIn (pullback.fst f I.subschemeι ⁻¹' G.support) w := by
    intro G hG w hw
    have hD := exists_isRegularSystemOfParameters_stalk_vanishingIdeal_preimage I f hsnc
      (𝔅 : Set (PrimeDivisor Y)) hKw (hD'mem𝔅 G hG) hG
    have hw' : w ∈ ((Scheme.IdealSheafData.vanishingIdeal
        ⟨pullback.fst f I.subschemeι ⁻¹' G.idealSheaf.support,
          G.idealSheaf.support.isClosed.preimage
            (pullback.fst f I.subschemeι).continuous⟩).support : Set _) := by
      rwa [Scheme.IdealSheafData.coe_support_vanishingIdeal]
    have h1 :=
      isIrreducible_connectedComponentIn_support_of_stalk_eq_span_parameter _ hD hw'
    have h2 := MMP.Mori.exists_primeDivisor_support_eq_connectedComponentIn _ hD hw'
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal] at h1 h2
    exact ⟨h1, h2⟩
  have hpure : IsPureCodimOne (exceptionalSet (pullback.snd f I.subschemeι)) :=
    isPureCodimOne_of_subset_union (pullback.fst f I.subschemeι) _ Ex hExset
      fun E hE w hw => (hcompG E (Finset.mem_union_right _ hE) w hw).2
  -- birationality
  have hZD : (Z : Set X) ⊆ D.supp := hZ ▸ connectedComponentIn_subset _ _
  have hcc : ∀ x ∈ (Z : Set X), connectedComponentIn (D.supp : Set X) x = Z := fun x hx => by
    rw [← hZ]
    exact (connectedComponentIn_eq (hZ ▸ hx)).symm
  have hηV : ∀ C : PrimeDivisor X,
      AlgebraicGeometry.PrimeDivisor.genericPoint C ∈ biregularLocus f :=
    fun C => MMP.Mori.mem_biregularLocus_of_ringKrullDim_stalk_le_one hXnv f hYvar
      hf.isBirationalMorphism (by
        rw [ringKrullDim_stalk_eq_coheight, AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]
        rfl)
  have hV'dense : Dense ((I.subschemeι ⁻¹ᵁ biregularLocus f : Opens _) : Set I.subscheme) := by
    refine dense_of_forall_exists_specializes fun t => ?_
    have htZ : I.subschemeι t ∈ (Z : Set X) := hιrange ▸ ⟨t, rfl⟩
    obtain ⟨C, hC, htC⟩ := DivisorWithCoeffs.mem_supp_iff.mp (hZD htZ)
    have hCZ : C.support ⊆ (Z : Set X) := by
      have hirr : IsIrreducible C.support := by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact isIrreducible_singleton.closure
      have := (IsIrreducible.isConnected hirr).isPreconnected.subset_connectedComponentIn htC
        (fun y hy => DivisorWithCoeffs.support_subset_supp hC hy)
      rwa [hcc _ htZ] at this
    obtain ⟨t', ht'⟩ : AlgebraicGeometry.PrimeDivisor.genericPoint C ∈ Set.range I.subschemeι :=
      hιrange ▸ hCZ (MMP.Flips.primeDivisor_genericPoint_mem_support C)
    refine ⟨t', ?_, ?_⟩
    · change I.subschemeι t' ∈ biregularLocus f
      rw [ht']
      exact hηV C
    · rw [← I.subschemeι.isClosedEmbedding.isInducing.specializes_iff, ht']
      exact MMP.Resolution.Aux.genericPoint_specializes_of_mem_support C htC
  have hUdense : Dense ((pullback.snd f I.subschemeι ⁻¹ᵁ
      (I.subschemeι ⁻¹ᵁ biregularLocus f) : Opens _) : Set ↥(pullback f I.subschemeι)) := by
    refine dense_of_forall_exists_specializes fun w => ?_
    obtain ⟨E, hE, hwE, hEZ, -⟩ := hK _ (hpZ w)
    obtain ⟨w', hw'⟩ : AlgebraicGeometry.PrimeDivisor.genericPoint E ∈
        Set.range (pullback.fst f I.subschemeι) := by
      rw [Scheme.Pullback.range_fst, hιrange]
      exact hEZ (MMP.Flips.primeDivisor_genericPoint_mem_support E)
    refine ⟨w', ?_, ?_⟩
    · change I.subschemeι (pullback.snd f I.subschemeι w') ∈ biregularLocus f
      rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply, hw']
      by_contra hη
      obtain ⟨E', hE', hηE'⟩ := exists_mem_of_mem_exceptionalSet hXnv hf hYvar Ex hEx
        (y := AlgebraicGeometry.PrimeDivisor.genericPoint E) hη
      have := eq_of_genericPoint_mem_support hηE'
      exact (hH'1 E hE).2 (Finset.mem_union_right _ (this ▸ hE'))
    · rw [← (pullback.fst f I.subschemeι).isClosedEmbedding.isInducing.specializes_iff, hw']
      exact MMP.Resolution.Aux.genericPoint_specializes_of_mem_support E hwE
  have : IsIso (pullback.snd f I.subschemeι ∣_ (I.subschemeι ⁻¹ᵁ biregularLocus f)) :=
    isBiregular_pullback_snd f I.subschemeι
  have hbir : IsBirationalMorphism (pullback.snd f I.subschemeι) :=
    isBirationalMorphism_of_isIso_morphismRestrict _ _ hV'dense hUdense
  -- the exceptional divisors of the base change
  have : AlgebraicGeometry.IsReduced (pullback f I.subschemeι) := isReduced_of_isSmoothScheme _ hsmW
  have : IsSeparated (I.subscheme ↘ ⊤_ Scheme) :=
    isSeparated_terminal_of_isSeparated (I.subschemeι ≫ sX)
  have : IsSeparated (X ↘ ⊤_ Scheme) := isSeparated_terminal_of_isSeparated sX
  have hirrE : ∀ E ∈ Ex, ∀ w ∈ pullback.fst f I.subschemeι ⁻¹' E.support,
      IsIrreducible (connectedComponentIn (pullback.fst f I.subschemeι ⁻¹' E.support) w) :=
    fun E hE w hw => (hcompG E (Finset.mem_union_right _ hE) w hw).1
  have hconj3 : ∀ E ∈ Ex, ∀ C, Maximal (fun T ↦ IsIrreducible T ∧ T ⊆
      pullback.fst f I.subschemeι ⁻¹' E.support) C →
      ∃ F : PrimeDivisor (pullback f I.subschemeι), F.support = C := by
    intro E hE C hC
    obtain ⟨x, hx, rfl⟩ := (maximal_isIrreducible_iff_connectedComponentIn (hirrE E hE) C).mp hC
    exact (hcompG E (Finset.mem_union_right _ hE) x hx).2
  have hconj2 : ∀ F : PrimeDivisor (pullback f I.subschemeι),
      RationalMap.IsExceptional (pullback.snd f I.subschemeι).toRationalMap F ↔
        ∃ E ∈ Ex, Maximal (fun T ↦ IsIrreducible T ∧ T ⊆
          pullback.fst f I.subschemeι ⁻¹' E.support) F.support := by
    intro F
    constructor
    · intro hF
      have hηF := MMP.Positivity.support_subset_exceptionalSet F hF
        (MMP.Flips.primeDivisor_genericPoint_mem_support F)
      obtain ⟨E, hE, hηE⟩ := (hExset _).mp hηF
      obtain ⟨P, hP⟩ := (hcompG E (Finset.mem_union_right _ hE) _ hηE).2
      obtain rfl : F = P :=
        eq_of_genericPoint_mem_support (by rw [hP]; exact mem_connectedComponentIn hηE)
      refine ⟨E, hE, ?_⟩
      rw [hP]
      exact (maximal_isIrreducible_iff_connectedComponentIn (hirrE E hE) _).mpr ⟨_, hηE, rfl⟩
    · rintro ⟨E, hE, hmax⟩
      rw [isExceptional_iff_two_le_coheight]
      refine two_le_coheight_subscheme_vanishingIdeal hD0 hDc hZ _ ?_
      have hpη : pullback.fst f I.subschemeι (AlgebraicGeometry.PrimeDivisor.genericPoint F) ∈
          E.support := hmax.prop.2
            (MMP.Flips.primeDivisor_genericPoint_mem_support F)
      rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]
      have hEc : 2 ≤ Order.coheight (f (AlgebraicGeometry.PrimeDivisor.genericPoint E)) :=
        (isExceptional_iff_two_le_coheight f E).mp ((hEx E).mp hE)
      have hsp : f (AlgebraicGeometry.PrimeDivisor.genericPoint E) ⤳
          f (pullback.fst f I.subschemeι (AlgebraicGeometry.PrimeDivisor.genericPoint F)) :=
        f.base.hom.map_specializes
          (MMP.Resolution.Aux.genericPoint_specializes_of_mem_support E hpη)
      have hne : f (pullback.fst f I.subschemeι (AlgebraicGeometry.PrimeDivisor.genericPoint F)) ≠
          f (AlgebraicGeometry.PrimeDivisor.genericPoint E) := by
        intro heq
        have hηZ : f (AlgebraicGeometry.PrimeDivisor.genericPoint E) ∈ (Z : Set X) :=
          heq ▸ hpZ _
        obtain ⟨E', hE', hηE', -, -⟩ := hK _ hηZ
        obtain rfl := eq_of_genericPoint_mem_support hηE'
        exact (hH'1 E hE').2 (Finset.mem_union_right _ hE)
      have := Order.coheight_add_one_le (MMP.Intersection.lt_of_specializes_of_ne hsp hne)
      calc (3 : ℕ∞) = 2 + 1 := rfl
        _ ≤ _ + 1 := add_le_add hEc le_rfl
        _ ≤ _ := this
  -- the transversal components of the boundary
  have hTC : ∀ (C : PrimeDivisor I.subscheme) (P : PrimeDivisor (pullback f I.subschemeι)),
      inverseTransformPrimeDivisor (pullback.snd f I.subschemeι) C = some P →
      (∃ E ∈ Δ.support, I.subschemeι (AlgebraicGeometry.PrimeDivisor.genericPoint C) ∈
        E.support) →
      ∃ G ∈ (inverseTransformDivisor f Δ).support, P.support = connectedComponentIn
        (pullback.fst f I.subschemeι ⁻¹' G.support)
          (AlgebraicGeometry.PrimeDivisor.genericPoint P) := by
    intro C P hP ⟨E, hE, hιE⟩
    obtain ⟨hηC, hgP⟩ := genericPoint_mem_biregularLocus_of_inverseTransformPrimeDivisor_eq_some hP
    have hPEx : pullback.fst f I.subschemeι (AlgebraicGeometry.PrimeDivisor.genericPoint P) ∉
        (exceptionalSet f : Set Y) := by
      intro h
      apply (mem_exceptionalSet_pullback_snd_iff f I.subschemeι hA _).mpr h
      change pullback.snd f I.subschemeι (AlgebraicGeometry.PrimeDivisor.genericPoint P) ∈
        biregularLocus (pullback.snd f I.subschemeι)
      rwa [hgP]
    have hfy : f (pullback.fst f I.subschemeι (AlgebraicGeometry.PrimeDivisor.genericPoint P)) =
        I.subschemeι (AlgebraicGeometry.PrimeDivisor.genericPoint C) := by
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, hgP]
    obtain ⟨FE, hFE, -⟩ := inverseTransformPrimeDivisor_eq_some_of_mem_biregularLocus f E (hηV E)
    have hyFE : pullback.fst f I.subschemeι (AlgebraicGeometry.PrimeDivisor.genericPoint P) ∈
        FE.support := by
      rw [support_inverseTransformPrimeDivisor hFE]
      apply subset_closure
      refine ⟨?_, ?_⟩
      · change f _ ∈ E.support
        rwa [hfy]
      · exact not_not.mp (mt mem_exceptionalSet.mpr hPEx)
    have hFEs := mem_support_inverseTransformDivisor f Δ hE hFE
    refine ⟨FE, hFEs, ?_⟩
    obtain ⟨-, Q, hQ⟩ := hcompG FE (Finset.mem_union_left _ hFEs) _ hyFE
    obtain rfl : P = Q :=
      eq_of_genericPoint_mem_support (by rw [hQ]; exact mem_connectedComponentIn hyFE)
    exact hQ
  -- the components of the boundary preimages have no generic points of components of `W`
  have hT0 : ∀ w ∈ (⋃ G ∈ 𝔅, pullback.fst f I.subschemeι ⁻¹' G.support), Order.coheight w ≠ 0 := by
    intro w hw h0
    simp only [Set.mem_iUnion] at hw
    obtain ⟨G, hG, hwG⟩ := hw
    obtain ⟨-, Q, hQ⟩ := hcompG G hG w hwG
    have hwQ : w ∈ Q.support := hQ ▸ mem_connectedComponentIn hwG
    have hle : w ≤ AlgebraicGeometry.PrimeDivisor.genericPoint Q :=
      Scheme.le_iff_specializes.mpr
        (MMP.Resolution.Aux.genericPoint_specializes_of_mem_support Q hwQ)
    have := Order.coheight_anti hle
    rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint, h0] at this
    exact absurd this (by decide)
  have hTcl : IsClosed (⋃ G ∈ 𝔅, pullback.fst f I.subschemeι ⁻¹' G.support) :=
    𝔅.finite_toSet.isClosed_biUnion fun G _ =>
      G.idealSheaf.support.isClosed.preimage (pullback.fst f I.subschemeι).continuous
  have hsuppZ : ∀ t : I.subscheme, t ∈ (QDivisor.toRDivisor
      (Δ.restrictComponents I.subschemeι)).supp ↔ ∃ C : PrimeDivisor I.subscheme,
        (Δ.restrictComponents I.subschemeι).coeff C ≠ 0 ∧ t ∈ C.support := by
    intro t
    rw [QDivisor.supp_toRDivisor, DivisorWithCoeffs.mem_supp_iff]
  -- the snc subset
  have hsnc' : IsSNCSubset (pullback.snd f I.subschemeι ≫ I.subschemeι ≫ sX)
      (exceptionalSet (pullback.snd f I.subschemeι) ⊔ (QDivisor.toRDivisor
        (Δ.restrictComponents I.subschemeι)).supp.preimage
          (pullback.snd f I.subschemeι).continuous) := by
    set Sx := exceptionalSet (pullback.snd f I.subschemeι) ⊔ (QDivisor.toRDivisor
        (Δ.restrictComponents I.subschemeι)).supp.preimage
          (pullback.snd f I.subschemeι).continuous
    have hmemS : ∀ w, w ∈ (Sx : Set _) ↔
        w ∈ (exceptionalSet (pullback.snd f I.subschemeι) : Set _) ∨
          pullback.snd f I.subschemeι w ∈ (QDivisor.toRDivisor
            (Δ.restrictComponents I.subschemeι)).supp := fun w => Iff.rfl
    set 𝔉 : Set (PrimeDivisor (pullback f I.subschemeι)) :=
      {P | (∃ G ∈ (𝔅 : Set (PrimeDivisor Y)), ∃ x, P.support =
        connectedComponentIn (pullback.fst f I.subschemeι ⁻¹' G.idealSheaf.support) x) ∧
        P.support ⊆ (Sx : Set _)}
    have hfin : 𝔉.Finite := by
      refine (MMP.Mori.finite_setOf_genericPoint_mem hTcl hT0).subset fun P hP => ?_
      obtain ⟨⟨G, hG, x, hx⟩, -⟩ := hP
      have : AlgebraicGeometry.PrimeDivisor.genericPoint P ∈
          pullback.fst f I.subschemeι ⁻¹' G.support :=
        connectedComponentIn_subset _ _ (hx ▸ MMP.Flips.primeDivisor_genericPoint_mem_support P)
      exact Set.mem_iUnion₂.mpr ⟨G, hG, this⟩
    refine Or.inr ⟨hfin.toFinset, ?_, isSNC_sum_of_connectedComponents I f _ hsnc
      (𝔅 : Set (PrimeDivisor Y)) hD'mem𝔅 hKw _ fun P hP => (hfin.mem_toFinset.mp hP).1⟩
    ext w
    simp only [Set.mem_iUnion, Set.Finite.mem_toFinset, exists_prop]
    constructor
    · exact fun ⟨_, ⟨_, hPS⟩, hwP⟩ => hPS hwP
    · intro hw
      by_cases hwEx : w ∈ (exceptionalSet (pullback.snd f I.subschemeι) : Set _)
      · obtain ⟨E, hE, hwE⟩ := (hExset w).mp hwEx
        obtain ⟨-, Q, hQ⟩ := hcompG E (Finset.mem_union_right _ hE) w hwE
        refine ⟨Q, ⟨⟨E, Finset.mem_union_right _ hE, w, hQ⟩, fun w' hw' => ?_⟩,
          hQ ▸ mem_connectedComponentIn hwE⟩
        exact (hmemS w').mpr (Or.inl ((hExset w').mpr ⟨E, hE, (connectedComponentIn_subset
          (pullback.fst f I.subschemeι ⁻¹' E.support) w (hQ ▸ hw') :
            w' ∈ pullback.fst f I.subschemeι ⁻¹' E.support)⟩))
      · have hw' := ((hmemS w).mp hw).resolve_left hwEx
        obtain ⟨C, hC, hwC⟩ := (hsuppZ _).mp hw'
        obtain ⟨E, hE, hιE⟩ := exists_mem_support_of_coeff_restrictComponents_ne_zero _ Δ hC
        have hgV : pullback.snd f I.subschemeι w ∈ biregularLocus (pullback.snd f I.subschemeι) :=
          not_not.mp (mt mem_exceptionalSet.mpr hwEx)
        have hηC : AlgebraicGeometry.PrimeDivisor.genericPoint C ∈
            biregularLocus (pullback.snd f I.subschemeι) :=
          (MMP.Resolution.Aux.genericPoint_specializes_of_mem_support C hwC).mem_open
            (biregularLocus _).isOpen hgV
        obtain ⟨P, hP, -⟩ :=
          inverseTransformPrimeDivisor_eq_some_of_mem_biregularLocus _ C hηC
        obtain ⟨G, hG, hPG⟩ := hTC C P hP ⟨E, hE, hιE⟩
        have hPs := support_inverseTransformPrimeDivisor hP
        have hPsub : P.support ⊆ (pullback.snd f I.subschemeι) ⁻¹' C.support := by
          rw [hPs]
          exact closure_minimal (fun w' hw' => hw'.1)
            (C.idealSheaf.support.isClosed.preimage (pullback.snd f I.subschemeι).continuous)
        refine ⟨P, ⟨⟨G, Finset.mem_union_left _ hG, _, hPG⟩, fun w' hw' => ?_⟩, ?_⟩
        · exact (hmemS w').mpr (Or.inr ((hsuppZ _).mpr ⟨C, hC, hPsub hw'⟩))
        · rw [hPs]
          exact subset_closure ⟨hwC, hgV⟩
  -- the birational transform of the restricted boundary is smooth
  have hdisjF := disjoint_of_isSmoothScheme_iInf (f ≫ sX) hsnc
    (T := (inverseTransformDivisor f Δ).support)
    (fun F hF => hD'mem𝔅 F (Finset.mem_union_left _ hF)) hsm
  have hdata : ∀ P ∈ (inverseTransformDivisor (pullback.snd f I.subschemeι)
      (Δ.restrictComponents I.subschemeι)).support,
      ∃ G ∈ (inverseTransformDivisor f Δ).support, P.support = connectedComponentIn
        (pullback.fst f I.subschemeι ⁻¹' G.support)
          (AlgebraicGeometry.PrimeDivisor.genericPoint P) := by
    intro P hP
    obtain ⟨C, hC, hCP⟩ := exists_of_mem_support_mapPrimeDivisors
      (inverseTransformPrimeDivisor (pullback.snd f I.subschemeι)) _ P hP
    exact hTC C P hCP (exists_mem_support_of_coeff_restrictComponents_ne_zero _ Δ
      (Finsupp.mem_support_iff.mp hC))
  have hconj4 : IsSmoothScheme
      ((⨅ F ∈ (inverseTransformDivisor (pullback.snd f I.subschemeι)
          (Δ.restrictComponents I.subschemeι)).support, F.idealSheaf).subschemeι ≫
        pullback.snd f I.subschemeι ≫ I.subschemeι ≫ sX) := by
    set T4 := (inverseTransformDivisor (pullback.snd f I.subschemeι)
          (Δ.restrictComponents I.subschemeι)).support
    choose G hG hPG using hdata
    have honly : ∀ P (hP : P ∈ T4) P' (hP' : P' ∈ T4) w, w ∈ P.support → w ∈ P'.support →
        P = P' := fun P hP P' hP' _ hw hw' =>
      eq_of_mem_support_of_eq_connectedComponentIn _ (hdisjF _ (hG P hP) _ (hG P' hP'))
        (hPG P hP) (hPG P' hP') hw hw'
    refine MMP.Resolution.isSmoothScheme_subscheme_of_stalk_eq_span_parameter _ _ fun w hw => ?_
    obtain ⟨P, hP, hwP, hstP⟩ := exists_mem_support_stalk_iInf_eq T4 honly hw
    obtain ⟨E, hE, hyE, hE𝔅, hJ⟩ := hKw w
    obtain ⟨n, z, κ, hz, -, hκ⟩ := exists_coordinates_pullback I f hsnc w hE hyE hJ
    have := isRegularLocalRing_of_isRegularSystemOfParameters hz
    have hwG : w ∈ pullback.fst f I.subschemeι ⁻¹' (G P hP).support :=
      connectedComponentIn_subset _ _ (hPG P hP ▸ hwP)
    have hne : G P hP ≠ E := fun h => hE𝔅 (h ▸ Finset.mem_union_left _ (hG P hP))
    set j := κ ⟨G P hP, hD'mem𝔅 _ (Finset.mem_union_left _ (hG P hP)), hwG, hne⟩
    refine ⟨n, z, j, hz, hstP.trans ?_⟩
    exact stalk_idealSheaf_eq_of_support_eq_connectedComponentIn
      ⟨pullback.fst f I.subschemeι ⁻¹' (G P hP).idealSheaf.support,
        (G P hP).idealSheaf.support.isClosed.preimage (pullback.fst f I.subschemeι).continuous⟩
      (MMP.Resolution.isPrime_span_singleton_of_isRegularSystemOfParameters hz j)
      (hκ ⟨G P hP, hD'mem𝔅 _ (Finset.mem_union_left _ (hG P hP)), hwG, hne⟩) P (hPG P hP) hwP
  exact ⟨⟨⟨inferInstance, hbir, hsmW⟩, hpure, hsnc'⟩, hconj2, hconj3, hconj4⟩

variable {k : Type u} [Field k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  [IsLocallyNoetherian Y] [IsNormal Y]

open Classical in
/-- **The log resolution induced on a general member** (Kollár–Mori, proof of Lemma 5.17). Let
`(X, Δ)` be a pair over an algebraically closed field `k` of characteristic zero with
`dim X ≥ 2`, `s : ι → H⁰(X, 𝒪_X(H))` finitely many sections without common zero, and
`f : Y ⟶ X` a log resolution of `(X, Δ)` whose `f`-exceptional prime divisors form the finite set
`Ex` and such that the reduced divisor on the components of `f⁻¹_* Δ` is smooth. Then there is a
nonzero polynomial `Q` such that for every `c` with `Q(c) ≠ 0` the section `σ = ∑ cᵢ sᵢ` is
nonzero and, for every connected component `Z` of `Supp (σ)₀` with its reduced structure
`ι_Z : H⁰ ⟶ X`, the base change `f⁰ : Y ×_X H⁰ ⟶ H⁰` is a log resolution of `(H⁰, Δ|_{H⁰})`,
its exceptional prime divisors are exactly the irreducible components of the preimages of the
`E ∈ Ex` (each of which is a prime divisor), and the reduced divisor on the components of
`(f⁰)⁻¹_*(Δ|_{H⁰})` is smooth. -/
@[mmp "lem_km5d_general_member_restricted_log_resolution"]
public theorem IsLogResolution.exists_polynomial_isLogResolution_restrict_connectedComponent
    [IsAlgClosed k] [CharZero k] (hdim : 2 ≤ topologicalKrullDim X)
    {Δ : QDivisor X} (hΔ : IsPair sX Δ) {f : Y ⟶ X}
    (hf : IsLogResolution sX (QDivisor.toRDivisor Δ) f) (Ex : Finset (PrimeDivisor Y))
    (hEx : ∀ F : PrimeDivisor Y, F ∈ Ex ↔ RationalMap.IsExceptional f.toRationalMap F)
    (hsm : IsSmoothScheme
      ((⨅ F ∈ (inverseTransformDivisor f Δ).support, F.idealSheaf).subschemeι ≫ f ≫ sX))
    {H : Divisor X} {ι : Type*} [Fintype ι] (s : ι → H.divisorialSubmodule ⊤)
    (hs : ∀ x : X, ∃ (i : ι) (hi : s i ≠ 0), x ∉ (H.zeroDivisor (s i) hi).supp) :
    ∃ Q : MvPolynomial ι k, Q ≠ 0 ∧ ∀ c : ι → k, MvPolynomial.eval c Q ≠ 0 →
      ∃ hσ : (∑ i, scalarsToGlobalSections k sX (c i) • s i) ≠ 0,
        ∀ (Z : Closeds X),
          ∀ x ∈ (H.zeroDivisor (∑ i, scalarsToGlobalSections k sX (c i) • s i) hσ).supp,
          connectedComponentIn
            ((H.zeroDivisor (∑ i, scalarsToGlobalSections k sX (c i) • s i) hσ).supp : Set X) x =
            (Z : Set X) →
          IsLogResolution ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ sX)
              (QDivisor.toRDivisor (Δ.restrictComponents
                (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι))
              (pullback.snd f (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι) ∧
            (∀ F : PrimeDivisor (pullback f (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι),
              RationalMap.IsExceptional
                  (pullback.snd f (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι).toRationalMap
                  F ↔
                ∃ E ∈ Ex, Maximal (fun T ↦ IsIrreducible T ∧ T ⊆
                  pullback.fst f (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ⁻¹'
                    E.support) F.support) ∧
            (∀ E ∈ Ex, ∀ C, Maximal (fun T ↦ IsIrreducible T ∧ T ⊆
                pullback.fst f (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ⁻¹'
                  E.support) C →
              ∃ F : PrimeDivisor (pullback f (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι),
                F.support = C) ∧
            IsSmoothScheme
              ((⨅ F ∈ (inverseTransformDivisor
                  (pullback.snd f (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι)
                  (Δ.restrictComponents
                    (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι)).support,
                  F.idealSheaf).subschemeι ≫
                pullback.snd f (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫
                (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ sX) := by
  obtain ⟨Q, hQ, hc⟩ :=
    IsLogResolution.exists_polynomial_isSNC_pullback_zeroDivisor_add hΔ hf Ex hEx hsm s hs
  refine ⟨Q, hQ, fun c hc' => ?_⟩
  obtain ⟨hσ, hB, H', hpb, h01, hsnc, hdisj⟩ := hc c hc'
  exact ⟨hσ, fun Z x _ hZ =>
    isLogResolution_pullback_snd_vanishingIdeal_of_isSNC hΔ hf Ex hEx hsm s hs
      _ hσ hB H' hpb h01 hsnc hdisj Z x hZ⟩

end MMP.Mori
