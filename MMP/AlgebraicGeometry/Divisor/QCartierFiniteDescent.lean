module

import MMP.AlgebraicGeometry.Resolution.OrderUpperSemicontinuous
public import MMP.AlgebraicGeometry.Morphisms.FiniteFunctionField
public import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupEmbedded
public import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.FieldDescent
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuasiProjectiveRegularSurface

/-!
# Finite morphisms, smoothness and regularity over a field

Foundational facts about schemes over a field and finite morphisms between normal schemes.

**`ℚ`-Cartierness descends along finite surjective morphisms.** Let `π : T ⟶ Z` be a finite
surjective morphism of integral, normal, locally Noetherian schemes and `B` a `ℚ`-divisor on `Z`.
The pull-back `π^*B` has coefficient `e(E'/E) · b_E` along a prime divisor `E'` over `E`, where
`e(E'/E) = ord_{E'}(π^* t)` for a uniformizer `t` of `𝒪_{Z,E}`. If `π^*B` is `ℚ`-Cartier, so is
`B`: write `m π^*B = div(g)` on the whole fibre over a point, and take the norm, so that
`div(N_{K(T)/K(Z)}(g)) = m [K(T) : K(Z)] B` near that point.

**Smoothness and regularity over a field.** A scheme smooth over a field `k` is regular, also
after any extension of the base field; over a perfect field a regular scheme locally of finite
type is smooth; smoothness descends along field extensions; and a scheme of finite type, smooth
of relative dimension two, is a regular surface. In particular a smooth proper scheme of
dimension at most one over `k` is projective over `k` (Stacks, Tag 0C5P).

**The tame canonical-order formula.** Let `h : Y' ⟶ Y` be a finite surjective morphism of normal
varieties of dimension `n` over a field of characteristic zero, `E'` a prime divisor of `Y'`
over a prime divisor `E` of `Y`, and `e = ord_{E'}(h^* t)` the ramification index. Every nonzero
rational `m`-canonical form `τ` satisfies `ord_{E'}(h^* τ) = e · ord_E(τ) + m (e - 1)`.

**The singular locus.** The singular locus of an integral scheme locally of finite type over a
perfect field is a proper closed subset, and the stalks of a scheme smooth over a perfect field
are regular local rings, hence domains.

## Main results

* `MMP.Mori.QDivisor.IsQCartier.of_isFinite_of_surjective`: if `π^*B` is `ℚ`-Cartier then so is
  `B`.
* `MMP.isRegular_of_smooth_of_field`: the dictionary between smoothness and regularity over a
  field, as one conjunction of five assertions.
* `MMP.isProjective_of_smooth_of_isProper_of_topologicalKrullDim_le_one`: smooth proper curves
  are projective.
* `MMP.Mori.ordForm_pullbackRationalPluriForms_of_finite`: the tame canonical-order formula.
* `MMP.singularLocus_ne_top_and_dense_smoothLocus`: the singular locus is a proper closed subset
  and the smooth locus is dense.

## Implementation notes

* The source works with normal complex varieties for the descent of `ℚ`-Cartierness. The norm
  argument only uses that `π` is finite and surjective and that `Z` and `T` are integral, normal
  and locally Noetherian, so the statement is made in that generality. The pull-back `π^*B` is
  given as a `ℚ`-divisor `B'` on `T` with the coefficients above; these determine `B'`, since by
  going-down and incomparability every prime divisor of `T` lies over one of `Z`. The single
  local equation on a fibre is built semilocally, by algebraic Hartogs, and the norm is computed
  divisor by divisor through Stacks, Tag 02RT.
* A curve is encoded only by `topologicalKrullDim X ≤ 1`; irreducibility and separatedness are
  not needed for projectivity, which is `AlgebraicGeometry.IsProjective` (Stacks, Tag 01W8).
* The base change of `f : X ⟶ Spec k` along `Spec K ⟶ Spec k` is
  `pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))`, and a morphism of finite
  type is written as `QuasiCompact` and `LocallyOfFiniteType`.
* The source states the canonical-order formula for rational top forms; it is stated here for
  rational `m`-canonical forms, `m ∈ ℤ`, the source's case being `m = 1`. The source computes
  the Jacobian factor `e a(s) s^{e-1} + a'(s) s^e` in the completions `κ(E)[[t]] → κ(E')[[s]]`;
  here the same calculation is done in the local rings `A = 𝒪_{Y,E} → B = 𝒪_{Y',E'}`, with
  `t ↦ a s^e`. The conormal sequence `𝔪/𝔪² → κ ⊗ Ω_{A/k} → Ω_{κ/k} → 0` is left exact because
  `κ(E)` is formally smooth over `k`; it gives `u_i ∈ A` such that `dt, du_i` lift a basis of
  `κ(E) ⊗ Ω_{A/k}`. Since `κ(E')/κ(E)` is finite separable, `ds, du_i` span
  `κ(E') ⊗ Ω_{B/k}`. By Nakayama the two families are bases of `Ω_{A/k}` and `Ω_{B/k}`, and
  `dt ∧ du = (e a + s a₀) s^{e-1} ds ∧ du`, where `da = a₀ ds + ∑ a_i du_i`.
* The singular-locus statement is made over any perfect field `k` rather than `ℂ`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 15
* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 5.20
* [Lazarsfeld, *Positivity in Algebraic Geometry I*, Notation and Conventions]
* [Kollár, *Lectures on resolution of singularities*]
* [Stacks, Tag 056S], [Stacks, Tag 00TV], [Stacks, Tag 02VL], [Stacks, Tag 0B9D],
  [Stacks, Tag 0C5P], [Stacks, Tag 01W8], [Stacks, Tag 02RT]
-/

universe u

/-! ### `ℚ`-Cartierness descends along finite surjective morphisms -/

section QCartier

open CategoryTheory
open AlgebraicGeometry hiding PrimeDivisor

namespace MMP.Mori

section Fibre

variable {Z T : Scheme.{u}} (π : T ⟶ Z)
    [IsIntegral Z] [IsIntegral T] [IsLocallyNoetherian Z] [IsLocallyNoetherian T]
    [IsNormal Z] [IsNormal T] [IsFinite π] [Surjective π]

/-- The order of vanishing of an element of the base does not depend on the fraction field in
which it is read. -/
private lemma ordFrac_algebraMap_eq {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Ring.KrullDimLE 1 R] {K K' : Type*} [Field K] [Field K'] [Algebra R K] [Algebra R K']
    [IsFractionRing R K] [IsFractionRing R K'] (x : R) :
    Ring.ordFrac R (algebraMap R K x) = Ring.ordFrac R (algebraMap R K' x) := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [Ring.ordFrac_eq_ord (K := K) R hx, Ring.ordFrac_eq_ord (K := K') R hx]

/-- The order of vanishing is invariant under an `R`-algebra map of fraction fields of `R`. -/
private lemma ordFrac_algHom {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Ring.KrullDimLE 1 R] {K K' : Type*} [Field K] [Field K'] [Algebra R K] [Algebra R K']
    [IsFractionRing R K] [IsFractionRing R K'] (σ : K →ₐ[R] K') (k : K) :
    Ring.ordFrac R (σ k) = Ring.ordFrac R k := by
  obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) k
  dsimp only
  rw [IsFractionRing.mk'_eq_div, map_div₀, AlgHom.commutes, AlgHom.commutes, map_div₀, map_div₀,
    ordFrac_algebraMap_eq (K := K) (K' := K') a,
    ordFrac_algebraMap_eq (K := K) (K' := K') (b : R)]

/-- On an integral normal scheme, the order `E.ord` of a rational function along a prime divisor
`E` is Mathlib's order of vanishing `Scheme.ord` at the generic point `η_E`, read through
`K(X) ≃ X.functionField`. -/
private lemma ord_eq_ord_genericPoint {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] (E : PrimeDivisor X) (φ : (RationalFunctions X)ˣ) :
    E.ord φ = X.ord (rationalFunctionsEquivFunctionField X φ) E.genericPoint := by
  have hy := E.coheight_genericPoint
  have : Ring.KrullDimLE 1 E.localRing := krullDimLE_of_coheight_le hy.le
  set f := rationalFunctionsEquivFunctionField X (φ : RationalFunctions X) with hfdef
  have hf : f ≠ 0 :=
    (Units.map (rationalFunctionsEquivFunctionField X : RationalFunctions X →* X.functionField)
      φ).ne_zero
  rw [eq_comm, Scheme.ord_eq_iff hy hf]
  change _ = WithZero.exp (E.ord φ)
  rw [← E.valuation_component φ]
  let := E.toComponent.hom.toAlgebra
  have hKc := isFractionRing_stalkToRationalFunctions E.genericPoint_mem_component
  let Kc := X.presheaf.stalk (componentGenericPoint X E.component)
  let ψ : Kc →ₐ[E.localRing] X.functionField :=
    { (X.presheaf.stalkSpecializes (genericPoint_specializes _)).hom with
      commutes' := fun a =>
        congrArg (fun h => h.hom a) (TopCat.Presheaf.stalkSpecializes_comp X.presheaf
          (genericPoint_specializes (componentGenericPoint X E.component))
          E.specializes_genericPoint) }
  obtain ⟨V, hV, s, hs⟩ := X.presheaf.exists_germ_eq ((φ : RationalFunctions X) E.component)
  have hVd : Dense (V : Set X) := V.isOpen.dense ⟨_, hV⟩
  have : Subsingleton (irreducibleComponents X) := by
    rw [irreducibleComponents_eq_singleton]; infer_instance
  have hψ : ψ ((φ : RationalFunctions X) E.component) = f := by
    rw [← hs]
    change (X.presheaf.germ V _ hV ≫ X.presheaf.stalkSpecializes _).hom s = f
    rw [TopCat.Presheaf.germ_stalkSpecializes]
    have hφ : (φ : RationalFunctions X) =
        (Stacks.Chow.rationalFunctionsEquivStalks X).1 (Stacks.Chow.ofSection X ⟨V, hVd⟩ s) := by
      funext Z
      obtain rfl : Z = E.component := Subsingleton.elim _ _
      rw [(Stacks.Chow.rationalFunctionsEquivStalks X).2 ⟨V, hVd⟩ s E.component hV, ← hs]
    rw [hfdef, hφ]
    change _ = (Stacks.Chow.rationalFunctionsEquivFunctionField X).1
      ((Stacks.Chow.rationalFunctionsEquivStalks X).1.symm
        ((Stacks.Chow.rationalFunctionsEquivStalks X).1 (Stacks.Chow.ofSection X ⟨V, hVd⟩ s)))
    rw [RingEquiv.symm_apply_apply, (Stacks.Chow.rationalFunctionsEquivFunctionField X).2 ⟨V, hVd⟩ s
      ((genericPoint_specializes _).mem_open V.isOpen hV)]
  have hval : E.valuation ((φ : RationalFunctions X) E.component) =
      Ring.ordFrac E.localRing (IsLocalization.algEquiv (nonZeroDivisors E.localRing) Kc
        (FractionRing E.localRing) ((φ : RationalFunctions X) E.component)) := rfl
  rw [hval, ← ordFrac_algHom (ψ.comp (IsLocalization.algEquiv (nonZeroDivisors E.localRing) Kc
    (FractionRing E.localRing)).symm.toAlgHom)]
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply, hψ]
  rfl

/-- On an integral normal scheme every prime divisor `E` has a uniformizer: a rational function
`t` with `ord_E t = 1`. -/
private lemma exists_ord_genericPoint_eq_one {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (E : PrimeDivisor X) :
    ∃ t : X.functionField, X.ord t E.genericPoint = 1 := by
  have := E.isDiscreteValuationRing_localRing
  have h1 := E.coheight_genericPoint
  have : Ring.KrullDimLE 1 E.localRing := krullDimLE_of_coheight_le h1.le
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible E.localRing
  have hne : algebraMap E.localRing X.functionField ϖ ≠ 0 :=
    (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero))
  refine ⟨algebraMap E.localRing X.functionField ϖ, ?_⟩
  rw [Scheme.ord_eq_iff h1 hne]
  exact Ring.ordFrac_irreducible hϖ

/-- Incomparability: a specialization inside a fibre of a finite morphism is trivial, the fibres
being discrete. -/
private lemma eq_of_specializes_of_map_eq {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] {x x' : X}
    (h : x ⤳ x') (he : f x = f x') : x = x' := by
  have : LocallyQuasiFinite f := inferInstance
  have : DiscreteTopology (f.fiber (f x')) := IsLocallyArtinian.discreteTopology
  have : DiscreteTopology (f ⁻¹' {f x'}) := (f.fiberHomeo (f x')).discreteTopology
  let a : ↥(f ⁻¹' {f x'}) := ⟨x, he⟩
  let b : ↥(f ⁻¹' {f x'}) := ⟨x', rfl⟩
  have hab : a ⤳ b := Topology.IsInducing.subtypeVal.specializes_iff.mp h
  have hb : a ∈ ({b} : Set _) := hab.mem_open (isOpen_discrete _) rfl
  exact congrArg Subtype.val hb

/-- A finite morphism is strictly monotone for the specialization order. -/
private lemma strictMono_of_isFinite {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] :
    StrictMono f := fun x y hxy =>
  have hyx : y ⤳ x := hxy.le
  lt_of_le_not_ge (hyx.map f.continuous) fun hle => hxy.not_ge <| by
    have hxy' : f x ⤳ f y := hle
    have he : f y = f x := ((hyx.map f.continuous).antisymm hxy').eq
    rw [eq_of_specializes_of_map_eq f hyx he]

omit [IsLocallyNoetherian Z] [IsLocallyNoetherian T] [IsNormal Z] [IsNormal T] in
/-- A point of `T` above a codimension-one point of `Z` has codimension one: by incomparability
its coheight is at most that of its image, and it is not the generic point, whose image is the
generic point of `Z`. -/
private lemma coheight_eq_one_of_coheight_map_eq_one (x : T) (hx : Order.coheight (π x) = 1) :
    Order.coheight x = 1 := by
  refine le_antisymm (hx ▸ Order.coheight_le_coheight_apply_of_strictMono _
    (strictMono_of_isFinite π) x) ?_
  have hne : x ≠ genericPoint T := by
    rintro rfl
    rw [map_genericPoint_of_isDominant π] at hx
    have h0 : Order.coheight (genericPoint Z) = 0 :=
      Order.coheight_eq_zero.mpr fun y _ => genericPoint_specializes y
    rw [h0] at hx
    exact zero_ne_one hx
  have hlt : x < genericPoint T := lt_of_le_not_ge (genericPoint_specializes x) fun h =>
    hne ((show x ⤳ genericPoint T from h).antisymm (genericPoint_specializes x)).eq
  have h0 : Order.coheight (genericPoint T) = 0 :=
    Order.coheight_eq_zero.mpr fun y _ => genericPoint_specializes y
  simpa [h0] using Order.coheight_add_one_le hlt

omit [IsLocallyNoetherian Z] [IsLocallyNoetherian T] [IsNormal Z] [IsNormal T] in
/-- A finite dominant morphism of integral schemes induces a finite extension of function
fields. -/
private lemma finite_functionField :
    letI := (functionFieldMap π).toAlgebra
    Module.Finite Z.functionField T.functionField := by
  have hdom : functionFieldMap π = dominantFunctionFieldMap π :=
    (congrArg CommRingCat.Hom.hom (Stacks.Chow.stalkMap_cast_target π (genericPoint T)
      (map_genericPoint_of_isDominant π))).symm
  rw [hdom]
  exact MMP.moduleFinite_functionField_of_isFinite π

/-- The rational function `1` has order zero everywhere. -/
private lemma ord_one {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] (x : X) :
    X.ord (1 : X.functionField) x = 0 := by
  have h := Scheme.ord_mul (x := x) (one_ne_zero (α := X.functionField)) one_ne_zero
  rw [mul_one] at h
  omega

/-- The order of a power is the multiple of the order. -/
private lemma ord_pow {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (x : X) {t : X.functionField} (ht : t ≠ 0) (n : ℕ) : X.ord (t ^ n) x = n * X.ord t x := by
  simpa using ord_zpow x ht n

/-- In a Noetherian domain of dimension at most one, a nonzero nonunit has positive order. -/
private lemma ofAdd_one_le_ordFrac {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Ring.KrullDimLE 1 R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] {x : R}
    (hx0 : x ≠ 0) (hx : ¬ IsUnit x) :
    ((Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ≤
      Ring.ordFrac R (algebraMap R K x) := by
  have hnz : x ∈ nonZeroDivisors R := mem_nonZeroDivisors_of_ne_zero hx0
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (Ring.ord_ne_top hnz)
  have : Nontrivial (R ⧸ Ideal.span {x}) :=
    Ideal.Quotient.nontrivial_iff.mpr (by rwa [ne_eq, Ideal.span_singleton_eq_top])
  have hpos : 0 < Ring.ord R x := Module.length_pos
  rw [Ring.ordFrac_eq_ord R hx0, Ring.ordMonoidWithZeroHom_eq_coe R hnz hn.symm]
  have : 1 ≤ n := by
    rw [← hn] at hpos; exact_mod_cast hpos
  exact_mod_cast (Multiplicative.ofAdd_le.mpr (by exact_mod_cast this))

/-- A nonzero section vanishing at a point `η` of codimension one has positive order at `η`. -/
private lemma one_le_ord_of_notMem_basicOpen {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] {V : X.Opens} [Nonempty V] (s : Γ(X, V)) {η : X} (hηV : η ∈ V)
    (hη : Order.coheight η = 1) (hs : η ∉ X.basicOpen s) (hs0 : s ≠ 0) :
    1 ≤ X.ord (X.germToFunctionField V s) η := by
  have : Ring.KrullDimLE 1 (X.presheaf.stalk η) := krullDimLE_of_coheight_le hη.le
  have hg0 : X.presheaf.germ V η hηV s ≠ 0 := fun h =>
    hs0 (germ_injective_of_isIntegral X η hηV (by rw [h, map_zero]))
  have hf : X.germToFunctionField V s ≠ 0 := by
    rw [← Scheme.algebraMap_germ_eq_germToFunctionField _ hηV]
    exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hg0
  rw [Scheme.le_ord_iff hη hf, ← Scheme.algebraMap_germ_eq_germToFunctionField _ hηV]
  exact ofAdd_one_le_ordFrac hg0 (by rwa [Scheme.mem_basicOpen X s η hηV] at hs)

/-- A section has nonnegative order at every point of its domain. -/
private lemma ord_germToFunctionField_nonneg {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] {V : X.Opens} [Nonempty V] (s : Γ(X, V)) (hs0 : s ≠ 0) {η : X}
    (hηV : η ∈ V) : 0 ≤ X.ord (X.germToFunctionField V s) η := by
  have h := Scheme.ord_le_smul hηV hs0 (1 : X.functionField)
  rwa [ord_one, Algebra.smul_def, mul_one] at h

/-- **Algebraic Hartogs at a point.** On a normal integral locally Noetherian scheme, a rational
function `g ≠ 0` with `v_Γ(g) ≥ 0` for every prime divisor `Γ` through `x` lies in `𝒪_{X,x}`. -/
private lemma exists_algebraMap_stalk_eq_of_forall_ord_nonneg {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (x : X) {g : X.functionField} (hg : g ≠ 0)
    (h : ∀ Γ : PrimeDivisor X, x ∈ Γ.support → 0 ≤ X.ord g Γ.genericPoint) :
    ∃ r : X.presheaf.stalk x, algebraMap (X.presheaf.stalk x) X.functionField r = g := by
  have : IsIntegrallyClosed (X.presheaf.stalk x) := IsNormal.stalk_normal x
  refine Stacks.AlgebraicGeometry.UnitsNormalProper.exists_algebraMap_eq_of_forall_height_eq_one
    X.functionField fun q hq => ?_
  have hξ1 : Order.coheight (X.fromSpecStalk x q) = 1 :=
    (Stacks.Chow.coheight_fromSpecStalk_eq_height x q).trans hq
  set E : PrimeDivisor X := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hξ1 with hEdef
  have hEξ : E.genericPoint = X.fromSpecStalk x q :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hξ1
  have hspec : E.genericPoint ⤳ x := hEξ ▸ Stacks.Chow.specializes_fromSpecStalk x q
  have hxE : x ∈ E.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact specializes_iff_mem_closure.mp hspec
  have hv : E.divisorialValuation g ≤ 1 := by
    rw [E.divisorialValuation_eq_exp_neg_ord hg, ← WithZero.exp_zero, WithZero.exp_le_exp]
    linarith [h E hxE]
  obtain ⟨b, hb⟩ := (E.divisorialValuation_le_one_iff g).mp hv
  let := (X.presheaf.stalkSpecializes hspec).hom.toAlgebra
  have hloc := Stacks.Chow.isLocalization_stalk_of_specializes hspec q hEξ.symm
  obtain ⟨⟨a, s⟩, hab⟩ := IsLocalization.mk'_surjective q.asIdeal.primeCompl b
  change IsLocalization.mk' E.localRing a s = b at hab
  refine ⟨a, s, s.2, ?_⟩
  have hspec' := IsLocalization.mk'_spec E.localRing a s
  rw [hab] at hspec'
  have h2 := congrArg (algebraMap E.localRing X.functionField) hspec'
  rw [map_mul, hb] at h2
  change g * algebraMap E.localRing X.functionField ((X.presheaf.stalkSpecializes hspec).hom s) =
    algebraMap E.localRing X.functionField ((X.presheaf.stalkSpecializes hspec).hom a) at h2
  rwa [MMP.Mori.algebraMap_stalkSpecializes, MMP.Mori.algebraMap_stalkSpecializes] at h2

/-- A unit of the stalk at `y` has order zero at every point of some open neighbourhood of `y`. -/
private lemma exists_open_ord_algebraMap_eq_zero {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] {y : X} {u : X.presheaf.stalk y} (hu : IsUnit u) :
    ∃ W : X.Opens, y ∈ W ∧ ∀ η ∈ W,
      X.ord (algebraMap (X.presheaf.stalk y) X.functionField u) η = 0 := by
  obtain ⟨V, hyV, s, rfl⟩ := X.presheaf.exists_germ_eq u
  have hyb : y ∈ X.basicOpen s := (Scheme.mem_basicOpen X s y hyV).mpr hu
  have : Nonempty (X.basicOpen s) := ⟨⟨y, hyb⟩⟩
  have : Nonempty V := ⟨⟨y, hyV⟩⟩
  refine ⟨X.basicOpen s, hyb, fun η hη => ?_⟩
  have : Nonempty (X.toRingedSpace.basicOpen s) := ⟨⟨y, hyb⟩⟩
  have h := Scheme.ord_of_isUnit (X.toRingedSpace.isUnit_res_basicOpen s) hη
  rw [Scheme.algebraMap_germ_eq_germToFunctionField]
  convert h using 2
  simp only [Scheme.germToFunctionField]
  rw [← TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (X.basicOpen_le s))]
  rfl

private lemma ord_div {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] (η : X)
    {f g : X.functionField} (hf : f ≠ 0) (hg : g ≠ 0) :
    X.ord (f / g) η = X.ord f η - X.ord g η := by
  have h := Scheme.ord_mul (x := η) (div_ne_zero hf hg) hg
  rw [div_mul_cancel₀ f hg] at h
  omega

/-- In an affine open `V₀`, a point `x ∈ V₀` lying in no closure `closure {y}`, `y ∈ P`, for a
finite set `P`, is in a basic open `D(f) ⊆ V₀` that avoids all of `P`. -/
lemma exists_basicOpen_mem_forall_notMem {X : Scheme.{u}} {V0 : X.Opens} (hV0 : IsAffineOpen V0)
    {x : X} (hx : x ∈ V0) (P : Finset X) (hP : ∀ y ∈ P, x ∉ closure {y}) :
    ∃ f : Γ(X, V0), x ∈ X.basicOpen f ∧ ∀ y ∈ P, y ∉ X.basicOpen f := by
  let O : X.Opens := V0 ⊓ ⟨⋂ y ∈ P, (closure {y})ᶜ,
    isOpen_biInter_finset fun y _ => isClosed_closure.isOpen_compl⟩
  obtain ⟨f, hfO, hxf⟩ := hV0.exists_basicOpen_le (V := O) ⟨x, hx, Set.mem_iInter₂.mpr hP⟩ hx
  exact ⟨f, hxf, fun y hy hyf => Set.mem_iInter₂.mp (hfO hyf).2 y hy (subset_closure rfl)⟩

/-- **Semilocal generator.** Let `S` be a finite set of pairwise incomparable points in an affine
open `V₀` of a normal integral locally Noetherian scheme, at each of which the divisor `D` has a
local equation. Then `D` has a single local equation on an open neighbourhood of `S`: choose
local equations `φ_x`, clear their poles against each other by sections `s_x` invertible at `x`,
and combine them with sections `a_x` invertible at `x` and vanishing at the other points; the
combination `g = ∑ a_x s_x^N φ_x` has `g / φ_y` a unit of `𝒪_{X,y}` for every `y ∈ S`, by
algebraic Hartogs. -/
private lemma exists_isLocalEquation_finset {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (D : Divisor X) (S : Finset X) (hS : S.Nonempty)
    (V0 : X.Opens) (hV0 : IsAffineOpen V0) (hSV0 : ∀ x ∈ S, x ∈ V0)
    (hinc : ∀ x ∈ S, ∀ y ∈ S, x ⤳ y → x = y)
    (hD : ∀ x ∈ S, ∃ U : X.Opens, x ∈ U ∧ ∃ φ : (RationalFunctions X)ˣ, D.IsLocalEquation U φ) :
    ∃ W : X.Opens, (∀ x ∈ S, x ∈ W) ∧ ∃ g : (RationalFunctions X)ˣ, D.IsLocalEquation W g := by
  classical
  obtain ⟨x₀, hx₀⟩ := hS
  have : Nonempty V0 := ⟨⟨x₀, hSV0 x₀ hx₀⟩⟩
  choose! V hxV φ hφ using hD
  set eX := rationalFunctionsEquivFunctionField X
  have hspecmem : ∀ (E : PrimeDivisor X) (W : X.Opens) (y : X), y ∈ E.support → y ∈ W →
      E.genericPoint ∈ W := fun E W y hyE hyW => by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hyE
    exact (specializes_iff_mem_closure.mpr hyE).mem_open W.isOpen hyW
  obtain ⟨F, hF0, hF⟩ : ∃ F : X → X.functionField, (∀ x, F x ≠ 0) ∧
      ∀ x ∈ S, ∀ E : PrimeDivisor X, E.genericPoint ∈ V x →
        D.coeff E = X.ord (F x) E.genericPoint :=
    ⟨fun x => eX (φ x : RationalFunctions X), fun x =>
      (Units.map (eX : RationalFunctions X →* X.functionField) (φ x)).ne_zero,
      fun x hx E hE => by
        rw [hφ x hx E ((E.genericPoint_mem_iff _).mp hE), ord_eq_ord_genericPoint]⟩
  -- the finitely many points of codimension one of `V₀` where some `F x / F y` has a zero or pole
  have hQfin : (⋃ p ∈ S ×ˢ S, {η : X | η ∈ V0 ∧ X.ord (F p.1 / F p.2) η ≠ 0}).Finite :=
    Set.Finite.biUnion (S ×ˢ S).finite_toSet fun _ _ =>
      (Stacks.Chow.locallyFiniteSupport_ord X _).finite_inter_support_of_isCompact hV0.isCompact
  obtain ⟨Qf, hQf⟩ : ∃ Qf : Finset X, ∀ η, η ∈ V0 → ∀ x ∈ S, ∀ y ∈ S,
      X.ord (F x / F y) η ≠ 0 → η ∈ Qf :=
    ⟨hQfin.toFinset, fun η hη x hx y hy hne => hQfin.mem_toFinset.mpr
      (Set.mem_biUnion (x := (x, y)) (Finset.mem_coe.mpr (Finset.mem_product.mpr ⟨hx, hy⟩))
        ⟨hη, hne⟩)⟩
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ η ∈ Qf, ∀ x ∈ S, ∀ y ∈ S, (X.ord (F x / F y) η).natAbs ≤ N :=
    ⟨∑ η ∈ Qf, ∑ p ∈ S ×ˢ S, (X.ord (F p.1 / F p.2) η).natAbs, fun η hη x hx y hy =>
      (Finset.single_le_sum (f := fun p : X × X => (X.ord (F p.1 / F p.2) η).natAbs)
        (fun _ _ => Nat.zero_le _) (a := (x, y)) (Finset.mem_product.mpr ⟨hx, hy⟩)).trans
      (Finset.single_le_sum (f := fun η => ∑ p ∈ S ×ˢ S, (X.ord (F p.1 / F p.2) η).natAbs)
        (fun _ _ => Nat.zero_le _) hη)⟩
  -- sections separating the points of `S`
  choose! a hxa haV using fun x (hx : x ∈ S) => exists_basicOpen_mem_forall_notMem hV0
    (hSV0 x hx) (S.erase x) fun y hy hxy => (Finset.mem_erase.mp hy).1
      (hinc y (Finset.mem_of_mem_erase hy) x hx (specializes_iff_mem_closure.mpr hxy))
  -- sections clearing the poles of the `F x / F y` not passing through `x`
  choose! s hxs hsV using fun x (hx : x ∈ S) => exists_basicOpen_mem_forall_notMem hV0
    (hSV0 x hx) (Qf.filter fun η => ¬ η ⤳ x) fun η hη hxη =>
      (Finset.mem_filter.mp hη).2 (specializes_iff_mem_closure.mpr hxη)
  have hne0 : ∀ (t : Γ(X, V0)) (x : X), x ∈ X.basicOpen t → t ≠ 0 := by
    rintro t x hx rfl
    rw [Scheme.basicOpen_zero] at hx
    exact hx
  set A : X → X.functionField := fun x => X.germToFunctionField V0 (a x)
  set Sx : X → X.functionField := fun x => X.germToFunctionField V0 (s x)
  have hSx0 : ∀ x ∈ S, Sx x ≠ 0 := fun x hx => by
    simp only [Sx, ne_eq, map_eq_zero_iff _ (X.germToFunctionField_injective V0)]
    exact hne0 _ x (hxs x hx)
  -- the quotients `s_x^N F_x / F_y` are regular at `y`
  have hreg : ∀ x ∈ S, ∀ y ∈ S, ∃ r : X.presheaf.stalk y,
      algebraMap (X.presheaf.stalk y) X.functionField r = Sx x ^ N * F x / F y := by
    intro x hx y hy
    refine exists_algebraMap_stalk_eq_of_forall_ord_nonneg y
      (div_ne_zero (mul_ne_zero (pow_ne_zero _ (hSx0 x hx)) (hF0 x)) (hF0 y)) fun E hyE => ?_
    have hηV0 : E.genericPoint ∈ V0 := hspecmem E V0 y hyE (hSV0 y hy)
    have hη1 : Order.coheight E.genericPoint = 1 := E.coheight_genericPoint
    rw [mul_div_assoc, Scheme.ord_mul (pow_ne_zero _ (hSx0 x hx)) (div_ne_zero (hF0 x) (hF0 y)),
      ord_pow _ (hSx0 x hx)]
    have hnn : 0 ≤ X.ord (Sx x) E.genericPoint :=
      ord_germToFunctionField_nonneg _ (hne0 _ x (hxs x hx)) hηV0
    by_cases hQη : E.genericPoint ∈ Qf
    · by_cases hηx : E.genericPoint ⤳ x
      · have h0 : X.ord (F x / F y) E.genericPoint = 0 := by
          rw [ord_div _ (hF0 x) (hF0 y), ← hF x hx E (hηx.mem_open (V x).isOpen (hxV x hx)),
            ← hF y hy E (hspecmem E (V y) y hyE (hxV y hy)), sub_self]
        rw [h0]; positivity
      · have hnot : E.genericPoint ∉ X.basicOpen (s x) :=
          hsV x hx _ (Finset.mem_filter.mpr ⟨hQη, hηx⟩)
        have h1 := one_le_ord_of_notMem_basicOpen (s x) hηV0 hη1 hnot (hne0 _ x (hxs x hx))
        have hle := hN _ hQη x hx y hy
        have hle' : -(X.ord (F x / F y) E.genericPoint) ≤ N := by omega
        have hNo : (N : ℤ) ≤ N * X.ord (Sx x) E.genericPoint :=
          le_mul_of_one_le_right (Nat.cast_nonneg N) h1
        linarith
    · have h0 : X.ord (F x / F y) E.genericPoint = 0 := by
        by_contra hne
        exact hQη (hQf _ hηV0 x hx y hy hne)
      rw [h0]; positivity
  choose! r hr using hreg
  set G : X.functionField := ∑ x ∈ S, A x * (Sx x ^ N * F x) with hG
  -- `G / F y` is a unit of `𝒪_{X,y}`
  have hunit : ∀ y ∈ S, ∃ u : X.presheaf.stalk y, IsUnit u ∧
      G = F y * algebraMap (X.presheaf.stalk y) X.functionField u := by
    intro y hy
    have hyV0 := hSV0 y hy
    refine ⟨∑ x ∈ S, X.presheaf.germ V0 y hyV0 (a x) * r x y, ?_, ?_⟩
    · have hyy : r y y = X.presheaf.germ V0 y hyV0 (s y) ^ N := by
        apply IsFractionRing.injective (X.presheaf.stalk y) X.functionField
        rw [hr y hy y hy, map_pow, Scheme.algebraMap_germ_eq_germToFunctionField,
          mul_div_assoc, div_self (hF0 y), mul_one]
      rw [← Finset.add_sum_erase _ _ hy, hyy]
      have hu : IsUnit (X.presheaf.germ V0 y hyV0 (a y) * X.presheaf.germ V0 y hyV0 (s y) ^ N) :=
        ((Scheme.mem_basicOpen X _ y hyV0).mp (hxa y hy)).mul
          (((Scheme.mem_basicOpen X _ y hyV0).mp (hxs y hy)).pow N)
      have hm : ∑ x ∈ S.erase y, X.presheaf.germ V0 y hyV0 (a x) * r x y ∈
          IsLocalRing.maximalIdeal (X.presheaf.stalk y) := by
        refine Ideal.sum_mem _ fun x hx => Ideal.mul_mem_right _ _ ?_
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← Scheme.mem_basicOpen X _ y hyV0]
        exact haV x (Finset.mem_of_mem_erase hx) y
          (Finset.mem_erase.mpr ⟨fun h => (Finset.mem_erase.mp hx).1 h.symm, hy⟩)
      by_contra hnu
      have hmem := Ideal.sub_mem _ ((IsLocalRing.mem_maximalIdeal _).mpr hnu) hm
      rw [add_sub_cancel_right] at hmem
      exact (IsLocalRing.mem_maximalIdeal _).mp hmem hu
    · rw [map_sum, Finset.mul_sum, hG]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [map_mul, hr x hx y hy, Scheme.algebraMap_germ_eq_germToFunctionField]
      field_simp [hF0 y]
      simp only [A]
      ring
  have hG0 : G ≠ 0 := by
    obtain ⟨u, hu, hGu⟩ := hunit x₀ hx₀
    rw [hGu]
    exact mul_ne_zero (hF0 x₀) ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hu.ne_zero)
  choose! u hu hGu using hunit
  choose! W hyW hW using fun y (hy : y ∈ S) => exists_open_ord_algebraMap_eq_zero (hu y hy)
  refine ⟨⨆ y ∈ S, W y ⊓ V y, fun y hy => ?_, (Units.mk0 G hG0).map
    (eX.symm : X.functionField →* RationalFunctions X), fun E hE => ?_⟩
  · simp only [TopologicalSpace.Opens.mem_iSup]
    exact ⟨y, hy, hyW y hy, hxV y hy⟩
  · have hη := (E.genericPoint_mem_iff _).mpr hE
    simp only [TopologicalSpace.Opens.mem_iSup] at hη
    obtain ⟨y, hy, hηW, hηV⟩ := hη
    rw [hF y hy E hηV, ord_eq_ord_genericPoint]
    have : rationalFunctionsEquivFunctionField X
        (((Units.mk0 G hG0).map (eX.symm : X.functionField →* RationalFunctions X) :
          (RationalFunctions X)ˣ) : RationalFunctions X) = G := by
      simp [eX]
    rw [this, hGu y hy, Scheme.ord_mul (hF0 y)
      ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (hu y hy).ne_zero),
      hW y hy _ hηW, add_zero]

/-- A Cartier divisor on `T` has, near any point `z` of `Z`, a single local equation on the whole
inverse image `π⁻¹ U`: the fibre over `z` is finite and its points are pairwise incomparable, so
`exists_isLocalEquation_finset` gives one local equation on a neighbourhood `W` of the fibre, and
as `π` is closed, `W` contains `π⁻¹ U` for a neighbourhood `U` of `z`. -/
private lemma exists_isLocalEquation_preimage {D' : Divisor T} (hD' : D'.IsCartier) (z : Z) :
    ∃ U : Z.Opens, z ∈ U ∧ ∃ g : (RationalFunctions T)ˣ, D'.IsLocalEquation (π ⁻¹ᵁ U) g := by
  obtain ⟨_, ⟨U0, hU0, rfl⟩, hzU0, -⟩ :=
    Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
  have hfin : (π.base ⁻¹' {z}).Finite := π.finite_preimage_singleton z
  obtain ⟨x₀, hx₀⟩ := π.surjective z
  obtain ⟨W, hSW, g, hg⟩ := exists_isLocalEquation_finset D' hfin.toFinset
    ⟨x₀, hfin.mem_toFinset.mpr hx₀⟩ (π ⁻¹ᵁ U0) (hU0.preimage π)
    (fun x hx => by
      have : π x = z := by simpa using hx
      change π x ∈ U0
      rw [this]; exact hzU0)
    (fun x hx y hy hxy => eq_of_specializes_of_map_eq π hxy (by
      have h1 : π x = z := by simpa using hx
      have h2 : π y = z := by simpa using hy
      rw [h1, h2]))
    (fun x _ => hD' x)
  have hcl : IsClosed (π '' ((W : Set T)ᶜ)) := π.isClosedMap _ W.isOpen.isClosed_compl
  refine ⟨⟨(π '' ((W : Set T)ᶜ))ᶜ, hcl.isOpen_compl⟩, ?_, g, hg.mono ?_⟩
  · rintro ⟨w, hw, hwz⟩
    exact hw (hSW w (hfin.mem_toFinset.mpr hwz))
  · intro t ht
    by_contra htW
    exact ht ⟨t, htW, rfl⟩

/-- The norm of a local equation of `m π^*B` on `π⁻¹ U` is a local equation of `m n B` on `U`,
where `n = [K(T) : K(Z)]`. At a prime divisor `E` of `Z` meeting `U`, Stacks 02RT
(`Stacks.Chow.finsum_ord_mul_residueDegree_of_isFinite`) gives
`ord_E N(g) = ∑ fᵢ ord_{Eᵢ}(g)` over the prime divisors `Eᵢ` above `E`; applied to a uniformizer
`t` at `E` it gives `∑ eᵢ fᵢ = ord_E (t ^ n) = n`. -/
private lemma exists_isLocalEquation_norm (B : QDivisor Z) (B' : QDivisor T)
    (hB' : ∀ (E : PrimeDivisor Z) (E' : PrimeDivisor T), π E'.genericPoint = E.genericPoint →
      ∀ t : Z.functionField, Z.ord t E.genericPoint = 1 →
        B' E' = (T.ord (functionFieldMap π t) E'.genericPoint : ℚ) * B E) :
    ∃ n : ℕ, 0 < n ∧ ∀ (m : ℕ) (D' : Divisor T), Divisor.toQDivisor D' = (m : ℤ) • B' →
      ∀ (U : Z.Opens) (g : (RationalFunctions T)ˣ), D'.IsLocalEquation (π ⁻¹ᵁ U) g →
        ∃ φ : (RationalFunctions Z)ˣ, ∀ E : PrimeDivisor Z, (E.support ∩ U).Nonempty →
          ((m * n : ℕ) : ℚ) * B E = (E.ord φ : ℚ) := by
  let : Algebra Z.functionField T.functionField := (functionFieldMap π).toAlgebra
  have : Module.Finite Z.functionField T.functionField := finite_functionField π
  have halg : algebraMap Z.functionField T.functionField = dominantFunctionFieldMap π :=
    (congrArg CommRingCat.Hom.hom (Stacks.Chow.stalkMap_cast_target π (genericPoint T)
      (map_genericPoint_of_isDominant π))).symm
  refine ⟨Module.finrank Z.functionField T.functionField, Module.finrank_pos, ?_⟩
  intro m D' hD' U g hg
  set eT := rationalFunctionsEquivFunctionField T
  set eZ := rationalFunctionsEquivFunctionField Z
  have hg0 : eT g ≠ 0 := (Units.map (eT : RationalFunctions T →* T.functionField) g).ne_zero
  have hN0 : Algebra.norm Z.functionField (eT g) ≠ 0 := Algebra.norm_ne_zero_iff.mpr hg0
  refine ⟨(Units.mk0 _ hN0).map (eZ.symm : Z.functionField →* RationalFunctions Z),
    fun E hE => ?_⟩
  set y := E.genericPoint
  have hyU : y ∈ U := by
    obtain ⟨w, hwE, hwU⟩ := hE
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hwE
    exact (specializes_iff_mem_closure.mpr hwE).mem_open U.isOpen hwU
  have hy1 : Order.coheight y = 1 := E.coheight_genericPoint
  have hfib : ∀ x : T, π x = y → Order.coheight x = 1 := fun x hx =>
    coheight_eq_one_of_coheight_map_eq_one π x (hx ▸ hy1)
  obtain ⟨t, ht⟩ := exists_ord_genericPoint_eq_one E
  have ht0 : t ≠ 0 := by rintro rfl; simp at ht
  have hπt0 : algebraMap Z.functionField T.functionField t ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap Z.functionField T.functionField).injective).mpr ht0
  have key := Stacks.Chow.finsum_ord_mul_residueDegree_of_isFinite π halg (eT g) hg0 y hy1 hfib
  have key2 := Stacks.Chow.finsum_ord_mul_residueDegree_of_isFinite π halg _ hπt0 y hy1 hfib
  rw [Algebra.norm_algebraMap, ord_pow y ht0, ht, mul_one] at key2
  have hfin : (π.base ⁻¹' {y}).Finite := π.finite_preimage_singleton y
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at key key2
  have hφ : E.ord ((Units.mk0 _ hN0).map (eZ.symm : Z.functionField →* RationalFunctions Z)) =
      Z.ord (Algebra.norm Z.functionField (eT g)) y := by
    rw [ord_eq_ord_genericPoint]
    simp [eZ, y]
  have hterm : ∀ x ∈ hfin.toFinset,
      ((T.ord (eT g) x : ℤ) : ℚ) = (m : ℚ) * B E * T.ord (algebraMap _ _ t) x := by
    intro x hx
    have hxy : π x = y := by simpa using hx
    have hx1 := hfib x hxy
    set E' : PrimeDivisor T := AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hx1
    have hE' : E'.genericPoint = x :=
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x hx1
    have hmeet : (E'.support ∩ π ⁻¹ᵁ U).Nonempty := by
      refine ⟨x, ?_, ?_⟩
      · have hx' : x ∈ closure {E'.genericPoint} := by rw [hE']; exact subset_closure rfl
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact hx'
      · change π x ∈ U
        rw [hxy]; exact hyU
    have h1 := hg E' hmeet
    rw [ord_eq_ord_genericPoint, hE'] at h1
    have h2 := Divisor.coeff_toQDivisor D' E'
    rw [hD'] at h2
    simp only [DivisorWithCoeffs.coeff, Finsupp.smul_apply, zsmul_eq_mul] at h2 h1
    have h3 := hB' E E' (by rw [hE', hxy]) t ht
    rw [hE'] at h3
    rw [← h1, ← h2, h3]
    simp only [Int.cast_natCast]
    change _ = _ * _ * (T.ord (functionFieldMap π t) x : ℚ)
    ring
  rw [hφ, ← key]
  push_cast
  rw [Finset.sum_congr rfl fun x hx => by rw [hterm x hx]]
  have key2' := congrArg (fun k : ℤ => (k : ℚ)) key2
  push_cast at key2'
  rw [← key2', Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

/-- A `ℚ`-divisor `B` such that `N B` has, near every point, a local equation, is `ℚ`-Cartier. -/
private lemma isQCartier_of_forall_exists {X : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] (B : QDivisor X) (N : ℕ) (hN : 0 < N)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ φ : (RationalFunctions X)ˣ,
      ∀ E : PrimeDivisor X, (E.support ∩ U).Nonempty → (N : ℚ) * B E = (E.ord φ : ℚ)) :
    B.IsQCartier := by
  have hint : ∀ E : PrimeDivisor X, ∃ k : ℤ, (N : ℚ) * B E = k := by
    intro E
    obtain ⟨U, hU, φ, hφ⟩ := h E.genericPoint
    refine ⟨E.ord φ, hφ E ⟨E.genericPoint, ?_, hU⟩⟩
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  let D : Divisor X := Finsupp.mapRange (fun q : ℚ => ⌊(N : ℚ) * q⌋) (by simp) B
  have hD : ∀ E, ((D E : ℤ) : ℚ) = (N : ℚ) * B E := by
    intro E
    obtain ⟨k, hk⟩ := hint E
    simp only [D, Finsupp.mapRange_apply, hk, Int.floor_intCast]
  refine ⟨N, by exact_mod_cast hN.ne', D, ?_, ?_⟩
  · refine Finsupp.ext fun E => ?_
    have := Divisor.coeff_toQDivisor D E
    simp only [DivisorWithCoeffs.coeff] at this
    rw [this, hD, Finsupp.smul_apply, zsmul_eq_mul]
    simp
  · intro x
    obtain ⟨U, hU, φ, hφ⟩ := h x
    refine ⟨U, hU, φ, fun E hE => ?_⟩
    have := hφ E hE
    rw [← hD] at this
    exact_mod_cast this

end Fibre

/-- **`ℚ`-Cartierness descends along finite surjective morphisms.** Let `π : T ⟶ Z` be a finite
surjective morphism of integral, normal, locally Noetherian schemes. Let `B` be a `ℚ`-divisor on
`Z`, and let `B'` be its pull-back `π^*B`: the coefficient of `B'` along a prime divisor `E'`
over a prime divisor `E` is `ord_{E'}(π^* t) · b_E`, for every uniformizer `t` at `E`. If `B'` is
`ℚ`-Cartier, then `B` is `ℚ`-Cartier. -/
@[mmp "lem_mmp_fa15_finite_pullback_q_cartier"]
public theorem QDivisor.IsQCartier.of_isFinite_of_surjective {Z T : Scheme.{u}} (π : T ⟶ Z)
    [IsIntegral Z] [IsIntegral T] [IsLocallyNoetherian Z] [IsLocallyNoetherian T]
    [IsNormal Z] [IsNormal T] [IsFinite π] [Surjective π]
    {B : QDivisor Z} {B' : QDivisor T}
    (hB' : ∀ (E : PrimeDivisor Z) (E' : PrimeDivisor T), π E'.genericPoint = E.genericPoint →
      ∀ t : Z.functionField, Z.ord t E.genericPoint = 1 →
        B' E' = (T.ord (functionFieldMap π t) E'.genericPoint : ℚ) * B E)
    (hB'q : B'.IsQCartier) :
    B.IsQCartier := by
  obtain ⟨m, hm, D', hD'eq, hD'⟩ := hB'q.exists_pos
  obtain ⟨n, hn, hnorm⟩ := exists_isLocalEquation_norm π B B' hB'
  refine isQCartier_of_forall_exists B (m * n) (Nat.mul_pos hm hn) fun z => ?_
  obtain ⟨U, hzU, g, hg⟩ := exists_isLocalEquation_preimage π hD' z
  exact ⟨U, hzU, hnorm m D' hD'eq U g hg⟩

end MMP.Mori

end QCartier

/-! ### Smoothness and regularity over a field -/

section Smooth

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace MMP

/-- A scheme smooth of relative dimension `n` over a field has topological Krull dimension `n`
at every point: the structure morphism has a single fibre, the scheme itself. -/
private theorem topologicalKrullDimAt_eq_of_smoothOfRelativeDimension
    {k : Type u} [Field k] {X : Scheme.{u}} (n : ℕ)
    (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension n f] (x : X) :
    topologicalKrullDimAt X x = n := by
  let e : f.fiber (f x) ≃ₜ X := (f.fiberHomeo (f x)).trans
    ((Homeomorph.setCongr (Set.eq_univ_of_forall fun y => Subsingleton.elim (f y) (f x))).trans
      (Homeomorph.Set.univ X))
  rw [← f.fiberι_asFiber x, ← fiberDimensionAt_eq_of_smoothOfRelativeDimension f n x]
  exact (topologicalKrullDimAt_eq_of_homeomorph e (f.asFiber x)).symm

/-- Let `f : X ⟶ Spec k` be a scheme over a field `k`.
1. If `f` is smooth, `X` is regular.
2. If `f` is smooth, then for every field extension `K / k` the base change `X ×_k K` is regular.
3. If `k` is perfect, `f` is locally of finite type and `X` is regular, then `f` is smooth.
4. If the base change of `f` to some field extension `K / k` is smooth, then `f` is smooth.
5. If `f` is of finite type and smooth of relative dimension two, `X` is a regular surface. -/
@[mmp "lem_mmp_resolution_smooth_regular_field_dictionary"]
public theorem isRegular_of_smooth_of_field {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) :
    (Smooth f → IsRegular X) ∧
    (Smooth f → ∀ (K : Type u) [Field K] [Algebra k K],
      IsRegular (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))))) ∧
    (∀ [PerfectField k] [LocallyOfFiniteType f], IsRegular X → Smooth f) ∧
    (∀ (K : Type u) [Field K] [Algebra k K],
      Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) → Smooth f) ∧
    (∀ [QuasiCompact f] [LocallyOfFiniteType f], SmoothOfRelativeDimension 2 f →
      Resolution.IsRegularSurface X) := by
  refine ⟨fun _ => isRegular_of_smooth_over_field f,
    fun _ K _ _ => isRegular_of_smooth_over_field (pullback.snd f _),
    fun hX => (MMP.mem_smoothLocus_iff_isRegularLocalRing_of_perfectField f).2.2
      ((isRegular_iff_regular_stalks X).1 hX).2,
    fun K _ _ h => smooth_of_smooth_pullback_snd_spec_algebraMap k K f h, fun h2 => ?_⟩
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : Smooth f := SmoothOfRelativeDimension.smooth 2 f
  refine ⟨{ }, isRegularLocalRing_stalk_of_smooth_over_field f, fun x hx => ?_⟩
  rw [← topologicalKrullDimAt_eq_ringKrullDim_stalk_of_closed_point f x hx,
    topologicalKrullDimAt_eq_of_smoothOfRelativeDimension 2 f x]
  rfl

/-- A smooth proper scheme of dimension at most one over a field `K` is projective over `K`. -/
@[mmp "lem_mmp_fa15_smooth_proper_curve_projective"]
public theorem isProjective_of_smooth_of_isProper_of_topologicalKrullDim_le_one
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [Smooth f] [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) : IsProjective f :=
  isProjective_of_isRegular_of_topologicalKrullDim_le_two f
    ((MMP.isRegular_of_smooth_of_field f).1 inferInstance) (hdim.trans (by norm_num))

end MMP

end Smooth

/-! ### The tame canonical-order formula -/

section TameOrder

open CategoryTheory AlgebraicGeometry

namespace MMP.Mori

section Algebra

open IsLocalRing KaehlerDifferential TensorProduct

/-- If `f` is onto modulo `x₀` (its kernel lies in `R ∙ x₀`) and the `f (y i)` span, then `x₀` and
the `y i` span. -/
private theorem span_cons_eq_top_of_ker_le {R V Q : Type*} [CommRing R] [AddCommGroup V]
    [Module R V] [AddCommGroup Q] [Module R Q] (f : V →ₗ[R] Q) (x₀ : V)
    (hker : LinearMap.ker f ≤ R ∙ x₀)
    {r : ℕ} (y : Fin r → V) (hy : Submodule.span R (Set.range (f ∘ y)) = ⊤) :
    Submodule.span R (Set.range (Fin.cons x₀ y : Fin (r + 1) → V)) = ⊤ := by
  refine eq_top_iff.mpr fun v _ => ?_
  have hv : f v ∈ (Submodule.span R (Set.range y)).map f := by
    rw [Submodule.map_span, ← Set.range_comp, hy]; trivial
  obtain ⟨w, hw, hfw⟩ := hv
  have hsub : Submodule.span R (Set.range y) ≤
      Submodule.span R (Set.range (Fin.cons x₀ y : Fin (r + 1) → V)) :=
    Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨i.succ, by simp⟩)
  have h0 : R ∙ x₀ ≤ Submodule.span R (Set.range (Fin.cons x₀ y : Fin (r + 1) → V)) :=
    Submodule.span_mono (by rintro _ rfl; exact ⟨0, by simp⟩)
  have : v - w ∈ LinearMap.ker f := by simp [hfw]
  have := h0 (hker this)
  simpa using Submodule.add_mem _ this (hsub hw)

/-- The wedge of a spanning family of `n` vectors generates the `n`-th exterior power. -/
private theorem span_singleton_ιMulti_eq_top {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] {n : ℕ} (v : Fin n → M) (hv : Submodule.span R (Set.range v) = ⊤) :
    Submodule.span R {exteriorPower.ιMulti R n v} = ⊤ := by
  refine eq_top_iff.mpr ((exteriorPower.ιMulti_span_of_span R n M hv).symm.le.trans ?_)
  rw [Submodule.span_le]
  rintro _ ⟨a, ha, rfl⟩
  choose g hg using fun i => ha (Set.mem_range_self i)
  obtain rfl : a = v ∘ g := funext fun i => (hg i).symm
  by_cases hinj : Function.Injective g
  · let σ := Equiv.ofBijective g (Finite.injective_iff_bijective.mp hinj)
    have : v ∘ g = v ∘ σ := rfl
    rw [this, AlternatingMap.map_perm]
    exact Submodule.smul_of_tower_mem _ _ (Submodule.mem_span_singleton_self _)
  · simp only [Function.Injective, not_forall] at hinj
    obtain ⟨i, j, hij, hne⟩ := hinj
    rw [AlternatingMap.map_eq_zero_of_eq _ _ (show (v ∘ g) i = (v ∘ g) j by simp [hij]) hne]
    exact Submodule.zero_mem _

/-- Changing the first vector by an element of the span of the others, and scaling it, scales the
wedge. -/
private theorem ιMulti_cons_eq_smul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {r : ℕ} (y : Fin r → M) {x x' : M} (c : R) (hx : x - c • x' ∈ Submodule.span R (Set.range y)) :
    exteriorPower.ιMulti R (r + 1) (Fin.cons x y) =
      c • exteriorPower.ιMulti R (r + 1) (Fin.cons x' y) := by
  let L : M →ₗ[R] ⋀[R]^(r + 1) M :=
    (exteriorPower.ιMulti R (r + 1)).toMultilinearMap.toLinearMap (Fin.cons 0 y) 0
  have hL : ∀ z, L z = exteriorPower.ιMulti R (r + 1) (Fin.cons z y) := fun z => by
    simp [L, MultilinearMap.toLinearMap_apply, Fin.update_cons_zero]
  have hker : Submodule.span R (Set.range y) ≤ LinearMap.ker L := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, hL]
    exact AlternatingMap.map_eq_zero_of_eq _ _ (i := 0) (j := i.succ) (by simp)
      (Fin.succ_ne_zero i).symm
  have := hker hx
  rw [LinearMap.mem_ker, map_sub, map_smul, sub_eq_zero] at this
  rw [← hL, ← hL, this]

/-- For a local ring with principal maximal ideal `(π)`, the kernel of
`κ ⊗ Ω_{R/k} → Ω_{κ/k}` is spanned by `1 ⊗ dπ`. -/
private theorem ker_mapBaseChange_le {k R : Type*} [CommRing k] [CommRing R] [IsLocalRing R]
    [Algebra k R] {π : R} (hπ : maximalIdeal R = Ideal.span {π}) :
    LinearMap.ker (mapBaseChange k R (ResidueField R)) ≤
      (ResidueField R) ∙ ((1 : ResidueField R) ⊗ₜ[R] D k R π) := by
  intro y hy
  obtain ⟨z, rfl⟩ := (exact_kerCotangentToTensor_mapBaseChange k R _ (residue_surjective) y).mp hy
  obtain ⟨⟨x, hx⟩, rfl⟩ := Ideal.toCotangent_surjective _ z
  have hx' : x ∈ maximalIdeal R := by
    rw [← ker_residue]; exact hx
  rw [hπ] at hx'
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hx'
  rw [kerCotangentToTensor_toCotangent, Derivation.leibniz, tmul_add, tmul_smul, tmul_smul,
    ← algebraMap_smul (ResidueField R) π, ← algebraMap_smul (ResidueField R) a]
  have : algebraMap R (ResidueField R) π = 0 := by
    rw [← RingHom.mem_ker, IsLocalRing.ResidueField.algebraMap_eq, ker_residue, hπ]
    exact Ideal.mem_span_singleton_self π
  rw [this, zero_smul, add_zero]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- If `R` and its residue field are formally smooth over `k`, then `1 ⊗ dπ ≠ 0` in
`κ ⊗ Ω_{R/k}` for `π ∈ 𝔪 \ 𝔪²`. -/
private theorem tmul_D_ne_zero {k R : Type*} [CommRing k] [CommRing R] [IsLocalRing R]
    [Algebra k R] [Algebra.FormallySmooth k R] [Algebra.FormallySmooth k (ResidueField R)]
    {π : R} (hπ : π ∈ maximalIdeal R) (hπ2 : π ∉ maximalIdeal R ^ 2) :
    ((1 : ResidueField R) ⊗ₜ[R] D k R π) ≠ 0 := by
  obtain ⟨l, hl⟩ := (Algebra.FormallySmooth.iff_split_injection (R := k) (P := R)
    (A := ResidueField R) residue_surjective).mp inferInstance
  intro h0
  have hker : RingHom.ker (algebraMap R (ResidueField R)) = maximalIdeal R := by
    rw [IsLocalRing.ResidueField.algebraMap_eq, ker_residue]
  have hmem : π ∈ RingHom.ker (algebraMap R (ResidueField R)) := hker ▸ hπ
  have h1 : kerCotangentToTensor k R (ResidueField R)
      ((RingHom.ker (algebraMap R (ResidueField R))).toCotangent ⟨π, hmem⟩) = 0 := by
    rwa [kerCotangentToTensor_toCotangent]
  have h2 := congrArg l h1
  rw [← LinearMap.comp_apply, hl, LinearMap.id_apply, map_zero, Ideal.toCotangent_eq_zero] at h2
  apply hπ2
  rw [← hker]
  exact h2

/-- Nakayama for a free module of rank `r`: `r` vectors spanning `κ ⊗ M` span `M`. -/
private theorem span_eq_top_of_span_tmul {R M : Type*} [CommRing R] [IsLocalRing R] [AddCommGroup M]
    [Module R M] [Module.Finite R M] [Module.Free R M] {r : ℕ} (hr : Module.finrank R M = r)
    (v : Fin r → M)
    (hv : Submodule.span (ResidueField R) (Set.range fun i => (1 : ResidueField R) ⊗ₜ[R] v i) = ⊤) :
    Submodule.span R (Set.range v) = ⊤ := by
  have hfr : Module.finrank (ResidueField R) (ResidueField R ⊗[R] M) = r := by
    rw [Module.finrank_baseChange, hr]
  let b := basisOfTopLeSpanOfCardEqFinrank _ hv.ge (by simp [hfr])
  exact span_eq_top_of_tmul_eq_basis v b (fun i => by simp [b])

/-- In a discrete valuation ring, an irreducible element does not lie in `𝔪²`. -/
private theorem irreducible_notMem_maximalIdeal_sq {A : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] {t : A} (ht : Irreducible t) : t ∉ maximalIdeal A ^ 2 := by
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer t).mp ht, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]
  rintro ⟨c, hc⟩
  have : t * (1 - t * c) = 0 := by linear_combination hc
  rcases mul_eq_zero.mp this with h | h
  · exact ht.ne_zero h
  · exact ht.not_isUnit (isUnit_iff_exists_inv.mpr ⟨c, by linear_combination -h⟩)

/-- Over a field of characteristic zero, replacing the factor `D s` of a spanning wedge by
`D (a s^(e+1))`, for `s` in the maximal ideal and a unit `a`, scales it by a unit times `s^e`. -/
private theorem exists_ιMulti_cons_D_eq_unit_mul_pow_smul {k B : Type*} [Field k] [CharZero k]
    [CommRing B] [IsLocalRing B] [Algebra k B] {r : ℕ} {s : B} (hs : s ∈ maximalIdeal B)
    (w : Fin r → Ω[B⁄k])
    (hv : Submodule.span B (Set.range (Fin.cons (D k B s) w : Fin (r + 1) → Ω[B⁄k])) = ⊤)
    (a : Bˣ) (e : ℕ) :
    ∃ u : Bˣ, exteriorPower.ιMulti B (r + 1) (Fin.cons (D k B (a * s ^ (e + 1))) w) =
      ((u : B) * s ^ e) • exteriorPower.ιMulti B (r + 1) (Fin.cons (D k B s) w) := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun B).mp
    (hv ▸ Submodule.mem_top : D k B (a : B) ∈
      Submodule.span B (Set.range (Fin.cons (D k B s) w : Fin (r + 1) → Ω[B⁄k])))
  have hsm : s * c 0 ∈ maximalIdeal B := Ideal.mul_mem_right _ _ hs
  have hek : IsUnit ((e + 1 : ℕ) : B) := by
    have : ((e + 1 : ℕ) : B) = algebraMap k B ((e + 1 : ℕ) : k) := by simp
    rw [this]
    exact (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero e))).map _
  have hu : IsUnit ((a : B) * ((e + 1 : ℕ) : B) + s * c 0) := by
    by_contra h
    have := (maximalIdeal B).sub_mem ((mem_maximalIdeal _).mpr h) hsm
    rw [add_sub_cancel_right, mem_maximalIdeal] at this
    exact this (a.isUnit.mul hek)
  refine ⟨hu.unit, ?_⟩
  rw [IsUnit.unit_spec]
  apply ιMulti_cons_eq_smul
  rw [Derivation.leibniz, Derivation.leibniz_pow, ← hc, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Nat.add_sub_cancel]
  have : (a : B) • ((e + 1) • s ^ e • D k B s) +
      s ^ (e + 1) • (c 0 • D k B s + ∑ i : Fin r, c i.succ • w i) -
      ((↑a * ((e + 1 : ℕ) : B) + s * c 0) * s ^ e) • D k B s =
      s ^ (e + 1) • ∑ i : Fin r, c i.succ • w i := by
    rw [← Nat.cast_smul_eq_nsmul B]
    module
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

/-- **The tame computation.** For a local extension `A → B` of discrete valuation rings over a
field `k` of characteristic zero, with `Ω_{A/k}` and `Ω_{B/k}` free of rank `n` and separable
residue extension, if `t ↦ a s^e` for uniformizers `t`, `s` and a unit `a`, then some generators
of the top forms satisfy `h^* σ_A = w s^{e-1} σ_B` for a unit `w`. -/
private theorem exists_topFormsMap_eq_unit_mul_pow_smul {k A B : Type*} [Field k] [CharZero k]
    [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B] [IsLocalHom (algebraMap A B)]
    [Algebra.FormallySmooth k A] [Algebra.FormallySmooth k (ResidueField A)]
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)]
    [Module.Free A Ω[A⁄k]] [Module.Finite A Ω[A⁄k]] [Module.Free B Ω[B⁄k]] [Module.Finite B Ω[B⁄k]]
    {n : ℕ} (hA : Module.finrank A Ω[A⁄k] = n) (hB : Module.finrank B Ω[B⁄k] = n)
    {t : A} (ht : Irreducible t) {s : B} (hs : Irreducible s) {a : Bˣ} {e : ℕ}
    (he : algebraMap A B t = a * s ^ e) :
    ∃ σA : ⋀[A]^n Ω[A⁄k], Submodule.span A {σA} = ⊤ ∧
      ∃ σB : ⋀[B]^n Ω[B⁄k], Submodule.span B {σB} = ⊤ ∧
        ∃ w : Bˣ, topFormsMap k A B n σA = ((w : B) * s ^ (e - 1)) • σB := by
  classical
  have htm : t ∈ maximalIdeal A := (mem_maximalIdeal t).mpr ht.not_isUnit
  have hmA : maximalIdeal A = Ideal.span {t} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer t).mp ht
  have hmB : maximalIdeal B = Ideal.span {s} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer s).mp hs
  have hx₀ := tmul_D_ne_zero (k := k) htm (irreducible_notMem_maximalIdeal_sq ht)
  have hV : Module.finrank (ResidueField A) (ResidueField A ⊗[A] Ω[A⁄k]) = n := by
    rw [Module.finrank_baseChange, hA]
  obtain ⟨r, rfl⟩ : ∃ r, n = r + 1 := Nat.exists_eq_succ_of_ne_zero fun h0 => by
    rw [h0, Module.finrank_zero_iff] at hV
    exact hx₀ (Subsingleton.elim _ _)
  let fA := mapBaseChange k A (ResidueField A)
  have hfA : Function.Surjective fA := mapBaseChange_surjective k A _ residue_surjective
  have hfx₀ : fA ((1 : ResidueField A) ⊗ₜ[A] D k A t) = 0 := by
    simp [fA, mapBaseChange_tmul, (residue_eq_zero_iff t).mpr htm]
  have hkerA : LinearMap.ker fA = ResidueField A ∙ ((1 : ResidueField A) ⊗ₜ[A] D k A t) :=
    le_antisymm (ker_mapBaseChange_le hmA)
      ((Submodule.span_singleton_le_iff_mem _ _).mpr hfx₀)
  have hQ : Module.finrank (ResidueField A) Ω[ResidueField A⁄k] = r := by
    have h := LinearMap.finrank_range_add_finrank_ker fA
    rw [LinearMap.range_eq_top.mpr hfA, finrank_top, hkerA, finrank_span_singleton hx₀, hV] at h
    omega
  have : Module.Finite (ResidueField A) Ω[ResidueField A⁄k] := Module.Finite.of_surjective fA hfA
  have hspanQ : Submodule.span (ResidueField A)
      (Set.range fun x : A => D k (ResidueField A) (algebraMap A (ResidueField A) x)) = ⊤ := by
    refine eq_top_iff.mpr ((span_range_derivation k (ResidueField A)).symm.le.trans
      (Submodule.span_mono ?_))
    rintro _ ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := residue_surjective y
    exact ⟨x, rfl⟩
  obtain ⟨b, hbs, hbspan, hbli⟩ := exists_linearIndependent (ResidueField A)
    (Set.range fun x : A => D k (ResidueField A) (algebraMap A (ResidueField A) x))
  let bb := Module.Basis.mk hbli (by rw [Subtype.range_coe, hbspan, hspanQ])
  have : Finite b := Module.Finite.finite_basis bb
  have : Fintype b := Fintype.ofFinite b
  let eqv : Fin r ≃ b :=
    (Fintype.equivFinOfCardEq (by rw [← Module.finrank_eq_card_basis bb, hQ])).symm
  have hu : ∀ i, ∃ x : A, D k (ResidueField A) (algebraMap A (ResidueField A) x) = (eqv i).1 :=
    fun i => hbs (eqv i).2
  choose u hu using hu
  let bQ : Module.Basis (Fin r) (ResidueField A) Ω[ResidueField A⁄k] := bb.reindex eqv.symm
  have hbQ : ∀ i, bQ i = D k (ResidueField A) (algebraMap A (ResidueField A) (u i)) := fun i => by
    simp only [bQ, bb, Module.Basis.reindex_apply, Module.Basis.mk_apply, Equiv.symm_symm]
    exact (hu i).symm
  have hu' : Submodule.span (ResidueField A)
      (Set.range (fA ∘ fun i => (1 : ResidueField A) ⊗ₜ[A] D k A (u i))) = ⊤ := by
    rw [← bQ.span_eq]; congr 1; ext x
    simp [fA, mapBaseChange_tmul, hbQ]
  have hVspan := span_cons_eq_top_of_ker_le fA _ hkerA.le _ hu'
  set vA : Fin (r + 1) → Ω[A⁄k] := Fin.cons (D k A t) fun i => D k A (u i) with hvA_def
  have hvA : Submodule.span A (Set.range vA) = ⊤ := by
    refine span_eq_top_of_span_tmul hA vA ?_
    have : (fun i => (1 : ResidueField A) ⊗ₜ[A] vA i) =
        Fin.cons ((1 : ResidueField A) ⊗ₜ[A] D k A t) fun i => 1 ⊗ₜ[A] D k A (u i) := by
      funext i; cases i using Fin.cases <;> simp [vA]
    rw [this]; exact hVspan
  -- the side of `B`
  have : Algebra.FormallyEtale (ResidueField A) (ResidueField B) :=
    Algebra.FormallyEtale.of_isSeparable _ _
  let fB := mapBaseChange k B (ResidueField B)
  let bQ' := (KaehlerDifferential.isBaseChange_of_formallyEtale k (ResidueField A)
    (ResidueField B)).basis bQ
  have hu'B : Submodule.span (ResidueField B)
      (Set.range (fB ∘ fun i => (1 : ResidueField B) ⊗ₜ[B] D k B (algebraMap A B (u i)))) = ⊤ := by
    rw [← bQ'.span_eq]; congr 1; ext x
    simp [fB, bQ', mapBaseChange_tmul, hbQ, IsBaseChange.basis_apply]
  have hWspan := span_cons_eq_top_of_ker_le fB _ (ker_mapBaseChange_le (k := k) hmB) _ hu'B
  set vB : Fin (r + 1) → Ω[B⁄k] := Fin.cons (D k B s) fun i => D k B (algebraMap A B (u i))
    with hvB_def
  have hvB : Submodule.span B (Set.range vB) = ⊤ := by
    refine span_eq_top_of_span_tmul hB vB ?_
    have : (fun i => (1 : ResidueField B) ⊗ₜ[B] vB i) =
        Fin.cons ((1 : ResidueField B) ⊗ₜ[B] D k B s)
          fun i => 1 ⊗ₜ[B] D k B (algebraMap A B (u i)) := by
      funext i; cases i using Fin.cases <;> simp [vB]
    rw [this]; exact hWspan
  refine ⟨_, span_singleton_ιMulti_eq_top vA hvA, _, span_singleton_ιMulti_eq_top vB hvB, ?_⟩
  rw [topFormsMap_ιMulti]
  have hcomp : (fun i => KaehlerDifferential.map k k A B (vA i)) =
      Fin.cons (D k B (algebraMap A B t)) fun i => D k B (algebraMap A B (u i)) := by
    funext i; cases i using Fin.cases <;> simp [vA]
  rw [hcomp]
  obtain ⟨e, rfl⟩ : ∃ e', e = e' + 1 := Nat.exists_eq_succ_of_ne_zero fun h0 => by
    rw [h0, pow_zero, mul_one] at he
    exact ht.not_isUnit ((isUnit_map_iff (algebraMap A B) t).mp (he ▸ a.isUnit))
  rw [he, Nat.add_sub_cancel]
  exact exists_ιMulti_cons_D_eq_unit_mul_pow_smul ((mem_maximalIdeal s).mpr hs.not_isUnit) _ hvB
    a e

end Algebra

/-- A rational function regular along `E` pulls back to one regular along `E'`. -/
private theorem ord_functionFieldMap_nonneg {Y Y' : Scheme.{u}} (h : Y' ⟶ Y) [IsIntegral Y]
    [IsIntegral Y'] [IsLocallyNoetherian Y] [IsLocallyNoetherian Y'] [IsNormal Y] [IsNormal Y']
    [IsDominant h] (E : PrimeDivisor Y) (E' : PrimeDivisor Y')
    (hEE' : h E'.genericPoint = E.genericPoint) {g : Y.functionField} (hg : g ≠ 0)
    (h0 : 0 ≤ Y.ord g E.genericPoint) : 0 ≤ Y'.ord (functionFieldMap h g) E'.genericPoint := by
  have hne : functionFieldMap h g ≠ 0 := (map_ne_zero _).mpr hg
  have h1 : E.divisorialValuation g ≤ 1 := by
    rw [E.divisorialValuation_eq_exp_neg_ord hg, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  obtain ⟨r, hr⟩ := (E.divisorialValuation_le_one_iff g).mp h1
  have hsp : h E'.genericPoint ⤳ E.genericPoint := hEE' ▸ specializes_rfl
  have h2 : E'.divisorialValuation (functionFieldMap h g) ≤ 1 := by
    rw [E'.divisorialValuation_le_one_iff]
    refine ⟨(h.stalkMap E'.genericPoint).hom ((Y.presheaf.stalkSpecializes hsp).hom r), ?_⟩
    rw [← functionFieldMap_algebraMap_stalk, algebraMap_stalkSpecializes, ← hr]
  rw [E'.divisorialValuation_eq_exp_neg_ord hne, ← WithZero.exp_zero, WithZero.exp_le_exp] at h2
  omega

/-- The order of an inverse: `v_z(g⁻¹) = -v_z(g)`. -/
private theorem ord_inv {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] (z : X)
    {g : X.functionField} (hg : g ≠ 0) : X.ord g⁻¹ z = -X.ord g z := by
  simpa using ord_zpow z hg (-1)

/-- A rational function that is a unit along `E` pulls back to a unit along `E'`. -/
private theorem ord_functionFieldMap_eq_zero {Y Y' : Scheme.{u}} (h : Y' ⟶ Y) [IsIntegral Y]
    [IsIntegral Y'] [IsLocallyNoetherian Y] [IsLocallyNoetherian Y'] [IsNormal Y] [IsNormal Y']
    [IsDominant h] (E : PrimeDivisor Y) (E' : PrimeDivisor Y')
    (hEE' : h E'.genericPoint = E.genericPoint) {g : Y.functionField} (hg : g ≠ 0)
    (h0 : Y.ord g E.genericPoint = 0) : Y'.ord (functionFieldMap h g) E'.genericPoint = 0 := by
  have h1 := ord_functionFieldMap_nonneg h E E' hEE' hg h0.ge
  have h2 := ord_functionFieldMap_nonneg h E E' hEE' (inv_ne_zero hg)
    (by rw [ord_inv _ hg, h0, neg_zero])
  rw [map_inv₀, ord_inv _ ((map_ne_zero _).mpr hg)] at h2
  omega

/-- The order along `E'` of the pull-back of a rational function is `e` times its order along
`E`, where `e` is the order of the pull-back of a uniformizer. -/
private theorem ord_functionFieldMap_eq_mul {Y Y' : Scheme.{u}} (h : Y' ⟶ Y) [IsIntegral Y]
    [IsIntegral Y'] [IsLocallyNoetherian Y] [IsLocallyNoetherian Y'] [IsNormal Y] [IsNormal Y']
    [IsDominant h] (E : PrimeDivisor Y) (E' : PrimeDivisor Y')
    (hEE' : h E'.genericPoint = E.genericPoint)
    {t : Y.functionField} (ht : Y.ord t E.genericPoint = 1) {f : Y.functionField} (hf : f ≠ 0) :
    Y'.ord (functionFieldMap h f) E'.genericPoint =
      Y'.ord (functionFieldMap h t) E'.genericPoint * Y.ord f E.genericPoint := by
  have htne : t ≠ 0 := by
    rintro rfl
    simp at ht
  set q := Y.ord f E.genericPoint
  set g := f * t ^ (-q) with hgdef
  have hgne : g ≠ 0 := mul_ne_zero hf (zpow_ne_zero _ htne)
  have hg' := ord_functionFieldMap_eq_zero h E E' hEE' hgne (by
    rw [hgdef, Scheme.ord_mul hf (zpow_ne_zero _ htne), ord_zpow _ htne, ht]
    ring)
  have hhg : functionFieldMap h g ≠ 0 := (map_ne_zero _).mpr hgne
  have hf' : f = g * t ^ q := by
    rw [hgdef, mul_assoc, ← zpow_add₀ htne, neg_add_cancel, zpow_zero, mul_one]
  have hhtne : functionFieldMap h t ≠ 0 := (map_ne_zero _).mpr htne
  rw [hf', map_mul, map_zpow₀, Scheme.ord_mul hhg (zpow_ne_zero _ hhtne), ord_zpow _ hhtne, hg']
  ring

/-- Pulling a form back along `A → K → K'` agrees with pulling it back along `A → B → K'` when
the two composites `A → K'` agree. -/
private theorem topFormsMap_topFormsMap_eq {k A B K K' : Type*} [CommRing k] [CommRing A]
    [CommRing B] [Field K] [Field K'] [Algebra k A] [Algebra k B] [Algebra k K] [Algebra k K']
    [Algebra A B] [Algebra A K] [Algebra B K'] [Algebra K K'] [IsScalarTower k A B]
    [IsScalarTower k A K] [IsScalarTower k B K'] [IsScalarTower k K K']
    (hφ : ∀ x : A, algebraMap B K' (algebraMap A B x) = algebraMap K K' (algebraMap A K x))
    {n : ℕ} (σ : ⋀[A]^n Ω[A⁄k]) :
    topFormsMap k K K' n (topFormsMap k A K n σ) =
      topFormsMap k B K' n (topFormsMap k A B n σ) := by
  have hΩ : ∀ y : Ω[A⁄k], KaehlerDifferential.map k k K K' (KaehlerDifferential.map k k A K y) =
      KaehlerDifferential.map k k B K' (KaehlerDifferential.map k k A B y) := by
    intro y
    have hy : y ∈ Submodule.span A (Set.range (KaehlerDifferential.D k A)) := by
      rw [KaehlerDifferential.span_range_derivation]; trivial
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      simp [hφ]
    | zero => simp
    | add x y _ _ hx hy => simp only [map_add, hx, hy]
    | smul a x _ hx =>
      have e1 : KaehlerDifferential.map k k A K (a • x) =
          algebraMap A K a • KaehlerDifferential.map k k A K x := by
        rw [map_smul, algebraMap_smul]
      have e2 : KaehlerDifferential.map k k A B (a • x) =
          algebraMap A B a • KaehlerDifferential.map k k A B x := by
        rw [map_smul, algebraMap_smul]
      rw [e1, e2, map_smul, map_smul, hx, ← algebraMap_smul K' (algebraMap A K a),
        ← algebraMap_smul K' (algebraMap A B a), hφ]
  have hs : σ ∈ Submodule.span A (Set.range (exteriorPower.ιMulti A n)) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    simp only [topFormsMap_ιMulti, hΩ]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul a x _ hx =>
    have e1 : topFormsMap k A K n (a • x) = algebraMap A K a • topFormsMap k A K n x := by
      rw [map_smul, algebraMap_smul]
    have e2 : topFormsMap k A B n (a • x) = algebraMap A B a • topFormsMap k A B n x := by
      rw [map_smul, algebraMap_smul]
    rw [e1, e2, map_smul, map_smul, hx, ← algebraMap_smul K' (algebraMap A K a),
      ← algebraMap_smul K' (algebraMap A B a), hφ]

/-- The order along a prime divisor of `u ϖ^n`, for a unit `u` and a uniformizer `ϖ`, is `n`. -/
private theorem ord_algebraMap_unit_mul_pow {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (E : PrimeDivisor Y) {ϖ : E.localRing} (hϖ : Irreducible ϖ)
    (w : E.localRingˣ) (n : ℕ) :
    Y.ord (algebraMap E.localRing Y.functionField (w * ϖ ^ n)) E.genericPoint = n := by
  have := E.isDiscreteValuationRing_localRing
  have hϖ0 : algebraMap E.localRing Y.functionField ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hϖ.ne_zero
  have h1 : Y.ord (algebraMap E.localRing Y.functionField ϖ) E.genericPoint = 1 := by
    have := E.divisorialValuation_algebraMap_of_irreducible hϖ
    rw [E.divisorialValuation_eq_exp_neg_ord hϖ0] at this
    have := WithZero.exp_injective this
    omega
  have hw0 : algebraMap E.localRing Y.functionField w ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr w.ne_zero
  rw [map_mul, map_pow, Scheme.ord_mul hw0 (pow_ne_zero _ hϖ0),
    E.ord_algebraMap_of_isUnit w.isUnit, ← zpow_natCast, ord_zpow _ hϖ0, h1]
  ring

/-- **The tame canonical-order formula for top forms** (the case `m = 1`). -/
private theorem ordForm_pullback_one {k : Type u} [Field k] [CharZero k]
    {Y Y' : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) (h : Y' ⟶ Y) [IsIntegral Y] [IsIntegral Y']
    [IsLocallyNoetherian Y] [IsLocallyNoetherian Y'] [IsFinite h] [Surjective h]
    (hY : IsNormalVariety k sY) (hY' : IsNormalVariety k (h ≫ sY)) {n : ℕ}
    (hdimY : topologicalKrullDim Y = n) (hdimY' : topologicalKrullDim Y' = n)
    (E : PrimeDivisor Y) (E' : PrimeDivisor Y') (hEE' : h E'.genericPoint = E.genericPoint)
    {t : Y.functionField} (ht : Y.ord t E.genericPoint = 1)
    {τ : RationalPluriForms sY n 1} (hτ : τ ≠ 0) :
    E'.ordForm (pullbackRationalPluriForms sY h τ) =
      Y'.ord (functionFieldMap h t) E'.genericPoint * E.ordForm τ +
        (Y'.ord (functionFieldMap h t) E'.genericPoint - 1) := by
  have := hY.1
  have := hY'.1
  have : IsNormal Y := hY.2
  have : IsNormal Y' := hY'.2
  have : IsDominant h := inferInstance
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sY) hdimY
  have hd' := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := h ≫ sY) hdimY'
  let := stalkAlgebra sY E.genericPoint
  let := stalkAlgebra (h ≫ sY) E'.genericPoint
  let := functionFieldAlgebra sY
  let := functionFieldAlgebra (h ≫ sY)
  let := functionFieldMapAlgebra h
  have := isScalarTower_stalk_functionField sY E.genericPoint
  have := isScalarTower_stalk_functionField (h ≫ sY) E'.genericPoint
  have := isScalarTower_functionFieldMap sY h
  have := E.isDiscreteValuationRing_localRing
  have := E'.isDiscreteValuationRing_localRing
  obtain ⟨_, _⟩ := E.formallySmooth_localRing (sX := sY)
  obtain ⟨_, _⟩ := E.free_kaehlerDifferential_localRing (sX := sY)
  obtain ⟨_, _⟩ := E'.free_kaehlerDifferential_localRing (sX := h ≫ sY)
  have hrkA := (E.finrank_kaehlerDifferential_localRing (sX := sY)).trans hd
  have hrkB := (E'.finrank_kaehlerDifferential_localRing (sX := h ≫ sY)).trans hd'
  have hsp : h E'.genericPoint ⤳ E.genericPoint := hEE' ▸ specializes_rfl
  let φ : E.localRing →+* E'.localRing :=
    (Y.presheaf.stalkSpecializes hsp ≫ h.stalkMap E'.genericPoint).hom
  let := φ.toAlgebra
  have hφ : ∀ x : E.localRing, algebraMap E'.localRing Y'.functionField (algebraMap _ _ x) =
      algebraMap Y.functionField Y'.functionField (algebraMap E.localRing Y.functionField x) := by
    intro x
    change algebraMap _ _ ((h.stalkMap E'.genericPoint).hom
      ((Y.presheaf.stalkSpecializes hsp).hom x)) = functionFieldMap h _
    rw [← functionFieldMap_algebraMap_stalk, algebraMap_stalkSpecializes]
  have : IsScalarTower k E.localRing E'.localRing := by
    refine IsScalarTower.of_algebraMap_eq fun c =>
      IsFractionRing.injective E'.localRing Y'.functionField ?_
    rw [← IsScalarTower.algebraMap_apply k E'.localRing Y'.functionField,
      IsScalarTower.algebraMap_apply k Y.functionField Y'.functionField,
      IsScalarTower.algebraMap_apply k E.localRing Y.functionField, hφ]
  have hins : Inseparable E.genericPoint (h E'.genericPoint) := hEE' ▸ Inseparable.rfl
  have hiso : IsIso (Y.presheaf.stalkSpecializes hsp) :=
    (Y.presheaf.stalkCongr hins).isIso_hom
  have hloc : IsLocalHom (Y.presheaf.stalkSpecializes hsp).hom := inferInstance
  have : IsLocalHom (algebraMap E.localRing E'.localRing) := by
    change IsLocalHom (CommRingCat.Hom.hom
      (Y.presheaf.stalkSpecializes hsp ≫ h.stalkMap E'.genericPoint))
    rw [CommRingCat.hom_comp]
    infer_instance
  have : Algebra.FormallySmooth k (IsLocalRing.ResidueField E.localRing) := by
    have : Algebra.EssFiniteType k (IsLocalRing.ResidueField E.localRing) :=
      Algebra.EssFiniteType.comp k E.localRing _
    have : CharZero (IsLocalRing.ResidueField E.localRing) :=
      charZero_of_injective_algebraMap (algebraMap k _).injective
    exact Algebra.FormallySmooth.of_perfectField
  have : Algebra.IsSeparable (IsLocalRing.ResidueField E.localRing)
      (IsLocalRing.ResidueField E'.localRing) := by
    have : Algebra.IsAlgebraic (IsLocalRing.ResidueField E.localRing)
        (IsLocalRing.ResidueField E'.localRing) := by
      have h1 : (h.residueFieldMap E'.genericPoint).hom.Finite :=
        MMP.moduleFinite_residueField h E'.genericPoint
      have hsurj : Function.Surjective (Y.presheaf.stalkSpecializes hsp).hom :=
        (ConcreteCategory.bijective_of_isIso (Y.presheaf.stalkSpecializes hsp)).2
      let ψ := IsLocalRing.ResidueField.map (Y.presheaf.stalkSpecializes hsp).hom
      have h2 : ψ.Finite := by
        refine RingHom.Finite.of_surjective ψ fun y => ?_
        obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective y
        obtain ⟨a, rfl⟩ := hsurj b
        exact ⟨IsLocalRing.residue _ a, IsLocalRing.ResidueField.map_residue _ a⟩
      have h3 : algebraMap (IsLocalRing.ResidueField E.localRing)
          (IsLocalRing.ResidueField E'.localRing) =
          (h.residueFieldMap E'.genericPoint).hom.comp ψ := by
        refine RingHom.ext fun y => ?_
        obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
        change IsLocalRing.ResidueField.map φ (IsLocalRing.residue _ a) =
          (h.residueFieldMap E'.genericPoint).hom (ψ (IsLocalRing.residue _ a))
        rw [IsLocalRing.ResidueField.map_residue, IsLocalRing.ResidueField.map_residue]
        rfl
      have h4 : (algebraMap (IsLocalRing.ResidueField E.localRing)
          (IsLocalRing.ResidueField E'.localRing)).Finite := by
        rw [h3]; exact h1.comp h2
      have : Module.Finite (IsLocalRing.ResidueField E.localRing)
          (IsLocalRing.ResidueField E'.localRing) := RingHom.finite_algebraMap.mp h4
      exact Algebra.IsAlgebraic.of_finite _ _
    have : CharZero (IsLocalRing.ResidueField E.localRing) :=
      charZero_of_injective_algebraMap (algebraMap k _).injective
    exact Algebra.IsAlgebraic.isSeparable_of_perfectField
  -- uniformizers
  have htne : t ≠ 0 := by
    rintro rfl
    simp at ht
  obtain ⟨t₀, rfl⟩ : t ∈ (algebraMap E.localRing Y.functionField).range := by
    rw [← E.divisorialValuation_le_one_iff, E.divisorialValuation_eq_exp_neg_ord htne,
      ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible E.localRing
  have ht₀ne : t₀ ≠ 0 := by
    rintro rfl
    simp at htne
  obtain ⟨n₀, u₀, hu₀⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ht₀ne hϖ
  rw [hu₀, ord_algebraMap_unit_mul_pow E hϖ] at ht
  have hn₀ : n₀ = 1 := by exact_mod_cast ht
  have ht₀ : Irreducible t₀ := by
    rw [hu₀, hn₀, pow_one]; exact (irreducible_units_mul u₀).mpr hϖ
  obtain ⟨s, hs⟩ := IsDiscreteValuationRing.exists_irreducible E'.localRing
  have hφt : algebraMap E.localRing E'.localRing t₀ ≠ 0 := by
    intro h0
    have := hφ t₀
    rw [h0, map_zero, eq_comm, map_eq_zero_iff _ (RingHom.injective _)] at this
    exact htne this
  obtain ⟨e₀, a, ha⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hφt hs
  have he₀ : 1 ≤ e₀ := by
    rcases Nat.eq_zero_or_pos e₀ with h0 | h0
    · rw [h0, pow_zero, mul_one] at ha
      exact absurd ((isUnit_map_iff (algebraMap E.localRing E'.localRing) t₀).mp
        (ha ▸ a.isUnit)) ht₀.not_isUnit
    · exact h0
  have hfm : ∀ x, functionFieldMap h x = algebraMap Y.functionField Y'.functionField x :=
    fun _ => rfl
  have he : Y'.ord (functionFieldMap h (algebraMap E.localRing Y.functionField t₀))
      E'.genericPoint = e₀ := by
    rw [hfm, ← hφ, ha, ord_algebraMap_unit_mul_pow E' hs]
  have hmul := fun {f : Y.functionField} (hf : f ≠ 0) =>
    ord_functionFieldMap_eq_mul h E E' hEE' (t := algebraMap E.localRing Y.functionField t₀)
      (by rw [hu₀, hn₀]; exact_mod_cast ord_algebraMap_unit_mul_pow E hϖ u₀ 1) hf
  rw [he]
  obtain ⟨σA, hσA, σB, hσB, w, hw⟩ :=
    exists_topFormsMap_eq_unit_mul_pow_smul (k := k) hrkA hrkB ht₀ hs ha
  have h0A := E.topFormsMap_ne_zero (sX := sY) hd hσA
  have h0B := E'.topFormsMap_ne_zero (sX := h ≫ sY) hd' hσB
  rw [E.ordForm_eq τ hσA h0A, E'.ordForm_eq _ hσB h0B]
  set c : Y'.functionField := algebraMap E'.localRing Y'.functionField (w * s ^ (e₀ - 1))
    with hc_def
  have hc : c ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
      (mul_ne_zero w.ne_zero (pow_ne_zero _ hs.ne_zero))
  have hcomp : topFormsMap k Y.functionField Y'.functionField n
      (topFormsMap k E.localRing Y.functionField n σA) =
      c • topFormsMap k E'.localRing Y'.functionField n σB := by
    rw [topFormsMap_topFormsMap_eq hφ, hw, map_smul, algebraMap_smul]
  have hωA : IsPullbackGenerator Y'.functionField
      (topFormsMap k E.localRing Y.functionField n σA) :=
    ⟨span_singleton_topFormsMap (nonZeroDivisors _) hσA, by
      rw [hcomp, Submodule.span_singleton_smul_eq (IsUnit.mk0 c hc),
        span_singleton_topFormsMap (nonZeroDivisors _) hσB], by
      rw [hcomp]; exact smul_ne_zero hc h0B⟩
  have hpb : pullbackRationalPluriForms sY h τ = pullbackFormsAlong hωA 1 τ :=
    pullbackForms_eq hωA 1 τ
  rw [hpb]
  have hb : basisOfSpanSingleton hωA.2.1 hωA.2.2 () =
      c • topFormsBasis E'.localRing hσB h0B () := by
    simp [hcomp]
  have key := ZTensorPower.basis_repr_of_eq_smul hb 1 (pullbackFormsAlong hωA 1 τ)
  have hfB : formCoeff E'.localRing hσB h0B (pullbackFormsAlong hωA 1 τ) =
      c * algebraMap Y.functionField Y'.functionField
        (formCoeff (m := 1) E.localRing hσA h0A τ) := by
    have h1 : formCoeff E'.localRing hσB h0B (pullbackFormsAlong hωA 1 τ) =
        c * (ZTensorPower.basis (basisOfSpanSingleton hωA.2.1 hωA.2.2) 1).repr
          (pullbackFormsAlong hωA 1 τ) () := by
      unfold formCoeff
      rw [key, zpow_one, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
    rw [h1, repr_pullbackFormsAlong hωA 1 τ]
    rfl
  have hf : formCoeff (m := 1) E.localRing hσA h0A τ ≠ 0 := fun h0 =>
    hτ ((formCoeff_eq_zero_iff hσA h0A _).mp h0)
  rw [hfB, Scheme.ord_mul hc ((map_ne_zero _).mpr hf), ← hfm, hmul hf, he, hc_def,
    ord_algebraMap_unit_mul_pow E' hs, Nat.cast_sub he₀]
  push_cast
  ring

/-- **The tame canonical-order formula.** Let `h : Y' ⟶ Y` be a finite surjective morphism of
normal varieties of dimension `n` over a field `k` of characteristic zero, `Y'` being a variety
over `k` through `h ≫ s_Y`. Let `E'` be a prime divisor of `Y'` over a prime divisor `E` of `Y`,
`t` a uniformizer at `E` and `e = ord_{E'}(h^* t)`. Then every nonzero rational `m`-canonical
form `τ` of degree `n` on `Y` satisfies `ord_{E'}(h^* τ) = e · ord_E(τ) + m (e - 1)`. -/
@[mmp "lem_mmp_finite_char_zero_tame_canonical_order"]
public theorem ordForm_pullbackRationalPluriForms_of_finite {k : Type u} [Field k] [CharZero k]
    {Y Y' : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) (h : Y' ⟶ Y) [IsIntegral Y] [IsIntegral Y']
    [IsLocallyNoetherian Y] [IsLocallyNoetherian Y'] [IsFinite h] [Surjective h]
    (hY : IsNormalVariety k sY) (hY' : IsNormalVariety k (h ≫ sY)) {n : ℕ}
    (hdimY : topologicalKrullDim Y = n) (hdimY' : topologicalKrullDim Y' = n)
    (E : PrimeDivisor Y) (E' : PrimeDivisor Y') (hEE' : h E'.genericPoint = E.genericPoint)
    {t : Y.functionField} (ht : Y.ord t E.genericPoint = 1) {m : ℤ}
    {τ : RationalPluriForms sY n m} (hτ : τ ≠ 0) :
    E'.ordForm (pullbackRationalPluriForms sY h τ) =
      Y'.ord (functionFieldMap h t) E'.genericPoint * E.ordForm τ +
        m * (Y'.ord (functionFieldMap h t) E'.genericPoint - 1) := by
  have := hY.1
  have := hY'.1
  have : IsNormal Y := hY.2
  have : IsNormal Y' := hY'.2
  have : IsDominant h := inferInstance
  let := functionFieldAlgebra sY
  let := functionFieldAlgebra (h ≫ sY)
  let := functionFieldMapAlgebra h
  have := isScalarTower_functionFieldMap sY h
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sY) hdimY
  have hd' := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := h ≫ sY) hdimY'
  have := essFiniteType_functionField (sX := sY)
  have htr : Algebra.trdeg k Y.functionField = Algebra.trdeg k Y'.functionField := by
    have h1 := (toENat_trdeg_functionField (sX := sY)).trans hdimY
    have h2 := (toENat_trdeg_functionField (sX := h ≫ sY)).trans hdimY'
    have h1' : Cardinal.toENat (Algebra.trdeg k Y.functionField) = n := by exact_mod_cast h1
    have h2' : Cardinal.toENat (Algebra.trdeg k Y'.functionField) = n := by exact_mod_cast h2
    rw [Cardinal.toENatAux_eq_nat.mp h1', Cardinal.toENatAux_eq_nat.mp h2']
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator (k := k) (K := Y.functionField)
    (K' := Y'.functionField) htr hd
  set b := basisOfSpanSingleton hω.1 hω.ne_zero
  set b' := basisOfSpanSingleton hω.2.1 hω.2.2
  obtain ⟨N, hN⟩ := E.exists_ordForm_eq_ord_add_mul hd b
  obtain ⟨N', hN'⟩ := E'.exists_ordForm_eq_ord_add_mul hd' b'
  have hpb : ∀ {m : ℤ} (τ : RationalPluriForms sY n m),
      pullbackRationalPluriForms sY h τ = pullbackFormsAlong hω m τ :=
    fun τ => pullbackForms_eq hω _ τ
  have hrepr : ∀ {m : ℤ} (τ : RationalPluriForms sY n m),
      (ZTensorPower.basis b' m).repr (pullbackRationalPluriForms sY h τ) () =
        functionFieldMap h ((ZTensorPower.basis b m).repr τ ()) := fun τ => by
    rw [hpb]
    exact repr_pullbackFormsAlong hω _ τ
  have hne : ∀ {m : ℤ} (τ : RationalPluriForms sY n m), τ ≠ 0 →
      (ZTensorPower.basis b m).repr τ () ≠ 0 := fun τ hτ hc =>
    hτ ((ZTensorPower.basis b _).repr.map_eq_zero_iff.mp (Finsupp.ext fun u => by simpa using hc))
  have hne' : ∀ {m : ℤ} (τ : RationalPluriForms sY n m), τ ≠ 0 →
      pullbackRationalPluriForms sY h τ ≠ 0 := fun τ hτ h0 => by
    have := hrepr τ
    rw [h0] at this
    erw [LinearEquiv.map_zero] at this
    rw [Finsupp.zero_apply, eq_comm, map_eq_zero_iff _ (RingHom.injective _)] at this
    exact hne τ hτ this
  set e := Y'.ord (functionFieldMap h t) E'.genericPoint
  have hv : ∀ {m : ℤ} (τ : RationalPluriForms sY n m), τ ≠ 0 →
      E'.ordForm (pullbackRationalPluriForms sY h τ) =
        e * Y.ord ((ZTensorPower.basis b m).repr τ ()) E.genericPoint + m * N' := fun τ hτ => by
    rw [hN' _ _ (hne' τ hτ), hrepr, ord_functionFieldMap_eq_mul h E E' hEE' ht (hne τ hτ)]
  -- the case `m = 1` along the basis form `ω` computes `N'`
  set τ₁ : RationalPluriForms sY n 1 := ZTensorPower.basis b 1 ()
  have hτ₁ : τ₁ ≠ 0 := (ZTensorPower.basis b 1).ne_zero ()
  have h1 : (ZTensorPower.basis b 1).repr τ₁ () = 1 := by simp [τ₁]
  have key := ordForm_pullback_one sY h hY hY' hdimY hdimY' E E' hEE' ht hτ₁
  rw [hv τ₁ hτ₁, hN 1 τ₁ hτ₁, h1, ord_one] at key
  rw [hv τ hτ, hN m τ hτ]
  have hN'eq : N' = e * N + (e - 1) := by linarith
  rw [hN'eq]
  ring

end MMP.Mori

end TameOrder

/-! ### The singular locus -/

section SingularLocus

open CategoryTheory AlgebraicGeometry

namespace MMP

/-- For an integral scheme `X` locally of finite type over a perfect field `k`, the singular locus
is a proper closed subset and the smooth locus is dense; and on any scheme `Y` smooth over `k`
every stalk is a regular local ring and an integral domain. -/
@[mmp "lem_mmp_foundation_laz_singular_locus_proper_closed"]
public theorem singularLocus_ne_top_and_dense_smoothLocus {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] :
    (Mori.singularLocus f ≠ ⊤ ∧ Dense (Mori.smoothLocus f : Set X)) ∧
      ∀ {Y : Scheme.{u}} (g : Y ⟶ Spec (.of k)), Mori.IsSmoothScheme g →
        ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y) ∧ IsDomain (Y.presheaf.stalk y) := by
  refine ⟨?_, fun {Y} g hg y => ?_⟩
  · have hgen : genericPoint X ∈ MMP.Mori.smoothLocus f := by
      rw [Mori.smoothLocus_eq_smoothLocus,
        (mem_smoothLocus_iff_isRegularLocalRing_of_perfectField f).1]
      exact inferInstanceAs (IsRegularLocalRing X.functionField)
    exact ⟨fun h => (h ▸ trivial : genericPoint X ∈ (MMP.Mori.singularLocus f : Set X)) hgen,
      (MMP.Mori.smoothLocus f).isOpen.dense ⟨_, hgen⟩⟩
  · obtain ⟨U, hyU, hU⟩ := MMP.Mori.mem_smoothLocus_iff.mp
      (hg ▸ trivial : y ∈ MMP.Mori.smoothLocus g)
    have := ((mem_smoothLocus_iff_isRegularLocalRing_of_perfectField (U.ι ≫ g)).1 ⟨y, hyU⟩).1 <| by
      rw [Scheme.Hom.smoothLocus_eq_top_iff.mpr hU]; trivial
    have := IsRegularLocalRing.of_ringEquiv (U.stalkIso ⟨y, hyU⟩).commRingCatIsoToRingEquiv
    exact ⟨this, IsRegularLocalRing.isDomain _⟩

end MMP

end SingularLocus
