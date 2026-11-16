module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Divisor.LinearSystem
public import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
public import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
public import MMP.AlgebraicGeometry.Intersection.Nef
public import MMP.AlgebraicGeometry.MMP.Abundance.Defs
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.OpenRestriction
import MMP.AlgebraicGeometry.Positivity.LogResolutionAmpleApproximation
import MMP.AlgebraicGeometry.Positivity.NefBigOfAmpleApproximation
import MMP.AlgebraicGeometry.MMP.MinimalModel.NefWeakModelStep
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.SurfaceMatrix
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
import MMP.AlgebraicGeometry.ChowForm.FibreDegreeRank
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal
import MMP.AlgebraicGeometry.MMP.Abundance.LogElliptic.GenericFibreDegree

/-!
# Global sections along a birational contraction

Let `c : Y ⟶ Z` be a proper birational morphism of normal varieties over a field `k`, with `Z`
proper over `k`, and `D` a divisor on `Y` whose birational transform `c_* D` is Cartier. A
rational function `φ ∈ k(Y) = k(Z)` with `div_Y φ + D ≥ 0` has `div_Z φ + c_* D ≥ 0`, because
`c_*` preserves effectivity and `c_* div_Y φ = div_Z φ` (KM §2.a). Hence
`H⁰(Y, 𝒪_Y(D)) ⊆ H⁰(Z, 𝒪_Z(c_* D))` and `h⁰(Y, D) ≤ h⁰(Z, c_* D)`.

## Main results

* `MMP.Mori.Divisor.h0_le_h0_transformDivisor`: `h⁰(Y, 𝒪_Y(D)) ≤ h⁰(Z, 𝒪_Z(c_* D))`.
* `MMP.Mori.exists_two_le_h0_transformDivisor`,
  `MMP.Mori.exists_two_le_h0_of_isPullback_transformDivisor`: a Cartier multiple with
  `h⁰ ≥ 2` survives birational transform, and pull-back across a roof of birational models.
* `MMP.Mori.QDivisor.isNef_of_isPullback_of_surjective`: nefness descends along a surjective
  proper morphism.
* `MMP.Mori.QDivisor.isNef_of_qLinearlyEquivalent`: nefness is invariant under `ℚ`-linear
  equivalence.
* `MMP.Flips.IsLogEllipticFiberSpace.exists_of_isOpenImmersion`: a log elliptic fiber space
  transports along an open immersion.

## Implementation notes

Sections of `𝒪_Z(c_* D)` over `Z` are pulled back to `Y` componentwise by the stalk maps of `c`
at the generic point; this is injective and `Γ(Z, 𝒪_Z)`-semilinear along `c^♯`. Every section of
`𝒪_Y(D)` is in its image: a nonzero section is a unit `χ` of `k(Y)` with `div χ + D ≥ 0`, which
is the pull-back of a unit `ψ` of `k(Z)` (`MMP.Fourfold.exists_pullbackRationalFunction_eq`), and
`ψ` is a section of `𝒪_Z(c_* D)` by `MMP.Positivity.transformDivisor_principalDivisor_pullback`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], §2.a
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

namespace MMP.Mori

section PullTop

variable {Y Z : Scheme.{0}} [IsIntegral Y] [IsIntegral Z] (c : Y ⟶ Z) [IsDominant c]

private theorem map_componentGenericPoint_eq' (W : irreducibleComponents Y) :
    componentGenericPoint Z (pointComponent (c (componentGenericPoint Y W))) =
      c (componentGenericPoint Y W) := by
  rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint,
    MMP.Fourfold.componentGenericPoint_eq_genericPoint, map_genericPoint_of_isDominant]

/-- `𝒪_{Z,c(η_W)} ≅ 𝒪_{Z,η}`: `c` maps the generic point of `Y` to that of `Z`. -/
private noncomputable def stalkEquivTop (W : irreducibleComponents Y) :
    Z.presheaf.stalk (c (componentGenericPoint Y W)) ≃+*
      Z.presheaf.stalk (componentGenericPoint Z (pointComponent (c (componentGenericPoint Y W)))) :=
  RingEquiv.ofBijective (stalkToRationalFunctions Z (mem_pointComponent _)).hom (by
    have h := map_componentGenericPoint_eq' c W
    unfold stalkToRationalFunctions
    generalize_proofs hs
    revert hs
    rw [h]
    intro hs
    rw [TopCat.Presheaf.stalkSpecializes_refl]
    exact Function.bijective_id)

/-- The pull-back `c^* : 𝒦_Z(Z) → 𝒦_Y(Y)` of rational functions along a dominant morphism of
integral schemes, componentwise by the stalk maps of `c`. -/
private noncomputable def ratPullTop :
    (rationalFunctionsPresheaf Z).obj (op ⊤) →+* (rationalFunctionsPresheaf Y).obj (op ⊤) :=
  Pi.ringHom fun W => (c.stalkMap (componentGenericPoint Y W.1)).hom.comp
    ((stalkEquivTop c W.1).symm.toRingHom.comp
      (Pi.evalRingHom (fun W' : {W' : irreducibleComponents Z //
          componentGenericPoint Z W' ∈ (⊤ : Z.Opens)} =>
        Z.presheaf.stalk (componentGenericPoint Z W'.1))
        ⟨pointComponent (c (componentGenericPoint Y W.1)), trivial⟩))

private theorem ratPullTop_apply (φ : (rationalFunctionsPresheaf Z).obj (op ⊤))
    (W : {W : irreducibleComponents Y // componentGenericPoint Y W ∈ (⊤ : Y.Opens)}) :
    ratPullTop c φ W = (c.stalkMap (componentGenericPoint Y W.1)).hom
      ((stalkEquivTop c W.1).symm
        (φ ⟨pointComponent (c (componentGenericPoint Y W.1)), trivial⟩)) :=
  rfl

/-- `c^*` sends the germ of a regular function to the germ of its pull-back. -/
private theorem ratPullTop_toRationalFunctionsPresheaf (r : Γ(Z, ⊤)) :
    ratPullTop c ((toRationalFunctionsPresheaf Z).app (op ⊤) r) =
      (toRationalFunctionsPresheaf Y).app (op ⊤) (c.appTop r) := by
  funext W
  rw [ratPullTop_apply, toRationalFunctionsPresheaf_app_apply,
    toRationalFunctionsPresheaf_app_apply]
  have h1 : (stalkEquivTop c W.1).symm
      ((Z.presheaf.germ ⊤ (componentGenericPoint Z (pointComponent _)) trivial).hom r) =
      (Z.presheaf.germ ⊤ (c (componentGenericPoint Y W.1)) trivial).hom r := by
    rw [RingEquiv.symm_apply_eq]
    exact (TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _).symm
  rw [h1]
  exact Scheme.Hom.germ_stalkMap_apply c ⊤ _ trivial r

/-- `c^*` is semilinear along `c^♯ : Γ(Z, 𝒪_Z) → Γ(Y, 𝒪_Y)`. -/
private theorem ratPullTop_smul [IsLocallyNoetherian Z] [IsNormal Z] [IsLocallyNoetherian Y]
    [IsNormal Y] (r : Γ(Z, ⊤)) (φ : (rationalFunctionsPresheaf Z).obj (op ⊤)) :
    ratPullTop c (r • φ) = c.appTop r • ratPullTop c φ := by
  change ratPullTop c ((toRationalFunctionsPresheaf Z).app (op ⊤) r * φ) =
    (toRationalFunctionsPresheaf Y).app (op ⊤) (c.appTop r) * ratPullTop c φ
  rw [map_mul, ratPullTop_toRationalFunctionsPresheaf]

/-- `c^*` is injective on `𝒦_Z(Z)`. -/
private theorem ratPullTop_injective : Function.Injective (ratPullTop c) := by
  intro φ ψ h
  have hsub := MMP.Fourfold.subsingleton_irreducibleComponents (X := Z)
  obtain ⟨y⟩ : Nonempty Y := inferInstance
  set W₀ := pointComponent y
  have h0 := congrFun h ⟨W₀, trivial⟩
  rw [ratPullTop_apply, ratPullTop_apply] at h0
  have hinj : Function.Injective (c.stalkMap (componentGenericPoint Y W₀)).hom := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0
    have hu : IsUnit x := by
      have h2 : stalkEquivTop c W₀ x ≠ 0 := fun h3 =>
        hx0 ((map_eq_zero_iff _ (stalkEquivTop c W₀).injective).mp h3)
      have := (isUnit_of_ne_zero_stalk _ h2).map (stalkEquivTop c W₀).symm.toRingHom
      simpa using this
    have := hu.map (c.stalkMap (componentGenericPoint Y W₀)).hom
    rw [hx] at this
    exact not_isUnit_zero this
  have h1 := (stalkEquivTop c W₀).symm.injective (hinj h0)
  funext W
  obtain ⟨W, hW⟩ := W
  obtain rfl : pointComponent (c (componentGenericPoint Y W₀)) = W := Subsingleton.elim _ _
  exact h1

/-- `c^*` on units of `k(Z)` is `MMP.Mori.pullbackRationalFunction`. -/
private theorem ratPullTop_unit [IsLocallyNoetherian Z] [IsNormal Z] [CompactSpace Z]
    [IsLocallyNoetherian Y] [IsNormal Y]
    (ψ : (RationalFunctions Z)ˣ)
    (hψ : ∀ W : irreducibleComponents Y, c (componentGenericPoint Y W) ∉ (principalDivisor ψ).supp)
    (W : {W : irreducibleComponents Y // componentGenericPoint Y W ∈ (⊤ : Y.Opens)}) :
    ratPullTop c (fun W => (ψ : RationalFunctions Z) W.1) W =
      (pullbackRationalFunction c ψ hψ : RationalFunctions Y) W.1 := by
  refine (ratPullTop_apply c _ W).trans ?_
  obtain ⟨a, ha⟩ := (Divisor.isLocalEquation_principalDivisor ψ ⊤).exists_unit_stalk
    (y := c (componentGenericPoint Y W.1)) trivial (hψ W.1) (mem_pointComponent _)
  change _ = ((pullbackComponent c hψ (Divisor.isLocalEquation_principalDivisor ψ ⊤) W.1
    trivial : (Y.presheaf.stalk (componentGenericPoint Y W.1))ˣ) :
      Y.presheaf.stalk (componentGenericPoint Y W.1))
  rw [pullbackComponent_eq hψ (Divisor.isLocalEquation_principalDivisor ψ ⊤) trivial
    (mem_pointComponent _) a ha]
  change _ = (c.stalkMap (componentGenericPoint Y W.1)).hom (a : Z.presheaf.stalk _)
  congr 1
  rw [RingEquiv.symm_apply_eq]
  exact ha.symm

end PullTop

section H0

variable {k : Type} [Field k]

private theorem exists_ratPullTop_eq {Y Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of k)}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [IsIntegral Z]
    [IsLocallyNoetherian Z] [IsNormal Z] [CompactSpace Z] [IsProper sZ]
    (hZ : IsNormalVariety k sZ) {c : Y ⟶ Z} [IsProper c] [IsDominant c]
    (hY : IsNormalVariety k (c ≫ sZ)) (hb : IsBirationalMorphism c) {D : Divisor Y}
    (σ : D.divisorialSubmodule ⊤) :
    ∃ s : Divisor.divisorialSubmodule
        (RationalMap.transformDivisor c.toRationalMap D : Divisor Z) ⊤,
      ratPullTop c s.1 = σ.1 := by
  classical
  set D' : Divisor Z := RationalMap.transformDivisor c.toRationalMap D
  obtain ⟨y⟩ : Nonempty Y := inferInstance
  by_cases hσ : σ = 0
  · refine ⟨0, ?_⟩
    rw [hσ]
    exact map_zero _
  obtain ⟨χ, hχ, hχD⟩ := MMP.Fourfold.exists_unit_of_divisorialSubmodule_ne_zero
    (V := ⊤) ⟨y, trivial⟩ σ hσ
  obtain ⟨ψ, hψ, hψχ⟩ := MMP.Fourfold.exists_pullbackRationalFunction_eq hb χ
  have heff : 0 ≤ D + principalDivisor χ := fun E => by
    change (0 : ℤ) ≤ D.coeff E + (principalDivisor χ).coeff E
    rw [coeff_principalDivisor]
    exact hχD E ((E.genericPoint_mem_iff ⊤).mp trivial)
  have hpush := RationalMap.transformDivisor_nonneg c.toRationalMap heff
  rw [map_add, ← hψχ, MMP.Positivity.transformDivisor_principalDivisor_pullback hZ hY hb ψ hψ]
    at hpush
  refine ⟨⟨fun W => (ψ : RationalFunctions Z) W.1,
    MMP.Fourfold.isDivisorialSection_of_unit ψ fun P _ => ?_⟩, ?_⟩
  · have := hpush P
    change (0 : ℤ) ≤ D'.coeff P + (principalDivisor ψ).coeff P at this
    rwa [coeff_principalDivisor] at this
  · change ratPullTop c (fun W => (ψ : RationalFunctions Z) W.1) = σ.1
    funext W
    rw [ratPullTop_unit c ψ hψ, hψχ]
    exact (hχ W.1 trivial).symm

/-- **Global sections along a birational contraction.** Let `c : Y ⟶ Z` be a proper birational
morphism of normal varieties over `k`, `Z` proper over `k`, and `D` a divisor on `Y` whose
birational transform `c_* D` is Cartier. Then `h⁰(Y, 𝒪_Y(D)) ≤ h⁰(Z, 𝒪_Z(c_* D))`. -/
theorem Divisor.h0_le_h0_transformDivisor {Y Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of k)}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Z] [IsLocallyNoetherian Z]
    [IsNormal Z] [CompactSpace Z] [IsProper sZ] (hZ : IsNormalVariety k sZ) {c : Y ⟶ Z}
    [IsProper c] (hY : IsNormalVariety k (c ≫ sZ)) (hb : IsBirationalMorphism c) (D : Divisor Y)
    (hD : Divisor.IsCartier (RationalMap.transformDivisor c.toRationalMap D : Divisor Z)) :
    D.h0 k (c ≫ sZ) ≤
      Divisor.h0 k sZ (RationalMap.transformDivisor c.toRationalMap D : Divisor Z) := by
  classical
  haveI : IsDominant c := hb.isDominant
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace c
  set D' : Divisor Z := RationalMap.transformDivisor c.toRationalMap D
  have hpre : ∀ σ : D.divisorialSubmodule ⊤,
      ∃ s : D'.divisorialSubmodule ⊤, ratPullTop c s.1 = σ.1 := exists_ratPullTop_eq hZ hY hb
  choose Ψf hΨf using hpre
  have hsc : ∀ a : k, c.appTop (scalarsToGlobalSections k sZ a) =
      scalarsToGlobalSections k (c ≫ sZ) a := by
    intro a
    simp only [scalarsToGlobalSections, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
      RingHom.comp_apply]
  have hinj : ∀ s t : D'.divisorialSubmodule ⊤, ratPullTop c s.1 = ratPullTop c t.1 → s = t :=
    fun s t h => Subtype.ext (ratPullTop_injective c h)
  unfold Divisor.h0
  letI := Module.compHom (D.divisorialSubmodule ⊤) (scalarsToGlobalSections k (c ≫ sZ))
  letI := Module.compHom (D'.divisorialSubmodule ⊤) (scalarsToGlobalSections k sZ)
  haveI : Module.Finite k (D'.divisorialSubmodule ⊤) :=
    Divisor.finite_divisorialSubmodule_top sZ hD
  let Ψ : D.divisorialSubmodule ⊤ →ₗ[k] D'.divisorialSubmodule ⊤ :=
    { toFun := Ψf
      map_add' := fun σ τ => hinj _ _ (by
        rw [hΨf, Submodule.coe_add, Submodule.coe_add, map_add, hΨf, hΨf])
      map_smul' := fun a σ => hinj _ _ (by
        change ratPullTop c (Ψf (scalarsToGlobalSections k (c ≫ sZ) a • σ)).1 =
          ratPullTop c (scalarsToGlobalSections k sZ a • Ψf σ).1
        rw [hΨf, Submodule.coe_smul, Submodule.coe_smul, ratPullTop_smul, hΨf, hsc]) }
  have hΨ : Function.Injective Ψ := fun σ τ h => Subtype.ext (by
    rw [← hΨf σ, ← hΨf τ]
    exact congrArg (fun s : D'.divisorialSubmodule ⊤ => ratPullTop c s.1) h)
  exact LinearMap.finrank_le_finrank_of_injective hΨ

/-- The birational transform along a birational morphism of normal varieties commutes with
regarding divisors as `ℚ`-divisors. -/
theorem transformDivisor_toQDivisor {Y Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of k)}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsLocallyNoetherian Z] [IsNormal Z]
    (hZ : IsNormalVariety k sZ) {c : Y ⟶ Z}
    [IsProper c] (hY : IsNormalVariety k (c ≫ sZ)) (hb : IsBirationalMorphism c) (D : Divisor Y) :
    RationalMap.transformDivisor c.toRationalMap (Divisor.toQDivisor D) =
      Divisor.toQDivisor (RationalMap.transformDivisor c.toRationalMap D : Divisor Z) := by
  refine Finsupp.ext fun P => ?_
  obtain ⟨E, -, -, hE⟩ := MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hZ hY
    hb P
  rw [hE]
  change ((D E : ℤ) : ℚ) =
    (((RationalMap.transformDivisor c.toRationalMap D : Divisor Z) P : ℤ) : ℚ)
  rw [hE]

omit [Field k] in
/-- A divisor with a nonzero global section has a nonzero global section of every multiple. -/
private theorem exists_ne_zero_zsmul {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] {D : Divisor Y} (σ : D.divisorialSubmodule ⊤) (hσ : σ ≠ 0) (n : ℕ) :
    ∃ τ : ((n : ℤ) • D).divisorialSubmodule ⊤, τ ≠ 0 := by
  obtain ⟨y⟩ : Nonempty Y := inferInstance
  obtain ⟨χ, -, hχD⟩ := MMP.Fourfold.exists_unit_of_divisorialSubmodule_ne_zero
    (V := ⊤) ⟨y, trivial⟩ σ hσ
  refine ⟨⟨fun W => ((χ ^ (n : ℤ) : (RationalFunctions Y)ˣ) : RationalFunctions Y) W.1,
    MMP.Fourfold.isDivisorialSection_of_unit _ fun P hP => ?_⟩, fun h0 => ?_⟩
  · rw [DivisorWithCoeffs.coeff_smul, PrimeDivisor.ord_zpow, smul_eq_mul, smul_eq_mul, ← mul_add]
    exact mul_nonneg (by positivity) (hχD P hP)
  · have h1 := congrArg (fun t : ((n : ℤ) • D).divisorialSubmodule ⊤ =>
      t.1 ⟨pointComponent y, trivial⟩) h0
    have hu := ((χ ^ (n : ℤ)).isUnit.map (Pi.evalRingHom _ (pointComponent y)))
    exact hu.ne_zero h1

/-- A divisor with `h⁰ > 0` has a nonzero global section. -/
private theorem exists_ne_zero_of_h0_pos {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of k)}
    [IsLocallyNoetherian Y] [IsNormal Y] {D : Divisor Y} (h : 0 < D.h0 k sY) :
    ∃ σ : D.divisorialSubmodule ⊤, σ ≠ 0 := by
  by_contra hne
  simp only [ne_eq, not_exists, not_not] at hne
  haveI : Subsingleton (D.divisorialSubmodule ⊤) := ⟨fun a b => (hne a).trans (hne b).symm⟩
  unfold Divisor.h0 at h
  letI := Module.compHom (D.divisorialSubmodule ⊤) (scalarsToGlobalSections k sY)
  rw [Module.finrank_zero_of_subsingleton] at h
  exact lt_irrefl 0 h

/-- If `M` is Cartier with `h⁰(Y, M) ≥ 2` and `c_*(aM)` is Cartier for some `a > 0`, then
`h⁰(Z, c_*(aM)) ≥ 2`. -/
private theorem two_le_h0_zsmul_transformDivisor {Y Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of k)}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Z] [IsLocallyNoetherian Z]
    [IsNormal Z] [CompactSpace Z] [IsProper sZ] (hZ : IsNormalVariety k sZ) {c : Y ⟶ Z}
    [IsProper c] (hY : IsNormalVariety k (c ≫ sZ)) (hb : IsBirationalMorphism c)
    {M : Divisor Y} (hMc : M.IsCartier) (h2 : 2 ≤ M.h0 k (c ≫ sZ)) {a : ℕ} (ha : 0 < a)
    (haC : Divisor.IsCartier
      ((a : ℤ) • RationalMap.transformDivisor c.toRationalMap M : Divisor Z)) :
    2 ≤ Divisor.h0 k sZ
      ((a : ℤ) • RationalMap.transformDivisor c.toRationalMap M : Divisor Z) := by
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace c
  obtain ⟨σ, hσ⟩ := exists_ne_zero_of_h0_pos (sY := c ≫ sZ) (D := M) (by omega)
  obtain ⟨τ, hτ⟩ := exists_ne_zero_zsmul σ hσ (a - 1)
  have hle : M + ((a - 1 : ℕ) : ℤ) • M ≤ (a : ℤ) • M := by
    rw [show ((a - 1 : ℕ) : ℤ) = (a : ℤ) - 1 by omega, sub_smul, one_smul, add_sub_cancel]
  have h3 := MMP.Mori.Divisor.h0_le_of_add_le (c ≫ sZ) (hMc.zsmul a) hle τ hτ
  have h4 := Divisor.h0_le_h0_transformDivisor hZ hY hb ((a : ℤ) • M)
    (by rw [map_zsmul]; exact haC)
  rw [map_zsmul] at h4
  omega

/-- **Condition (15.4.2) along a birational contraction.** Let `c : Y ⟶ Z` be a proper birational
morphism of normal varieties over `k`, `Z` proper over `k` with every Weil divisor `ℚ`-Cartier,
and `L` a `ℚ`-divisor on `Y`. If some Cartier multiple `M = mL` has `h⁰(Y, M) ≥ 2`, then some
Cartier multiple `M' = m'(c_* L)` has `h⁰(Z, M') ≥ 2`. -/
theorem exists_two_le_h0_transformDivisor {Y Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of k)}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Z] [IsLocallyNoetherian Z]
    [IsNormal Z] [CompactSpace Z] [IsProper sZ] (hZ : IsNormalVariety k sZ) {c : Y ⟶ Z}
    [IsProper c] (hY : IsNormalVariety k (c ≫ sZ)) (hb : IsBirationalMorphism c)
    (hQ : ∀ D : Divisor Z, ∃ m : ℕ, 0 < m ∧ ((m : ℤ) • D).IsCartier) {L : QDivisor Y}
    (h : ∃ m : ℕ, 0 < m ∧ ∃ M : Divisor Y, Divisor.toQDivisor M = (m : ℤ) • L ∧ M.IsCartier ∧
      2 ≤ M.h0 k (c ≫ sZ)) :
    ∃ m : ℕ, 0 < m ∧ ∃ M : Divisor Z,
      Divisor.toQDivisor M = (m : ℤ) • RationalMap.transformDivisor c.toRationalMap L ∧
      M.IsCartier ∧ 2 ≤ M.h0 k sZ := by
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace c
  obtain ⟨m, hm, M, hML, hMc, h2⟩ := h
  obtain ⟨a, ha, haC⟩ := hQ (RationalMap.transformDivisor c.toRationalMap M)
  refine ⟨a * m, Nat.mul_pos ha hm, (a : ℤ) • RationalMap.transformDivisor c.toRationalMap M,
    ?_, haC, ?_⟩
  · rw [map_zsmul, ← transformDivisor_toQDivisor hZ hY hb, hML, map_zsmul, smul_smul]
    push_cast
    rfl
  · exact two_le_h0_zsmul_transformDivisor hZ hY hb hMc h2 ha haC

/-- **Condition (15.4.2) across a roof of birational models** (FA 15.9, Steps 2 and 3). Let
`c : Y ⟶ T` be a proper birational morphism of normal varieties over `k`, `T` proper over `k`,
and `u : Y' ⟶ T` a dominant morphism from a proper normal integral `k`-scheme. Let `L` be a
`ℚ`-divisor on `Y` whose transform `c_* L` is `ℚ`-Cartier with pull-back `L' = u^*(c_* L)`. If
some Cartier multiple `M = mL` has `h⁰(Y, M) ≥ 2`, then some Cartier multiple `M' = m'L'` has
`h⁰(Y', M') ≥ 2`. -/
theorem exists_two_le_h0_of_isPullback_transformDivisor {Y T Y' : Scheme.{0}}
    {sT : T ⟶ Spec (.of k)} {sY' : Y' ⟶ Spec (.of k)} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] [CompactSpace T]
    [IsProper sT] (hT : IsNormalVariety k sT) {c : Y ⟶ T} [IsProper c]
    (hY : IsNormalVariety k (c ≫ sT)) (hb : IsBirationalMorphism c) [IsIntegral Y']
    [IsLocallyNoetherian Y'] [IsNormal Y'] [CompactSpace Y'] [IsProper sY'] (u : Y' ⟶ T)
    (hu : u ≫ sT = sY') [IsDominant u] [QuasiCompact u] {L : QDivisor Y} {L' : QDivisor Y'}
    (hLq : QDivisor.IsQCartier (RationalMap.transformDivisor c.toRationalMap L : QDivisor T))
    {hLB : ∀ W : irreducibleComponents Y',
      u (componentGenericPoint Y' W) ∉ (RationalMap.transformDivisor c.toRationalMap L).supp}
    (hpull : QDivisor.IsPullback u
      (RationalMap.transformDivisor c.toRationalMap L : QDivisor T) hLB L')
    (h : ∃ m : ℕ, 0 < m ∧ ∃ M : Divisor Y, Divisor.toQDivisor M = (m : ℤ) • L ∧ M.IsCartier ∧
      2 ≤ M.h0 k (c ≫ sT)) :
    ∃ m : ℕ, 0 < m ∧ ∃ M' : Divisor Y', Divisor.toQDivisor M' = (m : ℤ) • L' ∧ M'.IsCartier ∧
      2 ≤ M'.h0 k sY' := by
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace c
  obtain ⟨m, hm, M, hML, hMc, h2⟩ := h
  obtain ⟨a, ha, D, hD, hDc⟩ := hLq.exists_pos
  set N := (RationalMap.transformDivisor c.toRationalMap L : QDivisor T)
  have hcM : Divisor.toQDivisor ((a : ℤ) • RationalMap.transformDivisor c.toRationalMap M :
      Divisor T) = ((a * m : ℕ) : ℤ) • N := by
    rw [map_zsmul, ← transformDivisor_toQDivisor hT hY hb, hML, map_zsmul, smul_smul]
    push_cast
    rfl
  have hcMD : ((a : ℤ) • RationalMap.transformDivisor c.toRationalMap M : Divisor T) =
      (m : ℤ) • D := by
    have hq : Divisor.toQDivisor ((a : ℤ) • RationalMap.transformDivisor c.toRationalMap M :
        Divisor T) = Divisor.toQDivisor ((m : ℤ) • D) := by
      rw [hcM, map_zsmul, hD, smul_smul]
      push_cast
      ring_nf
    refine Finsupp.ext fun P => ?_
    have h1 := congrArg (fun G : QDivisor T => G P) hq
    change ((((a : ℤ) • RationalMap.transformDivisor c.toRationalMap M : Divisor T) P : ℤ) : ℚ) =
      ((((m : ℤ) • D : Divisor T) P : ℤ) : ℚ) at h1
    exact_mod_cast h1
  have hcMc : Divisor.IsCartier
      ((a : ℤ) • RationalMap.transformDivisor c.toRationalMap M : Divisor T) := by
    rw [hcMD]; exact hDc.zsmul m
  have hT2 := two_le_h0_zsmul_transformDivisor hT hY hb hMc h2 ha hcMc
  obtain ⟨D', hD', hp⟩ := hpull (a * m) (Nat.mul_pos ha hm) _ hcM hcMc
  have hD'c := hp.isCartier hcMc
  refine ⟨a * m, Nat.mul_pos ha hm, D', hD', hD'c, ?_⟩
  have h5 := Divisor.h0_le_of_iso_pullback u hu hcMc hD'c (hp.divisorialSheafIso (hBc := hcMc))
  omega

end H0

section Nef

variable {k : Type} [Field k]

/-- A closed integral curve `i : C ⟶ Z` of a proper `k`-scheme is, up to isomorphism over `Z`, the
proper curve `{x}⁻` of the image `x` of its generic point. -/
private theorem exists_properCurve_iso {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of k)) [IsProper sZ]
    {C : Scheme.{0}} (i : C ⟶ Z) [IsClosedImmersion i] [IsIntegral C]
    (hC : topologicalKrullDim C = 1) :
    ∃ (C' : ProperCurve sZ) (e : C ≅ C'.scheme), e.hom ≫ C'.ι = i := by
  set x := i (genericPoint C)
  have hcl : closure (Set.range i) = closure ({x} : Set Z) := by
    have h1 : Set.range i = i '' closure ({genericPoint C} : Set C) := by
      rw [(genericPoint_spec C).def, Set.image_univ]
    rw [h1, ← Set.image_singleton]
    exact (closure_image_closure i.continuous)
  have hker : i.ker = (curveSubschemeAtι x).ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.Hom.ker_eq_vanishingIdeal_closure_range]
    congr 1
    exact TopologicalSpace.Closeds.ext (by
      rw [TopologicalSpace.Closeds.coe_closure, TopologicalSpace.Closeds.coe_closure, hcl])
  haveI := IsClosedImmersion.isIso_lift (curveSubschemeAtι x) i hker.symm
  set e := IsClosedImmersion.lift (curveSubschemeAtι x) i hker.symm.le
  have he : e ≫ curveSubschemeAtι x = i := IsClosedImmersion.lift_fac _ _ _
  have hdim : topologicalKrullDim (curveSubschemeAt x) = 1 := by
    rw [← hC]
    exact ((Scheme.homeoOfIso (asIso e)).isHomeomorph.topologicalKrullDim_eq).symm
  exact ⟨⟨x, isProperCurve_of_isProper sZ hdim⟩, asIso e, he⟩

/-- Intersection numbers are unchanged by an isomorphism of curves over `Z`. -/
private theorem intersectionNumber_eq_of_iso_comp' {Z : Scheme.{0}} [IsLocallyNoetherian Z]
    [IsNormal Z] (sZ : Z ⟶ Spec (.of k)) [QuasiCompact sZ] {C C' : Scheme.{0}} (i : C ⟶ Z)
    (i' : C' ⟶ Z) [IsProper (i ≫ sZ)] [IsProper (i' ≫ sZ)] (hdim : topologicalKrullDim C ≤ 1)
    (hdim' : topologicalKrullDim C' ≤ 1) (e : C ≅ C') (he : e.hom ≫ i' = i) (D : QDivisor Z)
    (hD : D.IsQCartier) :
    D.intersectionNumber k sZ i hdim hD = D.intersectionNumber k sZ i' hdim' hD := by
  have := QuasiCompact.compactSpace_of_compactSpace sZ
  unfold QDivisor.intersectionNumber Divisor.degreeOn
  have := (QDivisor.isCartierDivisor_cartierIndex_smul hD).isCartier_toDivisor
    |>.isInvertibleModule_divisorialSheaf
  rw [MMP.Threefold.Resolution.degreeOn_eq_of_iso_comp k sZ i i' hdim hdim' e he]

/-- **Nefness descends along a surjective proper morphism.** Let `c : Y ⟶ Z` be a surjective
proper `k`-morphism, `Y` integral and normal, `Z` normal and proper over `k`, `L` a `ℚ`-Cartier
`ℚ`-divisor on `Z` and `B = c^* L`. If `B` is nef, so is `L`. -/
theorem QDivisor.isNef_of_isPullback_of_surjective {Y Z : Scheme.{0}} {sY : Y ⟶ Spec (.of k)}
    {sZ : Z ⟶ Spec (.of k)} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [LocallyOfFiniteType sY] [QuasiCompact sY] [IsLocallyNoetherian Z] [IsNormal Z]
    [LocallyOfFiniteType sZ] [IsProper sZ] (c : Y ⟶ Z) (hc : c ≫ sZ = sY) [IsProper c]
    [Surjective c] {L : QDivisor Z} (hL : L.IsQCartier)
    {hLB : ∀ W : irreducibleComponents Y, c (componentGenericPoint Y W) ∉ L.supp}
    {B : QDivisor Y} (hB : L.IsPullback c hLB B) (hBn : QDivisor.IsNef k sY B) :
    QDivisor.IsNef k sZ L := by
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  refine ⟨hL, fun C i _ _ _ hC => ?_⟩
  obtain ⟨C', e, he⟩ := exists_properCurve_iso sZ i hC
  rw [intersectionNumber_eq_of_iso_comp' sZ i C'.ι hC.le C'.dim_le e he L hL]
  obtain ⟨C₁, hC₁, hdeg⟩ := MMP.Fourfold.exists_properCurve_map_eq sY sZ c hc C'
  -- the projection formula `(B · C₁) = [k(C₁) : k(C')] (L · C')`
  obtain ⟨D, D', hDc, hDB, hD, hD', hp⟩ := hB.exists_cartierIndex hL
  have hD'c := hp.isCartier hDc
  have := hDc.isInvertibleModule_divisorialSheaf
  have := hD'c.isInvertibleModule_divisorialSheaf
  have hproj : B.intersectionNumber k sY C₁.ι C₁.dim_le (hB.isQCartier hL) =
      (residueFieldDegree c C₁.point : ℚ) * L.intersectionNumber k sZ C'.ι C'.dim_le hL := by
    have hC : IsProperCurve sZ (c C₁.point) := hC₁ ▸ C'.isProperCurve
    have hCC : (⟨c C₁.point, hC⟩ : ProperCurve sZ) = C' := ProperCurve.ext hC₁
    rw [QDivisor.intersectionNumber_eq_of_smul k sY C₁.ι C₁.dim_le _ _
      (QDivisor.cartierIndex_pos hL) D' hD'c hD', Divisor.degreeOn,
      degreeOn_eq_of_iso k sY C₁.ι C₁.dim_le (hp.divisorialSheafIso (hBc := hDc))]
    change ((C₁.degree k ((Scheme.Modules.pullback c).obj D.divisorialSheaf) : ℤ) : ℚ) /
      _ = _
    rw [C₁.degree_pullback c hc, dif_pos hC, hCC,
      QDivisor.intersectionNumber_eq_of_smul k sZ _ _ _ _ (QDivisor.cartierIndex_pos hL) D hDc hD]
    push_cast
    rw [mul_div_assoc]
    rfl
  have hnn := hBn.2 C₁.scheme C₁.ι C₁.dim_eq
  rw [hproj] at hnn
  have hpos : (0 : ℚ) < residueFieldDegree c C₁.point := by
    exact_mod_cast Nat.pos_of_ne_zero hdeg
  exact (mul_nonneg_iff_of_pos_left hpos).mp hnn

/-- `ℚ`-linearly equivalent `ℚ`-divisors on a scheme on which every `ℚ`-divisor is `ℚ`-Cartier
have the same intersection number with every curve `i : C ⟶ X` of dimension `≤ 1` proper over
`k`. -/
theorem QDivisor.intersectionNumber_eq_of_qLinearlyEquivalent {X : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)}
    [QuasiCompact sX] (hQ : ∀ D : QDivisor X, D.IsQCartier) {C : Scheme.{0}} (i : C ⟶ X)
    [IsProper (i ≫ sX)] (hdim : topologicalKrullDim C ≤ 1) {A B : QDivisor X}
    (hAB : A.QLinearlyEquivalent B) :
    A.intersectionNumber k sX i hdim (hQ A) = B.intersectionNumber k sX i hdim (hQ B) := by
  obtain ⟨m, hm, φ, hφ⟩ := hAB
  have hdc := Divisor.isCartier_principalDivisor φ
  have hP : (Divisor.toQDivisor (principalDivisor φ)).intersectionNumber k sX i hdim
      (hQ _) = 0 := by
    rw [QDivisor.intersectionNumber_toQDivisor k sX i hdim _ hdc]
    have := hdc.isInvertibleModule_divisorialSheaf
    have := (Divisor.isCartier_zero (X := X)).isInvertibleModule_divisorialSheaf
    have h1 : (principalDivisor φ).degreeOn k sX i hdim hdc =
        (0 : Divisor X).degreeOn k sX i hdim Divisor.isCartier_zero :=
      degreeOn_eq_of_iso k sX i hdim
        (Divisor.linearlyEquivalent_principalDivisor_zero φ).divisorialSheafIso
    rw [h1, Divisor.degreeOn_zero' k sX i hdim, Int.cast_zero]
  have hsmul := MMP.Fourfold.intersectionNumber_smul sX i hdim (A - B) (hQ _) (m : ℚ) (hQ _)
  have heq : (m : ℚ) • (A - B) = Divisor.toQDivisor (principalDivisor φ) := by
    rw [← hφ, natCast_zsmul, Nat.cast_smul_eq_nsmul]
  rw [MMP.Fourfold.intersectionNumber_congr sX i hdim (hQ _) (hQ _) heq, hP] at hsmul
  have hsub := QDivisor.intersectionNumber_add' k sX i hdim B (A - B) (hQ B) (hQ _) (hQ _)
  rw [MMP.Fourfold.intersectionNumber_congr sX i hdim (hQ _) (hQ A) (add_sub_cancel B A)] at hsub
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [hsub, (mul_eq_zero.1 hsmul.symm).resolve_left hm', add_zero]

/-- Nefness is invariant under `ℚ`-linear equivalence on a scheme on which every `ℚ`-divisor is
`ℚ`-Cartier. -/
theorem QDivisor.isNef_of_qLinearlyEquivalent {X : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)}
    [QuasiCompact sX] (hQ : ∀ D : QDivisor X, D.IsQCartier) {A B : QDivisor X}
    (hAB : A.QLinearlyEquivalent B) (hA : QDivisor.IsNef k sX A) : QDivisor.IsNef k sX B := by
  refine ⟨hQ B, fun C i _ _ _ hC => ?_⟩
  rw [← QDivisor.intersectionNumber_eq_of_qLinearlyEquivalent hQ i hC.le hAB]
  exact hA.2 C i hC

end Nef

end MMP.Mori

universe u

namespace MMP.Flips

open MMP.Mori

section Transport

variable {k : Type u} [Field k]

/-- The residue degree of a composite is that of the second map when the first induces an
isomorphism of residue fields. -/
private theorem residueDegree_comp_of_isIso_left' {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : X) [IsIso (f.residueFieldMap x)] :
    (f ≫ g).residueDegree x = g.residueDegree (f x) := by
  letI : Algebra (Z.residueField (g (f x))) (X.residueField x) :=
    ((f ≫ g).residueFieldMap x).hom.toAlgebra
  letI := (g.residueFieldMap (f x)).hom.toAlgebra
  refine (Algebra.finrank_eq_of_equiv_equiv (R₀ := Z.residueField (g (f x)))
    (S₀ := Y.residueField (f x)) (R₁ := Z.residueField (g (f x))) (S₁ := X.residueField x)
    (RingEquiv.refl _) (asIso (f.residueFieldMap x)).commRingCatIsoToRingEquiv ?_).symm
  ext a
  change ((f ≫ g).residueFieldMap x) a = f.residueFieldMap x (g.residueFieldMap (f x) a)
  rw [Scheme.residueFieldMap_comp]
  rfl

/-- The residue degree of a composite is that of the first map when the second induces an
isomorphism of residue fields. -/
private theorem residueDegree_comp_of_isIso_right' {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : X) [IsIso (g.residueFieldMap (f x))] :
    (f ≫ g).residueDegree x = f.residueDegree x := by
  letI : Algebra (Z.residueField (g (f x))) (X.residueField x) :=
    ((f ≫ g).residueFieldMap x).hom.toAlgebra
  letI := (f.residueFieldMap x).hom.toAlgebra
  refine Algebra.finrank_eq_of_equiv_equiv (R₀ := Z.residueField (g (f x)))
    (S₀ := X.residueField x) (R₁ := Y.residueField (f x)) (S₁ := X.residueField x)
    (asIso (g.residueFieldMap (f x))).commRingCatIsoToRingEquiv (RingEquiv.refl _) ?_
  ext a
  change f.residueFieldMap x (g.residueFieldMap (f x) a) = ((f ≫ g).residueFieldMap x) a
  rw [Scheme.residueFieldMap_comp]
  rfl

/-- The prime divisor map along a composite of open immersions is the composite. -/
theorem primeDivisorMap_eq_of_comp_eq {X Y T : Scheme.{u}} [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] [IsLocallyNoetherian T] (a : X ⟶ Y) [IsOpenImmersion a] (b : Y ⟶ T)
    [IsOpenImmersion b] (c : X ⟶ T) [IsOpenImmersion c] (habc : a ≫ b = c)
    (P : Mori.PrimeDivisor X) :
    OpenWeilRestriction.primeDivisorMap c P =
      OpenWeilRestriction.primeDivisorMap b (OpenWeilRestriction.primeDivisorMap a P) :=
  AlgebraicGeometry.PrimeDivisor.genericPoint_injective (by
    rw [OpenWeilRestriction.genericPoint_primeDivisorMap,
      OpenWeilRestriction.genericPoint_primeDivisorMap,
      OpenWeilRestriction.genericPoint_primeDivisorMap, ← habc]
    rfl)

/-- A contraction is surjective. -/
theorem IsContraction.surjective {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    {sY : Y ⟶ Spec (.of k)} {g : Y ⟶ X} (hg : IsContraction k sX sY g) :
    Function.Surjective g := by
  haveI := hg.isVariety_target.toIsIntegral
  haveI : IsProper g := hg.isProper
  have : IsDominant g := by
    constructor
    by_contra hd
    rw [DenseRange, dense_iff_closure_eq] at hd
    let U' : X.Opens := ⟨(closure (Set.range g))ᶜ, isClosed_closure.isOpen_compl⟩
    have hbot : g ⁻¹ᵁ U' = ⊥ := by
      ext x
      exact iff_of_false (fun hx => hx (subset_closure ⟨x, rfl⟩)) id
    have : Nonempty U' := (Set.nonempty_compl.mpr hd).to_subtype
    have : Subsingleton Γ(Y, g ⁻¹ᵁ U') := by
      rw [hbot]
      infer_instance
    haveI := hg.isIso_app U'
    exact not_subsingleton Γ(X, U')
      (asIso (g.app U')).commRingCatIsoToRingEquiv.injective.subsingleton
  exact g.surjective

section GenericFiber

variable {U V W W₀ : Scheme.{u}} [IsIntegral W] [IsIntegral W₀] (h : U ⟶ V)
  (g : V ⟶ W) (fU : U ⟶ W₀) (ι : W₀ ⟶ W) [IsOpenImmersion ι]

/-- Over an open immersion `ι : W₀ ⟶ W`, the generic fibre of `fU` is the preimage under `h` of
the generic fibre of `g` when `fU ≫ ι = h ≫ g`. -/
theorem preimage_genericPoint_eq_of_comp_eq (hfUh : fU ≫ ι = h ≫ g) :
    fU.base ⁻¹' {genericPoint W₀} = h ⁻¹' (g.base ⁻¹' {genericPoint W}) := by
  have hη : ι (genericPoint W₀) = genericPoint W := genericPoint_eq_of_isOpenImmersion _
  ext u
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  rw [← hη, ← ι.isOpenEmbedding.injective.eq_iff]
  change (fU ≫ ι) u = _ ↔ (h ≫ g) u = _
  rw [hfUh]

variable [IsOpenImmersion h]

/-- Irreducibility of the generic fibre transfers along an open immersion `h` whose range
contains the generic fibre of `g`. -/
theorem isIrreducible_genericFiber_of_comp_eq (hfUh : fU ≫ ι = h ≫ g)
    (hsub : g.base ⁻¹' {genericPoint W} ⊆ Set.range h)
    (hirr : IsIrreducible (g.base ⁻¹' {genericPoint W})) :
    IsIrreducible (fU.base ⁻¹' {genericPoint W₀}) := by
  rw [preimage_genericPoint_eq_of_comp_eq h g fU ι hfUh]
  refine ⟨?_, hirr.2.preimage h.isOpenEmbedding⟩
  obtain ⟨v, hv⟩ := hirr.1
  obtain ⟨u, rfl⟩ := hsub hv
  exact ⟨u, hv⟩

/-- The dimension of the generic fibre transfers along an open immersion `h` whose range
contains the generic fibre of `g`. -/
theorem topologicalKrullDim_genericFiber_of_comp_eq (hfUh : fU ≫ ι = h ≫ g)
    (hsub : g.base ⁻¹' {genericPoint W} ⊆ Set.range h) :
    topologicalKrullDim (fU.base ⁻¹' {genericPoint W₀}) =
      topologicalKrullDim (g.base ⁻¹' {genericPoint W}) := by
  rw [preimage_genericPoint_eq_of_comp_eq h g fU ι hfUh]
  let F := g.base ⁻¹' {genericPoint W}
  let φ : (h.base ⁻¹' F) → F := fun u => ⟨h u, u.2⟩
  have hφ : Topology.IsEmbedding φ :=
    (h.isOpenEmbedding.isEmbedding.comp Topology.IsEmbedding.subtypeVal).codRestrict _ _
  have hφs : Function.Surjective φ := by
    rintro ⟨v, hv⟩
    obtain ⟨u, rfl⟩ := hsub hv
    exact ⟨⟨u, hv⟩, rfl⟩
  exact (hφ.toHomeomorphOfSurjective hφs).isHomeomorph.topologicalKrullDim_eq

variable [IsLocallyNoetherian U] [IsLocallyNoetherian V]

/-- The degree of a prime divisor on the generic fibre is preserved by an open immersion `h`
over `ι` with `fU ≫ ι = h ≫ g`. -/
theorem genericFiberPointDegree_primeDivisorMap (hfUh : fU ≫ ι = h ≫ g)
    (P : Mori.PrimeDivisor U) :
    genericFiberPointDegree fU P =
      genericFiberPointDegree g (OpenWeilRestriction.primeDivisorMap h P) := by
  classical
  have hη : ι (genericPoint W₀) = genericPoint W := genericPoint_eq_of_isOpenImmersion _
  have hgen : (OpenWeilRestriction.primeDivisorMap h P).genericPoint = h P.genericPoint :=
    OpenWeilRestriction.genericPoint_primeDivisorMap h P
  have hiff : fU P.genericPoint = genericPoint W₀ ↔
      g (OpenWeilRestriction.primeDivisorMap h P).genericPoint = genericPoint W := by
    rw [hgen, ← hη, ← ι.isOpenEmbedding.injective.eq_iff]
    change (fU ≫ ι) _ = _ ↔ (h ≫ g) _ = _
    rw [hfUh]
  have hdeg : fU.residueDegree P.genericPoint =
      g.residueDegree (OpenWeilRestriction.primeDivisorMap h P).genericPoint := by
    rw [hgen, ← residueDegree_comp_of_isIso_left' h g, ← hfUh,
      residueDegree_comp_of_isIso_right' fU ι]
  change (if fU P.genericPoint = genericPoint W₀ then fU.residueDegree P.genericPoint
    else 0) = (if g (OpenWeilRestriction.primeDivisorMap h P).genericPoint = genericPoint W
      then g.residueDegree (OpenWeilRestriction.primeDivisorMap h P).genericPoint else 0)
  simp only [hiff, hdeg]

/-- The degree on the generic fibre is preserved by an open immersion `h` over `ι` whose range
contains the generic fibre of `g`, for divisors with corresponding coefficients. -/
theorem genericFiberDegree_eq_of_comp_eq (hfUh : fU ≫ ι = h ≫ g)
    (hsub : g.base ⁻¹' {genericPoint W} ⊆ Set.range h) {DU : QDivisor U} {DV : QDivisor V}
    (hcoeff : ∀ P, DU.coeff P = DV.coeff (OpenWeilRestriction.primeDivisorMap h P)) :
    genericFiberDegree fU DU = genericFiberDegree g DV := by
  classical
  have hcoeff' : ∀ P, DU P = DV (OpenWeilRestriction.primeDivisorMap h P) := hcoeff
  have hpd := genericFiberPointDegree_primeDivisorMap h g fU ι hfUh
  unfold genericFiberDegree
  refine Finset.sum_bij_ne_zero (fun P _ _ => OpenWeilRestriction.primeDivisorMap h P)
    ?_ ?_ ?_ ?_
  · intro P hP _
    rw [Finsupp.mem_support_iff] at hP ⊢
    rwa [← hcoeff']
  · intro P₁ _ _ P₂ _ _ heq
    exact OpenWeilRestriction.primeDivisorMap_injective h heq
  · intro E hE hne
    have hpd0 : genericFiberPointDegree g E ≠ 0 := fun h0 => hne (by
      rw [h0]
      simp)
    have hgE : g E.genericPoint = genericPoint W := by
      by_contra hc
      exact hpd0 (by simp [genericFiberPointDegree, hc])
    obtain ⟨u, hu⟩ := hsub (show E.genericPoint ∈ g.base ⁻¹' {genericPoint W} from hgE)
    obtain ⟨P, rfl⟩ := (OpenWeilRestriction.mem_range_primeDivisorMap_iff h E).mpr ⟨u, hu⟩
    refine ⟨P, ?_, ?_, rfl⟩
    · rw [Finsupp.mem_support_iff, hcoeff']
      exact Finsupp.mem_support_iff.mp hE
    · rw [hcoeff, hpd]
      exact hne
  · intro P _ _
    rw [hcoeff, hpd]

end GenericFiber

/-- **Transport of a log elliptic fiber space along an open immersion** (FA, proof of 15.9,
Step 4). Let `g : (V, Δ_V) ⟶ W` be a log elliptic fiber space, `W₀ ⊆ W` a nonempty open set, and
`j : g⁻¹(W₀) ⟶ Z` an open immersion over `k` into a normal variety `Z` with canonical divisor
`K_Z` and boundary `Δ_Z`, `K_Z + Δ_Z` `ℚ`-Cartier, such that `K_Z + Δ_Z` and `K_V + Δ_V` have the
same coefficient along corresponding prime divisors of `g⁻¹(W₀)`. Then `U = j(g⁻¹(W₀))` carries the
log elliptic fiber space `g ∘ j⁻¹ : (U, Δ_Z|_U) ⟶ W₀`. -/
theorem IsLogEllipticFiberSpace.exists_of_isOpenImmersion {V W Z : Scheme.{u}}
    {sV : V ⟶ Spec (.of k)} {sW : W ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
    [IsLocallyNoetherian V] [IsNormal V] [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
    {n : ℕ} {KV : Divisor V} {ΔV : QDivisor V} {g : V ⟶ W}
    (hg : IsLogEllipticFiberSpace k sV sW n KV ΔV g) (W₀ : W.Opens)
    (hW₀ : (W₀ : Set W).Nonempty) (hZ : IsNormalVariety k sZ) {KZ : Divisor Z} {ΔZ : QDivisor Z}
    (hKZ : KZ.IsCanonicalDivisor sZ n) (hQZ : (Divisor.toQDivisor KZ + ΔZ).IsQCartier)
    (hBZ : IsBoundary (QDivisor.toRDivisor ΔZ)) (j : (g ⁻¹ᵁ W₀).toScheme ⟶ Z)
    [IsOpenImmersion j] (hj : j ≫ sZ = (g ⁻¹ᵁ W₀).ι ≫ sV)
    (hcoeff : ∀ P : Mori.PrimeDivisor (g ⁻¹ᵁ W₀).toScheme,
      (Divisor.toQDivisor KZ + ΔZ).coeff (OpenWeilRestriction.primeDivisorMap j P) =
        (Divisor.toQDivisor KV + ΔV).coeff
          (OpenWeilRestriction.primeDivisorMap (g ⁻¹ᵁ W₀).ι P)) :
    ∃ (U : Z.Opens) (_ : (U : Set Z).Nonempty) (fU : U.toScheme ⟶ W₀.toScheme),
      IsLogEllipticFiberSpace k (U.ι ≫ sZ) (W₀.ι ≫ sW) n (DivisorWithCoeffs.restrict U.ι KZ)
        (DivisorWithCoeffs.restrict U.ι ΔZ) fU := by
  classical
  haveI := hg.isContraction.isVariety_target.toIsIntegral
  haveI : IsProper g := hg.isContraction.isProper
  obtain ⟨w₀, hw₀⟩ := hW₀
  obtain ⟨v₀, hv₀⟩ := hg.isContraction.surjective w₀
  haveI : Nonempty W₀ := ⟨⟨w₀, hw₀⟩⟩
  haveI : Nonempty (g ⁻¹ᵁ W₀) := ⟨⟨v₀, show g v₀ ∈ W₀ from hv₀ ▸ hw₀⟩⟩
  set U := j.opensRange
  set e := j.isoOpensRange
  have heι' : e.inv ≫ j = U.ι := Scheme.Hom.isoOpensRange_inv_comp j
  haveI : Nonempty U := ⟨e.hom (Classical.arbitrary (g ⁻¹ᵁ W₀))⟩
  have hUne : (U : Set Z).Nonempty := ⟨_, (Classical.arbitrary U).2⟩
  set g₀ := g ∣_ W₀ with hg₀
  have hg₀ι : g₀ ≫ W₀.ι = (g ⁻¹ᵁ W₀).ι ≫ g := morphismRestrict_ι g W₀
  set fU := e.inv ≫ g₀ with hfU
  refine ⟨U, hUne, fU, ?_⟩
  have hPZ : IsPairWith sZ n KZ ΔZ := ⟨hZ, hKZ, hQZ⟩
  have hPU := hPZ.restrictOpen U
  rw [restrict_ι_eq_restrictOpen U KZ, restrict_ι_eq_restrictOpen U ΔZ]
  set h : U.toScheme ⟶ V := e.inv ≫ (g ⁻¹ᵁ W₀).ι with hh
  haveI : IsOpenImmersion h := by
    rw [hh]
    infer_instance
  have hfUh : fU ≫ W₀.ι = h ≫ g := by
    rw [hfU, hh, Category.assoc, hg₀ι, Category.assoc]
  have hWv : Mori.IsVariety k (W₀.ι ≫ sW) := by
    have := hg.isContraction.isVariety_target
    have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian sW
    have := QuasiCompact.compactSpace_of_compactSpace sW
    have : IsNoetherian W := ⟨⟩
    refine (MMP.Mori.isVariety_iff k _).2 ⟨?_, inferInstance, inferInstance, inferInstance⟩
    exact isIntegral_of_isOpenImmersion W₀.ι
  haveI : IsIntegral W₀ := hWv.toIsIntegral
  have hηW₀ : W₀.ι (genericPoint W₀) = genericPoint W := genericPoint_eq_of_isOpenImmersion _
  have hcont : IsContraction k (W₀.ι ≫ sW) (U.ι ≫ sZ) fU := by
    refine ⟨hWv, hPU.1.1, ?_, ?_, fun O => ?_⟩
    · rw [← Category.assoc, hfUh, Category.assoc, hg.isContraction.comp_eq, hh, Category.assoc,
        ← hj, ← Category.assoc, heι']
    · rw [hfU]
      infer_instance
    · rw [hfU, Scheme.Hom.comp_app, hg₀, morphismRestrict_app]
      have h1 : IsIso (g.app (W₀.ι ''ᵁ O)) := hg.isContraction.isIso_app _
      have h2 : IsIso (V.presheaf.map (eqToHom (image_morphismRestrict_preimage g W₀ O)).op) :=
        inferInstance
      have h3 : IsIso (e.inv.app ((g ∣_ W₀) ⁻¹ᵁ O)) := inferInstance
      exact IsIso.comp_isIso' (IsIso.comp_isIso' h1 h2) h3
  have hsub : g.base ⁻¹' {genericPoint W} ⊆ Set.range h := by
    intro v hv
    have hvV : g v ∈ W₀ := by
      rw [Set.mem_preimage, Set.mem_singleton_iff] at hv
      rw [hv, ← hηW₀]
      exact (genericPoint W₀).2
    refine ⟨e.hom ⟨v, hvV⟩, ?_⟩
    change (e.hom ≫ e.inv ≫ (g ⁻¹ᵁ W₀).ι) _ = v
    rw [Iso.hom_inv_id_assoc]
    rfl
  refine ⟨⟨hPU.1, fun P => hBZ _⟩, hPU.2.1, hPU.2.2, hcont,
    isIrreducible_genericFiber_of_comp_eq h g fU W₀.ι hfUh hsub hg.isIrreducible_genericFiber,
    (topologicalKrullDim_genericFiber_of_comp_eq h g fU W₀.ι hfUh hsub).trans
      hg.dim_genericFiber, ?_⟩
  refine (genericFiberDegree_eq_of_comp_eq h g fU W₀.ι hfUh hsub fun P => ?_).trans
    hg.genericFiberDegree_eq_zero
  rw [primeDivisorMap_eq_of_comp_eq e.inv (g ⁻¹ᵁ W₀).ι h hh.symm P, ← hcoeff,
    ← primeDivisorMap_eq_of_comp_eq e.inv j U.ι heι' P]
  rfl

end Transport

end MMP.Flips
