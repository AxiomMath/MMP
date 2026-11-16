module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.SdltAdjointPair
public import MMP.AlgebraicGeometry.MMP.Fourfold.LogMinimalModel
public import MMP.AlgebraicGeometry.MMP.Abundance.SdltCommonBaseTwist
public import MMP.AlgebraicGeometry.MMP.Abundance.SdltThreefoldGluing
public import MMP.RingTheory.Kaehler.PluriformProduct
public import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.ValuativeSections
public import MMP.AlgebraicGeometry.Divisor.CartierLineBundle
public import MMP.AlgebraicGeometry.Positivity.RelativeAmplePullbackTwist
public import MMP.AlgebraicGeometry.Positivity.SemiampleDescent
public import MMP.AlgebraicGeometry.Divisor.PullbackExistence
public import MMP.AlgebraicGeometry.Divisor.LocalSectionDivisor
public import MMP.AlgebraicGeometry.Singularities.LocalGenerator
public import MMP.AlgebraicGeometry.Divisor.LinearSystem
public import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
public import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison
public import MMP.AlgebraicGeometry.Divisor.MeromorphicFunctionField
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheafSections

/-!
# Relative semiampleness glues on a projective sdlt threefold

Let `(T, Δ; L)` be a projective sdlt adjoint pair of pure dimension three over `ℂ`, with
normalization components `νᵢ : Tᵢ ⟶ T` carrying the boundaries `Θᵢ = Cᵢ + Δᵢ`, so that the
normalized adjoints are `ν^*L|_{Tᵢ} = K_{Tᵢ} + Θᵢ`, and let `f : T ⟶ Z` be a morphism to a
projective complex variety. If every `K_{Tᵢ} + Θᵢ` is semiample over `Z`, then `L` is
`f`-semiample on the whole union `T`, the conductor included: in some degree `m`, near every
fibre of `f` the sheaf `𝒪_T(mL)` has sections generating it at any given point.

The proof twists by one general effective rational Cartier divisor `G` on `Z` with small
coefficients, so that `(T, Δ + f^*G; L + f^*G)` stays sdlt and its normalized adjoints become
globally semiample, applies
`MMP.Fourfold.IsSdltAdjointPair.exists_isAdjointGeneratorOn_of_isRelativelySemiample`, and
removes the twist by trivializing `𝒪_Z(G)` locally on `Z`.

## Main results

* `MMP.Fourfold.IsSdltAdjointPair.exists_isAdjointGeneratorOn_of_isRelativelySemiample_comp`.

## Implementation notes

As in `MMP.Fourfold.IsSdltAdjointPair`, the adjoint `L = K_T + Δ` is not a divisor on `T`; a
section of `𝒪_T(mL)` over an open `W` is a family `t = (tᵢ)ᵢ` of rational `m`-canonical forms on
the `Tᵢ` which near every point `y ∈ W` is `ν^*a · g` for a function `a` and a local generator `g`
of `𝒪_T(mL)` (`MMP.Fourfold.IsAdjointGeneratorOn`); it generates at `y` when `a` can be taken to
be a unit. `f`-semiampleness of `L` is surjectivity of `f^* f_* 𝒪_T(mL) → 𝒪_T(mL)` for some
`m > 0`, that is, for every `x ∈ T` a section over `f⁻¹(V)`, `V` a neighbourhood of `f(x)`,
generating at `x`. Semiampleness of `K_{Tᵢ} + Θᵢ` over `Z` is
`MMP.Fourfold.QDivisor.IsRelativelySemiample` along `νᵢ ≫ f` for some canonical divisor
`K_{Tᵢ}`; it does not depend on that choice.

## References

* [J. Kollár, *Singularities of the minimal model program*][Kollar2013], Section 5.1
-/

@[expose] public section

section

namespace Proof_thm_fourfold_projective_sdlt_threefold_relative_normalized_generation

open CategoryTheory AlgebraicGeometry MMP MMP.Fourfold MMP.Mori MMP.Flips

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

noncomputable section

/-! ### Powers of forms on a line -/

section LinePow

open scoped TensorProduct

variable {K L : Type*} [Field K] [AddCommGroup L] [Module K L]

/-- The coordinate of `τ ∈ L^{⊗m}` along `b^{⊗m}`, for a basis `b` of the line `L`. -/
private def lineCoord (b : Module.Basis Unit K L) (m : ℕ) (τ : ⨂[K]^m L) : K :=
  (Basis.piTensorProduct fun _ : Fin m => b).repr τ (fun _ => ())

/-- The `a`-th power `τ^a ∈ L^{⊗ma}` of `τ ∈ L^{⊗m}`, for a line `L` with basis `b`: the form
with coordinate `c^a` along `b^{⊗ma}`, `c` the coordinate of `τ`. It does not depend on `b`
(`lineCoord_linePow`). -/
private def linePow (b : Module.Basis Unit K L) (m a : ℕ) (τ : ⨂[K]^m L) :
    ⨂[K]^(m * a) L :=
  lineCoord b m τ ^ a • PiTensorProduct.tprod K (fun _ : Fin (m * a) => b ())

private theorem eq_smul_basis (b : Module.Basis Unit K L) (x : L) : x = b.repr x () • b () := by
  conv_lhs => rw [← b.sum_repr x]
  simp

private theorem tprod_basis_eq (b : Module.Basis Unit K L) (m : ℕ) :
    (PiTensorProduct.tprod K fun _ : Fin m => b ()) =
      (Basis.piTensorProduct fun _ : Fin m => b) (fun _ => ()) := by
  rw [Basis.piTensorProduct_apply]

private theorem lineCoord_tprod (b : Module.Basis Unit K L) (m : ℕ) (x : L) :
    lineCoord b m (PiTensorProduct.tprod K (fun _ : Fin m => x)) = b.repr x () ^ m := by
  have hx := eq_smul_basis b x
  unfold lineCoord
  conv_lhs => rw [hx, tprod_const_smul]
  rw [tprod_basis_eq, LinearEquiv.map_smul, Module.Basis.repr_self]
  simp

private theorem lineCoord_smul (b : Module.Basis Unit K L) (m : ℕ) (c : K) (τ : ⨂[K]^m L) :
    lineCoord b m (c • τ) = c * lineCoord b m τ := by
  simp [lineCoord]

private theorem lineCoord_smul_tprod (b : Module.Basis Unit K L) (m : ℕ) (τ : ⨂[K]^m L) :
    τ = lineCoord b m τ • PiTensorProduct.tprod K (fun _ : Fin m => b ()) := by
  rw [tprod_basis_eq]
  conv_lhs => rw [← (Basis.piTensorProduct fun _ : Fin m => b).sum_repr τ]
  rw [Fintype.sum_eq_single (fun _ => ()) fun i hi => absurd (funext fun _ => rfl) hi]
  rfl

private theorem linePow_tprod (b : Module.Basis Unit K L) (m a : ℕ) (x : L) :
    linePow b m a (PiTensorProduct.tprod K (fun _ : Fin m => x)) =
      PiTensorProduct.tprod K (fun _ : Fin (m * a) => x) := by
  unfold linePow
  rw [lineCoord_tprod, ← pow_mul, ← tprod_const_smul, ← eq_smul_basis]

private theorem linePow_smul (b : Module.Basis Unit K L) (m a : ℕ) (c : K) (τ : ⨂[K]^m L) :
    linePow b m a (c • τ) = c ^ a • linePow b m a τ := by
  simp [linePow, lineCoord_smul, mul_pow, smul_smul]

private theorem lineCoord_linePow (b b' : Module.Basis Unit K L) (m a : ℕ) (τ : ⨂[K]^m L) :
    lineCoord b' (m * a) (linePow b m a τ) = lineCoord b' m τ ^ a := by
  conv_rhs => rw [lineCoord_smul_tprod b m τ]
  rw [linePow, lineCoord_smul, lineCoord_smul, lineCoord_tprod, lineCoord_tprod, mul_pow,
    ← pow_mul]

private theorem linePow_ne_zero (b : Module.Basis Unit K L) (m a : ℕ) {τ : ⨂[K]^m L}
    (hτ : τ ≠ 0) : linePow b m a τ ≠ 0 := by
  have hc : lineCoord b m τ ≠ 0 := fun hc =>
    hτ ((lineCoord_smul_tprod b m τ).trans (by rw [hc, zero_smul]))
  intro h0
  have := congrArg (lineCoord b (m * a)) h0
  rw [lineCoord_linePow, show lineCoord b (m * a) 0 = 0 by simp [lineCoord]] at this
  exact pow_ne_zero a hc this

end LinePow

open MMP.Mori in
/-- The coordinate of a form along a generator `σ` of the top forms of a local ring is its
coordinate along the line basis `σ^{⊗m}`. -/
private theorem formCoeff_eq_lineCoord {k K A : Type*} [CommRing k] [Field K] [Algebra k K]
    [CommRing A] [Algebra k A] [Algebra A K] [IsScalarTower k A K] [IsFractionRing A K] {d : ℕ}
    {σ : ⋀[A]^d Ω[A⁄k]} (hσ : Submodule.span A {σ} = ⊤) (h0 : topFormsMap k A K d σ ≠ 0)
    (m : ℕ) (τ : PluriForms k K d m) :
    formCoeff A hσ h0 τ = lineCoord (topFormsBasis A hσ h0) m τ := by
  simp only [formCoeff, lineCoord]
  rfl

open MMP.Mori in
private theorem formCoeff_linePow {k K A : Type*} [CommRing k] [Field K] [Algebra k K]
    [CommRing A] [Algebra k A] [Algebra A K] [IsScalarTower k A K] [IsFractionRing A K] {d : ℕ}
    {σ : ⋀[A]^d Ω[A⁄k]} (hσ : Submodule.span A {σ} = ⊤) (h0 : topFormsMap k A K d σ ≠ 0)
    (b : Module.Basis Unit K (⋀[K]^d Ω[K⁄k])) (m a : ℕ) (τ : PluriForms k K d m) :
    formCoeff A hσ h0 (show PluriForms k K d ((m * a : ℕ) : ℤ) from linePow b m a τ) =
      formCoeff A hσ h0 τ ^ a := by
  rw [formCoeff_eq_lineCoord, formCoeff_eq_lineCoord]
  exact lineCoord_linePow b _ m a τ

open MMP.Mori in
/-- The `a`-th power `τ^a` of a rational `m`-canonical form, a rational `ma`-canonical form. -/
private def pluriPow {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    {sX : X ⟶ Spec (.of k)} {d : ℕ}
    (b : letI := functionFieldAlgebra sX
      Module.Basis Unit X.functionField (⋀[X.functionField]^d Ω[X.functionField⁄k]))
    (m a : ℕ) (τ : RationalPluriForms sX d m) : RationalPluriForms sX d ((m * a : ℕ) : ℤ) :=
  letI := functionFieldAlgebra sX
  linePow b m a τ

open MMP.Mori in
/-- The order of `τ^a` along a prime divisor is `a` times that of `τ`. -/
private theorem ordForm_linePow {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    [LocallyOfFiniteType sX] {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d)
    (b : letI := functionFieldAlgebra sX
      Module.Basis Unit X.functionField (⋀[X.functionField]^d Ω[X.functionField⁄k]))
    (m a : ℕ) {τ : RationalPluriForms sX d m} (hτ : τ ≠ 0) (Γ : MMP.Mori.PrimeDivisor X) :
    Γ.ordForm (pluriPow b m a τ) = a * Γ.ordForm τ := by
  letI := stalkAlgebra sX Γ.genericPoint
  letI := functionFieldAlgebra sX
  haveI := isScalarTower_stalk_functionField sX Γ.genericPoint
  obtain ⟨σ, hσ, h0⟩ := Γ.exists_topForms_generator hd
  rw [Γ.ordForm_eq _ hσ h0, Γ.ordForm_eq _ hσ h0]
  let τ' : PluriForms k X.functionField d (m : ℤ) := τ
  have hc : formCoeff (k := k) Γ.localRing hσ h0 τ' ≠ 0 := by
    rwa [Ne, formCoeff_eq_zero_iff]
  have e := formCoeff_linePow (k := k) hσ h0 b m a τ'
  unfold pluriPow
  erw [e]
  exact Scheme.ord_pow hc a _

private theorem univ_mem_irreducibleComponents (X : Scheme.{u}) [IsIntegral X] :
    (Set.univ : Set X) ∈ irreducibleComponents X := by
  rw [irreducibleComponents_eq_singleton]; rfl

/-- The generic point of an integral scheme is an associated point. -/
private theorem genericPoint_mem_schemeAssociatedPoints (X : Scheme.{u}) [IsIntegral X]
    [IsLocallyNoetherian X] :
    genericPoint X ∈ Stacks.Divisors.schemeAssociatedPoints X :=
  mem_schemeAssociatedPoints_of_isGenericPoint_irreducibleComponent X
    (univ_mem_irreducibleComponents X) (genericPoint_spec X)

open MMP.Intersection in
/-- The pull-back of a regular local equation is a local equation of the pull-back. -/
private theorem isLocalEquationAt_of_isPullback {X Y : Scheme.{u}} (g : X ⟶ Y)
    {H : Y.CartierDivisor}
    {HX : X.CartierDivisor} (hHX : IsPullback g H HX) {W : Y.Opens} {h : Γ(Y, W)}
    (hu : IsUnit (toTotalQuotient W h)) (hloc : IsLocalEquationOn H W hu.unit) {x : X}
    (hx : g x ∈ W) :
    IsLocalEquationAt HX x
      (stalkToTotalQuotient x (X.presheaf.germ (g ⁻¹ᵁ W) x hx (g.app W h))) := by
  have h1 : IsLocalEquationAt H (g x) (stalkToTotalQuotient (g x) (Y.presheaf.germ W (g x) hx h)) :=
    ⟨W, hx, hu.unit, hloc, germ_toTotalQuotient hx h⟩
  have hf : ∀ {Z : Scheme.{u}} {z : Z} (c : Z.presheaf.stalk z),
      IsFraction (stalkToTotalQuotient z c) c 1 := fun c => ⟨by simp, by simp⟩
  have := hHX.isLocalEquationAt h1 (hf _) (by rw [map_one]; exact hf _)
  rwa [Scheme.Hom.germ_stalkMap_apply] at this

/-- The order of a regular function at a point of coheight one is the length of its quotient. -/
private theorem scheme_ord_algebraMap {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    {z : X}
    (hz : Order.coheight z = 1) {a : X.presheaf.stalk z} (ha : a ≠ 0) :
    X.ord (algebraMap (X.presheaf.stalk z) X.functionField a) z = (Ring.ord _ a).toNat := by
  have : Ring.KrullDimLE 1 (X.presheaf.stalk z) := krullDimLE_of_coheight_le hz.le
  have hne : algebraMap (X.presheaf.stalk z) X.functionField a ≠ 0 := by
    rwa [Ne, IsFractionRing.to_map_eq_zero_iff]
  rw [Scheme.ord_eq_iff hz hne]
  unfold Scheme.ordHom
  rw [Ring.ordFrac_eq_ord _ ha]
  have hnzd : a ∈ nonZeroDivisors _ := mem_nonZeroDivisors_of_ne_zero ha
  exact Ring.ordMonoidWithZeroHom_eq_coe (R := X.presheaf.stalk z) hnzd
    (ENat.natCast_toNat (Ring.ord_ne_top hnzd)).symm

open MMP.Intersection in
/-- The order of a pull-back along a prime divisor is the length of the quotient by the pulled-back
regular local equation. -/
private theorem primeDivisorOrder_eq_ord_toNat {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    (g : X ⟶ Y) {H : Y.CartierDivisor} {HX : X.CartierDivisor} (hHX : IsPullback g H HX)
    {W : Y.Opens} {h : Γ(Y, W)} (hu : IsUnit (toTotalQuotient W h))
    (hloc : IsLocalEquationOn H W hu.unit) (P : MMP.Mori.PrimeDivisor X)
    (hP : g P.genericPoint ∈ W)
    (hne : X.presheaf.germ (g ⁻¹ᵁ W) P.genericPoint hP (g.app W h) ∈ nonZeroDivisors _) :
    primeDivisorOrder P HX =
      (Ring.ord _ (X.presheaf.germ (g ⁻¹ᵁ W) P.genericPoint hP (g.app W h))).toNat := by
  set V := primeDivisorSubvariety P
  set c : X.presheaf.stalk V.genericPoint :=
    X.presheaf.germ (g ⁻¹ᵁ W) P.genericPoint hP (g.app W h)
  have hloc' : IsLocalEquationAt HX V.genericPoint (stalkToTotalQuotient V.genericPoint c) :=
    isLocalEquationAt_of_isPullback g hHX hu hloc hP
  have : Ring.KrullDimLE 1 (X.presheaf.stalk V.genericPoint) :=
    krullDimLE_of_coheight_le P.coheight_genericPoint.le
  have hO := isOrderAlong_of_isFraction (V := V) hloc' hne (one_mem _)
    ⟨by simp, by rw [map_one, one_mul]⟩
  rw [hO.primeDivisorOrder_eq]
  simp only [Ring.ord_one, ENat.toNat_zero, Nat.cast_zero, sub_zero]
  rfl

open MMP.Intersection in
/-- The order of the pull-back of a Cartier divisor along a prime divisor is the order of the
pulled-back local equation. -/
private theorem primeDivisorOrder_eq_ord_of_isPullback {X Y : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] (g : X ⟶ Y) {H : Y.CartierDivisor}
    {HX : X.CartierDivisor} (hHX : IsPullback g H HX) {W : Y.Opens} {h : Γ(Y, W)}
    (hu : IsUnit (toTotalQuotient W h)) (hloc : IsLocalEquationOn H W hu.unit)
    (P : MMP.Mori.PrimeDivisor X) (hP : g P.genericPoint ∈ W)
    (hne : X.presheaf.germ (g ⁻¹ᵁ W) P.genericPoint hP (g.app W h) ≠ 0) :
    primeDivisorOrder P HX = X.ord (algebraMap _ X.functionField
      (X.presheaf.germ (g ⁻¹ᵁ W) P.genericPoint hP (g.app W h))) P.genericPoint := by
  rw [primeDivisorOrder_eq_ord_toNat g hHX hu hloc P hP (mem_nonZeroDivisors_of_ne_zero hne),
    scheme_ord_algebraMap P.coheight_genericPoint hne]

open MMP.Intersection in
/-- Off the support of `H`, a regular local equation of `H` is a unit at the point. -/
private theorem isUnit_germ_of_notMem_cartierSupport {Y : Scheme.{u}} {H : Y.CartierDivisor}
    {W : Y.Opens} {h : Γ(Y, W)} (hu : IsUnit (toTotalQuotient W h))
    (hloc : IsLocalEquationOn H W hu.unit) {y : Y} (hy : y ∈ W) (hnot : y ∉ cartierSupport H) :
    IsUnit (Y.presheaf.germ W y hy h) := by
  have e1 : IsLocalEquationAt H y (stalkToTotalQuotient _ (Y.presheaf.germ W y hy h)) :=
    ⟨W, hy, hu.unit, hloc, germ_toTotalQuotient (X := Y) hy h⟩
  obtain ⟨w, hw⟩ := (isLocalEquationAt_one_of_notMem_cartierSupport hnot).exists_eq_mul_units e1
  rw [one_mul] at hw
  rw [stalkToTotalQuotient_injective _ hw]
  exact w.isUnit

open MMP.Intersection in
/-- The pull-back of a regular local equation of `H` along a morphism from an integral scheme
satisfying the pull-back condition has non-zero germs. -/
private theorem germ_ne_zero_of_isPullback {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (g : X ⟶ Y) {H : Y.CartierDivisor}
    {HX : X.CartierDivisor} (hHX : IsPullback g H HX) {W : Y.Opens} {h : Γ(Y, W)}
    (hu : IsUnit (toTotalQuotient W h)) (hloc : IsLocalEquationOn H W hu.unit) {x : X}
    (hx : g x ∈ W) : X.presheaf.germ (g ⁻¹ᵁ W) x hx (g.app W h) ≠ 0 := by
  intro h0
  have hsec : g.app W h = 0 := germ_injective_of_isIntegral X x hx (by rw [h0, map_zero])
  set ξ := genericPoint X
  have hξ : ξ ∈ g ⁻¹ᵁ W :=
    ((genericPoint_spec X).mem_open_set_iff (g ⁻¹ᵁ W).isOpen).mpr ⟨x, trivial, hx⟩
  have hass : ξ ∈ Stacks.Divisors.schemeAssociatedPoints X :=
    genericPoint_mem_schemeAssociatedPoints X
  have hξ' : g ξ ∈ W := hξ
  have h2 := (isUnit_germ_of_notMem_cartierSupport hu hloc hξ' (hHX.1 ξ hass)).map
    (g.stalkMap ξ).hom
  have h3 := Scheme.Hom.germ_stalkMap_apply g W ξ hξ' h
  erw [h3, hsec, map_zero] at h2
  exact not_isUnit_zero h2

/-- An epimorphic counit of `f^* ⊣ f_*` stays epimorphic along an isomorphism of modules. -/
private theorem epi_counit_of_iso {X Z : Scheme.{u}} (f : X ⟶ Z) {M N : X.Modules} (e : N ≅ M)
    (h : Epi ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app M)) :
    Epi ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app N) := by
  set adj := Scheme.Modules.pullbackPushforwardAdjunction f
  have hnat := adj.counit.naturality e.hom
  have heq : adj.counit.app N =
      (Scheme.Modules.pushforward f ⋙ Scheme.Modules.pullback f).map e.hom ≫
        adj.counit.app M ≫ e.inv := by
    rw [← Category.assoc, hnat, Functor.id_map, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  rw [heq]
  infer_instance

section FreeSections

open Opposite

variable {Y : Scheme.{u}} [IsIntegral Y]

private theorem specializes_genericPoint (Z : irreducibleComponents Y) :
    componentGenericPoint Y Z ⤳ genericPoint Y :=
  (Inseparable.of_eq (componentGenericPoint_eq_genericPoint Z)).specializes

private theorem genericPoint_specializes (Z : irreducibleComponents Y) :
    genericPoint Y ⤳ componentGenericPoint Y Z :=
  (genericPoint_spec Y).specializes trivial

/-- A rational function `φ ∈ K(Y)`, read in every factor of `K(Y) = ∏_Z 𝒪_{Y,η_Z}`. -/
private def toRationalFunctions : Y.functionField →+* RationalFunctions Y :=
  Pi.ringHom fun Z => (Y.presheaf.stalkSpecializes (specializes_genericPoint Z)).hom

private theorem stalkSpecializes_toRationalFunctions (Z : irreducibleComponents Y)
    (φ : Y.functionField) :
    (Y.presheaf.stalkSpecializes (genericPoint_specializes Z)).hom
      (toRationalFunctions φ Z) = φ := by
  change (Y.presheaf.stalkSpecializes _).hom ((Y.presheaf.stalkSpecializes _).hom φ) = φ
  rw [TopCat.Presheaf.stalkSpecializes_comp_apply, TopCat.Presheaf.stalkSpecializes_refl]
  rfl

variable [IsLocallyNoetherian Y] [IsNormal Y]

/-- `v_P` on the factor `𝒪_{Y,η}` of `K(Y)` is the inverse of the divisorial valuation of the
corresponding rational function. -/
private theorem valuation_eq_inv_divisorialValuation (P : MMP.Mori.PrimeDivisor Y)
    (s : Y.presheaf.stalk (componentGenericPoint Y P.component)) :
    P.valuation s = (P.divisorialValuation
      ((Y.presheaf.stalkSpecializes (genericPoint_specializes P.component)).hom s))⁻¹ := by
  rw [MMP.Threefold.Mori.Helpers.valuation_eq_ordFrac,
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_inv_ordHom, inv_inv]
  rfl

/-- The order along `P` of the unit of `K(Y)` defined by `φ ≠ 0` is `ord_{η_P}(φ)`. -/
private theorem ord_toRationalFunctions (P : MMP.Mori.PrimeDivisor Y) {φ : Y.functionField}
    (hφ : φ ≠ 0) (ψ : (RationalFunctions Y)ˣ) (hψ : (ψ : RationalFunctions Y) =
      toRationalFunctions φ) : P.ord ψ = Scheme.ord φ P.genericPoint := by
  have h2 := valuation_eq_inv_divisorialValuation P ((ψ : RationalFunctions Y) P.component)
  rw [hψ, stalkSpecializes_toRationalFunctions, ← hψ, P.valuation_component,
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hφ, ← WithZero.exp_neg,
    neg_neg] at h2
  exact WithZero.exp_injective h2

open MMP.Intersection

/-- On an integral locally Noetherian scheme, a point of coheight zero lies in the support of no
Cartier divisor. -/
private theorem notMem_cartierSupport_of_coheight_eq_zero {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] (A : X.CartierDivisor) {x : X} (hx : Order.coheight x = 0) :
    x ∉ cartierSupport A := by
  have : Ring.KrullDimLE 0 (X.presheaf.stalk x) := krullDimLE_of_coheight_le (by simp [hx])
  have : IsArtinianRing (X.presheaf.stalk x) := isArtinianRing_iff_krullDimLE_zero.mpr this
  exact notMem_cartierSupport_of_isArtinianRing A x

/-- Every Cartier divisor on a Noetherian integral scheme has a Weil divisor. -/
private theorem exists_isWeilDivisorOfCartier {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [TopologicalSpace.NoetherianSpace X] (A : X.CartierDivisor) :
    ∃ w : Divisor X, IsWeilDivisorOfCartier A w := by
  have hfin := MMP.Mori.finite_setOf_genericPoint_mem (isClosed_cartierSupport A)
    (fun s hs h0 => notMem_cartierSupport_of_coheight_eq_zero A h0 hs)
  refine ⟨Finsupp.ofSupportFinite (fun P => primeDivisorOrder P A) (hfin.subset fun P hP => ?_),
    fun P => ?_⟩
  · by_contra h
    have hg : (primeDivisorSubvariety P).genericPoint = P.genericPoint := rfl
    refine hP ((isOrderAlong_primeDivisorOrder A P).eq_zero_of_not_subset fun h' => h ?_)
    show P.genericPoint ∈ cartierSupport A
    rw [← hg]
    exact genericPoint_mem_cartierSupport_iff.mpr h'
  · rw [MMP.Mori.DivisorWithCoeffs.coeff_apply, Finsupp.ofSupportFinite_coe]
    exact isOrderAlong_primeDivisorOrder A P

/-- The Weil divisor of the realization of `q • C`, for a `ℚ`-Cartier divisor `C` with Weil
`ℚ`-divisor `D`, is `q • D`. -/
private theorem coeff_eq_mul_of_isWeilDivisorOfCartier_realization {X : Scheme.{u}}
    [IsLocallyNoetherian X] {D : QDivisor X} {C : KCartierDivisor ℚ X}
    (hC : ∀ P : MMP.Mori.PrimeDivisor X,
      D.coeff P = C.sum fun E c => c * (primeDivisorOrder P E : ℚ)) {q : ℕ}
    (h : ∀ E, ∃ n : ℤ, ((q : ℚ) • C) E = n) {B : Divisor X}
    (hB : IsWeilDivisorOfCartier (KCartierDivisor.realization ((q : ℚ) • C) h) B)
    (P : MMP.Mori.PrimeDivisor X) : (B.coeff P : ℚ) = q * D.coeff P := by
  classical
  have hc : ∀ E, ((Classical.choose (h E) : ℤ) : ℚ) = ((q : ℚ) • C) E := fun E =>
    (Classical.choose_spec (h E)).symm
  rw [← (hB P).primeDivisorOrder_eq, KCartierDivisor.realization, Finsupp.sum, map_sum,
    Int.cast_sum, hC P, Finsupp.sum, Finset.mul_sum]
  have hz : ∀ E ∈ C.support, E ∉ ((q : ℚ) • C).support →
      (q : ℚ) * (C E * (primeDivisorOrder P E : ℚ)) = 0 := fun E _ hE => by
    rw [Finsupp.notMem_support_iff, Finsupp.smul_apply, smul_eq_mul] at hE
    rw [← mul_assoc, hE, zero_mul]
  rw [← Finset.sum_subset (Finsupp.support_smul (b := (q : ℚ)) (g := C)) hz]
  refine Finset.sum_congr rfl fun E _ => ?_
  rw [map_zsmul, smul_eq_mul, Int.cast_mul, hc, Finsupp.smul_apply, smul_eq_mul, mul_assoc]

end FreeSections

/-- `KCartierDivisor.realization` depends only on the divisor. -/
private theorem realization_congr {X : Scheme.{u}} {c c' : KCartierDivisor ℚ X}
    (e : c = c') (h : ∀ D, ∃ n : ℤ, c D = n) (h' : ∀ D, ∃ n : ℤ, c' D = n) :
    KCartierDivisor.realization c h = KCartierDivisor.realization c' h' := by
  subst e; rfl

/-- A `ℚ`-divisor `Q` with `nQ` the Weil divisor of an `f`-free Cartier divisor is semiample over
the base. -/
private theorem isRelativelySemiample_of_isRelativelyFreeCartier {X Z : Scheme.{u}}
    [IsLocallyNoetherian X] (f : X ⟶ Z) (Q : QDivisor X) (n : ℕ) (hn : 0 < n) (D' : Divisor X)
    (hQ : ∀ P, (D'.coeff P : ℚ) = n * Q.coeff P) (E : X.CartierDivisor)
    (hE : MMP.Intersection.IsWeilDivisorOfCartier E D') (hfree : IsRelativelyFreeCartier f E) :
    QDivisor.IsRelativelySemiample f Q := by
  classical
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  refine ⟨Finsupp.single E ((n : ℚ)⁻¹), fun P => ?_, n, hn, ?_⟩
  · rw [Finsupp.sum_single_index (by simp),
      (MMP.Intersection.isOrderAlong_primeDivisorOrder E P).unique (hE P), hQ P]
    field_simp
  · have hc : (n : ℚ) • Finsupp.single E ((n : ℚ)⁻¹) =
        (Finsupp.single E (1 : ℤ)).mapRange (Int.cast : ℤ → ℚ) Int.cast_zero := by
      rw [Finsupp.smul_single, Finsupp.mapRange_single, smul_eq_mul, mul_inv_cancel₀ hn',
        Int.cast_one]
    refine ⟨fun D => ⟨(Finsupp.single E (1 : ℤ)) D, by rw [hc]; rfl⟩, ?_⟩
    rw [realization_congr hc _ (fun D => ⟨(Finsupp.single E (1 : ℤ)) D, rfl⟩),
      KCartierDivisor.realization_eq_sum, Finsupp.sum_single_index (by simp), one_smul]
    exact hfree

/-- Relative freeness of a Cartier divisor depends only on its sheaf up to isomorphism. -/
private theorem isRelativelyFreeCartier_of_iso {X Z : Scheme.{u}} (f : X ⟶ Z)
    {E E' : X.CartierDivisor}
    (e : MMP.CartierDivisor.sheaf E' ≅ MMP.CartierDivisor.sheaf E)
    (h : IsRelativelyFreeCartier f E) : IsRelativelyFreeCartier f E' :=
  epi_counit_of_iso f e h

open MMP.Intersection in
/-- The order along a prime divisor `Q` of the principal Cartier divisor of a rational function
`r ≠ 0` is `ord_{η_Q}(r)`. -/
private theorem primeDivisorOrder_principalDivisor_mk0 {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] {r : X.functionField} (hr0 : r ≠ 0) (Q : MMP.Mori.PrimeDivisor X) :
    primeDivisorOrder Q (MMP.Intersection.principalDivisor (Units.map
      (MMP.CartierDivisorSheaf.ofFunctionField (X := X) ⊤).toMonoidHom
      (Units.mk0 r hr0))) = Scheme.ord r Q.genericPoint := by
  set c : (X.totalQuotientSheaf.obj.obj (Opposite.op ⊤))ˣ :=
    Units.map (MMP.CartierDivisorSheaf.ofFunctionField (X := X) ⊤).toMonoidHom
      (Units.mk0 r hr0)
  set Pc := MMP.Intersection.principalDivisor c
  obtain ⟨⟨a, b⟩, hab⟩ :=
    IsLocalization.surj (nonZeroDivisors (X.presheaf.stalk Q.genericPoint)) r
  have hbK : algebraMap _ X.functionField (b : X.presheaf.stalk Q.genericPoint) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  have hb0 : (b : X.presheaf.stalk Q.genericPoint) ≠ 0 := nonZeroDivisors.ne_zero b.2
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at hab
    exact mul_ne_zero hr0 hbK hab
  have hloc : IsLocalEquationAt Pc Q.genericPoint
      (X.totalQuotientSheaf.presheaf.germ ⊤ Q.genericPoint trivial (c : _)) :=
    ⟨⊤, trivial, c, isLocalEquationOn_principalDivisor c, rfl⟩
  have hfrac : IsFraction (X.totalQuotientSheaf.presheaf.germ ⊤ Q.genericPoint trivial (c : _))
      a b := by
    refine ⟨isUnit_stalkToTotalQuotient_of_mem_nonZeroDivisors b.2, ?_⟩
    apply (totalQuotientStalkToFunctionField_bijective Q.genericPoint).1
    rw [map_mul, totalQuotientStalkToFunctionField_stalkToTotalQuotient,
      totalQuotientStalkToFunctionField_stalkToTotalQuotient]
    erw [MMP.CartierDivisorSheaf.totalQuotientStalkToFunctionField_germ_top_ofFunctionField]
    rw [mul_comm]
    exact hab
  have : Ring.KrullDimLE 1 (X.presheaf.stalk (primeDivisorSubvariety Q).genericPoint) :=
    krullDimLE_of_coheight_le Q.coheight_genericPoint.le
  have hO := isOrderAlong_of_isFraction (V := primeDivisorSubvariety Q) hloc
    (mem_nonZeroDivisors_of_ne_zero ha0) b.2 hfrac
  rw [hO.primeDivisorOrder_eq]
  have h1 := Scheme.ord_mul (x := Q.genericPoint) hr0 hbK
  rw [hab, scheme_ord_algebraMap Q.coheight_genericPoint ha0,
    scheme_ord_algebraMap Q.coheight_genericPoint hb0] at h1
  change ((Ring.ord _ a).toNat : ℤ) -
    ((Ring.ord _ (b : X.presheaf.stalk Q.genericPoint)).toNat : ℤ) = _
  linarith

open MMP.Intersection in
/-- **Relative semiampleness is a linear equivalence invariant.** Adding a principal divisor to a
relatively semiample `ℚ`-divisor keeps it relatively semiample: a section `ψ` of `𝒪(mD)` gives the
section `ψ φ^{-m}` of `𝒪(m(D + div φ))`. -/
private theorem isRelativelySemiample_add_principalDivisor {X Z : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] (f : X ⟶ Z) {D : QDivisor X}
    (hD : QDivisor.IsRelativelySemiample f D) (φ : (RationalFunctions X)ˣ) :
    QDivisor.IsRelativelySemiample f (D + Divisor.toQDivisor (principalDivisor φ)) := by
  classical
  haveI : IsNoetherian X := ⟨⟩
  obtain ⟨C, hC, q, hq, hint, hfree⟩ := hD
  set E := KCartierDivisor.realization ((q : ℚ) • C) hint
  obtain ⟨B, hEB⟩ := exists_isWeilDivisorOfCartier E
  -- `φ` as a rational function `r₀` on the integral scheme `X`
  obtain ⟨Z₀⟩ : Nonempty (irreducibleComponents X) :=
    ⟨⟨Set.univ, univ_mem_irreducibleComponents X⟩⟩
  set r₀ : X.functionField := (X.presheaf.stalkSpecializes (genericPoint_specializes Z₀)).hom
    ((φ : RationalFunctions X) Z₀)
  have hr : toRationalFunctions r₀ = (φ : RationalFunctions X) := by
    funext Z
    have hmem : ∀ W : irreducibleComponents X, (W : Set X) = Set.univ := fun W => by
      have h1 : (W : Set X) ∈ ({Set.univ} : Set (Set X)) := by
        rw [← irreducibleComponents_eq_singleton]; exact W.2
      exact h1
    have hZ : Z₀ = Z := Subtype.ext ((hmem Z₀).trans (hmem Z).symm)
    subst hZ
    change (X.presheaf.stalkSpecializes _).hom ((X.presheaf.stalkSpecializes _).hom _) = _
    rw [TopCat.Presheaf.stalkSpecializes_comp_apply, TopCat.Presheaf.stalkSpecializes_refl]
    rfl
  have hr0 : r₀ ≠ 0 := by
    intro h0
    haveI : Nontrivial (RationalFunctions X) := Pi.nontrivial_at Z₀
    rw [h0, map_zero] at hr
    exact φ.ne_zero hr.symm
  have hordφ : ∀ Q : MMP.Mori.PrimeDivisor X, Q.ord φ = Scheme.ord r₀ Q.genericPoint :=
    fun Q => ord_toRationalFunctions Q hr0 φ hr.symm
  -- the principal Cartier divisor of `r₀`
  set c : (X.totalQuotientSheaf.obj.obj (Opposite.op ⊤))ˣ :=
    Units.map (MMP.CartierDivisorSheaf.ofFunctionField (X := X) ⊤).toMonoidHom
      (Units.mk0 r₀ hr0)
  set Pc := MMP.Intersection.principalDivisor c with hPc
  have hPord : ∀ Q : MMP.Mori.PrimeDivisor X,
      primeDivisorOrder Q Pc = Scheme.ord r₀ Q.genericPoint :=
    primeDivisorOrder_principalDivisor_mk0 hr0
  -- `E + q div(r₀)` is free and has Weil divisor `B + q div(φ)`
  have hq' : q • Pc = MMP.Intersection.principalDivisor (c ^ q) := by
    rw [hPc, MMP.Intersection.principalDivisor, MMP.Intersection.principalDivisor, ← map_nsmul]
    rfl
  have hfree' : IsRelativelyFreeCartier f (E + q • Pc) := by
    refine isRelativelyFreeCartier_of_iso f ?_ hfree
    rw [hq']
    exact (MMP.CartierDivisor.sheafAddPrincipalIso E (c ^ q)).symm ≪≫
      Iso.refl (MMP.CartierDivisor.sheaf E)
  have hw : ∀ P : MMP.Mori.PrimeDivisor X, (B + q • principalDivisor φ).coeff P =
      B.coeff P + q * P.ord φ := fun P => by
    simp [DivisorWithCoeffs.coeff_apply, nsmul_eq_mul]
    exact Or.inl rfl
  have hEw : IsWeilDivisorOfCartier (E + q • Pc) (B + q • principalDivisor φ) := fun Q => by
    have h := isOrderAlong_primeDivisorOrder (E + q • Pc) Q
    have e : primeDivisorOrder Q (E + q • Pc) = (B + q • principalDivisor φ).coeff Q := by
      rw [map_add, map_nsmul, (hEB Q).primeDivisorOrder_eq, hPord, hw, ← hordφ, nsmul_eq_mul]
    rwa [e] at h
  refine isRelativelySemiample_of_isRelativelyFreeCartier f _ q hq _ (fun P => ?_) _ hEw hfree'
  rw [hw, DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor,
    coeff_principalDivisor]
  push_cast
  rw [coeff_eq_mul_of_isWeilDivisorOfCartier_realization hC hint hEB P]
  ring

/-! ### Removing the base twist -/

/-- `(c τ)^a = c^a τ^a`. -/
private theorem pluriPow_smul {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    {sX : X ⟶ Spec (.of k)} {d : ℕ}
    (b : letI := functionFieldAlgebra sX
      Module.Basis Unit X.functionField (⋀[X.functionField]^d Ω[X.functionField⁄k]))
    (m a : ℕ) (c : X.functionField) (τ : RationalPluriForms sX d m) :
    pluriPow b m a (c • τ) = c ^ a • pluriPow b m a τ := by
  letI := functionFieldAlgebra sX
  exact linePow_smul b m a c τ

/-- Local generators of `𝒪_T(m(K_T + Δ))` on `U` restrict to local generators on `U' ≤ U`. -/
private theorem isAdjointGeneratorOn_mono {k : Type u} [Field k] {T : Scheme.{u}}
    {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    {N : NormalizationComponents sT hT} {n m : ℕ} {Θ : ∀ i, QDivisor (N.X i)} {U U' : T.Opens}
    {s : ∀ i, RationalPluriForms (N.n i ≫ sT) n m} (h : IsAdjointGeneratorOn N n m Θ U s)
    (hU : U' ≤ U) : IsAdjointGeneratorOn N n m Θ U' s :=
  ⟨fun i => (h.1 i).mono fun _ hx => hU hx,
    fun i j P P' heq hQ hD hne => h.2 i j P P' heq (hU hQ) hD hne⟩

/-- **Transport of a residue presentation to the untwisted generator.** If `(V, a, g, ε)`
presents the residue of `s` along `P`, then on `V' ⊆ V`, for a function `u` on `V'` whose
pull-back is `φ` at the generic point of `P`, `(V', a|_{V'}, g^a u^e, ε^a)` presents the residue
of `φ^e s^a` along `P`. -/
private theorem isLogResiduePresentation_pow_smul {k : Type u} [Field k] {T : Scheme.{u}}
    {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    (N : NormalizationComponents sT hT) {n m : ℕ} (a e : ℕ) {i : N.ι}
    {P : MMP.Mori.PrimeDivisor (N.X i)} {V V' : T.Opens} (hV : V' ≤ V)
    {hP : (N.n i).base P.genericPoint ∈ V} (hP' : (N.n i).base P.genericPoint ∈ V')
    {av : Fin (n - 1) → Γ(T, V)} {g : Γ(T, V)} {ε : ℤ} {s : RationalPluriForms (N.n i ≫ sT) n m}
    (hs : IsLogResiduePresentation N n m i P V hP av g ε s)
    (b : letI := functionFieldAlgebra (N.n i ≫ sT)
      Module.Basis Unit (N.X i).functionField
        (⋀[(N.X i).functionField]^n Ω[(N.X i).functionField⁄k]))
    (u : Γ(T, V')) {φ : (N.X i).functionField}
    (hφ : algebraMap _ (N.X i).functionField ((N.X i).presheaf.germ ((N.n i) ⁻¹ᵁ V')
      P.genericPoint hP' ((N.n i).app V' u)) = φ) :
    IsLogResiduePresentation N n (m * a) i P V' hP'
      (fun j => T.presheaf.map (homOfLE hV).op (av j))
      (T.presheaf.map (homOfLE hV).op g ^ a * u ^ e)
      (ε ^ a) (φ ^ e • pluriPow b m a s) := by
  unfold IsLogResiduePresentation at hs ⊢
  obtain ⟨z, h0, hz, hseq, hda, hres⟩ := hs
  have R1 : ∀ t : Γ(T, V), (N.X i).presheaf.germ ((N.n i) ⁻¹ᵁ V') P.genericPoint hP'
      ((N.n i).app V' (T.presheaf.map (homOfLE hV).op t)) =
      (N.X i).presheaf.germ ((N.n i) ⁻¹ᵁ V) P.genericPoint hP ((N.n i).app V t) := by
    intro t
    rw [← Scheme.Hom.germ_stalkMap_apply, ← Scheme.Hom.germ_stalkMap_apply,
      TopCat.Presheaf.germ_res_apply]
  set w := (N.X i).presheaf.germ ((N.n i) ⁻¹ᵁ V') P.genericPoint hP' ((N.n i).app V' u)
    with hw_def
  dsimp only
  refine ⟨z, h0 ^ a * w ^ e, hz, ?_, ?_, ?_⟩
  · rw [hseq]
    simp only [R1]
    unfold pluriPow
    rw [linePow_smul, linePow_tprod]
    simp only [smul_smul, map_mul, map_pow, hφ, mul_comm]
    exact (mul_smul _ _ _).symm
  · simp only [R1]
    exact hda
  · simp only [map_mul, map_pow, R1]
    rw [← hw_def, hres]
    push_cast
    ring

open MMP.Intersection in
/-- **Untwisting a local generator.** Let `E` be a Cartier divisor on a normal variety `X` of
dimension `d`, `Θ' = Θ + (p/q) E` with `q > 0`, and `φ` a rational function whose order along
every prime divisor meeting `U` is that of `E`. If `s` generates `𝒪_X(m(K_X + Θ'))` on `U`, then
`φ^{mp} s^q` generates `𝒪_X(mq(K_X + Θ))` on `U`. -/
private theorem generatesOn_pow_smul_pluriPow {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    [LocallyOfFiniteType sX] {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d)
    (b : letI := functionFieldAlgebra sX
      Module.Basis Unit X.functionField (⋀[X.functionField]^d Ω[X.functionField⁄k]))
    {m p q : ℕ} (hq : 0 < q) {Θ Θ' : QDivisor X} {E : X.CartierDivisor} {U : X.Opens}
    {φ : X.functionField} (hφ0 : φ ≠ 0)
    (hφ : ∀ Γ : MMP.Mori.PrimeDivisor X, (Γ.support ∩ U).Nonempty →
      X.ord φ Γ.genericPoint = primeDivisorOrder Γ E)
    (hΘ' : ∀ P, Θ'.coeff P = Θ.coeff P + ((p : ℚ) / q) * primeDivisorOrder P E)
    {s : RationalPluriForms sX d m} (hs : GeneratesOn Θ' m U s) :
    GeneratesOn Θ (m * q) U (φ ^ (m * p) • pluriPow b m q s) := by
  have hpow0 : pluriPow b m q s ≠ 0 := linePow_ne_zero _ m q hs.1
  refine ⟨smul_ne_zero (pow_ne_zero _ hφ0) hpow0, fun Γ hΓ => ?_⟩
  have e1 := hs.2 Γ hΓ
  show ((Γ.ordForm (φ ^ (m * p) • pluriPow b m q s) : ℤ) : ℚ) +
    ((m * q : ℕ) : ℚ) * Θ.coeff Γ = 0
  rw [Γ.ordForm_smul hd (pow_ne_zero _ hφ0) hpow0, ordForm_linePow hd _ m q hs.1 Γ,
    Scheme.ord_pow hφ0, hφ Γ hΓ]
  rw [hΘ'] at e1
  have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  have hc : (q : ℚ) * ((p : ℚ) / q) = p := mul_div_cancel₀ _ hq'
  push_cast
  linear_combination (q : ℚ) * e1 - (m : ℚ) * (primeDivisorOrder Γ E : ℚ) * hc

/-- The rational function of the pull-back of a restricted function does not depend on the
restriction. -/
private theorem germToFunctionField_app_map {X Y : Scheme.{u}} (g : X ⟶ Y) {U U' : Y.Opens}
    (hUU : U' ≤ U) [IsIntegral X] [Nonempty (g ⁻¹ᵁ U')] [Nonempty (g ⁻¹ᵁ U)] (a : Γ(Y, U)) :
    (X.germToFunctionField (g ⁻¹ᵁ U')).hom (g.app U' (Y.presheaf.map (homOfLE hUU).op a)) =
      (X.germToFunctionField (g ⁻¹ᵁ U)).hom (g.app U a) := by
  obtain ⟨⟨z, hz⟩⟩ := ‹Nonempty (g ⁻¹ᵁ U')›
  rw [← Scheme.algebraMap_germ_eq_germToFunctionField X hz,
    ← Scheme.algebraMap_germ_eq_germToFunctionField X (show z ∈ g ⁻¹ᵁ U from hUU hz)]
  congr 1
  rw [← Scheme.Hom.germ_stalkMap_apply g U' z hz, ← Scheme.Hom.germ_stalkMap_apply g U z (hUU hz)]
  exact congrArg _ (TopCat.Presheaf.germ_res_apply _ _ _ _ _)

open Classical in
/-- The pull-back along `g` of a function `a` on an open `W` of the target, as a rational function
on the integral source; it is `1` when `g⁻¹ W` is empty. -/
private def pullbackFunction {X Y : Scheme.{u}} [IsIntegral X] (g : X ⟶ Y) (W : Y.Opens)
    (a : Γ(Y, W)) : X.functionField :=
  if hW : Nonempty (g ⁻¹ᵁ W) then
    haveI := hW
    X.germToFunctionField (g ⁻¹ᵁ W) (g.app W a)
  else 1

private theorem pullbackFunction_eq {X Y : Scheme.{u}} [IsIntegral X] (g : X ⟶ Y) {W : Y.Opens}
    (a : Γ(Y, W)) {x : X} (hx : g x ∈ W) :
    pullbackFunction g W a = algebraMap _ _ (X.presheaf.germ (g ⁻¹ᵁ W) x hx (g.app W a)) := by
  have hW : Nonempty (g ⁻¹ᵁ W) := ⟨⟨x, hx⟩⟩
  simp only [pullbackFunction, dif_pos hW]
  exact (Scheme.algebraMap_germ_eq_germToFunctionField X (U := g ⁻¹ᵁ W) hx _).symm

open MMP.Intersection in
private theorem pullbackFunction_ne_zero {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (g : X ⟶ Y) {H : Y.CartierDivisor} {HX : X.CartierDivisor} (hHX : IsPullback g H HX)
    {W : Y.Opens} {h : Γ(Y, W)} (hu : IsUnit (toTotalQuotient W h))
    (hloc : IsLocalEquationOn H W hu.unit) : pullbackFunction g W h ≠ 0 := by
  by_cases hW : Nonempty (g ⁻¹ᵁ W)
  · obtain ⟨⟨x, hx⟩⟩ := hW
    rw [pullbackFunction_eq g h hx, Ne, IsFractionRing.to_map_eq_zero_iff]
    exact germ_ne_zero_of_isPullback g hHX hu hloc hx
  · simp [pullbackFunction, dif_neg hW]

open MMP.Intersection in
/-- The pull-back of a regular local equation of `H` has, along every prime divisor whose generic
point maps into its domain, the order of the pull-back of `H`. -/
private theorem ord_pullbackFunction {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (g : X ⟶ Y) {H : Y.CartierDivisor} {HX : X.CartierDivisor} (hHX : IsPullback g H HX)
    {W : Y.Opens} {h : Γ(Y, W)} (hu : IsUnit (toTotalQuotient W h))
    (hloc : IsLocalEquationOn H W hu.unit) (P : MMP.Mori.PrimeDivisor X)
    (hP : g P.genericPoint ∈ W) :
    X.ord (pullbackFunction g W h) P.genericPoint = primeDivisorOrder P HX := by
  rw [pullbackFunction_eq g h hP]
  exact (primeDivisorOrder_eq_ord_of_isPullback g hHX hu hloc P hP
    (germ_ne_zero_of_isPullback g hHX hu hloc hP)).symm

open MMP.Intersection in
/-- **Removing the base twist.** Let `H` be a Cartier divisor on `Z` with regular local equation
`h` on `W`, `f : T ⟶ Z`, `Hᵢ` the pull-backs of `H` to the normalization components, and
`Θ'ᵢ = Θᵢ + (p/q) Hᵢ` with `q > 0`. If `s` is an adjoint generator of `m(K + Θ')` on `U ⊆ f⁻¹ W`,
then `h^{mp} s^q` is an adjoint generator of `mq(K + Θ)` on `U`. -/
private theorem isAdjointGeneratorOn_untwist {k : Type u} [Field k] [PerfectField k]
    {T Z : Scheme.{u}} {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    {N : NormalizationComponents sT hT} {d : ℕ} [∀ i, LocallyOfFiniteType (N.n i ≫ sT)]
    (hd : ∀ i, letI := functionFieldAlgebra (N.n i ≫ sT)
      (Algebra.trdeg k (N.X i).functionField).toNat = d)
    (b : ∀ i, letI := functionFieldAlgebra (N.n i ≫ sT)
      Module.Basis Unit (N.X i).functionField
        (⋀[(N.X i).functionField]^d Ω[(N.X i).functionField⁄k]))
    (f : T ⟶ Z) {H : Z.CartierDivisor} {HN : ∀ i, (N.X i).CartierDivisor}
    (hHN : ∀ i, IsPullback (N.n i ≫ f) H (HN i)) {W : Z.Opens} {h : Γ(Z, W)}
    (hu : IsUnit (toTotalQuotient W h)) (hloc : IsLocalEquationOn H W hu.unit)
    {p q : ℕ} (hq : 0 < q) {Θ Θ' : ∀ i, QDivisor (N.X i)}
    (hΘ' : ∀ i P, (Θ' i).coeff P = (Θ i).coeff P + ((p : ℚ) / q) * primeDivisorOrder P (HN i))
    {m : ℕ} {U : T.Opens} (hUW : U ≤ f ⁻¹ᵁ W) {s : ∀ i, RationalPluriForms (N.n i ≫ sT) d m}
    (hs : IsAdjointGeneratorOn N d m Θ' U s) :
    IsAdjointGeneratorOn N d (m * q) Θ U fun i =>
      pullbackFunction (N.n i ≫ f) W h ^ (m * p) • pluriPow (b i) m q (s i) := by
  refine ⟨fun i => ?_, fun i j P P' heq hQU hQD hne => ?_⟩
  · refine generatesOn_pow_smul_pluriPow (hd i) (b i) hq
      (pullbackFunction_ne_zero _ (hHN i) hu hloc) (fun Γ hΓ => ?_) (hΘ' i) (hs.1 i)
    rw [PrimeDivisor.support_eq_closure,
      closure_inter_open_nonempty_iff (TopologicalSpace.Opens.isOpen _)] at hΓ
    obtain ⟨y, hy, hyU⟩ := hΓ
    rw [Set.mem_singleton_iff.mp hy] at hyU
    exact ord_pullbackFunction _ (hHN i) hu hloc Γ (hUW hyU)
  · obtain ⟨V, hP, hP', av, g, h1, h2⟩ := hs.2 i j P P' heq hQU hQD hne
    have hV'W : V ⊓ f ⁻¹ᵁ W ≤ f ⁻¹ᵁ W := inf_le_right
    have hQV' : (N.n i).base P.genericPoint ∈ V ⊓ f ⁻¹ᵁ W := ⟨hP, hUW hQU⟩
    have hQ'V' : (N.n j).base P'.genericPoint ∈ V ⊓ f ⁻¹ᵁ W := heq ▸ hQV'
    let u : Γ(T, V ⊓ f ⁻¹ᵁ W) := T.presheaf.map (homOfLE hV'W).op (f.app W h)
    have hφu : ∀ (l : N.ι) (R : MMP.Mori.PrimeDivisor (N.X l))
        (hR : (N.n l).base R.genericPoint ∈ V ⊓ f ⁻¹ᵁ W),
        algebraMap _ (N.X l).functionField ((N.X l).presheaf.germ ((N.n l) ⁻¹ᵁ (V ⊓ f ⁻¹ᵁ W))
          R.genericPoint hR ((N.n l).app _ u)) = pullbackFunction (N.n l ≫ f) W h := by
      intro l R hR
      rw [pullbackFunction_eq (N.n l ≫ f) h (hV'W hR)]
      congr 1
      rw [← Scheme.Hom.germ_stalkMap_apply, TopCat.Presheaf.germ_res_apply,
        Scheme.Hom.germ_stalkMap_apply]
      rfl
    refine ⟨V ⊓ f ⁻¹ᵁ W, hQV', hQ'V', fun l => T.presheaf.map (homOfLE inf_le_left).op (av l),
      T.presheaf.map (homOfLE inf_le_left).op g ^ q * u ^ (m * p), ?_, ?_⟩
    · simpa only [one_pow] using
        isLogResiduePresentation_pow_smul N q (m * p) inf_le_left hQV' h1 (b i) u
          (hφu i P hQV')
    · simpa only [← pow_mul] using
        isLogResiduePresentation_pow_smul N q (m * p) inf_le_left hQ'V' h2 (b j) u
          (hφu j P' hQ'V')

private theorem solution :
    ∀ {T : Scheme.{0}} {sT : T ⟶ Spec (.of ℂ)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    {N : NormalizationComponents sT hT} {Δ : QWeilDivisor T}
    {Θ : ∀ i, QDivisor (N.X i)} (h : IsSdltAdjointPair N 3 Δ Θ)
    {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of ℂ)} (hZ : Mori.IsProjectiveVariety ℂ sZ)
    (f : T ⟶ Z) (hf : f ≫ sZ = sT)
    (hsemi : ∀ i, ∃ K : Divisor (N.X i), K.IsCanonicalDivisor (N.n i ≫ sT) 3 ∧
      QDivisor.IsRelativelySemiample (N.n i ≫ f) (Divisor.toQDivisor K + Θ i)),
    ∃ m : ℕ, 0 < m ∧ ∀ x : T, ∃ (V : Z.Opens) (_ : f x ∈ V)
      (t : ∀ i, RationalPluriForms (N.n i ≫ sT) 3 m),
      ∀ y ∈ f ⁻¹ᵁ V, ∃ (U : T.Opens) (_ : y ∈ U) (_ : U ≤ f ⁻¹ᵁ V)
        (g : ∀ i, RationalPluriForms (N.n i ≫ sT) 3 m) (a : Γ(T, U)),
          IsAdjointGeneratorOn N 3 m Θ U g ∧ (y = x → IsUnit a) ∧
          ∀ i (_ : Nonempty (N.n i ⁻¹ᵁ U)),
            t i = ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ U)).hom ((N.n i).app U a) • g i := by
  intro T sT hT N Δ Θ h Z sZ hZ f hf hsemi
  classical
  haveI : AlgebraicGeometry.IsVariety ℂ sZ := hZ.toIsVariety
  haveI : IsIntegral Z := AlgebraicGeometry.IsVariety.toIsIntegral sZ
  haveI : LocallyOfFiniteType sT := h.isNFold.1.2.1
  haveI : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian sT
  have hK0 : ∀ i, ∃ K : Divisor (N.X i), K.IsCanonicalDivisor (N.n i ≫ sT) 3 := fun i => by
    obtain ⟨K, hK⟩ := h.exists_isDltPair i
    exact ⟨K, hK.1.2.1⟩
  haveI : ∀ i, LocallyOfFiniteType (N.n i ≫ sT) := fun i =>
    (N.isNormalVariety i).1.toLocallyOfFiniteType
  have hdim : ∀ i, topologicalKrullDim (N.X i) = 3 := fun i => (hK0 i).choose_spec.1
  have htr : ∀ i, (letI := functionFieldAlgebra (N.n i ≫ sT)
      (Algebra.trdeg ℂ (N.X i).functionField).toNat = 3) := fun i =>
    toNat_trdeg_functionField_of_topologicalKrullDim_eq (hdim i)
  have hb := fun i => (exists_basis_topForms (sX := N.n i ≫ sT) (hdim i)).some
  -- semiampleness over `Z` for every canonical divisor
  have hL : ∀ (i : N.ι) (K : Divisor (N.X i)), K.IsCanonicalDivisor (N.n i ≫ sT) 3 →
      QDivisor.IsRelativelySemiample (N.n i ≫ f) (Divisor.toQDivisor K + Θ i) := by
    intro i K hK
    obtain ⟨K₀, hK₀, hs⟩ := hsemi i
    haveI : QuasiCompact (N.n i ≫ sT) := (N.isNormalVariety i).1.toQuasiCompact
    haveI : CompactSpace (N.X i) := QuasiCompact.compactSpace_of_compactSpace (N.n i ≫ sT)
    obtain ⟨φ, hφ⟩ := MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor (N.n i ≫ sT)
      (N.isNormalVariety i) hK hK₀
    have e : Divisor.toQDivisor K + Θ i =
        Divisor.toQDivisor K₀ + Θ i + Divisor.toQDivisor (principalDivisor φ) := by
      rw [← hφ, map_sub]; abel
    rw [e]
    exact isRelativelySemiample_add_principalDivisor (N.n i ≫ f) hs φ
  -- the common base twist
  obtain ⟨H, c, hHe, -, hc0, -, HT, HN, -, hHN, Δ', Θ', -, hΘ', h', hsemi'⟩ :=
    h.exists_isSdltAdjointPair_add_pullback N sZ hZ.isProjective f hf hL 1 one_pos
  -- the twisted adjoint is globally semiample
  obtain ⟨m, hm, -, hgen⟩ := h'.exists_isAdjointGeneratorOn_of_isRelativelySemiample fun i => by
    obtain ⟨K, hK⟩ := hK0 i
    exact ⟨K, hK, (hsemi' i K hK).1⟩
  -- write `c = p / q`
  set p : ℕ := c.num.toNat
  set q : ℕ := c.den
  have hqpos : 0 < q := c.den_pos
  have hcpq : c = (p : ℚ) / q := by
    have hnum : (0 : ℤ) ≤ c.num := (Rat.num_pos.mpr hc0).le
    have e : ((c.num.toNat : ℕ) : ℚ) = (c.num : ℚ) := by exact_mod_cast Int.toNat_of_nonneg hnum
    rw [e]
    exact (Rat.num_div_den c).symm
  have hΘq : ∀ i P, (Θ' i).coeff P =
      (Θ i).coeff P + ((p : ℚ) / q) * MMP.Intersection.primeDivisorOrder P (HN i) := by
    intro i P; rw [hΘ', hcpq]
  refine ⟨m * q, Nat.mul_pos hm hqpos, fun x => ?_⟩
  obtain ⟨t', ht'pres, U₀, hxU₀, ht'gen⟩ := hgen x
  obtain ⟨W, hfxW, φW, hu, hloc⟩ := hHe (f x)
  let untw : (∀ i, RationalPluriForms (N.n i ≫ sT) 3 m) →
      ∀ i, RationalPluriForms (N.n i ≫ sT) 3 ((m * q : ℕ) : ℤ) := fun s i =>
    pullbackFunction (N.n i ≫ f) W φW ^ (m * p) • pluriPow (hb i) m q (s i)
  have huntw : ∀ {U : T.Opens} {s}, IsAdjointGeneratorOn N 3 m Θ' U s →
      IsAdjointGeneratorOn N 3 (m * q) Θ (U ⊓ f ⁻¹ᵁ W) (untw s) := fun hs =>
    isAdjointGeneratorOn_untwist htr hb f hHN hu hloc hqpos hΘq inf_le_right
      (isAdjointGeneratorOn_mono hs inf_le_left)
  refine ⟨W, hfxW, untw t', fun y hy => ?_⟩
  by_cases hyx : y = x
  · subst hyx
    refine ⟨U₀ ⊓ f ⁻¹ᵁ W, ⟨hxU₀, hy⟩, inf_le_right, untw t', 1, huntw ht'gen,
      fun _ => isUnit_one, fun i hi => ?_⟩
    haveI := hi
    rw [map_one, map_one, one_smul]
  · obtain ⟨U, hyU, g', a', hg', ht'eq⟩ := ht'pres y
    refine ⟨U ⊓ f ⁻¹ᵁ W, ⟨hyU, hy⟩, inf_le_right, untw g',
      T.presheaf.map (homOfLE inf_le_left).op a' ^ q, huntw hg',
      fun h => absurd h hyx, fun i hi => ?_⟩
    haveI := hi
    have hiU : Nonempty ((N.n i) ⁻¹ᵁ U) := ⟨⟨hi.some.1, hi.some.2.1⟩⟩
    change _ • pluriPow (hb i) m q (t' i) = _ • (_ • pluriPow (hb i) m q (g' i))
    rw [ht'eq i hiU, map_pow, map_pow, germToFunctionField_app_map (N.n i) inf_le_left a',
      pluriPow_smul, smul_comm]

end

end Proof_thm_fourfold_projective_sdlt_threefold_relative_normalized_generation

end

open CategoryTheory AlgebraicGeometry

namespace MMP.Fourfold

open MMP.Mori MMP.Flips

/-- **Relative semiampleness glues on a projective sdlt threefold.** Let `(T, Δ; L)` be a
projective sdlt adjoint pair of dimension three over `ℂ` (`MMP.Fourfold.IsSdltAdjointPair`) with
normalization components `νᵢ : Tᵢ ⟶ T` and boundaries `Θᵢ`, and let `f : T ⟶ Z` be a morphism
to a projective complex variety. Suppose each normalized adjoint `K_{Tᵢ} + Θᵢ` is semiample over
`Z` (`MMP.Fourfold.QDivisor.IsRelativelySemiample` along `νᵢ ≫ f`). Then `L` is `f`-semiample:
there is `m > 0` such that for every `x ∈ T` there are an open `V ∋ f(x)` of `Z` and a section
`t` of `𝒪_T(mL)` over `f⁻¹(V)` generating `𝒪_T(mL)` at `x`; near each point of `f⁻¹(V)`, `t` is
`ν^*a · g` for a function `a` (a unit near `x`) and a local generator `g` of `𝒪_T(mL)`
(`MMP.Fourfold.IsAdjointGeneratorOn`). -/
@[mmp "thm_fourfold_projective_sdlt_threefold_relative_normalized_generation"]
public theorem IsSdltAdjointPair.exists_isAdjointGeneratorOn_of_isRelativelySemiample_comp
    {T : Scheme.{0}} {sT : T ⟶ Spec (.of ℂ)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    {N : NormalizationComponents sT hT} {Δ : QWeilDivisor T}
    {Θ : ∀ i, QDivisor (N.X i)} (h : IsSdltAdjointPair N 3 Δ Θ)
    {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of ℂ)} (hZ : Mori.IsProjectiveVariety ℂ sZ)
    (f : T ⟶ Z) (hf : f ≫ sZ = sT)
    (hsemi : ∀ i, ∃ K : Divisor (N.X i), K.IsCanonicalDivisor (N.n i ≫ sT) 3 ∧
      QDivisor.IsRelativelySemiample (N.n i ≫ f) (Divisor.toQDivisor K + Θ i)) :
    ∃ m : ℕ, 0 < m ∧ ∀ x : T, ∃ (V : Z.Opens) (_ : f x ∈ V)
      (t : ∀ i, RationalPluriForms (N.n i ≫ sT) 3 m),
      ∀ y ∈ f ⁻¹ᵁ V, ∃ (U : T.Opens) (_ : y ∈ U) (_ : U ≤ f ⁻¹ᵁ V)
        (g : ∀ i, RationalPluriForms (N.n i ≫ sT) 3 m) (a : Γ(T, U)),
          IsAdjointGeneratorOn N 3 m Θ U g ∧ (y = x → IsUnit a) ∧
          ∀ i (_ : Nonempty (N.n i ⁻¹ᵁ U)),
            t i = ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ U)).hom ((N.n i).app U a) • g i :=
              by revert T sT hT N Δ Θ h Z sZ hZ f hf hsemi; first | exact Proof_thm_fourfold_projective_sdlt_threefold_relative_normalized_generation.solution | exact Proof_thm_fourfold_projective_sdlt_threefold_relative_normalized_generation.solution _ | exact Proof_thm_fourfold_projective_sdlt_threefold_relative_normalized_generation.solution _ _ | exact Proof_thm_fourfold_projective_sdlt_threefold_relative_normalized_generation.solution _ _ _ | exact Proof_thm_fourfold_projective_sdlt_threefold_relative_normalized_generation.solution _ _ _ _

end MMP.Fourfold

