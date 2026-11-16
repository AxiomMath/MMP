module
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.SdltAdjointPair
public import MMP.AlgebraicGeometry.MMP.Fourfold.LogMinimalModel
public import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.Morphisms.Birational.FiniteFibreLocus
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.RingTheory.DiscreteValuationRing.Integrality
import MMP.AlgebraicGeometry.Divisor.FloorSectionAlgebraFG
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalCurveNegativity
import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.PushforwardComparison
import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.ValuativeSections
import MMP.AlgebraicGeometry.Divisor.CartierLineBundle
import MMP.AlgebraicGeometry.Divisor.AmpleSectionDivisor
import MMP.AlgebraicGeometry.Positivity.RelativeAmplePullbackTwist
import MMP.AlgebraicGeometry.Divisor.InvertibleSheafOfEffective
import MMP.AlgebraicGeometry.Divisor.MeromorphicFunctionField
import MMP.AlgebraicGeometry.MMP.BasepointFree.RelativelyFreeTwist
import MMP.AlgebraicGeometry.Positivity.SemiampleDescent
import MMP.AlgebraicGeometry.Divisor.PullbackExistence
import MMP.AlgebraicGeometry.Bertini.ReducedGeneralMember
import MMP.AlgebraicGeometry.Resolution.MaximalOrderAttained
import MMP.AlgebraicGeometry.Divisor.LocalSectionDivisor
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Divisor.LinearSystem
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.Singularities.DltLogResolutionCriterion
import MMP.AlgebraicGeometry.Singularities.DiscrepancyBoundaryChange
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Positivity.SerreAmpleCartier
import StacksFrontier.AlgebraicGeometry.AmpleCharacterization.NineClauses
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheafSections

/-!
# A common general base twist of an sdlt adjoint pair

Let `(T, Δ; L)` be a projective sdlt adjoint pair over an algebraically closed field `k` of
characteristic zero, with normalization components `νᵢ : Tᵢ ⟶ T` and normalized boundaries
`Θᵢ = Cᵢ + Δᵢ`, and let `f : T ⟶ Z` be a morphism to a projective variety over `k` such that
every normalized adjoint `K_{Tᵢ} + Θᵢ` is semiample over `Z`. Then for every `ε > 0` there are
an ample effective Cartier divisor `H` on `Z` and a rational `0 < c < ε` such that, with
`G = c H`, the pair `(T, Δ + f^*G; L + f^*G)` is again an sdlt adjoint pair whose normalized
adjoints `K_{Tᵢ} + Θᵢ + (f ∘ νᵢ)^*G` are globally semiample, hence globally nef.

One takes `H` a general member of `|aMA|`, `A` ample and `a ≫ 0`, and `c = a⁻¹`. The proof
has a part on the normalization and a part on `T`.

* Serre generation makes the twists `K_{Tᵢ} + Θᵢ + a⁻¹(f ∘ νᵢ)^*H` globally semiample: the
  nonvanishing loci `Z_σ` of sections of the multiples of the ample `A` form a basis of `Z`, so
  a section `ψ` of `𝒪(rLᵢ)` over `(f ∘ νᵢ)⁻¹(Z_σ)` generating it at a point becomes, after
  multiplication by a power of `(f ∘ νᵢ)^*σ`, a global section of `𝒪(r(Lᵢ + (f ∘ νᵢ)^*NA))`
  generating it there.
* A general member `H` keeps the pairs `(Tᵢ, Θᵢ + a⁻¹(f ∘ νᵢ)^*H)` dlt. On a fixed log
  resolution `Yᵢ ⟶ Tᵢ` of `(Tᵢ, Θᵢ)` and on the snc locus of `(Tᵢ, Θᵢ)` the pulled-back system
  is free; by Bertini its general member is reduced and snc with the fixed snc divisors, and it
  contains none of the generic points of their components, so the discrepancies over the
  non-snc locus are unchanged.
* On `T`, the boundary `Δ' = Δ + a⁻¹ f^*H` stays a boundary avoiding the double locus, and
  `Θ'ᵢ = Θᵢ + a⁻¹ (f ∘ νᵢ)^*H` is again `Cᵢ + Δ'ᵢ`: `νᵢ` is a local isomorphism at points of
  `Tᵢ` over a normal point of `T`, so the orders of `f^*H` and `(f ∘ νᵢ)^*H` agree along
  corresponding prime divisors.
* The local generators `sᵢ` of `𝒪_T(m(K_T + Δ))` give generators `φᵢ^{-m} sᵢ^a` of
  `𝒪_T(ma(K_T + Δ'))`, where `φᵢ` is a local equation of `(f ∘ νᵢ)^*H`. Since `H` misses the
  image of the double locus, the residue identification is transported with the sign
  `(-1)^{ma}`.

## Main results

* `MMP.Fourfold.IsSdltAdjointPair.exists_isSdltAdjointPair_add_pullback`: for an sdlt adjoint
  pair whose normalized adjoints are semiample over `Z`, one general small base twist `c • H` keeps
  it sdlt and makes every normalized adjoint globally semiample and nef.
* `MMP.Mori.IsDltPair.exists_isDltPair_add_inv_smul_pullback`: for a single dlt pair
  `(X, Θ)` over `Z`, a general member `H ∈ |aMA|` with `a > 1/ε` keeps `(X, Θ + a⁻¹ g^*H)` dlt.
* `MMP.Fourfold.exists_isEffective_isRelativelyAmpleQ`: a projective variety carries an
  effective ample Cartier divisor.
* `MMP.Fourfold.primeDivisorOrder_eq_zero_of_isPullback`: `ord_P g^*H = 0` when
  `g(η_P) ∉ Supp H`.
* `MMP.Fourfold.coeff_eq_mul_of_isWeilDivisorOfCartier_realization`: the Weil divisor of the
  realization of `q • C`, for a `ℚ`-Cartier divisor `C` with Weil `ℚ`-divisor `D`, is `q • D`.
* `MMP.Fourfold.QDivisor.isRelativelySemiample_of_isRelativelyFreeCartier`: a `ℚ`-divisor with a
  positive multiple the Weil divisor of an `f`-free Cartier divisor is semiample over the base.
* `MMP.Fourfold.QDivisor.isRelativelySemiample_iff_exists_isRelativelyFreeDivisor`: a
  `ℚ`-divisor `D` with a Cartier multiple `L = mD` is semiample over the base if and only if some
  positive multiple of `L` is relatively free.
* `MMP.Fourfold.QDivisor.IsRelativelySemiample.add_principalDivisor`: relative semiampleness is
  invariant under adding a principal divisor.
* `MMP.Fourfold.epi_counit_of_iso`: surjectivity of the counit of `f^* ⊣ f_*` at a module
  depends only on its isomorphism class.
* `MMP.Mori.isRelativelyFreeCartier_of_iso`: `f`-freeness depends only on the sheaf `𝒪(E)` up to
  isomorphism.
* `MMP.Mori.epi_counit_app_pullback`: the counit of `f^* ⊣ f_*` is an epimorphism at every
  pulled-back module.

## Implementation notes

The source works over `ℂ`; the statement is over any algebraically closed field of
characteristic zero. The added divisor `f^*G` is described by its coefficients: `Δ + f^*G` is a
`ℚ`-Weil divisor whose coefficient along a prime divisor `Γ` of `T` is
`Δ_Γ + c · ord_Γ(f^*H)`, and on `Tᵢ` the new boundary has coefficient
`(Θᵢ)_P + c · ord_P((f ∘ νᵢ)^*H)`, where `f^*H` and `(f ∘ νᵢ)^*H` are pull-backs of the Cartier
divisor `H` (`MMP.Intersection.IsPullback`). Global semiampleness and nefness are the relative
notions over `Spec k`.

The `a`-th power of a rational `m`-canonical form, a form of degree `ma`, is defined through a
basis of the line `Ω^n_{k(X)/k}` and does not depend on that basis.

The linear system on `Z` is a finite family of sections `sⱼ` of `𝒪_Z(aMA)`, read as elements of
`Γ(Z, 𝓜_Z)`, and a member is `∑ cⱼ sⱼ` for a coefficient vector `c ∈ kᴺ⁺¹`. A section `σ` is
pulled back to a normal variety `W ⟶ Z` as the rational function `g^*(σ f₀) ∈ K(W)`, `f₀` a
local equation at the image of the generic point; the order of the pulled-back divisor of `σ`
along a prime divisor `P` is the order of this function plus a constant depending only on `P`,
which identifies the pulled-back divisors with divisors of zeros of sections on `W` without
assuming `W ⟶ Z` dominant. Every genericity condition is the nonvanishing of a polynomial in
`c`, and one `c` avoids the finitely many of them over the infinite field `k`.

## References

* [J. Kollár, *Singularities of the minimal model program*][Kollar2013], Section 5.1
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Flips

namespace MMP.Fourfold

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

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
private def formPow {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
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
    Γ.ordForm (formPow b m a τ) = a * Γ.ordForm τ := by
  letI := stalkAlgebra sX Γ.genericPoint
  letI := functionFieldAlgebra sX
  haveI := isScalarTower_stalk_functionField sX Γ.genericPoint
  obtain ⟨σ, hσ, h0⟩ := Γ.exists_topForms_generator hd
  rw [Γ.ordForm_eq _ hσ h0, Γ.ordForm_eq _ hσ h0]
  let τ' : PluriForms k X.functionField d (m : ℤ) := τ
  have hc : formCoeff (k := k) Γ.localRing hσ h0 τ' ≠ 0 := by
    rwa [Ne, formCoeff_eq_zero_iff]
  have e := formCoeff_linePow (k := k) hσ h0 b m a τ'
  unfold formPow
  erw [e]
  exact Scheme.ord_pow hc a _

/-- An integral scheme is its own unique irreducible component. -/
private theorem univ_mem_irreducibleComponents (X : Type*) [TopologicalSpace X]
    [IrreducibleSpace X] :
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

/-- The order of `v⁻¹` is minus the order of `v`. -/
private theorem scheme_ord_inv {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    {v : X.functionField} (hv : v ≠ 0) (z : X) : X.ord v⁻¹ z = -X.ord v z := by
  have := Scheme.ord_mul (x := z) hv (inv_ne_zero hv)
  rw [mul_inv_cancel₀ hv, Scheme.ord_one] at this
  omega

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
    X.presheaf.germ (g ⁻¹ᵁ W) P.genericPoint hP (g.app W h) with hc
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

open MMP.Mori in
/-- The line `Ω^d_{k(X)/k}` of a variety of dimension `d` over a perfect field has a basis. -/
private theorem exists_basis_topForms {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    [IsIntegral X] {sX : X ⟶ Spec (.of k)} [LocallyOfFiniteType sX] {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d) :
    letI := functionFieldAlgebra sX
    Nonempty (Module.Basis Unit X.functionField (⋀[X.functionField]^d Ω[X.functionField⁄k])) := by
  letI := functionFieldAlgebra sX
  have := essFiniteType_functionField (sX := sX)
  have hK : Module.finrank X.functionField Ω[X.functionField⁄k] = d :=
    (finrank_kaehlerDifferential_eq_trdeg k X.functionField).trans hd
  have := nontrivial_exteriorPower_of_finrank_eq k X.functionField hK
  obtain ⟨σ, hσ⟩ := exists_span_singleton_eq_top_exteriorPower hK
  have h0 : σ ≠ 0 := by
    rintro rfl
    rw [Submodule.span_zero_singleton] at hσ
    exact bot_ne_top hσ
  exact ⟨basisOfSpanSingleton hσ h0⟩

/-- A morphism which is an isomorphism over an open `U` has isomorphic stalks over `U`. -/
private theorem isIso_stalkMap_of_isIso_restrict {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens}
    [IsIso (f ∣_ U)] {x : X} (hx : f x ∈ U) : IsIso (f.stalkMap x) := by
  have h := (MorphismProperty.isomorphisms CommRingCat).arrow_mk_iso_iff
    (morphismRestrictStalkMap f U ⟨x, hx⟩)
  exact h.mp (IsOpenImmersion.instIsIsoCommRingCatStalkMap _ _)

private theorem isIso_stalkMap_comp3 {X Y Z W : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (x : X) [IsOpenImmersion f] [IsIso g] (hh : IsIso (h.stalkMap (g (f x)))) :
    IsIso ((f ≫ g ≫ h).stalkMap x) := by
  rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp]
  have hg : IsIso (g.stalkMap (f x)) := IsOpenImmersion.instIsIsoCommRingCatStalkMap _ _
  have hf : IsIso (f.stalkMap x) := IsOpenImmersion.instIsIsoCommRingCatStalkMap _ _
  have h1 := @IsIso.comp_isIso _ _ _ _ _ _ _ hh hg
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 hf

/-- **The normalization components are local isomorphisms over normal points.** If the local ring
of `T` at `νᵢ(x)` is a normal domain, then `νᵢ` induces an isomorphism of local rings at `x`: the
normalization of the variety `T` is finite and birational, hence an isomorphism over a
neighbourhood of every point with finite fibre and normal local ring. -/
private theorem isIso_stalkMap_normalizationComponents {k : Type u} [Field k] {T : Scheme.{u}}
    {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    (N : NormalizationComponents sT hT) [IsNoetherian T] [IsReduced T]
    [LocallyOfFiniteType sT] (i : N.ι) (x : N.X i)
    [IsDomain (T.presheaf.stalk ((N.n i) x))]
    [IsIntegrallyClosed (T.presheaf.stalk ((N.n i) x))] :
    IsIso ((N.n i).stalkMap x) := by
  obtain ⟨φ, hφ⟩ := N.exists_iso
  set ν := slcCurveNormalization T hT
  have hni : N.n i = Limits.Sigma.ι N.X i ≫ φ.hom ≫ ν := by
    rw [hφ, Limits.Sigma.ι_desc]
  haveI : IsFinite ν :=
    Scheme.isFinite_normalization (isNagataScheme_of_locallyOfFiniteType_over_field k sT) hT
  haveI : IsNormal (Stacks.AlgebraicGeometry.Normalization.normalizationScheme T hT) :=
    Scheme.isNormal_normalizationScheme_of_isReduced T hT
  have hbir : IsBirational ν := Scheme.isBirational_normalization T hT
  have hp : ν (φ.hom ((Limits.Sigma.ι N.X i) x)) = (N.n i) x := by
    rw [hni]; rfl
  obtain ⟨U, hQU, hiso⟩ := exists_isIso_restrict_of_finite_fiber_of_normal ν hbir
    ((N.n i) x) (Scheme.Hom.finite_preimage_singleton _ _)
  haveI := hiso
  have hst : IsIso (ν.stalkMap (φ.hom ((Limits.Sigma.ι N.X i) x))) :=
    isIso_stalkMap_of_isIso_restrict _ (hp ▸ hQU)
  have key : ∀ g : N.X i ⟶ T, g = Limits.Sigma.ι N.X i ≫ φ.hom ≫ ν →
      IsIso (g.stalkMap x) := by
    intro g hg
    subst hg
    exact isIso_stalkMap_comp3 _ _ _ _ hst
  exact key _ hni

/-- **Residue fields under an integral morphism.** For an integral morphism `f : X ⟶ Y`, the
extension of residue fields `κ(f x) → κ(x)` is algebraic: on an affine open `V ∋ f(x)` every
section over `f⁻¹(V)` is integral over `Γ(Y, V)`, and `κ(x)` is generated by the values of those
sections and their inverses. -/
private theorem isAlgebraic_residueFieldMap {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f]
    (x : X) :
    letI := (f.residueFieldMap x).hom.toAlgebra
    Algebra.IsAlgebraic (Y.residueField (f x)) (X.residueField x) := by
  letI := (f.residueFieldMap x).hom.toAlgebra
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  have hU : IsAffineOpen (f ⁻¹ᵁ V) := hV.preimage f
  have hint := IsIntegralHom.isIntegral_app f V hV
  have hx : x ∈ f ⁻¹ᵁ V := hxV
  have key : ∀ a : Γ(X, f ⁻¹ᵁ V),
      IsAlgebraic (Y.residueField (f x)) (X.evaluation (f ⁻¹ᵁ V) x hx a) := by
    intro a
    obtain ⟨p, hpm, hp⟩ := hint a
    refine ⟨p.map (Y.evaluation V (f x) hxV).hom, (hpm.map _).ne_zero, ?_⟩
    have hcomp : (algebraMap (Y.residueField (f x)) (X.residueField x)).comp
        (Y.evaluation V (f x) hxV).hom =
        (X.evaluation (f ⁻¹ᵁ V) x hx).hom.comp (f.app V).hom :=
      RingHom.ext fun s => Scheme.evaluation_naturality_apply f x hxV s
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, hcomp, ← Polynomial.hom_eval₂, hp, map_zero]
  refine ⟨fun t => ?_⟩
  obtain ⟨s, rfl⟩ := X.residue_surjective x t
  letI : Algebra Γ(X, f ⁻¹ᵁ V) (X.presheaf.stalk x) := (X.presheaf.germ _ x hx).hom.toAlgebra
  haveI := hU.isLocalization_stalk ⟨x, hx⟩
  obtain ⟨⟨a, b⟩, hab⟩ :=
    IsLocalization.mk'_surjective (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl s
  have hb : IsUnit (X.presheaf.germ _ x hx (b : Γ(X, f ⁻¹ᵁ V))) :=
    IsLocalization.map_units (X.presheaf.stalk x)
      (M := (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl) b
  have e : s * X.presheaf.germ _ x hx (b : Γ(X, f ⁻¹ᵁ V)) = X.presheaf.germ _ x hx a := by
    rw [← hab]; exact IsLocalization.mk'_spec _ _ _
  have e2 : X.residue x s =
      X.evaluation (f ⁻¹ᵁ V) x hx a * (X.evaluation (f ⁻¹ᵁ V) x hx b)⁻¹ := by
    have hres := congrArg (X.residue x).hom e
    rw [map_mul] at hres
    have hne : X.evaluation (f ⁻¹ᵁ V) x hx b ≠ 0 := (hb.map (X.residue x).hom).ne_zero
    rwa [eq_mul_inv_iff_mul_eq₀ hne]
  rw [e2]
  exact (key a).mul (key b).inv

/-- Residue fields along an open immersion followed by a morphism with algebraic residue field
extensions are again algebraic extensions. -/
private theorem isAlgebraic_residueFieldMap_comp {X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z)
    [IsOpenImmersion g] (hh : ∀ y : Y, letI := (h.residueFieldMap y).hom.toAlgebra
      Algebra.IsAlgebraic (Z.residueField (h y)) (Y.residueField y)) (x : X) :
    letI := ((g ≫ h).residueFieldMap x).hom.toAlgebra
    Algebra.IsAlgebraic (Z.residueField ((g ≫ h) x)) (X.residueField x) := by
  letI := ((g ≫ h).residueFieldMap x).hom.toAlgebra
  letI := (h.residueFieldMap (g x)).hom.toAlgebra
  have hsurj : Function.Surjective (g.residueFieldMap x).hom :=
    (ConcreteCategory.bijective_of_isIso (g.residueFieldMap x)).2
  refine ⟨fun t => ?_⟩
  obtain ⟨t', rfl⟩ := hsurj t
  obtain ⟨p, hp0, hp⟩ := (hh (g x)).isAlgebraic t'
  refine ⟨p, hp0, ?_⟩
  have key : Polynomial.eval₂ ((g.residueFieldMap x).hom.comp
      (algebraMap (Z.residueField (h (g x))) (Y.residueField (g x))))
      ((g.residueFieldMap x).hom t') p = 0 := by
    rw [← Polynomial.hom_eval₂, ← Polynomial.aeval_def, hp, map_zero]
  have hcomp : ((g ≫ h).residueFieldMap x).hom =
      (g.residueFieldMap x).hom.comp (h.residueFieldMap (g x)).hom := by
    rw [Scheme.residueFieldMap_comp]
    rfl
  show Polynomial.eval₂ ((g ≫ h).residueFieldMap x).hom ((g.residueFieldMap x).hom t') p = 0
  simp only [hcomp]
  exact key

/-- The normalization components induce algebraic extensions of residue fields. -/
private theorem isAlgebraic_residueFieldMap_normalizationComponents {k : Type u} [Field k]
    {T : Scheme.{u}} {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    (N : NormalizationComponents sT hT) (i : N.ι) (x : N.X i) :
    letI := ((N.n i).residueFieldMap x).hom.toAlgebra
    Algebra.IsAlgebraic (T.residueField ((N.n i) x)) ((N.X i).residueField x) := by
  obtain ⟨φ, hφ⟩ := N.exists_iso
  set ν := slcCurveNormalization T hT
  have hni : N.n i = Limits.Sigma.ι N.X i ≫ (φ.hom ≫ ν) := by
    rw [hφ, Limits.Sigma.ι_desc]
  have key : ∀ g : N.X i ⟶ T, g = Limits.Sigma.ι N.X i ≫ (φ.hom ≫ ν) →
      letI := (g.residueFieldMap x).hom.toAlgebra
      Algebra.IsAlgebraic (T.residueField (g x)) ((N.X i).residueField x) := by
    intro g hg
    subst hg
    exact isAlgebraic_residueFieldMap_comp _ _ (fun y => isAlgebraic_residueFieldMap _ y) x
  exact key _ hni

open MMP.Intersection in
/-- A pull-back of a Cartier divisor has order zero along every prime divisor whose generic
point maps outside the support. -/
theorem primeDivisorOrder_eq_zero_of_isPullback {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    (g : X ⟶ Y) {H : Y.CartierDivisor} {HX : X.CartierDivisor} (hHX : IsPullback g H HX)
    (P : MMP.Mori.PrimeDivisor X) (hP : g P.genericPoint ∉ cartierSupport H) :
    primeDivisorOrder P HX = 0 := by
  have h2 : IsLocalEquationAt HX P.genericPoint 1 :=
    hHX.isLocalEquationAt (isLocalEquationAt_one_of_notMem_cartierSupport hP)
      (isFraction_one_one_one _) (by simpa using isFraction_one_one_one _)
  exact (isOrderAlong_zero_of_isLocalEquationAt_one (V := primeDivisorSubvariety P)
    h2).primeDivisorOrder_eq

/-- An epimorphic counit of `f^* ⊣ f_*` stays epimorphic along an isomorphism of modules. -/
theorem epi_counit_of_iso {X Z : Scheme.{u}} (f : X ⟶ Z) {M N : X.Modules} (e : N ≅ M)
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

/-- The unit of `K(Y) = ∏_Z 𝒪_{Y,η_Z}` defined by a non-zero rational function. -/
private def unitOfFunction {φ : Y.functionField} (hφ : φ ≠ 0) :
    (RationalFunctions Y)ˣ :=
  Units.map (toRationalFunctions (Y := Y)).toMonoidHom (Units.mk0 φ hφ)

variable [IsLocallyNoetherian Y] [IsNormal Y]

/-- A section of `𝒪_Y(M)` whose rational function is `φ ≠ 0` is non-zero. -/
private theorem ne_zero_of_sectionToRationalFunctions_eq {M : Divisor Y}
    {s : M.divisorialSubmodule ⊤} {φ : Y.functionField} (hφ : φ ≠ 0)
    (hs : Divisor.sectionToRationalFunctions s = toRationalFunctions φ) : s ≠ 0 := by
  rintro rfl
  haveI : Nontrivial (RationalFunctions Y) :=
    Pi.nontrivial_at ⟨Set.univ, univ_mem_irreducibleComponents Y⟩
  refine hφ ((toRationalFunctions (Y := Y)).injective ?_)
  rw [← hs, map_zero]
  simp [Divisor.sectionToRationalFunctions]

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

private theorem ord_unitOfFunction (P : MMP.Mori.PrimeDivisor Y) {φ : Y.functionField}
    (hφ : φ ≠ 0) : P.ord (unitOfFunction hφ) = Scheme.ord φ P.genericPoint :=
  ord_toRationalFunctions P hφ _ rfl

/-- **Local equations of a relatively free Cartier divisor.** Let `E` be a Cartier divisor with
Weil divisor `B` on a normal integral locally Noetherian scheme, `f`-free for `f : Y ⟶ Z`. Every
`x ∈ Y` has an open `U' ∋ f(x)` and a unit `ψ` of `K(Y)` with `B + div ψ` effective on `f⁻¹U'`
and zero along every prime divisor through `x`: `ψ` is a section of `𝒪_Y(E)` over `f⁻¹U'`
generating it at `x`. -/
private theorem exists_isLocalEquation_of_isRelativelyFreeCartier {Y Z : Scheme.{u}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (f : Y ⟶ Z) {E : Y.CartierDivisor}
    {B : Divisor Y} (hEB : MMP.Intersection.IsWeilDivisorOfCartier E B)
    (hfree : IsRelativelyFreeCartier f E)
    (x : Y) : ∃ U' : Z.Opens, f x ∈ U' ∧ ∃ ψ : (RationalFunctions Y)ˣ,
      (∀ P : MMP.Mori.PrimeDivisor Y, (P.support ∩ f ⁻¹ᵁ U').Nonempty →
        0 ≤ B.coeff P + P.ord ψ) ∧
      ∀ P : MMP.Mori.PrimeDivisor Y, x ∈ P.support → B.coeff P + P.ord ψ = 0 := by
  classical
  set L := MMP.CartierDivisor.sheaf E
  set adj := Scheme.Modules.pullbackPushforwardAdjunction f
  have hepiL : Epi (adj.counit.app L) :=
    epi_counit_of_iso f (Iso.refl (MMP.CartierDivisor.sheaf E)) hfree
  have : Epi ((adj.homEquiv ((Scheme.Modules.pushforward f).obj L) L).symm
      (𝟙 ((Scheme.Modules.pushforward f).obj L))) := by
    rwa [Stacks.Tag01VMVeryAmple.homEquiv_symm_id]
  obtain ⟨V', -, bsec, hxb⟩ := Stacks.Tag01VMVeryAmple.exists_mem_nonvanishingLocusOn_of_epi_adjoint
    f (𝟙 ((Scheme.Modules.pushforward f).obj L)) x
  set W' := f ⁻¹ᵁ V' with hW'
  let b : Γ(L, W') := bsec
  have hxb' : x ∈ Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn L W' b := hxb
  obtain ⟨hxW', hgerm⟩ := hxb'
  set σ := MMP.CartierDivisorSheaf.sectionVal b
  -- a local equation of `E` at `x`, and `σ = r g⁻¹` with `r` a unit at `x`
  obtain ⟨U, hxU, g, hg⟩ := MMP.Intersection.exists_isLocalEquationOn E x
  set U1 := U ⊓ W'
  have hxU1 : x ∈ U1 := ⟨hxU, hxW'⟩
  have hg1 := MMP.Intersection.isLocalEquationOn_resUnit (homOfLE (inf_le_left : U1 ≤ U)) hg
  set g1 := MMP.Intersection.resUnit (homOfLE (inf_le_left : U1 ≤ U)) g
  set b1 : Γ(L, U1) := L.presheaf.map (homOfLE (inf_le_right : U1 ≤ W')).op b with hb1
  obtain ⟨r, hr⟩ := (MMP.Intersection.mem_lineBundleSections_iff_of_isLocalEquationOn' hg1
      (MMP.CartierDivisorSheaf.sectionVal b1)).1
    (MMP.CartierDivisor.sectionVal_mem_lineBundleSections b1)
  have hb1r : b1 = r • MMP.CartierDivisor.invSection hg1 :=
    MMP.CartierDivisorSheaf.sectionVal_injective hr.symm
  have hru : IsUnit (Y.presheaf.germ U1 x hxU1 r) := by
    by_contra hnu
    apply hgerm
    have h1 : L.presheaf.germ W' x hxW' b = L.presheaf.germ U1 x hxU1 b1 := by
      rw [hb1]
      exact (TopCat.Presheaf.germ_res_apply (C := Ab.{u}) L.presheaf
        (homOfLE (inf_le_right : U1 ≤ W')) x hxU1 b).symm
    rw [h1, hb1r, Stacks.ModuleStalk.germ_smul]
    exact Submodule.smul_mem_smul ((IsLocalRing.mem_maximalIdeal _).mpr hnu) Submodule.mem_top
  -- on `U2 = D(r)` the section `σ` is a unit of `𝓜_Y`
  set U2 := Y.basicOpen r
  have hU21 : U2 ≤ U1 := Y.basicOpen_le r
  have hU2W : U2 ≤ W' := hU21.trans inf_le_right
  have hxU2 : x ∈ U2 := (Scheme.mem_basicOpen Y r x hxU1).mpr hru
  set r2 : Γ(Y, U2) := Y.presheaf.map (homOfLE hU21).op r
  have hr2 : IsUnit r2 := RingedSpace.isUnit_res_basicOpen Y.toRingedSpace r
  have hg2 := MMP.Intersection.isLocalEquationOn_resUnit (homOfLE hU21) hg1
  set g2 := MMP.Intersection.resUnit (homOfLE hU21) g1
  set σ2 := Y.totalQuotientSheaf.obj.map (homOfLE hU2W).op σ
  have hσ2 : σ2 = MMP.Intersection.toTotalQuotient U2 r2 * ((g2⁻¹ : _ˣ) : _) := by
    have h := congrArg (Y.totalQuotientSheaf.obj.map (homOfLE hU21).op) hr
    rw [map_mul, ← MMP.Intersection.toTotalQuotient_res] at h
    refine Eq.trans ?_ h.symm
    erw [hb1, MMP.CartierDivisorSheaf.sectionVal_map, MMP.Intersection.totalQuotient_map_map]
    rfl
  have hσ2u : IsUnit σ2 := by
    rw [hσ2]
    exact (hr2.map (MMP.Intersection.toTotalQuotient U2)).mul (Units.isUnit _)
  -- the rational function `φ` of `σ`
  set ξ := genericPoint Y
  have hξ : ∀ (O : Y.Opens) (y : Y), y ∈ O → ξ ∈ O := fun O y hy =>
    ((genericPoint_spec Y).specializes trivial : ξ ⤳ y).mem_open O.isOpen hy
  have hξW' : ξ ∈ W' := hξ W' x hxW'
  set φ := totalQuotientStalkToFunctionField ξ (Y.totalQuotientSheaf.presheaf.germ W' ξ hξW' σ)
  have hσgerm : ∀ (y : Y) (hy : y ∈ W'), totalQuotientStalkToFunctionField y
      (Y.totalQuotientSheaf.presheaf.germ W' y hy σ) = φ := by
    intro y hy
    have hsp : ξ ⤳ y := (genericPoint_spec Y).specializes trivial
    rw [← MMP.Intersection.totalQuotientStalkToFunctionField_stalkSpecializes hsp,
      TopCat.Presheaf.germ_stalkSpecializes_apply]
  have hσ2germ : ∀ (y : Y) (hy : y ∈ U2), totalQuotientStalkToFunctionField y
      (Y.totalQuotientSheaf.presheaf.germ U2 y hy σ2) = φ := by
    intro y hy
    rw [TopCat.Presheaf.germ_res_apply]
    exact hσgerm y (hU2W hy)
  have hφ : φ ≠ 0 := by
    rw [← hσ2germ x hxU2]
    exact ((hσ2u.map (Y.totalQuotientSheaf.presheaf.germ U2 x hxU2).hom).map
      (totalQuotientStalkToFunctionField x).hom).ne_zero
  -- `B + div φ ≥ 0` on `W'`
  have : Nonempty W' := ⟨⟨x, hxW'⟩⟩
  have hge := (MMP.Intersection.mem_lineBundleSections_iff_forall_zero_le_ord_add hEB W' hφ σ
    hσgerm).1 (MMP.CartierDivisor.sectionVal_mem_lineBundleSections b)
  -- `-B + div φ⁻¹ ≥ 0` on `U2`, as `σ⁻¹` is a section of `𝒪_Y(-E)` there
  have hnegEB : MMP.Intersection.IsWeilDivisorOfCartier (-E) (-B) := fun P => by
    have h := MMP.Intersection.isOrderAlong_primeDivisorOrder (-E) P
    rwa [map_neg, (hEB P).primeDivisorOrder_eq, ← DivisorWithCoeffs.coeff_neg] at h
  set τ : Y.totalQuotientSheaf.obj.obj (op U2) := (hσ2u.unit⁻¹).val
  have hτσ : τ * σ2 = 1 := hσ2u.val_inv_mul
  have hτmem : τ ∈ MMP.Intersection.lineBundleSections (-E) U2 := by
    refine (MMP.Intersection.mem_lineBundleSections_iff_of_isLocalEquationOn' hg2.inv τ).2
      ⟨((hr2.unit⁻¹ : _ˣ) : Γ(Y, U2)), ?_⟩
    rw [inv_inv]
    have h1 : MMP.Intersection.toTotalQuotient U2 ((hr2.unit⁻¹ : _ˣ) : Γ(Y, U2)) *
        MMP.Intersection.toTotalQuotient U2 r2 = 1 := by
      rw [← map_mul, hr2.val_inv_mul, map_one]
    calc _ = (MMP.Intersection.toTotalQuotient U2 ((hr2.unit⁻¹ : _ˣ) : Γ(Y, U2)) * (g2 : _)) *
          (σ2 * τ) := by rw [mul_comm σ2 τ, hτσ, mul_one]
      _ = τ * ((MMP.Intersection.toTotalQuotient U2 ((hr2.unit⁻¹ : _ˣ) : Γ(Y, U2)) *
          MMP.Intersection.toTotalQuotient U2 r2) * ((g2 : _) * ((g2⁻¹ : _ˣ) : _))) := by
            rw [hσ2]; ring
      _ = τ := by rw [h1, Units.mul_inv, mul_one, mul_one]
  have hτgerm : ∀ (y : Y) (hy : y ∈ U2), totalQuotientStalkToFunctionField y
      (Y.totalQuotientSheaf.presheaf.germ U2 y hy τ) = φ⁻¹ := by
    intro y hy
    have h := congrArg (fun t => totalQuotientStalkToFunctionField y
      (Y.totalQuotientSheaf.presheaf.germ U2 y hy t)) hτσ
    simp only [map_mul, map_one, hσ2germ y hy] at h
    exact eq_inv_of_mul_eq_one_left h
  have : Nonempty U2 := ⟨⟨x, hxU2⟩⟩
  have hle := (MMP.Intersection.mem_lineBundleSections_iff_forall_zero_le_ord_add hnegEB U2
    (inv_ne_zero hφ) τ hτgerm).1 hτmem
  -- the unit `ψ` of `K(Y)`
  let ψ : (RationalFunctions Y)ˣ := unitOfFunction hφ
  have hψ : ∀ P : MMP.Mori.PrimeDivisor Y, P.ord ψ = Scheme.ord φ P.genericPoint :=
    fun P => ord_unitOfFunction P hφ
  refine ⟨V', hxW', ψ, fun P hP => ?_, fun P hxP => ?_⟩
  · rw [hψ, add_comm]
    exact hge P hP
  · have h1 := hge P ⟨x, hxP, hxW'⟩
    have h2 := hle P ⟨x, hxP, hxU2⟩
    rw [scheme_ord_inv hφ, DivisorWithCoeffs.coeff_neg] at h2
    rw [hψ]
    omega

open MMP.Intersection

/-- The Weil divisor of the realization of `q • C`, for a `ℚ`-Cartier divisor `C` with Weil
`ℚ`-divisor `D`, is `q • D`. -/
theorem coeff_eq_mul_of_isWeilDivisorOfCartier_realization {X : Scheme.{u}}
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

/-- **Semiample divisors are nef.** On a normal variety `X` over `k`, a `ℚ`-divisor which is
semiample over `Spec k` has non-negative degree on every proper curve: a multiple is globally
generated, so some section of it does not vanish identically on the curve, and the degree of the
corresponding effective divisor is non-negative. -/
private theorem isRelativelyNef_of_isRelativelySemiample {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [QuasiCompact sX] (hX : MMP.Mori.IsNormalVariety k sX) {D : QDivisor X}
    (hD : QDivisor.IsRelativelySemiample sX D) :
    D.IsRelativelyNef sX sX := by
  classical
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : IsNoetherian X := ⟨⟩
  obtain ⟨C, hC, q, hq, hint, hfree⟩ := hD
  obtain ⟨B, hEB⟩ := MMP.Intersection.exists_isWeilDivisorOfCartier
    (KCartierDivisor.realization ((q : ℚ) • C) hint)
  have hBc : B.IsCartier := hEB.isCartier
  have hBq : Divisor.toQDivisor B = ((q : ℤ)) • D := by
    ext P
    rw [Divisor.coeff_toQDivisor, coeff_eq_mul_of_isWeilDivisorOfCartier_realization hC hint hEB P]
    simp [DivisorWithCoeffs.coeff_apply, zsmul_eq_mul]
  have hDq : D.IsQCartier := ⟨q, by exact_mod_cast hq.ne', B, hBq, hBc⟩
  refine ⟨hDq, fun Cv _ => ?_⟩
  obtain ⟨U', hxU', ψ, h1, h2⟩ :=
    exists_isLocalEquation_of_isRelativelyFreeCartier sX hEB hfree Cv.point
  haveI : Subsingleton (Spec (.of k)) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  have hall : ∀ y : X, sX y ∈ U' := fun y => by
    rwa [Subsingleton.elim (sX y) (sX Cv.point)]
  set B' := B + principalDivisor ψ with hB'
  have hB'c : B'.IsCartier := hBc.add (Divisor.isCartier_principalDivisor ψ)
  have hB'0 : 0 ≤ B' := by
    intro P
    have hη : P.genericPoint ∈ P.support := by
      rw [PrimeDivisor.support_eq_closure]; exact subset_closure rfl
    have := h1 P ⟨P.genericPoint, hη, hall _⟩
    show (0 : ℤ) ≤ B'.coeff P
    rwa [hB', DivisorWithCoeffs.coeff_add, coeff_principalDivisor]
  have hnot : Cv.point ∉ B'.supp := fun hm => by
    obtain ⟨P, hP, hxP⟩ := DivisorWithCoeffs.mem_supp_iff.mp hm
    exact hP (by rw [hB', DivisorWithCoeffs.coeff_add, coeff_principalDivisor]; exact h2 P hxP)
  obtain ⟨c₀, hc₀⟩ := MMP.Threefold.Mori.exists_ι_eq_point Cv.point
  have hnn := (MMP.Threefold.Mori.degreeOn_nonneg_and_eq_zero_iff sX Cv.ι Cv.dim_le B' hB'c hB'0
    ⟨c₀, hc₀ ▸ hnot⟩).1
  have hlin : B'.LinearlyEquivalent B := ⟨ψ, by rw [hB', add_sub_cancel_left]⟩
  have hdeg : B'.degreeOn k sX Cv.ι Cv.dim_le hB'c = B.degreeOn k sX Cv.ι Cv.dim_le hBc := by
    have := hB'c.isInvertibleModule_divisorialSheaf
    have := hBc.isInvertibleModule_divisorialSheaf
    exact degreeOn_eq_of_iso k sX Cv.ι Cv.dim_le hlin.divisorialSheafIso
  have hI := QDivisor.intersectionNumber_eq_of_smul k sX Cv.ι Cv.dim_le D hDq hq B hBc hBq
  have h0 : 0 ≤ D.intersectionNumber k sX Cv.ι Cv.dim_le hDq := by
    rw [hI]
    exact div_nonneg (by rw [← hdeg]; exact_mod_cast hnn) (by positivity)
  rw [QDivisor.intersectionNumber] at h0
  have hm : (0 : ℚ) < D.cartierIndex hDq := by exact_mod_cast QDivisor.cartierIndex_pos hDq
  have hd := mul_nonneg h0 hm.le
  rw [div_mul_cancel₀ _ hm.ne'] at hd
  rw [QDivisor.associatedCartier, CartierDivisorWithCoeffs.ofCartier, Finsupp.smul_single]
  simp only [Finsupp.sum_single_index, Rat.cast_zero, zero_mul, smul_eq_mul, mul_one,
    Rat.cast_div, Rat.cast_one, Rat.cast_natCast, one_div]
  exact mul_nonneg (by positivity) (by exact_mod_cast hd)

/-- `KCartierDivisor.realization` depends only on the divisor. -/
private theorem realization_congr {X : Scheme.{u}} {c c' : KCartierDivisor ℚ X}
    (e : c = c') (h : ∀ D, ∃ n : ℤ, c D = n) (h' : ∀ D, ∃ n : ℤ, c' D = n) :
    KCartierDivisor.realization c h = KCartierDivisor.realization c' h' := by
  subst e; rfl

/-- A scheme projective over a field is quasi-compact. -/
private theorem compactSpace_of_isProjectiveMorphism {k : Type u} [Field k] {X : Scheme.{u}}
    {s : X ⟶ Spec (.of k)} (hs : IsProjectiveMorphism s) : CompactSpace X :=
  haveI : IsProper s := isProper_of_isProjectiveMorphism s hs
  (quasiCompact_iff_compactSpace s).mp inferInstance

/-- The normalization of the Noetherian scheme `T` has finitely many components: the components
`Tᵢ` are the normalizations of the finitely many irreducible components of `T`. -/
private theorem finite_ι_of_isSdltAdjointPair
    {k : Type u} [Field k] {T : Scheme.{u}} [IsLocallyNoetherian T] {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    (N : NormalizationComponents sT hT) {n : ℕ} {Δ : QWeilDivisor T}
    {Θ : ∀ i, QDivisor (N.X i)} (hΔ : IsSdltAdjointPair N n Δ Θ) : Finite N.ι := by
  haveI : CompactSpace T := compactSpace_of_isProjectiveMorphism hΔ.isProjectiveMorphism
  haveI : IsNoetherian T := ⟨⟩
  haveI : IsReduced T := hΔ.isBoundary.2.1
  haveI : LocallyOfFiniteType sT := hΔ.isNFold.1.2.1
  obtain ⟨φ, -⟩ := N.exists_iso
  haveI : IsFinite (slcCurveNormalization T hT) :=
    Scheme.isFinite_normalization (isNagataScheme_of_locallyOfFiniteType_over_field k sT) hT
  haveI : CompactSpace (Stacks.AlgebraicGeometry.Normalization.normalizationScheme T hT) :=
    QuasiCompact.compactSpace_of_compactSpace (slcCurveNormalization T hT)
  haveI : CompactSpace ↥(∐ N.X : Scheme.{u}) := (Scheme.homeoOfIso φ).symm.compactSpace
  haveI : CompactSpace (Σ i, N.X i) := (sigmaMk N.X).symm.compactSpace
  have hcov : (Set.univ : Set (Σ i, N.X i)) ⊆
      ⋃ i, Set.range (@Sigma.mk N.ι (fun j => ↥(N.X j)) i) := by
    rintro ⟨i, y⟩ -
    exact Set.mem_iUnion.mpr ⟨i, y, rfl⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover _ (fun i => isOpen_range_sigmaMk) hcov
  refine Set.finite_univ_iff.mp (t.finite_toSet.subset fun i _ => ?_)
  obtain ⟨x⟩ : Nonempty (N.X i) := inferInstance
  obtain ⟨j, hj, y, hy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ ⟨i, x⟩))
  have hji : j = i := congrArg Sigma.fst hy
  exact hji ▸ hj

open MMP.Intersection in
/-- **Ampleness of the ample model in its class.** A Cartier divisor whose sheaf is ample is
relatively ample over the base as a `ℚ`-Cartier divisor. -/
private theorem isRelativelyAmpleQ_ofCartier_of_isAmple {k : Type u} [Field k] {Z : Scheme.{u}}
    (sZ : Z ⟶ Spec (.of k)) [IsProper sZ] (A : Z.CartierDivisor)
    (hAmp : Stacks.Ample.IsAmple Z (MMP.CartierDivisor.sheaf A)) :
    KCartierDivisor.IsRelativelyAmpleQ sZ (KCartierDivisor.ofCartier ℚ A) := by
  classical
  have hc : (1 : ℚ) • KCartierDivisor.ofCartier ℚ A =
      (Finsupp.single A (1 : ℤ)).mapRange (Int.cast : ℤ → ℚ) Int.cast_zero := by
    rw [one_smul, KCartierDivisor.ofCartier, Finsupp.mapRange_single, Int.cast_one]
  refine ⟨1, one_pos, fun D => ⟨(Finsupp.single A (1 : ℤ)) D, by
    rw [Nat.cast_one, hc]; rfl⟩, ?_⟩
  have hr : KCartierDivisor.realization (((1 : ℕ) : ℚ) • KCartierDivisor.ofCartier ℚ A)
      (fun D => ⟨(Finsupp.single A (1 : ℤ)) D, by rw [Nat.cast_one, hc]; rfl⟩) = A := by
    rw [realization_congr (by rw [Nat.cast_one, hc]) _
        (fun D => ⟨(Finsupp.single A (1 : ℤ)) D, rfl⟩),
      KCartierDivisor.realization_eq_sum, Finsupp.sum_single_index (by simp), one_smul]
  have h1 := MMP.Threefold.Resolution.isRelativelyAmple_of_isAmple sZ _ hAmp
  intro y
  obtain ⟨V, hV, hyV, hamp⟩ := h1 y
  refine ⟨V, hV, hyV, ?_⟩
  exact (Stacks.RelativeVeryAmple.isAmple_congr _ _
    ((RingedSpaceModuleAdjunction.modulePullback (sZ ⁻¹ᵁ V).ι.toLRSHom.toShHom).mapIso
      (eqToIso (congrArg MMP.CartierDivisor.sheaf hr) ≪≫
        Iso.refl (MMP.CartierDivisor.sheaf A)).symm)).1 hamp

open MMP.Intersection in
/-- A divisor linearly equivalent to a positive multiple of a divisor with ample sheaf is
relatively ample over the base. -/
private theorem isRelativelyAmpleQ_of_linearlyEquivalent_nsmul {k : Type u} [Field k]
    {Z : Scheme.{u}} (sZ : Z ⟶ Spec (.of k)) (hZ : IsProjectiveMorphism sZ)
    {A : Z.CartierDivisor} (hAamp : Stacks.Ample.IsAmple Z (MMP.CartierDivisor.sheaf A)) {d : ℕ} (hd
        : 0 < d)
    {H : Z.CartierDivisor} (hlin : LinearlyEquivalent H (d • A)) :
    KCartierDivisor.IsRelativelyAmpleQ sZ (KCartierDivisor.ofCartier ℚ H) := by
  haveI : IsProper sZ := isProper_of_isProjectiveMorphism sZ hZ
  haveI : CompactSpace Z := (quasiCompact_iff_compactSpace sZ).mp inferInstance
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : IsNoetherian Z := ⟨⟩
  have h1 := (MMP.Resolution.Bridges.isAmple_lineBundle_iff_nsmul A d hd).mp hAamp
  obtain ⟨e⟩ := (MMP.CartierDivisor.nonempty_sheaf_iso_iff H (d • A)).2 hlin
  have h2 : Stacks.Ample.IsAmple Z (MMP.CartierDivisor.sheaf H) :=
    (Stacks.RelativeVeryAmple.isAmple_congr _ _ e).mpr h1
  exact isRelativelyAmpleQ_ofCartier_of_isAmple sZ H
    ((Stacks.RelativeVeryAmple.isAmple_congr _ _ (Iso.refl (MMP.CartierDivisor.sheaf H))).mp h2)

open scoped Classical in
/-- A prime divisor of `Tᵢ` over the double locus lies in the conductor, with coefficient at least
one in `Θᵢ`. -/
private theorem one_le_coeff_of_mem_doubleIntersectionLocus {k : Type u} [Field k]
    {T : Scheme.{u}} [IsLocallyNoetherian T] {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    (N : NormalizationComponents sT hT) {n : ℕ} {Δ : QWeilDivisor T}
    {Θ : ∀ i, QDivisor (N.X i)} (hΔ : IsSdltAdjointPair N n Δ Θ) (i : N.ι)
    (P : MMP.Mori.PrimeDivisor (N.X i))
    (hP : (N.n i).base P.genericPoint ∈ (doubleIntersectionLocus T : Set T)) :
    1 ≤ (Θ i).coeff P := by
  rw [hΔ.isAdjointBoundary i P, adjointBoundaryCoeff, if_pos hP]
  have : 0 ≤ ∑ Γ ∈ Δ.support,
      if (N.n i).base P.genericPoint = Γ.1.genericPoint then Δ Γ else 0 :=
    Finset.sum_nonneg fun Γ _ => by
      split_ifs
      · exact (hΔ.isBoundary.2.2.2 Γ).1
      · exact le_rfl
  linarith

open MMP.Intersection in
/-- **An effective ample divisor on a projective variety.** A projective integral scheme over a
field carries an effective Cartier divisor that is relatively ample over the base and whose sheaf
is ample. -/
theorem exists_isEffective_isRelativelyAmpleQ {k : Type u} [Field k] {Z : Scheme.{u}}
    [IsIntegral Z] (sZ : Z ⟶ Spec (.of k)) (hZ : IsProjectiveMorphism sZ) :
    ∃ A : Z.CartierDivisor, MMP.Intersection.IsEffective A ∧
      KCartierDivisor.IsRelativelyAmpleQ sZ (KCartierDivisor.ofCartier ℚ A) ∧
      Stacks.Ample.IsAmple Z (MMP.CartierDivisor.sheaf A) := by
  classical
  haveI : IsProper sZ := isProper_of_isProjectiveMorphism sZ hZ
  have hX : AlgebraicGeometry.IsProjectiveVariety k sZ :=
    (AlgebraicGeometry.isProjectiveVariety_iff k sZ).2
      ⟨@AlgebraicGeometry.IsVariety.mk k _ Z sZ inferInstance inferInstance inferInstance
        inferInstance, hZ⟩
  obtain ⟨-, L, hLinv, hLamp⟩ := Stacks.HProjective.isQuasiProjective_of_isHQuasiProjective sZ
    hX.isProjective.isHQuasiProjective
  have hL : Stacks.Ample.IsAmple Z L :=
    Stacks.HProjective.isAmple_of_isRelativelyAmple_of_isAffine sZ L hLamp
  obtain ⟨I, hI, -, -, n, hn, ⟨eI⟩⟩ :=
    MMP.Threefold.Resolution.exists_isEffectiveCartierDivisor_of_isAmple L hL isClosed_empty
      (Set.notMem_empty (genericPoint Z))
  obtain ⟨A, hA, hAI⟩ :=
    (MMP.CartierDivisor.isEffectiveCartierDivisor_iff_exists_subscheme_eq _).1 hI
  have e : MMP.CartierDivisor.sheaf A ≅ Stacks.Ample.tensorPowModule Z L (n : ℤ) :=
    MMP.CartierDivisor.sheafIsoInvertibleSheaf A hA ≪≫ eqToIso (by rw [hAI]) ≪≫ eI.symm
  have hAmp : Stacks.Ample.IsAmple Z (MMP.CartierDivisor.sheaf A) :=
    (Stacks.RelativeVeryAmple.isAmple_congr _ _ e).mpr
      (Stacks.AmplePositivePower.isAmple_tensorPowModule_of_isAmple L n hn hL)
  exact ⟨A, hA, isRelativelyAmpleQ_ofCartier_of_isAmple sZ A hAmp,
    (Stacks.RelativeVeryAmple.isAmple_congr _ _ (Iso.refl (MMP.CartierDivisor.sheaf A))).mpr hAmp⟩

/-- A `ℚ`-divisor `Q` with `nQ` the Weil divisor of an `f`-free Cartier divisor is semiample over
the base. -/
theorem QDivisor.isRelativelySemiample_of_isRelativelyFreeCartier {X Z : Scheme.{u}}
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
theorem _root_.MMP.Mori.isRelativelyFreeCartier_of_iso {X Z : Scheme.{u}} (f : X ⟶ Z)
    {E E' : X.CartierDivisor}
    (e : MMP.CartierDivisor.sheaf E' ≅ MMP.CartierDivisor.sheaf E)
    (h : IsRelativelyFreeCartier f E) : IsRelativelyFreeCartier f E' :=
  epi_counit_of_iso f e h

/-- The counit of `f^* ⊣ f_*` at a pulled-back module `f^*L` is an epimorphism. -/
theorem _root_.MMP.Mori.epi_counit_app_pullback {X Z : Scheme.{u}} (f : X ⟶ Z) (L : Z.Modules) :
    Epi ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app
      ((Scheme.Modules.pullback f).obj L)) :=
  have := IsSplitEpi.mk'
    ⟨_, (Scheme.Modules.pullbackPushforwardAdjunction f).left_triangle_components L⟩
  IsSplitEpi.epi _

open MMP.Intersection in
/-- **Relative semiampleness is a linear equivalence invariant.** Adding a principal divisor to a
relatively semiample `ℚ`-divisor keeps it relatively semiample. -/
theorem QDivisor.IsRelativelySemiample.add_principalDivisor {X Z : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {f : X ⟶ Z} {D : QDivisor X}
    (hD : QDivisor.IsRelativelySemiample f D) (φ : (RationalFunctions X)ˣ) :
    QDivisor.IsRelativelySemiample f (D + Divisor.toQDivisor (principalDivisor φ)) := by
  haveI : IsNoetherian X := ⟨⟩
  obtain ⟨C, hC, q, hq, hint, hfree⟩ := hD
  set E := KCartierDivisor.realization ((q : ℚ) • C) hint
  obtain ⟨B, hEB⟩ := exists_isWeilDivisorOfCartier E
  obtain ⟨A, hA⟩ := exists_isWeilDivisorOfCartier_principalDivisor φ
  have hw : ∀ P, (B + q • principalDivisor φ).coeff P = B.coeff P + q * P.ord φ := fun P => by
    rw [DivisorWithCoeffs.coeff_add, ← coeff_principalDivisor, ← nsmul_eq_mul]
    rfl
  have hEw : IsWeilDivisorOfCartier (E + q • A) (B + q • principalDivisor φ) := fun P => by
    have e : primeDivisorOrder P (E + q • A) = (B + q • principalDivisor φ).coeff P := by
      rw [map_add, map_nsmul, (hEB P).primeDivisorOrder_eq, (hA P).primeDivisorOrder_eq, hw,
        coeff_principalDivisor, nsmul_eq_mul]
    exact e ▸ isOrderAlong_primeDivisorOrder (E + q • A) P
  have hlin : (B + q • principalDivisor φ).LinearlyEquivalent B :=
    ⟨φ ^ q, by ext P; simp [PrimeDivisor.ord_pow]⟩
  refine QDivisor.isRelativelySemiample_of_isRelativelyFreeCartier f _ q hq _ (fun P => ?_) _ hEw
    (epi_counit_of_iso f (hEw.sheafIsoDivisorialSheaf ≪≫ hlin.divisorialSheafIso ≪≫
      hEB.sheafIsoDivisorialSheaf.symm) hfree)
  rw [hw, DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, coeff_principalDivisor]
  push_cast
  rw [coeff_eq_mul_of_isWeilDivisorOfCartier_realization hC hint hEB P]
  ring

/-- **Semiampleness through a Cartier multiple.** If `L = mD` is a Cartier Weil divisor with
`m > 0`, then the `ℚ`-divisor `D` is semiample over `Z` if and only if some positive multiple
`kL` is relatively free. -/
theorem QDivisor.isRelativelySemiample_iff_exists_isRelativelyFreeDivisor {X Z : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] (f : X ⟶ Z)
    {D : QDivisor X} {m : ℕ} (hm : 0 < m) {L : Divisor X}
    (hL : Divisor.toQDivisor L = (m : ℤ) • D) (hLc : L.IsCartier) :
    QDivisor.IsRelativelySemiample f D ↔
      ∃ k : ℕ, 0 < k ∧ IsRelativelyFreeDivisor f ((k : ℤ) • L) := by
  haveI : IsNoetherian X := ⟨⟩
  have hLP : ∀ P, (L.coeff P : ℚ) = m * D.coeff P := fun P => by
    simpa [DivisorWithCoeffs.coeff_smul, zsmul_eq_mul] using
      congrArg (DivisorWithCoeffs.coeff · P) hL
  constructor
  · rintro ⟨C, hC, q, hq, hint, hfree⟩
    obtain ⟨B, hEB⟩ := MMP.Intersection.exists_isWeilDivisorOfCartier
      (KCartierDivisor.realization ((q : ℚ) • C) hint)
    have hqL : (q : ℤ) • L = (m : ℤ) • B := by
      ext P
      have h : ((q * L.coeff P : ℤ) : ℚ) = (m * B.coeff P : ℤ) := by
        push_cast
        rw [hLP, coeff_eq_mul_of_isWeilDivisorOfCartier_realization hC hint hEB P]
        ring
      simp only [DivisorWithCoeffs.coeff_smul, smul_eq_mul]
      exact_mod_cast h
    exact ⟨q, hq, hqL ▸ isRelativelyFreeDivisor_nsmul f hEB.isCartier
      (epi_counit_of_iso f hEB.sheafIsoDivisorialSheaf.symm hfree) m⟩
  · rintro ⟨k, hk, hfree⟩
    obtain ⟨A, hA⟩ := (hLc.zsmul k).exists_isWeilDivisorOfCartier
    refine QDivisor.isRelativelySemiample_of_isRelativelyFreeCartier f D (k * m)
      (Nat.mul_pos hk hm) _ (fun P => ?_) A hA
      (epi_counit_of_iso f hA.sheafIsoDivisorialSheaf hfree)
    simp only [DivisorWithCoeffs.coeff_smul, smul_eq_mul]
    push_cast
    rw [hLP]
    ring

/-- `1` is a local equation of the zero divisor. -/
private theorem isLocalEquationAt_zero_one (Z : Scheme.{u}) (x : Z) :
    MMP.Intersection.IsLocalEquationAt (0 : Z.CartierDivisor) x 1 :=
  ⟨⊤, trivial, 1, MMP.Intersection.isLocalEquationOn_one _, by simp⟩

/-- The zero divisor is the pull-back of the zero divisor. -/
private theorem isPullback_zero {X Y : Scheme.{u}} (g : Y ⟶ X) :
    MMP.Intersection.IsPullback g (0 : X.CartierDivisor) 0 := by
  open MMP.Intersection in
  refine ⟨fun η _ => ?_, fun y => ⟨1, 1,
    ⟨1, isLocalEquationAt_zero_one _ _, isFraction_one_one_one _⟩,
    ?_, ?_, 1, isLocalEquationAt_zero_one _ _, ?_⟩⟩
  · simp [MMP.Intersection.cartierSupport]
  · simp
  · simp
  · simpa only [map_one] using MMP.Intersection.isFraction_one_one_one y

open MMP.Intersection in
private theorem notMem_cartierSupport_add (Z : Scheme.{u}) (D₁ D₂ : Z.CartierDivisor) (x : Z)
    (h₁ : x ∉ cartierSupport D₁) (h₂ : x ∉ cartierSupport D₂) : x ∉ cartierSupport (D₁ + D₂) := by
  rw [germ_cartierSupport_eq_zero_iff] at *
  rw [map_add, h₁, h₂, add_zero]

open MMP.Intersection in
/-- Pull-backs of Cartier divisors add. -/
private theorem isPullback_add {X Y : Scheme.{u}} {g : Y ⟶ X} {D₁ D₂ : X.CartierDivisor}
    {D₁' D₂' : Y.CartierDivisor} (h₁ : IsPullback g D₁ D₁') (h₂ : IsPullback g D₂ D₂') :
    IsPullback g (D₁ + D₂) (D₁' + D₂') := by
  refine ⟨fun η hη => notMem_cartierSupport_add _ _ _ _ (h₁.1 η hη) (h₂.1 η hη), fun y => ?_⟩
  obtain ⟨a₁, b₁, ⟨e₁, he₁, hf₁⟩, ha₁, hb₁, e₁', he₁', hf₁'⟩ := h₁.2 y
  obtain ⟨a₂, b₂, ⟨e₂, he₂, hf₂⟩, ha₂, hb₂, e₂', he₂', hf₂'⟩ := h₂.2 y
  refine ⟨a₁ * a₂, b₁ * b₂, ⟨e₁ * e₂, he₁.add he₂, hf₁.mul hf₂⟩, ?_, ?_, e₁' * e₂',
    he₁'.add he₂', ?_⟩
  · rw [map_mul]; exact mul_mem ha₁ ha₂
  · rw [map_mul]; exact mul_mem hb₁ hb₂
  · rw [map_mul, map_mul]; exact hf₁'.mul hf₂'

open MMP.Intersection in
/-- Pull-backs of Cartier divisors commute with multiples. -/
private theorem isPullback_nsmul {X Y : Scheme.{u}} {g : Y ⟶ X} {D : X.CartierDivisor}
    {D' : Y.CartierDivisor} (h : IsPullback g D D') : ∀ n : ℕ, IsPullback g (n • D) (n • D')
  | 0 => by simpa using isPullback_zero g
  | n + 1 => by simpa [succ_nsmul] using isPullback_add (isPullback_nsmul h n) h

section

open Opposite TopologicalSpace

attribute [local instance] AlgebraicGeometry.IsVariety.toIsIntegral

section Bertini

private theorem support_sum_single {Y : Scheme.{u}} (S : Finset (MMP.Mori.PrimeDivisor Y)) :
    (∑ F ∈ S, Finsupp.single F (1 : ℤ)).support = S := by
  classical
  ext F; simp [Finsupp.finsetSum_apply, Finsupp.single_apply]

private theorem genericPoint_mem_support {Y : Scheme.{u}} (F : MMP.Mori.PrimeDivisor Y) :
    F.genericPoint ∈ F.support := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact subset_closure rfl

/-- The invertibility of `L` in the spelling the zero scheme takes. -/
local instance isInvertible_of_isInvertibleModule {Y : Scheme.{u}} (L : Y.Modules)
    [h : Stacks.Ample.IsInvertibleModule Y L] :
    SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L := h

section ZeroScheme

/-- A frame `b` of `𝒪_Y(D)` over `V`, on which `D` has the local equation `φ`, has order
`-d_E` along every prime divisor `E` with generic point in `V`. -/
private theorem valuation_frame_eq {Y : Scheme.{u}} [IsLocallyNoetherian Y] [IsNormal Y]
    {D : Divisor Y} {V : Y.Opens} {φ : (RationalFunctions Y)ˣ} (hφ : D.IsLocalEquation V φ)
    (b : D.divisorialSubmodule V) (r : Γ(Y, V)) (E : MMP.Mori.PrimeDivisor Y)
    (hE : E.genericPoint ∈ V) (hZ : componentGenericPoint Y E.component ∈ V)
    (hr : ((φ⁻¹ : (RationalFunctions Y)ˣ) : RationalFunctions Y) E.component =
      (Y.presheaf.germ V _ hZ).hom r * b.1 ⟨E.component, hZ⟩) :
    E.valuation (b.1 ⟨E.component, hZ⟩) = WithZero.exp (-D.coeff E) := by
  have hEV : (E.support ∩ V).Nonempty := ⟨E.genericPoint, genericPoint_mem_support E, hE⟩
  have hv := congrArg E.valuation hr
  rw [PrimeDivisor.valuation_component, PrimeDivisor.ord_inv, ← hφ E hEV, map_mul] at hv
  have hne : (Y.presheaf.germ V _ hZ).hom r ≠ 0 := by
    intro h0
    rw [h0, map_zero, zero_mul] at hv
    exact WithZero.coe_ne_zero hv
  have hgerm : (Y.presheaf.germ V _ hZ).hom r =
      E.toComponent.hom ((Y.presheaf.germ V _ hE).hom r) := by
    rw [← TopCat.Presheaf.germ_stalkSpecializes_apply Y.presheaf hE E.specializes_genericPoint]
    rfl
  have hne' : (Y.presheaf.germ V _ hE).hom r ≠ 0 := by
    intro h0; apply hne; rw [hgerm, h0, map_zero]
  have h1 : 1 ≤ E.valuation ((Y.presheaf.germ V _ hZ).hom r) := by
    rw [hgerm]; exact E.one_le_valuation_toComponent hne'
  have hb0 : b.1 ⟨E.component, hZ⟩ ≠ 0 := by
    intro h0
    rw [h0, map_zero, mul_zero] at hv
    exact WithZero.coe_ne_zero hv
  refine le_antisymm ?_ ?_
  · rw [hv]
    exact le_mul_of_one_le_left' h1
  · exact ((b.2 E hEV).resolve_left hb0)

/-- **The zero scheme of a section of `𝒪_Y(D)` near a point.** Around every point there is an
affine open `V` on which the ideal of `Z(t)` is generated by a function `a`, and the coefficient
of every prime divisor `E` with generic point in `V` in the divisor of zeros `(t)₀` is the order
of `a` along `E`. -/
private theorem exists_affine_zeroScheme_ideal_eq_span {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (D : Divisor Y) (hD : D.IsCartier)
    [Stacks.Ample.IsInvertibleModule Y D.divisorialSheaf]
    (t : D.divisorialSubmodule ⊤) (ht : t ≠ 0) (x : Y) :
    ∃ (V : Y.affineOpens) (_ : x ∈ (V : Y.Opens)) (a : Γ(Y, V))
      (ha : ∀ (Z : irreducibleComponents Y) (hZ : componentGenericPoint Y Z ∈ (V : Y.Opens)),
        (Y.presheaf.germ V _ hZ).hom a ≠ 0),
      (zeroScheme Y D.divisorialSheaf t).ideal V = Ideal.span {a} ∧
      ∀ E : MMP.Mori.PrimeDivisor Y, E.genericPoint ∈ (V : Y.Opens) →
        (D.zeroDivisor t ht).coeff E =
          E.ord (MMP.Threefold.Resolution.sectionUnit a ha) := by
  obtain ⟨W, hxW, φ, hφ⟩ := hD x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hxW W.isOpen
  obtain ⟨g, hxg, hgU, ⟨e⟩⟩ := exists_basicOpen_linearEquiv D.divisorialSheaf ⟨U, hU⟩ x hxU
  let V : Y.affineOpens := ⟨Y.basicOpen g, hU.basicOpen g⟩
  have hVW : (V : Y.Opens) ≤ W := hgU.trans hUW
  set tV := D.divisorialSheaf.presheaf.map (homOfLE (le_top : (V : Y.Opens) ≤ ⊤)).op t
  set a : Γ(Y, V) := e tV with ha_def
  set b : D.divisorialSubmodule V := e.symm 1
  have htV : (tV : D.divisorialSubmodule V) = a • b := by
    change tV = a • e.symm 1
    rw [← map_smul e.symm a 1, smul_eq_mul, mul_one, ha_def, e.symm_apply_apply]
  set u := (Divisor.isUnit_sectionToRationalFunctions ht).unit
  -- the value of `t` at a component through `V`
  have hval : ∀ (Z : irreducibleComponents Y) (hZ : componentGenericPoint Y Z ∈ (V : Y.Opens)),
      (u : RationalFunctions Y) Z = (Y.presheaf.germ V _ hZ).hom a * b.1 ⟨Z, hZ⟩ := by
    intro Z hZ
    have := congrArg (fun m : D.divisorialSubmodule V => m.1 ⟨Z, hZ⟩) htV
    simp only [Submodule.coe_smul, rationalFunctions_smul_apply] at this
    exact this
  have ha : ∀ (Z : irreducibleComponents Y) (hZ : componentGenericPoint Y Z ∈ (V : Y.Opens)),
      (Y.presheaf.germ V _ hZ).hom a ≠ 0 := by
    intro Z hZ h0
    have hu := (Pi.isUnit_iff.mp u.isUnit) Z
    rw [hval Z hZ, h0, zero_mul] at hu
    exact not_isUnit_zero hu
  refine ⟨V, hxg, a, ha, zeroScheme_ideal_of_trivialization Y D.divisorialSheaf t V e a rfl,
    fun E hE => ?_⟩
  set hZ := E.specializes_genericPoint.mem_open (V : Y.Opens).isOpen hE
  -- the frame `b` has order `-d_E`
  have hr : (hφ.mono hVW).invSection = e (hφ.mono hVW).invSection • e.symm 1 := by
    rw [← map_smul e.symm _ 1, smul_eq_mul, mul_one, e.symm_apply_apply]
  have hr' := congrArg (fun m : D.divisorialSubmodule V => m.1 ⟨E.component, hZ⟩) hr
  simp only [Divisor.IsLocalEquation.invSection_apply, Submodule.coe_smul,
    rationalFunctions_smul_apply] at hr'
  have hb := valuation_frame_eq (hφ.mono hVW) b _ E hE hZ hr'
  have hv := congrArg E.valuation (hval E.component hZ)
  rw [PrimeDivisor.valuation_component, map_mul, hb,
    ← MMP.Threefold.Resolution.sectionUnit_apply a ha E.component hZ,
    PrimeDivisor.valuation_component, ← WithZero.exp_add] at hv
  have hv' := WithZero.exp_injective hv
  rw [Divisor.zeroDivisor_eq, DivisorWithCoeffs.coeff_add, coeff_principalDivisor]
  change E.ord u + _ = _
  omega

/-- Off the zero scheme of `t`, a prime divisor has coefficient `0` in `(t)₀`. -/
private theorem coeff_zeroDivisor_eq_zero_of_notMem {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (D : Divisor Y) (hD : D.IsCartier)
    [Stacks.Ample.IsInvertibleModule Y D.divisorialSheaf]
    (t : D.divisorialSubmodule ⊤) (ht : t ≠ 0) (E : MMP.Mori.PrimeDivisor Y)
    (hE : E.genericPoint ∉ (zeroScheme Y D.divisorialSheaf t).supportSet) :
    (D.zeroDivisor t ht).coeff E = 0 := by
  obtain ⟨V, hxV, a, ha, hI, hc⟩ :=
    exists_affine_zeroScheme_ideal_eq_span D hD t ht E.genericPoint
  rw [hc E hxV]
  rw [Scheme.IdealSheafData.mem_supportSet_iff_of_mem hxV, hI, Scheme.zeroLocus_span,
    Scheme.zeroLocus_singleton, Set.mem_compl_iff, not_not] at hE
  exact MMP.Threefold.Resolution.ord_sectionUnit_eq_zero a ha E hxV
    ((Y.mem_basicOpen a _ hxV).mp hE)

/-- A point off the support of `(t)₀` lies in the nonvanishing open of `t`. -/
private theorem mem_nonvanishingOpen_of_notMem_supp {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (D : Divisor Y) (hD : D.IsCartier)
    [Stacks.Ample.IsInvertibleModule Y D.divisorialSheaf]
    (t : D.divisorialSubmodule ⊤) (ht : t ≠ 0) (y : Y)
    (hy : y ∉ (D.zeroDivisor t ht).supp) :
    y ∈ Stacks.NonvanishingOpen.nonvanishingOpen Y D.divisorialSheaf t := by
  have hyZ : y ∉ (zeroScheme Y D.divisorialSheaf t).supportSet := by
    obtain ⟨V, hyV, a, ha, hI, hc⟩ := exists_affine_zeroScheme_ideal_eq_span D hD t ht y
    rw [Scheme.IdealSheafData.mem_supportSet_iff_of_mem hyV, hI, Scheme.zeroLocus_span,
      Scheme.zeroLocus_singleton, Set.mem_compl_iff, not_not, SetLike.mem_coe,
      Y.mem_basicOpen a y hyV]
    obtain ⟨c, hc'⟩ := exists_unit_stalk_of_forall_ord_eq_zero (mem_pointComponent y)
      (MMP.Threefold.Resolution.sectionUnit a ha) fun E hE => by
        have hEV : E.genericPoint ∈ (V : Y.Opens) := by
          rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hE
          exact (specializes_iff_mem_closure.mpr hE).mem_open (V : Y.Opens).isOpen hyV
        rw [← hc E hEV]
        by_contra hne
        exact hy (DivisorWithCoeffs.support_subset_supp hne hE)
    have hZ : componentGenericPoint Y (pointComponent y) ∈ (V : Y.Opens) :=
      ((isGenericPoint_componentGenericPoint Y _).specializes
        (mem_pointComponent y)).mem_open (V : Y.Opens).isOpen hyV
    have heq : (Y.presheaf.germ V y hyV).hom a = c := by
      apply stalkToRationalFunctions_injective (mem_pointComponent y)
      rw [hc', MMP.Threefold.Resolution.sectionUnit_apply a ha _ hZ]
      exact TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _
    rw [heq]
    exact c.isUnit
  set s' := (Stacks.NonvanishingSpelling.sectionsEquiv Y D.divisorialSheaf).symm t
  have hev : PresheafOfModules.sections.eval s' (Opposite.op ⊤) = t :=
    (Stacks.NonvanishingSpelling.sectionsEquiv Y D.divisorialSheaf).apply_symm_apply t
  have h := AlgebraicGeometry.nonvanishingLocus_eq_compl_supportSet_zeroScheme
    D.divisorialSheaf s' (fun h0 => ht (hev.symm.trans h0))
  have h2 := Stacks.NonvanishingSpelling.stalkNonvanishingLocus_eq Y D.divisorialSheaf s'
  have h3 : y ∈ Stacks.SheafOfModules.nonvanishingLocus D.divisorialSheaf s' := by
    rw [h]
    exact fun hm => hyZ (hev ▸ hm)
  rw [h2] at h3
  change y ∈ Stacks.Ample.nonvanishingLocus D.divisorialSheaf t
  exact hev ▸ h3

end ZeroScheme

section Projective

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **A dense open of `ℙᴺ_k` contains the general points.** For a dense open `U ⊆ ℙᴺ_k` there is
a nonzero (homogeneous) polynomial `Q` with `[c] ∈ U` whenever `Q(c) ≠ 0`: `U` contains a basic
open `D₊(f)`, and a homogeneous component of `f` not vanishing at a point of `D₊(f)` will do. -/
private theorem exists_polynomial_dualPoint_mem {k : Type u} [Field k] {N : ℕ}
    (U : (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)).Opens)
    (hU : Dense (U : Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)))) :
    ∃ Q : MvPolynomial (Fin (N + 1)) k, Q ≠ 0 ∧ ∀ (c : Fin (N + 1) → k) (hc : c ≠ 0),
      MvPolynomial.eval c Q ≠ 0 → MMP.Threefold.Bridges.dualPoint c hc ∈ U := by
  classical
  obtain ⟨p, hp⟩ := hU.nonempty
  obtain ⟨_, ⟨f, rfl⟩, hpf, hfU⟩ :=
    (ProjectiveSpectrum.isTopologicalBasis_basic_opens
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)).exists_subset_of_mem_open hp U.isOpen
  have hpf' : f ∉ (show ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)
      from p).asHomogeneousIdeal :=
    (ProjectiveSpectrum.mem_basicOpen _ f _).mp hpf
  obtain ⟨d, hd⟩ : ∃ d, MvPolynomial.homogeneousComponent d f ∉
      (show ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)
        from p).asHomogeneousIdeal := by
    by_contra h
    push Not at h
    apply hpf'
    rw [← MvPolynomial.sum_homogeneousComponent f]
    exact Ideal.sum_mem _ fun i _ => h i
  have hQ0 : MvPolynomial.homogeneousComponent d f ≠ 0 := fun h0 => hd (h0 ▸ zero_mem _)
  refine ⟨_, hQ0, fun c hc hcQ => hfU ?_⟩
  refine (ProjectiveSpectrum.mem_basicOpen _ f
    (show ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) from
      MMP.Threefold.Bridges.dualPoint c hc)).mpr fun hf => hcQ ?_
  change f ∈ ((RingHom.ker (MvPolynomial.eval c)).homogeneousCore
    (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)).toIdeal at hf
  have hcore := (HomogeneousIdeal.isHomogeneous ((RingHom.ker (MvPolynomial.eval c)).homogeneousCore
    (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k))).mem_iff.mp hf d
  have hdec : ((DirectSum.decompose (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) f d :
      MvPolynomial (Fin (N + 1)) k)) = MvPolynomial.homogeneousComponent d f :=
    MvPolynomial.decomposition.decompose'_apply f d
  rw [hdec] at hcore
  exact RingHom.mem_ker.mp (Ideal.toIdeal_homogeneousCore_le _ _ hcore)

end Projective

section WeilBertini

open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections (globalSectionsModule)

attribute [local instance] globalSectionsModule

open Classical in
/-- **Bertini's theorem for snc divisors, in Weil-divisor form.** On a smooth variety `Y` over an
algebraically closed field of characteristic zero, let `D` be a Cartier divisor and
`t : ι → H⁰(Y, 𝒪_Y(D))` finitely many sections without common zero, and let `∑_{E ∈ S} E` be
snc. For a general coefficient vector `c`, every component of the divisor of zeros of
`τ = ∑ cᵢ tᵢ` lies in a finite set `T` of prime divisors disjoint from `S` with
`∑_{E ∈ T ∪ S} E` snc. -/
private theorem exists_polynomial_zeroDivisor_isSNC {k : Type u} [Field k]
    [IsAlgClosed k] [CharZero k] {Y : Scheme.{u}} [Y.Over (Spec (.of k))]
    [IsSmoothVariety k (Y ↘ Spec (.of k))] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    (D : Divisor Y) (hD : D.IsCartier) {ι : Type*} [Fintype ι]
    (t : ι → D.divisorialSubmodule ⊤)
    (ht : ∀ y : Y, ∃ (i : ι) (hi : t i ≠ 0), y ∉ (D.zeroDivisor (t i) hi).supp)
    (S : Finset (MMP.Mori.PrimeDivisor Y))
    (hS : DivisorWithCoeffs.IsSNC (Y ↘ Spec (.of k)) (∑ E ∈ S, Finsupp.single E (1 : ℤ))) :
    ∃ Q : MvPolynomial ι k, Q ≠ 0 ∧ ∀ c : ι → k, MvPolynomial.eval c Q ≠ 0 →
      ∀ hτ : (∑ i, scalarsToGlobalSections k (Y ↘ Spec (.of k)) (c i) • t i) ≠ 0,
        ∃ T : Finset (MMP.Mori.PrimeDivisor Y),
          (∀ E, (D.zeroDivisor _ hτ).coeff E ≠ 0 → E ∈ T) ∧ Disjoint T S ∧
          DivisorWithCoeffs.IsSNC (Y ↘ Spec (.of k)) (∑ E ∈ T ∪ S, Finsupp.single E (1 : ℤ)) := by
  classical
  haveI hL := hD.isInvertibleModule_divisorialSheaf
  haveI : TopologicalSpace.NoetherianSpace Y :=
    MMP.Resolution.Aux.noetherianSpace_of_finiteType (Y ↘ Spec (.of k))
  haveI : Nonempty Y := inferInstance
  obtain ⟨i₀, -, -⟩ := ht (Nonempty.some inferInstance)
  set N := Fintype.card ι - 1
  have hcard : Fintype.card ι = N + 1 := by
    have := Fintype.card_pos_iff.mpr ⟨i₀⟩
    omega
  let e : ι ≃ Fin (N + 1) := Fintype.equivFinOfCardEq hcard
  let s : Fin (N + 1) → Γ(D.divisorialSheaf, ⊤) := fun j => t (e.symm j)
  have hsys : ∀ c : ι → k, MMP.Threefold.Bridges.systemSection (k := k) s (c ∘ e.symm) =
      ∑ i, scalarsToGlobalSections k (Y ↘ Spec (.of k)) (c i) • t i := by
    intro c
    rw [MMP.Threefold.Bridges.systemSection_apply]
    exact Fintype.sum_equiv e.symm _ _ (fun j => rfl)
  have hs : ⨆ c : Fin (N + 1) → k, Stacks.NonvanishingOpen.nonvanishingOpen Y D.divisorialSheaf
      (MMP.Threefold.Bridges.systemSection s c) = ⊤ := by
    refine eq_top_iff.mpr fun y _ => ?_
    obtain ⟨i, hi, hy⟩ := ht y
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨Pi.single (e i) 1, ?_⟩
    have h1 : MMP.Threefold.Bridges.systemSection (k := k) s (Pi.single (e i) 1) = t i := by
      rw [MMP.Threefold.Bridges.systemSection_apply,
        Finset.sum_eq_single (e i) (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp)]
      simp only [s, Equiv.symm_apply_apply, Pi.single_eq_same]
      exact one_smul k _
    rw [h1]
    exact mem_nonvanishingOpen_of_notMem_supp D hD (t i) hi y hy
  obtain ⟨U, hU, hUc⟩ := MMP.Threefold.Bridges.exists_dense_open_isSNC_zeroScheme_add s hs _ hS
  obtain ⟨Q', hQ'0, hQ'⟩ := exists_polynomial_dualPoint_mem U hU
  refine ⟨MvPolynomial.rename e.symm Q', fun h => hQ'0
    (MvPolynomial.rename_injective _ e.symm.injective (h.trans (map_zero _).symm)),
    fun c hc hτ => ?_⟩
  rw [MvPolynomial.eval_rename] at hc
  have hc0 : c ∘ e.symm ≠ 0 := by
    intro h0
    apply hτ
    rw [← hsys, h0, map_zero]
    rfl
  obtain ⟨-, T, hTcomp, hTS, hsnc⟩ := hUc (c ∘ e.symm) hc0 (hQ' _ hc0 hc)
  rw [support_sum_single] at hTS hsnc
  rw [hsys] at hTcomp
  refine ⟨T, fun E hE => ?_, hTS, hsnc⟩
  by_contra hET
  apply hE
  by_cases hEZ : E.genericPoint ∈ (zeroScheme Y D.divisorialSheaf
      (∑ i, scalarsToGlobalSections k (Y ↘ Spec (.of k)) (c i) • t i)).supportSet
  · exfalso
    obtain ⟨-, hcov⟩ := MMP.Resolution.Aux.finite_and_cover_componentsOf
      (zeroScheme Y D.divisorialSheaf
        (∑ i, scalarsToGlobalSections k (Y ↘ Spec (.of k)) (c i) • t i)).support.isClosed
    obtain ⟨W, hW, hEW⟩ := Set.mem_sUnion.mp (hcov hEZ)
    obtain ⟨E', hE'T, hE'W⟩ := (hTcomp W).mp hW
    exact hET (by
      rwa [← MMP.Threefold.Mori.primeDivisor_eq_of_genericPoint_mem_support E' E (hE'W ▸ hEW)])
  · exact coeff_zeroDivisor_eq_zero_of_notMem D hD _ hτ E hEZ

end WeilBertini

end Bertini

end

section

open Opposite TopologicalSpace

attribute [local instance] AlgebraicGeometry.IsVariety.toIsIntegral

section Trivialization

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  {D : Divisor X} {W : X.Opens} {ψ : (RationalFunctions X)ˣ}

/-- The restriction to `W` of a global unit of `K(X)`. -/
private def unitOn (W : X.Opens) (ψ : (RationalFunctions X)ˣ) :
    ToType ((rationalFunctionsPresheaf X).obj (op W)) :=
  fun Z => (ψ : RationalFunctions X) Z.1

/-- The local frame `ψ⁻¹` of `𝒪_X(D)` on an open where `ψ` is a local equation of `D`. -/
private def frame (hψ : D.IsLocalEquation W ψ) : Γ(D.divisorialSheaf, W) :=
  (⟨unitOn W ψ⁻¹, fun E hE => Or.inr (by
    change WithZero.exp _ ≤ E.valuation
      (((ψ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) E.component)
    rw [E.valuation_component, PrimeDivisor.ord_inv, hψ E hE])⟩ : D.divisorialSubmodule W)

omit [IsIntegral X] [CompactSpace X] in
private theorem secVal_frame (hψ : D.IsLocalEquation W ψ) :
    Divisor.secVal D W (frame hψ) = unitOn W ψ⁻¹ := rfl

omit [IsIntegral X] [CompactSpace X] in
private theorem secVal_smul (r : Γ(X, W)) (a : Γ(D.divisorialSheaf, W)) :
    Divisor.secVal D W (r • a) = (toRationalFunctionsPresheaf X).app (op W) r *
      Divisor.secVal D W a := by
  funext Z
  exact rationalFunctions_smul_apply r _ Z

/-- Multiplication of a regular function by the frame `ψ⁻¹`, `𝒪_W ⟶ 𝒪_X(D)|_W`. -/
private def frameMap (hψ : D.IsLocalEquation W ψ) :
    Γ(X, W) →ₗ[Γ(X, W)] Γ(D.divisorialSheaf, W) :=
  LinearMap.toSpanSingleton Γ(X, W) Γ(D.divisorialSheaf, W) (frame hψ)

omit [IsIntegral X] [CompactSpace X] in
private theorem unitOn_mul_unitOn_inv (W : X.Opens) (ψ : (RationalFunctions X)ˣ) :
    unitOn W ψ * unitOn W ψ⁻¹ = 1 := by
  funext Z
  change (ψ : RationalFunctions X) Z.1 * ((ψ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) Z.1
    = 1
  rw [← Pi.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one, Pi.one_apply]

omit [IsIntegral X] [CompactSpace X] in
private theorem frameMap_bijective (hψ : D.IsLocalEquation W ψ) :
    Function.Bijective (frameMap hψ) := by
  refine ⟨fun r r' h => ?_, fun a => ?_⟩
  · apply toRationalFunctionsPresheaf_app_injective W
    have h1 := congrArg (fun b : Γ(D.divisorialSheaf, W) => Divisor.secVal D W b * unitOn W ψ) h
    simp only [frameMap, LinearMap.toSpanSingleton_apply] at h1
    rwa [secVal_smul, secVal_smul, secVal_frame, mul_assoc, mul_assoc, mul_comm (unitOn W ψ⁻¹),
      unitOn_mul_unitOn_inv, mul_one, mul_one] at h1
  · let a' : D.divisorialSubmodule W := a
    have hb : (0 : Divisor X).IsDivisorialSection W (unitOn W ψ * Divisor.secVal D W a) := by
      intro E hE
      have hψE : E.OrdGE (E.ord ψ) ((ψ : RationalFunctions X) E.component) :=
        Or.inr (E.valuation_component ψ).ge
      refine (hψE.mul (a'.2 E hE)).mono (le_of_eq ?_)
      rw [hψ E hE]
      simp
    obtain ⟨r, hr⟩ := Divisor.IsDivisorialSection.exists_eq hb
    refine ⟨r, ?_⟩
    apply Subtype.ext
    change Divisor.secVal D W (r • frame hψ) = Divisor.secVal D W a
    rw [secVal_smul, secVal_frame, hr, mul_comm, ← mul_assoc, mul_comm _ (unitOn W ψ),
      unitOn_mul_unitOn_inv, one_mul]

/-- The trivialization `𝒪_X(D)|_W ≅ 𝒪_W` given by a local equation `ψ` of `D` on `W`. -/
private def trivialization (hψ : D.IsLocalEquation W ψ) :
    Γ(D.divisorialSheaf, W) ≃ₗ[Γ(X, W)] Γ(X, W) :=
  (LinearEquiv.ofBijective (frameMap hψ) (frameMap_bijective hψ)).symm

omit [IsIntegral X] [CompactSpace X] in
/-- The function representing a section `a` of `𝒪_X(D)` on `W` is `ψ a`. -/
private theorem toRationalFunctions_trivialization (hψ : D.IsLocalEquation W ψ)
    (a : Γ(D.divisorialSheaf, W)) :
    (toRationalFunctionsPresheaf X).app (op W) (trivialization hψ a) =
      unitOn W ψ * Divisor.secVal D W a := by
  have h := (LinearEquiv.ofBijective (frameMap hψ) (frameMap_bijective hψ)).apply_symm_apply a
  set r := trivialization hψ a
  have h1 : frameMap hψ r = a := h
  have h2 := congrArg (fun b : Γ(D.divisorialSheaf, W) => unitOn W ψ * Divisor.secVal D W b) h1
  simp only [frameMap, LinearMap.toSpanSingleton_apply] at h2
  rw [← h2, secVal_smul, secVal_frame, mul_comm, mul_assoc, mul_comm (unitOn W ψ⁻¹),
    unitOn_mul_unitOn_inv, mul_one]

end Trivialization

/-- In a domain, if `a = u ϖ^m` with `ϖ` irreducible and `(a)` is a radical ideal, then
`m ≤ 1`: otherwise `ϖ^{m-1} ∉ (a)` while `(ϖ^{m-1})² ∈ (a)`. -/
private theorem le_one_of_radical_span_eq {R : Type*} [CommRing R] [IsDomain R]
    {ϖ a : R} (hϖ : Irreducible ϖ) (u : Rˣ) (m : ℕ) (ha : a = u * ϖ ^ m)
    (hrad : (Ideal.span {a}).radical = Ideal.span {a}) : m ≤ 1 := by
  by_contra h
  push Not at h
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
  have hmem : ϖ ^ (j + 1) ∈ (Ideal.span {a}).radical := by
    refine ⟨2, Ideal.mem_span_singleton.2 ⟨(u⁻¹ : Rˣ) * ϖ ^ j, ?_⟩⟩
    rw [ha]
    calc (ϖ ^ (j + 1)) ^ 2 = (u * (u⁻¹ : Rˣ) : R) * ϖ ^ (j + 2) * ϖ ^ j := by
          rw [Units.mul_inv, one_mul]; ring
      _ = _ := by ring
  rw [hrad, Ideal.mem_span_singleton, ha] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  have h1 : ϖ ^ (j + 1) * (1 - u * ϖ * c) = 0 := by
    rw [mul_sub, mul_one, sub_eq_zero]
    calc ϖ ^ (j + 1) = u * ϖ ^ (j + 2) * c := hc
      _ = _ := by ring
  rcases mul_eq_zero.1 h1 with h | h
  · exact hϖ0 (pow_eq_zero_iff (Nat.succ_ne_zero j) |>.1 h)
  · apply hϖ.not_isUnit
    rw [sub_eq_zero] at h
    exact IsUnit.of_mul_eq_one (u * c) (by rw [h]; ring)

/-- A principal radical ideal of the sections over an affine open stays radical in each stalk,
the stalk being a localization. -/
private theorem radical_span_germ_eq {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (g : Γ(X, U)) (h : (Ideal.span {g}).radical = Ideal.span {g}) (y : X) (hy : y ∈ U) :
    (Ideal.span {(X.presheaf.germ U y hy).hom g}).radical =
      Ideal.span {(X.presheaf.germ U y hy).hom g} := by
  letI := X.presheaf.algebra_section_stalk ⟨y, hy⟩
  have := hU.isLocalization_stalk ⟨y, hy⟩
  have hmap := IsLocalization.map_radical (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl
    (X.presheaf.stalk y) (Ideal.span {g})
  rw [h, Ideal.map_span, Set.image_singleton] at hmap
  exact hmap.symm

section ZeroScheme

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  {D : Divisor X}

omit [CompactSpace X] in
/-- The function representing `σ|_W` in the trivialization by a local equation `ψ` of `D` has
component `ψ_Z σ_Z` at the irreducible component `Z`. -/
private theorem germ_trivialization_restrict {W : X.Opens} {ψ : (RationalFunctions X)ˣ}
    (hψ : D.IsLocalEquation W ψ) (σ : D.divisorialSubmodule ⊤)
    (Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ W}) :
    X.presheaf.germ W _ Z.2 (trivialization hψ
        (D.divisorialSheaf.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op σ)) =
      (ψ : RationalFunctions X) Z.1 * σ.1 ⟨Z.1, trivial⟩ :=
  congrFun (toRationalFunctions_trivialization hψ
    (D.divisorialSheaf.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op σ)) Z

/-- **A section with reduced zero scheme has a reduced divisor of zeros.** If `D` is Cartier and
the zero scheme of a nonzero section `σ` of `𝒪_X(D)` is reduced, every coefficient of
`(σ)₀ = div σ + D` is at most `1`: at the generic point of a prime divisor `E` the ideal of the
zero scheme is `(π^a)` with `a` the coefficient, and it is radical only for `a ≤ 1`. -/
private theorem coeff_zeroDivisor_le_one (hD : D.IsCartier)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property D.divisorialSheaf]
    (σ : D.divisorialSubmodule ⊤) (hσ : σ ≠ 0)
    (hred : IsReduced (AlgebraicGeometry.zeroScheme X D.divisorialSheaf σ).subscheme)
    (E : MMP.Mori.PrimeDivisor X) :
    (D.zeroDivisor σ hσ).coeff E ≤ 1 := by
  obtain ⟨U, hxU, ψ, hψ⟩ := hD E.genericPoint
  obtain ⟨W, hW, hxW, hWU⟩ := (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hxU
  have hψW := hψ.mono hWU
  set r := trivialization hψW (D.divisorialSheaf.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op σ)
    with hr
  have hideal :
      (AlgebraicGeometry.zeroScheme X D.divisorialSheaf σ).ideal ⟨W, hW⟩ = Ideal.span {r} :=
    zeroScheme_ideal_of_trivialization X D.divisorialSheaf σ ⟨W, hW⟩ (trivialization hψW) r rfl
  have hrad := Stacks.Models.radical_eq_self_of_isReduced_subscheme
    (AlgebraicGeometry.zeroScheme X D.divisorialSheaf σ)
  have hWrad : (Ideal.span {r}).radical = Ideal.span {r} := by
    have := congrArg (fun J : X.IdealSheafData => J.ideal ⟨W, hW⟩) hrad
    simp only [Scheme.IdealSheafData.radical_ideal] at this
    rwa [hideal] at this
  have hst := radical_span_germ_eq hW r hWrad E.genericPoint hxW
  haveI := E.isDiscreteValuationRing_localRing
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible E.localRing
  set a : E.localRing := (X.presheaf.germ W E.genericPoint hxW).hom r with ha
  have hEW : (E.support ∩ W).Nonempty := ⟨E.genericPoint, genericPoint_mem_support E, hxW⟩
  have hZW := E.componentGenericPoint_mem_of_nonempty hEW
  set φσ := (Divisor.isUnit_sectionToRationalFunctions hσ).unit
  have hcoeff : (D.zeroDivisor σ hσ).coeff E = E.ord φσ + E.ord ψ := by
    rw [Divisor.zeroDivisor_eq, DivisorWithCoeffs.coeff_add, coeff_principalDivisor, hψW E hEW]
  have hval : E.valuation (E.toComponent.hom a) =
      WithZero.exp ((D.zeroDivisor σ hσ).coeff E) := by
    have h1 : E.toComponent.hom a = X.presheaf.germ W _ hZW r :=
      TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf hxW E.specializes_genericPoint r
    rw [h1, germ_trivialization_restrict hψW σ ⟨E.component, hZW⟩]
    have h2 : σ.1 ⟨E.component, trivial⟩ = (φσ : RationalFunctions X) E.component := by
      rw [IsUnit.unit_spec]; rfl
    rw [h2, map_mul, E.valuation_component ψ, E.valuation_component φσ, ← WithZero.exp_add,
      hcoeff, add_comm]
  have ha0 : a ≠ 0 := fun h0 => by
    rw [h0, map_zero, map_zero] at hval
    exact WithZero.exp_ne_zero hval.symm
  obtain ⟨n, u, hau⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
  have hn := le_one_of_radical_span_eq hϖ u n hau hst
  rw [hau, map_mul, map_mul, map_pow, map_pow, E.valuation_toComponent_of_isUnit u.isUnit,
    E.valuation_toComponent_of_irreducible hϖ, one_mul, ← WithZero.exp_nsmul] at hval
  have := WithZero.exp_injective hval
  rw [← this]
  simp only [nsmul_eq_mul, mul_one]
  exact_mod_cast hn

end ZeroScheme

section Bertini

open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections (globalSectionsModule) in
attribute [local instance] globalSectionsModule in
/-- **Bertini for the reducedness of a free system of divisorial sections.** For a general
coefficient vector `c`, every coefficient of the divisor of zeros of `∑ᵢ cᵢ sᵢ` is at most `1`. -/
private theorem exists_dense_open_coeff_zeroDivisor_le_one (k : Type u) [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsIntegral X] [IsNormal X]
    [IsLocallyNoetherian X] [CompactSpace X] (hX : AlgebraicGeometry.IsVariety k f) {D : Divisor X}
    (hD : D.IsCartier) {N : ℕ} (s : Fin (N + 1) → D.divisorialSubmodule ⊤)
    (hfree : ∀ x : X, ∃ (i : Fin (N + 1)) (hi : s i ≠ 0), x ∉ (D.zeroDivisor (s i) hi).supp) :
    ∃ U : (MMP.Threefold.Bridges.coefficientSpace k N).Opens,
      Dense (U : Set (MMP.Threefold.Bridges.coefficientSpace k N)) ∧
      ∀ c : Fin (N + 1) → k, MMP.Threefold.Bridges.coefficientPoint c ∈ U →
        ∀ (hc : ∑ i, scalarsToGlobalSections k f (c i) • s i ≠ 0) (E : MMP.Mori.PrimeDivisor X),
          (D.zeroDivisor _ hc).coeff E ≤ 1 := by
  letI : X.Over (Spec (.of k)) := ⟨f⟩
  haveI := hD.isInvertibleModule_divisorialSheaf
  haveI : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property D.divisorialSheaf :=
    (inferInstance : Stacks.Ample.IsInvertibleModule X D.divisorialSheaf)
  haveI : LocallyOfFiniteType (X ↘ Spec (.of k)) := hX.toLocallyOfFiniteType
  haveI : QuasiCompact (X ↘ Spec (.of k)) := hX.toQuasiCompact
  let s' : Fin (N + 1) → Γ(D.divisorialSheaf, ⊤) := s
  have hsys : ∀ c : Fin (N + 1) → k, MMP.Threefold.Bridges.systemSection s' c =
      (∑ i, scalarsToGlobalSections k f (c i) • s i : D.divisorialSubmodule ⊤) := fun c => by
    rw [MMP.Threefold.Bridges.systemSection_apply]
    rfl
  have hs : ⨆ c : Fin (N + 1) → k, Stacks.NonvanishingOpen.nonvanishingOpen X D.divisorialSheaf
      (MMP.Threefold.Bridges.systemSection s' c) = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨i, hi, hx⟩ := hfree x
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨Pi.single i 1, ?_⟩
    have : MMP.Threefold.Bridges.systemSection s' (Pi.single i (1 : k)) = s' i := by
      simp [MMP.Threefold.Bridges.systemSection_apply, Pi.single_apply]
    rw [this]
    exact mem_nonvanishingOpen_of_notMem_supp D hD (s i) hi x hx
  obtain ⟨⟨U, hU, hUred⟩, -⟩ := MMP.Threefold.Bridges.exists_dense_open_isReduced_zeroScheme s' hs
  refine ⟨U, hU, fun c hc hσ E => ?_⟩
  have hred := hUred c hc
  rw [hsys c] at hred
  exact coeff_zeroDivisor_le_one hD _ hσ hred E

end Bertini

end

section

open MMP.Intersection Opposite TopologicalSpace
open MMP.Intersection Opposite

section PullSec

variable {Z W : Scheme.{u}}

/-- A local equation at `x` is the image of a unit exactly off the support. -/
private theorem notMem_cartierSupport_iff_exists_unit {D : Z.CartierDivisor} {x : Z}
    {f : Z.totalQuotientSheaf.presheaf.stalk x} (hf : IsLocalEquationAt D x f) :
    x ∉ cartierSupport D ↔ ∃ u : (Z.presheaf.stalk x)ˣ, f = stalkToTotalQuotient x u := by
  constructor
  · intro h
    obtain ⟨w, hw⟩ := (isLocalEquationAt_one_of_notMem_cartierSupport h).exists_eq_mul_units hf
    exact ⟨w, by rw [hw, one_mul]⟩
  · rintro ⟨u, rfl⟩
    apply notMem_cartierSupport_of_isLocalEquationAt_one
    have := hf.mul_units u⁻¹
    rwa [← map_mul, Units.mul_inv, map_one] at this

/-- A fixed local equation of `D` at the point `x`. -/
private def refEqAt (x : Z) (D : Z.CartierDivisor) : Z.totalQuotientSheaf.presheaf.stalk x :=
  Classical.choose (exists_isLocalEquationAt D x)

private theorem refEqAt_spec (x : Z) (D : Z.CartierDivisor) :
    IsLocalEquationAt D x (refEqAt x D) :=
  Classical.choose_spec (exists_isLocalEquationAt D x)

open Classical in
/-- The numerator `σ f₀ ∈ 𝒪_{Z,x}` of a global section `σ` of `𝒪_Z(D)` at `x`, for the fixed local
equation `f₀ = refEqAt x D`. -/
private def secNumAt (x : Z) (D : Z.CartierDivisor) (σ : Z.totalQuotientSheaf.obj.obj (op ⊤)) :
    Z.presheaf.stalk x :=
  if h : Z.totalQuotientSheaf.presheaf.germ ⊤ x (Opens.mem_top _) σ * refEqAt x D ∈
      (stalkToTotalQuotient x).range then Classical.choose h else 0

private theorem secNumAt_spec (x : Z) (D : Z.CartierDivisor)
    {σ : Z.totalQuotientSheaf.obj.obj (op ⊤)} (hσ : σ ∈ lineBundleSections D ⊤) :
    stalkToTotalQuotient x (secNumAt x D σ) =
      Z.totalQuotientSheaf.presheaf.germ ⊤ x (Opens.mem_top _) σ * refEqAt x D := by
  have h := hσ x (Opens.mem_top _) _ (refEqAt_spec x D)
  rw [secNumAt, dif_pos h]
  exact Classical.choose_spec h

private theorem secNumAt_add (x : Z) (D : Z.CartierDivisor)
    {σ τ : Z.totalQuotientSheaf.obj.obj (op ⊤)}
    (hσ : σ ∈ lineBundleSections D ⊤) (hτ : τ ∈ lineBundleSections D ⊤) :
    secNumAt x D (σ + τ) = secNumAt x D σ + secNumAt x D τ := by
  apply stalkToTotalQuotient_injective
  rw [secNumAt_spec x D (add_mem hσ hτ), map_add, map_add, secNumAt_spec x D hσ,
    secNumAt_spec x D hτ, add_mul]

private theorem secNumAt_smul (x : Z) (D : Z.CartierDivisor) (r : Γ(Z, ⊤))
    {σ : Z.totalQuotientSheaf.obj.obj (op ⊤)} (hσ : σ ∈ lineBundleSections D ⊤) :
    secNumAt x D (r • σ) = Z.presheaf.germ ⊤ x (Opens.mem_top _) r * secNumAt x D σ := by
  apply stalkToTotalQuotient_injective
  rw [secNumAt_spec x D (Submodule.smul_mem _ r hσ), map_mul, secNumAt_spec x D hσ,
    smul_totalQuotient_def, map_mul, MMP.Intersection.germ_toTotalQuotient (Opens.mem_top _) r,
    mul_assoc]

private theorem secNumAt_sum (x : Z) (D : Z.CartierDivisor) {ι : Type*} (S : Finset ι)
    (r : ι → Γ(Z, ⊤)) {σ : ι → Z.totalQuotientSheaf.obj.obj (op ⊤)}
    (hσ : ∀ i, σ i ∈ lineBundleSections D ⊤) :
    secNumAt x D (∑ i ∈ S, r i • σ i) =
      ∑ i ∈ S, Z.presheaf.germ ⊤ x (Opens.mem_top _) (r i) * secNumAt x D (σ i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    apply stalkToTotalQuotient_injective
    rw [secNumAt_spec x D (zero_mem _)]
    simp
  | insert i S hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      secNumAt_add x D (Submodule.smul_mem _ _ (hσ i))
        (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hσ j)),
      secNumAt_smul x D _ (hσ i), ih]

/-- The local equation `f₀ σ` of `D + div σ` at `x`. -/
private theorem isLocalEquationAt_secNumAt (x : Z) (D : Z.CartierDivisor)
    (σ : (Z.totalQuotientSheaf.obj.obj (op ⊤))ˣ)
    (hσ : (σ : Z.totalQuotientSheaf.obj.obj (op ⊤)) ∈ lineBundleSections D ⊤) :
    IsLocalEquationAt (D + principalDivisor σ) x (stalkToTotalQuotient x (secNumAt x D σ)) := by
  rw [secNumAt_spec x D hσ, mul_comm]
  exact (refEqAt_spec x D).add ⟨⊤, Opens.mem_top _, σ, isLocalEquationOn_principalDivisor σ, rfl⟩

/-- **Nonvanishing of a section at a point.** A section `σ` of `𝒪_Z(D)` does not vanish at `x`,
i.e. `x` lies off its divisor `D + div σ`, exactly when its numerator at `x` is a unit. -/
private theorem notMem_cartierSupport_iff_isUnit_secNumAt (x : Z) (D : Z.CartierDivisor)
    (σ : (Z.totalQuotientSheaf.obj.obj (op ⊤))ˣ)
    (hσ : (σ : Z.totalQuotientSheaf.obj.obj (op ⊤)) ∈ lineBundleSections D ⊤) :
    x ∉ cartierSupport (D + principalDivisor σ) ↔ IsUnit (secNumAt x D σ) := by
  rw [notMem_cartierSupport_iff_exists_unit (isLocalEquationAt_secNumAt x D σ hσ)]
  constructor
  · rintro ⟨u, hu⟩
    rw [stalkToTotalQuotient_injective _ hu]
    exact u.isUnit
  · rintro ⟨u, hu⟩
    exact ⟨u, by rw [hu]⟩

variable [IsIntegral W] (g : W ⟶ Z)

/-- A fixed local equation of `D` at `g(η_W)`. -/
private abbrev refEq (D : Z.CartierDivisor) :
    Z.totalQuotientSheaf.presheaf.stalk (g (genericPoint W)) :=
  refEqAt (g (genericPoint W)) D

private theorem refEq_spec (D : Z.CartierDivisor) :
    IsLocalEquationAt D (g (genericPoint W)) (refEq g D) :=
  refEqAt_spec _ D

/-- The numerator `σ · f₀ ∈ 𝒪_{Z, g(η_W)}` of a global section `σ` of `𝒪_Z(D)`. -/
private abbrev secNum (D : Z.CartierDivisor) (σ : Z.totalQuotientSheaf.obj.obj (op ⊤)) :
    Z.presheaf.stalk (g (genericPoint W)) :=
  secNumAt (g (genericPoint W)) D σ

private theorem secNum_spec (D : Z.CartierDivisor) {σ : Z.totalQuotientSheaf.obj.obj (op ⊤)}
    (hσ : σ ∈ lineBundleSections D ⊤) :
    stalkToTotalQuotient _ (secNum g D σ) =
      Z.totalQuotientSheaf.presheaf.germ ⊤ _ (Opens.mem_top _) σ * refEq g D :=
  secNumAt_spec _ D hσ

/-- The pull-back `g^*(σ/f₀) ∈ K(W)` of a global section `σ` of `𝒪_Z(D)`. -/
private def pullSec (D : Z.CartierDivisor)
    (σ : Z.totalQuotientSheaf.obj.obj (op ⊤)) : W.functionField :=
  (g.stalkMap (genericPoint W)).hom (secNum g D σ)

/-- `g^*a ≠ 0` in `K(W)` exactly when `a` is a unit at `g(η_W)`. -/
private theorem stalkMap_genericPoint_ne_zero_iff
    (a : Z.presheaf.stalk (g (genericPoint W))) :
    (g.stalkMap (genericPoint W)).hom a ≠ 0 ↔ IsUnit a :=
  ⟨fun h => (isUnit_map_iff (g.stalkMap (genericPoint W)).hom a).mp
      ((isUnit_iff_ne_zero (G₀ := W.functionField)).mpr h),
    fun h => (h.map (g.stalkMap (genericPoint W)).hom).ne_zero⟩

end PullSec

end

section

open MMP.Intersection Opposite TopologicalSpace

section Orders

variable {Z W : Scheme.{u}} [IsIntegral W] (g : W ⟶ Z)

/-- **Nonvanishing of a pulled-back section.** `g^*σ ≠ 0` exactly when `g(η_W)` lies off the
divisor `D + div σ` of `σ`. -/
private theorem pullSec_ne_zero_iff (D : Z.CartierDivisor)
    (σ : (Z.totalQuotientSheaf.obj.obj (op ⊤))ˣ)
    (hσ : (σ : Z.totalQuotientSheaf.obj.obj (op ⊤)) ∈ lineBundleSections D ⊤) :
    pullSec g D σ ≠ 0 ↔ g (genericPoint W) ∉ cartierSupport (D + principalDivisor σ) := by
  rw [notMem_cartierSupport_iff_isUnit_secNumAt _ D σ hσ, pullSec,
    stalkMap_genericPoint_ne_zero_iff]

/-- The generization `g(η_W)` of the image of any point of `W`. -/
private theorem specializes_map_genericPoint (x : W) : g (genericPoint W) ⤳ g x :=
  ((genericPoint_spec W).specializes (Set.mem_univ x)).map g.continuous

/-- The germ of a section at a point `x` of `W`, read in `K(W)`, is its germ at `η_W`. -/
private theorem algebraMap_germ_eq_germ {V : W.Opens} {x : W} (hx : x ∈ V) (s : Γ(W, V)) :
    algebraMap (W.presheaf.stalk x) W.functionField (W.presheaf.germ V x hx s) =
      W.presheaf.germ V (genericPoint W)
        (((genericPoint_spec W).specializes (Set.mem_univ x)).mem_open V.isOpen hx) s := by
  change W.presheaf.stalkSpecializes _ _ = _
  exact TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _

variable [IsLocallyNoetherian W]

/-- **Orders of pulled-back divisors of sections.** For a prime divisor `P` of `W` there is an
integer `c`, depending on `D` only, such that the order along `P` of the pull-back of the divisor
`D + div σ` of any section `σ` of `𝒪_Z(D)` is `ord_P(g^*σ) + c`. -/
private theorem exists_primeDivisorOrder_eq (D : Z.CartierDivisor) (P : MMP.Mori.PrimeDivisor W) :
    ∃ c : ℤ, ∀ (σ : (Z.totalQuotientSheaf.obj.obj (op ⊤))ˣ),
      (σ : Z.totalQuotientSheaf.obj.obj (op ⊤)) ∈ lineBundleSections D ⊤ →
      ∀ HW : W.CartierDivisor, IsPullback g (D + principalDivisor σ) HW →
        primeDivisorOrder P HW = W.ord (pullSec g D σ) P.genericPoint + c := by
  obtain ⟨U, hzU, gz, hgz⟩ := MMP.Intersection.exists_isLocalEquationOn D (g P.genericPoint)
  have hz0U : g (genericPoint W) ∈ U :=
    (specializes_map_genericPoint g P.genericPoint).mem_open U.isOpen hzU
  have hloc0 : IsLocalEquationAt D (g (genericPoint W))
      (Z.totalQuotientSheaf.presheaf.germ U _ hz0U (gz : _)) := ⟨U, hz0U, gz, hgz, rfl⟩
  obtain ⟨w, hw⟩ := hloc0.exists_eq_mul_units (refEq_spec g D)
  have hw0 : (g.stalkMap (genericPoint W)).hom (w : Z.presheaf.stalk _) ≠ 0 :=
    (stalkMap_genericPoint_ne_zero_iff g _).mpr w.isUnit
  refine ⟨-W.ord ((g.stalkMap (genericPoint W)).hom (w : Z.presheaf.stalk _)) P.genericPoint,
    fun σ hσ HW hHW => ?_⟩
  set σU := Z.totalQuotientSheaf.obj.map (homOfLE le_top : U ⟶ ⊤).op
    (σ : Z.totalQuotientSheaf.obj.obj (op ⊤)) with hσU
  obtain ⟨r, hr⟩ := (mem_lineBundleSections_iff_of_isLocalEquationOn' hgz σU).1
    (res_mem D le_top hσ)
  have hrσ : toTotalQuotient U r = (gz : _) * σU := by
    rw [← hr, mul_comm, mul_assoc, Units.inv_mul, mul_one]
  have hu : IsUnit (toTotalQuotient U r) := by
    rw [hrσ]
    exact gz.isUnit.mul (σ.isUnit.map _)
  have hloc : IsLocalEquationOn (D + principalDivisor σ) U hu.unit := by
    have := hgz.mul (isLocalEquationOn_principalDivisor_res σ U)
    convert this using 1
    ext
    rw [IsUnit.unit_spec, hrσ]
    rfl
  have hne := germ_ne_zero_of_isPullback g hHW hu hloc hzU
  rw [primeDivisorOrder_eq_ord_of_isPullback g hHW hu hloc P hzU hne]
  -- the germ of `g^* r` at `η_W` is `g^*(secNum σ) · (g^* w)⁻¹`
  have key : secNum g D σ = Z.presheaf.germ U _ hz0U r * (w : Z.presheaf.stalk _) := by
    apply stalkToTotalQuotient_injective
    rw [secNum_spec g D hσ, hw, map_mul, ← MMP.Intersection.germ_toTotalQuotient hz0U r, hrσ,
      map_mul]
    rw [show Z.totalQuotientSheaf.presheaf.germ U _ hz0U σU =
        Z.totalQuotientSheaf.presheaf.germ ⊤ _ (Opens.mem_top _) (σ : _) from
      TopCat.Presheaf.germ_res_apply _ _ _ _ _]
    ring
  have h1 : W.presheaf.germ (g ⁻¹ᵁ U) (genericPoint W) _ (g.app U r) =
      (g.stalkMap (genericPoint W)).hom (Z.presheaf.germ U _ hz0U r) :=
    (Scheme.Hom.germ_stalkMap_apply g U _ hz0U r).symm
  have hpull : pullSec g D σ = (g.stalkMap (genericPoint W)).hom (Z.presheaf.germ U _ hz0U r) *
      (g.stalkMap (genericPoint W)).hom (w : Z.presheaf.stalk _) := by
    rw [pullSec, key, map_mul]
  have h2 : algebraMap (W.presheaf.stalk P.genericPoint) W.functionField
      (W.presheaf.germ (g ⁻¹ᵁ U) P.genericPoint hzU (g.app U r)) =
      (g.stalkMap (genericPoint W)).hom (Z.presheaf.germ U _ hz0U r) := by
    rw [← h1]
    exact algebraMap_germ_eq_germ _ _
  have hgr : (g.stalkMap (genericPoint W)).hom (Z.presheaf.germ U _ hz0U r) ≠ 0 := by
    rw [← h2]
    exact fun h0 => hne ((IsFractionRing.to_map_eq_zero_iff).mp h0)
  rw [h2, hpull, Scheme.ord_mul hgr hw0]
  ring

end Orders

end

section

open MMP.Intersection Opposite TopologicalSpace

section SectionArith

variable {Z : Scheme.{u}}

/-- Products of sections are sections of the sum. -/
private theorem mul_mem_lineBundleSections_add {D D' : Z.CartierDivisor} {V : Z.Opens}
    {σ τ : Z.totalQuotientSheaf.obj.obj (op V)} (hσ : σ ∈ lineBundleSections D V)
    (hτ : τ ∈ lineBundleSections D' V) : σ * τ ∈ lineBundleSections (D + D') V := by
  intro x hx e he
  obtain ⟨f, hf⟩ := exists_isLocalEquationAt D x
  obtain ⟨f', hf'⟩ := exists_isLocalEquationAt D' x
  obtain ⟨w, rfl⟩ := (hf.add hf').exists_eq_mul_units he
  obtain ⟨a, ha⟩ := hσ x hx f hf
  obtain ⟨b, hb⟩ := hτ x hx f' hf'
  refine ⟨a * b * w, ?_⟩
  rw [map_mul, map_mul, ha, hb, map_mul]
  ring

private theorem one_mem_lineBundleSections_zero (V : Z.Opens) :
    (1 : Z.totalQuotientSheaf.obj.obj (op V)) ∈ lineBundleSections (0 : Z.CartierDivisor) V := by
  intro x hx e he
  obtain ⟨w, rfl⟩ := (isLocalEquationAt_one_of_notMem_cartierSupport
    (show x ∉ cartierSupport (0 : Z.CartierDivisor) by
      simp [cartierSupport])).exists_eq_mul_units he
  exact ⟨w, by rw [map_one, one_mul, one_mul]⟩

private theorem pow_mem_lineBundleSections {D : Z.CartierDivisor} {V : Z.Opens}
    {σ : Z.totalQuotientSheaf.obj.obj (op V)} (hσ : σ ∈ lineBundleSections D V) :
    ∀ m : ℕ, σ ^ m ∈ lineBundleSections (m • D) V
  | 0 => by simpa using one_mem_lineBundleSections_zero V
  | m + 1 => by
    rw [pow_succ, succ_nsmul]
    exact mul_mem_lineBundleSections_add (pow_mem_lineBundleSections hσ m) hσ

private theorem nsmul_add_principalDivisor_pow (D : Z.CartierDivisor)
    (σ : (Z.totalQuotientSheaf.obj.obj (op ⊤))ˣ) :
    ∀ m : ℕ, m • D + principalDivisor (σ ^ m) = m • (D + principalDivisor σ)
  | 0 => by
    simp only [zero_smul, pow_zero, zero_add]
    exact (principalHom Z).map_zero
  | m + 1 => by
    rw [pow_succ, MMP.Intersection.principalDivisor_mul, succ_nsmul, succ_nsmul,
      ← nsmul_add_principalDivisor_pow D σ m]
    abel

/-- Off the support of `H`, a point is off the support of every multiple of `H`. -/
private theorem notMem_cartierSupport_nsmul {H : Z.CartierDivisor} {x : Z}
    (h : x ∉ cartierSupport H) : ∀ m : ℕ, x ∉ cartierSupport (m • H)
  | 0 => by simp [cartierSupport]
  | m + 1 => by
    rw [succ_nsmul]
    exact notMem_cartierSupport_add Z _ _ x (notMem_cartierSupport_nsmul h m) h

/-- If a unit `u` of `Γ(Z, 𝓜_Z)` is a section of `𝒪_Z(D)`, then `D + div u` is effective. -/
private theorem isEffective_add_principalDivisor {D : Z.CartierDivisor}
    (u : (Z.totalQuotientSheaf.obj.obj (op ⊤))ˣ)
    (hu : (u : Z.totalQuotientSheaf.obj.obj (op ⊤)) ∈ lineBundleSections D ⊤) :
    IsEffective (D + principalDivisor u) := by
  intro x
  obtain ⟨U, hxU, g, hg⟩ := MMP.Intersection.exists_isLocalEquationOn D x
  have hE := hg.mul (isLocalEquationOn_principalDivisor_res u U)
  obtain ⟨r, hr⟩ := (mem_lineBundleSections_iff_of_isLocalEquationOn' hg _).1 (res_mem D le_top hu)
  have hrσ : toTotalQuotient U r =
      (g : Z.totalQuotientSheaf.obj.obj (op U)) * Z.totalQuotientSheaf.obj.map
        (homOfLE (le_top : U ≤ ⊤)).op (u : Z.totalQuotientSheaf.obj.obj (op ⊤)) := by
    rw [← hr, mul_comm, mul_assoc, Units.inv_mul, mul_one]
  have hunit : IsUnit (toTotalQuotient U r) := by
    rw [hrσ]
    exact g.isUnit.mul (u.isUnit.map _)
  refine ⟨U, hxU, r, hunit, ?_⟩
  have : hunit.unit = g * MMP.Intersection.resUnit (homOfLE le_top) u :=
    Units.ext (by rw [IsUnit.unit_spec, hrσ]; rfl)
  rwa [this]

end SectionArith

section Positivity

variable {Z X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] (g : X ⟶ Z)

/-- The pull-back of an effective divisor has non-negative order along every prime divisor, and
positive order along those whose generic point maps into its support. -/
private theorem primeDivisorOrder_nonneg_and_pos_of_isPullback {H : Z.CartierDivisor}
    (hH : IsEffective H) {HX : X.CartierDivisor} (hHX : IsPullback g H HX)
    (P : MMP.Mori.PrimeDivisor X) :
    0 ≤ primeDivisorOrder P HX ∧
      (g P.genericPoint ∈ cartierSupport H → 1 ≤ primeDivisorOrder P HX) := by
  obtain ⟨W, hW, h, hu, hloc⟩ := hH (g P.genericPoint)
  have hne := germ_ne_zero_of_isPullback g hHX hu hloc hW
  rw [primeDivisorOrder_eq_ord_toNat g hHX hu hloc P hW (mem_nonZeroDivisors_of_ne_zero hne)]
  refine ⟨by positivity, fun hmem => ?_⟩
  set a := X.presheaf.germ (g ⁻¹ᵁ W) P.genericPoint hW (g.app W h)
  have hgh : ¬ IsUnit (Z.presheaf.germ W _ hW h) := fun hu' =>
    ((notMem_cartierSupport_iff_isUnit_germ hu hloc hW).mpr hu') hmem
  have hnu : ¬ IsUnit a := by
    intro ha
    rw [show a = (g.stalkMap P.genericPoint).hom (Z.presheaf.germ W _ hW h) from
      (Scheme.Hom.germ_stalkMap_apply g W _ hW h).symm] at ha
    exact hgh ((isUnit_map_iff (g.stalkMap P.genericPoint).hom _).mp ha)
  have hlen : Ring.ord _ a ≠ 0 := by
    intro h0
    rw [Ring.ord, Module.length_eq_zero_iff, Ideal.Quotient.subsingleton_iff,
      Ideal.span_singleton_eq_top] at h0
    exact hnu h0
  have : Ring.KrullDimLE 1 (X.presheaf.stalk P.genericPoint) :=
    krullDimLE_of_coheight_le P.coheight_genericPoint.le
  have htop := Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hne)
  have : 1 ≤ (Ring.ord _ a).toNat := by
    rcases ENat.ne_top_iff_exists.mp htop with ⟨m, hm⟩
    rw [← hm] at hlen ⊢
    simp only [ENat.toNat_coe]
    exact Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast hlen)
  exact_mod_cast this

end Positivity

end

section

open MMP.Intersection Opposite TopologicalSpace

/-- `A` has a basis of nonvanishing loci of sections of its positive multiples: every
neighbourhood `V` of a point `z` contains the locus `Z_σ ∋ z` where a section `σ` of some
`𝒪_Z(nA)`, `n > 0`, does not vanish. -/
private def IsNvBasis {Z : Scheme.{u}} (A : Z.CartierDivisor) : Prop :=
  ∀ (z : Z) (V : Z.Opens), z ∈ V → ∃ n : ℕ, 0 < n ∧
    ∃ σ : (Z.totalQuotientSheaf.obj.obj (op ⊤))ˣ,
      (σ : Z.totalQuotientSheaf.obj.obj (op ⊤)) ∈ lineBundleSections (n • A) ⊤ ∧
      z ∉ cartierSupport (n • A + MMP.Intersection.principalDivisor σ) ∧
      ∀ y : Z, y ∉ cartierSupport (n • A + MMP.Intersection.principalDivisor σ) → y ∈ V

/-- The only associated point of an integral locally Noetherian scheme is its generic point. -/
private theorem eq_genericPoint_of_mem_schemeAssociatedPoints {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] {ξ : X} (h : ξ ∈ Stacks.Divisors.schemeAssociatedPoints X) :
    ξ = genericPoint X := by
  have h1 : ξ ∈ Stacks.Divisors.schemeWeaklyAssociatedPoints X := by
    rwa [Stacks.Divisors.schemeAssociatedPoints,
      associatedPoints_eq_weaklyAssociatedPoints X (SheafOfModules.unit X.ringCatSheaf)] at h
  rw [weaklyAssociatedPointsOfScheme_eq_genericPoints] at h1
  have h2 : closure ({ξ} : Set X) ∈ ({Set.univ} : Set (Set X)) := by
    rwa [← irreducibleComponents_eq_singleton]
  exact (show IsGenericPoint ξ Set.univ from h2).eq (genericPoint_spec X)

private theorem principalDivisor_one' {Z : Scheme.{u}} :
    MMP.Intersection.principalDivisor (1 : (Z.totalQuotientSheaf.obj.obj (op ⊤))ˣ) = 0 :=
  (principalHom Z).map_zero

/-- A point specializing into the complement of a closed support stays in it. -/
private theorem notMem_cartierSupport_of_specializes {Z : Scheme.{u}} {H : Z.CartierDivisor}
    {z z' : Z} (h : z ⤳ z') (hz' : z' ∉ cartierSupport H) : z ∉ cartierSupport H :=
  fun hz => hz' (h.mem_closed (isClosed_cartierSupport H) hz)

variable {k : Type u} [Field k]

/-- **Serre generation, on a normal variety over the base.** Let `g : X ⟶ Z` be a morphism from a
normal integral Noetherian scheme, `A` a Cartier divisor on `Z` with a basis of nonvanishing
loci of sections of its multiples, and `E` a Cartier divisor on `X` which is `g`-free. There is
`M > 0` such that `aE + g^*H` is free over the base for every effective `H ∼ (atM)A`, `a, t > 0`:
near a point `x`, a section `ψ` of `𝒪(E)` over `g⁻¹(U)` generating it at `x` and a section `σ`
of `𝒪_Z(nA)` with `g(x) ∈ Z_σ ⊆ U` give the global section `ψ^a (g^*σ)^e` of `aE + g^*H`, the
power `e` absorbing the poles of `ψ` off `g⁻¹(Z_σ)`. -/
private theorem exists_isRelativelyFreeCartier_twist_of_isNvBasis
    {X Z : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsLocallyNoetherian Z] (sX : X ⟶ Spec (.of k)) (g : X ⟶ Z) {A : Z.CartierDivisor}
    (hAb : IsNvBasis A) {E : X.CartierDivisor} (hE : IsRelativelyFreeCartier g E) :
    ∃ M : ℕ, 0 < M ∧ ∀ (a t : ℕ) (H : Z.CartierDivisor) (HN : X.CartierDivisor), 0 < a → 0 < t →
      IsEffective H → LinearlyEquivalent H ((a * t * M) • A) → IsPullback g H HN →
      IsRelativelyFreeCartier sX (a • E + HN) := by
  classical
  haveI : IsNoetherian X := ⟨⟩
  obtain ⟨B, hEB⟩ := MMP.Intersection.exists_isWeilDivisorOfCartier E
  choose U' hU' ψ hψ1 hψ2 using fun x =>
    exists_isLocalEquation_of_isRelativelyFreeCartier g hEB hE x
  choose n hn σ hσ hxσ hσV using fun x => hAb (g x) (U' x) (hU' x)
  set G : X → Z.CartierDivisor := fun x => n x • A + MMP.Intersection.principalDivisor (σ x)
    with hGdef
  set C : X → Divisor X := fun x => B + MMP.Mori.principalDivisor (ψ x) with hCdef
  have hCcoeff : ∀ x P, (C x).coeff P = B.coeff P + P.ord (ψ x) := fun x P => by
    rw [hCdef, DivisorWithCoeffs.coeff_add, coeff_principalDivisor]
  let O : X → Set X := fun x =>
    g ⁻¹' (cartierSupport (G x))ᶜ ∩ ((C x).supp : Set X)ᶜ
  have hOopen : ∀ x, IsOpen (O x) := fun x =>
    ((isClosed_cartierSupport _).isOpen_compl.preimage g.continuous).inter
      (DivisorWithCoeffs.isClosed_supp _).isOpen_compl
  have hcoeff0 : ∀ x y, y ∈ O x → ∀ P : MMP.Mori.PrimeDivisor X, y ∈ P.support →
      (C x).coeff P = 0 := by
    intro x y hy P hyP
    by_contra hne
    exact hy.2 (DivisorWithCoeffs.mem_supp_iff.mpr ⟨P, hne, hyP⟩)
  have hxO : ∀ x, x ∈ O x := fun x => ⟨hxσ x, fun hm => by
    obtain ⟨P, hP, hxP⟩ := DivisorWithCoeffs.mem_supp_iff.mp hm
    exact hP (by rw [hCcoeff]; exact hψ2 x P hxP)⟩
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover O hOopen
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hxO x⟩)
  set e : X → ℕ := fun x => ∑ P ∈ (C x).support, ((C x).coeff P).natAbs with hedef
  have he : ∀ x P, -(e x : ℤ) ≤ (C x).coeff P := by
    intro x P
    by_cases hP : P ∈ (C x).support
    · have h1 : ((C x).coeff P).natAbs ≤ e x :=
        Finset.single_le_sum (f := fun P => ((C x).coeff P).natAbs) (fun _ _ => Nat.zero_le _) hP
      have h2 : -(((C x).coeff P).natAbs : ℤ) ≤ (C x).coeff P := by
        have := Int.natAbs_neg ((C x).coeff P); omega
      omega
    · rw [show (C x).coeff P = 0 from Finsupp.notMem_support_iff.mp hP]
      omega
  set M : ℕ := ∏ x ∈ S, (n x * (e x + 1)) with hMdef
  have hM : 0 < M := Finset.prod_pos fun x _ => Nat.mul_pos (hn x) (Nat.succ_pos _)
  refine ⟨M, hM, fun a t H HN ha ht hH hlin hHN => ?_⟩
  obtain ⟨u, hu⟩ := mem_principalSubgroup_iff.mp hlin
  obtain ⟨W, hW⟩ := MMP.Intersection.exists_isWeilDivisorOfCartier HN
  have hEW : IsWeilDivisorOfCartier (a • E + HN) (a • B + W) := fun Q => by
    have h := isOrderAlong_primeDivisorOrder (a • E + HN) Q
    have e1 : primeDivisorOrder Q (a • E + HN) = (a • B + W).coeff Q := by
      rw [map_add, map_nsmul, (hEB Q).primeDivisorOrder_eq, (hW Q).primeDivisorOrder_eq]
      simp [DivisorWithCoeffs.coeff_apply, nsmul_eq_mul]
    rwa [e1] at h
  suffices hfree : IsRelativelyFreeDivisor sX (a • B + W) by
    obtain ⟨φe⟩ := hEW.nonempty_sheaf_iso_divisorialSheaf
    exact epi_counit_of_iso sX φe hfree
  have hHη : g (genericPoint X) ∉ cartierSupport H :=
    hHN.1 _ (genericPoint_mem_schemeAssociatedPoints X)
  refine MMP.Fourfold.isRelativelyFreeDivisor_of_forall_exists sX fun y => ?_
  obtain ⟨x, hxS, hyx⟩ := Set.mem_iUnion₂.mp (hS (Set.mem_univ y))
  have hnM : n x * (e x + 1) ∣ M := Finset.dvd_prod_of_mem _ hxS
  obtain ⟨q, hq⟩ := hnM
  have hq0 : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h0 | h0
    · rw [h0, mul_zero] at hq; omega
    · exact h0
  set El : ℕ := a * (t * ((e x + 1) * q)) with hEl
  have hc : a * t * M = El * n x := by rw [hEl, hq]; ring
  -- the section `s = σ^El` of `𝒪_Z((atM) A)` and `s' = s / u` of `𝒪_Z(H)`
  have hs : ((σ x ^ El : _ˣ) : Z.totalQuotientSheaf.obj.obj (op ⊤)) ∈
      lineBundleSections ((a * t * M) • A) ⊤ := by
    have := pow_mem_lineBundleSections (hσ x) El
    rw [smul_smul] at this
    have hEq : (a * t * M) • A = (El * n x) • A := by rw [hc]
    rwa [Units.val_pow_eq_pow_val, hEq]
  set s' : (Z.totalQuotientSheaf.obj.obj (op ⊤))ˣ := u⁻¹ * σ x ^ El with hs'def
  have hHu : (a * t * M) • A + MMP.Intersection.principalDivisor u = H := by
    rw [hu]; abel
  have hs' : (s' : Z.totalQuotientSheaf.obj.obj (op ⊤)) ∈ lineBundleSections H ⊤ := by
    have := mul_mem_lineBundleSections_add_principalDivisor u hs
    rw [hHu, show (homOfLE le_top : (⊤ : Z.Opens) ⟶ ⊤) = homOfLE (le_refl ⊤) from rfl,
      totalQuotient_map_id] at this
    rwa [hs'def, Units.val_mul]
  have hHs' : H + MMP.Intersection.principalDivisor s' = El • G x := by
    rw [hs'def, MMP.Intersection.principalDivisor_mul, MMP.Intersection.principalDivisor_inv,
      ← hHu, hGdef]
    dsimp only
    rw [← nsmul_add_principalDivisor_pow, ← mul_nsmul', ← hc]
    abel
  -- the pull-back of `G x`
  have hGeff : IsEffective (G x) := isEffective_add_principalDivisor (σ x) (hσ x)
  have hgy : g y ∉ cartierSupport (G x) := hyx.1
  have hGη : g (genericPoint X) ∉ cartierSupport (G x) :=
    notMem_cartierSupport_of_specializes (specializes_map_genericPoint g y) hgy
  obtain ⟨GX, hGX⟩ := exists_isPullback (f := g) (D := G x) fun ξ hξ => by
    rwa [eq_genericPoint_of_mem_schemeAssociatedPoints hξ]
  have hpE : IsPullback g (H + MMP.Intersection.principalDivisor s') (El • GX) := by
    rw [hHs']; exact isPullback_nsmul hGX El
  have hpH : IsPullback g (H + MMP.Intersection.principalDivisor 1) HN := by
    rwa [principalDivisor_one', add_zero]
  have h1 : ((1 : (Z.totalQuotientSheaf.obj.obj (op ⊤))ˣ) : Z.totalQuotientSheaf.obj.obj (op ⊤)) ∈
      lineBundleSections H ⊤ := by
    rw [Units.val_one]; exact one_mem_lineBundleSections hH ⊤
  have hne1 : pullSec g H ((1 : (Z.totalQuotientSheaf.obj.obj (op ⊤))ˣ) :
      Z.totalQuotientSheaf.obj.obj (op ⊤)) ≠ 0 := by
    rwa [pullSec_ne_zero_iff g H 1 h1, principalDivisor_one', add_zero]
  have hnes : pullSec g H (s' : Z.totalQuotientSheaf.obj.obj (op ⊤)) ≠ 0 := by
    rw [pullSec_ne_zero_iff g H s' hs', hHs']; exact notMem_cartierSupport_nsmul hGη El
  set φ : X.functionField := pullSec g H (s' : Z.totalQuotientSheaf.obj.obj (op ⊤)) *
    (pullSec g H ((1 : (Z.totalQuotientSheaf.obj.obj (op ⊤))ˣ) :
      Z.totalQuotientSheaf.obj.obj (op ⊤)))⁻¹ with hφdef
  have hφ : φ ≠ 0 := mul_ne_zero hnes (inv_ne_zero hne1)
  let Φ₀ : (RationalFunctions X)ˣ := unitOfFunction hφ
  have hkey : ∀ P : MMP.Mori.PrimeDivisor X, (a • B + W).coeff P + P.ord (ψ x ^ a * Φ₀) =
      a * (C x).coeff P + El * primeDivisorOrder P GX := by
    intro P
    obtain ⟨cP, hcP⟩ := exists_primeDivisorOrder_eq g H P
    have e1 := hcP s' hs' _ hpE
    have e2 := hcP 1 h1 _ hpH
    have e3 : P.ord Φ₀ = X.ord φ P.genericPoint := ord_unitOfFunction P hφ
    rw [map_nsmul, nsmul_eq_mul] at e1
    rw [Units.val_one] at e2
    rw [PrimeDivisor.ord_mul, PrimeDivisor.ord_pow, e3, hφdef,
      Scheme.ord_mul hnes (inv_ne_zero hne1),
      scheme_ord_inv hne1, hCcoeff, DivisorWithCoeffs.coeff_add, ← (hW P).primeDivisorOrder_eq]
    simp only [DivisorWithCoeffs.coeff_apply, Finsupp.smul_apply, nsmul_eq_mul, smul_eq_mul]
    push_cast at e1 ⊢
    linarith
  refine ⟨⊤, trivial, ψ x ^ a * Φ₀, fun P _ => ?_, fun P hyP => ?_⟩
  · rw [hkey]
    obtain ⟨hG0, hG1⟩ := primeDivisorOrder_nonneg_and_pos_of_isPullback g hGeff hGX P
    by_cases hPU : (P.support ∩ g ⁻¹ᵁ U' x).Nonempty
    · have := hψ1 x P hPU
      rw [← hCcoeff] at this
      positivity
    · have hgP : g P.genericPoint ∈ cartierSupport (G x) := by
        by_contra hgP
        exact hPU ⟨P.genericPoint, genericPoint_mem_support P, hσV x _ hgP⟩
      have hG1' := hG1 hgP
      have hCe := he x P
      have hEl : a * (e x + 1) ≤ El := by
        rw [hEl]
        apply Nat.mul_le_mul_left
        calc e x + 1 ≤ (e x + 1) * q := Nat.le_mul_of_pos_right _ hq0
          _ ≤ t * ((e x + 1) * q) := Nat.le_mul_of_pos_left _ ht
      have : (a : ℤ) * (e x + 1) ≤ El := by exact_mod_cast hEl
      nlinarith
  · rw [hkey, hcoeff0 x y hyx P hyP, primeDivisorOrder_eq_zero_of_isPullback g hGX P ?_]
    · simp
    · refine notMem_cartierSupport_of_specializes ?_ hgy
      have : P.genericPoint ⤳ y := by
        rwa [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact this.map g.continuous

end

section

open MMP.Intersection Opposite TopologicalSpace

/-- On an integral scheme a non-zero global section of `𝓜_Z` is a unit: `Γ(Z, 𝓜_Z) = K(Z)`. -/
private theorem isUnit_of_ne_zero_totalQuotient {Z : Scheme.{u}} [IsIntegral Z]
    {σ : Z.totalQuotientSheaf.obj.obj (op ⊤)} (hσ : σ ≠ 0) : IsUnit σ := by
  obtain ⟨f, rfl⟩ :=
    (MMP.CartierDivisorSheaf.ofFunctionField_bijective ⊤ ⟨genericPoint Z, trivial⟩).2 σ
  have hf : f ≠ 0 := fun h => hσ (by rw [h, map_zero])
  exact (isUnit_iff_ne_zero.mpr hf).map _

/-- **Ampleness gives a basis of nonvanishing loci.** If `𝒪_Z(A)` is ample on the integral scheme
`Z`, the loci `Z_σ = Z ∖ Supp(nA + div σ)` of sections `σ` of `𝒪_Z(nA)`, `n > 0`, form a basis
of the topology of `Z` (Stacks 01Q3, clause (3)). -/
private theorem isNvBasis_of_isAmple {Z : Scheme.{u}} [IsIntegral Z] (A : Z.CartierDivisor)
    (hA : Stacks.Ample.IsAmple Z (MMP.CartierDivisor.sheaf A)) : IsNvBasis A := by
  intro z V hzV
  obtain ⟨n, hn, s, hzs, hsV⟩ :=
    Stacks.AmpleCharacterization.isBasisNonvanishing_of_isAmple (MMP.CartierDivisor.sheaf A) hA z V
        hzV
  obtain ⟨e1⟩ := MMP.Resolution.Bridges.lineBundle_nsmul_iso_tensorPow A n
  obtain ⟨e2⟩ := MMP.Resolution.Bridges.nonempty_tensorPow_iso_tensorPowModule Z
      (MMP.CartierDivisor.sheaf A) n
  set e := e1 ≪≫ e2
  set s' : Γ(MMP.CartierDivisor.sheaf (n • A), ⊤) := (Scheme.Modules.Hom.app e.inv ⊤).hom s with hs'
  have hnv : Stacks.Ample.nonvanishingLocus (MMP.CartierDivisor.sheaf (n • A)) s' =
      (Stacks.AmpleTheory.powNonvanishingOpen Z (MMP.CartierDivisor.sheaf A) n s : Set Z) := by
    rw [Stacks.AmpleTheory.coe_powNonvanishingOpen, ← Stacks.Ample.nonvanishingLocus_congr e s']
    congr 1
    rw [hs']
    change (Scheme.Modules.Hom.app (e.inv ≫ e.hom) ⊤).hom s = s
    rw [e.inv_hom_id]
    rfl
  set σ := MMP.CartierDivisorSheaf.sectionVal s' with hσdef
  have hσmem : σ ∈ lineBundleSections (n • A) ⊤ :=
      (MMP.CartierDivisor.sectionVal_mem_lineBundleSections s')
  have hs'0 : s' ≠ 0 := by
    intro h0
    have hz : z ∈ Stacks.Ample.nonvanishingLocus (MMP.CartierDivisor.sheaf (n • A)) s' := by
      rwa [hnv]
    rw [h0, Stacks.Ample.mem_nonvanishingLocus_iff] at hz
    exact hz (by simp)
  have hσ0 : σ ≠ 0 := fun h => hs'0 (MMP.CartierDivisorSheaf.sectionVal_injective (h.trans rfl))
  set σu := (isUnit_of_ne_zero_totalQuotient hσ0).unit
  have hσu : (σu : Z.totalQuotientSheaf.obj.obj (op ⊤)) = σ := IsUnit.unit_spec _
  have heff : IsEffective (n • A + MMP.Intersection.principalDivisor σu) :=
    isEffective_add_principalDivisor σu (hσu ▸ hσmem)
  have hcan : (Scheme.Modules.Hom.app (MMP.CartierDivisor.sheafAddPrincipalIso (n • A) σu).hom
      ⊤).hom s' =
      MMP.CartierDivisor.canonicalSection _ heff := by
    apply MMP.CartierDivisorSheaf.sectionVal_injective
    rw [MMP.CartierDivisor.sectionVal_canonicalSection]
    change Z.totalQuotientSheaf.obj.map (homOfLE le_top).op
      (↑σu⁻¹ : Z.totalQuotientSheaf.obj.obj (op ⊤)) * σ = 1
    rw [show (homOfLE le_top : (⊤ : Z.Opens) ⟶ ⊤) = homOfLE (le_refl ⊤) from rfl,
      totalQuotient_map_id, ← hσu, Units.inv_mul]
  have hloc : ∀ y : Z, y ∈ Stacks.Ample.nonvanishingLocus (MMP.CartierDivisor.sheaf (n • A)) s' ↔
      y ∉ cartierSupport (n • A + MMP.Intersection.principalDivisor σu) := by
    intro y
    rw [← Stacks.Ample.nonvanishingLocus_congr (MMP.CartierDivisor.sheafAddPrincipalIso (n • A) σu)
        s', hcan,
      MMP.CartierDivisor.mem_nonvanishingLocus_canonicalSection_iff]
  refine ⟨n, hn, σu, hσu.symm ▸ hσmem, (hloc z).mp (by rwa [hnv]), fun y hy => ?_⟩
  have := (hloc y).mpr hy
  rw [hnv] at this
  exact hsV this

end

section

open MMP.Intersection Opposite TopologicalSpace

section Generation

variable {Z : Scheme.{u}}

/-- **A generating family of sections in one degree.** If `A` has a basis of nonvanishing loci on
the quasi-compact `Z`, then for some `n₀ > 0` and every `L > 0` finitely many sections of
`𝒪_Z(L n₀ A)` have no common zero: finitely many `Z_σ` cover `Z`, and suitable powers bring the
sections to one degree. -/
private theorem exists_generating_sections [CompactSpace Z] [Nonempty Z] {A : Z.CartierDivisor}
    (hAb : IsNvBasis A) :
    ∃ n₀ : ℕ, 0 < n₀ ∧ ∀ L : ℕ,
      ∃ (N : ℕ) (s : Fin (N + 1) → (Z.totalQuotientSheaf.obj.obj (op ⊤))ˣ),
      (∀ j, ((s j : _ˣ) : Z.totalQuotientSheaf.obj.obj (op ⊤)) ∈
        lineBundleSections ((L * n₀) • A) ⊤) ∧
      ∀ z : Z, ∃ j,
        z ∉ cartierSupport ((L * n₀) • A + MMP.Intersection.principalDivisor (s j)) := by
  classical
  choose n hn σ hσ hzσ _ using fun z : Z => hAb z ⊤ trivial
  let O : Z → Set Z := fun z =>
    (cartierSupport (n z • A + MMP.Intersection.principalDivisor (σ z)))ᶜ
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover O
    (fun z => (isClosed_cartierSupport _).isOpen_compl) (fun z _ => Set.mem_iUnion.mpr ⟨z, hzσ z⟩)
  have hSne : S.Nonempty := by
    obtain ⟨z⟩ : Nonempty Z := inferInstance
    obtain ⟨x, hx, -⟩ := Set.mem_iUnion₂.mp (hS (Set.mem_univ z))
    exact ⟨x, hx⟩
  set n₀ := ∏ z ∈ S, n z with hn₀
  have hdiv : ∀ z ∈ S, n z ∣ n₀ := fun z hz => Finset.dvd_prod_of_mem _ hz
  refine ⟨n₀, Finset.prod_pos fun z _ => hn z, fun L => ?_⟩
  -- the sections `σ_z ^ (L n₀ / n_z)`, indexed by `S`
  let τ : S → (Z.totalQuotientSheaf.obj.obj (op ⊤))ˣ := fun z => σ z ^ (L * (n₀ / n z))
  have hdeg : ∀ z : S, (L * (n₀ / n z)) * n z = L * n₀ := fun z => by
    rw [mul_assoc, Nat.div_mul_cancel (hdiv z z.2)]
  have hτmem : ∀ z : S, ((τ z : _ˣ) : Z.totalQuotientSheaf.obj.obj (op ⊤)) ∈
      lineBundleSections ((L * n₀) • A) ⊤ := by
    intro z
    have := pow_mem_lineBundleSections (hσ z) (L * (n₀ / n z))
    rw [smul_smul, hdeg z] at this
    rwa [Units.val_pow_eq_pow_val]
  have hτdiv : ∀ z : S, (L * n₀) • A + MMP.Intersection.principalDivisor (τ z) =
      (L * (n₀ / n z)) • (n z • A + MMP.Intersection.principalDivisor (σ z)) := by
    intro z
    rw [← nsmul_add_principalDivisor_pow, smul_smul, hdeg z]
  have hcard : 0 < Fintype.card S := Fintype.card_pos_iff.mpr ⟨⟨_, hSne.choose_spec⟩⟩
  set N := Fintype.card S - 1
  have hN : Fintype.card S = N + 1 := by omega
  let e : S ≃ Fin (N + 1) := Fintype.equivFinOfCardEq hN
  refine ⟨N, fun j => τ (e.symm j), fun j => hτmem _, fun z => ?_⟩
  obtain ⟨x, hx, hzx⟩ := Set.mem_iUnion₂.mp (hS (Set.mem_univ z))
  refine ⟨e ⟨x, hx⟩, ?_⟩
  simp only [Equiv.symm_apply_apply]
  rw [hτdiv]
  exact notMem_cartierSupport_nsmul hzx _

end Generation

section ZChoice

variable {k : Type u} [Field k] {Z : Scheme.{u}} (sZ : Z ⟶ Spec (.of k))

/-- **Avoiding a point is a polynomial condition.** If one of the sections `s_j` of `𝒪_Z(D)` does
not vanish at `x`, there is a nonzero polynomial `Q` such that `∑ cⱼ sⱼ` does not vanish at `x`
whenever `Q(c) ≠ 0`: the values at `x` are `k`-linear in `c`, and a linear form on `κ(x)` not
killing a nonzero value gives `Q`. -/
private theorem exists_polynomial_isUnit_secNumAt (D : Z.CartierDivisor) {N : ℕ}
    (s : Fin (N + 1) → Z.totalQuotientSheaf.obj.obj (op ⊤))
    (hs : ∀ j, s j ∈ lineBundleSections D ⊤) (x : Z) (hx : ∃ j, IsUnit (secNumAt x D (s j))) :
    ∃ Q : MvPolynomial (Fin (N + 1)) k, Q ≠ 0 ∧ ∀ c : Fin (N + 1) → k,
      MvPolynomial.eval c Q ≠ 0 →
        IsUnit (secNumAt x D (∑ j, scalarsToGlobalSections k sZ (c j) • s j)) := by
  classical
  obtain ⟨j₀, hj₀⟩ := hx
  set φ : k →+* Z.residueField x :=
    (Z.residue x).hom.comp ((Z.presheaf.germ ⊤ x (Opens.mem_top _)).hom.comp
      (scalarsToGlobalSections k sZ)) with hφ
  letI : Module k (Z.residueField x) := Module.compHom _ φ
  set v : Fin (N + 1) → Z.residueField x := fun j => Z.residue x (secNumAt x D (s j))
  have hv₀ : v j₀ ≠ 0 := by
    change (Z.residue x).hom _ ≠ 0
    exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hj₀
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_ne_zero k hv₀
  set Q : MvPolynomial (Fin (N + 1)) k := ∑ j, MvPolynomial.C (l (v j)) * MvPolynomial.X j
  have hQeval : ∀ c, MvPolynomial.eval c Q = l (∑ j, c j • v j) := by
    intro c
    simp only [Q, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, map_smul,
      smul_eq_mul, mul_comm]
  refine ⟨Q, fun h0 => hl ?_, fun c hc => ?_⟩
  · have := hQeval (Pi.single j₀ 1)
    rw [h0, map_zero] at this
    have hsum : ∑ j, (Pi.single j₀ (1 : k) : Fin (N + 1) → k) j • v j = v j₀ := by
      rw [Finset.sum_eq_single j₀ (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp)]
      simp
    rw [hsum] at this
    exact this.symm
  · rw [hQeval] at hc
    have hne : ∑ j, c j • v j ≠ 0 := fun h0 => hc (by rw [h0, map_zero])
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    change (Z.residue x).hom _ ≠ 0
    rw [secNumAt_sum x D Finset.univ _ hs, map_sum]
    convert hne using 2 with j
    rw [map_mul]
    rfl

/-- A nonzero multivariate polynomial over an infinite field does not vanish at some point. -/
private theorem exists_eval_ne_zero [Infinite k] {σ : Type*} {Q : MvPolynomial σ k} (hQ : Q ≠ 0) :
    ∃ c : σ → k, MvPolynomial.eval c Q ≠ 0 := by
  by_contra h
  push Not at h
  exact hQ (MvPolynomial.funext fun c => by simpa using h c)

end ZChoice

end

section

open MMP.Intersection Opposite TopologicalSpace

section WFramework

variable {Z W : Scheme.{u}} [IsIntegral W] (g : W ⟶ Z)

private theorem pullSec_sum (D : Z.CartierDivisor) {ι : Type*} (S : Finset ι)
    (r : ι → Γ(Z, ⊤)) {σ : ι → Z.totalQuotientSheaf.obj.obj (op ⊤)}
    (hσ : ∀ i, σ i ∈ lineBundleSections D ⊤) :
    pullSec g D (∑ i ∈ S, r i • σ i) =
      ∑ i ∈ S,
        W.presheaf.germ (g ⁻¹ᵁ ⊤) _ (Opens.mem_top _) (g.app ⊤ (r i)) * pullSec g D (σ i) := by
  change (g.stalkMap (genericPoint W)).hom (secNumAt _ D _) = _
  rw [secNumAt_sum _ D S r hσ, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul]
  congr 1
  exact Scheme.Hom.germ_stalkMap_apply g ⊤ _ (Opens.mem_top _) (r i)

variable [IsLocallyNoetherian W] [IsNormal W]

/-- The divisorial section of `𝒪_W(M)` given by a rational function `φ ∈ K(W)` with
`M + div φ ≥ 0`. -/
private def secOfFun (M : Divisor W) (φ : W.functionField)
    (h : φ ≠ 0 → ∀ E : MMP.Mori.PrimeDivisor W, 0 ≤ M.coeff E + W.ord φ E.genericPoint) :
    M.divisorialSubmodule ⊤ :=
  ⟨(rationalFunctionsPresheafTopEquiv W).symm (toRationalFunctions φ), fun E _ => by
    by_cases hφ : φ = 0
    · left
      subst hφ
      change (toRationalFunctions (0 : W.functionField)) E.component = 0
      rw [map_zero]; rfl
    · right
      change WithZero.exp (-M.coeff E) ≤
        E.valuation ((unitOfFunction hφ : RationalFunctions W) E.component)
      rw [E.valuation_component, WithZero.exp_le_exp, ord_unitOfFunction E hφ]
      have := h hφ E
      omega⟩

private theorem sectionToRationalFunctions_secOfFun (M : Divisor W) (φ : W.functionField) (h) :
    Divisor.sectionToRationalFunctions (secOfFun M φ h) = toRationalFunctions φ := rfl

private theorem secOfFun_ne_zero (M : Divisor W) {φ : W.functionField} (hφ : φ ≠ 0) (h) :
    secOfFun M φ h ≠ 0 :=
  ne_zero_of_sectionToRationalFunctions_eq hφ (sectionToRationalFunctions_secOfFun M φ h)

/-- The coefficients of the divisor of zeros of a section `s` with `sectionToRationalFunctions s`
read from `φ ∈ K(W)`. -/
private theorem coeff_zeroDivisor_eq [CompactSpace W] (M : Divisor W) (s : M.divisorialSubmodule ⊤)
    (hs : s ≠ 0) {φ : W.functionField} (hφ : φ ≠ 0)
    (hsφ : Divisor.sectionToRationalFunctions s = toRationalFunctions φ)
    (E : MMP.Mori.PrimeDivisor W) :
    (M.zeroDivisor s hs).coeff E = W.ord φ E.genericPoint + M.coeff E := by
  rw [Divisor.zeroDivisor_eq, DivisorWithCoeffs.coeff_add, coeff_principalDivisor]
  congr 1
  exact ord_toRationalFunctions E hφ _ (by rwa [IsUnit.unit_spec])

end WFramework

end

section

open MMP.Intersection Opposite TopologicalSpace

section WSystem

variable {k : Type u} [Field k] {Z W : Scheme.{u}}

private theorem scalarsToGlobalSections_comp (sZ : Z ⟶ Spec (.of k)) (g : W ⟶ Z) (c : k) :
    scalarsToGlobalSections k (g ≫ sZ) c = g.app ⊤ (scalarsToGlobalSections k sZ c) := by
  simp only [scalarsToGlobalSections, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
    RingHom.comp_apply]
  rfl

variable [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]
  [IsLocallyNoetherian Z]

/-- **Pulling a linear system back to a normal variety.** Let `s₀, …, s_N` be sections of `𝒪_Z(D)`
without common zero and `g : W ⟶ Z` a morphism from a normal integral scheme. There are a Cartier
divisor `M` on `W` and sections `t_j` of `𝒪_W(M)` without common zero such that, for every
coefficient vector `c` with `σ = ∑ cⱼ sⱼ` not vanishing at `g(η_W)`, the divisor of zeros of
`∑ cⱼ tⱼ` is the Weil divisor of the pull-back `g^*(D + div σ)`: `M` is the pull-back of the
divisor of a section `s_{j₀}` not vanishing at `g(η_W)`, and `tⱼ = g^*(sⱼ / s_{j₀})`. -/
private theorem exists_divisorialSystem (sZ : Z ⟶ Spec (.of k)) (g : W ⟶ Z)
    (sW : W ⟶ Spec (.of k)) (hgW : g ≫ sZ = sW) (D : Z.CartierDivisor) {N : ℕ}
    (s : Fin (N + 1) → (Z.totalQuotientSheaf.obj.obj (op ⊤))ˣ)
    (hs : ∀ j, ((s j : _ˣ) : Z.totalQuotientSheaf.obj.obj (op ⊤)) ∈ lineBundleSections D ⊤)
    (hgen : ∀ z : Z, ∃ j, z ∉ cartierSupport (D + MMP.Intersection.principalDivisor (s j))) :
    ∃ (MW : Divisor W) (t : Fin (N + 1) → MW.divisorialSubmodule ⊤), MW.IsCartier ∧
      (∀ w : W, ∃ j, ∃ hj : t j ≠ 0, w ∉ (MW.zeroDivisor (t j) hj).supp) ∧
      ∀ (c : Fin (N + 1) → k) (u : (Z.totalQuotientSheaf.obj.obj (op ⊤))ˣ),
        (u : Z.totalQuotientSheaf.obj.obj (op ⊤)) =
          ∑ j, scalarsToGlobalSections k sZ (c j) •
            ((s j : _ˣ) : Z.totalQuotientSheaf.obj.obj (op ⊤)) →
        g (genericPoint W) ∉ cartierSupport (D + MMP.Intersection.principalDivisor u) →
        ∃ hτ : (∑ j, scalarsToGlobalSections k sW (c j) • t j) ≠ 0,
          ∀ HW : W.CartierDivisor, IsPullback g (D + MMP.Intersection.principalDivisor u) HW →
            IsWeilDivisorOfCartier HW (MW.zeroDivisor _ hτ) := by
  classical
  subst hgW
  haveI : IsNoetherian W := ⟨⟩
  obtain ⟨j₀, hj₀⟩ := hgen (g (genericPoint W))
  have hpb : ∀ σ : (Z.totalQuotientSheaf.obj.obj (op ⊤))ˣ,
      g (genericPoint W) ∉ cartierSupport (D + MMP.Intersection.principalDivisor σ) →
      ∃ Hσ, IsPullback g (D + MMP.Intersection.principalDivisor σ) Hσ := fun σ hσ =>
    exists_isPullback (f := g) fun ξ hξ => by
      rwa [eq_genericPoint_of_mem_schemeAssociatedPoints hξ]
  obtain ⟨H0, hH0⟩ := hpb _ hj₀
  obtain ⟨MW, hMW⟩ := MMP.Intersection.exists_isWeilDivisorOfCartier H0
  set p0 := pullSec g D ((s j₀ : _ˣ) : Z.totalQuotientSheaf.obj.obj (op ⊤)) with hp0def
  have hp0 : p0 ≠ 0 := (pullSec_ne_zero_iff g D _ (hs j₀)).mpr hj₀
  choose cE hcE using fun E : MMP.Mori.PrimeDivisor W => exists_primeDivisorOrder_eq g D E
  have hMWc : ∀ E, MW.coeff E = W.ord p0 E.genericPoint + cE E := fun E => by
    rw [← (hMW E).primeDivisorOrder_eq]; exact hcE E (s j₀) (hs j₀) H0 hH0
  have hkey : ∀ (σ : (Z.totalQuotientSheaf.obj.obj (op ⊤))ˣ),
      (σ : Z.totalQuotientSheaf.obj.obj (op ⊤)) ∈ lineBundleSections D ⊤ →
      ∀ Hσ, IsPullback g (D + MMP.Intersection.principalDivisor σ) Hσ →
      ∀ E : MMP.Mori.PrimeDivisor W, pullSec g D σ ≠ 0 →
        MW.coeff E + W.ord (pullSec g D σ * p0⁻¹) E.genericPoint = primeDivisorOrder E Hσ := by
    intro σ hσ Hσ hHσ E hne
    rw [Scheme.ord_mul hne (inv_ne_zero hp0), scheme_ord_inv hp0, hMWc, hcE E σ hσ Hσ hHσ]
    ring
  set φ : Fin (N + 1) → W.functionField := fun j =>
    pullSec g D ((s j : _ˣ) : Z.totalQuotientSheaf.obj.obj (op ⊤)) * p0⁻¹ with hφdef
  have hφ : ∀ j, φ j ≠ 0 → ∀ E : MMP.Mori.PrimeDivisor W,
      0 ≤ MW.coeff E + W.ord (φ j) E.genericPoint := by
    intro j hj E
    have hne : pullSec g D ((s j : _ˣ) : Z.totalQuotientSheaf.obj.obj (op ⊤)) ≠ 0 :=
      left_ne_zero_of_mul hj
    obtain ⟨Hj, hHj⟩ := hpb _ ((pullSec_ne_zero_iff g D _ (hs j)).mp hne)
    rw [hkey (s j) (hs j) Hj hHj E hne]
    exact (primeDivisorOrder_nonneg_and_pos_of_isPullback g
      (isEffective_add_principalDivisor _ (hs j)) hHj E).1
  set t : Fin (N + 1) → MW.divisorialSubmodule ⊤ := fun j => secOfFun MW (φ j) (hφ j) with htdef
  refine ⟨MW, t, hMW.isCartier, fun w => ?_, fun c u hu hη => ?_⟩
  · obtain ⟨j, hj⟩ := hgen (g w)
    have hjη := notMem_cartierSupport_of_specializes (specializes_map_genericPoint g w) hj
    have hne := (pullSec_ne_zero_iff g D _ (hs j)).mpr hjη
    have hφj : φ j ≠ 0 := mul_ne_zero hne (inv_ne_zero hp0)
    obtain ⟨Hj, hHj⟩ := hpb _ hjη
    refine ⟨j, secOfFun_ne_zero MW hφj _, fun hw => ?_⟩
    obtain ⟨E, hE, hwE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hw
    apply hE
    rw [coeff_zeroDivisor_eq MW (t j) _ hφj rfl E, add_comm (W.ord (φ j) E.genericPoint),
      hkey (s j) (hs j) Hj hHj E hne]
    refine primeDivisorOrder_eq_zero_of_isPullback g hHj E
      (notMem_cartierSupport_of_specializes ?_ hj)
    have : E.genericPoint ⤳ w := by
      rwa [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact this.map g.continuous
  · have hsmem : (u : Z.totalQuotientSheaf.obj.obj (op ⊤)) ∈ lineBundleSections D ⊤ := by
      rw [hu]; exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hs j)
    have hne := (pullSec_ne_zero_iff g D u hsmem).mpr hη
    set φu := pullSec g D (u : Z.totalQuotientSheaf.obj.obj (op ⊤)) * p0⁻¹ with hφudef
    have hφu : φu ≠ 0 := mul_ne_zero hne (inv_ne_zero hp0)
    have hpu : φu = ∑ j, W.presheaf.germ (g ⁻¹ᵁ ⊤) _ (Opens.mem_top _)
        (g.app ⊤ (scalarsToGlobalSections k sZ (c j))) * φ j := by
      rw [hφudef, hu, pullSec_sum g D Finset.univ _ hs, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hφdef, mul_assoc]
    have hτeq : Divisor.sectionToRationalFunctions
        (∑ j, scalarsToGlobalSections k (g ≫ sZ) (c j) • t j) = toRationalFunctions φu := by
      change (rationalFunctionsPresheafTopEquiv W)
          (∑ j, scalarsToGlobalSections k (g ≫ sZ) (c j) • t j).1 = _
      rw [Submodule.coe_sum, map_sum, hpu, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      funext Z'
      rw [map_mul, Pi.mul_apply]
      change (scalarsToGlobalSections k (g ≫ sZ) (c j) • (t j).1) ⟨Z', trivial⟩ = _
      rw [rationalFunctions_smul_apply]
      congr 1
      rw [scalarsToGlobalSections_comp]
      change _ = (W.presheaf.stalkSpecializes _).hom _
      exact (TopCat.Presheaf.germ_stalkSpecializes_apply W.presheaf (U := g ⁻¹ᵁ ⊤)
        (Opens.mem_top _) _ _).symm
    have hτ : (∑ j, scalarsToGlobalSections k (g ≫ sZ) (c j) • t j) ≠ 0 :=
      ne_zero_of_sectionToRationalFunctions_eq hφu hτeq
    refine ⟨hτ, fun HW hHW P => ?_⟩
    have e1 := coeff_zeroDivisor_eq MW _ hτ hφu hτeq P
    rw [add_comm (W.ord φu P.genericPoint) (MW.coeff P), hkey u hsmem HW hHW P hne] at e1
    convert isOrderAlong_primeDivisorOrder HW P using 1

end WSystem

end

section

open MMP.Intersection Opposite TopologicalSpace

section Supports

variable {Z W : Scheme.{u}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] (g : W ⟶ Z)

/-- **The support of a pulled-back effective divisor.** On a normal integral scheme the support of
the Weil divisor of `g^*H`, `H` effective, is `g⁻¹(Supp H)`: a point off the support has order
zero along every prime divisor through it, so the pulled-back local equation is a unit there
(`MMP.Mori.exists_unit_stalk_of_forall_ord_eq_zero`), and so is the local equation of `H`. -/
private theorem mem_supp_iff_of_isPullback {H : Z.CartierDivisor} (hH : IsEffective H)
    {HW : W.CartierDivisor} (hHW : IsPullback g H HW) {B : Divisor W}
    (hB : IsWeilDivisorOfCartier HW B) (x : W) :
    x ∈ B.supp ↔ g x ∈ cartierSupport H := by
  constructor
  · intro hx
    obtain ⟨P, hP, hxP⟩ := DivisorWithCoeffs.mem_supp_iff.mp hx
    by_contra hgx
    apply hP
    rw [← (hB P).primeDivisorOrder_eq]
    refine primeDivisorOrder_eq_zero_of_isPullback g hHW P
      (notMem_cartierSupport_of_specializes ?_ hgx)
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hxP
    exact (specializes_iff_mem_closure.mpr hxP).map g.continuous
  · intro hgx
    by_contra hx
    obtain ⟨V, hV, h, hu, hloc⟩ := hH (g x)
    set a : Γ(W, g ⁻¹ᵁ V) := g.app V h with ha_def
    have ha : ∀ (Z' : irreducibleComponents W) (hZ' : componentGenericPoint W Z' ∈ g ⁻¹ᵁ V),
        (W.presheaf.germ (g ⁻¹ᵁ V) _ hZ').hom a ≠ 0 := fun Z' hZ' =>
      germ_ne_zero_of_isPullback g hHW hu hloc hZ'
    set χ := MMP.Threefold.Resolution.sectionUnit a ha
    have hxV : x ∈ g ⁻¹ᵁ V := hV
    have hηV : genericPoint W ∈ g ⁻¹ᵁ V :=
      ((genericPoint_spec W).specializes (Set.mem_univ x)).mem_open (g ⁻¹ᵁ V).isOpen hxV
    have hχ : (χ : RationalFunctions W) =
        toRationalFunctions ((W.presheaf.germ (g ⁻¹ᵁ V) _ hηV).hom a) := by
      funext Z'
      have hZ' : componentGenericPoint W Z' ∈ g ⁻¹ᵁ V :=
        (specializes_genericPoint Z').mem_open (g ⁻¹ᵁ V).isOpen hηV
      rw [MMP.Threefold.Resolution.sectionUnit_apply a ha Z' hZ']
      change _ = (W.presheaf.stalkSpecializes _).hom _
      exact (TopCat.Presheaf.germ_stalkSpecializes_apply W.presheaf hηV _ _).symm
    have hne : (W.presheaf.germ (g ⁻¹ᵁ V) _ hηV).hom a ≠ 0 := by
      have := ha ⟨Set.univ, univ_mem_irreducibleComponents W⟩
        ((specializes_genericPoint _).mem_open (g ⁻¹ᵁ V).isOpen hηV)
      intro h0; apply this
      rw [← TopCat.Presheaf.germ_stalkSpecializes_apply W.presheaf hηV
        (specializes_genericPoint _), h0, map_zero]
    have hord : ∀ E : MMP.Mori.PrimeDivisor W, x ∈ E.support → E.ord χ = 0 := by
      intro E hxE
      have hEV : E.genericPoint ∈ g ⁻¹ᵁ V := by
        have : E.genericPoint ⤳ x := by
          rwa [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact this.mem_open (g ⁻¹ᵁ V).isOpen hxV
      rw [ord_toRationalFunctions E hne χ hχ]
      have h1 := primeDivisorOrder_eq_ord_of_isPullback g hHW hu hloc E hEV
        (germ_ne_zero_of_isPullback g hHW hu hloc hEV)
      rw [algebraMap_germ_eq_germ] at h1
      rw [← h1, (hB E).primeDivisorOrder_eq]
      by_contra hBE
      exact hx (DivisorWithCoeffs.mem_supp_iff.mpr ⟨E, hBE, hxE⟩)
    obtain ⟨w, hw⟩ := exists_unit_stalk_of_forall_ord_eq_zero (mem_pointComponent x) χ hord
    have hZx : componentGenericPoint W (pointComponent x) ∈ g ⁻¹ᵁ V :=
      ((isGenericPoint_componentGenericPoint W _).specializes
        (mem_pointComponent x)).mem_open (g ⁻¹ᵁ V).isOpen hxV
    have hgerm : (W.presheaf.germ (g ⁻¹ᵁ V) x hxV).hom a = w := by
      apply stalkToRationalFunctions_injective (mem_pointComponent x)
      rw [hw, MMP.Threefold.Resolution.sectionUnit_apply a ha _ hZx]
      exact TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _
    have hunit : IsUnit ((g.stalkMap x).hom (Z.presheaf.germ V (g x) hV h)) := by
      rw [Scheme.Hom.germ_stalkMap_apply, ← ha_def, hgerm]
      exact w.isUnit
    exact ((notMem_cartierSupport_iff_isUnit_germ hu hloc hV).mpr
      ((isUnit_map_iff (g.stalkMap x).hom _).mp hunit)) hgx

end Supports

section MoriPullback

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y]
  [IsNormal Y] {f : X ⟶ Y}

/-- The pull-back of a Cartier divisor has coefficient zero along a prime divisor whose generic
point maps off the support: on the complement of the support `1` is a local equation. -/
private theorem coeff_eq_zero_of_isPullback {B : Divisor Y}
    {hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ B.supp}
    {B' : Divisor X} (h : B.IsPullback f hB B') (E : MMP.Mori.PrimeDivisor X)
    (hE : f E.genericPoint ∉ (B.supp : Set Y)) : B'.coeff E = 0 := by
  let U : Y.Opens := ⟨(B.supp : Set Y)ᶜ, (DivisorWithCoeffs.isClosed_supp B).isOpen_compl⟩
  have hφ : B.IsLocalEquation U 1 := by
    intro P hP
    rw [PrimeDivisor.ord_one]
    by_contra hne
    obtain ⟨y, hyP, hyU⟩ := hP
    exact hyU (DivisorWithCoeffs.support_subset_supp hne hyP)
  have hEU : (E.support ∩ f ⁻¹ᵁ U).Nonempty :=
    ⟨E.genericPoint, genericPoint_mem_support E, hE⟩
  rw [h U 1 hφ E hEU]
  have hZ := E.map_componentGenericPoint_mem f hEU
  rw [pullbackComponent_eq hB hφ hZ (mem_pointComponent _) 1 (by simp)]
  simp [PrimeDivisor.ordUnit]

end MoriPullback

section NormalizationPoints

/-- A prime divisor of the normalization component `Tᵢ` lies over every prime Weil divisor `Γ` of
`T`: the normalization is finite and birational, hence surjective, and over the discrete valuation
ring `𝒪_{T,Γ}` it is a local isomorphism, so the point over `η_Γ` has codimension one. -/
private theorem exists_primeDivisor_map_genericPoint_eq {k : Type u} [Field k] {T : Scheme.{u}}
    {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    (N : NormalizationComponents sT hT) [IsNoetherian T] [IsReduced T]
    [LocallyOfFiniteType sT] (Γ : WeilDivisorPrime T) :
    ∃ (i : N.ι) (P : MMP.Mori.PrimeDivisor (N.X i)), (N.n i).base P.genericPoint =
      Γ.1.genericPoint := by
  obtain ⟨φ, hφ⟩ := N.exists_iso
  set ν := slcCurveNormalization T hT
  haveI : IsFinite ν :=
    Scheme.isFinite_normalization (isNagataScheme_of_locallyOfFiniteType_over_field k sT) hT
  have hbir : IsBirational ν := Scheme.isBirational_normalization T hT
  haveI : IsDominant ν := hbir.isDominant
  have hsurj : Function.Surjective ν.base :=
    Set.range_eq_univ.mp (ν.isClosedMap.isClosed_range.closure_eq ▸ ν.denseRange.closure_eq)
  obtain ⟨y, hy⟩ := hsurj Γ.1.genericPoint
  obtain ⟨⟨i, x⟩, hx⟩ := (sigmaMk N.X).surjective (φ.inv y)
  rw [sigmaMk_mk] at hx
  have hni : N.n i = Limits.Sigma.ι N.X i ≫ φ.hom ≫ ν := by rw [hφ, Limits.Sigma.ι_desc]
  have hxΓ : (N.n i) x = Γ.1.genericPoint := by
    rw [hni]
    have hφy : φ.hom (φ.inv y) = y := by
      rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]; rfl
    change ν (φ.hom (Limits.Sigma.ι N.X i x)) = _
    rwa [hx, hφy]
  -- the local ring at `x` is that of `T` at `η_Γ`, a discrete valuation ring
  have key : ∀ y' : T, (N.n i) x = y' →
      (∃ _ : IsDomain (T.presheaf.stalk y'), IsDiscreteValuationRing (T.presheaf.stalk y')) →
      Order.coheight y' = 1 → Order.coheight x = 1 := by
    intro y' hy' hdvr hcoh
    subst hy'
    obtain ⟨hdom, hdvr⟩ := hdvr
    haveI := isIso_stalkMap_normalizationComponents N i x
    let e := (asIso ((N.n i).stalkMap x)).commRingCatIsoToRingEquiv
    have h1 := ringKrullDim_eq_of_ringEquiv e
    rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight, hcoh] at h1
    exact_mod_cast h1.symm
  have hcoh := key _ hxΓ Γ.2 Γ.1.coheight_genericPoint
  refine ⟨i, AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hcoh, ?_⟩
  convert hxΓ using 2
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x hcoh

end NormalizationPoints

end

section

open MMP.Intersection Opposite TopologicalSpace

section Misc

/-- Off the preimage of `Supp H`, a pull-back of `H` has no support. -/
private theorem notMem_cartierSupport_of_isPullback {X Z : Scheme.{u}} {g : X ⟶ Z}
    {H : Z.CartierDivisor} {HX : X.CartierDivisor} (hHX : IsPullback g H HX) {x : X}
    (hx : g x ∉ cartierSupport H) : x ∉ cartierSupport HX :=
  notMem_cartierSupport_of_isLocalEquationAt_one
    (hHX.isLocalEquationAt (isLocalEquationAt_one_of_notMem_cartierSupport hx)
      (isFraction_one_one_one _) (by simpa using isFraction_one_one_one _))

/-- Restricting a pull-back to an open subscheme computes the orders along the restricted prime
divisors: `U ⟶ X` is a local isomorphism. -/
private theorem primeDivisorOrder_restrict_eq {X Z : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Z] (U : X.Opens) [Nonempty U] (g : X ⟶ Z)
    {H : Z.CartierDivisor}
    {HX : X.CartierDivisor} (hHX : IsPullback g H HX) {HU : U.toScheme.CartierDivisor}
    (hHU : IsPullback (U.ι ≫ g) H HU) (W : MMP.Mori.PrimeDivisor U.toScheme) :
    primeDivisorOrder W HU = primeDivisorOrder (OpenWeilRestriction.primeDivisorMap U.ι W) HX := by
  haveI : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  obtain ⟨HU', hHU'⟩ := exists_isPullback (f := U.ι) (D := HX) fun ξ hξ =>
    notMem_cartierSupport_of_isPullback hHX (hHU.1 ξ hξ)
  have hcomp := IsPullback.comp_eq hHX hHU' hHU
  subst hcomp
  set P := OpenWeilRestriction.primeDivisorMap U.ι W
  have hV : (primeDivisorSubvariety P).genericPoint =
      U.ι (primeDivisorSubvariety W).genericPoint :=
    OpenWeilRestriction.genericPoint_primeDivisorMap _ _
  haveI : Ring.KrullDimLE 1 (X.presheaf.stalk (U.ι (primeDivisorSubvariety W).genericPoint)) := by
    rw [← hV]; exact krullDimLE_of_coheight_le P.coheight_genericPoint.le
  exact (hHU'.isOrderAlong_of_isIso_stalkMap hV
    (isOrderAlong_primeDivisorOrder HX P)).primeDivisorOrder_eq

/-- A dense open of the affine space of coefficient vectors contains the points where some
nonzero polynomial does not vanish. -/
private theorem exists_polynomial_coefficientPoint_mem {k : Type u} [Field k] {N : ℕ}
    (U : (MMP.Threefold.Bridges.coefficientSpace k N).Opens)
    (hU : Dense (U : Set (MMP.Threefold.Bridges.coefficientSpace k N))) :
    ∃ Q : MvPolynomial (Fin (N + 1)) k, Q ≠ 0 ∧ ∀ c : Fin (N + 1) → k,
      MvPolynomial.eval c Q ≠ 0 → MMP.Threefold.Bridges.coefficientPoint c ∈ U := by
  obtain ⟨p, hp⟩ := hU.nonempty
  obtain ⟨_, ⟨f, rfl⟩, hpf, hfU⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens
      (R := MvPolynomial (Fin (N + 1)) k)).exists_subset_of_mem_open hp U.isOpen
  refine ⟨f, fun h0 => ?_, fun c hc => hfU ?_⟩
  · rw [h0] at hpf
    exact (PrimeSpectrum.mem_basicOpen _ _).mp hpf (zero_mem _)
  · exact (PrimeSpectrum.mem_basicOpen _ _).mpr fun hf => hc (RingHom.mem_ker.mp hf)

/-- A prime divisor whose support lies in a finite union of supports of prime divisors is one
of them. -/
private theorem mem_of_support_subset_biUnion {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    [IsNormal Y] (S : Finset (MMP.Mori.PrimeDivisor Y)) (E : MMP.Mori.PrimeDivisor Y)
    (h : E.support ⊆ ⋃ F ∈ S, F.support) : E ∈ S := by
  obtain ⟨F, hF, hEF⟩ := Set.mem_iUnion₂.mp (h (genericPoint_mem_support E))
  rwa [MMP.Threefold.Mori.primeDivisor_eq_of_genericPoint_mem_support F E hEF] at hF

end Misc

end

section

open MMP.Intersection Opposite TopologicalSpace

section DltComponent

/-- An open subscheme contained in the smooth locus of `s` is smooth. -/
private theorem isSmoothScheme_ι_of_le_smoothLocus {Y : Scheme.{u}} {k : Type u} [Field k]
    {s : Y ⟶ Spec (.of k)} {V : Y.Opens} (hV : V ≤ smoothLocus s) :
    MMP.Mori.IsSmoothScheme (V.ι ≫ s) := by
  rw [MMP.Mori.IsSmoothScheme, eq_top_iff]
  intro x _
  obtain ⟨W, hxW, hW⟩ := mem_smoothLocus_iff.1 (hV x.2 : V.ι x ∈ smoothLocus s)
  refine mem_smoothLocus_iff.2 ⟨V.ι ⁻¹ᵁ W, hxW, ?_⟩
  have : Smooth (W.ι ≫ s) := hW
  rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
  infer_instance

/-- A nonempty open subscheme of a normal variety is a normal variety. -/
private theorem isNormalVariety_ι {k : Type u} [Field k] {Y : Scheme.{u}}
    {s : Y ⟶ Spec (.of k)} (h : IsNormalVariety k s) (V : Y.Opens) [Nonempty V] :
    IsNormalVariety k (V.ι ≫ s) := by
  have := h.1
  have := h.2
  have : IsIntegral Y := h.1.toIsIntegral
  have : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace s
  have : IsNoetherian Y := {}
  exact ⟨⟨⟩, inferInstance⟩

/-- The union of the supports of a finite set of prime divisors exhibiting an snc subset. -/
private theorem exists_finset_of_isSNCSubset {Y : Scheme.{u}} {k : Type u} [Field k]
    {s : Y ⟶ Spec (.of k)} {C : Closeds Y} (h : IsSNCSubset s C) :
    ∃ S : Finset (MMP.Mori.PrimeDivisor Y), (⋃ E ∈ S, E.support) = (C : Set Y) := by
  rcases h with h | ⟨S, hS, -⟩
  · exact ⟨∅, by simp [h]⟩
  · exact ⟨S, hS⟩

private theorem coe_supp_add_smul {X : Scheme.{u}} {Θ : QDivisor X} (hΘ : ∀ P, 0 ≤ Θ.coeff P)
    {W : Divisor X} (hW : ∀ P, 0 ≤ W.coeff P) {t : ℚ} (ht : 0 < t) :
    ((Θ + t • Divisor.toQDivisor W).supp : Set X) = (Θ.supp : Set X) ∪ (W.supp : Set X) := by
  ext x
  simp only [Set.mem_union, SetLike.mem_coe, DivisorWithCoeffs.mem_supp_iff,
    DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, Divisor.coeff_toQDivisor,
    smul_eq_mul]
  constructor
  · rintro ⟨E, hE, hxE⟩
    by_cases h : Θ.coeff E = 0
    · right
      refine ⟨E, fun h0 => hE ?_, hxE⟩
      rw [h, h0]; simp
    · exact Or.inl ⟨E, h, hxE⟩
  · rintro (⟨E, hE, hxE⟩ | ⟨E, hE, hxE⟩)
    · refine ⟨E, fun h0 => hE ?_, hxE⟩
      have h1 := hΘ E
      have h2 : (0 : ℚ) ≤ W.coeff E := by exact_mod_cast hW E
      nlinarith
    · refine ⟨E, fun h0 => hE ?_, hxE⟩
      have h1 := hΘ E
      have h2 : (0 : ℚ) ≤ W.coeff E := by exact_mod_cast hW E
      have : (W.coeff E : ℚ) = 0 := by nlinarith
      exact_mod_cast this

end DltComponent

end

section

open MMP.Intersection Opposite TopologicalSpace

section DltMain

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]

/-- **A general member of a pulled-back free system keeps a dlt pair dlt.** Let `(X, Θ)` be a dlt
pair and `g : X ⟶ Z` a morphism over `k`, and let `s₀, …, s_N` be sections of `𝒪_Z(D)` without
common zero. There are a nonzero polynomial `Q` and finitely many points `F` of `Z` such that for
every `c` with `Q(c) ≠ 0` and `σ = ∑ cⱼ sⱼ` not vanishing on `F`, the Weil divisor `W` of
`g^*(D + div σ)` is reduced, shares no component with `Θ`, and `(X, Θ + a⁻¹ W)` is dlt for every
`a > 0`. The proof reads the dlt property on a fixed log resolution `f : Y ⟶ X`
(`MMP.Mori.isDltPair_iff_exists_isLogResolution`): by Bertini the pulled-back system is snc
with the fixed snc divisors on `Y` and on the snc locus `U` of `(X, Θ)`, and reduced on `X`; the
general member contains none of the generic points of the components of the snc divisor on `Y`,
so the discrepancies over `X ∖ U` are unchanged. -/
private theorem exists_polynomial_isDltPair_add {X Z : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsLocallyNoetherian Z]
    {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} (g : X ⟶ Z) (hg : g ≫ sZ = sX)
    {n : ℕ} {K : Divisor X} {Θ : QDivisor X} (hdlt : IsDltPair sX n K Θ)
    (D : Z.CartierDivisor) {N : ℕ} (s : Fin (N + 1) → (Z.totalQuotientSheaf.obj.obj (op ⊤))ˣ)
    (hs : ∀ j, ((s j : _ˣ) : Z.totalQuotientSheaf.obj.obj (op ⊤)) ∈ lineBundleSections D ⊤)
    (hgen : ∀ z : Z, ∃ j, z ∉ cartierSupport (D + MMP.Intersection.principalDivisor (s j))) :
    ∃ (Q : MvPolynomial (Fin (N + 1)) k) (F : Finset Z), Q ≠ 0 ∧ g (genericPoint X) ∈ F ∧
      (∀ P ∈ Θ.support, g P.genericPoint ∈ F) ∧
      ∀ (c : Fin (N + 1) → k) (u : (Z.totalQuotientSheaf.obj.obj (op ⊤))ˣ),
        (u : Z.totalQuotientSheaf.obj.obj (op ⊤)) =
          ∑ j, scalarsToGlobalSections k sZ (c j) •
            ((s j : _ˣ) : Z.totalQuotientSheaf.obj.obj (op ⊤)) →
        MvPolynomial.eval c Q ≠ 0 →
        (∀ z ∈ F, z ∉ cartierSupport (D + MMP.Intersection.principalDivisor u)) →
        ∀ (HX : X.CartierDivisor), IsPullback g (D + MMP.Intersection.principalDivisor u) HX →
        ∀ (W : Divisor X), IsWeilDivisorOfCartier HX W →
          (∀ P, W.coeff P ≤ 1) ∧ (∀ P, W.coeff P ≠ 0 → Θ.coeff P = 0) ∧
          ∀ a : ℕ, 0 < a → IsDltPair sX n K (Θ + (a : ℚ)⁻¹ • Divisor.toQDivisor W) := by
  classical
  haveI : PerfectField k := PerfectField.ofCharZero
  haveI : IsNoetherian X := ⟨⟩
  have hX : IsNormalVariety k sX := hdlt.1.1
  have hpair := hdlt.1
  have hcoeff := hdlt.2.1
  obtain ⟨Zc, hZne, hZsm, hZsnc, Y, f, hf, hpure, hsncY, hdisc⟩ :=
    (isDltPair_iff_exists_isLogResolution hpair hcoeff).mp hdlt
  obtain ⟨hYv, -, -⟩ := hf.toIsSmoothResolution.isNormalVariety hX
  haveI := hYv.isIntegral
  haveI := hYv.isNormal
  haveI := hYv.isLocallyNoetherian
  haveI : QuasiCompact (f ≫ sX) := hYv.1.toQuasiCompact
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  -- the snc locus `U`
  set U : X.Opens := Zc.compl with hUdef
  haveI : Nonempty U := by
    by_contra h0
    apply hZne
    rw [not_nonempty_iff] at h0
    ext x
    simp only [Closeds.coe_top, Set.mem_univ, iff_true]
    by_contra hx
    exact h0.false ⟨x, hx⟩
  have hUv : IsNormalVariety k (U.ι ≫ sX) := isNormalVariety_ι hX U
  haveI := hUv.isIntegral
  haveI := hUv.isNormal
  haveI := hUv.isLocallyNoetherian
  haveI : QuasiCompact (U.ι ≫ sX) := hUv.1.toQuasiCompact
  haveI : CompactSpace U.toScheme := QuasiCompact.compactSpace_of_compactSpace (U.ι ≫ sX)
  -- the systems on `X`, `Y` and `U`
  obtain ⟨MX, tX, hMX, hgenX, hXsys⟩ := exists_divisorialSystem sZ g sX hg D s hs hgen
  obtain ⟨MY, tY, hMY, hgenY, hYsys⟩ := exists_divisorialSystem sZ (f ≫ g) (f ≫ sX)
    (by rw [Category.assoc, hg]) D s hs hgen
  obtain ⟨MU, tU, hMU, hgenU, hUsys⟩ := exists_divisorialSystem sZ (U.ι ≫ g) (U.ι ≫ sX)
    (by rw [Category.assoc, hg]) D s hs hgen
  -- Bertini: reducedness on `X`
  obtain ⟨Ured, hUred, hred⟩ :=
    exists_dense_open_coeff_zeroDivisor_le_one k sX hX.1 hMX tX hgenX
  obtain ⟨QX, hQX0, hQX⟩ := exists_polynomial_coefficientPoint_mem Ured hUred
  -- Bertini: snc on `Y`
  haveI : LocallyOfFiniteType (f ≫ sX) := hYv.1.toLocallyOfFiniteType
  obtain ⟨SY, hSYeq, hSYsnc⟩ : ∃ S : Finset (MMP.Mori.PrimeDivisor Y),
      (⋃ E ∈ S, E.support) = ((MMP.Mori.exceptionalSet f ⊔ Θ.supp.preimage f.continuous ⊔
        Zc.preimage f.continuous : Closeds Y) : Set Y) ∧
        DivisorWithCoeffs.IsSNC (f ≫ sX) (∑ E ∈ S, Finsupp.single E (1 : ℤ)) := by
    rcases hsncY with h | ⟨S, hS, hsnc⟩
    · refine ⟨∅, by simp [h], ?_⟩
      rw [Finset.sum_empty]
      exact DivisorWithCoeffs.isSNC_zero_of_isSmoothScheme _ hf.isSmoothScheme
    · exact ⟨S, hS, hsnc⟩
  letI : Y.Over (Spec (.of k)) := ⟨f ≫ sX⟩
  haveI : IsSmoothVariety k (Y ↘ Spec (.of k)) :=
    (isSmoothVariety_iff k _).mpr ⟨hYv.1, hf.isSmoothScheme.smooth⟩
  obtain ⟨QY, hQY0, hQY⟩ := exists_polynomial_zeroDivisor_isSNC MY hMY tY hgenY SY hSYsnc
  -- Bertini: snc on `U`
  set SU := (Θ.restrictOpen U).support
  letI : U.toScheme.Over (Spec (.of k)) := ⟨U.ι ≫ sX⟩
  haveI : IsSmoothVariety k (U.toScheme ↘ Spec (.of k)) :=
    (isSmoothVariety_iff k _).mpr ⟨hUv.1, (isSmoothScheme_ι_of_le_smoothLocus hZsm).smooth⟩
  have hSU : DivisorWithCoeffs.IsSNC (U.toScheme ↘ Spec (.of k))
      (∑ E ∈ SU, Finsupp.single E (1 : ℤ)) :=
    (DivisorWithCoeffs.isSNC_iff_of_support_eq (by rw [support_sum_single])).mp hZsnc
  obtain ⟨QU, hQU0, hQU⟩ := exists_polynomial_zeroDivisor_isSNC MU hMU tU hgenU SU hSU
  -- the points to avoid
  set F : Finset Z := insert (g (genericPoint X)) (insert (g (f (genericPoint Y)))
    (insert (g (U.ι (genericPoint U.toScheme)))
      ((Θ.support.image fun P => g P.genericPoint) ∪ SY.image fun E => g (f E.genericPoint))))
  refine ⟨QX * QY * QU, F, mul_ne_zero (mul_ne_zero hQX0 hQY0) hQU0, by simp [F],
    fun P hP => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hP)))),
    fun c u hu hQ hF HX hHX W hW => ?_⟩
  have hQX' : MvPolynomial.eval c QX ≠ 0 := fun h => hQ (by simp [map_mul, h])
  have hQY' : MvPolynomial.eval c QY ≠ 0 := fun h => hQ (by simp [map_mul, h])
  have hQU' : MvPolynomial.eval c QU ≠ 0 := fun h => hQ (by simp [map_mul, h])
  have hsmem : (u : Z.totalQuotientSheaf.obj.obj (op ⊤)) ∈ lineBundleSections D ⊤ := by
    rw [hu]; exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hs j)
  have heff : IsEffective (D + MMP.Intersection.principalDivisor u) :=
    isEffective_add_principalDivisor u hsmem
  -- the member on `X`
  have hηX : g (genericPoint X) ∉ cartierSupport (D + MMP.Intersection.principalDivisor u) :=
    hF _ (by simp [F])
  obtain ⟨hτX, hWX⟩ := hXsys c u hu hηX
  have hWeq : ∀ P, W.coeff P = (MX.zeroDivisor _ hτX).coeff P := fun P => by
    rw [← (hW P).primeDivisorOrder_eq, ← ((hWX HX hHX) P).primeDivisorOrder_eq]
  have hW1 : ∀ P, W.coeff P ≤ 1 := fun P => by
    rw [hWeq]; exact hred c (hQX c hQX') hτX P
  have hW0 : ∀ P, 0 ≤ W.coeff P := fun P => by
    rw [← (hW P).primeDivisorOrder_eq]
    exact (primeDivisorOrder_nonneg_and_pos_of_isPullback g heff hHX P).1
  have hWΘ : ∀ P, W.coeff P ≠ 0 → Θ.coeff P = 0 := by
    intro P hP
    by_contra hΘ
    apply hP
    rw [← (hW P).primeDivisorOrder_eq]
    exact primeDivisorOrder_eq_zero_of_isPullback g hHX P (hF _
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_union_left _ (Finset.mem_image_of_mem _
          (Finsupp.mem_support_iff.mpr hΘ)))))))
  have hsuppX : ∀ x, x ∈ W.supp ↔ g x ∈ cartierSupport (D + MMP.Intersection.principalDivisor u) :=
    mem_supp_iff_of_isPullback g heff hHX hW
  refine ⟨hW1, hWΘ, fun a ha => ?_⟩
  have haQ : (0 : ℚ) < (a : ℚ)⁻¹ := by positivity
  set Δ' : QDivisor X := (a : ℚ)⁻¹ • Divisor.toQDivisor W with hΔ'def
  have hq : Δ'.IsQCartier :=
    MMP.Flips.QDivisor.IsQCartier.qsmul (QDivisor.isQCartier_toQDivisor hW.isCartier) _
  have hpair' : IsPairWith sX n K (Θ + Δ') :=
    ⟨hpair.1, hpair.2.1, by rw [← add_assoc]; exact hpair.2.2.add hq⟩
  have hcoeffΘ' : ∀ P, (Θ + Δ').coeff P = Θ.coeff P + (a : ℚ)⁻¹ * W.coeff P := fun P => by
    simp [hΔ'def, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul]
  have hcoeff' : ∀ P, 0 ≤ (Θ + Δ').coeff P ∧ (Θ + Δ').coeff P ≤ 1 := by
    intro P
    rw [hcoeffΘ']
    obtain ⟨h0, h1⟩ := hcoeff P
    have hw0 : (0 : ℚ) ≤ W.coeff P := by exact_mod_cast hW0 P
    have hw1 : (W.coeff P : ℚ) ≤ 1 := by exact_mod_cast hW1 P
    have ha1 : (a : ℚ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast ha)
    refine ⟨by positivity, ?_⟩
    by_cases hWP : W.coeff P = 0
    · rw [hWP]; simpa using h1
    · rw [hWΘ P hWP, zero_add]; nlinarith
  -- the member on `Y`
  have hηY : (f ≫ g) (genericPoint Y) ∉ cartierSupport (D + MMP.Intersection.principalDivisor u) :=
    hF _ (by simp [F])
  obtain ⟨hτY, hWYsys⟩ := hYsys c u hu hηY
  obtain ⟨HY, hHY⟩ := exists_isPullback (f := f ≫ g) (D := D + MMP.Intersection.principalDivisor u)
    fun ξ hξ => by rwa [eq_genericPoint_of_mem_schemeAssociatedPoints hξ]
  set WY := MY.zeroDivisor _ hτY with hWYdef
  have hWY : IsWeilDivisorOfCartier HY WY := hWYsys HY hHY
  obtain ⟨TY, hTY, -, hTYsnc⟩ := hQY c hQY' hτY
  have hsuppY : ∀ y, y ∈ WY.supp ↔
      (f ≫ g) y ∈ cartierSupport (D + MMP.Intersection.principalDivisor u) :=
    mem_supp_iff_of_isPullback (f ≫ g) heff hHY hWY
  have hpre : f ⁻¹' (W.supp : Set X) = (WY.supp : Set Y) := by
    ext y
    simp only [Set.mem_preimage, SetLike.mem_coe, hsuppX, hsuppY, Scheme.Hom.comp_apply]
  have hsuppΘ' : ((Θ + Δ').supp : Set X) = (Θ.supp : Set X) ∪ (W.supp : Set X) :=
    coe_supp_add_smul (fun P => (hcoeff P).1) hW0 haQ
  have hWYsub : WY.support ⊆ TY := fun E hE => hTY E (Finsupp.mem_support_iff.mp hE)
  have hSYsub : ∀ E : MMP.Mori.PrimeDivisor Y, E.support ⊆ ((MMP.Mori.exceptionalSet f ⊔
      Θ.supp.preimage f.continuous ⊔ Zc.preimage f.continuous : Closeds Y) : Set Y) → E ∈ SY :=
    fun E hE => mem_of_support_subset_biUnion SY E (hSYeq ▸ hE)
  have hsnc_of_sub : ∀ s' : Finset (MMP.Mori.PrimeDivisor Y), s' ⊆ TY ∪ SY →
      DivisorWithCoeffs.IsSNC (f ≫ sX) (∑ E ∈ s', Finsupp.single E (1 : ℤ)) := fun s' hs' =>
    hTYsnc.of_support_subset (by rwa [support_sum_single, support_sum_single])
  have hWYU : (⋃ E ∈ WY.support, E.support) = (WY.supp : Set Y) :=
    (DivisorWithCoeffs.coe_supp WY).symm
  have hlogres : MMP.Mori.IsLogResolution sX (QDivisor.toRDivisor (Θ + Δ')) f := by
    obtain ⟨sold, hsold⟩ := exists_finset_of_isSNCSubset hf.isSNCSubset
    refine ⟨hf.toIsSmoothResolution, hf.isPureCodimOne_exceptionalSet,
      Or.inr ⟨sold ∪ WY.support, ?_, hsnc_of_sub _ fun E hE => ?_⟩⟩
    · rw [Finset.set_biUnion_union, hsold, hWYU]
      simp only [Closeds.coe_sup, Closeds.coe_preimage, QDivisor.supp_toRDivisor, hsuppΘ',
        Set.preimage_union, hpre, Set.union_assoc]
    · rcases Finset.mem_union.mp hE with h | h
      · refine Finset.mem_union_right _ (hSYsub E fun y hy => ?_)
        have : y ∈ (⋃ E ∈ sold, E.support) := Set.mem_biUnion h hy
        rw [hsold] at this
        simp only [Closeds.coe_sup, Closeds.coe_preimage, QDivisor.supp_toRDivisor,
          Set.mem_union] at this ⊢
        exact Or.inl this
      · exact Finset.mem_union_left _ (hWYsub h)
  have hsncbig : IsSNCSubset (f ≫ sX) (MMP.Mori.exceptionalSet f ⊔
      (Θ + Δ').supp.preimage f.continuous ⊔ Zc.preimage f.continuous) := by
    refine Or.inr ⟨SY ∪ WY.support, ?_, hsnc_of_sub _ fun E hE => ?_⟩
    · rw [Finset.set_biUnion_union, hSYeq, hWYU]
      simp only [Closeds.coe_sup, Closeds.coe_preimage, hsuppΘ', Set.preimage_union, hpre]
      ext y
      simp only [Set.mem_union]
      constructor
      · rintro (((h | h) | h) | h) <;> simp [h]
      · rintro ((h | h | h) | h) <;> simp [h]
    · rcases Finset.mem_union.mp hE with h | h
      · exact Finset.mem_union_right _ h
      · exact Finset.mem_union_left _ (hWYsub h)
  have hdisc' : ∀ (hY' : IsNormalVariety k (f ≫ sX)) (E : MMP.Mori.PrimeDivisor Y),
      E.support ⊆ f ⁻¹' (Zc : Set X) → ∀ a' : ℚ,
        IsDiscrepancy sX n K (Θ + Δ') ⟨Y, f, hY', hlogres.isBirationalMorphism, E⟩ a' →
          -1 < a' := by
    intro hY' E hE a' ha'
    have hESY : E ∈ SY := hSYsub E fun y hy => by
      simp only [Closeds.coe_sup, Closeds.coe_preimage, Set.mem_union]
      exact Or.inr (hE hy)
    have hgE : g (f E.genericPoint) ∉ cartierSupport (D + MMP.Intersection.principalDivisor u) :=
      hF _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hESY)))))
    have hfE : f E.genericPoint ∉ (W.supp : Set X) := fun h => hgE ((hsuppX _).mp h)
    let E' : DivisorOver k sX := ⟨Y, f, hY', hlogres.isBirationalMorphism, E⟩
    obtain ⟨-, hB, hiff⟩ := hpair.isDiscrepancy_add_smul_iff hq E'
    obtain ⟨B', hB'⟩ := (hq.existsUnique_isPullback hB).exists
    have hB'E : B'.coeff E = 0 := by
      obtain ⟨D', hD', hpbD'⟩ := hB' a ha W (by
        ext P
        change DivisorWithCoeffs.coeff _ P = DivisorWithCoeffs.coeff _ P
        simp only [hΔ'def, DivisorWithCoeffs.coeff_smul, Divisor.coeff_toQDivisor, zsmul_eq_mul,
          Int.cast_natCast, smul_eq_mul]
        field_simp) hW.isCartier
      have h0 := coeff_eq_zero_of_isPullback hpbD' E hfE
      have h1 := congrArg (fun G : QDivisor Y => G.coeff E) hD'
      simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, h0, Int.cast_zero,
        zsmul_eq_mul, Int.cast_natCast] at h1
      exact (mul_eq_zero.mp h1.symm).resolve_left (by positivity)
    exact hdisc hY' E hE a' (((hiff B' hB').1 a').mp (by rwa [hB'E, sub_zero]))
  have hsncU : ((Θ + Δ').restrictOpen U).IsSNC (U.ι ≫ sX) := by
    have hηU : (U.ι ≫ g) (genericPoint U.toScheme) ∉
        cartierSupport (D + MMP.Intersection.principalDivisor u) := hF _ (by simp [F])
    obtain ⟨hτU, hWUsys⟩ := hUsys c u hu hηU
    obtain ⟨HU, hHU⟩ := exists_isPullback (f := U.ι ≫ g)
      (D := D + MMP.Intersection.principalDivisor u)
      fun ξ hξ => by rwa [eq_genericPoint_of_mem_schemeAssociatedPoints hξ]
    obtain ⟨TU, hTU, -, hTUsnc⟩ := hQU c hQU' hτU
    refine hTUsnc.of_support_subset fun E hE => ?_
    rw [support_sum_single, Finset.mem_union]
    rw [Finsupp.mem_support_iff] at hE
    change ((Θ + Δ').restrictOpen U).coeff E ≠ 0 at hE
    rw [DivisorWithCoeffs.coeff_restrictOpen, hcoeffΘ'] at hE
    by_cases hΘE : Θ.coeff (OpenWeilRestriction.primeDivisorMap U.ι E) = 0
    · left
      apply hTU E
      change (MU.zeroDivisor (∑ i, scalarsToGlobalSections k (U.ι ≫ sX) (c i) • tU i) hτU).coeff E
        ≠ 0
      rw [← ((hWUsys HU hHU) E).primeDivisorOrder_eq,
        primeDivisorOrder_restrict_eq U g hHX hHU E, (hW _).primeDivisorOrder_eq]
      intro h0
      apply hE
      rw [hΘE, h0]
      simp
    · right
      rw [Finsupp.mem_support_iff]
      change (Θ.restrictOpen U).coeff E ≠ 0
      rw [DivisorWithCoeffs.coeff_restrictOpen]
      exact hΘE
  exact (isDltPair_iff_exists_isLogResolution hpair' hcoeff').mpr
    ⟨Zc, hZne, hZsm, hsncU, Y, f, hlogres, hpure, hsncbig, hdisc'⟩

end DltMain

end

open MMP.Intersection in
/-- **The Serre input.** For `g = f ∘ νᵢ` and a `g`-free Cartier divisor `E` on `Tᵢ`, there is
`M > 0` such that `aE + g^*H` is free over the base field for every effective `H ∼ (atM)A`,
`a, t > 0`: the nonvanishing loci of sections of the multiples of the ample `A` form a basis of
the topology of `Z`. -/
private theorem exists_isRelativelyFreeCartier_twist
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {T Z : Scheme.{u}} [IsLocallyNoetherian T] {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    (N : NormalizationComponents sT hT) {n : ℕ} {Δ : QWeilDivisor T}
    {Θ : ∀ i, QDivisor (N.X i)} (hΔ : IsSdltAdjointPair N n Δ Θ)
    (sZ : Z ⟶ Spec (.of k)) [IsIntegral Z] (hZ : IsProjectiveMorphism sZ)
    (f : T ⟶ Z) (hf : f ≫ sZ = sT) {A : Z.CartierDivisor} (hAb : IsNvBasis A) (i : N.ι)
    {E : (N.X i).CartierDivisor} (hE : IsRelativelyFreeCartier (N.n i ≫ f) E) :
    ∃ M : ℕ, 0 < M ∧ ∀ (a t : ℕ) (H : Z.CartierDivisor) (HN : (N.X i).CartierDivisor), 0 < a →
      0 < t → MMP.Intersection.IsEffective H →
      MMP.Intersection.LinearlyEquivalent H ((a * t * M) • A) →
      IsPullback (N.n i ≫ f) H HN → IsRelativelyFreeCartier (N.n i ≫ sT) (a • E + HN) := by
  haveI : QuasiCompact (N.n i ≫ sT) := (N.isNormalVariety i).1.toQuasiCompact
  haveI : CompactSpace (N.X i) := QuasiCompact.compactSpace_of_compactSpace (N.n i ≫ sT)
  haveI : IsProper sZ := isProper_of_isProjectiveMorphism sZ hZ
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  exact exists_isRelativelyFreeCartier_twist_of_isNvBasis (N.n i ≫ sT) (N.n i ≫ f) hAb hE

open MMP.Intersection in
/-- **Serre generation for one relative adjoint.** Let `D` on `Tᵢ` be semiample over `Z` and `A`
ample on `Z`. There is `M` such that for all `a > 0` and `c ≥ aM`, every `D'` with
`D' = D + a⁻¹ (f ∘ νᵢ)^*H`, `H ∼ cA`, is globally semiample: twisting the coherent sheaf
`(f ∘ νᵢ)_* 𝒪(rD)` by `𝒪_Z(jA)`, `j ≥ M`, makes it globally generated, the relative evaluation
map then shows that `r(D + (f ∘ νᵢ)^* jA)` is globally generated, and powers and products of
globally generated invertible sheaves are globally generated. -/
private theorem exists_twist_isRelativelySemiample
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {T Z : Scheme.{u}} [IsLocallyNoetherian T] {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    (N : NormalizationComponents sT hT) {n : ℕ} {Δ : QWeilDivisor T}
    {Θ : ∀ i, QDivisor (N.X i)} (hΔ : IsSdltAdjointPair N n Δ Θ)
    (sZ : Z ⟶ Spec (.of k)) [IsIntegral Z] (hZ : IsProjectiveMorphism sZ)
    (f : T ⟶ Z) (hf : f ≫ sZ = sT) {A : Z.CartierDivisor} (hAb : IsNvBasis A) (i : N.ι)
    {D : QDivisor (N.X i)} (hD : QDivisor.IsRelativelySemiample (N.n i ≫ f) D) :
    ∃ M : ℕ, 0 < M ∧ ∀ (a t : ℕ) (H : Z.CartierDivisor) (HN : (N.X i).CartierDivisor)
      (D' : QDivisor (N.X i)), 0 < a → 0 < t → MMP.Intersection.IsEffective H →
      MMP.Intersection.LinearlyEquivalent H ((a * t * M) • A) → IsPullback (N.n i ≫ f) H HN →
      (∀ P, D'.coeff P = D.coeff P + (a : ℚ)⁻¹ * primeDivisorOrder P HN) →
      QDivisor.IsRelativelySemiample (N.n i ≫ sT) D' := by
  classical
  haveI : QuasiCompact (N.n i ≫ sT) := (N.isNormalVariety i).1.toQuasiCompact
  haveI : CompactSpace (N.X i) := QuasiCompact.compactSpace_of_compactSpace (N.n i ≫ sT)
  haveI : IsNoetherian (N.X i) := ⟨⟩
  obtain ⟨C, hC, q, hq, hint, hfree⟩ := hD
  obtain ⟨M, hM0, hM⟩ := exists_isRelativelyFreeCartier_twist N hΔ sZ hZ f hf hAb i hfree
  refine ⟨M, hM0, fun a t H HN D' ha ht hHe hlin hHN hD' => ?_⟩
  obtain ⟨B, hEB⟩ := MMP.Intersection.exists_isWeilDivisorOfCartier
    (KCartierDivisor.realization ((q : ℚ) • C) hint)
  obtain ⟨W, hW⟩ := MMP.Intersection.exists_isWeilDivisorOfCartier HN
  have hlin' : MMP.Intersection.LinearlyEquivalent (q • H) ((a * (q * t) * M) • A) := by
    have := (MMP.Intersection.principalSubgroup Z).nsmul_mem hlin q
    unfold MMP.Intersection.LinearlyEquivalent
    rw [show a * (q * t) * M = q * (a * t * M) by ring]
    simpa [smul_sub, mul_smul] using this
  have hfr := hM a (q * t) (q • H) (q • HN) ha (Nat.mul_pos hq ht)
    (hHe.nsmul q) hlin' (isPullback_nsmul hHN q)
  have hw : ∀ P : MMP.Mori.PrimeDivisor (N.X i), (a • B + q • W).coeff P =
      a * B.coeff P + q * W.coeff P := fun P => by
    simp [DivisorWithCoeffs.coeff_apply, nsmul_eq_mul]
  have hEW : IsWeilDivisorOfCartier
      (a • KCartierDivisor.realization ((q : ℚ) • C) hint + q • HN) (a • B + q • W) := fun Q => by
    have h := isOrderAlong_primeDivisorOrder
      (a • KCartierDivisor.realization ((q : ℚ) • C) hint + q • HN) Q
    have e : primeDivisorOrder Q (a • KCartierDivisor.realization ((q : ℚ) • C) hint + q • HN) =
        (a • B + q • W).coeff Q := by
      rw [map_add, map_nsmul, map_nsmul, (hEB Q).primeDivisorOrder_eq,
        (hW Q).primeDivisorOrder_eq, hw, nsmul_eq_mul, nsmul_eq_mul]
    rwa [e] at h
  refine QDivisor.isRelativelySemiample_of_isRelativelyFreeCartier _ D' (q * a)
    (Nat.mul_pos hq ha) (a • B + q • W) (fun P => ?_) _ hEW hfr
  have e1 := coeff_eq_mul_of_isWeilDivisorOfCartier_realization hC hint hEB P
  have e2 : (W.coeff P : ℚ) = primeDivisorOrder P HN := by rw [(hW P).primeDivisorOrder_eq]
  have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
  rw [hw, hD' P]
  push_cast
  rw [e1, e2]
  field_simp

open MMP.Intersection in
/-- **Serre generation for the relative adjoints.** There are an ample effective Cartier divisor
`A` on `Z` and `N > 0` such that, for every effective `H ∼ aN·A` with pull-backs `(f ∘ νᵢ)^*H`,
every `K_{Tᵢ} + Θᵢ + a⁻¹ (f ∘ νᵢ)^*H` is globally semiample and nef: twisting the coherent
sheaves `(f ∘ νᵢ)_* 𝒪(rLᵢ)` by `𝒪_Z(rNA)` makes them globally generated, and the relative
evaluation maps then show that `r(Lᵢ + (f ∘ νᵢ)^*NA)` is globally generated. -/
private theorem exists_semiampleTwistData
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {T Z : Scheme.{u}} [IsLocallyNoetherian T] {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    (N : NormalizationComponents sT hT) {n : ℕ} {Δ : QWeilDivisor T}
    {Θ : ∀ i, QDivisor (N.X i)} (hΔ : IsSdltAdjointPair N n Δ Θ)
    (sZ : Z ⟶ Spec (.of k)) [IsIntegral Z] (hZ : IsProjectiveMorphism sZ)
    (f : T ⟶ Z) (hf : f ≫ sZ = sT)
    (hL : ∀ (i : N.ι) (K : Divisor (N.X i)), K.IsCanonicalDivisor (N.n i ≫ sT) n →
      QDivisor.IsRelativelySemiample (N.n i ≫ f) (Divisor.toQDivisor K + Θ i)) :
    ∃ (A : Z.CartierDivisor) (M : ℕ), 0 < M ∧ MMP.Intersection.IsEffective A ∧
      KCartierDivisor.IsRelativelyAmpleQ sZ (KCartierDivisor.ofCartier ℚ A) ∧
      Stacks.Ample.IsAmple Z (MMP.CartierDivisor.sheaf A) ∧
      ∀ (a : ℕ) (H : Z.CartierDivisor) (HN : ∀ i, (N.X i).CartierDivisor)
        (Θ' : ∀ i, QDivisor (N.X i)), 0 < a → MMP.Intersection.IsEffective H →
        MMP.Intersection.LinearlyEquivalent H ((a * M : ℕ) • A) →
        (∀ i, IsPullback (N.n i ≫ f) H (HN i)) →
        (∀ i P, (Θ' i).coeff P = (Θ i).coeff P + (a : ℚ)⁻¹ * primeDivisorOrder P (HN i)) →
        ∀ (i : N.ι) (K : Divisor (N.X i)), K.IsCanonicalDivisor (N.n i ≫ sT) n →
          QDivisor.IsRelativelySemiample (N.n i ≫ sT) (Divisor.toQDivisor K + Θ' i) := by
  classical
  haveI := finite_ι_of_isSdltAdjointPair N hΔ
  haveI : Fintype N.ι := Fintype.ofFinite _
  obtain ⟨A, hAe, hA, hAamp⟩ := exists_isEffective_isRelativelyAmpleQ sZ hZ
  have hAb : IsNvBasis A := isNvBasis_of_isAmple A hAamp
  have hK0 : ∀ i, ∃ K : Divisor (N.X i), K.IsCanonicalDivisor (N.n i ≫ sT) n := fun i => by
    obtain ⟨K, hK⟩ := hΔ.exists_isDltPair i
    exact ⟨K, hK.1.2.1⟩
  choose K₀ hK₀ using hK0
  choose M hM using fun i =>
    exists_twist_isRelativelySemiample N hΔ sZ hZ f hf hAb i (hL i (K₀ i) (hK₀ i))
  refine ⟨A, ∏ i, M i, Finset.prod_pos fun i _ => (hM i).1, hAe, hA, hAamp,
    fun a H HN Θ' ha hHe hlin hHN hΘ' i K hK => ?_⟩
  haveI : QuasiCompact (N.n i ≫ sT) := (N.isNormalVariety i).1.toQuasiCompact
  haveI : CompactSpace (N.X i) := QuasiCompact.compactSpace_of_compactSpace (N.n i ≫ sT)
  haveI : PerfectField k := PerfectField.ofCharZero
  obtain ⟨φ, hφ⟩ := MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor (N.n i ≫ sT)
    (N.isNormalVariety i) hK (hK₀ i)
  have hprod : (a * ∏ j, M j : ℕ) = a * (∏ j ∈ Finset.univ.erase i, M j) * M i := by
    rw [mul_assoc, Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  have ht : 0 < ∏ j ∈ Finset.univ.erase i, M j := Finset.prod_pos fun j _ => (hM j).1
  have h1 := (hM i).2 a _ H (HN i) (Divisor.toQDivisor (K₀ i) + Θ' i) ha ht hHe
    (hprod ▸ hlin) (hHN i) (fun P => by
      rw [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_add, hΘ' i P]; ring)
  have h2 := h1.add_principalDivisor φ
  have e : Divisor.toQDivisor K + Θ' i =
      Divisor.toQDivisor (K₀ i) + Θ' i + Divisor.toQDivisor (principalDivisor φ) := by
    rw [← hφ, map_sub]; abel
  rw [e]
  exact h2

open MMP.Intersection in
/-- Along a prime divisor `P` of `Tᵢ`, the order of `(f ∘ νᵢ)^*H` is the order of `f^*H` along
the prime divisor `νᵢ(P)` of `T`, when the latter is a prime Weil divisor. -/
private theorem primeDivisorOrder_comp_eq
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {T Z : Scheme.{u}} [IsLocallyNoetherian T] {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    (N : NormalizationComponents sT hT) {n : ℕ} {Δ : QWeilDivisor T}
    {Θ : ∀ i, QDivisor (N.X i)} (hΔ : IsSdltAdjointPair N n Δ Θ)
    (sZ : Z ⟶ Spec (.of k)) [IsIntegral Z] (hZ : IsProjectiveMorphism sZ)
    (f : T ⟶ Z) (hf : f ≫ sZ = sT)
    {H : Z.CartierDivisor} (hH : MMP.Intersection.IsEffective H) {HT : T.CartierDivisor}
    {HN : ∀ i, (N.X i).CartierDivisor} (hHT : IsPullback f H HT)
    (hHN : ∀ i, IsPullback (N.n i ≫ f) H (HN i)) (i : N.ι) (P : MMP.Mori.PrimeDivisor (N.X i))
    (Γ : WeilDivisorPrime T) (hP : (N.n i).base P.genericPoint = Γ.1.genericPoint) :
    primeDivisorOrder P (HN i) = primeDivisorOrder Γ.1 HT := by
  haveI : CompactSpace T := compactSpace_of_isProjectiveMorphism hΔ.isProjectiveMorphism
  haveI : IsNoetherian T := ⟨⟩
  haveI : IsReduced T := hΔ.isBoundary.2.1
  haveI : LocallyOfFiniteType sT := hΔ.isNFold.1.2.1
  obtain ⟨W, hfW, h, hu, hloc⟩ := hH (f ((N.n i) P.genericPoint))
  have hW' : (N.n i ≫ f) P.genericPoint ∈ W := hfW
  have hne := germ_ne_zero_of_isPullback (N.n i ≫ f) (hHN i) hu hloc hW'
  rw [primeDivisorOrder_eq_ord_of_isPullback (N.n i ≫ f) (hHN i) hu hloc P hW' hne,
    scheme_ord_algebraMap P.coheight_genericPoint hne]
  have key : ∀ (y : T) (hy : (N.n i) P.genericPoint = y) (hyW : f y ∈ W),
      (∃ _ : IsDomain (T.presheaf.stalk y), IsDiscreteValuationRing (T.presheaf.stalk y)) →
      T.presheaf.germ (f ⁻¹ᵁ W) y hyW (f.app W h) ∈ nonZeroDivisors _ ∧
      (Ring.ord _ (T.presheaf.germ (f ⁻¹ᵁ W) y hyW (f.app W h))).toNat =
        (Ring.ord _ ((N.X i).presheaf.germ ((N.n i ≫ f) ⁻¹ᵁ W) P.genericPoint hW'
          ((N.n i ≫ f).app W h))).toNat := by
    intro y hy hyW hdvr
    subst hy
    obtain ⟨hdom, hdvr⟩ := hdvr
    haveI := isIso_stalkMap_normalizationComponents N i P.genericPoint
    let e := (asIso ((N.n i).stalkMap P.genericPoint)).commRingCatIsoToRingEquiv
    have e1 : (N.X i).presheaf.germ ((N.n i ≫ f) ⁻¹ᵁ W) P.genericPoint hW' ((N.n i ≫ f).app W h) =
        e (T.presheaf.germ (f ⁻¹ᵁ W) _ hyW (f.app W h)) := by
      change _ = (N.n i).stalkMap P.genericPoint _
      exact (Scheme.Hom.germ_stalkMap_apply (N.n i) (f ⁻¹ᵁ W) P.genericPoint hyW
        (f.app W h)).symm
    refine ⟨mem_nonZeroDivisors_of_ne_zero fun h0 => hne ?_, ?_⟩
    · rw [e1, h0, map_zero]
    · rw [e1, ← Ring.ord_ringEquiv]
  obtain ⟨hnz, hord⟩ := key _ hP (hP ▸ hfW) Γ.2
  rw [primeDivisorOrder_eq_ord_toNat f hHT hu hloc Γ.1 (hP ▸ hfW) hnz, hord]

/-- A normalization component maps the generic point of a prime divisor to a point of coheight at
most one: `νᵢ` is finite, so the residue field extension at the generic point is algebraic, and
the dimension formula on `T` (pure of dimension `n`) bounds the coheight. -/
private theorem coheight_map_genericPoint_le_one
    {k : Type u} [Field k] {T : Scheme.{u}} [IsLocallyNoetherian T] {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    (N : NormalizationComponents sT hT) {n : ℕ} {Δ : QWeilDivisor T}
    {Θ : ∀ i, QDivisor (N.X i)} (hΔ : IsSdltAdjointPair N n Δ Θ) (i : N.ι)
    (P : MMP.Mori.PrimeDivisor (N.X i)) :
    Order.coheight ((N.n i).base P.genericPoint) ≤ 1 := by
  haveI : CompactSpace T := compactSpace_of_isProjectiveMorphism hΔ.isProjectiveMorphism
  haveI : LocallyOfFiniteType sT := hΔ.isNFold.1.2.1
  haveI : IsNoetherian T := ⟨⟩
  haveI : LocallyOfFiniteType (N.n i ≫ sT) := (N.isNormalVariety i).1.toLocallyOfFiniteType
  set Q := (N.n i).base P.genericPoint with hQ
  have hdimX : topologicalKrullDim (N.X i) = n := by
    obtain ⟨K, hK⟩ := hΔ.exists_isDltPair i
    exact hK.1.2.1.1
  have h1 := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight (N.n i ≫ sT)
    P.genericPoint
  rw [P.coheight_genericPoint, hdimX] at h1
  have h2 := topologicalKrullDim_closure_singleton_eq_trdeg k (N.X i) (N.n i ≫ sT) P.genericPoint
  have h3 := MMP.Flips.trdeg_residueField_add (N.n i ≫ sT) sT (N.n i) rfl P.genericPoint
  letI := ((N.n i).residueFieldMap P.genericPoint).hom.toAlgebra
  have h4 : Algebra.trdeg (T.residueField Q) ((N.X i).residueField P.genericPoint) = 0 :=
    trdeg_eq_zero_iff.mpr (isAlgebraic_residueFieldMap_normalizationComponents N i P.genericPoint)
  rw [h4, add_zero] at h3
  have h5 := topologicalKrullDimAt_eq_trdeg_add_krullDim_stalk k T sT Q
  have h6 := _root_.topologicalKrullDimAt_le_topologicalKrullDim (X := T) Q
  have h7 : topologicalKrullDim T ≤ n :=
    MMP.Flips.topologicalKrullDim_le_of_forall_mem_irreducibleComponents fun Z hZ =>
      (hΔ.isNFold.2.2 Z hZ).le
  rw [ringKrullDim_stalk_eq_coheight] at h5
  rw [h3] at h5
  obtain ⟨e, he2, he5⟩ : ∃ e : ℕ∞,
      topologicalKrullDim (closure {P.genericPoint} : Set (N.X i)) = e ∧
      topologicalKrullDimAt T Q = (e : WithBot ℕ∞) + (Order.coheight Q : WithBot ℕ∞) :=
    ⟨_, h2, h5⟩
  have he1 : (e : WithBot ℕ∞) + ((1 : ℕ∞) : WithBot ℕ∞) = (n : WithBot ℕ∞) := by
    rwa [← he2]
  have hle : (e : WithBot ℕ∞) + (Order.coheight Q : WithBot ℕ∞) ≤ n := he5 ▸ h6.trans h7
  have he1' : e + 1 = (n : ℕ∞) := by exact_mod_cast he1
  have hle' : e + Order.coheight Q ≤ n := by exact_mod_cast hle
  have hetop : e ≠ ⊤ := fun h => by simp [h] at he1'
  rw [← he1'] at hle'
  exact (WithTop.add_le_add_iff_left hetop).mp hle'

open MMP.Intersection in
/-- A prime divisor of `Tᵢ` along which `(f ∘ νᵢ)^*H` has non-zero order, with `H` missing the
image of the double locus, lies over a prime Weil divisor of `T`. -/
private theorem exists_weilDivisorPrime_of_primeDivisorOrder_ne_zero
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {T Z : Scheme.{u}} [IsLocallyNoetherian T] {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    (N : NormalizationComponents sT hT) {n : ℕ} {Δ : QWeilDivisor T}
    {Θ : ∀ i, QDivisor (N.X i)} (hΔ : IsSdltAdjointPair N n Δ Θ)
    (sZ : Z ⟶ Spec (.of k)) [IsIntegral Z] (hZ : IsProjectiveMorphism sZ)
    (f : T ⟶ Z) (hf : f ≫ sZ = sT)
    {H : Z.CartierDivisor} (hH : MMP.Intersection.IsEffective H)
    (hD : ∀ (i : N.ι) (P : MMP.Mori.PrimeDivisor (N.X i)),
      (N.n i).base P.genericPoint ∈ (doubleIntersectionLocus T : Set T) →
      f ((N.n i).base P.genericPoint) ∉ cartierSupport H)
    {HT : T.CartierDivisor} (hHT : IsPullback f H HT)
    {HN : ∀ i, (N.X i).CartierDivisor} (hHN : ∀ i, IsPullback (N.n i ≫ f) H (HN i)) (i : N.ι)
    (P : MMP.Mori.PrimeDivisor (N.X i)) (hP : primeDivisorOrder P (HN i) ≠ 0) :
    ∃ Γ : WeilDivisorPrime T, (N.n i).base P.genericPoint = Γ.1.genericPoint := by
  haveI : CompactSpace T := compactSpace_of_isProjectiveMorphism hΔ.isProjectiveMorphism
  haveI : LocallyOfFiniteType sT := hΔ.isNFold.1.2.1
  haveI : IsNoetherian T := ⟨⟩
  haveI : LocallyOfFiniteType (N.n i ≫ sT) := (N.isNormalVariety i).1.toLocallyOfFiniteType
  set Q := (N.n i).base P.genericPoint with hQ
  have hc1 : Order.coheight Q ≤ 1 := coheight_map_genericPoint_le_one N hΔ i P
  have hQD : Q ∉ (doubleIntersectionLocus T : Set T) := fun hm =>
    hP (primeDivisorOrder_eq_zero_of_isPullback (N.n i ≫ f) (hHN i) P
      (by simpa using hD i P hm))
  have hc0 : Order.coheight Q ≠ 0 := by
    intro h0
    have hmax : IsMax Q := Order.coheight_eq_zero.mp h0
    obtain ⟨Z, hZ, hQZ⟩ :=
      exists_mem_irreducibleComponents_subset_of_isIrreducible _ (isIrreducible_singleton (x := Q))
    have hZc : IsClosed Z := isClosed_of_mem_irreducibleComponents Z hZ
    have hξ : IsGenericPoint hZ.1.genericPoint Z := by
      simpa [hZc.closure_eq] using hZ.1.isGenericPoint_genericPoint_closure
    have hle : Q ≤ hZ.1.genericPoint :=
      Scheme.le_iff_specializes.mpr (hξ.specializes (hQZ rfl))
    have heq : hZ.1.genericPoint = Q :=
      ((Scheme.le_iff_specializes.mp hle).antisymm (Scheme.le_iff_specializes.mp (hmax hle))).eq
    have hass := mem_schemeAssociatedPoints_of_isGenericPoint_irreducibleComponent T hZ
      (heq ▸ hξ)
    exact hP (primeDivisorOrder_eq_zero_of_isPullback (N.n i ≫ f) (hHN i) P (hHT.1 Q hass))
  have hcoh : Order.coheight Q = 1 := le_antisymm hc1 (Order.one_le_iff_ne_zero.mpr hc0)
  have hreg : IsRegularLocalRing (T.presheaf.stalk Q) := by
    by_contra hnr
    exact hQD (subset_closure ⟨hcoh, hnr⟩)
  have hdim1 : ringKrullDim (T.presheaf.stalk Q) = 1 := by
    rw [ringKrullDim_stalk_eq_coheight, hcoh]; rfl
  obtain ⟨hdom, hdvr⟩ := MMP.Resolution.Kollar.isDiscreteValuationRing_of_ringKrullDim_eq_one hdim1
  have hg := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne Q hcoh
  refine ⟨⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne Q hcoh, ?_⟩, hg.symm⟩
  have key : ∀ (y : T), (AlgebraicGeometry.PrimeDivisor.ofCoheightOne Q hcoh).genericPoint = y →
      (∃ _ : IsDomain (T.presheaf.stalk y), IsDiscreteValuationRing (T.presheaf.stalk y)) →
      ∃ _ : IsDomain (T.presheaf.stalk
        (AlgebraicGeometry.PrimeDivisor.ofCoheightOne Q hcoh).genericPoint),
        IsDiscreteValuationRing (T.presheaf.stalk
          (AlgebraicGeometry.PrimeDivisor.ofCoheightOne Q hcoh).genericPoint) := by
    intro y hy h
    subst hy
    exact h
  exact key Q hg ⟨hdom, hdvr⟩

open MMP.Intersection in
/-- On a Noetherian scheme only finitely many prime divisors have their generic point in the
support of a Cartier divisor. -/
private theorem finite_genericPoint_mem_cartierSupport {T : Scheme.{u}} [IsLocallyNoetherian T]
    [CompactSpace T] (D : T.CartierDivisor) :
    {P : MMP.Mori.PrimeDivisor T | P.genericPoint ∈ cartierSupport D}.Finite := by
  haveI : IsNoetherian T := ⟨⟩
  exact MMP.Mori.finite_setOf_genericPoint_mem (S := T) (isClosed_cartierSupport D)
    (fun s hs h0 => by
      have : Ring.KrullDimLE 0 (T.presheaf.stalk s) := krullDimLE_of_coheight_le (by simp [h0])
      have : IsArtinianRing (T.presheaf.stalk s) := isArtinianRing_iff_krullDimLE_zero.mpr this
      exact notMem_cartierSupport_of_isArtinianRing D s hs)

open MMP.Intersection in
/-- Only finitely many prime Weil divisors of `T` have non-zero order in a Cartier divisor. -/
private theorem finite_primeDivisorOrder_ne_zero {T : Scheme.{u}} [IsLocallyNoetherian T]
    [CompactSpace T] (D : T.CartierDivisor) :
    {Γ : WeilDivisorPrime T | primeDivisorOrder Γ.1 D ≠ 0}.Finite := by
  have h2 : ((fun Γ : WeilDivisorPrime T => Γ.1) ⁻¹'
      {P : MMP.Mori.PrimeDivisor T | P.genericPoint ∈ cartierSupport D}).Finite :=
    (finite_genericPoint_mem_cartierSupport D).preimage (fun _ _ _ _ h => Subtype.ext h)
  refine h2.subset ?_
  intro Γ hΓ
  by_contra h
  have hg : (primeDivisorSubvariety Γ.1).genericPoint = Γ.1.genericPoint := rfl
  refine hΓ ((isOrderAlong_primeDivisorOrder D Γ.1).eq_zero_of_not_subset fun h' => h ?_)
  show Γ.1.genericPoint ∈ cartierSupport D
  rw [← hg]
  exact genericPoint_mem_cartierSupport_iff.mpr h'

open scoped Classical in
/-- The coefficient sum of `adjointBoundaryCoeff` picks out the coefficient of the unique prime
Weil divisor with a given generic point. -/
private theorem sum_ite_genericPoint_eq {T : Scheme.{u}} (D : QWeilDivisor T)
    (Γ₀ : WeilDivisorPrime T) {x : T} (hx : x = Γ₀.1.genericPoint) :
    (∑ Γ ∈ D.support, if x = Γ.1.genericPoint then D Γ else 0) = D Γ₀ := by
  rw [Finset.sum_eq_single Γ₀]
  · rw [if_pos hx]
  · intro Γ _ hne
    rw [if_neg]
    intro h
    exact hne (Subtype.ext (PrimeDivisor.genericPoint_injective (h.symm.trans hx)))
  · intro h
    rw [Finsupp.notMem_support_iff.mp h, ite_self]

open scoped Classical in
private theorem sum_ite_genericPoint_eq_zero {T : Scheme.{u}} (D : QWeilDivisor T) {x : T}
    (hx : ∀ Γ : WeilDivisorPrime T, x ≠ Γ.1.genericPoint) :
    (∑ Γ ∈ D.support, if x = Γ.1.genericPoint then D Γ else 0) = 0 :=
  Finset.sum_eq_zero fun Γ _ => if_neg (hx Γ)

open MMP.Mori MMP.Fourfold in
/-- **Transport of a residue presentation to the twisted generator.** If `(V, a, g, ε)` presents
the residue of `s` along `P`, then on `V' ⊆ V`, for a unit `u` on `V'` whose pull-back is `φ` at
the generic point of `P`, `(V', a|_{V'}, g^a u^{-m}, ε^a)` presents the residue of
`φ^{-m} s^a` along `P`. -/
private theorem isLogResiduePresentation_twist {k : Type u} [Field k] {T : Scheme.{u}}
    {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    (N : NormalizationComponents sT hT) {n m : ℕ} (a : ℕ) {i : N.ι}
    {P : MMP.Mori.PrimeDivisor (N.X i)} {V V' : T.Opens} (hV : V' ≤ V)
    {hP : (N.n i).base P.genericPoint ∈ V} (hP' : (N.n i).base P.genericPoint ∈ V')
    {av : Fin (n - 1) → Γ(T, V)} {g : Γ(T, V)} {ε : ℤ} {s : RationalPluriForms (N.n i ≫ sT) n m}
    (hs : IsLogResiduePresentation N n m i P V hP av g ε s)
    (b : letI := functionFieldAlgebra (N.n i ≫ sT)
      Module.Basis Unit (N.X i).functionField
        (⋀[(N.X i).functionField]^n Ω[(N.X i).functionField⁄k]))
    {u : Γ(T, V')} (hu : IsUnit u) {φ : (N.X i).functionField}
    (hφ : algebraMap _ (N.X i).functionField ((N.X i).presheaf.germ ((N.n i) ⁻¹ᵁ V')
      P.genericPoint hP' ((N.n i).app V' u)) = φ) :
    IsLogResiduePresentation N n (m * a) i P V' hP'
      (fun j => T.presheaf.map (homOfLE hV).op (av j))
      (T.presheaf.map (homOfLE hV).op g ^ a * ((hu.unit⁻¹ : Γ(T, V')ˣ) : Γ(T, V')) ^ m)
      (ε ^ a) (φ⁻¹ ^ m • formPow b m a s) := by
  unfold IsLogResiduePresentation at hs ⊢
  obtain ⟨z, h0, hz, hseq, hda, hres⟩ := hs
  have R1 : ∀ t : Γ(T, V), (N.X i).presheaf.germ ((N.n i) ⁻¹ᵁ V') P.genericPoint hP'
      ((N.n i).app V' (T.presheaf.map (homOfLE hV).op t)) =
      (N.X i).presheaf.germ ((N.n i) ⁻¹ᵁ V) P.genericPoint hP ((N.n i).app V t) := by
    intro t
    rw [← Scheme.Hom.germ_stalkMap_apply, ← Scheme.Hom.germ_stalkMap_apply,
      TopCat.Presheaf.germ_res_apply]
  set w := (N.X i).presheaf.germ ((N.n i) ⁻¹ᵁ V') P.genericPoint hP' ((N.n i).app V' u) with hw_def
  set wInv := (N.X i).presheaf.germ ((N.n i) ⁻¹ᵁ V') P.genericPoint hP'
      ((N.n i).app V' ((hu.unit⁻¹ : Γ(T, V')ˣ) : Γ(T, V'))) with hwInv_def
  have hmul : wInv * w = 1 := by
    simpa only [map_mul, map_one, IsUnit.unit_spec] using congrArg (fun t =>
      (N.X i).presheaf.germ ((N.n i) ⁻¹ᵁ V') P.genericPoint hP' ((N.n i).app V' t)) hu.unit.inv_mul
  have hφinv : algebraMap _ (N.X i).functionField wInv = φ⁻¹ := by
    rw [← hφ]
    exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, hmul, map_one])
  dsimp only
  refine ⟨z, h0 ^ a * wInv ^ m, hz, ?_, ?_, ?_⟩
  · rw [hseq]
    simp only [R1]
    unfold formPow
    rw [linePow_smul, linePow_tprod]
    simp only [smul_smul, map_mul, map_pow, hφinv, mul_comm]
    exact (mul_smul _ _ _).symm
  · simp only [R1]
    exact hda
  · simp only [map_mul, map_pow, R1]
    rw [← hwInv_def, hres]
    push_cast
    ring

open MMP.Intersection in
/-- **Local generators of the twisted adjoint.** If `H` is effective and misses the image of the
double locus, and `a > 0`, the twisted pair `(T, Δ'; Θ')` with `Θ'ᵢ = Θᵢ + a⁻¹ (f ∘ νᵢ)^*H`
again has local generators of `𝒪_T(m'(K_T + Δ'))` with the residue identification and with
residues along the conductor pulled back from `T`, for some `m' > 0` with `m'Δ'` integral. Near a
double point the twisting function is the pull-back of a unit of `T`, so both residue clauses
survive the twist (`isLogResiduePresentation_twist`). -/
private theorem exists_isAdjointGeneratorOn_twist
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {T Z : Scheme.{u}} [IsLocallyNoetherian T] {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    (N : NormalizationComponents sT hT) {n : ℕ} {Δ : QWeilDivisor T}
    {Θ : ∀ i, QDivisor (N.X i)} (hΔ : IsSdltAdjointPair N n Δ Θ)
    (sZ : Z ⟶ Spec (.of k)) [IsIntegral Z] (hZ : IsProjectiveMorphism sZ)
    (f : T ⟶ Z) (hf : f ≫ sZ = sT)
    {H : Z.CartierDivisor} (hH : MMP.Intersection.IsEffective H)
    (hD : ∀ (i : N.ι) (P : MMP.Mori.PrimeDivisor (N.X i)),
      (N.n i).base P.genericPoint ∈ (doubleIntersectionLocus T : Set T) →
      f ((N.n i).base P.genericPoint) ∉ cartierSupport H)
    {HT : T.CartierDivisor} {HN : ∀ i, (N.X i).CartierDivisor} (hHT : IsPullback f H HT)
    (hHN : ∀ i, IsPullback (N.n i ≫ f) H (HN i)) {a : ℕ} (ha : 0 < a)
    {Δ' : QWeilDivisor T} {Θ' : ∀ i, QDivisor (N.X i)}
    (hΔ' : ∀ Γ, Δ' Γ = Δ Γ + (a : ℚ)⁻¹ * primeDivisorOrder Γ.1 HT)
    (hΘ' : ∀ i P, (Θ' i).coeff P = (Θ i).coeff P + (a : ℚ)⁻¹ * primeDivisorOrder P (HN i)) :
    ∃ m : ℕ, 0 < m ∧ (∀ Γ, ((m : ℚ) * Δ' Γ).den = 1) ∧
      ∀ x : T, ∃ (U : T.Opens) (_ : x ∈ U) (s : ∀ i, RationalPluriForms (N.n i ≫ sT) n m),
        IsAdjointGeneratorOn N n m Θ' U s ∧
          ∀ i (P : MMP.Mori.PrimeDivisor (N.X i)), (N.n i).base P.genericPoint ∈ U →
            (N.n i).base P.genericPoint ∈ (doubleIntersectionLocus T : Set T) →
            ∃ (V : T.Opens) (hP : (N.n i).base P.genericPoint ∈ V)
              (a : Fin (n - 1) → Γ(T, V)) (g : Γ(T, V)),
              IsLogResiduePresentation N n m i P V hP a g 1 (s i) := by
  classical
  obtain ⟨m, hm, hmΔ, hgen⟩ := hΔ.exists_isAdjointGeneratorOn
  have hdim : ∀ i, topologicalKrullDim (N.X i) = n := fun i => by
    obtain ⟨K, hK⟩ := hΔ.exists_isDltPair i
    exact hK.1.2.1.1
  haveI : ∀ i, LocallyOfFiniteType (N.n i ≫ sT) := fun i =>
    (N.isNormalVariety i).1.toLocallyOfFiniteType
  have htr : ∀ i, (letI := functionFieldAlgebra (N.n i ≫ sT)
      (Algebra.trdeg k (N.X i).functionField).toNat = n) := fun i =>
    toNat_trdeg_functionField_of_topologicalKrullDim_eq (hdim i)
  have hb := fun i => (exists_basis_topForms (htr i)).some
  refine ⟨m * a, Nat.mul_pos hm ha, ?_, fun x => ?_⟩
  · intro Γ
    rw [hΔ' Γ]
    obtain ⟨z, hz⟩ : ∃ z : ℤ, (m : ℚ) * Δ Γ = z :=
      ⟨((m : ℚ) * Δ Γ).num, (Rat.coe_int_num_of_den_eq_one (hmΔ Γ)).symm⟩
    have ha' : (a : ℚ) ≠ 0 := by positivity
    have : ((m * a : ℕ) : ℚ) * (Δ Γ + (a : ℚ)⁻¹ * primeDivisorOrder Γ.1 HT) =
        ((a * z + m * primeDivisorOrder Γ.1 HT : ℤ) : ℚ) := by
      push_cast
      rw [← hz]
      field_simp
    rw [this]
    exact Rat.den_intCast _
  · obtain ⟨U, hxU, s, hs, hself⟩ := hgen x
    obtain ⟨W, hfxW, h, hu, hloc⟩ := hH (f x)
    let φ : ∀ i, (N.X i).functionField := fun i =>
      if hW : Nonempty ((N.n i ≫ f) ⁻¹ᵁ W) then
        haveI := hW
        (N.X i).germToFunctionField ((N.n i ≫ f) ⁻¹ᵁ W) ((N.n i ≫ f).app W h)
      else 1
    have hφ : ∀ i (y : N.X i) (hy : (N.n i ≫ f) y ∈ W), φ i =
        algebraMap _ _ ((N.X i).presheaf.germ _ y hy ((N.n i ≫ f).app W h)) := by
      intro i y hy
      have hW : Nonempty ((N.n i ≫ f) ⁻¹ᵁ W) := ⟨⟨y, hy⟩⟩
      simp only [φ, dif_pos hW]
      exact (Scheme.algebraMap_germ_eq_germToFunctionField (N.X i)
        (U := (N.n i ≫ f) ⁻¹ᵁ W) hy _).symm
    have hφ0 : ∀ i, φ i ≠ 0 := by
      intro i
      by_cases hW : Nonempty ((N.n i ≫ f) ⁻¹ᵁ W)
      · obtain ⟨⟨y, hy⟩⟩ := hW
        rw [hφ i y hy]
        have := germ_ne_zero_of_isPullback (N.n i ≫ f) (hHN i) hu hloc hy
        rwa [Ne, IsFractionRing.to_map_eq_zero_iff]
      · simp only [φ, dif_neg hW]
        exact one_ne_zero
    let s' : ∀ i, RationalPluriForms (N.n i ≫ sT) n ((m * a : ℕ) : ℤ) := fun i =>
      ((φ i)⁻¹ ^ m) • formPow (hb i) m a (s i)
    have hpow0 : ∀ i, formPow (hb i) m a (s i) ≠ 0 := fun i =>
      linePow_ne_zero _ m a (hs.1 i).1
    -- near a double point, `φ` is the pull-back of a unit `u` of `T`
    have key : ∀ (i : N.ι) (P : MMP.Mori.PrimeDivisor (N.X i)) (V : T.Opens),
        (N.n i).base P.genericPoint ∈ V → (N.n i).base P.genericPoint ∈ U ⊓ f ⁻¹ᵁ W →
        (N.n i).base P.genericPoint ∈ (doubleIntersectionLocus T : Set T) →
        ∃ (V' : T.Opens) (hV' : V' ≤ V) (hQV' : (N.n i).base P.genericPoint ∈ V')
          (u : Γ(T, V')) (hu' : IsUnit u), ∀ (l : N.ι) (R : MMP.Mori.PrimeDivisor (N.X l))
          (hR : (N.n l).base R.genericPoint ∈ V'),
          algebraMap _ (N.X l).functionField ((N.X l).presheaf.germ ((N.n l) ⁻¹ᵁ V')
            R.genericPoint hR ((N.n l).app V' u)) = φ l := by
      intro i P V hP hQU hQD
      have hyW : f ((N.n i).base P.genericPoint) ∈ W := hQU.2
      have hyB : f ((N.n i).base P.genericPoint) ∈ Z.basicOpen h :=
        (Z.mem_basicOpen h _ hyW).mpr
          (isUnit_germ_of_notMem_cartierSupport hu hloc hyW (hD i P hQD))
      let V' : T.Opens := V ⊓ f ⁻¹ᵁ Z.basicOpen h
      have hV'W : V' ≤ f ⁻¹ᵁ W := inf_le_right.trans fun y hy => Z.basicOpen_le h hy
      let u : Γ(T, V') := T.presheaf.map (homOfLE hV'W).op (f.app W h)
      have hgu : ∀ (y : T) (hy : y ∈ V'), T.presheaf.germ V' y hy u =
          f.stalkMap y (Z.presheaf.germ W (f y) (hV'W hy) h) := by
        intro y hy
        rw [Scheme.Hom.germ_stalkMap_apply f W y (hV'W hy) h]
        exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
      have hu' : IsUnit u := by
        refine RingedSpace.isUnit_of_isUnit_germ T.toRingedSpace V' u fun y hy => ?_
        change IsUnit (T.presheaf.germ V' y hy u)
        rw [hgu y hy]
        exact ((Z.mem_basicOpen h _ (hV'W hy)).mp hy.2).map _
      refine ⟨V', inf_le_left, ⟨hP, hyB⟩, u, hu', fun l R hR => ?_⟩
      rw [hφ l R.genericPoint (hV'W hR)]
      congr 1
      rw [← Scheme.Hom.germ_stalkMap_apply, hgu _ hR,
        ← Scheme.Hom.germ_stalkMap_apply (N.n l ≫ f) W R.genericPoint (hV'W hR) h,
        Scheme.Hom.stalkMap_comp]
      rfl
    refine ⟨U ⊓ f ⁻¹ᵁ W, ⟨hxU, hfxW⟩, s', ⟨fun i => ⟨?_, fun Γ hΓ => ?_⟩, ?_⟩, ?_⟩
    · exact smul_ne_zero (pow_ne_zero _ (inv_ne_zero (hφ0 i))) (hpow0 i)
    · have hηΓ : Γ.genericPoint ∈ (N.n i) ⁻¹ᵁ (U ⊓ f ⁻¹ᵁ W) := by
        have h1 := hΓ
        rw [PrimeDivisor.support_eq_closure,
          closure_inter_open_nonempty_iff (TopologicalSpace.Opens.isOpen _)] at h1
        obtain ⟨y, hy, hyU⟩ := h1
        rwa [Set.mem_singleton_iff.mp hy] at hyU
      have hΓU : (Γ.support ∩ ((N.n i) ⁻¹ᵁ U : Set (N.X i))).Nonempty :=
        ⟨Γ.genericPoint, genericPoint_mem_support Γ, hηΓ.1⟩
      have e1 := (hs.1 i).2 Γ hΓU
      have hyW : (N.n i ≫ f) Γ.genericPoint ∈ W := hηΓ.2
      have hord : (N.X i).ord (φ i) Γ.genericPoint = primeDivisorOrder Γ (HN i) := by
        rw [hφ i _ hyW]
        exact (primeDivisorOrder_eq_ord_of_isPullback (N.n i ≫ f) (hHN i) hu hloc Γ hyW
          (germ_ne_zero_of_isPullback (N.n i ≫ f) (hHN i) hu hloc hyW)).symm
      show ((Γ.ordForm (((φ i)⁻¹ ^ m) • formPow (hb i) m a (s i)) : ℤ) : ℚ) +
        ((m * a : ℕ) : ℚ) * (Θ' i).coeff Γ = 0
      rw [Γ.ordForm_smul (htr i) (pow_ne_zero _ (inv_ne_zero (hφ0 i))) (hpow0 i),
        ordForm_linePow (htr i) _ m a (hs.1 i).1 Γ, Scheme.ord_pow (inv_ne_zero (hφ0 i)),
        scheme_ord_inv (hφ0 i),
        hord, hΘ']
      have ha' : (a : ℚ) ≠ 0 := by positivity
      push_cast
      field_simp
      linear_combination (a : ℚ) * e1
    · intro i j P P' heq hQU hQD hne
      obtain ⟨V, hP, hP', av, g, h1, h2⟩ := hs.2 i j P P' heq hQU.1 hQD hne
      obtain ⟨V', hV', hQV', u, hu', hφu⟩ := key i P V hP hQU hQD
      have hQ'V' : (N.n j).base P'.genericPoint ∈ V' := heq ▸ hQV'
      refine ⟨V', hQV', hQ'V', fun l => T.presheaf.map (homOfLE hV').op (av l),
        T.presheaf.map (homOfLE hV').op g ^ a * ((hu'.unit⁻¹ : Γ(T, V')ˣ) : Γ(T, V')) ^ m,
        ?_, ?_⟩
      · simpa only [one_pow] using
          isLogResiduePresentation_twist N a hV' hQV' h1 (hb i) hu' (hφu i P hQV')
      · simpa only [← pow_mul] using
          isLogResiduePresentation_twist N a hV' hQ'V' h2 (hb j) hu' (hφu j P' hQ'V')
    · intro i P hQU hQD
      obtain ⟨V, hP, av, g, h1⟩ := hself i P hQU.1 hQD
      obtain ⟨V', hV', hQV', u, hu', hφu⟩ := key i P V hP hQU hQD
      refine ⟨V', hQV', fun l => T.presheaf.map (homOfLE hV').op (av l),
        T.presheaf.map (homOfLE hV').op g ^ a * ((hu'.unit⁻¹ : Γ(T, V')ˣ) : Γ(T, V')) ^ m, ?_⟩
      simpa only [one_pow] using
        isLogResiduePresentation_twist N a hV' hQV' h1 (hb i) hu' (hφu i P hQV')

open MMP.Intersection Opposite in
/-- **A generating family of sections of `𝒪_Z(aMA)` with `a⁻¹ < ε`.** For `A` with ample sheaf
on a quasi-compact integral `Z`, `M : ℕ` and `ε > 0`, there are `a > 1/ε` and finitely many
sections of `𝒪_Z(aMA)` without common zero. -/
private theorem exists_sections_inv_lt {Z : Scheme.{u}} [IsIntegral Z] [CompactSpace Z]
    {A : Z.CartierDivisor} (hAamp : Stacks.Ample.IsAmple Z (MMP.CartierDivisor.sheaf A)) (M : ℕ) {ε
        : ℚ}
    (hε : 0 < ε) :
    ∃ a : ℕ, 0 < a ∧ (a : ℚ)⁻¹ < ε ∧
      ∃ (N : ℕ) (s : Fin (N + 1) → (Z.totalQuotientSheaf.obj.obj (op ⊤))ˣ),
        (∀ j, ((s j : _ˣ) : Z.totalQuotientSheaf.obj.obj (op ⊤)) ∈
          lineBundleSections ((a * M) • A) ⊤) ∧
        ∀ z : Z, ∃ j,
          z ∉ cartierSupport ((a * M) • A + MMP.Intersection.principalDivisor (s j)) := by
  obtain ⟨n₀, hn₀, hgs⟩ := exists_generating_sections (isNvBasis_of_isAmple A hAamp)
  obtain ⟨m, hm⟩ := exists_nat_gt ε⁻¹
  refine ⟨n₀ * (m + 1), Nat.mul_pos hn₀ (Nat.succ_pos m), ?_, ?_⟩
  · rw [inv_lt_comm₀ (by positivity) hε]
    have h1 : (1 : ℚ) ≤ n₀ := by exact_mod_cast hn₀
    refine hm.trans_le ?_
    push_cast
    nlinarith
  · obtain ⟨N, s, hs, hgen⟩ := hgs ((m + 1) * M)
    have hdeg : (m + 1) * M * n₀ = n₀ * (m + 1) * M := by ring
    rw [hdeg] at hs hgen
    exact ⟨N, s, hs, hgen⟩

open MMP.Intersection Opposite in
/-- **A member of a free linear system avoiding finitely many points.** Let `s₀, …, s_N` be
sections of `𝒪_Z(D)` without common zero on an integral scheme over an infinite field, `Q` a
nonzero polynomial and `F` a nonempty finite set of points. Some `c` with `Q(c) ≠ 0` gives a
member `σ = ∑ cⱼ sⱼ`, a unit of `Γ(Z, 𝓜_Z)`, whose divisor `D + div σ` is effective, linearly
equivalent to `D`, and misses `F`: not vanishing at `z ∈ F` is a polynomial condition on `c`
(`exists_polynomial_isUnit_secNumAt`). -/
private theorem exists_member_notMem_cartierSupport {k : Type u} [Field k] [Infinite k]
    {Z : Scheme.{u}} [IsIntegral Z] (sZ : Z ⟶ Spec (.of k)) (D : Z.CartierDivisor) {N : ℕ}
    (s : Fin (N + 1) → (Z.totalQuotientSheaf.obj.obj (op ⊤))ˣ)
    (hs : ∀ j, ((s j : _ˣ) : Z.totalQuotientSheaf.obj.obj (op ⊤)) ∈ lineBundleSections D ⊤)
    (hgen : ∀ z : Z, ∃ j, z ∉ cartierSupport (D + MMP.Intersection.principalDivisor (s j)))
    {Q : MvPolynomial (Fin (N + 1)) k} (hQ : Q ≠ 0) {F : Finset Z} (hF : F.Nonempty) :
    ∃ (c : Fin (N + 1) → k) (u : (Z.totalQuotientSheaf.obj.obj (op ⊤))ˣ),
      (u : Z.totalQuotientSheaf.obj.obj (op ⊤)) =
        ∑ j, scalarsToGlobalSections k sZ (c j) •
          ((s j : _ˣ) : Z.totalQuotientSheaf.obj.obj (op ⊤)) ∧
      MvPolynomial.eval c Q ≠ 0 ∧ IsEffective (D + MMP.Intersection.principalDivisor u) ∧
      LinearlyEquivalent (D + MMP.Intersection.principalDivisor u) D ∧
      ∀ z ∈ F, z ∉ cartierSupport (D + MMP.Intersection.principalDivisor u) := by
  classical
  obtain ⟨z₀, hz₀⟩ := hF
  choose Qz hQz0 hQz using fun z => exists_polynomial_isUnit_secNumAt sZ D
    (fun j => ((s j : _ˣ) : Z.totalQuotientSheaf.obj.obj (op ⊤))) hs z
    (by obtain ⟨j, hj⟩ := hgen z
        exact ⟨j, (notMem_cartierSupport_iff_isUnit_secNumAt z _ (s j) (hs j)).mp hj⟩)
  obtain ⟨c, hc⟩ := exists_eval_ne_zero
    (mul_ne_zero hQ (Finset.prod_ne_zero_iff.mpr fun z (_ : z ∈ F) => hQz0 z))
  rw [map_mul, map_prod] at hc
  set σ : Z.totalQuotientSheaf.obj.obj (op ⊤) := ∑ j, scalarsToGlobalSections k sZ (c j) •
    ((s j : _ˣ) : Z.totalQuotientSheaf.obj.obj (op ⊤))
  have hsmem : σ ∈ lineBundleSections D ⊤ :=
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hs j)
  have hσunit : ∀ z ∈ F, IsUnit (secNumAt z D σ) := fun z hz =>
    hQz z c (Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hc) z hz)
  have hσ0 : σ ≠ 0 := by
    intro h0
    have h2 : secNumAt z₀ D σ = 0 := by
      apply stalkToTotalQuotient_injective
      rw [secNumAt_spec _ _ hsmem, h0]
      simp
    exact not_isUnit_zero (h2 ▸ hσunit z₀ hz₀)
  set u := (isUnit_of_ne_zero_totalQuotient hσ0).unit
  have hu : (u : Z.totalQuotientSheaf.obj.obj (op ⊤)) = σ := IsUnit.unit_spec _
  have husmem : (u : Z.totalQuotientSheaf.obj.obj (op ⊤)) ∈ lineBundleSections D ⊤ := hu ▸ hsmem
  exact ⟨c, u, hu, left_ne_zero_of_mul hc, isEffective_add_principalDivisor u husmem,
    mem_principalSubgroup_iff.mpr ⟨u, by rw [add_sub_cancel_left]⟩, fun z hz =>
      (notMem_cartierSupport_iff_isUnit_secNumAt z _ u husmem).mpr (hu ▸ hσunit z hz)⟩

open MMP.Intersection in
/-- **A general member of `|aMA|` keeps a dlt pair dlt.** Let `(X, Θ)` be a dlt pair over an
algebraically closed field `k` of characteristic zero, `g : X ⟶ Z` a morphism over `k` to a
projective integral scheme, `A` a Cartier divisor on `Z` with ample sheaf, `M > 0` and
`ε > 0`. There are `a > 1/ε` and an ample effective `H ∼ aMA` with `g(η_X) ∉ Supp H` and a
pull-back `g^*H` whose Weil divisor `W` has all coefficients at most `1`, shares no component
with `Θ`, and makes `(X, Θ + a⁻¹ W)` dlt. -/
theorem _root_.MMP.Mori.IsDltPair.exists_isDltPair_add_inv_smul_pullback
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {X Z : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} [IsIntegral Z]
    (hZ : IsProjectiveMorphism sZ) (g : X ⟶ Z) (hg : g ≫ sZ = sX)
    {n : ℕ} {K : Divisor X} {Θ : QDivisor X} (hdlt : IsDltPair sX n K Θ)
    {A : Z.CartierDivisor} (hAamp : Stacks.Ample.IsAmple Z (MMP.CartierDivisor.sheaf A)) {M : ℕ}
    (hM : 0 < M) (ε : ℚ) (hε : 0 < ε) :
    ∃ (H : Z.CartierDivisor) (a : ℕ), IsEffective H ∧
      KCartierDivisor.IsRelativelyAmpleQ sZ (KCartierDivisor.ofCartier ℚ H) ∧ 0 < a ∧
      (a : ℚ)⁻¹ < ε ∧ LinearlyEquivalent H ((a * M : ℕ) • A) ∧
      g (genericPoint X) ∉ cartierSupport H ∧
      ∃ HX : X.CartierDivisor, IsPullback g H HX ∧
        ∀ W : Divisor X, IsWeilDivisorOfCartier HX W →
          (∀ P, W.coeff P ≤ 1) ∧ (∀ P, W.coeff P ≠ 0 → Θ.coeff P = 0) ∧
          IsDltPair sX n K (Θ + (a : ℚ)⁻¹ • Divisor.toQDivisor W) := by
  haveI : IsProper sZ := isProper_of_isProjectiveMorphism sZ hZ
  haveI : CompactSpace Z := (quasiCompact_iff_compactSpace sZ).mp inferInstance
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  obtain ⟨a, ha, haε, Ns, s, hs, hgen⟩ := exists_sections_inv_lt hAamp M hε
  obtain ⟨Q, F, hQ0, hFη, -, hF⟩ := exists_polynomial_isDltPair_add g hg hdlt _ s hs hgen
  obtain ⟨c, u, hu, hcQ, hHeff, hlin, hnv⟩ :=
    exists_member_notMem_cartierSupport sZ _ s hs hgen hQ0 ⟨_, hFη⟩
  obtain ⟨HX, hHX⟩ := exists_isPullback (f := g) (D := (a * M) • A + principalDivisor u)
    fun ξ hξ => by
      rw [eq_genericPoint_of_mem_schemeAssociatedPoints hξ]
      exact hnv _ hFη
  refine ⟨_, a, hHeff, isRelativelyAmpleQ_of_linearlyEquivalent_nsmul sZ hZ hAamp
    (Nat.mul_pos ha hM) hlin, ha, haε, hlin, hnv _ hFη, HX, hHX, fun W hW => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hF c u hu hcQ hnv HX hHX W hW
  exact ⟨h1, h2, h3 a ha⟩

open MMP.Intersection Opposite in
/-- **A common general member of `|aMA|`.** For an ample effective `A` on `Z`, `M > 0` and
`ε > 0`, there are `a > 1/ε` and a general member `H ∈ |aMA|` such that `H` is ample and
effective, misses the images of the conductor and of the prime divisors of `T` in the double
locus, its pull-back to `T` is reduced and shares no component with `Δ`, and every
`(Tᵢ, Θᵢ + a⁻¹ (f ∘ νᵢ)^*H)` is dlt. The sections of `𝒪_Z(aMA)` are taken from a generating
family; a general member is the member of one coefficient vector `c` avoiding finitely many
proper subvarieties of the coefficient space: Bertini on fixed log resolutions of the
`(Tᵢ, Θᵢ)` and on their snc loci (`exists_polynomial_isDltPair_add`), and the finitely many points
of `Z` to be avoided. -/
private theorem exists_generalMember
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {T Z : Scheme.{u}} [IsLocallyNoetherian T] {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    (N : NormalizationComponents sT hT) {n : ℕ} {Δ : QWeilDivisor T}
    {Θ : ∀ i, QDivisor (N.X i)} (hΔ : IsSdltAdjointPair N n Δ Θ)
    (sZ : Z ⟶ Spec (.of k)) [IsIntegral Z] (hZ : IsProjectiveMorphism sZ)
    (f : T ⟶ Z) (hf : f ≫ sZ = sT)
    {A : Z.CartierDivisor}
    (hAamp : Stacks.Ample.IsAmple Z (MMP.CartierDivisor.sheaf A)) {M : ℕ}
    (hM : 0 < M) (ε : ℚ) (hε : 0 < ε) :
    ∃ (H : Z.CartierDivisor) (a : ℕ), MMP.Intersection.IsEffective H ∧
      KCartierDivisor.IsRelativelyAmpleQ sZ (KCartierDivisor.ofCartier ℚ H) ∧ 0 < a ∧
      (a : ℚ)⁻¹ < ε ∧ MMP.Intersection.LinearlyEquivalent H ((a * M : ℕ) • A) ∧
      ∃ (HT : T.CartierDivisor) (HN : ∀ i, (N.X i).CartierDivisor),
        IsPullback f H HT ∧ (∀ i, IsPullback (N.n i ≫ f) H (HN i)) ∧
        ((∀ (i : N.ι) (P : MMP.Mori.PrimeDivisor (N.X i)),
            (N.n i).base P.genericPoint ∈ (doubleIntersectionLocus T : Set T) →
            f ((N.n i).base P.genericPoint) ∉ cartierSupport H) ∧
          ∀ Γ : WeilDivisorPrime T, Γ.1.genericPoint ∈ (doubleIntersectionLocus T : Set T) →
            f Γ.1.genericPoint ∉ cartierSupport H) ∧
        (∀ Γ : WeilDivisorPrime T, 0 ≤ primeDivisorOrder Γ.1 HT ∧ primeDivisorOrder Γ.1 HT ≤ 1 ∧
          (primeDivisorOrder Γ.1 HT ≠ 0 → Δ Γ = 0)) ∧
        ∃ Θ' : ∀ i, QDivisor (N.X i),
          (∀ i P, (Θ' i).coeff P = (Θ i).coeff P + (a : ℚ)⁻¹ * primeDivisorOrder P (HN i)) ∧
          ∀ i, ∃ K : Divisor (N.X i), MMP.Mori.IsDltPair (N.n i ≫ sT) n K (Θ' i) := by
  classical
  haveI : CompactSpace T := compactSpace_of_isProjectiveMorphism hΔ.isProjectiveMorphism
  haveI : IsNoetherian T := ⟨⟩
  haveI : IsReduced T := hΔ.isBoundary.2.1
  haveI : LocallyOfFiniteType sT := hΔ.isNFold.1.2.1
  haveI : IsProper sZ := isProper_of_isProjectiveMorphism sZ hZ
  haveI : CompactSpace Z := (quasiCompact_iff_compactSpace sZ).mp inferInstance
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI := finite_ι_of_isSdltAdjointPair N hΔ
  haveI : Fintype N.ι := Fintype.ofFinite _
  haveI hXc : ∀ i, CompactSpace (N.X i) := fun i => by
    haveI : QuasiCompact (N.n i ≫ sT) := (N.isNormalVariety i).1.toQuasiCompact
    exact QuasiCompact.compactSpace_of_compactSpace (N.n i ≫ sT)
  haveI : ∀ i, IsNoetherian (N.X i) := fun i => ⟨⟩
  obtain ⟨a, ha, haε, Ns, s, hs, hgen⟩ := exists_sections_inv_lt hAamp M hε
  -- the data on the components
  choose K hK using hΔ.exists_isDltPair
  choose Qi Fi hQi0 hFiη hFiΘ hFi using fun i =>
    exists_polynomial_isDltPair_add (N.n i ≫ f) (by rw [Category.assoc, hf]) (hK i)
      ((a * M) • A) s hs hgen
  -- the points of `Z` to avoid
  have hAss := Stacks.Divisors.finite_schemeAssociatedPoints T
  set Fall : Finset Z := insert (genericPoint Z) ((Finset.univ.biUnion Fi) ∪
    (hAss.toFinset.image f) ∪ (Δ.support.image fun Γ => f Γ.1.genericPoint)) with hFall
  obtain ⟨c, u, hu, hc, hHeff, hlin, hnv⟩ := exists_member_notMem_cartierSupport sZ _ s hs hgen
    (Finset.prod_ne_zero_iff.mpr fun i (_ : i ∈ Finset.univ) => hQi0 i)
    (F := Fall) ⟨_, Finset.mem_insert_self _ _⟩
  rw [map_prod] at hc
  have hcQi : ∀ i, MvPolynomial.eval c (Qi i) ≠ 0 := fun i =>
    Finset.prod_ne_zero_iff.mp hc i (Finset.mem_univ i)
  set H := (a * M) • A + MMP.Intersection.principalDivisor u with hHdef
  -- the pull-backs
  obtain ⟨HT, hHT⟩ := exists_isPullback (f := f) (D := H) fun ξ hξ => hnv _ (by
    rw [hFall]
    refine Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_union_right _ ?_))
    exact Finset.mem_image_of_mem _ (hAss.mem_toFinset.mpr hξ))
  have hFi_sub : ∀ i, ∀ z ∈ Fi i, z ∈ Fall := fun i z hz => by
    rw [hFall]
    exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hz⟩)))
  choose HN hHN using fun i => exists_isPullback (f := N.n i ≫ f) (D := H) fun ξ hξ => by
    rw [eq_genericPoint_of_mem_schemeAssociatedPoints hξ]
    exact hnv _ (hFi_sub i _ (hFiη i))
  choose W hW using fun i => MMP.Intersection.exists_isWeilDivisorOfCartier (HN i)
  have hres := fun i => hFi i c u hu (hcQi i) (fun z hz => hnv z (hFi_sub i z hz)) (HN i)
    (hHN i) (W i) (hW i)
  -- the double locus
  have hD1 : ∀ (i : N.ι) (P : MMP.Mori.PrimeDivisor (N.X i)),
      (N.n i).base P.genericPoint ∈ (doubleIntersectionLocus T : Set T) →
      f ((N.n i).base P.genericPoint) ∉ cartierSupport H := by
    intro i P hP
    have h1 := one_le_coeff_of_mem_doubleIntersectionLocus N hΔ i P hP
    have hPmem : P ∈ (Θ i).support := Finsupp.mem_support_iff.mpr (by
      intro h0; change (Θ i).coeff P = 0 at h0; rw [h0] at h1; norm_num at h1)
    exact hnv _ (hFi_sub i _ (hFiΘ i P hPmem))
  have hD2 : ∀ Γ : WeilDivisorPrime T, Γ.1.genericPoint ∈ (doubleIntersectionLocus T : Set T) →
      f Γ.1.genericPoint ∉ cartierSupport H := by
    intro Γ hΓ
    obtain ⟨i, P, hP⟩ := exists_primeDivisor_map_genericPoint_eq N Γ
    have := hD1 i P (hP ▸ hΓ)
    rwa [hP] at this
  refine ⟨H, a, hHeff, isRelativelyAmpleQ_of_linearlyEquivalent_nsmul sZ hZ hAamp
    (Nat.mul_pos ha hM) hlin, ha, haε, hlin, HT, HN, hHT, hHN, ⟨hD1, hD2⟩, fun Γ => ?_,
    fun i => Θ i + (a : ℚ)⁻¹ • Divisor.toQDivisor (W i), fun i P => ?_,
    fun i => ⟨K i, (hres i).2.2 a ha⟩⟩
  · obtain ⟨i, P, hP⟩ := exists_primeDivisor_map_genericPoint_eq N Γ
    have hcomp := primeDivisorOrder_comp_eq N hΔ sZ hZ f hf hHeff hHT hHN i P Γ hP
    have hWi := (hW i P).primeDivisorOrder_eq
    refine ⟨?_, ?_, fun hne => ?_⟩
    · rw [← hcomp]
      exact (primeDivisorOrder_nonneg_and_pos_of_isPullback _ hHeff (hHN i) P).1
    · rw [← hcomp, hWi]
      exact (hres i).1 P
    · by_contra hΔΓ
      apply hne
      refine primeDivisorOrder_eq_zero_of_isPullback f hHT Γ.1 (hnv _ ?_)
      rw [hFall]
      exact Finset.mem_insert_of_mem (Finset.mem_union_right _
        (Finset.mem_image_of_mem _ (Finsupp.mem_support_iff.mpr hΔΓ)))
  · rw [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, Divisor.coeff_toQDivisor,
      smul_eq_mul, (hW i P).primeDivisorOrder_eq]

open MMP.Intersection in
/-- **The choice of the general base hypersurface, read on the normalization.** For every
`ε > 0` there are an ample effective Cartier divisor `H` on `Z`, an integer `a > 1/ε` and
pull-backs `f^*H`, `(f ∘ νᵢ)^*H` such that `H` misses the image of the double locus, the
pull-backs are reduced and share no component with `Δ` (resp. `Θᵢ`), and with
`Θ'ᵢ = Θᵢ + a⁻¹ (f ∘ νᵢ)^*H` every `(Tᵢ, Θ'ᵢ)` is dlt and every `K_{Tᵢ} + Θ'ᵢ` is globally
semiample and nef. -/
private theorem exists_generalTwist
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {T Z : Scheme.{u}} [IsLocallyNoetherian T] {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    (N : NormalizationComponents sT hT) {n : ℕ} {Δ : QWeilDivisor T}
    {Θ : ∀ i, QDivisor (N.X i)} (hΔ : IsSdltAdjointPair N n Δ Θ)
    (sZ : Z ⟶ Spec (.of k)) [IsIntegral Z] (hZ : IsProjectiveMorphism sZ)
    (f : T ⟶ Z) (hf : f ≫ sZ = sT)
    (hL : ∀ (i : N.ι) (K : Divisor (N.X i)), K.IsCanonicalDivisor (N.n i ≫ sT) n →
      QDivisor.IsRelativelySemiample (N.n i ≫ f) (Divisor.toQDivisor K + Θ i))
    (ε : ℚ) (hε : 0 < ε) :
    ∃ (H : Z.CartierDivisor) (a : ℕ), MMP.Intersection.IsEffective H ∧
      KCartierDivisor.IsRelativelyAmpleQ sZ (KCartierDivisor.ofCartier ℚ H) ∧ 0 < a ∧
      (a : ℚ)⁻¹ < ε ∧
      ∃ (HT : T.CartierDivisor) (HN : ∀ i, (N.X i).CartierDivisor),
        IsPullback f H HT ∧ (∀ i, IsPullback (N.n i ≫ f) H (HN i)) ∧
        ((∀ (i : N.ι) (P : MMP.Mori.PrimeDivisor (N.X i)),
            (N.n i).base P.genericPoint ∈ (doubleIntersectionLocus T : Set T) →
            f ((N.n i).base P.genericPoint) ∉ cartierSupport H) ∧
          ∀ Γ : WeilDivisorPrime T, Γ.1.genericPoint ∈ (doubleIntersectionLocus T : Set T) →
            f Γ.1.genericPoint ∉ cartierSupport H) ∧
        (∀ Γ : WeilDivisorPrime T, 0 ≤ primeDivisorOrder Γ.1 HT ∧ primeDivisorOrder Γ.1 HT ≤ 1 ∧
          (primeDivisorOrder Γ.1 HT ≠ 0 → Δ Γ = 0)) ∧
        ∃ Θ' : ∀ i, QDivisor (N.X i),
          (∀ i P, (Θ' i).coeff P = (Θ i).coeff P + (a : ℚ)⁻¹ * primeDivisorOrder P (HN i)) ∧
          (∀ i, ∃ K : Divisor (N.X i), MMP.Mori.IsDltPair (N.n i ≫ sT) n K (Θ' i)) ∧
          ∀ (i : N.ι) (K : Divisor (N.X i)), K.IsCanonicalDivisor (N.n i ≫ sT) n →
            QDivisor.IsRelativelySemiample (N.n i ≫ sT) (Divisor.toQDivisor K + Θ' i) ∧
            haveI : QuasiCompact (N.n i ≫ sT) := (N.isNormalVariety i).1.toQuasiCompact
            (Divisor.toQDivisor K + Θ' i).IsRelativelyNef (N.n i ≫ sT) (N.n i ≫ sT) := by
  obtain ⟨A, M, hM, hAe, hA, hAamp, hsemi⟩ := exists_semiampleTwistData N hΔ sZ hZ f hf hL
  obtain ⟨H, a, hH, hHa, ha, haε, hlin, HT, HN, hHT, hHN, hD, hordT, Θ', hΘ', hdlt⟩ :=
    exists_generalMember N hΔ sZ hZ f hf hAamp hM ε hε
  refine ⟨H, a, hH, hHa, ha, haε, HT, HN, hHT, hHN, hD, hordT, Θ', hΘ', hdlt, fun i K hK => ?_⟩
  have hs := hsemi a H HN Θ' ha hH hlin hHN hΘ' i K hK
  haveI : QuasiCompact (N.n i ≫ sT) := (N.isNormalVariety i).1.toQuasiCompact
  exact ⟨hs, isRelativelyNef_of_isRelativelySemiample (N.isNormalVariety i) hs⟩

/-- **One general base twist makes all normalized adjoints globally semiample.** Let
`(T, Δ; L = K_T + Δ)` be a projective sdlt adjoint pair of dimension `n` over an algebraically
closed field `k` of characteristic zero, with normalization components `νᵢ : Tᵢ ⟶ T` (`N`) and
normalized boundaries `Θᵢ`, let `f : T ⟶ Z` be a morphism over `k` to a projective variety `Z`,
and suppose every `K_{Tᵢ} + Θᵢ` is semiample over `Z`. Then for every `ε > 0` there are an ample
effective Cartier divisor `H` on `Z` and `0 < c < ε` such that, with `G = c H` and the Cartier
pull-backs `f^*H` on `T` and `(f ∘ νᵢ)^*H` on `Tᵢ`, the pair `(T, Δ + f^*G; L + f^*G)` is an
sdlt adjoint pair with normalized boundaries `Θᵢ + (f ∘ νᵢ)^*G`, and every normalized adjoint
`K_{Tᵢ} + Θᵢ + (f ∘ νᵢ)^*G` is globally semiample and globally nef. -/
@[mmp "lem_fourfold_sdlt_common_base_twist"]
public theorem IsSdltAdjointPair.exists_isSdltAdjointPair_add_pullback
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {T Z : Scheme.{u}} [IsLocallyNoetherian T] {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    (N : NormalizationComponents sT hT) {n : ℕ} {Δ : QWeilDivisor T}
    {Θ : ∀ i, QDivisor (N.X i)} (hΔ : IsSdltAdjointPair N n Δ Θ)
    (sZ : Z ⟶ Spec (.of k)) [IsIntegral Z] (hZ : IsProjectiveMorphism sZ)
    (f : T ⟶ Z) (hf : f ≫ sZ = sT)
    (hL : ∀ (i : N.ι) (K : Divisor (N.X i)), K.IsCanonicalDivisor (N.n i ≫ sT) n →
      QDivisor.IsRelativelySemiample (N.n i ≫ f) (Divisor.toQDivisor K + Θ i))
    (ε : ℚ) (hε : 0 < ε) :
    ∃ (H : Z.CartierDivisor) (c : ℚ), MMP.Intersection.IsEffective H ∧
      KCartierDivisor.IsRelativelyAmpleQ sZ (KCartierDivisor.ofCartier ℚ H) ∧ 0 < c ∧ c < ε ∧
      ∃ (HT : T.CartierDivisor) (HN : ∀ i, (N.X i).CartierDivisor),
        MMP.Intersection.IsPullback f H HT ∧
        (∀ i, MMP.Intersection.IsPullback (N.n i ≫ f) H (HN i)) ∧
        ∃ (Δ' : QWeilDivisor T) (Θ' : ∀ i, QDivisor (N.X i)),
          (∀ Γ, Δ' Γ = Δ Γ + c * MMP.Intersection.primeDivisorOrder Γ.1 HT) ∧
          (∀ i P, (Θ' i).coeff P =
            (Θ i).coeff P + c * MMP.Intersection.primeDivisorOrder P (HN i)) ∧
          IsSdltAdjointPair N n Δ' Θ' ∧
          ∀ (i : N.ι) (K : Divisor (N.X i)), K.IsCanonicalDivisor (N.n i ≫ sT) n →
            QDivisor.IsRelativelySemiample (N.n i ≫ sT) (Divisor.toQDivisor K + Θ' i) ∧
            haveI : QuasiCompact (N.n i ≫ sT) := (N.isNormalVariety i).1.toQuasiCompact
            (Divisor.toQDivisor K + Θ' i).IsRelativelyNef (N.n i ≫ sT) (N.n i ≫ sT) := by
  classical
  obtain ⟨H, a, hH, hHa, ha, haε, HT, HN, hHT, hHN, hD, hordT, Θ', hΘ', hdlt, hsemi⟩ :=
    exists_generalTwist N hΔ sZ hZ f hf hL ε hε
  haveI : CompactSpace T := compactSpace_of_isProjectiveMorphism hΔ.isProjectiveMorphism
  let Δ' : QWeilDivisor T := Δ + Finsupp.ofSupportFinite
    (fun Γ => (a : ℚ)⁻¹ * MMP.Intersection.primeDivisorOrder Γ.1 HT) (by
      refine (finite_primeDivisorOrder_ne_zero HT).subset fun Γ hΓ => ?_
      simp only [Function.mem_support, ne_eq, mul_eq_zero, inv_eq_zero, Nat.cast_eq_zero,
        Int.cast_eq_zero, not_or] at hΓ
      exact hΓ.2)
  have hΔ' : ∀ Γ, Δ' Γ = Δ Γ + (a : ℚ)⁻¹ * MMP.Intersection.primeDivisorOrder Γ.1 HT := by
    intro Γ
    simp [Δ', Finsupp.ofSupportFinite_coe]
  refine ⟨H, (a : ℚ)⁻¹, hH, hHa, by positivity, haε, HT, HN, hHT, hHN, Δ', Θ', hΔ', hΘ', ?_,
    hsemi⟩
  refine ⟨hΔ.isNFold, hΔ.isProjectiveMorphism, hΔ.satisfiesS2, hΔ.isSeminormal,
    hΔ.isNcInCodimOne, ?_, ?_, ?_, hdlt,
    exists_isAdjointGeneratorOn_twist N hΔ sZ hZ f hf hH hD.1 hHT hHN ha hΔ' hΘ'⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hΔ.isBoundary
    refine ⟨h1, h2, h3, fun Γ => ?_⟩
    rw [hΔ' Γ]
    obtain ⟨o0, o1, oΔ⟩ := hordT Γ
    obtain ⟨hΓ0, hΓ1⟩ := h4 Γ
    rcases eq_or_ne (MMP.Intersection.primeDivisorOrder Γ.1 HT) 0 with h | h
    · simp [h, hΓ0, hΓ1]
    · have h1' : MMP.Intersection.primeDivisorOrder Γ.1 HT = 1 := by omega
      rw [oΔ h, h1']
      have ha1 : (1 : ℚ) ≤ a := by exact_mod_cast ha
      exact ⟨by positivity, by simpa using inv_le_one_of_one_le₀ ha1⟩
  · intro Γ hΓ hmem
    rw [Finsupp.mem_support_iff, hΔ'] at hΓ
    by_cases hΔΓ : Δ Γ = 0
    · have : MMP.Intersection.primeDivisorOrder Γ.1 HT = 0 :=
        primeDivisorOrder_eq_zero_of_isPullback f hHT Γ.1
          (hD.2 Γ hmem)
      simp [hΔΓ, this] at hΓ
    · exact hΔ.genericPoint_not_mem_doubleIntersectionLocus Γ (Finsupp.mem_support_iff.2 hΔΓ)
        hmem
  · intro i P
    have hP0 := hΔ.isAdjointBoundary i P
    unfold adjointBoundaryCoeff at hP0 ⊢
    rw [hΘ', hP0]
    by_cases hP : MMP.Intersection.primeDivisorOrder P (HN i) = 0
    · rw [hP]
      simp only [Int.cast_zero, mul_zero, add_zero]
      congr 1
      by_cases hex : ∃ Γ₀ : WeilDivisorPrime T, (N.n i).base P.genericPoint = Γ₀.1.genericPoint
      · obtain ⟨Γ₀, hΓ₀⟩ := hex
        rw [sum_ite_genericPoint_eq Δ' Γ₀ hΓ₀, sum_ite_genericPoint_eq Δ Γ₀ hΓ₀, hΔ',
          ← primeDivisorOrder_comp_eq N hΔ sZ hZ f hf hH hHT hHN i P Γ₀ hΓ₀, hP]
        simp
      · push Not at hex
        rw [sum_ite_genericPoint_eq_zero Δ' hex, sum_ite_genericPoint_eq_zero Δ hex]
    · obtain ⟨Γ₀, hΓ₀⟩ :=
        exists_weilDivisorPrime_of_primeDivisorOrder_ne_zero N hΔ sZ hZ f hf hH hD.1 hHT hHN i P hP
      have hcomp := primeDivisorOrder_comp_eq N hΔ sZ hZ f hf hH hHT hHN i P Γ₀ hΓ₀
      have hΔ0 : Δ Γ₀ = 0 := (hordT Γ₀).2.2 (hcomp ▸ hP)
      have hnot : (N.n i).base P.genericPoint ∉ (doubleIntersectionLocus T : Set T) := by
        intro hm
        apply hP
        refine primeDivisorOrder_eq_zero_of_isPullback (N.n i ≫ f) (hHN i) P ?_
        simpa using hD.1 i P hm
      rw [sum_ite_genericPoint_eq Δ' Γ₀ hΓ₀, sum_ite_genericPoint_eq Δ Γ₀ hΓ₀, hΔ', hΔ0,
        if_neg hnot, hcomp]
      simp

end MMP.Fourfold
