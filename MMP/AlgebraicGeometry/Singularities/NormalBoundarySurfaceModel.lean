module
public import MMP.Analysis.Complex.CauchyTransformRungeMontel
import MMP.RingTheory.Ideal.MaximalHeightFiniteType
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
public import MMP.RingTheory.KrullDimension.HeightAddCoheight
public import StacksFrontier.Order.HeightCoheight
import MMP.AlgebraicGeometry.Variety.Subvariety

/-!
# Algebraic surface models at codimension-two points of a normal boundary

Let `X` be a normal variety over an algebraically closed field `k` of characteristic zero, `S` a
normal prime divisor of `X` and `P` a point of `S` of codimension one in `S`. Put
`A = 𝒪_{X,P}`, let `H = A^{sh}` be a strict henselization of `A` and `R = Ĥ` its `𝔪_H`-adic
completion, with residue field `K`, a separable closure of `κ(P)`. Lifting a separating
transcendence basis of `κ(P)/k` and passing to the generic fibre, then to `K`, produces a
normal algebraic surface germ `(Y, y)` over `K` (`Y ∖ {y}` smooth), a smooth prime curve `C`
through `y` lying over `S` and a morphism `j : Y ⟶ X` sending `y` to `P`, together with a ring
isomorphism `𝒪̂_{Y,y} ≅ R` over `A` carrying the ideal of `C` onto `I_S R`. Smoothness off `y` is
obtained by shrinking `Y`: on the normal surface `Y` the singular points are closed, hence finite
in number.

The morphism `j` is a limit of étale morphisms after the generic-fibre localization, so a
projective log resolution `f : W ⟶ U` of an `ℝ`-divisor `D` on an open neighbourhood `U` of `P`
base changes along `j` to a projective log resolution of the pulled-back divisor on `j⁻¹(U)`,
and the discrepancy of every exceptional prime divisor of `W`, for every boundary `B` with
`K_U + B` `ℝ`-Cartier, equals the discrepancy of each prime divisor of the base change lying
over it. Consequently `(j⁻¹(U), B')` is log terminal when `(U, B)` is: every exceptional prime
divisor of the base change of a witnessing log resolution lies over an exceptional prime divisor
of the resolution, codimensions being preserved by `j`. The argument uses only that the map to
`U` is flat, formally unramified and compatible with `Spec κsep ⟶ Spec k`, so it applies equally
to `U₀ ⟶ U` for any open neighbourhood `U₀ ⊆ j⁻¹(U)` of `y`.

## Main results

* `MMP.Flips.exists_surfaceModel_of_codimension_two`

## Implementation notes

The ideal `I_S ⊆ 𝒪_{X,P}` is the kernel of `𝒪_{X,P} → κ(η_S)`, the specialization map to the
stalk at the generic point followed by the residue map, and `𝒪_{S,P} = 𝒪_{X,P}/I_S`; similarly
for `I_C ⊆ 𝒪_{Y,y}`. The pull-back along `j` of an `ℝ`-divisor `B` on `U` is described by its
coefficients: a prime divisor `Q` of `j⁻¹(U)` receives the coefficient of the prime divisor of `U`
whose generic point is `j(η_Q)`, and `0` if `j(η_Q)` is not the generic point of a prime divisor.
This is the flat pull-back, since `j` has geometrically reduced zero-dimensional fibres.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips]
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

namespace Proof_lem_mmp_normal_boundary_codimension_two_surface_model

open MMP MMP.Flips
open MMP.Mori hiding IsLogResolution

section TranscendenceLift

variable {k A ι : Type*} [Field k] [CommRing A] [IsLocalRing A] [Algebra k A]

/-- If the residues of `t i ∈ A` are algebraically independent over `k`, every nonzero polynomial
in the `t i` has nonzero residue, hence is a unit of the local ring `A`. -/
private theorem isUnit_aeval_of_algebraicIndependent_residue {t : ι → A}
    (ht : AlgebraicIndependent k (residue A ∘ t)) {p : MvPolynomial ι k} (hp : p ≠ 0) :
    IsUnit (MvPolynomial.aeval t p) := by
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
  have : residue A (MvPolynomial.aeval t p) = MvPolynomial.aeval (residue A ∘ t) p :=
    MvPolynomial.comp_aeval_apply t (IsScalarTower.toAlgHom k A (ResidueField A)) p
  rw [this]
  exact fun h => hp (ht.eq_zero_of_aeval_eq_zero p h)

/-- The embedding `k(t) ↪ A` of the rational function field in lifts `t i` of an algebraically
independent family of the residue field. -/
private noncomputable def fractionRingLift {t : ι → A}
    (ht : AlgebraicIndependent k (residue A ∘ t)) :
    FractionRing (MvPolynomial ι k) →+* A :=
  IsLocalization.lift (M := nonZeroDivisors (MvPolynomial ι k))
    (g := (MvPolynomial.aeval t : MvPolynomial ι k →ₐ[k] A).toRingHom)
    (fun p => isUnit_aeval_of_algebraicIndependent_residue ht (nonZeroDivisors.ne_zero p.2))

private theorem fractionRingLift_algebraMap {t : ι → A}
    (ht : AlgebraicIndependent k (residue A ∘ t)) (p : MvPolynomial ι k) :
    fractionRingLift ht (algebraMap _ _ p) = MvPolynomial.aeval t p :=
  IsLocalization.lift_eq _ p

/-- The residue field is algebraic over `k(t)` for lifts `t` of a transcendence basis. -/
private theorem isAlgebraic_residue_fractionRingLift {t : ι → A}
    (ht : IsTranscendenceBasis k (residue A ∘ t)) :
    letI : Algebra (FractionRing (MvPolynomial ι k)) (ResidueField A) :=
      ((residue A).comp (fractionRingLift ht.1)).toAlgebra
    Algebra.IsAlgebraic (FractionRing (MvPolynomial ι k)) (ResidueField A) := by
  let _ : Algebra (FractionRing (MvPolynomial ι k)) (ResidueField A) :=
    ((residue A).comp (fractionRingLift ht.1)).toAlgebra
  set L := IntermediateField.adjoin k (Set.range (residue A ∘ t))
  have hL := ht.isAlgebraic_field
  let e := ht.1.aevalEquivField
  have hcomp : (algebraMap (FractionRing (MvPolynomial ι k)) (ResidueField A)).comp
      (e.symm : L →+* FractionRing (MvPolynomial ι k)) = algebraMap L (ResidueField A) := by
    have h2 : (algebraMap (FractionRing (MvPolynomial ι k)) (ResidueField A)) =
        (algebraMap L (ResidueField A)).comp (e : FractionRing (MvPolynomial ι k) →+* L) := by
      apply IsLocalization.ringHom_ext (nonZeroDivisors (MvPolynomial ι k))
      ext p
      · simp [RingHom.algebraMap_toAlgebra, fractionRingLift_algebraMap, e]
        rfl
      · simp [RingHom.algebraMap_toAlgebra, fractionRingLift_algebraMap, e]
    rw [h2, RingHom.comp_assoc]
    ext x
    simp
  refine ⟨fun x => ?_⟩
  obtain ⟨p, hp, hpx⟩ := hL.isAlgebraic x
  refine ⟨p.map (e.symm : L →+* FractionRing (MvPolynomial ι k)), ?_, ?_⟩
  · exact (Polynomial.map_ne_zero_iff e.symm.injective).mpr hp
  · rw [Polynomial.aeval_def, Polynomial.eval₂_map, hcomp]
    exact hpx

/-- `κ(A)` is a finite extension of `k(t)` when it is finitely generated over `k`. -/
private theorem finite_residue_fractionRingLift [Algebra.EssFiniteType k (ResidueField A)]
    {t : ι → A}
    (ht : IsTranscendenceBasis k (residue A ∘ t)) :
    letI : Algebra (FractionRing (MvPolynomial ι k)) (ResidueField A) :=
      ((residue A).comp (fractionRingLift ht.1)).toAlgebra
    Module.Finite (FractionRing (MvPolynomial ι k)) (ResidueField A) := by
  let _ : Algebra (FractionRing (MvPolynomial ι k)) (ResidueField A) :=
    ((residue A).comp (fractionRingLift ht.1)).toAlgebra
  have : IsScalarTower k (FractionRing (MvPolynomial ι k)) (ResidueField A) := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply,
      IsScalarTower.algebraMap_apply k (MvPolynomial ι k) (FractionRing (MvPolynomial ι k)),
      fractionRingLift_algebraMap, MvPolynomial.algebraMap_eq, MvPolynomial.aeval_C]
    rfl
  have := isAlgebraic_residue_fractionRingLift ht
  have : Algebra.EssFiniteType (FractionRing (MvPolynomial ι k)) (ResidueField A) :=
    Algebra.EssFiniteType.of_comp k _ _
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic

end TranscendenceLift

section HenselLift

open Polynomial

/-- Two roots of a polynomial over a local ring with the same residue agree, when the derivative
is a unit at one of them. -/
private theorem eq_of_isRoot_of_residue_eq {H : Type*} [CommRing H] [IsLocalRing H] {f : H[X]}
    {a b : H}
    (ha : f.IsRoot a) (hb : f.IsRoot b) (hab : residue H a = residue H b)
    (hu : IsUnit (f.derivative.eval a)) : a = b := by
  obtain ⟨c, hc⟩ := f.binomExpansion a (b - a)
  have hm : b - a ∈ maximalIdeal H := by
    rw [← residue_eq_zero_iff, map_sub, hab, sub_self]
  rw [add_sub_cancel, hb.eq_zero, ha.eq_zero, zero_add] at hc
  have hunit : IsUnit (f.derivative.eval a + c * (b - a)) := by
    rw [← residue_ne_zero_iff_isUnit, map_add, map_mul,
      (residue_eq_zero_iff _).mpr hm, mul_zero, add_zero, residue_ne_zero_iff_isUnit]
    exact hu
  have : (b - a) * (f.derivative.eval a + c * (b - a)) = 0 := by rw [hc]; ring
  exact (sub_eq_zero.mp (hunit.mul_left_eq_zero.mp this)).symm

variable {F H L : Type*} [Field F] [CommRing H] [HenselianLocalRing H] [Algebra F H]
  [Field L] [Algebra F L]

private theorem residue_eval_map (p : F[X]) (a : H) :
    residue H ((p.map (algebraMap F H)).eval a) = aeval (residue H a) p := by
  rw [eval_map_algebraMap]
  exact (aeval_algHom_apply (IsScalarTower.toAlgHom F H (ResidueField H)) a p).symm

/-- **Hensel's lemma for a separable element.** The minimal polynomial of a separable `x` over
`F` has a root in the henselian `H` with residue `σ x`, at which its derivative is a unit. -/
private theorem exists_isRoot_minpoly (σ : L →ₐ[F] ResidueField H) {x : L}
    (hx : IsSeparable F x) :
    ∃ a : H, ((minpoly F x).map (algebraMap F H)).IsRoot a ∧ residue H a = σ x ∧
      IsUnit (((minpoly F x).map (algebraMap F H)).derivative.eval a) := by
  have hint := hx.isIntegral
  obtain ⟨a₀, ha₀⟩ := residue_surjective (σ x)
  have h1 : aeval (σ x) (minpoly F x) = 0 := by
    rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  have h2 : aeval (σ x) (derivative (minpoly F x)) ≠ 0 := by
    rw [Polynomial.aeval_algHom_apply]
    exact fun h => hx.aeval_derivative_ne_zero (minpoly.aeval F x)
      ((map_eq_zero_iff σ σ.injective).mp h)
  obtain ⟨a, ha, hres⟩ := HenselianLocalRing.is_henselian _ ((minpoly.monic hint).map _) a₀
    (by rw [← residue_eq_zero_iff, residue_eval_map, ha₀, h1])
    (by rwa [← residue_ne_zero_iff_isUnit, derivative_map, residue_eval_map, ha₀])
  have hres' : residue H a = σ x := by
    rwa [← ha₀, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
  refine ⟨a, ha, hres', ?_⟩
  rwa [← residue_ne_zero_iff_isUnit, derivative_map, residue_eval_map, hres']

/-- An `F`-algebra map into `H` lifting `σ` sends `z` to the Hensel root of its minimal
polynomial. -/
private theorem eq_of_isRoot_minpoly (σ : L →ₐ[F] ResidueField H) {E : Type*} [Field E]
    [Algebra F E]
    (ι : E →ₐ[F] L) (φ : E →ₐ[F] H)
    (hφ : (IsScalarTower.toAlgHom F H (ResidueField H)).comp φ = σ.comp ι) (z : E)
    {a : H} (ha : ((minpoly F (ι z)).map (algebraMap F H)).IsRoot a)
    (hres : residue H a = σ (ι z))
    (hu : IsUnit (((minpoly F (ι z)).map (algebraMap F H)).derivative.eval a)) : φ z = a := by
  refine (eq_of_isRoot_of_residue_eq ha ?_ ?_ hu).symm
  · rw [IsRoot, eval_map_algebraMap, minpoly.algHom_eq ι ι.injective, aeval_algHom_apply,
      minpoly.aeval, map_zero]
  · rw [hres]; exact (DFunLike.congr_fun hφ z).symm

/-- A finite separable extension `E/F` with an `F`-map to the residue field of a henselian local
`F`-algebra `H` lifts to `H`. -/
private theorem exists_algHom_lift_of_finite (E : Type*) [Field E] [Algebra F E]
    [FiniteDimensional F E]
    [Algebra.IsSeparable F E] (τ : E →ₐ[F] ResidueField H) :
    ∃ φ : E →ₐ[F] H, (IsScalarTower.toAlgHom F H (ResidueField H)).comp φ = τ := by
  let pb := Field.powerBasisOfFiniteOfSeparable F E
  obtain ⟨a, ha, hres, -⟩ := exists_isRoot_minpoly τ (Algebra.IsSeparable.isSeparable F pb.gen)
  refine ⟨pb.lift a (by rwa [IsRoot, eval_map_algebraMap] at ha), pb.algHom_ext ?_⟩
  simp [PowerBasis.lift_gen, hres]

/-- **Hensel lift of a separable algebraic extension.** Let `H` be a henselian local `F`-algebra
and `L/F` a separable algebraic extension with an `F`-map `σ` to the residue field of `H`. Then
`σ` lifts to an `F`-algebra map `L → H`: it sends `x` to the unique root of the minimal
polynomial of `x` with residue `σ x`. -/
private theorem exists_algHom_lift [Algebra.IsSeparable F L] (σ : L →ₐ[F] ResidueField H) :
    ∃ ψ : L →ₐ[F] H, (IsScalarTower.toAlgHom F H (ResidueField H)).comp ψ = σ := by
  choose r hr using fun x : L => exists_isRoot_minpoly σ (Algebra.IsSeparable.isSeparable F x)
  have key : ∀ x y : L, ∃ φ : IntermediateField.adjoin F {x, y} →ₐ[F] H,
      ∀ z, φ z = r z := by
    intro x y
    let E := IntermediateField.adjoin F ({x, y} : Set L)
    haveI : FiniteDimensional F E := IntermediateField.finiteDimensional_adjoin
      fun z _ => (Algebra.IsSeparable.isSeparable F z).isIntegral
    obtain ⟨φ, hφ⟩ := exists_algHom_lift_of_finite E (σ.comp E.val)
    exact ⟨φ, fun z => eq_of_isRoot_minpoly σ E.val φ hφ z (hr z).1 (hr z).2.1 (hr z).2.2⟩
  have mem1 : ∀ x y : L, x ∈ IntermediateField.adjoin F ({x, y} : Set L) :=
    fun x y => IntermediateField.subset_adjoin F _ (by simp)
  have mem2 : ∀ x y : L, y ∈ IntermediateField.adjoin F ({x, y} : Set L) :=
    fun x y => IntermediateField.subset_adjoin F _ (by simp)
  refine ⟨{ toFun := r
            map_one' := ?_
            map_mul' := ?_
            map_zero' := ?_
            map_add' := ?_
            commutes' := ?_ }, ?_⟩
  · obtain ⟨φ, hφ⟩ := key 1 1
    simpa using (hφ 1).symm
  · intro x y
    obtain ⟨φ, hφ⟩ := key x y
    have := hφ (⟨x, mem1 x y⟩ * ⟨y, mem2 x y⟩)
    rw [map_mul, hφ, hφ] at this
    exact this.symm
  · obtain ⟨φ, hφ⟩ := key 0 0
    simpa using (hφ 0).symm
  · intro x y
    obtain ⟨φ, hφ⟩ := key x y
    have := hφ (⟨x, mem1 x y⟩ + ⟨y, mem2 x y⟩)
    rw [map_add, hφ, hφ] at this
    exact this.symm
  · intro c
    obtain ⟨φ, hφ⟩ := key 0 0
    simpa using (hφ (algebraMap F _ c)).symm
  · ext x
    exact (hr x).2.1

end HenselLift

section NilpotentComparison

open TensorProduct

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- A module killed modulo a nilpotent ideal is zero: if `(R ⧸ J) ⊗ M = 0` and `J ^ n = 0`, then
`M = J M = ⋯ = J ^ n M = 0`. -/
private theorem subsingleton_of_subsingleton_quotTensor {J : Ideal R} {n : ℕ} (hJ : J ^ n = ⊥)
    (h : Subsingleton ((R ⧸ J) ⊗[R] M)) : Subsingleton M := by
  have h1 : Subsingleton (M ⧸ (J • (⊤ : Submodule R M))) :=
    (TensorProduct.quotTensorEquivQuotSMul M J).symm.subsingleton
  rw [Submodule.Quotient.subsingleton_iff] at h1
  have h2 : ∀ k : ℕ, J ^ k • (⊤ : Submodule R M) = ⊤ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', Submodule.mul_smul, ih, h1]
  have h3 := h2 n
  rw [hJ, Submodule.bot_smul] at h3
  exact (Submodule.subsingleton_iff R).mp (subsingleton_iff_bot_eq_top.mp h3)

/-- **Comparison of jets modulo a nilpotent ideal.** Let `J` be a nilpotent ideal of `R` and
`φ : M → N` a linear map to a flat module which becomes bijective after `(R ⧸ J) ⊗ -`. Then `φ`
is bijective: its cokernel `Q` has `Q = J Q`, and by flatness of `N` its kernel `K` satisfies
`(R ⧸ J) ⊗ K ↪ (R ⧸ J) ⊗ M`, with image killed by the injective map to `(R ⧸ J) ⊗ N`. No
finiteness is needed, since `J` is nilpotent. -/
private theorem bijective_of_bijective_lTensor_quotient [Module.Flat R N] {J : Ideal R} {n : ℕ}
    (hJ : J ^ n = ⊥) (φ : M →ₗ[R] N) (hφ : Function.Bijective (φ.lTensor (R ⧸ J))) :
    Function.Bijective φ := by
  have hsurj : Function.Surjective φ := by
    let g := (LinearMap.range φ).mkQ
    have hex : Function.Exact φ g := LinearMap.exact_iff.mpr (Submodule.ker_mkQ _)
    have hex' := lTensor_exact (R ⧸ J) hex (Submodule.mkQ_surjective _)
    have hg : Function.Surjective (g.lTensor (R ⧸ J)) :=
      LinearMap.lTensor_surjective _ (Submodule.mkQ_surjective _)
    have hsub : Subsingleton ((R ⧸ J) ⊗[R] (N ⧸ LinearMap.range φ)) := by
      refine ⟨fun a b => ?_⟩
      obtain ⟨a, rfl⟩ := hg a
      obtain ⟨b, rfl⟩ := hg b
      obtain ⟨a, rfl⟩ := hφ.2 a
      obtain ⟨b, rfl⟩ := hφ.2 b
      rw [hex'.apply_apply_eq_zero, hex'.apply_apply_eq_zero]
    have := subsingleton_of_subsingleton_quotTensor hJ hsub
    rw [Submodule.Quotient.subsingleton_iff] at this
    exact LinearMap.range_eq_top.mp this
  refine ⟨?_, hsurj⟩
  let K := LinearMap.ker φ
  have hex : Function.Exact K.subtype φ :=
    LinearMap.exact_iff.mpr (Submodule.range_subtype _).symm
  have hinj := LinearMap.lTensor_injective_of_exact_of_flat φ hsurj K.subtype
    K.injective_subtype hex (R ⧸ J)
  have hzero : ∀ x, K.subtype.lTensor (R ⧸ J) x = 0 := by
    intro x
    apply hφ.1
    rw [map_zero, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hex.linearMap_comp_eq_zero,
      LinearMap.lTensor_zero, LinearMap.zero_apply]
  have hsub : Subsingleton ((R ⧸ J) ⊗[R] K) :=
    ⟨fun a b => hinj ((hzero a).trans (hzero b).symm)⟩
  have := subsingleton_of_subsingleton_quotTensor hJ hsub
  rw [← LinearMap.ker_eq_bot]
  exact (Submodule.subsingleton_iff_eq_bot).mp this

/-- Cancelling the base change `R ⊗[A] -` inside `Q ⊗[R] -` is natural in the module. -/
private theorem cancelBaseChange_lTensor_baseChange {A M N : Type*} [CommRing A] [AddCommGroup M]
    [Module A M] [AddCommGroup N] [Module A N]
  (R : Type*) [CommRing R] [Algebra A R] (Q : Type*) [CommRing Q] [Algebra R Q] [Algebra A Q]
  [IsScalarTower A R Q] (ψ : M →ₗ[A] N) (x : Q ⊗[R] (R ⊗[A] M)) :
    TensorProduct.AlgebraTensorModule.cancelBaseChange A R R Q N ((ψ.baseChange R).lTensor Q x) =
    ψ.lTensor Q (TensorProduct.AlgebraTensorModule.cancelBaseChange A R R Q M x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul q x =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r m => simp [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
    | add x y hx hy => simp_all [tmul_add]
  | add x y hx hy => simp_all

/-- **Jets of every order.** If `ψ : M → N` with `N` flat becomes bijective modulo `I`, it is
bijective modulo every power `I ^ n`: apply `bijective_of_bijective_lTensor_quotient` over
`A ⧸ I ^ n` to the nilpotent ideal `I (A ⧸ I ^ n)`. -/
private theorem bijective_lTensor_quotient_pow {A M N : Type*} [CommRing A] [AddCommGroup M]
    [Module A M] [AddCommGroup N] [Module A N]
    [Module.Flat A N] (I : Ideal A) (ψ : M →ₗ[A] N)
    (h : Function.Bijective (ψ.lTensor (A ⧸ I))) (n : ℕ) :
    Function.Bijective (ψ.lTensor (A ⧸ I ^ n)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : Subsingleton (A ⧸ I ^ 0) := by
      rw [pow_zero, Ideal.one_eq_top]; infer_instance
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩
  let R := A ⧸ I ^ n
  let J : Ideal R := I.map (Ideal.Quotient.mkₐ A (I ^ n))
  have hJ : J ^ n = ⊥ := by
    rw [← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker]
    intro x hx
    exact RingHom.mem_ker.mpr (Ideal.Quotient.eq_zero_iff_mem.mpr hx)
  let Q := R ⧸ J
  let e : Q ≃ₐ[A] A ⧸ I := DoubleQuot.quotQuotEquivQuotOfLEₐ A (Ideal.pow_le_self hn.ne')
  have h1 : Function.Bijective (ψ.lTensor Q) := by
    have hc : ⇑(ψ.lTensor Q) = (e.symm.toLinearEquiv.rTensor N) ∘
        (ψ.lTensor (A ⧸ I)) ∘ (e.toLinearEquiv.rTensor M) := by
      funext x
      induction x using TensorProduct.induction_on with
      | zero => simp only [map_zero, Function.comp_apply]
      | tmul q m =>
        simp only [Function.comp_apply, LinearEquiv.rTensor_tmul, LinearMap.lTensor_tmul]
        congr 1
        exact (e.symm_apply_apply q).symm
      | add x y hx hy => simp only [map_add, hx, hy, Function.comp_apply]
    rw [hc]
    exact (LinearEquiv.rTensor N e.symm.toLinearEquiv).bijective.comp
      (h.comp (LinearEquiv.rTensor M e.toLinearEquiv).bijective)
  have h2 : Function.Bijective ((ψ.baseChange R).lTensor Q) := by
    have := (TensorProduct.AlgebraTensorModule.cancelBaseChange A R R Q N).bijective
    have hc : ⇑((ψ.baseChange R).lTensor Q) =
        (TensorProduct.AlgebraTensorModule.cancelBaseChange A R R Q N).symm ∘
          (ψ.lTensor Q) ∘ (TensorProduct.AlgebraTensorModule.cancelBaseChange A R R Q M) := by
      funext x
      apply (TensorProduct.AlgebraTensorModule.cancelBaseChange A R R Q N).injective
      simp only [Function.comp_apply, LinearEquiv.apply_symm_apply]
      exact cancelBaseChange_lTensor_baseChange R Q ψ x
    rw [hc]
    exact (LinearEquiv.bijective _).comp (h1.comp (LinearEquiv.bijective _))
  have h3 := bijective_of_bijective_lTensor_quotient hJ (ψ.baseChange R) h2
  rwa [LinearMap.baseChange_eq_ltensor] at h3

end NilpotentComparison

section CompletionComparison

variable {S T : Type*} [CommRing S] [CommRing T]

open AdicCompletion

/-- The evaluations of an element of the adic completion are compatible. -/
private theorem factorPow_evalₐ (I : Ideal S) {m n : ℕ} (hle : m ≤ n) (x : AdicCompletion I S) :
    Ideal.Quotient.factorPow I hle (evalₐ I n x) = evalₐ I m x := by
  obtain ⟨x, rfl⟩ := AdicCompletion.mk_surjective I S x
  rw [evalₐ_mk, evalₐ_mk, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
  exact AdicCompletion.Ideal.mk_eq_mk I hle x

private theorem map_pow_le_of_map_eq (g : S →+* T) {I : Ideal S} {J : Ideal T} (hIJ : I.map g = J)
    (n : ℕ) : I ^ n ≤ (J ^ n).comap g := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow, hIJ]

private theorem quotientMap_factorPow (g : S →+* T) {I : Ideal S} {J : Ideal T} (hIJ : I.map g = J)
    {m n : ℕ} (hle : m ≤ n) (w : S ⧸ I ^ n) :
    Ideal.quotientMap (J ^ m) g (map_pow_le_of_map_eq g hIJ m) (Ideal.Quotient.factorPow I hle w) =
      Ideal.Quotient.factorPow J hle
        (Ideal.quotientMap (J ^ n) g (map_pow_le_of_map_eq g hIJ n) w) := by
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective w
  rfl

private theorem completionMap_compat (g : S →+* T) {I : Ideal S} {J : Ideal T} (hIJ : I.map g = J)
    {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow J hle).comp
        ((Ideal.quotientMap (J ^ n) g (map_pow_le_of_map_eq g hIJ n)).comp
          (evalₐ I n : AdicCompletion I S →+* S ⧸ I ^ n)) =
      (Ideal.quotientMap (J ^ m) g (map_pow_le_of_map_eq g hIJ m)).comp
        (evalₐ I m : AdicCompletion I S →+* S ⧸ I ^ m) := by
  ext x
  simp only [RingHom.comp_apply, RingHom.coe_coe, ← quotientMap_factorPow g hIJ hle,
    factorPow_evalₐ]

/-- The map of adic completions induced by `g : S → T` with `I T = J`. -/
private noncomputable def completionMap (g : S →+* T) (I : Ideal S) (J : Ideal T)
    (hIJ : I.map g = J) :
    AdicCompletion I S →+* AdicCompletion J T :=
  AdicCompletion.liftRingHom J
    (fun n => (Ideal.quotientMap (J ^ n) g (map_pow_le_of_map_eq g hIJ n)).comp
      (evalₐ I n : AdicCompletion I S →+* S ⧸ I ^ n))
    (fun hle => completionMap_compat g hIJ hle)

private theorem evalₐ_completionMap (g : S →+* T) (I : Ideal S) (J : Ideal T) (hIJ : I.map g = J)
    (n : ℕ) (x : AdicCompletion I S) :
    evalₐ J n (completionMap g I J hIJ x) =
      Ideal.quotientMap (J ^ n) g (map_pow_le_of_map_eq g hIJ n) (evalₐ I n x) := by
  rw [completionMap,
    AdicCompletion.evalₐ_liftRingHom _ _ (fun hle => completionMap_compat g hIJ hle)]
  rfl

private theorem completionMap_of (g : S →+* T) (I : Ideal S) (J : Ideal T) (hIJ : I.map g = J)
    (x : S) : completionMap g I J hIJ (of I S x) = of J T (g x) :=
  ext_evalₐ fun n => by rw [evalₐ_completionMap, evalₐ_of, evalₐ_of, Ideal.quotientMap_mk]

/-- A ring map inducing bijections `S ⧸ I ^ n ≃ T ⧸ J ^ n` for all `n` induces an isomorphism of
the adic completions. -/
private noncomputable def completionEquiv (g : S →+* T) (I : Ideal S) (J : Ideal T)
    (hIJ : I.map g = J)
    (hg : ∀ n, Function.Bijective (Ideal.quotientMap (J ^ n) g (map_pow_le_of_map_eq g hIJ n))) :
    AdicCompletion I S ≃+* AdicCompletion J T :=
  RingEquiv.ofBijective (completionMap g I J hIJ) <| by
    let e := fun n => RingEquiv.ofBijective _ (hg n)
    have he : ∀ n w, e n ((e n).symm w) = w := fun n w => (e n).apply_symm_apply w
    constructor
    · intro x y hxy
      exact ext_evalₐ fun n => (hg n).1 (by
        rw [← evalₐ_completionMap g I J hIJ, ← evalₐ_completionMap g I J hIJ, hxy])
    · intro z
      refine ⟨AdicCompletion.liftRingHom I
        (fun n => ((e n).symm : T ⧸ J ^ n →+* S ⧸ I ^ n).comp
          (evalₐ J n : AdicCompletion J T →+* T ⧸ J ^ n))
        (fun {m n} hle => by
          ext z
          apply (hg m).1
          have h1 := quotientMap_factorPow g hIJ hle ((e n).symm (evalₐ J n z))
          have h2 := he n (evalₐ J n z)
          have h3 := he m (evalₐ J m z)
          simp only [e, RingEquiv.coe_ofBijective] at h2 h3
          simp only [RingHom.comp_apply, RingHom.coe_coe, RingHom.coe_coe]
          rw [h1]
          simp only [e, RingEquiv.coe_ofBijective] at *
          rw [h2, h3, factorPow_evalₐ]) z, ?_⟩
      refine ext_evalₐ fun n => ?_
      rw [evalₐ_completionMap, evalₐ_liftRingHom]
      exact he n _

end CompletionComparison

section QuotientTensor

open TensorProduct

variable {A A' H : Type*} [CommRing A] [CommRing A'] [CommRing H] [Algebra A A'] [Algebra A H]

/-- `(A ⧸ K) ⊗[A] B ≃ B ⧸ K B`. -/
private noncomputable def quotTensorEquivQuotMap (B : Type*) [CommRing B] [Algebra A B]
    (K : Ideal A) :
    ((A ⧸ K) ⊗[A] B) ≃ₗ[A] B ⧸ K.map (algebraMap A B) :=
  TensorProduct.quotTensorEquivQuotSMul B K ≪≫ₗ
    Submodule.quotEquivOfEq _ _ (Ideal.smul_top_eq_map K) ≪≫ₗ
    Submodule.Quotient.restrictScalarsEquiv A (K.map (algebraMap A B))

private theorem quotTensorEquivQuotMap_tmul (B : Type*) [CommRing B] [Algebra A B] (K : Ideal A)
    (r : A) (x : B) :
    quotTensorEquivQuotMap B K (Ideal.Quotient.mk K r ⊗ₜ x) =
      Ideal.Quotient.mk _ (algebraMap A B r * x) := by
  simp [quotTensorEquivQuotMap, Algebra.smul_def]

private theorem map_map_algebraMap_le (ψ : A' →ₐ[A] H) (K : Ideal A) :
    K.map (algebraMap A A') ≤ (K.map (algebraMap A H)).comap (ψ : A' →+* H) := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_map, AlgHom.comp_algebraMap]

/-- The map `A' ⧸ K A' → H ⧸ K H` induced by an `A`-algebra map. -/
private noncomputable def quotMap (ψ : A' →ₐ[A] H) (K : Ideal A) :
    A' ⧸ K.map (algebraMap A A') →+* H ⧸ K.map (algebraMap A H) :=
  Ideal.quotientMap _ (ψ : A' →+* H) (map_map_algebraMap_le ψ K)

private theorem bijective_quotMap_iff (ψ : A' →ₐ[A] H) (K : Ideal A) :
    Function.Bijective (quotMap ψ K) ↔ Function.Bijective (ψ.toLinearMap.lTensor (A ⧸ K)) := by
  have hc : ⇑(ψ.toLinearMap.lTensor (A ⧸ K)) = (quotTensorEquivQuotMap H K).symm ∘
      (quotMap ψ K) ∘ quotTensorEquivQuotMap A' K := by
    funext x
    apply (quotTensorEquivQuotMap H K).injective
    simp only [Function.comp_apply, LinearEquiv.apply_symm_apply]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r x =>
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
      simp only [LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply, quotTensorEquivQuotMap_tmul,
        quotMap, Ideal.quotientMap_mk, RingHom.coe_coe, map_mul, AlgHom.commutes]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [hc]
  refine ⟨fun h => (LinearEquiv.bijective _).comp (h.comp (LinearEquiv.bijective _)), fun h => ?_⟩
  have := ((LinearEquiv.bijective (quotTensorEquivQuotMap H K)).comp h).comp
    (LinearEquiv.bijective (quotTensorEquivQuotMap A' K).symm)
  convert this using 1
  funext x
  simp

/-- **Completion comparison.** Let `ψ : A' → H` be a map of `A`-algebras with `H` flat over `A`,
and `I` an ideal of `A` with `I A' = I'`, `I H = J`, such that `A' ⧸ I A' → H ⧸ I H` is
bijective. Then `ψ` induces an isomorphism of the `I'`-adic completion of `A'` with the
`J`-adic completion of `H`. -/
private theorem exists_completionEquiv [Module.Flat A H] (ψ : A' →ₐ[A] H) (I : Ideal A)
    (I' : Ideal A') (J : Ideal H) (hI' : I.map (algebraMap A A') = I')
    (hJ : I.map (algebraMap A H) = J)
    (hres : Function.Bijective (quotMap ψ I)) :
    ∃ e : AdicCompletion I' A' ≃+* AdicCompletion J H,
      ∀ x, e (AdicCompletion.of I' A' x) = AdicCompletion.of J H (ψ x) := by
  subst hI' hJ
  have hIJ : (I.map (algebraMap A A')).map (ψ : A' →+* H) = I.map (algebraMap A H) := by
    rw [Ideal.map_map, AlgHom.comp_algebraMap]
  have hlev : ∀ n, Function.Bijective (Ideal.quotientMap ((I.map (algebraMap A H)) ^ n)
      (ψ : A' →+* H) (map_pow_le_of_map_eq (ψ : A' →+* H) hIJ n)) := by
    intro n
    have key : ∀ (I1 : Ideal A') (J1 : Ideal H) (h1 : (I ^ n).map (algebraMap A A') = I1)
        (h2 : (I ^ n).map (algebraMap A H) = J1) (hle : I1 ≤ J1.comap (ψ : A' →+* H)),
        Function.Bijective (Ideal.quotientMap J1 (ψ : A' →+* H) hle) := by
      intro I1 J1 h1 h2 hle
      subst h1 h2
      exact (bijective_quotMap_iff ψ (I ^ n)).mpr
        (bijective_lTensor_quotient_pow I ψ.toLinearMap ((bijective_quotMap_iff ψ I).mp hres) n)
    exact key _ _ (Ideal.map_pow _ _ _) (Ideal.map_pow _ _ _) _
  exact ⟨completionEquiv (ψ : A' →+* H) _ _ hIJ hlev,
    fun x => completionMap_of (ψ : A' →+* H) _ _ hIJ x⟩

end QuotientTensor

section TensorComparison

open TensorProduct

/-- In a reduced Artinian ring every element `t` of a prime `q` is killed by an element outside
`q`: if `t ^ (n + 1) y = t ^ n`, then `s = 1 - t y` works. -/
private theorem exists_notMem_mul_eq_zero {T : Type*} [CommRing T] [IsArtinianRing T]
    [IsReduced T] (q : Ideal T) [q.IsPrime] {t : T} (ht : t ∈ q) : ∃ s ∉ q, s * t = 0 := by
  obtain ⟨n, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd t (1 : T)
  simp only [smul_eq_mul, mul_one] at hy
  refine ⟨1 - t * y, fun h => ?_, ?_⟩
  · exact (Ideal.IsPrime.ne_top inferInstance) (q.eq_top_of_isUnit_mem
      (by simpa using q.add_mem h (q.mul_mem_right y ht)) isUnit_one)
  · have : ((1 - t * y) * t) ^ (n + 1) = 0 := by
      have h0 : t ^ n * (1 - t * y) = 0 := by
        rw [mul_sub, mul_one, ← mul_assoc, ← pow_succ, hy, sub_self]
      calc ((1 - t * y) * t) ^ (n + 1) = (t ^ n * (1 - t * y)) * ((1 - t * y) ^ n * t) := by
            rw [mul_pow]; ring
        _ = 0 := by rw [h0, zero_mul]
    exact IsReduced.eq_zero _ ⟨_, this⟩

/-- `E ⊗[F] K` is reduced and Artinian for a finite separable extension `E/F` and any field
`K`. -/
private theorem isReduced_and_isArtinianRing_tensor (F E K : Type*) [Field F] [Field E] [Field K]
    [Algebra F E] [Algebra F K] [Algebra.IsSeparable F E] [FiniteDimensional F E] :
    IsReduced (E ⊗[F] K) ∧ IsArtinianRing (E ⊗[F] K) := by
  haveI := Algebra.FormallyEtale.of_isSeparable F E
  haveI : IsReduced (K ⊗[F] E) := Algebra.FormallyUnramified.isReduced_of_field K _
  haveI : IsArtinianRing (K ⊗[F] E) := IsArtinianRing.of_finite K _
  exact ⟨isReduced_of_injective (Algebra.TensorProduct.comm F E K).toRingHom
      (Algebra.TensorProduct.comm F E K).injective,
    (Algebra.TensorProduct.comm F K E).surjective.isArtinianRing⟩

variable {F A K H : Type*} [Field F] [CommRing A] [IsLocalRing A] [Algebra F A]
  [Field K] [Algebra (ResidueField A) K] [Algebra F K] [IsScalarTower F (ResidueField A) K]
  [CommRing H] [IsLocalRing H] [Algebra A H] [Algebra F H] [IsScalarTower F A H]

/-- Let `T = A ⊗[F] K` with an `A`-algebra map `Θ : T → H` to a local ring, which is local on
`A`, and `q = Θ⁻¹ 𝔪_H`. If the closed fibre `κ(A) ⊗[F] K` is reduced and Artinian, then
`𝔪_A` generates the maximal ideal of `T_q`. -/
private theorem map_maximalIdeal_localization_eq
    [FiniteDimensional F (ResidueField A)] [Algebra.IsSeparable F (ResidueField A)]
    (Θ : A ⊗[F] K →ₐ[A] H) [IsLocalHom (algebraMap A H)] :
    haveI : ((maximalIdeal H).comap (Θ : A ⊗[F] K →+* H)).IsPrime := Ideal.comap_isPrime _ _
    (maximalIdeal A).map (algebraMap A
        (Localization.AtPrime ((maximalIdeal H).comap (Θ : A ⊗[F] K →+* H)))) =
      maximalIdeal (Localization.AtPrime ((maximalIdeal H).comap (Θ : A ⊗[F] K →+* H))) := by
  set q := (maximalIdeal H).comap (Θ : A ⊗[F] K →+* H)
  haveI : q.IsPrime := Ideal.comap_isPrime _ _
  set A' := Localization.AtPrime q
  have hmq : (maximalIdeal A).map (algebraMap A (A ⊗[F] K)) ≤ q := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change Θ (algebraMap A _ a) ∈ maximalIdeal H
    rw [AlgHom.commutes]
    exact map_nonunit (algebraMap A H) a ha
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, IsScalarTower.algebraMap_apply A (A ⊗[F] K) A',
      IsLocalization.AtPrime.to_map_mem_maximal_iff A' q]
    exact hmq (Ideal.mem_map_of_mem _ ha)
  rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap]
  intro t ht
  let I := (maximalIdeal A).map (algebraMap A (A ⊗[F] K))
  let e : ResidueField A ⊗[F] K ≃ₐ[F] (A ⊗[F] K) ⧸ I :=
    Algebra.TensorProduct.quotientTensorEquiv (R := F) F K A (maximalIdeal A)
  obtain ⟨hred, hart⟩ := isReduced_and_isArtinianRing_tensor F (ResidueField A) K
  haveI : IsReduced ((A ⊗[F] K) ⧸ I) :=
    isReduced_of_injective e.symm.toRingHom e.symm.injective
  haveI : IsArtinianRing ((A ⊗[F] K) ⧸ I) := e.surjective.isArtinianRing
  have hker : RingHom.ker (Ideal.Quotient.mk I) ≤ q := by
    rwa [Ideal.mk_ker]
  haveI : (q.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
  obtain ⟨s', hs', hst⟩ := exists_notMem_mul_eq_zero (q.map (Ideal.Quotient.mk I))
    (Ideal.mem_map_of_mem _ ht)
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s'
  have hs : s ∈ q.primeCompl := fun h => hs' (Ideal.mem_map_of_mem _ h)
  have hst' : s * t ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, hst]
  have hu : IsUnit (algebraMap (A ⊗[F] K) A' s) := IsLocalization.map_units A' ⟨s, hs⟩
  rw [Ideal.mem_comap, ← Ideal.unit_mul_mem_iff_mem _ hu, ← map_mul]
  have : I.map (algebraMap (A ⊗[F] K) A') = (maximalIdeal A).map (algebraMap A A') := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  rw [← this]
  exact Ideal.mem_map_of_mem _ hst'

/-- **Completion of the base change to the separable closure.** Let `A` be a local ring
containing a field `F` with `κ(A)/F` finite separable, `K` a separable closure of `κ(A)` and
`H = A^{sh}` the strict henselization with residue field `K`. The Hensel lift `K ↪ H` over `F`
gives `Θ : A ⊗[F] K → H`; with `q = Θ⁻¹ 𝔪_H`, the local ring `A' = (A ⊗[F] K)_q` has completion
isomorphic to `Ĥ` over `A`. -/
private theorem exists_completionEquiv_localization_tensor
    [FiniteDimensional F (ResidueField A)] [Algebra.IsSeparable F (ResidueField A)]
    [IsSepClosure (ResidueField A) K] [IsHenselization A K H] :
    ∃ (q : Ideal (A ⊗[F] K)) (_ : q.IsPrime), q.comap (algebraMap A (A ⊗[F] K)) = maximalIdeal A ∧
      (maximalIdeal A).map (algebraMap A (Localization.AtPrime q)) =
        maximalIdeal (Localization.AtPrime q) ∧
      (∀ z : A ⊗[F] K, ∃ x : K, z - 1 ⊗ₜ x ∈ q) ∧
      ∃ e : AdicCompletion (maximalIdeal (Localization.AtPrime q)) (Localization.AtPrime q) ≃+*
          AdicCompletion (maximalIdeal H) H,
        ∀ a : A, e (AdicCompletion.of _ _ (algebraMap A (Localization.AtPrime q) a)) =
          AdicCompletion.of _ _ (algebraMap A H a) := by
  haveI : HenselianLocalRing H := IsHenselization.henselian A K
  haveI : IsLocalHom (algebraMap A H) := IsHenselization.isLocalHom (L := K)
  haveI : Module.Flat A H := IsHenselization.flat (L := K)
  haveI : Algebra.IsSeparable (ResidueField A) K := IsSepClosure.separable
  haveI : Algebra.IsSeparable F K := Algebra.IsSeparable.trans F (ResidueField A) K
  obtain ⟨ε, hε⟩ := IsHenselization.exists_residueFieldEquiv (R := A) (L := K) (Rh := H)
  let σ : K →ₐ[F] ResidueField H :=
    { toRingHom := (ε : K →+* ResidueField H)
      commutes' := fun c => by
        have h1 : algebraMap F K c =
            algebraMap (ResidueField A) K (residue A (algebraMap F A c)) := by
          rw [IsScalarTower.algebraMap_apply F (ResidueField A) K]; rfl
        have h2 : algebraMap F (ResidueField H) c =
            residue H (algebraMap A H (algebraMap F A c)) := by
          rw [← IsScalarTower.algebraMap_apply F A H]; rfl
        change ε (algebraMap F K c) = _
        rw [h1, hε, h2] }
  obtain ⟨ψ, hψ⟩ := exists_algHom_lift σ
  let Θ : A ⊗[F] K →ₐ[A] H :=
    Algebra.TensorProduct.lift (Algebra.ofId A H) ψ (fun _ _ => Commute.all _ _)
  set q := (maximalIdeal H).comap (Θ : A ⊗[F] K →+* H)
  haveI : q.IsPrime := Ideal.comap_isPrime _ _
  let A' := Localization.AtPrime q
  have hunits : ∀ y : q.primeCompl, IsUnit (Θ y) := fun y =>
    (IsLocalRing.notMem_maximalIdeal).mp y.2
  let Θ' : A' →ₐ[A] H := IsLocalization.liftAlgHom (M := q.primeCompl) (f := Θ) hunits
  have hΘ' : ∀ t, Θ' (algebraMap (A ⊗[F] K) A' t) = Θ t := fun t =>
    IsLocalization.lift_eq hunits t
  have hmax := map_maximalIdeal_localization_eq (F := F) (K := K) Θ
  have hres : Function.Bijective (quotMap Θ' (maximalIdeal A)) := by
    constructor
    · apply Ideal.quotientMap_injective'
      rw [IsHenselization.map_maximalIdeal (L := K), hmax]
      exact IsLocalRing.le_maximalIdeal (fun h => by
        have : (1 : A') ∈ Ideal.comap (Θ' : A' →+* H) (maximalIdeal H) := by rw [h]; trivial
        simp at this)
    · intro z
      obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective z
      obtain ⟨x, hx⟩ := ε.surjective (residue H h)
      refine ⟨Ideal.Quotient.mk _ (algebraMap (A ⊗[F] K) A' (1 ⊗ₜ x)), ?_⟩
      rw [quotMap, Ideal.quotientMap_mk, Ideal.Quotient.eq,
        IsHenselization.map_maximalIdeal (L := K),
        ← residue_eq_zero_iff, map_sub, sub_eq_zero]
      change residue H (Θ' _) = _
      rw [hΘ']
      simp only [Θ, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      rw [← hx]
      exact DFunLike.congr_fun hψ x
  obtain ⟨e, he⟩ := exists_completionEquiv Θ' (maximalIdeal A) _ _ hmax
    (IsHenselization.map_maximalIdeal (L := K)) hres
  refine ⟨q, inferInstance, ?_, hmax, fun z => ?_, e, fun a => by rw [he, AlgHom.commutes]⟩
  swap
  · obtain ⟨x, hx⟩ := ε.surjective (residue H (Θ z))
    refine ⟨x, ?_⟩
    change Θ (z - 1 ⊗ₜ x) ∈ maximalIdeal H
    rw [← residue_eq_zero_iff, map_sub, map_sub, sub_eq_zero]
    simp only [Θ, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    rw [← hx]
    exact (DFunLike.congr_fun hψ x).symm
  rw [← IsLocalRing.maximalIdeal_comap (algebraMap A H)]
  ext a
  change Θ (algebraMap A _ a) ∈ maximalIdeal H ↔ _
  rw [AlgHom.commutes]
  rfl

end TensorComparison

section TensorNormality

open TensorProduct IntermediateField

/-- A separable algebraic extension `E/F` is ind-étale: it is the directed union of its
intermediate fields of finite degree, each finite separable, hence étale, over `F`. -/
private theorem ind_etale_of_isSeparable (F E : Type v) [Field F] [Field E] [Algebra F E]
    [Algebra.IsSeparable F E] :
    (CommAlgCat.etale.{v} F).ind.{v} (CommAlgCat.of F E) := by
  rw [← StacksDraft.indEtale_iff]
  let ι := {K : IntermediateField F E // FiniteDimensional F K}
  have : Nonempty ι := ⟨⟨⊥, inferInstance⟩⟩
  refine StacksDraft.indEtale_of_directed_etale_subalgebras (ι := ι)
    (fun K => K.1.toSubalgebra) ?_ (fun K => ?_) ?_
  · intro K L
    have := K.2
    have := L.2
    exact ⟨⟨K.1 ⊔ L.1, inferInstance⟩, toSubalgebra_le_toSubalgebra.mpr le_sup_left,
      toSubalgebra_le_toSubalgebra.mpr le_sup_right⟩
  · have := K.2
    have : Algebra.IsSeparable F K.1 := Algebra.isSeparable_tower_bot_of_isSeparable F K.1 E
    have : Algebra.FormallyEtale F K.1 := Algebra.FormallyEtale.of_isSeparable F K.1
    have : Algebra.FinitePresentation F K.1 :=
      Algebra.FinitePresentation.of_finiteType.mp inferInstance
    exact ({} : Algebra.Etale F K.1)
  · exact eq_top_iff.mpr fun x _ => Algebra.mem_iSup_of_mem (S := fun K : ι => K.1.toSubalgebra)
      (⟨F⟮x⟯, adjoin.finiteDimensional (Algebra.IsSeparable.isSeparable F x).isIntegral⟩ : ι)
      (IntermediateField.mem_adjoin_simple_self F x)

/-- An integrally closed domain is a normal ring: its localizations at primes are integrally
closed domains. -/
private theorem isNormalRing_of_isIntegrallyClosed (A : Type*) [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] : IsNormalRing A := fun p _ =>
  ⟨inferInstance, isIntegrallyClosed_of_isLocalization _ p.primeCompl
    p.primeCompl_le_nonZeroDivisors⟩

/-- **Normality of the separable base change.** For an integrally closed domain `A` containing a
field `F` and a separable algebraic extension `K/F`, every localization of `A ⊗[F] K` at a prime
is an integrally closed domain: `A ⊗[F] K` is ind-étale over `A`, and normality ascends along
ind-étale maps. -/
private theorem isDomain_and_isIntegrallyClosed_localization_tensor {F A K : Type v} [Field F]
    [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Algebra F A] [Field K] [Algebra F K]
    [Algebra.IsSeparable F K] (q : Ideal (A ⊗[F] K)) [q.IsPrime] :
    IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) :=
  isNormalRing_tensorProduct_of_ind_etale A (isNormalRing_of_isIntegrallyClosed A)
    (ind_etale_of_isSeparable F K) q

end TensorNormality

section FiniteTypeModel

/-- Two minimal primes inside `q₀` coincide when `R_{q₀}` is a domain. -/
private theorem eq_of_minimalPrimes_le {R : Type*} [CommRing R] (q₀ : Ideal R) [q₀.IsPrime]
    [IsDomain (Localization.AtPrime q₀)] {m m' : Ideal R} (hm : m ∈ minimalPrimes R)
    (hm' : m' ∈ minimalPrimes R) (hmq : m ≤ q₀) (hm'q : m' ≤ q₀) : m = m' := by
  have key : ∀ {m : Ideal R}, m ∈ minimalPrimes R → m ≤ q₀ →
      (⊥ : Ideal (Localization.AtPrime q₀)).comap (algebraMap R _) = m := by
    intro m hm hmq
    have hmp : m.IsPrime := hm.1.1
    have hdis : Disjoint (q₀.primeCompl : Set R) m :=
      Set.disjoint_left.mpr fun _ hx hxm => hx (hmq hxm)
    have h1 := IsLocalization.under_map_of_isPrime_disjoint q₀.primeCompl
      (Localization.AtPrime q₀) hmp hdis
    have hle : (⊥ : Ideal (Localization.AtPrime q₀)).comap (algebraMap R _) ≤ m := by
      rw [← h1]; exact Ideal.comap_mono bot_le
    have : ((⊥ : Ideal (Localization.AtPrime q₀)).comap (algebraMap R _)).IsPrime :=
      Ideal.comap_isPrime _ _
    exact le_antisymm hle (hm.2 ⟨this, bot_le⟩ hle)
  exact (key hm hmq).symm.trans (key hm' hm'q)

/-- **Cutting out one component.** In a reduced Noetherian ring `R` whose localization at a prime
`q₀` is a domain, some `g ∉ q₀` makes `R_h` a domain for every multiple `h ∉ q₀` of `g`: take `g`
in every minimal prime other than the unique one inside `q₀`. -/
private theorem exists_isDomain_away {R : Type*} [CommRing R] [IsNoetherianRing R] [IsReduced R]
    (q₀ : Ideal R) [q₀.IsPrime] [IsDomain (Localization.AtPrime q₀)] :
    ∃ g ∉ q₀, ∀ h, g ∣ h → h ∉ q₀ → IsDomain (Localization.Away h) := by
  classical
  obtain ⟨m₀, hm₀, hm₀q⟩ := Ideal.exists_minimalPrimes_le (bot_le : (⊥ : Ideal R) ≤ q₀)
  have hfin : (minimalPrimes R).Finite := minimalPrimes.finite_of_isNoetherianRing R
  have hsel : ∀ m ∈ minimalPrimes R, m ≠ m₀ → ∃ x ∈ m, x ∉ q₀ := by
    intro m hm hne
    by_contra h
    push Not at h
    exact hne (eq_of_minimalPrimes_le q₀ hm hm₀ h hm₀q)
  choose! x hxm hxq using hsel
  let T := hfin.toFinset.filter (· ≠ m₀)
  let g := ∏ m ∈ T, x m
  have hg : g ∉ q₀ := by
    intro h
    obtain ⟨m, hmT, hm⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    simp only [T, Finset.mem_filter, Set.Finite.mem_toFinset] at hmT
    exact hxq m hmT.1 hmT.2 hm
  have hgm : ∀ m ∈ minimalPrimes R, m ≠ m₀ → g ∈ m := by
    intro m hm hne
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem x (by simp [T, hm, hne] : m ∈ T)
    rw [show g = _ from hc]
    exact Ideal.mul_mem_right _ _ (hxm m hm hne)
  refine ⟨g, hg, fun h hdvd hh => ?_⟩
  replace hgm : ∀ m ∈ minimalPrimes R, m ≠ m₀ → h ∈ m := fun m hm hne => by
    obtain ⟨c, rfl⟩ := hdvd
    exact Ideal.mul_mem_right _ _ (hgm m hm hne)
  let L := Localization.Away h
  have hm₀p : m₀.IsPrime := hm₀.1.1
  have hdis : Disjoint (Submonoid.powers h : Set R) m₀ := by
    rw [Set.disjoint_left]
    rintro _ ⟨n, rfl⟩ hx
    exact hh (hm₀q (hm₀p.mem_of_pow_mem n hx))
  let M := m₀.map (algebraMap R L)
  have hMp : M.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers h) L m₀
    hm₀p hdis
  have hMle : ∀ P : Ideal L, P.IsPrime → M ≤ P := by
    intro P hP
    obtain ⟨m, hm, hmP⟩ := Ideal.exists_minimalPrimes_le
      (bot_le : (⊥ : Ideal R) ≤ P.comap (algebraMap R L))
    by_cases hne : m = m₀
    · subst hne
      exact Ideal.map_le_iff_le_comap.mpr hmP
    · exfalso
      have := hmP (hgm m hm hne)
      rw [Ideal.mem_comap] at this
      exact hP.ne_top (Ideal.eq_top_of_isUnit_mem _ this
        (IsLocalization.Away.algebraMap_isUnit h))
  have hM : M = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have : z ∈ nilradical L := by
      rw [nilradical, Ideal.radical_eq_sInf, Submodule.mem_sInf]
      rintro P ⟨-, hP⟩
      exact hMle P hP hz
    rwa [nilradical_eq_zero] at this
  rw [hM] at hMp
  exact IsDomain.of_bot_isPrime L

/-- Normality at every prime is invariant under ring isomorphisms. -/
private theorem isDomain_and_isIntegrallyClosed_of_ringEquiv {T T' : Type*} [CommRing T]
    [CommRing T']
    (φ : T ≃+* T')
    (h : ∀ (Q : Ideal T') [Q.IsPrime], IsDomain (Localization.AtPrime Q) ∧
      IsIntegrallyClosed (Localization.AtPrime Q))
    (Q : Ideal T) [Q.IsPrime] :
    IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q) := by
  let Q' : Ideal T' := Q.comap (φ.symm : T' →+* T)
  haveI : Q'.IsPrime := Ideal.comap_isPrime _ _
  have hM : Q.primeCompl.map (φ : T →* T') = Q'.primeCompl := by
    ext x
    simp only [Submonoid.mem_map, Ideal.mem_primeCompl_iff, Q', Ideal.mem_comap]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨φ.symm x, hx, by simp⟩
  let ψ : Localization.AtPrime Q ≃+* Localization.AtPrime Q' :=
    IsLocalization.ringEquivOfRingEquiv _ _ φ hM
  obtain ⟨h1, h2⟩ := h Q'
  exact ⟨ψ.injective.isDomain (ψ : Localization.AtPrime Q →+* Localization.AtPrime Q'),
    IsIntegrallyClosed.of_equiv ψ.symm⟩

/-- A localization of a ring that is normal at every prime is normal at every prime. -/
private theorem isDomain_and_isIntegrallyClosed_of_isLocalization {T S : Type*} [CommRing T]
    [CommRing S] [Algebra T S] (M : Submonoid T) [IsLocalization M S]
    (h : ∀ (Q : Ideal T) [Q.IsPrime], IsDomain (Localization.AtPrime Q) ∧
      IsIntegrallyClosed (Localization.AtPrime Q))
    (Q : Ideal S) [Q.IsPrime] :
    IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q) := by
  have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
    (Localization.AtPrime Q) Q
  let ψ := (IsLocalization.algEquiv (Q.comap (algebraMap T S)).primeCompl
    (Localization.AtPrime (Q.comap (algebraMap T S))) (Localization.AtPrime Q)).toRingEquiv
  obtain ⟨h1, h2⟩ := h (Q.comap (algebraMap T S))
  exact ⟨Function.Injective.isDomain (ψ.symm : Localization.AtPrime Q →+*
    Localization.AtPrime (Q.comap (algebraMap T S))) ψ.symm.injective,
    IsIntegrallyClosed.of_equiv ψ⟩

end FiniteTypeModel

section PolynomialLocalization

/-- A finitely generated `k`-algebra `B` with a prime `p` has finitely many elements `t i` whose
images in `κ(p)`, the residue field of a localization `A` of `B` at `p`, form a transcendence
basis over `k`: choose one inside the image of a finite generating set. -/
private theorem exists_finite_isTranscendenceBasis_residue (k B : Type*) (A : Type v) [Field k]
    [CommRing B]
    [Algebra k B] [Algebra.FiniteType k B] (p : Ideal B) [p.IsPrime] [CommRing A] [Algebra B A]
    [IsLocalization.AtPrime A p] [Algebra k A] [IsScalarTower k B A] [IsLocalRing A] :
    ∃ (ι : Type v) (_ : Finite ι) (t : ι → B),
      IsTranscendenceBasis k (residue A ∘ algebraMap B A ∘ t) := by
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra k B).FG)
  let φ : B →ₐ[k] ResidueField A := (IsScalarTower.toAlgHom k A (ResidueField A)).comp
    (IsScalarTower.toAlgHom k B A)
  let S : Set (ResidueField A) := φ '' (s : Set B)
  have hmem : ∀ b : B, φ b ∈ Algebra.adjoin k S := by
    intro b
    have hb : b ∈ Algebra.adjoin k (s : Set B) := hs ▸ Algebra.mem_top
    rw [show S = φ '' (s : Set B) from rfl, Algebra.adjoin_image]
    exact ⟨b, hb, rfl⟩
  have : Algebra.IsAlgebraic (Algebra.adjoin k S) (ResidueField A) := by
    constructor
    intro x
    obtain ⟨a, rfl⟩ := residue_surjective x
    obtain ⟨b, c, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl a
    have hc : φ c ≠ 0 := by
      change residue A (algebraMap B A c) ≠ 0
      rw [residue_ne_zero_iff_isUnit]
      exact IsLocalization.map_units A c
    refine ⟨Polynomial.C ⟨φ c, hmem c⟩ * Polynomial.X - Polynomial.C ⟨φ b, hmem b⟩, ?_, ?_⟩
    · intro h
      have := congrArg (Polynomial.coeff · 1) h
      simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X, Polynomial.coeff_C,
        one_ne_zero, ite_false, sub_zero, Polynomial.coeff_zero] at this
      exact hc (congrArg Subtype.val this)
    · have h1 : residue A (IsLocalization.mk' A b c) * φ c = φ b := by
        change _ = residue A (algebraMap B A b)
        rw [← IsLocalization.mk'_spec A b c, map_mul]; rfl
      simp only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
      change φ c * _ - φ b = 0
      rw [mul_comm, h1, sub_self]
  obtain ⟨t, hts, ht⟩ := exists_isTranscendenceBasis_subset (R := k) S
  have hfin : t.Finite := ((s.finite_toSet.image φ).subset hts)
  have hlift : ∀ x : t, ∃ b ∈ (s : Set B), φ b = x := fun x => hts x.2
  choose b _ hb using hlift
  refine ⟨t, hfin.to_subtype, b, ?_⟩
  have : residue A ∘ algebraMap B A ∘ b = Subtype.val := funext hb
  rwa [this]

variable {k : Type v} [Field k] {B : Type v} [CommRing B] [Algebra k B] {ι : Type v}

/-- The image in `B` of the nonzero polynomials in `t`. -/
private noncomputable def polySubmonoid (t : ι → B) : Submonoid B :=
  (nonZeroDivisors (MvPolynomial ι k)).map (MvPolynomial.aeval t : MvPolynomial ι k →ₐ[k] B)

/-- Nonzero polynomials in lifts of algebraically independent residues lie outside `p`. -/
private theorem polySubmonoid_le {A : Type v} [CommRing A] [Algebra B A] [Algebra k A]
    [IsScalarTower k B A] (p : Ideal B) [p.IsPrime] [IsLocalization.AtPrime A p] [IsLocalRing A]
    {t : ι → B} (ht : AlgebraicIndependent k (residue A ∘ algebraMap B A ∘ t)) :
    polySubmonoid (k := k) t ≤ p.primeCompl := by
  rintro _ ⟨q, hq, rfl⟩
  have hu : IsUnit (MvPolynomial.aeval (algebraMap B A ∘ t) q) :=
    isUnit_aeval_of_algebraicIndependent_residue ht (nonZeroDivisors.ne_zero hq)
  have : MvPolynomial.aeval (algebraMap B A ∘ t) q =
      algebraMap B A (MvPolynomial.aeval t q) :=
    (MvPolynomial.comp_aeval_apply t (IsScalarTower.toAlgHom k B A) q).symm
  rw [this] at hu
  exact (IsLocalization.AtPrime.isUnit_to_map_iff A p _).mp hu

variable (t : ι → B)

/-- The map `k(t) → T⁻¹B`, for `T` the image of the nonzero polynomials in `t`. -/
private noncomputable def fieldToLocalization :
    FractionRing (MvPolynomial ι k) →+* Localization (polySubmonoid (k := k) t) :=
  IsLocalization.lift (M := nonZeroDivisors (MvPolynomial ι k))
    (g := (algebraMap B (Localization (polySubmonoid (k := k) t))).comp
      (MvPolynomial.aeval t : MvPolynomial ι k →ₐ[k] B).toRingHom)
    (fun q => IsLocalization.map_units _ (⟨_, ⟨q, q.2, rfl⟩⟩ : polySubmonoid (k := k) t))

private theorem fieldToLocalization_algebraMap (q : MvPolynomial ι k) :
    fieldToLocalization (k := k) t (algebraMap _ _ q) =
      algebraMap B (Localization (polySubmonoid (k := k) t)) (MvPolynomial.aeval t q) :=
  IsLocalization.lift_eq _ q

/-- `T⁻¹B` is of finite type over `k(t)`: it is generated by the image of generators of `B`. -/
private theorem finiteType_localization [Algebra.FiniteType k B] :
    letI := (fieldToLocalization (k := k) t).toAlgebra
    Algebra.FiniteType (FractionRing (MvPolynomial ι k))
      (Localization (polySubmonoid (k := k) t)) := by
  classical
  letI := (fieldToLocalization (k := k) t).toAlgebra
  set L := Localization (polySubmonoid (k := k) t)
  set F := FractionRing (MvPolynomial ι k)
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out (R := k) (A := B))
  refine ⟨⟨s.image (algebraMap B L), ?_⟩⟩
  rw [eq_top_iff]
  rintro x -
  obtain ⟨b, ⟨_, ⟨q, hq, rfl⟩⟩, rfl⟩ := IsLocalization.exists_mk'_eq (polySubmonoid (k := k) t) x
  have hb : ∀ b : B, algebraMap B L b ∈ Algebra.adjoin F (↑(s.image (algebraMap B L)) : Set L) := by
    intro b
    have hb : b ∈ Algebra.adjoin k (s : Set B) := hs ▸ Algebra.mem_top
    induction hb using Algebra.adjoin_induction with
    | mem x hx => exact Algebra.subset_adjoin (by simpa using ⟨x, hx, rfl⟩)
    | algebraMap c =>
      have : algebraMap B L (algebraMap k B c) =
          algebraMap F L (algebraMap (MvPolynomial ι k) F (MvPolynomial.C c)) := by
        rw [RingHom.algebraMap_toAlgebra, fieldToLocalization_algebraMap, MvPolynomial.aeval_C]
      rw [this]
      exact Subalgebra.algebraMap_mem _ _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  have hinv : IsLocalization.mk' L b (⟨_, ⟨q, hq, rfl⟩⟩ : polySubmonoid (k := k) t) =
      algebraMap F L (IsLocalization.mk' F 1 (⟨q, hq⟩ : nonZeroDivisors _)) * algebraMap B L b := by
    rw [IsLocalization.mk'_eq_iff_eq_mul]
    have h1 : algebraMap B L (MvPolynomial.aeval t q) = algebraMap F L (algebraMap _ F q) := by
      rw [RingHom.algebraMap_toAlgebra, fieldToLocalization_algebraMap]
    simp only
    rw [h1, mul_comm (algebraMap F L _), mul_assoc, ← map_mul, IsLocalization.mk'_spec, map_one,
      map_one,
      mul_one]
  rw [hinv]
  exact mul_mem (Subalgebra.algebraMap_mem _ _) (hb b)

end PolynomialLocalization

section LocalUnramified

/-- A field extension in characteristic zero is formally smooth. -/
private theorem formallySmooth_of_charZero (K L : Type*) [Field K] [Field L] [Algebra K L]
    [CharZero K] : Algebra.FormallySmooth K L := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis K L
  have := hs.isAlgebraic_field
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  have : CharZero (IntermediateField.adjoin K (Set.range ((↑) : s → L))) :=
    charZero_of_injective_algebraMap (algebraMap K _).injective
  have : Algebra.IsSeparable (IntermediateField.adjoin K (Set.range ((↑) : s → L))) L :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable hs.1

variable {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] [Algebra A B]
  [IsLocalHom (algebraMap A B)]

private theorem map_maximalIdeal_le : (maximalIdeal A).map (algebraMap A B) ≤ maximalIdeal B :=
  Ideal.map_le_iff_le_comap.mpr fun a ha => map_nonunit (algebraMap A B) a ha

/-- **A formally unramified local homomorphism is unramified at the closed point.** If
`A → B` is a formally unramified local homomorphism, `B` is Noetherian and `κ(B)` is formally
smooth over `κ(A)`, then `𝔪_A B = 𝔪_B`. -/
private theorem map_maximalIdeal_eq_of_formallyUnramified [IsNoetherianRing B]
    [Algebra.FormallyUnramified A B]
    [Algebra.FormallySmooth (ResidueField A) (ResidueField B)] :
    (maximalIdeal A).map (algebraMap A B) = maximalIdeal B := by
  set I := (maximalIdeal A).map (algebraMap A B)
  set m := maximalIdeal B
  set N := I ⊔ m ^ 2
  let S := B ⧸ N
  let J : Ideal S := m.map (Ideal.Quotient.mk N)
  have hJ : J ^ 2 = ⊥ := by
    rw [← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
    exact le_sup_right
  have hJn : IsNilpotent J := ⟨2, hJ⟩
  have hmA : ∀ a ∈ maximalIdeal A, algebraMap A S a = 0 := fun a ha => by
    rw [IsScalarTower.algebraMap_apply A B S, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ha)
  letI : Algebra (ResidueField A) S :=
    (Ideal.Quotient.lift (maximalIdeal A) (algebraMap A S) hmA).toAlgebra
  have : IsScalarTower A (ResidueField A) S := IsScalarTower.of_algebraMap_eq fun a => rfl
  have hmB : ∀ b ∈ m, (Ideal.Quotient.mk J (Ideal.Quotient.mk N b)) = 0 := fun b hb =>
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hb)
  let ψ₀ : ResidueField B →+* S ⧸ J :=
    Ideal.Quotient.lift m ((Ideal.Quotient.mk J).comp (Ideal.Quotient.mk N)) hmB
  let ψ : ResidueField B →ₐ[ResidueField A] S ⧸ J :=
    { ψ₀ with
      commutes' := fun c => by
        obtain ⟨a, rfl⟩ := residue_surjective c
        change ψ₀ (algebraMap (ResidueField A) (ResidueField B) (residue A a)) = _
        rw [ResidueField.algebraMap_residue]
        rfl }
  let s := Algebra.FormallySmooth.lift J hJn ψ
  let g₁ : B →ₐ[A] S := Ideal.Quotient.mkₐ A N
  let g₂ : B →ₐ[A] S := (s.restrictScalars A).comp (IsScalarTower.toAlgHom A B (ResidueField B))
  have hg : g₁ = g₂ := by
    refine Algebra.FormallyUnramified.ext J hJn fun x => ?_
    change _ = Ideal.Quotient.mk J (s (residue B x))
    rw [Algebra.FormallySmooth.mk_lift]
    rfl
  have hle : m ≤ I ⊔ m • m := by
    intro x hx
    have h1 : g₁ x = 0 := by
      rw [hg]
      change s (residue B x) = 0
      rw [(residue_eq_zero_iff x).mpr hx, map_zero]
    have : x ∈ N := Ideal.Quotient.eq_zero_iff_mem.mp h1
    rwa [Ideal.smul_eq_mul, ← sq]
  refine le_antisymm map_maximalIdeal_le ?_
  exact Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian m)
    (by rw [jacobson_eq_maximalIdeal ⊥ bot_ne_top]) hle

/-- A flat local homomorphism of Noetherian local rings with `𝔪_A B = 𝔪_B` preserves the Krull
dimension: the closed fibre is a field. -/
private theorem ringKrullDim_eq_of_map_maximalIdeal_eq [IsNoetherianRing A] [IsNoetherianRing B]
    [Module.Flat A B] (h : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B) :
    ringKrullDim B = ringKrullDim A := by
  rw [ringKrullDim_eq_add_ringKrullDim_closedFibre A B inferInstance]
  have : ringKrullDim (ClosedFibre A B) = 0 := by
    unfold ClosedFibre
    rw [h]
    exact @ringKrullDim_eq_zero_of_field _ (Ideal.Quotient.field _)
  rw [this, add_zero]

/-- A regular system of parameters of `A` maps to one of `B` under a flat local homomorphism of
Noetherian local rings with `𝔪_A B = 𝔪_B`. -/
private theorem IsRegularSystemOfParameters.map [IsNoetherianRing A] [IsNoetherianRing B]
    [Module.Flat A B] (h : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B) {n : ℕ}
    {z : Fin n → A} (hz : IsRegularSystemOfParameters z) :
    IsRegularSystemOfParameters (algebraMap A B ∘ z) := by
  refine ⟨?_, (ringKrullDim_eq_of_map_maximalIdeal_eq h).trans hz.2⟩
  rw [Set.range_comp, ← Ideal.map_span, hz.1, h]

/-- A flat local homomorphism `A → B` of Noetherian local rings with `𝔪_A B = 𝔪_B` preserves the
dimension of every quotient: `dim B ⧸ I B = dim A ⧸ I`. -/
private theorem ringKrullDim_quotient_map_eq_of_flat [IsNoetherianRing A] [IsNoetherianRing B]
    [Module.Flat A B]
    (h : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B) (I : Ideal A) (hI : I ≠ ⊤) :
    ringKrullDim (B ⧸ I.map (algebraMap A B)) = ringKrullDim (A ⧸ I) := by
  have hIm : I ≤ maximalIdeal A := le_maximalIdeal hI
  have hIB : I.map (algebraMap A B) ≠ ⊤ := fun h' => by
    have : I.map (algebraMap A B) ≤ maximalIdeal B := h ▸ Ideal.map_mono hIm
    exact (IsLocalRing.maximalIdeal.isMaximal B).ne_top (top_le_iff.mp (h' ▸ this))
  haveI : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  haveI : Nontrivial (B ⧸ I.map (algebraMap A B)) := Ideal.Quotient.nontrivial_iff.mpr hIB
  haveI : IsLocalRing (A ⧸ I) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  haveI : IsLocalRing (B ⧸ I.map (algebraMap A B)) :=
    IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  have hcomp : (algebraMap (A ⧸ I) (B ⧸ I.map (algebraMap A B))).comp (Ideal.Quotient.mk I) =
      (Ideal.Quotient.mk _).comp (algebraMap A B) := rfl
  have hmax : (maximalIdeal (A ⧸ I)).map (algebraMap (A ⧸ I) (B ⧸ I.map (algebraMap A B))) =
      maximalIdeal (B ⧸ I.map (algebraMap A B)) := by
    rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk I)
        Ideal.Quotient.mk_surjective, Ideal.map_map, hcomp, ← Ideal.map_map, h,
      IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective]
  haveI : IsLocalHom (algebraMap (A ⧸ I) (B ⧸ I.map (algebraMap A B))) :=
    ((local_hom_TFAE _).out 1 3).mpr hmax.le
  haveI : Module.Flat (A ⧸ I) (B ⧸ I.map (algebraMap A B)) :=
    Module.Flat.of_linearEquiv
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).toLinearEquiv
  exact ringKrullDim_eq_of_map_maximalIdeal_eq hmax

/-- **Regularity ascends along flat formally unramified local maps.** If `A → B` is a flat,
formally unramified local homomorphism of Noetherian local rings with `κ(B)/κ(A)` formally smooth
and `A` is regular, then `B` is regular: `𝔪_A B = 𝔪_B`, so the closed fibre is a field. -/
private theorem isRegularLocalRing_of_formallyUnramified [IsNoetherianRing A] [IsNoetherianRing B]
    [Module.Flat A B] [Algebra.FormallyUnramified A B]
    [Algebra.FormallySmooth (ResidueField A) (ResidueField B)] (hA : IsRegularLocalRing A) :
    IsRegularLocalRing B := by
  have h := map_maximalIdeal_eq_of_formallyUnramified (A := A) (B := B)
  refine isRegularLocalRing_of_flat_of_closedFibre A B hA ?_ inferInstance
  unfold ClosedFibre
  rw [h]
  letI := Ideal.Quotient.field (maximalIdeal B)
  infer_instance

end LocalUnramified

section TransportAlgebra

open TensorProduct TopologicalSpace

section UnramifiedOrder

/-- Along a local homomorphism of discrete valuation rings with `𝔪_R R' = 𝔪_{R'}`, the order of
vanishing is preserved: a uniformizer maps to a uniformizer. -/
private theorem ordFrac_map_eq {R R' K K' : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    [Field K] [Field K'] [Algebra R K] [IsFractionRing R K] [Algebra R' K'] [IsFractionRing R' K']
    (φ : R →+* R') (hφ : (maximalIdeal R).map φ = maximalIdeal R') (ψ : K →+* K')
    (hψ : ∀ a, ψ (algebraMap R K a) = algebraMap R' K' (φ a)) (x : K) :
    Ring.ordFrac R' (ψ x) = Ring.ordFrac R x := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hϖ' : Irreducible (φ ϖ) := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer, ← hφ,
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.map_span,
      Set.image_singleton]
  have key : ∀ a : R, a ≠ 0 → Ring.ordFrac R' (algebraMap R' K' (φ a)) =
      Ring.ordFrac R (algebraMap R K a) := by
    intro a ha
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
    simp only [map_mul, map_pow, Ring.ordFrac_irreducible hϖ, Ring.ordFrac_irreducible hϖ',
      Ring.ordFrac_of_isUnit (u.isUnit), Ring.ordFrac_of_isUnit (u.isUnit.map φ)]
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  by_cases ha : a = 0
  · simp [ha]
  rw [map_div₀, map_div₀, map_div₀, hψ, hψ, key a ha, key b hb0]

/-- The local ring at a point of codimension one of a normal locally Noetherian integral scheme is
a discrete valuation ring. -/
private theorem isDiscreteValuationRing_stalk_of_coheight {X : Scheme.{v}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {z : X} (hz : Order.coheight z = 1) :
    IsDiscreteValuationRing (X.presheaf.stalk z) := by
  have h5 : IsNoetherianRing (X.presheaf.stalk z) ∧ IsLocalRing (X.presheaf.stalk z) ∧
      IsDomain (X.presheaf.stalk z) ∧ IsIntegrallyClosed (X.presheaf.stalk z) ∧
      ringKrullDim (X.presheaf.stalk z) = 1 :=
    ⟨inferInstance, inferInstance, inferInstance, IsNormal.stalk_normal z, by
      rw [ringKrullDim_stalk_eq_coheight, hz]; rfl⟩
  obtain ⟨_, h⟩ := ((isDiscreteValuationRing_tfae (X.presheaf.stalk z)).out 5 1).mp h5
  exact h

/-- Orders of rational functions are preserved along a dominant morphism `f` at a point `y` of
codimension one with `f y` of codimension one, when `𝔪_{f y}` generates `𝔪_y`. -/
private theorem ord_functionFieldMap_eq {X Y : Scheme.{v}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (f : Y ⟶ X) [IsDominant f]
    {y : Y} (hy : Order.coheight y = 1) (hfy : Order.coheight (f y) = 1)
    (hmax : (maximalIdeal (X.presheaf.stalk (f y))).map (f.stalkMap y).hom =
      maximalIdeal (Y.presheaf.stalk y)) (g : X.functionField) :
    Y.ord (functionFieldMap f g) y = X.ord g (f y) := by
  by_cases hg : g = 0
  · simp [hg]
  have := isDiscreteValuationRing_stalk_of_coheight hy
  have := isDiscreteValuationRing_stalk_of_coheight hfy
  have h := ordFrac_map_eq (K := X.functionField) (K' := Y.functionField) (f.stalkMap y).hom hmax
    (functionFieldMap f) (MMP.Mori.functionFieldMap_algebraMap_stalk f y) g
  have hg' : functionFieldMap f g ≠ 0 := (map_ne_zero _).mpr hg
  rw [Scheme.ord_eq_iff hy hg', Scheme.ordHom]
  have h2 := (Scheme.ord_eq_iff hfy hg (n := X.ord g (f y))).mp rfl
  rw [Scheme.ordHom] at h2
  exact h.trans h2

/-- For a flat local homomorphism `A → A'` of local domains, an element of `Frac A` whose image
lies in `A'` lies in `A`: `A' ∩ Frac A = A`, by faithful flatness. -/
private theorem mem_range_of_map_mem_range {A A' K K' : Type*} [CommRing A] [IsLocalRing A]
    [IsDomain A] [CommRing A'] [IsLocalRing A'] [Field K] [Field K'] [Algebra A K]
    [IsFractionRing A K] [Algebra A' K'] [IsFractionRing A' K'] [Algebra A A']
    [IsLocalHom (algebraMap A A')] [Module.Flat A A'] (ψ : K →+* K')
    (hψ : ∀ a, ψ (algebraMap A K a) = algebraMap A' K' (algebraMap A A' a)) {x : K}
    (hx : ψ x ∈ Set.range (algebraMap A' K')) : x ∈ Set.range (algebraMap A K) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) x
  obtain ⟨a', ha'⟩ := hx
  have hbK : algebraMap A K b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have : Module.FaithfullyFlat A A' := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hbψ : ψ (algebraMap A K b) ≠ 0 := (map_ne_zero ψ).mpr hbK
  have h1 : algebraMap A A' a = algebraMap A A' b * a' := by
    apply IsFractionRing.injective A' K'
    rw [map_mul, ha', ← hψ, ← hψ, map_div₀, mul_div_cancel₀ _ hbψ]
  have hmem : a ∈ ((Ideal.span {b}).map (algebraMap A A')).comap (algebraMap A A') := by
    rw [Ideal.mem_comap, Ideal.map_span, Set.image_singleton, h1]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  rw [Ideal.comap_map_eq_self_of_faithfullyFlat, Ideal.mem_span_singleton'] at hmem
  obtain ⟨c, rfl⟩ := hmem
  exact ⟨c, by rw [map_mul, mul_div_cancel_right₀ _ hbK]⟩

end UnramifiedOrder

section KaehlerBasis

/-- Extension of a linearly independent family of `e` vectors to a basis `Fin.append v w`. -/
private theorem exists_append_basis {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] {e r : ℕ} (hV : Module.finrank F V = e + r) {v : Fin e → V}
    (hv : LinearIndependent F v) :
    ∃ w : Fin r → V, LinearIndependent F (Fin.append v w) ∧
      Submodule.span F (Set.range (Fin.append v w)) = ⊤ := by
  set N := Submodule.span F (Set.range v)
  have hN : Module.finrank F N = e := by
    rw [finrank_span_eq_card hv, Fintype.card_fin]
  have hQ : Module.finrank F (V ⧸ N) = r := by
    have := Submodule.finrank_quotient_add_finrank N
    omega
  let bQ := Module.finBasisOfFinrankEq F (V ⧸ N) hQ
  choose w hw using fun j => Submodule.mkQ_surjective N (bQ j)
  have hspan : Submodule.span F (Set.range (Fin.append v w)) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : N.mkQ x ∈ Submodule.span F (Set.range bQ) := bQ.span_eq ▸ Submodule.mem_top
    have hle : N ≤ Submodule.span F (Set.range (Fin.append v w)) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨Fin.castAdd r i, Fin.append_left v w i⟩
    have hmap : Submodule.span F (Set.range bQ) ≤
        (Submodule.span F (Set.range (Fin.append v w))).map N.mkQ := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact ⟨w j, Submodule.subset_span ⟨Fin.natAdd e j, Fin.append_right v w j⟩, hw j⟩
    obtain ⟨y, hy, hxy⟩ := hmap hx
    have : x - y ∈ N := by
      rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, hxy, sub_self]
    have := Submodule.add_mem _ (hle this) hy
    simpa using this
  refine ⟨w, ?_, hspan⟩
  apply linearIndependent_of_top_le_span_of_card_eq_finrank hspan.ge
  simp [hV]

/-- A family in a finite flat module over a local ring whose reduction is a basis is a basis. -/
private theorem exists_basis_of_residue {R M ι : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Flat R M] [Module.Finite R M] (v : ι → M)
    (hli : LinearIndependent (ResidueField R) (TensorProduct.mk R (ResidueField R) M 1 ∘ v))
    (hsp : Submodule.span (ResidueField R)
      (Set.range (TensorProduct.mk R (ResidueField R) M 1 ∘ v)) = ⊤) :
    ∃ b : Module.Basis ι R M, ⇑b = v := by
  let bk := Module.Basis.mk hli hsp.ge
  have hbij : Function.Bijective (Finsupp.linearCombination (ResidueField R)
      (TensorProduct.mk R (ResidueField R) M 1 ∘ v)) := by
    have : Finsupp.linearCombination (ResidueField R)
        (TensorProduct.mk R (ResidueField R) M 1 ∘ v) = bk.repr.symm.toLinearMap := by
      ext i; simp [bk]
    rw [this]; exact bk.repr.symm.bijective
  have h := Module.IsLocalRing.linearCombination_bijective_of_flat v hbij
  refine ⟨Module.Basis.ofRepr (LinearEquiv.ofBijective _ h).symm, ?_⟩
  ext i
  rw [Module.Basis.coe_ofRepr]
  simp [LinearEquiv.symm_symm]

/-- A spanning family of a module over a local ring spans its reduction. -/
private theorem span_range_mk_residue_eq_top {R M ι : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] {v : ι → M} (hv : Submodule.span R (Set.range v) = ⊤) :
    Submodule.span (ResidueField R)
      (Set.range (TensorProduct.mk R (ResidueField R) M 1 ∘ v)) = ⊤ := by
  have h : Submodule.span R (Set.range (TensorProduct.mk R (ResidueField R) M 1 ∘ v)) = ⊤ := by
    rw [Set.range_comp, ← Submodule.map_span, hv, Submodule.map_top, LinearMap.range_eq_top]
    exact TensorProduct.mk_surjective R M (ResidueField R) Ideal.Quotient.mk_surjective
  rw [eq_top_iff]
  intro x _
  exact Submodule.span_le_restrictScalars R (ResidueField R) _ (h ▸ Submodule.mem_top)

variable {k κ A A' : Type*} [Field k] [Field κ] [Algebra k κ]
  [CommRing A] [Algebra k A]
  [CommRing A'] [Algebra κ A'] [Algebra k A'] [IsScalarTower k κ A']
  [Algebra A A'] [IsScalarTower k A A']

private theorem kaehler_map_map_eq (ω : Ω[A⁄k]) :
    KaehlerDifferential.map k κ A' A' (KaehlerDifferential.map k k A A' ω) =
      KaehlerDifferential.map k κ A A' ω := by
  have h : ((KaehlerDifferential.map k κ A' A').restrictScalars A).comp
      (KaehlerDifferential.map k k A A') = KaehlerDifferential.map k κ A A' := by
    apply Derivation.liftKaehlerDifferential_unique
    ext a
    simp
  exact LinearMap.congr_fun h ω

/-- For a formally unramified `A → A'`, the image of `Ω_{A/k}` spans `Ω_{A'/κ}` over `A'`. -/
private theorem span_range_kaehler_map_eq_top [Algebra.FormallyUnramified A A'] :
    Submodule.span A' (Set.range (KaehlerDifferential.map k κ A A')) = ⊤ := by
  have hsurj : Function.Surjective (KaehlerDifferential.mapBaseChange k A A') := by
    rw [← LinearMap.range_eq_top, KaehlerDifferential.range_mapBaseChange]
    exact LinearMap.ker_eq_top.mpr (Subsingleton.elim _ _)
  rw [eq_top_iff, ← KaehlerDifferential.span_range_derivation, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  obtain ⟨y, hy⟩ := hsurj (KaehlerDifferential.D k A' x)
  have : KaehlerDifferential.D κ A' x =
      KaehlerDifferential.map k κ A' A' (KaehlerDifferential.mapBaseChange k A A' y) := by
    rw [hy, KaehlerDifferential.map_D, Algebra.algebraMap_self, RingHom.id_apply]
  rw [this]
  clear hy this
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a ω =>
    rw [KaehlerDifferential.mapBaseChange_tmul, map_smul, kaehler_map_map_eq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨ω, rfl⟩)
  | add y z hy hz => rw [map_add, map_add]; exact add_mem hy hz

/-- **Adapted bases of the differentials.** Let `A → A'` be a formally unramified local map, with
`Ω_{A/k}` free of rank `e + r` and `Ω_{A'/κ}` free of rank `r`, and let `t₁, …, t_e ∈ A` map into
`κ` with `dt₁, …, dt_e` independent modulo `𝔪_A`. Then `Ω_{A/k}` has a basis
`dt₁, …, dt_e, α₁, …, α_r` whose last `r` members map to a basis of `Ω_{A'/κ}`. -/
private theorem exists_basis_append_and_basis_map [IsLocalRing A] [IsLocalRing A']
    [Algebra.FormallyUnramified A A'] [Module.Free A Ω[A⁄k]] [Module.Finite A Ω[A⁄k]]
    [Module.Free A' Ω[A'⁄κ]] [Module.Finite A' Ω[A'⁄κ]] {e r : ℕ}
    (hrk : Module.finrank A Ω[A⁄k] = e + r) (hrk' : Module.finrank A' Ω[A'⁄κ] = r)
    (t : Fin e → A) (ht : ∀ i, algebraMap A A' (t i) ∈ Set.range (algebraMap κ A'))
    (hli : LinearIndependent (ResidueField A)
      (fun i => (1 : ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (t i))) :
    ∃ (s : Module.Basis (Fin (e + r)) A Ω[A⁄k]) (s' : Module.Basis (Fin r) A' Ω[A'⁄κ]),
      (∀ i, s (Fin.castAdd r i) = KaehlerDifferential.D k A (t i)) ∧
      ∀ j, s' j = KaehlerDifferential.map k κ A A' (s (Fin.natAdd e j)) := by
  classical
  set M := Ω[A⁄k]
  have hfin : Module.finrank (ResidueField A) (ResidueField A ⊗[A] M) = e + r := by
    rw [Module.finrank_baseChange, hrk]
  obtain ⟨w, hwli, hwsp⟩ := exists_append_basis hfin hli
  choose α hα using fun j => TensorProduct.mk_surjective A M (ResidueField A)
    Ideal.Quotient.mk_surjective (w j)
  have hred : TensorProduct.mk A (ResidueField A) M 1 ∘
      Fin.append (fun i => KaehlerDifferential.D k A (t i)) α =
      Fin.append (fun i => (1 : ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (t i)) w := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · simp
    · simp [← hα j]
  obtain ⟨s, hs⟩ := exists_basis_of_residue _ (hred ▸ hwli) (hred ▸ hwsp)
  have hθt : ∀ i, KaehlerDifferential.map k κ A A' (KaehlerDifferential.D k A (t i)) = 0 := by
    intro i
    obtain ⟨c, hc⟩ := ht i
    rw [KaehlerDifferential.map_D, ← hc, Derivation.map_algebraMap]
  have hspan : Submodule.span A' (Set.range (fun j => KaehlerDifferential.map k κ A A' (α j))) =
      ⊤ := by
    rw [eq_top_iff, ← span_range_kaehler_map_eq_top (k := k) (κ := κ) (A := A) (A' := A'),
      Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ Submodule.span A (Set.range s) := s.span_eq ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      refine Fin.addCases (fun i => ?_) (fun j => ?_) i
      · rw [hs, Fin.append_left, hθt]; exact zero_mem _
      · rw [hs, Fin.append_right]; exact Submodule.subset_span ⟨j, rfl⟩
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul a y _ hy =>
      rw [map_smul, ← algebraMap_smul A']
      exact Submodule.smul_mem _ _ hy
  have hfin' : Module.finrank (ResidueField A') (ResidueField A' ⊗[A'] Ω[A'⁄κ]) = r := by
    rw [Module.finrank_baseChange, hrk']
  have hsp' := span_range_mk_residue_eq_top hspan
  obtain ⟨s', hs'⟩ := exists_basis_of_residue _
    (linearIndependent_of_top_le_span_of_card_eq_finrank hsp'.ge (by simp [hfin'])) hsp'
  refine ⟨s, s', fun i => by rw [hs, Fin.append_left], fun j => by rw [hs, hs', Fin.append_right]⟩

end KaehlerBasis

section DifferentialsOfFields

/-- A formally smooth `S → T` makes `T ⊗[S] Ω_{S/R} → Ω_{T/R}` injective. -/
private theorem mapBaseChange_injective_of_formallySmooth (R S T : Type*) [CommRing R]
    [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra.FormallySmooth S T] :
    Function.Injective (KaehlerDifferential.mapBaseChange R S T) := by
  have : Subsingleton (Algebra.H1Cotangent S T) := ((Algebra.formallySmooth_iff S T).mp ‹_›).2
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨x, rfl⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange R S T x).mp hx
  rw [Subsingleton.elim x 0, map_zero]

/-- In characteristic zero, algebraically independent elements of a field have linearly
independent differentials. -/
private theorem linearIndependent_D_of_algebraicIndependent {k K ι : Type*} [Field k] [CharZero k]
    [Field K] [Algebra k K] {s : ι → K} (hs : AlgebraicIndependent k s) :
    LinearIndependent K (fun i => KaehlerDifferential.D k K (s i)) := by
  classical
  let P := MvPolynomial ι k
  let L := FractionRing P
  let ψ : L →+* K := IsLocalization.lift (M := nonZeroDivisors P)
    (g := (MvPolynomial.aeval s : P →ₐ[k] K).toRingHom) (fun p => by
      refine IsUnit.mk0 _ ?_
      intro h
      exact nonZeroDivisors.ne_zero p.2 (hs.eq_zero_of_aeval_eq_zero _ h))
  letI : Algebra L K := ψ.toAlgebra
  have hψ : ∀ p : P, algebraMap L K (algebraMap P L p) = MvPolynomial.aeval s p :=
    fun p => IsLocalization.lift_eq _ p
  haveI : IsScalarTower k L K := IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply k P L, hψ, MvPolynomial.algebraMap_eq,
      MvPolynomial.aeval_C]
  haveI : Algebra.FormallyEtale P L := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors P)
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap k L).injective
  haveI : Algebra.FormallySmooth L K := formallySmooth_of_charZero L K
  let bL : Module.Basis ι L Ω[L⁄k] :=
    ((KaehlerDifferential.mvPolynomialBasis k ι).baseChange L).map
      (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k P L)
  have hbL : ∀ i, bL i = KaehlerDifferential.D k L (algebraMap P L (MvPolynomial.X i)) := by
    intro i
    have : KaehlerDifferential.mvPolynomialBasis k ι i =
        KaehlerDifferential.D k (MvPolynomial ι k) (MvPolynomial.X i) := by
      apply (KaehlerDifferential.mvPolynomialBasis k ι).repr.injective
      rw [Module.Basis.repr_self, KaehlerDifferential.mvPolynomialBasis_repr_D_X]
    simp only [bL, Module.Basis.map_apply, Module.Basis.baseChange_apply,
      KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply]
    rw [KaehlerDifferential.mapBaseChange_tmul, one_smul, this, KaehlerDifferential.map_D]
  let bK := bL.baseChange K
  have h := bK.linearIndependent.map' _
    (LinearMap.ker_eq_bot.mpr (mapBaseChange_injective_of_formallySmooth k L K))
  have he : (fun i => KaehlerDifferential.D k K (s i)) =
      KaehlerDifferential.mapBaseChange k L K ∘ bK := by
    funext i
    simp [bK, hbL, hψ]
  rwa [he]

/-- In characteristic zero, elements of a local ring with algebraically independent residues have
differentials independent modulo the maximal ideal. -/
private theorem linearIndependent_tmul_D_of_algebraicIndependent {k A ι : Type*} [Field k]
    [CharZero k] [CommRing A] [IsLocalRing A] [Algebra k A] {t : ι → A}
    (ht : AlgebraicIndependent k (residue A ∘ t)) :
    LinearIndependent (ResidueField A)
      (fun i => (1 : ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (t i)) := by
  have h := linearIndependent_D_of_algebraicIndependent ht
  refine LinearIndependent.of_comp (KaehlerDifferential.mapBaseChange k A (ResidueField A)) ?_
  convert h using 1
  funext i
  simp only [Function.comp_apply, KaehlerDifferential.mapBaseChange_tmul, one_smul,
    KaehlerDifferential.map_D]
  rfl

end DifferentialsOfFields

section TopFormsDeterminant

/-- A vector-valued alternating map is determined by its value on a basis. -/
private theorem alternatingMap_apply_eq_det_smul {R M N ι : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] [Fintype ι] [DecidableEq ι]
    (e : Module.Basis ι R M) (f : M [⋀^ι]→ₗ[R] N) (v : ι → M) : f v = e.det v • f e := by
  have : f = e.det.smulRight (f e) := by
    refine Module.Basis.ext_alternating e fun i h => ?_
    let σ : Equiv.Perm ι := Equiv.ofBijective i (Finite.injective_iff_bijective.1 h)
    change f (e ∘ σ) = (e.det.smulRight (f e)) (e ∘ σ)
    simp [AlternatingMap.map_perm, Module.Basis.det_self, AlternatingMap.smulRight_apply,
      smul_smul]
  conv_lhs => rw [this]
  rfl

/-- The top exterior power of a free module of rank `n` is generated by the wedge of a basis. -/
private theorem span_ιMulti_basis_eq_top {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {n : ℕ} (s : Module.Basis (Fin n) R M) :
    Submodule.span R {exteriorPower.ιMulti R n (⇑s)} = ⊤ := by
  rw [eq_top_iff, ← exteriorPower.ιMulti_span R n M, Submodule.span_le]
  rintro _ ⟨v, rfl⟩
  rw [SetLike.mem_coe, alternatingMap_apply_eq_det_smul s (exteriorPower.ιMulti R n) v]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- The wedge of a basis of a finite free module over a field is nonzero in the top exterior
power. -/
private theorem ιMulti_basis_ne_zero {K M : Type*} [Field K] [AddCommGroup M] [Module K M] {n : ℕ}
    (s : Module.Basis (Fin n) K M) : exteriorPower.ιMulti K n (⇑s) ≠ 0 := by
  classical
  intro h
  haveI : Module.Finite K M := Module.Finite.of_basis s
  have hrk : Module.finrank K (⋀[K]^n M) = 1 := by
    rw [exteriorPower.finrank_eq, Module.finrank_eq_card_basis s, Fintype.card_fin, Nat.choose_self]
  have hsp := (exteriorPower.ιMulti_span K n M)
  have htb : (⊤ : Submodule K (⋀[K]^n M)) = ⊥ := by
    rw [← hsp, Submodule.span_eq_bot]
    rintro _ ⟨v, rfl⟩
    rw [alternatingMap_apply_eq_det_smul s (exteriorPower.ιMulti K n) v, h, smul_zero]
  haveI : Nontrivial (⋀[K]^n M) := Module.nontrivial_of_finrank_pos (by rw [hrk]; exact one_pos)
  obtain ⟨x, hx⟩ := exists_ne (0 : ⋀[K]^n M)
  have hx' : x ∈ (⊥ : Submodule K (⋀[K]^n M)) := htb ▸ Submodule.mem_top
  exact hx ((Submodule.mem_bot K).mp hx')

/-- The determinant of a matrix of the form `[[1, B], [0, Q]]` is the determinant of `Q`. -/
private theorem det_eq_det_bottomRight {R : Type*} [CommRing R] {e r : ℕ}
    (M : Matrix (Fin (e + r)) (Fin (e + r)) R)
    (h1 : ∀ i j, M (Fin.castAdd r i) (Fin.castAdd r j) = if i = j then 1 else 0)
    (h0 : ∀ i j, M (Fin.natAdd e i) (Fin.castAdd r j) = 0) :
    M.det = (Matrix.of fun i j => M (Fin.natAdd e i) (Fin.natAdd e j)).det := by
  rw [← Matrix.det_reindex_self finSumFinEquiv.symm, ← Matrix.fromBlocks_toBlocks
    (Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm M)]
  have hA : (Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm M).toBlocks₁₁ = 1 := by
    ext i j
    simp [Matrix.toBlocks₁₁, h1, Matrix.one_apply]
  have hC : (Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm M).toBlocks₂₁ = 0 := by
    ext i j
    simp [Matrix.toBlocks₂₁, h0]
  rw [hA, hC, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul]
  rfl

variable {k κ K K' : Type*} [Field k] [Field κ] [Algebra k κ] [Field K] [Algebra k K]
  [Field K'] [Algebra κ K'] [Algebra k K'] [IsScalarTower k κ K'] [Algebra K K']
  [IsScalarTower k K K']

/-- **The determinant of the contracted basis.** If the bases `sK`, `b` of `Ω_{K/k}` share their
first `e` vectors, killed by `π : Ω_{K/k} → Ω_{K'/κ}`, and `π` maps the last `r` vectors of `sK`
to a basis `sK'` of `Ω_{K'/κ}`, then the determinant of `π` of the last `r` vectors of `b` in
`sK'` is the image of the determinant of `b` in `sK`. -/
private theorem det_kaehler_map_eq {e r : ℕ} (sK b : Module.Basis (Fin (e + r)) K Ω[K⁄k])
    (sK' : Module.Basis (Fin r) K' Ω[K'⁄κ])
    (hcast : ∀ i, b (Fin.castAdd r i) = sK (Fin.castAdd r i))
    (hπ0 : ∀ i, KaehlerDifferential.map k κ K K' (sK (Fin.castAdd r i)) = 0)
    (hπ : ∀ j, KaehlerDifferential.map k κ K K' (sK (Fin.natAdd e j)) = sK' j) :
    sK'.det (fun j => KaehlerDifferential.map k κ K K' (b (Fin.natAdd e j))) =
      algebraMap K K' (sK.det b) := by
  classical
  set Q : Matrix (Fin r) (Fin r) K :=
    Matrix.of fun i j => sK.repr (b (Fin.natAdd e j)) (Fin.natAdd e i)
  have hexp : ∀ j, KaehlerDifferential.map k κ K K' (b (Fin.natAdd e j)) =
      ∑ i, algebraMap K K' (Q i j) • sK' i := by
    intro j
    conv_lhs => rw [← sK.sum_repr (b (Fin.natAdd e j))]
    rw [map_sum, Fin.sum_univ_add]
    simp only [map_smul, hπ0, smul_zero, Finset.sum_const_zero, zero_add, hπ, Q, Matrix.of_apply,
      algebraMap_smul]
  have h2 : sK'.toMatrix (fun j => KaehlerDifferential.map k κ K K' (b (Fin.natAdd e j))) =
      Q.map (algebraMap K K') := by
    ext i j
    rw [Module.Basis.toMatrix_apply, hexp, Module.Basis.repr_sum_self, Matrix.map_apply]
  have h3 := RingHom.map_det (algebraMap K K') Q
  rw [RingHom.mapMatrix_apply] at h3
  rw [Module.Basis.det_apply, h2, ← h3, Module.Basis.det_apply]
  congr 1
  rw [det_eq_det_bottomRight]
  · rfl
  · intro i j
    rw [Module.Basis.toMatrix_apply, hcast, Module.Basis.repr_self, Finsupp.single_apply]
    simp [eq_comm]
  · intro i j
    rw [Module.Basis.toMatrix_apply, hcast, Module.Basis.repr_self, Finsupp.single_apply]
    simp only [ite_eq_right_iff, one_ne_zero, imp_false]
    intro h
    have := congrArg Fin.val h
    simp only [Fin.coe_castAdd, Fin.coe_natAdd] at this
    omega

end TopFormsDeterminant

section UnramifiedMorphism

variable {Z Z' : Scheme.{v}} (φ : Z' ⟶ Z)

/-- For a formally unramified morphism with residue fields of characteristic zero, the maximal
ideal of `𝒪_{Z, φ z'}` generates that of `𝒪_{Z', z'}`. -/
private theorem map_maximalIdeal_stalkMap_eq [FormallyUnramified φ] [IsLocallyNoetherian Z']
    (z' : Z') [CharZero (ResidueField (Z.presheaf.stalk (φ z')))] :
    (maximalIdeal (Z.presheaf.stalk (φ z'))).map (φ.stalkMap z').hom =
      maximalIdeal (Z'.presheaf.stalk z') := by
  letI := (φ.stalkMap z').hom.toAlgebra
  haveI : Algebra.FormallyUnramified (Z.presheaf.stalk (φ z')) (Z'.presheaf.stalk z') :=
    FormallyUnramified.stalkMap φ z'
  haveI : IsLocalHom (algebraMap (Z.presheaf.stalk (φ z')) (Z'.presheaf.stalk z')) :=
    inferInstanceAs (IsLocalHom (φ.stalkMap z').hom)
  haveI : Algebra.FormallySmooth (ResidueField (Z.presheaf.stalk (φ z')))
      (ResidueField (Z'.presheaf.stalk z')) := formallySmooth_of_charZero _ _
  exact map_maximalIdeal_eq_of_formallyUnramified

/-- A flat, formally unramified morphism with residue fields of characteristic zero preserves
codimensions of points. -/
private theorem coheight_map_eq [Flat φ] [FormallyUnramified φ] [IsLocallyNoetherian Z]
    [IsLocallyNoetherian Z'] (z' : Z') [CharZero (ResidueField (Z.presheaf.stalk (φ z')))] :
    Order.coheight (φ z') = Order.coheight z' := by
  letI := (φ.stalkMap z').hom.toAlgebra
  haveI : IsLocalHom (algebraMap (Z.presheaf.stalk (φ z')) (Z'.presheaf.stalk z')) :=
    inferInstanceAs (IsLocalHom (φ.stalkMap z').hom)
  haveI : Module.Flat (Z.presheaf.stalk (φ z')) (Z'.presheaf.stalk z') := Flat.stalkMap φ z'
  have h := ringKrullDim_eq_of_map_maximalIdeal_eq (map_maximalIdeal_stalkMap_eq φ z')
  rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight] at h
  exact_mod_cast h.symm

end UnramifiedMorphism

section StructureMaps

/-- The stalk maps of a morphism over `Spec κ ⟶ Spec k` are compatible with the structure maps. -/
private theorem stalkMap_algebraMap_eq {k κ : Type v} [Field k] [Field κ] (g : k →+* κ)
    {Z Z' : Scheme.{v}} (sZ : Z ⟶ Spec (.of k)) (sZ' : Z' ⟶ Spec (.of κ)) (φ : Z' ⟶ Z)
    (hφ : φ ≫ sZ = sZ' ≫ Spec.map (CommRingCat.ofHom g)) (z' : Z') (c : k) :
    (φ.stalkMap z').hom (letI := stalkAlgebra sZ (φ z'); algebraMap k _ c) =
      (letI := stalkAlgebra sZ' z'; algebraMap κ _ (g c)) := by
  have h : (Scheme.ΓSpecIso (.of k)).inv ≫ sZ.appTop ≫
      Z.presheaf.germ ⊤ (φ z') (Opens.mem_top _) ≫ φ.stalkMap z' =
      CommRingCat.ofHom g ≫ (Scheme.ΓSpecIso (.of κ)).inv ≫ sZ'.appTop ≫
        Z'.presheaf.germ ⊤ z' (Opens.mem_top _) := by
    have e1 : sZ.appTop ≫ Z.presheaf.germ ⊤ (φ z') (Opens.mem_top _) ≫ φ.stalkMap z' =
        (φ ≫ sZ).appTop ≫ Z'.presheaf.germ ⊤ z' (Opens.mem_top _) := by
      simp only [Scheme.Hom.comp_appTop, Category.assoc, Scheme.Hom.germ_stalkMap]
      rfl
    rw [e1, hφ, Scheme.Hom.comp_appTop, ← Category.assoc, ← Category.assoc,
      ← Scheme.ΓSpecIso_inv_naturality]
    simp only [Category.assoc]
  exact congrArg (fun f => CommRingCat.Hom.hom f c) h

end StructureMaps

section LocalComparison

variable {k κ A A' K K' : Type*} [Field k] [Field κ] [Algebra k κ]
  [CommRing A] [IsLocalRing A] [Algebra k A]
  [CommRing A'] [IsLocalRing A'] [Algebra κ A'] [Algebra k A'] [IsScalarTower k κ A']
  [Algebra A A'] [IsScalarTower k A A'] [Algebra.FormallyUnramified A A']
  [Field K] [Algebra k K] [Algebra A K] [IsScalarTower k A K] [IsFractionRing A K]
  [Field K'] [Algebra κ K'] [Algebra k K'] [IsScalarTower k κ K'] [Algebra A' K']
  [IsScalarTower κ A' K'] [IsFractionRing A' K']
  [Algebra K K'] [IsScalarTower k K K'] [Algebra A K'] [IsScalarTower A K K']
  [IsScalarTower A A' K']

omit [IsLocalRing A] [IsLocalRing A'] [Algebra.FormallyUnramified A A'] [IsFractionRing A K]
  [IsFractionRing A' K'] in
private theorem kaehler_map_comm (ω : Ω[A⁄k]) :
    KaehlerDifferential.map k κ K K' (KaehlerDifferential.map k k A K ω) =
      KaehlerDifferential.map κ κ A' K' (KaehlerDifferential.map k κ A A' ω) := by
  have hω : ω ∈ Submodule.span A (Set.range (KaehlerDifferential.D k A)) :=
    (KaehlerDifferential.span_range_derivation k A).symm ▸ Submodule.mem_top
  induction hω using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    simp only [KaehlerDifferential.map_D]
    rw [← IsScalarTower.algebraMap_apply A K K', ← IsScalarTower.algebraMap_apply A A' K']
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul a x _ hx =>
    have e1 : KaehlerDifferential.map k k A K (a • x) =
        algebraMap A K a • KaehlerDifferential.map k k A K x := by
      rw [map_smul, algebraMap_smul]
    have e2 : KaehlerDifferential.map k κ A A' (a • x) =
        algebraMap A A' a • KaehlerDifferential.map k κ A A' x := by
      rw [map_smul, algebraMap_smul]
    rw [e1, e2, map_smul, map_smul, hx, ← algebraMap_smul K' (algebraMap A K a),
      ← algebraMap_smul K' (algebraMap A A' a), ← IsScalarTower.algebraMap_apply A K K',
      ← IsScalarTower.algebraMap_apply A A' K']

/-- **Adapted bases over the fraction fields.** In the setting of
`exists_basis_append_and_basis_map`, the adapted bases of `Ω_{A/k}` and `Ω_{A'/κ}` induce bases
`sK` of `Ω_{K/k}` and `sK'` of `Ω_{K'/κ}` with `sK = dt₁, …, dt_e, …`, `π (dtᵢ) = 0` and
`π (sK (e + j)) = sK' j`, for `π : Ω_{K/k} → Ω_{K'/κ}`. -/
private theorem exists_adapted_bases [Module.Free A Ω[A⁄k]] [Module.Finite A Ω[A⁄k]]
    [Module.Free A' Ω[A'⁄κ]] [Module.Finite A' Ω[A'⁄κ]] {e r : ℕ}
    (hrk : Module.finrank A Ω[A⁄k] = e + r) (hrk' : Module.finrank A' Ω[A'⁄κ] = r)
    (t : Fin e → A) (ht : ∀ i, algebraMap A A' (t i) ∈ Set.range (algebraMap κ A'))
    (hli : LinearIndependent (ResidueField A)
      (fun i => (1 : ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (t i))) :
    ∃ (s : Module.Basis (Fin (e + r)) A Ω[A⁄k]) (s' : Module.Basis (Fin r) A' Ω[A'⁄κ])
      (sK : Module.Basis (Fin (e + r)) K Ω[K⁄k]) (sK' : Module.Basis (Fin r) K' Ω[K'⁄κ]),
      (∀ i, sK i = KaehlerDifferential.map k k A K (s i)) ∧
      (∀ j, sK' j = KaehlerDifferential.map κ κ A' K' (s' j)) ∧
      (∀ i, sK (Fin.castAdd r i) = KaehlerDifferential.D k K (algebraMap A K (t i))) ∧
      (∀ i, KaehlerDifferential.map k κ K K' (sK (Fin.castAdd r i)) = 0) ∧
      ∀ j, KaehlerDifferential.map k κ K K' (sK (Fin.natAdd e j)) = sK' j := by
  obtain ⟨s, s', hs, hs'⟩ := exists_basis_append_and_basis_map (κ := κ) hrk hrk' t ht hli
  haveI : Algebra.FormallyEtale A K := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors A)
  haveI : Algebra.FormallyEtale A' K' :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors A')
  let sK := (KaehlerDifferential.isBaseChange_of_formallyEtale k A K).basis s
  let sK' := (KaehlerDifferential.isBaseChange_of_formallyEtale κ A' K').basis s'
  have hsK : ∀ i, sK i = KaehlerDifferential.map k k A K (s i) := fun i =>
    IsBaseChange.basis_apply _ _ i
  have hsK' : ∀ j, sK' j = KaehlerDifferential.map κ κ A' K' (s' j) := fun j =>
    IsBaseChange.basis_apply _ _ j
  have hcast : ∀ i, sK (Fin.castAdd r i) = KaehlerDifferential.D k K (algebraMap A K (t i)) := by
    intro i
    rw [hsK, hs, KaehlerDifferential.map_D]
  refine ⟨s, s', sK, sK', hsK, hsK', hcast, fun i => ?_, fun j => ?_⟩
  · obtain ⟨c, hc⟩ := ht i
    rw [hcast, KaehlerDifferential.map_D, ← IsScalarTower.algebraMap_apply A K K',
      IsScalarTower.algebraMap_apply A A' K', ← hc, ← IsScalarTower.algebraMap_apply κ A' K',
      Derivation.map_algebraMap]
  · rw [hsK, kaehler_map_comm (A' := A'), ← hs', hsK']

/-- **Comparison of the orders of the adapted top forms.** Let `A → A'` be a formally unramified
local map with `Ω_{A/k}` free of rank `e + r`, `Ω_{A'/κ}` free of rank `r`, and `t₁, …, t_e ∈ A`
mapping into `κ` with residues having independent differentials. For a basis `b` of `Ω_{K/k}`
starting with `dt₁, …, dt_e`, the order along `A` of `∧ b` equals the order along `A'` of
`∧ π(b_{e+1}), …, π(b_{e+r})`, for valuations `v` of `K` and `v'` of `K'` with `v' ∘ ι = v`. -/
private theorem ordAt_basis_eq [Module.Free A Ω[A⁄k]] [Module.Finite A Ω[A⁄k]]
    [Module.Free A' Ω[A'⁄κ]] [Module.Finite A' Ω[A'⁄κ]] {e r : ℕ}
    (hrk : Module.finrank A Ω[A⁄k] = e + r) (hrk' : Module.finrank A' Ω[A'⁄κ] = r)
    (t : Fin e → A) (ht : ∀ i, algebraMap A A' (t i) ∈ Set.range (algebraMap κ A'))
    (hli : LinearIndependent (ResidueField A)
      (fun i => (1 : ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (t i)))
    (b : Module.Basis (Fin (e + r)) K Ω[K⁄k])
    (hb : ∀ i, b (Fin.castAdd r i) = KaehlerDifferential.D k K (algebraMap A K (t i)))
    (ℓ : Module.Basis Unit K (⋀[K]^(e + r) Ω[K⁄k]))
    (hℓ : ℓ () = exteriorPower.ιMulti K (e + r) b)
    (ℓ' : Module.Basis Unit K' (⋀[K']^r Ω[K'⁄κ]))
    (hℓ' : ℓ' () = exteriorPower.ιMulti K' r
      (fun j => KaehlerDifferential.map k κ K K' (b (Fin.natAdd e j))))
    {v : K → ℤ} {v' : K' → ℤ}
    (hmul : ∀ x y : K, x ≠ 0 → y ≠ 0 → v (x * y) = v x + v y)
    (hunit : ∀ a : A, IsUnit a → v (algebraMap A K a) = 0)
    (hmul' : ∀ x y : K', x ≠ 0 → y ≠ 0 → v' (x * y) = v' x + v' y)
    (hunit' : ∀ a : A', IsUnit a → v' (algebraMap A' K' a) = 0)
    (hv : ∀ x, v' (algebraMap K K' x) = v x) :
    ordAt A' v' (ZTensorPower.basis ℓ' 1 () : PluriForms κ K' r 1) =
      ordAt A v (ZTensorPower.basis ℓ 1 () : PluriForms k K (e + r) 1) := by
  classical
  obtain ⟨s, s', sK, sK', hsK, hsK', hcast, hπ0, hπ⟩ :=
    exists_adapted_bases (K := K) (K' := K') hrk hrk' t ht hli
  have hσ := span_ιMulti_basis_eq_top s
  have hσ' := span_ιMulti_basis_eq_top s'
  have hσK : topFormsMap k A K (e + r) (exteriorPower.ιMulti A (e + r) ⇑s) =
      exteriorPower.ιMulti K (e + r) ⇑sK := by
    rw [topFormsMap_ιMulti]; congr 1; funext i; exact (hsK i).symm
  have hσK' : topFormsMap κ A' K' r (exteriorPower.ιMulti A' r ⇑s') =
      exteriorPower.ιMulti K' r ⇑sK' := by
    rw [topFormsMap_ιMulti]; congr 1; funext i; exact (hsK' i).symm
  have hb1 : ℓ () = sK.det b • topFormsMap k A K (e + r) (exteriorPower.ιMulti A (e + r) ⇑s) := by
    rw [hℓ, hσK, alternatingMap_apply_eq_det_smul sK]
  have hb2 : ℓ' () = algebraMap K K' (sK.det b) •
      topFormsMap κ A' K' r (exteriorPower.ιMulti A' r ⇑s') := by
    rw [hℓ', hσK', alternatingMap_apply_eq_det_smul sK',
      det_kaehler_map_eq sK b sK' (fun i => by rw [hb, hcast]) hπ0 hπ]
  have h0 : topFormsMap k A K (e + r) (exteriorPower.ιMulti A (e + r) ⇑s) ≠ 0 := fun h =>
    ℓ.ne_zero () (by rw [hb1, h, smul_zero])
  have h0' : topFormsMap κ A' K' r (exteriorPower.ιMulti A' r ⇑s') ≠ 0 := fun h =>
    ℓ'.ne_zero () (by rw [hb2, h, smul_zero])
  rw [ordAt_eq hmul' hunit' hσ' h0', ordAt_eq hmul hunit hσ h0]
  have c1 : ℓ () = sK.det b • topFormsBasis A hσ h0 () := by rwa [topFormsBasis_apply]
  have c2 : ℓ' () = algebraMap K K' (sK.det b) • topFormsBasis A' hσ' h0' () := by
    rwa [topFormsBasis_apply]
  rw [formCoeff, formCoeff, ZTensorPower.basis_apply_of_eq_smul c1,
    ZTensorPower.basis_apply_of_eq_smul c2]
  simp only [zpow_one, map_smul, Module.Basis.repr_self, Finsupp.smul_apply,
    Finsupp.single_apply, if_true, smul_eq_mul, mul_one]
  exact hv _

/-- In the setting of `ordAt_basis_eq`, the wedge of `π(b_{e+1}), …, π(b_{e+r})` is nonzero. -/
private theorem ιMulti_kaehler_map_ne_zero [Module.Free A Ω[A⁄k]] [Module.Finite A Ω[A⁄k]]
    [Module.Free A' Ω[A'⁄κ]] [Module.Finite A' Ω[A'⁄κ]] {e r : ℕ}
    (hrk : Module.finrank A Ω[A⁄k] = e + r) (hrk' : Module.finrank A' Ω[A'⁄κ] = r)
    (t : Fin e → A) (ht : ∀ i, algebraMap A A' (t i) ∈ Set.range (algebraMap κ A'))
    (hli : LinearIndependent (ResidueField A)
      (fun i => (1 : ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (t i)))
    (b : Module.Basis (Fin (e + r)) K Ω[K⁄k])
    (hb : ∀ i, b (Fin.castAdd r i) = KaehlerDifferential.D k K (algebraMap A K (t i))) :
    exteriorPower.ιMulti K' r
      (fun j => KaehlerDifferential.map k κ K K' (b (Fin.natAdd e j))) ≠ 0 := by
  classical
  obtain ⟨s, s', sK, sK', hsK, hsK', hcast, hπ0, hπ⟩ :=
    exists_adapted_bases (K := K) (K' := K') hrk hrk' t ht hli
  rw [alternatingMap_apply_eq_det_smul sK',
    det_kaehler_map_eq sK b sK' (fun i => by rw [hb, hcast]) hπ0 hπ]
  exact smul_ne_zero ((map_ne_zero _).mpr (sK.isUnit_det b).ne_zero) (ιMulti_basis_ne_zero sK')

end LocalComparison

section SchemeComparison

variable {k κ : Type v} [Field k] [Field κ] [Algebra k κ]
  {Z Z' : Scheme.{v}} (sZ : Z ⟶ Spec (.of k)) (sZ' : Z' ⟶ Spec (.of κ)) (φ : Z' ⟶ Z)

/-- The extension of function fields of a morphism over `Spec κ ⟶ Spec k` is compatible with the
structure maps. -/
private theorem functionFieldMap_algebraMap_eq [IsIntegral Z] [IsIntegral Z'] [IsDominant φ]
    (hφ : φ ≫ sZ = sZ' ≫ Spec.map (CommRingCat.ofHom (algebraMap k κ))) (c : k) :
    functionFieldMap φ (letI := functionFieldAlgebra sZ; algebraMap k Z.functionField c) =
      (letI := functionFieldAlgebra sZ'; algebraMap κ Z'.functionField (algebraMap k κ c)) := by
  let := stalkAlgebra sZ (φ (genericPoint Z'))
  let := functionFieldAlgebra sZ
  let := stalkAlgebra sZ' (genericPoint Z')
  let := functionFieldAlgebra sZ'
  have h1 := isScalarTower_stalk_functionField sZ (φ (genericPoint Z'))
  have h2 := isScalarTower_stalk_functionField sZ' (genericPoint Z')
  rw [IsScalarTower.algebraMap_apply k (Z.presheaf.stalk (φ (genericPoint Z'))) Z.functionField,
    functionFieldMap_algebraMap_stalk, stalkMap_algebraMap_eq _ sZ sZ' φ hφ,
    ← IsScalarTower.algebraMap_apply]

/-- On a locally Noetherian integral scheme, the order at a point of codimension one of a unit of
the local ring vanishes. -/
private theorem ord_algebraMap_stalk_of_isUnit {X : Scheme.{v}} [IsIntegral X]
    [IsLocallyNoetherian X] {x : X} (hx : Order.coheight x = 1) {a : X.presheaf.stalk x}
    (ha : IsUnit a) : X.ord (algebraMap (X.presheaf.stalk x) X.functionField a) x = 0 := by
  have hne : algebraMap (X.presheaf.stalk x) X.functionField a ≠ 0 := (ha.map _).ne_zero
  rw [Scheme.ord_eq_iff hx hne, ofAdd_zero]
  have : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  exact Ring.ordFrac_of_isUnit ha

/-- **Orders of the adapted top forms along a flat unramified morphism.** Let `φ : Z' ⟶ Z` be a
flat, formally unramified dominant morphism of normal integral locally Noetherian schemes, `Z` over
`k` and `Z'` over `κ` compatibly, and let `t₁, …, t_e ∈ k(Z)` pull back to algebraically
independent constants `c₁, …, c_e ∈ κ`. For a point `z'` of codimension one with
`Ω_{𝒪_{Z,φ z'}/k}` free of rank `e + r` and `Ω_{𝒪_{Z',z'}/κ}` free of rank `r`, and a basis
`b = dt₁, …, dt_e, …` of `Ω_{k(Z)/k}`, the order of `∧ b` at `φ z'` equals the order of
`∧ π(b_{e+1}), …, π(b_{e+r})` at `z'`. -/
private theorem ordAt_wedge_eq_of_scheme [CharZero k] [IsIntegral Z] [IsIntegral Z']
    [IsLocallyNoetherian Z] [IsNormal Z] [IsLocallyNoetherian Z'] [IsNormal Z'] [IsDominant φ]
    [Flat φ] [FormallyUnramified φ]
    (hφ : φ ≫ sZ = sZ' ≫ Spec.map (CommRingCat.ofHom (algebraMap k κ))) {e r : ℕ}
    (t : Fin e → Z.functionField) (c : Fin e → κ) (hc : AlgebraicIndependent k c)
    (htc : ∀ i, functionFieldMap φ (t i) =
      (letI := functionFieldAlgebra sZ'; algebraMap κ Z'.functionField (c i)))
    (z' : Z') (x : Z) (hx : φ z' = x)
    (hfree : letI := stalkAlgebra sZ x
      Module.Free (Z.presheaf.stalk x) Ω[Z.presheaf.stalk x⁄k] ∧
        Module.Finite (Z.presheaf.stalk x) Ω[Z.presheaf.stalk x⁄k] ∧
        Module.finrank (Z.presheaf.stalk x) Ω[Z.presheaf.stalk x⁄k] = e + r)
    (hfree' : letI := stalkAlgebra sZ' z'
      Module.Free (Z'.presheaf.stalk z') Ω[Z'.presheaf.stalk z'⁄κ] ∧
        Module.Finite (Z'.presheaf.stalk z') Ω[Z'.presheaf.stalk z'⁄κ] ∧
        Module.finrank (Z'.presheaf.stalk z') Ω[Z'.presheaf.stalk z'⁄κ] = r) :
    letI := functionFieldAlgebra sZ
    letI := functionFieldAlgebra sZ'
    letI : Algebra Z.functionField Z'.functionField := functionFieldMapAlgebra φ
    letI : Algebra k Z'.functionField :=
      ((algebraMap κ Z'.functionField).comp (algebraMap k κ)).toAlgebra
    haveI : IsScalarTower k κ Z'.functionField := IsScalarTower.of_algebraMap_eq' rfl
    haveI : IsScalarTower k Z.functionField Z'.functionField :=
      IsScalarTower.of_algebraMap_eq fun c => (functionFieldMap_algebraMap_eq sZ sZ' φ hφ c).symm
    ∀ (b : Module.Basis (Fin (e + r)) Z.functionField Ω[Z.functionField⁄k])
      (_ : ∀ i, b (Fin.castAdd r i) = KaehlerDifferential.D k _ (t i)),
      exteriorPower.ιMulti Z'.functionField r (fun j =>
        KaehlerDifferential.map k κ Z.functionField Z'.functionField (b (Fin.natAdd e j))) ≠ 0 ∧
      (Order.coheight z' = 1 → ∀
      (ℓ : Module.Basis Unit Z.functionField (⋀[Z.functionField]^(e + r) Ω[Z.functionField⁄k]))
      (_ : ℓ () = exteriorPower.ιMulti _ (e + r) b)
      (ℓ' : Module.Basis Unit Z'.functionField (⋀[Z'.functionField]^r Ω[Z'.functionField⁄κ]))
      (_ : ℓ' () = exteriorPower.ιMulti _ r (fun j =>
        KaehlerDifferential.map k κ Z.functionField Z'.functionField (b (Fin.natAdd e j)))),
      letI := stalkAlgebra sZ x
      haveI := isScalarTower_stalk_functionField sZ x
      letI := stalkAlgebra sZ' z'
      haveI := isScalarTower_stalk_functionField sZ' z'
      ordAt (Z'.presheaf.stalk z') (fun f => Z'.ord f z')
          (ZTensorPower.basis ℓ' 1 () : PluriForms κ Z'.functionField r 1) =
        ordAt (Z.presheaf.stalk x) (fun f => Z.ord f x)
          (ZTensorPower.basis ℓ 1 () : PluriForms k Z.functionField (e + r) 1)) := by
  subst hx
  letI := functionFieldAlgebra sZ
  letI := functionFieldAlgebra sZ'
  letI : Algebra Z.functionField Z'.functionField := functionFieldMapAlgebra φ
  letI : Algebra k Z'.functionField :=
    ((algebraMap κ Z'.functionField).comp (algebraMap k κ)).toAlgebra
  haveI : IsScalarTower k κ Z'.functionField := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower k Z.functionField Z'.functionField :=
    IsScalarTower.of_algebraMap_eq fun c => (functionFieldMap_algebraMap_eq sZ sZ' φ hφ c).symm
  intro b hb
  letI : Algebra k (Z.presheaf.stalk (φ z')) := stalkAlgebra sZ (φ z')
  haveI : IsScalarTower k (Z.presheaf.stalk (φ z')) Z.functionField :=
    isScalarTower_stalk_functionField sZ (φ z')
  letI : Algebra κ (Z'.presheaf.stalk z') := stalkAlgebra sZ' z'
  haveI : IsScalarTower κ (Z'.presheaf.stalk z') Z'.functionField :=
    isScalarTower_stalk_functionField sZ' z'
  obtain ⟨_, _, hrk⟩ := hfree
  obtain ⟨_, _, hrk'⟩ := hfree'
  letI : Algebra (Z.presheaf.stalk (φ z')) (Z'.presheaf.stalk z') :=
    (φ.stalkMap z').hom.toAlgebra
  letI : Algebra k (Z'.presheaf.stalk z') :=
    ((algebraMap κ (Z'.presheaf.stalk z')).comp (algebraMap k κ)).toAlgebra
  haveI : IsScalarTower k κ (Z'.presheaf.stalk z') := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower k (Z.presheaf.stalk (φ z')) (Z'.presheaf.stalk z') :=
    IsScalarTower.of_algebraMap_eq fun c =>
      (stalkMap_algebraMap_eq (algebraMap k κ) sZ sZ' φ hφ z' c).symm
  haveI : IsLocalHom (algebraMap (Z.presheaf.stalk (φ z')) (Z'.presheaf.stalk z')) :=
    inferInstanceAs (IsLocalHom (φ.stalkMap z').hom)
  haveI : Algebra.FormallyUnramified (Z.presheaf.stalk (φ z')) (Z'.presheaf.stalk z') :=
    FormallyUnramified.stalkMap φ z'
  haveI : Module.Flat (Z.presheaf.stalk (φ z')) (Z'.presheaf.stalk z') := Flat.stalkMap φ z'
  letI : Algebra (Z.presheaf.stalk (φ z')) Z'.functionField :=
    ((algebraMap Z.functionField Z'.functionField).comp
      (algebraMap (Z.presheaf.stalk (φ z')) Z.functionField)).toAlgebra
  haveI : IsScalarTower (Z.presheaf.stalk (φ z')) Z.functionField Z'.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower (Z.presheaf.stalk (φ z')) (Z'.presheaf.stalk z') Z'.functionField :=
    IsScalarTower.of_algebraMap_eq fun a => functionFieldMap_algebraMap_stalk φ z' a
  haveI : CharZero (ResidueField (Z.presheaf.stalk (φ z'))) :=
    charZero_of_injective_algebraMap
      (algebraMap k (ResidueField (Z.presheaf.stalk (φ z')))).injective
  -- the functions `tᵢ` are regular at `φ z'`
  have hmem : ∀ i, t i ∈ Set.range (algebraMap (Z.presheaf.stalk (φ z')) Z.functionField) :=
    fun i => mem_range_of_map_mem_range (functionFieldMap φ)
      (fun a => functionFieldMap_algebraMap_stalk φ z' a)
      ⟨algebraMap κ (Z'.presheaf.stalk z') (c i), by
        rw [← IsScalarTower.algebraMap_apply]; exact (htc i).symm⟩
  choose a ha using hmem
  have hac : ∀ i, algebraMap (Z.presheaf.stalk (φ z')) (Z'.presheaf.stalk z') (a i) =
      algebraMap κ (Z'.presheaf.stalk z') (c i) := by
    intro i
    apply IsFractionRing.injective (Z'.presheaf.stalk z') Z'.functionField
    rw [← IsScalarTower.algebraMap_apply κ (Z'.presheaf.stalk z') Z'.functionField,
      ← IsScalarTower.algebraMap_apply (Z.presheaf.stalk (φ z')) (Z'.presheaf.stalk z')
        Z'.functionField,
      IsScalarTower.algebraMap_apply (Z.presheaf.stalk (φ z')) Z.functionField Z'.functionField,
      ha]
    exact htc i
  have hres : AlgebraicIndependent k (residue (Z.presheaf.stalk (φ z')) ∘ a) := by
    rw [algebraicIndependent_iff]
    intro q hq
    by_contra hq0
    have h1 : MvPolynomial.aeval (residue (Z.presheaf.stalk (φ z')) ∘ a) q =
        residue (Z.presheaf.stalk (φ z')) (MvPolynomial.aeval a q) :=
      (MvPolynomial.comp_aeval_apply a (IsScalarTower.toAlgHom k (Z.presheaf.stalk (φ z'))
        (ResidueField (Z.presheaf.stalk (φ z')))) q).symm
    have h2 : algebraMap (Z.presheaf.stalk (φ z')) (Z'.presheaf.stalk z') (MvPolynomial.aeval a q) =
        algebraMap κ (Z'.presheaf.stalk z') (MvPolynomial.aeval c q) := by
      rw [← IsScalarTower.coe_toAlgHom' k (Z.presheaf.stalk (φ z')) (Z'.presheaf.stalk z'),
        MvPolynomial.comp_aeval_apply, ← IsScalarTower.coe_toAlgHom' k κ (Z'.presheaf.stalk z'),
        MvPolynomial.comp_aeval_apply]
      have hf : (fun i => (IsScalarTower.toAlgHom k (Z.presheaf.stalk (φ z'))
          (Z'.presheaf.stalk z')) (a i)) =
          fun i => (IsScalarTower.toAlgHom k κ (Z'.presheaf.stalk z')) (c i) := funext hac
      rw [hf]
    have hu : IsUnit (MvPolynomial.aeval a q) := by
      refine isUnit_of_map_unit (algebraMap (Z.presheaf.stalk (φ z')) (Z'.presheaf.stalk z')) _ ?_
      rw [h2]
      exact (IsUnit.mk0 _ fun h => hq0 (hc.eq_zero_of_aeval_eq_zero q h)).map _
    rw [h1] at hq
    exact (residue_ne_zero_iff_isUnit _).mpr hu hq
  refine ⟨ιMulti_kaehler_map_ne_zero (A := Z.presheaf.stalk (φ z')) (A' := Z'.presheaf.stalk z')
    hrk hrk' a (fun i => ⟨c i, (hac i).symm⟩)
    (linearIndependent_tmul_D_of_algebraicIndependent hres) b (fun i => by rw [hb, ha]),
    fun hz' ℓ hℓ ℓ' hℓ' => ?_⟩
  have hx1 : Order.coheight (φ z') = 1 := (coheight_map_eq φ z').trans hz'
  have hmax := map_maximalIdeal_stalkMap_eq φ z'
  refine ordAt_basis_eq (k := k) (κ := κ) (A := Z.presheaf.stalk (φ z'))
    (A' := Z'.presheaf.stalk z') hrk hrk' a
    (fun i => ⟨c i, (hac i).symm⟩) (linearIndependent_tmul_D_of_algebraicIndependent hres) b
    (fun i => by rw [hb, ha]) ℓ hℓ ℓ' hℓ' (fun _ _ hx hy => Scheme.ord_mul hx hy)
    (fun _ hu => ord_algebraMap_stalk_of_isUnit hx1 hu) (fun _ _ hx hy => Scheme.ord_mul hx hy)
    (fun _ hu => ord_algebraMap_stalk_of_isUnit hz' hu) (fun f => ?_)
  exact ord_functionFieldMap_eq φ hz' hx1 hmax f

end SchemeComparison

section TransportHelpers

/-- On a nonempty space, a scheme morphism that is flat with irreducible source and target maps the
generic point to the generic point, hence is dominant. -/
private theorem isDominant_of_flat {X Y : Scheme.{v}} [IrreducibleSpace X] [IrreducibleSpace Y]
    (f : X ⟶ Y) [Flat f] : IsDominant f := by
  have hgen : f (genericPoint X) = genericPoint Y := by
    obtain ⟨y', hy', hy'e⟩ := Flat.generalizingMap f
      ((genericPoint_spec Y).specializes (Set.mem_univ (f (genericPoint X))))
    have : y' = genericPoint X := (hy'.antisymm ((genericPoint_spec _).specializes trivial)).eq
    rw [← this, hy'e]
  constructor
  rw [DenseRange, dense_iff_closure_eq]
  refine Set.eq_univ_of_univ_subset ?_
  have h := (genericPoint_spec Y).def
  rw [← h]
  exact closure_mono (Set.singleton_subset_iff.mpr ⟨_, hgen⟩)

/-- On an integral scheme, a nonzero rational function is the image of a unit of `K(X)` on every
component. -/
private theorem exists_units_evalFF_eq {X : Scheme.{v}} [IsIntegral X] {g : X.functionField}
    (hg : g ≠ 0) : ∃ ψ : (RationalFunctions X)ˣ, ∀ Z,
      MMP.Threefold.Mori.Helpers.evalFF Z (ψ : RationalFunctions X) = g := by
  have hmem : ∀ Z : irreducibleComponents X, genericPoint X ∈ Z.1 := fun Z =>
    Z.2.2 (IrreducibleSpace.isIrreducible_univ X) (Set.subset_univ _) trivial
  let jZ : ∀ Z : irreducibleComponents X,
      X.functionField →+* X.presheaf.stalk (componentGenericPoint X Z) := fun Z =>
    (X.presheaf.stalkSpecializes
      ((isGenericPoint_componentGenericPoint X Z).specializes (hmem Z))).hom
  refine ⟨Units.map (RingHom.pi jZ).toMonoidHom (Units.mk0 g hg), fun Z => ?_⟩
  change (X.presheaf.stalkSpecializes _ ≫ X.presheaf.stalkSpecializes _).hom g = g
  rw [TopCat.Presheaf.stalkSpecializes_comp, TopCat.Presheaf.stalkSpecializes_refl]
  rfl

/-- An integral locally Noetherian scheme with a point other than its generic point has a point of
codimension one: a point `x` of finite codimension `≥ 1` has a generization of codimension one. -/
private theorem exists_coheight_eq_one {Z : Scheme.{v}} [IsIntegral Z] [IsLocallyNoetherian Z]
    {x : Z} (hx : x ≠ genericPoint Z) : ∃ z : Z, Order.coheight z = 1 := by
  have hg : genericPoint Z ⤳ x := (genericPoint_spec Z).specializes trivial
  have hlt : x < genericPoint Z :=
    lt_of_le_not_ge (Scheme.le_iff_specializes.mpr hg) fun h =>
      hx ((Scheme.le_iff_specializes.mp h).antisymm hg).eq
  have h1 : 1 ≤ Order.coheight x := le_add_self.trans (Order.coheight_add_one_le hlt)
  have hfin : Order.coheight x < ⊤ := by
    have h2 : ringKrullDim (Z.presheaf.stalk x) < ⊤ := ringKrullDim_lt_top
    rw [ringKrullDim_stalk_eq_coheight] at h2
    exact WithBot.coe_lt_coe.mp h2
  rcases h1.eq_or_lt with h | h
  · exact ⟨x, h.symm⟩
  · obtain ⟨z, -, hz⟩ := (Order.coe_lt_coheight_iff (n := 1) hfin).mp (by exact_mod_cast h)
    exact ⟨z, by exact_mod_cast hz⟩

end TransportHelpers

section PullbackForms

/-- The pull-back of a multiple of the generator `ℓ` along a pull-back generator `ℓ ()`, for
`ℓ' ()` the image of `ℓ ()`. -/
private theorem pullbackForms_smul_basis {k K K' : Type*} [CommRing k] [Field K] [Field K']
    [Algebra k K] [Algebra k K'] [Algebra K K'] [IsScalarTower k K K'] {d : ℕ}
    (ℓ : Module.Basis Unit K (⋀[K]^d Ω[K⁄k])) (ℓ' : Module.Basis Unit K' (⋀[K']^d Ω[K'⁄k]))
    (hω : IsPullbackGenerator K' (ℓ ())) (hℓ' : ℓ' () = topFormsMap k K K' d (ℓ ())) (c : K) :
    pullbackForms (K' := K') 1 (c • ZTensorPower.basis ℓ 1 () : PluriForms k K d 1) =
      algebraMap K K' c • ZTensorPower.basis ℓ' 1 () := by
  rw [pullbackForms_eq hω, pullbackFormsAlong]
  have h1 : basisOfSpanSingleton hω.1 hω.ne_zero = ℓ :=
    Module.Basis.eq_of_apply_eq fun i => by simp
  have h2 : basisOfSpanSingleton hω.2.1 hω.2.2 = ℓ' :=
    Module.Basis.eq_of_apply_eq fun i => by simp [hℓ']
  rw [h1, h2]
  simp

end PullbackForms

end TransportAlgebra

section Dimension

open Order

/-- A specialization `x ⤳ y` inside an affine open gives an inclusion of primes. -/
private theorem primeIdealOf_le_of_specializes {X : Scheme.{v}} {V : X.Opens} (hV : IsAffineOpen V)
    {x y : X} (hxy : x ⤳ y) (hy : y ∈ V) :
    hV.primeIdealOf ⟨x, hxy.mem_open V.isOpen hy⟩ ≤ hV.primeIdealOf ⟨y, hy⟩ := by
  refine (PrimeSpectrum.le_iff_specializes _ _).mpr ?_
  have : (⟨x, hxy.mem_open V.isOpen hy⟩ : V) ⤳ ⟨y, hy⟩ := (subtype_specializes_iff _ _).mpr hxy
  exact this.map (hV.isoSpec.hom.base.hom.continuous)

/-- The coheight of an element of an upper set is its coheight in the ambient order. -/
private theorem coheight_coe_of_isUpper {α : Type*} [Preorder α] {Z : Set α}
    (hZ : IsUpperSet Z) (b : Z) : coheight b = coheight (b : α) := by
  refine le_antisymm (coheight_le_coheight_apply_of_strictMono Subtype.val (fun _ _ h => h) b) ?_
  refine coheight_le fun p hp => ?_
  let q : LTSeries Z :=
    ⟨p.length, fun i => ⟨p i, hZ (hp ▸ p.monotone (Fin.zero_le i)) b.2⟩, p.step⟩
  exact length_le_coheight (p := q) (show b ≤ q.head from by
    change (b : α) ≤ p.head; rw [hp])

/-- If every element of `α`, and every element of the upper set `Z = [a, ∞)`, satisfies
`height + coheight = const` (finite on `α`), then `height b = height a + height_Z b`. -/
private theorem height_eq_height_add_height_of_isUpper {α : Type*} [PartialOrder α] {a : α}
    {Z : Set α}
    (hZ : ∀ x, x ∈ Z ↔ a ≤ x) {D D' : ℕ∞} (hD : D ≠ ⊤)
    (h₁ : ∀ x : α, height x + coheight x = D) (h₂ : ∀ z : Z, height z + coheight z = D')
    (b : α) (hb : b ∈ Z) : height b = height a + height (⟨b, hb⟩ : Z) := by
  have hup : IsUpperSet Z := fun x y hxy hx => (hZ y).mpr (((hZ x).mp hx).trans hxy)
  have ha : a ∈ Z := (hZ a).mpr le_rfl
  have h0 : height (⟨a, ha⟩ : Z) = 0 := by
    rw [height_eq_zero]
    intro z hz
    exact (hZ z).mp z.2
  have e1 := h₂ ⟨a, ha⟩
  have e2 := h₂ ⟨b, hb⟩
  rw [h0, zero_add, coheight_coe_of_isUpper hup] at e1
  rw [coheight_coe_of_isUpper hup] at e2
  change coheight a = D' at e1
  change _ + coheight b = D' at e2
  have e3 := h₁ a
  have e4 := h₁ b
  have hcb : coheight b ≠ ⊤ := fun h => hD (by rw [← e4, h, add_top])
  have : height b + coheight b = (height a + height (⟨b, hb⟩ : Z)) + coheight b := by
    rw [e4, add_assoc, e2, ← e1, e3]
  rw [add_comm (height b), add_comm (height a + _)] at this
  exact (WithTop.add_left_inj hcb).mp this

/-- In a domain of finite type over a field, `height x + coheight x` is the (finite) dimension. -/
private theorem exists_height_add_coheight_eq (k B : Type*) [Field k] [CommRing B] [IsDomain B]
    [Algebra k B] [Algebra.FiniteType k B] :
    ∃ D : ℕ, ∀ x : PrimeSpectrum B, height x + coheight x = D := by
  obtain ⟨h₁, -⟩ :=
    Algebra.FiniteType.ringKrullDim_eq_height_of_isMaximal_and_length_eq_ringKrullDim k B
  haveI := Algebra.FiniteType.isNoetherianRing k B
  obtain ⟨m, hm⟩ := Ideal.exists_maximal B
  have hne := Ideal.height_ne_top hm.ne_top
  obtain ⟨D, hD'⟩ := WithTop.ne_top_iff_exists.mp hne
  have hD : ringKrullDim B = (D : ℕ∞) := by rw [h₁ m, ← hD']; rfl
  refine ⟨D, fun x => ?_⟩
  have h1 := MMP.ringKrullDim_le_height_add_coheight k B x
  have h2 := Order.height_add_coheight_le_krullDim x
  rw [← WithBot.coe_add] at h2
  have : ((height x + coheight x : ℕ∞) : WithBot ℕ∞) = (D : ℕ∞) := by
    rw [← hD]; exact le_antisymm h2 h1
  exact_mod_cast this

/-- **Additivity of heights.** For primes `s ≤ p` of a domain of finite type over a field,
`ht p = ht s + ht (p / s)`. -/
private theorem height_eq_height_add_height_quotient (k B : Type*) [Field k] [CommRing B]
    [IsDomain B]
    [Algebra k B] [Algebra.FiniteType k B] (s p : Ideal B) [s.IsPrime] [p.IsPrime] (hsp : s ≤ p)
    [(p.map (Ideal.Quotient.mk s)).IsPrime] :
    p.height = s.height + (p.map (Ideal.Quotient.mk s)).height := by
  have : IsDomain (B ⧸ s) := Ideal.Quotient.isDomain s
  obtain ⟨D, hD⟩ := exists_height_add_coheight_eq k B
  obtain ⟨D', hD'⟩ := exists_height_add_coheight_eq k (B ⧸ s)
  let e := s.primeSpectrumQuotientOrderIsoZeroLocus
  let Z : Set (PrimeSpectrum B) := PrimeSpectrum.zeroLocus (s : Set B)
  have hZ : ∀ x, x ∈ Z ↔ (⟨s, inferInstance⟩ : PrimeSpectrum B) ≤ x := fun x =>
    (PrimeSpectrum.mem_zeroLocus _ _)
  have hp : (⟨p, inferInstance⟩ : PrimeSpectrum B) ∈ Z := (hZ _).mpr hsp
  have key := height_eq_height_add_height_of_isUpper hZ (ENat.coe_ne_top D) hD
    (D' := D') (fun z => by
      rw [← height_orderIso e.symm, ← coheight_orderIso e.symm]; exact hD' _) _ hp
  have he : e ⟨p.map (Ideal.Quotient.mk s), inferInstance⟩ = ⟨⟨p, inferInstance⟩, hp⟩ := by
    apply Subtype.ext
    apply PrimeSpectrum.ext
    change (p.map (Ideal.Quotient.mk s)).comap (Ideal.Quotient.mk s) = p
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker, sup_eq_left.mpr hsp]
  have h3 : height (⟨⟨p, inferInstance⟩, hp⟩ : Z) = (p.map (Ideal.Quotient.mk s)).height := by
    rw [← he, height_orderIso]
    exact (PrimeSpectrum.height_eq_orderHeight ⟨_, inferInstance⟩).symm
  rw [h3, ← PrimeSpectrum.height_eq_orderHeight ⟨s, inferInstance⟩] at key
  exact (PrimeSpectrum.height_eq_orderHeight ⟨p, inferInstance⟩).trans key

/-- For `A = B_p` and `s ≤ p`, `A ⧸ s A` is the localization of `B ⧸ s` at `p ⧸ s`. -/
private theorem isLocalization_atPrime_quotient_map (B A : Type*) [CommRing B] [CommRing A]
    [Algebra B A] (s p : Ideal B) [p.IsPrime] (hsp : s ≤ p) [IsLocalization.AtPrime A p]
    [(p.map (Ideal.Quotient.mk s)).IsPrime] :
    IsLocalization.AtPrime (A ⧸ s.map (algebraMap B A)) (p.map (Ideal.Quotient.mk s)) := by
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid (B ⧸ s) p.primeCompl)
      (A ⧸ s.map (algebraMap B A)) := inferInstance
  have hM : Algebra.algebraMapSubmonoid (B ⧸ s) p.primeCompl =
      (p.map (Ideal.Quotient.mk s)).primeCompl := by
    ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [Algebra.algebraMapSubmonoid, Submonoid.mem_map, Ideal.mem_primeCompl_iff]
    constructor
    · rintro ⟨y, hy, hyx⟩ hx
      rw [Ideal.Quotient.algebraMap_eq] at hyx
      rw [← hyx, Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at hx
      obtain ⟨z, hz, hzy⟩ := hx
      rw [Ideal.Quotient.eq] at hzy
      exact hy (by simpa using p.sub_mem hz (hsp hzy))
    · intro hx
      exact ⟨x, fun h => hx (Ideal.mem_map_of_mem _ h), rfl⟩
  rwa [hM] at hloc

/-- For `A = B_p` and a prime `s ≤ p`, `dim A ⧸ s A = ht (p / s)`. -/
private theorem ringKrullDim_quotient_map_eq_height (B A : Type*) [CommRing B] [CommRing A]
    [Algebra B A]
    (s p : Ideal B) [s.IsPrime] [p.IsPrime] (hsp : s ≤ p) [IsLocalization.AtPrime A p] :
    haveI : (p.map (Ideal.Quotient.mk s)).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
    ringKrullDim (A ⧸ s.map (algebraMap B A)) = (p.map (Ideal.Quotient.mk s)).height := by
  haveI : (p.map (Ideal.Quotient.mk s)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  haveI := isLocalization_atPrime_quotient_map B A s p hsp
  exact IsLocalization.AtPrime.ringKrullDim_eq_height (p.map (Ideal.Quotient.mk s)) _

/-- For `x ⤳ P` in an affine open `V`, the kernel of `𝒪_{X,P} → κ(x)` is generated by the prime of
`x` in `Γ(X, V)`. -/
private theorem ker_stalkSpecializes_residue_eq_map {X : Scheme.{v}} {V : X.Opens}
    (hV : IsAffineOpen V)
    {x P : X} (hxP : x ⤳ P) (hPV : P ∈ V) :
    letI := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨P, hPV⟩
    RingHom.ker (X.presheaf.stalkSpecializes hxP ≫ X.residue x).hom =
      (hV.primeIdealOf ⟨x, hxP.mem_open V.isOpen hPV⟩).asIdeal.map
        (algebraMap Γ(X, V) (X.presheaf.stalk P)) := by
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨P, hPV⟩
  have hxV : x ∈ V := hxP.mem_open V.isOpen hPV
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxV⟩
  have hP := hV.isLocalization_stalk ⟨P, hPV⟩
  have hx := hV.isLocalization_stalk ⟨x, hxV⟩
  set q := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  set φ := (X.presheaf.stalkSpecializes hxP ≫ X.residue x).hom
  have hψ : ∀ b : Γ(X, V), φ (algebraMap _ _ b) =
      residue (X.presheaf.stalk x) (algebraMap Γ(X, V) (X.presheaf.stalk x) b) := by
    intro b
    change (X.presheaf.germ V P hPV ≫ X.presheaf.stalkSpecializes hxP ≫ X.residue x).hom b = _
    rw [← Category.assoc, TopCat.Presheaf.germ_stalkSpecializes]
    rfl
  have hker : ∀ b : Γ(X, V), φ (algebraMap _ _ b) = 0 ↔ b ∈ q := by
    intro b
    rw [hψ]
    exact (residue_eq_zero_iff _).trans
      (IsLocalization.AtPrime.to_map_mem_maximal_iff (X.presheaf.stalk x) q b)
  apply le_antisymm
  · intro a ha
    obtain ⟨b, s, rfl⟩ := IsLocalization.exists_mk'_eq
      (hV.primeIdealOf ⟨P, hPV⟩).asIdeal.primeCompl a
    have h1 : φ (algebraMap _ _ b) = 0 := by
      rw [← IsLocalization.mk'_spec (X.presheaf.stalk P) b s, map_mul, RingHom.mem_ker.mp ha,
        zero_mul]
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ((hker b).mp h1))
  · rw [Ideal.map_le_iff_le_comap]
    intro b hb
    exact (hker b).mpr hb

/-- A point of codimension one on a prime divisor of a variety has a two-dimensional local ring. -/
private theorem ringKrullDim_stalk_eq_two (k : Type v) [Field k] (X : Scheme.{v}) (sX : X ⟶ Spec
    (.of k))
    (hX : IsNormalVariety k sX) (S : Mori.PrimeDivisor X) (P : X) (hPS : S.genericPoint ⤳ P)
    (hP : ringKrullDim (X.presheaf.stalk P ⧸
      RingHom.ker (X.presheaf.stalkSpecializes hPS ≫ X.residue S.genericPoint).hom) = 1) :
    ringKrullDim (X.presheaf.stalk P) = 2 := by
  obtain ⟨hvar, -⟩ := hX
  have := (Mori.isVariety_iff _ _).mp hvar
  obtain ⟨_, _, _, _⟩ := this
  obtain ⟨V, hV, hPV, -⟩ := exists_isAffineOpen_mem_and_subset (show P ∈ (⊤ : X.Opens) from trivial)
  have : Nonempty V := ⟨⟨P, hPV⟩⟩
  letI : Algebra k Γ(X, V) := sectionAlgebra sX V
  have : Algebra.FiniteType k Γ(X, V) := finiteType_sectionAlgebra sX hV
  letI : Algebra Γ(X, V) (X.presheaf.stalk P) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨P, hPV⟩
  have hηV : S.genericPoint ∈ V := hPS.mem_open V.isOpen hPV
  letI : Algebra Γ(X, V) (X.presheaf.stalk S.genericPoint) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨S.genericPoint, hηV⟩
  have hlocP := hV.isLocalization_stalk ⟨P, hPV⟩
  have hlocη := hV.isLocalization_stalk ⟨S.genericPoint, hηV⟩
  set s := (hV.primeIdealOf ⟨S.genericPoint, hηV⟩).asIdeal
  set p := (hV.primeIdealOf ⟨P, hPV⟩).asIdeal
  have hsp : s ≤ p := primeIdealOf_le_of_specializes hV hPS hPV
  have hs : s.height = 1 := by
    have h1 := AlgebraicGeometry.PrimeDivisor.ringKrullDim_stalk_genericPoint_eq_one S
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height s] at h1
    exact_mod_cast h1
  have hker := ker_stalkSpecializes_residue_eq_map hV hPS hPV
  rw [hker, ringKrullDim_quotient_map_eq_height _ _ s p hsp] at hP
  haveI : (p.map (Ideal.Quotient.mk s)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have hq : (p.map (Ideal.Quotient.mk s)).height = 1 := by exact_mod_cast hP
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p,
    height_eq_height_add_height_quotient k Γ(X, V) s p hsp, hs, hq]
  rfl

end Dimension

section Model

open TensorProduct

/-- The `κ`-algebra structure on `R ⊗[F] κ` through the right factor. -/
private noncomputable abbrev rightAlgebra (F R K : Type*) [Field F] [CommRing R] [Field K]
    [Algebra F R] [Algebra F K] : Algebra K (R ⊗[F] K) :=
  (Algebra.TensorProduct.includeRight : K →ₐ[F] R ⊗[F] K).toRingHom.toAlgebra

/-- `R ⊗[F] κ` is of finite type over `κ` when `R` is of finite type over `F`. -/
private theorem finiteType_rightAlgebra (F R K : Type*) [Field F] [CommRing R] [Field K]
    [Algebra F R] [Algebra F K] [Algebra.FiniteType F R] :
    letI := rightAlgebra F R K
    Algebra.FiniteType K (R ⊗[F] K) := by
  letI := rightAlgebra F R K
  let φ : K ⊗[F] R →ₐ[K] R ⊗[F] K :=
    { toRingHom := (Algebra.TensorProduct.comm F K R).toRingHom
      commutes' := fun c => by
        change Algebra.TensorProduct.comm F K R (c ⊗ₜ 1) = 1 ⊗ₜ c
        simp }
  exact Algebra.FiniteType.of_surjective φ (Algebra.TensorProduct.comm F K R).surjective

/-- A ring isomorphism of local rings induces an isomorphism of their adic completions. -/
private noncomputable def completionEquivOfRingEquiv {S T : Type*} [CommRing S] [IsLocalRing S]
    [CommRing T] [IsLocalRing T] (σ : S ≃+* T) :
    AdicCompletion (maximalIdeal S) S ≃+* AdicCompletion (maximalIdeal T) T :=
  completionEquiv (σ : S →+* T) _ _ (IsLocalRing.map_ringEquiv_maximalIdeal σ) fun n => by
    refine ⟨Ideal.quotientMap_injective' (le_of_eq ?_), Ideal.quotientMap_surjective σ.surjective⟩
    rw [Ideal.comap_coe, ← Ideal.map_symm, Ideal.map_pow, IsLocalRing.map_ringEquiv_maximalIdeal]

/-- `completionEquivOfRingEquiv σ` extends `σ`. -/
private theorem completionEquivOfRingEquiv_of {S T : Type*} [CommRing S] [IsLocalRing S]
    [CommRing T] [IsLocalRing T] (σ : S ≃+* T) (x : S) :
    completionEquivOfRingEquiv σ (AdicCompletion.of _ _ x) = AdicCompletion.of _ _ (σ x) :=
  completionMap_of (σ : S →+* T) _ _ (IsLocalRing.map_ringEquiv_maximalIdeal σ) x

variable {k : Type v} [Field k] [CharZero k] {B : Type v} [CommRing B] [IsDomain B]
  [IsIntegrallyClosed B] [Algebra k B] [Algebra.FiniteType k B] (p : Ideal B) [p.IsPrime]
  (A : Type v) [CommRing A] [IsLocalRing A] [Algebra B A] [IsLocalization.AtPrime A p]
  [Algebra k A] [IsScalarTower k B A]
  (K : Type v) [Field K] [Algebra (ResidueField A) K] [IsSepClosure (ResidueField A) K]
  (H : Type v) [CommRing H] [IsLocalRing H] [Algebra A H] [IsHenselization A K H]

/-- A strict henselization `H` of a normal local domain `A` essentially of finite type over a field
has the dimension of `A`: `A → H` is flat and local with `𝔪_A H = 𝔪_H`, so the closed fibre is a
field. -/
private theorem ringKrullDim_henselization_eq (k A K H : Type*) [Field k] [CommRing A]
    [IsLocalRing A] [IsDomain A] [IsIntegrallyClosed A] [Algebra k A] [Algebra.EssFiniteType k A]
    [Field K] [Algebra (ResidueField A) K] [IsSepClosure (ResidueField A) K] [CommRing H]
    [IsLocalRing H] [Algebra A H] [IsHenselization A K H] :
    ringKrullDim H = ringKrullDim A := by
  obtain ⟨⟨_, -, -⟩, ⟨_, _, hmax⟩, -⟩ :=
    MMP.Foundations.isNoetherianRing_strictHenselization_adicCompletion k A K H
  have : IsNoetherianRing A := Algebra.EssFiniteType.isNoetherianRing k A
  exact ringKrullDim_eq_of_map_maximalIdeal_eq hmax

include k p in
/-- The coefficient field `F = k(t)` of a lifted transcendence basis, the localization
`B_F = T⁻¹B` of finite type over `F`, and `A` as a localization of `B_F`. -/
private theorem exists_coefficientField_model :
    ∃ (F : Type v) (_ : Field F) (BF : Type v) (_ : CommRing BF) (_ : IsDomain BF)
      (_ : IsIntegrallyClosed BF) (_ : Algebra F BF) (_ : Algebra.FiniteType F BF)
      (_ : Algebra B BF) (_ : Algebra BF A) (_ : IsScalarTower B BF A) (_ : Algebra F A)
      (_ : IsScalarTower F BF A) (M : Submonoid BF),
      IsLocalization M A ∧ FiniteDimensional F (ResidueField A) ∧
        Algebra.IsSeparable F (ResidueField A) ∧
        (∃ T : Submonoid B, T ≤ p.primeCompl ∧ IsLocalization T BF) ∧
        (∀ c : k, ∃ y : F, algebraMap B BF (algebraMap k B c) = algebraMap F BF y ∧
          algebraMap F A y = algebraMap B A (algebraMap k B c)) ∧
        ∃ (ι : Type v) (_ : Finite ι) (t : ι → B),
          IsTranscendenceBasis k (residue A ∘ algebraMap B A ∘ t) ∧
          ∀ i, ∃ y : F, algebraMap B BF (t i) = algebraMap F BF y ∧
            algebraMap F A y = algebraMap B A (t i) := by
  obtain ⟨ι, _, t, ht⟩ := exists_finite_isTranscendenceBasis_residue k B A p
  have hT := polySubmonoid_le (k := k) (A := A) p ht.1
  let BF := Localization (polySubmonoid (k := k) t)
  let F := FractionRing (MvPolynomial ι k)
  letI : Algebra F BF := (fieldToLocalization (k := k) t).toAlgebra
  have : IsDomain BF := IsLocalization.isDomain_localization
    (hT.trans p.primeCompl_le_nonZeroDivisors)
  have : IsIntegrallyClosed BF := isIntegrallyClosed_of_isLocalization BF _
    (hT.trans p.primeCompl_le_nonZeroDivisors)
  have := finiteType_localization (k := k) t
  letI : Algebra BF A := (IsLocalization.lift (M := polySubmonoid (k := k) t) (S := BF)
    (g := algebraMap B A)
    (fun y => IsLocalization.map_units A (⟨y, hT y.2⟩ : p.primeCompl))).toAlgebra
  have : IsScalarTower B BF A := IsScalarTower.of_algebraMap_eq fun b =>
    (IsLocalization.lift_eq _ b).symm
  letI : Algebra F A := (fractionRingLift (t := algebraMap B A ∘ t) ht.1).toAlgebra
  have : IsScalarTower F BF A := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    apply IsLocalization.ringHom_ext (nonZeroDivisors (MvPolynomial ι k))
    ext q
    · simp only [RingHom.algebraMap_toAlgebra, RingHom.comp_apply]
      rw [fractionRingLift_algebraMap, fieldToLocalization_algebraMap, IsLocalization.lift_eq]
      exact (MvPolynomial.comp_aeval_apply t (IsScalarTower.toAlgHom k B A) _).symm
    · simp only [RingHom.algebraMap_toAlgebra, RingHom.comp_apply]
      rw [fractionRingLift_algebraMap, fieldToLocalization_algebraMap, IsLocalization.lift_eq]
      exact (MvPolynomial.comp_aeval_apply t (IsScalarTower.toAlgHom k B A) _).symm
  have hM := IsLocalization.isLocalization_of_submonoid_le BF A (polySubmonoid (k := k) t)
    p.primeCompl hT
  have : Algebra.EssFiniteType k A := by
    have : Algebra.EssFiniteType B A := Algebra.EssFiniteType.of_isLocalization A p.primeCompl
    exact Algebra.EssFiniteType.comp k B A
  have : Algebra.EssFiniteType k (ResidueField A) :=
    Algebra.EssFiniteType.of_surjective (IsScalarTower.toAlgHom k A (ResidueField A))
      residue_surjective
  have hfin := finite_residue_fractionRingLift (k := k) (A := A) (t := algebraMap B A ∘ t) ht
  have halg : Algebra.IsAlgebraic F (ResidueField A) :=
    isAlgebraic_residue_fractionRingLift (k := k) (A := A) (t := algebraMap B A ∘ t) ht
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap k F).injective
  refine ⟨F, inferInstance, BF, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, _,
    hM, hfin, Algebra.IsAlgebraic.isSeparable_of_perfectField, ⟨_, hT, inferInstance⟩,
    fun c => ⟨algebraMap k F c, ?_, ?_⟩, ι, inferInstance, t, ht, fun i =>
      ⟨algebraMap (MvPolynomial ι k) F (MvPolynomial.X i), ?_, ?_⟩⟩
  · rw [IsScalarTower.algebraMap_apply k (MvPolynomial ι k) F, RingHom.algebraMap_toAlgebra,
      fieldToLocalization_algebraMap, MvPolynomial.algebraMap_eq, MvPolynomial.aeval_C]
  · rw [IsScalarTower.algebraMap_apply k (MvPolynomial ι k) F, RingHom.algebraMap_toAlgebra,
      fractionRingLift_algebraMap, MvPolynomial.algebraMap_eq, MvPolynomial.aeval_C,
      ← IsScalarTower.algebraMap_apply]
  · rw [RingHom.algebraMap_toAlgebra, fieldToLocalization_algebraMap, MvPolynomial.aeval_X]
  · rw [RingHom.algebraMap_toAlgebra, fractionRingLift_algebraMap, MvPolynomial.aeval_X]
    rfl

include k in
/-- **The ring of the surface model.** A domain `C` of finite type over `κ = κ(A)^{sep}`, normal at
every prime, with a `B`-algebra structure and a prime `q₀` over `p` whose local ring has
completion isomorphic over `B` to the completed strict henselization `Ĥ` of `A = B_p`. -/
private theorem exists_surfaceModel_ring (s : Ideal B) [s.IsPrime] (hsp : s ≤ p)
    [IsIntegrallyClosed (B ⧸ s)] (hsA : ringKrullDim (A ⧸ s.map (algebraMap B A)) = 1)
    (hA : ringKrullDim A = 2) :
    ∃ (C : Type v) (_ : CommRing C) (_ : IsDomain C) (_ : Algebra K C)
      (_ : Algebra.FiniteType K C) (_ : Algebra B C) (q₀ : Ideal C) (_ : q₀.IsMaximal),
      q₀.comap (algebraMap B C) = p ∧
      (∀ (q : Ideal C) (_ : q.IsPrime), IsIntegrallyClosed (Localization.AtPrime q)) ∧
      ringKrullDim C = ringKrullDim A ∧ (algebraMap B C).Flat ∧
      (algebraMap B C).FormallyUnramified ∧
      (s.map (algebraMap B C)).IsPrime ∧ s.map (algebraMap B C) ≤ q₀ ∧
      (∀ (Q : Ideal (C ⧸ s.map (algebraMap B C))) (_ : Q.IsPrime),
        IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q)) ∧
      (s.map (algebraMap B C)).height = 1 ∧
      (∃ e : AdicCompletion (maximalIdeal (Localization.AtPrime q₀)) (Localization.AtPrime q₀) ≃+*
          AdicCompletion (maximalIdeal H) H,
        ∀ b : B, e (AdicCompletion.of _ _ (algebraMap B (Localization.AtPrime q₀) b)) =
          AdicCompletion.of _ _ (algebraMap A H (algebraMap B A b))) ∧
      (∀ c : k, algebraMap B C (algebraMap k B c) =
        algebraMap K C (algebraMap (ResidueField A) K (residue A (algebraMap k A c)))) ∧
      ∃ (n : ℕ) (t : Fin n → B), AlgebraicIndependent k (residue A ∘ algebraMap B A ∘ t) ∧
        Algebra.trdeg k (ResidueField A) = n ∧
        ∀ i, algebraMap B C (t i) =
          algebraMap K C (algebraMap (ResidueField A) K (residue A (algebraMap B A (t i)))) := by
  obtain ⟨F, _, BF, _, _, _, _, _, _, _, _, _, _, M, hM, _, _, ⟨T, hTp, hTloc⟩, hkF, ι, _, t, ht,
    htF⟩ := exists_coefficientField_model (k := k) p A
  letI : Algebra F K := ((algebraMap (ResidueField A) K).comp
    (algebraMap F (ResidueField A))).toAlgebra
  have : IsScalarTower F (ResidueField A) K := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra F H := ((algebraMap A H).comp (algebraMap F A)).toAlgebra
  have : IsScalarTower F A H := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.IsSeparable (ResidueField A) K := IsSepClosure.separable
  have : Algebra.IsSeparable F K := Algebra.IsSeparable.trans F (ResidueField A) K
  obtain ⟨q, _, hqA, hqmax, hqK, e, he⟩ :=
    exists_completionEquiv_localization_tensor (F := F) (A := A)
    (K := K) (H := H)
  let R := BF ⊗[F] K
  letI : Algebra K R := rightAlgebra F BF K
  have : Algebra.FiniteType K R := finiteType_rightAlgebra F BF K
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing K R
  let Φ : R →ₐ[F] A ⊗[F] K :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom F BF A) (AlgHom.id F K)
  letI : Algebra R (A ⊗[F] K) := Φ.toRingHom.toAlgebra
  have hΦ : ∀ x : BF, algebraMap R (A ⊗[F] K) (algebraMap BF R x) =
      algebraMap A (A ⊗[F] K) (algebraMap BF A x) := fun x => by
    change Φ (x ⊗ₜ 1) = algebraMap BF A x ⊗ₜ 1
    exact Algebra.TensorProduct.map_tmul _ _ x 1
  have : IsScalarTower BF R (A ⊗[F] K) := IsScalarTower.of_algebraMap_eq fun x => by
    rw [hΦ]; rfl
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid R M) (A ⊗[F] K) :=
    IsLocalization.tensorProduct_tensorProduct F K M A (by
      ext c
      exact Algebra.TensorProduct.map_tmul _ _ (1 : BF) c |>.trans (by simp))
  let q₀ : Ideal R := q.comap (algebraMap R (A ⊗[F] K))
  have hnorm : ∀ (Q : Ideal R) [Q.IsPrime],
      IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q) :=
    fun Q _ => isDomain_and_isIntegrallyClosed_localization_tensor (F := F) (A := BF) (K := K) Q
  have : IsReduced R := isReduced_ofLocalizationMaximal R fun m _ => by
    haveI := (hnorm m).1; infer_instance
  have : IsDomain (Localization.AtPrime q₀) := (hnorm q₀).1
  let sF : Ideal BF := s.map (algebraMap B BF)
  have hTs : Algebra.algebraMapSubmonoid (B ⧸ s) T ≤ nonZeroDivisors (B ⧸ s) := by
    rintro _ ⟨t, ht, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero fun h0 => hTp ht (hsp ?_)
    exact Ideal.Quotient.eq_zero_iff_mem.mp h0
  have : IsDomain (BF ⧸ sF) := IsLocalization.isDomain_of_le_nonZeroDivisors
    (M := Algebra.algebraMapSubmonoid (B ⧸ s) T) (BF ⧸ sF) hTs
  have : IsIntegrallyClosed (BF ⧸ sF) :=
    isIntegrallyClosed_of_isLocalization (BF ⧸ sF) _ hTs
  let I : Ideal R := sF.map (algebraMap BF R)
  have hnormI : ∀ (Q : Ideal (R ⧸ I)) [Q.IsPrime],
      IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q) :=
    isDomain_and_isIntegrallyClosed_of_ringEquiv
      ((Algebra.TensorProduct.quotientTensorEquiv (R := F) F K BF sF).toRingEquiv.symm :
        R ⧸ I ≃+* (BF ⧸ sF) ⊗[F] K)
      (fun Q _ => isDomain_and_isIntegrallyClosed_localization_tensor (F := F) (A := BF ⧸ sF)
        (K := K) Q)
  have : IsReduced (R ⧸ I) := isReduced_ofLocalizationMaximal _ fun m _ => by
    haveI := (hnormI m).1; infer_instance
  have hIq : I ≤ q₀ := by
    rw [Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
    intro b hb
    change algebraMap R (A ⊗[F] K) (algebraMap BF R (algebraMap B BF b)) ∈ q
    rw [hΦ, ← IsScalarTower.algebraMap_apply B BF A, ← Ideal.mem_comap, hqA]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff A p b).mpr (hsp hb)
  let qb₀ : Ideal (R ⧸ I) := q₀.map (Ideal.Quotient.mk I)
  have hqb₀c : qb₀.comap (Ideal.Quotient.mk I) = q₀ := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker, sup_eq_left.mpr hIq]
  have : qb₀.IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have : IsDomain (Localization.AtPrime qb₀) := (hnormI qb₀).1
  obtain ⟨g₂', hg₂', hg₂dom⟩ := exists_isDomain_away qb₀
  obtain ⟨g₂, rfl⟩ := Ideal.Quotient.mk_surjective g₂'
  have hg₂ : g₂ ∉ q₀ := fun h => hg₂' (Ideal.mem_map_of_mem _ h)
  obtain ⟨g₁, hg₁, hgdom⟩ := exists_isDomain_away q₀
  obtain ⟨g, hgdef⟩ : ∃ g, g = g₁ * g₂ := ⟨_, rfl⟩
  have hg : g ∉ q₀ := fun h => (Ideal.IsPrime.mem_or_mem inferInstance (hgdef ▸ h)).elim hg₁ hg₂
  have := hgdom g ⟨g₂, hgdef⟩ hg
  let C := Localization.Away g
  letI : Algebra B C := ((algebraMap R C).comp ((algebraMap BF R).comp (algebraMap B BF))).toAlgebra
  have : Algebra.FiniteType K C := Algebra.FiniteType.trans (S := R) inferInstance
    (IsLocalization.finiteType_of_monoid_fg (Submonoid.powers g) C)
  have hdis : Disjoint (Submonoid.powers g : Set R) q₀ := by
    rw [Set.disjoint_left]
    rintro _ ⟨n, rfl⟩ h
    exact hg (Ideal.IsPrime.mem_of_pow_mem inferInstance n h)
  let q₀' : Ideal C := q₀.map (algebraMap R C)
  have : q₀'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers g) C q₀
    inferInstance hdis
  have hq₀max : q₀.IsMaximal := by
    have : Nontrivial (R ⧸ q₀) :=
      Ideal.Quotient.nontrivial_iff.mpr (Ideal.IsPrime.ne_top inferInstance)
    rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient]
    refine ⟨exists_pair_ne _, mul_comm, fun {a} ha => ?_⟩
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨x, hx⟩ := hqK (Φ r)
    have hr : Ideal.Quotient.mk q₀ r = Ideal.Quotient.mk q₀ (1 ⊗ₜ x) := by
      rw [Ideal.Quotient.eq]
      change Φ (r - 1 ⊗ₜ x) ∈ q
      rw [map_sub]
      convert hx using 2
      exact (Algebra.TensorProduct.map_tmul _ _ (1 : BF) x).trans (by simp)
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact ha (by rw [hr, TensorProduct.tmul_zero, map_zero])
    refine ⟨Ideal.Quotient.mk q₀ (1 ⊗ₜ x⁻¹), ?_⟩
    rw [hr, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_inv_cancel₀ hx0]
    rfl
  have : q₀'.IsMaximal := IsLocalization.isMaximal_of_isMaximal_disjoint (M := Submonoid.powers g)
    (S := C) q₀ hdis
  have hq₀' : q₀'.comap (algebraMap R C) = q₀ :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers g) C inferInstance hdis
  have hlocC : ∀ (Q : Ideal C) [Q.IsPrime],
      IsLocalization (Q.comap (algebraMap R C)).primeCompl (Localization.AtPrime Q) := fun Q _ =>
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization (Submonoid.powers g)
      (Localization.AtPrime Q) Q
  have h1 : IsLocalization q₀.primeCompl (Localization.AtPrime q₀') := by
    have hs : (q₀'.comap (algebraMap R C)).primeCompl = q₀.primeCompl := by
      ext x; rw [Ideal.mem_primeCompl_iff, Ideal.mem_primeCompl_iff, hq₀']
    exact hs ▸ hlocC q₀'
  have h2 : IsLocalization q₀.primeCompl (Localization.AtPrime q) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Algebra.algebraMapSubmonoid R M) (Localization.AtPrime q) q
  let σ : Localization.AtPrime q₀' ≃ₐ[R] Localization.AtPrime q :=
    IsLocalization.algEquiv q₀.primeCompl _ _
  have hdim : ringKrullDim C = ringKrullDim A := by
    have : IsNoetherianRing (Localization.AtPrime q₀') :=
      IsLocalization.isNoetherianRing q₀'.primeCompl _ (Algebra.FiniteType.isNoetherianRing K C)
    have : IsDomain A := IsLocalization.isDomain_of_le_nonZeroDivisors (M := p.primeCompl)
      A p.primeCompl_le_nonZeroDivisors
    have : IsIntegrallyClosed A := isIntegrallyClosed_of_isLocalization A p.primeCompl
      p.primeCompl_le_nonZeroDivisors
    have : Algebra.EssFiniteType k A := by
      have : Algebra.EssFiniteType B A := Algebra.EssFiniteType.of_isLocalization A p.primeCompl
      exact Algebra.EssFiniteType.comp k B A
    have : IsNoetherianRing H :=
      (MMP.Foundations.isNoetherianRing_strictHenselization_adicCompletion k A K H).1.1
    rw [← MMP.IdealHeight.ringKrullDim_localization_atPrime_eq_of_isMaximal_of_finiteType K q₀',
      ← IsLocalRing.ringKrullDim_adicCompletion_maximalIdeal,
      ringKrullDim_eq_of_ringEquiv ((completionEquivOfRingEquiv σ.toRingEquiv).trans e),
      IsLocalRing.ringKrullDim_adicCompletion_maximalIdeal (A := H),
      ringKrullDim_henselization_eq k A K H]
  have key : ∀ b : B, σ (algebraMap B (Localization.AtPrime q₀') b) =
      algebraMap A (Localization.AtPrime q) (algebraMap B A b) := fun b => by
    rw [IsScalarTower.algebraMap_apply B C (Localization.AtPrime q₀'),
      RingHom.algebraMap_toAlgebra, RingHom.comp_apply,
      ← IsScalarTower.algebraMap_apply R C (Localization.AtPrime q₀'), AlgEquiv.commutes,
      IsScalarTower.algebraMap_apply R (A ⊗[F] K) (Localization.AtPrime q), RingHom.comp_apply,
      hΦ, ← IsScalarTower.algebraMap_apply A (A ⊗[F] K) (Localization.AtPrime q),
      ← IsScalarTower.algebraMap_apply B BF A]
  -- the model of the boundary: `𝔠 = s C`
  have hc : s.map (algebraMap B C) = I.map (algebraMap R C) := by
    rw [RingHom.algebraMap_toAlgebra, ← Ideal.map_map, ← Ideal.map_map]
  have hM' : Algebra.algebraMapSubmonoid (R ⧸ I) (Submonoid.powers g) =
      Submonoid.powers (Ideal.Quotient.mk I g) := Submonoid.map_powers _ _
  have hlocQ : IsLocalization (Submonoid.powers (Ideal.Quotient.mk I g))
      (C ⧸ I.map (algebraMap R C)) := hM' ▸ inferInstance
  have hgI : Ideal.Quotient.mk I g ∉ qb₀ := fun h => hg (by rwa [← hqb₀c])
  have hdomQ : IsDomain (C ⧸ I.map (algebraMap R C)) := by
    have := hg₂dom (Ideal.Quotient.mk I g)
      ⟨Ideal.Quotient.mk I g₁, by rw [hgdef, map_mul, mul_comm]⟩
      hgI
    let ψ := IsLocalization.algEquiv (Submonoid.powers (Ideal.Quotient.mk I g))
      (C ⧸ I.map (algebraMap R C)) (Localization.Away (Ideal.Quotient.mk I g))
    exact Function.Injective.isDomain (ψ.toRingEquiv : C ⧸ I.map (algebraMap R C) →+*
      Localization.Away (Ideal.Quotient.mk I g)) ψ.injective
  have hcp : (I.map (algebraMap R C)).IsPrime := (Ideal.Quotient.isDomain_iff_prime _).mp hdomQ
  have hcnorm : ∀ (Q : Ideal (C ⧸ I.map (algebraMap R C))) [Q.IsPrime],
      IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q) :=
    fun Q _ => isDomain_and_isIntegrallyClosed_of_isLocalization
      (Submonoid.powers (Ideal.Quotient.mk I g)) hnormI Q
  have hcq : I.map (algebraMap R C) ≤ q₀' := Ideal.map_mono hIq
  have hheight : (s.map (algebraMap B C)).height = 1 := by
    rw [hc]
    have hq₀'h : q₀'.height = 2 := by
      have h1 := IsLocalization.AtPrime.ringKrullDim_eq_height q₀' (Localization.AtPrime q₀')
      rw [MMP.IdealHeight.ringKrullDim_localization_atPrime_eq_of_isMaximal_of_finiteType K q₀',
        hdim, hA] at h1
      exact WithBot.coe_eq_coe.mp (h1.symm.trans rfl)
    haveI : (q₀'.map (Ideal.Quotient.mk (I.map (algebraMap R C)))).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
    have hadd := height_eq_height_add_height_quotient K C (I.map (algebraMap R C)) q₀' hcq
    have hquot := ringKrullDim_quotient_map_eq_height C (Localization.AtPrime q₀')
      (I.map (algebraMap R C)) q₀' hcq
    have hloc1 : ringKrullDim (Localization.AtPrime q₀' ⧸
        (I.map (algebraMap R C)).map (algebraMap C (Localization.AtPrime q₀'))) = 1 := by
      have hJ : (I.map (algebraMap R C)).map (algebraMap C (Localization.AtPrime q₀')) =
          s.map (algebraMap B (Localization.AtPrime q₀')) := by
        rw [← hc, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
      have hJ' : (s.map (algebraMap B A)).map (algebraMap A (Localization.AtPrime q)) =
          (s.map (algebraMap B (Localization.AtPrime q₀'))).map
            (σ.toRingEquiv : Localization.AtPrime q₀' →+* Localization.AtPrime q) := by
        rw [Ideal.map_map, Ideal.map_map]
        congr 1
        ext b
        exact (key b).symm
      rw [hJ, ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ _ σ.toRingEquiv hJ')]
      haveI : IsNoetherianRing A := IsLocalization.isNoetherianRing p.primeCompl A
        (Algebra.FiniteType.isNoetherianRing k B)
      haveI : IsNoetherianRing (Localization.AtPrime q₀') :=
        IsLocalization.isNoetherianRing q₀'.primeCompl _ (Algebra.FiniteType.isNoetherianRing K C)
      haveI : IsNoetherianRing (Localization.AtPrime q) :=
        isNoetherianRing_of_ringEquiv _ σ.toRingEquiv
      haveI : IsLocalHom (algebraMap A (Localization.AtPrime q)) :=
        ((local_hom_TFAE _).out 1 3).mpr hqmax.le
      haveI : Module.Flat (A ⊗[F] K) (Localization.AtPrime q) := IsLocalization.flat _ q.primeCompl
      haveI : Module.Flat A (Localization.AtPrime q) := Module.Flat.trans A (A ⊗[F] K) _
      have hne : s.map (algebraMap B A) ≠ ⊤ := fun h => by
        rw [h] at hsA
        haveI : Subsingleton (A ⧸ (⊤ : Ideal A)) := Ideal.Quotient.subsingleton_iff.mpr rfl
        rw [ringKrullDim_eq_bot_of_subsingleton] at hsA
        exact WithBot.bot_ne_one hsA
      rw [ringKrullDim_quotient_map_eq_of_flat hqmax _ hne, hsA]
    rw [hloc1] at hquot
    have h2 : (q₀'.map (Ideal.Quotient.mk (I.map (algebraMap R C)))).height = 1 := by
      exact_mod_cast hquot.symm
    rw [hq₀'h, h2] at hadd
    have h3 : (I.map (algebraMap R C)).height + 1 = 1 + 1 := by rw [← hadd]; rfl
    exact (WithTop.add_right_inj (by simp : (1 : ℕ∞) ≠ ⊤)).mp h3
  have hflat : (algebraMap B C).Flat := by
    have : IsLocalization T BF := hTloc
    have h1 : (algebraMap B BF).Flat :=
      RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat BF T)
    have h2 : (algebraMap BF R).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
    have h3 : (algebraMap R C).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
    rw [RingHom.algebraMap_toAlgebra]
    exact (h1.comp h2).comp h3
  have hfu : (algebraMap B C).FormallyUnramified := by
    have : IsLocalization T BF := hTloc
    have : Algebra.FormallyUnramified F K := Algebra.FormallyUnramified.of_isSeparable F K
    have h1 : (algebraMap B BF).FormallyUnramified :=
      RingHom.formallyUnramified_algebraMap.mpr (Algebra.FormallyUnramified.of_isLocalization T)
    have h2 : (algebraMap BF R).FormallyUnramified :=
      RingHom.formallyUnramified_algebraMap.mpr inferInstance
    have h3 : (algebraMap R C).FormallyUnramified :=
      RingHom.formallyUnramified_algebraMap.mpr inferInstance
    rw [RingHom.algebraMap_toAlgebra]
    exact (h1.comp h2).comp h3
  -- the elements of `B` coming from `F` land in `K`
  have hkey : ∀ (b : B) (y : F), algebraMap B BF b = algebraMap F BF y →
      algebraMap F A y = algebraMap B A b → algebraMap B C b =
        algebraMap K C (algebraMap (ResidueField A) K (residue A (algebraMap B A b))) := by
    intro b y h1 h2
    have h3 : algebraMap BF R (algebraMap F BF y) = algebraMap K R (algebraMap F K y) := by
      change (algebraMap F BF y) ⊗ₜ[F] (1 : K) = (1 : BF) ⊗ₜ[F] (algebraMap F K y)
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
        TensorProduct.smul_tmul]
    have h4 : algebraMap F K y = algebraMap (ResidueField A) K (residue A (algebraMap B A b)) := by
      rw [← h2]
      rfl
    change algebraMap R C (algebraMap BF R (algebraMap B BF b)) = _
    rw [h1, h3, h4, ← IsScalarTower.algebraMap_apply K R C]
  refine ⟨C, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, q₀',
    inferInstance, ?_, ?_, hdim, hflat, hfu, hc ▸ hcp, hc ▸ hcq,
    by rw [hc]; exact fun Q _ => hcnorm Q,
    hheight, ⟨(completionEquivOfRingEquiv σ.toRingEquiv).trans e, ?_⟩, ?_, ?_⟩
  · have e1 : (algebraMap R (A ⊗[F] K)).comp (algebraMap BF R) =
        (algebraMap A (A ⊗[F] K)).comp (algebraMap BF A) := RingHom.ext hΦ
    rw [RingHom.algebraMap_toAlgebra, ← Ideal.comap_comap, ← Ideal.comap_comap, hq₀',
      Ideal.comap_comap (algebraMap BF R), e1, ← Ideal.comap_comap, hqA, Ideal.comap_comap,
      ← IsScalarTower.algebraMap_eq]
    exact IsLocalization.AtPrime.under_maximalIdeal A p
  · intro Q _
    have := (hnorm (Q.comap (algebraMap R C))).2
    exact IsIntegrallyClosed.of_equiv
      (IsLocalization.algEquiv (Q.comap (algebraMap R C)).primeCompl
        (Localization.AtPrime (Q.comap (algebraMap R C))) (Localization.AtPrime Q)).toRingEquiv
  · intro b
    rw [RingEquiv.trans_apply, completionEquivOfRingEquiv_of]
    exact (congrArg (fun z => e (AdicCompletion.of _ _ z)) (key b)).trans (he _)
  · intro c
    obtain ⟨y, h1, h2⟩ := hkF c
    rw [hkey _ y h1 h2, ← IsScalarTower.algebraMap_apply k B A]
  · let σι := (Finite.equivFin ι).symm
    refine ⟨Nat.card ι, t ∘ σι, ht.1.comp _ σι.injective, ?_, fun i => ?_⟩
    · rw [← ht.cardinalMk_eq_trdeg, Nat.cast_card]
    · obtain ⟨y, h1, h2⟩ := htF (σι i)
      exact hkey _ y h1 h2

end Model

section CurveModel

/-- A Noetherian integrally closed local domain of dimension at most one (a field or a DVR) is
regular. -/
private theorem isRegularLocalRing_of_isIntegrallyClosed {T : Type*} [CommRing T] [IsLocalRing T]
    [IsDomain T] [IsNoetherianRing T] [IsIntegrallyClosed T] (h : ringKrullDim T ≤ 1) :
    IsRegularLocalRing T := by
  by_cases hf : IsField T
  · letI := hf.toField
    infer_instance
  · have hle : Ring.KrullDimLE 1 T := Ring.krullDimLE_iff.mpr h
    have h4 : IsIntegrallyClosed T ∧ ∃! P : Ideal T, P ≠ ⊥ ∧ P.IsPrime := by
      refine ⟨inferInstance, maximalIdeal T,
        ⟨fun h0 => hf ((isField_iff_maximalIdeal_eq).mpr h0), inferInstance⟩, ?_⟩
      intro P hP'
      obtain ⟨hP0, hP⟩ := hP'
      rcases (Ring.krullDimLE_one_iff.mp hle) P hP with hmin | hmax
      · have hb : (⊥ : Ideal T) ≤ P := bot_le
        exact absurd (le_antisymm (hmin.2 ⟨Ideal.isPrime_bot, le_rfl⟩ hb) hb) hP0
      · exact eq_maximalIdeal hmax
    have hdvr : IsDiscreteValuationRing T := ((IsDiscreteValuationRing.TFAE T hf).out 1 4).mpr h4
    infer_instance

/-- Let `C` be a domain of finite type over a field, of dimension at most two, and `𝔠` a prime of
height one with `C ⧸ 𝔠` normal. Then `C_Q ⧸ 𝔠 C_Q` is regular for every prime `Q ⊇ 𝔠`. -/
private theorem isRegularLocalRing_localization_quotient (K C : Type*) [Field K] [CommRing C]
    [IsDomain C]
    [Algebra K C] [Algebra.FiniteType K C] (hC : ringKrullDim C ≤ 2) (c : Ideal C) [c.IsPrime]
    (hc : c.height = 1)
    (hnorm : ∀ (Q : Ideal (C ⧸ c)) [Q.IsPrime], IsDomain (Localization.AtPrime Q) ∧
      IsIntegrallyClosed (Localization.AtPrime Q))
    (Q : Ideal C) [Q.IsPrime] (hcQ : c ≤ Q) :
    IsRegularLocalRing
      (Localization.AtPrime Q ⧸ c.map (algebraMap C (Localization.AtPrime Q))) := by
  haveI : (Q.map (Ideal.Quotient.mk c)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  haveI := isLocalization_atPrime_quotient_map C (Localization.AtPrime Q) c Q hcQ
  set T := Localization.AtPrime Q ⧸ c.map (algebraMap C (Localization.AtPrime Q))
  let e := IsLocalization.algEquiv (Q.map (Ideal.Quotient.mk c)).primeCompl T
    (Localization.AtPrime (Q.map (Ideal.Quotient.mk c)))
  obtain ⟨h1, h2⟩ := hnorm (Q.map (Ideal.Quotient.mk c))
  haveI : IsDomain T := Function.Injective.isDomain (e.toRingEquiv : T →+*
    Localization.AtPrime (Q.map (Ideal.Quotient.mk c))) e.toRingEquiv.injective
  haveI : IsIntegrallyClosed T := IsIntegrallyClosed.of_equiv e.toRingEquiv.symm
  haveI : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing K C
  haveI : IsLocalRing T := IsLocalization.AtPrime.isLocalRing T (Q.map (Ideal.Quotient.mk c))
  refine isRegularLocalRing_of_isIntegrallyClosed ?_
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height (Q.map (Ideal.Quotient.mk c)) T]
  have hadd := height_eq_height_add_height_quotient K C c Q hcQ
  have hQ : (Q.height : WithBot ℕ∞) ≤ 2 :=
    (Ideal.height_le_ringKrullDim_of_ne_top Ideal.IsPrime.ne_top').trans hC
  rw [hadd, hc] at hQ
  have h3 : (1 + (Q.map (Ideal.Quotient.mk c)).height : ℕ∞) ≤ 2 := WithBot.coe_le_coe.mp hQ
  have h4 : (Q.map (Ideal.Quotient.mk c)).height ≤ 1 := by
    generalize (Q.map (Ideal.Quotient.mk c)).height = h at h3 ⊢
    induction h using ENat.recTopCoe with
    | top => simp at h3
    | coe n => norm_cast at h3 ⊢; omega
  exact_mod_cast h4

/-- A point `x` of an affine open `V` lies on the zero locus of `J ⊆ Γ(X, V)` iff `J` is contained
in
the prime of `x`. -/
private theorem mem_zeroLocus_iff_le_primeIdealOf {X : Scheme.{v}} {V : X.Opens}
    (hV : IsAffineOpen V)
    (J : Ideal Γ(X, V)) {x : X} (hx : x ∈ V) :
    x ∈ X.zeroLocus (U := V) (J : Set Γ(X, V)) ↔ J ≤ (hV.primeIdealOf ⟨x, hx⟩).asIdeal := by
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
  have hloc := hV.isLocalization_stalk ⟨x, hx⟩
  simp only [Scheme.mem_zeroLocus_iff, SetLike.mem_coe]
  refine forall₂_congr fun f _ => ?_
  rw [Scheme.mem_basicOpen _ _ _ hx]
  have := IsLocalization.AtPrime.isUnit_to_map_iff (S := X.presheaf.stalk x)
    (hV.primeIdealOf ⟨x, hx⟩).asIdeal f
  rw [Ideal.mem_primeCompl_iff] at this
  exact (not_congr this).trans not_not

/-- The image of `Spec Γ(X, V) → X` lies in `V`. -/
private theorem fromSpec_mem {X : Scheme.{v}} {V : X.Opens} (hV : IsAffineOpen V)
    (q : PrimeSpectrum Γ(X, V)) : hV.fromSpec q ∈ V := by
  rw [← SetLike.mem_coe, ← hV.range_fromSpec]; exact ⟨q, rfl⟩

/-- On an affine open `V` containing `η`, a prime ideal of an ideal sheaf supported on the closure
of `η` is the prime of `η`. -/
private theorem ideal_eq_primeIdealOf {X : Scheme.{v}} (I : X.IdealSheafData) {η : X}
    (hsupp : (I.support : Set X) = closure {η}) {V : X.Opens} (hV : IsAffineOpen V) (hη : η ∈ V)
    [hp : (I.ideal ⟨V, hV⟩).IsPrime] :
    I.ideal ⟨V, hV⟩ = (hV.primeIdealOf ⟨η, hη⟩).asIdeal := by
  apply le_antisymm
  · have : η ∈ I.support := by rw [← SetLike.mem_coe, hsupp]; exact subset_closure rfl
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨V, hV⟩) hη] at this
    exact (mem_zeroLocus_iff_le_primeIdealOf hV _ hη).mp this
  · let q : PrimeSpectrum Γ(X, V) := ⟨_, hp⟩
    have hxV := fromSpec_mem hV q
    have hx : hV.fromSpec q ∈ I.support := by
      rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨V, hV⟩) hxV,
        mem_zeroLocus_iff_le_primeIdealOf hV _ hxV, AlgebraicGeometry.primeIdealOf_fromSpec]
    rw [← SetLike.mem_coe, hsupp, ← specializes_iff_mem_closure] at hx
    have := primeIdealOf_le_of_specializes hV hx hxV
    rwa [AlgebraicGeometry.primeIdealOf_fromSpec] at this

/-- The ideal of an integral closed subscheme on an affine open meeting it is prime. -/
private theorem isPrime_ideal_of_isIntegral {X : Scheme.{v}} (I : X.IdealSheafData)
    [IsIntegral I.subscheme] {V : X.Opens} (hV : IsAffineOpen V)
    [Nonempty (I.subschemeι ⁻¹ᵁ V)] : (I.ideal ⟨V, hV⟩).IsPrime := by
  let e := (I.subschemeObjIso ⟨V, hV⟩).commRingCatIsoToRingEquiv
  have : IsDomain (Γ(X, V) ⧸ I.ideal ⟨V, hV⟩) :=
    Function.Injective.isDomain (e.symm : Γ(X, V) ⧸ I.ideal ⟨V, hV⟩ →+*
      Γ(I.subscheme, I.subschemeι ⁻¹ᵁ V)) e.symm.injective
  exact (Ideal.Quotient.isDomain_iff_prime _).mp this

/-- For a normal prime divisor `S` and an affine open `V ∋ η_S`, `Γ(X, V) ⧸ 𝔭_{η_S}` is integrally
closed: it is `Γ(S, S ∩ V)`. -/
private theorem isIntegrallyClosed_quotient_primeIdealOf {X : Scheme.{v}} (S : Mori.PrimeDivisor X)
    (hS : IsNormal S.idealSheaf.subscheme) {V : X.Opens} (hV : IsAffineOpen V)
    (hη : S.genericPoint ∈ V) :
    IsIntegrallyClosed (Γ(X, V) ⧸ (hV.primeIdealOf ⟨S.genericPoint, hη⟩).asIdeal) := by
  have := S.integral
  let W := S.idealSheaf.subschemeι ⁻¹ᵁ V
  have hW : IsAffineOpen W := hV.preimage S.idealSheaf.subschemeι
  have : Nonempty W := ⟨⟨_root_.genericPoint S.idealSheaf.subscheme, hη⟩⟩
  have hnW : IsNormalRing Γ(S.idealSheaf.subscheme, W) := by
    have h := (isNormal_tfae S.idealSheaf.subscheme).out 1 2
    exact h.mp hS ⟨W, hW⟩
  have : IsIntegrallyClosed Γ(S.idealSheaf.subscheme, W) :=
    IsIntegrallyClosed.of_localization_maximal fun q _ _ => (hnW q).2
  let e := (S.idealSheaf.subschemeObjIso ⟨V, hV⟩).commRingCatIsoToRingEquiv
  haveI := isPrime_ideal_of_isIntegral S.idealSheaf hV
  have := IsIntegrallyClosed.of_equiv e
  rwa [ideal_eq_primeIdealOf S.idealSheaf
    (AlgebraicGeometry.PrimeDivisor.support_eq_closure S) hV hη] at this

/-- The prime of a point `q` of `Spec R` in `Γ(Spec R, ⊤) ≅ R` is `q`. -/
private theorem primeIdealOf_top_Spec (R : CommRingCat.{v}) (q : Spec R) :
    ((isAffineOpen_top (Spec R)).primeIdealOf ⟨q, trivial⟩).asIdeal =
      q.asIdeal.comap (Scheme.ΓSpecIso R).hom.hom := by
  haveI : q.asIdeal.IsPrime := q.isPrime
  rw [IsAffineOpen.primeIdealOf_eq_map_closedPoint]
  ext x
  show (Spec R).presheaf.germ ⊤ q trivial x ∈ maximalIdeal ((Spec R).presheaf.stalk q) ↔ _
  have h := congrArg (fun f => f.hom x) (Spec.germ_stalkMapIso_hom (R := R) q)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
  rw [Ideal.mem_comap, ← IsLocalization.AtPrime.to_map_mem_maximal_iff
    (Localization.AtPrime q.asIdeal) q.asIdeal]
  change _ ↔ CommRingCat.Hom.hom
    (CommRingCat.ofHom (algebraMap R (Localization.AtPrime q.asIdeal))) _ ∈ _
  rw [← h]
  exact (map_mem_nonunits_iff (Spec.stalkIso R q).commRingCatIsoToRingEquiv _).symm

/-- A prime divisor of `Spec R`, `R` of finite type over a perfect field `K`, is smooth over `K`
when `R_Q ⧸ 𝔠 R_Q` is regular at every prime `Q` containing its prime `𝔠`. -/
private theorem smooth_subschemeι_ofCoheightOne (K : Type v) [Field K] [PerfectField K]
    (R : CommRingCat.{v}) [Algebra K R] [Algebra.FiniteType K R] (ξ : Spec R)
    (hξ : Order.coheight ξ = 1)
    (hreg : ∀ (Q : Ideal R) [Q.IsPrime], ξ.asIdeal ≤ Q →
      IsRegularLocalRing (Localization.AtPrime Q ⧸
        ξ.asIdeal.map (algebraMap R (Localization.AtPrime Q)))) :
    Smooth ((AlgebraicGeometry.PrimeDivisor.ofCoheightOne ξ hξ).idealSheaf.subschemeι ≫
      Spec.map (CommRingCat.ofHom (algebraMap K R))) := by
  set I := (AlgebraicGeometry.PrimeDivisor.ofCoheightOne ξ hξ).idealSheaf with hIdef
  have hI : I = Stacks.Chow.integralComponentAt ξ := rfl
  haveI : IsIntegral I.subscheme := (AlgebraicGeometry.PrimeDivisor.ofCoheightOne ξ hξ).integral
  haveI : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap K R))) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  rw [MMP.Flips.ResolutionInputs.smooth_iff_forall_isRegularLocalRing_stalk]
  intro z
  set x := I.subschemeι z
  have hsupp : (I.support : Set (Spec R)) = closure {ξ} := by
    rw [hI]; exact Stacks.Chow.coe_support_integralComponentAt ξ
  have hxsupp : x ∈ (I.support : Set (Spec R)) := by
    rw [← I.range_subschemeι]; exact ⟨z, rfl⟩
  have hξx : ξ ⤳ x := by
    rwa [specializes_iff_mem_closure, ← hsupp]
  have hle : ξ.asIdeal ≤ x.asIdeal := (PrimeSpectrum.le_iff_specializes _ _).mpr hξx
  haveI : Nonempty (I.subschemeι ⁻¹ᵁ (⊤ : (Spec R).Opens)) := ⟨⟨z, trivial⟩⟩
  haveI := isPrime_ideal_of_isIntegral I (isAffineOpen_top (Spec R))
  have hideal : I.ideal ⟨⊤, isAffineOpen_top _⟩ =
      ξ.asIdeal.comap (Scheme.ΓSpecIso R).hom.hom := by
    rw [ideal_eq_primeIdealOf I hsupp (isAffineOpen_top _) trivial, primeIdealOf_top_Spec]
  haveI : x.asIdeal.IsPrime := x.isPrime
  let φ := (Spec.stalkIso R x).commRingCatIsoToRingEquiv
  have hmap : ξ.asIdeal.map (algebraMap R (Localization.AtPrime x.asIdeal)) =
      (IdealSheafData.stalk I x).map φ.toRingHom := by
    rw [IdealSheafData.stalk_eq_map_germ I x ⟨⊤, isAffineOpen_top _⟩ trivial, hideal,
      Ideal.map_map]
    have : φ.toRingHom.comp ((Spec R).presheaf.germ ⊤ x trivial).hom =
        (algebraMap R _).comp (Scheme.ΓSpecIso R).hom.hom := by
      ext a
      exact congrArg (fun f => CommRingCat.Hom.hom f a) (Spec.germ_stalkMapIso_hom (R := R) x)
    have hsurj : Function.Surjective (Scheme.ΓSpecIso R).hom.hom := fun b =>
      ⟨(Scheme.ΓSpecIso R).inv.hom b, by
        rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]⟩
    rw [this, ← Ideal.map_map, Ideal.map_comap_of_surjective _ hsurj]
  have e1 := MMP.Flips.ResolutionInputs.stalkQuotientEquiv I z
  have e2 := Ideal.quotientEquiv _ _ φ hmap
  haveI := hreg x.asIdeal hle
  exact IsRegularLocalRing.of_ringEquiv (e2.symm.trans e1)

end CurveModel

section RegularModel

/-- **The singular primes of a normal surface.** Let `C` be a normal domain of finite type and
dimension two over a perfect field. A prime of height at most one has a regular local ring, and
the primes with non-regular local ring form a closed set (the complement of the smooth locus),
hence finitely many maximal ideals. So some `h ∉ q₀` lies in each of them other than `q₀`. -/
private theorem exists_notMem_forall_isRegularLocalRing (K C : Type v) [Field K] [PerfectField K]
    [CommRing C]
    [IsDomain C] [Algebra K C] [Algebra.FiniteType K C]
    (hnorm : ∀ (q : Ideal C) (_ : q.IsPrime), IsIntegrallyClosed (Localization.AtPrime q))
    (hdim : ringKrullDim C = 2) (q₀ : Ideal C) [q₀.IsPrime] :
    ∃ h ∉ q₀, ∀ (Q : Ideal C) [Q.IsPrime], h ∉ Q → Q ≠ q₀ →
      IsRegularLocalRing (Localization.AtPrime Q) := by
  classical
  have : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing K C
  let Sing : Set (PrimeSpectrum C) :=
    {x | ¬ IsRegularLocalRing (Localization.AtPrime x.asIdeal)}
  -- the singular primes are maximal: a prime of height at most one has a regular local ring
  have hmax : ∀ x ∈ Sing, x.asIdeal.IsMaximal := by
    intro x hx
    by_contra hnm
    obtain ⟨m, hm, hxm⟩ := Ideal.exists_le_maximal x.asIdeal x.isPrime.ne_top
    have hlt : x.asIdeal < m := lt_of_le_of_ne hxm fun h => hnm (h ▸ hm)
    have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    have h2 : (m.height : WithBot ℕ∞) ≤ 2 :=
      hdim ▸ Ideal.height_le_ringKrullDim_of_ne_top hm.ne_top
    have h3 : x.asIdeal.height ≤ 1 := by
      have h4 : x.asIdeal.height + 1 ≤ 2 := h1.trans (WithBot.coe_le_coe.mp h2)
      generalize x.asIdeal.height = c at h4 ⊢
      induction c using ENat.recTopCoe with
      | top => simp at h4
      | coe c => norm_cast at h4 ⊢; omega
    apply hx
    have := hnorm x.asIdeal x.isPrime
    refine isRegularLocalRing_of_isIntegrallyClosed ?_
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height x.asIdeal]
    exact_mod_cast h3
  -- the singular primes form a closed set: the complement of the smooth locus of `Spec C`
  have hcl : IsClosed Sing := by
    let sC := Spec.map (CommRingCat.ofHom (algebraMap K C))
    haveI : LocallyOfFiniteType sC := by
      rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
      exact RingHom.finiteType_algebraMap.mpr inferInstance
    have hsm := (MMP.mem_smoothLocus_iff_isRegularLocalRing_of_perfectField sC).1
    have : Sing = ((sC.smoothLocus : Set (Spec (CommRingCat.of C))))ᶜ := by
      ext x
      let e := (Spec.stalkIso (CommRingCat.of C) x).commRingCatIsoToRingEquiv
      refine (not_congr ⟨fun h => ?_, fun h => ?_⟩).trans (not_congr (hsm x)).symm
      · haveI : IsRegularLocalRing (CommRingCat.of (Localization.AtPrime x.asIdeal)) := h
        exact IsRegularLocalRing.of_ringEquiv e.symm
      · haveI : IsRegularLocalRing ((Spec (CommRingCat.of C)).presheaf.stalk x) := h
        exact IsRegularLocalRing.of_ringEquiv e
    rw [this]
    exact sC.smoothLocus.isOpen.isClosed_compl
  -- hence they are finitely many
  have hfin : Sing.Finite := by
    obtain ⟨S, hS, hScl, hirr, hSing⟩ :=
      TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hcl
    rw [hSing]
    refine hS.sUnion fun t ht => ?_
    obtain ⟨g, hg⟩ := QuasiSober.sober (hirr t ht) (hScl t ht)
    have hgS : g ∈ Sing := by rw [hSing]; exact Set.mem_sUnion_of_mem hg.mem ht
    rw [← hg.def, ((PrimeSpectrum.isClosed_singleton_iff_isMaximal g).mpr (hmax g hgS)).closure_eq]
    exact Set.finite_singleton g
  -- an element in every singular prime other than `q₀`, but not in `q₀`
  have hsel : ∀ x ∈ Sing, x.asIdeal ≠ q₀ → ∃ a ∈ x.asIdeal, a ∉ q₀ := by
    intro x hx hne
    by_contra hc
    push Not at hc
    exact hne ((hmax x hx).eq_of_le (Ideal.IsPrime.ne_top inferInstance) hc)
  choose! a ha haq using hsel
  let T := hfin.toFinset.filter (fun x => x.asIdeal ≠ q₀)
  refine ⟨∏ x ∈ T, a x, fun hmem => ?_, fun Q _ hQ hne => ?_⟩
  · obtain ⟨x, hxT, hx⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    simp only [T, Finset.mem_filter, Set.Finite.mem_toFinset] at hxT
    exact haq x hxT.1 hxT.2 hx
  · by_contra hreg
    have hx : (⟨Q, inferInstance⟩ : PrimeSpectrum C) ∈ Sing := hreg
    have hmemT : (⟨Q, inferInstance⟩ : PrimeSpectrum C) ∈ T := by simp [T, hx, hne]
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem a hmemT
    exact hQ (hc ▸ Ideal.mul_mem_right _ _ (ha _ hx hne))

/-- The local ring of a localization `S = M⁻¹R` at a prime `Q` has dimension the height of the
prime of `R` under `Q`. -/
private theorem ringKrullDim_localization_atPrime_eq_height_comap {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] (M : Submonoid R) [IsLocalization M S] (Q : Ideal S) [Q.IsPrime] :
    ringKrullDim (Localization.AtPrime Q) = (Q.comap (algebraMap R S)).height := by
  have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
    (Localization.AtPrime Q) Q
  rw [ringKrullDim_eq_of_ringEquiv (IsLocalization.algEquiv (Q.comap (algebraMap R S)).primeCompl
    (Localization.AtPrime Q) (Localization.AtPrime (Q.comap (algebraMap R S)))).toRingEquiv,
    IsLocalization.AtPrime.ringKrullDim_eq_height (Q.comap (algebraMap R S))]

variable {k : Type v} [Field k] [CharZero k] {B : Type v} [CommRing B] [IsDomain B]
  [IsIntegrallyClosed B] [Algebra k B] [Algebra.FiniteType k B] (p : Ideal B) [p.IsPrime]
  (A : Type v) [CommRing A] [IsLocalRing A] [Algebra B A] [IsLocalization.AtPrime A p]
  [Algebra k A] [IsScalarTower k B A]
  (K : Type v) [Field K] [Algebra (ResidueField A) K] [IsSepClosure (ResidueField A) K]
  (H : Type v) [CommRing H] [IsLocalRing H] [Algebra A H] [IsHenselization A K H]

include k in
/-- **The ring of the surface model, regular away from `q₀`.** The ring `C` of
`exists_surfaceModel_ring`, localized away from an element outside `q₀` lying in every other
prime with non-regular local ring (`exists_notMem_forall_isRegularLocalRing`): the localization
keeps every property of `exists_surfaceModel_ring`, and every local ring of the localization at a
prime other than `q₀` is regular. -/
private theorem exists_surfaceModel_ring_isRegularLocalRing (s : Ideal B) [s.IsPrime]
    (hsp : s ≤ p) [IsIntegrallyClosed (B ⧸ s)]
    (hsA : ringKrullDim (A ⧸ s.map (algebraMap B A)) = 1) (hA : ringKrullDim A = 2) :
    ∃ (C : Type v) (_ : CommRing C) (_ : IsDomain C) (_ : Algebra K C)
      (_ : Algebra.FiniteType K C) (_ : Algebra B C) (q₀ : Ideal C) (_ : q₀.IsMaximal),
      q₀.comap (algebraMap B C) = p ∧
      (∀ (q : Ideal C) (_ : q.IsPrime), IsIntegrallyClosed (Localization.AtPrime q)) ∧
      (∀ (Q : Ideal C) (_ : Q.IsPrime), Q ≠ q₀ → IsRegularLocalRing (Localization.AtPrime Q)) ∧
      ringKrullDim C = ringKrullDim A ∧ (algebraMap B C).Flat ∧
      (algebraMap B C).FormallyUnramified ∧
      (s.map (algebraMap B C)).IsPrime ∧ s.map (algebraMap B C) ≤ q₀ ∧
      (∀ (Q : Ideal (C ⧸ s.map (algebraMap B C))) (_ : Q.IsPrime),
        IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q)) ∧
      (s.map (algebraMap B C)).height = 1 ∧
      (∃ e : AdicCompletion (maximalIdeal (Localization.AtPrime q₀)) (Localization.AtPrime q₀) ≃+*
          AdicCompletion (maximalIdeal H) H,
        ∀ b : B, e (AdicCompletion.of _ _ (algebraMap B (Localization.AtPrime q₀) b)) =
          AdicCompletion.of _ _ (algebraMap A H (algebraMap B A b))) ∧
      (∀ c : k, algebraMap B C (algebraMap k B c) =
        algebraMap K C (algebraMap (ResidueField A) K (residue A (algebraMap k A c)))) ∧
      ∃ (n : ℕ) (t : Fin n → B), AlgebraicIndependent k (residue A ∘ algebraMap B A ∘ t) ∧
        Algebra.trdeg k (ResidueField A) = n ∧
        ∀ i, algebraMap B C (t i) =
          algebraMap K C (algebraMap (ResidueField A) K (residue A (algebraMap B A (t i)))) := by
  obtain ⟨C, _, _, _, _, _, q₀, _, hq₀, hCnorm, hdim, hCflat, hCfu, hcp, hcq, hcnorm, hcheight,
    ⟨e, he⟩, hkC, nt, t, ht, htrdeg, htC⟩ := exists_surfaceModel_ring (k := k) p A K H s hsp hsA hA
  have : CharZero (ResidueField A) :=
    charZero_of_injective_algebraMap (algebraMap k (ResidueField A)).injective
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap (ResidueField A) K).injective
  obtain ⟨h, hhq, hreg⟩ :=
    exists_notMem_forall_isRegularLocalRing K C hCnorm (hdim.trans hA) q₀
  let C' := Localization.Away h
  have hdis : ∀ {Q : Ideal C}, Q ≤ q₀ → Disjoint (Submonoid.powers h : Set C) Q := by
    intro Q hQ
    rw [Set.disjoint_left]
    rintro _ ⟨n, rfl⟩ hn
    exact hhq (Ideal.IsPrime.mem_of_pow_mem inferInstance n (hQ hn))
  have : Algebra.FiniteType K C' := Algebra.FiniteType.trans (S := C) inferInstance
    (IsLocalization.finiteType_of_monoid_fg (Submonoid.powers h) C')
  have : IsDomain C' := IsLocalization.isDomain_of_le_nonZeroDivisors (M := Submonoid.powers h) C'
    (powers_le_nonZeroDivisors_of_noZeroDivisors fun h0 => hhq (h0 ▸ zero_mem q₀))
  let q₀' : Ideal C' := q₀.map (algebraMap C C')
  have : q₀'.IsMaximal :=
    IsLocalization.isMaximal_of_isMaximal_disjoint (M := Submonoid.powers h) (S := C') q₀
      (hdis le_rfl)
  have hq₀' : q₀'.comap (algebraMap C C') = q₀ :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers h) C' inferInstance (hdis le_rfl)
  -- the local rings of `C'`
  have hlocC : ∀ (Q : Ideal C') [Q.IsPrime],
      IsLocalization (Q.comap (algebraMap C C')).primeCompl (Localization.AtPrime Q) := fun Q _ =>
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization (Submonoid.powers h)
      (Localization.AtPrime Q) Q
  have h1 : IsLocalization q₀.primeCompl (Localization.AtPrime q₀') := by
    have hs : (q₀'.comap (algebraMap C C')).primeCompl = q₀.primeCompl := by
      ext x; rw [Ideal.mem_primeCompl_iff, Ideal.mem_primeCompl_iff, hq₀']
    exact hs ▸ hlocC q₀'
  let σ : Localization.AtPrime q₀' ≃ₐ[C] Localization.AtPrime q₀ :=
    IsLocalization.algEquiv q₀.primeCompl _ _
  -- the boundary
  have hsC : s.map (algebraMap B C') = (s.map (algebraMap B C)).map (algebraMap C C') := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have hcp' : (s.map (algebraMap B C')).IsPrime := hsC ▸
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers h) C' _ hcp (hdis hcq)
  have hsC' : (s.map (algebraMap B C')).comap (algebraMap C C') = s.map (algebraMap B C) := by
    rw [hsC]
    exact IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers h) C' hcp (hdis hcq)
  refine ⟨C', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, q₀',
    inferInstance, ?_, fun Q _ => ?_, fun Q _ hQ => ?_, ?_, ?_, ?_, hcp', ?_, ?_, ?_,
    ⟨(completionEquivOfRingEquiv σ.toRingEquiv).trans e, fun b => ?_⟩, fun c => ?_,
    nt, t, ht, htrdeg, fun i => ?_⟩
  · rw [IsScalarTower.algebraMap_eq B C C', ← Ideal.comap_comap, hq₀', hq₀]
  · have := hCnorm (Q.comap (algebraMap C C')) inferInstance
    have := hlocC Q
    exact IsIntegrallyClosed.of_equiv
      (IsLocalization.algEquiv (Q.comap (algebraMap C C')).primeCompl
        (Localization.AtPrime (Q.comap (algebraMap C C'))) (Localization.AtPrime Q)).toRingEquiv
  · have hhQ : h ∉ Q.comap (algebraMap C C') := fun hh =>
      Ideal.IsPrime.ne_top (inferInstance : Q.IsPrime) (Ideal.eq_top_of_isUnit_mem Q hh
        (IsLocalization.map_units C' ⟨h, Submonoid.mem_powers h⟩))
    have hne : Q.comap (algebraMap C C') ≠ q₀ := fun hQ₀ =>
      hQ ((IsLocalization.map_comap (Submonoid.powers h) C' Q).symm.trans
        (congrArg (Ideal.map (algebraMap C C')) hQ₀))
    have := hreg _ hhQ hne
    have := hlocC Q
    exact IsRegularLocalRing.of_ringEquiv
      (IsLocalization.algEquiv (Q.comap (algebraMap C C')).primeCompl
        (Localization.AtPrime (Q.comap (algebraMap C C'))) (Localization.AtPrime Q)).toRingEquiv
  · rw [← MMP.IdealHeight.ringKrullDim_localization_atPrime_eq_of_isMaximal_of_finiteType K q₀',
      ringKrullDim_localization_atPrime_eq_height_comap (Submonoid.powers h) q₀', hq₀',
      ← IsLocalization.AtPrime.ringKrullDim_eq_height q₀ (Localization.AtPrime q₀),
      MMP.IdealHeight.ringKrullDim_localization_atPrime_eq_of_isMaximal_of_finiteType K q₀, hdim]
  · rw [IsScalarTower.algebraMap_eq B C C']
    exact hCflat.comp
      (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat C' (Submonoid.powers h)))
  · rw [IsScalarTower.algebraMap_eq B C C']
    exact hCfu.comp (RingHom.formallyUnramified_algebraMap.mpr
      (Algebra.FormallyUnramified.of_isLocalization (Submonoid.powers h)))
  · rw [hsC]
    exact Ideal.map_mono hcq
  · rw [hsC]
    intro Q _
    exact isDomain_and_isIntegrallyClosed_of_isLocalization
      (Algebra.algebraMapSubmonoid (C ⧸ s.map (algebraMap B C)) (Submonoid.powers h))
      (fun Q' _ => hcnorm Q' inferInstance) Q
  · have h2 := (IsLocalization.AtPrime.ringKrullDim_eq_height (s.map (algebraMap B C'))
      (Localization.AtPrime (s.map (algebraMap B C')))).symm.trans
        (ringKrullDim_localization_atPrime_eq_height_comap (Submonoid.powers h)
          (s.map (algebraMap B C')))
    rw [hsC', hcheight] at h2
    exact_mod_cast h2
  · rw [RingEquiv.trans_apply, completionEquivOfRingEquiv_of]
    have hb : σ (algebraMap B (Localization.AtPrime q₀') b) =
        algebraMap B (Localization.AtPrime q₀) b := by
      rw [IsScalarTower.algebraMap_apply B C' (Localization.AtPrime q₀'),
        IsScalarTower.algebraMap_apply B C C', ← IsScalarTower.algebraMap_apply C C',
        AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
    exact (congrArg (fun z => e (AdicCompletion.of _ _ z)) hb).trans (he b)
  · rw [IsScalarTower.algebraMap_apply B C C', hkC c, ← IsScalarTower.algebraMap_apply]
  · rw [IsScalarTower.algebraMap_apply B C C', htC i, ← IsScalarTower.algebraMap_apply]

end RegularModel

section BaseChange

/-- Let `f : W ⟶ U` restrict to an open immersion on a nonempty open `Wo` of the irreducible `W`,
and let `g : Y' ⟶ U` be flat. If `W ×_U Y'` is nonempty, the preimage `O` of `Wo` is a nonempty
dense open of `W ×_U Y'` mapping isomorphically onto an open of `Y'`: `O ⟶ Y'` is a base change of
`Wo ⟶ U`, and `O` is dense since `W ×_U Y' ⟶ W` is generalizing. -/
private theorem exists_dense_open_pullback_of_flat {W U Y' : Scheme.{v}} (f : W ⟶ U) (g : Y' ⟶ U)
    [IrreducibleSpace W] [Flat g]
    (Wo : W.Opens) (hWo : (Wo : Set W).Nonempty) (hWoi : IsOpenImmersion (Wo.ι ≫ f))
    [Nonempty (pullback f g : Scheme.{v})] :
    ∃ O : (pullback f g : Scheme.{v}).Opens, (O : Set (pullback f g : Scheme.{v})).Nonempty ∧
      IsOpenImmersion (O.ι ≫ pullback.snd f g) ∧
      closure (O : Set (pullback f g : Scheme.{v})) = Set.univ := by
  haveI : Flat (pullback.fst f g) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Flat)
      (IsPullback.of_hasPullback f g).flip inferInstance
  let O := (pullback.fst f g) ⁻¹ᵁ Wo
  have hsq : IsPullback ((pullback.fst f g) ∣_ Wo) (O.ι ≫ pullback.snd f g) (Wo.ι ≫ f) g :=
    (isPullback_morphismRestrict (pullback.fst f g) Wo).paste_vert (IsPullback.of_hasPullback f g)
  have hgen : ∀ w' : (pullback f g : Scheme.{v}), ∃ w'' ∈ (O : Set (pullback f g : Scheme.{v})),
      w'' ⤳ w' := by
    intro w'
    obtain ⟨w'', h1, h2⟩ := Flat.generalizingMap (pullback.fst f g)
      ((genericPoint_spec W).specializes (Set.mem_univ ((pullback.fst f g).base w')))
    refine ⟨w'', ?_, h1⟩
    show (pullback.fst f g).base w'' ∈ Wo
    rw [h2]
    exact (genericPoint_spec W).mem_open_set_iff Wo.isOpen |>.mpr (by simpa using hWo)
  obtain ⟨w₀⟩ := ‹Nonempty (pullback f g : Scheme.{v})›
  obtain ⟨o, ho, -⟩ := hgen w₀
  refine ⟨O, ⟨o, ho⟩,
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion) hsq hWoi, ?_⟩
  refine Set.eq_univ_of_forall fun w' => ?_
  obtain ⟨w'', hw'', hsp⟩ := hgen w'
  exact closure_mono (Set.singleton_subset_iff.mpr hw'') (specializes_iff_mem_closure.mp hsp)

/-- **Irreducibility of a flat base change of a birational map.** In the situation of
`exists_dense_open_pullback_of_flat`, with `Y'` irreducible, `W ×_U Y'` is irreducible. -/
private theorem irreducibleSpace_pullback_of_flat {W U Y' : Scheme.{v}} (f : W ⟶ U) (g : Y' ⟶ U)
    [IrreducibleSpace W] [IrreducibleSpace Y'] [Flat g]
    (Wo : W.Opens) (hWo : (Wo : Set W).Nonempty) (hWoi : IsOpenImmersion (Wo.ι ≫ f))
    [Nonempty (pullback f g : Scheme.{v})] :
    IrreducibleSpace (pullback f g : Scheme.{v}) := by
  obtain ⟨O, ⟨o, ho⟩, hOi, hdense⟩ := exists_dense_open_pullback_of_flat f g Wo hWo hWoi
  haveI : Nonempty O := ⟨⟨o, ho⟩⟩
  have hOirr : IrreducibleSpace O := hOi.base_open.irreducibleSpace
  have hirr : IsIrreducible (O : Set (pullback f g : Scheme.{v})) :=
    isIrreducible_iff_irreducibleSpace.mpr hOirr
  rw [irreducibleSpace_def, Set.top_eq_univ, ← hdense]
  exact hirr.closure

/-- **Birationality of a flat base change of a birational map.** In the situation of
`exists_dense_open_pullback_of_flat`, with `Y'` irreducible, `W ×_U Y' ⟶ Y'` is birational. -/
private theorem isBirationalMorphism_pullback_snd_of_flat {W U Y' : Scheme.{v}} (f : W ⟶ U)
    (g : Y' ⟶ U) [IrreducibleSpace W] [IrreducibleSpace Y'] [Flat g]
    (Wo : W.Opens) (hWo : (Wo : Set W).Nonempty) (hWoi : IsOpenImmersion (Wo.ι ≫ f))
    [Nonempty (pullback f g : Scheme.{v})] :
    MMP.Mori.IsBirationalMorphism (pullback.snd f g) := by
  haveI := irreducibleSpace_pullback_of_flat f g Wo hWo hWoi
  obtain ⟨O, hOne, hOi, -⟩ := exists_dense_open_pullback_of_flat f g Wo hWo hWoi
  let V := (O.ι ≫ pullback.snd f g).opensRange
  have h : O ≤ (pullback.snd f g) ⁻¹ᵁ V := fun x hx => ⟨⟨x, hx⟩, rfl⟩
  have hVne : (V : Set Y').Nonempty := by
    obtain ⟨o, ho⟩ := hOne
    exact ⟨_, ⟨⟨o, ho⟩, rfl⟩⟩
  refine MMP.Flips.isBirationalMorphism_of_isIso_resLE _ O V hOne hVne h ?_
  have : (pullback.snd f g).resLE V O h = (O.ι ≫ pullback.snd f g).isoOpensRange.hom := by
    rw [← cancel_mono V.ι, Scheme.Hom.resLE_comp_ι, Scheme.Hom.isoOpensRange_hom_ι]
  rw [this]
  infer_instance

end BaseChange

/-- The `k`-algebra structure of a field `κ` over the residue field `κ(P)` of a scheme over `k`. -/
private noncomputable abbrev residueExtAlgebra {k : Type v} [Field k] {X : Scheme.{v}}
    (sX : X ⟶ Spec (.of k)) (P : X) (κ : Type v) [Field κ]
    [Algebra (ResidueField (X.presheaf.stalk P)) κ] : Algebra k κ :=
  letI := stalkAlgebra sX P
  ((algebraMap (ResidueField (X.presheaf.stalk P)) κ).comp
    (algebraMap k (ResidueField (X.presheaf.stalk P)))).toAlgebra

section SchemeModel

/-- The local homomorphism `𝒪_{X,P} → 𝒪_{Spec C, y}` of `Spec C ⟶ Spec Γ(X, V) ⟶ X`, for an
affine open `V ∋ P` and `g : Γ(X, V) → C`, restricted to sections over `V`: it is `g` followed by
`C → 𝒪_{Spec C, y}`. -/
private theorem germ_comp_stalkMap_fromSpec {X : Scheme.{v}} {V : X.Opens} (hV : IsAffineOpen V)
    {C : CommRingCat.{v}} (g : Γ(X, V) ⟶ C) (y : Spec C) {P : X} (hPV : P ∈ V)
    (hjy : (Spec.map g ≫ hV.fromSpec).base y ⤳ P) :
    X.presheaf.germ V P hPV ≫ X.presheaf.stalkSpecializes hjy ≫
        (Spec.map g ≫ hV.fromSpec).stalkMap y =
      g ≫ (Scheme.ΓSpecIso C).inv ≫ (Spec C).presheaf.germ ⊤ y trivial := by
  have hy : hV.fromSpec.base ((Spec.map g).base y) ∈ V := hjy.mem_open V.isOpen hPV
  rw [← Category.assoc, X.presheaf.germ_stalkSpecializes hPV hjy, Scheme.Hom.stalkMap_comp]
  erw [hV.fromSpec.germ_stalkMap_assoc V _ hy]
  rw [IsAffineOpen.fromSpec_app_self]
  erw [Category.assoc, TopCat.Presheaf.germ_res_assoc]
  erw [(Spec.map g).germ_stalkMap ⊤ y trivial, Scheme.ΓSpecIso_inv_naturality_assoc]
  rfl

/-- **The surface germ.** Let `P` be a point of a normal variety `X` over a field `k` of
characteristic zero, of codimension one on a normal prime divisor `S`. There are a normal surface
germ `(Y, y)` over `κsep`, a prime divisor `C` of `Y` through `y`, smooth over `κsep`, and a
morphism `j : Y ⟶ X` with `j y = P` and `j(η_C) = η_S`, and an isomorphism `𝒪̂_{Y,y} ≅ Ĥ`
compatible with `𝒪_{X,P} → 𝒪_{Y,y}` and `𝒪_{X,P} → H`, carrying `I_C` to `I_S`. The point
`j(η_C)` is a specialization of `η_S` of codimension one, since `j` preserves codimensions. -/
private theorem exists_surfaceModel_germ
    (k : Type v) [Field k] [CharZero k]
    (X : Scheme.{v}) (sX : X ⟶ Spec (.of k)) (hX : IsNormalVariety k sX)
    (S : Mori.PrimeDivisor X) (hS : IsNormal S.idealSheaf.subscheme)
    (P : X) (hPS : S.genericPoint ⤳ P)
    (hP : ringKrullDim (X.presheaf.stalk P ⧸
      RingHom.ker (X.presheaf.stalkSpecializes hPS ≫ X.residue S.genericPoint).hom) = 1)
    (κsep : Type v) [Field κsep] [Algebra (ResidueField (X.presheaf.stalk P)) κsep]
    [IsSepClosure (ResidueField (X.presheaf.stalk P)) κsep]
    (H : Type v) [CommRing H] [IsLocalRing H] [Algebra (X.presheaf.stalk P) H]
    [IsHenselization (X.presheaf.stalk P) κsep H] :
    let A := X.presheaf.stalk P
    let R := AdicCompletion (maximalIdeal H) H
    let IS : Ideal A :=
      RingHom.ker (X.presheaf.stalkSpecializes hPS ≫ X.residue S.genericPoint).hom
    ∃ (Y : Scheme.{v}) (sY : Y ⟶ Spec (.of κsep)) (j : Y ⟶ X) (y : Y) (C : Mori.PrimeDivisor Y)
      (hCy : C.genericPoint ⤳ y) (hjy : j.base y ⤳ P),
      IsSurfaceGerm sY y ∧ j.base y = P ∧ Smooth (C.idealSheaf.subschemeι ≫ sY) ∧
      j.base C.genericPoint = S.genericPoint ∧
      (let φ : A →+* Y.presheaf.stalk y :=
        (X.presheaf.stalkSpecializes hjy ≫ j.stalkMap y).hom
      let IC : Ideal (Y.presheaf.stalk y) :=
        RingHom.ker (Y.presheaf.stalkSpecializes hCy ≫ Y.residue C.genericPoint).hom
      ∃ e : AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y) ≃+* R,
        (∀ a : A, e (algebraMap _ _ (φ a)) = algebraMap H R (algebraMap A H a)) ∧
        (IC.map (algebraMap _ _)).map e = (IS.map (algebraMap A H)).map (algebraMap H R)) ∧
      Flat j ∧ FormallyUnramified j ∧
      (letI := residueExtAlgebra sX P κsep;
        j ≫ sX = sY ≫ Spec.map (CommRingCat.ofHom (algebraMap k κsep))) ∧
      ∃ (_ : IsIntegral X) (_ : IsIntegral Y) (_ : IsDominant j) (e : ℕ)
        (t : Fin e → X.functionField) (c : Fin e → κsep),
        (letI := residueExtAlgebra sX P κsep; AlgebraicIndependent k c) ∧
        topologicalKrullDim X = (e + 2 : ℕ) ∧
        ∀ i, functionFieldMap j (t i) =
          (letI := functionFieldAlgebra sY; algebraMap κsep Y.functionField (c i)) := by
  intro A R IS
  obtain ⟨hvar, hnorm⟩ := hX
  obtain ⟨V, hV, hPV, -⟩ := exists_isAffineOpen_mem_and_subset (show P ∈ (⊤ : X.Opens) from trivial)
  have : Nonempty V := ⟨⟨P, hPV⟩⟩
  letI : Algebra k Γ(X, V) := sectionAlgebra sX V
  letI : Algebra k (X.presheaf.stalk P) := stalkAlgebra sX P
  letI : Algebra Γ(X, V) (X.presheaf.stalk P) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨P, hPV⟩
  have : Algebra.FiniteType k Γ(X, V) := finiteType_sectionAlgebra sX hV
  have : IsScalarTower k Γ(X, V) (X.presheaf.stalk P) := isScalarTower_section_stalk sX V ⟨P, hPV⟩
  have hnormV : IsNormalRing Γ(X, V) := by
    have h := (isNormal_tfae X).out 1 2
    exact h.mp hnorm ⟨V, hV⟩
  have : IsIntegrallyClosed Γ(X, V) :=
    IsIntegrallyClosed.of_localization_maximal fun q _ _ => (hnormV q).2
  have := hV.isLocalization_stalk ⟨P, hPV⟩
  have hηV : S.genericPoint ∈ V := hPS.mem_open V.isOpen hPV
  set s := (hV.primeIdealOf ⟨S.genericPoint, hηV⟩).asIdeal with hs_def
  have hsp : s ≤ (hV.primeIdealOf ⟨P, hPV⟩).asIdeal := primeIdealOf_le_of_specializes hV hPS hPV
  haveI : IsIntegrallyClosed (Γ(X, V) ⧸ s) := isIntegrallyClosed_quotient_primeIdealOf S hS hV hηV
  have hker : IS = s.map (algebraMap Γ(X, V) (X.presheaf.stalk P)) :=
    ker_stalkSpecializes_residue_eq_map hV hPS hPV
  have hsA : ringKrullDim (X.presheaf.stalk P ⧸ s.map (algebraMap Γ(X, V) (X.presheaf.stalk P))) =
      1 := by rwa [← hker]
  have hA := ringKrullDim_stalk_eq_two k X sX ⟨hvar, hnorm⟩ S P hPS hP
  obtain ⟨C, _, _, _, _, _, q₀, _, hq₀, hCnorm, hCreg, hdim, hCflat, hCfu, hcp, hcq, hcnorm,
    hcheight, ⟨e, he⟩, hkC, nt, t, ht, htrdeg, htC⟩ :=
    exists_surfaceModel_ring_isRegularLocalRing (k := k) (B := Γ(X, V))
      (hV.primeIdealOf ⟨P, hPV⟩).asIdeal
      (X.presheaf.stalk P) κsep H s hsp hsA hA
  have : IsIntegrallyClosed C :=
    IsIntegrallyClosed.of_localization_maximal fun q _ _ => hCnorm q inferInstance
  let g : Γ(X, V) ⟶ CommRingCat.of C := CommRingCat.ofHom (algebraMap Γ(X, V) C)
  let j : Spec (CommRingCat.of C) ⟶ X := Spec.map g ≫ hV.fromSpec
  let y : Spec (CommRingCat.of C) := ⟨q₀, inferInstance⟩
  have hgy : (Spec.map g).base y = hV.primeIdealOf ⟨P, hPV⟩ :=
    PrimeSpectrum.ext hq₀
  have hjP : j.base y = P := by
    change hV.fromSpec.base ((Spec.map g).base y) = P
    rw [hgy]
    exact hV.fromSpec_primeIdealOf ⟨P, hPV⟩
  have hjy : j.base y ⤳ P := by rw [hjP]
  let σ : (Spec (CommRingCat.of C)).presheaf.stalk y ≃+* Localization.AtPrime q₀ :=
    (Spec.stalkIso (CommRingCat.of C) y).commRingCatIsoToRingEquiv
  -- the curve `C`: the prime divisor with generic point `𝔠 = s C`
  let ξ : Spec (CommRingCat.of C) := ⟨s.map (algebraMap Γ(X, V) C), hcp⟩
  have hcoh : Order.coheight ξ = 1 := by
    have h1 := ringKrullDim_stalk_eq_coheight ξ
    rw [ringKrullDim_eq_of_ringEquiv
      (Spec.stalkIso (CommRingCat.of C) ξ).commRingCatIsoToRingEquiv,
      IsLocalization.AtPrime.ringKrullDim_eq_height (s.map (algebraMap Γ(X, V) C))
        (Localization.AtPrime (s.map (algebraMap Γ(X, V) C))), hcheight] at h1
    exact (WithBot.coe_eq_coe.mp h1).symm
  let Cd : Mori.PrimeDivisor (Spec (CommRingCat.of C)) :=
    AlgebraicGeometry.PrimeDivisor.ofCoheightOne ξ hcoh
  have hCg : Cd.genericPoint = ξ := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne ξ hcoh
  have hCy : Cd.genericPoint ⤳ y := by
    rw [hCg]; exact (PrimeSpectrum.le_iff_specializes ξ y).mp hcq
  haveI : CharZero (ResidueField (X.presheaf.stalk P)) :=
    charZero_of_injective_algebraMap (algebraMap k _).injective
  haveI : CharZero κsep :=
    charZero_of_injective_algebraMap (algebraMap (ResidueField (X.presheaf.stalk P)) κsep).injective
  -- the compatibility of `e` with `𝒪_{X,P}`
  let φ := (X.presheaf.stalkSpecializes hjy ≫ j.stalkMap y).hom
  let e' := (completionEquivOfRingEquiv σ).trans e
  have key := germ_comp_stalkMap_fromSpec hV g y hPV hjy
  have hf : (e'.toRingHom.comp ((algebraMap _ (AdicCompletion _ _)).comp φ)) =
      (algebraMap H (AdicCompletion (maximalIdeal H) H)).comp (algebraMap _ H) := by
    refine IsLocalization.ringHom_ext (hV.primeIdealOf ⟨P, hPV⟩).asIdeal.primeCompl
      (RingHom.ext fun b => ?_)
    have key' := key
    rw [← Spec.algebraMap_stalkIso_inv] at key'
    have k2 : φ (algebraMap Γ(X, V) _ b) =
        σ.symm (algebraMap C (Localization.AtPrime q₀) (algebraMap Γ(X, V) C b)) :=
      congrArg (fun h => h.hom b) key'
    simp only [RingHom.comp_apply, k2, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, e',
      RingEquiv.trans_apply]
    rw [show algebraMap _ (AdicCompletion _ _) (σ.symm _) = AdicCompletion.of _ _ _ from rfl,
      completionEquivOfRingEquiv_of, Algebra.algebraMap_self, RingHom.id_apply,
      RingEquiv.apply_symm_apply, ← IsScalarTower.algebraMap_apply]
    exact he b
  have hjflat : Flat j := by
    have : Flat (Spec.map g) := Flat.SpecMap_iff.mpr hCflat
    infer_instance
  have hjfu : FormallyUnramified j := by
    have h1 : FormallyUnramified (Spec.map g) :=
      (HasRingHomProperty.Spec_iff (P := @FormallyUnramified)).mpr hCfu
    have h2 : FormallyUnramified hV.fromSpec :=
      FormallyUnramified.instOfIsOpenImmersionDiagonalScheme hV.fromSpec
    exact MorphismProperty.comp_mem @FormallyUnramified _ _ h1 h2
  haveI : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap κsep C))) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  -- the curve `C` lies over `S`: `j(η_C)` is a specialization of `η_S` of the same codimension
  have hjC : j.base Cd.genericPoint = S.genericPoint := by
    rw [hCg]
    haveI := hjflat
    haveI := hjfu
    haveI : LocallyOfFiniteType sX := hvar.toLocallyOfFiniteType
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    haveI : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing κsep C
    haveI : CharZero (ResidueField (X.presheaf.stalk (j.base ξ))) := by
      letI := stalkAlgebra sX (j.base ξ)
      exact charZero_of_injective_algebraMap (algebraMap k _).injective
    have hc : Order.coheight (j.base ξ) = 1 := (coheight_map_eq j ξ).trans hcoh
    have hsp : S.genericPoint ⤳ j.base ξ := by
      have h := ((PrimeSpectrum.le_iff_specializes _ _).mp
        (show (hV.primeIdealOf ⟨S.genericPoint, hηV⟩).asIdeal ≤ ((Spec.map g).base ξ).asIdeal
          from Ideal.le_comap_map)).map hV.fromSpec.continuous
      rwa [hV.fromSpec_primeIdealOf] at h
    by_contra hne
    have hlt : j.base ξ < S.genericPoint := lt_of_le_not_ge (Scheme.le_iff_specializes.mpr hsp)
      fun h => hne ((Scheme.le_iff_specializes.mp h).antisymm hsp).eq
    have h2 := Order.coheight_add_one_le hlt
    rw [hc, S.coheight_genericPoint] at h2
    exact absurd h2 (by decide)
  refine ⟨Spec (CommRingCat.of C), Spec.map (CommRingCat.ofHom (algebraMap κsep C)), j, y, Cd, hCy,
    hjy, ?_, hjP, ?_, hjC, ⟨e', fun a => DFunLike.congr_fun hf a, ?_⟩, hjflat, hjfu, ?_, ?_⟩
  · -- `(Y, y)` is a surface germ: `Y ∖ {y}` is regular, hence smooth
    unfold IsSurfaceGerm
    refine ⟨⟨(Mori.isVariety_iff _ _).mpr ⟨inferInstance, inferInstance, inferInstance,
      inferInstance⟩, isNormal_spec_of_isIntegrallyClosed C⟩,
      (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim C).trans (hdim.trans hA),
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal y).mpr inferInstance, fun y' hy' => ?_⟩
    haveI : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap κsep C))) :=
      LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
    haveI := hCreg y'.asIdeal y'.isPrime fun h => hy' (PrimeSpectrum.ext h)
    rw [smoothLocus_eq_smoothLocus]
    exact ((MMP.mem_smoothLocus_iff_isRegularLocalRing_of_perfectField _).1 y').mpr
      (IsRegularLocalRing.of_ringEquiv
        (Spec.stalkIso (CommRingCat.of C) y').commRingCatIsoToRingEquiv.symm)
  · exact smooth_subschemeι_ofCoheightOne κsep (CommRingCat.of C) ξ hcoh fun Q _ hQ =>
      isRegularLocalRing_localization_quotient κsep C (le_of_eq (hdim.trans hA))
        (s.map (algebraMap Γ(X, V) C)) hcheight (fun Q' _ => hcnorm Q' inferInstance) Q hQ
  · -- the ideal clause: `I_C 𝒪_{Y,y} = I_S 𝒪_{Y,y}`
    let γ : C →+* (Spec (CommRingCat.of C)).presheaf.stalk y :=
      ((Scheme.ΓSpecIso (CommRingCat.of C)).inv ≫
        (Spec (CommRingCat.of C)).presheaf.germ ⊤ y trivial).hom
    have hprime : ∀ (x : Spec (CommRingCat.of C)) (hx : x ∈ (⊤ : (Spec (CommRingCat.of C)).Opens)),
        x = ξ → ((isAffineOpen_top _).primeIdealOf ⟨x, hx⟩).asIdeal =
          (s.map (algebraMap Γ(X, V) C)).comap (Scheme.ΓSpecIso (CommRingCat.of C)).hom.hom := by
      rintro x hx rfl
      exact primeIdealOf_top_Spec (CommRingCat.of C) ξ
    have hcomap : (s.map (algebraMap Γ(X, V) C)).comap
        (Scheme.ΓSpecIso (CommRingCat.of C)).hom.hom =
        (s.map (algebraMap Γ(X, V) C)).map (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom := by
      symm
      exact Ideal.map_comap_of_equiv
        (Scheme.ΓSpecIso (CommRingCat.of C)).commRingCatIsoToRingEquiv.symm
    have hIC : RingHom.ker ((Spec (CommRingCat.of C)).presheaf.stalkSpecializes hCy ≫
        (Spec (CommRingCat.of C)).residue Cd.genericPoint).hom =
        (s.map (algebraMap Γ(X, V) C)).map γ := by
      rw [ker_stalkSpecializes_residue_eq_map (isAffineOpen_top _) hCy trivial,
        hprime _ _ hCg, hcomap, Ideal.map_map]
      rfl
    have hIS : IS.map φ = (s.map (algebraMap Γ(X, V) C)).map γ := by
      rw [hker, Ideal.map_map, Ideal.map_map]
      congr 1
      exact congrArg CommRingCat.Hom.hom key
    rw [hIC, ← hIS, Ideal.map_map, Ideal.map_map]
    change Ideal.map e'.toRingHom _ = _
    rw [Ideal.map_map]
    congr 1
  · -- compatibility of the structure morphisms
    have h1 : hV.fromSpec ≫ sX =
        Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appLE ⊤ V (by simp)) := by
      rw [← IsAffineOpen.SpecMap_appLE_fromSpec sX (isAffineOpen_top _) hV (by simp),
        IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
    change (Spec.map g ≫ hV.fromSpec) ≫ sX = _
    rw [Category.assoc, h1, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext c
    change algebraMap Γ(X, V) C (algebraMap k Γ(X, V) c) = algebraMap κsep C
      ((residueExtAlgebra sX P κsep).algebraMap c)
    rw [hkC c]
    rfl
  · haveI : IsIntegral X := hvar.toIsIntegral
    have hdom : IsDominant j := isDominant_of_flat j
    letI := residueExtAlgebra sX P κsep
    haveI : IsScalarTower k (ResidueField (X.presheaf.stalk P)) κsep :=
      IsScalarTower.of_algebraMap_eq' rfl
    refine ⟨inferInstance, inferInstance, hdom, nt, fun i => X.germToFunctionField V (t i),
      fun i => algebraMap (ResidueField (X.presheaf.stalk P)) κsep
        (residue _ (algebraMap Γ(X, V) (X.presheaf.stalk P) (t i))), ?_, ?_, fun i => ?_⟩
    · exact ht.map' (f := IsScalarTower.toAlgHom k (ResidueField (X.presheaf.stalk P)) κsep)
        (algebraMap (ResidueField (X.presheaf.stalk P)) κsep).injective
    · have : LocallyOfFiniteType sX := hvar.toLocallyOfFiniteType
      rw [topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k X sX P,
        topologicalKrullDimAt_eq_trdeg_add_krullDim_stalk k X sX P, hA]
      have hal : ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫ X.Γevaluation P).hom.toAlgebra =
          (inferInstance : Algebra k (ResidueField (X.presheaf.stalk P))) :=
        Algebra.algebra_ext _ _ fun _ => rfl
      have htr : (Cardinal.toENat (@Algebra.trdeg k (X.residueField P) _ _
          ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫ X.Γevaluation P).hom.toAlgebra) :
            WithBot ℕ∞) = nt := by
        rw [hal]
        exact congrArg (fun c => ((Cardinal.toENat c : ℕ∞) : WithBot ℕ∞)) htrdeg |>.trans
          (by simp)
      rw [htr]
      push_cast
      rfl
    · have hyV : j.base y ∈ V := hjP ▸ hPV
      have h1 : X.germToFunctionField V (t i) = algebraMap (X.presheaf.stalk (j.base y))
          X.functionField
            ((X.presheaf.germ V P hPV ≫ X.presheaf.stalkSpecializes hjy).hom (t i)) := by
        rw [TopCat.Presheaf.germ_stalkSpecializes, Scheme.algebraMap_germ_eq_germToFunctionField]
      letI := stalkAlgebra (Spec.map (CommRingCat.ofHom (algebraMap κsep C))) y
      letI := functionFieldAlgebra (Spec.map (CommRingCat.ofHom (algebraMap κsep C)))
      have hT := isScalarTower_stalk_functionField
        (Spec.map (CommRingCat.ofHom (algebraMap κsep C))) y
      change functionFieldMap j (X.germToFunctionField V (t i)) = _
      rw [h1, functionFieldMap_algebraMap_stalk, IsScalarTower.algebraMap_apply κsep
        ((Spec (CommRingCat.of C)).presheaf.stalk y)]
      congr 1
      have h2 := congrArg (fun f => CommRingCat.Hom.hom f (t i)) key
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2 ⊢
      rw [h2]
      change ((Scheme.ΓSpecIso (CommRingCat.of C)).inv ≫ (Spec (CommRingCat.of C)).presheaf.germ ⊤ y
        trivial).hom (algebraMap Γ(X, V) C (t i)) = ((Scheme.ΓSpecIso (.of κsep)).inv ≫
          (Spec.map (CommRingCat.ofHom (algebraMap κsep C))).appTop ≫
          (Spec (CommRingCat.of C)).presheaf.germ ⊤ y (TopologicalSpace.Opens.mem_top _)).hom _
      rw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, htC i]
      rfl

end SchemeModel

section SNCTransport

/-- The ideal of a closed subscheme at a generization `x` of `x₀` is the extension of its ideal at
`x₀` along the generization map `𝒪_{X,x₀} → 𝒪_{X,x}`. -/
private theorem stalk_idealSheaf_eq_map_stalkSpecializes {X : Scheme.{v}} (I : X.IdealSheafData)
    {x x₀ : X} (h : x ⤳ x₀) :
    IdealSheafData.stalk I x =
      (IdealSheafData.stalk I x₀).map (X.presheaf.stalkSpecializes h).hom := by
  obtain ⟨U, hU, hx₀U, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show x₀ ∈ (⊤ : X.Opens) from trivial)
  have hxU : x ∈ U := h.mem_open U.isOpen hx₀U
  rw [IdealSheafData.stalk_eq_map_germ I x ⟨U, hU⟩ hxU,
    IdealSheafData.stalk_eq_map_germ I x₀ ⟨U, hU⟩ hx₀U, Ideal.map_map, ← CommRingCat.hom_comp,
    TopCat.Presheaf.germ_stalkSpecializes]

/-- The differential of an element of `𝔪²` vanishes modulo `𝔪`. -/
private theorem tmul_D_eq_zero_of_mem_sq {k R : Type*} [Field k] [CommRing R] [IsLocalRing R]
    [Algebra k R] {x : R} (hx : x ∈ maximalIdeal R ^ 2) :
    (1 : ResidueField R) ⊗ₜ[R] KaehlerDifferential.D k R x = 0 := by
  rw [pow_two] at hx
  refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun x y hx hy => ?_)
  · rw [Derivation.leibniz, TensorProduct.tmul_add, TensorProduct.tmul_smul,
      TensorProduct.tmul_smul, ← algebraMap_smul (ResidueField R) a,
      ← algebraMap_smul (ResidueField R) b, IsLocalRing.ResidueField.algebraMap_eq,
      (residue_eq_zero_iff a).mpr ha, (residue_eq_zero_iff b).mpr hb, zero_smul, zero_smul,
      add_zero]
  · rw [map_add, TensorProduct.tmul_add, hx, hy, add_zero]

/-- Modulo `𝔪`, the differential of `∑ bⱼ yⱼ` with `yⱼ ∈ 𝔪` is `∑ b̄ⱼ dyⱼ`. -/
private theorem tmul_D_sum {k R : Type*} [Field k] [CommRing R] [IsLocalRing R]
    [Algebra k R] {r : ℕ} (y : Fin r → R) (hy : ∀ i, y i ∈ maximalIdeal R) (b : Fin r → R) :
    (1 : ResidueField R) ⊗ₜ[R] KaehlerDifferential.D k R (∑ j, b j * y j) =
      ∑ j, residue R (b j) • ((1 : ResidueField R) ⊗ₜ[R] KaehlerDifferential.D k R (y j)) := by
  rw [map_sum, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Derivation.leibniz, TensorProduct.tmul_add, TensorProduct.tmul_smul,
    TensorProduct.tmul_smul, ← algebraMap_smul (ResidueField R) (y j),
    IsLocalRing.ResidueField.algebraMap_eq, (residue_eq_zero_iff _).mpr (hy j), zero_smul,
    add_zero, ← algebraMap_smul (ResidueField R) (b j), IsLocalRing.ResidueField.algebraMap_eq]

/-- **Extending to a regular system of parameters.** In a regular local ring over `k`, elements
of `𝔪` whose differentials are independent modulo `𝔪` are the first members of a regular system
of parameters: their classes in `𝔪/𝔪²` are independent, so extend to a basis, and lifts of a
basis of `𝔪/𝔪²` generate `𝔪` by Nakayama. -/
private theorem exists_isRegularSystemOfParameters_append {k R : Type*} [Field k] [CommRing R]
    [IsRegularLocalRing R] [Algebra k R] {r : ℕ} (y : Fin r → R)
    (hy : ∀ i, y i ∈ maximalIdeal R)
    (hli : LinearIndependent (ResidueField R)
      (fun i => (1 : ResidueField R) ⊗ₜ[R] KaehlerDifferential.D k R (y i))) :
    ∃ (s : ℕ) (w : Fin s → R), MMP.Mori.IsRegularSystemOfParameters (Fin.append y w) := by
  classical
  let c : Fin r → CotangentSpace R := fun i => (maximalIdeal R).toCotangent ⟨y i, hy i⟩
  have hc : LinearIndependent (ResidueField R) c := by
    rw [Fintype.linearIndependent_iff] at hli ⊢
    intro a ha i
    choose b hb using fun i => residue_surjective (a i)
    have hmem : (∑ j, b j * y j) ∈ maximalIdeal R ^ 2 := by
      have h1 : (maximalIdeal R).toCotangent
          (∑ j, b j • (⟨y j, hy j⟩ : maximalIdeal R)) = 0 := by
        rw [map_sum, ← ha]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, ← hb j]
        exact (algebraMap_smul (ResidueField R) (b j) (c j)).symm
      rw [Ideal.toCotangent_eq_zero, AddSubmonoidClass.coe_finsetSum] at h1
      exact h1
    have h2 := tmul_D_eq_zero_of_mem_sq (k := k) hmem
    rw [tmul_D_sum y hy b] at h2
    have := hli (fun j => residue R (b j)) h2 i
    rwa [← hb i]
  set d := Module.finrank (ResidueField R) (CotangentSpace R) with hd
  have hdim : ringKrullDim R = d := by
    rw [← IsRegularLocalRing.spanFinrank_maximalIdeal,
      spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
  have hrd : r ≤ d := by simpa using hc.fintype_card_le_finrank
  obtain ⟨wb, -, hsp⟩ := exists_append_basis (e := r) (r := d - r) (by omega) hc
  choose w hw using fun j => Ideal.toCotangent_surjective (maximalIdeal R) (wb j)
  refine ⟨d - r, fun j => (w j : R), ?_, ?_⟩
  · let v : Fin (r + (d - r)) → maximalIdeal R := Fin.append (fun i => ⟨y i, hy i⟩) w
    have hv : (maximalIdeal R).toCotangent ∘ v = Fin.append c wb := by
      funext i
      refine Fin.addCases (fun i => ?_) (fun j => ?_) i
      · simp [v, c]
      · simp [v, hw]
    have htop : Submodule.span R (Set.range v) = ⊤ := by
      rw [← CotangentSpace.span_image_eq_top_iff, ← Set.range_comp, hv, hsp]
    have h3 := congrArg (Submodule.map (maximalIdeal R).subtype) htop
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at h3
    convert h3 using 3
    funext i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · simp [v]
    · simp [v]
  · rw [hdim]
    norm_cast
    omega

/-- Local coordinates on `V` have differentials independent modulo the maximal ideal at every
point of `V`: on an affine open around the point they form a basis of the differentials, which
localizes to a basis of `Ω_{𝒪_{X,x}/k}`. -/
private theorem linearIndependent_tmul_D_germ_of_isLocalCoordinatesOn {k : Type v} [Field k]
    {X : Scheme.{v}} (sX : X ⟶ Spec (.of k)) {V : X.Opens} {n : ℕ} {z : Fin n → Γ(X, V)}
    (hz : MMP.Resolution.IsLocalCoordinatesOn sX V z) (x : X) (hx : x ∈ V) :
    letI := stalkAlgebra sX x
    LinearIndependent (ResidueField (X.presheaf.stalk x)) (fun i =>
      (1 : ResidueField (X.presheaf.stalk x)) ⊗ₜ[X.presheaf.stalk x]
        KaehlerDifferential.D k (X.presheaf.stalk x) ((X.presheaf.germ V x hx).hom (z i))) := by
  letI := stalkAlgebra sX x
  obtain ⟨_, ⟨W₁, hW₁, rfl⟩, hxW₁, hW₁V⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx V.isOpen
  letI := sectionAlgebra sX W₁
  letI : Algebra Γ(X, W₁) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxW₁⟩
  haveI : IsScalarTower k Γ(X, W₁) (X.presheaf.stalk x) :=
    isScalarTower_section_stalk sX W₁ ⟨x, hxW₁⟩
  haveI := (show IsAffineOpen W₁ from hW₁).isLocalization_stalk ⟨x, hxW₁⟩
  haveI : Algebra.FormallyEtale Γ(X, W₁) (X.presheaf.stalk x) :=
    Algebra.FormallyEtale.of_isLocalization
      ((show IsAffineOpen W₁ from hW₁).primeIdealOf ⟨x, hxW₁⟩).asIdeal.primeCompl
  obtain ⟨b, hb⟩ := hz ⟨W₁, hW₁⟩ hW₁V
  let bx := (KaehlerDifferential.isBaseChange_of_formallyEtale k Γ(X, W₁)
    (X.presheaf.stalk x)).basis b
  have hbx : ∀ i, bx i = KaehlerDifferential.D k (X.presheaf.stalk x)
      ((X.presheaf.germ V x hx).hom (z i)) := by
    intro i
    rw [IsBaseChange.basis_apply, hb, KaehlerDifferential.map_D]
    congr 1
    exact X.presheaf.germ_res_apply (homOfLE hW₁V) x hxW₁ (z i)
  have h := (bx.baseChange (ResidueField (X.presheaf.stalk x))).linearIndependent
  convert h using 1
  funext i
  rw [Module.Basis.baseChange_apply, hbx]

/-- **Simple normal crossing coordinates at every point.** On a scheme smooth over a field of
characteristic zero with regular local rings, the coordinates of an snc divisor at closed points
give coordinates at every point `x`: choose a closed point `x₀` specializing `x`; its regular
parameters are local coordinates near `x₀`, so the equations of the components through `x` have
differentials independent modulo `𝔪_x`, and extend to a regular system of parameters of
`𝒪_{X,x}`. -/
private theorem exists_snc_coordinates {k : Type v} [Field k] [CharZero k] {X : Scheme.{v}}
    (sX : X ⟶ Spec (.of k)) [Smooth sX] [CompactSpace X]
    (hreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)) {D : Divisor X}
    (hD : MMP.Flips.IsSNCDivisor sX D) (x : X) :
    ∃ (n : ℕ) (z : Fin n → X.presheaf.stalk x)
      (j : {E : Mori.PrimeDivisor X // E ∈ D.support ∧ x ∈ E.support} → Fin n),
      MMP.Mori.IsRegularSystemOfParameters z ∧ Function.Injective j ∧
        ∀ E, IdealSheafData.stalk E.1.idealSheaf x = Ideal.span {z (j E)} := by
  classical
  obtain ⟨x₀, hx₀, hcl⟩ := (isClosed_closure (s := ({x} : Set X))).exists_closed_singleton
    ⟨x, subset_closure rfl⟩
  have hsp : x ⤳ x₀ := specializes_iff_mem_closure.mpr hx₀
  obtain ⟨n, z, j, hz, hj, hI⟩ := hD.2.2 x₀ hcl
  obtain ⟨V, hx₀V, zV, hzV, hcoord⟩ :=
    MMP.Flips.ResolutionInputs.exists_isLocalCoordinatesAt_of_isRegularSystemOfParameters sX x₀
      hcl z hz
  have hxV : x ∈ V := hsp.mem_open V.isOpen hx₀V
  let y : Fin n → X.presheaf.stalk x := fun i => (X.presheaf.germ V x hxV).hom (zV i)
  have hy : ∀ i, (X.presheaf.stalkSpecializes hsp).hom (z i) = y i := by
    intro i
    rw [← hzV i, ← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
  let S := {E : Mori.PrimeDivisor X // E ∈ D.support ∧ x ∈ E.support}
  have hS0 : ∀ E : S, x₀ ∈ E.1.support := fun E => by
    have hc : IsClosed (E.1.support : Set X) := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isClosed_closure
    exact closure_minimal (Set.singleton_subset_iff.mpr E.2.2) hc hx₀
  let j0 : S → Fin n := fun E => j ⟨E.1, E.2.1, hS0 E⟩
  have hj0 : Function.Injective j0 := fun E E' h => by
    exact Subtype.ext (Subtype.mk.inj (hj h))
  have hIx : ∀ E : S, IdealSheafData.stalk E.1.idealSheaf x = Ideal.span {y (j0 E)} := by
    intro E
    rw [stalk_idealSheaf_eq_map_stalkSpecializes _ hsp, hI ⟨E.1, E.2.1, hS0 E⟩, Ideal.map_span,
      Set.image_singleton, hy]
  have hmem : ∀ E : S, y (j0 E) ∈ maximalIdeal (X.presheaf.stalk x) := by
    intro E
    have hne : IdealSheafData.stalk E.1.idealSheaf x ≠ ⊤ := fun h =>
      ((Stacks.Divisors.stalk_eq_top_iff_notMem_support _ x).mp h) E.2.2
    have := le_maximalIdeal hne
    rw [hIx E] at this
    exact this (Ideal.subset_span rfl)
  haveI : Finite S := Finite.of_injective
    (fun E : S => (⟨E.1, E.2.1⟩ : {E // E ∈ D.support}))
    fun E E' h => Subtype.ext (Subtype.mk.inj h)
  letI : Fintype S := Fintype.ofFinite S
  let e := Fintype.equivFin S
  let yS : Fin (Fintype.card S) → X.presheaf.stalk x := fun i => y (j0 (e.symm i))
  letI := stalkAlgebra sX x
  have hli : LinearIndependent (ResidueField (X.presheaf.stalk x)) (fun i =>
      (1 : ResidueField (X.presheaf.stalk x)) ⊗ₜ[X.presheaf.stalk x]
        KaehlerDifferential.D k (X.presheaf.stalk x) (yS i)) :=
    (linearIndependent_tmul_D_germ_of_isLocalCoordinatesOn sX hcoord.1 x hxV).comp
      (j0 ∘ e.symm) (hj0.comp e.symm.injective)
  haveI := hreg x
  obtain ⟨s, w, hw⟩ := exists_isRegularSystemOfParameters_append (k := k) yS
    (fun i => hmem _) hli
  refine ⟨Fintype.card S + s, Fin.append yS w, fun E => Fin.castAdd s (e E), hw,
    fun E E' h => e.injective (Fin.castAdd_injective _ _ h), fun E => ?_⟩
  rw [Fin.append_left, hIx E]
  simp [yS]

/-- A prime `P ≠ ⊥` contained in a prime of height one of a domain is that prime. -/
private theorem eq_of_le_of_height_eq_one {R : Type*} [CommRing R] [IsDomain R] {P q : Ideal R}
    [P.IsPrime] [q.IsPrime] (h : P ≤ q) (hq : q.height = 1) (hP : P ≠ ⊥) : P = q := by
  by_contra hne
  have h1 := Ideal.height_add_one_le_of_lt_of_isPrime (lt_of_le_of_ne h hne)
  have h2 := Ideal.height_add_one_le_of_lt_of_isPrime (I := (⊥ : Ideal R)) (J := P)
    (bot_lt_iff_ne_bot.mpr hP)
  rw [hq] at h1
  have h4 : (1 : ℕ∞) ≤ P.height := le_trans le_add_self h2
  have h3 : (1 : ℕ∞) + 1 ≤ 1 := le_trans (by gcongr) h1
  exact absurd h3 (by decide)

/-- **Equations of prime divisors along a flat unramified morphism.** Let `p : W' ⟶ W` be flat,
with `𝔪_{p z}` generating `𝔪_z` and `𝒪_{W',z}` regular. If the ideal of a prime divisor `E` of
`W` at `p z` is generated by a member `a i` of a regular system of parameters, then the ideal at
`z` of every prime divisor `E'` through `z` lying over `E` is generated by the image of `a i`. -/
private theorem stalk_idealSheaf_eq_span_stalkMap {W W' : Scheme.{v}} (p : W' ⟶ W) [Flat p]
    [IsLocallyNoetherian W] [IsLocallyNoetherian W'] {z : W'}
    (hreg : IsRegularLocalRing (W'.presheaf.stalk z))
    (hmax : (maximalIdeal (W.presheaf.stalk (p z))).map (p.stalkMap z).hom =
      maximalIdeal (W'.presheaf.stalk z))
    {E : Mori.PrimeDivisor W} {E' : Mori.PrimeDivisor W'}
    (hEE' : p E'.genericPoint = E.genericPoint)
    (hz : z ∈ E'.support) {n : ℕ} {a : Fin n → W.presheaf.stalk (p z)}
    (ha : MMP.Mori.IsRegularSystemOfParameters a) (i : Fin n)
    (hE : IdealSheafData.stalk E.idealSheaf (p z) = Ideal.span {a i}) :
    IdealSheafData.stalk E'.idealSheaf z = Ideal.span {(p.stalkMap z).hom (a i)} := by
  letI := (p.stalkMap z).hom.toAlgebra
  haveI : IsLocalHom (algebraMap (W.presheaf.stalk (p z)) (W'.presheaf.stalk z)) :=
    inferInstanceAs (IsLocalHom (p.stalkMap z).hom)
  haveI : Module.Flat (W.presheaf.stalk (p z)) (W'.presheaf.stalk z) := Flat.stalkMap p z
  have hsp : E'.genericPoint ⤳ z := by
    rwa [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  have hx : p z ∈ E.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← specializes_iff_mem_closure]
    have := hsp.map p.continuous
    rwa [hEE'] at this
  obtain ⟨q', hq', hqE', hht'⟩ := MMP.Intersection.exists_stalk_idealSheaf_eq_of_mem_support E' hz
  obtain ⟨q, hq, hqE, hht⟩ := MMP.Intersection.exists_stalk_idealSheaf_eq_of_mem_support E hx
  -- `q'` lies over `q`
  have hcomap : Ideal.comap (p.stalkMap z).hom q'.asIdeal = q.asIdeal := by
    let q'' : Spec (W'.presheaf.stalk z) := q'
    have h0 := Scheme.Hom.comp_apply (Spec.map (p.stalkMap z)) (W.fromSpecStalk (p z)) q''
    have h0' := Scheme.Hom.comp_apply (W'.fromSpecStalk z) p q''
    rw [Scheme.SpecMap_stalkMap_fromSpecStalk, h0'] at h0
    change p (W'.fromSpecStalk z q') = _ at h0
    rw [hq', hEE', ← hq] at h0
    exact congrArg PrimeSpectrum.asIdeal ((W.fromSpecStalk (p z)).isEmbedding.injective h0.symm)
  have hmem : (p.stalkMap z).hom (a i) ∈ q'.asIdeal := by
    have : a i ∈ q.asIdeal := by rw [← hqE, hE]; exact Ideal.subset_span rfl
    rwa [← hcomap] at this
  haveI := hreg
  haveI := IsRegularLocalRing.isDomain (W'.presheaf.stalk z)
  have hb : MMP.Mori.IsRegularSystemOfParameters
      (algebraMap (W.presheaf.stalk (p z)) (W'.presheaf.stalk z) ∘ a) :=
    IsRegularSystemOfParameters.map hmax ha
  haveI : (Ideal.span {(p.stalkMap z).hom (a i)}).IsPrime :=
    MMP.Resolution.isPrime_span_singleton_of_isRegularSystemOfParameters hb i
  have hne : Ideal.span {(p.stalkMap z).hom (a i)} ≠ ⊥ := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    intro h0
    haveI := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := W.presheaf.stalk (p z))
      (B := W'.presheaf.stalk z)
    have hai : a i = 0 := (FaithfulSMul.algebraMap_injective (W.presheaf.stalk (p z))
      (W'.presheaf.stalk z)) (h0.trans (map_zero _).symm)
    rw [← hqE, hE, hai, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.height_bot] at hht
    exact absurd hht (by decide)
  rw [hqE']
  exact (eq_of_le_of_height_eq_one ((Ideal.span_singleton_le_iff_mem _).mpr hmem) hht' hne).symm

/-- A point of a prime divisor `E'` maps into every prime divisor `E` with `p(η_{E'}) = η_E`. -/
private theorem map_mem_support_of_map_genericPoint_eq {W W' : Scheme.{v}} (p : W' ⟶ W)
    {E : Mori.PrimeDivisor W} {E' : Mori.PrimeDivisor W'}
    (hEE' : p E'.genericPoint = E.genericPoint)
    {z : W'} (hz : z ∈ E'.support) : p z ∈ E.support := by
  have hsp : E'.genericPoint ⤳ z := by
    rwa [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← specializes_iff_mem_closure]
  have := hsp.map p.continuous
  rwa [hEE'] at this

/-- **Simple normal crossing divisors pull back along flat unramified morphisms.** Let
`p : W' ⟶ W` be flat and formally unramified, with `W` smooth over a field `k` of characteristic
zero and `W'` regular, locally of finite type over a field `κ` of characteristic zero. If `G` is
snc on `W`, then a reduced divisor `G'` on `W'` all of whose components lie over components of
`G` is snc: at `z ∈ W'`, the images of the snc coordinates of `G` at `p z` are a regular system of
parameters of `𝒪_{W',z}` cutting out the components of `G'` through `z`. -/
private theorem isSNCDivisor_of_flat_of_formallyUnramified {k κ : Type v} [Field k] [CharZero k]
    [Field κ] [CharZero κ] {W W' : Scheme.{v}} (sW : W ⟶ Spec (.of k)) [Smooth sW]
    [CompactSpace W] (sW' : W' ⟶ Spec (.of κ)) [LocallyOfFiniteType sW'] (p : W' ⟶ W) [Flat p]
    [FormallyUnramified p] (hreg : ∀ w : W, IsRegularLocalRing (W.presheaf.stalk w))
    (hreg' : ∀ z : W', IsRegularLocalRing (W'.presheaf.stalk z)) {G : Divisor W}
    (hG : MMP.Flips.IsSNCDivisor sW G) {G' : Divisor W'}
    (hG'01 : ∀ Q : Mori.PrimeDivisor W', G'.coeff Q = 0 ∨ G'.coeff Q = 1)
    (hG' : ∀ Q : Mori.PrimeDivisor W', G'.coeff Q ≠ 0 →
      ∃ E ∈ G.support, p Q.genericPoint = E.genericPoint) :
    MMP.Flips.IsSNCDivisor sW' G' := by
  classical
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian sW
  haveI : IsLocallyNoetherian W' := LocallyOfFiniteType.isLocallyNoetherian sW'
  choose Eof hEof hEofg using hG'
  have hloc : ∀ z : W', ∃ (n : ℕ) (b : Fin n → W'.presheaf.stalk z)
      (j : {E' : Mori.PrimeDivisor W' // E' ∈ G'.support ∧ z ∈ E'.support} → Fin n),
      MMP.Mori.IsRegularSystemOfParameters b ∧ Function.Injective j ∧
        ∀ E', IdealSheafData.stalk E'.1.idealSheaf z = Ideal.span {b (j E')} := by
    intro z
    haveI : CharZero (ResidueField (W.presheaf.stalk (p z))) := by
      letI := stalkAlgebra sW (p z)
      exact charZero_of_injective_algebraMap (algebraMap k _).injective
    obtain ⟨n, a, j, ha, hj, hI⟩ := exists_snc_coordinates sW hreg hG (p z)
    have hmax := map_maximalIdeal_stalkMap_eq p z
    letI := (p.stalkMap z).hom.toAlgebra
    haveI : IsLocalHom (algebraMap (W.presheaf.stalk (p z)) (W'.presheaf.stalk z)) :=
      inferInstanceAs (IsLocalHom (p.stalkMap z).hom)
    haveI : Module.Flat (W.presheaf.stalk (p z)) (W'.presheaf.stalk z) := Flat.stalkMap p z
    have hne : ∀ E' : {E' : Mori.PrimeDivisor W' // E' ∈ G'.support ∧ z ∈ E'.support},
        G'.coeff E'.1 ≠ 0 := fun E' => Finsupp.mem_support_iff.mp E'.2.1
    let e : {E' : Mori.PrimeDivisor W' // E' ∈ G'.support ∧ z ∈ E'.support} →
        {E : Mori.PrimeDivisor W // E ∈ G.support ∧ p z ∈ E.support} := fun E' =>
      ⟨Eof E'.1 (hne E'), hEof _ _, map_mem_support_of_map_genericPoint_eq p (hEofg _ _) E'.2.2⟩
    have hst : ∀ E', IdealSheafData.stalk E'.1.idealSheaf z =
        Ideal.span {(p.stalkMap z).hom (a (j (e E')))} := fun E' =>
      stalk_idealSheaf_eq_span_stalkMap p (hreg' z) hmax (hEofg _ _) E'.2.2 ha _ (hI (e E'))
    refine ⟨n, fun i => (p.stalkMap z).hom (a i), fun E' => j (e E'),
      IsRegularSystemOfParameters.map hmax ha, fun E₁ E₂ h12 => ?_, hst⟩
    have h := (hst E₁).trans ((congrArg (fun i => Ideal.span {(p.stalkMap z).hom (a i)}) h12).trans
      (hst E₂).symm)
    exact Subtype.ext (MMP.Intersection.eq_of_stalk_idealSheaf_eq E₁.2.2 E₂.2.2 h)
  refine ⟨hG'01, fun E' hE' => ?_, fun z _ => hloc z⟩
  refine MMP.Resolution.isSmoothScheme_subscheme_of_stalk_eq_span_parameter sW' _ fun y hy => ?_
  obtain ⟨n, b, j, hb, -, hst⟩ := hloc y
  exact ⟨n, b, j ⟨E', hE', hy⟩, hb, hst ⟨E', hE', hy⟩⟩

end SNCTransport

section InverseTransform

private theorem topologicalKrullDim_closure_singleton_add_coheight {k : Type v} [Field k]
    {Y : Scheme.{v}} (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [LocallyOfFiniteType sY] (x : Y) :
    topologicalKrullDim (closure {x} : Set Y) + Order.coheight x = topologicalKrullDim Y := by
  let _ : Y.Over (Spec (.of k)) := ⟨sY⟩
  have : LocallyOfFiniteType (Y ↘ Spec (.of k)) := inferInstanceAs (LocallyOfFiniteType sY)
  have h := MMP.Intersection.Scheme.Subvariety.dim_add_codim k
    (MMP.Intersection.Scheme.Subvariety.ofPoint x)
  rw [MMP.Intersection.Scheme.Subvariety.dim_eq_topologicalKrullDim_support,
    MMP.Intersection.Scheme.Subvariety.support_ofPoint,
    MMP.Intersection.Scheme.Subvariety.codim_eq_coheight_genericPoint,
    MMP.Intersection.Scheme.Subvariety.genericPoint_ofPoint] at h
  exact h

private theorem withBot_add_two_le_iff {d : WithBot ℕ∞} {c : ℕ∞} {n : ℕ} (h : d + c = n) :
    d + 2 ≤ n ↔ 2 ≤ c := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h
  | coe d =>
    induction d using ENat.recTopCoe with
    | top =>
      exfalso
      have : ((⊤ : ℕ∞) : WithBot ℕ∞) + c = ((⊤ : ℕ∞) : WithBot ℕ∞) := by
        rw [← WithBot.coe_add, top_add]
      rw [this] at h
      exact ENat.top_ne_natCast n (WithBot.coe_injective h)
    | coe d =>
      induction c using ENat.recTopCoe with
      | top =>
        exfalso
        have : ((d : ℕ∞) : WithBot ℕ∞) + ((⊤ : ℕ∞) : WithBot ℕ∞) = ((⊤ : ℕ∞) : WithBot ℕ∞) := by
          rw [← WithBot.coe_add, add_top]
        rw [this] at h
        exact ENat.top_ne_natCast n (WithBot.coe_injective h)
      | coe c =>
        have h' : d + c = n := by exact_mod_cast h
        have e1 : (((d : ℕ∞) : WithBot ℕ∞) + 2 ≤ (n : WithBot ℕ∞)) ↔ d + 2 ≤ n := by
          rw [show ((d : ℕ∞) : WithBot ℕ∞) + 2 = (((d + 2 : ℕ) : ℕ∞) : WithBot ℕ∞) from rfl,
            show (n : WithBot ℕ∞) = ((n : ℕ∞) : WithBot ℕ∞) from rfl, WithBot.coe_le_coe,
            Nat.cast_le]
        rw [e1]
        constructor
        · intro h2; exact_mod_cast (show 2 ≤ c by omega)
        · intro h2; have : 2 ≤ c := by exact_mod_cast h2
          omega

private theorem isExceptional_iff_two_le_coheight {k : Type v} [Field k] {X : Scheme.{v}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [LocallyOfFiniteType sX] {n : ℕ}
    (hn : topologicalKrullDim X = n) (D : ProperDivisorOver k sX) :
    D.IsExceptional ↔ 2 ≤ Order.coheight (D.f D.E.genericPoint) := by
  unfold ProperDivisorOver.IsExceptional
  rw [D.center_eq_toDivisorOver_center, D.toDivisorOver.center_eq_closure_genericPoint, hn]
  have h := topologicalKrullDim_closure_singleton_add_coheight sX (D.f D.E.genericPoint)
  rw [hn] at h
  exact withBot_add_two_le_iff h

variable {X Y : Scheme.{v}}

private theorem source_ι_comp_eq_of_toRationalMap_eq {X Y : Scheme.{v}} [IsReduced Y]
    [IsSeparated (X ↘ ⊤_ Scheme)] (f : Y ⟶ X) (e : Y.PartialIso X)
    (he : e.toRationalMap = f.toRationalMap) : e.source.ι ≫ f = e.iso.hom ≫ e.target.ι :=
  ((Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
    (Scheme.PartialMap.toRationalMap_eq_iff.mp he)).symm

/-- If `e` is a partial isomorphism representing a morphism `f : Y ⟶ X` and `g'` a partial map
representing `e⁻¹`, then `f ∘ g'` is the identity where `g'` is defined. -/
private theorem apply_hom_eq_of_isInverse {X Y : Scheme.{v}} [IsReduced Y] [IsReduced X]
    [IsSeparated (X ↘ ⊤_ Scheme)] (f : Y ⟶ X) (e : Y.PartialIso X)
    (he : e.toRationalMap = f.toRationalMap) (g' : X.PartialMap Y)
    (hg' : g'.toRationalMap = e.symm.toRationalMap) {x : X} (hx : x ∈ g'.domain) :
    f (g'.hom ⟨x, hx⟩) = x := by
  have h1 : (g'.compHom f).toRationalMap = (Scheme.PartialMap.id X).toRationalMap := by
    rw [Scheme.RationalMap.compHom_toRationalMap, hg', ← Scheme.RationalMap.compHom_toRationalMap,
      Scheme.PartialMap.toRationalMap_eq_iff,
      Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)]
    change e.iso.inv ≫ e.source.ι ≫ f = e.target.ι ≫ 𝟙 X
    rw [source_ι_comp_eq_of_toRationalMap_eq f e he, Iso.inv_hom_id_assoc, Category.comp_id]
  have h2 := MMP.Positivity.PartialMap.hom_apply_eq_of_toRationalMap_eq
    (g := g'.compHom f) (g' := Scheme.PartialMap.id X) h1 hx trivial
  change (g'.hom ≫ f) ⟨x, hx⟩ = (X.topIso.hom ≫ 𝟙 X) ⟨x, trivial⟩ at h2
  refine (Scheme.Hom.comp_apply _ _ _).symm.trans (h2.trans ?_)
  rw [Category.comp_id, Scheme.topIso_hom]
  rfl

private theorem coe_transform_eq_closure_singleton {X Y : Scheme.{v}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} (g' : X.PartialMap Y)
    (hg' : g'.toRationalMap = φ) (P : Mori.PrimeDivisor X) (hP : P.genericPoint ∈ g'.domain) :
    (Mori.RationalMap.transform φ P.idealSheaf.support : Set Y) =
      closure {g'.hom ⟨P.genericPoint, hP⟩} := by
  have hZ : closure ((P.idealSheaf.support : Set X) ∩ g'.domain) = P.idealSheaf.support := by
    refine le_antisymm ?_ ?_
    · exact closure_minimal Set.inter_subset_left P.idealSheaf.support.isClosed
    · change P.support ⊆ _
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      refine closure_mono (Set.singleton_subset_iff.mpr ⟨?_, hP⟩)
      change P.genericPoint ∈ P.support
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
  rw [← MMP.Positivity.closure_image_eq_transform g' hg' _ hZ, TopologicalSpace.Closeds.coe_closure]
  refine le_antisymm (closure_minimal ?_ isClosed_closure) (closure_mono ?_)
  · rintro _ ⟨q, hq, rfl⟩
    have hq' : P.genericPoint ⤳ g'.domain.ι q := by
      have : g'.domain.ι q ∈ P.support := hq
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at this
      exact specializes_iff_mem_closure.mpr this
    have h1 := (g'.domain.ι.isOpenEmbedding.isInducing.specializes_iff (y := q)
      (x := ⟨P.genericPoint, hP⟩)).mp (by rwa [Scheme.Opens.ι_apply])
    exact specializes_iff_mem_closure.mp (h1.map g'.hom.continuous)
  · rw [Set.singleton_subset_iff]
    refine ⟨⟨P.genericPoint, hP⟩, ?_, rfl⟩
    change g'.domain.ι ⟨P.genericPoint, hP⟩ ∈ P.support
    rw [Scheme.Opens.ι_apply, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl

/-- If the strict transform of `P` under `φ` is `E` and `g'` represents `φ` at `η_P`, then
`η_E = g'(η_P)`. -/
private theorem genericPoint_eq_of_transformPrimeDivisor_eq_some {X Y : Scheme.{v}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} {P : Mori.PrimeDivisor X}
    {E : Mori.PrimeDivisor Y} (h : Mori.RationalMap.transformPrimeDivisor φ P = some E)
    (g' : X.PartialMap Y) (hg' : g'.toRationalMap = φ) (hP : P.genericPoint ∈ g'.domain) :
    E.genericPoint = g'.hom ⟨P.genericPoint, hP⟩ := by
  have h1 := Mori.RationalMap.support_transformPrimeDivisor h
  rw [coe_transform_eq_closure_singleton g' hg' P hP,
    AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h1
  exact (inseparable_iff_closure_eq.2 h1).eq

/-- If `g'` represents `φ` at `η_P` and `g'(η_P) = η_E`, then the strict transform of `P` under
`φ` is `E`. -/
private theorem transformPrimeDivisor_eq_some_of_genericPoint_eq {X Y : Scheme.{v}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} {P : Mori.PrimeDivisor X}
    {E : Mori.PrimeDivisor Y} (g' : X.PartialMap Y) (hg' : g'.toRationalMap = φ)
    (hP : P.genericPoint ∈ g'.domain) (hE : E.genericPoint = g'.hom ⟨P.genericPoint, hP⟩) :
    Mori.RationalMap.transformPrimeDivisor φ P = some E := by
  refine Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mpr
    ⟨Mori.RationalMap.definedAt_iff.mpr ⟨g', hP, hg'⟩, ?_⟩
  have h1 : Mori.RationalMap.transform φ P.idealSheaf.support = E.idealSheaf.support := by
    apply SetLike.coe_injective
    rw [coe_transform_eq_closure_singleton g' hg' P hP, ← hE]
    exact (AlgebraicGeometry.PrimeDivisor.support_eq_closure E).symm
  have := E.integral
  rw [Mori.RationalMap.transformIdeal, h1, MMP.Positivity.vanishingIdeal_support_of_isReduced]

/-- The coefficient of `P` in the linear extension of a partial map `φ` on prime divisors is `0`
when no prime divisor is sent to `P`. -/
private theorem mapPrimeDivisors_apply_eq_zero_of_forall_ne {X Y : Scheme.{v}} {R : Type*}
    [AddCommMonoid R] {φ : Mori.PrimeDivisor X → Option (Mori.PrimeDivisor Y)}
    {P : Mori.PrimeDivisor Y} (h : ∀ E, φ E ≠ some P) (D : DivisorWithCoeffs R X) :
    DivisorWithCoeffs.mapPrimeDivisors φ D P = 0 := by
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D D' hD hD' => rw [map_add, Finsupp.add_apply, hD, hD', add_zero]
  | single E r =>
    rw [DivisorWithCoeffs.mapPrimeDivisors_single]
    rcases hE : φ E with _ | E'
    · rfl
    · have hne : E' ≠ P := fun he => h E (by rw [hE, he])
      exact Finsupp.single_eq_of_ne' hne

/-- If the strict transform of a prime divisor `P` of `X` under the inverse of a birational
morphism `f : Y ⟶ X` is `E`, then `f` sends the generic point of `E` to that of `P`. -/
private theorem genericPoint_eq_of_transformPrimeDivisor_inverse_eq_some [IsReduced X] [IsReduced Y]
    [IsSeparated (X ↘ ⊤_ Scheme)] [IsSeparated (Y ↘ ⊤_ Scheme)] {f : Y ⟶ X}
    (hf : IsBirationalMorphism f) {P : Mori.PrimeDivisor X} {E : Mori.PrimeDivisor Y}
    (h : Mori.RationalMap.transformPrimeDivisor (Mori.RationalMap.IsBirational.inverse hf) P =
      some E) :
    f E.genericPoint = P.genericPoint := by
  obtain ⟨e, he, he'⟩ := hf.isInverse_inverse
  obtain ⟨g', hP, hg'⟩ :=
    Mori.RationalMap.definedAt_iff.mp (Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mp h).1
  rw [genericPoint_eq_of_transformPrimeDivisor_eq_some h g' hg' hP]
  exact apply_hom_eq_of_isInverse f e he g' (hg'.trans he'.symm) hP

private theorem isSeparated_terminal_from {k : Type v} [Field k] (sX : X ⟶ Spec (.of k))
    [IsSeparated sX] : IsSeparated (X ↘ ⊤_ Scheme) := by
  rw [show (X ↘ ⊤_ Scheme) = sX ≫ (Spec (.of k) ↘ ⊤_ Scheme) from Limits.terminal.hom_ext _ _]
  infer_instance

/-- Conversely, let `f : Y ⟶ X` be a proper birational morphism of varieties with `X` normal. If
`f` sends the generic point of a prime divisor `E` of `Y` to that of a prime divisor `P` of `X`,
then the strict transform of `P` under `f⁻¹` is `E`: the map `f⁻¹` is defined at `η_P`
(`MMP.Flips.RationalMap.isMorphismInCodimOne_inverse`), and `f` is injective on the points over
`η_P`, whose local ring is a valuation ring. -/
private theorem transformPrimeDivisor_inverse_eq_some_of_genericPoint_eq {k : Type v} [Field k]
    {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) (f : Y ⟶ X)
    (hY : Mori.IsVariety k (f ≫ sX)) [IsProper f] (hf : IsBirationalMorphism f)
    {P : Mori.PrimeDivisor X} {E : Mori.PrimeDivisor Y} (h : f E.genericPoint = P.genericPoint) :
    Mori.RationalMap.transformPrimeDivisor (Mori.RationalMap.IsBirational.inverse hf) P =
      some E := by
  have : IsIntegral X := hX.1.toIsIntegral
  have : IsIntegral Y := hY.toIsIntegral
  have : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated (f ≫ sX) := hY.toIsSeparated
  have := isSeparated_terminal_from sX
  have := isSeparated_terminal_from (f ≫ sX)
  have : IsNormal X := hX.2
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsDominant f := hf.isDominant
  have hbij := hf.functionFieldMap_bijective
  obtain ⟨e, he, he'⟩ := hf.isInverse_inverse
  have hdef : Mori.RationalMap.DefinedAt (Mori.RationalMap.IsBirational.inverse hf)
      P.genericPoint := by
    by_contra hnd
    have h2 := le_closedsCodimension_iff.mp (RationalMap.isMorphismInCodimOne_inverse hX f hY hf)
      (TopologicalSpace.IrreducibleCloseds.closureSingleton P.genericPoint)
      (closure_minimal (Set.singleton_subset_iff.mpr hnd)
        (Mori.RationalMap.dom (Mori.RationalMap.IsBirational.inverse hf)).compl.isClosed)
    rw [codimension_eq_coheight,
      show TopologicalSpace.IrreducibleCloseds.closureSingleton P.genericPoint =
      (irreducibleSetEquivPoints (α := X)).symm P.genericPoint from rfl,
      Order.coheight_orderIso, P.coheight_genericPoint] at h2
    exact absurd h2 (by decide)
  obtain ⟨g', hP, hg'⟩ := Mori.RationalMap.definedAt_iff.mp hdef
  refine transformPrimeDivisor_eq_some_of_genericPoint_eq g' hg' hP ?_
  have hy := apply_hom_eq_of_isInverse f e he g' (hg'.trans he'.symm) hP
  have := P.isDiscreteValuationRing_localRing
  have : ValuationRing (X.presheaf.stalk (f E.genericPoint)) := by rw [h]; infer_instance
  have : ValuationRing (X.presheaf.stalk (f (g'.hom ⟨P.genericPoint, hP⟩))) := by
    rw [hy]; infer_instance
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing f hbij E.genericPoint
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing f hbij (g'.hom ⟨P.genericPoint, hP⟩)
  exact MMP.Positivity.eq_of_isIso_stalkMap f hbij (hy.trans h.symm)

/-- For a proper birational morphism `f : Y ⟶ X` of varieties with `X` normal, the coefficient of
`f⁻¹_* D` along a prime divisor `E` of `Y` with `f(η_E) = η_P` is the coefficient of `D`
along `P`. -/
private theorem birationalInverseTransform_apply_of_genericPoint_eq {k : Type v} [Field k]
    {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) (f : Y ⟶ X)
    (hY : Mori.IsVariety k (f ≫ sX)) [IsProper f] (hf : IsBirationalMorphism f) {R : Type*}
    [AddCommMonoid R] (D : DivisorWithCoeffs R X) {P : Mori.PrimeDivisor X}
    {E : Mori.PrimeDivisor Y} (h : f E.genericPoint = P.genericPoint) :
    birationalInverseTransform f hf D E = D P := by
  have : IsIntegral X := hX.1.toIsIntegral
  have : IsIntegral Y := hY.toIsIntegral
  have : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated (f ≫ sX) := hY.toIsSeparated
  have := isSeparated_terminal_from sX
  have := isSeparated_terminal_from (f ≫ sX)
  exact MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
    (transformPrimeDivisor_inverse_eq_some_of_genericPoint_eq hX f hY hf h)
    (fun P' hP' => AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      ((genericPoint_eq_of_transformPrimeDivisor_inverse_eq_some hf hP').symm.trans h)) D

/-- `X ⟶ ⊤_ Scheme` is separated for a variety `X`. -/
private theorem isSeparated_terminal_of_isVariety {k : Type v} [Field k] {X : Scheme.{v}}
    {sX : X ⟶ Spec (.of k)} (hX : MMP.Mori.IsVariety k sX) : IsSeparated (X ↘ ⊤_ Scheme) :=
  have : IsSeparated sX := hX.toIsSeparated
  isSeparated_terminal_from sX

/-- The coefficient of `μ⁻¹_* D` along a prime divisor `E` lying over no prime divisor of `X`
vanishes. -/
private theorem coeff_birationalInverseTransform_eq_zero {k : Type v} [Field k]
    {X Y : Scheme.{v}} {sX : X ⟶ Spec (.of k)} {R : Type*} [AddCommMonoid R]
    (hX : MMP.Mori.IsVariety k sX) {μ : Y ⟶ X} (hY : MMP.Mori.IsVariety k (μ ≫ sX))
    (hμ : IsBirationalMorphism μ) (D : DivisorWithCoeffs R X) {E : MMP.Mori.PrimeDivisor Y}
    (h : ∀ P : MMP.Mori.PrimeDivisor X, μ E.genericPoint ≠ P.genericPoint) :
    MMP.Flips.birationalInverseTransform μ hμ D E = 0 := by
  have : IsIntegral X := hX.toIsIntegral
  have : IsIntegral Y := hY.toIsIntegral
  have := isSeparated_terminal_of_isVariety hX
  have := isSeparated_terminal_of_isVariety hY
  exact mapPrimeDivisors_apply_eq_zero_of_forall_ne (fun P hP =>
    h P (genericPoint_eq_of_transformPrimeDivisor_inverse_eq_some hμ hP)) D

/-- For a proper birational morphism `f : Y ⟶ X` of normal varieties of dimension `n`, a prime
divisor `E` of `Y` lies in `Supp(f⁻¹_* D) ∪ Exc(f)` exactly when `f(η_E)` is the generic point of
a prime divisor of `X` along which `D` is nonzero, or has codimension at least two. -/
private theorem birationalInverseTransform_ne_zero_or_isExceptional_iff {k : Type v} [Field k]
    {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) {n : ℕ} (hn : topologicalKrullDim X = n)
    (f : Y ⟶ X) (hY : IsNormalVariety k (f ≫ sX)) [IsProper f] (hf : IsBirationalMorphism f)
    {R : Type*} [AddCommMonoid R] (D : DivisorWithCoeffs R X) (E : Mori.PrimeDivisor Y) :
    (birationalInverseTransform f hf D E ≠ 0 ∨ IsExceptionalPrimeDivisor sX f E) ↔
      ((∃ P : Mori.PrimeDivisor X, f E.genericPoint = P.genericPoint ∧ D P ≠ 0) ∨
        2 ≤ Order.coheight (f E.genericPoint)) := by
  have : IsIntegral X := hX.1.toIsIntegral
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hexc : IsExceptionalPrimeDivisor sX f E ↔ 2 ≤ Order.coheight (f E.genericPoint) :=
    ⟨fun ⟨_, _, _, h⟩ => (isExceptional_iff_two_le_coheight hn
        (ProperDivisorOver.mk ⟨Y, f, hY, hf, E⟩ inferInstance)).mp h,
      fun h => ⟨hY, hf, inferInstance, (isExceptional_iff_two_le_coheight hn
        (ProperDivisorOver.mk ⟨Y, f, hY, hf, E⟩ inferInstance)).mpr h⟩⟩
  rw [hexc]
  refine or_congr_left ⟨fun h => ?_, fun ⟨P, hP, hD⟩ => ?_⟩
  · by_contra hne
    push Not at hne
    by_cases hP : ∃ P : Mori.PrimeDivisor X, f E.genericPoint = P.genericPoint
    · obtain ⟨P, hP⟩ := hP
      rw [birationalInverseTransform_apply_of_genericPoint_eq hX f hY.1 hf D hP] at h
      exact h (hne P hP)
    · push Not at hP
      exact h (coeff_birationalInverseTransform_eq_zero hX.1 hY.1 hf D hP)
  · rwa [birationalInverseTransform_apply_of_genericPoint_eq hX f hY.1 hf D hP]

end InverseTransform

section DivisorPullback

variable {W W' : Scheme.{v}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [IsIntegral W']
  [IsLocallyNoetherian W'] [IsNormal W'] (p : W' ⟶ W) [Flat p] [FormallyUnramified p]

/-- Along a flat, formally unramified morphism with residue fields of characteristic zero, the
generic point of a prime divisor maps to the generic point of a prime divisor. -/
private theorem exists_map_genericPoint_eq
    (hchar : ∀ w : W, CharZero (ResidueField (W.presheaf.stalk w))) (Q : Mori.PrimeDivisor W') :
    ∃ E : Mori.PrimeDivisor W, p Q.genericPoint = E.genericPoint := by
  haveI := hchar (p Q.genericPoint)
  have hcoh := (coheight_map_eq p Q.genericPoint).trans Q.coheight_genericPoint
  exact ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcoh,
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hcoh).symm⟩

/-- **Pull-back of a Cartier divisor along a flat unramified morphism.** Along a flat, formally
unramified morphism `p : W' ⟶ W` of normal integral schemes with residue fields of characteristic
zero, a Cartier divisor `G` pulls back to a divisor `G'` with `coeff_{Q} G' = coeff_E G` whenever
`p(η_Q) = η_E`. -/
private theorem exists_divisor_coeff_eq_of_flat [CompactSpace W']
    (hchar : ∀ w : W, CharZero (ResidueField (W.presheaf.stalk w))) {G : Divisor W}
    (hG : G.IsCartier) : ∃ G' : Divisor W', ∀ (Q : Mori.PrimeDivisor W') (E : Mori.PrimeDivisor W),
      p Q.genericPoint = E.genericPoint → G'.coeff Q = G.coeff E := by
  haveI : IsDominant p := isDominant_of_flat p
  obtain ⟨G', hG'⟩ := MMP.Threefold.Bridges.exists_isPullback_of_isDominant p hG
  refine ⟨G', fun Q E hQE => ?_⟩
  haveI := hchar (p Q.genericPoint)
  have hcoh := (coheight_map_eq p Q.genericPoint).trans Q.coheight_genericPoint
  obtain ⟨V, hV, φ, hφ⟩ := hG E.genericPoint
  rw [MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF hG' hφ Q (by rwa [hQE])
      E.component, ord_functionFieldMap_eq p Q.coheight_genericPoint hcoh
      (map_maximalIdeal_stalkMap_eq p Q.genericPoint), hQE,
    ← MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord, hφ E ((E.genericPoint_mem_iff V).mp hV)]

end DivisorPullback

section DiscrepancyTransport

/-- **Transport of discrepancies along a flat unramified morphism.** Let `jU : U' ⟶ U` be a flat,
formally unramified, dominant morphism from a normal variety over `κ` to a normal variety over
`k`, compatible with `k → κ`, and let `t₁, …, t_e ∈ k(U)` pull back to algebraically independent
constants of `κ`, with `dim U = e + 2` and `dim U' = 2`. For a divisor `E` over `U` on a model
`f : W ⟶ U` and a prime divisor `E'` of `W ×_U U'` over `E`, every discrepancy of `E` with
respect to `B` is a discrepancy of `E'` with respect to the flat pull-back `B'`, for any canonical
divisor of `U'`: the top form `dt₁ ∧ ⋯ ∧ dt_e ∧ α` corresponds to `α` on `U'` and on
`W ×_U U'`, with the same orders along corresponding prime divisors. -/
private theorem isDiscrepancy_transport {k κ : Type v} [Field k] [CharZero k] [Field κ]
    [Algebra k κ] {U U' : Scheme.{v}} (sU : U ⟶ Spec (.of k)) (sU' : U' ⟶ Spec (.of κ))
    (jU : U' ⟶ U) [IsIntegral U] [IsLocallyNoetherian U] [IsNormal U] [CompactSpace U]
    [LocallyOfFiniteType sU] [IsIntegral U'] [IsLocallyNoetherian U'] [IsNormal U']
    [CompactSpace U'] [LocallyOfFiniteType sU'] [Flat jU] [FormallyUnramified jU] [IsDominant jU]
    (hjU : jU ≫ sU = sU' ≫ Spec.map (CommRingCat.ofHom (algebraMap k κ)))
    {e : ℕ} (t : Fin e → U.functionField) (c : Fin e → κ) (hc : AlgebraicIndependent k c)
    (htc : ∀ i, functionFieldMap jU (t i) =
      (letI := functionFieldAlgebra sU'; algebraMap κ U'.functionField (c i)))
    (hdimU : topologicalKrullDim U = (e + 2 : ℕ)) (hU'n : IsNormalVariety κ sU')
    {W : Scheme.{v}} (f : W ⟶ U) (E : Mori.PrimeDivisor W)
    (E' : Mori.PrimeDivisor (pullback f jU))
    (hEE' : (pullback.fst f jU).base E'.genericPoint = E.genericPoint)
    (hW : IsNormalVariety k (f ≫ sU)) (hf : IsBirationalMorphism f) (hfp : IsProper f)
    (hW' : IsNormalVariety κ (pullback.snd f jU ≫ sU'))
    (hf' : IsBirationalMorphism (pullback.snd f jU)) (hfp' : IsProper (pullback.snd f jU))
    (n : ℕ) (K : Divisor U) (K' : Divisor U') (B : RDivisor U) (B' : RDivisor U')
    (hB' : ∀ (Q : Mori.PrimeDivisor U') (Γ : Mori.PrimeDivisor U),
      jU.base Q.genericPoint = Γ.genericPoint → B'.coeff Q = B.coeff Γ)
    (hK' : K'.IsCanonicalDivisor sU' 2) (a : ℝ)
    (ha : IsDiscrepancy sU n K B (ProperDivisorOver.mk ⟨W, f, hW, hf, E⟩ hfp).valuation a) :
    IsDiscrepancy sU' 2 K' B' (ProperDivisorOver.mk ⟨_, _, hW', hf', E'⟩ hfp').valuation a := by
  classical
  obtain ⟨hK, hKB, -, E₀, ω, m, r, L, hE₀, hωK, hX, hn, hω0, hLc, hsum, L₀, hpb₀, ha₀⟩ := ha
  have hne : n = e + 2 := by
    have := hn.symm.trans hdimU
    exact_mod_cast this
  subst hne
  -- the schemes and their structure
  set p := pullback.fst f jU with hp
  set f' := pullback.snd f jU with hf'def
  haveI : IsIntegral W := hW.1.toIsIntegral
  haveI : IsNormal W := hW.2
  haveI : LocallyOfFiniteType (f ≫ sU) := hW.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sU)
  haveI : IsIntegral (pullback f jU) := hW'.1.toIsIntegral
  haveI : IsNormal (pullback f jU) := hW'.2
  haveI : LocallyOfFiniteType (f' ≫ sU') := hW'.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian (pullback f jU) := LocallyOfFiniteType.isLocallyNoetherian (f' ≫ sU')
  haveI : IsDominant f := hf.isDominant
  haveI : IsDominant f' := hf'.isDominant
  haveI : Flat p := MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Flat)
    (IsPullback.of_hasPullback f jU).flip inferInstance
  haveI : FormallyUnramified p :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @FormallyUnramified)
      (IsPullback.of_hasPullback f jU).flip inferInstance
  haveI : IsDominant p := isDominant_of_flat p
  have hpf : p ≫ f = f' ≫ jU := pullback.condition
  have hpcompat : p ≫ (f ≫ sU) = (f' ≫ sU') ≫ Spec.map (CommRingCat.ofHom (algebraMap k κ)) := by
    rw [← Category.assoc, hpf, Category.assoc, hjU, Category.assoc]
  -- the function fields of `U` and `U'`
  letI := functionFieldAlgebra sU
  letI := functionFieldAlgebra sU'
  letI : Algebra U.functionField U'.functionField := functionFieldMapAlgebra jU
  letI : Algebra k U'.functionField :=
    ((algebraMap κ U'.functionField).comp (algebraMap k κ)).toAlgebra
  haveI : IsScalarTower k κ U'.functionField := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower k U.functionField U'.functionField :=
    IsScalarTower.of_algebraMap_eq fun c => (functionFieldMap_algebraMap_eq sU sU' jU hjU c).symm
  haveI : CharZero κ := charZero_of_injective_algebraMap (algebraMap k κ).injective
  have hdU : (Algebra.trdeg k U.functionField).toNat = e + 2 :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq hdimU
  have hdU' : (Algebra.trdeg κ U'.functionField).toNat = 2 :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq hK'.1
  haveI := essFiniteType_functionField (sX := sU)
  haveI := essFiniteType_functionField (sX := sU')
  haveI hfinU : FiniteDimensional U.functionField Ω[U.functionField⁄k] :=
    (trdeg_eq_finrank_kaehlerDifferential_sub_finrank_h1Cotangent k U.functionField).1
  haveI hfinU' : FiniteDimensional U'.functionField Ω[U'.functionField⁄κ] :=
    (trdeg_eq_finrank_kaehlerDifferential_sub_finrank_h1Cotangent κ U'.functionField).1
  have hrkU : Module.finrank U.functionField Ω[U.functionField⁄k] = e + 2 :=
    (finrank_kaehlerDifferential_eq_trdeg k _).trans hdU
  have hrkU' : Module.finrank U'.functionField Ω[U'.functionField⁄κ] = 2 :=
    (finrank_kaehlerDifferential_eq_trdeg κ _).trans hdU'
  -- the functions `tᵢ` are algebraically independent
  have ht : AlgebraicIndependent k t := by
    have h1 : AlgebraicIndependent k (fun i => algebraMap κ U'.functionField (c i)) :=
      hc.map' (f := IsScalarTower.toAlgHom k κ U'.functionField) (algebraMap κ _).injective
    refine AlgebraicIndependent.of_comp
      (IsScalarTower.toAlgHom k U.functionField U'.functionField) ?_
    convert h1 using 1
    funext i
    exact htc i
  -- the adapted basis `dt₁, …, dt_e, w₁, w₂` of `Ω_{k(U)/k}`
  obtain ⟨w, hwli, hwsp⟩ :=
    exists_append_basis hrkU (linearIndependent_D_of_algebraicIndependent ht)
  let bU : Module.Basis (Fin (e + 2)) U.functionField Ω[U.functionField⁄k] :=
    Module.Basis.mk hwli hwsp.ge
  have hbU : ∀ i, bU (Fin.castAdd 2 i) = KaehlerDifferential.D k _ (t i) := fun i => by
    simp [bU]
  let ℓU : Module.Basis Unit U.functionField (⋀[U.functionField]^(e + 2) Ω[U.functionField⁄k]) :=
    basisOfSpanSingleton (span_ιMulti_basis_eq_top bU) (ιMulti_basis_ne_zero bU)
  have hℓU : ℓU () = exteriorPower.ιMulti _ (e + 2) bU := by simp [ℓU]
  -- the contracted form `π(w₁) ∧ π(w₂)` on `U'`
  have hslclU := ordAt_wedge_eq_of_scheme sU sU' jU hjU t c hc htc (genericPoint U')
    (genericPoint U) (map_genericPoint_of_isDominant jU)
    ⟨inferInstance, hfinU, hrkU⟩ ⟨inferInstance, hfinU', hrkU'⟩
  have hβ' := (hslclU bU hbU).1
  have hrk1 :
      Module.finrank U'.functionField (⋀[U'.functionField]^2 Ω[U'.functionField⁄κ]) = 1 := by
    rw [exteriorPower.finrank_eq, hrkU']
    rfl
  let ℓU' : Module.Basis Unit U'.functionField (⋀[U'.functionField]^2 Ω[U'.functionField⁄κ]) :=
    basisOfSpanSingleton ((finrank_eq_one_iff_of_nonzero _ hβ').mp hrk1) hβ'
  have hℓU' : ℓU' () = exteriorPower.ιMulti _ 2 (fun j =>
      KaehlerDifferential.map k κ U.functionField U'.functionField (bU (Fin.natAdd e j))) := by
    simp [ℓU']
  -- prime divisors of `U'` lie over prime divisors of `U`
  have hcharU : ∀ x : U, CharZero (ResidueField (U.presheaf.stalk x)) := fun x => by
    letI := stalkAlgebra sU x
    exact charZero_of_injective_algebraMap
      (algebraMap k (ResidueField (U.presheaf.stalk x))).injective
  have hcoh : ∀ Q : Mori.PrimeDivisor U', Order.coheight (jU.base Q.genericPoint) = 1 := fun Q => by
    haveI := hcharU (jU.base Q.genericPoint)
    exact (coheight_map_eq jU Q.genericPoint).trans Q.coheight_genericPoint
  -- the orders of the adapted top forms agree along corresponding prime divisors
  let τU : RationalPluriForms sU (e + 2) 1 := ZTensorPower.basis ℓU 1 ()
  let τU' : RationalPluriForms sU' 2 1 := ZTensorPower.basis ℓU' 1 ()
  have hordU : ∀ (Q : Mori.PrimeDivisor U') (Γ : Mori.PrimeDivisor U),
      jU.base Q.genericPoint = Γ.genericPoint → Q.ordForm τU' = Γ.ordForm τU := by
    intro Q Γ hQΓ
    have hfreeΓ := Γ.free_kaehlerDifferential_localRing (sX := sU)
    have hfreeQ := Q.free_kaehlerDifferential_localRing (sX := sU')
    have h := ordAt_wedge_eq_of_scheme sU sU' jU hjU t c hc htc Q.genericPoint Γ.genericPoint hQΓ
      ⟨hfreeΓ.1, hfreeΓ.2, Γ.finrank_kaehlerDifferential_localRing.trans hdU⟩
      ⟨hfreeQ.1, hfreeQ.2, Q.finrank_kaehlerDifferential_localRing.trans hdU'⟩ bU hbU
    exact h.2 Q.coheight_genericPoint ℓU hℓU ℓU' hℓU'
  have hmaxU : ∀ Q : Mori.PrimeDivisor U',
      (maximalIdeal (U.presheaf.stalk (jU.base Q.genericPoint))).map
        (jU.stalkMap Q.genericPoint).hom = maximalIdeal (U'.presheaf.stalk Q.genericPoint) :=
    fun Q => by
      haveI := hcharU (jU.base Q.genericPoint)
      exact map_maximalIdeal_stalkMap_eq jU Q.genericPoint
  -- the forms `ω`, `ω''` and `ω'`
  have hτU0 : τU ≠ 0 := (ZTensorPower.basis ℓU 1).ne_zero ()
  have hτU'0 : τU' ≠ 0 := (ZTensorPower.basis ℓU' 1).ne_zero ()
  set cω := (ZTensorPower.basis ℓU 1).repr ω () with hcω
  have hωc : ω = cω • τU := (basis_unit_repr_smul (ZTensorPower.basis ℓU 1) ω).symm
  have hcω0 : cω ≠ 0 := repr_ne_zero_of_ne_zero ℓU hω0
  obtain ⟨ω', hω'0, hω'K⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hU'n hK'
  set cω' := (ZTensorPower.basis ℓU' 1).repr ω' () with hcω'
  have hω'c : ω' = cω' • τU' := (basis_unit_repr_smul (ZTensorPower.basis ℓU' 1) ω').symm
  have hcω'0 : cω' ≠ 0 := repr_ne_zero_of_ne_zero ℓU' hω'0
  have hjcω0 : functionFieldMap jU cω ≠ 0 := (map_ne_zero _).mpr hcω0
  set h := cω' / functionFieldMap jU cω with hh
  have hh0 : h ≠ 0 := div_ne_zero hcω'0 hjcω0
  have hω'h : ω' = (h * functionFieldMap jU cω) • τU' := by
    rwa [hh, div_mul_cancel₀ _ hjcω0]
  -- orders of `ω'` along the prime divisors of `U'`
  have hordω' : ∀ (Q : Mori.PrimeDivisor U') (Γ : Mori.PrimeDivisor U),
      jU.base Q.genericPoint = Γ.genericPoint →
      Q.ordForm ω' = U'.ord h Q.genericPoint + Γ.ordForm ω := by
    intro Q Γ hQΓ
    rw [hω'h, Q.ordForm_smul hdU' (mul_ne_zero hh0 hjcω0) hτU'0, Scheme.ord_mul hh0 hjcω0,
      ord_functionFieldMap_eq jU Q.coheight_genericPoint (hcoh Q) (hmaxU Q), hordU Q Γ hQΓ,
      hωc, Γ.ordForm_smul hdU hcω0 hτU0, hQΓ]
    ring
  -- the pull-backs of the Cartier divisors `L j` to `U'`
  let Z0 : irreducibleComponents U := pointComponent (genericPoint U)
  choose LY hLY using fun j => MMP.Threefold.Bridges.exists_isPullback_of_isDominant jU (hLc j)
  have hLYcoeff : ∀ j (Q : Mori.PrimeDivisor U') (Γ : Mori.PrimeDivisor U),
      jU.base Q.genericPoint = Γ.genericPoint → (LY j).coeff Q = (L j).coeff Γ := by
    intro j Q Γ hQΓ
    obtain ⟨V, hV, φ, hφ⟩ := hLc j Γ.genericPoint
    rw [MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF (hLY j) hφ Q (by rwa [hQΓ])
      Γ.component, ord_functionFieldMap_eq jU Q.coheight_genericPoint (hcoh Q) (hmaxU Q), hQΓ,
      ← MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord, hφ Γ ((Γ.genericPoint_mem_iff V).mp hV)]
  have hLYloc : ∀ j (y' : U'), ∃ (V : U.Opens) (_ : jU.base y' ∈ V)
      (φ : (RationalFunctions U)ˣ) (_ : (L j).IsLocalEquation V φ)
      (ψ : (RationalFunctions U')ˣ), (LY j).IsLocalEquation (jU ⁻¹ᵁ V) ψ ∧
        ∀ Z, MMP.Threefold.Mori.Helpers.evalFF Z (ψ : RationalFunctions U') =
          functionFieldMap jU
            (MMP.Threefold.Mori.Helpers.evalFF Z0 (φ : RationalFunctions U)) := by
    intro j y'
    obtain ⟨V, hV, φ, hφ⟩ := hLc j (jU.base y')
    have hg : functionFieldMap jU
        (MMP.Threefold.Mori.Helpers.evalFF Z0 (φ : RationalFunctions U)) ≠ 0 :=
      (map_ne_zero _).mpr (φ.isUnit.map _).ne_zero
    obtain ⟨ψ, hψ⟩ := exists_units_evalFF_eq hg
    refine ⟨V, hV, φ, hφ, ψ, fun Q hQ => ?_, hψ⟩
    rw [MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF (hLY j) hφ Q
      ((Q.genericPoint_mem_iff _).mpr hQ) Z0, MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord, hψ]
  have hLYc : ∀ j, (LY j).IsCartier := fun j y' => by
    obtain ⟨V, hV, -, -, ψ, hψ, -⟩ := hLYloc j y'
    exact ⟨jU ⁻¹ᵁ V, hV, ψ, hψ⟩
  -- the principal divisor of `h = ω' / ω''`
  obtain ⟨ψh, hψh⟩ := exists_units_evalFF_eq hh0
  have hψhcoeff : ∀ Q : Mori.PrimeDivisor U',
      (principalDivisor ψh).coeff Q = U'.ord h Q.genericPoint := fun Q => by
    rw [coeff_principalDivisor, MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord, hψh]
  -- the presentation of `K' + B'` by Cartier divisors
  let r'' : Fin (m + 1) → ℝ := Fin.snoc r 1
  let L'' : Fin (m + 1) → Divisor U' := Fin.snoc LY (principalDivisor ψh)
  have hL''c : ∀ j, (L'' j).IsCartier := fun j => by
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa [L''] using Divisor.isCartier_principalDivisor ψh
    · simpa [L''] using hLYc j
  have hpres : Divisor.toRDivisor (divisorOfForm ω') + B' =
      ∑ j, r'' j • Divisor.toRDivisor (L'' j) := by
    refine DivisorWithCoeffs.ext' fun Q => ?_
    have hΓ := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ (hcoh Q)
    set Γ := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ (hcoh Q)
    have hQΓ : jU.base Q.genericPoint = Γ.genericPoint := hΓ.symm
    have hΓsum := congrArg (fun D : RDivisor U => D.coeff Γ) hsum
    simp only [DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor, coeff_divisorOfForm,
      MMP.Flips.coeff_sum_smul_toRDivisor] at hΓsum
    simp only [DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor, coeff_divisorOfForm,
      MMP.Flips.coeff_sum_smul_toRDivisor, Fin.sum_univ_castSucc, r'', L'', Fin.snoc_castSucc,
      Fin.snoc_last]
    rw [hordω' Q Γ hQΓ, hB' Q Γ hQΓ, DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor,
      hψhcoeff]
    simp_rw [hLYcoeff _ Q Γ hQΓ]
    push_cast
    rw [one_smul]
    linarith
  -- the function fields of `W` and `W' = W ×_U U'`
  letI := functionFieldAlgebra (f ≫ sU)
  letI : Algebra U.functionField W.functionField := functionFieldMapAlgebra f
  haveI : IsScalarTower k U.functionField W.functionField := isScalarTower_functionFieldMap sU f
  letI := functionFieldAlgebra (f' ≫ sU')
  letI : Algebra U'.functionField (pullback f jU).functionField := functionFieldMapAlgebra f'
  haveI : IsScalarTower κ U'.functionField (pullback f jU).functionField :=
    isScalarTower_functionFieldMap sU' f'
  letI : Algebra W.functionField (pullback f jU).functionField := functionFieldMapAlgebra p
  letI : Algebra k (pullback f jU).functionField :=
    ((algebraMap κ (pullback f jU).functionField).comp (algebraMap k κ)).toAlgebra
  haveI : IsScalarTower k κ (pullback f jU).functionField := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower k W.functionField (pullback f jU).functionField :=
    IsScalarTower.of_algebraMap_eq fun c =>
      (functionFieldMap_algebraMap_eq (f ≫ sU) (f' ≫ sU') p hpcompat c).symm
  letI : Algebra U.functionField (pullback f jU).functionField :=
    ((algebraMap W.functionField (pullback f jU).functionField).comp
      (algebraMap U.functionField W.functionField)).toAlgebra
  haveI : IsScalarTower U.functionField W.functionField (pullback f jU).functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hsq : ∀ x : U.functionField,
      functionFieldMap f' (functionFieldMap jU x) = functionFieldMap p (functionFieldMap f x) := by
    intro x
    rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
      MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
      MMP.Positivity.DivisorOver.functionFieldMap_congr hpf]
  haveI : IsScalarTower U.functionField U'.functionField (pullback f jU).functionField :=
    IsScalarTower.of_algebraMap_eq fun x => (hsq x).symm
  -- the adapted bases on `W` and `W'`
  have hbijf := hf.functionFieldMap_bijective
  have hbijf' := hf'.functionFieldMap_bijective
  haveI : Algebra.FormallyEtale U.functionField W.functionField :=
    Algebra.FormallyEtale.of_equiv
      (AlgEquiv.ofBijective (Algebra.ofId U.functionField W.functionField) hbijf)
  haveI : Algebra.FormallyEtale U'.functionField (pullback f jU).functionField :=
    Algebra.FormallyEtale.of_equiv
      (AlgEquiv.ofBijective (Algebra.ofId U'.functionField (pullback f jU).functionField) hbijf')
  let bW := (KaehlerDifferential.isBaseChange_of_formallyEtale k U.functionField
    W.functionField).basis bU
  have hbW : ∀ i, bW i = KaehlerDifferential.map k k _ _ (bU i) := fun i =>
    IsBaseChange.basis_apply _ _ i
  have hli' : LinearIndependent U'.functionField (fun j =>
      KaehlerDifferential.map k κ U.functionField U'.functionField (bU (Fin.natAdd e j))) := by
    by_contra hdep
    exact hβ' (AlternatingMap.map_linearDependent _ _ hdep)
  let b'U : Module.Basis (Fin 2) U'.functionField Ω[U'.functionField⁄κ] :=
    basisOfLinearIndependentOfCardEqFinrank hli' (by simp [hrkU'])
  have hb'U : ∀ j, b'U j =
      KaehlerDifferential.map k κ U.functionField U'.functionField (bU (Fin.natAdd e j)) :=
    fun j => by simp [b'U]
  let b'W := (KaehlerDifferential.isBaseChange_of_formallyEtale κ U'.functionField
    (pullback f jU).functionField).basis b'U
  have hb'W : ∀ j, b'W j = KaehlerDifferential.map κ κ _ _ (b'U j) := fun j =>
    IsBaseChange.basis_apply _ _ j
  let ℓW : Module.Basis Unit W.functionField (⋀[W.functionField]^(e + 2) Ω[W.functionField⁄k]) :=
    basisOfSpanSingleton (span_ιMulti_basis_eq_top bW) (ιMulti_basis_ne_zero bW)
  have hℓW : ℓW () = exteriorPower.ιMulti _ (e + 2) bW := by simp [ℓW]
  let ℓ'W : Module.Basis Unit (pullback f jU).functionField
      (⋀[(pullback f jU).functionField]^2 Ω[(pullback f jU).functionField⁄κ]) :=
    basisOfSpanSingleton (span_ιMulti_basis_eq_top b'W) (ιMulti_basis_ne_zero b'W)
  have hℓ'W : ℓ'W () = exteriorPower.ιMulti _ 2 b'W := by simp [ℓ'W]
  have htopW : ℓW () = topFormsMap k U.functionField W.functionField (e + 2) (ℓU ()) := by
    rw [hℓU, topFormsMap_ιMulti, hℓW]
    congr 1
    funext i
    exact hbW i
  have htopW' : ℓ'W () =
      topFormsMap κ U'.functionField (pullback f jU).functionField 2 (ℓU' ()) := by
    rw [hℓU', topFormsMap_ιMulti, hℓ'W]
    congr 1
    funext j
    rw [hb'W, hb'U]
  have hgenW : IsPullbackGenerator W.functionField (ℓU ()) :=
    ⟨by rw [hℓU]; exact span_ιMulti_basis_eq_top bU,
      by rw [← htopW, hℓW]; exact span_ιMulti_basis_eq_top bW,
      by rw [← htopW, hℓW]; exact ιMulti_basis_ne_zero bW⟩
  have hgenW' : IsPullbackGenerator (pullback f jU).functionField (ℓU' ()) :=
    ⟨by rw [hℓU']; exact (finrank_eq_one_iff_of_nonzero _ hβ').mp hrk1,
      by rw [← htopW', hℓ'W]; exact span_ιMulti_basis_eq_top b'W,
      by rw [← htopW', hℓ'W]; exact ιMulti_basis_ne_zero b'W⟩
  -- the orders of the adapted forms along `E` and `E'`
  let τW : RationalPluriForms (f ≫ sU) (e + 2) 1 := ZTensorPower.basis ℓW 1 ()
  let τW' : RationalPluriForms (f' ≫ sU') 2 1 := ZTensorPower.basis ℓ'W 1 ()
  have htcW : ∀ i, functionFieldMap p (functionFieldMap f (t i)) =
      algebraMap κ (pullback f jU).functionField (c i) := by
    intro i
    rw [← hsq, htc i]
    exact (IsScalarTower.algebraMap_apply κ U'.functionField (pullback f jU).functionField
      (c i)).symm
  have hdW : (Algebra.trdeg k W.functionField).toNat = e + 2 := by
    rwa [← trdeg_functionField_eq_of_bijective sU f hbijf]
  have hdW' : (Algebra.trdeg κ (pullback f jU).functionField).toNat = 2 := by
    rwa [← trdeg_functionField_eq_of_bijective sU' f' hbijf']
  have hordW : E'.ordForm τW' = E.ordForm τW := by
    have hfreeE := E.free_kaehlerDifferential_localRing (sX := f ≫ sU)
    have hfreeE' := E'.free_kaehlerDifferential_localRing (sX := f' ≫ sU')
    have h := ordAt_wedge_eq_of_scheme (f ≫ sU) (f' ≫ sU') p hpcompat
      (fun i => functionFieldMap f (t i)) c hc htcW E'.genericPoint E.genericPoint hEE'
      ⟨hfreeE.1, hfreeE.2, E.finrank_kaehlerDifferential_localRing.trans hdW⟩
      ⟨hfreeE'.1, hfreeE'.2, E'.finrank_kaehlerDifferential_localRing.trans hdW'⟩ bW
      (fun i => by rw [hbW, hbU, KaehlerDifferential.map_D]; rfl)
    refine h.2 E'.coheight_genericPoint ℓW hℓW ℓ'W ?_
    rw [hℓ'W]
    congr 1
    funext j
    rw [hb'W, hb'U, hbW, kaehler_map_comm (A' := U'.functionField)]
  -- the pull-backs of the forms and their orders along `E` and `E'`
  have hτW0 : τW ≠ 0 := (ZTensorPower.basis ℓW 1).ne_zero ()
  have hτW'0 : τW' ≠ 0 := (ZTensorPower.basis ℓ'W 1).ne_zero ()
  have hpbω : pullbackRationalPluriForms sU f ω = functionFieldMap f cω • τW := by
    rw [hωc]
    exact pullbackForms_smul_basis ℓU ℓW hgenW htopW cω
  have hpbω' : pullbackRationalPluriForms sU' f' ω' =
      functionFieldMap f' (h * functionFieldMap jU cω) • τW' := by
    rw [hω'h]
    exact pullbackForms_smul_basis ℓU' ℓ'W hgenW' htopW' _
  haveI : CharZero (ResidueField (W.presheaf.stalk (p E'.genericPoint))) := by
    letI := stalkAlgebra (f ≫ sU) (p E'.genericPoint)
    exact charZero_of_injective_algebraMap (algebraMap k _).injective
  have hpE : Order.coheight (p E'.genericPoint) = 1 := by
    rw [hEE']; exact E.coheight_genericPoint
  have hordp : ∀ g : W.functionField, (pullback f jU).ord (functionFieldMap p g) E'.genericPoint =
      W.ord g E.genericPoint := fun g => by
    rw [ord_functionFieldMap_eq p E'.coheight_genericPoint hpE
      (map_maximalIdeal_stalkMap_eq p E'.genericPoint) g, hEE']
  have hfcω0 : functionFieldMap f cω ≠ 0 := (map_ne_zero _).mpr hcω0
  have hf'h0 : functionFieldMap f' h ≠ 0 := (map_ne_zero _).mpr hh0
  have hf'jcω0 : functionFieldMap f' (functionFieldMap jU cω) ≠ 0 := (map_ne_zero _).mpr hjcω0
  have hordD : E.ordForm (pullbackRationalPluriForms sU f ω) =
      W.ord (functionFieldMap f cω) E.genericPoint + E.ordForm τW := by
    rw [hpbω, E.ordForm_smul hdW hfcω0 hτW0]
  have hordD' : E'.ordForm (pullbackRationalPluriForms sU' f' ω') =
      (pullback f jU).ord (functionFieldMap f' h) E'.genericPoint +
        W.ord (functionFieldMap f cω) E.genericPoint + E.ordForm τW := by
    rw [hpbω', E'.ordForm_smul hdW' ((map_ne_zero _).mpr (mul_ne_zero hh0 hjcω0)) hτW'0, map_mul,
      Scheme.ord_mul hf'h0 hf'jcω0, hsq, hordp, hordW]
  -- the Cartier pull-backs to `W` and to `W'`
  haveI : QuasiCompact (f ≫ sU) := hW.1.toQuasiCompact
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (f ≫ sU)
  haveI : QuasiCompact (f' ≫ sU') := hW'.1.toQuasiCompact
  haveI : CompactSpace (Limits.pullback f jU : Scheme.{v}) :=
    QuasiCompact.compactSpace_of_compactSpace (f' ≫ sU')
  choose LW hLW using fun j => MMP.Threefold.Bridges.exists_isPullback_of_isDominant f (hLc j)
  choose L''' hL''' using fun j =>
    MMP.Threefold.Bridges.exists_isPullback_of_isDominant f' (hL''c j)
  have hfE : f.base E.genericPoint = jU.base (f'.base E'.genericPoint) := by
    rw [← hEE', ← Scheme.Hom.comp_apply, hpf, Scheme.Hom.comp_apply]
  have hcoeffW : ∀ j : Fin m, ((L''' (Fin.castSucc j)).coeff E' : ℝ) = (LW j).coeff E := by
    intro j
    obtain ⟨V, hV, φ, hφ, ψ, hψ, hψev⟩ := hLYloc j (f'.base E'.genericPoint)
    have hψ' : (L'' (Fin.castSucc j)).IsLocalEquation (jU ⁻¹ᵁ V) ψ := by simpa [L''] using hψ
    rw [MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF (hL''' (Fin.castSucc j)) hψ' E' hV
      (pointComponent (genericPoint U')), hψev, hsq, hordp,
      MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF (hLW j) hφ E (by rw [hfE]; exact hV) Z0]
  have hcoeffh : ((L''' (Fin.last m)).coeff E' : ℝ) =
      (pullback f jU).ord (functionFieldMap f' h) E'.genericPoint := by
    have hψ' : (L'' (Fin.last m)).IsLocalEquation ⊤ ψh := by
      simpa [L''] using Divisor.isLocalEquation_principalDivisor ψh ⊤
    rw [MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF (hL''' (Fin.last m)) hψ' E' trivial
      (pointComponent (genericPoint U')), hψh]
  -- the discrepancy computed on `(W, f, E)`
  let DW : ProperDivisorOver k sU := ProperDivisorOver.mk ⟨W, f, hW, hf, E⟩ hfp
  have haW : IsDiscrepancyWith sU (e + 2) B ω r L DW
      ((DW.toDivisorOver.ordPullback ω : ℝ) - ∑ j, r j * ((LW j).coeff E : ℝ)) :=
    ⟨hX, hn, hω0, hLc, hsum, LW, fun j => ⟨_, hLW j⟩, rfl⟩
  have haa := (show IsDiscrepancyWith sU (e + 2) B ω r L E₀ a from
    ⟨hX, hn, hω0, hLc, hsum, L₀, hpb₀, ha₀⟩).eq haW hE₀
  have hdivK' : divisorOfForm ω' = K' := DivisorWithCoeffs.ext' fun Q => by
    rw [coeff_divisorOfForm, hω'K]
  refine ⟨hK', ⟨m + 1, r'', L'', hL''c, ?_⟩, ⟨⟨_, _, hW', E',
    functionFieldAlgEquiv sU' f' hbijf', Valuation.ext fun g => rfl⟩, _, rfl⟩,
    ProperDivisorOver.mk ⟨_, _, hW', hf', E'⟩ hfp', ω', m + 1, r'', L'', rfl, hdivK', hU'n, hK'.1,
    hω'0, hL''c, hpres, L''', fun j => ⟨_, hL''' j⟩, ?_⟩
  · rw [← hdivK', hpres]
    simp only [MMP.Flips.toRDivisor_eq_mapCoeffs]
  · rw [haa]
    change (E.ordForm (pullbackRationalPluriForms sU f ω) : ℝ) - _ =
      (E'.ordForm (pullbackRationalPluriForms sU' f' ω') : ℝ) - _
    rw [hordD, hordD', Fin.sum_univ_castSucc]
    simp only [r'', Fin.snoc_castSucc, Fin.snoc_last, hcoeffh]
    simp_rw [hcoeffW]
    push_cast
    ring

/-- On a normal variety with `K` canonical and `K + B` `ℝ`-Cartier, every divisor over `X` has a
discrepancy: compute it with a form `ω` with `div ω = K` and any presentation of `K + B`. -/
private theorem exists_isDiscrepancy {k : Type v} [Field k] [PerfectField k] {X : Scheme.{v}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [LocallyOfFiniteType sX] (hX : IsNormalVariety k sX) {n : ℕ} {K : Divisor X}
    {B : RDivisor X} (hK : K.IsCanonicalDivisor sX n)
    (hKB : IsCartierCombination (Divisor.toRDivisor K + B)) (E : ProperDivisorOver k sX) :
    ∃ a : ℝ, IsDiscrepancy sX n K B E.valuation a := by
  obtain ⟨ω, hω0, hωK⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  have hdiv : divisorOfForm ω = K := DivisorWithCoeffs.ext' fun Q => by
    rw [coeff_divisorOfForm, hωK]
  obtain ⟨m, r, L, hLc, hsum⟩ := hKB
  haveI := E.isIntegral
  haveI := E.isLocallyNoetherian
  haveI := E.isNormal
  haveI := E.isDominant
  haveI : QuasiCompact (E.f ≫ sX) := E.isNormalVariety.1.toQuasiCompact
  haveI : CompactSpace E.Y := QuasiCompact.compactSpace_of_compactSpace (E.f ≫ sX)
  choose L' hL' using fun j => MMP.Threefold.Bridges.exists_isPullback_of_isDominant E.f (hLc j)
  exact ⟨_, hK, ⟨m, r, L, hLc, hsum⟩, ⟨⟨E.Y, E.f ≫ sX, E.isNormalVariety, E.E,
    functionFieldAlgEquiv sX E.f E.isBirationalMorphism.functionFieldMap_bijective, rfl⟩, E, rfl⟩,
    E, ω, m, r, L, rfl, hdiv, hX, hK.topologicalKrullDim_eq, hω0, hLc, by rwa [hdiv],
    L', fun j => ⟨_, hL' j⟩, rfl⟩

end DiscrepancyTransport

section LogTerminalTransport

/-- **Log resolutions base change along flat unramified morphisms.** Let `jU : U' ⟶ U` be a flat,
formally unramified morphism from a normal variety over `κ` to a normal variety over `k`, both of
characteristic zero, and `D'` the flat pull-back of an `ℝ`-divisor `D` on `U`. The base change of
a log resolution `f : W ⟶ U` of `D` along `jU` is a log resolution of `D'`: its local rings are
regular, being flat and unramified over those of `W`, and the flat pull-back of the snc divisor
of `f` is an snc divisor cutting out `Supp(f'⁻¹_* D') ∪ Exc(f')`, codimensions being preserved. -/
private theorem isLogResolution_pullback_of_flat {k κ : Type v} [Field k] [CharZero k] [Field κ]
    [CharZero κ] {U U' : Scheme.{v}} (sU : U ⟶ Spec (.of k)) (sU' : U' ⟶ Spec (.of κ)) (jU : U' ⟶ U)
    [IsIntegral U] [IsLocallyNoetherian U] [IsNormal U] [CompactSpace U] [LocallyOfFiniteType sU]
    [IsIntegral U'] [IsLocallyNoetherian U'] [IsNormal U'] [CompactSpace U']
    [LocallyOfFiniteType sU'] [Flat jU] [FormallyUnramified jU] [Nonempty U']
    (hU'n : IsNormalVariety κ sU') {d d' : ℕ} (hdimU : topologicalKrullDim U = d)
    (hdimU' : topologicalKrullDim U' = d') (D : RDivisor U) (D' : RDivisor U')
    (hD'1 : ∀ (Q : Mori.PrimeDivisor U') (Γ : Mori.PrimeDivisor U),
      jU.base Q.genericPoint = Γ.genericPoint → D'.coeff Q = D.coeff Γ)
    (hD'2 : ∀ Q : Mori.PrimeDivisor U',
      (∀ Γ : Mori.PrimeDivisor U, jU.base Q.genericPoint ≠ Γ.genericPoint) → D'.coeff Q = 0)
    {W : Scheme.{v}} (f : W ⟶ U) (hflog : IsLogResolution sU D f) :
    IsLogResolution sU' D' (pullback.snd f jU) := by
  have hcharU : ∀ x : U, CharZero (ResidueField (U.presheaf.stalk x)) := fun x => by
    letI := stalkAlgebra sU x
    exact charZero_of_injective_algebraMap (algebraMap k _).injective
  obtain ⟨hDlog, hWvar, hWsm, hfprop, hfbir, G, hG01, hGsupp, hGsnc⟩ := hflog
  haveI : FormallyUnramified (pullback.fst f jU) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @FormallyUnramified)
      (IsPullback.of_hasPullback f jU).flip inferInstance
  have hWreg : ∀ w : W, IsRegularLocalRing (W.presheaf.stalk w) := by
    haveI : LocallyOfFinitePresentation (f ≫ sU) := inferInstance
    exact (MMP.Flips.ResolutionInputs.smooth_iff_forall_isRegularLocalRing_stalk _).mp
      ((Mori.isSmoothScheme_iff _).mp hWsm)
  -- the local rings of `W ×_U U'` are regular: flat unramified over those of `W`
  have hW'reg : ∀ w' : (pullback f jU : Scheme.{v}),
      IsRegularLocalRing ((pullback f jU).presheaf.stalk w') := by
    haveI : LocallyOfFinitePresentation (pullback.snd f jU ≫ sU') :=
      inferInstance
    intro w'
    set w := (pullback.fst f jU).base w'
    letI := ((pullback.fst f jU).stalkMap w').hom.toAlgebra
    haveI : Module.Flat (W.presheaf.stalk w) ((pullback f jU).presheaf.stalk w') :=
      Flat.stalkMap (pullback.fst f jU) w'
    haveI : Algebra.FormallyUnramified (W.presheaf.stalk w)
        ((pullback f jU).presheaf.stalk w') :=
      FormallyUnramified.stalkMap (pullback.fst f jU) w'
    haveI : IsLocalHom (algebraMap (W.presheaf.stalk w)
        ((pullback f jU).presheaf.stalk w')) :=
      inferInstanceAs (IsLocalHom ((pullback.fst f jU).stalkMap w').hom)
    haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sU)
    haveI : IsLocallyNoetherian (pullback f jU) :=
      LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f jU ≫ sU')
    haveI : CharZero (ResidueField (W.presheaf.stalk w)) := by
      letI := stalkAlgebra (f ≫ sU) w
      exact charZero_of_injective_algebraMap (algebraMap k _).injective
    haveI : Algebra.FormallySmooth (ResidueField (W.presheaf.stalk w))
        (ResidueField ((pullback f jU).presheaf.stalk w')) :=
      formallySmooth_of_charZero _ _
    exact isRegularLocalRing_of_formallyUnramified (hWreg w)
  -- a nonempty open of `W` where `f` is an open immersion, and a point of `W ×_U U'`
  haveI : IsIntegral W := hWvar.toIsIntegral
  haveI : IsDominant f := hfbir.isDominant
  haveI : Surjective f := inferInstance
  obtain ⟨u'⟩ := ‹Nonempty U'›
  obtain ⟨w, hw⟩ := f.surjective (jU.base u')
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := jU) w u' hw
  haveI : Nonempty (pullback f jU : Scheme.{v}) := ⟨z⟩
  obtain ⟨Wo, hWo, hWoi⟩ := MMP.Mori.IsBirationalMorphism.exists_isOpenImmersion hfbir
  -- `W ×_U U'` is a variety over `κ`
  have hW'var : Mori.IsVariety κ (pullback.snd f jU ≫ sU') := by
    obtain ⟨_, _, _, _⟩ := (Mori.isVariety_iff _ _).mp hU'n.1
    refine (Mori.isVariety_iff _ _).mpr ⟨?_, inferInstance, inferInstance, inferInstance⟩
    haveI := irreducibleSpace_pullback_of_flat f jU Wo hWo hWoi
    haveI : ∀ w' : (pullback f jU : Scheme.{v}),
        _root_.IsReduced ((pullback f jU).presheaf.stalk w') := fun w' => by
      haveI := hW'reg w'
      haveI := IsRegularLocalRing.isDomain ((pullback f jU).presheaf.stalk w')
      exact isReduced_of_noZeroDivisors
    haveI : IsReduced (pullback f jU : Scheme.{v}) := isReduced_of_isReduced_stalk _
    exact isIntegral_of_irreducibleSpace_of_isReduced _
  refine ⟨⟨hU'n, fun Q => ?_⟩, ?_, ?_, inferInstance, ?_⟩
  · by_cases h : ∃ Γ : Mori.PrimeDivisor U, jU.base Q.genericPoint = Γ.genericPoint
    · obtain ⟨Γ, hΓ⟩ := h
      rw [hD'1 Q Γ hΓ]
      exact hDlog.isBoundary Γ
    · push Not at h
      rw [hD'2 Q h]
      exact ⟨le_rfl, zero_le_one⟩
  · exact hW'var
  · -- `W ×_U U'` is smooth over `κ`
    haveI : LocallyOfFinitePresentation (pullback.snd f jU ≫ sU') :=
      inferInstance
    rw [Mori.isSmoothScheme_iff,
      MMP.Flips.ResolutionInputs.smooth_iff_forall_isRegularLocalRing_stalk]
    exact hW'reg
  · refine ⟨isBirationalMorphism_pullback_snd_of_flat f jU Wo hWo hWoi, ?_⟩
    -- the flat pull-back `G'` of the snc divisor `G`
    haveI : Smooth (f ≫ sU) := (Mori.isSmoothScheme_iff _).mp hWsm
    haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sU)
    haveI : IsNormal W := isNormal_of_smooth_over_field (f ≫ sU)
    haveI : CompactSpace W := by
      haveI : QuasiCompact (f ≫ sU) := hWvar.toQuasiCompact
      exact (quasiCompact_iff_compactSpace (f ≫ sU)).mp inferInstance
    haveI : LocallyOfFinitePresentation (pullback.snd f jU ≫ sU') :=
      inferInstance
    haveI : Smooth (pullback.snd f jU ≫ sU') := by
      rwa [MMP.Flips.ResolutionInputs.smooth_iff_forall_isRegularLocalRing_stalk]
    haveI : IsIntegral (pullback f jU : Scheme.{v}) := hW'var.toIsIntegral
    haveI : IsLocallyNoetherian (pullback f jU : Scheme.{v}) :=
      LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f jU ≫ sU')
    haveI : IsNormal (pullback f jU : Scheme.{v}) :=
      isNormal_of_smooth_over_field (pullback.snd f jU ≫ sU')
    haveI : CompactSpace (pullback f jU : Scheme.{v}) := by
      haveI : QuasiCompact (pullback.snd f jU ≫ sU') :=
        hW'var.toQuasiCompact
      exact (quasiCompact_iff_compactSpace
        (pullback.snd f jU ≫ sU')).mp inferInstance
    have hcharW : ∀ w : W, CharZero (ResidueField (W.presheaf.stalk w)) := fun w => by
      letI := stalkAlgebra (f ≫ sU) w
      exact charZero_of_injective_algebraMap (algebraMap k _).injective
    obtain ⟨G', hG'⟩ := exists_divisor_coeff_eq_of_flat (pullback.fst f jU) hcharW
      (MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hWsm G)
    have hEx := exists_map_genericPoint_eq (pullback.fst f jU) hcharW
    have hG'01 : ∀ Q, G'.coeff Q = 0 ∨ G'.coeff Q = 1 := fun Q => by
      obtain ⟨E, hE⟩ := hEx Q
      rw [hG' Q E hE]
      exact hG01 E
    refine ⟨G', hG'01, fun Q => ?_, ?_⟩
    · -- the coefficient-one locus of `G'` is `Supp(f'⁻¹_* D') ∪ Exc(f')`
      have hUn : IsNormalVariety k (sU) := hDlog.isNormalVariety
      have hWn : IsNormalVariety k (f ≫ sU) := ⟨hWvar, inferInstance⟩
      have hW'n : IsNormalVariety κ (pullback.snd f jU ≫ sU') :=
        ⟨hW'var, inferInstance⟩
      obtain ⟨E, hQE⟩ := hEx Q
      rw [hG' Q E hQE, hGsupp E]
      refine (birationalInverseTransform_ne_zero_or_isExceptional_iff hUn hdimU f hWn hfbir D
        E).trans (Iff.trans ?_ (birationalInverseTransform_ne_zero_or_isExceptional_iff hU'n
        hdimU' (pullback.snd f jU) hW'n
        (isBirationalMorphism_pullback_snd_of_flat f jU Wo hWo hWoi) D' Q).symm)
      have hx : f E.genericPoint = jU (pullback.snd f jU Q.genericPoint) := by
        rw [← hQE, ← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
      haveI := hcharU (jU (pullback.snd f jU Q.genericPoint))
      have hcohx := coheight_map_eq jU (pullback.snd f jU Q.genericPoint)
      rw [hx, hcohx]
      refine or_congr_left ⟨fun ⟨Γ, hΓ, hD⟩ => ?_, fun ⟨Q₀, hQ₀, hD'⟩ => ?_⟩
      · have h1 : Order.coheight (pullback.snd f jU Q.genericPoint) = 1 := by
          rw [← hcohx, hΓ, Γ.coheight_genericPoint]
        refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ h1,
          (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ h1).symm, ?_⟩
        change D'.coeff _ ≠ 0
        rw [hD'1 _ Γ ((congrArg jU
          (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ h1)).trans hΓ)]
        exact hD
      · haveI := hcharU (jU Q₀.genericPoint)
        have h1 : Order.coheight (jU Q₀.genericPoint) = 1 :=
          (coheight_map_eq jU Q₀.genericPoint).trans Q₀.coheight_genericPoint
        refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ h1, ?_, ?_⟩
        · rw [hQ₀]
          exact (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ h1).symm
        · change D.coeff _ ≠ 0
          rwa [← hD'1 Q₀ _ (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ h1).symm]
    · refine isSNCDivisor_of_flat_of_formallyUnramified (f ≫ sU)
        (pullback.snd f jU ≫ sU') (pullback.fst f jU) hWreg hW'reg
        hGsnc hG'01 fun Q hQ => ?_
      obtain ⟨E, hE⟩ := hEx Q
      refine ⟨E, Finsupp.mem_support_iff.mpr ?_, hE⟩
      change G.coeff E ≠ 0
      rwa [← hG' Q E hE]

/-- **Log terminality transports along flat unramified morphisms.** In the setting of
`isDiscrepancy_transport`, with `U'` a surface having a point other than its generic point, if
`(U, B)` is log terminal then so is `(U', B')`, for the flat pull-back `B'` of `B` and any
canonical divisor `K'` of `U'`: base change a witnessing log resolution `g` along `jU`; each
exceptional prime divisor of the base change lies over an exceptional prime divisor of `g`, with
the same discrepancy, and `K' + B'` is `ℝ`-Cartier since a transported discrepancy exists. -/
private theorem isLogTerminal_pullback_of_flat {k κ : Type v} [Field k] [CharZero k] [Field κ]
    [Algebra k κ] {U U' : Scheme.{v}} (sU : U ⟶ Spec (.of k)) (sU' : U' ⟶ Spec (.of κ))
    (jU : U' ⟶ U)
    [IsIntegral U] [IsLocallyNoetherian U] [IsNormal U] [CompactSpace U] [LocallyOfFiniteType sU]
    [IsIntegral U'] [IsLocallyNoetherian U'] [IsNormal U'] [CompactSpace U']
    [LocallyOfFiniteType sU'] [Flat jU] [FormallyUnramified jU] [IsDominant jU]
    (hjU : jU ≫ sU = sU' ≫ Spec.map (CommRingCat.ofHom (algebraMap k κ)))
    {e : ℕ} (t : Fin e → U.functionField) (c : Fin e → κ) (hc : AlgebraicIndependent k c)
    (htc : ∀ i, functionFieldMap jU (t i) =
      (letI := functionFieldAlgebra sU'; algebraMap κ U'.functionField (c i)))
    (hdimU : topologicalKrullDim U = (e + 2 : ℕ)) (hU'n : IsNormalVariety κ sU')
    (hdimU' : topologicalKrullDim U' = (2 : ℕ)) {x : U'} (hx : x ≠ genericPoint U')
    {n : ℕ} {K : Divisor U} {K' : Divisor U'} {B : RDivisor U} {B' : RDivisor U'}
    (hB'1 : ∀ (Q : Mori.PrimeDivisor U') (Γ : Mori.PrimeDivisor U),
      jU.base Q.genericPoint = Γ.genericPoint → B'.coeff Q = B.coeff Γ)
    (hB'2 : ∀ Q : Mori.PrimeDivisor U',
      (∀ Γ : Mori.PrimeDivisor U, jU.base Q.genericPoint ≠ Γ.genericPoint) → B'.coeff Q = 0)
    (hK' : K'.IsCanonicalDivisor sU' 2) (hlt : IsLogTerminal sU n K B) :
    IsLogTerminal sU' 2 K' B' := by
  haveI : CharZero κ := charZero_of_injective_algebraMap (algebraMap k κ).injective
  haveI : Nonempty U' := ⟨x⟩
  have hcharU : ∀ x : U, CharZero (ResidueField (U.presheaf.stalk x)) := fun x => by
    letI := stalkAlgebra sU x
    exact charZero_of_injective_algebraMap (algebraMap k _).injective
  obtain ⟨hBlog, hK, hKB, W, g, hglog, hgpos⟩ := hlt
  have hglog' := isLogResolution_pullback_of_flat sU sU' jU hU'n hdimU hdimU' B B' hB'1 hB'2 g hglog
  obtain ⟨-, hWvar, hWsm, hgp, hgb, -⟩ := hglog
  obtain ⟨hB'log, hW'var, hW'sm, hg'p, hg'b, -⟩ := id hglog'
  haveI : Smooth (g ≫ sU) := (Mori.isSmoothScheme_iff _).mp hWsm
  haveI : Smooth (pullback.snd g jU ≫ sU') :=
    (Mori.isSmoothScheme_iff _).mp hW'sm
  have hWn : IsNormalVariety k (g ≫ sU) :=
    ⟨hWvar, isNormal_of_smooth_over_field (g ≫ sU)⟩
  have hW'n : IsNormalVariety κ (pullback.snd g jU ≫ sU') :=
    ⟨hW'var, isNormal_of_smooth_over_field (pullback.snd g jU ≫ sU')⟩
  haveI : IsIntegral W := hWvar.toIsIntegral
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (g ≫ sU)
  haveI : IsNormal W := hWn.2
  haveI : IsIntegral (pullback g jU : Scheme.{v}) := hW'var.toIsIntegral
  haveI : IsLocallyNoetherian (pullback g jU : Scheme.{v}) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd g jU ≫ sU')
  haveI : IsNormal (pullback g jU : Scheme.{v}) := hW'n.2
  haveI : Flat (pullback.fst g jU) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Flat)
      (IsPullback.of_hasPullback g jU).flip inferInstance
  haveI : FormallyUnramified (pullback.fst g jU) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @FormallyUnramified)
      (IsPullback.of_hasPullback g jU).flip inferInstance
  have hEx := exists_map_genericPoint_eq (pullback.fst g jU) fun w => by
    letI := stalkAlgebra (g ≫ sU) w
    exact charZero_of_injective_algebraMap (algebraMap k _).injective
  have hex : ∀ E : Mori.PrimeDivisor W, ∃ a : ℝ, IsDiscrepancy (sU) n K B
      (ProperDivisorOver.mk ⟨W, g, hWn, hgb, E⟩ hgp).valuation a := fun E =>
    exists_isDiscrepancy hBlog.isNormalVariety hK hKB _
  -- a prime divisor of `W ×_U U'`: the base change is not a point, since it lies over `x`
  obtain ⟨E₀, hE₀⟩ : ∃ z : (pullback g jU : Scheme.{v}), Order.coheight z = 1 := by
    haveI : IsDominant (pullback.snd g jU) := hg'b.isDominant
    haveI : Surjective (pullback.snd g jU) := inferInstance
    obtain ⟨w, hw⟩ := (pullback.snd g jU).surjective x
    exact exists_coheight_eq_one (x := w) fun hwg =>
      hx (by rw [← hw, hwg, map_genericPoint_of_isDominant])
  refine ⟨hB'log, hK', ?_, _, _, hglog', fun hY' hf' hp' E' hexc b hb => ?_⟩
  · -- `K' + B'` is `ℝ`-Cartier: read off a transported discrepancy
    obtain ⟨E, hE⟩ := hEx (AlgebraicGeometry.PrimeDivisor.ofCoheightOne E₀ hE₀)
    obtain ⟨a, ha⟩ := hex E
    exact (isDiscrepancy_transport sU sU' jU hjU t c hc htc hdimU hU'n g E _ hE hWn hgb hgp hW'n
      hg'b hg'p n K K' B B' hB'1 hK' a ha).2.1
  · -- an exceptional `E'` lies over an exceptional `E`, with the same discrepancy
    obtain ⟨a', ha', rfl⟩ := hb
    obtain ⟨E, hE⟩ := hEx E'
    obtain ⟨a, ha⟩ := hex E
    rw [ha'.eq (isDiscrepancy_transport sU sU' jU hjU t c hc htc hdimU hU'n g E E' hE hWn hgb hgp
      hY' hf' hp' n K K' B B' hB'1 hK' a ha)]
    refine hgpos hWn hgb hgp E ?_ (1 + a) ⟨a, ha, rfl⟩
    have hx : g E.genericPoint = jU (pullback.snd g jU E'.genericPoint) := by
      rw [← hE, ← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    haveI := hcharU (jU (pullback.snd g jU E'.genericPoint))
    refine (isExceptional_iff_two_le_coheight hdimU _).mpr ?_
    have h := (isExceptional_iff_two_le_coheight hdimU' _).mp hexc
    change 2 ≤ Order.coheight (g E.genericPoint)
    rwa [hx, coheight_map_eq jU]

end LogTerminalTransport

end Proof_lem_mmp_normal_boundary_codimension_two_surface_model

namespace MMP.Flips

open MMP.Mori

open Proof_lem_mmp_normal_boundary_codimension_two_surface_model in
/-- Let `X` be a normal variety over an algebraically closed field `k` of characteristic zero,
`S` a prime divisor of `X` which is normal, and `P` a point of `S` with `dim 𝒪_{S,P} = 1`. Let
`H` be a strict henselization of `A = 𝒪_{X,P}` with residue field `κsep` and `R = Ĥ`. Then there
are a normal surface germ `(Y, y)` over `κsep` (`MMP.Mori.IsSurfaceGerm`: `y` closed, `Y ∖ {y}`
smooth), a prime divisor `C` of `Y` through `y` smooth over `κsep`, a flat, formally unramified
morphism `j : Y ⟶ X` with `j y = P` and `j(η_C) = η_S`, lying over
`Spec κsep ⟶ Spec k` (for `k → κ(P) → κsep`), and an isomorphism of `A`-algebras
`𝒪̂_{Y,y} ≃ R` carrying `I_C 𝒪̂_{Y,y}` onto `I_S R`. Moreover, for every open neighbourhood `U`
of `P`, every `ℝ`-divisor `D` on `U` with flat pull-back `D'` to `j⁻¹(U)`, and every projective
log resolution `f : W ⟶ U` of `D`, the base change of `f` along `j ∣_ U` is a projective log
resolution of `D'`; and for every exceptional prime divisor `E` of `W`, every prime divisor `E'`
of the base change lying over it and every `ℝ`-divisor `B` on `U` with flat pull-back `B'`, the
discrepancy of `E` with respect to `B` (`MMP.Flips.IsDiscrepancy`) is the discrepancy of `E'` with
respect to `B'`, computed with any canonical divisor of `j⁻¹(U)`; and if `(U, B)` is log terminal
(`MMP.Flips.IsLogTerminal`), so is `(j⁻¹(U), B')`, for any canonical divisor of `j⁻¹(U)`, and so
is `(U₀, B₀)` for every open neighbourhood `U₀ ⊆ j⁻¹(U)` of `y`, with `B₀` the flat pull-back of
`B` along `U₀ ⟶ U` and any canonical divisor of `U₀`. -/
@[mmp "lem_mmp_normal_boundary_codimension_two_surface_model"]
public theorem exists_surfaceModel_of_codimension_two
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (X : Scheme.{u}) (sX : X ⟶ Spec (.of k)) (hX : IsNormalVariety k sX)
    (S : Mori.PrimeDivisor X) (hS : IsNormal S.idealSheaf.subscheme)
    (P : X) (hPS : S.genericPoint ⤳ P)
    (hP : ringKrullDim (X.presheaf.stalk P ⧸
      RingHom.ker (X.presheaf.stalkSpecializes hPS ≫ X.residue S.genericPoint).hom) = 1)
    (κsep : Type u) [Field κsep] [Algebra (ResidueField (X.presheaf.stalk P)) κsep]
    [IsSepClosure (ResidueField (X.presheaf.stalk P)) κsep]
    (H : Type u) [CommRing H] [IsLocalRing H] [Algebra (X.presheaf.stalk P) H]
    [IsHenselization (X.presheaf.stalk P) κsep H] :
    let A := X.presheaf.stalk P
    let R := AdicCompletion (maximalIdeal H) H
    let IS : Ideal A :=
      RingHom.ker (X.presheaf.stalkSpecializes hPS ≫ X.residue S.genericPoint).hom
    ∃ (Y : Scheme.{u}) (sY : Y ⟶ Spec (.of κsep)) (j : Y ⟶ X) (y : Y) (C : Mori.PrimeDivisor Y)
      (hCy : C.genericPoint ⤳ y) (hjy : j.base y ⤳ P),
      IsSurfaceGerm sY y ∧ j.base y = P ∧ Smooth (C.idealSheaf.subschemeι ≫ sY) ∧
      j.base C.genericPoint = S.genericPoint ∧ Flat j ∧ FormallyUnramified j ∧
      j ≫ sX = sY ≫ Spec.map (CommRingCat.ofHom ((algebraMap (ResidueField A) κsep).comp
        (letI := stalkAlgebra sX P; algebraMap k (ResidueField A)))) ∧
      let φ : A →+* Y.presheaf.stalk y :=
        (X.presheaf.stalkSpecializes hjy ≫ j.stalkMap y).hom
      let IC : Ideal (Y.presheaf.stalk y) :=
        RingHom.ker (Y.presheaf.stalkSpecializes hCy ≫ Y.residue C.genericPoint).hom
      ∃ e : AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y) ≃+* R,
        (∀ a : A, e (algebraMap _ _ (φ a)) = algebraMap H R (algebraMap A H a)) ∧
        (IC.map (algebraMap _ _)).map e = (IS.map (algebraMap A H)).map (algebraMap H R) ∧
      ∀ (U : X.Opens) (_ : P ∈ U) [IsIntegral U] [IsLocallyNoetherian U] [IsNormal U]
        [CompactSpace U] [LocallyOfFiniteType (U.ι ≫ sX)]
        [IsIntegral (j ⁻¹ᵁ U)] [IsLocallyNoetherian (j ⁻¹ᵁ U)] [IsNormal (j ⁻¹ᵁ U)]
        [CompactSpace (j ⁻¹ᵁ U)] [LocallyOfFiniteType ((j ⁻¹ᵁ U).ι ≫ sY)],
        (∀ (D : RDivisor U) (D' : RDivisor (j ⁻¹ᵁ U)),
          (∀ (Q : Mori.PrimeDivisor (j ⁻¹ᵁ U)) (Γ : Mori.PrimeDivisor U),
            (j ∣_ U).base Q.genericPoint = Γ.genericPoint → D'.coeff Q = D.coeff Γ) →
          (∀ Q : Mori.PrimeDivisor (j ⁻¹ᵁ U),
            (∀ Γ : Mori.PrimeDivisor U, (j ∣_ U).base Q.genericPoint ≠ Γ.genericPoint) →
              D'.coeff Q = 0) →
          ∀ (W : Scheme.{u}) (f : W ⟶ U), IsProjectiveMorphism f →
            IsLogResolution (U.ι ≫ sX) D f →
            (IsProjectiveMorphism (pullback.snd f (j ∣_ U)) ∧
              IsLogResolution ((j ⁻¹ᵁ U).ι ≫ sY) D' (pullback.snd f (j ∣_ U))) ∧
            ∀ (E : Mori.PrimeDivisor W) (E' : Mori.PrimeDivisor (pullback f (j ∣_ U))),
              IsExceptionalPrimeDivisor (U.ι ≫ sX) f E →
              (pullback.fst f (j ∣_ U)).base E'.genericPoint = E.genericPoint →
              ∀ (hW : IsNormalVariety k (f ≫ U.ι ≫ sX)) (hf : IsBirationalMorphism f)
                (hfp : IsProper f)
                (hW' : IsNormalVariety κsep (pullback.snd f (j ∣_ U) ≫ (j ⁻¹ᵁ U).ι ≫ sY))
                (hf' : IsBirationalMorphism (pullback.snd f (j ∣_ U)))
                (hfp' : IsProper (pullback.snd f (j ∣_ U)))
                (n : ℕ) (K : Divisor U) (K' : Divisor (j ⁻¹ᵁ U)) (B : RDivisor U)
                (B' : RDivisor (j ⁻¹ᵁ U)),
                (∀ (Q : Mori.PrimeDivisor (j ⁻¹ᵁ U)) (Γ : Mori.PrimeDivisor U),
                  (j ∣_ U).base Q.genericPoint = Γ.genericPoint → B'.coeff Q = B.coeff Γ) →
                (∀ Q : Mori.PrimeDivisor (j ⁻¹ᵁ U),
                  (∀ Γ : Mori.PrimeDivisor U, (j ∣_ U).base Q.genericPoint ≠ Γ.genericPoint) →
                    B'.coeff Q = 0) →
                K'.IsCanonicalDivisor ((j ⁻¹ᵁ U).ι ≫ sY) 2 →
                ∀ a : ℝ,
                  IsDiscrepancy (U.ι ≫ sX) n K B
                      (ProperDivisorOver.mk ⟨W, f, hW, hf, E⟩ hfp).valuation a →
                    IsDiscrepancy ((j ⁻¹ᵁ U).ι ≫ sY) 2 K' B'
                      (ProperDivisorOver.mk ⟨_, _, hW', hf', E'⟩ hfp').valuation a) ∧
        (∀ (n : ℕ) (K : Divisor U) (K' : Divisor (j ⁻¹ᵁ U)) (B : RDivisor U)
          (B' : RDivisor (j ⁻¹ᵁ U)),
          (∀ (Q : Mori.PrimeDivisor (j ⁻¹ᵁ U)) (Γ : Mori.PrimeDivisor U),
            (j ∣_ U).base Q.genericPoint = Γ.genericPoint → B'.coeff Q = B.coeff Γ) →
          (∀ Q : Mori.PrimeDivisor (j ⁻¹ᵁ U),
            (∀ Γ : Mori.PrimeDivisor U, (j ∣_ U).base Q.genericPoint ≠ Γ.genericPoint) →
              B'.coeff Q = 0) →
          K'.IsCanonicalDivisor ((j ⁻¹ᵁ U).ι ≫ sY) 2 →
          IsLogTerminal (U.ι ≫ sX) n K B → IsLogTerminal ((j ⁻¹ᵁ U).ι ≫ sY) 2 K' B') ∧
        ∀ (U₀ : Y.Opens) (_ : y ∈ U₀) (_ : U₀ ≤ j ⁻¹ᵁ U) [IsIntegral U₀] [IsLocallyNoetherian U₀]
          [IsNormal U₀] [CompactSpace U₀] [LocallyOfFiniteType (U₀.ι ≫ sY)] (n : ℕ)
          (K : Divisor U) (B : RDivisor U) (K₀ : Divisor U₀) (B₀ : RDivisor U₀),
          (∀ (Q : Mori.PrimeDivisor U₀) (Γ : Mori.PrimeDivisor U),
            j.base (U₀.ι.base Q.genericPoint) = U.ι.base Γ.genericPoint →
              B₀.coeff Q = B.coeff Γ) →
          (∀ Q : Mori.PrimeDivisor U₀, (∀ Γ : Mori.PrimeDivisor U,
            j.base (U₀.ι.base Q.genericPoint) ≠ U.ι.base Γ.genericPoint) → B₀.coeff Q = 0) →
          K₀.IsCanonicalDivisor (U₀.ι ≫ sY) 2 →
          IsLogTerminal (U.ι ≫ sX) n K B → IsLogTerminal (U₀.ι ≫ sY) 2 K₀ B₀ := by
  intro A R IS
  obtain ⟨Y, sY, j, y, C, hCy, hjy, hgerm, hjP, hCs, hjC, ⟨e, he, hIdeal⟩, hjflat, hjfu,
    hjcompat, _, _, _, et, tX, cK, hcK, hdimX, htX⟩ :=
    exists_surfaceModel_germ k X sX hX S hS P hPS hP κsep H
  obtain ⟨hYn, hYd, -, -⟩ := id hgerm
  refine ⟨Y, sY, j, y, C, hCy, hjy, hgerm, hjP, hCs, hjC, hjflat, hjfu, hjcompat, e, he,
    hIdeal, ?_⟩
  intro U hPU _ _ _ _ _ _ _ _ _ _
  haveI : CharZero (ResidueField (X.presheaf.stalk P)) := by
    letI := stalkAlgebra sX P
    exact charZero_of_injective_algebraMap (algebraMap k _).injective
  haveI : CharZero κsep := charZero_of_injective_algebraMap
    (algebraMap (ResidueField (X.presheaf.stalk P)) κsep).injective
  haveI : FormallyUnramified (j ∣_ U) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @FormallyUnramified)
      (isPullback_morphismRestrict j U).flip hjfu
  haveI : Flat (j ∣_ U) := MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Flat)
    (isPullback_morphismRestrict j U).flip hjflat
  have hdimU : topologicalKrullDim U = (et + 2 : ℕ) := by
    have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
    rw [← hdimX]
    exact (topologicalKrullDim_eq_of_isOpen k X sX U U.isOpen ⟨P, hPU⟩).symm
  have hU'n : IsNormalVariety κsep ((j ⁻¹ᵁ U).ι ≫ sY) := by
    obtain ⟨_, hsep, _, _⟩ := (Mori.isVariety_iff _ _).mp hYn.1
    refine ⟨(Mori.isVariety_iff _ _).mpr ⟨inferInstance, inferInstance, inferInstance, ?_⟩,
      inferInstance⟩
    exact (quasiCompact_iff_compactSpace _).mpr inferInstance
  have hyU : y ∈ j ⁻¹ᵁ U := by
    change j.base y ∈ U
    rwa [hjP]
  have hdimU' : topologicalKrullDim (j ⁻¹ᵁ U) = (2 : ℕ) := by
    have : LocallyOfFiniteType sY := hYn.1.toLocallyOfFiniteType
    rw [show ((2 : ℕ) : WithBot ℕ∞) = 2 from rfl, ← hYd]
    exact (topologicalKrullDim_eq_of_isOpen κsep Y sY (j ⁻¹ᵁ U) (j ⁻¹ᵁ U).isOpen ⟨y, hyU⟩).symm
  letI := residueExtAlgebra sX P κsep
  haveI : IsIntegral Y := hYn.1.toIsIntegral
  haveI : LocallyOfFiniteType sY := hYn.1.toLocallyOfFiniteType
  haveI : Nonempty U := ⟨⟨P, hPU⟩⟩
  haveI : IsDominant U.ι := MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion U.ι
  -- `y` is not the generic point of an open neighbourhood: it specializes `η_C`
  have hyV : ∀ (V : Y.Opens) (hyV : y ∈ V) [IsIntegral V], (⟨y, hyV⟩ : V) ≠ genericPoint V := by
    intro V hyV _ h
    haveI : IsDominant V.ι := MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion V.ι
    have h1 : y = genericPoint Y := by
      have h2 := map_genericPoint_of_isDominant V.ι
      rwa [← h] at h2
    have h3 : C.genericPoint = genericPoint Y :=
      ((h1 ▸ hCy).antisymm ((genericPoint_spec Y).specializes trivial)).eq
    have h4 := C.coheight_genericPoint
    rw [h3, Order.coheight_eq_zero.mpr fun b _ =>
      Scheme.le_iff_specializes.mpr ((genericPoint_spec Y).specializes trivial)] at h4
    exact absurd h4 (by decide)
  -- an open `V` of `Y` over `U` lies over `Spec κsep ⟶ Spec k`, and the `tᵢ` pull back to the `cᵢ`
  have hdata : ∀ (V : Y.Opens) [IsIntegral V] (g : V.toScheme ⟶ U.toScheme) [IsDominant g],
      g ≫ U.ι = V.ι ≫ j →
      g ≫ U.ι ≫ sX = (V.ι ≫ sY) ≫ Spec.map (CommRingCat.ofHom (algebraMap k κsep)) ∧
      ∀ i, functionFieldMap g (functionFieldMap U.ι (tX i)) =
        (letI := MMP.Mori.functionFieldAlgebra (V.ι ≫ sY);
          algebraMap κsep V.toScheme.functionField (cK i)) := by
    intro V _ g _ hg
    haveI : IsDominant V.ι := MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion V.ι
    haveI : IsDominant (V.ι ≫ j) := by rw [← hg]; infer_instance
    refine ⟨by rw [← Category.assoc, hg, Category.assoc, hjcompat, Category.assoc], fun i => ?_⟩
    letI := MMP.Mori.functionFieldAlgebra sY
    letI := MMP.Mori.functionFieldAlgebra (V.ι ≫ sY)
    letI := functionFieldMapAlgebra V.ι
    haveI := isScalarTower_functionFieldMap sY V.ι
    rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
      MMP.Positivity.DivisorOver.functionFieldMap_congr hg,
      ← MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply, htX i,
      IsScalarTower.algebraMap_apply κsep Y.functionField V.toScheme.functionField]
    rfl
  haveI : IsDominant (j ∣_ U) := isDominant_of_flat (j ∣_ U)
  haveI : Nonempty (j ⁻¹ᵁ U) := ⟨⟨y, hyU⟩⟩
  obtain ⟨hjUc, htcU⟩ := hdata (j ⁻¹ᵁ U) (j ∣_ U) (morphismRestrict_ι j U)
  refine ⟨fun D D' hD'1 hD'2 W f hfproj hflog =>
    ⟨⟨hfproj.baseChange _, isLogResolution_pullback_of_flat _ _ _ hU'n hdimU hdimU' D D' hD'1
      hD'2 f hflog⟩, fun E E' _ hEE' hW hf hfp hW' hf' hfp' n K K' B B' hB'1 _ hK' a ha =>
        isDiscrepancy_transport _ _ _ hjUc _ cK hcK htcU hdimU hU'n f E E' hEE' hW hf hfp hW'
          hf' hfp' n K K' B B' hB'1 hK' a ha⟩,
    fun n K K' B B' hB'1 hB'2 hK' hlt => isLogTerminal_pullback_of_flat _ _ _ hjUc _ cK hcK
      htcU hdimU hU'n hdimU' (hyV _ hyU) hB'1 hB'2 hK' hlt, ?_⟩
  -- the same transport along `U₀ ⟶ j⁻¹U ⟶ U`, an open immersion followed by `j ∣_ U`
  intro U₀ hyU₀ hU₀ _ _ _ _ _ n K B K₀ B₀ hB1 hB2 hK₀ hlt
  let g : U₀.toScheme ⟶ U := Y.homOfLE hU₀ ≫ j ∣_ U
  haveI : FormallyUnramified g := MorphismProperty.comp_mem @FormallyUnramified _ _
    (FormallyUnramified.instOfIsOpenImmersionDiagonalScheme _) inferInstance
  haveI : IsDominant g := isDominant_of_flat g
  have hg : g ≫ U.ι = U₀.ι ≫ j := by
    simp only [g, Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι_assoc]
  obtain ⟨hgc, htcg⟩ := hdata U₀ g hg
  have hgj : ∀ Q : Mori.PrimeDivisor U₀, U.ι.base (g.base Q.genericPoint) =
      j.base (U₀.ι.base Q.genericPoint) := fun Q => by
    rw [← Scheme.Hom.comp_apply, hg, Scheme.Hom.comp_apply]
  have hU₀n : IsNormalVariety κsep (U₀.ι ≫ sY) := by
    obtain ⟨_, hsep, _, _⟩ := (Mori.isVariety_iff _ _).mp hYn.1
    refine ⟨(Mori.isVariety_iff _ _).mpr ⟨inferInstance, inferInstance, inferInstance, ?_⟩,
      inferInstance⟩
    exact (quasiCompact_iff_compactSpace _).mpr inferInstance
  have hdimU₀ : topologicalKrullDim U₀ = (2 : ℕ) := by
    rw [show ((2 : ℕ) : WithBot ℕ∞) = 2 from rfl, ← hYd]
    exact (topologicalKrullDim_eq_of_isOpen κsep Y sY U₀ U₀.isOpen ⟨y, hyU₀⟩).symm
  exact isLogTerminal_pullback_of_flat _ _ g hgc _ cK hcK htcg hdimU hU₀n hdimU₀ (hyV _ hyU₀)
    (fun Q Γ h => hB1 Q Γ (by rw [← hgj, h]))
    (fun Q h => hB2 Q fun Γ hΓ => h Γ (U.ι.isOpenEmbedding.injective (by rwa [hgj])))
    hK₀ hlt

end MMP.Flips

end
