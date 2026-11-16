module

public import MMP.Attr
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Stalk
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.Completion
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.Normalization
public import StacksFrontier.AlgebraicGeometry.NormalizationQuotient.Defs
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.Basic
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.FiniteType
public import StacksFrontier.RingTheory.AdicCompletion.FiniteAlgebra
public import StacksFrontier.RingTheory.IntegrallyClosed.Stability
public import Mathlib.RingTheory.Flat.Basic
public import StacksFrontier.RingTheory.AdicCompletion.QuotientCompletionMap
public import StacksFrontier.RingTheory.Excellent.Basic
public import StacksFrontier.RingTheory.GRing.Henselization
public import StacksFrontier.RingTheory.IntegrallyClosed.Defs
public import StacksFrontier.RingTheory.Nagata.Basic
public import StacksFrontier.RingTheory.Nagata.Japanese
public import StacksFrontier.RingTheory.Regular.AscentAlongRegularRingHom
public import StacksFrontier.RingTheory.Regular.RegularRingHom
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.CompleteCaseStepCompletedStalk
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.ExcellentLocalResolution

/-!
# Completion and normalization

Three finiteness and normality statements about local rings of schemes of finite type over a
field.

* The completion `Â` of a normal local ring `A` essentially of finite type over a field `k` is a
  Noetherian normal local domain. The ring `A` is excellent, so `A → Â` is a regular ring map, and
  normality ascends along flat maps with geometrically regular fibres.
* Let `R` be a Noetherian normal domain with fraction field `F` and `F'/F` a finite extension. If
  `F'/F` is separable, or `R` is of finite type over an excellent ring, then the integral closure
  of `R` in `F'` is a finite `R`-module.
* Let `X` be a reduced scheme locally of finite type over a field, `ν : X^ν → X` its normalization
  and `x ∈ X`. Then `Ô_{X,x}` is reduced, and `(ν_* 𝒪_{X^ν})_x ⊗_{𝒪_{X,x}} Ô_{X,x}`, which is the
  product of the completions `Ô_{X^ν,x'}` over the points `x'` of `ν⁻¹(x)`, is the integral
  closure of `Ô_{X,x}` in its total ring of fractions.

## Main results

* `MMP.Resolution.isNormalDomain_adicCompletion_of_essFiniteType`
* `MMP.Resolution.finite_integralClosure_of_isSeparable_or_finiteType_isExcellent`
* `MMP.Resolution.isReduced_adicCompletion_stalk_and_normalization_completion`

## Implementation notes

The completion of a local ring `A` is `AdicCompletion (IsLocalRing.maximalIdeal A) A`, and the
total ring of fractions of a ring `B` is `FractionRing B`, the localization at the
nonzerodivisors. The normalization `ν : X^ν → X` of a scheme whose quasi-compact opens have
finitely many irreducible components is `AlgebraicGeometry.Scheme.normalization`, the relative
normalization of `X` in the disjoint union of the spectra of the residue fields at its generic
points.

The statement on normalization and completion is false for an arbitrary reduced scheme: Nagata's
examples give a reduced Noetherian local ring with non-reduced completion. It is stated for
schemes locally of finite type over a field, whose local rings are excellent. Closedness of the
point is not needed and is not assumed. The identification of the base-changed normalization
stalk with the product of the completed local rings is required to restrict, on each factor, to
the canonical map `(ν_* 𝒪_{X^ν})_x → 𝒪_{X^ν,x'}`; this determines it, since an `𝒪_{X,x}`-algebra
map out of `Ô_{X,x}` into a complete local ring is determined by its restriction to `𝒪_{X,x}`.

## References

* [Stacks Project, Tag 07QV](https://stacks.math.columbia.edu/tag/07QV)
* [Stacks Project, Tag 0C23](https://stacks.math.columbia.edu/tag/0C23)
* [Stacks Project, Tag 032L](https://stacks.math.columbia.edu/tag/032L)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing
open scoped TensorProduct

universe u v

namespace MMP.Resolution

/-- **The completion of a normal local ring essentially of finite type over a field is a
Noetherian normal local domain.** -/
@[mmp "lem_mmp_foundation_normal_ess_finite_type_local_completion"]
theorem isNormalDomain_adicCompletion_of_essFiniteType (k : Type v) (A : Type u) [Field k]
    [CommRing A] [IsLocalRing A] [Algebra k A] [Algebra.EssFiniteType k A] (hA : IsNormalRing A) :
    IsNoetherianRing (AdicCompletion (maximalIdeal A) A) ∧
      IsLocalRing (AdicCompletion (maximalIdeal A) A) ∧
      IsNormalDomain (AdicCompletion (maximalIdeal A) A) := by
  have hexc : IsExcellent A :=
    (isQuasiExcellent_and_isExcellent_of_essFiniteType.{v, u}).2
      ((isExcellent_of_standard_classes_and_finiteType.{v, v}).1 k)
  have : IsNoetherianRing A := hexc.1.1
  exact ⟨inferInstance, AdicCompletion.isLocalRing_of_fg (IsNoetherian.noetherian _),
    AlgebraicGeometry.isNormalDomain_adicCompletion_of_isExcellent A hexc hA⟩

/-- **Finiteness of the integral closure in a finite extension.** Let `R` be a Noetherian normal
domain with fraction field `F` and `F'/F` a finite field extension. If `F'/F` is separable, or `R`
is a finitely generated algebra over an excellent ring, then the integral closure of `R` in `F'`
is a finite `R`-module. -/
@[mmp "lem_mmp_foundation_separable_or_excellent_normalization"]
theorem finite_integralClosure_of_isSeparable_or_finiteType_isExcellent
    {R F F' : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    [Field F] [Field F'] [Algebra R F] [IsFractionRing R F] [Algebra F F'] [Algebra R F']
    [IsScalarTower R F F'] [FiniteDimensional F F']
    (h : Algebra.IsSeparable F F' ∨
      ∃ (E : Type u) (_ : CommRing E) (_ : Algebra E R), Algebra.FiniteType E R ∧ IsExcellent E) :
    Module.Finite R (integralClosure R F') := by
  rcases h with hsep | ⟨E, _, _, _, hE⟩
  · exact Noetherian_normal_domain_finite_separable_extension R F F'
  · have hR : IsExcellent R := (isQuasiExcellent_and_isExcellent_of_essFiniteType.{u, u}).2 hE
    have hN : IsNagataRing R := isNagataRing_of_isQuasiExcellent hR.1
    have hJ : IsJapaneseRing R :=
      IsJapaneseRing.of_ringEquiv (RingEquiv.quotientBot R) (hN.isJapaneseRing_quotient ⊥)
    let e : FractionRing R ≃ₐ[R] F := IsLocalization.algEquiv (nonZeroDivisors R) _ _
    let : Algebra (FractionRing R) F' := ((algebraMap F F').comp e.toRingHom).toAlgebra
    have : IsScalarTower R (FractionRing R) F' := IsScalarTower.of_algebraMap_eq fun a ↦ by
      change algebraMap R F' a = algebraMap F F' (e (algebraMap R (FractionRing R) a))
      rw [e.commutes, ← IsScalarTower.algebraMap_apply]
    let : Algebra (FractionRing R) F := e.toRingHom.toAlgebra
    have : IsScalarTower (FractionRing R) F F' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    have : Module.Finite (FractionRing R) F :=
      Module.Finite.of_surjective (Algebra.linearMap (FractionRing R) F) e.surjective
    have : Module.Finite (FractionRing R) F' := Module.Finite.trans F F'
    exact hJ.finite F'

/-! ### Helpers for `isReduced_adicCompletion_stalk_and_normalization_completion` -/

/-- A `B`-algebra `R` with `B → R` injective and birational to `B` (some `c` of `B`, a
nonzerodivisor in `R`, carries `R` into `B`) has `Frac R` a localization of `B` at its
nonzerodivisors. -/
private theorem isLocalization_fractionRing_of_smul_mem_range
    {B R : Type u} [CommRing B] [CommRing R] [Algebra B R]
    (hinj : Function.Injective (algebraMap B R)) (c : B)
    (hcR : ∀ r : R, ∃ b : B, c • r = algebraMap B R b)
    (hcnzd : algebraMap B R c ∈ nonZeroDivisors R) :
    IsLocalization (nonZeroDivisors B) (FractionRing R) := by
  classical
  have h1 : ∀ s ∈ nonZeroDivisors B, algebraMap B R s ∈ nonZeroDivisors R := by
    intro s hs
    rw [mem_nonZeroDivisors_iff_right]
    intro r hr
    obtain ⟨b, hb⟩ := hcR r
    have h2 : algebraMap B R (b * s) = 0 := by
      rw [map_mul, ← hb, Algebra.smul_def, mul_assoc, hr, mul_zero]
    have h3 : b = 0 :=
      (mem_nonZeroDivisors_iff_right.mp hs) b (hinj (h2.trans (map_zero _).symm))
    rw [h3, map_zero, Algebra.smul_def] at hb
    exact (mem_nonZeroDivisors_iff_right.mp hcnzd) r (by rwa [mul_comm])
  have h4 : ∀ r ∈ nonZeroDivisors R, ∀ b : B, c • r = algebraMap B R b →
      b ∈ nonZeroDivisors B := by
    intro r hr b hb
    rw [mem_nonZeroDivisors_iff_right]
    intro a ha
    have : algebraMap B R a * algebraMap B R b = 0 := by rw [← map_mul, ha, map_zero]
    rw [← hb, Algebra.smul_def, ← mul_assoc] at this
    have h5 := (mem_nonZeroDivisors_iff_right.mp hcnzd) _
      ((mem_nonZeroDivisors_iff_right.mp hr) _ this)
    exact hinj (h5.trans (map_zero _).symm)
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨s, hs⟩
    have := IsLocalization.map_units (FractionRing R) ⟨algebraMap B R s, h1 s hs⟩
    rwa [IsScalarTower.algebraMap_apply B R (FractionRing R)]
  · intro z
    obtain ⟨⟨r, t⟩, hz⟩ := IsLocalization.surj (nonZeroDivisors R) z
    obtain ⟨b, hb⟩ := hcR r
    obtain ⟨b', hb'⟩ := hcR t.1
    refine ⟨(b, ⟨b', h4 t.1 t.2 b' hb'⟩), ?_⟩
    dsimp only
    rw [IsScalarTower.algebraMap_apply B R (FractionRing R),
      IsScalarTower.algebraMap_apply B R (FractionRing R),
      ← hb, ← hb', Algebra.smul_def, Algebra.smul_def, map_mul, map_mul]
    dsimp only at hz
    linear_combination (algebraMap R (FractionRing R) (algebraMap B R c)) * hz
  · intro a b hab
    refine ⟨1, ?_⟩
    have : algebraMap B R a = algebraMap B R b := by
      apply IsFractionRing.injective R (FractionRing R)
      rwa [← IsScalarTower.algebraMap_apply B R (FractionRing R),
        ← IsScalarTower.algebraMap_apply B R (FractionRing R)]
    simp [hinj this]

/-- A finite, normal `B`-algebra `R` that is birational to `B` (some nonzerodivisor `c` of `B`
carries `R` into `B`) is the integral closure of `B` in `Frac B`. -/
private theorem exists_injective_range_eq_integralClosure_of_finite_normal
    {B R : Type u} [CommRing B] [CommRing R] [Algebra B R] [Module.Finite B R]
    (hinj : Function.Injective (algebraMap B R)) (c : B)
    (hcR : ∀ r : R, ∃ b : B, c • r = algebraMap B R b)
    (hcnzd : algebraMap B R c ∈ nonZeroDivisors R) (hR : IsNormalRing R) :
    ∃ g : R →+* FractionRing B, Function.Injective g ∧
      g.range = (integralClosure B (FractionRing B)).toSubring ∧
      ∀ y : B, g (algebraMap B R y) = algebraMap B (FractionRing B) y := by
  classical
  let L := FractionRing R
  have hloc : IsLocalization (nonZeroDivisors B) L :=
    isLocalization_fractionRing_of_smul_mem_range hinj c hcR hcnzd
  let e : FractionRing B ≃ₐ[B] L := IsLocalization.algEquiv (nonZeroDivisors B) _ _
  let gA : R →ₐ[B] FractionRing B :=
    e.symm.toAlgHom.comp (IsScalarTower.toAlgHom B R L)
  refine ⟨gA.toRingHom, fun x y hxy => IsFractionRing.injective R L (e.symm.injective hxy), ?_,
    gA.commutes⟩
  ext z
  simp only [RingHom.mem_range, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Subalgebra.mem_toSubring, mem_integralClosure_iff]
  constructor
  · rintro ⟨r, rfl⟩
    exact (Algebra.IsIntegral.isIntegral r).map gA
  · intro hz
    have hz' : IsIntegral B (e z) := hz.map e.toAlgHom
    have hclosed : IsIntegrallyClosedIn R L :=
      (isIntegrallyClosed_iff_isIntegrallyClosedIn L).mp hR.isIntegrallyClosed
    obtain ⟨y, hy⟩ := hclosed.isIntegral_iff.mp hz'.tower_top
    refine ⟨y, ?_⟩
    change e.symm (algebraMap R L y) = z
    rw [hy]
    simp

private theorem exists_injective_range_eq_integralClosure_tensorProduct
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B] [Algebra A A'] [Algebra A B]
    [Module.Finite A A'] [Module.Flat A B]
    (hinj : Function.Injective (algebraMap A A')) (c : A)
    (hcA' : ∀ a' : A', ∃ a : A, c • a' = algebraMap A A' a)
    (hc : ∀ a' : A', c • a' = 0 → a' = 0)
    (hnormal : IsNormalRing (A' ⊗[A] B)) :
    ∃ g : A' ⊗[A] B →+* FractionRing B, Function.Injective g ∧
      g.range = (integralClosure B (FractionRing B)).toSubring ∧
      ∀ y : B, g (1 ⊗ₜ[A] y) = algebraMap B (FractionRing B) y := by
  classical
  let : Algebra B (A' ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  have : IsScalarTower A B (A' ⊗[A] B) := Algebra.TensorProduct.right_isScalarTower
  have halg : ∀ y : B, algebraMap B (A' ⊗[A] B) y = 1 ⊗ₜ[A] y := fun y => rfl
  have : Module.Finite B (A' ⊗[A] B) := by
    have : Module.Finite B (B ⊗[A] A') := Module.Finite.base_change (R := A) (A := B) (M := A')
    exact Module.Finite.equiv (Algebra.TensorProduct.commRight A B A').toLinearEquiv
  have hinjB : Function.Injective (algebraMap B (A' ⊗[A] B)) := by
    have h1 : Function.Injective ((Algebra.linearMap A A').rTensor B) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ hinj
    intro y z hyz
    have : (Algebra.linearMap A A').rTensor B ((1 : A) ⊗ₜ[A] y) =
        (Algebra.linearMap A A').rTensor B ((1 : A) ⊗ₜ[A] z) := by
      simpa [halg] using hyz
    exact (TensorProduct.lid A B).symm.injective (by simpa using h1 this)
  have hsmul : ∀ x : A' ⊗[A] B, algebraMap B (A' ⊗[A] B) (algebraMap A B c) * x = c • x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a' y =>
      rw [halg, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← Algebra.smul_def,
        TensorProduct.tmul_smul]
    | add x y hx hy => rw [mul_add, smul_add, hx, hy]
  refine exists_injective_range_eq_integralClosure_of_finite_normal hinjB (algebraMap A B c) ?_ ?_
    hnormal
  · intro r
    induction r using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul a' y =>
      obtain ⟨a, ha⟩ := hcA' a'
      refine ⟨a • y, ?_⟩
      rw [Algebra.smul_def, hsmul, halg, TensorProduct.smul_tmul', ha, ← TensorProduct.smul_tmul,
        Algebra.smul_def, mul_one]
    | add x y hx hy =>
      obtain ⟨b₁, h₁⟩ := hx
      obtain ⟨b₂, h₂⟩ := hy
      exact ⟨b₁ + b₂, by rw [smul_add, h₁, h₂, map_add]⟩
  · rw [mem_nonZeroDivisors_iff_right]
    intro x hx
    rw [mul_comm, hsmul, TensorProduct.AlgebraTensorModule.smul_eq_lsmul_rTensor] at hx
    have h1 : Function.Injective ((LinearMap.lsmul A A' c).rTensor B) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ (fun a b hab => by
        have : c • (a - b) = 0 := by
          rw [smul_sub]
          exact sub_eq_zero.mpr hab
        exact sub_eq_zero.mp (hc _ this))
    exact h1 (hx.trans (map_zero _).symm)

private theorem exists_conductor_of_algEquiv_integralClosure
    {A A' : Type u} [CommRing A] [CommRing A'] [Algebra A A'] [Module.Finite A A']
    (e : A' ≃ₐ[A] integralClosure A (FractionRing A)) :
    ∃ c : A, (∀ a' : A', c • a' = 0 → a' = 0) ∧
      ∀ a' : A', ∃ a : A, c • a' = algebraMap A A' a := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := A')
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors A)
    (s.image fun x => ((e x : integralClosure A (FractionRing A)) : FractionRing A))
  refine ⟨b.1, fun a' h => ?_, fun a' => ?_⟩
  · have h1 : algebraMap A (FractionRing A) b.1 *
        ((e a' : integralClosure A (FractionRing A)) : FractionRing A) = 0 := by
      simpa [Algebra.smul_def] using
        congrArg (fun z => ((e z : integralClosure A (FractionRing A)) : FractionRing A)) h
    have hu : IsUnit (algebraMap A (FractionRing A) b.1) := IsLocalization.map_units _ b
    exact e.injective (Subtype.ext (by simpa using hu.mul_right_eq_zero.mp h1))
  · have hmem : a' ∈ Submodule.span A (s : Set A') := by simp [hs]
    induction hmem using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha⟩ := hb _ (Finset.mem_image_of_mem _ hx)
      refine ⟨a, e.injective (Subtype.ext ?_)⟩
      simp only [AlgEquiv.commutes]
      rw [map_smul]
      exact ha.symm
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a₁, h₁⟩ := hx
      obtain ⟨a₂, h₂⟩ := hy
      exact ⟨a₁ + a₂, by rw [smul_add, h₁, h₂, map_add]⟩
    | smul r x _ hx =>
      obtain ⟨a, ha⟩ := hx
      exact ⟨r * a, by rw [smul_comm, ha, map_mul, Algebra.smul_def]⟩

private theorem exists_ringEquiv_tensorProduct_adicCompletion_pi
    {A A' : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [CommRing A']
    [Algebra A A'] [Module.Finite A A']
    {I : Type u} (O : I → Type u) [∀ i, CommRing (O i)] [∀ i, IsLocalRing (O i)]
    (φ : ∀ i, A' →+* O i)
    (hover : ∀ i, (Ideal.comap (φ i) (maximalIdeal (O i))).comap (algebraMap A A') =
      maximalIdeal A)
    (hloc : ∀ i, letI := (φ i).toAlgebra
      IsLocalization.AtPrime (O i) (Ideal.comap (φ i) (maximalIdeal (O i))))
    (hbij : ∀ p : Ideal A', p.IsPrime → p.comap (algebraMap A A') = maximalIdeal A →
      ∃! i, Ideal.comap (φ i) (maximalIdeal (O i)) = p) :
    Finite I ∧ ∃ e : A' ⊗[A] AdicCompletion (maximalIdeal A) A ≃+*
        ((i : I) → AdicCompletion (maximalIdeal (O i)) (O i)),
      ∀ (a' : A') (i : I), e (a' ⊗ₜ 1) i =
        algebraMap (O i) (AdicCompletion (maximalIdeal (O i)) (O i)) (φ i a') := by
  classical
  let p := maximalIdeal A
  have : IsLocalization.AtPrime A p :=
    IsLocalization.of_le_isUnit fun a ha => (notMem_maximalIdeal (R := A)).mp ha
  let Q := p.primesOver A'
  let θ : I → Q := fun i =>
    ⟨Ideal.comap (φ i) (maximalIdeal (O i)), inferInstance, ⟨(hover i).symm⟩⟩
  have hθ : Function.Bijective θ := by
    refine ⟨fun i j hij => ?_, fun q => ?_⟩
    · obtain ⟨_, -, huniq⟩ := hbij (θ i).1 (θ i).2.1 (hover i)
      exact (huniq i rfl).trans (huniq j (congrArg Subtype.val hij).symm).symm
    · obtain ⟨i, hi, -⟩ := hbij q.1 q.2.1 q.2.2.over.symm
      exact ⟨i, Subtype.ext hi⟩
  let eθ : I ≃ Q := Equiv.ofBijective θ hθ
  have : Finite Q := Algebra.QuasiFinite.finite_primesOver (S := A') p
  refine ⟨Finite.of_equiv _ eθ.symm, ?_⟩
  have hprime : ∀ (j : I) (P P' : Ideal A') [P.IsPrime] [P'.IsPrime], P = P' →
      (letI := (φ j).toAlgebra; IsLocalization.AtPrime (O j) P) →
      (letI := (φ j).toAlgebra; IsLocalization.AtPrime (O j) P') := by
    rintro j P _ _ _ rfl
    exact id
  let Sq : Q → Type u := fun q => O (eθ.symm q)
  let (q : Q) : Algebra A' (Sq q) := (φ (eθ.symm q)).toAlgebra
  have hSq (q : Q) : IsLocalization.AtPrime (Sq q) q.1 := by
    have hq : Ideal.comap (φ (eθ.symm q)) (maximalIdeal (O (eθ.symm q))) = q.1 :=
      congrArg Subtype.val (eθ.apply_symm_apply q)
    have := q.2.1
    exact hprime (eθ.symm q) _ _ hq (hloc (eθ.symm q))
  obtain ⟨e0⟩ := AdicCompletion.nonempty_algEquiv_pi_primesOver (R := A) (S := A') p A Sq
  refine ⟨e0.toRingEquiv.trans
    (RingEquiv.piCongrLeft (fun i => AdicCompletion (maximalIdeal (O i)) (O i)) eθ.symm),
    fun a' i => ?_⟩
  obtain ⟨q, rfl⟩ := eθ.symm.surjective i
  have h1 : e0 (a' ⊗ₜ 1) = algebraMap A' _ a' := e0.commutes a'
  change (RingEquiv.piCongrLeft (fun i => AdicCompletion (maximalIdeal (O i)) (O i)) eθ.symm)
    (e0 (a' ⊗ₜ 1)) (eθ.symm q) = _
  rw [h1]
  exact (Equiv.piCongrLeft_apply_apply (P := fun i => AdicCompletion (maximalIdeal (O i)) (O i))
    (e := eθ.symm) _ q).trans rfl

section Geometry

open AlgebraicGeometry

/-- The canonical map from the pushforward stalk to the stalk at a point of the fibre. -/
private def fibreStalkMap (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) (x : X)
    (x' : (Scheme.normalization X hX).base ⁻¹' {x}) :
    Scheme.normalizationPushforwardStalk X hX x →+*
      (Scheme.normalizationScheme X hX).presheaf.stalk x' :=
  (TopCat.Presheaf.stalkSpecializes ((Scheme.normalization X hX).base _*
      (Scheme.normalizationScheme X hX).presheaf)
      (specializes_of_eq (Set.mem_singleton_iff.mp x'.2)) ≫
    TopCat.Presheaf.stalkPushforward _ (Scheme.normalization X hX).base
      (Scheme.normalizationScheme X hX).presheaf x').hom

private theorem isAffineOpen_preimage_normalization (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    {U : X.Opens} (hU : IsAffineOpen U) : IsAffineOpen (Scheme.normalization X hX ⁻¹ᵁ U) := by
  have := Scheme.quasiCompactFromGenericPointResidueFields X hX
  have := Scheme.quasiSeparatedFromGenericPointResidueFields X
  exact hU.preimage _

private theorem isAffineOpen_primeIdealOf_injective {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) : Function.Injective hU.primeIdealOf := fun a b h => by
  have e₁ := hU.fromSpec_primeIdealOf a
  rw [h, hU.fromSpec_primeIdealOf b] at e₁
  exact Subtype.ext e₁.symm

private theorem comap_app_primeIdealOf {Y X : Scheme.{u}} (f : Y ⟶ X) {U : X.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen (f ⁻¹ᵁ U)) (y : Y) (hy : y ∈ f ⁻¹ᵁ U) :
    (hV.primeIdealOf ⟨y, hy⟩).asIdeal.comap (f.app U).hom =
      (hU.primeIdealOf ⟨f.base y, hy⟩).asIdeal := by
  have h := IsAffineOpen.comap_primeIdealOf_appLE (f := f) (x := y) U hU (f ⁻¹ᵁ U) hV le_rfl hy
  have happ : (f.appLE U (f ⁻¹ᵁ U) le_rfl).hom = (f.app U).hom :=
    congrArg CommRingCat.Hom.hom (Scheme.Hom.appLE_eq_app f)
  rw [happ] at h
  exact congrArg PrimeSpectrum.asIdeal h

private theorem stalkSpecializes_stalkPushforward_germ {Y X : Scheme.{u}} (f : Y ⟶ X) (y : Y)
    (x : X) (h : f.base y = x) (U : X.Opens) (hx : x ∈ U) :
    (TopCat.Presheaf.germ (f.base _* Y.presheaf) U x hx ≫
      TopCat.Presheaf.stalkSpecializes (f.base _* Y.presheaf) (specializes_of_eq h) ≫
        TopCat.Presheaf.stalkPushforward _ f.base Y.presheaf y) =
      Y.presheaf.germ (f ⁻¹ᵁ U) y (by rw [← h] at hx; exact hx) := by
  subst h
  rw [TopCat.Presheaf.germ_stalkSpecializes_assoc]
  exact TopCat.Presheaf.stalkPushforward_germ _ _ _ _ _ _

private theorem stalkPushforward_comp_stalkMap {Y X : Scheme.{u}} (f : Y ⟶ X) (y : Y) :
    (TopCat.Presheaf.stalkSpecializes (f.base _* Y.presheaf)
        (specializes_of_eq (rfl : f.base y = f.base y)) ≫
        TopCat.Presheaf.stalkPushforward _ f.base Y.presheaf y).hom.comp
      ((TopCat.Presheaf.stalkFunctor CommRingCat (f.base y)).map f.c).hom =
      (f.stalkMap y).hom := by
  ext a
  simp [Scheme.Hom.stalkMap, TopCat.Presheaf.stalkSpecializes_refl]
  rfl

private theorem comap_comap_fibreStalkMap_eq_maximalIdeal (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) (x : X)
    (x' : (Scheme.normalization X hX).base ⁻¹' {x}) :
    letI : Algebra (X.presheaf.stalk x) (Scheme.normalizationPushforwardStalk X hX x) :=
      Scheme.normalizationPushforwardStalkAlgebra X hX x
    Ideal.comap (algebraMap (X.presheaf.stalk x) (Scheme.normalizationPushforwardStalk X hX x))
      (Ideal.comap (fibreStalkMap X hX x x')
        (maximalIdeal ((Scheme.normalizationScheme X hX).presheaf.stalk x'))) =
      maximalIdeal (X.presheaf.stalk x) := by
  obtain ⟨y, hy⟩ := x'
  have hy' : (Scheme.normalization X hX).base y = x := hy
  subst hy'
  let : Algebra (X.presheaf.stalk ((Scheme.normalization X hX).base y))
    (Scheme.normalizationPushforwardStalk X hX ((Scheme.normalization X hX).base y)) :=
    Scheme.normalizationPushforwardStalkAlgebra X hX _
  rw [Ideal.comap_comap]
  have hcomp : (fibreStalkMap X hX _ ⟨y, hy⟩).comp
      (algebraMap (X.presheaf.stalk _) (Scheme.normalizationPushforwardStalk X hX _)) =
        ((Scheme.normalization X hX).stalkMap y).hom :=
    stalkPushforward_comp_stalkMap (Scheme.normalization X hX) y
  rw [hcomp]
  ext a
  simp only [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    isUnit_map_iff]

private theorem isLocalization_atPrime_fibreStalk (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) (x : X)
    (x' : (Scheme.normalization X hX).base ⁻¹' {x}) :
    letI := (fibreStalkMap X hX x x').toAlgebra
    IsLocalization.AtPrime ((Scheme.normalizationScheme X hX).presheaf.stalk x')
      (Ideal.comap (fibreStalkMap X hX x x')
        (maximalIdeal ((Scheme.normalizationScheme X hX).presheaf.stalk x'))) := by
  classical
  let : Algebra _ _ := (fibreStalkMap X hX x x').toAlgebra
  obtain ⟨y, hy⟩ := x'
  have hy' : (Scheme.normalization X hX).base y = x := hy
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  change IsAffineOpen U at hU
  let ν := Scheme.normalization X hX
  let Y := Scheme.normalizationScheme X hX
  have hV : IsAffineOpen (ν ⁻¹ᵁ U) := isAffineOpen_preimage_normalization X hX hU
  have hyV : y ∈ ν ⁻¹ᵁ U := by
    change ν.base y ∈ U
    rwa [hy']
  let F := ν.base _* Y.presheaf
  let T := Γ(Y, ν ⁻¹ᵁ U)
  let M : Submonoid T :=
    Submonoid.map (ν.app U).hom (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
  let algTA' : Algebra T (Scheme.normalizationPushforwardStalk X hX x) :=
    (F.germ U x hxU).hom.toAlgebra
  have hA'loc : IsLocalization M (Scheme.normalizationPushforwardStalk X hX x) :=
    Scheme.pushforwardStalk_isLocalization ν U hU x hxU
  let algTO : Algebra T (Y.presheaf.stalk y) := (Y.presheaf.germ (ν ⁻¹ᵁ U) y hyV).hom.toAlgebra
  let P := (hV.primeIdealOf ⟨y, hyV⟩).asIdeal
  have hOloc : IsLocalization.AtPrime (Y.presheaf.stalk y) P := hV.isLocalization_stalk ⟨y, hyV⟩
  have hcomap : P.comap (ν.app U).hom = (hU.primeIdealOf ⟨x, hxU⟩).asIdeal := by
    have h := comap_app_primeIdealOf ν hU hV y hyV
    rwa [show (⟨ν.base y, hyV⟩ : U) = ⟨x, hxU⟩ from Subtype.ext hy'] at h
  have hMP : M ≤ P.primeCompl := by
    rintro _ ⟨r, hr, rfl⟩ hrP
    apply hr
    have : r ∈ Ideal.comap (ν.app U).hom P := hrP
    rwa [hcomap] at this
  have : IsScalarTower T (Scheme.normalizationPushforwardStalk X hX x) (Y.presheaf.stalk y) :=
    IsScalarTower.of_algebraMap_eq fun t =>
      (congrArg (fun f => f.hom t) (stalkSpecializes_stalkPushforward_germ ν y x hy' U hxU)).symm
  have h1 := IsLocalization.isLocalization_of_submonoid_le (R := T)
    (S := Scheme.normalizationPushforwardStalk X hX x) (T := Y.presheaf.stalk y) M P.primeCompl hMP
  refine IsLocalization.of_le (P.primeCompl.map (algebraMap T
    (Scheme.normalizationPushforwardStalk X hX x))) _ ?_ ?_
  · rintro _ ⟨t, ht, rfl⟩
    have hu := IsLocalization.map_units (Y.presheaf.stalk y) (⟨t, ht⟩ : P.primeCompl)
    rw [IsScalarTower.algebraMap_apply T (Scheme.normalizationPushforwardStalk X hX x)
      (Y.presheaf.stalk y)] at hu
    exact IsLocalRing.notMem_maximalIdeal.mpr hu
  · intro r hr
    exact IsLocalRing.notMem_maximalIdeal.mp hr

/-- For `x'` in the fibre over `x` and an affine open `U ∋ x`, the prime of `x'` in `ν⁻¹(U)` is the
contraction of the maximal ideal of `𝒪_{X^ν,x'}`. -/
private theorem comap_algebraMap_comap_fibreStalkMap (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) (x : X)
    {U : X.Opens} (hxU : x ∈ U) (hV : IsAffineOpen (Scheme.normalization X hX ⁻¹ᵁ U))
    (x' : (Scheme.normalization X hX).base ⁻¹' {x})
    (hyV : x'.1 ∈ Scheme.normalization X hX ⁻¹ᵁ U) :
    letI : Algebra Γ(Scheme.normalizationScheme X hX, Scheme.normalization X hX ⁻¹ᵁ U)
        (Scheme.normalizationPushforwardStalk X hX x) :=
      (((Scheme.normalization X hX).base _* (Scheme.normalizationScheme X hX).presheaf).germ
        U x hxU).hom.toAlgebra
    Ideal.comap (algebraMap Γ(Scheme.normalizationScheme X hX, Scheme.normalization X hX ⁻¹ᵁ U)
        (Scheme.normalizationPushforwardStalk X hX x))
      (Ideal.comap (fibreStalkMap X hX x x')
        (maximalIdeal ((Scheme.normalizationScheme X hX).presheaf.stalk x'))) =
      (hV.primeIdealOf ⟨x'.1, hyV⟩).asIdeal := by
  let : Algebra Γ(Scheme.normalizationScheme X hX, Scheme.normalization X hX ⁻¹ᵁ U)
      (Scheme.normalizationPushforwardStalk X hX x) :=
    (((Scheme.normalization X hX).base _* (Scheme.normalizationScheme X hX).presheaf).germ
      U x hxU).hom.toAlgebra
  let : Algebra Γ(Scheme.normalizationScheme X hX, Scheme.normalization X hX ⁻¹ᵁ U)
      ((Scheme.normalizationScheme X hX).presheaf.stalk x'.1) :=
    ((Scheme.normalizationScheme X hX).presheaf.germ _ x'.1 hyV).hom.toAlgebra
  have : IsLocalization.AtPrime ((Scheme.normalizationScheme X hX).presheaf.stalk x'.1)
      (hV.primeIdealOf ⟨x'.1, hyV⟩).asIdeal := hV.isLocalization_stalk ⟨x'.1, hyV⟩
  rw [Ideal.comap_comap]
  have hcomp : (fibreStalkMap X hX x x').comp
      (algebraMap Γ(Scheme.normalizationScheme X hX, Scheme.normalization X hX ⁻¹ᵁ U)
        (Scheme.normalizationPushforwardStalk X hX x)) =
      algebraMap Γ(Scheme.normalizationScheme X hX, Scheme.normalization X hX ⁻¹ᵁ U)
        ((Scheme.normalizationScheme X hX).presheaf.stalk x'.1) := by
    ext t
    exact congrArg (fun f => f.hom t)
      (stalkSpecializes_stalkPushforward_germ (Scheme.normalization X hX) x'.1 x x'.2 U hxU)
  rw [hcomp]
  exact IsLocalization.AtPrime.under_maximalIdeal _ _

/-- A point of the fibre over `x` is determined by the contraction to `A'` of the maximal ideal of
its local ring. -/
private theorem fibre_eq_of_comap_fibreStalkMap_eq (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) (x : X)
    (x₁ x₂ : (Scheme.normalization X hX).base ⁻¹' {x})
    (h : Ideal.comap (fibreStalkMap X hX x x₁)
        (maximalIdeal ((Scheme.normalizationScheme X hX).presheaf.stalk x₁)) =
      Ideal.comap (fibreStalkMap X hX x x₂)
        (maximalIdeal ((Scheme.normalizationScheme X hX).presheaf.stalk x₂))) :
    x₁ = x₂ := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hV := isAffineOpen_preimage_normalization X hX hU
  have hy (x' : (Scheme.normalization X hX).base ⁻¹' {x}) :
      x'.1 ∈ Scheme.normalization X hX ⁻¹ᵁ U := by
    change (Scheme.normalization X hX).base x'.1 ∈ U
    rwa [show (Scheme.normalization X hX).base x'.1 = x from x'.2]
  have e₁ := comap_algebraMap_comap_fibreStalkMap X hX x hxU hV x₁ (hy x₁)
  rw [h, comap_algebraMap_comap_fibreStalkMap X hX x hxU hV x₂ (hy x₂)] at e₁
  have h₁₂ := congrArg Subtype.val
    (isAffineOpen_primeIdealOf_injective hV (PrimeSpectrum.ext e₁.symm))
  exact Subtype.ext h₁₂

/-- A point of `ν⁻¹(U)` whose prime is the contraction of a prime of `A'` lying over the maximal
ideal of `𝒪_{X,x}` lies over `x`. -/
private theorem base_eq_of_primeIdealOf_eq_comap (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) (x : X)
    {U : X.Opens} (hU : IsAffineOpen U) (hxU : x ∈ U)
    (hV : IsAffineOpen (Scheme.normalization X hX ⁻¹ᵁ U))
    (p : Ideal (Scheme.normalizationPushforwardStalk X hX x))
    (hp : letI : Algebra (X.presheaf.stalk x) (Scheme.normalizationPushforwardStalk X hX x) :=
      Scheme.normalizationPushforwardStalkAlgebra X hX x
      Ideal.comap (algebraMap (X.presheaf.stalk x)
        (Scheme.normalizationPushforwardStalk X hX x)) p = maximalIdeal (X.presheaf.stalk x))
    (z : Scheme.normalizationScheme X hX) (hz : z ∈ Scheme.normalization X hX ⁻¹ᵁ U)
    (hzP :
      letI : Algebra Γ(Scheme.normalizationScheme X hX, Scheme.normalization X hX ⁻¹ᵁ U)
          (Scheme.normalizationPushforwardStalk X hX x) :=
        (((Scheme.normalization X hX).base _* (Scheme.normalizationScheme X hX).presheaf).germ
          U x hxU).hom.toAlgebra
      (hV.primeIdealOf ⟨z, hz⟩).asIdeal = Ideal.comap
        (algebraMap Γ(Scheme.normalizationScheme X hX, Scheme.normalization X hX ⁻¹ᵁ U)
          (Scheme.normalizationPushforwardStalk X hX x)) p) :
    (Scheme.normalization X hX).base z = x := by
  let : Algebra Γ(Scheme.normalizationScheme X hX, Scheme.normalization X hX ⁻¹ᵁ U)
      (Scheme.normalizationPushforwardStalk X hX x) :=
    (((Scheme.normalization X hX).base _* (Scheme.normalizationScheme X hX).presheaf).germ
      U x hxU).hom.toAlgebra
  let : Algebra (X.presheaf.stalk x) (Scheme.normalizationPushforwardStalk X hX x) :=
    Scheme.normalizationPushforwardStalkAlgebra X hX x
  let : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hxU).hom.toAlgebra
  have : IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨x, hxU⟩
  have hcomm : (algebraMap Γ(Scheme.normalizationScheme X hX, Scheme.normalization X hX ⁻¹ᵁ U)
      (Scheme.normalizationPushforwardStalk X hX x)).comp ((Scheme.normalization X hX).app U).hom =
      (algebraMap (X.presheaf.stalk x) (Scheme.normalizationPushforwardStalk X hX x)).comp
        (algebraMap Γ(X, U) (X.presheaf.stalk x)) := by
    ext r
    exact (congrArg (fun f => f.hom r)
      (TopCat.Presheaf.stalkFunctor_map_germ U x hxU (Scheme.normalization X hX).c)).symm
  have h := comap_app_primeIdealOf (Scheme.normalization X hX) hU hV z hz
  rw [hzP, Ideal.comap_comap, hcomm, ← Ideal.comap_comap, hp] at h
  have hx := IsLocalization.AtPrime.under_maximalIdeal (X.presheaf.stalk x)
    (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
  exact congrArg Subtype.val
    (isAffineOpen_primeIdealOf_injective hU (PrimeSpectrum.ext (h.symm.trans hx)))

private theorem existsUnique_fibre_comap_eq (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) (x : X)
    (p : Ideal (Scheme.normalizationPushforwardStalk X hX x)) [p.IsPrime]
    (hp : letI : Algebra (X.presheaf.stalk x) (Scheme.normalizationPushforwardStalk X hX x) :=
      Scheme.normalizationPushforwardStalkAlgebra X hX x
      Ideal.comap (algebraMap (X.presheaf.stalk x)
        (Scheme.normalizationPushforwardStalk X hX x)) p = maximalIdeal (X.presheaf.stalk x)) :
    ∃! x' : (Scheme.normalization X hX).base ⁻¹' {x},
      Ideal.comap (fibreStalkMap X hX x x')
        (maximalIdeal ((Scheme.normalizationScheme X hX).presheaf.stalk x')) = p := by
  classical
  let algAA' : Algebra (X.presheaf.stalk x) (Scheme.normalizationPushforwardStalk X hX x) :=
    Scheme.normalizationPushforwardStalkAlgebra X hX x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  change IsAffineOpen U at hU
  let ν := Scheme.normalization X hX
  let Y := Scheme.normalizationScheme X hX
  have hV : IsAffineOpen (ν ⁻¹ᵁ U) := isAffineOpen_preimage_normalization X hX hU
  let F := ν.base _* Y.presheaf
  let T := Γ(Y, ν ⁻¹ᵁ U)
  let M : Submonoid T :=
    Submonoid.map (ν.app U).hom (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
  let algTA' : Algebra T (Scheme.normalizationPushforwardStalk X hX x) :=
    (F.germ U x hxU).hom.toAlgebra
  have hA'loc : IsLocalization M (Scheme.normalizationPushforwardStalk X hX x) :=
    Scheme.pushforwardStalk_isLocalization ν U hU x hxU
  let P : PrimeSpectrum T :=
    ⟨Ideal.comap (algebraMap T (Scheme.normalizationPushforwardStalk X hX x)) p,
      Ideal.comap_isPrime _ _⟩
  let z : Y := hV.fromSpec P
  have hz : z ∈ ν ⁻¹ᵁ U := by
    have h0 : z ∈ Set.range hV.fromSpec := ⟨P, rfl⟩
    rwa [hV.range_fromSpec] at h0
  have hzP : hV.primeIdealOf ⟨z, hz⟩ = P :=
    hV.fromSpec.isOpenEmbedding.injective (hV.fromSpec_primeIdealOf ⟨z, hz⟩)
  have hνz : ν.base z = x := base_eq_of_primeIdealOf_eq_comap X hX x hU hxU hV p hp z hz
    (congrArg PrimeSpectrum.asIdeal hzP)
  have hex : Ideal.comap (fibreStalkMap X hX x ⟨z, hνz⟩) (maximalIdeal (Y.presheaf.stalk z)) =
      p := by
    have e : Ideal.comap (algebraMap T (Scheme.normalizationPushforwardStalk X hX x))
        (Ideal.comap (fibreStalkMap X hX x ⟨z, hνz⟩) (maximalIdeal (Y.presheaf.stalk z))) =
        Ideal.comap (algebraMap T (Scheme.normalizationPushforwardStalk X hX x)) p :=
      (comap_algebraMap_comap_fibreStalkMap X hX x hxU hV ⟨z, hνz⟩ hz).trans
        (congrArg PrimeSpectrum.asIdeal hzP)
    have := congrArg (Ideal.map (algebraMap T (Scheme.normalizationPushforwardStalk X hX x))) e
    rwa [IsLocalization.map_under M, IsLocalization.map_under M] at this
  exact ⟨⟨z, hνz⟩, hex, fun x'' hx'' =>
    fibre_eq_of_comap_fibreStalkMap_eq X hX x _ _ (hx''.trans hex.symm)⟩

/-- **Normalization commutes with completion** for a reduced scheme `X` locally of finite type
over a field. Let `ν : X^ν → X` be the normalization, `x ∈ X`, `A = 𝒪_{X,x}` and
`A' = (ν_* 𝒪_{X^ν})_x`. Then the completion `Â` is reduced; `A' ⊗_A Â` is the product of the
completions `Ô_{X^ν,x'}` over the points `x'` of `ν⁻¹(x)`, by an isomorphism restricting on each
factor to the canonical map `A' → 𝒪_{X^ν,x'}`; and `A' ⊗_A Â` is the integral closure of `Â` in
its total ring of fractions, by an injection into `Frac Â` extending the structure map of `Â`. -/
@[mmp "lem_mmp_foundation_reduced_normalization_completion"]
theorem isReduced_adicCompletion_stalk_and_normalization_completion
    {k : Type u} [Field k] (X : Scheme.{u}) [IsReduced X] (π : X ⟶ Spec (.of k))
    [LocallyOfFiniteType π]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) (x : X) :
    letI : Algebra (X.presheaf.stalk x) (Scheme.normalizationPushforwardStalk X hX x) :=
      Scheme.normalizationPushforwardStalkAlgebra X hX x
    let ν := Scheme.normalization X hX
    let Xν := Scheme.normalizationScheme X hX
    let A := X.presheaf.stalk x
    let A' := Scheme.normalizationPushforwardStalk X hX x
    let Ac := AdicCompletion (maximalIdeal A) A
    _root_.IsReduced Ac ∧
      (∃ e : A' ⊗[A] Ac ≃+*
          ((x' : ν.base ⁻¹' {x}) →
            AdicCompletion (maximalIdeal (Xν.presheaf.stalk x')) (Xν.presheaf.stalk x')),
        ∀ (a' : A') (x' : ν.base ⁻¹' {x}),
          e (a' ⊗ₜ 1) x' =
            algebraMap (Xν.presheaf.stalk x')
              (AdicCompletion (maximalIdeal (Xν.presheaf.stalk x')) (Xν.presheaf.stalk x'))
              ((TopCat.Presheaf.stalkSpecializes (ν.base _* Xν.presheaf)
                  (specializes_of_eq (Set.mem_singleton_iff.mp x'.2)) ≫
                TopCat.Presheaf.stalkPushforward _ ν.base Xν.presheaf x').hom a')) ∧
      ∃ g : A' ⊗[A] Ac →+* FractionRing Ac,
        Function.Injective g ∧
        g.range = (integralClosure Ac (FractionRing Ac)).toSubring ∧
        ∀ y : Ac, g (1 ⊗ₜ y) = algebraMap Ac (FractionRing Ac) y := by
  intro ν Xν A A' Ac
  have hA : IsNagataRing A :=
    isNagataRing_of_isQuasiExcellent
      (AlgebraicGeometry.isExcellent_stalk_of_locallyOfFiniteType_of_isExcellent k
        ((isExcellent_of_standard_classes_and_finiteType.{u, u}).1 k) π x).1
  have : _root_.IsReduced A := AlgebraicGeometry.isReduced_stalk_of_isReduced X x
  have : IsNoetherianRing A := hA.1
  let : Algebra A A' := Scheme.normalizationPushforwardStalkAlgebra X hX x
  let e0 : A' ≃ₐ[A] integralClosure A (FractionRing A) :=
    Stacks.AlgebraicGeometry.NormalizationQuotient.normalizationStalkAlgEquivIntegralClosureSelf
      X hX x
  have : Module.Finite A (integralClosure A (FractionRing A)) :=
    module_finite_integralClosure_fractionRing hA
  have : Module.Finite A A' := Module.Finite.of_surjective e0.symm.toLinearMap e0.symm.surjective
  have hNag : IsNagataScheme X := isNagataScheme_of_locallyOfFiniteType_over_field k π
  have : IsFinite ν := Scheme.isFinite_normalization hNag hX
  have hNormalScheme : IsNormal Xν := Scheme.isNormal_normalizationScheme X hX
  obtain ⟨hfinI, e, he⟩ := exists_ringEquiv_tensorProduct_adicCompletion_pi (A := A) (A' := A')
    (I := ν.base ⁻¹' {x}) (fun i => Xν.presheaf.stalk i) (fibreStalkMap X hX x)
    (comap_comap_fibreStalkMap_eq_maximalIdeal X hX x) (isLocalization_atPrime_fibreStalk X hX x)
    (fun p _ hov => existsUnique_fibre_comap_eq X hX x p hov)
  have hnormal : IsNormalRing (A' ⊗[A] Ac) := by
    refine IsNormalRing.congr e.symm (isNormalRing_pi fun i => ?_)
    have hexc : IsExcellent (Xν.presheaf.stalk i) :=
      AlgebraicGeometry.isExcellent_stalk_of_locallyOfFiniteType_of_isExcellent k
        ((isExcellent_of_standard_classes_and_finiteType.{u, u}).1 k) (ν ≫ π) i
    have hn : IsNormalRing (Xν.presheaf.stalk i) := by
      have : IsDomain (Xν.presheaf.stalk i) := hNormalScheme.stalk_isDomain i
      have : IsIntegrallyClosed (Xν.presheaf.stalk i) := hNormalScheme.stalk_normal i
      exact IsNormalRing.of_isIntegrallyClosed _
    have := AlgebraicGeometry.isNormalDomain_adicCompletion_of_isExcellent _ hexc hn
    exact IsNormalRing.of_isIntegrallyClosed _
  refine ⟨IsLocalRing.isReduced_adicCompletion_maximalIdeal_of_isNagataRing hA, ⟨e, he⟩, ?_⟩
  obtain ⟨c, hc, hcA'⟩ := exists_conductor_of_algEquiv_integralClosure e0
  have : Module.Flat A Ac := AdicCompletion.flat_of_isNoetherian (maximalIdeal A)
  exact exists_injective_range_eq_integralClosure_tensorProduct (A := A) (A' := A') (B := Ac)
    (Stacks.AlgebraicGeometry.NormalizationQuotient.normalizationPushforwardStalk_map_injective
      X hX x) c hcA' hc hnormal

end Geometry

end MMP.Resolution
