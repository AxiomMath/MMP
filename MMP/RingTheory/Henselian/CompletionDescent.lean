module
public import MMP.Analysis.Complex.CauchyTransformRungeMontel
import MMP.RingTheory.DualizingComplex.FlatLocalExtension
import MMP.AlgebraicGeometry.Resolution.SmoothCentreBlowup
import MMP.RingTheory.RegularLocalRing.CompletionStrictHenselization

/-!
# Descent from the completed strict henselization of a normal local ring

Let `A` be a normal local domain essentially of finite type over a field `k` (the local ring
`𝒪_{X,x}` of a normal variety `X` at a point `x`), let `H = A^{sh}` be a strict henselization
and `R = Ĥ` its `𝔪_H`-adic completion. Then `R` is a Noetherian normal local domain, and the
following properties descend along the faithfully flat local map `A → R`:

* `A` is regular if and only if `R` is;
* a finite reflexive rank-one `A`-module `M` (the stalk `𝒪_X(D)_x` of a divisorial sheaf) is
  free if and only if `R ⊗[A] M` is; for a reflexive fractional ideal `I ⊆ K = Frac A` the
  multiplication map `R ⊗[A] I → L = Frac R` is injective with reflexive image, the divisorial
  module of the pulled-back divisor;
* the canonical module `ω_A = H^{-d}(ω_A^•)` of a normalized dualizing complex satisfies
  `R ⊗[A] ω_A ≅ ω_R`;
* `M ↦ R ⊗[A] M` is compatible with reflexive products and reflects isomorphisms, so it induces
  an injective homomorphism of divisor class groups `Cl(A) → Cl(R)`; iterating, it commutes
  with the reflexive powers `M^{[n]}`, and freeness of `(R ⊗[A] M)^{[n]}` descends to `M^{[n]}`;
* for every ideal `I` of `A`, contraction is a bijection from the minimal primes of `R` over
  `I R` onto the minimal primes of `H` over `I H`.

## Main results

* `MMP.isIntegrallyClosed_adicCompletion_strictHenselization_and_descent`
* `MMP.nonempty_baseChange_reflexivePower_equiv_and_free_of_free`: base change to `R`
  commutes with the reflexive powers `M^{[n]}` of a finite reflexive rank-one `A`-module, and
  freeness of `(R ⊗[A] M)^{[n]}` descends to `M^{[n]}`.

## References

* [KM98] Kollár, Mori, *Birational geometry of algebraic varieties*.
* [Kol92] Kollár et al., *Flips and abundance for algebraic threefolds*, Chapter 16.
-/

@[expose] public section

universe u

open CategoryTheory IsLocalRing TensorProduct

attribute [local instance] HasDerivedCategory.standard

namespace MMP

/-- A separable closure transported along a ring isomorphism compatible with the structure
maps is a separable closure. -/
private theorem isSepClosure_of_ringEquiv.{v} {K L M : Type v} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M] [IsSepClosure K L] (e : L ≃+* M)
    (he : ∀ x, e (algebraMap K L x) = algebraMap K M x) : IsSepClosure K M := by
  have : IsSepClosed L := IsSepClosure.sep_closed K
  exact isSepClosure_iff.2 ⟨IsSepClosed.of_ringEquiv e.symm,
    .of_equiv_equiv (RingEquiv.refl K) e (RingHom.ext fun x => (he x).symm)⟩

/-- Extension of scalars along an algebra map is the tensor product, `S`-linearly. -/
private noncomputable def extendScalarsObjEquivTensor.{v} {R S : Type v} [CommRing R] [CommRing S]
    [Algebra R S] (M : ModuleCat.{v} R) :
    (ModuleCat.extendScalars (algebraMap R S)).obj M ≃ₗ[S] S ⊗[R] M :=
  let e : (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S) ≃ₗ[R] S :=
    { AddEquiv.refl S with map_smul' := fun r s => (Algebra.smul_def r (show S from s)).symm }
  let eR := TensorProduct.congr e (LinearEquiv.refl R M)
  { __ := eR.toAddEquiv
    map_smul' := by
      intro s x
      let f₁ : (ModuleCat.extendScalars (algebraMap R S)).obj M →+ S ⊗[R] M :=
        eR.toAddMonoidHom.comp (AddMonoidHom.mk' (s • ·) (smul_add s))
      let f₂ : (ModuleCat.extendScalars (algebraMap R S)).obj M →+ S ⊗[R] M :=
        (AddMonoidHom.mk' (s • ·) (smul_add s)).comp eR.toAddMonoidHom
      change f₁ x = f₂ x
      induction x using TensorProduct.induction_on with
      | zero => exact (map_zero f₁).trans (map_zero f₂).symm
      | add x y hx hy =>
        exact ((map_add f₁ x y).trans (congrArg₂ (· + ·) hx hy)).trans (map_add f₂ x y).symm
      | tmul a m => rfl }

/-- An algebra essentially of finite type has a structure map essentially of finite type. -/
public theorem isEssentiallyOfFiniteType_algebraMap (k A : Type u) [CommRing k] [CommRing A]
    [Algebra k A] [Algebra.EssFiniteType k A] :
    IsEssentiallyOfFiniteType k A (algebraMap k A) := by
  rw [IsEssentiallyOfFiniteType, toAlgebra_algebraMap]
  exact ⟨Algebra.EssFiniteType.subalgebra k A, inferInstance, inferInstance, inferInstance,
    Algebra.EssFiniteType.submonoid k A, inferInstance, inferInstance,
    Algebra.EssFiniteType.isLocalization k A⟩

/-- The residue field of a strict henselization `H` of a local ring `A` (with respect to a
separable closure `κsep` of the residue field of `A`) is a separable closure of the residue
field of `A`. -/
public theorem isSepClosure_residueField_of_isHenselization (A : Type u) [CommRing A]
    [IsLocalRing A] (κsep : Type u) [Field κsep] [Algebra (ResidueField A) κsep]
    [IsSepClosure (ResidueField A) κsep] (H : Type u) [CommRing H] [IsLocalRing H] [Algebra A H]
    [IsLocalHom (algebraMap A H)] [IsHenselization A κsep H] :
    IsSepClosure (ResidueField A) (ResidueField H) := by
  obtain ⟨e, he⟩ := IsLocalRing.IsHenselization.exists_residueFieldEquiv
    (R := A) (L := κsep) (Rh := H)
  exact isSepClosure_of_ringEquiv e fun x => by
    obtain ⟨a, rfl⟩ := residue_surjective x
    rw [ResidueField.algebraMap_residue]
    exact he a

/-- **Completion descent for a normal local ring essentially of finite type over a field.**
Let `A` be a normal local domain essentially of finite type over `k`, `H` a strict
henselization of `A` and `R = Ĥ` its `𝔪_H`-adic completion. Then `R` is a Noetherian normal local
domain; `A` is regular iff `R` is; for finite reflexive rank-one `A`-modules, `R ⊗[A] -` preserves
reflexivity and rank one, detects freeness, commutes with reflexive products and reflects
isomorphisms; for a reflexive fractional ideal `I ⊆ K` the multiplication map `R ⊗[A] I → L` is
injective with reflexive image; `A` and `R` have normalized dualizing complexes and
`R ⊗[A] H^{-d}(ω_A^•) ≅ H^{-d}(ω_R^•)` with `d = dim A = dim R`; and for every ideal `I` of `A`,
`Ideal.comap (algebraMap H R)` is a bijection from the minimal primes of `R` over `I R` onto
those of `H` over `I H`. -/
@[mmp "lem_mmp_foundation_fa16_full_completion_descent"]
public theorem isIntegrallyClosed_adicCompletion_strictHenselization_and_descent
    (k : Type u) [Field k] (A : Type u) [CommRing A] [IsLocalRing A] [IsDomain A]
    [IsIntegrallyClosed A] [Algebra k A] [Algebra.EssFiniteType k A]
    (κsep : Type u) [Field κsep] [Algebra (ResidueField A) κsep]
    [IsSepClosure (ResidueField A) κsep]
    (H : Type u) [CommRing H] [IsLocalRing H] [Algebra A H] [IsHenselization A κsep H]
    (K L : Type u) [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra (AdicCompletion (maximalIdeal H) H) L]
    [IsFractionRing (AdicCompletion (maximalIdeal H) H) L] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A (AdicCompletion (maximalIdeal H) H) L] :
    ∃ _ : IsLocalRing (AdicCompletion (maximalIdeal H) H),
      -- `R` is a Noetherian normal local domain
      (IsNoetherianRing (AdicCompletion (maximalIdeal H) H) ∧
        IsDomain (AdicCompletion (maximalIdeal H) H) ∧
        IsIntegrallyClosed (AdicCompletion (maximalIdeal H) H)) ∧
      -- regularity descends and ascends
      (IsRegularLocalRing A ↔ IsRegularLocalRing (AdicCompletion (maximalIdeal H) H)) ∧
      -- reflexive rank-one modules: freeness (invertibility), reflexive products, isomorphisms
      (∀ (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
          [Module.IsReflexive A M], Module.rank A M = 1 →
        (Module.IsReflexive (AdicCompletion (maximalIdeal H) H)
            (AdicCompletion (maximalIdeal H) H ⊗[A] M) ∧
          Module.rank (AdicCompletion (maximalIdeal H) H)
            (AdicCompletion (maximalIdeal H) H ⊗[A] M) = 1) ∧
        (Module.Free A M ↔ Module.Free (AdicCompletion (maximalIdeal H) H)
            (AdicCompletion (maximalIdeal H) H ⊗[A] M)) ∧
        ∀ (N : Type u) [AddCommGroup N] [Module A N] [Module.Finite A N]
          [Module.IsReflexive A N], Module.rank A N = 1 →
          Nonempty (AdicCompletion (maximalIdeal H) H ⊗[A]
              Module.Dual A (Module.Dual A (M ⊗[A] N)) ≃ₗ[AdicCompletion (maximalIdeal H) H]
            Module.Dual (AdicCompletion (maximalIdeal H) H)
              (Module.Dual (AdicCompletion (maximalIdeal H) H)
                ((AdicCompletion (maximalIdeal H) H ⊗[A] M) ⊗[AdicCompletion (maximalIdeal H) H]
                  (AdicCompletion (maximalIdeal H) H ⊗[A] N)))) ∧
          (Nonempty ((AdicCompletion (maximalIdeal H) H ⊗[A] M)
              ≃ₗ[AdicCompletion (maximalIdeal H) H]
              (AdicCompletion (maximalIdeal H) H ⊗[A] N)) ↔ Nonempty (M ≃ₗ[A] N))) ∧
      -- the divisorial module of the pulled-back divisor
      (∀ (I : Submodule A K) [Module.Finite A I] [Module.IsReflexive A I],
        Function.Injective (LinearMap.liftBaseChange (AdicCompletion (maximalIdeal H) H)
            (((Algebra.linearMap K L).restrictScalars A).comp I.subtype)) ∧
          Module.IsReflexive (AdicCompletion (maximalIdeal H) H)
            (LinearMap.range (LinearMap.liftBaseChange (AdicCompletion (maximalIdeal H) H)
              (((Algebra.linearMap K L).restrictScalars A).comp I.subtype)))) ∧
      -- canonical modules: `ω_A ⊗[A] R ≅ ω_R`
      (∃ _ : IsNoetherianRing A, ∃ _ : IsNoetherianRing (AdicCompletion (maximalIdeal H) H),
        ringKrullDim (AdicCompletion (maximalIdeal H) H) = ringKrullDim A ∧
        (∃ DA : Stacks.Duality.StandardDerivedCategory A,
          Dualizing.IsNormalizedDualizingComplex.{u, u} DA) ∧
        (∃ DR : Stacks.Duality.StandardDerivedCategory (AdicCompletion (maximalIdeal H) H),
          Dualizing.IsNormalizedDualizingComplex.{u, u} DR) ∧
        ∀ (DA : Stacks.Duality.StandardDerivedCategory A)
          (DR : Stacks.Duality.StandardDerivedCategory (AdicCompletion (maximalIdeal H) H)),
          Dualizing.IsNormalizedDualizingComplex.{u, u} DA →
          Dualizing.IsNormalizedDualizingComplex.{u, u} DR →
          ∀ d : ℕ, ringKrullDim A = d →
            Nonempty (AdicCompletion (maximalIdeal H) H ⊗[A]
                Stacks.Duality.standardHomology DA (-(d : ℤ)) ≃ₗ[AdicCompletion (maximalIdeal H) H]
              Stacks.Duality.standardHomology DR (-(d : ℤ)))) ∧
      -- minimal primes of `H / I H` and of `R / I R`
      (∀ I : Ideal A,
        Set.BijOn (Ideal.comap (algebraMap H (AdicCompletion (maximalIdeal H) H)))
          ((I.map (algebraMap A H)).map
            (algebraMap H (AdicCompletion (maximalIdeal H) H))).minimalPrimes
          (I.map (algebraMap A H)).minimalPrimes) := by
  obtain ⟨-, ⟨-, hffAH, hmaxAH⟩, hloc, ⟨hNR, hdR, hicR⟩, ⟨-, hffHR, hmaxHR⟩, hreg⟩ :=
    MMP.Foundations.isNoetherianRing_strictHenselization_adicCompletion k A κsep H
  have hNA : IsNoetherianRing A := Algebra.EssFiniteType.isNoetherianRing k A
  have hcomp : algebraMap A (AdicCompletion (maximalIdeal H) H) =
      (algebraMap H (AdicCompletion (maximalIdeal H) H)).comp (algebraMap A H) :=
    IsScalarTower.algebraMap_eq A H _
  have : Module.Flat A (AdicCompletion (maximalIdeal H) H) :=
    Module.Flat.trans A H (AdicCompletion (maximalIdeal H) H)
  have : IsLocalHom (algebraMap A (AdicCompletion (maximalIdeal H) H)) := by
    rw [hcomp]
    infer_instance
  have hmax : (maximalIdeal A).map (algebraMap A (AdicCompletion (maximalIdeal H) H)) =
      maximalIdeal (AdicCompletion (maximalIdeal H) H) := by
    rw [hcomp, ← Ideal.map_map, hmaxAH, hmaxHR]
  refine ⟨hloc, ⟨hNR, hdR, hicR⟩, hreg, ?_, ?_, ?_, ?_⟩
  · intro M _ _ _ _ hM
    obtain ⟨h1, h2, h3, h4, -⟩ :=
      MMP.isReflexive_baseChange_and_free_iff_of_flat_of_rank_eq_one
        (B := AdicCompletion (maximalIdeal H) H) K L hM
    exact ⟨h1, h2.symm, fun N _ _ _ _ hN => ⟨h3 N hN, h4 N hN⟩⟩
  · intro I _ _
    exact (MMP.isReflexive_baseChange_and_free_iff_of_flat_of_rank_eq_one.{u, u, u, u, u, u, u}
      (B := AdicCompletion (maximalIdeal H) H) (M := A) K L (by simp)).2.2.2.2 I
  · obtain ⟨K0, hK0⟩ := Dualizing.exists_isDualizingComplex k
    obtain ⟨_, D, hD⟩ := Dualizing.exists_isDualizingComplex_of_isEssentiallyOfFiniteType
      (isEssentiallyOfFiniteType_algebraMap k A) K0 hK0
    obtain ⟨m, hm⟩ := Dualizing.exists_isNormalizedDualizingComplex_shift D hD
    obtain ⟨hDR, hdim, -⟩ := MMP.canonicalModule_derivedExtensionScalars_iso_of_flat hmax _ hm
    refine ⟨hNA, hNR, hdim, ⟨_, hm⟩, ⟨_, hDR⟩, ?_⟩
    intro DA DR hDA hDR' d hd
    obtain ⟨hDA', -, hiso, -⟩ :=
      MMP.canonicalModule_derivedExtensionScalars_iso_of_flat hmax DA hDA
    obtain ⟨eR⟩ := Dualizing.IsNormalizedDualizingComplex.nonempty_iso hDA' hDR'
    have := hiso d hd
    let e := asIso ((MMP.flatHomologyTensorComparison _ _ (-(d : ℤ))).app DA) ≪≫
      (DerivedCategory.homologyFunctor _ (-(d : ℤ))).mapIso eR
    exact ⟨(extendScalarsObjEquivTensor (Stacks.Duality.standardHomology DA (-(d : ℤ)))).symm ≪≫ₗ
      e.toLinearEquiv⟩
  · intro I
    have : HenselianLocalRing H := IsLocalRing.IsHenselization.henselian A κsep
    have := isSepClosure_residueField_of_isHenselization A κsep H
    exact (MMP.minimalPrimes_bijOn_comap_adicCompletion_of_strictHenselization k
      (IsLocalRing.IsHenselization.ind_etale_of_universe_le.{u, u, u} (R := A) κsep)
      hmaxAH I).2.2

/-! ### Reflexive powers -/

open Stacks.AlgebraicGeometry.ModuleReflexivePower (reflexivePower)

/-- Over a Noetherian domain a finite module and its double dual have the same rank: over the
fraction field both become the same finite-dimensional vector space. -/
private theorem rank_dual_dual {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (P : Type u) [AddCommGroup P] [Module A P] [Module.Finite A P] :
    Module.rank A (Module.Dual A (Module.Dual A P)) = Module.rank A P := by
  let K := FractionRing A
  have := Module.finitePresentation_of_finite A P
  have := Module.finitePresentation_of_finite A (Module.Dual A P)
  let e (Q : Type u) [AddCommGroup Q] [Module A Q] [Module.FinitePresentation A Q] :
      K ⊗[A] Module.Dual A Q ≃ₗ[K] Module.Dual K (K ⊗[A] Q) :=
    (Module.FinitePresentation.isBaseChange_map A Q A K).equiv ≪≫ₗ
      LinearEquiv.congrRight (AlgebraTensorModule.rid A K K)
  rw [← (TensorProduct.isBaseChange A (Module.Dual A (Module.Dual A P)) K).rank_eq,
    ← (TensorProduct.isBaseChange A P K).rank_eq]
  exact (e (Module.Dual A P) ≪≫ₗ (e P).symm.dualMap ≪≫ₗ
    (Module.evalEquiv K (K ⊗[A] P)).symm).rank_eq

/-- Over a domain the tensor product of two modules of rank one has rank one. -/
private theorem rank_tensorProduct_eq_one {A : Type u} [CommRing A] [IsDomain A]
    {M N : Type u} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (hM : Module.rank A M = 1) (hN : Module.rank A N = 1) : Module.rank A (M ⊗[A] N) = 1 := by
  let K := FractionRing A
  rw [← (TensorProduct.isBaseChange A (M ⊗[A] N) K).rank_eq,
    (AlgebraTensorModule.distribBaseChange A K M N).rank_eq, rank_tensorProduct',
    (TensorProduct.isBaseChange A M K).rank_eq, (TensorProduct.isBaseChange A N K).rank_eq, hM,
    hN, one_mul]

/-- **Reflexive powers and completion descent.** In the setting of
`isIntegrallyClosed_adicCompletion_strictHenselization_and_descent`, let `M` be a finite
reflexive `A`-module of rank one. Then for every `n`, base change to `R = Ĥ` commutes with the
reflexive power, `R ⊗[A] M^{[n]} ≅ (R ⊗[A] M)^{[n]}`, and `M^{[n]}` is free as soon as
`(R ⊗[A] M)^{[n]}` is.

Every `M^{[n]}` with `n ≥ 1` is again finite, reflexive (a double dual over a Noetherian
domain) and of rank one, so the binary product comparison and the descent of freeness of that
theorem apply to it; the comparison follows by induction on `n`. -/
public theorem nonempty_baseChange_reflexivePower_equiv_and_free_of_free
    (k : Type u) [Field k] (A : Type u) [CommRing A] [IsLocalRing A] [IsDomain A]
    [IsIntegrallyClosed A] [Algebra k A] [Algebra.EssFiniteType k A]
    (κsep : Type u) [Field κsep] [Algebra (ResidueField A) κsep]
    [IsSepClosure (ResidueField A) κsep]
    (H : Type u) [CommRing H] [IsLocalRing H] [Algebra A H] [IsHenselization A κsep H]
    (K L : Type u) [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra (AdicCompletion (maximalIdeal H) H) L]
    [IsFractionRing (AdicCompletion (maximalIdeal H) H) L] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A (AdicCompletion (maximalIdeal H) H) L]
    (M : ModuleCat.{u} (CommRingCat.of A)) [Module.Finite A M] [Module.IsReflexive A M]
    (hM : Module.rank A M = 1) (n : ℕ) :
    Nonempty (AdicCompletion (maximalIdeal H) H ⊗[A] reflexivePower M n
        ≃ₗ[AdicCompletion (maximalIdeal H) H]
      reflexivePower (ModuleCat.of (CommRingCat.of (AdicCompletion (maximalIdeal H) H))
        (AdicCompletion (maximalIdeal H) H ⊗[A] M)) n) ∧
    (Module.Free (AdicCompletion (maximalIdeal H) H)
        (reflexivePower (ModuleCat.of (CommRingCat.of (AdicCompletion (maximalIdeal H) H))
          (AdicCompletion (maximalIdeal H) H ⊗[A] M)) n) →
      Module.Free A (reflexivePower M n)) := by
  obtain ⟨-, -, -, hmod, -⟩ :=
    isIntegrallyClosed_adicCompletion_strictHenselization_and_descent k A κsep H K L
  have : IsNoetherianRing (CommRingCat.of A) := Algebra.EssFiniteType.isNoetherianRing k A
  have hfin (m : ℕ) : Module.Finite A (reflexivePower M m) :=
    @Stacks.AlgebraicGeometry.ModuleReflexivePower.finite_reflexivePower _ _ M ‹_› m
  have hpow (m : ℕ) : Module.IsReflexive A (reflexivePower M (m + 1)) ∧
      Module.rank A (reflexivePower M (m + 1)) = 1 := by
    induction m with
    | zero => exact ⟨‹_›, hM⟩
    | succ m ih =>
      have := hfin (m + 1)
      have : Module.Finite A (Module.Dual A (M ⊗[A] reflexivePower M (m + 1))) :=
        have := isNoetherian_linearMap A A (M ⊗[A] reflexivePower M (m + 1))
        Module.IsNoetherian.finite A _
      exact ⟨Stacks.ReflexiveDual.isReflexive_dual_of_finite
          (M := Module.Dual A (M ⊗[A] reflexivePower M (m + 1))),
        (rank_dual_dual (M ⊗[A] reflexivePower M (m + 1))).trans
          (rank_tensorProduct_eq_one hM ih.2)⟩
  have he : ∀ m, Nonempty (AdicCompletion (maximalIdeal H) H ⊗[A] reflexivePower M m
      ≃ₗ[AdicCompletion (maximalIdeal H) H]
      reflexivePower (ModuleCat.of (CommRingCat.of (AdicCompletion (maximalIdeal H) H))
        (AdicCompletion (maximalIdeal H) H ⊗[A] M)) m) := fun m => by
    induction m with
    | zero =>
      exact ⟨AlgebraTensorModule.rid A (AdicCompletion (maximalIdeal H) H)
        (AdicCompletion (maximalIdeal H) H)⟩
    | succ m ih =>
      match m, ih with
      | 0, _ => exact ⟨LinearEquiv.refl _ _⟩
      | m + 1, ⟨e⟩ =>
        have := hfin (m + 1)
        have := (hpow m).1
        obtain ⟨e'⟩ := (hmod M hM).2.2 _ (hpow m).2 |>.1
        exact ⟨e' ≪≫ₗ (TensorProduct.congr (LinearEquiv.refl _ _) e).dualMap.dualMap⟩
  refine ⟨he n, fun hfree => ?_⟩
  obtain ⟨e⟩ := he n
  cases n with
  | zero => exact Module.Free.self A
  | succ m =>
    have := hfin (m + 1)
    have := (hpow m).1
    exact ((hmod _ (hpow m).2).2.1).2 (Module.Free.of_equiv e.symm)

end MMP
