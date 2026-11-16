module
public import MMP.AlgebraicGeometry.Divisor.Basic
public import MMP.AlgebraicGeometry.ProjectiveBundle.VectorBundles
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.OverQuotients
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LargeModuleUniverse
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.Birational
public import StacksFrontier.AlgebraicGeometry.FiberRank.LocallyFree
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Sheaf
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.AdicQuotientMap
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteTypePullbackScheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.GenericPoint
public import StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiSliceComponentModule
public import StacksFrontier.AlgebraicGeometry.Topologies.FiniteTypeOnSiteEpi

/-!
# Blowing up the first Fitting ideal of a rank-one module

Let `X` be a normal complex variety and `M` a coherent torsion-free `𝒪_X`-module of generic
rank one, and put `I = Fitt₁(M)`. Then `I` is the unit ideal at every codimension-one point of
`X`, and on the blowup `b : X' = Bl_I X → X` the quotient of `b^*M` by its torsion is
invertible: there is an invertible `𝒪_{X'}`-module `L` and a surjection `b^*M → L` whose
kernel is exactly the torsion of `b^*M`. Consequently `X'` maps over `X` into the component
of `ℙ_X(M)` which is the closure of the fibre over the generic point of `X`.

## Main results

* `MMP.Conductor.fittingIdeal_one_blowUp_torsionFreeQuotient_invertible`

## References

* [Stacks Project, Tag 0ESN](https://stacks.math.columbia.edu/tag/0ESN)
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Stacks.AlgebraicGeometry.ReflexiveModules (IsTorsionFree IsTorsionSection)
open MMP.Intersection.Scheme.Modules (projectiveBundle projectiveBundleToBase
  projectiveBundleTwistOne)

namespace MMP.Conductor

universe u

private theorem fittingIdeal_eq_map_of_localizedModule
    {R : Type u} [CommRing R] (P : Ideal R) [P.IsPrime]
    {S : Type u} [CommRing S] [Algebra R S] [IsLocalization.AtPrime S P]
    {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
    {Ms : Type u} [AddCommGroup Ms] [Module R Ms] [Module S Ms] [IsScalarTower R S Ms]
    [Module.Finite S Ms]
    (f : M →ₗ[R] Ms) [IsLocalizedModule P.primeCompl f] (k : ℕ) :
    fittingIdeal (R := S) (M := Ms) (k : ℤ) =
      Ideal.map (algebraMap R S) (fittingIdeal (R := R) (M := M) (k : ℤ)) := by
  have hb := IsLocalizedModule.isBaseChange P.primeCompl S f
  let e : TensorProduct R S M ≃ₗ[S] Ms := hb.equiv
  have : Module.Finite S (TensorProduct R S M) := Module.Finite.equiv e.symm
  rw [← (fittingIdeal_basic_properties.{u, u, u, u} (R := R) (M := M)).2.2.1 S k]
  exact (fittingIdeal_eq_of_linearEquiv e k).symm

/-- If the localization of `M` at `P` is cyclic, then `Fitt₁ M ⊄ P`. -/
private theorem not_fittingIdeal_one_le_of_exists_span_singleton_eq_top
    {R : Type u} [CommRing R] (P : Ideal R) [P.IsPrime]
    {S : Type u} [CommRing S] [Algebra R S] [IsLocalization.AtPrime S P]
    {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
    {Ms : Type u} [AddCommGroup Ms] [Module R Ms] [Module S Ms] [IsScalarTower R S Ms]
    (f : M →ₗ[R] Ms) [IsLocalizedModule P.primeCompl f]
    (hcyc : ∃ m : Ms, Submodule.span S {m} = ⊤) :
    ¬ fittingIdeal (R := R) (M := M) (1 : ℤ) ≤ P := by
  intro hle
  obtain ⟨m, hm⟩ := hcyc
  have : Module.Finite S Ms := ⟨⟨{m}, by simpa using hm⟩⟩
  have h1 : fittingIdeal (R := S) (M := Ms) ((1 : ℕ) : ℤ) = ⊤ :=
    (fittingIdeal_basic_properties.{u,u,u,u} (R := S) (M := Ms)).1 1
      ⟨fun _ => m, by simpa [Set.range_const] using hm⟩
  rw [fittingIdeal_eq_map_of_localizedModule P f 1] at h1
  have hP : (Ideal.map (algebraMap R S) P).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint P.primeCompl S P ‹_› disjoint_compl_left
  apply hP.ne_top
  rw [eq_top_iff, ← h1]
  exact Ideal.map_mono (by exact_mod_cast hle)

/-- A one-dimensional integrally closed noetherian local domain is a DVR. -/
private theorem isDiscreteValuationRing_of_ringKrullDim_eq_one {S : Type*} [CommRing S] [IsDomain S]
    [IsLocalRing S] [IsNoetherianRing S] [IsIntegrallyClosed S] (h : ringKrullDim S = 1) :
    IsDiscreteValuationRing S := by
  have hnf : ¬ IsField S := (ringKrullDim_eq_one_iff_of_isLocalRing_isDomain.mp h).1
  have hk : Ring.KrullDimLE 1 S := Ring.krullDimLE_iff.mpr h.le
  have : Ring.DimensionLEOne S :=
    ⟨fun hp hpr => Ring.krullDimLE_one_iff_of_noZeroDivisors.mp hk _ hp hpr⟩
  have hd : IsDedekindDomain S := { }
  exact ((IsDiscreteValuationRing.TFAE S hnf).out 3 1).mp hd

/-- A finite torsion-free module over a DVR whose localization has rank one is cyclic. -/
private theorem exists_span_singleton_eq_top_of_finrank_localization_eq_one
    {S : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    (T : Submonoid S) {K : Type*} [CommRing K] [Nontrivial K] [Algebra S K] [IsLocalization T K]
    {Ms : Type*} [AddCommGroup Ms] [Module S Ms] [Module.Finite S Ms] [NoZeroSMulDivisors S Ms]
    {Mg : Type*} [AddCommGroup Mg] [Module S Mg] [Module K Mg] [IsScalarTower S K Mg]
    (g : Ms →ₗ[S] Mg) [IsLocalizedModule T g]
    (hrank : Module.finrank K Mg = 1) :
    ∃ m : Ms, Submodule.span S {m} = ⊤ := by
  classical
  let ι := Module.Free.ChooseBasisIndex S Ms
  let b := Module.Free.chooseBasis S Ms
  have : Finite ι := Module.Finite.finite_basis b
  have : Fintype ι := Fintype.ofFinite ι
  let b' := b.ofIsLocalizedModule K T g
  obtain ⟨i, hi⟩ := Fintype.card_eq_one_iff.mp <| by
    rw [← Module.finrank_eq_card_basis b', hrank]
  refine ⟨b i, ?_⟩
  have : Set.range b = {b i} := by
    ext x
    exact ⟨by rintro ⟨j, rfl⟩; rw [hi j]; rfl, fun h => ⟨i, h.symm⟩⟩
  rw [← this]
  exact b.span_eq

/-- The stalk of a torsion-free module on an integral scheme has no zero-divisor action. -/
private theorem noZeroSMulDivisors_stalk {X : Scheme.{u}} [IsIntegral X]
    (M : X.Modules) (hM : IsTorsionFree M) (x : X) :
    let := Stacks.ModuleStalkSpecialization.stalkModule M x
    NoZeroSMulDivisors (X.presheaf.stalk x) (M.presheaf.stalk x) := by
  let := Stacks.ModuleStalkSpecialization.stalkModule M x
  refine ⟨fun {r m} h => ?_⟩
  by_contra hne
  push Not at hne
  obtain ⟨hr, hm⟩ := hne
  obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.presheaf m
  obtain ⟨W, hWU, hxW, a, ha, has⟩ :=
    Stacks.AlgebraicGeometry.ReflexiveModules.exists_annihilator_of_isTorsionSection hxU
      ⟨r, hr, h⟩
  have ha0 : a ≠ 0 := fun h0 => ha (by rw [h0, map_zero])
  have hWs : IsTorsionSection M (M.presheaf.map (homOfLE hWU).op s) := by
    intro y hy
    refine ⟨X.presheaf.germ W y hy a, fun h0 => ha0 ?_, ?_⟩
    · exact germ_injective_of_isIntegral (X := X) y hy (by rw [h0, map_zero])
    · have := Stacks.ModuleStalkSpecialization.germ_smul M hy a (M.presheaf.map (homOfLE hWU).op s)
      rw [← this, has, map_zero]
  have hz := hM W _ hWs
  apply hm
  rw [← M.presheaf.germ_res_apply (homOfLE hWU) x hxW, hz, map_zero]

private theorem mem_zeroLocus_iff_le {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U)
    {x : X} (hx : x ∈ U) (I : Ideal Γ(X, U)) :
    x ∈ X.zeroLocus (U := U) (I : Set Γ(X, U)) ↔ I ≤ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
  rw [Scheme.mem_zeroLocus_iff]
  have key : ∀ f : Γ(X, U), x ∈ X.basicOpen f ↔ f ∉ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
    intro f
    have h3 : x ∈ X.basicOpen f ↔ hU.primeIdealOf ⟨x, hx⟩ ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen f := by
      change x ∈ X.basicOpen f ↔ hU.fromSpec (hU.primeIdealOf ⟨x, hx⟩) ∈ X.basicOpen f
      rw [hU.fromSpec_primeIdealOf ⟨x, hx⟩]
    rw [h3, hU.fromSpec_preimage_basicOpen f]
    rfl
  simp only [key, SetLike.mem_coe, not_not]
  exact Iff.rfl

/-- If the stalk of `M` at `x` is cyclic, then `x` is not in the support of `Fitt₁ M`. -/
private theorem notMem_support_fittingIdeal_one_of_cyclic_stalk
    {X : Scheme.{0}} (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] (x : X)
    (hcyc : ∃ m : M.presheaf.stalk x, Submodule.span (X.presheaf.stalk x) {m} = ⊤) :
    x ∉ (fittingIdeal M (1 : ℤ)).support := by
  intro hxs
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hPprime : (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.IsPrime :=
    (hU.primeIdealOf ⟨x, hxU⟩).isPrime
  let : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hxU).hom.toAlgebra
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨x, hxU⟩
  let := Stacks.ModuleStalkSpecialization.stalkModule M x
  let := Stacks.ModuleStalkSpecialization.sectionsStalkModule M hxU
  have hST := Stacks.ModuleStalkSpecialization.isScalarTower_sectionsStalk M hxU
  have hM' := Stacks.ModuleStalkSpecialization.isLocalizedModule_germₗ M hU hxU
  have : Module.Finite Γ(X, U) Γ(M, U) := moduleFinite_sections_on_affine M U hU
  have hnle := not_fittingIdeal_one_le_of_exists_span_singleton_eq_top
    (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
    (S := X.presheaf.stalk x) (Ms := M.presheaf.stalk x)
    (Stacks.ModuleStalkSpecialization.germₗ M hxU) hcyc
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨U, hU⟩) hxU,
    mem_zeroLocus_iff_le hU hxU, fittingIdeal_ideal M 1 ⟨U, hU⟩] at hxs
  exact hnle hxs

/-- At a codimension-one point of a normal variety, the first Fitting ideal of a torsion-free
module of generic rank one is the unit ideal. -/
private theorem notMem_support_fittingIdeal_one_of_ringKrullDim_eq_one
    {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) (hX : Mori.IsNormalVariety ℂ sX) [IsIntegral X]
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] (hM : IsTorsionFree M)
    (hrank : Module.finrank (X.presheaf.stalk (genericPoint X))
      (M.presheaf.stalk (genericPoint X)) = 1) :
    ∀ x : X, ringKrullDim (X.presheaf.stalk x) = 1 →
        x ∉ (fittingIdeal M (1 : ℤ)).support := by
  intro x hx
  have := hX.1
  have := hX.2
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsIntegrallyClosed (X.presheaf.stalk x) := (hX.2).stalk_normal x
  have hDVR : IsDiscreteValuationRing (X.presheaf.stalk x) :=
    isDiscreteValuationRing_of_ringKrullDim_eq_one hx
  refine notMem_support_fittingIdeal_one_of_cyclic_stalk M x ?_
  have hη : genericPoint X ⤳ x := genericPoint_specializes x
  let : Algebra (X.presheaf.stalk x) (X.presheaf.stalk (genericPoint X)) :=
    (X.presheaf.stalkSpecializes hη).hom.toAlgebra
  let := Stacks.ModuleStalkSpecialization.stalkModule M (genericPoint X)
  let := Stacks.ModuleStalkSpecialization.stalkSpecializesModule M hη
  have hlocK := Stacks.StalkSpecialization.isLocalization_atPrime_stalkSpecializes hη
  have hlocM := Stacks.ModuleStalkSpecialization.isLocalizedModule_atPrime_stalkSpecializes M hη
  have hTower : IsScalarTower (X.presheaf.stalk x) (X.presheaf.stalk (genericPoint X))
      (M.presheaf.stalk (genericPoint X)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : NoZeroSMulDivisors (X.presheaf.stalk x) (M.presheaf.stalk x) :=
    noZeroSMulDivisors_stalk M hM x
  have : Module.Finite (X.presheaf.stalk x) (M.presheaf.stalk x) :=
    _root_.SheafOfModules.finite_stalk X.sheaf M x
  exact exists_span_singleton_eq_top_of_finrank_localization_eq_one
    ((IsLocalRing.maximalIdeal (X.presheaf.stalk (genericPoint X))).under
      (X.presheaf.stalk x)).primeCompl
    (Stacks.ModuleStalkSpecialization.stalkSpecializesₗ M hη) hrank

/-- The first Fitting ideal of a module of generic rank one is nonzero. -/
private theorem fittingIdeal_one_ne_bot {X : Scheme.{0}} [IsIntegral X]
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (hrank : Module.finrank (X.presheaf.stalk (genericPoint X))
      (M.presheaf.stalk (genericPoint X)) = 1) :
    fittingIdeal M (1 : ℤ) ≠ ⊥ := by
  intro h
  refine notMem_support_fittingIdeal_one_of_cyclic_stalk M (genericPoint X) ?_ ?_
  · let : Field (X.presheaf.stalk (genericPoint X)) := inferInstanceAs (Field X.functionField)
    obtain ⟨v, -, hv⟩ := finrank_eq_one_iff'.mp hrank
    exact ⟨v, Submodule.eq_top_iff'.2 fun w => Submodule.mem_span_singleton.2 (hv w)⟩
  · rw [h]
    exact Set.mem_univ _

section Alg

variable {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N] [Module.Finite R N]

/-- The relation matrix of the presentation of `N` by the kernel of `f`. -/
private def relMat {n : ℕ} (f : (Fin n → R) →ₗ[R] N) : Matrix (Fin n) (LinearMap.ker f) R :=
  fun i j => (j : Fin n → R) i

private lemma fittingIdeal_eq_minorIdeal_relMat {n : ℕ} (f : (Fin n → R) →ₗ[R] N)
    (hf : Function.Surjective f) (k : ℕ) :
    fittingIdeal (R := R) (M := N) (k : ℤ) = minorIdeal (relMat f) (n - k) := by
  have hker : Submodule.span R
      (Set.range (fun j : LinearMap.ker f => fun i : Fin n => relMat f i j)) = LinearMap.ker f :=
    le_antisymm (Submodule.span_le.2 (Set.range_subset_iff.2 fun j => j.2))
      fun x hx => Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩
  exact fittingIdeal_eq_minorIdeal_of_presentation (relMat f) k
    ((Submodule.quotEquivOfEq _ _ hker).trans (f.quotKerEquivOfSurjective hf))

end Alg

private theorem exists_mem_eq_unit_mul_of_span_eq_span_singleton
    {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R] (S : Set R) (t : R) (ht : t ≠ 0)
    (hS : Ideal.span S = Ideal.span {t}) : ∃ x ∈ S, ∃ u : Rˣ, x = u * t := by
  by_contra hcon
  push Not at hcon
  have hle : Ideal.span S ≤ IsLocalRing.maximalIdeal R * Ideal.span {t} := by
    refine Ideal.span_le.2 fun x hx => ?_
    have hx' : x ∈ Ideal.span {t} := hS ▸ Ideal.subset_span hx
    obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.1 hx'
    have : s ∈ IsLocalRing.maximalIdeal R := by
      by_contra hs
      exact hcon (s * t) hx (IsLocalRing.notMem_maximalIdeal.1 hs).unit
        (by simp)
    exact Ideal.mem_mul_span_singleton.2 ⟨s, this, rfl⟩
  have htm : t ∈ IsLocalRing.maximalIdeal R * Ideal.span {t} :=
    hle (hS ▸ Ideal.mem_span_singleton_self t)
  obtain ⟨z, hz, hzt⟩ := Ideal.mem_mul_span_singleton.1 htm
  have : (1 - z) * t = 0 := by
    rw [sub_mul, hzt]
    ring
  rcases mul_eq_zero.1 this with h | h
  · exact IsLocalRing.notMem_maximalIdeal.2 isUnit_one (by rwa [← sub_eq_zero.1 h] at hz)
  · exact ht h

section Main

open Matrix in
/-- If the first `m` columns of a square matrix `C` lie in `K` and replacing its last column by
`x` gives a singular matrix, then `C.det • x ∈ K` (Cramer's rule). -/
theorem det_smul_mem_of_det_updateCol_last_eq_zero {R : Type*} [CommRing R] {m : ℕ}
    (C : Matrix (Fin (m + 1)) (Fin (m + 1)) R) (K : Submodule R (Fin (m + 1) → R))
    (hC : ∀ k : Fin m, (fun i => C i k.castSucc) ∈ K) (x : Fin (m + 1) → R)
    (hx : (C.updateCol (Fin.last m) x).det = 0) : C.det • x ∈ K := by
  have hyl : (adjugate C *ᵥ x) (Fin.last m) = 0 := by
    rw [← cramer_eq_adjugate_mulVec, cramer_apply, hx]
  have hmv : C *ᵥ (adjugate C *ᵥ x) = C.det • x := by
    rw [mulVec_mulVec, mul_adjugate, smul_mulVec, one_mulVec]
  rw [← hmv]
  generalize adjugate C *ᵥ x = y at hyl ⊢
  have : C *ᵥ y = ∑ k : Fin m, y k.castSucc • fun i => C i k.castSucc := by
    ext i
    simp [mulVec, dotProduct, Fin.sum_univ_castSucc, hyl, mul_comm]
  rw [this]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hC k)

/-- An injective map `Fin m → Fin (m + 1)` misses some `j0` and factors as `j0.succAbove`
after a permutation of `Fin m`. -/
theorem exists_perm_succAbove_eq_of_injective {m : ℕ} {φ : Fin m → Fin (m + 1)}
    (hφ : Function.Injective φ) :
    ∃ (j0 : Fin (m + 1)) (σ : Equiv.Perm (Fin m)), ∀ i, j0.succAbove (σ i) = φ i := by
  obtain ⟨j0, hj0⟩ : ∃ j0, j0 ∉ Set.range φ := by
    by_contra hcon
    push Not at hcon
    have := Fintype.card_le_of_surjective φ hcon
    simp at this
  have hex : ∀ i, ∃ k, j0.succAbove k = φ i := fun i =>
    Fin.exists_succAbove_eq (fun h => hj0 ⟨i, h⟩)
  choose σ hσ using hex
  refine ⟨j0, Equiv.ofBijective σ (Finite.injective_iff_bijective.1 fun i j hij => ?_), hσ⟩
  apply hφ
  rw [← hσ i, ← hσ j, hij]

open Matrix in
/-- If the first `m` columns of a square matrix `C` are the columns `g` of `A`, and `φ` factors
as `j0.succAbove` after a permutation, then replacing the last column of `C` by the `j0`-th
basis vector gives, up to a unit, the minor of `A` on the rows `φ` and columns `g`. -/
theorem exists_unit_det_updateCol_last_single_eq {R : Type*} [CommRing R] {m : ℕ} {κ : Type*}
    (A : Matrix (Fin (m + 1)) κ R) (g : Fin m → κ) {φ : Fin m → Fin (m + 1)}
    {j0 : Fin (m + 1)} {σ : Equiv.Perm (Fin m)} (hσ : ∀ i, j0.succAbove (σ i) = φ i)
    (C : Matrix (Fin (m + 1)) (Fin (m + 1)) R) (hC : ∀ i (k : Fin m), C i k.castSucc = A i (g k)) :
    ∃ w : Rˣ, (C.updateCol (Fin.last m) (Pi.single j0 1)).det = w * (A.submatrix φ g).det := by
  have h1 : (C.updateCol (Fin.last m) (Pi.single j0 1)).det =
      (-1) ^ (j0 + Fin.last m : ℕ) * (A.submatrix j0.succAbove g).det := by
    rw [← cramer_apply, cramer_eq_adjugate_mulVec, mulVec_single_one]
    change C.adjugate (Fin.last m) j0 = _
    rw [adjugate_fin_succ_eq_det_submatrix]
    congr 2
    ext i k
    simp [hC]
  have h2 : ((σ.sign : ℤ) : R) * (A.submatrix j0.succAbove g).det = (A.submatrix φ g).det := by
    have : A.submatrix φ g = (A.submatrix j0.succAbove g).submatrix σ id := by
      ext i k
      simp [hσ]
    rw [this, det_permute]
  have hss : ((σ.sign : ℤ) : R) * ((σ.sign : ℤ) : R) = 1 := by
    exact_mod_cast congrArg (fun z : ℤˣ => ((z : ℤ) : R)) (Int.units_mul_self σ.sign)
  have hunit : IsUnit ((-1 : R) ^ (j0 + Fin.last m : ℕ) * ((σ.sign : ℤ) : R)) :=
    (IsUnit.pow _ isUnit_one.neg).mul (isUnit_iff_exists_inv.2 ⟨_, hss⟩)
  refine ⟨hunit.unit, ?_⟩
  rw [h1, IsUnit.unit_spec]
  linear_combination ((-1 : R) ^ (j0 + Fin.last m : ℕ) * ((σ.sign : ℤ) : R)) * h2 -
    ((-1 : R) ^ (j0 + Fin.last m : ℕ) * (A.submatrix j0.succAbove g).det) * hss

open Matrix in
/-- If the last row of the adjugate of `C` lies in `(t)`, then `t` times some linear form is the
determinant of `C` with its last column replaced. -/
theorem exists_linearMap_mul_eq_det_updateCol_last {R : Type*} [CommRing R] {m : ℕ}
    (C : Matrix (Fin (m + 1)) (Fin (m + 1)) R) (t : R)
    (h : ∀ j, C.adjugate (Fin.last m) j ∈ Ideal.span {t}) :
    ∃ q : (Fin (m + 1) → R) →ₗ[R] R, ∀ x, t * q x = (C.updateCol (Fin.last m) x).det := by
  choose c hc using fun j => Ideal.mem_span_singleton'.1 (h j)
  let q : (Fin (m + 1) → R) →ₗ[R] R := ∑ j, c j • (LinearMap.proj j : (Fin (m + 1) → R) →ₗ[R] R)
  have hq : ∀ x, q x = ∑ j, c j * x j := fun x => by simp [q]
  refine ⟨q, fun x => ?_⟩
  rw [← cramer_apply, cramer_eq_adjugate_mulVec, mulVec, dotProduct, hq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← hc j]
  ring

open Matrix in
/-- If the `(m + 1)`-minors of a matrix `A` with `m + 1` rows over a local domain vanish and its
`m`-minors generate `(t)` with `t ≠ 0`, then some surjective linear form vanishes on the columns
of `A`, and every vector it kills has a nonzero multiple in the column span of `A`. -/
theorem exists_surjective_linearMap_of_span_minors_eq_span_singleton {R : Type*} [CommRing R]
    [IsDomain R] [IsLocalRing R] {m : ℕ} {κ : Type*} (A : Matrix (Fin (m + 1)) κ R) (t : R)
    (ht : t ≠ 0)
    (h0 : ∀ (g : Fin (m + 1) → Fin (m + 1)) (g' : Fin (m + 1) → κ), (A.submatrix g g').det = 0)
    (h1 : Ideal.span {x : R | ∃ (g : Fin m → Fin (m + 1)) (g' : Fin m → κ),
      x = (A.submatrix g g').det} = Ideal.span {t}) :
    ∃ q : (Fin (m + 1) → R) →ₗ[R] R, Function.Surjective q ∧ (∀ k, q (fun i => A i k) = 0) ∧
      ∀ x, q x = 0 → ∃ r : R, r ≠ 0 ∧ r • x ∈ Submodule.span R (Set.range fun k i => A i k) := by
  classical
  obtain ⟨x, ⟨φ, g, rfl⟩, u, hu⟩ := exists_mem_eq_unit_mul_of_span_eq_span_singleton _ t ht h1
  have hdetne : (A.submatrix φ g).det ≠ 0 := hu ▸ mul_ne_zero u.ne_zero ht
  have hφinj : Function.Injective φ := fun i j hij =>
    Classical.byContradiction fun hne => hdetne (det_zero_of_row_eq hne (by ext k; simp [hij]))
  let B : (Fin (m + 1) → R) → Matrix (Fin (m + 1)) (Fin (m + 1)) R := fun z =>
    Matrix.of fun i k => Fin.lastCases (motive := fun _ => R) (z i) (fun k' => A i (g k')) k
  have hB : ∀ z, B z = (B 0).updateCol (Fin.last m) z := by
    intro z
    ext i k
    refine Fin.lastCases ?_ (fun k' => ?_) k
    · simp [B]
    · simp [B, updateCol_ne (Fin.castSucc_lt_last k').ne]
  have hadj : ∀ j, (B 0).adjugate (Fin.last m) j ∈ Ideal.span {t} := by
    intro j
    rw [adjugate_fin_succ_eq_det_submatrix]
    refine Ideal.mul_mem_left _ _ ?_
    rw [← h1]
    refine Ideal.subset_span ⟨j.succAbove, g, ?_⟩
    congr 1
    ext i k
    simp [B]
  obtain ⟨q', hD'⟩ := exists_linearMap_mul_eq_det_updateCol_last (B 0) t hadj
  have hD : ∀ x, t * q' x = (B x).det := fun x => by rw [hB x]; exact hD' x
  have hker : ∀ k, q' (fun i => A i k) = 0 := by
    refine fun k => (mul_eq_zero.1 ((hD _).trans ?_)).resolve_left ht
    have : (B fun i => A i k) = A.submatrix id (Fin.lastCases (motive := fun _ => κ) k g) := by
      ext i k'
      refine Fin.lastCases ?_ (fun k'' => ?_) k' <;> simp [B]
    rw [this]
    exact h0 id _
  obtain ⟨j0, σe, hσ⟩ := exists_perm_succAbove_eq_of_injective hφinj
  obtain ⟨w, hw⟩ : ∃ w : Rˣ, (B (Pi.single j0 1)).det = w * t := by
    obtain ⟨w, hw⟩ := exists_unit_det_updateCol_last_single_eq A g hσ (B 0) fun i k => by simp [B]
    exact ⟨w * u, by rw [hB, hw, hu, Units.val_mul, mul_assoc]⟩
  have hq'z0 : q' (Pi.single j0 1) = w := mul_left_cancel₀ ht (by rw [hD, hw, mul_comm])
  refine ⟨q', fun r => ⟨(r * ((w⁻¹ : Rˣ) : R)) • Pi.single j0 1, ?_⟩, hker, fun x hx => ?_⟩
  · rw [map_smul, hq'z0, smul_eq_mul, mul_assoc, Units.inv_mul, mul_one]
  refine ⟨(B (Pi.single j0 1)).det, by rw [hw]; exact mul_ne_zero w.ne_zero ht, ?_⟩
  refine det_smul_mem_of_det_updateCol_last_eq_zero _ _ (fun k' => ?_) x ?_
  · refine Submodule.subset_span ⟨g k', ?_⟩
    ext i
    simp [B]
  · have hCx : (B (Pi.single j0 1)).updateCol (Fin.last m) x = B x := by
      rw [hB x, hB (Pi.single j0 1)]
      ext i k
      by_cases hk : k = Fin.last m <;> simp [updateCol_apply, hk]
    rw [hCx, ← hD x, hx, mul_zero]

open Matrix in
private theorem exists_surjective_linearMap_ker_eq_torsion_of_fittingIdeal
    {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    {N : Type*} [AddCommGroup N] [Module R N] [Module.Finite R N] (t : R) (ht : t ≠ 0)
    (h0 : fittingIdeal (R := R) (M := N) (0 : ℤ) = ⊥)
    (h1 : fittingIdeal (R := R) (M := N) (1 : ℤ) = Ideal.span {t}) :
    ∃ q : N →ₗ[R] R, Function.Surjective q ∧
      ∀ m, q m = 0 ↔ ∃ r : R, r ≠ 0 ∧ r • m = 0 := by
  classical
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R N
  have e0 := fittingIdeal_eq_minorIdeal_relMat f hf 0
  have e1 := fittingIdeal_eq_minorIdeal_relMat f hf 1
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
    rcases n with _ | m
    · exfalso
      simp only [Nat.cast_zero, Nat.sub_zero] at e0
      rw [h0, minorIdeal_zero] at e0
      exact bot_ne_top e0
    · exact ⟨m, rfl⟩
  simp only [Nat.cast_zero, Nat.sub_zero, Nat.cast_one, Nat.add_sub_cancel] at e0 e1
  rw [h0] at e0
  rw [h1] at e1
  set A := relMat f
  have hmin0 : ∀ (g : Fin (m + 1) → Fin (m + 1)) (g' : Fin (m + 1) → LinearMap.ker f),
      (A.submatrix g g').det = 0 := by
    intro g g'
    have : (A.submatrix g g').det ∈ minorIdeal A (m + 1) :=
      Ideal.subset_span ⟨g, g', rfl⟩
    rw [← e0] at this
    simpa using this
  have hS : Ideal.span {x : R | ∃ (g : Fin m → Fin (m + 1)) (g' : Fin m → LinearMap.ker f),
      x = (A.submatrix g g').det} = Ideal.span {t} := by
    rw [e1]
    rfl
  obtain ⟨q', hq's, hq'A, hq'x⟩ :=
    exists_surjective_linearMap_of_span_minors_eq_span_singleton A t ht hmin0 hS
  have hker' : LinearMap.ker f ≤ LinearMap.ker q' := fun w hw => hq'A ⟨w, hw⟩
  have hspan : Submodule.span R (Set.range fun k i => A i k) ≤ LinearMap.ker f :=
    Submodule.span_le.2 (Set.range_subset_iff.2 fun k => k.2)
  let q : N →ₗ[R] R := ((LinearMap.ker f).liftQ q' hker') ∘ₗ
    (f.quotKerEquivOfSurjective hf).symm.toLinearMap
  have hqf : ∀ x, q (f x) = q' x := by
    intro x
    have : (f.quotKerEquivOfSurjective hf).symm (f x) = Submodule.Quotient.mk x := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    simp [q, this]
  refine ⟨q, fun r => ?_, fun n' => ?_⟩
  · obtain ⟨y, hy⟩ := hq's r
    exact ⟨f y, by rw [hqf, hy]⟩
  obtain ⟨x, rfl⟩ := hf n'
  rw [hqf]
  refine ⟨fun hx => ?_, fun ⟨r, hr, hrx⟩ => ?_⟩
  · obtain ⟨r, hr, hrx⟩ := hq'x x hx
    exact ⟨r, hr, by rw [← map_smul]; exact hspan hrx⟩
  · have : r * q (f x) = 0 := by rw [← smul_eq_mul, ← map_smul, hrx, map_zero]
    rw [hqf] at this
    exact (mul_eq_zero.1 this).resolve_left hr

end Main

private theorem fittingIdeal_stalk_eq_map {X : Scheme.{0}} (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] {U : X.Opens} (hU : IsAffineOpen U) {x : X}
    (hx : x ∈ U) [Module.Finite (X.presheaf.stalk x) (F.presheaf.stalk x)]
    [Module.Finite Γ(X, U) Γ(F, U)] (k : ℕ) :
    fittingIdeal (R := X.presheaf.stalk x) (M := F.presheaf.stalk x) (k : ℤ) =
      Ideal.map (X.presheaf.germ U x hx).hom
        (fittingIdeal (R := Γ(X, U)) (M := Γ(F, U)) (k : ℤ)) := by
  have hPprime : (hU.primeIdealOf ⟨x, hx⟩).asIdeal.IsPrime :=
    (hU.primeIdealOf ⟨x, hx⟩).isPrime
  let : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toAlgebra
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hx⟩).asIdeal :=
    hU.isLocalization_stalk ⟨x, hx⟩
  let := Stacks.ModuleStalkSpecialization.stalkModule F x
  let := Stacks.ModuleStalkSpecialization.sectionsStalkModule F hx
  have hST := Stacks.ModuleStalkSpecialization.isScalarTower_sectionsStalk F hx
  have hM' := Stacks.ModuleStalkSpecialization.isLocalizedModule_germₗ F hU hx
  exact fittingIdeal_eq_map_of_localizedModule (hU.primeIdealOf ⟨x, hx⟩).asIdeal
    (Stacks.ModuleStalkSpecialization.germₗ F hx) k

private theorem fittingIdeal_zero_eq_bot {X : Scheme.{0}} [IsIntegral X]
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (hrank : Module.finrank (X.presheaf.stalk (genericPoint X))
      (M.presheaf.stalk (genericPoint X)) = 1) :
    fittingIdeal M (0 : ℤ) = ⊥ := by
  refine Scheme.IdealSheafData.ext ?_
  funext U
  change (fittingIdeal M (0 : ℤ)).ideal U = ⊥
  have hfin : Module.Finite Γ(X, U.1) Γ(M, U.1) := moduleFinite_sections_on_affine M U.1 U.2
  rw [fittingIdeal_ideal M 0 U]
  by_cases hne : (U.1 : Set X).Nonempty
  · have hη : genericPoint X ∈ U.1 :=
      (genericPoint_spec X).mem_open_set_iff U.1.isOpen |>.2 (by simpa using hne)
    have hfinη : Module.Finite (X.presheaf.stalk (genericPoint X))
        (M.presheaf.stalk (genericPoint X)) :=
      _root_.SheafOfModules.finite_stalk X.sheaf M _
    have h := fittingIdeal_stalk_eq_map M U.2 hη 0
    have h0 : fittingIdeal (R := X.presheaf.stalk (genericPoint X))
        (M := M.presheaf.stalk (genericPoint X)) ((0 : ℕ) : ℤ) = ⊥ := by
      let : Field (X.presheaf.stalk (genericPoint X)) := inferInstanceAs (Field X.functionField)
      have hle := (fittingIdeal_basic_properties.{0, 0, 0, 0}
        (R := X.presheaf.stalk (genericPoint X))
        (M := M.presheaf.stalk (genericPoint X))).2.2.2.2.2.1
      have hnt : Nontrivial (M.presheaf.stalk (genericPoint X)) :=
        Module.nontrivial_of_finrank_pos (R := X.presheaf.stalk (genericPoint X)) (by omega)
      have hann : Module.annihilator (X.presheaf.stalk (genericPoint X))
          (M.presheaf.stalk (genericPoint X)) = ⊥ :=
        (Ideal.eq_bot_or_top _).resolve_right fun h =>
          not_subsingleton _ (Module.annihilator_eq_top_iff.1 h)
      exact le_bot_iff.1 (hle.trans hann.le)
    rw [h0] at h
    exact (Ideal.map_eq_bot_iff_of_injective (germ_injective_of_isIntegral (X := X) _ hη)).1 h.symm
  · have hbot : U.1 = ⊥ := by
      rwa [← Opens.not_nonempty_iff_eq_bot]
    have : Subsingleton Γ(X, U.1) :=
      CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hbot)
    exact Subsingleton.elim _ _

section Cok

open Limits Opposite
open Stacks.SheafOfModules.FlatShortExact

/-- Injectivity, exactness and surjectivity of a pair of maps of additive monoids transfer
along a ladder of additive equivalences. -/
theorem injective_exact_surjective_of_ladder_addEquiv {A₁ A₂ A₃ B₁ B₂ B₃ : Type*}
    [AddCommMonoid A₁] [AddCommMonoid A₂] [AddCommMonoid A₃]
    [AddCommMonoid B₁] [AddCommMonoid B₂] [AddCommMonoid B₃]
    (f : A₁ →+ A₂) (g : A₂ →+ A₃) (f' : B₁ →+ B₂) (g' : B₂ →+ B₃)
    (e₁ : A₁ ≃+ B₁) (e₂ : A₂ ≃+ B₂) (e₃ : A₃ ≃+ B₃)
    (sq1 : f'.comp (e₁ : A₁ →+ B₁) = (e₂ : A₂ →+ B₂).comp f)
    (sq2 : g'.comp (e₂ : A₂ →+ B₂) = (e₃ : A₃ →+ B₃).comp g)
    (h : Function.Injective f' ∧ Function.Exact f' g' ∧ Function.Surjective g') :
    Function.Injective f ∧ Function.Exact f g ∧ Function.Surjective g := by
  obtain ⟨hf, hex, hg⟩ := h
  have hpt1 : ∀ s, e₂ (f s) = f' (e₁ s) := fun s => (DFunLike.congr_fun sq1 s).symm
  have hpt2 : ∀ s, e₃ (g s) = g' (e₂ s) := fun s => (DFunLike.congr_fun sq2 s).symm
  refine ⟨fun a b hab => e₁.injective (hf (by rw [← hpt1, ← hpt1, hab])),
    (Function.Exact.iff_of_ladder_addEquiv e₁ e₂ e₃ sq1 sq2).mp hex, fun c => ?_⟩
  obtain ⟨b, hb⟩ := hg (e₃ c)
  exact ⟨e₂.symm b, e₃.injective (by rw [hpt2, AddEquiv.apply_symm_apply, hb])⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem preservesFiniteLimits_and_colimits_stalkF
    {X : AlgebraicGeometry.RingedSpace.{u, u}} (x : X.carrier) :
    PreservesFiniteLimits (stalkF (X := X) x) ∧ PreservesFiniteColimits (stalkF (X := X) x) ∧
      (stalkF (X := X) x).PreservesZeroMorphisms := by
  have : (SheafOfModules.toSheaf.{u} (structureSheafRing X)).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive _
  have i1 : PreservesFiniteLimits
      (TopCat.Sheaf.forget AddCommGrpCat.{u} X.carrier ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) :=
    inferInstance
  have hpzm_inner : (TopCat.Sheaf.forget AddCommGrpCat.{u} X.carrier ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).PreservesZeroMorphisms := inferInstance
  have hpl : PreservesFiniteLimits (stalkF x) := by
    unfold stalkF
    exact comp_preservesFiniteLimits _ _
  -- Both preservation facts are fed explicitly through `compPFC`.
  have hpc : PreservesFiniteColimits (stalkF x) := by
    unfold stalkF
    exact compPFC (SheafOfModules.toSheaf (structureSheafRing X))
      (TopCat.Sheaf.forget AddCommGrpCat.{u} X.carrier ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)
      (toSheafColim X) (forgetStalkColim x)
  -- Both functors are given explicitly so that no instance is re-folded.
  have : (stalkF x).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_comp (SheafOfModules.toSheaf (structureSheafRing X))
      (TopCat.Sheaf.forget AddCommGrpCat.{u} X.carrier ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)
  exact ⟨hpl, hpc, this⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem injective_exact_surjective_stalkLinearMap_of_shortExact
    {X : AlgebraicGeometry.RingedSpace.{u, u}}
    (S : ShortComplex (SheafOfModules (structureSheafRing X)))
    (hS : S.ShortExact) (x : X.carrier) :
    letI := stalkModule S.X₁ x; letI := stalkModule S.X₂ x; letI := stalkModule S.X₃ x
    Function.Injective (stalkLinearMap S.f x) ∧
      Function.Exact (stalkLinearMap S.f x) (stalkLinearMap S.g x) ∧
      Function.Surjective (stalkLinearMap S.g x) := by
  let := stalkModule S.X₁ x
  let := stalkModule S.X₂ x
  let := stalkModule S.X₃ x
  obtain ⟨hpl, hpc, _⟩ := preservesFiniteLimits_and_colimits_stalkF (X := X) x
  have hUSE : (S.map (stalkF x)).ShortExact := hS.map_of_exact (stalkF x)
  -- `abStalk S.Xᵢ x` and `(stalkF x).obj S.Xᵢ` are equal by unfolding `stalkF`; the
  -- comparison goes through the `AddEquiv`s of `eqToIso` rather than a defeq `exact`.
  have hobj : ∀ F, abStalk F x = (stalkF x).obj F := fun _ => by
    unfold stalkF abStalk toAbPresheaf
    rfl
  let e₁ : abStalk S.X₁ x ≃+ (S.map (stalkF x)).X₁ :=
    (eqToIso (hobj S.X₁)).addCommGroupIsoToAddEquiv
  let e₂ : abStalk S.X₂ x ≃+ (S.map (stalkF x)).X₂ :=
    (eqToIso (hobj S.X₂)).addCommGroupIsoToAddEquiv
  let e₃ : abStalk S.X₃ x ≃+ (S.map (stalkF x)).X₃ :=
    (eqToIso (hobj S.X₃)).addCommGroupIsoToAddEquiv
  -- The equivalences conjugate `(S.map (stalkF x)).f/.g` to `stalkLinearMap S.f/.g x`.
  have sq1 : ((S.map (stalkF x)).f.hom).comp (e₁ : abStalk S.X₁ x →+ _)
      = (e₂ : abStalk S.X₂ x →+ _).comp (stalkLinearMap S.f x).toAddMonoidHom := by
    ext s
    simp only [e₁, e₂, Iso.addCommGroupIsoToAddEquiv, AddMonoidHom.coe_comp,
      Function.comp_apply, eqToIso.hom]
    rfl
  have sq2 : ((S.map (stalkF x)).g.hom).comp (e₂ : abStalk S.X₂ x →+ _)
      = (e₃ : abStalk S.X₃ x →+ _).comp (stalkLinearMap S.g x).toAddMonoidHom := by
    ext s
    simp only [e₂, e₃, Iso.addCommGroupIsoToAddEquiv, AddMonoidHom.coe_comp,
      Function.comp_apply, eqToIso.hom]
    rfl
  exact injective_exact_surjective_of_ladder_addEquiv _ _ _ _ e₁ e₂ e₃ sq1 sq2
    ⟨(AddCommGrpCat.mono_iff_injective _).mp hUSE.mono_f,
      (ShortComplex.ab_exact_iff_function_exact (S.map (stalkF x))).mp hUSE.exact,
      (AddCommGrpCat.epi_iff_surjective _).mp hUSE.epi_g⟩

private theorem stalkLinearMap_germ {X : AlgebraicGeometry.RingedSpace.{0, 0}}
    {F G : SheafOfModules (structureSheafRing X)} (φ : F ⟶ G) {U : Opens X.carrier}
    {y : X.carrier} (hy : y ∈ U) (s : F.val.obj (op U)) :
    stalkLinearMap φ y (abGerm F U hy s) = abGerm G U hy (φ.val.app (op U) s) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply U y hy
    ((PresheafOfModules.toPresheaf (structureSheafRing X).obj).map φ.val) s

private theorem torsion_of_stalkLinearMap_torsionSubsheaf {T : Scheme.{0}} [IsIntegral T]
    (N : T.Modules) [N.IsQuasicoherent] (y : T)
    (k : abStalk (X := T.toRingedSpace) (Stacks.AlgebraicGeometry.TorsionSubsheaf.torsionSubsheaf
      N).toSheafOfModules y) :
    letI := stalkModule (X := T.toRingedSpace) N y
    ∃ r : T.presheaf.stalk y, r ≠ 0 ∧ r • stalkLinearMap (X := T.toRingedSpace)
      (Stacks.AlgebraicGeometry.TorsionSubsheaf.torsionSubsheaf N).ι y k = 0 := by
  letI := stalkModule (X := T.toRingedSpace) N y
  obtain ⟨V, hyV, k0, rfl⟩ := TopCat.Presheaf.exists_germ_eq
    (toAbPresheaf (X := T.toRingedSpace)
      (Stacks.AlgebraicGeometry.TorsionSubsheaf.torsionSubsheaf N).toSheafOfModules) k
  change ∃ r : T.presheaf.stalk y, r ≠ 0 ∧ r • stalkLinearMap (X := T.toRingedSpace)
      (Stacks.AlgebraicGeometry.TorsionSubsheaf.torsionSubsheaf N).ι y (abGerm _ V hyV k0) = 0
  obtain ⟨r, hr, hr0⟩ := k0.2 y hyV
  refine ⟨r, hr, ?_⟩
  erw [stalkLinearMap_germ]
  exact hr0

private theorem exists_stalkLinearMap_torsionSubsheaf_eq {T : Scheme.{0}} [IsIntegral T]
    (N : T.Modules) [N.IsQuasicoherent] (y : T) (m : abStalk (X := T.toRingedSpace) N y) :
    letI := stalkModule (X := T.toRingedSpace) N y
    (∃ r : T.presheaf.stalk y, r ≠ 0 ∧ r • m = 0) →
    ∃ k, stalkLinearMap (X := T.toRingedSpace)
      (Stacks.AlgebraicGeometry.TorsionSubsheaf.torsionSubsheaf N).ι y k = m := by
  letI := stalkModule (X := T.toRingedSpace) N y
  intro hm
  obtain ⟨V, hyV, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq
    (toAbPresheaf (X := T.toRingedSpace) N) m
  obtain ⟨W, hWV, hyW, a, ha, has⟩ :=
    Stacks.AlgebraicGeometry.ReflexiveModules.exists_annihilator_of_isTorsionSection
      (F := N) (U := V) (s := s) hyV hm
  have ha0 : a ≠ 0 := fun h0 => ha (by rw [h0, map_zero])
  have hWs : Stacks.AlgebraicGeometry.TorsionSubsheaf.IsTorsionSection N
      (N.presheaf.map (homOfLE hWV).op s) := by
    intro z hz
    refine ⟨T.presheaf.germ W z hz a, fun h0 => ha0 ?_, ?_⟩
    · exact germ_injective_of_isIntegral (X := T) z hz (by rw [h0, map_zero])
    · have := Stacks.ModuleStalkSpecialization.germ_smul N hz a (N.presheaf.map (homOfLE hWV).op s)
      rw [← this, has, map_zero]
  let k0 : (Stacks.AlgebraicGeometry.TorsionSubsheaf.torsionSubsheaf N).toSheafOfModules.val.obj
      (op W) := ⟨N.presheaf.map (homOfLE hWV).op s, hWs⟩
  refine ⟨abGerm _ W hyW k0, ?_⟩
  erw [stalkLinearMap_germ]
  exact TopCat.Presheaf.germ_res_apply (toAbPresheaf (X := T.toRingedSpace) N) (homOfLE hWV) y hyW s

private theorem isFiniteLocallyFreeOfRank_one_of_stalks {X : Scheme.{0}} (F : X.Modules)
    [F.IsFiniteType]
    (hgen : ∀ x : X,
      letI : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) F.val x
      ∃ m : F.presheaf.stalk x, Submodule.span (X.presheaf.stalk x) {m} = ⊤)
    (hrank : ∀ x : X,
      letI : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) F.val x
      Module.finrank (X.presheaf.stalk x) (F.presheaf.stalk x) = 1) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} F 1 := by
  classical
  rw [← Scheme.Modules.isFiniteLocallyFreeOfRank_iff]
  intro x
  let A := ToType (X.presheaf.stalk x)
  let M := ToType (F.presheaf.stalk x)
  let : Module A M :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val x
  obtain ⟨m, hm⟩ := hgen x
  obtain ⟨U, -, hxU, s, hs⟩ := Scheme.Modules.finite_germ_lifts F.val.presheaf x
    (I := ULift.{0} (Fin 1)) (fun _ => m) (V := (⊤ : X.Opens)) (Set.mem_univ x)
  have hspanx : ⊤ ≤ Submodule.span A
      (Set.range fun i => TopCat.Presheaf.germ F.val.presheaf U x hxU (s i)) := by
    have hrange : (Set.range fun i => TopCat.Presheaf.germ F.val.presheaf U x hxU (s i))
        = {m} := by
      ext z
      simp only [Set.mem_range, Set.mem_singleton_iff]
      exact ⟨by rintro ⟨i, rfl⟩; exact hs i, by rintro rfl; exact ⟨ULift.up 0, hs _⟩⟩
    rw [hrange]
    exact le_of_eq hm.symm
  obtain ⟨W, hWU, hxW, hspanW⟩ := Scheme.Modules.span_germs_near F s x hxU hspanx
  let t : ULift.{0} (Fin 1) → F.val.presheaf.obj (op W) :=
    fun i => F.val.presheaf.map (homOfLE hWU).op (s i)
  have hgermt : ∀ (y : X) (hy : y ∈ W) (i : ULift.{0} (Fin 1)),
      TopCat.Presheaf.germ F.val.presheaf W y hy (t i)
        = TopCat.Presheaf.germ F.val.presheaf U y (hWU hy) (s i) := fun y hy i =>
    Scheme.Modules.germ_map_section F (homOfLE hWU) y hy (s i)
  have hspanZ : ∀ (y : X) (hy : y ∈ W),
      letI : Module (X.presheaf.stalk y)
          (TopCat.Presheaf.stalk (C := Ab.{0}) F.val.presheaf y) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) F.val y
      ⊤ ≤ Submodule.span (X.presheaf.stalk y)
        (Set.range fun i => TopCat.Presheaf.germ F.val.presheaf W y hy (t i)) := by
    intro y hy
    let : Module (X.presheaf.stalk y)
        (TopCat.Presheaf.stalk (C := Ab.{0}) F.val.presheaf y) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val y
    have hrange : (Set.range fun i => TopCat.Presheaf.germ F.val.presheaf W y hy (t i))
        = Set.range fun i => TopCat.Presheaf.germ F.val.presheaf U y (hWU hy) (s i) :=
      congrArg Set.range (funext fun i => hgermt y hy i)
    rw [hrange]
    exact hspanW y hy
  have hcardZ : ∀ (y : X), y ∈ W →
      letI : Module (X.presheaf.stalk y)
          (TopCat.Presheaf.stalk (C := Ab.{0}) F.val.presheaf y) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) F.val y
      Fintype.card (ULift.{0} (Fin 1)) = Module.finrank (X.presheaf.stalk y)
        (TopCat.Presheaf.stalk (C := Ab.{0}) F.val.presheaf y) := by
    intro y _
    exact (by simp : Fintype.card (ULift.{0} (Fin 1)) = 1).trans (hrank y).symm
  obtain ⟨e⟩ := Scheme.Modules.nonempty_over_iso_free_of_span_germs F t hspanZ hcardZ
  exact ⟨W, hxW, ⟨Stacks.Modules.restrictIsoFree W F _ e.symm⟩⟩

private theorem exists_cokernel_torsion
    {T : Scheme.{0}} [IsIntegral T] (N : T.Modules) [N.IsQuasicoherent] [N.IsFiniteType]
    (hq : ∀ y : T, ∃ q : N.presheaf.stalk y →ₗ[T.presheaf.stalk y] T.presheaf.stalk y,
      Function.Surjective q ∧ ∀ m, q m = 0 ↔ ∃ r : T.presheaf.stalk y, r ≠ 0 ∧ r • m = 0) :
    ∃ (L : T.Modules) (π : N ⟶ L), SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} L 1 ∧
      Epi π ∧ ∀ (U : T.Opens) (s : Γ(N, U)), π.app U s = 0 ↔ IsTorsionSection N s := by
  classical
  let K := Stacks.AlgebraicGeometry.TorsionSubsheaf.torsionSubsheaf N
  let K0 : T.Modules := K.toSheafOfModules
  let ι : K0 ⟶ N := K.ι
  let L := cokernel ι
  let π : N ⟶ L := cokernel.π ι
  let S : ShortComplex T.Modules := ShortComplex.mk ι π (cokernel.condition ι)
  have : Mono ι := inferInstanceAs (Mono K.ι)
  have : Epi π := inferInstance
  have hS : S.ShortExact := ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel ι)
    (inferInstanceAs (Mono ι)) (inferInstanceAs (Epi π))
  have hex := fun y : T =>
    injective_exact_surjective_stalkLinearMap_of_shortExact (X := T.toRingedSpace) S hS y
  have hker : ∀ (U : T.Opens) (s : Γ(N, U)), π.app U s = 0 ↔ IsTorsionSection N s := by
    refine fun U s => ⟨fun h y hy => ?_, fun hs => ?_⟩
    · letI := stalkModule (X := T.toRingedSpace) N y
      obtain ⟨-, hexact, -⟩ := hex y
      have h1 : stalkLinearMap (X := T.toRingedSpace) π y (abGerm N U hy s) = 0 := by
        erw [stalkLinearMap_germ]
        change abGerm L U hy (π.app U s) = 0
        rw [h]
        exact map_zero _
      obtain ⟨k, hk⟩ := (hexact (abGerm N U hy s)).1 h1
      obtain ⟨r, hr, hr0⟩ := torsion_of_stalkLinearMap_torsionSubsheaf N y k
      exact ⟨r, hr, by change r • abGerm N U hy s = 0; rw [← hk]; exact hr0⟩
    · have h0 : (ι ≫ π).app U = 0 := by rw [cokernel.condition]; rfl
      exact ConcreteCategory.congr_hom h0 (⟨s, hs⟩ : Γ(K0, U))
  have hΛ : ∀ y : T, Nonempty (letI := stalkModule (X := T.toRingedSpace) L y
      abStalk (X := T.toRingedSpace) L y ≃ₗ[T.presheaf.stalk y] T.presheaf.stalk y) := by
    intro y
    letI := stalkModule (X := T.toRingedSpace) N y
    letI := stalkModule (X := T.toRingedSpace) L y
    obtain ⟨q0, hqs, hqk⟩ := hq y
    let q : abStalk (X := T.toRingedSpace) N y →ₗ[T.presheaf.stalk y] T.presheaf.stalk y := q0
    obtain ⟨-, hexact, hsurj⟩ := hex y
    have hg : ∀ m : abStalk (X := T.toRingedSpace) N y,
        stalkLinearMap (X := T.toRingedSpace) π y m = 0 ↔ q m = 0 := by
      intro m
      refine Iff.trans ⟨fun h => ?_, fun h =>
        (hexact m).2 (exists_stalkLinearMap_torsionSubsheaf_eq N y m h)⟩ (hqk m).symm
      obtain ⟨k, hk⟩ := (hexact m).1 h
      obtain ⟨r, hr, hr0⟩ := torsion_of_stalkLinearMap_torsionSubsheaf N y k
      exact ⟨r, hr, by rw [← hk]; exact hr0⟩
    have hkerEq : LinearMap.ker (stalkLinearMap (X := T.toRingedSpace) π y) = LinearMap.ker q :=
      Submodule.ext hg
    exact ⟨((LinearMap.quotKerEquivOfSurjective _ hsurj).symm.trans
      ((Submodule.quotEquivOfEq _ _ hkerEq).trans (LinearMap.quotKerEquivOfSurjective q hqs)))⟩
  have : L.IsFiniteType := @Stacks.SheafOfModules.isFiniteType_of_epi.{0, 0, 0} _ _ _
    T.ringCatSheaf _ _ _ N L π ‹_› inferInstance
  refine ⟨L, π, ?_, inferInstance, hker⟩
  refine isFiniteLocallyFreeOfRank_one_of_stalks L ?_ ?_
  · intro x
    obtain ⟨e⟩ := hΛ x
    letI := stalkModule (X := T.toRingedSpace) L x
    refine ⟨e.symm 1, Submodule.eq_top_iff'.2 fun w => Submodule.mem_span_singleton.2 ⟨e w, ?_⟩⟩
    have h := e.symm.map_smul (e w) 1
    rw [smul_eq_mul, mul_one] at h
    exact h.symm.trans (e.symm_apply_apply w)
  · intro x
    obtain ⟨e⟩ := hΛ x
    letI := stalkModule (X := T.toRingedSpace) L x
    exact e.finrank_eq.trans (Module.finrank_self _)

end Cok

attribute [local instance] Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback in
private theorem exists_stalk_torsion_quotient {X : Scheme.{0}} [IsIntegral X]
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (hrank : Module.finrank (X.presheaf.stalk (genericPoint X))
      (M.presheaf.stalk (genericPoint X)) = 1) :
    ∀ y : blowUp (fittingIdeal M (1 : ℤ)),
    ∃ q : ((Scheme.Modules.pullback (blowUpToBase (fittingIdeal M (1 : ℤ)))).obj M).presheaf.stalk y
        →ₗ[(blowUp (fittingIdeal M (1 : ℤ))).presheaf.stalk y]
        (blowUp (fittingIdeal M (1 : ℤ))).presheaf.stalk y,
      Function.Surjective q ∧ ∀ m, q m = 0 ↔
        ∃ r : (blowUp (fittingIdeal M (1 : ℤ))).presheaf.stalk y, r ≠ 0 ∧ r • m = 0 := by
  classical
  set I := fittingIdeal M (1 : ℤ)
  intro y
  have : IsIntegral (blowUp I) := isIntegral_blowUp I (fittingIdeal_one_ne_bot M hrank)
  set N := (Scheme.Modules.pullback (blowUpToBase I)).obj M
  obtain ⟨U, hU, hyU, f, hf, hgen⟩ :=
    Stacks.Divisors.exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor
      (exceptionalIdeal I) inferInstance y
  have hfin : Module.Finite ((blowUp I).presheaf.stalk y) (N.presheaf.stalk y) :=
    _root_.SheafOfModules.finite_stalk (blowUp I).sheaf N y
  have hfinU : Module.Finite Γ(blowUp I, U) Γ(N, U) := moduleFinite_sections_on_affine N U hU
  let Uaff : (blowUp I).affineOpens := ⟨U, hU⟩
  have e1 : fittingIdeal N (1 : ℤ) = exceptionalIdeal I :=
    (fittingIdeal_comap (blowUpToBase I) M 1).symm
  have e0 : fittingIdeal N (0 : ℤ) = ⊥ := by
    rw [← fittingIdeal_comap, fittingIdeal_zero_eq_bot M hrank, Scheme.IdealSheafData.comap_bot]
  have h1 : fittingIdeal (R := (blowUp I).presheaf.stalk y) (M := N.presheaf.stalk y) (1 : ℤ) =
      Ideal.span {(blowUp I).presheaf.germ U y hyU f} := by
    have h := fittingIdeal_stalk_eq_map N hU hyU 1
    have h' := fittingIdeal_ideal N 1 Uaff
    rw [e1] at h'
    rw [Nat.cast_one] at h
    rw [h, ← h']
    change Ideal.map _ ((exceptionalIdeal I).ideal ⟨U, hU⟩) = _
    rw [hgen, Ideal.map_span, Set.image_singleton]
  have h0 : fittingIdeal (R := (blowUp I).presheaf.stalk y) (M := N.presheaf.stalk y) (0 : ℤ) =
      ⊥ := by
    have h := fittingIdeal_stalk_eq_map N hU hyU 0
    have h' := fittingIdeal_ideal N 0 Uaff
    rw [e0] at h'
    rw [Nat.cast_zero] at h
    rw [h, ← h']
    change Ideal.map _ (⊥ : Ideal Γ(blowUp I, U)) = ⊥
    exact Ideal.map_bot
  have hfne : f ≠ 0 := by
    have : Nontrivial Γ(blowUp I, U) :=
      RingHom.domain_nontrivial ((blowUp I).presheaf.germ U y hyU).hom
    exact hf.ne_zero
  have ht : (blowUp I).presheaf.germ U y hyU f ≠ 0 := fun h =>
    hfne (germ_injective_of_isIntegral (X := blowUp I) y hyU (by rw [h, map_zero]))
  exact exists_surjective_linearMap_ker_eq_torsion_of_fittingIdeal _ ht h0 h1

attribute [local instance] Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback in
/-- On the blowup of the first Fitting ideal, the torsion-free quotient of the pulled-back
module is invertible. -/
private theorem exists_epi_invertible_ker_eq_torsion
    {X : Scheme.{0}} [IsIntegral X] (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (hrank : Module.finrank (X.presheaf.stalk (genericPoint X))
      (M.presheaf.stalk (genericPoint X)) = 1) :
    ∃ (L : (blowUp (fittingIdeal M (1 : ℤ))).Modules)
        (q : (Scheme.Modules.pullback (blowUpToBase (fittingIdeal M (1 : ℤ)))).obj M ⟶ L),
        SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} L 1 ∧ Epi q ∧
        (∀ (U : (blowUp (fittingIdeal M (1 : ℤ))).Opens)
          (s : Γ((Scheme.Modules.pullback (blowUpToBase (fittingIdeal M (1 : ℤ)))).obj M, U)),
          q.app U s = 0 ↔ IsTorsionSection _ s) := by
  have := isIntegral_blowUp (fittingIdeal M (1 : ℤ)) (fittingIdeal_one_ne_bot M hrank)
  exact exists_cokernel_torsion _ (exists_stalk_torsion_quotient M hrank)

attribute [local instance] Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback in
private theorem exists_toProjectiveBundle_comp_eq_of_epi {X : Scheme.{0}} (M : X.Modules)
    [M.IsQuasicoherent] {T : Scheme.{0}} (b : T ⟶ X) (L : T.Modules)
    (q : (Scheme.Modules.pullback b).obj M ⟶ L)
    (hL : SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} L 1) (hq : Epi q) :
    ∃ φ : T ⟶ projectiveBundle M,
      φ ≫ projectiveBundleToBase M = b ∧
        Nonempty ((Scheme.Modules.pullback φ).obj (projectiveBundleTwistOne M) ≅ L) := by
  classical
  let Q : Stacks.Divisors.InvertibleQuotient T ((Scheme.Modules.pullback b).obj M) :=
    { L := L
      invertible := Stacks.InvertibleRankOneIff.isInvertible_of_isFiniteLocallyFreeOfRank_one
        T.toRingedSpace L
      q := q
      epi := hq }
  let g := (Stacks.RelativeProj.symGradedOverEquiv (F := M) ((Scheme.Modules.pullback b).obj M)
    (f := b) (Iso.refl _)).symm (Quotient.mk _ Q)
  obtain ⟨α, -⟩ := (Stacks.RelativeProj.symGradedOverEquiv_eq_iff (F := M)
    ((Scheme.Modules.pullback b).obj M) (Iso.refl _) g Q).mp (Equiv.apply_symm_apply _ _)
  exact ⟨g.1, g.2, ⟨α⟩⟩

/-- An invertible quotient of the pulled-back module defines a morphism of the blowup into
`ℙ_X(M)` over `X`, pulling `𝒪(1)` back to it, with image in the closure of the generic fibre. -/
private theorem exists_toProjectiveBundle_of_epi
    {X : Scheme.{0}} [IsIntegral X] (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (hrank : Module.finrank (X.presheaf.stalk (genericPoint X))
      (M.presheaf.stalk (genericPoint X)) = 1)
    (L : (blowUp (fittingIdeal M (1 : ℤ))).Modules)
    (q : (Scheme.Modules.pullback (blowUpToBase (fittingIdeal M (1 : ℤ)))).obj M ⟶ L)
    (hL : SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} L 1) (hq : Epi q) :
    ∃ φ : blowUp (fittingIdeal M (1 : ℤ)) ⟶ projectiveBundle M,
      φ ≫ projectiveBundleToBase M = blowUpToBase (fittingIdeal M (1 : ℤ)) ∧
        Nonempty ((Scheme.Modules.pullback φ).obj (projectiveBundleTwistOne M) ≅ L) ∧
        Set.range φ ⊆ closure ((projectiveBundleToBase M) ⁻¹' {genericPoint X}) := by
  obtain ⟨φ, hφ, hα⟩ := exists_toProjectiveBundle_comp_eq_of_epi M
    (blowUpToBase (fittingIdeal M (1 : ℤ))) L q hL hq
  refine ⟨φ, hφ, hα, ?_⟩
  have hI := fittingIdeal_one_ne_bot M hrank
  have := isIntegral_blowUp (fittingIdeal M (1 : ℤ)) hI
  have hξ : blowUpToBase (fittingIdeal M (1 : ℤ)) (genericPoint (blowUp (fittingIdeal M (1 : ℤ))))
      = genericPoint X := IsBirational.genericPoint_eq _ (isBirational_blowUpToBase _ hI)
  rintro _ ⟨t, rfl⟩
  have ht : t ∈ closure {genericPoint (blowUp (fittingIdeal M (1 : ℤ)))} := by
    rw [(genericPoint_spec _).def]
    exact Set.mem_univ _
  have h1 : φ t ∈ closure (φ '' {genericPoint (blowUp (fittingIdeal M (1 : ℤ)))}) :=
    image_closure_subset_closure_image φ.continuous ⟨t, ht, rfl⟩
  refine closure_mono ?_ h1
  rintro _ ⟨_, rfl, rfl⟩
  change projectiveBundleToBase M (φ _) = genericPoint X
  rw [← Scheme.Hom.comp_apply, hφ, hξ]

/-- Let `X` be a normal complex variety and `M` a coherent torsion-free module of generic rank
one. The first Fitting ideal `I = fittingIdeal M 1` is the unit ideal at every point of
codimension one; on the blowup `b = blowUpToBase I` there is an invertible module `L` and an
epimorphism `b^*M ⟶ L` whose kernel consists exactly of the torsion sections of `b^*M`; and
`blowUp I` maps over `X`, pulling `𝒪(1)` back to `L`, into the closure of the generic fibre
of the projective bundle `ℙ_X(M)`. -/
@[mmp "lem_mmp_conductor_rank_one_fitting_blowup"]
public theorem fittingIdeal_one_blowUp_torsionFreeQuotient_invertible
    {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) (hX : Mori.IsNormalVariety ℂ sX) [IsIntegral X]
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] (hM : IsTorsionFree M)
    (hrank : Module.finrank (X.presheaf.stalk (genericPoint X))
      (M.presheaf.stalk (genericPoint X)) = 1) :
    (∀ x : X, ringKrullDim (X.presheaf.stalk x) = 1 →
        x ∉ (fittingIdeal M (1 : ℤ)).support) ∧
      ∃ (L : (blowUp (fittingIdeal M (1 : ℤ))).Modules)
        (q : (Scheme.Modules.pullback (blowUpToBase (fittingIdeal M (1 : ℤ)))).obj M ⟶ L),
        SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} L 1 ∧ Epi q ∧
        (∀ (U : (blowUp (fittingIdeal M (1 : ℤ))).Opens)
          (s : Γ((Scheme.Modules.pullback (blowUpToBase (fittingIdeal M (1 : ℤ)))).obj M, U)),
          q.app U s = 0 ↔ IsTorsionSection _ s) ∧
        ∃ φ : blowUp (fittingIdeal M (1 : ℤ)) ⟶ projectiveBundle M,
          φ ≫ projectiveBundleToBase M = blowUpToBase (fittingIdeal M (1 : ℤ)) ∧
            Nonempty ((Scheme.Modules.pullback φ).obj (projectiveBundleTwistOne M) ≅ L) ∧
            Set.range φ ⊆ closure ((projectiveBundleToBase M) ⁻¹' {genericPoint X}) := by
  refine ⟨notMem_support_fittingIdeal_one_of_ringKrullDim_eq_one sX hX M hM hrank, ?_⟩
  obtain ⟨L, q, hL, hq, htors⟩ := exists_epi_invertible_ker_eq_torsion M hrank
  exact ⟨L, q, hL, hq, htors, exists_toProjectiveBundle_of_epi M hrank L q hL hq⟩

end MMP.Conductor
