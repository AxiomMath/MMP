module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Divisor.Cartier
public import StacksFrontier.AlgebraicGeometry.AssociatedPointPrime.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentFinite.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic

/-!
# Associated points of a coherent sheaf

Let `F` be a coherent sheaf on a locally Noetherian scheme `X` and `x ∈ X`. The associated primes
of the stalk `F_x`, as a module over `𝒪_{X,x}`, are exactly the primes of `𝒪_{X,x}` corresponding
to the associated points of `F` that specialize to `x`, and the zero divisors of `𝒪_{X,x}` on `F_x`
are the union of these primes. If moreover `X` is Noetherian (quasi-compact), `F` has only finitely
many associated points, hence finitely many associated subvarieties.

## Main definitions

* `MMP.Foundations.stalkSpecializationPrime`: the prime of `𝒪_{X,x}` corresponding to a
  generization `y ⤳ x`, the contraction of the maximal ideal of `𝒪_{X,y}`.

## Main results

* `MMP.Foundations.associatedPrimes_stalk_eq`, `MMP.Foundations.zeroDivisors_stalk_eq`.
* `MMP.Foundations.finite_associatedPoints`, `MMP.Foundations.finite_associatedSubvarieties`.

## Implementation notes

The source works with schemes of finite type over a field, which are Noetherian; here the
standing hypothesis is `[IsLocallyNoetherian X]` for the local statements and `[IsNoetherian X]`
for finiteness (which also needs only quasi-compactness beyond the local one). Coherence is
`SheafOfModules.IsCoherent`. Associated points are `Stacks.Divisors.IsAssociatedPoint`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace MMP.Foundations

variable {X : Scheme.{u}}

/-- The prime ideal of `𝒪_{X,x}` corresponding to a generization `y ⤳ x`. -/
noncomputable def stalkSpecializationPrime {x y : X} (h : y ⤳ x) : Ideal (X.presheaf.stalk x) :=
  (IsLocalRing.maximalIdeal (X.presheaf.stalk y)).comap (X.presheaf.stalkSpecializes h).hom

@[simp]
theorem mem_stalkSpecializationPrime_iff {x y : X} {h : y ⤳ x} {a : X.presheaf.stalk x} :
    a ∈ stalkSpecializationPrime h ↔
      (X.presheaf.stalkSpecializes h).hom a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk y) :=
  Iff.rfl

instance {x y : X} (h : y ⤳ x) : (stalkSpecializationPrime h).IsPrime :=
  Ideal.IsPrime.comap _

open IsLocalRing in
/-- Every prime ideal of `𝒪_{X,x}` is `stalkSpecializationPrime h` for a generization `y ⤳ x`. -/
theorem exists_specializes_stalkSpecializationPrime_eq (x : X) (p : Ideal (X.presheaf.stalk x))
    [hp : p.IsPrime] : ∃ (y : X) (h : y ⤳ x), stalkSpecializationPrime h = p := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  replace hU : IsAffineOpen U := hU
  let : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hxU).hom.toAlgebra
  let pp : Ideal Γ(X, U) := (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
  have hlocx : IsLocalization.AtPrime (X.presheaf.stalk x) pp := hU.isLocalization_stalk _
  let q : Spec Γ(X, U) := (⟨p.comap (algebraMap Γ(X, U) (X.presheaf.stalk x)),
    Ideal.IsPrime.comap _⟩ : PrimeSpectrum Γ(X, U))
  have hqp : q.asIdeal ≤ pp := by
    rw [← IsLocalization.AtPrime.under_maximalIdeal (X.presheaf.stalk x) pp]
    exact Ideal.comap_mono (le_maximalIdeal hp.ne_top)
  have hyU : hU.fromSpec q ∈ U := (Set.ext_iff.mp hU.range_fromSpec _).mp ⟨q, rfl⟩
  set y := hU.fromSpec q with hy
  have hprime : hU.primeIdealOf ⟨y, hyU⟩ = q :=
    hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf ⟨y, hyU⟩)
  have hspec : y ⤳ x := by
    have : (⟨y, hyU⟩ : U) ⤳ ⟨x, hxU⟩ := by
      have h1 : hU.primeIdealOf ⟨y, hyU⟩ ⤳ hU.primeIdealOf ⟨x, hxU⟩ :=
        (PrimeSpectrum.le_iff_specializes _ _).mp (by rwa [hprime])
      have := h1.map (Scheme.homeoOfIso hU.isoSpec).symm.continuous
      have e : ∀ z : U, (Scheme.homeoOfIso hU.isoSpec).symm (hU.primeIdealOf z) = z :=
        fun z => (Scheme.homeoOfIso hU.isoSpec).symm_apply_apply z
      rwa [e, e] at this
    exact (subtype_specializes_iff _ _).mp this
  refine ⟨y, hspec, ?_⟩
  let : Algebra Γ(X, U) (X.presheaf.stalk y) := (X.presheaf.germ U y hyU).hom.toAlgebra
  have hlocy : IsLocalization.AtPrime (X.presheaf.stalk y)
      (hU.primeIdealOf ⟨y, hyU⟩).asIdeal := hU.isLocalization_stalk _
  have hc : (stalkSpecializationPrime hspec).comap (algebraMap Γ(X, U) (X.presheaf.stalk x)) =
      q.asIdeal := by
    rw [← (IsLocalization.AtPrime.under_maximalIdeal (X.presheaf.stalk y)
      (hU.primeIdealOf ⟨y, hyU⟩).asIdeal).trans (congrArg PrimeSpectrum.asIdeal hprime),
      stalkSpecializationPrime, Ideal.comap_comap]
    congr 1
    exact RingHom.ext fun r =>
      Stacks.ModuleStalkSpecialization.ringGerm_stalkSpecializes_apply hxU hspec r
  have hmap : ∀ I : Ideal (X.presheaf.stalk x),
      (I.comap (algebraMap Γ(X, U) (X.presheaf.stalk x))).map
        (algebraMap Γ(X, U) (X.presheaf.stalk x)) = I := fun I =>
    IsLocalization.map_under pp.primeCompl _ I
  rw [← hmap (stalkSpecializationPrime hspec), ← hmap p, hc]

open Stacks.ModuleStalkSpecialization in
/-- For a generization `y ⤳ x`, the prime of `𝒪_{X,x}` attached to `y` is an associated prime of
the stalk `ℱ_x` iff `y` is an associated point of `ℱ`. -/
theorem stalkSpecializationPrime_mem_associatedPrimes_iff [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsQuasicoherent] {x y : X} (h : y ⤳ x) :
    stalkSpecializationPrime h ∈
        associatedPrimes (X.presheaf.stalk x) (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x)
      ↔ Stacks.Divisors.IsAssociatedPoint F y := by
  let : Algebra (X.presheaf.stalk x) (X.presheaf.stalk y) :=
    (X.presheaf.stalkSpecializes h).hom.toAlgebra
  let := stalkModule F x
  let := stalkSpecializesModule F h
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk y)
      ((IsLocalRing.maximalIdeal (X.presheaf.stalk y)).under (X.presheaf.stalk x)) :=
    Stacks.StalkSpecialization.isLocalization_atPrime_stalkSpecializes h
  have hlm := isLocalizedModule_atPrime_stalkSpecializes F h
  have : IsScalarTower (X.presheaf.stalk x) (X.presheaf.stalk y) (F.presheaf.stalk y) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have key :=
    Module.associatedPrimes.preimage_comap_associatedPrimes_eq_associatedPrimes_of_isLocalizedModule
      (S := ((IsLocalRing.maximalIdeal (X.presheaf.stalk y)).under (X.presheaf.stalk x)).primeCompl)
      (R' := X.presheaf.stalk y) (stalkSpecializesₗ F h)
  refine (Set.ext_iff.mp key (IsLocalRing.maximalIdeal (X.presheaf.stalk y))).trans ?_
  rw [← Stacks.RingTheory.AssociatedPrimeStacks.assStacks_eq_associatedPrimes]
  exact Iff.rfl

/-- The associated primes of the stalk `F_x` of a coherent sheaf `F` on a locally Noetherian
scheme are exactly the primes of `𝒪_{X,x}` corresponding to the associated points of `F`
specializing to `x`. -/
@[mmp "lem_mmp_foundation_laz_associated_points_localization"]
theorem associatedPrimes_stalk_eq [IsLocallyNoetherian X] (F : X.Modules) [F.IsCoherent] (x : X) :
    associatedPrimes (X.presheaf.stalk x) (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) =
      {p | ∃ (y : X) (h : y ⤳ x), Stacks.Divisors.IsAssociatedPoint F y ∧
        p = stalkSpecializationPrime h} := by
  have := (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F).1
  ext p
  refine ⟨fun hp => ?_, ?_⟩
  · have := hp.1
    obtain ⟨y, h, rfl⟩ := exists_specializes_stalkSpecializationPrime_eq x p
    exact ⟨y, h, (stalkSpecializationPrime_mem_associatedPrimes_iff F h).mp hp, rfl⟩
  · rintro ⟨y, h, hy, rfl⟩
    exact (stalkSpecializationPrime_mem_associatedPrimes_iff F h).mpr hy

/-- The set of zero divisors of `𝒪_{X,x}` on the stalk `F_x` of a coherent sheaf is the union of
the primes of `𝒪_{X,x}` corresponding to the associated points of `F` specializing to `x`. -/
@[mmp "lem_mmp_foundation_laz_associated_points_localization"]
theorem zeroDivisors_stalk_eq [IsLocallyNoetherian X] (F : X.Modules) [F.IsCoherent] (x : X) :
    {a : X.presheaf.stalk x | ∃ m : TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x,
        m ≠ 0 ∧ a • m = 0} =
      ⋃ (y : X) (h : y ⤳ x) (_ : Stacks.Divisors.IsAssociatedPoint F y),
        (stalkSpecializationPrime h : Set (X.presheaf.stalk x)) := by
  rw [← biUnion_associatedPrimes_eq_zero_divisors, associatedPrimes_stalk_eq]
  ext a
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, SetLike.mem_coe, exists_prop]
  constructor
  · rintro ⟨p, ⟨y, h, hy, rfl⟩, ha⟩
    exact ⟨y, h, hy, ha⟩
  · rintro ⟨y, h, hy, ha⟩
    exact ⟨_, ⟨y, h, hy, rfl⟩, ha⟩

/-- A coherent sheaf on a Noetherian scheme has only finitely many associated points. -/
theorem finite_associatedPoints [IsNoetherian X] (F : X.Modules) [F.IsCoherent] :
    (Stacks.Divisors.associatedPoints F).Finite := by
  obtain ⟨_, _⟩ :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F
  have hcov : (Set.univ : Set X) ⊆ ⋃ U : X.affineOpens, (U : Set X) := by
    intro x _
    have : x ∈ ((⨆ i : X.affineOpens, (i : X.Opens) : X.Opens) : Set X) := by
      rw [iSup_affineOpens_eq_top]
      trivial
    simpa [TopologicalSpace.Opens.mem_iSup] using this
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun U : X.affineOpens => (U : Set X))
    (fun U => U.1.isOpen) hcov
  have hU : ∀ U : X.affineOpens,
      {y : X | y ∈ (U : Set X) ∧ y ∈ Stacks.Divisors.associatedPoints F}.Finite := by
    intro U
    have hU' : IsAffineOpen (U : X.Opens) := U.2
    have : IsNoetherianRing Γ(X, (U : X.Opens)) := IsLocallyNoetherian.component_noetherian U
    have hfin : Module.Finite Γ(X, (U : X.Opens)) Γ(F, (U : X.Opens)) :=
      Stacks.AlgebraicGeometry.CoherentFinite.finite_sections F hU'
    have hfinU : {z : (U : X.Opens) | (z : X) ∈ Stacks.Divisors.associatedPoints F}.Finite := by
      refine Set.Finite.of_injOn (f := fun z => (hU'.primeIdealOf z).asIdeal) ?_ ?_
        (associatedPrimes.finite Γ(X, (U : X.Opens)) Γ(F, (U : X.Opens)))
      · exact fun z hz =>
          Stacks.AlgebraicGeometry.AssociatedPointPrime.mem_associatedPrimes_of_isAssociatedPoint
            F hU' z.2 hz
      · intro z _ w _ hzw
        apply Subtype.ext
        rw [← hU'.fromSpec_primeIdealOf z, ← hU'.fromSpec_primeIdealOf w, PrimeSpectrum.ext hzw]
    refine (hfinU.image Subtype.val).subset ?_
    rintro y ⟨hyU, hy⟩
    exact ⟨⟨y, hyU⟩, hy, rfl⟩
  refine (t.finite_toSet.biUnion fun U _ => hU U).subset fun y hy => ?_
  obtain ⟨U, hUt, hyU⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ y))
  exact Set.mem_iUnion₂.mpr ⟨U, hUt, hyU, hy⟩

/-- A coherent sheaf on a Noetherian scheme has only finitely many associated subvarieties. -/
@[mmp "lem_mmp_foundation_laz_associated_points_finite"]
theorem finite_associatedSubvarieties [IsNoetherian X] (F : X.Modules) [F.IsCoherent] :
    {V | MMP.Intersection.IsAssociatedSubvariety F V}.Finite := by
  refine ((finite_associatedPoints F).image MMP.Intersection.associatedSubvariety).subset ?_
  rintro V ⟨ξ, hξ, rfl⟩
  exact ⟨ξ, hξ, rfl⟩

end MMP.Foundations

