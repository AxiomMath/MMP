module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Resolution.Blowup.SmoothGeometry
public import MMP.AlgebraicGeometry.Resolution.Blowup.SmoothCentre
public import MMP.AlgebraicGeometry.Resolution.ExceptionalDivisorPrime
public import MMP.AlgebraicGeometry.ProjectiveSpace.ProjComparison
public import StacksFrontier.AlgebraicGeometry.ProjTwistDegreeOneCover.Basic
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.ZeroTwist
public import StacksFrontier.AlgebraicGeometry.ProjTwistRank.Basic
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Cover
public import StacksFrontier.AlgebraicGeometry.PicardGroup.Pullback
public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorPicardClass
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.TautologicalDatumTwistComparison
public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.ProjectiveBundleBaseChange
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.FibreProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.DeRham.ProjectiveSpaceDeRhamClassPow
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistenceAlgebraization

/-!
# The normal bundle of the exceptional divisor of a smooth blow-up, on a fibre

Let `Y` be smooth over a field `k`, `Z ⊆ Y` a smooth irreducible closed subscheme of codimension
`c ≥ 2` with ideal sheaf `I`, `π : V = Bl_Z Y ⟶ Y` the blow-up and `E = π⁻¹(Z)` its exceptional
divisor. For every `z ∈ Z` the fibre `π⁻¹(z)` of `E ⟶ Z` is `ℙ^{c-1}_{κ(z)}`, and
`𝒪_V(E)|_{π⁻¹(z)} ≅ 𝒪_{ℙ^{c-1}_{κ(z)}}(-1)`.

The proof identifies `E` with the projective bundle `𝐏(I_Z/I_Z²)` over `Z`, under which
`𝒪_V(-E)|_E` is the twisting sheaf `𝒪(1)` of the bundle ([Stacks, Tag 0FUT]). The twisting sheaf
of a relative `Proj` is compatible with base change ([Stacks, Tag 01O3]); along
`Spec κ(z) ⟶ Z`, where `I_Z/I_Z²` is free of rank `c`, it becomes `𝒪(1)` on
`Proj κ(z)[T₀, …, T_{c-1}]`. So `𝒪_V(-E)` restricts to `𝒪(1)` on the fibre. Finally `𝒪_V(E)` and
`𝒪_V(-E)` have opposite classes in the Picard group of the fibre, as do `𝒪(-1)` and `𝒪(1)`.

## Main results

* `MMP.Threefold.Resolution.exists_fiber_iso_projSpace_pullback_invertibleSheaf_exceptionalIdeal`:
  `𝒪_V(E)|_{π⁻¹(z)} ≅ 𝒪_{ℙ^{c-1}_{κ(z)}}(-1)`, with `c` the codimension of `Z`.
* `MMP.Threefold.Resolution.exists_fiber_iso_proj_pullback_exceptionalIdealModule`: the degree
  one statement `𝒪_V(-E)|_{π⁻¹(z)} ≅ 𝒪(1)`, on `Proj κ(z)[T₀, …, Tₙ]`.
* `MMP.Threefold.Resolution.pullbackPicardClass_twistingSheaf_neg_one` and
  `MMP.Threefold.Resolution.pullbackPicardClass_invertibleSheaf_eq_neg`: the two sign rules in
  the Picard group.

## Implementation notes

* `𝒪_V(E)` is `Stacks.Divisors.invertibleSheaf'` of the exceptional ideal, the dual of the ideal
  sheaf `𝒪_V(-E)`; restriction to the fibre is the pullback along `π⁻¹(z) ⟶ E ⟶ V`.
* `ℙ^{c-1}_{κ(z)}` is `MMP.Intersection.ProjSpace κ(z) (ULift (Fin c))` over `κ(z)`, and
  `𝒪(-1)` is its twisting sheaf `ProjectiveSpectrum.Proj.twistingSheaf _ (-1)`.

## References

* [J. Kollár, *Lectures on resolution of singularities*, Notation 3.19]
* [Stacks Project, Tags 0FUT, 01O3, 01MT]
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace RingedSpaceModuleAdjunction IsLocalRing

universe u

namespace MMP.Threefold.Resolution

open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **`𝒪(-1)` and `𝒪(1)` on `ℙⁿ_R` have opposite pullback classes.** For any morphism
`φ : F ⟶ Proj R[T₀, …, Tₙ]`, the classes of `φ^*𝒪(-1)` and `φ^*𝒪(1)` in `Pic(F)` are opposite,
since `𝒪(1) ⊗ 𝒪(-1) ≅ 𝒪(0) ≅ 𝒪`. -/
theorem pullbackPicardClass_twistingSheaf_neg_one {R : Type u} [CommRing R] {n : ℕ}
    {F : Scheme.{u}} (φ : F ⟶ AlgebraicGeometry.Proj (polyGrading R n))
    (hm : Stacks.SheafOfModules.IsInvertible (AlgebraicGeometry.Proj (polyGrading R n)).presheaf
      (AlgebraicGeometry.Proj (polyGrading R n)).ringCatIsSheaf
      (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) (-1)))
    (h₁ : Stacks.SheafOfModules.IsInvertible (AlgebraicGeometry.Proj (polyGrading R n)).presheaf
      (AlgebraicGeometry.Proj (polyGrading R n)).ringCatIsSheaf
      (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) 1)) :
    Stacks.SheafOfModules.pullbackPicardClass φ
        (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) (-1)) hm =
      -Stacks.SheafOfModules.pullbackPicardClass φ
        (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) 1) h₁ := by
  refine Stacks.SheafOfModules.pullbackPicardClass_eq_neg_of_isTrivial_tensorSheaf φ _ _ _ _
    (Stacks.SheafOfModules.isInvertible_schemeTensor _ _ _ h₁ hm) ⟨?_⟩
  exact Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover.twistMultiplicationIso (polyGrading R n)
      (Stacks.AlgebraicGeometry.ProjTwistRank.degreeOneCover_polyGrading R n) 1 (-1) ≪≫
    eqToIso (congrArg _ (by norm_num)) ≪≫
    Stacks.AlgebraicGeometry.ProjEulerSequence.twistingSheafZeroIsoUnit (polyGrading R n)

open AlgebraicGeometry.Scheme.Modules in
/-- A finite locally free module is free of rank its fibre rank near each point. -/
private theorem exists_restrict_iso_free_fiberRank {X : Scheme.{u}} (E : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] (x : X) :
    ∃ (V : X.Opens) (_ : x ∈ V), Nonempty (E.restrict V.ι ≅
      SheafOfModules.free (R := V.toScheme.ringCatSheaf)
        (ULift.{u} (Fin (fiberRank E x)))) := by
  obtain ⟨V, hV, -, I, ⟨eI⟩, ⟨eV⟩⟩ :=
    exists_free_nbhd_of_mem_rankStratum E _ x ((mem_rankStratum E).2 rfl)
  have e1 := restrictIsoFreeOfOverIso E V I eV
  have hcard : fiberRank E x = Nat.card I :=
    @fiberRank_eq_card_of_trivialization _ E x V hV (trivializationOfRestrictIso E V I e1)
      (Finite.of_equiv _ eI.symm)
  have hI : Nonempty (I ≃ ULift.{u} (Fin (fiberRank E x))) := by
    refine ⟨eI.trans ?_⟩
    rw [show finiteLocallyFreeRank E x = fiberRank E x by
      rw [hcard, Nat.card_congr eI, Nat.card_fin]]
    exact Equiv.ulift.symm
  obtain ⟨eq⟩ := hI
  exact ⟨V, hV, ⟨e1 ≪≫ (SheafOfModules.freeFunctor).mapIso (Equiv.toIso eq)⟩⟩

open Stacks.RelativeProj in
/-- The base-change morphism `𝐏(E') ⟶ 𝐏(E)` pulls `𝒪_{𝐏(E)}(1)` back to `𝒪_{𝐏(E')}(1)`. -/
def projectiveBundleBaseChangeTwistOneIso {X Y : Scheme.{u}} (g : X ⟶ Y) (E : Y.Modules)
    [SheafOfModules.IsQuasicoherent E] (E' : X.Modules) [SheafOfModules.IsQuasicoherent E']
    (hE : E' ≅ (Scheme.Modules.pullback g).obj E) :
    (Scheme.Modules.pullback (projectiveBundleBaseChange g E E' hE)).obj
        (Situation.twistSheaf (symmetricSituationOfQuasicoherent Y E) 1) ≅
      Situation.twistSheaf (symmetricSituationOfQuasicoherent X E') 1 :=
  Situation.twistSheafPullbackIso (s := symmetricSituationOfQuasicoherent Y E)
    (s' := symmetricSituationOfQuasicoherent X E') g (symmetricSituationPullbackHom g E E' hE)
    (fun m => isIso_symmetricSituationPullbackHom_app g E E' hE (m : ℤ)) 1

open Stacks.RelativeProj in
/-- The presentation isomorphism of the projective bundle of `F` pulls `𝒪(1)` back to the
tautological twist. -/
def bundlePresentationIsoTwistOneIso {X : Scheme.{u}} (F : X.Modules)
    [SheafOfModules.IsQuasicoherent F] :
    (Scheme.Modules.pullback (bundlePresentationIso F).hom).obj
        (Situation.twistSheaf (symmetricSituationOfQuasicoherent X F) 1) ≅
      Stacks.ProjectiveBundleSplitting.tautologicalTwist F
        (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent F) :=
  (Scheme.Modules.pullback (bundlePresentationIso F).hom).mapIso
      (twistSheafOneIsoTautologicalDatumTwist F) ≪≫
    (Scheme.Modules.pullbackComp _ (bundlePresentationIso F).inv).app _ ≪≫
    (Scheme.Modules.pullbackCongr (bundlePresentationIso F).hom_inv_id).app _ ≪≫
    (Scheme.Modules.pullbackId _).app _

open Stacks.RelativeProj Stacks.AlgebraicGeometry in
open Stacks.AlgebraicGeometry.ProjPolyChart (projToSpecCoeff) in
/-- **The ideal sheaf of the exceptional divisor restricts to `𝒪(1)` on each fibre.** For a
smooth blow-up and `z` in the centre at which `I_Z/I_Z²` has rank `n + 1`, the fibre of `E ⟶ Z`
over `z` is identified with `Proj κ(z)[T₀, …, Tₙ]` over `κ(z)` so that `𝒪_V(-E)` pulls back to
`𝒪(1)`. -/
theorem exists_fiber_iso_proj_pullback_exceptionalIdealModule {k : Type u} [Field k]
    {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) (I : Y.IdealSheafData) [Smooth sY]
    [Smooth (I.subschemeι ≫ sY)]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (Stacks.Conormal.conormalSheafDegreeOne I.subschemeι)]
    (z : I.subscheme) (n : ℕ)
    (hn : Scheme.Modules.fiberRank (Stacks.Conormal.conormalSheafDegreeOne I.subschemeι) z =
      n + 1) :
    ∃ e₀ : (exceptionalSubschemeMap I).fiber z ≅
        AlgebraicGeometry.Proj (polyGrading (I.subscheme.residueField z) n),
      e₀.hom ≫ projToSpecCoeff (I.subscheme.residueField z) n =
          (exceptionalSubschemeMap I).fiberToSpecResidueField z ∧
        Nonempty ((Scheme.Modules.pullback ((exceptionalSubschemeMap I).fiberι z ≫
            (exceptionalIdeal I).subschemeι)).obj (exceptionalIdealModule I) ≅
          (Scheme.Modules.pullback e₀.hom).obj
            (ProjectiveSpectrum.Proj.twistingSheaf
              (polyGrading (I.subscheme.residueField z) n) 1)) := by
  set C := Stacks.Conormal.conormalSheafDegreeOne I.subschemeι
  set K := I.subscheme.residueField z
  set p := exceptionalSubschemeMap I
  obtain ⟨V, hV, ⟨eV⟩⟩ := exists_restrict_iso_free_fiberRank C z
  rw [hn] at eV
  let j : Spec (CommRingCat.of K) ⟶ I.subscheme := I.subscheme.fromSpecResidueField z
  have hj : Set.range j ⊆ V := by simpa [j, I.subscheme.range_fromSpecResidueField] using hV
  obtain ⟨hF⟩ := Stacks.ProjectiveBundleFibre.nonempty_iso_pullback_of_restrict_free C _ V eV j hj
  have : (SheafOfModules.free (R := (Spec (CommRingCat.of K)).ringCatSheaf)
      (ULift.{u} (Fin (n + 1)))).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineQcohEquivalence.isQuasicoherent_free _
  obtain ⟨θ, hθ, ⟨β⟩⟩ := Stacks.ProjectiveBundleFibre.exists_iso_freeProjectiveBundle K n
  let Ff := SheafOfModules.free (R := (Spec (CommRingCat.of K)).ringCatSheaf)
    (ULift.{u} (Fin (n + 1)))
  let B := bundlePresentationIso Ff
  let ψ := θ ≪≫ B
  let bc := projectiveBundleBaseChange j C Ff hF
  have hψ : ψ.hom ≫ projectiveBundleToBase _ Ff = projToSpecCoeff K n :=
    (Category.assoc _ _ _).trans ((congrArg (fun k => θ.hom ≫ k)
      (bundlePresentationIso_hom_comp_toBase Ff)).trans hθ)
  have hP : IsPullback (ψ.hom ≫ bc) (projToSpecCoeff K n) (projectiveBundleToBase _ C) j := by
    refine (isPullback_projectiveBundleToBase_baseChange j C Ff hF).flip.of_iso
      ψ.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp [j])
    · simp [bc]
    · simp [← hψ]
  let δ := exceptionalDivisorIsoProjectiveBundle sY I
  have h' : IsPullback ((ψ.hom ≫ bc) ≫ δ.inv) (projToSpecCoeff K n) p j :=
    hP.of_iso (Iso.refl _) δ.symm (Iso.refl _) (Iso.refl _) (by simp) (by simp)
      (δ.eq_inv_comp.mpr (exceptionalDivisorIsoProjectiveBundle_hom_toCentre sY I)) (by simp)
  have hfib : IsPullback (p.fiberι z) (p.fiberToSpecResidueField z) p
      (I.subscheme.fromSpecResidueField z) := IsPullback.of_hasPullback _ _
  let e₀ := hfib.isoIsPullback _ _ h'
  have he₀ : e₀.hom ≫ (ψ.hom ≫ bc) ≫ δ.inv = p.fiberι z := hfib.isoIsPullback_hom_fst _ _ h'
  refine ⟨e₀, hfib.isoIsPullback_hom_snd _ _ h', ⟨?_⟩⟩
  have hcomp : p.fiberι z ≫ δ.hom = e₀.hom ≫ θ.hom ≫ B.hom ≫ bc := by
    rw [← he₀]
    simp [ψ]
  exact ((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫
    (Scheme.Modules.pullback (p.fiberι z)).mapIso (exceptionalTwistOneIso sY I).symm ≪≫
    (Scheme.Modules.pullbackComp _ _).app _ ≪≫
    (Scheme.Modules.pullbackCongr hcomp).app _ ≪≫
    ((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫
    (Scheme.Modules.pullback e₀.hom).mapIso
      (((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫
        (Scheme.Modules.pullback θ.hom).mapIso
          (((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫
            (Scheme.Modules.pullback B.hom).mapIso
              (projectiveBundleBaseChangeTwistOneIso j C Ff hF) ≪≫
            bundlePresentationIsoTwistOneIso Ff) ≪≫ β)

/-- A morphism smooth at every point is smooth. -/
private theorem smooth_of_isSmoothScheme' {X S : Scheme.{u}} {f : X ⟶ S}
    (h : MMP.Mori.IsSmoothScheme f) : Smooth f := by
  have : IsZariskiLocalAtSource @Smooth := HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @Smooth)
    (fun U : {U : X.Opens // Smooth (U.ι ≫ f)} => U.1) ?_ fun U => U.2
  rw [← h, MMP.Mori.smoothLocus, sSup_eq_iSup']
  rfl

/-- For an effective Cartier divisor `D` on `V` and `g : F ⟶ V`, the classes of `g^*𝒪_V(D)` and
`g^*𝒪_V(-D)` in `Pic(F)` are opposite. -/
theorem pullbackPicardClass_invertibleSheaf_eq_neg {F V : Scheme.{u}} (g : F ⟶ V)
    (D : V.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D] :
    Stacks.SheafOfModules.pullbackPicardClass g (Stacks.Divisors.invertibleSheaf' D)
        (Stacks.Divisors.isInvertible_invertibleSheaf_picard D) =
      -Stacks.SheafOfModules.pullbackPicardClass g (Stacks.Divisors.negativeTwist' D)
        (Stacks.Divisors.isInvertible_negativeTwist_picard D) := by
  have hO := Stacks.Divisors.isInvertible_invertibleSheaf_picard D
  have hN := Stacks.Divisors.isInvertible_negativeTwist_picard D
  have htriv : Stacks.SheafOfModules.IsTrivial V.presheaf V.ringCatIsSheaf
      (Stacks.SheafOfModules.schemeTensor V (Stacks.Divisors.invertibleSheaf' D)
        (Stacks.Divisors.negativeTwist' D)) := by
    have := Stacks.Divisors.isTensorInvertible_negativeTwist D
    exact ⟨Stacks.SheafOfModules.Scheme.evaluationIso V (Stacks.Divisors.negativeTwist' D)⟩
  rw [Stacks.SheafOfModules.pullbackPicardClass_eq_neg_of_isTrivial_tensorSheaf g _ _ hO hN
    (Stacks.SheafOfModules.isInvertible_schemeTensor V _ _ hO hN) htriv, neg_neg]

open Stacks.AlgebraicGeometry in
open Stacks.AlgebraicGeometry.ProjPolyChart (projToSpecCoeff) in
/-- **`𝒪_V(E)` restricts to `𝒪(-1)` on each fibre**, with the fibre read as
`Proj κ(z)[T₀, …, Tₙ]` over `κ(z)`. -/
theorem exists_fiber_iso_proj_pullback_invertibleSheaf {k : Type u} [Field k]
    {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) (I : Y.IdealSheafData) [Smooth sY]
    [Smooth (I.subschemeι ≫ sY)]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (Stacks.Conormal.conormalSheafDegreeOne I.subschemeι)]
    (z : I.subscheme) (n : ℕ)
    (hn : Scheme.Modules.fiberRank (Stacks.Conormal.conormalSheafDegreeOne I.subschemeι) z =
      n + 1) :
    ∃ e₀ : (exceptionalSubschemeMap I).fiber z ≅
        AlgebraicGeometry.Proj (polyGrading (I.subscheme.residueField z) n),
      e₀.hom ≫ projToSpecCoeff (I.subscheme.residueField z) n =
          (exceptionalSubschemeMap I).fiberToSpecResidueField z ∧
        Nonempty ((Scheme.Modules.pullback ((exceptionalSubschemeMap I).fiberι z ≫
            (exceptionalIdeal I).subschemeι)).obj
              (Stacks.Divisors.invertibleSheaf' (exceptionalIdeal I)) ≅
          (Scheme.Modules.pullback e₀.hom).obj
            (ProjectiveSpectrum.Proj.twistingSheaf
              (polyGrading (I.subscheme.residueField z) n) (-1))) := by
  obtain ⟨e₀, he₀, ⟨ι₁⟩⟩ := exists_fiber_iso_proj_pullback_exceptionalIdealModule sY I z n hn
  refine ⟨e₀, he₀, ?_⟩
  have := Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal I
  set g := (exceptionalSubschemeMap I).fiberι z ≫ (exceptionalIdeal I).subschemeι
  have hinv (m : ℤ) : Stacks.SheafOfModules.IsInvertible
      (AlgebraicGeometry.Proj (polyGrading (I.subscheme.residueField z) n)).presheaf
      (AlgebraicGeometry.Proj (polyGrading (I.subscheme.residueField z) n)).ringCatIsSheaf
      (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading (I.subscheme.residueField z) n) m) :=
    Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover.isInvertible_twistingSheaf _
      (Stacks.AlgebraicGeometry.ProjTwistRank.degreeOneCover_polyGrading _ n) m
  have h1 : Stacks.SheafOfModules.pullbackPicardClass g
      (Stacks.Divisors.negativeTwist' (exceptionalIdeal I))
        (Stacks.Divisors.isInvertible_negativeTwist_picard _) =
      Stacks.SheafOfModules.pullbackPicardClass e₀.hom
        (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading (I.subscheme.residueField z) n) 1)
        (hinv 1) :=
    (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).2
      ⟨(AlgebraicGeometry.GrothendieckExistence.modulePullbackIsoPullback g).app _ ≪≫ ι₁ ≪≫
        ((AlgebraicGeometry.GrothendieckExistence.modulePullbackIsoPullback e₀.hom).app _).symm⟩
  have h2 : Stacks.SheafOfModules.pullbackPicardClass g
      (Stacks.Divisors.invertibleSheaf' (exceptionalIdeal I))
        (Stacks.Divisors.isInvertible_invertibleSheaf_picard _) =
      Stacks.SheafOfModules.pullbackPicardClass e₀.hom
        (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading (I.subscheme.residueField z) n) (-1))
        (hinv (-1)) := by
    rw [pullbackPicardClass_invertibleSheaf_eq_neg, h1, pullbackPicardClass_twistingSheaf_neg_one]
  obtain ⟨i⟩ := (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).1 h2
  exact ⟨((AlgebraicGeometry.GrothendieckExistence.modulePullbackIsoPullback g).app _).symm ≪≫ i ≪≫
    (AlgebraicGeometry.GrothendieckExistence.modulePullbackIsoPullback e₀.hom).app _⟩

/- The height computations below repeat lemmas that are private in
`MMP/Resolution/Bridges/SmoothBlowup.lean`. -/

section Height

open RingTheory.Sequence

/-- A weakly regular sequence of length `n` generates an ideal of height at least `n`. -/
private theorem le_height_ofList_of_isWeaklyRegular {R : Type*} [CommRing R] [IsNoetherianRing R]
    (rs : List R) (hreg : IsWeaklyRegular R rs) :
    (rs.length : ℕ∞) ≤ (Ideal.ofList rs).height := by
  rw [Ideal.height_eq_inf_minimalPrimes]
  refine le_iInf₂ fun P hP => ?_
  have hPp : P.IsPrime := hP.1.1
  have hle : ∀ r ∈ rs, r ∈ P := fun r hr => hP.1.2 (Ideal.subset_span hr)
  let S := Localization.AtPrime P
  have hS : IsRegular S (rs.map (algebraMap R S)) :=
    hreg.isRegular_of_isLocalization_of_mem S P hle
  have h1 := ringKrullDim_add_length_eq_ringKrullDim_of_isRegular _ hS
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height P S] at h1
  have hne : Nontrivial (S ⧸ Ideal.ofList (rs.map (algebraMap R S))) := by
    apply Ideal.Quotient.nontrivial_iff.mpr
    intro htop
    apply hS.2
    simp [htop]
  have h0 : (0 : WithBot ℕ∞) ≤ ringKrullDim (S ⧸ Ideal.ofList (rs.map (algebraMap R S))) :=
    ringKrullDim_nonneg_of_nontrivial
  rw [List.length_map] at h1
  have : ((rs.length : ℕ∞) : WithBot ℕ∞) ≤ ((P.height : ℕ∞) : WithBot ℕ∞) := by
    rw [← h1]
    calc ((rs.length : ℕ∞) : WithBot ℕ∞) = 0 + (rs.length : WithBot ℕ∞) := by simp
      _ ≤ _ := by gcongr
  exact_mod_cast this

/-- A proper ideal generated by `n` elements has height at most `n` (Krull's height theorem). -/
private theorem height_ofList_le {R : Type*} [CommRing R] [IsNoetherianRing R]
    (rs : List R) (hne : Ideal.ofList rs ≠ ⊤) :
    (Ideal.ofList rs).height ≤ (rs.length : ℕ∞) := by
  classical
  refine (Ideal.height_le_spanRank_toENat _ hne).trans ?_
  rw [show Ideal.ofList rs = Ideal.span (rs.toFinset : Set R) by simp [Ideal.ofList]]
  refine (OrderHomClass.mono Cardinal.toENat (Submodule.spanRank_span_le_card _)).trans ?_
  have h : Cardinal.mk ((rs.toFinset : Set R)) = rs.toFinset.card := by
    simp only [Finset.coe_sort_coe]
    exact Cardinal.mk_coe_finset
  rw [h, show Cardinal.toENat (rs.toFinset.card : Cardinal) = (rs.toFinset.card : ℕ∞) by simp]
  exact_mod_cast List.toFinset_card_le rs

end Height

/-- Composing with the inclusion of an open does not change the height of the kernel of the stalk
map. -/
private theorem height_ker_stalkMap_eq_of_comp_opens {Z X : Scheme.{u}} (U : X.Opens)
    (j : Z ⟶ U.toScheme) (i : Z ⟶ X) (h : j ≫ U.ι = i) (z : Z) :
    (RingHom.ker (i.stalkMap z).hom).height = (RingHom.ker (j.stalkMap z).hom).height := by
  subst h
  let e : X.presheaf.stalk ((j ≫ U.ι) z) ≅ U.toScheme.presheaf.stalk (j z) :=
    (U.stalkIso (j z)).symm
  have hcomp : (j ≫ U.ι).stalkMap z = e.hom ≫ j.stalkMap z := by
    rw [Scheme.Hom.stalkMap_comp]
    exact (congrArg (fun t => t ≫ j.stalkMap z) (Scheme.Opens.stalkIso_inv U (j z))).symm
  have hker : RingHom.ker ((j ≫ U.ι).stalkMap z).hom =
      (RingHom.ker (j.stalkMap z).hom).comap e.commRingCatIsoToRingEquiv := by
    rw [hcomp, CommRingCat.hom_comp, ← RingHom.comap_ker]
    rfl
  rw [hker, RingEquiv.height_comap]

open Stacks.AlgebraicGeometry Stacks.AlgebraicGeometry.RegularIdealSheaf in
/-- **The rank of the conormal sheaf of a regular immersion at `z` is the height of the ideal of
`Z` in the local ring of `X` at `i z`.** A regular sequence generating the ideal near `i z` has
length equal to the fibre rank of the conormal sheaf, and its germs are a regular sequence of the
local ring. -/
private theorem fiberRank_conormalModule_eq_height {Z X : Scheme.{u}}
    [IsLocallyNoetherian X] (i : Z ⟶ X) [IsImmersion i] (hi : IsRegularImmersion i) (z : Z) :
    ((Scheme.Modules.fiberRank (Stacks.Chow.conormalModule i) z : ℕ) : ℕ∞) =
      (RingHom.ker (i.stalkMap z).hom).height := by
  set U := i.coborderRange
  set j : Z ⟶ U.toScheme := i.liftCoborder
  have hij : j ≫ U.ι = i := i.liftCoborder_ι
  have hreg : IsRegularIdealSheaf U.toScheme.toLocallyRingedSpace.toRingedSpace
      (definingIdealOfHom j) := (isRegularImmersion_iff_of_open i U j hij).mp hi
  have hx : j z ∈ idealQuotientSupport U.toScheme.toLocallyRingedSpace.toRingedSpace
      (definingIdealOfHom j) :=
    (mem_idealQuotientSupport_definingIdealOfHom_iff j (j z)).mpr (subset_closure ⟨z, rfl⟩)
  obtain ⟨U₀, hxU₀, s, g, hgreg, hgen⟩ := hreg (j z) hx
  have hrank : Scheme.Modules.fiberRank (Stacks.Chow.conormalModule i) z = s := by
    rw [Scheme.Modules.fiberRank_eq_of_iso (Stacks.Chow.immersionConormalSheafFactorIso U j hij) z]
    obtain ⟨V, hV, hxV, hVU₀⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp U.toScheme.isBasis_affineOpens hxU₀
    have hker := ker_app_eq_span_range j hV _ (isGeneratedByOn_of_le U₀ g hgen V hVU₀)
    have hq := isQuasiRegular_of_isWeaklyRegular _ (isWeaklyRegular_of_isRegularSequenceOn
      U.toScheme V hV _ (isRegularSequenceOn_of_le _ hVU₀ g hgreg))
    exact Stacks.Conormal.fiberRank_conormalSheaf_eq_of_isQuasiRegular j hV
      (by rw [Stacks.Conormal.coborderRange_eq_top j]; exact le_top) _ hq hker hxV
  set rs := List.ofFn (germFamily U.toScheme.toLocallyRingedSpace.toRingedSpace U₀ g (j z) hxU₀)
  have hspan : Ideal.ofList rs = RingHom.ker (j.stalkMap z).hom := by
    rw [ideal_ofList_ofFn, ← stalkIdeal_definingIdealOfHom_eq_ker,
      stalkIdeal_eq_Jid_germFamily _ U₀ g hgen (j z) hxU₀]
    rfl
  have hrs : RingTheory.Sequence.IsWeaklyRegular (U.toScheme.presheaf.stalk (j z)) rs :=
    isWeaklyRegular_germFamily_of_isRegularSequenceOn _ U₀ g hgreg (j z) hxU₀
  have hne : Ideal.ofList rs ≠ ⊤ := by
    rw [hspan]
    exact RingHom.ker_ne_top _
  have hht : (RingHom.ker (j.stalkMap z).hom).height = (s : ℕ∞) := by
    rw [← hspan]
    refine le_antisymm ?_ ?_
    · simpa [rs] using height_ofList_le rs hne
    · simpa [rs] using le_height_ofList_of_isWeaklyRegular rs hrs
  rw [height_ker_stalkMap_eq_of_comp_opens U j i hij z, hht, hrank]

open Stacks.AlgebraicGeometry.ProjPolyChart (projToSpecCoeff) in
/-- The renaming isomorphism `ℙ^{ULift (Fin (n + 1))}_K ≅ Proj K[T₀, …, Tₙ]` lies over
`Spec K`. -/
theorem isoPolyGrading_inv_comp_toSpec (K : Type u) [Field K] (n : ℕ) :
    (MMP.Intersection.ProjSpace.isoPolyGrading K n).inv ≫
      MMP.Intersection.ProjSpace.toSpec K (ULift.{u} (Fin (n + 1))) = projToSpecCoeff K n := by
  change AlgebraicGeometry.Proj.map _ _ ≫ _ = _
  unfold MMP.Intersection.ProjSpace.toSpec projToSpecCoeff
  rw [AlgebraicGeometry.Proj.map_toSpecZero_assoc, ← Spec.map_comp]
  congr 2
  refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
  apply Subtype.ext
  have h : (MvPolynomial.C r : MvPolynomial (Fin (n + 1)) K) ∈ polyGrading K n 0 :=
    MvPolynomial.isHomogeneous_C _ r
  simp [MMP.Intersection.renameGradedHom_apply, DirectSum.decompose_of_mem_same _ h]

open MMP.Resolution Stacks.AlgebraicGeometry in
/-- **Smooth blow-ups: `𝒪_V(E)` restricted to a fibre is `𝒪(-1)`.** Let `Y` be smooth over `k`,
and `Z = V(I)` an irreducible closed subscheme smooth over `k` of codimension `c ≥ 2`, with blow-up
`π : V ⟶ Y` and exceptional divisor `E`. For every `z ∈ Z` the fibre `π⁻¹(z)` of `E ⟶ Z` over `z`
is identified with `ℙ^{c-1}_{κ(z)}` over `κ(z)` so that `𝒪_V(E)|_{π⁻¹(z)} ≅ 𝒪_{ℙ^{c-1}}(-1)`. -/
@[mmp "lem_mmp_threefold_smooth_blowup_geometry"]
theorem exists_fiber_iso_projSpace_pullback_invertibleSheaf_exceptionalIdeal {k : Type u}
    [Field k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) (I : Y.IdealSheafData)
    (h : IsSmoothBlowup sY I) (hirr : IsIrreducible (I.support : Set Y))
    (hc : 2 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y)) :
    ∃ c : ℕ, (c : ℕ∞) =
        codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y) ∧
      ∀ z : I.subscheme,
        ∃ e : (exceptionalSubschemeMap I).fiber z ≅
            MMP.Intersection.ProjSpace (I.subscheme.residueField z) (ULift.{u} (Fin c)),
          e.hom ≫ MMP.Intersection.ProjSpace.toSpec (I.subscheme.residueField z) _ =
              (exceptionalSubschemeMap I).fiberToSpecResidueField z ∧
            Nonempty ((Scheme.Modules.pullback ((exceptionalSubschemeMap I).fiberι z ≫
                (exceptionalIdeal I).subschemeι)).obj
                  (Stacks.Divisors.invertibleSheaf' (exceptionalIdeal I)) ≅
              (Scheme.Modules.pullback e.hom).obj
                (ProjectiveSpectrum.Proj.twistingSheaf
                  (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin c))
                    (I.subscheme.residueField z)) (-1))) := by
  have : Smooth sY := smooth_of_isSmoothScheme' h.1
  have : Smooth (I.subschemeι ≫ sY) := smooth_of_isSmoothScheme' h.2
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : IsIntegral I.subscheme := isIntegral_subscheme_of_isIrreducible sY I h.2 hirr
  have hlf :=
    RegularIdealSheaf.isFiniteLocallyFree_conormalSheaf_of_isQuasiRegularImmersion I.subschemeι
      (isQuasiRegularImmersion_of_smooth_of_smooth sY I.subschemeι)
  have hlf1 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (Stacks.Conormal.conormalSheafDegreeOne I.subschemeι) :=
    Stacks.AlgebraicGeometry.isFiniteLocallyFree_of_iso (h := hlf)
      (Stacks.Conormal.conormalDegreeOneIso I.subschemeι)
  have hreg := isRegularImmersion_of_smooth_of_smooth I.subschemeι sY
  have hrank : ∀ z : I.subscheme,
      ((Scheme.Modules.fiberRank (Stacks.Conormal.conormalSheafDegreeOne I.subschemeι) z : ℕ) :
        ℕ∞) = codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y) := by
    intro z
    rw [← height_ker_stalkMap_subschemeι_eq_codimension I hirr z,
      ← fiberRank_conormalModule_eq_height I.subschemeι hreg z]
    exact congrArg _ (Scheme.Modules.fiberRank_eq_of_iso
      (Stacks.Conormal.immersionConormalSheafIsoDegreeOne (i := I.subschemeι)) z).symm
  obtain ⟨z₀⟩ : Nonempty I.subscheme := inferInstance
  set c := Scheme.Modules.fiberRank (Stacks.Conormal.conormalSheafDegreeOne I.subschemeι) z₀
  refine ⟨c, hrank z₀, fun z => ?_⟩
  have hcz : Scheme.Modules.fiberRank (Stacks.Conormal.conormalSheafDegreeOne I.subschemeι) z =
      c := by exact_mod_cast (hrank z).trans (hrank z₀).symm
  have hc2 : 2 ≤ c := by exact_mod_cast hc.trans_eq (hrank z₀).symm
  obtain ⟨n, hn⟩ : ∃ n, c = n + 1 := ⟨c - 1, by omega⟩
  rw [hn] at hcz ⊢
  obtain ⟨e₀, he₀, ⟨ι⟩⟩ := exists_fiber_iso_proj_pullback_invertibleSheaf sY I z n hcz
  set K := I.subscheme.residueField z
  refine ⟨e₀ ≪≫ (MMP.Intersection.ProjSpace.isoPolyGrading K n).symm, ?_, ⟨?_⟩⟩
  · rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, isoPolyGrading_inv_comp_toSpec, he₀]
  · have he : e₀.hom = (e₀ ≪≫ (MMP.Intersection.ProjSpace.isoPolyGrading K n).symm).hom ≫
        (MMP.Intersection.ProjSpace.isoPolyGrading K n).hom := by simp
    exact ι ≪≫ (Scheme.Modules.pullbackCongr he).app _ ≪≫
      ((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫
      (Scheme.Modules.pullback _).mapIso
        (MMP.Intersection.ProjSpace.twistingSheafIsoPullback K n (-1))

end MMP.Threefold.Resolution

end
