module

import MMP.AlgebraicGeometry.Intersection.EulerPolynomialGenericRank
import MMP.AlgebraicGeometry.Intersection.PairingSeparation
import MMP.AlgebraicGeometry.Cohomology.ProperCoherentSections
import StacksFrontier.AlgebraicGeometry.Cube.SectionNeighbourhood
import StacksFrontier.AlgebraicGeometry.Modules.ReducedFiniteLocallyFree
public import MMP.AlgebraicGeometry.Divisor.InvertibleSheafOfEffective
public import MMP.AlgebraicGeometry.Divisor.AmpleSectionDivisor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom
public import StacksFrontier.AlgebraicGeometry.Curves.GenusZeroPositiveDegree.PlaneConic
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistenceLevelIso
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.SectionPowerThickenings
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.GenericDominantDimensionFormula
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.CanonicalMap
public import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.ConnectedLocal
public import StacksFrontier.AlgebraicGeometry.Scheme.SpecQuotientInSite
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.ImmersionClosure
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.AsymptoticRiemannRoch
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.SectionFromCechVanishing
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheafMul
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheafSections

/-!
# Relative bigness over a projective target

This file proves a result of Kollár–Mori used in the proof of the base-point-free theorem.

**Relative bigness over a projective target.** Let `f : X ⟶ Y` be a morphism of projective
varieties over an algebraically closed field `k` of characteristic zero, and `D` a Cartier
divisor on `X`. Then `D` is `f`-big (the rank of `f_* 𝒪_X(kD)` at the generic point of `f(X)`
grows at least like `c kⁿ`, `n = dim X - dim f(X)`) if and only if some positive multiple `mD`
is linearly equivalent to `A + E`, with `A` an `f`-ample and `E` an effective Cartier divisor.
The proof passes to the generic fibre `X_η` over the generic point `η` of `f(X)`: the rank of
`f_* F` at `η` is `h⁰(X_η, F_η)`. For the forward direction a very ample `H` on `X` and the
growth bound on `H_η` give a non-zero section of `mD - H` on `X_η`; Serre generation on `Y` and
the projection formula lift it to a section of `mD - H + q f^* M`, whose divisor is `E`, and
`A = H - q f^* M`. For the converse an ample `L = A|_{X_η}` and the section of `E` inject
`𝒪(kL + rD)` into `𝒪((km + r)D)`, and Snapper's polynomial gives growth of degree `n`.

## Main results

* `MMP.Mori.isRelativelyBigCartier_iff_exists_linearlyEquivalent_add`: `D` is `f`-big iff
  `mD ∼ A + E` with `m > 0`, `A` `f`-ample and `E` effective.
* `MMP.Mori.exists_pos_relativeGenericRank_sub_of_isRelativelyBigCartier`: for `f` proper with
  integral source, of finite type over a field, and `D` `f`-big, some `mD - H` has non-zero
  generic rank; no projectivity of `X` or `Y` is needed.
* `MMP.Mori.relativeGenericRank_eq_finrank_fibre`: the generic rank of `f_* F` is `h⁰(X_η, F_η)`.
* `MMP.Mori.isIntegral_generic_fibre`: the generic fibre of a morphism with integral source is
  integral.
* `MMP.Intersection.exists_isDivisorOfSection`: a non-zero section of an invertible sheaf on an
  integral scheme has a divisor.
* `MMP.Mori.exists_isEffective_sheaf_iso_cartierSupport_of_ne_zero`: a non-zero section of an
  invertible sheaf `L` on an integral scheme gives an effective Cartier divisor `D` with
  `𝒪_X(D) ≅ L` whose support is the zero locus of the section;
  `MMP.Mori.exists_isEffective_sheaf_iso_of_ne_zero` forgets the support.
* `MMP.Mori.relativeGenericRank_morphismRestrict`: the generic rank of `f_* F` is unchanged by
  restricting `f` over an open `V` of the base with `f⁻¹ V` irreducible.
* `MMP.Mori.fiberRank_eq_zero_of_isZero`: a zero module has fibre rank zero.

## Implementation notes

`f`-bigness is `MMP.Mori.IsRelativelyBigCartier`; `A` is `f`-ample when its invertible sheaf
`𝒪_X(A)` is (`MMP.Mori.IsRelativelyAmple`); effectivity and linear equivalence are
`MMP.Intersection.IsEffective` and `MMP.Intersection.LinearlyEquivalent`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], proof of
  Theorem 3.3, 3.22–3.23
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u v

namespace MMP.Mori

section RelativeBig

open Opposite Limits TensorProduct

/-- The prime `𝔭 = g(ξ)` of the image of the generic point kills the image of `R` in the global
sections of an integral scheme. -/
private theorem ker_le {R : CommRingCat.{u}} {X : Scheme.{u}} [IsIntegral X] (g : X ⟶ Spec R) :
    ∀ a ∈ (g (genericPoint X)).asIdeal, ((Scheme.ΓSpecIso R).inv ≫ g.appTop).hom a = 0 := by
  intro a ha
  have hb : (Spec R).basicOpen ((Scheme.ΓSpecIso R).inv.hom a) = PrimeSpectrum.basicOpen a := by
    rw [basicOpen_eq_of_affine]
  apply eq_zero_of_basicOpen_eq_bot
  have h1 := Scheme.preimage_basicOpen g ((Scheme.ΓSpecIso R).inv.hom a)
  rw [hb] at h1
  have h2 : X.basicOpen (((Scheme.ΓSpecIso R).inv ≫ g.appTop).hom a) =
      g ⁻¹ᵁ PrimeSpectrum.basicOpen a := h1.symm
  rw [h2]
  by_contra hne
  have hne' : ((g ⁻¹ᵁ PrimeSpectrum.basicOpen a : X.Opens) : Set X).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]; intro h; apply hne; exact TopologicalSpace.Opens.ext h
  have := (genericPoint_spec X).mem_open_set_iff
    (U := (g ⁻¹ᵁ PrimeSpectrum.basicOpen a : X.Opens)) (g ⁻¹ᵁ PrimeSpectrum.basicOpen a).isOpen
  have hm := this.mpr (by simpa using hne')
  exact hm ha

/-- A morphism from an integral scheme to `Spec R` factors through `Spec (R ⧸ 𝔭)`, `𝔭` the
image of the generic point. -/
private noncomputable def toSpecQuot {R : CommRingCat.{u}} {X : Scheme.{u}} [IsIntegral X]
    (g : X ⟶ Spec R) : X ⟶ Spec (CommRingCat.of (R ⧸ (g (genericPoint X)).asIdeal)) :=
  (ΓSpec.adjunction.homEquiv X (op (CommRingCat.of (R ⧸ (g (genericPoint X)).asIdeal))))
    (CommRingCat.ofHom (Ideal.Quotient.lift _ ((Scheme.ΓSpecIso R).inv ≫ g.appTop).hom
      (ker_le g))).op

private theorem toSpecQuot_comp {R : CommRingCat.{u}} {X : Scheme.{u}} [IsIntegral X]
    (g : X ⟶ Spec R) :
    toSpecQuot g ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (g (genericPoint X)).asIdeal)) =
      g := by
  apply ext_to_Spec
  have h := ΓSpecIso_inv_ΓSpec_adjunction_homEquiv (X := X)
    (B := CommRingCat.of (R ⧸ (g (genericPoint X)).asIdeal))
    (CommRingCat.ofHom (Ideal.Quotient.lift _ ((Scheme.ΓSpecIso R).inv ≫ g.appTop).hom
      (ker_le g)))
  have h2 := Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (Ideal.Quotient.mk (g (genericPoint X)).asIdeal))
  change _ ≫ (toSpecQuot g ≫ _).appTop = _ ≫ g.appTop
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← h2, Category.assoc]
  change _ ≫ (toSpecQuot g).appTop = _ at h
  rw [h]
  ext a
  rfl

/-- The map `R ⟶ κ(x)` to the residue field of the point `x` of `Spec R`. -/
private noncomputable def resMap (R : CommRingCat.{u}) (x : Spec R) :
    R ⟶ (Spec R).residueField x :=
  CommRingCat.ofHom (algebraMap R x.asIdeal.ResidueField) ≫
    (Scheme.Spec.residueFieldIso R x).inv

private theorem map_resMap (R : CommRingCat.{u}) (x : Spec R) :
    Spec.map (resMap R x) = (Spec R).fromSpecResidueField x := by
  rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField R x, resMap, Spec.map_comp]

private theorem ker_resMap (R : CommRingCat.{u}) (x : Spec R) :
    RingHom.ker (resMap R x).hom = x.asIdeal := by
  have hk := Ideal.ker_algebraMap_residueField x.asIdeal
  have h1 : ∀ a : R, a ∈ x.asIdeal ↔ algebraMap R x.asIdeal.ResidueField a = 0 :=
    fun a => by rw [← RingHom.mem_ker, hk]
  let e := ((Scheme.Spec.residueFieldIso R x).symm.commRingCatIsoToRingEquiv)
  ext a
  rw [h1 a, RingHom.mem_ker]
  change e (algebraMap R _ a) = 0 ↔ _
  exact map_eq_zero_iff e e.injective

/-- The map `R ⧸ 𝔭 ⟶ κ(𝔭)`. -/
private noncomputable def resMapQuot (R : CommRingCat.{u}) (x : Spec R) :
    CommRingCat.of (R ⧸ x.asIdeal) ⟶ (Spec R).residueField x :=
  CommRingCat.ofHom (Ideal.Quotient.lift _ (resMap R x).hom (fun a ha => by
    rwa [← ker_resMap R x] at ha))

private theorem mk_comp_resMapQuot (R : CommRingCat.{u}) (x : Spec R) :
    CommRingCat.ofHom (Ideal.Quotient.mk x.asIdeal) ≫ resMapQuot R x = resMap R x := by
  ext a; rfl

private theorem spec_resMapQuot (R : CommRingCat.{u}) (x : Spec R) :
    Spec.map (resMapQuot R x) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk x.asIdeal)) =
      (Spec R).fromSpecResidueField x := by
  rw [← Spec.map_comp, mk_comp_resMapQuot]
  exact map_resMap R x

private theorem flat_resMapQuot (R : CommRingCat.{u}) (x : Spec R) :
    RingHom.Flat (resMapQuot R x).hom := by
  have : (resMapQuot R x).hom =
      ((Scheme.Spec.residueFieldIso R x).symm.commRingCatIsoToRingEquiv :
        x.asIdeal.ResidueField →+* _).comp
        (algebraMap (R ⧸ x.asIdeal) x.asIdeal.ResidueField) := by
    refine RingHom.ext fun a => ?_
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
    rfl
  rw [this]
  have h1 : RingHom.Flat (algebraMap (R ⧸ x.asIdeal) x.asIdeal.ResidueField) := by
    have := IsLocalization.flat x.asIdeal.ResidueField (nonZeroDivisors (R ⧸ x.asIdeal))
    exact this
  exact RingHom.Flat.comp h1 (RingHom.Flat.of_bijective
    ((Scheme.Spec.residueFieldIso R x).symm.commRingCatIsoToRingEquiv).bijective)

/-- Tensoring over `R` or over a quotient ring `A` of `R` gives the same `K`-module, `A` acting
compatibly on `K` and `M`. -/
private theorem tensor_quot_equiv {R A K M : Type*} [CommRing R] [CommRing A] [CommRing K]
    [AddCommGroup M] [Algebra R A] [Algebra A K] [Algebra R K] [IsScalarTower R A K]
    [Module R M] [Module A M] [IsScalarTower R A M] (h : Function.Surjective (algebraMap R A)) :
    Nonempty ((K ⊗[R] M) ≃ₗ[K] (K ⊗[A] M)) := by
  haveI : TensorProduct.CompatibleSMul R A K M := ⟨fun a k m => by
    obtain ⟨r, rfl⟩ := h a
    rw [algebraMap_smul, algebraMap_smul, TensorProduct.smul_tmul]⟩
  haveI : TensorProduct.CompatibleSMul A R K M := ⟨fun r k m => by
    rw [← algebraMap_smul A r k, ← algebraMap_smul A r m, TensorProduct.smul_tmul]⟩
  exact ⟨(TensorProduct.equivOfCompatibleSMul R A K K M).symm⟩

private theorem finrank_tensor_le_of_injective {O K N N' : Type*} [CommRing O] [Field K] [Algebra O
    K]
    (hs : Function.Surjective (algebraMap O K)) [AddCommGroup N] [Module O N]
    [AddCommGroup N'] [Module O N'] (φ : N →ₗ[O] N') (hφ : Function.Injective φ)
    (hN : ∀ a : O, algebraMap O K a = 0 → ∀ n : N, a • n = 0)
    (hN' : ∀ a : O, algebraMap O K a = 0 → ∀ n : N', a • n = 0) [Module.Finite O N'] :
    Module.finrank K (K ⊗[O] N) ≤ Module.finrank K (K ⊗[O] N') := by
  set I : Ideal O := RingHom.ker (algebraMap O K) with hI
  have h1 : Module.IsTorsionBySet O N (I : Set O) := fun n a => hN a (RingHom.mem_ker.1 a.2) n
  have h2 : Module.IsTorsionBySet O N' (I : Set O) := fun n a => hN' a (RingHom.mem_ker.1 a.2) n
  letI : Module (O ⧸ I) N := h1.module
  letI : Module (O ⧸ I) N' := h2.module
  haveI : IsScalarTower O (O ⧸ I) N := h1.isScalarTower
  haveI : IsScalarTower O (O ⧸ I) N' := h2.isScalarTower
  haveI : Module.Finite (O ⧸ I) N' := Module.Finite.of_restrictScalars_finite O (O ⧸ I) N'
  let A := O ⧸ I
  letI : Algebra A K := (Ideal.Quotient.lift I (algebraMap O K) (fun a ha => RingHom.mem_ker.1
      ha)).toAlgebra
  haveI : IsScalarTower O A K := IsScalarTower.of_algebraMap_eq (fun r => rfl)
  have hbij : Function.Bijective (algebraMap A K) := by
    refine ⟨?_, ?_⟩
    · rw [injective_iff_map_eq_zero]
      intro a ha
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
      have : algebraMap O K b = 0 := ha
      exact Ideal.Quotient.eq_zero_iff_mem.2 (RingHom.mem_ker.2 this)
    · intro k
      obtain ⟨b, hb⟩ := hs k
      exact ⟨Ideal.Quotient.mk I b, hb⟩
  haveI : Module.Flat A K := Module.Flat.of_linearEquiv (LinearEquiv.ofBijective (Algebra.linearMap
      A K) hbij).symm
  obtain ⟨e⟩ := tensor_quot_equiv (R := O) (A := A) (K := K) (M := N)
    (Ideal.Quotient.mk_surjective (I := I))
  obtain ⟨e'⟩ := tensor_quot_equiv (R := O) (A := A) (K := K) (M := N')
    (Ideal.Quotient.mk_surjective (I := I))
  rw [e.finrank_eq, e'.finrank_eq]
  let φA : N →ₗ[A] N' := LinearMap.extendScalarsOfSurjective (Ideal.Quotient.mk_surjective (I := I))
      φ
  have hinj : Function.Injective (φA.baseChange K) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap φA hφ
  exact LinearMap.finrank_le_finrank_of_injective hinj

/-- The fibre rank of `M^~` at `x` is the dimension of `κ(x) ⊗_R M`. -/
private theorem fiberRank_tilde (R : CommRingCat.{u}) (M : ModuleCat.{u} R)
    (x : PrimeSpectrum.Top R) :
    letI : Algebra ((structurePresheafInCommRingCat R).stalk x) ((Spec R).residueField x) :=
      ((Spec R).residue x).hom.toAlgebra
    letI : Algebra R ((Spec R).residueField x) :=
      ((algebraMap ((structurePresheafInCommRingCat R).stalk x) ((Spec R).residueField x)).comp
        (algebraMap R ((structurePresheafInCommRingCat R).stalk x))).toAlgebra
    Scheme.Modules.fiberRank (tilde M) x =
      Module.finrank ((Spec R).residueField x) (((Spec R).residueField x) ⊗[R] M) := by
  letI : Algebra ((structurePresheafInCommRingCat R).stalk x) ((Spec R).residueField x) :=
      ((Spec R).residue x).hom.toAlgebra
  letI : Algebra R ((Spec R).residueField x) :=
      ((algebraMap ((structurePresheafInCommRingCat R).stalk x) ((Spec R).residueField x)).comp
        (algebraMap R ((structurePresheafInCommRingCat R).stalk x))).toAlgebra
  haveI : IsScalarTower R ((structurePresheafInCommRingCat R).stalk x) ((Spec R).residueField x) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : Module ((structurePresheafInCommRingCat R).stalk x) ((tilde M).presheaf.stalk x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := (Spec R).presheaf) (tilde M).val x
  haveI : IsScalarTower R ((structurePresheafInCommRingCat R).stalk x) ((tilde M).presheaf.stalk x)
      :=
    (inferInstance : IsScalarTower R ((structurePresheafInCommRingCat R).stalk x)
      ↑(TopCat.Presheaf.stalk (moduleStructurePresheaf R M).presheaf x))
  have hbc : IsBaseChange ((structurePresheafInCommRingCat R).stalk x) (tilde.toStalk M x).hom :=
    IsLocalizedModule.isBaseChange x.asIdeal.primeCompl _ _
  unfold Scheme.Modules.fiberRank
  let e1 := hbc.equiv
  let e2 := (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl ((Spec R).residueField x) _)
    e1.symm) ≪≫ₗ (TensorProduct.AlgebraTensorModule.cancelBaseChange R
      ((structurePresheafInCommRingCat R).stalk x) ((Spec R).residueField x)
      ((Spec R).residueField x) M)
  exact e2.finrank_eq

section FiberRankCongr

variable {X : Scheme.{u}} {F G : X.Modules}

private lemma germM_smul' (M : X.Modules) (y : X) (W : X.Opens) (hy : y ∈ W) (r : Γ(X, W))
    (m : Γ(M, W)) :
    TopCat.Presheaf.germ M.val.presheaf W y hy (r • m) =
      X.presheaf.germ W y hy r • TopCat.Presheaf.germ M.val.presheaf W y hy m :=
  PresheafOfModules.germ_smul M.val y W hy r m

/-- The map on stalks (as abelian groups) induced by a morphism of modules. -/
private noncomputable def stalkMapAb (φ : F ⟶ G) (y : X) :
    TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf y ⟶
      TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf y :=
  (TopCat.Presheaf.stalkFunctor Ab.{u} y).map φ.mapPresheaf

private lemma stalkMapAb_germ (φ : F ⟶ G) (y : X) {W : X.Opens} (hy : y ∈ W) (ξ : Γ(F, W)) :
    stalkMapAb φ y (TopCat.Presheaf.germ F.val.presheaf W y hy ξ) =
      TopCat.Presheaf.germ G.val.presheaf W y hy (φ.app W ξ) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply W y hy φ.mapPresheaf ξ

private lemma stalkMapAb_smul (φ : F ⟶ G) (y : X) (ρ : X.presheaf.stalk y)
    (n : TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf y) :
    stalkMapAb φ y (ρ • n) = ρ • stalkMapAb φ y n := by
  obtain ⟨V, hyV, ξ, hξ⟩ := X.presheaf.exists_germ_eq ρ
  obtain ⟨W, hWV, hyW, ζ, hζ⟩ := TopCat.Presheaf.exists_le_germ_eq F.val.presheaf n hyV
  subst hξ
  subst hζ
  have key : ∀ (r : Γ(X, W)) (m : Γ(F, W)),
      stalkMapAb φ y (X.presheaf.germ W y hyW r •
          TopCat.Presheaf.germ F.val.presheaf W y hyW m) =
        X.presheaf.germ W y hyW r •
          stalkMapAb φ y (TopCat.Presheaf.germ F.val.presheaf W y hyW m) := by
    intro r m
    rw [← germM_smul' F y W hyW r m, stalkMapAb_germ φ y hyW,
      stalkMapAb_germ φ y hyW m, ← germM_smul' G y W hyW r (φ.app W m)]
    congr 1
    exact Scheme.Modules.Hom.app_smul φ r m
  rw [← X.presheaf.germ_res_apply (homOfLE hWV) y hyW ξ]
  exact key _ ζ

private lemma stalkMapAb_inv_hom (e : F ≅ G) (x : X)
    (n : TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :
    stalkMapAb e.inv x (stalkMapAb e.hom x n) = n := by
  obtain ⟨W, hW, ζ, rfl⟩ := TopCat.Presheaf.germ_exist F.val.presheaf n
  have h1 := stalkMapAb_germ e.hom x hW (ζ : Γ(F, W))
  have h2 := stalkMapAb_germ e.inv x hW (e.hom.app W (ζ : Γ(F, W)))
  have h3 : e.inv.app W (e.hom.app W (ζ : Γ(F, W))) = ζ :=
    ConcreteCategory.congr_hom (show e.hom.app W ≫ e.inv.app W = 𝟙 _ from by
      rw [← Scheme.Modules.Hom.comp_app, e.hom_inv_id]; rfl) ζ
  rw [h1, h2, h3]

/-- The fibre rank is invariant under isomorphism of modules. -/
private theorem fiberRank_congr (e : F ≅ G) (x : X) :
    Scheme.Modules.fiberRank F x = Scheme.Modules.fiberRank G x := by
  unfold Scheme.Modules.fiberRank
  let eS : TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x ≃ₗ[X.presheaf.stalk x]
      TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x :=
    { toFun := stalkMapAb e.hom x
      map_add' := map_add _
      map_smul' := fun ρ n => stalkMapAb_smul e.hom x ρ n
      invFun := stalkMapAb e.inv x
      left_inv := stalkMapAb_inv_hom e x
      right_inv := stalkMapAb_inv_hom e.symm x }
  exact (TensorProduct.AlgebraTensorModule.congr
    (LinearEquiv.refl (X.residueField x) _) eS).finrank_eq

private theorem stalkMapAb_injective (φ : F ⟶ G) [Mono φ] (y : X) :
    Function.Injective (stalkMapAb φ y) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨W, hW, ζ, rfl⟩ := TopCat.Presheaf.germ_exist F.val.presheaf a
  have ha' : TopCat.Presheaf.germ G.val.presheaf W y hW (φ.app W ζ) = 0 :=
    (stalkMapAb_germ φ y hW ζ).symm.trans ha
  have h0 : TopCat.Presheaf.germ G.val.presheaf W y hW (φ.app W ζ) =
      TopCat.Presheaf.germ G.val.presheaf W y hW 0 := by rw [ha', map_zero]
  obtain ⟨V, hyV, iU, iV, hUV⟩ := TopCat.Presheaf.germ_eq G.val.presheaf y hW hW _ _ h0
  have h1 := Stacks.AlgebraicGeometry.CardinalGeneration.app_map φ iU ζ
  have hUV' : (G.presheaf.map iU.op) (φ.app W ζ) = 0 := hUV.trans (map_zero _)
  rw [hUV'] at h1
  have h2 : F.val.presheaf.map iU.op ζ = 0 := by
    apply Stacks.AlgebraicGeometry.CardinalGeneration.injective_app_of_mono φ V
    exact h1.trans (map_zero _).symm
  rw [← TopCat.Presheaf.germ_res_apply F.val.presheaf iU y hyV ζ, h2, map_zero]

private theorem smul_zero_of_not_isUnit {Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X] (G : X.Modules)
    (a : Y.presheaf.stalk (f (genericPoint X))) (ha : ¬ IsUnit a)
    (n : ((Scheme.Modules.pushforward f).obj G).presheaf.stalk (f (genericPoint X))) :
    a • n = 0 := by
  have key : ∀ (W : Y.Opens) (hW : f (genericPoint X) ∈ W) (α : Γ(Y, W))
      (m : Γ(((Scheme.Modules.pushforward f).obj G), W)),
      ¬ IsUnit (Y.presheaf.germ W (f (genericPoint X)) hW α) →
      Y.presheaf.germ W (f (genericPoint X)) hW α •
        TopCat.Presheaf.germ ((Scheme.Modules.pushforward f).obj G).val.presheaf W
          (f (genericPoint X)) hW m = 0 := by
    intro W hW α m hna
    rw [← germM_smul']
    have hα' : f.app W α = 0 := by
      have hx : genericPoint X ∈ f ⁻¹ᵁ W := hW
      apply germ_injective_of_isIntegral X (genericPoint X) hx
      have h := congrArg (fun φ => φ α) (Scheme.Hom.germ_stalkMap f W (genericPoint X) hW)
      simp only [CategoryTheory.comp_apply] at h
      rw [map_zero, ← h]
      have hn2 : ¬ IsUnit (Scheme.Hom.stalkMap f (genericPoint X)
          (Y.presheaf.germ W (f (genericPoint X)) hW α)) :=
        fun hu => hna (IsLocalHom.map_nonunit _ hu)
      by_contra h0
      exact hn2 (isUnit_iff_ne_zero.2 (show (Scheme.Hom.stalkMap f (genericPoint X)
        (Y.presheaf.germ W (f (genericPoint X)) hW α) : X.functionField) ≠ 0 from h0))
    have h0 : α • m = 0 := by
      have h := (show α • m = (f.app W α) • (show Γ(G, f ⁻¹ᵁ W) from m) from rfl)
      rw [h, hα', zero_smul]
      rfl
    rw [h0]; exact map_zero _
  obtain ⟨V, hV, α, rfl⟩ := Y.presheaf.germ_exist a
  obtain ⟨V', hV', m, rfl⟩ := TopCat.Presheaf.germ_exist _ n
  have hW : f (genericPoint X) ∈ V ⊓ V' := ⟨hV, hV'⟩
  have e1 : (Y.presheaf.germ V _ hV) α =
      (Y.presheaf.germ (V ⊓ V') _ hW) (Y.presheaf.map (homOfLE inf_le_left).op α) :=
    (Y.presheaf.germ_res_apply (homOfLE inf_le_left) _ hW α).symm
  have e2 : TopCat.Presheaf.germ ((Scheme.Modules.pushforward f).obj G).val.presheaf V' _ hV' m =
      TopCat.Presheaf.germ ((Scheme.Modules.pushforward f).obj G).val.presheaf (V ⊓ V') _ hW
        (((Scheme.Modules.pushforward f).obj G).val.presheaf.map (homOfLE inf_le_right).op m) :=
    (TopCat.Presheaf.germ_res_apply _ (homOfLE inf_le_right) _ hW m).symm
  rw [e1] at ha ⊢
  erw [e2]
  exact key _ hW _ _ ha

end FiberRankCongr

/-- The fibre rank at `x` of a quasi-coherent module `G` on `Spec R` is the dimension of
`κ(x) ⊗_R Γ(G, ⊤)`. -/
private theorem fiberRank_of_isQuasicoherent (R : CommRingCat.{u}) (G : (Spec R).Modules)
    [G.IsQuasicoherent] (x : PrimeSpectrum.Top R) :
    letI : Algebra ((structurePresheafInCommRingCat R).stalk x) ((Spec R).residueField x) :=
      ((Spec R).residue x).hom.toAlgebra
    letI : Algebra R ((Spec R).residueField x) :=
      ((algebraMap ((structurePresheafInCommRingCat R).stalk x) ((Spec R).residueField x)).comp
        (algebraMap R ((structurePresheafInCommRingCat R).stalk x))).toAlgebra
    Scheme.Modules.fiberRank G x =
      Module.finrank ((Spec R).residueField x) (((Spec R).residueField x) ⊗[R]
        ((modulesSpecToSheaf.obj G).presheaf.obj (op ⊤))) := by
  have := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent G
  rw [← fiberRank_congr (asIso G.fromTildeΓ) x]
  exact fiberRank_tilde R _ x

private theorem finrank_eq_of_ringEquiv_addEquiv {K L : Type*} {M N : Type v} [Semiring K]
    [Semiring L] [AddCommMonoid M] [AddCommMonoid N] [Module K M] [Module L N] (i : K ≃+* L)
    (j : M ≃+ N) (hc : ∀ (r : K) (m : M), j (r • m) = i r • j m) :
    Module.finrank K M = Module.finrank L N := by
  unfold Module.finrank
  rw [rank_eq_of_equiv_equiv i j i.bijective hc]

private theorem finrank_tensor_congr {R : Type*} {K L M : Type v} [CommRing R] [CommRing K]
    [CommRing L] [Algebra R K] [Algebra R L] (τ : K ≃ₐ[R] L) [AddCommGroup M] [Module R M] :
    Module.finrank K (K ⊗[R] M) = Module.finrank L (L ⊗[R] M) := by
  refine finrank_eq_of_ringEquiv_addEquiv τ.toRingEquiv
    (TensorProduct.congr τ.toLinearEquiv (LinearEquiv.refl R M)).toAddEquiv ?_
  intro k x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a m => simp [TensorProduct.smul_tmul']
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

private theorem appLE_top_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (h : (⊤ : X.Opens) ≤ f ⁻¹ᵁ ⊤) :
    f.appLE ⊤ ⊤ h = f.appTop :=
  Scheme.Hom.appLE_eq_app f

private theorem baseModule_top_smul {Z W : Scheme.{u}} (h : Z ⟶ W) (M : Z.Modules)
    (b : Γ(W, ⊤)) (m : Γ(M, ⊤)) :
    letI := Stacks.AlgebraicGeometry.SectionsBaseChange.baseModule h M ⊤
    b • m = (h.appTop.hom b) • m := by
  show (h.appLE ⊤ ⊤ _).hom b • m = _
  rw [appLE_top_eq]

private theorem surjective_mk_appTop (R : CommRingCat.{u}) (x : Spec R) :
    Function.Surjective ((Scheme.ΓSpecIso R).inv ≫
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk x.asIdeal))).appTop).hom := by
  have h := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk x.asIdeal))
  have hs : Function.Surjective (CommRingCat.ofHom (Ideal.Quotient.mk x.asIdeal) ≫
      (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ x.asIdeal))).inv).hom :=
    (((Scheme.ΓSpecIso (CommRingCat.of (R ⧸
        x.asIdeal))).symm.commRingCatIsoToRingEquiv).surjective).comp
      (Ideal.Quotient.mk_surjective)
  rw [h] at hs
  exact hs

private theorem algebraMap_chain {R S : CommRingCat.{u}} (I : Ideal R) (ψ : CommRingCat.of (R ⧸ I) ⟶
    S) :
    (Scheme.ΓSpecIso R).inv ≫ (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).appTop ≫
      (Spec.map ψ).appTop = (CommRingCat.ofHom (Ideal.Quotient.mk I) ≫ ψ) ≫
        (Scheme.ΓSpecIso S).inv := by
  rw [← Scheme.Hom.comp_appTop, ← Spec.map_comp]
  exact (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk I) ≫ ψ)).symm

/-- For any flat field extension `ψ : R ⧸ 𝔭 → K` and any cartesian square over `Spec ψ`, the
sections of `F` pulled back to the corner have `K`-dimension `K ⊗_R Γ(X, F)`. -/
private theorem finrank_fibre_sections {R : CommRingCat.{u}} {X : Scheme.{u}} [IsIntegral X]
    [CompactSpace X] [QuasiSeparatedSpace X] (g : X ⟶ Spec R) (F : X.Modules)
    [F.IsQuasicoherent] {K : Type u} [Field K]
    (ψ : CommRingCat.of (R ⧸ (g (genericPoint X)).asIdeal) ⟶ CommRingCat.of K)
    (hψ : RingHom.Flat ψ.hom) {Fib : Scheme.{u}} (p : Fib ⟶ X)
    (k : Fib ⟶ Spec (CommRingCat.of K))
    (H : IsPullback p k (toSpecQuot g) (Spec.map ψ)) :
    letI : Algebra R K :=
      (CommRingCat.ofHom (Ideal.Quotient.mk (g (genericPoint X)).asIdeal) ≫ ψ).hom.toAlgebra
    letI : Module R Γ(F, ⊤) := Module.compHom _ ((Scheme.ΓSpecIso R).inv ≫ g.appTop).hom
    Module.finrank K (cohomologyOverField K k ((Scheme.Modules.pullback p).obj F) 0) =
    Module.finrank K (K ⊗[R] Γ(F, ⊤)) := by
  have hflat : Flat (Spec.map ψ) := (HasRingHomProperty.Spec_iff (P := @Flat)).mpr hψ
  obtain ⟨e, he⟩ :=
      Stacks.AlgebraicGeometry.SectionsBaseChange.exists_linearEquiv_sections_baseChange
    H F
  have P1 : Module.finrank (CommRingCat.of K)
      (cohomologyOverField (CommRingCat.of K)
        k
        ((Scheme.Modules.pullback p).obj F) 0) =
      letI := Stacks.AlgebraicGeometry.SectionsBaseChange.baseModule
          k
          ((Scheme.Modules.pullback p).obj F) ⊤
      Module.finrank Γ(Spec (CommRingCat.of K), ⊤)
        Γ((Scheme.Modules.pullback p).obj F, ⊤) := by
    refine ((cohomologyOverFieldZeroIsoSections _ _ _).toLinearEquiv.finrank_eq).trans ?_
    letI := Stacks.AlgebraicGeometry.SectionsBaseChange.baseModule
          k
          ((Scheme.Modules.pullback p).obj F) ⊤
    refine finrank_eq_of_ringEquiv_addEquiv
      ((Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv)
      (AddEquiv.refl _) ?_
    intro r m
    simp only [AddEquiv.refl_apply]
    refine Eq.trans ?_ (baseModule_top_smul k _ _ m).symm
    rfl
  letI algκ : Algebra R (CommRingCat.of K) :=
    (CommRingCat.ofHom (Ideal.Quotient.mk (g (genericPoint X)).asIdeal) ≫ ψ).hom.toAlgebra
  letI algRB : Algebra R Γ(Spec (CommRingCat.of (R ⧸ (g (genericPoint X)).asIdeal)), ⊤) :=
    ((Scheme.ΓSpecIso R).inv ≫
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (g (genericPoint
          X)).asIdeal))).appTop).hom.toAlgebra
  letI algBL := Stacks.AlgebraicGeometry.SectionsBaseChange.baseAlgebra
    (Spec.map ψ)
  letI algRL : Algebra R Γ(Spec (CommRingCat.of K), ⊤) :=
    ((algebraMap _ Γ(Spec (CommRingCat.of K), ⊤)).comp
      (algebraMap R Γ(Spec (CommRingCat.of (R ⧸ (g (genericPoint X)).asIdeal)), ⊤))).toAlgebra
  haveI : IsScalarTower R Γ(Spec (CommRingCat.of (R ⧸ (g (genericPoint X)).asIdeal)), ⊤)
      Γ(Spec (CommRingCat.of K), ⊤) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI modBF := Stacks.AlgebraicGeometry.SectionsBaseChange.baseModule (toSpecQuot g) F ⊤
  letI modRF : Module R Γ(F, ⊤) := Module.compHom _ ((Scheme.ΓSpecIso R).inv ≫ g.appTop).hom
  have key : (Scheme.ΓSpecIso R).inv ≫
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (g (genericPoint X)).asIdeal))).appTop ≫
        (toSpecQuot g).appTop = (Scheme.ΓSpecIso R).inv ≫ g.appTop := by
    rw [← Scheme.Hom.comp_appTop, toSpecQuot_comp]
  haveI tower : IsScalarTower R Γ(Spec (CommRingCat.of (R ⧸ (g (genericPoint X)).asIdeal)), ⊤)
      Γ(F, ⊤) := ⟨fun r b m => by
    have h1 := baseModule_top_smul (toSpecQuot g) F (r • b) m
    have h2 := baseModule_top_smul (toSpecQuot g) F b m
    have hr : (toSpecQuot g).appTop.hom (algebraMap R _ r) =
        ((Scheme.ΓSpecIso R).inv ≫ g.appTop).hom r := by
      rw [← key]; rfl
    rw [h1, h2, Algebra.smul_def, map_mul, mul_smul, hr]
    rfl⟩
  obtain ⟨eq⟩ := tensor_quot_equiv (R := R)
    (A := Γ(Spec (CommRingCat.of (R ⧸ (g (genericPoint X)).asIdeal)), ⊤))
    (K := Γ(Spec (CommRingCat.of K), ⊤)) (M := Γ(F, ⊤))
    (surjective_mk_appTop R (g (genericPoint X)))
  have hcomm : ∀ r : R,
      (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv
        (algebraMap R (CommRingCat.of K) r) =
      algebraMap R Γ(Spec (CommRingCat.of K), ⊤) r := by
    intro r
    have h := congrArg (fun φ => φ.hom r) (algebraMap_chain (g (genericPoint X)).asIdeal ψ)
    show _ = ((Spec.map ψ).appLE ⊤ ⊤ _).hom _
    rw [appLE_top_eq]
    exact h.symm
  let τ : (CommRingCat.of K) ≃ₐ[R]
      Γ(Spec (CommRingCat.of K), ⊤) :=
    AlgEquiv.ofRingEquiv hcomm
  letI modLG := Stacks.AlgebraicGeometry.SectionsBaseChange.baseModule
    k
    ((Scheme.Modules.pullback p).obj F) ⊤
  exact P1.trans (e.finrank_eq.symm.trans (eq.finrank_eq.symm.trans
    (finrank_tensor_congr τ).symm))

private theorem finrank_tensor_inst_congr {R K N : Type*} [CommRing R] [CommRing K]
    [AddCommGroup N] (alg1 alg2 : Algebra R K) (m1 m2 : Module R N) (hA : alg1 = alg2)
    (hM : m1 = m2) :
    (letI := alg1; letI := m1; Module.finrank K (K ⊗[R] N)) =
      (letI := alg2; letI := m2; Module.finrank K (K ⊗[R] N)) := by
  subst hA hM
  rfl

private theorem alg_eq (R : CommRingCat.{u}) (x : PrimeSpectrum.Top R) :
    letI : Algebra ((structurePresheafInCommRingCat R).stalk x) ((Spec R).residueField x) :=
      ((Spec R).residue x).hom.toAlgebra
    ((algebraMap ((structurePresheafInCommRingCat R).stalk x) ((Spec R).residueField x)).comp
        (algebraMap R ((structurePresheafInCommRingCat R).stalk x))) = (resMap R x).hom := by
  ext r
  have := congrArg (fun φ => φ.hom r) (Scheme.Spec.algebraMap_residueFieldIso_inv R x)
  exact this.symm

private theorem isPullback_of_factor {C : Type*} [Category C] {P X' T S R' : C} (ι : S ⟶ R')
    [Mono ι] (g' : X' ⟶ S) (p : P ⟶ X') (k : P ⟶ T) (q : T ⟶ S)
    (H : IsPullback p k (g' ≫ ι) (q ≫ ι)) : IsPullback p k g' q := by
  have hmono : IsPullback (𝟙 X') g' (g' ≫ ι) ι := IsPullback.of_horiz_isIso_mono ⟨by simp⟩
  refine IsPullback.of_right (h₁₂ := 𝟙 X') (v₁₂ := g') (v₁₃ := g' ≫ ι) (h₂₂ := ι) ?_ ?_ hmono
  · simpa using H
  · refine (cancel_mono ι).1 ?_
    simpa using H.w

/-- The map `Spec κ(j z) ⟶ Spec R` through the open immersion `j : Spec R ⟶ Y`. -/
private noncomputable def resGamma {Y : Scheme.{u}} {R : CommRingCat.{u}} (j : Spec R ⟶ Y)
    [IsOpenImmersion j] (z : Spec R) : Spec (Y.residueField (j z)) ⟶ Spec R :=
  Spec.map (inv (j.residueFieldMap z)) ≫ (Spec R).fromSpecResidueField z

private theorem resGamma_comp {Y : Scheme.{u}} {R : CommRingCat.{u}} (j : Spec R ⟶ Y)
    [IsOpenImmersion j] (z : Spec R) : resGamma j z ≫ j = Y.fromSpecResidueField (j z) := by
  rw [resGamma, Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
    ← Spec.map_comp_assoc]
  simp

/-- The generic fibre of `f` over `j z` is the fibre over `z` of the base change of `f` along the
open immersion `j`. -/
private theorem isPullback_fiber_open {X Y : Scheme.{u}} (f : X ⟶ Y) {R : CommRingCat.{u}}
    (j : Spec R ⟶ Y) [IsOpenImmersion j] (z : Spec R) :
    IsPullback (pullback.lift (f.fiberι (j z)) (f.fiberToSpecResidueField (j z) ≫ resGamma j z)
        (by rw [Category.assoc, resGamma_comp]; exact Scheme.Hom.fiber_fac f (j z)))
      (f.fiberToSpecResidueField (j z)) (pullback.snd f j) (resGamma j z) := by
  refine IsPullback.of_right (h₁₂ := pullback.fst f j) ?_
    (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f j)
  rw [pullback.lift_fst, resGamma_comp]
  exact IsPullback.of_hasPullback f _

/-- The ring map `R ⧸ 𝔭 ⟶ κ(j z)`. -/
private noncomputable def psiK {Y : Scheme.{u}} {R : CommRingCat.{u}} (j : Spec R ⟶ Y)
    [IsOpenImmersion j] (z : Spec R) :
    CommRingCat.of (R ⧸ z.asIdeal) ⟶ Y.residueField (j z) :=
  resMapQuot R z ≫ inv (j.residueFieldMap z)

private theorem spec_psiK {Y : Scheme.{u}} {R : CommRingCat.{u}} (j : Spec R ⟶ Y)
    [IsOpenImmersion j] (z : Spec R) :
    Spec.map (psiK j z) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk z.asIdeal)) =
      resGamma j z := by
  rw [psiK, Spec.map_comp, Category.assoc, spec_resMapQuot]
  rfl

private theorem flat_psiK {Y : Scheme.{u}} {R : CommRingCat.{u}} (j : Spec R ⟶ Y)
    [IsOpenImmersion j] (z : Spec R) : RingHom.Flat (psiK j z).hom := by
  rw [psiK]
  exact RingHom.Flat.comp (flat_resMapQuot R z)
    (RingHom.Flat.of_bijective (asIso (inv (j.residueFieldMap
        z))).commRingCatIsoToRingEquiv.bijective)

/-- The base change of `f` along `j`, as a scheme. -/
private noncomputable abbrev bcScheme {X Y Z : Scheme.{u}} (f : X ⟶ Y) (j : Z ⟶ Y) : Scheme.{u} :=
    pullback f j

/-- The generic fibre of `f` over `j z`, `z` the image of the generic point of `X ×_Y Spec R`, is
the base change of the factorisation of `X ×_Y Spec R ⟶ Spec R` through `Spec (R ⧸ 𝔭)` along the
flat map `Spec κ(j z) ⟶ Spec (R ⧸ 𝔭)`. -/
private theorem isPullback_fiber_toSpecQuot {X Y : Scheme.{u}} (f : X ⟶ Y) {R : CommRingCat.{u}}
    (j : Spec R ⟶ Y) [IsOpenImmersion j] [IsIntegral (bcScheme f j)] :
    IsPullback
      (pullback.lift (f.fiberι (j ((pullback.snd f j) (genericPoint (bcScheme f j)))))
        (f.fiberToSpecResidueField (j ((pullback.snd f j) (genericPoint (bcScheme f j)))) ≫
          resGamma j ((pullback.snd f j) (genericPoint (bcScheme f j))))
        (by rw [Category.assoc, resGamma_comp]; exact Scheme.Hom.fiber_fac f _))
      (f.fiberToSpecResidueField (j ((pullback.snd f j) (genericPoint (bcScheme f j)))))
      (toSpecQuot (pullback.snd f j))
      (Spec.map (psiK j ((pullback.snd f j) (genericPoint (bcScheme f j))))) := by
  refine isPullback_of_factor (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
    ((pullback.snd f j) (genericPoint (bcScheme f j))).asIdeal))) _ _ _ _ ?_
  rw [toSpecQuot_comp, spec_psiK]
  exact isPullback_fiber_open f j _

/-- The dimension of the sections on the generic fibre of `f` over `j z`, computed on the base
change `X' = X ×_Y Spec R` along an affine open immersion `j`. -/
private theorem finrank_fibre_via_open {X Y : Scheme.{u}} (f : X ⟶ Y) {R : CommRingCat.{u}}
    (j : Spec R ⟶ Y) [IsOpenImmersion j] [IsIntegral (bcScheme f j)]
    [CompactSpace (bcScheme f j)] [QuasiSeparatedSpace (bcScheme f j)]
    (F : X.Modules) [F.IsQuasicoherent] :
    letI z := (pullback.snd f j) (genericPoint (bcScheme f j))
    letI : Algebra R (Y.residueField (j z)) :=
      (CommRingCat.ofHom (Ideal.Quotient.mk z.asIdeal) ≫ psiK j z).hom.toAlgebra
    letI : Module R Γ((Scheme.Modules.restrictFunctor (pullback.fst f j)).obj F, ⊤) :=
      Module.compHom _ ((Scheme.ΓSpecIso R).inv ≫ (pullback.snd f j).appTop).hom
    Module.finrank (Y.residueField (j z))
      (cohomologyOverField (Y.residueField (j z)) (f.fiberToSpecResidueField (j z))
        ((Scheme.Modules.pullback (f.fiberι (j z))).obj F) 0) =
    Module.finrank (Y.residueField (j z))
      (Y.residueField (j z) ⊗[R] Γ((Scheme.Modules.restrictFunctor (pullback.fst f j)).obj F, ⊤)) :=
          by
  haveI : ((Scheme.Modules.restrictFunctor (pullback.fst f j)).obj F).IsQuasicoherent :=
    inferInstance
  have H := isPullback_fiber_toSpecQuot f j
  have h := finrank_fibre_sections (pullback.snd f j)
    ((Scheme.Modules.restrictFunctor (pullback.fst f j)).obj F) (psiK j _) (flat_psiK j _) _ _ H
  have hobj : (Scheme.Modules.pullback (pullback.lift
      (f.fiberι (j ((pullback.snd f j) (genericPoint (bcScheme f j)))))
      (f.fiberToSpecResidueField (j ((pullback.snd f j) (genericPoint (bcScheme f j)))) ≫
        resGamma j ((pullback.snd f j) (genericPoint (bcScheme f j))))
      (by rw [Category.assoc, resGamma_comp]; exact Scheme.Hom.fiber_fac f _) ≫
        pullback.fst f j)).obj F =
      (Scheme.Modules.pullback
        (f.fiberι (j ((pullback.snd f j) (genericPoint (bcScheme f j)))))).obj F := by
    rw [pullback.lift_fst]
  let e : (Scheme.Modules.pullback (pullback.lift
      (f.fiberι (j ((pullback.snd f j) (genericPoint (bcScheme f j)))))
      (f.fiberToSpecResidueField (j ((pullback.snd f j) (genericPoint (bcScheme f j)))) ≫
        resGamma j ((pullback.snd f j) (genericPoint (bcScheme f j))))
      (by rw [Category.assoc, resGamma_comp]; exact Scheme.Hom.fiber_fac f _))).obj
      ((Scheme.Modules.restrictFunctor (pullback.fst f j)).obj F) ≅
      (Scheme.Modules.pullback
        (f.fiberι (j ((pullback.snd f j) (genericPoint (bcScheme f j)))))).obj F :=
    ((Scheme.Modules.pullback _).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback (pullback.fst f j)).app F)) ≪≫
      ((Scheme.Modules.pullbackComp _ _).app F) ≪≫ eqToIso hobj
  exact (finrank_cohomologyOverField_eq_of_iso _ _ e.symm 0).trans h

private noncomputable def openResidueRingEquiv {Z Y : Scheme.{u}} (j : Z ⟶ Y)
    [IsOpenImmersion j] (z : Z) : Y.residueField (j z) ≃+* Z.residueField z :=
  haveI : IsIso (j.residueFieldMap z) := Scheme.instIsIsoCommRingCatResidueFieldMapOfIsOpenImmersion
      j z
  (asIso (j.residueFieldMap z)).commRingCatIsoToRingEquiv

private theorem image_fst_top {X Y : Scheme.{u}} (f : X ⟶ Y) {Z : Scheme.{u}} (j : Z ⟶ Y)
    [IsOpenImmersion j] :
    (pullback.fst f j) ''ᵁ ⊤ = f ⁻¹ᵁ (j ''ᵁ ⊤) := by
  ext x
  simp only [Scheme.Hom.coe_image, Scheme.Hom.coe_preimage, TopologicalSpace.Opens.coe_top,
    Set.image_univ, Set.mem_preimage]
  rw [Scheme.Pullback.range_fst]
  rfl

private theorem appLE_congr_hom {A B : Scheme.{u}} {u v : A ⟶ B} (h : u = v) (U : B.Opens)
    (V : A.Opens) (e : V ≤ u ⁻¹ᵁ U) (e' : V ≤ v ⁻¹ᵁ U) : u.appLE U V e = v.appLE U V e' := by
  subst h; rfl

/-- The ring-level compatibility of the pullback square along an open immersion. -/
private theorem scalar_compat {X Y : Scheme.{u}} (f : X ⟶ Y) {Z : Scheme.{u}} (j : Z ⟶ Y)
    [IsOpenImmersion j] (W : X.Opens) (hW : W ≤ f ⁻¹ᵁ (j ''ᵁ ⊤))
    (hW' : (⊤ : (pullback f j).Opens) ≤ (pullback.fst f j) ⁻¹ᵁ W) :
    (j.appIso ⊤).inv ≫ f.appLE (j ''ᵁ ⊤) W hW ≫ (pullback.fst f j).appLE W ⊤ hW' =
      (pullback.snd f j).appTop := by
  rw [Scheme.Hom.appLE_comp_appLE,
    appLE_congr_hom (pullback.condition (f := f) (g := j)) _ _ _
      (e' := fun x hx => by simp), Scheme.Hom.comp_appLE, Scheme.Hom.appIso_inv_app_assoc]
  rw [Scheme.Hom.map_appLE' _ _ (Scheme.Hom.preimage_image_eq j ⊤)]
  all_goals first | exact appLE_top_eq _ _ | exact le_top | simp

/-- The `R`-linear identification of the sections of the restriction of `f_* F` to `Spec R` with
the sections of the restriction of `F` to the base change `X ×_Y Spec R`. -/
private noncomputable def sectionsEquiv {X Y : Scheme.{u}} (f : X ⟶ Y) {R : CommRingCat.{u}}
    (j : Spec R ⟶ Y) [IsOpenImmersion j] (F : X.Modules) :
    letI : Module R Γ((Scheme.Modules.restrictFunctor (pullback.fst f j)).obj F, ⊤) :=
      Module.compHom _ ((Scheme.ΓSpecIso R).inv ≫ (pullback.snd f j).appTop).hom
    ((modulesSpecToSheaf.obj ((Scheme.Modules.restrictFunctor j).obj
      ((Scheme.Modules.pushforward f).obj F))).presheaf.obj (op ⊤)) ≃ₗ[R]
      Γ((Scheme.Modules.restrictFunctor (pullback.fst f j)).obj F, ⊤) :=
  letI : Module R Γ((Scheme.Modules.restrictFunctor (pullback.fst f j)).obj F, ⊤) :=
    Module.compHom _ ((Scheme.ΓSpecIso R).inv ≫ (pullback.snd f j).appTop).hom
  { toFun := fun x => (F.presheaf.map (homOfLE (image_fst_top f j).le).op).hom x
    map_add' := fun x y => map_add _ _ _
    map_smul' := fun r x => by
      have h1 : r • x = (f.app (j ''ᵁ ⊤) ((j.appIso ⊤).inv ((Scheme.ΓSpecIso R).inv r))) •
          (show F.presheaf.obj (op (f ⁻¹ᵁ (j ''ᵁ ⊤))) from x) := rfl
      have h2 : ∀ y : F.presheaf.obj (op ((pullback.fst f j) ''ᵁ ⊤)),
          (RingHom.id R) r • (show Γ((Scheme.Modules.restrictFunctor (pullback.fst f j)).obj F, ⊤)
            from y) =
          (((pullback.fst f j).appIso ⊤).inv ((pullback.snd f j).appTop
            ((Scheme.ΓSpecIso R).inv r))) • y := fun y => rfl
      have h3 := Scheme.Modules.map_smul F (homOfLE (image_fst_top f j).le)
        (f.app (j ''ᵁ ⊤) ((j.appIso ⊤).inv ((Scheme.ΓSpecIso R).inv r))) x
      have hsc : X.presheaf.map (homOfLE (image_fst_top f j).le).op
          (f.app (j ''ᵁ ⊤) ((j.appIso ⊤).inv ((Scheme.ΓSpecIso R).inv r))) =
          ((pullback.fst f j).appIso ⊤).inv ((pullback.snd f j).appTop
            ((Scheme.ΓSpecIso R).inv r)) := by
        have h := congrArg (fun φ => CommRingCat.Hom.hom φ ((Scheme.ΓSpecIso R).inv r))
          (scalar_compat f j ((pullback.fst f j) ''ᵁ ⊤) (image_fst_top f j).le
            (Scheme.Hom.preimage_image_eq _ _).ge)
        apply ((pullback.fst f j).appIso ⊤).commRingCatIsoToRingEquiv.injective
        show ((pullback.fst f j).appIso ⊤).hom _ =
          ((pullback.fst f j).appIso ⊤).hom (((pullback.fst f j).appIso ⊤).inv _)
        rw [Iso.inv_hom_id_apply, Scheme.Hom.appIso_hom']
        exact h
      show (F.presheaf.map (homOfLE (image_fst_top f j).le).op).hom (r • x) = _
      rw [h1, h3, h2, hsc]
    invFun := fun y => (F.presheaf.map (homOfLE (image_fst_top f j).ge).op).hom y
    left_inv := fun x =>
      ConcreteCategory.congr_hom (show F.presheaf.map (homOfLE (image_fst_top f j).le).op ≫
        F.presheaf.map (homOfLE (image_fst_top f j).ge).op = 𝟙 _ by
          rw [← F.presheaf.map_comp,
            show (homOfLE (image_fst_top f j).le).op ≫ (homOfLE (image_fst_top f j).ge).op = 𝟙 _
              from Subsingleton.elim _ _, F.presheaf.map_id]) x
    right_inv := fun y =>
      ConcreteCategory.congr_hom (show F.presheaf.map (homOfLE (image_fst_top f j).ge).op ≫
        F.presheaf.map (homOfLE (image_fst_top f j).le).op = 𝟙 _ by
          rw [← F.presheaf.map_comp,
            show (homOfLE (image_fst_top f j).ge).op ≫ (homOfLE (image_fst_top f j).le).op = 𝟙 _
              from Subsingleton.elim _ _, F.presheaf.map_id]) y }

/-- Over an affine open immersion `j : Spec R ⟶ Y`, the fibre rank of `f_* F` at `j z` equals the
`κ(j z)`-dimension of `κ(j z) ⊗_R Γ(X ×_Y Spec R, F)`. -/
private theorem fiberRank_pushforward_via_open {X Y : Scheme.{u}} (f : X ⟶ Y) {R : CommRingCat.{u}}
    (j : Spec R ⟶ Y) [IsOpenImmersion j] [IsIntegral (bcScheme f j)] [QuasiCompact f]
    [QuasiSeparated f] (F : X.Modules) [F.IsQuasicoherent] :
    letI z := (pullback.snd f j) (genericPoint (bcScheme f j))
    letI : Algebra R (Y.residueField (j z)) :=
      (CommRingCat.ofHom (Ideal.Quotient.mk z.asIdeal) ≫ psiK j z).hom.toAlgebra
    letI : Module R Γ((Scheme.Modules.restrictFunctor (pullback.fst f j)).obj F, ⊤) :=
      Module.compHom _ ((Scheme.ΓSpecIso R).inv ≫ (pullback.snd f j).appTop).hom
    Scheme.Modules.fiberRank ((Scheme.Modules.pushforward f).obj F) (j z) =
      Module.finrank (Y.residueField (j z))
        (Y.residueField (j z) ⊗[R] Γ((Scheme.Modules.restrictFunctor (pullback.fst f j)).obj F, ⊤))
            := by
  haveI : ((Scheme.Modules.pushforward f).obj F).IsQuasicoherent :=
    AlgebraicGeometry.ProperCoherentFiniteType.isQuasicoherent_pushforward f F inferInstance
  rw [← Stacks.FiniteLocallyFree.Reduced.fiberRank_restrict j
    ((Scheme.Modules.pushforward f).obj F) ((pullback.snd f j) (genericPoint (bcScheme f j)))]
  rw [fiberRank_of_isQuasicoherent R ((Scheme.Modules.restrictFunctor j).obj
    ((Scheme.Modules.pushforward f).obj F)) ((pullback.snd f j) (genericPoint (bcScheme f j)))]
  generalize hz : (pullback.snd f j) (genericPoint (bcScheme f j)) = z
  letI algR : Algebra R ((Spec R).residueField z) := (resMap R z).hom.toAlgebra
  letI alg2 : Algebra R (Y.residueField (j z)) :=
    (CommRingCat.ofHom (Ideal.Quotient.mk z.asIdeal) ≫ psiK j z).hom.toAlgebra
  letI modM2 : Module R Γ((Scheme.Modules.restrictFunctor (pullback.fst f j)).obj F, ⊤) :=
    Module.compHom _ ((Scheme.ΓSpecIso R).inv ≫ (pullback.snd f j).appTop).hom
  have hcomm : ∀ r : R, (openResidueRingEquiv j z).symm (algebraMap R ((Spec R).residueField z) r) =
      algebraMap R (Y.residueField (j z)) r := fun r => by
    haveI : IsIso (j.residueFieldMap z) :=
        Scheme.instIsIsoCommRingCatResidueFieldMapOfIsOpenImmersion j z
    show (inv (j.residueFieldMap z)).hom ((resMap R z).hom r) =
      (CommRingCat.ofHom (Ideal.Quotient.mk z.asIdeal) ≫ psiK j z).hom r
    rw [psiK, ← Category.assoc, mk_comp_resMapQuot]
    rfl
  let τ : ((Spec R).residueField z) ≃ₐ[R] (Y.residueField (j z)) :=
    AlgEquiv.ofRingEquiv hcomm
  have hΘ := sectionsEquiv f j F
  refine (finrank_tensor_inst_congr (N := ((modulesSpecToSheaf.obj
      ((Scheme.Modules.restrictFunctor j).obj ((Scheme.Modules.pushforward f).obj F))).presheaf.obj
        (op ⊤))) _ algR inferInstance inferInstance ?_ rfl).trans ?_
  · exact Algebra.algebra_ext _ _ (fun r => by
      have := congrArg (fun φ => φ r) (alg_eq R z)
      exact this)
  · exact ((TensorProduct.AlgebraTensorModule.congr
      (LinearEquiv.refl ((Spec R).residueField z) _) hΘ).finrank_eq).trans
      (finrank_tensor_congr τ)

/-- **The generic rank is local on the base.** For `f : X ⟶ Y` with `X` irreducible and an open
`V ⊆ Y` with `f⁻¹ V` irreducible, the generic rank of `(f ∣_ V)_* (F|_{f⁻¹ V})` equals that of
`f_* F`. -/
theorem relativeGenericRank_morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens)
    [IrreducibleSpace X] [IrreducibleSpace (f ⁻¹ᵁ V)] (F : X.Modules) :
    relativeGenericRank (f ∣_ V) ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F) =
      relativeGenericRank f F := by
  have hpt : V.ι ((f ∣_ V) (genericPoint (f ⁻¹ᵁ V))) = f (genericPoint X) := by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply,
      genericPoint_eq_of_isOpenImmersion]
  unfold relativeGenericRank
  exact (fiberRank_congr
    ((Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso f V).app F) _).symm.trans
    ((Stacks.FiniteLocallyFree.Reduced.fiberRank_restrict V.ι _ _).trans (by rw [hpt]))

/-- An affine chart `j : Spec R ⟶ Y` around the image of the generic point of an integral `X`,
over which the base change `X ×_Y Spec R` is integral with generic point over `f (genericPoint X)`.
-/
private theorem exists_affine_chart_genericPoint {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X] :
    ∃ (R : CommRingCat.{u}) (j : Spec R ⟶ Y) (_ : IsOpenImmersion j)
      (_ : IsIntegral (bcScheme f j)),
      f (genericPoint X) = j ((pullback.snd f j) (genericPoint (bcScheme f j))) := by
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset
    (x := f (genericPoint X)) (U := ⊤) trivial
  haveI : IsOpenImmersion hV.fromSpec := hV.isOpenImmersion_fromSpec
  obtain ⟨x', -⟩ : genericPoint X ∈ Set.range (pullback.fst f hV.fromSpec) := by
    rwa [Scheme.Pullback.range_fst, hV.range_fromSpec]
  haveI : Nonempty (bcScheme f hV.fromSpec) := ⟨x'⟩
  haveI : IsIntegral (bcScheme f hV.fromSpec) :=
    isIntegral_of_isOpenImmersion (pullback.fst f hV.fromSpec)
  refine ⟨_, hV.fromSpec, inferInstance, inferInstance, ?_⟩
  rw [← genericPoint_eq_of_isOpenImmersion (pullback.fst f hV.fromSpec), ← Scheme.Hom.comp_apply,
    pullback.condition, Scheme.Hom.comp_apply]

/-- **Generic rank as sections on the generic fibre.** For an integral `X` and a quasi-compact
quasi-separated `f`, the generic rank of `f_* F` is the `κ(η)`-dimension of the global sections of
the restriction of a quasi-coherent `F` to the generic fibre `X_η`. -/
theorem relativeGenericRank_eq_finrank_fibre {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegral X] [QuasiCompact f] [QuasiSeparated f] (F : X.Modules) [F.IsQuasicoherent] :
    relativeGenericRank f F = Module.finrank (Y.residueField (f (genericPoint X)))
      (cohomologyOverField (Y.residueField (f (genericPoint X)))
        (f.fiberToSpecResidueField (f (genericPoint X)))
        ((Scheme.Modules.pullback (f.fiberι (f (genericPoint X)))).obj F) 0) := by
  obtain ⟨R, j, _, _, hy⟩ := exists_affine_chart_genericPoint f
  haveI : CompactSpace (bcScheme f j) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd f j)
  haveI : QuasiSeparatedSpace (bcScheme f j) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd f j)
  have key : ∀ y : Y, y = j ((pullback.snd f j) (genericPoint (bcScheme f j))) →
      Scheme.Modules.fiberRank ((Scheme.Modules.pushforward f).obj F) y =
        Module.finrank (Y.residueField y)
          (cohomologyOverField (Y.residueField y) (f.fiberToSpecResidueField y)
            ((Scheme.Modules.pullback (f.fiberι y)).obj F) 0) := by
    rintro y rfl
    exact (fiberRank_pushforward_via_open f j F).trans (finrank_fibre_via_open f j F).symm
  exact key _ hy

/-- Projective varieties over `k` with `f ≫ sY = sX`: `X` is integral and `f` is quasi-compact and
quasi-separated. -/
private theorem projective_facts {k : Type u} [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [MMP.Mori.IsProjectiveVariety k sX]
    [MMP.Mori.IsProjectiveVariety k sY] (f : X ⟶ Y) (hf : f ≫ sY = sX) :
    IsIntegral X ∧ QuasiCompact f ∧ QuasiSeparated f := by
  have : IsIntegral X := (inferInstance : AlgebraicGeometry.IsVariety k sX).toIsIntegral
  have : QuasiCompact (f ≫ sY) := hf ▸ (inferInstance : QuasiCompact sX)
  have : QuasiSeparated (f ≫ sY) := hf ▸ (inferInstance : QuasiSeparated sX)
  exact ⟨inferInstance, QuasiCompact.of_comp f sY, QuasiSeparated.of_comp f sY⟩

/-- `f` is proper and `X` is locally Noetherian in the projective setting. -/
private theorem projective_facts' {k : Type u} [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [MMP.Mori.IsProjectiveVariety k sX]
    [MMP.Mori.IsProjectiveVariety k sY] (f : X ⟶ Y) (hf : f ≫ sY = sX) :
    IsProper f ∧ IsLocallyNoetherian X ∧ IsLocallyNoetherian Y := by
  have : IsProper (f ≫ sY) := hf ▸ (inferInstance : IsProper sX)
  exact ⟨IsProper.of_comp f sY, LocallyOfFiniteType.isLocallyNoetherian sX,
    LocallyOfFiniteType.isLocallyNoetherian sY⟩

private theorem isRelativelyBigCartier_of_generic_rank {X Y : Scheme.{u}} [IsIntegral X] (f : X ⟶ Y)
    (D A E : X.CartierDivisor) (m : ℕ) (hm : 0 < m)
    (hmono : ∀ B E : X.CartierDivisor, MMP.Intersection.IsEffective E →
      relativeGenericRank f (MMP.CartierDivisor.sheaf B) ≤
      relativeGenericRank f (MMP.CartierDivisor.sheaf (B + E)))
    (hlin : ∀ B B' : X.CartierDivisor, MMP.Intersection.LinearlyEquivalent B B' →
      relativeGenericRank f (MMP.CartierDivisor.sheaf B) =
      relativeGenericRank f (MMP.CartierDivisor.sheaf B'))
    (hasym : ∀ B : X.CartierDivisor, ∃ a b : ℕ, topologicalKrullDim X = a ∧ topologicalKrullDim
        (closure (Set.range f.base)) = b ∧
      ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℤ, ∀ n : ℤ, k₀ ≤ n →
        c * (n : ℝ) ^ (a - b) <
          (relativeGenericRank f (MMP.CartierDivisor.sheaf (n • A + B)) : ℝ))
    (hE : MMP.Intersection.IsEffective E)
    (hDAE : MMP.Intersection.LinearlyEquivalent (m • D) (A + E)) :
    IsRelativelyBigCartier f D := by
  have hmono' : ∀ (B : X.CartierDivisor) (q : ℕ),
      relativeGenericRank f (MMP.CartierDivisor.sheaf B) ≤
      relativeGenericRank f (MMP.CartierDivisor.sheaf (B + q • E)) := by
    intro B q
    induction q with
    | zero => simp
    | succ q ih =>
      refine ih.trans ?_
      have := hmono (B + q • E) E hE
      rwa [add_assoc, ← succ_nsmul] at this
  obtain ⟨a, b, ha, hb, -⟩ := hasym 0
  have hr : ∀ r : ℕ, ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℤ, ∀ n : ℤ, k₀ ≤ n →
        c * (n : ℝ) ^ (a - b) <
          (relativeGenericRank f (MMP.CartierDivisor.sheaf (n • A + (r : ℤ) • D)) :
              ℝ) := by
    intro r
    obtain ⟨a', b', ha', hb', h⟩ := hasym ((r : ℤ) • D)
    have h1 : a' = a := by
      have := ha'.symm.trans ha
      exact_mod_cast this
    have h2 : b' = b := by
      have := hb'.symm.trans hb
      exact_mod_cast this
    subst h1; subst h2; exact h
  choose c hc k hk using hr
  have hne : (Finset.range m).Nonempty := ⟨0, Finset.mem_range.2 hm⟩
  set c0 := (Finset.range m).inf' hne c with hc0def
  have hc0 : 0 < c0 := (Finset.lt_inf'_iff hne).2 (fun r _ => hc r)
  set K : ℤ := (Finset.range m).sup' hne k with hKdef
  set K' : ℕ := (max K 0).toNat + 1 with hK'
  have hKK : ∀ r < m, k r ≤ (K' : ℤ) := by
    intro r hr
    have h1 : k r ≤ K := Finset.le_sup' k (Finset.mem_range.2 hr)
    have h2 : K ≤ (max K 0).toNat := by
      have := Int.self_le_toNat (max K 0)
      exact (le_max_left K 0).trans this
    omega
  refine ⟨a, b, ha, hb, c0 / (2 * m) ^ (a - b), by positivity, (m * K' : ℕ), ?_⟩
  intro n hn
  have hn0 : 0 ≤ n := le_trans (by positivity) hn
  lift n to ℕ using hn0
  have hn' : m * K' ≤ n := by exact_mod_cast hn
  set q := n / m with hq
  set r := n % m with hr
  have hrm : r < m := Nat.mod_lt _ hm
  have hqK : K' ≤ q := (Nat.le_div_iff_mul_le hm).2 (by rw [mul_comm]; exact hn')
  have hq1 : 1 ≤ q := le_trans (by omega) hqK
  have hdecomp : n • D = q • (m • D) + r • D := by
    conv_lhs => rw [← Nat.div_add_mod' n m]
    rw [add_smul, mul_smul]
  have hlin' : MMP.Intersection.LinearlyEquivalent (n • D) ((q • A + r • D) + q • E) := by
    have h := (hDAE.nsmul q).add (MMP.Intersection.linearlyEquivalent_equivalence.refl (r • D))
    rw [hdecomp]
    convert h using 1
    rw [smul_add]; abel
  have h1 := hlin _ _ hlin'
  have h2 := hmono' (q • A + r • D) q
  have h3 := hk r q (by have := hKK r hrm; omega)
  rw [natCast_zsmul, natCast_zsmul] at h3
  have h4 : (n : ℝ) ≤ 2 * m * q := by
    have : n < m * (q + 1) := by
      have := Nat.lt_mul_div_succ n hm
      exact this
    have : (n : ℝ) < m * (q + 1) := by exact_mod_cast this
    have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
    nlinarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
  have h5 : ((n : ℤ) : ℝ) ^ (a - b) ≤ (2 * m) ^ (a - b) * (q : ℝ) ^ (a - b) := by
    rw [← mul_pow]
    push_cast
    exact pow_le_pow_left₀ (Nat.cast_nonneg n) h4 _
  have hcr : c0 ≤ c r := Finset.inf'_le c (Finset.mem_range.2 hrm)
  have h6 : (relativeGenericRank f (MMP.CartierDivisor.sheaf (q • A + r • D)) : ℝ) ≤
      relativeGenericRank f (MMP.CartierDivisor.sheaf ((n : ℤ) • D)) := by
    rw [natCast_zsmul, h1]
    exact_mod_cast h2
  have hqpos : (0 : ℝ) ≤ (q : ℝ) ^ (a - b) := by positivity
  have h7 : c0 / (2 * m) ^ (a - b) * ((n : ℤ) : ℝ) ^ (a - b) ≤ c0 * (q : ℝ) ^ (a - b) := by
    have hpos : (0 : ℝ) < (2 * m : ℝ) ^ (a - b) := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
    calc c0 * ((n : ℤ) : ℝ) ^ (a - b) ≤ c0 * ((2 * m) ^ (a - b) * (q : ℝ) ^ (a - b)) :=
          mul_le_mul_of_nonneg_left h5 hc0.le
      _ = c0 * (q : ℝ) ^ (a - b) * (2 * m) ^ (a - b) := by ring
  have h8 : c0 * (q : ℝ) ^ (a - b) ≤ c r * (q : ℝ) ^ (a - b) := mul_le_mul_of_nonneg_right hcr hqpos
  have h9 : c r * ((q : ℤ) : ℝ) ^ (a - b) < _ := h3
  push_cast at h9
  linarith

section SectionDivisor

open MMP.Intersection

variable {X : Scheme.{u}}

/-- A section of an invertible sheaf on an integral scheme vanishing on a non-empty open is
zero. -/
private theorem eq_zero_of_restrict_eq_zero [IsIntegral X] (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (s : Γ(L, ⊤)) (U : X.Opens) (hU : (U : Set X).Nonempty)
    (h : L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s = 0) : s = 0 := by
  refine TopCat.Presheaf.section_ext (Stacks.AlgebraicGeometry.CardinalGeneration.asSheaf L) ⊤ s 0
      ?_
  intro x hx
  obtain ⟨V, -, e, hxV, he⟩ := exists_isTrivializingGenerator L (show x ∈ (⊤ : X.Opens) from
      trivial)
  obtain ⟨r, hr⟩ := (he V le_rfl).2 (L.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op s)
  dsimp only at hr
  rw [modules_map_id] at hr
  obtain ⟨p, hpU, hpV⟩ := nonempty_preirreducible_inter U.isOpen V.isOpen hU ⟨x, hxV⟩
  have hpUV : p ∈ (U ⊓ V : X.Opens) := ⟨hpU, hpV⟩
  have h1 : X.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op r = 0 := by
    apply ((he (U ⊓ V) inf_le_right).1)
    show X.presheaf.map _ r • L.presheaf.map _ e = (0 : Γ(X, U ⊓ V)) • L.presheaf.map _ e
    rw [zero_smul, ← Scheme.Modules.map_smul, hr,
      modules_map_map L le_top inf_le_right s,
      ← modules_map_map L (le_top : U ≤ ⊤) (inf_le_left : U ⊓ V ≤ U) s, h]
    exact map_zero _
  have h2 : r = 0 := by
    apply germ_injective_of_isIntegral X p hpV
    rw [map_zero, ← X.presheaf.germ_res_apply (homOfLE (inf_le_right : U ⊓ V ≤ V)) p hpUV r, h1]
    exact map_zero _
  have h3 := (Stacks.AlgebraicGeometry.CardinalGeneration.asSheaf L).presheaf.germ_res_apply
    (homOfLE (le_top : V ≤ ⊤)) x hxV s
  rw [h2, zero_smul] at hr
  rw [← h3, ← hr]
  exact (map_zero _).trans (map_zero _).symm

/-- Two trivializations of a line bundle differ by a unit, and so do the corresponding functions
of a section. -/
private theorem exists_unit_mul_of_trivializing (L : X.Modules) (s : Γ(L, ⊤)) {U V : X.Opens}
    {e : Γ(L, U)} {e' : Γ(L, V)} (he : IsTrivializingGenerator L U e)
    (he' : IsTrivializingGenerator L V e') {r : Γ(X, U)} {r' : Γ(X, V)}
    (hr : r • e = L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s)
    (hr' : r' • e' = L.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op s) :
    ∃ w : Γ(X, U ⊓ V)ˣ, X.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op r =
      (w : Γ(X, U ⊓ V)) * X.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op r' := by
  let W : X.Opens := U ⊓ V
  have hU := (he.res (inf_le_left : W ≤ U)).bijective
  have hV := (he'.res (inf_le_right : W ≤ V)).bijective
  set ē := L.presheaf.map (homOfLE (inf_le_left : W ≤ U)).op e with hē
  set ē' := L.presheaf.map (homOfLE (inf_le_right : W ≤ V)).op e' with hē'
  obtain ⟨w, hw⟩ := hU.2 ē'
  obtain ⟨w', hw'⟩ := hV.2 ē
  dsimp only at hw hw'
  have h1 : w' * w = 1 := by
    apply hU.1
    dsimp only
    rw [mul_smul, hw, hw', one_smul]
  have h2 : w * w' = 1 := by rwa [mul_comm]
  refine ⟨Units.mkOfMulEqOne w w' h2, ?_⟩
  have hsW : L.presheaf.map (homOfLE (inf_le_left : W ≤ U)).op (r • e) =
      L.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op s := by
    rw [hr, modules_map_map L le_top inf_le_left s]
  have hsW' : L.presheaf.map (homOfLE (inf_le_right : W ≤ V)).op (r' • e') =
      L.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op s := by
    rw [hr', modules_map_map L le_top inf_le_right s]
  rw [Scheme.Modules.map_smul] at hsW hsW'
  apply hU.1
  dsimp only
  have key : X.presheaf.map (homOfLE (inf_le_right : W ≤ V)).op r' • ē' =
      ((Units.mkOfMulEqOne w w' h2 : Γ(X, W)) * X.presheaf.map (homOfLE (inf_le_right : W ≤ V)).op
          r') • ē := by
    rw [← hw, smul_smul, mul_comm]
    rfl
  rw [hsW]
  exact hsW'.symm.trans key

/-- On an integral scheme, a non-zero section of an invertible sheaf has a divisor. -/
theorem _root_.MMP.Intersection.exists_isDivisorOfSection [IsIntegral X] (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (s : Γ(L, ⊤)) (hs : s ≠ 0) :
    ∃ D : X.CartierDivisor, IsDivisorOfSection L s D := by
  choose U _ e hxU he using fun x : X =>
    exists_isTrivializingGenerator L (show x ∈ (⊤ : X.Opens) from trivial)
  have hr : ∀ x, ∃ r : Γ(X, U x), r • e x = L.presheaf.map (homOfLE (le_top : U x ≤ ⊤)).op s := by
    intro x
    obtain ⟨r, hr⟩ := (he x (U x) le_rfl).2 (L.presheaf.map (homOfLE (le_top : U x ≤ ⊤)).op s)
    dsimp only at hr
    rw [modules_map_id] at hr
    exact ⟨r, hr⟩
  choose r hr using hr
  have hrne : ∀ {V : X.Opens} {e' : Γ(L, V)} {r' : Γ(X, V)},
      r' • e' = L.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op s → (V : Set X).Nonempty → r' ≠ 0 := by
    intro V e' r' h hV h0
    rw [h0, zero_smul] at h
    exact hs (eq_zero_of_restrict_eq_zero L s V hV h.symm)
  have hnzd : ∀ {V : X.Opens} {r' : Γ(X, V)}, r' ≠ 0 → ∀ y (hy : y ∈ V),
      X.presheaf.germ V y hy r' ∈ nonZeroDivisors (X.presheaf.stalk y) := by
    intro V r' h y hy
    refine mem_nonZeroDivisors_of_ne_zero fun h0 => h ?_
    exact germ_injective_of_isIntegral X y hy (by rw [h0, map_zero])
  have hu : ∀ {V : X.Opens} {r' : Γ(X, V)}, r' ≠ 0 → IsUnit (toTotalQuotient V r') := by
    intro V r' h
    exact isUnit_toTotalQuotientSheaf_app X.sheaf V r' (fun y hy => hnzd h y hy)
  have hne : ∀ x, r x ≠ 0 := fun x => hrne (hr x) ⟨x, hxU x⟩
  let f : ∀ x : X, (X.totalQuotientSheaf.obj.obj (op (U x)))ˣ := fun x => (hu (hne x)).unit
  have hcompat : ∀ i j, ∃ u : Γ(X, U i ⊓ U j)ˣ, MMP.Intersection.resUnit (homOfLE inf_le_left) (f i)
      =
      Units.map (toTotalQuotient (U i ⊓ U j)).toMonoidHom u *
        MMP.Intersection.resUnit (homOfLE inf_le_right) (f j) := by
    intro i j
    obtain ⟨w, hw⟩ := exists_unit_mul_of_trivializing L s (he i) (he j) (hr i) (hr j)
    refine ⟨w, Units.ext ?_⟩
    simp only [MMP.Intersection.resUnit, Units.val_mul, Units.coe_map]
    change X.totalQuotientSheaf.obj.map _ (toTotalQuotient (U i) (r i)) = _
    rw [← toTotalQuotient_res, hw, map_mul, toTotalQuotient_res]
    rfl
  obtain ⟨D, hD, -⟩ := existsUnique_isLocalEquationOn U
    (eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxU x⟩) f hcompat
  refine ⟨D, ?_, ?_, ?_⟩
  · intro V e' he' r' hr' x hx
    exact hnzd (hrne hr'.symm ⟨x, hx⟩) x hx
  · intro x
    exact ⟨U x, hxU x, r x, hu (hne x), hD x⟩
  · intro V e' he' r' hr'
    have hunit : IsUnit (toTotalQuotient V r') := by
      refine isUnit_of_locally _ fun x hx => ⟨V, 𝟙 V, hx, ?_⟩
      rw [show (X.totalQuotientSheaf.obj.map (𝟙 V).op) = 𝟙 _ from by simp]
      exact hu (hrne hr'.symm ⟨x, hx⟩)
    refine ⟨hunit, isLocalEquationOn_of_locally fun x hx => ⟨V ⊓ U x, homOfLE inf_le_left, ⟨hx, hxU
        x⟩, ?_⟩⟩
    obtain ⟨w, hw⟩ := exists_unit_mul_of_trivializing L s he' (he x) hr'.symm (hr x)
    have h1 := (isLocalEquationOn_resUnit (homOfLE (inf_le_right : V ⊓ U x ≤ U x)) (hD x)).units_mul
        w
    convert h1 using 1
    refine Units.ext ?_
    simp only [MMP.Intersection.resUnit, Units.val_mul, Units.coe_map]
    change X.totalQuotientSheaf.obj.map _ (toTotalQuotient V r') =
      toTotalQuotient (V ⊓ U x) w * X.totalQuotientSheaf.obj.map _ (toTotalQuotient (U x) (r x))
    rw [← toTotalQuotient_res, ← toTotalQuotient_res, ← map_mul, hw]

/-- A non-zero section `s` of an invertible sheaf `L` on an integral scheme gives an effective
Cartier divisor `D` with `𝒪_X(D) ≅ L` whose support is the zero locus of `s`. -/
theorem exists_isEffective_sheaf_iso_cartierSupport_of_ne_zero [IsIntegral X] (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (s : Γ(L, ⊤)) (hs : s ≠ 0) :
    ∃ D : X.CartierDivisor, IsEffective D ∧
      ∃ _ : MMP.CartierDivisor.sheaf D ≅ L, ∀ x,
        x ∈ MMP.Intersection.cartierSupport D ↔
          x ∉ Stacks.Ample.nonvanishingLocus L s := by
  obtain ⟨D, hD⟩ := exists_isDivisorOfSection L s hs
  obtain ⟨φ, hφ⟩ := MMP.CartierDivisor.exists_sheaf_iso_of_isDivisorOfSection L hD
  refine ⟨D, hD.2.1, φ, fun x => ?_⟩
  erw [← hφ, AlgebraicGeometry.Cube.nonvanishingLocus_hom_app_top_of_iso,
    MMP.CartierDivisor.mem_nonvanishingLocus_canonicalSection_iff, not_not]

/-- A non-zero section `s` of an invertible sheaf `L` on an integral scheme gives an effective
Cartier divisor `D` with `𝒪_X(D) ≅ L`. -/
theorem exists_isEffective_sheaf_iso_of_ne_zero [IsIntegral X] (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (s : Γ(L, ⊤)) (hs : s ≠ 0) :
    ∃ D : X.CartierDivisor, IsEffective D ∧
      Nonempty (MMP.CartierDivisor.sheaf D ≅ L) := by
  obtain ⟨D, hD, e, -⟩ := exists_isEffective_sheaf_iso_cartierSupport_of_ne_zero L s hs
  exact ⟨D, hD, ⟨e⟩⟩

end SectionDivisor

section LineBundleIncl

open MMP.Intersection

variable {X : Scheme.{u}}

private theorem lineBundleSections_le_add {B E : X.CartierDivisor} (hE : IsEffective E) (V :
    X.Opens) :
    lineBundleSections B V ≤ lineBundleSections (B + E) V := by
  intro σ hσ
  refine mem_lineBundleSections_of_locally σ fun x hx => ?_
  obtain ⟨U, hxU, g, hg⟩ := MMP.Intersection.exists_isLocalEquationOn B x
  obtain ⟨W, hxW, s, hs, hsE⟩ := hE x
  let U' := V ⊓ U ⊓ W
  have hU' : x ∈ U' := ⟨⟨hx, hxU⟩, hxW⟩
  refine ⟨U', homOfLE (le_trans inf_le_left inf_le_left), hU', ?_⟩
  have hg' := isLocalEquationOn_resUnit (homOfLE (show U' ≤ U from le_trans inf_le_left
      inf_le_right)) hg
  have hs' := isLocalEquationOn_resUnit (homOfLE (show U' ≤ W from inf_le_right))
    (g := hs.unit) hsE
  have hsum := hg'.mul hs'
  rw [mem_lineBundleSections_iff_of_isLocalEquationOn' hsum]
  have hres := res_mem B (le_trans inf_le_left inf_le_left : U' ≤ V) hσ
  rw [mem_lineBundleSections_iff_of_isLocalEquationOn' hg'] at hres
  obtain ⟨r, hr⟩ := hres
  refine ⟨r * X.presheaf.map (homOfLE (show U' ≤ W from inf_le_right)).op s, ?_⟩
  have e : toTotalQuotient U' (X.presheaf.map (homOfLE (show U' ≤ W from inf_le_right)).op s) =
      ((MMP.Intersection.resUnit (homOfLE (show U' ≤ W from inf_le_right)) hs.unit :
          (X.totalQuotientSheaf.obj.obj (op U'))ˣ) : X.totalQuotientSheaf.obj.obj (op U')) := by
    rw [toTotalQuotient_res]; rfl
  rw [← hr, map_mul, e, mul_inv, Units.val_mul]
  have h1 := Units.mul_inv (MMP.Intersection.resUnit (homOfLE (show U' ≤ W from inf_le_right))
      hs.unit)
  linear_combination (toTotalQuotient U' r * ↑(MMP.Intersection.resUnit (homOfLE (show U' ≤ U from
      le_trans inf_le_left inf_le_right)) g)⁻¹) * h1

/-- Inclusion `𝒪(B) ⟶ 𝒪(B + E)` for effective `E`. -/
private noncomputable def lineBundleIncl (B : X.CartierDivisor) {E : X.CartierDivisor} (hE :
    IsEffective E) :
    MMP.CartierDivisor.sheaf B ⟶ MMP.CartierDivisor.sheaf (B + E) :=
  (SheafOfModules.fullyFaithfulForget _).preimage
    (PresheafOfModules.Hom.mk (M₁ := (MMP.CartierDivisor.sheaf B).val) (M₂ :=
        (MMP.CartierDivisor.sheaf (B + E)).val)
      (fun (V : (X.Opens)ᵒᵖ) =>
      ModuleCat.ofHom (Submodule.inclusion (fun s hs => (mem_lineBundleSections_iff_mem _ _ s).1
        (lineBundleSections_le_add hE V.unop ((mem_lineBundleSections_iff_mem _ _ s).2 hs))) :
          ↥((MMP.CartierDivisor.sheafSubmodule B).obj V) →ₗ[X.ringCatSheaf.obj.obj V]
            ↥((MMP.CartierDivisor.sheafSubmodule (B + E)).obj V)))
      (fun {V W} i => by
        refine ModuleCat.hom_ext (LinearMap.ext fun σ => Subtype.ext ?_)
        rfl))

private theorem mono_lineBundleIncl (B : X.CartierDivisor) {E : X.CartierDivisor} (hE : IsEffective
    E) :
    Mono (lineBundleIncl B hE) := by
  refine (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).mono_of_mono_map ?_
  have : ∀ V, Mono ((((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map
      (lineBundleIncl B hE))).app V) := fun V => by
    rw [AddCommGrpCat.mono_iff_injective]
    intro a b h
    let a' : ↥((MMP.CartierDivisor.sheafSubmodule B).obj V) := a
    let b' : ↥((MMP.CartierDivisor.sheafSubmodule B).obj V) := b
    have h' : a'.1 = b'.1 :=
      congrArg (fun x : ↥((MMP.CartierDivisor.sheafSubmodule (B + E)).obj V) => x.1) h
    exact (Subtype.ext h' : a' = b')
  exact NatTrans.mono_of_mono_app _

end LineBundleIncl

/-- Monotonicity of the generic rank along a monomorphism into a coherent module on a proper
morphism (the heart of the effective-divisor comparison). -/
private theorem relativeGenericRank_le_of_mono {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X]
    [IsProper f] [IsLocallyNoetherian Y] {F F' : X.Modules} [F.IsQuasicoherent] [F'.IsCoherent]
    (φ : F ⟶ F') [Mono φ] :
    relativeGenericRank f F ≤ relativeGenericRank f F' := by
  have hG' : ((Scheme.Modules.pushforward f).obj F').IsCoherent :=
    ProperCoherenceWitness.isCoherent_pushforward f F'
  unfold relativeGenericRank Scheme.Modules.fiberRank
  let ψ := (Scheme.Modules.pushforward f).map φ
  let φl : TopCat.Presheaf.stalk (C := Ab.{u}) ((Scheme.Modules.pushforward f).obj F).val.presheaf
      (f (genericPoint X)) →ₗ[Y.presheaf.stalk (f (genericPoint X))]
      TopCat.Presheaf.stalk (C := Ab.{u}) ((Scheme.Modules.pushforward f).obj F').val.presheaf
      (f (genericPoint X)) :=
    { toFun := stalkMapAb ψ (f (genericPoint X))
      map_add' := map_add _
      map_smul' := fun ρ n => stalkMapAb_smul ψ (f (genericPoint X)) ρ n }
  haveI : Module.Finite (Y.presheaf.stalk (f (genericPoint X)))
      (((Scheme.Modules.pushforward f).obj F').presheaf.stalk (f (genericPoint X))) :=
    Scheme.Modules.finite_stalk_of_isCoherent _ _
  refine finrank_tensor_le_of_injective (O := Y.presheaf.stalk (f (genericPoint X)))
    (K := Y.residueField (f (genericPoint X))) ?_ φl (stalkMapAb_injective ψ _) ?_ ?_
  · exact Ideal.Quotient.mk_surjective
  · intro a ha n
    exact smul_zero_of_not_isUnit f F a (fun hu => (IsLocalRing.residue_eq_zero_iff a).1 ha |> fun h
        => (IsLocalRing.mem_maximalIdeal _).1 h hu) n
  · intro a ha n
    exact smul_zero_of_not_isUnit f F' a (fun hu => (IsLocalRing.residue_eq_zero_iff a).1 ha |> fun
        h => (IsLocalRing.mem_maximalIdeal _).1 h hu) n

/-- Multiplication by the section of an effective divisor embeds the generic sections of `𝒪(B)`
into those of `𝒪(B + E)`, so the generic rank is monotone. -/
private theorem relativeGenericRank_le_of_isEffective {k : Type u} [Field k] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    [MMP.Mori.IsProjectiveVariety k sX] [MMP.Mori.IsProjectiveVariety k sY] (f : X ⟶ Y)
    (hf : f ≫ sY = sX) (B E : X.CartierDivisor) (hE : MMP.Intersection.IsEffective E) :
    relativeGenericRank f (MMP.CartierDivisor.sheaf B) ≤
      relativeGenericRank f (MMP.CartierDivisor.sheaf (B + E)) := by
  obtain ⟨hI, -, -⟩ := projective_facts sX sY f hf
  obtain ⟨hP, hN, hNY⟩ := projective_facts' sX sY f hf
  have hF' : SheafOfModules.IsFiniteType.{u, u, u} (MMP.CartierDivisor.sheaf (B + E)) :=
    Scheme.Modules.isFiniteType_of_isFinitePresentation _
      (MMP.CartierDivisor.isFinitePresentation_sheaf (B + E))
  have hcoh : (MMP.CartierDivisor.sheaf (B + E)).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_of_isQuasicoherent_of_isFiniteType _
  haveI := mono_lineBundleIncl B hE
  exact relativeGenericRank_le_of_mono f (lineBundleIncl B hE)

/-- The generic rank only depends on the linear equivalence class. -/
private theorem relativeGenericRank_eq_of_linearlyEquivalent {k : Type u} [Field k]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (sY : Y ⟶ Spec (.of k)) [MMP.Mori.IsProjectiveVariety k sX]
    [MMP.Mori.IsProjectiveVariety k sY] (f : X ⟶ Y) (hf : f ≫ sY = sX) (B B' : X.CartierDivisor)
    (h : MMP.Intersection.LinearlyEquivalent B B') :
    relativeGenericRank f (MMP.CartierDivisor.sheaf B) =
      relativeGenericRank f (MMP.CartierDivisor.sheaf B') := by
  obtain ⟨hI, -, -⟩ := projective_facts sX sY f hf
  obtain ⟨e⟩ := MMP.CartierDivisor.nonempty_iso_of_linearlyEquivalent h
  exact fiberRank_congr ((Scheme.Modules.pushforward f).mapIso e) (f (genericPoint X))

private theorem dim_formula_aux {k : Type u} [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [IsIntegral X] [LocallyOfFiniteType sX]
    [LocallyOfFiniteType sY] (f : X ⟶ Y) (hf : f ≫ sY = sX) [QuasiCompact f] :
    topologicalKrullDim X = topologicalKrullDim (closure (Set.range f.base)) +
      topologicalKrullDim (f.fiber (f (genericPoint X))) := by
  have hLY : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have hLX : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have hfact : f.toImage ≫ f.imageι = f := Scheme.Hom.toImage_imageι f
  have hLS : LocallyOfFiniteType (f.imageι ≫ sY) := by infer_instance
  haveI : LocallyOfFiniteType (f.toImage ≫ f.imageι ≫ sY) := by
    rw [← Category.assoc, hfact, hf]
    infer_instance
  haveI : LocallyOfFiniteType f.toImage := LocallyOfFiniteType.of_comp (g := f.imageι ≫ sY)
      inferInstance
  haveI : IsLocallyNoetherian f.image := LocallyOfFiniteType.isLocallyNoetherian (f.imageι ≫ sY)
  haveI : IrreducibleSpace f.image := (irreducibleSpace_def _).2 (by
      have h := ((IrreducibleSpace.isIrreducible_univ X).image _
          f.toImage.continuous.continuousOn).closure
      rwa [Set.image_univ, (IsDominant.denseRange (f := f.toImage)).closure_eq] at h)
  obtain ⟨O, hO, hne, hform⟩ :=
      exists_isOpen_nonempty_topologicalKrullDimAt_eq_add_fiber_of_irreducibleSpace f.toImage
  have hξ : genericPoint X ∈ O := by
    obtain ⟨w, hw⟩ := hne
    exact ((genericPoint_spec X).mem_open_set_iff hO).2 ⟨w, ⟨trivial, hw⟩⟩
  have h1 := hform _ hξ
  have e1 : topologicalKrullDim X = topologicalKrullDimAt X (genericPoint X) :=
    topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k X sX _
  have e2 : topologicalKrullDim f.image =
      topologicalKrullDimAt f.image (f.toImage (genericPoint X)) :=
    topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k f.image (f.imageι ≫ sY) _
  have e3 : topologicalKrullDim f.image = topologicalKrullDim (closure (Set.range f.base)) := by
    let e := f.imageι.isEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr (Scheme.Hom.range_imageι f))
    exact IsHomeomorph.topologicalKrullDim_eq e e.isHomeomorph
  have hset :
      (f.toImage ⁻¹' {f.toImage (genericPoint X)} : Set X) = f ⁻¹' {f (genericPoint X)} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      rw [← hfact]
      simp only [Scheme.Hom.comp_apply]
      rw [h]
    · intro h
      rw [← hfact] at h
      simp only [Scheme.Hom.comp_apply] at h
      exact f.imageι.injective h
  have hirr : IsIrreducible (f.toImage ⁻¹' {f.toImage (genericPoint X)} : Set X) := by
    rw [← isIrreducible_iff_closure]
    have : closure (f.toImage ⁻¹' {f.toImage (genericPoint X)} : Set X) = Set.univ := by
      apply Set.eq_univ_of_univ_subset
      rw [← (genericPoint_spec X).def]
      exact closure_mono (by simp)
    rw [this]
    exact IrreducibleSpace.isIrreducible_univ X
  haveI : IrreducibleSpace (f.toImage.fiber (f.toImage (genericPoint X))) := by
    refine (irreducibleSpace_def _).2 ?_
    haveI : IrreducibleSpace ↥(f.toImage ⁻¹' {f.toImage (genericPoint X)} : Set X) :=
      Subtype.irreducibleSpace hirr
    let φ := f.toImage.fiberHomeo (f.toImage (genericPoint X))
    have h := (IrreducibleSpace.isIrreducible_univ
      ↥(f.toImage ⁻¹' {f.toImage (genericPoint X)} : Set X)).image φ.symm
      φ.symm.continuous.continuousOn
    rwa [Set.image_univ, φ.symm.surjective.range_eq] at h
  have e4 : topologicalKrullDim (f.toImage.fiber (f.toImage (genericPoint X))) =
      topologicalKrullDimAt (f.toImage.fiber (f.toImage (genericPoint X)))
        (f.toImage.asFiber (genericPoint X)) :=
    have := Scheme.Hom.locallyOfFiniteType_fiberToSpecResidueField f.toImage
      (f.toImage (genericPoint X))
    topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible
      (f.image.residueField (f.toImage (genericPoint X)))
      (f.toImage.fiber (f.toImage (genericPoint X)))
      (f.toImage.fiberToSpecResidueField _) _
  have e5 : topologicalKrullDim (f.toImage.fiber (f.toImage (genericPoint X))) =
      topologicalKrullDim (f.fiber (f (genericPoint X))) := by
    let e := (f.toImage.fiberHomeo (f.toImage (genericPoint X))).trans
      ((Homeomorph.setCongr hset).trans (f.fiberHomeo (f (genericPoint X))).symm)
    exact IsHomeomorph.topologicalKrullDim_eq e e.isHomeomorph
  rw [e1, h1, ← e4, ← e2, e3, e5]

private theorem exists_dim_generic_fibre_aux {k : Type u} [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [IsIntegral X] [LocallyOfFiniteType sX]
    [LocallyOfFiniteType sY] (f : X ⟶ Y) (hf : f ≫ sY = sX) [QuasiCompact f] [CompactSpace X] :
    ∃ a b : ℕ, topologicalKrullDim X = a ∧ topologicalKrullDim (closure (Set.range f.base)) = b ∧
      topologicalKrullDim (f.fiber (f (genericPoint X))) = ((a - b : ℕ) : ℕ∞) := by
  have h := dim_formula_aux sX sY f hf
  have h1 := topologicalKrullDim_ne_top_of_locallyOfFiniteType k sX
  have hbot : topologicalKrullDim X ≠ ⊥ := fun hb =>
    ((Order.krullDim_eq_bot_iff.mp hb).false (TopologicalSpace.IrreducibleCloseds.closureSingleton
        (genericPoint X))).elim
  induction hX : topologicalKrullDim X using WithBot.recBotCoe with
  | bot => exact absurd hX hbot
  | coe a' =>
    induction hB : topologicalKrullDim (closure (Set.range f.base)) using WithBot.recBotCoe with
    | bot => rw [hX, hB] at h; simp at h
    | coe B =>
      induction hD : topologicalKrullDim (f.fiber (f (genericPoint X))) using WithBot.recBotCoe with
      | bot => rw [hX, hB, hD] at h; simp at h
      | coe D =>
        rw [hX, hB, hD, ← WithBot.coe_add, WithBot.coe_inj] at h
        have ha : a' ≠ ⊤ := by rintro rfl; exact h1 hX
        have hB' : B ≠ ⊤ := by rintro rfl; rw [top_add] at h; exact ha h
        have hD' : D ≠ ⊤ := by rintro rfl; rw [add_top] at h; exact ha h
        lift a' to ℕ using ha
        lift B to ℕ using hB'
        lift D to ℕ using hD'
        refine ⟨a', B, rfl, rfl, ?_⟩
        have : D = a' - B := by norm_cast at h; omega
        rw [this]

section Asymptotics

open Filter

private theorem poly_lower {c0 : ℝ} (hc : 0 < c0) (d : ℕ) (P : Polynomial ℚ)
    (hP : P.degree < (d : WithBot ℕ)) :
    ∀ᶠ n : ℕ in atTop, -(c0 * (n : ℝ) ^ d) < ((P.eval (n : ℚ) : ℚ) : ℝ) := by
  have hdeg : (P.map (algebraMap ℚ ℝ)).degree < (Polynomial.X ^ d : Polynomial ℝ).degree := by
    rwa [Polynomial.degree_map, Polynomial.degree_X_pow]
  have h := Polynomial.div_tendsto_atTop_zero_of_degree_lt _ _ hdeg
  have h2 := (h.comp tendsto_natCast_atTop_atTop).eventually (Metric.ball_mem_nhds 0 hc)
  filter_upwards [h2, eventually_gt_atTop 0] with n hn hn0
  simp only [Function.comp, Metric.mem_ball, dist_zero_right, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_map, norm_div, norm_pow, Real.norm_natCast] at hn
  have hpos : (0 : ℝ) < (n : ℝ) ^ d := by positivity
  have h3 := (div_lt_iff₀ hpos).1 hn
  have h4 : ((P.eval (n : ℚ) : ℚ) : ℝ) = Polynomial.eval₂ (algebraMap ℚ ℝ) (n : ℝ) P := by
    rw [Polynomial.eval₂_at_natCast]; simp
  rw [h4]
  have h5 := abs_lt.1 (show |Polynomial.eval₂ (algebraMap ℚ ℝ) (n : ℝ) P| < c0 * (n : ℝ) ^ d from
      h3)
  linarith [h5.1]

private theorem exists_lt_finrank_tensorPower {κ : Type u} [Field κ] {Z : Scheme.{u}}
    (g : Z ⟶ Spec (.of κ)) [IsProper g] (d : ℕ) (hd : topologicalKrullDim Z = (d : WithBot ℕ∞))
    (L : Z.Modules) [SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 L]
    (hL : Scheme.Modules.IsAmple Z L) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      c * (n : ℝ) ^ d < (Module.finrank κ (cohomologyOverField κ g
        (Stacks.SheafOfModules.Invertible.tensorPower Z.presheaf Z.ringCatSheaf.2 L (n : ℤ)) 0) : ℝ)
            := by
  obtain ⟨hpos, P, hP, hev⟩ := asymptotic_riemann_roch κ g d hd L hL
  set c1 : ℝ := ((degreeWithRespectTo κ g (𝟙 Z) d hd L hL : ℚ) : ℝ) / (d.factorial : ℝ) with hc1
  have hc1pos : 0 < c1 := by
    rw [hc1]
    have : (0 : ℝ) < ((((degreeWithRespectTo κ g (𝟙 Z) d hd L hL : ℚ) / (d.factorial : ℚ) : ℚ)) : ℝ)
        :=
      by exact_mod_cast hpos
    simpa using this
  have hlow := poly_lower (c0 := c1 / 2) (by positivity) d P hP
  obtain ⟨N, hN⟩ := (hev.and hlow).exists_forall_of_atTop
  refine ⟨c1 / 2, by positivity, N + 1, fun n hn => ?_⟩
  obtain ⟨h1, h2⟩ := hN n (by omega)
  have h3 : (Module.finrank κ (cohomologyOverField κ g
      (Stacks.SheafOfModules.Invertible.tensorPower Z.presheaf Z.ringCatSheaf.2 L (n : ℤ)) 0) : ℝ) =
      ((Module.finrank κ (globalSectionsOverField κ g
        (Stacks.SheafOfModules.Invertible.tensorPower Z.presheaf Z.ringCatSheaf.2 L (n : ℤ))) : ℕ) :
            ℝ) := by
    exact_mod_cast (finrank_globalSectionsOverField κ g _).symm
  rw [h3]
  have h4 : ((Module.finrank κ (globalSectionsOverField κ g
        (Stacks.SheafOfModules.Invertible.tensorPower Z.presheaf Z.ringCatSheaf.2 L (n : ℤ))) : ℕ) :
            ℝ) =
      c1 * (n : ℝ) ^ d + ((P.eval (n : ℚ) : ℚ) : ℝ) := by
    have := congrArg (fun q : ℚ => (q : ℝ)) h1
    simpa [hc1] using this
  rw [h4]
  have hn0 : (0 : ℝ) < (n : ℝ) ^ d := by
    have : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    positivity
  nlinarith

end Asymptotics

/-- Dimension of the generic fibre: with `a = dim X`, `b = dim f(X)-closure`, the generic fibre
`X_η` has dimension `a - b`. -/
private theorem exists_dim_generic_fibre {k : Type u} [Field k]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    [MMP.Mori.IsProjectiveVariety k sX] [MMP.Mori.IsProjectiveVariety k sY] (f : X ⟶ Y)
    (hf : f ≫ sY = sX) :
    ∃ a b : ℕ, topologicalKrullDim X = a ∧ topologicalKrullDim (closure (Set.range f.base)) = b ∧
      topologicalKrullDim (f.fiber (f (genericPoint X))) = ((a - b : ℕ) : ℕ∞) := by
  obtain ⟨hI, hQC, -⟩ := projective_facts sX sY f hf
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  exact exists_dim_generic_fibre_aux sX sY f hf

/-- Restriction of an `f`-ample invertible sheaf to the generic fibre is ample. -/
private theorem isAmple_generic_fibre {k : Type u} [Field k]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    [MMP.Mori.IsProjectiveVariety k sX] [MMP.Mori.IsProjectiveVariety k sY] (f : X ⟶ Y)
    (hf : f ≫ sY = sX) (A : X.CartierDivisor)
    (hA : IsRelativelyAmple f (MMP.CartierDivisor.sheaf A)) :
    Stacks.Ample.IsAmple (f.fiber (f (genericPoint X)))
      ((Scheme.Modules.pullback (f.fiberι (f (genericPoint X)))).obj
        (MMP.CartierDivisor.sheaf A)) := by
  obtain ⟨hI, hQC, hQS⟩ := projective_facts sX sY f hf
  haveI : Stacks.Ample.IsInvertibleModule X (MMP.CartierDivisor.sheaf A) :=
    inferInstance
  have hrel : Stacks.RelativeAmple.IsRelativelyAmple f (MMP.CartierDivisor.sheaf A)
      :=
    Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_of_forall_exists_isAmple f _ hQC hA
  have h2 := Stacks.RelativeAmpleBaseChange.isRelativelyAmple_modulePullback_unconditional f
    (Y.fromSpecResidueField (f (genericPoint X))) (MMP.CartierDivisor.sheaf A) hrel
  haveI : Stacks.Ample.IsInvertibleModule (f.fiber (f (genericPoint X)))
    (Stacks.AmpleLocallyClosed.pullbackModule (pullback.fst f (Y.fromSpecResidueField (f
        (genericPoint X)))) (MMP.CartierDivisor.sheaf A)) :=
    inferInstanceAs (Stacks.Ample.IsInvertibleModule (f.fiber (f (genericPoint X)))
      ((Scheme.Modules.pullback (f.fiberι (f (genericPoint X)))).obj
        (MMP.CartierDivisor.sheaf A)))
  exact (Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple _ _).1 h2

section TwistIso

open MonoidalCategory

variable {X : Scheme.{u}}

private theorem sheaf_nsmul_add_iso (A B : X.CartierDivisor) (n : ℕ) :
    Nonempty (MMP.CartierDivisor.sheaf (n • A + B) ≅
      MMP.CartierDivisor.sheaf B ⊗
        Stacks.Ample.tensorPowModule X (MMP.CartierDivisor.sheaf A) n) := by
  induction n with
  | zero =>
    have h : ((0 : ℕ) • A + B) = B := by simp
    refine ⟨eqToIso (by rw [h]) ≪≫ (ρ_ _).symm ≪≫ ?_⟩
    exact (whiskerLeftIso _ (Stacks.Ample.tensorPowModuleZeroIso X
      (MMP.CartierDivisor.sheaf A)).symm)
  | succ n ih =>
    obtain ⟨e⟩ := ih
    have h : ((n + 1 : ℕ) • A + B) = (n • A + B) + A := by
      rw [succ_nsmul]; abel
    refine ⟨eqToIso (by rw [h]) ≪≫ (MMP.CartierDivisorSheaf.sheafMulIso _ A).symm ≪≫ ?_⟩
    refine (whiskerRightIso e _) ≪≫ (α_ _ _ _) ≪≫ ?_
    refine whiskerLeftIso _ ?_
    exact (whiskerLeftIso _ (Stacks.Ample.tensorPowModuleOneIso X
      (MMP.CartierDivisor.sheaf A)).symm) ≪≫
      Stacks.Ample.tensorPowModuleAddIso X (MMP.CartierDivisor.sheaf A) (n : ℤ) 1 ≪≫
      Stacks.RelativeVeryAmple.tensorPowModuleCongr X (MMP.CartierDivisor.sheaf A)
        (by push_cast; ring)

private theorem pullback_sheaf_nsmul_add_iso {Z : Scheme.{u}} (i : Z ⟶ X) (A B : X.CartierDivisor)
    (n : ℕ) :
    Nonempty ((Scheme.Modules.pullback i).obj (MMP.CartierDivisor.sheaf (n • A + B))
        ≅
      (Scheme.Modules.pullback i).obj (MMP.CartierDivisor.sheaf B) ⊗
        Stacks.Ample.tensorPowModule Z
          ((Scheme.Modules.pullback i).obj (MMP.CartierDivisor.sheaf A)) n) := by
  obtain ⟨e⟩ := sheaf_nsmul_add_iso A B n
  exact ⟨(Scheme.Modules.pullback i).mapIso e ≪≫
    Stacks.ProjectiveBundleConormal.pullbackTensorComparisonIso i _ _ ≪≫
    whiskerLeftIso _ (Stacks.AlgebraicGeometry.HyperplaneTwistSequence.pullbackTensorPowModuleIntIso
        i
      (MMP.CartierDivisor.sheaf A) (n : ℤ))⟩

end TwistIso

/-- Twisting the pulled-back `𝒪(B)` by the powers of the pulled-back `𝒪(A)` gives the pulled-back
`𝒪(n • A + B)`. -/
private theorem nonempty_twist_iso_pullback {Z X : Scheme.{u}} (i : Z ⟶ X)
    (A B : X.CartierDivisor)
    [SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2
      ((Scheme.Modules.pullback i).obj (MMP.CartierDivisor.sheaf A))] (n : ℕ) :
    Nonempty (twistedSheaf ((Scheme.Modules.pullback i).obj (MMP.CartierDivisor.sheaf
        B))
      (fun _ : Fin 1 => (Scheme.Modules.pullback i).obj (MMP.CartierDivisor.sheaf A))
      (fun _ => (n : ℤ)) ≅
      (Scheme.Modules.pullback i).obj (MMP.CartierDivisor.sheaf (n • A + B))) := by
  obtain ⟨e⟩ := pullback_sheaf_nsmul_add_iso i A B n
  exact ⟨(MonoidalCategory.whiskerLeftIso _
    (Stacks.PowerFamilyBridge.invertibleTensorPowerModuleIso Z
      ((Scheme.Modules.pullback i).obj (MMP.CartierDivisor.sheaf A)) (n : ℤ))) ≪≫
    e.symm⟩

private theorem stalkMap_bijective_of_flat_preimmersion {Z W : Scheme.{u}} (L : Z ⟶ W) [Flat L]
    [IsPreimmersion L] (z : Z) : Function.Bijective (L.stalkMap z) := by
  refine ⟨?_, L.stalkMap_surjective z⟩
  algebraize [(L.stalkMap z).hom]
  have : Module.FaithfullyFlat (W.presheaf.stalk (L z)) (Z.presheaf.stalk z) :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap L z) (L.toLRSHom.prop z)
  exact ‹RingHom.FaithfullyFlat _›.injective

private theorem isReduced_of_flat_preimmersion {Z W : Scheme.{u}} (L : Z ⟶ W) [Flat L]
    [IsPreimmersion L] [IsReduced W] : IsReduced Z := by
  have : ∀ z : Z, _root_.IsReduced (Z.presheaf.stalk z) := fun z => by
    let e := RingEquiv.ofBijective (L.stalkMap z).hom (stalkMap_bijective_of_flat_preimmersion L z)
    exact isReduced_of_injective e.symm.toRingHom e.symm.injective
  exact isReduced_of_isReduced_stalk Z

private theorem isReduced_of_isPullback_flat_preimmersion {P X' T S : Scheme.{u}} (p : P ⟶ X')
    (k : P ⟶ T) (g : X' ⟶ S) (q : T ⟶ S) (H : IsPullback p k g q) [Flat q] [IsPreimmersion q]
    [IsReduced X'] : IsReduced P := by
  haveI : Flat p := MorphismProperty.of_isPullback H.flip ‹_›
  haveI : IsPreimmersion p := MorphismProperty.of_isPullback H.flip ‹_›
  exact isReduced_of_flat_preimmersion p

private theorem isPreimmersion_spec_resMapQuot (R : CommRingCat.{u}) (x : Spec R) :
    IsPreimmersion (Spec.map (resMapQuot R x)) := by
  have h : resMapQuot R x = CommRingCat.ofHom (algebraMap (R ⧸ x.asIdeal) x.asIdeal.ResidueField) ≫
      (Scheme.Spec.residueFieldIso R x).inv := by
    ext a
    rfl
  have : IsPreimmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (R ⧸ x.asIdeal) x.asIdeal.ResidueField))) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors (R ⧸ x.asIdeal))
  rw [h, Spec.map_comp]
  infer_instance

private theorem isPreimmersion_spec_psiK {Y : Scheme.{u}} {R : CommRingCat.{u}} (j : Spec R ⟶ Y)
    [IsOpenImmersion j] (z : Spec R) : IsPreimmersion (Spec.map (psiK j z)) := by
  have := isPreimmersion_spec_resMapQuot R z
  rw [psiK, Spec.map_comp]
  infer_instance

private theorem irreducibleSpace_fiber_genericPoint {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IrreducibleSpace X] : IrreducibleSpace (f.fiber (f (genericPoint X))) := by
  have hirr : IsIrreducible (f ⁻¹' {f (genericPoint X)} : Set X) := by
    rw [← isIrreducible_iff_closure]
    have : closure (f ⁻¹' {f (genericPoint X)} : Set X) = Set.univ := by
      apply Set.eq_univ_of_univ_subset
      rw [← (genericPoint_spec X).def]
      exact closure_mono (by simp)
    rw [this]
    exact IrreducibleSpace.isIrreducible_univ X
  refine (irreducibleSpace_def _).2 ?_
  haveI : IrreducibleSpace ↥(f ⁻¹' {f (genericPoint X)} : Set X) := Subtype.irreducibleSpace hirr
  let φ := f.fiberHomeo (f (genericPoint X))
  have h := (IrreducibleSpace.isIrreducible_univ
    ↥(f ⁻¹' {f (genericPoint X)} : Set X)).image φ.symm φ.symm.continuous.continuousOn
  rwa [Set.image_univ, φ.symm.surjective.range_eq] at h

/-- The generic fibre `X_η`, `η = f(ξ)` the image of the generic point, of a morphism with
integral source is integral. -/
theorem isIntegral_generic_fibre {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X] :
    IsIntegral (f.fiber (f (genericPoint X))) := by
  haveI := irreducibleSpace_fiber_genericPoint f
  obtain ⟨R, j, _, _, hy⟩ := exists_affine_chart_genericPoint f
  have key : ∀ y : Y, y = j ((pullback.snd f j) (genericPoint (bcScheme f j))) →
      IsReduced (f.fiber y) := by
    rintro y rfl
    haveI : Flat (Spec.map (psiK j ((pullback.snd f j) (genericPoint (bcScheme f j))))) :=
      (HasRingHomProperty.Spec_iff (P := @Flat)).mpr (flat_psiK _ _)
    haveI := isPreimmersion_spec_psiK j ((pullback.snd f j) (genericPoint (bcScheme f j)))
    exact isReduced_of_isPullback_flat_preimmersion _ _ _ _ (isPullback_fiber_toSpecQuot f j)
  haveI := key _ hy
  exact isIntegral_of_irreducibleSpace_of_isReduced _

section EulerTwist

open Filter MvPolynomial Polynomial

private noncomputable def finOneToPolynomial : MvPolynomial (Fin 1) ℚ →ₐ[ℚ] ℚ[X] :=
  MvPolynomial.aeval (fun _ => Polynomial.X)

private theorem finOneToPolynomial_eval (φ : MvPolynomial (Fin 1) ℚ) (x : ℚ) :
    Polynomial.eval x (finOneToPolynomial φ) = MvPolynomial.eval (fun _ => x) φ := by
  induction φ using MvPolynomial.induction_on with
  | C a => simp [finOneToPolynomial]
  | add p q hp hq => simp only [map_add, Polynomial.eval_add, hp, hq]
  | mul_X p i hp => simp [finOneToPolynomial] at hp ⊢; rw [hp]; simp [Subsingleton.elim i 0]

private theorem finOneToPolynomial_monomial (m : Fin 1 →₀ ℕ) (c : ℚ) :
    finOneToPolynomial (MvPolynomial.monomial m c) = Polynomial.C c * Polynomial.X ^ (m 0) := by
  simp [finOneToPolynomial, MvPolynomial.aeval_monomial, Finsupp.prod_fintype]

private theorem finOneToPolynomial_coeff (φ : MvPolynomial (Fin 1) ℚ) (j : ℕ) :
    (finOneToPolynomial φ).coeff j = φ.coeff (Finsupp.single 0 j) := by
  induction φ using MvPolynomial.induction_on' with
  | monomial m c =>
    rw [finOneToPolynomial_monomial, Polynomial.coeff_C_mul_X_pow, MvPolynomial.coeff_monomial]
    by_cases h : m 0 = j
    · have : m = Finsupp.single 0 j := Finsupp.ext fun i => by
        fin_cases i; simpa using h
      simp [h, this]
    · have : m ≠ Finsupp.single 0 j := fun hm => h (by rw [hm]; simp)
      simp only [h, this, if_false]
      by_cases hj : j = m 0
      · exact absurd hj.symm h
      · simp [hj]
  | add p q hp hq => simp [hp, hq]

private theorem finOneToPolynomial_natDegree_le (φ : MvPolynomial (Fin 1) ℚ) :
    (finOneToPolynomial φ).natDegree ≤ φ.totalDegree :=
    by
  conv_lhs => rw [φ.as_sum]
  rw [map_sum]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun m hm => ?_
  rw [finOneToPolynomial_monomial]
  refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
  have := MvPolynomial.le_totalDegree hm
  simpa [Finsupp.sum_fintype] using this

private theorem poly_lower_twist (d : ℕ) (A B : MvPolynomial (Fin 1) ℚ) (hA : A.totalDegree ≤ d)
    (hB : B.totalDegree ≤ d)
    (hc : MvPolynomial.homogeneousComponent d A = MvPolynomial.homogeneousComponent d B)
    {c : ℝ} (hcpos : 0 < c)
    (hBn : ∀ᶠ n : ℕ in atTop, c * (n : ℝ) ^ d < ((MvPolynomial.eval (fun _ => (n : ℚ)) B : ℚ) : ℝ))
        :
    ∀ᶠ n : ℕ in atTop, (c / 2) * (n : ℝ) ^ d <
      ((MvPolynomial.eval (fun _ => (n : ℚ)) A : ℚ) : ℝ) := by
  have hcoeff : (finOneToPolynomial (A - B)).coeff d = 0 := by
    rw [finOneToPolynomial_coeff, MvPolynomial.coeff_sub]
    have h := congrArg (·.coeff (Finsupp.single (0 : Fin 1) d)) hc
    simp only [MvPolynomial.coeff_homogeneousComponent] at h
    simp at h
    simp [h]
  have hdeg : (finOneToPolynomial (A - B)).natDegree ≤ d :=
    (finOneToPolynomial_natDegree_le _).trans
      ((MvPolynomial.totalDegree_sub A B).trans (max_le hA hB))
  have hlt : (finOneToPolynomial (A - B)).degree < (d : WithBot ℕ) := by
    by_cases h0 : finOneToPolynomial (A - B) = 0
    · rw [h0, Polynomial.degree_zero]; exact WithBot.bot_lt_coe d
    · rw [Polynomial.degree_eq_natDegree h0]
      refine WithBot.coe_lt_coe.2 (lt_of_le_of_ne hdeg fun hd => ?_)
      apply h0
      have : (finOneToPolynomial (A - B)).leadingCoeff = 0 := by
        have hd' : (finOneToPolynomial (A - B)).natDegree = d := by exact_mod_cast hd
        rw [Polynomial.leadingCoeff, hd']; exact hcoeff
      exact Polynomial.leadingCoeff_eq_zero.1 this
  filter_upwards [hBn, poly_lower (c0 := c / 2) (by positivity) d _ hlt] with n h1 h2
  have h3 : MvPolynomial.eval (fun _ => (n : ℚ)) A =
      MvPolynomial.eval (fun _ => (n : ℚ)) B +
        Polynomial.eval (n : ℚ) (finOneToPolynomial (A - B)) := by
    rw [finOneToPolynomial_eval, map_sub]; ring
  rw [h3]
  push_cast
  have hn : (0 : ℝ) ≤ (n : ℝ) ^ d := by positivity
  push_cast at h2
  linarith

open MonoidalCategory in
private theorem chi_eq_finrank {κ : Type u} [Field κ] {Z : Scheme.{u}}
    (g : Z ⟶ Spec (.of κ)) [IsProper g] [IsLocallyNoetherian Z]
    (L : Fin 1 → Z.Modules)
    [∀ i, SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 (L i)]
    (hL : Scheme.Modules.IsAmple Z (L 0)) (F : Z.Modules) [hF : SheafOfModules.IsCoherent F] :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (@eulerCharacteristic κ _ Z g _ (twistedSheaf F L (fun _ => (n : ℤ)))
        (twistedSheaf_isCoherent F L _) : ℚ) =
      (Module.finrank κ (cohomologyOverField κ g (twistedSheaf F L (fun _ => (n : ℤ))) 0) : ℚ) := by
  obtain ⟨N, hN⟩ := Scheme.Modules.hasEventualTwistCohomologyVanishing_of_isAmple (L 0) g hL F hF
  refine ⟨N, fun n hn => ?_⟩
  have hvan : ∀ r : ℕ, 0 < r → Limits.IsZero (cohomologyOverField κ g
      (twistedSheaf F L (fun _ => (n : ℤ))) r) := by
    intro r hr
    have h := hN n r hn hr
    exact (ModuleCat.restrictScalars
      ((Scheme.ΓSpecIso (.of κ)).inv ≫ g.appLE ⊤ ⊤ (by simp)).hom).map_isZero h
  have := twistedSheaf_isCoherent F L (fun _ => (n : ℤ))
  exact_mod_cast finsum_alternating_finrank_cohomologyOverField_eq_finrank_zero κ g _ hvan

private theorem exists_lt_finrank_twist {κ : Type u} [Field κ] {Z : Scheme.{u}}
    (g : Z ⟶ Spec (.of κ)) [IsProper g] [IsIntegral Z] [IsLocallyNoetherian Z] (d : ℕ)
    (hd : topologicalKrullDim Z = (d : WithBot ℕ∞))
    (M P : Z.Modules) [SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 M]
    [SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 P]
    (hM : Scheme.Modules.IsAmple Z M) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      c * (n : ℝ) ^ d < (Module.finrank κ (cohomologyOverField κ g
        (twistedSheaf P (fun _ : Fin 1 => M) (fun _ => (n : ℤ))) 0) : ℝ) := by
  let L : Fin 1 → Z.Modules := fun _ => M
  haveI : ∀ i, SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 (L i) := fun _ =>
      inferInstance
  have hPcoh : SheafOfModules.IsCoherent P :=
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible Z P
  have hUcoh : SheafOfModules.IsCoherent (SheafOfModules.unit Z.ringCatSheaf) :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit κ g
  obtain ⟨PP, hPdeg, hPeval⟩ := exists_eulerPolynomial_twistedSheaf_of_isProper κ g L P hPcoh
  obtain ⟨QQ, hQdeg, hQeval⟩ := exists_eulerPolynomial_twistedSheaf_of_isProper κ g L
    (SheafOfModules.unit Z.ringCatSheaf) hUcoh
  have hcomp := MMP.Mori.homogeneousComponent_eulerPolynomial_eq_fiberRank_smul κ g d hd L P hPcoh
    PP QQ hPeval hQeval
  have hrank : P.fiberRank (genericPoint Z) = 1 := by
    haveI : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} P 1 :=
      (Stacks.InvertibleRankOneScheme.stacksIsInvertible_iff_isFiniteLocallyFreeOfRank_one Z P).mp
        inferInstance
    exact Scheme.Modules.fiberRank_eq_of_isFiniteLocallyFreeOfRank P 1 _
  have hcomp' : MvPolynomial.homogeneousComponent d PP = MvPolynomial.homogeneousComponent d QQ :=
      by
    rw [hcomp, hrank]; simp
  have hdeg_of : ∀ (F : Z.Modules) (R : MvPolynomial (Fin 1) ℚ),
      (R = 0 ∨ (R.totalDegree : WithBot ℕ∞) ≤ topologicalKrullDim ↑(SheafOfModules.supp F)) →
      R.totalDegree ≤ d := by
    intro F R h
    rcases h with h | h
    · simp [h]
    · have := h.trans ((topologicalKrullDim_subspace_le Z _).trans hd.le)
      exact_mod_cast this
  have hPd := hdeg_of P PP hPdeg
  have hQd := hdeg_of _ QQ hQdeg
  obtain ⟨c, hc, N1, hN1⟩ := exists_lt_finrank_tensorPower g d hd M hM
  obtain ⟨N2, h2⟩ := chi_eq_finrank g L hM (SheafOfModules.unit Z.ringCatSheaf)
  obtain ⟨N3, h3⟩ := chi_eq_finrank g L hM P
  have hQlow : ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ) ^ d < ((MvPolynomial.eval (fun _ => (n : ℚ)) QQ : ℚ) : ℝ) := by
    rw [eventually_atTop]
    refine ⟨max N1 N2, fun n hn => ?_⟩
    have e1 := hQeval (fun _ => (n : ℤ))
    have e2 := h2 n (le_trans (le_max_right _ _) hn)
    have e3 := hN1 n (le_trans (le_max_left _ _) hn)
    have hiso : twistedSheaf (SheafOfModules.unit Z.ringCatSheaf) L (fun _ => (n : ℤ)) ≅
        Stacks.SheafOfModules.Invertible.tensorPower Z.presheaf Z.ringCatSheaf.2 M (n : ℤ) :=
      Stacks.SheafOfModules.Invertible.tensorProductLeftUnitor Z.presheaf Z.ringCatSheaf.2 _
    have e4 := finrank_cohomologyOverField_eq_of_iso _ g hiso 0
    simp only [Int.cast_natCast] at e1
    have e5 : ((MvPolynomial.eval (fun _ => (n : ℚ)) QQ : ℚ)) =
        (Module.finrank κ (cohomologyOverField κ g
          (Stacks.SheafOfModules.Invertible.tensorPower Z.presheaf Z.ringCatSheaf.2 M (n : ℤ)) 0) :
              ℚ) := by
      rw [e1, e2, e4]
    rw [e5]
    exact_mod_cast e3
  have hlow := poly_lower_twist d PP QQ hPd hQd hcomp' hc hQlow
  obtain ⟨N4, hN4⟩ := eventually_atTop.1 hlow
  refine ⟨c / 2, by positivity, max N3 N4, fun n hn => ?_⟩
  have e1 := hPeval (fun _ => (n : ℤ))
  have e2 := h3 n (le_trans (le_max_left _ _) hn)
  have e3 := hN4 n (le_trans (le_max_right _ _) hn)
  simp only [Int.cast_natCast] at e1
  have e5 : ((MvPolynomial.eval (fun _ => (n : ℚ)) PP : ℚ)) =
      (Module.finrank κ (cohomologyOverField κ g
        (twistedSheaf P L (fun _ => (n : ℤ))) 0) : ℚ) := by
    rw [e1, e2]
  rw [e5] at e3
  exact_mod_cast e3

end EulerTwist

/-- Asymptotic lower bound for sections on the generic fibre: for `A` `f`-ample and any `B`,
`h⁰(X_η, 𝒪(nA + B)|_{X_η}) > c n^d`, `d = dim X_η`. -/
private theorem exists_lt_finrank_generic_fibre {k : Type u} [Field k] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    [MMP.Mori.IsProjectiveVariety k sX] [MMP.Mori.IsProjectiveVariety k sY] (f : X ⟶ Y)
    (hf : f ≫ sY = sX) (A B : X.CartierDivisor)
    (hA : IsRelativelyAmple f (MMP.CartierDivisor.sheaf A)) (d : ℕ)
    (hd : topologicalKrullDim (f.fiber (f (genericPoint X))) = (d : ℕ∞)) :
    ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℤ, ∀ n : ℤ, k₀ ≤ n →
      c * (n : ℝ) ^ d <
        (Module.finrank (Y.residueField (f (genericPoint X)))
          (cohomologyOverField (Y.residueField (f (genericPoint X)))
            (f.fiberToSpecResidueField (f (genericPoint X)))
            ((Scheme.Modules.pullback (f.fiberι (f (genericPoint X)))).obj
              (MMP.CartierDivisor.sheaf (n • A + B))) 0) : ℝ) := by
  have hamp := isAmple_generic_fibre sX sY f hf A hA
  obtain ⟨hI, hQC, -⟩ := projective_facts sX sY f hf
  obtain ⟨hP, -, -⟩ := projective_facts' sX sY f hf
  haveI hLFT : LocallyOfFiniteType f := by
    have : LocallyOfFiniteType (f ≫ sY) := hf ▸ (inferInstance : LocallyOfFiniteType sX)
    exact LocallyOfFiniteType.of_comp (g := sY) inferInstance
  haveI hPZ : IsProper (f.fiberToSpecResidueField (f (genericPoint X))) :=
    inferInstanceAs (IsProper (pullback.snd f (Y.fromSpecResidueField (f (genericPoint X)))))
  haveI hZI : IsIntegral (f.fiber (f (genericPoint X))) := isIntegral_generic_fibre f
  haveI hZN : IsLocallyNoetherian (f.fiber (f (genericPoint X))) :=
    isLocallyNoetherian_fiber_of_locallyOfFiniteType f _
  haveI hinvA : SheafOfModules.IsInvertible (f.fiber (f (genericPoint X))).presheaf
      (f.fiber (f (genericPoint X))).ringCatSheaf.2
      ((Scheme.Modules.pullback (f.fiberι (f (genericPoint X)))).obj
        (MMP.CartierDivisor.sheaf A)) := inferInstance
  haveI hinvB : SheafOfModules.IsInvertible (f.fiber (f (genericPoint X))).presheaf
      (f.fiber (f (genericPoint X))).ringCatSheaf.2
      ((Scheme.Modules.pullback (f.fiberι (f (genericPoint X)))).obj
        (MMP.CartierDivisor.sheaf B)) := inferInstance
  have hd' : topologicalKrullDim (f.fiber (f (genericPoint X))) = ((d : ℕ) : WithBot ℕ∞) := by
    simpa using hd
  have hamp' : Scheme.Modules.IsAmple (f.fiber (f (genericPoint X)))
      ((Scheme.Modules.pullback (f.fiberι (f (genericPoint X)))).obj
        (MMP.CartierDivisor.sheaf A)) :=
    (Stacks.AmpleBridge.isAmple_iff_isAmple _ _).1 hamp
  obtain ⟨c, hc, N, hN⟩ := @exists_lt_finrank_twist _ _ _
    (f.fiberToSpecResidueField (f (genericPoint X))) hPZ hZI hZN d hd' _ _ hinvA hinvB hamp'
  refine ⟨c, hc, (N : ℤ), fun n hn => ?_⟩
  have hn0 : 0 ≤ n := le_trans (by positivity) hn
  lift n to ℕ using hn0
  have hn' : N ≤ n := by exact_mod_cast hn
  have h1 := hN n hn'
  obtain ⟨e2⟩ := nonempty_twist_iso_pullback (f.fiberι (f (genericPoint X))) A B n
  have e3 := finrank_cohomologyOverField_eq_of_iso _
    (f.fiberToSpecResidueField (f (genericPoint X))) e2 0
  rw [natCast_zsmul, Int.cast_natCast]
  exact lt_of_lt_of_eq h1 (congrArg Nat.cast e3)

/-- Asymptotic Riemann-Roch on the generic fibre: for `A` `f`-ample and any Cartier divisor `B`,
the generic rank of `𝒪(kA + B)` grows like `kⁿ`, `n = dim X - dim f(X)`. -/
private theorem exists_lt_relativeGenericRank_of_isRelativelyAmple {k : Type u} [Field k]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (sY : Y ⟶ Spec (.of k)) [MMP.Mori.IsProjectiveVariety k sX]
    [MMP.Mori.IsProjectiveVariety k sY] (f : X ⟶ Y) (hf : f ≫ sY = sX) (A B : X.CartierDivisor)
    (hA : IsRelativelyAmple f (MMP.CartierDivisor.sheaf A)) :
    ∃ a b : ℕ, topologicalKrullDim X = a ∧ topologicalKrullDim (closure (Set.range f.base)) = b ∧
      ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℤ, ∀ n : ℤ, k₀ ≤ n →
        c * (n : ℝ) ^ (a - b) <
          (relativeGenericRank f (MMP.CartierDivisor.sheaf (n • A + B)) : ℝ) := by
  obtain ⟨hI, hQC, hQS⟩ := projective_facts sX sY f hf
  obtain ⟨a, b, ha, hb, hfib⟩ := exists_dim_generic_fibre sX sY f hf
  obtain ⟨c, hc, k₀, hk⟩ := exists_lt_finrank_generic_fibre sX sY f hf A B hA (a - b) hfib
  refine ⟨a, b, ha, hb, c, hc, k₀, fun n hn => ?_⟩
  have h := hk n hn
  rw [relativeGenericRank_eq_finrank_fibre f (MMP.CartierDivisor.sheaf (n • A + B))]
  exact h

section Growth

variable {k : Type u} [Field k] {X : Scheme.{u}}

variable (k) (f : X ⟶ Spec (.of k))

/-- `h⁰` is subadditive along a short exact sequence of finite-dimensional cohomologies. -/
private theorem finrank_zero_le_add {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [FiniteDimensional k (cohomologyOverField k f S.X₁ 0)]
    [FiniteDimensional k (cohomologyOverField k f S.X₂ 0)]
    [FiniteDimensional k (cohomologyOverField k f S.X₃ 0)] :
    Module.finrank k (cohomologyOverField k f S.X₂ 0) ≤
      Module.finrank k (cohomologyOverField k f S.X₁ 0) +
        Module.finrank k (cohomologyOverField k f S.X₃ 0) := by
  obtain ⟨-, -, hex, -, -⟩ := exists_cohomologyOverField_longExactSequence k f hS
  set ψ := (cohomologyOverFieldMap k f S.g 0).hom
  have hker : Module.finrank k (LinearMap.ker ψ) ≤
      Module.finrank k (cohomologyOverField k f S.X₁ 0) :=
    (LinearMap.exact_iff.1 (hex 0)) ▸ LinearMap.finrank_range_le _
  have := LinearMap.finrank_range_add_finrank_ker ψ
  have := Submodule.finrank_le (LinearMap.range ψ)
  omega

/-- `h⁰` is monotone along the first map of a short exact sequence. -/
private theorem finrank_zero_le_of_shortExact {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [FiniteDimensional k (cohomologyOverField k f S.X₂ 0)] :
    Module.finrank k (cohomologyOverField k f S.X₁ 0) ≤
      Module.finrank k (cohomologyOverField k f S.X₂ 0) := by
  obtain ⟨-, hinj, -, -, -⟩ := exists_cohomologyOverField_longExactSequence k f hS
  exact LinearMap.finrank_le_finrank_of_injective hinj

variable [IsProper f] (L : Fin 1 → X.Modules)
  [∀ i, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L i)]

private theorem finiteDimensional_twistedSheafFunctor_obj (G : X.Modules)
    (hG : _root_.SheafOfModules.IsCoherent G) (n : Fin 1 → ℤ) :
    FiniteDimensional k (cohomologyOverField k f ((twistedSheafFunctor L n).obj G) 0) :=
  haveI := hG
  haveI := forall_finiteDimensional_cohomologyOverField_of_isProper k f _
    (@twistedSheaf_isCoherent X 1 G L _ hG n) 0
  (cohomologyOverFieldIso k f (twistedSheafFunctorObjIso L n G) 0).toLinearEquiv.symm
    |>.finiteDimensional

private theorem finrank_twistedSheafFunctor_obj (G : X.Modules) (n : Fin 1 → ℤ) :
    Module.finrank k (cohomologyOverField k f ((twistedSheafFunctor L n).obj G) 0) =
      Module.finrank k (cohomologyOverField k f (twistedSheaf G L n) 0) :=
  finrank_cohomologyOverField_eq_of_iso k f (twistedSheafFunctorObjIso L n G) 0

/-- `h⁰` of the twists is subadditive along a short exact sequence of coherent sheaves. -/
private theorem finrank_twistedSheaf_le_add {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h1 : _root_.SheafOfModules.IsCoherent S.X₁) (h2 : _root_.SheafOfModules.IsCoherent S.X₂)
    (h3 : _root_.SheafOfModules.IsCoherent S.X₃) (n : Fin 1 → ℤ) :
    Module.finrank k (cohomologyOverField k f (twistedSheaf S.X₂ L n) 0) ≤
      Module.finrank k (cohomologyOverField k f (twistedSheaf S.X₁ L n) 0) +
        Module.finrank k (cohomologyOverField k f (twistedSheaf S.X₃ L n) 0) := by
  simpa only [ShortComplex.map_X₁, ShortComplex.map_X₂, ShortComplex.map_X₃,
    finrank_twistedSheafFunctor_obj] using
    @finrank_zero_le_add k _ X f _ (shortExact_map_twistedSheafFunctor L hS n)
      (finiteDimensional_twistedSheafFunctor_obj k f L _ h1 n)
      (finiteDimensional_twistedSheafFunctor_obj k f L _ h2 n)
      (finiteDimensional_twistedSheafFunctor_obj k f L _ h3 n)

/-- `h⁰` of the twists is monotone along the first map of a short exact sequence. -/
private theorem finrank_twistedSheaf_le_of_shortExact {S : ShortComplex X.Modules}
    (hS : S.ShortExact) (h2 : _root_.SheafOfModules.IsCoherent S.X₂) (n : Fin 1 → ℤ) :
    Module.finrank k (cohomologyOverField k f (twistedSheaf S.X₁ L n) 0) ≤
      Module.finrank k (cohomologyOverField k f (twistedSheaf S.X₂ L n) 0) := by
  simpa only [ShortComplex.map_X₁, ShortComplex.map_X₂, finrank_twistedSheafFunctor_obj] using
    @finrank_zero_le_of_shortExact k _ X f _ (shortExact_map_twistedSheafFunctor L hS n)
      (finiteDimensional_twistedSheafFunctor_obj k f L _ h2 n)

end Growth

section Main

open Stacks.SheafOfModules.Invertible

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **`h⁰` of twists of `𝒪` is bounded by `h⁰` of twists of an invertible `F` plus
`C m^{n-1}`.** -/
private theorem finrank_unit_le_finrank_add_pow [IsIntegral X] [IsLocallyNoetherian X] [IsProper f]
    {n : ℕ} (hn : topologicalKrullDim X = n) (hn1 : 1 ≤ n) (F L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 F]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 0 < m →
      (Module.finrank k (cohomologyOverField k f
        (twistedSheaf (SheafOfModules.unit X.ringCatSheaf) (fun _ : Fin 1 => L) (fun _ => (m : ℤ)))
            0) : ℝ) ≤
      Module.finrank k (cohomologyOverField k f
        (twistedSheaf F (fun _ : Fin 1 => L) (fun _ => (m : ℤ))) 0) + C * (m : ℝ) ^ (n - 1) := by
  set O := SheafOfModules.unit X.ringCatSheaf
  have hO := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k f
  have hsuppO : _root_.SheafOfModules.supp O = Set.univ := supp_unit_eq_univ X
  have hdimO : natDimSupp O = n := by
    have := coe_natDimSupp_eq k f O (by rw [hsuppO]; exact Set.univ_nonempty.ne_empty)
    rw [topologicalKrullDim_supp_unit, hn] at this
    exact_mod_cast this
  obtain ⟨s, hs⟩ := exists_isRegularMeromorphicSection_of_hasNoEmbeddedPoints X
    (PlaneConic.hasNoEmbeddedPoints_of_isIntegral X) F
  obtain ⟨S, T, hS, hT, cS1, cS2, cS3, cT1, cT2, cT3, ⟨eS⟩, ⟨eT⟩, ⟨e01⟩, -, -, hS3, -⟩ :=
    exists_differenceSequences_of_supp_eq_univ k f F O hO (by omega)
      (PlaneConic.hasNoEmbeddedPoints_of_isIntegral X) hsuppO s hs
  have hd3 : topologicalKrullDim (_root_.SheafOfModules.supp S.X₃) ≤
      ((n - 1 : ℕ) : WithBot ℕ∞) := by
    by_cases h : _root_.SheafOfModules.supp S.X₃ = ∅
    · rw [(topologicalKrullDim_supp_eq_bot_iff _).2 h]; exact bot_le
    · rw [← coe_natDimSupp_eq k f _ h]
      exact_mod_cast (by omega : natDimSupp S.X₃ ≤ n - 1)
  obtain ⟨C, hC, hb⟩ :=
    MMP.Foundations.exists_finrank_cohomologyOverField_zero_twistedSheaf_le_pow k f L S.X₃
      cS3 (n - 1) hd3
  refine ⟨C, hC, fun m hm => ?_⟩
  have hle1 := finrank_twistedSheaf_le_add k f (fun _ : Fin 1 => L) hS cS1 cS2 cS3
    (fun _ => (m : ℤ))
  have hle2 := finrank_twistedSheaf_le_of_shortExact k f (fun _ : Fin 1 => L) hT cT2
    (fun _ => (m : ℤ))
  rw [finrank_cohomologyOverField_eq_of_iso k f (twistedSheafIsoOfIso _ e01 _) 0] at hle1
  have hb' := hb m (by exact_mod_cast hm)
  push_cast at hb'
  have eO : twistedSheaf S.X₂ (fun _ : Fin 1 => L) (fun _ => (m : ℤ)) ≅
      twistedSheaf O (fun _ : Fin 1 => L) (fun _ => (m : ℤ)) := twistedSheafIsoOfIso _ eS _
  have eF : twistedSheaf T.X₂ (fun _ : Fin 1 => L) (fun _ => (m : ℤ)) ≅
      twistedSheaf F (fun _ : Fin 1 => L) (fun _ => (m : ℤ)) :=
    twistedSheafIsoOfIso _ (eT ≪≫ tensorProductLeftUnitor X.presheaf X.ringCatSheaf.2 F) _
  rw [finrank_cohomologyOverField_eq_of_iso k f eO 0] at hle1
  rw [finrank_cohomologyOverField_eq_of_iso k f eF 0] at hle2
  calc _ ≤ ((Module.finrank k (cohomologyOverField k f
          (twistedSheaf T.X₁ (fun _ : Fin 1 => L) (fun _ => (m : ℤ))) 0) +
        Module.finrank k (cohomologyOverField k f
          (twistedSheaf S.X₃ (fun _ : Fin 1 => L) (fun _ => (m : ℤ))) 0) : ℕ) : ℝ) := by
        exact_mod_cast hle1
    _ ≤ _ := by
        push_cast
        have : (Module.finrank k (cohomologyOverField k f
          (twistedSheaf T.X₁ (fun _ : Fin 1 => L) (fun _ => (m : ℤ))) 0) : ℝ) ≤
          Module.finrank k (cohomologyOverField k f
            (twistedSheaf F (fun _ : Fin 1 => L) (fun _ => (m : ℤ))) 0) := by exact_mod_cast hle2
        linarith

end Main

section ZeroIso

open Stacks.SheafOfModules.Invertible MMP.CartierDivisorSheaf MonoidalCategory

variable {X : Scheme.{u}}

private noncomputable abbrev tens (X : Scheme.{u}) : X.Modules ⥤ X.Modules ⥤ X.Modules :=
  Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _
    (X.presheaf) (forget₂ CommRingCat RingCat) (X.ringCatSheaf.2)⟩

/-- Tensoring by an invertible sheaf is cancellable up to isomorphism. -/
private theorem nonempty_iso_of_tensor_iso (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] {M N : X.Modules}
    (h : ((tens X).obj M).obj L ≅ ((tens X).obj N).obj L) : Nonempty (M ≅ N) := by
  haveI : ((tens X).flip.obj L).IsEquivalence :=
    (isInvertible_iff_tensorRightFunctor_isEquivalence X.presheaf X.ringCatSheaf.2 L).1
      inferInstance
  exact ⟨((tens X).flip.obj L).preimageIso h⟩

/-- `𝒪_X(0) ≅ 𝒪_X`. -/
private theorem nonempty_sheaf_zero_iso :
    Nonempty (MMP.CartierDivisor.sheaf (0 : X.CartierDivisor) ≅ SheafOfModules.unit
        X.ringCatSheaf) := by
  set s0 := MMP.CartierDivisor.sheaf (0 : X.CartierDivisor)
  have h1 : ((tens X).obj (SheafOfModules.unit X.ringCatSheaf)).obj s0 ≅ s0 :=
    (tensorPowerSuccIso X.presheaf X.ringCatSheaf.2 s0 0).symm ≪≫
      tensorPowerReindex X.presheaf X.ringCatSheaf.2 s0 (by norm_num : (0:ℤ) + 1 = 1) ≪≫
      tensorPowerOneIso X.presheaf X.ringCatSheaf.2 s0
  have h2 : ((tens X).obj s0).obj s0 ≅ s0 :=
    sheafMulIso (0 : X.CartierDivisor) 0 ≪≫ eqToIso (by rw [add_zero])
  exact nonempty_iso_of_tensor_iso s0 (h2.trans h1.symm)

end ZeroIso

/-- A projective variety carries an effective Cartier divisor whose sheaf is ample. -/
private theorem exists_effective_ample_divisor {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [MMP.Mori.IsProjectiveVariety k sX] :
    ∃ H : X.CartierDivisor, MMP.Intersection.IsEffective H ∧
      Stacks.Ample.IsAmple X (MMP.CartierDivisor.sheaf H) := by
  have hX : AlgebraicGeometry.IsProjectiveVariety k sX := inferInstance
  haveI : IsIntegral X := hX.toIsIntegral
  obtain ⟨-, L, hLinv, hLamp⟩ := Stacks.HProjective.isQuasiProjective_of_isHQuasiProjective sX
    hX.isProjective.isHQuasiProjective
  have hL : Stacks.Ample.IsAmple X L :=
    Stacks.HProjective.isAmple_of_isRelativelyAmple_of_isAffine sX L hLamp
  obtain ⟨I, hI, -, -, n, hn, ⟨eI⟩⟩ :=
    MMP.Threefold.Resolution.exists_isEffectiveCartierDivisor_of_isAmple L hL isClosed_empty
      (Set.notMem_empty (genericPoint X))
  obtain ⟨A, hA, hAI⟩ :=
    (MMP.CartierDivisor.isEffectiveCartierDivisor_iff_exists_subscheme_eq _).1 hI
  have e : MMP.CartierDivisor.sheaf A ≅ Stacks.Ample.tensorPowModule X L (n : ℤ) :=
    MMP.CartierDivisor.sheafIsoInvertibleSheaf A hA ≪≫ eqToIso (by rw [hAI]) ≪≫ eI.symm
  refine ⟨A, hA, ?_⟩
  exact (Stacks.RelativeVeryAmple.isAmple_congr _ _ e).mpr
    (Stacks.AmplePositivePower.isAmple_tensorPowModule_of_isAmple L n hn hL)

/-- On an integral proper scheme of dimension zero an invertible sheaf has a non-zero section. -/
private theorem finrank_ne_zero_of_dim_zero {κ : Type u} [Field κ] {Z : Scheme.{u}}
    (g : Z ⟶ Spec (.of κ)) [IsProper g] [IsIntegral Z] [IsLocallyNoetherian Z]
    (hd : topologicalKrullDim Z = 0) (P : Z.Modules)
    [SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 P] :
    Module.finrank κ (cohomologyOverField κ g P 0) ≠ 0 := by
  have hall : ∀ x : Z, x = genericPoint Z := by
    intro x
    have hmin := Order.krullDim_nonpos_iff_forall_isMin.1 (le_of_eq hd)
    let W : TopologicalSpace.IrreducibleCloseds Z :=
      ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
    let T : TopologicalSpace.IrreducibleCloseds Z :=
      ⟨Set.univ, IrreducibleSpace.isIrreducible_univ Z, isClosed_univ⟩
    have hWT : W ≤ T := fun _ _ => Set.mem_univ _
    have hTW : T ≤ W := hmin T hWT
    have hx : IsGenericPoint x ⊤ := by
      change closure {x} = Set.univ
      exact Set.eq_univ_of_univ_subset hTW
    exact hx.eq (genericPoint_spec Z)
  obtain ⟨U, -, e, hxU, he⟩ := MMP.Intersection.exists_isTrivializingGenerator P
    (show genericPoint Z ∈ (⊤ : Z.Opens) from trivial)
  have hU : U = ⊤ := eq_top_iff.2 fun y _ => by rw [hall y]; exact hxU
  subst hU
  have he0 : e ≠ 0 := by
    intro h0
    have h1 := (he ⊤ le_rfl).1 (a₁ := (1 : Γ(Z, ⊤))) (a₂ := 0) (by
      simp only [MMP.Intersection.modules_map_id, h0, smul_zero])
    exact one_ne_zero h1
  haveI : SheafOfModules.IsCoherent P :=
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible Z P
  haveI := finiteDimensional_cohomologyOverField_of_isProper κ g P 0
  haveI : Nontrivial (cohomologyOverField κ g P 0) :=
    @Equiv.nontrivial _ _
      (cohomologyOverFieldZeroIsoSections κ g P).toLinearEquiv.toEquiv ⟨⟨e, 0, he0⟩⟩
  exact (Module.finrank_pos (R := κ) (M := cohomologyOverField κ g P 0)).ne'

/-- If `a = b + d` in `WithBot ℕ∞` with `a b` natural, then `d = a - b`. -/
private theorem eq_natSub_of_coe_eq_add {a b : ℕ} {d : WithBot ℕ∞}
    (h : (a : WithBot ℕ∞) = b + d) : d = ((a - b : ℕ) : ℕ∞) := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h
  | coe d =>
    induction d using ENat.recTopCoe with
    | top =>
      rw [← WithBot.coe_natCast, ← WithBot.coe_natCast, ← WithBot.coe_add, WithBot.coe_inj] at h
      simp at h
    | coe d =>
      have : a = b + d := by exact_mod_cast h
      subst this
      simp

/-- For `0 < c` there is a natural number `0 < m` with `k₀ ≤ m` and `C < c * m`. -/
theorem exists_nat_pos_le_and_lt_mul (k₀ : ℤ) {C c : ℝ} (hc : 0 < c) :
    ∃ m : ℕ, 0 < m ∧ k₀ ≤ (m : ℤ) ∧ C < c * m := by
  refine ⟨max (max 1 k₀.toNat) (⌈C / c⌉₊ + 1), by omega, ?_, ?_⟩
  · have := Int.self_le_toNat k₀
    have h2 : k₀.toNat ≤ max (max 1 k₀.toNat) (⌈C / c⌉₊ + 1) :=
      le_trans (le_max_right _ _) (le_max_left _ _)
    omega
  · have h1 : C / c < ((max (max 1 k₀.toNat) (⌈C / c⌉₊ + 1) : ℕ) : ℝ) := by
      have : ⌈C / c⌉₊ < max (max 1 k₀.toNat) (⌈C / c⌉₊ + 1) :=
        lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
      exact lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast this)
    rwa [div_lt_iff₀ hc, mul_comm] at h1

/-- If `C < c * m` with `0 < m` and `1 ≤ n`, then `C * m ^ (n - 1) < c * m ^ n`. -/
theorem mul_pow_pred_lt_mul_pow {C c m : ℝ} (hm : 0 < m) {n : ℕ} (hn : 1 ≤ n)
    (h : C < c * m) : C * m ^ (n - 1) < c * m ^ n := by
  have hpow : m ^ n = m ^ (n - 1) * m := by
    rw [← pow_succ, Nat.sub_add_cancel hn]
  rw [hpow, ← mul_assoc, mul_comm c, mul_assoc, mul_comm C]
  exact mul_lt_mul_of_pos_left h (pow_pos hm _)

/-- **The generic-fibre half of the forward direction.** Let `f : X ⟶ Y` be a proper morphism of
schemes locally of finite type over a field `k`, with `X` integral. For an `f`-big Cartier divisor
`D` and any Cartier divisor `H` there is `m > 0` with `f_* 𝒪_X(mD - H)` of non-zero rank at the
generic point of `f(X)`. -/
theorem exists_pos_relativeGenericRank_sub_of_isRelativelyBigCartier {k : Type u} [Field k]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [IsIntegral X]
    [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] (f : X ⟶ Y) [IsProper f]
    (hf : f ≫ sY = sX) {D : X.CartierDivisor} (hD : IsRelativelyBigCartier f D)
    (H : X.CartierDivisor) :
    ∃ m : ℕ, 0 < m ∧
      relativeGenericRank f (MMP.CartierDivisor.sheaf (m • D + -H)) ≠ 0 := by
  haveI : IsSeparated f := IsProper.toIsSeparated
  haveI : QuasiSeparated f := IsSeparated.instQuasiSeparated f
  haveI hPZ : IsProper (f.fiberToSpecResidueField (f (genericPoint X))) :=
    inferInstanceAs (IsProper (pullback.snd f (Y.fromSpecResidueField (f (genericPoint X)))))
  haveI hZI : IsIntegral (f.fiber (f (genericPoint X))) := isIntegral_generic_fibre f
  haveI hZN : IsLocallyNoetherian (f.fiber (f (genericPoint X))) :=
    isLocallyNoetherian_fiber_of_locallyOfFiniteType f _
  have hrel : ∀ B : X.CartierDivisor,
      relativeGenericRank f (MMP.CartierDivisor.sheaf B) =
      Module.finrank (Y.residueField (f (genericPoint X)))
        (cohomologyOverField (Y.residueField (f (genericPoint X)))
          (f.fiberToSpecResidueField (f (genericPoint X)))
          ((Scheme.Modules.pullback (f.fiberι (f (genericPoint X)))).obj
            (MMP.CartierDivisor.sheaf B)) 0) := by
    intro B
    haveI : (MMP.CartierDivisor.sheaf B).IsQuasicoherent :=
      SheafOfModules.isQuasicoherent_of_iso
        (Iso.refl (MMP.CartierDivisor.sheaf B)) inferInstance
    exact relativeGenericRank_eq_finrank_fibre f _
  obtain ⟨a, b, ha, hb, c, hc, k₀, hk⟩ := hD
  have hfib : topologicalKrullDim (f.fiber (f (genericPoint X))) = ((a - b : ℕ) : ℕ∞) := by
    have h := dim_formula_aux sX sY f hf
    rw [ha, hb] at h
    exact eq_natSub_of_coe_eq_add h
  haveI hinvD : SheafOfModules.IsInvertible (f.fiber (f (genericPoint X))).presheaf
      (f.fiber (f (genericPoint X))).ringCatSheaf.2
      ((Scheme.Modules.pullback (f.fiberι (f (genericPoint X)))).obj
        (MMP.CartierDivisor.sheaf D)) := inferInstance
  haveI hinvH : SheafOfModules.IsInvertible (f.fiber (f (genericPoint X))).presheaf
      (f.fiber (f (genericPoint X))).ringCatSheaf.2
      ((Scheme.Modules.pullback (f.fiberι (f (genericPoint X)))).obj
        (MMP.CartierDivisor.sheaf (-H))) := inferInstance
  by_cases hn0 : a - b = 0
  · refine ⟨1, one_pos, ?_⟩
    rw [hrel]
    haveI hinvP : SheafOfModules.IsInvertible (f.fiber (f (genericPoint X))).presheaf
        (f.fiber (f (genericPoint X))).ringCatSheaf.2
        ((Scheme.Modules.pullback (f.fiberι (f (genericPoint X)))).obj
          (MMP.CartierDivisor.sheaf (1 • D + -H))) := inferInstance
    have hd0 : topologicalKrullDim (f.fiber (f (genericPoint X))) = 0 := by
      rw [hfib, hn0]
      rfl
    exact @finrank_ne_zero_of_dim_zero _ _ _ (f.fiberToSpecResidueField (f (genericPoint X)))
      hPZ hZI hZN hd0 _ hinvP
  · have hn1 : 1 ≤ a - b := Nat.pos_of_ne_zero hn0
    have hdim :
        topologicalKrullDim (f.fiber (f (genericPoint X))) = ((a - b : ℕ) : WithBot ℕ∞) := by
      rw [hfib]
      norm_cast
    obtain ⟨C, hC, hineq⟩ := @finrank_unit_le_finrank_add_pow ↑(Y.residueField (f (genericPoint X)))
        _ _
      (f.fiberToSpecResidueField (f (genericPoint X))) hZI hZN hPZ (a - b) hdim hn1 _ _ hinvH hinvD
    have hunit : ∀ m : ℕ, Module.finrank (Y.residueField (f (genericPoint X)))
        (cohomologyOverField (Y.residueField (f (genericPoint X)))
          (f.fiberToSpecResidueField (f (genericPoint X)))
          (twistedSheaf (SheafOfModules.unit (f.fiber (f (genericPoint X))).ringCatSheaf)
            (fun _ : Fin 1 => (Scheme.Modules.pullback (f.fiberι (f (genericPoint X)))).obj
              (MMP.CartierDivisor.sheaf D)) (fun _ => (m : ℤ))) 0) =
        relativeGenericRank f (MMP.CartierDivisor.sheaf (m • D)) := by
      intro m
      obtain ⟨e0⟩ := nonempty_sheaf_zero_iso (X := X)
      let eu : SheafOfModules.unit (f.fiber (f (genericPoint X))).ringCatSheaf ≅
          (Scheme.Modules.pullback (f.fiberι (f (genericPoint X)))).obj
            (MMP.CartierDivisor.sheaf (0 : X.CartierDivisor)) :=
        (Stacks.RelativeAmple.pullbackUnitModuleIso (f.fiberι (f (genericPoint X)))).symm ≪≫
          (Scheme.Modules.pullback (f.fiberι (f (genericPoint X)))).mapIso e0.symm
      obtain ⟨e1⟩ := nonempty_twist_iso_pullback (f.fiberι (f (genericPoint X))) D 0 m
      have h1 := finrank_cohomologyOverField_eq_of_iso _
        (f.fiberToSpecResidueField (f (genericPoint X))) (twistedSheafIsoOfIso _ eu _ ≪≫ e1) 0
      refine h1.trans ?_
      rw [add_zero]
      exact (hrel _).symm
    have hF : ∀ m : ℕ, Module.finrank (Y.residueField (f (genericPoint X)))
        (cohomologyOverField (Y.residueField (f (genericPoint X)))
          (f.fiberToSpecResidueField (f (genericPoint X)))
          (twistedSheaf ((Scheme.Modules.pullback (f.fiberι (f (genericPoint X)))).obj
            (MMP.CartierDivisor.sheaf (-H)))
            (fun _ : Fin 1 => (Scheme.Modules.pullback (f.fiberι (f (genericPoint X)))).obj
              (MMP.CartierDivisor.sheaf D)) (fun _ => (m : ℤ))) 0) =
        relativeGenericRank f (MMP.CartierDivisor.sheaf (m • D + -H)) := by
      intro m
      obtain ⟨e1⟩ := nonempty_twist_iso_pullback (f.fiberι (f (genericPoint X))) D (-H) m
      exact (finrank_cohomologyOverField_eq_of_iso _
        (f.fiberToSpecResidueField (f (genericPoint X))) e1 0).trans (hrel _).symm
    obtain ⟨m, hm1, hm2, hm3⟩ := exists_nat_pos_le_and_lt_mul k₀ hc
    refine ⟨m, hm1, ?_⟩
    have hbig := hk (m : ℤ) hm2
    rw [natCast_zsmul, ← hunit m] at hbig
    have hin := hineq m hm1
    intro h0
    have hF0 := (hF m).trans h0
    rw [hF0] at hin
    have := mul_pow_pred_lt_mul_pow (by exact_mod_cast hm1 : (0 : ℝ) < m) hn1 hm3
    push_cast at hin
    simp only [Int.cast_natCast] at hbig
    linarith

/-- The fibre rank of a zero module is zero. -/
theorem fiberRank_eq_zero_of_isZero {Y : Scheme.{u}} (G : Y.Modules)
    (hG : Limits.IsZero G) (y : Y) : Scheme.Modules.fiberRank G y = 0 := by
  have hsec : ∀ (U : Y.Opens) (m : Γ(G, U)), m = 0 := by
    intro U m
    have h := (SheafOfModules.evaluation Y.ringCatSheaf (op U)).map_isZero hG
    exact (ModuleCat.isZero_iff_subsingleton.1 h).elim m 0
  have hstalk : ∀ n : TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf y, n = 0 := by
    intro n
    obtain ⟨U, hU, m, rfl⟩ := TopCat.Presheaf.germ_exist G.val.presheaf n
    rw [hsec U m]
    exact map_zero _
  unfold Scheme.Modules.fiberRank
  letI : Module (Y.presheaf.stalk y) (G.presheaf.stalk y) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := Y.presheaf) G.val y
  letI : Algebra (Y.presheaf.stalk y) (Y.residueField y) := (Y.residue y).hom.toAlgebra
  haveI : Subsingleton (Y.residueField y ⊗[Y.presheaf.stalk y] G.presheaf.stalk y) := by
    refine ⟨fun a b => ?_⟩
    have : ∀ x : Y.residueField y ⊗[Y.presheaf.stalk y] G.presheaf.stalk y, x = 0 := fun x =>
      TensorProduct.inductionOn x
        (fun a n => by rw [hstalk n]; exact TensorProduct.tmul_zero _ a)
        (fun a b ha hb => by rw [ha, hb, add_zero])
    exact (this a).trans (this b).symm
  show Module.finrank (Y.residueField y)
    (Y.residueField y ⊗[Y.presheaf.stalk y] G.presheaf.stalk y) = 0
  exact Module.finrank_zero_of_subsingleton

/-- The tensor product of `𝒪_Y`-modules, at the monoidal structure of the Stacks library. -/
private noncomputable abbrev tensorS (Y : Scheme.{u}) (A B : Y.Modules) : Y.Modules :=
  @MonoidalCategoryStruct.tensorObj Y.Modules _
    (@MonoidalCategory.toMonoidalCategoryStruct _ _ (Stacks.SheafInternalHom.schemeMonoidalCategory
        Y)) A B

/-- A sheaf of modules generated by sections whose values at `⊤` vanish is zero. -/
private theorem exists_ne_zero_of_generatingSections {Y : Scheme.{u}}
    {N : SheafOfModules.{u} Y.ringCatSheaf} (σ : N.GeneratingSections) (hN : ¬ Limits.IsZero N) :
    ∃ i, (σ.s i).1 (op ⊤) ≠ 0 := by
  by_contra h
  push Not at h
  apply hN
  have hπ : σ.π = 0 := by
    apply N.freeHomEquiv.injective
    funext i
    apply Subtype.ext
    funext X
    have e1 : N.freeHomEquiv σ.π i = σ.s i := by
      change (N.freeHomEquiv (N.freeHomEquiv.symm σ.s)) i = σ.s i
      rw [Equiv.apply_symm_apply]
    rw [e1]
    obtain ⟨U⟩ := X
    have hc := (σ.s i).2 (show op (⊤ : Y.Opens) ⟶ op U from (homOfLE (le_top : U ≤ ⊤)).op)
    have h0 := h i
    rw [← hc, h0]
    have hR : (N.freeHomEquiv (0 : SheafOfModules.free σ.I ⟶ N) i).1 (op U) = 0 := by
      show (N.unitHomEquiv (SheafOfModules.ιFree i ≫ 0)).val (op U) = 0
      rw [SheafOfModules.unitHomEquiv_apply_coe, Limits.comp_zero]
      have hz : SheafOfModules.Hom.val (0 : SheafOfModules.unit Y.ringCatSheaf ⟶ N) = 0 :=
        (SheafOfModules.forget _).map_zero _ _
      rw [hz]
      have h2 : PresheafOfModules.Hom.app (0 : (SheafOfModules.unit Y.ringCatSheaf).val ⟶ N.val)
          (op U) = 0 := (PresheafOfModules.evaluation _ (op U)).map_zero _ _
      rw [h2]
      first | rfl | exact LinearMap.zero_apply _ | simp [ModuleCat.hom_zero]
    rw [hR]
    exact (map_zero (ConcreteCategory.hom (N.val.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op)))
  exact Limits.IsZero.of_epi_eq_zero σ.π hπ

/-- On a locally Noetherian scheme, a non-zero coherent module acquires a non-zero global
section after a twist by a high power of an ample invertible sheaf. -/
private theorem exists_ne_zero_section_twist {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (M : Y.Modules) [Stacks.Ample.IsInvertibleModule Y M] (hM : Stacks.Ample.IsAmple Y M)
    (G : Y.Modules) [SheafOfModules.IsCoherent G] (hG : ¬ Limits.IsZero G) :
    ∃ q : ℕ, ∃ t : Γ(tensorS Y G (Stacks.Ample.tensorPowModule Y M (q : ℤ)), ⊤),
      t ≠ 0 := by
  obtain ⟨hqc, hft⟩ :=
      Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent G
  obtain ⟨n₀, hn₀⟩ := Stacks.AmpleLocalGeneration.isEventuallyGloballyGenerated_of_isAmple M hM G
    hqc hft
  obtain ⟨σ, -⟩ := hn₀ (n₀.toNat : ℤ) (Int.self_le_toNat n₀)
  have hN : ¬ Limits.IsZero (tensorS Y G (Stacks.Ample.tensorPowModule Y M (n₀.toNat : ℤ))) := by
    intro hz
    haveI : ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Y.presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ (Y.presheaf) (forget₂ CommRingCat RingCat)
          (Y.ringCatSheaf.2)⟩).flip.obj
        (Stacks.Ample.tensorPowModule Y M (n₀.toNat : ℤ))).IsEquivalence :=
      (Stacks.SheafOfModules.Invertible.isInvertible_iff_tensorRightFunctor_isEquivalence
        Y.presheaf Y.ringCatSheaf.2 _).1 inferInstance
    exact hG (IsZero.of_full_of_faithful_of_isZero
      ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Y.presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ (Y.presheaf) (forget₂ CommRingCat RingCat)
          (Y.ringCatSheaf.2)⟩).flip.obj (Stacks.Ample.tensorPowModule Y M (n₀.toNat : ℤ))) G
      (hz.of_iso (Stacks.SheafOfModules.tensorObjIso Y.presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y) G
        (Stacks.Ample.tensorPowModule Y M (n₀.toNat : ℤ))).symm))
  obtain ⟨i, hi⟩ := exists_ne_zero_of_generatingSections σ hN
  exact ⟨n₀.toNat, (σ.s i).1 (op ⊤), hi⟩

/-- A divisor with non-zero generic rank becomes linearly equivalent to an effective divisor
after a twist by a pull-back from `Y`. -/
private theorem exists_effective_of_relativeGenericRank_ne_zero {k : Type u} [Field k]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    [MMP.Mori.IsProjectiveVariety k sX] [MMP.Mori.IsProjectiveVariety k sY] (f : X ⟶ Y)
    (hf : f ≫ sY = sX) (M : Y.Modules) [Stacks.Ample.IsInvertibleModule Y M]
    (hM : Stacks.Ample.IsAmple Y M) (B : X.CartierDivisor)
    (hB : relativeGenericRank f (MMP.CartierDivisor.sheaf B) ≠ 0) :
    ∃ (q : ℕ) (E Nn : X.CartierDivisor), MMP.Intersection.IsEffective E ∧
      Nonempty (MMP.CartierDivisor.sheaf Nn ≅
        (Scheme.Modules.pullback f).obj (Stacks.Ample.tensorPowModule Y M (-(q : ℤ)))) ∧
      MMP.Intersection.LinearlyEquivalent (E + Nn) B := by
  obtain ⟨hI, hQC, hQS⟩ := projective_facts sX sY f hf
  obtain ⟨hP, hN, hNY⟩ := projective_facts' sX sY f hf
  set F0 := MMP.CartierDivisor.sheaf B with hF0
  haveI hF0coh : SheafOfModules.IsCoherent F0 :=
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible X F0
  haveI hGcoh : SheafOfModules.IsCoherent ((Scheme.Modules.pushforward f).obj F0) :=
    ProperCoherenceWitness.isCoherent_pushforward f F0
  have hG : ¬ Limits.IsZero ((Scheme.Modules.pushforward f).obj F0) := fun h0 =>
    hB (fiberRank_eq_zero_of_isZero _ h0 (f (genericPoint X)))
  obtain ⟨q, t, ht⟩ := exists_ne_zero_section_twist M hM _ hG
  haveI hMq : Stacks.Ample.IsInvertibleModule Y (Stacks.Ample.tensorPowModule Y M (q : ℤ)) :=
    inferInstance
  have hproj : ∃ t' : Γ(MonoidalCategory.tensorObj F0 ((Scheme.Modules.pullback f).obj
      (Stacks.Ample.tensorPowModule Y M (q : ℤ))), ⊤), t' ≠ 0 := by
    let e0 := Stacks.SheafOfModules.tensorObjIso Y.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y)
      ((Scheme.Modules.pushforward f).obj F0) (Stacks.Ample.tensorPowModule Y M (q : ℤ))
    haveI : Stacks.SheafOfModules.IsInvertible Y.presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y)
        (Stacks.Ample.tensorPowModule Y M (q : ℤ)) := inferInstance
    let pf := @Stacks.ProjectionFormula.projectionFormulaIso X.toRingedSpace Y.toRingedSpace
      f.toLRSHom.toShHom F0 (Stacks.Ample.tensorPowModule Y M (q : ℤ)) this
    let E := e0 ≪≫ pf
    have hbij := ConcreteCategory.bijective_of_isIso
      (((SheafOfModules.evaluation Y.ringCatSheaf (op (⊤ : Y.Opens))).mapIso E).hom)
    exact ⟨(SheafOfModules.evaluation Y.ringCatSheaf (op (⊤ : Y.Opens))).map E.hom t,
      fun h => ht (hbij.1 (h.trans (map_zero _).symm))⟩
  obtain ⟨t', ht'⟩ := hproj
  haveI hL' : Stacks.Ample.IsInvertibleModule X (MonoidalCategory.tensorObj F0
      ((Scheme.Modules.pullback f).obj (Stacks.Ample.tensorPowModule Y M (q : ℤ)))) :=
    Stacks.AmplePullbackPart1.isInvertibleModule_tensorModules X F0
      ((Scheme.Modules.pullback f).obj (Stacks.Ample.tensorPowModule Y M (q : ℤ)))
  obtain ⟨E, hE, ⟨eE⟩⟩ := exists_isEffective_sheaf_iso_of_ne_zero _ t' ht'
  haveI hMn : Stacks.Ample.IsInvertibleModule Y (Stacks.Ample.tensorPowModule Y M (-(q : ℤ))) :=
    inferInstance
  haveI hPn : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      ((Scheme.Modules.pullback f).obj (Stacks.Ample.tensorPowModule Y M (-(q : ℤ)))) :=
    inferInstance
  obtain ⟨Nn, ⟨eN'⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf
    ((Scheme.Modules.pullback f).obj (Stacks.Ample.tensorPowModule Y M (-(q : ℤ))))
  refine ⟨q, E, Nn, hE, ⟨eN'.symm⟩, ?_⟩
  let Tq := Stacks.Ample.tensorPowModule Y M (q : ℤ)
  let Tn := Stacks.Ample.tensorPowModule Y M (-(q : ℤ))
  have hPP : MonoidalCategory.tensorObj ((Scheme.Modules.pullback f).obj Tq)
      ((Scheme.Modules.pullback f).obj Tn) ≅ MonoidalCategory.tensorUnit X.Modules :=
    (Stacks.ProjectiveBundleConormal.pullbackTensorComparisonIso f Tq Tn).symm ≪≫
      (Scheme.Modules.pullback f).mapIso
        (Stacks.Ample.tensorPowModuleAddIso Y M (q : ℤ) (-(q : ℤ)) ≪≫
          Stacks.RelativeVeryAmple.tensorPowModuleCongr Y M (add_neg_cancel (q : ℤ)) ≪≫
          Stacks.Ample.tensorPowModuleZeroIso Y M) ≪≫
      Stacks.RelativeAmple.pullbackUnitModuleIso f
  have hiso : MMP.CartierDivisor.sheaf (E + Nn) ≅
      MMP.CartierDivisor.sheaf B :=
    (MMP.CartierDivisorSheaf.sheafMulIso E Nn).symm ≪≫
      MonoidalCategory.tensorIso eE eN'.symm ≪≫ MonoidalCategory.associator _ _ _ ≪≫
      MonoidalCategory.whiskerLeftIso _ hPP ≪≫ MonoidalCategory.rightUnitor _
  exact MMP.CartierDivisor.linearlyEquivalent_of_sheaf_iso hiso

/-- Relative ampleness depends only on the isomorphism class. -/
private theorem isRelativelyAmple_of_iso {X Y : Scheme.{u}} (f : X ⟶ Y) {L L' : X.Modules}
    [Stacks.Ample.IsInvertibleModule X L] [Stacks.Ample.IsInvertibleModule X L'] (e : L ≅ L')
    (h : IsRelativelyAmple f L) : IsRelativelyAmple f L' := by
  intro y
  obtain ⟨V, hV, hyV, hamp⟩ := h y
  refine ⟨V, hV, hyV, ?_⟩
  exact (Stacks.RelativeVeryAmple.isAmple_congr _ _
    ((RingedSpaceModuleAdjunction.modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).mapIso e)).1 hamp

/-- Forward direction: an `f`-big Cartier divisor has a multiple `mD ∼ A + E`. -/
private theorem exists_linearlyEquivalent_add_of_isRelativelyBigCartier {k : Type u} [Field k]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (sY : Y ⟶ Spec (.of k)) [MMP.Mori.IsProjectiveVariety k sX]
    [MMP.Mori.IsProjectiveVariety k sY] (f : X ⟶ Y)
    (hf : f ≫ sY = sX) (D : X.CartierDivisor) (hD : IsRelativelyBigCartier f D) :
      ∃ m : ℕ, 0 < m ∧ ∃ A E : X.CartierDivisor,
        IsRelativelyAmple f (MMP.CartierDivisor.sheaf A) ∧
        MMP.Intersection.IsEffective E ∧
        MMP.Intersection.LinearlyEquivalent (m • D) (A + E) := by
  obtain ⟨hI, -, -⟩ := projective_facts sX sY f hf
  obtain ⟨hP, -, -⟩ := projective_facts' sX sY f hf
  obtain ⟨H, hHeff, hHamp⟩ := exists_effective_ample_divisor sX
  obtain ⟨m, hm, hne⟩ :=
    exists_pos_relativeGenericRank_sub_of_isRelativelyBigCartier sX sY f hf hD H
  obtain ⟨Hy, hHyeff, hHyamp⟩ := exists_effective_ample_divisor sY
  obtain ⟨q, E, Nn, hE, ⟨eN⟩, hlin⟩ := exists_effective_of_relativeGenericRank_ne_zero sX sY f hf
    (MMP.CartierDivisor.sheaf Hy) hHyamp (m • D + -H) hne
  refine ⟨m, hm, H + Nn, E, ?_, hE, ?_⟩
  · -- `H + Nn` is `f`-ample: `H` is ample, hence `f`-ample, and `Nn ≅ f^*(M^{-q})`
    haveI : Stacks.Ample.IsInvertibleModule Y
        (Stacks.Ample.tensorPowModule Y (MMP.CartierDivisor.sheaf Hy) (-(q : ℤ))) :=
      inferInstance
    have hH : IsRelativelyAmple f (MMP.CartierDivisor.sheaf H) :=
      MMP.Threefold.Resolution.isRelativelyAmple_of_isAmple f _ hHamp
    have hH' := MMP.Threefold.Resolution.isRelativelyAmple_tensorModules_modulePullback f
      (MMP.CartierDivisor.sheaf H)
      (Stacks.Ample.tensorPowModule Y (MMP.CartierDivisor.sheaf Hy) (-(q : ℤ))) hH
    haveI := Stacks.AmplePullbackPart1.isInvertibleModule_tensorModules X
      (MMP.CartierDivisor.sheaf H)
      ((RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom).obj
        (Stacks.Ample.tensorPowModule Y (MMP.CartierDivisor.sheaf Hy) (-(q : ℤ))))
    refine isRelativelyAmple_of_iso f ?_ hH'
    exact (MonoidalCategory.whiskerLeftIso _ eN).symm ≪≫
      MMP.CartierDivisorSheaf.sheafMulIso H Nn
  · have h1 := MMP.Intersection.linearlyEquivalent_equivalence.symm hlin
    have h3 := h1.add (MMP.Intersection.linearlyEquivalent_equivalence.refl H)
    convert h3 using 1 <;> abel

/-- Converse: `mD ∼ A + E` with `A` `f`-ample and `E` effective makes `D` `f`-big. -/
private theorem isRelativelyBigCartier_of_linearlyEquivalent_add {k : Type u} [Field k]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (sY : Y ⟶ Spec (.of k)) [MMP.Mori.IsProjectiveVariety k sX]
    [MMP.Mori.IsProjectiveVariety k sY] (f : X ⟶ Y)
    (hf : f ≫ sY = sX) (D : X.CartierDivisor) (m : ℕ) (hm : 0 < m) (A E : X.CartierDivisor)
    (hA : IsRelativelyAmple f (MMP.CartierDivisor.sheaf A))
    (hE : MMP.Intersection.IsEffective E)
    (hDAE : MMP.Intersection.LinearlyEquivalent (m • D) (A + E)) :
    IsRelativelyBigCartier f D := by
  obtain ⟨hI, -, -⟩ := projective_facts sX sY f hf
  exact isRelativelyBigCartier_of_generic_rank f D A E m hm
    (fun B E' hE' => relativeGenericRank_le_of_isEffective sX sY f hf B E' hE')
    (fun B B' h => relativeGenericRank_eq_of_linearlyEquivalent sX sY f hf B B' h)
    (fun B => exists_lt_relativeGenericRank_of_isRelativelyAmple sX sY f hf A B hA) hE hDAE

/-- **Relative bigness over a projective target.** Let `f : X ⟶ Y` be a morphism of projective
varieties over an algebraically closed field of characteristic zero. A Cartier divisor `D` on
`X` is `f`-big if and only if there are `m > 0`, an `f`-ample Cartier divisor `A` and an
effective Cartier divisor `E` with `mD ∼ A + E`. -/
@[mmp "lem_mmp_foundation_projective_relative_big_decomposition"]
public theorem isRelativelyBigCartier_iff_exists_linearlyEquivalent_add {k : Type u} [Field k]
    [IsAlgClosed k] [CharZero k] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (sY : Y ⟶ Spec (.of k)) [IsProjectiveVariety k sX] [IsProjectiveVariety k sY] (f : X ⟶ Y)
    (hf : f ≫ sY = sX) (D : X.CartierDivisor) :
    IsRelativelyBigCartier f D ↔
      ∃ m : ℕ, 0 < m ∧ ∃ A E : X.CartierDivisor,
        IsRelativelyAmple f (MMP.CartierDivisor.sheaf A) ∧
        MMP.Intersection.IsEffective E ∧
        MMP.Intersection.LinearlyEquivalent (m • D) (A + E) := by
  refine ⟨exists_linearlyEquivalent_add_of_isRelativelyBigCartier sX sY f hf D, ?_⟩
  rintro ⟨m, hm, A, E, hA, hE, hDAE⟩
  exact isRelativelyBigCartier_of_linearlyEquivalent_add sX sY f hf D m hm A E hA hE hDAE

end RelativeBig

end MMP.Mori

end
