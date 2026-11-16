/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.Attr
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Etale.Locus
public import Mathlib.RingTheory.Kaehler.JacobiZariski
public import Mathlib.RingTheory.LocalRing.Module

/-!
# Étale coordinate charts over an arbitrary field

Let `f : X ⟶ Spec k` be smooth, `k` any field, `x ∈ X` any scheme point, and let
`n = rank_x Ω_{X/k}`. Then `x` has an affine open neighbourhood `U` with an étale `k`-morphism
`U ⟶ 𝔸^n_k`. More precisely, any `n` regular functions `g_1, …, g_n` on a neighbourhood of `x`
whose differentials form a basis of the fibre `Ω_{X/k} ⊗ κ(x)` define, on a smaller affine
neighbourhood `U` of `x`, an étale morphism `(g_1, …, g_n) : U ⟶ 𝔸^n_k`. No perfectness of `k`
is assumed, and `x` need not be closed.

## Main results

* `MMP.Flips.ResolutionInputs.exists_isAffineOpen_etale_homOfVector`: functions whose
  differentials form a basis of `Ω_{X/k} ⊗ κ(x)` are étale coordinates near `x`.
* `MMP.Flips.ResolutionInputs.exists_isAffineOpen_etale_affineSpace`: an étale `k`-morphism
  from an affine neighbourhood of `x` to `𝔸^n_k`, `n = rank_x Ω_{X/k}`.

## Implementation notes

The stalk of `Ω_{X/k}` at `x` is written as the module of Kähler differentials
`Ω[𝒪_{X,x} ⁄ 𝒪_{Spec k, f x}]` of the stalk map of `f`, an `𝒪_{X,x}`-module; the local ring
`𝒪_{Spec k, f x}` is `k` itself, being a localization of a field. This is the stalk of the sheaf
of relative differentials by Stacks Tag 01V0 at a point. The rank `rank_x Ω_{X/k}` is its
`Module.finrank` over `𝒪_{X,x}` (the module is free, `f` being smooth), and the fibre at `x` is
`κ(x) ⊗_{𝒪_{X,x}} Ω[𝒪_{X,x} ⁄ 𝒪_{Spec k, f x}]`. The differential of a section `g` over an open
`V ∋ x` is the universal derivation of its germ at `x`.

The coordinates of affine space are indexed by `ULift.{u} (Fin n)`, so that the index type lies in
the universe of the schemes, as `AlgebraicGeometry.AffineSpace` requires. The morphism defined by
the functions is `AlgebraicGeometry.AffineSpace.homOfVector`, applied to `U ⟶ X ⟶ Spec k` and the
restrictions of the `g_i` to `U`.

## References

* [Stacks Project, Tag 054L](https://stacks.math.columbia.edu/tag/054L)
* [Stacks Project, Tag 01V0](https://stacks.math.columbia.edu/tag/01V0)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TensorProduct

universe u

namespace MMP.Flips.ResolutionInputs

section Algebra

open KaehlerDifferential

/-- Let `B` be a local ring, formally smooth over `R` with finite module of differentials, and let
`b : ι → B` be such that the `1 ⊗ d bᵢ` form a basis of `κ(B) ⊗ Ω[B⁄R]`. Then `B` is formally
étale over `R[Xᵢ]` via `Xᵢ ↦ bᵢ`. -/
theorem formallyEtale_mvPolynomial_of_isBasis_D {R B : Type u} [CommRing R] [CommRing B]
    [IsLocalRing B] [Algebra R B] [Algebra.FormallySmooth R B] [Module.Finite B Ω[B⁄R]]
    {ι : Type u} (b : ι → B)
    (hli : LinearIndependent (IsLocalRing.ResidueField B)
      (fun i ↦ (1 : IsLocalRing.ResidueField B) ⊗ₜ[B] D R B (b i)))
    (hsp : Submodule.span (IsLocalRing.ResidueField B)
      (Set.range (fun i ↦ (1 : IsLocalRing.ResidueField B) ⊗ₜ[B] D R B (b i))) = ⊤) :
    letI := (MvPolynomial.aeval (R := R) b).toRingHom.toAlgebra
    Algebra.FormallyEtale (MvPolynomial ι R) B := by
  classical
  let := (MvPolynomial.aeval (R := R) b).toRingHom.toAlgebra
  have hT : IsScalarTower R (MvPolynomial ι R) B :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      change _ = MvPolynomial.aeval b (MvPolynomial.C r)
      simp
  have hX : ∀ i, algebraMap (MvPolynomial ι R) B (MvPolynomial.X i) = b i := fun i ↦ by
    change MvPolynomial.aeval b (MvPolynomial.X i) = b i
    simp
  let e := Algebra.TensorProduct.basis B (mvPolynomialBasis R ι)
  have hproj : Module.Projective B Ω[B⁄R] := Algebra.FormallySmooth.projective_kaehlerDifferential
  have hbij : Function.Bijective (Finsupp.linearCombination B (fun i ↦ D R B (b i))) := by
    apply Module.IsLocalRing.linearCombination_bijective_of_flat
    refine ⟨hli, ?_⟩
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
    exact hsp
  have heq : mapBaseChange R (MvPolynomial ι R) B =
      (Finsupp.linearCombination B (fun i ↦ D R B (b i))) ∘ₗ e.repr.toLinearMap := by
    apply e.ext
    intro i
    simp [e, Algebra.TensorProduct.basis_apply, mvPolynomialBasis_apply, hX]
  have hF : Function.Bijective (mapBaseChange R (MvPolynomial ι R) B) := by
    rw [heq]
    exact hbij.comp e.repr.bijective
  refine (Algebra.formallyEtale_iff _ B).mpr ⟨?_, ?_⟩
  · refine subsingleton_of_forall_eq 0 fun x ↦ ?_
    obtain ⟨u, rfl⟩ := KaehlerDifferential.map_surjective R (MvPolynomial ι R) B x
    obtain ⟨w, rfl⟩ := hF.2 u
    exact (KaehlerDifferential.exact_mapBaseChange_map R (MvPolynomial ι R) B).apply_apply_eq_zero w
  · refine subsingleton_of_forall_eq 0 fun z ↦ ?_
    have : Subsingleton (Algebra.H1Cotangent R B) := Algebra.FormallySmooth.subsingleton_h1Cotangent
    obtain ⟨w, hw⟩ := (Algebra.H1Cotangent.exact_map_δ R (MvPolynomial ι R) B z).mp
      (hF.1 (by rw [(Algebra.H1Cotangent.exact_δ_mapBaseChange R (MvPolynomial ι R) B _).mpr
        ⟨z, rfl⟩, map_zero]))
    rw [← hw, Subsingleton.elim w 0, map_zero]

/-- Let `A` be smooth over `R`, `p` a prime of `A` with localization `B`, and `a : ι → A` such
that the `1 ⊗ d aᵢ` form a basis of `κ(p) ⊗ Ω[B⁄R]`. Then some `s ∉ p` makes `A_s` étale over
`R[Xᵢ]` via `Xᵢ ↦ aᵢ`. -/
theorem exists_etale_away_of_isBasis_D {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra.Smooth R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [IsLocalRing B] (p : Ideal A) [p.IsPrime] [IsLocalization.AtPrime B p] {ι : Type u}
    [Finite ι] (a : ι → A)
    (hli : LinearIndependent (IsLocalRing.ResidueField B)
      (fun i ↦ (1 : IsLocalRing.ResidueField B) ⊗ₜ[B] D R B (algebraMap A B (a i))))
    (hsp : Submodule.span (IsLocalRing.ResidueField B)
      (Set.range (fun i ↦ (1 : IsLocalRing.ResidueField B) ⊗ₜ[B] D R B (algebraMap A B (a i))))
        = ⊤) :
    letI := (MvPolynomial.aeval (R := R) a).toRingHom.toAlgebra
    ∃ s ∉ p, Algebra.Etale (MvPolynomial ι R) (Localization.Away s) := by
  classical
  have : Algebra.FormallySmooth A B := Algebra.FormallySmooth.of_isLocalization p.primeCompl
  have : Algebra.FormallySmooth R B := Algebra.FormallySmooth.comp R A B
  have : Module.Finite B Ω[B⁄R] :=
    Module.Finite.of_isLocalizedModule p.primeCompl (KaehlerDifferential.map R R A B)
  have hB := formallyEtale_mvPolynomial_of_isBasis_D (R := R) (fun i ↦ algebraMap A B (a i))
    hli hsp
  let := (MvPolynomial.aeval (R := R) a).toRingHom.toAlgebra
  let iB : Algebra (MvPolynomial ι R) B :=
    (MvPolynomial.aeval (R := R) (fun i ↦ algebraMap A B (a i))).toRingHom.toAlgebra
  have hcomp : ∀ q : MvPolynomial ι R, algebraMap (MvPolynomial ι R) B q =
      algebraMap A B (algebraMap (MvPolynomial ι R) A q) := by
    intro q
    change MvPolynomial.aeval _ q = algebraMap A B (MvPolynomial.aeval a q)
    rw [← IsScalarTower.toAlgHom_apply R A B, ← AlgHom.comp_apply]
    congr 1
    apply MvPolynomial.algHom_ext
    intro i
    simp
  let e0 : B ≃ₐ[A] Localization.AtPrime p := IsLocalization.algEquiv p.primeCompl B _
  let e : B ≃ₐ[MvPolynomial ι R] Localization.AtPrime p :=
    { e0.toRingEquiv with
      commutes' := fun q ↦ by
        change e0 (algebraMap (MvPolynomial ι R) B q) = _
        rw [hcomp, AlgEquiv.commutes]
        exact (IsScalarTower.algebraMap_apply _ A _ q).symm }
  have : Algebra.IsEtaleAt (MvPolynomial ι R) p := Algebra.FormallyEtale.of_equiv e
  have : IsScalarTower R (MvPolynomial ι R) A :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      change _ = MvPolynomial.aeval a (MvPolynomial.C r)
      simp
  have : Algebra.FinitePresentation (MvPolynomial ι R) A := by
    have := Fintype.ofFinite ι
    exact Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R _ A
  exact Algebra.exists_etale_of_isEtaleAt p

/-- For a localization `R₀` of `R` and an `R₀`-algebra `B`, the comparison map
`Ω[B⁄R] → Ω[B⁄R₀]` is bijective. -/
theorem bijective_kaehlerDifferential_map_of_isLocalization {R R₀ B : Type*} [CommRing R]
    [CommRing R₀] [CommRing B] [Algebra R R₀] (M : Submonoid R) [IsLocalization M R₀]
    [Algebra R₀ B] [Algebra R B] [IsScalarTower R R₀ B] :
    Function.Bijective (KaehlerDifferential.map R R₀ B B) := by
  have : Algebra.FormallyUnramified R R₀ := Algebra.FormallyUnramified.of_isLocalization M
  have : Subsingleton Ω[R₀⁄R] := (Algebra.formallyUnramified_iff R R₀).mp this
  refine ⟨?_, KaehlerDifferential.map_surjective R R₀ B⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, hy⟩ := (KaehlerDifferential.exact_mapBaseChange_map R R₀ B x).mp hx
  rw [← hy, Subsingleton.elim y 0, map_zero]

/-- For a localization `R₀` of `R` and a local `R₀`-algebra `B`, a family whose differentials
form a basis of `κ(B) ⊗ Ω[B⁄R₀]` also has differentials forming a basis of `κ(B) ⊗ Ω[B⁄R]`. -/
theorem isBasis_D_of_isLocalization_base {R R₀ B : Type u} [CommRing R] [CommRing R₀]
    [CommRing B] [IsLocalRing B] [Algebra R R₀] (M : Submonoid R) [IsLocalization M R₀]
    [Algebra R₀ B] [Algebra R B] [IsScalarTower R R₀ B] {ι : Type*} (b : ι → B)
    (hli : LinearIndependent (IsLocalRing.ResidueField B)
      (fun i ↦ (1 : IsLocalRing.ResidueField B) ⊗ₜ[B] D R₀ B (b i)))
    (hsp : Submodule.span (IsLocalRing.ResidueField B)
      (Set.range (fun i ↦ (1 : IsLocalRing.ResidueField B) ⊗ₜ[B] D R₀ B (b i))) = ⊤) :
    LinearIndependent (IsLocalRing.ResidueField B)
      (fun i ↦ (1 : IsLocalRing.ResidueField B) ⊗ₜ[B] D R B (b i)) ∧
    Submodule.span (IsLocalRing.ResidueField B)
      (Set.range (fun i ↦ (1 : IsLocalRing.ResidueField B) ⊗ₜ[B] D R B (b i))) = ⊤ := by
  let e : Ω[B⁄R] ≃ₗ[B] Ω[B⁄R₀] := LinearEquiv.ofBijective (KaehlerDifferential.map R R₀ B B)
    (bijective_kaehlerDifferential_map_of_isLocalization M)
  let e' := e.baseChange B (IsLocalRing.ResidueField B)
  have hcomp : (fun i ↦ (1 : IsLocalRing.ResidueField B) ⊗ₜ[B] D R₀ B (b i)) =
      e' ∘ (fun i ↦ (1 : IsLocalRing.ResidueField B) ⊗ₜ[B] D R B (b i)) := by
    funext i
    change _ = (1 : IsLocalRing.ResidueField B) ⊗ₜ[B]
      KaehlerDifferential.map R R₀ B B (D R B (b i))
    rw [KaehlerDifferential.map_D, Algebra.algebraMap_self, RingHom.id_apply]
  rw [hcomp] at hli hsp
  refine ⟨hli.of_comp e'.toLinearMap, ?_⟩
  have := congrArg (Submodule.map e'.symm.toLinearMap) hsp
  rw [Submodule.map_span, Set.range_comp, Set.image_image] at this
  simpa using this

end Algebra

/-- Let `h : X ⟶ S` with `S` affine and `U ⊆ X` an affine open. If a ring map
`φ : Γ(S, ⊤)[Xᵢ] → Γ(X, U)` restricting to `h` on constants and sending `Xᵢ ↦ wᵢ` is étale,
then the morphism `(w₁, …, wₙ) : U ⟶ 𝔸_S` is étale. -/
theorem etale_homOfVector_of_etale {X S : Scheme.{u}} [IsAffine S] (h : X ⟶ S) (U : X.Opens)
    (hU : IsAffineOpen U) {ι : Type u} (w : ι → Γ(X, U))
    (φ : MvPolynomial ι Γ(S, ⊤) →+* Γ(X, U))
    (hC : φ.comp MvPolynomial.C = (h.appLE ⊤ U le_top).hom) (hX : ∀ i, φ (.X i) = w i)
    (hφ : φ.Etale) :
    Etale (AffineSpace.homOfVector (U.ι ≫ h) (fun i ↦ U.topIso.inv (w i))) := by
  have : IsAffine U.toScheme := hU
  set π := AffineSpace.homOfVector (U.ι ≫ h) (fun i ↦ U.topIso.inv (w i))
  suffices H : Etale (π ≫ (AffineSpace.isoOfIsAffine ι S).hom) by
    have : Etale ((π ≫ (AffineSpace.isoOfIsAffine ι S).hom) ≫
      (AffineSpace.isoOfIsAffine ι S).inv) := inferInstance
    simpa using this
  rw [HasRingHomProperty.iff_of_isAffine (P := @Etale), Scheme.Hom.comp_appTop,
    AffineSpace.isoOfIsAffine_hom_appTop]
  have heq : (π.appTop.hom).comp (MvPolynomial.eval₂Hom ((AffineSpace ι S ↘ S).appTop).hom
      (AffineSpace.coord S)) = U.topIso.inv.hom.comp φ := by
    apply MvPolynomial.ringHom_ext
    · intro r
      have h1 := congrArg (fun g ↦ g.appTop.hom r) (AffineSpace.homOfVector_over (U.ι ≫ h)
        (fun i ↦ U.topIso.inv (w i)))
      simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at h1
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, ← RingHom.comp_apply φ, hC]
      have key : (U.ι ≫ h).appTop = h.appLE ⊤ U le_top ≫ U.topIso.inv := by
        rw [Iso.eq_comp_inv, Scheme.Hom.comp_appTop, Scheme.Opens.ι_appTop,
          Scheme.Opens.topIso_hom]
        simp only [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
        erw [Scheme.Hom.appLE_map, Scheme.Hom.appLE_map]
      rw [h1, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, key]
      rfl
    · intro i
      simp [π, hX]
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom]
  rw [← RingHom.comp_assoc, heq]
  refine RingHom.Etale.stableUnderComposition _ _
    (RingHom.Etale.of_bijective (ConcreteCategory.bijective_of_isIso _)) ?_
  exact RingHom.Etale.stableUnderComposition _ _ hφ
    (RingHom.Etale.of_bijective (ConcreteCategory.bijective_of_isIso _))

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- For `f : X ⟶ Spec k` smooth, the stalk at `x` of `Ω_{X/k}`, written as
`Ω[𝒪_{X,x} ⁄ 𝒪_{Spec k, f x}]`, is a finite free `𝒪_{X,x}`-module. -/
theorem free_finite_kaehlerDifferential_stalk (f : X ⟶ Spec (.of k)) [Smooth f] (x : X) :
    letI := (f.stalkMap x).hom.toAlgebra
    Module.Free (X.presheaf.stalk x)
        Ω[X.presheaf.stalk x ⁄ (Spec (.of k)).presheaf.stalk (f x)] ∧
      Module.Finite (X.presheaf.stalk x)
        Ω[X.presheaf.stalk x ⁄ (Spec (.of k)).presheaf.stalk (f x)] := by
  obtain ⟨W, hW, hxW, -⟩ := exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)
  let R := Γ(Spec (.of k), ⊤)
  let A := Γ(X, W)
  have hWf : W ≤ f ⁻¹ᵁ ⊤ := le_top
  let algRA : Algebra R A := (f.appLE ⊤ W hWf).hom.toAlgebra
  have hsm : Algebra.Smooth R A :=
    HasRingHomProperty.appLE (P := @Smooth) f ‹_› ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ hWf
  let B := X.presheaf.stalk x
  let algAB : Algebra A B := (X.presheaf.germ W x hxW).hom.toAlgebra
  let R₀ := (Spec (.of k)).presheaf.stalk (f x)
  let algR₀B : Algebra R₀ B := (f.stalkMap x).hom.toAlgebra
  let algRR₀ : Algebra R R₀ := ((Spec (.of k)).presheaf.germ ⊤ (f x) trivial).hom.toAlgebra
  let algRB : Algebra R B := ((algebraMap R₀ B).comp (algebraMap R R₀)).toAlgebra
  have : IsScalarTower R R₀ B := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hcompat : f.appLE ⊤ W hWf ≫ X.presheaf.germ W x hxW =
      (Spec (.of k)).presheaf.germ ⊤ (f x) trivial ≫ f.stalkMap x := by
    rw [Scheme.Hom.appLE, Category.assoc, X.presheaf.germ_res (homOfLE hWf) x hxW]
    exact (Scheme.Hom.germ_stalkMap f ⊤ x trivial).symm
  have : IsScalarTower R A B := by
    refine IsScalarTower.of_algebraMap_eq fun a ↦ ?_
    change (f.stalkMap x).hom (((Spec (.of k)).presheaf.germ ⊤ (f x) trivial).hom a) = _
    exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hcompat.symm) a
  have : IsLocalization.AtPrime R₀ ((isAffineOpen_top _).primeIdealOf ⟨f x, trivial⟩).asIdeal :=
    (isAffineOpen_top _).isLocalization_stalk ⟨f x, trivial⟩
  let p := (hW.primeIdealOf ⟨x, hxW⟩).asIdeal
  have : IsLocalization.AtPrime B p := hW.isLocalization_stalk ⟨x, hxW⟩
  have : Algebra.FormallySmooth A B := Algebra.FormallySmooth.of_isLocalization p.primeCompl
  have : Algebra.FormallySmooth R B := Algebra.FormallySmooth.comp R A B
  have : Module.Finite B Ω[B⁄R] :=
    Module.Finite.of_isLocalizedModule p.primeCompl (KaehlerDifferential.map R R A B)
  have : Module.Projective B Ω[B⁄R] := Algebra.FormallySmooth.projective_kaehlerDifferential
  have : Module.Free B Ω[B⁄R] := Module.free_of_flat_of_isLocalRing
  let e : Ω[B⁄R] ≃ₗ[B] Ω[B⁄R₀] := LinearEquiv.ofBijective (KaehlerDifferential.map R R₀ B B)
    (bijective_kaehlerDifferential_map_of_isLocalization
      ((isAffineOpen_top _).primeIdealOf ⟨f x, trivial⟩).asIdeal.primeCompl)
  exact ⟨Module.Free.of_equiv e, Module.Finite.equiv e⟩

/-- **Étale coordinates from a basis of differentials.** Let `f : X ⟶ Spec k` be smooth over a
field `k`, `x ∈ X`, and let `g_1, …, g_n` be sections of `𝒪_X` over an open `V ∋ x` whose
differentials `d g_i ⊗ 1` form a basis of `κ(x) ⊗ Ω_{X/k,x}`. Then there is an affine open
`U ∋ x` inside `V` on which the morphism `(g_1|_U, …, g_n|_U) : U ⟶ 𝔸^n_k` over `k` is étale. -/
@[mmp "lem_mmp_foundation_arbitrary_field_etale_coordinate_chart"]
theorem exists_isAffineOpen_etale_homOfVector (f : X ⟶ Spec (.of k)) [Smooth f] (x : X)
    {n : ℕ} (V : X.Opens) (hxV : x ∈ V) (g : Fin n → Γ(X, V))
    (hg : letI := (f.stalkMap x).hom.toAlgebra
      let v : Fin n → IsLocalRing.ResidueField (X.presheaf.stalk x) ⊗[X.presheaf.stalk x]
          Ω[X.presheaf.stalk x ⁄ (Spec (.of k)).presheaf.stalk (f x)] := fun i ↦
        1 ⊗ₜ KaehlerDifferential.D _ _ (X.presheaf.germ V x hxV (g i))
      LinearIndependent (IsLocalRing.ResidueField (X.presheaf.stalk x)) v ∧
        Submodule.span (IsLocalRing.ResidueField (X.presheaf.stalk x)) (Set.range v) = ⊤) :
    ∃ (U : X.Opens) (_ : IsAffineOpen U) (_ : x ∈ U) (hUV : U ≤ V),
      Etale (AffineSpace.homOfVector (U.ι ≫ f)
        (fun i : ULift.{u} (Fin n) ↦
          U.topIso.inv (X.presheaf.map (homOfLE hUV).op (g i.down)))) := by
  classical
  obtain ⟨W, hW, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset hxV
  have hWV' : W ≤ V := hWV
  let R := Γ(Spec (.of k), ⊤)
  let A := Γ(X, W)
  have hWf : W ≤ f ⁻¹ᵁ ⊤ := le_top
  let algRA : Algebra R A := (f.appLE ⊤ W hWf).hom.toAlgebra
  have hsm : Algebra.Smooth R A :=
    HasRingHomProperty.appLE (P := @Smooth) f ‹_› ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ hWf
  let B := X.presheaf.stalk x
  let algAB : Algebra A B := (X.presheaf.germ W x hxW).hom.toAlgebra
  let R₀ := (Spec (.of k)).presheaf.stalk (f x)
  let algR₀B : Algebra R₀ B := (f.stalkMap x).hom.toAlgebra
  let algRR₀ : Algebra R R₀ := ((Spec (.of k)).presheaf.germ ⊤ (f x) trivial).hom.toAlgebra
  let algRB : Algebra R B := ((algebraMap R₀ B).comp (algebraMap R R₀)).toAlgebra
  have : IsScalarTower R R₀ B := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hcompat : f.appLE ⊤ W hWf ≫ X.presheaf.germ W x hxW =
      (Spec (.of k)).presheaf.germ ⊤ (f x) trivial ≫ f.stalkMap x := by
    rw [Scheme.Hom.appLE, Category.assoc, X.presheaf.germ_res (homOfLE hWf) x hxW]
    exact (Scheme.Hom.germ_stalkMap f ⊤ x trivial).symm
  have : IsScalarTower R A B := by
    refine IsScalarTower.of_algebraMap_eq fun a ↦ ?_
    change (f.stalkMap x).hom (((Spec (.of k)).presheaf.germ ⊤ (f x) trivial).hom a) = _
    exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hcompat.symm) a
  have : IsLocalization.AtPrime R₀ ((isAffineOpen_top _).primeIdealOf ⟨f x, trivial⟩).asIdeal :=
    (isAffineOpen_top _).isLocalization_stalk ⟨f x, trivial⟩
  let p := (hW.primeIdealOf ⟨x, hxW⟩).asIdeal
  have : IsLocalization.AtPrime B p := hW.isLocalization_stalk ⟨x, hxW⟩
  let a : ULift.{u} (Fin n) → A := fun i ↦ X.presheaf.map (homOfLE hWV').op (g i.down)
  have ha : ∀ i, algebraMap A B (a i) = X.presheaf.germ V x hxV (g i.down) := fun i ↦
    X.presheaf.germ_res_apply (homOfLE hWV') x hxW (g i.down)
  obtain ⟨hli0, hsp0⟩ := hg
  have hfun : (fun i : ULift.{u} (Fin n) ↦ (1 : IsLocalRing.ResidueField B) ⊗ₜ[B]
      KaehlerDifferential.D R₀ B (algebraMap A B (a i))) =
      (fun i : Fin n ↦ (1 : IsLocalRing.ResidueField B) ⊗ₜ[B]
        KaehlerDifferential.D R₀ B (X.presheaf.germ V x hxV (g i))) ∘ Equiv.ulift := by
    funext i
    simp only [Function.comp_apply, ha]
    rfl
  have hli1 : LinearIndependent (IsLocalRing.ResidueField B)
      (fun i : ULift.{u} (Fin n) ↦ (1 : IsLocalRing.ResidueField B) ⊗ₜ[B]
        KaehlerDifferential.D R₀ B (algebraMap A B (a i))) := by
    rw [hfun]
    exact hli0.comp _ Equiv.ulift.injective
  have hsp1 : Submodule.span (IsLocalRing.ResidueField B) (Set.range
      (fun i : ULift.{u} (Fin n) ↦ (1 : IsLocalRing.ResidueField B) ⊗ₜ[B]
        KaehlerDifferential.D R₀ B (algebraMap A B (a i)))) = ⊤ := by
    rw [hfun, Equiv.ulift.surjective.range_comp]
    exact hsp0
  obtain ⟨hli2, hsp2⟩ := isBasis_D_of_isLocalization_base (R := R) (R₀ := R₀) (B := B)
    ((isAffineOpen_top _).primeIdealOf ⟨f x, trivial⟩).asIdeal.primeCompl
    (fun i ↦ algebraMap A B (a i)) hli1 hsp1
  obtain ⟨s, hs, hEt⟩ := exists_etale_away_of_isBasis_D (R := R) p a hli2 hsp2
  have hU : IsAffineOpen (X.basicOpen s) := hW.basicOpen s
  have hxU : x ∈ X.basicOpen s := by
    rw [Scheme.mem_basicOpen X s x hxW]
    exact IsLocalization.map_units B (⟨s, hs⟩ : p.primeCompl)
  have hUW : X.basicOpen s ≤ W := X.basicOpen_le s
  have hUV : X.basicOpen s ≤ V := hUW.trans hWV'
  refine ⟨X.basicOpen s, hU, hxU, hUV, ?_⟩
  have : IsLocalization.Away s Γ(X, X.basicOpen s) := hW.isLocalization_basicOpen s
  let := (MvPolynomial.aeval (R := R) a).toRingHom.toAlgebra
  let eL : Localization.Away s ≃ₐ[A] Γ(X, X.basicOpen s) :=
    IsLocalization.algEquiv (Submonoid.powers s) _ _
  let φ : MvPolynomial (ULift.{u} (Fin n)) R →+* Γ(X, X.basicOpen s) :=
    eL.toRingEquiv.toRingHom.comp (algebraMap _ (Localization.Away s))
  have hφ : φ.Etale := RingHom.Etale.stableUnderComposition _ _
    (RingHom.etale_algebraMap.mpr hEt) (RingHom.Etale.of_bijective eL.bijective)
  have hφa : ∀ q, φ q = algebraMap A Γ(X, X.basicOpen s) (algebraMap _ A q) := fun q ↦ by
    change eL (algebraMap _ (Localization.Away s) q) = _
    rw [IsScalarTower.algebraMap_apply _ A (Localization.Away s), AlgEquiv.commutes]
  have hC : φ.comp MvPolynomial.C = (f.appLE ⊤ (X.basicOpen s) le_top).hom := by
    refine RingHom.ext fun r ↦ ?_
    rw [RingHom.comp_apply, hφa]
    change (X.presheaf.map (homOfLE hUW).op).hom (MvPolynomial.aeval a (MvPolynomial.C r)) = _
    rw [MvPolynomial.aeval_C]
    change (f.appLE ⊤ W hWf ≫ X.presheaf.map (homOfLE hUW).op).hom r = _
    rw [Scheme.Hom.appLE_map]
  have hX : ∀ i, φ (.X i) = X.presheaf.map (homOfLE hUV).op (g i.down) := by
    intro i
    rw [hφa]
    change (X.presheaf.map (homOfLE hUW).op).hom (MvPolynomial.aeval a (MvPolynomial.X i)) = _
    rw [MvPolynomial.aeval_X]
    change (X.presheaf.map (homOfLE hUW).op).hom
      ((X.presheaf.map (homOfLE hWV').op).hom (g i.down)) = _
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
  have key := etale_homOfVector_of_etale (S := Spec (.of k)) f (X.basicOpen s) hU
    (fun i ↦ X.presheaf.map (homOfLE hUV).op (g i.down)) φ hC hX hφ
  exact key

/-- **Étale coordinate charts.** Let `f : X ⟶ Spec k` be smooth over a field `k`, `x ∈ X`, and
`n = rank_x Ω_{X/k}`. Then there is an affine open `U ∋ x` with an étale morphism `U ⟶ 𝔸^n_k`
over `k`. -/
@[mmp "lem_mmp_foundation_arbitrary_field_etale_coordinate_chart"]
theorem exists_isAffineOpen_etale_affineSpace (f : X ⟶ Spec (.of k)) [Smooth f] (x : X) :
    letI := (f.stalkMap x).hom.toAlgebra
    ∃ (U : X.Opens) (_ : IsAffineOpen U) (_ : x ∈ U)
      (π : U.toScheme ⟶ 𝔸(ULift.{u} (Fin (Module.finrank (X.presheaf.stalk x)
        Ω[X.presheaf.stalk x ⁄ (Spec (.of k)).presheaf.stalk (f x)])); Spec (.of k))),
      Etale π ∧ π ≫ 𝔸(_; Spec (.of k)) ↘ Spec (.of k) = U.ι ≫ f := by
  classical
  let := (f.stalkMap x).hom.toAlgebra
  obtain ⟨hfree, hfin⟩ := free_finite_kaehlerDifferential_stalk f x
  let B := X.presheaf.stalk x
  let R₀ := (Spec (.of k)).presheaf.stalk (f x)
  let K := IsLocalRing.ResidueField B
  let N := Module.finrank B Ω[B⁄R₀]
  let S : Set (K ⊗[B] Ω[B⁄R₀]) := Set.range (fun b : B ↦ (1 : K) ⊗ₜ[B] KaehlerDifferential.D R₀ B b)
  have hS : Submodule.span K S = ⊤ := by
    have := Submodule.baseChange_span (R := B) (A := K) (Set.range (KaehlerDifferential.D R₀ B))
    rw [KaehlerDifferential.span_range_derivation, Submodule.baseChange_top,
      ← Set.range_comp] at this
    exact this.symm
  obtain ⟨T, hTS, hTspan, hTli⟩ := exists_linearIndependent K S
  let bT : Module.Basis T K (K ⊗[B] Ω[B⁄R₀]) :=
    Module.Basis.mk hTli (by rw [Subtype.range_coe, hTspan, hS])
  have : Finite T := Module.Finite.finite_basis bT
  have : Fintype T := Fintype.ofFinite T
  have hcard : Fintype.card T = N := by
    rw [← Module.finrank_eq_card_basis bT, Module.finrank_baseChange]
  let e : Fin N ≃ T := (Fintype.equivFinOfCardEq hcard).symm
  have hmem : ∀ i, ∃ c : B, (1 : K) ⊗ₜ[B] KaehlerDifferential.D R₀ B c = (e i : _) :=
    fun i ↦ hTS (e i).2
  choose c hc using hmem
  choose U hxU t ht using fun i ↦ X.presheaf.exists_germ_eq (c i)
  let V : X.Opens := ⨅ i, U i
  have hxV : x ∈ V := by
    change x ∈ ((⨅ i, U i : X.Opens) : Set X)
    rw [TopologicalSpace.Opens.coe_iInf]
    exact Set.mem_iInter.mpr hxU
  let g : Fin N → Γ(X, V) := fun i ↦ X.presheaf.map (homOfLE (iInf_le U i)).op (t i)
  have hgerm : ∀ i, X.presheaf.germ V x hxV (g i) = c i := fun i ↦ by
    rw [X.presheaf.germ_res_apply]
    exact ht i
  have hv : (fun i ↦ (1 : K) ⊗ₜ[B] KaehlerDifferential.D R₀ B (X.presheaf.germ V x hxV (g i))) =
      (fun t : T ↦ (t : K ⊗[B] Ω[B⁄R₀])) ∘ e := by
    funext i
    simp only [hgerm, hc, Function.comp_apply]
  have hg : LinearIndependent K
        (fun i ↦ (1 : K) ⊗ₜ[B] KaehlerDifferential.D R₀ B (X.presheaf.germ V x hxV (g i))) ∧
      Submodule.span K (Set.range
        (fun i ↦ (1 : K) ⊗ₜ[B] KaehlerDifferential.D R₀ B (X.presheaf.germ V x hxV (g i)))) =
          ⊤ := by
    rw [hv, e.surjective.range_comp, Subtype.range_coe, hTspan, hS]
    exact ⟨hTli.comp e e.injective, rfl⟩
  obtain ⟨W, hW, hxW, hWV, hEt⟩ := exists_isAffineOpen_etale_homOfVector f x V hxV g hg
  exact ⟨W, hW, hxW, _, hEt, AffineSpace.homOfVector_over _ _⟩

end MMP.Flips.ResolutionInputs

end
