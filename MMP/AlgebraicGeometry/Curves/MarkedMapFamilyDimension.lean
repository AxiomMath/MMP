module
public import MMP.AlgebraicGeometry.MMP.Models
public import MMP.AlgebraicGeometry.Curves.Maps.Injectivity
public import MMP.AlgebraicGeometry.Curves.Maps.Sections
public import MMP.AlgebraicGeometry.Curves.Maps.Derivations

/-!
# A finite-type space of pointed maps from a curve, with a dimension bound

Let `C` be a smooth projective curve of genus `g` over an algebraically closed field `k`, let
`U` be a smooth quasi-projective `k`-variety of dimension `n`, let `f : C ⟶ U` be a morphism and
let `P₁, …, P_b` be distinct `k`-points of `C`, with `B = P₁ + ⋯ + P_b`. There is a scheme `M` of
finite type over `k`, a `k`-point `[f]` of `M` and a family `F : C ×_k M ⟶ U` of maps, restricting
to `f` over `[f]` and to the constant value `f(Pᵢ)` along each `Pᵢ × M`, whose geometric points
define pairwise distinct maps, and such that
`dim 𝒪_{M,[f]} ≥ χ(C, f^* T_U(-B)) - 2g = χ(C, f^* T_U) - n b - 2g`.

## Main results

* `MMP.Fourfold.exists_fixedMarked_mapFamily_le_ringKrullDim`: the existence of such a family.

## Implementation notes

The tangent sheaf `T_U` is the dual `(Ω_{U/k})^∨` of the sheaf of relative differentials. The
twist by `-B` enters only through its Euler characteristic: as `f^* T_U` is locally free of rank
`n` and `B` is a reduced divisor of degree `b`, the sequence
`0 → f^* T_U(-B) → f^* T_U → f^* T_U|_B → 0` gives `χ(f^* T_U(-B)) = χ(f^* T_U) - n b`, which is
the form stated. The genus is the arithmetic genus `MMP.Mori.arithmeticGenus`, which for a smooth
projective connected curve over an algebraically closed field is `h¹(C, 𝒪_C)`. The local
dimension of `M` at the closed point `[f]` is the Krull dimension of the stalk there; as the
stalk is a nonzero ring this is `≥ 0`, so the bound is stated for the positive part of the
right-hand side.

## References

* [Kollár–Mori, *Birational geometry of algebraic varieties*, Theorem 1.10 and its proof]
-/

section

universe u

open CategoryTheory Limits AlgebraicGeometry Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.ProjectiveFromSections Stacks.NonvanishingOpen
open Stacks.Ample (IsInvertibleModule nonvanishingLocus)
open MMP.Fourfold MMP.Fourfold.CurveChartDeformations MMP.Fourfold.CurveMapTangent
open MMP.Fourfold.CurveMapSections
open Stacks.GradedSections (powSections sectionRing)
open Stacks.Algebraization (degreeOneSection)
open Stacks.AmpleProjectiveImmersion Stacks.TwistPullbackPinned
open Stacks.AlgebraicGeometry.ProjPolyChart Stacks.RingTheory.HomogeneousQuotient
open Stacks.AlgebraicGeometry.SectionsBaseChange
open Stacks.ClosedSubschemeProjQuotient Stacks.ClosedSubschemeProjectiveSpace
open IsLocalRing MMP
open Stacks.LinearSystemScheme
open AlgebraicGeometry.SectionsEqualizer (pullbackGlobalSections_smul)
open Stacks.LinearSystemScheme (coordSection coordSection_bijective)
open scoped TensorProduct

namespace MMP.Fourfold.Internal.FixedLineCurveMapDimension

noncomputable section

section CurveMapSpace

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow

variable {k : Type u} [Field k] {n : ℕ}

section FamilyIdentification

variable {C : Scheme.{u}} (sC : C ⟶ Spec (.of k)) (L : C.Modules)
    [IsInvertibleModule C L] {N : ℕ} (e : Fin N → Γ(L, ⊤))

/-- **A morphism to `ℙⁿ_k` with a pinned isomorphism is the morphism of the generating tuple**
(Stacks Tag 01NE, uniqueness, in the form of `toProjectiveSpaceOver`). -/
private theorem eq_toProjectiveSpaceOver_of_pinned {Y : Scheme.{u}} {M₁ : Y.Modules}
    [IsInvertibleModule Y M₁] (s : Fin (n + 1) → Γ(M₁, ⊤)) (hs : GeneratesStalks s)
    (π : Y ⟶ Spec (.of k)) (p : Y ⟶ projectiveSpaceOver n (Spec (.of k)))
    (hp : p ≫ pullback.fst (terminal.from (Spec (.of k)))
      (terminal.from (projectiveSpaceAtUniverse.{u} n)) = π)
    (α : (Scheme.Modules.pullback (p ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of
        k)))).obj
      (twistingSheafAtUniverse.{u} n) ⟶ M₁) [IsIso α]
    (hα : ∀ i, α.app ⊤ (pullbackCoordSection.{u}
      (p ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) i) = s i) :
    p = toProjectiveSpaceOver s hs π := by
  refine pullback.hom_ext (hp.trans (toProjectiveSpaceOver_fst s hs π).symm) ?_
  change p ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)) =
    toProjectiveSpaceOver s hs π ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))
  rw [toProjectiveSpaceOver_snd]
  exact eq_toProjectiveSpaceAtUniverse_of_pinned s _ α hα hs

variable [IsProper sC] {T' : Scheme.{u}}

/-- **The family on `M₁`, restricted along any `T'`-point `h` of `M₁`, is the morphism of the
generating tuple `familySection (h ≫ ι)`.** -/
private theorem familyBaseChange_noCommonZeroFamily_eq (h : T' ⟶ noCommonZeroScheme (n := n) sC L
    e) :
    familyBaseChange (sC := sC) (noCommonZeroScheme.ι (n := n) sC L e) h ≫
        noCommonZeroFamily (n := n) sC L e =
      toProjectiveSpaceOver
        (familySection (n := n) (N := N) (L := L) (e := e) (sC := sC)
          (h ≫ noCommonZeroScheme.ι (n := n) sC L e))
        (generatesStalks_familySection _ (fun t => base_noCommonZeroScheme_ι_mem sC L e (h.base t)))
        (pullback.fst sC ((h ≫ noCommonZeroScheme.ι (n := n) sC L e) ≫ coefficientSpaceOver n N k)
            ≫ sC) := by
  obtain ⟨αM, hiso, hαM⟩ := exists_iso_noCommonZeroFamily (n := n) sC L e
  have := hiso
  obtain ⟨γ, hγ⟩ := exists_iso_pullbackGlobalSections_comp
    (familyBaseChange (sC := sC) (noCommonZeroScheme.ι (n := n) sC L e) h)
    (familyPullbackMap (n := n) (N := N) (sC := sC) (noCommonZeroScheme.ι (n := n) sC L e))
    (familyPullbackMap (n := n) (N := N) (sC := sC) (h ≫ noCommonZeroScheme.ι (n := n) sC L e))
    (familyPullbackMap_comp _ h)
    ((Scheme.Modules.pullback (pullback.fst sC (coefficientSpaceOver n N k))).obj L)
  let α₁ := ((((Scheme.Modules.pullbackComp
      (familyBaseChange (sC := sC) (noCommonZeroScheme.ι (n := n) sC L e) h)
      (noCommonZeroFamily (n := n) sC L e ≫
        projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))).app
        (twistingSheafAtUniverse.{u} n)).symm ≪≫
      (Scheme.Modules.pullback
        (familyBaseChange (sC := sC) (noCommonZeroScheme.ι (n := n) sC L e) h)).mapIso
          (asIso αM)) ≪≫ γ)
  haveI : IsInvertibleModule
      (pullback sC (h ≫ noCommonZeroScheme.ι (n := n) sC L e ≫ coefficientSpaceOver n N k))
      (familyModule (n := n) (N := N) (L := L) (sC := sC)
        (h ≫ noCommonZeroScheme.ι (n := n) sC L e)) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback _ _
  refine @eq_toProjectiveSpaceOver_of_pinned k _ n _ _ this _ _ _ _ ?_ α₁.hom (Iso.isIso_hom α₁) ?_
  · exact (Category.assoc _ _ _).trans ((congrArg
      ((familyBaseChange (sC := sC) (noCommonZeroScheme.ι (n := n) sC L e) h) ≫ ·)
      (noCommonZeroFamily_over (n := n) sC L e)).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ sC)
        (familyBaseChange_fst (sC := sC) (noCommonZeroScheme.ι (n := n) sC L e) h))))
  · intro i
    have h1 := pullbackComp_inv_map_pullbackGlobalSections
      (familyBaseChange (sC := sC) (noCommonZeroScheme.ι (n := n) sC L e) h)
      (noCommonZeroFamily (n := n) sC L e ≫
        projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) αM
      (coordGlobalSection.{u} n i)
    have h2 := hγ (universalSection (n := n) sC L e i)
    change γ.hom.app ⊤ (((Scheme.Modules.pullbackComp
      (familyBaseChange (sC := sC) (noCommonZeroScheme.ι (n := n) sC L e) h)
      (noCommonZeroFamily (n := n) sC L e ≫
        projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))).inv.app
        (twistingSheafAtUniverse.{u} n) ≫
      (Scheme.Modules.pullback
        (familyBaseChange (sC := sC) (noCommonZeroScheme.ι (n := n) sC L e) h)).map αM).app ⊤
      (AlgebraicGeometry.pullbackGlobalSections
        ((familyBaseChange (sC := sC) (noCommonZeroScheme.ι (n := n) sC L e) h) ≫
          (noCommonZeroFamily (n := n) sC L e ≫
            projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))) _
        (coordGlobalSection.{u} n i))) = _
    rw [h1]
    exact (congrArg (fun z => γ.hom.app ⊤
      (AlgebraicGeometry.pullbackGlobalSections
        (familyBaseChange (sC := sC) (noCommonZeroScheme.ι (n := n) sC L e) h) _ z))
      (hαM i)).trans h2

/-- `familyMapOfHom` over `M₁` and `familyBaseChange` agree (general base). -/
private theorem familyMapOfHom_eq_familyBaseChange_general (h : T' ⟶ noCommonZeroScheme (n := n) sC
    L e) :
    familyMapOfHom sC h (sT := noCommonZeroScheme.over (n := n) sC L e)
        (sT' := h ≫ noCommonZeroScheme.over (n := n) sC L e) rfl =
      familyBaseChange (sC := sC) (noCommonZeroScheme.ι (n := n) sC L e) h := by
  refine pullback.hom_ext ?_ ?_
  · simp
  · simp

/-- **The family on `M₁` restricted along `h`, in the form of the morphism of the generating tuple
of the `T'`-point `g = h ≫ ι`**, with the structure morphism spelled as `g ≫ coefficientSpaceOver`.
-/
private theorem familyMapOfHom_noCommonZeroFamily_eq (g : T' ⟶ coefficientSpace n N k)
    (h : T' ⟶ noCommonZeroScheme (n := n) sC L e)
    (hgh : h ≫ noCommonZeroScheme.ι (n := n) sC L e = g)
    (hg0 : ∀ t : T', g.base t ∈ noCommonZeroOpen (n := n) sC L e)
    (hh : h ≫ noCommonZeroScheme.over (n := n) sC L e = g ≫ coefficientSpaceOver n N k) :
    familyMapOfHom sC h hh ≫ noCommonZeroFamily (n := n) sC L e =
      toProjectiveSpaceOver (familySection (n := n) (N := N) (L := L) (e := e) (sC := sC) g)
        (generatesStalks_familySection g hg0)
        (pullback.fst sC (g ≫ coefficientSpaceOver n N k) ≫ sC) := by
  subst hgh
  have := familyBaseChange_noCommonZeroFamily_eq (n := n) (N := N) sC L e h
  rw [← familyMapOfHom_eq_familyBaseChange_general] at this
  exact this

end FamilyIdentification

section FinalRestrict

variable {k : Type u} [Field k] {C : Scheme.{u}} (sC : C ⟶ Spec (.of k)) (L : C.Modules)
    [IsInvertibleModule C L] {n N : ℕ} (e : Fin N → Γ(L, ⊤)) [IsProper sC] {κ : Type*} (q : κ →
    Γ(coefficientSpace n N k, ⊤)) (Zc : Set (projectiveSpaceOver n (Spec (.of k)))) (hZc : IsClosed
    Zc) {T : Scheme.{u}}

/-- The family `Φ` on `M`, restricted along a `T`-point `u` of `M`, is the family on `M₁`
restricted along the corresponding `T`-point of `M₁`. -/
private theorem finalFamily_restrict (u : T ⟶ finalSpace (n := n) sC L e q Zc hZc) :
    familyMapOfHom sC u
        (sT := finalSpace.over (n := n) sC L e q Zc hZc)
        (sT' := u ≫ finalSpace.over (n := n) sC L e q Zc hZc) rfl ≫
      finalFamily (n := n) sC L e q Zc hZc =
    familyMapOfHom sC
        (u ≫ finalSpace.ι (n := n) sC L e q Zc hZc ≫
          closedNoCommonZeroScheme.toNoCommonZero (n := n) sC L e q)
        (sT := noCommonZeroScheme.over (n := n) sC L e)
        (sT' := u ≫ finalSpace.over (n := n) sC L e q Zc hZc)
        (by
          rw [Category.assoc, Category.assoc, closedNoCommonZeroScheme.toNoCommonZero_over]) ≫
      noCommonZeroFamily (n := n) sC L e := by
  have h1 := familyMapOfHom_comp (sC := sC)
    (closedNoCommonZeroScheme.toNoCommonZero (n := n) sC L e q)
    (closedNoCommonZeroScheme.toNoCommonZero_over sC L e q)
    (u ≫ finalSpace.ι (n := n) sC L e q Zc hZc) rfl
  have h2 := familyMapOfHom_comp (sC := sC) (finalSpace.ι (n := n) sC L e q Zc hZc)
    (sT := closedNoCommonZeroScheme.over (n := n) sC L e q)
    (sT' := finalSpace.over (n := n) sC L e q Zc hZc) rfl u
    (sT'' := u ≫ finalSpace.over (n := n) sC L e q Zc hZc) rfl
  unfold finalFamily closedNoCommonZeroFamily
  refine ((Category.assoc _ _ _).symm.trans ?_)
  refine (congrArg (· ≫ _) h2.symm).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  exact congrArg (· ≫ noCommonZeroFamily (n := n) sC L e) h1.symm

end FinalRestrict

section Gluing

/-- **Lifting through a monomorphism is local on the source.** If a morphism `φ` to the target of
a monomorphism `i` lifts through `i` on every member of an open cover of its source, it lifts. -/
private theorem exists_lift_of_openCover {Y P Z : Scheme.{u}} (i : Z ⟶ P) [Mono i] (φ : Y ⟶ P)
    (𝒰 : Y.OpenCover) (h : ∀ a, ∃ ψ : 𝒰.X a ⟶ Z, ψ ≫ i = 𝒰.f a ≫ φ) :
    ∃ ψ : Y ⟶ Z, ψ ≫ i = φ := by
  choose ψ hψ using h
  have hf : ∀ x y : 𝒰.I₀, pullback.fst (𝒰.f x) (𝒰.f y) ≫ ψ x =
      pullback.snd (𝒰.f x) (𝒰.f y) ≫ ψ y := by
    intro x y
    rw [← cancel_mono i, Category.assoc, Category.assoc, hψ x, hψ y, ← Category.assoc,
      ← Category.assoc, pullback.condition]
  refine ⟨𝒰.glueMorphisms ψ hf, ?_⟩
  refine 𝒰.hom_ext _ _ fun a => ?_
  rw [← Category.assoc, Scheme.Cover.ι_glueMorphisms, hψ]

end Gluing

section FinalAvoid

variable {k : Type u} [Field k] {C : Scheme.{u}} (sC : C ⟶ Spec (.of k)) (L : C.Modules)
    [IsInvertibleModule C L] {n N : ℕ} (e : Fin N → Γ(L, ⊤)) [IsProper sC] {κ : Type*} (q : κ →
    Γ(coefficientSpace n N k, ⊤)) (Zc : Set (projectiveSpaceOver n (Spec (.of k)))) (hZc : IsClosed
    Zc)

/-- **The family of maps on `M` avoids the closed set `Zc`** (by the definition of `M`). -/
private theorem finalFamily_base_not_mem (x : ↥(pullback sC (finalSpace.over (n := n) sC L e q Zc
    hZc))) :
    (finalFamily (n := n) sC L e q Zc hZc).base x ∉ Zc := by
  have ht := ((pullback.snd sC (finalSpace.over (n := n) sC L e q Zc hZc)).base x).2
  have ht' : ((finalSpace.ι (n := n) sC L e q Zc hZc).base
      ((pullback.snd sC (finalSpace.over (n := n) sC L e q Zc hZc)).base x)) ∈
      finalOpen (n := n) sC L e q Zc hZc := ht
  unfold finalOpen at ht'
  rw [mem_avoidOpen_iff] at ht'
  exact ht' ((familyMapOfHom sC (finalSpace.ι (n := n) sC L e q Zc hZc)
      (sT := closedNoCommonZeroScheme.over (n := n) sC L e q)
      (sT' := finalSpace.over (n := n) sC L e q Zc hZc) rfl).base x)
    (congrArg (fun φ => φ.base x) (familyMapOfHom_snd sC
      (finalSpace.ι (n := n) sC L e q Zc hZc)
      (sT := closedNoCommonZeroScheme.over (n := n) sC L e q)
      (sT' := finalSpace.over (n := n) sC L e q Zc hZc) rfl))

end FinalAvoid

section Generators

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k] {n : ℕ}

/-- **A homogeneous ideal of `k[T₀, …, Tₙ]` has finitely many homogeneous generators**
(Hilbert's basis theorem together with the decomposition into homogeneous components). -/
private theorem exists_finset_homogeneous_generators (J : HomogeneousIdeal (polyGrading k n)) :
    ∃ G : Finset (MvPolynomial (Fin (n + 1)) k),
      (∀ x ∈ G, ∃ d, x.IsHomogeneous d) ∧ J.toIdeal = Ideal.span (G : Set _) := by
  classical
  obtain ⟨S, hS⟩ := (IsNoetherian.noetherian J.toIdeal : J.toIdeal.FG)
  let G : Finset (MvPolynomial (Fin (n + 1)) k) :=
    S.biUnion fun f => ((DirectSum.decompose (polyGrading k n) f).support).image
      fun d => ((DirectSum.decompose (polyGrading k n) f d : polyGrading k n d) :
        MvPolynomial (Fin (n + 1)) k)
  refine ⟨G, ?_, ?_⟩
  · intro x hx
    simp only [G, Finset.mem_biUnion, Finset.mem_image] at hx
    obtain ⟨f, _, d, _, rfl⟩ := hx
    exact ⟨d, (MvPolynomial.mem_homogeneousSubmodule d _).1 (SetLike.coe_mem _)⟩
  · refine le_antisymm ?_ ?_
    · rw [← hS, Ideal.span_le]
      intro f hf
      have hfJ : f ∈ Ideal.span (G : Set _) := by
        rw [← DirectSum.sum_support_decompose (polyGrading k n) f]
        refine Ideal.sum_mem _ fun d hd => Ideal.subset_span ?_
        simp only [G, Finset.coe_biUnion, Finset.coe_image, Set.mem_iUnion, Set.mem_image,
          Finset.mem_coe]
        exact ⟨f, hf, d, hd, rfl⟩
      exact hfJ
    · rw [Ideal.span_le]
      intro x hx
      simp only [G, Finset.coe_biUnion, Finset.coe_image, Set.mem_iUnion, Set.mem_image,
        Finset.mem_coe] at hx
      obtain ⟨f, hf, d, _, rfl⟩ := hx
      have hfJ : f ∈ J.toIdeal := by rw [← hS]; exact Ideal.subset_span hf
      exact J.2 d hfJ

end Generators

section Bases

variable {k : Type u} [Field k] {C : Scheme.{u}} (sC : C ⟶ Spec (.of k)) [IsProper sC]

/-- **Global sections of a coherent module on a proper `k`-scheme have a finite `k`-basis**, in
the module structure over `Γ(Spec k, ⊤)` used for the coefficient space
(`H⁰` finite-dimensional, Stacks Tag 02O6). -/
private theorem exists_finBasis_globalSections (L' : C.Modules) [L'.IsCoherent] :
    ∃ m : ℕ, Nonempty (letI := baseModule sC L' ⊤;
      Module.Basis (Fin m) Γ(Spec (.of k), ⊤) Γ(L', ⊤)) := by
  have := finiteDimensional_cohomologyOverField_of_isProper k sC L' 0
  let b := Module.finBasis k (cohomologyOverField k sC L' 0)
  let e := (cohomologyOverFieldZeroIsoSections k sC L').toLinearEquiv
  letI kmod : Module k Γ(L', ⊤) :=
    Module.compHom _ ((Scheme.ΓSpecIso (.of k)).inv ≫ sC.appTop).hom
  let ι : ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of k)).inv ≫ sC.appTop).hom).obj
      ((_root_.SheafOfModules.evaluation C.ringCatSheaf (Opposite.op (⊤ : C.Opens))).obj L')) ≃ₗ[k]
      Γ(L', ⊤) :=
    { toFun := fun x => x, invFun := fun x => x, map_add' := fun _ _ => rfl,
      map_smul' := fun _ _ => rfl, left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  letI := baseModule sC L' ⊤
  exact ⟨_, ⟨((b.map e).map ι).mapCoeffs (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv
    fun c x => by
      change (sC.appLE ⊤ ⊤ _).hom ((Scheme.ΓSpecIso (.of k)).inv.hom c) • x =
        ((Scheme.ΓSpecIso (.of k)).inv ≫ sC.appTop).hom c • x
      rw [show sC.appLE ⊤ ⊤ (le_preimage_top sC ⊤) = sC.app ⊤ from
        Scheme.Hom.appLE_preimage_self sC ⊤]
      rfl⟩⟩

/-- **Finite `k`-bases of `H⁰(C, L^{⊗ d})`** for an invertible module on a proper `k`-scheme. -/
private theorem exists_finBasis_natTensorPow (L : C.Modules) [IsInvertibleModule C L] (d : ℕ) :
    ∃ m : ℕ, Nonempty (letI := baseModule sC (Stacks.TensorPowers.natTensorPow L d) ⊤;
      Module.Basis (Fin m) Γ(Spec (.of k), ⊤) Γ(Stacks.TensorPowers.natTensorPow L d, ⊤)) := by
  haveI : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian sC
  haveI : (Stacks.TensorPowers.natTensorPow L d).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isInvertible C _
  exact exists_finBasis_globalSections sC _

end Bases

section FinalAffine

variable {k : Type u} [Field k] {C : Scheme.{u}} (sC : C ⟶ Spec (.of k))
  (L : C.Modules) [IsInvertibleModule C L] {n N : ℕ} (e : Fin N → Γ(L, ⊤)) [IsProper sC]
  {ιE : Type} (F : ιE → MvPolynomial (Fin (n + 1)) k) (d : ιE → ℕ) {N' : ιE → ℕ}
  (w' : ∀ α, letI := baseModule sC (Stacks.TensorPowers.natTensorPow L (d α)) ⊤;
    Module.Basis (Fin (N' α)) Γ(Spec (.of k), ⊤)
      Γ(Stacks.TensorPowers.natTensorPow L (d α), ⊤))
  {ιB : Type} (ℓ : ιB → Fin N → k) (c : ιB → Fin (n + 1) → k) (μ : Fin (n + 1) → Fin N → k)
  (Zc : Set (projectiveSpaceOver n (Spec (.of k)))) (hZc : IsClosed Zc)
  {Z : Scheme.{u}} (i : Z ⟶ AlgebraicGeometry.projectiveSpaceOverRing n (CommRingCat.of k))
  [IsClosedImmersion i]

/-- **Affine pieces of `M` map into `Z`.** For an affine scheme `T` over `k` with a morphism `u`
to the curve-map space, the family `Φ` restricted to `C ×ₖ T` factors through the closed
subscheme `Z ⊆ ℙⁿ_k` cut out by the forms `F_α`. -/
private theorem exists_lift_finalFamily_affine
    (hF : ∀ α, (F α).IsHomogeneous (d α))
    (hJ : (closedSubschemeIdeal i).toIdeal = Ideal.span (Set.range F))
    {T : Scheme.{u}} [IsAffine T] {sT' : T ⟶ Spec (.of k)}
    (u : T ⟶ curveMapSpace (n := n) sC L e F d w' ℓ c μ Zc hZc)
    (hu : u ≫ finalSpace.over (n := n) sC L e
        (curveMapConditions (n := n) sC L e F d w' ℓ c μ) Zc hZc = sT') :
    ∃ ψ : pullback sC sT' ⟶ Z,
      ψ ≫ i = familyMapOfHom sC u hu ≫
        finalFamily (n := n) sC L e (curveMapConditions (n := n) sC L e F d w' ℓ c μ) Zc hZc := by
  subst hu
  set q := curveMapConditions (n := n) sC L e F d w' ℓ c μ with hq
  set g : T ⟶ coefficientSpace n N k :=
    u ≫ finalSpace.ι (n := n) sC L e q Zc hZc ≫ closedNoCommonZeroScheme.ι (n := n) sC L e q ≫
      closedLocus.ι (n := n) (N := N) (k := k) q with hg
  set h : T ⟶ noCommonZeroScheme (n := n) sC L e :=
    u ≫ finalSpace.ι (n := n) sC L e q Zc hZc ≫
      closedNoCommonZeroScheme.toNoCommonZero (n := n) sC L e q with hh
  have hgh : h ≫ noCommonZeroScheme.ι (n := n) sC L e = g := by
    rw [hh, hg, Category.assoc, Category.assoc, closedNoCommonZeroScheme.toNoCommonZero_ι]
  have hg0 : ∀ t : T, g.base t ∈ noCommonZeroOpen (n := n) sC L e := by
    intro t
    rw [← hgh]
    exact base_noCommonZeroScheme_ι_mem sC L e (h.base t)
  have hgq : ∀ κ, g.appTop (q κ) = 0 :=
    (exists_lift_zeroLocusScheme_ι_iff (coefficientSpace n N k) q g).1
      ⟨u ≫ finalSpace.ι (n := n) sC L e q Zc hZc ≫ closedNoCommonZeroScheme.ι (n := n) sC L e q,
        by rw [hg]; simp⟩
  obtain ⟨ψ, hψ⟩ := exists_lift_familyMap_of_equations sC L e F d w' i hF hJ g hg0
    (fun α j => hgq (Sum.inl ⟨α, j⟩))
  refine ⟨ψ, hψ.trans ?_⟩
  have hh' : h ≫ noCommonZeroScheme.over (n := n) sC L e = g ≫ coefficientSpaceOver n N k := by
    rw [← hgh]
    rfl
  exact (familyMapOfHom_noCommonZeroFamily_eq sC L e g h hgh hg0 hh').symm.trans
    (finalFamily_restrict sC L e q Zc hZc u).symm

/-- **The family of maps on the curve-map space `M` factors through `Z`** (the closed subscheme
`Ū ⊆ ℙⁿ_k` of the forms `F_α`): for the family `Φ : C ×ₖ M → ℙⁿ_k`, glueing the factorizations on
the pieces `C ×ₖ T` for `T` in an affine open cover of `M`. -/
private theorem exists_lift_finalFamily
    (hF : ∀ α, (F α).IsHomogeneous (d α))
    (hJ : (closedSubschemeIdeal i).toIdeal = Ideal.span (Set.range F)) :
    ∃ ψ : pullback sC (finalSpace.over (n := n) sC L e
        (curveMapConditions (n := n) sC L e F d w' ℓ c μ) Zc hZc) ⟶ Z,
      ψ ≫ i = finalFamily (n := n) sC L e
        (curveMapConditions (n := n) sC L e F d w' ℓ c μ) Zc hZc := by
  refine exists_lift_of_openCover i _
    ((curveMapSpace (n := n) sC L e F d w' ℓ c μ Zc hZc).affineCover.pullbackCoverOfRight sC
      (finalSpace.over (n := n) sC L e
        (curveMapConditions (n := n) sC L e F d w' ℓ c μ) Zc hZc)) fun a => ?_
  haveI : IsAffine ((curveMapSpace (n := n) sC L e F d w' ℓ c μ Zc hZc).affineCover.X a) :=
    Scheme.isAffine_affineCover _ a
  exact exists_lift_finalFamily_affine sC L e F d w' ℓ c μ Zc hZc i hF hJ
    ((curveMapSpace (n := n) sC L e F d w' ℓ c μ Zc hZc).affineCover.f a) rfl

/-- **The family of maps `Φ : C ×ₖ M → ℙⁿ_k` lands in the open subscheme `U` of the closed
subscheme `Z = Ū`.** Here `j : U ⟶ Z` is an open immersion and the avoided closed set `Zc` contains
the image of `Z ∖ U`; the factorization `C ×ₖ M → Z` of `exists_lift_finalFamily` avoids `Z ∖ U`
by the definition of `M`. -/
private theorem exists_lift_finalFamily_open
    (hF : ∀ α, (F α).IsHomogeneous (d α))
    (hJ : (closedSubschemeIdeal i).toIdeal = Ideal.span (Set.range F))
    {U : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j]
    (hZc' : ∀ z : Z, z ∉ Set.range j.base → i.base z ∈ Zc) :
    ∃ Φ : pullback sC (finalSpace.over (n := n) sC L e
        (curveMapConditions (n := n) sC L e F d w' ℓ c μ) Zc hZc) ⟶ U,
      Φ ≫ j ≫ i = finalFamily (n := n) sC L e
        (curveMapConditions (n := n) sC L e F d w' ℓ c μ) Zc hZc := by
  obtain ⟨ψ, hψ⟩ := exists_lift_finalFamily sC L e F d w' ℓ c μ Zc hZc i hF hJ
  have hr : Set.range ψ.base ⊆ Set.range j.base := by
    rintro _ ⟨x, rfl⟩
    by_contra hx
    refine finalFamily_base_not_mem sC L e
      (curveMapConditions (n := n) sC L e F d w' ℓ c μ) Zc hZc x ?_
    rw [← hψ]
    exact hZc' _ hx
  refine ⟨IsOpenImmersion.lift j ψ hr, ?_⟩
  rw [← Category.assoc, IsOpenImmersion.lift_fac, hψ]

end FinalAffine

section Landing

variable {k : Type u} [Field k] {C : Scheme.{u}} (sC : C ⟶ Spec (.of k)) (L : C.Modules)
    [IsInvertibleModule C L] {n N : ℕ} (e : Fin N → Γ(L, ⊤)) [IsProper sC] {ιB : Type} (ℓ : ιB →
    Fin N → k) (c : ιB → Fin (n + 1) → k) (μ : Fin (n + 1) → Fin N → k) (Zc : Set
    (projectiveSpaceOver n (Spec (.of k)))) (hZc : IsClosed Zc) {Z : Scheme.{u}} (i : Z ⟶
    AlgebraicGeometry.projectiveSpaceOverRing n (CommRingCat.of k)) [IsClosedImmersion i]

/-- **The family of maps of the fixed-line curve-map space lands in `U`.** For a closed subscheme
`Z = Ū ⊆ ℙⁿ_k`, an open subscheme `j : U ⟶ Z` and a closed set `Zc ⊇ i (Z ∖ U)`, there are finitely
many homogeneous generators `F_α` of the ideal of `Z`, with bases `w'_α` of `H⁰(C, L^{⊗ d_α})`,
such that the family `Φ : C ×ₖ M ⟶ ℙⁿ_k` of the space `M = curveMapSpace` built from them factors
through `U`. -/
private theorem exists_curveMapSpace_family {U : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j]
    (hZc' : ∀ z : Z, z ∉ Set.range j.base → i.base z ∈ Zc) :
    ∃ (ιE : Type) (_ : Finite ιE) (F : ιE → MvPolynomial (Fin (n + 1)) k) (d : ιE → ℕ)
      (N' : ιE → ℕ)
      (w' : ∀ α, letI := baseModule sC (Stacks.TensorPowers.natTensorPow L (d α)) ⊤;
        Module.Basis (Fin (N' α)) Γ(Spec (.of k), ⊤)
          Γ(Stacks.TensorPowers.natTensorPow L (d α), ⊤)),
      (∀ α, (F α).IsHomogeneous (d α)) ∧
      (closedSubschemeIdeal i).toIdeal = Ideal.span (Set.range F) ∧
      ∃ Φ : pullback sC (finalSpace.over (n := n) sC L e
          (curveMapConditions (n := n) sC L e F d w' ℓ c μ) Zc hZc) ⟶ U,
        Φ ≫ j ≫ i = finalFamily (n := n) sC L e
          (curveMapConditions (n := n) sC L e F d w' ℓ c μ) Zc hZc := by
  classical
  obtain ⟨G, hG, hGJ⟩ := exists_finset_homogeneous_generators (closedSubschemeIdeal i)
  let r : Fin G.card ≃ G := G.equivFin.symm
  let F : Fin G.card → MvPolynomial (Fin (n + 1)) k := fun a => (r a).1
  let d : Fin G.card → ℕ := fun a => Classical.choose (hG (r a).1 (r a).2)
  have hd : ∀ a, (F a).IsHomogeneous (d a) := fun a => Classical.choose_spec (hG (r a).1 (r a).2)
  let N' : Fin G.card → ℕ := fun a => (exists_finBasis_natTensorPow sC L (d a)).choose
  let w' : ∀ a, (letI := baseModule sC (Stacks.TensorPowers.natTensorPow L (d a)) ⊤;
        Module.Basis (Fin (N' a)) Γ(Spec (.of k), ⊤)
          Γ(Stacks.TensorPowers.natTensorPow L (d a), ⊤)) :=
    fun a => (exists_finBasis_natTensorPow sC L (d a)).choose_spec.some
  have hJ : (closedSubschemeIdeal i).toIdeal = Ideal.span (Set.range F) := by
    rw [hGJ]
    congr 1
    ext y
    simp only [Set.mem_range, Finset.mem_coe, F]
    exact ⟨fun h => ⟨r.symm ⟨y, h⟩, by simp⟩, fun ⟨a, ha⟩ => ha ▸ (r a).2⟩
  obtain ⟨Φ, hΦ⟩ := exists_lift_finalFamily_open sC L e F d w' ℓ c μ Zc hZc i hd hJ j hZc'
  exact ⟨Fin G.card, inferInstance, F, d, N', w', hd, hJ, Φ, hΦ⟩

end Landing

end CurveMapSpace

section Numerics

open MMP.Mori

variable {k : Type u} [Field k] {C U : Scheme.{u}}

/-- **`h¹(𝒪_C)` is the arithmetic genus** of an integral proper scheme of dimension at most one
over an algebraically closed field: `H⁰(C, 𝒪_C) = k` and the cohomology vanishes above degree
one. -/
private theorem finrank_cohomologyOverField_one_unit_eq_arithmeticGenus [IsAlgClosed k]
    (sC : C ⟶ Spec (.of k)) [IsProper sC] [IsIntegral C]
    (hC : topologicalKrullDim C ≤ 1) [(SheafOfModules.unit C.ringCatSheaf).IsCoherent] :
    (Module.finrank k (cohomologyOverField k sC (SheafOfModules.unit C.ringCatSheaf) 1) : ℤ) =
      arithmeticGenus sC := by
  have hvan : ∀ m, 2 ≤ m → IsZero (cohomologyOverField k sC
      (SheafOfModules.unit C.ringCatSheaf) m) := fun m hm =>
    isZero_cohomologyOverField_of_topologicalKrullDim_le k sC _ (d := 1)
      (by exact_mod_cast hC) (by omega : 1 < m)
  have h0 : Module.finrank k
      (cohomologyOverField k sC (SheafOfModules.unit C.ringCatSheaf) 0) = 1 := by
    rw [finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections]
    exact finrank_globalSections_eq_one k sC
  rw [arithmeticGenus, eulerCharacteristic_eq_sub_of_isZero k sC _ hvan, h0]
  ring

/-- **The dimension count from a two-stage obstruction theory with the cohomological obstruction
spaces.** Let `C` be integral and proper of dimension at most one over an algebraically closed
field, of arithmetic genus `g`, and `F` a coherent sheaf on `C`. If `M` is locally of finite type
over `k` with a `k`-point `m₀`, whose cotangent space has dimension at least `h⁰(F) - g`, and the
local ring of `M` at `m₀` carries a two-stage obstruction theory with obstruction spaces
`H¹(C, F)` and `H¹(C, 𝒪_C)`, then `dim 𝒪_{M,m₀} ≥ χ(C, F) - 2g`. -/
private theorem le_ringKrullDim_stalk_of_twoStageObstruction [IsAlgClosed k]
    (sC : C ⟶ Spec (.of k)) [IsProper sC] [IsIntegral C]
    (hC : topologicalKrullDim C ≤ 1) [(SheafOfModules.unit C.ringCatSheaf).IsCoherent]
    (g : ℕ) (hg : arithmeticGenus sC = g) (F : C.Modules) [F.IsCoherent]
    {M : Scheme.{u}} (sM : M ⟶ Spec (.of k)) [LocallyOfFiniteType sM]
    (m₀ : Spec (.of k) ⟶ M) (hm₀ : m₀ ≫ sM = 𝟙 _)
    (T : @TwoStageObstructionTheory k _ (M.presheaf.stalk (m₀ (closedPoint k))) _
      (Mori.stalkAlgebra sM (m₀ (closedPoint k))) (cohomologyOverField k sC F 1)
      (cohomologyOverField k sC (SheafOfModules.unit C.ringCatSheaf) 1) _ _ _ _)
    (htan : (Module.finrank k (cohomologyOverField k sC F 0) : ℤ) - g ≤
      Module.finrank (ResidueField (M.presheaf.stalk (m₀ (closedPoint k))))
        (CotangentSpace (M.presheaf.stalk (m₀ (closedPoint k))))) :
    ∀ n : ℕ, (n : ℤ) ≤ eulerCharacteristic k sC F - 2 * g →
      (n : WithBot ℕ∞) ≤ ringKrullDim (M.presheaf.stalk (m₀ (closedPoint k))) := by
  intro n hn
  have := finiteDimensional_cohomologyOverField_of_isProper k sC F 1
  have := finiteDimensional_cohomologyOverField_of_isProper k sC
    (SheafOfModules.unit C.ringCatSheaf) 1
  have hT := natCast_finrank_cotangentSpace_sub_le_topologicalKrullDimAt sM m₀ hm₀
    (closedPoint k) T
  have hclosed : IsClosed ({m₀ (closedPoint k)} : Set M) := by
    let : Algebra k (M.residueField (m₀ (closedPoint k))) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ sM.appTop ≫
        M.Γevaluation (m₀ (closedPoint k))).hom.toAlgebra
    have hfin : Module.finrank k (M.residueField (m₀ (closedPoint k))) = 1 :=
      ProjectiveLineCriterion.finrank_residueField_of_section sM m₀ hm₀ (closedPoint k)
    refine isClosed_singleton_of_module_finite_residueField sM _ ?_
    exact Module.finite_of_finrank_pos (by omega)
  rw [topologicalKrullDimAt_eq_krullDimOfRing_stalk k M sM _ hclosed] at hT
  refine le_trans ?_ hT
  have hvan : ∀ m, 2 ≤ m → IsZero (cohomologyOverField k sC F m) := fun m hm =>
    isZero_cohomologyOverField_of_topologicalKrullDim_le k sC _ (d := 1)
      (by exact_mod_cast hC) (by omega : 1 < m)
  have hχ := eulerCharacteristic_eq_sub_of_isZero k sC F hvan
  have hO := finrank_cohomologyOverField_one_unit_eq_arithmeticGenus sC hC
  rw [hg] at hO
  rw [hχ] at hn
  exact_mod_cast (show n ≤ _ by omega)

end Numerics

section MarkedPoints

variable {k : Type u} [Field k] {C : Scheme.{u}} {b : ℕ} (P : Fin b → (Spec (.of k) ⟶ C))

/-- The reduced closed subscheme of the marked points, as the morphism `Spec (kᵇ) ⟶ C` which is
`P i` on the `i`-th point. -/
private def markedPointsMap : Spec (.of (ULift.{u} (Fin b) → k)) ⟶ C :=
  inv (sigmaSpec (fun _ : ULift.{u} (Fin b) => CommRingCat.of k)) ≫ Sigma.desc (fun i => P i.down)

private theorem specMap_eval_markedPointsMap (i : ULift.{u} (Fin b)) :
    Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : ULift.{u} (Fin b) => k) i)) ≫
      markedPointsMap P = P i.down := by
  rw [markedPointsMap, ← ι_sigmaSpec (fun _ : ULift.{u} (Fin b) => CommRingCat.of k) i,
      Category.assoc,
    IsIso.hom_inv_id_assoc, Sigma.ι_desc]

private theorem markedPointsMap_comp (sC : C ⟶ Spec (.of k)) (hP : ∀ i, P i ≫ sC = 𝟙 _) :
    markedPointsMap P ≫ sC = Spec.map (CommRingCat.ofHom (algebraMap k (ULift.{u} (Fin b) → k))) :=
        by
  rw [markedPointsMap, Category.assoc, IsIso.inv_comp_eq]
  refine Sigma.hom_ext _ _ fun i => ?_
  rw [Sigma.ι_desc_assoc, hP i.down, ← Category.assoc, ι_sigmaSpec, ← Spec.map_comp]
  change 𝟙 _ = Spec.map (CommRingCat.ofHom (RingHom.id k))
  simp

private theorem isZeroDimensionalOfDegree_markedPointsMap (sC : C ⟶ Spec (.of k))
    (hP : ∀ i, P i ≫ sC = 𝟙 _) : IsZeroDimensionalOfDegree (markedPointsMap P ≫ sC) b := by
  rw [markedPointsMap_comp P sC hP]
  haveI : DiscreteTopology (Spec (.of (ULift.{u} (Fin b) → k))) :=
    inferInstanceAs (DiscreteTopology (PrimeSpectrum _))
  refine ⟨topologicalKrullDim_zero_of_discreteTopology _, ?_⟩
  rw [finrank_sections_specMap]
  have h := Module.finrank_fintype_fun_eq_card (R := k) (η := ULift.{u} (Fin b))
  rw [Fintype.card_ulift, Fintype.card_fin] at h
  convert h using 2
  · rfl

private theorem isClosedImmersion_markedPointsMap [IsAlgClosed k] (sC : C ⟶ Spec (.of k))
    [LocallyOfFiniteType sC] (hP : ∀ i, P i ≫ sC = 𝟙 _) (hPinj : Function.Injective P) :
    IsClosedImmersion (markedPointsMap P) := by
  have hQ : ∀ i, IsClosedImmersion (P i) := fun i => isClosedImmersion_of_comp_eq_id sC (P i) (hP i)
  set g := Sigma.desc (fun i : ULift.{u} (Fin b) => P i.down) with hg
  have hl : ∀ i (y : Spec (.of k)), g.base ((Sigma.ι (fun _ : ULift.{u} (Fin b) => Spec (.of k))
      i).base y) =
      (P i.down).base y := fun i y => by
    rw [← Scheme.Hom.comp_apply, hg, Sigma.ι_desc]
  have hsos : SurjectiveOnStalks g := by
    refine IsZariskiLocalAtSource.of_openCover
      (sigmaOpenCover (fun _ : ULift.{u} (Fin b) => Spec (.of k))) fun (i : ULift.{u} (Fin b)) => ?_
    change SurjectiveOnStalks (Sigma.ι (fun _ : ULift.{u} (Fin b) => Spec (.of k)) i ≫ g)
    rw [hg, Sigma.ι_desc]
    infer_instance
  have hsurj : ∀ x : ↥(∐ fun _ : ULift.{u} (Fin b) => Spec (.of k)),
      ∃ i y, (Sigma.ι (fun _ : ULift.{u} (Fin b) => Spec (.of k)) i).base y = x := by
    intro x
    obtain ⟨⟨i, y⟩, rfl⟩ := (sigmaMk (fun _ : ULift.{u} (Fin b) => Spec (.of k))).surjective x
    exact ⟨i, y, (sigmaMk_mk (fun _ : ULift.{u} (Fin b) => Spec (.of k)) i y).symm⟩
  have hinj : Function.Injective g.base := by
    intro x x' hxx
    obtain ⟨i, y, rfl⟩ := hsurj x
    obtain ⟨j, y', rfl⟩ := hsurj x'
    rw [hl, hl] at hxx
    obtain rfl : y = IsLocalRing.closedPoint k := Subsingleton.elim _ _
    obtain rfl : y' = IsLocalRing.closedPoint k := Subsingleton.elim _ _
    have h1 : (⟨P i.down, hP i.down⟩ : {p : Spec (.of k) ⟶ C // p ≫ sC = 𝟙 _}) =
        ⟨P j.down, hP j.down⟩ :=
      (pointEquivClosedPoint sC).injective (Subtype.ext hxx)
    obtain rfl : i = j := ULift.ext (hPinj (congrArg Subtype.val h1))
    rfl
  have hclosed : ∀ i, IsClosed ({(P i).base (IsLocalRing.closedPoint k)} : Set C) := by
    intro i
    have := (P i).isClosedEmbedding.isClosed_range
    have hr : Set.range (P i).base = {(P i).base (IsLocalRing.closedPoint k)} :=
      Set.ext fun z => ⟨by
          rintro ⟨x, rfl⟩; rw [Subsingleton.elim x (IsLocalRing.closedPoint k)]; rfl,
        by rintro rfl; exact ⟨_, rfl⟩⟩
    rwa [hr] at this
  have himage : ∀ s : Set ↥(∐ fun _ : ULift.{u} (Fin b) => Spec (.of k)),
      g.base '' s = ⋃ i ∈ {i : ULift.{u} (Fin b) | ∃ x ∈ s, ∃ y,
        (Sigma.ι (fun _ : ULift.{u} (Fin b) => Spec (.of k)) i).base y = x},
        {(P i.down).base (IsLocalRing.closedPoint k)} := by
    intro s
    ext z
    simp only [Set.mem_image, Set.mem_iUnion, Set.mem_singleton_iff, Set.mem_setOf_eq,
      exists_prop]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨i, y, rfl⟩ := hsurj x
      refine ⟨i, ⟨_, hx, y, rfl⟩, ?_⟩
      rw [hl, Subsingleton.elim y (IsLocalRing.closedPoint k)]
    · rintro ⟨i, ⟨x, hx, y, rfl⟩, rfl⟩
      refine ⟨_, hx, ?_⟩
      rw [hl, Subsingleton.elim y (IsLocalRing.closedPoint k)]
  have hcm : IsClosedMap g.base := by
    intro s _
    rw [himage s]
    exact (Set.toFinite _).isClosed_biUnion fun i _ => hclosed i.down
  have hemb : Topology.IsClosedEmbedding g.base :=
    Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap g.base.hom.continuous hinj hcm
  haveI : IsPreimmersion g := IsPreimmersion.mk hemb.isEmbedding
  haveI : IsClosedImmersion g := IsClosedImmersion.of_isPreimmersion g hemb.isClosed_range
  unfold markedPointsMap
  infer_instance

/-- Every point of `Spec (kᵇ)` is one of the `b` evaluation points. -/
private theorem exists_specMap_eval_eq (y : Spec (.of (ULift.{u} (Fin b) → k))) :
    ∃ i : ULift.{u} (Fin b), (Spec.map (CommRingCat.ofHom
      (Pi.evalRingHom (fun _ : ULift.{u} (Fin b) => k) i))).base (IsLocalRing.closedPoint k) =
        y := by
  set σ := sigmaSpec (fun _ : ULift.{u} (Fin b) => CommRingCat.of k)
  obtain ⟨⟨i, y'⟩, hz⟩ := (sigmaMk (fun _ : ULift.{u} (Fin b) => Spec (.of k))).surjective
    ((inv σ).base y)
  refine ⟨i, ?_⟩
  have h1 : (Sigma.ι (fun _ : ULift.{u} (Fin b) => Spec (.of k)) i).base y' = (inv σ).base y := by
    rw [← hz, sigmaMk_mk]
  rw [Subsingleton.elim (IsLocalRing.closedPoint k) y',
    ← ι_sigmaSpec (fun _ : ULift.{u} (Fin b) => CommRingCat.of k) i, Scheme.Hom.comp_apply, h1,
    ← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
  rfl

/-- **The functions killed by `Spec (kᵇ) ⟶ C` are those vanishing at the marked points.** -/
private theorem mem_vanishingIdeal_iff_app_markedPointsMap (V : C.Opens) (a : Γ(C, V)) :
    a ∈ CurveMapCharts.vanishingIdeal (fun β => (P β).base (IsLocalRing.closedPoint k)) V ↔
      ((markedPointsMap P).app V).hom a = 0 := by
  have hpt' : ∀ (i : ULift.{u} (Fin b)) (y' : Spec (.of k)), (markedPointsMap P).base
      ((Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : ULift.{u} (Fin b) => k) i))).base y') =
        (P i.down).base y' := fun i y' => by
    rw [← Scheme.Hom.comp_apply, specMap_eval_markedPointsMap]
  have hpt : ∀ i : ULift.{u} (Fin b), (markedPointsMap P).base ((Spec.map (CommRingCat.ofHom
      (Pi.evalRingHom (fun _ : ULift.{u} (Fin b) => k) i))).base (IsLocalRing.closedPoint k)) =
        (P i.down).base (IsLocalRing.closedPoint k) := fun i => hpt' i _
  have hgerm : ∀ (x x' : C) (hxx : x = x') (hx : x ∈ V) (hx' : x' ∈ V),
      C.presheaf.germ V x hx a ∈ IsLocalRing.maximalIdeal _ ↔
        C.presheaf.germ V x' hx' a ∈ IsLocalRing.maximalIdeal _ := by
    rintro x _ rfl hx hx'
    rfl
  rw [CurveMapCharts.mem_vanishingIdeal,
    MMP.Fourfold.CurveMapDerivations.app_eq_zero_iff_forall_stalkMap]
  simp only [MMP.Fourfold.CurveMapDerivations.stalkMap_eq_zero_iff _ _
    (MMP.Fourfold.CurveMapDerivations.isField_stalk_spec _ _)]
  constructor
  · intro h y hy
    obtain ⟨i, rfl⟩ := exists_specMap_eval_eq y
    exact (hgerm _ _ (hpt i).symm _ hy).1 (h i.down ((hpt i) ▸ hy))
  · intro h β hβ
    have hβ' := (hpt ⟨β⟩).symm ▸ hβ
    exact (hgerm _ _ (hpt ⟨β⟩) hβ' hβ).1 (h _ hβ')

/-- **The sections of the ideal sheaf of the marked points over an affine open** are the
functions vanishing at the marked points. -/
private theorem idealSheafSections_markedPoints [IsClosedImmersion (markedPointsMap P)]
    (V : C.Opens) (hV : IsAffineOpen V) (a : Γ(C, V)) :
    (∃ y, MMP.Fourfold.CurveMapDerivations.idealSheafSectionsIncl
      (markedPointsMap P).ker.subschemeι V y = a) ↔
      a ∈ CurveMapCharts.vanishingIdeal (fun β => (P β).base (IsLocalRing.closedPoint k)) V := by
  rw [MMP.Fourfold.CurveMapDerivations.exists_idealSheafSectionsIncl_eq_iff _ hV,
    Scheme.Hom.ker_apply, RingHom.mem_ker, mem_vanishingIdeal_iff_app_markedPointsMap]

end MarkedPoints

section MarkedTwist

variable {k : Type u} [Field k] [IsAlgClosed k] {C U : Scheme.{u}} (sC : C ⟶ Spec (.of k)) (sU : U
    ⟶ Spec (.of k))

/-- `H⁰(C, 𝒪_C) = k` for a proper integral scheme over an algebraically closed field. -/
private theorem isIso_globalSections_of_isProper [IsProper sC] [IsIntegral C] :
    IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ sC.appTop) := by
  have h1 := finrank_globalSections_eq_one k sC
  have : Nontrivial Γ(C, ⊤) := by
    letI : Algebra k Γ(C, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ sC.appTop).hom.toAlgebra
    exact Module.nontrivial_of_finrank_pos (R := k) (by rw [h1]; exact one_pos)
  exact Stacks.Models.isIso_constants_of_finrank_globalSections_eq_one sC h1

/-- **The sheaf `f^* T_U(-B)`**: the pullback of the tangent sheaf `T_U = Ω_{U/k}^∨` tensored with
the ideal sheaf of the reduced divisor `B = P₁ + ⋯ + P_b`. -/
private abbrev markedTangentSheaf (f : C ⟶ U) {b : ℕ} (P : Fin b → (Spec (.of k) ⟶ C)) : C.Modules
    :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨C.toRingedSpace.presheaf, C.toRingedSpace.IsSheaf⟩).obj
    ((Scheme.Modules.pullback f).obj (dualSheaf sU.relativeDifferentials))).obj
    (Stacks.ClosedImmersion.idealSheaf (markedPointsMap P).ker.subschemeι.toLRSHom.toShHom)

/-- **`χ(C, f^* T_U(-B)) = χ(C, f^* T_U) - n b`.** -/
private theorem eulerCharacteristic_markedTangentSheaf [IsProjectiveVariety k sC] [IsCurve k sC]
    {n : ℕ} [SmoothOfRelativeDimension n sU] (f : C ⟶ U)
    {b : ℕ} (P : Fin b → (Spec (.of k) ⟶ C)) (hP : ∀ i, P i ≫ sC = 𝟙 _)
    (hPinj : Function.Injective P)
    [((Scheme.Modules.pullback f).obj (dualSheaf sU.relativeDifferentials)).IsCoherent] :
    ∃ h : (markedTangentSheaf sU f P).IsCoherent,
      @eulerCharacteristic k _ C sC _ (markedTangentSheaf sU f P) h = eulerCharacteristic k sC
        ((Scheme.Modules.pullback f).obj (dualSheaf sU.relativeDifferentials)) - n * b := by
  have hvar : IsVariety k sC := inferInstance
  haveI : IsIntegral C := hvar.toIsIntegral
  haveI : LocallyOfFiniteType sC := hvar.toLocallyOfFiniteType
  haveI : IsProper sC := (inferInstance : IsProperVariety k sC).toIsProper
  haveI : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ sC.appTop) := isIso_globalSections_of_isProper sC
  have hC : topologicalKrullDim C = 1 := IsCurve.topologicalKrullDim_eq_one (k := k) (f := sC)
  haveI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} sU.relativeDifferentials n :=
    Stacks.Discriminant.isFiniteLocallyFreeOfRank_relativeDifferentials sU n
  haveI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (dualSheaf sU.relativeDifferentials) n :=
    isFiniteLocallyFreeOfRank_dualSheaf _ n inferInstance
  haveI hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback f).obj (dualSheaf sU.relativeDifferentials)) n :=
    AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback f _ n
  let S : CohenMacaulayCurveSituation.{u} :=
    { k := k, X := C, f := sC, dimension_one := hC }
  haveI := isClosedImmersion_markedPointsMap P sC hP hPinj
  obtain ⟨hdim, hdeg⟩ :=
      CohenMacaulayCurveSituation.subschemeDegree_ker_eq_of_isZeroDimensionalOfDegree
    (S := S) (markedPointsMap P) (isZeroDimensionalOfDegree_markedPointsMap P sC hP)
  haveI hI := S.isCoherent_idealSheafModule (markedPointsMap P).ker
  have hcoh := isCoherent_tensorSheaf_of_isCurve k sC
    ((Scheme.Modules.pullback f).obj (dualSheaf sU.relativeDifferentials)) n
    (S.idealSheafModule (markedPointsMap P).ker)
  refine ⟨hcoh, ?_⟩
  have h1 := eulerCharacteristic_tensorSheaf_eq_fiberRank_mul_curveDegree_add k sC
    ((Scheme.Modules.pullback f).obj (dualSheaf sU.relativeDifferentials)) n
    (S.idealSheafModule (markedPointsMap P).ker) hcoh
  rw [S.fiberRank_idealSheafModule_genericPoint _ hdim] at h1
  have hχI := S.eulerCharacteristic_idealSheafModule _ hdim
  rw [hdeg] at hχI
  haveI hO : (SheafOfModules.unit C.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k sC
  have hcoh' := isCoherent_tensorSheaf_of_isCurve k sC
    ((Scheme.Modules.pullback f).obj (dualSheaf sU.relativeDifferentials)) n
    (SheafOfModules.unit C.ringCatSheaf)
  have h2 := eulerCharacteristic_tensorSheaf_eq_fiberRank_mul_curveDegree_add k sC
    ((Scheme.Modules.pullback f).obj (dualSheaf sU.relativeDifferentials)) n
    (SheafOfModules.unit C.ringCatSheaf) hcoh'
  rw [Scheme.Modules.fiberRank_unit_eq_one, eulerCharacteristic_unit_eq_one_sub_genus k sC
    (le_of_eq hC)] at h2
  have h3 := @eulerCharacteristic_eq_of_iso k _ C sC _ _ _ hcoh' _
    (SheafOfModules.tensorSheafUnitRightIso C.toRingedSpace
      ((Scheme.Modules.pullback f).obj (dualSheaf sU.relativeDifferentials)))
  have hE' := h3.symm.trans h2
  have e1 : eulerCharacteristic k sC (S.idealSheafModule (markedPointsMap P).ker) =
      1 - (genus sC : ℤ) - b := hχI
  rw [h1, e1, hE']
  ring

end MarkedTwist

section TangentSpace

variable {k : Type u} [Field k]

/-- The structure morphism `Spec k[ε] ⟶ Spec k`. -/
private abbrev dualStruct : Spec (.of (DualNumber k)) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))

/-- The closed point `Spec k ⟶ Spec k[ε]`. -/
private abbrev dualClosed : Spec (.of k) ⟶ Spec (.of (DualNumber k)) :=
  Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)

private theorem dualClosed_surjective : Function.Surjective (dualClosed (k := k)).base := by
  intro p
  have hs : Function.Surjective (TrivSqZeroExt.fstHom k k k).toRingHom :=
    fun c => ⟨TrivSqZeroExt.inl c, rfl⟩
  have hr : p ∈ Set.range (PrimeSpectrum.comap (TrivSqZeroExt.fstHom k k k).toRingHom) := by
    rw [_root_.range_comap_of_surjective _ _ hs]
    intro x hx
    have hx' : x.fst = 0 := hx
    have hsq : x * x = 0 := by
      ext
      · simp [hx']
      · simp [hx']
    exact p.isPrime.mem_of_pow_mem 2 (by rw [pow_two, hsq]; exact p.asIdeal.zero_mem)
  obtain ⟨y, hy⟩ := hr
  exact ⟨y, hy⟩

private theorem dualClosed_struct : dualClosed (k := k) ≫ dualStruct = 𝟙 _ := by
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1

variable {n N : ℕ}

/-- The `k[ε]`-point of the coefficient space with coefficients `c`. -/
private abbrev dualTuple (c : Fin (n + 1) → Fin N → DualNumber k) :
    Spec (.of (DualNumber k)) ⟶ coefficientSpace n N k :=
  AffineSpace.homOfVector dualStruct
    (fun x : ULift.{u} (Fin (n + 1) × Fin N) =>
      (Scheme.ΓSpecIso (.of (DualNumber k))).inv (c x.down.1 x.down.2))

private theorem dualTuple_appTop_coord (c : Fin (n + 1) → Fin N → DualNumber k) (i : Fin (n + 1))
    (j : Fin N) : (dualTuple c).appTop (coefficientCoord n N k i j) =
      (Scheme.ΓSpecIso (.of (DualNumber k))).inv (c i j) :=
  AffineSpace.homOfVector_appTop_coord _ _ _

private theorem dualClosed_comp_dualTuple (c : Fin (n + 1) → Fin N → DualNumber k) :
    dualClosed ≫ dualTuple c = coefficientPoint (n := n) (N := N) (fun i j => (c i j).fst) := by
  rw [dualTuple, AffineSpace.comp_homOfVector, dualClosed_struct, coefficientPoint]
  congr 1
  funext x
  have := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)
  exact (congrArg (fun φ => φ (c x.down.1 x.down.2)) (congrArg CommRingCat.Hom.hom this)).symm

variable {C : Scheme.{u}} (sC : C ⟶ Spec (.of k)) (L : C.Modules) [IsInvertibleModule C L] (e : Fin
    N → Γ(L, ⊤)) [IsProper sC] {κ : Type*} (q : κ → Γ(coefficientSpace n N k, ⊤)) (Zc : Set
    (projectiveSpaceOver n (Spec (.of k)))) (hZc : IsClosed Zc)

/-- **`k[ε]`-points of `M` over `[f]`.** A tuple `c` in `k[ε]` reducing to the coefficients `a`
of a `k`-point of `M` and satisfying the closed conditions `q` is a `k[ε]`-point of `M`. -/
private theorem exists_lift_dualTuple (a : Fin (n + 1) → Fin N → k)
    (m₀ : Spec (.of k) ⟶ finalSpace (n := n) sC L e q Zc hZc)
    (hm₀c : m₀ ≫ finalSpace.toCoefficientSpace (n := n) sC L e q Zc hZc =
      coefficientPoint (n := n) (N := N) a)
    (c : Fin (n + 1) → Fin N → DualNumber k) (hc : ∀ i j, (c i j).fst = a i j)
    (hq : ∀ i, (dualTuple c).appTop (q i) = 0) :
    ∃ m' : Spec (.of (DualNumber k)) ⟶ finalSpace (n := n) sC L e q Zc hZc,
      m' ≫ finalSpace.toCoefficientSpace (n := n) sC L e q Zc hZc = dualTuple c := by
  obtain ⟨z, hz⟩ := (exists_lift_zeroLocusScheme_ι_iff (coefficientSpace n N k) q (dualTuple c)).2
      hq
  have hca : (fun i j => (c i j).fst) = a := funext fun i => funext fun j => hc i j
  have hz0 : dualClosed ≫ z = m₀ ≫ finalSpace.ι (n := n) sC L e q Zc hZc ≫
      closedNoCommonZeroScheme.ι (n := n) sC L e q := by
    rw [← cancel_mono (closedLocus.ι (n := n) (N := N) (k := k) q), Category.assoc, hz,
      dualClosed_comp_dualTuple, hca, ← hm₀c]
    simp only [Category.assoc]
  have hle : Set.range z.base ⊆ Set.range (finalSpace.ι (n := n) sC L e q Zc hZc ≫
      closedNoCommonZeroScheme.ι (n := n) sC L e q).base := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨s, rfl⟩ := dualClosed_surjective t
    refine ⟨m₀.base s, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← hz0]
    rfl
  refine ⟨IsOpenImmersion.lift _ z hle, ?_⟩
  rw [finalSpace.toCoefficientSpace, ← Category.assoc, ← Category.assoc,
    Category.assoc _ (finalSpace.ι (n := n) sC L e q Zc hZc), IsOpenImmersion.lift_fac, hz]

private theorem germ_top_stalkClosedPointTo_apply {X : Scheme.{u}} {R : Type u} [CommRing R]
    [IsLocalRing R] (g : Spec (.of R) ⟶ X) (h : Γ(X, ⊤)) :
    (Scheme.stalkClosedPointTo g).hom (X.presheaf.germ ⊤ _ trivial h) =
      (Scheme.ΓSpecIso (.of R)).hom (g.appTop h) := by
  have := Scheme.germ_stalkClosedPointTo g ⊤ trivial
  have h2 := congrArg (fun φ => φ.hom h) this
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
  rw [h2]
  rfl

/-- **The `k[ε]`-point of the local ring of `M` at `[f]`** attached to a tuple `c` in `k[ε]`
reducing to `a` and satisfying the closed conditions: a `k`-algebra map `𝒪_{M,[f]} → k[ε]`
sending the germ of each coordinate `x_{ij}` to `c_{ij}`. -/
private theorem exists_algHom_stalk_of_dualTuple (a : Fin (n + 1) → Fin N → k)
    (m₀ : Spec (.of k) ⟶ finalSpace (n := n) sC L e q Zc hZc)
    (hm₀c : m₀ ≫ finalSpace.toCoefficientSpace (n := n) sC L e q Zc hZc =
      coefficientPoint (n := n) (N := N) a)
    (c : Fin (n + 1) → Fin N → DualNumber k) (hc : ∀ i j, (c i j).fst = a i j)
    (hq : ∀ i, (dualTuple c).appTop (q i) = 0) :
    letI := MMP.Mori.stalkAlgebra (finalSpace.over (n := n) sC L e q Zc hZc)
      (m₀ (closedPoint k))
    ∃ φ : (finalSpace (n := n) sC L e q Zc hZc).presheaf.stalk (m₀ (closedPoint k)) →ₐ[k]
        DualNumber k, ∀ i j, φ ((finalSpace (n := n) sC L e q Zc hZc).presheaf.germ ⊤
          (m₀ (closedPoint k)) trivial
          ((finalSpace.toCoefficientSpace (n := n) sC L e q Zc hZc).appTop
            (coefficientCoord n N k i j))) = c i j := by
  haveI : Mono (finalSpace.toCoefficientSpace (n := n) sC L e q Zc hZc) := by
    unfold finalSpace.toCoefficientSpace
    infer_instance
  obtain ⟨m', hm'⟩ := exists_lift_dualTuple sC L e q Zc hZc a m₀ hm₀c c hc hq
  have hca : (fun i j => (c i j).fst) = a := funext fun i => funext fun j => hc i j
  have h0 : dualClosed ≫ m' = m₀ := by
    rw [← cancel_mono (finalSpace.toCoefficientSpace (n := n) sC L e q Zc hZc), Category.assoc,
      hm', dualClosed_comp_dualTuple, hca, hm₀c]
  have hover : m' ≫ finalSpace.over (n := n) sC L e q Zc hZc = dualStruct := by
    rw [← finalSpace.toCoefficientSpace_over, ← Category.assoc, hm']
    exact AffineSpace.homOfVector_over _ _
  have hpt : m' (closedPoint (DualNumber k)) = m₀ (closedPoint k) := by
    obtain ⟨s, hs⟩ := dualClosed_surjective (k := k) (closedPoint (DualNumber k))
    rw [← hs, Subsingleton.elim s (closedPoint k), ← h0]
    rfl
  suffices H : ∀ x (hx : m' (closedPoint (DualNumber k)) = x),
      letI := MMP.Mori.stalkAlgebra (finalSpace.over (n := n) sC L e q Zc hZc) x
      ∃ φ : (finalSpace (n := n) sC L e q Zc hZc).presheaf.stalk x →ₐ[k] DualNumber k,
        ∀ i j, φ ((finalSpace (n := n) sC L e q Zc hZc).presheaf.germ ⊤ x trivial
          ((finalSpace.toCoefficientSpace (n := n) sC L e q Zc hZc).appTop
            (coefficientCoord n N k i j))) = c i j from H _ hpt
  intro x hx
  subst hx
  letI := MMP.Mori.stalkAlgebra (finalSpace.over (n := n) sC L e q Zc hZc) (m' (closedPoint
      (DualNumber k)))
  have hcomp : ∀ {Y : Scheme.{u}} (G : finalSpace (n := n) sC L e q Zc hZc ⟶ Y) (h : Γ(Y, ⊤)),
      m'.appTop (G.appTop h) = (m' ≫ G).appTop h := fun G h => by
    rw [Scheme.Hom.comp_appTop]
    rfl
  refine ⟨{ toRingHom := (Scheme.stalkClosedPointTo m').hom, commutes' := fun r => ?_ }, ?_⟩
  · change (Scheme.stalkClosedPointTo m').hom ((finalSpace (n := n) sC L e q Zc hZc).presheaf.germ
      ⊤ _ trivial ((finalSpace.over (n := n) sC L e q Zc hZc).appTop
        ((Scheme.ΓSpecIso (.of k)).inv r))) = _
    rw [germ_top_stalkClosedPointTo_apply, hcomp, hover]
    have := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k (DualNumber k)))
    have h2 := congrArg (fun φ => φ.hom r) this
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
    erw [← h2]
    exact (Scheme.ΓSpecIso (.of (DualNumber k))).inv_hom_id_apply _
  · intro i j
    change (Scheme.stalkClosedPointTo m').hom _ = _
    rw [germ_top_stalkClosedPointTo_apply, hcomp, hm',
      dualTuple_appTop_coord]
    exact (Scheme.ΓSpecIso (.of (DualNumber k))).inv_hom_id_apply _

/-- **The tangent space of `M` at `[f]` contains every space of first-order tuples.** If every
`v` in the subspace `V` gives a tuple `a + ε v` in `k[ε]` satisfying the closed conditions `q`,
then `dim V ≤ dim 𝔪/𝔪²` for the local ring of `M` at `[f]`. -/
private theorem finrank_le_finrank_cotangentSpace_finalSpace (a : Fin (n + 1) → Fin N → k)
    (m₀ : Spec (.of k) ⟶ finalSpace (n := n) sC L e q Zc hZc)
    (hm₀ : m₀ ≫ finalSpace.over (n := n) sC L e q Zc hZc = 𝟙 _)
    (hm₀c : m₀ ≫ finalSpace.toCoefficientSpace (n := n) sC L e q Zc hZc =
      coefficientPoint (n := n) (N := N) a)
    (V : Submodule k (Fin (n + 1) × Fin N → k))
    (hV : ∀ v ∈ V, ∀ i, (dualTuple (fun i j => TrivSqZeroExt.inl (a i j) +
      TrivSqZeroExt.inr (v (i, j)))).appTop (q i) = 0) :
    letI := MMP.Mori.stalkAlgebra (finalSpace.over (n := n) sC L e q Zc hZc)
      (m₀ (closedPoint k))
    Module.finrank k V ≤ Module.finrank
      (ResidueField ((finalSpace (n := n) sC L e q Zc hZc).presheaf.stalk (m₀ (closedPoint k))))
      (CotangentSpace ((finalSpace (n := n) sC L e q Zc hZc).presheaf.stalk
        (m₀ (closedPoint k)))) := by
  letI := MMP.Mori.stalkAlgebra (finalSpace.over (n := n) sC L e q Zc hZc) (m₀ (closedPoint k))
  have hfin := ProjectiveLineCriterion.finrank_residueField_of_section (finalSpace.over (n := n) sC
      L e q Zc hZc) m₀ hm₀ (closedPoint k)
  have hk : Function.Bijective (algebraMap k (ResidueField ((finalSpace (n := n) sC L e q Zc
      hZc).presheaf.stalk (m₀ (closedPoint k))))) := by
    letI : Algebra k ((finalSpace (n := n) sC L e q Zc hZc).residueField (m₀ (closedPoint k))) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (finalSpace.over (n := n) sC L e q Zc hZc).appTop ≫
          (finalSpace (n := n) sC L e q Zc hZc).Γevaluation (m₀ (closedPoint k))).hom.toAlgebra
    have h1 : Function.Bijective (algebraMap k ((finalSpace (n := n) sC L e q Zc hZc).residueField
        (m₀ (closedPoint k)))) :=
      Algebra.finrank_eq_one_iff_bijective_algebraMap.1 hfin
    exact h1
  haveI := LocallyOfFiniteType.isLocallyNoetherian (finalSpace.over (n := n) sC L e q Zc hZc)
  haveI : IsNoetherianRing ((finalSpace (n := n) sC L e q Zc hZc).presheaf.stalk (m₀ (closedPoint
      k))) := inferInstance
  refine MMP.Fourfold.CurveMapDerivations.finrank_le_finrank_cotangentSpace_of_values hk
    (fun l => (finalSpace (n := n) sC L e q Zc hZc).presheaf.germ ⊤ (m₀ (closedPoint k)) trivial
      ((finalSpace.toCoefficientSpace (n := n) sC L e q Zc hZc).appTop
        (coefficientCoord n N k l.1 l.2)))
    (fun l => a l.1 l.2) V ?_
  intro v hv
  obtain ⟨φ, hφ⟩ := exists_algHom_stalk_of_dualTuple sC L e q Zc hZc a m₀ hm₀c
    (fun i j => TrivSqZeroExt.inl (a i j) + TrivSqZeroExt.inr (v (i, j))) (fun i j => by simp)
    (hV v hv)
  exact ⟨φ, fun l => hφ l.1 l.2⟩

end TangentSpace

/-! ### Points of the coefficient space with values in local Artinian algebras -/

section Reduction

variable {k : Type u} [Field k] {C : Scheme.{u}} (sC : C ⟶ Spec (.of k)) (L : C.Modules)
    [IsInvertibleModule C L] {n N : ℕ} (e : Fin N → Γ(L, ⊤)) [IsProper sC] {κ : Type*} (q : κ →
    Γ(coefficientSpace n N k, ⊤)) (Zc : Set (projectiveSpaceOver n (Spec (.of k)))) (hZc : IsClosed
    Zc)

/-- **Universal property of the coefficient space `M` for thickenings of `[f]`.** Let `T` be a
scheme with a surjection `r : Spec k ⟶ T` (so `T` is a single point), and `g : T ⟶ 𝔸` a `T`-point
of the coefficient space, reducing along `r` to the `k`-point `a` of a morphism `f : C ⟶ ℙⁿ_k`
avoiding `Zc` (`f^* 𝒪(1) ≅ L` carrying `f^* Tᵢ` to `τᵢ = Σⱼ aᵢⱼ eⱼ`). If `g` satisfies the
closed conditions `q`, then `g` lifts to `M`: the no-common-zero and avoidance conditions hold
automatically. -/
private theorem exists_lift_finalSpace_of_reduction {T : Scheme.{u}} (r : Spec (.of k) ⟶ T)
    (hr : Function.Surjective r.base) (g : T ⟶ coefficientSpace n N k)
    (a : Fin (n + 1) → Fin N → k)
    (f : C ⟶ projectiveSpaceOver n (Spec (.of k)))
    (hf : f ≫ pullback.fst (terminal.from (Spec (.of k)))
      (terminal.from (projectiveSpaceAtUniverse.{u} n)) = sC)
    (l : (Scheme.Modules.pullback (f ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of
        k)))).obj
      (twistingSheafAtUniverse.{u} n) ⟶ L) [IsIso l]
    (hτ : ∀ i, l.app ⊤ (pullbackCoordSection.{u}
        (f ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) i) =
      ∑ j, sC.appTop ((Scheme.ΓSpecIso (.of k)).inv (a i j)) • e j)
    (hZ : ∀ x : C, f.base x ∉ Zc)
    (hga : r ≫ g = coefficientPoint (n := n) (N := N) a)
    (hq : ∀ i, g.appTop (q i) = 0) :
    ∃ m : T ⟶ finalSpace (n := n) sC L e q Zc hZc,
      m ≫ finalSpace.ι (n := n) sC L e q Zc hZc ≫
        closedNoCommonZeroScheme.ι (n := n) sC L e q ≫
        closedLocus.ι (n := n) (N := N) (k := k) q = g := by
  have ha := coefficientPoint_mem_noCommonZeroOpen (n := n) (N := N) (L := L) (e := e) (sC := sC)
    a f l hτ
  have hg0 : ∀ t : T, g.base t ∈ noCommonZeroOpen (n := n) sC L e := by
    intro t
    obtain ⟨s, rfl⟩ := hr t
    have := ha s
    rw [← hga] at this
    exact this
  obtain ⟨z, hz⟩ := (exists_lift_zeroLocusScheme_ι_iff (coefficientSpace n N k) q g).2 hq
  have hle2 : Set.range z.base ⊆
      Set.range (closedNoCommonZeroScheme.ι (n := n) sC L e q).base := by
    rintro _ ⟨t, rfl⟩
    rw [Scheme.Opens.range_ι]
    change (closedLocus.ι (n := n) (N := N) (k := k) q).base (z.base t) ∈
      noCommonZeroOpen (n := n) sC L e
    have := hg0 t
    rw [← hz] at this
    exact this
  set m₂ := IsOpenImmersion.lift (closedNoCommonZeroScheme.ι (n := n) sC L e q) z hle2 with hm₂
  have hm₂ι : m₂ ≫ closedNoCommonZeroScheme.ι (n := n) sC L e q = z :=
    IsOpenImmersion.lift_fac _ _ _
  set m := m₂ ≫ closedNoCommonZeroScheme.toNoCommonZero (n := n) sC L e q with hm
  have hmι : m ≫ noCommonZeroScheme.ι (n := n) sC L e = g := by
    rw [hm, Category.assoc, closedNoCommonZeroScheme.toNoCommonZero_ι, ← Category.assoc, hm₂ι, hz]
  have hle3 : Set.range m₂.base ⊆ Set.range (finalSpace.ι (n := n) sC L e q Zc hZc).base := by
    rintro _ ⟨t, rfl⟩
    rw [Scheme.Opens.range_ι]
    change m₂.base t ∈ finalOpen (n := n) sC L e q Zc hZc
    unfold finalOpen
    rw [mem_avoidOpen_iff]
    intro x hx hxZ
    obtain ⟨x', hx'1, hx'2⟩ := exists_preimage_familyMapOfHom (sC := sC) m₂ rfl x t hx
    have h1 : closedNoCommonZeroFamily (n := n) sC L e q = familyMapOfHom sC
        (closedNoCommonZeroScheme.toNoCommonZero (n := n) sC L e q)
        (closedNoCommonZeroScheme.toNoCommonZero_over sC L e q) ≫
          noCommonZeroFamily (n := n) sC L e := rfl
    have hs : m ≫ noCommonZeroScheme.over (n := n) sC L e =
        m₂ ≫ closedNoCommonZeroScheme.over (n := n) sC L e q := by
      rw [hm, Category.assoc, closedNoCommonZeroScheme.toNoCommonZero_over]
    have h2 : (familyMapOfHom sC m₂ (sT := closedNoCommonZeroScheme.over (n := n) sC L e q)
          (sT' := m₂ ≫ closedNoCommonZeroScheme.over (n := n) sC L e q) rfl ≫
        closedNoCommonZeroFamily (n := n) sC L e q) =
        familyMapOfHom sC m hs ≫ noCommonZeroFamily (n := n) sC L e :=
      (congrArg (familyMapOfHom sC m₂ (sT := closedNoCommonZeroScheme.over (n := n) sC L e q)
          (sT' := m₂ ≫ closedNoCommonZeroScheme.over (n := n) sC L e q) rfl ≫ ·) h1).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ noCommonZeroFamily (n := n) sC L e)
            (familyMapOfHom_comp (sC := sC)
              (closedNoCommonZeroScheme.toNoCommonZero (n := n) sC L e q)
              (closedNoCommonZeroScheme.toNoCommonZero_over sC L e q) m₂ rfl).symm))
    rw [← hx'1, ← Scheme.Hom.comp_apply, h2] at hxZ
    -- reduce to the closed point
    obtain ⟨s, hs'⟩ := hr ((pullback.snd sC (m₂ ≫ closedNoCommonZeroScheme.over (n := n) sC L e
        q)).base x')
    obtain ⟨x'', hx''1, -⟩ := exists_preimage_familyMapOfHom (sC := sC) (T' := Spec (.of k))
      (sT := m₂ ≫ closedNoCommonZeroScheme.over (n := n) sC L e q) r rfl x' s hs'.symm
    have h3 := familyMapOfHom_comp (sC := sC) m hs r
      (sT'' := r ≫ m₂ ≫ closedNoCommonZeroScheme.over (n := n) sC L e q) rfl
    have hs2 : (r ≫ m) ≫ noCommonZeroScheme.over (n := n) sC L e =
        r ≫ m₂ ≫ closedNoCommonZeroScheme.over (n := n) sC L e q := by
      rw [Category.assoc, hs]
    have e3 : familyMapOfHom sC (r ≫ m) hs2 ≫ noCommonZeroFamily (n := n) sC L e =
        familyMapOfHom sC r (sT := m₂ ≫ closedNoCommonZeroScheme.over (n := n) sC L e q)
          (sT' := r ≫ m₂ ≫ closedNoCommonZeroScheme.over (n := n) sC L e q) rfl ≫
          familyMapOfHom sC m hs ≫ noCommonZeroFamily (n := n) sC L e := by
      rw [h3, Category.assoc]
    have hxZ' : (familyMapOfHom sC (r ≫ m) hs2 ≫ noCommonZeroFamily (n := n) sC L e).base x'' ∈
        Zc := by
      rw [e3]
      rw [← hx''1, ← Scheme.Hom.comp_apply] at hxZ
      exact hxZ
    have hmk : (r ≫ m) ≫ noCommonZeroScheme.ι (n := n) sC L e =
        coefficientPoint (n := n) (N := N) a := by
      rw [Category.assoc, hmι, hga]
    exact familyMapOfHom_noCommonZeroFamily_not_mem sC L e a f hf l hτ (r ≫ m) hmk
      hZ hs2 x'' hxZ'
  refine ⟨IsOpenImmersion.lift (finalSpace.ι (n := n) sC L e q Zc hZc) m₂ hle3, ?_⟩
  rw [← Category.assoc, IsOpenImmersion.lift_fac, ← Category.assoc, hm₂ι, hz]

/-- **Universal property of the coefficient space `M` for thickenings of `[f]`: both directions.**
For `T`, `r`, `g`, `a`, `f` as in `exists_lift_finalSpace_of_reduction`, the `T`-point `g` of the
coefficient space lifts to `M` if and only if it satisfies the closed conditions `q`. -/
private theorem exists_lift_finalSpace_iff_of_reduction {T : Scheme.{u}} (r : Spec (.of k) ⟶ T)
    (hr : Function.Surjective r.base) (g : T ⟶ coefficientSpace n N k)
    (a : Fin (n + 1) → Fin N → k)
    (f : C ⟶ projectiveSpaceOver n (Spec (.of k)))
    (hf : f ≫ pullback.fst (terminal.from (Spec (.of k)))
      (terminal.from (projectiveSpaceAtUniverse.{u} n)) = sC)
    (l : (Scheme.Modules.pullback (f ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of
        k)))).obj
      (twistingSheafAtUniverse.{u} n) ⟶ L) [IsIso l]
    (hτ : ∀ i, l.app ⊤ (pullbackCoordSection.{u}
        (f ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) i) =
      ∑ j, sC.appTop ((Scheme.ΓSpecIso (.of k)).inv (a i j)) • e j)
    (hZ : ∀ x : C, f.base x ∉ Zc)
    (hga : r ≫ g = coefficientPoint (n := n) (N := N) a) :
    (∃ m : T ⟶ finalSpace (n := n) sC L e q Zc hZc,
      m ≫ finalSpace.ι (n := n) sC L e q Zc hZc ≫
        closedNoCommonZeroScheme.ι (n := n) sC L e q ≫
        closedLocus.ι (n := n) (N := N) (k := k) q = g) ↔
    ∀ i, g.appTop (q i) = 0 := by
  refine ⟨fun ⟨m, hm⟩ => ?_, exists_lift_finalSpace_of_reduction sC L e q Zc hZc r hr g a f hf l hτ
    hZ hga⟩
  refine (exists_lift_zeroLocusScheme_ι_iff (coefficientSpace n N k) q g).1
    ⟨m ≫ finalSpace.ι (n := n) sC L e q Zc hZc ≫ closedNoCommonZeroScheme.ι (n := n) sC L e q, ?_⟩
  rw [← hm]
  simp only [Category.assoc]

end Reduction

section TuplePoint

variable {k : Type u} [Field k] {n N : ℕ}

/-- **The `T`-point of the coefficient space with the given coefficients** `c i j ∈ Γ(T, 𝒪)`
(over the structure morphism `sT`). -/
private def tuplePoint {T : Scheme.{u}} (sT : T ⟶ Spec (.of k)) (c : Fin (n + 1) → Fin N → Γ(T, ⊤))
    :
    T ⟶ coefficientSpace n N k :=
  AffineSpace.homOfVector sT (fun x : ULift.{u} (Fin (n + 1) × Fin N) => c x.down.1 x.down.2)

private theorem tuplePoint_over {T : Scheme.{u}} (sT : T ⟶ Spec (.of k))
    (c : Fin (n + 1) → Fin N → Γ(T, ⊤)) :
    tuplePoint sT c ≫ coefficientSpaceOver n N k = sT :=
  AffineSpace.homOfVector_over _ _

private theorem tuplePoint_appTop_coord {T : Scheme.{u}} (sT : T ⟶ Spec (.of k))
    (c : Fin (n + 1) → Fin N → Γ(T, ⊤)) (i : Fin (n + 1)) (j : Fin N) :
    (tuplePoint sT c).appTop (coefficientCoord n N k i j) = c i j :=
  AffineSpace.homOfVector_appTop_coord _ _ _

private theorem coefficientPoint_eq_tuplePoint (a : Fin (n + 1) → Fin N → k) :
    coefficientPoint (n := n) (N := N) a =
      tuplePoint (𝟙 (Spec (.of k))) (fun i j => (Scheme.ΓSpecIso (.of k)).inv (a i j)) := rfl

/-- **Every `T`-point of the coefficient space is the tuple of its coordinates.** -/
private theorem eq_tuplePoint {T : Scheme.{u}} (g : T ⟶ coefficientSpace n N k) :
    g = tuplePoint (g ≫ coefficientSpaceOver n N k)
      (fun i j => g.appTop (coefficientCoord n N k i j)) := by
  ext : 2
  · rw [tuplePoint_over]
  · rename_i x
    obtain ⟨⟨i, j⟩⟩ := x
    exact (tuplePoint_appTop_coord (g ≫ coefficientSpaceOver n N k)
      (fun i j => g.appTop (coefficientCoord n N k i j)) i j).symm

private theorem comp_tuplePoint {T T' : Scheme.{u}} (r : T' ⟶ T) (sT : T ⟶ Spec (.of k))
    (c : Fin (n + 1) → Fin N → Γ(T, ⊤)) :
    r ≫ tuplePoint sT c = tuplePoint (r ≫ sT) (fun i j => r.appTop (c i j)) :=
  AffineSpace.comp_homOfVector _ _ _

/-- A `T`-point `tuplePoint sT c` reduces along `r : Spec k ⟶ T` to the `k`-point `a` as soon
as the coefficients do. -/
private theorem comp_tuplePoint_eq_coefficientPoint {T : Scheme.{u}} (r : Spec (.of k) ⟶ T)
    (sT : T ⟶ Spec (.of k)) (hr : r ≫ sT = 𝟙 _) (c : Fin (n + 1) → Fin N → Γ(T, ⊤))
    (a : Fin (n + 1) → Fin N → k)
    (h : ∀ i j, r.appTop (c i j) = (Scheme.ΓSpecIso (.of k)).inv (a i j)) :
    r ≫ tuplePoint sT c = coefficientPoint (n := n) (N := N) a := by
  rw [comp_tuplePoint, coefficientPoint_eq_tuplePoint, hr]
  congr 1
  funext i j
  exact h i j

end TuplePoint

section Artin

variable {k : Type u} [Field k] {n N : ℕ} (A : ArtinLocalAlgebra k)

/-- The residue map `A → k` of a local Artinian `k`-algebra with residue field `k`. -/
private def artinToResidue : A.carrier →ₐ[k] k :=
  letI e : k ≃+* IsLocalRing.ResidueField A.carrier :=
    RingEquiv.ofBijective (algebraMap k (IsLocalRing.ResidueField A.carrier)) A.residue_bijective
  { toRingHom := e.symm.toRingHom.comp (IsLocalRing.residue A.carrier)
    commutes' := fun x => by
      change e.symm (IsLocalRing.residue A.carrier (algebraMap k A.carrier x)) = x
      have : IsLocalRing.residue A.carrier (algebraMap k A.carrier x) = e x := rfl
      rw [this, RingEquiv.symm_apply_apply] }

/-- The structure morphism of `Spec A`. -/
private def artinStructMap : Spec (.of A.carrier) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k A.carrier))

/-- The closed point `Spec k ⟶ Spec A`. -/
private def artinClosedPoint : Spec (.of k) ⟶ Spec (.of A.carrier) :=
  Spec.map (CommRingCat.ofHom (artinToResidue A).toRingHom)

private theorem artinClosedPoint_structMap : (artinClosedPoint A) ≫ (artinStructMap A) = 𝟙 _ := by
  unfold artinClosedPoint artinStructMap
  rw [← Spec.map_comp]
  have : CommRingCat.ofHom (algebraMap k A.carrier) ≫ CommRingCat.ofHom (artinToResidue
      A).toRingHom =
      𝟙 (CommRingCat.of k) := by
    ext x
    exact (artinToResidue A).commutes x
  rw [this, Spec.map_id]

/-- `Spec A` is a single point: the closed point `Spec k ⟶ Spec A` is surjective. -/
private theorem artinClosedPoint_surjective : Function.Surjective (artinClosedPoint A).base := by
  haveI : Subsingleton (Spec (.of A.carrier)) := Ring.KrullDimLE.subsingleton_primeSpectrum _
  exact fun _ => ⟨IsLocalRing.closedPoint k, Subsingleton.elim _ _⟩

/-- The `A`-point of the coefficient space with coefficients `c i j ∈ A`. -/
private def artinCoefficientPoint (c : Fin (n + 1) → Fin N → A.carrier) :
    Spec (.of A.carrier) ⟶ coefficientSpace n N k :=
  tuplePoint (artinStructMap A) (fun i j => (Scheme.ΓSpecIso (.of A.carrier)).inv (c i j))

/-- The `A`-point with coefficients `c` reduces to the `k`-point `a` when `c` reduces to `a`. -/
private theorem artinClosedPoint_comp_coefficientPoint (c : Fin (n + 1) → Fin N → A.carrier)
    (a : Fin (n + 1) → Fin N → k) (h : ∀ i j, (artinToResidue A) (c i j) = a i j) :
    (artinClosedPoint A) ≫ (artinCoefficientPoint A) c = MMP.Fourfold.coefficientPoint (n := n) (N
        := N) a := by
  refine comp_tuplePoint_eq_coefficientPoint _ _ (artinClosedPoint_structMap A) _ _ fun i j => ?_
  have := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (artinToResidue A).toRingHom)
  have h2 := congrArg (fun φ => φ (c i j)) (congrArg CommRingCat.Hom.hom this)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
  rw [artinClosedPoint]
  rw [← h i j]
  exact h2.symm

end Artin

section ArtinMain

variable {k : Type u} [Field k] {C : Scheme.{u}} (sC : C ⟶ Spec (.of k)) (L : C.Modules)
    [IsInvertibleModule C L] {n N : ℕ} (e : Fin N → Γ(L, ⊤)) [IsProper sC] {κ : Type*} (q : κ →
    Γ(coefficientSpace n N k, ⊤)) (Zc : Set (projectiveSpaceOver n (Spec (.of k)))) (hZc : IsClosed
    Zc)

/-- **The universal property of `M` for `Spec A`, `A` local Artinian with residue field `k`.**
Let `f : C ⟶ ℙⁿ_k` avoid `Zc`, with `f^* 𝒪(1) ≅ L` carrying `f^* Tᵢ` to `τᵢ = Σⱼ aᵢⱼ eⱼ`. The
`A`-points of `M` reducing to `[f]` are exactly the tuples `c` of coefficients in `A` reducing to
`a` that satisfy the closed conditions `q`: no condition of non-vanishing (open) or avoidance of
`Zc` remains. -/
private theorem exists_lift_finalSpace_artin_iff (A : ArtinLocalAlgebra k)
    (a : Fin (n + 1) → Fin N → k)
    (f : C ⟶ projectiveSpaceOver n (Spec (.of k)))
    (hf : f ≫ pullback.fst (terminal.from (Spec (.of k)))
      (terminal.from (projectiveSpaceAtUniverse.{u} n)) = sC)
    (l : (Scheme.Modules.pullback (f ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of
        k)))).obj
      (twistingSheafAtUniverse.{u} n) ⟶ L) [IsIso l]
    (hτ : ∀ i, l.app ⊤ (pullbackCoordSection.{u}
        (f ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) i) =
      ∑ j, sC.appTop ((Scheme.ΓSpecIso (.of k)).inv (a i j)) • e j)
    (hZ : ∀ x : C, f.base x ∉ Zc) (c : Fin (n + 1) → Fin N → A.carrier)
    (hc : ∀ i j, (artinToResidue A) (c i j) = a i j) :
    (∃ m : Spec (.of A.carrier) ⟶ finalSpace (n := n) sC L e q Zc hZc,
      m ≫ finalSpace.ι (n := n) sC L e q Zc hZc ≫
        closedNoCommonZeroScheme.ι (n := n) sC L e q ≫
        closedLocus.ι (n := n) (N := N) (k := k) q = (artinCoefficientPoint A) c) ↔
    ∀ i, ((artinCoefficientPoint A) c).appTop (q i) = 0 :=
  exists_lift_finalSpace_iff_of_reduction sC L e q Zc hZc (artinClosedPoint A)
      (artinClosedPoint_surjective A)
    _ a f hf l hτ hZ ((artinClosedPoint_comp_coefficientPoint A) c a hc)

end ArtinMain

section Stalk

variable {k : Type u} [Field k] {M : Scheme.{u}} (sM : M ⟶ Spec (.of k)) (x : M)

/-- The structure map `k → 𝒪_{M, x}` of the stalk of a `k`-scheme. -/
private def stalkAlgebraMap : k →+* M.presheaf.stalk x :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ sM.appTop ≫ M.presheaf.germ ⊤ x trivial).hom

private theorem fromSpecStalk_comp_over_appTop (A : Type u) [CommRing A] [IsLocalRing A]
    (b : M.presheaf.stalk x ⟶ CommRingCat.of A) :
    (Scheme.ΓSpecIso (.of k)).inv ≫ (Spec.map b ≫ M.fromSpecStalk x ≫ sM).appTop =
      CommRingCat.ofHom (stalkAlgebraMap sM x) ≫ b ≫ (Scheme.ΓSpecIso (.of A)).inv := by
  simp only [Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop, Category.assoc, stalkAlgebraMap,
    CommRingCat.ofHom_hom]
  erw [CategoryTheory.Functor.map_id]
  simp only [Category.id_comp]
  rw [← Scheme.ΓSpecIso_inv_naturality b]

private theorem specMap_fromSpecStalk_comp_over_eq_iff (A : Type u) [CommRing A] [IsLocalRing A]
    [Algebra k A] (b : M.presheaf.stalk x ⟶ CommRingCat.of A) :
    Spec.map b ≫ M.fromSpecStalk x ≫ sM = Spec.map (CommRingCat.ofHom (algebraMap k A)) ↔
      b.hom.comp (stalkAlgebraMap sM x) = algebraMap k A := by
  have key : (Spec.map b ≫ M.fromSpecStalk x ≫ sM = Spec.map (CommRingCat.ofHom (algebraMap k A))) ↔
      (Scheme.ΓSpecIso (.of k)).inv ≫ (Spec.map b ≫ M.fromSpecStalk x ≫ sM).appTop =
        (Scheme.ΓSpecIso (.of k)).inv ≫
          (Spec.map (CommRingCat.ofHom (algebraMap k A))).appTop :=
    ⟨fun h => by rw [h], fun h => ext_of_isAffine ((cancel_epi _).1 h)⟩
  rw [key, fromSpecStalk_comp_over_appTop, ← Scheme.ΓSpecIso_inv_naturality, ← Category.assoc,
    cancel_mono]
  exact ⟨congrArg CommRingCat.Hom.hom, fun h => CommRingCat.hom_ext h⟩

end Stalk

section LocalAlgebra

variable {k : Type u} [Field k] {R S : Type*} [CommRing R] [IsLocalRing R] [Algebra k R]
    [CommRing S] [IsLocalRing S] [Algebra k S]

/-- A `k`-algebra map between local `k`-algebras, the target having a `k`-point, is local. -/
private theorem isLocalHom_of_algHom (φ : R →ₐ[k] S) (ε : S →ₐ[k] k) : IsLocalHom φ.toRingHom := by
  refine ⟨fun y hy => ?_⟩
  by_contra hne
  have hm : y ∈ IsLocalRing.maximalIdeal R := by
    simpa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hne
  rw [← ker_algHom_eq_maximalIdeal' (ε.comp φ)] at hm
  exact (IsLocalRing.mem_maximalIdeal _).1 (by rwa [← ker_algHom_eq_maximalIdeal' ε]) hy

end LocalAlgebra

section ArtinMorphisms

variable {k : Type u} [Field k] {n N : ℕ} (A A' : ArtinLocalAlgebra k)

/-- Coefficients of an `A`-point recovered from its reduction. -/
private theorem artinToResidue_eq_of_closedPoint_comp (c : Fin (n + 1) → Fin N → A.carrier)
    (a : Fin (n + 1) → Fin N → k)
    (h : artinClosedPoint A ≫ artinCoefficientPoint A c =
      MMP.Fourfold.coefficientPoint (n := n) (N := N) a)
    (i : Fin (n + 1)) (j : Fin N) : artinToResidue A (c i j) = a i j := by
  have h1 := congrArg (fun g => g.appTop (coefficientCoord n N k i j)) h
  simp only [artinCoefficientPoint, comp_tuplePoint, tuplePoint_appTop_coord,
    MMP.Fourfold.coefficientPoint_appTop_coord] at h1
  have := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (artinToResidue A).toRingHom)
  have h2 := congrArg (fun φ => φ (c i j)) (congrArg CommRingCat.Hom.hom this)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
  rw [artinClosedPoint] at h1
  rw [← h2] at h1
  exact ConcreteCategory.injective_of_mono_of_preservesPullback (Scheme.ΓSpecIso (.of k)).inv h1

/-- Base change of the tuple along a `k`-algebra map `π : A' → A`. -/
private theorem artinSpecMap_comp_coefficientPoint (π : A'.carrier →ₐ[k] A.carrier)
    (c : Fin (n + 1) → Fin N → A'.carrier) :
    Spec.map (CommRingCat.ofHom π.toRingHom) ≫ (artinCoefficientPoint A') c =
      (artinCoefficientPoint A) (fun i j => π (c i j)) := by
  unfold artinCoefficientPoint
  rw [comp_tuplePoint]
  have hs : Spec.map (CommRingCat.ofHom π.toRingHom) ≫ (artinStructMap A') = (artinStructMap A) :=
      by
    unfold artinStructMap
    rw [← Spec.map_comp]
    congr 2
    ext x
    exact π.commutes x
  rw [hs]
  congr 1
  funext i j
  have := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom π.toRingHom)
  have h2 := congrArg (fun φ => φ (c i j)) (congrArg CommRingCat.Hom.hom this)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
  exact h2.symm

end ArtinMorphisms

section StalkPoints

variable {k : Type u} [Field k] {M : Scheme.{u}} (sM : M ⟶ Spec (.of k))

/-- Two ring maps from the stalk of a `k`-scheme to `k` that are `k`-linear agree. -/
private theorem stalk_ringHom_eq_of_comp (x : M) (φ ψ : M.presheaf.stalk x →+* k)
    (hφ : φ.comp (stalkAlgebraMap sM x) = RingHom.id k)
    (hψ : ψ.comp (stalkAlgebraMap sM x) = RingHom.id k) : φ = ψ := by
  letI : Algebra k (M.presheaf.stalk x) := (stalkAlgebraMap sM x).toAlgebra
  have := algHom_eq_of_local' (k := k) (R := M.presheaf.stalk x)
    { toRingHom := φ, commutes' := fun r => congrArg (fun h => h r) hφ }
    { toRingHom := ψ, commutes' := fun r => congrArg (fun h => h r) hψ }
  exact congrArg AlgHom.toRingHom this

/-- A `k`-point of the stalk-scheme through `x` is the one given by the unique `k`-linear map
`𝒪_{M,x} → k`. -/
private theorem closedPoint_comp_specMap_fromSpecStalk (m0 : Spec (.of k) ⟶ M) (hm0 : m0 ≫ sM = 𝟙 _)
    (x : M) (hx : m0 (IsLocalRing.closedPoint (CommRingCat.of k)) = x)
    (A : ArtinLocalAlgebra k) (a : M.presheaf.stalk x →+* A.carrier)
    (ha : a.comp (stalkAlgebraMap sM x) = algebraMap k A.carrier) :
    (artinClosedPoint A) ≫ Spec.map (CommRingCat.ofHom a) ≫ M.fromSpecStalk x = m0 := by
  subst hx
  have h0 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk m0
  have hb0 : (Scheme.stalkClosedPointTo m0).hom.comp
      (stalkAlgebraMap sM (m0 (IsLocalRing.closedPoint (CommRingCat.of k)))) = RingHom.id k := by
    have := (specMap_fromSpecStalk_comp_over_eq_iff sM
      (m0 (IsLocalRing.closedPoint (CommRingCat.of k))) k (Scheme.stalkClosedPointTo m0)).1 (by
      rw [← Category.assoc, h0, hm0]
      have : CommRingCat.ofHom (algebraMap k k) = 𝟙 (CommRingCat.of k) := by
        ext x; simp
      rw [this, Spec.map_id])
    simpa using this
  have hab : ((artinToResidue A).toRingHom.comp a).comp
      (stalkAlgebraMap sM (m0 (IsLocalRing.closedPoint (CommRingCat.of k)))) = RingHom.id k := by
    rw [RingHom.comp_assoc, ha]
    ext x
    exact (artinToResidue A).commutes x
  have heq := stalk_ringHom_eq_of_comp sM _ _ _ hab hb0
  rw [artinClosedPoint, ← Category.assoc, ← Spec.map_comp]
  conv_rhs => rw [← h0]
  congr 2
  exact CommRingCat.hom_ext heq

private theorem isLocalHom_stalk_of_comp (x : M) (A : ArtinLocalAlgebra k) (a : M.presheaf.stalk x
    →+* A.carrier)
    (ha : a.comp (stalkAlgebraMap sM x) = algebraMap k A.carrier) : IsLocalHom a := by
  letI : Algebra k (M.presheaf.stalk x) := (stalkAlgebraMap sM x).toAlgebra
  exact isLocalHom_of_algHom (k := k) (R := M.presheaf.stalk x) (S := A.carrier)
    { toRingHom := a, commutes' := fun r => congrArg (fun h => h r) ha } (artinToResidue A)

private theorem specMap_fromSpecStalk_comp_over (x : M) (A : ArtinLocalAlgebra k)
    (a : M.presheaf.stalk x →+* A.carrier)
    (ha : a.comp (stalkAlgebraMap sM x) = algebraMap k A.carrier) :
    Spec.map (CommRingCat.ofHom a) ≫ M.fromSpecStalk x ≫ sM = (artinStructMap A) :=
  (specMap_fromSpecStalk_comp_over_eq_iff sM x A.carrier (CommRingCat.ofHom a)).2 ha

private theorem exists_stalk_hom_of_spec (A : ArtinLocalAlgebra k) (m : Spec (.of A.carrier) ⟶ M)
    (hm : m ≫ sM = (artinStructMap A)) (x : M) (hx : m (IsLocalRing.closedPoint A.carrier) = x) :
    ∃ b : M.presheaf.stalk x →+* A.carrier, IsLocalHom b ∧
      b.comp (stalkAlgebraMap sM x) = algebraMap k A.carrier ∧
      Spec.map (CommRingCat.ofHom b) ≫ M.fromSpecStalk x = m := by
  subst hx
  refine ⟨(Scheme.stalkClosedPointTo m).hom, inferInstance, ?_, ?_⟩
  · refine (specMap_fromSpecStalk_comp_over_eq_iff sM _ A.carrier
      (Scheme.stalkClosedPointTo m)).1 ?_
    rw [Scheme.Spec_stalkClosedPointTo_fromSpecStalk_assoc, hm]
    rfl
  · exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk m

private theorem stalk_hom_ext_of_spec (x : M) (A : Type u) [CommRing A] [IsLocalRing A]
    (a₁ a₂ : M.presheaf.stalk x ⟶ CommRingCat.of A) [IsLocalHom a₁.hom] [IsLocalHom a₂.hom]
    (h : Spec.map a₁ ≫ M.fromSpecStalk x = Spec.map a₂ ≫ M.fromSpecStalk x) : a₁ = a₂ := by
  have h1 := (SpecToEquivOfLocalRing M (CommRingCat.of A)).symm.injective
    (a₁ := ⟨x, a₁, inferInstance⟩) (a₂ := ⟨x, a₂, inferInstance⟩) h
  have h2 := (Sigma.mk.inj_iff.1 h1).2
  have h3 := eq_of_heq h2
  exact congrArg Subtype.val h3

end StalkPoints

section StalkLift

variable {k : Type u} [Field k] {C : Scheme.{u}} (sC : C ⟶ Spec (.of k)) (L : C.Modules)
    [IsInvertibleModule C L] {n N : ℕ} (e : Fin N → Γ(L, ⊤)) [IsProper sC] {κ : Type*} (q : κ →
    Γ(coefficientSpace n N k, ⊤)) (Zc : Set (projectiveSpaceOver n (Spec (.of k)))) (hZc : IsClosed
    Zc)

private instance : Mono (finalSpace.toCoefficientSpace (n := n) sC L e q Zc hZc) := by
  unfold finalSpace.toCoefficientSpace
  infer_instance

/-- The coefficients in `A` of an `A`-point of the coefficient space. -/
private def pointCoordinates {A : ArtinLocalAlgebra k} (g : Spec (.of A.carrier) ⟶ coefficientSpace
    n N k) :
    Fin (n + 1) → Fin N → A.carrier :=
  fun i j => (Scheme.ΓSpecIso (.of A.carrier)).hom (g.appTop (coefficientCoord n N k i j))

private theorem eq_coefficientPoint_pointCoordinates {A : ArtinLocalAlgebra k}
    (g : Spec (.of A.carrier) ⟶ coefficientSpace n N k)
    (hg : g ≫ coefficientSpaceOver n N k = (artinStructMap A)) :
    g = (artinCoefficientPoint A) (pointCoordinates g) := by
  have h := eq_tuplePoint g
  rw [hg] at h
  refine h.trans ?_
  unfold artinCoefficientPoint pointCoordinates
  congr 1
  funext i j
  exact (Scheme.ΓSpecIso (.of A.carrier)).hom_inv_id_apply _ |>.symm ▸ rfl

end StalkLift

section StalkLiftAbstract

variable {k : Type u} [Field k] {n N : ℕ} {M : Scheme.{u}} (sM : M ⟶ Spec (.of k)) (toC : M ⟶
    coefficientSpace n N k) [Mono toC] (hover : toC ≫ coefficientSpaceOver n N k = sM)

include hover in
/-- **Lifting local-ring maps along a surjection of Artinian algebras (the universal property of
the stalk of `M` at `[f]`).** Let `M` be a `k`-scheme with a monomorphism `toC` to the coefficient
space whose `A'`-points are the tuples `c'` in `A'` reducing to `a₀` and satisfying a condition
`good` (the closed conditions), `m₀` the `k`-point of `M` over `a₀`, `R = 𝒪_{M,x}` the stalk at
its image, `a : R → A` a `k`-algebra map (an `A`-point of `M` at `x`), and `π : A' → A` a map of
local Artinian algebras. Any good tuple `c'` in `A'` lifting the coefficients of `a` along `π`
determines a `k`-algebra map `b : R → A'` with `π ∘ b = a`. -/
private theorem exists_stalk_lift_abstract (a₀ : Fin (n + 1) → Fin N → k)
    (m₀ : Spec (.of k) ⟶ M) (hm₀ : m₀ ≫ sM = 𝟙 _)
    (hm₀c : m₀ ≫ toC = coefficientPoint (n := n) (N := N) a₀)
    (good : ∀ A' : ArtinLocalAlgebra k, (Fin (n + 1) → Fin N → A'.carrier) → Prop)
    (hlift : ∀ (A' : ArtinLocalAlgebra k) (c' : Fin (n + 1) → Fin N → A'.carrier),
      (∀ i j, (artinToResidue A') (c' i j) = a₀ i j) → good A' c' →
        ∃ m : Spec (.of A'.carrier) ⟶ M, m ≫ toC = (artinCoefficientPoint A') c')
    (x : M) (hx : m₀ (IsLocalRing.closedPoint (CommRingCat.of k)) = x)
    (A A' : ArtinLocalAlgebra k) (π : A'.carrier →ₐ[k] A.carrier)
    (a : M.presheaf.stalk x →+* A.carrier)
    (ha : a.comp (stalkAlgebraMap sM x) = algebraMap k A.carrier)
    (c' : Fin (n + 1) → Fin N → A'.carrier)
    (hc' : ∀ i j, π (c' i j) = pointCoordinates (n := n) (N := N) (A := A)
      (Spec.map (CommRingCat.ofHom a) ≫ M.fromSpecStalk x ≫ toC) i j)
    (hgood : good A' c') :
    ∃ b : M.presheaf.stalk x →+* A'.carrier,
      b.comp (stalkAlgebraMap sM x) = algebraMap k A'.carrier ∧ π.toRingHom.comp b = a := by
  have hloc_a := isLocalHom_stalk_of_comp sM x A a ha
  have hu_over : Spec.map (CommRingCat.ofHom a) ≫ M.fromSpecStalk x ≫ sM = (artinStructMap A) :=
    specMap_fromSpecStalk_comp_over sM x A a ha
  have hu_toC_over : (Spec.map (CommRingCat.ofHom a) ≫ M.fromSpecStalk x ≫ toC) ≫
      coefficientSpaceOver n N k = (artinStructMap A) := by
    rw [Category.assoc, Category.assoc, hover, hu_over]
  have h3 := eq_coefficientPoint_pointCoordinates _ hu_toC_over
  have h4 : (artinClosedPoint A) ≫ Spec.map (CommRingCat.ofHom a) ≫ M.fromSpecStalk x = m₀ :=
    closedPoint_comp_specMap_fromSpecStalk sM m₀ hm₀ x hx A a ha
  have h5 : (artinClosedPoint A) ≫ (artinCoefficientPoint A) (pointCoordinates
      (Spec.map (CommRingCat.ofHom a) ≫ M.fromSpecStalk x ≫ toC)) =
      coefficientPoint (n := n) (N := N) a₀ := by
    rw [← h3]
    calc (artinClosedPoint A) ≫ Spec.map (CommRingCat.ofHom a) ≫ M.fromSpecStalk x ≫ toC
        = ((artinClosedPoint A) ≫ Spec.map (CommRingCat.ofHom a) ≫ M.fromSpecStalk x) ≫ toC := by
          simp only [Category.assoc]
      _ = m₀ ≫ toC := by rw [h4]
      _ = _ := hm₀c
  have h6 := (artinToResidue_eq_of_closedPoint_comp A) _ a₀ h5
  have hres : ∀ i j, (artinToResidue A') (c' i j) = a₀ i j := by
    intro i j
    rw [← (algHom_eq_of_local' _ _ : (artinToResidue A).comp π = artinToResidue A')]
    change (artinToResidue A) (π (c' i j)) = _
    rw [hc']
    exact h6 i j
  obtain ⟨m', hm'⟩ := hlift A' c' hres hgood
  have hm'over : m' ≫ sM = (artinStructMap A') := by
    rw [← hover, ← Category.assoc, hm']
    exact tuplePoint_over _ _
  have hm'pt : m' (IsLocalRing.closedPoint A'.carrier) = x := by
    obtain ⟨y, hy⟩ := (artinClosedPoint_surjective A') (IsLocalRing.closedPoint A'.carrier)
    have e1 : toC (m' (IsLocalRing.closedPoint A'.carrier)) =
        coefficientPoint (n := n) (N := N) a₀ y := by
      rw [← hy]
      have := (artinClosedPoint_comp_coefficientPoint A') c' a₀ hres
      rw [← this, ← hm']
      rfl
    have e2 : toC x = coefficientPoint (n := n) (N := N) a₀ y := by
      rw [← hx, Subsingleton.elim y (IsLocalRing.closedPoint (CommRingCat.of k)), ← hm₀c]
      rfl
    exact Scheme.Hom.injective toC (e1.trans e2.symm)
  obtain ⟨b, hbloc, hbalg, hbm⟩ := exists_stalk_hom_of_spec sM A' m' hm'over x hm'pt
  refine ⟨b, hbalg, ?_⟩
  have hπ : Spec.map (CommRingCat.ofHom π.toRingHom) ≫ m' =
      Spec.map (CommRingCat.ofHom a) ≫ M.fromSpecStalk x := by
    rw [← cancel_mono toC, Category.assoc, hm', Category.assoc, h3,
      artinSpecMap_comp_coefficientPoint A A' π c']
    congr 1
    funext i j
    exact hc' i j
  have hlocπb : IsLocalHom (π.toRingHom.comp b) := by
    haveI := isLocalHom_of_algHom π (artinToResidue A)
    exact inferInstance
  have hext := @stalk_hom_ext_of_spec M x A.carrier _ _ (CommRingCat.ofHom (π.toRingHom.comp b))
    (CommRingCat.ofHom a) hlocπb hloc_a (by
      have e : CommRingCat.ofHom (π.toRingHom.comp b) =
          CommRingCat.ofHom b ≫ CommRingCat.ofHom π.toRingHom := rfl
      refine (congrArg (fun r => Spec.map r ≫ M.fromSpecStalk x) e).trans ?_
      rw [Spec.map_comp, Category.assoc, hbm]
      exact hπ)
  exact congrArg CommRingCat.Hom.hom hext

end StalkLiftAbstract

section StalkLiftFinal

variable {k : Type u} [Field k] {C : Scheme.{u}} (sC : C ⟶ Spec (.of k)) (L : C.Modules)
    [IsInvertibleModule C L] {n N : ℕ} (e : Fin N → Γ(L, ⊤)) [IsProper sC] {κ : Type*} (q : κ →
    Γ(coefficientSpace n N k, ⊤)) (Zc : Set (projectiveSpaceOver n (Spec (.of k)))) (hZc : IsClosed
    Zc)

/-- **The stalk of the coefficient space `M` at `[f]` lifts `A`-points along surjections.** Let
`f : C ⟶ ℙⁿ_k` avoid `Zc`, `f^* 𝒪(1) ≅ L` carrying `f^* Tᵢ` to `τᵢ = Σⱼ a₀ᵢⱼ eⱼ`, and `m₀` the
`k`-point of `M` over `a₀`. For `R = 𝒪_{M, m₀}`, a `k`-algebra map `a : R → A` into a local
Artinian algebra, and `π : A' → A`, every tuple `c'` of coefficients in `A'` that lifts the
coefficients of `a` along `π` and satisfies the closed conditions `q` (the equations, the
proportionality at the marked points and the normalization) gives a `k`-algebra map `b : R → A'`
with `π ∘ b = a`. -/
private theorem exists_stalk_lift_finalSpace (a₀ : Fin (n + 1) → Fin N → k)
    (f : C ⟶ projectiveSpaceOver n (Spec (.of k)))
    (hf : f ≫ pullback.fst (terminal.from (Spec (.of k)))
      (terminal.from (projectiveSpaceAtUniverse.{u} n)) = sC)
    (l : (Scheme.Modules.pullback (f ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of
        k)))).obj
      (twistingSheafAtUniverse.{u} n) ⟶ L) [IsIso l]
    (hτ : ∀ i, l.app ⊤ (pullbackCoordSection.{u}
        (f ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) i) =
      ∑ j, sC.appTop ((Scheme.ΓSpecIso (.of k)).inv (a₀ i j)) • e j)
    (hZ : ∀ x : C, f.base x ∉ Zc)
    (m₀ : Spec (.of k) ⟶ finalSpace (n := n) sC L e q Zc hZc)
    (hm₀ : m₀ ≫ finalSpace.over (n := n) sC L e q Zc hZc = 𝟙 _)
    (hm₀c : m₀ ≫ finalSpace.toCoefficientSpace (n := n) sC L e q Zc hZc =
      coefficientPoint (n := n) (N := N) a₀)
    (x : finalSpace (n := n) sC L e q Zc hZc)
    (hx : m₀ (IsLocalRing.closedPoint (CommRingCat.of k)) = x)
    (A A' : ArtinLocalAlgebra k) (π : A'.carrier →ₐ[k] A.carrier)
    (a : (finalSpace (n := n) sC L e q Zc hZc).presheaf.stalk x →+* A.carrier)
    (ha : a.comp (stalkAlgebraMap (finalSpace.over (n := n) sC L e q Zc hZc) x) =
      algebraMap k A.carrier)
    (c' : Fin (n + 1) → Fin N → A'.carrier)
    (hc' : ∀ i j, π (c' i j) = pointCoordinates (n := n) (N := N) (A := A)
      (Spec.map (CommRingCat.ofHom a) ≫ (finalSpace (n := n) sC L e q Zc hZc).fromSpecStalk x ≫
        finalSpace.toCoefficientSpace (n := n) sC L e q Zc hZc) i j)
    (hq : ∀ i, ((artinCoefficientPoint A') c').appTop (q i) = 0) :
    ∃ b : (finalSpace (n := n) sC L e q Zc hZc).presheaf.stalk x →+* A'.carrier,
      b.comp (stalkAlgebraMap (finalSpace.over (n := n) sC L e q Zc hZc) x) =
        algebraMap k A'.carrier ∧ π.toRingHom.comp b = a :=
  exists_stalk_lift_abstract (finalSpace.over (n := n) sC L e q Zc hZc)
    (finalSpace.toCoefficientSpace (n := n) sC L e q Zc hZc)
    (finalSpace.toCoefficientSpace_over (n := n) sC L e q Zc hZc) a₀ m₀ hm₀ hm₀c
    (fun A' c' => ∀ i, ((artinCoefficientPoint A') c').appTop (q i) = 0)
    (fun A' c' hres hgood => (exists_lift_finalSpace_artin_iff sC L e q Zc hZc A' a₀ f hf l hτ hZ
      c' hres).2 hgood) x hx A A' π a ha c' hc' hq

end StalkLiftFinal

section StalkPointGood

variable {k : Type u} [Field k] {C : Scheme.{u}} (sC : C ⟶ Spec (.of k)) (L : C.Modules)
    [IsInvertibleModule C L] {n N : ℕ} (e : Fin N → Γ(L, ⊤)) [IsProper sC] {κ : Type*} (q : κ →
    Γ(coefficientSpace n N k, ⊤)) (Zc : Set (projectiveSpaceOver n (Spec (.of k)))) (hZc : IsClosed
    Zc)

/-- The coefficients of the `A`-point of `M` defined by a map `a : 𝒪_{M,x} → A`. -/
private def stalkPointCoeff (x : finalSpace (n := n) sC L e q Zc hZc) {A : ArtinLocalAlgebra k}
    (a : (finalSpace (n := n) sC L e q Zc hZc).presheaf.stalk x →+* A.carrier) :
    Fin (n + 1) → Fin N → A.carrier :=
  pointCoordinates (n := n) (N := N) (A := A)
    (Spec.map (CommRingCat.ofHom a) ≫ (finalSpace (n := n) sC L e q Zc hZc).fromSpecStalk x ≫
      finalSpace.toCoefficientSpace (n := n) sC L e q Zc hZc)

/-- **The coefficients of an `A`-point of `M` satisfy the closed conditions.** -/
private theorem stalkPointCoeff_mem_conditions (a₀ : Fin (n + 1) → Fin N → k)
    (f : C ⟶ projectiveSpaceOver n (Spec (.of k)))
    (hf : f ≫ pullback.fst (terminal.from (Spec (.of k)))
      (terminal.from (projectiveSpaceAtUniverse.{u} n)) = sC)
    (l : (Scheme.Modules.pullback (f ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of
        k)))).obj
      (twistingSheafAtUniverse.{u} n) ⟶ L) [IsIso l]
    (hτ : ∀ i, l.app ⊤ (pullbackCoordSection.{u}
        (f ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) i) =
      ∑ j, sC.appTop ((Scheme.ΓSpecIso (.of k)).inv (a₀ i j)) • e j)
    (hZ : ∀ x : C, f.base x ∉ Zc)
    (m₀ : Spec (.of k) ⟶ finalSpace (n := n) sC L e q Zc hZc)
    (hm₀ : m₀ ≫ finalSpace.over (n := n) sC L e q Zc hZc = 𝟙 _)
    (hm₀c : m₀ ≫ finalSpace.toCoefficientSpace (n := n) sC L e q Zc hZc =
      coefficientPoint (n := n) (N := N) a₀)
    (x : finalSpace (n := n) sC L e q Zc hZc)
    (hx : m₀ (IsLocalRing.closedPoint (CommRingCat.of k)) = x)
    (A : ArtinLocalAlgebra k)
    (a : (finalSpace (n := n) sC L e q Zc hZc).presheaf.stalk x →+* A.carrier)
    (ha : a.comp (stalkAlgebraMap (finalSpace.over (n := n) sC L e q Zc hZc) x) =
      algebraMap k A.carrier) :
    ∀ t, ((artinCoefficientPoint A) (stalkPointCoeff sC L e q Zc hZc x a)).appTop (q t) = 0 := by
  set g := Spec.map (CommRingCat.ofHom a) ≫ (finalSpace (n := n) sC L e q Zc hZc).fromSpecStalk x ≫
      finalSpace.toCoefficientSpace (n := n) sC L e q Zc hZc with hg_def
  have hg : g ≫ coefficientSpaceOver n N k = artinStructMap A := by
    simp only [g, Category.assoc, finalSpace.toCoefficientSpace_over]
    exact specMap_fromSpecStalk_comp_over _ x A a ha
  have hge := eq_coefficientPoint_pointCoordinates g hg
  have hcl : artinClosedPoint A ≫ g = coefficientPoint (n := n) (N := N) a₀ := by
    rw [hg_def, ← Category.assoc, ← Category.assoc,
      Category.assoc (artinClosedPoint A),
      closedPoint_comp_specMap_fromSpecStalk _ m₀ hm₀ x hx A a ha, hm₀c]
  have hres := artinToResidue_eq_of_closedPoint_comp A (pointCoordinates g) a₀
    (by rw [← hge]; exact hcl)
  refine (exists_lift_finalSpace_artin_iff sC L e q Zc hZc A a₀ f hf l hτ hZ _ hres).1
    ⟨Spec.map (CommRingCat.ofHom a) ≫ (finalSpace (n := n) sC L e q Zc hZc).fromSpecStalk x, ?_⟩
  refine Eq.trans ?_ hge
  simp only [g, Category.assoc]

end StalkPointGood

/-- **A constant at an `A`-point**: the constant function `r` evaluated at the tuple `c`. -/
private theorem appTop_artinCoefficientPoint_constFunction {k : Type u} [Field k] {n N : ℕ}
    (A : ArtinLocalAlgebra k) (c : Fin (n + 1) → Fin N → A.carrier) (r : k) :
    ((artinCoefficientPoint A) c).appTop (constFunction n N k r) =
      (Scheme.ΓSpecIso (.of A.carrier)).inv (algebraMap k A.carrier r) := by
  unfold constFunction
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
  unfold artinCoefficientPoint
  rw [tuplePoint_over]
  unfold artinStructMap
  exact (ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k A.carrier))) r).symm

/-- **A linear form at an `A`-point**: `Σ μ_{ij} x_{ij}` evaluated at the tuple `c`. -/
private theorem appTop_artinCoefficientPoint_linearFunction {k : Type u} [Field k] {n N : ℕ}
    (A : ArtinLocalAlgebra k) (c : Fin (n + 1) → Fin N → A.carrier) (μ : Fin (n + 1) → Fin N → k) :
    ((artinCoefficientPoint A) c).appTop (linearFunction n N k μ) =
      (Scheme.ΓSpecIso (.of A.carrier)).inv (∑ i, ∑ j, algebraMap k A.carrier (μ i j) * c i j) := by
  unfold linearFunction
  simp only [map_sum, map_mul, appTop_artinCoefficientPoint_constFunction]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [artinCoefficientPoint, tuplePoint_appTop_coord]

/-- **The normalization at an `A`-point**: `μ - 1` evaluated at the tuple `c`. -/
private theorem appTop_artinCoefficientPoint_normalizationFunction {k : Type u} [Field k] {n N : ℕ}
    (A : ArtinLocalAlgebra k) (c : Fin (n + 1) → Fin N → A.carrier) (μ : Fin (n + 1) → Fin N → k) :
    ((artinCoefficientPoint A) c).appTop (normalizationFunction n N k μ) =
      (Scheme.ΓSpecIso (.of A.carrier)).inv
        (∑ i, ∑ j, algebraMap k A.carrier (μ i j) * c i j - 1) := by
  unfold normalizationFunction
  rw [map_sub, appTop_artinCoefficientPoint_linearFunction,
    appTop_artinCoefficientPoint_constFunction, map_one, map_sub, map_one]

/-- **The normalization at an `A`-point**: the vanishing of `μ - 1` at the tuple `c`. -/
private theorem sum_mul_eq_one_of_normalizationFunction {k : Type u} [Field k] {n N : ℕ}
    (A : ArtinLocalAlgebra k) (c : Fin (n + 1) → Fin N → A.carrier) (μ : Fin (n + 1) → Fin N → k)
    (h : ((artinCoefficientPoint A) c).appTop (normalizationFunction n N k μ) = 0) :
    ∑ i, ∑ j, algebraMap k A.carrier (μ i j) * c i j = 1 := by
  rw [appTop_artinCoefficientPoint_normalizationFunction] at h
  have h' := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of A.carrier)).inv).1
    (h.trans (map_zero _).symm)
  exact sub_eq_zero.1 h'

private theorem normalizationFunction_eq_zero_of_sum_mul_eq_one {k : Type u} [Field k] {n N : ℕ}
    (A : ArtinLocalAlgebra k) (c : Fin (n + 1) → Fin N → A.carrier) (μ : Fin (n + 1) → Fin N → k)
    (h : ∑ i, ∑ j, algebraMap k A.carrier (μ i j) * c i j = 1) :
    ((artinCoefficientPoint A) c).appTop (normalizationFunction n N k μ) = 0 := by
  rw [appTop_artinCoefficientPoint_normalizationFunction, h, sub_self, map_zero]

section Assembly

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

/-- **`U` is open in a closed subscheme of projective space.** A quasi-projective `k`-variety has a
quasi-compact immersion into `ℙᵈ_k` over `k`, which factors as an open immersion into a closed
subscheme. -/
private theorem exists_openImmersion_closedImmersion (k : Type u) [Field k] {U : Scheme.{u}}
    (sU : U ⟶ Spec (.of k)) [IsQuasiProjectiveVariety k sU] :
    ∃ (d : ℕ) (Z : Scheme.{u}) (i : Z ⟶ projectiveSpaceOverRing d (CommRingCat.of k))
      (j : U ⟶ Z), IsClosedImmersion i ∧ IsOpenImmersion j ∧
      j ≫ i ≫ pullback.fst (terminal.from (Spec (.of k)))
        (terminal.from (projectiveSpaceAtUniverse.{u} d)) = sU := by
  obtain ⟨d, ι, h1, h2, h3⟩ :=
    ((isQuasiProjectiveVariety_iff_isHQuasiProjective k sU).1 inferInstance).2
  haveI := h2
  obtain ⟨Z, g₁, g₂, hg₁, hg₂, hg⟩ :=
    (IsImmersion.isImmersion_iff_exists_of_quasiCompact (f := ι)).1 h1
  refine ⟨d, Z, g₂, g₁, hg₂, hg₁, ?_⟩
  rwa [← Category.assoc, hg]

/-- A nonempty scheme proper over an algebraically closed field has a `k`-point. -/
private theorem exists_section_of_isProper {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (sC : C ⟶ Spec (.of k)) [QuasiCompact sC] [LocallyOfFiniteType sC] [Nonempty C] :
    ∃ P : Spec (.of k) ⟶ C, P ≫ sC = 𝟙 _ := by
  haveI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace sC
  obtain ⟨x, -, hx⟩ := (isClosed_univ (X := C)).exists_closed_singleton Set.univ_nonempty
  exact ⟨_, ((pointEquivClosedPoint sC).symm ⟨x, hx⟩).2⟩

variable {k : Type u} [Field k] {C : Scheme.{u}} (sC : C ⟶ Spec (.of k)) (L : C.Modules)
    [IsInvertibleModule C L] {n N : ℕ} (e : Fin N → Γ(L, ⊤))

/-- **Marked-point data for any number of marked points**, given one `k`-point `P₀` of `C`
(used only for the normalizing functional when there are no marked points). -/
private theorem exists_marked_points_data_of_point {ιB : Type}
    (f : C ⟶ projectiveSpaceOver n (Spec (.of k)))
    (l : (Scheme.Modules.pullback (f ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of
        k)))).obj
      (twistingSheafAtUniverse.{u} n) ⟶ L) [IsIso l] (a : Fin (n + 1) → Fin N → k)
    (hτ : ∀ i, l.app ⊤ (pullbackCoordSection.{u}
        (f ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) i) =
      ∑ j, sC.appTop ((Scheme.ΓSpecIso (.of k)).inv (a i j)) • e j)
    (P : ιB → (Spec (.of k) ⟶ C)) (hP : ∀ β, P β ≫ sC = 𝟙 _)
    (P₀ : Spec (.of k) ⟶ C) (hP₀ : P₀ ≫ sC = 𝟙 _) :
    ∃ (ℓ : ιB → Fin N → k) (v : ∀ β, Γ((Scheme.Modules.pullback (P β)).obj L, ⊤))
      (c : ιB → Fin (n + 1) → k) (μ : Fin (n + 1) → Fin N → k),
      (∀ β j, AlgebraicGeometry.pullbackGlobalSections (P β) L (e j) =
        (Scheme.ΓSpecIso (.of k)).inv (ℓ β j) • v β) ∧
      (∀ β i, c β i = ∑ j, ℓ β j * a i j) ∧
      (∀ β i i', (∑ j, ℓ β j * a i j) * c β i' = (∑ j, ℓ β j * a i' j) * c β i) ∧
      ∑ i, ∑ j, μ i j * a i j = 1 := by
  by_cases h : Nonempty ιB
  · obtain ⟨ℓ, v, c, μ, h1, h2, h3, -, h5⟩ := exists_marked_points_data sC L e f l a hτ P hP
    exact ⟨ℓ, v, c, μ, h1, h2, h3, h5⟩
  · rw [not_nonempty_iff] at h
    obtain ⟨ℓ₀, v₀, c₀, -, h₂, -, i₀, hi₀⟩ := exists_marked_point_data sC L e f l a hτ P₀ hP₀
    obtain ⟨μ, hμ⟩ := exists_normalizing_functional a
      (exists_ne_zero_of_sum_ne_zero a ℓ₀ ⟨i₀, by rwa [h₂] at hi₀⟩)
    exact ⟨isEmptyElim, isEmptyElim, isEmptyElim, μ, isEmptyElim, isEmptyElim, isEmptyElim, hμ⟩

/-- **The substituted equations of `Z` vanish at `[f]`.** If `f : C ⟶ ℙⁿ_k` factors
through the closed subscheme `Z` whose homogeneous ideal is generated by the forms `F_α`, the
coefficient functions of the substituted equations vanish at the `k`-point of the tuple of `f`. -/
private theorem equationFunctions_coefficientPoint_eq_zero [IsProper sC]
    (w : letI := baseModule sC L ⊤; Module.Basis (Fin N) Γ(Spec (.of k), ⊤) Γ(L, ⊤))
    (f : C ⟶ projectiveSpaceOver n (Spec (.of k)))
    (hf : f ≫ pullback.fst (terminal.from (Spec (.of k)))
      (terminal.from (projectiveSpaceAtUniverse.{u} n)) = sC)
    (l : (Scheme.Modules.pullback (f ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of
        k)))).obj
      (twistingSheafAtUniverse.{u} n) ⟶ L) [IsIso l] (a : Fin (n + 1) → Fin N → k)
    (hτ : ∀ i, l.app ⊤ (pullbackCoordSection.{u}
        (f ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) i) =
      ∑ j, sC.appTop ((Scheme.ΓSpecIso (.of k)).inv (a i j)) • w j)
    {Z : Scheme.{u}} (i : Z ⟶ AlgebraicGeometry.projectiveSpaceOverRing n (CommRingCat.of k))
    [IsClosedImmersion i] (g : C ⟶ Z) (hg : g ≫ i = f)
    {ιE : Type} (F : ιE → MvPolynomial (Fin (n + 1)) k) (d : ιE → ℕ) {N' : ιE → ℕ}
    (w' : ∀ α, letI := baseModule sC (Stacks.TensorPowers.natTensorPow L (d α)) ⊤;
      Module.Basis (Fin (N' α)) Γ(Spec (.of k), ⊤)
        Γ(Stacks.TensorPowers.natTensorPow L (d α), ⊤))
    (hF : ∀ α, (F α).IsHomogeneous (d α))
    (hJ : (closedSubschemeIdeal i).toIdeal = Ideal.span (Set.range F)) :
    ∀ α j, (coefficientPoint (n := n) (N := N) a).appTop
      (equationFunctions (n := n) sC L w (d α) (w' α) (F α) j) = 0 := by
  intro α
  set g₀ := coefficientPoint (n := n) (N := N) a with hg₀
  have ha := coefficientPoint_mem_noCommonZeroOpen (e := w) sC L a f l hτ
  have hs := generatesStalks_familySection (L := L) (e := w) (sC := sC) g₀ ha
  obtain ⟨p, hp, αp, hαiso, hαp⟩ :=
    exists_familyMap_iso_pullback_twistingSheaf (L := L) (e := w) (sC := sC) g₀ ha
  haveI := hαiso
  have hp1 := familyMap_coefficientPoint_eq (L := L) (e := w) (sC := sC) a g₀ rfl ha f hf l hτ
    p hp (asIso αp) hαp
  have hp2 := eq_toProjectiveSpaceOver_of_pinned _ hs _ p hp αp hαp
  have hlift : ∃ ψ : pullback sC (g₀ ≫ coefficientSpaceOver n N k) ⟶ Z,
      ψ ≫ i = toProjectiveSpaceOver (familySection (n := n) (N := N) (L := L) (e := w) (sC := sC)
          g₀)
        hs (pullback.fst sC (g₀ ≫ coefficientSpaceOver n N k) ≫ sC) :=
    ⟨(familyPullbackMap (n := n) (N := N) (sC := sC) g₀ ≫ pullback.fst sC _) ≫ g, by
      rw [← hp2, hp1, Category.assoc, hg]⟩
  have hchart := (exists_lift_closedImmersion_iff _ _ i hs).1 hlift
  have hFα : F α ∈ (closedSubschemeIdeal i).toIdeal := by
    rw [hJ]
    exact Ideal.subset_span ⟨α, rfl⟩
  have e1 : familyPullbackMap (n := n) (N := N) (sC := sC) g₀ ≫
      (pullback.fst sC (coefficientSpaceOver n N k) ≫ sC) =
      pullback.fst sC (g₀ ≫ coefficientSpaceOver n N k) ≫ sC := by
    rw [← Category.assoc, familyPullbackMap_fst]
  exact equationFunctions_eq_zero_of_pullSection sC L w g₀ (d α) (w' α) (F α)
    (pullSection_eq_zero_of_chartEval_pullback _ _ _ _ (hF α) hs e1 fun r => hchart r _ hFα)

/-- **`Φ|_{[f]} = f` on `M`.** The family of `M` restricted along the `k`-point lying
over the coefficients `a` of the tuple of `f` is `f`. -/
private theorem lift_comp_finalFamily_eq [IsProper sC] {κ : Type*}
    (q : κ → Γ(coefficientSpace n N k, ⊤))
    (Zc : Set (projectiveSpaceOver n (Spec (.of k)))) (hZc : IsClosed Zc)
    (a : Fin (n + 1) → Fin N → k)
    (f : C ⟶ projectiveSpaceOver n (Spec (.of k)))
    (hf : f ≫ pullback.fst (terminal.from (Spec (.of k)))
      (terminal.from (projectiveSpaceAtUniverse.{u} n)) = sC)
    (l : (Scheme.Modules.pullback (f ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of
        k)))).obj
      (twistingSheafAtUniverse.{u} n) ⟶ L) [IsIso l]
    (hτ : ∀ i, l.app ⊤ (pullbackCoordSection.{u}
        (f ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) i) =
      ∑ j, sC.appTop ((Scheme.ΓSpecIso (.of k)).inv (a i j)) • e j)
    (m : Spec (.of k) ⟶ finalSpace (n := n) sC L e q Zc hZc)
    (hm : m ≫ finalSpace.over (n := n) sC L e q Zc hZc = 𝟙 (Spec (.of k)))
    (hma : m ≫ finalSpace.toCoefficientSpace (n := n) sC L e q Zc hZc =
      coefficientPoint (n := n) (N := N) a) :
    pullback.lift (𝟙 C) (sC ≫ m) (by simp [hm]) ≫ finalFamily (n := n) sC L e q Zc hZc = f := by
  obtain ⟨m₁, hm₁def⟩ : ∃ m₁ : Spec (.of k) ⟶ noCommonZeroScheme (n := n) sC L e,
      m₁ = m ≫ finalSpace.ι (n := n) sC L e q Zc hZc ≫
        closedNoCommonZeroScheme.toNoCommonZero (n := n) sC L e q := ⟨_, rfl⟩
  have hm₁ : m₁ ≫ noCommonZeroScheme.ι (n := n) sC L e = coefficientPoint (n := n) (N := N) a := by
    rw [hm₁def, Category.assoc, Category.assoc, closedNoCommonZeroScheme.toNoCommonZero_ι]
    exact hma
  have hm₁o : m₁ ≫ noCommonZeroScheme.ι (n := n) sC L e ≫ coefficientSpaceOver n N k = 𝟙 _ := by
    rw [← Category.assoc, hm₁, coefficientPoint_over]
  have key := noCommonZeroFamily_base_change_eq (n := n) (N := N) (L := L) (e := e) (sC := sC)
    a f hf l hτ m₁ hm₁
  let t : C ⟶ pullback sC (m₁ ≫ noCommonZeroScheme.ι (n := n) sC L e ≫ coefficientSpaceOver n N k)
      :=
    pullback.lift (𝟙 C) sC (by rw [hm₁o]; simp)
  have hs : pullback.lift (𝟙 C) (sC ≫ m) (by simp [hm]) ≫ finalFamily (n := n) sC L e q Zc hZc =
      t ≫ familyBaseChange (sC := sC) (noCommonZeroScheme.ι (n := n) sC L e) m₁ ≫
        noCommonZeroFamily (n := n) sC L e := by
    unfold finalFamily closedNoCommonZeroFamily
    simp only [← Category.assoc]
    congr 1
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, familyMapOfHom_fst, familyBaseChange_fst]
      erw [pullback.lift_fst, pullback.lift_fst]
    · simp only [Category.assoc, familyMapOfHom_snd, familyMapOfHom_snd_assoc,
        familyBaseChange_snd]
      erw [pullback.lift_snd_assoc, pullback.lift_snd_assoc]
      rw [hm₁def]
      simp only [Category.assoc]
  rw [hs, key, Category.assoc, familyPullbackMap_fst_assoc]
  have ht : t ≫ pullback.fst sC ((m₁ ≫ noCommonZeroScheme.ι (n := n) sC L e) ≫
      coefficientSpaceOver n N k) = 𝟙 C := pullback.lift_fst _ _ _
  exact ((reassoc_of% ht) f).trans (Category.id_comp f)

/-- **The points of the curve map on charts**: for each `A`-point of `R`, the induced map on the
charts with its coefficients and frames, the closed conditions `Good` from local data, and the
universal property of `R`. These are the fields of a `ChartSystem` beyond the charts, the Čech
comparisons and the trivializations. -/
private structure ChartPoints (k : Type u) [Field k] (R : Type u) [CommRing R] [Algebra k R]
    {ι : Type u} (Ch : CurveCharts k ι) (d N : ℕ) (x : Fin (d + 1) → ∀ i : ι, Ch.S {i})
    (w : ∀ i : ι, Fin N → Ch.O {i}) (μ : Fin (d + 1) → Fin N → k) where
  pt : ∀ {A : ArtinLocalAlgebra k}, (R →ₐ[k] A.carrier) → CurvePoint Ch A
  coeff : ∀ {A : ArtinLocalAlgebra k}, (R →ₐ[k] A.carrier) → Fin (d + 1) → Fin N → A.carrier
  frame : ∀ {A : ArtinLocalAlgebra k} (a : R →ₐ[k] A.carrier) (i : ι),
    ∃ fr : (Ch.O {i} ⊗[k] A.carrier)ˣ, ∀ m,
      ∑ j, w i j ⊗ₜ[k] coeff a m j = fr * (pt a).pt {i} (x m i)
  μ_coeff : ∀ {A : ArtinLocalAlgebra k} (a : R →ₐ[k] A.carrier),
    ∑ m, ∑ j, algebraMap k A.carrier (μ m j) * coeff a m j = 1
  Good : ∀ B : ArtinLocalAlgebra k, (Fin (d + 1) → Fin N → B.carrier) → Prop
  good_of_local : ∀ (B : ArtinLocalAlgebra k) (c : Fin (d + 1) → Fin N → B.carrier)
    (y : ∀ i : ι, Ch.S {i} →ₐ[k] Ch.O {i} ⊗[k] B.carrier)
    (fr : ∀ i : ι, (Ch.O {i} ⊗[k] B.carrier)ˣ),
    (∀ i m, ∑ j, w i j ⊗ₜ[k] c m j = fr i * y i (x m i)) →
    (∀ i z, Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (Ch.𝔟 {i})) (AlgHom.id k _) (y i z) =
      Ideal.Quotient.mk _ (Ch.f0 {i} z) ⊗ₜ[k] 1) →
    ∑ m, ∑ j, algebraMap k B.carrier (μ m j) * c m j = 1 → Good B c
  lift : ∀ {A : ArtinLocalAlgebra k} (E : SmallExtension A) (a : R →ₐ[k] A.carrier)
    (c : Fin (d + 1) → Fin N → E.big.carrier),
    (∀ m j, E.π (c m j) = coeff a m j) → Good E.big c → ∃ b : R →ₐ[k] E.big.carrier, E.π.comp b = a

/-- **The pulled-back coordinates separate the charts**: every point of `C` lies in some
`D₊(f^* T_l)` with `f(x) ∈ D₊(T_l|_U)`. -/
private theorem exists_mem_nvCover_pullbackCoordSection {C U : Scheme.{u}} (f : C ⟶ U) {d : ℕ}
    (gU : U ⟶ projectiveSpaceAtUniverse.{u} d) (gC : C ⟶ projectiveSpaceAtUniverse.{u} d)
    (hg : gC = f ≫ gU)
    [IsInvertibleModule C ((Scheme.Modules.pullback gC).obj (twistingSheafAtUniverse.{u} d))]
    [IsInvertibleModule U ((Scheme.Modules.pullback gU).obj (twistingSheafAtUniverse.{u} d))]
    (x : C) : ∃ l', x ∈ nvCover (pullbackCoordSection.{u} gC) l' ∧
      f.base x ∈ nvCover (pullbackCoordSection.{u} gU) l' := by
  subst hg
  obtain ⟨l', hl'⟩ := exists_mem_nvCover_of_generatesStalks _
    (Stacks.ProjectiveSpaceModuli.taut_generates (f ≫ gU)) x
  refine ⟨l', hl', ?_⟩
  change x ∈ nonvanishingLocus _ (AlgebraicGeometry.pullbackGlobalSections _ _ _) at hl'
  change f.base x ∈ nonvanishingLocus _ (AlgebraicGeometry.pullbackGlobalSections _ _ _)
  rw [mem_nonvanishingLocus_pullbackGlobalSections_iff] at hl' ⊢
  simpa using hl'

/-- **An affine chart cover adapted to the coordinates.** For `gC = f ≫ gU` there are finitely
many affine opens `U_t ⊆ C` covering `C` and affine opens `W_t ⊆ U` with `f(U_t) ⊆ W_t`, and a
coordinate index `l t` with `U_t ⊆ D₊(gC^* T_{l t})` and `W_t ⊆ D₊(gU^* T_{l t})`. -/
private theorem exists_chartCover_le_nvCover {C U : Scheme.{u}} [CompactSpace C] (f : C ⟶ U)
    {d : ℕ} (gU : U ⟶ projectiveSpaceAtUniverse.{u} d) (gC : C ⟶ projectiveSpaceAtUniverse.{u} d)
    (hg : gC = f ≫ gU)
    [IsInvertibleModule C ((Scheme.Modules.pullback gC).obj (twistingSheafAtUniverse.{u} d))]
    [IsInvertibleModule U ((Scheme.Modules.pullback gU).obj (twistingSheafAtUniverse.{u} d))] :
    ∃ (r : ℕ) (K : CurveMapCharts.ChartCover f (ULift.{u} (Fin r)))
      (l : ULift.{u} (Fin r) → Fin (d + 1)),
      (∀ t, K.UC t ≤ nvCover (pullbackCoordSection.{u} gC) (l t)) ∧
      ∀ t, K.WU t ≤ nvCover (pullbackCoordSection.{u} gU) (l t) := by
  obtain ⟨r, l, UC, WU, hUCa, hWUa, hle, hUCσ, hWUσ, hcov⟩ :=
    CurveMapCharts.exists_affine_chartCover f (nvCover (pullbackCoordSection.{u} gC))
      (nvCover (pullbackCoordSection.{u} gU)) (exists_mem_nvCover_pullbackCoordSection f gU _ hg)
  refine ⟨r,
    { UC := fun t => UC t.down
      WU := fun t => WU t.down
      affC := fun t => hUCa _
      affW := fun t => hWUa _
      le := fun t => hle _
      cover := by
        rw [hcov]
        exact le_antisymm (iSup_le fun t => le_iSup (fun s : ULift.{u} (Fin r) => UC s.down) ⟨t⟩)
          (iSup_le fun t => le_iSup (fun s : Fin r => UC s) t.down) },
    fun t => l t.down, fun t => hUCσ _, fun t => hWUσ _⟩

/-- **The derivations of the charts with values in the ideals of the marked points are the
sections of `f^* T_U(-B)`**, compatibly with restriction. -/
private theorem exists_derivationEquiv_sections (k : Type u) [Field k] [IsAlgClosed k]
    {C U : Scheme.{u}} (sC : C ⟶ Spec (.of k)) (sU : U ⟶ Spec (.of k))
    [IsProjectiveVariety k sC] [IsCurve k sC] [Smooth sC]
    {n : ℕ} [IsQuasiProjectiveVariety k sU] [SmoothOfRelativeDimension n sU] [IsSeparated sU]
    [Smooth sU]
    (f : C ⟶ U) (hf : f ≫ sU = sC)
    {b : ℕ} (P : Fin b → (Spec (.of k) ⟶ C)) (hP : ∀ i, P i ≫ sC = 𝟙 _)
    (hPinj : Function.Injective P)
    [((Scheme.Modules.pullback f).obj (dualSheaf sU.relativeDifferentials)).IsCoherent]
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] (K : CurveMapCharts.ChartCover f ι) :
    ∃ θ : ∀ s : Finset ι, s.Nonempty →
        (Derivation k ((CurveMapCharts.curveCharts sC sU K hf (fun β => (P β).base
            (IsLocalRing.closedPoint k))).S s) ((CurveMapCharts.curveCharts sC sU K hf (fun β => (P
            β).base (IsLocalRing.closedPoint k))).𝔟 s) ≃ₗ[k]
          (CurveMapCharts.sectionsCechPresheaf sC K.UC (markedTangentSheaf sU f P)).obj s),
      ∀ (s t : Finset ι) (h : s ⊆ t) (hs : s.Nonempty) (D : Derivation k
          ((CurveMapCharts.curveCharts sC sU K hf (fun β => (P β).base (IsLocalRing.closedPoint
          k))).S s) ((CurveMapCharts.curveCharts sC sU K hf (fun β => (P β).base
          (IsLocalRing.closedPoint k))).𝔟 s)),
        θ t (hs.mono h) ((CurveMapCharts.curveCharts sC sU K hf (fun β => (P β).base
            (IsLocalRing.closedPoint k))).extDerB h hs D) =
          (CurveMapCharts.sectionsCechPresheaf sC K.UC (markedTangentSheaf sU f P)).res h (θ s hs
              D) := by
  have hvar : IsVariety k sC := inferInstance
  haveI : IsSeparated sC := hvar.toIsSeparated
  haveI : LocallyOfFiniteType sC := hvar.toLocallyOfFiniteType
  haveI := MMP.Fourfold.CurveMapDerivations.isQuasicoherent_relativeDifferentials sU
  haveI := MMP.Fourfold.CurveMapDerivations.isQuasicoherent_dualSheaf_relativeDifferentials sU n
  haveI : ((Scheme.Modules.pullback f).obj (dualSheaf sU.relativeDifferentials)).IsQuasicoherent :=
    isQuasicoherent_of_isCoherent _
  haveI := isClosedImmersion_markedPointsMap P sC hP hPinj
  haveI := MMP.Fourfold.CurveMapDerivations.isQuasicoherent_idealSheafModule
    (markedPointsMap P).ker.subschemeι
  exact MMP.Fourfold.CurveMapDerivations.exists_derivationEquiv_curveCharts sC sU hf K _
    (markedPointsMap P).ker.subschemeι (idealSheafSections_markedPoints P)

/-- **`θ_G`**: the Čech `H¹` of the presheaf of derivations of the charts with values in the ideals
of the marked points is `H¹(C, f^* T_U(-B))`. -/
private theorem nonempty_derivPresheafB_h1Equiv (k : Type u) [Field k] [IsAlgClosed k]
    {C U : Scheme.{u}} (sC : C ⟶ Spec (.of k)) (sU : U ⟶ Spec (.of k))
    [IsProjectiveVariety k sC] [IsCurve k sC] [Smooth sC]
    {n : ℕ} [IsQuasiProjectiveVariety k sU] [SmoothOfRelativeDimension n sU] [IsSeparated sU]
    [Smooth sU]
    (f : C ⟶ U) (hf : f ≫ sU = sC)
    {b : ℕ} (P : Fin b → (Spec (.of k) ⟶ C)) (hP : ∀ i, P i ≫ sC = 𝟙 _)
    (hPinj : Function.Injective P)
    [((Scheme.Modules.pullback f).obj (dualSheaf sU.relativeDifferentials)).IsCoherent]
    {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι] (K : CurveMapCharts.ChartCover f ι) :
    Nonempty ((CurveMapCharts.curveCharts sC sU K hf
        (fun β => (P β).base (IsLocalRing.closedPoint k))).derivPresheafB.H1 ≃ₗ[k]
      cohomologyOverField k sC (markedTangentSheaf sU f P) 1) := by
  classical
  obtain ⟨θ, hθ⟩ := exists_derivationEquiv_sections k sC sU (n := n) f hf P hP hPinj K
  have hvar : IsVariety k sC := inferInstance
  haveI : IsSeparated sC := hvar.toIsSeparated
  obtain ⟨hG, -⟩ := eulerCharacteristic_markedTangentSheaf (n := n) sC sU f P hP hPinj
  haveI : (markedTangentSheaf sU f P).IsQuasicoherent := isQuasicoherent_of_isCoherent _
  let e : NonemptyIso (CurveMapCharts.curveCharts sC sU K hf (fun β => (P β).base
      (IsLocalRing.closedPoint k))).derivPresheafB
      (CurveMapCharts.sectionsCechPresheaf sC K.UC (markedTangentSheaf sU f P)) :=
    { equiv := fun s hs =>
        letI : Unique (PLift s.Nonempty) := ⟨⟨⟨hs⟩⟩, fun _ => rfl⟩
        (LinearEquiv.funUnique (PLift s.Nonempty) k _).trans (θ s hs)
      map_res := fun {s t} h hs x => by
        letI : Unique (PLift s.Nonempty) := ⟨⟨⟨hs⟩⟩, fun _ => rfl⟩
        letI : Unique (PLift t.Nonempty) := ⟨⟨⟨hs.mono h⟩⟩, fun _ => rfl⟩
        change θ t _ ((CurveMapCharts.curveCharts sC sU K hf (fun β => (P β).base
            (IsLocalRing.closedPoint k))).derivPresheafB.res h x ⟨hs.mono h⟩) =
          (CurveMapCharts.sectionsCechPresheaf sC K.UC (markedTangentSheaf sU f P)).res h
            (θ s hs (x ⟨hs⟩))
        rw [← hθ s t h hs]
        congr 1
        exact dif_pos hs }
  exact ⟨e.h1Equiv.trans (CurveMapCharts.cechH1EquivCohomologyOverField sC K.UC _ K.cover
    (fun r s => Stacks.Cech.inter_isAffineOpen sC K.UC K.affC s))⟩

/-- **An `A`-point of `M` at `[f]` on the charts, with its frames.** -/
private theorem exists_curvePoint_frames (k : Type u) [Field k] [IsAlgClosed k]
    {C U : Scheme.{u}} (sC : C ⟶ Spec (.of k)) (sU : U ⟶ Spec (.of k))
    [IsProjectiveVariety k sC] [IsCurve k sC] [Smooth sC]
    {n : ℕ} [IsQuasiProjectiveVariety k sU] [SmoothOfRelativeDimension n sU]
    (f : C ⟶ U) (hf : f ≫ sU = sC)
    {b : ℕ} (P : Fin b → (Spec (.of k) ⟶ C)) (hP : ∀ i, P i ≫ sC = 𝟙 _)
    (hPinj : Function.Injective P)
    [((Scheme.Modules.pullback f).obj (dualSheaf sU.relativeDifferentials)).IsCoherent]
    [(SheafOfModules.unit C.ringCatSheaf).IsCoherent]
    {d : ℕ} {Z : Scheme.{u}} (i : Z ⟶ projectiveSpaceOverRing d (CommRingCat.of k))
    [IsClosedImmersion i] (j : U ⟶ Z) [IsOpenImmersion j]
    (hij : j ≫ i ≫ pullback.fst (terminal.from (Spec (.of k)))
        (terminal.from (projectiveSpaceAtUniverse.{u} d)) = sU)
    [IsInvertibleModule C ((Scheme.Modules.pullback ((f ≫ j ≫ i) ≫
      projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
        (twistingSheafAtUniverse.{u} d))]
    {N : ℕ} (w : letI := baseModule sC ((Scheme.Modules.pullback ((f ≫ j ≫ i) ≫
      projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
        (twistingSheafAtUniverse.{u} d)) ⊤;
      Module.Basis (Fin N) Γ(Spec (.of k), ⊤) Γ((Scheme.Modules.pullback ((f ≫ j ≫ i) ≫
        projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
          (twistingSheafAtUniverse.{u} d), ⊤))
    (a : Fin (d + 1) → Fin N → k)
    (hτ : ∀ i', pullbackCoordSection.{u} ((f ≫ j ≫ i) ≫
        projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k))) i' =
      ∑ j', sC.appTop ((Scheme.ΓSpecIso (.of k)).inv (a i' j')) • w j')
    {ιE : Type} (F : ιE → MvPolynomial (Fin (d + 1)) k) (dd : ιE → ℕ) {N' : ιE → ℕ}
    (w' : ∀ α, letI := baseModule sC (Stacks.TensorPowers.natTensorPow
        ((Scheme.Modules.pullback ((f ≫ j ≫ i) ≫
          projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
          (twistingSheafAtUniverse.{u} d)) (dd α)) ⊤;
      Module.Basis (Fin (N' α)) Γ(Spec (.of k), ⊤)
        Γ(Stacks.TensorPowers.natTensorPow ((Scheme.Modules.pullback ((f ≫ j ≫ i) ≫
          projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
          (twistingSheafAtUniverse.{u} d)) (dd α), ⊤))
    (hhom : ∀ α, (F α).IsHomogeneous (dd α))
    (hJ : (closedSubschemeIdeal i).toIdeal = Ideal.span (Set.range F))
    (ℓ : Fin b → Fin N → k) (c : Fin b → Fin (d + 1) → k) (μ : Fin (d + 1) → Fin N → k)
    (hc : ∀ β i', c β i' = ∑ j', ℓ β j' * a i' j')
    (hμ : ∑ i', ∑ j', μ i' j' * a i' j' = 1)
    (v : ∀ β, Γ((Scheme.Modules.pullback (P β)).obj ((Scheme.Modules.pullback ((f ≫ j ≫ i) ≫
      projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
        (twistingSheafAtUniverse.{u} d)), ⊤))
    (hv : ∀ β j', AlgebraicGeometry.pullbackGlobalSections (P β) ((Scheme.Modules.pullback
      ((f ≫ j ≫ i) ≫ projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
        (twistingSheafAtUniverse.{u} d)) (w j') = (Scheme.ΓSpecIso (.of k)).inv (ℓ β j') • v β)
    (Zc : Set (projectiveSpaceOver d (Spec (.of k)))) (hZc : IsClosed Zc)
    (hZc' : ∀ z : Z, z ∉ Set.range j.base → i.base z ∈ Zc)
    (hZ : ∀ x : C, (f ≫ j ≫ i).base x ∉ Zc)
    (Φ : pullback sC (finalSpace.over (n := d) sC _ w
      (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ) Zc hZc) ⟶ U)
    (hΦ : Φ ≫ j ≫ i = finalFamily (n := d) sC _ w
      (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ) Zc hZc)
    (m : Spec (.of k) ⟶ curveMapSpace (n := d) sC _ w F dd w' ℓ c μ Zc hZc)
    (hm : m ≫ finalSpace.over (n := d) sC _ w
      (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ) Zc hZc = 𝟙 (Spec (.of k)))
    (hma : m ≫ finalSpace.toCoefficientSpace (n := d) sC _ w
      (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ) Zc hZc =
        coefficientPoint (n := d) (N := N) a)
    {ι : Type u} [Fintype ι] [DecidableEq ι] [IsSeparated sU] [Smooth sU]
    (K : CurveMapCharts.ChartCover f ι) (l : ι → Fin (d + 1))
    (hσC : ∀ t, K.UC t ≤ nvCover (pullbackCoordSection.{u} ((f ≫ j ≫ i) ≫
      projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))) (l t))
    [IsInvertibleModule U ((Scheme.Modules.pullback ((j ≫ i) ≫
      projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
        (twistingSheafAtUniverse.{u} d))]
    (hσU : ∀ t, K.WU t ≤ nvCover (pullbackCoordSection.{u} ((j ≫ i) ≫
      projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))) (l t))
    (A : ArtinLocalAlgebra k) :
    letI := MMP.Mori.stalkAlgebra (finalSpace.over (n := d) sC _ w
      (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ) Zc hZc) (m (IsLocalRing.closedPoint k))
    ∀ a' : ((curveMapSpace (n := d) sC _ w F dd w' ℓ c μ Zc hZc).presheaf.stalk
          (m (IsLocalRing.closedPoint k))) →ₐ[k] A.carrier,
      ∃ p : CurvePoint (CurveMapCharts.curveCharts sC sU K hf
          (fun β => (P β).base (IsLocalRing.closedPoint k))) A,
        ∀ t : ι, ∃ fr : ((CurveMapCharts.curveCharts sC sU K hf
            (fun β => (P β).base (IsLocalRing.closedPoint k))).O {t} ⊗[k] A.carrier)ˣ, ∀ m',
          ∑ j', CurveMapCharts.localSection sC sU hf K
              (fun β => (P β).base (IsLocalRing.closedPoint k)) _ l hσC (w j') t ⊗ₜ[k]
            stalkPointCoeff sC _ w (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ) Zc hZc
              (m (IsLocalRing.closedPoint k)) a'.toRingHom m' j' =
          fr * p.pt {t} (CurveMapCharts.chartCoord _ K.WU l hσU m' t) := by
  letI := MMP.Mori.stalkAlgebra (finalSpace.over (n := d) sC _ w
    (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ) Zc hZc) (m (IsLocalRing.closedPoint k))
  intro a'
  classical
  have hvarC : IsVariety k sC := inferInstance
  haveI : IsSeparated sC := hvarC.toIsSeparated
  haveI : IsProper sC := (inferInstance : IsProperVariety k sC).toIsProper
  haveI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace sC
  haveI : QuasiSeparatedSpace C := quasiSeparatedSpace_of_quasiSeparated sC
  have hf' : (f ≫ j ≫ i) ≫ pullback.fst (terminal.from (Spec (.of k)))
      (terminal.from (projectiveSpaceAtUniverse.{u} d)) = sC := by
    rw [Category.assoc, Category.assoc, hij, hf]
  have hτ' : ∀ i', (𝟙 _ : ((Scheme.Modules.pullback ((f ≫ j ≫ i) ≫
      projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
        (twistingSheafAtUniverse.{u} d)) ⟶ ((Scheme.Modules.pullback ((f ≫ j ≫ i) ≫
      projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
        (twistingSheafAtUniverse.{u} d))).app ⊤ (pullbackCoordSection.{u} ((f ≫ j ≫ i) ≫
      projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k))) i') =
      ∑ j', sC.appTop ((Scheme.ΓSpecIso (.of k)).inv (a i' j')) • w j' := hτ
  -- the `A`-point of `M`
  have ha : a'.toRingHom.comp (stalkAlgebraMap (finalSpace.over (n := d) sC _ w
      (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ) Zc hZc) (m (IsLocalRing.closedPoint k))) =
      algebraMap k A.carrier := RingHom.ext a'.commutes
  let mA : Spec (.of A.carrier) ⟶ curveMapSpace (n := d) sC _ w F dd w' ℓ c μ Zc hZc :=
    Spec.map (CommRingCat.ofHom a'.toRingHom) ≫
      (curveMapSpace (n := d) sC _ w F dd w' ℓ c μ Zc hZc).fromSpecStalk
        (m (IsLocalRing.closedPoint k))
  have hmAo : mA ≫ finalSpace.over (n := d) sC _ w
      (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ) Zc hZc = artinStructMap A :=
    specMap_fromSpecStalk_comp_over _ _ A a'.toRingHom ha
  set cA := stalkPointCoeff sC _ w (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ) Zc hZc
    (m (IsLocalRing.closedPoint k)) a'.toRingHom with hcA
  have hg : mA ≫ finalSpace.toCoefficientSpace (n := d) sC _ w
      (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ) Zc hZc = artinCoefficientPoint A cA :=
    eq_coefficientPoint_pointCoordinates _ (by
      rw [Category.assoc, finalSpace.toCoefficientSpace_over]; exact hmAo)
  have hmA : mA ≫ finalSpace.over (n := d) sC _ w
      (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ) Zc hZc =
      artinCoefficientPoint A cA ≫ coefficientSpaceOver d N k := by
    rw [← finalSpace.toCoefficientSpace_over, ← Category.assoc, hg]
  have hgo : artinCoefficientPoint A cA ≫ coefficientSpaceOver d N k =
      specStructMap (k := k) A.carrier := tuplePoint_over _ _
  have H : IsPullback (pullback.fst sC (artinCoefficientPoint A cA ≫ coefficientSpaceOver d N k))
      (pullback.snd sC (artinCoefficientPoint A cA ≫ coefficientSpaceOver d N k)) sC
      (specStructMap (k := k) A.carrier) := by
    rw [← hgo]
    exact IsPullback.of_hasPullback _ _
  -- the family over `Spec A`
  let ΦA := familyMapOfHom sC mA hmA ≫ Φ
  have hΦA : ΦA ≫ sU =
      pullback.fst sC (artinCoefficientPoint A cA ≫ coefficientSpaceOver d N k) ≫ sC := by
    have e1 : Φ ≫ sU = pullback.fst sC (finalSpace.over (n := d) sC _ w
        (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ) Zc hZc) ≫ sC := by
      rw [← hij, ← finalFamily_over, ← hΦ]
      simp only [Category.assoc]
    simp only [ΦA, Category.assoc, e1, familyMapOfHom_fst_assoc]
  have htr : toRes A = artinToResidue A := algHom_eq_of_local' _ _
  have hcl : artinClosedPoint A ≫ specStructMap (k := k) A.carrier = 𝟙 _ :=
    artinClosedPoint_structMap A
  let ιC : C ⟶ pullback sC (artinCoefficientPoint A cA ≫ coefficientSpaceOver d N k) :=
    pullback.lift (𝟙 C) (sC ≫ artinClosedPoint A) (by
      rw [hgo, Category.assoc, hcl, Category.comp_id, Category.id_comp])
  have hιp : ιC ≫ pullback.fst sC (artinCoefficientPoint A cA ≫ coefficientSpaceOver d N k) =
      𝟙 C := pullback.lift_fst _ _ _
  have hιq : ιC ≫ pullback.snd sC (artinCoefficientPoint A cA ≫ coefficientSpaceOver d N k) =
      sC ≫ Spec.map (CommRingCat.ofHom (toRes A).toRingHom) := by
    rw [htr]
    exact pullback.lift_snd _ _ _
  have hιΦ : ιC ≫ ΦA = f := by
    have h1 : ιC ≫ familyMapOfHom sC mA hmA = pullback.lift (𝟙 C) (sC ≫ m) (by simp [hm]) := by
      refine pullback.hom_ext ?_ ?_
      · simpa only [Category.assoc, familyMapOfHom_fst, pullback.lift_fst] using hιp
      · simp only [Category.assoc, familyMapOfHom_snd, pullback.lift_snd]
        have e0 : ιC ≫ pullback.snd sC (artinCoefficientPoint A cA ≫ coefficientSpaceOver d N k) =
            sC ≫ artinClosedPoint A := pullback.lift_snd _ _ _
        rw [reassoc_of% e0]
        exact congrArg (fun φ => sC ≫ φ)
          (closedPoint_comp_specMap_fromSpecStalk _ m hm _ rfl A a'.toRingHom ha)
    have h2 : pullback.lift (𝟙 C) (sC ≫ m) (by simp [hm]) ≫ Φ = f := by
      apply (cancel_mono (j ≫ i)).1
      rw [Category.assoc, hΦ]
      exact lift_comp_finalFamily_eq sC _ w _ Zc hZc a (f ≫ j ≫ i) hf' (𝟙 _) hτ' m hm hma
    simp only [ΦA]
    rw [← Category.assoc, h1, h2]
  haveI : Surjective (artinClosedPoint A) := ⟨artinClosedPoint_surjective A⟩
  have hsurj : ∀ y, ιC.base ((pullback.fst sC
      (artinCoefficientPoint A cA ≫ coefficientSpaceOver d N k)).base y) = y := by
    intro y
    obtain ⟨y', rfl⟩ := (pullback.fst (pullback.snd sC
      (artinCoefficientPoint A cA ≫ coefficientSpaceOver d N k)) (artinClosedPoint A)).surjective y
    have heq : pullback.fst (pullback.snd sC (artinCoefficientPoint A cA ≫
        coefficientSpaceOver d N k)) (artinClosedPoint A) ≫
          pullback.fst sC (artinCoefficientPoint A cA ≫ coefficientSpaceOver d N k) ≫ ιC =
        pullback.fst _ _ := by
      refine pullback.hom_ext ?_ ?_
      · simp only [Category.assoc, hιp, Category.comp_id]
      · simp only [Category.assoc]
        rw [show ιC ≫ pullback.snd sC (artinCoefficientPoint A cA ≫ coefficientSpaceOver d N k) =
          sC ≫ artinClosedPoint A from pullback.lift_snd _ _ _, pullback.condition_assoc,
          pullback.condition_assoc, hgo, reassoc_of% hcl]
        exact pullback.condition.symm
    exact congrArg (fun φ => φ.base y') heq
  have hle := preimage_le_of_section (p := pullback.fst sC
    (artinCoefficientPoint A cA ≫ coefficientSpaceOver d N k)) K ιC hιΦ hsurj
  -- the marked points
  let PA : Fin b → (Spec (.of A.carrier) ⟶
      pullback sC (artinCoefficientPoint A cA ≫ coefficientSpaceOver d N k)) := fun β =>
    pullback.lift (specStructMap (k := k) A.carrier ≫ P β) (𝟙 _) (by
      rw [Category.assoc, hP β, Category.comp_id, Category.id_comp, hgo])
  have hPAp : ∀ β, PA β ≫ pullback.fst sC (artinCoefficientPoint A cA ≫ coefficientSpaceOver d N k)
      =
      specStructMap (k := k) A.carrier ≫ P β := fun β => pullback.lift_fst _ _ _
  have hPAq : ∀ β, PA β ≫ pullback.snd sC (artinCoefficientPoint A cA ≫ coefficientSpaceOver d N k)
      =
      𝟙 _ := fun β => pullback.lift_snd _ _ _
  have hPAΦ : ∀ β, PA β ≫ ΦA = specStructMap (k := k) A.carrier ≫ P β ≫ f := by
    intro β
    have e1 : PA β ≫ familyMapOfHom sC mA hmA = mA ≫ finalSpace.markedMap (n := d) sC _ w
        (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ) Zc hZc (P β) (hP β) := by
      refine pullback.hom_ext ?_ ?_
      · simp only [Category.assoc, familyMapOfHom_fst, hPAp, finalSpace.markedMap,
          pullback.lift_fst]
        rw [reassoc_of% hmAo]
        rfl
      · simp only [Category.assoc, familyMapOfHom_snd, finalSpace.markedMap, pullback.lift_snd,
          Category.comp_id]
        rw [reassoc_of% (hPAq β)]
    have e2 : finalSpace.markedMap (n := d) sC _ w
        (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ) Zc hZc (P β) (hP β) ≫ Φ =
        finalSpace.over (n := d) sC _ w
          (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ) Zc hZc ≫ P β ≫ f := by
      apply (cancel_mono (j ≫ i)).1
      refine (Category.assoc _ _ _).trans ?_
      rw [hΦ]
      refine (curveMapSpace_markedMap_comp_family sC ((Scheme.Modules.pullback ((f ≫ j ≫ i) ≫
      projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
        (twistingSheafAtUniverse.{u} d)) w F dd w' ℓ c μ Zc hZc
        (f ≫ j ≫ i) hf' (𝟙 _) a hτ' β (P β) (hP β) (v β) (hv β) (hc β)).trans ?_
      exact ((Category.assoc _ _ _).trans (congrArg (fun φ => finalSpace.over (n := d) sC _ w
        (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ) Zc hZc ≫ φ)
          (Category.assoc _ _ _))).symm
    simp only [ΦA]
    rw [← Category.assoc, e1, Category.assoc, e2, ← Category.assoc, hmAo]
    rfl
  have hpts : ∀ β (z : Spec (.of k)), (P β).base z = (P β).base (IsLocalRing.closedPoint k) :=
    fun β z => congrArg (P β).base (Subsingleton.elim _ _)
  refine ⟨familyCurvePoint sC sU hf K _ A H ΦA hΦA hle P hP PA hPAp hPAq hPAΦ ιC hιp hιq hιΦ hpts,
    fun t => ?_⟩
  obtain ⟨α, hαiso, hα⟩ := exists_pinned_finalFamily_comp (n := d) sC ((Scheme.Modules.pullback ((f
      ≫ j ≫ i) ≫
      projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
        (twistingSheafAtUniverse.{u} d)) w
    (curveMapConditions (n := d) sC ((Scheme.Modules.pullback ((f ≫ j ≫ i) ≫
      projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
        (twistingSheafAtUniverse.{u} d)) w F dd w' ℓ c μ) Zc hZc mA hmA (𝟙 _)
    (pullback.fst sC (artinCoefficientPoint A cA ≫ coefficientSpaceOver d N k))
    (pullback.snd sC (artinCoefficientPoint A cA ≫ coefficientSpaceOver d N k))
    (Category.id_comp _) (Category.id_comp _) (ΦA ≫ j ≫ i) (by
      rw [Category.id_comp]
      exact (congrArg (fun φ => familyMapOfHom sC mA hmA ≫ φ) hΦ.symm).trans
        (Category.assoc _ _ _).symm)
  haveI := hαiso
  have hcoord : ∀ m' j', (mA ≫ finalSpace.toCoefficientSpace (n := d) sC _ w
      (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ) Zc hZc).appTop
        (coefficientCoord d N k m' j') = (Scheme.ΓSpecIso (.of A.carrier)).inv (cA m' j') := by
    intro m' j'
    rw [hg]
    exact tuplePoint_appTop_coord _ _ m' j'
  exact exists_frames_familyChartMap sC sU hf K _ A H ΦA hΦA hle
    ((f ≫ j ≫ i) ≫ projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))
    ((j ≫ i) ≫ projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k))) l hσC hσU w cA
    ((ΦA ≫ j ≫ i) ≫ projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))
    (by simp only [Category.assoc]) α
    (fun m' => (hα m').trans (congrArg _ (funext fun j' => hcoord m' j'))) t

/-- **The family tuple of an `B`-point in a frame over a chart.** On `p⁻¹ V ⊆ C ×ₖ Spec B`, the
`m`-th section `Σⱼ c'_{m j} wⱼ` of the family of the tuple `c'` is the image of
`Σⱼ (wⱼ / σ) ⊗ c'_{m j}` times the pulled-back frame `σ`. -/
private theorem resT_familySection_eq_smul {k : Type u} [Field k] {C : Scheme.{u}}
    (sC : C ⟶ Spec (.of k)) (L : C.Modules) [IsInvertibleModule C L] {n N : ℕ}
    (w : Fin N → Γ(L, ⊤)) (B : ArtinLocalAlgebra k) (c' : Fin (n + 1) → Fin N → B.carrier)
    (H : IsPullback (pullback.fst sC (artinCoefficientPoint B c' ≫ coefficientSpaceOver n N k))
      (pullback.snd sC (artinCoefficientPoint B c' ≫ coefficientSpaceOver n N k)) sC
      (specStructMap (k := k) B.carrier))
    (σ : Γ(L, ⊤)) {V : C.Opens} (hV : V ≤ nvOpen L σ) (hVc : IsCompact (V : Set C))
    (hVq : IsQuasiSeparated (V : Set C)) (m : Fin (n + 1)) :
    letI := CurveMapCharts.sectionsAlgebra sC V
    resT (pullback.fst sC (artinCoefficientPoint B c' ≫ coefficientSpaceOver n N k) ⁻¹ᵁ V)
        (familySection (n := n) (N := N) (L := L) (e := w) (sC := sC)
          (artinCoefficientPoint B c') m) =
      baseChangeEquiv sC H V hVc hVq (∑ j, div σ hV (resT V (w j)) ⊗ₜ[k] c' m j) •
        resT _ (AlgebraicGeometry.pullbackGlobalSections
          (familyPullbackMap (n := n) (N := N) (sC := sC) (artinCoefficientPoint B c'))
          ((Scheme.Modules.pullback (pullback.fst sC (coefficientSpaceOver n N k))).obj L)
          (AlgebraicGeometry.pullbackGlobalSections (pullback.fst sC (coefficientSpaceOver n N k))
            L σ)) := by
  letI := CurveMapCharts.sectionsAlgebra sC V
  have hW : pullback.fst sC (artinCoefficientPoint B c' ≫ coefficientSpaceOver n N k) ⁻¹ᵁ V ≤
      (familyPullbackMap (n := n) (N := N) (sC := sC) (artinCoefficientPoint B c') ≫
        pullback.fst sC (coefficientSpaceOver n N k)) ⁻¹ᵁ V := by
    rw [familyPullbackMap_fst]
  have hfr := fun j => resT_pullback_pullback_eq_smul
    (familyPullbackMap (n := n) (N := N) (sC := sC) (artinCoefficientPoint B c'))
    (pullback.fst sC (coefficientSpaceOver n N k)) L (w j) σ hV hW
  have happ : ∀ (f f' : pullback sC (artinCoefficientPoint B c' ≫ coefficientSpaceOver n N k) ⟶ C)
      (_ : f = f') (e : pullback.fst sC (artinCoefficientPoint B c' ≫ coefficientSpaceOver n N k)
        ⁻¹ᵁ V ≤ f ⁻¹ᵁ V)
      (e' : pullback.fst sC (artinCoefficientPoint B c' ≫ coefficientSpaceOver n N k) ⁻¹ᵁ V ≤
        f' ⁻¹ᵁ V), f.appLE V _ e = f'.appLE V _ e' := by
    rintro f f' rfl e e'
    rfl
  unfold familySection universalSection Stacks.LinearSystemScheme.coordSection
  rw [map_sum, resT_sum, map_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_smul, resT_smul, hfr j, smul_smul,
    baseChangeEquiv_tmul, mul_comm]
  congr 1
  congr 1
  · exact ConcreteCategory.congr_hom (happ _ _ (familyPullbackMap_fst (n := n) (N := N) (sC := sC)
      (artinCoefficientPoint B c')) hW le_rfl) _
  · have e1 : (familyPullbackMap (n := n) (N := N) (sC := sC) (artinCoefficientPoint B c')).appTop
        ((pullback.snd sC (coefficientSpaceOver n N k)).appTop (coefficientCoord n N k m j)) =
        (pullback.snd sC (artinCoefficientPoint B c' ≫ coefficientSpaceOver n N k)).appTop
          ((artinCoefficientPoint B c').appTop (coefficientCoord n N k m j)) := by
      rw [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop, familyPullbackMap_snd,
        Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply]
    simp only
    rw [e1]
    unfold artinCoefficientPoint
    rw [tuplePoint_appTop_coord]
    rfl

/-- **The substituted equations from local data.** -/
private theorem curveMapConditions_equations_of_local (k : Type u) [Field k] [IsAlgClosed k]
    {C U : Scheme.{u}} (sC : C ⟶ Spec (.of k)) (sU : U ⟶ Spec (.of k))
    [IsProjectiveVariety k sC] [IsCurve k sC] [Smooth sC]
    {n : ℕ} [IsQuasiProjectiveVariety k sU] [SmoothOfRelativeDimension n sU]
    (f : C ⟶ U) (hf : f ≫ sU = sC)
    {b : ℕ} (P : Fin b → (Spec (.of k) ⟶ C)) (hP : ∀ i, P i ≫ sC = 𝟙 _)
    (hPinj : Function.Injective P)
    [((Scheme.Modules.pullback f).obj (dualSheaf sU.relativeDifferentials)).IsCoherent]
    [(SheafOfModules.unit C.ringCatSheaf).IsCoherent]
    {d : ℕ} {Z : Scheme.{u}} (i : Z ⟶ projectiveSpaceOverRing d (CommRingCat.of k))
    [IsClosedImmersion i] (j : U ⟶ Z) [IsOpenImmersion j]
    (hij : j ≫ i ≫ pullback.fst (terminal.from (Spec (.of k)))
        (terminal.from (projectiveSpaceAtUniverse.{u} d)) = sU)
    [IsInvertibleModule C ((Scheme.Modules.pullback ((f ≫ j ≫ i) ≫
      projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
        (twistingSheafAtUniverse.{u} d))]
    {N : ℕ} (w : letI := baseModule sC ((Scheme.Modules.pullback ((f ≫ j ≫ i) ≫
      projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
        (twistingSheafAtUniverse.{u} d)) ⊤;
      Module.Basis (Fin N) Γ(Spec (.of k), ⊤) Γ((Scheme.Modules.pullback ((f ≫ j ≫ i) ≫
        projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
          (twistingSheafAtUniverse.{u} d), ⊤))
    (a : Fin (d + 1) → Fin N → k)
    (hτ : ∀ i', pullbackCoordSection.{u} ((f ≫ j ≫ i) ≫
        projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k))) i' =
      ∑ j', sC.appTop ((Scheme.ΓSpecIso (.of k)).inv (a i' j')) • w j')
    {ιE : Type} (F : ιE → MvPolynomial (Fin (d + 1)) k) (dd : ιE → ℕ) {N' : ιE → ℕ}
    (w' : ∀ α, letI := baseModule sC (Stacks.TensorPowers.natTensorPow
        ((Scheme.Modules.pullback ((f ≫ j ≫ i) ≫
          projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
          (twistingSheafAtUniverse.{u} d)) (dd α)) ⊤;
      Module.Basis (Fin (N' α)) Γ(Spec (.of k), ⊤)
        Γ(Stacks.TensorPowers.natTensorPow ((Scheme.Modules.pullback ((f ≫ j ≫ i) ≫
          projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
          (twistingSheafAtUniverse.{u} d)) (dd α), ⊤))
    (hhom : ∀ α, (F α).IsHomogeneous (dd α))
    (hJ : (closedSubschemeIdeal i).toIdeal = Ideal.span (Set.range F))
    (ℓ : Fin b → Fin N → k) (c : Fin b → Fin (d + 1) → k) (μ : Fin (d + 1) → Fin N → k)
    (hc : ∀ β i', c β i' = ∑ j', ℓ β j' * a i' j')
    (hμ : ∑ i', ∑ j', μ i' j' * a i' j' = 1)
    (v : ∀ β, Γ((Scheme.Modules.pullback (P β)).obj ((Scheme.Modules.pullback ((f ≫ j ≫ i) ≫
      projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
        (twistingSheafAtUniverse.{u} d)), ⊤))
    (hv : ∀ β j', AlgebraicGeometry.pullbackGlobalSections (P β) ((Scheme.Modules.pullback
      ((f ≫ j ≫ i) ≫ projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
        (twistingSheafAtUniverse.{u} d)) (w j') = (Scheme.ΓSpecIso (.of k)).inv (ℓ β j') • v β)
    (Zc : Set (projectiveSpaceOver d (Spec (.of k)))) (hZc : IsClosed Zc)
    (hZc' : ∀ z : Z, z ∉ Set.range j.base → i.base z ∈ Zc)
    (hZ : ∀ x : C, (f ≫ j ≫ i).base x ∉ Zc)
    (Φ : pullback sC (finalSpace.over (n := d) sC _ w
      (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ) Zc hZc) ⟶ U)
    (hΦ : Φ ≫ j ≫ i = finalFamily (n := d) sC _ w
      (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ) Zc hZc)
    (m : Spec (.of k) ⟶ curveMapSpace (n := d) sC _ w F dd w' ℓ c μ Zc hZc)
    (hm : m ≫ finalSpace.over (n := d) sC _ w
      (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ) Zc hZc = 𝟙 (Spec (.of k)))
    (hma : m ≫ finalSpace.toCoefficientSpace (n := d) sC _ w
      (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ) Zc hZc =
        coefficientPoint (n := d) (N := N) a)
    {ι : Type u} [Fintype ι] [DecidableEq ι] [IsSeparated sU] [Smooth sU]
    (K : CurveMapCharts.ChartCover f ι) (l : ι → Fin (d + 1))
    (hσC : ∀ t, K.UC t ≤ nvCover (pullbackCoordSection.{u} ((f ≫ j ≫ i) ≫
      projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))) (l t))
    [IsInvertibleModule U ((Scheme.Modules.pullback ((j ≫ i) ≫
      projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
        (twistingSheafAtUniverse.{u} d))]
    (hσU : ∀ t, K.WU t ≤ nvCover (pullbackCoordSection.{u} ((j ≫ i) ≫
      projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))) (l t)) :
    ∀ (B : ArtinLocalAlgebra k) (c' : Fin (d + 1) → Fin N → B.carrier)
        (y : ∀ t : ι, (CurveMapCharts.curveCharts sC sU K hf
            (fun β => (P β).base (IsLocalRing.closedPoint k))).S {t} →ₐ[k]
          (CurveMapCharts.curveCharts sC sU K hf
            (fun β => (P β).base (IsLocalRing.closedPoint k))).O {t} ⊗[k] B.carrier)
        (fr : ∀ t : ι, ((CurveMapCharts.curveCharts sC sU K hf
            (fun β => (P β).base (IsLocalRing.closedPoint k))).O {t} ⊗[k] B.carrier)ˣ),
        (∀ t m', ∑ j', CurveMapCharts.localSection sC sU hf K
              (fun β => (P β).base (IsLocalRing.closedPoint k)) _ l hσC (w j') t ⊗ₜ[k] c' m' j' =
            fr t * y t (CurveMapCharts.chartCoord _ K.WU l hσU m' t)) →
        (∀ t z, Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k ((CurveMapCharts.curveCharts sC sU K
            hf (fun β => (P β).base (IsLocalRing.closedPoint k))).𝔟 {t})) (AlgHom.id k _) (y t z) =
          Ideal.Quotient.mk _ ((CurveMapCharts.curveCharts sC sU K hf
            (fun β => (P β).base (IsLocalRing.closedPoint k))).f0 {t} z) ⊗ₜ[k] 1) →
        ∀ α j', ((artinCoefficientPoint B) c').appTop
          (equationFunctions (n := d) sC _ w (dd α) (w' α) (F α) j') = 0 := by
  intro B c' y fr hy hfix α j'
  classical
  have hvarC : IsVariety k sC := inferInstance
  haveI : IsSeparated sC := hvarC.toIsSeparated
  haveI : IsProper sC := (inferInstance : IsProperVariety k sC).toIsProper
  have hgo : artinCoefficientPoint B c' ≫ coefficientSpaceOver d N k =
      specStructMap (k := k) B.carrier := tuplePoint_over _ _
  have H : IsPullback (pullback.fst sC (artinCoefficientPoint B c' ≫ coefficientSpaceOver d N k))
      (pullback.snd sC (artinCoefficientPoint B c' ≫ coefficientSpaceOver d N k)) sC
      (specStructMap (k := k) B.carrier) := by
    rw [← hgo]
    exact IsPullback.of_hasPullback _ _
  -- the equations vanish on the charts of `U`
  let gU := (j ≫ i) ≫ projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k))
  have hsU : GeneratesStalks (pullbackCoordSection.{u} gU) :=
    Stacks.ProjectiveSpaceModuli.taut_generates gU
  have hjU : j ≫ i = toProjectiveSpaceOver (pullbackCoordSection.{u} gU) hsU sU :=
    eq_toProjectiveSpaceOver_of_pinned _ hsU sU (j ≫ i) (by rw [Category.assoc]; exact hij)
      (𝟙 _) (fun _ => rfl)
  have hFα : F α ∈ (closedSubschemeIdeal i).toIdeal := by
    rw [hJ]
    exact Ideal.subset_span ⟨α, rfl⟩
  have hU0 : ∀ t, MvPolynomial.eval₂ (algebraMap k ((CurveMapCharts.curveCharts sC sU K hf
      (fun β => (P β).base (IsLocalRing.closedPoint k))).S {t}))
      (fun m => CurveMapCharts.chartCoord _ K.WU l hσU m t) (F α) = 0 := by
    intro t
    have h0 := (exists_lift_closedImmersion_iff (pullbackCoordSection.{u} gU) sU i hsU).1
      ⟨j, hjU⟩ (l t) (F α) hFα
    exact eval₂_resO_ratio_eq_zero _ sU (l t) h0 _
  -- the local frames on `C ×ₖ Spec B`
  let V : ι → (pullback sC (artinCoefficientPoint B c' ≫ coefficientSpaceOver d N k)).Opens :=
    fun t => pullback.fst sC (artinCoefficientPoint B c' ≫ coefficientSpaceOver d N k) ⁻¹ᵁ
      (({t} : Finset ι).inf K.UC)
  have hVcov : ∀ y, ∃ t, y ∈ V t := by
    intro y
    have hcov : (pullback.fst sC (artinCoefficientPoint B c' ≫ coefficientSpaceOver d N k)).base y ∈
        ⨆ t, K.UC t := K.cover ▸ trivial
    obtain ⟨t, ht⟩ := TopologicalSpace.Opens.mem_iSup.1 hcov
    exact ⟨t, by change _ ∈ ({t} : Finset ι).inf K.UC; rwa [Finset.inf_singleton]⟩
  have hUt : ∀ t, ({t} : Finset ι).inf K.UC ≤ nvOpen _ (pullbackCoordSection.{u}
      ((f ≫ j ≫ i) ≫ projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k))) (l t)) :=
    fun t => CurveMapCharts.inf_le_nvCover _ K.UC l hσC (Finset.mem_singleton_self t)
  have hcpt : ∀ t, IsCompact ((({t} : Finset ι).inf K.UC : C.Opens) : Set C) := fun t =>
    (K.isAffineOpen_inf_UC sC (Finset.singleton_nonempty t)).isCompact
  have hqs : ∀ t, IsQuasiSeparated ((({t} : Finset ι).inf K.UC : C.Opens) : Set C) := fun t =>
    (K.isAffineOpen_inf_UC sC (Finset.singleton_nonempty t)).isQuasiSeparated
  let σ : ι → Γ(familyModule (n := d) (N := N) (L := (Scheme.Modules.pullback ((f ≫ j ≫ i) ≫
      projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
        (twistingSheafAtUniverse.{u} d)) (sC := sC) (artinCoefficientPoint B c'), ⊤) := fun t =>
    AlgebraicGeometry.pullbackGlobalSections
      (familyPullbackMap (n := d) (N := N) (sC := sC) (artinCoefficientPoint B c')) _
      (AlgebraicGeometry.pullbackGlobalSections (pullback.fst sC (coefficientSpaceOver d N k)) _
        (pullbackCoordSection.{u}
          ((f ≫ j ≫ i) ≫ projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k))) (l t)))
  have hσ : ∀ t, V t ≤ nvOpen _ (σ t) := by
    intro t
    rw [Stacks.RatioPullback.nvOpen_pullbackGlobalSections,
      Stacks.RatioPullback.nvOpen_pullbackGlobalSections]
    intro x hx
    have hx' : (familyPullbackMap (n := d) (N := N) (sC := sC) (artinCoefficientPoint B c') ≫
        pullback.fst sC (coefficientSpaceOver d N k)).base x ∈ ({t} : Finset ι).inf K.UC := by
      rwa [familyPullbackMap_fst]
    exact hUt t hx'
  let e : ∀ t, _ := fun t => baseChangeEquiv sC H (({t} : Finset ι).inf K.UC) (hcpt t) (hqs t)
  let u : ∀ t, Fin (d + 1) →
      Γ(pullback sC (artinCoefficientPoint B c' ≫ coefficientSpaceOver d N k), V t) :=
    fun t m => e t (∑ j', CurveMapCharts.localSection sC sU hf K
      (fun β => (P β).base (IsLocalRing.closedPoint k)) _ l hσC (w j') t ⊗ₜ[k] c' m j' :
        (CurveMapCharts.curveCharts sC sU K hf
          (fun β => (P β).base (IsLocalRing.closedPoint k))).O {t} ⊗[k] B.carrier)
  have hu : ∀ t m, resT (V t) (familySection (n := d) (N := N) (e := w) (sC := sC)
      (artinCoefficientPoint B c') m) = u t m • resT (V t) (σ t) := fun t m =>
    resT_familySection_eq_smul sC _ w B c' H _ (hUt t) (hcpt t) (hqs t) m
  -- the local equations
  have hF0 : ∀ t, MvPolynomial.eval₂ (Stacks.Cech.baseRingHom
      (pullback.fst sC (artinCoefficientPoint B c' ≫ coefficientSpaceOver d N k) ≫ sC) (V t)).hom
      (u t) (F α) = 0 := by
    intro t
    let ψ := (e t).toRingHom.comp (y t).toRingHom
    have hut : u t = fun m => e t ((fr t : (CurveMapCharts.curveCharts sC sU K hf
        (fun β => (P β).base (IsLocalRing.closedPoint k))).O {t} ⊗[k] B.carrier)) *
          ψ (CurveMapCharts.chartCoord _ K.WU l hσU m t) := by
      funext m
      change e t _ = _
      rw [hy t m]
      exact (e t).map_mul _ _
    have hψ : ψ.comp (algebraMap k ((CurveMapCharts.curveCharts sC sU K hf
        (fun β => (P β).base (IsLocalRing.closedPoint k))).S {t})) =
        (Stacks.Cech.baseRingHom
          (pullback.fst sC (artinCoefficientPoint B c' ≫ coefficientSpaceOver d N k) ≫ sC)
          (V t)).hom := by
      ext c
      change e t (y t (algebraMap k _ c)) = _
      rw [AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply]
      refine (baseChangeEquiv_tmul sC H _ (hcpt t) (hqs t) _ _).trans ?_
      rw [map_one, map_one, mul_one]
      exact ConcreteCategory.congr_hom (CurveMapCharts.baseRingHom_comp_appLE
        (pullback.fst sC (artinCoefficientPoint B c' ≫ coefficientSpaceOver d N k) ≫ sC) sC rfl
        (le_refl (V t))) c
    rw [hut, CurveMapSections.eval₂_mul_of_isHomogeneous _ (hhom α), ← hψ]
    have := MvPolynomial.eval₂_comp_left ψ (algebraMap k ((CurveMapCharts.curveCharts sC sU K hf
      (fun β => (P β).base (IsLocalRing.closedPoint k))).S {t}))
      (fun m => CurveMapCharts.chartCoord _ K.WU l hσU m t) (F α)
    erw [← this]
    rw [hU0 t, map_zero, mul_zero]
  -- generation and the chart evaluations on `C ×ₖ Spec B`
  have hunit : ∀ t, ∃ m, IsUnit (u t m) := by
    intro t
    refine ⟨l t, ?_⟩
    have h1 : ((fr t : (CurveMapCharts.curveCharts sC sU K hf
        (fun β => (P β).base (IsLocalRing.closedPoint k))).O {t} ⊗[k] B.carrier) *
        y t (CurveMapCharts.chartCoord _ K.WU l hσU (l t) t)) = fr t := by
      rw [CurveMapCharts.chartCoord_self]
      exact (congrArg (fun z => (fr t : (CurveMapCharts.curveCharts sC sU K hf
        (fun β => (P β).base (IsLocalRing.closedPoint k))).O {t} ⊗[k] B.carrier) * z)
          (map_one (y t))).trans (mul_one _)
    change IsUnit (e t _)
    rw [hy t (l t)]
    erw [h1]
    exact (fr t).isUnit.map (e t)
  have hs := generatesStalks_of_local _ V hVcov σ hσ u hu hunit
  have h0 := chartEval_eq_zero_of_local _
    (pullback.fst sC (artinCoefficientPoint B c' ≫ coefficientSpaceOver d N k) ≫ sC) V hVcov σ hσ
      u hu (hhom α) hF0
  refine equationFunctions_eq_zero_of_pullSection sC _ w (artinCoefficientPoint B c') (dd α)
    (w' α) (F α) ?_ j'
  refine pullSection_eq_zero_of_chartEval_pullback
    (familyPullbackMap (n := d) (N := N) (sC := sC) (artinCoefficientPoint B c'))
    (pullback.fst sC (coefficientSpaceOver d N k) ≫ sC) _ (universalSection sC _ w) (hhom α) hs
    (by rw [← Category.assoc, familyPullbackMap_fst]) h0

/-- **The proportionality at the marked points from local data.** -/
private theorem curveMapConditions_proportionality_of_local (k : Type u) [Field k] [IsAlgClosed k]
    {C U : Scheme.{u}} (sC : C ⟶ Spec (.of k)) (sU : U ⟶ Spec (.of k))
    [IsProjectiveVariety k sC] [IsCurve k sC] [Smooth sC]
    {n : ℕ} [IsQuasiProjectiveVariety k sU] [SmoothOfRelativeDimension n sU]
    (f : C ⟶ U) (hf : f ≫ sU = sC)
    {b : ℕ} (P : Fin b → (Spec (.of k) ⟶ C)) (hP : ∀ i, P i ≫ sC = 𝟙 _)
    (hPinj : Function.Injective P)
    [((Scheme.Modules.pullback f).obj (dualSheaf sU.relativeDifferentials)).IsCoherent]
    [(SheafOfModules.unit C.ringCatSheaf).IsCoherent]
    {d : ℕ} {Z : Scheme.{u}} (i : Z ⟶ projectiveSpaceOverRing d (CommRingCat.of k))
    [IsClosedImmersion i] (j : U ⟶ Z) [IsOpenImmersion j]
    (hij : j ≫ i ≫ pullback.fst (terminal.from (Spec (.of k)))
        (terminal.from (projectiveSpaceAtUniverse.{u} d)) = sU)
    [IsInvertibleModule C ((Scheme.Modules.pullback ((f ≫ j ≫ i) ≫
      projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
        (twistingSheafAtUniverse.{u} d))]
    {N : ℕ} (w : letI := baseModule sC ((Scheme.Modules.pullback ((f ≫ j ≫ i) ≫
      projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
        (twistingSheafAtUniverse.{u} d)) ⊤;
      Module.Basis (Fin N) Γ(Spec (.of k), ⊤) Γ((Scheme.Modules.pullback ((f ≫ j ≫ i) ≫
        projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
          (twistingSheafAtUniverse.{u} d), ⊤))
    (a : Fin (d + 1) → Fin N → k)
    (hτ : ∀ i', pullbackCoordSection.{u} ((f ≫ j ≫ i) ≫
        projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k))) i' =
      ∑ j', sC.appTop ((Scheme.ΓSpecIso (.of k)).inv (a i' j')) • w j')
    {ιE : Type} (F : ιE → MvPolynomial (Fin (d + 1)) k) (dd : ιE → ℕ) {N' : ιE → ℕ}
    (w' : ∀ α, letI := baseModule sC (Stacks.TensorPowers.natTensorPow
        ((Scheme.Modules.pullback ((f ≫ j ≫ i) ≫
          projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
          (twistingSheafAtUniverse.{u} d)) (dd α)) ⊤;
      Module.Basis (Fin (N' α)) Γ(Spec (.of k), ⊤)
        Γ(Stacks.TensorPowers.natTensorPow ((Scheme.Modules.pullback ((f ≫ j ≫ i) ≫
          projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
          (twistingSheafAtUniverse.{u} d)) (dd α), ⊤))
    (hhom : ∀ α, (F α).IsHomogeneous (dd α))
    (hJ : (closedSubschemeIdeal i).toIdeal = Ideal.span (Set.range F))
    (ℓ : Fin b → Fin N → k) (c : Fin b → Fin (d + 1) → k) (μ : Fin (d + 1) → Fin N → k)
    (hc : ∀ β i', c β i' = ∑ j', ℓ β j' * a i' j')
    (hμ : ∑ i', ∑ j', μ i' j' * a i' j' = 1)
    (v : ∀ β, Γ((Scheme.Modules.pullback (P β)).obj ((Scheme.Modules.pullback ((f ≫ j ≫ i) ≫
      projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
        (twistingSheafAtUniverse.{u} d)), ⊤))
    (hv : ∀ β j', AlgebraicGeometry.pullbackGlobalSections (P β) ((Scheme.Modules.pullback
      ((f ≫ j ≫ i) ≫ projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
        (twistingSheafAtUniverse.{u} d)) (w j') = (Scheme.ΓSpecIso (.of k)).inv (ℓ β j') • v β)
    (Zc : Set (projectiveSpaceOver d (Spec (.of k)))) (hZc : IsClosed Zc)
    (hZc' : ∀ z : Z, z ∉ Set.range j.base → i.base z ∈ Zc)
    (hZ : ∀ x : C, (f ≫ j ≫ i).base x ∉ Zc)
    (Φ : pullback sC (finalSpace.over (n := d) sC _ w
      (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ) Zc hZc) ⟶ U)
    (hΦ : Φ ≫ j ≫ i = finalFamily (n := d) sC _ w
      (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ) Zc hZc)
    (m : Spec (.of k) ⟶ curveMapSpace (n := d) sC _ w F dd w' ℓ c μ Zc hZc)
    (hm : m ≫ finalSpace.over (n := d) sC _ w
      (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ) Zc hZc = 𝟙 (Spec (.of k)))
    (hma : m ≫ finalSpace.toCoefficientSpace (n := d) sC _ w
      (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ) Zc hZc =
        coefficientPoint (n := d) (N := N) a)
    {ι : Type u} [Fintype ι] [DecidableEq ι] [IsSeparated sU] [Smooth sU]
    (K : CurveMapCharts.ChartCover f ι) (l : ι → Fin (d + 1))
    (hσC : ∀ t, K.UC t ≤ nvCover (pullbackCoordSection.{u} ((f ≫ j ≫ i) ≫
      projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))) (l t))
    [IsInvertibleModule U ((Scheme.Modules.pullback ((j ≫ i) ≫
      projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
        (twistingSheafAtUniverse.{u} d))]
    (hσU : ∀ t, K.WU t ≤ nvCover (pullbackCoordSection.{u} ((j ≫ i) ≫
      projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))) (l t)) :
    ∀ (B : ArtinLocalAlgebra k) (c' : Fin (d + 1) → Fin N → B.carrier)
        (y : ∀ t : ι, (CurveMapCharts.curveCharts sC sU K hf
            (fun β => (P β).base (IsLocalRing.closedPoint k))).S {t} →ₐ[k]
          (CurveMapCharts.curveCharts sC sU K hf
            (fun β => (P β).base (IsLocalRing.closedPoint k))).O {t} ⊗[k] B.carrier)
        (fr : ∀ t : ι, ((CurveMapCharts.curveCharts sC sU K hf
            (fun β => (P β).base (IsLocalRing.closedPoint k))).O {t} ⊗[k] B.carrier)ˣ),
        (∀ t m', ∑ j', CurveMapCharts.localSection sC sU hf K
              (fun β => (P β).base (IsLocalRing.closedPoint k)) _ l hσC (w j') t ⊗ₜ[k] c' m' j' =
            fr t * y t (CurveMapCharts.chartCoord _ K.WU l hσU m' t)) →
        (∀ t z, Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k ((CurveMapCharts.curveCharts sC sU K
            hf (fun β => (P β).base (IsLocalRing.closedPoint k))).𝔟 {t})) (AlgHom.id k _) (y t z) =
          Ideal.Quotient.mk _ ((CurveMapCharts.curveCharts sC sU K hf
            (fun β => (P β).base (IsLocalRing.closedPoint k))).f0 {t} z) ⊗ₜ[k] 1) →
        ∀ β i₁ i₂, ((artinCoefficientPoint B) c').appTop
          (proportionalityFunction d N k (ℓ β) (c β) i₁ i₂) = 0 := by
  intro B c' y fr hy hfix β i₁ i₂
  classical
  have hτ' : ∀ i', pullbackCoordSection.{u} ((f ≫ j ≫ i) ≫
      projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k))) i' =
      ∑ j', sC.appTop ((Scheme.ΓSpecIso (.of k)).inv (a i' j')) • w j' := hτ
  have hcov : (P β).base (IsLocalRing.closedPoint k) ∈ ⨆ t, K.UC t := K.cover ▸ trivial
  obtain ⟨t, ht⟩ := TopologicalSpace.Opens.mem_iSup.1 hcov
  have hV : ⊤ ≤ (P β) ⁻¹ᵁ (({t} : Finset ι).inf K.UC) := by
    intro x _
    change (P β).base x ∈ ({t} : Finset ι).inf K.UC
    rw [Finset.inf_singleton, Subsingleton.elim x (IsLocalRing.closedPoint k)]
    exact ht
  set ev := chartPointEval sC sU hf K (fun β => (P β).base (IsLocalRing.closedPoint k)) (P β) (hP β)
    t hV with hev
  obtain ⟨κ, hκ⟩ := exists_eq_mul_pointEval_localSection sC sU hf K
    (fun β => (P β).base (IsLocalRing.closedPoint k)) _ l hσC w (P β) (hP β) t hV (ℓ β) (v β)
    (hv β) (a (l t)) (hτ' (l t))
  -- the value of the pulled-back coordinates
  have hloc : ∀ m', ev ((CurveMapCharts.curveCharts sC sU K hf (fun β => (P β).base
      (IsLocalRing.closedPoint k))).f0 {t} (CurveMapCharts.chartCoord _ K.WU l hσU m' t)) =
      ∑ j', a m' j' * ev (CurveMapCharts.localSection sC sU hf K
        (fun β => (P β).base (IsLocalRing.closedPoint k)) _ l hσC (w j') t) := by
    intro m'
    have h1 : (CurveMapCharts.curveCharts sC sU K hf (fun β => (P β).base (IsLocalRing.closedPoint
        k))).f0 {t} (CurveMapCharts.chartCoord _ K.WU l hσU m' t) =
        CurveMapCharts.chartLocal _ K.UC l hσC (pullbackCoordSection.{u} ((f ≫ j ≫ i) ≫
          projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k))) m') t := by
      change f.appLE _ _ (K.le_inf {t}) (Stacks.ProjectiveFromSections.resO _ (div _ le_rfl
        (resT _ _))) = div _ _ (resT _ _)
      rw [CurveMapCharts.resO_div, resM_resT]
      exact appLE_div_pullbackCoordSection f ((j ≫ i) ≫
        projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k))) _ (by simp only [Category.assoc])
        (K.le_inf {t}) (l t) m' _ _
    rw [h1, hτ' m', CurveMapCharts.chartLocal_sum_coefficients sC sU hf K _ _ l hσC w, map_sum]
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [map_smul, smul_eq_mul]
  have hcm : ∀ m', c β m' = κ * ev ((CurveMapCharts.curveCharts sC sU K hf (fun β => (P β).base
      (IsLocalRing.closedPoint k))).f0 {t} (CurveMapCharts.chartCoord _ K.WU l hσU m' t)) := by
    intro m'
    rw [hloc m', hc β m', Finset.mul_sum]
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [hκ j']
    change κ * ev _ * a m' j' = κ * (a m' j' * ev _)
    ring
  -- the evaluated frame equations
  have hI : ∀ x ∈ (CurveMapCharts.curveCharts sC sU K hf (fun β => (P β).base
      (IsLocalRing.closedPoint k))).𝔟 {t}, ev x = 0 := fun x hx =>
    chartPointEval_eq_zero_of_mem sC sU hf K _ (P β) (hP β) t hV β _ rfl x hx
  have hlam : ∀ m', ∑ j', algebraMap k B.carrier (ℓ β j') * c' m' j' =
      tensorEval ev (fr t : (CurveMapCharts.curveCharts sC sU K hf (fun β => (P β).base
          (IsLocalRing.closedPoint k))).O {t} ⊗[k] B.carrier) * algebraMap k B.carrier (c β m') :=
          by
    intro m'
    have h1 := congrArg (tensorEval ev) (hy t m')
    rw [tensorEval_sum, map_mul, tensorEval_eq_of_map_mk ev _ hI _ _ _
      (hfix t (CurveMapCharts.chartCoord _ K.WU l hσU m' t))] at h1
    rw [hcm m', map_mul]
    calc ∑ j', algebraMap k B.carrier (ℓ β j') * c' m' j'
        = algebraMap k B.carrier κ * ∑ j', algebraMap k B.carrier (ev
          (CurveMapCharts.localSection sC sU hf K
            (fun β => (P β).base (IsLocalRing.closedPoint k)) _ l hσC (w j') t)) * c' m' j' := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j' _ => ?_
          rw [hκ j', map_mul, mul_assoc]
          rfl
      _ = _ := by rw [h1]; ring
  -- the proportionality
  rw [proportionalityFunction, appTop_artinCoefficientPoint_linearFunction]
  have hsum : ∑ r, ∑ j', algebraMap k B.carrier
      (proportionalityVector (ℓ β) (c β) i₁ i₂ r j') * c' r j' =
      tensorEval ev (fr t : (CurveMapCharts.curveCharts sC sU K hf (fun β => (P β).base
          (IsLocalRing.closedPoint k))).O {t} ⊗[k] B.carrier) * algebraMap k B.carrier
        (∑ r, ((if r = i₁ then c β i₂ else 0) - (if r = i₂ then c β i₁ else 0)) * c β r) := by
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    have h2 : ∑ j', algebraMap k B.carrier (proportionalityVector (ℓ β) (c β) i₁ i₂ r j') *
        c' r j' = algebraMap k B.carrier
          ((if r = i₁ then c β i₂ else 0) - (if r = i₂ then c β i₁ else 0)) *
        ∑ j', algebraMap k B.carrier (ℓ β j') * c' r j' := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j' _ => ?_
      simp only [proportionalityVector, map_mul]
      ring
    rw [h2, hlam r, map_mul]
    ring
  have h0 : ∑ r, ((if r = i₁ then c β i₂ else 0) - (if r = i₂ then c β i₁ else 0)) * c β r = 0 := by
    simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    ring
  rw [hsum, h0, map_zero, mul_zero, map_zero]

/-- **The substituted equations and the proportionality at the marked points from local data.** -/
private theorem curveMapConditions_of_local (k : Type u) [Field k] [IsAlgClosed k]
    {C U : Scheme.{u}} (sC : C ⟶ Spec (.of k)) (sU : U ⟶ Spec (.of k))
    [IsProjectiveVariety k sC] [IsCurve k sC] [Smooth sC]
    {n : ℕ} [IsQuasiProjectiveVariety k sU] [SmoothOfRelativeDimension n sU]
    (f : C ⟶ U) (hf : f ≫ sU = sC)
    {b : ℕ} (P : Fin b → (Spec (.of k) ⟶ C)) (hP : ∀ i, P i ≫ sC = 𝟙 _)
    (hPinj : Function.Injective P)
    [((Scheme.Modules.pullback f).obj (dualSheaf sU.relativeDifferentials)).IsCoherent]
    [(SheafOfModules.unit C.ringCatSheaf).IsCoherent]
    {d : ℕ} {Z : Scheme.{u}} (i : Z ⟶ projectiveSpaceOverRing d (CommRingCat.of k))
    [IsClosedImmersion i] (j : U ⟶ Z) [IsOpenImmersion j]
    (hij : j ≫ i ≫ pullback.fst (terminal.from (Spec (.of k)))
        (terminal.from (projectiveSpaceAtUniverse.{u} d)) = sU)
    [IsInvertibleModule C ((Scheme.Modules.pullback ((f ≫ j ≫ i) ≫
      projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
        (twistingSheafAtUniverse.{u} d))]
    {N : ℕ} (w : letI := baseModule sC ((Scheme.Modules.pullback ((f ≫ j ≫ i) ≫
      projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
        (twistingSheafAtUniverse.{u} d)) ⊤;
      Module.Basis (Fin N) Γ(Spec (.of k), ⊤) Γ((Scheme.Modules.pullback ((f ≫ j ≫ i) ≫
        projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
          (twistingSheafAtUniverse.{u} d), ⊤))
    (a : Fin (d + 1) → Fin N → k)
    (hτ : ∀ i', pullbackCoordSection.{u} ((f ≫ j ≫ i) ≫
        projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k))) i' =
      ∑ j', sC.appTop ((Scheme.ΓSpecIso (.of k)).inv (a i' j')) • w j')
    {ιE : Type} (F : ιE → MvPolynomial (Fin (d + 1)) k) (dd : ιE → ℕ) {N' : ιE → ℕ}
    (w' : ∀ α, letI := baseModule sC (Stacks.TensorPowers.natTensorPow
        ((Scheme.Modules.pullback ((f ≫ j ≫ i) ≫
          projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
          (twistingSheafAtUniverse.{u} d)) (dd α)) ⊤;
      Module.Basis (Fin (N' α)) Γ(Spec (.of k), ⊤)
        Γ(Stacks.TensorPowers.natTensorPow ((Scheme.Modules.pullback ((f ≫ j ≫ i) ≫
          projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
          (twistingSheafAtUniverse.{u} d)) (dd α), ⊤))
    (hhom : ∀ α, (F α).IsHomogeneous (dd α))
    (hJ : (closedSubschemeIdeal i).toIdeal = Ideal.span (Set.range F))
    (ℓ : Fin b → Fin N → k) (c : Fin b → Fin (d + 1) → k) (μ : Fin (d + 1) → Fin N → k)
    (hc : ∀ β i', c β i' = ∑ j', ℓ β j' * a i' j')
    (hμ : ∑ i', ∑ j', μ i' j' * a i' j' = 1)
    (v : ∀ β, Γ((Scheme.Modules.pullback (P β)).obj ((Scheme.Modules.pullback ((f ≫ j ≫ i) ≫
      projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
        (twistingSheafAtUniverse.{u} d)), ⊤))
    (hv : ∀ β j', AlgebraicGeometry.pullbackGlobalSections (P β) ((Scheme.Modules.pullback
      ((f ≫ j ≫ i) ≫ projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
        (twistingSheafAtUniverse.{u} d)) (w j') = (Scheme.ΓSpecIso (.of k)).inv (ℓ β j') • v β)
    (Zc : Set (projectiveSpaceOver d (Spec (.of k)))) (hZc : IsClosed Zc)
    (hZc' : ∀ z : Z, z ∉ Set.range j.base → i.base z ∈ Zc)
    (hZ : ∀ x : C, (f ≫ j ≫ i).base x ∉ Zc)
    (Φ : pullback sC (finalSpace.over (n := d) sC _ w
      (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ) Zc hZc) ⟶ U)
    (hΦ : Φ ≫ j ≫ i = finalFamily (n := d) sC _ w
      (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ) Zc hZc)
    (m : Spec (.of k) ⟶ curveMapSpace (n := d) sC _ w F dd w' ℓ c μ Zc hZc)
    (hm : m ≫ finalSpace.over (n := d) sC _ w
      (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ) Zc hZc = 𝟙 (Spec (.of k)))
    (hma : m ≫ finalSpace.toCoefficientSpace (n := d) sC _ w
      (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ) Zc hZc =
        coefficientPoint (n := d) (N := N) a)
    {ι : Type u} [Fintype ι] [DecidableEq ι] [IsSeparated sU] [Smooth sU]
    (K : CurveMapCharts.ChartCover f ι) (l : ι → Fin (d + 1))
    (hσC : ∀ t, K.UC t ≤ nvCover (pullbackCoordSection.{u} ((f ≫ j ≫ i) ≫
      projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))) (l t))
    [IsInvertibleModule U ((Scheme.Modules.pullback ((j ≫ i) ≫
      projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
        (twistingSheafAtUniverse.{u} d))]
    (hσU : ∀ t, K.WU t ≤ nvCover (pullbackCoordSection.{u} ((j ≫ i) ≫
      projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))) (l t)) :
    ∀ (B : ArtinLocalAlgebra k) (c' : Fin (d + 1) → Fin N → B.carrier)
        (y : ∀ t : ι, (CurveMapCharts.curveCharts sC sU K hf
            (fun β => (P β).base (IsLocalRing.closedPoint k))).S {t} →ₐ[k]
          (CurveMapCharts.curveCharts sC sU K hf
            (fun β => (P β).base (IsLocalRing.closedPoint k))).O {t} ⊗[k] B.carrier)
        (fr : ∀ t : ι, ((CurveMapCharts.curveCharts sC sU K hf
            (fun β => (P β).base (IsLocalRing.closedPoint k))).O {t} ⊗[k] B.carrier)ˣ),
        (∀ t m', ∑ j', CurveMapCharts.localSection sC sU hf K
              (fun β => (P β).base (IsLocalRing.closedPoint k)) _ l hσC (w j') t ⊗ₜ[k] c' m' j' =
            fr t * y t (CurveMapCharts.chartCoord _ K.WU l hσU m' t)) →
        (∀ t z, Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k ((CurveMapCharts.curveCharts sC sU K
            hf (fun β => (P β).base (IsLocalRing.closedPoint k))).𝔟 {t})) (AlgHom.id k _) (y t z) =
          Ideal.Quotient.mk _ ((CurveMapCharts.curveCharts sC sU K hf
            (fun β => (P β).base (IsLocalRing.closedPoint k))).f0 {t} z) ⊗ₜ[k] 1) →
        (∀ α j', ((artinCoefficientPoint B) c').appTop
          (equationFunctions (n := d) sC _ w (dd α) (w' α) (F α) j') = 0) ∧
        ∀ β i₁ i₂, ((artinCoefficientPoint B) c').appTop
          (proportionalityFunction d N k (ℓ β) (c β) i₁ i₂) = 0 := by
  intro B c' y fr hy hfix
  exact ⟨curveMapConditions_equations_of_local k sC sU (n := n) f hf P hP hPinj i j hij w a hτ F dd
      w' hhom hJ ℓ c μ hc hμ v hv Zc hZc hZc' hZ Φ hΦ m hm hma K l hσC hσU B c' y fr hy hfix,
    curveMapConditions_proportionality_of_local k sC sU (n := n) f hf P hP hPinj i j hij w a hτ F
        dd w' hhom hJ ℓ c μ hc hμ v hv Zc hZc hZc' hZ Φ hΦ m hm hma K l hσC hσU B c' y fr hy hfix⟩

/-- **The points of `M` at `[f]` on an adapted affine chart cover.** -/
private theorem nonempty_chartPoints (k : Type u) [Field k] [IsAlgClosed k]
    {C U : Scheme.{u}} (sC : C ⟶ Spec (.of k)) (sU : U ⟶ Spec (.of k))
    [IsProjectiveVariety k sC] [IsCurve k sC] [Smooth sC]
    {n : ℕ} [IsQuasiProjectiveVariety k sU] [SmoothOfRelativeDimension n sU]
    (f : C ⟶ U) (hf : f ≫ sU = sC)
    {b : ℕ} (P : Fin b → (Spec (.of k) ⟶ C)) (hP : ∀ i, P i ≫ sC = 𝟙 _)
    (hPinj : Function.Injective P)
    [((Scheme.Modules.pullback f).obj (dualSheaf sU.relativeDifferentials)).IsCoherent]
    [(SheafOfModules.unit C.ringCatSheaf).IsCoherent]
    {d : ℕ} {Z : Scheme.{u}} (i : Z ⟶ projectiveSpaceOverRing d (CommRingCat.of k))
    [IsClosedImmersion i] (j : U ⟶ Z) [IsOpenImmersion j]
    (hij : j ≫ i ≫ pullback.fst (terminal.from (Spec (.of k)))
        (terminal.from (projectiveSpaceAtUniverse.{u} d)) = sU)
    [IsInvertibleModule C ((Scheme.Modules.pullback ((f ≫ j ≫ i) ≫
      projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
        (twistingSheafAtUniverse.{u} d))]
    {N : ℕ} (w : letI := baseModule sC ((Scheme.Modules.pullback ((f ≫ j ≫ i) ≫
      projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
        (twistingSheafAtUniverse.{u} d)) ⊤;
      Module.Basis (Fin N) Γ(Spec (.of k), ⊤) Γ((Scheme.Modules.pullback ((f ≫ j ≫ i) ≫
        projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
          (twistingSheafAtUniverse.{u} d), ⊤))
    (a : Fin (d + 1) → Fin N → k)
    (hτ : ∀ i', pullbackCoordSection.{u} ((f ≫ j ≫ i) ≫
        projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k))) i' =
      ∑ j', sC.appTop ((Scheme.ΓSpecIso (.of k)).inv (a i' j')) • w j')
    {ιE : Type} (F : ιE → MvPolynomial (Fin (d + 1)) k) (dd : ιE → ℕ) {N' : ιE → ℕ}
    (w' : ∀ α, letI := baseModule sC (Stacks.TensorPowers.natTensorPow
        ((Scheme.Modules.pullback ((f ≫ j ≫ i) ≫
          projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
          (twistingSheafAtUniverse.{u} d)) (dd α)) ⊤;
      Module.Basis (Fin (N' α)) Γ(Spec (.of k), ⊤)
        Γ(Stacks.TensorPowers.natTensorPow ((Scheme.Modules.pullback ((f ≫ j ≫ i) ≫
          projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
          (twistingSheafAtUniverse.{u} d)) (dd α), ⊤))
    (hhom : ∀ α, (F α).IsHomogeneous (dd α))
    (hJ : (closedSubschemeIdeal i).toIdeal = Ideal.span (Set.range F))
    (ℓ : Fin b → Fin N → k) (c : Fin b → Fin (d + 1) → k) (μ : Fin (d + 1) → Fin N → k)
    (hc : ∀ β i', c β i' = ∑ j', ℓ β j' * a i' j')
    (hμ : ∑ i', ∑ j', μ i' j' * a i' j' = 1)
    (v : ∀ β, Γ((Scheme.Modules.pullback (P β)).obj ((Scheme.Modules.pullback ((f ≫ j ≫ i) ≫
      projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
        (twistingSheafAtUniverse.{u} d)), ⊤))
    (hv : ∀ β j', AlgebraicGeometry.pullbackGlobalSections (P β) ((Scheme.Modules.pullback
      ((f ≫ j ≫ i) ≫ projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
        (twistingSheafAtUniverse.{u} d)) (w j') = (Scheme.ΓSpecIso (.of k)).inv (ℓ β j') • v β)
    (Zc : Set (projectiveSpaceOver d (Spec (.of k)))) (hZc : IsClosed Zc)
    (hZc' : ∀ z : Z, z ∉ Set.range j.base → i.base z ∈ Zc)
    (hZ : ∀ x : C, (f ≫ j ≫ i).base x ∉ Zc)
    (Φ : pullback sC (finalSpace.over (n := d) sC _ w
      (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ) Zc hZc) ⟶ U)
    (hΦ : Φ ≫ j ≫ i = finalFamily (n := d) sC _ w
      (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ) Zc hZc)
    (m : Spec (.of k) ⟶ curveMapSpace (n := d) sC _ w F dd w' ℓ c μ Zc hZc)
    (hm : m ≫ finalSpace.over (n := d) sC _ w
      (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ) Zc hZc = 𝟙 (Spec (.of k)))
    (hma : m ≫ finalSpace.toCoefficientSpace (n := d) sC _ w
      (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ) Zc hZc =
        coefficientPoint (n := d) (N := N) a)
    {ι : Type u} [Fintype ι] [DecidableEq ι] [IsSeparated sU] [Smooth sU]
    (K : CurveMapCharts.ChartCover f ι) (l : ι → Fin (d + 1))
    (hσC : ∀ t, K.UC t ≤ nvCover (pullbackCoordSection.{u} ((f ≫ j ≫ i) ≫
      projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))) (l t))
    [IsInvertibleModule U ((Scheme.Modules.pullback ((j ≫ i) ≫
      projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
        (twistingSheafAtUniverse.{u} d))]
    (hσU : ∀ t, K.WU t ≤ nvCover (pullbackCoordSection.{u} ((j ≫ i) ≫
      projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))) (l t)) :
    letI := MMP.Mori.stalkAlgebra (finalSpace.over (n := d) sC _ w
      (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ) Zc hZc) (m (IsLocalRing.closedPoint k))
    Nonempty (ChartPoints k
      ((curveMapSpace (n := d) sC _ w F dd w' ℓ c μ Zc hZc).presheaf.stalk
        (m (IsLocalRing.closedPoint k)))
      (CurveMapCharts.curveCharts sC sU K hf (fun β => (P β).base (IsLocalRing.closedPoint k)))
      d N
      (fun m' i' => CurveMapCharts.chartCoord _ K.WU l hσU m' i')
      (fun i' m' => CurveMapCharts.localSection sC sU hf K
        (fun β => (P β).base (IsLocalRing.closedPoint k)) _ l hσC (w m') i')
      μ) := by
  letI := MMP.Mori.stalkAlgebra (finalSpace.over (n := d) sC _ w
    (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ) Zc hZc) (m (IsLocalRing.closedPoint k))
  haveI : IsProper sC := (inferInstance : IsProperVariety k sC).toIsProper
  choose pt hframe using fun A => exists_curvePoint_frames k sC sU (n := n) f hf P hP hPinj i j
    hij w a hτ F dd w' hhom hJ ℓ c μ hc hμ v hv Zc hZc hZc' hZ Φ hΦ m hm hma K l hσC hσU A
  have hloc := curveMapConditions_of_local k sC sU (n := n) f hf P hP hPinj i j hij w a
    hτ F dd w' hhom hJ ℓ c μ hc hμ v hv Zc hZc hZc' hZ Φ hΦ m hm hma K l hσC hσU
  have hf' : (f ≫ j ≫ i) ≫ pullback.fst (terminal.from (Spec (.of k)))
      (terminal.from (projectiveSpaceAtUniverse.{u} d)) = sC := by
    rw [Category.assoc, Category.assoc, hij, hf]
  have ha : ∀ {A : ArtinLocalAlgebra k} (a' : ((curveMapSpace (n := d) sC _ w F dd w' ℓ c μ Zc
      hZc).presheaf.stalk (m (IsLocalRing.closedPoint k))) →ₐ[k] A.carrier),
      a'.toRingHom.comp (stalkAlgebraMap (finalSpace.over (n := d) sC _ w
        (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ) Zc hZc)
          (m (IsLocalRing.closedPoint k))) = algebraMap k A.carrier :=
    fun a' => RingHom.ext a'.commutes
  refine ⟨{ pt := fun {A} a' => pt A a'
            coeff := fun a' => stalkPointCoeff sC _ w
              (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ) Zc hZc
              (m (IsLocalRing.closedPoint k)) a'.toRingHom
            frame := fun {A} a' t => hframe A a' t
            μ_coeff := fun {A} a' => sum_mul_eq_one_of_normalizationFunction A _ μ
              (stalkPointCoeff_mem_conditions sC _ w
                (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ) Zc hZc a
                (f ≫ j ≫ i) hf' (𝟙 _) hτ hZ m hm hma _ rfl A a'.toRingHom (ha a')
                (Sum.inr (Sum.inr ())))
            Good := fun B c' => ∀ q', ((artinCoefficientPoint B) c').appTop
              (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ q') = 0
            good_of_local := fun B c' y fr hy hfix hμ' q' => by
              obtain ⟨heq, hprop⟩ := hloc B c' y fr hy hfix
              rcases q' with ⟨α, j'⟩ | ⟨β, i₁, i₂⟩ | ⟨⟩
              · exact heq α j'
              · exact hprop β i₁ i₂
              · exact normalizationFunction_eq_zero_of_sum_mul_eq_one B c' μ hμ'
            lift := fun {A} E a' c' hc' hq => ?_ }⟩
  obtain ⟨b', hb1, hb2⟩ := exists_stalk_lift_finalSpace sC _ w
    (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ) Zc hZc a (f ≫ j ≫ i) hf' (𝟙 _) hτ hZ m hm
    hma _ rfl A E.big E.π a'.toRingHom (ha a') c' hc' hq
  refine ⟨{ toRingHom := b', commutes' := fun r => congrArg (fun φ => φ r) hb1 }, ?_⟩
  exact AlgHom.ext fun r => congrArg (fun φ => φ r) hb2

/-- **The chart system of `M` at `[f]`**, with obstruction spaces `H¹(C, f^* T_U(-B))` and
`H¹(C, 𝒪_C)`. -/
private theorem exists_chartSystem (k : Type u) [Field k] [IsAlgClosed k]
    {C U : Scheme.{u}} (sC : C ⟶ Spec (.of k)) (sU : U ⟶ Spec (.of k))
    [IsProjectiveVariety k sC] [IsCurve k sC] [Smooth sC]
    {n : ℕ} [IsQuasiProjectiveVariety k sU] [SmoothOfRelativeDimension n sU]
    (f : C ⟶ U) (hf : f ≫ sU = sC)
    {b : ℕ} (P : Fin b → (Spec (.of k) ⟶ C)) (hP : ∀ i, P i ≫ sC = 𝟙 _)
    (hPinj : Function.Injective P)
    [((Scheme.Modules.pullback f).obj (dualSheaf sU.relativeDifferentials)).IsCoherent]
    [(SheafOfModules.unit C.ringCatSheaf).IsCoherent]
    {d : ℕ} {Z : Scheme.{u}} (i : Z ⟶ projectiveSpaceOverRing d (CommRingCat.of k))
    [IsClosedImmersion i] (j : U ⟶ Z) [IsOpenImmersion j]
    (hij : j ≫ i ≫ pullback.fst (terminal.from (Spec (.of k)))
        (terminal.from (projectiveSpaceAtUniverse.{u} d)) = sU)
    [IsInvertibleModule C ((Scheme.Modules.pullback ((f ≫ j ≫ i) ≫
      projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
        (twistingSheafAtUniverse.{u} d))]
    {N : ℕ} (w : letI := baseModule sC ((Scheme.Modules.pullback ((f ≫ j ≫ i) ≫
      projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
        (twistingSheafAtUniverse.{u} d)) ⊤;
      Module.Basis (Fin N) Γ(Spec (.of k), ⊤) Γ((Scheme.Modules.pullback ((f ≫ j ≫ i) ≫
        projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
          (twistingSheafAtUniverse.{u} d), ⊤))
    (a : Fin (d + 1) → Fin N → k)
    (hτ : ∀ i', pullbackCoordSection.{u} ((f ≫ j ≫ i) ≫
        projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k))) i' =
      ∑ j', sC.appTop ((Scheme.ΓSpecIso (.of k)).inv (a i' j')) • w j')
    {ιE : Type} (F : ιE → MvPolynomial (Fin (d + 1)) k) (dd : ιE → ℕ) {N' : ιE → ℕ}
    (w' : ∀ α, letI := baseModule sC (Stacks.TensorPowers.natTensorPow
        ((Scheme.Modules.pullback ((f ≫ j ≫ i) ≫
          projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
          (twistingSheafAtUniverse.{u} d)) (dd α)) ⊤;
      Module.Basis (Fin (N' α)) Γ(Spec (.of k), ⊤)
        Γ(Stacks.TensorPowers.natTensorPow ((Scheme.Modules.pullback ((f ≫ j ≫ i) ≫
          projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
          (twistingSheafAtUniverse.{u} d)) (dd α), ⊤))
    (hhom : ∀ α, (F α).IsHomogeneous (dd α))
    (hJ : (closedSubschemeIdeal i).toIdeal = Ideal.span (Set.range F))
    (ℓ : Fin b → Fin N → k) (c : Fin b → Fin (d + 1) → k) (μ : Fin (d + 1) → Fin N → k)
    (hc : ∀ β i', c β i' = ∑ j', ℓ β j' * a i' j')
    (hμ : ∑ i', ∑ j', μ i' j' * a i' j' = 1)
    (v : ∀ β, Γ((Scheme.Modules.pullback (P β)).obj ((Scheme.Modules.pullback ((f ≫ j ≫ i) ≫
      projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
        (twistingSheafAtUniverse.{u} d)), ⊤))
    (hv : ∀ β j', AlgebraicGeometry.pullbackGlobalSections (P β) ((Scheme.Modules.pullback
      ((f ≫ j ≫ i) ≫ projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
        (twistingSheafAtUniverse.{u} d)) (w j') = (Scheme.ΓSpecIso (.of k)).inv (ℓ β j') • v β)
    (Zc : Set (projectiveSpaceOver d (Spec (.of k)))) (hZc : IsClosed Zc)
    (hZc' : ∀ z : Z, z ∉ Set.range j.base → i.base z ∈ Zc)
    (hZ : ∀ x : C, (f ≫ j ≫ i).base x ∉ Zc)
    (Φ : pullback sC (finalSpace.over (n := d) sC _ w
      (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ) Zc hZc) ⟶ U)
    (hΦ : Φ ≫ j ≫ i = finalFamily (n := d) sC _ w
      (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ) Zc hZc)
    (m : Spec (.of k) ⟶ curveMapSpace (n := d) sC _ w F dd w' ℓ c μ Zc hZc)
    (hm : m ≫ finalSpace.over (n := d) sC _ w
      (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ) Zc hZc = 𝟙 (Spec (.of k)))
    (hma : m ≫ finalSpace.toCoefficientSpace (n := d) sC _ w
      (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ) Zc hZc =
        coefficientPoint (n := d) (N := N) a) :
    letI := MMP.Mori.stalkAlgebra (finalSpace.over (n := d) sC _ w
      (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ) Zc hZc) (m (IsLocalRing.closedPoint k))
    Nonempty (ChartSystem k
      ((curveMapSpace (n := d) sC _ w F dd w' ℓ c μ Zc hZc).presheaf.stalk
        (m (IsLocalRing.closedPoint k)))
      (cohomologyOverField k sC (markedTangentSheaf sU f P) 1)
      (cohomologyOverField k sC (SheafOfModules.unit C.ringCatSheaf) 1) d N) := by
  letI := MMP.Mori.stalkAlgebra (finalSpace.over (n := d) sC _ w
    (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ) Zc hZc) (m (IsLocalRing.closedPoint k))
  have hvarC : IsVariety k sC := inferInstance
  have hvarU : IsVariety k sU := inferInstance
  haveI : IsSeparated sC := hvarC.toIsSeparated
  haveI : IsSeparated sU := hvarU.toIsSeparated
  haveI : Smooth sU := SmoothOfRelativeDimension.smooth n sU
  haveI : IsProper sC := (inferInstance : IsProperVariety k sC).toIsProper
  haveI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace sC
  let gU := (j ≫ i) ≫ projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k))
  haveI : IsInvertibleModule U ((Scheme.Modules.pullback gU).obj (twistingSheafAtUniverse.{u} d)) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback gU (twistingSheafAtUniverse.{u} d)
  obtain ⟨r, K, l', hσC, hσU⟩ := exists_chartCover_le_nvCover f gU
    ((f ≫ j ≫ i) ≫ projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))
    (by simp only [gU, Category.assoc])
  let pts : Fin b → C := fun β => (P β).base (IsLocalRing.closedPoint k)
  obtain ⟨θG⟩ := nonempty_derivPresheafB_h1Equiv k sC sU (n := n) f hf P hP hPinj K
  obtain ⟨CP⟩ := nonempty_chartPoints k sC sU (n := n) f hf P hP hPinj i j hij w a hτ F dd w'
    hhom hJ ℓ c μ hc hμ v hv Zc hZc hZc' hZ Φ hΦ m hm hma K l' hσC hσU
  exact ⟨{ ι := ULift.{u} (Fin r)
           Ch := CurveMapCharts.curveCharts sC sU K hf pts
           θG := θG
           θO := CurveMapCharts.ringPresheafH1Equiv sC sU hf K pts
           l := l'
           x := fun m' t => CurveMapCharts.chartCoord _ K.WU l' hσU m' t
           x_self := fun t => CurveMapCharts.chartCoord_self _ _ _ _ t
           t := CurveMapCharts.chartTrans _ K.WU l' hσU
           x_trans := fun m' s t => CurveMapCharts.chartCoord_trans _ _ _ _ m' s t
           t_cocycle := CurveMapCharts.chartTrans_cocycle _ _ _ _
           w := fun t m' => CurveMapCharts.localSection sC sU hf K pts _ l' hσC (w m') t
           g := CurveMapCharts.localTrans sC sU hf K pts _ l' hσC
           g_cocycle := CurveMapCharts.chartTrans_cocycle _ _ _ _
           w_trans := fun s t m' => CurveMapCharts.chartLocal_trans _ _ _ _ (w m') s t
           glue := fun B u hu =>
             CurveMapCharts.exists_glue_curveCharts sC sU hf K pts _ l' hσC w B.carrier u hu
           glue_unique := fun B c' hc' =>
             CurveMapCharts.glue_unique_curveCharts sC sU hf K pts _ l' hσC w B.carrier c' hc'
           pt := CP.pt
           coeff := CP.coeff
           frame := CP.frame
           μ := μ
           μ_coeff := CP.μ_coeff
           Good := CP.Good
           good_of_local := CP.good_of_local
           lift := CP.lift }⟩

/-- **The two-stage obstruction theory of `M` at `[f]`**, with obstruction spaces
`H¹(C, f^* T_U(-B))` and `H¹(C, 𝒪_C)`. -/
private theorem nonempty_twoStageObstructionTheory (k : Type u) [Field k] [IsAlgClosed k]
    {C U : Scheme.{u}} (sC : C ⟶ Spec (.of k)) (sU : U ⟶ Spec (.of k))
    [IsProjectiveVariety k sC] [IsCurve k sC] [Smooth sC]
    {n : ℕ} [IsQuasiProjectiveVariety k sU] [SmoothOfRelativeDimension n sU]
    (f : C ⟶ U) (hf : f ≫ sU = sC)
    {b : ℕ} (P : Fin b → (Spec (.of k) ⟶ C)) (hP : ∀ i, P i ≫ sC = 𝟙 _)
    (hPinj : Function.Injective P)
    [((Scheme.Modules.pullback f).obj (dualSheaf sU.relativeDifferentials)).IsCoherent]
    [(SheafOfModules.unit C.ringCatSheaf).IsCoherent]
    {d : ℕ} {Z : Scheme.{u}} (i : Z ⟶ projectiveSpaceOverRing d (CommRingCat.of k))
    [IsClosedImmersion i] (j : U ⟶ Z) [IsOpenImmersion j]
    (hij : j ≫ i ≫ pullback.fst (terminal.from (Spec (.of k)))
        (terminal.from (projectiveSpaceAtUniverse.{u} d)) = sU)
    [IsInvertibleModule C ((Scheme.Modules.pullback ((f ≫ j ≫ i) ≫
      projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
        (twistingSheafAtUniverse.{u} d))]
    {N : ℕ} (w : letI := baseModule sC ((Scheme.Modules.pullback ((f ≫ j ≫ i) ≫
      projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
        (twistingSheafAtUniverse.{u} d)) ⊤;
      Module.Basis (Fin N) Γ(Spec (.of k), ⊤) Γ((Scheme.Modules.pullback ((f ≫ j ≫ i) ≫
        projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
          (twistingSheafAtUniverse.{u} d), ⊤))
    (a : Fin (d + 1) → Fin N → k)
    (hτ : ∀ i', pullbackCoordSection.{u} ((f ≫ j ≫ i) ≫
        projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k))) i' =
      ∑ j', sC.appTop ((Scheme.ΓSpecIso (.of k)).inv (a i' j')) • w j')
    {ιE : Type} (F : ιE → MvPolynomial (Fin (d + 1)) k) (dd : ιE → ℕ) {N' : ιE → ℕ}
    (w' : ∀ α, letI := baseModule sC (Stacks.TensorPowers.natTensorPow
        ((Scheme.Modules.pullback ((f ≫ j ≫ i) ≫
          projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
          (twistingSheafAtUniverse.{u} d)) (dd α)) ⊤;
      Module.Basis (Fin (N' α)) Γ(Spec (.of k), ⊤)
        Γ(Stacks.TensorPowers.natTensorPow ((Scheme.Modules.pullback ((f ≫ j ≫ i) ≫
          projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
          (twistingSheafAtUniverse.{u} d)) (dd α), ⊤))
    (hhom : ∀ α, (F α).IsHomogeneous (dd α))
    (hJ : (closedSubschemeIdeal i).toIdeal = Ideal.span (Set.range F))
    (ℓ : Fin b → Fin N → k) (c : Fin b → Fin (d + 1) → k) (μ : Fin (d + 1) → Fin N → k)
    (hc : ∀ β i', c β i' = ∑ j', ℓ β j' * a i' j')
    (hμ : ∑ i', ∑ j', μ i' j' * a i' j' = 1)
    (v : ∀ β, Γ((Scheme.Modules.pullback (P β)).obj ((Scheme.Modules.pullback ((f ≫ j ≫ i) ≫
      projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
        (twistingSheafAtUniverse.{u} d)), ⊤))
    (hv : ∀ β j', AlgebraicGeometry.pullbackGlobalSections (P β) ((Scheme.Modules.pullback
      ((f ≫ j ≫ i) ≫ projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
        (twistingSheafAtUniverse.{u} d)) (w j') = (Scheme.ΓSpecIso (.of k)).inv (ℓ β j') • v β)
    (Zc : Set (projectiveSpaceOver d (Spec (.of k)))) (hZc : IsClosed Zc)
    (hZc' : ∀ z : Z, z ∉ Set.range j.base → i.base z ∈ Zc)
    (hZ : ∀ x : C, (f ≫ j ≫ i).base x ∉ Zc)
    (Φ : pullback sC (finalSpace.over (n := d) sC _ w
      (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ) Zc hZc) ⟶ U)
    (hΦ : Φ ≫ j ≫ i = finalFamily (n := d) sC _ w
      (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ) Zc hZc)
    (m : Spec (.of k) ⟶ curveMapSpace (n := d) sC _ w F dd w' ℓ c μ Zc hZc)
    (hm : m ≫ finalSpace.over (n := d) sC _ w
      (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ) Zc hZc = 𝟙 (Spec (.of k)))
    (hma : m ≫ finalSpace.toCoefficientSpace (n := d) sC _ w
      (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ) Zc hZc =
        coefficientPoint (n := d) (N := N) a) :
    Nonempty (@TwoStageObstructionTheory.{u, u, u} k _
        ((curveMapSpace (n := d) sC _ w F dd w' ℓ c μ Zc hZc).presheaf.stalk
            (m (IsLocalRing.closedPoint k))) _
        (MMP.Mori.stalkAlgebra (finalSpace.over (n := d) sC _ w
          (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ) Zc hZc)
          (m (IsLocalRing.closedPoint k)))
        (cohomologyOverField k sC (markedTangentSheaf sU f P) 1)
        (cohomologyOverField k sC (SheafOfModules.unit C.ringCatSheaf) 1) _ _ _ _) := by
  letI := MMP.Mori.stalkAlgebra (finalSpace.over (n := d) sC _ w
    (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ) Zc hZc) (m (IsLocalRing.closedPoint k))
  obtain ⟨CS⟩ := exists_chartSystem k sC sU (n := n) f hf P hP hPinj i j hij w a
    hτ F dd w' hhom hJ ℓ c μ hc hμ v hv Zc hZc hZc' hZ Φ hΦ m hm hma
  exact nonempty_theory_of_chartSystem CS

/-- **First-order tuples at `[f]`**: a subspace `V` of the tuples `v` with `a + ε v` satisfying the
closed conditions of `M` over `k[ε]`, of dimension at least `h⁰(C, f^* T_U(-B)) - h¹(C, 𝒪_C)`.
A global section of `f^* T_U(-B)` is a compatible family of derivations `D_t` of the charts; on
the kernel of its obstruction class `[D(t_{ij})/t_{ij}] ∈ Ȟ¹(𝒪_C)` the local expressions
`φ_t f(x_m) + D_t(x_m)` glue to a tuple `v`, normalized by `μ`, and `f + ε D_t` with the frames
`1 + ε φ_t` satisfies the closed conditions by `curveMapConditions_of_local`. -/
private theorem exists_tangentSubspace_curveMapSpace (k : Type u) [Field k] [IsAlgClosed k]
    {C U : Scheme.{u}} (sC : C ⟶ Spec (.of k)) (sU : U ⟶ Spec (.of k))
    [IsProjectiveVariety k sC] [IsCurve k sC] [Smooth sC]
    {n : ℕ} [IsQuasiProjectiveVariety k sU] [SmoothOfRelativeDimension n sU]
    (f : C ⟶ U) (hf : f ≫ sU = sC)
    {b : ℕ} (P : Fin b → (Spec (.of k) ⟶ C)) (hP : ∀ i, P i ≫ sC = 𝟙 _)
    (hPinj : Function.Injective P)
    [((Scheme.Modules.pullback f).obj (dualSheaf sU.relativeDifferentials)).IsCoherent]
    [(SheafOfModules.unit C.ringCatSheaf).IsCoherent]
    {d : ℕ} {Z : Scheme.{u}} (i : Z ⟶ projectiveSpaceOverRing d (CommRingCat.of k))
    [IsClosedImmersion i] (j : U ⟶ Z) [IsOpenImmersion j]
    (hij : j ≫ i ≫ pullback.fst (terminal.from (Spec (.of k)))
        (terminal.from (projectiveSpaceAtUniverse.{u} d)) = sU)
    [IsInvertibleModule C ((Scheme.Modules.pullback ((f ≫ j ≫ i) ≫
      projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
        (twistingSheafAtUniverse.{u} d))]
    {N : ℕ} (w : letI := baseModule sC ((Scheme.Modules.pullback ((f ≫ j ≫ i) ≫
      projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
        (twistingSheafAtUniverse.{u} d)) ⊤;
      Module.Basis (Fin N) Γ(Spec (.of k), ⊤) Γ((Scheme.Modules.pullback ((f ≫ j ≫ i) ≫
        projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
          (twistingSheafAtUniverse.{u} d), ⊤))
    (a : Fin (d + 1) → Fin N → k)
    (hτ : ∀ i', pullbackCoordSection.{u} ((f ≫ j ≫ i) ≫
        projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k))) i' =
      ∑ j', sC.appTop ((Scheme.ΓSpecIso (.of k)).inv (a i' j')) • w j')
    {ιE : Type} (F : ιE → MvPolynomial (Fin (d + 1)) k) (dd : ιE → ℕ) {N' : ιE → ℕ}
    (w' : ∀ α, letI := baseModule sC (Stacks.TensorPowers.natTensorPow
        ((Scheme.Modules.pullback ((f ≫ j ≫ i) ≫
          projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
          (twistingSheafAtUniverse.{u} d)) (dd α)) ⊤;
      Module.Basis (Fin (N' α)) Γ(Spec (.of k), ⊤)
        Γ(Stacks.TensorPowers.natTensorPow ((Scheme.Modules.pullback ((f ≫ j ≫ i) ≫
          projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
          (twistingSheafAtUniverse.{u} d)) (dd α), ⊤))
    (hhom : ∀ α, (F α).IsHomogeneous (dd α))
    (hJ : (closedSubschemeIdeal i).toIdeal = Ideal.span (Set.range F))
    (ℓ : Fin b → Fin N → k) (c : Fin b → Fin (d + 1) → k) (μ : Fin (d + 1) → Fin N → k)
    (hc : ∀ β i', c β i' = ∑ j', ℓ β j' * a i' j')
    (hμ : ∑ i', ∑ j', μ i' j' * a i' j' = 1)
    (v : ∀ β, Γ((Scheme.Modules.pullback (P β)).obj ((Scheme.Modules.pullback ((f ≫ j ≫ i) ≫
      projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
        (twistingSheafAtUniverse.{u} d)), ⊤))
    (hv : ∀ β j', AlgebraicGeometry.pullbackGlobalSections (P β) ((Scheme.Modules.pullback
      ((f ≫ j ≫ i) ≫ projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
        (twistingSheafAtUniverse.{u} d)) (w j') = (Scheme.ΓSpecIso (.of k)).inv (ℓ β j') • v β)
    (Zc : Set (projectiveSpaceOver d (Spec (.of k)))) (hZc : IsClosed Zc)
    (hZc' : ∀ z : Z, z ∉ Set.range j.base → i.base z ∈ Zc)
    (hZ : ∀ x : C, (f ≫ j ≫ i).base x ∉ Zc)
    (Φ : pullback sC (finalSpace.over (n := d) sC _ w
      (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ) Zc hZc) ⟶ U)
    (hΦ : Φ ≫ j ≫ i = finalFamily (n := d) sC _ w
      (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ) Zc hZc)
    (m : Spec (.of k) ⟶ curveMapSpace (n := d) sC _ w F dd w' ℓ c μ Zc hZc)
    (hm : m ≫ finalSpace.over (n := d) sC _ w
      (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ) Zc hZc = 𝟙 (Spec (.of k)))
    (hma : m ≫ finalSpace.toCoefficientSpace (n := d) sC _ w
      (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ) Zc hZc =
        coefficientPoint (n := d) (N := N) a) :
    ∃ V : Submodule k (Fin (d + 1) × Fin N → k),
      (Module.finrank k (cohomologyOverField k sC (markedTangentSheaf sU f P) 0) : ℤ) -
          Module.finrank k (cohomologyOverField k sC (SheafOfModules.unit C.ringCatSheaf) 1) ≤
        Module.finrank k V ∧
      ∀ v ∈ V, ∀ i', (dualTuple (fun i'' j'' => TrivSqZeroExt.inl (a i'' j'') +
        TrivSqZeroExt.inr (v (i'', j'')))).appTop
          (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ i') = 0 := by
  classical
  have hvarC : IsVariety k sC := inferInstance
  have hvarU : IsVariety k sU := inferInstance
  haveI : IsSeparated sC := hvarC.toIsSeparated
  haveI : IsSeparated sU := hvarU.toIsSeparated
  haveI : Smooth sU := SmoothOfRelativeDimension.smooth n sU
  haveI : IsProper sC := (inferInstance : IsProperVariety k sC).toIsProper
  haveI : LocallyOfFiniteType sC := hvarC.toLocallyOfFiniteType
  haveI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace sC
  let gU := (j ≫ i) ≫ projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k))
  haveI : IsInvertibleModule U ((Scheme.Modules.pullback gU).obj (twistingSheafAtUniverse.{u} d)) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback gU (twistingSheafAtUniverse.{u} d)
  obtain ⟨r, K, l', hσC, hσU⟩ := exists_chartCover_le_nvCover f gU
    ((f ≫ j ≫ i) ≫ projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))
    (by simp only [gU, Category.assoc])
  let pts : Fin b → C := fun β => (P β).base (IsLocalRing.closedPoint k)
  -- the derivations of the charts attached to the sections of `G = f^* T_U(-B)`
  haveI := MMP.Fourfold.CurveMapDerivations.isQuasicoherent_relativeDifferentials sU
  haveI := MMP.Fourfold.CurveMapDerivations.isQuasicoherent_dualSheaf_relativeDifferentials sU n
  haveI : ((Scheme.Modules.pullback f).obj (dualSheaf sU.relativeDifferentials)).IsQuasicoherent :=
    isQuasicoherent_of_isCoherent _
  haveI := isClosedImmersion_markedPointsMap P sC hP hPinj
  haveI := MMP.Fourfold.CurveMapDerivations.isQuasicoherent_idealSheafModule
    (markedPointsMap P).ker.subschemeι
  obtain ⟨Ψ, hΨ, hnat⟩ := MMP.Fourfold.CurveMapDerivations.exists_derivationMaps_curveCharts sC sU
    hf K pts (markedPointsMap P).ker.subschemeι (idealSheafSections_markedPoints P)
  let Ch := CurveMapCharts.curveCharts sC sU K hf pts
  obtain ⟨hGc, -⟩ := eulerCharacteristic_markedTangentSheaf (n := n) sC sU f P hP hPinj
  letI := Stacks.Cech.sectionsModule sC (markedTangentSheaf sU f P) ⊤
  have hH0 : FiniteDimensional k Γ(markedTangentSheaf sU f P, ⊤) ∧
      Module.finrank k Γ(markedTangentSheaf sU f P, ⊤) =
        Module.finrank k (cohomologyOverField k sC (markedTangentSheaf sU f P) 0) := by
    have := finiteDimensional_cohomologyOverField_of_isProper k sC (markedTangentSheaf sU f P) 0
    have e := (cohomologyOverFieldZeroLinearIso k sC (markedTangentSheaf sU f P)).toLinearEquiv
    have key : ∀ φ : k →+* Γ(C, ⊤),
        φ = ((Scheme.ΓSpecIso (.of k)).inv ≫ sC.appLE ⊤ ⊤ (by simp)).hom →
          (letI := Module.compHom Γ(markedTangentSheaf sU f P, ⊤) φ
           FiniteDimensional k Γ(markedTangentSheaf sU f P, ⊤) ∧
            Module.finrank k Γ(markedTangentSheaf sU f P, ⊤) =
              Module.finrank k (cohomologyOverField k sC (markedTangentSheaf sU f P) 0)) := by
      rintro φ rfl
      exact ⟨Module.Finite.equiv e, e.finrank_eq.symm⟩
    refine key _ ?_
    rw [Stacks.Cech.baseRingHom_eq_appLE sC ⊤ (by simp)]
    rfl
  haveI := hH0.1
  let δ : ∀ s : Finset (ULift.{u} (Fin r)), s.Nonempty →
      Γ(markedTangentSheaf sU f P, ⊤) →ₗ[k] Derivation k (Ch.S s) (Ch.𝔟 s) := fun s hs =>
    (Ψ s hs).comp (Stacks.Cech.sectionsRestrₗ sC (markedTangentSheaf sU f P)
      (le_top : s.inf K.UC ≤ ⊤))
  have hδ : ∀ X, MMP.Fourfold.CurveMapDerivations.IsCompatibleDerivations Ch
      (fun s hs => δ s hs X) := by
    intro X s t h hs
    exact (hnat s t h hs (Stacks.Cech.sectionsRestrₗ sC (markedTangentSheaf sU f P)
      (le_top : s.inf K.UC ≤ ⊤) X)).symm.trans
      (congrArg (Ψ t (hs.mono h)) (CechCochains.restr_restr _ _ _ X))
  have hinj : ∀ X, (∀ t, δ {t} (Finset.singleton_nonempty t) X = 0) → X = 0 := by
    intro X hX
    have h1 : ∀ t, CechCochains.restr (markedTangentSheaf sU f P).presheaf
        (le_top : ({t} : Finset (ULift.{u} (Fin r))).inf K.UC ≤ ⊤) X = 0 := fun t =>
      (hΨ {t} (Finset.singleton_nonempty t)).1 ((hX t).trans
        (map_zero (Ψ {t} (Finset.singleton_nonempty t))).symm)
    refine TopCat.Sheaf.eq_of_locally_eq' ⟨(markedTangentSheaf sU f P).presheaf,
      (markedTangentSheaf sU f P).isSheaf⟩ (fun t => ({t} : Finset (ULift.{u} (Fin r))).inf K.UC)
      ⊤ (fun t => homOfLE le_top) ?_ X 0 fun t => ?_
    · rw [K.cover]
      exact iSup_le fun t => le_iSup_of_le t (by rw [Finset.inf_singleton])
    · exact (h1 t).trans (map_zero _).symm
  -- the chart data at `[f]`
  have hf0x : ∀ t m', Ch.f0 {t} (CurveMapCharts.chartCoord _ K.WU l' hσU m' t) =
      CurveMapCharts.chartLocal _ K.UC l' hσC (pullbackCoordSection.{u} ((f ≫ j ≫ i) ≫
        projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k))) m') t := by
    intro t m'
    change f.appLE _ _ (K.le_inf {t}) (Stacks.ProjectiveFromSections.resO _ (div _ le_rfl
      (resT _ _))) = div _ _ (resT _ _)
    rw [CurveMapCharts.resO_div, resM_resT]
    exact appLE_div_pullbackCoordSection f ((j ≫ i) ≫
      projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k))) _ (by simp only [Category.assoc])
      (K.le_inf {t}) (l' t) m' _ _
  have ha : ∀ t m', ∑ n, a m' n • CurveMapCharts.localSection sC sU hf K pts _ l' hσC (w n) t =
      Ch.f0 {t} (CurveMapCharts.chartCoord _ K.WU l' hσU m' t) := by
    intro t m'
    rw [hf0x, hτ m', CurveMapCharts.chartLocal_sum_coefficients sC sU hf K _ _ l' hσC w]
  have hf0T : ∀ i₁ i₂, Ch.f0 {i₁, i₂} (CurveMapCharts.chartTrans _ K.WU l' hσU i₁ i₂).val =
      (CurveMapCharts.localTrans sC sU hf K pts _ l' hσC i₁ i₂ :
        Ch.O {i₁, i₂}) := by
    intro i₁ i₂
    change f.appLE _ _ (K.le_inf {i₁, i₂}) (Stacks.ProjectiveFromSections.resO _ (div _ le_rfl
      (resT _ _))) = Stacks.ProjectiveFromSections.resO _ (div _ le_rfl (resT _ _))
    rw [CurveMapCharts.resO_div, CurveMapCharts.resO_div, resM_resT, resM_resT]
    exact appLE_div_pullbackCoordSection f ((j ≫ i) ≫
      projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k))) _ (by simp only [Category.assoc])
      (K.le_inf {i₁, i₂}) (l' i₁) (l' i₂) _ _
  have hglue : ∀ u : ∀ t, Ch.O {t}, (∀ i₁ i₂, Ch.ρ (CechPresheaf.sub_pair_left i₁ i₂) (u i₁) =
        Ch.f0 {i₁, i₂} (CurveMapCharts.chartTrans _ K.WU l' hσU i₁ i₂).val *
          Ch.ρ (CechPresheaf.sub_pair_right i₁ i₂) (u i₂)) →
      ∃ cc : Fin N → k, ∀ t, u t =
        ∑ n, cc n • CurveMapCharts.localSection sC sU hf K pts _ l' hσC (w n) t := by
    intro u hu
    obtain ⟨cc, hcc⟩ := CurveMapCharts.exists_glue_curveCharts sC sU hf K pts _ l' hσC w k
      (fun t => u t ⊗ₜ[k] (1 : k)) fun i₁ i₂ => by
        simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
          Algebra.TensorProduct.tmul_mul_tmul, mul_one]
        rw [← hf0T]
        exact congrArg (· ⊗ₜ[k] (1 : k)) (hu i₁ i₂)
    refine ⟨cc, fun t => ?_⟩
    have := congrArg (TensorProduct.rid k _) (hcc t)
    simpa [map_sum] using this
  have hglue_unique : ∀ cc : Fin N → k, (∀ t,
      ∑ n, cc n • CurveMapCharts.localSection sC sU hf K pts _ l' hσC (w n) t = 0) → cc = 0 := by
    intro cc hcc
    refine CurveMapCharts.glue_unique_curveCharts sC sU hf K pts _ l' hσC w k cc fun t => ?_
    have e : ∀ n, CurveMapCharts.localSection sC sU hf K pts _ l' hσC (w n) t ⊗ₜ[k] cc n =
        (cc n • CurveMapCharts.localSection sC sU hf K pts _ l' hσC (w n) t) ⊗ₜ[k] (1 : k) :=
      fun n => by
        rw [← TensorProduct.smul_tmul', ← TensorProduct.tmul_smul, smul_eq_mul, mul_one]
    simp only [e, ← TensorProduct.sum_tmul, hcc t, TensorProduct.zero_tmul]
  have hxsep : ∀ t (E : Derivation k (Ch.S {t}) (Ch.𝔟 {t})),
      (∀ m', E (CurveMapCharts.chartCoord _ K.WU l' hσU m' t) = 0) → E = 0 := by
    intro t E hE
    refine MMP.Fourfold.CurveMapDerivations.eq_zero_of_dualPoint_eq Ch E ?_
    have hWl : ({t} : Finset (ULift.{u} (Fin r))).inf K.WU ≤
        nvCover (pullbackCoordSection.{u} gU) (l' t) := by
      rw [Finset.inf_singleton]
      exact hσU t
    exact MMP.Fourfold.CurveMapDerivations.algHom_ext_of_ratio sU (j ≫ i)
      (by rw [Category.assoc]; exact hij) (l' t) (K.isAffineOpen_inf_WU sU
        (Finset.singleton_nonempty t)) hWl _ _ fun m' => by
      change MMP.Fourfold.CurveMapDerivations.dualPoint Ch E
          (CurveMapCharts.chartCoord _ K.WU l' hσU m' t) =
        MMP.Fourfold.CurveMapDerivations.dualPoint Ch 0
          (CurveMapCharts.chartCoord _ K.WU l' hσU m' t)
      have e1 := MMP.Fourfold.CurveMapDerivations.dualPoint_apply Ch E
        (CurveMapCharts.chartCoord _ K.WU l' hσU m' t)
      have e2 := MMP.Fourfold.CurveMapDerivations.dualPoint_apply Ch 0
        (CurveMapCharts.chartCoord _ K.WU l' hσU m' t)
      rw [hE m'] at e1
      exact e1.trans e2.symm
  haveI := finiteDimensional_cohomologyOverField_of_isProper k sC
    (SheafOfModules.unit C.ringCatSheaf) 1
  haveI : FiniteDimensional k Ch.ringPresheaf.H1 :=
    Module.Finite.equiv (CurveMapCharts.ringPresheafH1Equiv sC sU hf K pts).symm
  obtain ⟨Vsub, hdim, hVsub⟩ := MMP.Fourfold.CurveMapDerivations.exists_tangentSubspace_of_charts
    Ch (x := fun m' t => CurveMapCharts.chartCoord _ K.WU l' hσU m' t)
    (T := CurveMapCharts.chartTrans _ K.WU l' hσU) l'
    (fun t => CurveMapCharts.chartCoord_self _ _ _ _ t)
    (fun m' i₁ i₂ => CurveMapCharts.chartCoord_trans _ _ _ _ m' i₁ i₂)
    (CurveMapCharts.chartTrans_cocycle _ _ _ _)
    (fun t n => CurveMapCharts.localSection sC sU hf K pts _ l' hσC (w n) t) hglue hglue_unique
    a ha μ hμ hxsep Γ(markedTangentSheaf sU f P, ⊤) δ hδ hinj
  refine ⟨Vsub, ?_, fun vv hvv => ?_⟩
  · rw [← hH0.2, ← (CurveMapCharts.ringPresheafH1Equiv sC sU hf K pts).finrank_eq]
    exact hdim
  obtain ⟨D, φ, heqs, hnorm⟩ := hVsub vv hvv
  let B := MMP.Fourfold.CurveMapDerivations.dualNumberArtin k
  let c' : Fin (d + 1) → Fin N → B.carrier := fun m' n =>
    (TrivSqZeroExt.inl (a m' n) + TrivSqZeroExt.inr (vv (m', n)) : DualNumber k)
  have hy : ∀ t m', ∑ j', CurveMapCharts.localSection sC sU hf K pts _ l' hσC (w j') t ⊗ₜ[k]
      c' m' j' = (MMP.Fourfold.CurveMapDerivations.dualFrame Ch (φ t) :
        Ch.O {t} ⊗[k] DualNumber k) * MMP.Fourfold.CurveMapDerivations.dualPoint Ch (D t)
          (CurveMapCharts.chartCoord _ K.WU l' hσU m' t) := fun t m' =>
    MMP.Fourfold.CurveMapDerivations.sum_tmul_eq_dualFrame_mul Ch (D t) (φ t)
      (fun n => CurveMapCharts.localSection sC sU hf K pts _ l' hσC (w n) t) (a m')
      (fun n => vv (m', n)) _ (ha t m') (heqs t m')
  obtain ⟨heq, hprop⟩ := curveMapConditions_of_local k sC sU (n := n) f hf P hP hPinj i j hij w a
    hτ F dd w' hhom hJ ℓ c μ hc hμ v hv Zc hZc hZc' hZ Φ hΦ m hm hma K l' hσC hσU B c'
    (fun t => MMP.Fourfold.CurveMapDerivations.dualPoint Ch (D t))
    (fun t => MMP.Fourfold.CurveMapDerivations.dualFrame Ch (φ t)) hy
    (fun t z => MMP.Fourfold.CurveMapDerivations.dualPoint_mod Ch (D t) z)
  have hμ' : ∑ m', ∑ j', algebraMap k B.carrier (μ m' j') * c' m' j' = 1 := by
    change ∑ m', ∑ j', algebraMap k (DualNumber k) (μ m' j') *
      (TrivSqZeroExt.inl (a m' j') + TrivSqZeroExt.inr (vv (m', j')) : DualNumber k) = 1
    refine TrivSqZeroExt.ext ?_ ?_
    · simp [TrivSqZeroExt.fst_sum, TrivSqZeroExt.algebraMap_eq_inl, hμ]
    · simp [TrivSqZeroExt.snd_sum, TrivSqZeroExt.algebraMap_eq_inl, hnorm]
  intro q'
  rcases q' with ⟨α, j'⟩ | ⟨β, i₁, i₂⟩ | ⟨⟩
  · exact heq α j'
  · exact hprop β i₁ i₂
  · exact normalizationFunction_eq_zero_of_sum_mul_eq_one B c' μ hμ'

/-- **The tangent bound at `[f]`**: the cotangent space of `𝒪_{M,[f]}` has dimension at least
`h⁰(C, f^* T_U(-B)) - h¹(C, 𝒪_C)`. -/
private theorem finrank_cohomology_sub_le_finrank_cotangentSpace (k : Type u) [Field k]
    [IsAlgClosed k]
    {C U : Scheme.{u}} (sC : C ⟶ Spec (.of k)) (sU : U ⟶ Spec (.of k))
    [IsProjectiveVariety k sC] [IsCurve k sC] [Smooth sC]
    {n : ℕ} [IsQuasiProjectiveVariety k sU] [SmoothOfRelativeDimension n sU]
    (f : C ⟶ U) (hf : f ≫ sU = sC)
    {b : ℕ} (P : Fin b → (Spec (.of k) ⟶ C)) (hP : ∀ i, P i ≫ sC = 𝟙 _)
    (hPinj : Function.Injective P)
    [((Scheme.Modules.pullback f).obj (dualSheaf sU.relativeDifferentials)).IsCoherent]
    [(SheafOfModules.unit C.ringCatSheaf).IsCoherent]
    {d : ℕ} {Z : Scheme.{u}} (i : Z ⟶ projectiveSpaceOverRing d (CommRingCat.of k))
    [IsClosedImmersion i] (j : U ⟶ Z) [IsOpenImmersion j]
    (hij : j ≫ i ≫ pullback.fst (terminal.from (Spec (.of k)))
        (terminal.from (projectiveSpaceAtUniverse.{u} d)) = sU)
    [IsInvertibleModule C ((Scheme.Modules.pullback ((f ≫ j ≫ i) ≫
      projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
        (twistingSheafAtUniverse.{u} d))]
    {N : ℕ} (w : letI := baseModule sC ((Scheme.Modules.pullback ((f ≫ j ≫ i) ≫
      projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
        (twistingSheafAtUniverse.{u} d)) ⊤;
      Module.Basis (Fin N) Γ(Spec (.of k), ⊤) Γ((Scheme.Modules.pullback ((f ≫ j ≫ i) ≫
        projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
          (twistingSheafAtUniverse.{u} d), ⊤))
    (a : Fin (d + 1) → Fin N → k)
    (hτ : ∀ i', pullbackCoordSection.{u} ((f ≫ j ≫ i) ≫
        projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k))) i' =
      ∑ j', sC.appTop ((Scheme.ΓSpecIso (.of k)).inv (a i' j')) • w j')
    {ιE : Type} (F : ιE → MvPolynomial (Fin (d + 1)) k) (dd : ιE → ℕ) {N' : ιE → ℕ}
    (w' : ∀ α, letI := baseModule sC (Stacks.TensorPowers.natTensorPow
        ((Scheme.Modules.pullback ((f ≫ j ≫ i) ≫
          projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
          (twistingSheafAtUniverse.{u} d)) (dd α)) ⊤;
      Module.Basis (Fin (N' α)) Γ(Spec (.of k), ⊤)
        Γ(Stacks.TensorPowers.natTensorPow ((Scheme.Modules.pullback ((f ≫ j ≫ i) ≫
          projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
          (twistingSheafAtUniverse.{u} d)) (dd α), ⊤))
    (hhom : ∀ α, (F α).IsHomogeneous (dd α))
    (hJ : (closedSubschemeIdeal i).toIdeal = Ideal.span (Set.range F))
    (ℓ : Fin b → Fin N → k) (c : Fin b → Fin (d + 1) → k) (μ : Fin (d + 1) → Fin N → k)
    (hc : ∀ β i', c β i' = ∑ j', ℓ β j' * a i' j')
    (hμ : ∑ i', ∑ j', μ i' j' * a i' j' = 1)
    (v : ∀ β, Γ((Scheme.Modules.pullback (P β)).obj ((Scheme.Modules.pullback ((f ≫ j ≫ i) ≫
      projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
        (twistingSheafAtUniverse.{u} d)), ⊤))
    (hv : ∀ β j', AlgebraicGeometry.pullbackGlobalSections (P β) ((Scheme.Modules.pullback
      ((f ≫ j ≫ i) ≫ projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
        (twistingSheafAtUniverse.{u} d)) (w j') = (Scheme.ΓSpecIso (.of k)).inv (ℓ β j') • v β)
    (Zc : Set (projectiveSpaceOver d (Spec (.of k)))) (hZc : IsClosed Zc)
    (hZc' : ∀ z : Z, z ∉ Set.range j.base → i.base z ∈ Zc)
    (hZ : ∀ x : C, (f ≫ j ≫ i).base x ∉ Zc)
    (Φ : pullback sC (finalSpace.over (n := d) sC _ w
      (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ) Zc hZc) ⟶ U)
    (hΦ : Φ ≫ j ≫ i = finalFamily (n := d) sC _ w
      (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ) Zc hZc)
    (m : Spec (.of k) ⟶ curveMapSpace (n := d) sC _ w F dd w' ℓ c μ Zc hZc)
    (hm : m ≫ finalSpace.over (n := d) sC _ w
      (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ) Zc hZc = 𝟙 (Spec (.of k)))
    (hma : m ≫ finalSpace.toCoefficientSpace (n := d) sC _ w
      (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ) Zc hZc =
        coefficientPoint (n := d) (N := N) a) :
    (Module.finrank k (cohomologyOverField k sC (markedTangentSheaf sU f P) 0) : ℤ) -
        Module.finrank k (cohomologyOverField k sC (SheafOfModules.unit C.ringCatSheaf) 1) ≤
      Module.finrank (IsLocalRing.ResidueField ((curveMapSpace (n := d) sC _ w F dd w' ℓ c μ Zc
          hZc).presheaf.stalk
            (m (IsLocalRing.closedPoint k))))
        (IsLocalRing.CotangentSpace ((curveMapSpace (n := d) sC _ w F dd w' ℓ c μ Zc
            hZc).presheaf.stalk
            (m (IsLocalRing.closedPoint k)))) := by
  have hvar : IsVariety k sC := inferInstance
  haveI : IsProper sC := (inferInstance : IsProperVariety k sC).toIsProper
  obtain ⟨V, hdim, hV⟩ := exists_tangentSubspace_curveMapSpace k sC sU (n := n) f hf P hP hPinj i j
    hij w a hτ F dd w' hhom hJ ℓ c μ hc hμ v hv Zc hZc hZc' hZ Φ hΦ m hm hma
  have h := finrank_le_finrank_cotangentSpace_finalSpace sC _ w _ Zc hZc a m hm hma V hV
  exact hdim.trans (by exact_mod_cast h)

/-- **The obstruction sheaf and the two-stage obstruction theory of `M` at `[f]`.**
For the coefficient space `M` of curve maps attached to `f` (through the embedding `U ⊆ Z ⊆ ℙᵈ`,
`L = f^* 𝒪(1)`, the basis `w`, the generators `F` of the ideal of `Z`, the marked-point data
`ℓ, c` and the normalization `μ`), with `[f]` the `k`-point `m`, there is a coherent sheaf `G`
(namely `f^* T_U(-B)`) with `χ(G) = χ(f^* T_U) - n b`, the cotangent space of `𝒪_{M,[f]}` has
dimension at least `h⁰(G) - h¹(𝒪_C)`, and `𝒪_{M,[f]}` carries a two-stage obstruction theory with
obstruction spaces `H¹(C, G)` and `H¹(C, 𝒪_C)`. -/
private theorem exists_obstructionSheaf (k : Type u) [Field k] [IsAlgClosed k]
    {C U : Scheme.{u}} (sC : C ⟶ Spec (.of k)) (sU : U ⟶ Spec (.of k))
    [IsProjectiveVariety k sC] [IsCurve k sC] [Smooth sC]
    {n : ℕ} [IsQuasiProjectiveVariety k sU] [SmoothOfRelativeDimension n sU]
    (f : C ⟶ U) (hf : f ≫ sU = sC)
    {b : ℕ} (P : Fin b → (Spec (.of k) ⟶ C)) (hP : ∀ i, P i ≫ sC = 𝟙 _)
    (hPinj : Function.Injective P)
    [((Scheme.Modules.pullback f).obj (dualSheaf sU.relativeDifferentials)).IsCoherent]
    [(SheafOfModules.unit C.ringCatSheaf).IsCoherent]
    {d : ℕ} {Z : Scheme.{u}} (i : Z ⟶ projectiveSpaceOverRing d (CommRingCat.of k))
    [IsClosedImmersion i] (j : U ⟶ Z) [IsOpenImmersion j]
    (hij : j ≫ i ≫ pullback.fst (terminal.from (Spec (.of k)))
        (terminal.from (projectiveSpaceAtUniverse.{u} d)) = sU)
    [IsInvertibleModule C ((Scheme.Modules.pullback ((f ≫ j ≫ i) ≫
      projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
        (twistingSheafAtUniverse.{u} d))]
    {N : ℕ} (w : letI := baseModule sC ((Scheme.Modules.pullback ((f ≫ j ≫ i) ≫
      projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
        (twistingSheafAtUniverse.{u} d)) ⊤;
      Module.Basis (Fin N) Γ(Spec (.of k), ⊤) Γ((Scheme.Modules.pullback ((f ≫ j ≫ i) ≫
        projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
          (twistingSheafAtUniverse.{u} d), ⊤))
    (a : Fin (d + 1) → Fin N → k)
    (hτ : ∀ i', pullbackCoordSection.{u} ((f ≫ j ≫ i) ≫
        projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k))) i' =
      ∑ j', sC.appTop ((Scheme.ΓSpecIso (.of k)).inv (a i' j')) • w j')
    {ιE : Type} (F : ιE → MvPolynomial (Fin (d + 1)) k) (dd : ιE → ℕ) {N' : ιE → ℕ}
    (w' : ∀ α, letI := baseModule sC (Stacks.TensorPowers.natTensorPow
        ((Scheme.Modules.pullback ((f ≫ j ≫ i) ≫
          projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
          (twistingSheafAtUniverse.{u} d)) (dd α)) ⊤;
      Module.Basis (Fin (N' α)) Γ(Spec (.of k), ⊤)
        Γ(Stacks.TensorPowers.natTensorPow ((Scheme.Modules.pullback ((f ≫ j ≫ i) ≫
          projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
          (twistingSheafAtUniverse.{u} d)) (dd α), ⊤))
    (hhom : ∀ α, (F α).IsHomogeneous (dd α))
    (hJ : (closedSubschemeIdeal i).toIdeal = Ideal.span (Set.range F))
    (ℓ : Fin b → Fin N → k) (c : Fin b → Fin (d + 1) → k) (μ : Fin (d + 1) → Fin N → k)
    (hc : ∀ β i', c β i' = ∑ j', ℓ β j' * a i' j')
    (hμ : ∑ i', ∑ j', μ i' j' * a i' j' = 1)
    (v : ∀ β, Γ((Scheme.Modules.pullback (P β)).obj ((Scheme.Modules.pullback ((f ≫ j ≫ i) ≫
      projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
        (twistingSheafAtUniverse.{u} d)), ⊤))
    (hv : ∀ β j', AlgebraicGeometry.pullbackGlobalSections (P β) ((Scheme.Modules.pullback
      ((f ≫ j ≫ i) ≫ projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
        (twistingSheafAtUniverse.{u} d)) (w j') = (Scheme.ΓSpecIso (.of k)).inv (ℓ β j') • v β)
    (Zc : Set (projectiveSpaceOver d (Spec (.of k)))) (hZc : IsClosed Zc)
    (hZc' : ∀ z : Z, z ∉ Set.range j.base → i.base z ∈ Zc)
    (hZ : ∀ x : C, (f ≫ j ≫ i).base x ∉ Zc)
    (Φ : pullback sC (finalSpace.over (n := d) sC _ w
      (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ) Zc hZc) ⟶ U)
    (hΦ : Φ ≫ j ≫ i = finalFamily (n := d) sC _ w
      (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ) Zc hZc)
    (m : Spec (.of k) ⟶ curveMapSpace (n := d) sC _ w F dd w' ℓ c μ Zc hZc)
    (hm : m ≫ finalSpace.over (n := d) sC _ w
      (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ) Zc hZc = 𝟙 (Spec (.of k)))
    (hma : m ≫ finalSpace.toCoefficientSpace (n := d) sC _ w
      (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ) Zc hZc =
        coefficientPoint (n := d) (N := N) a) :
    ∃ (G : C.Modules) (_ : G.IsCoherent),
      eulerCharacteristic k sC G = eulerCharacteristic k sC
        ((Scheme.Modules.pullback f).obj (dualSheaf sU.relativeDifferentials)) - n * b ∧
      (Module.finrank k (cohomologyOverField k sC G 0) : ℤ) -
          Module.finrank k (cohomologyOverField k sC (SheafOfModules.unit C.ringCatSheaf) 1) ≤
        Module.finrank (IsLocalRing.ResidueField ((curveMapSpace (n := d) sC _ w F dd w' ℓ c μ Zc
            hZc).presheaf.stalk (m (IsLocalRing.closedPoint k))))
          (IsLocalRing.CotangentSpace ((curveMapSpace (n := d) sC _ w F dd w' ℓ c μ Zc
            hZc).presheaf.stalk (m (IsLocalRing.closedPoint k)))) ∧
      Nonempty (@TwoStageObstructionTheory.{u, u, u} k _
        ((curveMapSpace (n := d) sC _ w F dd w' ℓ c μ Zc hZc).presheaf.stalk
          (m (IsLocalRing.closedPoint k))) _
        (MMP.Mori.stalkAlgebra (finalSpace.over (n := d) sC _ w
          (curveMapConditions (n := d) sC _ w F dd w' ℓ c μ) Zc hZc)
          (m (IsLocalRing.closedPoint k)))
        (cohomologyOverField k sC G 1)
        (cohomologyOverField k sC (SheafOfModules.unit C.ringCatSheaf) 1) _ _ _ _) := by
  obtain ⟨hG, hχ⟩ := eulerCharacteristic_markedTangentSheaf (n := n) sC sU f P hP hPinj
  exact ⟨markedTangentSheaf sU f P, hG, hχ,
    finrank_cohomology_sub_le_finrank_cotangentSpace k sC sU (n := n) f hf P hP hPinj i j hij w a
      hτ F dd w' hhom hJ ℓ c μ hc hμ v hv Zc hZc hZc' hZ Φ hΦ m hm hma,
    nonempty_twoStageObstructionTheory k sC sU (n := n) f hf P hP hPinj i j hij w a hτ F dd w'
      hhom hJ ℓ c μ hc hμ v hv Zc hZc hZc' hZ Φ hΦ m hm hma⟩

end Assembly

section Main

/-- **The dimension count.** From the obstruction sheaf `G` of `exists_obstructionSheaf`, the
two-stage obstruction bound gives `dim 𝒪_{M,[f]} ≥ (h⁰(G) - g) - h¹(G) - g = χ(f^* T_U) - n b - 2g`
(with `g = h¹(𝒪_C) = p_a(C)`). -/
private theorem toNat_le_ringKrullDim_of_obstructionSheaf (k : Type u) [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} (sC : C ⟶ Spec (.of k)) [IsProjectiveVariety k sC] [IsCurve k sC]
    [(SheafOfModules.unit C.ringCatSheaf).IsCoherent] (χ₀ : ℤ)
    {M : Scheme.{u}} (sM : M ⟶ Spec (.of k)) [LocallyOfFiniteType sM]
    (m : Spec (.of k) ⟶ M) (hm : m ≫ sM = 𝟙 _)
    (G : C.Modules) [G.IsCoherent] (hG : eulerCharacteristic k sC G = χ₀)
    (htan : (Module.finrank k (cohomologyOverField k sC G 0) : ℤ) -
          Module.finrank k (cohomologyOverField k sC (SheafOfModules.unit C.ringCatSheaf) 1) ≤
        Module.finrank (IsLocalRing.ResidueField (M.presheaf.stalk (m (IsLocalRing.closedPoint k))))
          (IsLocalRing.CotangentSpace (M.presheaf.stalk (m (IsLocalRing.closedPoint k)))))
    (T : @TwoStageObstructionTheory k _ (M.presheaf.stalk (m (IsLocalRing.closedPoint k))) _
      (MMP.Mori.stalkAlgebra sM (m (IsLocalRing.closedPoint k))) (cohomologyOverField k sC G 1)
      (cohomologyOverField k sC (SheafOfModules.unit C.ringCatSheaf) 1) _ _ _ _) :
    ((χ₀ - 2 * MMP.Mori.arithmeticGenus sC).toNat : WithBot ℕ∞) ≤
      ringKrullDim (M.presheaf.stalk (m.base default)) := by
  have hC : topologicalKrullDim C = 1 := IsCurve.topologicalKrullDim_eq_one (k := k) (f := sC)
  have hpt : m.base default = m (IsLocalRing.closedPoint k) :=
    congrArg m.base (Subsingleton.elim _ _)
  rw [hpt]
  set g := Module.finrank k (cohomologyOverField k sC (SheafOfModules.unit C.ringCatSheaf) 1)
  have hg : MMP.Mori.arithmeticGenus sC = g :=
    (finrank_cohomologyOverField_one_unit_eq_arithmeticGenus sC (le_of_eq hC)).symm
  rcases le_or_gt 0 (χ₀ - 2 * MMP.Mori.arithmeticGenus sC) with h0 | h0
  · refine le_ringKrullDim_stalk_of_twoStageObstruction sC hC.le g hg G sM m hm T htan _ ?_
    rw [Int.toNat_of_nonneg h0, hG, ← hg]
  · rw [Int.toNat_of_nonpos h0.le]
    exact_mod_cast ringKrullDim_nonneg_of_nontrivial

end Main

end

end MMP.Fourfold.Internal.FixedLineCurveMapDimension

namespace MMP.Fourfold

@[expose] public section

open MMP.Fourfold.Internal.FixedLineCurveMapDimension in
/-- Given a smooth projective curve `C` over an algebraically closed field `k`, a morphism
`f : C ⟶ U` to a smooth quasi-projective `k`-variety of dimension `n` and distinct `k`-points
`P₁, …, P_b` of `C`, there is a finite-type `k`-scheme `M`, a `k`-point `m` of `M` and a family
`F : C ×_k M ⟶ U` over `k` with `F|_{C × m} = f` and `F|_{Pᵢ × M}` constant with value `f(Pᵢ)`,
such that distinct geometric points of `M` give distinct maps, and
`dim 𝒪_{M,m} ≥ max(0, χ(C, f^* T_U) - n b - 2 g)` (mathematically `χ(C, f^* T_U(-B)) - 2g`). -/
@[mmp "lem_fourfold_fixed_line_curve_map_dimension"]
public theorem exists_fixedMarked_mapFamily_le_ringKrullDim
    (k : Type u) [Field k] [IsAlgClosed k]
    {C U : Scheme.{u}} (sC : C ⟶ Spec (.of k)) (sU : U ⟶ Spec (.of k))
    [IsProjectiveVariety k sC] [IsCurve k sC] [Smooth sC]
    {n : ℕ} [IsQuasiProjectiveVariety k sU] [SmoothOfRelativeDimension n sU]
    (f : C ⟶ U) (hf : f ≫ sU = sC)
    {b : ℕ} (P : Fin b → (Spec (.of k) ⟶ C)) (hP : ∀ i, P i ≫ sC = 𝟙 _)
    (hPinj : Function.Injective P)
    [((Scheme.Modules.pullback f).obj (dualSheaf sU.relativeDifferentials)).IsCoherent]
    [(SheafOfModules.unit C.ringCatSheaf).IsCoherent] :
    ∃ (M : Scheme.{u}) (sM : M ⟶ Spec (.of k)) (m : Spec (.of k) ⟶ M)
      (F : pullback sC sM ⟶ U) (hm : m ≫ sM = 𝟙 _),
      LocallyOfFiniteType sM ∧ QuasiCompact sM ∧
      F ≫ sU = pullback.fst sC sM ≫ sC ∧
      pullback.lift (𝟙 C) (sC ≫ m) (by simp [hm]) ≫ F = f ∧
      (∀ i, pullback.lift (sM ≫ P i) (𝟙 M) (by simp [hP i]) ≫ F = sM ≫ P i ≫ f) ∧
      (∀ (K : Type u) [Field K] [IsAlgClosed K] (t : Spec (.of K) ⟶ Spec (.of k))
          (x y : Spec (.of K) ⟶ M) (hx : x ≫ sM = t) (hy : y ≫ sM = t),
          pullback.map sC t sC sM (𝟙 C) x (𝟙 _) (by simp) (by simp [hx]) ≫ F =
            pullback.map sC t sC sM (𝟙 C) y (𝟙 _) (by simp) (by simp [hy]) ≫ F → x = y) ∧
      ((eulerCharacteristic k sC
            ((Scheme.Modules.pullback f).obj (dualSheaf sU.relativeDifferentials)) -
          n * b - 2 * MMP.Mori.arithmeticGenus sC).toNat : WithBot ℕ∞) ≤
        ringKrullDim (M.presheaf.stalk (m.base default)) := by
  classical
  obtain ⟨d, Z, i, j, hi, hj, hij⟩ := exists_openImmersion_closedImmersion k sU
  set f' : C ⟶ projectiveSpaceOver d (Spec (.of k)) := f ≫ j ≫ i with hf'_def
  have hf' : f' ≫ pullback.fst (terminal.from (Spec (.of k)))
      (terminal.from (projectiveSpaceAtUniverse.{u} d)) = sC := by
    rw [hf'_def, Category.assoc, Category.assoc, hij, hf]
  have hvar : IsVariety k sC := inferInstance
  haveI : IsIntegral C := hvar.toIsIntegral
  haveI : LocallyOfFiniteType sC := hvar.toLocallyOfFiniteType
  haveI : IsProper sC := (inferInstance : IsProperVariety k sC).toIsProper
  haveI : Nonempty C := inferInstance
  haveI : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian sC
  let L := (Scheme.Modules.pullback (f' ≫
    projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
      (twistingSheafAtUniverse.{u} d)
  haveI : IsInvertibleModule C L := Stacks.InvertiblePullback.isInvertibleModule_pullback
    (f' ≫ projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k))) (twistingSheafAtUniverse.{u} d)
  haveI : L.IsCoherent := Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isInvertible C L
  obtain ⟨N, ⟨w⟩⟩ := exists_finBasis_globalSections sC L
  let a : Fin (d + 1) → Fin N → k := fun i' =>
    coefficients sC L w (pullbackCoordSection.{u}
      (f' ≫ projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k))) i')
  have hτ₀ : ∀ i', pullbackCoordSection.{u}
      (f' ≫ projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k))) i' =
      ∑ j', sC.appTop ((Scheme.ΓSpecIso (.of k)).inv (a i' j')) • w j' := fun i' =>
    eq_sum_coefficients sC L w _
  have hτ : ∀ i', (𝟙 L : L ⟶ L).app ⊤ (pullbackCoordSection.{u}
      (f' ≫ projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k))) i') =
      ∑ j', sC.appTop ((Scheme.ΓSpecIso (.of k)).inv (a i' j')) • w j' := fun i' =>
    hτ₀ i'
  obtain ⟨P₀, hP₀⟩ := exists_section_of_isProper sC
  obtain ⟨ℓ, v, c, μ, hv, hc, hprop, hμ⟩ :=
    exists_marked_points_data_of_point sC L w f' (𝟙 L) a hτ P hP P₀ hP₀
  let Zc : Set (projectiveSpaceOver d (Spec (.of k))) := i.base '' (Set.range j.base)ᶜ
  have hZc : IsClosed Zc :=
    i.isClosedEmbedding.isClosedMap _ (IsOpenImmersion.isOpen_range j).isClosed_compl
  have hZc' : ∀ z : Z, z ∉ Set.range j.base → i.base z ∈ Zc := fun z hz => ⟨z, hz, rfl⟩
  obtain ⟨ιE, _, F, dd, N', w', hhom, hJ, Φ, hΦ⟩ :=
    exists_curveMapSpace_family sC L w ℓ c μ Zc hZc i j hZc'
  have hZ : ∀ x : C, f'.base x ∉ Zc := by
    rintro x ⟨z, hz, hzx⟩
    refine hz ⟨f.base x, i.isClosedEmbedding.injective ?_⟩
    rw [hzx, hf'_def]
    simp
  have hF := equationFunctions_coefficientPoint_eq_zero sC L w f' hf' (𝟙 L) a hτ i (f ≫ j) rfl
    F dd w' hhom hJ
  obtain ⟨m, hm, hma⟩ := exists_kPoint_curveMapSpace sC L w F dd w' ℓ c μ Zc hZc a f' hf'
    (𝟙 L) hτ hF hprop hμ hZ
  haveI : Mono (j ≫ i) := inferInstance
  refine ⟨curveMapSpace (n := d) sC L w F dd w' ℓ c μ Zc hZc,
    finalSpace.over (n := d) sC L w (curveMapConditions (n := d) sC L w F dd w' ℓ c μ) Zc hZc,
    m, Φ, hm, inferInstance, inferInstance, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : Φ ≫ sU = (Φ ≫ j ≫ i) ≫ pullback.fst (terminal.from (Spec (.of k)))
        (terminal.from (projectiveSpaceAtUniverse.{u} d)) := by
      rw [← hij]
      simp only [Category.assoc]
    rw [h1, hΦ, finalFamily_over]
  · apply (cancel_mono (j ≫ i)).1
    rw [Category.assoc, hΦ]
    exact lift_comp_finalFamily_eq sC L w _ Zc hZc a f' hf' (𝟙 L) hτ m hm hma
  · intro β
    apply (cancel_mono (j ≫ i)).1
    rw [Category.assoc, hΦ]
    simp only [Category.assoc]
    exact curveMapSpace_markedMap_comp_family sC L w F dd w' ℓ c μ Zc hZc f' hf' (𝟙 L) a hτ β
      (P β) (hP β) (v β) (hv β) (hc β)
  · intro K _ _ t x y hx hy hxy
    obtain ⟨φ, rfl⟩ : ∃ φ, Spec.map φ = t := ⟨Spec.preimage t, Spec.map_preimage t⟩
    letI : Algebra k K := φ.hom.toAlgebra
    have ht : Spec.map φ = Spec.map (CommRingCat.ofHom (algebraMap k K)) := rfl
    exact finalSpace_point_injective_of_mono (sC := sC) (L := L) (w := w) (Zc := Zc)
      (hZc := hZc) (q := curveMapConditions (n := d) sC L w F dd w' ℓ c μ) (μ' := μ)
      (hμ := ⟨Sum.inr (Sum.inr ()), rfl⟩) (m := j ≫ i) (Ψ := Φ) (hΨ := hΦ) x y
      (hx.trans ht) (hy.trans ht) hxy
  · obtain ⟨G, hGc, hχ, htan, ⟨T⟩⟩ := exists_obstructionSheaf k sC sU (n := n) f hf P hP hPinj i j
      hij w a
      hτ₀ F dd w' hhom hJ ℓ c μ hc hμ v hv Zc hZc hZc' hZ Φ hΦ m hm hma
    exact toNat_le_ringKrullDim_of_obstructionSheaf k sC _ _ m hm G hχ htan T

end

end MMP.Fourfold

end
