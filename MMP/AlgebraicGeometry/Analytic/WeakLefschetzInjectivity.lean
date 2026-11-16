module

public import MMP.AlgebraicGeometry.CohenMacaulay.SerreDuality
public import MMP.AlgebraicGeometry.MMP.Fourfold.PuncturedLocalSystem
import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.CurveAmple
import MMP.AlgebraicGeometry.Vanishing.AkizukiNakano
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.CurveRankShrinking
import MMP.AlgebraicGeometry.DeRham.BettiComparison
public import MMP.AlgebraicGeometry.Morphisms.HProjective

/-!
# Weak Lefschetz injectivity for a smooth ample divisor

Let `W` be a smooth projective complex variety of dimension `n` and `T ⊆ W` a smooth effective
Cartier divisor with `𝒪_W(T)` ample. For every `k < n`, restriction of rational singular
cohomology of the analytic spaces `H^k(W^an; ℚ) → H^k(T^an; ℚ)` is injective. For a threefold
and `k = 2` this is the degree-two weak Lefschetz theorem.

The proof works without a general Lefschetz theorem. Twist the residue sequences
`0 → Ω_W^a(-T) → Ω_W^a(log T)(-T) → Ω_T^{a-1}(-T) → 0` by `-T`. Negative Akizuki--Nakano
vanishing on `W` and on `T` gives `H^q(Ω_W^a(log T)(-T)) = 0` for `a + q < n`. After
analytification and GAGA this complex computes `H^*_c(W \ T; ℂ)`, so `H^k_c(W \ T; ℂ) = 0` for
`k < n`, and the long exact sequence of the pair gives injectivity with complex coefficients,
hence with rational ones.

## Main results

* `MMP.Analytic.injective_rationalCohomologyMap_subschemeι_of_isAmple`: restriction
  `H^k(W^an; ℚ) → H^k(T^an; ℚ)` is injective for `k < dim W`.

## Implementation notes

* The divisor `T` is an ideal sheaf `T : W.IdealSheafData` with
  `Stacks.Divisors.IsEffectiveCartierDivisor T`. It is ample when `𝒪_W(T)`
  (`Stacks.Divisors.divisorSheaf T`) is, and it is smooth when its closed subscheme, with
  structure morphism `T.subschemeι ≫ f`, is smooth over `ℂ`.
* `H^k(-; ℚ)` of a complex scheme is `MMP.Fourfold.rationalCohomology` of its complex points with
  the analytic topology (`MMP.Analytic.ComplexPoints.analyticSpace`). Restriction is the pullback
  `MMP.Fourfold.rationalCohomologyMap` along the realization
  `MMP.Analytic.ComplexPoints.analyticMap` of the closed immersion `T.subschemeι`.

## References

* [S. Akizuki, S. Nakano, *Note on Kodaira--Spencer's proof of Lefschetz theorems*]
  [AkizukiNakano1954]
* [P. Deligne, L. Illusie, *Relèvements modulo p² et décomposition du complexe de de Rham*]
  [DeligneIllusie1987]
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MMP.Analytic

namespace MMP.ConductorThreefoldWeakLefschetzTwo

open Limits Pretriangulated

section LES

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A] (F : A ⥤ B) [F.Additive]

/-- A short exact sequence of bounded below complexes
gives, in each degree `k`, an exact sequence `H^k RF(X₁) ⟶ H^k RF(X₂) ⟶ H^k RF(X₃)`. -/
private theorem exact_homology_rightDerivedFunctorPlus (S : ShortComplex (CochainComplex.Plus A))
    (hS : (Stacks.Cohomology.RightDerivedBoundary.toSC S).ShortExact) (k : ℤ) :
    (ShortComplex.mk ((DerivedCategory.Plus.homologyFunctor B k).map
        (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map S.f)))
      ((DerivedCategory.Plus.homologyFunctor B k).map
        (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map S.g)))
      (by
        letI := Functor.commShiftRightDerivedFunctorPlus F
        haveI := Functor.isTriangulated_rightDerivedFunctorPlus F
        rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
          show DerivedCategory.Plus.Q.map (S.f ≫ S.g) = 0 from
            (DerivedCategory.Plus.Q.map_comp _ _).trans (comp_distTriang_mor_zero₁₂ _
              (Stacks.Cech.Hypercohomology.plusTriangle_distinguished S hS)),
          Functor.map_zero, Functor.map_zero])).Exact := by
  letI : F.rightDerivedFunctorPlus.CommShift ℤ := Functor.commShiftRightDerivedFunctorPlus F
  haveI : F.rightDerivedFunctorPlus.IsTriangulated := Functor.isTriangulated_rightDerivedFunctorPlus F
  have hT := F.rightDerivedFunctorPlus.map_distinguished _
    (Stacks.Cech.Hypercohomology.plusTriangle_distinguished S hS)
  exact (DerivedCategory.Plus.homologyFunctor B k).map_distinguished_exact _ hT

/-- For a short exact sequence of bounded below complexes whose first term has vanishing
derived cohomology in degree `k`, the map induced in degree `k` by the second map is a
monomorphism. -/
private theorem mono_homologyFunctor_map_rightDerivedFunctorPlus_map_g
    (S : ShortComplex (CochainComplex.Plus A))
    (hS : (Stacks.Cohomology.RightDerivedBoundary.toSC S).ShortExact) (k : ℤ)
    (h : IsZero ((DerivedCategory.Plus.homologyFunctor B k).obj
      (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj S.X₁)))) :
    Mono ((DerivedCategory.Plus.homologyFunctor B k).map
      (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map S.g))) :=
  (exact_homology_rightDerivedFunctorPlus F S hS k).mono_g (h.eq_of_src _ _)

/-- If the outer terms of a short exact sequence of bounded below complexes have vanishing
`H^k RF`, so does the middle term. -/
private theorem isZero_homology_rightDerivedFunctorPlus_X₂ (S : ShortComplex (CochainComplex.Plus A))
    (hS : (Stacks.Cohomology.RightDerivedBoundary.toSC S).ShortExact) (k : ℤ)
    (h₁ : IsZero ((DerivedCategory.Plus.homologyFunctor B k).obj
      (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj S.X₁))))
    (h₃ : IsZero ((DerivedCategory.Plus.homologyFunctor B k).obj
      (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj S.X₃)))) :
    IsZero ((DerivedCategory.Plus.homologyFunctor B k).obj
      (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj S.X₂))) :=
  (exact_homology_rightDerivedFunctorPlus F S hS k).isZero_X₂ (h₁.eq_of_src _ _)
    (h₃.eq_of_tgt _ _)

/-- `RF` of a complex concentrated in degrees `≥ p` has no cohomology below `p`. -/
private theorem isZero_homology_rightDerivedFunctorPlus_of_isStrictlyGE (K : CochainComplex A ℤ) (p : ℤ)
    [K.IsStrictlyGE p] (k : ℤ) (hk : k < p) :
    IsZero ((DerivedCategory.Plus.homologyFunctor B k).obj
      (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj ⟨K, ⟨p, inferInstance⟩⟩))) := by
  have : (DerivedCategory.Plus.Q.obj (⟨K, ⟨p, inferInstance⟩⟩ : CochainComplex.Plus A)).IsGE p := by
    rw [← DerivedCategory.Plus.isGE_ι_obj_iff]
    change (DerivedCategory.Q.obj K).IsGE p
    infer_instance
  have := F.isGE_rightDerivedFunctorPlus_obj
    (DerivedCategory.Plus.Q.obj (⟨K, ⟨p, inferInstance⟩⟩ : CochainComplex.Plus A)) p
  exact DerivedCategory.Plus.isZero_homology_of_isGE _ p k hk

/-- The localization of the single complex, as a bounded below complex, is the single
object of the bounded below derived category. -/
private noncomputable def plusQSingleIso (X : A) (p : ℤ) :
    DerivedCategory.Plus.Q.obj
        (⟨(HomologicalComplex.single A (ComplexShape.up ℤ) p).obj X, ⟨p, inferInstance⟩⟩ :
          CochainComplex.Plus A) ≅
      (DerivedCategory.Plus.singleFunctor A p).obj X :=
  DerivedCategory.Plus.ι.preimageIso
    ((DerivedCategory.singleFunctorIsoCompQ A p).app X).symm

/-- The inclusion of the stupid truncation `σ_{≥ 0} K` of a complex concentrated in degrees
`≥ 0` is an isomorphism. -/
private theorem isIso_ιStupidTrunc_embeddingUpIntGE_zero (K : CochainComplex A ℤ)
    [K.IsStrictlyGE 0] : IsIso (K.ιStupidTrunc (ComplexShape.embeddingUpIntGE 0)) := by
  haveI : ∀ i, IsIso ((K.ιStupidTrunc (ComplexShape.embeddingUpIntGE 0)).f i) := by
    intro i
    by_cases hi : 0 ≤ i
    · exact HomologicalComplex.isIso_ιStupidTrunc_f _ _
        (i := i.toNat) (by change (0 : ℤ) + (i.toNat : ℤ) = i; omega)
    · exact IsZero.isIso (CochainComplex.isZero_of_isStrictlyGE _ 0 i (by omega))
        (CochainComplex.isZero_of_isStrictlyGE K 0 i (by omega)) _
  exact HomologicalComplex.Hom.isIso_of_components _

/-- **Hypercohomology from the cohomology of the terms.** Let `K` be a complex concentrated
in degrees `≥ 0` such that `H^k(RF(Kᵃ[-a])) = 0` for every `a ≥ 0` and every `k < m`. Then
`H^k(RF(K)) = 0` for `k < m`. -/
private theorem isZero_homology_rightDerivedFunctorPlus_of_isZero_single (K : CochainComplex A ℤ)
    [K.IsStrictlyGE 0] (m : ℤ)
    (h : ∀ a k : ℤ, 0 ≤ a → k < m → IsZero ((DerivedCategory.Plus.homologyFunctor B k).obj
      (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A a).obj (K.X a)))))
    (k : ℤ) (hk : k < m) :
    IsZero ((DerivedCategory.Plus.homologyFunctor B k).obj
      (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj ⟨K, ⟨0, inferInstance⟩⟩))) := by
  letI : F.rightDerivedFunctorPlus.CommShift ℤ := Functor.commShiftRightDerivedFunctorPlus F
  haveI : F.rightDerivedFunctorPlus.IsTriangulated := Functor.isTriangulated_rightDerivedFunctorPlus F
  let σ : ℤ → CochainComplex.Plus A := fun p =>
    ⟨K.stupidTrunc (ComplexShape.embeddingUpIntGE p), ⟨p, inferInstance⟩⟩
  have key : ∀ (d : ℕ) (p : ℤ), m - p ≤ d → ∀ k < m,
      IsZero ((DerivedCategory.Plus.homologyFunctor B k).obj
        (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj (σ p)))) := by
    intro d
    induction d with
    | zero =>
      intro p hp k hk
      exact isZero_homology_rightDerivedFunctorPlus_of_isStrictlyGE F _ p k (by omega)
    | succ d ih =>
      intro p hp k hk
      by_cases hmp : m ≤ p
      · exact isZero_homology_rightDerivedFunctorPlus_of_isStrictlyGE F _ p k (by omega)
      let T := StacksDraft.StupidTruncation.stupidTruncGEShortComplex K p
      let S : ShortComplex (CochainComplex.Plus A) :=
        ShortComplex.mk (X₁ := σ (p + 1)) (X₂ := σ p)
          (X₃ := ⟨(HomologicalComplex.single A (ComplexShape.up ℤ) p).obj (K.X p),
            ⟨p, inferInstance⟩⟩)
          (ObjectProperty.homMk T.f) (ObjectProperty.homMk T.g)
          (ObjectProperty.hom_ext _ T.zero)
      have hS : (Stacks.Cohomology.RightDerivedBoundary.toSC S).ShortExact :=
        StacksDraft.StupidTruncation.stupidTruncGEShortComplex_shortExact K p
      refine isZero_homology_rightDerivedFunctorPlus_X₂ F S hS k (ih (p + 1) (by omega) k hk) ?_
      refine IsZero.of_iso ?_ ((DerivedCategory.Plus.homologyFunctor B k).mapIso
        (F.rightDerivedFunctorPlus.mapIso (plusQSingleIso (K.X p) p)))
      by_cases hp0 : 0 ≤ p
      · exact h p k hp0 hk
      · have hz : IsZero (K.X p) := CochainComplex.isZero_of_isStrictlyGE K 0 p (by omega)
        exact Functor.map_isZero _ (Functor.map_isZero _ (Functor.map_isZero _ hz))
  let ι : σ 0 ⟶ ⟨K, ⟨0, inferInstance⟩⟩ :=
    ObjectProperty.homMk (K.ιStupidTrunc (ComplexShape.embeddingUpIntGE 0))
  haveI : IsIso ι := by
    haveI := isIso_ιStupidTrunc_embeddingUpIntGE_zero K
    haveI : IsIso ((ObjectProperty.ι _).map ι) :=
      inferInstanceAs (IsIso (K.ιStupidTrunc (ComplexShape.embeddingUpIntGE 0)))
    exact isIso_of_fully_faithful (ObjectProperty.ι _) ι
  exact (key (m - 0).toNat 0 (by omega) k hk).of_iso
    ((DerivedCategory.Plus.homologyFunctor B k).mapIso
      (F.rightDerivedFunctorPlus.mapIso (DerivedCategory.Plus.Q.mapIso (asIso ι)))).symm

/-- `H^k(RF(X[-a])) ≅ R^{k-a}F(X)`. -/
private noncomputable def homologyRightDerivedFunctorPlusSingleIso (X : A) (a k : ℤ) :
    (DerivedCategory.Plus.homologyFunctor B k).obj
        (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A a).obj X)) ≅
      (F.rightDerivedPlus (k - a)).obj X := by
  letI : F.rightDerivedFunctorPlus.CommShift ℤ := Functor.commShiftRightDerivedFunctorPlus F
  exact (DerivedCategory.Plus.homologyFunctor B k).mapIso (F.rightDerivedFunctorPlus.mapIso
      (((DerivedCategory.Plus.singleFunctors A).shiftIso (-a) a 0 (by omega)).symm.app X)) ≪≫
    (DerivedCategory.Plus.homologyFunctor B k).mapIso
      ((F.rightDerivedFunctorPlus.commShiftIso (-a)).app _) ≪≫
    ((DerivedCategory.Plus.homologyFunctor B 0).shiftIso (-a) k (k - a) (by omega)).app _

/-- The short exact sequence `0 ⟶ ker φ ⟶ X ⟶ Y ⟶ 0` of bounded below complexes attached to
a morphism `φ` which is an epimorphism of complexes. -/
private noncomputable def plusKernelShortComplex {X Y : CochainComplex.Plus A} (φ : X ⟶ Y) (n : ℤ)
    [CochainComplex.IsStrictlyGE (kernel φ.hom) n] : ShortComplex (CochainComplex.Plus A) :=
  ShortComplex.mk (X₁ := ⟨kernel φ.hom, ⟨n, inferInstance⟩⟩) (ObjectProperty.homMk (kernel.ι φ.hom))
    φ (ObjectProperty.hom_ext _ (kernel.condition φ.hom))

private theorem plusKernelShortComplex_shortExact {X Y : CochainComplex.Plus A} (φ : X ⟶ Y) (n : ℤ)
    [CochainComplex.IsStrictlyGE (kernel φ.hom) n] [Epi φ.hom] :
    (Stacks.Cohomology.RightDerivedBoundary.toSC (plusKernelShortComplex φ n)).ShortExact where
  exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel φ.hom)
  mono_f := inferInstanceAs (Mono (kernel.ι φ.hom))
  epi_g := inferInstanceAs (Epi φ.hom)

/-- The image of a short exact sequence of objects under the right derived functors: if the
outer terms have vanishing `R^q F`, so does the middle one. -/
private theorem isZero_rightDerivedPlus_obj_X₂ (S : ShortComplex A) (hS : S.ShortExact) (q : ℤ)
    (h₁ : IsZero ((F.rightDerivedPlus q).obj S.X₁)) (h₃ : IsZero ((F.rightDerivedPlus q).obj S.X₃)) :
    IsZero ((F.rightDerivedPlus q).obj S.X₂) := by
  let sg := HomologicalComplex.single A (ComplexShape.up ℤ) 0
  let S' : ShortComplex (CochainComplex.Plus A) :=
    ShortComplex.mk (X₁ := ⟨sg.obj S.X₁, ⟨0, inferInstance⟩⟩)
      (X₂ := ⟨sg.obj S.X₂, ⟨0, inferInstance⟩⟩) (X₃ := ⟨sg.obj S.X₃, ⟨0, inferInstance⟩⟩)
      (ObjectProperty.homMk (sg.map S.f)) (ObjectProperty.homMk (sg.map S.g))
      (ObjectProperty.hom_ext _ (by
        change sg.map S.f ≫ sg.map S.g = 0
        rw [← Functor.map_comp, S.zero, Functor.map_zero]))
  have hS' : (Stacks.Cohomology.RightDerivedBoundary.toSC S').ShortExact :=
    HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i => by
      by_cases hi : i = 0
      · subst hi
        refine ShortComplex.shortExact_of_iso (S₁ := S)
          (S₂ := (Stacks.Cohomology.RightDerivedBoundary.toSC S').map
            (HomologicalComplex.eval A (ComplexShape.up ℤ) 0)) (ShortComplex.isoMk
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 S.X₁).symm
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 S.X₂).symm
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 S.X₃).symm ?_ ?_) hS
        · change _ ≫ (sg.map S.f).f 0 = _
          simp [sg, HomologicalComplex.single_map_f_self]
        · change _ ≫ (sg.map S.g).f 0 = _
          simp [sg, HomologicalComplex.single_map_f_self]
      · have z : ∀ Y : A, IsZero ((sg.obj Y).X i) := fun Y =>
          HomologicalComplex.isZero_single_obj_X _ _ _ _ hi
        exact ShortComplex.ShortExact.mk' (ShortComplex.exact_of_isZero_X₂ _ (z S.X₂))
          ⟨fun g h _ => (z S.X₁).eq_of_tgt g h⟩ ⟨fun g h _ => (z S.X₃).eq_of_src g h⟩
  have e : ∀ Y : A, (DerivedCategory.Plus.homologyFunctor B q).obj
      (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj
        (⟨sg.obj Y, ⟨0, inferInstance⟩⟩ : CochainComplex.Plus A))) ≅
      (F.rightDerivedPlus q).obj Y := fun Y =>
    (DerivedCategory.Plus.homologyFunctor B q).mapIso
      (F.rightDerivedFunctorPlus.mapIso (plusQSingleIso Y 0))
  exact (isZero_homology_rightDerivedFunctorPlus_X₂ F S' hS' q (h₁.of_iso (e S.X₁))
    (h₃.of_iso (e S.X₃))).of_iso (e S.X₂).symm

end LES

section Conj

variable {C : Type*} [Category* C] [Abelian C] {Y₁ Y₂ Z₁ Z₂ : C}

/-- The kernel of a morphism conjugated by isomorphisms. -/
private noncomputable def kernelConjIso (a : Y₁ ⟶ Y₂) (g : Y₂ ⟶ Z₂) (b : Z₂ ⟶ Z₁) (ha : IsIso a)
    (hb : IsIso b) : kernel (a ≫ g ≫ b) ≅ kernel g :=
  kernelIsIsoComp a (g ≫ b) ≪≫ kernelCompMono g b

/-- `extendMap φ e` is an epimorphism when every component of `φ` is. -/
private theorem epi_extendMap {ι ι' : Type*}
    {c : ComplexShape ι} {c' : ComplexShape ι'} {K L : HomologicalComplex C c} (φ : K ⟶ L)
    (e : c.Embedding c') [∀ i, Epi (φ.f i)] : Epi (HomologicalComplex.extendMap φ e) := by
  refine HomologicalComplex.epi_of_epi_f _ (fun i' => ?_)
  by_cases h : ∃ i, e.f i = i'
  · obtain ⟨i, hi⟩ := h
    rw [HomologicalComplex.extendMap_f φ e hi]
    infer_instance
  · exact IsZero.epi (L.isZero_extend_X e i' (fun i hi => h ⟨i, hi⟩)) _

end Conj

section DeRham

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {X S : Scheme.{u}} (f : X ⟶ S) (I : X.IdealSheafData)

/-- The canonical map `Ω^•_{X/S} ⟶ i_*Ω^•_{Y/S}` of bounded below complexes of abelian
sheaves, for the closed subscheme `Y` cut out by `I`. -/
private noncomputable abbrev restrictionMapPlus :=
  Scheme.Hom.deRhamAbelianPushforwardMapPlus I.subschemeι f (I.subschemeι ≫ f) (𝟙 S)
    (Stacks.HodgeWeil.subschemeι_square f I)

/-- The restriction of forms to a closed subscheme, read in abelian sheaves, is an epimorphism of
complexes. -/
private instance epi_deRhamAbelianPushforwardMap_subschemeι :
    Epi (Scheme.Hom.deRhamAbelianPushforwardMap I.subschemeι f (I.subschemeι ≫ f) (𝟙 S)
      (Stacks.HodgeWeil.subschemeι_square f I)) := by
  refine HomologicalComplex.epi_of_epi_f _ (fun p => ?_)
  change Epi ((SheafOfModules.toSheaf _).map
    ((Scheme.Hom.deRhamFormsPushforwardHom I.subschemeι f (I.subschemeι ≫ f) (𝟙 S)
      (Stacks.HodgeWeil.subschemeι_square f I)).app (p : ℤ)))
  rw [← Stacks.DeRham.FormsGenerators.formsDirectImageComparison_eq]
  exact @Stacks.SheafOfModules.EpiMono.epi_toSheaf_map _ _ _ _ _ _ _ _ _
    (Scheme.Hom.epi_formRestriction I.subschemeι f p)

private instance epi_restrictionMapPlus_hom : Epi (restrictionMapPlus f I).hom := by
  haveI : ∀ i, Epi ((Scheme.Hom.deRhamAbelianPushforwardMap I.subschemeι f
      (I.subschemeι ≫ f) (𝟙 S) (Stacks.HodgeWeil.subschemeι_square f I)).f i) := fun i =>
    @HomologicalComplex.instEpiFOfHasFiniteColimits _ _ _ _ _ Abelian.hasFiniteColimits _ _ _
      (epi_deRhamAbelianPushforwardMap_subschemeι f I) i
  haveI := epi_extendMap (Scheme.Hom.deRhamAbelianPushforwardMap I.subschemeι f
    (I.subschemeι ≫ f) (𝟙 S) (Stacks.HodgeWeil.subschemeι_square f I)) ComplexShape.embeddingUpNat
  change Epi (HomologicalComplex.extendMap _ _ ≫ _)
  exact @epi_comp _ _ _ _ _ _ inferInstance _
    (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_hom (HomologicalComplex.mapHomologicalComplexExtendIso _ _ _)))

/-- The complex `𝒦^•` of forms vanishing on the closed subscheme. -/
private noncomputable abbrev kernelComplex : CochainComplex (Stacks.Cohomology.Leray.AbelianSheaf
    X.toRingedSpace.carrier) ℤ :=
  kernel (restrictionMapPlus f I).hom

private instance kernelComplex_isStrictlyGE : CochainComplex.IsStrictlyGE (kernelComplex f I) 0 := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  have h : IsZero ((SheafOfModules.deRhamAbelianComplexPlus (Scheme.Hom.deRhamAlgebras f)
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f))).obj.X i) :=
    HomologicalComplex.isZero_extend_X
      (SheafOfModules.deRhamAbelianComplex (Scheme.Hom.deRhamAlgebras f)
        (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f)))
      ComplexShape.embeddingUpNat i (fun k hk => by
        have : (0 : ℤ) ≤ ComplexShape.embeddingUpNat.f k := Int.natCast_nonneg k
        omega)
  exact IsZero.of_mono ((kernel.ι (restrictionMapPlus f I).hom).f i) h

/-- **Restriction of de Rham cohomology to a closed subscheme is injective in low degrees**
when the terms of the complex of forms vanishing on it have no cohomology in total
degree `< m`. -/
private theorem injective_deRhamCohomologyPullback_subschemeι (m : ℤ)
    (hK : ∀ a q : ℕ, (a : ℤ) + q < m →
      IsZero (((Stacks.Cohomology.Leray.sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerivedPlus
        (q : ℤ)).obj ((kernelComplex f I).X a)))
    (k : ℤ) (hk : k < m) :
    Function.Injective (Scheme.Hom.deRhamCohomologyPullback I.subschemeι f (I.subschemeι ≫ f)
      (𝟙 S) (Stacks.HodgeWeil.subschemeι_square f I) k).hom := by
  rw [injective_iff_map_eq_zero]
  intro b hb
  rw [Scheme.Hom.deRhamCohomologyPullback_apply_eq_zero_iff] at hb
  have hz : IsZero ((DerivedCategory.Plus.homologyFunctor _ k).obj
      ((Stacks.Cohomology.Leray.sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.obj
        (DerivedCategory.Plus.Q.obj (plusKernelShortComplex (restrictionMapPlus f I) 0).X₁))) := by
    have e : (plusKernelShortComplex (restrictionMapPlus f I) 0).X₁ =
        (⟨kernelComplex f I, ⟨0, inferInstance⟩⟩ : CochainComplex.Plus _) := rfl
    rw [e]
    refine isZero_homology_rightDerivedFunctorPlus_of_isZero_single
      (Stacks.Cohomology.Leray.sectionsFunctor X.toRingedSpace.carrier ⊤) (kernelComplex f I) m
      (fun a k ha hk' => ?_) k hk
    obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le ha
    refine IsZero.of_iso ?_ (homologyRightDerivedFunctorPlusSingleIso _ _ p k)
    by_cases hq : 0 ≤ k - p
    · obtain ⟨q, hq'⟩ := Int.eq_ofNat_of_zero_le hq
      rw [hq']
      exact hK p q (by omega)
    · exact Functor.isZero_rightDerivedPlus_of_neg _ _ _ (by omega)
  have hmono := mono_homologyFunctor_map_rightDerivedFunctorPlus_map_g _
    (plusKernelShortComplex (restrictionMapPlus f I) 0)
    (plusKernelShortComplex_shortExact (restrictionMapPlus f I) 0) k hz
  exact (AddCommGrpCat.mono_iff_injective _).1 hmono (hb.trans (map_zero _).symm)

end DeRham

section Residue

variable {X S : Scheme.{0}} (f : X ⟶ S) (I : X.IdealSheafData)
  (hI : Stacks.Divisors.IsEffectiveCartierDivisor I)

/-- The residue sequence `0 → Ω^{p+1} → Ω^{p+1}(log Y) → i_*Ω^p_Y → 0` as a short complex of
`𝒪_X`-modules. -/
private noncomputable abbrev residueShortComplex (hlog : f.HasLogPolesDeRhamComplex I) (p : ℕ) :
    ShortComplex (SheafOfModules X.ringCatSheaf) :=
  ShortComplex.mk (C := SheafOfModules X.ringCatSheaf)
    (Scheme.Hom.logPolesFormsInclusion f I (p + 1)) (Scheme.Hom.logResHom f I hI hlog p) (by
      apply (SheafOfModules.toSheaf X.ringCatSheaf).map_injective
      refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun W =>
        AddCommGrpCat.hom_ext (AddMonoidHom.ext fun ω => ?_)))
      exact Scheme.Hom.logRes_logPolesFormsInclusion hI hlog (W := W.unop) ω)

/-- **The residue sequence is short exact as a sequence of `𝒪_X`-modules.** -/
private theorem residueShortComplex_shortExact (hlog : f.HasLogPolesDeRhamComplex I)
    (p : ℕ) :
    (residueShortComplex f I hI hlog p).ShortExact := by
  have h : ((residueShortComplex f I hI hlog p).map
      (SheafOfModules.toSheaf X.ringCatSheaf)).ShortExact :=
    Scheme.Hom.shortExact_eval_succ f I hI hlog p
  exact ShortComplex.ShortExact.mk'
    (((residueShortComplex f I hI hlog p).exact_map_iff_of_faithful
      (SheafOfModules.toSheaf X.ringCatSheaf)).1 h.exact)
    ((SheafOfModules.toSheaf X.ringCatSheaf).mono_of_mono_map h.mono_f)
    ((SheafOfModules.toSheaf X.ringCatSheaf).epi_of_epi_map h.epi_g)

include hI in
/-- In degree `0` a form with logarithmic poles has no pole. -/
private theorem isIso_logPolesFormsInclusion_zero
    (hlog : f.HasLogPolesDeRhamComplex I) :
    IsIso (C := SheafOfModules X.ringCatSheaf) (Scheme.Hom.logPolesFormsInclusion f I 0) := by
  have h := Scheme.Hom.shortExact_eval_zero f I hI hlog
  have hm : Mono ((SheafOfModules.toSheaf X.ringCatSheaf).map
      (C := SheafOfModules X.ringCatSheaf) (Scheme.Hom.logPolesFormsInclusion f I 0)) := h.mono_f
  have he : Epi ((SheafOfModules.toSheaf X.ringCatSheaf).map
      (C := SheafOfModules X.ringCatSheaf) (Scheme.Hom.logPolesFormsInclusion f I 0)) :=
    h.exact.epi_f (IsZero.eq_of_tgt (isZero_zero _) _ _)
  haveI := (SheafOfModules.toSheaf X.ringCatSheaf).mono_of_mono_map hm
  haveI := (SheafOfModules.toSheaf X.ringCatSheaf).epi_of_epi_map he
  exact isIso_of_mono_of_epi _

end Residue

section KernelTerms

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {X S : Scheme.{u}} (f : X ⟶ S) (I : X.IdealSheafData)

/-- The de Rham complex `Ω^•_{X/S}` read in abelian sheaves, indexed by `ℕ`. -/
private noncomputable abbrev formsComplex :=
  SheafOfModules.deRhamAbelianComplex (Scheme.Hom.deRhamAlgebras f)
    (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f))

private theorem restrictionMapPlus_f (p : ℕ) :
    (restrictionMapPlus f I).hom.f (p : ℤ) =
      (HomologicalComplex.extendXIso (formsComplex f) ComplexShape.embeddingUpNat (i := p)
          (i' := (p : ℤ)) rfl).hom ≫
        (SheafOfModules.toSheaf _).map (Stacks.HodgeWeil.formsRestrictionBase f I p) ≫
          (Stacks.Cohomology.LerayLowDegree.abelianPushforward.{u, u} I.subschemeι.base).map
            (HomologicalComplex.extendXIso (formsComplex (I.subschemeι ≫ f))
              ComplexShape.embeddingUpNat (i := p) (i' := (p : ℤ)) rfl).inv := by
  have hf := HomologicalComplex.extendMap_mapHomologicalComplexExtendIso_f
    (F := Stacks.Cohomology.LerayLowDegree.abelianPushforward.{u, u} I.subschemeι.base)
    (SheafOfModules.deRhamAbelianComplex (Scheme.Hom.deRhamAlgebras (I.subschemeι ≫ f))
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (I.subschemeι ≫ f))))
    (Scheme.Hom.deRhamAbelianPushforwardMap I.subschemeι f (I.subschemeι ≫ f) (𝟙 S)
      (Stacks.HodgeWeil.subschemeι_square f I))
    ComplexShape.embeddingUpNat (i := p) (i' := (p : ℤ)) rfl
  refine hf.trans ?_
  rw [Stacks.DeRhamBaseChange.deRhamAbelianPushforwardMap_f]
  rfl

private theorem restrictionMapPlus_f' (p : ℕ) :
    (restrictionMapPlus f I).hom.f (p : ℤ) =
      (HomologicalComplex.extendXIso (formsComplex f) ComplexShape.embeddingUpNat (i := p)
          (i' := (p : ℤ)) rfl).hom ≫
        (SheafOfModules.toSheaf X.ringCatSheaf).map
          (Scheme.Hom.formRestriction I.subschemeι f (p : ℤ)) ≫
          (Stacks.Cohomology.LerayLowDegree.abelianPushforward.{u, u} I.subschemeι.base).map
            (HomologicalComplex.extendXIso (formsComplex (I.subschemeι ≫ f))
              ComplexShape.embeddingUpNat (i := p) (i' := (p : ℤ)) rfl).inv := by
  refine (restrictionMapPlus_f f I p).trans ?_
  exact congrArg (fun g => _ ≫ g ≫ _) (Stacks.HodgeWeil.toSheaf_map_formsRestrictionBase f I p)

/-- The term in degree `p` of the kernel of `Ω^•_{X/S} ⟶ i_*Ω^•_{Y/S}`, as a kernel. -/
private noncomputable def kernelComplexXIsoKernel (p : ℕ) :
    (kernelComplex f I).X (p : ℤ) ≅ kernel ((restrictionMapPlus f I).hom.f (p : ℤ)) :=
  PreservesKernel.iso (HomologicalComplex.eval _ (ComplexShape.up ℤ) (p : ℤ))
      (restrictionMapPlus f I).hom

/-- The kernel in degree `p` is the kernel of the restriction of `p`-forms. -/
private noncomputable def kernelRestrictionMapPlusFIso (p : ℕ) :
    kernel ((restrictionMapPlus f I).hom.f (p : ℤ)) ≅
      kernel ((SheafOfModules.toSheaf X.ringCatSheaf).map
        (Scheme.Hom.formRestriction I.subschemeι f (p : ℤ))) :=
  kernelIsoOfEq (restrictionMapPlus_f' f I p) ≪≫
    kernelConjIso (HomologicalComplex.extendXIso (formsComplex f) ComplexShape.embeddingUpNat
        (i := p) (i' := (p : ℤ)) rfl).hom
      ((SheafOfModules.toSheaf X.ringCatSheaf).map
        (Scheme.Hom.formRestriction I.subschemeι f (p : ℤ)))
      ((Stacks.Cohomology.LerayLowDegree.abelianPushforward.{u, u} I.subschemeι.base).map
        (HomologicalComplex.extendXIso (formsComplex (I.subschemeι ≫ f))
          ComplexShape.embeddingUpNat (i := p) (i' := (p : ℤ)) rfl).inv) inferInstance
      ((Stacks.Cohomology.LerayLowDegree.abelianPushforward.{u, u} I.subschemeι.base).mapIso
        (HomologicalComplex.extendXIso (formsComplex (I.subschemeι ≫ f))
          ComplexShape.embeddingUpNat (i := p) (i' := (p : ℤ)) rfl)).isIso_inv

/-- The kernel of the restriction of `p`-forms, in abelian sheaves, is the sheaf of `p`-forms
vanishing on the closed subscheme. -/
private noncomputable def kernelToSheafFormRestrictionIso (p : ℕ) :
    kernel ((SheafOfModules.toSheaf X.ringCatSheaf).map
        (Scheme.Hom.formRestriction I.subschemeι f (p : ℤ))) ≅
      (SheafOfModules.toSheaf X.ringCatSheaf).obj (Scheme.Hom.formRestrictionKernelSheaf f I p) :=
  (PreservesKernel.iso (SheafOfModules.toSheaf X.ringCatSheaf)
      (Scheme.Hom.formRestriction I.subschemeι f (p : ℤ))).symm ≪≫
    (SheafOfModules.toSheaf X.ringCatSheaf).mapIso (SheafOfModules.Submodule.kerIsoKernel _).symm

/-- The term of `𝒦^•` in degree `p` is the sheaf of `p`-forms vanishing on the closed
subscheme. -/
private noncomputable def kernelComplexXIso (p : ℕ) :
    (kernelComplex f I).X (p : ℤ) ≅
      (SheafOfModules.toSheaf X.ringCatSheaf).obj (Scheme.Hom.formRestrictionKernelSheaf f I p) :=
  kernelComplexXIsoKernel f I p ≪≫ kernelRestrictionMapPlusFIso f I p ≪≫
    kernelToSheafFormRestrictionIso f I p

end KernelTerms

section Comparison

open MMP

/-- Pullback `H^q(X; ℂ) ⟶ H^q(X'; ℂ)` of complex singular cohomology along `g : X' ⟶ X`. -/
private noncomputable abbrev complexCohomologyMap {X' X : TopCat.{0}} (g : X' ⟶ X) (q : ℕ) :
    cohomologyWithSupports ℂ (ModuleCat.of ℂ ℂ) X Set.univ q ⟶
      cohomologyWithSupports ℂ (ModuleCat.of ℂ ℂ) X' Set.univ q :=
  relativeSingularCohomology.map ℂ (ModuleCat.of ℂ ℂ) g (fun _ hx ↦ absurd (Set.mem_univ _) hx) q

/-- **Injectivity passes from de Rham to singular cohomology** along a morphism of smooth
projective complex varieties, by the natural comparison isomorphisms. -/
private theorem injective_complexCohomologyMap_of_injective_deRhamCohomologyPullback
    {X Y : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) (sY : Y ⟶ Spec (.of ℂ))
    [IsProjectiveVariety ℂ sX] [IsProjectiveVariety ℂ sY] (hX : MMP.Mori.IsSmoothScheme sX)
    (hY : MMP.Mori.IsSmoothScheme sY) (g : X ⟶ Y) (hg : g ≫ sY = sX) (n : ℕ)
    (h : Function.Injective (Scheme.Hom.deRhamCohomologyPullback g sY sX (𝟙 _)
      (by rw [hg, Category.comp_id]) n).hom) :
    Function.Injective (complexCohomologyMap (ComplexPoints.analyticMap g hg) n).hom := by
  obtain ⟨e, he, -⟩ := MMP.Analytic.exists_deRhamCohomology_linearEquiv_singularCohomology
  have hsurj : ∀ z, ∃ y, e Y sY hY n
      ((SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology _ _ (n : ℤ)).hom y) = z :=
    fun z => ⟨(SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology _ _ (n : ℤ)).inv
      ((e Y sY hY n).symm z), (congrArg (e Y sY hY n) (Iso.inv_hom_id_apply
        (SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology _ _ (n : ℤ)) _)).trans
          (LinearEquiv.apply_symm_apply _ _)⟩
  intro z₁ z₂ hz
  obtain ⟨y₁, rfl⟩ := hsurj z₁
  obtain ⟨y₂, rfl⟩ := hsurj z₂
  have hpb := (e X sX hX n).injective
    ((he X Y sX sY hX hY g hg n y₁).trans (hz.trans (he X Y sX sY hX hY g hg n y₂).symm))
  rw [h ((Iso.hom_inv_id_apply _ _).symm.trans ((congrArg
    (SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology _ _ (n : ℤ)).inv hpb).trans
      (Iso.hom_inv_id_apply _ _)))]

end Comparison

section Coefficients

open MMP MMP.SingularCochain MMP.Analytic

/-- The change of coefficients `H^n(-; ℚ) ⟶ H^n(-; ℂ)` commutes with pullbacks. -/
private theorem mapCoeff_rationalCohomologyMap {Y' Y : TopCat.{0}} (g : Y' ⟶ Y) (n : ℕ)
    (x : singularCohomology ℚ Y n) :
    singularCohomology.mapCoeff (algebraMap ℚ ℂ) n
      ((MMP.Fourfold.rationalCohomologyMap g n).hom x) =
    (complexCohomologyMap g n).hom (singularCohomology.mapCoeff (algebraMap ℚ ℂ) n x) := by
  have k : ∀ {Z : TopCat.{0}} (y : singularCohomology ℚ Z n),
      relativeSingularCohomologyEquiv ℂ (Set.univᶜ : Set Z) n
        (singularCohomology.mapCoeff (algebraMap ℚ ℂ) n y) =
      singularCohomology.relCohomologyMap (algebraMap ℚ ℂ) Set.univᶜ n
        (relativeSingularCohomologyEquiv ℚ Set.univᶜ n y) :=
    fun y => LinearEquiv.apply_symm_apply _ _
  have h₁ := relativeSingularCohomologyEquiv_map (R := ℂ) g
    (A' := (Set.univᶜ : Set Y')) (A := (Set.univᶜ : Set Y))
    (fun _ hx ↦ (hx (Set.mem_univ _)).elim) n (singularCohomology.mapCoeff (algebraMap ℚ ℂ) n x)
  have h₂ := relativeSingularCohomologyEquiv_map (R := ℚ) g
    (A' := (Set.univᶜ : Set Y')) (A := (Set.univᶜ : Set Y))
    (fun _ hx ↦ (hx (Set.mem_univ _)).elim) n x
  apply (relativeSingularCohomologyEquiv ℂ (Set.univᶜ : Set Y') n).injective
  refine (k _).trans (Eq.trans ?_ h₁.symm)
  refine (congrArg _ h₂).trans ?_
  rw [k x]
  generalize relativeSingularCohomologyEquiv ℚ _ n x = y
  induction y using Submodule.Quotient.induction_on
  rfl

/-- The change of coefficients `H^n(Y; ℚ) ⟶ H^n(Y; ℂ)` is injective: a `ℚ`-linear retraction
`ℂ ⟶ ℚ` carries a primitive of the complexified cocycle to a primitive of the cocycle. -/
private theorem injective_mapCoeff_algebraMap (Y : TopCat.{0}) (n : ℕ) :
    Function.Injective (singularCohomology.mapCoeff (algebraMap ℚ ℂ) n :
      singularCohomology ℚ Y n → singularCohomology ℂ Y n) := by
  obtain ⟨π, hπ⟩ : ∃ π : ℂ →ₗ[ℚ] ℚ, π.comp (Algebra.linearMap ℚ ℂ) = LinearMap.id :=
    LinearMap.exists_leftInverse_of_injective _
      (LinearMap.ker_eq_bot.2 (algebraMap ℚ ℂ).injective)
  have hπa : ∀ q : ℚ, π (algebraMap ℚ ℂ q) = q := fun q => LinearMap.congr_fun hπ q
  have hπm : ∀ (q : ℚ) (z : ℂ), π (algebraMap ℚ ℂ q * z) = q * π z := fun q z => by
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  rw [injective_iff_map_eq_zero]
  intro x hx
  apply (relativeSingularCohomologyEquiv ℚ (Set.univᶜ : Set Y) n).injective
  rw [map_zero]
  have hx' : singularCohomology.relCohomologyMap (algebraMap ℚ ℂ) Set.univᶜ n
      (relativeSingularCohomologyEquiv ℚ Set.univᶜ n x) = 0 := by
    have h0 := congrArg (relativeSingularCohomologyEquiv ℂ (Set.univᶜ : Set Y) n) hx
    rw [map_zero] at h0
    exact (LinearEquiv.apply_symm_apply _ _).symm.trans h0
  generalize relativeSingularCohomologyEquiv ℚ _ n x = y at hx' ⊢
  induction y using Submodule.Quotient.induction_on with | H φ => ?_
  change Submodule.Quotient.mk (singularCohomology.relCocyclesMap (algebraMap ℚ ℂ) _ n φ) = 0 at hx'
  rw [Submodule.Quotient.mk_eq_zero] at hx'
  rw [Submodule.Quotient.mk_eq_zero]
  simp only [Submodule.mem_comap, Submodule.coe_subtype] at hx' ⊢
  change singularCohomology.cochainMap (algebraMap ℚ ℂ) n φ.1 ∈ _ at hx'
  cases n with
  | zero =>
    change _ ∈ (⊥ : Submodule ℂ _) at hx'
    change _ ∈ (⊥ : Submodule ℚ _)
    rw [Submodule.mem_bot] at hx' ⊢
    funext σ
    have h0 := congrFun hx' σ
    simp only [singularCohomology.cochainMap_apply, Pi.zero_apply] at h0
    exact (algebraMap ℚ ℂ).injective (h0.trans (map_zero _).symm)
  | succ m =>
    obtain ⟨α, hα, hαe⟩ := hx'
    refine ⟨fun σ => π (α σ), fun σ hσ => by simp [hα σ hσ], ?_⟩
    funext σ
    have h0 := congrFun hαe σ
    rw [coboundary_apply, singularCohomology.cochainMap_apply] at h0
    rw [coboundary_apply, ← hπa (φ.1 σ), ← h0, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show ((-1 : ℂ) ^ (i : ℕ)) = algebraMap ℚ ℂ ((-1) ^ (i : ℕ)) by simp, hπm]

/-- **Rational injectivity from complex injectivity.** -/
private theorem injective_rationalCohomologyMap_of_injective_complexCohomologyMap
    {Y' Y : TopCat.{0}} (g : Y' ⟶ Y) (n : ℕ)
    (h : Function.Injective (complexCohomologyMap g n).hom) :
    Function.Injective (MMP.Fourfold.rationalCohomologyMap g n) := by
  intro x y hxy
  apply injective_mapCoeff_algebraMap Y n
  apply h
  rw [← mapCoeff_rationalCohomologyMap, ← mapCoeff_rationalCohomologyMap]
  exact congrArg _ hxy

/-- On a path-connected space a singular `0`-cocycle is constant: a path from `σ` to `τ` is a
singular `1`-simplex whose boundary is `τ - σ`. -/
private theorem eq_of_coboundary_zero_eq_zero {Y : Type*} [TopologicalSpace Y]
    [PathConnectedSpace Y] {R : Type*} [CommRing R] (φ : SingularChain.Simplex Y 0 → R)
    (hφ : coboundary R 0 φ = 0) (σ τ : SingularChain.Simplex Y 0) : φ σ = φ τ := by
  classical
  haveI : Subsingleton (stdSimplex ℝ (Fin (0 + 1))) :=
    inferInstanceAs (Subsingleton (stdSimplex ℝ (Fin 1)))
  let v : stdSimplex ℝ (Fin 1) := stdSimplex.vertex 0
  have hconst : ∀ ρ : SingularChain.Simplex Y 0, ρ = ContinuousMap.const _ (ρ v) := fun ρ => by
    ext p
    rw [Subsingleton.elim p v]
    rfl
  let γ : Path (σ v) (τ v) := PathConnectedSpace.somePath _ _
  let ρ : SingularChain.Simplex Y 1 :=
    ⟨fun p => γ.extend (p 1), γ.continuous_extend.comp
      ((continuous_apply 1).comp continuous_subtype_val)⟩
  have hface : ∀ i : Fin 2, ρ.comp (SingularChain.face 0 i) =
      ContinuousMap.const _ (γ.extend ((stdSimplex.vertex (S := ℝ) (i.succAbove 0) :
        stdSimplex ℝ (Fin 2)) 1)) := fun i => by
    ext p
    rw [Subsingleton.elim p v]
    change γ.extend ((stdSimplex.map i.succAbove v) 1) = _
    rw [stdSimplex.map_vertex]
    rfl
  have e0 : (0 : Fin 2).succAbove (0 : Fin 1) = 1 := rfl
  have e1 : (1 : Fin 2).succAbove (0 : Fin 1) = 0 := rfl
  have h0 : ρ.comp (SingularChain.face 0 0) = τ := by
    rw [hface]
    ext p
    rw [Subsingleton.elim p v]
    simp [e0]
  have h1 : ρ.comp (SingularChain.face 0 1) = σ := by
    rw [hface]
    ext p
    rw [Subsingleton.elim p v]
    simp [e1]
  have h := congrFun hφ ρ
  rw [coboundary_apply, Fin.sum_univ_two, h0, h1] at h
  simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_one, pow_one, neg_mul, Pi.zero_apply] at h
  exact (add_neg_eq_zero.1 h).symm

/-- **Restriction to a nonempty subspace is injective on `H^0` of a path-connected space.** -/
private theorem injective_complexCohomologyMap_zero {Y' Y : TopCat.{0}} (g : Y' ⟶ Y)
    [PathConnectedSpace Y] [Nonempty Y'] :
    Function.Injective (complexCohomologyMap g 0).hom := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  apply (relativeSingularCohomologyEquiv ℂ (Set.univᶜ : Set Y) 0).injective
  rw [map_zero]
  have hx' := relativeSingularCohomologyEquiv_map (R := ℂ) g (A' := (Set.univᶜ : Set Y'))
    (A := (Set.univᶜ : Set Y)) (fun _ hx ↦ (hx (Set.mem_univ _)).elim) 0 x
  change relativeSingularCohomologyEquiv ℂ _ 0 ((complexCohomologyMap g 0).hom x) = _ at hx'
  rw [hx, map_zero] at hx'
  generalize relativeSingularCohomologyEquiv ℂ _ 0 x = y at hx' ⊢
  induction y using Submodule.Quotient.induction_on with | H φ => ?_
  erw [relCohomologyMap_mk] at hx'
  have h0 := (Submodule.Quotient.mk_eq_zero _).1 hx'.symm
  have hpull : cochainPullback ℂ g 0 φ.1 = 0 := (Submodule.mem_bot ℂ).1 h0
  rw [Submodule.Quotient.mk_eq_zero]
  change φ.1 ∈ (⊥ : Submodule ℂ _)
  rw [Submodule.mem_bot]
  obtain ⟨y0⟩ := ‹Nonempty Y'›
  have hcoc : coboundary ℂ 0 φ.1 = 0 := ((mem_relCocycles_iff ℂ _ 0 φ.1).1 φ.2).2
  funext σ
  rw [eq_of_coboundary_zero_eq_zero φ.1 hcoc σ (g.hom.comp (ContinuousMap.const _ y0))]
  exact congrFun hpull (ContinuousMap.const _ y0)

end Coefficients

section Evaluation

/-! ### Evaluation out of the sheaf-hom from an invertible module -/

open Opposite TopologicalSpace
open Stacks.SheafOfModules Stacks.SheafOfModules.TensorStalkRingedSpace

variable (X : AlgebraicGeometry.RingedSpace.{0, 0})
variable {F G H : _root_.SheafOfModules.{0} (structureSheafRing X)}

/-- A morphism into the sheaf-hom is determined by its components at the identity of each
open. -/
private theorem eq_of_isTensorCurry
    {t : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj F).obj G) ⟶ H}
    {c c' : F ⟶ sheafHomSpace X G H} (hc : IsTensorCurry X t c) (hc' : IsTensorCurry X t c') :
    c = c' := by
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro g
  have key : ∀ c₀ : F ⟶ sheafHomSpace X G H, ((c₀.val.app U x).app V).hom g =
      ((c₀.val.app (op V.unop.left) (F.val.map V.unop.hom.op x)).app
        (op (Over.mk (𝟙 V.unop.left)))).hom g := by
    intro c₀
    have h := congrArg (fun k => k.hom x) (c₀.val.naturality V.unop.hom.op)
    change c₀.val.app (op V.unop.left) (F.val.map V.unop.hom.op x) =
      (sheafHomSpace X G H).val.map V.unop.hom.op (c₀.val.app U x) at h
    rw [h]
    change _ = ((c₀.val.app U x).app (op (Over.mk (𝟙 V.unop.left ≫ V.unop.hom)))).hom g
    rfl
  rw [key c, key c']
  exact (hc _ _ g).trans (hc' _ _ g).symm

variable {A A' B C : _root_.SheafOfModules.{0} (structureSheafRing X)}

/-- The tensor product of a morphism with the identity, on a local pure tensor. -/
private theorem tensorMap_app_toTensorSheafSection (g : A' ⟶ A) (U : (Opens X.carrier)ᵒᵖ)
    (a : A'.val.obj U) (b : B.val.obj U) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).map g).app B).val.app U
        (toTensorSheafSection X A' B U (a ⊗ₜ b)) =
      toTensorSheafSection X A B U (g.val.app U a ⊗ₜ b) := by
  have h := congrArg (fun φ => φ.app U (a ⊗ₜ b))
    ((PresheafOfModules.sheafificationAdjunction
      (R := Stacks.SheafOfModules.Tensor.ringSheaf ⟨X.presheaf, X.IsSheaf⟩)
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf ⟨X.presheaf, X.IsSheaf⟩).obj)).unit.naturality
        (PresheafOfModules.tensorHom (O := X.presheaf) g.val (𝟙 B.val)))
  exact h.symm

/-- **Naturality of the currying bijection in the first variable.** -/
private theorem tensorHomEquiv_naturality_left (g : A' ⟶ A)
    (t : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj A).obj B) ⟶ C) :
    tensorHomEquiv X A' B C
        (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).map g).app B ≫ t) =
      g ≫ tensorHomEquiv X A B C t := by
  refine eq_of_isTensorCurry X (tensorHomEquiv_isTensorCurry X _) (fun U f b => ?_)
  refine (tensorHomEquiv_isTensorCurry X t U (g.val.app (op U) f) b).trans ?_
  change _ = t.val.app (op U) ((((Stacks.SheafOfModules.Tensor.sheafTensor
    ⟨X.presheaf, X.IsSheaf⟩).map g).app B).val.app (op U)
      (toTensorSheafSection X A' B (op U) (f ⊗ₜ b)))
  rw [tensorMap_app_toTensorSheafSection]

/-- The evaluation `ℋom(B, C) ⊗ B ⟶ C`. -/
private noncomputable def sheafHomEval (B C : _root_.SheafOfModules.{0} (structureSheafRing X)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj
      (sheafHomSpace X B C)).obj B ⟶ C :=
  (tensorHomEquiv X _ B C).symm (𝟙 _)

private theorem tensorMap_comp_sheafHomEval (φ : A ⟶ sheafHomSpace X B C) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).map φ).app B ≫
        sheafHomEval X B C = (tensorHomEquiv X A B C).symm φ := by
  apply (tensorHomEquiv X A B C).injective
  rw [Equiv.apply_symm_apply, tensorHomEquiv_naturality_left, sheafHomEval,
    Equiv.apply_symm_apply, Category.comp_id]

/-- **Evaluation out of the sheaf-hom from an invertible module is an isomorphism**: if
tensoring on the right by `B` is an equivalence, then `ℋom(B, C) ⊗ B ⟶ C` is an isomorphism. -/
private theorem isIso_sheafHomEval
    [hB : ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).flip.obj B).IsEquivalence] :
    IsIso (sheafHomEval X B C) := by
  let E : _root_.SheafOfModules.{0} (structureSheafRing X) ⥤
      _root_.SheafOfModules.{0} (structureSheafRing X) :=
    (Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).flip.obj B
  haveI : E.IsEquivalence := hB
  let ev : E.obj (sheafHomSpace X B C) ⟶ C := sheafHomEval X B C
  have hE : ∀ {A : _root_.SheafOfModules.{0} (structureSheafRing X)}
      (φ : A ⟶ sheafHomSpace X B C), E.map φ ≫ ev = (tensorHomEquiv X A B C).symm φ :=
    fun φ => tensorMap_comp_sheafHomEval X φ
  change IsIso ev
  apply isIso_of_yoneda_map_bijective
  intro Z
  let e : E.obj (E.objPreimage Z) ≅ Z := E.objObjPreimageIso Z
  refine ⟨fun ψ₁ ψ₂ h => ?_, fun χ => ?_⟩
  · have h0 : ψ₁ ≫ ev = ψ₂ ≫ ev := h
    obtain ⟨φ₁, hφ₁⟩ := E.map_surjective (e.hom ≫ ψ₁)
    obtain ⟨φ₂, hφ₂⟩ := E.map_surjective (e.hom ≫ ψ₂)
    have h1 : E.map φ₁ ≫ ev = E.map φ₂ ≫ ev := by
      rw [hφ₁, hφ₂, Category.assoc, Category.assoc, h0]
    have h'' := (tensorHomEquiv X _ B C).symm.injective ((hE φ₁).symm.trans (h1.trans (hE φ₂)))
    rw [h''] at hφ₁
    exact (cancel_epi e.hom).1 (hφ₁.symm.trans hφ₂)
  · refine ⟨e.inv ≫ E.map (tensorHomEquiv X _ B C (e.hom ≫ χ)), ?_⟩
    change (e.inv ≫ E.map _) ≫ ev = _
    rw [Category.assoc, hE, Equiv.symm_apply_apply]
    exact Iso.inv_hom_id_assoc e χ

end Evaluation

section Assembly

open Opposite

attribute [local instance 10000] HasDerivedCategory.standard

variable {W : Scheme.{0}} (f : W ⟶ Spec (.of ℂ)) [IsProjectiveVariety ℂ f]
  (T : W.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor T]

omit [IsProjectiveVariety ℂ f] in
/-- Vanishing of the hypercohomology over `ℂ` of a module placed in degree zero is vanishing of
its classical module cohomology. -/
private theorem isZero_rightDerived_evaluation_of_subsingleton (M : W.Modules) (q : ℕ)
    (h : Subsingleton (Stacks.Duality.derivedCohomologyOverField f
      ((DerivedCategory.singleFunctor W.Modules 0).obj M) (q : ℤ))) :
    IsZero (((SheafOfModules.evaluation W.ringCatSheaf (op ⊤)).rightDerived q).obj M) := by
  have h1 : Subsingleton (cohomologyOverField ℂ f M q) :=
    @Equiv.subsingleton _ _
      (Stacks.Duality.cohomologyOverFieldLinearEquivDerivedCohomologyOverField ℂ f M q).toEquiv h
  exact @ModuleCat.isZero_of_subsingleton _ _ _ h1

/-- **Vanishing passes from module cohomology to the cohomology of the underlying abelian
sheaf.** -/
private theorem isZero_rightDerivedPlus_toSheaf_of_isZero (M : W.Modules) (q : ℕ)
    (h : IsZero (((SheafOfModules.evaluation W.ringCatSheaf (op ⊤)).rightDerived q).obj M)) :
    IsZero (((Stacks.Cohomology.Leray.sectionsFunctor W.toRingedSpace.carrier ⊤).rightDerivedPlus
      (q : ℤ)).obj ((SheafOfModules.toSheaf W.ringCatSheaf).obj M)) := by
  have h3 := (Functor.map_isZero (forget₂ _ AddCommGrpCat) h).of_iso
    ((Stacks.Cohomology.ModuleComparison.rightDerivedSectionsForgetIso _ ⊤ q).app M).symm
  exact h3.of_iso ((Stacks.DerivedIndexing.rightDerivedIso _ q).app _).symm

/-- A smooth ample divisor on a smooth projective variety of dimension at least two is a
projective variety. -/
private theorem isProjectiveVariety_subschemeι (hW : MMP.Mori.IsSmoothScheme f) {n : ℕ}
    (hn : topologicalKrullDim W = n)
    (hT : haveI := Stacks.Divisors.isInvertible_divisorSheaf T
      Stacks.Ample.IsAmple W (Stacks.Divisors.divisorSheaf T))
    (hTs : MMP.Mori.IsSmoothScheme (T.subschemeι ≫ f)) (hn2 : 2 ≤ n) :
    IsProjectiveVariety ℂ (T.subschemeι ≫ f) := by
  haveI : IsProper f := isProper_of_isProjectiveMorphism f ‹IsProjectiveVariety ℂ f›.isProjective
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : Smooth f := (MMP.Mori.isSmoothScheme_iff f).1 hW
  haveI : Smooth (T.subschemeι ≫ f) := (MMP.Mori.isSmoothScheme_iff _).1 hTs
  haveI : IsGorenstein W := isGorenstein_of_isRegular W (isRegular_of_smooth_over_field f)
  have hCM : IsCohenMacaulay W := isCohenMacaulay_of_isGorenstein W
  have hpure : ∀ Z ∈ irreducibleComponents W, topologicalKrullDim Z = n := by
    intro Z hZ
    obtain rfl : Z = Set.univ := by rwa [irreducibleComponents_eq_singleton] at hZ
    rw [(Homeomorph.Set.univ W).isHomeomorph.topologicalKrullDim_eq, hn]
  have hproj : IsProjective f :=
    (isProjectiveVariety_iff_isProjective' ℂ f).1 inferInstance |>.2
  haveI : IsIntegral W := ‹IsProjectiveVariety ℂ f›.toIsVariety.toIsIntegral
  have hconn := MMP.Mori.isConnected_support_of_isAmple_divisorSheaf f hproj hCM hn2 hpure T hT
  haveI : ConnectedSpace T.subscheme := by
    rw [← T.range_subschemeι] at hconn
    haveI := isConnected_iff_connectedSpace.1 hconn
    let e := T.subschemeι.isClosedEmbedding.toIsEmbedding.toHomeomorph
    exact e.symm.surjective.connectedSpace e.symm.continuous
  haveI : IsIntegral T.subscheme := Stacks.Chow.isIntegral_of_connectedSpace_of_smooth (T.subschemeι ≫ f)
  haveI : IsVariety ℂ (T.subschemeι ≫ f) :=
    (MMP.Mori.isVariety_iff ℂ _).mpr ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  exact (isProjectiveVariety_iff ℂ _).mpr
    ⟨inferInstance, (MMP.isProjectiveMorphism_of_isClosedImmersion _).comp
      ‹IsProjectiveVariety ℂ f›.isProjective⟩

omit [IsProjectiveVariety ℂ f] in
/-- The ideal sheaf `𝒪_W(-T)` of an effective Cartier divisor is the dual of `𝒪_W(T)`. -/
private theorem nonempty_negativeTwist_iso_dualSheaf :
    Nonempty ((Stacks.Divisors.negativeTwist T : W.Modules) ≅
      Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf (Stacks.Divisors.divisorSheaf T)) := by
  haveI := Stacks.Divisors.isTensorInvertible_negativeTwist T
  exact ⟨Stacks.SheafOfModules.Invertible.tensorInverseIsoDualSheaf W.presheaf W.ringCatSheaf.2
    (Stacks.Divisors.divisorSheaf T) (Stacks.Divisors.negativeTwist T)
    (Stacks.SheafOfModules.Scheme.evaluationIso W (Stacks.Divisors.negativeTwist' T))⟩

/-- **Negative Akizuki–Nakano vanishing for the twist by the divisor**:
`H^q(W, Ω^a_W(-T)) = 0` for `a + q < n`. -/
private theorem isZero_rightDerivedPlus_forms_tensor_negativeTwist
    (hW : MMP.Mori.IsSmoothScheme f) {n : ℕ} (hn : topologicalKrullDim W = n)
    (hT : haveI := Stacks.Divisors.isInvertible_divisorSheaf T
      Stacks.Ample.IsAmple W (Stacks.Divisors.divisorSheaf T)) (a q : ℕ) (haq : (a : ℤ) + q < n) :
    IsZero (((Stacks.Cohomology.Leray.sectionsFunctor W.toRingedSpace.carrier ⊤).rightDerivedPlus
      (q : ℤ)).obj ((SheafOfModules.toSheaf W.ringCatSheaf).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0} W.toRingedSpace.sheaf).obj
          (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) a)).obj
            (Stacks.Divisors.negativeTwist T : W.Modules)))) := by
  haveI := Stacks.Divisors.isInvertible_divisorSheaf T
  apply isZero_rightDerivedPlus_toSheaf_of_isZero _ q
  obtain ⟨e⟩ := nonempty_negativeTwist_iso_dualSheaf T
  have hN := isZero_rightDerived_evaluation_of_subsingleton f _ q
    (MMP.Mori.subsingleton_derivedCohomologyOverField_exteriorPower_tensor_dualSheaf_of_isAmple
      f hW n hn (Stacks.Divisors.divisorSheaf T) hT a q haq)
  exact hN.of_iso (((SheafOfModules.evaluation W.ringCatSheaf (op ⊤)).rightDerived q).mapIso
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0} W.toRingedSpace.sheaf).obj
      (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) a)).mapIso e))

/-- **A smooth ample divisor has dimension one less**: `dim T = n - 1`. -/
private theorem topologicalKrullDim_subscheme (hW : MMP.Mori.IsSmoothScheme f) {n : ℕ}
    (hn : topologicalKrullDim W = n)
    (hT : haveI := Stacks.Divisors.isInvertible_divisorSheaf T
      Stacks.Ample.IsAmple W (Stacks.Divisors.divisorSheaf T))
    (hTs : MMP.Mori.IsSmoothScheme (T.subschemeι ≫ f)) (hn2 : 2 ≤ n) :
    topologicalKrullDim T.subscheme = ((n - 1 : ℕ) : WithBot ℕ∞) := by
  haveI := isProjectiveVariety_subschemeι f T hW hn hT hTs hn2
  haveI : IsIntegral T.subscheme := ‹IsProjectiveVariety ℂ (T.subschemeι ≫ f)›.toIsVariety.toIsIntegral
  haveI : IsIntegral W := ‹IsProjectiveVariety ℂ f›.toIsVariety.toIsIntegral
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian f
  have hstalk : ringKrullDim (W.presheaf.stalk (T.subschemeι (genericPoint T.subscheme))) = 1 :=
    ringKrullDim_stalk_eq_one_of_isEffectiveCartierDivisor T ‹_› _
      ⟨⟨Set.univ, by simp [irreducibleComponents_eq_singleton]⟩,
        by simpa using genericPoint_spec (T.subscheme : Type)⟩
  have hcoh : Order.coheight (T.subschemeι (genericPoint T.subscheme)) = 1 := by
    have h := ringKrullDim_stalk_eq_coheight (T.subschemeι (genericPoint T.subscheme))
    rw [hstalk] at h
    exact_mod_cast h.symm
  let _ : W.Over (Spec (.of ℂ)) := ⟨f⟩
  have : LocallyOfFiniteType (W ↘ Spec (.of ℂ)) := inferInstanceAs (LocallyOfFiniteType f)
  have h := MMP.Intersection.Scheme.Subvariety.dim_add_codim ℂ
    (MMP.Intersection.Scheme.Subvariety.ofPoint (T.subschemeι (genericPoint T.subscheme)))
  rw [MMP.Intersection.Scheme.Subvariety.dim_eq_topologicalKrullDim_support,
    MMP.Intersection.Scheme.Subvariety.support_ofPoint,
    MMP.Intersection.Scheme.Subvariety.codim_eq_coheight_genericPoint,
    MMP.Intersection.Scheme.Subvariety.genericPoint_ofPoint, hcoh] at h
  have hcl : closure ({T.subschemeι (genericPoint T.subscheme)} : Set W) = (T.support : Set W) := by
    rw [← T.range_subschemeι, ← Set.image_singleton,
      T.subschemeι.isClosedEmbedding.closure_image_eq, genericPoint_closure, Set.image_univ]
  have h2 : topologicalKrullDim (T.support : Set W) + 1 = (n : WithBot ℕ∞) := by
    rw [← hcl, ← hn]
    exact_mod_cast h
  rw [T.subschemeι.isClosedEmbedding.toIsEmbedding.toHomeomorph.isHomeomorph.topologicalKrullDim_eq,
    show Set.range T.subschemeι = (T.support : Set W) from T.range_subschemeι]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  exact ENat.WithBot.add_one_cancel.1 (by exact_mod_cast h2)

omit [IsProjectiveVariety ℂ f] in
/-- The restriction of `𝒪_W(-T)` to `T` is the dual of the restriction of `𝒪_W(T)`. -/
private theorem nonempty_pullback_negativeTwist_iso_dualSheaf :
    haveI := Stacks.Divisors.isInvertible_divisorSheaf T
    Nonempty ((Scheme.Modules.pullback T.subschemeι).obj (Stacks.Divisors.negativeTwist T : W.Modules) ≅
      Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf
        ((Scheme.Modules.pullback T.subschemeι).obj (Stacks.Divisors.divisorSheaf T))) := by
  haveI := Stacks.Divisors.isTensorInvertible_negativeTwist T
  exact ⟨Stacks.SheafOfModules.Invertible.tensorInverseIsoDualSheaf T.subscheme.presheaf
    T.subscheme.ringCatSheaf.2
    ((Scheme.Modules.pullback T.subschemeι).obj (Stacks.Divisors.divisorSheaf T))
    ((Scheme.Modules.pullback T.subschemeι).obj (Stacks.Divisors.negativeTwist T : W.Modules))
    ((Stacks.RelativeVeryAmple.pullbackTensorModulesIso T.subschemeι _ _).symm ≪≫
      (Scheme.Modules.pullback T.subschemeι).mapIso
        (Stacks.SheafOfModules.Scheme.evaluationIso W (Stacks.Divisors.negativeTwist' T)) ≪≫
      @asIso _ _ _ _ _
        (SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal.{0} T.subschemeι.toRingCatSheafHom))⟩

/-- **Negative Akizuki–Nakano vanishing on the divisor**, pushed forward to `W`:
`H^q(W, i_*(Ω^p_T ⊗ i^*𝒪_W(-T))) = 0` for `p + q + 1 < n`. -/
private theorem isZero_rightDerivedPlus_pushforward_forms_tensor (hW : MMP.Mori.IsSmoothScheme f)
    {n : ℕ} (hn : topologicalKrullDim W = n)
    (hT : haveI := Stacks.Divisors.isInvertible_divisorSheaf T
      Stacks.Ample.IsAmple W (Stacks.Divisors.divisorSheaf T))
    (hTs : MMP.Mori.IsSmoothScheme (T.subschemeι ≫ f)) (hn2 : 2 ≤ n) (p q : ℕ)
    (hpq : (p : ℤ) + q + 1 < n) :
    IsZero (((Stacks.Cohomology.Leray.sectionsFunctor W.toRingedSpace.carrier ⊤).rightDerivedPlus
      (q : ℤ)).obj ((SheafOfModules.toSheaf W.ringCatSheaf).obj
        ((Scheme.Modules.pushforward T.subschemeι).obj
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0}
            T.subscheme.toRingedSpace.sheaf).obj
              (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials (T.subschemeι ≫ f)) p)).obj
                ((Scheme.Modules.pullback T.subschemeι).obj
                  (Stacks.Divisors.negativeTwist T : W.Modules)))))) := by
  haveI := Stacks.Divisors.isInvertible_divisorSheaf T
  haveI := isProjectiveVariety_subschemeι f T hW hn hT hTs hn2
  apply isZero_rightDerivedPlus_toSheaf_of_isZero _ q
  let LT := (Scheme.Modules.pullback T.subschemeι).obj (Stacks.Divisors.divisorSheaf T)
  haveI : SheafOfModules.IsInvertible T.subscheme.presheaf T.subscheme.ringCatSheaf.2 LT :=
    Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback T.subschemeι _
  have hLT : Stacks.Ample.IsAmple T.subscheme LT :=
    (Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple T.subscheme _).1
      (Scheme.Modules.isAmple_pullback_of_isClosedImmersion T.subschemeι _
        ((Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple W _).2 hT))
  have hNT := isZero_rightDerived_evaluation_of_subsingleton (T.subschemeι ≫ f) _ q
    (MMP.Mori.subsingleton_derivedCohomologyOverField_exteriorPower_tensor_dualSheaf_of_isAmple
      (T.subschemeι ≫ f) hTs (n - 1) (topologicalKrullDim_subscheme f T hW hn hT hTs hn2) LT hLT p q
      (by omega))
  obtain ⟨e⟩ := nonempty_pullback_negativeTwist_iso_dualSheaf T
  have hM := hNT.of_iso (((SheafOfModules.evaluation T.subscheme.ringCatSheaf (op ⊤)).rightDerived q).mapIso
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0} T.subscheme.toRingedSpace.sheaf).obj
      (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials (T.subschemeι ≫ f)) p)).mapIso e))
  have hM' : Subsingleton (cohomologyOverField ℂ (T.subschemeι ≫ f)
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0} T.subscheme.toRingedSpace.sheaf).obj
        (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials (T.subschemeι ≫ f)) p)).obj
          ((Scheme.Modules.pullback T.subschemeι).obj (Stacks.Divisors.negativeTwist T : W.Modules)))
      q) := by
    have := ModuleCat.subsingleton_of_isZero hM
    exact this
  have hW' := @Equiv.subsingleton _ _
    (cohomologyOverFieldPushforwardIsoOfIsClosedImmersion ℂ T.subschemeι f _ q).toLinearEquiv.toEquiv.symm hM'
  exact @ModuleCat.isZero_of_subsingleton _ _ _ hW'

/-- **Vanishing for the forms vanishing on the divisor**: `H^q(W, 𝒦^a) = 0` for `a + q < n`. -/
private theorem isZero_rightDerivedPlus_kernelComplex (hW : MMP.Mori.IsSmoothScheme f) {n : ℕ}
    (hn : topologicalKrullDim W = n)
    (hT : haveI := Stacks.Divisors.isInvertible_divisorSheaf T
      Stacks.Ample.IsAmple W (Stacks.Divisors.divisorSheaf T))
    (hTs : MMP.Mori.IsSmoothScheme (T.subschemeι ≫ f)) (a q : ℕ) (haq : (a : ℤ) + q < n) :
    IsZero (((Stacks.Cohomology.Leray.sectionsFunctor W.toRingedSpace.carrier ⊤).rightDerivedPlus
      (q : ℤ)).obj ((kernelComplex f T).X a)) := by
  haveI := Stacks.Divisors.isInvertible_divisorSheaf T
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : Smooth f := (MMP.Mori.isSmoothScheme_iff f).1 hW
  haveI : Smooth (T.subschemeι ≫ f) := (MMP.Mori.isSmoothScheme_iff _).1 hTs
  have hlog : f.HasLogPolesDeRhamComplex T := by
    have h := Scheme.Hom.hasLogPolesDeRhamComplex_of_smooth f (𝟙 (Spec (.of ℂ))) T ‹_›
    rwa [Category.comp_id] at h
  haveI hIinv : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2
      (Stacks.Divisors.negativeTwist T : W.Modules) :=
    Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
      (Stacks.Divisors.stacksIsInvertible_negativeTwist T)
  let E := (Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0} W.toRingedSpace.sheaf).flip.obj
    (Stacks.Divisors.negativeTwist T : W.Modules)
  have hEq : ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨W.toRingedSpace.presheaf,
      W.toRingedSpace.IsSheaf⟩).flip.obj (Stacks.Divisors.negativeTwist T)).IsEquivalence :=
    @Stacks.SheafOfModules.isEquivalence_tensorRightFunctor_of_stacksIsInvertible _ _ _
      W.presheaf _ _ _ (Stacks.Divisors.negativeTwist T)
      (Stacks.Divisors.stacksIsInvertible_negativeTwist T)
  have eK : ∀ p, E.obj (Scheme.Hom.logPolesForms f T p) ≅
      Scheme.Hom.formRestrictionKernelSheaf f T p := fun p =>
    @asIso _ _ _ _ (sheafHomEval W.toRingedSpace (Stacks.Divisors.negativeTwist T)
      (Scheme.Hom.formRestrictionKernelSheaf f T p))
      (@isIso_sheafHomEval W.toRingedSpace _ _ hEq)
  refine IsZero.of_iso ?_ (Functor.mapIso _ (kernelComplexXIso f T a))
  refine IsZero.of_iso ?_ ((Functor.mapIso _ (Functor.mapIso _ (eK a))).symm)
  rcases a with _ | p
  · have e0 : E.obj (Scheme.Hom.logPolesForms f T 0) ≅
        E.obj (Scheme.Hom.relativeDifferentialForms f ((0 : ℕ) : ℤ)) :=
      E.mapIso (@asIso _ _ _ _ (Scheme.Hom.logPolesFormsInclusion f T 0)
        (isIso_logPolesFormsInclusion_zero f T ‹_› hlog)).symm
    exact (isZero_rightDerivedPlus_forms_tensor_negativeTwist f T hW hn hT 0 q haq).of_iso
      (Functor.mapIso _ (Functor.mapIso _ e0))
  · let E' : SheafOfModules W.ringCatSheaf ⥤ SheafOfModules W.ringCatSheaf := E
    haveI : E'.IsEquivalence := hEq
    have hS := (residueShortComplex_shortExact f T ‹_› hlog p).map_of_exact E'
    have hS' := hS.map_of_exact (SheafOfModules.toSheaf W.ringCatSheaf)
    refine isZero_rightDerivedPlus_obj_X₂ _ _ hS' q ?_ ?_
    · exact isZero_rightDerivedPlus_forms_tensor_negativeTwist f T hW hn hT (p + 1) q haq
    · have pf' : E'.obj (Scheme.Hom.divisorForms f T p) ≅ (Scheme.Modules.pushforward T.subschemeι).obj
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0}
            T.subscheme.toRingedSpace.sheaf).obj
              (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials (T.subschemeι ≫ f)) p)).obj
                ((Scheme.Modules.pullback T.subschemeι).obj
                  (Stacks.Divisors.negativeTwist T : W.Modules))) :=
        @Stacks.ProjectionFormula.projectionFormulaIso _ _ T.subschemeι.toLRSHom.toShHom
          (Scheme.Hom.relativeDifferentialForms (T.subschemeι ≫ f) p)
          (Stacks.Divisors.negativeTwist T) (Stacks.Divisors.stacksIsInvertible_negativeTwist T)
      exact (isZero_rightDerivedPlus_pushforward_forms_tensor f T hW hn hT hTs (by omega) p q
        (by omega)).of_iso
          (((Stacks.Cohomology.Leray.sectionsFunctor W.toRingedSpace.carrier ⊤).rightDerivedPlus
            (q : ℤ)).mapIso ((SheafOfModules.toSheaf W.ringCatSheaf).mapIso pf'))

omit [IsProjectiveVariety ℂ f] [Stacks.Divisors.IsEffectiveCartierDivisor T] in
/-- A nonempty scheme locally of finite type and quasi-compact over `ℂ` has a complex point. -/
private theorem nonempty_complexPoints_of_nonempty {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    [LocallyOfFiniteType sX] [QuasiCompact sX] [Nonempty X] : Nonempty (ComplexPoints sX) := by
  letI : X.Over (Spec (.of ℂ)) := ⟨sX⟩
  have : CompactSpace X :=
    ⟨QuasiCompact.isCompact_preimage (f := sX) Set.univ isOpen_univ isCompact_univ⟩
  obtain ⟨x, -, hx⟩ := IsClosed.exists_closed_singleton (X := X) isClosed_univ Set.univ_nonempty
  have : LocallyOfFiniteType (X ↘ Spec (.of ℂ)) := show LocallyOfFiniteType sX from inferInstance
  obtain ⟨p⟩ : Nonempty (MMP.UnderlyingSpace ℂ X) :=
    ⟨(MMP.UnderlyingSpace.equivClosedPoints X).symm ⟨x, hx⟩⟩
  exact ⟨(ComplexPoints.homeomorphUnderlyingSpace (X := X)).symm p⟩

include f in
/-- **An ample effective Cartier divisor on a proper curve is nonempty**: its invertible sheaf has
positive degree, and that degree is `h⁰` of the divisor. -/
private theorem nonempty_subscheme_of_topologicalKrullDim_eq_one (hn : topologicalKrullDim W = 1)
    (hT : haveI := Stacks.Divisors.isInvertible_divisorSheaf T
      Stacks.Ample.IsAmple W (Stacks.Divisors.divisorSheaf T)) :
    Nonempty T.subscheme := by
  haveI : IsProper f := isProper_of_isProjectiveMorphism f ‹IsProjectiveVariety ℂ f›.isProjective
  haveI : IsCurve ℂ f := (isCurve_iff ℂ f).2 ⟨inferInstance, hn⟩
  have hdim : topologicalKrullDim W ≤ 1 := hn.le
  have hamp : Scheme.Modules.IsAmple W (Stacks.Divisors.divisorSheaf T) :=
    (Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple W _).2 hT
  have hpos := (isAmple_iff_invertibleCurveDegree_pos ℂ f hdim
    (Stacks.Divisors.divisorSheaf T)).1 hamp
  have hdeg := invertibleCurveDegree_eq_finrank_cohomologyOverField_zero_unit_zeroScheme ℂ f hdim
    (Stacks.Divisors.divisorSheaf T) (Stacks.Divisors.canonicalSection' T)
    (Stacks.Divisors.canonicalSection_isRegular T)
  have hz : zeroScheme W (Stacks.Divisors.divisorSheaf T)
      ((Stacks.Divisors.canonicalSection' T).eval (op ⊤)) = T :=
    Stacks.Divisors.zeroScheme_canonicalSection T
  rw [hz] at hdeg
  by_contra hne
  rw [not_nonempty_iff] at hne
  have h1 : Module.finrank ℂ (cohomologyOverField ℂ (T.subschemeι ≫ f)
      (SheafOfModules.unit T.subscheme.ringCatSheaf) 0) = 0 := by
    rw [finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections]
    letI : Algebra ℂ Γ(T.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of ℂ)).inv ≫ (T.subschemeι ≫ f).appTop).hom.toAlgebra
    exact Module.finrank_zero_of_subsingleton
  rw [hdeg, h1] at hpos
  exact lt_irrefl _ hpos

/-- The case of a curve: restriction `H^0(W; ℂ) ⟶ H^0(T; ℂ)` is injective. -/
private theorem injective_complexCohomologyMap_zero_of_topologicalKrullDim_eq_one
    (hW : MMP.Mori.IsSmoothScheme f)
    (hn : topologicalKrullDim W = 1)
    (hT : haveI := Stacks.Divisors.isInvertible_divisorSheaf T
      Stacks.Ample.IsAmple W (Stacks.Divisors.divisorSheaf T))
    (hTs : MMP.Mori.IsSmoothScheme (T.subschemeι ≫ f)) :
    Function.Injective (complexCohomologyMap
      (ComplexPoints.analyticMap (sX := T.subschemeι ≫ f) (sY := f) T.subschemeι rfl) 0).hom := by
  haveI : IsIntegral W := ‹IsProjectiveVariety ℂ f›.toIsVariety.toIsIntegral
  haveI : ConnectedSpace (ComplexPoints.analyticSpace f) := MMP.Fourfold.connectedSpace_analyticSpace f
  haveI : LocallyPathConnectedSpace (ComplexPoints.analyticSpace f) :=
    MMP.Fourfold.locallyPathConnectedSpace_analyticSpace f
  haveI : PathConnectedSpace (ComplexPoints.analyticSpace f) :=
    pathConnectedSpace_iff_connectedSpace.2 ‹_›
  haveI := nonempty_subscheme_of_topologicalKrullDim_eq_one f T hn hT
  haveI : Nonempty (ComplexPoints.analyticSpace (T.subschemeι ≫ f)) :=
    nonempty_complexPoints_of_nonempty (T.subschemeι ≫ f)
  exact injective_complexCohomologyMap_zero _

end Assembly

/-- **Weak Lefschetz injectivity.** Let `W` be a smooth complex projective variety of dimension
`n` and `T` a smooth ample effective Cartier divisor on `W`. Then for every `k < n` the
restriction map `H^k(W(ℂ); ℚ) ⟶ H^k(T(ℂ); ℚ)` on rational singular cohomology is injective. -/
theorem solution :
    ∀ {W : Scheme.{0}} (f : W ⟶ Spec (.of ℂ)) [IsProjectiveVariety ℂ f]
    (hW : MMP.Mori.IsSmoothScheme f) {n : ℕ} (hn : topologicalKrullDim W = n)
    (T : W.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor T]
    (hT : haveI := Stacks.Divisors.isInvertible_divisorSheaf T
      Stacks.Ample.IsAmple W (Stacks.Divisors.divisorSheaf T))
    (hTs : MMP.Mori.IsSmoothScheme (T.subschemeι ≫ f)) {k : ℕ} (hk : k < n),
    Function.Injective
      (MMP.Fourfold.rationalCohomologyMap
        (ComplexPoints.analyticMap (sX := T.subschemeι ≫ f) (sY := f) T.subschemeι rfl) k) := by
  intro W f _ hW n hn T _ hT hTs k hk
  apply injective_rationalCohomologyMap_of_injective_complexCohomologyMap
  by_cases hn2 : 2 ≤ n
  · haveI := isProjectiveVariety_subschemeι f T hW hn hT hTs hn2
    exact injective_complexCohomologyMap_of_injective_deRhamCohomologyPullback
      (T.subschemeι ≫ f) f hTs hW T.subschemeι rfl k
      (injective_deRhamCohomologyPullback_subschemeι f T n
        (isZero_rightDerivedPlus_kernelComplex f T hW hn hT hTs) k (by omega))
  · obtain rfl : n = 1 := by omega
    obtain rfl : k = 0 := by omega
    exact injective_complexCohomologyMap_zero_of_topologicalKrullDim_eq_one f T hW hn hT hTs

end MMP.ConductorThreefoldWeakLefschetzTwo

namespace MMP.Analytic

/-- **Weak Lefschetz injectivity.** Let `W` be a smooth projective complex variety of dimension
`n` and `T` a smooth effective Cartier divisor on `W` with `𝒪_W(T)` ample. Then for `k < n`,
restriction `H^k(W^an; ℚ) → H^k(T^an; ℚ)` along the inclusion `T ↪ W` is injective. -/
@[mmp "lem_mmp_conductor_threefold_weak_lefschetz_two"]
public theorem injective_rationalCohomologyMap_subschemeι_of_isAmple
    {W : Scheme.{0}} (f : W ⟶ Spec (.of ℂ)) [IsProjectiveVariety ℂ f]
    (hW : MMP.Mori.IsSmoothScheme f) {n : ℕ} (hn : topologicalKrullDim W = n)
    (T : W.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor T]
    (hT : haveI := Stacks.Divisors.isInvertible_divisorSheaf T
      Stacks.Ample.IsAmple W (Stacks.Divisors.divisorSheaf T))
    (hTs : MMP.Mori.IsSmoothScheme (T.subschemeι ≫ f)) {k : ℕ} (hk : k < n) :
    Function.Injective
      (MMP.Fourfold.rationalCohomologyMap
        (ComplexPoints.analyticMap (sX := T.subschemeι ≫ f) (sY := f) T.subschemeι rfl) k) :=
  MMP.ConductorThreefoldWeakLefschetzTwo.solution f hW hn T hT hTs hk

end MMP.Analytic
