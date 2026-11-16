module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.LogMinimalModel
public import MMP.AlgebraicGeometry.Divisor.Canonical.Basic
public import MMP.AlgebraicGeometry.Divisor.Arithmetic
public import MMP.AlgebraicGeometry.Divisor.Pullback
public import MMP.AlgebraicGeometry.Divisor.SNC
public import MMP.AlgebraicGeometry.Divisor.LinearSystem
public import MMP.AlgebraicGeometry.MMP.BasepointFree.ProofData
public import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.SepClosedComponents
public import MMP.AlgebraicGeometry.Resolution.BlowupChartClosedImmersion
public import MMP.AlgebraicGeometry.Divisor.SmoothWeilCartier
public import MMP.AlgebraicGeometry.Positivity.SerreAmpleCartier
public import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalCurveNegativity
public import MMP.AlgebraicGeometry.Divisor.RegularWeilCartier
public import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.Corollaries
public import MMP.AlgebraicGeometry.MMP.BasepointFree.RelativelyFreeTwist
public import MMP.AlgebraicGeometry.Divisor.Canonical.TopFormGenerator
public import MMP.AlgebraicGeometry.Cohomology.ProperCoherentSections
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormulaMultiplicities.MultiplicityOneSmoothness
public import MMP.AlgebraicGeometry.Singularities.CyclicCover.UnramifiedOffZeroScheme
public import MMP.AlgebraicGeometry.Divisor.AmpleSectionDivisor
public import MMP.AlgebraicGeometry.Curves.Maps.CoefficientSpace
public import MMP.AlgebraicGeometry.Resolution.OrderReduction.RegularStalkComponents
public import MMP.AlgebraicGeometry.Vanishing.SncTorsionFreeness
public import MMP.AlgebraicGeometry.SubschemeOver
public import StacksFrontier.AlgebraicGeometry.Limits.ProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Cover
public import StacksFrontier.AlgebraicGeometry.ProjBaseChange.IsIso
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceZero
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.HProjective
public import StacksFrontier.AlgebraicGeometry.FiniteMorphismProjective.Projective
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.Composition
public import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
public import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
public import MMP.AlgebraicGeometry.Divisor.SmoothDivisorRestriction
public import MMP.AlgebraicGeometry.Divisor.SmoothDivisorAdjunction
public import MMP.AlgebraicGeometry.Morphisms.ValuativeCentre
public import MMP.AlgebraicGeometry.Bertini.FreeLinearSystem
public import MMP.AlgebraicGeometry.Bertini.FreeSystemIrreducible
public import MMP.AlgebraicGeometry.Intersection.Surface.Symmetry
public import StacksFrontier.AlgebraicGeometry.EnriquesSeveriZariski.GlobalSections
public import StacksFrontier.AlgebraicGeometry.Properties.NormalConnectedIntegral
public import MMP.AlgebraicGeometry.Bertini.GeneralHyperplane
public import MMP.AlgebraicGeometry.Vanishing.SemiampleInjectivity
public import MMP.AlgebraicGeometry.Morphisms.HProjective

section

/-!
# Vanishing of cohomology of higher direct images of snc adjoint sheaves

Let `f : V ⟶ X` be a projective morphism of complex projective varieties with `V` smooth, let
`B` be an snc `ℚ`-divisor on `V` with coefficients in `[0, 1]` and let `M` be a Cartier divisor
with `M - (K_V + B) ∼_ℚ f^*H` for an ample `H`. Then `H^p(X, R^q f_* 𝒪_V(M)) = 0` for `p > 0`.

The proof inducts on the dimension of the image of `f`.

* For `p ≥ 2`: when the image has dimension at most one this is Grothendieck's vanishing theorem
  for the coherent sheaf `R^q f_* 𝒪_V(M)`, supported on the image. Otherwise a general member
  `A` of a large multiple of `H` pulls back to a smooth prime divisor `F` transverse to `B`, and
  `A` misses the associated points of every `R^q f_* 𝒪_V(M)`, which by torsion-freeness are the
  generic points of images of strata. Multiplication by the equation of `A` is then injective on
  the direct images, and the restriction sequence `0 → 𝒪_V(M) → 𝒪_V(M + F) → 𝒪_F(M + F) → 0`
  gives short exact sequences of direct images. Serre vanishing kills the cohomology of the
  middle terms, and adjunction together with the induction kills that of the last terms.
* For `p = 1`: the higher cohomology of the direct images of `𝒪_V(M)` is concentrated in the
  columns `0` and `1`, so `H^1(X, R^q f_* 𝒪_V(M))` is the kernel of the edge map
  `H^{q+1}(V, 𝒪_V(M)) → H^0(X, R^{q+1} f_* 𝒪_V(M))`. The edge map for `𝒪_V(M + F)` is an
  isomorphism, and `H^{q+1}(V, 𝒪_V(M)) → H^{q+1}(V, 𝒪_V(M + F))` is injective by the
  injectivity theorem for a semiample adjoint difference, so that kernel vanishes.

## Implementation notes

The Leray spectral sequence is not used. The columns statement is proved directly on the complex
`f_* I^•` of `Γ(X, -)`-acyclic sheaves, for an injective resolution `I^•`, by dimension shifting
along its cycles and boundaries.

## References

* [O. Fujino, *Fundamental theorems for the log minimal model program*][Fujino2011],
  Theorem 6.3
* [J. Kollár, *Higher direct images of dualizing sheaves I*][Kollar1986], Theorem 2.1
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MMP.Mori Opposite

namespace MMP.FourfoldProofs.MmpLcBpfSncDirectImageVanishingProof

/-! ### Cohomology of a complex of acyclic objects -/

section Homological

open Stacks.RightDerivedComp Stacks.Cohomology.RightDerivedCoEdge

variable {D : Type*} [Category D] [Abelian D] {E : Type*} [Category E] [Abelian E]
  [EnoughInjectives D] (T : D ⥤ E) [T.Additive] [PreservesFiniteLimits T]

/-- A short exact sequence stays short exact under a left exact functor as soon as its first
term is acyclic. -/
private theorem shortExact_map_of_acyclic_X₁ (S : ShortComplex D) (hS : S.ShortExact)
    (h₁ : acyclic T S.X₁) : (S.map T).ShortExact := by
  letI := HasDerivedCategory.standard D
  letI := HasDerivedCategory.standard E
  have h := (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono T).1 inferInstance S hS
  exact
    { exact := h.1
      mono_f := h.2
      epi_g := Functor.epi_map_g T hS
        (((Functor.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus T S.X₁).2
          inferInstance).1 ((rightAcyclic_iff_acyclic T S.X₁).2 h₁) 1 one_pos) }

/-- In a short exact sequence, vanishing of `R^p T` at the outer terms gives vanishing at the
middle term. -/
private theorem isZero_rightDerived_X₂ {S : ShortComplex D} (hS : S.ShortExact) (p : ℕ)
    (h₁ : IsZero ((T.rightDerived p).obj S.X₁)) (h₃ : IsZero ((T.rightDerived p).obj S.X₃)) :
    IsZero ((T.rightDerived p).obj S.X₂) := by
  letI := HasDerivedCategory.standard D
  letI := HasDerivedCategory.standard E
  exact ((Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives T).exact_map hS
    p).isZero_X₂ (h₁.eq_of_src _ _) (h₃.eq_of_tgt _ _)

/-- In a short exact sequence, vanishing of `R^{p+1} T` at the first term and of `R^p T` at the
middle term gives vanishing of `R^p T` at the last term. -/
private theorem isZero_rightDerived_X₃ {S : ShortComplex D} (hS : S.ShortExact) (p : ℕ)
    (h₂ : IsZero ((T.rightDerived p).obj S.X₂))
    (h₁ : IsZero ((T.rightDerived (p + 1)).obj S.X₁)) :
    IsZero ((T.rightDerived p).obj S.X₃) := by
  letI := HasDerivedCategory.standard D
  letI := HasDerivedCategory.standard E
  have h := (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives T).exact_δ₁ hS p
  exact h.isZero_X₂ (h₂.eq_of_src _ _) (h₁.eq_of_tgt _ _)

/-- In a short exact sequence with `T`-acyclic middle term, `R^1 T` of the first term vanishes
as soon as `T` keeps the quotient map an epimorphism. -/
private theorem isZero_rightDerived_one_X₁ {S : ShortComplex D} (hS : S.ShortExact)
    (h₂ : acyclic T S.X₂) (hepi : Epi (T.map S.g)) :
    IsZero ((T.rightDerived 1).obj S.X₁) := by
  letI := HasDerivedCategory.standard D
  letI := HasDerivedCategory.standard E
  let F := Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives T
  haveI : Epi (F.δ hS 0) := F.epi_δ_of_map_f_eq_zero hS 0 ((h₂ 1 one_pos).eq_of_tgt _ _)
  haveI hg : Epi ((F.functor 0).map S.g) := by
    have e := (Functor.rightDerivedZeroIsoSelf T).hom.naturality S.g
    have e' : (T.rightDerived 0).map S.g = ((Functor.rightDerivedZeroIsoSelf T).hom.app S.X₂ ≫
        T.map S.g) ≫ (Functor.rightDerivedZeroIsoSelf T).inv.app S.X₃ := by
      rw [← e, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
    change Epi ((T.rightDerived 0).map S.g)
    rw [e']
    infer_instance
  have h0 : F.δ hS 0 = 0 := by
    rw [← cancel_epi ((F.functor 0).map S.g), F.map_g_δ, comp_zero]
  have hz := IsZero.of_epi_eq_zero (F.δ hS 0) h0
  exact hz

/-- The cycles and boundaries of a complex of `T`-acyclic objects whose cohomology in degrees
`≤ n` has no `R^p T` for `p ≥ 2`: the cycles in degree `m ≤ n` have no `R^p T` for `p ≥ 2`, and
the boundaries out of degree `m` are `T`-acyclic. -/
private theorem cycles_boundaries_of_le (K : CochainComplex D ℕ)
    (hX : ∀ q, acyclic T (K.X q)) (n : ℕ)
    (h2 : ∀ q ≤ n, ∀ p, 2 ≤ p → IsZero ((T.rightDerived p).obj (K.homology q))) :
    ∀ m ≤ n, (∀ p, 2 ≤ p → IsZero ((T.rightDerived p).obj (K.cycles m))) ∧
      acyclic T (cokernel (K.iCycles m)) := by
  have hB : ∀ m, (∀ p, 2 ≤ p → IsZero ((T.rightDerived p).obj (K.cycles m))) →
      acyclic T (cokernel (K.iCycles m)) := fun m hZ p hp =>
    isZero_rightDerived_X₃ T (shortExact_cycles K m) p (hX m p hp) (hZ (p + 1) (by omega))
  intro m hm
  induction m with
  | zero =>
    have hZ : ∀ p, 2 ≤ p → IsZero ((T.rightDerived p).obj (K.cycles 0)) := fun p hp =>
      (h2 0 (Nat.zero_le _) p hp).of_iso
        ((T.rightDerived p).mapIso (CochainComplex.isoHomologyπ₀ K))
    exact ⟨hZ, hB 0 hZ⟩
  | succ m ih =>
    obtain ⟨-, hBm⟩ := ih (by omega)
    have hZ : ∀ p, 2 ≤ p → IsZero ((T.rightDerived p).obj (K.cycles (m + 1))) := fun p hp =>
      isZero_rightDerived_X₂ T (shortExact_boundaries K m (m + 1) rfl) p
        (hBm p (by omega)) (h2 (m + 1) hm p hp)
    exact ⟨hZ, hB (m + 1) hZ⟩

/-- **Two columns.** Let `K` be a complex of `T`-acyclic objects whose cohomology objects in
degrees `≤ n` have no `R^p T` for `p ≥ 2`. If the comparison `H^{n+1}(T K) ⟶ T(H^{n+1} K)` is a
monomorphism, then `R^1 T (H^n K) = 0`. -/
private theorem isZero_rightDerived_one_homology_of_mono (K : CochainComplex D ℕ)
    (hX : ∀ q, acyclic T (K.X q)) (n : ℕ)
    (h2 : ∀ q ≤ n, ∀ p, 2 ≤ p → IsZero ((T.rightDerived p).obj (K.homology q)))
    (hmono : Mono (homologyToMapHomology T K (n + 1))) :
    IsZero ((T.rightDerived 1).obj (K.homology n)) := by
  have hcb := cycles_boundaries_of_le T K hX n h2
  -- `T` keeps `Kⁿ ⟶ Bⁿ⁺¹` an epimorphism
  set TK := (T.mapHomologicalComplex (ComplexShape.up ℕ)).obj K
  let j := T.map (boundariesToCycles K n (n + 1)) ≫ (mapCyclesIso T K (n + 1)).hom
  haveI : Mono (boundariesToCycles K n (n + 1)) := mono_boundariesToCycles K n (n + 1) rfl
  haveI : Mono j := mono_comp _ _
  have hj0 : j ≫ TK.homologyπ (n + 1) = 0 := by
    rw [← cancel_mono (homologyToMapHomology T K (n + 1)), zero_comp, Category.assoc,
      Category.assoc, homologyπ_comp_homologyToMapHomology, Iso.hom_inv_id_assoc,
      ← T.map_comp, boundariesToCycles_comp_homologyπ, T.map_zero]
  have hto : T.map (cokernel.π (K.iCycles n)) ≫ j = TK.toCycles n (n + 1) := by
    change T.map _ ≫ T.map _ ≫ _ = _
    rw [← T.map_comp_assoc, π_comp_boundariesToCycles, ← toCycles_comp_mapCyclesIso_inv,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hex : (ShortComplex.mk (TK.toCycles n (n + 1)) (TK.homologyπ (n + 1))
      (TK.toCycles_comp_homologyπ n (n + 1))).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ (TK.homologyIsCokernel n (n + 1) (by simp))
  have hepi : Epi (T.map (cokernel.π (K.iCycles n))) := by
    rw [epi_iff_surjective_up_to_refinements]
    intro A y
    obtain ⟨A', π, hπ, x, hx⟩ := hex.exact_up_to_refinements (y ≫ j)
      (by rw [Category.assoc, hj0, comp_zero])
    refine ⟨A', π, hπ, x, ?_⟩
    rw [← cancel_mono j, Category.assoc, Category.assoc, hto]
    exact hx
  have hZ1 : IsZero ((T.rightDerived 1).obj (K.cycles n)) :=
    isZero_rightDerived_one_X₁ T (shortExact_cycles K n) (hX n) hepi
  obtain _ | m := n
  · exact hZ1.of_iso ((T.rightDerived 1).mapIso (CochainComplex.isoHomologyπ₀ K).symm)
  · exact isZero_rightDerived_X₃ T (shortExact_boundaries K m (m + 1) rfl) 1 hZ1
      ((hcb m (by omega)).2 2 (by omega))

/-- A left exact functor commutes with the cohomology of a complex of acyclic objects in
degree `n` as soon as the cohomology is acyclic in the degrees below `n`. -/
private theorem isIso_homologyToMapHomology_of_acyclic_lt (K : CochainComplex D ℕ)
    (hX : ∀ q, acyclic T (K.X q)) (n : ℕ) (hH : ∀ q < n, acyclic T (K.homology q)) :
    IsIso (homologyToMapHomology T K n) := by
  have hcyc : ∀ m, (∀ q ≤ m, acyclic T (K.homology q)) → acyclic T (K.cycles m) := by
    intro m
    induction m with
    | zero => exact fun h => acyclic_of_iso T (CochainComplex.isoHomologyπ₀ K).symm (h 0 le_rfl)
    | succ m ih =>
      exact fun h => (acyclic_shortExact_X₂ T _ (shortExact_boundaries K m (m + 1) rfl)
        (acyclic_shortExact T _ (shortExact_cycles K m)
          (ih fun q hq => h q (by omega)) (hX m)).1 (h (m + 1) le_rfl)).1
  obtain _ | n := n
  · exact isIso_homologyToMapHomology_zero T K
  · have h := acyclic_shortExact T _ (shortExact_cycles K n)
      (hcyc n fun q hq => hH q (by omega)) (hX n)
    have hTH : IsColimit (CokernelCofork.ofπ (T.map (K.homologyπ (n + 1)))
        (show T.map (boundariesToCycles K n (n + 1)) ≫ T.map (K.homologyπ (n + 1)) = 0 by
          rw [← T.map_comp, boundariesToCycles_comp_homologyπ, T.map_zero])) :=
      (shortExact_map_of_acyclic_X₁ T _ (shortExact_boundaries K n (n + 1) rfl) h.1).gIsCokernel
    haveI : Epi (T.map (cokernel.π (K.iCycles n))) := h.2.epi_g
    exact isIso_homologyToMapHomology_of_isColimit T K (n + 1) n
      (isCokernelEpiComp hTH (T.map (cokernel.π (K.iCycles n)))
        (by rw [← T.map_comp, π_comp_boundariesToCycles]))

end Homological

/-! ### The first column of the Leray spectral sequence -/

/-- The global sections functor `Γ(X, -)` on `𝒪_X`-modules. -/
private abbrev sections (X : Scheme.{0}) :
    X.Modules ⥤ ModuleCat.{0} (X.ringCatSheaf.obj.obj (op ⊤)) :=
  _root_.SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))

private theorem sections_additive (X : Scheme.{0}) : (sections X).Additive where
  map_add := (AlgebraicGeometry.evaluationAdditive X).map_add

private theorem sections_preservesFiniteLimits (X : Scheme.{0}) :
    PreservesFiniteLimits (sections X) :=
  inferInstanceAs (PreservesFiniteLimits
    (_root_.SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))))

attribute [local instance] sections_additive sections_preservesFiniteLimits

/-- The pushforward of an injective module is acyclic for `Γ(X, -)`. -/
private theorem acyclic_sections_pushforward_of_injective {V X : Scheme.{0}} (f : V ⟶ X)
    (I : V.Modules) [Injective I] :
    Stacks.RightDerivedComp.acyclic (sections X) ((Scheme.Modules.pushforward f).obj I) :=
  fun p hp => (Stacks.Cohomology.CechAcyclic.isZero_rightDerived_evaluation_iff_isZero_Hgroup
    _ _ p _).2
    (Stacks.AlgebraicGeometry.LerayAffineBase.isZero_hgroup_pushforward_injective f p hp I
      inferInstance)

/-- **The first column of the Leray spectral sequence.** Let `g : G ⟶ G'` be a map of modules on
`V` and `f : V ⟶ X`. Suppose that the higher direct images `R^q f_* G`, `q ≤ n`, have no
cohomology in degrees `≥ 2`, that those of `G'` have no positive cohomology, and that
`g` induces a monomorphism `H^{n+1}(V, G) ⟶ H^{n+1}(V, G')`. Then
`H^1(X, R^n f_* G) = 0`. -/
private theorem isZero_rightDerived_one_rightDerived_pushforward {V X : Scheme.{0}}
    (f : V ⟶ X) {G G' : V.Modules} (g : G ⟶ G') (n : ℕ)
    (h2 : ∀ q ≤ n, ∀ p, 2 ≤ p → IsZero (((sections X).rightDerived p).obj
      (((Scheme.Modules.pushforward f).rightDerived q).obj G)))
    (h' : ∀ q ≤ n, ∀ p, 0 < p → IsZero (((sections X).rightDerived p).obj
      (((Scheme.Modules.pushforward f).rightDerived q).obj G')))
    (hinj : Mono (((Scheme.Modules.pushforward f ⋙ sections X).rightDerived (n + 1)).map g)) :
    IsZero (((sections X).rightDerived 1).obj
      (((Scheme.Modules.pushforward f).rightDerived n).obj G)) := by
  open Stacks.Cohomology.RightDerivedCoEdge in
  let P := Scheme.Modules.pushforward f
  let T := sections X
  let I := injectiveResolution G
  let J := injectiveResolution G'
  let φ := InjectiveResolution.desc g J I
  have comm := InjectiveResolution.desc_commutes_zero g J I
  let K := (P.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  let K' := (P.mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex
  let ψ : K ⟶ K' := (P.mapHomologicalComplex (ComplexShape.up ℕ)).map φ
  have hX : ∀ q, Stacks.RightDerivedComp.acyclic T (K.X q) := fun q => by
    haveI := I.injective q
    exact acyclic_sections_pushforward_of_injective f _
  have hX' : ∀ q, Stacks.RightDerivedComp.acyclic T (K'.X q) := fun q => by
    haveI := J.injective q
    exact acyclic_sections_pushforward_of_injective f _
  -- the comparison for `G'` is an isomorphism
  have hiso' : IsIso (homologyToMapHomology T K' (n + 1)) :=
    isIso_homologyToMapHomology_of_acyclic_lt T K' hX' (n + 1) fun q hq p hp =>
      (h' q (by omega) p hp).of_iso ((T.rightDerived p).mapIso (J.isoRightDerivedObj P q).symm)
  -- the map on cohomology upstairs is a monomorphism
  have hnat := Stacks.Cohomology.RightDerivedEdge.isoRightDerivedObjComp_inv_naturality P T g I J
    φ comm (n + 1)
  have hmap : Mono (HomologicalComplex.homologyMap
      ((T.mapHomologicalComplex (ComplexShape.up ℕ)).map ψ) (n + 1)) := by
    have e : HomologicalComplex.homologyMap
        ((T.mapHomologicalComplex (ComplexShape.up ℕ)).map ψ) (n + 1) =
        (Stacks.Cohomology.RightDerivedEdge.isoRightDerivedObjComp P T I (n + 1)).inv ≫
          ((P ⋙ T).rightDerived (n + 1)).map g ≫
          (Stacks.Cohomology.RightDerivedEdge.isoRightDerivedObjComp P T J (n + 1)).hom := by
      rw [← Category.assoc, hnat, Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rfl
    rw [e]
    exact @mono_comp _ _ _ _ _ _ (@IsIso.mono_of_iso _ _ _ _ _ (Iso.isIso_inv _)) _
      (@mono_comp _ _ _ _ _ _ hinj _ (@IsIso.mono_of_iso _ _ _ _ _ (Iso.isIso_hom _)))
  have hmono : Mono (homologyToMapHomology T K (n + 1)) := by
    have hfac := homologyToMapHomology_naturality T ψ (n + 1)
    have : Mono (homologyToMapHomology T K (n + 1) ≫
        T.map (HomologicalComplex.homologyMap ψ (n + 1))) := by
      rw [← hfac]
      exact mono_comp' hmap (IsIso.mono_of_iso _)
    exact mono_of_mono _ (T.map (HomologicalComplex.homologyMap ψ (n + 1)))
  exact (isZero_rightDerived_one_homology_of_mono T K hX n (fun q hq p hp =>
      (h2 q hq p hp).of_iso ((T.rightDerived p).mapIso (I.isoRightDerivedObj P q).symm))
      hmono).of_iso ((T.rightDerived 1).mapIso (I.isoRightDerivedObj P n))

/-! ### Higher direct images along a short exact sequence -/

/-- If `R^q f_*` of the first map of a short exact sequence is a monomorphism in degrees `q` and
`q + 1`, then `R^q f_*` of the sequence is short exact. -/
private theorem shortExact_rightDerived_pushforward {V X : Scheme.{0}} (f : V ⟶ X)
    {S : ShortComplex V.Modules} (hS : S.ShortExact) (q : ℕ)
    (h₀ : Mono (((Scheme.Modules.pushforward f).rightDerived q).map S.f))
    (h₁ : Mono (((Scheme.Modules.pushforward f).rightDerived (q + 1)).map S.f)) :
    (S.map ((Scheme.Modules.pushforward f).rightDerived q)).ShortExact := by
  letI := HasDerivedCategory.standard V.Modules
  letI := HasDerivedCategory.standard X.Modules
  let F := Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
    (Scheme.Modules.pushforward f)
  haveI : Mono ((F.functor (q + 1)).map S.f) := h₁
  have hδ : F.δ hS q = 0 := by
    rw [← cancel_mono ((F.functor (q + 1)).map S.f), zero_comp, F.δ_map_f]
  have hepi : Epi ((F.functor q).map S.g) :=
    (ShortComplex.exact_iff_epi _ hδ).1 (F.exact_δ₁ hS q)
  exact { exact := F.exact_map hS q, mono_f := h₀, epi_g := hepi }

/-- In a short exact sequence of modules on `X`, `H^{p+1}` of the first term vanishes when `H^p`
of the last and `H^{p+1}` of the middle term vanish. -/
private theorem isZero_rightDerived_sections_X₁ {X : Scheme.{0}} {S : ShortComplex X.Modules}
    (hS : S.ShortExact) (p : ℕ)
    (h₃ : IsZero (((sections X).rightDerived p).obj S.X₃))
    (h₂ : IsZero (((sections X).rightDerived (p + 1)).obj S.X₂)) :
    IsZero (((sections X).rightDerived (p + 1)).obj S.X₁) := by
  letI := HasDerivedCategory.standard X.Modules
  letI := HasDerivedCategory.standard (ModuleCat.{0} (X.ringCatSheaf.obj.obj (op ⊤)))
  have h := (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
    (sections X)).exact_δ₂ hS p
  exact h.isZero_X₂ (h₃.eq_of_src _ _) (h₂.eq_of_tgt _ _)

/-! ### The data -/

/-- The data of the theorem for a fixed target `X` and ample sheaf `L`. -/
private structure Datum (X : Scheme.{0}) (sX : X ⟶ Spec (.of ℂ)) (L : X.Modules) where
  V : Scheme.{0}
  sV : V ⟶ Spec (.of ℂ)
  [proj : MMP.Mori.IsProjectiveVariety ℂ sV]
  hVsm : IsSmoothScheme sV
  [ln : IsLocallyNoetherian V]
  [nrm : IsNormal V]
  f : V ⟶ X
  hfs : f ≫ sX = sV
  hfp : IsProjective f
  n : ℕ
  K : Divisor V
  hK : K.IsCanonicalDivisor sV n
  B : QDivisor V
  hB : B.IsSNC sV
  hB0 : ∀ E, 0 ≤ B E
  hB1 : ∀ E, B E ≤ 1
  M : Divisor V
  hM : M.IsCartier
  hlin : ∃ m : ℕ, 0 < m ∧ ∃ D : Divisor V,
    Divisor.toQDivisor D = (m : ℚ) • (Divisor.toQDivisor M - (Divisor.toQDivisor K + B)) ∧
    Nonempty (D.divisorialSheaf ≅ (Scheme.Modules.pullback f).obj L)

attribute [local instance] Datum.proj Datum.ln Datum.nrm

variable {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {L : X.Modules}

private theorem Datum.isIntegral (δ : Datum X sX L) : IsIntegral δ.V :=
  ((AlgebraicGeometry.isProjectiveVariety_iff ℂ δ.sV).1 δ.proj).1.toIsIntegral

/-- Every divisor on the smooth variety `V` is Cartier. -/
private theorem Datum.isCartier (δ : Datum X sX L) (D : Divisor δ.V) : D.IsCartier := by
  haveI : IsSmoothVariety ℂ δ.sV :=
    { toIsVariety := inferInstance, toSmooth := (isSmoothScheme_iff _).mp δ.hVsm }
  exact (Divisor.cartier_weil_dictionary_of_isSmoothVariety ℂ δ.sV).1 D

/-- The dimension of the image of `f`. -/
private noncomputable def Datum.dim (δ : Datum X sX L) : WithBot ℕ∞ :=
  topologicalKrullDim (closure (Set.range δ.f.base))

/-- The cohomology `H^p(X, R^q f_* 𝒪_V(M))` of the datum. -/
private noncomputable abbrev Datum.coh (δ : Datum X sX L) (p q : ℕ) :=
  ((sections X).rightDerived p).obj
    (((Scheme.Modules.pushforward δ.f).rightDerived q).obj δ.M.divisorialSheaf)

/-! ### Strata -/

/-- In a Noetherian space the maximal irreducible subsets of a closed set are finite in
number. -/
private theorem finite_maximal_irreducible_subset {Y : Type*} [TopologicalSpace Y]
    [TopologicalSpace.NoetherianSpace Y] (C : Set Y) (hC : IsClosed C) :
    {S : Set Y | Maximal (fun T : Set Y => IsIrreducible T ∧ T ⊆ C) S}.Finite := by
  classical
  obtain ⟨F, hF, hCF⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finset_irreducible
      (⟨C, hC⟩ : TopologicalSpace.Closeds Y)
  refine ((F.image (fun k : TopologicalSpace.Closeds Y => (k : Set Y))).finite_toSet).subset ?_
  intro S hS
  have hCeq : C = ⋃₀ ((F.image (fun k : TopologicalSpace.Closeds Y => (k : Set Y)) :
      Finset (Set Y)) : Set (Set Y)) := by
    have := congrArg (fun s : TopologicalSpace.Closeds Y => (s : Set Y)) hCF
    rw [show C = ((⟨C, hC⟩ : TopologicalSpace.Closeds Y) : Set Y) from rfl, this]
    ext y
    simp [TopologicalSpace.Closeds.coe_finset_sup]
  obtain ⟨z, hz, hSz⟩ := (isIrreducible_iff_sUnion_isClosed.1 hS.1.1)
    (F.image (fun k : TopologicalSpace.Closeds Y => (k : Set Y)))
    (by intro z hz; simp only [Finset.mem_image] at hz; obtain ⟨k, -, rfl⟩ := hz; exact k.2)
    (hCeq ▸ hS.1.2)
  simp only [Finset.mem_image] at hz
  obtain ⟨k, hk, rfl⟩ := hz
  have hkC : (k : Set Y) ⊆ C := by
    rw [hCeq]
    exact Set.subset_sUnion_of_mem (by
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]; exact ⟨k, hk, rfl⟩)
  have : S = k := le_antisymm hSz (hS.2 ⟨hF ⟨k, hk⟩, hkC⟩ hSz)
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
  exact ⟨k, hk, this.symm⟩

/-- The source of a datum is a Noetherian space. -/
private theorem Datum.noetherianSpace (δ : Datum X sX L) :
    TopologicalSpace.NoetherianSpace δ.V := by
  haveI : IsProper δ.sV := (IsProjectiveMorphism.isProjective
    (AlgebraicGeometry.IsProjectiveVariety.isProjective (k := ℂ) (f := δ.sV))).isProper
  haveI : CompactSpace δ.V := QuasiCompact.compactSpace_of_compactSpace δ.sV
  haveI : IsNoetherian δ.V := ⟨⟩
  infer_instance

/-- The strata of `⌊B⌋` are finite in number. -/
private theorem Datum.finite_strata (δ : Datum X sX L) :
    {S : Set δ.V | MMP.Fourfold.IsSNCStratum δ.B.roundDown S}.Finite := by
  classical
  haveI := δ.noetherianSpace
  refine ((δ.B.roundDown.support.powerset.finite_toSet).biUnion fun J _ =>
    finite_maximal_irreducible_subset (⋂ E ∈ J, (E.support : Set δ.V))
      (isClosed_biInter fun E _ => E.idealSheaf.support.isClosed)).subset ?_
  rintro S ⟨J, hJ, hS⟩
  exact Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_powerset.2 hJ)) hS

/-! ### Semiampleness -/

/-- The pullback of a module generated by global sections is generated by global sections. -/
private theorem isGeneratedByGlobalSections_pullback {Y Z : Scheme.{0}} (f : Y ⟶ Z)
    {M : Z.Modules} (h : SheafOfModules.IsGeneratedByGlobalSections M) :
    SheafOfModules.IsGeneratedByGlobalSections ((Scheme.Modules.pullback f).obj M) := by
  obtain ⟨σ⟩ := h
  let p : SheafOfModules.free σ.I ⟶ (Scheme.Modules.pullback f).obj M :=
    (SheafOfModules.pullbackObjFreeIso _ σ.I).inv ≫ (Scheme.Modules.pullback f).map σ.π
  have hm : Epi ((Scheme.Modules.pullback f).map σ.π) :=
    @Functor.map_epi _ _ _ _ _
      (Functor.preservesEpimorphisms_of_adjunction (Scheme.Modules.pullbackPushforwardAdjunction f))
      _ _ σ.π σ.epi
  haveI : Epi p := @epi_comp _ _ _ _ _ _ inferInstance _ hm
  have hp : Epi ((SheafOfModules.freeHomEquiv ((Scheme.Modules.pullback f).obj M)).symm
      ((SheafOfModules.freeHomEquiv ((Scheme.Modules.pullback f).obj M)) p)) := by
    rw [Equiv.symm_apply_apply]; infer_instance
  exact ⟨⟨σ.I, ((Scheme.Modules.pullback f).obj M).freeHomEquiv p, hp⟩⟩

/-- Large powers of an ample sheaf are generated by global sections. -/
private theorem exists_isGeneratedByGlobalSections_tensorPowModule {Y : Scheme.{0}}
    [IsLocallyNoetherian Y] (M : Y.Modules) [Stacks.Ample.IsInvertibleModule Y M]
    (hM : Stacks.Ample.IsAmple Y M) :
    ∃ n₀ : ℤ, ∀ n : ℤ, n₀ ≤ n → SheafOfModules.IsGeneratedByGlobalSections
      (Stacks.Ample.tensorPowModule Y M n) := by
  haveI hinv : Stacks.Ample.IsInvertibleModule Y (Stacks.Ample.unitModule Y) := inferInstance
  haveI : (Stacks.Ample.unitModule Y).IsCoherent :=
    @Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isInvertible Y _ _ hinv
  obtain ⟨n₀, hn₀⟩ :=
    (Stacks.AmpleCharacterization.quasiSeparatedSpace_and_isGeneratedByGlobalSections_of_isAmple
      M hM).2 (Stacks.Ample.unitModule Y) (_root_.isQuasicoherent_of_isCoherent (M := _))
      (SheafOfModules.IsCoherent.isFiniteType (M := _))
  exact ⟨n₀, fun n hn => Stacks.SheafOfModules.Intrinsic.isGeneratedByGlobalSections_of_iso
    (Stacks.AmpleEventualGeneration.unitTensorIsoSelf _) (hn₀ n hn)⟩

private theorem isLocalEquationAt_zero_one (Z : Scheme.{0}) (x : Z) :
    MMP.Intersection.IsLocalEquationAt (0 : Z.CartierDivisor) x 1 :=
  ⟨⊤, trivial, 1, MMP.Intersection.isLocalEquationOn_one _, by simp⟩

private theorem isPullback_zero {Y Z : Scheme.{0}} (g : Y ⟶ Z) :
    MMP.Intersection.IsPullback g (0 : Z.CartierDivisor) 0 := by
  open MMP.Intersection in
  refine ⟨fun η _ => ?_, fun y => ⟨1, 1,
    ⟨1, isLocalEquationAt_zero_one _ _, isFraction_one_one_one _⟩,
    ?_, ?_, 1, isLocalEquationAt_zero_one _ _, ?_⟩⟩
  · simp [MMP.Intersection.cartierSupport]
  · simp
  · simp
  · simpa only [map_one] using MMP.Intersection.isFraction_one_one_one y

private theorem realization_congr {Y : Scheme.{0}} {c c' : KCartierDivisor ℚ Y}
    (e : c = c') (h : ∀ D, ∃ n : ℤ, c D = n) (h' : ∀ D, ∃ n : ℤ, c' D = n) :
    KCartierDivisor.realization c h = KCartierDivisor.realization c' h' := by
  subst e; rfl

/-- A `ℚ`-divisor `Q` on a smooth projective variety with `nQ` integral and globally generated
is semiample over every proper map `g` to a variety. -/
private theorem isRelativelySemiample_of_isGeneratedByGlobalSections {Y : Scheme.{0}}
    (sY : Y ⟶ Spec (.of ℂ)) [MMP.Mori.IsProjectiveVariety ℂ sY] (hsm : IsSmoothScheme sY)
    [IsLocallyNoetherian Y] [IsNormal Y] {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ))
    [AlgebraicGeometry.IsVariety ℂ sZ] (g : Y ⟶ Z) (hg : g ≫ sZ = sY) [IsProper g]
    (Q : QDivisor Y) (n : ℕ) (hn : 0 < n) (D' : Divisor Y)
    (hQ : ∀ P, (D'.coeff P : ℚ) = n * Q.coeff P)
    (hgg : SheafOfModules.IsGeneratedByGlobalSections D'.divisorialSheaf) :
    MMP.Fourfold.QDivisor.IsRelativelySemiample g Q := by
  classical
  obtain ⟨E, hE⟩ := (MMP.Resolution.Bridges.uniqueFactorization_and_exists_isWeilDivisorOfCartier).2
    Y (MMP.Threefold.Resolution.isRegular_of_isSmoothScheme hsm) D'
  obtain ⟨e⟩ := MMP.Intersection.IsWeilDivisorOfCartier.nonempty_sheaf_iso_divisorialSheaf hE
  haveI : IsProper sY := (IsProjectiveMorphism.isProjective
    (AlgebraicGeometry.IsProjectiveVariety.isProjective (k := ℂ) (f := sY))).isProper
  have : AlgebraicGeometry.IsVariety ℂ sY :=
    ((AlgebraicGeometry.isProjectiveVariety_iff ℂ sY).1 inferInstance).1
  have hfree : IsRelativelyFreeCartier g E :=
    MMP.Mori.isRelativelyFreeCartier_of_isGeneratedByGlobalSections_add_pullback
      (sY := sZ) (f := g) hg E (B := 0) (B' := 0)
      (isPullback_zero g) (by
        rw [add_zero]
        exact Stacks.SheafOfModules.Intrinsic.isGeneratedByGlobalSections_of_iso e.symm hgg)
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  refine ⟨Finsupp.single E ((n : ℚ)⁻¹), fun P => ?_, n, hn, ?_⟩
  · rw [Finsupp.sum_single_index (by simp),
      (MMP.Intersection.isOrderAlong_primeDivisorOrder E P).unique (hE P), hQ P]
    field_simp
  · have hc : (n : ℚ) • Finsupp.single E ((n : ℚ)⁻¹) =
        (Finsupp.single E (1 : ℤ)).mapRange (Int.cast : ℤ → ℚ) Int.cast_zero := by
      rw [Finsupp.smul_single, Finsupp.mapRange_single, smul_eq_mul, mul_inv_cancel₀ hn',
        Int.cast_one]
    refine ⟨fun D => ⟨(Finsupp.single E (1 : ℤ)) D, by rw [hc]; rfl⟩, ?_⟩
    rw [realization_congr hc _ (fun D => ⟨(Finsupp.single E (1 : ℤ)) D, rfl⟩),
      KCartierDivisor.realization_eq_sum, Finsupp.sum_single_index (by simp), one_smul]
    exact hfree

/-! ### The geometric inputs -/

variable [MMP.Mori.IsProjectiveVariety ℂ sX]
  [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]

/-- The image of `f` has finite dimension. -/
private theorem Datum.exists_dim_le (δ : Datum X sX L) : ∃ d : ℕ, δ.dim ≤ d := by
  letI := MMP.Mori.functionFieldAlgebra sX
  haveI := MMP.Mori.essFiniteType_functionField (sX := sX)
  refine ⟨(Algebra.trdeg ℂ X.functionField).toNat,
    (topologicalKrullDim_subspace_le X _).trans ?_⟩
  rw [← MMP.Mori.toENat_trdeg_functionField (sX := sX),
    ← Cardinal.cast_toNat_of_lt_aleph0 (trdeg_lt_aleph0 (K := ℂ) (L := X.functionField))]
  simp

/-- **Grothendieck vanishing.** `R^q f_* 𝒪_V(M)` is a coherent sheaf supported on the image of
`f`, so its cohomology vanishes above the dimension of that image. -/
private theorem Datum.isZero_coh_of_dim_lt (δ : Datum X sX L) (p q : ℕ) (hp0 : 0 < p)
    (hp : δ.dim < p) : IsZero (δ.coh p q) := by
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  haveI : IsProper δ.f := δ.hfp.isProper
  haveI : CompactSpace δ.V := QuasiCompact.compactSpace_of_compactSpace δ.sV
  haveI : δ.M.divisorialSheaf.IsCoherent :=
    @Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isInvertible δ.V _ _
      δ.hM.isInvertibleModule_divisorialSheaf
  set F := ((Scheme.Modules.pushforward δ.f).rightDerived q).obj δ.M.divisorialSheaf
  haveI : F.IsCoherent :=
    Stacks.AlgebraicGeometry.RelativeSerreVanishing.isCoherent_of_iso
      ((@Stacks.DerivedIndexing.rightDerivedIso _ _ _ _ _ _ _ (Scheme.Modules.pushforward δ.f) _
        (HasDerivedCategory.standard _) (HasDerivedCategory.standard _) q).app _).symm
      (ProperCoherenceWitness.higherDirectImageIsCoherent δ.V X δ.f inferInstance inferInstance _
        inferInstance q)
  -- `R^q f_* 𝒪_V(M)` is supported on the closure of the image of `f`
  have hsupp : SheafOfModules.supp F ⊆ closure (Set.range δ.f.base) := by
    intro x hx
    by_contra hxc
    let U : X.Opens := ⟨(closure (Set.range δ.f.base))ᶜ, isClosed_closure.isOpen_compl⟩
    refine Stacks.AlgebraicGeometry.ConfinedDevissage.notMem_supp_of_supp_restrict_eq_empty F U
      ?_ x hxc hx
    apply SheafOfModules.supp_eq_empty_of_isZero
    have e := (AlgebraicGeometry.ProjectiveCoherentImage.higherDirectImageRestrictIsoScheme δ.f U
      q).app δ.M.divisorialSheaf
    refine IsZero.of_iso ?_ e.symm
    haveI : IsEmpty (δ.f ⁻¹ᵁ U) := ⟨fun ⟨y, hy⟩ => hy (subset_closure ⟨y, rfl⟩)⟩
    exact Functor.map_isZero ((Scheme.Modules.pushforward (δ.f ∣_ U)).rightDerived q)
      (Stacks.AlgebraicGeometry.DevissageNoetherian.isZero_of_supp_eq_empty _
        (Set.eq_empty_of_isEmpty _))
  -- Grothendieck vanishing
  obtain ⟨d, hdV, hdp⟩ : ∃ d : ℕ, δ.dim ≤ d ∧ d < p := by
    induction hx : δ.dim using WithBot.recBotCoe with
    | bot => exact ⟨0, bot_le, hp0⟩
    | coe e =>
      rw [hx] at hp
      induction e using ENat.recTopCoe with
      | top => exact absurd hp (by simp)
      | coe k => exact ⟨k, le_rfl, by exact_mod_cast hp⟩
  have hF : topologicalKrullDim (SheafOfModules.supp F) ≤ d :=
    ((Topology.IsInducing.subtypeVal.of_comp_iff (f := Set.inclusion hsupp)).1
      Topology.IsInducing.subtypeVal).topologicalKrullDim_le.trans hdV
  have h := AlgebraicGeometry.isZero_cohomologyOverField_of_topologicalKrullDim_supp_le ℂ sX F
    hF hdp
  have h1 := ModuleCat.subsingleton_of_isZero h
  exact @ModuleCat.isZero_of_subsingleton _ _ _ h1

/-! ### Effective divisors from sections of powers of the ample sheaf -/

section Sections

open Stacks.Ample RingedSpaceModuleAdjunction

/-- The powers of a section of `L^n` are sections of `L^{n(k+1)}` with the same nonvanishing
locus. -/
private theorem exists_powNonvanishingOpen_eq_self {Y : Scheme.{0}} (M : Y.Modules)
    [IsInvertibleModule Y M] (n : ℕ) (s : Γ(tensorPowModule Y M (n : ℤ), ⊤)) (k : ℕ) :
    ∀ m : ℕ, m = n * (k + 1) → ∃ u : Γ(tensorPowModule Y M (m : ℤ), ⊤),
      Stacks.AmpleTheory.powNonvanishingOpen Y M m u =
        Stacks.AmpleTheory.powNonvanishingOpen Y M n s := by
  induction k with
  | zero =>
    intro m hm
    obtain rfl : m = n := by rw [hm]; ring
    exact ⟨s, rfl⟩
  | succ k ih =>
    intro m hm
    obtain ⟨u, hu⟩ := ih (n * (k + 1)) rfl
    obtain ⟨w, hw⟩ := Stacks.SectionExtension.exists_powNonvanishingOpen_eq_inf M n
      (n * (k + 1)) s u
    obtain rfl : m = n * (k + 1) + n := by rw [hm]; ring
    exact ⟨w, by rw [hw, hu, inf_idem]⟩

/-- **An effective divisor in the class of a large power of the ample sheaf.** For every `d₀`
and every finite set `E ⊆ X` there are `d ≥ d₀` and an effective Cartier divisor `A` on `V` with
`𝒪_V(A) ≅ f^*(L^d)` whose support misses `f⁻¹(E)`. -/
private theorem Datum.exists_divisor (hL : IsAmple X L) (δ : Datum X sX L) (d₀ : ℕ)
    {E : Set X} (hE : E.Finite) :
    ∃ d : ℕ, d₀ ≤ d ∧ ∃ A : Divisor δ.V, 0 ≤ A ∧ A.IsCartier ∧
      Nonempty (A.divisorialSheaf ≅
        (Scheme.Modules.pullback δ.f).obj (tensorPowModule X L (d : ℤ))) ∧
      ∀ x : δ.V, δ.f.base x ∈ E → x ∉ A.supp := by
  haveI : IsInvertibleModule X L := ‹_›
  haveI : IsIntegral δ.V := δ.isIntegral
  haveI : CompactSpace δ.V := QuasiCompact.compactSpace_of_compactSpace δ.sV
  obtain ⟨n, hn, s, -, hsE, -⟩ :=
    Stacks.AmpleFiniteAffineNonvanishing.exists_affine_nonvanishingOpen_containing_finite L hL
      (hE.insert (δ.f.base (genericPoint δ.V))) ⊤ (by simp)
  obtain ⟨u, hu⟩ := exists_powNonvanishingOpen_eq_self L n s d₀ _ rfl
  refine ⟨n * (d₀ + 1), by nlinarith, ?_⟩
  set M' := (Scheme.Modules.pullback δ.f).obj (tensorPowModule X L ((n * (d₀ + 1) : ℕ) : ℤ))
  have : SheafOfModules.IsInvertible δ.V.sheaf.obj δ.V.ringCatSheaf.property M' :=
    InvertibleSheafGeneral.isInvertible_of_isInvertibleModule _
  let σ : Γ(M', ⊤) := AlgebraicGeometry.pullbackGlobalSections δ.f _ u
  have hσ : ∀ x : δ.V, x ∈ nonvanishingLocus M' σ ↔
      δ.f.base x ∈ (Stacks.AmpleTheory.powNonvanishingOpen X L n s : Set X) := fun x => by
    rw [MMP.Fourfold.mem_nonvanishingLocus_pullbackGlobalSections_iff, ← hu,
      Stacks.AmpleTheory.coe_powNonvanishingOpen]
  have hx₀ : genericPoint δ.V ∈ nonvanishingLocus M' σ :=
    (hσ _).2 (hsE (Set.mem_insert _ _))
  have hne0 : σ ≠ 0 := by
    intro h
    rw [h, mem_nonvanishingLocus_iff] at hx₀
    exact hx₀ (by simp)
  have hevaltop : (Stacks.SheafOfModules.sectionsOfTop M' σ).eval (op ⊤) = σ :=
    Stacks.SheafOfModules.sectionsOfTop_eval_top _ σ
  have hne0' : (Stacks.SheafOfModules.sectionsOfTop M' σ).eval (op ⊤) ≠ 0 := by
    rwa [hevaltop]
  have hreg : IsRegularSection δ.V.sheaf.obj δ.V.ringCatSheaf.property
      (Stacks.SheafOfModules.sectionsOfTop M' σ) :=
    isRegularSection_of_eval_top_ne_zero _ _ hne0'
  have hZc : Stacks.Divisors.IsEffectiveCartierDivisor
      (zeroScheme δ.V M' ((Stacks.SheafOfModules.sectionsOfTop M' σ).eval (op ⊤))) :=
    (isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection δ.V _ _).2 hreg
  have hcompl := nonvanishingLocus_eq_compl_supportSet_zeroScheme M' _ hne0'
  have hnv : nonvanishingLocus M' σ =
      (zeroScheme δ.V M' ((Stacks.SheafOfModules.sectionsOfTop M' σ).eval (op ⊤))).supportSetᶜ := by
    rw [← hcompl]
    conv_lhs => rw [← hevaltop]
    rw [← Stacks.AmplePredicateBridge.coe_nonvanishingOpen_eval δ.V _
        (Stacks.SheafOfModules.sectionsOfTop M' σ)]
    rfl
  obtain ⟨A, hA0, hAc, ⟨eA⟩, hAsupp⟩ :=
    MMP.Threefold.Resolution.exists_divisor_of_isEffectiveCartierDivisor _ hZc
  refine ⟨A, hA0, hAc, ⟨eA ≪≫ (invertibleSheafIsoZeroSchemeOfIsRegularSection _ _ hreg).symm⟩,
    fun x hx hxA => ?_⟩
  have hxσ : x ∈ nonvanishingLocus M' σ := (hσ x).2 (hsE (Set.mem_insert_of_mem _ hx))
  rw [hnv] at hxσ
  obtain ⟨P, hP, hxP⟩ := DivisorWithCoeffs.mem_supp_iff.1 hxA
  have hPpos : 0 < A P := lt_of_le_of_ne (hA0 P) (Ne.symm hP)
  exact hxσ ((MMP.Resolution.Aux.genericPoint_specializes_of_mem_support P hxP).mem_closed
    (zeroScheme δ.V M' ((Stacks.SheafOfModules.sectionsOfTop M' σ).eval (op ⊤))).support.isClosed
    (hAsupp P hPpos))

end Sections

/-- **Serre vanishing for the twisted direct images.** For every `Q` there is `d₀` such that for
`d ≥ d₀` the direct images `R^q f_*(𝒪_V(M) ⊗ f^*L^d)`, `q ≤ Q`, have no positive cohomology. -/
private theorem Datum.exists_serre (hL : Stacks.Ample.IsAmple X L) (δ : Datum X sX L) (Q : ℕ) :
    ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ q ≤ Q, ∀ p, 0 < p →
      IsZero (((sections X).rightDerived p).obj
        (((Scheme.Modules.pushforward δ.f).rightDerived q).obj
          (Stacks.RelativeVeryAmple.tensorModules δ.V δ.M.divisorialSheaf
            ((Scheme.Modules.pullback δ.f).obj
              (Stacks.Ample.tensorPowModule X L (d : ℤ)))))) := by
  haveI : Stacks.Ample.IsInvertibleModule X L := ‹_›
  haveI : IsProper sX := (IsProjectiveMorphism.isProjective
    (AlgebraicGeometry.IsProjectiveVariety.isProjective (k := ℂ) (f := sX))).isProper
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  haveI : IsProper δ.f := δ.hfp.isProper
  haveI : CompactSpace δ.V := QuasiCompact.compactSpace_of_compactSpace δ.sV
  haveI : δ.M.divisorialSheaf.IsCoherent :=
    @Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isInvertible δ.V _ _
      δ.hM.isInvertibleModule_divisorialSheaf
  have hcoh : ∀ q, (((Scheme.Modules.pushforward δ.f).rightDerived q).obj
      δ.M.divisorialSheaf).IsCoherent := fun q =>
    Stacks.AlgebraicGeometry.RelativeSerreVanishing.isCoherent_of_iso
      ((@Stacks.DerivedIndexing.rightDerivedIso _ _ _ _ _ _ _ (Scheme.Modules.pushforward δ.f) _
        (HasDerivedCategory.standard _) (HasDerivedCategory.standard _) q).app _).symm
      (ProperCoherenceWitness.higherDirectImageIsCoherent δ.V X δ.f inferInstance inferInstance _
        inferInstance q)
  have hS : ∀ q, ∃ d₀ : ℕ, ∀ d p : ℕ, d₀ ≤ d → 0 < p →
      IsZero (Hgroup X.ringCatSheaf ⊤ p (Stacks.RelativeVeryAmple.tensorModules X
        (((Scheme.Modules.pushforward δ.f).rightDerived q).obj δ.M.divisorialSheaf)
        (Stacks.Ample.tensorPowModule X L (d : ℤ)))) := fun q =>
    haveI := hcoh q
    Stacks.AlgebraicGeometry.ProperAmpleCohomology.exists_isZero_Hgroup_tensorPowTwist sX _ L hL
  choose e he using hS
  refine ⟨∑ q ∈ Finset.range (Q + 1), e q, fun d hd q hq p hp => ?_⟩
  have hle : e q ≤ d := le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hq))) hd
  have h1 := (Stacks.Cohomology.CechAcyclic.isZero_rightDerived_evaluation_iff_isZero_Hgroup
    _ _ p _).2 (he q d p hle hp)
  haveI : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (Stacks.Ample.tensorPowModule X L (d : ℤ)) :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).2 inferInstance
  open scoped Stacks.SmallDerivedModel in
  let e₁ := (Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward δ.f) q)
  open scoped Stacks.SmallDerivedModel in
  refine h1.of_iso (((sections X).rightDerived p).mapIso
    (e₁.app _ ≪≫ Stacks.ProjectionFormula.higherDirectImageProjectionFormulaIso δ.f
      (Stacks.Ample.tensorPowModule X L (d : ℤ)) δ.M.divisorialSheaf q ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0} X.toRingedSpace.sheaf).mapIso
        (e₁.app _).symm).app _))

/-- The strata of `⌊B⌋` are finitely many, so finitely many points of `X` meet all their
images. -/
private theorem Datum.exists_finite_points (δ : Datum X sX L) :
    ∃ E : Set X, E.Finite ∧ ∀ S : Set δ.V, MMP.Fourfold.IsSNCStratum δ.B.roundDown S →
      ∃ x ∈ S, δ.f.base x ∈ E := by
  classical
  have hne : ∀ S ∈ {S : Set δ.V | MMP.Fourfold.IsSNCStratum δ.B.roundDown S}, S.Nonempty :=
    fun S ⟨_, _, hS⟩ => hS.1.1.nonempty
  choose! x hx using hne
  refine ⟨(fun S => δ.f.base (x S)) '' {S | MMP.Fourfold.IsSNCStratum δ.B.roundDown S},
    δ.finite_strata.image _, fun S hS => ⟨x S, hx S hS, S, hS, rfl⟩⟩

/-- **The twisted adjoint sheaf.** For an effective Cartier `A` with `𝒪_V(A) ≅ f^*L^d`,
`𝒪_V(M + A) ≅ 𝒪_V(M) ⊗ f^*L^d`. -/
private noncomputable def Datum.twistIso (δ : Datum X sX L) {A : Divisor δ.V} (hA : A.IsCartier)
    {d : ℕ} (eA : A.divisorialSheaf ≅
      (Scheme.Modules.pullback δ.f).obj (Stacks.Ample.tensorPowModule X L (d : ℤ))) :
    (δ.M + A).divisorialSheaf ≅
      Stacks.RelativeVeryAmple.tensorModules δ.V δ.M.divisorialSheaf
        ((Scheme.Modules.pullback δ.f).obj (Stacks.Ample.tensorPowModule X L (d : ℤ))) :=
  haveI : CompactSpace δ.V := QuasiCompact.compactSpace_of_compactSpace δ.sV
  (δ.hM.divisorialSheafTensorIso hA).symm ≪≫
    Stacks.RelativeVeryAmple.tensorModulesMapIso δ.V (Iso.refl _) eA

/-- The positive tensor powers of the divisorial sheaf of a Cartier divisor `G` are the
divisorial sheaves of the multiples of `G`. -/
private theorem nonempty_tensorPowModule_iso_divisorialSheaf {Y : Scheme.{0}}
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    (G : Divisor Y) (hG : G.IsCartier) [Stacks.Ample.IsInvertibleModule Y G.divisorialSheaf]
    (n : ℕ) :
    Nonempty (Stacks.Ample.tensorPowModule Y G.divisorialSheaf ((n + 1 : ℕ) : ℤ) ≅
      (((n + 1 : ℕ) : ℤ) • G).divisorialSheaf) := by
  induction n with
  | zero => exact ⟨Stacks.RelativeVeryAmple.tensorPowModuleCongr Y _ (by norm_num) ≪≫
      Stacks.Ample.tensorPowModuleOneIso Y _ ≪≫
      eqToIso (by rw [Nat.cast_one, one_smul])⟩
  | succ n ih =>
    obtain ⟨e⟩ := ih
    exact ⟨Stacks.RelativeVeryAmple.tensorPowModuleCongr Y _ (by push_cast; ring) ≪≫
      (Stacks.Ample.tensorPowModuleAddIso Y _ ((n + 1 : ℕ) : ℤ) 1).symm ≪≫
      Stacks.RelativeVeryAmple.tensorModulesMapIso Y e (Stacks.Ample.tensorPowModuleOneIso Y _) ≪≫
      (hG.zsmul _).divisorialSheafTensorIso hG ≪≫
      eqToIso (by congr 1; push_cast; simp only [add_smul, one_smul])⟩

/-- `𝒪_V(dD) ≅ f^*(L^d)` for the divisor `D = m(M - (K + B))` of the datum. -/
private theorem Datum.nonempty_divisorialSheaf_nsmul_iso (δ : Datum X sX L) {D : Divisor δ.V}
    (eD : D.divisorialSheaf ≅ (Scheme.Modules.pullback δ.f).obj L) (d : ℕ) (hd : 0 < d) :
    Nonempty ((d • D).divisorialSheaf ≅
      (Scheme.Modules.pullback δ.f).obj (Stacks.Ample.tensorPowModule X L (d : ℤ))) := by
  haveI : CompactSpace δ.V := QuasiCompact.compactSpace_of_compactSpace δ.sV
  have hcart := δ.isCartier
  haveI := (hcart D).isInvertibleModule_divisorialSheaf
  haveI : Stacks.Ample.IsInvertibleModule X L := ‹_›
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  obtain ⟨eP⟩ := nonempty_tensorPowModule_iso_divisorialSheaf D (hcart D) n
  exact ⟨eqToIso (by rw [natCast_zsmul]) ≪≫ eP.symm ≪≫
    Stacks.RelativeVeryAmple.tensorPowModuleIsoOfIso δ.V _ _ eD (n + 1) ≪≫
    (Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso δ.f L (n + 1)).symm⟩

/-- **The adjoint difference is semiample.** `M - (K + B) ∼_ℚ f^*H` with `H` ample, so a multiple
of it has globally generated sheaf, and it is semiample over every proper map `g` from `V` to a
variety. -/
private theorem Datum.isRelativelySemiample_adjoint (hL : Stacks.Ample.IsAmple X L)
    (δ : Datum X sX L) {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ))
    [AlgebraicGeometry.IsVariety ℂ sZ] (g : δ.V ⟶ Z) (hg : g ≫ sZ = δ.sV) [IsProper g] :
    MMP.Fourfold.QDivisor.IsRelativelySemiample g
      (Divisor.toQDivisor δ.M - (Divisor.toQDivisor δ.K + δ.B)) := by
  haveI : Stacks.Ample.IsInvertibleModule X L := ‹_›
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  obtain ⟨n₀, hn₀⟩ := exists_isGeneratedByGlobalSections_tensorPowModule L hL
  have hgg := hn₀ ((n₀.toNat + 1 : ℕ) : ℤ) (by omega)
  obtain ⟨m, hm, D, hD, ⟨eD⟩⟩ := δ.hlin
  obtain ⟨e⟩ := δ.nonempty_divisorialSheaf_nsmul_iso eD (n₀.toNat + 1) (Nat.succ_pos _)
  refine isRelativelySemiample_of_isGeneratedByGlobalSections δ.sV δ.hVsm sZ g hg _
    ((n₀.toNat + 1) * m) (by positivity) ((n₀.toNat + 1) • D) (fun P => ?_)
    (Stacks.SheafOfModules.Intrinsic.isGeneratedByGlobalSections_of_iso e.symm
      (isGeneratedByGlobalSections_pullback δ.f hgg))
  have h1 := congrArg (fun Q : QDivisor δ.V => Q.coeff P) hD
  have h2 := Divisor.coeff_toQDivisor D P
  simp only [DivisorWithCoeffs.coeff_apply, Finsupp.smul_apply, smul_eq_mul] at h1 h2 ⊢
  rw [nsmul_eq_mul]
  push_cast
  rw [← h2, h1]
  simp only [Finsupp.coe_sub, Finsupp.coe_add, Pi.sub_apply, Pi.add_apply]
  ring

open scoped Stacks.SmallDerivedModel in
/-- Injectivity on the cohomology of `V`, read on the cohomology of the direct images. -/
private theorem mono_rightDerived_pushforward_comp_sections_of_injective {V X : Scheme.{0}}
    (sV : V ⟶ Spec (.of ℂ)) (f : V ⟶ X) (k : ℕ) {G G' : V.Modules} (g : G ⟶ G')
    (h : Function.Injective ((DerivedCategory.homologyFunctor (ModuleCat.{0} ℂ) (k : ℤ)).map
      ((derivedGlobalSectionsOver sV).map
        ((DerivedCategory.singleFunctor V.Modules 0).map g))).hom) :
    Mono (((Scheme.Modules.pushforward f ⋙ sections X).rightDerived k).map g) := by
  -- injectivity on `H^k(V, -)`
  have e1 := Stacks.Duality.cohomologyOverFieldFunctorIsoDerivedCohomology ℂ sV k
  have h1 : Function.Injective ((cohomologyOverFieldFunctor ℂ sV k).map g).hom := by
    have hn := e1.hom.naturality g
    have : (cohomologyOverFieldFunctor ℂ sV k).map g =
        ((cohomologyOverFieldFunctor ℂ sV k).map g ≫ e1.hom.app G') ≫ e1.inv.app G' := by
      rw [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
    rw [this, hn]
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp]
    exact ((ModuleCat.mono_iff_injective _).1 (IsIso.mono_of_iso _)).comp
      (h.comp ((ModuleCat.mono_iff_injective _).1 (IsIso.mono_of_iso _)))
  have h2 : Function.Injective (((sections V).rightDerived k).map g).hom := h1
  -- both cohomologies, read as abelian groups
  let F₁ := sections V ⋙ forget₂ (ModuleCat (V.ringCatSheaf.obj.obj (op ⊤))) AddCommGrpCat
  let F₂ := (Scheme.Modules.pushforward f ⋙ sections X) ⋙
    forget₂ (ModuleCat (X.ringCatSheaf.obj.obj (op ⊤))) AddCommGrpCat
  let e : F₁ ≅ F₂ := NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)
  have m1 : Mono ((forget₂ (ModuleCat (V.ringCatSheaf.obj.obj (op ⊤))) AddCommGrpCat).map
      (((sections V).rightDerived k).map g)) := by
    haveI : Mono (((sections V).rightDerived k).map g) := (ModuleCat.mono_iff_injective _).2 h2
    infer_instance
  have m2 : Mono ((F₁.rightDerived k).map g) := by
    have hn := (Functor.rightDerivedCompIso (sections V)
      (forget₂ (ModuleCat (V.ringCatSheaf.obj.obj (op ⊤))) AddCommGrpCat) k).hom.naturality g
    haveI : Mono (((sections V).rightDerived k ⋙
        forget₂ (ModuleCat (V.ringCatSheaf.obj.obj (op ⊤))) AddCommGrpCat).map g) := m1
    have : Mono ((F₁.rightDerived k).map g ≫ (Functor.rightDerivedCompIso (sections V)
        (forget₂ (ModuleCat (V.ringCatSheaf.obj.obj (op ⊤))) AddCommGrpCat) k).hom.app G') := by
      rw [hn]; exact mono_comp' (IsIso.mono_of_iso _) ‹_›
    exact mono_of_mono _ ((Functor.rightDerivedCompIso (sections V)
        (forget₂ (ModuleCat (V.ringCatSheaf.obj.obj (op ⊤))) AddCommGrpCat) k).hom.app G')
  have m3 : Mono ((F₂.rightDerived k).map g) := by
    have hn := (NatTrans.rightDerived e.hom k).naturality g
    have hiso : ∀ Y, IsIso ((NatTrans.rightDerived e.hom k).app Y) := fun Y =>
      ⟨(NatTrans.rightDerived e.inv k).app Y, by
        rw [← NatTrans.comp_app, ← NatTrans.rightDerived_comp, e.hom_inv_id,
          NatTrans.rightDerived_id, NatTrans.id_app],
        by rw [← NatTrans.comp_app, ← NatTrans.rightDerived_comp, e.inv_hom_id,
          NatTrans.rightDerived_id, NatTrans.id_app]⟩
    have heq : (F₂.rightDerived k).map g = inv ((NatTrans.rightDerived e.hom k).app G) ≫
        (F₁.rightDerived k).map g ≫ (NatTrans.rightDerived e.hom k).app G' := by
      rw [IsIso.eq_inv_comp, hn]
    rw [heq]
    exact mono_comp' (IsIso.mono_of_iso _) (mono_comp' m2 (IsIso.mono_of_iso _))
  have m4 : Mono ((forget₂ (ModuleCat (X.ringCatSheaf.obj.obj (op ⊤))) AddCommGrpCat).map
      (((Scheme.Modules.pushforward f ⋙ sections X).rightDerived k).map g)) := by
    have hn := (Functor.rightDerivedCompIso (Scheme.Modules.pushforward f ⋙ sections X)
      (forget₂ (ModuleCat (X.ringCatSheaf.obj.obj (op ⊤))) AddCommGrpCat) k).inv.naturality g
    have : Mono (((Functor.rightDerivedCompIso (Scheme.Modules.pushforward f ⋙ sections X)
        (forget₂ (ModuleCat (X.ringCatSheaf.obj.obj (op ⊤))) AddCommGrpCat) k).inv.app G) ≫
          (F₂.rightDerived k).map g) := mono_comp' (IsIso.mono_of_iso _) m3
    rw [← hn] at this
    exact @mono_of_mono _ _ _ _ _ _ _ this
  exact Functor.mono_of_mono_map
    (forget₂ (ModuleCat (X.ringCatSheaf.obj.obj (op ⊤))) AddCommGrpCat) m4

/-- **Injectivity from the semiample adjoint difference.** If `A ≥ 0` is Cartier with
`𝒪_V(A) ≅ f^*L^d`, `d > 0`, and no stratum of `⌊B⌋` lies in `Supp A`, then
`H^k(V, 𝒪_V(M)) ⟶ H^k(V, 𝒪_V(M + A))` is injective. -/
private theorem Datum.mono_of_noStratum (hL : Stacks.Ample.IsAmple X L) (δ : Datum X sX L)
    {A : Divisor δ.V} (hA0 : 0 ≤ A) (hA : A.IsCartier) {d : ℕ} (hd : 0 < d)
    (eA : A.divisorialSheaf ≅
      (Scheme.Modules.pullback δ.f).obj (Stacks.Ample.tensorPowModule X L (d : ℤ)))
    (hAS : MMP.Fourfold.ContainsNoStratum δ.B.roundDown (A.supp : Set δ.V)) (k : ℕ) :
    Mono (((Scheme.Modules.pushforward δ.f ⋙ sections X).rightDerived k).map
      (Divisor.divisorialSheafInclusion (le_add_of_nonneg_right hA0 : δ.M ≤ δ.M + A))) := by
  haveI : CompactSpace δ.V := QuasiCompact.compactSpace_of_compactSpace δ.sV
  obtain ⟨m, hm, D, hD, ⟨eD⟩⟩ := δ.hlin
  obtain ⟨eDd⟩ := δ.nonempty_divisorialSheaf_nsmul_iso eD d hd
  obtain ⟨φ, hφ⟩ := MMP.Flips.linearlyEquivalent_of_divisorialSheaf_iso (eDd ≪≫ eA.symm)
  set H := Divisor.toQDivisor δ.M - (Divisor.toQDivisor δ.K + δ.B)
  have hinj := MMP.Mori.injective_derivedCohomologyOverField_map_divisorialSheafInclusion_of_semiample
    δ.sV δ.hVsm δ.hK δ.B δ.hB δ.hB0 δ.hB1 H
    (haveI : AlgebraicGeometry.IsVariety ℂ (𝟙 (Spec (.of ℂ))) := ⟨⟩
     haveI : IsProper δ.sV := (IsProjectiveMorphism.isProjective
       (AlgebraicGeometry.IsProjectiveVariety.isProjective (k := ℂ) (f := δ.sV))).isProper
     δ.isRelativelySemiample_adjoint hL _ δ.sV (Category.comp_id _)) δ.M
    (by rw [show Divisor.toQDivisor δ.K + δ.B + H = Divisor.toQDivisor δ.M by
      simp only [H]; abel]) A hA0 0 le_rfl
    (t := (d * m : ℚ)) (by positivity) ?_ hAS ?_ k
  · exact mono_rightDerived_pushforward_comp_sections_of_injective δ.sV δ.f k _ hinj
  · refine ⟨1, one_pos, φ, ?_⟩
    rw [Nat.cast_one, one_smul, add_zero, ← hφ, map_sub, map_nsmul, hD,
      ← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
  · intro S hS hSsub
    obtain ⟨_, _, hS⟩ := hS
    obtain ⟨x, hx⟩ := hS.1.1.nonempty
    have h0 := hSsub hx
    simp [DivisorWithCoeffs.supp] at h0

/-- **The twist for the first column.** For every `Q` there is an effective divisor `A` on `V`
such that the direct images `R^q f_* 𝒪_V(M + A)`, `q ≤ Q`, have no positive cohomology and
`H^k(V, 𝒪_V(M)) ⟶ H^k(V, 𝒪_V(M + A))` is injective for every `k`. -/
private theorem Datum.exists_twist (hL : Stacks.Ample.IsAmple X L) (δ : Datum X sX L) (Q : ℕ) :
    ∃ (A : Divisor δ.V) (hA : 0 ≤ A),
      (∀ q ≤ Q, ∀ p, 0 < p → IsZero (((sections X).rightDerived p).obj
        (((Scheme.Modules.pushforward δ.f).rightDerived q).obj (δ.M + A).divisorialSheaf))) ∧
      ∀ k, Mono (((Scheme.Modules.pushforward δ.f ⋙ sections X).rightDerived k).map
        (Divisor.divisorialSheafInclusion (le_add_of_nonneg_right hA : δ.M ≤ δ.M + A))) := by
  obtain ⟨d₀, hd₀⟩ := δ.exists_serre hL Q
  obtain ⟨E, hE, hES⟩ := δ.exists_finite_points
  obtain ⟨d, hd, A, hA0, hAc, ⟨eA⟩, hAE⟩ := δ.exists_divisor hL (d₀ + 1) hE
  refine ⟨A, hA0, fun q hq p hp => (hd₀ d (by omega) q hq p hp).of_iso
    (((sections X).rightDerived p).mapIso
      (((Scheme.Modules.pushforward δ.f).rightDerived q).mapIso (δ.twistIso hAc eA))),
    δ.mono_of_noStratum hL hA0 hAc (by omega) eA fun S hS hSA => ?_⟩
  obtain ⟨x, hxS, hxE⟩ := hES S hS
  exact hAE x hxE (hSA hxS)

/-! ### A chain of specializations in the image -/

/-- Three points `p ⤳ q ⤳ r` of a subset `R` of a `T₀` space, with `p ≠ q ≠ r`, give a chain
of irreducible closed subsets of `R` of length two. -/
private theorem two_le_topologicalKrullDim_of_specializes {Y : Type*} [TopologicalSpace Y]
    [T0Space Y] {R : Set Y} {p q r : Y} (hp : p ∈ R) (hq : q ∈ R) (hr : r ∈ R) (hpq : p ⤳ q)
    (hqr : q ⤳ r) (hpq' : p ≠ q) (hqr' : q ≠ r) : 2 ≤ topologicalKrullDim R := by
  let p' : R := ⟨p, hp⟩
  let q' : R := ⟨q, hq⟩
  let r' : R := ⟨r, hr⟩
  have hpq₁ : p' ⤳ q' := (Topology.IsInducing.subtypeVal.specializes_iff (x := p') (y := q')).1 hpq
  have hqr₁ : q' ⤳ r' := (Topology.IsInducing.subtypeVal.specializes_iff (x := q') (y := r')).1 hqr
  let Z : R → TopologicalSpace.IrreducibleCloseds R := fun x =>
    ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hlt : ∀ {x y : R}, x ⤳ y → x ≠ y → Z y < Z x := fun {x y} hxy hne => by
    refine lt_of_le_of_ne (specializes_iff_closure_subset.1 hxy) fun h => hne ?_
    have hyx : y ⤳ x := specializes_iff_closure_subset.2
      (congrArg (fun W : TopologicalSpace.IrreducibleCloseds R => (W : Set R)) h).ge
    exact (hxy.antisymm hyx).eq
  have h1 : Z r' < Z q' := hlt hqr₁ fun h => hqr' (congrArg Subtype.val h)
  have h2 : Z q' < Z p' := hlt hpq₁ fun h => hpq' (congrArg Subtype.val h)
  let c : LTSeries (TopologicalSpace.IrreducibleCloseds R) :=
    ⟨2, ![Z r', Z q', Z p'], fun i => by fin_cases i <;> simpa⟩
  exact Order.LTSeries.length_le_krullDim c

/-- If the image of `f` has dimension at least two, there are `y₂ ⤳ y₁ ⤳ y₀` in `V` whose images
are distinct. -/
private theorem Datum.exists_chain (δ : Datum X sX L) (hd : 2 ≤ δ.dim) :
    ∃ y₂ y₁ y₀ : δ.V, y₂ ⤳ y₁ ∧ y₁ ⤳ y₀ ∧ δ.f.base y₂ ≠ δ.f.base y₁ ∧
      δ.f.base y₁ ≠ δ.f.base y₀ := by
  haveI : IsProper δ.f := δ.hfp.isProper
  set C := closure (Set.range δ.f.base) with hC
  have hCc : IsClosed C := isClosed_closure
  have hCr : C = Set.range δ.f.base := δ.f.isClosedMap.isClosed_range.closure_eq
  obtain ⟨c, hc⟩ := (Order.le_krullDim_iff (α := TopologicalSpace.IrreducibleCloseds C)
    (n := 2)).1 hd
  rcases c with ⟨len, cf, cstep⟩
  change len = 2 at hc
  subst hc
  let c : LTSeries (TopologicalSpace.IrreducibleCloseds C) := ⟨2, cf, cstep⟩
  let W : Fin (c.length + 1) → Set X := fun i => Subtype.val '' (c i : Set C)
  have hWi : ∀ i, IsIrreducible (W i) := fun i =>
    (c i).isIrreducible.image _ continuous_subtype_val.continuousOn
  have hWc : ∀ i, IsClosed (W i) := fun i =>
    hCc.isClosedEmbedding_subtypeVal.isClosedMap _ (c i).isClosed
  have hWlt : ∀ i j, c i < c j → W i ⊂ W j := fun i j h =>
    Function.Injective.image_strictMono Subtype.val_injective
      (show (c i : Set C) ⊂ (c j : Set C) from h)
  let e : Fin (c.length + 1) → X := fun i => (hWi i).genericPoint
  have he : ∀ i, closure {e i} = W i := fun i => by
    have := (hWi i).isGenericPoint_genericPoint_closure
    rw [(hWc i).closure_eq] at this
    exact this
  have hspec : ∀ i j, c i < c j → e j ⤳ e i ∧ e j ≠ e i := fun i j h => by
    refine ⟨specializes_iff_closure_subset.2 (by rw [he, he]; exact (hWlt i j h).subset),
      fun heq => (hWlt i j h).ne ?_⟩
    rw [← he, ← he, heq]
  have hmem : ∀ i, e i ∈ Set.range δ.f.base := fun i => by
    rw [← hCr]
    have : e i ∈ W i := by rw [← he]; exact subset_closure rfl
    obtain ⟨z, -, hz⟩ := this
    rw [← hz]; exact z.2
  have h01 : c 0 < c 1 := c.strictMono (show (0 : Fin 3) < 1 by decide)
  have h12 : c 1 < c 2 := c.strictMono (show (1 : Fin 3) < 2 by decide)
  obtain ⟨y₂, hy₂⟩ := hmem 2
  have hsm : SpecializingMap δ.f.base := δ.f.isClosedMap.specializingMap
  obtain ⟨y₁, hy₂₁, hy₁⟩ := hsm (hy₂ ▸ (hspec 1 2 h12).1)
  obtain ⟨y₀, hy₁₀, hy₀⟩ := hsm (hy₁ ▸ (hspec 0 1 h01).1)
  refine ⟨y₂, y₁, y₀, hy₂₁, hy₁₀, ?_, ?_⟩
  · rw [hy₂, hy₁]; exact (hspec 1 2 h12).2
  · rw [hy₁, hy₀]; exact (hspec 0 1 h01).2

/-! ### General points of the parameter space -/

/-- A dense open of `Spec R`, for a domain `R`, contains the basic open of a nonzero element. -/
private theorem exists_ne_zero_basicOpen_le_of_dense {R : Type*} [CommRing R] [IsDomain R]
    (U : TopologicalSpace.Opens (PrimeSpectrum R)) (hU : Dense (U : Set (PrimeSpectrum R))) :
    ∃ g : R, g ≠ 0 ∧ PrimeSpectrum.basicOpen g ≤ U := by
  obtain ⟨x, hx⟩ := hU.nonempty
  obtain ⟨_, ⟨g, rfl⟩, hxg, hgU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hx U.isOpen
  refine ⟨g, fun h => ?_, hgU⟩
  subst h
  exact (PrimeSpectrum.mem_basicOpen _ _).1 hxg (zero_mem _)

/-- Three dense opens of the affine space of coefficient vectors over an infinite field have a
common rational point. -/
private theorem exists_coefficientPoint_mem {k : Type} [Field k] [Infinite k] {N : ℕ}
    (U₁ U₂ U₃ : (MMP.Threefold.Bridges.coefficientSpace k N).Opens)
    (h₁ : Dense (U₁ : Set (MMP.Threefold.Bridges.coefficientSpace k N)))
    (h₂ : Dense (U₂ : Set (MMP.Threefold.Bridges.coefficientSpace k N)))
    (h₃ : Dense (U₃ : Set (MMP.Threefold.Bridges.coefficientSpace k N))) :
    ∃ c : Fin (N + 1) → k, MMP.Threefold.Bridges.coefficientPoint c ∈ U₁ ∧
      MMP.Threefold.Bridges.coefficientPoint c ∈ U₂ ∧
      MMP.Threefold.Bridges.coefficientPoint c ∈ U₃ := by
  obtain ⟨g₁, hg₁, hU₁⟩ := exists_ne_zero_basicOpen_le_of_dense U₁ h₁
  obtain ⟨g₂, hg₂, hU₂⟩ := exists_ne_zero_basicOpen_le_of_dense U₂ h₂
  obtain ⟨g₃, hg₃, hU₃⟩ := exists_ne_zero_basicOpen_le_of_dense U₃ h₃
  have hg : g₁ * g₂ * g₃ ≠ 0 := mul_ne_zero (mul_ne_zero hg₁ hg₂) hg₃
  obtain ⟨c, hc⟩ : ∃ c : Fin (N + 1) → k, MvPolynomial.eval c (g₁ * g₂ * g₃) ≠ 0 := by
    by_contra h
    push Not at h
    exact hg (MvPolynomial.funext fun c => by simpa using h c)
  simp only [map_mul, ne_eq, mul_eq_zero, not_or] at hc
  have hmem : ∀ g : MvPolynomial (Fin (N + 1)) k, MvPolynomial.eval c g ≠ 0 →
      MMP.Threefold.Bridges.coefficientPoint c ∈ PrimeSpectrum.basicOpen g := fun g hg =>
    (PrimeSpectrum.mem_basicOpen _ _).2 fun h => hg (RingHom.mem_ker.1 h)
  exact ⟨c, hU₁ (hmem _ hc.1.1), hU₂ (hmem _ hc.1.2), hU₃ (hmem _ hc.2)⟩

/-- The components of an snc divisor form an snc family. -/
private theorem isSNCFamily_idealSheaf_of_isSNC {k : Type} [Field k] {Y : Scheme.{0}}
    {g : Y ⟶ Spec (.of k)} {R : Type*} [Zero R] {D : MMP.Mori.DivisorWithCoeffs R Y}
    (hD : D.IsSNC g) : MMP.Resolution.IsSNCFamily g (fun E : D.support => E.1.idealSheaf) := by
  refine ⟨fun E => ⟨?_, MMP.Resolution.isPureCodimOne_support_primeDivisor E.1, hD.1 E.1 E.2⟩,
    fun x => ?_⟩
  · haveI := E.1.integral
    infer_instance
  · obtain ⟨n, z, j, hz, hj, hI⟩ := hD.2 x
    refine ⟨n, z, fun E => j ⟨E.1.1, E.1.2, E.2⟩, hz, fun E => hI ⟨E.1.1, E.1.2, E.2⟩,
      fun E E' h => ?_⟩
    exact Subtype.ext (Subtype.ext (Subtype.mk.inj (hj h)))

section Hyperplane

open Stacks.Ample RingedSpaceModuleAdjunction
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections (globalSectionsModule
  morphismOfGeneratingSections preimage_basicOpen_morphismOfGeneratingSections)
open Stacks.AlgebraicGeometry.GeneratingSectionsRestrict (pullbackSectionsₗ
  pullbackSectionsₗ_apply nonvanishingOpen_pullbackGlobalSections)
open MMP.Threefold.Bridges (systemSection systemSection_apply coefficientPoint)

attribute [local instance] globalSectionsModule

/-- Finitely many sections of positive powers of an invertible sheaf have powers of one common
degree `D ≥ d₀` with the same nonvanishing loci. -/
private theorem exists_common_degree {Y : Scheme.{0}} (M : Y.Modules) [IsInvertibleModule Y M]
    {ι : Type*} [Fintype ι] (n : ι → ℕ) (hn : ∀ i, 1 ≤ n i)
    (σ : ∀ i, Γ(tensorPowModule Y M (n i : ℤ), ⊤)) (d₀ : ℕ) :
    ∃ D : ℕ, d₀ ≤ D ∧ ∃ τ : ι → Γ(tensorPowModule Y M (D : ℤ), ⊤), ∀ i,
      Stacks.AmpleTheory.powNonvanishingOpen Y M D (τ i) =
        Stacks.AmpleTheory.powNonvanishingOpen Y M (n i) (σ i) := by
  classical
  have hP : 0 < ∏ i, n i := Finset.prod_pos fun i _ => hn i
  refine ⟨(∏ i, n i) * (d₀ + 1), by nlinarith, ?_⟩
  have h : ∀ i, ∃ τ : Γ(tensorPowModule Y M (((∏ i, n i) * (d₀ + 1) : ℕ) : ℤ), ⊤),
      Stacks.AmpleTheory.powNonvanishingOpen Y M ((∏ i, n i) * (d₀ + 1)) τ =
        Stacks.AmpleTheory.powNonvanishingOpen Y M (n i) (σ i) := fun i => by
    have hpos : 0 < (∏ j ∈ Finset.univ.erase i, n j) * (d₀ + 1) :=
      Nat.mul_pos (Finset.prod_pos fun j _ => hn j) (Nat.succ_pos _)
    refine exists_powNonvanishingOpen_eq_self M (n i) (σ i)
      ((∏ j ∈ Finset.univ.erase i, n j) * (d₀ + 1) - 1) _ ?_
    rw [Nat.sub_add_cancel hpos, ← mul_assoc, Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  choose τ hτ using h
  exact ⟨τ, hτ⟩

private theorem mem_support_sum_single {Y : Scheme.{0}} {S : Finset (MMP.Mori.PrimeDivisor Y)}
    {E : MMP.Mori.PrimeDivisor Y} :
    E ∈ (∑ P ∈ S, Finsupp.single P (1 : ℤ)).support ↔ E ∈ S := by
  classical
  rw [Finsupp.mem_support_iff, Finsupp.finset_sum_apply]
  simp [Finsupp.single_apply]

/-- **A general hyperplane section.** If the image of `f` has dimension at least two, for every
`d₀` there are `d ≥ d₀` and a smooth prime divisor `F` on `V`, transverse to `B`, with
`𝒪_V(F) ≅ f^*L^d`, which is the preimage of a closed subset of `X` and contains no stratum of
`⌊B⌋`. -/
private theorem Datum.exists_hyperplane (hL : Stacks.Ample.IsAmple X L) (δ : Datum X sX L)
    (hd : 2 ≤ δ.dim) (d₀ : ℕ) :
    ∃ d : ℕ, d₀ ≤ d ∧ ∃ F : MMP.Mori.PrimeDivisor δ.V,
      Nonempty (Divisor.divisorialSheaf (Finsupp.single F 1 : Divisor δ.V) ≅
        (Scheme.Modules.pullback δ.f).obj (Stacks.Ample.tensorPowModule X L (d : ℤ))) ∧
      IsSmoothScheme (F.idealSheaf.subschemeι ≫ δ.sV) ∧ F ∉ δ.B.support ∧
      DivisorWithCoeffs.IsSNC δ.sV
        (Finsupp.single F (1 : ℤ) + ∑ E ∈ δ.B.support, Finsupp.single E (1 : ℤ)) ∧
      ∃ A : Set X, IsClosed A ∧ (F.support : Set δ.V) = δ.f.base ⁻¹' A ∧
        ∀ S : Set δ.V, MMP.Fourfold.IsSNCStratum δ.B.roundDown S → ¬ S ⊆ F.support := by
  classical
  haveI : IsInvertibleModule X L := ‹_›
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  haveI : IsProper sX := (IsProjectiveMorphism.isProjective
    (AlgebraicGeometry.IsProjectiveVariety.isProjective (k := ℂ) (f := sX))).isProper
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : IsIntegral δ.V := δ.isIntegral
  haveI : CompactSpace δ.V := QuasiCompact.compactSpace_of_compactSpace δ.sV
  letI : X.Over (Spec (.of ℂ)) := ⟨sX⟩
  letI : δ.V.Over (Spec (.of ℂ)) := ⟨δ.sV⟩
  haveI : AlgebraicGeometry.IsVariety ℂ (δ.V ↘ Spec (.of ℂ)) :=
    ((AlgebraicGeometry.isProjectiveVariety_iff ℂ δ.sV).1 δ.proj).1
  haveI : IsSmoothVariety ℂ (δ.V ↘ Spec (.of ℂ)) :=
    { toIsVariety := inferInstance, toSmooth := (isSmoothScheme_iff _).mp δ.hVsm }
  -- a chain in the image of `f`, and sections of powers of `L` separating it
  obtain ⟨y₂, y₁, y₀, h21, h10, hne21, hne10⟩ := δ.exists_chain hd
  have hsep : ∀ {a b : X}, a ⤳ b → a ≠ b → ∃ n : ℕ, 1 ≤ n ∧
      ∃ σ : Γ(tensorPowModule X L (n : ℤ), ⊤),
        a ∈ Stacks.AmpleTheory.powNonvanishingOpen X L n σ ∧
        b ∉ Stacks.AmpleTheory.powNonvanishingOpen X L n σ := by
    intro a b hab hne
    have hb : a ∉ closure {b} := fun h =>
      hne (hab.antisymm (specializes_iff_mem_closure.2 h)).eq
    obtain ⟨n, hn, σ, -, haσ, hσW⟩ :=
      Stacks.AmpleFiniteAffineNonvanishing.exists_affine_nonvanishingOpen_containing_finite L hL
        (Set.finite_singleton a) ⟨(closure {b})ᶜ, isClosed_closure.isOpen_compl⟩
        (Set.singleton_subset_iff.2 hb)
    exact ⟨n, hn, σ, haσ rfl, fun h => hσW h (subset_closure rfl)⟩
  obtain ⟨n₁, hn₁, σ₁, h₁a, h₁b⟩ := hsep (h21.map δ.f.base.hom.continuous) hne21
  obtain ⟨n₂, hn₂, σ₂, h₂a, h₂b⟩ := hsep (h10.map δ.f.base.hom.continuous) hne10
  -- a finite cover of `X` by nonvanishing opens
  have hcov : ∀ x : X, ∃ n : ℕ, 1 ≤ n ∧ ∃ σ : Γ(tensorPowModule X L (n : ℤ), ⊤),
      x ∈ Stacks.AmpleTheory.powNonvanishingOpen X L n σ := fun x => by
    obtain ⟨n, hn, σ, -, hxσ, -⟩ :=
      Stacks.AmpleFiniteAffineNonvanishing.exists_affine_nonvanishingOpen_containing_finite L hL
        (Set.finite_singleton x) ⊤ (by simp)
    exact ⟨n, hn, σ, hxσ rfl⟩
  choose nx hnx σx hσx using hcov
  obtain ⟨P, hP⟩ := isCompact_univ.elim_finite_subcover
    (fun x => (Stacks.AmpleTheory.powNonvanishingOpen X L (nx x) (σx x) : Set X))
    (fun x => (Stacks.AmpleTheory.powNonvanishingOpen X L (nx x) (σx x)).isOpen)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hσx x⟩)
  -- all these sections in one degree `D ≥ d₀`
  let nι : Option (Option P) → ℕ := fun i => i.elim n₁ fun j => j.elim n₂ fun x => nx x
  have hnι : ∀ i, 1 ≤ nι i := by
    rintro (_ | _ | x)
    · exact hn₁
    · exact hn₂
    · exact hnx x
  let σι : ∀ i, Γ(tensorPowModule X L (nι i : ℤ), ⊤) := fun i =>
    match i with
    | none => σ₁
    | some none => σ₂
    | some (some x) => σx x
  obtain ⟨D, hD, τ, hτ⟩ := exists_common_degree L nι hnι σι d₀
  obtain ⟨N, hN⟩ : ∃ N, Fintype.card (Option (Option P)) = N + 1 :=
    ⟨Fintype.card (Option (Option P)) - 1, by
      have : 0 < Fintype.card (Option (Option P)) := Fintype.card_pos
      omega⟩
  let e : Fin (N + 1) ≃ Option (Option P) := (Fintype.equivFinOfCardEq hN).symm
  let ML := tensorPowModule X L (D : ℤ)
  let t : Fin (N + 1) → Γ(ML, ⊤) := fun j => τ (e j)
  have ht : ∀ i, nonvanishingOpen X ML (t (e.symm i)) =
      Stacks.AmpleTheory.powNonvanishingOpen X L (nι i) (σι i) := fun i => by
    have := hτ i
    simp only [t, Equiv.apply_symm_apply]
    rw [← this]
    rfl
  let MV := (Scheme.Modules.pullback δ.f).obj ML
  have hfs' : δ.f ≫ (X ↘ Spec (.of ℂ)) = δ.V ↘ Spec (.of ℂ) := δ.hfs
  let s : Fin (N + 1) → Γ(MV, ⊤) := fun j => pullbackSectionsₗ ℂ δ.f ML hfs' (t j)
  have hsys : ∀ c : Fin (N + 1) → ℂ,
      systemSection s c = pullbackSectionsₗ ℂ δ.f ML hfs' (systemSection t c) :=
    fun c => by simp only [systemSection_apply, map_sum, map_smul, s]
  have hnvV : ∀ (c : Fin (N + 1) → ℂ) (y : δ.V), y ∈ nonvanishingOpen δ.V MV (systemSection s c) ↔
      δ.f.base y ∈ nonvanishingOpen X ML (systemSection t c) := fun c y => by
    rw [hsys, pullbackSectionsₗ_apply, nonvanishingOpen_pullbackGlobalSections]
    try exact Iff.rfl
  have hsingle : ∀ j, systemSection t (Pi.single j (1 : ℂ)) = t j := fun j => by
    simp [systemSection, Fintype.linearCombination_apply_single]
  have hsV : ⨆ c : Fin (N + 1) → ℂ, nonvanishingOpen δ.V MV (systemSection s c) = ⊤ := by
    refine eq_top_iff.2 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ?_
    obtain ⟨x, hxP, hx⟩ := Set.mem_iUnion₂.1 (hP (Set.mem_univ (δ.f.base y)))
    refine ⟨Pi.single (e.symm (some (some ⟨x, hxP⟩))) 1, (hnvV _ y).2 ?_⟩
    rw [hsingle, ht]
    exact hx
  -- the morphism of the system separates the chain, so its image has dimension at least two
  have hΨ : ∀ (j : Fin (N + 1)) (y : δ.V),
      (morphismOfGeneratingSections ℂ (Fin (N + 1) → ℂ) MV (systemSection s) hsV).base y ∈
        Proj.basicOpen (ProjectiveSpaceOfModule.symmetricGrading ℂ (Fin (N + 1) → ℂ))
          (SymmetricAlgebra.ι ℂ (Fin (N + 1) → ℂ) (Pi.single j 1)) ↔
      δ.f.base y ∈ nonvanishingOpen X ML (t j) := fun j y => by
    have h := preimage_basicOpen_morphismOfGeneratingSections ℂ (Fin (N + 1) → ℂ) MV
      (systemSection s) hsV (Pi.single j 1)
    rw [← hsingle, ← hnvV, ← h]
    try exact Iff.rfl
  have hdim : 2 ≤ topologicalKrullDim (Set.range
      (morphismOfGeneratingSections ℂ (Fin (N + 1) → ℂ) MV (systemSection s) hsV)) := by
    refine two_le_topologicalKrullDim_of_specializes ⟨y₂, rfl⟩ ⟨y₁, rfl⟩ ⟨y₀, rfl⟩
      (h21.map (Scheme.Hom.continuous _)) (h10.map (Scheme.Hom.continuous _)) ?_ ?_
    · intro h
      have h1 := (hΨ (e.symm none) y₂).2 (by rw [ht]; exact h₁a)
      change (morphismOfGeneratingSections ℂ (Fin (N + 1) → ℂ) MV (systemSection s) hsV).base
        y₂ = _ at h
      rw [h, hΨ, ht] at h1
      exact h₁b h1
    · intro h
      have h1 := (hΨ (e.symm (some none)) y₁).2 (by rw [ht]; exact h₂a)
      change (morphismOfGeneratingSections ℂ (Fin (N + 1) → ℂ) MV (systemSection s) hsV).base
        y₁ = _ at h
      rw [h, hΨ, ht] at h1
      exact h₂b h1
  -- Bertini
  haveI : Smooth (𝟙 δ.V ≫ δ.V ↘ Spec (.of ℂ)) := by rw [Category.id_comp]; infer_instance
  obtain ⟨U₁, hU₁, hB₁⟩ :=
    MMP.Threefold.Bridges.exists_dense_open_smooth_zeroScheme_isSNC_add s hsV δ.B δ.hB
  obtain ⟨⟨U₂, hU₂, hB₂⟩, -⟩ := MMP.Threefold.Bridges.exists_dense_open_isSNCFamily_zeroScheme
    s hsV (𝟙 δ.V) (fun E : δ.B.support => E.1.idealSheaf)
    (by rw [Category.id_comp]; exact isSNCFamily_idealSheaf_of_isSNC δ.hB)
  obtain ⟨⟨U₃, hU₃, hB₃⟩, -⟩ :=
    MMP.Threefold.Bridges.exists_dense_open_geometricallyIntegral_zeroScheme s hsV hdim
  obtain ⟨c, hc₁, hc₂, hc₃⟩ := exists_coefficientPoint_mem U₁ U₂ U₃ hU₁ hU₂ hU₃
  obtain ⟨-, T, hT, hTB, hTsnc⟩ := hB₁ c hc₁
  obtain ⟨-, hstr, -⟩ := hB₂ c hc₂
  obtain ⟨-, hZint⟩ := hB₃ c hc₃
  simp only [Scheme.IdealSheafData.comap_id] at hstr
  -- the member `Z = Z(σ)` is a prime divisor `F`
  haveI : SheafOfModules.IsInvertible δ.V.sheaf.obj δ.V.ringCatSheaf.property MV :=
    InvertibleSheafGeneral.isInvertible_of_isInvertibleModule _
  haveI := hZint
  have hZirr : IsIrreducible ((zeroScheme δ.V MV (systemSection s c)).support : Set δ.V) := by
    rw [← Scheme.IdealSheafData.range_subschemeι, ← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ (Scheme.Hom.continuous _).continuousOn
  obtain ⟨F, hFT, hFZ⟩ := (hT _).1 ⟨⟨hZirr, le_rfl⟩, fun W hW _ => hW.2⟩
  have hFV : ∀ y : δ.V, y ∈ F.support ↔
      δ.f.base y ∉ nonvanishingOpen X ML (systemSection t c) := fun y => by
    rw [hFZ, ← hnvV]
    have := mem_nonvanishingLocus_iff_notMem_supportSet_zeroScheme MV (systemSection s c) y
    exact ⟨fun h h' => (this.1 h') h, fun h => by
      by_contra h'
      exact h (this.2 h')⟩
  -- no stratum lies in `F`
  have huniv : MMP.Fourfold.IsSNCStratum δ.B.roundDown Set.univ := by
    haveI : IrreducibleSpace δ.V := by haveI := δ.isIntegral; infer_instance
    exact ⟨∅, Finset.empty_subset _, ⟨IrreducibleSpace.isIrreducible_univ _, by simp⟩,
      fun T _ _ => Set.subset_univ T⟩
  have hS : ∀ S : Set δ.V, MMP.Fourfold.IsSNCStratum δ.B.roundDown S → ¬ S ⊆ F.support := by
    rintro S ⟨J', hJ', hS⟩ hSF
    have hJB : ∀ E ∈ J', E ∈ δ.B.support := fun E hE => by
      have h := Finsupp.mem_support_iff.1 (hJ' hE)
      rw [Finsupp.mem_support_iff]
      intro h0
      apply h
      change (δ.B.roundDown).coeff E = 0
      rw [DivisorWithCoeffs.coeff_roundDown]
      change ⌊δ.B E⌋ = 0
      rw [h0, Int.floor_zero]
    let J : Set δ.B.support := {E | E.1 ∈ J'}
    have hJeq : (⋂ i ∈ J, ((i.1.idealSheaf.support : Set δ.V))) =
        ⋂ E ∈ J', (E.support : Set δ.V) := by
      ext x
      simp only [Set.mem_iInter]
      exact ⟨fun h E hE => h ⟨E, hJB E hE⟩ hE, fun h i hi => h i.1 hi⟩
    refine hstr J S ?_ ?_
    · simp only [MMP.Resolution.componentsOf, Set.mem_setOf_eq]
      rw [hJeq]
      exact hS
    · rw [← hFZ]
      exact hSF
  -- `σ ≠ 0`, so `Z` is an effective Cartier divisor, equal to `F`
  have hne0 : systemSection s c ≠ 0 := by
    intro h0
    apply hS Set.univ huniv
    intro y _
    rw [hFV, ← hnvV, h0]
    intro hy
    change y ∈ nonvanishingLocus MV 0 at hy
    rw [mem_nonvanishingLocus_iff] at hy
    exact hy (by simp)
  have hevaltop : (Stacks.SheafOfModules.sectionsOfTop MV (systemSection s c)).eval (op ⊤) =
      systemSection s c := Stacks.SheafOfModules.sectionsOfTop_eval_top _ _
  have hreg : IsRegularSection δ.V.sheaf.obj δ.V.ringCatSheaf.property
      (Stacks.SheafOfModules.sectionsOfTop MV (systemSection s c)) :=
    isRegularSection_of_eval_top_ne_zero _ _ (by rwa [hevaltop])
  have hZc : Stacks.Divisors.IsEffectiveCartierDivisor (zeroScheme δ.V MV
      ((Stacks.SheafOfModules.sectionsOfTop MV (systemSection s c)).eval (op ⊤))) :=
    (isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection δ.V _ _).2 hreg
  have hZF : zeroScheme δ.V MV
      ((Stacks.SheafOfModules.sectionsOfTop MV (systemSection s c)).eval (op ⊤)) =
        F.idealSheaf := by
    rw [hevaltop]
    haveI : IsIntegral F.idealSheaf.subscheme := F.integral
    rw [Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme
        (zeroScheme δ.V MV (systemSection s c)) F.idealSheaf.support
        (TopologicalSpace.Closeds.ext hFZ.symm),
      ← Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme F.idealSheaf
        F.idealSheaf.support rfl]
  obtain ⟨eF⟩ := MMP.Threefold.Resolution.nonempty_divisorialSheaf_single_iso_invertibleSheaf'
    F (hZF ▸ hZc) (δ.isCartier _)
  have hFmem : F ∈ (∑ E ∈ T ∪ δ.B.support, Finsupp.single E (1 : ℤ)).support :=
    mem_support_sum_single.2 (Finset.mem_union_left _ hFT)
  refine ⟨D, hD, F, ⟨eF ≪≫ eqToIso (by rw [hZF]) ≪≫
      (invertibleSheafIsoZeroSchemeOfIsRegularSection _ _ hreg).symm⟩,
    hTsnc.1 F hFmem, fun h => Finset.disjoint_left.1 hTB hFT h, ?_,
    _, (nonvanishingOpen X ML (systemSection t c)).isOpen.isClosed_compl, ?_, hS⟩
  · refine hTsnc.of_support_subset fun E hE => mem_support_sum_single.2 ?_
    rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.finset_sum_apply] at hE
    by_cases hEF : E = F
    · exact hEF ▸ Finset.mem_union_left _ hFT
    · refine Finset.mem_union_right _ ?_
      by_contra hEB
      exact hE (by simp [Finsupp.single_apply, Ne.symm hEF, hEB])
  · ext y
    exact hFV y

end Hyperplane

/-- **Torsion-freeness gives injectivity.** If `f(F)` misses the generic points of the images of
the strata of `⌊B⌋`, then `R^q f_* 𝒪_V(M) ⟶ R^q f_* 𝒪_V(M + F)` is a monomorphism. -/
private theorem Datum.mono_of_avoid (hL : Stacks.Ample.IsAmple X L) (δ : Datum X sX L)
    (F : MMP.Mori.PrimeDivisor δ.V)
    (hF : ∀ S : Set δ.V, MMP.Fourfold.IsSNCStratum δ.B.roundDown S → ∀ x : X,
      closure {x} = δ.f.base '' S → ∀ y ∈ F.support, δ.f.base y ≠ x) (q : ℕ) :
    Mono (((Scheme.Modules.pushforward δ.f).rightDerived q).map
      (Divisor.divisorialSheafInclusion (le_add_of_nonneg_right
        (Finsupp.single_nonneg.2 zero_le_one) : δ.M ≤ δ.M + Finsupp.single F 1))) := by
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  haveI : IsProper δ.f := δ.hfp.isProper
  haveI : CompactSpace δ.V := QuasiCompact.compactSpace_of_compactSpace δ.sV
  haveI : AlgebraicGeometry.IsVariety ℂ sX :=
    ((AlgebraicGeometry.isProjectiveVariety_iff ℂ sX).1 inferInstance).1
  have hqc : ∀ D : Divisor δ.V, D.IsCartier →
      (((Scheme.Modules.pushforward δ.f).rightDerived q).obj D.divisorialSheaf).IsQuasicoherent :=
    fun D hD =>
    haveI : D.divisorialSheaf.IsCoherent :=
      @Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isInvertible δ.V _ _
        hD.isInvertibleModule_divisorialSheaf
    haveI : (((Scheme.Modules.pushforward δ.f).rightDerived q).obj D.divisorialSheaf).IsCoherent :=
      Stacks.AlgebraicGeometry.RelativeSerreVanishing.isCoherent_of_iso
        ((@Stacks.DerivedIndexing.rightDerivedIso _ _ _ _ _ _ _ (Scheme.Modules.pushforward δ.f) _
          (HasDerivedCategory.standard _) (HasDerivedCategory.standard _) q).app _).symm
        (ProperCoherenceWitness.higherDirectImageIsCoherent δ.V X δ.f inferInstance inferInstance _
          inferInstance q)
    _root_.isQuasicoherent_of_isCoherent _
  haveI := hqc _ δ.hM
  haveI := hqc _ (δ.isCartier (δ.M + Finsupp.single F 1))
  set φ := Divisor.divisorialSheafInclusion (le_add_of_nonneg_right
    (Finsupp.single_nonneg.2 zero_le_one) : δ.M ≤ δ.M + Finsupp.single F 1)
  refine Stacks.Divisors.mono_of_stalk_injective_on_associatedPoints _ fun x => ?_
  by_cases hx : x ∈ Stacks.Divisors.associatedPoints
    (((Scheme.Modules.pushforward δ.f).rightDerived q).obj δ.M.divisorialSheaf)
  swap
  · exact Or.inr hx
  left
  obtain ⟨S, hS, hSx⟩ :=
    MMP.Mori.exists_isSNCStratum_closure_eq_image_of_isAssociatedPoint_rightDerived_pushforward
      sX δ.sV δ.hVsm δ.f δ.hfs δ.hfp δ.K δ.hK δ.B δ.hB δ.hB0 δ.hB1 δ.M δ.hM
      (δ.isRelativelySemiample_adjoint hL sX δ.f δ.hfs) q x hx
  let U : X.Opens := ⟨(δ.f.base '' F.support)ᶜ,
    (δ.f.isClosedMap _ F.idealSheaf.support.isClosed).isOpen_compl⟩
  have hxU : x ∈ U := fun ⟨y, hy, hyx⟩ => hF S hS x hSx y hy hyx
  have hW : IsIso ((Scheme.Modules.restrictFunctor (δ.f ⁻¹ᵁ U).ι).map φ) :=
    Divisor.isIso_restrict_divisorialSheafInclusion _ fun E ⟨y, hyE, hyU⟩ => by
      have hEF : E ≠ F := by
        rintro rfl
        exact hyU ⟨y, hyE, rfl⟩
      simp [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply, Ne.symm hEF]
  have hV : IsIso ((Scheme.Modules.restrictFunctor U.ι).map
      (((Scheme.Modules.pushforward δ.f).rightDerived q).map φ)) :=
    (NatIso.isIso_map_iff
      (AlgebraicGeometry.ProjectiveCoherentImage.higherDirectImageRestrictIsoScheme δ.f U q) φ).mp
      (by dsimp only [Functor.comp_map]; infer_instance)
  set g := ((Scheme.Modules.pushforward δ.f).rightDerived q).map φ
  let e := Scheme.Modules.restrictStalkNatIso U.ι ⟨x, hxU⟩
  have hnat := e.hom.naturality g
  haveI : IsIso ((Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.toPresheaf _ ⋙
      TopCat.Presheaf.stalkFunctor _ (⟨x, hxU⟩ : U.toScheme)).map g) := by
    dsimp only [Functor.comp_map]; infer_instance
  have hiso : IsIso ((Scheme.Modules.toPresheaf _ ⋙
      TopCat.Presheaf.stalkFunctor _ (U.ι ⟨x, hxU⟩)).map g) := by
    have : (Scheme.Modules.toPresheaf _ ⋙ TopCat.Presheaf.stalkFunctor _ (U.ι ⟨x, hxU⟩)).map g =
        e.inv.app _ ≫ (Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.toPresheaf _ ⋙
          TopCat.Presheaf.stalkFunctor _ (⟨x, hxU⟩ : U.toScheme)).map g ≫ e.hom.app _ := by
      rw [hnat, Iso.inv_hom_id_app_assoc]
    rw [this]
    infer_instance
  exact ((ConcreteCategory.isIso_iff_bijective _).1 hiso).1

/-! ### Divisorial sheaves along a morphism

For `g : W ⟶ Y` between normal schemes on which every divisor is Cartier, say that `a' ↝ a` when
`𝒪_W(a') ≅ g^* 𝒪_Y(a)`. This relation is additive, and it can be cancelled when `W` is integral
and every invertible sheaf on `W` is divisorial. -/

section Restricts

variable {Y W : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
  [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W] (g : W ⟶ Y)
  (hY : ∀ D : Divisor Y, D.IsCartier) (hW : ∀ D : Divisor W, D.IsCartier)

include hY hW

/-- `𝒪_W(a') ≅ g^* 𝒪_Y(a)` is additive in `(a, a')`. -/
private theorem nonempty_divisorialSheaf_add_iso_pullback {a b : Divisor Y} {a' b' : Divisor W}
    (ea : Nonempty (a'.divisorialSheaf ≅ (Scheme.Modules.pullback g).obj a.divisorialSheaf))
    (eb : Nonempty (b'.divisorialSheaf ≅ (Scheme.Modules.pullback g).obj b.divisorialSheaf)) :
    Nonempty ((a' + b').divisorialSheaf ≅
      (Scheme.Modules.pullback g).obj (a + b).divisorialSheaf) := by
  obtain ⟨ea⟩ := ea
  obtain ⟨eb⟩ := eb
  exact ⟨((hW a').divisorialSheafTensorIso (hW b')).symm ≪≫ MonoidalCategory.tensorIso ea eb ≪≫
    (Stacks.RelativeVeryAmple.pullbackTensorModulesIso g _ _).symm ≪≫
    (Scheme.Modules.pullback g).mapIso ((hY a).divisorialSheafTensorIso (hY b))⟩

/-- `𝒪_W(a') ≅ g^* 𝒪_Y(a)` passes to positive multiples. -/
private theorem nonempty_divisorialSheaf_nsmul_iso_pullback {a : Divisor Y} {a' : Divisor W}
    (ea : Nonempty (a'.divisorialSheaf ≅ (Scheme.Modules.pullback g).obj a.divisorialSheaf))
    {j : ℕ} (hj : 1 ≤ j) :
    Nonempty ((j • a').divisorialSheaf ≅
      (Scheme.Modules.pullback g).obj (j • a).divisorialSheaf) := by
  induction j, hj using Nat.le_induction with
  | base => simpa using ea
  | succ j _ ih =>
    simpa [succ_nsmul] using nonempty_divisorialSheaf_add_iso_pullback g hY hW ih ea

/-- **Cancellation.** If `c ↝ a + b` and `a' ↝ a`, then `c - a' ↝ b`. -/
private theorem nonempty_divisorialSheaf_sub_iso_pullback [IsIntegral W]
    (hinv : ∀ L : W.Modules, Stacks.Ample.IsInvertibleModule W L →
      ∃ G : Divisor W, Nonempty (G.divisorialSheaf ≅ L))
    {a b : Divisor Y} {a' c : Divisor W}
    (h : Nonempty (c.divisorialSheaf ≅ (Scheme.Modules.pullback g).obj (a + b).divisorialSheaf))
    (ea : Nonempty (a'.divisorialSheaf ≅ (Scheme.Modules.pullback g).obj a.divisorialSheaf)) :
    Nonempty ((c - a').divisorialSheaf ≅ (Scheme.Modules.pullback g).obj b.divisorialSheaf) := by
  haveI := (hY b).isInvertibleModule_divisorialSheaf
  obtain ⟨G, ⟨eG⟩⟩ := hinv ((Scheme.Modules.pullback g).obj b.divisorialSheaf) inferInstance
  obtain ⟨e⟩ := h
  obtain ⟨e'⟩ := nonempty_divisorialSheaf_add_iso_pullback g hY hW ea ⟨eG⟩
  have hl : c.LinearlyEquivalent (a' + G) :=
    MMP.Flips.linearlyEquivalent_of_divisorialSheaf_iso (e ≪≫ e'.symm)
  have hl' : (c - a').LinearlyEquivalent G := by
    have := hl.add (Divisor.LinearlyEquivalent.refl (-a'))
    rwa [← sub_eq_add_neg, add_neg_cancel_comm] at this
  exact ⟨hl'.divisorialSheafIso ≪≫ eG⟩

end Restricts

/-- **Adjunction.** The restriction of the datum to a smooth prime divisor `F` transverse to `B`
is a datum over `X`, whose direct images are those of `𝒪_F(M + F)`. -/
private theorem Datum.exists_restrict (δ : Datum X sX L) (F : MMP.Mori.PrimeDivisor δ.V)
    (hFsm : IsSmoothScheme (F.idealSheaf.subschemeι ≫ δ.sV)) (hFB : F ∉ δ.B.support)
    (hsnc : DivisorWithCoeffs.IsSNC δ.sV
      (Finsupp.single F (1 : ℤ) + ∑ E ∈ δ.B.support, Finsupp.single E (1 : ℤ))) :
    ∃ δ' : Datum X sX L, Set.range δ'.f.base = δ.f.base '' F.support ∧
      ∀ q, Nonempty ((((Scheme.Modules.pushforward δ.f).rightDerived q).obj
        ((Scheme.Modules.pullback F.idealSheaf.subschemeι ⋙
          Scheme.Modules.pushforward F.idealSheaf.subschemeι).obj
            (δ.M + Finsupp.single F 1).divisorialSheaf)) ≅
        ((Scheme.Modules.pushforward δ'.f).rightDerived q).obj δ'.M.divisorialSheaf) := by
  classical
  set ι := F.idealSheaf.subschemeι with hι
  haveI : CompactSpace δ.V := QuasiCompact.compactSpace_of_compactSpace δ.sV
  haveI : IsIntegral δ.V := δ.isIntegral
  haveI hVsv : IsSmoothVariety ℂ δ.sV :=
    { toIsVariety := inferInstance, toSmooth := (isSmoothScheme_iff _).mp δ.hVsm }
  haveI : IsIntegral F.idealSheaf.subscheme := F.integral
  haveI : Smooth (ι ≫ δ.sV) := (isSmoothScheme_iff _).mp hFsm
  haveI : AlgebraicGeometry.IsVariety ℂ δ.sV :=
    ((AlgebraicGeometry.isProjectiveVariety_iff ℂ δ.sV).1 δ.proj).1
  haveI : AlgebraicGeometry.IsVariety ℂ (ι ≫ δ.sV) := {}
  haveI hproj : AlgebraicGeometry.IsProjectiveVariety ℂ (ι ≫ δ.sV) :=
    (AlgebraicGeometry.isProjectiveVariety_iff ℂ _).mpr
      ⟨inferInstance, (MMP.isProjectiveMorphism_of_isClosedImmersion _).comp
        (AlgebraicGeometry.IsProjectiveVariety.isProjective (k := ℂ) (f := δ.sV))⟩
  haveI hWsv : IsSmoothVariety ℂ (ι ≫ δ.sV) :=
    { toIsVariety := inferInstance, toSmooth := inferInstance }
  haveI : IsLocallyNoetherian F.idealSheaf.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (ι ≫ δ.sV)
  haveI : IsNormal F.idealSheaf.subscheme := isNormal_of_smooth_over_field (ι ≫ δ.sV)
  haveI : CompactSpace F.idealSheaf.subscheme :=
    QuasiCompact.compactSpace_of_compactSpace (ι ≫ δ.sV)
  obtain ⟨hcW, -, -, -, hinvW, -⟩ := Divisor.cartier_weil_dictionary_of_isSmoothVariety ℂ (ι ≫ δ.sV)
  -- the canonical divisor of `F`
  obtain ⟨n', hn', hdimW⟩ : ∃ n' : ℕ, δ.n = n' + 1 ∧
      topologicalKrullDim F.idealSheaf.subscheme = n' := by
    have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight δ.sV F.genericPoint
    rw [F.coheight_genericPoint, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      δ.hK.topologicalKrullDim_eq] at h
    rw [ι.isClosedEmbedding.toIsEmbedding.toHomeomorph.isHomeomorph.topologicalKrullDim_eq,
      Scheme.IdealSheafData.range_subschemeι]
    generalize hd : topologicalKrullDim (F.support : Set δ.V) = d at h
    induction d using WithBot.recBotCoe with
    | bot => exact absurd h (by simp)
    | coe e =>
      induction e using ENat.recTopCoe with
      | top =>
        exfalso
        have h' : ((⊤ : ℕ∞) + 1 : ℕ∞) = (δ.n : ℕ∞) :=
          WithBot.coe_injective (by rw [WithBot.coe_add]; exact h)
        rw [top_add] at h'
        exact ENat.top_ne_coe _ h'
      | coe k =>
        refine ⟨k, ?_, rfl⟩
        have : ((k + 1 : ℕ) : WithBot ℕ∞) = (δ.n : WithBot ℕ∞) := by rw [← h]; norm_cast
        exact_mod_cast this.symm
  obtain ⟨KF, hKF⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (ι ≫ δ.sV) hFsm hdimW
  -- the adjoint divisor on `F`
  haveI := (δ.isCartier (δ.M + Finsupp.single F 1)).isInvertibleModule_divisorialSheaf
  obtain ⟨M', ⟨eM'⟩⟩ := hinvW
    ((Scheme.Modules.pullback ι).obj (δ.M + Finsupp.single F 1).divisorialSheaf) inferInstance
  -- the boundary on `F`
  have hBF : δ.B.coeff F = 0 := Finsupp.notMem_support_iff.mp hFB
  haveI : TopologicalSpace.NoetherianSpace δ.V := δ.noetherianSpace
  haveI : Smooth δ.sV := hVsv.toSmooth
  set T : Divisor δ.V := ∑ E ∈ δ.B.support, Finsupp.single E (1 : ℤ) with hT
  have hTapp : ∀ E, T E = if E ∈ δ.B.support then 1 else 0 := fun E => by
    simp [hT, Finsupp.finset_sum_apply, Finsupp.single_apply]
  have hTsupp : T.support ⊆ δ.B.support := fun E hE => by
    rw [Finsupp.mem_support_iff, hTapp] at hE
    by_contra h
    exact hE (if_neg h)
  have hTF : T.coeff F = 0 := by
    change T F = 0
    rw [hTapp, if_neg hFB]
  obtain ⟨hTsnc, hT1⟩ :=
    DivisorWithCoeffs.isSNC_restrictPrimeDivisor_sum_single (k := ℂ) δ.sV F δ.B.support hFB hsnc
  have hcT : ∀ Q, (T.restrictPrimeDivisor F).coeff Q =
      ((∑ E ∈ δ.B.support, E.intersectionLength ι Q : ℕ) : ℤ) := by
    intro Q
    rw [DivisorWithCoeffs.coeff_restrictPrimeDivisor _ F hTF Q,
      Finsupp.sum_of_support_subset _ hTsupp _ (fun _ _ => smul_zero _), Nat.cast_sum]
    refine Finset.sum_congr rfl fun E hE => ?_
    rw [hTapp, if_pos hE, nsmul_eq_mul, mul_one]
  have hcB : ∀ Q, (δ.B.restrictPrimeDivisor F).coeff Q =
      ∑ E ∈ δ.B.support, E.intersectionLength ι Q • δ.B E := fun Q => by
    rw [DivisorWithCoeffs.coeff_restrictPrimeDivisor _ F hBF Q]
    rfl
  have hT01 : ∀ Q, ∑ E ∈ δ.B.support, E.intersectionLength ι Q ≤ 1 := by
    intro Q
    by_cases hQ : Q ∈ (T.restrictPrimeDivisor F).support
    · have h := hT1 Q hQ
      rw [hcT] at h
      exact_mod_cast h.le
    · have h : (T.restrictPrimeDivisor F).coeff Q = 0 := Finsupp.notMem_support_iff.mp hQ
      rw [hcT] at h
      exact_mod_cast h.le.trans zero_le_one
  have hBsnc : (δ.B.restrictPrimeDivisor F).IsSNC (ι ≫ δ.sV) := by
    refine hTsnc.of_support_subset fun Q hQ => ?_
    rw [Finsupp.mem_support_iff] at hQ ⊢
    intro hTQ
    have h0 : ∑ E ∈ δ.B.support, E.intersectionLength ι Q = 0 := by
      have h := hcT Q
      change T.restrictPrimeDivisor F Q = _ at h
      rw [hTQ] at h
      exact_mod_cast h.symm
    apply hQ
    change (δ.B.restrictPrimeDivisor F).coeff Q = 0
    rw [hcB]
    exact Finset.sum_eq_zero fun E hE => by
      rw [(Finset.sum_eq_zero_iff.mp h0) E hE, zero_smul]
  have hB01 : ∀ E, 0 ≤ δ.B.restrictPrimeDivisor F E ∧ δ.B.restrictPrimeDivisor F E ≤ 1 := by
    intro Q
    change 0 ≤ (δ.B.restrictPrimeDivisor F).coeff Q ∧ (δ.B.restrictPrimeDivisor F).coeff Q ≤ 1
    rw [hcB]
    refine ⟨Finset.sum_nonneg fun E _ => nsmul_nonneg (δ.hB0 E) _, ?_⟩
    calc ∑ E ∈ δ.B.support, E.intersectionLength ι Q • δ.B E
        ≤ ∑ E ∈ δ.B.support, E.intersectionLength ι Q • (1 : ℚ) :=
          Finset.sum_le_sum fun E _ => nsmul_le_nsmul_right (δ.hB1 E) _
      _ = ((∑ E ∈ δ.B.support, E.intersectionLength ι Q : ℕ) : ℚ) := by
          simp [nsmul_eq_mul]
      _ ≤ 1 := by exact_mod_cast hT01 Q
  have hlin' : ∃ m : ℕ, 0 < m ∧ ∃ D : Divisor F.idealSheaf.subscheme,
      Divisor.toQDivisor D = (m : ℚ) • (Divisor.toQDivisor M' -
        (Divisor.toQDivisor KF + δ.B.restrictPrimeDivisor F)) ∧
      Nonempty (D.divisorialSheaf ≅ (Scheme.Modules.pullback (ι ≫ δ.f)).obj L) := by
    obtain ⟨hcV, -⟩ := Divisor.cartier_weil_dictionary_of_isSmoothVariety ℂ δ.sV
    obtain ⟨m, hm, D, hD, ⟨eD⟩⟩ := δ.hlin
    set E : Divisor δ.V := m • (δ.M - δ.K) - D with hE
    have hEq : Divisor.toQDivisor E = (m : ℚ) • δ.B := by
      simp only [hE, map_sub, map_nsmul, hD, ← Nat.cast_smul_eq_nsmul ℚ]
      module
    have hEF : E.coeff F = 0 := by
      have h := congrArg (fun Q : QDivisor δ.V => Q.coeff F) hEq
      simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, hBF, smul_zero] at h
      exact_mod_cast h
    have rE : Nonempty (Divisor.divisorialSheaf (E.restrictPrimeDivisor F) ≅
        (Scheme.Modules.pullback ι).obj E.divisorialSheaf) :=
      (Divisor.isCartier_restrictPrimeDivisor_of_isSmoothVariety ℂ δ.sV F E hEF).2.1
    have rAdj : Nonempty ((KF + M').divisorialSheaf ≅ (Scheme.Modules.pullback ι).obj
        ((δ.M + Finsupp.single F 1) + (δ.K + Finsupp.single F 1)).divisorialSheaf) := by
      obtain ⟨eA⟩ := Divisor.nonempty_pullback_divisorialSheaf_iso_of_isCanonicalDivisor δ.sV
        inferInstance δ.hVsm (hn' ▸ δ.hK) F hFsm (hcV (δ.M + Finsupp.single F 1))
      obtain ⟨eK⟩ := nonempty_divisorialSheaf_iso_of_isCanonicalDivisor hFsm hKF
      rw [show (δ.M + Finsupp.single F 1) + (δ.K + Finsupp.single F 1) =
        δ.K + (δ.M + Finsupp.single F 1) + Finsupp.single F 1 by abel]
      exact ⟨((hcW KF).divisorialSheafTensorIso (hcW M')).symm ≪≫
        MonoidalCategory.tensorIso eK eM' ≪≫ eA.symm⟩
    have rK : Nonempty (KF.divisorialSheaf ≅
        (Scheme.Modules.pullback ι).obj (δ.K + Finsupp.single F 1).divisorialSheaf) := by
      simpa using nonempty_divisorialSheaf_sub_iso_pullback ι hcV hcW hinvW rAdj ⟨eM'⟩
    have rA : Nonempty (Divisor.divisorialSheaf (m • KF + E.restrictPrimeDivisor F) ≅
        (Scheme.Modules.pullback ι).obj (m • (δ.K + Finsupp.single F 1) + E).divisorialSheaf) :=
      nonempty_divisorialSheaf_add_iso_pullback ι hcV hcW
        (nonempty_divisorialSheaf_nsmul_iso_pullback ι hcV hcW rK hm) rE
    have rM : Nonempty ((m • M').divisorialSheaf ≅ (Scheme.Modules.pullback ι).obj
        ((m • (δ.K + Finsupp.single F 1) + E) + D).divisorialSheaf) := by
      rw [show (m • (δ.K + Finsupp.single F 1) + E) + D = m • (δ.M + Finsupp.single F 1) by
        rw [hE]; module]
      exact nonempty_divisorialSheaf_nsmul_iso_pullback ι hcV hcW ⟨eM'⟩ hm
    obtain ⟨eD'⟩ := nonempty_divisorialSheaf_sub_iso_pullback ι hcV hcW hinvW rM rA
    refine ⟨m, hm, m • M' - (m • KF + E.restrictPrimeDivisor F), ?_,
      ⟨eD' ≪≫ (Scheme.Modules.pullback ι).mapIso eD ≪≫
        (Scheme.Modules.pullbackComp ι δ.f).app L⟩⟩
    rw [map_sub, map_add, ← Divisor.restrictPrimeDivisor_toQDivisor E F hEF, hEq,
      ← Int.cast_natCast (R := ℚ) m, Int.cast_smul_eq_zsmul,
      DivisorWithCoeffs.restrictPrimeDivisor_zsmul δ.B F hBF]
    simp only [map_nsmul, ← Nat.cast_smul_eq_nsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ, Int.cast_natCast]
    module
  have hfp' : IsProjective (ι ≫ δ.f) := by
    obtain ⟨E, h1, h2, hqc, i', hi', hcomp⟩ := δ.hfp
    exact ⟨E, h1, h2, hqc, ι ≫ i', inferInstance, by rw [Category.assoc, hcomp]⟩
  have hfs' : (ι ≫ δ.f) ≫ sX = ι ≫ δ.sV := by rw [Category.assoc, δ.hfs]
  let δ' : Datum X sX L :=
    { V := F.idealSheaf.subscheme, sV := ι ≫ δ.sV, hVsm := hFsm, f := ι ≫ δ.f, hfs := hfs',
      hfp := hfp', n := n', K := KF, hK := hKF, B := δ.B.restrictPrimeDivisor F, hB := hBsnc,
      hB0 := fun E => (hB01 E).1, hB1 := fun E => (hB01 E).2, M := M', hM := hcW M',
      hlin := hlin' }
  refine ⟨δ', ?_, fun q => ?_⟩
  · change Set.range (ι ≫ δ.f).base = δ.f.base '' F.support
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Scheme.IdealSheafData.range_subschemeι]
  · exact ⟨((Scheme.Modules.pushforward δ.f).rightDerived q).mapIso
      ((Scheme.Modules.pushforward ι).mapIso eM'.symm) ≪≫
      (Stacks.AlgebraicGeometry.ClosedImmersionRelativeLeray.rightDerivedPushforwardObjIso
        ι δ.f _ q).symm⟩

/-- A closed subset of the image of `f` missing the image of the generic point has smaller
dimension. -/
private theorem Datum.dim_lt_of_genericPoint_notMem (δ : Datum X sX L) {Z : Set X}
    (hZ : IsClosed Z) (hZf : Z ⊆ closure (Set.range δ.f.base))
    (hη : δ.f.base (genericPoint δ.V) ∉ Z) :
    topologicalKrullDim (closure Z) < δ.dim := by
  rw [hZ.closure_eq]
  have hC : IsIrreducible (closure (Set.range δ.f.base)) := by
    rw [← Set.image_univ]
    haveI : IrreducibleSpace δ.V := by
      haveI := δ.isIntegral; infer_instance
    exact ((IrreducibleSpace.isIrreducible_univ δ.V).image _
      δ.f.base.hom.continuous.continuousOn).closure
  have hηC : δ.f.base (genericPoint δ.V) ∈ closure (Set.range δ.f.base) :=
    subset_closure ⟨_, rfl⟩
  obtain ⟨d, hd⟩ := δ.exists_dim_le
  have hne : (closure (Set.range δ.f.base)).Nonempty := ⟨_, hηC⟩
  obtain ⟨n, hn⟩ : ∃ n : ℕ, δ.dim = n := by
    induction hx : δ.dim using WithBot.recBotCoe with
    | bot =>
      exfalso
      have : IsEmpty (closure (Set.range δ.f.base)) :=
        (topologicalKrullDim_eq_bot_iff_isEmpty _).1 hx
      exact this.false ⟨_, hηC⟩
    | coe e =>
      rw [hx] at hd
      induction e using ENat.recTopCoe with
      | top => exact absurd hd (by
          rw [show ((d : ℕ) : WithBot ℕ∞) = ((d : ℕ∞) : WithBot ℕ∞) from rfl,
            WithBot.coe_le_coe]
          simp)
      | coe k => exact ⟨k, rfl⟩
  rcases Z.eq_empty_or_nonempty with rfl | hZne
  · rw [show topologicalKrullDim (∅ : Set X) = ⊥ from
      (topologicalKrullDim_eq_bot_iff_isEmpty _).2 (Set.isEmpty_coe_sort.2 rfl), hn]
    exact WithBot.bot_lt_coe _
  have hinter : closure (Set.range δ.f.base) ∩ Z = Z := Set.inter_eq_right.2 hZf
  obtain ⟨h1, h2⟩ := topologicalKrullDim_inter_le_pred_of_not_subset hC hZ
    (fun h => hη (h hηC)) (by rw [hinter]; exact hZne) (le_of_eq hn)
  rw [hinter] at h2
  rw [hn]
  exact h2.trans_lt (by exact_mod_cast (by omega : n - 1 < n))

/-- **The restriction to a general hyperplane section.** When the image of `f` has dimension at
least two, for every `Q` there is a prime divisor `F` on `V`, the pullback of a general member of
a large multiple of the ample class, such that the direct images of `𝒪_V(M) ⊆ 𝒪_V(M + F)` are
injective, those of `𝒪_V(M + F)` in degree `Q` have no positive cohomology, and the direct images
of `𝒪_F(M + F)` are those of a datum over `X` whose image has smaller dimension. -/
private theorem Datum.exists_restriction (hL : Stacks.Ample.IsAmple X L) (δ : Datum X sX L)
    (hd : 2 ≤ δ.dim) (Q : ℕ) :
    ∃ (F : MMP.Mori.PrimeDivisor δ.V) (δ' : Datum X sX L), δ'.dim < δ.dim ∧
      (∀ q, Mono (((Scheme.Modules.pushforward δ.f).rightDerived q).map
        (Divisor.divisorialSheafInclusion (le_add_of_nonneg_right
          (Finsupp.single_nonneg.2 zero_le_one) : δ.M ≤ δ.M + Finsupp.single F 1)))) ∧
      (∀ p, 0 < p → IsZero (((sections X).rightDerived p).obj
        (((Scheme.Modules.pushforward δ.f).rightDerived Q).obj
          (δ.M + Finsupp.single F 1).divisorialSheaf))) ∧
      ∀ q, Nonempty ((((Scheme.Modules.pushforward δ.f).rightDerived q).obj
        ((Scheme.Modules.pullback F.idealSheaf.subschemeι ⋙
          Scheme.Modules.pushforward F.idealSheaf.subschemeι).obj
            (δ.M + Finsupp.single F 1).divisorialSheaf)) ≅
        ((Scheme.Modules.pushforward δ'.f).rightDerived q).obj δ'.M.divisorialSheaf) := by
  obtain ⟨d₀, hd₀⟩ := δ.exists_serre hL Q
  obtain ⟨d, hdd, F, ⟨eF⟩, hFsm, hFB, hsnc, A, hAc, hFA, hFS⟩ := δ.exists_hyperplane hL hd d₀
  have hFA' : ∀ y ∈ F.support, δ.f.base y ∈ A := fun y hy => by
    rw [← Set.mem_preimage, ← hFA]; exact hy
  have hsub : ∀ S : Set δ.V, δ.f.base '' S ⊆ A → S ⊆ F.support := fun S hS z hz => by
    rw [hFA]; exact hS ⟨z, hz, rfl⟩
  have huniv : MMP.Fourfold.IsSNCStratum δ.B.roundDown Set.univ := by
    haveI : IrreducibleSpace δ.V := by haveI := δ.isIntegral; infer_instance
    exact ⟨∅, Finset.empty_subset _, ⟨IrreducibleSpace.isIrreducible_univ _, by simp⟩,
      fun T _ _ => Set.subset_univ T⟩
  obtain ⟨δ', hδ'f, hiso⟩ := δ.exists_restrict F hFsm hFB hsnc
  haveI : IsProper δ.f := δ.hfp.isProper
  have hFcl : IsClosed (δ.f.base '' F.support) :=
    δ.f.isClosedMap _ F.idealSheaf.support.isClosed
  have hηF : δ.f.base (genericPoint δ.V) ∉ δ.f.base '' F.support := by
    rintro ⟨y, hy, hyη⟩
    apply hFS _ huniv
    apply hsub
    have hηA : δ.f.base (genericPoint δ.V) ∈ A := hyη ▸ hFA' y hy
    rintro _ ⟨z, -, rfl⟩
    have hz : z ∈ closure {genericPoint δ.V} := by
      rw [(genericPoint_spec δ.V).def]; trivial
    have := image_closure_subset_closure_image δ.f.base.hom.continuous ⟨z, hz, rfl⟩
    rw [Set.image_singleton] at this
    exact closure_minimal (Set.singleton_subset_iff.2 hηA) hAc this
  refine ⟨F, δ', ?_, fun q => δ.mono_of_avoid hL F (fun S hS x hx y hy hyx =>
      hFS S hS (hsub S (hx ▸ closure_minimal
        (Set.singleton_subset_iff.2 (hyx ▸ hFA' y hy)) hAc))) q,
    fun p hp => (hd₀ d hdd Q le_rfl p hp).of_iso (((sections X).rightDerived p).mapIso
      (((Scheme.Modules.pushforward δ.f).rightDerived Q).mapIso
        (δ.twistIso (δ.isCartier _) eF))), hiso⟩
  have h := δ.dim_lt_of_genericPoint_notMem hFcl
    (fun y ⟨x, _, hx⟩ => hx ▸ subset_closure ⟨x, rfl⟩)
    hηF
  rw [← hδ'f] at h
  exact h

/-! ### The induction -/

/-- **The columns `p ≥ 2`.** -/
private theorem Datum.isZero_coh_of_two_le (hL : Stacks.Ample.IsAmple X L) (δ : Datum X sX L)
    (ih : ∀ δ' : Datum X sX L, δ'.dim < δ.dim → ∀ p q, 0 < p → IsZero (δ'.coh p q))
    (p q : ℕ) (hp : 2 ≤ p) : IsZero (δ.coh p q) := by
  by_cases hd : 2 ≤ δ.dim
  · obtain ⟨F, δ', hδ', hmono, hserre, he⟩ := δ.exists_restriction hL hd q
    obtain ⟨hz, hS⟩ := Divisor.IsCartier.shortExact_divisorialSheafInclusion_restriction δ.sV
      (inferInstance : MMP.Mori.IsVariety ℂ δ.sV) δ.hVsm F δ.hM
    have hSq := shortExact_rightDerived_pushforward δ.f hS q (hmono q) (hmono (q + 1))
    obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
    obtain ⟨e⟩ := he q
    exact isZero_rightDerived_sections_X₁ hSq p'
      ((ih δ' hδ' p' q (by omega)).of_iso (((sections X).rightDerived p').mapIso e))
      (hserre (p' + 1) (by omega))
  · refine δ.isZero_coh_of_dim_lt p q (by omega) (lt_of_lt_of_le (not_le.1 hd) ?_)
    exact_mod_cast hp

/-- **The column `p = 1`.** -/
private theorem Datum.isZero_coh_one (hL : Stacks.Ample.IsAmple X L) (δ : Datum X sX L)
    (h2 : ∀ p q, 2 ≤ p → IsZero (δ.coh p q)) (q : ℕ) : IsZero (δ.coh 1 q) := by
  obtain ⟨A, hA, hserre, hinj⟩ := δ.exists_twist hL q
  exact isZero_rightDerived_one_rightDerived_pushforward δ.f _ q (fun q' _ p hp => h2 p q' hp)
    hserre (hinj (q + 1))

/-- **The induction on the dimension of the image.** -/
private theorem main (hL : Stacks.Ample.IsAmple X L) (d : ℕ) :
    ∀ δ : Datum X sX L, δ.dim ≤ d → ∀ p q, 0 < p → IsZero (δ.coh p q) := by
  induction d using Nat.strong_induction_on with
  | _ d ihd =>
  intro δ hδ
  have ih : ∀ δ' : Datum X sX L, δ'.dim < δ.dim → ∀ p q, 0 < p → IsZero (δ'.coh p q) := by
    intro δ' hδ'
    have hlt : δ'.dim < (d : WithBot ℕ∞) := lt_of_lt_of_le hδ' hδ
    induction hx : δ'.dim using WithBot.recBotCoe with
    | bot =>
      exact fun p q hp =>
        δ'.isZero_coh_of_dim_lt p q hp (by rw [hx]; exact WithBot.bot_lt_coe _)
    | coe e =>
      induction e using ENat.recTopCoe with
      | top => rw [hx] at hlt; exact absurd hlt (by simp)
      | coe k =>
        rw [hx] at hlt
        exact ihd k (by exact_mod_cast hlt) δ' hx.le
  have h2 := δ.isZero_coh_of_two_le hL ih
  intro p q hp
  obtain rfl | hp1 : p = 1 ∨ 2 ≤ p := by omega
  · exact δ.isZero_coh_one hL h2 q
  · exact h2 p q hp1

end MMP.FourfoldProofs.MmpLcBpfSncDirectImageVanishingProof

end

section

/-!
# Vanishing of cohomology of higher direct images of snc adjoint sheaves

Let `f : V ⟶ X` be a projective morphism of projective varieties over `ℂ`, with `V` smooth,
let `K_V` be a canonical divisor of `V`, and let `B` be a `ℚ`-divisor with simple normal
crossing support and coefficients in `[0, 1]`. If `M` is a Cartier divisor with
`M - (K_V + B) ∼_ℚ f^*H` for an ample `ℚ`-Cartier divisor `H` on `X`, then
`H^p(X, R^q f_* 𝒪_V(M)) = 0` for every `p > 0` and every `q`. This is Kollár's vanishing theorem
in Ambro's and Fujino's form for snc pairs.

## Main results

* `MMP.Mori.subsingleton_cohomologyOverField_rightDerived_pushforward_divisorialSheaf`:
  `H^p(X, R^q f_* 𝒪_V(M)) = 0` for `p > 0`.

## Implementation notes

* `V` and `X` carry structure morphisms `sV`, `sX` to `Spec ℂ`, and `f ≫ sX = sV` says that `f`
  is a morphism over `ℂ`.
* `X` is an arbitrary projective variety, not necessarily normal, so the ample `ℚ`-Cartier
  divisor `H` is given through an ample invertible sheaf `L` on `X` (`Stacks.Ample.IsAmple`),
  standing for `𝒪_X(mH)` with `m > 0` and `mH` Cartier. The relation
  `M - (K_V + B) ∼_ℚ f^*H` then says: for some `m > 0`, `m(M - (K_V + B))` is an integral
  divisor `D` with `𝒪_V(D) ≅ f^*L`. Clearing denominators and passing to a power of `L` shows
  this is equivalent to the source's formulation whenever `H` is a `ℚ`-Cartier divisor.
* `R^q f_*` is the `q`-th right derived functor of `Scheme.Modules.pushforward f`, `𝒪_V(M)` is
  `MMP.Mori.Divisor.divisorialSheaf`, and `H^p(X, -)` is `AlgebraicGeometry.cohomologyOverField`
  over `sX`, a `ℂ`-vector space.

## References

* [O. Fujino, *Fundamental theorems for the log minimal model program*][Fujino2011],
  Theorem 6.3
* [F. Ambro, *Quasi-log varieties*][Ambro2003]
* [J. Kollár, *Higher direct images of dualizing sheaves I*][Kollar1986]
-/

public section

open CategoryTheory AlgebraicGeometry

namespace MMP.Mori

/-- **Kollár vanishing for snc pairs** (Kollár, Ambro, Fujino). Let `f : V ⟶ X` be a projective
morphism of projective varieties over `ℂ`,
with `V` smooth of dimension `n` and canonical divisor `K`, and let `B` be a `ℚ`-divisor with snc
support and coefficients in `[0, 1]`. Let `L` be an ample invertible sheaf on `X`. If `M` is a
Cartier divisor such that for some `m > 0` the divisor `m(M - (K + B))` is integral with
associated sheaf isomorphic to `f^*L` (that is, `M - (K + B) ∼_ℚ f^*H` for the ample
`ℚ`-Cartier divisor `H = L / m`), then `H^p(X, R^q f_* 𝒪_V(M)) = 0` for all `p > 0` and all
`q`. -/
@[mmp "thm_mmp_lc_bpf_snc_direct_image_vanishing"]
public theorem subsingleton_cohomologyOverField_rightDerived_pushforward_divisorialSheaf
    {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) [IsProjectiveVariety ℂ sX]
    {V : Scheme.{0}} (sV : V ⟶ Spec (.of ℂ)) [IsProjectiveVariety ℂ sV]
    (hVsm : IsSmoothScheme sV) [IsLocallyNoetherian V] [IsNormal V] (f : V ⟶ X)
    (hfs : f ≫ sX = sV) (hfp : IsProjective f)
    {n : ℕ} (K : Divisor V) (hK : K.IsCanonicalDivisor sV n)
    (B : QDivisor V) (hB : B.IsSNC sV) (hB0 : ∀ E, 0 ≤ B E) (hB1 : ∀ E, B E ≤ 1)
    (M : Divisor V) (hM : M.IsCartier)
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hL : Stacks.Ample.IsAmple X L)
    (hlin : ∃ m : ℕ, 0 < m ∧ ∃ D : Divisor V,
      Divisor.toQDivisor D = (m : ℚ) • (Divisor.toQDivisor M - (Divisor.toQDivisor K + B)) ∧
      Nonempty (D.divisorialSheaf ≅ (Scheme.Modules.pullback f).obj L))
    (p q : ℕ) (hp : 0 < p) :
    Subsingleton (cohomologyOverField ℂ sX
      (((Scheme.Modules.pushforward f).rightDerived q).obj M.divisorialSheaf) p) := by
  let δ : MMP.FourfoldProofs.MmpLcBpfSncDirectImageVanishingProof.Datum X sX L :=
    { V := V, sV := sV, hVsm := hVsm, f := f, hfs := hfs, hfp := hfp, n := n, K := K, hK := hK,
      B := B, hB := hB, hB0 := hB0, hB1 := hB1, M := M, hM := hM, hlin := hlin }
  obtain ⟨d, hd⟩ := δ.exists_dim_le
  have h := ModuleCat.subsingleton_of_isZero
    (MMP.FourfoldProofs.MmpLcBpfSncDirectImageVanishingProof.main hL d δ hd p q hp)
  exact h

end MMP.Mori

end
