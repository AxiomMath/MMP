module
public import MMP.AlgebraicGeometry.Singularities.CyclicCover.Action
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LargeModuleUniverse
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SitePointStalkAdditive
public import StacksFrontier.AlgebraicGeometry.Cohomology.HypercoveringModuleComparison
public import StacksFrontier.AlgebraicGeometry.CurveEulerBridge.Basic
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.TotalSpaceBaseChange
public import StacksFrontier.AlgebraicGeometry.Duality.AffinePushforwardQcohExact
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentThree.DerivedChowFourierMukai
public import StacksFrontier.AlgebraicGeometry.ProjectionFormula.HigherDirectImage
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.HyperplaneTwistSequence
public import StacksFrontier.AlgebraicGeometry.ProperAmpleCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.ChowStalk
public import StacksFrontier.AlgebraicGeometry.RelativeProjBridge.RestrictOpen
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.TorsionInFirstCohomology
public import StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiSliceComponentModule
public import StacksFrontier.AlgebraicGeometry.TensorSheafSpellingIso.Basic

/-!
# Twisted vanishing of higher direct images; cyclic covers off the zero scheme

This file proves two facts used in the study of cyclic covers and vanishing theorems.

**Higher direct images detected by twisted cohomology.** Let `f : Y ⟶ X` be a proper morphism,
where `X` is proper over a field `k`, let `ℱ` be a coherent sheaf on `Y` and `ℋ` an ample
invertible sheaf on `X`. If `H^j(Y, ℱ ⊗ (f^*ℋ)^{⊗ r}) = 0` for all sufficiently large `r`, then
`R^j f_* ℱ = 0`. For `r ≫ 0` the Leray spectral sequence degenerates: by the projection formula
`R^q f_*(ℱ ⊗ f^*ℋ^r) ≅ R^q f_* ℱ ⊗ ℋ^r` and Serre vanishing for the finitely many coherent
sheaves `R^q f_* ℱ`, one gets `H^j(Y, ℱ ⊗ f^*ℋ^r) ≅ H^0(X, R^j f_* ℱ ⊗ ℋ^r)`; Serre's global
generation then forces `R^j f_* ℱ = 0`.

**The ramified cyclic cover is unramified off the zero scheme.** Let `N = L⁻¹` be a line bundle
on a scheme `X`, `m` a natural number and `σ = ⟨·, s⟩ : Symᵐ(N) ⟶ 𝒪_X` for a section
`s ∈ H⁰(X, Lᵐ)`, with zero scheme `D = (s = 0)`. Over an open `U ⊆ X ∖ D` the section `s`
generates `Lᵐ`, so `σ|_U` is an isomorphism `ψ : L⁻ᵐ|_U ≅ 𝒪_U`, and the part `p⁻¹(U)` of the
cyclic cover `p : Z ⟶ X` lying over `U` is the unramified cyclic cover attached to `ψ`, as
`U`-schemes and compatibly with the automorphisms `α_ζ` given by the `m`-th roots of unity `ζ`.

## Main results

* `MMP.Mori.isZero_rightDerived_pushforward_of_eventually_isZero_cohomology_twist`
* `MMP.Mori.cyclicCover_restrict_of_le_compl_zeroScheme`

## Implementation notes

A scheme proper over `k` carrying an ample invertible sheaf is projective over `k`, so the
hypothesis "`X` projective" is expressed as properness of `X ⟶ Spec k` together with the
ampleness of `ℋ`. Cohomology `H^j(Y, -)` is the `j`-th right derived functor of global sections
on `𝒪_Y`-modules, and `R^j f_*` the `j`-th right derived functor of `Scheme.Modules.pushforward f`.
The twist `ℱ ⊗ (f^*ℋ)^{⊗ r}` is `Stacks.AlgebraicGeometry.HyperplaneTwistSequence.twistModule`
of `ℱ` by the pullback `Stacks.AmpleLocallyClosed.pullbackModule f ℋ`. The Leray degeneration
is proved without a spectral sequence, by dimension shifting along `0 ⟶ M ⟶ I ⟶ I/M ⟶ 0`
for `Γ(Y, -) = Γ(X, -) ∘ f_*`.

The source states the cyclic cover result for `U = X ∖ D`; it is stated for every open
`U ⊆ X ∖ D`. The restriction `N|_U` is given as an invertible `𝒪_U`-module `N'` with an
isomorphism `e : N' ≅ N|_U`, and the restriction `ψ` of `σ` is characterised on the sections
`t₁ ⋯ tₘ` of `Symᵐ(N')`, which generate it: `ψ(t₁ ⋯ tₘ) = σ(e(t₁) ⋯ e(tₘ))|_U`.

## References

* [KM98] J. Kollár, S. Mori, *Birational geometry of algebraic varieties*, Proposition 2.69
  and 2.50.
-/

universe u

/-! ## Higher direct images detected by twisted cohomology -/

section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

open scoped Stacks.SmallDerivedModel
open Stacks.Ample (IsAmple IsInvertibleModule)
open Stacks.AmpleLocallyClosed (pullbackModule)
open Stacks.AlgebraicGeometry.HyperplaneTwistSequence (twistModule tensorRightModules)

namespace MMP.Mori.HigherDirectImageTwisted

/-- On a scheme, a module with no global sections over `⊤` has a subsingleton type of
compatible families of sections. -/
private theorem subsingleton_sections_of_isZero_evaluation_top (X : Scheme.{u}) (M : X.Modules)
    (h : IsZero ((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).obj M)) :
    Subsingleton M.sections := by
  refine ⟨fun s t => ?_⟩
  apply Subtype.ext
  funext U
  rw [← s.2 (homOfLE (le_top : U.unop ≤ ⊤)).op, ← t.2 (homOfLE (le_top : U.unop ≤ ⊤)).op]
  congr 1
  exact @Subsingleton.elim _ (ModuleCat.subsingleton_of_isZero h) _ _

/-- A module generated by global sections, all of which vanish, is zero. -/
private theorem isZero_of_generatingSections_of_subsingleton (X : Scheme.{u}) (M : X.Modules)
    (σ : M.GeneratingSections) (h : Subsingleton M.sections) : IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  generalize hz : (0 : M ⟶ M) = z
  have he := σ.epi
  refine he.left_cancellation _ _ ?_
  refine (SheafOfModules.freeHomEquiv_symm_comp σ.s (𝟙 M)).trans
    (Eq.trans ?_ (SheafOfModules.freeHomEquiv_symm_comp σ.s z).symm)
  congr 1
  funext i
  exact Subsingleton.elim _ _

/-- Twisting by an invertible module reflects vanishing. -/
private theorem isZero_of_isZero_twistModule (X : Scheme.{u}) (L : X.Modules)
    [IsInvertibleModule X L] (G : X.Modules) (n : ℤ) (h : IsZero (twistModule X L G n)) :
    IsZero G := by
  haveI : (tensorRightModules X (Stacks.Ample.tensorPowModule X L n)).IsEquivalence :=
    Stacks.RelativeVeryAmple.isEquivalence_tensorRightFunctor_of_isInvertibleModule X _
  rw [IsZero.iff_id_eq_zero]
  apply (tensorRightModules X (Stacks.Ample.tensorPowModule X L n)).map_injective
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
  exact h.eq_of_src _ _

/-- Serre's global generation, read as a vanishing criterion: for a coherent module `𝒢` on a
scheme with an ample invertible module `ℒ`, if `Γ(X, 𝒢 ⊗ ℒ^{⊗ r}) = 0` for some large `r`, then
`𝒢 = 0`. -/
private theorem eventually_isZero_of_isZero_sections_twistModule (X : Scheme.{u}) (L : X.Modules)
    [IsInvertibleModule X L] (hL : IsAmple X L) (G : X.Modules) [G.IsCoherent] :
    ∀ᶠ r : ℕ in Filter.atTop,
      IsZero ((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).obj
        (twistModule X L G r)) → IsZero G := by
  obtain ⟨n₀, hn⟩ := Stacks.AmpleLocalGeneration.isEventuallyGloballyGenerated_of_isAmple L hL G
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent G).1
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent G).2
  refine Filter.eventually_atTop.2 ⟨n₀.toNat, fun r hr h0 => ?_⟩
  obtain ⟨σ, -⟩ := hn r (by omega)
  let e := Stacks.TensorSheafSpellingIso.monoidalTensorIso X G (Stacks.Ample.tensorPowModule X L r)
  have h1 := h0.of_iso ((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).mapIso e)
  have h2 := isZero_of_generatingSections_of_subsingleton X _ σ
    (subsingleton_sections_of_isZero_evaluation_top X _ h1)
  exact isZero_of_isZero_twistModule X L G r (h2.of_iso e.symm)

/-- The higher direct images of a coherent module under a proper morphism to a scheme proper
over a field are coherent. -/
private theorem isCoherent_rightDerived_pushforward (k : Type u) [Field k] {X Y : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) [IsProper pX] (f : Y ⟶ X) [IsProper f] (F : Y.Modules)
    [F.IsCoherent] (j : ℕ) :
    (((Scheme.Modules.pushforward f).rightDerived j).obj F).IsCoherent :=
  Stacks.AlgebraicGeometry.RelativeSerreVanishing.isCoherent_of_iso
    ((@Stacks.DerivedIndexing.rightDerivedIso _ _ _ _ _ _ _ (Scheme.Modules.pushforward f) _
      (HasDerivedCategory.standard _) (HasDerivedCategory.standard _) j).app F).symm
    (ProperCoherenceWitness.higherDirectImageIsCoherent Y X f
      (Stacks.AlgebraicGeometry.CurveEulerBridge.isLocallyNoetherian_of_isProper_over_field k pX)
      inferInstance F inferInstance j)

section Abstract

variable {A B C : Type*} [Category* A] [Category* B] [Category* C] [Abelian A] [Abelian B]
    [Abelian C] [EnoughInjectives A]

private noncomputable def delta (F : A ⥤ B) [F.Additive] : DeltaFunctor A B :=
  letI := HasDerivedCategory.standard A
  letI := HasDerivedCategory.standard B
  Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives F

/-- The connecting morphism `R^n F(X₃) ⟶ R^{n+1} F(X₁)` of a short exact sequence. -/
private noncomputable def dlt (F : A ⥤ B) [F.Additive] {S : ShortComplex A} (hS : S.ShortExact)
    (n : ℕ) : (F.rightDerived n).obj S.X₃ ⟶ (F.rightDerived (n + 1)).obj S.X₁ :=
  (delta F).δ hS n

private theorem map_g_dlt (F : A ⥤ B) [F.Additive] {S : ShortComplex A} (hS : S.ShortExact)
    (n : ℕ) : (F.rightDerived n).map S.g ≫ dlt F hS n = 0 :=
  (delta F).map_g_δ hS n

private theorem dlt_map_f (F : A ⥤ B) [F.Additive] {S : ShortComplex A} (hS : S.ShortExact)
    (n : ℕ) : dlt F hS n ≫ (F.rightDerived (n + 1)).map S.f = 0 :=
  (delta F).δ_map_f hS n

private theorem exact_dlt₁ (F : A ⥤ B) [F.Additive] {S : ShortComplex A} (hS : S.ShortExact)
    (n : ℕ) : (ShortComplex.mk _ _ (map_g_dlt F hS n)).Exact :=
  (delta F).exact_δ₁ hS n

private theorem exact_dlt₂ (F : A ⥤ B) [F.Additive] {S : ShortComplex A} (hS : S.ShortExact)
    (n : ℕ) : (ShortComplex.mk _ _ (dlt_map_f F hS n)).Exact :=
  (delta F).exact_δ₂ hS n

private theorem exact_map_rightDerived (F : A ⥤ B) [F.Additive] {S : ShortComplex A}
    (hS : S.ShortExact) (n : ℕ) : (S.map (F.rightDerived n)).Exact :=
  (delta F).exact_map hS n

private theorem mono_rightDerived_zero_map_f (F : A ⥤ B) [F.Additive] {S : ShortComplex A}
    (hS : S.ShortExact) : Mono ((F.rightDerived 0).map S.f) :=
  (delta F).mono_map_f hS

/-- In a short exact sequence, `R^p` vanishes at the quotient once it vanishes at the middle
term in degree `p` and at the subobject in degree `p + 1`. -/
private theorem isZero_rightDerived_X₃ (F : A ⥤ B) [F.Additive] {S : ShortComplex A}
    (hS : S.ShortExact) (p : ℕ) (h₂ : IsZero ((F.rightDerived p).obj S.X₂))
    (h₁ : IsZero ((F.rightDerived (p + 1)).obj S.X₁)) :
    IsZero ((F.rightDerived p).obj S.X₃) :=
  (exact_dlt₁ F hS p).isZero_X₂ (h₂.eq_of_src _ _) (h₁.eq_of_tgt _ _)

/-- In a short exact sequence, `R^p` vanishes at the middle term once it vanishes at both ends. -/
private theorem isZero_rightDerived_X₂ (F : A ⥤ B) [F.Additive] {S : ShortComplex A}
    (hS : S.ShortExact) (p : ℕ) (h₁ : IsZero ((F.rightDerived p).obj S.X₁))
    (h₃ : IsZero ((F.rightDerived p).obj S.X₃)) :
    IsZero ((F.rightDerived p).obj S.X₂) :=
  (exact_map_rightDerived F hS p).isZero_X₂ (h₁.eq_of_src _ _) (h₃.eq_of_tgt _ _)

/-- The connecting isomorphism `R^n(X₃) ≅ R^{n+1}(X₁)` when the middle term is acyclic in
degrees `n` and `n + 1`. -/
private noncomputable def deltaIso (F : A ⥤ B) [F.Additive] {S : ShortComplex A}
    (hS : S.ShortExact) (n : ℕ) (h₁ : IsZero ((F.rightDerived n).obj S.X₂))
    (h₂ : IsZero ((F.rightDerived (n + 1)).obj S.X₂)) :
    (F.rightDerived n).obj S.X₃ ≅ (F.rightDerived (n + 1)).obj S.X₁ :=
  haveI : Mono (dlt F hS n) := (exact_dlt₁ F hS n).mono_g (h₁.eq_of_src _ _)
  haveI : Epi (dlt F hS n) := (exact_dlt₂ F hS n).epi_f (h₂.eq_of_tgt _ _)
  haveI : IsIso (dlt F hS n) := isIso_of_mono_of_epi _
  asIso (dlt F hS n)

/-- A left exact functor maps `g` to an epimorphism when its `R⁰` does. -/
private theorem epi_map_of_epi_rightDerived_zero (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] {X Y : A} (g : X ⟶ Y) (h : Epi ((F.rightDerived 0).map g)) :
    Epi (F.map g) := by
  rw [← NatIso.naturality_1 F.rightDerivedZeroIsoSelf g]
  infer_instance

/-- The second map of a short exact sequence stays epi under a left exact functor whose first
derived functor vanishes at the subobject. -/
private theorem epi_map_g (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    {S : ShortComplex A} (hS : S.ShortExact) (h : IsZero ((F.rightDerived 1).obj S.X₁)) :
    Epi (F.map S.g) :=
  epi_map_of_epi_rightDerived_zero F S.g ((exact_dlt₁ F hS 0).epi_f (h.eq_of_tgt _ _))

section Pair

variable (F : A ⥤ B) [F.Additive] {S : ShortComplex A} (hS : S.ShortExact)

/-- `0 ⟶ R⁰F(X₁) ⟶ R⁰F(X₂) ⟶ Q ⟶ 0`, with `Q` the cokernel. -/
private noncomputable abbrev pairFst : ShortComplex B :=
  ShortComplex.mk ((F.rightDerived 0).map S.f) (cokernel.π _) (cokernel.condition _)

include hS in
private theorem pairFst_shortExact : (pairFst F (S := S)).ShortExact :=
  haveI : Mono ((F.rightDerived 0).map S.f) := mono_rightDerived_zero_map_f F hS
  ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _))
    inferInstance inferInstance

/-- `0 ⟶ Q ⟶ R⁰F(X₃) ⟶ R¹F(X₁) ⟶ 0`. -/
private noncomputable abbrev pairSnd : ShortComplex B :=
  ShortComplex.mk
    (cokernel.desc ((F.rightDerived 0).map S.f) ((F.rightDerived 0).map S.g)
      (by rw [← Functor.map_comp, S.zero, Functor.map_zero]))
    (dlt F hS 0)
    ((cancel_epi (cokernel.π ((F.rightDerived 0).map S.f))).1 (by
      rw [comp_zero, ← Category.assoc, cokernel.π_desc]
      exact map_g_dlt F hS 0))

private theorem pairSnd_shortExact (hI : IsZero ((F.rightDerived 1).obj S.X₂)) :
    (pairSnd F hS).ShortExact := by
  let φ : ShortComplex.mk _ _ (map_g_dlt F hS 0) ⟶ pairSnd F hS :=
    { τ₁ := cokernel.π _
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by simp
      comm₂₃ := (Category.id_comp _).trans (Category.comp_id _).symm }
  have : Epi φ.τ₁ := by dsimp [φ]; infer_instance
  have : IsIso φ.τ₂ := by dsimp [φ]; infer_instance
  have : Mono φ.τ₃ := by dsimp [φ]; infer_instance
  have hm : Mono (pairSnd F hS).f := (exact_map_rightDerived F hS 0).mono_cokernelDesc
  exact ShortComplex.ShortExact.mk'
    ((ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 (exact_dlt₁ F hS 0)) hm
    ((exact_dlt₂ F hS 0).epi_f (hI.eq_of_tgt _ _))

end Pair

section Collapse

variable [EnoughInjectives B] (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteLimits G]

/-- The injective presentation `0 ⟶ M ⟶ I ⟶ I/M ⟶ 0`. -/
private noncomputable abbrev presS (M : A) : ShortComplex A :=
  ShortComplex.mk (Injective.ι M) (cokernel.π _) (cokernel.condition _)

private theorem presS_shortExact (M : A) : (presS M).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _))
    inferInstance inferInstance

omit [PreservesFiniteLimits G] in
private theorem isZero_rightDerived_pairFst_X₃
    (hFG : ∀ I : A, Injective I → ∀ p : ℕ, 0 < p → IsZero ((G.rightDerived p).obj (F.obj I)))
    (M : A) (h0 : ∀ p : ℕ, 0 < p → IsZero ((G.rightDerived p).obj ((F.rightDerived 0).obj M)))
    (p : ℕ) (hp : 0 < p) :
    IsZero ((G.rightDerived p).obj (pairFst F (S := presS M)).X₃) := by
  refine isZero_rightDerived_X₃ G (pairFst_shortExact F (presS_shortExact M)) p ?_ (h0 _ (by omega))
  exact (hFG _ inferInstance p hp).of_iso
    ((G.rightDerived p).mapIso ((F.rightDerivedZeroIsoSelf).app (Injective.under M)))

omit [PreservesFiniteLimits G] in
private theorem isZero_rightDerived_presS_X₃
    (hFG : ∀ I : A, Injective I → ∀ p : ℕ, 0 < p → IsZero ((G.rightDerived p).obj (F.obj I)))
    (M : A) (h0 : ∀ p : ℕ, 0 < p → IsZero ((G.rightDerived p).obj ((F.rightDerived 0).obj M)))
    (h1 : ∀ p : ℕ, 0 < p → IsZero ((G.rightDerived p).obj ((F.rightDerived 1).obj M)))
    (p : ℕ) (hp : 0 < p) :
    IsZero ((G.rightDerived p).obj ((F.rightDerived 0).obj (presS M).X₃)) :=
  isZero_rightDerived_X₂ G (pairSnd_shortExact F (presS_shortExact M)
      (Functor.isZero_rightDerived_obj_injective_succ F 0 _)) p
    (isZero_rightDerived_pairFst_X₃ F G hFG M h0 p hp) (h1 p hp)

private theorem isZero_map_rightDerived_one
    (hFG : ∀ I : A, Injective I → ∀ p : ℕ, 0 < p → IsZero ((G.rightDerived p).obj (F.obj I)))
    (M : A) (h0 : ∀ p : ℕ, 0 < p → IsZero ((G.rightDerived p).obj ((F.rightDerived 0).obj M)))
    (h : IsZero (((F ⋙ G).rightDerived 1).obj M)) :
    IsZero (G.obj ((F.rightDerived 1).obj M)) := by
  have hS := presS_shortExact M
  have hI : IsZero ((F.rightDerived 1).obj (presS M).X₂) :=
    Functor.isZero_rightDerived_obj_injective_succ F 0 _
  have hT := pairSnd_shortExact F hS hI
  -- `Φ(I) ⟶ Φ(I/M)` is epi
  have h1 : Epi ((F ⋙ G).map (presS M).g) := epi_map_g (F ⋙ G) hS h
  have h2 : Epi (G.map ((F.rightDerived 0).map (presS M).g)) := by
    rw [← NatIso.naturality_2 F.rightDerivedZeroIsoSelf, G.map_comp, G.map_comp]
    have : Epi (G.map (F.map (presS M).g)) := h1
    infer_instance
  have h3 : Epi (G.map (pairSnd F hS).f) := by
    have hfac : (F.rightDerived 0).map (presS M).g =
        cokernel.π _ ≫ (pairSnd F hS).f := (cokernel.π_desc _ _ _).symm
    rw [hfac, G.map_comp] at h2
    exact epi_of_epi (G.map (cokernel.π _)) _
  have h4 : Epi (G.map (pairSnd F hS).g) :=
    epi_map_g G hT (isZero_rightDerived_pairFst_X₃ F G hFG M h0 1 one_pos)
  have h5 : G.map (pairSnd F hS).g = 0 := by
    rw [← cancel_epi (G.map (pairSnd F hS).f), ← G.map_comp, (pairSnd F hS).zero, G.map_zero,
      comp_zero]
  exact IsZero.of_epi_eq_zero _ h5

/-- **The degenerate Leray sequence, in vanishing form.** Let `F` and `G` be left exact, with `F`
carrying injectives to `G`-acyclic objects. If `R^q F(M)` is `G`-acyclic for every `q ≤ j`, then
`R^j(G ∘ F)(M) = 0` forces `G(R^j F(M)) = 0`. -/
private theorem isZero_map_rightDerived_of_isZero_rightDerived_comp
    (hFG : ∀ I : A, Injective I → ∀ p : ℕ, 0 < p → IsZero ((G.rightDerived p).obj (F.obj I))) :
    ∀ (j : ℕ) (M : A),
      (∀ q ≤ j, ∀ p : ℕ, 0 < p → IsZero ((G.rightDerived p).obj ((F.rightDerived q).obj M))) →
      IsZero (((F ⋙ G).rightDerived j).obj M) → IsZero (G.obj ((F.rightDerived j).obj M))
  | 0, M, _, h =>
    (h.of_iso ((F ⋙ G).rightDerivedZeroIsoSelf.app M).symm).of_iso
      (G.mapIso ((F.rightDerivedZeroIsoSelf).app M))
  | 1, M, hM, h => isZero_map_rightDerived_one F G hFG M (hM 0 (by omega)) h
  | k + 2, M, hM, h => by
    have hS := presS_shortExact M
    have hC : ∀ q ≤ k + 1, ∀ p : ℕ, 0 < p →
        IsZero ((G.rightDerived p).obj ((F.rightDerived q).obj (presS M).X₃)) := by
      intro q hq p hp
      rcases q with _ | q
      · exact isZero_rightDerived_presS_X₃ F G hFG M (hM 0 (by omega)) (hM 1 (by omega)) p hp
      · exact (hM (q + 2) (by omega) p hp).of_iso ((G.rightDerived p).mapIso
          (deltaIso F hS (q + 1) (Functor.isZero_rightDerived_obj_injective_succ F q _)
            (Functor.isZero_rightDerived_obj_injective_succ F (q + 1) _)))
    have hΦ : IsZero (((F ⋙ G).rightDerived (k + 1)).obj (presS M).X₃) :=
      h.of_iso (deltaIso (F ⋙ G) hS (k + 1)
        (Functor.isZero_rightDerived_obj_injective_succ _ k _)
        (Functor.isZero_rightDerived_obj_injective_succ _ (k + 1) _))
    exact (isZero_map_rightDerived_of_isZero_rightDerived_comp hFG (k + 1) _ hC hΦ).of_iso
      (G.mapIso (deltaIso F hS (k + 1) (Functor.isZero_rightDerived_obj_injective_succ F k _)
        (Functor.isZero_rightDerived_obj_injective_succ F (k + 1) _))).symm

end Collapse

end Abstract

section Concrete

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- The direct image of an injective module has no higher cohomology. -/
private theorem isZero_Hgroup_pushforward_of_injective {X Y : Scheme.{u}} (f : Y ⟶ X)
    (I : Y.Modules) (hI : Injective I) (p : ℕ) (hp : 0 < p) :
    IsZero (Hgroup X.ringCatSheaf ⊤ p ((Scheme.Modules.pushforward f).obj I)) := by
  have h := @Stacks.Cohomology.PushforwardAcyclic.pushforward_injective_rightAcyclic _ _
    f.toLRSHom.toShHom I hI ⊤
  have h' := (@Stacks.Cohomology.rightAcyclic_iff_isZero_rightDerived _ _ _ _ _ _
    (HasDerivedCategory.standard _) (HasDerivedCategory.standard _) _ _ _ _ _ _).1 h p hp
  exact (Stacks.Cohomology.CechAcyclic.isZero_rightDerived_evaluation_iff_isZero_Hgroup
    (O := X.ringCatSheaf) ⊤ p ((Scheme.Modules.pushforward f).obj I)).1 h'

/-- Global sections `Γ(X, -)` of the underlying abelian sheaf, on `X.Modules`. -/
private noncomputable abbrev globalSec (X : Scheme.{u}) : X.Modules ⥤ AddCommGrpCat.{u} :=
  secF X.ringCatSheaf ⊤

private instance (X : Scheme.{u}) : (globalSec X).Additive :=
  inferInstanceAs (secF X.ringCatSheaf ⊤).Additive
private instance (X : Scheme.{u}) : PreservesFiniteLimits (globalSec X) :=
  inferInstanceAs (PreservesFiniteLimits (secF X.ringCatSheaf ⊤))

/-- The degenerate Leray sequence for `Γ(Y, -) = Γ(X, f_* -)`. -/
private theorem isZero_secF_rightDerived_of_isZero_Hgroup {X Y : Scheme.{u}} (f : Y ⟶ X)
    (M : Y.Modules) (j : ℕ)
    (hM : ∀ q ≤ j, ∀ p : ℕ, 0 < p →
      IsZero (Hgroup X.ringCatSheaf ⊤ p (((Scheme.Modules.pushforward f).rightDerived q).obj M)))
    (h : IsZero (Hgroup Y.ringCatSheaf ⊤ j M)) :
    IsZero ((secF X.ringCatSheaf ⊤).obj (((Scheme.Modules.pushforward f).rightDerived j).obj M)) :=
  @isZero_map_rightDerived_of_isZero_rightDerived_comp Y.Modules X.Modules AddCommGrpCat.{u}
    _ _ _ _ _ _ _ _ (Scheme.Modules.pushforward f) (globalSec X)
    (Stacks.SchemeCohomology.pushforward_additive f) inferInstance inferInstance inferInstance
    (isZero_Hgroup_pushforward_of_injective f) j M hM h

/-- The projection formula for the twists: `R^q f_*(ℱ ⊗ (f^*ℋ)^{⊗ r}) ≅ R^q f_* ℱ ⊗ ℋ^{⊗ r}`. -/
private noncomputable def rightDerivedTwistIso {X Y : Scheme.{u}} (f : Y ⟶ X) (H : X.Modules)
    [IsInvertibleModule X H] (F : Y.Modules) (q : ℕ) (r : ℤ) :
    ((Scheme.Modules.pushforward f).rightDerived q).obj (twistModule Y (pullbackModule f H) F r) ≅
      twistModule X H (((Scheme.Modules.pushforward f).rightDerived q).obj F) r :=
  haveI : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (Stacks.Ample.tensorPowModule X H r) :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).2
      (inferInstanceAs (IsInvertibleModule X (Stacks.Ample.tensorPowModule X H r)))
  ((Scheme.Modules.pushforward f).rightDerived q).mapIso
      (Stacks.RelativeVeryAmple.tensorModulesMapIso Y (Iso.refl F)
        (Stacks.AlgebraicGeometry.HyperplaneTwistSequence.pullbackTensorPowModuleIntIso
          f H r).symm) ≪≫
    (Stacks.DerivedIndexing.rightDerivedIso _ q).app _ ≪≫
    Stacks.ProjectionFormula.higherDirectImageProjectionFormulaIso f
      (Stacks.Ample.tensorPowModule X H r) F q ≪≫
    Stacks.RelativeVeryAmple.tensorModulesMapIso X
      ((Stacks.DerivedIndexing.rightDerivedIso _ q).app F).symm (Iso.refl _)

end Concrete

/-- For `r ≫ 0`, vanishing of `H^j(Y, ℱ ⊗ (f^*ℋ)^{⊗ r})` forces vanishing of
`Γ(X, R^j f_* ℱ ⊗ ℋ^{⊗ r})`, by the degenerate Leray sequence. -/
private theorem eventually_isZero_sections_twist_of_isZero_cohomology_twist
    (k : Type u) [Field k] {X Y : Scheme.{u}} (pX : X ⟶ Spec (.of k)) [IsProper pX]
    (f : Y ⟶ X) [IsProper f] (H : X.Modules) [IsInvertibleModule X H] (hH : IsAmple X H)
    (F : Y.Modules) [F.IsCoherent] (j : ℕ) :
    ∀ᶠ r : ℕ in Filter.atTop,
      IsZero (((SheafOfModules.evaluation Y.ringCatSheaf (op (⊤ : Y.Opens))).rightDerived j).obj
          (twistModule Y (pullbackModule f H) F r)) →
        IsZero ((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).obj
          (twistModule X H (((Scheme.Modules.pushforward f).rightDerived j).obj F) r)) := by
  have serre : ∀ q : ℕ, ∃ d₀ : ℕ, ∀ d p : ℕ, d₀ ≤ d → 0 < p →
      IsZero (Hgroup X.ringCatSheaf ⊤ p
        (twistModule X H (((Scheme.Modules.pushforward f).rightDerived q).obj F) d)) := by
    intro q
    have := isCoherent_rightDerived_pushforward k pX f F q
    exact Stacks.AlgebraicGeometry.ProperAmpleCohomology.exists_isZero_Hgroup_tensorPowTwist pX
      _ H hH
  choose d₀ hd₀ using serre
  refine Filter.eventually_atTop.2 ⟨(Finset.range (j + 1)).sup d₀, fun r hr h => ?_⟩
  have h' := (Stacks.Cohomology.CechAcyclic.isZero_rightDerived_evaluation_iff_isZero_Hgroup
    (O := Y.ringCatSheaf) ⊤ j _).1 h
  have hM : ∀ q ≤ j, ∀ p : ℕ, 0 < p → IsZero (Hgroup X.ringCatSheaf ⊤ p
      (((Scheme.Modules.pushforward f).rightDerived q).obj
        (twistModule Y (pullbackModule f H) F r))) := by
    intro q hq p hp
    have hle : d₀ q ≤ r :=
      le_trans (Finset.le_sup (Finset.mem_range.2 (Nat.lt_succ_of_le hq))) hr
    exact (hd₀ q r p hle hp).of_iso
      ((Hfunctor X.ringCatSheaf ⊤ p).mapIso (rightDerivedTwistIso f H F q r))
  have h2 := isZero_secF_rightDerived_of_isZero_Hgroup f _ j hM h'
  have h3 := h2.of_iso ((secF X.ringCatSheaf ⊤).mapIso (rightDerivedTwistIso f H F j r)).symm
  have hs := AddCommGrpCat.subsingleton_of_isZero h3
  exact @ModuleCat.isZero_of_subsingleton _ _ _ hs

end MMP.Mori.HigherDirectImageTwisted

namespace MMP.Mori

@[expose] public section

open MMP.Mori.HigherDirectImageTwisted in
/-- **Higher direct images detected by twisted cohomology** (Kollár–Mori, Proposition 2.69,
`(1) ⇒ (2)`). Let `X` be proper over a field `k`, `ℋ` an ample invertible sheaf on `X`,
`f : Y ⟶ X` a proper morphism and `ℱ` a coherent sheaf on `Y`. If
`H^j(Y, ℱ ⊗ (f^*ℋ)^{⊗ r}) = 0` for all sufficiently large `r`, then `R^j f_* ℱ = 0`. -/
@[mmp "lem_km2c_higher_direct_image_of_twisted_vanishing"]
public theorem isZero_rightDerived_pushforward_of_eventually_isZero_cohomology_twist
    (k : Type u) [Field k] {X Y : Scheme.{u}} (pX : X ⟶ Spec (.of k)) [IsProper pX]
    (f : Y ⟶ X) [IsProper f] (H : X.Modules) [IsInvertibleModule X H] (hH : IsAmple X H)
    (F : Y.Modules) [F.IsCoherent] (j : ℕ)
    (hvan : ∀ᶠ r : ℕ in Filter.atTop,
      IsZero (((SheafOfModules.evaluation Y.ringCatSheaf (op (⊤ : Y.Opens))).rightDerived j).obj
        (twistModule Y (pullbackModule f H) F r))) :
    IsZero (((Scheme.Modules.pushforward f).rightDerived j).obj F) := by
  haveI := isCoherent_rightDerived_pushforward k pX f F j
  obtain ⟨r, hr, hleray, hgen⟩ := (hvan.and
    ((eventually_isZero_sections_twist_of_isZero_cohomology_twist k pX f H hH F j).and
      (eventually_isZero_of_isZero_sections_twistModule X H hH
        (((Scheme.Modules.pushforward f).rightDerived j).obj F)))).exists
  exact hgen (hleray hr)

end

end MMP.Mori

end

/-! ## The cyclic cover off the zero scheme -/

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite MMP.Mori

namespace MMP.Mori.RamifiedCoverRestriction

section SymPowers

open Polynomial

section AffineChart

/-! ### The polynomial model of `Sym(N)` over an affine open -/

open PresheafOfModules in
/-- The degree-one sheafification unit carries `ι x` to the degree-one generator of `Sym(E)`. -/
private theorem pieceUnit_one_ι {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent]
    {V : X.Opens} (hV : IsAffineOpen V) (x : Γ(E, V)) :
    Stacks.SymAlgSections.pieceUnit E hV 1
        ⟨SymmetricAlgebra.ι Γ(X, V) Γ(E, V) x, SymPow.ι_mem_symmetricPowerInt_one _ _ x⟩ =
      (Scheme.Modules.symmetricAlgebraGen X E).val.app (op V) x :=
  Eq.trans ((symPowIntGradedAlgebra E.val).sheafifyGen_unit
      (𝟙 X.ringCatSheaf.obj) (symPowIntGen E.val) (op V) x).symm
    (congrArg (fun t => ((symPowIntGradedAlgebra E.val).sheafifyGen
        (𝟙 X.ringCatSheaf.obj) (symPowIntGen E.val)).val.app (op V) t)
      (PresheafOfModules.sheafifyCounitIso_inv_apply (𝟙 X.ringCatSheaf.obj) E (op V) x).symm)

variable (D : Stacks.LineBundle.Situation.{u})

/-- Over an affine open, an element of `Symᵏ(Γ(L, U))` is carried to the homogeneous function
of the corresponding section of `Symᵏ(L)`. -/
private theorem symSectionsRingEquiv_coe (U : D.X.affineOpens) (k : ℕ)
    (y : SymPow.symmetricPower k Γ(D.X, U.1) Γ(D.L, U.1)) :
    D.symSectionsRingEquiv U (y : SymmetricAlgebra Γ(D.X, U.1) Γ(D.L, U.1)) =
      D.totalFunction k U.1 (Stacks.SymAlgSections.pieceUnit D.L U.2 k y) := by
  have h1 : DirectSum.decomposeRingEquiv
      (fun n : ℕ => SymPow.symmetricPower n Γ(D.X, U.1) Γ(D.L, U.1))
      (y : SymmetricAlgebra Γ(D.X, U.1) Γ(D.L, U.1)) = DirectSum.of _ k y :=
    DirectSum.decompose_coe (fun n : ℕ => SymPow.symmetricPower n Γ(D.X, U.1) Γ(D.L, U.1)) y
  have h2 := Stacks.SymAlgSections.ofSymPowers_of D.L U.2 k y
  unfold Stacks.LineBundle.Situation.totalFunction
  rw [D.universalAlgebraMap_app_eq_sectionsIso U]
  show (D.sectionsIso U).hom.hom (Stacks.RelativeSpec.ungradedSectionsRingEquiv D.X
    D.symmetricAlgebra D.symmetricAlgebra_mul_comm U.2
      (Stacks.SymAlgSections.symPowersRingEquiv D.L U.2 (DirectSum.decomposeRingEquiv
        (fun n : ℕ => SymPow.symmetricPower n Γ(D.X, U.1) Γ(D.L, U.1))
          (y : SymmetricAlgebra Γ(D.X, U.1) Γ(D.L, U.1))))) = _
  rw [h1]
  exact congrArg (fun z => (D.sectionsIso U).hom.hom
    ((Stacks.RelativeSpec.ungradedCommUnit D.X D.symmetricAlgebra
      D.symmetricAlgebra_mul_comm U.1).hom z)) h2

/-- The basis vector of `Γ(L, U)` is the variable of the polynomial model. -/
private theorem polynomialAlgEquiv_ι (U : D.X.affineOpens)
    (b : Module.Basis PUnit.{u + 1} Γ(D.X, U.1) Γ(D.L, U.1)) :
    D.polynomialAlgEquiv U b (SymmetricAlgebra.ι Γ(D.X, U.1) Γ(D.L, U.1) (b PUnit.unit)) =
      Polynomial.X := by
  unfold Stacks.LineBundle.Situation.polynomialAlgEquiv
  rw [AlgEquiv.trans_apply, SymmetricAlgebra.equivMvPolynomial_ι_apply]
  simp

/-- Under the polynomial model, `Symᵏ(Γ(L, U))` lands in the monomials of degree `k`. -/
private theorem polynomialAlgEquiv_mem_range_monomial (U : D.X.affineOpens)
    (b : Module.Basis PUnit.{u + 1} Γ(D.X, U.1) Γ(D.L, U.1)) (k : ℕ)
    {y : SymmetricAlgebra Γ(D.X, U.1) Γ(D.L, U.1)}
    (hy : y ∈ SymPow.symmetricPower k Γ(D.X, U.1) Γ(D.L, U.1)) :
    D.polynomialAlgEquiv U b y ∈
      LinearMap.range (monomial k : Γ(D.X, U.1) →ₗ[Γ(D.X, U.1)] _) := by
  induction k generalizing y with
  | zero =>
      rw [SymPow.symmetricPower, pow_zero, Submodule.one_eq_range] at hy
      obtain ⟨c, rfl⟩ := hy
      exact ⟨c, by simp⟩
  | succ k ih =>
      rw [SymPow.symmetricPower, pow_succ] at hy
      refine Submodule.mul_induction_on hy (fun y₁ hy₁ y₂ hy₂ => ?_) (fun y₁ y₂ h₁ h₂ => ?_)
      · obtain ⟨c₁, hc₁⟩ := ih hy₁
        obtain ⟨m, rfl⟩ := hy₂
        have hspan : m ∈ Submodule.span Γ(D.X, U.1) {b PUnit.unit} := by
          have := b.mem_span m
          rwa [Set.range_unique] at this
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hspan
        refine ⟨c₁ * c, ?_⟩
        rw [map_mul (D.polynomialAlgEquiv U b), ← hc₁, map_smul, map_smul,
          polynomialAlgEquiv_ι, Polynomial.smul_eq_C_mul, ← Polynomial.monomial_zero_left,
          ← Polynomial.monomial_one_one_eq_X, monomial_mul_monomial, monomial_mul_monomial]
        simp
      · rw [map_add]; exact Submodule.add_mem _ h₁ h₂

/-- Over an affine open, a section of `Symᵏ(L)` is determined by its homogeneous function. -/
private theorem totalFunction_injective [D.L.IsQuasicoherent] (U : D.X.affineOpens) (k : ℕ) :
    Function.Injective (D.totalFunction k U.1) := by
  intro x y h
  obtain ⟨x', rfl⟩ := (Stacks.SymAlgSections.pieceUnit D.L U.2 k).surjective x
  obtain ⟨y', rfl⟩ := (Stacks.SymAlgSections.pieceUnit D.L U.2 k).surjective y
  rw [← symSectionsRingEquiv_coe, ← symSectionsRingEquiv_coe] at h
  exact congrArg _ (Subtype.ext ((D.symSectionsRingEquiv U).injective h))

end AffineChart

section Gluing

/-! ### Freeness of rank one is local -/

variable {X : Scheme.{u}} (M : X.Modules)

private theorem modules_map_map {W W' W'' : X.Opens} (h : W' ≤ W) (h' : W'' ≤ W')
    (x : M.val.obj (op W)) :
    M.val.map (homOfLE h').op (M.val.map (homOfLE h).op x) =
      M.val.map (homOfLE (h'.trans h)).op x := by
  rw [← PresheafOfModules.map_comp_apply]
  rfl

private theorem presheaf_map_map {W W' W'' : X.Opens} (h : W' ≤ W) (h' : W'' ≤ W')
    (x : Γ(X, W)) :
    X.presheaf.map (homOfLE h').op (X.presheaf.map (homOfLE h).op x) =
      X.presheaf.map (homOfLE (h'.trans h)).op x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/-- The affine opens contained in `W` cover `W`. -/
private theorem le_iSup_affineOpens (W : X.Opens) :
    W ≤ ⨆ V : {V : X.affineOpens // V.1 ≤ W}, V.1.1 := by
  intro x hx
  obtain ⟨V, hV, hxV, hVW⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hx
  exact Opens.mem_iSup.mpr ⟨⟨⟨V, hV⟩, hVW⟩, hxV⟩

/-- Two sections of `𝒪_X` over `W` agreeing on every affine open in `W` are equal. -/
private theorem presheaf_eq_of_affine {W : X.Opens} (a a' : Γ(X, W))
    (h : ∀ V : X.affineOpens, ∀ hV : V.1 ≤ W,
      X.presheaf.map (homOfLE hV).op a = X.presheaf.map (homOfLE hV).op a') : a = a' :=
  TopCat.Sheaf.eq_of_locally_eq' X.sheaf (fun V : {V : X.affineOpens // V.1 ≤ W} => V.1.1) W
    (fun V => homOfLE V.2) (le_iSup_affineOpens W) a a' fun V => h V.1 V.2

/-- Two sections of `M` over `W` agreeing on every affine open in `W` are equal. -/
private theorem modules_eq_of_affine {W : X.Opens} (x x' : M.val.obj (op W))
    (h : ∀ V : X.affineOpens, ∀ hV : V.1 ≤ W,
      M.val.map (homOfLE hV).op x = M.val.map (homOfLE hV).op x') : x = x' :=
  TopCat.Sheaf.eq_of_locally_eq' (C := Ab.{u}) ⟨M.val.presheaf, M.isSheaf⟩
    (fun V : {V : X.affineOpens // V.1 ≤ W} => V.1.1) W
    (fun V => homOfLE V.2) (le_iSup_affineOpens W) x x' fun V => h V.1 V.2

/-- If a compatible family `e_W ∈ M(W)`, `W ⊆ U`, is a basis over every affine `W ⊆ U`, it is a
basis over every open `W ⊆ U`. -/
private theorem bijective_smul_of_affine (U : X.Opens)
    (e : ∀ W : X.Opens, W ≤ U → M.val.obj (op W))
    (he : ∀ (W W' : X.Opens) (hW : W ≤ U) (h : W' ≤ W),
      M.val.map (homOfLE h).op (e W hW) = e W' (h.trans hW))
    (haff : ∀ (V : X.affineOpens) (hV : V.1 ≤ U),
      Function.Bijective fun a : X.ringCatSheaf.obj.obj (op V.1) => a • e V.1 hV)
    (W : X.Opens) (hW : W ≤ U) :
    Function.Bijective fun a : X.ringCatSheaf.obj.obj (op W) => a • e W hW := by
  have hres : ∀ (W' : X.Opens) (h : W' ≤ W) (a : X.ringCatSheaf.obj.obj (op W)),
      M.val.map (homOfLE h).op (a • e W hW) =
        (show X.ringCatSheaf.obj.obj (op W') from X.presheaf.map (homOfLE h).op a) •
          e W' (h.trans hW) := by
    intro W' h a
    rw [PresheafOfModules.map_smul, he]
    rfl
  -- the coefficient of a section over an affine open in `W`
  have huniq : ∀ (V : X.affineOpens) (hV : V.1 ≤ W) (b b' : Γ(X, V.1)),
      (show X.ringCatSheaf.obj.obj (op V.1) from b) • e V.1 (hV.trans hW) =
        (show X.ringCatSheaf.obj.obj (op V.1) from b') • e V.1 (hV.trans hW) → b = b' :=
    fun V hV b b' h => (haff V (hV.trans hW)).1 h
  refine ⟨fun a a' h => presheaf_eq_of_affine a a' fun V hV => huniq V hV _ _ ?_, fun y => ?_⟩
  · rw [← hres, ← hres]
    exact congrArg _ h
  · have hc : ∀ V : {V : X.affineOpens // V.1 ≤ W}, ∃ c : Γ(X, V.1.1),
        (show X.ringCatSheaf.obj.obj (op V.1.1) from c) • e V.1.1 (V.2.trans hW) =
          M.val.map (homOfLE V.2).op y :=
      fun V => (haff V.1 (V.2.trans hW)).2 _
    choose c hc using hc
    obtain ⟨a, ha, -⟩ := TopCat.Sheaf.existsUnique_gluing' X.sheaf
      (fun V : {V : X.affineOpens // V.1 ≤ W} => V.1.1) W (fun V => homOfLE V.2)
      (le_iSup_affineOpens W) c (by
        intro V₁ V₂
        refine presheaf_eq_of_affine _ _ fun V hV => huniq V (hV.trans (inf_le_left.trans V₁.2))
          _ _ ?_
        have h₁ := congrArg (M.val.map (homOfLE (hV.trans inf_le_left)).op) (hc V₁)
        have h₂ := congrArg (M.val.map (homOfLE (hV.trans inf_le_right)).op) (hc V₂)
        rw [PresheafOfModules.map_smul, he, modules_map_map] at h₁ h₂
        erw [presheaf_map_map, presheaf_map_map]
        exact h₁.trans h₂.symm)
    refine ⟨a, modules_eq_of_affine M _ _ fun V hV => ?_⟩
    change M.val.map (homOfLE hV).op
      ((show X.ringCatSheaf.obj.obj (op W) from a) • e W hW) = _
    rw [hres]
    have := hc ⟨V, hV⟩
    rw [← this]
    exact congrArg (· • _) (ha ⟨V, hV⟩)

end Gluing

section Geometry

variable {X : Scheme.{u}} (N : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]

private theorem gen_nat (U W : X.Opens) (hW : W ≤ U) (t : N.val.obj (op U)) :
    (cyclicCoverSituation N).symmetricAlgebraGen.val.app (op W) (N.val.map (homOfLE hW).op t) =
      ((cyclicCoverSituation N).symmetricAlgebra.piece 1).val.map (homOfLE hW).op
        ((cyclicCoverSituation N).symmetricAlgebraGen.val.app (op U) t) :=
  PresheafOfModules.naturality_apply (cyclicCoverSituation N).symmetricAlgebraGen.val
    (homOfLE hW).op t

private theorem incl_cast (U : X.Opens) {n n' : ℤ} (h : n = n')
    (z : ((cyclicCoverSituation N).symmetricAlgebra.piece n).val.obj (op U)) :
    (cyclicCoverSituation N).algebraSheafIncl n' U
      ((eqToHom (congrArg (cyclicCoverSituation N).symmetricAlgebra.piece h)).val.app (op U) z) =
      (cyclicCoverSituation N).algebraSheafIncl n U z := by
  subst h; rfl

/-- The powers `tⁱ ∈ Γ(W, Symⁱ N)` of a section `t ∈ Γ(W, N)`, built from the graded product. -/
private noncomputable def symPow {W : X.Opens}
    (g : ((cyclicCoverSituation N).symmetricAlgebra.piece 1).val.obj (op W)) :
    ∀ i : ℕ, ((cyclicCoverSituation N).symmetricAlgebra.piece (i : ℤ)).val.obj (op W)
  | 0 => (cyclicCoverSituation N).symmetricAlgebra.one.eval (op W)
  | i + 1 => (eqToHom (congrArg (cyclicCoverSituation N).symmetricAlgebra.piece
      (Nat.cast_succ i).symm)).val.app (op W)
      (((cyclicCoverSituation N).symmetricAlgebra.mul (i : ℤ) 1).app (op W) (symPow g i) g)

private theorem incl_symPow {W : X.Opens}
    (g : ((cyclicCoverSituation N).symmetricAlgebra.piece 1).val.obj (op W)) (i : ℕ) :
    (cyclicCoverSituation N).algebraSheafIncl i W (symPow N g i) =
      (cyclicCoverSituation N).algebraSheafIncl 1 W g ^ i := by
  induction i with
  | zero => exact ((cyclicCoverSituation N).algebraSheafIncl_one W).trans (pow_zero _).symm
  | succ i ih =>
    rw [symPow, incl_cast N W (Nat.cast_succ i).symm,
      ← (cyclicCoverSituation N).algebraSheafIncl_mul, ih, pow_succ]

/-- The function on `Spec_X Sym(N)` attached to `gⁱ` is the `i`-th power of that of `g`. -/
private theorem symSpecFunction_symPow {W : X.Opens}
    (g : ((cyclicCoverSituation N).symmetricAlgebra.piece 1).val.obj (op W)) (i : ℕ) :
    symSpecFunction N i W (symPow N g i) = symSpecFunction N 1 W g ^ i := by
  unfold symSpecFunction
  rw [incl_symPow]
  exact map_pow _ _ _

/-- Over an affine open `V` on which `N` has the basis `b`, the function attached to the
degree-one generator `b` is the variable of the polynomial model. -/
private theorem symSpecFunction_gen_basis (V : X.affineOpens)
    (b : Module.Basis PUnit.{u + 1} Γ(X, V.1) Γ(N, V.1)) :
    symSpecFunction N 1 V.1
      ((cyclicCoverSituation N).symmetricAlgebraGen.val.app (op V.1) (b PUnit.unit)) =
      (cyclicCoverSituation N).polynomialSectionsRingEquiv V b Polynomial.X := by
  have e : ((cyclicCoverSituation N).polynomialAlgEquiv V b).symm Polynomial.X =
      SymmetricAlgebra.ι Γ(X, V.1) Γ(N, V.1) (b PUnit.unit) := by
    rw [AlgEquiv.symm_apply_eq, polynomialAlgEquiv_ι]
  have h2 := symSectionsRingEquiv_coe (cyclicCoverSituation N) V 1
    ⟨SymmetricAlgebra.ι Γ(X, V.1) Γ(N, V.1) (b PUnit.unit),
      SymPow.ι_mem_symmetricPowerInt_one _ _ _⟩
  refine Eq.trans ?_ ((congrArg _ e).trans (h2.trans
    (congrArg _ (pieceUnit_one_ι N V.2 (b PUnit.unit))))).symm
  rfl

/-- Over an affine open `V` on which `N` has the basis `b`, the function on `Spec_X Sym(N)`
attached to `a • bⁱ` is the monomial `a Tⁱ` of the polynomial model. -/
private theorem symSpecFunction_smul_symPow (V : X.affineOpens)
    (b : Module.Basis PUnit.{u + 1} Γ(X, V.1) Γ(N, V.1)) (i : ℕ) (a : Γ(X, V.1)) :
    symSpecFunction N i V.1 ((show X.ringCatSheaf.obj.obj (op V.1) from a) • symPow N
      ((cyclicCoverSituation N).symmetricAlgebraGen.val.app (op V.1) (b PUnit.unit)) i) =
    (cyclicCoverSituation N).polynomialSectionsRingEquiv V b (monomial i a) := by
  rw [symSpecFunction_smul, symSpecFunction_symPow, symSpecFunction_gen_basis,
    ← C_mul_X_pow_eq_monomial, map_mul, map_pow,
    (cyclicCoverSituation N).polynomialSectionsRingEquiv_C]

/-- Over an affine open `V` on which `N` has the basis `b`, `Symⁱ(N)(V)` is free of rank one
with basis `bⁱ`. -/
private theorem smul_symPow_bijective_of_basis (V : X.affineOpens)
    (b : Module.Basis PUnit.{u + 1} Γ(X, V.1) Γ(N, V.1)) (i : ℕ) :
    Function.Bijective fun a : X.ringCatSheaf.obj.obj (op V.1) => a • symPow N
      ((cyclicCoverSituation N).symmetricAlgebraGen.val.app (op V.1) (b PUnit.unit)) i := by
  refine ⟨fun a a' h => ?_, fun y => ?_⟩
  · have := congrArg (symSpecFunction N i V.1) h
    exact Polynomial.monomial_injective i
      (((cyclicCoverSituation N).polynomialSectionsRingEquiv V b).injective
        ((symSpecFunction_smul_symPow N V b i a).symm.trans
          (this.trans (symSpecFunction_smul_symPow N V b i a'))))
  · obtain ⟨y', rfl⟩ := (Stacks.SymAlgSections.pieceUnit N V.2 i).surjective y
    obtain ⟨c, hc⟩ := polynomialAlgEquiv_mem_range_monomial (cyclicCoverSituation N) V b i y'.2
    refine ⟨c, totalFunction_injective (cyclicCoverSituation N) V i ?_⟩
    refine (symSpecFunction_smul_symPow N V b i c).trans ?_
    rw [← symSectionsRingEquiv_coe]
    change (cyclicCoverSituation N).symSectionsRingEquiv V
      (((cyclicCoverSituation N).polynomialAlgEquiv V b).symm (monomial i c)) = _
    rw [show (monomial i c : Γ(X, V.1)[X]) =
      (cyclicCoverSituation N).polynomialAlgEquiv V b y' from hc, AlgEquiv.symm_apply_apply]

/-- The powers `tⁱ` commute with restriction. -/
private theorem symPow_map {W W' : X.Opens} (h : W' ≤ W)
    (g : ((cyclicCoverSituation N).symmetricAlgebra.piece 1).val.obj (op W)) :
    ∀ i : ℕ, ((cyclicCoverSituation N).symmetricAlgebra.piece (i : ℤ)).val.map (homOfLE h).op
        (symPow N g i) =
      symPow N (((cyclicCoverSituation N).symmetricAlgebra.piece 1).val.map (homOfLE h).op g) i
  | 0 => PresheafOfModules.sections_property _ _
  | i + 1 => by
    simp only [symPow]
    refine (PresheafOfModules.naturality_apply (eqToHom (congrArg
      (cyclicCoverSituation N).symmetricAlgebra.piece (Nat.cast_succ i).symm)).val
        (homOfLE h).op _).symm.trans (congrArg _ ?_)
    refine (((cyclicCoverSituation N).symmetricAlgebra.mul (i : ℤ) 1).naturality _ _ _).trans ?_
    exact congrArg (fun z => (((cyclicCoverSituation N).symmetricAlgebra.mul (i : ℤ) 1).app
      (op W')) z _) (symPow_map h g i)

/-- A section `t` of `N` over `V` with `a ↦ a • t` bijective gives a one-element basis. -/
private noncomputable def basisOfBijective {V : X.Opens} (t : N.val.obj (op V))
    (ht : Function.Bijective fun a : X.ringCatSheaf.obj.obj (op V) => a • t) :
    Module.Basis PUnit.{u + 1} Γ(X, V) Γ(N, V) :=
  (Module.Basis.singleton PUnit.{u + 1} Γ(X, V)).map
    (LinearEquiv.ofBijective (LinearMap.toSpanSingleton Γ(X, V) Γ(N, V) t) ht)

private theorem basisOfBijective_apply {V : X.Opens} (t : N.val.obj (op V))
    (ht : Function.Bijective fun a : X.ringCatSheaf.obj.obj (op V) => a • t) :
    basisOfBijective N t ht PUnit.unit = t := by
  simp only [basisOfBijective, Module.Basis.map_apply, Module.Basis.singleton_apply]
  exact one_smul _ _

/-- Over `W ⊆ U`, `Symⁱ(N)(W)` is free of rank one with basis `tⁱ`. -/
private theorem symPow_smul_bijective (U : X.Opens) (t : N.val.obj (op U))
    (ht : ∀ (W : X.Opens) (hW : W ≤ U),
      Function.Bijective fun a : X.ringCatSheaf.obj.obj (op W) =>
        a • (N.val.map (homOfLE hW).op t : N.val.obj (op W)))
    (W : X.Opens) (hW : W ≤ U) (i : ℕ) :
    Function.Bijective fun a : X.ringCatSheaf.obj.obj (op W) =>
      a • symPow N ((cyclicCoverSituation N).symmetricAlgebraGen.val.app (op W)
        (N.val.map (homOfLE hW).op t)) i := by
  refine bijective_smul_of_affine _ U (fun W hW => symPow N
    ((cyclicCoverSituation N).symmetricAlgebraGen.val.app (op W)
      (N.val.map (homOfLE hW).op t)) i) (fun W W' hW h => ?_) (fun V hV => ?_) W hW
  · rw [symPow_map]
    exact congrArg (symPow N · i)
      ((gen_nat N W W' h _).symm.trans (congrArg _ (modules_map_map N hW h t)))
  · have := smul_symPow_bijective_of_basis N V (basisOfBijective N _ (ht V.1 hV)) i
    convert this using 5
    exact congrArg _ (basisOfBijective_apply N _ _).symm

end Geometry

end SymPowers

section Helpers

variable {X : Scheme.{u}} (N : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
    (U : X.Opens) (N' : U.toScheme.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible U.toScheme.sheaf.obj
      U.toScheme.ringCatSheaf.property N']
    (e : N' ≅ N.restrict U.ι)

/-- Transposition along `e` and the restriction adjunction: module maps out of `N'` into a
pushforward along `h` correspond to module maps out of `N` into the pushforward along `h ≫ U.ι`. -/
private noncomputable def transposeEquiv {T : Scheme.{u}} (h : T ⟶ U.toScheme) :
    (N' ⟶ (Scheme.Modules.pushforward h).obj (SheafOfModules.unit T.ringCatSheaf)) ≃
      (N ⟶ (Scheme.Modules.pushforward (h ≫ U.ι)).obj (SheafOfModules.unit T.ringCatSheaf)) :=
  (e.homCongr (Iso.refl _)).trans
    (((Scheme.Modules.restrictAdjunction U.ι).homEquiv N _).trans
      (Iso.homToEquiv ((Scheme.Modules.pushforwardComp h U.ι).app
        (SheafOfModules.unit T.ringCatSheaf))))

omit [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
  [SheafOfModules.IsInvertible U.toScheme.sheaf.obj U.toScheme.ringCatSheaf.property N'] in
private theorem transposeEquiv_comp {T T' : Scheme.{u}} (h : T ⟶ U.toScheme) (a : T' ⟶ T)
    (τ : N' ⟶ (Scheme.Modules.pushforward h).obj (SheafOfModules.unit T.ringCatSheaf)) :
    transposeEquiv N U N' e (a ≫ h) (τ ≫ Stacks.LineBundle.structureComparison h a) =
      transposeEquiv N U N' e h τ ≫ Stacks.LineBundle.structureComparison (h ≫ U.ι) a := by
  simp only [transposeEquiv, Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_hom,
    Category.comp_id, Iso.homToEquiv_apply]
  rw [← Category.assoc e.inv, Adjunction.homEquiv_naturality_right]
  exact (Category.assoc _ _ _).trans ((congrArg _
    (Stacks.LineBundle.pushforwardComp_structureComparison U.ι h a)).trans
      (Category.assoc _ _ _).symm)

/-- The morphism `Tot(N') ⟶ Tot(N)` over `U.ι` induced by `e : N' ≅ N|_U`. -/
private noncomputable def toSymSpec : symSpec N' ⟶ symSpec N :=
  ((cyclicCoverSituation N).totalSpaceHomEquiv _).symm
    ⟨symSpecToBase N' ≫ U.ι,
      transposeEquiv N U N' e (symSpecToBase N') (cyclicCoverSituation N').tautologicalMap⟩

private theorem totalSpaceHomEquiv_toSymSpec :
    (cyclicCoverSituation N).totalSpaceHomEquiv _ (toSymSpec N U N' e) =
      ⟨symSpecToBase N' ≫ U.ι,
        transposeEquiv N U N' e (symSpecToBase N') (cyclicCoverSituation N').tautologicalMap⟩ :=
  Equiv.apply_symm_apply _ _

private theorem toSymSpec_toBase : toSymSpec N U N' e ≫ symSpecToBase N = symSpecToBase N' ≫ U.ι :=
  congrArg Sigma.fst (totalSpaceHomEquiv_toSymSpec N U N' e)

/-- A point of `Tot(N')` as a point of `Tot(N)`. -/
private noncomputable def point {T : Scheme.{u}}
    (σ : Σ h : T ⟶ U.toScheme, (N' ⟶
      (Scheme.Modules.pushforward h).obj (SheafOfModules.unit T.ringCatSheaf))) :
    Σ k : T ⟶ X, (N ⟶ (Scheme.Modules.pushforward k).obj
      (SheafOfModules.unit T.ringCatSheaf)) :=
  ⟨σ.1 ≫ U.ι, transposeEquiv N U N' e σ.1 σ.2⟩

private theorem totalSpaceHomEquiv_comp_toSymSpec {T : Scheme.{u}} (l : T ⟶ symSpec N') :
    (cyclicCoverSituation N).totalSpaceHomEquiv T (l ≫ toSymSpec N U N' e) =
      point N U N' e ((cyclicCoverSituation N').totalSpaceHomEquiv T l) := by
  rw [(cyclicCoverSituation N').totalSpaceHomEquiv_eq l]
  refine ((cyclicCoverSituation N).totalSpaceHomEquiv_comp_of_eq l _ _ _
    (totalSpaceHomEquiv_toSymSpec N U N' e)).trans ?_
  exact congrArg (Sigma.mk (l ≫ symSpecToBase N' ≫ U.ι))
    (transposeEquiv_comp N U N' e (symSpecToBase N') l
      (cyclicCoverSituation N').tautologicalMap).symm

private theorem toSymSpec_universal {T : Scheme.{u}} (a : T ⟶ U.toScheme) (b : T ⟶ symSpec N)
    (hab : b ≫ symSpecToBase N = a ≫ U.ι) :
    ∃ l : T ⟶ symSpec N', l ≫ toSymSpec N U N' e = b ∧ l ≫ symSpecToBase N' = a ∧
      ∀ m : T ⟶ symSpec N', m ≫ toSymSpec N U N' e = b → m ≫ symSpecToBase N' = a → m = l := by
  let D := cyclicCoverSituation N
  let D' := cyclicCoverSituation N'
  obtain ⟨⟨k, φ⟩, rfl⟩ : ∃ σ, (D.totalSpaceHomEquiv T).symm σ = b :=
    ⟨D.totalSpaceHomEquiv T b, (D.totalSpaceHomEquiv T).symm_apply_apply b⟩
  have hk : (D.totalSpaceHomEquiv T).symm ⟨k, φ⟩ ≫ D.totalSpaceToBase = k :=
    congrArg Sigma.fst ((D.totalSpaceHomEquiv T).apply_symm_apply ⟨k, φ⟩)
  change _ ≫ D.totalSpaceToBase = _ at hab
  rw [hk] at hab
  subst hab
  refine ⟨(D'.totalSpaceHomEquiv T).symm ⟨a, (transposeEquiv N U N' e a).symm φ⟩, ?_, ?_, ?_⟩
  · refine (D.totalSpaceHomEquiv T).injective ?_
    rw [totalSpaceHomEquiv_comp_toSymSpec, (D'.totalSpaceHomEquiv T).apply_symm_apply,
      (D.totalSpaceHomEquiv T).apply_symm_apply]
    exact congrArg (Sigma.mk (a ≫ U.ι)) ((transposeEquiv N U N' e a).apply_symm_apply φ)
  · exact congrArg Sigma.fst ((D'.totalSpaceHomEquiv T).apply_symm_apply _)
  · intro m hm₁ hm₂
    obtain ⟨⟨h, τ⟩, rfl⟩ : ∃ σ, (D'.totalSpaceHomEquiv T).symm σ = m :=
      ⟨D'.totalSpaceHomEquiv T m, (D'.totalSpaceHomEquiv T).symm_apply_apply m⟩
    have hσ : D'.totalSpaceHomEquiv T ((D'.totalSpaceHomEquiv T).symm ⟨h, τ⟩) = ⟨h, τ⟩ :=
      (D'.totalSpaceHomEquiv T).apply_symm_apply _
    have hh : (D'.totalSpaceHomEquiv T).symm ⟨h, τ⟩ ≫ D'.totalSpaceToBase = h :=
      congrArg Sigma.fst hσ
    obtain rfl : h = a := hh.symm.trans hm₂
    have h1 := totalSpaceHomEquiv_comp_toSymSpec N U N' e ((D'.totalSpaceHomEquiv T).symm ⟨h, τ⟩)
    rw [hσ, hm₁, (D.totalSpaceHomEquiv T).apply_symm_apply] at h1
    refine congrArg _ (congrArg (Sigma.mk _) ?_)
    exact (Equiv.eq_symm_apply _).mpr (sigma_mk_injective h1).symm

private theorem isPullback_toSymSpec :
    IsPullback (toSymSpec N U N' e) (symSpecToBase N') (symSpecToBase N) U.ι :=
  IsPullback.of_isLimit (PullbackCone.IsLimit.mk (toSymSpec_toBase N U N' e)
    (fun s => (toSymSpec_universal N U N' e s.snd s.fst s.condition).choose)
    (fun s => (toSymSpec_universal N U N' e s.snd s.fst s.condition).choose_spec.1)
    (fun s => (toSymSpec_universal N U N' e s.snd s.fst s.condition).choose_spec.2.1)
    (fun s m hm₁ hm₂ =>
      (toSymSpec_universal N U N' e s.snd s.fst s.condition).choose_spec.2.2 m hm₁ hm₂))

/-- `Tot(N')` is isomorphic to the part `π⁻¹(U)` of `Tot(N)` lying over `U`. -/
private noncomputable def symSpecIso : symSpec N' ≅ (symSpecToBase N ⁻¹ᵁ U).toScheme :=
  (isPullback_toSymSpec N U N' e).isoIsPullback _ _ (isPullback_morphismRestrict _ U).flip

@[reassoc]
private theorem symSpecIso_hom_ι :
    (symSpecIso N U N' e).hom ≫ (symSpecToBase N ⁻¹ᵁ U).ι = toSymSpec N U N' e :=
  IsPullback.isoIsPullback_hom_fst _ _ (isPullback_toSymSpec N U N' e)
    (isPullback_morphismRestrict _ U).flip

private theorem symSpecIso_hom_restrict :
    (symSpecIso N U N' e).hom ≫ (symSpecToBase N ∣_ U) = symSpecToBase N' :=
  IsPullback.isoIsPullback_hom_snd _ _ (isPullback_toSymSpec N U N' e)
    (isPullback_morphismRestrict _ U).flip

omit [SheafOfModules.IsInvertible U.toScheme.sheaf.obj U.toScheme.ringCatSheaf.property N'] in
/-- The functions of degree one pulled back along a point of `Tot(N)` are its module map. -/
private theorem appLE_symSpecFunction_of_eq {T : Scheme.{u}} (f : T ⟶ symSpec N) (k : T ⟶ X)
    (φ : N ⟶ (Scheme.Modules.pushforward k).obj (SheafOfModules.unit T.ringCatSheaf))
    (hf : (cyclicCoverSituation N).totalSpaceHomEquiv T f = ⟨k, φ⟩) (V : X.Opens)
    (n : N.val.obj (op V)) (O : T.Opens) (h₁ : O ≤ f ⁻¹ᵁ (symSpecToBase N ⁻¹ᵁ V))
    (h₂ : O ≤ k ⁻¹ᵁ V) :
    (f.appLE (symSpecToBase N ⁻¹ᵁ V) O h₁).hom
        (symSpecFunction N 1 V ((cyclicCoverSituation N).symmetricAlgebraGen.val.app (op V) n)) =
      (T.presheaf.map (homOfLE h₂).op).hom (φ.val.app (op V) n) := by
  have hk : f ≫ symSpecToBase N = k := congrArg Sigma.fst hf
  subst hk
  rw [(cyclicCoverSituation N).totalSpaceHomEquiv_eq f] at hf
  have hφ := eq_of_heq (Sigma.mk.inj hf).2
  subst hφ
  rfl

omit [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
  [SheafOfModules.IsInvertible U.toScheme.sheaf.obj U.toScheme.ringCatSheaf.property N'] in
private theorem transposeEquiv_val_app {T : Scheme.{u}} (h : T ⟶ U.toScheme)
    (τ : N' ⟶ (Scheme.Modules.pushforward h).obj (SheafOfModules.unit T.ringCatSheaf))
    (V : X.Opens) (n : N.val.obj (op V)) :
    (transposeEquiv N U N' e h τ).val.app (op V) n =
      τ.val.app (op (U.ι ⁻¹ᵁ V)) (e.inv.val.app (op (U.ι ⁻¹ᵁ V))
        (N.val.map (homOfLE (U.ι.image_preimage_le V)).op n)) := by
  simp only [transposeEquiv, Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_hom,
    Category.comp_id, Iso.homToEquiv_apply, Adjunction.homEquiv_unit]
  rfl

private theorem toSymSpec_appLE (V : X.Opens) (n : N.val.obj (op V))
    (h₁ : symSpecToBase N' ⁻¹ᵁ (U.ι ⁻¹ᵁ V) ≤ toSymSpec N U N' e ⁻¹ᵁ (symSpecToBase N ⁻¹ᵁ V)) :
    ((toSymSpec N U N' e).appLE (symSpecToBase N ⁻¹ᵁ V) _ h₁).hom
        (symSpecFunction N 1 V ((cyclicCoverSituation N).symmetricAlgebraGen.val.app (op V) n)) =
      symSpecFunction N' 1 (U.ι ⁻¹ᵁ V)
        ((cyclicCoverSituation N').symmetricAlgebraGen.val.app (op (U.ι ⁻¹ᵁ V))
          (e.inv.val.app (op (U.ι ⁻¹ᵁ V))
            (N.val.map (homOfLE (U.ι.image_preimage_le V)).op n))) := by
  rw [appLE_symSpecFunction_of_eq N (toSymSpec N U N' e) _ _
    (totalSpaceHomEquiv_toSymSpec N U N' e) V n _ h₁ le_rfl, transposeEquiv_val_app]
  exact (symSpec N').presheaf.map_id _ ▸ rfl

omit [SheafOfModules.IsInvertible U.toScheme.sheaf.obj U.toScheme.ringCatSheaf.property N'] in
/-- **Morphisms into `Tot(N)` are determined by their degree-one functions.** -/
private theorem symSpec_hom_ext {T : Scheme.{u}} (f g : T ⟶ symSpec N)
    (hb : f ≫ symSpecToBase N = g ≫ symSpecToBase N)
    (hm : ∀ (V : X.Opens) (n : N.val.obj (op V)), ∃ (O : T.Opens)
      (h₁ : O ≤ f ⁻¹ᵁ (symSpecToBase N ⁻¹ᵁ V)) (h₂ : O ≤ g ⁻¹ᵁ (symSpecToBase N ⁻¹ᵁ V)),
      (f ≫ symSpecToBase N) ⁻¹ᵁ V ≤ O ∧
      (f.appLE (symSpecToBase N ⁻¹ᵁ V) O h₁).hom
          (symSpecFunction N 1 V ((cyclicCoverSituation N).symmetricAlgebraGen.val.app (op V) n)) =
        (g.appLE (symSpecToBase N ⁻¹ᵁ V) O h₂).hom
          (symSpecFunction N 1 V ((cyclicCoverSituation N).symmetricAlgebraGen.val.app (op V) n))) :
    f = g := by
  apply ((cyclicCoverSituation N).totalSpaceHomEquiv T).injective
  rcases hf : (cyclicCoverSituation N).totalSpaceHomEquiv T f with ⟨k, φ⟩
  rcases hg : (cyclicCoverSituation N).totalSpaceHomEquiv T g with ⟨k', φ'⟩
  have hfk : f ≫ symSpecToBase N = k := congrArg Sigma.fst hf
  have hgk : g ≫ symSpecToBase N = k' := congrArg Sigma.fst hg
  obtain rfl : k' = k := hgk.symm.trans (hb.symm.trans hfk)
  congr 1
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun W =>
    ModuleCat.hom_ext (LinearMap.ext fun s => ?_))
  obtain ⟨V⟩ := W
  have h₁ := appLE_symSpecFunction_of_eq N f k' φ hf V s (k' ⁻¹ᵁ V)
    (by rw [← hfk]; exact le_rfl) le_rfl
  have h₂ := appLE_symSpecFunction_of_eq N g k' φ' hg V s (k' ⁻¹ᵁ V)
    (by rw [← hgk]; exact le_rfl) le_rfl
  have hmap : ∀ x : Γ(T, k' ⁻¹ᵁ V),
      (T.presheaf.map (homOfLE (le_refl (k' ⁻¹ᵁ V))).op).hom x = x := fun x => by
    rw [show (homOfLE (le_refl (k' ⁻¹ᵁ V))) = 𝟙 _ from rfl, op_id, T.presheaf.map_id]; rfl
  have key : (f.appLE (symSpecToBase N ⁻¹ᵁ V) (k' ⁻¹ᵁ V) (by rw [← hfk]; exact le_rfl)).hom
      (symSpecFunction N 1 V ((cyclicCoverSituation N).symmetricAlgebraGen.val.app (op V) s)) =
      (g.appLE (symSpecToBase N ⁻¹ᵁ V) (k' ⁻¹ᵁ V) (by rw [← hgk]; exact le_rfl)).hom
      (symSpecFunction N 1 V ((cyclicCoverSituation N).symmetricAlgebraGen.val.app (op V) s)) := by
    subst hfk
    obtain ⟨O, h₁O, h₂O, hO, hOeq⟩ := hm V s
    rw [← Scheme.Hom.appLE_map _ h₁O (homOfLE hO).op, ← Scheme.Hom.appLE_map _ h₂O (homOfLE hO).op,
      CommRingCat.comp_apply, CommRingCat.comp_apply, hOeq]
  exact (hmap _).symm.trans (h₁.symm.trans (key.trans (h₂.trans (hmap _))))

section Kernel

variable {Y : Scheme.{u}} (M : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M] (m : ℕ)
    (τ : (cyclicCoverSituation M).symmetricAlgebra.piece (m : ℤ) ⟶
      SheafOfModules.unit Y.ringCatSheaf)

omit [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N] in
/-- A morphism into `Spec Sym(M)` killing every generator `u - ⟨u, s⟩` kills `I_s`. -/
private theorem cyclicCoverIdeal_le_ker {T : Scheme.{u}} (k : T ⟶ symSpec M)
    (hk : ∀ (W : Y.Opens)
      (u : ((cyclicCoverSituation M).symmetricAlgebra.piece (m : ℤ)).val.obj (op W)),
      (k.app (symSpecToBase M ⁻¹ᵁ W)).hom (cyclicCoverGenerator M m τ W u) = 0) :
    cyclicCoverIdeal M m τ ≤ k.ker := by
  refine Scheme.IdealSheafData.le_ofIdeals_iff.mpr fun V x hx => ?_
  have hx' := Scheme.IdealSheafData.ideal_ofIdeals_le _ _ hx
  refine (Ideal.span_le (I := RingHom.ker (k.app V.1).hom)).mpr ?_ hx'
  intro f hf
  rw [SetLike.mem_coe, RingHom.mem_ker]
  have hloc : ∀ z : (k ⁻¹ᵁ V.1 : Set T), ∃ (V' : (symSpec M).Opens) (_ : V' ≤ V.1),
      k z.1 ∈ V' ∧ (T.presheaf.map (homOfLE (k.preimage_mono ‹V' ≤ V.1›)).op).hom
        ((k.app V.1).hom f) = 0 := by
    intro z
    obtain ⟨W, V', h₁, h₂, hyV', hV'⟩ := hf (k z.1) z.2
    refine ⟨V'.1, h₁, hyV', ?_⟩
    have e₁ : (T.presheaf.map (homOfLE (k.preimage_mono h₁)).op).hom ((k.app V.1).hom f) =
        (k.app V'.1).hom (((symSpec M).presheaf.map (homOfLE h₁).op).hom f) :=
      (ConcreteCategory.congr_hom (k.naturality (homOfLE h₁).op) f).symm
    rw [e₁]
    refine (Ideal.span_le (I := RingHom.ker (k.app V'.1).hom)).mpr ?_ hV'
    rintro _ ⟨u, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    refine (ConcreteCategory.congr_hom (k.naturality (homOfLE h₂).op)
      (cyclicCoverGenerator M m τ W u)).trans ?_
    rw [CommRingCat.comp_apply, hk W u]
    exact map_zero _
  choose V' hV'V hzV' hV' using hloc
  exact TopCat.Sheaf.eq_of_locally_eq' T.sheaf (fun z => k ⁻¹ᵁ V' z) _
    (fun z => homOfLE (k.preimage_mono (hV'V z)))
    (fun z hz => Opens.mem_iSup.mpr ⟨⟨z, hz⟩, hzV' ⟨z, hz⟩⟩) _ _
    fun z => (hV' z).trans (map_zero _).symm

/-- Vanishing of the pulled-back generators is local on the source. -/
private theorem app_cyclicCoverGenerator_eq_zero {T : Scheme.{u}} (k : T ⟶ symSpec M) (W : Y.Opens)
    (u : ((cyclicCoverSituation M).symmetricAlgebra.piece (m : ℤ)).val.obj (op W))
    (H : ∀ z ∈ k ⁻¹ᵁ (symSpecToBase M ⁻¹ᵁ W), ∃ (V : Y.Opens) (hV : V ≤ W) (O : T.Opens)
      (hO : O ≤ k ⁻¹ᵁ (symSpecToBase M ⁻¹ᵁ V)), z ∈ O ∧
      (k.appLE (symSpecToBase M ⁻¹ᵁ V) O hO).hom (cyclicCoverGenerator M m τ V
        (((cyclicCoverSituation M).symmetricAlgebra.piece (m : ℤ)).val.map (homOfLE hV).op u))
        = 0) :
    (k.app (symSpecToBase M ⁻¹ᵁ W)).hom (cyclicCoverGenerator M m τ W u) = 0 := by
  choose V hVW O hO hzO hV using H
  refine TopCat.Sheaf.eq_of_locally_eq' T.sheaf
    (fun z : (k ⁻¹ᵁ (symSpecToBase M ⁻¹ᵁ W) : Set T) => O z.1 z.2) _
    (fun z => homOfLE ((hO z.1 z.2).trans
      (k.preimage_mono ((symSpecToBase M).preimage_mono (hVW z.1 z.2)))))
    (fun z hz => Opens.mem_iSup.mpr ⟨⟨z, hz⟩, hzO z hz⟩) _ _ fun z => ?_
  refine Eq.trans ?_ (map_zero _).symm
  refine Eq.trans ?_ (hV z.1 z.2)
  rw [← cyclicCoverGenerator_restrict M m τ (hVW z.1 z.2) u, ← CommRingCat.comp_apply,
    Scheme.Hom.map_appLE]
  rfl

/-- An invertible module has local generators: around each point of an open `W` there is an open
`V ≤ W` and a section `t` of `M` over `V` which is a basis over every open in `V`. -/
private theorem exists_generator (W : Y.Opens) (y : Y) (hy : y ∈ W) :
    ∃ V : Y.Opens, V ≤ W ∧ y ∈ V ∧ ∃ t : M.val.obj (op V), ∀ (V' : Y.Opens) (h : V' ≤ V),
      Function.Bijective fun a : Y.ringCatSheaf.obj.obj (op V') =>
        a • (M.val.map (homOfLE h).op t : M.val.obj (op V')) := by
  obtain ⟨U₀, hyU₀, ⟨e₀⟩⟩ := (cyclicCoverSituation M).exists_trivializing_affineOpen y
  let V : Y.Opens := U₀.1 ⊓ W
  let e : M.over V ≅ SheafOfModules.unit (Y.ringCatSheaf.over V) :=
    Stacks.SheafOfModules.isoUnitOverOfHom M (homOfLE inf_le_left) e₀
  refine ⟨V, inf_le_right, ⟨hyU₀, hy⟩, e.inv.val.app (op (Over.mk (𝟙 V)))
    (1 : Y.ringCatSheaf.obj.obj (op V)), fun V' hV => ?_⟩
  have key : ∀ (a : Y.ringCatSheaf.obj.obj (op V')),
      a • (M.val.map (homOfLE hV).op (e.inv.val.app (op (Over.mk (𝟙 V)))
        (1 : Y.ringCatSheaf.obj.obj (op V))) : M.val.obj (op V')) =
        e.inv.val.app (op (Over.mk (homOfLE hV))) a := by
    intro a
    have h1 := PresheafOfModules.naturality_apply e.inv.val (X := op (Over.mk (𝟙 V)))
      (Y := op (Over.mk (homOfLE hV)))
      (Over.homMk (homOfLE hV) : Over.mk (homOfLE hV) ⟶ Over.mk (𝟙 V)).op
      (1 : Y.ringCatSheaf.obj.obj (op V))
    erw [PresheafOfModules.unit_map_one] at h1
    have h2 := (e.inv.val.app (op (Over.mk (homOfLE hV)))).hom.map_smul a
      (1 : Y.ringCatSheaf.obj.obj (op V'))
    exact (congrArg (fun z : M.val.obj (op V') => a • z) h1).symm.trans
      (h2.symm.trans (congrArg _ (mul_one a)))
  have : (fun a : Y.ringCatSheaf.obj.obj (op V') =>
      a • (M.val.map (homOfLE hV).op (e.inv.val.app (op (Over.mk (𝟙 V)))
        (1 : Y.ringCatSheaf.obj.obj (op V))) : M.val.obj (op V'))) =
      e.inv.val.app (op (Over.mk (homOfLE hV))) := funext key
  rw [this]
  exact ((PresheafOfModules.toPresheaf _ ⋙ (CategoryTheory.evaluation _ _).obj
    (op (Over.mk (homOfLE hV))) ⋙ forget _).mapIso
      ((SheafOfModules.forget _).mapIso e.symm)).toEquiv.bijective

end Kernel

section Generators

variable (m : ℕ)
    (σ : (cyclicCoverSituation N).symmetricAlgebra.piece (m : ℤ) ⟶
      SheafOfModules.unit X.ringCatSheaf)

/-- `ψ` is the restriction of `σ` along `e : N' ≅ N|_U`, tested on products of generators. -/
private def IsRestr
    (ψ : (cyclicCoverSituation N').symmetricAlgebra.piece (m : ℤ) ⟶
        SheafOfModules.unit U.toScheme.ringCatSheaf) : Prop :=
  ∀ (W : U.toScheme.Opens) (t : Fin m → N'.val.obj (op W))
    (u' : ((cyclicCoverSituation N').symmetricAlgebra.piece (m : ℤ)).val.obj (op W))
    (u : ((cyclicCoverSituation N).symmetricAlgebra.piece (m : ℤ)).val.obj (op (U.ι ''ᵁ W))),
    (cyclicCoverSituation N').algebraSheafIncl m W u' =
        ∏ i, (cyclicCoverSituation N').algebraSheafIncl 1 W
          ((cyclicCoverSituation N').symmetricAlgebraGen.val.app (op W) (t i)) →
    (cyclicCoverSituation N).algebraSheafIncl m (U.ι ''ᵁ W) u =
        ∏ i, (cyclicCoverSituation N).algebraSheafIncl 1 (U.ι ''ᵁ W)
          ((cyclicCoverSituation N).symmetricAlgebraGen.val.app (op (U.ι ''ᵁ W))
            ((N.restrictAppIso U.ι W).hom (e.hom.val.app (op W) (t i)))) →
    ψ.val.app (op W) u' = (U.ι.appIso W).inv (σ.val.app (op (U.ι ''ᵁ W)) u)

omit [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
  [SheafOfModules.IsInvertible U.toScheme.sheaf.obj U.toScheme.ringCatSheaf.property N'] in
private theorem e_hom_inv_apply (W : U.toScheme.Opens) (y : (N.restrict U.ι).val.obj (op W)) :
    e.hom.val.app (op W) (e.inv.val.app (op W) y) = y :=
  congrArg (fun f : N.restrict U.ι ⟶ N.restrict U.ι => f.val.app (op W) y) e.inv_hom_id

private theorem incl_symPow_eq_prod {Y : Scheme.{u}} (M : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M]
    (W : Y.Opens) (t : M.val.obj (op W)) (k : ℕ) :
    (cyclicCoverSituation M).algebraSheafIncl k W
        (symPow M ((cyclicCoverSituation M).symmetricAlgebraGen.val.app (op W) t) k) =
      ∏ _i : Fin k, (cyclicCoverSituation M).algebraSheafIncl 1 W
        ((cyclicCoverSituation M).symmetricAlgebraGen.val.app (op W) t) := by
  rw [incl_symPow, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The restriction `ψ` of `σ` on `tᵐ`, for a section `t` of `N` over `V ⊆ U`. -/
private theorem isRestr_symPow
    {ψ : (cyclicCoverSituation N').symmetricAlgebra.piece (m : ℤ) ⟶
        SheafOfModules.unit U.toScheme.ringCatSheaf} (hψ : IsRestr N U N' e m σ ψ)
    (V : X.Opens) (t : N.val.obj (op V)) :
    ψ.val.app (op (U.ι ⁻¹ᵁ V)) (symPow N' ((cyclicCoverSituation N').symmetricAlgebraGen.val.app
        (op (U.ι ⁻¹ᵁ V)) (e.inv.val.app (op (U.ι ⁻¹ᵁ V))
          (N.val.map (homOfLE (U.ι.image_preimage_le V)).op t))) m) =
      U.ι.app V (σ.val.app (op V) (symPow N
        ((cyclicCoverSituation N).symmetricAlgebraGen.val.app (op V) t) m)) := by
  set t' := e.inv.val.app (op (U.ι ⁻¹ᵁ V)) (N.val.map (homOfLE (U.ι.image_preimage_le V)).op t)
  have h := hψ (U.ι ⁻¹ᵁ V) (fun _ => t') _ _ (incl_symPow_eq_prod N' _ t' m)
    (incl_symPow_eq_prod N _ _ m)
  refine h.trans ?_
  rw [Scheme.Opens.ι_appIso, Iso.refl_inv, Scheme.Opens.ι_app]
  change σ.val.app _ (symPow N ((cyclicCoverSituation N).symmetricAlgebraGen.val.app _
    (e.hom.val.app (op (U.ι ⁻¹ᵁ V)) t')) m) = _
  have ht' : e.hom.val.app (op (U.ι ⁻¹ᵁ V)) t' =
      N.val.map (homOfLE (U.ι.image_preimage_le V)).op t := e_hom_inv_apply N U N' e _ _
  rw [ht']
  erw [gen_nat N V _ (U.ι.image_preimage_le V) t, ← symPow_map,
    PresheafOfModules.naturality_apply]
  rfl

private theorem appLE_congr_hom {A B : Scheme.{u}} {f g : A ⟶ B} (hfg : f = g) (W : B.Opens)
    (V : A.Opens) (h : V ≤ f ⁻¹ᵁ W) (h' : V ≤ g ⁻¹ᵁ W) : f.appLE W V h = g.appLE W V h' := by
  subst hfg
  rfl

private theorem preimage_toSymSpec (V : X.Opens) :
    symSpecToBase N' ⁻¹ᵁ (U.ι ⁻¹ᵁ V) = toSymSpec N U N' e ⁻¹ᵁ (symSpecToBase N ⁻¹ᵁ V) := by
  rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, toSymSpec_toBase]

/-- The base functions of `Tot(N)` pull back along `Tot(N') ⟶ Tot(N)` through `U.ι`. -/
private theorem app_toSymSpec_appLE (V : X.Opens)
    (h₁ : symSpecToBase N' ⁻¹ᵁ (U.ι ⁻¹ᵁ V) ≤ toSymSpec N U N' e ⁻¹ᵁ (symSpecToBase N ⁻¹ᵁ V))
    (c : Γ(X, V)) :
    ((toSymSpec N U N' e).appLE (symSpecToBase N ⁻¹ᵁ V) _ h₁).hom
        (((symSpecToBase N).app V).hom c) =
      ((symSpecToBase N').app (U.ι ⁻¹ᵁ V)).hom ((U.ι.app V).hom c) := by
  have hB : symSpecToBase N' ⁻¹ᵁ (U.ι ⁻¹ᵁ V) ≤ (symSpecToBase N' ≫ U.ι) ⁻¹ᵁ V := le_rfl
  have hA : symSpecToBase N' ⁻¹ᵁ (U.ι ⁻¹ᵁ V) ≤
      (toSymSpec N U N' e ≫ symSpecToBase N) ⁻¹ᵁ V := h₁
  have e₂' : (symSpecToBase N).app V ≫ (toSymSpec N U N' e).appLE (symSpecToBase N ⁻¹ᵁ V) _ h₁ =
      U.ι.app V ≫ (symSpecToBase N').app (U.ι ⁻¹ᵁ V) := by
    calc (symSpecToBase N).app V ≫ (toSymSpec N U N' e).appLE (symSpecToBase N ⁻¹ᵁ V) _ h₁
        = (toSymSpec N U N' e ≫ symSpecToBase N).appLE V _ hA := by
          rw [Scheme.Hom.app_eq_appLE (symSpecToBase N) (U := V)]
          exact Scheme.Hom.appLE_comp_appLE _ _ V _ _ le_rfl h₁
      _ = (symSpecToBase N' ≫ U.ι).appLE V _ hB :=
          appLE_congr_hom (toSymSpec_toBase N U N' e) _ _ _ _
      _ = U.ι.app V ≫ (symSpecToBase N').app (U.ι ⁻¹ᵁ V) := by
          rw [Scheme.Hom.app_eq_appLE U.ι (U := V),
            Scheme.Hom.app_eq_appLE (symSpecToBase N') (U := U.ι ⁻¹ᵁ V)]
          exact (Scheme.Hom.appLE_comp_appLE _ _ V _ _ le_rfl le_rfl).symm
  exact ConcreteCategory.congr_hom e₂' c

/-- **The pulled-back generators vanish on the cyclic cover of `N'`**, for `u = tᵐ`. -/
private theorem toSymSpec_cyclicCoverGenerator_symPow
    {ψ : (cyclicCoverSituation N').symmetricAlgebra.piece (m : ℤ) ⟶
        SheafOfModules.unit U.toScheme.ringCatSheaf} (hψ : IsRestr N U N' e m σ ψ)
    (V : X.Opens) (t : N.val.obj (op V))
    (hO : (cyclicCoverIdeal N' m ψ).subschemeι ⁻¹ᵁ (symSpecToBase N' ⁻¹ᵁ (U.ι ⁻¹ᵁ V)) ≤
      ((cyclicCoverIdeal N' m ψ).subschemeι ≫ toSymSpec N U N' e) ⁻¹ᵁ
        (symSpecToBase N ⁻¹ᵁ V)) :
    (((cyclicCoverIdeal N' m ψ).subschemeι ≫ toSymSpec N U N' e).appLE _ _ hO).hom
      (cyclicCoverGenerator N m σ V
        (symPow N ((cyclicCoverSituation N).symmetricAlgebraGen.val.app (op V) t) m)) = 0 := by
  set ι' := (cyclicCoverIdeal N' m ψ).subschemeι
  have h₁ := (preimage_toSymSpec N U N' e V).le
  rw [← Scheme.Hom.appLE_comp_appLE ι' (toSymSpec N U N' e) _ _ _ h₁ le_rfl,
    Scheme.Hom.appLE_eq_app, CommRingCat.comp_apply]
  unfold cyclicCoverGenerator
  rw [map_sub, map_sub, symSpecFunction_symPow, map_pow, toSymSpec_appLE N U N' e V t h₁,
    ← symSpecFunction_symPow]
  erw [app_toSymSpec_appLE N U N' e V h₁]
  rw [← isRestr_symPow N U N' e m σ hψ V t]
  change cyclicCoverAlgebraIncl N' m ψ m _ _ - _ = 0
  rw [cyclicCoverAlgebraIncl_self]
  exact sub_eq_zero.mpr rfl

omit [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
  [SheafOfModules.IsInvertible U.toScheme.sheaf.obj U.toScheme.ringCatSheaf.property N'] in
private theorem e_inv_hom_apply (W : U.toScheme.Opens) (y : N'.val.obj (op W)) :
    e.inv.val.app (op W) (e.hom.val.app (op W) y) = y :=
  congrArg (fun f : N' ⟶ N' => f.val.app (op W) y) e.hom_inv_id

/-- The degree-one functions on `Spec Sym(N)` over `ι(W')` pull back along `Tot(N') ⟶ Tot(N)`
to those of `N'` over `W'`. -/
private theorem toSymSpec_appLE' (W' : U.toScheme.Opens) (t' : N'.val.obj (op W'))
    (h : symSpecToBase N' ⁻¹ᵁ W' ≤ toSymSpec N U N' e ⁻¹ᵁ (symSpecToBase N ⁻¹ᵁ (U.ι ''ᵁ W'))) :
    ((toSymSpec N U N' e).appLE (symSpecToBase N ⁻¹ᵁ (U.ι ''ᵁ W')) _ h).hom
        (symSpecFunction N 1 (U.ι ''ᵁ W')
          ((cyclicCoverSituation N).symmetricAlgebraGen.val.app (op (U.ι ''ᵁ W'))
            (e.hom.val.app (op W') t'))) =
      symSpecFunction N' 1 W'
        ((cyclicCoverSituation N').symmetricAlgebraGen.val.app (op W') t') := by
  have h₁ := (preimage_toSymSpec N U N' e (U.ι ''ᵁ W')).le
  have hW : W' ≤ U.ι ⁻¹ᵁ (U.ι ''ᵁ W') := (U.ι.preimage_image_eq W').ge
  rw [← Scheme.Hom.appLE_map _ h₁ (homOfLE ((symSpecToBase N').preimage_mono hW)).op,
    CommRingCat.comp_apply]
  erw [toSymSpec_appLE N U N' e (U.ι ''ᵁ W') (e.hom.val.app (op W') t') h₁]
  erw [symSpecFunction_restrict N' 1 hW]
  congr 1
  erw [← gen_nat N' _ _ hW]
  congr 1
  erw [← PresheafOfModules.naturality_apply e.inv.val]
  have key : ∀ y : N.val.obj (op (U.ι ''ᵁ W')), (N.restrict U.ι).val.map (homOfLE hW).op
      (N.val.map (homOfLE (U.ι.image_preimage_le (U.ι ''ᵁ W'))).op y) = y := fun y => by
    show N.val.map (homOfLE (U.ι.image_mono hW)).op
      (N.val.map (homOfLE (U.ι.image_preimage_le (U.ι ''ᵁ W'))).op y) = y
    rw [modules_map_map]
    exact PresheafOfModules.map_id_apply _ _ _
  erw [key]
  exact e_inv_hom_apply N U N' e W' t'

private theorem toSymSpec_apply (w : symSpec N') :
    symSpecToBase N (toSymSpec N U N' e w) = U.ι (symSpecToBase N' w) := by
  rw [← Scheme.Hom.comp_apply, toSymSpec_toBase, Scheme.Hom.comp_apply]

/-- **The pulled-back generators vanish on the cyclic cover of `N'`.** -/
private theorem toSymSpec_cyclicCoverGenerator
    {ψ : (cyclicCoverSituation N').symmetricAlgebra.piece (m : ℤ) ⟶
        SheafOfModules.unit U.toScheme.ringCatSheaf} (hψ : IsRestr N U N' e m σ ψ)
    (W : X.Opens) (u : ((cyclicCoverSituation N).symmetricAlgebra.piece (m : ℤ)).val.obj (op W)) :
    (((cyclicCoverIdeal N' m ψ).subschemeι ≫ toSymSpec N U N' e).app
      (symSpecToBase N ⁻¹ᵁ W)).hom (cyclicCoverGenerator N m σ W u) = 0 := by
  refine app_cyclicCoverGenerator_eq_zero (M := N) (m := m) (τ := σ) _ W u fun z hz => ?_
  have hy : U.ι (symSpecToBase N' ((cyclicCoverIdeal N' m ψ).subschemeι z)) ∈ W ⊓ U := by
    refine ⟨?_, (symSpecToBase N' ((cyclicCoverIdeal N' m ψ).subschemeι z)).2⟩
    rw [← toSymSpec_apply N U N' e]
    exact hz
  obtain ⟨V, hVWU, hyV, t, ht⟩ := exists_generator (M := N) (W ⊓ U) _ hy
  have hO : (cyclicCoverIdeal N' m ψ).subschemeι ⁻¹ᵁ (symSpecToBase N' ⁻¹ᵁ (U.ι ⁻¹ᵁ V)) ≤
      ((cyclicCoverIdeal N' m ψ).subschemeι ≫ toSymSpec N U N' e) ⁻¹ᵁ
        (symSpecToBase N ⁻¹ᵁ V) :=
    (congrArg ((cyclicCoverIdeal N' m ψ).subschemeι ⁻¹ᵁ ·) (preimage_toSymSpec N U N' e V)).le
  refine ⟨V, hVWU.trans inf_le_left, _, hO, hyV, ?_⟩
  obtain ⟨a, ha⟩ := (symPow_smul_bijective N V t ht V le_rfl m).2
    (((cyclicCoverSituation N).symmetricAlgebra.piece (m : ℤ)).val.map
      (homOfLE (hVWU.trans inf_le_left)).op u)
  rw [← ha, cyclicCoverGenerator_smul, map_mul,
    toSymSpec_cyclicCoverGenerator_symPow N U N' e m σ hψ V
      (N.val.map (homOfLE (le_refl V)).op t) hO, mul_zero]

end Generators

section Scaling

omit [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N] in
private theorem globalScalar_ι (V : X.Opens) (c : Γ(X, ⊤)) :
    globalScalar (U.ι.appTop c) (op (U.ι ⁻¹ᵁ V)) = U.ι.app V (globalScalar c (op V)) :=
  (ConcreteCategory.congr_hom (U.ι.naturality (homOfLE le_top : V ⟶ ⊤).op) c).symm

/-- **`Tot(N') ⟶ Tot(N)` intertwines the scaling automorphisms** for `ζ` and its restriction. -/
private theorem symSpecScaling_toSymSpec (ζ : Γ(X, ⊤)ˣ) (ζ' : Γ(U.toScheme, ⊤)ˣ)
    (hζ : (ζ' : Γ(U.toScheme, ⊤)) = U.ι.appTop (ζ : Γ(X, ⊤))) :
    symSpecScaling N' ζ' ≫ toSymSpec N U N' e = toSymSpec N U N' e ≫ symSpecScaling N ζ := by
  have hb : (symSpecScaling N' ζ' ≫ toSymSpec N U N' e) ≫ symSpecToBase N =
      (toSymSpec N U N' e ≫ symSpecScaling N ζ) ≫ symSpecToBase N := by
    rw [Category.assoc, Category.assoc, toSymSpec_toBase, symSpecScaling_toBase,
      symSpecScaling_toBase_assoc]
    exact (toSymSpec_toBase N U N' e).symm
  refine symSpec_hom_ext N _ _ hb fun V n => ?_
  have hS' : symSpecToBase N' ⁻¹ᵁ (U.ι ⁻¹ᵁ V) ≤
      symSpecScaling N' ζ' ⁻¹ᵁ (symSpecToBase N' ⁻¹ᵁ (U.ι ⁻¹ᵁ V)) :=
    (symSpecScaling_preimage N' ζ' _).ge
  have hS : symSpecToBase N ⁻¹ᵁ V ≤ symSpecScaling N ζ ⁻¹ᵁ (symSpecToBase N ⁻¹ᵁ V) :=
    (symSpecScaling_preimage N ζ _).ge
  have h₁ := (preimage_toSymSpec N U N' e V).le
  have hO₁ : symSpecToBase N' ⁻¹ᵁ (U.ι ⁻¹ᵁ V) ≤
      (symSpecScaling N' ζ' ≫ toSymSpec N U N' e) ⁻¹ᵁ (symSpecToBase N ⁻¹ᵁ V) :=
    hS'.trans ((symSpecScaling N' ζ').preimage_mono h₁)
  have hO₂ : symSpecToBase N' ⁻¹ᵁ (U.ι ⁻¹ᵁ V) ≤
      (toSymSpec N U N' e ≫ symSpecScaling N ζ) ⁻¹ᵁ (symSpecToBase N ⁻¹ᵁ V) :=
    h₁.trans ((toSymSpec N U N' e).preimage_mono hS)
  refine ⟨_, hO₁, hO₂, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_preimage, hb, Category.assoc, symSpecScaling_toBase, toSymSpec_toBase]
  rw [← Scheme.Hom.appLE_comp_appLE _ _ _ _ _ h₁ hS', ← Scheme.Hom.appLE_comp_appLE _ _ _ _ _ hS h₁,
    CommRingCat.comp_apply, CommRingCat.comp_apply, toSymSpec_appLE N U N' e V n h₁]
  erw [symSpecScaling_symSpecFunction N' ζ' 1 _ _ hS', symSpecScaling_symSpecFunction N ζ 1 V _ hS]
  rw [symSpecFunction_smul, symSpecFunction_smul, map_mul, toSymSpec_appLE N U N' e V n h₁]
  congr 1
  erw [app_toSymSpec_appLE N U N' e V h₁]
  rw [Nat.cast_one, zpow_one, zpow_one, hζ, globalScalar_ι]

end Scaling

section CoverIso

variable (m : ℕ)
    (σ : (cyclicCoverSituation N).symmetricAlgebra.piece (m : ℤ) ⟶
      SheafOfModules.unit X.ringCatSheaf)
    (ψ : (cyclicCoverSituation N').symmetricAlgebra.piece (m : ℤ) ⟶
      SheafOfModules.unit U.toScheme.ringCatSheaf)

/-- The cyclic cover of `N'` maps to that of `N`. -/
private noncomputable def coverToCover (hψ : IsRestr N U N' e m σ ψ) :
    cyclicCover N' m ψ ⟶ cyclicCover N m σ :=
  IsClosedImmersion.lift (cyclicCoverIdeal N m σ).subschemeι
    ((cyclicCoverIdeal N' m ψ).subschemeι ≫ toSymSpec N U N' e) (by
      rw [Scheme.IdealSheafData.ker_subschemeι]
      exact cyclicCoverIdeal_le_ker N m σ _
        (toSymSpec_cyclicCoverGenerator N U N' e m σ hψ))

@[reassoc]
private theorem coverToCover_subschemeι (hψ : IsRestr N U N' e m σ ψ) :
    coverToCover N U N' e m σ ψ hψ ≫ (cyclicCoverIdeal N m σ).subschemeι =
      (cyclicCoverIdeal N' m ψ).subschemeι ≫ toSymSpec N U N' e :=
  IsClosedImmersion.lift_fac _ _ _

private theorem coverToCover_toBase (hψ : IsRestr N U N' e m σ ψ) :
    coverToCover N U N' e m σ ψ hψ ≫ cyclicCoverToBase N m σ =
      cyclicCoverToBase N' m ψ ≫ U.ι := by
  unfold cyclicCoverToBase
  rw [← Category.assoc, coverToCover_subschemeι, Category.assoc, toSymSpec_toBase,
    Category.assoc]

/-- The cyclic cover of `N'` maps into `p⁻¹(U)`. -/
private noncomputable def coverToPreimage (hψ : IsRestr N U N' e m σ ψ) :
    cyclicCover N' m ψ ⟶ (cyclicCoverToBase N m σ ⁻¹ᵁ U).toScheme :=
  IsOpenImmersion.lift (cyclicCoverToBase N m σ ⁻¹ᵁ U).ι (coverToCover N U N' e m σ ψ hψ) (by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    change cyclicCoverToBase N m σ (coverToCover N U N' e m σ ψ hψ w) ∈ U
    rw [← Scheme.Hom.comp_apply, coverToCover_toBase, Scheme.Hom.comp_apply]
    exact (cyclicCoverToBase N' m ψ w).2)

@[reassoc]
private theorem coverToPreimage_ι (hψ : IsRestr N U N' e m σ ψ) :
    coverToPreimage N U N' e m σ ψ hψ ≫ (cyclicCoverToBase N m σ ⁻¹ᵁ U).ι =
      coverToCover N U N' e m σ ψ hψ :=
  IsOpenImmersion.lift_fac _ _ _

/-- `p⁻¹(U)` maps into `π⁻¹(U)`. -/
private noncomputable def preimageToPreimage :
    (cyclicCoverToBase N m σ ⁻¹ᵁ U).toScheme ⟶ (symSpecToBase N ⁻¹ᵁ U).toScheme :=
  IsOpenImmersion.lift (symSpecToBase N ⁻¹ᵁ U).ι
    ((cyclicCoverToBase N m σ ⁻¹ᵁ U).ι ≫ (cyclicCoverIdeal N m σ).subschemeι) (by
      rintro _ ⟨w, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact w.2)

@[reassoc]
private theorem preimageToPreimage_ι :
    preimageToPreimage N U m σ ≫ (symSpecToBase N ⁻¹ᵁ U).ι =
      (cyclicCoverToBase N m σ ⁻¹ᵁ U).ι ≫ (cyclicCoverIdeal N m σ).subschemeι :=
  IsOpenImmersion.lift_fac _ _ _

/-- `p⁻¹(U) ⟶ Tot(N')`. -/
private noncomputable def preimageToSymSpec :
    (cyclicCoverToBase N m σ ⁻¹ᵁ U).toScheme ⟶ symSpec N' :=
  preimageToPreimage N U m σ ≫ (symSpecIso N U N' e).inv

private theorem preimageToSymSpec_toSymSpec :
    preimageToSymSpec N U N' e m σ ≫ toSymSpec N U N' e =
      (cyclicCoverToBase N m σ ⁻¹ᵁ U).ι ≫ (cyclicCoverIdeal N m σ).subschemeι := by
  rw [preimageToSymSpec, ← symSpecIso_hom_ι, Category.assoc, Iso.inv_hom_id_assoc,
    preimageToPreimage_ι]

private theorem preimageToSymSpec_toBase :
    preimageToSymSpec N U N' e m σ ≫ symSpecToBase N' =
      preimageToPreimage N U m σ ≫ (symSpecToBase N ∣_ U) := by
  rw [preimageToSymSpec, Category.assoc, ← symSpecIso_hom_restrict N U N' e,
    Iso.inv_hom_id_assoc]

private theorem preimageToSymSpec_toBase_ι :
    preimageToSymSpec N U N' e m σ ≫ symSpecToBase N' ≫ U.ι =
      (cyclicCoverToBase N m σ ⁻¹ᵁ U).ι ≫ cyclicCoverToBase N m σ := by
  rw [← Category.assoc, preimageToSymSpec_toBase, Category.assoc, morphismRestrict_ι,
    ← Category.assoc, preimageToPreimage_ι, Category.assoc]
  rfl

/-- **The pulled-back generators of `N'` vanish on `p⁻¹(U)`**, for `u' = t'ᵐ`. -/
private theorem preimageToSymSpec_cyclicCoverGenerator_symPow (hψ : IsRestr N U N' e m σ ψ)
    (V' : U.toScheme.Opens) (t' : N'.val.obj (op V')) :
    ((preimageToSymSpec N U N' e m σ).app (symSpecToBase N' ⁻¹ᵁ V')).hom
      (cyclicCoverGenerator N' m ψ V'
        (symPow N' ((cyclicCoverSituation N').symmetricAlgebraGen.val.app (op V') t') m)) = 0 := by
  have hh : symSpecToBase N' ⁻¹ᵁ V' ≤
      toSymSpec N U N' e ⁻¹ᵁ (symSpecToBase N ⁻¹ᵁ (U.ι ''ᵁ V')) := by
    rw [← preimage_toSymSpec N U N' e]
    exact (symSpecToBase N').preimage_mono (U.ι.preimage_image_eq V').ge
  have hkG : preimageToSymSpec N U N' e m σ ⁻¹ᵁ (symSpecToBase N' ⁻¹ᵁ V') ≤
      (preimageToSymSpec N U N' e m σ ≫ toSymSpec N U N' e) ⁻¹ᵁ
        (symSpecToBase N ⁻¹ᵁ (U.ι ''ᵁ V')) := (preimageToSymSpec N U N' e m σ).preimage_mono hh
  have hkG' : preimageToSymSpec N U N' e m σ ⁻¹ᵁ (symSpecToBase N' ⁻¹ᵁ V') ≤
      ((cyclicCoverToBase N m σ ⁻¹ᵁ U).ι ≫ (cyclicCoverIdeal N m σ).subschemeι) ⁻¹ᵁ
        (symSpecToBase N ⁻¹ᵁ (U.ι ''ᵁ V')) := by
    rw [← preimageToSymSpec_toSymSpec N U N' e m σ]; exact hkG
  have e₁ : ((preimageToSymSpec N U N' e m σ).app (symSpecToBase N' ⁻¹ᵁ V')).hom
      (symSpecFunction N' 1 V'
        ((cyclicCoverSituation N').symmetricAlgebraGen.val.app (op V') t')) =
      (((cyclicCoverToBase N m σ ⁻¹ᵁ U).ι ≫ (cyclicCoverIdeal N m σ).subschemeι).appLE _ _
        hkG').hom (symSpecFunction N 1 (U.ι ''ᵁ V')
          ((cyclicCoverSituation N).symmetricAlgebraGen.val.app (op (U.ι ''ᵁ V'))
          (e.hom.val.app (op V') t'))) := by
    rw [← toSymSpec_appLE' N U N' e V' t' hh, ← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE,
      Scheme.Hom.appLE_comp_appLE _ _ _ _ _ hh le_rfl,
      appLE_congr_hom (preimageToSymSpec_toSymSpec N U N' e m σ) _ _ hkG hkG']
  unfold cyclicCoverGenerator
  rw [map_sub, symSpecFunction_symPow, map_pow, e₁, ← map_pow, ← symSpecFunction_symPow]
  set x := symPow N ((cyclicCoverSituation N).symmetricAlgebraGen.val.app (op (U.ι ''ᵁ V'))
    (e.hom.val.app (op V') t')) m
  have hψx : ψ.val.app (op V') (symPow N'
      ((cyclicCoverSituation N').symmetricAlgebraGen.val.app (op V') t') m) =
      σ.val.app (op (U.ι ''ᵁ V')) x := by
    have h := hψ V' (fun _ => t') _ x (incl_symPow_eq_prod N' V' t' m)
      (incl_symPow_eq_prod N _ _ m)
    rw [Scheme.Opens.ι_appIso, Iso.refl_inv] at h
    exact h
  rw [hψx, sub_eq_zero]
  have hO₁ : preimageToSymSpec N U N' e m σ ⁻¹ᵁ (symSpecToBase N' ⁻¹ᵁ V') ≤
      (cyclicCoverToBase N m σ ⁻¹ᵁ U).ι ⁻¹ᵁ (cyclicCoverToBase N m σ ⁻¹ᵁ (U.ι ''ᵁ V')) := hkG'
  have hO₂ : preimageToSymSpec N U N' e m σ ⁻¹ᵁ (symSpecToBase N' ⁻¹ᵁ V') ≤
      ((cyclicCoverToBase N m σ ⁻¹ᵁ U).ι ≫ cyclicCoverToBase N m σ) ⁻¹ᵁ (U.ι ''ᵁ V') := hkG'
  have hO₃ : preimageToSymSpec N U N' e m σ ⁻¹ᵁ (symSpecToBase N' ⁻¹ᵁ V') ≤
      (preimageToSymSpec N U N' e m σ ≫ symSpecToBase N' ≫ U.ι) ⁻¹ᵁ (U.ι ''ᵁ V') := by
    rw [preimageToSymSpec_toBase_ι]; exact hO₂
  have hV : V' ≤ U.ι ⁻¹ᵁ (U.ι ''ᵁ V') := (U.ι.preimage_image_eq V').ge
  have hO₄ : preimageToSymSpec N U N' e m σ ⁻¹ᵁ (symSpecToBase N' ⁻¹ᵁ V') ≤
      (preimageToSymSpec N U N' e m σ ≫ symSpecToBase N') ⁻¹ᵁ V' := le_rfl
  have m₁ : ((cyclicCoverToBase N m σ ⁻¹ᵁ U).ι ≫ (cyclicCoverIdeal N m σ).subschemeι).appLE
      (symSpecToBase N ⁻¹ᵁ (U.ι ''ᵁ V')) _ hkG' =
      (cyclicCoverIdeal N m σ).subschemeι.app (symSpecToBase N ⁻¹ᵁ (U.ι ''ᵁ V')) ≫
        (cyclicCoverToBase N m σ ⁻¹ᵁ U).ι.appLE _ _ hO₁ := by
    rw [Scheme.Hom.app_eq_appLE (cyclicCoverIdeal N m σ).subschemeι]
    exact (Scheme.Hom.appLE_comp_appLE (cyclicCoverToBase N m σ ⁻¹ᵁ U).ι
      (cyclicCoverIdeal N m σ).subschemeι _ _ _ le_rfl hO₁).symm
  have m₂ : (cyclicCoverToBase N m σ).app (U.ι ''ᵁ V') ≫
      (cyclicCoverToBase N m σ ⁻¹ᵁ U).ι.appLE _ _ hO₁ =
      ((cyclicCoverToBase N m σ ⁻¹ᵁ U).ι ≫ cyclicCoverToBase N m σ).appLE _ _ hO₂ := by
    rw [Scheme.Hom.app_eq_appLE (cyclicCoverToBase N m σ)]
    exact Scheme.Hom.appLE_comp_appLE (cyclicCoverToBase N m σ ⁻¹ᵁ U).ι (cyclicCoverToBase N m σ)
      _ _ _ le_rfl hO₁
  have m₃ : ((cyclicCoverToBase N m σ ⁻¹ᵁ U).ι ≫ cyclicCoverToBase N m σ).appLE _ _ hO₂ =
      U.ι.appLE (U.ι ''ᵁ V') V' hV ≫
        (preimageToSymSpec N U N' e m σ ≫ symSpecToBase N').appLE _ _ hO₄ := by
    rw [appLE_congr_hom (preimageToSymSpec_toBase_ι N U N' e m σ).symm _ _ hO₂ hO₃]
    exact (Scheme.Hom.appLE_comp_appLE (preimageToSymSpec N U N' e m σ ≫ symSpecToBase N') U.ι
      _ _ _ hV hO₄).symm
  have m₄ : U.ι.appLE (U.ι ''ᵁ V') V' hV = 𝟙 _ := by
    rw [Scheme.Opens.ι_appLE]
    exact X.presheaf.map_id _
  have m₅ : (preimageToSymSpec N U N' e m σ ≫ symSpecToBase N').appLE _ _ hO₄ =
      (symSpecToBase N').app V' ≫
        (preimageToSymSpec N U N' e m σ).app (symSpecToBase N' ⁻¹ᵁ V') := by
    rw [Scheme.Hom.app_eq_appLE (preimageToSymSpec N U N' e m σ),
      Scheme.Hom.app_eq_appLE (symSpecToBase N')]
    exact (Scheme.Hom.appLE_comp_appLE (preimageToSymSpec N U N' e m σ) (symSpecToBase N')
      _ _ _ le_rfl le_rfl).symm
  have hx := cyclicCoverAlgebraIncl_self N m σ (U.ι ''ᵁ V') x
  unfold cyclicCoverAlgebraIncl at hx
  have total : (cyclicCoverToBase N m σ).app (U.ι ''ᵁ V') ≫
      (cyclicCoverToBase N m σ ⁻¹ᵁ U).ι.appLE _ _ hO₁ =
      (symSpecToBase N').app V' ≫
        (preimageToSymSpec N U N' e m σ).app (symSpecToBase N' ⁻¹ᵁ V') := by
    rw [m₂, m₃, m₄]
    exact (Category.id_comp _).trans m₅
  rw [m₁, CommRingCat.comp_apply, hx]
  exact ConcreteCategory.congr_hom total (σ.val.app (op (U.ι ''ᵁ V')) x)

/-- **The pulled-back generators of `N'` vanish on `p⁻¹(U)`.** -/
private theorem preimageToSymSpec_cyclicCoverGenerator (hψ : IsRestr N U N' e m σ ψ)
    (W' : U.toScheme.Opens)
    (u' : ((cyclicCoverSituation N').symmetricAlgebra.piece (m : ℤ)).val.obj (op W')) :
    ((preimageToSymSpec N U N' e m σ).app (symSpecToBase N' ⁻¹ᵁ W')).hom
      (cyclicCoverGenerator N' m ψ W' u') = 0 := by
  refine app_cyclicCoverGenerator_eq_zero (M := N') (m := m) (τ := ψ) _ W' u' fun z hz => ?_
  obtain ⟨V', hV'W', hz', t', ht'⟩ := exists_generator (M := N') W' _ hz
  refine ⟨V', hV'W', _, le_rfl, hz', ?_⟩
  obtain ⟨a, ha⟩ := (symPow_smul_bijective N' V' t' ht' V' le_rfl m).2
    (((cyclicCoverSituation N').symmetricAlgebra.piece (m : ℤ)).val.map (homOfLE hV'W').op u')
  rw [← ha, cyclicCoverGenerator_smul, map_mul, Scheme.Hom.appLE_eq_app,
    preimageToSymSpec_cyclicCoverGenerator_symPow N U N' e m σ ψ hψ V'
      (N'.val.map (homOfLE (le_refl V')).op t'), mul_zero]

/-- `p⁻¹(U)` maps to the cyclic cover of `N'`. -/
private noncomputable def preimageToCover (hψ : IsRestr N U N' e m σ ψ) :
    (cyclicCoverToBase N m σ ⁻¹ᵁ U).toScheme ⟶ cyclicCover N' m ψ :=
  IsClosedImmersion.lift (cyclicCoverIdeal N' m ψ).subschemeι (preimageToSymSpec N U N' e m σ) (by
    rw [Scheme.IdealSheafData.ker_subschemeι]
    exact cyclicCoverIdeal_le_ker N' m ψ _
      (preimageToSymSpec_cyclicCoverGenerator N U N' e m σ ψ hψ))

@[reassoc]
private theorem preimageToCover_subschemeι (hψ : IsRestr N U N' e m σ ψ) :
    preimageToCover N U N' e m σ ψ hψ ≫ (cyclicCoverIdeal N' m ψ).subschemeι =
      preimageToSymSpec N U N' e m σ :=
  IsClosedImmersion.lift_fac _ _ _

/-- The part `p⁻¹(U)` of the cyclic cover of `N` over `U` is isomorphic to the cyclic cover
of `N'`. -/
private noncomputable def preimageCoverIso (hψ : IsRestr N U N' e m σ ψ) :
    (cyclicCoverToBase N m σ ⁻¹ᵁ U).toScheme ≅ cyclicCover N' m ψ where
  hom := preimageToCover N U N' e m σ ψ hψ
  inv := coverToPreimage N U N' e m σ ψ hψ
  hom_inv_id := by
    rw [← cancel_mono (cyclicCoverToBase N m σ ⁻¹ᵁ U).ι,
      ← cancel_mono (cyclicCoverIdeal N m σ).subschemeι, Category.assoc, Category.assoc,
      coverToPreimage_ι_assoc, coverToCover_subschemeι, preimageToCover_subschemeι_assoc,
      preimageToSymSpec_toSymSpec, Category.id_comp]
  inv_hom_id := by
    rw [← cancel_mono (cyclicCoverIdeal N' m ψ).subschemeι, Category.assoc,
      preimageToCover_subschemeι, Category.id_comp, preimageToSymSpec,
      ← cancel_mono (symSpecIso N U N' e).hom, Category.assoc, Category.assoc, Iso.inv_hom_id,
      Category.comp_id, ← cancel_mono (symSpecToBase N ⁻¹ᵁ U).ι, Category.assoc,
      preimageToPreimage_ι, Category.assoc, symSpecIso_hom_ι, coverToPreimage_ι_assoc,
      coverToCover_subschemeι]

private theorem preimageCoverIso_hom_toBase (hψ : IsRestr N U N' e m σ ψ) :
    (preimageCoverIso N U N' e m σ ψ hψ).hom ≫ cyclicCoverToBase N' m ψ =
      cyclicCoverToBase N m σ ∣_ U := by
  rw [← cancel_mono U.ι, morphismRestrict_ι, Category.assoc]
  have h : (preimageCoverIso N U N' e m σ ψ hψ).hom = preimageToCover N U N' e m σ ψ hψ := rfl
  have h' : cyclicCoverToBase N' m ψ =
      (cyclicCoverIdeal N' m ψ).subschemeι ≫ symSpecToBase N' := rfl
  rw [h, h', Category.assoc, preimageToCover_subschemeι_assoc, preimageToSymSpec_toBase_ι]

@[reassoc]
private theorem symSpecIso_inv_toSymSpec :
    (symSpecIso N U N' e).inv ≫ toSymSpec N U N' e = (symSpecToBase N ⁻¹ᵁ U).ι := by
  rw [← symSpecIso_hom_ι, Iso.inv_hom_id_assoc]

private theorem preimageCoverIso_scaling (hψ : IsRestr N U N' e m σ ψ)
    (ζ : Γ(X, ⊤)ˣ) (hζ : ζ ^ m = 1) (ζ' : Γ(U.toScheme, ⊤)ˣ) (hζ' : ζ' ^ m = 1)
    (hζζ' : (ζ' : Γ(U.toScheme, ⊤)) = U.ι.appTop (ζ : Γ(X, ⊤)))
    (h : cyclicCoverToBase N m σ ⁻¹ᵁ U ≤
      cyclicCoverScaling N m σ ζ hζ ⁻¹ᵁ (cyclicCoverToBase N m σ ⁻¹ᵁ U)) :
    (cyclicCoverScaling N m σ ζ hζ).resLE _ _ h ≫ (preimageCoverIso N U N' e m σ ψ hψ).hom =
      (preimageCoverIso N U N' e m σ ψ hψ).hom ≫ cyclicCoverScaling N' m ψ ζ' hζ' := by
  have hh : (preimageCoverIso N U N' e m σ ψ hψ).hom = preimageToCover N U N' e m σ ψ hψ := rfl
  rw [hh, ← cancel_mono (cyclicCoverIdeal N' m ψ).subschemeι, Category.assoc, Category.assoc,
    preimageToCover_subschemeι, cyclicCoverScaling_subschemeι, preimageToCover_subschemeι_assoc,
    preimageToSymSpec, Category.assoc, ← cancel_mono (symSpecIso N U N' e).hom, Category.assoc,
    Category.assoc, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    ← cancel_mono (symSpecToBase N ⁻¹ᵁ U).ι, Category.assoc, Category.assoc, Category.assoc,
    Category.assoc, preimageToPreimage_ι, symSpecIso_hom_ι,
    symSpecScaling_toSymSpec N U N' e ζ ζ' hζζ',
    symSpecIso_inv_toSymSpec_assoc, preimageToPreimage_ι_assoc, Scheme.Hom.resLE_comp_ι_assoc,
    cyclicCoverScaling_subschemeι]

end CoverIso

section Generic

variable {Y : Scheme.{u}} (M : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M]

omit [SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M] in
private theorem isIso_of_bijective {M' : Y.Modules} (φ : M ⟶ M')
    (h : ∀ W : Y.Opens, Function.Bijective (φ.val.app (op W))) : IsIso φ := by
  have h₁ : IsIso ((Scheme.Modules.toPresheaf Y).map φ) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro W
    exact (ConcreteCategory.isIso_iff_bijective _).mpr (h W.unop)
  exact isIso_of_reflects_iso φ (Scheme.Modules.toPresheaf Y)

private theorem algebraSheafIncl_injective (k : ℕ) (W : Y.Opens) :
    Function.Injective ((cyclicCoverSituation M).algebraSheafIncl k W) := by
  intro x y h
  refine modules_eq_of_affine _ x y fun V hV => ?_
  refine totalFunction_injective (cyclicCoverSituation M) V k ?_
  change symSpecFunction M k V.1 _ = symSpecFunction M k V.1 _
  rw [← symSpecFunction_restrict M k hV x, ← symSpecFunction_restrict M k hV y]
  unfold symSpecFunction
  rw [h]

omit [SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M] in
/-- Bijectivity of a morphism of modules on sections is local. -/
private theorem bijective_of_local {M' : Y.Modules} (φ : M ⟶ M') (W : Y.Opens)
    (H : ∀ y ∈ W, ∃ V : Y.Opens, V ≤ W ∧ y ∈ V ∧
      ∀ V'' : Y.Opens, V'' ≤ V → Function.Bijective (φ.val.app (op V''))) :
    Function.Bijective (φ.val.app (op W)) := by
  choose V hVW hyV hbij using H
  let F : TopCat.Sheaf Ab.{u} Y := ⟨M.val.presheaf, M.isSheaf⟩
  let G : TopCat.Sheaf Ab.{u} Y := ⟨M'.val.presheaf, M'.isSheaf⟩
  let C : {y // y ∈ W} → Y.Opens := fun y => V y.1 y.2
  have hcov : W ≤ iSup C := fun y hy => Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hyV y hy⟩
  have hnat : ∀ {A B : Y.Opens} (h : B ≤ A) (x : M.val.obj (op A)),
      φ.val.app (op B) (M.val.map (homOfLE h).op x) =
        M'.val.map (homOfLE h).op (φ.val.app (op A) x) :=
    fun h x => PresheafOfModules.naturality_apply φ.val (homOfLE h).op x
  refine ⟨fun x x' hx => ?_, fun c => ?_⟩
  · refine TopCat.Sheaf.eq_of_locally_eq' F C W (fun i => homOfLE (hVW i.1 i.2)) hcov x x'
      fun i => ?_
    exact (hbij i.1 i.2 _ le_rfl).1 ((hnat (hVW i.1 i.2) x).trans
      ((congrArg _ hx).trans (hnat (hVW i.1 i.2) x').symm))
  · choose x hx using fun i : {y // y ∈ W} => (hbij i.1 i.2 _ le_rfl).2
      (M'.val.map (homOfLE (hVW i.1 i.2)).op c)
    obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' F C W
      (fun i => homOfLE (hVW i.1 i.2)) hcov x (by
        intro i j
        refine (hbij i.1 i.2 _ inf_le_left).1 ?_
        refine (hnat (A := C i) (B := C i ⊓ C j) inf_le_left (x i)).trans ?_
        refine Eq.trans ?_ (hnat (A := C j) (B := C i ⊓ C j) inf_le_right (x j)).symm
        rw [hx, hx, modules_map_map, modules_map_map])
    refine ⟨s, TopCat.Sheaf.eq_of_locally_eq' G C W (fun i => homOfLE (hVW i.1 i.2)) hcov _ _
      fun i => ?_⟩
    refine (hnat (hVW i.1 i.2) s).symm.trans ?_
    exact (congrArg _ (hs i)).trans (hx i)

/-- The product `g₀ ⋯ g_{k-1}` of degree-one local sections in a graded algebra. -/
private noncomputable def prodGen (A : SheafOfModules.GradedAlgebra.{u, u} Y.ringCatSheaf)
    (W : (Y.Opens)ᵒᵖ) : ∀ k : ℕ, (Fin k → (A.piece 1).val.obj W) → (A.piece (k : ℤ)).val.obj W
  | 0, _ => A.one.eval W
  | k + 1, g => (eqToHom (congrArg A.piece (Nat.cast_succ k).symm)).val.app W
      ((A.mul (k : ℤ) 1).app W (prodGen A W k (g ∘ Fin.castSucc)) (g (Fin.last k)))

private theorem incl_prodGen (W : Y.Opens) : ∀ (k : ℕ)
    (g : Fin k → ((cyclicCoverSituation M).symmetricAlgebra.piece 1).val.obj (op W)),
    (cyclicCoverSituation M).algebraSheafIncl k W
        (prodGen (cyclicCoverSituation M).symmetricAlgebra (op W) k g) =
      ∏ i, (cyclicCoverSituation M).algebraSheafIncl 1 W (g i)
  | 0, g => by
    rw [Fin.prod_univ_zero]
    exact (cyclicCoverSituation M).algebraSheafIncl_one W
  | k + 1, g => by
    rw [prodGen, incl_cast M W (Nat.cast_succ k).symm,
      ← (cyclicCoverSituation M).algebraSheafIncl_mul, incl_prodGen W k, Fin.prod_univ_castSucc]
    rfl

private theorem unitalHom_cast {A B : SheafOfModules.GradedAlgebra.{u, u} Y.ringCatSheaf}
    (φ : A.UnitalHom B) (W : (Y.Opens)ᵒᵖ) {n n' : ℤ} (h : n = n') (y : (A.piece n).val.obj W) :
    (φ.app n').val.app W ((eqToHom (congrArg A.piece h)).val.app W y) =
      (eqToHom (congrArg B.piece h)).val.app W ((φ.app n).val.app W y) := by
  subst h; rfl

private theorem unitalHom_prodGen {A B : SheafOfModules.GradedAlgebra.{u, u} Y.ringCatSheaf}
    (φ : A.UnitalHom B) (W : (Y.Opens)ᵒᵖ) : ∀ (k : ℕ) (g : Fin k → (A.piece 1).val.obj W),
    (φ.app k).val.app W (prodGen A W k g) = prodGen B W k (fun i => (φ.app 1).val.app W (g i))
  | 0, g => φ.map_one W
  | k + 1, g => by
    rw [prodGen, unitalHom_cast φ W (Nat.cast_succ k).symm, φ.map_mul, unitalHom_prodGen φ W k]
    rfl

end Generic

section Restriction

private theorem restrictGradedAlgebra_cast (A : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf)
    (W : U.toScheme.Opens) {n n' : ℤ} (h : n = n') (y : (A.piece n).val.obj (op (U.ι ''ᵁ W))) :
    (eqToHom (congrArg (Stacks.AlgebraicGeometry.RelativeProjBridge.restrictGradedAlgebra A U).piece
      h)).val.app (op W) y = (eqToHom (congrArg A.piece h)).val.app (op (U.ι ''ᵁ W)) y := by
  subst h; rfl

private theorem prodGen_restrict (A : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf)
    (W : U.toScheme.Opens) : ∀ (k : ℕ) (g : Fin k → (A.piece 1).val.obj (op (U.ι ''ᵁ W))),
    prodGen (Stacks.AlgebraicGeometry.RelativeProjBridge.restrictGradedAlgebra A U) (op W) k g =
      prodGen A (op (U.ι ''ᵁ W)) k g
  | 0, g => rfl
  | k + 1, g => by
    dsimp only [prodGen]
    refine (restrictGradedAlgebra_cast (U := U) A W (Nat.cast_succ k).symm _).trans ?_
    rw [← prodGen_restrict A W k]
    rfl

/-- The degree-one generator of `Sym(N)|_U` on `N'`. -/
private noncomputable def restrictGen : N' ⟶
    (Stacks.AlgebraicGeometry.RelativeProjBridge.restrictGradedAlgebra
      (cyclicCoverSituation N).symmetricAlgebra U).piece 1 :=
  e.hom ≫ (Scheme.Modules.restrictFunctor U.ι).map (cyclicCoverSituation N).symmetricAlgebraGen

omit [SheafOfModules.IsInvertible U.toScheme.sheaf.obj U.toScheme.ringCatSheaf.property N'] in
private theorem pairwiseCommutes_restrictGen :
    SheafOfModules.GradedAlgebra.PairwiseCommutes (restrictGen N U N' e) := fun V _ _ =>
  eq_of_heq ((cyclicCoverSituation N).symmetricAlgebra_mul_comm 1 1 (op (U.ι ''ᵁ V.unop)) _ _)

/-- `Sym(N') ⟶ Sym(N)|_U`. -/
private noncomputable def symRestrict :
    SheafOfModules.GradedAlgebra.UnitalHom (cyclicCoverSituation N').symmetricAlgebra
      (Stacks.AlgebraicGeometry.RelativeProjBridge.restrictGradedAlgebra
        (cyclicCoverSituation N).symmetricAlgebra U) :=
  (cyclicCoverSituation N').isSymmetricAlgebra_symmetricAlgebra.isUniversal.desc _
    (restrictGen N U N' e) (pairwiseCommutes_restrictGen N U N' e)

private theorem symRestrict_gen (W : U.toScheme.Opens) (t : N'.val.obj (op W)) :
    ((symRestrict N U N' e).app 1).val.app (op W)
        ((cyclicCoverSituation N').symmetricAlgebraGen.val.app (op W) t) =
      (cyclicCoverSituation N).symmetricAlgebraGen.val.app (op (U.ι ''ᵁ W))
        (e.hom.val.app (op W) t) :=
  congrArg (fun f => f.val.app (op W) t)
    ((cyclicCoverSituation N').isSymmetricAlgebra_symmetricAlgebra.isUniversal.desc_extends _
      (restrictGen N U N' e) (pairwiseCommutes_restrictGen N U N' e))

omit [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
  [SheafOfModules.IsInvertible U.toScheme.sheaf.obj U.toScheme.ringCatSheaf.property N'] in
/-- A generator of `N` over `V ⊆ X` gives a generator of `N'` over `ι⁻¹ V`. -/
private theorem generator_transport (V : X.Opens) (t : N.val.obj (op V))
    (ht : ∀ (V'' : X.Opens) (h : V'' ≤ V),
      Function.Bijective fun a : X.ringCatSheaf.obj.obj (op V'') =>
        a • (N.val.map (homOfLE h).op t : N.val.obj (op V''))) :
    ∀ (W : U.toScheme.Opens) (h : W ≤ U.ι ⁻¹ᵁ V),
      Function.Bijective fun a : U.toScheme.ringCatSheaf.obj.obj (op W) =>
        a • (N'.val.map (homOfLE h).op (e.inv.val.app (op (U.ι ⁻¹ᵁ V))
          (N.val.map (homOfLE (U.ι.image_preimage_le V)).op t)) : N'.val.obj (op W)) := by
  intro W h
  have hW : U.ι ''ᵁ W ≤ V := (U.ι.image_mono h).trans (U.ι.image_preimage_le V)
  have key : (fun a : U.toScheme.ringCatSheaf.obj.obj (op W) =>
      a • (N'.val.map (homOfLE h).op (e.inv.val.app (op (U.ι ⁻¹ᵁ V))
        (N.val.map (homOfLE (U.ι.image_preimage_le V)).op t)) : N'.val.obj (op W))) =
      (e.inv.val.app (op W)) ∘ (fun a : X.ringCatSheaf.obj.obj (op (U.ι ''ᵁ W)) =>
        a • (N.val.map (homOfLE hW).op t : N.val.obj (op (U.ι ''ᵁ W)))) := by
    funext a
    erw [← PresheafOfModules.naturality_apply e.inv.val]
    have hmm : (N.restrict U.ι).val.map (homOfLE h).op
        (N.val.map (homOfLE (U.ι.image_preimage_le V)).op t) = N.val.map (homOfLE hW).op t := by
      show N.val.map (homOfLE (U.ι.image_mono h)).op
        (N.val.map (homOfLE (U.ι.image_preimage_le V)).op t) = _
      exact modules_map_map N _ _ t
    erw [hmm]
    refine ((e.inv.val.app (op W)).hom.map_smul a _).symm.trans ?_
    change e.inv.val.app (op W)
      ((show X.ringCatSheaf.obj.obj (op (U.ι ''ᵁ W)) from (U.ι.appIso W).inv a) •
        (show N.val.obj (op (U.ι ''ᵁ W)) from N.val.map (homOfLE hW).op t)) = _
    rw [Scheme.Opens.ι_appIso]
    rfl
  rw [key]
  exact ((PresheafOfModules.toPresheaf _ ⋙ (CategoryTheory.evaluation _ _).obj
    (op W) ⋙ forget _).mapIso
      ((SheafOfModules.forget _).mapIso e.symm)).toEquiv.bijective.comp (ht _ hW)

variable (m : ℕ)
    (σ : (cyclicCoverSituation N).symmetricAlgebra.piece (m : ℤ) ⟶
      SheafOfModules.unit X.ringCatSheaf)

omit [SheafOfModules.IsInvertible U.toScheme.sheaf.obj U.toScheme.ringCatSheaf.property N'] in
/-- Off the zero scheme, `⟨tᵐ, s⟩` does not vanish, for a generator `t` of `N`. -/
private theorem mem_basicOpen_sigma_symPow (y : X) (hy : y ∉ (zeroSchemeIdeal N m σ).support)
    (V : X.Opens) (hyV : y ∈ V) (t : N.val.obj (op V))
    (ht : ∀ (V'' : X.Opens) (h : V'' ≤ V),
      Function.Bijective fun a : X.ringCatSheaf.obj.obj (op V'') =>
        a • (N.val.map (homOfLE h).op t : N.val.obj (op V''))) :
    y ∈ X.basicOpen (σ.val.app (op V)
      (symPow N ((cyclicCoverSituation N).symmetricAlgebraGen.val.app (op V) t) m) :
        Γ(X, V)) := by
  set f : Γ(X, V) := σ.val.app (op V)
    (symPow N ((cyclicCoverSituation N).symmetricAlgebraGen.val.app (op V) t) m)
  by_contra hf
  apply hy
  rw [Scheme.IdealSheafData.mem_support_iff]
  intro V₁
  rw [Scheme.mem_zeroLocus_iff]
  intro g hg hyg
  have hg' := Scheme.IdealSheafData.ideal_ofIdeals_le _ _ hg
  have hyV₁ : y ∈ V₁.1 := X.basicOpen_le g hyg
  have h₃ : V₁.1 ⊓ V ≤ V := inf_le_right
  have hspan : (Ideal.span (Set.range (σ.val.app (op V₁.1))) : Ideal Γ(X, V₁.1)) ≤
      (Ideal.span {X.presheaf.map (homOfLE h₃).op f}).comap
        (X.presheaf.map (homOfLE (inf_le_left : V₁.1 ⊓ V ≤ V₁.1)).op).hom := by
    rw [Ideal.span_le]
    rintro _ ⟨w, rfl⟩
    obtain ⟨a, ha⟩ := (symPow_smul_bijective N V t ht (V₁.1 ⊓ V) h₃ m).2
      (((cyclicCoverSituation N).symmetricAlgebra.piece (m : ℤ)).val.map
        (homOfLE (inf_le_left : V₁.1 ⊓ V ≤ V₁.1)).op w)
    refine Ideal.mem_comap.mpr ?_
    have hn : (X.presheaf.map (homOfLE (inf_le_left : V₁.1 ⊓ V ≤ V₁.1)).op).hom
        (σ.val.app (op V₁.1) w) = σ.val.app (op (V₁.1 ⊓ V))
          (((cyclicCoverSituation N).symmetricAlgebra.piece (m : ℤ)).val.map
            (homOfLE (inf_le_left : V₁.1 ⊓ V ≤ V₁.1)).op w) :=
      (PresheafOfModules.naturality_apply σ.val _ w).symm
    rw [hn, ← ha]
    erw [(σ.val.app _).hom.map_smul]
    refine Ideal.mul_mem_left _ a (Ideal.subset_span ?_)
    erw [gen_nat N V _ h₃ t, ← symPow_map, PresheafOfModules.naturality_apply]
    rfl
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (hspan hg')
  have : y ∈ X.basicOpen ((X.presheaf.map (homOfLE (inf_le_left : V₁.1 ⊓ V ≤ V₁.1)).op).hom g) := by
    rw [Scheme.basicOpen_res]; exact ⟨⟨hyV₁, hyV⟩, hyg⟩
  rw [← hc, Scheme.basicOpen_mul, Scheme.basicOpen_res] at this
  exact hf this.2.2

/-- The restriction `σ|_U : Symᵐ(N') ⟶ 𝒪_U`. -/
private noncomputable def psi0 :
    (cyclicCoverSituation N').symmetricAlgebra.piece (m : ℤ) ⟶
      SheafOfModules.unit U.toScheme.ringCatSheaf :=
  (symRestrict N U N' e).app m ≫ (Scheme.Modules.restrictFunctor U.ι).map σ ≫
    (Scheme.Modules.restrictUnitIso U.ι).hom

private theorem psi0_apply (W : U.toScheme.Opens)
    (x : ((cyclicCoverSituation N').symmetricAlgebra.piece (m : ℤ)).val.obj (op W)) :
    (psi0 N U N' e m σ).val.app (op W) x =
      (U.ι.appIso W).hom (σ.val.app (op (U.ι ''ᵁ W))
        (((symRestrict N U N' e).app m).val.app (op W) x)) := rfl

private theorem isRestr_psi0 : IsRestr N U N' e m σ (psi0 N U N' e m σ) := by
  intro W t u' u h1 h2
  have hu' : u' = prodGen (cyclicCoverSituation N').symmetricAlgebra (op W) m
      (fun i => (cyclicCoverSituation N').symmetricAlgebraGen.val.app (op W) (t i)) :=
    algebraSheafIncl_injective N' m W (h1.trans (incl_prodGen N' W m _).symm)
  have hRu : ((symRestrict N U N' e).app m).val.app (op W) u' = u := by
    rw [hu', unitalHom_prodGen]
    have hfun : (fun i => ((symRestrict N U N' e).app 1).val.app (op W)
        ((cyclicCoverSituation N').symmetricAlgebraGen.val.app (op W) (t i))) =
        (fun i => (cyclicCoverSituation N).symmetricAlgebraGen.val.app (op (U.ι ''ᵁ W))
          (e.hom.val.app (op W) (t i))) := funext fun i => symRestrict_gen N U N' e W (t i)
    refine (congrArg (prodGen _ (op W) m) hfun).trans ((prodGen_restrict (U := U) _ W m _).trans ?_)
    apply algebraSheafIncl_injective N m (U.ι ''ᵁ W)
    rw [incl_prodGen, h2]
    rfl
  rw [psi0_apply, hRu, Scheme.Opens.ι_appIso]
  rfl

private theorem psi0_bijective (hU : ∀ x ∈ U, x ∉ (zeroSchemeIdeal N m σ).support)
    (W : U.toScheme.Opens) : Function.Bijective ((psi0 N U N' e m σ).val.app (op W)) := by
  refine bijective_of_local _ (psi0 N U N' e m σ) W fun x hx => ?_
  have hy : U.ι x ∈ U.ι ''ᵁ W := ⟨x, hx, rfl⟩
  obtain ⟨V, hVW, hyV, t, ht⟩ := exists_generator (M := N) (U.ι ''ᵁ W) _ hy
  have hyf := mem_basicOpen_sigma_symPow N m σ (U.ι x) (hU _ x.2) V hyV t ht
  set f : Γ(X, V) := σ.val.app (op V)
    (symPow N ((cyclicCoverSituation N).symmetricAlgebraGen.val.app (op V) t) m) with hfdef
  have hV₂ : X.basicOpen f ≤ V := X.basicOpen_le f
  set t₂ : N.val.obj (op (X.basicOpen f)) := N.val.map (homOfLE hV₂).op t
  have ht₂ : ∀ (V'' : X.Opens) (h : V'' ≤ X.basicOpen f),
      Function.Bijective fun a : X.ringCatSheaf.obj.obj (op V'') =>
        a • (N.val.map (homOfLE h).op t₂ : N.val.obj (op V'')) := by
    intro V'' h
    have := ht V'' (h.trans hV₂)
    simp only [t₂, modules_map_map]
    exact this
  refine ⟨U.ι ⁻¹ᵁ X.basicOpen f,
    (U.ι.preimage_mono (hV₂.trans hVW)).trans (U.ι.preimage_image_eq W).le, hyf,
    fun W'' hW'' => ?_⟩
  have ht' := generator_transport N U N' e _ t₂ ht₂
  set t' := e.inv.val.app (op (U.ι ⁻¹ᵁ X.basicOpen f))
    (N.val.map (homOfLE (U.ι.image_preimage_le (X.basicOpen f))).op t₂)
  have hb := symPow_smul_bijective N' _ t' ht' W'' hW'' m
  set sW := symPow N' ((cyclicCoverSituation N').symmetricAlgebraGen.val.app (op W'')
    (N'.val.map (homOfLE hW'').op t')) m
  -- the value on the basis vector
  have hval : (psi0 N U N' e m σ).val.app (op W'') sW =
      U.toScheme.presheaf.map (homOfLE hW'').op ((U.ι.app (X.basicOpen f)).hom
        (X.presheaf.map (homOfLE hV₂).op f)) := by
    have h1 : sW = ((cyclicCoverSituation N').symmetricAlgebra.piece (m : ℤ)).val.map
        (homOfLE hW'').op (symPow N' ((cyclicCoverSituation N').symmetricAlgebraGen.val.app
          (op (U.ι ⁻¹ᵁ X.basicOpen f)) t') m) := by
      simp only [sW]
      erw [gen_nat N' _ _ hW'' t', ← symPow_map]
    have hσ : σ.val.app (op (X.basicOpen f)) (symPow N
        ((cyclicCoverSituation N).symmetricAlgebraGen.val.app (op (X.basicOpen f)) t₂) m) =
        X.presheaf.map (homOfLE hV₂).op f := by
      simp only [t₂]
      erw [gen_nat N V _ hV₂ t, ← symPow_map, PresheafOfModules.naturality_apply]
      rfl
    rw [h1, PresheafOfModules.naturality_apply,
      isRestr_symPow N U N' e m σ (isRestr_psi0 N U N' e m σ) _ t₂, hσ]
    rfl
  have hunit : IsUnit (show Γ(U.toScheme, W'') from (psi0 N U N' e m σ).val.app (op W'') sW) := by
    rw [hval]
    exact ((X.toRingedSpace.isUnit_res_basicOpen f).map (U.ι.app (X.basicOpen f)).hom).map _
  have hcomp : (psi0 N U N' e m σ).val.app (op W'') ∘
      (fun a : U.toScheme.ringCatSheaf.obj.obj (op W'') => a • sW) =
      fun a => (show Γ(U.toScheme, W'') from a) *
        (show Γ(U.toScheme, W'') from (psi0 N U N' e m σ).val.app (op W'') sW) := by
    funext a
    exact ((psi0 N U N' e m σ).val.app (op W'')).hom.map_smul a sW
  refine (Function.Bijective.of_comp_iff _ hb).mp ?_
  erw [hcomp]
  exact (Units.mulRight hunit.unit).bijective

end Restriction

end Helpers

end MMP.Mori.RamifiedCoverRestriction

namespace MMP.Mori

@[expose] public section

open MMP.Mori.RamifiedCoverRestriction in
/-- **The cyclic cover is unramified off the zero scheme.** Over an open `U` disjoint from the
zero scheme of `σ`, the restriction of `σ` to `N' ≅ N|_U` is an isomorphism `ψ`, and for every
such `ψ` the part `p⁻¹(U)` of the cyclic cover is isomorphic over `U` to the unramified cyclic
cover attached to `ψ`, compatibly with the automorphisms `cyclicCoverScaling` attached to an
`m`-th root of unity `ζ` and to its restriction to `U`. -/
@[mmp "lem_km2c_ramified_cover_restriction_unramified"]
public theorem cyclicCover_restrict_of_le_compl_zeroScheme {X : Scheme.{u}} (N : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
    (m : ℕ) (σ : (cyclicCoverSituation N).symmetricAlgebra.piece (m : ℤ) ⟶
      SheafOfModules.unit X.ringCatSheaf)
    (U : X.Opens) (hU : ∀ x ∈ U, x ∉ (zeroSchemeIdeal N m σ).support) (N' : U.toScheme.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible U.toScheme.sheaf.obj
      U.toScheme.ringCatSheaf.property N']
    (e : N' ≅ N.restrict U.ι) :
    let IsRestriction : ((cyclicCoverSituation N').symmetricAlgebra.piece (m : ℤ) ⟶
        SheafOfModules.unit U.toScheme.ringCatSheaf) → Prop := fun ψ =>
      ∀ (W : U.toScheme.Opens) (t : Fin m → N'.val.obj (op W))
        (u' : ((cyclicCoverSituation N').symmetricAlgebra.piece (m : ℤ)).val.obj (op W))
        (u : ((cyclicCoverSituation N).symmetricAlgebra.piece (m : ℤ)).val.obj (op (U.ι ''ᵁ W))),
        (cyclicCoverSituation N').algebraSheafIncl m W u' =
            ∏ i, (cyclicCoverSituation N').algebraSheafIncl 1 W
              ((cyclicCoverSituation N').symmetricAlgebraGen.val.app (op W) (t i)) →
        (cyclicCoverSituation N).algebraSheafIncl m (U.ι ''ᵁ W) u =
            ∏ i, (cyclicCoverSituation N).algebraSheafIncl 1 (U.ι ''ᵁ W)
              ((cyclicCoverSituation N).symmetricAlgebraGen.val.app (op (U.ι ''ᵁ W))
                ((N.restrictAppIso U.ι W).hom (e.hom.val.app (op W) (t i)))) →
        ψ.val.app (op W) u' = (U.ι.appIso W).inv (σ.val.app (op (U.ι ''ᵁ W)) u)
    (∃ ψ : (cyclicCoverSituation N').symmetricAlgebra.piece (m : ℤ) ≅
        SheafOfModules.unit U.toScheme.ringCatSheaf, IsRestriction ψ.hom) ∧
    ∀ ψ : (cyclicCoverSituation N').symmetricAlgebra.piece (m : ℤ) ≅
        SheafOfModules.unit U.toScheme.ringCatSheaf, IsRestriction ψ.hom →
      ∃ φ : (cyclicCoverToBase N m σ ⁻¹ᵁ U).toScheme ≅ cyclicCover N' m ψ.hom,
        φ.hom ≫ unramifiedCyclicCover N' m ψ = cyclicCoverToBase N m σ ∣_ U ∧
        ∀ (ζ : Γ(X, ⊤)ˣ) (hζ : ζ ^ m = 1) (ζ' : Γ(U.toScheme, ⊤)ˣ) (hζ' : ζ' ^ m = 1),
          (ζ' : Γ(U.toScheme, ⊤)) = U.ι.appTop (ζ : Γ(X, ⊤)) →
          ∀ h : cyclicCoverToBase N m σ ⁻¹ᵁ U ≤
              cyclicCoverScaling N m σ ζ hζ ⁻¹ᵁ (cyclicCoverToBase N m σ ⁻¹ᵁ U),
            (cyclicCoverScaling N m σ ζ hζ).resLE _ _ h ≫ φ.hom =
              φ.hom ≫ cyclicCoverScaling N' m ψ.hom ζ' hζ' := by
  haveI : IsIso (psi0 N U N' e m σ) := isIso_of_bijective _ _ (psi0_bijective N U N' e m σ hU)
  exact ⟨⟨asIso (psi0 N U N' e m σ), isRestr_psi0 N U N' e m σ⟩, fun ψ hψ =>
    ⟨preimageCoverIso N U N' e m σ ψ.hom hψ, preimageCoverIso_hom_toBase N U N' e m σ ψ.hom hψ,
      fun ζ hζ ζ' hζ' => preimageCoverIso_scaling N U N' e m σ ψ.hom hψ ζ hζ ζ' hζ'⟩⟩

end

end MMP.Mori

end
