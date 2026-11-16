module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
public import MMP.AlgebraicGeometry.Singularities.Basic
public import MMP.AlgebraicGeometry.Divisor.Arithmetic
public import MMP.AlgebraicGeometry.Divisor.Pullback
import MMP.AlgebraicGeometry.Singularities.LogResolution.FloorIdealVanishing
import MMP.AlgebraicGeometry.Vanishing.SncTorsionFreeness
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueDifferent
import MMP.AlgebraicGeometry.Morphisms.FiniteCoverTrace
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms
import MMP.AlgebraicGeometry.Singularities.BlowupDiscrepancy
import MMP.AlgebraicGeometry.Morphisms.ProjectiveFieldExtension
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.Valuation
import MMP.AlgebraicGeometry.MMP.Abundance.SdltCommonBaseTwist
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalCurveNegativity
import MMP.AlgebraicGeometry.Divisor.RegularWeilCartier
import MMP.AlgebraicGeometry.Resolution.Surface.CastelnuovoContraction
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.Resolution.SncPreservingLogResolution
import MMP.AlgebraicGeometry.Singularities.DltLogTerminal
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafQuasicoherent
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.Basic
import MMP.AlgebraicGeometry.Resolution.SNCWeight.Subtraction
import StacksFrontier.AlgebraicGeometry.HigherDirectImageBaseChange.Basic

/-!
# The structure sheaf of the image of a vertical dlt floor

Let `(X, B)` be a `ℚ`-factorial projective dlt pair, with `B` a `ℚ`-divisor, over `ℂ`, and let
`f : X ⟶ R` be a projective morphism to a normal projective variety `R` with `f_* 𝒪_X = 𝒪_R`.
Suppose `K_X + B ∼_ℚ f^*H` for a `ℚ`-Cartier `ℚ`-divisor `H` on `R`. Let `S = ⌊B⌋` with its
reduced structure and let `V = f(S)` with its reduced structure. If `V ≠ R`, then
`f_* 𝒪_S = 𝒪_V`.

## Main results

* `MMP.Fourfold.isIso_app_toImage_suppScheme_of_isDltPair_of_qLinearlyEquivalent`

## Implementation notes

* `S` is the reduced closed subscheme `MMP.Mori.DivisorWithCoeffs.suppScheme` of `⌊B⌋`, with
  closed immersion `ι`. Since `S` is reduced, the scheme-theoretic image
  `(ι ≫ f).image` of `ι ≫ f` is the closed subscheme of `R` with the reduced structure on the
  closed set `f(S)`; this is `V`, and `ι ≫ f` factors as `(ι ≫ f).toImage ≫ (ι ≫ f).imageι`.
  The assertion `f_* 𝒪_S = 𝒪_V` is that the comorphism of `(ι ≫ f).toImage` is an isomorphism
  on every open of `V`.
* `f_* 𝒪_X = 𝒪_R` is written `∀ U, IsIso (f.app U)`.
* `K_X + B ∼_ℚ f^*H` is `MMP.Mori.QDivisor.QLinearlyEquivalent` with a `ℚ`-divisor `H_X` on `X`
  pinned as `f^*H` by `MMP.Mori.QDivisor.IsPullback`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori]
-/

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MMP.Mori Opposite TopologicalSpace

namespace Proof_lem_fourfold_vertical_dlt_floor_stein_image

section Image

variable {S X R : Scheme.{0}}

/-- The comorphism `𝒪_X ⟶ ι_* 𝒪_S` of a morphism `ι : S ⟶ X`, as a morphism of
`𝒪_X`-modules. -/
private noncomputable def unitHom (ι : S ⟶ X) :
    @Quiver.Hom X.Modules _ (SheafOfModules.unit X.ringCatSheaf)
      ((Scheme.Modules.pushforward ι).obj (SheafOfModules.unit S.ringCatSheaf)) :=
  SheafOfModules.unitToPushforwardObjUnit ι.toRingCatSheafHom

/-- The comorphism `𝒪_R ⟶ (ι ≫ f)_* 𝒪_S` of a composite is `𝒪_R ⟶ f_* 𝒪_X ⟶ f_* ι_* 𝒪_S`
followed by the canonical isomorphism `f_* ι_* ≅ (ι ≫ f)_*`. -/
private theorem unitHom_comp (ι : S ⟶ X) (f : X ⟶ R) :
    unitHom (ι ≫ f) = unitHom f ≫ (Scheme.Modules.pushforward f).map (unitHom ι) ≫
      ((Scheme.Modules.pushforwardComp ι f).app _).inv := by
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  ext x
  rfl

/-- `𝒪_R ⟶ (f ∘ ι)_* 𝒪_S` is an epimorphism if `𝒪_R ⟶ f_* 𝒪_X` is an isomorphism and
`f_* 𝒪_X ⟶ f_* ι_* 𝒪_S` is an epimorphism. -/
private theorem epi_unitHom_comp (ι : S ⟶ X) (f : X ⟶ R) (h₁ : IsIso (unitHom f))
    (h₂ : Epi ((Scheme.Modules.pushforward f).map (unitHom ι))) : Epi (unitHom (ι ≫ f)) := by
  rw [unitHom_comp]
  have h₃ : Epi ((Scheme.Modules.pushforwardComp ι f).app
    (SheafOfModules.unit S.ringCatSheaf)).inv := inferInstance
  exact epi_comp' (@IsIso.epi_of_iso _ _ _ _ _ h₁) (epi_comp' h₂ h₃)

/-- On sections over `U`, `unitHom q` is an isomorphism iff the comorphism `q.app U` is. -/
private theorem isIso_app_unitHom_iff (q : S ⟶ X) (U : X.Opens) :
    IsIso ((unitHom q).app U) ↔ IsIso (q.app U) := by
  rw [ConcreteCategory.isIso_iff_bijective, ConcreteCategory.isIso_iff_bijective]
  rfl

/-- `𝒪_R ⟶ f_* 𝒪_X` is an isomorphism when the comorphism of `f` is bijective on every open. -/
private theorem isIso_unitHom_of_isIso_app (f : X ⟶ R)
    (hO : ∀ U : R.Opens, IsIso (f.app U)) : IsIso (unitHom f) :=
  (Scheme.Modules.Hom.isIso_iff_isIso_app (φ := unitHom f)).mpr fun U =>
    (isIso_app_unitHom_iff f U).2 (hO U)

/-- `unitHom q` is a monomorphism when the comorphism of `q` is injective on every open. -/
private theorem mono_unitHom_of_injective (q : S ⟶ X)
    (hinj : ∀ U : X.Opens, Function.Injective (q.app U)) : Mono (unitHom q) := by
  apply (Scheme.Modules.toPresheaf _).mono_of_mono_map
  have : ∀ U, Mono (((Scheme.Modules.toPresheaf _).map (unitHom q)).app U) := fun U =>
    (AddCommGrpCat.mono_iff_injective _).2 (hinj U.unop)
  exact NatTrans.mono_of_mono_app _

/-- If `𝒪_R ⟶ g_* 𝒪_S` is an epimorphism of `𝒪_R`-modules, for `g` quasi-compact, then the
comorphism of `g.toImage` is an isomorphism on every open of the scheme-theoretic image. -/
private theorem isIso_toImage_app_of_epi (g : S ⟶ R) [QuasiCompact g] (h : Epi (unitHom g)) :
    ∀ U : g.image.Opens, IsIso (g.toImage.app U) := by
  set j := g.imageι
  set q := g.toImage
  have hqj : q ≫ j = g := g.toImage_imageι
  have hinj : ∀ U : g.image.Opens, Function.Injective (q.app U) := fun U =>
    TopCat.Presheaf.app_injective_of_stalkFunctor_map_injective (F := g.image.sheaf) q.c
      U fun x _ => g.stalkFunctor_toImage_injective x
  let ρ : (Scheme.Modules.pushforward j).obj ((Scheme.Modules.pushforward q).obj
      (SheafOfModules.unit S.ringCatSheaf)) ≅
      (Scheme.Modules.pushforward g).obj (SheafOfModules.unit S.ringCatSheaf) :=
    (Scheme.Modules.pushforwardComp q j).symm.app _ ≪≫
      (Scheme.Modules.pushforwardCongr hqj).app _
  have hfac : unitHom g = unitHom j ≫ (Scheme.Modules.pushforward j).map (unitHom q) ≫ ρ.hom := by
    refine Scheme.Modules.hom_ext _ _ fun U => ?_
    ext x
    have h1 := Scheme.Hom.congr_app hqj.symm U
    rw [Scheme.Hom.comp_app] at h1
    exact ConcreteCategory.congr_hom h1 x
  haveI : Mono (unitHom q) := mono_unitHom_of_injective q hinj
  have hpq : IsIso ((Scheme.Modules.pushforward j).map (unitHom q)) := by
    haveI := (Scheme.Modules.pullbackPushforwardAdjunction j).rightAdjoint_preservesLimits
    haveI : Mono ((Scheme.Modules.pushforward j).map (unitHom q)) :=
      (Scheme.Modules.pushforward j).map_mono _
    haveI : Epi ((Scheme.Modules.pushforward j).map (unitHom q) ≫ ρ.hom) := by
      rw [hfac] at h
      exact epi_of_epi (unitHom j) _
    haveI : Epi ((Scheme.Modules.pushforward j).map (unitHom q)) := by
      have he : (Scheme.Modules.pushforward j).map (unitHom q) =
          ((Scheme.Modules.pushforward j).map (unitHom q) ≫ ρ.hom) ≫ ρ.inv := by
        simp
      rw [he]
      exact epi_comp _ _
    exact isIso_of_mono_of_epi _
  intro U
  obtain ⟨U₀, hU₀⟩ : ∃ U₀ : R.Opens, j ⁻¹ᵁ U₀ = U := by
    obtain ⟨V, hV, hVU⟩ := j.isEmbedding.isInducing.isOpen_iff.mp U.isOpen
    exact ⟨⟨V, hV⟩, TopologicalSpace.Opens.ext hVU⟩
  subst hU₀
  exact (isIso_app_unitHom_iff q _).1
    ((Scheme.Modules.Hom.isIso_iff_isIso_app (φ := (Scheme.Modules.pushforward j).map
      (unitHom q))).mp hpq U₀)

end Image

section Homological

universe u v

/-- **The low-degree Leray injection.** For left exact functors `G : C ⥤ D` and `T : D ⥤ E`
such that `G` sends injectives to objects without `R¹T`, there is a monomorphism
`R¹T (G F) ⟶ R¹(G ⋙ T) F`. -/
private theorem exists_mono_rightDerived_one_comp {C D E : Type u} [Category.{v} C] [Category.{v} D]
    [Category.{v} E] [Abelian C] [Abelian D] [Abelian E] [EnoughInjectives C] [EnoughInjectives D]
    (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] (T : D ⥤ E) [T.Additive]
    [PreservesFiniteLimits T]
    (hacyc : ∀ I : C, Injective I → IsZero ((T.rightDerived 1).obj (G.obj I))) (F : C) :
    ∃ e : (T.rightDerived 1).obj (G.obj F) ⟶ ((G ⋙ T).rightDerived 1).obj F, Mono e := by
  letI := HasDerivedCategory.standard C
  letI := HasDerivedCategory.standard D
  letI := HasDerivedCategory.standard E
  let ι := Injective.ι F
  let S₀ : ShortComplex C := ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)
  have hS₀ : S₀.ShortExact := ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)) inferInstance inferInstance
  let S₂ : ShortComplex D := ShortComplex.mk (G.map ι) (cokernel.π (G.map ι))
    (cokernel.condition _)
  have hS₂ : S₂.ShortExact := ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)) inferInstance inferInstance
  have hGex : (S₀.map G).Exact :=
    hS₀.exact.map_of_mono_of_preservesKernel G inferInstance inferInstance
  let c : cokernel (G.map ι) ⟶ G.obj (cokernel ι) := cokernel.desc _ (G.map (cokernel.π ι))
    (by rw [← G.map_comp, cokernel.condition, G.map_zero])
  have hc : Mono c := hGex.mono_cokernelDesc
  have hcπ : cokernel.π (G.map ι) ≫ c = G.map (cokernel.π ι) := cokernel.π_desc _ _ _
  let ΔT := Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives T
  let ΔGT := Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives (G ⋙ T)
  let δ₀ : ((G ⋙ T).rightDerived 0).obj (cokernel ι) ⟶ ((G ⋙ T).rightDerived 1).obj F :=
    ΔGT.δ hS₀ 0
  let δ₂ : (T.rightDerived 0).obj (cokernel (G.map ι)) ⟶ (T.rightDerived 1).obj (G.obj F) :=
    ΔT.δ hS₂ 0
  have hδ₀ : ((G ⋙ T).rightDerived 0).map (cokernel.π ι) ≫ δ₀ = 0 := ΔGT.map_g_δ hS₀ 0
  have hδ₂ : (T.rightDerived 0).map (cokernel.π (G.map ι)) ≫ δ₂ = 0 := ΔT.map_g_δ hS₂ 0
  have hex₂ : (ShortComplex.mk _ _ hδ₂).Exact := ΔT.exact_δ₁ hS₂ 0
  have hex₀ : (ShortComplex.mk _ _ hδ₀).Exact := ΔGT.exact_δ₁ hS₀ 0
  have hepi : Epi δ₂ :=
    ΔT.epi_δ_of_map_f_eq_zero hS₂ 0 ((hacyc _ inferInstance).eq_of_tgt _ _)
  let α : (G ⋙ T).rightDerived 0 ≅ G ⋙ T.rightDerived 0 :=
    (G ⋙ T).rightDerivedZeroIsoSelf ≪≫ Functor.isoWhiskerLeft G T.rightDerivedZeroIsoSelf.symm
  have hmc : Mono ((T.rightDerived 0).map c) := by
    have h := T.rightDerivedZeroIsoSelf.hom.naturality c
    have : Mono (T.rightDerivedZeroIsoSelf.hom.app _ ≫ T.map c) := inferInstance
    rw [← h] at this
    exact mono_of_mono _ (T.rightDerivedZeroIsoSelf.hom.app _)
  have h1 := α.inv.naturality (cokernel.π ι)
  have h1' := α.hom.naturality (cokernel.π ι)
  dsimp only [Functor.comp_map] at h1 h1'
  let φ : (T.rightDerived 0).obj (cokernel (G.map ι)) ⟶ ((G ⋙ T).rightDerived 1).obj F :=
    (T.rightDerived 0).map c ≫ α.inv.app _ ≫ δ₀
  have hφ : (T.rightDerived 0).map (cokernel.π (G.map ι)) ≫ φ = 0 := by
    simp only [φ, ← Category.assoc, ← Functor.map_comp, hcπ]
    rw [h1, Category.assoc, hδ₀, comp_zero]
  let e : (T.rightDerived 1).obj (G.obj F) ⟶ ((G ⋙ T).rightDerived 1).obj F :=
    hex₂.gIsCokernel.desc (CokernelCofork.ofπ φ hφ)
  have he : δ₂ ≫ e = φ := hex₂.gIsCokernel.fac _ WalkingParallelPair.one
  refine ⟨e, ?_⟩
  rw [Preadditive.mono_iff_cancel_zero]
  intro T₀ x hx
  obtain ⟨T₁, q, hq, y, hy⟩ := surjective_up_to_refinements_of_epi δ₂ x
  have h0 : (y ≫ (T.rightDerived 0).map c ≫ α.inv.app _) ≫ δ₀ = 0 := by
    have : y ≫ δ₂ ≫ e = 0 := by rw [← Category.assoc, ← hy, Category.assoc, hx, comp_zero]
    rw [he] at this
    simpa [φ] using this
  obtain ⟨T₂, q', hq', z, hz⟩ := hex₀.exact_up_to_refinements _ h0
  have hz' : q' ≫ y = (z ≫ α.hom.app _) ≫ (T.rightDerived 0).map (cokernel.π (G.map ι)) := by
    rw [← cancel_mono ((T.rightDerived 0).map c)]
    have h2 := congrArg (· ≫ α.hom.app (cokernel ι)) hz
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id] at h2
    dsimp only [Functor.comp_obj] at h2
    rw [Category.comp_id] at h2
    rw [Category.assoc, h2, Category.assoc, Category.assoc, ← Functor.map_comp, hcπ, h1']
  have : (q' ≫ q) ≫ x = 0 := by
    rw [Category.assoc, hy, ← Category.assoc, hz', Category.assoc, hδ₂, comp_zero]
  exact zero_of_epi_comp _ this

/-- In the long exact sequence of a left exact functor, `T X₂ ⟶ T X₃` is an epimorphism as soon
as every morphism `R⁰T X₃ ⟶ R¹T X₁` vanishes, since the connecting morphism is one of them. -/
private theorem epi_map_g_of_forall_eq_zero {C D : Type u} [Category.{v} C] [Category.{v} D]
    [Abelian C] [Abelian D] [EnoughInjectives C] (T : C ⥤ D) [T.Additive]
    [PreservesFiniteLimits T] {S : ShortComplex C} (hS : S.ShortExact)
    (h : ∀ φ : (T.rightDerived 0).obj S.X₃ ⟶ (T.rightDerived 1).obj S.X₁, φ = 0) :
    Epi (T.map S.g) := by
  letI := HasDerivedCategory.standard C
  letI := HasDerivedCategory.standard D
  let Δ := Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives T
  have hex := Δ.exact_δ₁ hS 0
  have hδ : Δ.δ hS 0 = 0 := h _
  have h0 : Epi ((T.rightDerived 0).map S.g) := hex.epi_f hδ
  have heq : T.map S.g = T.rightDerivedZeroIsoSelf.inv.app _ ≫ (T.rightDerived 0).map S.g ≫
      T.rightDerivedZeroIsoSelf.hom.app _ := by
    rw [T.rightDerivedZeroIsoSelf.hom.naturality, Iso.inv_hom_id_app_assoc]
  rw [heq]
  infer_instance

end Homological

section Torsion

variable {R : Scheme.{0}}

open Stacks.AlgebraicGeometry in
/-- On an affine open of a locally Noetherian integral scheme, a section of a quasi-coherent
module whose only associated point is the generic point vanishes as soon as it is killed by a
function which does not vanish identically. -/
private theorem eq_zero_of_smul_eq_zero [IsIntegral R] [IsLocallyNoetherian R] (N : R.Modules)
    [N.IsQuasicoherent]
    (hN : ∀ x, Stacks.Divisors.IsAssociatedPoint N x → x = genericPoint R)
    {U : R.Opens} (hU : IsAffineOpen U) (g : Γ(R, U)) (hg : (R.basicOpen g : Set R).Nonempty)
    (t : Γ(N, U)) (ht : g • t = 0) : t = 0 := by
  by_contra ht0
  haveI : IsNoetherianRing Γ(R, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  obtain ⟨P, hP, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing Γ(R, U) t ht0
  have hgP : g ∈ P := hle (by
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
    exact ht)
  let P' : PrimeSpectrum Γ(R, U) := ⟨P, hP.isPrime⟩
  set y : R := hU.fromSpec P' with hy
  have hyU : y ∈ U := by
    have : y ∈ Set.range hU.fromSpec := ⟨P', rfl⟩
    rwa [hU.range_fromSpec] at this
  have hyP : hU.primeIdealOf ⟨y, hyU⟩ = P' :=
    hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf ⟨y, hyU⟩)
  have hass : Stacks.Divisors.IsAssociatedPoint N y := by
    rw [AssociatedPointPrime.divisorsIsAssociatedPoint_iff_mem_associatedPrimes N hU hyU, hyP]
    exact hP
  have hyb : y ∉ R.basicOpen g := by
    intro h
    have : P' ∈ hU.fromSpec ⁻¹ᵁ R.basicOpen g := h
    rw [hU.fromSpec_preimage_basicOpen] at this
    exact this hgP
  obtain ⟨z, hz⟩ := hg
  apply hyb
  rw [hN y hass]
  exact ((genericPoint_spec R).mem_open_set_iff (R.basicOpen g).isOpen).mpr ⟨z, trivial, hz⟩

/-- A morphism into a quasi-coherent module whose only associated point is the generic point
vanishes if every section of its source over a nonempty affine open is killed by a function
which does not vanish identically. -/
private theorem hom_eq_zero_of_forall_smul_eq_zero [IsIntegral R] [IsLocallyNoetherian R]
    {M N : R.Modules} [N.IsQuasicoherent]
    (hN : ∀ x, Stacks.Divisors.IsAssociatedPoint N x → x = genericPoint R)
    (hM : ∀ U : R.Opens, IsAffineOpen U → (U : Set R).Nonempty → ∀ s : Γ(M, U),
      ∃ g : Γ(R, U), (R.basicOpen g : Set R).Nonempty ∧ g • s = 0)
    (φ : M ⟶ N) : φ = 0 := by
  apply (Scheme.Modules.toPresheaf R).map_injective
  let N' : TopCat.Sheaf AddCommGrpCat R := ⟨N.presheaf, N.isSheaf⟩
  refine TopCat.Sheaf.hom_ext M.presheaf N'
    (B := fun U : {U : R.affineOpens // ((U : R.Opens) : Set R).Nonempty} => (U.1 : R.Opens))
    ?_ fun U => ?_
  · rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
    intro V x hx
    obtain ⟨W, hW, hxW, hWV⟩ :=
      (TopologicalSpace.Opens.isBasis_iff_nbhd.mp R.isBasis_affineOpens) hx
    exact ⟨W, ⟨⟨⟨W, hW⟩, ⟨x, hxW⟩⟩, rfl⟩, hxW, hWV⟩
  · rw [Functor.map_zero]
    change Scheme.Modules.Hom.app φ U.1.1 = Scheme.Modules.Hom.app 0 U.1.1
    rw [Scheme.Modules.Hom.zero_app]
    ext s
    obtain ⟨g, hg, hgs⟩ := hM U.1.1 U.1.2 U.2 s
    refine eq_zero_of_smul_eq_zero N hN U.1.2 g hg _ ?_
    rw [← Scheme.Modules.Hom.app_smul, hgs, map_zero]

/-- The direct image of the structure sheaf of a reduced scheme `S` along `ι ≫ f`, with
`ι ≫ f` of image a proper closed subset of the irreducible `R`, is killed on every nonempty
affine open by a function vanishing on that image. -/
private theorem exists_smul_eq_zero_pushforward {S X : Scheme.{0}} [IsReduced S]
    [IrreducibleSpace R] (ι : S ⟶ X) (f : X ⟶ R) (hc : IsClosed (Set.range (ι ≫ f)))
    (hV : Set.range (ι ≫ f) ≠ Set.univ) (U : R.Opens) (hU : IsAffineOpen U)
    (hne : (U : Set R).Nonempty)
    (s : Γ((Scheme.Modules.pushforward f).obj
      ((Scheme.Modules.pushforward ι).obj (SheafOfModules.unit S.ringCatSheaf)), U)) :
    ∃ g : Γ(R, U), (R.basicOpen g : Set R).Nonempty ∧ g • s = 0 := by
  -- a point of `U` off the image
  obtain ⟨x, hxU, hxV⟩ : ∃ x ∈ (U : Set R), x ∉ Set.range (ι ≫ f) := by
    by_contra h
    push Not at h
    apply hV
    have hdense : Dense (U : Set R) := U.isOpen.dense hne
    rw [← hc.closure_eq]
    exact (hdense.mono h).closure_eq
  obtain ⟨g, hgV, hxg⟩ := hU.exists_basicOpen_le
    (V := ⟨(Set.range (ι ≫ f))ᶜ, hc.isOpen_compl⟩) ⟨x, hxV⟩ hxU
  refine ⟨g, ⟨x, hxg⟩, ?_⟩
  have h0 : ι.app (f ⁻¹ᵁ U) (f.app U g) = 0 := by
    apply eq_zero_of_basicOpen_eq_bot
    rw [← Scheme.Hom.preimage_basicOpen, ← Scheme.Hom.preimage_basicOpen]
    ext y
    simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
    intro hy
    exact hgV hy ⟨y, rfl⟩
  change (show Γ(S, ι ⁻¹ᵁ f ⁻¹ᵁ U) from ι.app (f ⁻¹ᵁ U) (f.app U g) *
    show Γ(S, ι ⁻¹ᵁ f ⁻¹ᵁ U) from s) = 0
  rw [h0, zero_mul]

end Torsion

section Exactness

variable {Y : Scheme.{0}}

/-- Exactness of a short complex of `𝒪_Y`-modules can be tested on the sections over affine
opens. -/
private theorem exact_of_forall_isAffineOpen {E F G : Y.Modules} (f : E ⟶ F) (g : F ⟶ G)
    (w : f ≫ g = 0)
    (h : ∀ U : Y.Opens, IsAffineOpen U → (U : Set Y).Nonempty → ∀ s : Γ(F, U), g.app U s = 0 →
      ∃ t : Γ(E, U), f.app U t = s) :
    (ShortComplex.mk f g w).Exact := by
  have hS : (ShortComplex.mk (C := _root_.SheafOfModules.{0} Y.ringCatSheaf) f g w).Exact := by
    rw [AlgebraicGeometry.SheafOfModules.exact_iff_stalkFunctor_map_exact]
    intro x
    rw [ShortComplex.moduleCat_exact_iff]
    intro m hm
    obtain ⟨W, hxW, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq F.val.presheaf m
    have hm' : (TopCat.Presheaf.germ G.val.presheaf W x hxW).hom (g.val.app (op W) s) =
        (TopCat.Presheaf.germ G.val.presheaf W x hxW).hom 0 := by
      rw [map_zero]
      exact (AlgebraicGeometry.SheafOfModules.stalkMap_germ _ x g W hxW s).symm.trans hm
    obtain ⟨W', hxW', i₁, i₂, hW'⟩ := TopCat.Presheaf.germ_eq _ x hxW hxW _ _ hm'
    obtain ⟨V, hV, hxV, hVW'⟩ := Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens hxW'
    have hgs : g.app V (F.presheaf.map (homOfLE (hVW'.trans i₁.le)).op s) = 0 := by
      have e := congr($(g.mapPresheaf.naturality (homOfLE (hVW'.trans i₁.le)).op) s)
      have hW'' : G.presheaf.map i₁.op (g.app W s) = G.presheaf.map i₂.op 0 := hW'
      refine e.trans ?_
      change G.presheaf.map (homOfLE (hVW'.trans i₁.le)).op (g.app W s) = 0
      have hc : (homOfLE (hVW'.trans i₁.le)).op = i₁.op ≫ (homOfLE hVW').op := rfl
      rw [hc, Functor.map_comp, ConcreteCategory.comp_apply, hW'', map_zero, map_zero]
    obtain ⟨t, ht⟩ := h V hV ⟨x, hxV⟩ _ hgs
    refine ⟨(TopCat.Presheaf.germ E.val.presheaf V x hxV).hom t, ?_⟩
    refine (AlgebraicGeometry.SheafOfModules.stalkMap_germ _ x f V hxV t).trans ?_
    change (TopCat.Presheaf.germ F.val.presheaf V x hxV).hom (f.app V t) = _
    rw [ht]
    exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
  exact hS

/-- On sections, the inverse of an isomorphism of `𝒪_Y`-modules is a right inverse. -/
private theorem iso_hom_app_inv_app {M N : Y.Modules} (e : M ≅ N) (U : Y.Opens) (x : Γ(N, U)) :
    e.hom.app U (e.inv.app U x) = x := by
  rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, Iso.inv_hom_id]
  rfl

/-- On sections, the inverse of an isomorphism of `𝒪_Y`-modules is a left inverse. -/
private theorem iso_inv_app_hom_app {M N : Y.Modules} (e : M ≅ N) (U : Y.Opens) (x : Γ(M, U)) :
    e.inv.app U (e.hom.app U x) = x :=
  iso_hom_app_inv_app e.symm U x

end Exactness

section Values

variable {X : Scheme.{0}} [IsIntegral X]

/-- On an integral scheme, the generization from the stalk at the generic point of a component
to the function field is injective. -/
private theorem componentToFunctionField_injective (Z : irreducibleComponents X) :
    Function.Injective (MMP.Positivity.componentToFunctionField Z).hom := by
  have hmem : genericPoint X ∈ Z.1 :=
    Z.2.2 (IrreducibleSpace.isIrreducible_univ X) (Set.subset_univ _) trivial
  let j := (X.presheaf.stalkSpecializes
    ((isGenericPoint_componentGenericPoint X Z).specializes hmem)).hom
  refine Function.LeftInverse.injective (g := j) fun a => ?_
  change (X.presheaf.stalkSpecializes _ ≫ X.presheaf.stalkSpecializes _).hom a = a
  rw [TopCat.Presheaf.stalkSpecializes_comp, TopCat.Presheaf.stalkSpecializes_refl]
  rfl

/-- On an integral scheme, the generic point of every irreducible component lies in every
nonempty open. -/
private theorem componentGenericPoint_mem_of_nonempty {W : X.Opens} (hW : (W : Set X).Nonempty)
    (Z : irreducibleComponents X) : componentGenericPoint X Z ∈ W := by
  rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint]
  obtain ⟨x, hx⟩ := hW
  exact (genericPoint_spec X).specializes trivial |>.mem_open W.isOpen hx

/-- The value in the function field of the germ of a regular function at the generic point of a
component. -/
private theorem componentToFunctionField_germ {W : X.Opens} [Nonempty W] (a : Γ(X, W))
    (Z : irreducibleComponents X) (hZ : componentGenericPoint X Z ∈ W) :
    (MMP.Positivity.componentToFunctionField Z).hom
        ((X.presheaf.germ W (componentGenericPoint X Z) hZ).hom a) =
      X.germToFunctionField W a :=
  TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf _ _ _

end Values

section Orders

variable {X W : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]

/-- Along a prime divisor `P` of `W` lying over a prime divisor `Q` of `X`, the order of the
pull-back of a rational function is its order along `Q`. -/
private theorem ord_functionFieldMap_of_map_genericPoint (p : W ⟶ X) [IsDominant p]
    (hp : Function.Surjective (functionFieldMap p)) {P : MMP.Mori.PrimeDivisor W}
    {Q : MMP.Mori.PrimeDivisor X}
    (h : p P.genericPoint = Q.genericPoint) {g : X.functionField} (hg : g ≠ 0) :
    W.ord (functionFieldMap p g) P.genericPoint = X.ord g Q.genericPoint := by
  have hv := congrArg (fun v => v g)
    (MMP.Fourfold.Oai4C1.CommonModel.valuationOver_eq_of_map_genericPoint p hp P Q h)
  simp only [PrimeDivisor.valuationOver_apply] at hv
  have hg' : functionFieldMap p g ≠ 0 := (map_ne_zero_iff _ (functionFieldMap p).injective).2 hg
  rw [PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg',
    PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg] at hv
  have := WithZero.exp_injective hv
  linarith

/-- A regular function has positive order along a prime divisor `Q` through its open exactly
when it vanishes at the generic point of `Q`. -/
private theorem one_le_ord_germToFunctionField_iff {U : X.Opens} [Nonempty U] (r : Γ(X, U))
    (hr : X.germToFunctionField U r ≠ 0) (Q : MMP.Mori.PrimeDivisor X) (hQ : Q.genericPoint ∈ U) :
    1 ≤ X.ord (X.germToFunctionField U r) Q.genericPoint ↔ Q.genericPoint ∉ X.basicOpen r := by
  rw [← Scheme.algebraMap_germ_eq_germToFunctionField X hQ r] at hr ⊢
  have hv := Q.divisorialValuation_eq_exp_neg_ord hr
  have hlt :=
    Q.divisorialValuation_algebraMap_lt_one_iff ((X.presheaf.germ U Q.genericPoint hQ).hom r)
  rw [Scheme.mem_basicOpen X r Q.genericPoint hQ]
  refine Iff.trans ?_ (hlt.trans (IsLocalRing.mem_maximalIdeal _))
  change _ ↔ Q.divisorialValuation (algebraMap _ X.functionField
    ((X.presheaf.germ U Q.genericPoint hQ).hom r)) < 1
  rw [hv, ← WithZero.exp_zero, WithZero.exp_lt_exp]
  omega

end Orders

section SES

variable {S X W : Scheme.{0}}

/-- A regular function restricts to zero on the reduced support of a divisor exactly when it
vanishes at the generic points of its prime divisors. -/
private theorem app_subschemeι_eq_zero_iff (T : Divisor X) [IsReduced T.suppIdeal.subscheme]
    (U : X.Opens) (r : Γ(X, U)) :
    T.suppIdeal.subschemeι.app U r = 0 ↔ ∀ Q : MMP.Mori.PrimeDivisor X, T.coeff Q ≠ 0 →
      Q.genericPoint ∈ U → Q.genericPoint ∉ X.basicOpen r := by
  have hrange : Set.range T.suppIdeal.subschemeι = (T.supp : Set X) := by
    rw [Scheme.IdealSheafData.range_subschemeι, DivisorWithCoeffs.coe_support_suppIdeal]
  constructor
  · intro h0 Q hQ _ hb
    have hQs : Q.genericPoint ∈ (T.supp : Set X) :=
      DivisorWithCoeffs.support_subset_supp hQ (MMP.Spreading.genericPoint_mem_support Q)
    rw [← hrange] at hQs
    obtain ⟨y, hy⟩ := hQs
    have : y ∈ T.suppIdeal.subschemeι ⁻¹ᵁ X.basicOpen r := by
      change T.suppIdeal.subschemeι y ∈ X.basicOpen r
      rwa [hy]
    rw [Scheme.Hom.preimage_basicOpen, h0, Scheme.basicOpen_zero] at this
    exact this
  · intro h
    apply eq_zero_of_basicOpen_eq_bot
    rw [← Scheme.Hom.preimage_basicOpen]
    ext y
    simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
    intro hy
    have hyb : T.suppIdeal.subschemeι y ∈ X.basicOpen r := hy
    have hyT : T.suppIdeal.subschemeι y ∈ (T.supp : Set X) := hrange ▸ ⟨y, rfl⟩
    obtain ⟨Q, hQ, hyQ⟩ := DivisorWithCoeffs.mem_supp_iff.mp hyT
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hyQ
    have hsp : Q.genericPoint ⤳ T.suppIdeal.subschemeι y := specializes_iff_mem_closure.mpr hyQ
    exact h Q hQ ((hsp.mem_open (X.basicOpen r).isOpen hyb) |> X.basicOpen_le r)
      (hsp.mem_open (X.basicOpen r).isOpen hyb)

variable [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]

/-- **The floor ideal as a direct image.** Let `p : W ⟶ X` be a proper birational morphism of
normal varieties, `T_X` a divisor on `X`, `E ≥ 0` a `p`-exceptional Cartier divisor and `T` a
divisor on `W` whose components are the strict transforms of the components of `T_X`, with
coefficient one, along which `E` vanishes. Then `0 ⟶ p_* 𝒪_W(E - T) ⟶ 𝒪_X ⟶ ι_* 𝒪_S ⟶ 0` is
exact, where `ι : S ⟶ X` is the reduced subscheme on `Supp T_X`. -/
private theorem exists_shortExact_of_floor {k : Type} [Field k] (sX : X ⟶ Spec (.of k))
    (hXv : MMP.Mori.IsVariety k sX) (p : W ⟶ X) (hWv : MMP.Mori.IsVariety k (p ≫ sX))
    [IsProper p] (hb : IsBirationalMorphism p) (Tx : Divisor X)
    [IsReduced Tx.suppIdeal.subscheme] (E T : Divisor W) (hEc : E.IsCartier) (hE0 : 0 ≤ E)
    (hEexc : ∀ P, E.coeff P ≠ 0 → RationalMap.IsExceptional (X := W) p.toRationalMap P)
    (hT : ∀ P, T.coeff P = 0 ∨ (T.coeff P = 1 ∧ E.coeff P = 0 ∧
      ∃ Q : MMP.Mori.PrimeDivisor X, Tx.coeff Q ≠ 0 ∧ p P.genericPoint = Q.genericPoint))
    (hT' : ∀ Q : MMP.Mori.PrimeDivisor X, Tx.coeff Q ≠ 0 →
      ∃ P : MMP.Mori.PrimeDivisor W, p P.genericPoint = Q.genericPoint ∧ T.coeff P = 1) :
    ∃ (β : (Scheme.Modules.pushforward p).obj (E - T).divisorialSheaf ⟶
        SheafOfModules.unit X.ringCatSheaf)
      (hβ : β ≫ unitHom Tx.suppIdeal.subschemeι = 0), (ShortComplex.mk _ _ hβ).ShortExact := by
  haveI := hb.isDominant
  have hsurj : Function.Surjective (functionFieldMap p) := hb.functionFieldMap_bijective.2
  have hB0 : ∀ Z : irreducibleComponents W,
      p (componentGenericPoint W Z) ∉ (0 : Divisor X).supp := by
    intro Z h
    rw [DivisorWithCoeffs.supp_zero] at h
    exact h
  obtain ⟨e, he⟩ := Divisor.exists_iso_pushforward_divisorialSheaf_add_of_isExceptional sX p
    hXv hWv hb 0 Divisor.isCartier_zero hB0 0 (Divisor.isPullback_zero hB0) E hEc hE0 hEexc
  have hTle : ∀ P, 0 ≤ T.coeff P := fun P => by
    rcases hT P with h | ⟨h, -⟩ <;> rw [h] <;> norm_num
  have hGE : E - T ≤ 0 + E := by
    intro P
    change (E - T).coeff P ≤ (0 + E).coeff P
    rw [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_zero]
    linarith [hTle P]
  let ι := Tx.suppIdeal.subschemeι
  let incl := (Scheme.Modules.pushforward p).map (Divisor.divisorialSheafInclusion hGE)
  let β : (Scheme.Modules.pushforward p).obj (E - T).divisorialSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf := incl ≫ e.inv ≫ Divisor.divisorialSheafZeroIso.hom
  -- the value of the pull-back of a regular function
  have hval : ∀ (U : X.Opens) [Nonempty U] (r : Γ(X, U)) (Z : irreducibleComponents W)
      (hZ : componentGenericPoint W Z ∈ p ⁻¹ᵁ U),
      (MMP.Positivity.componentToFunctionField Z).hom
        ((e.hom.app U ((Divisor.divisorialSheafZeroIso (X := X)).inv.app U r)).1 ⟨Z, hZ⟩) =
        functionFieldMap p (X.germToFunctionField U r) := by
    intro U _ r Z hZ
    obtain ⟨ZX, -⟩ := exists_mem_irreducibleComponents (genericPoint X)
    have hZX : componentGenericPoint X ZX ∈ U :=
      componentGenericPoint_mem_of_nonempty
        (by obtain ⟨x⟩ := ‹Nonempty U›; exact ⟨x.1, x.2⟩) ZX
    have h1 := (he U ((Divisor.divisorialSheafZeroIso (X := X)).inv.app U r) ZX hZX Z hZ).1
    refine h1.trans ?_
    congr 1
    change (X.presheaf.stalkSpecializes _).hom
      (((Divisor.structureSheafToDivisorialSheaf (le_refl (0 : Divisor X))).app U r).1
        ⟨ZX, hZX⟩) = _
    rw [Divisor.coe_structureSheafToDivisorialSheaf_app, toRationalFunctionsPresheaf_app_apply]
    exact componentToFunctionField_germ r ZX hZX
  -- the coefficient of `E - T` along a component of the strict transform of the floor
  have hcoeff1 : ∀ P, T.coeff P = 1 → E.coeff P = 0 → -(E - T).coeff P = 1 := fun P h1 h2 => by
    rw [DivisorWithCoeffs.coeff_sub, h1, h2]; norm_num
  -- the order condition along a component of the strict transform of the floor
  have hord : ∀ (U : X.Opens) [Nonempty U] (r : Γ(X, U)) (P : MMP.Mori.PrimeDivisor W)
      (Q : MMP.Mori.PrimeDivisor X), p P.genericPoint = Q.genericPoint → Q.genericPoint ∈ U →
      (hZ : componentGenericPoint W P.component ∈ p ⁻¹ᵁ U) →
      (P.OrdGE 1 ((e.hom.app U ((Divisor.divisorialSheafZeroIso (X := X)).inv.app U r)).1
        ⟨P.component, hZ⟩) ↔ Q.genericPoint ∉ X.basicOpen r) := by
    intro U _ r P Q hPQ hQU hZ
    have hv := hval U r P.component hZ
    by_cases hz : ((e.hom.app U ((Divisor.divisorialSheafZeroIso (X := X)).inv.app U r)).1
        ⟨P.component, hZ⟩) = 0
    · have hr0 : X.germToFunctionField U r = 0 := by
        rw [hz, map_zero] at hv
        exact (map_eq_zero_iff _ (functionFieldMap p).injective).mp hv.symm
      have hr : r = 0 := (Scheme.germToFunctionField_injective X U) (by rw [hr0, map_zero])
      rw [hz, hr, Scheme.basicOpen_zero]
      exact ⟨fun _ h => h, fun _ => PrimeDivisor.OrdGE.zero _⟩
    · have hr0 : X.germToFunctionField U r ≠ 0 := by
        intro h0
        rw [h0, map_zero] at hv
        exact hz (componentToFunctionField_injective _ (hv.trans (map_zero _).symm))
      rw [MMP.Fourfold.PrimeDivisor.ordGE_iff_le_ord P hz, hv,
        ord_functionFieldMap_of_map_genericPoint p hsurj hPQ hr0]
      exact one_le_ord_germToFunctionField_iff r hr0 Q hQU
  -- `β` kills the floor
  have hzero : β ≫ unitHom ι = 0 := by
    refine Scheme.Modules.hom_ext _ _ fun U => ?_
    ext φ
    rw [Scheme.Modules.Hom.zero_app]
    let r : Γ(X, U) := β.app U φ
    change ι.app U r = 0
    have hσ : e.hom.app U ((Divisor.divisorialSheafZeroIso (X := X)).inv.app U r) =
        (Divisor.divisorialSheafInclusion hGE).app (p ⁻¹ᵁ U) φ := by
      change e.hom.app U ((Divisor.divisorialSheafZeroIso (X := X)).inv.app U
        ((Divisor.divisorialSheafZeroIso (X := X)).hom.app U (e.inv.app U (incl.app U φ)))) = _
      rw [iso_inv_app_hom_app, iso_hom_app_inv_app]
      rfl
    refine (app_subschemeι_eq_zero_iff Tx U r).2 fun Q hQ hQU => ?_
    haveI : Nonempty U := ⟨⟨_, hQU⟩⟩
    obtain ⟨P, hPQ, hTP⟩ := hT' Q hQ
    have hEP : E.coeff P = 0 := by
      rcases hT P with h | ⟨-, h, -⟩
      · omega
      · exact h
    have hPU : P.genericPoint ∈ p ⁻¹ᵁ U := by
      change p P.genericPoint ∈ U
      rwa [hPQ]
    have hPm : (P.support ∩ p ⁻¹ᵁ U).Nonempty :=
      ⟨P.genericPoint, MMP.Spreading.genericPoint_mem_support P, hPU⟩
    have hZ := P.componentGenericPoint_mem_of_nonempty hPm
    have h1 := φ.2 P hPm
    rw [hcoeff1 P hTP hEP] at h1
    refine (hord U r P Q hPQ hQU hZ).mp ?_
    rwa [hσ]
  -- exactness at `𝒪_X`
  have hex : (ShortComplex.mk _ _ hzero).Exact := by
    refine exact_of_forall_isAffineOpen β (unitHom ι) hzero fun U _ hne r₀ hr₀ => ?_
    haveI : Nonempty U := ⟨⟨_, hne.some_mem⟩⟩
    let r : Γ(X, U) := r₀
    have hr : ι.app U r = 0 := hr₀
    have hvan := (app_subschemeι_eq_zero_iff Tx U r).1 hr
    let σ : (0 + E).divisorialSubmodule (p ⁻¹ᵁ U) :=
      e.hom.app U ((Divisor.divisorialSheafZeroIso (X := X)).inv.app U r)
    have hσmem : σ.1 ∈ (E - T).divisorialSubmodule (p ⁻¹ᵁ U) := by
      intro P hP
      rcases hT P with h0 | ⟨h1, h2, Q, hQ, hPQ⟩
      · have hc : -(E - T).coeff P = -(0 + E).coeff P := by
          rw [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_add,
            DivisorWithCoeffs.coeff_zero, h0]
          ring
        rw [hc]
        exact σ.2 P hP
      · rw [hcoeff1 P h1 h2]
        have hPU : P.genericPoint ∈ p ⁻¹ᵁ U := P.genericPoint_mem_of_nonempty hP
        have hQU : Q.genericPoint ∈ U := by
          have : p P.genericPoint ∈ U := hPU
          rwa [hPQ] at this
        exact (hord U r P Q hPQ hQU (P.componentGenericPoint_mem_of_nonempty hP)).2
          (hvan Q hQ hQU)
    refine ⟨(⟨σ.1, hσmem⟩ : (E - T).divisorialSubmodule (p ⁻¹ᵁ U)), ?_⟩
    change (Divisor.divisorialSheafZeroIso (X := X)).hom.app U
      (e.inv.app U (incl.app U ⟨σ.1, hσmem⟩)) = r₀
    have h4 : incl.app U ⟨σ.1, hσmem⟩ =
        e.hom.app U ((Divisor.divisorialSheafZeroIso (X := X)).inv.app U r) := Subtype.ext rfl
    rw [h4, iso_inv_app_hom_app, iso_hom_app_inv_app]
  -- `β` is a monomorphism and `𝒪_X ⟶ ι_* 𝒪_S` an epimorphism
  haveI := (Scheme.Modules.pullbackPushforwardAdjunction p).rightAdjoint_preservesLimits
  have hm₁ : Mono incl := (Scheme.Modules.pushforward p).map_mono _
  have hm₂ : Mono (e.inv ≫ Divisor.divisorialSheafZeroIso.hom) := inferInstance
  have hmono : Mono β := @mono_comp _ _ _ _ _ incl hm₁ _ hm₂
  have hepi : Epi (unitHom ι) := Scheme.Modules.epi_unitToPushforwardObjUnit ι
  exact ⟨β, hzero, ShortComplex.ShortExact.mk' hex hmono hepi⟩

end SES

section Cases

variable {k : Type} [Field k] {X W : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
  [IsNormal X] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]

/-- A prime divisor of a proper birational model either lies over a prime divisor, at a point of
the biregular locus, or over a point of codimension at least two outside it. -/
private theorem map_genericPoint_cases (sX : X ⟶ Spec (.of k)) (hXv : MMP.Mori.IsVariety k sX)
    (p : W ⟶ X) (hWv : MMP.Mori.IsVariety k (p ≫ sX)) [IsProper p]
    (hb : IsBirationalMorphism p) (P : MMP.Mori.PrimeDivisor W) :
    (p P.genericPoint ∈ biregularLocus p ∧
      ∃ Q : MMP.Mori.PrimeDivisor X, p P.genericPoint = Q.genericPoint) ∨
    (p P.genericPoint ∉ biregularLocus p ∧ 2 ≤ Order.coheight (p P.genericPoint)) := by
  by_cases h : p P.genericPoint ∈ biregularLocus p
  · left
    have hc : Order.coheight (p P.genericPoint) = 1 := by
      rw [MMP.Positivity.coheight_map_of_mem_biregularLocus p h]
      exact P.coheight_genericPoint
    exact ⟨h, AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hc,
      (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hc).symm⟩
  · right
    refine ⟨h, ?_⟩
    have h2 :=
      MMP.Mori.two_le_closedsCodimension_compl_biregularLocus sX p (hY := hXv) (hX := hWv) hb
    exact (MMP.Flips.le_closedsCodimension_iff_le_coheight.mp h2) _ h

/-- Every prime divisor of the base is the image of a prime divisor of a proper birational
model. -/
private theorem exists_map_genericPoint_eq (p : W ⟶ X) [IsProper p] (hb : IsBirationalMorphism p)
    (Q : MMP.Mori.PrimeDivisor X) :
    ∃ P : MMP.Mori.PrimeDivisor W, p P.genericPoint = Q.genericPoint := by
  have hQ := MMP.Fourfold.Oai4C1.genericPoint_mem_biregularLocus p hb Q
  haveI := hb.isDominant
  obtain ⟨y, hy⟩ := p.surjective Q.genericPoint
  have hc : Order.coheight y = 1 := by
    rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus p (hy ▸ hQ), hy]
    exact Q.coheight_genericPoint
  exact ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hc,
    (congrArg p (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne y hc)).trans hy⟩

/-- A prime divisor of a proper birational model of a normal variety is exceptional exactly when
its generic point lies over a point of codimension at least two. -/
private theorem isExceptional_toRationalMap_iff_two_le_coheight (sX : X ⟶ Spec (.of k))
    (hX : IsNormalVariety k sX)
    (p : W ⟶ X) (hW : IsNormalVariety k (p ≫ sX)) (hb : IsBirationalMorphism p)
    (P : MMP.Mori.PrimeDivisor W) :
    RationalMap.IsExceptional (X := W) p.toRationalMap P ↔
      2 ≤ Order.coheight (p P.genericPoint) := by
  have : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated (X ↘ ⊤_ Scheme) := by
    rw [show (X ↘ ⊤_ Scheme) = sX ≫ (Spec (.of k) ↘ ⊤_ Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  rw [MMP.Positivity.isExceptional_toRationalMap_iff]
  let D : DivisorOver k sX := ⟨W, p, hW, hb, P⟩
  have hcl : Closeds.closure (p '' (P.idealSheaf.support : Set W)) =
      ⟨(D.center : Set X), D.center.isClosed⟩ := Closeds.ext rfl
  rw [hcl, closedsCodimension_coe, MMP.Positivity.DivisorOver.codimension_center]

/-- The crepant boundary along a prime divisor `P` lying over a prime divisor `Q` has the
coefficient of the boundary along `Q`. -/
private theorem coeff_crepantBoundary_of_map_genericPoint {sX : X ⟶ Spec (.of k)} {n : ℕ}
    {K : Divisor X} {B : QDivisor X} (hP : MMP.Mori.IsPair sX B) {p : W ⟶ X} [IsProper p]
    {hW : IsNormalVariety k (p ≫ sX)} {hb : IsBirationalMorphism p} {ΔW : QDivisor W}
    (hΔ : IsCrepantBoundary sX n K B p hW hb ΔW) {P : MMP.Mori.PrimeDivisor W}
    {Q : MMP.Mori.PrimeDivisor X} (h : p P.genericPoint = Q.genericPoint) :
    ΔW.coeff P = B.coeff Q := by
  classical
  have hnex : ¬ RationalMap.IsExceptional (X := W) p.toRationalMap P := by
    rw [isExceptional_toRationalMap_iff_two_le_coheight sX hP.1 p hW hb P, h,
      AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]
    decide
  have heq := (hΔ.eq_inverseTransformDivisor_add_exceptional hP).1
  have h1 := congrArg (fun G : QDivisor W => G P) heq
  simp only [Finsupp.add_apply, Finsupp.filter_apply, if_neg hnex, add_zero] at h1
  rw [DivisorWithCoeffs.coeff_apply, h1,
    MMP.Fourfold.Oai4C1.inverseTransformDivisor_apply_of_map_genericPoint h
      (MMP.Fourfold.Oai4C1.genericPoint_mem_biregularLocus p hb Q)]
  rfl

/-- The strict transform has no component over a point of codimension at least two. -/
private theorem inverseTransformDivisor_apply_of_two_le_coheight {R : Type*} [AddCommMonoid R]
    (p : W ⟶ X) (D : DivisorWithCoeffs R X) {P : MMP.Mori.PrimeDivisor W}
    (h : 2 ≤ Order.coheight (p P.genericPoint)) : inverseTransformDivisor p D P = 0 :=
  MMP.Fourfold.Oai4C1.mapPrimeDivisors_apply_eq_zero (φ := inverseTransformPrimeDivisor p)
    (fun Q hQ => by
    rw [((MMP.ProgramBaseChange.inverseTransformPrimeDivisor_eq_some_iff' p Q P).1 hQ).2,
      AlgebraicGeometry.PrimeDivisor.coheight_genericPoint] at h
    exact absurd h (by decide)) D

/-- **The dlt bound on exceptional coefficients.** If `p` is an isomorphism over an open `U` such
that every divisor over `X` with centre outside `U` has discrepancy `> -1`, then the crepant
boundary has coefficient `< 1` along every prime divisor lying over a point of codimension at
least two. -/
private theorem coeff_crepantBoundary_lt_one {sX : X ⟶ Spec (.of k)} {n : ℕ} {K : Divisor X}
    {B : QDivisor X} {U : X.Opens}
    (hdisc : ∀ (D : DivisorOver k sX) (a : ℚ), (D.center : Set X) ⊆ (U : Set X)ᶜ →
      IsDiscrepancy sX n K B D a → -1 < a)
    {p : W ⟶ X} [IsIso (p ∣_ U)] {hW : IsNormalVariety k (p ≫ sX)}
    {hb : IsBirationalMorphism p} {ΔW : QDivisor W}
    (hΔ : IsCrepantBoundary sX n K B p hW hb ΔW) (P : MMP.Mori.PrimeDivisor W)
    (h2 : 2 ≤ Order.coheight (p P.genericPoint)) : ΔW.coeff P < 1 := by
  let D : DivisorOver k sX := ⟨W, p, hW, hb, P⟩
  have hxU : p P.genericPoint ∉ U := by
    intro hxU
    have hbir : p P.genericPoint ∈ biregularLocus p :=
      MMP.Mori.le_biregularLocus (V := U) (inferInstance : IsIso (p ∣_ U)) hxU
    rw [MMP.Positivity.coheight_map_of_mem_biregularLocus p hbir,
      P.coheight_genericPoint] at h2
    exact absurd h2 (by decide)
  have hsub : (D.center : Set X) ⊆ (U : Set X)ᶜ := by
    rw [MMP.Mori.DivisorOver.center_eq_closure_genericPoint]
    exact closure_minimal (Set.singleton_subset_iff.2 hxU) U.isOpen.isClosed_compl
  have := hdisc D _ hsub (hΔ P)
  linarith

end Cases

section Assoc

/-- The only stratum of the zero divisor of an irreducible scheme is the whole space. -/
private theorem eq_univ_of_isSNCStratum_zero {W : Scheme.{0}} [IrreducibleSpace W] {S : Set W}
    (h : MMP.Fourfold.IsSNCStratum (0 : Divisor W) S) : S = Set.univ := by
  obtain ⟨J, hJ, hmax⟩ := h
  have hJe : J = ∅ := Finset.subset_empty.mp (by simpa using hJ)
  subst hJe
  refine Set.eq_univ_of_univ_subset (hmax.2 ⟨IrreducibleSpace.isIrreducible_univ W, ?_⟩
    (Set.subset_univ _))
  simp

/-- **No torsion in the first higher direct image.** In the setting of the torsion-freeness
theorem, with a fractional boundary `B'` (all coefficients `< 1`) and a surjective `g`, the only
associated point of `R¹g_* 𝒪_W(M)` is the generic point of the base. -/
private theorem eq_genericPoint_of_isAssociatedPoint_rightDerived {R W : Scheme.{0}}
    (sR : R ⟶ Spec (.of ℂ)) [MMP.Mori.IsProjectiveVariety ℂ sR] (sW : W ⟶ Spec (.of ℂ))
    [MMP.Mori.IsProjectiveVariety ℂ sW] (hWsm : IsSmoothScheme sW) [IsLocallyNoetherian W]
    [IsNormal W]
    (g : W ⟶ R) (hgs : g ≫ sR = sW) (hgp : IsProjective g) (hgsurj : Function.Surjective g)
    {n : ℕ} (KW : Divisor W) (hKW : KW.IsCanonicalDivisor sW n) (B' : QDivisor W)
    (hB' : B'.IsSNC sW) (hB'0 : ∀ E, 0 ≤ B' E) (hB'1 : ∀ E, B' E < 1) (M : Divisor W)
    (hM : M.IsCartier)
    (hsa : MMP.Fourfold.QDivisor.IsRelativelySemiample g
      (Divisor.toQDivisor M - (Divisor.toQDivisor KW + B')))
    (x : R) (hx : Stacks.Divisors.IsAssociatedPoint
      (((Scheme.Modules.pushforward g).rightDerived 1).obj M.divisorialSheaf) x) :
    x = genericPoint R := by
  obtain ⟨S, hS, hcl⟩ :=
    exists_isSNCStratum_closure_eq_image_of_isAssociatedPoint_rightDerived_pushforward
      sR sW hWsm g hgs hgp KW hKW B' hB' hB'0 (fun E => (hB'1 E).le) M hM hsa 1 x hx
  have h0 : B'.roundDown = 0 := by
    ext E
    rw [DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_zero,
      Int.floor_eq_zero_iff]
    exact ⟨hB'0 E, hB'1 E⟩
  rw [h0] at hS
  have hSu := eq_univ_of_isSNCStratum_zero hS
  rw [hSu, Set.image_univ, Set.range_eq_univ.mpr hgsurj] at hcl
  exact ((genericPoint_spec R).eq hcl).symm

end Assoc

section Free

/-- A Cartier divisor whose sheaf is isomorphic to a pull-back from the base is relatively free
over the base. -/
private theorem isRelativelyFreeCartier_of_iso_pullback {W R : Scheme.{0}} (g : W ⟶ R)
    (E : W.CartierDivisor) (L : R.Modules)
    (e : MMP.CartierDivisor.sheaf E ≅ (Scheme.Modules.pullback g).obj L) :
    IsRelativelyFreeCartier g E := by
  have h := MMP.Mori.epi_counit_app_pullback g L
  let adj := Scheme.Modules.pullbackPushforwardAdjunction g
  have hn := adj.counit.naturality e.hom
  simp only [Functor.comp_map, Functor.id_map] at hn
  have heq : adj.counit.app (MMP.CartierDivisor.sheaf E) =
      (Scheme.Modules.pullback g).map ((Scheme.Modules.pushforward g).map e.hom) ≫
        adj.counit.app _ ≫ e.inv := by
    rw [← Category.assoc, hn, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change Epi (adj.counit.app _)
  rw [heq]
  infer_instance

section Semiample

variable {X R W : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  [CompactSpace X] [IsIntegral R] [IsLocallyNoetherian R] [IsNormal R] [CompactSpace R]
  [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]

/-- **The pull-back of a `ℚ`-linear pull-back from the base is semiample over the base.** If
`(cN) L = (mN) f^*D_H + div χ` on `X` for a Cartier `D_H` on `R`, then `-(1/m) p^*L` is
semiample over `R` on a smooth `W`. -/
private theorem isRelativelySemiample_neg_smul_pullback {k : Type} [Field k]
    (sW : W ⟶ Spec (.of k))
    (hWsm : IsSmoothScheme sW) (f : X ⟶ R) [IsDominant f] (p : W ⟶ X) [IsDominant p]
    {m N c : ℕ} (hm : 0 < m) (hN : 0 < N) (hc : 0 < c) {L : Divisor X} (hLc : L.IsCartier)
    {LW : Divisor W}
    (hLW : L.IsPullback p (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant p L)
      LW)
    {DH : Divisor R} (hDH : DH.IsCartier) {DX : Divisor X} (hDXc : DX.IsCartier)
    (hDX : DH.IsPullback f (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant f DH)
      DX)
    (χ : (RationalFunctions X)ˣ)
    (hrel : ((c * N : ℕ) : ℤ) • L = ((m * N : ℕ) : ℤ) • DX + principalDivisor χ) :
    MMP.Fourfold.QDivisor.IsRelativelySemiample (p ≫ f)
      (-((1 / (m : ℚ)) • Divisor.toQDivisor LW)) := by
  classical
  have hBp : ∀ (C : Divisor X) (Z : irreducibleComponents W),
      p (componentGenericPoint W Z) ∉ C.supp :=
    MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant p
  have hBf : ∀ (C : Divisor R) (Z : irreducibleComponents X),
      f (componentGenericPoint X Z) ∉ C.supp :=
    MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant f
  -- the pull-backs of `D_X` and of `χ`
  set DW : Divisor W := DX.pullback hDXc (hBp DX) with hDWdef
  have hDW : DX.IsPullback p (hBp DX) DW := Divisor.isPullback_pullback hDXc (hBp DX)
  set χW := pullbackRationalFunction p χ (hBp (principalDivisor χ)) with hχWdef
  have hχW := Divisor.isPullback_principalDivisor (f := p) χ (hBp _)
  -- the relation on `W`
  have hrelW : ((c * N : ℕ) : ℤ) • LW = ((m * N : ℕ) : ℤ) • DW + principalDivisor χW := by
    have h1 := (hLW.zsmul hLc ((c * N : ℕ) : ℤ) (hBp _)).of_eq hrel (hB₂ := hBp _)
    have h2 := (hDW.zsmul hDXc ((m * N : ℕ) : ℤ) (hBp _)).add (hDXc.zsmul _)
      (Divisor.isCartier_principalDivisor χ) (hBp _) hχW
    exact h1.eq ((hDXc.zsmul _).add (Divisor.isCartier_principalDivisor χ)) h2
  set D'' : Divisor W := -(((m * N : ℕ) : ℤ) • DW + principalDivisor χW) with hD''def
  have hn : 0 < m * c * N := Nat.mul_pos (Nat.mul_pos hm hc) hN
  have hD'' : ∀ P, (D''.coeff P : ℚ) =
      ((m * c * N : ℕ) : ℚ) * (-((1 / (m : ℚ)) • Divisor.toQDivisor LW)).coeff P := by
    intro P
    have h := congrArg (fun D : Divisor W => (D.coeff P : ℚ)) hrelW
    simp only [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add, smul_eq_mul,
      Int.cast_mul, Int.cast_add, Int.cast_natCast] at h
    have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
    have hinv : (m : ℚ) * (1 / (m : ℚ)) = 1 := by field_simp
    have hQ : (-((1 / (m : ℚ)) • Divisor.toQDivisor LW)).coeff P =
        -((1 / (m : ℚ)) * (LW.coeff P : ℚ)) := by
      rw [DivisorWithCoeffs.coeff_neg, DivisorWithCoeffs.coeff_smul, Divisor.coeff_toQDivisor,
        smul_eq_mul]
    have hD : (D''.coeff P : ℚ) = -((((m * N : ℕ) : ℤ) : ℚ) * (DW.coeff P : ℚ) +
        ((principalDivisor χW).coeff P : ℚ)) := by
      rw [hD''def, DivisorWithCoeffs.coeff_neg, DivisorWithCoeffs.coeff_add,
        DivisorWithCoeffs.coeff_smul, smul_eq_mul]
      push_cast
      ring
    rw [hQ, hD]
    push_cast at h ⊢
    linear_combination h + ((c : ℚ) * N * (LW.coeff P : ℚ)) * hinv
  obtain ⟨E'', hE''⟩ :=
    (MMP.Resolution.Bridges.uniqueFactorization_and_exists_isWeilDivisorOfCartier).2
      W (MMP.Resolution.Bridges.isRegular_of_isSmoothScheme sW hWsm) D''
  have hfree : IsRelativelyFreeCartier (p ≫ f) E'' := by
    have hDHn := hDX.zsmul hDH (-((m * N : ℕ) : ℤ)) (hBf _)
    have hDWn := hDW.zsmul hDXc (-((m * N : ℕ) : ℤ)) (hBp _)
    have hlin : D''.LinearlyEquivalent ((-((m * N : ℕ) : ℤ)) • DW) :=
      ⟨χW⁻¹, by rw [MMP.Mori.principalDivisor_inv, hD''def, neg_smul]; abel⟩
    exact isRelativelyFreeCartier_of_iso_pullback (p ≫ f) E''
      ((-((m * N : ℕ) : ℤ)) • DH).divisorialSheaf
      (hE''.sheafIsoDivisorialSheaf ≪≫ hlin.divisorialSheafIso ≪≫
        Divisor.IsPullback.divisorialSheafIso (hBc := hDXc.zsmul _) hDWn ≪≫
        (Scheme.Modules.pullback p).mapIso
          (Divisor.IsPullback.divisorialSheafIso (hBc := hDH.zsmul _) hDHn) ≪≫
        (Scheme.Modules.pullbackComp p f).app _)
  exact MMP.Fourfold.QDivisor.isRelativelySemiample_of_isRelativelyFreeCartier (p ≫ f) _
    (m * c * N) hn D'' hD'' E'' hE'' hfree

end Semiample

end Free

section Smooth

/-- An open subscheme contained in the smooth locus is smooth. -/
private theorem isSmoothScheme_ι_of_le_smoothLocus {Y : Scheme.{0}} {k : Type} [Field k]
    {s : Y ⟶ Spec (.of k)} {V : Y.Opens} (hV : V ≤ smoothLocus s) : IsSmoothScheme (V.ι ≫ s) := by
  rw [IsSmoothScheme, eq_top_iff]
  intro x _
  obtain ⟨U, hxU, hU⟩ := mem_smoothLocus_iff.1 (hV x.2 : V.ι x ∈ smoothLocus s)
  refine mem_smoothLocus_iff.2 ⟨V.ι ⁻¹ᵁ U, hxU, ?_⟩
  have : Smooth (U.ι ≫ s) := hU
  rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
  infer_instance

end Smooth

section Auxiliary

/-- A morphism to an integral scheme whose comorphism is bijective on every open is dominant. -/
private theorem isDominant_of_isIso_app {X R : Scheme.{0}} [IsIntegral R] (f : X ⟶ R)
    (hO : ∀ U : R.Opens, IsIso (f.app U)) : IsDominant f := by
  rw [isDominant_iff]
  by_contra hd
  change ¬ Dense (Set.range f) at hd
  obtain ⟨V, hV, hVne, hVd⟩ : ∃ V : Set R, IsOpen V ∧ V.Nonempty ∧ Disjoint V (Set.range f) := by
    rw [dense_iff_closure_eq] at hd
    refine ⟨(closure (Set.range f))ᶜ, isClosed_closure.isOpen_compl, ?_, ?_⟩
    · exact Set.nonempty_compl.mpr hd
    · exact Set.disjoint_left.mpr fun x hx hx' => hx (subset_closure hx')
  let V' : R.Opens := ⟨V, hV⟩
  haveI : Nonempty V' := ⟨⟨_, hVne.some_mem⟩⟩
  have hpre : f ⁻¹ᵁ V' = ⊥ := by
    ext x
    simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
    intro hx
    exact Set.disjoint_left.mp hVd hx ⟨x, rfl⟩
  have hsub : Subsingleton Γ(X, f ⁻¹ᵁ V') := by
    rw [hpre]
    infer_instance
  have hbij := (ConcreteCategory.isIso_iff_bijective _).mp (hO V')
  have : Subsingleton Γ(R, V') := hbij.1.subsingleton
  exact (not_subsingleton Γ(R, V')) this

/-- A nonzero rational top form is nonzero as a `1`-canonical form. -/
private theorem toPluriForms_ne_zero {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    {sX : X ⟶ Spec (.of k)} {n : ℕ} {ω : RationalTopForms sX n} (hω : ω ≠ 0) :
    ω.toPluriForms sX ≠ 0 := by
  letI := functionFieldAlgebra sX
  intro h
  apply hω
  have h' : (PiTensorProduct.tprod X.functionField
      fun _ : Fin 1 => (ω : ⋀[X.functionField]^n Ω[X.functionField⁄k])) = 0 := h
  have h'' := congrArg (PiTensorProduct.subsingletonEquiv (0 : Fin 1)) h'
  rwa [PiTensorProduct.subsingletonEquiv_apply_tprod, map_zero] at h''

/-- Discrepancies do not depend on the canonical divisor within its linear equivalence class. -/
private theorem isDiscrepancy_of_sub_eq_principalDivisor {k : Type} [Field k] {X : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sX : X ⟶ Spec (.of k)} {n : ℕ} {K K' : Divisor X} {Δ : QDivisor X}
    {D : DivisorOver k sX} {a : ℚ} (hK' : K'.IsCanonicalDivisor sX n)
    {φ : (RationalFunctions X)ˣ} (hKK' : K - K' = principalDivisor φ)
    (h : IsDiscrepancy sX n K Δ D a) : IsDiscrepancy sX n K' Δ D a := by
  obtain ⟨hX, -, m, hm, ⟨D', hD', hD'c⟩, U, hU, τ, hτ, ha⟩ := h
  refine ⟨hX, hK', m, hm, ⟨D' - (m : ℤ) • principalDivisor φ, ?_,
    hD'c.sub ((Divisor.isCartier_principalDivisor φ).zsmul _)⟩, U, hU, τ, hτ, ha⟩
  have hK : K' = K - principalDivisor φ := by rw [← hKK']; abel
  rw [map_sub, hD', map_zsmul, hK, map_sub, smul_add, smul_add, smul_sub]
  abel

/-- On a smooth Noetherian scheme, a `ℚ`-divisor all of whose components have their generic
points in a closed subset with simple normal crossings has simple normal crossings. -/
private theorem isSNC_of_genericPoint_mem {Y : Scheme.{0}} [IsLocallyNoetherian Y]
    [CompactSpace Y] {k : Type} [Field k] {sY : Y ⟶ Spec (.of k)} [LocallyOfFiniteType sY]
    (hsm : IsSmoothScheme sY) {Z : Set Y} (hZ : MMP.Resolution.IsSNCClosedSubset sY Z)
    (D : QDivisor Y)
    (hD : ∀ P, D.coeff P ≠ 0 → P.genericPoint ∈ Z) : D.IsSNC sY := by
  classical
  haveI : IsNoetherian Y := ⟨⟩
  obtain ⟨hZc, -⟩ := id hZ
  rcases MMP.ProgramBaseChange.isSNCSubset_of_isSNCClosedSubset hsm (S := ⟨Z, hZc⟩) hZ with
    h0 | ⟨s, hs, hsncs⟩
  · refine (DivisorWithCoeffs.isSNC_zero_of_isSmoothScheme (R := ℚ) sY hsm).of_support_subset
      fun P hP => absurd (hD P (Finsupp.mem_support_iff.mp hP)) ?_
    have hZ0 : Z = ∅ := congrArg (fun C : Closeds Y => (C : Set Y)) h0
    rw [hZ0]
    exact Set.notMem_empty _
  · refine hsncs.of_support_subset fun P hP => ?_
    have h2 : P.genericPoint ∈ ⋃ E ∈ s, (E.support : Set Y) := by
      rw [hs]
      exact hD P (Finsupp.mem_support_iff.mp hP)
    obtain ⟨E', hE', hηE'⟩ := Set.mem_iUnion₂.mp h2
    obtain rfl := (MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hηE').symm
    rw [Finsupp.mem_support_iff, Finsupp.finset_sum_apply, Finset.sum_eq_single P]
    · simp
    · intro b _ hb
      rw [Finsupp.single_apply, if_neg hb]
    · exact fun h => absurd hE' h

end Auxiliary

section Geometry

/-- **Coefficients of the floor on a model.** Let `Δ_W` and `T` agree with `B` and `⌊B⌋` along
the prime divisors over prime divisors of `X`, with `Δ_W < 1` and `T = 0` along those over points
of codimension at least two, where `0 ≤ B ≤ 1`. Then for `Γ = Δ_W - T`, `E = -⌊Γ⌋` and
`B' = Γ + E`: `E` is effective and lies over points of codimension at least two, `T` is reduced,
disjoint from `E` and covers `⌊B⌋`, and `B'` is fractional, equal to `{B}` over `X`. -/
private theorem floor_coeff_data {X W : Scheme.{0}} (p : W ⟶ X) {B : QDivisor X}
    {ΔW Γ B' : QDivisor W} {T E : Divisor W}
    (hcoeff : ∀ Q : MMP.Mori.PrimeDivisor X, 0 ≤ B.coeff Q ∧ B.coeff Q ≤ 1)
    (hcases : ∀ P : MMP.Mori.PrimeDivisor W,
      (∃ Q : MMP.Mori.PrimeDivisor X, p P.genericPoint = Q.genericPoint) ∨
        2 ≤ Order.coheight (p P.genericPoint))
    (hsurj : ∀ Q : MMP.Mori.PrimeDivisor X,
      ∃ P : MMP.Mori.PrimeDivisor W, p P.genericPoint = Q.genericPoint)
    (hA : ∀ (P : MMP.Mori.PrimeDivisor W) (Q : MMP.Mori.PrimeDivisor X),
      p P.genericPoint = Q.genericPoint →
      ΔW.coeff P = B.coeff Q ∧ T.coeff P = B.roundDown.coeff Q)
    (hBc : ∀ P : MMP.Mori.PrimeDivisor W, 2 ≤ Order.coheight (p P.genericPoint) →
      ΔW.coeff P < 1 ∧ T.coeff P = 0)
    (hΓdef : Γ = ΔW - Divisor.toQDivisor T) (hEdef : E = -Γ.roundDown)
    (hB'def : B' = Γ + Divisor.toQDivisor E) :
    0 ≤ E ∧ (∀ P, E.coeff P ≠ 0 → 2 ≤ Order.coheight (p P.genericPoint)) ∧
      (∀ P, T.coeff P = 0 ∨ (T.coeff P = 1 ∧ E.coeff P = 0 ∧
        ∃ Q : MMP.Mori.PrimeDivisor X, B.roundDown.coeff Q ≠ 0 ∧
          p P.genericPoint = Q.genericPoint)) ∧
      (∀ Q : MMP.Mori.PrimeDivisor X, B.roundDown.coeff Q ≠ 0 →
        ∃ P : MMP.Mori.PrimeDivisor W, p P.genericPoint = Q.genericPoint ∧ T.coeff P = 1) ∧
      (∀ P, 0 ≤ B'.coeff P ∧ B'.coeff P < 1) ∧
      ∀ (P : MMP.Mori.PrimeDivisor W) (Q : MMP.Mori.PrimeDivisor X),
        p P.genericPoint = Q.genericPoint → B'.coeff P = Int.fract (B.coeff Q) := by
  have hfl : ∀ Q : MMP.Mori.PrimeDivisor X,
      B.roundDown.coeff Q = 0 ∨ B.roundDown.coeff Q = 1 := fun Q => by
    rw [DivisorWithCoeffs.coeff_roundDown]
    obtain ⟨h0, h1⟩ := hcoeff Q
    rcases eq_or_lt_of_le h1 with h | h
    · exact Or.inr (by simp [h])
    · exact Or.inl (Int.floor_eq_zero_iff.mpr ⟨h0, h⟩)
  have hΓc : ∀ P, Γ.coeff P = ΔW.coeff P - T.coeff P := fun P => by
    rw [hΓdef, DivisorWithCoeffs.coeff_sub, Divisor.coeff_toQDivisor]
  have hEc : ∀ P, E.coeff P = -⌊Γ.coeff P⌋ := fun P => by
    rw [hEdef, DivisorWithCoeffs.coeff_neg, DivisorWithCoeffs.coeff_roundDown]
  have hB'c : ∀ P, B'.coeff P = Int.fract (Γ.coeff P) := fun P => by
    rw [hB'def, DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, hEc, Int.fract]
    push_cast
    ring
  have hΓA : ∀ (P : MMP.Mori.PrimeDivisor W) (Q : MMP.Mori.PrimeDivisor X),
      p P.genericPoint = Q.genericPoint → Γ.coeff P = Int.fract (B.coeff Q) := by
    intro P Q h
    obtain ⟨h1, h2⟩ := hA P Q h
    rw [hΓc, h1, h2, DivisorWithCoeffs.coeff_roundDown]
    rfl
  have hΓ1 : ∀ P, Γ.coeff P < 1 := fun P => by
    rcases hcases P with ⟨Q, h⟩ | h2
    · rw [hΓA P Q h]
      exact Int.fract_lt_one _
    · rw [hΓc, (hBc P h2).2]
      simpa using (hBc P h2).1
  have hEA : ∀ (P : MMP.Mori.PrimeDivisor W) (Q : MMP.Mori.PrimeDivisor X),
      p P.genericPoint = Q.genericPoint → E.coeff P = 0 := fun P Q h => by
    rw [hEc, hΓA P Q h, Int.floor_eq_zero_iff.mpr ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩,
      neg_zero]
  refine ⟨fun P => ?_, fun P hP => (hcases P).resolve_left fun ⟨Q, h⟩ => hP (hEA P Q h),
    fun P => ?_, fun Q hQ => ?_, fun P => ?_, fun P Q h => by rw [hB'c, hΓA P Q h, Int.fract_fract]⟩
  · change 0 ≤ E.coeff P
    rw [hEc]
    have : ⌊Γ.coeff P⌋ < 1 := Int.floor_lt.mpr (by exact_mod_cast hΓ1 P)
    omega
  · rcases hcases P with ⟨Q, h⟩ | h2
    · rcases hfl Q with h0 | h1
      · exact Or.inl (by rw [(hA P Q h).2, h0])
      · right
        exact ⟨by rw [(hA P Q h).2, h1], hEA P Q h, Q, by rw [h1]; exact one_ne_zero, h⟩
    · exact Or.inl (hBc P h2).2
  · obtain ⟨P, hP⟩ := hsurj Q
    exact ⟨P, hP, (hA P Q hP).2.trans ((hfl Q).resolve_left hQ)⟩
  · rw [hB'c]
    exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

/-- The divisor relation `c N L₁ = m N D_X + div χ` from `L₁ = m (K₀ + B)`, `K₀ - K = div φ`,
`N (K + B - H_X) = div ψ` and `D_X = c H_X`, with `χ = ψ ^ (m c) φ ^ (m c N)`. -/
private theorem zsmul_eq_zsmul_add_principalDivisor {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {K K₀ L₁ DX : Divisor X}
    {B HX : QDivisor X} {m c N : ℕ} {φ ψ : (RationalFunctions X)ˣ}
    (hL₁ : Divisor.toQDivisor L₁ = (m : ℤ) • (Divisor.toQDivisor K₀ + B))
    (hφ : K₀ - K = principalDivisor φ)
    (hψ : (N : ℤ) • (Divisor.toQDivisor K + B - HX) = Divisor.toQDivisor (principalDivisor ψ))
    (hDXq : Divisor.toQDivisor DX = (c : ℤ) • HX) :
    ((c * N : ℕ) : ℤ) • L₁ = ((m * N : ℕ) : ℤ) • DX +
      principalDivisor (ψ ^ ((m * c : ℕ) : ℤ) * φ ^ ((m * c * N : ℕ) : ℤ)) := by
  ext P
  have e₁ := congrArg (fun D : QDivisor X => D.coeff P) hL₁
  have e₂ := congrArg (fun D : Divisor X => D.coeff P) hφ
  have e₃ := congrArg (fun D : QDivisor X => D.coeff P) hψ
  have e₄ := congrArg (fun D : QDivisor X => D.coeff P) hDXq
  simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul,
    DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_sub, coeff_principalDivisor,
    zsmul_eq_mul] at e₁ e₂ e₃ e₄
  simp only [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add,
    coeff_principalDivisor, PrimeDivisor.ord_mul, PrimeDivisor.ord_zpow, smul_eq_mul]
  have e₂q := congrArg (Int.cast : ℤ → ℚ) e₂
  apply Int.cast_injective (α := ℚ)
  push_cast at e₁ e₂q e₃ e₄ ⊢
  linear_combination (c * N : ℚ) * e₁ + (m * c * N : ℚ) * e₂q + (m * c : ℚ) * e₃ -
    (m * N : ℚ) * e₄

/-- **The floor ideal on a log resolution.** In the situation of the main theorem there are a
projective log resolution `p : W ⟶ X` and a divisor `G = E - T` on `W` such that
`0 ⟶ p_* 𝒪_W(G) ⟶ 𝒪_X ⟶ ι_* 𝒪_S ⟶ 0` is exact, and `R¹(f ∘ p)_* 𝒪_W(G)` is quasi-coherent
with the generic point of `R` as its only associated point. -/
private theorem exists_shortExact_pushforward {X R : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    (sR : R ⟶ Spec (.of ℂ))
    [MMP.Mori.IsProjectiveVariety ℂ sX] [MMP.Mori.IsProjectiveVariety ℂ sR]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsLocallyNoetherian R] [IsNormal R] [IsIntegral R]
    (f : X ⟶ R) (hf : f ≫ sR = sX) (hfp : IsProjectiveMorphism f)
    (hO : ∀ U : R.Opens, IsIso (f.app U))
    {n : ℕ} (K : MMP.Mori.Divisor X) (B : MMP.Mori.QDivisor X)
    (hdlt : MMP.Mori.IsDltPair sX n K B) (hQ : MMP.Fourfold.IsQFactorial sX)
    (H : MMP.Mori.QDivisor R) (hH : H.IsQCartier) (HX : MMP.Mori.QDivisor X)
    (hHX : ∃ hB, H.IsPullback f hB HX)
    (hKB : (Divisor.toQDivisor K + B).QLinearlyEquivalent HX) :
    ∃ (W : Scheme.{0}) (p : W ⟶ X) (F : W.Modules)
      (β : (Scheme.Modules.pushforward p).obj F ⟶ SheafOfModules.unit X.ringCatSheaf)
      (hβ : β ≫ unitHom B.roundDown.suppIdeal.subschemeι = 0),
      (ShortComplex.mk _ _ hβ).ShortExact ∧
      (((Scheme.Modules.pushforward (p ≫ f)).rightDerived 1).obj F).IsQuasicoherent ∧
      ∀ x, Stacks.Divisors.IsAssociatedPoint
        (((Scheme.Modules.pushforward (p ≫ f)).rightDerived 1).obj F) x → x = genericPoint R := by
  classical
  haveI : CompactSpace R := QuasiCompact.compactSpace_of_compactSpace sR
  have hXv : MMP.Mori.IsVariety ℂ sX := inferInstance
  have hXn : IsNormalVariety ℂ sX := ⟨hXv, inferInstance⟩
  obtain ⟨hPW, hcoeff, U, hUsm, hUsnc, hdisc⟩ := hdlt
  -- a projective log resolution which is an isomorphism over the snc locus `U` of the dlt pair
  obtain ⟨W, p, hres, -, hsnc, hiso⟩ :=
    MMP.Resolution.exists_isLogResolution_isIso_restrict_of_isSNCClosedSubset sX hXn B.support
  haveI hpU : IsIso (p ∣_ U) := hiso U (isSmoothScheme_ι_of_le_smoothLocus hUsm)
    (MMP.Intersection.isSNCClosedSubset_preimage_of_isSNC_restrictOpen sX U B hUsnc)
  have hWv : MMP.Mori.IsVariety ℂ (p ≫ sX) := hres.isVariety_source
  haveI : IsIntegral W := hWv.toIsIntegral
  obtain ⟨hWln, hWnor⟩ :=
    MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hres.isSmoothScheme
  haveI := hWln
  haveI := hWnor
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (p ≫ sX)
  haveI : IsProper p := hres.isProjective.isProper
  have hb : IsBirationalMorphism p := hres.isBirationalMorphism
  haveI := hb.isDominant
  have hWn : IsNormalVariety ℂ (p ≫ sX) := ⟨hWv, hWnor⟩
  have hn : topologicalKrullDim X = n := hPW.2.1.topologicalKrullDim_eq
  have hnW : topologicalKrullDim W = n := by
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (p ≫ sX) hb, hn]
  -- a top form `ω` and the canonical divisor `K₀ = div ω`
  obtain ⟨bas⟩ := MMP.Positivity.exists_basis_topForms hXn hn
  let ω : RationalTopForms sX n := bas ()
  have hω : ω ≠ 0 := bas.ne_zero ()
  set K₀ : Divisor X := topFormDivisor sX ω with hK₀
  obtain ⟨φ, hφ⟩ := MMP.Spreading.CanonExist.linearlyEquivalent_topFormDivisor hXn hn hω hPW.2.1
  -- a Cartier multiple `L₁ = m (K₀ + B)`
  obtain ⟨m, hm, L₁, hL₁, hL₁c⟩ : ∃ m : ℕ, 0 < m ∧ ∃ L₁ : Divisor X,
      Divisor.toQDivisor L₁ = (m : ℤ) • (Divisor.toQDivisor K₀ + B) ∧ L₁.IsCartier := by
    obtain ⟨m, hm, D, hD, hDc⟩ := hPW.2.2.exists_pos
    refine ⟨m, hm, D + (m : ℤ) • principalDivisor φ, ?_,
      hDc.add ((Divisor.isCartier_principalDivisor φ).zsmul _)⟩
    have hK₀K : K₀ = K + principalDivisor φ := by rw [← hφ]; abel
    rw [map_add, hD, map_zsmul, hK₀K, map_add, smul_add, smul_add, smul_add]
    abel
  -- the crepant boundary `Δ_W = (1/m) p^* L₁ - div(p^* ω)`
  have hB₁ := MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant p L₁
  set L₁W : Divisor W := L₁.pullback hL₁c hB₁ with hL₁W
  set KW : Divisor W := divisorOfForm (pullbackRationalPluriForms sX p (ω.toPluriForms sX))
    with hKWdef
  set ΔW : QDivisor W := (1 / (m : ℚ)) • Divisor.toQDivisor L₁W - Divisor.toQDivisor KW
    with hΔW
  have hcb₀ : IsCrepantBoundary sX n K₀ B p hWn hb ΔW :=
    MMP.ProgramBaseChange.isCrepantBoundary_pullback hXn hn hWn hb hnW hω hm hL₁ hL₁c
  have hcb : IsCrepantBoundary sX n K B p hWn hb ΔW := fun P =>
    isDiscrepancy_of_sub_eq_principalDivisor hPW.2.1 hφ (hcb₀ P)
  have hKW : KW.IsCanonicalDivisor (p ≫ sX) n := by
    obtain ⟨K₁, hK₁⟩ := exists_isCanonicalDivisor_of_isSmoothScheme (p ≫ sX)
      hres.isSmoothScheme hnW
    have hτ : pullbackRationalPluriForms sX p (ω.toPluriForms sX) ≠ 0 :=
      MMP.Fourfold.SNCWeight.SNCModel.pullbackRationalPluriForms_ne_zero' p
        hb.functionFieldMap_bijective
        (MMP.Mori.toNat_trdeg_functionField_of_topologicalKrullDim_eq hn)
        (toPluriForms_ne_zero hω)
    have h := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hWn hK₁ hτ
    rw [one_smul] at h
    exact hK₁.of_linearlyEquivalent h
  -- the strict transform `T` of the floor, `Γ = Δ_W - T`, `E = -⌊Γ⌋` and `B' = {Γ}`
  set T : Divisor W := inverseTransformDivisor p B.roundDown with hTdef
  set Γ : QDivisor W := ΔW - Divisor.toQDivisor T with hΓdef
  set E : Divisor W := -Γ.roundDown with hEdef
  set B' : QDivisor W := Γ + Divisor.toQDivisor E with hB'def
  have hcases := map_genericPoint_cases sX hXv p hWv hb
  have hA : ∀ (P : MMP.Mori.PrimeDivisor W) (Q : MMP.Mori.PrimeDivisor X),
      p P.genericPoint = Q.genericPoint →
      ΔW.coeff P = B.coeff Q ∧ T.coeff P = B.roundDown.coeff Q := fun P Q h =>
    ⟨coeff_crepantBoundary_of_map_genericPoint hPW.isPair hcb h,
      MMP.Fourfold.Oai4C1.inverseTransformDivisor_apply_of_map_genericPoint h
        (MMP.Fourfold.Oai4C1.genericPoint_mem_biregularLocus p hb Q) _⟩
  have hBc : ∀ P : MMP.Mori.PrimeDivisor W, 2 ≤ Order.coheight (p P.genericPoint) →
      ΔW.coeff P < 1 ∧ T.coeff P = 0 := fun P h2 =>
    ⟨coeff_crepantBoundary_lt_one hdisc hcb P h2,
      inverseTransformDivisor_apply_of_two_le_coheight p _ h2⟩
  obtain ⟨hE0, hEexc, hT, hT', hB'01, hB'A⟩ := floor_coeff_data p hcoeff
    (fun P => (hcases P).imp (·.2) (·.2)) (exists_map_genericPoint_eq p hb) hA hBc hΓdef hEdef
    hB'def
  -- the short exact sequence of the floor
  haveI : IsReduced B.roundDown.suppIdeal.subscheme :=
    Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  obtain ⟨β, hβ, hS⟩ := exists_shortExact_of_floor sX hXv p hWv hb B.roundDown E T
    (MMP.Fourfold.isCartier_of_isSmoothScheme hres.isSmoothScheme E) hE0
    (fun P hP => (isExceptional_toRationalMap_iff_two_le_coheight sX hXn p hWn hb P).2 (hEexc P hP))
    hT hT'
  haveI : IsProper f := isProper_of_isProjectiveMorphism f hfp
  refine ⟨W, p, (E - T).divisorialSheaf, β, hβ, hS, ?_, ?_⟩
  · exact Stacks.AlgebraicGeometry.Tag0EX4ProperQcoh.isQuasicoherent_rightDerived (p ≫ f) _ 1
  · intro x hx
    haveI : IsDominant f := isDominant_of_isIso_app f hO
    -- projectivity
    have hXproj : IsProjectiveMorphism sX :=
      (inferInstance : MMP.Mori.IsProjectiveVariety ℂ sX).isProjective
    have hWproj : IsProjectiveMorphism (p ≫ sX) :=
      (isProjective_iff_isProjectiveMorphism_of_isAffine _).1
        (IsProjective.comp hres.isProjective hXproj.isProjective)
    haveI : MMP.Mori.IsProjectiveVariety ℂ (p ≫ sX) :=
      (AlgebraicGeometry.isProjectiveVariety_iff ℂ _).2 ⟨hWv, hWproj⟩
    have hgp : IsProjective (p ≫ f) := IsProjective.comp hres.isProjective hfp.isProjective
    -- `B'` has simple normal crossings: its components lie in `Ex(p) ∪ p⁻¹(Supp B)`
    have hB'snc : B'.IsSNC (p ≫ sX) := by
      refine isSNC_of_genericPoint_mem hres.isSmoothScheme hsnc B' fun P hP => ?_
      rcases hcases P with ⟨-, Q, h⟩ | ⟨hnb, -⟩
      · have hBQ : B.coeff Q ≠ 0 := by
          intro h0
          apply hP
          rw [hB'A P Q h, h0]
          simp
        refine Or.inr ?_
        change p P.genericPoint ∈ B.support.sup fun E => (E.idealSheaf.support : Set X)
        rw [h, Finset.sup_set_eq_biUnion]
        exact Set.mem_biUnion (Finsupp.mem_support_iff.mpr hBQ)
          (MMP.Spreading.genericPoint_mem_support Q)
      · exact Or.inl (MMP.Mori.mem_exceptionalSet.mpr hnb)
    -- the adjoint gap is semiample over `R`
    have hQeq : Divisor.toQDivisor (E - T) - (Divisor.toQDivisor KW + B') =
        -((1 / (m : ℚ)) • Divisor.toQDivisor L₁W) := by
      rw [hB'def, hΓdef, hΔW, map_sub]
      abel
    obtain ⟨c, hc, DH, hDHq, hDHc⟩ := hH.exists_pos
    obtain ⟨hBH, hpbH⟩ := hHX
    obtain ⟨DX, hDXq, hDX⟩ := hpbH c hc DH hDHq hDHc
    obtain ⟨N, hN, ψ, hψ⟩ := hKB
    have hDXc : DX.IsCartier := by
      have h1 := Divisor.isPullback_pullback hDHc
        (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant f DH)
      rw [hDX.eq hDHc h1]
      exact MMP.Mori.Divisor.IsCartier.isCartier_pullback hDHc f _
    have hrel := zsmul_eq_zsmul_add_principalDivisor (K₀ := K₀) hL₁ hφ hψ hDXq
    have hsa : MMP.Fourfold.QDivisor.IsRelativelySemiample (p ≫ f)
        (Divisor.toQDivisor (E - T) - (Divisor.toQDivisor KW + B')) := by
      rw [hQeq]
      exact isRelativelySemiample_neg_smul_pullback (p ≫ sX) hres.isSmoothScheme f p hm hN hc
        hL₁c (Divisor.isPullback_pullback hL₁c hB₁) hDHc hDXc hDX _ hrel
    exact eq_genericPoint_of_isAssociatedPoint_rightDerived sR (p ≫ sX) hres.isSmoothScheme
      (p ≫ f) (by rw [Category.assoc, hf]) hgp (p ≫ f).surjective KW hKW B' hB'snc
      (fun P => by rw [← DivisorWithCoeffs.coeff_apply]; exact (hB'01 P).1)
      (fun P => by rw [← DivisorWithCoeffs.coeff_apply]; exact (hB'01 P).2)
      (E - T) (MMP.Fourfold.isCartier_of_isSmoothScheme hres.isSmoothScheme _) hsa x hx

end Geometry

section Assembly

/-- Naturally isomorphic additive functors have isomorphic right derived functors. -/
private noncomputable def rightDerivedIsoOfIso {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [HasInjectiveResolutions C] [Abelian D] {F G : C ⥤ D} [F.Additive] [G.Additive]
    (e : F ≅ G) (n : ℕ) : F.rightDerived n ≅ G.rightDerived n where
  hom := NatTrans.rightDerived e.hom n
  inv := NatTrans.rightDerived e.inv n
  hom_inv_id := by rw [← NatTrans.rightDerived_comp, e.hom_inv_id, NatTrans.rightDerived_id]
  inv_hom_id := by rw [← NatTrans.rightDerived_comp, e.inv_hom_id, NatTrans.rightDerived_id]

/-- **Surjectivity onto the direct image of a vertical subscheme.** Let `ι : S ⟶ X` with `S`
reduced and `f : X ⟶ R` with `R` integral and locally Noetherian, such that the image of
`ι ≫ f` is a proper closed subset. If `0 ⟶ p_* 𝓕 ⟶ 𝒪_X ⟶ ι_* 𝒪_S ⟶ 0` is exact for some
`p : W ⟶ X` and `R¹(f ∘ p)_* 𝓕` is quasi-coherent with only the generic point of `R` as
associated point, then `f_* 𝒪_X ⟶ f_* ι_* 𝒪_S` is an epimorphism. -/
private theorem epi_pushforward_map_unitHom {S X R W : Scheme.{0}} [IsReduced S] [IsIntegral R]
    [IsLocallyNoetherian R] (ι : S ⟶ X) (f : X ⟶ R) (hc : IsClosed (Set.range (ι ≫ f)))
    (hV : Set.range (ι ≫ f) ≠ Set.univ) (p : W ⟶ X) (F : W.Modules)
    (β : (Scheme.Modules.pushforward p).obj F ⟶ SheafOfModules.unit X.ringCatSheaf)
    (hβ : β ≫ unitHom ι = 0) (hS : (ShortComplex.mk _ _ hβ).ShortExact)
    [(((Scheme.Modules.pushforward (p ≫ f)).rightDerived 1).obj F).IsQuasicoherent]
    (hN : ∀ x, Stacks.Divisors.IsAssociatedPoint
      (((Scheme.Modules.pushforward (p ≫ f)).rightDerived 1).obj F) x → x = genericPoint R) :
    Epi ((Scheme.Modules.pushforward f).map (unitHom ι)) := by
  refine epi_map_g_of_forall_eq_zero (Scheme.Modules.pushforward f) hS fun φ => ?_
  have hacyc : ∀ I : W.Modules, Injective I →
      IsZero (((Scheme.Modules.pushforward f).rightDerived 1).obj
        ((Scheme.Modules.pushforward p).obj I)) := fun I hI => by
    letI := HasDerivedCategory.standard X.Modules
    letI := HasDerivedCategory.standard R.Modules
    exact (Stacks.Cohomology.LerayDegreewise.rightAcyclic_iff_isZero_rightDerived _ _).1
      (Stacks.AlgebraicGeometry.HigherDirectImageBaseChange.rightAcyclic_pushforward_obj_injective
        p f I) 1 one_pos
  obtain ⟨e, he⟩ := exists_mono_rightDerived_one_comp (Scheme.Modules.pushforward p)
    (Scheme.Modules.pushforward f) hacyc F
  let cI : ((Scheme.Modules.pushforward (p ≫ f)).rightDerived 1).obj F ≅
      ((Scheme.Modules.pushforward p ⋙ Scheme.Modules.pushforward f).rightDerived 1).obj F :=
    (rightDerivedIsoOfIso (Scheme.Modules.pushforwardComp p f) 1).app F
  let c := cI.inv
  let M : R.Modules := (Scheme.Modules.pushforward f).obj
    ((Scheme.Modules.pushforward ι).obj (SheafOfModules.unit S.ringCatSheaf))
  let ψ : M ⟶ ((Scheme.Modules.pushforward (p ≫ f)).rightDerived 1).obj F :=
    ((Scheme.Modules.pushforward f).rightDerivedZeroIsoSelf).inv.app _ ≫ φ ≫ e ≫ c
  have hz : ψ = 0 :=
    hom_eq_zero_of_forall_smul_eq_zero hN (exists_smul_eq_zero_pushforward ι f hc hV) ψ
  have h1 : φ ≫ e ≫ c = 0 :=
    ((((Scheme.Modules.pushforward f).rightDerivedZeroIsoSelf).app _).cancel_iso_inv_left _ _).1
      (by rwa [comp_zero])
  haveI : Mono (e ≫ c) := mono_comp _ _
  exact (cancel_mono (e ≫ c)).1 (by rw [h1, zero_comp])

end Assembly

end Proof_lem_fourfold_vertical_dlt_floor_stein_image

end

open CategoryTheory AlgebraicGeometry MMP.Mori

namespace MMP.Fourfold

open Proof_lem_fourfold_vertical_dlt_floor_stein_image in
/-- **The image of a vertical dlt floor.** Let `(X, B)` be a `ℚ`-factorial projective dlt pair
(canonical divisor `K`, dimension `n`) over `ℂ`,
and `f : X ⟶ R` a projective morphism to a normal projective variety with `f_* 𝒪_X = 𝒪_R` and
`K + B ∼_ℚ f^*H` for a `ℚ`-Cartier `H` on `R`. Let `ι : S ⟶ X` be the reduced subscheme of
`⌊B⌋`. If `f(S) ≠ R`, then `ι ≫ f` induces `𝒪_V ≅ (ι ≫ f)_* 𝒪_S` on its scheme-theoretic image
`V = (ι ≫ f).image`, i.e. the comorphism of `(ι ≫ f).toImage` is an isomorphism on every open. -/
@[mmp "lem_fourfold_vertical_dlt_floor_stein_image"]
public theorem isIso_app_toImage_suppScheme_of_isDltPair_of_qLinearlyEquivalent
    {X R : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) (sR : R ⟶ Spec (.of ℂ))
    [MMP.Mori.IsProjectiveVariety ℂ sX] [MMP.Mori.IsProjectiveVariety ℂ sR]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsLocallyNoetherian R] [IsNormal R]
    (f : X ⟶ R) (hf : f ≫ sR = sX) (hfp : IsProjectiveMorphism f)
    (hO : ∀ U : R.Opens, IsIso (f.app U))
    {n : ℕ} (K : MMP.Mori.Divisor X) (B : MMP.Mori.QDivisor X)
    (hdlt : MMP.Mori.IsDltPair sX n K B) (hQ : MMP.Fourfold.IsQFactorial sX)
    (H : MMP.Mori.QDivisor R) (hH : H.IsQCartier) (HX : MMP.Mori.QDivisor X)
    (hHX : ∃ hB, H.IsPullback f hB HX)
    (hKB : (Divisor.toQDivisor K + B).QLinearlyEquivalent HX)
    (hV : Set.range (B.roundDown.suppIdeal.subschemeι ≫ f) ≠ Set.univ) :
    ∀ U : (B.roundDown.suppIdeal.subschemeι ≫ f).image.Opens,
      IsIso ((B.roundDown.suppIdeal.subschemeι ≫ f).toImage.app U) := by
  
  classical
  haveI : IsIntegral R := inferInstance
  haveI : IsProper f := isProper_of_isProjectiveMorphism f hfp
  set ι := B.roundDown.suppIdeal.subschemeι
  haveI : IsReduced B.roundDown.suppIdeal.subscheme :=
    Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  obtain ⟨W, p, F, β, hβ, hS, hNqc, hN⟩ := exists_shortExact_pushforward sX sR f hf hfp hO K B
    hdlt hQ H hH HX hHX hKB
  haveI := hNqc
  have hc : IsClosed (Set.range (ι ≫ f)) := (ι ≫ f).isClosedMap.isClosed_range
  exact isIso_toImage_app_of_epi (ι ≫ f) (epi_unitHom_comp ι f (isIso_unitHom_of_isIso_app f hO)
    (epi_pushforward_map_unitHom ι f hc hV p F β hβ hS hN))

end MMP.Fourfold
