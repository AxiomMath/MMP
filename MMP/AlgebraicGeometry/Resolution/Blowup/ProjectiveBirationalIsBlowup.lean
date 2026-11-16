module
public import MMP.Attr
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.InvertibleToBaseIso
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.EpiClosedImmersionFactorization
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.DualTensorInternalHom
public import StacksFrontier.AlgebraicGeometry.AmpleCharacterization.NineClauses
public import StacksFrontier.AlgebraicGeometry.Modules.InvertibleStalkFree
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.QuasiProjectiveOverAmpleBase
public import MMP.AlgebraicGeometry.ProjectiveBundle.BundleCongr
public import StacksFrontier.AlgebraicGeometry.SymProjectiveBundleTwist.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.Integral
public import StacksFrontier.AlgebraicGeometry.Blowup.TwoStepTower
public import StacksFrontier.AlgebraicGeometry.InternalHomCoherent.TopSections
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentThree.DerivedChowFourierMukai
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.IsoOverDenseOpen
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.WedgeFiltrationGlobal
public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.ZeroNotInvertible
public import StacksFrontier.AlgebraicGeometry.ProperCoherentFiniteType.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.QuasiCompactOpenIdeal
public import StacksFrontier.AlgebraicGeometry.ReflexiveTorsionFree.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Projective

/-!
# Projective birational morphisms onto quasi-projective varieties are blowups

Let `X` be a quasi-projective variety over a field `k` and `f : X' ⟶ X` a projective birational
morphism from an integral scheme `X'`. Then `f` is, up to isomorphism over `X`, the blowup of `X`
in a nonzero coherent ideal sheaf: there is `J : X.IdealSheafData` of finite type with `J ≠ ⊥`
and an isomorphism `X' ≅ AlgebraicGeometry.blowUp J` whose composite with
`AlgebraicGeometry.blowUpToBase J` is `f`.

## Main results

* `MMP.exists_blowUp_iso_of_isProjective_of_isBirational`

## Implementation notes

Projectivity is `AlgebraicGeometry.IsProjective` and birationality is
`AlgebraicGeometry.IsBirational`. The source asks `X'` to be a variety; only integrality is
assumed, the remaining variety axioms of `X'` following from projectivity of `f` over the
variety `X`. A coherent ideal sheaf is an `AlgebraicGeometry.Scheme.IdealSheafData` of finite
type.

## References

* [KM98] J. Kollár, S. Mori, *Birational geometry of algebraic varieties*.
* [Har77] R. Hartshorne, *Algebraic geometry*, II.7.17.
-/

universe u

open AlgebraicGeometry CategoryTheory

namespace MMP

/-! ### Two integral closed subschemes of one scheme that agree over a dense open coincide -/

/-- A closed immersion with reduced source, whose ideal contains the kernel of `i` and whose
support is the range of `i`, is isomorphic to its source. -/
private lemma exists_iso_subscheme {A P : Scheme.{u}} (i : A ⟶ P) [IsClosedImmersion i]
    [IsReduced A] (K : P.IdealSheafData) (hK : i.ker ≤ K)
    (hs : (K.support : Set P) = Set.range i) :
    ∃ e : K.subscheme ≅ A, e.hom ≫ i = K.subschemeι := by
  let a : K.subscheme ⟶ A := IsClosedImmersion.lift i K.subschemeι (by rwa [K.ker_subschemeι])
  have ha : a ≫ i = K.subschemeι := IsClosedImmersion.lift_fac _ _ _
  have : IsClosedImmersion a := by
    have : IsClosedImmersion (a ≫ i) := ha ▸ inferInstance
    exact IsClosedImmersion.of_comp_isClosedImmersion a i
  have : Surjective a := ⟨fun x => by
    obtain ⟨c, hc⟩ : i x ∈ Set.range K.subschemeι := by
      rw [Scheme.IdealSheafData.range_subschemeι, hs]
      exact ⟨x, rfl⟩
    exact ⟨c, i.isEmbedding.injective (by rw [← Scheme.Hom.comp_apply, ha]; exact hc)⟩⟩
  have := isIso_of_isClosedImmersion_of_surjective a
  exact ⟨asIso a, ha⟩

/-- Two closed immersions with reduced sources and the same range are isomorphic over the
target. -/
private lemma exists_iso_of_range_eq {A B P : Scheme.{u}} (i₁ : A ⟶ P) (i₂ : B ⟶ P)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsReduced A] [IsReduced B]
    (h : Set.range i₁ = Set.range i₂) : ∃ e : A ≅ B, e.hom ≫ i₂ = i₁ := by
  let K : P.IdealSheafData := i₁.ker ⊔ i₂.ker
  have hK : (K.support : Set P) = Set.range i₁ := by
    simp only [K, Scheme.IdealSheafData.support_sup, TopologicalSpace.Closeds.coe_inf,
      Scheme.Hom.support_ker, i₁.isClosedEmbedding.isClosed_range.closure_eq,
      i₂.isClosedEmbedding.isClosed_range.closure_eq, ← h, Set.inter_self]
  obtain ⟨e₁, h₁⟩ := exists_iso_subscheme i₁ K le_sup_left hK
  obtain ⟨e₂, h₂⟩ := exists_iso_subscheme i₂ K le_sup_right (hK.trans h)
  refine ⟨e₁.symm ≪≫ e₂, ?_⟩
  simp [h₂, ← h₁]

/-- If `S ⊆ range i` and the preimage of `S` in an irreducible `A` is a nonempty open set, then
`range i` is the closure of `S`. -/
private lemma range_eq_closure {A P : Scheme.{u}} [IrreducibleSpace A] (i : A ⟶ P)
    [IsClosedImmersion i] (S : Set P) (hS : S ⊆ Set.range i)
    (hO : IsOpen (i ⁻¹' S)) (hne : (i ⁻¹' S).Nonempty) : Set.range i = closure S := by
  refine Set.Subset.antisymm ?_ (closure_minimal hS i.isClosedEmbedding.isClosed_range)
  rintro _ ⟨a, rfl⟩
  exact closure_mono (Set.image_preimage_subset i S)
    (image_closure_subset_closure_image i.continuous ⟨a, hO.dense hne a, rfl⟩)

/-- Points over a set on which `p` is injective, and which are hit over it by `i ≫ p`, are in the
range of `i`. -/
private lemma mem_range_of_injOn {A P X : Scheme.{u}} (p : P ⟶ X) (i : A ⟶ P) (W : Set X)
    (hinj : ∀ z z' : P, p z = p z' → p z ∈ W → z = z')
    (hsurj : ∀ x ∈ W, ∃ a : A, p (i a) = x) (z : P) (hz : p z ∈ W) : z ∈ Set.range i := by
  obtain ⟨a, ha⟩ := hsurj _ hz
  exact ⟨a, (hinj z (i a) ha.symm hz).symm⟩

/-- A morphism that is an isomorphism over an open `U` is bijective over `U`. -/
private lemma surj_inj_of_isIso_restrict {P X : Scheme.{u}} (p : P ⟶ X) (U : X.Opens)
    [IsIso (p ∣_ U)] :
    (∀ x ∈ U, ∃ z : P, p z = x) ∧ (∀ z z' : P, p z = p z' → p z ∈ U → z = z') := by
  have key : ∀ z : (p ⁻¹ᵁ U).toScheme, U.ι ((p ∣_ U) z) = p ((p ⁻¹ᵁ U).ι z) :=
    morphismRestrict_base_coe p U
  refine ⟨fun x hx => ?_, fun z z' h hz => ?_⟩
  · let y : U.toScheme := ⟨x, hx⟩
    refine ⟨(p ⁻¹ᵁ U).ι (inv (p ∣_ U) y), ?_⟩
    rw [← key, ← Scheme.Hom.comp_apply (inv (p ∣_ U)), IsIso.inv_hom_id]
    rfl
  · let a : (p ⁻¹ᵁ U).toScheme := ⟨z, hz⟩
    let a' : (p ⁻¹ᵁ U).toScheme := ⟨z', show p z' ∈ U from h ▸ hz⟩
    exact congrArg Subtype.val (show a = a' from (p ∣_ U).isOpenEmbedding.injective
      (U.ι.isOpenEmbedding.injective (by rw [key, key]; exact h)))

/-- **Two integral closed subschemes agreeing over an open coincide.** Let `p : P ⟶ X` be injective
over an open `W`, and let `i₁ : A ⟶ P`, `i₂ : B ⟶ P` be closed immersions of integral schemes
whose composites with `p` both hit every point of the nonempty `W`. Then `A ≅ B` over `P`: both
ranges are the closure of `p⁻¹ W`. -/
private theorem exists_iso_of_closedImmersion_over {A B P X : Scheme.{u}} [IsIntegral A]
    [IsIntegral B] (p : P ⟶ X) (i₁ : A ⟶ P) (i₂ : B ⟶ P) [IsClosedImmersion i₁]
    [IsClosedImmersion i₂] (W : X.Opens) (hW : (W : Set X).Nonempty)
    (hinj : ∀ z z' : P, p z = p z' → p z ∈ W → z = z')
    (hs₁ : ∀ x ∈ W, ∃ a : A, p (i₁ a) = x) (hs₂ : ∀ x ∈ W, ∃ b : B, p (i₂ b) = x) :
    ∃ e : A ≅ B, e.hom ≫ i₂ = i₁ := by
  obtain ⟨x, hx⟩ := hW
  have hr {C : Scheme.{u}} [IsIntegral C] (i : C ⟶ P) [IsClosedImmersion i]
      (hs : ∀ x ∈ W, ∃ c : C, p (i c) = x) : Set.range i = closure (p ⁻¹' W) := by
    refine range_eq_closure i _ (mem_range_of_injOn p i W hinj hs)
      ((W.isOpen.preimage p.continuous).preimage i.continuous) ?_
    obtain ⟨c, hc⟩ := hs x hx
    exact ⟨c, by simpa [hc] using hx⟩
  exact exists_iso_of_range_eq i₁ i₂ ((hr i₁ hs₁).trans (hr i₂ hs₂).symm)

/-! ### The projective bundle of an ideal sheaf -/

/-- The degree-one piece of the Rees algebra of `J`, which is `J` as an `𝒪_X`-module. -/
private noncomputable abbrev idealModule {X : Scheme.{u}} (J : X.IdealSheafData) : X.Modules :=
  (Stacks.Blowup.reesSheafGradedAlgebra J).piece 1

/-- The projective bundle `𝐏(𝒥) = Proj_X Sym 𝒥` of an ideal sheaf. -/
private noncomputable abbrev idealBundle {X : Scheme.{u}} (J : X.IdealSheafData) : Scheme.{u} :=
  (Stacks.SymGraded.schemeProjectiveBundle (idealModule J)
    (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent _)).scheme

/-- The projection `𝐏(𝒥) ⟶ X`. -/
private noncomputable abbrev idealBundleToBase {X : Scheme.{u}} (J : X.IdealSheafData) :
    idealBundle J ⟶ X :=
  (Stacks.SymGraded.schemeProjectiveBundle (idealModule J)
    (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent _)).toBase

section ImageSheaf

open CategoryTheory.Limits Stacks.RelativeProj

/-- Lifting along `𝐏(G) ⟶ 𝐏(F)` for an epimorphism `u : F ⟶ G`: a morphism `f : T ⟶ 𝐏(F)` over
`g` whose tautological quotient `g^* F ⟶ f^* 𝒪(1)` factors through `g^* u` factors through
`𝐏(G)`. -/
private theorem exists_comp_projectiveBundleMapOfEpi_of_factor {X : Scheme.{u}}
    {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
    (u : F ⟶ G) [Epi u] {T : Scheme.{u}} (f : T ⟶ projectiveBundle X F)
    (g : T ⟶ X) (hg : f ≫ projectiveBundleToBase X F = g)
    (q' : (Scheme.Modules.pullback g).obj G ⟶
      (Scheme.Modules.pullback f).obj (tautologicalDatum F).twist)
    (hq : (Scheme.Modules.pullback g).map u ≫ q' =
      (tautologicalDatum F).overQuotientMap f hg) :
    ∃ h : T ⟶ projectiveBundle X G, h ≫ projectiveBundleMapOfEpi u = f := by
  have hepi : Epi q' := by
    have : Epi ((Scheme.Modules.pullback g).map u ≫ q') :=
      hq ▸ (tautologicalDatum F).epi_overQuotientMap f hg
    exact epi_of_epi ((Scheme.Modules.pullback g).map u) q'
  let Q' : Stacks.Divisors.InvertibleQuotient T ((Scheme.Modules.pullback g).obj G) :=
    ⟨_, ((tautologicalDatum F).overQuotient ((Scheme.Modules.pullback g).obj F) (Iso.refl _) f
      hg).invertible, q', hepi⟩
  have hγ₀ := (tautologicalDatum G).overQuotient_classifyingMorphismOver_isEquivalent
    ((Scheme.Modules.pullback g).obj G) (Iso.refl _) Q'
  generalize (tautologicalDatum G).classifyingMorphismOver ((Scheme.Modules.pullback g).obj G)
    (Iso.refl _) Q' = c at hγ₀
  obtain ⟨hm, hhm⟩ := c
  refine ⟨hm, ?_⟩
  have hh₁ : (hm ≫ projectiveBundleMapOfEpi u) ≫ projectiveBundleToBase X F = g := by
    rw [Category.assoc, projectiveBundleMapOfEpi_comp_toBase]
    exact hhm
  refine (tautologicalDatum F).eq_of_overQuotient_isEquivalent ((Scheme.Modules.pullback g).obj F)
    (Iso.refl _) _ _ hh₁ hg ?_
  obtain ⟨β, hβ⟩ := exists_overQuotientMap_comp_projectiveBundleMapOfEpi u hm hhm hh₁
  obtain ⟨γ, hγ⟩ := hγ₀
  have hγ' : (tautologicalDatum G).overQuotientMap hm hhm ≫ γ.hom = q' := by
    simp only [TautologicalDatum.overQuotient_q, Iso.refl_hom, Category.id_comp] at hγ
    exact hγ
  refine ⟨β ≪≫ γ, ?_⟩
  show (Iso.refl _).hom ≫ (tautologicalDatum F).overQuotientMap _ hh₁ ≫ (β ≪≫ γ).hom =
    (Iso.refl _).hom ≫ (tautologicalDatum F).overQuotientMap f hg
  rw [Iso.refl_hom, Category.id_comp, Category.id_comp]
  exact (Category.assoc _ β.hom γ.hom).symm.trans ((congrArg (· ≫ γ.hom) hβ).trans
    ((Category.assoc _ _ _).trans
      ((congrArg ((Scheme.Modules.pullback g).map u ≫ ·) hγ').trans hq)))

/-- Pullback is right exact: a map out of `g^* E` killing `g^*` of the kernel of an epimorphism
`u : E ⟶ F` factors through `g^* u`. -/
private theorem exists_pullback_factor_of_epi {X T : Scheme.{u}} (g : T ⟶ X) {E F : X.Modules}
    (u : E ⟶ F) [Epi u] {W : T.Modules} (t : (Scheme.Modules.pullback g).obj E ⟶ W)
    (ht : (Scheme.Modules.pullback g).map (kernel.ι u) ≫ t = 0) :
    ∃ q : (Scheme.Modules.pullback g).obj F ⟶ W, (Scheme.Modules.pullback g).map u ≫ q = t := by
  have : (Scheme.Modules.pullback g).IsLeftAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction g).isLeftAdjoint
  have : (Scheme.Modules.pullback g).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  let hc := Abelian.epiIsCokernelOfKernel (f := u)
    (KernelFork.ofι (kernel.ι u) (kernel.condition u))
    (kernelIsKernel u)
  let hc' := CokernelCofork.mapIsColimit _ hc (Scheme.Modules.pullback g)
  exact ⟨hc'.desc (CokernelCofork.ofπ t (by simpa using ht)), hc'.fac _ .one⟩

/-- A map `t : g^* E ⟶ L` kills `g^*` of the kernel of `E ⟶ image (t^♭)`, where `t^♭` is its
adjoint `E ⟶ g_* L`. -/
private theorem pullback_map_kernel_comp_eq_zero {X T : Scheme.{u}} (g : T ⟶ X) {E : X.Modules}
    {L : T.Modules} (t : (Scheme.Modules.pullback g).obj E ⟶ L)
    (eps : E ⟶ (Scheme.Modules.pushforward g).obj L)
    (heps : eps = ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv E L) t) :
    (Scheme.Modules.pullback g).map (kernel.ι (Abelian.factorThruImage eps)) ≫ t = 0 := by
  have h := (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv_naturality_left
    (kernel.ι (Abelian.factorThruImage eps)) t
  rw [← heps] at h
  have h0 : kernel.ι (Abelian.factorThruImage eps) ≫ eps = 0 := by
    refine (congrArg (kernel.ι (Abelian.factorThruImage eps) ≫ ·)
      (Abelian.image.fac eps)).symm.trans ?_
    rw [← Category.assoc, kernel.condition, zero_comp]
  rw [h0] at h
  apply ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ L).injective
  rw [h]
  simp [Adjunction.homEquiv_unit]

/-- An epimorphism onto an invertible module on a nonempty scheme is nonzero. -/
theorem ne_zero_of_epi_of_isInvertible {X : Scheme.{u}} [Nonempty X] {A L : X.Modules}
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L)
    (t : A ⟶ L) [Epi t] : t ≠ 0 := by
  intro ht
  have hLz : IsZero L := by
    rw [IsZero.iff_id_eq_zero]
    refine (cancel_epi t).1 ?_
    rw [ht, zero_comp, zero_comp]
  exact not_isEmpty_of_nonempty X
    (Stacks.AlgebraicGeometry.ProjRepresentsF1.isEmpty_of_isZero_of_isInvertible X L
      ((Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr hL) hLz)

/-- A projective morphism `f : X' ⟶ X` from an integral scheme embeds into `𝐏(ℱ)` over `X` for a
nonzero quasi-coherent `ℱ` of finite type which is a subsheaf of `f_* ℒ` for an invertible `ℒ`:
take for `ℱ` the image of `ℰ ⟶ f_* ℒ` for an embedding `X' ⟶ 𝐏(ℰ)` with `ℒ = 𝒪(1)|_{X'}`. -/
private theorem exists_closedImmersion_bundle_mono_pushforward {X X' : Scheme.{u}}
    [IsIntegral X'] (f : X' ⟶ X) (hf : IsProjective f) :
    ∃ (F : X.Modules) (_ : F.IsQuasicoherent) (_ : F.IsFiniteType) (_ : ¬ Limits.IsZero F)
      (L : X'.Modules)
      (_ : AlgebraicGeometry.SheafOfModules.IsInvertible X'.presheaf X'.ringCatSheaf.2 L)
      (_ : F ⟶ (Scheme.Modules.pushforward f).obj L),
      Mono ‹F ⟶ (Scheme.Modules.pushforward f).obj L› ∧
      ∃ i : X' ⟶ (Stacks.RelativeProj.symGradedBundle F).scheme,
        IsClosedImmersion i ∧ i ≫ (Stacks.RelativeProj.symGradedBundle F).toBase = f := by
  have hqf : QuasiCompact f := hf.quasiCompact
  have hsf : IsSeparated f := hf.isSeparated
  have hqs : QuasiSeparated f := AlgebraicGeometry.IsSeparated.instQuasiSeparated f
  obtain ⟨E, hE, hEft, hqc, i, hi, hif⟩ := hf
  obtain rfl : hqc = Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E := rfl
  let i' : X' ⟶ (symGradedBundle E).scheme := i
  have hi' : IsClosedImmersion i' := hi
  have hif' : i' ≫ (symGradedBundle E).toBase = f := hif
  let i₁ : X' ⟶ projectiveBundle X E := i' ≫ (bundlePresentationIso E).hom
  have hg : i₁ ≫ projectiveBundleToBase X E = f := by
    rw [Category.assoc, bundlePresentationIso_hom_comp_toBase]
    exact hif'
  let D := tautologicalDatum E
  let L : X'.Modules := (Scheme.Modules.pullback i₁).obj D.twist
  have hL : AlgebraicGeometry.SheafOfModules.IsInvertible X'.presheaf X'.ringCatSheaf.2 L :=
    (D.overQuotient ((Scheme.Modules.pullback f).obj E) (Iso.refl _) i₁ hg).invertible
  let t : (Scheme.Modules.pullback f).obj E ⟶ L := D.overQuotientMap i₁ hg
  let eps : E ⟶ (Scheme.Modules.pushforward f).obj L :=
    ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv E L) t
  have : L.IsQuasicoherent := inferInstance
  have : ((Scheme.Modules.pushforward f).obj L).IsQuasicoherent :=
    AlgebraicGeometry.ProperCoherentFiniteType.isQuasicoherent_pushforward f L ‹_›
  have : (cokernel eps).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel eps
  have : (Abelian.image eps).IsQuasicoherent :=
    inferInstanceAs (kernel (cokernel.π eps)).IsQuasicoherent
  have : Epi (Abelian.factorThruImage eps) := inferInstance
  have : (Abelian.image eps).IsFiniteType :=
    (@Stacks.SheafOfModules.isFiniteType_of_epi.{u, u, u} _ _ _ X.ringCatSheaf _ _ _ E
      (Abelian.image eps) (Abelian.factorThruImage eps) ‹_›) inferInstance
  obtain ⟨q', hq⟩ := exists_pullback_factor_of_epi f (Abelian.factorThruImage eps) t
    (pullback_map_kernel_comp_eq_zero f t eps rfl)
  obtain ⟨h, hh⟩ := exists_comp_projectiveBundleMapOfEpi_of_factor (Abelian.factorThruImage eps)
    i₁ f hg q' hq
  have : IsClosedImmersion i₁ := by
    have : IsClosedImmersion i' := hi'
    infer_instance
  have : IsClosedImmersion (h ≫ projectiveBundleMapOfEpi (Abelian.factorThruImage eps)) :=
    hh ▸ inferInstance
  have : IsClosedImmersion h :=
    IsClosedImmersion.of_comp_isClosedImmersion h
      (projectiveBundleMapOfEpi (Abelian.factorThruImage eps))
  refine ⟨Abelian.image eps, inferInstance, inferInstance, ?_, L, hL, Abelian.image.ι eps,
    inferInstance, h ≫ (bundlePresentationIso (Abelian.image eps)).inv, inferInstance, ?_⟩
  · intro hz
    have : Epi t := D.epi_overQuotientMap i₁ hg
    refine ne_zero_of_epi_of_isInvertible hL t ?_
    rw [← hq, (Functor.map_isZero (Scheme.Modules.pullback f) hz).eq_of_tgt
      ((Scheme.Modules.pullback f).map (Abelian.factorThruImage eps)) 0, zero_comp]
  · rw [Category.assoc, bundlePresentationIso_inv_comp_toBase,
      ← projectiveBundleMapOfEpi_comp_toBase (Abelian.factorThruImage eps), ← Category.assoc, hh]
    exact hg

end ImageSheaf

section MonoToInvertible

open TopologicalSpace Opposite

/-- A section of an invertible module vanishing on `V' ≤ V` vanishes, provided restriction of
functions from any open `T` meeting `V` to `T ⊓ V'` is injective. -/
private theorem eq_zero_of_map_eq_zero_of_injective_restrict {X : RingedSpace.{u, u}}
    [∀ x : X.carrier, IsLocalRing (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X x)]
    (L : SheafOfModules.{u} (structureSheafRing X))
    [Stacks.SheafOfModules.IsInvertible X.presheaf (structureSheafRing X).property L]
    {V' V : Opens X.carrier} (h : V' ≤ V) (s : L.val.obj (op V))
    (hs : L.val.map (homOfLE h).op s = 0)
    (hinj : ∀ (T T' : Opens X.carrier) (hT : T' ≤ T), T' = T ⊓ V' → (∃ x ∈ V, x ∈ T) →
      Function.Injective (X.presheaf.map (homOfLE hT).op)) : s = 0 := by
  have hloc : ∀ x ∈ V, ∃ T : Opens X.carrier, ∃ hT : T ≤ V, x ∈ T ∧
      L.val.map (homOfLE hT).op s = 0 := by
    intro x hx
    obtain ⟨W, hxW, a, ha⟩ :=
      Stacks.SheafOfModules.exists_bijective_smul_of_isInvertible L x
    let T : Opens X.carrier := W ⊓ V
    have hTW : T ≤ W := inf_le_left
    have hTV : T ≤ V := inf_le_right
    let T' : Opens X.carrier := T ⊓ V'
    have hT'T : T' ≤ T := inf_le_left
    have hT'V' : T' ≤ V' := inf_le_right
    obtain ⟨c, hc⟩ := (ha T hTW).2 (L.val.map (homOfLE hTV).op s)
    have hc0 : X.presheaf.map (homOfLE hT'T).op c = 0 := by
      refine (ha T' (hT'T.trans hTW)).1 (a₁ := X.presheaf.map (homOfLE hT'T).op c)
        (a₂ := 0) ?_
      beta_reduce
      rw [zero_smul]
      have hc' : c • (L.val.map (homOfLE hTW).op) a = (L.val.map (homOfLE hTV).op) s := hc
      have e1 := Stacks.SheafOfModules.map_smul_restrict L hT'T c ((L.val.map (homOfLE hTW).op) a)
      have e2 := Stacks.SheafOfModules.map_restrict_comp L hT'T hTW a
      have e3 := Stacks.SheafOfModules.map_restrict_comp L hT'T hTV s
      have e4 := Stacks.SheafOfModules.map_restrict_comp L hT'V' h s
      have e5 : (L.val.map (homOfLE hT'V').op) ((L.val.map (homOfLE h).op) s) = 0 := by
        rw [hs]
        exact map_zero _
      refine (congrArg (fun z => X.presheaf.map (homOfLE hT'T).op c • z) e2.symm).trans ?_
      refine e1.symm.trans ?_
      refine (congrArg (fun z => (L.val.map (homOfLE hT'T).op) z) hc').trans ?_
      exact e3.trans (e4.symm.trans e5)
    have : c = 0 := (hinj T T' hT'T rfl ⟨x, hx, hxW, hx⟩) (by rw [hc0, map_zero])
    refine ⟨T, hTV, ⟨hxW, hx⟩, ?_⟩
    rw [← hc, this]
    exact zero_smul _ _
  refine TopCat.Presheaf.IsSheaf.section_ext (F := L.val.presheaf) (SheafOfModules.isSheaf L)
    (U := op V) (s := s) (t := 0) fun x hx => ?_
  obtain ⟨T, hT, hxT, h0⟩ := hloc x hx
  exact ⟨T, hT, hxT, h0.trans (map_zero _).symm⟩

/-- Restriction to a nonempty open is injective on sections of an invertible module over an
integral scheme. -/
private theorem sections_restrict_injective_of_isInvertible {Y : Scheme.{u}} [IsIntegral Y]
    (L : Y.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L)
    {V' V : Y.Opens} (h : V' ≤ V) (hne : Nonempty V') (s : Γ(L, V))
    (hs : L.val.map (homOfLE h).op s = 0) : s = 0 := by
  have hL' : Stacks.SheafOfModules.IsInvertible Y.presheaf
      (structureSheafRing Y.toRingedSpace).property L :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ L).2 hL
  have : ∀ z : Y.toRingedSpace.carrier,
      IsLocalRing (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk Y.toRingedSpace z) :=
    Y.isLocalRing
  refine eq_zero_of_map_eq_zero_of_injective_restrict (X := Y.toRingedSpace) L h s hs ?_
  intro T T' hT hT' ⟨x, hx, hxT⟩
  have : Nonempty T' := by
    subst hT'
    obtain ⟨y, hy1, hy2⟩ := nonempty_preirreducible_inter T.isOpen V'.isOpen
      ⟨x, hxT⟩ (Set.nonempty_coe_sort.1 hne)
    exact ⟨⟨y, hy1, hy2⟩⟩
  exact map_injective_of_isIntegral Y (homOfLE hT)

/-- Over an open `U` where `f` is an isomorphism, every open of `X'` inside `f⁻¹ U` is the
preimage of an open of `X` inside `U`, namely its image. -/
private theorem exists_opens_preimage_eq {X X' : Scheme.{u}} (f : X' ⟶ X) (U : X.Opens)
    [IsIso (f ∣_ U)] (S : X'.Opens) (hS : S ≤ f ⁻¹ᵁ U) :
    ∃ W : X.Opens, W ≤ U ∧ f ⁻¹ᵁ W = S ∧ ∀ w ∈ W, ∃ y ∈ S, f y = w := by
  let g := f ∣_ U
  have hopen : IsOpenMap g := (inferInstance : IsOpenImmersion g).base_open.isOpenMap
  let S₀ : Set (f ⁻¹ᵁ U) := (f ⁻¹ᵁ U).ι ⁻¹' (S : Set X')
  have hS₀ : IsOpen S₀ := S.isOpen.preimage (f ⁻¹ᵁ U).ι.continuous
  have himg : IsOpen (U.ι '' (g '' S₀)) :=
    U.ι.isOpenEmbedding.isOpenMap _ (hopen _ hS₀)
  have hcomm : ∀ z : f ⁻¹ᵁ U, U.ι (g z) = f ((f ⁻¹ᵁ U).ι z) := morphismRestrict_base_coe f U
  refine ⟨⟨_, himg⟩, ?_, ?_, ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    exact y.2
  · ext y
    constructor
    · rintro ⟨w, ⟨z, hz, rfl⟩, hw⟩
      have hyU : f y ∈ U := by rw [← hw]; exact (g z).2
      have hinj : Function.Injective g := (inferInstance : IsOpenImmersion g).base_open.injective
      obtain rfl : (⟨y, hyU⟩ : f ⁻¹ᵁ U) = z :=
        hinj (U.ι.isOpenEmbedding.injective ((hcomm _).trans hw.symm))
      exact hz
    · intro hy
      exact ⟨g ⟨y, hS hy⟩, ⟨⟨y, hS hy⟩, hy, rfl⟩, hcomm ⟨y, hS hy⟩⟩
  · rintro _ ⟨w, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨(f ⁻¹ᵁ U).ι z, hz, (hcomm z).symm⟩

/-- If `f` is an isomorphism over `U`, then `f.app W` is an isomorphism for every `W ≤ U`. -/
private theorem isIso_app_of_le {X X' : Scheme.{u}} (f : X' ⟶ X) (U : X.Opens)
    [IsIso (f ∣_ U)] (W : X.Opens) (hW : W ≤ U) : IsIso (f.app W) := by
  let V : U.toScheme.Opens := U.ι ⁻¹ᵁ W
  have hV : U.ι ''ᵁ V = W := by
    simp only [V, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr hW
  have h1 : IsIso ((f ∣_ U).app V) := inferInstance
  rw [morphismRestrict_app] at h1
  have h2 : IsIso (f.app (U.ι ''ᵁ V)) :=
    @IsIso.of_isIso_comp_right _ _ _ _ _ (f.app (U.ι ''ᵁ V))
      (X'.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V)).op) inferInstance h1
  exact hV ▸ h2

/-- An invertible module has a local generator around every point. -/
private theorem exists_generator_of_isInvertible {Y : Scheme.{u}} (L : Y.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L) (x : Y) :
    ∃ (T : Y.Opens) (_ : x ∈ T) (e : Γ(L, T)), ∀ (V : Y.Opens) (hV : V ≤ T),
      Function.Bijective fun c : Γ(Y, V) => c • L.presheaf.map (homOfLE hV).op e := by
  have hL' : Stacks.SheafOfModules.IsInvertible Y.presheaf
      (structureSheafRing Y.toRingedSpace).property L :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ L).2 hL
  have : ∀ z : Y.toRingedSpace.carrier,
      IsLocalRing (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk Y.toRingedSpace z) :=
    Y.isLocalRing
  exact Stacks.SheafOfModules.exists_bijective_smul_of_isInvertible (X := Y.toRingedSpace) L x

/-- A projective birational morphism of integral schemes is an isomorphism over a dense open. -/
private theorem exists_dense_open_isIso_of_isBirational {X X' : Scheme.{u}} [IsIntegral X]
    [IsIntegral X'] (f : X' ⟶ X) (hf : IsProjective f) (hb : IsBirational f) :
    ∃ U : X.Opens, Dense (U : Set X) ∧ IsIso (f ∣_ U) := by
  have : Finite (irreducibleComponents X) := by
    rw [irreducibleComponents_eq_singleton]; infer_instance
  have : Finite (irreducibleComponents X') := by
    rw [irreducibleComponents_eq_singleton]; infer_instance
  exact exists_dense_open_isIso_morphismRestrict_of_isBirational f hb (Or.inr hf.isSeparated)
    (Or.inl ⟨hf.locallyOfFiniteType, inferInstance⟩)

/-- The generic point of an integral scheme lies in every nonempty open. -/
private theorem genericPoint_mem_of_nonempty {X : Scheme.{u}} [IsIntegral X] (O : X.Opens)
    (hO : Nonempty O) : genericPoint X ∈ O :=
  ((genericPoint_spec X).mem_open_set_iff O.isOpen).2 (by simpa using hO)

/-- A birational morphism of integral schemes maps generic point to generic point. -/
private theorem map_genericPoint {X X' : Scheme.{u}} [IsIntegral X] [IsIntegral X']
    (f : X' ⟶ X) (hb : IsBirational f) : f (genericPoint X') = genericPoint X := by
  have h := hb.1.mapsTo (show genericPoint X' ∈ genericPoints X' by
    rw [genericPoints_eq_singleton]; rfl)
  rw [genericPoints_eq_singleton] at h
  exact h

/-- The preimage under a birational morphism of an open containing the generic point is
nonempty. -/
private theorem nonempty_preimage_of_isBirational {X X' : Scheme.{u}} [IsIntegral X]
    [IsIntegral X'] (f : X' ⟶ X) (hb : IsBirational f) {W : X.Opens} (hW : genericPoint X ∈ W) :
    Nonempty (f ⁻¹ᵁ W) :=
  ⟨⟨genericPoint X', show f (genericPoint X') ∈ W by rwa [map_genericPoint f hb]⟩⟩

/-- Inside any nonempty open `O` there is a nonempty open `W ≤ U` over which both `f_* ℒ` and `ℳ`
are free of rank one. -/
private theorem exists_open_trivializing {X X' : Scheme.{u}} [IsIntegral X] [IsIntegral X']
    (f : X' ⟶ X) (hb : IsBirational f) (U : X.Opens) (hU : Nonempty U) [IsIso (f ∣_ U)]
    (L : X'.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X'.presheaf X'.ringCatSheaf.2 L)
    (M : X.Modules)
    (hM : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M)
    (O : X.Opens) (hO : Nonempty O) :
    ∃ W : X.Opens, W ≤ O ∧ W ≤ U ∧ Nonempty W ∧
      (∃ eL : Γ((Scheme.Modules.pushforward f).obj L, W),
        Function.Bijective fun c : Γ(X, W) => c • eL) ∧
      (∃ eM : Γ(M, W), Function.Bijective fun c : Γ(X, W) => c • eM) := by
  have hξ := map_genericPoint f hb
  obtain ⟨TM, hξTM, eM, heM⟩ := exists_generator_of_isInvertible M hM (genericPoint X)
  obtain ⟨TL, hξTL, eL, heL⟩ := exists_generator_of_isInvertible L hL (genericPoint X')
  let P : X.Opens := TM ⊓ O ⊓ U
  have hξP : genericPoint X ∈ P :=
    ⟨⟨hξTM, genericPoint_mem_of_nonempty O hO⟩, genericPoint_mem_of_nonempty U hU⟩
  let S : X'.Opens := TL ⊓ f ⁻¹ᵁ P
  have hSU : S ≤ f ⁻¹ᵁ U := fun y hy => hy.2.2
  obtain ⟨W, hWU, hfW, hsurj⟩ := exists_opens_preimage_eq f U S hSU
  have hWP : W ≤ P := by
    intro w hw
    obtain ⟨y, hy, rfl⟩ := hsurj w hw
    exact hy.2
  have hξW : genericPoint X ∈ W := by
    have : genericPoint X' ∈ f ⁻¹ᵁ W := by
      rw [hfW]; exact ⟨hξTL, show f (genericPoint X') ∈ P by rw [hξ]; exact hξP⟩
    simpa [hξ] using this
  have hWTL : f ⁻¹ᵁ W ≤ TL := by rw [hfW]; exact inf_le_left
  have := isIso_app_of_le f U W hWU
  have hWTM : W ≤ TM := hWP.trans (inf_le_left.trans inf_le_left)
  refine ⟨W, hWP.trans (inf_le_left.trans inf_le_right), hWU, ⟨⟨genericPoint X, hξW⟩⟩,
    ⟨L.presheaf.map (homOfLE hWTL).op eL, ?_⟩, ⟨M.presheaf.map (homOfLE hWTM).op eM, heM W hWTM⟩⟩
  have h1 : Function.Bijective (f.app W) := (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
  exact (heL (f ⁻¹ᵁ W) hWTL).comp h1

/-- Naturality of a morphism of modules with respect to restriction. -/
private theorem app_naturality {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N) {U V : X.Opens}
    (h : U ≤ V) (x : Γ(M, V)) :
    N.presheaf.map (homOfLE h).op (φ.app V x) = φ.app U (M.presheaf.map (homOfLE h).op x) :=
  (congr($(φ.mapPresheaf.naturality (homOfLE h).op) x)).symm

/-- Sections of a module over an empty open coincide. -/
private theorem sections_eq_of_isEmpty {X : Scheme.{u}} (M : X.Modules) {V : X.Opens}
    [hV : IsEmpty V] (s t : Γ(M, V)) : s = t :=
  TopCat.Presheaf.IsSheaf.section_ext (F := M.presheaf) (Scheme.Modules.isSheaf M)
    (U := op V) (s := s) (t := t) fun x hx => (hV.false ⟨x, hx⟩).elim

/-- A morphism of modules injective on all sections is a monomorphism. -/
private theorem mono_of_injective_app {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ U, Function.Injective (φ.app U)) : Mono φ := by
  have : Mono ((Scheme.Modules.toPresheafOfModules X).map φ) :=
    PresheafOfModules.mono_of_injective (fun U => h U.unop)
  exact (Scheme.Modules.toPresheafOfModules X).mono_of_mono_map this

/-- A morphism from a subsheaf `ℱ` of `f_* ℒ` (`X'` integral, `f` birational, `ℒ` invertible) to
an invertible `ℳ` which is nonzero on one section is a monomorphism. -/
private theorem mono_of_ne_zero_of_mono_pushforward
    {X X' : Scheme.{u}} [IsIntegral X'] [IsIntegral X]
    (f : X' ⟶ X) (hf : IsProjective f) (hb : IsBirational f)
    (F : X.Modules) [F.IsQuasicoherent]
    (L : X'.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X'.presheaf X'.ringCatSheaf.2 L)
    (φ : F ⟶ (Scheme.Modules.pushforward f).obj L) [Mono φ]
    (M : X.Modules)
    (hM : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M)
    (ψ : F ⟶ M) (V : X.Opens) (b : Γ(F, V)) (hb' : ψ.app V b ≠ 0) : Mono ψ := by
  obtain ⟨U, hUd, hUi⟩ := exists_dense_open_isIso_of_isBirational f hf hb
  have := hUi
  have hUne : Nonempty U := hUd.nonempty.to_subtype
  have hφ := Stacks.AlgebraicGeometry.ReflexiveModules.injective_app_of_mono φ
  have hVne : Nonempty V := by
    by_contra hV
    have := not_nonempty_iff.1 hV
    exact hb' (sections_eq_of_isEmpty M _ _)
  apply mono_of_injective_app
  intro W
  show Function.Injective (ψ.app W).hom
  rw [injective_iff_map_eq_zero]
  intro s hs
  rcases isEmpty_or_nonempty W with hW | hWne
  · exact sections_eq_of_isEmpty F s 0
  have hO : Nonempty ↥(W ⊓ V) := by
    obtain ⟨y, hy1, hy2⟩ := nonempty_preirreducible_inter W.isOpen V.isOpen
      (Set.nonempty_coe_sort.1 hWne) (Set.nonempty_coe_sort.1 hVne)
    exact ⟨⟨y, hy1, hy2⟩⟩
  obtain ⟨W₁, hW₁O, hW₁U, hW₁ne, ⟨eL, heL⟩, ⟨eM, heM⟩⟩ :=
    exists_open_trivializing f hb U hUne L hL M hM (W ⊓ V) hO
  have hW₁W : W₁ ≤ W := hW₁O.trans inf_le_left
  have hW₁V : W₁ ≤ V := hW₁O.trans inf_le_right
  have : IsDomain Γ(X, W₁) := IsIntegral.component_integral W₁
  let s₁ : Γ(F, W₁) := F.presheaf.map (homOfLE hW₁W).op s
  let b₁ : Γ(F, W₁) := F.presheaf.map (homOfLE hW₁V).op b
  obtain ⟨α, hα⟩ := heL.2 (φ.app W₁ s₁)
  obtain ⟨β, hβ⟩ := heL.2 (φ.app W₁ b₁)
  have hrel : β • s₁ = α • b₁ := by
    apply hφ W₁
    rw [Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul, ← hα, ← hβ, smul_smul,
      smul_smul, mul_comm]
  have hψs₁ : ψ.app W₁ s₁ = 0 := by
    have := app_naturality ψ hW₁W s
    rw [hs, map_zero] at this
    exact this.symm
  have hψb₁ : ψ.app W₁ b₁ ≠ 0 := by
    intro h
    apply hb'
    refine sections_restrict_injective_of_isInvertible M hM hW₁V hW₁ne _ ?_
    exact (app_naturality ψ hW₁V b).trans h
  obtain ⟨γ, hγ⟩ := heM.2 (ψ.app W₁ b₁)
  have hγ0 : γ ≠ 0 := fun h => hψb₁ (by rw [← hγ]; simp [h])
  have hα0 : α = 0 := by
    have h1 : ψ.app W₁ (β • s₁) = ψ.app W₁ (α • b₁) := congrArg _ hrel
    rw [Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul, hψs₁, smul_zero, ← hγ,
      smul_smul] at h1
    have h2 : (α * γ) • eM = (0 : Γ(X, W₁)) • eM := by
      rw [zero_smul]
      exact h1.symm
    exact (mul_eq_zero.1 (heM.1 h2)).resolve_right hγ0
  have hφs₁ : φ.app W₁ s₁ = 0 := by
    have hα' : α • eL = φ.app W₁ s₁ := hα
    rw [← hα', hα0, zero_smul]
  have hnat := app_naturality φ hW₁W s
  have hφs : φ.app W s = 0 :=
    sections_restrict_injective_of_isInvertible L hL (fun y hy => hW₁W hy)
      (nonempty_preimage_of_isBirational f hb (genericPoint_mem_of_nonempty W₁ hW₁ne))
      (φ.app W s) (hnat.trans hφs₁)
  exact hφ W (by rw [hφs, map_zero])

end MonoToInvertible

section SerreTwist

open Stacks.AlgebraicGeometry
open scoped MonoidalCategory

attribute [local instance] Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

/-- A module all of whose sections vanish is zero. -/
private lemma isZero_of_forall_sections {Y : Scheme.{u}} {M : Y.Modules}
    (h : ∀ (U : Y.Opens) (s : Γ(M, U)), s = 0) : Limits.IsZero M := by
  rw [Limits.IsZero.iff_id_eq_zero]
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  ext s
  exact (h U _).trans (h U _).symm

/-- A module all of whose global sections vanish has a unique compatible family of sections. -/
private lemma subsingleton_sections_of_forall_top {X : Scheme.{u}} (P : X.Modules)
    (h : ∀ x : P.val.obj (Opposite.op (⊤ : X.Opens)), x = 0) : Subsingleton P.sections := by
  refine ⟨fun a b => ?_⟩
  apply Subtype.ext
  funext U
  induction U using Opposite.rec with | op V =>
  have key : ∀ c : P.sections, c.1 (Opposite.op V) = 0 := by
    intro c
    have h2 := c.2 (homOfLE (le_top : V ≤ ⊤)).op
    have h3 : c.1 (Opposite.op ⊤) = 0 := h _
    rw [← h2]
    change (P.val.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom (c.1 (Opposite.op ⊤)) = 0
    rw [h3]
    exact map_zero _
  rw [key a, key b]

/-- Serre twisting: a coherent `ℱ` with nonzero generic stalk on a noetherian integral scheme with
an ample `ℋ` has a nonzero map to some `ℋ^{⊗ n}`, since `ℱ^∨ ⊗ ℋ^{⊗ n}` is globally generated
for `n ≫ 0`. -/
private theorem exists_ne_zero_hom_tensorPow_of_nontrivial_stalk
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (H : X.Modules) [Stacks.Ample.IsInvertibleModule X H] (hH : Stacks.Ample.IsAmple X H)
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (hF : Nontrivial (F.presheaf.stalk (genericPoint X))) :
    ∃ (n : ℤ) (ψ : F ⟶ Stacks.Ample.tensorPowModule X H n), ψ ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hcoh : F.IsCoherent := CoherentOfFiniteType.isCoherent_of_isQuasicoherent_of_isFiniteType F
  have : F.IsFinitePresentation := isFinitePresentation_of_isCoherent F
  have hGcoh : (ReflexiveModules.dualSheaf F).IsCoherent :=
    ReflexiveEquivalence.isCoherent_dualSheaf F
  have : (ReflexiveModules.dualSheaf F).IsQuasicoherent := isQuasicoherent_of_isCoherent _
  have : (ReflexiveModules.dualSheaf F).IsFiniteType := hGcoh.isFiniteType
  obtain ⟨-, hserre⟩ :=
    Stacks.AmpleCharacterization.quasiSeparatedSpace_and_isGeneratedByGlobalSections_of_isAmple
      H hH
  obtain ⟨n₀, hn₀⟩ := hserre (ReflexiveModules.dualSheaf F) inferInstance inferInstance
  obtain ⟨σ⟩ := hn₀ n₀ le_rfl
  set N := Stacks.Ample.tensorPowModule X H n₀
  let G := ReflexiveModules.dualSheaf F
  have β : (G ⊗ N : X.Modules) ≅ AlgebraicGeometry.CoherentReflexive.tensorModules N G :=
    β_ G N ≪≫ Stacks.TensorSheafSpellingIso.monoidalTensorIso X N G
  let P : X.Modules := AlgebraicGeometry.CoherentReflexive.sheafHomModule F N
  let π' : (G ⊗ N : X.Modules) ⟶ P :=
    β.hom ≫ AlgebraicGeometry.CoherentReflexive.tensorDualToSheafHomModule F N
  have hπ' : π' = 0 := by
    have hsub : Subsingleton P.sections := by
      refine subsingleton_sections_of_forall_top _ fun x => ?_
      have e := (Stacks.Algebraization.internalHomSectionsTopMapAddEquiv F N).apply_symm_apply x
      rw [← e, hcon n₀ ((Stacks.Algebraization.internalHomSectionsTopMapAddEquiv F N).symm x)]
      exact map_zero _
    have : Epi σ.π := σ.epi
    refine (cancel_epi σ.π).1 ?_
    have h1 := SheafOfModules.freeHomEquiv_symm_comp σ.s π'
    have h2 := SheafOfModules.freeHomEquiv_symm_comp σ.s (0 : (G ⊗ N : X.Modules) ⟶ P)
    refine h1.trans (Eq.trans ?_ h2.symm)
    congr 1
    funext i
    exact Subsingleton.elim _ _
  have hpi : AlgebraicGeometry.CoherentReflexive.tensorDualToSheafHomModule F N = 0 := by
    refine (cancel_epi β.hom).1 ?_
    rw [Limits.comp_zero]
    exact hπ'
  let ξ := genericPoint X
  have : Module.Finite (X.presheaf.stalk ξ) (F.presheaf.stalk ξ) :=
    Scheme.Modules.finite_stalk_of_isCoherent F ξ
  have hbij :=
    CoherentReflexive.bijective_stalkMapOfHom_tensorDualToSheafHomModule F N ξ
  rw [hpi] at hbij
  have htriv : ∀ y : P.presheaf.stalk ξ, y = 0 := by
    intro y
    obtain ⟨x, hx⟩ := hbij.2 y
    rw [← hx]
    have h0 : Stacks.AlgebraicGeometry.ReflexiveModules.stalkMapOfHom
        (0 : CoherentReflexive.tensorModules N G ⟶ P) ξ = 0 := by
      unfold Stacks.AlgebraicGeometry.ReflexiveModules.stalkMapOfHom
      exact Functor.map_zero _ _ _
    rw [h0]
    rfl
  have hnt : Nontrivial (F.presheaf.stalk ξ →ₗ[X.presheaf.stalk ξ] N.presheaf.stalk ξ) := by
    have : Nontrivial (N.presheaf.stalk ξ) := by
      obtain ⟨e⟩ := Stacks.InvertibleStalk.nonempty_linearEquiv_stalk N ξ
      exact e.toEquiv.nontrivial
    obtain ⟨v, hv⟩ := exists_ne (0 : F.presheaf.stalk ξ)
    obtain ⟨n, hn⟩ := exists_ne (0 : N.presheaf.stalk ξ)
    obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : Module.Dual (X.presheaf.stalk ξ) (F.presheaf.stalk ξ), ℓ v ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hv ((Module.forall_dual_apply_eq_zero_iff (X.presheaf.stalk ξ) v).1 hc)
    exact ⟨ℓ.smulRight n, 0, fun h =>
      hn ((smul_eq_zero.1 (LinearMap.congr_fun h v)).resolve_left hℓ)⟩
  obtain ⟨g, hg⟩ := exists_ne (0 : F.presheaf.stalk ξ →ₗ[X.presheaf.stalk ξ] N.presheaf.stalk ξ)
  exact hg (by
    have := htriv ((AlgebraicGeometry.CoherentReflexive.sheafHomModuleStalkEquiv F N ξ).symm g)
    simpa using congrArg (AlgebraicGeometry.CoherentReflexive.sheafHomModuleStalkEquiv F N ξ) this)

/-- A nonzero subsheaf of `f_* ℒ` (`ℒ` invertible, `f` birational) has nonzero generic stalk. -/
private theorem nontrivial_stalk_generic_of_mono_pushforward {X X' : Scheme.{u}}
    [IsIntegral X'] [IsIntegral X] (f : X' ⟶ X) (hb : IsBirational f) (F : X.Modules)
    (hF : ¬ Limits.IsZero F) (L : X'.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X'.presheaf X'.ringCatSheaf.2 L)
    (φ : F ⟶ (Scheme.Modules.pushforward f).obj L) [Mono φ] :
    Nontrivial (F.presheaf.stalk (genericPoint X)) := by
  by_contra hc
  rw [not_nontrivial_iff_subsingleton] at hc
  apply hF
  refine isZero_of_forall_sections fun V a => ?_
  have hφ := Stacks.AlgebraicGeometry.ReflexiveModules.injective_app_of_mono φ
  rcases isEmpty_or_nonempty V with hV | hV
  · exact sections_eq_of_isEmpty F a 0
  · have hξ := genericPoint_mem_of_nonempty V hV
    have hg : F.presheaf.germ V (genericPoint X) hξ a =
        F.presheaf.germ V (genericPoint X) hξ 0 := Subsingleton.elim _ _
    obtain ⟨W, hξW, iV, iV', h⟩ := TopCat.Presheaf.germ_eq _ _ _ _ _ _ hg
    have hle : W ≤ V := leOfHom iV
    have h0 : F.presheaf.map (homOfLE hle).op a = 0 := h.trans (map_zero _)
    have hnat := app_naturality φ hle a
    have hz : φ.app V a = 0 :=
      sections_restrict_injective_of_isInvertible L hL (fun y hy => hle hy)
        (nonempty_preimage_of_isBirational f hb hξW) (φ.app V a)
        (hnat.trans ((congrArg (φ.app W) h0).trans (map_zero _)))
    exact hφ V (hz.trans (map_zero _).symm)

end SerreTwist

/-- A nonzero subsheaf of finite type of `f_* ℒ` on a quasi-projective variety has a nonzero map
to an invertible module. -/
private theorem exists_hom_to_invertible_ne_zero_of_mono_pushforward {k : Type u} [Field k]
    {X X' : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsQuasiProjectiveVariety k sX] [IsIntegral X']
    (f : X' ⟶ X) (hb : IsBirational f)
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (hF : ¬ Limits.IsZero F) (L : X'.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X'.presheaf X'.ringCatSheaf.2 L)
    (φ : F ⟶ (Scheme.Modules.pushforward f).obj L) [Mono φ] :
    ∃ (M : X.Modules)
      (_ : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M)
      (ψ : F ⟶ M) (V : X.Opens) (a : Γ(F, V)), ψ.app V a ≠ 0 := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  obtain ⟨H, hHinv, hHa⟩ := AlgebraicGeometry.exists_isAmple_of_isQuasiProjective sX
    (Stacks.Ample.unitModule (Spec (.of k)))
    (Stacks.Ample.isAmple_unitModule_of_isAffine _)
    (IsQuasiProjectiveVariety.isQuasiProjective (f := sX))
  have := hHinv
  have hnt := nontrivial_stalk_generic_of_mono_pushforward f hb F hF L hL φ
  obtain ⟨n, ψ, hψ⟩ := exists_ne_zero_hom_tensorPow_of_nontrivial_stalk H hHa F hnt
  refine ⟨Stacks.Ample.tensorPowModule X H n, inferInstance, ψ, ?_⟩
  by_contra hcon
  push Not at hcon
  refine hψ (Scheme.Modules.hom_ext _ _ fun U => ?_)
  ext s
  exact (hcon U s).trans (by simp)

/-- The first power `J ^ 1`, as a submodule of `𝒪_X`, is the degree-one piece `idealModule J` of
the Rees algebra of `J`. -/
private noncomputable def idealPowOneIsoIdealModule {X : Scheme.{u}} (J : X.IdealSheafData) :
    Stacks.AlgebraicGeometry.IdealPowerColimit.idealPow J 1 ≅ idealModule J :=
  eqToIso (congrArg SheafOfModules.Submodule.toSheafOfModules
      (Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowerMultiple_one_eq_unitSubmodule J)) ≪≫
    Stacks.ClosedSubscheme.unitSubmoduleIsoKernel J ≪≫
    (eqToIso (congrArg (fun K : X.IdealSheafData => Limits.kernel (C := X.Modules)
      (Stacks.ClosedSubscheme.structureSheafProjection K)) (pow_one J)).symm ≪≫
      (Iso.refl _ : Limits.kernel (C := X.Modules)
        (Stacks.ClosedSubscheme.structureSheafProjection (J ^ 1)) ≅ idealModule J))

/-- A quasi-coherent subsheaf of `𝒪_X` is the ideal sheaf it generates, viewed as a module. -/
private theorem exists_iso_idealModule_of_mono_unit {X : Scheme.{u}} (G : X.Modules)
    [G.IsQuasicoherent]
    (ι : G ⟶ Stacks.AlgebraicGeometry.IdealPowerColimit.structureModule X) [Mono ι] :
    Nonempty (G ≅ idealModule (idealSheafDataOfHom G ι)) := by
  have : Epi (toIdealPowOfHom G ι) := epi_toIdealPowOfHom G ι
  have : Mono (toIdealPowOfHom G ι) :=
    mono_of_mono_fac (toIdealPowOfHom_ι G ι)
  have := isIso_of_mono_of_epi (toIdealPowOfHom G ι)
  exact ⟨asIso (toIdealPowOfHom G ι) ≪≫ idealPowOneIsoIdealModule _⟩

/-- Tensoring on the right with `L`, as an endofunctor of `X.Modules`. -/
private noncomputable abbrev tensorRight {X : Scheme.{u}} (L : X.Modules) :
    X.Modules ⥤ X.Modules :=
  (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} ⟨X.sheaf.obj,
    Presheaf.isSheaf_of_isSheaf_comp _ X.sheaf.obj (forget₂ CommRingCat RingCat)
      X.ringCatSheaf.property⟩).flip.obj L

/-- Cancelling an invertible tensor factor on the other side: `(F ⊗ L^{⊗ -1}) ⊗ L ≅ F`. -/
private noncomputable def tensorInverseCancelIso {X : Scheme.{u}} (F L : X.Modules)
    [hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    Scheme.Modules.tensorObj (Scheme.Modules.tensorObj F (Scheme.Modules.tensorInverse L)) L ≅ F :=
  have hLst : Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ L hL
  have _ := hLst
  have _ : (tensorRight L).IsEquivalence :=
    Stacks.SheafOfModules.TensorPower.isEquivalence_tensorRightFunctor X.sheaf.obj
      X.ringCatSheaf.property L
  have eLW : Scheme.Modules.tensorObj (Scheme.Modules.tensorInverse L) L ≅
      SheafOfModules.unit X.ringCatSheaf :=
    Stacks.SheafOfModules.Invertible.tensorProductIso X.sheaf.obj X.ringCatSheaf.property
        (Iso.refl _) (Stacks.SheafOfModules.Invertible.tensorPowerOneIso X.sheaf.obj
          X.ringCatSheaf.property L).symm ≪≫
      Stacks.SheafOfModules.TensorPower.tensorPowerMulIso X.sheaf.obj X.ringCatSheaf.property
        L (-1) 1
  Stacks.SheafOfModules.Invertible.tensorProductAssociator X.sheaf.obj
      X.ringCatSheaf.property F _ L ≪≫
    Stacks.SheafOfModules.Invertible.tensorProductIso X.sheaf.obj X.ringCatSheaf.property
      (Iso.refl F) eLW ≪≫
    Stacks.SheafOfModules.Invertible.tensorProductRightUnitor X.sheaf.obj
      X.ringCatSheaf.property F

attribute [local instance] Stacks.Algebraization.sectionsModuleΓ
  Stacks.Algebraization.sectionsModuleΓSheaf Stacks.Algebraization.sectionsSMulCommClassΓ in
/-- A subsheaf of `𝒪_X` whose ideal sheaf is `⊥` is zero. -/
private lemma isZero_of_mono_unit_of_idealSheafDataOfHom_eq_bot {X : Scheme.{u}} (G : X.Modules)
    [G.IsQuasicoherent] (ι : G ⟶ Stacks.AlgebraicGeometry.IdealPowerColimit.structureModule X)
    [Mono ι] (h : idealSheafDataOfHom G ι = ⊥) : Limits.IsZero G := by
  refine isZero_of_forall_sections fun U s => ?_
  apply Stacks.AlgebraicGeometry.ReflexiveModules.injective_app_of_mono ι U
  have key : ι.app U s ∈ (⊥ : (Stacks.AlgebraicGeometry.IdealPowerColimit.structureModule
      X).Submodule).toSubmodule.obj (Opposite.op U) := by
    refine Stacks.Algebraization.mem_submodule_of_affine _ U (ι.app U s) fun V i => ?_
    have hn := map_structureAppₗ ι i.le s
    have hmem : structureAppₗ ι V.1 (G.presheaf.map i.op s) ∈
        (idealSheafDataOfHom G ι).ideal V := LinearMap.mem_range_self _ _
    rw [h, Scheme.IdealSheafData.ideal_bot] at hmem
    have hz : structureAppₗ ι V.1 (G.presheaf.map i.op s) = 0 := Ideal.mem_bot.mp hmem
    have h0 : (Stacks.AlgebraicGeometry.IdealPowerColimit.structureModule X).val.map i.op
        (ι.app U s) = 0 := hn.trans hz
    rw [h0]
    exact Submodule.zero_mem _
  have key' : ι.app U s = 0 := by
    letI : Module ↑(X.ringCatSheaf.obj.obj (Opposite.op U))
        ↑Γ(Stacks.AlgebraicGeometry.IdealPowerColimit.structureModule X, U) :=
      ((Stacks.AlgebraicGeometry.IdealPowerColimit.structureModule X).val.obj
        (Opposite.op U)).isModule
    exact (Submodule.mem_bot _).mp ((SheafOfModules.Submodule.bot_obj
      (Stacks.AlgebraicGeometry.IdealPowerColimit.structureModule X) (Opposite.op U)).le key)
  rw [key', map_zero]

/-- A nonzero quasi-coherent subsheaf `ℱ` of an invertible `ℳ` is `𝒥 ⊗ ℳ` for a nonzero ideal sheaf
`𝒥`, namely the image of `ℱ ⊗ ℳ^{-1} ⟶ 𝒪_X`. -/
private theorem exists_iso_idealModule_tensor_of_mono_invertible {X : Scheme.{u}}
    (F : X.Modules) [F.IsQuasicoherent] (hF : ¬ Limits.IsZero F) (M : X.Modules)
    (hM : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M)
    (ψ : F ⟶ M) [Mono ψ] :
    ∃ (J : X.IdealSheafData) (_ : J ≠ ⊥),
      Nonempty (F ≅ Scheme.Modules.tensorObj (idealModule J) M) := by
  have hM'' : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj
    X.ringCatSheaf.property M := hM
  let N : X.Modules := Scheme.Modules.tensorInverse M
  have hN : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N :=
    Scheme.Modules.isInvertible_tensorInverse M
  have hMst : Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ M hM''
  have _ := hMst
  have _ : (tensorRight M).IsEquivalence :=
    Stacks.SheafOfModules.TensorPower.isEquivalence_tensorRightFunctor X.sheaf.obj
      X.ringCatSheaf.property M
  have eMN : Scheme.Modules.tensorObj M N ≅
      Stacks.AlgebraicGeometry.IdealPowerColimit.structureModule X :=
    Stacks.SheafOfModules.Invertible.tensorProductIso X.sheaf.obj X.ringCatSheaf.property
        (Stacks.SheafOfModules.Invertible.tensorPowerOneIso X.sheaf.obj
          X.ringCatSheaf.property M).symm (Iso.refl _) ≪≫
      Stacks.SheafOfModules.TensorPower.tensorPowerMulIso X.sheaf.obj X.ringCatSheaf.property
        M 1 (-1)
  let G : X.Modules := Scheme.Modules.tensorObj F N
  let R : X.Modules ⥤ X.Modules := tensorRight N
  let ι : G ⟶ Stacks.AlgebraicGeometry.IdealPowerColimit.structureModule X := R.map ψ ≫ eMN.hom
  have hR : R.IsEquivalence := Scheme.Modules.isEquivalence_invertibleTensorRightFunctor N
  have : Mono (R.map ψ) := Functor.map_mono R ψ
  have hι : Mono ι := by
    have hw : ι ≫ eMN.inv = R.map ψ := by
      change (R.map ψ ≫ eMN.hom) ≫ eMN.inv = R.map ψ
      rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    have : Mono (ι ≫ eMN.inv) := by rw [hw]; infer_instance
    exact mono_of_mono ι eMN.inv
  have : N.IsQuasicoherent := AlgebraicGeometry.isQuasicoherent_of_isInvertible N
  have : G.IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_tensorObj F N inferInstance inferInstance
  obtain ⟨e⟩ := exists_iso_idealModule_of_mono_unit G ι
  refine ⟨idealSheafDataOfHom G ι, ?_, ⟨(tensorInverseCancelIso F M).symm ≪≫ ?_⟩⟩
  · intro hJ
    apply hF
    have hGz : Limits.IsZero G := isZero_of_mono_unit_of_idealSheafDataOfHom_eq_bot G ι hJ
    rw [Limits.IsZero.iff_id_eq_zero]
    exact R.map_injective (hGz.eq_of_src (R.map (𝟙 F)) (R.map 0))
  · exact (tensorRight M).mapIso e

/-- **Twist invariance of the projective bundle** (Stacks 02NC): `𝐏(ℱ ⊗ ℳ) ≅ 𝐏(ℱ)` over the base
for invertible `ℳ`; a module `G ≅ ℱ ⊗ ℳ` has the same bundle. -/
private theorem exists_bundleIso_twist {X : Scheme.{u}} (F G M : X.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent]
    (hM : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M)
    (e : G ≅ Scheme.Modules.tensorObj F M) :
    ∃ e' : (Stacks.RelativeProj.symGradedBundle G).scheme ≅
        (Stacks.RelativeProj.symGradedBundle F).scheme,
      e'.hom ≫ (Stacks.RelativeProj.symGradedBundle F).toBase =
        (Stacks.RelativeProj.symGradedBundle G).toBase := by
  have : Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr hM
  obtain ⟨t, ht⟩ := Stacks.SymProjectiveBundleTwist.exists_iso_schemeProjectiveBundle_tensorObj F M
  refine ⟨MMP.ProjectiveBundleCongr.bundleIso e ≪≫ t, ?_⟩
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ht).trans
    (MMP.ProjectiveBundleCongr.bundleIso_hom_toBase e))

/-- A projective birational `f : X' ⟶ X` onto a quasi-projective variety embeds as a closed
subscheme of `𝐏(𝒥)` over `X` for a nonzero ideal sheaf `𝒥`. -/
private theorem exists_closedImmersion_idealBundle {k : Type u} [Field k]
    {X X' : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsQuasiProjectiveVariety k sX] [IsIntegral X']
    (f : X' ⟶ X) (hf : IsProjective f) (hb : IsBirational f) :
    ∃ (J : X.IdealSheafData) (_ : J ≠ ⊥) (i : X' ⟶ idealBundle J),
      IsClosedImmersion i ∧ i ≫ idealBundleToBase J = f := by
  obtain ⟨F, hF, hFt, hF0, L, hL, φ, hφ, i, hi, hif⟩ :=
    exists_closedImmersion_bundle_mono_pushforward f hf
  obtain ⟨M, hM, ψ, V, a, ha⟩ :=
    exists_hom_to_invertible_ne_zero_of_mono_pushforward sX f hb F hF0 L hL φ
  have := mono_of_ne_zero_of_mono_pushforward f hf hb F L hL φ M hM ψ V a ha
  obtain ⟨J, hJ, ⟨α⟩⟩ := exists_iso_idealModule_tensor_of_mono_invertible F hF0 M hM ψ
  obtain ⟨e', he'⟩ := exists_bundleIso_twist (idealModule J) F M hM α
  exact ⟨J, hJ, i ≫ e'.hom, IsClosedImmersion.comp i e'.hom,
    (Category.assoc _ _ _).trans ((congrArg (i ≫ ·) he').trans hif)⟩

/-- The blowup of an ideal sheaf `𝒥` of finite type is a closed subscheme of `𝐏(𝒥)` over `X`. -/
private theorem exists_closedImmersion_blowUp_idealBundle {X : Scheme.{u}} (J : X.IdealSheafData)
    (hJ : J.IsFiniteType) :
    ∃ i : blowUp J ⟶ idealBundle J,
      IsClosedImmersion i ∧ i ≫ idealBundleToBase J = blowUpToBase J := by
  obtain ⟨e, he⟩ := Stacks.Blowup.exists_iso_relativeProj_reesSheafGradedAlgebra_blowUp J
  have hgen := Stacks.Blowup.isGeneratedInDegreeOne_reesSheafGradedAlgebra J
  obtain ⟨-, hci, hcomp⟩ := isProjective_relativeProj_toBase_and_isClosedImmersion
    (Stacks.Blowup.reesSheafGradedAlgebra J) hgen
    (Stacks.Blowup.isFiniteType_reesSheafGradedAlgebra_piece J hJ 1)
  let c : (Stacks.AlgebraicGeometry.RelativeProj.relativeProj
      (Stacks.Blowup.reesSheafGradedAlgebra J)).scheme ⟶ idealBundle J :=
    Stacks.Tag01VMRelativeVeryAmple.canonicalSymProjHom _ hgen
  have hci' : IsClosedImmersion c := hci
  have hcomp' : c ≫ idealBundleToBase J =
      (Stacks.AlgebraicGeometry.RelativeProj.relativeProj
        (Stacks.Blowup.reesSheafGradedAlgebra J)).toBase := hcomp
  refine ⟨e.inv ≫ c, inferInstance, ?_⟩
  rw [Category.assoc, hcomp', ← he, Iso.inv_hom_id_assoc]

/-- Precomposing with an isomorphism preserves being an isomorphism over `U`. -/
private lemma isIso_restrict_iso_comp {P Q X : Scheme.{u}} (e : P ≅ Q) (q : Q ⟶ X) (U : X.Opens)
    (h : IsIso (q ∣_ U)) : IsIso ((e.hom ≫ q) ∣_ U) := by
  rw [morphismRestrict_comp]
  have h2 : IsIso (e.hom ∣_ (q ⁻¹ᵁ U)) := by
    delta morphismRestrict
    infer_instance
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h2 h

/-- If the restriction of a quasi-coherent `E` to an open `U` is invertible, then `𝐏(E) ⟶ X` is
an isomorphism over `U`. -/
private theorem isIso_projectiveBundleToBase_restrict_of_isInvertible {X : Scheme.{u}}
    (E : X.Modules) [E.IsQuasicoherent] (U : X.Opens)
    [((Scheme.Modules.pullback U.ι).obj E).IsQuasicoherent]
    (hE : AlgebraicGeometry.SheafOfModules.IsInvertible U.toScheme.presheaf
      U.toScheme.ringCatSheaf.2 ((Scheme.Modules.pullback U.ι).obj E)) :
    IsIso (Stacks.RelativeProj.projectiveBundleToBase X E ∣_ U) := by
  have hsq := Stacks.RelativeProj.isPullback_projectiveBundleBaseChange U.ι E
    ((Scheme.Modules.pullback U.ι).obj E) (Iso.refl _)
  have hiso := Stacks.RelativeProj.isIso_projectiveBundleToBase_of_isInvertible _ hE
  have hsq2 := isPullback_morphismRestrict (Stacks.RelativeProj.projectiveBundleToBase X E) U
  let e := hsq.isoIsPullback _ _ hsq2.flip
  have h1 : e.hom ≫ (Stacks.RelativeProj.projectiveBundleToBase X E ∣_ U) =
      Stacks.RelativeProj.projectiveBundleToBase _ _ := IsPullback.isoIsPullback_hom_snd _ _ _ _
  have : (Stacks.RelativeProj.projectiveBundleToBase X E ∣_ U) =
      e.inv ≫ Stacks.RelativeProj.projectiveBundleToBase _ _ := by
    rw [← h1, Iso.inv_hom_id_assoc]
  rw [this]
  infer_instance

/-- The complement of the support of an ideal sheaf, as an open of the scheme. -/
private abbrev offCentre {X : Scheme.{u}} (J : X.IdealSheafData) : X.Opens := J.support.compl

/-- The pullback to an open disjoint from a closed subscheme of the pushforward of a module on the
subscheme is zero. -/
private lemma isZero_pullback_pushforward_of_disjoint {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (N : Z.Modules) (U : X.Opens) (hU : Disjoint (Set.range i) (U : Set X)) :
    Limits.IsZero ((Scheme.Modules.pullback U.ι).obj ((Scheme.Modules.pushforward i).obj N)) := by
  refine Limits.IsZero.of_iso ?_
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app
      ((Scheme.Modules.pushforward i).obj N)).symm
  refine isZero_of_forall_sections fun W s => ?_
  have key : ∀ V : Z.Opens, V = ⊥ → ∀ t : Γ(N, V), t = 0 := by
    intro V hV t
    subst hV
    let F : TopCat.Sheaf Ab Z := (SheafOfModules.toSheaf _).obj N
    exact (AddCommGrpCat.subsingleton_of_isZero F.isTerminalOfEmpty.isZero).elim t 0
  have hV : (i ⁻¹ᵁ (U.ι ''ᵁ W)) = ⊥ := by
    refine le_bot_iff.mp fun z hz => ?_
    have h1 : i z ∈ (U.ι ''ᵁ W : Set X) := hz
    have h2 : i z ∈ (U : Set X) := by
      obtain ⟨a, -, ha⟩ := h1
      rw [← ha]; exact a.2
    exact (Set.disjoint_left.mp hU ⟨z, rfl⟩ h2).elim
  exact key _ hV s

/-- Away from its support, an ideal sheaf is invertible (it is the unit module there). -/
private theorem isInvertible_pullback_idealModule {X : Scheme.{u}} (J : X.IdealSheafData) :
    AlgebraicGeometry.SheafOfModules.IsInvertible (offCentre J).toScheme.presheaf
      (offCentre J).toScheme.ringCatSheaf.2
      ((Scheme.Modules.pullback (offCentre J).ι).obj (idealModule J)) := by
  let S := Stacks.ClosedSubscheme.idealShortComplex (J ^ 1)
  have hS := Stacks.ClosedSubscheme.shortExact_idealShortComplex (J ^ 1)
  have := AlgebraicGeometry.pullback_preservesFiniteLimits_of_isOpenImmersion (offCentre J).ι
  have hS' : (S.map (Scheme.Modules.pullback (offCentre J).ι)).ShortExact :=
    hS.map_of_exact _
  have h3 : Limits.IsZero (S.map (Scheme.Modules.pullback (offCentre J).ι)).X₃ := by
    refine isZero_pullback_pushforward_of_disjoint (J ^ 1).subschemeι _ _ ?_
    rw [Scheme.IdealSheafData.range_subschemeι, pow_one]
    exact (Set.disjoint_compl_right_iff_subset.mpr le_rfl)
  have hiso : IsIso (S.map (Scheme.Modules.pullback (offCentre J).ι)).f := hS'.isIso_f_iff.mpr h3
  refine Stacks.InvertibleLocallyFree.isInvertible_of_iso_unit _ _ ?_
  exact (Iso.refl _ : (Scheme.Modules.pullback (offCentre J).ι).obj (idealModule J) ≅
      (S.map (Scheme.Modules.pullback (offCentre J).ι)).X₁) ≪≫
    @asIso _ _ _ _ (S.map (Scheme.Modules.pullback (offCentre J).ι)).f hiso ≪≫
    ((Scheme.Modules.restrictFunctorIsoPullback (offCentre J).ι).app
      (SheafOfModules.unit X.ringCatSheaf)).symm ≪≫ Scheme.Modules.restrictUnitIso _

/-- `𝐏(𝒥) ⟶ X` is an isomorphism away from the support of `𝒥`. -/
private theorem isIso_idealBundleToBase_restrict_compl_support {X : Scheme.{u}}
    (J : X.IdealSheafData) : IsIso (idealBundleToBase J ∣_ J.support.compl) := by
  have h := isIso_projectiveBundleToBase_restrict_of_isInvertible (idealModule J) (offCentre J)
    (isInvertible_pullback_idealModule J)
  have e : idealBundleToBase J = (Stacks.RelativeProj.bundlePresentationIso (idealModule J)).hom ≫
      Stacks.RelativeProj.projectiveBundleToBase X (idealModule J) :=
    (Stacks.RelativeProj.bundlePresentationIso_hom_comp_toBase _).symm
  rw [e]
  exact isIso_restrict_iso_comp _ _ _ h

/-! ### Assembly -/

/-- **Hartshorne II.7.17.** A projective birational morphism `f : X' ⟶ X` from an integral scheme
onto a quasi-projective variety over a field is the blowup of `X` in a nonzero ideal sheaf `J`
of finite type, via an isomorphism `X' ≅ blowUp J` over `X`.

The closed immersion `X' ⟶ 𝐏(ℱ)` of `f` is moved into `𝐏(𝒥)` for an ideal sheaf `𝒥` with
`ℱ ≅ 𝒥 ⊗ ℳ`; the blowup of `𝒥` is a second integral closed subscheme of `𝐏(𝒥)`, and the two
agree over the open where `f` is an isomorphism and `𝒥` is trivial, so they coincide. -/
@[mmp "lem_mmp_foundation_projective_birational_over_qp_is_blowup"]
public theorem exists_blowUp_iso_of_isProjective_of_isBirational {k : Type u} [Field k]
    {X X' : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsQuasiProjectiveVariety k sX] [IsIntegral X']
    (f : X' ⟶ X) (hf : IsProjective f) (hb : IsBirational f) :
    ∃ (J : X.IdealSheafData) (_ : J ≠ ⊥) (_ : J.IsFiniteType) (e : X' ≅ blowUp J),
      e.hom ≫ blowUpToBase J = f := by
  -- Step 1: `f` is an isomorphism over a dense open `V` (Stacks 0BAJ).
  obtain ⟨V, hVd, hVi⟩ := exists_dense_open_isIso_of_isBirational f hf hb
  -- Step 2: the two closed embeddings into `𝐏(𝒥)`.
  obtain ⟨J, hJ, i₁, hi₁, hi₁f⟩ := exists_closedImmersion_idealBundle sX f hf hb
  have hft : J.IsFiniteType := by
    have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    exact AlgebraicGeometry.TwoStepTower.isFiniteType_of_isLocallyNoetherian J
  obtain ⟨i₂, hi₂, hi₂f⟩ := exists_closedImmersion_blowUp_idealBundle J hft
  have : IsIntegral (blowUp J) := isIntegral_blowUp J hJ
  refine ⟨J, hJ, hft, ?_⟩
  -- Step 3: both embeddings are bijective over `W = V ∖ V(𝒥)`, which contains the generic point.
  have := isIso_idealBundleToBase_restrict_compl_support J
  obtain ⟨-, hinj⟩ := surj_inj_of_isIso_restrict (idealBundleToBase J) J.support.compl
  obtain ⟨hsurjB, -⟩ := surj_inj_of_isIso_restrict (blowUpToBase J) J.support.compl
  obtain ⟨hsurjF, -⟩ := surj_inj_of_isIso_restrict f V
  -- the open `W` over which everything is an isomorphism
  let W : X.Opens := V ⊓ J.support.compl
  have hη : genericPoint X ∈ W :=
    ⟨genericPoint_mem_of_nonempty V hVd.nonempty.to_subtype, genericPoint_notMem_supportSet J hJ⟩
  obtain ⟨e, he⟩ := exists_iso_of_closedImmersion_over (idealBundleToBase J) i₁ i₂ W ⟨_, hη⟩
    (fun z z' h hz => hinj z z' h hz.2)
    (fun x hx => (hsurjF x hx.1).imp fun a ha => by rwa [← Scheme.Hom.comp_apply, hi₁f])
    (fun x hx => (hsurjB x hx.2).imp fun b hb' => by rwa [← Scheme.Hom.comp_apply, hi₂f])
  exact ⟨e, by rw [← hi₁f, ← he, Category.assoc, hi₂f]⟩

end MMP
