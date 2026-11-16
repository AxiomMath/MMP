module

public import MMP.AlgebraicGeometry.DeRham.Logarithmic.RelativeLogForms
public import StacksFrontier.CategoryTheory.Sites.Modules.GrothendieckAbelian
public import StacksFrontier.Topology.Sheaves.Cohomology.FilteredComplexSpectralSequence.StupidTruncationSpectralSequence

/-!
# The relative logarithmic de Rham complex and its Hodge data

Let `f : X ⟶ S` be smooth of relative dimension `n` and let `D` be a relative simple normal
crossing divisor on `X` (`MMP.Mori.Divisor.IsRelativeSNC`), with complement `U = X ∖ D` and
inclusion `j : U ⟶ X`. The relative de Rham complex `Ω^•_{U/S}` pushes forward to a complex
`j_*Ω^•_{U/S}` of sheaves of `f⁻¹𝒪_S`-modules on `X`. The relative logarithmic de Rham complex
`Ω^•_{X/S}(log D)` is its subcomplex `Ω^0_{X/S} → Ω^1_{X/S}(log D) → Ω^2_{X/S}(log D) → ⋯`
whose degree-`p` term is the sheaf `Ω^p_{X/S}(log D)` of `MMP.Mori.Divisor.relativeLogForms`,
with the relative de Rham differential, and `Ω^•_{X/S}(log D)(-D)` is its subcomplex of
reduced-boundary twists, with terms `Ω^p_{X/S}(log D)(-D)`.

The Hodge filtration of `Ω^•_{X/S}(log D)` is the stupid filtration `σ_{≥ i}`. The logarithmic
de Rham hypercohomology is `ℍ^k(X, Ω^•_{X/S}(log D))`, with or without the twist. For
`S = Spec k` and `X` proper, the Hodge numbers are `h^{i,q} = dim_k H^q(X, Ω^i_X(log D))` and
`dim_k H^q(X, Ω^i_X(log D)(-D))`. The Hodge-to-de Rham spectral sequence is the spectral sequence
of the stupid filtration, `E_1^{i,q} = H^q(X, Ω^i) ⇒ ℍ^{i+q}`.

## Main definitions

* `MMP.Mori.Divisor.relativeLogDeRhamComplex`: the complex `I · Ω^•_{X/S}(log D)` of sheaves of
  `f⁻¹𝒪_S`-modules on `X`, for an ideal sheaf `I` of `X`. The case `I = ⊤` is
  `Ω^•_{X/S}(log D)` and the case `I = D.suppIdeal` is `Ω^•_{X/S}(log D)(-D)`.
* `MMP.Mori.Divisor.relativeLogDeRhamTwistSubcomplex`: `Ω^•_{X/S}(log D)(-D)` as a subobject of
  `Ω^•_{X/S}(log D)` in the category of complexes.
* `MMP.Mori.Divisor.relativeLogHodgeFiltration`: the Hodge filtration, the stupid filtration
  `σ_{≥ i}` of the complex.
* `MMP.Mori.Divisor.relativeLogDeRhamHypercohomology`: `ℍ^k(X, I · Ω^•_{X/S}(log D))`.
* `MMP.Mori.Divisor.relativeLogHodgeNumber`: for `S = Spec k` and `X` proper,
  `dim_k H^q(X, I · Ω^i_X(log D))`.
* `MMP.Mori.Divisor.relativeLogHodgeToDeRhamSpectralSequence`: the spectral sequence of the
  stupid filtration, with `E_1^{i,q} = H^q(X, I · Ω^i_{X/S}(log D))`, abutting to
  `ℍ^{i+q}(X, I · Ω^•_{X/S}(log D))`.

## Main results

* `MMP.Mori.Divisor.relativeLogHodgeToDeRhamSpectralSequence_spec`: the first page, the
  boundedness and the abutment of the Hodge-to-de Rham spectral sequence.

## Implementation notes

The complex is the smallest family `(N_p)_p` of sub-`f⁻¹𝒪_S`-modules `N_p ⊆ j_*Ω^p_{U/S}` such
that every section of `relativeLogForms n f D hD I p` lies in `N_p` and the de Rham differential
maps `N_p` into `N_{p+1}`. The relative logarithmic forms are already a subsheaf of
`f⁻¹𝒪_S`-modules, and for `I = ⊤` and `I = D.suppIdeal` the differential preserves them
(`MMP.Mori.Divisor.relativeLogForms_free_and_deRhamD_mem`), so in these two cases `N_p` is
`Ω^p_{X/S}(log D)`, respectively `Ω^p_{X/S}(log D)(-D)`. Since the twisted forms are among the
untwisted ones, the twisted complex is a subcomplex of the untwisted one.

The direct image `j_*Ω^•_{U/S}` is taken over the base rings: `f⁻¹𝒪_S` acts on the forms on
`j⁻¹W` through the comparison map `f⁻¹𝒪_S ⟶ j_*((j ≫ f)⁻¹𝒪_S)`, adjoint under `f⁻¹ ⊣ f_*` to
the unit `𝒪_S ⟶ (j ≫ f)_*(j ≫ f)⁻¹𝒪_S`.

The complex is indexed by `ℕ`, like `AlgebraicGeometry.Scheme.Hom.deRhamComplex`; the Hodge
data are taken on its extension by zero to `ℤ`. The cohomology is that of sheaves of
`f⁻¹𝒪_S`-modules, computed by the derived global sections functor
`AlgebraicGeometry.SheafOfModules.derivedSectionsBase` of the ringed space
`AlgebraicGeometry.SheafOfModules.baseRingedSpace (f⁻¹𝒪_S)`, with values in modules over
`Γ(X, f⁻¹𝒪_S)`; over `S = Spec k` these are read over `k` along `k = Γ(S, 𝒪_S) ⟶ Γ(X, f⁻¹𝒪_S)`.
The same derived functor is used for the hypercohomology, the Hodge numbers and the spectral
sequence, so that the spectral sequence abuts to the hypercohomology defined here. The spectral
sequence of a filtered complex is built from a choice of filtered injective replacement, and is
well defined up to isomorphism from its first page on; it is the one of
`Stacks.Cohomology.FilteredComplex.exists_spectralSequence_of_boundedBelowFilteredComplex`
for the stupid filtration.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori]
* [Stacks Project, Tag 0FLK](https://stacks.math.columbia.edu/tag/0FLK)
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
  ComplexShape

universe u

namespace MMP.Mori.Divisor

attribute [local instance] HasDerivedCategory.standard

/-! ### The complex and its twist -/

/-- The complex `j_*Ω^•_{U/S}` of sheaves of `f⁻¹𝒪_S`-modules on `X`, for `U = X ∖ D` and
`j : U ⟶ X` the inclusion: the pushforward of the relative de Rham complex of `U` over `S`, with
`f⁻¹𝒪_S` acting through the comparison `f⁻¹𝒪_S ⟶ j_*((j ≫ f)⁻¹𝒪_S)`. -/
@[expose] public noncomputable def complementDeRhamPushforward {X S : Scheme.{u}} (f : X ⟶ S)
    (D : Divisor X) :
    CochainComplex (SheafOfModules.{u}
      (SheafOfModules.underlyingRingSheaf
        ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf))) ℕ :=
  let U : X.Opens := D.supp.compl
  -- the comparison of base rings `f⁻¹𝒪_S ⟶ j_*((j ≫ f)⁻¹𝒪_S)`, adjoint to the unit of `j ≫ f`
  let φ : (TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} U.ι.base).obj
        ((TopCat.Sheaf.pullback CommRingCat.{u} (U.ι ≫ f).base).obj S.sheaf) :=
    ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.base).homEquiv _ _).symm
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} (U.ι ≫ f).base).unit.app
        S.sheaf)
  -- `j_*`, from `(j ≫ f)⁻¹𝒪_S`-modules on `U` to `f⁻¹𝒪_S`-modules on `X`
  let jStar := SheafOfModules.pushforward.{u}
    (F := Opens.map U.ι.base) ((sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map φ)
  (jStar.mapHomologicalComplex (up ℕ)).obj (Scheme.Hom.deRhamComplex (U.ι ≫ f))

/-- The terms of `I · Ω^•_{X/S}(log D)`: the smallest family of sub-`f⁻¹𝒪_S`-modules
`N_p ⊆ j_*Ω^p_{U/S}` containing the sections of `relativeLogForms n f D hD I p` and mapped into
`N_{p+1}` by the de Rham differential. -/
@[expose] public noncomputable def relativeLogDeRhamTerms (n : ℕ) {X S : Scheme.{u}} (f : X ⟶ S)
    [SmoothOfRelativeDimension n f] (D : Divisor X) (hD : D.IsRelativeSNC n f)
    (I : X.IdealSheafData) : ∀ p : ℕ, ((complementDeRhamPushforward f D).X p).Submodule :=
  sInf {N |
    (∀ (p : ℕ) (W : X.Opens), ∀ ω ∈ relativeLogForms n f D hD I p W,
      ω ∈ (N p).obj (op W)) ∧
    ∀ (p : ℕ) (W : X.Opensᵒᵖ) (ω : ((complementDeRhamPushforward f D).X p).val.obj W),
      ω ∈ (N p).obj W →
        ((complementDeRhamPushforward f D).d p (p + 1)).val.app W ω ∈ (N (p + 1)).obj W}

/-- Membership in a pointwise infimum of a set of families of submodules of sheaves of modules. -/
private theorem mem_sInf_pi_obj_iff {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {ι : Type*} {M : ι → SheafOfModules.{u} R}
    (s : Set (∀ i, (M i).Submodule)) (q : ι) (W : Cᵒᵖ) (x : (M q).val.obj W) :
    x ∈ ((sInf s) q).obj W ↔ ∀ N ∈ s, x ∈ (N q).obj W := by
  constructor
  · intro hx N hN
    exact PresheafOfModules.Submodule.le_iff.mp
      (SheafOfModules.Submodule.le_iff.mp ((sInf_le hN : sInf s ≤ N) q)) W hx
  · intro hx
    rw [sInf_apply]
    change x ∈ (⨅ N : s, (N.1 q)).toSubmodule.obj W
    rw [SheafOfModules.Submodule.toSubmodule_iInf, iInf, PresheafOfModules.Submodule.sInf_obj]
    refine (Submodule.mem_iInf _).2 fun N' => (Submodule.mem_iInf _).2 ?_
    rintro ⟨N, rfl⟩
    exact hx N.1 N.2

/-- The de Rham differential maps the `p`-th term of `I · Ω^•_{X/S}(log D)` into the
`(p + 1)`-st. -/
public theorem relativeLogDeRhamTerms_d_mem (n : ℕ) {X S : Scheme.{u}} (f : X ⟶ S)
    [SmoothOfRelativeDimension n f] (D : Divisor X) (hD : D.IsRelativeSNC n f)
    (I : X.IdealSheafData) (p : ℕ) (W : X.Opensᵒᵖ)
    (ω : ((complementDeRhamPushforward f D).X p).val.obj W)
    (hω : ω ∈ (relativeLogDeRhamTerms n f D hD I p).obj W) :
    ((complementDeRhamPushforward f D).d p (p + 1)).val.app W ω ∈
      (relativeLogDeRhamTerms n f D hD I (p + 1)).obj W := by
  unfold relativeLogDeRhamTerms at hω ⊢
  rw [mem_sInf_pi_obj_iff] at hω ⊢
  intro M hM
  exact hM.2 p W ω (hω M hM)

/-- Every section of `relativeLogForms n f D hD I p` lies in the `p`-th term of
`I · Ω^•_{X/S}(log D)`. -/
public theorem mem_relativeLogDeRhamTerms_of_mem_relativeLogForms (n : ℕ) {X S : Scheme.{u}}
    (f : X ⟶ S) [SmoothOfRelativeDimension n f] (D : Divisor X) (hD : D.IsRelativeSNC n f)
    (I : X.IdealSheafData) (p : ℕ) (W : X.Opens)
    {ω : ((complementDeRhamPushforward f D).X p).val.obj (op W)}
    (hω : ω ∈ relativeLogForms n f D hD I p W) :
    ω ∈ (relativeLogDeRhamTerms n f D hD I p).obj (op W) := by
  unfold relativeLogDeRhamTerms
  rw [mem_sInf_pi_obj_iff]
  exact fun N hN => hN.1 p W ω hω

/-- `I · Ω^•_{X/S}(log D)` is contained in every family of submodules of `j_*Ω^•_{U/S}` that
contains the logarithmic forms and is stable under the de Rham differential. -/
public theorem relativeLogDeRhamTerms_le (n : ℕ) {X S : Scheme.{u}} (f : X ⟶ S)
    [SmoothOfRelativeDimension n f] (D : Divisor X) (hD : D.IsRelativeSNC n f)
    (I : X.IdealSheafData) {N : ∀ p : ℕ, ((complementDeRhamPushforward f D).X p).Submodule}
    (h₁ : ∀ (p : ℕ) (W : X.Opens), ∀ ω ∈ relativeLogForms n f D hD I p W, ω ∈ (N p).obj (op W))
    (h₂ : ∀ (p : ℕ) (W : X.Opensᵒᵖ) (ω : ((complementDeRhamPushforward f D).X p).val.obj W),
      ω ∈ (N p).obj W →
        ((complementDeRhamPushforward f D).d p (p + 1)).val.app W ω ∈ (N (p + 1)).obj W) :
    relativeLogDeRhamTerms n f D hD I ≤ N :=
  sInf_le ⟨h₁, h₂⟩

/-- The sections of `I · Ω^p_{X/S}(log D)` grow with the ideal sheaf `I`. -/
public theorem relativeLogForms_mono (n : ℕ) {X S : Scheme.{u}} (f : X ⟶ S)
    [SmoothOfRelativeDimension n f] (D : Divisor X) (hD : D.IsRelativeSNC n f)
    {I I' : X.IdealSheafData} (h : I ≤ I') (p : ℤ) (W : X.Opens) :
    relativeLogForms n f D hD I p W ⊆ relativeLogForms n f D hD I' p W := by
  intro ω hω x hx
  obtain ⟨W', hW', hxW', hmem⟩ := hω x hx
  refine ⟨W', hW', hxW', AddSubgroup.closure_mono ?_ hmem⟩
  rintro η ⟨g, hg, ζ, hζ, rfl⟩
  exact ⟨g, Scheme.IdealSheafData.le_def.mp h W' hg, ζ, hζ, rfl⟩

/-- The terms of `I · Ω^•_{X/S}(log D)` grow with the ideal sheaf `I`. -/
public theorem relativeLogDeRhamTerms_mono (n : ℕ) {X S : Scheme.{u}} (f : X ⟶ S)
    [SmoothOfRelativeDimension n f] (D : Divisor X) (hD : D.IsRelativeSNC n f)
    {I I' : X.IdealSheafData} (h : I ≤ I') :
    relativeLogDeRhamTerms n f D hD I ≤ relativeLogDeRhamTerms n f D hD I' :=
  sInf_le_sInf fun _ ⟨hN₁, hN₂⟩ =>
    ⟨fun p W ω hω => hN₁ p W ω (relativeLogForms_mono n f D hD h p W hω), hN₂⟩

/-- The differential `I · Ω^p_{X/S}(log D) ⟶ I · Ω^{p+1}_{X/S}(log D)`: the restriction of the
de Rham differential of `j_*Ω^•_{U/S}`. -/
@[expose] public noncomputable def relativeLogDeRhamDifferential (n : ℕ) {X S : Scheme.{u}}
    (f : X ⟶ S) [SmoothOfRelativeDimension n f] (D : Divisor X) (hD : D.IsRelativeSNC n f)
    (I : X.IdealSheafData) (p : ℕ) :
    (relativeLogDeRhamTerms n f D hD I p).toSheafOfModules ⟶
      (relativeLogDeRhamTerms n f D hD I (p + 1)).toSheafOfModules :=
  ⟨{app := fun W => ModuleCat.ofHom
        ((((complementDeRhamPushforward f D).d p (p + 1)).val.app W).hom.restrict
          (relativeLogDeRhamTerms_d_mem n f D hD I p W))
    naturality := by
      intro W W' g
      ext ω
      exact Subtype.ext (PresheafOfModules.naturality_apply
        ((complementDeRhamPushforward f D).d p (p + 1)).val g ω.1) }⟩

/-- The differential of `I · Ω^•_{X/S}(log D)` is the restriction of that of `j_*Ω^•_{U/S}`. -/
@[reassoc]
public theorem relativeLogDeRhamDifferential_comp_ι (n : ℕ) {X S : Scheme.{u}}
    (f : X ⟶ S) [SmoothOfRelativeDimension n f] (D : Divisor X) (hD : D.IsRelativeSNC n f)
    (I : X.IdealSheafData) (p : ℕ) :
    relativeLogDeRhamDifferential n f D hD I p ≫ (relativeLogDeRhamTerms n f D hD I (p + 1)).ι =
      (relativeLogDeRhamTerms n f D hD I p).ι ≫ (complementDeRhamPushforward f D).d p (p + 1) :=
  rfl

/-- **The relative logarithmic de Rham complex** `I · Ω^•_{X/S}(log D)` of a relative simple normal
crossing divisor `D` on `X`, for `f : X ⟶ S` smooth of relative dimension `n` and an ideal sheaf
`I` of `X`. It is the subcomplex of `j_*Ω^•_{U/S}` (`U = X ∖ D`, `j : U ⟶ X`) of sheaves of
`f⁻¹𝒪_S`-modules on `X` generated by the sections of `MMP.Mori.Divisor.relativeLogForms`, with the
relative de Rham differential.

`relativeLogDeRhamComplex n f D hD ⊤` is `Ω^•_{X/S}(log D)` and
`relativeLogDeRhamComplex n f D hD D.suppIdeal` is `Ω^•_{X/S}(log D)(-D)`. -/
@[expose, mmp "def_mmp_relative_log_de_rham_complex"]
public noncomputable def relativeLogDeRhamComplex (n : ℕ) {X S : Scheme.{u}} (f : X ⟶ S)
    [SmoothOfRelativeDimension n f] (D : Divisor X) (hD : D.IsRelativeSNC n f)
    (I : X.IdealSheafData) :
    CochainComplex (SheafOfModules.{u}
      (SheafOfModules.underlyingRingSheaf
        ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf))) ℕ :=
  CochainComplex.of (fun p => (relativeLogDeRhamTerms n f D hD I p).toSheafOfModules)
    (relativeLogDeRhamDifferential n f D hD I)
    (fun p => by
      rw [← cancel_mono (relativeLogDeRhamTerms n f D hD I (p + 1 + 1)).ι, Category.assoc,
        relativeLogDeRhamDifferential_comp_ι, ← Category.assoc,
        relativeLogDeRhamDifferential_comp_ι, Category.assoc,
        (complementDeRhamPushforward f D).d_comp_d, comp_zero, zero_comp])

/-- The `p`-th term of `I · Ω^•_{X/S}(log D)` is `relativeLogDeRhamTerms`. -/
@[simp]
public theorem relativeLogDeRhamComplex_X (n : ℕ) {X S : Scheme.{u}} (f : X ⟶ S)
    [SmoothOfRelativeDimension n f] (D : Divisor X) (hD : D.IsRelativeSNC n f)
    (I : X.IdealSheafData) (p : ℕ) :
    (relativeLogDeRhamComplex n f D hD I).X p =
      (relativeLogDeRhamTerms n f D hD I p).toSheafOfModules :=
  rfl

/-- The `p`-th differential of `I · Ω^•_{X/S}(log D)` is `relativeLogDeRhamDifferential`. -/
@[simp]
public theorem relativeLogDeRhamComplex_d (n : ℕ) {X S : Scheme.{u}} (f : X ⟶ S)
    [SmoothOfRelativeDimension n f] (D : Divisor X) (hD : D.IsRelativeSNC n f)
    (I : X.IdealSheafData) (p : ℕ) :
    (relativeLogDeRhamComplex n f D hD I).d p (p + 1) =
      relativeLogDeRhamDifferential n f D hD I p := by
  unfold relativeLogDeRhamComplex
  exact CochainComplex.of_d (fun p => (relativeLogDeRhamTerms n f D hD I p).toSheafOfModules)
    (relativeLogDeRhamDifferential n f D hD I) p

/-- The inclusion of the `p`-th term of `I · Ω^•_{X/S}(log D)` into that of
`I' · Ω^•_{X/S}(log D)`, for ideal sheaves `I ≤ I'`. -/
@[expose] public noncomputable def relativeLogDeRhamTermsMapOfLE (n : ℕ) {X S : Scheme.{u}}
    (f : X ⟶ S) [SmoothOfRelativeDimension n f] (D : Divisor X) (hD : D.IsRelativeSNC n f)
    {I I' : X.IdealSheafData} (h : I ≤ I') (p : ℕ) :
    (relativeLogDeRhamTerms n f D hD I p).toSheafOfModules ⟶
      (relativeLogDeRhamTerms n f D hD I' p).toSheafOfModules :=
  ⟨PresheafOfModules.Submodule.homOfLE
    (SheafOfModules.Submodule.le_iff.mp (relativeLogDeRhamTerms_mono n f D hD h p))⟩

/-- The inclusion of terms is compatible with the inclusions into `j_*Ω^p_{U/S}`. -/
@[reassoc]
public theorem relativeLogDeRhamTermsMapOfLE_comp_ι (n : ℕ) {X S : Scheme.{u}}
    (f : X ⟶ S) [SmoothOfRelativeDimension n f] (D : Divisor X) (hD : D.IsRelativeSNC n f)
    {I I' : X.IdealSheafData} (h : I ≤ I') (p : ℕ) :
    relativeLogDeRhamTermsMapOfLE n f D hD h p ≫ (relativeLogDeRhamTerms n f D hD I' p).ι =
      (relativeLogDeRhamTerms n f D hD I p).ι := by
  apply (SheafOfModules.forget _).map_injective
  rw [Functor.map_comp]
  exact PresheafOfModules.Submodule.homOfLE_ι _

/-- The inclusion `I · Ω^•_{X/S}(log D) ⟶ I' · Ω^•_{X/S}(log D)` for ideal sheaves `I ≤ I'`. -/
public noncomputable def relativeLogDeRhamComplexMapOfLE (n : ℕ) {X S : Scheme.{u}}
    (f : X ⟶ S) [SmoothOfRelativeDimension n f] (D : Divisor X) (hD : D.IsRelativeSNC n f)
    {I I' : X.IdealSheafData} (h : I ≤ I') :
    relativeLogDeRhamComplex n f D hD I ⟶ relativeLogDeRhamComplex n f D hD I' :=
  CochainComplex.ofHom (relativeLogDeRhamTermsMapOfLE n f D hD h)
    (fun p => by
      rw [relativeLogDeRhamComplex_d, relativeLogDeRhamComplex_d]
      change relativeLogDeRhamTermsMapOfLE n f D hD h p ≫
          relativeLogDeRhamDifferential n f D hD I' p =
        relativeLogDeRhamDifferential n f D hD I p ≫
          relativeLogDeRhamTermsMapOfLE n f D hD h (p + 1)
      refine (cancel_mono (relativeLogDeRhamTerms n f D hD I' (p + 1)).ι).1 ?_
      rw [Category.assoc,
        relativeLogDeRhamDifferential_comp_ι, ← Category.assoc,
        relativeLogDeRhamTermsMapOfLE_comp_ι, Category.assoc,
        relativeLogDeRhamTermsMapOfLE_comp_ι, relativeLogDeRhamDifferential_comp_ι])

/-- The inclusion `I · Ω^•_{X/S}(log D) ⟶ I' · Ω^•_{X/S}(log D)` is a monomorphism. -/
public instance mono_relativeLogDeRhamComplexMapOfLE (n : ℕ) {X S : Scheme.{u}}
    (f : X ⟶ S) [SmoothOfRelativeDimension n f] (D : Divisor X) (hD : D.IsRelativeSNC n f)
    {I I' : X.IdealSheafData} (h : I ≤ I') :
    Mono (relativeLogDeRhamComplexMapOfLE n f D hD h) := by
  refine HomologicalComplex.mono_of_mono_f _ fun p => ?_
  change Mono (relativeLogDeRhamTermsMapOfLE n f D hD h p)
  exact mono_of_mono_fac (relativeLogDeRhamTermsMapOfLE_comp_ι n f D hD h p)

/-- The `p`-th component of the inclusion `I · Ω^• ⟶ I' · Ω^•` is the inclusion of terms. -/
@[simp]
public theorem relativeLogDeRhamComplexMapOfLE_f (n : ℕ) {X S : Scheme.{u}}
    (f : X ⟶ S) [SmoothOfRelativeDimension n f] (D : Divisor X) (hD : D.IsRelativeSNC n f)
    {I I' : X.IdealSheafData} (h : I ≤ I') (p : ℕ) :
    (relativeLogDeRhamComplexMapOfLE n f D hD h).f p =
      relativeLogDeRhamTermsMapOfLE n f D hD h p := by
  unfold relativeLogDeRhamComplexMapOfLE
  rfl

/-- **The subcomplex `Ω^•_{X/S}(log D)(-D)` of reduced-boundary twists** of
`Ω^•_{X/S}(log D)`: the subobject of `relativeLogDeRhamComplex n f D hD ⊤` given by the
inclusion of `relativeLogDeRhamComplex n f D hD D.suppIdeal`. -/
@[mmp "def_mmp_relative_log_de_rham_complex"]
public noncomputable def relativeLogDeRhamTwistSubcomplex (n : ℕ) {X S : Scheme.{u}}
    (f : X ⟶ S) [SmoothOfRelativeDimension n f] (D : Divisor X) (hD : D.IsRelativeSNC n f) :
    Subobject (relativeLogDeRhamComplex n f D hD ⊤) :=
  Subobject.mk (relativeLogDeRhamComplexMapOfLE n f D hD (le_top : D.suppIdeal ≤ ⊤))

/-! ### The Hodge filtration -/

/-- **The Hodge filtration** of `I · Ω^•_{X/S}(log D)`: the stupid filtration, whose `i`-th step
is the brutal truncation `σ_{≥ i}` of the complex, extended by zero to negative degrees. -/
@[expose, mmp "def_mmp_relative_log_de_rham_complex"]
public noncomputable def relativeLogHodgeFiltration (n : ℕ) {X S : Scheme.{u}} (f : X ⟶ S)
    [SmoothOfRelativeDimension n f] (D : Divisor X) (hD : D.IsRelativeSNC n f)
    (I : X.IdealSheafData) :
    CochainComplex.Filtered (SheafOfModules.{u}
      (SheafOfModules.underlyingRingSheaf
        ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf))) :=
  CochainComplex.stupidTruncationFiltration
    ((relativeLogDeRhamComplex n f D hD I).extend embeddingUpNat)

/-! ### Logarithmic de Rham hypercohomology -/

/-- **The logarithmic de Rham hypercohomology** `ℍ^k(X, I · Ω^•_{X/S}(log D))`: the `k`-th
cohomology of the derived global sections of the complex of sheaves of `f⁻¹𝒪_S`-modules
`I · Ω^•_{X/S}(log D)`, a module over `Γ(X, f⁻¹𝒪_S)`. For `I = ⊤` it is
`ℍ^k(X, Ω^•_{X/S}(log D))` and for `I = D.suppIdeal` it is `ℍ^k(X, Ω^•_{X/S}(log D)(-D))`. -/
@[expose, mmp "def_mmp_relative_log_de_rham_complex"]
public noncomputable def relativeLogDeRhamHypercohomology (n : ℕ) {X S : Scheme.{u}}
    (f : X ⟶ S) [SmoothOfRelativeDimension n f] (D : Divisor X) (hD : D.IsRelativeSNC n f)
    (I : X.IdealSheafData) (k : ℤ) :
    ModuleCat.{u} ((SheafOfModules.underlyingRingSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf)).obj.obj (op ⊤)) :=
  (DerivedCategory.homologyFunctor _ k).obj
    ((SheafOfModules.derivedSectionsBase (X := X.toRingedSpace)
      ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf)).obj
      (DerivedCategory.Q.obj ((relativeLogDeRhamComplex n f D hD I).extend embeddingUpNat)))

/-! ### Hodge numbers -/

/-- The ring map `k = Γ(Spec k, 𝒪) ⟶ Γ(X, f⁻¹𝒪_{Spec k})`, through which the cohomology of
sheaves of `f⁻¹𝒪_{Spec k}`-modules is read over `k`. -/
@[expose] public noncomputable def baseFieldToInverseImageSections (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) :
    k →+* (SheafOfModules.underlyingRingSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj
        (Spec (CommRingCat.of k)).sheaf)).obj.obj (op ⊤) :=
  (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.base).unit.app
      (Spec (CommRingCat.of k)).sheaf).hom.app (op ⊤)).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom

/-- **The logarithmic Hodge numbers** of a proper `X` smooth over a field `k`: for `S = Spec k`,
`dim_k H^q(X, I · Ω^i_X(log D))`. For `I = ⊤` this is `h^{i,q} = dim_k H^q(X, Ω^i_X(log D))` and
for `I = D.suppIdeal` it is `dim_k H^q(X, Ω^i_X(log D)(-D))`. The cohomology is that of the
`i`-th term of `relativeLogDeRhamComplex` as a sheaf of `f⁻¹𝒪_S`-modules, read over `k`. -/
@[expose, mmp "def_mmp_relative_log_de_rham_complex"]
public noncomputable def relativeLogHodgeNumber (k : Type u) [Field k] (n : ℕ) {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [SmoothOfRelativeDimension n f]
    (D : Divisor X) (hD : D.IsRelativeSNC n f) (I : X.IdealSheafData) (i q : ℕ) : ℕ :=
  Module.finrank k ((ModuleCat.restrictScalars (baseFieldToInverseImageSections k f)).obj
    ((DerivedCategory.homologyFunctor _ (q : ℤ)).obj
      ((SheafOfModules.derivedSectionsBase (X := X.toRingedSpace)
        ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj
          (Spec (CommRingCat.of k)).sheaf)).obj
        ((DerivedCategory.singleFunctor _ 0).obj ((relativeLogDeRhamComplex n f D hD I).X i)))))

/-! ### The Hodge-to-de Rham spectral sequence -/

/-- **The Hodge-to-de Rham spectral sequence exists**: the stupid filtration of
`I · Ω^•_{X/S}(log D)` has a spectral sequence, computed from a filtered injective replacement,
with `E_1^{i,q} = H^q(X, I · Ω^i_{X/S}(log D))`, which is bounded and abuts to
`ℍ^{i+q}(X, I · Ω^•_{X/S}(log D))`. The cohomology on both sides is taken with the derived
global sections functor `AlgebraicGeometry.SheafOfModules.derivedSectionsBase` of sheaves of
`f⁻¹𝒪_S`-modules. -/
public theorem exists_relativeLogHodgeToDeRhamSpectralSequence (n : ℕ) {X S : Scheme.{u}}
    (f : X ⟶ S) [SmoothOfRelativeDimension n f] (D : Divisor X) (hD : D.IsRelativeSNC n f)
    (I : X.IdealSheafData) :
    ∃ E : Stacks.Cohomology.FilteredComplex.StupidTruncationSpectralSequence
        (SheafOfModules.baseRingedSpace (X := X.toRingedSpace)
          ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf))
        ((relativeLogDeRhamComplex n f D hD I).extend embeddingUpNat),
      (∀ i q : ℤ, Nonempty ((E.spectralSequence.page 1 le_rfl).X (i, q) ≅
        (DerivedCategory.homologyFunctor (ModuleCat.{u}
            ((SheafOfModules.underlyingRingSheaf
              ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf)).obj.obj (op ⊤))) q).obj
          ((SheafOfModules.derivedSectionsBase (X := X.toRingedSpace)
            ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf)).obj
            ((DerivedCategory.singleFunctor _ 0).obj
              (((relativeLogDeRhamComplex n f D hD I).extend embeddingUpNat).X i))))) ∧
      IsBounded E.spectralSequence ∧
      SpectralSequence.AbutsTo E.spectralSequence
        (relativeLogDeRhamHypercohomology n f D hD I) := by
  let A := (TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf
  let Y := SheafOfModules.baseRingedSpace (X := X.toRingedSpace) A
  let K := (relativeLogDeRhamComplex n f D hD I).extend embeddingUpNat
  have hK : (CochainComplex.stupidTruncationFiltration K).X.IsStrictlyGE 0 := by
    change CochainComplex.IsStrictlyGE K 0
    infer_instance
  obtain ⟨J, i, -, -, -, hgr, hstep, hhom, -, hfirst, hbdd, F, hF, -, hFfin, hinf, hinfIso⟩ :=
    Stacks.Cohomology.FilteredComplex.exists_spectralSequence_of_boundedBelowFilteredComplex
      Y (SheafOfModules.derivedSectionsBase A)
      (Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpenUnit Y ⊤) inferInstance
      (CochainComplex.stupidTruncationFiltration K) 0 hK
      (CochainComplex.stupidTruncationFiltration_isDegreewiseFinite K)
  have hShift (p q : ℤ) : Nonempty
      (((Stacks.Cohomology.FilteredComplex.globalSectionsSpectralSequence Y J).page 1
          (by omega)).X (p, q) ≅
        (DerivedCategory.homologyFunctor
            (ModuleCat.{u} ((SheafOfModules.underlyingRingSheaf A).obj.obj (op ⊤))) (p + q)).obj
          ((SheafOfModules.derivedSectionsBase A).obj
            (((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (SheafOfModules.underlyingRingSheaf A)) 0).obj
                (K.X p))⟦(-p : ℤ)⟧))) := by
    obtain ⟨e⟩ := hfirst p q
    exact ⟨e ≪≫ Stacks.Cohomology.FilteredComplex.stupidGradedPieceHypercohomologyIso
      Y (SheafOfModules.derivedSectionsBase A) K p q⟩
  have hE₁ (p q : ℤ) : Nonempty
      (((Stacks.Cohomology.FilteredComplex.globalSectionsSpectralSequence Y J).page 1
          (by omega)).X (p, q) ≅
        (DerivedCategory.homologyFunctor
            (ModuleCat.{u} ((SheafOfModules.underlyingRingSheaf A).obj.obj (op ⊤))) q).obj
          ((SheafOfModules.derivedSectionsBase A).obj
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (SheafOfModules.underlyingRingSheaf A)) 0).obj (K.X p)))) := by
    obtain ⟨e⟩ := hShift p q
    exact ⟨e ≪≫ Stacks.Cohomology.FilteredComplex.shiftHypercohomologyIso Y
      (SheafOfModules.derivedSectionsBase A)
      (Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpenUnit Y ⊤) inferInstance
      (K.X p) p q⟩
  refine ⟨{ RΓ := SheafOfModules.derivedSectionsBase A
            α := Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpenUnit Y ⊤
            isRightDerived := inferInstance
            replacement := J
            replacementMap := i
            replacementMap_quasiIso := hhom
            replacementMap_step_quasiIso := hstep
            replacementMap_gr_quasiIso := hgr
            e₁IsoShift := hShift
            e₁Iso := hE₁ }, hE₁, hbdd, ?_⟩
  exact SpectralSequence.AbutsTo.shiftStart
    (E := Stacks.Cohomology.FilteredComplex.globalSectionsSpectralSequence Y J)
    ⟨hinf, F, hF, hFfin, hinfIso⟩ (by omega)

/-- **The Hodge-to-de Rham spectral sequence** of `I · Ω^•_{X/S}(log D)`: the spectral sequence
of its stupid filtration `σ_{≥ i}` (definitionally `relativeLogHodgeFiltration`), built from a
filtered injective replacement of that filtration
(`Stacks.Cohomology.FilteredComplex.StupidTruncationSpectralSequence`). Its spectral sequence
(`.spectralSequence`) has `E_1^{i,q} = H^q(X, I · Ω^i_{X/S}(log D))` and abuts to
`ℍ^{i+q}(X, I · Ω^•_{X/S}(log D))`
(`MMP.Mori.Divisor.relativeLogHodgeToDeRhamSpectralSequence_spec`). The spectral sequence of a
filtered complex depends on the replacement only up to isomorphism; one is chosen. -/
@[mmp "def_mmp_relative_log_de_rham_complex"]
public noncomputable def relativeLogHodgeToDeRhamSpectralSequence (n : ℕ) {X S : Scheme.{u}}
    (f : X ⟶ S) [SmoothOfRelativeDimension n f] (D : Divisor X) (hD : D.IsRelativeSNC n f)
    (I : X.IdealSheafData) :
    Stacks.Cohomology.FilteredComplex.StupidTruncationSpectralSequence
      (SheafOfModules.baseRingedSpace (X := X.toRingedSpace)
        ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf))
      ((relativeLogDeRhamComplex n f D hD I).extend embeddingUpNat) :=
  Classical.choose (exists_relativeLogHodgeToDeRhamSpectralSequence n f D hD I)

/-- **`E_1^{i,q} = H^q(X, I · Ω^i_{X/S}(log D)) ⇒ ℍ^{i+q}(X, I · Ω^•_{X/S}(log D))`**: the first
page, the boundedness and the abutment of the Hodge-to-de Rham spectral sequence. -/
@[mmp "def_mmp_relative_log_de_rham_complex"]
public theorem relativeLogHodgeToDeRhamSpectralSequence_spec (n : ℕ) {X S : Scheme.{u}}
    (f : X ⟶ S) [SmoothOfRelativeDimension n f] (D : Divisor X) (hD : D.IsRelativeSNC n f)
    (I : X.IdealSheafData) :
    (∀ i q : ℤ, Nonempty
      (((relativeLogHodgeToDeRhamSpectralSequence n f D hD I).spectralSequence.page 1 le_rfl).X
          (i, q) ≅
        (DerivedCategory.homologyFunctor (ModuleCat.{u}
            ((SheafOfModules.underlyingRingSheaf
              ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf)).obj.obj (op ⊤))) q).obj
          ((SheafOfModules.derivedSectionsBase (X := X.toRingedSpace)
            ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf)).obj
            ((DerivedCategory.singleFunctor _ 0).obj
              (((relativeLogDeRhamComplex n f D hD I).extend embeddingUpNat).X i))))) ∧
      IsBounded (relativeLogHodgeToDeRhamSpectralSequence n f D hD I).spectralSequence ∧
      SpectralSequence.AbutsTo
        (relativeLogHodgeToDeRhamSpectralSequence n f D hD I).spectralSequence
        (relativeLogDeRhamHypercohomology n f D hD I) :=
  Classical.choose_spec (exists_relativeLogHodgeToDeRhamSpectralSequence n f D hD I)

end MMP.Mori.Divisor
