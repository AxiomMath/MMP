module

public import StacksFrontier.AlgebraicGeometry.CechSiteChange.Resolution
public import StacksFrontier.Algebra.Homology.TotalComplexQuasiIso
public import StacksFrontier.Algebra.Homology.TotalSingleRow

/-!
# Morphisms into the derived category glued from local maps

Let `V` be a scheme, `𝒰 = (U α)` an open cover of `V`, `K` a bounded below cochain complex of
`𝒪_V`-modules and `M` an `𝒪_V`-module. Suppose given, for an integer `n`, morphisms
`f α : M|_{U α} → K^{n+1}|_{U α}` with `d ∘ f α = 0`, homotopies
`h α β : M|_{U α ∩ U β} → K^n|_{U α ∩ U β}` with `f β - f α = d ∘ h α β`, satisfying the cocycle
condition `h α β + h β γ = h α γ` on triple intersections. These data glue to a morphism
`M[-(n+1)] ⟶ K` in the derived category `D(V)`, whose effect on cohomology sheaves is, on every
open `W ⊆ U α`, `s ↦ [f α s]`.

The construction is the classical one. Let `Č(𝒰, K)` be the double complex whose term of bidegree
`(p, q)` is the sheafified Čech cochains `Č^q(𝒰, K^p) = ∏ (j_{α₀⋯α_q})_* (j_{α₀⋯α_q})^* K^p`. Its
columns are the Čech resolutions of the terms of `K`, so the augmentation `K ⟶ Tot Č(𝒰, K)` is a
quasi-isomorphism ([Stacks, Tag 02FU] columnwise and [Stacks, Tag 0133]). The pair `(f, h)` is a
cocycle of total degree `n + 1` of `Hom(M, Tot Č(𝒰, K))`, that is, a morphism of complexes
`M[-(n+1)] ⟶ Tot Č(𝒰, K)`; composing with the inverse of the quasi-isomorphism in `D(V)` gives the
morphism.

## Main definitions

* `MMP.DeRham.cechBicomplex`, `MMP.DeRham.cechTotal`: the Čech double complex `Č(𝒰, K)` and its
  total complex.
* `MMP.DeRham.toCechTotal`: the augmentation `K ⟶ Tot Č(𝒰, K)`.
* `MMP.DeRham.CechGluingData`: local maps into `K^{n+1}` glued up to a coherent homotopy.
* `MMP.DeRham.CechGluingData.cechMap`: the morphism of complexes `M[-(n+1)] ⟶ Tot Č(𝒰, K)`.
* `MMP.DeRham.CechGluingData.derivedMap`: the morphism `M[-(n+1)] ⟶ K` in `D(V)`.
* `MMP.DeRham.CechGluingData.homologyMap`: the induced morphism `M ⟶ ℋ^{n+1}(K)`.

## Main results

* `MMP.DeRham.quasiIso_toCechTotal`: `K ⟶ Tot Č(𝒰, K)` is a quasi-isomorphism for every open
  cover and every bounded below `K`.
* `MMP.DeRham.CechGluingData.homologyFunctor_map_derivedMap`: the cohomology in degree `n + 1` of
  `derivedMap` is `homologyMap`, up to the canonical identifications.
* `MMP.DeRham.CechGluingData.homologyMap_app_eq`: on an open `W ⊆ U α`, `homologyMap` sends a
  section `s` of `M` to the class of any cycle whose restriction to `W ∩ U α` is `f α s`.

## Implementation notes

The direct image of the restriction to an open set `A`, `(j_A)_* (j_A)^* F`, is
`((cechDiagramOpens V).obj F).obj (op A)`: its sections on `W` are the sections of `F` on `W ⊓ A`
(wrapped in `ULift`). The local maps are morphisms of sheaves on `V` into these direct images,
which is the form in which they enter the Čech complex. The Čech complex uses all tuples of
indices, not only the alternating ones, so no order on the index type and no finiteness of the
cover is needed; the total complex exists because the double complex lives in the first quadrant up
to the lower bound of `K`. The local description of the cohomology map is proved on sections: the
difference between the image of `s` and the image of a representing cycle is the total differential
of the Čech `0`-cochain `(h α β s)_β`.

## References

* [Stacks Project, Tag 02FU](https://stacks.math.columbia.edu/tag/02FU)
* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
* [P. Deligne, L. Illusie, *Relèvements modulo p² et décomposition du complexe de de Rham*,
  Invent. Math. 89 (1987)][DeligneIllusie1987], §2.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.CechSiteChange Stacks.CechTotalComplex.CoveringResolution
open ComplexShape
open Stacks.CategoryTheory.CechComplex (inter interπ interMap lift lift_comp_π)

universe w u

namespace MMP.DeRham

variable {V : Scheme.{u}} {ι : Type u} (U : ι → V.Opens)

/-- The functor `F ↦ ((j_A)_* (j_A)^* F)_A` sends zero morphisms to zero morphisms. -/
theorem cechDiagramOpens_map_zero (F G : V.Modules) :
    (cechDiagramOpens V).map (0 : F ⟶ G) = 0 := by
  ext W : 2
  apply SheafOfModules.hom_ext
  ext Y x
  rfl

/-- The functor `F ↦ ((j_A)_* (j_A)^* F)_A` preserves zero morphisms. -/
instance : (cechDiagramOpens V).PreservesZeroMorphisms where
  map_zero F G := cechDiagramOpens_map_zero F G

/-- The Čech complex functor on presheaves of modules on the opens preserves zero morphisms. -/
instance : (cechComplexFunctor U : ((V.Opens)ᵒᵖ ⥤ V.Modules) ⥤ _).PreservesZeroMorphisms where
  map_zero P Q := by
    ext n : 1
    refine Stacks.CategoryTheory.CechComplex.hom_ext U Q fun x => ?_
    rw [Stacks.AlgebraicGeometry.CoveringResolution.cech_map_f_comp_π]
    simp

/-- The sheafified Čech complex functor of the cover `U` preserves zero morphisms. -/
instance : (coveringComplexOpens V U).PreservesZeroMorphisms := by
  unfold coveringComplexOpens
  infer_instance

variable {U}

/-- The augmentation `F ⟶ Č⁰(𝒰, F)` in degree zero. -/
def cechAug (F : V.Modules) : F ⟶ ((coveringComplexOpens V U).obj F).X 0 :=
  (HomologicalComplex.singleObjXSelf (up ℕ) 0 F).inv ≫ ((augOpens V U).app F).f 0

/-- The augmentation `F ⟶ Č⁰(𝒰, F)` is natural in `F`. -/
theorem cechAug_naturality {F G : V.Modules} (φ : F ⟶ G) :
    cechAug F ≫ ((coveringComplexOpens V U).map φ).f 0 = φ ≫ cechAug (U := U) G := by
  have h := congrArg (fun t => HomologicalComplex.Hom.f t 0) ((augOpens V U).naturality φ)
  simp only [HomologicalComplex.comp_f,
    HomologicalComplex.single_map_f_self] at h
  simp only [cechAug, Category.assoc, ← h, Iso.inv_hom_id_assoc]

/-- The augmentation `F ⟶ Č⁰(𝒰, F)` composed with the Čech differential is zero. -/
theorem cechAug_comp_d (F : V.Modules) :
    cechAug (U := U) F ≫ ((coveringComplexOpens V U).obj F).d 0 1 = 0 := by
  rw [cechAug, Category.assoc, ((augOpens V U).app F).comm 0 1]
  simp only [HomologicalComplex.single_obj_d]
  exact (congrArg _ zero_comp).trans comp_zero

/-- For a cover `𝒰` of `V`, the sequence `F ⟶ Č⁰(𝒰, F) ⟶ Č¹(𝒰, F)` is exact and the
augmentation `F ⟶ Č⁰(𝒰, F)` is a monomorphism. -/
theorem cechAug_exact (hU : ⨆ i, U i = ⊤) (F : V.Modules) :
    (ShortComplex.mk (cechAug (U := U) F) _ (cechAug_comp_d F)).Exact ∧
      Mono (cechAug (U := U) F) := by
  have hq := quasiIso_augOpens_app V U hU F
  have h0 : QuasiIsoAt ((augOpens V U).app F) 0 := inferInstance
  rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros _ (by simp; rfl)
    (by simp; rfl) (by simp)] at h0
  obtain ⟨h1, h2⟩ := h0
  refine ⟨ShortComplex.exact_of_iso
    (ShortComplex.isoMk (HomologicalComplex.singleObjXSelf (up ℕ) 0 F)
      (Iso.refl _) (Iso.refl _) ?_ ?_) h1, ?_⟩
  · simp only [cechAug]
    exact (Category.comp_id _).symm
  · exact (Category.id_comp _).trans (Category.comp_id _).symm
  · have hm : Mono (((augOpens V U).app F).f 0) := h2
    exact mono_comp _ _

/-- An exact short complex with monic first map: the induced map into the kernel of the second
map is an isomorphism. -/
theorem isIso_kernel_lift_of_exact {A : Type*} [Category A] [Abelian A] (S : ShortComplex A)
    (hS : S.Exact) [Mono S.f] : IsIso (kernel.lift S.g S.f S.zero) :=
  have := hS.epi_kernelLift
  isIso_of_mono_of_epi _

/-- The augmentation into degree zero of the `ℤ`-indexed Čech complex. -/
def cechAugExt (F : V.Modules) :
    F ⟶ (((coveringComplexOpens V U).obj F).extend embeddingUpNat).X 0 :=
  cechAug F ≫ (((coveringComplexOpens V U).obj F).extendXIso embeddingUpNat
    embeddingUpNat_f_zero).inv

/-- The augmentation into the `ℤ`-indexed Čech complex is natural in `F`. -/
theorem cechAugExt_naturality {F G : V.Modules} (φ : F ⟶ G) :
    cechAugExt (U := U) F ≫
        (HomologicalComplex.extendMap ((coveringComplexOpens V U).map φ) embeddingUpNat).f 0 =
      φ ≫ cechAugExt G := by
  rw [HomologicalComplex.extendMap_f _ embeddingUpNat embeddingUpNat_f_zero]
  simp only [cechAugExt, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, cechAug_naturality, Category.assoc]

/-- The augmentation into the `ℤ`-indexed Čech complex composed with the differential in degree
zero is zero. -/
theorem cechAugExt_comp_d (F : V.Modules) :
    cechAugExt (U := U) F ≫
      (((coveringComplexOpens V U).obj F).extend embeddingUpNat).d 0 1 = 0 := by
  rw [HomologicalComplex.extend_d_eq _ embeddingUpNat (i' := 0) (j' := 1) (i := 0) (j := 1)
    embeddingUpNat_f_zero rfl]
  simp only [cechAugExt, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, cechAug_comp_d, zero_comp]

/-- For a cover `𝒰` of `V`, the augmentation into the `ℤ`-indexed Čech complex is a monomorphism
whose image is the kernel of the differential in degree zero. -/
theorem cechAugExt_exact (hU : ⨆ i, U i = ⊤) (F : V.Modules) :
    (ShortComplex.mk (cechAugExt (U := U) F) _ (cechAugExt_comp_d F)).Exact ∧
      Mono (cechAugExt (U := U) F) := by
  obtain ⟨h1, h2⟩ := cechAug_exact (U := U) hU F
  refine ⟨ShortComplex.exact_of_iso (ShortComplex.isoMk
    (S₁ := ShortComplex.mk (cechAug (U := U) F) _ (cechAug_comp_d F)) (Iso.refl _)
    (((coveringComplexOpens V U).obj F).extendXIso embeddingUpNat embeddingUpNat_f_zero).symm
    (((coveringComplexOpens V U).obj F).extendXIso embeddingUpNat (i := 1) rfl).symm ?_ ?_) h1, ?_⟩
  · simp [cechAugExt]
  · simp [HomologicalComplex.extend_d_eq _ embeddingUpNat (i' := 0) (j' := 1) (i := 0) (j := 1)
      embeddingUpNat_f_zero rfl]
    rfl
  · exact mono_comp _ _

variable (U) in
/-- **The Čech double complex** of a cochain complex `K`: in bidegree `(p, q)` it is the Čech
cochains `Č^q(𝒰, K^p)`, the sheafified ones (products of direct images of restrictions). -/
abbrev cechBicomplex (K : CochainComplex V.Modules ℤ) :
    HomologicalComplex₂ V.Modules (up ℤ) (up ℤ) :=
  ((coveringComplexOpens V U ⋙ embeddingUpNat.extendFunctor V.Modules).mapHomologicalComplex
    (up ℤ)).obj K

/-- The augmentation `K^p ⟶ Č⁰(𝒰, K^p)` into the Čech double complex. -/
def cechAugBi (K : CochainComplex V.Modules ℤ) (p : ℤ) :
    K.X p ⟶ ((cechBicomplex U K).X p).X 0 :=
  cechAugExt (K.X p)

/-- The augmentation `K^p ⟶ Č⁰(𝒰, K^p)` composed with the Čech differential is zero. -/
theorem cechAugBi_comp_d (K : CochainComplex V.Modules ℤ) (p : ℤ) :
    cechAugBi (U := U) K p ≫ ((cechBicomplex U K).X p).d 0 1 = 0 :=
  cechAugExt_comp_d _

/-- The augmentations `K^p ⟶ Č⁰(𝒰, K^p)` commute with the differentials of `K` and of the
Čech double complex. -/
theorem cechAugBi_naturality (K : CochainComplex V.Modules ℤ) (p p' : ℤ) :
    cechAugBi (U := U) K p ≫ ((cechBicomplex U K).d p p').f 0 = K.d p p' ≫ cechAugBi K p' :=
  cechAugExt_naturality _

/-- The augmentation of `K` into the row `q = 0` of its Čech double complex. -/
def cechAugRow (K : CochainComplex V.Modules ℤ) : K ⟶ rowZero (cechBicomplex U K) where
  f p := cechAugBi K p
  comm' p p' _ := cechAugBi_naturality K p p'

/-- For a cover `𝒰` of `V` and a bounded below `K`, the Čech double complex and the augmentation
of `K` into its row `q = 0` satisfy the hypotheses of the comparison with the total complex. -/
theorem cechAugRow_hypotheses (hU : ⨆ i, U i = ⊤) (K : CochainComplex V.Modules ℤ) (a : ℤ)
    [K.IsStrictlyGE a] : Hypotheses K (cechBicomplex U K) (cechAugRow K) where
  diagonalFinite N := by
    refine (Set.finite_Icc a N).subset fun p hp => ?_
    simp only [Set.mem_ofPred_eq] at hp
    constructor
    · by_contra h
      push Not at h
      exact hp ((HomologicalComplex.eval _ _ (N - p)).map_isZero
        ((coveringComplexOpens V U ⋙ embeddingUpNat.extendFunctor V.Modules).map_isZero
          (K.isZero_of_isStrictlyGE a p h)))
    · by_contra h
      push Not at h
      exact hp (HomologicalComplex.isZero_extend_X _ _ _ (fun i => by
        change (i : ℤ) ≠ _
        omega))
  zero_of_neg p q hq := HomologicalComplex.isZero_extend_X _ _ _ (fun i => by
    change (i : ℤ) ≠ _
    omega)
  exactAt_of_ne_zero p q hq := by
    rcases lt_or_gt_of_ne hq with h | h
    · exact HomologicalComplex.extend_exactAt _ _ _ (fun i => by
        change (i : ℤ) ≠ _
        omega)
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, q = ((k + 1 : ℕ) : ℤ) := ⟨(q - 1).toNat, by omega⟩
      change (((coveringComplexOpens V U).obj (K.X p)).extend embeddingUpNat).ExactAt
        (embeddingUpNat.f (k + 1))
      rw [HomologicalComplex.extend_exactAt_iff _ embeddingUpNat rfl]
      have := quasiIso_augOpens_app V U hU (K.X p)
      exact (quasiIsoAt_iff_exactAt ((augOpens V U).app (K.X p)) _
        (CochainComplex.exactAt_succ_single_obj _ _)).1 inferInstance
  inducesIsoKernel p := by
    obtain ⟨h1, h2⟩ := cechAugExt_exact (U := U) hU (K.X p)
    exact ⟨cechAugExt_comp_d _, isIso_kernel_lift_of_exact _ h1⟩

variable (U) in
/-- The Čech total complex `Tot Č(𝒰, K)`. -/
abbrev cechTotal (K : CochainComplex V.Modules ℤ) : CochainComplex V.Modules ℤ :=
  (cechBicomplex U K).total (up ℤ)

variable (U) in
/-- The comparison map `K ⟶ Tot Č(𝒰, K)`: in degree `n` the augmentation `K^n ⟶ Č⁰(𝒰, K^n)`
followed by the inclusion of the summand of bidegree `(n, 0)`. -/
def toCechTotal (K : CochainComplex V.Modules ℤ) : K ⟶ cechTotal U K where
  f n := cechAugBi K n ≫ (cechBicomplex U K).ιTotal (up ℤ) n 0 n (add_zero n)
  comm' n m h := by
    obtain rfl : n + 1 = m := h
    have h0 : cechAugBi (U := U) K n ≫ ((cechBicomplex U K).X n).d 0 (0 + 1) = 0 :=
      cechAugBi_comp_d K n
    rw [Category.assoc, HomologicalComplex₂.ιTotal_d_up_ℤ, Preadditive.comp_add, Units.smul_def,
      Preadditive.comp_zsmul, reassoc_of% h0, zero_comp, smul_zero, add_zero,
      reassoc_of% (cechAugBi_naturality K n (n + 1))]

/-- In degree `n`, `toCechTotal` is the augmentation `K^n ⟶ Č⁰(𝒰, K^n)` followed by the
inclusion of the summand of bidegree `(n, 0)`. -/
theorem toCechTotal_f (K : CochainComplex V.Modules ℤ) (n : ℤ) :
    (toCechTotal U K).f n =
      cechAugBi K n ≫ (cechBicomplex U K).ιTotal (up ℤ) n 0 n (add_zero n) := rfl

/-- **The Čech resolution of a bounded below complex**: `K ⟶ Tot Č(𝒰, K)` is a
quasi-isomorphism for every open cover `𝒰`. -/
theorem quasiIso_toCechTotal (hU : ⨆ i, U i = ⊤) (K : CochainComplex V.Modules ℤ) (a : ℤ)
    [K.IsStrictlyGE a] : QuasiIso (toCechTotal U K) := by
  obtain ⟨f, hf, hq⟩ := exists_comparisonMap_p K (cechBicomplex U K) (cechAugRow K)
    (cechAugRow_hypotheses hU K a) inferInstance
  obtain rfl : toCechTotal U K = f := by
    ext n
    rw [hf]
    rfl
  exact hq

/-! ### Morphisms into the Čech double complex -/

/-- The term of bidegree `(p, m)` of the Čech double complex is the degree `m` Čech term of
`K^p`. -/
def cechBiXIso (K : CochainComplex V.Modules ℤ) (p : ℤ) (m : ℕ) :
    ((cechBicomplex U K).X p).X m ≅
      ((cechComplexFunctor U).obj ((cechDiagramOpens V).obj (K.X p))).X m :=
  ((coveringComplexOpens V U).obj (K.X p)).extendXIso embeddingUpNat rfl

/-- The horizontal differential of the Čech double complex is, under `cechBiXIso`, the Čech
complex functor applied to the differential of `K`. -/
theorem cechBi_d_f (K : CochainComplex V.Modules ℤ) (p p' : ℤ) (m : ℕ) :
    ((cechBicomplex U K).d p p').f m = (cechBiXIso K p m).hom ≫
      ((cechComplexFunctor U).map ((cechDiagramOpens V).map (K.d p p'))).f m ≫
        (cechBiXIso K p' m).inv :=
  HomologicalComplex.extendMap_f _ embeddingUpNat rfl

/-- The vertical differential of the Čech double complex is, under `cechBiXIso`, the
differential of the Čech complex of `K^p`. -/
theorem cechBi_X_d (K : CochainComplex V.Modules ℤ) (p : ℤ) (m : ℕ) :
    ((cechBicomplex U K).X p).d m ((m + 1 : ℕ) : ℤ) = (cechBiXIso K p m).hom ≫
      ((cechComplexFunctor U).obj ((cechDiagramOpens V).obj (K.X p))).d m (m + 1) ≫
        (cechBiXIso K p (m + 1)).inv :=
  HomologicalComplex.extend_d_eq _ embeddingUpNat rfl rfl

variable (U) in
/-- A morphism into the term of bidegree `(p, m)` of the Čech double complex, given by its
components on the `(m + 1)`-fold intersections. -/
def toCechBi (K : CochainComplex V.Modules ℤ) (p : ℤ) (m : ℕ) {M : V.Modules}
    (g : ∀ x : Fin (m + 1) → ι, M ⟶ ((cechDiagramOpens V).obj (K.X p)).obj (op (inter U x))) :
    M ⟶ ((cechBicomplex U K).X p).X m :=
  lift U _ g ≫ (cechBiXIso K p m).inv

/-- The projection of the term of bidegree `(p, m)` of the Čech double complex onto the factor
of an `(m + 1)`-fold intersection. -/
def cechBiπ (K : CochainComplex V.Modules ℤ) (p : ℤ) (m : ℕ) (x : Fin (m + 1) → ι) :
    ((cechBicomplex U K).X p).X m ⟶ ((cechDiagramOpens V).obj (K.X p)).obj (op (inter U x)) :=
  (cechBiXIso K p m).hom ≫ Stacks.CategoryTheory.CechComplex.π U _ m x

/-- The components of `toCechBi U K p m g` are the maps `g x`. -/
@[reassoc (attr := simp)]
theorem toCechBi_cechBiπ (K : CochainComplex V.Modules ℤ) (p : ℤ) (m : ℕ) {M : V.Modules}
    (g : ∀ x : Fin (m + 1) → ι, M ⟶ ((cechDiagramOpens V).obj (K.X p)).obj (op (inter U x)))
    (x : Fin (m + 1) → ι) : toCechBi U K p m g ≫ cechBiπ K p m x = g x := by
  rw [toCechBi, cechBiπ, Category.assoc, Iso.inv_hom_id_assoc, lift_comp_π]

/-- Two morphisms into the term of bidegree `(p, m)` of the Čech double complex agree if their
components on every `(m + 1)`-fold intersection agree. -/
theorem cechBi_hom_ext (K : CochainComplex V.Modules ℤ) (p : ℤ) (m : ℕ) {M : V.Modules}
    {a b : M ⟶ ((cechBicomplex U K).X p).X m}
    (h : ∀ x, a ≫ cechBiπ K p m x = b ≫ cechBiπ K p m x) : a = b := by
  rw [← cancel_mono (cechBiXIso (U := U) K p m).hom]
  exact Stacks.CategoryTheory.CechComplex.hom_ext U _ fun x => by
    simpa only [cechBiπ, Category.assoc] using h x

/-- The horizontal differential of the Čech double complex, on the factors: the differential of
`K` on each intersection. -/
@[reassoc (attr := simp)]
theorem cechBi_d_f_cechBiπ (K : CochainComplex V.Modules ℤ) (p p' : ℤ) (m : ℕ)
    (x : Fin (m + 1) → ι) :
    ((cechBicomplex U K).d p p').f m ≫ cechBiπ K p' m x =
      cechBiπ K p m x ≫ ((cechDiagramOpens V).map (K.d p p')).app (op (inter U x)) := by
  rw [cechBi_d_f, cechBiπ, cechBiπ, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc]
  exact congrArg (_ ≫ ·)
    (Stacks.AlgebraicGeometry.CoveringResolution.cech_map_f_comp_π U _ m x)

/-- The vertical (Čech) differential of the Čech double complex, on the factors: the
alternating sum of the restrictions. -/
theorem cechBi_X_d_cechBiπ (K : CochainComplex V.Modules ℤ) (p : ℤ) (m : ℕ)
    (y : Fin (m + 2) → ι) :
    ((cechBicomplex U K).X p).d m ((m + 1 : ℕ) : ℤ) ≫ cechBiπ K p (m + 1) y =
      ∑ i : Fin (m + 2), (-1 : ℤ) ^ (i : ℕ) • (cechBiπ K p m (y ∘ i.succAbove) ≫
        ((cechDiagramOpens V).obj (K.X p)).map (interMap U y i.succAbove).op) := by
  rw [cechBi_X_d, cechBiπ, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc,
    Stacks.CategoryTheory.CechComplex.d_comp_π, Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Preadditive.comp_zsmul, cechBiπ, Category.assoc]

/-- An open contained in every `U (x a)` is contained in their intersection `inter U x`. -/
theorem le_inter {m : ℕ} {x : Fin m → ι} {T : V.Opens} (h : ∀ a, T ≤ U (x a)) :
    T ≤ inter U x :=
  leOfHom (Stacks.CategoryTheory.CechComplex.interLift U fun a => homOfLE (h a))

/-! ### Sections -/

/-- Two successive restrictions of a section are the restriction along the composite. -/
theorem presheaf_map_map {F : V.Modules} {A B C : V.Opens} (f : B ⟶ A) (g : C ⟶ B) (k : C ⟶ A)
    (t : Γ(F, A)) : F.presheaf.map g.op (F.presheaf.map f.op t) = F.presheaf.map k.op t := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  exact congrArg (fun r : C ⟶ A => F.presheaf.map r.op t) (Subsingleton.elim _ _)

/-- Restriction of a section along the identity of an open is the identity. -/
theorem presheaf_map_id {F : V.Modules} {A : V.Opens} (k : A ⟶ A) (t : Γ(F, A)) :
    F.presheaf.map k.op t = t := by
  rw [show k = 𝟙 A from Subsingleton.elim _ _, op_id, F.presheaf.map_id]
  rfl

/-- A morphism of sheaves of modules commutes with restriction of sections. -/
theorem app_presheaf_map {F G : V.Modules} (φ : F ⟶ G) {A B : V.Opens} (i : A ⟶ B)
    (x : Γ(F, B)) : φ.app A (F.presheaf.map i.op x) = G.presheaf.map i.op (φ.app B x) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply]
  exact congrArg (fun f => f x) (congrArg ConcreteCategory.hom (φ.mapPresheaf.naturality i.op))

/-- The sections of `k • φ` on `W` are `k` times those of `φ`. -/
theorem zsmul_app_apply {F G : V.Modules} (φ : F ⟶ G) (k : ℤ) (W : V.Opens) (x : Γ(F, W)) :
    (k • φ).app W x = k • φ.app W x := by
  have h := map_zsmul (AddMonoidHom.mk' (fun ψ : F ⟶ G => ψ.app W)
    (fun a b => Scheme.Modules.Hom.add_app a b)) k φ
  simp only [AddMonoidHom.mk'_apply] at h
  rw [h]
  rfl

/-- A monomorphism of sheaves of modules is injective on sections over every open. -/
theorem app_injective_of_mono {F G : V.Modules} (φ : F ⟶ G) [Mono φ] (W : V.Opens) :
    Function.Injective (φ.app W) := by
  have : Mono ((Scheme.Modules.toPresheaf V).map φ) := inferInstance
  have : Mono (((Scheme.Modules.toPresheaf V).map φ).app (op W)) := inferInstance
  exact (AddCommGrpCat.mono_iff_injective _).1 this

/-- Sections of `(j_A)_* (j_A)^* F` on `W` are sections of `F` on `W ⊓ A`, and restriction along
`A ⟶ B` is restriction of sections. -/
theorem cechDiagram_map_app_down (F : V.Modules) {A B : V.Opens} (g : A ⟶ B) (W : V.Opens)
    (x : Γ(((cechDiagramOpens V).obj F).obj (op B), W)) :
    ((((cechDiagramOpens V).obj F).map g.op).app W x).down =
      F.presheaf.map (homOfLE (inf_le_inf_left W (leOfHom g))).op x.down := rfl

/-- The map induced by `φ : F ⟶ G` on sections over `W` of `(j_A)_* (j_A)^* F` is `φ` on
sections over `W ⊓ A`. -/
theorem cechDiagram_map_app_app_down {F G : V.Modules} (φ : F ⟶ G) (A W : V.Opens)
    (x : Γ(((cechDiagramOpens V).obj F).obj (op A), W)) :
    ((((cechDiagramOpens V).map φ).app (op A)).app W x).down = φ.app (W ⊓ A) x.down := rfl

/-- Restriction `(j_B)_* (j_B)^* F ⟶ (j_A)_* (j_A)^* F` is bijective on sections over `W` when
`W ⊓ B ≤ A`. -/
theorem cechDiagram_map_app_bijective (F : V.Modules) {A B : V.Opens} (g : A ⟶ B)
    {W : V.Opens} (h : W ⊓ B ≤ A) :
    Function.Bijective ((((cechDiagramOpens V).obj F).map g.op).app W) := by
  refine Function.bijective_iff_has_inverse.2 ⟨fun y => ULift.up
    (F.presheaf.map (homOfLE (le_inf inf_le_left h : W ⊓ B ≤ W ⊓ A)).op y.down), fun x => ?_,
    fun y => ?_⟩ <;>
  exact ULift.ext ((presheaf_map_map _ _ (𝟙 _) _).trans (presheaf_map_id _ _))

/-- Two sections over `W` of a product of sheaves of modules agree if all their components
agree. -/
theorem sections_ext_of_isLimit {J : Type u} {f : J → V.Modules} {c : Fan f} (hc : IsLimit c)
    (W : V.Opens) (a b : Γ(c.pt, W)) (h : ∀ j, (c.proj j).app W a = (c.proj j).app W b) :
    a = b := by
  have hc' := isLimitOfPreserves (forget AddCommGrpCat.{u})
    (isLimitOfPreserves ((evaluation (V.Opens)ᵒᵖ Ab.{u}).obj (op W))
      (isLimitOfPreserves (Scheme.Modules.toPresheaf V) hc))
  apply (Types.isLimitEquivSections hc').injective
  ext ⟨j⟩
  exact h j

/-- A family of sections over `W` of the factors of a product of sheaves of modules comes from a
section of the product. -/
theorem exists_sections_of_isLimit {J : Type u} {f : J → V.Modules} {c : Fan f} (hc : IsLimit c)
    (W : V.Opens) (g : ∀ j, Γ(f j, W)) : ∃ a : Γ(c.pt, W), ∀ j, (c.proj j).app W a = g j := by
  have hc' := isLimitOfPreserves (forget AddCommGrpCat.{u})
    (isLimitOfPreserves ((evaluation (V.Opens)ᵒᵖ Ab.{u}).obj (op W))
      (isLimitOfPreserves (Scheme.Modules.toPresheaf V) hc))
  refine ⟨(Types.isLimitEquivSections hc').symm ⟨fun j => g j.as, ?_⟩, fun j => ?_⟩
  · rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl⟩⟩
    rfl
  · exact Types.isLimitEquivSections_symm_apply hc' _ ⟨j⟩

/-- Two sections over `W` of the term of bidegree `(p, m)` of the Čech double complex agree if
their components on every `(m + 1)`-fold intersection agree. -/
theorem cechBi_sections_ext (K : CochainComplex V.Modules ℤ) (p : ℤ) (m : ℕ) (W : V.Opens)
    (a b : Γ(((cechBicomplex U K).X p).X m, W))
    (h : ∀ x, (cechBiπ K p m x).app W a = (cechBiπ K p m x).app W b) : a = b :=
  app_injective_of_mono (cechBiXIso (U := U) K p m).hom W <|
    sections_ext_of_isLimit (Stacks.CategoryTheory.CechComplex.isLimitFan U _ m) W _ _
      fun x => by simpa [cechBiπ] using h x

/-- A family of sections over `W` on the `(m + 1)`-fold intersections comes from a section over
`W` of the term of bidegree `(p, m)` of the Čech double complex. -/
theorem cechBi_sections_exists (K : CochainComplex V.Modules ℤ) (p : ℤ) (m : ℕ) (W : V.Opens)
    (g : ∀ x : Fin (m + 1) → ι, Γ(((cechDiagramOpens V).obj (K.X p)).obj (op (inter U x)), W)) :
    ∃ a : Γ(((cechBicomplex U K).X p).X m, W), ∀ x, (cechBiπ K p m x).app W a = g x := by
  obtain ⟨b, hb⟩ := exists_sections_of_isLimit
    (Stacks.CategoryTheory.CechComplex.isLimitFan U _ m) W g
  refine ⟨(cechBiXIso (U := U) K p m).inv.app W b, fun x => ?_⟩
  rw [← hb x, ← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app]
  simp [cechBiπ]

/-- The augmentation `cechAug` is the augmentation `augZero` of the covering resolution, up to
the universe lift `moduleUniverseLiftOpensIso`. -/
theorem cechAug_eq (F : V.Modules) : cechAug (U := U) F =
    (moduleUniverseLiftOpensIso V).inv.app F ≫
      Stacks.AlgebraicGeometry.CoveringResolution.augZero.{u, u, u, u} V.carrier V.ringCatSheaf
        U F := by
  rw [cechAug, augOpens_app, HomologicalComplex.comp_f, HomologicalComplex.single_map_f_self]
  erw [Stacks.AlgebraicGeometry.CoveringResolution.augmentationNatTrans_f_zero]
  simp
  rfl

/-- The augmentation is restriction of sections. -/
theorem cechAug_π_app (F : V.Modules) (x : Fin 1 → ι) (W : V.Opens) (t : Γ(F, W)) :
    ((cechAug (U := U) F ≫ Stacks.CategoryTheory.CechComplex.π U _ 0 x).app W t).down =
      F.presheaf.map (homOfLE (inf_le_left : W ⊓ inter U x ≤ W)).op t := by
  have e : (cechAug (U := U) F ≫ Stacks.CategoryTheory.CechComplex.π U _ 0 x).app W t =
    (Stacks.CategoryTheory.CechComplex.π U
        (Stacks.CechTotalComplex.CoveringResolution.infPushforwardOpens.{u, u, u, u} V.carrier
          V.ringCatSheaf F) 0 x).val.app (op W)
      ((Stacks.AlgebraicGeometry.CoveringResolution.augZero.{u, u, u, u} V.carrier
        V.ringCatSheaf U F).val.app (op W)
          (((moduleUniverseLiftOpensIso V).inv.app F).app W t)) := by
    rw [cechAug_eq]
    rfl
  exact (congrArg ULift.down e).trans
    ((Stacks.AlgebraicGeometry.CoveringResolution.augZero_comp_π_down.{u, u, u, u} V.carrier
      V.ringCatSheaf U F W x _).trans (presheaf_map_map (F := F) _ _ _ t))

/-- The components of the augmentation `K^p ⟶ Č⁰(𝒰, K^p)` are those of the augmentation
`cechAug` of `K^p`. -/
theorem cechAugBi_cechBiπ (K : CochainComplex V.Modules ℤ) (p : ℤ) (x : Fin 1 → ι) :
    cechAugBi (U := U) K p ≫ cechBiπ K p 0 x =
      cechAug (K.X p) ≫ Stacks.CategoryTheory.CechComplex.π U _ 0 x :=
  (Category.assoc _ _ _).trans
    (congrArg (cechAug (K.X p) ≫ ·) (Iso.inv_hom_id_assoc (cechBiXIso (U := U) K p 0) _))

/-! ### Local maps glued up to a coherent homotopy -/

variable (U) in
/-- **Local maps into a complex, glued up to a coherent homotopy.** For a sheaf of modules `M`,
a cochain complex `K` and a degree `n`, the data of maps `f α : M ⟶ (j_α)_* (j_α)^* K^{n+1}`
on the members `U α` of the cover, killed by the differential, of homotopies
`h α β : M ⟶ (j_{αβ})_* (j_{αβ})^* K^n` on the double intersections with
`f β - f α = d ∘ h α β`, and of the cocycle condition `h α β + h β γ = h α γ` on the triple
intersections. Here `(j_W)_* (j_W)^* F` is `(cechDiagramOpens V).obj F` at `W`, whose sections on
`W'` are those of `F` on `W' ⊓ W`. -/
structure CechGluingData (K : CochainComplex V.Modules ℤ) (M : V.Modules) (n : ℤ) where
  /-- The local maps. -/
  f (α : ι) : M ⟶ ((cechDiagramOpens V).obj (K.X (n + 1))).obj (op (U α))
  /-- The homotopies on the double intersections. -/
  h (α β : ι) : M ⟶ ((cechDiagramOpens V).obj (K.X n)).obj (op (U α ⊓ U β))
  /-- The local maps are killed by the differential of `K`. -/
  f_d (α : ι) : f α ≫ ((cechDiagramOpens V).map (K.d (n + 1) (n + 2))).app (op (U α)) = 0
  /-- On `U α ⊓ U β`, the difference `f β - f α` is the differential of `h α β`. -/
  f_sub_f (α β : ι) :
    f β ≫ ((cechDiagramOpens V).obj (K.X (n + 1))).map
        (homOfLE (inf_le_right : U α ⊓ U β ≤ U β)).op -
      f α ≫ ((cechDiagramOpens V).obj (K.X (n + 1))).map
        (homOfLE (inf_le_left : U α ⊓ U β ≤ U α)).op =
    h α β ≫ ((cechDiagramOpens V).map (K.d n (n + 1))).app (op (U α ⊓ U β))
  /-- The cocycle condition `h α β + h β γ = h α γ` on `U α ⊓ U β ⊓ U γ`. -/
  h_add (α β γ : ι) :
    h α β ≫ ((cechDiagramOpens V).obj (K.X n)).map
        (homOfLE (inf_le_left : U α ⊓ U β ⊓ U γ ≤ U α ⊓ U β)).op +
      h β γ ≫ ((cechDiagramOpens V).obj (K.X n)).map
        (homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          U α ⊓ U β ⊓ U γ ≤ U β ⊓ U γ)).op =
    h α γ ≫ ((cechDiagramOpens V).obj (K.X n)).map
        (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
          U α ⊓ U β ⊓ U γ ≤ U α ⊓ U γ)).op

/-- Inserting the isomorphisms `b` and `c` and their inverses does not change `a.hom ≫ k`. -/
theorem iso_comp_aux {C : Type*} [Category C] {A B X Y Z : C} (a : A ≅ B) (b : B ≅ X)
    (k : B ⟶ Y) (c : Z ≅ Y) : a.hom ≫ k = (a ≪≫ b).hom ≫ ((b.inv ≫ k) ≫ c.inv) ≫ c.hom := by
  simp

section

variable [HasDerivedCategory.{w} V.Modules]

/-- The identification of the cohomology in degree `m` of `M[-m]` with `M`. -/
def homologySingleIso (m : ℤ) (M : V.Modules) : (DerivedCategory.homologyFunctor V.Modules m).obj
    ((DerivedCategory.singleFunctor V.Modules m).obj M) ≅ M :=
  (DerivedCategory.homologyFunctor V.Modules m).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ V.Modules m).app M) ≪≫
    (DerivedCategory.homologyFunctorFactors V.Modules m).app _ ≪≫
      HomologicalComplex.singleObjHomologySelfIso (up ℤ) m M

end

namespace CechGluingData

variable {K : CochainComplex V.Modules ℤ} {M : V.Modules} {n : ℤ} (D : CechGluingData U K M n)

/-- The Čech `0`-cochain of `K^{n+1}` given by the local maps. -/
def cechF : M ⟶ ((cechBicomplex U K).X (n + 1)).X ((0 : ℕ) : ℤ) :=
  toCechBi U K (n + 1) 0 fun x =>
    D.f (x 0) ≫ ((cechDiagramOpens V).obj (K.X (n + 1))).map (interπ U x 0).op

/-- The Čech `1`-cochain of `K^n` given by the homotopies. -/
def cechH : M ⟶ ((cechBicomplex U K).X n).X ((1 : ℕ) : ℤ) :=
  toCechBi U K n 1 fun x =>
    D.h (x 0) (x 1) ≫ ((cechDiagramOpens V).obj (K.X n)).map
      (homOfLE (le_inf (leOfHom (interπ U x 0)) (leOfHom (interπ U x 1)))).op

/-- The Čech `0`-cochain `cechF` is killed by the horizontal differential. -/
theorem cechF_d : D.cechF ≫ ((cechBicomplex U K).d (n + 1) (n + 2)).f ((0 : ℕ) : ℤ) = 0 := by
  refine cechBi_hom_ext K (n + 2) 0 fun x => ?_
  rw [Category.assoc, cechBi_d_f_cechBiπ, cechF, toCechBi_cechBiπ_assoc, zero_comp,
    Category.assoc, NatTrans.naturality, reassoc_of% (D.f_d (x 0)), zero_comp]

/-- The Čech `1`-cochain `cechH` is a Čech cocycle. -/
theorem cechH_d :
    D.cechH ≫ ((cechBicomplex U K).X n).d ((1 : ℕ) : ℤ) ((1 + 1 : ℕ) : ℤ) = 0 := by
  refine cechBi_hom_ext K n 2 fun y => ?_
  rw [Category.assoc, cechBi_X_d_cechBiπ, zero_comp, Preadditive.comp_sum, Fin.sum_univ_three]
  simp only [cechH, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero,
    pow_one, one_smul, neg_smul, neg_one_sq, Preadditive.comp_neg, toCechBi_cechBiπ_assoc,
    Category.assoc, ← Functor.map_comp, ← op_comp]
  have h01 : inter U y ≤ U (y 0) ⊓ U (y 1) :=
    le_inf (leOfHom (interπ U y 0)) (leOfHom (interπ U y 1))
  have h02 : inter U y ≤ U (y 0) ⊓ U (y 2) :=
    le_inf (leOfHom (interπ U y 0)) (leOfHom (interπ U y 2))
  have h12 : inter U y ≤ U (y 1) ⊓ U (y 2) :=
    le_inf (leOfHom (interπ U y 1)) (leOfHom (interπ U y 2))
  have T : inter U y ≤ U (y 0) ⊓ U (y 1) ⊓ U (y 2) := le_inf h01 (leOfHom (interπ U y 2))
  change D.h (y 1) (y 2) ≫ ((cechDiagramOpens V).obj (K.X n)).map (homOfLE h12).op +
    -(D.h (y 0) (y 2) ≫ ((cechDiagramOpens V).obj (K.X n)).map (homOfLE h02).op) +
    D.h (y 0) (y 1) ≫ ((cechDiagramOpens V).obj (K.X n)).map (homOfLE h01).op = 0
  have key := congrArg (· ≫ ((cechDiagramOpens V).obj (K.X n)).map (homOfLE T).op)
    (D.h_add (y 0) (y 1) (y 2))
  simp only [Preadditive.add_comp, Category.assoc, ← Functor.map_comp, ← op_comp] at key
  change D.h (y 0) (y 1) ≫ ((cechDiagramOpens V).obj (K.X n)).map (homOfLE h01).op +
    D.h (y 1) (y 2) ≫ ((cechDiagramOpens V).obj (K.X n)).map (homOfLE h12).op =
    D.h (y 0) (y 2) ≫ ((cechDiagramOpens V).obj (K.X n)).map (homOfLE h02).op at key
  rw [← key]
  abel

/-- The horizontal differential of `cechH` is the Čech differential of `cechF`. -/
theorem cechH_d_f :
    D.cechH ≫ ((cechBicomplex U K).d n (n + 1)).f ((1 : ℕ) : ℤ) =
      D.cechF ≫ ((cechBicomplex U K).X (n + 1)).d ((0 : ℕ) : ℤ) ((1 : ℕ) : ℤ) := by
  change _ = D.cechF ≫ ((cechBicomplex U K).X (n + 1)).d ((0 : ℕ) : ℤ) ((0 + 1 : ℕ) : ℤ)
  refine cechBi_hom_ext K (n + 1) 1 fun y => ?_
  rw [Category.assoc, cechBi_d_f_cechBiπ, cechH, toCechBi_cechBiπ_assoc, Category.assoc,
    NatTrans.naturality, ← Category.assoc, ← D.f_sub_f, Category.assoc, cechBi_X_d_cechBiπ,
    Preadditive.comp_sum, Fin.sum_univ_two]
  simp only [cechF, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    one_smul, neg_smul, Preadditive.comp_neg, toCechBi_cechBiπ_assoc, Category.assoc,
    ← Functor.map_comp, ← op_comp, Preadditive.sub_comp]
  have g0 : inter U y ≤ U (y 0) := leOfHom (interπ U y 0)
  have g1 : inter U y ≤ U (y 1) := leOfHom (interπ U y 1)
  change D.f (y 1) ≫ ((cechDiagramOpens V).obj (K.X (n + 1))).map (homOfLE g1).op -
    D.f (y 0) ≫ ((cechDiagramOpens V).obj (K.X (n + 1))).map (homOfLE g0).op =
    D.f (y 1) ≫ ((cechDiagramOpens V).obj (K.X (n + 1))).map (homOfLE g1).op +
    -(D.f (y 0) ≫ ((cechDiagramOpens V).obj (K.X (n + 1))).map (homOfLE g0).op)
  exact sub_eq_add_neg _ _

/-- The Čech cocycle of total degree `n + 1` given by the local maps and the homotopies. -/
def cechCocycle : M ⟶ (cechTotal U K).X (n + 1) :=
  D.cechF ≫ (cechBicomplex U K).ιTotal (up ℤ) (n + 1) ((0 : ℕ) : ℤ) (n + 1) (by simp) +
    (n.negOnePow : ℤ) •
      (D.cechH ≫ (cechBicomplex U K).ιTotal (up ℤ) n ((1 : ℕ) : ℤ) (n + 1) (by simp))

/-- The Čech cochain `cechCocycle` is a cocycle of the total complex. -/
theorem cechCocycle_d (k : ℤ) (hk : n + 1 + 1 = k) :
    D.cechCocycle ≫ (cechTotal U K).d (n + 1) k = 0 := by
  rw [cechCocycle, Preadditive.add_comp, Preadditive.zsmul_comp, Category.assoc, Category.assoc,
    StacksDraft.TotalSingleRow.ιTotal_d_up_ℤ' _ (n + 1) (n + 2) ((0 : ℕ) : ℤ) ((1 : ℕ) : ℤ)
      (n + 1) k (by ring) (by simp) (by simp) hk,
    StacksDraft.TotalSingleRow.ιTotal_d_up_ℤ' _ n (n + 1) ((1 : ℕ) : ℤ) ((1 + 1 : ℕ) : ℤ)
      (n + 1) k rfl (by simp) (by simp) hk,
    Preadditive.comp_add, Preadditive.comp_add, reassoc_of% D.cechF_d, zero_comp,
    Linear.comp_units_smul, Linear.comp_units_smul, reassoc_of% D.cechH_d, zero_comp, smul_zero,
    reassoc_of% D.cechH_d_f]
  simp only [Int.negOnePow_succ, Units.smul_def, add_zero, zero_add,
    Units.val_neg, neg_smul, neg_add_cancel]

/-- **The morphism of complexes `M[-(n+1)] ⟶ Tot Č(𝒰, K)`** given by the Čech cocycle of the
local maps and the homotopies. -/
def cechMap : (HomologicalComplex.single V.Modules (up ℤ) (n + 1)).obj M ⟶ cechTotal U K :=
  HomologicalComplex.mkHomFromSingle D.cechCocycle D.cechCocycle_d

/-- In degree `n + 1`, `cechMap` is the Čech cocycle `cechCocycle`. -/
theorem cechMap_f : D.cechMap.f (n + 1) =
    (HomologicalComplex.singleObjXSelf (up ℤ) (n + 1) M).hom ≫ D.cechCocycle :=
  HomologicalComplex.mkHomFromSingle_f _ _

/-- The morphism `M ⟶ ℋ^{n+1}(K)` induced on cohomology sheaves. -/
def homologyMap (hU : ⨆ i, U i = ⊤) (a : ℤ) [K.IsStrictlyGE a] :
    M ⟶ K.homology (n + 1) :=
  haveI := quasiIso_toCechTotal hU K a
  (HomologicalComplex.singleObjHomologySelfIso (up ℤ) (n + 1) M).inv ≫
    HomologicalComplex.homologyMap D.cechMap (n + 1) ≫
      inv (HomologicalComplex.homologyMap (toCechTotal U K) (n + 1))

/-- On an open `W ⊆ U α`, the Čech `0`-cochain of the local maps is the augmentation of a cycle
`z` restricting to `f α s`, plus the differential of a `0`-cochain `Y` restricting to the
homotopies `h α _`. -/
theorem cechF_app_eq_cechAugBi_add_d {α : ι} {W : V.Opens} (hW : W ≤ U α) (s : Γ(M, W))
    (z : Γ(K.cycles (n + 1), W))
    (hz : ((D.f α).app W s).down = (K.X (n + 1)).presheaf.map
      (homOfLE (inf_le_left : W ⊓ U α ≤ W)).op ((K.iCycles (n + 1)).app W z))
    (Y : Γ(((cechBicomplex U K).X n).X ((0 : ℕ) : ℤ), W))
    (hY : ∀ x : Fin 1 → ι, ((((cechDiagramOpens V).obj (K.X n)).map (homOfLE
      (le_inter (U := U) (x := x) fun a => (inf_le_right : U α ⊓ U (x 0) ≤ U (x 0)).trans
        (le_of_eq (congrArg (fun i => U (x i)) (Subsingleton.elim 0 a))))).op).app W
      ((cechBiπ K n 0 x).app W Y)) = (D.h α (x 0)).app W s) :
    D.cechF.app W s = (cechAugBi K (n + 1)).app W ((K.iCycles (n + 1)).app W z) +
      (((cechBicomplex U K).d n (n + 1)).f ((0 : ℕ) : ℤ)).app W Y := by
  refine cechBi_sections_ext K (n + 1) 0 W _ _ fun x => ?_
  have gx : U α ⊓ U (x 0) ≤ inter U x := le_inter (U := U) (x := x) fun a =>
    (inf_le_right : U α ⊓ U (x 0) ≤ U (x 0)).trans
      (le_of_eq (congrArg (fun i => U (x i)) (Subsingleton.elim (α := Fin 1) 0 a)))
  apply (cechDiagram_map_app_bijective (K.X (n + 1)) (homOfLE gx)
    (le_inf (inf_le_left.trans hW) (inf_le_right.trans (leOfHom (interπ U x 0))))).1
  have hF := congrArg (fun φ => φ.app W s) (toCechBi_cechBiπ K (n + 1) 0 (fun x =>
    D.f (x 0) ≫ ((cechDiagramOpens V).obj (K.X (n + 1))).map (interπ U x 0).op) x)
  have hA := cechAug_π_app (U := U) (K.X (n + 1)) x W ((K.iCycles (n + 1)).app W z)
  have hA' := congrArg (fun φ => φ.app W ((K.iCycles (n + 1)).app W z))
    (cechAugBi_cechBiπ (U := U) K (n + 1) x)
  have hD := congrArg (fun φ => φ.app W Y) (cechBi_d_f_cechBiπ (U := U) K n (n + 1) 0 x)
  have hY' := hY x
  have hS := congrArg (fun φ => φ.app W s) (D.f_sub_f α (x 0))
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    Scheme.Modules.Hom.sub_app, AddCommGrpCat.hom_sub, AddMonoidHom.sub_apply] at hF hA' hD hS
  rw [map_add, map_add]
  let R := (((cechDiagramOpens V).obj (K.X (n + 1))).map (homOfLE gx).op).app W
  have L1 : (R ((cechBiπ K (n + 1) 0 x).app W (D.cechF.app W s))).down =
      (K.X (n + 1)).presheaf.map
        (homOfLE (inf_le_inf_left W inf_le_right : W ⊓ (U α ⊓ U (x 0)) ≤ W ⊓ U (x 0))).op
        ((D.f (x 0)).app W s).down :=
    (congrArg (fun t => (R t).down) hF).trans (presheaf_map_map _ _ _ _)
  have L2 : (R ((cechBiπ K (n + 1) 0 x).app W ((cechAugBi K (n + 1)).app W
      ((K.iCycles (n + 1)).app W z)))).down = (K.X (n + 1)).presheaf.map
        (homOfLE (inf_le_left : W ⊓ (U α ⊓ U (x 0)) ≤ W)).op ((K.iCycles (n + 1)).app W z) :=
    (congrArg (fun t => (R t).down) hA').trans
      ((congrArg (fun t => (K.X (n + 1)).presheaf.map
        (homOfLE (inf_le_inf_left W gx)).op t) hA).trans (presheaf_map_map _ _ _ _))
  have L3 : (R ((cechBiπ K (n + 1) 0 x).app W
      ((((cechBicomplex U K).d n (n + 1)).f ((0 : ℕ) : ℤ)).app W Y))).down =
      (K.d n (n + 1)).app (W ⊓ (U α ⊓ U (x 0))) ((D.h α (x 0)).app W s).down :=
    (congrArg (fun t => (R t).down) hD).trans
      ((app_presheaf_map (K.d n (n + 1)) (homOfLE (inf_le_inf_left W gx)) _).symm.trans
        (congrArg (fun t => (K.d n (n + 1)).app (W ⊓ (U α ⊓ U (x 0))) (ULift.down t)) hY'))
  have L4 : (K.d n (n + 1)).app (W ⊓ (U α ⊓ U (x 0))) ((D.h α (x 0)).app W s).down =
      (K.X (n + 1)).presheaf.map
        (homOfLE (inf_le_inf_left W inf_le_right : W ⊓ (U α ⊓ U (x 0)) ≤ W ⊓ U (x 0))).op
        ((D.f (x 0)).app W s).down - (K.X (n + 1)).presheaf.map
        (homOfLE (inf_le_inf_left W inf_le_left : W ⊓ (U α ⊓ U (x 0)) ≤ W ⊓ U α)).op
        ((D.f α).app W s).down :=
    (congrArg ULift.down hS).symm
  have L5 : (K.X (n + 1)).presheaf.map
        (homOfLE (inf_le_inf_left W inf_le_left : W ⊓ (U α ⊓ U (x 0)) ≤ W ⊓ U α)).op
        ((D.f α).app W s).down = (K.X (n + 1)).presheaf.map
        (homOfLE (inf_le_left : W ⊓ (U α ⊓ U (x 0)) ≤ W)).op ((K.iCycles (n + 1)).app W z) :=
    (congrArg _ hz).trans (presheaf_map_map _ _ _ _)
  refine ULift.ext (L1.trans (Eq.trans ?_ (congrArg₂ (· + ·) L2 L3).symm))
  rw [L4, L5]
  abel

/-- On `W ⊓ (U α ⊓ inter U yy)`, the face `j` of a `0`-cochain `Y` restricting to the homotopies
`h α _` is the restriction of `h α (yy (j.succAbove 0))`. -/
theorem cechBiπ_face_app_down {α : ι} {W : V.Opens} (s : Γ(M, W))
    (Y : Γ(((cechBicomplex U K).X n).X ((0 : ℕ) : ℤ), W))
    (hY : ∀ x : Fin 1 → ι, ((((cechDiagramOpens V).obj (K.X n)).map (homOfLE
      (le_inter (U := U) (x := x) fun a => (inf_le_right : U α ⊓ U (x 0) ≤ U (x 0)).trans
        (le_of_eq (congrArg (fun i => U (x i)) (Subsingleton.elim 0 a))))).op).app W
      ((cechBiπ K n 0 x).app W Y)) = (D.h α (x 0)).app W s)
    (yy : Fin 2 → ι) (j : Fin 2)
    (hA : W ⊓ (U α ⊓ inter U yy) ≤ W ⊓ (U α ⊓ U (yy (j.succAbove 0)))) :
    ((((cechDiagramOpens V).obj (K.X n)).map
      (homOfLE (inf_le_right : U α ⊓ inter U yy ≤ inter U yy)).op).app W
      ((((cechDiagramOpens V).obj (K.X n)).map (interMap U yy (Fin.succAbove j)).op).app W
        ((cechBiπ K n 0 (yy ∘ Fin.succAbove j)).app W Y))).down =
      (K.X n).presheaf.map (homOfLE hA).op ((D.h α (yy (j.succAbove 0))).app W s).down :=
  (presheaf_map_map _ _ (homOfLE (hA.trans (inf_le_inf_left W (le_inter (U := U)
    (x := yy ∘ Fin.succAbove j) fun a =>
      (inf_le_right : U α ⊓ U (yy (j.succAbove 0)) ≤ U (yy (j.succAbove 0))).trans
        (le_of_eq (congrArg (fun i => U ((yy ∘ Fin.succAbove j) i))
          (Subsingleton.elim (α := Fin 1) 0 a))))))) _).trans
    ((presheaf_map_map _ (homOfLE hA) _ _).symm.trans
      (congrArg (fun t => (K.X n).presheaf.map (homOfLE hA).op (ULift.down t))
        (hY (yy ∘ Fin.succAbove j))))

/-- The cocycle condition `h α β + h β γ = h α γ`, restricted to `W ⊓ (U α ⊓ inter U yy)`. -/
theorem h_add_restrict_down {α : ι} {W : V.Opens} (s : Γ(M, W)) (yy : Fin 2 → ι)
    (h0 : inter U yy ≤ U (yy 0)) (h1 : inter U yy ≤ U (yy 1))
    (hA0 : W ⊓ (U α ⊓ inter U yy) ≤ W ⊓ (U α ⊓ U (yy 0)))
    (hA1 : W ⊓ (U α ⊓ inter U yy) ≤ W ⊓ (U α ⊓ U (yy 1)))
    (hA01 : W ⊓ (U α ⊓ inter U yy) ≤ W ⊓ (U (yy 0) ⊓ U (yy 1))) :
    (K.X n).presheaf.map (homOfLE hA0).op ((D.h α (yy 0)).app W s).down +
      (K.X n).presheaf.map (homOfLE hA01).op ((D.h (yy 0) (yy 1)).app W s).down =
      (K.X n).presheaf.map (homOfLE hA1).op ((D.h α (yy 1)).app W s).down := by
  have T : U α ⊓ inter U yy ≤ U α ⊓ U (yy 0) ⊓ U (yy 1) :=
    le_inf (inf_le_inf_left _ h0) (inf_le_right.trans h1)
  have hS2 := congrArg (fun φ => φ.app W s) (D.h_add α (yy 0) (yy 1))
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    Scheme.Modules.Hom.add_app, AddCommGrpCat.hom_add, AddMonoidHom.add_apply] at hS2
  have C := congrArg (fun t => ((((cechDiagramOpens V).obj (K.X n)).map
    (homOfLE T).op).app W t).down) hS2
  simp only [map_add] at C
  exact (congrArg₂ (· + ·) (presheaf_map_map _ _ _ _) (presheaf_map_map _ _ _ _)).symm.trans
    (C.trans (presheaf_map_map _ _ _ _))

/-- On an open `W ⊆ U α`, the Čech `1`-cochain of the homotopies is the Čech differential of a
`0`-cochain `Y` restricting to the homotopies `h α _`. -/
theorem cechH_app_eq_d {α : ι} {W : V.Opens} (hW : W ≤ U α) (s : Γ(M, W))
    (Y : Γ(((cechBicomplex U K).X n).X ((0 : ℕ) : ℤ), W))
    (hY : ∀ x : Fin 1 → ι, ((((cechDiagramOpens V).obj (K.X n)).map (homOfLE
      (le_inter (U := U) (x := x) fun a => (inf_le_right : U α ⊓ U (x 0) ≤ U (x 0)).trans
        (le_of_eq (congrArg (fun i => U (x i)) (Subsingleton.elim 0 a))))).op).app W
      ((cechBiπ K n 0 x).app W Y)) = (D.h α (x 0)).app W s) :
    D.cechH.app W s = (((cechBicomplex U K).X n).d ((0 : ℕ) : ℤ) ((1 : ℕ) : ℤ)).app W Y := by
  refine cechBi_sections_ext K n 1 W _ _ fun yy => ?_
  have h0 : inter U yy ≤ U (yy 0) := leOfHom (interπ U yy 0)
  have h1 : inter U yy ≤ U (yy 1) := leOfHom (interπ U yy 1)
  apply (cechDiagram_map_app_bijective (K.X n)
    (homOfLE (inf_le_right : U α ⊓ inter U yy ≤ inter U yy))
    (le_inf (inf_le_left.trans hW) inf_le_right : W ⊓ inter U yy ≤ U α ⊓ inter U yy)).1
  let R := (((cechDiagramOpens V).obj (K.X n)).map
    (homOfLE (inf_le_right : U α ⊓ inter U yy ≤ inter U yy)).op).app W
  have hHh := congrArg (fun φ => φ.app W s) (toCechBi_cechBiπ K n 1 (fun x =>
    D.h (x 0) (x 1) ≫ ((cechDiagramOpens V).obj (K.X n)).map
      (homOfLE (le_inf (leOfHom (interπ U x 0)) (leOfHom (interπ U x 1)))).op) yy)
  have hD0 := cechBi_X_d_cechBiπ (U := U) K n 0 yy
  rw [Fin.sum_univ_two] at hD0
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul,
    ← sub_eq_add_neg] at hD0
  have hD := congrArg (fun φ => φ.app W Y) hD0
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    Scheme.Modules.Hom.sub_app, AddCommGrpCat.hom_sub, AddMonoidHom.sub_apply] at hHh hD
  have hA0 : W ⊓ (U α ⊓ inter U yy) ≤ W ⊓ (U α ⊓ U (yy 0)) :=
    inf_le_inf_left W (inf_le_inf_left _ h0)
  have hA1 : W ⊓ (U α ⊓ inter U yy) ≤ W ⊓ (U α ⊓ U (yy 1)) :=
    inf_le_inf_left W (inf_le_inf_left _ h1)
  have hA01 : W ⊓ (U α ⊓ inter U yy) ≤ W ⊓ (U (yy 0) ⊓ U (yy 1)) :=
    inf_le_inf_left W (inf_le_right.trans (le_inf h0 h1))
  have M1 : (R ((cechBiπ K n 1 yy).app W (D.cechH.app W s))).down =
      (K.X n).presheaf.map (homOfLE hA01).op ((D.h (yy 0) (yy 1)).app W s).down :=
    (congrArg (fun t => (R t).down) hHh).trans (presheaf_map_map _ _ _ _)
  have N0 : (R ((((cechDiagramOpens V).obj (K.X n)).map
      (interMap U yy (Fin.succAbove 0)).op).app W
        ((cechBiπ K n 0 (yy ∘ Fin.succAbove 0)).app W Y))).down =
      (K.X n).presheaf.map (homOfLE hA1).op ((D.h α (yy 1)).app W s).down :=
    D.cechBiπ_face_app_down s Y hY yy 0 hA1
  have N1 : (R ((((cechDiagramOpens V).obj (K.X n)).map
      (interMap U yy (Fin.succAbove 1)).op).app W
        ((cechBiπ K n 0 (yy ∘ Fin.succAbove 1)).app W Y))).down =
      (K.X n).presheaf.map (homOfLE hA0).op ((D.h α (yy 0)).app W s).down :=
    D.cechBiπ_face_app_down s Y hY yy 1 hA0
  have E : (R ((cechBiπ K n 1 yy).app W
      ((((cechBicomplex U K).X n).d ((0 : ℕ) : ℤ) ((1 : ℕ) : ℤ)).app W Y))).down =
      (K.X n).presheaf.map (homOfLE hA1).op ((D.h α (yy 1)).app W s).down -
        (K.X n).presheaf.map (homOfLE hA0).op ((D.h α (yy 0)).app W s).down :=
    (congrArg (fun t => (R t).down) hD).trans
      ((congrArg ULift.down (map_sub (ConcreteCategory.hom R) _ _)).trans
        (congrArg₂ (· - ·) N0 N1))
  have C' := D.h_add_restrict_down s yy h0 h1 hA0 hA1 hA01
  refine ULift.ext (M1.trans (Eq.trans ?_ E.symm))
  rw [← C']
  abel

/-- On an open `W ⊆ U α`, there is a `0`-cochain of `K^n` restricting to the homotopies
`h α _`. -/
theorem exists_cechBi_restrict_eq_h {α : ι} {W : V.Opens} (hW : W ≤ U α) (s : Γ(M, W)) :
    ∃ Y : Γ(((cechBicomplex U K).X n).X ((0 : ℕ) : ℤ), W), ∀ x : Fin 1 → ι,
      ((((cechDiagramOpens V).obj (K.X n)).map (homOfLE
        (le_inter (U := U) (x := x) fun a => (inf_le_right : U α ⊓ U (x 0) ≤ U (x 0)).trans
          (le_of_eq (congrArg (fun i => U (x i)) (Subsingleton.elim 0 a))))).op).app W
        ((cechBiπ K n 0 x).app W Y)) = (D.h α (x 0)).app W s := by
  have hR : ∀ x : Fin 1 → ι, Function.Bijective
      ((((cechDiagramOpens V).obj (K.X n)).map (homOfLE (le_inter (U := U) (x := x)
        fun a => (inf_le_right : U α ⊓ U (x 0) ≤ U (x 0)).trans
          (le_of_eq (congrArg (fun i => U (x i)) (Subsingleton.elim 0 a))))).op).app W) :=
    fun x => cechDiagram_map_app_bijective _ _ (le_inf (inf_le_left.trans hW)
      (inf_le_right.trans (leOfHom (interπ U x 0))))
  obtain ⟨Y, hY⟩ := cechBi_sections_exists (U := U) K n 0 W
    fun x => ((hR x).2 ((D.h α (x 0)).app W s)).choose
  exact ⟨Y, fun x => by
    rw [hY x]
    exact ((hR x).2 _).choose_spec⟩

/-- On an open `W ⊆ U α`, the Čech cocycle of the local maps is the image of a cycle `z`
restricting to `f α s`, plus a coboundary. -/
theorem cechCocycle_app_eq {α : ι} {W : V.Opens} (hW : W ≤ U α) (s : Γ(M, W))
    (z : Γ(K.cycles (n + 1), W))
    (hz : ((D.f α).app W s).down = (K.X (n + 1)).presheaf.map
      (homOfLE (inf_le_left : W ⊓ U α ≤ W)).op ((K.iCycles (n + 1)).app W z))
    (Y : Γ(((cechBicomplex U K).X n).X ((0 : ℕ) : ℤ), W))
    (hY : ∀ x : Fin 1 → ι, ((((cechDiagramOpens V).obj (K.X n)).map (homOfLE
      (le_inter (U := U) (x := x) fun a => (inf_le_right : U α ⊓ U (x 0) ≤ U (x 0)).trans
        (le_of_eq (congrArg (fun i => U (x i)) (Subsingleton.elim 0 a))))).op).app W
      ((cechBiπ K n 0 x).app W Y)) = (D.h α (x 0)).app W s) :
    D.cechCocycle.app W s = ((toCechTotal U K).f (n + 1)).app W
      ((K.iCycles (n + 1)).app W z) + ((cechTotal U K).d n (n + 1)).app W
        (((cechBicomplex U K).ιTotal (up ℤ) n ((0 : ℕ) : ℤ) n (by simp)).app W Y) := by
  have hd : (cechBicomplex U K).ιTotal (up ℤ) n ((0 : ℕ) : ℤ) n (by simp) ≫
      (cechTotal U K).d n (n + 1) = ((cechBicomplex U K).d n (n + 1)).f ((0 : ℕ) : ℤ) ≫
        (cechBicomplex U K).ιTotal (up ℤ) (n + 1) ((0 : ℕ) : ℤ) (n + 1) (by simp) +
      (n.negOnePow : ℤ) • (((cechBicomplex U K).X n).d ((0 : ℕ) : ℤ) ((1 : ℕ) : ℤ) ≫
        (cechBicomplex U K).ιTotal (up ℤ) n ((1 : ℕ) : ℤ) (n + 1) (by simp)) := by
    rw [StacksDraft.TotalSingleRow.ιTotal_d_up_ℤ' _ n (n + 1) ((0 : ℕ) : ℤ) ((1 : ℕ) : ℤ) n
      (n + 1) rfl (by simp) (by simp) rfl, Units.smul_def]
  have hf : (toCechTotal U K).f (n + 1) = cechAugBi K (n + 1) ≫
      (cechBicomplex U K).ιTotal (up ℤ) (n + 1) ((0 : ℕ) : ℤ) (n + 1) (by simp) := rfl
  have hd' := congrArg (fun φ => φ.app W Y) hd
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    Scheme.Modules.Hom.add_app, zsmul_app_apply, AddCommGrpCat.hom_add,
    AddMonoidHom.add_apply] at hd'
  rw [hf, cechCocycle]
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    Scheme.Modules.Hom.add_app, zsmul_app_apply, AddCommGrpCat.hom_add, AddMonoidHom.add_apply]
  rw [D.cechF_app_eq_cechAugBi_add_d hW s z hz Y hY, D.cechH_app_eq_d hW s Y hY, map_add, hd',
    add_assoc]

/-- **The cohomology map is induced by the local maps.** On an open `W` inside a member `U α`
of the cover, `homologyMap` sends a section `s` of `M` to the class of any cycle `z` of `K^{n+1}`
whose restriction to `W ⊓ U α` is `f α s`. -/
theorem homologyMap_app_eq (hU : ⨆ i, U i = ⊤) (a : ℤ) [K.IsStrictlyGE a] (α : ι)
    {W : V.Opens} (hW : W ≤ U α) (s : Γ(M, W)) (z : Γ(K.cycles (n + 1), W))
    (hz : ((D.f α).app W s).down = (K.X (n + 1)).presheaf.map
      (homOfLE (inf_le_left : W ⊓ U α ≤ W)).op ((K.iCycles (n + 1)).app W z)) :
    (D.homologyMap hU a).app W s = (K.homologyπ (n + 1)).app W z := by
  have hq := quasiIso_toCechTotal hU K a
  have hH : IsIso (HomologicalComplex.homologyMap (toCechTotal U K) (n + 1)) :=
    (quasiIsoAt_iff_isIso_homologyMap _ _).1 (hq.quasiIsoAt _)
  obtain ⟨Y, hYx⟩ := D.exists_cechBi_restrict_eq_h hW s
  let y : Γ((cechTotal U K).X n, W) :=
    ((cechBicomplex U K).ιTotal (up ℤ) n ((0 : ℕ) : ℤ) n (by simp)).app W Y
  have hcore := D.cechCocycle_app_eq hW s z hz Y hYx
  have m1 : (HomologicalComplex.singleObjCyclesSelfIso (up ℤ) (n + 1) M).inv ≫
      HomologicalComplex.cyclesMap D.cechMap (n + 1) ≫ (cechTotal U K).iCycles (n + 1) =
        D.cechCocycle := by
    rw [HomologicalComplex.cyclesMap_i, HomologicalComplex.singleObjCyclesSelfIso_inv_iCycles_assoc,
      cechMap_f, Iso.inv_hom_id_assoc]
  have m2 := HomologicalComplex.cyclesMap_i (toCechTotal U K) (n + 1)
  have m3 := (cechTotal U K).toCycles_i n (n + 1)
  have m4 := (cechTotal U K).toCycles_comp_homologyπ n (n + 1)
  have e1 : D.homologyMap hU a ≫ HomologicalComplex.homologyMap (toCechTotal U K) (n + 1) =
      (HomologicalComplex.singleObjCyclesSelfIso (up ℤ) (n + 1) M).inv ≫
        HomologicalComplex.cyclesMap D.cechMap (n + 1) ≫ (cechTotal U K).homologyπ (n + 1) := by
    simp only [homologyMap, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    rw [← HomologicalComplex.singleObjCyclesSelfIso_inv_homologyπ, Category.assoc,
      HomologicalComplex.homologyπ_naturality]
  have e2 := HomologicalComplex.homologyπ_naturality (toCechTotal U K) (n + 1)
  have hw : (HomologicalComplex.cyclesMap D.cechMap (n + 1)).app W
      ((HomologicalComplex.singleObjCyclesSelfIso (up ℤ) (n + 1) M).inv.app W s) =
      (HomologicalComplex.cyclesMap (toCechTotal U K) (n + 1)).app W z +
        ((cechTotal U K).toCycles n (n + 1)).app W y := by
    apply app_injective_of_mono ((cechTotal U K).iCycles (n + 1)) W
    have h1 := congrArg (fun φ => φ.app W s) m1
    have h2 := congrArg (fun φ => φ.app W z) m2
    have h3 := congrArg (fun φ => φ.app W y) m3
    simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at h1 h2 h3
    rw [map_add, h1, h2, h3, hcore]
  apply (ConcreteCategory.bijective_of_isIso
    ((HomologicalComplex.homologyMap (toCechTotal U K) (n + 1)).app W)).1
  have h1 := congrArg (fun φ => φ.app W s) e1
  have h2 := congrArg (fun φ => φ.app W z) e2
  have h4 := congrArg (fun φ => φ.app W y) m4
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    Scheme.Modules.Hom.zero_app] at h1 h2 h4
  rw [h1, h2, hw, map_add, h4]
  simp

variable [HasDerivedCategory.{w} V.Modules]

/-- **The morphism `M[-(n+1)] ⟶ K` in the derived category** glued from the local maps: the
morphism of complexes `M[-(n+1)] ⟶ Tot Č(𝒰, K)` followed by the inverse of the
quasi-isomorphism `K ⟶ Tot Č(𝒰, K)`. -/
def derivedMap (hU : ⨆ i, U i = ⊤) (a : ℤ) [K.IsStrictlyGE a] :
    (DerivedCategory.singleFunctor V.Modules (n + 1)).obj M ⟶ DerivedCategory.Q.obj K :=
  haveI := (DerivedCategory.isIso_Q_map_iff_quasiIso _ (toCechTotal U K)).2
    (quasiIso_toCechTotal hU K a)
  (DerivedCategory.singleFunctorIsoCompQ V.Modules (n + 1)).hom.app M ≫
    DerivedCategory.Q.map D.cechMap ≫ inv (DerivedCategory.Q.map (toCechTotal U K))

/-- **The cohomology of the glued morphism** is `homologyMap`, up to the canonical
identifications. -/
theorem homologyFunctor_map_derivedMap (hU : ⨆ i, U i = ⊤) (a : ℤ) [K.IsStrictlyGE a] :
    (DerivedCategory.homologyFunctor V.Modules (n + 1)).map (D.derivedMap hU a) =
      (homologySingleIso (n + 1) M).hom ≫ D.homologyMap hU a ≫
        ((DerivedCategory.homologyFunctorFactors V.Modules (n + 1)).app K).inv := by
  have hq := quasiIso_toCechTotal hU K a
  have := (DerivedCategory.isIso_Q_map_iff_quasiIso _ (toCechTotal U K)).2 hq
  have hH : IsIso (HomologicalComplex.homologyMap (toCechTotal U K) (n + 1)) :=
    (quasiIsoAt_iff_isIso_homologyMap _ _).1 (hq.quasiIsoAt _)
  rw [← cancel_mono ((DerivedCategory.homologyFunctorFactors V.Modules (n + 1)).app K).hom]
  simp only [derivedMap, homologySingleIso, homologyMap, Functor.map_comp, Category.assoc,
    Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  congr 1
  have h1 : (DerivedCategory.homologyFunctor V.Modules (n + 1)).map
      (inv (DerivedCategory.Q.map (toCechTotal U K))) ≫
        (DerivedCategory.homologyFunctorFactors V.Modules (n + 1)).hom.app K =
      (DerivedCategory.homologyFunctorFactors V.Modules (n + 1)).hom.app (cechTotal U K) ≫
        (inv (HomologicalComplex.homologyMap (toCechTotal U K) (n + 1)) :
          (cechTotal U K).homology (n + 1) ⟶ K.homology (n + 1)) := by
    rw [Functor.map_inv]
    refine (IsIso.inv_comp_eq _).2 ?_
    erw [DerivedCategory.homologyFunctorFactors_hom_naturality_assoc, IsIso.hom_inv_id,
      Category.comp_id]
  erw [h1, DerivedCategory.homologyFunctorFactors_hom_naturality_assoc]
  exact iso_comp_aux (C := V.Modules)
    ((DerivedCategory.homologyFunctorFactors V.Modules (n + 1)).app
      ((CochainComplex.singleFunctor V.Modules (n + 1)).obj M))
    (HomologicalComplex.singleObjHomologySelfIso (up ℤ) (n + 1) M)
    (HomologicalComplex.homologyMap D.cechMap (n + 1) ≫
      inv (HomologicalComplex.homologyMap (toCechTotal U K) (n + 1)))
    ((DerivedCategory.homologyFunctorFactors V.Modules (n + 1)).app K)

end CechGluingData

end MMP.DeRham
