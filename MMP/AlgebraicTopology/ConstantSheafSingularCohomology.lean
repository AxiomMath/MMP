module

public import MMP.Topology.Sheaves.Godement
public import MMP.AlgebraicTopology.SingularCohomology.Relative.Excision
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.CategoryTheory.Sites.LocalSite
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.EMetricSpace.Paracompact
public import Mathlib.Topology.GDelta.MetrizableSpace
public import Mathlib.Topology.Homotopy.LocallyContractible
public import Mathlib.Topology.Sheaves.Flasque
public import Mathlib.Topology.Sheaves.Sheafify
public import Mathlib.Topology.ShrinkingLemma

/-!
# Constant-sheaf cohomology and singular cohomology of locally contractible metrizable spaces

Let `M` be a metrizable, locally contractible topological space and let `A` be an abelian group.
The cohomology `H^n(M, A_M)` of the constant sheaf `A_M` is isomorphic to the singular cohomology
`H^n_sing(M; A) = H^n(Hom(C_•(M; ℤ), A))`. The isomorphisms are natural for continuous maps
`f : N → M` between such spaces: on the sheaf side, `f` acts by the pullback
`H^n(M, A_M) ⟶ H^n(N, f⁻¹ A_M)`, followed by the canonical map `f⁻¹ A_M ⟶ A_N`. That map is the
adjunct of `A ⟶ Γ(N, A_N) ⟶ Γ(f⁻¹ M, A_N)` under the composite adjunction
`f⁻¹ ∘ (-)_M ⊣ Γ(M, -) ∘ f_*`. On the singular side, `f` acts by the pullback of cochains.

## Main results

* `MMP.Analytic.exists_sheafCohomology_constantSheaf_iso_singularCohomology`: the natural
  isomorphism `H^n(M, A_M) ≅ H^n_sing(M; A)`.
* `MMP.Analytic.exists_sheafCohomology_constantSheaf_iso_singularCohomology_natural`: the same
  isomorphisms, natural also in the coefficient group `A`.

## Implementation notes

* Sheaf cohomology is `MMP.Analytic.sheafCohomology`, computed by the Godement resolution, and
  its functoriality in the space is `MMP.Analytic.sheafCohomologyPullback`.
* Singular cohomology with coefficients in the abelian group `A` is the cohomology of the cochain
  complex `Hom(C_•(M; ℤ), A)`. Here `C_•(M; ℤ)` is Mathlib's `singularChainComplexFunctor` with
  coefficients `ℤ`, and `Hom(-, A)` is `preadditiveYoneda.obj A`. Both are functorial, so the
  pullback along `f` is `map f.op` of the resulting functor `TopCat.{u}ᵒᵖ ⥤ AddCommGrpCat.{u}`.
* Local contractibility is Mathlib's classical `LocallyContractibleSpace`. Every neighbourhood
  `U` of a point contains a neighbourhood `V` whose inclusion into `U` is null-homotopic. This is
  weaker than having a basis of contractible neighbourhoods (`StronglyLocallyContractibleSpace`).
  It suffices because the stalks of the sheafified singular cochain complex are colimits along
  such inclusions, and those inclusions induce zero on reduced singular cohomology.
* The proof follows the classical route. The sheafified singular cochains `𝒮^•` resolve `A_M`
  (exactness on stalks is local contractibility) by flasque sheaves (singular cochains glue along
  a locally finite shrinking of a cover, which uses paracompactness of metrizable spaces). A
  flasque resolution computes Godement cohomology: the double complex `Γ(M, G^q(𝒮^p))` has exact
  rows and columns, so both augmentations into its total complex are quasi-isomorphisms. Finally
  `Γ(M, 𝒮^•)` is quasi-isomorphic to the singular cochains by small-chains acyclicity. Naturality
  comes from making every step functorial in explicit morphisms `𝒮_M^• ⟶ f_* 𝒮_N^•`.
-/

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicTopology Metric

universe u u' v'

namespace MMP.Analytic

noncomputable section

namespace SingularComparison

private lemma exact_cokernel_comp_mono {C : Type u'} [Category.{v'} C] [Abelian C] {A B D : C} (f :
    A ⟶ B) (i : cokernel f ⟶ D) [Mono i] :
    (ShortComplex.mk f (cokernel.π f ≫ i) (by simp)).Exact := by
  have h1 : (ShortComplex.mk f (cokernel.π f) (by simp)).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f)
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono (S₁ := ShortComplex.mk f (cokernel.π f)
      (by simp))
    (S₂ := ShortComplex.mk f (cokernel.π f ≫ i) (by simp)) ⟨𝟙 _, 𝟙 _, i, by simp, by simp⟩).1 h1

open Limits CokernelCoresolution in
private lemma quasiIso_augmentation {C : Type u'} [Category.{v'} C] [Abelian C] (G : C ⥤ C) (η : 𝟭 C
    ⟶ G)
    [∀ X, Mono (η.app X)] (F : C) : QuasiIso (augmentation G η F) := by
  refine ⟨fun n => ?_⟩
  cases n with
  | zero =>
    rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
    · refine (ShortComplex.exact_and_mono_f_iff_of_iso ?_).2
        ⟨exact_cokernel_comp_mono (η.app F) (η.app (cokernel (η.app F))), by dsimp; infer_instance⟩
      exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by
          dsimp
          simp only [HomologicalComplex.shortComplexFunctor'_map_τ₂, augmentation_f_zero,
              CochainComplex.single₀_obj_zero, CochainComplex.single₀ObjXSelf, Iso.refl_hom,
              Category.id_comp]
          erw [Category.comp_id])
        (by
          dsimp
          simp only [HomologicalComplex.shortComplexFunctor'_obj_g, complex_d, d_zero,
              Functor.id_obj]
          erw [Category.id_comp, Category.comp_id])
    all_goals rfl
  | succ n =>
    rw [quasiIsoAt_iff_exactAt _ _ (CochainComplex.exactAt_succ_single_obj _ _)]
    rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)]
    have h := exact_cokernel_comp_mono (d G η F n) (η.app (cokernel (d G η F n)))
    refine (ShortComplex.exact_iff_of_iso ?_).2 h
    exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by
        dsimp
        simp only [HomologicalComplex.shortComplexFunctor'_obj_f, complex_d]
        erw [Category.id_comp, Category.comp_id])
      (by
        dsimp
        simp only [HomologicalComplex.shortComplexFunctor'_obj_g, complex_d, d_succ]
        erw [Category.id_comp, Category.comp_id])

private instance mono_godementUnit {T : TopCat.{u}} (F : TopCat.Sheaf AddCommGrpCat.{u} T) :
    Mono ((godementUnit T).app F) :=
  CategoryTheory.Sheaf.mono_of_injective _ (godementUnit_app_hom_app_injective F)

/-- The Godement resolution is a resolution (exact on stalks). -/
private theorem godementAugmentation_quasiIso (T : TopCat.{u}) (F : TopCat.Sheaf AddCommGrpCat.{u}
    T) :
    QuasiIso (godementAugmentation T F) :=
  quasiIso_augmentation (godementFunctor T) (godementUnit T) F

/-- The Godement sheaf is flasque. -/
private lemma isFlasque_godementFunctor {T : TopCat.{u}} (F : TopCat.Sheaf AddCommGrpCat.{u} T) :
    TopCat.Presheaf.IsFlasque ((godementFunctor T).obj F).obj where
  epi {U V} i := by
    rw [AddCommGrpCat.epi_iff_surjective]
    classical
    intro s
    let s' : (x : U.unop) → F.presheaf.stalk x := fun x =>
      if h : x.1 ∈ V.unop then s ⟨x.1, h⟩ else 0
    refine ⟨s', ?_⟩
    funext x
    have : (i.unop x).1 ∈ V.unop := x.2
    change s' (i.unop x) = s x
    simp [s']

section Flasque

variable {T : TopCat.{u}}

private instance preservesLimits_globalSections {T : TopCat.{u}} : PreservesLimitsOfSize.{u,u}
    (globalSections T) :=
  inferInstanceAs (PreservesLimitsOfSize.{u,u} (sheafToPresheaf (Opens.grothendieckTopology T)
      AddCommGrpCat.{u} ⋙ (evaluation _ _).obj (op ⊤)))

private lemma isFlasque_of_iso {A B : TopCat.Sheaf AddCommGrpCat.{u} T} (e : A ≅ B)
    (hA : TopCat.Presheaf.IsFlasque A.obj) : TopCat.Presheaf.IsFlasque B.obj where
  epi {U V} i := by
    have hA' := hA.epi i
    let ε := (sheafToPresheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}).mapIso e
    have : Epi (ε.hom.app U ≫ B.obj.map i) := by
      have h : ε.hom.app U ≫ B.obj.map i = A.obj.map i ≫ ε.hom.app V := (ε.hom.naturality i).symm
      rw [h]
      infer_instance
    exact epi_of_epi (ε.hom.app U) _

private lemma ses_kernel {C : Type*} [Category C] [Abelian C] (E : CochainComplex C ℕ) (p : ℕ)
    (hE : E.ExactAt (p + 1)) :
    (ShortComplex.mk (kernel.ι (E.d p (p + 1))) (kernel.lift (E.d (p + 1) (p + 2)) (E.d p (p + 1))
      (E.d_comp_d _ _ _)) (by ext; simp)).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ inferInstance ((ShortComplex.exact_iff_epi_kernel_lift _).1
    ((E.exactAt_iff' p (p + 1) (p + 2) (by simp) (by simp)).1 hE))
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono (S₁ := ShortComplex.mk (kernel.ι (E.d p (p +
      1))) (kernel.lift (E.d (p + 1) (p + 2)) (E.d p (p + 1))
      (E.d_comp_d _ _ _)) (by ext; simp)) (S₂ := ShortComplex.mk (kernel.ι (E.d p (p + 1))) (E.d p
          (p + 1)) (by simp))
      ⟨𝟙 _, 𝟙 _, kernel.ι (E.d (p + 1) (p + 2)), by simp, by simp⟩).2
    (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _))

private lemma isFlasque_kernel_zero (F : TopCat.Sheaf AddCommGrpCat.{u} T) (hF :
    TopCat.Presheaf.IsFlasque F.obj)
    (E : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℕ)
    (ι : (CochainComplex.single₀ _).obj F ⟶ E) [QuasiIso ι] :
    TopCat.Presheaf.IsFlasque (kernel (E.d 0 1)).obj := by
  obtain ⟨hex, hmono⟩ := (ShortComplex.quasiIso_iff_of_zeros _ rfl rfl
    (by show E.d 0 0 = 0; exact E.shape _ _ (by simp))).1
    ((CochainComplex.quasiIsoAt₀_iff ι).1 (QuasiIso.quasiIsoAt (f := ι) 0))
  let e := IsLimit.conePointUniqueUpToIso hex.fIsKernel (kernelIsKernel (E.d 0 1))
  exact isFlasque_of_iso (show F ≅ kernel (E.d 0 1) from e) hF

private lemma isFlasque_kernel' (E : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℕ)
    (h0 : TopCat.Presheaf.IsFlasque (kernel (E.d 0 1)).obj) (hex : ∀ i, E.ExactAt (i + 1))
    (hE : ∀ p, TopCat.Presheaf.IsFlasque (E.X p).obj) (p : ℕ) :
    TopCat.Presheaf.IsFlasque (kernel (E.d p (p + 1))).obj := by
  induction p with
  | zero => exact h0
  | succ p ih =>
    have hs := ses_kernel E p (hex p)
    have := ih
    have := hE p
    exact TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂ hs

/-- Global sections are exact in positive degrees on an exact complex of flasque sheaves whose
first kernel is flasque. -/
private theorem exactAt_globalSections_of_flasque' (E : CochainComplex (TopCat.Sheaf
    AddCommGrpCat.{u} T) ℕ)
    (h0 : TopCat.Presheaf.IsFlasque (kernel (E.d 0 1)).obj) (hex : ∀ i, E.ExactAt (i + 1))
    (hE : ∀ p, TopCat.Presheaf.IsFlasque (E.X p).obj) (i : ℕ) :
    (((globalSections T).mapHomologicalComplex _).obj E).ExactAt (i + 1) := by
  have hs := ses_kernel E i (hex i)
  have := isFlasque_kernel' E h0 hex hE i
  have hepi : Epi ((globalSections T).map (kernel.lift (E.d (i + 1) (i + 2)) (E.d i (i + 1))
      (E.d_comp_d _ _ _))) :=
    TopCat.Sheaf.IsFlasque.epi_of_shortExact (U := ⊤) hs
  rw [HomologicalComplex.exactAt_iff' _ i (i + 1) (i + 2) (by simp) (by simp)]
  have hS2 : (ShortComplex.mk (kernel.ι (E.d (i + 1) (i + 2))) (E.d (i + 1) (i + 2))
      (by simp)).Exact :=
    ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)
  have hS2' := hS2.map_of_mono_of_preservesKernel (globalSections T) inferInstance inferInstance
  let φ : (((globalSections T).mapHomologicalComplex _).obj E).sc' i (i + 1) (i + 2) ⟶
      (ShortComplex.mk (kernel.ι (E.d (i + 1) (i + 2))) (E.d (i + 1) (i + 2)) (by simp)).map
          (globalSections T) :=
    ⟨(globalSections T).map (kernel.lift (E.d (i + 1) (i + 2)) (E.d i (i + 1)) (E.d_comp_d _ _ _)),
        𝟙 _, 𝟙 _, by
      dsimp
      erw [Category.comp_id, ← Functor.map_comp]
      simp, by dsimp; rfl⟩
  have : Epi φ.τ₁ := hepi
  have : IsIso φ.τ₂ := inferInstanceAs (IsIso (𝟙 _))
  have : Mono φ.τ₃ := inferInstanceAs (Mono (𝟙 _))
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 hS2'

/-- Global sections are exact on an exact resolution of a flasque sheaf by flasque
sheaves. -/
private theorem exactAt_globalSections_of_flasque_resolution
    (F : TopCat.Sheaf AddCommGrpCat.{u} T) (hF : TopCat.Presheaf.IsFlasque F.obj)
    (E : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℕ)
    (ι : (CochainComplex.single₀ _).obj F ⟶ E) [QuasiIso ι]
    (hE : ∀ p, TopCat.Presheaf.IsFlasque (E.X p).obj) (i : ℕ) :
    (((globalSections T).mapHomologicalComplex _).obj E).ExactAt (i + 1) :=
  exactAt_globalSections_of_flasque' E (isFlasque_kernel_zero F hF E ι) (fun i => by
    rw [← exactAt_iff_of_quasiIsoAt ι (i + 1)]
    exact CochainComplex.exactAt_succ_single_obj _ _) hE i

end Flasque

section Assembly

private lemma ab_quasiIso_of {S₁ S₂ : ShortComplex AddCommGrpCat.{u}} (φ : S₁ ⟶ S₂)
    (hs : ∀ y : S₂.X₂, S₂.g y = 0 → ∃ x : S₁.X₂, S₁.g x = 0 ∧ ∃ t : S₂.X₁, φ.τ₂ x - y = S₂.f t)
    (hi : ∀ x : S₁.X₂, S₁.g x = 0 → (∃ t : S₂.X₁, φ.τ₂ x = S₂.f t) → ∃ s : S₁.X₁, x = S₁.f s) :
    ShortComplex.QuasiIso φ := by
  have hcomm : ∀ x : S₁.X₂, S₂.g (φ.τ₂ x) = φ.τ₃ (S₁.g x) := fun x => by
    simpa using congrArg (fun f => f.hom x) φ.comm₂₃
  have hcomm' : ∀ x : S₁.X₁, φ.τ₂ (S₁.f x) = S₂.f (φ.τ₁ x) := fun x => by
    simpa using (congrArg (fun f => f.hom x) φ.comm₁₂).symm
  let kφ : AddMonoidHom.ker S₁.g.hom →+ AddMonoidHom.ker S₂.g.hom :=
    AddMonoidHom.codRestrict (φ.τ₂.hom.comp (AddMonoidHom.ker S₁.g.hom).subtype) _ (fun x => by
      have := x.2
      simp only [AddMonoidHom.mem_ker] at this ⊢
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddSubgroup.coe_subtype]
      rw [hcomm, this, map_zero])
  have hmap : AddMonoidHom.range S₁.abToCycles ≤
      (AddMonoidHom.range S₂.abToCycles).comap kφ := by
    rintro _ ⟨x, rfl⟩
    exact ⟨φ.τ₁ x, Subtype.ext (hcomm' x).symm⟩
  let γ : ShortComplex.LeftHomologyMapData φ S₁.abLeftHomologyData S₂.abLeftHomologyData :=
    { φK := AddCommGrpCat.ofHom kφ
      φH := AddCommGrpCat.ofHom (QuotientAddGroup.map _ _ kφ hmap)
      commi := rfl
      commf' := by
        refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => ?_)
        exact Subtype.ext (hcomm' x)
      commπ := rfl }
  rw [γ.quasiIso_iff, ConcreteCategory.isIso_iff_bijective]
  refine ⟨?_, fun q => ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro q hq
    induction q using QuotientAddGroup.induction_on with
    | H x =>
      obtain ⟨x, hx⟩ := x
      change QuotientAddGroup.map _ _ kφ hmap (QuotientAddGroup.mk ⟨x, hx⟩) = 0 at hq
      rw [QuotientAddGroup.map_mk, QuotientAddGroup.eq_zero_iff] at hq
      obtain ⟨t, ht⟩ := hq
      obtain ⟨s, hs'⟩ := hi x hx ⟨t, (congrArg Subtype.val ht).symm⟩
      show (QuotientAddGroup.mk ⟨x, hx⟩ : (AddMonoidHom.ker S₁.g.hom) ⧸ AddMonoidHom.range
          S₁.abToCycles) = 0
      rw [QuotientAddGroup.eq_zero_iff]
      exact ⟨s, Subtype.ext hs'.symm⟩
  · induction q using QuotientAddGroup.induction_on with
    | H y =>
      obtain ⟨y, hy⟩ := y
      obtain ⟨x, hx, t, ht⟩ := hs y hy
      refine ⟨QuotientAddGroup.mk ⟨x, hx⟩, ?_⟩
      change QuotientAddGroup.map _ _ kφ hmap (QuotientAddGroup.mk ⟨x, hx⟩) = _
      rw [QuotientAddGroup.map_mk, QuotientAddGroup.eq_iff_sub_mem]
      exact ⟨t, Subtype.ext ht.symm⟩

/-- A first-quadrant double complex of abelian groups. -/
private structure DblCx where
  X : ℕ → ℕ → AddCommGrpCat.{u}
  dh : ∀ p q, X p q ⟶ X (p + 1) q
  dv : ∀ p q, X p q ⟶ X p (q + 1)
  dh_dh : ∀ p q, dh p q ≫ dh (p + 1) q = 0
  dv_dv : ∀ p q, dv p q ≫ dv p (q + 1) = 0
  comm : ∀ p q, dh p q ≫ dv (p + 1) q = dv p q ≫ dh p (q + 1)

namespace DblCx

variable (D : DblCx.{u}) (n : ℕ)

/-- Total degree `n` indices. -/
private abbrev Idx (n : ℕ) := {x : ℕ × ℕ // x.1 + x.2 = n}

/-- Elements of the total complex in degree `n`. -/
private abbrev TotX (n : ℕ) : Type u := (x : Idx n) → D.X x.1.1 x.1.2

private def hPart (z : D.TotX n) : D.TotX (n + 1)
  | ⟨(0, _), _⟩ => 0
  | ⟨(p + 1, q), h⟩ => D.dh p q (z ⟨(p, q), by simp at h ⊢; omega⟩)

private def vPart (z : D.TotX n) : D.TotX (n + 1)
  | ⟨(_, 0), _⟩ => 0
  | ⟨(p, q + 1), h⟩ => (-1 : ℤ) ^ p • D.dv p q (z ⟨(p, q), by simp at h ⊢; omega⟩)

private def dTot (z : D.TotX n) : D.TotX (n + 1) := D.hPart n z + D.vPart n z

end DblCx

namespace DblCx

variable (D : DblCx.{u}) (n : ℕ)

private lemma dh_dh_apply (p q : ℕ) (x : D.X p q) : D.dh (p + 1) q (D.dh p q x) = 0 := by
  have := congrArg (fun f => f.hom x) (D.dh_dh p q)
  simpa using this

private lemma dv_dv_apply (p q : ℕ) (x : D.X p q) : D.dv p (q + 1) (D.dv p q x) = 0 := by
  have := congrArg (fun f => f.hom x) (D.dv_dv p q)
  simpa using this

private lemma comm_apply (p q : ℕ) (x : D.X p q) :
    D.dv (p + 1) q (D.dh p q x) = D.dh p (q + 1) (D.dv p q x) := by
  have := congrArg (fun f => f.hom x) (D.comm p q)
  simpa using this

private lemma hPart_hPart (z : D.TotX n) : D.hPart (n + 1) (D.hPart n z) = 0 := by
  funext ⟨⟨p, q⟩, h⟩
  rcases p with _ | _ | p
  · rfl
  · simp [hPart]
  · simp [hPart, D.dh_dh_apply]

private lemma vPart_vPart (z : D.TotX n) : D.vPart (n + 1) (D.vPart n z) = 0 := by
  funext ⟨⟨p, q⟩, h⟩
  rcases q with _ | _ | q
  · rfl
  · simp [vPart]
  · simp [vPart, D.dv_dv_apply]

end DblCx

namespace DblCx

variable (D : DblCx.{u}) (n : ℕ)

private lemma hPart_vPart_add (z : D.TotX n) :
    D.hPart (n + 1) (D.vPart n z) + D.vPart (n + 1) (D.hPart n z) = 0 := by
  funext ⟨⟨p, q⟩, h⟩
  rcases p with _ | p <;> rcases q with _ | q
  · simp [hPart, vPart]
  · simp [hPart, vPart]
  · simp [hPart, vPart]
  · simp only [hPart, vPart, Pi.add_apply, Pi.zero_apply]
    rw [map_zsmul, D.comm_apply, pow_succ]
    simp
    
private lemma dTot_dTot (z : D.TotX n) : D.dTot (n + 1) (D.dTot n z) = 0 := by
  have h1 : ∀ (m : ℕ) (a b : D.TotX m), D.hPart m (a + b) = D.hPart m a + D.hPart m b := by
    intro m a b; funext ⟨⟨p, q⟩, h⟩; rcases p with _ | p <;> simp [hPart]
  have h2 : ∀ (m : ℕ) (a b : D.TotX m), D.vPart m (a + b) = D.vPart m a + D.vPart m b := by
    intro m a b; funext ⟨⟨p, q⟩, h⟩; rcases q with _ | q <;> simp [vPart, smul_add]
  unfold dTot
  rw [h1, h2, D.hPart_hPart, D.vPart_vPart]
  simp only [zero_add, add_zero]
  exact D.hPart_vPart_add n z

end DblCx

namespace DblCx

variable (D : DblCx.{u})

private lemma dTot_add (n : ℕ) (a b : D.TotX n) : D.dTot n (a + b) = D.dTot n a + D.dTot n b := by
  unfold dTot
  have h1 : D.hPart n (a + b) = D.hPart n a + D.hPart n b := by
    funext ⟨⟨p, q⟩, h⟩; rcases p with _ | p <;> simp [hPart]
  have h2 : D.vPart n (a + b) = D.vPart n a + D.vPart n b := by
    funext ⟨⟨p, q⟩, h⟩; rcases q with _ | q <;> simp [vPart, smul_add]
  rw [h1, h2]; abel

private lemma dTot_zero (n : ℕ) : D.dTot n 0 = 0 := by
  have := D.dTot_add n 0 0
  simpa using this

private lemma dTot_neg (n : ℕ) (a : D.TotX n) : D.dTot n (-a) = - D.dTot n a := by
  have := D.dTot_add n a (-a)
  rw [add_neg_cancel, D.dTot_zero] at this
  exact eq_neg_of_add_eq_zero_right this.symm

private lemma dTot_sub (n : ℕ) (a b : D.TotX n) : D.dTot n (a - b) = D.dTot n a - D.dTot n b := by
  rw [sub_eq_add_neg, D.dTot_add, D.dTot_neg, ← sub_eq_add_neg]

/-- The total complex. -/
private def tot : CochainComplex AddCommGrpCat.{u} ℕ :=
  CochainComplex.of (fun n => AddCommGrpCat.of (D.TotX n))
    (fun n => AddCommGrpCat.ofHom
      { toFun := D.dTot n
        map_zero' := D.dTot_zero n
        map_add' := D.dTot_add n })
    (fun n => by
      refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun z => ?_)
      exact D.dTot_dTot n z)

end DblCx

namespace DblCx

variable (D : DblCx.{u}) (A : CochainComplex AddCommGrpCat.{u} ℕ) (ε : ∀ p, A.X p ⟶ D.X p 0)

/-- The augmentation in total degree `n`: `a ↦ ε a` placed at the component `(n, 0)`. -/
private def augFun (n : ℕ) (a : A.X n) : D.TotX n
  | ⟨(p, 0), h⟩ => ε p (cast (congrArg (fun m => (A.X m : Type u)) (show n = p by simpa using
      h.symm)) a)
  | ⟨(_, _ + 1), _⟩ => 0

end DblCx

namespace DblCx

variable (D : DblCx.{u}) (A : CochainComplex AddCommGrpCat.{u} ℕ) (ε : ∀ p, A.X p ⟶ D.X p 0)

private lemma augFun_succ (n : ℕ) (a : A.X n) (p q : ℕ) (h : p + (q + 1) = n) :
    D.augFun A ε n a ⟨(p, q + 1), h⟩ = 0 := rfl

private lemma augFun_add (n : ℕ) (a b : A.X n) :
    D.augFun A ε n (a + b) = D.augFun A ε n a + D.augFun A ε n b := by
  funext ⟨⟨p, q⟩, h⟩
  rcases q with _ | q
  · simp only [add_zero] at h; subst h
    show ε p (a + b) = ε p a + ε p b
    exact map_add _ _ _
  · simp [augFun_succ]

private lemma augFun_zero (n : ℕ) : D.augFun A ε n 0 = 0 := by
  have := D.augFun_add A ε n 0 0
  simpa using this

end DblCx

namespace DblCx

variable (D : DblCx.{u}) (A : CochainComplex AddCommGrpCat.{u} ℕ) (ε : ∀ p, A.X p ⟶ D.X p 0)

private lemma augFun_ne (n : ℕ) (a : A.X n) (p q : ℕ) (h : p + q = n) (hq : q ≠ 0) :
    D.augFun A ε n a ⟨(p, q), h⟩ = 0 := by
  rcases q with _ | q
  · exact absurd rfl hq
  · rfl

private lemma augFun_d (hd : ∀ p x, ε (p + 1) (A.d p (p + 1) x) = D.dh p 0 (ε p x))
    (hv : ∀ p x, D.dv p 0 (ε p x) = 0) (n : ℕ) (a : A.X n) :
    D.augFun A ε (n + 1) (A.d n (n + 1) a) = D.dTot n (D.augFun A ε n a) := by
  funext ⟨⟨p, q⟩, h⟩
  simp only [dTot, Pi.add_apply]
  rcases q with _ | _ | q
  · simp only [add_zero] at h; subst h
    simp only [hPart, vPart, add_zero]
    exact hd n a
  · simp only [zero_add, Nat.add_right_cancel_iff] at h; subst h
    rw [augFun_succ]
    rcases p with _ | p
    · simp only [Nat.reduceAdd, hPart, vPart, Int.reduceNeg, pow_zero, one_smul, zero_add]
      exact (hv 0 a).symm
    · simp only [Nat.reduceAdd, hPart, vPart, Int.reduceNeg]
      rw [augFun_ne _ _ _ _ _ _ _ _ (by omega)]
      simp only [map_zero, Int.reduceNeg, zero_add]
      have h2 : D.augFun A ε (p + 1) a ⟨(p + 1, 0), rfl⟩ = ε (p + 1) a := rfl
      erw [h2, hv]
      simp
  · rw [augFun_succ]
    rcases p with _ | p
    · simp only [hPart, vPart, Int.reduceNeg, pow_zero, one_smul, zero_add]
      rw [augFun_ne _ _ _ _ _ _ _ _ (by omega)]
      simp
    · simp only [hPart, vPart, Int.reduceNeg]
      rw [augFun_ne _ _ _ _ _ _ _ _ (by omega), augFun_ne _ _ _ _ _ _ _ _ (by omega)]
      simp

end DblCx

namespace DblCx

variable (D : DblCx.{u})

open Classical in
private lemma dTot_single_lt (m k r : ℕ) (hk : k + r = m) (y : D.X k r) (x : Idx (m + 1)) (hx :
    x.1.1 < k) :
    D.dTot m (Pi.single (⟨(k, r), hk⟩ : Idx m) y) x = 0 := by
  obtain ⟨⟨p, q⟩, h⟩ := x
  simp only at hx
  simp only [dTot, Pi.add_apply]
  have h1 : hPart D m (Pi.single (⟨(k, r), hk⟩ : Idx m) y) ⟨(p, q), h⟩ = 0 := by
    rcases p with _ | p
    · rfl
    · simp only [hPart]
      rw [Pi.single_eq_of_ne, map_zero]
      intro hne
      have := congrArg (fun t : Idx m => t.1.1) hne
      simp at this
      omega
  have h2 : vPart D m (Pi.single (⟨(k, r), hk⟩ : Idx m) y) ⟨(p, q), h⟩ = 0 := by
    rcases q with _ | q
    · rfl
    · simp only [vPart]
      rw [Pi.single_eq_of_ne, map_zero, smul_zero]
      intro hne
      have := congrArg (fun t : Idx m => t.1.1) hne
      simp at this
      omega
  rw [h1, h2, add_zero]

end DblCx

namespace DblCx

variable (D : DblCx.{u})

open Classical in
private lemma dTot_single_self (m k r : ℕ) (hk : k + r = m) (y : D.X k r) (h : k + (r + 1) = m + 1)
    :
    D.dTot m (Pi.single (⟨(k, r), hk⟩ : Idx m) y) ⟨(k, r + 1), h⟩ = (-1 : ℤ) ^ k • D.dv k r y := by
  simp only [dTot, Pi.add_apply]
  have h1 : hPart D m (Pi.single (⟨(k, r), hk⟩ : Idx m) y) ⟨(k, r + 1), h⟩ = 0 := by
    rcases k with _ | k
    · rfl
    · simp only [hPart]
      rw [Pi.single_eq_of_ne, map_zero]
      intro hne
      have := congrArg (fun t : Idx m => t.1.2) hne
      simp at this
  have h2 : vPart D m (Pi.single (⟨(k, r), hk⟩ : Idx m) y) ⟨(k, r + 1), h⟩ = (-1 : ℤ) ^ k • D.dv k r
      y := by
    simp only [vPart]
    rw [Pi.single_eq_same]
  rw [h1, h2, zero_add]

end DblCx

namespace DblCx

/-- Augmentation data of a double complex: a complex `A` with maps `ε p : A^p → D^{p,0}`
making every column an exact resolution of `A^p`. -/
private structure AugData (D : DblCx.{u}) where
  A : CochainComplex AddCommGrpCat.{u} ℕ
  ε : ∀ p, A.X p ⟶ D.X p 0
  hd : ∀ p x, ε (p + 1) (A.d p (p + 1) x) = D.dh p 0 (ε p x)
  hv : ∀ p x, D.dv p 0 (ε p x) = 0
  inj : ∀ p, Function.Injective (ε p)
  ex0 : ∀ p (x : D.X p 0), D.dv p 0 x = 0 → ∃ a, ε p a = x
  exS : ∀ p q (x : D.X p (q + 1)), D.dv p (q + 1) x = 0 → ∃ y, D.dv p q y = x

namespace AugData

variable {D : DblCx.{u}} (G : AugData D)

/-- Degree zero surjectivity. -/
private lemma surj_zero (z : D.TotX 0) (hz : D.dTot 0 z = 0) : ∃ a, z = D.augFun G.A G.ε 0 a := by
  have h := congrFun hz ⟨(0, 1), rfl⟩
  simp only [DblCx.dTot, Pi.add_apply, DblCx.hPart, DblCx.vPart] at h
  simp only [Nat.reduceAdd, Int.reduceNeg, pow_zero, one_smul, zero_add, Pi.zero_apply] at h
  obtain ⟨a, ha⟩ := G.ex0 0 (z ⟨(0, 0), rfl⟩) h
  refine ⟨a, ?_⟩
  funext ⟨⟨p, q⟩, hh⟩
  simp only [Nat.add_eq_zero_iff] at hh
  obtain ⟨rfl, rfl⟩ := hh
  exact ha.symm

open Classical in
private lemma surj_step (G : AugData D) (m : ℕ) (z : D.TotX (m + 1)) (hz : D.dTot (m + 1) z = 0) (k
    : ℕ) (hk : k ≤ m)
    (hvan : ∀ x : DblCx.Idx (m + 1), x.1.1 < k → z x = 0) :
    ∃ (z' : D.TotX (m + 1)) (w : D.TotX m), D.dTot (m + 1) z' = 0 ∧ z = z' + D.dTot m w ∧
      ∀ x : DblCx.Idx (m + 1), x.1.1 < k + 1 → z' x = 0 := by
  obtain ⟨r, hr⟩ : ∃ r, k + r = m := ⟨m - k, by omega⟩
  have h1 := congrFun hz ⟨(k, r + 2), by omega⟩
  simp only [DblCx.dTot, Pi.add_apply] at h1
  have hh : DblCx.hPart D (m + 1) z ⟨(k, r + 2), by omega⟩ = 0 := by
    rcases k with _ | k
    · rfl
    · simp only [DblCx.hPart]
      rw [hvan ⟨(k, r + 2), by omega⟩ (by simp), map_zero]
  rw [hh, zero_add] at h1
  simp only [DblCx.vPart] at h1
  have h2 : D.dv k (r + 1) (z ⟨(k, r + 1), by omega⟩) = 0 := by
    have hu : IsUnit ((-1 : ℤ) ^ k) := (isUnit_neg_one (α := ℤ)).pow k
    exact (hu.smul_eq_zero).1 h1
  obtain ⟨y, hy⟩ := G.exS k r _ h2
  refine ⟨z - D.dTot m (Pi.single (⟨(k, r), hr⟩ : DblCx.Idx m) ((-1 : ℤ) ^ k • y)), 
    Pi.single (⟨(k, r), hr⟩ : DblCx.Idx m) ((-1 : ℤ) ^ k • y), ?_, by abel, ?_⟩
  · rw [D.dTot_sub, hz, D.dTot_dTot, sub_zero]
  · rintro ⟨⟨p, q⟩, hx⟩ hlt
    simp only at hlt
    simp only [Pi.sub_apply]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with hlt | rfl
    · rw [D.dTot_single_lt m k r hr _ ⟨(p, q), hx⟩ hlt, hvan ⟨(p, q), hx⟩ hlt, sub_zero]
    · obtain rfl : q = r + 1 := by simp at hx; omega
      rw [D.dTot_single_self m p r hr _ hx, ← hy, map_zsmul, smul_smul, ← pow_add, ← two_mul,
          pow_mul]
      simp

private lemma surj_succ (G : AugData D) (m : ℕ) (z : D.TotX (m + 1)) (hz : D.dTot (m + 1) z = 0) :
    ∃ (a : G.A.X (m + 1)) (w : D.TotX m), z = D.augFun G.A G.ε (m + 1) a + D.dTot m w := by
  have key : ∀ k, k ≤ m + 1 → ∃ (z' : D.TotX (m + 1)) (w : D.TotX m), D.dTot (m + 1) z' = 0 ∧
      z = z' + D.dTot m w ∧ ∀ x : DblCx.Idx (m + 1), x.1.1 < k → z' x = 0 := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨z, 0, hz, by simp [D.dTot_zero], fun x hx => absurd hx (by omega)⟩
    | succ k ih =>
      intro hk
      obtain ⟨z', w, hz', hw, hvan⟩ := ih (by omega)
      obtain ⟨z'', w0, hz'', hzz, hvan'⟩ := surj_step G m z' hz' k (by omega) hvan
      exact ⟨z'', w + w0, hz'', by rw [hw, hzz, D.dTot_add]; abel, hvan'⟩
  obtain ⟨z', w, hz', hw, hvan⟩ := key (m + 1) le_rfl
  have h1 := congrFun hz' ⟨(m + 1, 1), rfl⟩
  simp only [DblCx.dTot, Pi.add_apply, DblCx.hPart, DblCx.vPart] at h1
  rw [hvan ⟨(m, 1), by simp⟩ (by simp)] at h1
  simp only [map_zero, zero_add] at h1
  have h2 : D.dv (m + 1) 0 (z' ⟨(m + 1, 0), rfl⟩) = 0 := by
    have hu : IsUnit ((-1 : ℤ) ^ (m + 1)) := (isUnit_neg_one (α := ℤ)).pow _
    exact (hu.smul_eq_zero).1 h1
  obtain ⟨a, ha⟩ := G.ex0 _ _ h2
  refine ⟨a, w, ?_⟩
  have : z' = D.augFun G.A G.ε (m + 1) a := by
    funext ⟨⟨p, q⟩, hh⟩
    rcases q with _ | q
    · simp only [add_zero] at hh; subst hh
      exact ha.symm
    · rw [D.augFun_succ, hvan ⟨(p, q + 1), hh⟩ (by simp at hh ⊢; omega)]
  rw [hw, this]

open Classical in
private lemma inj_step (G : AugData D) (m : ℕ) (a : G.A.X (m + 1)) (w : D.TotX m)
    (hw : D.dTot m w = D.augFun G.A G.ε (m + 1) a) (k : ℕ) (hk : k < m)
    (hvan : ∀ x : DblCx.Idx m, x.1.1 < k → w x = 0) :
    ∃ w' : D.TotX m, D.dTot m w' = D.augFun G.A G.ε (m + 1) a ∧
      ∀ x : DblCx.Idx m, x.1.1 < k + 1 → w' x = 0 := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨r', hr⟩ : ∃ r', k + (r' + 1) = m' + 1 := ⟨m' - k, by omega⟩
  have h1 := congrFun hw ⟨(k, r' + 2), by omega⟩
  rw [D.augFun_ne _ _ _ _ _ _ _ (by omega)] at h1
  simp only [DblCx.dTot, Pi.add_apply] at h1
  have hh : DblCx.hPart D (m' + 1) w ⟨(k, r' + 2), by omega⟩ = 0 := by
    rcases k with _ | k
    · rfl
    · simp only [DblCx.hPart]
      rw [hvan ⟨(k, r' + 2), by omega⟩ (by simp), map_zero]
  rw [hh, zero_add] at h1
  simp only [DblCx.vPart] at h1
  have h2 : D.dv k (r' + 1) (w ⟨(k, r' + 1), hr⟩) = 0 := by
    have hu : IsUnit ((-1 : ℤ) ^ k) := (isUnit_neg_one (α := ℤ)).pow k
    exact (hu.smul_eq_zero).1 h1
  obtain ⟨y, hy⟩ := G.exS k r' _ h2
  have hk' : k + r' = m' := by omega
  refine ⟨w - D.dTot m' (Pi.single (⟨(k, r'), hk'⟩ : DblCx.Idx m') ((-1 : ℤ) ^ k • y)), ?_, ?_⟩
  · rw [D.dTot_sub, hw, D.dTot_dTot, sub_zero]
  · rintro ⟨⟨p, q⟩, hx⟩ hlt
    simp only at hlt
    simp only [Pi.sub_apply]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with hlt | rfl
    · rw [D.dTot_single_lt m' k r' hk' _ ⟨(p, q), hx⟩ hlt, hvan ⟨(p, q), hx⟩ hlt, sub_zero]
    · obtain rfl : q = r' + 1 := by simp at hx; omega
      rw [D.dTot_single_self m' p r' hk' _ hx, map_zsmul, smul_smul, ← pow_add, ← two_mul, pow_mul,
          hy]
      simp

private lemma inj_succ (G : AugData D) (m : ℕ) (a : G.A.X (m + 1)) (w : D.TotX m)
    (hw : D.dTot m w = D.augFun G.A G.ε (m + 1) a) : ∃ a' : G.A.X m, G.A.d m (m + 1) a' = a := by
  have key : ∀ k, k ≤ m → ∃ w' : D.TotX m, D.dTot m w' = D.augFun G.A G.ε (m + 1) a ∧
      ∀ x : DblCx.Idx m, x.1.1 < k → w' x = 0 := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨w, hw, fun x hx => absurd hx (by omega)⟩
    | succ k ih =>
      intro hk
      obtain ⟨w', hw', hvan⟩ := ih (by omega)
      exact inj_step G m a w' hw' k (by omega) hvan
  obtain ⟨w', hw', hvan⟩ := key m le_rfl
  have h1 := congrFun hw' ⟨(m, 1), rfl⟩
  rw [D.augFun_ne _ _ _ _ _ _ _ (by omega)] at h1
  simp only [DblCx.dTot, Pi.add_apply] at h1
  have hh : DblCx.hPart D m w' ⟨(m, 1), rfl⟩ = 0 := by
    rcases m with _ | m
    · rfl
    · simp only [DblCx.hPart]
      rw [hvan ⟨(m, 1), by simp⟩ (by simp), map_zero]
  rw [hh, zero_add] at h1
  simp only [DblCx.vPart] at h1
  have h2 : D.dv m 0 (w' ⟨(m, 0), rfl⟩) = 0 := by
    have hu : IsUnit ((-1 : ℤ) ^ m) := (isUnit_neg_one (α := ℤ)).pow m
    exact (hu.smul_eq_zero).1 h1
  obtain ⟨a', ha'⟩ := G.ex0 _ _ h2
  refine ⟨a', ?_⟩
  have h3 : w' = D.augFun G.A G.ε m a' := by
    funext ⟨⟨p, q⟩, hh⟩
    rcases q with _ | q
    · simp only [add_zero] at hh; subst hh
      exact ha'.symm
    · rw [D.augFun_succ, hvan ⟨(p, q + 1), hh⟩ (by simp at hh ⊢; omega)]
  rw [h3, ← D.augFun_d G.A G.ε G.hd G.hv] at hw'
  have h4 := congrFun hw' ⟨(m + 1, 0), rfl⟩
  exact G.inj (m + 1) h4

private lemma augFun_eq_zero (n : ℕ) (a : G.A.X n) (h : D.augFun G.A G.ε n a = 0) : a = 0 := by
  have := congrFun h ⟨(n, 0), rfl⟩
  exact G.inj n (by rwa [map_zero])

/-- The augmentation as a morphism of complexes. -/
private def augHom : G.A ⟶ D.tot where
  f n := AddCommGrpCat.ofHom
      { toFun := D.augFun G.A G.ε n
        map_zero' := D.augFun_zero G.A G.ε n
        map_add' := D.augFun_add G.A G.ε n }
  comm' i j hij := by
    have hij' : i + 1 = j := hij
    subst hij'
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun a => ?_)
    have : D.tot.d i (i + 1) = AddCommGrpCat.ofHom
      { toFun := D.dTot i
        map_zero' := D.dTot_zero i
        map_add' := D.dTot_add i } := by simp [tot]
    rw [this]
    exact (D.augFun_d G.A G.ε G.hd G.hv i a).symm

private lemma tot_d_apply (n : ℕ) (y : D.tot.X n) : D.tot.d n (n + 1) y = D.dTot n y := by
  have : D.tot.d n (n + 1) = AddCommGrpCat.ofHom
      { toFun := D.dTot n
        map_zero' := D.dTot_zero n
        map_add' := D.dTot_add n } := by simp [tot]
  rw [this]; rfl

private theorem quasiIso_augHom : QuasiIso G.augHom := by
  refine ⟨fun n => ?_⟩
  cases n with
  | zero =>
    rw [CochainComplex.quasiIsoAt₀_iff]
    apply ab_quasiIso_of
    · intro y hy
      have hy' : D.dTot 0 y = 0 := (tot_d_apply (D := D) 0 y).symm.trans hy
      obtain ⟨a, rfl⟩ := G.surj_zero y hy'
      refine ⟨a, ?_, 0, ?_⟩
      · have h1 : D.augFun G.A G.ε 1 (G.A.d 0 1 a) = 0 := by
          rw [D.augFun_d G.A G.ε G.hd G.hv]; exact hy'
        exact G.augFun_eq_zero _ _ h1
      · change D.augFun G.A G.ε 0 a - D.augFun G.A G.ε 0 a = _
        rw [sub_self]; exact (map_zero _).symm
    · intro x _ ⟨t, ht⟩
      refine ⟨0, ?_⟩
      have : D.augFun G.A G.ε 0 x = 0 := by
        have h0 : D.tot.d 0 0 = 0 := D.tot.shape _ _ (by simp)
        have : (D.tot.d 0 0) t = 0 := by rw [h0]; rfl
        exact ht.trans this
      have hx := G.augFun_eq_zero _ _ this
      have h0 : G.A.d 0 0 = 0 := G.A.shape _ _ (by simp)
      show x = (G.A.d 0 0) 0
      rw [h0, hx]; rfl
  | succ m =>
    rw [quasiIsoAt_iff' _ m (m + 1) (m + 2) (by simp) (by simp)]
    apply ab_quasiIso_of
    · intro y hy
      have hy' : D.dTot (m + 1) y = 0 := (tot_d_apply (D := D) (m + 1) y).symm.trans hy
      obtain ⟨a, w, hw⟩ := G.surj_succ m y hy'
      refine ⟨a, ?_, -w, ?_⟩
      · have h1 : D.augFun G.A G.ε (m + 2) (G.A.d (m + 1) (m + 2) a) = 0 := by
          rw [D.augFun_d G.A G.ε G.hd G.hv]
          have := hy'
          rw [hw, D.dTot_add, D.dTot_dTot, add_zero] at this
          exact this
        exact G.augFun_eq_zero _ _ h1
      · have aux : ∀ (y : D.TotX (m + 1)), y = D.augFun G.A G.ε (m + 1) a + D.dTot m w →
            D.augFun G.A G.ε (m + 1) a - y = D.dTot m (-w) := by
          intro y hw
          rw [D.dTot_neg, hw]; abel
        exact (aux y hw).trans (tot_d_apply (D := D) m (-w)).symm
    · intro x _ ⟨t, ht⟩
      have ht' : D.augFun G.A G.ε (m + 1) x = D.dTot m t := ht.trans (tot_d_apply (D := D) m t)
      obtain ⟨a', ha'⟩ := G.inj_succ m x t ht'.symm
      exact ⟨a', ha'.symm⟩

end AugData

end DblCx

namespace DblCx

variable (D : DblCx.{u})

/-- The transposed double complex, with signs. -/
private def transpose : DblCx.{u} where
  X p q := D.X q p
  dh p q := (-1 : ℤ) ^ q • D.dv q p
  dv p q := (-1 : ℤ) ^ p • D.dh q p
  dh_dh p q := by
    rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul, ← pow_add, ← two_mul, pow_mul]
    simp [D.dv_dv]
  dv_dv p q := by
    rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul, ← pow_add, ← two_mul, pow_mul]
    simp [D.dh_dh]
  comm p q := by
    rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul, Preadditive.zsmul_comp,
      Preadditive.comp_zsmul, smul_smul]
    have h := D.comm q p
    have e : (-1 : ℤ) ^ q * (-1) ^ (p + 1) = (-1) ^ p * (-1) ^ (q + 1) := by
      rw [pow_succ, pow_succ]; ring
    rw [e, D.comm q p]

end DblCx

namespace DblCx

variable (D : DblCx.{u})

/-- Swap the indices of a total-degree-`n` family. -/
private def swapFun (n : ℕ) (z : D.TotX n) : D.transpose.TotX n :=
  fun x => z ⟨(x.1.2, x.1.1), by have := x.2; simp only at this ⊢; omega⟩

private lemma dTot_swapFun (n : ℕ) (z : D.TotX n) :
    D.transpose.dTot n (D.swapFun n z) = D.swapFun (n + 1) (D.dTot n z) := by
  funext ⟨⟨p, q⟩, h⟩
  simp only [dTot, Pi.add_apply]
  rcases p with _ | p <;> rcases q with _ | q
  · simp at h
  · simp only [transpose, Int.reduceNeg, hPart, vPart, pow_zero, one_smul, swapFun, Pi.add_apply,
      add_zero]
    erw [zero_add, one_smul]
    rfl
  · simp only [transpose, Int.reduceNeg, hPart, pow_zero, one_smul, swapFun, vPart, Pi.add_apply,
      zero_add]
    erw [add_zero]
    rfl
  · simp only [transpose, Int.reduceNeg, hPart, AddCommGrpCat.hom_zsmul, swapFun, vPart,
      Pi.add_apply]
    refine (add_comm _ _).trans (congrArg₂ _ ?_ ?_)
    · erw [smul_smul, ← pow_add, ← two_mul, pow_mul]
      simp
    · rfl

end DblCx

namespace DblCx

variable (D : DblCx.{u})

private lemma swapFun_add (n : ℕ) (a b : D.TotX n) : D.swapFun n (a + b) = D.swapFun n a + D.swapFun
    n b := rfl

/-- The identification of the total complex with that of the transposed double complex. -/
private def swapHom : D.tot ⟶ D.transpose.tot where
  f n := AddCommGrpCat.ofHom
    { toFun := D.swapFun n
      map_zero' := rfl
      map_add' := D.swapFun_add n }
  comm' i j hij := by
    have hij' : i + 1 = j := hij
    subst hij'
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun a => ?_)
    have h1 : D.tot.d i (i + 1) = AddCommGrpCat.ofHom
      { toFun := D.dTot i
        map_zero' := D.dTot_zero i
        map_add' := D.dTot_add i } := by simp [tot]
    have h2 : D.transpose.tot.d i (i + 1) = AddCommGrpCat.ofHom
      { toFun := D.transpose.dTot i
        map_zero' := D.transpose.dTot_zero i
        map_add' := D.transpose.dTot_add i } := by simp [tot]
    rw [h1, h2]
    exact D.dTot_swapFun i a

private instance isIso_swapHom : IsIso D.swapHom := by
  have : ∀ n, IsIso (D.swapHom.f n) := fun n => by
    rw [ConcreteCategory.isIso_iff_bijective]
    refine ⟨fun a b h => ?_, fun z =>
      ⟨fun x => z ⟨(x.1.2, x.1.1), by have := x.2; simp only at this ⊢; omega⟩, ?_⟩⟩
    · funext ⟨⟨p, q⟩, hh⟩
      exact congrFun h ⟨(q, p), by simp only at hh ⊢; omega⟩
    · funext ⟨⟨p, q⟩, hh⟩
      rfl
  exact HomologicalComplex.Hom.isIso_of_components _

end DblCx

namespace DblCx

variable (D : DblCx.{u})

/-- Row augmentation: the augmentation of the transposed double complex, followed by the
identification of the total complexes. -/
private def rowAugHom (G : AugData D.transpose) : G.A ⟶ D.tot := G.augHom ≫ inv D.swapHom

private theorem quasiIso_rowAugHom (G : AugData D.transpose) : QuasiIso (D.rowAugHom G) := by
  have := G.quasiIso_augHom
  unfold rowAugHom
  infer_instance

end DblCx

/-- A morphism of first-quadrant double complexes. -/
private structure DblHom (D D' : DblCx.{u}) where
  f : ∀ p q, D.X p q ⟶ D'.X p q
  dh : ∀ p q, f p q ≫ D'.dh p q = D.dh p q ≫ f (p + 1) q
  dv : ∀ p q, f p q ≫ D'.dv p q = D.dv p q ≫ f p (q + 1)

namespace DblHom

variable {D D' : DblCx.{u}} (Ψ : DblHom D D')

private lemma dh_apply (p q : ℕ) (x : D.X p q) : D'.dh p q (Ψ.f p q x) = Ψ.f (p + 1) q (D.dh p q
    x) := by
  have := congrArg (fun g => g.hom x) (Ψ.dh p q)
  simpa using this

private lemma dv_apply (p q : ℕ) (x : D.X p q) : D'.dv p q (Ψ.f p q x) = Ψ.f p (q + 1) (D.dv p q
    x) := by
  have := congrArg (fun g => g.hom x) (Ψ.dv p q)
  simpa using this

/-- The induced map on total degree-`n` families. -/
private def totFun (n : ℕ) (z : D.TotX n) : D'.TotX n := fun x => Ψ.f x.1.1 x.1.2 (z x)

private lemma totFun_dTot (n : ℕ) (z : D.TotX n) :
    D'.dTot n (Ψ.totFun n z) = Ψ.totFun (n + 1) (D.dTot n z) := by
  funext ⟨⟨p, q⟩, h⟩
  simp only [DblCx.dTot, Pi.add_apply]
  rcases p with _ | p <;> rcases q with _ | q
  · simp [DblCx.hPart, DblCx.vPart, totFun]
  · simp only [DblCx.hPart, DblCx.vPart, Int.reduceNeg, pow_zero, totFun, one_smul, zero_add,
      Pi.add_apply]
    exact Ψ.dv_apply _ _ _
  · simp only [DblCx.hPart, totFun, DblCx.vPart, add_zero, Pi.add_apply]
    rw [Ψ.dh_apply]
  · simp only [DblCx.hPart, totFun, DblCx.vPart, Int.reduceNeg, Pi.add_apply, map_add, map_zsmul]
    rw [Ψ.dh_apply, Ψ.dv_apply]

/-- The induced map of total complexes. -/
private def totHom : D.tot ⟶ D'.tot where
  f n := AddCommGrpCat.ofHom
    { toFun := Ψ.totFun n
      map_zero' := by funext x; exact map_zero _
      map_add' := fun a b => by funext x; exact map_add _ _ _ }
  comm' i j hij := by
    have hij' : i + 1 = j := hij
    subst hij'
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun a => ?_)
    have h1 : D.tot.d i (i + 1) = AddCommGrpCat.ofHom
      { toFun := D.dTot i
        map_zero' := D.dTot_zero i
        map_add' := D.dTot_add i } := by simp [DblCx.tot]
    have h2 : D'.tot.d i (i + 1) = AddCommGrpCat.ofHom
      { toFun := D'.dTot i
        map_zero' := D'.dTot_zero i
        map_add' := D'.dTot_add i } := by simp [DblCx.tot]
    rw [h1, h2]
    exact Ψ.totFun_dTot i a

end DblHom

namespace DblHom

variable {D D' : DblCx.{u}} (Ψ : DblHom D D')

/-- The transposed morphism. -/
private def transpose : DblHom D.transpose D'.transpose where
  f p q := Ψ.f q p
  dh p q := by
    change Ψ.f q p ≫ ((-1 : ℤ) ^ q • D'.dv q p) = ((-1 : ℤ) ^ q • D.dv q p) ≫ Ψ.f q (p + 1)
    rw [Preadditive.comp_zsmul, Preadditive.zsmul_comp, Ψ.dv]
  dv p q := by
    change Ψ.f q p ≫ ((-1 : ℤ) ^ p • D'.dh q p) = ((-1 : ℤ) ^ p • D.dh q p) ≫ Ψ.f (q + 1) p
    rw [Preadditive.comp_zsmul, Preadditive.zsmul_comp, Ψ.dh]

private lemma swap_natural : Ψ.totHom ≫ D'.swapHom = D.swapHom ≫ Ψ.transpose.totHom := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun a => ?_)
  funext ⟨⟨p, q⟩, h⟩
  rfl

private lemma augHom_naturality {G : DblCx.AugData D} {G' : DblCx.AugData D'} (α : G.A ⟶ G'.A)
    (h : ∀ p, α.f p ≫ G'.ε p = G.ε p ≫ Ψ.f p 0) :
    G.augHom ≫ Ψ.totHom = α ≫ G'.augHom := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun a => ?_)
  funext ⟨⟨p, q⟩, hh⟩
  rcases q with _ | q
  · have hp : p = n := by simpa using hh
    subst hp
    have := congrArg (fun g => g.hom a) (h p)
    simp at this
    exact this.symm
  · change Ψ.f p (q + 1) (D.augFun G.A G.ε n a ⟨(p, q + 1), hh⟩) =
      D'.augFun G'.A G'.ε n (α.f n a) ⟨(p, q + 1), hh⟩
    rw [DblCx.augFun_succ, DblCx.augFun_succ, map_zero]

private lemma rowAugHom_naturality {G : DblCx.AugData D.transpose} {G' : DblCx.AugData D'.transpose}
    (α : G.A ⟶ G'.A) (h : ∀ p, α.f p ≫ G'.ε p = G.ε p ≫ Ψ.f 0 p) :
    D.rowAugHom G ≫ Ψ.totHom = α ≫ D'.rowAugHom G' := by
  have h' : ∀ p, α.f p ≫ G'.ε p = G.ε p ≫ Ψ.transpose.f p 0 := h
  have h1 := Ψ.transpose.augHom_naturality α h'
  have h2 : inv D.swapHom ≫ Ψ.totHom = Ψ.transpose.totHom ≫ inv D'.swapHom := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, ← Ψ.swap_natural, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  unfold DblCx.rowAugHom
  rw [Category.assoc, h2, ← Category.assoc, h1, Category.assoc]

end DblHom

end Assembly

section GodementExact

open TopCat TopCat.Presheaf

variable {T : TopCat.{u}}

/-- `G` sends exact short complexes of sheaves to exact short complexes. -/
private theorem godement_map_exact (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} T)) (hS :
    S.Exact) :
    (S.map (godementFunctor T)).Exact := by
  rw [TopCat.Sheaf.exact_iff_stalkFunctor_map_exact]
  intro x
  rw [ShortComplex.ab_exact_iff]
  intro e he
  have hS' := fun y => (ShortComplex.ab_exact_iff _).1
    ((TopCat.Sheaf.exact_iff_stalkFunctor_map_exact S).1 hS y)
  obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq ((godementFunctor T).obj S.X₂).presheaf
      e
  change (stalkFunctor AddCommGrpCat x).map ((godementFunctor T).map S.g).hom
    (((godementFunctor T).obj S.X₂).presheaf.germ U x hxU s) = 0 at he
  rw [stalkFunctor_map_germ_apply] at he
  have he' : ((godementFunctor T).obj S.X₃).presheaf.germ U x hxU
      (((godementFunctor T).map S.g).hom.app (op U) s) =
      ((godementFunctor T).obj S.X₃).presheaf.germ U x hxU 0 := by
    rwa [map_zero]
  obtain ⟨W, hxW, iU, iV, hW⟩ := TopCat.Presheaf.germ_eq _ x hxU hxU _ _ he'
  have hy : ∀ y : W, ∃ t : S.X₁.presheaf.stalk y.1,
      (stalkFunctor AddCommGrpCat y.1).map S.f.hom t = s ⟨y.1, iU.le y.2⟩ :=
    fun y => hS' y.1 _ (congrFun hW y)
  choose t ht using hy
  refine ⟨((godementFunctor T).obj S.X₁).presheaf.germ W x hxW t, ?_⟩
  have hsec : ((godementFunctor T).map S.f).hom.app (op W) (t : ((godementFunctor T).obj
      S.X₁).presheaf.obj (op W)) =
      ((godementFunctor T).obj S.X₂).presheaf.map iU.op s := by
    funext y
    exact ht y
  change ((stalkFunctor AddCommGrpCat x).map ((godementFunctor T).map S.f).hom)
      (((godementFunctor T).obj S.X₁).presheaf.germ W x hxW t) = _
  erw [stalkFunctor_map_germ_apply, hsec]
  exact germ_res_apply _ iU x hxW s

private instance godement_additive : (godementFunctor T).Additive where
  map_add {F F'} f g := sheafHom_ext fun U s => funext fun x => by
    change (stalkFunctor AddCommGrpCat x.1).map (f.hom + g.hom) (s x) =
      (stalkFunctor AddCommGrpCat x.1).map f.hom (s x) + (stalkFunctor AddCommGrpCat x.1).map g.hom
          (s x)
    rw [Functor.map_add]
    rfl

private theorem godement_exactFunctor :
    PreservesFiniteLimits (godementFunctor T) ∧ PreservesFiniteColimits (godementFunctor T) :=
  ((Functor.exact_tfae (godementFunctor T)).out 2 4).mp fun S hS => godement_map_exact S hS

end GodementExact

section AugmentedExact

open CokernelCoresolution

variable {C : Type u'} [Category.{v'} C] [Abelian C] (G : C ⥤ C) (η : 𝟭 C ⟶ G) [G.Additive]

private def phi : C ⥤ C where
  obj F := cokernel (η.app F)
  map f := cokernel.map (η.app _) (η.app _) f (G.map f) (η.naturality f).symm
  map_id F := by ext; simp
  map_comp f g := by ext; simp

@[reassoc]
private lemma π_phi_map {X Y : C} (f : X ⟶ Y) :
    cokernel.π (η.app X) ≫ (phi G η).map f = G.map f ≫ cokernel.π (η.app Y) := by
  simp [phi]

attribute [local simp] π_phi_map π_phi_map_assoc

private instance : (phi G η).PreservesZeroMorphisms where
  map_zero X Y := by
    refine coequalizer.hom_ext ?_
    change cokernel.π _ ≫ _ = cokernel.π _ ≫ _
    rw [π_phi_map, G.map_zero]
    exact zero_comp.trans comp_zero.symm

private lemma phi_shortExact [∀ X, Mono (η.app X)] (hG : PreservesFiniteLimits G ∧
    PreservesFiniteColimits G)
    (S : ShortComplex C) (hS : S.ShortExact) : (S.map (phi G η)).ShortExact := by
  have hGS : (S.map G).ShortExact := ((Functor.exact_tfae G).out 1 4 rfl rfl).mpr hG S hS
  let v : S ⟶ S.map G := ⟨η.app _, η.app _, η.app _, (η.naturality _).symm, (η.naturality _).symm⟩
  let SI : ShortComplex.SnakeInput C :=
  { L₀ := ShortComplex.mk (kernel.map (η.app S.X₁) (η.app S.X₂) S.f (G.map S.f) (η.naturality
      _).symm)
        (kernel.map (η.app S.X₂) (η.app S.X₃) S.g (G.map S.g) (η.naturality _).symm) (by ext; simp)
    L₁ := S
    L₂ := S.map G
    L₃ := S.map (phi G η)
    v₀₁ := ⟨kernel.ι _, kernel.ι _, kernel.ι _, by simp, by simp⟩
    v₁₂ := v
    v₂₃ := ⟨cokernel.π _, cokernel.π _, cokernel.π _, π_phi_map G η _, π_phi_map G η _⟩
    w₀₂ := by ext <;> simp [v]
    w₁₃ := by ext <;> exact cokernel.condition _
    h₀ := by
      apply ShortComplex.isLimitOfIsLimitπ <;>
        apply (KernelFork.isLimitMapConeEquiv _ _).2 <;> exact kernelIsKernel _
    h₃ := by
      apply ShortComplex.isColimitOfIsColimitπ <;>
        apply (CokernelCofork.isColimitMapCoconeEquiv _ _).2 <;> exact cokernelIsCokernel _
    L₁_exact := hS.exact
    epi_L₁_g := hS.epi_g
    L₂_exact := hGS.exact
    mono_L₂_f := hGS.mono_f }
  have h3 : (S.map (phi G η)).Exact := SI.L₃_exact
  have h0 : IsZero SI.L₀.X₃ := isZero_kernel_of_mono (η.app S.X₃)
  have hmono : Mono (S.map (phi G η)).f := by
    have hz : SI.δ = 0 := h0.eq_of_src _ _
    exact (ShortComplex.exact_iff_mono SI.L₂' hz).1 SI.L₂'_exact
  have hepi : Epi (S.map (phi G η)).g := by
    have : Epi SI.L₂.g := hGS.epi_g
    exact SI.epi_L₃_g
  exact ShortComplex.ShortExact.mk' h3 hmono hepi

private def cokerFunctor (n : ℕ) : C ⥤ C where
  obj F := cokernel (stage G η F n).2.2
  map a := cokerDesc (stageHom (idLift G η) a n)
  map_id F := by
    refine coequalizer.hom_ext ?_
    change cokernel.π _ ≫ _ = cokernel.π _ ≫ _
    rw [π_cokerDesc, Category.comp_id]
    change homX (idLift G η) (𝟙 F) n ≫ cokernel.π _ = _
    rw [homX_id, Category.id_comp]
  map_comp a b := by
    refine coequalizer.hom_ext ?_
    change cokernel.π _ ≫ _ = cokernel.π _ ≫ _
    rw [π_cokerDesc, reassoc_of% (π_cokerDesc (stageHom (idLift G η) a n)), π_cokerDesc]
    change homX (idLift G η) (a ≫ b) n ≫ cokernel.π _ = homX (idLift G η) a n ≫ homX (idLift G η) b
        n ≫ cokernel.π _
    rw [homX_comp, Category.assoc]

private instance : (phi G η).Additive where
  map_add {X Y f g} := by
    refine coequalizer.hom_ext ?_
    have e : ∀ h : X ⟶ Y, cokernel.π (η.app X) ≫ (phi G η).map h = G.map h ≫ cokernel.π (η.app Y) :=
      fun h => π_phi_map G η h
    refine (e (f + g)).trans ?_
    refine Eq.trans ?_ (Preadditive.comp_add _ _ _ _ _ _).symm
    rw [G.map_add, Preadditive.add_comp, e, e]
    rfl

private lemma phi_exact [∀ X, Mono (η.app X)] (hG : PreservesFiniteLimits G ∧
    PreservesFiniteColimits G) :
    PreservesFiniteLimits (phi G η) ∧ PreservesFiniteColimits (phi G η) :=
  (((Functor.exact_tfae (phi G η)).out 1 4 rfl rfl).mp (phi_shortExact G η hG))

private def cokerFunctorZeroIso : cokerFunctor G η 0 ≅ phi G η :=
  NatIso.ofComponents (fun F => Iso.refl _) (fun {X Y} a => by
    refine coequalizer.hom_ext ?_
    change cokernel.π _ ≫ _ = cokernel.π _ ≫ _
    have e : cokernel.π (η.app X) ≫ (phi G η).map a = G.map a ≫ cokernel.π (η.app Y) := π_phi_map G
        η a
    have e2 : cokernel.π (η.app X) ≫ (cokerFunctor G η 0).map a = G.map a ≫ cokernel.π (η.app Y) :=
        by
      exact π_cokerDesc (stageHom (idLift G η) a 0)
    erw [Category.comp_id, Category.id_comp]
    exact e2.trans e.symm)

private def cokerFunctorSuccIso (n : ℕ) : cokerFunctor G η (n + 1) ≅ cokerFunctor G η n ⋙ phi G η :=
  NatIso.ofComponents (fun F => cokernelEpiComp (cokernel.π (stage G η F n).2.2)
      (η.app (cokernel (stage G η F n).2.2))) (fun {X Y} a => by
    refine coequalizer.hom_ext ?_
    change cokernel.π _ ≫ _ = cokernel.π _ ≫ _
    have A : ∀ F : C, cokernel.π (stage G η F (n + 1)).2.2 ≫
        (cokernelEpiComp (cokernel.π (stage G η F n).2.2) (η.app (cokernel (stage G η F
            n).2.2))).hom =
        cokernel.π (η.app (cokernel (stage G η F n).2.2)) := fun F => cokernel.π_desc _ _ _
    have B : cokernel.π (stage G η X (n + 1)).2.2 ≫ (cokerFunctor G η (n + 1)).map a =
        G.map ((cokerFunctor G η n).map a) ≫ cokernel.π (stage G η Y (n + 1)).2.2 :=
      π_cokerDesc (stageHom (idLift G η) a (n + 1))
    have C' : cokernel.π (η.app (cokernel (stage G η X n).2.2)) ≫ (phi G η).map ((cokerFunctor G η
        n).map a) =
        G.map ((cokerFunctor G η n).map a) ≫ cokernel.π (η.app (cokernel (stage G η Y n).2.2)) :=
      π_phi_map G η _
    have L : cokernel.π (stage G η X (n + 1)).2.2 ≫ ((cokerFunctor G η (n + 1)).map a ≫
        (cokernelEpiComp (cokernel.π (stage G η Y n).2.2) (η.app (cokernel (stage G η Y
            n).2.2))).hom) =
        G.map ((cokerFunctor G η n).map a) ≫ cokernel.π (η.app (cokernel (stage G η Y n).2.2)) :=
      (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) B).trans
        ((Category.assoc _ _ _).trans (congrArg (G.map _ ≫ ·) (A Y))))
    have R : cokernel.π (stage G η X (n + 1)).2.2 ≫
        ((cokernelEpiComp (cokernel.π (stage G η X n).2.2) (η.app (cokernel (stage G η X
            n).2.2))).hom ≫
          (phi G η).map ((cokerFunctor G η n).map a)) =
        G.map ((cokerFunctor G η n).map a) ≫ cokernel.π (η.app (cokernel (stage G η Y n).2.2)) :=
      (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (A X)).trans C')
    exact L.trans R.symm)

variable [∀ X, Mono (η.app X)] (hG : PreservesFiniteLimits G ∧ PreservesFiniteColimits G)

include hG

private lemma cokerFunctor_exact (n : ℕ) :
    PreservesFiniteLimits (cokerFunctor G η n) ∧ PreservesFiniteColimits (cokerFunctor G η n) := by
  induction n with
  | zero =>
    obtain ⟨h1, h2⟩ := phi_exact G η hG
    exact ⟨preservesFiniteLimits_of_natIso (cokerFunctorZeroIso G η).symm,
      preservesFiniteColimits_of_natIso (cokerFunctorZeroIso G η).symm⟩
  | succ n ih =>
    obtain ⟨h1, h2⟩ := phi_exact G η hG
    obtain ⟨h3, h4⟩ := ih
    exact ⟨preservesFiniteLimits_of_natIso (cokerFunctorSuccIso G η n).symm,
      preservesFiniteColimits_of_natIso (cokerFunctorSuccIso G η n).symm⟩

private def complexEvalZeroIso : complexFunctor G η ⋙ HomologicalComplex.eval C _ 0 ≅ G :=
  NatIso.ofComponents (fun F => Iso.refl _) (fun {X Y} a => by
    change homX (idLift G η) a 0 ≫ _ = _ ≫ _
    erw [Category.comp_id, Category.id_comp]
    rfl)

private def complexEvalSuccIso (n : ℕ) :
    complexFunctor G η ⋙ HomologicalComplex.eval C _ (n + 1) ≅ cokerFunctor G η n ⋙ G :=
  NatIso.ofComponents (fun F => Iso.refl _) (fun {X Y} a => by
    change homX (idLift G η) a (n + 1) ≫ _ = _ ≫ _
    erw [Category.comp_id, Category.id_comp]
    rfl)

private lemma complexFunctor_eval_exact (n : ℕ) :
    PreservesFiniteLimits (complexFunctor G η ⋙ HomologicalComplex.eval C _ n) ∧
      PreservesFiniteColimits (complexFunctor G η ⋙ HomologicalComplex.eval C _ n) := by
  cases n with
  | zero =>
    obtain ⟨h1, h2⟩ := id hG
    exact ⟨preservesFiniteLimits_of_natIso (complexEvalZeroIso G η).symm,
      preservesFiniteColimits_of_natIso (complexEvalZeroIso G η).symm⟩
  | succ n =>
    obtain ⟨h1, h2⟩ := id hG
    obtain ⟨h3, h4⟩ := cokerFunctor_exact G η hG n
    exact ⟨preservesFiniteLimits_of_natIso (complexEvalSuccIso G η n).symm,
      preservesFiniteColimits_of_natIso (complexEvalSuccIso G η n).symm⟩

end AugmentedExact

section SingleColumn

variable {C : Type u'} [Category.{v'} C] [Preadditive C]
  (D : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
  [D.HasTotal (ComplexShape.up ℤ)]
  (hD : ∀ i : ℤ, i ≠ 0 → IsZero (D.X i))

/-- inclusion of the zeroth column into the total complex -/
private def colToTotal : D.X 0 ⟶ D.total (ComplexShape.up ℤ) where
  f j := D.ιTotal (ComplexShape.up ℤ) 0 j j (by simp)
  comm' i j hij := by
    have hij' : i + 1 = j := hij
    subst hij'
    simp only [HomologicalComplex₂.total_d]
    rw [Preadditive.comp_add, HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂]
    have hd : D.d 0 1 = 0 := (hD 1 one_ne_zero).eq_of_tgt _ _
    rw [HomologicalComplex₂.d₁_eq' D _ (show (ComplexShape.up ℤ).Rel 0 1 by simp) i (i + 1),
      HomologicalComplex₂.d₂_eq D _ 0 hij (i + 1) (by simp), hd]
    simp

open Classical in
/-- inverse components -/
private def totalToColF (j : ℤ) : (D.total (ComplexShape.up ℤ)).X j ⟶ (D.X 0).X j :=
  D.totalDesc (fun i₁ i₂ hi => if h : i₁ = 0 then
      (by subst h; have h2 : i₂ = j := by simpa using hi
          subst h2; exact 𝟙 _) else 0)

private lemma totalToColF_ι_zero (j : ℤ) :
    D.ιTotal (ComplexShape.up ℤ) 0 j j (by simp) ≫ totalToColF D j = 𝟙 _ := by
  unfold totalToColF
  rw [HomologicalComplex₂.ι_totalDesc]
  simp

private instance isIso_colToTotal : IsIso (colToTotal D hD) := by
  have : ∀ j, IsIso ((colToTotal D hD).f j) := fun j => by
    refine ⟨totalToColF D j, totalToColF_ι_zero D j, ?_⟩
    change totalToColF D j ≫ D.ιTotal (ComplexShape.up ℤ) 0 j j (by simp) = 𝟙 _
    apply HomologicalComplex₂.total.hom_ext
    intro i₁ i₂ hi
    by_cases h : i₁ = 0
    · subst h
      have h2 : i₂ = j := by simpa using hi
      subst h2
      rw [Category.comp_id, ← Category.assoc, totalToColF_ι_zero, Category.id_comp]
    · rw [Category.comp_id]
      have hz : IsZero ((D.X i₁).X i₂) := by
        have := hD i₁ h
        exact (HomologicalComplex.eval _ _ i₂).map_isZero this
      exact hz.eq_of_src _ _
  exact HomologicalComplex.Hom.isIso_of_components _

end SingleColumn

section SingleColumnNat

variable {C : Type u'} [Category.{v'} C] [Preadditive C]
  (D D' : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
  [D.HasTotal (ComplexShape.up ℤ)] [D'.HasTotal (ComplexShape.up ℤ)]
  (hD : ∀ i : ℤ, i ≠ 0 → IsZero (D.X i)) (hD' : ∀ i : ℤ, i ≠ 0 → IsZero (D'.X i))

private lemma colToTotal_natural (Φ : D ⟶ D') :
    colToTotal D hD ≫ HomologicalComplex₂.total.map Φ (ComplexShape.up ℤ) =
      Φ.f 0 ≫ colToTotal D' hD' := by
  refine HomologicalComplex.hom_ext _ _ fun j => ?_
  change D.ιTotal (ComplexShape.up ℤ) 0 j j (by simp) ≫ (HomologicalComplex₂.total.map Φ
      (ComplexShape.up ℤ)).f j =
    (Φ.f 0).f j ≫ D'.ιTotal (ComplexShape.up ℤ) 0 j j (by simp)
  rw [HomologicalComplex₂.ιTotal_map]

end SingleColumnNat

/-- The `q`-th term of the Godement resolution, as an endofunctor of sheaves. -/
private def godementTerm (T : TopCat.{u}) (q : ℕ) :
    TopCat.Sheaf AddCommGrpCat.{u} T ⥤ TopCat.Sheaf AddCommGrpCat.{u} T :=
  godementResolution T ⋙ HomologicalComplex.eval _ _ q

private instance (T : TopCat.{u}) (q : ℕ) : (godementTerm T q).PreservesZeroMorphisms := by
  dsimp only [godementTerm]
  infer_instance

/-- The double complex `Γ(T, G^q(K^p))` of a complex `K` of sheaves. -/
private def godementDbl {T : TopCat.{u}} (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℕ) :
    DblCx.{u} where
  X p q := (globalSections T).obj (((godementResolution T).obj (K.X p)).X q)
  dh p q := (globalSections T).map (((godementResolution T).map (K.d p (p + 1))).f q)
  dv p q := (globalSections T).map (((godementResolution T).obj (K.X p)).d q (q + 1))
  dh_dh p q := by
    rw [← Functor.map_comp, ← HomologicalComplex.comp_f, ← Functor.map_comp, K.d_comp_d,
      Functor.map_zero]
    simp
  dv_dv p q := by
    rw [← Functor.map_comp, HomologicalComplex.d_comp_d]
    simp
  comm p q := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    exact ((godementResolution T).map (K.d p (p + 1))).comm q (q + 1)

section Columns

variable {T : TopCat.{u}}

private lemma isFlasque_godementTerm (F : TopCat.Sheaf AddCommGrpCat.{u} T) (q : ℕ) :
    TopCat.Presheaf.IsFlasque (((godementResolution T).obj F).X q).obj := by
  rcases q with _ | _ | q
  · exact isFlasque_godementFunctor F
  · exact isFlasque_godementFunctor _
  · exact isFlasque_godementFunctor _

/-- Elementwise form of exactness of the global sections of the Godement resolution in positive
degrees, for a flasque sheaf. -/
private lemma godement_exS (F : TopCat.Sheaf AddCommGrpCat.{u} T) (hF : TopCat.Presheaf.IsFlasque
    F.obj)
    (q : ℕ) (x : (globalSections T).obj (((godementResolution T).obj F).X (q + 1)))
    (hx : (globalSections T).map (((godementResolution T).obj F).d (q + 1) (q + 2)) x = 0) :
    ∃ y : (globalSections T).obj (((godementResolution T).obj F).X q),
      (globalSections T).map (((godementResolution T).obj F).d q (q + 1)) y = x := by
  haveI := godementAugmentation_quasiIso T F
  have h := exactAt_globalSections_of_flasque_resolution F hF ((godementResolution T).obj F)
    (godementAugmentation T F) (isFlasque_godementTerm F) q
  rw [HomologicalComplex.exactAt_iff' _ q (q + 1) (q + 2) (by simp) (by simp)] at h
  exact (ShortComplex.ab_exact_iff _).1 h x hx

/-- Exactness of global sections at degree `0` of the augmented Godement resolution. -/
private lemma godement_ex0 (F : TopCat.Sheaf AddCommGrpCat.{u} T)
    (x : (globalSections T).obj (((godementResolution T).obj F).X 0))
    (hx : (globalSections T).map (((godementResolution T).obj F).d 0 1) x = 0) :
    ∃ a : (globalSections T).obj F, (globalSections T).map ((godementUnit T).app F) a = x := by
  have h1 : (ShortComplex.mk ((godementUnit T).app F)
      (CokernelCoresolution.d (godementFunctor T) (godementUnit T) F 0) (by simp)).Exact :=
    exact_cokernel_comp_mono ((godementUnit T).app F) (((godementUnit T).app _))
  have h2 := h1.map_of_mono_of_preservesKernel (globalSections T) inferInstance inferInstance
  rw [ShortComplex.ab_exact_iff] at h2
  have hx' : (globalSections T).map (CokernelCoresolution.d (godementFunctor T) (godementUnit T) F
      0) x = 0 := by
    have := hx
    rw [show ((godementResolution T).obj F).d 0 1 =
      CokernelCoresolution.d (godementFunctor T) (godementUnit T) F 0 from
      CokernelCoresolution.complex_d _ _ _ _] at this
    exact this
  exact h2 x hx'

/-- The column augmentation data of `godementDbl K` for a complex `K` of flasque sheaves. -/
private def godementColAug (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℕ)
    (hK : ∀ p, TopCat.Presheaf.IsFlasque (K.X p).obj) : (godementDbl K).AugData where
  A := ((globalSections T).mapHomologicalComplex _).obj K
  ε p := (globalSections T).map ((godementUnit T).app (K.X p))
  hd p x := by
    have h := congrArg (fun f => ((globalSections T).map f).hom x)
      ((godementUnit T).naturality (K.d p (p + 1)))
    simp only [Functor.map_comp] at h
    exact h
  hv p x := by
    have h := congrArg (fun f => ((globalSections T).map f).hom x)
      (CokernelCoresolution.app_comp_d_zero (godementFunctor T) (godementUnit T) (K.X p))
    simp only [Functor.map_comp, Functor.map_zero] at h
    exact h
  inj p a b hab := by
    have := godementUnit_app_hom_app_injective (K.X p) (op ⊤)
    exact this hab
  ex0 p := godement_ex0 (K.X p)
  exS p q := godement_exS (K.X p) (hK p) q

/-- The degree-zero map of an augmentation `F[0] ⟶ K`. -/
private def augDeg0 {F : TopCat.Sheaf AddCommGrpCat.{u} T}
    {K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℕ}
    (ι : (CochainComplex.single₀ _).obj F ⟶ K) : F ⟶ K.X 0 :=
  (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 F).inv ≫ ι.f 0

private lemma augDeg0_comp_d {F : TopCat.Sheaf AddCommGrpCat.{u} T}
    {K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℕ}
    (ι : (CochainComplex.single₀ _).obj F ⟶ K) : augDeg0 ι ≫ K.d 0 1 = 0 := by
  have h := ι.comm 0 1
  have h0 : ((CochainComplex.single₀ (TopCat.Sheaf AddCommGrpCat.{u} T)).obj F).d 0 1 = 0 := rfl
  rw [h0, zero_comp] at h
  rw [augDeg0, Category.assoc, h, comp_zero]

private lemma exact_augDeg0 {F : TopCat.Sheaf AddCommGrpCat.{u} T}
    {K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℕ}
    (ι : (CochainComplex.single₀ _).obj F ⟶ K) [QuasiIso ι] :
    (ShortComplex.mk (augDeg0 ι) (K.d 0 1) (augDeg0_comp_d ι)).Exact ∧ Mono (augDeg0 ι) := by
  have h := (CochainComplex.quasiIsoAt₀_iff ι).1 (QuasiIso.quasiIsoAt (f := ι) 0)
  have h2 := (ShortComplex.quasiIso_iff_of_zeros _ rfl rfl
    (by show K.d 0 0 = 0; exact K.shape _ _ (by simp))).1 h
  refine (ShortComplex.exact_and_mono_f_iff_of_iso ?_).2 h2
  exact ShortComplex.isoMk (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 F).symm
    (Iso.refl _) (Iso.refl _) (by dsimp [augDeg0]; simp) (by dsimp; simp)

private lemma zsmul_hom_apply {M N : AddCommGrpCat.{u}} (k : ℤ) (f : M ⟶ N) (x : M) :
    (ConcreteCategory.hom (k • f)) x = k • ConcreteCategory.hom f x := rfl

private lemma quasiIso_of_exact_augDeg0 {F : TopCat.Sheaf AddCommGrpCat.{u} T}
    {K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℕ}
    (ι : (CochainComplex.single₀ _).obj F ⟶ K) [Mono (augDeg0 ι)]
    (hex : (ShortComplex.mk (augDeg0 ι) (K.d 0 1) (augDeg0_comp_d ι)).Exact)
    (hK : ∀ i, K.ExactAt (i + 1)) : QuasiIso ι := by
  refine ⟨fun n => ?_⟩
  cases n with
  | zero =>
    refine (CochainComplex.quasiIsoAt₀_iff ι).2 ?_
    refine (ShortComplex.quasiIso_iff_of_zeros _ rfl rfl
      (by show K.d 0 0 = 0; exact K.shape _ _ (by simp))).2 ?_
    refine (ShortComplex.exact_and_mono_f_iff_of_iso ?_).1 ⟨hex, inferInstance⟩
    exact ShortComplex.isoMk (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 F).symm
      (Iso.refl _) (Iso.refl _) (by dsimp [augDeg0]; simp) (by dsimp; simp)
  | succ n =>
    exact (quasiIsoAt_iff_exactAt _ _ (CochainComplex.exactAt_succ_single_obj _ _)).2 (hK n)

private lemma godementTerm_preservesHomology (p : ℕ) :
    (godementTerm T p).PreservesHomology ∧ (godementTerm T p).Additive := by
  have hq := complexFunctor_eval_exact (godementFunctor T) (godementUnit T) godement_exactFunctor p
  have : PreservesFiniteLimits (godementTerm T p) := hq.1
  have : PreservesFiniteColimits (godementTerm T p) := hq.2
  have : PreservesBinaryBiproducts (godementTerm T p) :=
    preservesBinaryBiproducts_of_preservesBinaryProducts _
  exact ⟨inferInstance, Functor.additive_of_preservesBinaryBiproducts _⟩

private lemma isFlasque_kernel_of_exact0 (F : TopCat.Sheaf AddCommGrpCat.{u} T)
    (hF : TopCat.Presheaf.IsFlasque F.obj) (E : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℕ)
    (ι₀ : F ⟶ E.X 0) (h0 : ι₀ ≫ E.d 0 1 = 0) [Mono ι₀]
    (hex : (ShortComplex.mk ι₀ (E.d 0 1) h0).Exact) :
    TopCat.Presheaf.IsFlasque (kernel (E.d 0 1)).obj := by
  let e := IsLimit.conePointUniqueUpToIso hex.fIsKernel (kernelIsKernel (E.d 0 1))
  exact isFlasque_of_iso (show F ≅ kernel (E.d 0 1) from e) hF

private lemma godementTerm_map_augDeg0_comp_d {F : TopCat.Sheaf AddCommGrpCat.{u} T}
    {K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℕ}
    (ι : (CochainComplex.single₀ _).obj F ⟶ K) (p : ℕ) :
    (godementTerm T p).map (augDeg0 ι) ≫ (godementTerm T p).map (K.d 0 1) = 0 := by
  rw [← Functor.map_comp, augDeg0_comp_d, Functor.map_zero]

private lemma godementTerm_exact_aug {F : TopCat.Sheaf AddCommGrpCat.{u} T}
    {K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℕ}
    (ι : (CochainComplex.single₀ _).obj F ⟶ K) [QuasiIso ι] (p : ℕ) :
    (ShortComplex.mk ((godementTerm T p).map (augDeg0 ι)) ((godementTerm T p).map (K.d 0 1))
      (godementTerm_map_augDeg0_comp_d ι p)).Exact ∧ Mono ((godementTerm T p).map (augDeg0 ι)) := by
  obtain ⟨hex, hmono⟩ := exact_augDeg0 ι
  haveI := (godementTerm_preservesHomology (T := T) p).1
  haveI := (godementTerm_preservesHomology (T := T) p).2
  have : PreservesFiniteLimits (godementTerm T p) :=
    (complexFunctor_eval_exact (godementFunctor T) (godementUnit T) godement_exactFunctor p).1
  exact ⟨hex.map (godementTerm T p), inferInstance⟩

private lemma exactAt_godementTerm_map {K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℕ} (p
    j : ℕ)
    (h : K.ExactAt j) : (((godementTerm T p).mapHomologicalComplex _).obj K).ExactAt j := by
  haveI := (godementTerm_preservesHomology (T := T) p).1
  haveI := (godementTerm_preservesHomology (T := T) p).2
  exact ShortComplex.Exact.map h (godementTerm T p)

/-- Elementwise exactness of global sections of `G^p(K^•)` in positive degrees. -/
private lemma godementRow_exS {F : TopCat.Sheaf AddCommGrpCat.{u} T}
    {K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℕ}
    (ι : (CochainComplex.single₀ _).obj F ⟶ K) [QuasiIso ι] (p q : ℕ)
    (x : (globalSections T).obj ((godementTerm T p).obj (K.X (q + 1))))
    (hx : (globalSections T).map ((godementTerm T p).map (K.d (q + 1) (q + 2))) x = 0) :
    ∃ y : (globalSections T).obj ((godementTerm T p).obj (K.X q)),
      (globalSections T).map ((godementTerm T p).map (K.d q (q + 1))) y = x := by
  have hFp : TopCat.Presheaf.IsFlasque ((godementTerm T p).obj F).obj := isFlasque_godementTerm F p
  obtain ⟨hex0, hmono0⟩ := godementTerm_exact_aug ι p
  have hK : ∀ i, K.ExactAt (i + 1) := fun i => by
    rw [← exactAt_iff_of_quasiIsoAt ι (i + 1)]
    exact CochainComplex.exactAt_succ_single_obj _ _
  have h0 := isFlasque_kernel_of_exact0 (T := T) ((godementTerm T p).obj F) hFp
    (((godementTerm T p).mapHomologicalComplex _).obj K) ((godementTerm T p).map (augDeg0 ι))
    (godementTerm_map_augDeg0_comp_d ι p) hex0
  have h := exactAt_globalSections_of_flasque' (((godementTerm T p).mapHomologicalComplex _).obj K)
      h0
    (fun i => exactAt_godementTerm_map p _ (hK i)) (fun p' => isFlasque_godementTerm (K.X p') p) q
  rw [HomologicalComplex.exactAt_iff' _ q (q + 1) (q + 2) (by simp) (by simp)] at h
  exact (ShortComplex.ab_exact_iff _).1 h x hx

private lemma godementRow_ex0 {F : TopCat.Sheaf AddCommGrpCat.{u} T}
    {K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℕ}
    (ι : (CochainComplex.single₀ _).obj F ⟶ K) [QuasiIso ι] (p : ℕ)
    (x : (globalSections T).obj ((godementTerm T p).obj (K.X 0)))
    (hx : (globalSections T).map ((godementTerm T p).map (K.d 0 1)) x = 0) :
    ∃ a : (globalSections T).obj ((godementTerm T p).obj F),
      (globalSections T).map ((godementTerm T p).map (augDeg0 ι)) a = x := by
  obtain ⟨hex0, hmono0⟩ := godementTerm_exact_aug ι p
  have h2 := hex0.map_of_mono_of_preservesKernel (globalSections T) inferInstance inferInstance
  rw [ShortComplex.ab_exact_iff] at h2
  exact h2 x hx

private lemma godementRow_inj {F : TopCat.Sheaf AddCommGrpCat.{u} T}
    {K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℕ}
    (ι : (CochainComplex.single₀ _).obj F ⟶ K) [QuasiIso ι] (p : ℕ) :
    Function.Injective ((globalSections T).map ((godementTerm T p).map (augDeg0 ι))) := by
  obtain ⟨hex0, hmono0⟩ := godementTerm_exact_aug ι p
  haveI := hmono0
  exact (AddCommGrpCat.mono_iff_injective _).1 inferInstance

/-- The row augmentation data of `(godementDbl K).transpose`. -/
private def godementRowAug (F : TopCat.Sheaf AddCommGrpCat.{u} T) (K : CochainComplex (TopCat.Sheaf
    AddCommGrpCat.{u} T) ℕ)
    (ι : (CochainComplex.single₀ _).obj F ⟶ K) [QuasiIso ι] : (godementDbl K).transpose.AugData
        where
  A := ((globalSections T).mapHomologicalComplex _).obj ((godementResolution T).obj F)
  ε p := (globalSections T).map ((godementTerm T p).map (augDeg0 ι))
  hd p x := by
    have h := congrArg (fun g => ((globalSections T).map g).hom x)
      (((godementResolution T).map (augDeg0 ι)).comm p (p + 1))
    simp only [Functor.map_comp] at h
    refine h.symm.trans ?_
    simp [godementDbl, DblCx.transpose]
    rfl
  hv p x := by
    have h : (globalSections T).map ((godementTerm T p).map (K.d 0 1))
        ((globalSections T).map ((godementTerm T p).map (augDeg0 ι)) x) = 0 := by
      have := congrArg (fun g => ((globalSections T).map ((godementTerm T p).map g)).hom x)
        (augDeg0_comp_d ι)
      simp only [Functor.map_comp, Functor.map_zero] at this
      exact this
    simp only [godementDbl, DblCx.transpose, Int.reduceNeg, Nat.reduceAdd, AddCommGrpCat.hom_zsmul,
        Functor.mapHomologicalComplex_obj_X]
    refine (zsmul_hom_apply ((-1 : ℤ) ^ p) _ _).trans ?_
    erw [h]
    exact smul_zero ((-1 : ℤ) ^ p)
  inj p := godementRow_inj ι p
  ex0 p x hx := by
    refine godementRow_ex0 ι p x ?_
    have hu : IsUnit ((-1 : ℤ) ^ p) := (isUnit_neg_one (α := ℤ)).pow p
    exact (hu.smul_eq_zero).1 hx
  exS p q x hx := by
    have hu : IsUnit ((-1 : ℤ) ^ p) := (isUnit_neg_one (α := ℤ)).pow p
    obtain ⟨y, hy⟩ := godementRow_exS ι p q x ((hu.smul_eq_zero).1 hx)
    refine ⟨(-1 : ℤ) ^ p • y, ?_⟩
    simp only [godementDbl, DblCx.transpose]
    refine (zsmul_hom_apply ((-1 : ℤ) ^ p) _ _).trans ?_
    erw [map_zsmul, smul_smul, ← pow_add, ← two_mul, pow_mul]
    erw [one_pow, one_smul]
    exact hy

end Columns

section NatDbl

variable {M N : TopCat.{u}} (f : N ⟶ M)

private lemma gamma_push {E E' : TopCat.Sheaf AddCommGrpCat.{u} N} (g : E ⟶ E') :
    (globalSections N).map g = (globalSections M).map ((TopCat.Sheaf.pushforward AddCommGrpCat.{u}
        f).map g) :=
  rfl

/-- The map of Godement double complexes induced by a map of complexes `K ⟶ f_* K'`. -/
private def godementDblHom (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} M) ℕ)
    (K' : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} N) ℕ)
    (θ : K ⟶ ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex _).obj K') :
    DblHom (godementDbl K) (godementDbl K') where
  f p q := (globalSections M).map
    ((CokernelCoresolution.complexHom (godementPullbackLift f) (θ.f p)).f q)
  dh p q := by
    have h := congrArg (fun g => g.f q) (CokernelCoresolution.complexFunctor_map_comp_complexHom
      (godementPullbackLift f) (K.d p (p + 1)) (K'.d p (p + 1)) (θ.f p) (θ.f (p + 1))
      (by simpa using (θ.comm p (p + 1)).symm))
    simp only [HomologicalComplex.comp_f] at h
    simp only [godementDbl]
    erw [gamma_push f]
    erw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (globalSections M).map h.symm
  dv p q := by
    have h := (CokernelCoresolution.complexHom (godementPullbackLift f) (θ.f p)).comm q (q + 1)
    simp only [godementDbl]
    rw [gamma_push f]
    erw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (globalSections M).map h

end NatDbl

section Natural

variable {M N : TopCat.{u}} (f : N ⟶ M)

/-- The `Γ`-map `Γ(M, K) ⟶ Γ(N, K')` of a morphism `K ⟶ f_* K'`. -/
private def gammaMap (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} M) ℕ)
    (K' : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} N) ℕ)
    (θ : K ⟶ ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex _).obj K') :
    ((globalSections M).mapHomologicalComplex _).obj K ⟶ ((globalSections N).mapHomologicalComplex
        _).obj K' :=
  ((globalSections M).mapHomologicalComplex _).map θ

/-- The isomorphism `H^n(Γ G^•(F)) ≅ H^n(Γ K)` through the double complex. -/
private def cmp2 {T : TopCat.{u}} (F : TopCat.Sheaf AddCommGrpCat.{u} T)
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℕ)
    (ι : (CochainComplex.single₀ _).obj F ⟶ K) [QuasiIso ι]
    (hK : ∀ p, TopCat.Presheaf.IsFlasque (K.X p).obj) (n : ℕ) :
    (((globalSections T).mapHomologicalComplex _).obj ((godementResolution T).obj F)).homology n ≅
      (((globalSections T).mapHomologicalComplex _).obj K).homology n := by
  haveI := (godementColAug K hK).quasiIso_augHom
  haveI := (godementDbl K).quasiIso_rowAugHom (godementRowAug F K ι)
  haveI : IsIso (HomologicalComplex.homologyMap (godementColAug K hK).augHom n) :=
    (quasiIsoAt_iff_isIso_homologyMap _ n).1 inferInstance
  have h2 : IsIso (HomologicalComplex.homologyMap ((godementDbl K).rowAugHom (godementRowAug F K ι))
      n) :=
    (quasiIsoAt_iff_isIso_homologyMap _ n).1 inferInstance
  exact @asIso _ _ _ _ _ h2 ≪≫
    (asIso (HomologicalComplex.homologyMap (godementColAug K hK).augHom n)).symm

private lemma iso_square {C : Type*} [Category C] {X Y Z X' Y' Z' : C} (b : X ⟶ Z) (c : Y ⟶ Z)
    (b' : X' ⟶ Z') (c' : Y' ⟶ Z') [IsIso b] [IsIso c] [IsIso b'] [IsIso c']
    (αF : X ⟶ X') (αK : Y ⟶ Y') (t : Z ⟶ Z') (h1 : b ≫ t = αF ≫ b') (h2 : c ≫ t = αK ≫ c') :
    (asIso b ≪≫ (asIso c).symm).hom ≫ αK = αF ≫ (asIso b' ≪≫ (asIso c').symm).hom := by
  have h3 : inv c ≫ αK = t ≫ inv c' := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, h2, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  simp only [Iso.trans_hom, asIso_hom, Iso.symm_hom, asIso_inv, Category.assoc]
  rw [h3, ← Category.assoc, h1, Category.assoc]

/-- The `Γ`-map `Γ(M, G^•F) ⟶ Γ(N, G^•F')` of a morphism `F ⟶ f_* F'`. -/
private def gammaMapF (F : TopCat.Sheaf AddCommGrpCat.{u} M) (F' : TopCat.Sheaf AddCommGrpCat.{u} N)
    (θF : F ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F') :
    ((globalSections M).mapHomologicalComplex _).obj ((godementResolution M).obj F) ⟶
      ((globalSections N).mapHomologicalComplex _).obj ((godementResolution N).obj F') :=
  ((globalSections M).mapHomologicalComplex _).map
    (CokernelCoresolution.complexHom (godementPullbackLift f) θF)

private lemma cmp2_natural (F : TopCat.Sheaf AddCommGrpCat.{u} M)
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} M) ℕ)
    (ι : (CochainComplex.single₀ _).obj F ⟶ K) [QuasiIso ι]
    (hK : ∀ p, TopCat.Presheaf.IsFlasque (K.X p).obj)
    (F' : TopCat.Sheaf AddCommGrpCat.{u} N)
    (K' : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} N) ℕ)
    (ι' : (CochainComplex.single₀ _).obj F' ⟶ K') [QuasiIso ι']
    (hK' : ∀ p, TopCat.Presheaf.IsFlasque (K'.X p).obj)
    (θF : F ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F')
    (θ : K ⟶ ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex _).obj K')
    (hι : augDeg0 ι ≫ θ.f 0 = θF ≫ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map (augDeg0 ι'))
        (n : ℕ) :
    (cmp2 F K ι hK n).hom ≫ HomologicalComplex.homologyMap (gammaMap f K K' θ) n =
      HomologicalComplex.homologyMap (gammaMapF f F F' θF) n ≫ (cmp2 F' K' ι' hK' n).hom := by
  let Ψ := godementDblHom f K K' θ
  have hcol : (godementColAug K hK).augHom ≫ Ψ.totHom =
      gammaMap f K K' θ ≫ (godementColAug K' hK').augHom := by
    refine Ψ.augHom_naturality (G := godementColAug K hK) (G' := godementColAug K' hK')
      (gammaMap f K K' θ) (fun p => ?_)
    change (globalSections M).map (θ.f p) ≫ (globalSections N).map ((godementUnit N).app (K'.X p)) =
      (globalSections M).map ((godementUnit M).app (K.X p)) ≫
        (globalSections M).map ((CokernelCoresolution.complexHom (godementPullbackLift f) (θ.f p)).f
            0)
    rw [gamma_push f]
    erw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (globalSections M).map
      (CokernelCoresolution.app_comp_homX_zero (godementPullbackLift f) (θ.f p)).symm
  have hrow : (godementDbl K).rowAugHom (godementRowAug F K ι) ≫ Ψ.totHom =
      gammaMapF f F F' θF ≫ (godementDbl K').rowAugHom (godementRowAug F' K' ι') := by
    refine Ψ.rowAugHom_naturality (G := godementRowAug F K ι) (G' := godementRowAug F' K' ι')
      (gammaMapF f F F' θF) (fun p => ?_)
    have h := congrArg (fun g => g.f p) (CokernelCoresolution.complexFunctor_map_comp_complexHom
      (godementPullbackLift f) (augDeg0 ι) (augDeg0 ι') θF (θ.f 0) hι)
    simp only [HomologicalComplex.comp_f] at h
    change (globalSections M).map ((CokernelCoresolution.complexHom (godementPullbackLift f) θF).f
        p) ≫
        (globalSections N).map (((godementResolution N).map (augDeg0 ι')).f p) =
      (globalSections M).map (((godementResolution M).map (augDeg0 ι)).f p) ≫
        (globalSections M).map ((CokernelCoresolution.complexHom (godementPullbackLift f) (θ.f 0)).f
            p)
    erw [gamma_push f]
    erw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (globalSections M).map h.symm
  haveI := (godementColAug K hK).quasiIso_augHom
  haveI := (godementDbl K).quasiIso_rowAugHom (godementRowAug F K ι)
  haveI := (godementColAug K' hK').quasiIso_augHom
  haveI := (godementDbl K').quasiIso_rowAugHom (godementRowAug F' K' ι')
  have e1 := (HomologicalComplex.homologyMap_comp _ _ n).symm.trans
    ((congrArg (fun g => HomologicalComplex.homologyMap g n) hcol).trans
      (HomologicalComplex.homologyMap_comp _ _ n))
  have e2 := (HomologicalComplex.homologyMap_comp _ _ n).symm.trans
    ((congrArg (fun g => HomologicalComplex.homologyMap g n) hrow).trans
      (HomologicalComplex.homologyMap_comp _ _ n))
  unfold cmp2
  haveI : IsIso (HomologicalComplex.homologyMap (godementColAug K hK).augHom n) :=
    (quasiIsoAt_iff_isIso_homologyMap _ n).1 inferInstance
  haveI : IsIso (HomologicalComplex.homologyMap ((godementDbl K).rowAugHom (godementRowAug F K ι))
      n) :=
    (quasiIsoAt_iff_isIso_homologyMap _ n).1 inferInstance
  haveI : IsIso (HomologicalComplex.homologyMap (godementColAug K' hK').augHom n) :=
    (quasiIsoAt_iff_isIso_homologyMap _ n).1 inferInstance
  haveI : IsIso (HomologicalComplex.homologyMap ((godementDbl K').rowAugHom (godementRowAug F' K'
      ι')) n) :=
    (quasiIsoAt_iff_isIso_homologyMap _ n).1 inferInstance
  exact iso_square (b := HomologicalComplex.homologyMap ((godementDbl K).rowAugHom (godementRowAug F
      K ι)) n)
    (c := HomologicalComplex.homologyMap (godementColAug K hK).augHom n)
    (b' := HomologicalComplex.homologyMap ((godementDbl K').rowAugHom (godementRowAug F' K' ι')) n)
    (c' := HomologicalComplex.homologyMap (godementColAug K' hK').augHom n)
    (HomologicalComplex.homologyMap (gammaMapF f F F' θF) n) (HomologicalComplex.homologyMap
        (gammaMap f K K' θ) n)
    (HomologicalComplex.homologyMap Ψ.totHom n) e2 e1

end Natural

private lemma isZero_godementSectionsDbl_X {T : TopCat.{u}} (F : TopCat.Sheaf AddCommGrpCat.{u} T)
    (i : ℤ)
    (hi : i ≠ 0) :
    IsZero ((godementSectionsDoubleComplex T
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F)).X i) :=
  (godementSections T).map_isZero (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi)

/-- The cohomology `H^n(T, F)` is the cohomology of `Γ(T, G^•(F))`. -/
private def sheafCohomologyIso {T : TopCat.{u}} (F : TopCat.Sheaf AddCommGrpCat.{u} T) (n : ℕ) :
    (sheafCohomology T n).obj F ≅
      (((globalSections T).mapHomologicalComplex _).obj ((godementResolution T).obj F)).homology
          n := by
  let D := godementSectionsDoubleComplex T ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
      F)
  haveI := isIso_colToTotal D (isZero_godementSectionsDbl_X F)
  refine (HomologicalComplex.homologyMapIso (asIso (colToTotal D (isZero_godementSectionsDbl_X
      F))).symm
    (n : ℤ)) ≪≫ ?_
  refine (HomologicalComplex.homologyMapIso ((godementSections T).mapIso
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F)) (n : ℤ)) ≪≫ ?_
  exact HomologicalComplex.extendHomologyIso
    (((globalSections T).mapHomologicalComplex _).obj ((godementResolution T).obj F))
    ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl

private lemma sheafCohomologyIso_hom {T : TopCat.{u}} (F : TopCat.Sheaf AddCommGrpCat.{u} T) (n : ℕ)
    :
    (sheafCohomologyIso F n).hom =
      HomologicalComplex.homologyMap (inv (colToTotal (godementSectionsDoubleComplex T
        ((HomologicalComplex.single (TopCat.Sheaf AddCommGrpCat.{u} T) (ComplexShape.up ℤ) 0).obj
            F))
          (isZero_godementSectionsDbl_X F))) n ≫
      (HomologicalComplex.extendHomologyIso (((globalSections T).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
          ((godementResolution T).obj F)) ComplexShape.embeddingUpNat
          (j := n) (j' := (n : ℤ)) rfl).hom := by
  haveI := isIso_colToTotal (godementSectionsDoubleComplex T
    ((HomologicalComplex.single (TopCat.Sheaf AddCommGrpCat.{u} T) (ComplexShape.up ℤ) 0).obj F))
    (isZero_godementSectionsDbl_X F)
  have h0 : HomologicalComplex.homologyMap ((godementSections T).map
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom) (n : ℤ) = 𝟙 _ := by
    have : (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom = 𝟙 F := rfl
    rw [this]
    erw [(godementSections T).map_id, HomologicalComplex.homologyMap_id]
  change HomologicalComplex.homologyMap (inv (colToTotal (godementSectionsDoubleComplex T
        ((HomologicalComplex.single (TopCat.Sheaf AddCommGrpCat.{u} T) (ComplexShape.up ℤ) 0).obj
            F))
          (isZero_godementSectionsDbl_X F))) (n : ℤ) ≫
    HomologicalComplex.homologyMap ((godementSections T).map
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom) (n : ℤ) ≫
    (HomologicalComplex.extendHomologyIso (((globalSections T).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
          ((godementResolution T).obj F)) ComplexShape.embeddingUpNat
          (j := n) (j' := (n : ℤ)) rfl).hom = _
  erw [h0, Category.id_comp]

private lemma homologyMap_inv_natural {X Y Z W : HomologicalComplex AddCommGrpCat.{u}
    (ComplexShape.up ℤ)}
    (cF : X ⟶ Z) (cF' : Y ⟶ W) [IsIso cF] [IsIso cF'] (T : Z ⟶ W) (P : X ⟶ Y)
    (h : cF ≫ T = P ≫ cF') (n : ℤ) :
    HomologicalComplex.homologyMap T n ≫ HomologicalComplex.homologyMap (inv cF') n =
      HomologicalComplex.homologyMap (inv cF) n ≫ HomologicalComplex.homologyMap P n := by
  have h2 : T ≫ inv cF' = inv cF ≫ P := by
    rw [IsIso.eq_inv_comp, ← Category.assoc, h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp, h2]

section F1

variable {M N : TopCat.{u}} (f : N ⟶ M)

private lemma complexHom_postcomp (f : N ⟶ M) {E : TopCat.Sheaf AddCommGrpCat.{u} M}
    {E' E'' : TopCat.Sheaf AddCommGrpCat.{u} N}
    (φ : E ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj E') (b : E' ⟶ E'') :
    CokernelCoresolution.complexHom (godementPullbackLift f) (φ ≫ (TopCat.Sheaf.pushforward
        AddCommGrpCat.{u} f).map b) =
      CokernelCoresolution.complexHom (godementPullbackLift f) φ ≫
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex _).map
            ((godementResolution N).map b) := by
  have h := CokernelCoresolution.complexFunctor_map_comp_complexHom (godementPullbackLift f) (𝟙 E) b
      φ
    (φ ≫ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map b) (by simp)
  rw [(CokernelCoresolution.complexFunctor (godementFunctor M) (godementUnit M)).map_id] at h
  erw [Category.id_comp] at h
  exact h

private lemma sheafCohomologyIso_natural (F : TopCat.Sheaf AddCommGrpCat.{u} M) (F' : TopCat.Sheaf
    AddCommGrpCat.{u} N)
    (g : (TopCat.Sheaf.pullback AddCommGrpCat.{u} f).obj F ⟶ F') (n : ℕ) :
    (sheafCohomologyIso F n).hom ≫ HomologicalComplex.homologyMap (gammaMapF f F F'
      ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app F ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map g)) n =
      sheafCohomologyPullback f F n ≫ (sheafCohomology N n).map g ≫ (sheafCohomologyIso F' n).hom :=
          by
  let s := (HomologicalComplex.singleMapHomologicalComplex (TopCat.Sheaf.pullback AddCommGrpCat.{u}
      f)
    (ComplexShape.up ℤ) 0).hom.app F
  let Φ : godementSectionsDoubleComplex M ((HomologicalComplex.single (TopCat.Sheaf
      AddCommGrpCat.{u} M)
      (ComplexShape.up ℤ) 0).obj F) ⟶ godementSectionsDoubleComplex N
        ((HomologicalComplex.single (TopCat.Sheaf AddCommGrpCat.{u} N) (ComplexShape.up ℤ) 0).obj
            F') :=
    godementSectionsDoubleComplexPullback f ((HomologicalComplex.single (TopCat.Sheaf
        AddCommGrpCat.{u} M)
      (ComplexShape.up ℤ) 0).obj F) ≫
    ((godementSections N).mapHomologicalComplex _).map s ≫
    ((godementSections N).mapHomologicalComplex _).map
      ((HomologicalComplex.single (TopCat.Sheaf AddCommGrpCat.{u} N) (ComplexShape.up ℤ) 0).map g)
  have hSC : sheafCohomologyPullback f F n ≫ (sheafCohomology N n).map g =
      HomologicalComplex.homologyMap (HomologicalComplex₂.total.map Φ (ComplexShape.up ℤ)) n := by
    have e : ∀ {A₁ A₂ A₃ A₄ : HomologicalComplex₂ AddCommGrpCat.{u} (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)}
        [A₁.HasTotal (ComplexShape.up ℤ)] [A₂.HasTotal (ComplexShape.up ℤ)]
        [A₃.HasTotal (ComplexShape.up ℤ)] [A₄.HasTotal (ComplexShape.up ℤ)]
        (a : A₁ ⟶ A₂) (b : A₂ ⟶ A₃) (c : A₃ ⟶ A₄),
        HomologicalComplex.homologyMap (HomologicalComplex₂.total.map a (ComplexShape.up ℤ)) n ≫
          HomologicalComplex.homologyMap (HomologicalComplex₂.total.map b (ComplexShape.up ℤ)) n ≫
          HomologicalComplex.homologyMap (HomologicalComplex₂.total.map c (ComplexShape.up ℤ)) n =
        HomologicalComplex.homologyMap (HomologicalComplex₂.total.map (a ≫ b ≫ c) (ComplexShape.up
            ℤ)) n := by
      intro A₁ A₂ A₃ A₄ _ _ _ _ a b c
      rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
        ← HomologicalComplex₂.total.map_comp, ← HomologicalComplex₂.total.map_comp]
    unfold sheafCohomologyPullback sheafCohomology
    rw [Category.assoc]
    exact e _ _ _
  have hkey := colToTotal_natural
    (godementSectionsDoubleComplex M ((HomologicalComplex.single (TopCat.Sheaf AddCommGrpCat.{u} M)
      (ComplexShape.up ℤ) 0).obj F))
    (godementSectionsDoubleComplex N ((HomologicalComplex.single (TopCat.Sheaf AddCommGrpCat.{u} N)
      (ComplexShape.up ℤ) 0).obj F'))
    (isZero_godementSectionsDbl_X F) (isZero_godementSectionsDbl_X F') Φ
  have hΦ0 : Φ.f 0 = HomologicalComplex.extendMap (gammaMapF f F F'
      ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app F ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map g)) ComplexShape.embeddingUpNat := by
    have h1 : gammaMapF f F F' ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
        f).unit.app F ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map g) =
        ((globalSections M).mapHomologicalComplex _).map
          (CokernelCoresolution.complexHom (godementPullbackLift f)
            ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app F)) ≫
        ((globalSections M).mapHomologicalComplex _).map
          (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex _).map
            ((godementResolution N).map g)) := by
      unfold gammaMapF
      rw [complexHom_postcomp]
      exact Functor.map_comp _ _ _
    rw [h1]
    refine Eq.trans ?_ (HomologicalComplex.extendMap_comp _ _ _).symm
    have hs0 : s.f 0 = 𝟙 _ := rfl
    have hg0 : ((HomologicalComplex.single (TopCat.Sheaf AddCommGrpCat.{u} N) (ComplexShape.up ℤ)
        0).map g).f 0 = g := rfl
    have hd : Φ.f 0 = godementSectionsPullback f F ≫ (godementSections N).map g := by
      change godementSectionsPullback f F ≫ (godementSections N).map (s.f 0) ≫
        (godementSections N).map (((HomologicalComplex.single (TopCat.Sheaf AddCommGrpCat.{u} N)
          (ComplexShape.up ℤ) 0).map g).f 0) = _
      rw [hs0, hg0]
      erw [(godementSections N).map_id, Category.id_comp]
      rfl
    exact hd
  haveI hc1 := isIso_colToTotal (godementSectionsDoubleComplex M
    ((HomologicalComplex.single (TopCat.Sheaf AddCommGrpCat.{u} M) (ComplexShape.up ℤ) 0).obj F))
    (isZero_godementSectionsDbl_X F)
  haveI hc2 := isIso_colToTotal (godementSectionsDoubleComplex N
    ((HomologicalComplex.single (TopCat.Sheaf AddCommGrpCat.{u} N) (ComplexShape.up ℤ) 0).obj F'))
    (isZero_godementSectionsDbl_X F')
  rw [← Category.assoc, hSC]
  have hH := congrArg (fun t => HomologicalComplex.homologyMap t (n : ℤ)) hkey
  simp only [HomologicalComplex.homologyMap_comp] at hH
  have hnat := HomologicalComplex.extendHomologyIso_hom_naturality
    (gammaMapF f F F' ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app F ≫
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map g)) ComplexShape.embeddingUpNat
    (j := n) (j' := (n : ℤ)) rfl
  have hX : HomologicalComplex.homologyMap (HomologicalComplex₂.total.map Φ (ComplexShape.up ℤ)) (n
      : ℤ) ≫
      HomologicalComplex.homologyMap (inv (colToTotal (godementSectionsDoubleComplex N
        ((HomologicalComplex.single (TopCat.Sheaf AddCommGrpCat.{u} N) (ComplexShape.up ℤ) 0).obj
            F'))
        (isZero_godementSectionsDbl_X F'))) (n : ℤ) =
      HomologicalComplex.homologyMap (inv (colToTotal (godementSectionsDoubleComplex M
        ((HomologicalComplex.single (TopCat.Sheaf AddCommGrpCat.{u} M) (ComplexShape.up ℤ) 0).obj
            F))
        (isZero_godementSectionsDbl_X F))) (n : ℤ) ≫ HomologicalComplex.homologyMap (Φ.f 0) (n :
            ℤ) :=
    homologyMap_inv_natural _ _ _ _ hkey (n : ℤ)
  have e1 : (HomologicalComplex.extendHomologyIso (((globalSections M).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj
          ((godementResolution M).obj F)) ComplexShape.embeddingUpNat
          (j := n) (j' := (n : ℤ)) rfl).hom ≫ HomologicalComplex.homologyMap (gammaMapF f F F'
      ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app F ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map g)) n =
      HomologicalComplex.homologyMap (Φ.f 0) (n : ℤ) ≫
        (HomologicalComplex.extendHomologyIso (((globalSections N).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj
          ((godementResolution N).obj F')) ComplexShape.embeddingUpNat
          (j := n) (j' := (n : ℤ)) rfl).hom := by
    rw [hΦ0]
    exact hnat.symm
  rw [sheafCohomologyIso_hom F n, sheafCohomologyIso_hom F' n]
  exact ((Category.assoc _ _ _).trans ((congrArg (fun x => _ ≫ x) e1).trans (Category.assoc _ _
      _).symm)).trans
    ((congrArg (fun x => x ≫ _) hX.symm).trans (Category.assoc _ _ _))

end F1

/-- The `n`-chains of `X` of `ℤ`-coefficients (Mathlib's singular chain complex). -/
private abbrev singChains (X : TopCat.{u}) : ChainComplex AddCommGrpCat.{u} ℕ :=
  ((singularChainComplexFunctor AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift ℤ))).obj X

section CochainBridge

open scoped Simplicial

/-- The value of an `A`-valued cochain on a singular simplex. -/
private def cochainEval (A : AddCommGrpCat.{u}) (X : TopCat.{u}) (n : ℕ)
    (φ : (singChains X).X n ⟶ A) (σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌)) : A :=
  (Sigma.ι (fun _ ↦ AddCommGrpCat.of (ULift ℤ)) σ ≫ φ).hom ⟨1⟩

private def cochainOfFun (A : AddCommGrpCat.{u}) (X : TopCat.{u}) (n : ℕ)
    (g : (TopCat.toSSet.obj X).obj (op ⦋n⦌) → A) : (singChains X).X n ⟶ A :=
  Sigma.desc fun σ ↦ AddCommGrpCat.ofHom
    { toFun := fun k ↦ k.down • g σ
      map_zero' := by simp
      map_add' := fun a b ↦ by simp [add_smul] }

private def cochainEquiv (A : AddCommGrpCat.{u}) (X : TopCat.{u}) (n : ℕ) :
    ((singChains X).X n ⟶ A) ≃ ((TopCat.toSSet.obj X).obj (op ⦋n⦌) → A) where
  toFun φ := cochainEval A X n φ
  invFun g := cochainOfFun A X n g
  left_inv φ := by
    refine Sigma.hom_ext _ _ fun σ ↦ AddCommGrpCat.hom_ext (AddMonoidHom.ext fun k ↦ ?_)
    change (Sigma.ι (fun _ ↦ AddCommGrpCat.of (ULift ℤ)) σ ≫ cochainOfFun A X n (cochainEval A X n
        φ)).hom k = _
    rw [cochainOfFun, Sigma.ι_desc]
    change k.down • cochainEval A X n φ σ = (Sigma.ι (fun _ ↦ AddCommGrpCat.of (ULift ℤ)) σ ≫ φ).hom
        k
    have : k = k.down • (⟨1⟩ : ULift ℤ) := by ext; simp
    conv_rhs => rw [this]
    rw [map_zsmul]
    rfl
  right_inv g := by
    funext σ
    change (Sigma.ι (fun _ ↦ AddCommGrpCat.of (ULift ℤ)) σ ≫ cochainOfFun A X n g).hom ⟨1⟩ = g σ
    simp [cochainOfFun]

private lemma hom_sum' {M N : AddCommGrpCat.{u}} {ι : Type*} (s : Finset ι) (f : ι → (M ⟶ N)) (x :
    M) :
    (∑ i ∈ s, f i).hom x = ∑ i ∈ s, (f i).hom x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, AddCommGrpCat.hom_add]; simp
      [ih]

@[reassoc]
private lemma ι_singChains_d (X : TopCat.{u}) (n : ℕ) (σ : (TopCat.toSSet.obj X).obj (op ⦋n + 1⦌)) :
    Sigma.ι (fun _ ↦ AddCommGrpCat.of (ULift ℤ)) σ ≫ (singChains X).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        Sigma.ι (fun _ ↦ AddCommGrpCat.of (ULift ℤ)) ((TopCat.toSSet.obj X).δ i σ) := by
  have : (singChains X).d (n + 1) n = ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
      SimplicialObject.δ (TopCat.toSSet.obj X ⋙
        (sigmaConst : AddCommGrpCat.{u} ⥤ Type u ⥤ AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift ℤ))) i :=
    AlternatingFaceMapComplex.obj_d_eq _ n
  rw [this]
  erw [Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  erw [Preadditive.comp_zsmul]
  congr 1
  simp only [SimplicialObject.δ, sigmaConst]
  erw [Sigma.ι_comp_map', Category.id_comp]

private lemma cochainEval_d (A : AddCommGrpCat.{u}) (X : TopCat.{u}) (n : ℕ)
    (φ : (singChains X).X n ⟶ A) (σ : (TopCat.toSSet.obj X).obj (op ⦋n + 1⦌)) :
    cochainEval A X (n + 1) ((singChains X).d (n + 1) n ≫ φ) σ =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • cochainEval A X n φ ((TopCat.toSSet.obj X).δ i σ) :=
          by
  unfold cochainEval
  change (Sigma.ι (fun _ ↦ AddCommGrpCat.of (ULift ℤ)) σ ≫ (singChains X).d (n + 1) n ≫ φ).hom ⟨1⟩ =
      _
  erw [ι_singChains_d_assoc, Preadditive.sum_comp]
  rw [hom_sum']
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  erw [Preadditive.zsmul_comp]
  simp
  rfl

private lemma cochainEval_map (A : AddCommGrpCat.{u}) {X Y : TopCat.{u}} (f : Y ⟶ X) (n : ℕ)
    (φ : (singChains X).X n ⟶ A) (σ : (TopCat.toSSet.obj Y).obj (op ⦋n⦌)) :
    cochainEval A Y n ((((singularChainComplexFunctor AddCommGrpCat.{u}).obj (AddCommGrpCat.of
        (ULift ℤ))).map f).f n ≫ φ) σ =
      cochainEval A X n φ ((TopCat.toSSet.map f).app _ σ) := by
  unfold cochainEval
  change (Sigma.ι (fun _ ↦ AddCommGrpCat.of (ULift ℤ)) σ ≫
    (((singularChainComplexFunctor AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift ℤ))).map f).f n ≫
        φ).hom ⟨1⟩ = _
  have : Sigma.ι (fun _ ↦ AddCommGrpCat.of (ULift ℤ)) σ ≫
        (((singularChainComplexFunctor AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift ℤ))).map f).f
            n =
      Sigma.ι (fun _ ↦ AddCommGrpCat.of (ULift ℤ)) ((TopCat.toSSet.map f).app _ σ) := by
    dsimp [singularChainComplexFunctor, SSet.chainComplexFunctor]
    simp [Sigma.ι_comp_map']
  erw [← Category.assoc, this]
  rfl

end CochainBridge

section CochainBridge2

open scoped Simplicial

/-- The singular cochain complex `Hom(C_•(Y; ℤ), A)`. -/
private abbrev singCochains (A : AddCommGrpCat.{u}) (Y : TopCat.{u}) : CochainComplex
    AddCommGrpCat.{u} ℕ :=
  ((preadditiveYoneda.obj A).mapHomologicalComplex _).obj
    ((HomologicalComplex.opFunctor _ _).obj (op (singChains Y)))

/-- The one-point space. -/
private abbrev pt : TopCat.{u} := TopCat.of PUnit.{u + 1}

open scoped Simplicial in
private instance (n : ℕ) : Unique ((TopCat.toSSet.obj pt).obj (op ⦋n⦌)) :=
  haveI : Unique C(Convexity.StdSimplex ℝ (Fin ((op ⦋n⦌).unop.len + 1)), (pt : Type u)) :=
    ⟨⟨⟨fun _ => PUnit.unit, continuous_const⟩⟩, fun f => by ext x⟩
  (TopCat.toSSetObjEquiv pt (op ⦋n⦌)).unique

open scoped Simplicial in
private lemma pt_eval_d (A : AddCommGrpCat.{u}) (m : ℕ) (φ : (singChains pt).X m ⟶ A) :
    cochainEval A pt (m + 1) ((singChains pt).d (m + 1) m ≫ φ) default =
      (if m % 2 = 0 then (0 : ℤ) else 1) • cochainEval A pt m φ default := by
  have h : ∑ i : Fin (m + 2), (-1 : ℤ) ^ (i : ℕ) = if m % 2 = 0 then 0 else 1 := by
    rw [Fin.sum_neg_one_pow]; simp [Nat.even_add, Nat.even_iff]
  rw [cochainEval_d, ← h, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Subsingleton.elim ((TopCat.toSSet.obj pt).δ i default) default]

private lemma cochainEval_injective (A : AddCommGrpCat.{u}) (X : TopCat.{u}) (n : ℕ) :
    Function.Injective (cochainEval A X n) := (cochainEquiv A X n).injective

/-- The cohomology of a point vanishes in positive degrees. -/
private lemma pt_coboundary (A : AddCommGrpCat.{u}) (n : ℕ) (z : (singChains pt).X (n + 1) ⟶ A)
    (hz : (singChains pt).d (n + 2) (n + 1) ≫ z = 0) :
    ∃ w : (singChains pt).X n ⟶ A, (singChains pt).d (n + 1) n ≫ w = z := by
  have h1 := pt_eval_d A (n + 1) z
  rw [hz] at h1
  have h0 : cochainEval A pt (n + 2) (0 : (singChains pt).X (n + 2) ⟶ A) default = 0 := by
    rfl
  rw [h0] at h1
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · -- n even: `z` itself vanishes
    refine ⟨0, ?_⟩
    have h2 : cochainEval A pt (n + 1) z default = 0 := by
      have : (n + 1) % 2 ≠ 0 := by omega
      rw [if_neg this] at h1
      simpa using h1.symm
    refine cochainEval_injective A pt (n + 1) ?_
    funext σ
    rw [Subsingleton.elim σ default]
    change cochainEval A pt (n + 1) _ default = cochainEval A pt (n + 1) z default
    rw [comp_zero, h2]
    rfl
  · refine ⟨cochainOfFun A pt n (fun _ => cochainEval A pt (n + 1) z default), ?_⟩
    refine cochainEval_injective A pt (n + 1) ?_
    funext σ
    rw [Subsingleton.elim σ default, pt_eval_d]
    have : (if n % 2 = 0 then (0 : ℤ) else 1) = 1 := by simp [show n % 2 ≠ 0 by omega]
    rw [this, one_smul]
    exact congrFun ((cochainEquiv A pt n).right_inv (fun _ => cochainEval A pt (n + 1) z default))
        default

/-- The pullback of a chain along a continuous map. -/
private abbrev chainMap {Z Y : TopCat.{u}} (i : Z ⟶ Y) :=
  ((singularChainComplexFunctor AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift ℤ))).map i

private lemma nullhomotopic_coboundary (A : AddCommGrpCat.{u}) {Z Y : TopCat.{u}} (i : Z ⟶ Y)
    (hi : ContinuousMap.Nullhomotopic i.hom) (n : ℕ) (z : (singChains Y).X (n + 1) ⟶ A)
    (hz : (singChains Y).d (n + 2) (n + 1) ≫ z = 0) :
    ∃ b : (singChains Z).X n ⟶ A, (chainMap i).f (n + 1) ≫ z = (singChains Z).d (n + 1) n ≫ b := by
  obtain ⟨y0, ⟨H⟩⟩ := hi
  let q : Z ⟶ pt := TopCat.ofHom ⟨fun _ => PUnit.unit, continuous_const⟩
  let j : pt ⟶ Y := TopCat.ofHom ⟨fun _ => y0, continuous_const⟩
  have hc : (TopCat.ofHom (ContinuousMap.const Z y0) : Z ⟶ Y) = q ≫ j := rfl
  let Hh := TopCat.Homotopy.singularChainComplexFunctorObjMap (C := AddCommGrpCat.{u})
    (f := i) (g := TopCat.ofHom (ContinuousMap.const Z y0)) H (AddCommGrpCat.of (ULift ℤ))
  have hcomm := Hh.comm (n + 1)
  rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex] at hcomm
  have hw : (singChains pt).d (n + 2) (n + 1) ≫ (chainMap j).f (n + 1) ≫ z = 0 := by
    rw [← Category.assoc, ← (chainMap j).comm (n + 2) (n + 1), Category.assoc, hz, comp_zero]
  obtain ⟨w', hw'⟩ := pt_coboundary A n _ hw
  refine ⟨Hh.hom n (n + 1) ≫ z + (chainMap q).f n ≫ w', ?_⟩
  have hg : (chainMap (TopCat.ofHom (ContinuousMap.const Z y0) : Z ⟶ Y)).f (n + 1) =
      (chainMap q).f (n + 1) ≫ (chainMap j).f (n + 1) := by
    rw [hc]
    have hm : chainMap (q ≫ j) = chainMap q ≫ chainMap j := Functor.map_comp _ q j
    rw [hm, HomologicalComplex.comp_f]
  have e1 : (singChains Z).d (n + 1) n ≫ (chainMap q).f n ≫ w' =
      (chainMap q).f (n + 1) ≫ (chainMap j).f (n + 1) ≫ z := by
    rw [← Category.assoc, ← (chainMap q).comm (n + 1) n, Category.assoc, hw']
  rw [hcomm, hg]
  simp only [Preadditive.add_comp, Category.assoc, Preadditive.comp_add]
  erw [hz, comp_zero, add_zero, e1]

private lemma nullhomotopic_const (A : AddCommGrpCat.{u}) {Z Y : TopCat.{u}} (i : Z ⟶ Y)
    (hi : ContinuousMap.Nullhomotopic i.hom) (z : (singChains Y).X 0 ⟶ A)
    (hz : (singChains Y).d 1 0 ≫ z = 0) :
    ∃ a : A, ∀ σ, cochainEval A Z 0 ((chainMap i).f 0 ≫ z) σ = a := by
  obtain ⟨y0, ⟨H⟩⟩ := hi
  let q : Z ⟶ pt := TopCat.ofHom ⟨fun _ => PUnit.unit, continuous_const⟩
  let j : pt ⟶ Y := TopCat.ofHom ⟨fun _ => y0, continuous_const⟩
  have hc : (TopCat.ofHom (ContinuousMap.const Z y0) : Z ⟶ Y) = q ≫ j := rfl
  let Hh := TopCat.Homotopy.singularChainComplexFunctorObjMap (C := AddCommGrpCat.{u})
    (f := i) (g := TopCat.ofHom (ContinuousMap.const Z y0)) H (AddCommGrpCat.of (ULift ℤ))
  have hcomm := Hh.comm 0
  rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex] at hcomm
  have hg : (chainMap (TopCat.ofHom (ContinuousMap.const Z y0) : Z ⟶ Y)).f 0 =
      (chainMap q).f 0 ≫ (chainMap j).f 0 := by
    rw [hc]
    have hm : chainMap (q ≫ j) = chainMap q ≫ chainMap j := Functor.map_comp _ q j
    rw [hm, HomologicalComplex.comp_f]
  refine ⟨cochainEval A pt 0 ((chainMap j).f 0 ≫ z) default, fun σ => ?_⟩
  have h1 : (chainMap i).f 0 ≫ z = (chainMap q).f 0 ≫ (chainMap j).f 0 ≫ z := by
    rw [hcomm, hg]
    simp only [Preadditive.add_comp, Category.assoc, Preadditive.comp_add, zero_add]
    erw [hz, comp_zero, zero_add]
  rw [h1, cochainEval_map]
  congr 1

end CochainBridge2

/-- The presheaf complex `U ↦ Hom(C_•(U; ℤ), A)` of singular cochains, as a functor from
`(Opens X)ᵒᵖ` to cochain complexes. -/
private def singCochainPresheaf (A : AddCommGrpCat.{u}) (X : TopCat.{u}) :
    (Opens X)ᵒᵖ ⥤ CochainComplex AddCommGrpCat.{u} ℕ :=
  (Opens.toTopCat X).op ⋙
    ((singularChainComplexFunctor AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift ℤ))).op ⋙
      HomologicalComplex.opFunctor _ _ ⋙ (preadditiveYoneda.obj A).mapHomologicalComplex _

private lemma exists_open_nullhomotopic {X : TopCat.{u}} (hX : LocallyContractibleSpace X) (x : X)
    (U : Opens X) (hx : x ∈ U) :
    ∃ (V : Opens X) (h : V ≤ U), x ∈ V ∧
      ContinuousMap.Nullhomotopic ((Opens.toTopCat X).map (homOfLE h)).hom := by
  obtain ⟨V, hVU, hV, hnull⟩ := hX x (U : Set X) (U.isOpen.mem_nhds hx)
  refine ⟨⟨interior V, isOpen_interior⟩, (interior_subset.trans hVU), mem_interior_iff_mem_nhds.2
      hV, ?_⟩
  have := hnull.comp_left (ContinuousMap.inclusion (interior_subset : interior V ⊆ V))
  exact this

private lemma restrict_coboundary {X : TopCat.{u}} (A : AddCommGrpCat.{u}) (hX :
    LocallyContractibleSpace X)
    (x : X) (U : Opens X) (hx : x ∈ U) (n : ℕ)
    (z : ((singCochainPresheaf A X).obj (op U)).X (n + 1))
    (hz : ((singCochainPresheaf A X).obj (op U)).d (n + 1) (n + 2) z = 0) :
    ∃ (V : Opens X) (h : V ≤ U), x ∈ V ∧ ∃ b : ((singCochainPresheaf A X).obj (op V)).X n,
      ((singCochainPresheaf A X).map (homOfLE h).op).f (n + 1) z =
        ((singCochainPresheaf A X).obj (op V)).d n (n + 1) b := by
  obtain ⟨V, h, hxV, hnull⟩ := exists_open_nullhomotopic hX x U hx
  obtain ⟨b, hb⟩ := nullhomotopic_coboundary A ((Opens.toTopCat X).map (homOfLE h)) hnull n z hz
  exact ⟨V, h, hxV, b, hb⟩

private lemma restrict_const {X : TopCat.{u}} (A : AddCommGrpCat.{u}) (hX : LocallyContractibleSpace
    X)
    (x : X) (U : Opens X) (hx : x ∈ U)
    (z : ((singCochainPresheaf A X).obj (op U)).X 0)
    (hz : ((singCochainPresheaf A X).obj (op U)).d 0 1 z = 0) :
    ∃ (V : Opens X) (h : V ≤ U), x ∈ V ∧ ∃ a : A, ∀ σ,
      cochainEval A (Opens.toTopCat X |>.obj V) 0
        (((singCochainPresheaf A X).map (homOfLE h).op).f 0 z) σ = a := by
  obtain ⟨V, h, hxV, hnull⟩ := exists_open_nullhomotopic hX x U hx
  obtain ⟨a, ha⟩ := nullhomotopic_const A ((Opens.toTopCat X).map (homOfLE h)) hnull z hz
  exact ⟨V, h, hxV, a, ha⟩

/-- The `p`-th term of the presheaf complex of singular cochains, `U ↦ Hom(C_p(U; ℤ), A)`. -/
private def singCochainTerm (A : AddCommGrpCat.{u}) (X : TopCat.{u}) (p : ℕ) :
    TopCat.Presheaf AddCommGrpCat.{u} X :=
  singCochainPresheaf A X ⋙ HomologicalComplex.eval _ _ p

private def singCochainTermD (A : AddCommGrpCat.{u}) (X : TopCat.{u}) (p : ℕ) :
    singCochainTerm A X p ⟶ singCochainTerm A X (p + 1) where
  app U := ((singCochainPresheaf A X).obj U).d p (p + 1)
  naturality _ _ i := ((singCochainPresheaf A X).map i).comm p (p + 1)

/-- The complex of presheaves of singular cochains. -/
private def singCochainPresheafComplex (A : AddCommGrpCat.{u}) (X : TopCat.{u}) :
    CochainComplex (TopCat.Presheaf AddCommGrpCat.{u} X) ℕ :=
  CochainComplex.of (singCochainTerm A X) (singCochainTermD A X) (fun p => by
    refine NatTrans.ext (funext fun U => ?_)
    exact ((singCochainPresheaf A X).obj U).d_comp_d p (p + 1) (p + 2))

/-- The complex of sheafified singular cochains `𝒮^•`. -/
private def singCochainSheaves (A : AddCommGrpCat.{u}) (X : TopCat.{u}) :
    CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℕ :=
  ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapHomologicalComplex _).obj
    (singCochainPresheafComplex A X)

section SheafifyStalks

variable {X : TopCat.{u}}

/-- the sheafified complex -/
private abbrev sheafifyComplex (P : CochainComplex (TopCat.Presheaf AddCommGrpCat.{u} X) ℕ) :
    CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℕ :=
  ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapHomologicalComplex _).obj P

/-- the sheafification as a `TopCat.Sheaf` -/
private abbrev sheafify (F : TopCat.Presheaf AddCommGrpCat.{u} X) : TopCat.Sheaf AddCommGrpCat.{u}
    X :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj F

/-- stalk comparison -/
private def stalkTau (x : X) (F : TopCat.Presheaf AddCommGrpCat.{u} X) :
    F.stalk x ⟶ (sheafify F).presheaf.stalk x :=
  (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
    ((sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{u}).unit.app F)

private instance (x : X) (F : TopCat.Presheaf AddCommGrpCat.{u} X) : IsIso (stalkTau x F) :=
  TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x _ F

private lemma stalkTau_naturality (x : X) {F G : TopCat.Presheaf AddCommGrpCat.{u} X} (η : F ⟶ G) :
    stalkTau x F ≫ (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map η).hom =
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map η ≫ stalkTau x G := by
  unfold stalkTau
  have hnat := (sheafificationAdjunction (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}).unit.naturality η
  exact (Functor.map_comp (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) _ _).symm.trans
    ((congrArg (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map hnat.symm).trans
      (Functor.map_comp (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) _ _))

private lemma exactAt_sheafifyComplex (P : CochainComplex (TopCat.Presheaf AddCommGrpCat.{u} X) ℕ)
    (n : ℕ)
    (h : ∀ (U : Opens X) (x : X) (hx : x ∈ U) (z : (P.X (n + 1)).obj (op U)),
      (P.d (n + 1) (n + 2)).app (op U) z = 0 →
        ∃ (V : Opens X) (hV : V ≤ U), x ∈ V ∧ ∃ b : (P.X n).obj (op V),
          (P.X (n + 1)).map (homOfLE hV).op z = (P.d n (n + 1)).app (op V) b) :
    (sheafifyComplex P).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp),
    TopCat.Sheaf.exact_iff_stalkFunctor_map_exact]
  intro x
  rw [ShortComplex.ab_exact_iff]
  intro e he
  have hsurj : ∀ (F : TopCat.Presheaf AddCommGrpCat.{u} X), Function.Surjective (stalkTau x F) :=
      fun F =>
    ((ConcreteCategory.isIso_iff_bijective _).1 inferInstance).2
  have hinj : ∀ (F : TopCat.Presheaf AddCommGrpCat.{u} X), Function.Injective (stalkTau x F) := fun
      F =>
    ((ConcreteCategory.isIso_iff_bijective _).1 inferInstance).1
  obtain ⟨e', rfl⟩ := hsurj (P.X (n + 1)) e
  obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq (P.X (n + 1)) e'
  have hg : ∀ w, (ConcreteCategory.hom ((HomologicalComplex.sc' (sheafifyComplex P) n (n + 1) (n +
      2)).map
      (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
          x)).g)
        (stalkTau x (P.X (n + 1)) w) =
      stalkTau x (P.X (n + 2)) ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (P.d (n + 1)
          (n + 2)) w) :=
    fun w => ConcreteCategory.congr_hom (stalkTau_naturality x (P.d (n + 1) (n + 2))) w
  have hf : ∀ w, (ConcreteCategory.hom ((HomologicalComplex.sc' (sheafifyComplex P) n (n + 1) (n +
      2)).map
      (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
          x)).f)
        (stalkTau x (P.X n) w) =
      stalkTau x (P.X (n + 1)) ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (P.d n (n +
          1)) w) :=
    fun w => ConcreteCategory.congr_hom (stalkTau_naturality x (P.d n (n + 1))) w
  rw [hg] at he
  have he1 : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (P.d (n + 1) (n + 2))
      ((P.X (n + 1)).germ U x hxU s) = 0 := hinj _ (he.trans (map_zero _).symm)
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at he1
  have he2 : (P.X (n + 2)).germ U x hxU ((P.d (n + 1) (n + 2)).app (op U) s) =
      (P.X (n + 2)).germ U x hxU 0 := he1.trans (map_zero _).symm
  obtain ⟨W, hxW, iU, iV, hW⟩ := TopCat.Presheaf.germ_eq _ x hxU hxU _ _ he2
  have hd0 : (ConcreteCategory.hom ((P.d (n + 1) (n + 2)).app (op W)))
      ((ConcreteCategory.hom ((P.X (n + 1)).map iU.op)) s) = 0 := by
    have hn := ConcreteCategory.congr_hom ((P.d (n + 1) (n + 2)).naturality iU.op) s
    refine hn.trans (hW.trans (map_zero _))
  obtain ⟨V, hV, hxV, b, hb⟩ := h W x hxW _ hd0
  refine ⟨stalkTau x (P.X n) ((P.X n).germ V x hxV b), ?_⟩
  rw [hf, TopCat.Presheaf.stalkFunctor_map_germ_apply, ← hb]
  congr 1
  erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]

end SheafifyStalks

/-- The sheafified singular cochain complex is exact in positive degrees when `X` is locally
contractible. -/
private theorem singCochainSheaves_exactAt (A : AddCommGrpCat.{u}) (X : TopCat.{u})
    (hX : LocallyContractibleSpace X) (n : ℕ) : (singCochainSheaves A X).ExactAt (n + 1) :=
  exactAt_sheafifyComplex (singCochainPresheafComplex A X) n (fun U x hx z hz => by
    have hz' : ((singCochainPresheaf A X).obj (op U)).d (n + 1) (n + 2) z = 0 := by
      have e : (singCochainPresheafComplex A X).d (n + 1) (n + 2) = singCochainTermD A X (n + 1) :=
        CochainComplex.of_d _ _ _
      rw [e] at hz
      exact hz
    obtain ⟨V, h, hxV, b, hb⟩ := restrict_coboundary A hX x U hx n z hz'
    refine ⟨V, h, hxV, b, ?_⟩
    have e : (singCochainPresheafComplex A X).d n (n + 1) = singCochainTermD A X n :=
      CochainComplex.of_d _ _ _
    rw [e]
    exact hb)

section ConstantAugmentation

open scoped Simplicial

/-- The constant `0`-cochain with value `a`. -/
private def constCochain (A : AddCommGrpCat.{u}) (Y : TopCat.{u}) (a : A) : (singChains Y).X 0 ⟶
    A :=
  cochainOfFun A Y 0 (fun _ => a)

private lemma cochainEval_constCochain (A : AddCommGrpCat.{u}) (Y : TopCat.{u}) (a : A)
    (σ : (TopCat.toSSet.obj Y).obj (op ⦋0⦌)) : cochainEval A Y 0 (constCochain A Y a) σ = a :=
  congrFun ((cochainEquiv A Y 0).right_inv (fun _ => a)) σ

private lemma cochainEval_add (A : AddCommGrpCat.{u}) (Y : TopCat.{u}) (n : ℕ)
    (φ ψ : (singChains Y).X n ⟶ A) (σ : (TopCat.toSSet.obj Y).obj (op ⦋n⦌)) :
    cochainEval A Y n (φ + ψ) σ = cochainEval A Y n φ σ + cochainEval A Y n ψ σ := by
  unfold cochainEval
  rfl

/-- The augmentation of the constant presheaf into the `0`-cochains: `a ↦ (σ ↦ a)`. -/
private def constToCochain (A : AddCommGrpCat.{u}) (X : TopCat.{u}) :
    (Functor.const (Opens X)ᵒᵖ).obj A ⟶ singCochainTerm A X 0 where
  app U := AddCommGrpCat.ofHom
    { toFun := fun a => constCochain A (Opens.toTopCat X |>.obj U.unop) a
      map_zero' := by
        refine cochainEval_injective A _ 0 (funext fun σ => ?_)
        rw [cochainEval_constCochain]; rfl
      map_add' := fun a b => by
        refine cochainEval_injective A _ 0 (funext fun σ => ?_)
        rw [cochainEval_constCochain]
        erw [cochainEval_add, cochainEval_constCochain, cochainEval_constCochain] }
  naturality U V i := by
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun a => ?_)
    refine cochainEval_injective A _ 0 (funext fun σ => ?_)
    change cochainEval A _ 0 (constCochain A _ a) σ =
      cochainEval A _ 0 ((chainMap ((Opens.toTopCat X).map i.unop)).f 0 ≫ constCochain A _ a) σ
    rw [cochainEval_map, cochainEval_constCochain, cochainEval_constCochain]

private lemma constToCochain_comp_d (A : AddCommGrpCat.{u}) (X : TopCat.{u}) :
    constToCochain A X ≫ singCochainTermD A X 0 = 0 := by
  refine NatTrans.ext (funext fun U => ?_)
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun a => ?_)
  refine cochainEval_injective A _ 1 (funext fun σ => ?_)
  change cochainEval A _ 1 ((singChains _).d 1 0 ≫ constCochain A _ a) σ = cochainEval A _ 1 0 σ
  rw [cochainEval_d]
  have h0 : cochainEval A _ 1 (0 : (singChains _).X 1 ⟶ A) σ = 0 := rfl
  rw [h0, Fin.sum_univ_two]
  simp only [cochainEval_constCochain]
  simp

/-- The constant sheaf. -/
private abbrev constSheaf (A : AddCommGrpCat.{u}) (X : TopCat.{u}) : TopCat.Sheaf AddCommGrpCat.{u}
    X :=
  (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj A

/-- The augmentation `A_X ⟶ 𝒮^0`, as the sheafification of `constToCochain`. -/
private def constAugDeg0 (A : AddCommGrpCat.{u}) (X : TopCat.{u}) :
    constSheaf A X ⟶ (singCochainSheaves A X).X 0 :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map (constToCochain A X)

private lemma constAugDeg0_comp_d (A : AddCommGrpCat.{u}) (X : TopCat.{u}) :
    constAugDeg0 A X ≫ (singCochainSheaves A X).d 0 1 = 0 := by
  have e : (singCochainSheaves A X).d 0 1 =
      (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map (singCochainTermD A X
          0) :=
    congrArg (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
      (show (singCochainPresheafComplex A X).d 0 1 = singCochainTermD A X 0 by
        simp only [singCochainPresheafComplex]
        exact CochainComplex.of_d _ _ _)
  have h : (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
      (constToCochain A X ≫ singCochainTermD A X 0) = 0 := by
    rw [constToCochain_comp_d, Functor.map_zero]
  rw [e]
  exact (Functor.map_comp _ _ _).symm.trans h

/-- The augmentation `A_X[0] ⟶ 𝒮^•`. -/
private def constAug (A : AddCommGrpCat.{u}) (X : TopCat.{u}) :
    (CochainComplex.single₀ (TopCat.Sheaf AddCommGrpCat.{u} X)).obj (constSheaf A X) ⟶
      singCochainSheaves A X :=
  HomologicalComplex.mkHomFromSingle (constAugDeg0 A X) (fun k hk => by
    have hk' : 0 + 1 = k := hk
    subst hk'; exact constAugDeg0_comp_d A X)

private lemma augDeg0_constAug (A : AddCommGrpCat.{u}) (X : TopCat.{u}) :
    augDeg0 (constAug A X) = constAugDeg0 A X := by
  unfold augDeg0 constAug
  erw [HomologicalComplex.mkHomFromSingle_f]
  simp

end ConstantAugmentation

/-- The sheaf-level exactness at degree `0`, on stalks. -/
private theorem exact_constAugDeg0 (A : AddCommGrpCat.{u}) (X : TopCat.{u})
    (hX : LocallyContractibleSpace X) :
    (ShortComplex.mk (constAugDeg0 A X) ((singCochainSheaves A X).d 0 1)
      (constAugDeg0_comp_d A X)).Exact := by
  rw [TopCat.Sheaf.exact_iff_stalkFunctor_map_exact]
  intro x
  rw [ShortComplex.ab_exact_iff]
  intro e he
  have hsurj : ∀ (F : TopCat.Presheaf AddCommGrpCat.{u} X), Function.Surjective (stalkTau x F) :=
      fun F =>
    ((ConcreteCategory.isIso_iff_bijective _).1 inferInstance).2
  have hinj : ∀ (F : TopCat.Presheaf AddCommGrpCat.{u} X), Function.Injective (stalkTau x F) := fun
      F =>
    ((ConcreteCategory.isIso_iff_bijective _).1 inferInstance).1
  obtain ⟨e', rfl⟩ := hsurj (singCochainTerm A X 0) e
  obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq (singCochainTerm A X 0) e'
  have hg : ∀ w, (ConcreteCategory.hom ((ShortComplex.mk (constAugDeg0 A X) ((singCochainSheaves A
      X).d 0 1)
      (constAugDeg0_comp_d A X)).map
      (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
          x)).g)
        (stalkTau x (singCochainTerm A X 0) w) =
      stalkTau x (singCochainTerm A X 1)
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (singCochainTermD A X 0) w) :=
    fun w => ConcreteCategory.congr_hom (stalkTau_naturality x (singCochainTermD A X 0)) w
  have hf : ∀ w, (ConcreteCategory.hom ((ShortComplex.mk (constAugDeg0 A X) ((singCochainSheaves A
      X).d 0 1)
      (constAugDeg0_comp_d A X)).map
      (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
          x)).f)
        (stalkTau x ((Functor.const (Opens X)ᵒᵖ).obj A) w) =
      stalkTau x (singCochainTerm A X 0)
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (constToCochain A X) w) :=
    fun w => ConcreteCategory.congr_hom (stalkTau_naturality x (constToCochain A X)) w
  rw [hg] at he
  have he1 : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (singCochainTermD A X 0)
      ((singCochainTerm A X 0).germ U x hxU s) = 0 := hinj _ (he.trans (map_zero _).symm)
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at he1
  have he2 : (singCochainTerm A X 1).germ U x hxU ((singCochainTermD A X 0).app (op U) s) =
      (singCochainTerm A X 1).germ U x hxU 0 := he1.trans (map_zero _).symm
  obtain ⟨W, hxW, iU, iV, hW⟩ := TopCat.Presheaf.germ_eq _ x hxU hxU _ _ he2
  have hd0 : ConcreteCategory.hom ((singCochainTermD A X 0).app (op W))
      ((ConcreteCategory.hom ((singCochainTerm A X 0).map iU.op)) s) = 0 := by
    have hn := ConcreteCategory.congr_hom ((singCochainTermD A X 0).naturality iU.op) s
    exact hn.trans (hW.trans (map_zero _))
  obtain ⟨V, hV, hxV, a, ha⟩ := restrict_const A hX x W hxW
    (ConcreteCategory.hom ((singCochainTerm A X 0).map iU.op) s) hd0
  let cp : TopCat.Presheaf AddCommGrpCat.{u} X := (Functor.const (Opens X)ᵒᵖ).obj A
  refine ⟨stalkTau x cp (cp.germ V x hxV a), ?_⟩
  rw [hf, TopCat.Presheaf.stalkFunctor_map_germ_apply]
  have hres : (ConcreteCategory.hom ((constToCochain A X).app (op V))) a =
      (ConcreteCategory.hom ((singCochainTerm A X 0).map (homOfLE hV).op))
        ((ConcreteCategory.hom ((singCochainTerm A X 0).map iU.op)) s) := by
    refine cochainEval_injective A _ 0 (funext fun σ => ?_)
    exact (cochainEval_constCochain A _ a σ).trans (ha σ).symm
  rw [hres]
  congr 1
  erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]

private theorem mono_constAugDeg0 (A : AddCommGrpCat.{u}) (X : TopCat.{u}) :
    Mono (constAugDeg0 A X) := by
  have hm : ∀ x : X, Mono ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (constAugDeg0 A X).hom) := fun x => by
   rw [AddCommGrpCat.mono_iff_injective, injective_iff_map_eq_zero]
   intro w hw
   have hsurj : ∀ (F : TopCat.Presheaf AddCommGrpCat.{u} X), Function.Surjective (stalkTau x F) :=
       fun F =>
     ((ConcreteCategory.isIso_iff_bijective _).1 inferInstance).2
   have hinj : ∀ (F : TopCat.Presheaf AddCommGrpCat.{u} X), Function.Injective (stalkTau x F) := fun
       F =>
     ((ConcreteCategory.isIso_iff_bijective _).1 inferInstance).1
   let cp : TopCat.Presheaf AddCommGrpCat.{u} X := (Functor.const (Opens X)ᵒᵖ).obj A
   obtain ⟨w', rfl⟩ := hsurj cp w
   obtain ⟨U, hxU, a, rfl⟩ := TopCat.Presheaf.exists_germ_eq cp w'
   have hf : (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
       (constAugDeg0 A X).hom)) (stalkTau x cp (cp.germ U x hxU a)) =
       stalkTau x (singCochainTerm A X 0)
         ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (constToCochain A X) (cp.germ U x
             hxU a)) :=
     ConcreteCategory.congr_hom (stalkTau_naturality x (constToCochain A X)) _
   have hw' : (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
       (constAugDeg0 A X).hom)) (stalkTau x cp (cp.germ U x hxU a)) = 0 := hw
   rw [hf] at hw'
   have h1 := hinj _ (hw'.trans (map_zero _).symm)
   rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at h1
   have h2 : (singCochainTerm A X 0).germ U x hxU ((constToCochain A X).app (op U) a) =
       (singCochainTerm A X 0).germ U x hxU 0 := h1.trans (map_zero _).symm
   obtain ⟨W, hxW, iU, iV, hW⟩ := TopCat.Presheaf.germ_eq _ x hxU hxU _ _ h2
   have hn := ConcreteCategory.congr_hom ((constToCochain A X).naturality iU.op) a
   have h3 : cochainEval A ((Opens.toTopCat X).obj W) 0
       (ConcreteCategory.hom ((singCochainTerm A X 0).map iU.op)
         (ConcreteCategory.hom ((constToCochain A X).app (op U)) a))
       (TopCat.toSSetObj₀Equiv.symm ⟨x, hxW⟩) = 0 := by
     rw [hW]
     exact congrArg (fun φ => cochainEval A _ 0 φ _) (map_zero _)
   have h4 : ConcreteCategory.hom ((singCochainTerm A X 0).map iU.op)
         (ConcreteCategory.hom ((constToCochain A X).app (op U)) a) =
       constCochain A _ a :=
     hn.symm.trans rfl
   rw [h4] at h3
   erw [cochainEval_constCochain] at h3
   rw [h3]
   exact (congrArg (stalkTau x cp) (map_zero _)).trans (map_zero _)
  haveI := hm
  exact TopCat.Presheaf.mono_of_stalk_mono _

/-- The augmented complex is exact on stalks when `X` is locally contractible. -/
private theorem quasiIso_constAug (A : AddCommGrpCat.{u}) (X : TopCat.{u})
    (hX : LocallyContractibleSpace X) : QuasiIso (constAug A X) := by
  haveI : Mono (augDeg0 (constAug A X)) := by
    rw [augDeg0_constAug]; exact mono_constAugDeg0 A X
  refine quasiIso_of_exact_augDeg0 (constAug A X) ?_ (singCochainSheaves_exactAt A X hX)
  have key : ∀ (f : constSheaf A X ⟶ (singCochainSheaves A X).X 0), f = constAugDeg0 A X →
      ∀ h : f ≫ (singCochainSheaves A X).d 0 1 = 0,
        (ShortComplex.mk f ((singCochainSheaves A X).d 0 1) h).Exact := by
    rintro f rfl h
    exact exact_constAugDeg0 A X hX
  exact key _ (augDeg0_constAug A X) _

section FnSmall

open MMP MMP.SingularChain Finsupp Set

variable {Y : Type u} [TopologicalSpace Y] {M : Type u} [AddCommGroup M]

/-- evaluation of an `M`-valued cochain on an integral chain -/
private abbrev evalA {n : ℕ} (φ : Simplex Y n → M) : Chain ℤ Y n →ₗ[ℤ] M :=
  Finsupp.linearCombination ℤ φ

/-- coboundary of `M`-valued cochains -/
private def cob (n : ℕ) (φ : Simplex Y n → M) : Simplex Y (n + 1) → M :=
  fun σ => ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • φ (σ.comp (face n i))

private lemma evalA_single {n : ℕ} (φ : Simplex Y n → M) (σ : Simplex Y n) :
    evalA φ (single σ 1) = φ σ := by simp

private lemma evalA_bd (n : ℕ) (φ : Simplex Y n → M) (c : Chain ℤ Y (n + 1)) :
    evalA φ (bd ℤ n c) = evalA (cob n φ) c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single σ a =>
    rw [← mul_one a, ← smul_eq_mul, ← smul_single, map_smul, map_smul, map_smul, bd_single,
      map_sum]
    simp [cob]

private lemma evalA_eq_zero_of_mem_small {n : ℕ} {𝒰 : Set (Set Y)} {φ : Simplex Y n → M}
    (h : ∀ σ : Simplex Y n, (∃ U ∈ 𝒰, range σ ⊆ U) → φ σ = 0) {c : Chain ℤ Y n}
    (hc : c ∈ small ℤ n 𝒰) : evalA φ c = 0 := by
  have hc' := (mem_supported ℤ c).1 hc
  rw [Finsupp.linearCombination_apply]
  exact Finset.sum_eq_zero fun σ hσ => by show c σ • φ σ = 0; rw [h σ (hc' hσ), smul_zero]

private lemma smallIndex_eq_zero {𝒰 : Set (Set Y)} (n : ℕ) :
    ∀ σ : Simplex Y n, (∃ U ∈ 𝒰, range σ ⊆ U) → smallIndex ℤ 𝒰 n σ = 0 := by
  have h0 : ∀ {m : ℕ} (σ : Simplex Y m), (∃ U ∈ 𝒰, range σ ⊆ U) → smallIndex₀ ℤ 𝒰 σ = 0 := by
    intro m σ hσ
    classical
    have hs : (subdiv ℤ m ^ 0) (single σ (1 : ℤ)) ∈ small ℤ m 𝒰 := by
      obtain ⟨U, hU, hs⟩ := hσ
      rw [pow_zero]; exact mem_small_of_mem_inside hU (single_mem_inside hs)
    have h : ∃ k, (subdiv ℤ m ^ k) (single σ (1 : ℤ)) ∈ small ℤ m 𝒰 := ⟨0, hs⟩
    simp only [smallIndex₀, h, dite_true]
    exact Nat.eq_zero_of_le_zero (Nat.find_min' h hs)
  induction n with
  | zero => exact fun σ hσ => h0 σ hσ
  | succ n ih =>
    intro σ hσ
    simp only [smallIndex, h0 σ hσ, max_eq_left_iff]
    refine Finset.sup_le fun i _ => ?_
    refine le_of_eq (ih _ ?_)
    obtain ⟨U, hU, hs⟩ := hσ
    exact ⟨U, hU, fun _ ⟨t, ht⟩ => hs ⟨_, ht⟩⟩

private lemma smallHomotopy_eq_zero {𝒰 : Set (Set Y)} (n : ℕ) (σ : Simplex Y n)
    (hσ : ∃ U ∈ 𝒰, range σ ⊆ U) : smallHomotopy ℤ 𝒰 n (single σ 1) = 0 := by
  rw [smallHomotopy_single, smallIndex_eq_zero n σ hσ]
  simp [homotopyUpTo]

private lemma evalA_smallHomotopy_pull {𝒰 : Set (Set Y)} (n : ℕ) (φ : Simplex Y (n + 1) → M)
    (c : Chain ℤ Y n) :
    evalA (fun τ : Simplex Y n => evalA φ (smallHomotopy ℤ 𝒰 n (single τ 1))) c =
      evalA φ (smallHomotopy ℤ 𝒰 n c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single σ a =>
    rw [← mul_one a, ← smul_eq_mul, ← smul_single, map_smul, map_smul, map_smul]
    simp

/-- small-chains acyclicity at the level of cochains: a cocycle vanishing on `𝒰`-small simplices
is the coboundary of a cochain vanishing on `𝒰`-small simplices. -/
private theorem exists_cob_eq_of_small {𝒰 : Set (Set Y)} (h𝒰 : ∀ U ∈ 𝒰, IsOpen U)
    (h𝒰c : ⋃₀ 𝒰 = univ) (n : ℕ) (φ : Simplex Y (n + 1) → M)
    (hφ : ∀ σ : Simplex Y (n + 1), (∃ U ∈ 𝒰, range σ ⊆ U) → φ σ = 0) (hc : cob (n + 1) φ = 0) :
    ∃ ψ : Simplex Y n → M, cob n ψ = φ ∧ ∀ τ : Simplex Y n, (∃ U ∈ 𝒰, range τ ⊆ U) → ψ τ = 0 := by
  refine ⟨fun τ : Simplex Y n => evalA φ (smallHomotopy ℤ 𝒰 n (single τ 1)), ?_, ?_⟩
  · funext σ
    have h1 : cob n (fun τ : Simplex Y n => evalA φ (smallHomotopy ℤ 𝒰 n (single τ 1))) σ =
        evalA φ (smallHomotopy ℤ 𝒰 n (bd ℤ n (single σ 1))) := by
      rw [← evalA_smallHomotopy_pull, ← evalA_single (cob n _) σ, ← evalA_bd]
    have h2 := smallChainMap_add_succ (R := ℤ) 𝒰 n (single σ 1)
    have h3 : evalA φ (smallChainMap ℤ 𝒰 (n + 1) (single σ 1)) = 0 :=
      evalA_eq_zero_of_mem_small hφ
        (smallChainMap_single_mem_small h𝒰 (n + 1) (by rw [h𝒰c]; exact subset_univ _))
    have h4 : evalA φ (bd ℤ (n + 1) (smallHomotopy ℤ 𝒰 (n + 1) (single σ 1))) = 0 := by
      rw [evalA_bd, hc]; simp
    have h5 := congrArg (evalA φ) h2
    rw [map_add, map_add, h3, h4, zero_add, zero_add, evalA_single] at h5
    rw [h1, h5]
  · intro τ hτ
    simp [smallHomotopy_eq_zero n τ hτ]

end FnSmall

section CochainModel

open scoped Simplicial

private abbrev Sx (Y : Type u) [TopologicalSpace Y] (n : ℕ) :=
    MMP.SingularChain.Simplex Y n

private def fnEquiv (A : AddCommGrpCat.{u}) (Y : TopCat.{u}) (n : ℕ) :
    ((singChains Y).X n ⟶ A) ≃ (Sx Y n → A) :=
  (cochainEquiv A Y n).trans
    (Equiv.arrowCongr (MMP.SingularCochain.simplexEquiv Y n) (Equiv.refl _))

private lemma fnEquiv_apply (A : AddCommGrpCat.{u}) (Y : TopCat.{u}) (n : ℕ)
    (φ : (singChains Y).X n ⟶ A) (τ : Sx Y n) :
    fnEquiv A Y n φ τ = cochainEval A Y n φ ((MMP.SingularCochain.simplexEquiv Y
        n).symm τ) :=
  rfl

private lemma fnEquiv_map (A : AddCommGrpCat.{u}) {Y Z : TopCat.{u}} (f : Z ⟶ Y) (n : ℕ)
    (φ : (singChains Y).X n ⟶ A) (τ : Sx Z n) :
    fnEquiv A Z n ((((singularChainComplexFunctor AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift ℤ))).map f).f n ≫ φ) τ = fnEquiv A Y n φ (f.hom.comp τ) := by
  rw [fnEquiv_apply, fnEquiv_apply, cochainEval_map]
  rfl

end CochainModel

section CochainModel2

variable (A : AddCommGrpCat.{u}) (X : TopCat.{u}) (p : ℕ)

private def reprFn (V : Opens X) (g : Sx X p → A) : (singCochainTerm A X p).obj (op V) :=
  (fnEquiv A ((Opens.toTopCat X).obj V) p).symm
    (fun τ => g ((ContinuousMap.subtypeVal (V : Set X)).comp τ))

private lemma fnEquiv_res {V W : Opens X} (h : W ≤ V) (φ : (singCochainTerm A X p).obj (op V))
    (τ : Sx ((Opens.toTopCat X).obj W) p) :
    fnEquiv A ((Opens.toTopCat X).obj W) p ((singCochainTerm A X p).map (homOfLE h).op φ) τ =
      fnEquiv A ((Opens.toTopCat X).obj V) p φ (((Opens.toTopCat X).map (homOfLE h)).hom.comp τ) :=
  fnEquiv_map A ((Opens.toTopCat X).map (homOfLE h)) p φ τ

private lemma reprFn_res {V W : Opens X} (h : W ≤ V) (g : Sx X p → A) :
    (singCochainTerm A X p).map (homOfLE h).op (reprFn A X p V g) = reprFn A X p W g := by
  apply (fnEquiv A ((Opens.toTopCat X).obj W) p).injective
  funext τ
  rw [fnEquiv_res]
  simp only [reprFn, Equiv.apply_symm_apply]
  rfl

private def liftOpen (V : Opens X) (σ : Sx X p) (h : Set.range σ ⊆ V) :
    Sx ((Opens.toTopCat X).obj V) p :=
  ⟨fun t => ⟨σ t, h ⟨t, rfl⟩⟩, σ.continuous.subtype_mk _⟩

private lemma liftOpen_subtypeVal_comp (V : Opens X) (τ : Sx ((Opens.toTopCat X).obj V) p)
    (h : Set.range ((ContinuousMap.subtypeVal (V : Set X)).comp τ) ⊆ V) :
    liftOpen X p V ((ContinuousMap.subtypeVal (V : Set X)).comp τ) h = τ := by ext; rfl

private lemma reprFn_surj (V : Opens X) (φ : (singCochainTerm A X p).obj (op V)) :
    ∃ g, reprFn A X p V g = φ := by
  classical
  refine ⟨fun σ => if h : Set.range σ ⊆ V then fnEquiv A ((Opens.toTopCat X).obj V) p φ (liftOpen X
      p V σ h)
    else 0, ?_⟩
  apply (fnEquiv A ((Opens.toTopCat X).obj V) p).injective
  funext τ
  simp only [reprFn, Equiv.apply_symm_apply]
  have h : Set.range ((ContinuousMap.subtypeVal (V : Set X)).comp τ) ⊆ V :=
    Set.range_subset_iff.2 fun t => (τ t).2
  rw [dif_pos h, liftOpen_subtypeVal_comp]

private lemma reprFn_eq (V : Opens X) (g g' : Sx X p → A) :
    reprFn A X p V g = reprFn A X p V g' ↔ ∀ t : Sx X p, Set.range t ⊆ V → g t = g' t := by
  refine ⟨fun h t ht => ?_, fun h => ?_⟩
  · exact congrFun ((fnEquiv A ((Opens.toTopCat X).obj V) p).symm.injective h)
      (liftOpen X p V t ht)
  · refine congrArg (fnEquiv A ((Opens.toTopCat X).obj V) p).symm (funext fun τ => ?_)
    exact h ((ContinuousMap.subtypeVal (V : Set X)).comp τ)
      (Set.range_subset_iff.2 fun t => (τ t).2)

private lemma fnEquiv_add (Y : TopCat.{u}) (n : ℕ) (φ ψ : (singChains Y).X n ⟶ A) :
    fnEquiv A Y n (φ + ψ) = fnEquiv A Y n φ + fnEquiv A Y n ψ := by
  funext τ
  exact cochainEval_add A Y n φ ψ _

private lemma fnEquiv_zero (Y : TopCat.{u}) (n : ℕ) : fnEquiv A Y n 0 = 0 := by
  funext τ
  rw [fnEquiv_apply]
  unfold cochainEval
  erw [Limits.comp_zero]
  rfl

private lemma reprFn_add (V : Opens X) (g g' : Sx X p → A) :
    reprFn A X p V (g + g') = reprFn A X p V g + reprFn A X p V g' := by
  apply (fnEquiv A ((Opens.toTopCat X).obj V) p).injective
  refine Eq.trans ?_ (fnEquiv_add A _ p _ _).symm
  funext τ
  simp only [reprFn, Equiv.apply_symm_apply, Pi.add_apply]

private lemma reprFn_zero (V : Opens X) : reprFn A X p V 0 = 0 := by
  apply (fnEquiv A ((Opens.toTopCat X).obj V) p).injective
  refine Eq.trans ?_ (fnEquiv_zero A _ p).symm
  funext τ
  simp only [reprFn, Equiv.apply_symm_apply, Pi.zero_apply]

private lemma fnEquiv_d (Y : TopCat.{u}) (n : ℕ) (φ : (singChains Y).X n ⟶ A) (τ : Sx Y (n + 1)) :
    fnEquiv A Y (n + 1) ((singChains Y).d (n + 1) n ≫ φ) τ =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • fnEquiv A Y n φ (τ.comp
          (MMP.SingularChain.face n i)) := by
  rw [fnEquiv_apply, cochainEval_d]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fnEquiv_apply, MMP.SingularCochain.simplexEquiv_symm_δ]

private lemma reprFn_d (V : Opens X) (g : Sx X p → A) :
    ((singCochainPresheaf A X).obj (op V)).d p (p + 1) (reprFn A X p V g) =
      reprFn A X (p + 1) V (cob p g) := by
  apply (fnEquiv A ((Opens.toTopCat X).obj V) (p + 1)).injective
  have h := fun τ => fnEquiv_d A ((Opens.toTopCat X).obj V) p (reprFn A X p V g) τ
  funext τ
  refine (h τ).trans ?_
  simp only [reprFn, Equiv.apply_symm_apply, cob]
  rfl

end CochainModel2

section FunModelSection

variable {X : TopCat.{u}}

private abbrev unitNat (F : TopCat.Presheaf AddCommGrpCat.{u} X) : F ⟶ (sheafify F).obj :=
  (sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{u}).unit.app F

private lemma stalkTau_germ (F : TopCat.Presheaf AddCommGrpCat.{u} X) (U : Opens X) (x : X) (hx : x
    ∈ U)
    (s : F.obj (op U)) :
    stalkTau x F (F.germ U x hx s) = (sheafify F).presheaf.germ U x hx ((unitNat F).app (op U) s) :=
        by
  unfold stalkTau
  exact TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx (unitNat F) s

/-- local representatives -/
private lemma exists_local_repr (P : TopCat.Presheaf AddCommGrpCat.{u} X) (V : Opens X)
    (s : (sheafify P).obj.obj (op V)) (x : X) (hx : x ∈ V) :
    ∃ (W : Opens X) (hW : W ≤ V) (_ : x ∈ W) (ψ : P.obj (op W)),
      (unitNat P).app (op W) ψ = (sheafify P).obj.map (homOfLE hW).op s := by
  have hsurj : Function.Surjective (stalkTau x P) :=
    ((ConcreteCategory.isIso_iff_bijective _).1 inferInstance).2
  obtain ⟨e, he⟩ := hsurj ((sheafify P).presheaf.germ V x hx s)
  obtain ⟨U, hxU, ψ, rfl⟩ := TopCat.Presheaf.exists_germ_eq P e
  rw [stalkTau_germ] at he
  obtain ⟨W, hxW, iU, iV, hW⟩ := TopCat.Presheaf.germ_eq _ x hxU hx _ _ he
  refine ⟨W, leOfHom iV, hxW, P.map iU.op ψ, ?_⟩
  have hn := ConcreteCategory.congr_hom ((unitNat P).naturality iU.op) ψ
  exact hn.trans hW

/-- A presheaf modelled on functions on a set `T` with supports `rng` (singular cochains). -/
private structure FunModel (A : Type u) [AddCommGroup A] (P : TopCat.Presheaf AddCommGrpCat.{u} X)
    where
  T : Type u
  rng : T → Set X
  rng_nonempty : ∀ t, (rng t).Nonempty
  repr : ∀ V : Opens X, (T → A) → P.obj (op V)
  repr_res : ∀ {V W : Opens X} (h : W ≤ V) (g : T → A), P.map (homOfLE h).op (repr V g) = repr W g
  repr_surj : ∀ (V : Opens X) (φ : P.obj (op V)), ∃ g, repr V g = φ
  repr_eq : ∀ (V : Opens X) (g g' : T → A), repr V g = repr V g' ↔ ∀ t, rng t ⊆ V → g t = g' t

variable {A : Type u} [AddCommGroup A] {P : TopCat.Presheaf AddCommGrpCat.{u} X}

private lemma FunModel.agree (M : FunModel A P) (V : Opens X) (s : (sheafify P).obj.obj (op V))
    {W₁ W₂ : Opens X} (h₁ : W₁ ≤ V) (h₂ : W₂ ≤ V) (g₁ g₂ : M.T → A)
    (e₁ : (unitNat P).app (op W₁) (M.repr W₁ g₁) = (sheafify P).obj.map (homOfLE h₁).op s)
    (e₂ : (unitNat P).app (op W₂) (M.repr W₂ g₂) = (sheafify P).obj.map (homOfLE h₂).op s)
    (x : X) (hx₁ : x ∈ W₁) (hx₂ : x ∈ W₂) :
    ∃ N : Opens X, N ≤ W₁ ⊓ W₂ ∧ x ∈ N ∧ ∀ t, M.rng t ⊆ N → g₁ t = g₂ t := by
  have hinj : Function.Injective (stalkTau x P) :=
    ((ConcreteCategory.isIso_iff_bijective _).1 inferInstance).1
  have hg : stalkTau x P (P.germ W₁ x hx₁ (M.repr W₁ g₁)) = stalkTau x P (P.germ W₂ x hx₂ (M.repr W₂
      g₂)) := by
    rw [stalkTau_germ, stalkTau_germ, e₁, e₂]
    erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
  obtain ⟨W, hxW, iU, iV, hW⟩ := TopCat.Presheaf.germ_eq _ x hx₁ hx₂ _ _ (hinj hg)
  have r1 : P.map iU.op (M.repr W₁ g₁) = M.repr W g₁ := M.repr_res (leOfHom iU) g₁
  have r2 : P.map iV.op (M.repr W₂ g₂) = M.repr W g₂ := M.repr_res (leOfHom iV) g₂
  rw [r1, r2, M.repr_eq] at hW
  exact ⟨W, le_inf (leOfHom iU) (leOfHom iV), hxW, fun t ht => hW t ht⟩

private lemma exists_shrink {Y : Type*} [TopologicalSpace Y] [ParacompactSpace Y] [NormalSpace Y]
    {ι : Type*} (W : ι → Set Y) (hW : ∀ i, IsOpen (W i)) (hc : ⋃ i, W i = Set.univ) :
    ∃ u : ι → Set Y, (∀ i, IsOpen (u i)) ∧ ⋃ i, u i = Set.univ ∧ LocallyFinite u ∧
      ∀ i, closure (u i) ⊆ W i := by
  obtain ⟨v, hvo, hvc, hvl, hvW⟩ := precise_refinement W hW hc
  obtain ⟨u, hu1, hu2, hu3⟩ := exists_subset_iUnion_closure_subset (u := v) (s := Set.univ)
    isClosed_univ hvo (fun x _ => hvl.point_finite x) (by rw [hvc])
  refine ⟨u, hu2, Set.eq_univ_of_univ_subset hu1, hvl.subset fun i => ?_, fun i => ?_⟩
  · exact subset_closure.trans (hu3 i)
  · exact (hu3 i).trans (hvW i)

private lemma FunModel.exists_glue (M : FunModel A P) (V : Opens X) [ParacompactSpace V]
    [NormalSpace V]
    (s : (sheafify P).obj.obj (op V)) :
    ∃ φ : P.obj (op V), (unitNat P).app (op V) φ = s := by
  classical
  have hloc := fun (x : V) => exists_local_repr P V s x.1 x.2
  choose W hWV hxW ψ hψ using hloc
  have hg := fun (x : V) => M.repr_surj (W x) (ψ x)
  choose g hg using hg
  have he : ∀ x : V, (unitNat P).app (op (W x)) (M.repr (W x) (g x)) =
      (sheafify P).obj.map (homOfLE (hWV x)).op s := fun x => by rw [hg x]; exact hψ x
  obtain ⟨u, huo, huc, hul, hucl⟩ := exists_shrink (fun i : V => (Subtype.val ⁻¹' (W i : Set X) :
      Set V))
    (fun i => (W i).isOpen.preimage continuous_subtype_val)
    (Set.eq_univ_of_forall fun y => Set.mem_iUnion.2 ⟨y, hxW y⟩)
  let g0 : M.T → A := fun t =>
    if h : ∃ i : V, M.rng t ⊆ Subtype.val '' u i then g (Classical.choose h) t else 0
  have hC : ∀ x (hx : x ∈ V), ∃ (i0 : V) (N : Opens X), N ≤ W i0 ∧ N ≤ V ∧ x ∈ N ∧
      ∀ t, M.rng t ⊆ N → g0 t = g i0 t := by
    intro x hx
    set xv : V := ⟨x, hx⟩ with hxv
    obtain ⟨i0, hi0⟩ := Set.mem_iUnion.1 (huc ▸ Set.mem_univ xv)
    obtain ⟨Nv, hNv, hfin⟩ := hul xv
    have hNi : ∀ i : V, ∃ Ni : Opens X, xv ∈ closure (u i) →
        (x ∈ Ni ∧ Ni ≤ W i ⊓ W i0 ∧ ∀ t, M.rng t ⊆ Ni → g i t = g i0 t) := by
      intro i
      by_cases hc : xv ∈ closure (u i)
      · have hxi : x ∈ W i := hucl i hc
        have hxi0 : x ∈ W i0 := hucl i0 (subset_closure hi0)
        obtain ⟨N, hN1, hN2, hN3⟩ := M.agree V s (hWV i) (hWV i0) (g i) (g i0) (he i) (he i0) x hxi
            hxi0
        exact ⟨N, fun _ => ⟨hN2, hN1, hN3⟩⟩
      · exact ⟨⊥, fun h => absurd h hc⟩
    choose Ni hNi using hNi
    let F : V → Set V := fun i => if xv ∈ closure (u i) then Subtype.val ⁻¹' (Ni i : Set X) else
        (closure (u i))ᶜ
    have hFo : ∀ i, IsOpen (F i) := fun i => by
      by_cases hc : xv ∈ closure (u i)
      · simp only [F, if_pos hc]
        exact (Ni i).isOpen.preimage continuous_subtype_val
      · simp only [F, if_neg hc]
        exact isClosed_closure.isOpen_compl
    have hFx : ∀ i, xv ∈ F i := fun i => by
      by_cases hc : xv ∈ closure (u i)
      · simp only [F, if_pos hc]
        exact (hNi i hc).1
      · simp only [F, if_neg hc]
        exact hc
    let S : Set V := interior Nv ∩ u i0 ∩ ⋂ i ∈ hfin.toFinset, F i
    have hSo : IsOpen S := by
      refine (isOpen_interior.inter (huo i0)).inter ?_
      exact Set.Finite.isOpen_biInter hfin.toFinset.finite_toSet fun i _ => hFo i
    have hxS : xv ∈ S := ⟨⟨mem_interior_iff_mem_nhds.2 hNv, hi0⟩, Set.mem_iInter₂.2 fun i _ => hFx
        i⟩
    have hSV : IsOpen (Subtype.val '' S) := V.isOpen.isOpenMap_subtype_val S hSo
    refine ⟨i0, ⟨Subtype.val '' S, hSV⟩, ?_, ?_, ⟨xv, hxS, rfl⟩, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact hucl i0 (subset_closure hy.1.2)
    · rintro _ ⟨y, hy, rfl⟩
      exact y.2
    · intro t ht
      have hex : ∃ i : V, M.rng t ⊆ Subtype.val '' u i := ⟨i0, fun q hq => by
        obtain ⟨y, hy, rfl⟩ := ht hq
        exact ⟨y, hy.1.2, rfl⟩⟩
      have h0 : g0 t = g (Classical.choose hex) t := dif_pos hex
      rw [h0]
      set j := Classical.choose hex with hj
      have hjt : M.rng t ⊆ Subtype.val '' u j := Classical.choose_spec hex
      obtain ⟨p, hp⟩ := M.rng_nonempty t
      obtain ⟨y, hyS, rfl⟩ := ht hp
      obtain ⟨y', hy'u, hy'⟩ := hjt hp
      have hyy : y' = y := Subtype.ext hy'
      subst hyy
      have hjG : j ∈ hfin.toFinset := by
        rw [Set.Finite.mem_toFinset]
        exact ⟨y', hy'u, interior_subset hyS.1.1⟩
      have hyF : y' ∈ F j := Set.mem_iInter₂.1 hyS.2 j hjG
      by_cases hc : xv ∈ closure (u j)
      · refine (hNi j hc).2.2 t (fun q hq => ?_)
        obtain ⟨z, hz, rfl⟩ := ht hq
        have hzF : z ∈ F j := Set.mem_iInter₂.1 hz.2 j hjG
        simp only [F, if_pos hc] at hzF
        exact hzF
      · simp only [F, if_neg hc] at hyF
        exact absurd (subset_closure hy'u) hyF
  refine ⟨M.repr V g0, TopCat.Presheaf.section_ext (sheafify P) V _ _ fun x hx => ?_⟩
  obtain ⟨i0, N, hNW, hNV, hxN, hNg⟩ := hC x hx
  rw [← TopCat.Presheaf.germ_res_apply (sheafify P).presheaf (homOfLE hNV) x hxN,
    ← TopCat.Presheaf.germ_res_apply (sheafify P).presheaf (homOfLE hNV) x hxN s]
  congr 1
  have h1 : (sheafify P).obj.map (homOfLE hNV).op ((unitNat P).app (op V) (M.repr V g0)) =
      (unitNat P).app (op N) (P.map (homOfLE hNV).op (M.repr V g0)) :=
    (ConcreteCategory.congr_hom ((unitNat P).naturality (homOfLE hNV).op) (M.repr V g0)).symm
  have h2 :
      P.map (homOfLE hNV).op (M.repr V g0) = P.map (homOfLE hNW).op (M.repr (W i0) (g i0)) := by
    rw [M.repr_res hNV, M.repr_res hNW, M.repr_eq]
    exact hNg
  have h3 : (unitNat P).app (op N) (P.map (homOfLE hNW).op (M.repr (W i0) (g i0))) =
      (sheafify P).obj.map (homOfLE hNW).op ((unitNat P).app (op (W i0)) (M.repr (W i0) (g i0))) :=
    ConcreteCategory.congr_hom ((unitNat P).naturality (homOfLE hNW).op) (M.repr (W i0) (g i0))
  have h4 : (sheafify P).obj.map (homOfLE hNV).op s =
      (sheafify P).obj.map (homOfLE hNW).op ((sheafify P).obj.map (homOfLE (hWV i0)).op s) := by
    rw [← ConcreteCategory.comp_apply, ← (sheafify P).obj.map_comp]
    rfl
  erw [h1, h2, h3, he i0]
  exact h4.symm

end FunModelSection

section Flasque5

private def cochainFunModel (A : AddCommGrpCat.{u}) (X : TopCat.{u}) (p : ℕ) :
    FunModel (A : Type u) (singCochainTerm A X p) where
  T := Sx X p
  rng := fun t => Set.range t
  rng_nonempty := fun t => ⟨t (stdSimplex.vertex 0), ⟨_, rfl⟩⟩
  repr := reprFn A X p
  repr_res := reprFn_res A X p
  repr_surj := reprFn_surj A X p
  repr_eq := reprFn_eq A X p

/-- The sheafified singular cochains are flasque on a metrizable space. -/
private theorem singCochainSheaves_isFlasque (A : AddCommGrpCat.{u}) (X : TopCat.{u})
    [MetrizableSpace X] (p : ℕ) : TopCat.Presheaf.IsFlasque ((singCochainSheaves A X).X p).obj where
  epi {U V} i := by
    rw [AddCommGrpCat.epi_iff_surjective]
    intro t
    haveI : MetrizableSpace V.unop := Topology.IsEmbedding.subtypeVal.metrizableSpace
    letI := TopologicalSpace.metrizableSpaceMetric V.unop
    obtain ⟨φ, hφ⟩ := (cochainFunModel A X p).exists_glue V.unop t
    obtain ⟨g, rfl⟩ := reprFn_surj A X p V.unop φ
    refine ⟨(unitNat (singCochainTerm A X p)).app U (reprFn A X p U.unop g), ?_⟩
    have h1 : (unitNat (singCochainTerm A X p)).app V ((singCochainTerm A X p).map i (reprFn A X p
        U.unop g)) =
        (sheafify (singCochainTerm A X p)).obj.map i
          ((unitNat (singCochainTerm A X p)).app U (reprFn A X p U.unop g)) :=
      ConcreteCategory.congr_hom ((unitNat (singCochainTerm A X p)).naturality i) _
    have h2 : (singCochainTerm A X p).map i (reprFn A X p U.unop g) = reprFn A X p V.unop g :=
      reprFn_res A X p (leOfHom i.unop) g
    rw [h2] at h1
    exact h1.symm.trans hφ

end Flasque5

section Step6

private abbrev gammaS (A : AddCommGrpCat.{u}) (X : TopCat.{u}) : CochainComplex AddCommGrpCat.{u}
    ℕ :=
  ((globalSections X).mapHomologicalComplex _).obj (singCochainSheaves A X)

private def singEps (A : AddCommGrpCat.{u}) (X : TopCat.{u}) :
    (singCochainPresheaf A X).obj (op ⊤) ⟶ gammaS A X where
  f p := (unitNat (singCochainTerm A X p)).app (op ⊤)
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    have e : (singCochainPresheafComplex A X).d i (i + 1) = singCochainTermD A X i :=
      CochainComplex.of_d _ _ _
    have h := (sheafificationAdjunction (Opens.grothendieckTopology X)
        AddCommGrpCat.{u}).unit.naturality
      (singCochainTermD A X i)
    have h2 := congrArg (fun t => t.app (op ⊤)) h
    simp only [Functor.id_map, NatTrans.comp_app] at h2
    have hd : (gammaS A X).d i (i + 1) =
        ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
          (singCochainTermD A X i)).hom.app (op ⊤) := by
      change ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
        ((singCochainPresheafComplex A X).d i (i + 1))).hom.app (op ⊤) = _
      rw [e]
      rfl
    rw [hd]
    exact h2.symm

/-- A cochain vanishing on all simplices that are small for some open cover. -/
private def LocZero {A : AddCommGrpCat.{u}} {X : TopCat.{u}} {p : ℕ} (g : Sx X p → A) : Prop :=
  ∃ 𝒰 : Set (Set X), (∀ U ∈ 𝒰, IsOpen U) ∧ ⋃₀ 𝒰 = Set.univ ∧
    ∀ t : Sx X p, (∃ U ∈ 𝒰, Set.range t ⊆ U) → g t = 0

private lemma locZero_of_eps_eq_zero (A : AddCommGrpCat.{u}) (X : TopCat.{u}) (p : ℕ) (g : Sx X p →
    A)
    (h : (singEps A X).f p (reprFn A X p ⊤ g) = 0) : LocZero g := by
  classical
  have hinj : ∀ x : X, Function.Injective (stalkTau x (singCochainTerm A X p)) := fun x =>
    ((ConcreteCategory.isIso_iff_bijective _).1 inferInstance).1
  have hloc : ∀ x : X, ∃ W : Opens X, x ∈ W ∧ ∀ t : Sx X p, Set.range t ⊆ W → g t = 0 := by
    intro x
    have hx : x ∈ (⊤ : Opens X) := trivial
    have hg : stalkTau x (singCochainTerm A X p) ((singCochainTerm A X p).germ ⊤ x hx (reprFn A X p
        ⊤ g)) =
        stalkTau x (singCochainTerm A X p) ((singCochainTerm A X p).germ ⊤ x hx 0) := by
      rw [stalkTau_germ, stalkTau_germ]
      have h' : (unitNat (singCochainTerm A X p)).app (op ⊤) (reprFn A X p ⊤ g) = 0 := h
      rw [h']
      rw [map_zero, map_zero, map_zero]
    obtain ⟨W, hxW, iU, iV, hW⟩ := TopCat.Presheaf.germ_eq _ x hx hx _ _ (hinj x hg)
    refine ⟨W, hxW, ?_⟩
    have r1 : (singCochainTerm A X p).map iU.op (reprFn A X p ⊤ g) = reprFn A X p W g :=
      reprFn_res A X p (leOfHom iU) g
    rw [r1, map_zero, ← reprFn_zero A X p W, reprFn_eq] at hW
    exact fun t ht => by simpa using hW t ht
  choose W hxW hW using hloc
  refine ⟨Set.range (fun x => (W x : Set X)), ?_, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩; exact (W x).isOpen
  · exact Set.eq_univ_of_forall fun x => Set.mem_sUnion.2 ⟨_, ⟨x, rfl⟩, hxW x⟩
  · rintro t ⟨_, ⟨x, rfl⟩, ht⟩
    exact hW x t ht

private lemma eps_eq_zero_of_locZero (A : AddCommGrpCat.{u}) (X : TopCat.{u}) (p : ℕ) (g : Sx X p →
    A)
    (h : LocZero g) : (singEps A X).f p (reprFn A X p ⊤ g) = 0 := by
  obtain ⟨𝒰, ho, hc, hv⟩ := h
  refine TopCat.Presheaf.section_ext (sheafify (singCochainTerm A X p)) ⊤ _ _ fun x hx => ?_
  obtain ⟨U, hU, hxU⟩ := Set.mem_sUnion.1 (hc ▸ Set.mem_univ x)
  let U' : Opens X := ⟨U, ho U hU⟩
  have hle : U' ≤ ⊤ := le_top
  have hz : (singCochainTerm A X p).map (homOfLE hle).op (reprFn A X p ⊤ g) = 0 := by
    rw [reprFn_res, ← reprFn_zero A X p U', reprFn_eq]
    exact fun t ht => hv t ⟨U, hU, ht⟩
  show (sheafify (singCochainTerm A X p)).presheaf.germ ⊤ x hx
      ((unitNat (singCochainTerm A X p)).app (op ⊤) (reprFn A X p ⊤ g)) = _
  rw [← TopCat.Presheaf.germ_res_apply (sheafify (singCochainTerm A X p)).presheaf (homOfLE hle) x
      hxU]
  have h1 : (sheafify (singCochainTerm A X p)).obj.map (homOfLE hle).op
      ((unitNat (singCochainTerm A X p)).app (op ⊤) (reprFn A X p ⊤ g)) =
      (unitNat (singCochainTerm A X p)).app (op U') ((singCochainTerm A X p).map (homOfLE hle).op
          (reprFn A X p ⊤ g)) :=
    (ConcreteCategory.congr_hom ((unitNat (singCochainTerm A X p)).naturality (homOfLE hle).op)
        _).symm
  erw [h1, hz, map_zero, map_zero, map_zero]

private lemma eps_surj (A : AddCommGrpCat.{u}) (X : TopCat.{u}) [MetrizableSpace X] (p : ℕ)
    (s : (gammaS A X).X p) : ∃ g : Sx X p → A, (singEps A X).f p (reprFn A X p ⊤ g) = s := by
  haveI : MetrizableSpace (⊤ : Opens X) := Topology.IsEmbedding.subtypeVal.metrizableSpace
  letI := TopologicalSpace.metrizableSpaceMetric (⊤ : Opens X)
  obtain ⟨φ, hφ⟩ := (cochainFunModel A X p).exists_glue ⊤ s
  obtain ⟨g, rfl⟩ := reprFn_surj A X p ⊤ φ
  exact ⟨g, hφ⟩

private lemma reprFn_sub (A : AddCommGrpCat.{u}) (X : TopCat.{u}) (p : ℕ) (V : Opens X) (g g' : Sx X
    p → A) :
    reprFn A X p V (g - g') = reprFn A X p V g - reprFn A X p V g' := by
  rw [eq_sub_iff_add_eq, ← reprFn_add, sub_add_cancel]

private lemma reprFn_top_injective (A : AddCommGrpCat.{u}) (X : TopCat.{u}) (p : ℕ) {g g' : Sx X p →
    A}
    (h : reprFn A X p ⊤ g = reprFn A X p ⊤ g') : g = g' :=
  funext fun t => (reprFn_eq A X p ⊤ g g').1 h t (fun _ _ => trivial)

private lemma cob_sub (n : ℕ) {A : AddCommGrpCat.{u}} {X : TopCat.{u}} (g g' : Sx X n → A) :
    cob n (g - g') = cob n g - cob n g' := by
  funext σ
  simp [cob, smul_sub, Finset.sum_sub_distrib]

private lemma cob_cob (A : AddCommGrpCat.{u}) (X : TopCat.{u}) (p : ℕ) (g : Sx X p → A) :
    cob (p + 1) (cob p g) = 0 := by
  apply reprFn_top_injective A X (p + 2)
  have h := ConcreteCategory.congr_hom (((singCochainPresheaf A X).obj (op ⊤)).d_comp_d p (p + 1) (p
      + 2))
    (reprFn A X p ⊤ g)
  rw [reprFn_zero]
  erw [← reprFn_d, ← reprFn_d]
  erw [← ConcreteCategory.comp_apply]
  rw [HomologicalComplex.d_comp_d]
  rfl

private lemma eps_d (A : AddCommGrpCat.{u}) (X : TopCat.{u}) (p : ℕ) (x : ((singCochainPresheaf A
    X).obj (op ⊤)).X p) :
    (singEps A X).f (p + 1) (((singCochainPresheaf A X).obj (op ⊤)).d p (p + 1) x) =
      (gammaS A X).d p (p + 1) ((singEps A X).f p x) :=
  (ConcreteCategory.congr_hom ((singEps A X).comm p (p + 1)) x).symm

private lemma eps_surj_cohom (A : AddCommGrpCat.{u}) (X : TopCat.{u}) [MetrizableSpace X] (q : ℕ)
    (y : (gammaS A X).X q) (hy : (gammaS A X).d q (q + 1) y = 0) :
    ∃ g : Sx X q → A, cob q g = 0 ∧ (singEps A X).f q (reprFn A X q ⊤ g) = y := by
  obtain ⟨g, hg⟩ := eps_surj A X q y
  have h1 : (singEps A X).f (q + 1) (reprFn A X (q + 1) ⊤ (cob q g)) = 0 := by
    have e1 := eps_d A X q (reprFn A X q ⊤ g)
    rw [hg, hy] at e1
    erw [reprFn_d] at e1
    exact e1
  obtain ⟨𝒰, ho, hc, hv⟩ := locZero_of_eps_eq_zero A X (q + 1) _ h1
  obtain ⟨ψ, hψ, hψv⟩ := exists_cob_eq_of_small ho hc q (cob q g) hv (cob_cob A X q g)
  refine ⟨g - ψ, ?_, ?_⟩
  · rw [cob_sub, hψ, sub_self]
  · have h2 := eps_eq_zero_of_locZero A X q ψ ⟨𝒰, ho, hc, hψv⟩
    rw [reprFn_sub]
    erw [map_sub, hg, h2, sub_zero]

private lemma cob_add (n : ℕ) {A : AddCommGrpCat.{u}} {X : TopCat.{u}} (g g' : Sx X n → A) :
    cob n (g + g') = cob n g + cob n g' := by
  funext σ
  simp [cob, smul_add, Finset.sum_add_distrib]

private lemma eq_zero_of_locZero_zero (A : AddCommGrpCat.{u}) (X : TopCat.{u}) (g : Sx X 0 → A)
    (h : LocZero g) : g = 0 := by
  obtain ⟨𝒰, ho, hc, hv⟩ := h
  funext t
  let v : stdSimplex ℝ (Fin (0 + 1)) := stdSimplex.vertex 0
  obtain ⟨U, hU, hx⟩ := Set.mem_sUnion.1 (hc ▸ Set.mem_univ (t v))
  refine hv t ⟨U, hU, ?_⟩
  rintro _ ⟨s, rfl⟩
  have : s = v := by
    apply Subtype.ext
    funext i
    have h1 := s.2.2
    have h2 := v.2.2
    simp [Fin.sum_univ_succ] at h1 h2
    have : i = 0 := Fin.ext (by have := i.2; omega)
    subst this
    simp [h1, v]
  rwa [this]

private lemma eps_inj_succ (A : AddCommGrpCat.{u}) (X : TopCat.{u}) [MetrizableSpace X] (m : ℕ)
    (g : Sx X (m + 1) → A) (hg : cob (m + 1) g = 0) (t : (gammaS A X).X m)
    (ht : (singEps A X).f (m + 1) (reprFn A X (m + 1) ⊤ g) = (gammaS A X).d m (m + 1) t) :
    ∃ h : Sx X m → A, cob m h = g := by
  obtain ⟨h0, hh0⟩ := eps_surj A X m t
  have h1 : (singEps A X).f (m + 1) (reprFn A X (m + 1) ⊤ (g - cob m h0)) = 0 := by
    rw [reprFn_sub]
    have e1 := eps_d A X m (reprFn A X m ⊤ h0)
    rw [hh0] at e1
    erw [reprFn_d] at e1
    erw [map_sub, e1, ht, sub_self]
  obtain ⟨𝒰, ho, hc, hv⟩ := locZero_of_eps_eq_zero A X (m + 1) _ h1
  obtain ⟨ψ, hψ, -⟩ := exists_cob_eq_of_small ho hc m (g - cob m h0) hv (by
    rw [cob_sub, hg, cob_cob, sub_zero])
  refine ⟨ψ + h0, ?_⟩
  rw [cob_add, hψ, sub_add_cancel]

private lemma eps_inj_zero (A : AddCommGrpCat.{u}) (X : TopCat.{u}) (g : Sx X 0 → A)
    (h : (singEps A X).f 0 (reprFn A X 0 ⊤ g) = 0) : g = 0 :=
  eq_zero_of_locZero_zero A X g (locZero_of_eps_eq_zero A X 0 g h)

private theorem quasiIso_singEps (A : AddCommGrpCat.{u}) (X : TopCat.{u}) [MetrizableSpace X] :
    QuasiIso (singEps A X) := by
  refine ⟨fun n => ?_⟩
  cases n with
  | zero =>
    rw [CochainComplex.quasiIsoAt₀_iff]
    apply ab_quasiIso_of
    · intro y hy
      obtain ⟨g, hg, hεg⟩ := eps_surj_cohom A X 0 y hy
      refine ⟨reprFn A X 0 ⊤ g, ?_, 0, ?_⟩
      · change ((singCochainPresheaf A X).obj (op ⊤)).d 0 1 (reprFn A X 0 ⊤ g) = 0
        erw [reprFn_d, hg, reprFn_zero]
        rfl
      · erw [hεg, sub_self, map_zero]
    · intro x hx ht
      obtain ⟨t, ht⟩ := ht
      obtain ⟨g, rfl⟩ := reprFn_surj A X 0 ⊤ x
      have h0 : (gammaS A X).d 0 0 = 0 := (gammaS A X).shape _ _ (by simp)
      have h1 : (singEps A X).f 0 (reprFn A X 0 ⊤ g) = 0 := by
        refine ht.trans ?_
        change (gammaS A X).d 0 0 t = 0
        rw [h0]; rfl
      have h2 := eps_inj_zero A X g h1
      refine ⟨0, ?_⟩
      rw [map_zero, h2, reprFn_zero]
      rfl
  | succ m =>
    rw [quasiIsoAt_iff' _ m (m + 1) (m + 2) (by simp) (by simp)]
    apply ab_quasiIso_of
    · intro y hy
      obtain ⟨g, hg, hεg⟩ := eps_surj_cohom A X (m + 1) y hy
      refine ⟨reprFn A X (m + 1) ⊤ g, ?_, 0, ?_⟩
      · change ((singCochainPresheaf A X).obj (op ⊤)).d (m + 1) (m + 2) (reprFn A X (m + 1) ⊤ g) = 0
        erw [reprFn_d, hg, reprFn_zero]
        rfl
      · erw [hεg, sub_self, map_zero]
    · intro x hx ht
      obtain ⟨t, ht⟩ := ht
      obtain ⟨g, rfl⟩ := reprFn_surj A X (m + 1) ⊤ x
      have hg : cob (m + 1) g = 0 := by
        apply reprFn_top_injective A X (m + 2)
        rwa [reprFn_zero, ← reprFn_d]
      obtain ⟨h, hh⟩ := eps_inj_succ A X m g hg t ht
      refine ⟨reprFn A X m ⊤ h, ?_⟩
      change _ = ((singCochainPresheaf A X).obj (op ⊤)).d m (m + 1) (reprFn A X m ⊤ h)
      erw [reprFn_d, hh]

/-- The comparison of `Hom(C_•(X; ℤ), A)` with the cochains `P^•(⊤)` of the open set `⊤`. -/
private def bridge (A : AddCommGrpCat.{u}) (X : TopCat.{u}) :
    singCochains A X ⟶ (singCochainPresheaf A X).obj (op ⊤) where
  f p := AddCommGrpCat.ofHom
    { toFun := fun φ => reprFn A X p ⊤ (fnEquiv A X p φ)
      map_zero' := by
        change reprFn A X p ⊤ (fnEquiv A X p 0) = 0
        rw [fnEquiv_zero, reprFn_zero]
      map_add' := fun a b => by
        exact (congrArg (reprFn A X p ⊤) (fnEquiv_add A X p a b)).trans (reprFn_add A X p ⊤ _ _) }
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun φ => ?_)
    change ((singCochainPresheaf A X).obj (op ⊤)).d i (i + 1) (reprFn A X i ⊤ (fnEquiv A X i φ)) =
      reprFn A X (i + 1) ⊤ (fnEquiv A X (i + 1) ((singChains X).d (i + 1) i ≫ φ))
    erw [reprFn_d]
    congr 1
    funext τ
    erw [fnEquiv_d]
    rfl

private instance isIso_bridge (A : AddCommGrpCat.{u}) (X : TopCat.{u}) : IsIso (bridge A X) := by
  have : ∀ p, IsIso ((bridge A X).f p) := fun p => by
    rw [ConcreteCategory.isIso_iff_bijective]
    refine ⟨fun a b h => ?_, fun y => ?_⟩
    · have h' : reprFn A X p ⊤ (fnEquiv A X p a) = reprFn A X p ⊤ (fnEquiv A X p b) := h
      exact (fnEquiv A X p).injective (reprFn_top_injective A X p h')
    · obtain ⟨g, rfl⟩ := reprFn_surj A X p ⊤ y
      exact ⟨(fnEquiv A X p).symm g, by
        change reprFn A X p ⊤ (fnEquiv A X p ((fnEquiv A X p).symm g)) = _
        rw [Equiv.apply_symm_apply]⟩
  exact HomologicalComplex.Hom.isIso_of_components _

/-- The comparison of singular cochains `Hom(C_•(X; ℤ), A)` with global sections of `𝒮^•`. -/
private def singEps' (A : AddCommGrpCat.{u}) (X : TopCat.{u}) : singCochains A X ⟶ gammaS A X :=
  bridge A X ≫ singEps A X

private theorem quasiIso_singEps' (A : AddCommGrpCat.{u}) (X : TopCat.{u}) [MetrizableSpace X] :
    QuasiIso (singEps' A X) := by
  haveI := quasiIso_singEps A X
  exact inferInstanceAs (QuasiIso (bridge A X ≫ singEps A X))

end Step6

section Pushforward

variable (A : AddCommGrpCat.{u}) {M N : TopCat.{u}} (f : N ⟶ M)

/-- The restriction `f⁻¹ U ⟶ U` of `f` to an open set. -/
private def fRes (U : Opens M) :
    (Opens.toTopCat N).obj ((Opens.map f).obj U) ⟶ (Opens.toTopCat M).obj U :=
  TopCat.ofHom ⟨fun y => ⟨f y.1, y.2⟩, by fun_prop⟩

private lemma fRes_comp {U V : Opens M} (i : V ⟶ U) :
    (Opens.toTopCat N).map ((Opens.map f).map i) ≫ fRes f U = fRes f V ≫ (Opens.toTopCat M).map i :=
        by
  ext y
  rfl

/-- The presheaf map `P_M^p ⟶ f_* P_N^p`, `φ ↦ f^* φ`. -/
private def thetaP (p : ℕ) :
    singCochainTerm A M p ⟶ (TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).obj (singCochainTerm A
        N p) where
  app U := AddCommGrpCat.ofHom
    { toFun := fun φ => (((singularChainComplexFunctor AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift ℤ))).map (fRes f U.unop)).f p ≫ φ
      map_zero' := by
        erw [Limits.comp_zero]; rfl
      map_add' := fun a b => by
        erw [Preadditive.comp_add]; rfl }
  naturality U V i := by
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun φ => ?_)
    have h := congrArg (fun g => (((singularChainComplexFunctor AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift ℤ))).map g).f p) (fRes_comp f i.unop)
    simp only [Functor.map_comp, HomologicalComplex.comp_f] at h
    change (((singularChainComplexFunctor AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift ℤ))).map
        (fRes f V.unop)).f p ≫ ((((singularChainComplexFunctor AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift ℤ))).map ((Opens.toTopCat M).map i.unop)).f p ≫ φ) =
      (((singularChainComplexFunctor AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift ℤ))).map
        ((Opens.toTopCat N).map ((Opens.map f).map i.unop))).f p ≫ ((((singularChainComplexFunctor
            AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift ℤ))).map (fRes f U.unop)).f p ≫ φ)
    erw [← Category.assoc, ← Category.assoc, h]

private instance pushforwardPresheafZero : (TopCat.Presheaf.pushforward AddCommGrpCat.{u}
    f).PreservesZeroMorphisms :=
  ⟨fun _ _ => rfl⟩

private def thetaPComplex : singCochainPresheafComplex A M ⟶
    ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex _).obj
      (singCochainPresheafComplex A N) where
  f p := thetaP A f p
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    have e1 : ∀ (Y : TopCat.{u}), (singCochainPresheafComplex A Y).d i (i + 1) = singCochainTermD A
        Y i :=
      fun Y => CochainComplex.of_d _ _ _
    refine NatTrans.ext (funext fun U => ?_)
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun φ => ?_)
    have h := (((singularChainComplexFunctor AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift
        ℤ))).map
      (fRes f U.unop)).comm (i + 1) i
    change ((singCochainPresheafComplex A N).d i (i + 1)).app (op ((Opens.map f).obj U.unop))
        ((thetaP A f i).app U φ) =
      (thetaP A f (i + 1)).app U (((singCochainPresheafComplex A M).d i (i + 1)).app U φ)
    rw [e1, e1]
    change (singChains _).d (i + 1) i ≫ ((((singularChainComplexFunctor AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift ℤ))).map (fRes f U.unop)).f i ≫ φ) =
      (((singularChainComplexFunctor AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift ℤ))).map
        (fRes f U.unop)).f (i + 1) ≫ ((singChains _).d (i + 1) i ≫ φ)
    erw [← Category.assoc, ← Category.assoc, h]

private def thetaKf (p : ℕ) : sheafify (singCochainTerm A M p) ⟶
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj (sheafify (singCochainTerm A N p)) :=
  ((sheafificationAdjunction (Opens.grothendieckTopology M) AddCommGrpCat.{u}).homEquiv
    (singCochainTerm A M p) ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj (sheafify
        (singCochainTerm A N p)))).symm
    (thetaP A f p ≫ (TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).map
      (unitNat (singCochainTerm A N p)))

private lemma thetaKf_unit (p : ℕ) :
    unitNat (singCochainTerm A M p) ≫ (thetaKf A f p).hom =
      thetaP A f p ≫ (TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).map
        (unitNat (singCochainTerm A N p)) := by
  have h := (sheafificationAdjunction (Opens.grothendieckTopology M)
      AddCommGrpCat.{u}).homEquiv_unit
    (X := singCochainTerm A M p) (Y := (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj (sheafify
        (singCochainTerm A N p)))
    (f := thetaKf A f p)
  have h2 := ((sheafificationAdjunction (Opens.grothendieckTopology M) AddCommGrpCat.{u}).homEquiv
    (singCochainTerm A M p) ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj (sheafify
        (singCochainTerm A N p)))).apply_symm_apply
    (thetaP A f p ≫ (TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).map (unitNat (singCochainTerm
        A N p)))
  exact h.symm.trans h2

private lemma thetaP_comm (p : ℕ) :
    thetaP A f p ≫ (TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).map (singCochainTermD A N p) =
      singCochainTermD A M p ≫ thetaP A f (p + 1) := by
  have h := (thetaPComplex A f).comm p (p + 1)
  have e1 : ∀ (Y : TopCat.{u}), (singCochainPresheafComplex A Y).d p (p + 1) = singCochainTermD A Y
      p :=
    fun Y => CochainComplex.of_d _ _ _
  change thetaP A f p ≫ (TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).map
      ((singCochainPresheafComplex A N).d p (p + 1)) =
    (singCochainPresheafComplex A M).d p (p + 1) ≫ thetaP A f (p + 1) at h
  rwa [e1, e1] at h

private lemma singSheaf_d (X : TopCat.{u}) (p : ℕ) :
    (singCochainSheaves A X).d p (p + 1) =
      (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map (singCochainTermD A X
          p) :=
  congrArg (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
    (CochainComplex.of_d _ _ _)

private lemma unit_comp_singSheaf_d (X : TopCat.{u}) (p : ℕ) :
    unitNat (singCochainTerm A X p) ≫ ((singCochainSheaves A X).d p (p + 1)).hom =
      singCochainTermD A X p ≫ unitNat (singCochainTerm A X (p + 1)) := by
  rw [singSheaf_d]
  exact ((sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{u}).unit.naturality
    (singCochainTermD A X p)).symm

private lemma sheafify_hom_ext {X : TopCat.{u}} {P : TopCat.Presheaf AddCommGrpCat.{u} X}
    {S : TopCat.Sheaf AddCommGrpCat.{u} X} {u v : sheafify P ⟶ S}
    (h : unitNat P ≫ u.hom = unitNat P ≫ v.hom) : u = v := by
  have e1 := (sheafificationAdjunction (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}).homEquiv_unit
    (X := P) (Y := S) (f := u)
  have e2 := (sheafificationAdjunction (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}).homEquiv_unit
    (X := P) (Y := S) (f := v)
  exact ((sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{u}).homEquiv P
      S).injective
    (e1.trans (h.trans e2.symm))

private def thetaK : singCochainSheaves A M ⟶
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex _).obj (singCochainSheaves
        A N) where
  f p := thetaKf A f p
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    apply sheafify_hom_ext
    change unitNat (singCochainTerm A M i) ≫ ((thetaKf A f i) ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map ((singCochainSheaves A N).d i (i +
            1))).hom =
      unitNat (singCochainTerm A M i) ≫ (((singCochainSheaves A M).d i (i + 1)) ≫ thetaKf A f (i +
          1)).hom
    have hθ := thetaKf_unit A f i
    have hθ' := thetaKf_unit A f (i + 1)
    have hdN := unit_comp_singSheaf_d A N i
    have hdM := unit_comp_singSheaf_d A M i
    have hc := thetaP_comm A f i
    change unitNat (singCochainTerm A M i) ≫ ((thetaKf A f i).hom ≫
        (TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).map ((singCochainSheaves A N).d i (i +
            1)).hom) =
      unitNat (singCochainTerm A M i) ≫ (((singCochainSheaves A M).d i (i + 1)).hom ≫ (thetaKf A f
          (i + 1)).hom)
    erw [← Category.assoc, hθ, Category.assoc, ← Functor.map_comp, hdN, Functor.map_comp, ←
        Category.assoc, hc,
      Category.assoc, ← hθ', ← Category.assoc, ← hdM, Category.assoc]

/-- the induced map on global sections `Γ(M, 𝒮_M^•) ⟶ Γ(N, 𝒮_N^•)` -/
private def gammaTheta : gammaS A M ⟶ gammaS A N :=
  ((globalSections M).mapHomologicalComplex _).map (thetaK A f)

private lemma gammaTheta_singEps' (p : ℕ) (φ : (singChains M).X p ⟶ A) :
    (gammaTheta A f).f p ((singEps' A M).f p φ) =
      (singEps' A N).f p ((((singularChainComplexFunctor AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift ℤ))).map f).f p ≫ φ) := by
  have hθ := ConcreteCategory.congr_hom (congrArg (fun t => t.app (op ⊤)) (thetaKf_unit A f p))
    (reprFn A M p ⊤ (fnEquiv A M p φ))
  change (thetaKf A f p).hom.app (op ⊤) ((unitNat (singCochainTerm A M p)).app (op ⊤) (reprFn A M p
      ⊤ (fnEquiv A M p φ))) =
    (unitNat (singCochainTerm A N p)).app (op ⊤) (reprFn A N p ⊤ (fnEquiv A N p _))
  have key : (thetaP A f p).app (op ⊤) (reprFn A M p ⊤ (fnEquiv A M p φ)) =
      reprFn A N p ⊤ (fnEquiv A N p ((((singularChainComplexFunctor AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift ℤ))).map f).f p ≫ φ)) := by
    apply (fnEquiv A ((Opens.toTopCat N).obj ⊤) p).injective
    funext τ
    have h1 := fnEquiv_map A (fRes f ⊤) p (reprFn A M p ⊤ (fnEquiv A M p φ)) τ
    erw [h1]
    simp only [reprFn, Equiv.apply_symm_apply]
    erw [fnEquiv_map]
    rfl
  erw [hθ]
  exact congrArg (fun x => (unitNat (singCochainTerm A N p)).app (op ⊤) x) key

end Pushforward

section ConstCompat

private def constPt (A : AddCommGrpCat.{u}) (X : TopCat.{u}) :=
  (constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u} Limits.isTerminalTop).unit.app
      A

private lemma constPt_aug (A : AddCommGrpCat.{u}) (X : TopCat.{u}) (a : A) :
    ((constPt A X ≫ (globalSections X).map (constAugDeg0 A X)).hom a) =
      (singEps A X).f 0 (constCochain A ((Opens.toTopCat X).obj ⊤) a) := by
  unfold constPt
  simp only [constantSheafAdj, Adjunction.comp_unit_app, constantPresheafAdj_unit_app]
  have hn := congrArg (fun t => t.app (op ⊤))
    ((sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{u}).unit.naturality
        (constToCochain A X))
  have hn' := ConcreteCategory.congr_hom hn.symm a
  rw [Category.id_comp]
  exact hn'

variable {M N : TopCat.{u}} (f : N ⟶ M)

/-- The comparison `f⁻¹ A_M ⟶ A_N` of the statement. -/
private def toConstDef (A : AddCommGrpCat.{u}) :
    (TopCat.Sheaf.pullback AddCommGrpCat.{u} f).obj (constSheaf A M) ⟶ constSheaf A N :=
  (((constantSheafAdj (Opens.grothendieckTopology M) AddCommGrpCat.{u}
      Limits.isTerminalTop).comp
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f)).homEquiv
      A (constSheaf A N)).symm
    ((constantSheafAdj (Opens.grothendieckTopology N) AddCommGrpCat.{u}
        Limits.isTerminalTop).unit.app A ≫
      (constSheaf A N).obj.map (homOfLE le_top).op)

/-- The adjoint `A_M ⟶ f_* A_N` of the comparison. -/
private def thetaF (A : AddCommGrpCat.{u}) : constSheaf A M ⟶
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj (constSheaf A N) :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app (constSheaf A M) ≫
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map (toConstDef f A)

private lemma constPt_thetaF (A : AddCommGrpCat.{u}) :
    constPt A M ≫ (globalSections M).map (thetaF f A) =
      constPt A N ≫ (constSheaf A N).obj.map (homOfLE le_top).op := by
  have h0 := ((((constantSheafAdj (Opens.grothendieckTopology M) AddCommGrpCat.{u}
      Limits.isTerminalTop).comp
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f)).homEquiv
      A (constSheaf A N))).apply_symm_apply
    (constPt A N ≫ (constSheaf A N).obj.map (homOfLE le_top).op)
  have e : ∀ u : (TopCat.Sheaf.pullback AddCommGrpCat.{u} f).obj (constSheaf A M) ⟶ constSheaf A N,
      (((constantSheafAdj (Opens.grothendieckTopology M) AddCommGrpCat.{u}
        Limits.isTerminalTop).comp
          (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f)).homEquiv A (constSheaf A
              N)) u =
        constPt A M ≫ (globalSections M).map
          ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app (constSheaf A
              M) ≫
            (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map u) := by
    intro u
    erw [Adjunction.comp_homEquiv]
    simp only [Equiv.trans_apply, Adjunction.homEquiv_unit]
    rfl
  exact (e _).symm.trans h0

private lemma const_theta (A : AddCommGrpCat.{u}) (a : A) :
    (thetaKf A f 0).hom.app (op ⊤) ((singEps A M).f 0 (constCochain A ((Opens.toTopCat M).obj ⊤) a))
        =
      (singEps A N).f 0 (constCochain A ((Opens.toTopCat N).obj ⊤) a) := by
  let x0 : (singCochainTerm A M 0).obj (op ⊤) := constCochain A ((Opens.toTopCat M).obj ⊤) a
  have hθ := ConcreteCategory.congr_hom (congrArg (fun t => t.app (op ⊤)) (thetaKf_unit A f 0)) x0
  have key : (thetaP A f 0).app (op ⊤) (constCochain A ((Opens.toTopCat M).obj ⊤) a) =
      constCochain A ((Opens.toTopCat N).obj ⊤) a := by
    refine cochainEval_injective A _ 0 (funext fun σ => ?_)
    change cochainEval A _ 0 ((((singularChainComplexFunctor AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift ℤ))).map (fRes f ⊤)).f 0 ≫ constCochain A ((Opens.toTopCat M).obj ⊤)
          a) σ = _
    rw [cochainEval_map, cochainEval_constCochain]
    erw [cochainEval_constCochain]
  change (thetaKf A f 0).hom.app (op ⊤) ((unitNat (singCochainTerm A M 0)).app (op ⊤)
      (constCochain A ((Opens.toTopCat M).obj ⊤) a)) = (unitNat (singCochainTerm A N 0)).app (op ⊤)
      (constCochain A ((Opens.toTopCat N).obj ⊤) a)
  erw [hθ]
  exact congrArg (fun x => (unitNat (singCochainTerm A N 0)).app (op ⊤) x) key

private lemma map_homOfLE_top (A : AddCommGrpCat.{u}) (x : ((constSheaf A N).obj.obj (op ⊤))) :
    (constSheaf A N).obj.map (homOfLE le_top : (Opens.map f).obj ⊤ ⟶ ⊤).op x = x := by
  have : (homOfLE le_top : (Opens.map f).obj ⊤ ⟶ ⊤) = 𝟙 _ := Subsingleton.elim _ _
  rw [this]
  simp
  rfl

private lemma constAugDeg0_theta (A : AddCommGrpCat.{u}) :
    constAugDeg0 A M ≫ thetaKf A f 0 =
      thetaF f A ≫ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map (constAugDeg0 A N) := by
  let adj := constantSheafAdj (Opens.grothendieckTopology M) AddCommGrpCat.{u} Limits.isTerminalTop
  have e1 := adj.homEquiv_unit (X := A) (Y := (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj
    ((singCochainSheaves A N).X 0)) (f := constAugDeg0 A M ≫ thetaKf A f 0)
  have e2 := adj.homEquiv_unit (X := A) (Y := (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj
    ((singCochainSheaves A N).X 0)) (f := thetaF f A ≫ (TopCat.Sheaf.pushforward AddCommGrpCat.{u}
        f).map (constAugDeg0 A N))
  refine (adj.homEquiv A ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj
    ((singCochainSheaves A N).X 0))).injective (e1.trans (Eq.trans ?_ e2.symm))
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun a => ?_)
  change (thetaKf A f 0).hom.app (op ⊤) ((constAugDeg0 A M).hom.app (op ⊤) ((constPt A M).hom a)) =
    (constAugDeg0 A N).hom.app (op ⊤) ((thetaF f A).hom.app (op ⊤) ((constPt A M).hom a))
  have hL' : (constAugDeg0 A M).hom.app (op ⊤) ((constPt A M).hom a) =
      (singEps A M).f 0 (constCochain A ((Opens.toTopCat M).obj ⊤) a) := constPt_aug A M a
  have hT'' : (thetaF f A).hom.app (op ⊤) ((constPt A M).hom a) = (constPt A N).hom a :=
    (ConcreteCategory.congr_hom (constPt_thetaF f A) a).trans (map_homOfLE_top f A _)
  rw [hL', hT'']
  erw [const_theta f A a]
  exact (constPt_aug A N a).symm

end ConstCompat

section Assembly2

private lemma final_chase {C : Type*} [Category C] {P P' X1 X1' X2 X2' Y Y' : C}
    (a : P ⟶ X1) (c2 : X1 ⟶ X2) (s : Y ⟶ X2) [IsIso s] (Hp : Y ⟶ Y') (Ha : X1 ⟶ X1') (Hg : X2 ⟶ X2')
    (a' : P' ⟶ X1') (c2' : X1' ⟶ X2') (s' : Y' ⟶ X2') [IsIso s'] (SC : P ⟶ P')
    (F1 : a ≫ Ha = SC ≫ a') (h2 : c2 ≫ Hg = Ha ≫ c2') (h3 : s ≫ Hg = Hp ≫ s') :
    (a ≫ c2 ≫ inv s) ≫ Hp = SC ≫ (a' ≫ c2' ≫ inv s') := by
  have h4 : inv s ≫ Hp = Hg ≫ inv s' := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, h3, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  simp only [Category.assoc, h4, reassoc_of% h2, reassoc_of% F1]

/-- The comparison isomorphism `H^n(X, A_X) ≅ H^n_sing(X; A)`. -/
private def eIso (A : AddCommGrpCat.{u}) (M : TopCat.{u}) [MetrizableSpace M]
    (hM : LocallyContractibleSpace M) (n : ℕ) :
    (sheafCohomology M n).obj (constSheaf A M) ≅ (singCochains A M).homology n := by
  haveI := quasiIso_constAug A M hM
  haveI := quasiIso_singEps' A M
  haveI : IsIso (HomologicalComplex.homologyMap (singEps' A M) n) :=
    (quasiIsoAt_iff_isIso_homologyMap _ n).1 inferInstance
  exact sheafCohomologyIso (constSheaf A M) n ≪≫
    cmp2 (constSheaf A M) (singCochainSheaves A M) (constAug A M)
      (fun p => singCochainSheaves_isFlasque A M p) n ≪≫
    (asIso (HomologicalComplex.homologyMap (singEps' A M) n)).symm

/-- The pullback of singular cochains. -/
private def singPull (A : AddCommGrpCat.{u}) {M N : TopCat.{u}} (f : N ⟶ M) :
    singCochains A M ⟶ singCochains A N :=
  ((preadditiveYoneda.obj A).mapHomologicalComplex _).map
    ((HomologicalComplex.opFunctor _ _).map
      ((((singularChainComplexFunctor AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift ℤ))).map
          f).op))

private lemma singEps'_natural (A : AddCommGrpCat.{u}) {M N : TopCat.{u}} (f : N ⟶ M) :
    singEps' A M ≫ gammaMap f _ _ (thetaK A f) = singPull A f ≫ singEps' A N := by
  refine HomologicalComplex.hom_ext _ _ fun p => ?_
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun φ => ?_)
  exact gammaTheta_singEps' A f p φ

private lemma eIso_natural (A : AddCommGrpCat.{u}) {M N : TopCat.{u}} [MetrizableSpace M]
    [MetrizableSpace N]
    (hM : LocallyContractibleSpace M) (hN : LocallyContractibleSpace N) (f : N ⟶ M) (n : ℕ) :
    (eIso A M hM n).hom ≫ HomologicalComplex.homologyMap (singPull A f) n =
      sheafCohomologyPullback f (constSheaf A M) n ≫
        (sheafCohomology N n).map (toConstDef f A) ≫ (eIso A N hN n).hom := by
  haveI := quasiIso_constAug A M hM
  haveI := quasiIso_singEps' A M
  haveI := quasiIso_constAug A N hN
  haveI := quasiIso_singEps' A N
  have h1 := sheafCohomologyIso_natural f (constSheaf A M) (constSheaf A N) (toConstDef f A) n
  have hι : augDeg0 (constAug A M) ≫ (thetaK A f).f 0 =
      thetaF f A ≫ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map (augDeg0 (constAug A N)) := by
    rw [augDeg0_constAug, augDeg0_constAug]
    exact constAugDeg0_theta f A
  have h2 := cmp2_natural f (constSheaf A M) (singCochainSheaves A M) (constAug A M)
    (fun p => singCochainSheaves_isFlasque A M p) (constSheaf A N) (singCochainSheaves A N)
        (constAug A N)
    (fun p => singCochainSheaves_isFlasque A N p) (thetaF f A) (thetaK A f) hι n
  have h3 := congrArg (fun t => HomologicalComplex.homologyMap t n) (singEps'_natural A f)
  simp only [HomologicalComplex.homologyMap_comp] at h3
  haveI : IsIso (HomologicalComplex.homologyMap (singEps' A M) n) :=
    (quasiIsoAt_iff_isIso_homologyMap _ n).1 inferInstance
  haveI : IsIso (HomologicalComplex.homologyMap (singEps' A N) n) :=
    (quasiIsoAt_iff_isIso_homologyMap _ n).1 inferInstance
  exact final_chase _ _ (HomologicalComplex.homologyMap (singEps' A M) n) _ _ _ _ _
    (HomologicalComplex.homologyMap (singEps' A N) n) _ h1 h2 h3

end Assembly2

section CoefficientNaturality

/-- Godement double complexes map along a morphism of complexes of sheaves on one space. -/
private def godementDblHomSelf {T : TopCat.{u}}
    {K K' : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℕ} (θ : K ⟶ K') :
    DblHom (godementDbl K) (godementDbl K') where
  f p q := (globalSections T).map (((godementResolution T).map (θ.f p)).f q)
  dh p q := by
    simp only [godementDbl]
    rw [← Functor.map_comp, ← Functor.map_comp, ← HomologicalComplex.comp_f,
      ← HomologicalComplex.comp_f, ← Functor.map_comp, ← Functor.map_comp, θ.comm]
  dv p q := by
    simp only [godementDbl]
    rw [← Functor.map_comp, ← Functor.map_comp, HomologicalComplex.Hom.comm]

private lemma cmp2_natural_self {T : TopCat.{u}} (F : TopCat.Sheaf AddCommGrpCat.{u} T)
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℕ)
    (ι : (CochainComplex.single₀ _).obj F ⟶ K) [QuasiIso ι]
    (hK : ∀ p, TopCat.Presheaf.IsFlasque (K.X p).obj)
    (F' : TopCat.Sheaf AddCommGrpCat.{u} T)
    (K' : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℕ)
    (ι' : (CochainComplex.single₀ _).obj F' ⟶ K') [QuasiIso ι']
    (hK' : ∀ p, TopCat.Presheaf.IsFlasque (K'.X p).obj)
    (θF : F ⟶ F') (θ : K ⟶ K') (hι : augDeg0 ι ≫ θ.f 0 = θF ≫ augDeg0 ι') (n : ℕ) :
    (cmp2 F K ι hK n).hom ≫
        HomologicalComplex.homologyMap (((globalSections T).mapHomologicalComplex _).map θ) n =
      HomologicalComplex.homologyMap (((globalSections T).mapHomologicalComplex _).map
        ((godementResolution T).map θF)) n ≫ (cmp2 F' K' ι' hK' n).hom := by
  let Ψ := godementDblHomSelf θ
  have hcol : (godementColAug K hK).augHom ≫ Ψ.totHom =
      ((globalSections T).mapHomologicalComplex _).map θ ≫ (godementColAug K' hK').augHom := by
    refine Ψ.augHom_naturality (G := godementColAug K hK) (G' := godementColAug K' hK') _
      (fun p => ?_)
    change (globalSections T).map (θ.f p) ≫ (globalSections T).map ((godementUnit T).app (K'.X p)) =
      (globalSections T).map ((godementUnit T).app (K.X p)) ≫
        (globalSections T).map (((godementResolution T).map (θ.f p)).f 0)
    erw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (globalSections T).map ((godementUnit T).naturality (θ.f p))
  have hrow : (godementDbl K).rowAugHom (godementRowAug F K ι) ≫ Ψ.totHom =
      ((globalSections T).mapHomologicalComplex _).map ((godementResolution T).map θF) ≫
        (godementDbl K').rowAugHom (godementRowAug F' K' ι') := by
    refine Ψ.rowAugHom_naturality (G := godementRowAug F K ι) (G' := godementRowAug F' K' ι') _
      (fun p => ?_)
    change (globalSections T).map (((godementResolution T).map θF).f p) ≫
        (globalSections T).map (((godementResolution T).map (augDeg0 ι')).f p) =
      (globalSections T).map (((godementResolution T).map (augDeg0 ι)).f p) ≫
        (globalSections T).map (((godementResolution T).map (θ.f 0)).f p)
    rw [← Functor.map_comp, ← Functor.map_comp, ← HomologicalComplex.comp_f,
      ← HomologicalComplex.comp_f, ← Functor.map_comp, ← Functor.map_comp, hι]
  haveI := (godementColAug K hK).quasiIso_augHom
  haveI := (godementDbl K).quasiIso_rowAugHom (godementRowAug F K ι)
  haveI := (godementColAug K' hK').quasiIso_augHom
  haveI := (godementDbl K').quasiIso_rowAugHom (godementRowAug F' K' ι')
  have e1 := (HomologicalComplex.homologyMap_comp _ _ n).symm.trans
    ((congrArg (fun g => HomologicalComplex.homologyMap g n) hcol).trans
      (HomologicalComplex.homologyMap_comp _ _ n))
  have e2 := (HomologicalComplex.homologyMap_comp _ _ n).symm.trans
    ((congrArg (fun g => HomologicalComplex.homologyMap g n) hrow).trans
      (HomologicalComplex.homologyMap_comp _ _ n))
  haveI : IsIso (HomologicalComplex.homologyMap (godementColAug K hK).augHom n) :=
    (quasiIsoAt_iff_isIso_homologyMap _ n).1 inferInstance
  haveI : IsIso (HomologicalComplex.homologyMap ((godementDbl K).rowAugHom (godementRowAug F K ι))
      n) :=
    (quasiIsoAt_iff_isIso_homologyMap _ n).1 inferInstance
  haveI : IsIso (HomologicalComplex.homologyMap (godementColAug K' hK').augHom n) :=
    (quasiIsoAt_iff_isIso_homologyMap _ n).1 inferInstance
  haveI : IsIso (HomologicalComplex.homologyMap
      ((godementDbl K').rowAugHom (godementRowAug F' K' ι')) n) :=
    (quasiIsoAt_iff_isIso_homologyMap _ n).1 inferInstance
  unfold cmp2
  exact iso_square
    (b := HomologicalComplex.homologyMap ((godementDbl K).rowAugHom (godementRowAug F K ι)) n)
    (c := HomologicalComplex.homologyMap (godementColAug K hK).augHom n)
    (b' := HomologicalComplex.homologyMap ((godementDbl K').rowAugHom (godementRowAug F' K' ι')) n)
    (c' := HomologicalComplex.homologyMap (godementColAug K' hK').augHom n) _ _
    (HomologicalComplex.homologyMap Ψ.totHom n) e2 e1

private lemma sheafCohomologyIso_natural_self {T : TopCat.{u}}
    {F F' : TopCat.Sheaf AddCommGrpCat.{u} T} (g : F ⟶ F') (n : ℕ) :
    (sheafCohomologyIso F n).hom ≫ HomologicalComplex.homologyMap
        (((globalSections T).mapHomologicalComplex _).map ((godementResolution T).map g)) n =
      (sheafCohomology T n).map g ≫ (sheafCohomologyIso F' n).hom := by
  let Φ := ((godementSections T).mapHomologicalComplex _).map
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map g)
  haveI := isIso_colToTotal _ (isZero_godementSectionsDbl_X F)
  haveI := isIso_colToTotal _ (isZero_godementSectionsDbl_X F')
  have hX := homologyMap_inv_natural _ _ _ _ (colToTotal_natural _ _
    (isZero_godementSectionsDbl_X F) (isZero_godementSectionsDbl_X F') Φ) (n : ℤ)
  have e1 := HomologicalComplex.extendHomologyIso_hom_naturality
    (((globalSections T).mapHomologicalComplex _).map ((godementResolution T).map g))
    ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl
  rw [sheafCohomologyIso_hom F n, sheafCohomologyIso_hom F' n]
  exact ((Category.assoc _ _ _).trans ((congrArg (fun x => _ ≫ x) e1.symm).trans
    (Category.assoc _ _ _).symm)).trans ((congrArg (fun x => x ≫ _) hX.symm).trans
      (Category.assoc _ _ _))

variable {A A' : AddCommGrpCat.{u}} (a : A ⟶ A')

/-- Post-composition with `a : A ⟶ A'` on the presheaf of singular cochain complexes. -/
private def coefP (X : TopCat.{u}) : singCochainPresheaf A X ⟶ singCochainPresheaf A' X :=
  Functor.whiskerLeft ((Opens.toTopCat X).op ⋙
    ((singularChainComplexFunctor AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift ℤ))).op ⋙
      HomologicalComplex.opFunctor _ _)
    (NatTrans.mapHomologicalComplex (preadditiveYoneda.map a) _)

/-- Post-composition with `a` on the complex of presheaves of singular cochains. -/
private def coefPC (X : TopCat.{u}) :
    singCochainPresheafComplex A X ⟶ singCochainPresheafComplex A' X :=
  CochainComplex.ofHom
    (fun p => (Functor.whiskerRight (coefP a X) (HomologicalComplex.eval _ _ p) :
      singCochainTerm A X p ⟶ singCochainTerm A' X p)) (fun p => by
      rw [show (singCochainPresheafComplex A' X).d p (p + 1) = singCochainTermD A' X p from
          CochainComplex.of_d _ _ _,
        show (singCochainPresheafComplex A X).d p (p + 1) = singCochainTermD A X p from
          CochainComplex.of_d _ _ _]
      exact NatTrans.ext (funext fun U => ((coefP a X).app U).comm p (p + 1)))

/-- Post-composition with `a` on the sheafified singular cochains. -/
private def coefK (X : TopCat.{u}) : singCochainSheaves A X ⟶ singCochainSheaves A' X :=
  ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapHomologicalComplex
    _).map (coefPC a X)

private lemma cochainEval_comp (Y : TopCat.{u}) (n : ℕ) (φ : (singChains Y).X n ⟶ A)
    (σ : (TopCat.toSSet.obj Y).obj (op (SimplexCategory.mk n))) :
    cochainEval A' Y n (φ ≫ a) σ = a (cochainEval A Y n φ σ) := rfl

private lemma constAugDeg0_coef (X : TopCat.{u}) :
    constAugDeg0 A X ≫ (coefK a X).f 0 =
      (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map a ≫
        constAugDeg0 A' X := by
  have h : constToCochain A X ≫ (coefPC a X).f 0 =
      (Functor.const _).map a ≫ constToCochain A' X := by
    refine NatTrans.ext (funext fun U => AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => ?_))
    refine cochainEval_injective A' _ 0 (funext fun σ => ?_)
    change cochainEval A' _ 0 (constCochain A _ x ≫ a) σ =
      cochainEval A' _ 0 (constCochain A' _ (a x)) σ
    rw [cochainEval_comp, cochainEval_constCochain, cochainEval_constCochain]
  exact (Functor.map_comp _ _ _).symm.trans
    ((congrArg (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map h).trans
      (Functor.map_comp _ _ _))

private lemma singEps'_coef (X : TopCat.{u}) :
    singEps' A X ≫ ((globalSections X).mapHomologicalComplex _).map (coefK a X) =
      (NatTrans.mapHomologicalComplex (preadditiveYoneda.map a) _).app _ ≫ singEps' A' X := by
  refine HomologicalComplex.hom_ext _ _ fun p => ?_
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun φ => ?_)
  have hn := ConcreteCategory.congr_hom (congrArg (fun t => t.app (op ⊤))
    ((sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{u}).unit.naturality
      ((coefPC a X).f p))) (reprFn A X p ⊤ (fnEquiv A X p φ))
  have key : ((coefPC a X).f p).app (op ⊤) (reprFn A X p ⊤ (fnEquiv A X p φ)) =
      reprFn A' X p ⊤ (fnEquiv A' X p (φ ≫ a)) := by
    apply (fnEquiv A' ((Opens.toTopCat X).obj ⊤) p).injective
    funext τ
    simp only [reprFn, Equiv.apply_symm_apply]
    exact congrArg a (congrFun ((fnEquiv A _ p).apply_symm_apply _) τ)
  change ((coefK a X).f p).hom.app (op ⊤) ((unitNat (singCochainTerm A X p)).app (op ⊤)
      (reprFn A X p ⊤ (fnEquiv A X p φ))) =
    (unitNat (singCochainTerm A' X p)).app (op ⊤) (reprFn A' X p ⊤ (fnEquiv A' X p (φ ≫ a)))
  rw [← key]
  exact hn.symm

private lemma eIso_coef (M : TopCat.{u}) [MetrizableSpace M] (hM : LocallyContractibleSpace M)
    (n : ℕ) :
    (eIso A M hM n).hom ≫ HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex (preadditiveYoneda.map a) _).app _) n =
      (sheafCohomology M n).map
          ((constantSheaf (Opens.grothendieckTopology M) AddCommGrpCat.{u}).map a) ≫
        (eIso A' M hM n).hom := by
  haveI := quasiIso_constAug A M hM
  haveI := quasiIso_singEps' A M
  haveI := quasiIso_constAug A' M hM
  haveI := quasiIso_singEps' A' M
  have h1 := sheafCohomologyIso_natural_self
    ((constantSheaf (Opens.grothendieckTopology M) AddCommGrpCat.{u}).map a) n
  have hι : augDeg0 (constAug A M) ≫ (coefK a M).f 0 =
      (constantSheaf (Opens.grothendieckTopology M) AddCommGrpCat.{u}).map a ≫
        augDeg0 (constAug A' M) := by
    rw [augDeg0_constAug, augDeg0_constAug]
    exact constAugDeg0_coef a M
  have h2 := cmp2_natural_self (constSheaf A M) (singCochainSheaves A M) (constAug A M)
    (fun p => singCochainSheaves_isFlasque A M p) (constSheaf A' M) (singCochainSheaves A' M)
    (constAug A' M) (fun p => singCochainSheaves_isFlasque A' M p) _ (coefK a M) hι n
  have h3 := congrArg (fun t => HomologicalComplex.homologyMap t n) (singEps'_coef a M)
  simp only [HomologicalComplex.homologyMap_comp] at h3
  haveI : IsIso (HomologicalComplex.homologyMap (singEps' A M) n) :=
    (quasiIsoAt_iff_isIso_homologyMap _ n).1 inferInstance
  haveI : IsIso (HomologicalComplex.homologyMap (singEps' A' M) n) :=
    (quasiIsoAt_iff_isIso_homologyMap _ n).1 inferInstance
  exact final_chase _ _ (HomologicalComplex.homologyMap (singEps' A M) n) _ _ _ _ _
    (HomologicalComplex.homologyMap (singEps' A' M) n) _ h1 h2 h3

end CoefficientNaturality

end SingularComparison

open SingularComparison in
/-- The cohomology `H^n(M, A_M)` of the constant sheaf on a metrizable, locally contractible space
`M` is isomorphic to the singular cohomology `H^n(Hom(C_•(M; ℤ), A))`, naturally in both
arguments. For continuous maps `f : N ⟶ M`, the sheaf side acts by `sheafCohomologyPullback`
followed by the canonical map `f⁻¹ A_M ⟶ A_N`, and the singular side by the pullback of singular
cochains. For homomorphisms `a : A ⟶ A'`, the sheaf side acts by the induced map of constant
sheaves, and the singular side by post-composition of cochains with `a`. -/
public theorem exists_sheafCohomology_constantSheaf_iso_singularCohomology_natural :
    let constSh : AddCommGrpCat.{u} → ∀ M : TopCat.{u}, TopCat.Sheaf AddCommGrpCat.{u} M :=
      fun A M ↦ (constantSheaf (Opens.grothendieckTopology M) AddCommGrpCat.{u}).obj A
    let singH : AddCommGrpCat.{u} → ℕ → TopCat.{u}ᵒᵖ ⥤ AddCommGrpCat.{u} := fun A n ↦
      ((singularChainComplexFunctor AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift ℤ))).op ⋙
        HomologicalComplex.opFunctor _ _ ⋙
          (preadditiveYoneda.obj A).mapHomologicalComplex _ ⋙
            HomologicalComplex.homologyFunctor _ _ n
    let singCoef : ∀ {A A' : AddCommGrpCat.{u}}, (A ⟶ A') → ∀ n, singH A n ⟶ singH A' n :=
      fun a n ↦ Functor.whiskerRight (Functor.whiskerLeft
        (((singularChainComplexFunctor AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift ℤ))).op ⋙
          HomologicalComplex.opFunctor _ _)
        (NatTrans.mapHomologicalComplex (preadditiveYoneda.map a) _))
        (HomologicalComplex.homologyFunctor _ _ n)
    let toConst : ∀ (A : AddCommGrpCat.{u}) {M N : TopCat.{u}} (f : N ⟶ M),
        (TopCat.Sheaf.pullback AddCommGrpCat.{u} f).obj (constSh A M) ⟶ constSh A N :=
      fun A {M N} f ↦
        (((constantSheafAdj (Opens.grothendieckTopology M) AddCommGrpCat.{u}
            Limits.isTerminalTop).comp
          (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f)).homEquiv
            A (constSh A N)).symm
          ((constantSheafAdj (Opens.grothendieckTopology N) AddCommGrpCat.{u}
              Limits.isTerminalTop).unit.app A ≫
            (constSh A N).obj.map (homOfLE le_top).op)
    ∃ e : ∀ (A : AddCommGrpCat.{u}) (M : TopCat.{u}) [MetrizableSpace M],
        LocallyContractibleSpace M → ∀ n : ℕ,
        (sheafCohomology M n).obj (constSh A M) ≅ (singH A n).obj (op M),
      (∀ (A : AddCommGrpCat.{u}) (M N : TopCat.{u}) [MetrizableSpace M] [MetrizableSpace N]
        (hM : LocallyContractibleSpace M) (hN : LocallyContractibleSpace N) (f : N ⟶ M) (n : ℕ),
        (e A M hM n).hom ≫ (singH A n).map f.op =
          sheafCohomologyPullback f (constSh A M) n ≫ (sheafCohomology N n).map (toConst A f) ≫
            (e A N hN n).hom) ∧
      ∀ (A A' : AddCommGrpCat.{u}) (a : A ⟶ A') (M : TopCat.{u}) [MetrizableSpace M]
        (hM : LocallyContractibleSpace M) (n : ℕ),
        (sheafCohomology M n).map
            ((constantSheaf (Opens.grothendieckTopology M) AddCommGrpCat.{u}).map a) ≫
          (e A' M hM n).hom = (e A M hM n).hom ≫ (singCoef a n).app (op M) :=
  ⟨fun A M _ hM n => eIso A M hM n, fun A _ _ _ _ hM hN f n => eIso_natural A hM hN f n,
    fun _ _ a M _ hM n => (eIso_coef a M hM n).symm⟩

open SingularComparison in
/-- For an abelian group `A`, the cohomology `H^n(M, A_M)` of the constant sheaf on a metrizable,
locally contractible space `M` is isomorphic to the singular cohomology
`H^n(Hom(C_•(M; ℤ), A))`. The isomorphisms are natural in continuous maps `f : N ⟶ M` between
such spaces: on the sheaf side, `f` acts by `sheafCohomologyPullback` followed by the canonical
map `f⁻¹ A_M ⟶ A_N`; on the singular side, `f` acts by the pullback of singular cochains. -/
@[mmp "lem_mmp_locally_contractible_singular_sheaf_comparison"]
public theorem exists_sheafCohomology_constantSheaf_iso_singularCohomology
    (A : AddCommGrpCat.{u}) :
    let constSh : ∀ M : TopCat.{u}, TopCat.Sheaf AddCommGrpCat.{u} M := fun M ↦
      (constantSheaf (Opens.grothendieckTopology M) AddCommGrpCat.{u}).obj A
    let singH : ℕ → TopCat.{u}ᵒᵖ ⥤ AddCommGrpCat.{u} := fun n ↦
      ((singularChainComplexFunctor AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift ℤ))).op ⋙
        HomologicalComplex.opFunctor _ _ ⋙
          (preadditiveYoneda.obj A).mapHomologicalComplex _ ⋙
            HomologicalComplex.homologyFunctor _ _ n
    let toConst : ∀ {M N : TopCat.{u}} (f : N ⟶ M),
        (TopCat.Sheaf.pullback AddCommGrpCat.{u} f).obj (constSh M) ⟶ constSh N :=
      fun {M N} f ↦
        (((constantSheafAdj (Opens.grothendieckTopology M) AddCommGrpCat.{u}
            Limits.isTerminalTop).comp
          (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f)).homEquiv
            A (constSh N)).symm
          ((constantSheafAdj (Opens.grothendieckTopology N) AddCommGrpCat.{u}
              Limits.isTerminalTop).unit.app A ≫
            (constSh N).obj.map (homOfLE le_top).op)
    ∃ e : ∀ (M : TopCat.{u}) [MetrizableSpace M], LocallyContractibleSpace M → ∀ n : ℕ,
        (sheafCohomology M n).obj (constSh M) ≅ (singH n).obj (op M),
      ∀ (M N : TopCat.{u}) [MetrizableSpace M] [MetrizableSpace N]
        (hM : LocallyContractibleSpace M) (hN : LocallyContractibleSpace N) (f : N ⟶ M) (n : ℕ),
        (e M hM n).hom ≫ (singH n).map f.op =
          sheafCohomologyPullback f (constSh M) n ≫ (sheafCohomology N n).map (toConst f) ≫
            (e N hN n).hom :=
  ⟨exists_sheafCohomology_constantSheaf_iso_singularCohomology_natural.choose A,
    exists_sheafCohomology_constantSheaf_iso_singularCohomology_natural.choose_spec.1 A⟩

end

end MMP.Analytic
