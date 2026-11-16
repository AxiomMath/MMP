module

public import MMP.Analysis.Complex.Dolbeault.Basic
public import MMP.Analysis.Complex.Submanifold
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Combinatorics.Quiver.ReflQuiver

/-!
# The Dolbeault resolution of the sheaf of holomorphic functions

A holomorphic function `f` on an open `U ⊆ ℂⁿ` is a smooth `(0, 0)`-form with `∂̄ f = 0`. This
gives the augmentation `𝒪 ⟶ ℰ^{0,0}` of the Dolbeault complex, which is injective on sections.

## Main definitions

* `MMP.Analytic.holomorphicSheafAb`: the sheaf of abelian groups underlying `𝒪_{ℂⁿ}`.
* `MMP.Analytic.holomorphicToDolbeault`: the inclusion `𝒪 ⟶ ℰ^{0,0}` of the underlying sheaf of
  abelian groups of `𝒪_{ℂⁿ}` into smooth functions.
* `MMP.Analytic.dolbeaultAugmentation`: the augmentation `𝒪[0] ⟶ ℰ^{0,•}`.

## Main results

* `MMP.Analytic.holomorphicToDolbeault_comp_dbarHom`: `∂̄ ∘ (𝒪 ⟶ ℰ^{0,0}) = 0`.
* `MMP.Analytic.exact_holomorphicToDolbeault_dbarHom`: `𝒪 ⟶ ℰ^{0,0} ⟶ ℰ^{0,1}` is exact.
* `MMP.Analytic.quasiIso_dolbeaultAugmentation`: if every `∂̄`-closed form of positive degree is
  locally `∂̄`-exact, then `𝒪[0] ⟶ ℰ^{0,•}` is a quasi-isomorphism.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite
open scoped Manifold ContDiff

namespace MMP.Analytic

variable {n : ℕ}

variable (n) in
/-- The underlying sheaf of abelian groups of the sheaf `𝒪` of holomorphic functions on `ℂⁿ`, the
sheaf of abelian groups underlying the unit module over `holomorphicRingCatSheaf`. -/
noncomputable abbrev holomorphicSheafAb :
    TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of (EuclideanSpace ℂ (Fin n))) :=
  (SheafOfModules.toSheaf _).obj
    (SheafOfModules.unit (holomorphicRingCatSheaf n (EuclideanSpace ℂ (Fin n))))

local notation "𝒪ab[" n "]" => holomorphicSheafAb n

/-- A holomorphic function on `U`, as a `(0, 0)`-form: the coefficient of `dz̄_∅` is the
function extended by zero, all other coefficients vanish. -/
noncomputable def holomorphicForm {U : Opens (EuclideanSpace ℂ (Fin n))} (f : U → ℂ) :
    Finset (Fin n) → EuclideanSpace ℂ (Fin n) → ℂ :=
  fun I => if I = ∅ then extendByZero f else 0

/-- The `(0, 0)`-form of a holomorphic function on `U` is a smooth `(0, 0)`-form on `U`. -/
lemma holomorphicForm_mem_dolbeaultSections {U : Opens (TopCat.of (EuclideanSpace ℂ (Fin n)))}
    (f : 𝒪ab[n].obj.obj (op U)) :
    holomorphicForm (U := U) f.1 ∈ dolbeaultSections n 0 (U : Set _) := by
  have hf : ContMDiff 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) ∞ f.1 :=
    smoothSheaf.contMDiff_section (IM := 𝓘(ℂ, EuclideanSpace ℂ (Fin n))) (I := 𝓘(ℂ))
      (N := ℂ) f
  have hd : ContDiffOn ℂ ∞ (extendByZero (U := U) f.1) U :=
    (contMDiff_iff_contDiffOn_extendByZero f.1).1 hf
  refine ⟨fun I hI => ?_, fun I => ?_, fun I z hz => ?_⟩
  · simp [holomorphicForm, Finset.card_eq_zero.not.1 hI]
  · unfold holomorphicForm
    split_ifs
    · exact hd.restrict_scalars ℝ
    · exact contDiffOn_const
  · unfold holomorphicForm
    split_ifs
    · exact extendByZero_of_notMem _ hz
    · rfl

/-- The inclusion `𝒪(U) → ℰ^{0,0}(U)`. -/
noncomputable def holomorphicToDolbeaultSections
    (U : Opens (TopCat.of (EuclideanSpace ℂ (Fin n)))) :
    𝒪ab[n].obj.obj (op U) →+ dolbeaultSections n 0 (U : Set _) where
  toFun f := ⟨holomorphicForm (U := U) f.1, holomorphicForm_mem_dolbeaultSections f⟩
  map_zero' := by
    ext I z
    simp only [holomorphicForm, ZeroMemClass.coe_zero, Pi.zero_apply]
    split_ifs
    · by_cases hz : z ∈ U
      · rw [extendByZero_of_mem _ hz]
        rfl
      · exact extendByZero_of_notMem _ hz
    · rfl
  map_add' a b := by
    ext I z
    simp only [holomorphicForm, AddMemClass.coe_add, Pi.add_apply]
    split_ifs
    · by_cases hz : z ∈ U
      · simp only [extendByZero_of_mem _ hz]
        rfl
      · simp [extendByZero_of_notMem _ hz]
    · simp

/-- The coefficients of `holomorphicToDolbeaultSections U f` are those of `holomorphicForm f`. -/
@[simp]
lemma holomorphicToDolbeaultSections_apply (U : Opens (TopCat.of (EuclideanSpace ℂ (Fin n))))
    (f : 𝒪ab[n].obj.obj (op U)) (I : Finset (Fin n)) :
    (holomorphicToDolbeaultSections U f).1 I = holomorphicForm (U := U) f.1 I := rfl

/-- The inclusion `𝒪(U) → ℰ^{0,0}(U)` is injective. -/
lemma holomorphicToDolbeaultSections_injective
    (U : Opens (TopCat.of (EuclideanSpace ℂ (Fin n)))) :
    Function.Injective (holomorphicToDolbeaultSections U) := by
  intro a b h
  apply Subtype.ext
  funext z
  have := congrFun (congrArg (fun s => (s : dolbeaultSections n 0 (U : Set _)).1 ∅) h) z.1
  change holomorphicForm (U := U) a.1 ∅ z.1 = holomorphicForm (U := U) b.1 ∅ z.1 at this
  unfold holomorphicForm at this
  rw [ite_eq_left rfl, ite_eq_left rfl] at this
  simpa only [extendByZero, dite_eq_left z.2] using this

variable (n) in
/-- The augmentation `𝒪 ⟶ ℰ^{0,0}` of the Dolbeault complex. -/
noncomputable def holomorphicToDolbeault : 𝒪ab[n] ⟶ dolbeaultSheaf n 0 :=
  ObjectProperty.homMk
    { app U := AddCommGrpCat.ofHom (holomorphicToDolbeaultSections U.unop)
      naturality {U V} h := by
        ext f : 2
        apply Subtype.ext
        funext I z
        change holomorphicForm (U := V.unop) (fun x => f.1 ⟨x.1, h.unop.le x.2⟩) I z =
          ((V.unop : Opens _) : Set _).indicator (holomorphicForm (U := U.unop) f.1 I) z
        unfold holomorphicForm
        by_cases hz : z ∈ ((V.unop : Opens _) : Set _)
        · rw [Set.indicator_of_mem hz]
          split_ifs
          · rw [extendByZero_of_mem _ hz, extendByZero_of_mem _ (h.unop.le hz)]
          · rfl
        · rw [Set.indicator_of_notMem hz]
          split_ifs
          · exact extendByZero_of_notMem _ hz
          · rfl }

/-- On sections over `U`, `holomorphicToDolbeault` is `holomorphicToDolbeaultSections U`. -/
@[simp]
lemma holomorphicToDolbeault_app_apply (U : (Opens (TopCat.of (EuclideanSpace ℂ (Fin n))))ᵒᵖ)
    (f : 𝒪ab[n].obj.obj U) :
    (holomorphicToDolbeault n).hom.app U f = holomorphicToDolbeaultSections U.unop f := rfl

private lemma dbarForm_singleton (w : Finset (Fin n) → EuclideanSpace ℂ (Fin n) → ℂ) (j : Fin n)
    (z : EuclideanSpace ℂ (Fin n)) : dbarForm w {j} z = dbarPartial j (w ∅) z := by
  simp [dbarForm, dolbeaultSign]

/-- A smooth function on an open `U` with `∂̄ f = 0` on `U` is a section of `𝒪` over `U`. -/
lemma exists_holomorphicToDolbeaultSections_eq_of_dbarPartial_eq_zero
    {U : Opens (TopCat.of (EuclideanSpace ℂ (Fin n)))} (s : dolbeaultSections n 0 (U : Set _))
    (hs : ∀ j, ∀ z ∈ (U : Set (EuclideanSpace ℂ (Fin n))), dbarPartial j (s.1 ∅) z = 0) :
    ∃ f, holomorphicToDolbeaultSections U f = s := by
  have hc : ContDiffOn ℂ ∞ (s.1 ∅) U :=
    contDiffOn_complex_of_dbarPartial_eq_zero U.isOpen (s.2.2.1 ∅) fun z hz j => hs j z hz
  let g : U → ℂ := fun x => s.1 ∅ x
  have hge : ∀ z ∈ (U : Set (EuclideanSpace ℂ (Fin n))), extendByZero (U := U) g z = s.1 ∅ z :=
    fun z hz => extendByZero_of_mem g hz
  have hg : ContMDiff 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) ∞ g :=
    (contMDiff_iff_contDiffOn_extendByZero g).2 (hc.congr hge)
  refine ⟨⟨g, hg⟩, Subtype.ext ?_⟩
  refine dolbeaultSections_ext (holomorphicForm_mem_dolbeaultSections _) s.2 fun I z hz => ?_
  change holomorphicForm (U := U) g I z = s.1 I z
  unfold holomorphicForm
  split_ifs with hI
  · subst hI
    exact hge z hz
  · exact (congrFun (s.2.1 I (by simpa [Finset.card_eq_zero] using hI)) z).symm

variable (n) in
/-- The composite `𝒪 ⟶ ℰ^{0,0} ⟶ ℰ^{0,1}` vanishes: `∂̄ f = 0` for holomorphic `f`. -/
lemma holomorphicToDolbeault_comp_dbarHom :
    holomorphicToDolbeault n ≫ dbarHom n 0 = 0 := by
  refine InducedCategory.hom_ext (NatTrans.ext (funext fun U => AddCommGrpCat.ext fun f => ?_))
  apply Subtype.ext
  funext I z
  change ((dbarHom n 0).hom.app U ((holomorphicToDolbeault n).hom.app U f)).1 I z = 0
  rw [dbarHom_app_apply]
  by_cases hz : z ∈ ((U.unop : Opens _) : Set _)
  · rw [Set.indicator_of_mem hz]
    by_cases hI : I.card = 1
    · obtain ⟨j, rfl⟩ := Finset.card_eq_one.1 hI
      rw [dbarForm_singleton]
      have hf : ContMDiff 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) ∞ f.1 :=
        smoothSheaf.contMDiff_section (IM := 𝓘(ℂ, EuclideanSpace ℂ (Fin n))) (I := 𝓘(ℂ))
          (N := ℂ) f
      have hd := ((contMDiff_iff_contDiffOn_extendByZero f.1).1 hf).differentiableOn (by simp)
      have hdz : DifferentiableAt ℂ (extendByZero (U := U.unop) f.1) z :=
        hd.differentiableAt ((U.unop : Opens _).isOpen.mem_nhds hz)
      change dbarPartial j (holomorphicForm (U := U.unop) f.1 ∅) z = 0
      unfold holomorphicForm
      rw [ite_eq_left rfl]
      exact dbarPartial_eq_zero_of_differentiableAt hdz j
    · exact congrFun (dbarForm_of_degree ((holomorphicToDolbeault n).hom.app U f).2.1 I hI) z
  · simp [hz]

section Criteria

open CategoryTheory.Limits

/-- A short complex of sheaves of abelian groups is exact if every section of the middle term
killed by `g` is, near every point, the image of a section under `f`. -/
theorem exact_of_forall_exists_map_eq {X : TopCat.{0}}
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X))
    (h : ∀ (U : Opens X) (s : S.X₂.obj.obj (op U)), S.g.hom.app (op U) s = 0 →
      ∀ x ∈ U, ∃ (V : Opens X) (_ : x ∈ V) (i : V ⟶ U) (t : S.X₁.obj.obj (op V)),
        S.f.hom.app (op V) t = S.X₂.obj.map i.op s) :
    S.Exact := by
  rw [TopCat.Sheaf.exact_iff_stalkFunctor_map_exact]
  intro x
  rw [ShortComplex.ab_exact_iff]
  intro y hy
  obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq S.X₂.presheaf y
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map S.g.hom
    (S.X₂.presheaf.germ U x hxU s) = 0 at hy
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at hy
  obtain ⟨W, hxW, iU, iU', hW⟩ := S.X₃.presheaf.germ_eq x hxU hxU _ 0 (hy.trans (map_zero _).symm)
  rw [map_zero, ← ConcreteCategory.comp_apply, ← S.g.hom.naturality,
    ConcreteCategory.comp_apply] at hW
  obtain ⟨V, hxV, i, t, ht⟩ := h W _ hW x hxW
  refine ⟨S.X₁.presheaf.germ V x hxV t, ?_⟩
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map S.f.hom
    (S.X₁.presheaf.germ V x hxV t) = _
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  change S.X₂.presheaf.germ V x hxV (S.f.hom.app (op V) t) = _
  rw [ht]
  change S.X₂.presheaf.germ V x hxV (S.X₂.presheaf.map i.op (S.X₂.presheaf.map iU.op s)) = _
  rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]

/-- An augmentation `X[0] ⟶ A` of an `ℕ`-indexed cochain complex in an abelian category is a
quasi-isomorphism when `0 → X → A⁰ → A¹` is exact and `A` is exact in positive degrees. -/
theorem quasiIso_fromSingle₀Equiv_symm {C : Type*} [Category C] [Abelian C]
    (A : CochainComplex C ℕ) {X : C} (f : X ⟶ A.X 0) (hf : f ≫ A.d 0 1 = 0)
    (h₀ : (ShortComplex.mk f (A.d 0 1) hf).Exact) [Mono f] (h : ∀ q : ℕ, A.ExactAt (q + 1)) :
    QuasiIso ((A.fromSingle₀Equiv X).symm ⟨f, hf⟩) := by
  rw [quasiIso_iff]
  intro i
  rcases i with _ | q
  · rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
    · change (ShortComplex.mk (((A.fromSingle₀Equiv X).symm ⟨f, hf⟩).f 0) (A.d 0 1) _).Exact ∧
        Mono (((A.fromSingle₀Equiv X).symm ⟨f, hf⟩).f 0)
      simp only [CochainComplex.fromSingle₀Equiv_symm_apply_f_zero]
      exact ⟨h₀, (inferInstance : Mono f)⟩
    · exact ((CochainComplex.single₀ C).obj X).shape 0 0 (by decide)
    · exact HomologicalComplex.single_obj_d (ComplexShape.up ℕ) 0 X 0 1
    · exact A.shape 0 0 (by decide)
  · rw [quasiIsoAt_iff_exactAt _ _ (CochainComplex.exactAt_succ_single_obj X q)]
    exact h q

end Criteria

section Augmentation

variable (n) in
/-- The differential `ℰ^{0,q} ⟶ ℰ^{0,q+1}` of the Dolbeault complex is `dbarHom n q`. -/
lemma dolbeaultComplex_d (q : ℕ) : (dolbeaultComplex n).d q (q + 1) = dbarHom n q :=
  CochainComplex.of_d _ _ q

variable (n) in
/-- The augmentation `𝒪[0] ⟶ ℰ^{0,•}` of the Dolbeault complex. -/
noncomputable def dolbeaultAugmentation :
    (CochainComplex.single₀ _).obj (holomorphicSheafAb n) ⟶ dolbeaultComplex n :=
  ((dolbeaultComplex n).fromSingle₀Equiv _).symm
    ⟨holomorphicToDolbeault n, by
      rw [dolbeaultComplex_d]
      exact holomorphicToDolbeault_comp_dbarHom n⟩

variable (n) in
/-- The augmentation `𝒪 ⟶ ℰ^{0,0}` is a monomorphism of sheaves of abelian groups. -/
theorem mono_holomorphicToDolbeault : Mono (holomorphicToDolbeault n) := by
  have : ∀ U, Mono (((sheafToPresheaf _ _).map (holomorphicToDolbeault n)).app U) := fun U => by
    rw [AddCommGrpCat.mono_iff_injective]
    exact holomorphicToDolbeaultSections_injective U.unop
  exact (sheafToPresheaf _ _).mono_of_mono_map (NatTrans.mono_of_mono_app _)

/-- The Dolbeault complex is exact in degree `q + 1` once every `∂̄`-closed `(0, q + 1)`-form is
locally `∂̄`-exact. -/
theorem exactAt_dolbeaultComplex_of_local (q : ℕ)
    (h : ∀ (U : Opens (EuclideanSpace ℂ (Fin n))) (s : dolbeaultSections n (q + 1) U),
      dbarSections n (q + 1) U s = 0 → ∀ x ∈ U, ∃ (V : Opens (EuclideanSpace ℂ (Fin n)))
        (_ : x ∈ V) (hVU : V ≤ U) (t : dolbeaultSections n q V),
        dbarSections n q V t = dolbeaultRestrict n (q + 1) hVU s) :
    (dolbeaultComplex n).ExactAt (q + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ q (q + 1) (q + 2) (by simp) (by simp)]
  apply exact_of_forall_exists_map_eq
  intro U s hs x hx
  change ((dolbeaultComplex n).d (q + 1) (q + 1 + 1)).hom.app (op U) s = 0 at hs
  rw [dolbeaultComplex_d] at hs
  obtain ⟨V, hxV, hVU, t, ht⟩ := h U s hs x hx
  refine ⟨V, hxV, homOfLE hVU, t, ?_⟩
  change ((dolbeaultComplex n).d q (q + 1)).hom.app (op V) t = _
  rwa [dolbeaultComplex_d]

variable (n) in
/-- `𝒪 ⟶ ℰ^{0,0} ⟶ ℰ^{0,1}` is exact: a smooth function annihilated by `∂̄` is holomorphic. -/
theorem exact_holomorphicToDolbeault_dbarHom :
    (ShortComplex.mk (holomorphicToDolbeault n) ((dolbeaultComplex n).d 0 1)
      (by rw [dolbeaultComplex_d]; exact holomorphicToDolbeault_comp_dbarHom n)).Exact := by
  apply exact_of_forall_exists_map_eq
  intro U s hs x hx
  change ((dolbeaultComplex n).d 0 (0 + 1)).hom.app (op U) s = 0 at hs
  rw [dolbeaultComplex_d] at hs
  refine ⟨U, hx, 𝟙 U, ?_⟩
  have hcr : ∀ j, ∀ z ∈ (U : Set (EuclideanSpace ℂ (Fin n))), dbarPartial j (s.1 ∅) z = 0 := by
    intro j z hz
    have := congrFun (congrArg (fun w : dolbeaultSections n 1 (U : Set _) => w.1 {j}) hs) z
    change (U : Set _).indicator (dbarForm s.1 {j}) z = 0 at this
    rwa [Set.indicator_of_mem hz, dbarForm_singleton] at this
  obtain ⟨f, hf⟩ := exists_holomorphicToDolbeaultSections_eq_of_dbarPartial_eq_zero s hcr
  refine ⟨f, ?_⟩
  change holomorphicToDolbeaultSections U f = (dolbeaultSheaf n 0).obj.map (𝟙 (op U)) s
  rw [CategoryTheory.Functor.map_id]
  exact hf

/-- **The Dolbeault resolution.** If every `∂̄`-closed form of positive degree is locally
`∂̄`-exact, the augmentation `𝒪[0] ⟶ ℰ^{0,•}` is a quasi-isomorphism. -/
theorem quasiIso_dolbeaultAugmentation
    (h : ∀ (q : ℕ) (U : Opens (EuclideanSpace ℂ (Fin n))) (s : dolbeaultSections n (q + 1) U),
      dbarSections n (q + 1) U s = 0 → ∀ x ∈ U, ∃ (V : Opens (EuclideanSpace ℂ (Fin n)))
        (_ : x ∈ V) (hVU : V ≤ U) (t : dolbeaultSections n q V),
        dbarSections n q V t = dolbeaultRestrict n (q + 1) hVU s) :
    QuasiIso (dolbeaultAugmentation n) :=
  @quasiIso_fromSingle₀Equiv_symm _ _ _ _ _ _ _ (exact_holomorphicToDolbeault_dbarHom n)
    (mono_holomorphicToDolbeault n) fun q => exactAt_dolbeaultComplex_of_local q (h q)

end Augmentation

end MMP.Analytic
