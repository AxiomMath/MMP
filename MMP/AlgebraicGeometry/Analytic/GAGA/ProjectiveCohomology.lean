module

public import MMP.AlgebraicGeometry.Analytic.GAGA.Stalks
public import MMP.AlgebraicGeometry.Analytic.GAGA.ProjectiveSpaceTwists

/-!
# GAGA: cohomology of coherent sheaves on complex projective schemes

Let `X` be a projective scheme over `ℂ`, not necessarily reduced, and `F` a coherent sheaf on
`X`. Serre's comparison theorem says that for every `q` the comparison map
`c^q_F : H^q(X, F) → H^q(X^an, F^an)`, the pullback of cohomology along `α_X : X^an → X`
followed by `ι_F : α_X⁻¹ F → F^an`, is an isomorphism.

## Main results

* `MMP.Analytic.isIso_comparisonMap_of_isProjective`: `c^q_F` is an isomorphism for every
  coherent `F` on a projective `ℂ`-scheme and every `q`.

The proof embeds `X` as a closed subscheme of some `ℙᴺ_ℂ` with `N ≥ 1`, replaces `F` by its
direct image along the embedding, resolves that by finite sums of twisting sheaves `𝒪(k)`, and
descends along the short exact sequences of cycles of the resolution by the five lemma on the
long exact cohomology sequences, starting from the twisting sheaves themselves.

## Implementation notes

The degree `q` ranges over `ℤ`: both cohomology groups vanish in negative degrees, so the
statement for `q ≥ 0` is the content and the negative degrees come for free. Projectivity is
projectivity of the structure morphism `X → Spec ℂ`; no reducedness is assumed.

## References

* [Serre, *Géométrie algébrique et géométrie analytique*], §12, Théorème 1
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MMP.Analytic.Analytification
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)

namespace MMP.Analytic

/-- The five lemma in an abelian category, with the rows given by their arrows. -/
private lemma isIso_of_five {C : Type*} [Category C] [Abelian C]
    {A₁ A₂ A₃ A₄ A₅ B₁ B₂ B₃ B₄ B₅ : C}
    (f₁ : A₁ ⟶ A₂) (f₂ : A₂ ⟶ A₃) (f₃ : A₃ ⟶ A₄) (f₄ : A₄ ⟶ A₅)
    (g₁ : B₁ ⟶ B₂) (g₂ : B₂ ⟶ B₃) (g₃ : B₃ ⟶ B₄) (g₄ : B₄ ⟶ B₅)
    (e₁ : A₁ ⟶ B₁) (e₂ : A₂ ⟶ B₂) (e₃ : A₃ ⟶ B₃) (e₄ : A₄ ⟶ B₄) (e₅ : A₅ ⟶ B₅)
    (w₁ : f₁ ≫ e₂ = e₁ ≫ g₁) (w₂ : f₂ ≫ e₃ = e₂ ≫ g₂) (w₃ : f₃ ≫ e₄ = e₃ ≫ g₃)
    (w₄ : f₄ ≫ e₅ = e₄ ≫ g₄)
    (zf₁ : f₁ ≫ f₂ = 0) (zf₂ : f₂ ≫ f₃ = 0) (zf₃ : f₃ ≫ f₄ = 0)
    (zg₁ : g₁ ≫ g₂ = 0) (zg₂ : g₂ ≫ g₃ = 0) (zg₃ : g₃ ≫ g₄ = 0)
    (hf₁ : (ShortComplex.mk f₁ f₂ zf₁).Exact) (hf₂ : (ShortComplex.mk f₂ f₃ zf₂).Exact)
    (hf₃ : (ShortComplex.mk f₃ f₄ zf₃).Exact)
    (hg₁ : (ShortComplex.mk g₁ g₂ zg₁).Exact) (hg₂ : (ShortComplex.mk g₂ g₃ zg₂).Exact)
    (hg₃ : (ShortComplex.mk g₃ g₄ zg₃).Exact)
    (h₁ : IsIso e₁) (h₂ : IsIso e₂) (h₄ : IsIso e₄) (h₅ : IsIso e₅) : IsIso e₃ := by
  have hR₁ : (ComposableArrows.mk₄ f₁ f₂ f₃ f₄).Exact :=
    ComposableArrows.exact_of_δ₀ (ComposableArrows.exact₂_mk _ zf₁ hf₁)
      (ComposableArrows.exact_of_δ₀ (ComposableArrows.exact₂_mk _ zf₂ hf₂)
        (ComposableArrows.exact₂_mk _ zf₃ hf₃))
  have hR₂ : (ComposableArrows.mk₄ g₁ g₂ g₃ g₄).Exact :=
    ComposableArrows.exact_of_δ₀ (ComposableArrows.exact₂_mk _ zg₁ hg₁)
      (ComposableArrows.exact_of_δ₀ (ComposableArrows.exact₂_mk _ zg₂ hg₂)
        (ComposableArrows.exact₂_mk _ zg₃ hg₃))
  exact Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono hR₁ hR₂
    (ComposableArrows.homMk₄ e₁ e₂ e₃ e₄ e₅ w₁ w₂ w₃ w₄)
    (show Epi e₁ by infer_instance) h₂ h₄ (show Mono e₅ by infer_instance)

/-- If `K` is exact at `j` and `c.Rel i j`, then `0 → Z_i → K_i → Z_j → 0` is short exact. -/
private lemma shortExact_cycles {C : Type*} [Category C] [Abelian C] {ι : Type*}
    {c : ComplexShape ι} (K : HomologicalComplex C c) (i j : ι) (hij : c.Rel i j)
    (h : K.ExactAt j) :
    (ShortComplex.mk (K.iCycles i) (K.toCycles i j) (by
      rw [← cancel_mono (K.iCycles j), Category.assoc, K.toCycles_i, K.iCycles_d,
        zero_comp])).ShortExact := by
  obtain rfl : c.prev j = i := c.prev_eq' hij
  refine { exact := ?_, mono_f := inferInstance, epi_g := ?_ }
  · exact ShortComplex.exact_of_f_is_kernel _
      (isKernelOfComp (K.iCycles j) (K.d _ j) (K.cyclesIsKernel _ _ (c.next_eq' hij)) _
        (K.toCycles_i _ _))
  · exact (h : (K.sc j).Exact).epi_toCycles

/-- Sheaf cohomology vanishes in negative degrees. -/
private lemma isZero_sheafCohomology_of_neg {T : TopCat.{0}} {F : TopCat.Sheaf AddCommGrpCat.{0} T}
    {q : ℤ} (hq : q < 0) : IsZero ((sheafCohomology T q).obj F) := by
  let D := godementSectionsDoubleComplex T
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F)
  have hX : IsZero ((D.total (ComplexShape.up ℤ)).X q) := by
    rw [IsZero.iff_id_eq_zero]
    refine HomologicalComplex₂.total.hom_ext _ fun i j hij => ?_
    have : IsZero ((D.X i).X j) := by
      by_cases hi : i = 0
      · subst hi
        obtain rfl : j = q := by simpa using hij
        exact HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat _
          (fun k => by simp only [ComplexShape.embeddingUpNat_f]; omega)
      · exact (HomologicalComplex.eval _ _ j).map_isZero ((godementSections T).map_isZero
          (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi))
    exact this.eq_of_src _ _
  exact ((D.total _).sc q).isZero_homology_of_isZero_X₂ hX

/-- Sheaf cohomology preserves zero morphisms. -/
private instance sheafCohomology_preservesZeroMorphisms (T : TopCat.{0}) (q : ℤ) :
    (sheafCohomology T q).PreservesZeroMorphisms := by
  unfold sheafCohomology hypercohomology
  infer_instance

/-- The short complex of total complexes of Godement sections of a short complex of sheaves. -/
private noncomputable abbrev godementTot {T : TopCat.{0}}
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} T)) :
    ShortComplex (CochainComplex AddCommGrpCat.{0} ℤ) :=
  ShortComplex.mk
    ((HomologicalComplex₂.totalFunctor AddCommGrpCat.{0} (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (c₁₂ := ComplexShape.up ℤ)).map (((godementSections T).mapHomologicalComplex _).map
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map S.f)))
    ((HomologicalComplex₂.totalFunctor AddCommGrpCat.{0} (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (c₁₂ := ComplexShape.up ℤ)).map (((godementSections T).mapHomologicalComplex _).map
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map S.g)))
    (by
      rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, S.zero,
        Functor.map_zero, Functor.map_zero]
      ext n : 1
      exact HomologicalComplex₂.total.hom_ext _ fun _ _ h =>
        (HomologicalComplex₂.ιTotal_map _ _ _ _ _ _ _ h).trans
          (by
            simp only [Functor.mapHomologicalComplex_obj_X, HomologicalComplex.zero_f, zero_comp]
            exact Limits.comp_zero.symm))

/-- The connecting map `H^q(S.X₃) → H^r(S.X₁)`, `q + 1 = r`, with its source and target written
as sheaf cohomology. -/
private noncomputable def sheafCohomologyδ {T : TopCat.{0}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} T)} (hS : (godementTot S).ShortExact)
    (q r : ℤ) (h : q + 1 = r) : (sheafCohomology T q).obj S.X₃ ⟶ (sheafCohomology T r).obj S.X₁ :=
  hS.δ q r h

/-- `H^q(S.X₁) → H^q(S.X₂) → H^q(S.X₃)` composes to zero. -/
private lemma sheafCohomology_map_comp_map {T : TopCat.{0}}
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} T)) (q : ℤ) :
    (sheafCohomology T q).map S.f ≫ (sheafCohomology T q).map S.g = 0 := by
  rw [← Functor.map_comp, S.zero, Functor.map_zero]

/-- `H^q(S.X₂) → H^q(S.X₃) → H^{q+1}(S.X₁)` composes to zero. -/
private lemma sheafCohomology_map_comp_δ {T : TopCat.{0}}
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} T)) (hS : (godementTot S).ShortExact)
    (q r : ℤ) (h : q + 1 = r) : (sheafCohomology T q).map S.g ≫ sheafCohomologyδ hS q r h = 0 :=
  hS.comp_δ q r h

/-- `H^q(S.X₃) → H^{q+1}(S.X₁) → H^{q+1}(S.X₂)` composes to zero. -/
private lemma δ_comp_sheafCohomology_map {T : TopCat.{0}}
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} T)) (hS : (godementTot S).ShortExact)
    (q r : ℤ) (h : q + 1 = r) : sheafCohomologyδ hS q r h ≫ (sheafCohomology T r).map S.f = 0 :=
  hS.δ_comp q r h

/-- Exactness of `H^q(S.X₁) → H^q(S.X₂) → H^q(S.X₃)`. -/
private lemma sheafCohomology_exact₂ {T : TopCat.{0}}
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} T)) (hS : (godementTot S).ShortExact)
    (q : ℤ) :
    (ShortComplex.mk ((sheafCohomology T q).map S.f) ((sheafCohomology T q).map S.g)
      (sheafCohomology_map_comp_map S q)).Exact :=
  hS.homology_exact₂ q

/-- Exactness of `H^q(S.X₂) → H^q(S.X₃) → H^{q+1}(S.X₁)`. -/
private lemma sheafCohomology_exact₃ {T : TopCat.{0}}
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} T)) (hS : (godementTot S).ShortExact)
    (q r : ℤ) (h : q + 1 = r) :
    (ShortComplex.mk ((sheafCohomology T q).map S.g) (sheafCohomologyδ hS q r h)
      (sheafCohomology_map_comp_δ S hS q r h)).Exact :=
  hS.homology_exact₃ q r h

/-- Exactness of `H^q(S.X₃) → H^{q+1}(S.X₁) → H^{q+1}(S.X₂)`. -/
private lemma sheafCohomology_exact₁ {T : TopCat.{0}}
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} T)) (hS : (godementTot S).ShortExact)
    (q r : ℤ) (h : q + 1 = r) :
    (ShortComplex.mk (sheafCohomologyδ hS q r h) ((sheafCohomology T r).map S.f)
      (δ_comp_sheafCohomology_map S hS q r h)).Exact :=
  hS.homology_exact₁ q r h

/-- The five lemma on long exact cohomology sequences, around `H^q(S.X₃)`. -/
private lemma isIso_of_les_right {T T' : TopCat.{0}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} T)}
    {S' : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} T')} (hS : (godementTot S).ShortExact)
    (hS' : (godementTot S').ShortExact)
    (c₁ : ∀ q : ℤ, (sheafCohomology T q).obj S.X₁ ⟶ (sheafCohomology T' q).obj S'.X₁)
    (c₂ : ∀ q : ℤ, (sheafCohomology T q).obj S.X₂ ⟶ (sheafCohomology T' q).obj S'.X₂)
    (c₃ : ∀ q : ℤ, (sheafCohomology T q).obj S.X₃ ⟶ (sheafCohomology T' q).obj S'.X₃)
    (nf : ∀ q : ℤ, c₁ q ≫ (sheafCohomology T' q).map S'.f = (sheafCohomology T q).map S.f ≫ c₂ q)
    (ng : ∀ q : ℤ, c₂ q ≫ (sheafCohomology T' q).map S'.g = (sheafCohomology T q).map S.g ≫ c₃ q)
    (nδ : ∀ q : ℤ, hS.δ q (q + 1) rfl ≫ c₁ (q + 1) = c₃ q ≫ hS'.δ q (q + 1) rfl)
    (h₁ : ∀ q, IsIso (c₁ q)) (h₂ : ∀ q, IsIso (c₂ q)) (q : ℤ) : IsIso (c₃ q) :=
  isIso_of_five ((sheafCohomology T q).map S.f) ((sheafCohomology T q).map S.g)
    (sheafCohomologyδ hS q (q + 1) rfl) ((sheafCohomology T (q + 1)).map S.f)
    ((sheafCohomology T' q).map S'.f) ((sheafCohomology T' q).map S'.g)
    (sheafCohomologyδ hS' q (q + 1) rfl) ((sheafCohomology T' (q + 1)).map S'.f)
    (c₁ q) (c₂ q) (c₃ q) (c₁ (q + 1)) (c₂ (q + 1))
    (nf q).symm (ng q).symm (nδ q) (nf (q + 1)).symm
    (sheafCohomology_map_comp_map S q) (sheafCohomology_map_comp_δ S hS q (q + 1) rfl)
    (δ_comp_sheafCohomology_map S hS q (q + 1) rfl) (sheafCohomology_map_comp_map S' q)
    (sheafCohomology_map_comp_δ S' hS' q (q + 1) rfl)
    (δ_comp_sheafCohomology_map S' hS' q (q + 1) rfl)
    (sheafCohomology_exact₂ S hS q) (sheafCohomology_exact₃ S hS q (q + 1) rfl)
    (sheafCohomology_exact₁ S hS q (q + 1) rfl) (sheafCohomology_exact₂ S' hS' q)
    (sheafCohomology_exact₃ S' hS' q (q + 1) rfl) (sheafCohomology_exact₁ S' hS' q (q + 1) rfl)
    (h₁ q) (h₂ q) (h₁ (q + 1)) (h₂ (q + 1))

/-- The five lemma on long exact cohomology sequences, around `H^q(S.X₂)`, with `p + 1 = q`. -/
private lemma isIso_of_les_mid {T T' : TopCat.{0}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} T)}
    {S' : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} T')} (hS : (godementTot S).ShortExact)
    (hS' : (godementTot S').ShortExact)
    (c₁ : ∀ q : ℤ, (sheafCohomology T q).obj S.X₁ ⟶ (sheafCohomology T' q).obj S'.X₁)
    (c₂ : ∀ q : ℤ, (sheafCohomology T q).obj S.X₂ ⟶ (sheafCohomology T' q).obj S'.X₂)
    (c₃ : ∀ q : ℤ, (sheafCohomology T q).obj S.X₃ ⟶ (sheafCohomology T' q).obj S'.X₃)
    (nf : ∀ q : ℤ, c₁ q ≫ (sheafCohomology T' q).map S'.f = (sheafCohomology T q).map S.f ≫ c₂ q)
    (ng : ∀ q : ℤ, c₂ q ≫ (sheafCohomology T' q).map S'.g = (sheafCohomology T q).map S.g ≫ c₃ q)
    (nδ : ∀ q : ℤ, hS.δ q (q + 1) rfl ≫ c₁ (q + 1) = c₃ q ≫ hS'.δ q (q + 1) rfl)
    (h₁ : ∀ q, IsIso (c₁ q)) (h₃ : ∀ q, IsIso (c₃ q)) (p q : ℤ) (hp : p + 1 = q) :
    IsIso (c₂ q) :=
  isIso_of_five (sheafCohomologyδ hS p q hp) ((sheafCohomology T q).map S.f)
    ((sheafCohomology T q).map S.g) (sheafCohomologyδ hS q (q + 1) rfl)
    (sheafCohomologyδ hS' p q hp) ((sheafCohomology T' q).map S'.f)
    ((sheafCohomology T' q).map S'.g) (sheafCohomologyδ hS' q (q + 1) rfl)
    (c₃ p) (c₁ q) (c₂ q) (c₃ q) (c₁ (q + 1))
    (by subst hp; exact nδ p) (nf q).symm (ng q).symm
    (nδ q)
    (δ_comp_sheafCohomology_map S hS p q hp) (sheafCohomology_map_comp_map S q)
    (sheafCohomology_map_comp_δ S hS q (q + 1) rfl) (δ_comp_sheafCohomology_map S' hS' p q hp)
    (sheafCohomology_map_comp_map S' q) (sheafCohomology_map_comp_δ S' hS' q (q + 1) rfl)
    (sheafCohomology_exact₁ S hS p q hp) (sheafCohomology_exact₂ S hS q)
    (sheafCohomology_exact₃ S hS q (q + 1) rfl) (sheafCohomology_exact₁ S' hS' p q hp)
    (sheafCohomology_exact₂ S' hS' q) (sheafCohomology_exact₃ S' hS' q (q + 1) rfl)
    (h₃ p) (h₁ q) (h₃ q) (h₁ (q + 1))

section

variable {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))

/-- The comparison maps `c^q_F` are isomorphisms in every degree. -/
private def Good (F : X.Modules) : Prop := ∀ q : ℤ, IsIso (comparisonMap sX F q)

/-- `ι_F` is natural in `F`. -/
private lemma analytifyModuleι_naturality {F G : X.Modules} (f : F ⟶ G) :
    analytifyModuleι sX F ≫ (SheafOfModules.toSheaf _).map ((analytifyModule sX).map f) =
      (TopCat.Sheaf.pullback AddCommGrpCat.{0} (toSchemeHom sX)).map
        ((SheafOfModules.toSheaf _).map f) ≫ analytifyModuleι sX G := by
  simp only [analytifyModuleι]
  erw [← Adjunction.homEquiv_naturality_right_symm, ← Adjunction.homEquiv_naturality_left_symm]
  congr 1
  change (SheafOfModules.toSheaf _).map (analytifyModuleUnit sX F ≫
      (SheafOfModules.pushforward.{0} (ringCatSheafHom sX)).map ((analytifyModule sX).map f)) =
    (SheafOfModules.toSheaf _).map (f ≫ analytifyModuleUnit sX G)
  congr 1
  exact ((SheafOfModules.pullbackPushforwardAdjunction.{0} (ringCatSheafHom sX)).unit.naturality
    f).symm

/-- A zero module is `Good`. -/
private lemma good_of_isZero {F : X.Modules} (hF : IsZero F) : Good sX F := by
  haveI : (SheafOfModules.toSheaf X.ringCatSheaf).PreservesZeroMorphisms :=
    @Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
      (SheafOfModules.instAdditiveSheafAddCommGrpCatToSheaf X.ringCatSheaf)
  haveI : (SheafOfModules.toSheaf (ringCatSheaf sX)).PreservesZeroMorphisms :=
    @Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
      (SheafOfModules.instAdditiveSheafAddCommGrpCatToSheaf (ringCatSheaf sX))
  haveI : (analytifyModule sX).IsLeftAdjoint :=
    (SheafOfModules.pullbackPushforwardAdjunction.{0} (ringCatSheafHom sX)).isLeftAdjoint
  intro q
  have h₁ : IsZero ((sheafCohomology _ q).obj ((SheafOfModules.toSheaf _).obj F)) :=
    (sheafCohomology _ q).map_isZero ((SheafOfModules.toSheaf X.ringCatSheaf).map_isZero hF)
  have h₂ : IsZero ((sheafCohomology (space sX) q).obj
      ((SheafOfModules.toSheaf _).obj ((analytifyModule sX).obj F))) :=
    (sheafCohomology (space sX) q).map_isZero
      ((SheafOfModules.toSheaf (ringCatSheaf sX)).map_isZero ((analytifyModule sX).map_isZero hF))
  exact ⟨⟨0, h₁.eq_of_src _ _, h₂.eq_of_src _ _⟩⟩

variable [LocallyOfFiniteType sX] [QuasiCompact sX]

/-- `Good` is invariant under isomorphism. -/
private lemma good_of_iso {F G : X.Modules} (e : F ≅ G) (hF : Good sX F) : Good sX G := by
  obtain ⟨-, -, -, -, -, -, -, -, hNat, -⟩ := analytification_stalks sX
  intro q
  have hn := hNat F G ((SheafOfModules.toSheaf _).map e.hom)
    ((SheafOfModules.toSheaf _).map ((analytifyModule sX).map e.hom))
    (analytifyModuleι_naturality sX e.hom) q
  haveI := hF q
  haveI : IsIso ((sheafCohomology _ q).map ((SheafOfModules.toSheaf _).map e.hom)) :=
    ((sheafCohomology _ q).mapIso ((SheafOfModules.toSheaf _).mapIso e)).isIso_hom
  haveI : IsIso ((sheafCohomology (space sX) q).map
      ((SheafOfModules.toSheaf _).map ((analytifyModule sX).map e.hom))) :=
    ((sheafCohomology (space sX) q).mapIso
      ((SheafOfModules.toSheaf _).mapIso ((analytifyModule sX).mapIso e))).isIso_hom
  exact IsIso.of_isIso_fac_left hn.symm

/-- Two-out-of-three for `Good` along a short exact sequence: from the sub and the middle to
the quotient, and from the sub and the quotient to the middle. -/
private lemma good_of_shortExact (S : ShortComplex X.Modules) (hS : S.ShortExact) :
    (Good sX S.X₁ → Good sX S.X₂ → Good sX S.X₃) ∧
      (Good sX S.X₁ → Good sX S.X₃ → Good sX S.X₂) := by
  obtain ⟨-, -, -, -, -, -, -, -, hNat, ⟨hLES, -⟩, -⟩ := analytification_stalks sX
  obtain ⟨h₁, h₂, hδS⟩ := hLES S hS
  have nf := hNat S.X₁ S.X₂ ((SheafOfModules.toSheaf _).map S.f)
    ((SheafOfModules.toSheaf _).map ((analytifyModule sX).map S.f))
    (analytifyModuleι_naturality sX S.f)
  have ng := hNat S.X₂ S.X₃ ((SheafOfModules.toSheaf _).map S.g)
    ((SheafOfModules.toSheaf _).map ((analytifyModule sX).map S.g))
    (analytifyModuleι_naturality sX S.g)
  exact ⟨fun g₁ g₂ => isIso_of_les_right h₁ h₂ (comparisonMap sX S.X₁) (comparisonMap sX S.X₂)
      (comparisonMap sX S.X₃) nf ng hδS g₁ g₂,
    fun g₁ g₃ q => isIso_of_les_mid h₁ h₂ (comparisonMap sX S.X₁) (comparisonMap sX S.X₂)
      (comparisonMap sX S.X₃) nf ng hδS g₁ g₃ (q - 1) q (Int.sub_add_cancel q 1)⟩

end

attribute [local instance] MvPolynomial.gradedAlgebra
  Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff

/-- The twisting sheaf `𝒪(k)` of `ℙᴺ_ℂ = Proj (polyGrading ℂ N)`. -/
local notation3 (prettyPrint := false) "𝒪ℙ[" N ", " k "]" =>
  (show (AlgebraicGeometry.Proj (polyGrading ℂ N)).Modules from
    ProjectiveSpectrum.Proj.twistingSheaf (polyGrading ℂ N) k)

/-- Twisting sheaves on `ℙᴺ_ℂ`, `N ≥ 1`, satisfy GAGA. -/
private lemma good_twistingSheaf (N : ℕ) (hN : 1 ≤ N) (k : ℤ) :
    Good (projToSpecCoeff ℂ N) 𝒪ℙ[N, k] := by
  intro q
  rcases lt_or_ge q 0 with hq | hq
  · exact ⟨⟨0, (isZero_sheafCohomology_of_neg hq).eq_of_src _ _,
      (isZero_sheafCohomology_of_neg hq).eq_of_src _ _⟩⟩
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hq
    exact (isIso_comparisonMap_projectiveSpace_twistingSheaf N hN k).1 n

/-- Finite sums of twisting sheaves on `ℙᴺ_ℂ`, `N ≥ 1`, satisfy GAGA. -/
private lemma good_sigma_twistingSheaf (N : ℕ) (hN : 1 ≤ N) (p : ℕ) (d : Fin p → ℤ) :
    Good (projToSpecCoeff ℂ N) (∐ fun i => 𝒪ℙ[N, d i]) := by
  induction p with
  | zero =>
    apply good_of_isZero
    rw [IsZero.iff_id_eq_zero]
    exact Sigma.hom_ext _ _ (fun i => Fin.elim0 i)
  | succ p ih =>
    let f := fun i : Fin (p + 1) => 𝒪ℙ[N, d i]
    let e : (∐ f) ≅ f 0 ⊞ ∐ (fun i : Fin p => f i.succ) :=
      (colimit.isColimit _).coconePointUniqueUpToIso
        (extendCofanIsColimit f (colimit.isColimit (Discrete.functor fun i : Fin p => f i.succ))
          (coprodIsCoprod (f 0) (∐ fun i : Fin p => f i.succ))) ≪≫ (biprod.isoCoprod _ _).symm
    exact good_of_iso _ e.symm ((good_of_shortExact _ _
      (ShortComplex.Splitting.ofHasBinaryBiproduct _ _).shortExact).2
      (good_twistingSheaf N hN (d 0)) (ih fun i => d i.succ))

/-- Coherent sheaves on `ℙᴺ_ℂ`, `N ≥ 1`, satisfy GAGA. -/
private lemma good_of_isCoherent_projectiveSpace (N : ℕ) (hN : 1 ≤ N)
    (G : (AlgebraicGeometry.Proj (polyGrading ℂ N)).Modules)
    (hG : Stacks.SheafOfModules.IsCoherent G) : Good (projToSpecCoeff ℂ N) G := by
  obtain ⟨E, ε, hε, hac, hzero, hsum⟩ := exists_twistingSheaf_resolution_projectiveSpace N G hG
  let K := E.augment ε hε
  have hK : ∀ j, Good (projToSpecCoeff ℂ N) (K.X (j + 1)) := fun j => by
    obtain ⟨p, d, ⟨e⟩⟩ := hsum j
    exact good_of_iso _ e.symm (good_sigma_twistingSheaf N hN p d)
  have key : ∀ k j, j + k = N + 3 →
      Good (projToSpecCoeff ℂ N) (K.cycles j) := by
    intro k
    induction k with
    | zero =>
      intro j hj
      apply good_of_isZero
      obtain rfl : j = N + 2 + 1 := by omega
      exact IsZero.of_mono (K.iCycles _) (hzero (N + 2) (by omega))
    | succ k ih =>
      intro j hj
      exact (good_of_shortExact _ _ (shortExact_cycles K (j + 1) j rfl (hac j))).1
        (ih (j + 1) (by omega)) (hK j)
  exact good_of_iso _ (@asIso _ _ _ _ (K.iCycles 0)
    (K.isIso_iCycles 0 0 (by simp) (K.shape _ _ (by simp)))) (key (N + 3) 0 (by omega))

/-- A projective `ℂ`-scheme embeds as a closed subscheme of some `ℙᴺ_ℂ` with `N ≥ 1`. -/
private lemma exists_isClosedImmersion_projectiveSpace {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) (hX : IsProjective sX) :
    ∃ (N : ℕ) (i : X ⟶ AlgebraicGeometry.Proj (polyGrading ℂ N)), 1 ≤ N ∧ IsClosedImmersion i ∧
      i ≫ projToSpecCoeff ℂ N = sX := by
  obtain ⟨n, j, hj, hjs⟩ := isProjectiveMorphism_of_isProjective_of_isAffine sX hX
  let L := Stacks.AmpleProjectiveImmersion.linearEmbeddingOver (Spec (.of ℂ)) (Nat.le_succ n)
  have hL : IsClosedImmersion L :=
    MorphismProperty.pullbackMap (P := @IsClosedImmersion) inferInstance
      (Stacks.AmpleProjectiveImmersion.isClosedImmersion_linearEmbeddingAtUniverse
        (Nat.le_succ n)) (Category.id_comp _).symm (by simp)
  let e := Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison ℂ (n + 1)
  refine ⟨n + 1, j ≫ L ≫ e.iso.hom, by omega, ?_, ?_⟩
  · haveI := hj
    infer_instance
  · rw [Category.assoc, Category.assoc, projToSpecCoeff, e.toBase]
    erw [Stacks.AmpleProjectiveImmersion.linearEmbeddingOver_comp_fst]
    exact hjs

/-- **Serre's GAGA comparison theorem.** For a projective scheme `X` over `ℂ` (possibly
nonreduced) and a coherent `𝒪_X`-module `F`, the comparison map
`c^q_F : H^q(X, F) → H^q(X^an, F^an)` is an isomorphism for every `q`. -/
@[mmp "thm_mmp_gaga_projective_cohomology"]
public theorem isIso_comparisonMap_of_isProjective {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    (hX : IsProjective sX) (F : X.Modules) (hF : Stacks.SheafOfModules.IsCoherent F) (q : ℤ) :
    IsIso (comparisonMap sX F q) := by
  obtain ⟨N, i, hN, hi, his⟩ := exists_isClosedImmersion_projectiveSpace sX hX
  haveI := hi
  haveI : LocallyOfFiniteType sX := his ▸ inferInstance
  haveI : QuasiCompact sX := his ▸ inferInstance
  haveI : IsLocallyNoetherian (AlgebraicGeometry.Proj (polyGrading ℂ N)) :=
    LocallyOfFiniteType.isLocallyNoetherian (projToSpecCoeff ℂ N)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h5⟩ := analytification_stalks sX
  obtain ⟨-, -, _, -, hcomp⟩ := h5 (projToSpecCoeff ℂ N) i his
  obtain ⟨_, -, hq⟩ := hcomp F
  haveI := good_of_isCoherent_projectiveSpace N hN _
    (by
      haveI : F.IsCoherent := (Stacks.AlgebraicGeometry.ProperMapping.isCoherent_iff F).mpr hF
      exact (Stacks.AlgebraicGeometry.ProperMapping.isCoherent_iff _).mp
        (AlgebraicGeometry.isCoherent_pushforward_of_isClosedImmersion i F)) q
  obtain ⟨_, _, hC⟩ := hq q
  exact IsIso.of_isIso_fac_left hC.symm

end MMP.Analytic

end
