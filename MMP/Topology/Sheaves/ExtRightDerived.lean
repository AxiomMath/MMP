module

public import MMP.Topology.Sheaves.Godement
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver

/-!
# `Ext`-cohomology and right derived functors of global sections

For a sheaf of abelian groups `F` on a topological space `X`, Mathlib's `Sheaf.H' F n ⊤` is the
group `Ext^n(ℤ_⊤, F)`, where `ℤ_⊤` is the sheafified free abelian presheaf on `yoneda ⊤`. Since
morphisms `ℤ_⊤ ⟶ G` are the global sections of `G`, naturally in `G`, an injective resolution
`F → I^•` computes both: `Ext^n(ℤ_⊤, F) = H^n(Hom(ℤ_⊤, I^•)) = H^n(Γ(X, I^•))`, and the latter is
`R^n Γ(X, F)`. We record the consequence we need: if `H'^{q+1}(X, F)` vanishes, so does
`R^{q+1}Γ(X, -)` at `F`.

## Main definitions

* `MMP.Analytic.freeYonedaTop`: the free abelian sheaf `ℤ_⊤` on the representable presheaf
  `yoneda ⊤`.
* `MMP.Analytic.freeYonedaTopHomEquiv`: morphisms from the free abelian sheaf on `yoneda ⊤` to
  `G` are the global sections of `G`.

## Main results

* `MMP.Analytic.subsingleton_ext_of_sum_comp_eq_id`: `Ext^n(P, -)` vanishes on retracts of finite
  sums of an object on which it vanishes.
* `MMP.Analytic.isZero_rightDerived_globalSections_of_subsingleton_H'`: vanishing of
  `H'^{q+1}(X, F)` implies vanishing of `(R^{q+1} Γ(X, -))(F)`.
-/

@[expose] public section

universe w

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace MMP.Analytic

variable {X : TopCat.{0}}

/-- The free abelian sheaf on the representable presheaf of the whole space. -/
noncomputable abbrev freeYonedaTop (X : TopCat.{0}) :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0} :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
    (yoneda.obj (⊤ : Opens X) ⋙ AddCommGrpCat.free)

/-- Morphisms from the free abelian sheaf on `yoneda ⊤` to `G` are the global sections of `G`. -/
noncomputable def freeYonedaTopHomEquiv
    (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) :
    (freeYonedaTop X ⟶ G) ≃ G.obj.obj (op ⊤) :=
  ((sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{0}).homEquiv _ G).trans
    ((((AddCommGrpCat.adj.whiskerRight (C := (Opens X)ᵒᵖ))).homEquiv
      (yoneda.obj (⊤ : Opens X)) G.obj).trans yonedaEquiv)

/-- The equivalence `freeYonedaTopHomEquiv` is natural in the target sheaf: composing with
`h : G ⟶ G'` corresponds to applying `h` to global sections. -/
lemma freeYonedaTopHomEquiv_comp {G G' : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}}
    (f : freeYonedaTop X ⟶ G) (h : G ⟶ G') :
    freeYonedaTopHomEquiv G' (f ≫ h) = h.hom.app (op ⊤) (freeYonedaTopHomEquiv G f) := by
  simp only [freeYonedaTopHomEquiv, Equiv.trans_apply]
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right,
    yonedaEquiv_comp]
  rfl

/-- The zero morphism corresponds under `freeYonedaTopHomEquiv` to the zero global section. -/
lemma freeYonedaTopHomEquiv_zero (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) :
    freeYonedaTopHomEquiv G 0 = 0 := by
  have h := freeYonedaTopHomEquiv_comp ((freeYonedaTopHomEquiv G).symm 0) (0 : G ⟶ G)
  rw [Limits.comp_zero] at h
  rw [h]
  rfl

/-- `Ext^n(P, -)` vanishes on a retract `A` of a finite sum of copies of `B` once it vanishes
on `B`. -/
theorem subsingleton_ext_of_sum_comp_eq_id {C : Type*} [Category C] [Abelian C]
    [HasExt.{w} C] {P A B : C} {ι : Type*} (s : Finset ι) (π : ι → (A ⟶ B)) (i : ι → (B ⟶ A))
    (h : ∑ k ∈ s, π k ≫ i k = 𝟙 A) (n : ℕ) (hY : Subsingleton (Abelian.Ext P B n)) :
    Subsingleton (Abelian.Ext P A n) := by
  refine subsingleton_of_forall_eq 0 fun x => ?_
  have hsum : ∀ t : Finset ι, x.comp (Abelian.Ext.mk₀ (∑ k ∈ t, π k ≫ i k)) (add_zero n) = 0 := by
    intro t
    classical
    induction t using Finset.induction_on with
    | empty => simp [Abelian.Ext.mk₀_zero]
    | insert a t ha ih =>
      rw [Finset.sum_insert ha, Abelian.Ext.mk₀_add, Abelian.Ext.comp_add, ih, add_zero,
        ← Abelian.Ext.mk₀_comp_mk₀, ← Abelian.Ext.comp_assoc _ _ _ (add_zero n) (zero_add 0)
          (by simp), Subsingleton.elim (x.comp (Abelian.Ext.mk₀ (π a)) (add_zero n)) 0,
        Abelian.Ext.zero_comp]
  rw [← Abelian.Ext.comp_mk₀_id x, ← h]
  exact hsum s

/-- **`Ext` vanishing implies derived-functor vanishing.** If the `Ext`-cohomology
`H'^{q+1}(X, F) = Ext^{q+1}(ℤ_⊤, F)` vanishes, then so does `(R^{q+1}Γ(X, -))(F)`. -/
theorem isZero_rightDerived_globalSections_of_subsingleton_H'
    [HasExt.{w} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0})]
    [(globalSections X).Additive]
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (q : ℕ)
    (h : Subsingleton (Sheaf.H' F (q + 1) (⊤ : Opens X))) :
    IsZero (((globalSections X).rightDerived (q + 1)).obj F) := by
  have : HasExt.{w} (TopCat.Sheaf AddCommGrpCat.{0} X) := ‹_›
  let R : InjectiveResolution F := injectiveResolution F
  refine IsZero.of_iso ?_ (R.isoRightDerivedObj (globalSections X) (q + 1))
  change IsZero ((((globalSections X).mapHomologicalComplex _).obj R.cocomplex).homology (q + 1))
  rw [← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ q (q + 1) (q + 2) (by simp) (by simp),
    ShortComplex.ab_exact_iff]
  intro x hx
  let P : TopCat.Sheaf AddCommGrpCat.{0} X := freeYonedaTop X
  let e : ∀ G : TopCat.Sheaf AddCommGrpCat.{0} X, (P ⟶ G) ≃ G.obj.obj (op ⊤) :=
    fun G => freeYonedaTopHomEquiv (X := X) G
  have he : ∀ {G G' : TopCat.Sheaf AddCommGrpCat.{0} X} (f : P ⟶ G) (k : G ⟶ G'),
      e G' (f ≫ k) = k.hom.app (op ⊤) (e G f) := fun f k => freeYonedaTopHomEquiv_comp f k
  have he0 : ∀ G : TopCat.Sheaf AddCommGrpCat.{0} X, e G 0 = 0 := fun G =>
    freeYonedaTopHomEquiv_zero G
  let f : P ⟶ R.cocomplex.X (q + 1) := (e _).symm x
  have hfx : e _ f = x := (e _).apply_symm_apply x
  have hf : f ≫ R.cocomplex.d (q + 1) (q + 2) = 0 := by
    apply (e _).injective
    rw [he, he0, hfx]
    exact hx
  have h0 : R.extMk f (q + 2) rfl hf = 0 := @Subsingleton.elim _ h _ _
  obtain ⟨g, hg⟩ := (R.extMk_eq_zero_iff f (q + 2) rfl hf q rfl).1 h0
  refine ⟨e _ g, ?_⟩
  have := he g (R.cocomplex.d q (q + 1))
  rw [hg, hfx] at this
  exact this.symm

end MMP.Analytic
