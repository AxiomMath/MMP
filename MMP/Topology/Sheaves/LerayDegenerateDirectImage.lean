module
public import MMP.Topology.Sheaves.LeraySpectralSequence
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedFunctorAdditive
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.CohomologyAtTheTerminalObject
public import StacksFrontier.Cotangent.CohomologyPresheaf.SiteSectionsComparison

/-!
# Cohomology of a sheaf with vanishing higher direct images

Let `f : Y → X` be a continuous map and `F` an abelian sheaf on `Y` whose higher direct
images `Rʲ f_* F` vanish for all `j > 0`. Then the Leray spectral sequence degenerates and
`Hⁱ(Y, F) ≅ Hⁱ(X, f_* F)` for every `i ≥ 0`.

## Main results

* `MMP.nonempty_addEquiv_H_pushforward_of_isZero_rightDerived`: under the vanishing
  of the higher direct images, `Hⁱ(Y, F)` and `Hⁱ(X, f_* F)` are isomorphic groups.

## Implementation notes

The statement is made for a continuous map of topological spaces; a morphism of schemes
`f : Y ⟶ X` is the special case of its underlying continuous map `f.base`. Sheaves are
taken in `Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat`, the category on which
`CategoryTheory.Sheaf.H` is defined, and the direct image is
`Functor.sheafPushforwardContinuous` along `Opens.map f`. The higher direct images are the
right derived functors `Functor.rightDerived` of that direct image, which requires it to be
additive; that instance is assumed, as is the existence of `Ext` groups in the universe `w`.

## References

* [R. Lazarsfeld, *Positivity in Algebraic Geometry I*][lazarsfeld2004]
-/

@[expose] public section

universe w v u

open CategoryTheory TopologicalSpace Limits
open Stacks.Cohomology.Leray Stacks.Cohomology.LerayLowDegree

namespace MMP

/-- Changing the universe of an `Ext` group is additive. -/
private theorem ext_chgUniv_add {C : Type*} [Category* C] [Abelian C] [HasExt.{w} C]
    [HasExt.{v} C] {A B : C} {n : ℕ} (x y : Abelian.Ext.{w} A B n) :
    Abelian.Ext.chgUniv.{v} (x + y) =
      Abelian.Ext.chgUniv.{v} x + Abelian.Ext.chgUniv.{v} y := by
  let := HasDerivedCategory.standard C
  ext
  simp only [Abelian.Ext.homEquiv_chgUniv, Abelian.Ext.add_hom]

/-- Global sheaf cohomology `Sheaf.H` agrees with the right derived functors of global
sections. -/
private theorem nonempty_addEquiv_H_abelianCohomology (Z : TopCat.{u})
    [HasExt.{w} (Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u})]
    (G : Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}) (n : ℕ) :
    Nonempty (Sheaf.H.{w} G n ≃+ (abelianCohomology.{u, u} Z ⊤ n).obj G) := by
  let : HasExt.{u} (Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}) :=
    hasExt_of_enoughInjectives _
  let e₁ : Sheaf.H.{w} G n ≃+ Sheaf.H.{u} G n :=
    { Abelian.Ext.chgUniv.{u} with map_add' := ext_chgUniv_add }
  let e₂ := (Stacks.Cohomology.TerminalCohomology.h'IsoH.{u} _ G n ⊤
      Stacks.Cohomology.TerminalCohomology.topIsTerminal).symm ≪≫
    Stacks.Cohomology.SiteSections.cohomologyIsoRightDerivedSections _ G n ⊤
  exact ⟨e₁.trans e₂.addCommGroupIsoToAddEquiv⟩

section SpectralSequence

variable {C : Type*} [Category* C] [Abelian C] (E : E₂CohomologicalSpectralSequenceNat C)

/-- A position which is zero on the second page is zero on every later page. -/
private theorem isZero_page_of_isZero_two (pq : ℕ × ℕ) (h₂ : IsZero ((E.page 2).X pq))
    (r : ℤ) (hr : 2 ≤ r) : IsZero ((E.page r hr).X pq) := by
  induction r, hr using Int.leInduction with
  | base => exact h₂
  | succ r hr ih =>
    exact (ShortComplex.isZero_homology_of_isZero_X₂ _ ih).of_iso (E.iso r (r + 1) pq).symm

/-- A position which is zero on the second page is zero on the infinity page. -/
private theorem isZero_pageInfinity_of_isZero_two (pq : ℕ × ℕ) [E.HasPageInfinityAt pq]
    (h₂ : IsZero ((E.page 2).X pq)) : IsZero (E.pageInfinity pq) :=
  (isZero_page_of_isZero_two E pq h₂ _ (E.LE_rMin pq)).of_iso (E.pageInfinityIso' pq)

variable {E}

/-- If the second page vanishes off the bottom row, no differential reaches the bottom row
from page two on. -/
private theorem hasEdgeMonoAtFrom_of_isZero (hE : ∀ p q, q ≠ 0 → IsZero ((E.page 2).X (p, q)))
    (n : ℕ) [E.HasPageInfinityAt (n, 0)] : E.HasEdgeMonoAtFrom (n, 0) 2 := by
  refine SpectralSequence.HasEdgeMonoAtFrom.mk' _ _ _ fun k => ⟨by lia, fun pq' => ?_⟩
  by_cases hq : pq'.2 = 0
  · apply HomologicalComplex.shape
    simp only [ComplexShape.spectralSequenceNat_rel_iff, not_and]
    intro _; lia
  · exact (isZero_page_of_isZero_two E pq' (hE pq'.1 pq'.2 hq) _ _).eq_of_src _ _

/-- If the second page vanishes off the bottom row, no differential leaves the bottom row
from page two on. -/
private theorem hasEdgeEpiAtFrom_of_isZero (hE : ∀ p q, q ≠ 0 → IsZero ((E.page 2).X (p, q)))
    (n : ℕ) [E.HasPageInfinityAt (n, 0)] : E.HasEdgeEpiAtFrom (n, 0) 2 := by
  refine SpectralSequence.HasEdgeEpiAtFrom.mk' _ _ _ fun k => ⟨by lia, fun pq' => ?_⟩
  by_cases hq : pq'.2 = 0
  · apply HomologicalComplex.shape
    simp only [ComplexShape.spectralSequenceNat_rel_iff, not_and]
    intro _; lia
  · exact (isZero_page_of_isZero_two E pq' (hE pq'.1 pq'.2 hq) _ _).eq_of_tgt _ _

variable {H : ℕ → C} (D : FirstQuadrantAbutment E H)

/-- The filtration steps below the bottom row are isomorphisms when the infinity page vanishes
off the bottom row. -/
private theorem isIso_ι (hE : ∀ p q, q ≠ 0 → IsZero (E.pageInfinity (p, q))) (n k : ℕ)
    (hk : k < n) : IsIso (D.ι n k) := by
  obtain ⟨q, rfl⟩ : ∃ q, n = k + q := ⟨n - k, by lia⟩
  have := D.mono_ι (k + q) k
  have : Epi (D.ι (k + q) k) :=
    Preadditive.epi_of_isZero_cokernel _ ((hE k q (by lia)).of_iso (D.gradedIso k q).symm)
  exact isIso_of_mono_of_epi _

/-- When the infinity page vanishes off the bottom row, every filtration step `FᵏHⁿ` with
`k ≤ n` is the whole of `F⁰Hⁿ`. -/
private theorem nonempty_iso_obj (hE : ∀ p q, q ≠ 0 → IsZero (E.pageInfinity (p, q)))
    (n : ℕ) : ∀ k ≤ n, Nonempty (D.obj n k ≅ D.obj n 0)
  | 0, _ => ⟨Iso.refl _⟩
  | k + 1, hk =>
    have := isIso_ι D hE n k (by lia)
    ⟨asIso (D.ι n k) ≪≫ (nonempty_iso_obj hE n k (by lia)).some⟩

include D in
/-- A first-quadrant spectral sequence whose second page vanishes off the bottom row
collapses: its abutment is the bottom row of the second page, `Hⁿ ≅ E₂^{n,0}`. -/
private theorem nonempty_iso_page_two_of_isZero
    (hE : ∀ p q, q ≠ 0 → IsZero ((E.page 2).X (p, q))) (n : ℕ) :
    Nonempty (H n ≅ (E.page 2).X (n, 0)) :=
  have := hasEdgeMonoAtFrom_of_isZero hE n
  have := hasEdgeEpiAtFrom_of_isZero hE n
  ⟨(D.topIso n).symm ≪≫ (nonempty_iso_obj D (fun p q hq =>
      isZero_pageInfinity_of_isZero_two E (p, q) (hE p q hq)) n n le_rfl).some.symm ≪≫
    (D.topGradedIso n).symm ≪≫ E.pageInfinityIso (n, 0) 2⟩

end SpectralSequence

/-- If the higher direct images `Rʲ f_* F` of an abelian sheaf `F` on `Y` along a continuous
map `f : Y ⟶ X` vanish for all `j > 0`, then `Hⁱ(Y, F) ≃+ Hⁱ(X, f_* F)` for every `i`. -/
@[mmp "prop_pab_cohomology_direct_image_higher_vanishing"]
public theorem nonempty_addEquiv_H_pushforward_of_isZero_rightDerived
    {X Y : TopCat.{u}} (f : Y ⟶ X) (F : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})
    [HasExt.{w} (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})]
    [HasExt.{w} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    [((Opens.map f).sheafPushforwardContinuous AddCommGrpCat.{u}
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).Additive]
    (h : ∀ j > 0, IsZero ((((Opens.map f).sheafPushforwardContinuous AddCommGrpCat.{u}
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).rightDerived j).obj F))
    (i : ℕ) :
    Nonempty (Sheaf.H.{w} F i ≃+
      Sheaf.H.{w} (((Opens.map f).sheafPushforwardContinuous AddCommGrpCat.{u}
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).obj F) i) := by
  obtain ⟨E, D, e, -⟩ := exists_leraySpectralSequence_bottomRowEdge_eq_abelianEdgeMap f F
  obtain ⟨φ⟩ := nonempty_iso_page_two_of_isZero D (fun p q hq =>
    ((abelianCohomology.{u, u} X ⊤ p).map_isZero (h q (by lia))).of_iso (e p q)) i
  let ψ := φ ≪≫ e i 0 ≪≫ (abelianCohomology.{u, u} X ⊤ i).mapIso
    ((abelianPushforward.{u, u} f).rightDerivedZeroIsoSelf.app F)
  obtain ⟨bY⟩ := nonempty_addEquiv_H_abelianCohomology.{w} Y F i
  obtain ⟨bX⟩ := nonempty_addEquiv_H_abelianCohomology.{w} X
    ((abelianPushforward.{u, u} f).obj F) i
  exact ⟨bY.trans (ψ.addCommGroupIsoToAddEquiv.trans bX.symm)⟩

end MMP
