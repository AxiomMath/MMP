module
public import MMP.Attr
public import StacksFrontier.AlgebraicGeometry.AffineMorphismCohomology.ResolutionDesc
public import StacksFrontier.Topology.Sheaves.Cohomology.CechSpectralSequence.DoubleComplexAsAFilteredComplex
public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.RestrictionUnivLE
public import StacksFrontier.Topology.Sheaves.Cohomology.Leray.FunctorialFilteredAbutment
public import StacksFrontier.Topology.Sheaves.Cohomology.Torsors.FirstCohomologyClassification.TorsorClasses

/-!
# The Leray spectral sequence of a continuous map, with its bottom-row edge

Let `f : Y ⟶ X` be a continuous map of topological spaces and `F` a sheaf of abelian groups
on `Y`. There is a first-quadrant cohomological spectral sequence
```
E₂^{p,q} = Hᵖ(X, R^q f_* F) ⟹ H^{p+q}(Y, F),
```
converging through a finite decreasing filtration of each `Hⁿ(Y, F)`. Its bottom-row edge map
`E₂^{p,0} = Hᵖ(X, f_* F) ⟶ Hᵖ(Y, F)` is the canonical comparison map of cohomology.

## Main results

* `MMP.exists_leraySpectralSequence_bottomRowEdge_eq_abelianEdgeMap`: the Leray spectral
  sequence with its second page, its abutment, and the identification of its bottom-row
  edge map with `Stacks.Cohomology.LerayLowDegree.abelianEdgeMap`.

## Implementation notes

The spectral sequence is an `E₂CohomologicalSpectralSequenceNat`, indexed by `ℕ × ℕ`, so it is
first-quadrant by construction; convergence is the datum
`Stacks.Cohomology.Leray.FirstQuadrantAbutment`, a finite decreasing filtration
`Hⁿ ≅ F⁰Hⁿ ⊇ F¹Hⁿ ⊇ ⋯ ⊇ Fⁿ⁺¹Hⁿ = 0` whose graded pieces are the terms of the infinity page.

The bottom-row edge map in degree `p` is the composite of the edge epimorphism
`E₂^{p,0} ⟶ E_∞^{p,0}`, the identification `E_∞^{p,0} ≅ FᵖHᵖ` (the step `F^{p+1}Hᵖ` being
zero, `FirstQuadrantAbutment.topGradedIso`), and the inclusion `FᵖHᵖ ⊆ F⁰Hᵖ ≅ Hᵖ`, the
composite of the filtration steps written with `CategoryTheory.Functor.ofOpSequence`.
The second page is identified with `Hᵖ(X, R^q f_* F)`; on the bottom row `R⁰ f_* F` is
identified with `f_* F` by
`CategoryTheory.Functor.rightDerivedZeroIsoSelf`, the direct image being left exact.

The comparison map `Hᵖ(X, f_* F) ⟶ Hᵖ(Y, F)` is
`Stacks.Cohomology.LerayLowDegree.abelianEdgeMap`, the edge morphism of the composite
`Γ(Y, -) = Γ(X, -) ∘ f_*` of right derived functors: it is induced on cohomology of global
sections by any comparison `J ⟶ f_* I` of an injective resolution `J` of `f_* F` with the direct
image of an injective resolution `I` of `F` (`abelianEdgeMap_eq`). This is the map induced by the
counit `f⁻¹ f_* F ⟶ F`: `f⁻¹` is exact, so `f⁻¹ J` resolves `f⁻¹ f_* F`, and the adjoint of the
comparison `J ⟶ f_* I` is a comparison `f⁻¹ J ⟶ I` over that counit.

Sheaves and their cohomology are taken in the universe of the spaces.

## References

* [Stacks Project, Tag 01F2](https://stacks.math.columbia.edu/tag/01F2)
* [Stacks Project, Tag 015N](https://stacks.math.columbia.edu/tag/015N)
-/

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Cohomology.Leray Stacks.Cohomology.LerayLowDegree

namespace MMP

section Abutment

variable {C : Type*} [Category C] [Abelian C]

omit [Abelian C] in
private lemma ofOpSequence_comp_ι {X : C} (F : Filtration X ℤᵒᵖ) (p : ℕ) :
    (Functor.ofOpSequence (X := fun k : ℕ => F.obj (op (k : ℤ)))
      (fun k => F.step (FilteredObject.succHom (k : ℤ)))).map (homOfLE (Nat.zero_le p)).op ≫
      F.ι.app (op ((0 : ℕ) : ℤ)) = F.ι.app (op (p : ℤ)) := by
  induction p with
  | zero =>
    have : (homOfLE (Nat.zero_le 0)).op = 𝟙 (op 0) := rfl
    rw [this]
    exact (congrArg (· ≫ _) (CategoryTheory.Functor.map_id _ _)).trans (Category.id_comp _)
  | succ p ih =>
    have : (homOfLE (Nat.zero_le (p + 1))).op =
        (homOfLE (Nat.le_succ p)).op ≫ (homOfLE (Nat.zero_le p)).op := rfl
    rw [this, Functor.map_comp, Functor.ofOpSequence_map_homOfLE_succ]
    exact (Category.assoc _ _ _).trans ((congrArg _ ih).trans (F.step_comp_ι_app _))

variable {D : Type*} [Category D]
  {E : D ⥤ E₂CohomologicalSpectralSequenceNat C} {H : ℕ → D ⥤ C}
  (h : FunctorialFirstQuadrantAbutsTo E H)

private noncomputable def edgeComp (K : D) (p : ℕ) :
    ((E.obj K).page 2).X (p, 0) ⟶ (H p).obj K :=
  (E.obj K).edgeEpi (p, 0) 2 ≫ ((h.toFirstQuadrantAbutment K).topGradedIso p).hom ≫
    (Functor.ofOpSequence ((h.toFirstQuadrantAbutment K).ι p)).map
      (homOfLE (Nat.zero_le p)).op ≫ ((h.toFirstQuadrantAbutment K).topIso p).hom

private lemma edgeComp_eq (K : D) (p : ℕ) :
    edgeComp h K p = (E.obj K).edgeEpi (p, 0) 2 ≫ (h.gradedIso K p 0).hom ≫
      (cokernelIsoTargetOfIsZeroSrc _ ((h.toFirstQuadrantAbutment K).isZero_bot p)).hom ≫
      ((h.filtration p).obj K).filtration.ι.app (op (p : ℤ)) ≫ (h.abutmentIso p).hom.app K := by
  have := ofOpSequence_comp_ι ((h.filtration p).obj K).filtration p
  simp only [edgeComp, FirstQuadrantAbutment.topGradedIso, Iso.trans_hom, Category.assoc]
  congr 3
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) this)

section EdgeEpiNaturality

variable {ι : Type*} {c : ℤ → ComplexShape ι} {r₀ : ℤ}
  {E₁ E₂ : SpectralSequence C c r₀} (g : E₁ ⟶ E₂)

@[reassoc]
private lemma edgeEpiStep_naturality' (pq : ι) (r r' : ℤ)
    [E₁.HasEdgeEpiAt pq r] [E₂.HasEdgeEpiAt pq r]
    (hrr' : r + 1 = r' := by lia) (hr : r₀ ≤ r := by lia) :
    E₁.edgeEpiStep pq r r' hrr' ≫ (g.hom r').f pq =
      (g.hom r).f pq ≫ E₂.edgeEpiStep pq r r' hrr' := by
  have h₁ : (g.hom r').f pq ≫ (E₂.iso r r' pq hrr' hr).inv =
      (E₁.iso r r' pq hrr' hr).inv ≫ HomologicalComplex.homologyMap (g.hom r hr) pq := by
    rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq, g.comm r r' pq hrr' hr]
  rw [← cancel_mono (E₂.iso r r' pq hrr' hr).inv, Category.assoc, Category.assoc,
    E₂.edgeEpiStep_comp_iso_inv pq r r', h₁, E₁.edgeEpiStep_comp_iso_inv_assoc pq r r',
    ← cancel_mono ((E₂.page r hr).isoHomologyι pq _ rfl (by simp)).hom]
  simp [HomologicalComplex.homologyι_naturality, HomologicalComplex.p_opcyclesMap]

@[reassoc]
private lemma edgeEpiSteps_naturality' (pq : ι) (r r' : ℤ)
    (hrr' : r ≤ r' := by lia) (hr₀ : r₀ ≤ r := by lia)
    [E₁.HasPageInfinityAt pq] [E₂.HasPageInfinityAt pq]
    [E₁.HasEdgeEpiAtFrom pq r] [E₂.HasEdgeEpiAtFrom pq r] :
    E₁.edgeEpiSteps pq r r' hrr' ≫ (g.hom r').f pq =
      (g.hom r).f pq ≫ E₂.edgeEpiSteps pq r r' hrr' := by
  obtain ⟨k, hk⟩ := Int.le.dest hrr'
  revert r'
  induction k with
  | zero =>
    intro r' hrr' hk
    obtain rfl : r = r' := by omega
    simp
  | succ k hk =>
    intro r' hrr' hk'
    rw [E₁.edgeEpiSteps_eq_edgeEpiSteps_comp_edgeEpiStep pq r (r + k) r' (by lia) (by lia),
      Category.assoc, edgeEpiStep_naturality' _ _ _ _ (by lia) (by lia),
      ← Category.assoc, hk (r + k) (by lia) rfl, Category.assoc,
      E₂.edgeEpiSteps_eq_edgeEpiSteps_comp_edgeEpiStep pq r (r + k) r' (by lia) (by lia)]

private lemma edgeEpi_naturality' (pq : ι) (r : ℤ) (hr₀ : r₀ ≤ r := by lia)
    [E₁.HasPageInfinityAt pq] [E₂.HasPageInfinityAt pq]
    [E₁.HasEdgeEpiAtFrom pq r] [E₂.HasEdgeEpiAtFrom pq r] :
    (g.hom r hr₀).f pq ≫ E₂.edgeEpi pq r =
      E₁.edgeEpi pq r ≫ SpectralSequence.Hom.mapPageInfinity g pq := by
  have hrs : r ≤ max r (max (E₁.rMin pq) (E₂.rMin pq)) := le_max_left _ _
  set s := max r (max (E₁.rMin pq) (E₂.rMin pq)) with hs
  have hs₀ : r₀ ≤ s := hr₀.trans hrs
  have : E₁.HasEdgeMonoAtFrom pq s :=
    E₁.hasEdgeMonoAtFrom_of_GE pq (E₁.rMin pq) s ((le_max_left _ _).trans (le_max_right r _))
  have : E₁.HasEdgeEpiAtFrom pq s := E₁.hasEdgeEpiAtFrom_of_GE pq r s hrs
  have : E₂.HasEdgeMonoAtFrom pq s :=
    E₂.hasEdgeMonoAtFrom_of_GE pq (E₂.rMin pq) s ((le_max_right _ _).trans (le_max_right r _))
  have : E₂.HasEdgeEpiAtFrom pq s := E₂.hasEdgeEpiAtFrom_of_GE pq r s hrs
  rw [SpectralSequence.Hom.mapPageInfinity_eq g pq s hs₀,
    ← E₁.edgeEpiSteps_pageInfinityIso_inv' pq r s hrs,
    ← E₂.edgeEpiSteps_pageInfinityIso_inv' pq r s hrs,
    Category.assoc, Iso.inv_hom_id_assoc, ← edgeEpiSteps_naturality'_assoc g pq r s hrs hr₀]

end EdgeEpiNaturality

@[reassoc]
private lemma π_cokernelIsoTargetOfIsZeroSrc_hom {Z W : C} (g : Z ⟶ W) (hZ : IsZero Z) :
    cokernel.π g ≫ (cokernelIsoTargetOfIsZeroSrc g hZ).hom = 𝟙 W := by
  simp [cokernelIsoTargetOfIsZeroSrc]

private lemma gr_map_cokernelIsoTarget {A B : FilteredObject C ℤᵒᵖ} (ψ : A ⟶ B) (p : ℤ)
    (hA : IsZero (A.filtration.obj (op (p + 1)))) (hB : IsZero (B.filtration.obj (op (p + 1)))) :
    (FilteredObject.gr p).map ψ ≫
      (cokernelIsoTargetOfIsZeroSrc (B.filtration.step (FilteredObject.succHom p)) hB).hom ≫
        B.filtration.ι.app (op p) =
      (cokernelIsoTargetOfIsZeroSrc (A.filtration.step (FilteredObject.succHom p)) hA).hom ≫
        A.filtration.ι.app (op p) ≫ ψ.hom := by
  rw [← cancel_epi (cokernel.π _)]
  simp [FilteredObject.grMap, π_cokernelIsoTargetOfIsZeroSrc_hom_assoc]

private lemma edgeComp_naturality {K L : D} (φ : K ⟶ L) (p : ℕ) :
    ((E.map φ).hom 2).f (p, 0) ≫ edgeComp h L p = edgeComp h K p ≫ (H p).map φ := by
  rw [edgeComp_eq, edgeComp_eq, reassoc_of% (edgeEpi_naturality' (E.map φ) (p, 0) 2),
    reassoc_of% (h.gradedIso_naturality φ p 0)]
  simp only [Category.assoc]
  refine congrArg (_ ≫ _ ≫ ·) ?_
  have hab := (h.abutmentIso p).hom.naturality φ
  simp only [Functor.comp_map, FilteredObject.forget_map] at hab
  have key := gr_map_cokernelIsoTarget ((h.filtration p).map φ) (p : ℤ)
    ((h.toFirstQuadrantAbutment K).isZero_bot p) ((h.toFirstQuadrantAbutment L).isZero_bot p)
  have key' := congrArg (· ≫ (h.abutmentIso p).hom.app L) key
  simp only [Category.assoc, hab] at key'
  exact key'.trans ((Category.assoc _ _ _).trans (congrArg _ (Category.assoc _ _ _))).symm

private lemma isZero_page_of_isZero_two (S : E₂CohomologicalSpectralSequenceNat C) (pq : ℕ × ℕ)
    (h0 : IsZero ((S.page 2).X pq)) (r : ℤ) (hr : 2 ≤ r) : IsZero ((S.page r hr).X pq) := by
  induction r, hr using Int.leInduction with
  | base => exact h0
  | succ r hr ih =>
    exact (((S.page r hr).sc pq).isZero_homology_of_isZero_X₂ ih).of_iso
      (S.iso r (r + 1) pq rfl hr).symm

private lemma hasEdgeMonoAtFrom_bottom (S : E₂CohomologicalSpectralSequenceNat C)
    (h0 : ∀ a b : ℕ, 1 ≤ b → IsZero ((S.page 2).X (a, b))) (p : ℕ) :
    S.HasEdgeMonoAtFrom (p, 0) 2 :=
  SpectralSequence.HasEdgeMonoAtFrom.mk' _ _ _ fun k =>
    { le := by lia
      zero := fun pq' => by
        by_cases hrel : (ComplexShape.spectralSequenceNat ((2 + (k : ℤ)), 1 - (2 + (k : ℤ)))).Rel
            pq' (p, 0)
        · rw [ComplexShape.spectralSequenceNat_rel_iff] at hrel
          exact (isZero_page_of_isZero_two S pq' (h0 _ _ (by lia)) _ (by lia)).eq_of_src _ _
        · exact (S.page (2 + (k : ℤ)) (by lia)).shape _ _ hrel }

private lemma isZero_pageInfinity_of (S : E₂CohomologicalSpectralSequenceNat C) (pq : ℕ × ℕ)
    (h0 : IsZero ((S.page 2).X pq)) : IsZero (S.pageInfinity pq) :=
  (isZero_page_of_isZero_two S pq h0 _ (S.LE_rMin pq)).of_iso (S.pageInfinityIso' pq)

private lemma isIso_edgeComp (K : D) (h0 : ∀ a b : ℕ, 1 ≤ b → IsZero (((E.obj K).page 2).X (a, b)))
    (p : ℕ) : IsIso (edgeComp h K p) := by
  have := hasEdgeMonoAtFrom_bottom (E.obj K) h0 p
  have hι : ∀ n a, a < n → IsIso ((h.toFirstQuadrantAbutment K).ι n a) := by
    intro n a han
    obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_lt han
    have := (h.toFirstQuadrantAbutment K).mono_ι (a + q + 1) a
    have hz : IsZero (cokernel ((h.toFirstQuadrantAbutment K).ι (a + q + 1) a)) :=
      (isZero_pageInfinity_of (E.obj K) (a, q + 1) (h0 _ _ (by lia))).of_iso
        ((h.toFirstQuadrantAbutment K).gradedIso a (q + 1)).symm
    have := Preadditive.epi_of_isZero_cokernel _ hz
    exact isIso_of_mono_of_epi _
  have hseq : ∀ k m (hm : m + k = p), IsIso ((Functor.ofOpSequence
      ((h.toFirstQuadrantAbutment K).ι p)).map (homOfLE (show m ≤ p by lia)).op) := by
    intro k
    induction k with
    | zero =>
      intro m hm
      obtain rfl : m = p := by lia
      have : (homOfLE (show m ≤ m by lia)).op = 𝟙 (op m) := rfl
      rw [this, CategoryTheory.Functor.map_id]
      infer_instance
    | succ k ih =>
      intro m hm
      have : (homOfLE (show m ≤ p by lia)).op =
          (homOfLE (show m + 1 ≤ p by lia)).op ≫ (homOfLE (Nat.le_succ m)).op := rfl
      rw [this, Functor.map_comp, Functor.ofOpSequence_map_homOfLE_succ]
      exact IsIso.comp_isIso' (ih (m + 1) (by lia)) (hι p m (by lia))
  have h1 := hseq p 0 (by lia)
  have h2 : IsIso ((E.obj K).edgeEpi (p, 0) 2) := by
    rw [SpectralSequence.edgeEpi_eq_pageInfinityIso_inv]; infer_instance
  rw [edgeComp]
  exact IsIso.comp_isIso' h2
    (IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' h1 (Iso.isIso_hom _)))

omit [Abelian C] in
private lemma assoc4 {A₁ A₂ A₃ A₄ A₅ A₆ : C} (a : A₁ ⟶ A₂) (b : A₂ ⟶ A₃) (c : A₃ ⟶ A₄)
    (d : A₄ ⟶ A₅) (e : A₅ ⟶ A₆) : (a ≫ b ≫ c ≫ d) ≫ e = a ≫ b ≫ c ≫ d ≫ e := by
  simp only [Category.assoc]

/-- The abutment of `h` at `K` with its top identification composed with `θ`. -/
private noncomputable def abutmentWith (K : D) {HY : ℕ → C} (θ : ∀ n, (H n).obj K ≅ HY n) :
    FirstQuadrantAbutment (E.obj K) HY :=
  { h.toFirstQuadrantAbutment K with
    topIso := fun n => (h.toFirstQuadrantAbutment K).topIso n ≪≫ θ n }

private lemma edge_abutmentWith {KA KL : D} (φ : KA ⟶ KL) {HY : ℕ → C}
    (θ : ∀ n, (H n).obj KL ≅ HY n)
    {T : C} (p : ℕ) (N : T ⟶ HY p) (κ : (H p).obj KA ≅ T)
    (hκ : κ.hom ≫ N = (H p).map φ ≫ (θ p).hom)
    [IsIso (((E.map φ).hom 2 (le_refl 2)).f (p, 0))] [IsIso (edgeComp h KA p)] :
    (E.obj KL).edgeEpi (p, 0) 2 ≫ ((abutmentWith h KL θ).topGradedIso p).hom ≫
        (Functor.ofOpSequence ((abutmentWith h KL θ).ι p)).map (homOfLE (Nat.zero_le p)).op ≫
          ((abutmentWith h KL θ).topIso p).hom =
      ((asIso (((E.map φ).hom 2 (le_refl 2)).f (p, 0))).symm ≪≫ asIso (edgeComp h KA p) ≪≫ κ).hom ≫
        N := by
  have e1 : (E.obj KL).edgeEpi (p, 0) 2 ≫ ((abutmentWith h KL θ).topGradedIso p).hom ≫
        (Functor.ofOpSequence ((abutmentWith h KL θ).ι p)).map (homOfLE (Nat.zero_le p)).op ≫
          ((abutmentWith h KL θ).topIso p).hom = edgeComp h KL p ≫ (θ p).hom := by
    rw [edgeComp]
    exact (assoc4 _ _ _ _ _).symm
  rw [e1, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, asIso_inv, asIso_hom, Category.assoc,
    Category.assoc, hκ, IsIso.eq_inv_comp, ← Category.assoc, edgeComp_naturality, Category.assoc]

end Abutment

private abbrev Ab := AddCommGrpCat.{u}

private def FQ (K : HomologicalComplex₂ Ab.{u} (ComplexShape.up ℤ) (ComplexShape.up ℤ)) : Prop :=
  ∀ i j : ℤ, (i < 0 ∨ j < 0) → IsZero ((K.X i).X j)

private abbrev DQ := ObjectProperty.FullSubcategory FQ.{u}

private noncomputable abbrev GQ : DQ.{u} ⥤ CochainComplex.Filtered Ab.{u} :=
  ObjectProperty.ι FQ ⋙ Stacks.Cohomology.CechSpectral.totalFiltrationFunctor Ab
    (fun _ j => j) (fun _ _ => le_rfl) (fun _ _ => by omega)

private lemma isIso_GQ_filtration_ι_f (X : DQ.{u}) (n : ℤ) :
    IsIso (((GQ.obj X).filtration.ι.app (op (0 : ℤ))).f n) :=
  HomologicalComplex₂.isIso_totalFiltration₂_ι_f X.obj (fun i j hj => X.property i j (Or.inr hj)) n

private lemma isZero_GQ_filtration_obj_X (X : DQ.{u}) (p n : ℤ) (h : n < p) :
    IsZero (((GQ.obj X).filtration.obj (op p)).X n) :=
  HomologicalComplex₂.isZero_totalFiltration₂_obj_X X.obj
    (fun i j hi => X.property i j (Or.inl hi)) p n h

private noncomputable abbrev SQ : DQ.{u} ⥤ E₂CohomologicalSpectralSequenceNat Ab.{u} :=
  CochainComplex.Filtered.natE₂SequenceFunctor GQ isIso_GQ_filtration_ι_f isZero_GQ_filtration_obj_X

private lemma isIso_iff_of_iso_square {C : Type*} [Category C] [Abelian C]
    {ι : Type*} {c : ℤ → ComplexShape ι} {r₀ : ℤ}
    {E₁ E₂ E₁' E₂' : SpectralSequence C c r₀} (e₁ : E₁ ⟶ E₁') (e₂ : E₂ ⟶ E₂')
    [IsIso e₁] [IsIso e₂]
    (f : E₁ ⟶ E₂) (f' : E₁' ⟶ E₂') (sq : f ≫ e₂ = e₁ ≫ f')
    (r : ℤ) (hr : r₀ ≤ r) (pq : ι) :
    IsIso ((f.hom r hr).f pq) ↔ IsIso ((f'.hom r hr).f pq) := by
  let Φ := SpectralSequence.pageFunctor C c r₀ r hr ⋙ HomologicalComplex.eval C _ pq
  have h := congrArg Φ.map sq
  rw [Φ.map_comp, Φ.map_comp] at h
  change IsIso (Φ.map f) ↔ IsIso (Φ.map f')
  rw [← isIso_comp_right_iff (Φ.map f) (Φ.map e₂), h, isIso_comp_left_iff]

private lemma isIso_spectralSequenceMap₂_iff
    {K L : HomologicalComplex₂ Ab.{u} (ComplexShape.up ℤ) (ComplexShape.up ℤ)}
    (φ : K ⟶ L) (r : ℤ) (hr : 0 ≤ r) (pq : ℤ × ℤ) :
    IsIso (((HomologicalComplex₂.spectralSequenceMap₂ φ).hom r hr).f pq) ↔
    IsIso (((CochainComplex.filteredSpectralSequenceMap
          (Stacks.Cohomology.CechSpectral.totalFiltrationMap
            (fun (_ : ℤ) j => j) (fun _ _ => le_rfl) (fun _ _ => by omega) φ)).hom r hr).f pq) :=
  isIso_iff_of_iso_square _ _ _ _ (HomologicalComplex₂.spectralSequenceMap₂_eqToHom φ) r hr pq

private lemma isIso_SQ_map_iff {K L : DQ.{u}} (φ : K ⟶ L) (p q : ℕ) :
    IsIso (((SQ.map φ).hom 2).f (p, q)) ↔
      IsIso (HomologicalComplex.homologyMap
        (HomologicalComplex.homologyMap ((ObjectProperty.ι FQ).map φ) (q : ℤ)) (p : ℤ)) := by
  have e0 := NatIso.isIso_map_iff (SpectralSequence.natRestrictE₂Comp_pageTwoIso
    (CochainComplex.Filtered.e₂SequenceFunctorAux GQ)
    (CochainComplex.Filtered.isFirstQuadrant_e₂SequenceFunctorAux GQ isIso_GQ_filtration_ι_f
      isZero_GQ_filtration_obj_X) p q) φ
  have e1 :=
    isIso_spectralSequenceMap₂_iff ((ObjectProperty.ι FQ).map φ) 2 (by omega) ((p : ℤ), (q : ℤ))
  have e2 := HomologicalComplex₂.isoTwoPageTotalFiltration₂_naturality_functor
    ((ObjectProperty.ι FQ).map φ) p q
  refine e0.trans (e1.symm.trans ?_)
  rw [← isIso_comp_right_iff _ (HomologicalComplex₂.isoTwoPageTotalFiltration₂
      ((ObjectProperty.ι FQ).obj L)
      (HomologicalComplex₂.spectralSequence₂ ((ObjectProperty.ι FQ).obj L))
      (HomologicalComplex₂.pageIso₂ ((ObjectProperty.ι FQ).obj L))
          (HomologicalComplex₂.exists_delta₂ ((ObjectProperty.ι FQ).obj L)) p q).hom, e2,
    isIso_comp_left_iff]

private noncomputable def pageTwoIsoQ (K : DQ.{u}) (p q : ℕ) :
    ((SQ.obj K).page 2).X (p, q) ≅ (K.obj.homology (q : ℤ)).homology (p : ℤ) :=
  (SpectralSequence.natRestrictE₂Comp_pageTwoIso
    (CochainComplex.Filtered.e₂SequenceFunctorAux GQ)
    (CochainComplex.Filtered.isFirstQuadrant_e₂SequenceFunctorAux GQ isIso_GQ_filtration_ι_f
      isZero_GQ_filtration_obj_X) p q).app K ≪≫
  ((SpectralSequence.pageFunctor Ab.{u} (fun r => ComplexShape.up' (r, 1 - r)) 0 2 (by omega) ⋙
      HomologicalComplex.eval Ab.{u} _ ((p : ℤ), (q : ℤ))).mapIso
    (eqToIso (HomologicalComplex₂.spectralSequence₂_eq_filteredSpectralSequence K.obj))).symm ≪≫
  HomologicalComplex₂.isoTwoPageTotalFiltration₂ K.obj
      (HomologicalComplex₂.spectralSequence₂ K.obj) (HomologicalComplex₂.pageIso₂ K.obj)
          (HomologicalComplex₂.exists_delta₂ K.obj) p q

/-- **The edge computation by naturality.** Let `φ : A ⟶ L` be a morphism of first-quadrant
double complexes whose second spectral sequence for `A` is concentrated on the bottom row and
which induces isomorphisms `H^p_{II} H^0_I(A) ≅ H^p_{II} H^0_I(L)`. Then the second spectral
sequence of `L`, with its abutment transported along `θ`, has a second page identified with
`T` such that its bottom-row edge map is `N`, as soon as `N` is the map induced by `φ` on total
cohomology under `κ` and `θ`. -/
private theorem assembly {HY : ℕ → Ab.{u}} {T : ℕ → ℕ → Ab.{u}} {KA KL : DQ.{u}} (φ : KA ⟶ KL)
    (hA : ∀ p q : ℕ, 1 ≤ q → IsZero ((KA.obj.homology (q : ℤ)).homology (p : ℤ)))
    (hφ : ∀ p : ℕ, IsIso (HomologicalComplex.homologyMap
        (HomologicalComplex.homologyMap ((ObjectProperty.ι FQ).map φ) 0) (p : ℤ)))
    (eL : ∀ p q : ℕ, Nonempty ((KL.obj.homology (q : ℤ)).homology (p : ℤ) ≅ T p q))
    (θ : ∀ n : ℕ, (GQ ⋙ FilteredObject.forget ⋙
      HomologicalComplex.homologyFunctor Ab.{u} (ComplexShape.up ℤ) (n : ℤ)).obj KL ≅ HY n)
    (N : ∀ p : ℕ, T p 0 ⟶ HY p)
    (κ : ∀ p : ℕ, (GQ ⋙ FilteredObject.forget ⋙
      HomologicalComplex.homologyFunctor Ab.{u} (ComplexShape.up ℤ) (p : ℤ)).obj KA ≅ T p 0)
    (hκ : ∀ p : ℕ, (κ p).hom ≫ N p = (GQ ⋙ FilteredObject.forget ⋙
      HomologicalComplex.homologyFunctor Ab.{u} (ComplexShape.up ℤ) (p : ℤ)).map φ ≫ (θ p).hom) :
    ∃ (E : E₂CohomologicalSpectralSequenceNat Ab.{u}) (h : FirstQuadrantAbutment E HY)
      (e : ∀ p q : ℕ, (E.page 2).X (p, q) ≅ T p q),
      ∀ p : ℕ, E.edgeEpi (p, 0) 2 ≫ (h.topGradedIso p).hom ≫
          (Functor.ofOpSequence (h.ι p)).map (homOfLE (Nat.zero_le p)).op ≫ (h.topIso p).hom =
        (e p 0).hom ≫ N p := by
  let 𝔄 := CochainComplex.Filtered.functorialFirstQuadrantAbutment GQ isIso_GQ_filtration_ι_f
    isZero_GQ_filtration_obj_X
  have hφ2 : ∀ p : ℕ, IsIso (((SQ.map φ).hom 2 (le_refl 2)).f (p, 0)) := fun p =>
    (isIso_SQ_map_iff φ p 0).2 (hφ p)
  have hAz : ∀ a b : ℕ, 1 ≤ b → IsZero (((SQ.obj KA).page 2).X (a, b)) := fun a b hb =>
    (hA a b hb).of_iso (pageTwoIsoQ KA a b)
  have hedA := isIso_edgeComp 𝔄 KA hAz
  let e : ∀ p q : ℕ, ((SQ.obj KL).page 2).X (p, q) ≅ T p q := fun p q =>
    match q with
    | 0 => (asIso (((SQ.map φ).hom 2 (le_refl 2)).f (p, 0))).symm ≪≫
        asIso (edgeComp 𝔄 KA p) ≪≫ κ p
    | q + 1 => pageTwoIsoQ KL p (q + 1) ≪≫ (eL p (q + 1)).some
  exact ⟨SQ.obj KL, abutmentWith 𝔄 KL θ, e, fun p =>
    edge_abutmentWith 𝔄 φ θ p (N p) (κ p) (hκ p)⟩

section Sheaf

attribute [local instance] HasDerivedCategory.standard

variable {X Y : TopCat.{u}} (f : Y ⟶ X) (F : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})

/-- The complex `f_* I` for an injective resolution `I`, extended by zero to `ℤ`. -/
private noncomputable abbrev pushRes (I : InjectiveResolution F) :
    CochainComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) ℤ :=
  (((abelianPushforward.{u, u} f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    I.cocomplex).extend ComplexShape.embeddingUpNat

private instance (I : InjectiveResolution F) : (pushRes f F I).IsStrictlyGE 0 := by
  dsimp [pushRes]
  infer_instance

private lemma injective_pushRes (I : InjectiveResolution F) (n : ℤ) :
    Injective ((pushRes f F I).X n) := by
  by_cases hn : 0 ≤ n
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    exact Injective.of_iso (HomologicalComplex.extendXIso _ _ rfl).symm
      ((abelianPushforward.{u, u} f).injective_obj_of_injective (I.injective k))
  · exact IsZero.injective (CochainComplex.isZero_of_isStrictlyGE _ 0 _ (by lia))

/-- A kernel of `K.d i j` is identified with the cycles by `liftCycles`. -/
private lemma isIso_liftCycles_of_isLimit {C : Type*} [Category C] [Abelian C] {ι : Type*}
    {c : ComplexShape ι} (K : HomologicalComplex C c) {i j : ι} (hij : c.next i = j) {A : C}
    (g : A ⟶ K.X i) (w : g ≫ K.d i j = 0) (hg : IsLimit (KernelFork.ofι g w)) :
    IsIso (K.liftCycles g j hij w) := by
  let e := IsLimit.conePointUniqueUpToIso hg (K.cyclesIsKernel i j hij)
  have : K.liftCycles g j hij w = e.hom := by
    rw [← cancel_mono (K.iCycles i), HomologicalComplex.liftCycles_i]
    exact (IsLimit.conePointUniqueUpToIso_hom_comp hg (K.cyclesIsKernel i j hij)
      WalkingParallelPair.zero).symm
  rw [this]
  infer_instance

section Data

variable (I : InjectiveResolution F) (J : (pushRes f F I).CartanEilenbergResolution)
  [hJ : CochainComplex.IsStrictlyGE J.bicomplex 0]

/-- The column `Ker(d₁^{0,•})` of the Cartan-Eilenberg resolution. -/
private noncomputable abbrev Jc :
    CochainComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) ℤ :=
  J.bicomplex.cycles 0

private noncomputable abbrev Acol := (HomologicalComplex.single
  (CochainComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) ℤ)
    (ComplexShape.up ℤ) 0).obj (Jc f F I J)

private noncomputable def φcol : Acol f F I J ⟶ J.bicomplex :=
  HomologicalComplex.mkHomFromSingle (J.bicomplex.iCycles 0) (fun k hk => by
    obtain rfl : k = 1 := by simpa using hk.symm
    exact J.bicomplex.iCycles_d 0 1)

private lemma fq_L : FQ (HomologicalComplex₂.TotalMap.mapBicomplex (abelianSections.{u, u} X ⊤)
    J.bicomplex) := by
  intro i j hij
  apply (abelianSections.{u, u} X ⊤).map_isZero
  rcases hij with h | h
  · exact (HomologicalComplex.eval _ _ j).map_isZero
      (CochainComplex.isZero_of_isStrictlyGE J.bicomplex 0 i h)
  · exact CochainComplex.isZero_of_isStrictlyGE (J.bicomplex.X i) 0 j h

include hJ in
private lemma isZero_Jc_X (j : ℤ) (hj : j < 0) : IsZero ((Jc f F I J).X j) :=
  IsZero.of_mono ((J.bicomplex.iCycles 0).f j)
    (CochainComplex.isZero_of_isStrictlyGE (J.bicomplex.X 0) 0 j hj)

private lemma isZero_Acol_X (i : ℤ) (hi : i ≠ 0) : IsZero ((Acol f F I J).X i) :=
  HomologicalComplex.isZero_single_obj_X _ _ _ _ hi

include hJ in
private lemma fq_A : FQ (HomologicalComplex₂.TotalMap.mapBicomplex (abelianSections.{u, u} X ⊤)
    (Acol f F I J)) := by
  intro i j hij
  apply (abelianSections.{u, u} X ⊤).map_isZero
  by_cases hi : i = 0
  · subst hi
    rcases hij with h | h
    · omega
    · exact (isZero_Jc_X f F I J j h).of_iso ((HomologicalComplex.eval _ _ j).mapIso
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (Jc f F I J)))
  · exact (HomologicalComplex.eval _ _ j).map_isZero (isZero_Acol_X f F I J i hi)

private lemma isZero_homology_homology_Acol (p q : ℕ) (hq : 1 ≤ q) :
    IsZero (((HomologicalComplex₂.TotalMap.mapBicomplex (abelianSections.{u, u} X ⊤)
      (Acol f F I J)).homology (q : ℤ)).homology (p : ℤ)) := by
  apply (HomologicalComplex.homologyFunctor _ _ (p : ℤ)).map_isZero
  apply StacksDraft.TotalComplexQuasiIso.isZero_homology_of_isZero_X
  exact ((abelianSections.{u, u} X ⊤).mapHomologicalComplex _).map_isZero
    (isZero_Acol_X f F I J q (by omega))

/-- The morphism `Γ(A) ⟶ Γ(J)` of double complexes. -/
private noncomputable abbrev φΓ := (((abelianSections.{u, u} X ⊤).mapHomologicalComplex
  (ComplexShape.up ℤ)).mapHomologicalComplex (ComplexShape.up ℤ)).map (φcol f F I J)

include hJ in
private lemma isIso_homologyMap_φΓ : IsIso (HomologicalComplex.homologyMap (φΓ f F I J) 0) := by
  set K := HomologicalComplex₂.TotalMap.mapBicomplex (abelianSections.{u, u} X ⊤) (Acol f F I J)
  set L := HomologicalComplex₂.TotalMap.mapBicomplex (abelianSections.{u, u} X ⊤) J.bicomplex
  set G := (abelianSections.{u, u} X ⊤).mapHomologicalComplex (ComplexShape.up ℤ)
  have hK1 : IsZero (K.X 1) := G.map_isZero (isZero_Acol_X f F I J 1 (by omega))
  have hKm : IsZero (K.X (-1)) := G.map_isZero (isZero_Acol_X f F I J (-1) (by omega))
  have hLm : IsZero (L.X (-1)) := G.map_isZero
    (CochainComplex.isZero_of_isStrictlyGE J.bicomplex 0 (-1) (by omega))
  have : IsIso (K.homologyπ 0) := K.isIso_homologyπ (-1) 0 (by simp) (hKm.eq_of_src _ _)
  have : IsIso (L.homologyπ 0) := L.isIso_homologyπ (-1) 0 (by simp) (hLm.eq_of_src _ _)
  have : IsIso (K.iCycles 0) := K.isIso_iCycles 0 1 (by simp) (hK1.eq_of_tgt _ _)
  -- `Γ(Z⁰_I J) ⟶ Γ(J^{0,•})` is a kernel of `Γ(d^{0,1})`
  have wJ : (φcol f F I J).f 0 ≫ J.bicomplex.d 0 1 = 0 := by
    simp [φcol, HomologicalComplex.mkHomFromSingle_f]
  have hJlim : IsLimit (KernelFork.ofι ((φcol f F I J).f 0) wJ) := by
    refine (J.bicomplex.cyclesIsKernel 0 1 (by simp)).ofIsoLimit
      (Fork.ext (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (Jc f F I J)).symm ?_)
    simp [φcol, HomologicalComplex.mkHomFromSingle_f]
  have hLlim := KernelFork.mapIsLimit _ hJlim G
  have w : (φΓ f F I J).f 0 ≫ L.d 0 1 = 0 := by
    change G.map _ ≫ G.map _ = 0
    rw [← G.map_comp, wJ, G.map_zero]
  have hlift := isIso_liftCycles_of_isLimit L (i := 0) (j := 1) (by simp)
    ((φΓ f F I J).f 0) w hLlim
  have hc : HomologicalComplex.cyclesMap (φΓ f F I J) 0 =
      K.iCycles 0 ≫ L.liftCycles ((φΓ f F I J).f 0) 1 (by simp) w := by
    rw [← cancel_mono (L.iCycles 0), HomologicalComplex.cyclesMap_i, Category.assoc,
      HomologicalComplex.liftCycles_i]
  have : IsIso (HomologicalComplex.cyclesMap (φΓ f F I J) 0) := by rw [hc]; infer_instance
  have h := HomologicalComplex.homologyπ_naturality (φΓ f F I J) 0
  have : IsIso (K.homologyπ 0 ≫ HomologicalComplex.homologyMap (φΓ f F I J) 0) := by
    rw [h]; infer_instance
  exact IsIso.of_isIso_comp_left (K.homologyπ 0) _

end Data

section Generic

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]

private lemma homologyMap_map_eq_of_Q_eq (G : C ⥤ D) [G.Additive] {K L : CochainComplex C ℤ}
    [L.IsKInjective] (u v : K ⟶ L) (h : DerivedCategory.Q.map u = DerivedCategory.Q.map v)
    (n : ℤ) : HomologicalComplex.homologyMap ((G.mapHomologicalComplex _).map u) n =
      HomologicalComplex.homologyMap ((G.mapHomologicalComplex _).map v) n := by
  have h' : (HomotopyCategory.quotient C _).map u = (HomotopyCategory.quotient C _).map v := by
    apply (CochainComplex.IsKInjective.Qh_map_bijective _ L).1
    have e := (DerivedCategory.quotientCompQhIso C).hom.naturality u
    have e' := (DerivedCategory.quotientCompQhIso C).hom.naturality v
    simp only [Functor.comp_map] at e e'
    rw [← cancel_mono ((DerivedCategory.quotientCompQhIso C).hom.app L), e, e', h]
  exact (G.mapHomotopy (HomotopyCategory.homotopyOfEq _ _ h')).homologyMap_eq n

private lemma quasiIso_map_of_kInjective (G : C ⥤ D) [G.Additive] {K L : CochainComplex C ℤ}
    [K.IsKInjective] [L.IsKInjective] (u : K ⟶ L) [QuasiIso u] :
    QuasiIso ((G.mapHomologicalComplex _).map u) := by
  obtain ⟨e, he⟩ := (CochainComplex.IsKInjective.quasiIso_iff u).1 inferInstance
  subst he
  exact (G.mapHomotopyEquiv e).quasiIso_hom

private lemma exists_lift_along_quasiIso {K K' L : CochainComplex C ℤ} [L.IsKInjective] (η : K ⟶ K')
    [QuasiIso η] (c : K ⟶ L) :
    ∃ χ : K' ⟶ L, DerivedCategory.Q.map η ≫ DerivedCategory.Q.map χ = DerivedCategory.Q.map c := by
  let iso := DerivedCategory.quotientCompQhIso C
  obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient C _).obj K') L).2
      (iso.hom.app K' ≫ inv (DerivedCategory.Q.map η) ≫ DerivedCategory.Q.map c ≫ iso.inv.app L)
  obtain ⟨χ, rfl⟩ := (HomotopyCategory.quotient C _).map_surjective g
  refine ⟨χ, ?_⟩
  have e := iso.hom.naturality χ
  simp only [Functor.comp_map] at e
  rw [← IsIso.eq_inv_comp, ← cancel_epi (iso.hom.app K'), ← e, hg]
  have e2 := iso.hom.naturality c
  simp only [Functor.comp_map] at e2
  simp [e2]

private lemma quasiIso_of_Q_map_comp_eq {K K' L : CochainComplex C ℤ} (η : K ⟶ K') [QuasiIso η]
    (χ : K' ⟶ L) (c : K ⟶ L) [QuasiIso c]
    (h : DerivedCategory.Q.map η ≫ DerivedCategory.Q.map χ = DerivedCategory.Q.map c) :
    QuasiIso χ := by
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
  have : IsIso (DerivedCategory.Q.map η ≫ DerivedCategory.Q.map χ) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_left (DerivedCategory.Q.map η) _

end Generic

private lemma hκ_alg {C : Type*} [Category C] {HA HL Hc H2z H2 RJ T0 HT HM HI HY : C}
    (totφ : HA ⟶ HL) (tA : Hc ≅ HA) (cT : HL ≅ HT) (inc : Hc ⟶ HT) (χ : H2z ≅ Hc)
    (ψz : H2z ⟶ HM) (α : HM ≅ HT) (zJ : H2z ≅ H2) (ψℕ : H2 ⟶ HI) (zI : HM ≅ HI) (iJ : RJ ≅ H2)
    (iI : HY ≅ HI) (r0 : T0 ≅ RJ)
    (h3 : tA.hom ≫ totφ ≫ cT.hom = inc) (h4 : χ.hom ≫ inc = ψz ≫ α.hom)
    (h2 : zJ.hom ≫ ψℕ = ψz ≫ zI.hom) :
    (tA.symm ≪≫ χ.symm ≪≫ zJ ≪≫ iJ.symm ≪≫ r0.symm).hom ≫ (r0.hom ≫ iJ.hom ≫ ψℕ ≫ iI.inv) =
      totφ ≫ (cT ≪≫ α.symm ≪≫ zI ≪≫ iI.symm).hom := by
  have h4' : ψz = χ.hom ≫ inc ≫ α.inv := by
    rw [← Category.assoc, h4, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% h2,
    h4', ← h3, Iso.inv_hom_id_assoc]

section Data2

variable (I : InjectiveResolution F) (J : (pushRes f F I).CartanEilenbergResolution)
  [hJ : CochainComplex.IsStrictlyGE J.bicomplex 0]

/-- The augmentation `F ⟶ I⁰` of the injective resolution `I`. -/
private noncomputable def ι0 : F ⟶ I.cocomplex.X 0 :=
  (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 F).inv ≫ I.ι.f 0

private lemma ι0_d : ι0 F I ≫ I.cocomplex.d 0 1 = 0 := by
  rw [ι0, Category.assoc, I.ι_f_zero_comp_complex_d, comp_zero]

private noncomputable def gAug : (abelianPushforward.{u, u} f).obj F ⟶ (pushRes f F I).X 0 :=
  (abelianPushforward.{u, u} f).map (ι0 F I) ≫
    ((((abelianPushforward.{u, u} f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      I.cocomplex).extendXIso ComplexShape.embeddingUpNat
        (show ComplexShape.embeddingUpNat.f 0 = (0 : ℤ) from rfl)).inv

private lemma pushRes_d01 : (pushRes f F I).d 0 1 =
    ((((abelianPushforward.{u, u} f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      I.cocomplex).extendXIso ComplexShape.embeddingUpNat
        (show ComplexShape.embeddingUpNat.f 0 = (0 : ℤ) from rfl)).hom ≫
      (abelianPushforward.{u, u} f).map (I.cocomplex.d 0 1) ≫
    ((((abelianPushforward.{u, u} f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      I.cocomplex).extendXIso ComplexShape.embeddingUpNat
        (show ComplexShape.embeddingUpNat.f 1 = (1 : ℤ) from rfl)).inv :=
  HomologicalComplex.extend_d_eq _ _ rfl rfl

private lemma gAug_d : gAug f F I ≫ (pushRes f F I).d 0 1 = 0 := by
  rw [pushRes_d01, gAug]
  erw [Category.assoc, Iso.inv_hom_id_assoc, ← Functor.map_comp_assoc, ι0_d, Functor.map_zero,
    zero_comp]

private noncomputable def gAugIsLimit : IsLimit (KernelFork.ofι (gAug f F I) (gAug_d f F I)) := by
  let P := abelianPushforward.{u, u} f
  have hS : (ShortComplex.mk _ _ (ι0_d F I)).Exact := by
    refine (ShortComplex.exact_iff_of_iso ?_).1 I.exact₀
    exact ShortComplex.isoMk (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 F)
      (Iso.refl _) (Iso.refl _)
      (by simpa only [ι0, Iso.hom_inv_id_assoc, Iso.refl_hom] using
        (Category.comp_id (I.ι.f 0)).symm)
      (by simp)
  have : Mono (ι0 F I) := by rw [ι0]; infer_instance
  let S' := ShortComplex.mk (gAug f F I) ((pushRes f F I).d 0 1) (gAug_d f F I)
  have e : S' ≅ (ShortComplex.mk _ _ (ι0_d F I)).map P :=
    ShortComplex.isoMk (Iso.refl _)
      (((P.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).extendXIso
        ComplexShape.embeddingUpNat (show ComplexShape.embeddingUpNat.f 0 = (0 : ℤ) from rfl))
      (((P.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).extendXIso
        ComplexShape.embeddingUpNat (show ComplexShape.embeddingUpNat.f 1 = (1 : ℤ) from rfl))
      (by
        dsimp [S', gAug]
        erw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp])
      (by
        dsimp [S']
        rw [pushRes_d01]
        erw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id])
  have hS'' : S'.Exact := (ShortComplex.exact_iff_of_iso e).2
    (hS.map_of_mono_of_preservesKernel P inferInstance inferInstance)
  have : Mono (gAug f F I) := by
    have : Mono ((abelianPushforward.{u, u} f).map (ι0 F I)) := Functor.map_mono _ _
    exact mono_comp' this (IsIso.mono_of_iso _)
  exact hS''.fIsKernel

private noncomputable abbrev embM := ((HomologicalComplex.single
  (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (ComplexShape.up ℤ)
    0).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj (pushRes f F I)

private lemma sAug_d : (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map (gAug f F I) ≫
    (embM f F I).d 0 1 = 0 := by
  change _ ≫ (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map ((pushRes f F I).d 0 1) = 0
  rw [← Functor.map_comp, gAug_d, Functor.map_zero]

private noncomputable def e₀ := (embM f F I).liftCycles
  ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map (gAug f F I)) 1 (by simp) (sAug_d f F I)

private instance : IsIso (e₀ f F I) :=
  isIso_liftCycles_of_isLimit _ _ _ _
    (KernelFork.mapIsLimit _ (gAugIsLimit f F I)
      (HomologicalComplex.single _ (ComplexShape.up ℤ) 0))

/-- The augmentation `f_* F[0] ⟶ Z⁰_I(J)`. -/
private noncomputable def cAug : (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
    ((abelianPushforward.{u, u} f).obj F) ⟶ Jc f F I J :=
  e₀ f F I ≫ HomologicalComplex.cyclesMap J.ε 0

private instance : QuasiIso (cAug f F I J) := by
  rw [cAug]; infer_instance

private lemma cAug_i : cAug f F I J ≫ J.bicomplex.iCycles 0 =
    (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map (gAug f F I) ≫ J.ε.f 0 := by
  rw [cAug, Category.assoc, HomologicalComplex.cyclesMap_i, e₀,
    HomologicalComplex.liftCycles_i_assoc]

private instance (n : ℤ) : Injective ((Jc f F I J).X n) := J.injective_cycles 0 n

include hJ in
private lemma isKInjective_Jc : (Jc f F I J).IsKInjective := by
  have : (Jc f F I J).IsStrictlyGE 0 :=
    (CochainComplex.isStrictlyGE_iff _ _).2 fun n hn => isZero_Jc_X f F I J n hn
  exact CochainComplex.isKInjective_of_injective _ 0

private lemma nonempty_homology_homology_iso_abelianCohomology (p q : ℕ) :
    Nonempty ((((((abelianSections.{u, u} X ⊤).mapHomologicalComplex
      (ComplexShape.up ℤ)).mapHomologicalComplex (ComplexShape.up ℤ)).obj J.bicomplex).homology
        (q : ℤ)).homology (p : ℤ) ≅ (abelianCohomology.{u, u} X ⊤ p).obj
          (((abelianPushforward.{u, u} f).rightDerived q).obj F)) := by
  obtain ⟨-, h2, -⟩ := J.exists_homologyIso_rightDerivedPlus (abelianSections.{u, u} X ⊤)
    ⟨0, inferInstance⟩
  obtain ⟨e⟩ := h2 p q
  refine ⟨e ≪≫ (Stacks.Cohomology.HigherDirectImagePresheaf.derivedPlusToStandard
    (abelianSections.{u, u} X ⊤) p).app _ ≪≫
      (abelianCohomology.{u, u} X ⊤ p).mapIso ?_⟩
  exact HomologicalComplex.extendHomologyIso _ ComplexShape.embeddingUpNat (by simp) ≪≫
    (I.isoRightDerivedObj (abelianPushforward.{u, u} f) q).symm

private noncomputable abbrev ΓX := abelianSections.{u, u} X ⊤

private instance : J.bicomplex.HasTotal (ComplexShape.up ℤ) :=
  StacksDraft.CartanEilenbergResolutions.hasTotal_bicomplex J

private noncomputable abbrev αTot : pushRes f F I ⟶ J.bicomplex.total (ComplexShape.up ℤ) :=
  StacksDraft.CartanEilenbergResolutions.totalAugmentation J

private instance : QuasiIso (αTot f F I J) :=
  StacksDraft.CartanEilenbergResolutions.quasiIso_totalAugmentation J ⟨0, inferInstance⟩

private lemma isKInjective_T :
    CochainComplex.IsKInjective (J.bicomplex.total (ComplexShape.up ℤ)) := by
  obtain ⟨n, hn⟩ := StacksDraft.CartanEilenbergResolutions.plus_total J
  have := StacksDraft.CartanEilenbergResolutions.injective_total_X J
  exact CochainComplex.isKInjective_of_injective _ n

private lemma isKInjective_M : CochainComplex.IsKInjective (pushRes.{u} f F I) := by
  have := injective_pushRes f F I
  exact CochainComplex.isKInjective_of_injective _ 0

private instance : HomologicalComplex₂.HasTotal (Acol.{u} f F I J) (ComplexShape.up ℤ) :=
  StacksDraft.TotalComplexQuasiIso.hasTotal_singleColumn _ 0

include hJ in
private lemma fin_A (n : ℤ) : {pq : ℤ × ℤ | ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
    (ComplexShape.up ℤ) pq = n ∧ ¬ IsZero (((Acol f F I J).X pq.1).X pq.2)}.Finite := by
  refine StacksDraft.TotalComplexQuasiIso.finite_not_isZero_of_bounded _ 0 (fun p q hq => ?_)
    (fun p hp => isZero_Acol_X f F I J p (by omega)) n
  by_cases hp : p = 0
  · subst hp
    exact (isZero_Jc_X f F I J q hq).of_iso ((HomologicalComplex.eval _ _ q).mapIso
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (Jc f F I J)))
  · exact (HomologicalComplex.eval _ _ q).map_isZero (isZero_Acol_X f F I J p hp)

/-- `Z⁰_I(J) ⟶ Tot(A)`, an isomorphism. -/
private noncomputable def uA :
    Jc.{u} f F I J ⟶ HomologicalComplex₂.total (Acol.{u} f F I J) (ComplexShape.up ℤ) :=
  haveI := StacksDraft.TotalComplexQuasiIso.hasTotal_singleColumn (Jc.{u} f F I J) 0
  (shiftFunctorZero' (CochainComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) ℤ)
    (-0) (by simp)).inv.app _ ≫
    StacksDraft.TotalComplexQuasiIso.totalSingleColumnUnit (Jc.{u} f F I J) 0

private instance : IsIso (uA f F I J) := by
  haveI := StacksDraft.TotalComplexQuasiIso.hasTotal_singleColumn (Jc.{u} f F I J) 0
  have := StacksDraft.TotalComplexQuasiIso.isIso_totalSingleColumnUnit (Jc.{u} f F I J) 0
  rw [uA]
  exact IsIso.comp_isIso'
    (Iso.isIso_hom (Iso.app (shiftFunctorZero' _ (-0) (by simp)).symm _)) this

/-- The inclusion `Z⁰_I(J) ⟶ Tot(J)`. -/
private noncomputable abbrev incl : Jc f F I J ⟶ J.bicomplex.total (ComplexShape.up ℤ) :=
  uA f F I J ≫ HomologicalComplex₂.total.map (φcol f F I J) (ComplexShape.up ℤ)

private noncomputable abbrev cTot := HomologicalComplex₂.TotalMap.totalIsoOfFinite (ΓX.{u} (X := X))
  J.bicomplex (StacksDraft.CartanEilenbergResolutions.finite_not_isZero_bicomplex J)

private noncomputable abbrev cAcol :=
  HomologicalComplex₂.TotalMap.totalIsoOfFinite (ΓX.{u} (X := X))
    (Acol.{u} f F I J) (fin_A.{u} f F I J)

private lemma map_uA_comp_totalMap_eq_map_incl :
    (((ΓX.{u} (X := X)).mapHomologicalComplex _).map (uA.{u} f F I J) ≫
    (cAcol.{u} f F I J).inv) ≫ HomologicalComplex₂.total.map (φΓ.{u} f F I J) (ComplexShape.up ℤ) ≫
      (cTot.{u} f F I J).hom =
        ((ΓX.{u} (X := X)).mapHomologicalComplex _).map (incl.{u} f F I J) := by
  have h := HomologicalComplex₂.TotalMap.totalMap_naturality (c₁₂ := ComplexShape.up ℤ)
    (ΓX.{u} (X := X)) (Acol.{u} f F I J) (φcol.{u} f F I J)
  have e1 : (cTot.{u} f F I J).hom = HomologicalComplex₂.TotalMap.totalMap (ΓX.{u} (X := X))
    J.bicomplex := rfl
  have e2 : (cAcol.{u} f F I J).hom = HomologicalComplex₂.TotalMap.totalMap (ΓX.{u} (X := X))
    (Acol.{u} f F I J) := rfl
  rw [e1, Category.assoc, h, ← e2, Iso.inv_hom_id_assoc, ← Functor.map_comp]

private lemma uA_f_zero : (uA.{u} f F I J).f 0 =
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (Jc.{u} f F I J)).inv.f 0 ≫
      HomologicalComplex₂.ιTotal (Acol.{u} f F I J) (ComplexShape.up ℤ) 0 0 0 (by simp) := by
  have : ((shiftFunctorZero' (CochainComplex (Sheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}) ℤ) (-0) (by simp)).inv.app (Jc.{u} f F I J)).f 0 = 𝟙 _ := by
    simp [shiftFunctorZero', CochainComplex.shiftFunctorZero_inv_app_f]
  refine (HomologicalComplex.comp_f _ _ 0).trans ((congrArg (· ≫ _) this).trans
    ((Category.id_comp _).trans ?_))
  rfl

private lemma incl_f_zero : (incl.{u} f F I J).f 0 = (J.bicomplex.iCycles 0).f 0 ≫
    J.bicomplex.ιTotal (ComplexShape.up ℤ) 0 0 0 (by simp) := by
  rw [incl, HomologicalComplex.comp_f, uA_f_zero, Category.assoc, HomologicalComplex₂.ιTotal_map]
  simp [φcol, HomologicalComplex.mkHomFromSingle_f]

set_option backward.isDefEq.respectTransparency false in
private lemma cAug_comp_incl (J'' : InjectiveResolution ((abelianPushforward.{u, u} f).obj F))
    (ψ : J''.cocomplex ⟶ ((abelianPushforward.{u, u} f).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj I.cocomplex)
    (hψ : J''.ι.f 0 ≫ ψ.f 0 = (abelianPushforward.{u, u} f).map (I.ι.f 0)) :
    cAug.{u} f F I J ≫ incl.{u} f F I J =
      J''.ι' ≫ HomologicalComplex.extendMap ψ ComplexShape.embeddingUpNat ≫ αTot.{u} f F I J := by
  apply HomologicalComplex.from_single_hom_ext
  have h1 := congrArg (fun t => HomologicalComplex.Hom.f t 0) (cAug_i.{u} f F I J)
  simp only [HomologicalComplex.comp_f] at h1
  rw [HomologicalComplex.comp_f, incl_f_zero, ← Category.assoc, h1]
  have h2 : (J''.ι' ≫ HomologicalComplex.extendMap ψ ComplexShape.embeddingUpNat ≫
      αTot.{u} f F I J).f 0 = J''.ι'.f 0 ≫
        (HomologicalComplex.extendMap ψ ComplexShape.embeddingUpNat).f 0 ≫
          StacksDraft.CartanEilenbergResolutions.totalAugmentationf J 0 := rfl
  rw [h2, InjectiveResolution.ι'_f_zero,
    HomologicalComplex.extendMap_f _ _ (i := 0) (i' := 0) rfl]
  rw [HomologicalComplex.single_map_f_self]
  simp only [StacksDraft.CartanEilenbergResolutions.totalAugmentationf, gAug, ι0,
    InjectiveResolution.cochainComplexXIso, Category.assoc,
    Iso.inv_hom_id_assoc, reassoc_of% hψ, HomologicalComplex.singleObjXSelf,
    HomologicalComplex.singleObjXIsoOfEq, eqToIso.inv, eqToIso.hom, eqToHom_refl, Category.id_comp]

end Data2

/-- Extension by zero from `ℕ` to `ℤ` commutes with homology after an additive functor. -/
private noncomputable def extendMapHomologyIso {A B : Type*} [Category A] [Category B]
    [Abelian A] [Abelian B]
    (G : A ⥤ B) [G.Additive] (n : ℕ) :
    ComplexShape.embeddingUpNat.extendFunctor A ⋙ G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      HomologicalComplex.homologyFunctor B (ComplexShape.up ℤ) (n : ℤ) ≅
    G.mapHomologicalComplex (ComplexShape.up ℕ) ⋙ HomologicalComplex.homologyFunctor B _ n :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Stacks.DerivedIndexing.mapExtendNatIso G
      ComplexShape.embeddingUpNat).symm _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Stacks.DerivedIndexing.extendHomologyNatIso
      ComplexShape.embeddingUpNat (j := n) (by simp))

section Data3

variable (I : InjectiveResolution F) (J : (pushRes f F I).CartanEilenbergResolution)
  [hJ : CochainComplex.IsStrictlyGE J.bicomplex 0]

/-- The identification `H^n(Tot Γ(J)) ≅ Hⁿ(Y, F)`. -/
private noncomputable def θIso (n : ℕ) :
    ((HomologicalComplex₂.TotalMap.mapBicomplex (abelianSections.{u, u} X ⊤)
      J.bicomplex).total (ComplexShape.up ℤ)).homology (n : ℤ) ≅
        (abelianCohomology.{u, u} Y ⊤ n).obj F :=
  haveI := isKInjective_M.{u} f F I
  haveI := isKInjective_T.{u} f F I J
  haveI := quasiIso_map_of_kInjective (abelianSections.{u, u} X ⊤) (αTot.{u} f F I J)
  haveI : IsIso (HomologicalComplex.homologyMap (((abelianSections.{u, u} X ⊤).mapHomologicalComplex
      _).map (αTot.{u} f F I J)) n) :=
    (quasiIsoAt_iff_isIso_homologyMap _ (n : ℤ)).1 inferInstance
  (HomologicalComplex.homologyFunctor _ _ (n : ℤ)).mapIso (cTot.{u} f F I J) ≪≫
    (asIso (HomologicalComplex.homologyMap (((abelianSections.{u, u} X ⊤).mapHomologicalComplex
      _).map (αTot.{u} f F I J)) n)).symm ≪≫
    (extendMapHomologyIso (abelianSections.{u, u} X ⊤) n).app
      (((abelianPushforward.{u, u} f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex) ≪≫
    (I.isoRightDerivedObj (abelianSections.{u, u} Y ⊤) n).symm

/-- The identification `H^p(Tot Γ(Z⁰_I J)) ≅ Hᵖ(X, R⁰f_* F)` along a quasi-isomorphism `χ`. -/
private noncomputable def κIso (J'' : InjectiveResolution ((abelianPushforward.{u, u} f).obj F))
    (χ : J''.cochainComplex ⟶ Jc.{u} f F I J) [QuasiIso χ] (p : ℕ) :
    ((HomologicalComplex₂.TotalMap.mapBicomplex (abelianSections.{u, u} X ⊤)
      (Acol.{u} f F I J)).total (ComplexShape.up ℤ)).homology (p : ℤ) ≅
        (abelianCohomology.{u, u} X ⊤ p).obj
          (((abelianPushforward.{u, u} f).rightDerived 0).obj F) :=
  haveI := isKInjective_Jc.{u} f F I J
  haveI := quasiIso_map_of_kInjective (abelianSections.{u, u} X ⊤) χ
  haveI : IsIso (HomologicalComplex.homologyMap (((abelianSections.{u, u} X ⊤).mapHomologicalComplex
      _).map χ) p) :=
    (quasiIsoAt_iff_isIso_homologyMap _ (p : ℤ)).1 inferInstance
  ((HomologicalComplex.homologyFunctor _ _ (p : ℤ)).mapIso
      (((abelianSections.{u, u} X ⊤).mapHomologicalComplex _).mapIso (asIso (uA.{u} f F I J)) ≪≫
        (cAcol.{u} f F I J).symm)).symm ≪≫
    (asIso (HomologicalComplex.homologyMap (((abelianSections.{u, u} X ⊤).mapHomologicalComplex
      _).map χ) p)).symm ≪≫
    (extendMapHomologyIso (abelianSections.{u, u} X ⊤) p).app J''.cocomplex ≪≫
    (J''.isoRightDerivedObj (abelianSections.{u, u} X ⊤) p).symm ≪≫
    (((abelianSections.{u, u} X ⊤).rightDerived p).mapIso
      ((abelianPushforward.{u, u} f).rightDerivedZeroIsoSelf.app F)).symm

include hJ in
/-- Under `θIso` and `κIso`, the map `φΓ` induces the edge map `abelianEdgeMap` on total
cohomology. -/
private lemma κIso_comp_abelianEdgeMap
    (J'' : InjectiveResolution ((abelianPushforward.{u, u} f).obj F))
    (ψ : J''.cocomplex ⟶ ((abelianPushforward.{u, u} f).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj I.cocomplex)
    (hψ : J''.ι.f 0 ≫ ψ.f 0 = (abelianPushforward.{u, u} f).map (I.ι.f 0))
    (χ : J''.cochainComplex ⟶ Jc.{u} f F I J) [QuasiIso χ]
    (hχ : DerivedCategory.Q.map J''.ι' ≫ DerivedCategory.Q.map χ =
      DerivedCategory.Q.map (cAug.{u} f F I J)) (p : ℕ) :
    (κIso.{u} f F I J J'' χ p).hom ≫ ((abelianCohomology.{u, u} X ⊤ p).map
        ((abelianPushforward.{u, u} f).rightDerivedZeroIsoSelf.hom.app F) ≫
          (abelianEdgeMap.{u, u} f p).app F) =
      HomologicalComplex.homologyMap (HomologicalComplex₂.total.map (φΓ.{u} f F I J)
        (ComplexShape.up ℤ)) (p : ℤ) ≫ (θIso.{u} f F I J p).hom := by
  let Γ := abelianSections.{u, u} X ⊤
  let ψz : J''.cochainComplex ⟶ pushRes.{u} f F I :=
    HomologicalComplex.extendMap ψ ComplexShape.embeddingUpNat
  have := isKInjective_M.{u} f F I
  have := isKInjective_T.{u} f F I J
  have := isKInjective_Jc.{u} f F I J
  have := quasiIso_map_of_kInjective Γ χ
  have := quasiIso_map_of_kInjective Γ (αTot.{u} f F I J)
  have hQ : DerivedCategory.Q.map (χ ≫ incl.{u} f F I J) =
      DerivedCategory.Q.map (ψz ≫ αTot.{u} f F I J) := by
    rw [← cancel_epi (DerivedCategory.Q.map J''.ι'), Functor.map_comp, ← Category.assoc, hχ,
      ← Functor.map_comp, ← Functor.map_comp, cAug_comp_incl.{u} f F I J J'' ψ hψ]
  have h2 : ((extendMapHomologyIso Γ p).app J''.cocomplex).hom ≫
      HomologicalComplex.homologyMap ((Γ.mapHomologicalComplex _).map ψ) p =
      HomologicalComplex.homologyMap ((Γ.mapHomologicalComplex _).map ψz) p ≫
        ((extendMapHomologyIso Γ p).app (((abelianPushforward.{u, u} f).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex)).hom :=
    ((extendMapHomologyIso Γ p).hom.naturality ψ).symm
  have hα : IsIso (HomologicalComplex.homologyMap
      ((Γ.mapHomologicalComplex _).map (αTot.{u} f F I J)) p) :=
    (quasiIsoAt_iff_isIso_homologyMap _ (p : ℤ)).1 inferInstance
  have hχ' : IsIso (HomologicalComplex.homologyMap ((Γ.mapHomologicalComplex _).map χ) p) :=
    (quasiIsoAt_iff_isIso_homologyMap _ (p : ℤ)).1 inferInstance
  rw [abelianEdgeMap_eq.{u, u} f F p I J'' ψ hψ]
  unfold κIso θIso
  refine hκ_alg (HomologicalComplex.homologyMap (HomologicalComplex₂.total.map (φΓ.{u} f F I J)
      (ComplexShape.up ℤ)) p)
    ((HomologicalComplex.homologyFunctor _ _ (p : ℤ)).mapIso
      ((Γ.mapHomologicalComplex _).mapIso (asIso (uA.{u} f F I J)) ≪≫ (cAcol.{u} f F I J).symm))
    ((HomologicalComplex.homologyFunctor _ _ (p : ℤ)).mapIso (cTot.{u} f F I J))
    (HomologicalComplex.homologyMap ((Γ.mapHomologicalComplex _).map (incl.{u} f F I J)) p)
    (@asIso _ _ _ _ (HomologicalComplex.homologyMap ((Γ.mapHomologicalComplex _).map χ) p) hχ')
    (HomologicalComplex.homologyMap ((Γ.mapHomologicalComplex _).map ψz) p)
    (@asIso _ _ _ _ (HomologicalComplex.homologyMap
      ((Γ.mapHomologicalComplex _).map (αTot.{u} f F I J)) p) hα) _ _ _ _ _ _ ?_ ?_ h2
  · change HomologicalComplex.homologyMap _ (p : ℤ) ≫
      HomologicalComplex.homologyMap _ (p : ℤ) ≫ HomologicalComplex.homologyMap _ (p : ℤ) = _
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
    exact congrArg (HomologicalComplex.homologyMap · (p : ℤ))
      (map_uA_comp_totalMap_eq_map_incl.{u} f F I J)
  · change HomologicalComplex.homologyMap ((Γ.mapHomologicalComplex _).map χ) (p : ℤ) ≫
        HomologicalComplex.homologyMap ((Γ.mapHomologicalComplex _).map (incl.{u} f F I J))
          (p : ℤ) =
      HomologicalComplex.homologyMap ((Γ.mapHomologicalComplex _).map ψz) (p : ℤ) ≫
        HomologicalComplex.homologyMap ((Γ.mapHomologicalComplex _).map (αTot.{u} f F I J))
          (p : ℤ)
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      ← Functor.map_comp, ← Functor.map_comp]
    exact homologyMap_map_eq_of_Q_eq Γ _ _ hQ p

end Data3

/-- **The sheaf-theoretic inputs of the Leray spectral sequence.**  For `f : Y ⟶ X` and an
abelian sheaf `F` on `Y` there are first-quadrant double complexes of abelian groups
`L = Γ(X, J)` (for `J` a Cartan-Eilenberg resolution of `f_* I`, `I` an injective resolution of
`F`) and `A = Γ(X, Z⁰_I J)` placed in column `0` (the first-direction cycles of `J`), with a
morphism `φ : A ⟶ L`, such that: the columns-homology of `A` vanishes in positive degree; `φ`
induces isomorphisms on `H^p_{II} H^0_I`; `H^p_{II} H^q_I(L) ≅ Hᵖ(X, R^q f_* F)`; the total
cohomology of `L` is `Hⁿ(Y, F)`; and, under these identifications, the map induced by `φ` on
total cohomology is the comparison map `abelianEdgeMap`. -/
private theorem exists_doubleComplexes_leray :
    ∃ (KA KL : DQ.{u}) (φ : KA ⟶ KL),
      (∀ p q : ℕ, 1 ≤ q → IsZero ((KA.obj.homology (q : ℤ)).homology (p : ℤ))) ∧
      (∀ p : ℕ, IsIso (HomologicalComplex.homologyMap
        (HomologicalComplex.homologyMap ((ObjectProperty.ι FQ).map φ) 0) (p : ℤ))) ∧
      (∀ p q : ℕ, Nonempty ((KL.obj.homology (q : ℤ)).homology (p : ℤ) ≅
        (abelianCohomology.{u, u} X ⊤ p).obj
          (((abelianPushforward.{u, u} f).rightDerived q).obj F))) ∧
      ∃ (θ : ∀ n : ℕ, (KL.obj.total (ComplexShape.up ℤ)).homology (n : ℤ) ≅
            (abelianCohomology.{u, u} Y ⊤ n).obj F)
        (κ : ∀ p : ℕ, (KA.obj.total (ComplexShape.up ℤ)).homology (p : ℤ) ≅
            (abelianCohomology.{u, u} X ⊤ p).obj
              (((abelianPushforward.{u, u} f).rightDerived 0).obj F)),
        ∀ p : ℕ, (κ p).hom ≫ ((abelianCohomology.{u, u} X ⊤ p).map
            ((abelianPushforward.{u, u} f).rightDerivedZeroIsoSelf.hom.app F) ≫
              (abelianEdgeMap.{u, u} f p).app F) =
          HomologicalComplex.homologyMap (HomologicalComplex₂.total.map
            ((ObjectProperty.ι FQ).map φ) (ComplexShape.up ℤ)) (p : ℤ) ≫ (θ p).hom := by
  let I := injectiveResolution F
  obtain ⟨J, hJ⟩ := CochainComplex.exists_cartanEilenbergResolution (pushRes.{u} f F I) 0
  let P := abelianPushforward.{u, u} f
  let J'' := injectiveResolution (P.obj F)
  have := isKInjective_Jc.{u} f F I J
  obtain ⟨χ, hχ⟩ := exists_lift_along_quasiIso J''.ι' (cAug.{u} f F I J)
  have := quasiIso_of_Q_map_comp_eq J''.ι' χ _ hχ
  have := isIso_homologyMap_φΓ.{u} f F I J
  let ψ : J''.cocomplex ⟶ (P.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex :=
    Stacks.Cohomology.SpectralLimit.descToComplex J'' _
      (fun n => P.injective_obj_of_injective (I.injective n)) (P.map (ι0 F I))
      (by change P.map _ ≫ P.map (I.cocomplex.d 0 1) = 0; rw [← P.map_comp, ι0_d, P.map_zero])
  have hψ : J''.ι.f 0 ≫ ψ.f 0 = P.map (I.ι.f 0) :=
    Stacks.Cohomology.SpectralLimit.ι_comp_descToComplex _ _ _ _ _
  exact ⟨⟨_, fq_A.{u} f F I J⟩, ⟨_, fq_L.{u} f F I J⟩, ObjectProperty.homMk (φΓ.{u} f F I J),
    isZero_homology_homology_Acol.{u} f F I J, fun p => Functor.map_isIso
      (HomologicalComplex.homologyFunctor _ _ (p : ℤ)) (HomologicalComplex.homologyMap
        (φΓ.{u} f F I J) 0), nonempty_homology_homology_iso_abelianCohomology.{u} f F I J,
    θIso.{u} f F I J,
    κIso.{u} f F I J J'' χ, κIso_comp_abelianEdgeMap.{u} f F I J J'' ψ hψ χ hχ⟩

end Sheaf

@[expose] public section

/-- **The Leray spectral sequence of a continuous map, with its bottom-row edge.**
For a continuous map `f : Y ⟶ X` and a sheaf of abelian groups `F` on `Y` there is a
first-quadrant `E₂` cohomological spectral sequence `E` with `E₂^{p,q} ≅ Hᵖ(X, R^q f_* F)`,
abutting through a finite filtration to `H^{p+q}(Y, F)`, whose bottom-row edge map
`E₂^{p,0} ⟶ E_∞^{p,0} ≅ FᵖHᵖ(Y, F) ⊆ Hᵖ(Y, F)` is, under `E₂^{p,0} ≅ Hᵖ(X, f_* F)`, the
comparison map `Stacks.Cohomology.LerayLowDegree.abelianEdgeMap`. -/
@[mmp "thm_mmp_abelian_leray_with_edge"]
public theorem exists_leraySpectralSequence_bottomRowEdge_eq_abelianEdgeMap
    {X Y : TopCat.{u}} (f : Y ⟶ X)
    (F : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}) :
    ∃ (E : E₂CohomologicalSpectralSequenceNat AddCommGrpCat.{u})
      (h : FirstQuadrantAbutment E fun n ↦ (abelianCohomology.{u, u} Y ⊤ n).obj F)
      (e : ∀ p q : ℕ, (E.page 2).X (p, q) ≅ (abelianCohomology.{u, u} X ⊤ p).obj
        (((abelianPushforward.{u, u} f).rightDerived q).obj F)),
      ∀ p : ℕ, E.edgeEpi (p, 0) 2 ≫ (h.topGradedIso p).hom ≫
          (Functor.ofOpSequence (h.ι p)).map (homOfLE (Nat.zero_le p)).op ≫ (h.topIso p).hom =
        (e p 0).hom ≫ (abelianCohomology.{u, u} X ⊤ p).map
            ((abelianPushforward.{u, u} f).rightDerivedZeroIsoSelf.hom.app F) ≫
          (abelianEdgeMap.{u, u} f p).app F := by
  obtain ⟨KA, KL, φ, hA, hφ, eL, θ, κ, hκ⟩ := exists_doubleComplexes_leray f F
  exact assembly φ hA hφ eL θ _ κ hκ

end

end MMP
