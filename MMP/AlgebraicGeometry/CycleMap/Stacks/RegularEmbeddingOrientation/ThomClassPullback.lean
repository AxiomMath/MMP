module

public import MMP.AlgebraicTopology.ThomClass.Natural
public import MMP.AlgebraicTopology.ThomClass.Isomorphism.Basic
public import MMP.AlgebraicTopology.ThomClass.OfRank

/-!
# Thom classes along fibrewise isomorphisms, and maps of pairs in relative cohomology

Lemmas on complex topological vector bundles (Fulton, §19.2): a Thom class moved to degree
`2r`, `r = dim F`, satisfies the Thom condition of rank `r` and is unique there; Thom classes
pull back to Thom classes along bundle maps that are complex linear isomorphisms on the fibres;
and the functoriality of `relativeSingularCohomology.map` applied to elements.

## Main results

* `MMP.IsThomClass.isThomClassOfRank`: a Thom class in degree `2 * dim F` satisfies the Thom
  condition of rank `dim F`.
* `MMP.ThomClass.IsThomClassOfRank.eq`: uniqueness of the Thom class of rank `dim F`.
* `MMP.ThomClass.IsThomClassOfRank.map`: Thom classes pull back along fibrewise isomorphisms.
* `MMP.relativeSingularCohomology.map_comp_apply'`,
  `MMP.relativeSingularCohomology.map_congr_apply`,
  `MMP.relativeSingularCohomology.map_eqToHom_apply`: functoriality of the map of pairs on
  elements.
* `Bundle.TotalSpace.mk_cast_snd`: transporting a point of the total space to an equal base point
  and back recovers the point.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Set Bundle

namespace MMP

namespace ThomClass

open SingularChain SingularCochain

section rank

variable {R : Type u} [CommRing R] {B : Type u} [TopologicalSpace B]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  (E : B → Type u) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [_root_.VectorBundle ℂ F E]

variable {F E}

/-- A Thom class, moved to degree `2r` for `r = dim F`, satisfies the Thom condition of rank
`r`. -/
lemma _root_.MMP.IsThomClass.isThomClassOfRank {r : ℕ} (hr : Module.finrank ℂ F = r)
    {u : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (TotalSpace F E))
      (range (zeroSection F E)) (2 * Module.finrank ℂ F : ℕ)} (hu : IsThomClass F E u)
    (h : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (TotalSpace F E))
      (range (zeroSection F E)) (2 * Module.finrank ℂ F : ℕ) =
      cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (TotalSpace F E))
        (range (zeroSection F E)) (2 * r : ℕ)) :
    IsThomClassOfRank F E r ((eqToHom h).hom u) := by
  subst hr
  rwa [eqToHom_refl]

/-- **Uniqueness of the Thom class**, in degree `2r` for `r = dim F`. -/
lemma IsThomClassOfRank.eq {r : ℕ} (hr : Module.finrank ℂ F = r)
    {u u' : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (TotalSpace F E))
      (range (zeroSection F E)) (2 * r : ℕ)}
    (hu : IsThomClassOfRank F E r u) (hu' : IsThomClassOfRank F E r u') : u = u' := by
  subst hr
  exact (existsUnique_isThomClass (R := R) F E).unique hu hu'

variable {B' : Type u} [TopologicalSpace B'] {F' : Type*} [NormedAddCommGroup F']
  [NormedSpace ℂ F'] [FiniteDimensional ℂ F'] {E' : B' → Type u} [∀ x, AddCommGroup (E' x)]
  [∀ x, Module ℂ (E' x)] [∀ x, TopologicalSpace (E' x)] [TopologicalSpace (TotalSpace F' E')]
  [FiberBundle F' E'] [_root_.VectorBundle ℂ F' E']
  {Φ : TopCat.of (TotalSpace F' E') ⟶ TopCat.of (TotalSpace F E)} {g : B' → B}
  {φ : ∀ x, E' x ≃L[ℂ] E (g x)}

/-- A bundle map which is injective on the fibres maps the complement of the zero section into the
complement of the zero section. -/
lemma compl_zeroSection_subset_preimage (hΦ : ∀ x v, Φ ⟨x, v⟩ = ⟨g x, φ x v⟩) :
    (range (zeroSection F' E'))ᶜ ⊆ Φ ⁻¹' (range (zeroSection F E))ᶜ := by
  rintro ⟨x, v⟩ hp ⟨y, hy⟩
  refine hp ⟨x, ?_⟩
  change zeroSection F E y = Φ ⟨x, v⟩ at hy
  rw [hΦ] at hy
  have h1 : y = g x := congrArg TotalSpace.proj hy
  subst h1
  have h2 : (0 : E (g x)) = φ x v := (TotalSpace.mk_inj).1 hy
  have h3 : v = 0 := (φ x).map_eq_zero_iff.1 h2.symm
  rw [zeroSection, h3]

/-- **Thom classes pull back along fibrewise isomorphisms**: if `Φ : E' → E` covers `g : B' → B`
and is a complex linear isomorphism `E'_x ≅ E_{g x}` on each fibre, then `Φ^* u` satisfies the
Thom condition of rank `r` when `u` does. -/
theorem IsThomClassOfRank.map {r : ℕ} (hΦ : ∀ x v, Φ ⟨x, v⟩ = ⟨g x, φ x v⟩)
    {u : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (TotalSpace F E))
      (range (zeroSection F E)) (2 * r : ℕ)} (hu : IsThomClassOfRank F E r u) :
    IsThomClassOfRank F' E' r ((relativeSingularCohomology.map R (ModuleCat.of R R) Φ
      (compl_zeroSection_subset_preimage hΦ) _).hom u) := by
  intro x' ψ v hv
  rw [relativeSingularCohomologyEquiv_map]
  have hσ : Φ.hom.comp (fibreSimplex F' x' ψ v) = fibreSimplex F (g x') (ψ.trans (φ x')) v :=
    ContinuousMap.ext fun _ ↦ hΦ _ _
  have hc' : ∀ θ ∈ relCoboundaries R (range (zeroSection F E))ᶜ (2 * r),
      eval θ (Finsupp.mapDomain Φ.hom.comp (Finsupp.single (fibreSimplex F' x' ψ v) 1)) = 0 := by
    rw [Finsupp.mapDomain_single, hσ]
    exact eval_single_eq_zero_of_mem_relCoboundaries _
      (fibreSimplex_notMem_range_zeroSection F (g x') _ hv)
  refine (relEval_relCohomologyMap Φ _ _ _ hc' _).trans ?_
  exact (LinearMap.congr_fun (relEval_congr (by rw [Finsupp.mapDomain_single, hσ]) hc' _) _).trans
    (hu (g x') _ v hv)

end rank

end ThomClass

namespace relativeSingularCohomology

variable (R : Type u) [CommRing R]

/-- The map induced by a composite of maps of pairs is the composite of the induced maps,
applied to an element. -/
lemma map_comp_apply' {Y'' Y' Y : TopCat.{u}} {g : Y'' ⟶ Y'} {f : Y' ⟶ Y} {A'' : Set Y''}
    {A' : Set Y'} {A : Set Y} (hg : A'' ⊆ g ⁻¹' A') (hf : A' ⊆ f ⁻¹' A)
    (h : A'' ⊆ (g ≫ f) ⁻¹' A) (j : ℤ) (x : relativeSingularCohomology R (ModuleCat.of R R) Y A j) :
    (map R (ModuleCat.of R R) (g ≫ f) h j).hom x =
      (map R (ModuleCat.of R R) g hg j).hom ((map R (ModuleCat.of R R) f hf j).hom x) := by
  rw [map_comp R (ModuleCat.of R R) g f hg hf j]
  rfl

/-- Equal maps of pairs induce equal maps on relative cohomology, applied to an element. -/
lemma map_congr_apply {Y' Y : TopCat.{u}} {f g : Y' ⟶ Y} {A' : Set Y'} {A : Set Y} (e : f = g)
    (hf : A' ⊆ f ⁻¹' A) (hg : A' ⊆ g ⁻¹' A) (j : ℤ)
    (x : relativeSingularCohomology R (ModuleCat.of R R) Y A j) :
    (map R (ModuleCat.of R R) f hf j).hom x = (map R (ModuleCat.of R R) g hg j).hom x := by
  subst e
  rfl

/-- Moving a class to an equal degree commutes with the map of a map of pairs. -/
lemma map_eqToHom_apply {Y' Y : TopCat.{u}} (f : Y' ⟶ Y) {A' : Set Y'} {A : Set Y}
    (h : A' ⊆ f ⁻¹' A) {n m : ℕ} (hnm : n = m)
    (e : relativeSingularCohomology R (ModuleCat.of R R) Y A n =
      relativeSingularCohomology R (ModuleCat.of R R) Y A m)
    (e' : relativeSingularCohomology R (ModuleCat.of R R) Y' A' n =
      relativeSingularCohomology R (ModuleCat.of R R) Y' A' m)
    (x : relativeSingularCohomology R (ModuleCat.of R R) Y A n) :
    (eqToHom e').hom ((map R (ModuleCat.of R R) f h n).hom x) =
      (map R (ModuleCat.of R R) f h m).hom ((eqToHom e).hom x) := by
  subst hnm
  simp only [eqToHom_refl, ModuleCat.id_apply]

end relativeSingularCohomology

/-- The point `⟨b, p.2⟩` of the total space, with the fibre coordinate transported along
`p.proj = b`, is `p`. -/
lemma _root_.Bundle.TotalSpace.mk_cast_snd {B : Type*} {F : Type*} {E : B → Type*}
    (p : TotalSpace F E) {b : B} (h : p.proj = b) :
    (⟨b, cast (congrArg E h) p.2⟩ : TotalSpace F E) = p := by
  subst h
  rfl

end MMP
