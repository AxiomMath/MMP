module

public import MMP.AlgebraicGeometry.Analytic.SchemeManifoldDescent
public import MMP.Geometry.Manifold.RelativeSNCProductGerm
import MMP.AlgebraicGeometry.Analytic.ComplexPoints.LocallyContractible
import MMP.AlgebraicGeometry.Analytic.ComplexPoints.UnderlyingSpaceProper

/-!
# Product germs along a smooth centre fibred over a curve

Let `f : Z ⟶ X` be a proper surjective morphism of complex schemes which is an isomorphism off a
closed subscheme `T ⊆ X` finite étale over a smooth curve `B`, and suppose that near
`E = f⁻¹(T)` the scheme `Z` is smooth and `E` is a relative simple normal crossing divisor over
`B`. Then at every point `x ∈ T(ℂ)` over `b ∈ B(ℂ)`, the germ of `(X^an, T^an)` is the product of
the germ of the slice `(X_b^an, {x})` with `(B^an, b)`.

On each relative dimension locus `Y_d` of the smooth open neighbourhood of `E`, the flow of a
vector field lifting `∂/∂t` and tangent to the strata of `E` trivializes a neighbourhood of `E`
over a disk around `b`. Finitely many loci meet the compact fibre `E_b`, so these products glue
over a common disk to a product structure near `E_Δ`, which descends along `f^an`.

## Main results

* `MMP.Analytic.ComplexPoints.exists_homeomorph_prod_of_isOpenEmbedding_family`: product
  structures over disks on the members of a disjoint open cover glue to one over a common disk.
* `MMP.Analytic.ComplexPoints.exists_homeomorph_prod_of_relativeSNC_of_isProper`: the product
  germ of `(X^an, T^an)` at a point of `T^an`.

## References

* [Kollár–Mori, *Birational geometry of algebraic varieties*]
-/

open CategoryTheory AlgebraicGeometry Topology
open scoped ContDiff Manifold

namespace MMP.Analytic.ComplexPoints

section Glue

variable {Zs Bs : Type*} [TopologicalSpace Zs] [TopologicalSpace Bs]

/-- **Gluing product structures over a common disk.** Let `G : Z → B` be proper on a subset
`E ⊆ Z` and `b ∈ B` have a basis of open preconnected neighbourhoods. Suppose `E` is covered by
the disjoint images of open embeddings `ρ_i : M_i → Z`, and that for each `i`, a neighbourhood of
`ρ_i⁻¹(E)` over a neighbourhood `Δ_i` of `b` is the product `U_{b,i} × Δ_i` of a neighbourhood of
`ρ_i⁻¹(E)_b` in the fibre with `Δ_i`, over `Δ_i` and preserving `E`. Then there is an open
preconnected `Δ ∋ b` over which a neighbourhood of `E_Δ` is the product of a neighbourhood
`U_b` of `E_b` in the fibre over `b` with `Δ`, over `Δ` and preserving `E`. -/
public theorem exists_homeomorph_prod_of_isOpenEmbedding_family
    {G : Zs → Bs} {E : Set Zs} (hG : IsProperMap (E.domRestrict G)) {b : Bs}
    (hloc : ∀ N ∈ 𝓝 b, ∃ Δ ⊆ N, IsOpen Δ ∧ IsPreconnected Δ ∧ b ∈ Δ)
    {ι : Type*} {M : ι → Type*} [∀ i, TopologicalSpace (M i)] {ρ : ∀ i, M i → Zs}
    (hρ : ∀ i, IsOpenEmbedding (ρ i))
    (hdisj : Pairwise fun i j ↦ Disjoint (Set.range (ρ i)) (Set.range (ρ j)))
    (hcov : E ⊆ ⋃ i, Set.range (ρ i))
    (hflow : ∀ i, ∃ Δi ∈ 𝓝 b, ∃ (Ubi Ui : Set (M i)) (hb : b ∈ Δi),
      (∃ O, IsOpen O ∧ Ubi = O ∩ (G ∘ ρ i) ⁻¹' {b}) ∧ ρ i ⁻¹' E ∩ (G ∘ ρ i) ⁻¹' {b} ⊆ Ubi ∧
      IsOpen Ui ∧ ρ i ⁻¹' E ∩ (G ∘ ρ i) ⁻¹' Δi ⊆ Ui ∧ ∃ Φ : Ubi × Δi ≃ₜ Ui,
        (∀ p, G (ρ i (Φ p)) = p.2) ∧ (∀ z, (Φ (z, ⟨b, hb⟩) : M i) = z) ∧
        ∀ p, ρ i (Φ p) ∈ E ↔ ρ i p.1 ∈ E) :
    ∃ Δ : Set Bs, IsOpen Δ ∧ IsPreconnected Δ ∧ ∃ hbΔ : b ∈ Δ, ∃ O Ub U : Set Zs,
      IsOpen O ∧ Ub = O ∩ G ⁻¹' {b} ∧ E ∩ G ⁻¹' {b} ⊆ Ub ∧ IsOpen U ∧ E ∩ G ⁻¹' Δ ⊆ U ∧
      ∃ Φ : Ub × Δ ≃ₜ U, (∀ p, G (Φ p) = p.2) ∧ (∀ z : Ub, (Φ (z, ⟨b, hbΔ⟩) : Zs) = z) ∧
        ∀ p, (Φ p : Zs) ∈ E ↔ (p.1 : Zs) ∈ E := by
  classical
  choose Δi hΔi Ubi Ui hbi hO hEb hUo hEU Φi hΦg hΦb hΦE using hflow
  choose O hOo hOeq using hO
  -- the fibre `E_b` is compact, so finitely many members of the cover meet it
  have hEbc : IsCompact (E ∩ G ⁻¹' {b}) := by
    rw [← Subtype.image_preimage_coe]
    exact (hG.isCompact_preimage isCompact_singleton).image continuous_subtype_val
  obtain ⟨T, hT⟩ := hEbc.elim_finite_subcover (fun i ↦ Set.range (ρ i))
    (fun i ↦ (hρ i).isOpen_range) (fun z hz ↦ hcov hz.1)
  -- the part of `E` off these members has closed image missing `b`
  have hRo : IsOpen (⋃ i ∈ T, Set.range (ρ i)) := isOpen_biUnion fun i _ ↦ (hρ i).isOpen_range
  let C : Set E := {z | (z : Zs) ∉ ⋃ i ∈ T, Set.range (ρ i)}
  have hCc : IsClosed C := (hRo.preimage continuous_subtype_val).isClosed_compl
  have hbC : b ∉ E.domRestrict G '' C := by
    rintro ⟨z, hzC, hzb⟩
    exact hzC (hT ⟨z.2, hzb⟩)
  have hN : (⋂ i ∈ T, Δi i) ∩ (E.domRestrict G '' C)ᶜ ∈ 𝓝 b :=
    Filter.inter_mem ((Filter.biInter_finset_mem T).2 fun i _ ↦ hΔi i)
      ((hG.isClosedMap C hCc).isOpen_compl.mem_nhds hbC)
  obtain ⟨Δ, hΔN, hΔo, hΔc, hbΔ⟩ := hloc _ hN
  have hΔsub : ∀ i ∈ T, Δ ⊆ Δi i := fun i hi t ht ↦ Set.mem_iInter₂.1 (hΔN ht).1 i hi
  have hΔR : ∀ z ∈ E, G z ∈ Δ → z ∈ ⋃ i ∈ T, Set.range (ρ i) := fun z hzE hzΔ ↦
    by_contra fun hz ↦ (hΔN hzΔ).2 ⟨⟨z, hzE⟩, hz, rfl⟩
  -- the glued product chart on the disjoint union of the slices
  let P := Σ i : T, Ubi i.1
  let inc : ∀ i : T, Δ → Δi i.1 := fun i ↦ Set.inclusion (hΔsub i.1 i.2)
  have hinc : ∀ i : T, IsOpenEmbedding (inc i) := fun i ↦
    IsOpenEmbedding.inclusion _ (hΔo.preimage continuous_subtype_val)
  let σ : (Σ i : T, Ubi i.1 × Δ) → Zs := fun q ↦
    ρ q.1.1 (Φi q.1.1 (q.2.1, inc q.1 q.2.2))
  have hσp : ∀ i : T, IsOpenEmbedding fun a : Ubi i.1 × Δ ↦ σ ⟨i, a⟩ := fun i ↦
    (hρ i.1).comp ((hUo i.1).isOpenEmbedding_subtypeVal.comp
      ((Φi i.1).isOpenEmbedding.comp (IsOpenEmbedding.id.prodMap (hinc i))))
  have hσ : IsOpenEmbedding σ := by
    refine IsOpenEmbedding.of_continuous_injective_isOpenMap
      (continuous_sigma fun i ↦ (hσp i).continuous) ?_
      (isOpenMap_sigma.2 fun i ↦ (hσp i).isOpenMap)
    rintro ⟨i, a⟩ ⟨j, a'⟩ h
    obtain rfl : i = j := by
      by_contra hij
      exact Set.disjoint_left.1 (hdisj fun h' ↦ hij (Subtype.ext h')) ⟨_, rfl⟩
        (show σ ⟨i, a⟩ ∈ Set.range (ρ j.1) from h ▸ ⟨_, rfl⟩)
    exact congrArg (Sigma.mk i) ((hσp i).injective h)
  let Φs : P × Δ → Zs := σ ∘ Homeomorph.sigmaProdDistrib
  have hΦs : IsOpenEmbedding Φs := hσ.comp Homeomorph.sigmaProdDistrib.isOpenEmbedding
  have hΦsg : ∀ q, G (Φs q) = q.2 := fun ⟨⟨i, _⟩, _⟩ ↦ hΦg i.1 _
  have hΦsE : ∀ q, Φs q ∈ E ↔ ρ q.1.1.1 q.1.2 ∈ E := fun ⟨⟨i, _⟩, _⟩ ↦ hΦE i.1 _
  -- the slice `e : P → Z`, an embedding
  let e : P → Zs := fun p ↦ Φs (p, ⟨b, hbΔ⟩)
  have he : ∀ p : P, e p = ρ p.1.1 p.2 := fun p ↦ by
    obtain ⟨i, m⟩ := p
    change ρ i.1 (Φi i.1 (m, ⟨b, hbi i.1⟩)) = _
    rw [hΦb]
  have hemb : IsEmbedding e := hΦs.isEmbedding.comp (isEmbedding_prodMkLeft _)
  let eh := hemb.toHomeomorph
  have heh : ∀ z : Set.range e, e (eh.symm z) = z := fun z ↦
    congrArg Subtype.val (eh.apply_symm_apply z)
  let Φ' : Set.range e × Δ → Zs := Φs ∘ Prod.map eh.symm id
  have hΦ' : IsOpenEmbedding Φ' :=
    hΦs.comp (eh.symm.prodCongr (Homeomorph.refl Δ)).isOpenEmbedding
  refine ⟨Δ, hΔo, hΔc, hbΔ, ⋃ i ∈ T, ρ i '' O i, Set.range e, Set.range Φ',
    isOpen_biUnion fun i _ ↦ (hρ i).isOpenMap _ (hOo i), ?_, ?_, hΦ'.isOpen_range, ?_,
    hΦ'.isEmbedding.toHomeomorph, fun p ↦ ?_, fun z ↦ ?_, fun p ↦ ?_⟩
  · ext z
    constructor
    · rintro ⟨⟨i, m⟩, rfl⟩
      have hm : (m : M i.1) ∈ O i.1 ∩ (G ∘ ρ i.1) ⁻¹' {b} := hOeq i.1 ▸ m.2
      rw [he]
      exact ⟨Set.mem_iUnion₂.2 ⟨i.1, i.2, m.1, hm.1, rfl⟩, hm.2⟩
    · rintro ⟨hz, hzb⟩
      obtain ⟨i, hi, o, ho, rfl⟩ := Set.mem_iUnion₂.1 hz
      have hm : o ∈ Ubi i := by
        rw [hOeq]
        exact ⟨ho, hzb⟩
      exact ⟨⟨⟨i, hi⟩, ⟨o, hm⟩⟩, he _⟩
  · rintro z ⟨hzE, hzb⟩
    obtain ⟨i, hi, m, rfl⟩ := Set.mem_iUnion₂.1 (hT ⟨hzE, hzb⟩)
    exact ⟨⟨⟨i, hi⟩, ⟨m, hEb i ⟨hzE, hzb⟩⟩⟩, he _⟩
  · rintro z ⟨hzE, hzΔ⟩
    obtain ⟨i, hi, m, rfl⟩ := Set.mem_iUnion₂.1 (hΔR _ hzE hzΔ)
    have hmU : m ∈ Ui i := hEU i ⟨hzE, hΔsub i hi hzΔ⟩
    set pr := (Φi i).symm ⟨m, hmU⟩ with hpr
    have hΦpr : (Φi i pr : M i) = m := by rw [hpr, Homeomorph.apply_symm_apply]
    have hpr2 : (pr.2 : Bs) ∈ Δ := by
      rw [← hΦg i pr, hΦpr]
      exact hzΔ
    let p : P := ⟨⟨i, hi⟩, pr.1⟩
    refine ⟨(eh p, ⟨pr.2, hpr2⟩), ?_⟩
    change Φs (eh.symm (eh p), ⟨pr.2, hpr2⟩) = _
    rw [Homeomorph.symm_apply_apply]
    change ρ i (Φi i (pr.1, ⟨pr.2, _⟩)) = _
    rw [← hΦpr]
  · rw [IsEmbedding.toHomeomorph_apply_coe]
    exact hΦsg _
  · rw [IsEmbedding.toHomeomorph_apply_coe]
    exact heh z
  · rw [IsEmbedding.toHomeomorph_apply_coe]
    change Φs (eh.symm p.1, p.2) ∈ E ↔ _
    rw [hΦsE, ← he, heh]

/-- If open embeddings with pairwise disjoint ranges cover `E`, each of them restricts to a closed
embedding over `E`. -/
public lemma isClosedEmbedding_restrictPreimage_of_pairwise_disjoint {ι : Type*} {M : ι → Type*}
    [∀ i, TopologicalSpace (M i)] {ρ : ∀ i, M i → Zs} (hρ : ∀ i, IsOpenEmbedding (ρ i))
    (hdisj : Pairwise fun i j ↦ Disjoint (Set.range (ρ i)) (Set.range (ρ j)))
    {E : Set Zs} (hcov : E ⊆ ⋃ i, Set.range (ρ i)) (i : ι) :
    IsClosedEmbedding (E.restrictPreimage (ρ i)) := by
  refine ⟨((hρ i).restrictPreimage E).isEmbedding, ?_⟩
  rw [Set.range_restrictPreimage, ← isOpen_compl_iff]
  have : (Subtype.val ⁻¹' Set.range (ρ i) : Set E)ᶜ =
      Subtype.val ⁻¹' ⋃ (j : ι) (_ : j ≠ i), Set.range (ρ j) := by
    ext e
    simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_iUnion, exists_prop]
    refine ⟨fun he ↦ ?_, fun ⟨j, hj, hej⟩ hei ↦ Set.disjoint_left.1 (hdisj hj) hej hei⟩
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (hcov e.2)
    exact ⟨j, fun h' ↦ he (h' ▸ hj), hj⟩
  rw [this]
  exact (isOpen_biUnion fun j _ ↦ (hρ j).isOpen_range).preimage continuous_subtype_val

end Glue

section SchemeSlice

variable {U X : Scheme.{0}} {sU : U ⟶ Spec (.of ℂ)} {sX : X ⟶ Spec (.of ℂ)}

/-- The realization of an open immersion is an open embedding. -/
private lemma isOpenEmbedding_realize_of_isOpenImmersion' (j : U ⟶ X) [IsOpenImmersion j]
    (hj : j ≫ sX = sU) : IsOpenEmbedding (realize j hj) := by
  let : X.Over (Spec (.of ℂ)) := ⟨sX⟩
  let : U.Over (Spec (.of ℂ)) := ⟨sU⟩
  have : j.IsOver (Spec (.of ℂ)) := ⟨hj⟩
  have heq : realize j hj = (homeomorphUnderlyingSpace (X := X)).symm ∘
      MMP.UnderlyingSpace.map (K := ℂ) j ∘ homeomorphUnderlyingSpace := by
    funext x
    exact homeomorphUnderlyingSpace.eq_symm_apply.mpr (MMP.UnderlyingSpace.ext rfl)
  rw [heq]
  exact (homeomorphUnderlyingSpace (X := X)).symm.isOpenEmbedding.comp
    ((MMP.UnderlyingSpace.isOpenEmbedding_map_of_isOpenImmersion (K := ℂ) j).comp
      (homeomorphUnderlyingSpace (X := U)).isOpenEmbedding)

/-- A `ℂ`-point lying over the image of an open immersion comes from its source. -/
private lemma mem_range_realize_of_isOpenImmersion (j : U ⟶ X) [IsOpenImmersion j]
    (hj : j ≫ sX = sU) (x : ComplexPoints sX) (hx : toScheme x ∈ Set.range j) :
    x ∈ Set.range (realize j hj) := by
  have H : Set.range x.hom ⊆ Set.range j := by
    rintro _ ⟨p, rfl⟩
    rw [Subsingleton.elim p default]
    exact hx
  refine ⟨⟨IsOpenImmersion.lift j x.hom H, ?_⟩, ?_⟩
  · rw [← hj, ← Category.assoc, IsOpenImmersion.lift_fac, x.hom_comp_structure]
  · ext1
    exact IsOpenImmersion.lift_fac j x.hom H

variable {Z X T B : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sB : B ⟶ Spec (.of ℂ)}

/-- The realization of a surjective morphism locally of finite type over `ℂ` is surjective. -/
public lemma surjective_realize_of_surjective (f : Z ⟶ X) [Surjective f]
    [LocallyOfFiniteType (f ≫ sX)] : Function.Surjective (realize (sX := f ≫ sX) f rfl) := by
  let : X.Over (Spec (.of ℂ)) := ⟨sX⟩
  let : Z.Over (Spec (.of ℂ)) := ⟨f ≫ sX⟩
  have : f.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  have : LocallyOfFiniteType (Z ↘ Spec (.of ℂ)) :=
    (inferInstance : LocallyOfFiniteType (f ≫ sX))
  have heq : realize (sX := f ≫ sX) f rfl = (homeomorphUnderlyingSpace (X := X)).symm ∘
      MMP.UnderlyingSpace.mapFun (K := ℂ) f ∘ homeomorphUnderlyingSpace (X := Z) := by
    funext z
    exact homeomorphUnderlyingSpace.eq_symm_apply.mpr (MMP.UnderlyingSpace.ext rfl)
  rw [heq]
  exact (homeomorphUnderlyingSpace (X := X)).symm.surjective.comp
    ((MMP.UnderlyingSpace.mapFun_surjective (K := ℂ) f).comp
      homeomorphUnderlyingSpace.surjective)

/-- Every `ℂ`-point of a scheme locally of finite type over `ℂ` has a basis of open preconnected
neighbourhoods. -/
public lemma exists_isOpen_isPreconnected_subset_of_mem_nhds [LocallyOfFiniteType sB]
    {b : ComplexPoints sB} {N : Set (ComplexPoints sB)} (hN : N ∈ 𝓝 b) :
    ∃ Δ ⊆ N, IsOpen Δ ∧ IsPreconnected Δ ∧ b ∈ Δ := by
  let : B.Over (Spec (.of ℂ)) := ⟨sB⟩
  have : LocallyOfFiniteType (B ↘ Spec (.of ℂ)) := ‹LocallyOfFiniteType sB›
  obtain ⟨D', ⟨hD', hbD', hc⟩, hD'N⟩ :=
    (((MMP.UnderlyingSpace.hasOpenContractibleBasis B).of_homeomorph
      (homeomorphUnderlyingSpace (X := B)).symm) b).mem_iff.1 hN
  have hpc : PathConnectedSpace D' := @ContractibleSpace.instPathConnectedSpace _ _ hc
  exact ⟨D', hD'N, hD', isPreconnected_iff_preconnectedSpace.2
    (@ConnectedSpace.toPreconnectedSpace _ _ (@PathConnectedSpace.connectedSpace _ _ hpc)), hbD'⟩

/-- **The product germ along a smooth centre fibred over a curve.** Let `f : Z ⟶ X` be a proper
surjective morphism of separated complex schemes of finite type, an isomorphism off a closed
subscheme `T` finite étale over a smooth curve `B` by `h : X ⟶ B`, and suppose that on an open
`W ⊇ f⁻¹(T)` smooth over `ℂ`, `f⁻¹(T)` is the support of a simple normal crossing divisor all of
whose strata are smooth over `B`. Then at a point `x ∈ T(ℂ)` over `b`, there are an open disk
`Δ ∋ b`, open `U' ∋ x` in `X^an`, `U₀ ∋ x` in the fibre `X_b^an`, and a homeomorphism
`U' ≃ₜ U₀ × Δ` over `Δ`, sending `x` to `(x, b)`, `T^an ∩ U'` to `{x} × Δ`, and the identity on
the slice. -/
public theorem exists_homeomorph_prod_of_relativeSNC_of_isProper
    [LocallyOfFiniteType sX] [IsSeparated sX] [QuasiCompact sX]
    [LocallyOfFiniteType sB] [IsSeparated sB] [QuasiCompact sB] [SmoothOfRelativeDimension 1 sB]
    (f : Z ⟶ X) [IsProper f] [Surjective f] [IsSeparated (f ≫ sX)] [QuasiCompact (f ≫ sX)]
    (iT : T ⟶ X) [IsClosedImmersion iT]
    (U : X.Opens) (hU : (U : Set X) = (Set.range iT.base)ᶜ) [IsIso (f ∣_ U)]
    (h : X ⟶ B) (hh : h ≫ sB = sX) [IsFinite (iT ≫ h)] [Etale (iT ≫ h)]
    (hE : ∃ (W : Z.Opens) (s : Finset (Mori.PrimeDivisor W)),
      f.base ⁻¹' Set.range iT.base ⊆ W ∧ Smooth (W.ι ≫ f ≫ sX) ∧
      (⋃ E ∈ s, (E.support : Set W)) = W.ι.base ⁻¹' (f.base ⁻¹' Set.range iT.base) ∧
      Mori.DivisorWithCoeffs.IsSNC (W.ι ≫ f ≫ sX) (∑ E ∈ s, Finsupp.single E (1 : ℤ)) ∧
      ∀ J ⊆ s, Smooth ((⨆ E ∈ J, E.idealSheaf).subschemeι ≫ W.ι ≫ f ≫ h))
    (b : ComplexPoints sB) (x : ComplexPoints sX)
    (hxT : x ∈ Set.range (realize iT rfl)) (hxb : realize h hh x = b) :
    ∃ (Δ : Set (ComplexPoints sB)) (_ : IsOpen Δ) (hbΔ : b ∈ Δ)
      (U' : Set (ComplexPoints sX)) (U₀ : Set (realize h hh ⁻¹' {b})) (_ : IsOpen U')
      (_ : IsOpen U₀) (hxU : x ∈ U') (hx₀ : (⟨x, hxb⟩ : realize h hh ⁻¹' {b}) ∈ U₀)
      (φ : U' ≃ₜ U₀ × Δ),
      φ ⟨x, hxU⟩ = (⟨⟨x, hxb⟩, hx₀⟩, ⟨b, hbΔ⟩) ∧
      (∀ y : U', ((φ y).2 : ComplexPoints sB) = realize h hh y) ∧
      (∀ y : U', (y : ComplexPoints sX) ∈ Set.range (realize iT rfl) ↔
        (φ y).1 = ⟨⟨x, hxb⟩, hx₀⟩) ∧
      ∀ (y : U') (hy : realize h hh y = b),
        ((φ y).1 : realize h hh ⁻¹' {b}) = ⟨y, hy⟩ := by
  classical
  obtain ⟨W, s, hEW, hWs, hEs, hsnc, hstr⟩ := hE
  have : Smooth sB := SmoothOfRelativeDimension.smooth 1 sB
  set τ : Set (ComplexPoints sX) := Set.range (realize (sX := iT ≫ sX) iT rfl) with hτ
  let π := realize (sX := f ≫ sX) f rfl
  let hB := realize h hh
  let G : ComplexPoints (f ≫ sX) → ComplexPoints sB := hB ∘ π
  let Eset : Set (ComplexPoints (f ≫ sX)) := π ⁻¹' τ
  have hπp := (isSeparatedMap_and_isProperMap_realize (sX := f ≫ sX) (sS := sX) f rfl).2
  have hTp := (isSeparatedMap_and_isProperMap_realize (sX := iT ≫ sX) (sS := sX) iT rfl).2
  have hτc : IsClosed τ := hTp.isClosedMap.isClosed_range
  have hEc : IsClosed Eset := hτc.preimage hπp.continuous
  -- `G` is proper on `E`
  have hGE : IsProperMap (Eset.domRestrict G) := by
    have H := isProperMap_restrict_realize_preimage_range f iT h hh
    rwa [realize_comp f rfl h hh] at H
  -- the relative dimension loci of `W` and their realizations in `Z^an`
  let sW := W.ι ≫ f ≫ sX
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  have : IsLocallyNoetherian W := isLocallyNoetherian_of_isOpenImmersion W.ι
  let Y : ℕ → W.toScheme.Opens := fun d ↦ relativeDimensionLocus sW d
  let M : ℕ → Type := fun d ↦ ComplexPoints ((Y d).ι ≫ sW)
  have hρeq : ∀ d, ((Y d).ι ≫ W.ι) ≫ f ≫ sX = (Y d).ι ≫ sW := fun d ↦ by
    simp only [sW, Category.assoc]
  let ρ : ∀ d, M d → ComplexPoints (f ≫ sX) := fun d ↦
    realize (sX := (Y d).ι ≫ sW) (sY := f ≫ sX) ((Y d).ι ≫ W.ι) (hρeq d)
  have hρ : ∀ d, IsOpenEmbedding (ρ d) := fun d ↦
    isOpenEmbedding_realize_of_isOpenImmersion' _ _
  have hρpt : ∀ d (m : M d), toScheme (ρ d m) = W.ι ((Y d).ι (toScheme m)) := fun _ _ ↦ rfl
  have hdisj : Pairwise fun d d' ↦ Disjoint (Set.range (ρ d)) (Set.range (ρ d')) := by
    intro d d' hdd
    rw [Set.disjoint_left]
    rintro _ ⟨m, rfl⟩ ⟨m', hm'⟩
    have h1 := congrArg toScheme hm'
    rw [hρpt, hρpt] at h1
    have h2 := W.ι.isOpenEmbedding.injective h1
    have hm1 : (Y d').ι (toScheme m') ∈ Y d' := (Scheme.Opens.range_ι (Y d')).le ⟨_, rfl⟩
    have hm2 : (Y d).ι (toScheme m) ∈ Y d := (Scheme.Opens.range_ι (Y d)).le ⟨_, rfl⟩
    rw [h2] at hm1
    exact hdd (eq_of_mem_relativeDimensionLocus hm2 hm1)
  have hmemE : ∀ z, z ∈ Eset ↔ f (toScheme z) ∈ Set.range iT := fun z ↦
    mem_range_realize_iff_of_isClosedImmersion iT (π z)
  have hcov : Eset ⊆ ⋃ d, Set.range (ρ d) := by
    intro z hz
    have hzW : toScheme z ∈ W := hEW ((hmemE z).1 hz)
    obtain ⟨d, hd⟩ := exists_mem_relativeDimensionLocus (sX := sW) ⟨toScheme z, hzW⟩
    obtain ⟨q, hq⟩ : (⟨toScheme z, hzW⟩ : W) ∈ Set.range (Y d).ι := by
      rwa [Scheme.Opens.range_ι]
    refine Set.mem_iUnion.2 ⟨d, mem_range_realize_of_isOpenImmersion _ _ z ⟨q, ?_⟩⟩
    rw [Scheme.Hom.comp_apply, hq, Scheme.Opens.ι_apply]
  have : Smooth sW := hWs
  have : QuasiCompact sW := inferInstanceAs (QuasiCompact (W.ι ≫ f ≫ sX))
  have : IsSeparated sW := inferInstanceAs (IsSeparated (W.ι ≫ f ≫ sX))
  have hg : (W.ι ≫ f ≫ h) ≫ sB = sW := by simp only [sW, Category.assoc, hh]
  -- on each locus, the flow trivializes a neighbourhood of `E` over a disk
  have hflow : ∀ d, ∃ Δi ∈ 𝓝 b, ∃ (Ubi Ui : Set (M d)) (hb : b ∈ Δi),
      (∃ O, IsOpen O ∧ Ubi = O ∩ (G ∘ ρ d) ⁻¹' {b}) ∧ ρ d ⁻¹' Eset ∩ (G ∘ ρ d) ⁻¹' {b} ⊆ Ubi ∧
      IsOpen Ui ∧ ρ d ⁻¹' Eset ∩ (G ∘ ρ d) ⁻¹' Δi ⊆ Ui ∧ ∃ Φ : Ubi × Δi ≃ₜ Ui,
        (∀ p, G (ρ d (Φ p)) = p.2) ∧ (∀ z, (Φ (z, ⟨b, hb⟩) : M d) = z) ∧
        ∀ p, ρ d (Φ p) ∈ Eset ↔ ρ d p.1 ∈ Eset := by
    intro d
    obtain ⟨pick, hcmd, hD, hsub, hstrata⟩ :=
      exists_pick_relativeSNC_relativeDimensionLocus (sX := sW) d (W.ι ≫ f ≫ h) hg s hsnc hstr
    let := etaleChartedSpaceOf ((Y d).ι ≫ sW) d (EuclideanSpace.equiv (Fin d) ℂ).symm pick
    have := isManifold_etaleChartedSpaceOf ((Y d).ι ≫ sW) d
      (EuclideanSpace.equiv (Fin d) ℂ).symm pick ∞
    have : T2Space (M d) := t2Space
    have : SecondCountableTopology (M d) := secondCountableTopology d
    let D : s → Set (M d) := fun E ↦ {y | (Y d).ι (toScheme y) ∈ E.1.support}
    let gY := realize (sX := (Y d).ι ≫ sW) (sY := sB) ((Y d).ι ≫ (W.ι ≫ f ≫ h))
      (by rw [Category.assoc, hg])
    have hgY : gY = G ∘ ρ d := by
      funext y
      ext1
      simp only [gY, G, π, hB, ρ, Function.comp_apply, realize_hom, Category.assoc]
    have hDE : (⋃ i, D i) = ρ d ⁻¹' Eset := by
      ext y
      rw [Set.mem_preimage, hmemE, Set.mem_iUnion]
      have := congrArg (fun S : Set W ↦ (Y d).ι (toScheme y) ∈ S) hEs
      simp only [Set.mem_iUnion, Set.mem_preimage, eq_iff_iff, exists_prop] at this
      rw [hρpt, ← this]
      exact ⟨fun ⟨i, hi⟩ ↦ ⟨i.1, i.2, hi⟩, fun ⟨E, hE, hi⟩ ↦ ⟨⟨E, hE⟩, hi⟩⟩
    have hEcl : IsClosed (⋃ i, D i) := by
      rw [hDE]
      exact hEc.preimage (hρ d).continuous
    have hprop : IsProperMap fun y : (⋃ i, D i : Set (M d)) ↦ gY y := by
      have H := (hGE.comp (isClosedEmbedding_restrictPreimage_of_pairwise_disjoint hρ hdisj hcov
        d).isProperMap).comp (Homeomorph.setCongr hDE).isProperMap
      convert H using 1
      funext y
      exact congrFun hgY y.1
    obtain ⟨ψ, -, -, r, -, -, -, Ub, Ui, hb, -, ⟨O, hO, hUbO⟩, hEb, hUo, -, hEU, Φ, hΦg, hΦb,
        hΦD⟩ :=
      MMP.Analytic.exists_homeomorph_prod_of_relativeSNC ((hcmd ∞).mdifferentiable (by simp))
        (hD ∞) hEcl hprop ⟨Set.univ, isOpen_univ, Set.subset_univ _, fun y _ ↦ hsub y⟩
        (fun y _ ↦ hstrata y) b Filter.univ_mem
    rw [hDE] at hEb hEU
    change ρ d ⁻¹' Eset ∩ gY ⁻¹' {b} ⊆ Ub at hEb
    change ρ d ⁻¹' Eset ∩ gY ⁻¹' (ψ.source ∩ ψ ⁻¹' Metric.ball (ψ b) r) ⊆ Ui at hEU
    change Ub = O ∩ gY ⁻¹' {b} at hUbO
    change ∀ p, gY (Φ p) = p.2 at hΦg
    rw [hgY] at hEb hEU hUbO hΦg
    refine ⟨_, (ψ.isOpen_inter_preimage Metric.isOpen_ball).mem_nhds hb, Ub, Ui, hb,
      ⟨O, hO, hUbO⟩, hEb, hUo, hEU, Φ, hΦg, hΦb, fun p ↦ ?_⟩
    rw [← Set.mem_preimage (f := ρ d), ← Set.mem_preimage (f := ρ d), ← hDE]
    simp only [Set.mem_iUnion]
    exact exists_congr fun i ↦ hΦD i p
  obtain ⟨Δ, hΔo, hΔc, hbΔ, O, Ub, Uz, hOo, hUb, hEb, hUo, hEU, Φ, hΦg, hΦb, hΦE⟩ :=
    exists_homeomorph_prod_of_isOpenEmbedding_family hGE
      (fun _ ↦ exists_isOpen_isPreconnected_subset_of_mem_nhds) hρ hdisj hcov hflow
  -- `T^an → B^an` is a covering map
  have hTe : IsClosedEmbedding (realize (sX := iT ≫ sX) iT rfl) :=
    IsClosedEmbedding.of_continuous_injective_isClosedMap hTp.continuous
      (fun t t' htt ↦ ComplexPoints.ext
        ((cancel_mono iT).1 (congrArg (fun y : ComplexPoints sX ↦ y.hom) htt)))
      hTp.isClosedMap
  have hcovτ : IsCoveringMap (fun t : τ ↦ hB t) := by
    have hc := isCoveringMap_realize_of_isFinite_of_etale (sT := iT ≫ sX) (sB := sB) (iT ≫ h)
      (by rw [Category.assoc, hh])
    let e := hTe.isEmbedding.toHomeomorph
    have : (fun t : τ ↦ hB t) =
        realize (sX := iT ≫ sX) (iT ≫ h) (by rw [Category.assoc, hh]) ∘ e.symm := by
      funext t
      obtain ⟨t', rfl⟩ := e.surjective t
      rw [Function.comp_apply, e.symm_apply_apply, IsEmbedding.toHomeomorph_apply_coe]
      exact (congrFun (realize_comp iT rfl h hh) t').symm
    rw [this]
    exact hc.comp_homeomorph e.symm
  -- `f^an` is surjective, and injective off `E`
  have hπs : Function.Surjective π := surjective_realize_of_surjective f
  have hinj : ∀ z z', π z ∉ τ → π z = π z' → z = z' := fun z z' hz hzz ↦ by
    refine eq_of_realize_eq_of_isIso_restrict f U ?_ hzz
    rw [← SetLike.mem_coe, hU]
    exact fun hmem ↦ hz ((mem_range_realize_iff_of_isClosedImmersion iT _).2 hmem)
  exact ⟨Δ, hΔo, hbΔ, exists_homeomorph_prod_of_isProperMap hπp hπs hinj hcovτ hxT hxb hΔc hbΔ
    hOo hUb hEb hUo hEU Φ hΦg hΦb hΦE⟩

end SchemeSlice

end MMP.Analytic.ComplexPoints
