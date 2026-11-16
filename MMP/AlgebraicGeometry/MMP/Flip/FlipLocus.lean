module

public import MMP.AlgebraicGeometry.MMP.Models
public import MMP.AlgebraicGeometry.Singularities.Deminormal.Basic
public import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.ValuativeLineBundle

/-!
# The locus where a flip is not an isomorphism

Let `f : X → Y` be a `(K + D)`-flipping contraction and `f⁺ : X⁺ → Y` a `(K + D)`-flip of `f`.
The set `W = f(Ex(f)) ∪ f⁺(Ex(f⁺))` is closed, `f` and `f⁺` are isomorphisms over `Y ∖ W`, and
`f⁻¹(W)`, `(f⁺)⁻¹(W)` and `W` have codimension at least two (KM, proof of Prop. 3.37).

## Main results

* `MMP.Positivity.IsFlip.exists_isClosed_image_exceptionalSet`
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Positivity

open MMP.Mori

section Helpers

open Order

variable {X Y : Scheme.{u}}

/-- If `Ex(f)` has codimension at least two, every point of `Ex(f)` has coheight at least two. -/
theorem two_le_coheight_of_mem_exceptionalSet {f : X ⟶ Y}
    (h2 : 2 ≤ closedsCodimension (exceptionalSet f)) {x : X} (hx : x ∈ exceptionalSet f) :
    2 ≤ coheight x := by
  have hsub : ((irreducibleSetEquivPoints (α := X)).symm x : Set X) ⊆ exceptionalSet f :=
    (isClosed_exceptionalSet f).closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hx)
  have := le_closedsCodimension_iff.mp h2 _ hsub
  rwa [codimension_eq_coheight, Order.coheight_orderIso] at this

/-- A dominant morphism of irreducible schemes maps the generic point to the generic point. -/
theorem map_genericPoint_eq_of_isDominant [IrreducibleSpace X] [IrreducibleSpace Y] (f : X ⟶ Y)
    [IsDominant f] : f (genericPoint X) = genericPoint Y := by
  refine ((genericPoint_spec Y).eq ?_).symm
  change closure {f (genericPoint X)} = Set.univ
  refine Set.eq_univ_of_univ_subset ?_
  rw [← f.denseRange.closure_range]
  refine closure_minimal ?_ isClosed_closure
  rintro _ ⟨x, rfl⟩
  exact ((genericPoint_specializes x).map f.continuous).mem_closure

/-- **A proper birational morphism onto a normal scheme is an isomorphism over the points of
codimension at most one**, provided its exceptional set has codimension at least two. -/
theorem mem_biregularLocus_of_coheight_le_one [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (f : X ⟶ Y) [IsDominant f] [UniversallyClosed f]
    [LocallyOfFiniteType f] (hf : Function.Bijective (functionFieldMap f))
    (h2 : 2 ≤ closedsCodimension (exceptionalSet f)) {y : Y} (hy : coheight y ≤ 1) :
    y ∈ biregularLocus f := by
  by_contra hyV
  rcases lt_or_eq_of_le hy with h0 | h1
  · have hy0 : coheight y = 0 := Order.lt_one_iff.mp h0
    have hmax : IsMax y := Order.coheight_eq_zero.mp hy0
    have hgy : y = genericPoint Y :=
      Specializes.antisymm (hmax (genericPoint_specializes y)) (genericPoint_specializes y) |>.eq
    have hx : genericPoint X ∈ exceptionalSet f := by
      rw [mem_exceptionalSet, map_genericPoint_eq_of_isDominant, ← hgy]
      exact hyV
    have h2x := two_le_coheight_of_mem_exceptionalSet h2 hx
    have hmaxX : IsMax (genericPoint X) := fun z _ ↦ genericPoint_specializes z
    rw [Order.coheight_eq_zero.mpr hmaxX] at h2x
    exact absurd h2x (by decide)
  · obtain ⟨x', hx', hc, -, -⟩ :=
      MMP.Intersection.exists_preimage_of_coheight_eq_one f hf h1
    have hxE : x' ∈ exceptionalSet f := by
      rw [mem_exceptionalSet, hx']
      exact hyV
    have h2x := two_le_coheight_of_mem_exceptionalSet h2 hxE
    rw [hc] at h2x
    exact absurd h2x (by decide)

/-- For a surjective morphism, the image of the exceptional set is the complement of the
biregular locus. -/
theorem image_exceptionalSet_eq (f : X ⟶ Y) (hs : Function.Surjective f) :
    f '' (exceptionalSet f : Set X) = (biregularLocus f : Set Y)ᶜ := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact mem_exceptionalSet.mp hx
  · intro hy
    obtain ⟨x, rfl⟩ := hs y
    exact ⟨x, mem_exceptionalSet.mpr hy, rfl⟩

/-- Over the biregular locus, a morphism preserves the coheight of points. -/
theorem coheight_map_of_mem_biregularLocus (f : X ⟶ Y) {x : X} (hx : f x ∈ biregularLocus f) :
    coheight (f x) = coheight x := by
  set V := biregularLocus f
  haveI : IsIso (f ∣_ V) := isBiregular_biregularLocus f
  let p : (f ⁻¹ᵁ V).toScheme := ⟨x, hx⟩
  have e1 : coheight ((f ⁻¹ᵁ V).ι p) = coheight p :=
    Topology.IsOpenEmbedding.coheight_eq _ (f ⁻¹ᵁ V).ι.isOpenEmbedding
  have e2 : coheight ((f ∣_ V) p) = coheight p :=
    Topology.IsOpenEmbedding.coheight_eq _ (f ∣_ V).isOpenEmbedding
  have e3 : coheight (V.ι ((f ∣_ V) p)) = coheight ((f ∣_ V) p) :=
    Topology.IsOpenEmbedding.coheight_eq _ V.ι.isOpenEmbedding
  have h : V.ι ((f ∣_ V) p) = f x := by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
    rfl
  have h' : (f ⁻¹ᵁ V).ι p = x := rfl
  rw [← h, e3, e2, ← e1, h']

end Helpers

variable {k : Type u} [Field k] {X Y X' : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  {sY : Y ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)}
  [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']

/-- **The flipping locus** (KM, proof of Prop. 3.37). Let `f : X → Y` be a `(K + D)`-flipping
contraction and `f⁺ : X⁺ → Y` a `(K + D)`-flip of `f`, and `W = f(Ex(f)) ∪ f⁺(Ex(f⁺))`. Then `W` is
closed, `f` and `f⁺` are isomorphisms over `Y ∖ W`, and `f⁻¹(W) ⊆ X`, `(f⁺)⁻¹(W) ⊆ X⁺` and `W ⊆ Y`
have codimension at least two. -/
@[mmp "lem_km3c_flip_exceptional_locus_codim_two"]
theorem IsFlip.exists_isClosed_image_exceptionalSet {K : Divisor X} {D : QDivisor X}
    {f : X ⟶ Y} {fp : X' ⟶ Y} (h : IsFlip sX sY sX' K D f fp) :
    ∃ hW : IsClosed (f '' (exceptionalSet f : Set X) ∪ fp '' (exceptionalSet fp : Set X')),
      IsBiregular f ⟨_, hW.isOpen_compl⟩ ∧ IsBiregular fp ⟨_, hW.isOpen_compl⟩ ∧
      2 ≤ closedsCodimension ⟨f ⁻¹' _, hW.preimage f.continuous⟩ ∧
      2 ≤ closedsCodimension ⟨fp ⁻¹' _, hW.preimage fp.continuous⟩ ∧
      2 ≤ closedsCodimension ⟨_, hW⟩ := by
  obtain ⟨hFC, hX', -, hpProper, hpBir, -, -, hp2⟩ := h
  obtain ⟨hXv, hYv, -, -, -, hfProper, hfBir, hf2, -⟩ := hFC
  haveI : IsIntegral X := hXv.1.toIsIntegral
  haveI : IsIntegral X' := hX'.1.toIsIntegral
  haveI : IsIntegral Y := hYv.1.toIsIntegral
  haveI : IsNormal Y := hYv.2
  haveI : LocallyOfFiniteType sY := hYv.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  haveI := hfProper
  haveI := hpProper
  haveI : IsDominant f := hfBir.isDominant
  haveI : IsDominant fp := hpBir.isDominant
  have hfb := hfBir.functionFieldMap_bijective
  have hpb := hpBir.functionFieldMap_bijective
  set U : Y.Opens := biregularLocus f ⊓ biregularLocus fp with hU
  have hWeq : f '' (exceptionalSet f : Set X) ∪ fp '' (exceptionalSet fp : Set X') =
      (U : Set Y)ᶜ := by
    rw [image_exceptionalSet_eq f f.surjective, image_exceptionalSet_eq fp fp.surjective, hU,
      TopologicalSpace.Opens.coe_inf, Set.compl_inter]
  have hW : IsClosed (f '' (exceptionalSet f : Set X) ∪ fp '' (exceptionalSet fp : Set X')) := by
    rw [hWeq]; exact U.isOpen.isClosed_compl
  have hUf : ∀ y : Y, Order.coheight y ≤ 1 → y ∈ U := fun y hy ↦
    ⟨mem_biregularLocus_of_coheight_le_one f hfb hf2 hy,
      mem_biregularLocus_of_coheight_le_one fp hpb hp2 hy⟩
  have hpre : ∀ {Z : Scheme.{u}} (g : Z ⟶ Y), 2 ≤ closedsCodimension (exceptionalSet g) →
      (∀ z : Z, Order.coheight z ≤ 1 → g z ∈ U) →
      2 ≤ closedsCodimension (⟨g ⁻¹' (f '' (exceptionalSet f : Set X) ∪
        fp '' (exceptionalSet fp : Set X')), hW.preimage g.continuous⟩ : Closeds Z) := by
    intro Z g _ hg
    have e : (⟨g ⁻¹' (f '' (exceptionalSet f : Set X) ∪ fp '' (exceptionalSet fp : Set X')),
        hW.preimage g.continuous⟩ : Closeds Z) =
        ⟨(g ⁻¹ᵁ U : Set Z)ᶜ, (g ⁻¹ᵁ U).isOpen.isClosed_compl⟩ :=
      Closeds.ext (by simp only [hWeq]; rfl)
    rw [e]
    exact MMP.Flips.two_le_closedsCodimension_compl (g ⁻¹ᵁ U).isOpen hg
  have hcod : ∀ {Z : Scheme.{u}} (g : Z ⟶ Y), 2 ≤ closedsCodimension (exceptionalSet g) →
      ∀ z : Z, Order.coheight z ≤ 1 → g z ∈ U := by
    intro Z g hg2 z hz
    have hgz : g z ∈ biregularLocus g := by
      by_contra hn
      have := two_le_coheight_of_mem_exceptionalSet hg2 (mem_exceptionalSet.mpr hn)
      exact absurd (this.trans hz) (by decide)
    exact hUf _ ((coheight_map_of_mem_biregularLocus g hgz).trans_le hz)
  refine ⟨hW, ?_, ?_, hpre f hf2 (hcod f hf2), hpre fp hp2 (hcod fp hp2), ?_⟩
  · rw [isBiregular_iff_le_biregularLocus]
    intro y hy
    have hy' : y ∉ f '' (exceptionalSet f : Set X) ∪ fp '' (exceptionalSet fp : Set X') := hy
    rw [hWeq] at hy'
    exact (not_not.mp hy').1
  · rw [isBiregular_iff_le_biregularLocus]
    intro y hy
    have hy' : y ∉ f '' (exceptionalSet f : Set X) ∪ fp '' (exceptionalSet fp : Set X') := hy
    rw [hWeq] at hy'
    exact (not_not.mp hy').2
  · have e : (⟨_, hW⟩ : Closeds Y) = ⟨(U : Set Y)ᶜ, U.isOpen.isClosed_compl⟩ := Closeds.ext hWeq
    rw [e]
    exact MMP.Flips.two_le_closedsCodimension_compl U.isOpen hUf

end MMP.Positivity
