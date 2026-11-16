module
public import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram.LabelNormalizationModel
import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldBadBranchCount
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Morphisms.Birational.FiniteFibreLocus
import MMP.AlgebraicGeometry.MMP.Abundance.ComplementedNefThreefold
import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagramBranches
import MMP.AlgebraicGeometry.MMP.Fourfold.PreparedChainDifficulty
import MMP.AlgebraicGeometry.Divisor.SmoothRDivisors

/-!
# Contracted branches of the label normalizations are the bad branches

Let `Y⁻ → Z ← Y⁺` (by `f^±`) be a threefold step diagram in which both morphisms are small, with
bad loci `W^±`. Let `S⁻` be a prime divisor of `Y⁻` with strict transform `S⁺` on `Y⁺`, let
`ν^± : (S^±)^ν ⟶ S^± ⊆ Y^±` be the normalizations, and let `τ : T ⟶ Z` be the normalization of
the prime divisor `D = f⁻(S⁻)` of `Z`. For a morphism `σ^ε : (S^ε)^ν ⟶ T` with
`σ^ε ≫ τ = ν^ε ≫ f^ε` (as given by
`MMP.Fourfold.exists_normalization_hom_isIso_restrict_commonBiregularLocus`), a prime divisor `P`
of `(S^ε)^ν` is mapped by `σ^ε` to a point if and only if `ν^ε(P) ⊆ W^ε`.

Every point `z` of the bad locus `Σ` of the base is closed. Some `f^ε` is not an isomorphism
over `z`, so its fibre over `z` is positive-dimensional and contains a specialization `b ⤳ a`
of distinct points. As `f^ε` is small, `b` has coheight at least two, so `a` has coheight three
and is a closed point of the threefold `Y^ε`; hence `z = f^ε(a)` is closed.

If `ν(P) ⊆ W`, then `τ(σ(η_P)) ∈ Σ` is closed, and since `τ` is finite, `σ` maps all of `P` to
`σ(η_P)`. If `ν(η_P) ∉ W`, then `f^ε` is injective over `f^ε(ν(η_P))`. A contracted `P` would then
map to a single point under the finite `ν`, which would make `P` a closed point of the surface
`(S^ε)^ν`; a prime divisor is not a closed point.

## Main results

* `MMP.Fourfold.image_eq_singleton_iff_image_subset_badLocus`: the prime divisors of `(S^±)^ν`
  contracted by `σ^±` are exactly those lying over the bad loci `W^±`.

## Implementation notes

* The morphism `σ^ε` is characterised by `σ^ε ≫ τ = ν^ε ≫ f^ε` alone: `(S^ε)^ν` is integral and
  `T` separated, and `τ` is an isomorphism over a dense open subset of `D`, so there is at most one
  such morphism. The statement therefore applies to every morphism with this property.
* The source deduces that `σ^ε(P)` is a curve when `ν^ε(P) ⊄ W^ε` from `σ^ε` being an open
  immersion on `O^ε`. Here the same conclusion comes from `f^ε` being injective over the common
  biregular locus, so the uniqueness of `σ^ε` is not needed.
* "`σ^ε` maps `P` to a point" is: the image of the support of `P` is a singleton.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Order

namespace MMP.Fourfold

open MMP.Mori

/-- A positive-dimensional fibre `f⁻¹(z)` of a continuous map from a quasi-sober space to a `T₀`
space contains a specialization `b ⤳ a` between two distinct points. -/
private theorem exists_specializes_ne_of_pos {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [QuasiSober X] [T0Space Y] {f : X → Y} (hf : Continuous f) {z : Y}
    (h : 0 < topologicalKrullDim (f ⁻¹' {z})) :
    ∃ a b, f a = z ∧ f b = z ∧ b ⤳ a ∧ b ≠ a := by
  rw [topologicalKrullDim, Order.krullDim_pos_iff] at h
  obtain ⟨A, B, hAB⟩ := h
  have hmem : ∀ C : IrreducibleCloseds (f ⁻¹' {z}), ∀ x : f ⁻¹' {z},
      (x : X) ∈ closure (((↑) : f ⁻¹' {z} → X) '' (C : Set (f ⁻¹' {z}))) ↔
        x ∈ (C : Set (f ⁻¹' {z})) := by
    intro C x
    rw [← Set.mem_preimage, ← Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image,
      C.isClosed.closure_eq]
  have hgen : ∀ C : IrreducibleCloseds (f ⁻¹' {z}),
      ∀ hC : IsIrreducible (((↑) : f ⁻¹' {z} → X) '' (C : Set (f ⁻¹' {z}))),
      f hC.genericPoint = z := by
    intro C hC
    have hg := hC.isGenericPoint_genericPoint_closure
    obtain ⟨x, hx⟩ := C.isIrreducible.nonempty
    have h1 : hC.genericPoint ⤳ (x : X) := hg.specializes (subset_closure ⟨x, hx, rfl⟩)
    have h2 : f hC.genericPoint ∈ closure ({z} : Set Y) := by
      refine closure_mono ?_ (image_closure_subset_closure_image hf ⟨_, hg.mem, rfl⟩)
      rintro _ ⟨_, ⟨y, -, rfl⟩, rfl⟩
      exact y.2
    have h3 : f hC.genericPoint ⤳ z := by
      have := h1.map hf
      rwa [show f x = z from x.2] at this
    exact (inseparable_iff_specializes_and.mpr ⟨h3, specializes_iff_mem_closure.mpr h2⟩).eq
  have hA : IsIrreducible (((↑) : f ⁻¹' {z} → X) '' (A : Set (f ⁻¹' {z}))) :=
    A.isIrreducible.image _ continuous_subtype_val.continuousOn
  have hB : IsIrreducible (((↑) : f ⁻¹' {z} → X) '' (B : Set (f ⁻¹' {z}))) :=
    B.isIrreducible.image _ continuous_subtype_val.continuousOn
  have ha := hA.isGenericPoint_genericPoint_closure
  have hb := hB.isGenericPoint_genericPoint_closure
  refine ⟨hA.genericPoint, hB.genericPoint, hgen A hA, hgen B hB,
    hb.specializes (closure_mono (Set.image_mono hAB.le) ha.mem), fun heq => ?_⟩
  refine hAB.ne (IrreducibleCloseds.ext (Set.ext fun x => ?_))
  rw [← hmem A x, ← hmem B x, ← ha.def, ← hb.def, heq]

/-- A small morphism from a threefold of finite type over `ℂ` is an isomorphism over every
non-closed point. -/
private theorem isClosed_singleton_of_notMem_biregularLocus {Y Z : Scheme.{0}}
    {sY : Y ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {g : Y ⟶ Z} (hg : IsSmallMorphism sY sZ g)
    (hdim : topologicalKrullDim Y = 3) {z : Z} (hz : z ∉ biregularLocus g) :
    IsClosed ({z} : Set Z) := by
  have hYv := hg.isNormalVariety_source
  have hZv := hg.isNormalVariety_target
  have := hZv.2
  have := hg.isProper
  have := hYv.1.toIsIntegral
  have := hYv.1.toLocallyOfFiniteType
  have hpos : 0 < topologicalKrullDim (g ⁻¹' {z}) := by
    by_contra h
    exact hz (MMP.Fourfold.mem_biregularLocus_of_topologicalKrullDim_le hYv.1 hZv.1 g hg.comp_eq
      hg.isBirationalMorphism (not_lt.mp h))
  obtain ⟨a, b, ha, hb, hba, hne⟩ := exists_specializes_ne_of_pos g.continuous hpos
  have h2 := MMP.Positivity.two_le_coheight_of_mem_exceptionalSet hg.two_le_codimension
    (mem_exceptionalSet.mpr (hb ▸ hz))
  have h3 : 2 + 1 ≤ coheight a := (add_le_add h2 le_rfl).trans
    (Order.coheight_add_one_le (MMP.Intersection.lt_of_specializes_of_ne hba hne.symm))
  have hle : ∀ x : Y, coheight x ≤ 3 := fun x => by
    have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY x
    rw [hdim] at h
    have : Nonempty (IrreducibleCloseds (closure {x} : Set Y)) :=
      ⟨⟨closure {⟨x, subset_closure rfl⟩}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
    have h0 : 0 ≤ topologicalKrullDim (closure {x} : Set Y) := Order.krullDim_nonneg
    have h4 : ((coheight x : ℕ∞) : WithBot ℕ∞) ≤ ((3 : ℕ∞) : WithBot ℕ∞) :=
      (le_add_of_nonneg_left h0).trans h.le
    exact WithBot.coe_le_coe.mp h4
  have hcl : IsClosed ({a} : Set Y) := by
    refine closure_subset_iff_isClosed.mp fun c hc => ?_
    by_contra hca
    have hca' : c < a :=
      MMP.Intersection.lt_of_specializes_of_ne (specializes_iff_mem_closure.mpr hc) hca
    have h5 := (add_le_add h3 le_rfl).trans ((Order.coheight_add_one_le hca').trans (hle c))
    exact absurd h5 (by decide)
  rw [← ha, ← Set.image_singleton]
  exact g.isClosedMap _ hcl

/-- The normalization of a prime divisor of a scheme locally of finite type over a field is
finite. -/
private theorem isFinite_primeDivisorNormalization {k : Type} [Field k] {Y : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] (S : MMP.Mori.PrimeDivisor Y) :
    IsFinite (primeDivisorNormalization S) := by
  have := S.integral
  have : IsFinite (Stacks.AlgebraicGeometry.Normalization.normalization S.idealSheaf.subscheme
      (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U)) :=
    isFinite_normalization_of_locallyOfFiniteType S.idealSheaf.subscheme
      (S.idealSheaf.subschemeι ≫ sY) _
  infer_instance

/-- **Contracted prime divisors over a partial isomorphism.** Let `σ ≫ τ = ν ≫ g` with `ν`, `τ`
finite, `N` an integral surface of finite type over `ℂ`, and `g` an isomorphism over an open `V`
whose complement consists of closed points. A prime divisor `P` of `N` is mapped by `σ` to a
point if and only if `ν(P) ⊆ g⁻¹(Z ∖ V)`. -/
private theorem image_eq_singleton_iff_of_comp_eq {Y Z N T : Scheme.{0}} (g : Y ⟶ Z)
    (ν : N ⟶ Y) [IsFinite ν] (τ : T ⟶ Z) [IsFinite τ] (σ : N ⟶ T) (hσ : σ ≫ τ = ν ≫ g)
    [CompactSpace Y] {sN : N ⟶ Spec (.of ℂ)} [IsIntegral N] [LocallyOfFiniteType sN]
    (hN : topologicalKrullDim N = 2) (V : Z.Opens) [IsIso (g ∣_ V)]
    (hV : ∀ z ∉ V, IsClosed ({z} : Set Z)) (P : MMP.Mori.PrimeDivisor N) :
    (∃ t, σ '' P.support = {t}) ↔ ν '' P.support ⊆ g ⁻¹' (V : Set Z)ᶜ := by
  have hP : (P.support : Set N) = closure {P.genericPoint} :=
    AlgebraicGeometry.PrimeDivisor.support_eq_closure P
  have hη : P.genericPoint ∈ (P.support : Set N) := hP ▸ subset_closure rfl
  have hspec : ∀ p ∈ (P.support : Set N), P.genericPoint ⤳ p := fun p hp =>
    specializes_iff_mem_closure.mpr (hP ▸ hp)
  have hpt : ∀ x, τ (σ x) = g (ν x) := fun x => by
    rw [← Scheme.Hom.comp_apply, hσ, Scheme.Hom.comp_apply]
  constructor
  · rintro ⟨t, ht⟩
    by_contra hsub
    have hu : g (ν P.genericPoint) ∈ V := by
      by_contra hu
      refine hsub ?_
      rintro _ ⟨p, hp, rfl⟩
      exact ((hspec p hp).map ν.continuous).mem_closed
        (V.isOpen.isClosed_compl.preimage g.continuous) hu
    have hfib := MMP.Resolution.Bridges.subsingleton_preimage_of_isIso_morphismRestrict g V hu
    have hσt : ∀ p ∈ (P.support : Set N), σ p = t := fun p hp => ht.subset ⟨p, hp, rfl⟩
    have : CompactSpace N := QuasiCompact.compactSpace_of_compactSpace ν
    have hPc : IsClosed (P.support : Set N) := hP ▸ isClosed_closure
    obtain ⟨p, hp, hpcl⟩ := hPc.exists_closed_singleton ⟨_, hη⟩
    have hνp : ν P.genericPoint = ν p := hfib rfl (by
      rw [Set.mem_preimage, Set.mem_singleton_iff, ← hpt, ← hpt, hσt p hp, hσt _ hη])
    rw [← MMP.Fourfold.eq_of_specializes_of_isFinite ν (hspec p hp) hνp] at hpcl
    have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sN P.genericPoint
    rw [hpcl.closure_eq, hN, P.coheight_genericPoint] at h
    have h2 := add_le_add (topologicalKrullDim_zero_of_discreteTopology _ :
      topologicalKrullDim ({P.genericPoint} : Set N) ≤ 0) (le_refl ((1 : ℕ∞) : WithBot ℕ∞))
    rw [h] at h2
    exact absurd h2 (by decide)
  · intro hsub
    have hcl := hV _ (hsub ⟨_, hη, rfl⟩)
    refine ⟨σ P.genericPoint, Set.eq_singleton_iff_unique_mem.mpr ⟨⟨_, hη, rfl⟩, ?_⟩⟩
    rintro _ ⟨p, hp, rfl⟩
    have hs : σ P.genericPoint ⤳ σ p := (hspec p hp).map σ.continuous
    have heq : τ (σ P.genericPoint) = τ (σ p) := by
      have h1 : τ (σ p) ∈ closure {τ (σ P.genericPoint)} :=
        specializes_iff_mem_closure.mp (hs.map τ.continuous)
      rw [hpt P.genericPoint] at h1 ⊢
      rw [hcl.closure_eq] at h1
      exact (Set.mem_singleton_iff.mp h1).symm
    exact (MMP.Fourfold.eq_of_specializes_of_isFinite τ hs heq).symm

variable {Xm Xp Z : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
  [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]

/-- Every point of the bad locus `Σ` of a threefold step diagram with `f⁻` small is closed. -/
private theorem isClosed_singleton_of_notMem_commonBiregularLocus
    {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
    {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (hdiag : IsThreefoldStepDiagram sXm sZ sXp K B fm fp) (hsmall : IsSmallMorphism sXm sZ fm)
    (z : Z) (hz : z ∉ commonBiregularLocus fm fp) : IsClosed ({z} : Set Z) := by
  by_cases hm : z ∈ biregularLocus fm
  · exact isClosed_singleton_of_notMem_biregularLocus hdiag.isSmallMorphism_plus hdiag.dim_plus
      fun hp => hz ⟨hm, hp⟩
  · exact isClosed_singleton_of_notMem_biregularLocus hsmall hdiag.dim_minus hm

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- **Contracted branches are the bad branches.** Let `Y⁻ → Z ← Y⁺` (by `f^±`) be a threefold
step diagram with both morphisms small, `S⁻` a prime divisor of `Y⁻` with strict transform `S⁺`
on `Y⁺`, and `D` the prime divisor `f⁻(S⁻)` of `Z`, with normalizations `ν^±` of `S^±` and `τ`
of `D`. For every morphism `σ^ε : (S^ε)^ν ⟶ T` with `σ^ε ≫ τ = ν^ε ≫ f^ε`, a prime divisor `P` of
`(S^ε)^ν` is mapped by `σ^ε` to a point if and only if `ν^ε(P)` lies in the bad locus `W^ε`. -/
@[mmp "lem_mmp_indexd_bad_branches_exceptional"]
public theorem image_eq_singleton_iff_image_subset_badLocus
    {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
    {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (hdiag : IsThreefoldStepDiagram sXm sZ sXp K B fm fp) (hsmall : IsSmallMorphism sXm sZ fm)
    {S : MMP.Mori.PrimeDivisor Xm} {S' : MMP.Mori.PrimeDivisor Xp}
    (hS' : flipTransformPrimeDivisor fm fp S = some S')
    {D : MMP.Mori.PrimeDivisor Z} (hD : (D.support : Set Z) = fm '' S.support) :
    (∀ σm : primeDivisorNormalizationScheme S ⟶ primeDivisorNormalizationScheme D,
      σm ≫ primeDivisorNormalization D = primeDivisorNormalization S ≫ fm →
      ∀ P : MMP.Mori.PrimeDivisor (primeDivisorNormalizationScheme S),
        (∃ t, σm '' P.support = {t}) ↔
          primeDivisorNormalization S '' P.support ⊆ badLocusMinus fm fp) ∧
    (∀ σp : primeDivisorNormalizationScheme S' ⟶ primeDivisorNormalizationScheme D,
      σp ≫ primeDivisorNormalization D = primeDivisorNormalization S' ≫ fp →
      ∀ P : MMP.Mori.PrimeDivisor (primeDivisorNormalizationScheme S'),
        (∃ t, σp '' P.support = {t}) ↔
          primeDivisorNormalization S' '' P.support ⊆ badLocusPlus fm fp) := by
  obtain ⟨⟨-, hNm, hdm⟩, ⟨-, hNp, hdp⟩, -⟩ :=
    exists_normalization_hom_isIso_restrict_commonBiregularLocus hdiag hsmall hS'
  have := hdiag.isNormalVariety_minus.1.toLocallyOfFiniteType
  have := hdiag.isNormalVariety_plus.1.toLocallyOfFiniteType
  have := hdiag.isNormalVariety_target.1.toLocallyOfFiniteType
  have := hNm.1.toIsIntegral
  have := hNm.1.toLocallyOfFiniteType
  have := hNp.1.toIsIntegral
  have := hNp.1.toLocallyOfFiniteType
  have := isFinite_primeDivisorNormalization sXm S
  have := isFinite_primeDivisorNormalization sXp S'
  have := isFinite_primeDivisorNormalization sZ D
  have : IsIso (fm ∣_ commonBiregularLocus fm fp) := isBiregular_commonBiregularLocus_left fm fp
  have : IsIso (fp ∣_ commonBiregularLocus fm fp) := isBiregular_commonBiregularLocus_right fm fp
  have hbad := isClosed_singleton_of_notMem_commonBiregularLocus hdiag hsmall
  exact ⟨fun σm hσm P => image_eq_singleton_iff_of_comp_eq fm _ _ σm hσm
    (sN := primeDivisorNormalization S ≫ sXm) hdm _ hbad P,
    fun σp hσp P => image_eq_singleton_iff_of_comp_eq fp _ _ σp hσp
      (sN := primeDivisorNormalization S' ≫ sXp) hdp _ hbad P⟩

end MMP.Fourfold

end
