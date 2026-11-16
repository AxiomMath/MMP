module

public import Mathlib
public import MMP.AlgebraicGeometry.MMP.Fourfold.ConductorDefect
public import MMP.AlgebraicGeometry.MMP.Fourfold.PuncturedLocalSystem
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.PointsOver
import MMP.AlgebraicGeometry.Analytic.SchemeManifoldSlice
import MMP.AlgebraicGeometry.Analytic.ComplexPoints.LocallyContractible
import MMP.AlgebraicGeometry.Analytic.AnalyticMapOpenSubscheme
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.ContractedEdgeInjectivity
import MMP.AlgebraicGeometry.Analytic.ComplexPoints.RegularPartConnected
import MMP.AlgebraicGeometry.Analytic.ComplexPoints.RegularPartDense
import StacksFrontier.AlgebraicGeometry.IrreducibleComponentSubscheme.Basic
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.RingTheory.Presentation.HypersurfacePresentation
import StacksFrontier.AlgebraicGeometry.Properties.NormalCoproduct
import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AmpleSmoothIrreducible
import MMP.AlgebraicGeometry.Morphisms.GenericSmoothness
import StacksFrontier.AlgebraicGeometry.Intersection.TorFormulaMultiplicities.MultiplicityOneSmoothness
import MMP.AlgebraicGeometry.Resolution.DisjoiningCenter
import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.Sequence
import MMP.AlgebraicGeometry.Morphisms.Smooth.RegularParameters
public import MMP.AlgebraicGeometry.Chow.FieldSituation
public import MMP.Topology.KrullDimensionProperClosed
public import MMP.AlgebraicGeometry.ReducedSubschemeOver
public import StacksFrontier.RingTheory.NoetherNormalization.Basic
public import MMP.AlgebraicGeometry.SubschemeOver

/-!
# Topological triviality of the exceptional family over a general curve

Let `r : Z ⟶ Y` be a curve-and-point exceptional model with snc exceptional divisor
`F = ∑ Fᵢ`, and `T ⊆ Sing Y` a curve. Over a general open `T° ⊆ T` every stratum `F_J` is smooth
over `T°`, and near every point `b ∈ T°(ℂ)` the family `F^an ∩ r⁻¹(Δ) → Δ` over a small disk
`Δ ∋ b` is topologically the product `F_b^an × Δ`, by a homeomorphism over `Δ`, equal to the
identity over `b`, preserving every component `Fᵢ`. The double surfaces dominating `T` have
connected complex points over `T°`.

## Main definitions

* `MMP.Fourfold.ExceptionalChart`: a smooth open of `Z` with a function to a smooth curve, on
  which the trace of `F` is relatively snc and proper, and a sheet of `T` over the curve.
* `MMP.Fourfold.ExceptionalAlgebraicChart`: the algebraic data of such a chart, a function on an
  open of `Y` finite étale on `T` over a smooth curve.

## Main results

* `MMP.Analytic.ComplexPoints.exists_homeomorph_prod_of_isSNC_of_isProperMap`: the product germ
  along a relative snc divisor of a smooth complex scheme over a curve, preserving every component.
* `MMP.Fourfold.mem_pointsOver_carrier_iff_of_homeomorph`: a trivialization preserving the
  components of `F` preserves the double surfaces.
* `MMP.Fourfold.exists_homeomorph_prod_of_isClopen_sheet`: restricting a product germ to an open
  and closed sheet.
* `MMP.Fourfold.smooth_iSup_idealSheaf_of_isSNC`, `MMP.Fourfold.smooth_sup_idealSheaf_of_isSNC`:
  the strata of an snc divisor over a perfect field are smooth.
* `MMP.Fourfold.nonempty_exceptionalChart_of_algebraicChart`: exceptional charts from algebraic
  ones.
* `MMP.Fourfold.exists_open_singularLocus_inter_eq`: near a general point of `T`, `Sing Y = T`.
* `MMP.Fourfold.exists_homeomorph_prod_exceptionalFibre`: the product germ of the exceptional
  family over a general open of `T`.
* `MMP.Fourfold.isConnected_pointsOver_doubleSurface_inter`: connectedness of a double surface
  over a general open of `T`.

## Implementation notes

The fibre and the family are subspaces of `Z(ℂ)` (`MMP.UnderlyingSpace ℂ Z`):
`F_b = F(ℂ) ∩ r⁻¹{b}` and `F_Δ = F(ℂ) ∩ r⁻¹ Δ`, for `Δ` relatively open in `(T° ∩ U)(ℂ)`. The
trivialization is that of a neighbourhood of `F` in `Z^an` for a local holomorphic function on
`Y` restricting to a coordinate of `T` at `b`, read on `F`.

## References

* [Kollár–Mori, *Birational geometry of algebraic varieties*]
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace MMP Topology
open MMP.UnderlyingSpace
open scoped MMP.SubschemeOver

namespace MMP.Analytic.ComplexPoints

section Glue

variable {Zs Bs : Type*} [TopologicalSpace Zs] [TopologicalSpace Bs]

/-- **Gluing component-preserving product structures over a common disk.** As
`MMP.Analytic.ComplexPoints.exists_homeomorph_prod_of_isOpenEmbedding_family`, for local product
structures which moreover preserve each member of a family of sets `Dk k`: the glued product
structure preserves each `Dk k` as well. -/
theorem exists_homeomorph_prod_of_isOpenEmbedding_family_of_forall_mem_iff
    {G : Zs → Bs} {E : Set Zs} (hG : IsProperMap (E.domRestrict G)) {b : Bs}
    (hloc : ∀ N ∈ 𝓝 b, ∃ Δ ⊆ N, IsOpen Δ ∧ IsPreconnected Δ ∧ b ∈ Δ)
    {ι : Type*} {M : ι → Type*} [∀ i, TopologicalSpace (M i)] {ρ : ∀ i, M i → Zs}
    (hρ : ∀ i, IsOpenEmbedding (ρ i))
    (hdisj : Pairwise fun i j ↦ Disjoint (Set.range (ρ i)) (Set.range (ρ j)))
    (hcov : E ⊆ ⋃ i, Set.range (ρ i)) {κ : Type*} (Dk : κ → Set Zs)
    (hflow : ∀ i, ∃ Δi ∈ 𝓝 b, ∃ (Ubi Ui : Set (M i)) (hb : b ∈ Δi),
      (∃ O, IsOpen O ∧ Ubi = O ∩ (G ∘ ρ i) ⁻¹' {b}) ∧ ρ i ⁻¹' E ∩ (G ∘ ρ i) ⁻¹' {b} ⊆ Ubi ∧
      IsOpen Ui ∧ ρ i ⁻¹' E ∩ (G ∘ ρ i) ⁻¹' Δi ⊆ Ui ∧ ∃ Φ : Ubi × Δi ≃ₜ Ui,
        (∀ p, G (ρ i (Φ p)) = p.2) ∧ (∀ z, (Φ (z, ⟨b, hb⟩) : M i) = z) ∧
        (∀ p, ρ i (Φ p) ∈ E ↔ ρ i p.1 ∈ E) ∧ ∀ k p, ρ i (Φ p) ∈ Dk k ↔ ρ i p.1 ∈ Dk k) :
    ∃ Δ : Set Bs, IsOpen Δ ∧ IsPreconnected Δ ∧ ∃ hbΔ : b ∈ Δ, ∃ O Ub U : Set Zs,
      IsOpen O ∧ Ub = O ∩ G ⁻¹' {b} ∧ E ∩ G ⁻¹' {b} ⊆ Ub ∧ IsOpen U ∧ E ∩ G ⁻¹' Δ ⊆ U ∧
      ∃ Φ : Ub × Δ ≃ₜ U, (∀ p, G (Φ p) = p.2) ∧ (∀ z : Ub, (Φ (z, ⟨b, hbΔ⟩) : Zs) = z) ∧
        (∀ p, (Φ p : Zs) ∈ E ↔ (p.1 : Zs) ∈ E) ∧ ∀ k p, (Φ p : Zs) ∈ Dk k ↔ (p.1 : Zs) ∈ Dk k := by
  classical
  choose Δi hΔi Ubi Ui hbi hO hEb hUo hEU Φi hΦg hΦb hΦE hΦD using hflow
  choose O hOo hOeq using hO
  -- the fibre `E_b` is compact, so finitely many members of the cover meet it
  have hEbc : IsCompact (E ∩ G ⁻¹' {b}) := by
    have := (hG.isCompact_preimage (isCompact_singleton (x := b))).image continuous_subtype_val
    convert this using 1
    ext z
    constructor
    · rintro ⟨hzE, hzb⟩
      exact ⟨⟨z, hzE⟩, hzb, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.2, hw⟩
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
  have hΦsg : ∀ q, G (Φs q) = q.2 := fun q ↦ by
    obtain ⟨⟨i, m⟩, t⟩ := q
    exact (hΦg i.1 _).trans rfl
  have hΦsE : ∀ q, Φs q ∈ E ↔ ρ q.1.1.1 q.1.2 ∈ E := fun q ↦ by
    obtain ⟨⟨i, m⟩, t⟩ := q
    exact hΦE i.1 _
  have hΦsD : ∀ k q, Φs q ∈ Dk k ↔ ρ q.1.1.1 q.1.2 ∈ Dk k := fun k q ↦ by
    obtain ⟨⟨i, m⟩, t⟩ := q
    exact hΦD i.1 k _
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
    hΦ'.isEmbedding.toHomeomorph, fun p ↦ ?_, fun z ↦ ?_, fun p ↦ ?_, fun k p ↦ ?_⟩
  · ext z
    constructor
    · rintro ⟨⟨i, m⟩, rfl⟩
      have hm : (m : M i.1) ∈ O i.1 ∩ (G ∘ ρ i.1) ⁻¹' {b} := hOeq i.1 ▸ m.2
      rw [he]
      exact ⟨Set.mem_iUnion₂.2 ⟨i.1, i.2, m.1, hm.1, rfl⟩, hm.2⟩
    · rintro ⟨hz, hzb⟩
      obtain ⟨i, hi, o, ho, rfl⟩ := Set.mem_iUnion₂.1 hz
      have hm : o ∈ Ubi i := by rw [hOeq]; exact ⟨ho, hzb⟩
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
  · rw [IsEmbedding.toHomeomorph_apply_coe]
    change Φs (eh.symm p.1, p.2) ∈ Dk k ↔ _
    rw [hΦsD, ← he, heh]

end Glue

section SchemeSNC

open scoped ContDiff Manifold

variable {W B : Scheme.{0}} {sW : W ⟶ Spec (.of ℂ)} {sB : B ⟶ Spec (.of ℂ)}

/-- **Component-preserving product germ along a relative snc divisor.** Let `g : W ⟶ B` be a
morphism from a separated quasi-compact smooth complex scheme to a smooth complex curve, and
`E = ∑_{Eᵢ ∈ s} Eᵢ` an snc divisor on `W` all of whose strata, `W` included, are smooth over `B`,
with `E^an` proper over `B^an`. Then over an open preconnected `Δ ∋ b`, a neighbourhood of `E_Δ`
is the product of a neighbourhood of `E_b` in the fibre over `b` with `Δ`, by a homeomorphism
over `Δ` which is the identity over `b` and preserves every `Eᵢ^an`. -/
theorem exists_homeomorph_prod_of_isSNC_of_isProperMap
    [LocallyOfFiniteType sW] [IsSeparated sW] [QuasiCompact sW] [Smooth sW]
    [LocallyOfFiniteType sB] [IsSeparated sB] [QuasiCompact sB] [SmoothOfRelativeDimension 1 sB]
    (g : W ⟶ B) (hg : g ≫ sB = sW) (s : Finset (Mori.PrimeDivisor W))
    (hsnc : Mori.DivisorWithCoeffs.IsSNC sW (∑ E ∈ s, Finsupp.single E (1 : ℤ)))
    (hstr : ∀ J ⊆ s, Smooth ((⨆ E ∈ J, E.idealSheaf).subschemeι ≫ g))
    (hprop : IsProperMap ({z : ComplexPoints sW | toScheme z ∈ ⋃ E ∈ s, (E.support : Set W)}
      |>.domRestrict (realize g hg)))
    (b : ComplexPoints sB) :
    ∃ Δ : Set (ComplexPoints sB), IsOpen Δ ∧ IsPreconnected Δ ∧ ∃ hbΔ : b ∈ Δ,
      ∃ O Ub U : Set (ComplexPoints sW), IsOpen O ∧ Ub = O ∩ realize g hg ⁻¹' {b} ∧
        {z : ComplexPoints sW | toScheme z ∈ ⋃ E ∈ s, (E.support : Set W)} ∩
          realize g hg ⁻¹' {b} ⊆ Ub ∧ IsOpen U ∧
        {z : ComplexPoints sW | toScheme z ∈ ⋃ E ∈ s, (E.support : Set W)} ∩
          realize g hg ⁻¹' Δ ⊆ U ∧
        ∃ Φ : Ub × Δ ≃ₜ U, (∀ p, realize g hg (Φ p) = p.2) ∧
          (∀ z : Ub, (Φ (z, ⟨b, hbΔ⟩) : ComplexPoints sW) = z) ∧
          ∀ E ∈ s, ∀ p, toScheme (Φ p : ComplexPoints sW) ∈ E.support ↔
            toScheme (p.1 : ComplexPoints sW) ∈ E.support := by
  classical
  have : Smooth sB := SmoothOfRelativeDimension.smooth 1 sB
  set G := realize g hg
  set Eset : Set (ComplexPoints sW) :=
    {z : ComplexPoints sW | toScheme z ∈ ⋃ E ∈ s, (E.support : Set W)} with hEset
  have hEc : IsClosed Eset := by
    refine isClosed_setOf_toScheme_mem (Set.Finite.isClosed_biUnion s.finite_toSet fun E _ ↦ ?_)
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isClosed_closure
  have hloc : ∀ N ∈ 𝓝 b, ∃ Δ ⊆ N, IsOpen Δ ∧ IsPreconnected Δ ∧ b ∈ Δ :=
    fun _ hN ↦ exists_isOpen_isPreconnected_subset_of_mem_nhds hN
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian sW
  let Y : ℕ → W.Opens := fun d ↦ relativeDimensionLocus sW d
  let M : ℕ → Type := fun d ↦ ComplexPoints ((Y d).ι ≫ sW)
  let ρ : ∀ d, M d → ComplexPoints sW := fun d ↦
    realize (sX := (Y d).ι ≫ sW) (sY := sW) (Y d).ι rfl
  have hρ : ∀ d, IsOpenEmbedding (ρ d) := fun d ↦
    isOpenEmbedding_realize_of_isOpenImmersion _ _
  have hρpt : ∀ d (m : M d), toScheme (ρ d m) = (Y d).ι (toScheme m) := fun _ _ ↦ rfl
  have hdisj : Pairwise fun d d' ↦ Disjoint (Set.range (ρ d)) (Set.range (ρ d')) := by
    intro d d' hdd
    rw [Set.disjoint_left]
    rintro _ ⟨m, rfl⟩ ⟨m', hm'⟩
    have h1 := congrArg toScheme hm'
    rw [hρpt, hρpt] at h1
    have hm1 : (Y d').ι (toScheme m') ∈ Y d' := (Scheme.Opens.range_ι (Y d')).le ⟨_, rfl⟩
    have hm2 : (Y d).ι (toScheme m) ∈ Y d := (Scheme.Opens.range_ι (Y d)).le ⟨_, rfl⟩
    rw [h1] at hm1
    exact hdd (eq_of_mem_relativeDimensionLocus hm2 hm1)
  have hcov : Eset ⊆ ⋃ d, Set.range (ρ d) := by
    intro z _
    obtain ⟨d, hd⟩ := exists_mem_relativeDimensionLocus (sX := sW) (toScheme z)
    obtain ⟨q, hq⟩ : toScheme z ∈ Set.range (Y d).ι := by
      rw [Scheme.Opens.range_ι]; exact hd
    refine Set.mem_iUnion.2 ⟨d, ?_⟩
    rw [range_realize_of_isOpenImmersion]
    exact ⟨q, hq⟩
  let Dk : s → Set (ComplexPoints sW) := fun E ↦ {z | toScheme z ∈ E.1.support}
  -- on each locus, the flow trivializes a neighbourhood of `E` over a disk
  have hflow : ∀ d, ∃ Δi ∈ 𝓝 b, ∃ (Ubi Ui : Set (M d)) (hb : b ∈ Δi),
      (∃ O, IsOpen O ∧ Ubi = O ∩ (G ∘ ρ d) ⁻¹' {b}) ∧ ρ d ⁻¹' Eset ∩ (G ∘ ρ d) ⁻¹' {b} ⊆ Ubi ∧
      IsOpen Ui ∧ ρ d ⁻¹' Eset ∩ (G ∘ ρ d) ⁻¹' Δi ⊆ Ui ∧ ∃ Φ : Ubi × Δi ≃ₜ Ui,
        (∀ p, G (ρ d (Φ p)) = p.2) ∧ (∀ z, (Φ (z, ⟨b, hb⟩) : M d) = z) ∧
        (∀ p, ρ d (Φ p) ∈ Eset ↔ ρ d p.1 ∈ Eset) ∧
        ∀ k p, ρ d (Φ p) ∈ Dk k ↔ ρ d p.1 ∈ Dk k := by
    intro d
    obtain ⟨pick, hcmd, hD, hsub, hstrata⟩ :=
      exists_pick_relativeSNC_relativeDimensionLocus (sX := sW) d g hg s hsnc hstr
    let := etaleChartedSpaceOf ((Y d).ι ≫ sW) d (EuclideanSpace.equiv (Fin d) ℂ).symm pick
    have := isManifold_etaleChartedSpaceOf ((Y d).ι ≫ sW) d
      (EuclideanSpace.equiv (Fin d) ℂ).symm pick ∞
    have : T2Space (M d) := t2Space
    have : SecondCountableTopology (M d) := secondCountableTopology d
    let D : s → Set (M d) := fun E ↦ {y | (Y d).ι (toScheme y) ∈ E.1.support}
    let gY := realize (sX := (Y d).ι ≫ sW) (sY := sB) ((Y d).ι ≫ g)
      (by rw [Category.assoc, hg])
    have hgY : gY = G ∘ ρ d := by
      funext y
      ext1
      simp only [gY, G, ρ, Function.comp_apply, realize_hom, Category.assoc]
    have hDk : ∀ k, D k = ρ d ⁻¹' Dk k := fun k ↦ rfl
    have hDE : (⋃ i, D i) = ρ d ⁻¹' Eset := by
      ext y
      simp only [D, Eset, Set.mem_iUnion, Set.mem_preimage, Set.mem_setOf_eq, hρpt]
      exact ⟨fun ⟨i, hi⟩ ↦ ⟨i.1, i.2, hi⟩, fun ⟨E, hE, hi⟩ ↦ ⟨⟨E, hE⟩, hi⟩⟩
    have hEcl : IsClosed (⋃ i, D i) := by
      rw [hDE]
      exact hEc.preimage (hρ d).continuous
    have hprop' : IsProperMap fun y : (⋃ i, D i : Set (M d)) ↦ gY y := by
      have hcl : IsClosedEmbedding (Eset.restrictPreimage (ρ d)) := by
        refine ⟨((hρ d).restrictPreimage Eset).isEmbedding, ?_⟩
        rw [Set.range_restrictPreimage, ← isOpen_compl_iff]
        have : (Subtype.val ⁻¹' Set.range (ρ d) : Set Eset)ᶜ =
            Subtype.val ⁻¹' ⋃ (d' : ℕ) (_ : d' ≠ d), Set.range (ρ d') := by
          ext e
          simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_iUnion, exists_prop]
          constructor
          · intro he
            obtain ⟨d', hd'⟩ := Set.mem_iUnion.1 (hcov e.2)
            exact ⟨d', fun h' ↦ he (h' ▸ hd'), hd'⟩
          · rintro ⟨d', hd', hed⟩ hed'
            exact Set.disjoint_left.1 (hdisj hd') hed hed'
        rw [this]
        exact (isOpen_biUnion fun d' _ ↦ (hρ d').isOpen_range).preimage continuous_subtype_val
      have H := (hprop.comp hcl.isProperMap).comp (Homeomorph.setCongr hDE).isProperMap
      convert H using 1
      funext y
      exact congrFun hgY y.1
    obtain ⟨ψ, -, -, r, -, -, -, Ub, Ui, hb, -, ⟨O, hO, hUbO⟩, hEb, hUo, -, hEU, Φ, hΦg, hΦb,
        hΦD⟩ :=
      MMP.Analytic.exists_homeomorph_prod_of_relativeSNC ((hcmd ∞).mdifferentiable (by simp))
        (hD ∞) hEcl hprop' ⟨Set.univ, isOpen_univ, Set.subset_univ _, fun y _ ↦ hsub y⟩
        (fun y _ ↦ hstrata y) b Filter.univ_mem
    rw [hDE] at hEb hEU
    change ρ d ⁻¹' Eset ∩ gY ⁻¹' {b} ⊆ Ub at hEb
    change ρ d ⁻¹' Eset ∩ gY ⁻¹' (ψ.source ∩ ψ ⁻¹' Metric.ball (ψ b) r) ⊆ Ui at hEU
    change Ub = O ∩ gY ⁻¹' {b} at hUbO
    change ∀ p, gY (Φ p) = p.2 at hΦg
    rw [hgY] at hEb hEU hUbO hΦg
    refine ⟨_, (ψ.isOpen_inter_preimage Metric.isOpen_ball).mem_nhds hb, Ub, Ui, hb,
      ⟨O, hO, hUbO⟩, hEb, hUo, hEU, Φ, hΦg, hΦb, fun p ↦ ?_, fun k p ↦ ?_⟩
    · rw [← Set.mem_preimage (f := ρ d), ← Set.mem_preimage (f := ρ d), ← hDE]
      simp only [Set.mem_iUnion]
      exact exists_congr fun i ↦ hΦD i p
    · rw [← Set.mem_preimage (f := ρ d), ← Set.mem_preimage (f := ρ d), ← hDk]
      exact hΦD k p
  obtain ⟨Δ, hΔo, hΔc, hbΔ, O, Ub, Uz, hOo, hUb, hEb, hUo, hEU, Φ, hΦg, hΦb, -, hΦD⟩ :=
    exists_homeomorph_prod_of_isOpenEmbedding_family_of_forall_mem_iff hprop hloc hρ hdisj hcov
      Dk hflow
  exact ⟨Δ, hΔo, hΔc, hbΔ, O, Ub, Uz, hOo, hUb, hEb, hUo, hEU, Φ, hΦg, hΦb,
    fun E hE p ↦ hΦD ⟨E, hE⟩ p⟩

end SchemeSNC

end MMP.Analytic.ComplexPoints

universe u

namespace MMP.Fourfold

open MMP.Mori

/-! ### Double surfaces along a trivialization -/

section DoubleSurfaceTransport

/-- In any space, the connected component of a point in a closed set is closed. -/
private theorem isClosed_connectedComponentIn_of_isClosed {X : Type*} [TopologicalSpace X]
    {S : Set X} (hS : IsClosed S) (x : X) : IsClosed (connectedComponentIn S x) := by
  by_cases hx : x ∈ S
  · refine closure_subset_iff_isClosed.1 ?_
    exact (isPreconnected_connectedComponentIn.closure).subset_connectedComponentIn
      (subset_closure (mem_connectedComponentIn hx))
      (closure_minimal (connectedComponentIn_subset S x) hS)
  · rw [connectedComponentIn_eq_empty hx]; exact isClosed_empty

/-- In a Noetherian space, the complement of a connected component of a closed set `S` in `S` is
closed: it is the union of the finitely many other components. -/
private theorem isClosed_diff_connectedComponentIn {X : Type*} [TopologicalSpace X]
    [NoetherianSpace X] {S : Set X} (hS : IsClosed S) (x : X) :
    IsClosed (S \ connectedComponentIn S x) := by
  have hfin := DoubleSurface.finite_connectedComponentIn hS
  have heq : S \ connectedComponentIn S x =
      ⋃ K ∈ {K | ∃ y ∈ S, connectedComponentIn S y = K} ∩ {K | Disjoint K (connectedComponentIn S x)},
        K := by
    ext y
    simp only [Set.mem_diff, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq, exists_prop]
    constructor
    · rintro ⟨hyS, hyx⟩
      refine ⟨connectedComponentIn S y, ⟨⟨y, hyS, rfl⟩, ?_⟩, mem_connectedComponentIn hyS⟩
      rw [Set.disjoint_iff]
      rintro w ⟨hwy, hwx⟩
      exact hyx ((connectedComponentIn_eq hwy).trans (connectedComponentIn_eq hwx).symm ▸
        mem_connectedComponentIn hyS)
    · rintro ⟨K, ⟨⟨w, hwS, rfl⟩, hdisj⟩, hyK⟩
      exact ⟨connectedComponentIn_subset S w hyK, fun hyx ↦ Set.disjoint_left.1 hdisj hyK hyx⟩
  rw [heq]
  exact (hfin.subset Set.inter_subset_left).isClosed_biUnion fun K hK ↦ by
    obtain ⟨⟨w, -, rfl⟩, -⟩ := hK
    exact isClosed_connectedComponentIn_of_isClosed hS w

variable {Z Y : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))] [NoetherianSpace Z]
  {r : Z ⟶ Y} [r.IsOver (Spec (.of ℂ))] {F : Divisor Z}

/-- **A trivialization preserving the components of `F` preserves every double surface.** Let
`Φ : F_b × Δ ≃ₜ F_Δ` be the identity over `b` and preserve every component of `F`, with `Δ`
preconnected. Then `Φ` preserves the complex points of every double surface `S`: `S` is a
connected component of `Eᵢ ∩ Eⱼ`, so `S(ℂ)` is open and closed in `(Eᵢ ∩ Eⱼ)(ℂ)`, and each slice
`{z} × Δ` is connected. -/
theorem mem_pointsOver_carrier_iff_of_homeomorph {b : UnderlyingSpace ℂ Y}
    {Δ : Set (UnderlyingSpace ℂ Y)} (hΔ : IsPreconnected Δ) (hbΔ : b ∈ Δ)
    (Φ : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}) × Δ ≃ₜ
      ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' Δ))
    (hΦb : ∀ z, (Φ (z, ⟨b, hbΔ⟩) : UnderlyingSpace ℂ Z) = z)
    (hΦE : ∀ E ∈ F.support, ∀ p, (Φ p : UnderlyingSpace ℂ Z) ∈ pointsOver (E.support : Set Z) ↔
      (p.1 : UnderlyingSpace ℂ Z) ∈ pointsOver (E.support : Set Z))
    (σ : DoubleSurface F) (p) :
    (Φ p : UnderlyingSpace ℂ Z) ∈ pointsOver σ.carrier ↔
      (p.1 : UnderlyingSpace ℂ Z) ∈ pointsOver σ.carrier := by
  obtain ⟨z, t⟩ := p
  set S : Set Z := (σ.fst.support : Set Z) ∩ σ.snd.support with hS
  have hsupp : ∀ E : Mori.PrimeDivisor Z, IsClosed (E.support : Set Z) := fun E ↦ by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isClosed_closure
  have hSc : IsClosed S := (hsupp σ.fst).inter (hsupp σ.snd)
  obtain ⟨x, -, hx⟩ := σ.isComponent
  have hC : IsClosed σ.carrier := hx ▸ isClosed_connectedComponentIn_of_isClosed hSc x
  have hD : IsClosed (S \ σ.carrier) := hx ▸ isClosed_diff_connectedComponentIn hSc x
  have hmemS : ∀ q, (Φ q : UnderlyingSpace ℂ Z) ∈ pointsOver S ↔
      (q.1 : UnderlyingSpace ℂ Z) ∈ pointsOver S := fun q ↦ by
    rw [hS, pointsOver_inter, Set.mem_inter_iff, Set.mem_inter_iff,
      hΦE _ σ.fst_mem, hΦE _ σ.snd_mem]
  by_cases hz : (z : UnderlyingSpace ℂ Z) ∈ pointsOver S
  · -- the path `s ↦ Φ (z, s)` stays in `S(ℂ) = S'(ℂ) ⊔ (S \ S')(ℂ)`
    let φ : Δ → UnderlyingSpace ℂ Z := fun s ↦ (Φ (z, s) : UnderlyingSpace ℂ Z)
    have hφ : Continuous φ :=
      continuous_subtype_val.comp (Φ.continuous.comp (Continuous.prodMk_right z))
    have : PreconnectedSpace Δ := Subtype.preconnectedSpace hΔ
    have hrange : Set.range φ ⊆ pointsOver σ.carrier ∪ pointsOver (S \ σ.carrier) := by
      rintro _ ⟨s, rfl⟩
      have h := (hmemS (z, s)).2 hz
      by_cases h' : (φ s) ∈ pointsOver σ.carrier
      · exact Or.inl h'
      · exact Or.inr ⟨h, h'⟩
    have hdisj : Disjoint (pointsOver (K := ℂ) σ.carrier) (pointsOver (S \ σ.carrier)) :=
      Set.disjoint_left.2 fun _ h1 h2 ↦ h2.2 h1
    have hb : φ ⟨b, hbΔ⟩ = z := hΦb z
    rcases (isPreconnected_iff_subset_of_disjoint_closed.1 (isPreconnected_range hφ)) _ _
      (isClosed_pointsOver hC) (isClosed_pointsOver hD) hrange
      (by rw [Set.disjoint_iff_inter_eq_empty.1 hdisj, Set.inter_empty]) with h | h
    · have hzC : (z : UnderlyingSpace ℂ Z) ∈ pointsOver σ.carrier := by
        rw [← hb]; exact h ⟨⟨b, hbΔ⟩, rfl⟩
      exact iff_of_true (h ⟨t, rfl⟩) hzC
    · have hzD : (z : UnderlyingSpace ℂ Z) ∈ pointsOver (S \ σ.carrier) := by
        rw [← hb]; exact h ⟨⟨b, hbΔ⟩, rfl⟩
      exact iff_of_false (fun h1 ↦ (h ⟨t, rfl⟩).2 h1) (fun h1 ↦ hzD.2 h1)
  · have hz' : (Φ (z, t) : UnderlyingSpace ℂ Z) ∉ pointsOver S := fun h ↦ hz ((hmemS _).1 h)
    exact iff_of_false (fun h ↦ hz' (pointsOver_mono σ.carrier_subset h))
      (fun h ↦ hz (pointsOver_mono σ.carrier_subset h))

end DoubleSurfaceTransport

/-! ### Restricting a product germ to a sheet -/

section SheetRestriction

variable {X Bs Zs Ys : Type*} [TopologicalSpace X] [TopologicalSpace Bs] [TopologicalSpace Zs]
  [TopologicalSpace Ys]

/-- **Restricting a product germ to an open and closed sheet.** Let `ι : X → Zs` be an
embedding, `G : X → Bs`, and `Eset ⊆ X` the union of the sets `Dk k`, `k ∈ Ks`, read in `Zs` as
`Fs`. Let `sheet ⊆ Ys` be homeomorphic by `β` to an open `Bo ⊆ Bs`, such that the points of `Fs`
over `sheet` (for `Rz : Zs → Ys`) come from `X`, form an open and closed part of `Eset` over `Bo`,
and are sent by `G` to the image under `β` of their point of `sheet`. Then a product germ of
`Eset` at `β b` over `Bs`, preserving each `Dk k`, induces, inside every neighbourhood `N` of `b`,
a product germ `Fs_b × Δ ≃ₜ Fs_Δ` over a preconnected `Δ ∋ b`, relatively open in `sheet`,
the identity over `b`, preserving every set `Ek e` cut out on `X` by the `Dk k`. -/
theorem exists_homeomorph_prod_of_isClopen_sheet {G : X → Bs} (hGc : Continuous G) {ι : X → Zs}
    (hι : IsEmbedding ι) {Rz : Zs → Ys} {κ : Type*} {Ks : Set κ} {Dk : κ → Set X}
    {Eset : Set X} (hE : Eset = ⋃ k ∈ Ks, Dk k) {Fs : Set Zs} (hEF : ∀ w, ι w ∈ Fs ↔ w ∈ Eset)
    {κ' : Type*} {Es : Set κ'} {Ek : κ' → Set Zs}
    (hEk : ∀ e ∈ Es, ∃ K ⊆ Ks, ∀ w, ι w ∈ Ek e ↔ ∃ k ∈ K, w ∈ Dk k)
    {sheet : Set Ys} {Bo : Set Bs} (hBo : IsOpen Bo) (β : sheet ≃ₜ Bo)
    (hW : ∀ z ∈ Fs, Rz z ∈ sheet → ∃ w, ι w = z)
    (hcl : IsClopen {w : ↥(Eset ∩ G ⁻¹' Bo) | Rz (ι w) ∈ sheet})
    (hreal : ∀ w ∈ Eset, ∀ hw : Rz (ι w) ∈ sheet, G w = β ⟨_, hw⟩)
    {b : Ys} (hb : b ∈ sheet)
    (hloc : ∀ N ∈ 𝓝 (β ⟨b, hb⟩ : Bs), ∃ Δ ⊆ N, IsOpen Δ ∧ IsPreconnected Δ ∧
      (β ⟨b, hb⟩ : Bs) ∈ Δ)
    {Δ₁ : Set Bs} (hΔ₁ : IsOpen Δ₁) (hbΔ₁ : (β ⟨b, hb⟩ : Bs) ∈ Δ₁) {Ub U : Set X}
    (hUb : Ub ⊆ G ⁻¹' {(β ⟨b, hb⟩ : Bs)}) (hEb : Eset ∩ G ⁻¹' {(β ⟨b, hb⟩ : Bs)} ⊆ Ub)
    (hEU : Eset ∩ G ⁻¹' Δ₁ ⊆ U)
    (Φ₁ : Ub × Δ₁ ≃ₜ U) (hΦg : ∀ p, G (Φ₁ p) = p.2) (hΦb : ∀ z, (Φ₁ (z, ⟨_, hbΔ₁⟩) : X) = z)
    (hΦD : ∀ k ∈ Ks, ∀ p, (Φ₁ p : X) ∈ Dk k ↔ (p.1 : X) ∈ Dk k)
    {N : Set Ys} (hN : N ∈ 𝓝 b) :
    ∃ Δ : Set Ys, Δ ⊆ N ∧ (∃ O, IsOpen O ∧ Δ = O ∩ sheet) ∧ IsPreconnected Δ ∧ ∃ hbΔ : b ∈ Δ,
      ∃ Φ : ↥(Fs ∩ Rz ⁻¹' {b}) × Δ ≃ₜ ↥(Fs ∩ Rz ⁻¹' Δ),
        (∀ p, Rz (Φ p : Zs) = p.2) ∧ (∀ z, (Φ (z, ⟨b, hbΔ⟩) : Zs) = z) ∧
        ∀ e ∈ Es, ∀ p, (Φ p : Zs) ∈ Ek e ↔ (p.1 : Zs) ∈ Ek e := by
  classical
  set bB : Bs := ((β ⟨b, hb⟩ : Bo) : Bs)
  have hΦE : ∀ p, (Φ₁ p : X) ∈ Eset ↔ (p.1 : X) ∈ Eset := fun p ↦ by
    rw [hE]; simp only [Set.mem_iUnion₂]
    exact exists₂_congr fun k hk ↦ hΦD k hk p
  -- a small preconnected disk `Δ'` around `bB`
  have hN₁ : Δ₁ ∩ Subtype.val '' (β '' (Subtype.val ⁻¹' N : Set sheet)) ∈ 𝓝 bB := by
    refine Filter.inter_mem (hΔ₁.mem_nhds hbΔ₁) ?_
    refine hBo.isOpenMap_subtype_val.image_mem_nhds (x := β ⟨b, hb⟩) ?_
    exact β.isOpenMap.image_mem_nhds (continuous_subtype_val.continuousAt.preimage_mem_nhds hN)
  obtain ⟨Δ', hΔ'N, hΔ'o, hΔ'c, hbΔ'⟩ := hloc _ hN₁
  have hΔ'B : Δ' ⊆ Bo := fun t ht ↦ by
    obtain ⟨-, ⟨u, -, rfl⟩⟩ := hΔ'N ht; exact u.2
  have hΔ'₁ : Δ' ⊆ Δ₁ := fun t ht ↦ (hΔ'N ht).1
  set Δ : Set Ys := Subtype.val '' (β ⁻¹' (Subtype.val ⁻¹' Δ')) with hΔ
  have hΔs : Δ ⊆ sheet := by rintro _ ⟨y, -, rfl⟩; exact y.2
  have hmemΔ : ∀ y (hy : y ∈ sheet), y ∈ Δ ↔ (β ⟨y, hy⟩ : Bs) ∈ Δ' := fun y hy ↦
    ⟨fun ⟨y', hy', hyy⟩ ↦ by subst hyy; exact hy', fun h ↦ ⟨⟨y, hy⟩, h, rfl⟩⟩
  have hβinj : ∀ y y' (hy : y ∈ sheet) (hy' : y' ∈ sheet),
      (β ⟨y, hy⟩ : Bs) = β ⟨y', hy'⟩ → y = y' := fun y y' hy hy' h ↦
    congrArg Subtype.val (β.injective (Subtype.ext h))
  have hΔN : Δ ⊆ N := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨-, ⟨u, ⟨y', hy'N, hyu⟩, hu⟩⟩ := hΔ'N hy
    rw [← hyu] at hu
    rw [← hβinj _ _ y'.2 y.2 hu]; exact hy'N
  have hbΔ : b ∈ Δ := (hmemΔ b hb).2 hbΔ'
  have hΔopen : ∃ O, IsOpen O ∧ Δ = O ∩ sheet := by
    obtain ⟨O, hO, hOeq⟩ := isOpen_induced_iff.1
      ((hΔ'o.preimage continuous_subtype_val).preimage β.continuous)
    refine ⟨O, hO, ?_⟩
    ext y
    refine ⟨fun hy ↦ ⟨?_, hΔs hy⟩, fun ⟨hyO, hys⟩ ↦ ?_⟩
    · obtain ⟨y', hy', rfl⟩ := hy
      rw [← hOeq] at hy'; exact hy'
    · refine ⟨⟨y, hys⟩, ?_, rfl⟩
      rw [← hOeq]; exact hyO
  have hΔc : IsPreconnected Δ := by
    have : PreconnectedSpace Δ' := Subtype.preconnectedSpace hΔ'c
    have hrange : Set.range (fun t : Δ' ↦ ((β.symm ⟨t, hΔ'B t.2⟩ : sheet) : Ys)) = Δ := by
      ext y
      constructor
      · rintro ⟨t, rfl⟩
        refine ⟨β.symm ⟨t, hΔ'B t.2⟩, ?_, rfl⟩
        change ((β (β.symm _) : Bo) : Bs) ∈ Δ'
        rw [β.apply_symm_apply]; exact t.2
      · rintro ⟨y', hy', rfl⟩
        refine ⟨⟨β y', hy'⟩, ?_⟩
        simp
    rw [← hrange]
    exact isPreconnected_range (continuous_subtype_val.comp
      (β.symm.continuous.comp (continuous_subtype_val.subtype_mk _)))
  -- constancy of the sheet condition along the slices
  have hconst : ∀ u : Ub, (u : X) ∈ Eset → ∀ (t : Δ₁) (ht : (t : Bs) ∈ Δ'),
      (Rz (ι (Φ₁ (u, t))) ∈ sheet ↔ Rz (ι u) ∈ sheet) := by
    intro u hu t ht
    have : PreconnectedSpace Δ' := Subtype.preconnectedSpace hΔ'c
    let φ : Δ' → ↥(Eset ∩ G ⁻¹' Bo) := fun s ↦
      ⟨Φ₁ (u, ⟨s, hΔ'₁ s.2⟩), (hΦE _).2 hu, by
        change G (Φ₁ (u, ⟨s, hΔ'₁ s.2⟩)) ∈ Bo
        rw [hΦg]; exact hΔ'B s.2⟩
    have hφ : Continuous φ := by
      refine Continuous.subtype_mk (continuous_subtype_val.comp (Φ₁.continuous.comp ?_)) _
      exact Continuous.prodMk_right u |>.comp
        (continuous_subtype_val.subtype_mk _) |>.congr fun _ ↦ rfl
    have h := isClopen_iff.1 (hcl.preimage hφ)
    have hb' : (φ ⟨bB, hbΔ'⟩ : X) = u := hΦb u
    have ht' : (φ ⟨t, ht⟩ : X) = Φ₁ (u, t) := rfl
    change Rz (ι (φ ⟨t, ht⟩ : X)) ∈ sheet ↔ Rz (ι u) ∈ sheet
    conv_rhs => rw [← hb']
    rcases h with h | h
    · have h1 : (⟨t, ht⟩ : Δ') ∉ φ ⁻¹' _ := h ▸ Set.notMem_empty _
      have h2 : (⟨bB, hbΔ'⟩ : Δ') ∉ φ ⁻¹' _ := h ▸ Set.notMem_empty _
      exact iff_of_false h1 h2
    · have h1 : (⟨t, ht⟩ : Δ') ∈ φ ⁻¹' _ := h ▸ Set.mem_univ _
      have h2 : (⟨bB, hbΔ'⟩ : Δ') ∈ φ ⁻¹' _ := h ▸ Set.mem_univ _
      exact iff_of_true h1 h2
  -- the slice map `κ : Fs_b → Ub`
  have hκex : ∀ z : ↥(Fs ∩ Rz ⁻¹' {b}), ∃ w : Ub, ι w = z := fun z ↦ by
    obtain ⟨w, hw⟩ := hW z z.2.1 (by rw [z.2.2]; exact hb)
    have hwE : w ∈ Eset := (hEF w).1 (hw ▸ z.2.1)
    have hws : Rz (ι w) ∈ sheet := by rw [hw, z.2.2]; exact hb
    refine ⟨⟨w, hEb ⟨hwE, ?_⟩⟩, hw⟩
    rw [Set.mem_preimage, Set.mem_singleton_iff, hreal w hwE hws]
    have hwb : (⟨Rz (ι w), hws⟩ : sheet) = ⟨b, hb⟩ := Subtype.ext (by change Rz (ι w) = b; rw [hw]; exact z.2.2)
    rw [hwb]
  choose κ hκ using hκex
  have hκE : ∀ z, ((κ z : Ub) : X) ∈ Eset := fun z ↦ (hEF _).1 (by rw [hκ]; exact z.2.1)
  have hκs : ∀ z, Rz (ι (κ z : X)) ∈ sheet := fun z ↦ by rw [hκ, z.2.2]; exact hb
  have hιc : ∀ {A : Type _} [TopologicalSpace A] (f : A → X), Continuous (ι ∘ f) →
      Continuous f := fun f h ↦ hι.continuous_iff.2 h
  have hκc : Continuous κ :=
    Continuous.subtype_mk (hιc (fun z ↦ (κ z : X)) (by
      convert (continuous_subtype_val : Continuous fun z : ↥(Fs ∩ Rz ⁻¹' {b}) ↦ (z : Zs))
        using 1
      funext z; exact hκ z)) _
  have hκe : IsEmbedding κ := by
    refine IsEmbedding.of_comp hκc (hι.continuous.comp continuous_subtype_val) ?_
    convert IsEmbedding.subtypeVal (p := fun z ↦ z ∈ Fs ∩ Rz ⁻¹' {b}) using 1
    funext z; exact hκ z
  -- the base map `τ : Δ → Δ₁`
  let τ : Δ → Δ₁ := fun t ↦ ⟨β ⟨t, hΔs t.2⟩, hΔ'₁ ((hmemΔ _ _).1 t.2)⟩
  have hτc : Continuous τ := Continuous.subtype_mk (continuous_subtype_val.comp
    (β.continuous.comp (continuous_subtype_val.subtype_mk _))) _
  have hτe : IsEmbedding τ := by
    refine IsEmbedding.of_comp hτc continuous_subtype_val ?_
    have : (Subtype.val ∘ τ) = Subtype.val ∘ β ∘ Set.inclusion hΔs := rfl
    rw [this]
    exact IsEmbedding.subtypeVal.comp (β.isEmbedding.comp
      (IsEmbedding.inclusion hΔs))
  have hτΔ' : ∀ t, ((τ t : Δ₁) : Bs) ∈ Δ' := fun t ↦ (hmemΔ _ _).1 t.2
  -- the product map
  let Ψ : ↥(Fs ∩ Rz ⁻¹' {b}) × Δ → Zs := fun p ↦ ι (Φ₁ (κ p.1, τ p.2))
  have hΨe : IsEmbedding Ψ :=
    (hι.comp IsEmbedding.subtypeVal).comp (Φ₁.isEmbedding.comp (hκe.prodMap hτe))
  have hΨs : ∀ p : ↥(Fs ∩ Rz ⁻¹' {b}) × Δ, Rz (Ψ p) ∈ sheet := fun p ↦
    (hconst (κ p.1) (hκE p.1) (τ p.2) (hτΔ' p.2)).2 (hκs p.1)
  have hΨE : ∀ p : ↥(Fs ∩ Rz ⁻¹' {b}) × Δ, ((Φ₁ (κ p.1, τ p.2) : U) : X) ∈ Eset := fun p ↦ (hΦE _).2 (hκE p.1)
  have hΨR : ∀ p : ↥(Fs ∩ Rz ⁻¹' {b}) × Δ, Rz (Ψ p) = p.2 := fun p ↦ by
    have h1 := hreal _ (hΨE p) (hΨs p)
    rw [hΦg] at h1
    exact (hβinj _ _ (hΔs p.2.2) (hΨs p) h1).symm
  have hrange : Set.range Ψ = Fs ∩ Rz ⁻¹' Δ := by
    ext z'
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨(hEF _).2 (hΨE p), by rw [Set.mem_preimage, hΨR]; exact p.2.2⟩
    · rintro ⟨hz'F, hz'Δ⟩
      obtain ⟨w, rfl⟩ := hW z' hz'F (hΔs hz'Δ)
      have hwE := (hEF w).1 hz'F
      have hws : Rz (ι w) ∈ sheet := hΔs hz'Δ
      have hGw := hreal w hwE hws
      have hGΔ' : G w ∈ Δ' := by rw [hGw]; exact (hmemΔ _ _).1 hz'Δ
      set q := Φ₁.symm ⟨w, hEU ⟨hwE, hΔ'₁ hGΔ'⟩⟩ with hq
      have hΦq : (Φ₁ q : X) = w := by rw [hq, Homeomorph.apply_symm_apply]
      have hq2 : (q.2 : Bs) = G w := by rw [← hΦg q, hΦq]
      have hq2' : (q.2 : Bs) ∈ Δ' := hq2 ▸ hGΔ'
      have hu : ((q.1 : Ub) : X) ∈ Eset := (hΦE q).1 (hΦq ▸ hwE)
      have hus : Rz (ι q.1) ∈ sheet := by
        have h := (hconst q.1 hu q.2 hq2').1
        rw [show ((q.1, q.2) : Ub × Δ₁) = q from rfl, hΦq] at h
        exact h hws
      have hub : Rz (ι q.1) = b := by
        have h1 := hreal _ hu hus
        rw [hUb q.1.2] at h1
        exact (hβinj _ _ hb hus h1).symm
      let z₀ : ↥(Fs ∩ Rz ⁻¹' {b}) := ⟨ι q.1, (hEF _).2 hu, hub⟩
      have hκz₀ : κ z₀ = q.1 := Subtype.ext (hι.injective (hκ z₀))
      have hτ : τ ⟨Rz (ι w), hz'Δ⟩ = q.2 := by
        apply Subtype.ext
        change (β ⟨Rz (ι w), _⟩ : Bs) = q.2
        rw [hq2, hGw]
      refine ⟨(z₀, ⟨Rz (ι w), hz'Δ⟩), ?_⟩
      change ι (Φ₁ (κ z₀, τ ⟨Rz (ι w), hz'Δ⟩)) = ι w
      rw [hκz₀, hτ, show ((q.1, q.2) : Ub × Δ₁) = q from rfl, hΦq]
  let Φ := hΨe.toHomeomorph.trans (Homeomorph.setCongr hrange)
  refine ⟨Δ, hΔN, hΔopen, hΔc, hbΔ, Φ, fun p ↦ hΨR p, fun z ↦ ?_, fun e he p ↦ ?_⟩
  · change ι (Φ₁ (κ z, τ ⟨b, hbΔ⟩)) = z
    have : τ ⟨b, hbΔ⟩ = ⟨bB, hbΔ₁⟩ := rfl
    rw [this, hΦb, hκ]
  · obtain ⟨K, hK, hKe⟩ := hEk e he
    change ι (Φ₁ (κ p.1, τ p.2)) ∈ Ek e ↔ (p.1 : Zs) ∈ Ek e
    rw [hKe, ← hκ p.1, hKe]
    exact exists_congr fun k ↦ and_congr_right fun hk ↦ hΦD k (hK hk) (κ p.1, τ p.2)

end SheetRestriction

variable {Z Y : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))] [IsComplexScheme Z]
  [CompactSpace Z] [IsLocallyNoetherian Z] [IsNormal Z] [IsIntegral Y] [IsLocallyNoetherian Y]
  [IsNormal Y] {r : Z ⟶ Y} [r.IsOver (Spec (.of ℂ))] {F D : Divisor Z}

/-! ### Charts of the exceptional family -/

open MMP.Analytic MMP.Analytic.ComplexPoints in
/-- An *exceptional chart* at `b ∈ (U₀ ∩ T)(ℂ)`: a smooth open `W ⊆ Z` with a morphism `g` to a
smooth complex curve `B`, such that the trace on `W` of the components of `F` is an snc divisor
`∑_{E' ∈ s} E'` all of whose strata are smooth over `B` and proper over `B^an`; a neighbourhood
`sheet` of `b` in `(U₀ ∩ T)(ℂ)` mapping homeomorphically onto an open `B_o ⊆ B^an`, such that
the points of `F` over `sheet` lie in `W`, are an open and closed part of the points of the trace
over `B_o`, and are sent by `g` to the image of their point of `sheet`. -/
structure ExceptionalChart (r : Z ⟶ Y) [r.IsOver (Spec (.of ℂ))] (F : Divisor Z)
    (T : IrreducibleCloseds Y) (U₀ : Y.Opens) (b : UnderlyingSpace ℂ Y) where
  /-- The base curve. -/
  B : Scheme.{0}
  /-- Its structure morphism. -/
  sB : B ⟶ Spec (.of ℂ)
  /-- `B` is locally of finite type over `ℂ`. -/
  lft : LocallyOfFiniteType sB
  sep : IsSeparated sB
  /-- `B` is quasi-compact over `ℂ`. -/
  qc : QuasiCompact sB
  /-- `B` is smooth of relative dimension `1` over `ℂ`. -/
  smooth : SmoothOfRelativeDimension 1 sB
  /-- The smooth open of `Z`. -/
  W : Z.Opens
  /-- `W` is locally of finite type over `ℂ`. -/
  lftW : LocallyOfFiniteType (W.ι ≫ Z ↘ Spec (.of ℂ))
  sepW : IsSeparated (W.ι ≫ Z ↘ Spec (.of ℂ))
  /-- `W` is quasi-compact over `ℂ`. -/
  qcW : QuasiCompact (W.ι ≫ Z ↘ Spec (.of ℂ))
  /-- `W` is smooth over `ℂ`. -/
  smoothW : Smooth (W.ι ≫ Z ↘ Spec (.of ℂ))
  /-- The function to the curve. -/
  g : W.toScheme ⟶ B
  hg : g ≫ sB = W.ι ≫ Z ↘ Spec (.of ℂ)
  /-- The trace of `F` on `W`. -/
  s : Finset (Mori.PrimeDivisor W)
  isSNC : Mori.DivisorWithCoeffs.IsSNC (W.ι ≫ Z ↘ Spec (.of ℂ))
    (∑ E ∈ s, Finsupp.single E (1 : ℤ))
  smooth_strata : ∀ J ⊆ s, Smooth ((⨆ E ∈ J, E.idealSheaf).subschemeι ≫ g)
  isProperMap : IsProperMap ({w : ComplexPoints (W.ι ≫ Z ↘ Spec (.of ℂ)) |
    toScheme w ∈ ⋃ E ∈ s, (E.support : Set W)}.domRestrict (realize g hg))
  trace_eq : ∀ E ∈ F.support, ∃ sE ⊆ s,
    W.ι.base ⁻¹' (E.support : Set Z) = ⋃ E' ∈ sE, (E'.support : Set W)
  trace_supp : W.ι.base ⁻¹' (F.supp : Set Z) = ⋃ E' ∈ s, (E'.support : Set W)
  /-- The sheet of `T` through `b`. -/
  sheet : Set (UnderlyingSpace ℂ Y)
  isOpen_sheet : ∃ O, IsOpen O ∧ sheet = O ∩ pointsOver (K := ℂ) ((U₀ : Set Y) ∩ T)
  mem_sheet : b ∈ sheet
  /-- Its image in the base curve. -/
  Bo : Set (ComplexPoints sB)
  isOpen_Bo : IsOpen Bo
  /-- The homeomorphism of `sheet` onto `Bo`. -/
  β : sheet ≃ₜ Bo
  mem_W : ∀ z ∈ pointsOver (K := ℂ) (F.supp : Set Z), mapFun r z ∈ sheet →
    ∃ w : ComplexPoints (W.ι ≫ Z ↘ Spec (.of ℂ)),
      homeomorphUnderlyingSpace (realize W.ι rfl w) = z
  isClopen_sheet : IsClopen {w : ↥({w : ComplexPoints (W.ι ≫ Z ↘ Spec (.of ℂ)) |
      toScheme w ∈ ⋃ E ∈ s, (E.support : Set W)} ∩ realize g hg ⁻¹' Bo) |
    mapFun r (homeomorphUnderlyingSpace (realize W.ι rfl (w : ComplexPoints _))) ∈ sheet}
  realize_eq : ∀ w : ComplexPoints (W.ι ≫ Z ↘ Spec (.of ℂ)),
    toScheme w ∈ ⋃ E ∈ s, (E.support : Set W) →
    ∀ hw : mapFun r (homeomorphUnderlyingSpace (realize W.ι rfl w)) ∈ sheet,
      (realize g hg w : ComplexPoints sB) = β ⟨_, hw⟩

open MMP.Analytic MMP.Analytic.ComplexPoints in
/-- An *algebraic exceptional chart* at `b`: an open `X ⊆ U₀` of `Y` around `b` with a morphism
`φ : X ⟶ B` to a smooth complex curve, finite étale on a closed subscheme `C ⊆ X` with support
`X ∩ T`; a smooth open `W ⊆ r⁻¹(X)` containing `F ∩ r⁻¹(X)`, which lies over `T`, on which the
trace of the components of `F` is an snc divisor `∑_{E' ∈ s} E'` all of whose strata are smooth
over `B` by `φ ∘ r`. -/
structure ExceptionalAlgebraicChart (r : Z ⟶ Y) [r.IsOver (Spec (.of ℂ))] (F : Divisor Z)
    (T : IrreducibleCloseds Y) (U₀ : Y.Opens) (b : UnderlyingSpace ℂ Y) where
  /-- The base curve. -/
  B : Scheme.{0}
  /-- Its structure morphism. -/
  sB : B ⟶ Spec (.of ℂ)
  /-- `B` is locally of finite type over `ℂ`. -/
  lft : LocallyOfFiniteType sB
  sep : IsSeparated sB
  /-- `B` is quasi-compact over `ℂ`. -/
  qc : QuasiCompact sB
  /-- `B` is smooth of relative dimension `1` over `ℂ`. -/
  smooth : SmoothOfRelativeDimension 1 sB
  /-- The open of `Y` around `b`. -/
  X : Y.Opens
  le_U₀ : X ≤ U₀
  mem_X : b ∈ pointsOver (K := ℂ) (X : Set Y)
  /-- `X` is locally of finite type over `ℂ`. -/
  lftX : LocallyOfFiniteType (X.ι ≫ Y ↘ Spec (.of ℂ))
  /-- `X` is quasi-compact over `ℂ`. -/
  qcX : QuasiCompact (X.ι ≫ Y ↘ Spec (.of ℂ))
  /-- The function to the curve. -/
  φ : X.toScheme ⟶ B
  hφ : φ ≫ sB = X.ι ≫ Y ↘ Spec (.of ℂ)
  /-- The closed subscheme with support `X ∩ T`. -/
  C : Scheme.{0}
  /-- The closed immersion of `C` into `X`. -/
  iC : C ⟶ X.toScheme
  isClosedImmersion : IsClosedImmersion iC
  range_iC : X.ι.base '' Set.range iC.base = (X : Set Y) ∩ T
  sepC : IsSeparated (iC ≫ X.ι ≫ Y ↘ Spec (.of ℂ))
  finite : IsFinite (iC ≫ φ)
  /-- `C` is étale over `B` by `φ`. -/
  etale : Etale (iC ≫ φ)
  /-- The smooth open of `Z`. -/
  W : Z.Opens
  /-- `W` is locally of finite type over `ℂ`. -/
  lftW : LocallyOfFiniteType (W.ι ≫ Z ↘ Spec (.of ℂ))
  sepW : IsSeparated (W.ι ≫ Z ↘ Spec (.of ℂ))
  /-- `W` is quasi-compact over `ℂ`. -/
  qcW : QuasiCompact (W.ι ≫ Z ↘ Spec (.of ℂ))
  /-- `W` is smooth over `ℂ`. -/
  smoothW : Smooth (W.ι ≫ Z ↘ Spec (.of ℂ))
  /-- `r` on `W`, as a morphism to `X`. -/
  ρ : W.toScheme ⟶ X.toScheme
  hρ : ρ ≫ X.ι = W.ι ≫ r
  supp_subset_W : r.base ⁻¹' X ∩ F.supp ⊆ W
  supp_inter_eq : r.base ⁻¹' X ∩ F.supp = r.base ⁻¹' ((X : Set Y) ∩ T)
  /-- The trace of `F` on `W`. -/
  s : Finset (Mori.PrimeDivisor W)
  isSNC : Mori.DivisorWithCoeffs.IsSNC (W.ι ≫ Z ↘ Spec (.of ℂ))
    (∑ E ∈ s, Finsupp.single E (1 : ℤ))
  smooth_strata : ∀ J ⊆ s, Smooth ((⨆ E ∈ J, E.idealSheaf).subschemeι ≫ ρ ≫ φ)
  trace_eq : ∀ E ∈ F.support, ∃ sE ⊆ s,
    W.ι.base ⁻¹' (E.support : Set Z) = ⋃ E' ∈ sE, (E'.support : Set W)
  trace_supp : W.ι.base ⁻¹' (F.supp : Set Z) = ⋃ E' ∈ s, (E'.support : Set W)

/-- The function `φ ∘ r : W ⟶ B` of an algebraic exceptional chart is a morphism over `ℂ`. -/
theorem ExceptionalAlgebraicChart.comp_eq {T : IrreducibleCloseds Y} {U₀ : Y.Opens}
    {b : UnderlyingSpace ℂ Y} (a : ExceptionalAlgebraicChart r F T U₀ b) :
    (a.ρ ≫ a.φ) ≫ a.sB = a.W.ι ≫ Z ↘ Spec (.of ℂ) := by
  rw [Category.assoc, a.hφ, ← Category.assoc, a.hρ, Category.assoc, comp_over r]

open MMP.Analytic MMP.Analytic.ComplexPoints in
/-- **The trace of `F` on an algebraic exceptional chart is proper over the base curve.** The
points of `F` over `X` are those of `r⁻¹(C)`, proper over `C` by `r`, and `C` is finite over
`B`. -/
theorem ExceptionalAlgebraicChart.isProperMap [IsProper r] {T : IrreducibleCloseds Y}
    {U₀ : Y.Opens} {b : UnderlyingSpace ℂ Y} (a : ExceptionalAlgebraicChart r F T U₀ b) :
    IsProperMap ({w : ComplexPoints (a.W.ι ≫ Z ↘ Spec (.of ℂ)) |
      toScheme w ∈ ⋃ E ∈ a.s, (E.support : Set a.W)}.domRestrict
        (realize (a.ρ ≫ a.φ) a.comp_eq)) := by
  have hg := a.comp_eq
  classical
  obtain ⟨B, sB, hlft, hsep, hqc, hsm, X, hXU, hbX, hlftX, hqcX, φ, hφ, C, iC, hiC, hrange,
    hsepC, hfin, het, W, hlftW, hsepW, hqcW, hsmW, ρ, hρ, hFW, hFT, s, hsnc, hstr, htr,
    hsupp⟩ := a
  let sY : Y ⟶ Spec (.of ℂ) := Y ↘ Spec (.of ℂ)
  let sZ : Z ⟶ Spec (.of ℂ) := Z ↘ Spec (.of ℂ)
  let sX : X.toScheme ⟶ Spec (.of ℂ) := X.ι ≫ sY
  have : LocallyOfFiniteType sX := hlftX
  have : QuasiCompact sX := hqcX
  have : LocallyOfFiniteType sB := hlft
  have : QuasiCompact sB := hqc
  have : IsClosedImmersion iC := hiC
  have : IsFinite (iC ≫ φ) := hfin
  have hρpt : ∀ x : W, X.ι (ρ x) = r (W.ι x) := fun x ↦
    congrArg (fun f : W.toScheme ⟶ Y ↦ f x) hρ
  have hWle : W ≤ r ⁻¹ᵁ X := fun z hz ↦ by
    obtain ⟨w', rfl⟩ : z ∈ Set.range W.ι.base := (Scheme.Opens.range_ι W).ge hz
    change r (W.ι w') ∈ (X : Set Y)
    convert ((Scheme.Opens.range_ι X).le ⟨ρ w', rfl⟩ : X.ι (ρ w') ∈ (X : Set Y)) using 1
    exact (hρpt w').symm
  let f : (r ⁻¹ᵁ X).toScheme ⟶ X.toScheme := r ∣_ X
  let j : W.toScheme ⟶ (r ⁻¹ᵁ X).toScheme := Z.homOfLE hWle
  have hjf : j ≫ f = ρ := by
    rw [← cancel_mono X.ι, Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι_assoc, hρ]
  have hρs : ρ ≫ sX = W.ι ≫ sZ := by
    change ρ ≫ X.ι ≫ sY = W.ι ≫ sZ
    rw [← Category.assoc, hρ, Category.assoc, comp_over r]
  have hj : j ≫ f ≫ sX = W.ι ≫ sZ := by rw [← Category.assoc, hjf, hρs]
  let J := realize (sX := W.ι ≫ sZ) (sY := f ≫ sX) j hj
  have hJ : IsOpenEmbedding J := isOpenEmbedding_realize_of_isOpenImmersion j hj
  set Etr : Set (ComplexPoints (W.ι ≫ sZ)) := {w | toScheme w ∈ ⋃ E ∈ s, (E.support : Set W)}
    with hEtr
  set Dom : Set (ComplexPoints (f ≫ sX)) :=
    realize f rfl ⁻¹' Set.range (realize (sX := iC ≫ sX) (sY := sX) iC rfl) with hDom
  have hzX : ∀ z : (r ⁻¹ᵁ X).toScheme, r ((r ⁻¹ᵁ X).ι z) ∈ (X : Set Y) := fun z ↦
    (Scheme.Opens.range_ι (r ⁻¹ᵁ X)).le ⟨z, rfl⟩
  -- a point of `r⁻¹(X)` lies over `C` iff it lies in `F`
  have hmemC : ∀ z : (r ⁻¹ᵁ X).toScheme, f z ∈ Set.range iC.base ↔
      (r ⁻¹ᵁ X).ι z ∈ (F.supp : Set Z) := by
    intro z
    have hfz : X.ι (f z) = r ((r ⁻¹ᵁ X).ι z) :=
      congrArg (fun g : (r ⁻¹ᵁ X).toScheme ⟶ Y ↦ g z) (morphismRestrict_ι r X)
    constructor
    · intro h
      have h1 : X.ι (f z) ∈ X.ι.base '' Set.range iC.base := ⟨_, h, rfl⟩
      rw [hrange, hfz] at h1
      exact ((Set.ext_iff.1 hFT _).2 h1).2
    · intro h
      have h1 : r ((r ⁻¹ᵁ X).ι z) ∈ (X : Set Y) ∩ T := (Set.ext_iff.1 hFT _).1 ⟨hzX z, h⟩
      rw [← hfz, ← hrange] at h1
      obtain ⟨y, hy, hyx⟩ := h1
      obtain rfl : y = f z := X.ι.isOpenEmbedding.injective hyx
      exact hy
  have hDom' : ∀ q, q ∈ Dom ↔ (r ⁻¹ᵁ X).ι (toScheme q) ∈ (F.supp : Set Z) := fun q ↦ by
    rw [hDom, Set.mem_preimage, mem_range_realize_iff_of_isClosedImmersion]
    exact hmemC _
  have hJE : ∀ w, J w ∈ Dom ↔ w ∈ Etr := fun w ↦ by
    rw [hDom', hEtr, Set.mem_setOf_eq, ← hsupp, Set.mem_preimage]
    change (r ⁻¹ᵁ X).ι (j (toScheme w)) ∈ _ ↔ _
    rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
  have hrJ : Set.range (J ∘ Subtype.val : Etr → ComplexPoints (f ≫ sX)) = Dom := by
    ext q
    constructor
    · rintro ⟨w, rfl⟩; exact (hJE w.1).2 w.2
    · intro hq
      have hqW : (r ⁻¹ᵁ X).ι (toScheme q) ∈ W := hFW ⟨hzX _, (hDom' q).1 hq⟩
      obtain ⟨w, rfl⟩ : q ∈ Set.range J := by
        rw [range_realize_of_isOpenImmersion, Scheme.opensRange_homOfLE]
        exact hqW
      exact ⟨⟨w, (hJE w).1 hq⟩, rfl⟩
  let hom : Etr ≃ₜ Dom :=
    (hJ.isEmbedding.comp IsEmbedding.subtypeVal).toHomeomorph.trans (Homeomorph.setCongr hrJ)
  have key : Etr.domRestrict (realize (ρ ≫ φ) hg) =
      Dom.domRestrict (realize (sX := f ≫ sX) (sY := sB) (f ≫ φ) (by rw [Category.assoc, hφ])) ∘
        hom := by
    funext w
    ext1
    change w.1.hom ≫ ρ ≫ φ = (w.1.hom ≫ j) ≫ f ≫ φ
    rw [Category.assoc, ← Category.assoc j, hjf]
  rw [key]
  exact (isProperMap_restrict_realize_preimage_range f iC φ hφ).comp hom.isProperMap

open MMP.Analytic MMP.Analytic.ComplexPoints in
/-- **Exceptional charts from algebraic ones.** An algebraic exceptional chart at
`b ∈ (U₀ ∩ T)(ℂ)` yields an exceptional chart at `b`. -/
theorem nonempty_exceptionalChart_of_algebraicChart [IsProper r] {T : IrreducibleCloseds Y}
    {U₀ : Y.Opens}
    {b : UnderlyingSpace ℂ Y} (hbT : b ∈ pointsOver (K := ℂ) ((U₀ : Set Y) ∩ T))
    (a : ExceptionalAlgebraicChart r F T U₀ b) : Nonempty (ExceptionalChart r F T U₀ b) := by
  classical
  have hprop := a.isProperMap
  have hg := a.comp_eq
  obtain ⟨B, sB, hlft, hsep, hqc, hsm, X, hXU, hbX, hlftX, hqcX, φ, hφ, C, iC, hiC, hrange,
    hsepC, hfin, het, W, hlftW, hsepW, hqcW, hsmW, ρ, hρ, hFW, hFT, s, hsnc, hstr, htr,
    hsupp⟩ := a
  let sY : Y ⟶ Spec (.of ℂ) := Y ↘ Spec (.of ℂ)
  let sZ : Z ⟶ Spec (.of ℂ) := Z ↘ Spec (.of ℂ)
  let sX : X.toScheme ⟶ Spec (.of ℂ) := X.ι ≫ sY
  let sC : C ⟶ Spec (.of ℂ) := iC ≫ sX
  have : SmoothOfRelativeDimension 1 sB := hsm
  have : LocallyOfFiniteType sC := inferInstanceAs (LocallyOfFiniteType (iC ≫ sX))
  have : QuasiCompact sC := inferInstanceAs (QuasiCompact (iC ≫ sX))
  have : IsSeparated sC := hsepC
  let ψ : C ⟶ B := iC ≫ φ
  have hψ : ψ ≫ sB = sC := by
    change (iC ≫ φ) ≫ sB = iC ≫ X.ι ≫ sY
    rw [Category.assoc, hφ]
  have : LocallyOfFiniteType sX := hlftX
  have : QuasiCompact sX := hqcX
  have hiCe : IsClosedEmbedding (realize (sX := sC) (sY := sX) iC rfl) := by
    have hp := (isSeparatedMap_and_isProperMap_realize (sX := sC) (sS := sX) iC rfl).2
    have hinj : Function.Injective (realize (sX := sC) (sY := sX) iC rfl) := fun t t' htt ↦
      ComplexPoints.ext ((cancel_mono iC).1 (congrArg (fun y : ComplexPoints sX ↦ y.hom) htt))
    exact IsClosedEmbedding.of_continuous_injective_isClosedMap hp.continuous hinj hp.isClosedMap
  -- the inclusion `γ : C(ℂ) → Y(ℂ)`
  let γ : ComplexPoints sC → UnderlyingSpace ℂ Y := fun c ↦
    homeomorphUnderlyingSpace (realize X.ι rfl (realize iC rfl c))
  have hγ : IsEmbedding γ := (homeomorphUnderlyingSpace (X := Y)).isEmbedding.comp
    ((isOpenEmbedding_realize_ι (sX := sY) X).isEmbedding.comp
      hiCe.isEmbedding)
  have hγpt : ∀ c (S : Set Y), γ c ∈ pointsOver (K := ℂ) S ↔
      X.ι (iC (toScheme c)) ∈ S := by
    intro c S
    rw [mem_pointsOver, Subsingleton.elim (α := Spec (.of ℂ)) (IsLocalRing.closedPoint ℂ) default]
    rfl
  let ι : ComplexPoints (W.ι ≫ sZ) → UnderlyingSpace ℂ Z := fun w ↦
    homeomorphUnderlyingSpace (realize W.ι rfl w)
  have hιpt : ∀ w (S : Set Z), ι w ∈ pointsOver (K := ℂ) S ↔ W.ι (toScheme w) ∈ S := by
    intro w S
    rw [mem_pointsOver, Subsingleton.elim (α := Spec (.of ℂ)) (IsLocalRing.closedPoint ℂ) default]
    rfl
  have hρs : ρ ≫ sX = W.ι ≫ sZ := by
    change ρ ≫ X.ι ≫ sY = W.ι ≫ sZ
    rw [← Category.assoc, hρ, Category.assoc, comp_over r]
  have hrι : ∀ w, mapFun r (ι w) =
      homeomorphUnderlyingSpace (realize X.ι rfl (realize ρ hρs w)) := fun w ↦ by
    apply MMP.UnderlyingSpace.ext
    change w.hom ≫ W.ι ≫ r = w.hom ≫ ρ ≫ X.ι
    rw [hρ]
  -- `γ` has range `(X ∩ T)(ℂ)`
  have hγr : Set.range γ = pointsOver (K := ℂ) ((X : Set Y) ∩ T) := by
    ext z
    constructor
    · rintro ⟨c, rfl⟩
      rw [hγpt, ← hrange]
      exact ⟨_, ⟨_, rfl⟩, rfl⟩
    · intro hz
      obtain ⟨z', rfl⟩ := (homeomorphUnderlyingSpace (X := Y)).surjective z
      have hz' : toScheme z' ∈ (X : Set Y) ∩ T := by
        rw [mem_pointsOver, Subsingleton.elim (α := Spec (.of ℂ)) (IsLocalRing.closedPoint ℂ)
          default] at hz
        exact hz
      obtain ⟨x, rfl⟩ : z' ∈ Set.range (realize (sX := sX) X.ι rfl) := by
        rw [range_realize_ι]; exact hz'.1
      have hx : toScheme x ∈ Set.range iC.base := by
        have hz'' := hz'
        rw [← hrange] at hz''
        obtain ⟨y, hy, hyx⟩ := hz''
        obtain rfl : y = toScheme x := X.ι.isOpenEmbedding.injective hyx
        exact hy
      obtain ⟨c, rfl⟩ := (mem_range_realize_iff_of_isClosedImmersion (sX := sX) iC x).2 hx
      exact ⟨c, rfl⟩
  obtain ⟨cb, hcb⟩ : b ∈ Set.range γ := hγr ▸ ⟨hbX, hbT.2⟩
  -- an evenly covered neighbourhood of `ψ(cb)`
  have : IsFinite ψ := hfin
  have : Etale ψ := het
  let p := realize ψ hψ
  obtain ⟨hdisc, Bo, hbBo, hBo, hpre, H, hH⟩ :=
    isCoveringMap_realize_of_isFinite_of_etale (sT := sC) (sB := sB) ψ hψ (p cb)
  let cb' : ↥(p ⁻¹' Bo) := ⟨cb, hbBo⟩
  let i₀ := (H cb').2
  let P' : Set ↥(p ⁻¹' Bo) := {c | (H c).2 = i₀}
  have hP'cl : IsClopen P' := (isClopen_discrete {i₀}).preimage (continuous_snd.comp H.continuous)
  let θ : P' ≃ₜ Bo :=
    { toFun := fun c ↦ (H c.1).1
      invFun := fun u ↦ ⟨H.symm (u, i₀), by
        change (H (H.symm (u, i₀))).2 = i₀
        rw [H.apply_symm_apply]⟩
      left_inv := fun c ↦ by
        apply Subtype.ext
        have hc : (H c.1).2 = i₀ := c.2
        change H.symm ((H c.1).1, i₀) = c.1
        rw [← hc, Prod.mk.eta, H.symm_apply_apply]
      right_inv := fun u ↦ by
        change (H (H.symm (u, i₀))).1 = u
        rw [H.apply_symm_apply]
      continuous_toFun := (continuous_fst.comp H.continuous).comp continuous_subtype_val
      continuous_invFun :=
        (H.symm.continuous.comp (continuous_id.prodMk continuous_const)).subtype_mk fun u ↦ by
          change (H (H.symm (u, i₀))).2 = i₀
          rw [H.apply_symm_apply] }
  have hθ : ∀ c : P', (θ c : ComplexPoints sB) = p c.1.1 := fun c ↦ hH c.1
  -- the sheet `γ(P')` of `T` through `b`
  let γ' : P' → UnderlyingSpace ℂ Y := fun c ↦ γ c.1.1
  have hγ' : IsEmbedding γ' := hγ.comp (IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal)
  let e := hγ'.toHomeomorph
  have he : ∀ z : Set.range γ', γ (e.symm z).1.1 = z := fun z ↦
    congrArg Subtype.val (e.apply_symm_apply z)
  have hsheetO : ∃ O, IsOpen O ∧ Set.range γ' = O ∩ pointsOver (K := ℂ) ((U₀ : Set Y) ∩ T) := by
    have hP'' : IsOpen (Subtype.val '' P' : Set (ComplexPoints sC)) :=
      hpre.isOpenMap_subtype_val _ hP'cl.isOpen
    obtain ⟨O₁, hO₁, hO₁eq⟩ := hγ.isInducing.isOpen_iff.1 hP''
    have hXo : IsOpen (pointsOver (K := ℂ) (X : Set Y)) := by
      convert isOpen_setOf_le_preimage (K := ℂ) X using 1
      ext q
      exact (top_le_preimage_iff q X).symm
    refine ⟨O₁ ∩ pointsOver (K := ℂ) (X : Set Y), hO₁.inter hXo, ?_⟩
    ext z
    constructor
    · rintro ⟨c, rfl⟩
      have hm : γ c.1.1 ∈ pointsOver (K := ℂ) ((X : Set Y) ∩ T) := hγr ▸ ⟨_, rfl⟩
      refine ⟨⟨?_, hm.1⟩, hXU hm.1, hm.2⟩
      change c.1.1 ∈ γ ⁻¹' O₁
      rw [hO₁eq]
      exact ⟨c.1, c.2, rfl⟩
    · rintro ⟨⟨hz₁, hzX⟩, -, hzT⟩
      obtain ⟨c, rfl⟩ : z ∈ Set.range γ := hγr ▸ ⟨hzX, hzT⟩
      have hc : c ∈ γ ⁻¹' O₁ := hz₁
      rw [hO₁eq] at hc
      obtain ⟨c', hc', rfl⟩ := hc
      exact ⟨⟨c', hc'⟩, rfl⟩
  have hmemb : b ∈ Set.range γ' := ⟨⟨cb', rfl⟩, hcb⟩
  -- the point of `C` under a point of the trace
  have hcex : ∀ w : ComplexPoints (W.ι ≫ sZ), toScheme w ∈ ⋃ E ∈ s, (E.support : Set W) →
      ∃ c, realize (sX := sC) (sY := sX) iC rfl c = realize ρ hρs w := by
    intro w hw
    refine (mem_range_realize_iff_of_isClosedImmersion (sX := sX) iC _).2 ?_
    have hwF : W.ι (toScheme w) ∈ (F.supp : Set Z) := by
      rw [← Set.mem_preimage, hsupp]; exact hw
    have hrw : X.ι (ρ (toScheme w)) = r (W.ι (toScheme w)) :=
      congrArg (fun f : W.toScheme ⟶ Y ↦ f (toScheme w)) hρ
    have hX : r (W.ι (toScheme w)) ∈ (X : Set Y) := by
      rw [← hrw]; exact (Scheme.Opens.range_ι X).le ⟨_, rfl⟩
    have hT : X.ι (ρ (toScheme w)) ∈ (X : Set Y) ∩ T := by
      rw [hrw]; exact ⟨hX, ((Set.ext_iff.1 hFT _).1 ⟨hX, hwF⟩).2⟩
    rw [← hrange] at hT
    obtain ⟨y, hy, hyx⟩ := hT
    obtain rfl : y = ρ (toScheme w) := X.ι.isOpenEmbedding.injective hyx
    exact hy
  have : Nonempty (ComplexPoints sC) := ⟨cb⟩
  choose! c hc using hcex
  have hγc : ∀ w, toScheme w ∈ ⋃ E ∈ s, (E.support : Set W) → mapFun r (ι w) = γ (c w) :=
    fun w hw ↦ by rw [hrι]; exact congrArg _ (congrArg _ (hc w hw)).symm
  have hpc : ∀ w, toScheme w ∈ ⋃ E ∈ s, (E.support : Set W) →
      p (c w) = realize (ρ ≫ φ) hg w := fun w hw ↦ by
    ext1
    change (c w).hom ≫ iC ≫ φ = w.hom ≫ ρ ≫ φ
    rw [← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ φ) (congrArg ComplexPoints.hom (hc w hw))
  refine ⟨⟨B, sB, hlft, hsep, hqc, hsm, W, hlftW, hsepW, hqcW, hsmW, ρ ≫ φ, hg, s, hsnc, hstr,
    hprop, htr, hsupp, Set.range γ', hsheetO, hmemb, Bo, hBo, e.symm.trans θ, ?_, ?_, ?_⟩⟩
  · intro z hzF hzs
    obtain ⟨z', rfl⟩ := (homeomorphUnderlyingSpace (X := Z)).surjective z
    have hzs' : mapFun r (homeomorphUnderlyingSpace z') ∈
        pointsOver (K := ℂ) ((X : Set Y) ∩ T) := by
      rw [← hγr]; obtain ⟨q, hq⟩ := hzs; exact ⟨q.1.1, hq⟩
    have hpt : toScheme z' ∈ r.base ⁻¹' X ∩ F.supp := by
      rw [mem_pointsOver, Subsingleton.elim (α := Spec (.of ℂ)) (IsLocalRing.closedPoint ℂ)
        default] at hzF hzs'
      exact ⟨hzs'.1, hzF⟩
    obtain ⟨w, rfl⟩ : z' ∈ Set.range (realize (sX := W.ι ≫ sZ) W.ι rfl) := by
      rw [range_realize_ι]; exact hFW hpt
    exact ⟨w, rfl⟩
  · let Etr : Set (ComplexPoints (W.ι ≫ sZ)) :=
      {w | toScheme w ∈ ⋃ E ∈ s, (E.support : Set W)} ∩ realize (ρ ≫ φ) hg ⁻¹' Bo
    let κ : Etr → ↥(p ⁻¹' Bo) := fun w ↦
      ⟨c w, by change p (c w) ∈ Bo; rw [hpc w w.2.1]; exact w.2.2⟩
    have hκc : Continuous κ := by
      refine Continuous.subtype_mk ?_ _
      refine hiCe.isEmbedding.continuous_iff.2 ?_
      have : (realize (sX := sC) (sY := sX) iC rfl ∘ fun w : Etr ↦ c w) =
          realize ρ hρs ∘ Subtype.val := funext fun w ↦ hc w w.2.1
      rw [this]; exact (continuous_realize _ _).comp continuous_subtype_val
    convert hP'cl.preimage hκc using 1
    ext w
    change mapFun r (ι w.1) ∈ Set.range γ' ↔ κ w ∈ P'
    rw [hγc w.1 w.2.1]
    constructor
    · rintro ⟨q, hq⟩
      have : q.1 = κ w := Subtype.ext (hγ.injective hq)
      rw [← this]; exact q.2
    · intro h; exact ⟨⟨κ w, h⟩, rfl⟩
  · intro w hw hws
    change _ = (θ (e.symm ⟨_, hws⟩) : ComplexPoints sB)
    rw [hθ, ← hpc w hw]
    congr 1
    apply hγ.injective
    rw [he ⟨_, hws⟩]
    exact (hγc w hw).symm

/-- **The singular locus near a general point of `T`.** Over a general open `U` of the
singular curve `T`, the singular locus of `Y` is `T`. -/
theorem exists_open_singularLocus_inter_eq
    (hM : IsCurvePointExceptionalModel (Y ↘ Spec (.of ℂ)) r F D)
    (T : IrreducibleCloseds Y) (hTs : (T : Set Y) ⊆ (singularLocus (Y ↘ Spec (.of ℂ)) : Set Y))
    (hT1 : topologicalKrullDim (T : Set Y) = 1) :
    ∃ U : Y.Opens, ((U : Set Y) ∩ T).Nonempty ∧
      (U : Set Y) ∩ (singularLocus (Y ↘ Spec (.of ℂ)) : Set Y) = (U : Set Y) ∩ T := by
  classical
  haveI : IsProper r := (IsProjectiveMorphism.isProjective hM.isResolution.2.2.2.1).isProper
  haveI : IsDominant r := MMP.Mori.IsBirationalMorphism.isDominant hM.isResolution.2.2.2.2
  have hsurj : Function.Surjective r.base := by
    have h := r.denseRange.closure_range
    rw [r.isClosedMap.isClosed_range.closure_eq] at h
    exact Set.range_eq_univ.1 h
  set S : Set Y := (singularLocus (Y ↘ Spec (.of ℂ)) : Set Y) with hS
  let K : Mori.PrimeDivisor Z → Set Y := fun E ↦ r.base '' (E.support : Set Z)
  have hKcl : ∀ E : Mori.PrimeDivisor Z, IsClosed (K E) := fun E ↦ r.isClosedMap _ (by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isClosed_closure)
  have hKirr : ∀ E : Mori.PrimeDivisor Z, IsIrreducible (K E) := fun E ↦ by
    refine IsIrreducible.image ?_ _ r.continuous.continuousOn
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact isIrreducible_singleton.closure
  have hSK : S = ⋃ E ∈ F.support, K E := by
    ext y
    obtain ⟨z, rfl⟩ := hsurj y
    constructor
    · intro hy
      have hz : z ∈ (F.supp : Set Z) := by
        rw [hM.supp_eq_preimage_singularLocus]; exact hy
      rw [DivisorWithCoeffs.coe_supp] at hz
      obtain ⟨E, hE, hzE⟩ := Set.mem_iUnion₂.1 hz
      exact Set.mem_iUnion₂.2 ⟨E, hE, z, hzE, rfl⟩
    · intro hy
      obtain ⟨E, hE, w, hwE, hw⟩ := Set.mem_iUnion₂.1 hy
      have hw' : w ∈ (F.supp : Set Z) := by
        rw [DivisorWithCoeffs.coe_supp]; exact Set.mem_iUnion₂.2 ⟨E, hE, hwE⟩
      rw [hM.supp_eq_preimage_singularLocus] at hw'
      change r.base z ∈ S
      rw [← hw]; exact hw'
  -- every image `K E` containing `T` is `T`
  have hKT : ∀ E ∈ F.support, (T : Set Y) ⊆ K E → K E = T := fun E hE hTK ↦ by
    by_contra hne
    have hlt := MMP.topologicalKrullDim_lt_of_subset_of_ne (hKirr E) T.isClosed
      hTK (Ne.symm hne) (ne_top_of_le_ne_top (by decide) (hM.topologicalKrullDim_image_le E hE))
    rw [hT1] at hlt
    exact absurd (hlt.trans_le (hM.topologicalKrullDim_image_le E hE)) (lt_irrefl _)
  set J := F.support.filter fun E ↦ ¬ (T : Set Y) ⊆ K E with hJ
  have hJcl : IsClosed (⋃ E ∈ J, K E) :=
    Set.Finite.isClosed_biUnion J.finite_toSet fun E _ ↦ hKcl E
  refine ⟨⟨(⋃ E ∈ J, K E)ᶜ, hJcl.isOpen_compl⟩, ?_, ?_⟩
  · by_contra hne
    have hsub : (T : Set Y) ⊆ ⋃₀ ((J.image K : Finset (Set Y)) : Set (Set Y)) := by
      intro t ht
      by_contra htn
      refine hne ⟨t, ?_, ht⟩
      intro htJ
      obtain ⟨E, hE, htE⟩ := Set.mem_iUnion₂.1 htJ
      exact htn (Set.mem_sUnion.2 ⟨K E, Finset.mem_coe.2 (Finset.mem_image_of_mem K hE), htE⟩)
    obtain ⟨z, hz, hTz⟩ := (isIrreducible_iff_sUnion_isClosed.1 T.isIrreducible) (J.image K)
      (fun z hz ↦ by
        obtain ⟨E, -, rfl⟩ := Finset.mem_image.1 hz
        exact hKcl E) hsub
    obtain ⟨E, hE, rfl⟩ := Finset.mem_image.1 hz
    exact (Finset.mem_filter.1 hE).2 hTz
  · ext y
    simp only [Set.mem_inter_iff, Opens.coe_mk, Set.mem_compl_iff]
    refine ⟨fun ⟨hyU, hyS⟩ ↦ ⟨hyU, ?_⟩, fun ⟨hyU, hyT⟩ ↦ ⟨hyU, hTs hyT⟩⟩
    rw [hSK] at hyS
    obtain ⟨E, hE, hyE⟩ := Set.mem_iUnion₂.1 hyS
    by_cases hTE : (T : Set Y) ⊆ K E
    · rw [← hKT E hE hTE]; exact hyE
    · exact absurd (Set.mem_iUnion₂.2 ⟨E, Finset.mem_filter.2 ⟨hE, hTE⟩, hyE⟩) hyU

/-! ### Algebraic charts over a general open of `T` -/

section AlgebraicChart

/-- The complex affine line `𝔸¹ = Spec ℂ[t]`. -/
local notation "𝔸¹ℂ" => Spec (CommRingCat.of (MvPolynomial (Fin 1) ℂ))

/-- The structure morphism of `𝔸¹`. -/
local notation "s𝔸¹ℂ" => Spec.map (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin 1) ℂ)))

private theorem smoothOfRelativeDimension_one_affineLine :
    SmoothOfRelativeDimension 1 s𝔸¹ℂ := by
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)]
  apply RingHom.locally_of
  · exact RingHom.isStandardSmoothOfRelativeDimension_respectsIso
  · rw [CommRingCat.hom_ofHom, RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
    infer_instance

/-- `T` meets the open `X` of `Y` in a closed subscheme which is finite étale over `B` by `φ`. -/
private def HasFiniteEtaleTrace (T : Set Y) (X : Y.Opens) {B : Scheme.{0}}
    (φ : X.toScheme ⟶ B) : Prop :=
  ∃ (C : Scheme.{0}) (iC : C ⟶ X.toScheme), IsClosedImmersion iC ∧
    X.ι.base '' Set.range iC.base = (X : Set Y) ∩ T ∧
    IsSeparated (iC ≫ X.ι ≫ Y ↘ Spec (.of ℂ)) ∧ IsFinite (iC ≫ φ) ∧ Etale (iC ≫ φ)

/-- A function `g : V ⟶ A` on an open `V` of `Y`, over an open `B ⊆ A`, as a morphism from the
open `g⁻¹(B)` of `Y` to `B`. -/
private noncomputable def coordinateRestrict {A : Scheme.{0}} (V : Y.Opens)
    (g : V.toScheme ⟶ A) (B : A.Opens) : (V.ι ''ᵁ (g ⁻¹ᵁ B)).toScheme ⟶ B.toScheme :=
  (V.ι.isoImage (g ⁻¹ᵁ B)).inv ≫ g ∣_ B

private theorem coordinateRestrict_ι {A : Scheme.{0}} (V : Y.Opens) (g : V.toScheme ⟶ A)
    (B : A.Opens) :
    coordinateRestrict V g B ≫ B.ι = Y.homOfLE (V.ι_image_le _) ≫ g := by
  rw [coordinateRestrict, Category.assoc, morphismRestrict_ι, ← Category.assoc]
  congr 1
  rw [← cancel_mono V.ι]
  simp

/-- Formal smoothness of stalk maps along a square `q ≫ j = e ≫ p` with `e`, `j` open
immersions. -/
private theorem formallySmooth_stalkMap_of_comp_eq {S S₀ B B₀ : Scheme.{0}} {q : S ⟶ B}
    {p : S₀ ⟶ B₀} {e : S ⟶ S₀} {j : B ⟶ B₀} [IsOpenImmersion e] [IsOpenImmersion j]
    (h : q ≫ j = e ≫ p) (x : S) (hx : (p.stalkMap (e x)).hom.FormallySmooth) :
    (q.stalkMap x).hom.FormallySmooth := by
  haveI := IsOpenImmersion.instIsIsoCommRingCatStalkMap e x
  haveI := IsOpenImmersion.instIsIsoCommRingCatStalkMap j (q x)
  have h1 : ((e ≫ p).stalkMap x).hom.FormallySmooth := by
    rw [Scheme.Hom.stalkMap_comp]
    exact (RingHom.FormallySmooth.respectsIso.cancel_right_isIso _ (e.stalkMap x)).2 hx
  have h2 : ((q ≫ j).stalkMap x).hom.FormallySmooth := by
    rw [Scheme.Hom.stalkMap_congr_hom (q ≫ j) (e ≫ p) h x]
    exact (RingHom.FormallySmooth.respectsIso.cancel_left_isIso _ _).2 h1
  rw [Scheme.Hom.stalkMap_comp] at h2
  exact (RingHom.FormallySmooth.respectsIso.cancel_left_isIso (j.stalkMap (q x)) _).1 h2

open MMP.Threefold.Mori.OpenRestriction in
/-- The restriction of an snc divisor to an open subscheme is snc. -/
private theorem isSNC_restrictOpen' {R : Type*} [Zero R] {X S : Scheme.{0}} (g : X ⟶ S)
    [∀ E : Mori.PrimeDivisor X, LocallyOfFinitePresentation (E.idealSheaf.subschemeι ≫ g)]
    {D : DivisorWithCoeffs R X} (hD : D.IsSNC g) (U : X.Opens) :
    (D.restrictOpen U).IsSNC (U.ι ≫ g) := by
  refine ⟨fun E₀ hE₀ => ?_, fun x => (sncStalk_restrict_iff U.ι D x).mpr (hD.2 (U.ι x))⟩
  have hsm := hD.1 (OpenWeilRestriction.primeDivisorMap U.ι E₀)
    (Finsupp.mem_support_iff.2 (Finsupp.mem_support_iff.1 hE₀ : D.restrictOpen U E₀ ≠ 0))
  rw [IsSmoothScheme, smoothLocus_eq_smoothLocus] at hsm
  exact (isSmoothScheme_comap_iff U.ι g (OpenWeilRestriction.primeDivisorMap U.ι E₀).idealSheaf
    E₀.idealSheaf (idealSheaf_comap_primeDivisorMap U.ι E₀)).mpr fun z _ => hsm ▸ trivial

/-- **Generic étaleness** (char. `0`). A domain `A` of finite type and algebraic over a Noetherian
domain `R` of characteristic zero, with `R ⟶ A` injective, is étale over `R` after inverting some
nonzero element: the extension of fraction fields is separable. -/
private theorem exists_ne_zero_etale_away' {R A : Type} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [CharZero R] [CommRing A] [IsDomain A] [Algebra R A]
    [Algebra.FiniteType R A] [Algebra.IsAlgebraic R A]
    (hinj : Function.Injective (algebraMap R A)) :
    ∃ f : A, f ≠ 0 ∧ Algebra.Etale R (Localization.Away f) := by
  classical
  let K := FractionRing R
  let L := FractionRing A
  haveI : FaithfulSMul R L :=
    (faithfulSMul_iff_algebraMap_injective R L).2 (by
      rw [IsScalarTower.algebraMap_eq R A L]
      exact (IsFractionRing.injective A L).comp hinj)
  letI : Algebra K L := FractionRing.liftAlgebra R L
  haveI : IsScalarTower R K L := FractionRing.isScalarTower_liftAlgebra R L
  haveI : Algebra.IsAlgebraic A L := IsLocalization.isAlgebraic L (nonZeroDivisors A)
  haveI : Algebra.IsAlgebraic R L := Algebra.IsAlgebraic.trans R A L
  haveI : Algebra.IsAlgebraic K L :=
    ⟨fun x => (IsFractionRing.isAlgebraic_iff R K L).1 (Algebra.IsAlgebraic.isAlgebraic x)⟩
  haveI : CharZero K := IsFractionRing.charZero R
  haveI : Algebra.IsSeparable K L := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
  haveI : Algebra.FormallyEtale R K := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors R)
  haveI : Algebra.FormallyEtale R L := Algebra.FormallyEtale.comp R K L
  have hM : (⊥ : Ideal A).primeCompl = nonZeroDivisors A := by
    ext x
    simp [Ideal.primeCompl, mem_nonZeroDivisors_iff_ne_zero]
  haveI : IsLocalization (⊥ : Ideal A).primeCompl L := by rw [hM]; infer_instance
  haveI : Algebra.IsEtaleAt R (⊥ : Ideal A) :=
    Algebra.FormallyEtale.of_equiv
      ((IsLocalization.algEquiv (⊥ : Ideal A).primeCompl L
        (Localization.AtPrime (⊥ : Ideal A))).restrictScalars R)
  haveI : Algebra.FinitePresentation R A :=
    Algebra.FinitePresentation.of_finiteType.1 inferInstance
  exact Algebra.exists_etale_of_isEtaleAt (R := R) (⊥ : Ideal A)

/-- **A finite coordinate, étale over a dense open of the line.** A domain `A` of finite type and
of dimension one over `ℂ` is finite over a polynomial ring `ℂ[t] ⊆ A` (Noether normalization), and
étale over `ℂ[t]` after inverting a nonzero `h ∈ ℂ[t]`. -/
private theorem exists_finite_etale_coordinate_algebra {A : Type} [CommRing A] [IsDomain A]
    [Algebra ℂ A] [Algebra.FiniteType ℂ A] (hA : ringKrullDim A = 1) :
    ∃ (ψ : MvPolynomial (Fin 1) ℂ →ₐ[ℂ] A) (h : MvPolynomial (Fin 1) ℂ),
      Function.Injective ψ ∧ ψ.toRingHom.Finite ∧ h ≠ 0 ∧
      ((algebraMap A (Localization.Away (ψ h))).comp ψ.toRingHom).Etale := by
  classical
  obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg ℂ A
  have hs : s = 1 := by
    letI := g.toRingHom.toAlgebra
    haveI : Module.Finite (MvPolynomial (Fin s) ℂ) A := hfin
    have h1 := (ringKrullDim_eq_of_injective_isIntegral (algebraMap (MvPolynomial (Fin s) ℂ) A)
      hinj Algebra.IsIntegral.isIntegral).symm
    rw [hA, MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
      ENat.card_eq_coe_fintype_card, Fintype.card_fin, zero_add] at h1
    exact_mod_cast h1.symm
  subst hs
  set R := MvPolynomial (Fin 1) ℂ
  letI : Algebra R A := g.toRingHom.toAlgebra
  haveI : Module.Finite R A := hfin
  have hinj' : Function.Injective (algebraMap R A) := hinj
  obtain ⟨a, ha, hae⟩ := exists_ne_zero_etale_away' (R := R) (A := A) hinj'
  obtain ⟨r, hr, hdvd⟩ := MMP.SmoothLocusConnected.exists_ne_zero_dvd_algebraMap
    (Algebra.IsIntegral.isIntegral (R := R) a) ha
  refine ⟨g, r, hinj, hfin, hr, ?_⟩
  haveI : Algebra.FinitePresentation R A :=
    Algebra.FinitePresentation.of_finiteType.1 inferInstance
  have hsub : ↑(PrimeSpectrum.basicOpen (algebraMap R A r)) ⊆ Algebra.etaleLocus R A := by
    obtain ⟨c, hc⟩ := hdvd
    rw [hc]
    exact (show (PrimeSpectrum.basicOpen (a * c) : Set (PrimeSpectrum A)) ⊆
      PrimeSpectrum.basicOpen a from PrimeSpectrum.basicOpen_mul_le_left a c).trans
      ((Algebra.basicOpen_subset_etaleLocus_iff_etale (R := R)).2 hae)
  have he : Algebra.Etale R (Localization.Away (algebraMap R A r)) :=
    (Algebra.basicOpen_subset_etaleLocus_iff_etale (R := R)).1 hsub
  have := RingHom.etale_algebraMap.2 he
  rwa [IsScalarTower.algebraMap_eq R A] at this

/-- A morphism of affine schemes which is étale over a basic open `D(h)` of the target, i.e. after
inverting `h`, is étale over every open `B ⊆ D(h)`. -/
private theorem etale_morphismRestrict_of_le_basicOpen {R A : CommRingCat.{0}} (φ : R ⟶ A) (h : R)
    (het : ((algebraMap A (Localization.Away (φ h))).comp φ.hom).Etale) (B : (Spec R).Opens)
    (hB : B ≤ PrimeSpectrum.basicOpen h) : Etale (Spec.map φ ∣_ B) := by
  set j := Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (φ h))))
  have hr : Set.range (Spec.map φ ⁻¹ᵁ B).ι.base ⊆ Set.range j.base := by
    rw [Scheme.Opens.range_ι]
    intro x hx
    have hx' : x ∈ (PrimeSpectrum.basicOpen (φ.hom h) : Set (PrimeSpectrum A)) := hB hx
    have := PrimeSpectrum.localization_away_comap_range (Localization.Away (φ.hom h)) (φ.hom h)
    rw [← this] at hx'
    exact hx'
  set k := IsOpenImmersion.lift j _ hr
  have hk : k ≫ j = (Spec.map φ ⁻¹ᵁ B).ι := IsOpenImmersion.lift_fac _ _ _
  haveI : Etale (j ≫ Spec.map φ) := by
    rw [← Spec.map_comp]
    exact HasRingHomProperty.Spec_iff.2 het
  haveI : Etale (Spec.map φ ∣_ B ≫ B.ι) := by
    rw [morphismRestrict_ι, ← hk, Category.assoc]
    infer_instance
  exact Etale.of_comp _ B.ι

/-- **A coordinate on `T`, finite étale over an open of the line.** Near a general point of the
curve `T`, an affine open `V ⊆ U` meeting `T` carries a function `g : V ⟶ 𝔸¹` and a nonempty
open `B₀ ⊆ 𝔸¹` onto which `g` maps `V ∩ T`, such that over every open `B ⊆ B₀` the trace of `T`
on `g⁻¹(B)` is finite étale over `B`. -/
private theorem exists_coordinate_hasFiniteEtaleTrace [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))]
    [IsSeparated (Y ↘ Spec (.of ℂ))] (T : IrreducibleCloseds Y)
    (hT1 : topologicalKrullDim (T : Set Y) = 1) (U : Y.Opens) (hU : ((U : Set Y) ∩ T).Nonempty) :
    ∃ (V : Y.Opens) (g : V.toScheme ⟶ 𝔸¹ℂ), V ≤ U ∧
      IsAffineOpen V ∧
      g ≫ s𝔸¹ℂ =
        V.ι ≫ Y ↘ Spec (.of ℂ) ∧
      ∃ B₀ : (𝔸¹ℂ).Opens, (B₀ : Set 𝔸¹ℂ).Nonempty ∧
        (∀ a ∈ B₀, ∃ v : V.toScheme, V.ι v ∈ (T : Set Y) ∧ g v = a) ∧
        ∀ B ≤ B₀,
          HasFiniteEtaleTrace (T : Set Y) (V.ι ''ᵁ (g ⁻¹ᵁ B)) (coordinateRestrict V g B) := by
  classical
  set sY := Y ↘ Spec (.of ℂ) with hsY
  obtain ⟨y, hyU, hyT⟩ := hU
  set ζ := T.isIrreducible.genericPoint with hζdef
  have hζ : IsGenericPoint ζ (T : Set Y) := by
    have := T.isIrreducible.isGenericPoint_genericPoint_closure
    rwa [T.isClosed.closure_eq] at this
  obtain ⟨V, hV, hyV, hVU⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := U) hyU
  have hζV : ζ ∈ V := (hζ.specializes hyT).mem_open V.isOpen hyV
  obtain ⟨ζ', hζ'⟩ : ζ ∈ Set.range hV.fromSpec := hV.range_fromSpec ▸ hζV
  set P : Ideal Γ(Y, V) := (ζ' : PrimeSpectrum Γ(Y, V)).asIdeal with hPdef
  haveI hP : P.IsPrime := (ζ' : PrimeSpectrum Γ(Y, V)).isPrime
  -- the `ℂ`-algebra structure of `Γ(Y, V)`
  set ι₀ : CommRingCat.of ℂ ⟶ Γ(Y, V) := Spec.preimage (hV.fromSpec ≫ sY) with hι₀def
  have hι₀ : Spec.map ι₀ = hV.fromSpec ≫ sY := Spec.map_preimage _
  letI : Algebra ℂ Γ(Y, V) := ι₀.hom.toAlgebra
  haveI : Algebra.FiniteType ℂ Γ(Y, V) := by
    have : LocallyOfFiniteType (Spec.map ι₀) := hι₀ ▸ inferInstance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 this
  haveI : Algebra.FiniteType ℂ (Γ(Y, V) ⧸ P) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ P) Ideal.Quotient.mk_surjective
  -- the trace of `T` on `V` is `Spec (Γ(Y, V)/P)`
  set i₀ : Spec (.of (Γ(Y, V) ⧸ P)) ⟶ V.toScheme :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk P)) ≫ hV.isoSpec.inv with hi₀
  have hi₀ι : ∀ c, V.ι (i₀ c) = hV.fromSpec (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk P)) c) := by
    intro c
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hi₀, Category.assoc,
      IsAffineOpen.isoSpec_inv_ι]
  have hrange₀ : V.ι.base '' Set.range i₀.base = (V : Set Y) ∩ T := by
    have h3 : Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk P))).base =
        closure {ζ'} := by
      have hcl : closure ({ζ'} : Set (Spec Γ(Y, V))) = PrimeSpectrum.zeroLocus P :=
        PrimeSpectrum.closure_singleton (R := Γ(Y, V)) ζ'
      rw [hcl]
      refine (range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective).trans ?_
      rw [CommRingCat.hom_ofHom, Ideal.mk_ker]
    have h4 : V.ι.base '' Set.range i₀.base =
        hV.fromSpec.base '' Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk P))).base := by
      ext y
      constructor
      · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
        exact ⟨_, ⟨c, rfl⟩, (hi₀ι c).symm⟩
      · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
        exact ⟨_, ⟨c, rfl⟩, hi₀ι c⟩
    rw [h4, h3, hV.fromSpec.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image,
      Set.image_preimage_eq_inter_range, Set.image_singleton, hζ', hζ.def, hV.range_fromSpec,
      Set.inter_comm]
  have hdim : ringKrullDim (Γ(Y, V) ⧸ P) = 1 := by
    set k := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk P))
    have hkemb : IsEmbedding (fun c => hV.fromSpec (k c)) :=
      hV.fromSpec.isOpenEmbedding.isEmbedding.comp k.isClosedEmbedding.isEmbedding
    have hkT : ∀ c, hV.fromSpec (k c) ∈ (T : Set Y) := fun c => by
      have := (hrange₀ ▸ ⟨_, ⟨c, rfl⟩, rfl⟩ : V.ι (i₀ c) ∈ (V : Set Y) ∩ T).2
      rwa [hi₀ι] at this
    refine le_antisymm ?_ ?_
    · rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ← hT1]
      exact (hkemb.isInducing.codRestrict hkT).topologicalKrullDim_le
    · -- `T` has two distinct points
      obtain ⟨Z₁, Z₂, hZ⟩ := Order.one_le_krullDim_iff.1 (hT1.symm ▸ le_rfl :
        (1 : WithBot ℕ∞) ≤ topologicalKrullDim (T : Set Y))
      obtain ⟨p₂, hp₂, hp₂'⟩ := Set.exists_of_ssubset (show (Z₁ : Set (T : Set Y)) ⊂ Z₂ from hZ)
      obtain ⟨p₁, hp₁⟩ := Z₁.isIrreducible.nonempty
      -- a point of `V ∩ T` other than `ζ`
      haveI : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace sY
      obtain ⟨y', ⟨hy'V, hy'T⟩, hy'⟩ : ∃ y' ∈ (V : Set Y) ∩ T, y' ≠ ζ := by
        by_contra hne
        push Not at hne
        have hVT : (V : Set Y) ∩ T = {ζ} := by
          ext z
          refine ⟨fun hz => hne z hz, ?_⟩
          rintro rfl
          exact ⟨hζV, hζ.mem⟩
        have hcl : IsClosed ({ζ} : Set Y) := isClosed_singleton_of_isLocallyClosed_singleton
          ⟨_, _, V.isOpen, T.isClosed, hVT.symm⟩
        have hTζ : (T : Set Y) = {ζ} := by rw [← hζ.def, hcl.closure_eq]
        have h₁ : (p₁ : Y) = ζ := by simpa [hTζ] using p₁.2
        have h₂ : (p₂ : Y) = ζ := by simpa [hTζ] using p₂.2
        exact hp₂' (Subtype.ext (h₂.trans h₁.symm) ▸ hp₁)
      obtain ⟨_, ⟨c, rfl⟩, hc⟩ := (hrange₀.symm ▸ ⟨hy'V, hy'T⟩ :
        y' ∈ V.ι.base '' Set.range i₀.base)
      refine Order.one_le_krullDim_iff.2 ⟨⟨⊥, Ideal.isPrime_bot⟩, c, lt_of_le_of_ne bot_le ?_⟩
      intro hbot
      apply hy'
      rw [← hc, hi₀ι, ← hζ']
      congr 1
      apply PrimeSpectrum.ext
      change Ideal.comap (Ideal.Quotient.mk P) c.asIdeal = P
      rw [← (show (⊥ : Ideal (Γ(Y, V) ⧸ P)) = c.asIdeal from congrArg PrimeSpectrum.asIdeal hbot),
        ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  obtain ⟨ψ, h, hψinj, hψfin, hh, hψet⟩ := exists_finite_etale_coordinate_algebra hdim
  obtain ⟨f, hf⟩ := Ideal.Quotient.mk_surjective (ψ (MvPolynomial.X 0))
  set ψ' : MvPolynomial (Fin 1) ℂ →+* Γ(Y, V) := MvPolynomial.eval₂Hom ι₀.hom (fun _ => f)
    with hψ'def
  have hψ' : (Ideal.Quotient.mk P).comp ψ' = ψ.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change Ideal.Quotient.mk P (ψ' (MvPolynomial.C c)) = ψ (MvPolynomial.C c)
      rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, hψ'def, MvPolynomial.algebraMap_eq,
        MvPolynomial.eval₂Hom_C]
      rfl
    · intro i
      fin_cases i
      change Ideal.Quotient.mk P (ψ' (MvPolynomial.X 0)) = ψ (MvPolynomial.X 0)
      rw [hψ'def, MvPolynomial.eval₂Hom_X', hf]
  set g : V.toScheme ⟶ 𝔸¹ℂ := hV.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ψ') with hgdef
  have hg : g ≫ s𝔸¹ℂ = V.ι ≫ sY := by
    rw [← hV.isoSpec_hom_fromSpec, hgdef, Category.assoc, Category.assoc, ← hι₀,
      ← Spec.map_comp]
    congr 2
    ext c
    change ψ' (MvPolynomial.C c) = _
    rw [hψ'def, MvPolynomial.eval₂Hom_C]
  have hq₀ : i₀ ≫ g = Spec.map (CommRingCat.ofHom ψ.toRingHom) := by
    rw [hi₀, hgdef, Category.assoc, Iso.inv_hom_id_assoc, ← Spec.map_comp, ← hψ']
    rfl
  haveI : IsFinite (i₀ ≫ g) := by
    rw [hq₀]
    exact (IsFinite.SpecMap_iff _).2 hψfin
  refine ⟨V, g, hVU, hV, hg, PrimeSpectrum.basicOpen h, ?_, ?_, ?_⟩
  · refine ⟨⟨⊥, Ideal.isPrime_bot⟩, ?_⟩
    show h ∉ (⊥ : Ideal (MvPolynomial (Fin 1) ℂ))
    simpa using hh
  · intro a _
    letI : Algebra (MvPolynomial (Fin 1) ℂ) (Γ(Y, V) ⧸ P) := ψ.toRingHom.toAlgebra
    haveI : Module.Finite (MvPolynomial (Fin 1) ℂ) (Γ(Y, V) ⧸ P) := hψfin
    let a' : PrimeSpectrum (MvPolynomial (Fin 1) ℂ) := a
    have hinj' : Function.Injective (algebraMap (MvPolynomial (Fin 1) ℂ) (Γ(Y, V) ⧸ P)) := hψinj
    obtain ⟨Q, -, hQ, hQa⟩ := Ideal.exists_ideal_over_prime_of_isIntegral a'.asIdeal ⊥
      (Ideal.comap_bot_le_of_injective _ hinj')
    let q : Spec (.of (Γ(Y, V) ⧸ P)) := (⟨Q, hQ⟩ : PrimeSpectrum (Γ(Y, V) ⧸ P))
    refine ⟨i₀ q, ?_, ?_⟩
    · have : V.ι (i₀ q) ∈ (V : Set Y) ∩ T := hrange₀ ▸ ⟨_, ⟨q, rfl⟩, rfl⟩
      exact this.2
    · rw [← Scheme.Hom.comp_apply, hq₀]
      exact PrimeSpectrum.ext hQa
  · intro B hB
    have hcomp : (i₀ ∣_ (g ⁻¹ᵁ B) ≫ (V.ι.isoImage (g ⁻¹ᵁ B)).hom) ≫
        coordinateRestrict V g B = (i₀ ≫ g) ∣_ B := by
      rw [morphismRestrict_comp i₀ g B, coordinateRestrict]
      simp
    refine ⟨(i₀ ⁻¹ᵁ (g ⁻¹ᵁ B)).toScheme, i₀ ∣_ (g ⁻¹ᵁ B) ≫ (V.ι.isoImage (g ⁻¹ᵁ B)).hom,
      inferInstance, ?_, inferInstance, ?_, ?_⟩
    · set U' := i₀ ⁻¹ᵁ (g ⁻¹ᵁ B)
      have e : ∀ c : U'.toScheme,
          (V.ι ''ᵁ (g ⁻¹ᵁ B)).ι ((i₀ ∣_ (g ⁻¹ᵁ B) ≫ (V.ι.isoImage (g ⁻¹ᵁ B)).hom) c) =
            V.ι (i₀ (U'.ι c)) := by
        intro c
        rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
          Category.assoc, Scheme.Hom.isoImage_hom_ι, morphismRestrict_ι_assoc]
      ext y
      constructor
      · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
        refine ⟨Scheme.Opens.range_ι _ ▸ ⟨_, rfl⟩, ?_⟩
        rw [e]
        exact (hrange₀ ▸ ⟨_, ⟨_, rfl⟩, rfl⟩ : V.ι (i₀ (U'.ι c)) ∈ (V : Set Y) ∩ T).2
      · rintro ⟨⟨v, hvB, rfl⟩, hyT⟩
        obtain ⟨_, ⟨c, rfl⟩, hc⟩ :=
          (hrange₀.symm ▸ ⟨(V.ι_image_le _) ⟨v, hvB, rfl⟩, hyT⟩ :
            V.ι v ∈ V.ι.base '' Set.range i₀.base)
        have hcv : i₀ c = v := V.ι.isOpenEmbedding.injective hc
        have hcU : c ∈ U' := by
          change i₀ c ∈ g ⁻¹ᵁ B
          rw [hcv]; exact hvB
        let c' : U'.toScheme := ⟨c, hcU⟩
        refine ⟨_, ⟨c', rfl⟩, ?_⟩
        rw [e c']
        exact hc
    · rw [hcomp]
      haveI : IsFinite (Spec.map (CommRingCat.ofHom ψ.toRingHom)) :=
        (IsFinite.SpecMap_iff _).2 hψfin
      have : IsFinite (Spec.map (CommRingCat.ofHom ψ.toRingHom) ∣_ B) := inferInstance
      rwa [← hq₀] at this
    · rw [hcomp]
      have := etale_morphismRestrict_of_le_basicOpen (CommRingCat.ofHom ψ.toRingHom) h hψet B hB
      rwa [← hq₀] at this

/-- A point over `U` of a morphism smooth over `U` is a formally smooth point. -/
private theorem formallySmooth_stalkMap_of_smooth_morphismRestrict {S A : Scheme.{0}}
    (p : S ⟶ A) [LocallyOfFinitePresentation p] (U : A.Opens) [Smooth (p ∣_ U)] (x : S)
    (hx : p x ∈ U) :
    (p.stalkMap x).hom.FormallySmooth := by
  let x' : (p ⁻¹ᵁ U).toScheme := ⟨x, hx⟩
  have h1 : ((p ∣_ U).stalkMap x').hom.FormallySmooth := by
    have hmem : x' ∈ (p ∣_ U).smoothLocus :=
      (Scheme.Hom.smoothLocus_eq_top (p ∣_ U)) ▸ trivial
    exact hmem
  haveI := IsOpenImmersion.instIsIsoCommRingCatStalkMap U.ι ((p ∣_ U) x')
  haveI := IsOpenImmersion.instIsIsoCommRingCatStalkMap (p ⁻¹ᵁ U).ι x'
  have h2 : (((p ∣_ U) ≫ U.ι).stalkMap x').hom.FormallySmooth := by
    rw [Scheme.Hom.stalkMap_comp]
    exact (RingHom.FormallySmooth.respectsIso.cancel_left_isIso _ _).2 h1
  rw [Scheme.Hom.stalkMap_congr_hom _ _ (morphismRestrict_ι p U), Scheme.Hom.stalkMap_comp] at h2
  have h3 := (RingHom.FormallySmooth.respectsIso.cancel_left_isIso _ _).1 h2
  exact (RingHom.FormallySmooth.respectsIso.cancel_right_isIso
    (p.stalkMap ((p ⁻¹ᵁ U).ι x')) ((p ⁻¹ᵁ U).ι.stalkMap x')).1 h3

/-- **Generic smoothness over the line.** A function `p : S ⟶ 𝔸¹` on a quasi-compact scheme `S`
smooth over `ℂ` is smooth over a dense open of `𝔸¹`: `S` is a finite disjoint union of smooth
integral schemes, and each of them is smooth over a dense open
(`MMP.exists_dense_smooth_restrict_of_smooth`). -/
private theorem exists_dense_formallySmooth_of_smooth {S : Scheme.{0}} (sS : S ⟶ Spec (.of ℂ))
    [Smooth sS] [QuasiCompact sS] (p : S ⟶ 𝔸¹ℂ) (hp : p ≫ s𝔸¹ℂ = sS) :
    ∃ B : 𝔸¹ℂ.Opens, Dense (B : Set 𝔸¹ℂ) ∧
      ∀ x : S, p x ∈ B → (p.stalkMap x).hom.FormallySmooth := by
  classical
  haveI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian sS
  haveI : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace sS
  haveI : IsNoetherian S := {}
  haveI : IsNormal S := isNormal_of_smooth_over_field sS
  obtain ⟨ι, hι, Y, -, hYi, ⟨e⟩⟩ :=
    (isNormal_iff_exists_iso_finite_coproduct_integral_normal S).1 inferInstance
  haveI := Fintype.ofFinite ι
  let j : ∀ i, Y i ⟶ S := fun i => CategoryTheory.Limits.Sigma.ι Y i ≫ e.inv
  haveI : ∀ i, IsOpenImmersion (j i) := fun i => by
    haveI : IsOpenImmersion (CategoryTheory.Limits.Sigma.ι Y i) := (sigmaOpenCover Y).map_prop i
    infer_instance
  haveI hsA := smoothOfRelativeDimension_one_affineLine
  have hU : ∀ i, ∃ U : 𝔸¹ℂ.Opens, Dense (U : Set 𝔸¹ℂ) ∧
      ∀ y : Y i, (j i ≫ p) y ∈ U → ((j i ≫ p).stalkMap y).hom.FormallySmooth := by
    intro i
    letI : (Y i).Over (Spec (.of ℂ)) := ⟨j i ≫ sS⟩
    letI : 𝔸¹ℂ.Over (Spec (.of ℂ)) := ⟨s𝔸¹ℂ⟩
    haveI : IsIntegral (Y i) := hYi i
    haveI : LocallyOfFiniteType ((Y i) ↘ Spec (.of ℂ)) :=
      inferInstanceAs (LocallyOfFiniteType (j i ≫ sS))
    haveI : NoetherianSpace (Y i) := (j i).isOpenEmbedding.isInducing.noetherianSpace
    haveI : QuasiCompact ((Y i) ↘ Spec (.of ℂ)) :=
      (quasiCompact_iff_compactSpace _).2 inferInstance
    haveI : LocallyOfFiniteType (𝔸¹ℂ ↘ Spec (.of ℂ)) :=
      inferInstanceAs (LocallyOfFiniteType s𝔸¹ℂ)
    haveI : QuasiCompact (𝔸¹ℂ ↘ Spec (.of ℂ)) := inferInstanceAs (QuasiCompact s𝔸¹ℂ)
    haveI : Smooth ((Y i) ↘ Spec (.of ℂ)) := inferInstanceAs (Smooth (j i ≫ sS))
    haveI : (j i ≫ p).IsOver (Spec (.of ℂ)) :=
      ⟨by change (j i ≫ p) ≫ s𝔸¹ℂ = j i ≫ sS; rw [Category.assoc, hp]⟩
    haveI : LocallyOfFiniteType (j i ≫ p) := by
      have : LocallyOfFiniteType ((j i ≫ p) ≫ s𝔸¹ℂ) := by
        rw [Category.assoc, hp]; infer_instance
      exact LocallyOfFiniteType.of_comp (g := s𝔸¹ℂ) this
    haveI : LocallyOfFinitePresentation (j i ≫ p) :=
      LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
    obtain ⟨U, hUd, -, hsm, -⟩ := MMP.exists_dense_smooth_restrict_of_smooth (K := ℂ) (j i ≫ p)
    exact ⟨U, hUd, fun y hy => formallySmooth_stalkMap_of_smooth_morphismRestrict _ U y hy⟩
  choose U hUd hUs using hU
  have hdense : ∀ s : Finset ι, Dense ((s.inf U : 𝔸¹ℂ.Opens) : Set 𝔸¹ℂ) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      rw [Finset.inf_insert, TopologicalSpace.Opens.coe_inf]
      exact (hUd i).inter_of_isOpen_left ih (U i).isOpen
  refine ⟨Finset.univ.inf U, hdense _, fun x hx => ?_⟩
  obtain ⟨⟨i, y⟩, hy⟩ : ∃ t, sigmaMk Y t = e.hom x := ⟨(sigmaMk Y).symm (e.hom x), by simp⟩
  have hx' : j i y = x := by
    rw [sigmaMk_mk] at hy
    change e.inv (CategoryTheory.Limits.Sigma.ι Y i y) = x
    rw [hy, ← Scheme.Hom.comp_apply, Iso.hom_inv_id]
    rfl
  have hpy : (j i ≫ p) y ∈ U i := by
    rw [Scheme.Hom.comp_apply, hx']
    exact (Finset.inf_le (Finset.mem_univ i) : Finset.univ.inf U ≤ U i) hx
  have hsm' := hUs i y hpy
  rw [Scheme.Hom.stalkMap_comp] at hsm'
  haveI := IsOpenImmersion.instIsIsoCommRingCatStalkMap (j i) y
  rw [← hx']
  exact (RingHom.FormallySmooth.respectsIso.cancel_right_isIso _ _).1 hsm'

/-- **The strata of an snc divisor are smooth.** For a finite set `J` of components of an snc
divisor `B` on `X` locally of finite type over a perfect field `k`, the stratum cut out by
`⨆_{E ∈ J} I_E` is smooth over `k` (for `J = ∅` this is `X`). -/
theorem smooth_iSup_idealSheaf_of_isSNC {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] {R : Type*} [Zero R]
    {B : DivisorWithCoeffs R X} (hB : B.IsSNC sX) (J : Finset (Mori.PrimeDivisor X))
    (hJ : J ⊆ B.support) :
    Smooth ((⨆ E ∈ J, E.idealSheaf).subschemeι ≫ sX) := by
  classical
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  set D : X.IdealSheafData := ⨆ E ∈ J, E.idealSheaf with hD
  rw [MMP.Flips.ResolutionInputs.smooth_iff_forall_isRegularLocalRing_stalk]
  intro z
  have hzD : D.subschemeι z ∈ (D.support : Set X) := by
    rw [← D.range_subschemeι]; exact ⟨z, rfl⟩
  have hmem : ∀ E ∈ J, D.subschemeι z ∈ E.support := fun E hE =>
    Scheme.IdealSheafData.support_antitone
      (le_biSup (fun E : Mori.PrimeDivisor X => E.idealSheaf) hE) hzD
  obtain ⟨n, w, j, hw, -, hI⟩ := hB.2 (D.subschemeι z)
  haveI := isRegularLocalRing_of_isRegularSystemOfParameters hw
  let s : Finset (Fin n) := J.attach.image fun E => j ⟨E.1, hJ E.2, hmem E.1 E.2⟩
  have hstalk : AlgebraicGeometry.IdealSheafData.stalk D (D.subschemeι z) =
      Ideal.span (w '' (s : Set (Fin n))) := by
    have hsup : ∀ y : X, AlgebraicGeometry.IdealSheafData.stalk D y =
        ⨆ E ∈ J, AlgebraicGeometry.IdealSheafData.stalk E.idealSheaf y := fun y => by
      rw [hD, iSup_subtype', MMP.Resolution.stalk_iSup, iSup_subtype']
    rw [hsup]
    refine le_antisymm (iSup₂_le fun E hE => ?_) (Ideal.span_le.2 ?_)
    · rw [hI ⟨E, hJ hE, hmem E hE⟩, Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.subset_span ⟨_, Finset.mem_coe.2 (Finset.mem_image.2
        ⟨⟨E, hE⟩, Finset.mem_attach _ _, rfl⟩), rfl⟩
    · rintro _ ⟨i, hi, rfl⟩
      obtain ⟨⟨E, hE⟩, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hi)
      refine (le_biSup (fun E : Mori.PrimeDivisor X =>
        AlgebraicGeometry.IdealSheafData.stalk E.idealSheaf (D.subschemeι z)) hE) ?_
      rw [hI ⟨E, hJ hE, hmem E hE⟩]
      exact Ideal.mem_span_singleton_self _
  exact isRegularLocalRing_stalk_subscheme_of_isRegularLocalRing_quotient D z (by
    rw [hstalk]
    exact MMP.Resolution.isRegularLocalRing_quotient_span_image w hw s)

/-- **The double intersections of an snc divisor are smooth.** For components `E₁, E₂` of an snc
divisor on a scheme locally of finite type over a perfect field `k`, the closed subscheme
`E₁ ∩ E₂` cut out by `I_{E₁} + I_{E₂}` is smooth over `k`. -/
theorem smooth_sup_idealSheaf_of_isSNC {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] {R : Type*} [Zero R]
    {B : DivisorWithCoeffs R X} (hB : B.IsSNC sX) {E₁ E₂ : Mori.PrimeDivisor X}
    (h₁ : E₁ ∈ B.support) (h₂ : E₂ ∈ B.support) :
    Smooth ((E₁.idealSheaf ⊔ E₂.idealSheaf).subschemeι ≫ sX) := by
  classical
  have h := smooth_iSup_idealSheaf_of_isSNC sX hB {E₁, E₂}
    (Finset.insert_subset_iff.2 ⟨h₁, Finset.singleton_subset_iff.2 h₂⟩)
  rwa [Finset.iSup_insert, Finset.iSup_singleton] at h

/-- **Generic smoothness of the strata of `F` over the line.** For a function `g : V ⟶ 𝔸¹` on an
open `V` of `Y`, there is a dense open `B₁ ⊆ 𝔸¹` such that every stratum `F_J ∩ r⁻¹(V)`
(`J ⊆ F.support`, `F_∅ = Z`) is smooth over `B₁` by `g ∘ r`. -/
private theorem exists_dense_formallySmooth_strata
    (hM : IsCurvePointExceptionalModel (Y ↘ Spec (.of ℂ)) r F D) (V : Y.Opens)
    (g : V.toScheme ⟶ 𝔸¹ℂ)
    (hg : g ≫ s𝔸¹ℂ =
        V.ι ≫ Y ↘ Spec (.of ℂ)) :
    ∃ B₁ : (𝔸¹ℂ).Opens, Dense (B₁ : Set 𝔸¹ℂ) ∧ ∀ J ⊆ F.support,
      ∀ x : ((⨆ E ∈ J, E.idealSheaf).comap (r ⁻¹ᵁ V).ι).subscheme,
        (((⨆ E ∈ J, E.idealSheaf).comap (r ⁻¹ᵁ V).ι).subschemeι ≫ r ∣_ V ≫ g) x ∈ B₁ →
        ((((⨆ E ∈ J, E.idealSheaf).comap (r ⁻¹ᵁ V).ι).subschemeι ≫ r ∣_ V ≫ g).stalkMap
          x).hom.FormallySmooth := by
  classical
  haveI hvZ : AlgebraicGeometry.IsVariety ℂ (Z ↘ Spec (.of ℂ)) := hM.comp_eq ▸ hM.isResolution.2.1
  have hS : ∀ J ⊆ F.support, ∃ B : 𝔸¹ℂ.Opens, Dense (B : Set 𝔸¹ℂ) ∧
      ∀ x : ((⨆ E ∈ J, E.idealSheaf).comap (r ⁻¹ᵁ V).ι).subscheme,
        (((⨆ E ∈ J, E.idealSheaf).comap (r ⁻¹ᵁ V).ι).subschemeι ≫ r ∣_ V ≫ g) x ∈ B →
        ((((⨆ E ∈ J, E.idealSheaf).comap (r ⁻¹ᵁ V).ι).subschemeι ≫ r ∣_ V ≫ g).stalkMap
          x).hom.FormallySmooth := by
    intro J hJ
    set I := ⨆ E ∈ J, E.idealSheaf
    haveI : Smooth (I.subschemeι ≫ Z ↘ Spec (.of ℂ)) := smooth_iSup_idealSheaf_of_isSNC (Z ↘ Spec (.of ℂ))
      (hM.comp_eq ▸ hM.isSNC) J hJ
    obtain ⟨k, hk, hcomm, -⟩ :=
      MMP.Threefold.Mori.OpenRestriction.exists_openImmersion_comap_subscheme (r ⁻¹ᵁ V).ι I
    haveI : Smooth ((I.comap (r ⁻¹ᵁ V).ι).subschemeι ≫ (r ⁻¹ᵁ V).ι ≫ Z ↘ Spec (.of ℂ)) := by
      rw [← Category.assoc, hcomm, Category.assoc]
      infer_instance
    haveI : IsNoetherian Z := {}
    haveI : QuasiCompact ((I.comap (r ⁻¹ᵁ V).ι).subschemeι ≫ (r ⁻¹ᵁ V).ι ≫
        Z ↘ Spec (.of ℂ)) := inferInstance
    refine exists_dense_formallySmooth_of_smooth
      ((I.comap (r ⁻¹ᵁ V).ι).subschemeι ≫ (r ⁻¹ᵁ V).ι ≫ Z ↘ Spec (.of ℂ)) _ ?_
    rw [Category.assoc, Category.assoc, hg, ← Category.assoc (r ∣_ V), morphismRestrict_ι,
      Category.assoc, comp_over r]
  choose! B hBd hBs using hS
  have hdense : ∀ s : Finset (Finset (Mori.PrimeDivisor Z)),
      Dense ((s.inf B : 𝔸¹ℂ.Opens) : Set 𝔸¹ℂ) ∨ ∃ J ∈ s, ¬ J ⊆ F.support := by
    intro s
    induction s using Finset.induction_on with
    | empty => left; simp
    | insert J s hJs ih =>
      by_cases hJ : J ⊆ F.support
      · rcases ih with ih | ⟨J', hJ', h'⟩
        · left
          rw [Finset.inf_insert, TopologicalSpace.Opens.coe_inf]
          exact (hBd J hJ).inter_of_isOpen_left ih (B J).isOpen
        · exact Or.inr ⟨J', Finset.mem_insert_of_mem hJ', h'⟩
      · exact Or.inr ⟨J, Finset.mem_insert_self _ _, hJ⟩
  have hd := hdense F.support.powerset
  rcases hd with hd | ⟨J, hJ, h⟩
  · refine ⟨F.support.powerset.inf B, hd, fun J hJ x hx => hBs J hJ x ?_⟩
    exact (Finset.inf_le (Finset.mem_powerset.2 hJ) : F.support.powerset.inf B ≤ B J) hx
  · exact absurd (Finset.mem_powerset.1 hJ) h

/-- **Algebraic exceptional charts exist over a general open of `T`.** There is an open `U₀`
meeting `T` such that every `b ∈ (U₀ ∩ T)(ℂ)` has an algebraic exceptional chart. -/
theorem exists_open_forall_nonempty_exceptionalAlgebraicChart
    (hM : IsCurvePointExceptionalModel (Y ↘ Spec (.of ℂ)) r F D)
    (T : IrreducibleCloseds Y) (hTs : (T : Set Y) ⊆ (singularLocus (Y ↘ Spec (.of ℂ)) : Set Y))
    (hT1 : topologicalKrullDim (T : Set Y) = 1) :
    ∃ U₀ : Y.Opens, ((U₀ : Set Y) ∩ T).Nonempty ∧
      ∀ b ∈ pointsOver (K := ℂ) ((U₀ : Set Y) ∩ T),
        Nonempty (ExceptionalAlgebraicChart r F T U₀ b) := by
  classical
  haveI hvY : AlgebraicGeometry.IsVariety ℂ (Y ↘ Spec (.of ℂ)) := hM.isResolution.1
  haveI hvZ : AlgebraicGeometry.IsVariety ℂ (Z ↘ Spec (.of ℂ)) := hM.comp_eq ▸ hM.isResolution.2.1
  haveI : IsProper r := (IsProjectiveMorphism.isProjective hM.isResolution.2.2.2.1).isProper
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of ℂ))
  haveI : LocallyOfFinitePresentation (Z ↘ Spec (.of ℂ)) :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  haveI : Smooth (Z ↘ Spec (.of ℂ)) :=
    (Mori.isSmoothScheme_iff _).1 (hM.comp_eq ▸ hM.isResolution.2.2.1)
  haveI hsA := smoothOfRelativeDimension_one_affineLine
  obtain ⟨U, hU, hUS⟩ := exists_open_singularLocus_inter_eq hM T hTs hT1
  obtain ⟨V, g, hVU, -, hg, B₀, hB₀, hB₀T, hfe⟩ :=
    exists_coordinate_hasFiniteEtaleTrace T hT1 U hU
  obtain ⟨B₁, hB₁, hsm⟩ := exists_dense_formallySmooth_strata hM V g hg
  haveI : LocallyOfFiniteType g := by
    have : LocallyOfFiniteType (g ≫ s𝔸¹ℂ) := hg ▸ inferInstance
    exact LocallyOfFiniteType.of_comp (g := s𝔸¹ℂ) this
  set Bo : 𝔸¹ℂ.Opens := B₀ ⊓ B₁ with hBo
  obtain ⟨a, haB₀, haB₁⟩ := hB₁.inter_open_nonempty _ B₀.isOpen hB₀
  set X : Y.Opens := V.ι ''ᵁ (g ⁻¹ᵁ Bo) with hX
  have hXV : X ≤ V := V.ι_image_le _
  obtain ⟨v, hvT, hva⟩ := hB₀T a haB₀
  have hvX : V.ι v ∈ X := ⟨v, (show g v ∈ Bo from hva ▸ ⟨haB₀, haB₁⟩), rfl⟩
  obtain ⟨C, iC, hci, hrange, hsep, hfin, het⟩ := hfe Bo inf_le_left
  refine ⟨X, ⟨V.ι v, hvX, hvT⟩, fun b hb => ⟨?_⟩⟩
  haveI : LocallyOfFiniteType (coordinateRestrict V g Bo) := by
    unfold coordinateRestrict; infer_instance
  have hF : F.IsSNC (Z ↘ Spec (.of ℂ)) := hM.comp_eq ▸ hM.isSNC
  haveI : ∀ E : Mori.PrimeDivisor Z,
      LocallyOfFinitePresentation (E.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ)) := fun _ =>
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  set W : Z.Opens := r ⁻¹ᵁ X with hW
  have hWF := isSNC_restrictOpen' _ hF W
  -- the components of `F` meeting `W`, restricted to `W`
  have hmemW : ∀ E ∈ F.support, ∀ w : W.toScheme, W.ι w ∈ E.support →
      ∃ E' ∈ (F.restrictOpen W).support, OpenWeilRestriction.primeDivisorMap W.ι E' = E ∧
        w ∈ E'.support := by
    intro E hE w hw
    obtain ⟨E', hE'⟩ :=
      MMP.Threefold.Mori.OpenRestriction.exists_primeDivisorMap_eq_of_mem_support W.ι E w hw
    refine ⟨E', ?_, hE', (MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff
      W.ι E' w).1 (hE' ▸ hw)⟩
    rw [Finsupp.mem_support_iff]
    change F (OpenWeilRestriction.primeDivisorMap W.ι E') ≠ 0
    rw [hE']
    exact Finsupp.mem_support_iff.1 hE
  exact
  { B := Bo.toScheme
    sB := Bo.ι ≫ s𝔸¹ℂ
    lft := inferInstance
    sep := inferInstance
    qc := inferInstance
    smooth := by
      have : SmoothOfRelativeDimension (0 + 1) (Bo.ι ≫ s𝔸¹ℂ) := inferInstance
      simpa using this
    X := X
    le_U₀ := le_rfl
    mem_X := pointsOver_mono Set.inter_subset_left hb
    lftX := inferInstance
    qcX := inferInstance
    φ := coordinateRestrict V g Bo
    hφ := by
      rw [← Category.assoc, coordinateRestrict_ι, Category.assoc, hg, ← Category.assoc,
        Scheme.homOfLE_ι]
    C := C
    iC := iC
    isClosedImmersion := hci
    range_iC := hrange
    sepC := hsep
    finite := hfin
    etale := het
    W := W
    lftW := inferInstance
    sepW := inferInstance
    qcW := inferInstance
    smoothW := inferInstance
    ρ := r ∣_ X
    hρ := morphismRestrict_ι r X
    supp_subset_W := Set.inter_subset_left
    supp_inter_eq := by
      have hXU : (X : Set Y) ⊆ U := hXV.trans hVU
      rw [hM.supp_eq_preimage_singularLocus, ← Set.preimage_inter]
      congr 1
      calc (X : Set Y) ∩ (singularLocus (Y ↘ Spec (.of ℂ)) : Set Y)
          = (X : Set Y) ∩ ((U : Set Y) ∩ (singularLocus (Y ↘ Spec (.of ℂ)) : Set Y)) := by
            rw [← Set.inter_assoc, Set.inter_eq_left.2 hXU]
        _ = (X : Set Y) ∩ T := by rw [hUS, ← Set.inter_assoc, Set.inter_eq_left.2 hXU]
    s := (F.restrictOpen W).support
    isSNC := by
      refine (DivisorWithCoeffs.isSNC_iff_of_support_eq ?_).1 hWF
      ext E
      simp only [Finsupp.mem_support_iff, Finsupp.finset_sum_apply, Finsupp.single_apply,
        Finset.sum_ite_eq', ne_eq]
      split_ifs with h <;> simp [h]
    smooth_strata := by
      intro J hJ
      set J₀ := J.image (OpenWeilRestriction.primeDivisorMap W.ι) with hJ₀
      have hJ₀F : J₀ ⊆ F.support := by
        intro E hE
        obtain ⟨E', hE', rfl⟩ := Finset.mem_image.1 hE
        exact Finsupp.mem_support_iff.2
          (Finsupp.mem_support_iff.1 (hJ hE') : F.restrictOpen W E' ≠ 0)
      let incl : W.toScheme ⟶ (r ⁻¹ᵁ V).toScheme := Z.homOfLE (r.preimage_mono hXV)
      have hincl : incl ≫ (r ⁻¹ᵁ V).ι = W.ι := Scheme.homOfLE_ι _ _
      have hI : (⨆ E ∈ J, E.idealSheaf) =
          ((⨆ E ∈ J₀, E.idealSheaf).comap (r ⁻¹ᵁ V).ι).comap incl := by
        rw [← Scheme.IdealSheafData.comap_comp, hincl,
          (Scheme.IdealSheafData.map_gc W.ι).l_iSup₂, hJ₀, Finset.iSup_finset_image]
        simp only [MMP.Threefold.Mori.OpenRestriction.idealSheaf_comap_primeDivisorMap]
      obtain ⟨k, hk, hcomm, -⟩ :=
        MMP.Threefold.Mori.OpenRestriction.exists_openImmersion_comap_subscheme incl
          ((⨆ E ∈ J₀, E.idealSheaf).comap (r ⁻¹ᵁ V).ι)
      have h1 : r ∣_ X ≫ Y.homOfLE hXV = incl ≫ r ∣_ V := by
        rw [← cancel_mono V.ι]
        simp only [Category.assoc, Scheme.homOfLE_ι, morphismRestrict_ι]
        rw [← Category.assoc incl, hincl]
      have hsq : ((((⨆ E ∈ J₀, E.idealSheaf).comap (r ⁻¹ᵁ V).ι).comap incl).subschemeι ≫
          r ∣_ X ≫ coordinateRestrict V g Bo) ≫ Bo.ι =
          k ≫ ((⨆ E ∈ J₀, E.idealSheaf).comap (r ⁻¹ᵁ V).ι).subschemeι ≫ r ∣_ V ≫ g := by
        rw [Category.assoc, Category.assoc, coordinateRestrict_ι, ← Category.assoc (r ∣_ X), h1,
          Category.assoc, ← Category.assoc _ incl, hcomm, Category.assoc]
      rw [hI]
      haveI : LocallyOfFinitePresentation
          ((((⨆ E ∈ J₀, E.idealSheaf).comap (r ⁻¹ᵁ V).ι).comap incl).subschemeι ≫
            r ∣_ X ≫ coordinateRestrict V g Bo) :=
        LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
      refine Scheme.Hom.smoothLocus_eq_top_iff.mp (eq_top_iff.2 fun x _ => ?_)
      refine formallySmooth_stalkMap_of_comp_eq hsq x (hsm J₀ hJ₀F (k x) ?_)
      rw [← Scheme.Hom.comp_apply, ← hsq, Scheme.Hom.comp_apply]
      exact (Scheme.Opens.ι_apply _ _ ▸ (_ : Bo.toScheme).2 : _ ∈ Bo).2
    trace_eq := by
      intro E hE
      refine ⟨(F.restrictOpen W).support.filter
        (fun E' => OpenWeilRestriction.primeDivisorMap W.ι E' = E), Finset.filter_subset _ _, ?_⟩
      ext w
      simp only [Set.mem_preimage, Set.mem_iUnion, Finset.mem_filter, exists_prop]
      constructor
      · intro hw
        obtain ⟨E', hE's, hE', hw'⟩ := hmemW E hE w hw
        exact ⟨E', ⟨hE's, hE'⟩, hw'⟩
      · rintro ⟨E', ⟨-, rfl⟩, hw⟩
        exact (MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff W.ι E' w).2 hw
    trace_supp := by
      rw [DivisorWithCoeffs.coe_supp]
      ext w
      simp only [Set.mem_preimage, Set.mem_iUnion, exists_prop]
      constructor
      · rintro ⟨E, hE, hw⟩
        obtain ⟨E', hE's, -, hw'⟩ := hmemW E hE w hw
        exact ⟨E', hE's, hw'⟩
      · rintro ⟨E', hE', hw⟩
        refine ⟨OpenWeilRestriction.primeDivisorMap W.ι E', Finsupp.mem_support_iff.2
          (Finsupp.mem_support_iff.1 hE' : F.restrictOpen W E' ≠ 0), ?_⟩
        exact (MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff W.ι E' w).2 hw }

end AlgebraicChart

/-- **Exceptional charts exist over a general open of `T`.** There is an open `U₀` meeting `T`
such that every `b ∈ (U₀ ∩ T)(ℂ)` has an exceptional chart. -/
theorem exists_open_forall_nonempty_exceptionalChart
    (hM : IsCurvePointExceptionalModel (Y ↘ Spec (.of ℂ)) r F D)
    (T : IrreducibleCloseds Y) (hTs : (T : Set Y) ⊆ (singularLocus (Y ↘ Spec (.of ℂ)) : Set Y))
    (hT1 : topologicalKrullDim (T : Set Y) = 1) :
    ∃ U₀ : Y.Opens, ((U₀ : Set Y) ∩ T).Nonempty ∧
      ∀ b ∈ pointsOver (K := ℂ) ((U₀ : Set Y) ∩ T), Nonempty (ExceptionalChart r F T U₀ b) := by
  haveI : IsProper r := (IsProjectiveMorphism.isProjective hM.isResolution.2.2.2.1).isProper
  obtain ⟨U₀, hU₀, ha⟩ := exists_open_forall_nonempty_exceptionalAlgebraicChart hM T hTs hT1
  exact ⟨U₀, hU₀, fun b hb ↦ nonempty_exceptionalChart_of_algebraicChart hb (ha b hb).some⟩

open MMP.Analytic MMP.Analytic.ComplexPoints in
/-- **The product germ from an exceptional chart.** An exceptional chart at `b` gives, inside
every neighbourhood of `b`, a product germ `F_b × Δ ≃ₜ F_Δ` over a preconnected `Δ ∋ b`,
relatively open in `(U₀ ∩ T)(ℂ)`, the identity over `b`, preserving every component of `F`. -/
theorem exists_homeomorph_prod_of_exceptionalChart {T : IrreducibleCloseds Y} {U₀ : Y.Opens}
    {b : UnderlyingSpace ℂ Y} (c : ExceptionalChart r F T U₀ b) {N : Set (UnderlyingSpace ℂ Y)}
    (hN : N ∈ 𝓝 b) :
    ∃ Δ : Set (UnderlyingSpace ℂ Y), Δ ⊆ N ∧
      (∃ O, IsOpen O ∧ Δ = O ∩ pointsOver (K := ℂ) ((U₀ : Set Y) ∩ T)) ∧
      IsPreconnected Δ ∧ ∃ hbΔ : b ∈ Δ,
      ∃ Φ : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}) × Δ ≃ₜ
          ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' Δ),
        (∀ p, mapFun r (Φ p : UnderlyingSpace ℂ Z) = p.2) ∧
        (∀ z, (Φ (z, ⟨b, hbΔ⟩) : UnderlyingSpace ℂ Z) = z) ∧
        ∀ E ∈ F.support, ∀ p, (Φ p : UnderlyingSpace ℂ Z) ∈ pointsOver (E.support : Set Z) ↔
          (p.1 : UnderlyingSpace ℂ Z) ∈ pointsOver (E.support : Set Z) := by
  classical
  obtain ⟨B, sB, hlft, hsep, hqc, hsm, W, hlftW, hsepW, hqcW, hsmW, g, hg, s, hsnc, hstr, hprop,
    htr, hsupp, sheet, hsheet, hb, Bo, hBo, β, hW, hcl, hreal⟩ := c
  let sZ : Z ⟶ Spec (.of ℂ) := Z ↘ Spec (.of ℂ)
  let ι : ComplexPoints (W.ι ≫ sZ) → UnderlyingSpace ℂ Z := fun w ↦
    homeomorphUnderlyingSpace (realize W.ι rfl w)
  have hι : IsEmbedding ι := (homeomorphUnderlyingSpace (X := Z)).isEmbedding.comp
    (isOpenEmbedding_realize_ι (sX := sZ) W).isEmbedding
  have hpts : ∀ w (S : Set Z), ι w ∈ pointsOver (K := ℂ) S ↔ toScheme w ∈ W.ι.base ⁻¹' S := by
    intro w S
    rw [mem_pointsOver, Subsingleton.elim (α := Spec (.of ℂ)) (IsLocalRing.closedPoint ℂ) default]
    rfl
  have : LocallyOfFiniteType sB := hlft
  obtain ⟨Δ₁, hΔ₁o, -, hbΔ₁, O, Ub, U, -, hUb, hEb, -, hEU, Φ₁, hΦg, hΦb, hΦD⟩ :=
    @exists_homeomorph_prod_of_isSNC_of_isProperMap W B (W.ι ≫ sZ) sB hlftW hsepW hqcW hsmW
      hlft hsep hqc hsm g hg s hsnc hstr hprop (β ⟨b, hb⟩)
  have hUb' : Ub ⊆ realize g hg ⁻¹' {(β ⟨b, hb⟩ : ComplexPoints sB)} := by
    rw [hUb]; exact Set.inter_subset_right
  obtain ⟨Δ, hΔN, ⟨O', hO', hΔO'⟩, hΔc, hbΔ, Φ, hΦr, hΦb', hΦE⟩ :=
    exists_homeomorph_prod_of_isClopen_sheet (continuous_realize g hg) hι (Rz := mapFun r)
      (Ks := (s : Set (Mori.PrimeDivisor W))) (Dk := fun E ↦ {w | toScheme w ∈ E.support})
      (Eset := {w | toScheme w ∈ ⋃ E ∈ s, (E.support : Set W)})
      (by ext w; simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_coe])
      (Fs := pointsOver (K := ℂ) (F.supp : Set Z))
      (fun w ↦ by rw [hpts, Set.mem_preimage, ← Set.mem_preimage, hsupp]; rfl)
      (Es := (F.support : Set (Mori.PrimeDivisor Z)))
      (Ek := fun E ↦ pointsOver (K := ℂ) (E.support : Set Z))
      (fun E hE ↦ by
        obtain ⟨sE, hsE, hEq⟩ := htr E hE
        refine ⟨sE, Finset.coe_subset.2 hsE, fun w ↦ ?_⟩
        rw [hpts, Set.mem_preimage, ← Set.mem_preimage, hEq]
        simp only [Set.mem_iUnion, Finset.mem_coe, Set.mem_setOf_eq, exists_prop])
      hBo β hW hcl (fun w hw hw' ↦ hreal w hw hw') hb
      (fun _ ↦ exists_isOpen_isPreconnected_subset_of_mem_nhds) hΔ₁o hbΔ₁ hUb' hEb hEU Φ₁ hΦg
      hΦb (fun k hk p ↦ hΦD k hk p) hN
  obtain ⟨O₀, hO₀, hsheetO⟩ := hsheet
  refine ⟨Δ, hΔN, ⟨O' ∩ O₀, hO'.inter hO₀, ?_⟩, hΔc, hbΔ, Φ, hΦr, hΦb', hΦE⟩
  rw [hΔO', hsheetO, Set.inter_assoc]

/-- **Product germ of the exceptional family.** Over a general open `U₀` of a singular curve `T`,
for every `b ∈ (U₀ ∩ T)(ℂ)` and every neighbourhood `N` of `b`, there are a preconnected `Δ ∋ b`,
relatively open in `(U₀ ∩ T)(ℂ)` and contained in `N`, and a homeomorphism
`Φ : F_b × Δ ≃ₜ F_Δ` over `Δ`, the identity over `b`, preserving every component of `F`. -/
theorem exists_homeomorph_prod_exceptionalFibre
    (hM : IsCurvePointExceptionalModel (Y ↘ Spec (.of ℂ)) r F D)
    (T : IrreducibleCloseds Y) (hTs : (T : Set Y) ⊆ (singularLocus (Y ↘ Spec (.of ℂ)) : Set Y))
    (hT1 : topologicalKrullDim (T : Set Y) = 1) :
    ∃ U₀ : Y.Opens, ((U₀ : Set Y) ∩ T).Nonempty ∧
      ∀ b ∈ pointsOver (K := ℂ) ((U₀ : Set Y) ∩ T), ∀ N ∈ 𝓝 b,
        ∃ Δ : Set (UnderlyingSpace ℂ Y), Δ ⊆ N ∧
          (∃ O, IsOpen O ∧ Δ = O ∩ pointsOver (K := ℂ) ((U₀ : Set Y) ∩ T)) ∧
          IsPreconnected Δ ∧ ∃ hbΔ : b ∈ Δ,
          ∃ Φ : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}) × Δ ≃ₜ
              ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' Δ),
            (∀ p, mapFun r (Φ p : UnderlyingSpace ℂ Z) = p.2) ∧
            (∀ z, (Φ (z, ⟨b, hbΔ⟩) : UnderlyingSpace ℂ Z) = z) ∧
            ∀ E ∈ F.support, ∀ p, (Φ p : UnderlyingSpace ℂ Z) ∈ pointsOver (E.support : Set Z) ↔
              (p.1 : UnderlyingSpace ℂ Z) ∈ pointsOver (E.support : Set Z) := by
  obtain ⟨U₀, hU₀, hc⟩ := exists_open_forall_nonempty_exceptionalChart hM T hTs hT1
  exact ⟨U₀, hU₀, fun b hb N hN ↦ exists_homeomorph_prod_of_exceptionalChart (hc b hb).some hN⟩

/-- **Connectedness of a double surface over a general open.** For a double surface `S` of `F`
mapping onto the singular curve `T`, over a general open `U₀` of `T` and every smaller open `U`
meeting `T`, the complex points of `S ∩ r⁻¹(U)` form a connected set. -/
theorem isConnected_pointsOver_doubleSurface_inter
    (hM : IsCurvePointExceptionalModel (Y ↘ Spec (.of ℂ)) r F D)
    (T : IrreducibleCloseds Y) (hTs : (T : Set Y) ⊆ (singularLocus (Y ↘ Spec (.of ℂ)) : Set Y))
    (hT1 : topologicalKrullDim (T : Set Y) = 1) :
    ∃ U₀ : Y.Opens, ((U₀ : Set Y) ∩ T).Nonempty ∧ ∀ σ : DoubleSurface F,
      r.base '' σ.carrier = (T : Set Y) → ∀ U ≤ U₀, ((U : Set Y) ∩ T).Nonempty →
        IsConnected (pointsOver (K := ℂ) (σ.carrier ∩ r.base ⁻¹' (U : Set Y))) := by
  obtain ⟨y₀, hy₀⟩ := T.isIrreducible.nonempty
  refine ⟨⊤, ⟨y₀, trivial, hy₀⟩, fun σ hσ U _ hU ↦ ?_⟩
  haveI : IsProper (r ≫ Y ↘ Spec (.of ℂ)) := by
    haveI := (IsProjectiveMorphism.isProjective hM.isProjectiveVariety.isProjective).isProper
    haveI := (IsProjectiveMorphism.isProjective hM.isResolution.2.2.2.1).isProper
    infer_instance
  have hirr : IsIrreducible σ.carrier :=
    MMP.Fourfold.Conductor.ProofLemContractedEdgeInjectivity.isIrreducible_carrier hM.isSNC σ
  have hsupp : ∀ E : Mori.PrimeDivisor Z, IsClosed (E.support : Set Z) := fun E ↦ by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isClosed_closure
  obtain ⟨x, -, hx⟩ := σ.isComponent
  have hcl : IsClosed σ.carrier :=
    hx ▸ isClosed_connectedComponentIn_of_isClosed ((hsupp σ.fst).inter (hsupp σ.snd)) x
  set I := Scheme.IdealSheafData.vanishingIdeal ⟨σ.carrier, hcl⟩ with hI
  haveI : IsIntegral I.subscheme :=
    StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible _ hirr
  have hrange : Set.range I.subschemeι = σ.carrier := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  set Zc : Set I.subscheme := I.subschemeι.base ⁻¹' (r.base ⁻¹' (U : Set Y))ᶜ with hZc
  have hZcl : IsClosed Zc :=
    ((U.isOpen.preimage r.continuous).isClosed_compl).preimage I.subschemeι.continuous
  have hZne : Zc ≠ Set.univ := by
    obtain ⟨y, hyU, hyT⟩ := hU
    rw [← hσ] at hyT
    obtain ⟨z, hzσ, rfl⟩ := hyT
    rw [← hrange] at hzσ
    obtain ⟨w, rfl⟩ := hzσ
    exact fun h ↦ (h ▸ Set.mem_univ w : w ∈ Zc) hyU
  have hconn := MMP.UnderlyingSpace.isConnected_regularPart_diff
    (X := I.subscheme) hZcl hZne
  have hdense := MMP.UnderlyingSpace.dense_regularPart_diff
    (X := I.subscheme) hZcl hZne
  set A : Set (UnderlyingSpace ℂ I.subscheme) :=
    {p | p.toHom (IsLocalRing.closedPoint ℂ) ∉ Zc} with hA
  have hAconn : IsConnected A :=
    hconn.subset_closure (fun p hp ↦ hp.2) (by rw [hdense.closure_eq]; exact Set.subset_univ _)
  have himage : map (K := ℂ) I.subschemeι '' A =
      pointsOver (K := ℂ) (σ.carrier ∩ r.base ⁻¹' (U : Set Y)) := by
    ext q
    constructor
    · rintro ⟨p, hp, rfl⟩
      refine ⟨?_, ?_⟩
      · change I.subschemeι (p.toHom (IsLocalRing.closedPoint ℂ)) ∈ σ.carrier
        have h := Set.mem_range_self (f := I.subschemeι.base) (p.toHom (IsLocalRing.closedPoint ℂ))
        rwa [hrange] at h
      · change r (I.subschemeι (p.toHom (IsLocalRing.closedPoint ℂ))) ∈ (U : Set Y)
        by_contra h
        exact hp h
    · rintro ⟨hqσ, hqU⟩
      have hq : q ∈ Set.range (map (K := ℂ) I.subschemeι) := by
        rw [range_map_of_isClosedImmersion]
        change q.toHom (IsLocalRing.closedPoint ℂ) ∈ Set.range I.subschemeι
        rw [hrange]; exact hqσ
      obtain ⟨p, rfl⟩ := hq
      refine ⟨p, fun h ↦ h hqU, rfl⟩
  rw [← himage]
  exact hAconn.image _ (map (K := ℂ) I.subschemeι).continuous.continuousOn

end MMP.Fourfold
