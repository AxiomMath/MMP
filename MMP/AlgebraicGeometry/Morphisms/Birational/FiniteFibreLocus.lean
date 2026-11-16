module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Morphisms.Birational.RationalMap
public import StacksFrontier.AlgebraicGeometry.Variety.Geometric.BirationalIsomorphismLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.BirationalIsIso
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.LocallyProjective
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Basic
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.LocalizationBaseChange

/-!
# The finite-fibre locus of a proper birational morphism

Let `f : X ⟶ Y` be a proper birational morphism of integral schemes with `Y` normal. The set
`U ⊆ Y` of points with finite fibre is open and `f⁻¹(U) ⟶ U` is an isomorphism.

## Main results

* `MMP.Resolution.Bridges.subsingleton_preimage_of_isIso_morphismRestrict`: if `f ∣_ V` is an
  isomorphism, the fibres of `f` over the points of `V` have at most one point.
* `MMP.Resolution.Bridges.finite_preimage_singleton_of_topologicalKrullDim_le`: a fibre of
  dimension at most `0` of a quasi-compact morphism locally of finite type is finite.
* `MMP.Resolution.Bridges.isOpen_finiteFibreLocus_and_isIso`: the finite-fibre locus `U` is open,
  `f ∣_ U` is an isomorphism, and a finite birational morphism to a normal integral scheme is an
  isomorphism.
* `MMP.Resolution.Bridges.isOpen_finiteFibreLocus_and_isIso_of_isProjective`: the same for a
  projective birational morphism of integral schemes.
* `MMP.Resolution.Bridges.isIso_finiteFibreLocus_and_exceptionalSet_eq`: for a proper birational
  morphism of varieties onto a normal variety, the exceptional set is the union of the
  positive-dimensional fibres, and a quasi-finite such morphism is an isomorphism.

## Implementation notes

* Birationality is `AlgebraicGeometry.IsBirational` (Stacks 01RO), normality
  `AlgebraicGeometry.IsNormal` (Stacks 033I), projectivity `AlgebraicGeometry.IsProjective`
  (Stacks 01W8), and a variety is `AlgebraicGeometry.IsVariety k s` for the structure morphism `s`.
* The exceptional set is `MMP.Mori.exceptionalSet` (KM 0, the complement of the
  preimage of the largest open over which `f` is an isomorphism); a fibre `f⁻¹(y)` is
  positive-dimensional when its topological Krull dimension, in the subspace topology, is positive.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace MMP.Resolution.Bridges

/-- The set of points of `Y` whose set-theoretic fibre under `f` is finite. -/
def finiteFibreLocus {X Y : Scheme.{u}} (f : X ⟶ Y) : Set Y :=
  {y | (f ⁻¹' {y}).Finite}

@[simp]
theorem mem_finiteFibreLocus {X Y : Scheme.{u}} {f : X ⟶ Y} {y : Y} :
    y ∈ finiteFibreLocus f ↔ (f ⁻¹' {y}).Finite :=
  Iff.rfl

/-- A fibre of topological Krull dimension at most `0` of a quasi-compact morphism locally of
finite type is finite. -/
theorem finite_preimage_singleton_of_topologicalKrullDim_le {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f] (y : Y) (h : topologicalKrullDim (f ⁻¹' {y}) ≤ 0) :
    (f ⁻¹' {y}).Finite := by
  have h' : topologicalKrullDim (f.fiber y) ≤ 0 := by
    rwa [IsHomeomorph.topologicalKrullDim_eq _ (f.fiberHomeo y).isHomeomorph]
  have : IsLocallyNoetherian (f.fiber y) :=
    inferInstanceAs (IsLocallyNoetherian (Limits.pullback f (Y.fromSpecResidueField y)))
  have : IsLocallyArtinian (f.fiber y) := IsLocallyArtinian.of_topologicalKrullDim_le_zero h'
  have : DiscreteTopology (f.fiber y) :=
    (IsLocallyArtinian.iff_isLocallyNoetherian_and_discreteTopology.mp inferInstance).2
  have : Finite (f.fiber y) := finite_of_compact_of_discrete
  exact Set.finite_coe_iff.mp (Finite.of_equiv _ (f.fiberHomeo y).toEquiv)

section Helpers

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

private lemma preimage_singleton_eq_image {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) (y : V) :
    f ⁻¹' {(y : Y)} = (f ⁻¹ᵁ V).ι '' ((f ∣_ V) ⁻¹' {y}) := by
  have hmap (z : (f ⁻¹ᵁ V : X.Opens)) : V.ι ((f ∣_ V) z) = f ((f ⁻¹ᵁ V).ι z) :=
    congrArg (fun g : (f ⁻¹ᵁ V).toScheme ⟶ Y => g z) (morphismRestrict_ι f V)
  ext x
  refine ⟨fun hx => ?_, ?_⟩
  · have hxV : x ∈ f ⁻¹ᵁ V := by
      change f x ∈ V
      rw [show f x = y from hx]
      exact y.2
    refine ⟨⟨x, hxV⟩, ?_, rfl⟩
    apply V.ι.isOpenEmbedding.injective
    rwa [hmap]
  · rintro ⟨z, hz, rfl⟩
    exact (hmap z).symm.trans (congrArg V.ι hz)

private lemma isIso_morphismRestrict_of_isFinite {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] [IsNormal Y] (f : X ⟶ Y) (hf : IsBirational f) (V : Y.Opens)
    [IsFinite (f ∣_ V)] : IsIso (f ∣_ V) := by
  by_cases hV : Nonempty V
  · have : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
    have hne : Nonempty (f ⁻¹ᵁ V) := by
      have hηX : genericPoint X ∈ genericPoints X := by simp [genericPoints_eq_singleton]
      have heq : f (genericPoint X) = genericPoint Y := by
        simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using hf.bijOn.1 hηX
      obtain ⟨v⟩ := hV
      refine ⟨⟨genericPoint X, ?_⟩⟩
      change f (genericPoint X) ∈ V
      rw [heq]
      exact ((genericPoint_spec Y).mem_open_set_iff V.isOpen).2 ⟨v.1, Set.mem_univ _, v.2⟩
    have : IsIntegral (f ⁻¹ᵁ V).toScheme := isIntegral_of_isOpenImmersion (f ⁻¹ᵁ V).ι
    have : IsNormal V.toScheme := isNormal_of_flat_preimmersion V.ι
    exact isIso_of_isIntegralHom_of_isBirational_of_isNormal _ (birational_morphismRestrict f hf V)
  · have : IsEmpty V.toScheme := not_nonempty_iff.mp hV
    infer_instance

private lemma exists_biregular_of_finite_fibre {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsNormal Y] (f : X ⟶ Y) (hf : IsBirational f) [IsProper f] (y : Y)
    (hy : (f ⁻¹' {y}).Finite) : ∃ V : Y.Opens, y ∈ V ∧ V.1 ⊆ finiteFibreLocus f ∧
      MMP.Mori.IsBiregular f V := by
  obtain ⟨V, hyV, hV⟩ := exists_isFinite_morphismRestrict_of_finite_preimage_singleton f y hy
  refine ⟨V, hyV, fun y' hy' => ?_, isIso_morphismRestrict_of_isFinite f hf V⟩
  rw [mem_finiteFibreLocus, show y' = ((⟨y', hy'⟩ : V) : Y) from rfl, preimage_singleton_eq_image]
  exact ((f ∣_ V).finite_preimage_singleton _).image _

private lemma isOpen_and_isBiregular_finiteFibreLocus {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] [IsNormal Y] (f : X ⟶ Y) (hf : IsBirational f) [IsProper f] :
    ∃ hU : IsOpen (finiteFibreLocus f), MMP.Mori.IsBiregular f ⟨finiteFibreLocus f, hU⟩ := by
  have hU : IsOpen (finiteFibreLocus f) := by
    rw [isOpen_iff_forall_mem_open]
    intro y hy
    obtain ⟨V, hyV, hVU, -⟩ := exists_biregular_of_finite_fibre f hf y hy
    exact ⟨V.1, hVU, V.isOpen, hyV⟩
  refine ⟨hU, ?_⟩
  rw [MMP.Mori.isBiregular_iff_le_biregularLocus]
  intro y hy
  obtain ⟨V, hyV, -, hV⟩ := exists_biregular_of_finite_fibre f hf y hy
  exact MMP.Mori.le_biregularLocus hV hyV

/-- A morphism that restricts to an isomorphism over an open `V` has subsingleton fibres over
the points of `V`. -/
theorem subsingleton_preimage_of_isIso_morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y)
    (V : Y.Opens) [IsIso (f ∣_ V)] {y : Y} (hy : y ∈ V) : (f ⁻¹' {y}).Subsingleton := by
  rw [show y = ((⟨y, hy⟩ : V) : Y) from rfl, preimage_singleton_eq_image]
  exact Set.Subsingleton.image (fun a ha b hb => (f ∣_ V).injective (ha.trans hb.symm)) _

private lemma coe_biregularLocus_eq_finiteFibreLocus {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] [IsNormal Y] (f : X ⟶ Y) (hf : IsBirational f) [IsProper f] :
    ((MMP.Mori.biregularLocus f : Y.Opens) : Set Y) = finiteFibreLocus f := by
  ext y
  constructor
  · intro hy
    have : IsIso (f ∣_ MMP.Mori.biregularLocus f) := MMP.Mori.isBiregular_biregularLocus f
    exact (subsingleton_preimage_of_isIso_morphismRestrict f _ hy).finite
  · intro hy
    obtain ⟨V, hyV, -, hV⟩ := exists_biregular_of_finite_fibre f hf y hy
    exact MMP.Mori.le_biregularLocus hV hyV

end Helpers

/-- **The finite-fibre locus of a proper birational morphism.** Let `f : X ⟶ Y` be a proper
birational morphism of integral schemes with `Y` normal. The set `U` of points of `Y` with finite
fibre is open and `f⁻¹(U) ⟶ U` is an isomorphism. In particular a finite birational morphism of
integral schemes to a normal target is an isomorphism. -/
@[mmp "lem_mmp_foundation_proper_birational_finite_fibre_locus"]
theorem isOpen_finiteFibreLocus_and_isIso {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsNormal Y] (f : X ⟶ Y) (hf : IsBirational f) :
    (IsProper f → ∃ hU : IsOpen (finiteFibreLocus f),
      IsIso (f ∣_ ⟨finiteFibreLocus f, hU⟩)) ∧
    (IsFinite f → IsIso f) :=
  ⟨fun _ => isOpen_and_isBiregular_finiteFibreLocus f hf,
    fun _ => isIso_of_isIntegralHom_of_isBirational_of_isNormal f hf⟩

/-- **The finite-fibre locus of a projective birational morphism.** Let `g : S ⟶ X` be a
projective birational morphism of integral schemes with `X` normal. The set `U` of
points of `X` with finite fibre is open and `g⁻¹(U) ⟶ U` is an isomorphism. -/
@[mmp "lem_mmp_foundation_projective_birational_finite_fibre_locus"]
theorem isOpen_finiteFibreLocus_and_isIso_of_isProjective {S X : Scheme.{u}} [IsIntegral S]
    [IsIntegral X] [IsNormal X] (g : S ⟶ X) (hg : IsProjective g) (hb : IsBirational g) :
    ∃ hU : IsOpen (finiteFibreLocus g), IsIso (g ∣_ ⟨finiteFibreLocus g, hU⟩) :=
  (isOpen_finiteFibreLocus_and_isIso g hb).1 hg.isProper

/-- **The finite-fibre isomorphism locus of a birational morphism of varieties.** Let
`h : U ⟶ R` be a proper birational morphism of varieties over `k` with `R` normal. Then `h` is an
isomorphism over the open set of points of `R` whose fibre is finite; the exceptional set of `h`
is the union of its positive-dimensional fibres; and if `h` is moreover quasi-finite, it is an
isomorphism. -/
@[mmp "lem_mmp_foundation_bg_finite_fibre_isomorphism"]
theorem isIso_finiteFibreLocus_and_exceptionalSet_eq (k : Type u) [Field k] {U R : Scheme.{u}}
    {sU : U ⟶ Spec (.of k)} {sR : R ⟶ Spec (.of k)} (hU : IsVariety k sU) (hR : IsVariety k sR)
    [IsNormal R] (h : U ⟶ R) (hh : h ≫ sR = sU) [IsProper h] (hb : IsBirational h) :
    (∃ hO : IsOpen (finiteFibreLocus h), IsIso (h ∣_ ⟨finiteFibreLocus h, hO⟩)) ∧
    (MMP.Mori.exceptionalSet h : Set U) =
      {u | 0 < topologicalKrullDim (h ⁻¹' {h u})} ∧
    (LocallyQuasiFinite h → IsIso h) := by
  have := hU.toIsIntegral
  have := hR.toIsIntegral
  have : LocallyOfFiniteType sU := hU.toLocallyOfFiniteType
  subst hh
  have : LocallyOfFiniteType h := locallyOfFiniteType_of_comp h sR
  have hloc := isOpen_and_isBiregular_finiteFibreLocus h hb
  refine ⟨hloc, ?_, ?_⟩
  · ext u
    have e : h u ∈ MMP.Mori.biregularLocus h ↔ h u ∈ finiteFibreLocus h :=
      Set.ext_iff.mp (coe_biregularLocus_eq_finiteFibreLocus h hb) (h u)
    have hmem : h u ∈ MMP.Mori.biregularLocus h ↔ ¬ 0 < topologicalKrullDim (h ⁻¹' {h u}) := by
      refine ⟨fun hbm => ?_, fun hn =>
        e.mpr (finite_preimage_singleton_of_topologicalKrullDim_le h (h u) (not_lt.mp hn))⟩
      have : IsIso (h ∣_ MMP.Mori.biregularLocus h) := MMP.Mori.isBiregular_biregularLocus h
      have : Subsingleton (h ⁻¹' {h u}) :=
        (subsingleton_preimage_of_isIso_morphismRestrict h _ hbm).coe_sort
      exact not_lt.mpr (topologicalKrullDim_zero_of_discreteTopology _)
    change h u ∉ MMP.Mori.biregularLocus h ↔ _
    rw [hmem, not_not]
    rfl
  · intro hq
    have hall : finiteFibreLocus h = Set.univ :=
      Set.eq_univ_of_forall h.finite_preimage_singleton
    have htop : (⟨finiteFibreLocus h, hloc.1⟩ : R.Opens) = ⊤ := by
      ext y
      simp [hall]
    have := hloc.2
    rw [htop] at this
    exact (MMP.Mori.isBiregular_top_iff h).mp this

end MMP.Resolution.Bridges
