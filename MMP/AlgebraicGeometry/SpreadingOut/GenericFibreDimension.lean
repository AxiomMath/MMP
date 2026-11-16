module

public import MMP.Attr
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.GenericConstancy
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
public import Mathlib.AlgebraicGeometry.Fiber

/-!
# The fibre dimension bound spreads out from the generic fibre

If `W → Spec R` is of finite presentation with `W` quasi-compact and quasi-separated, `R` a
domain with fraction field `F`, and the generic fibre `W_F` has dimension at most `d`, then after
inverting a nonzero element of `R` every fibre has dimension at most `d`; if `W_F` is empty,
`W` becomes empty after such an inversion.

## Main results

* `MMP.Threefold.Bridges.exists_forall_fiberDimension_le_of_genericFibre`: the fibre dimension
  bound spreads out from the generic fibre.
* `MMP.Threefold.Bridges.exists_isEmpty_of_isEmpty_genericFibre`: an empty generic fibre forces
  emptiness over a nonempty principal open.

## Implementation notes

"After inverting a nonzero `r ∈ R`" is expressed over the original ring: the fibres of the base
change to `Spec R[1/r]` are the fibres over the points of the principal open `D(r) ⊆ Spec R`,
with the same residue fields.

The proof uses generic constancy of the fibre dimension (Stacks, Tag 05F7) and Chevalley's
theorem: a constructible image missing the generic point misses a principal open around it.

## References

* [The Stacks Project, Tag 05F7](https://stacks.math.columbia.edu/tag/05F7)
* [The Stacks Project, Tag 05M5](https://stacks.math.columbia.edu/tag/05M5)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace MMP.Threefold.Bridges

section GenericFibreHelpers

open Topology

/-- In a space with a generic point `η`, a constructible set containing `η` contains an open
neighbourhood of `η`, and one not containing `η` is disjoint from an open neighbourhood of `η`. -/
theorem exists_isOpen_mem_subset_of_isConstructible {X : Type*} [TopologicalSpace X] {η : X}
    (hη : IsGenericPoint η Set.univ) {s : Set X} (hs : IsConstructible s) :
    (η ∈ s → ∃ U : Set X, IsOpen U ∧ η ∈ U ∧ U ⊆ s) ∧
      (η ∉ s → ∃ U : Set X, IsOpen U ∧ η ∈ U ∧ U ⊆ sᶜ) := by
  induction hs using IsConstructible.empty_union_induction with
  | open_retrocompact U hU _ =>
    refine ⟨fun h ↦ ⟨U, hU, h, subset_rfl⟩, fun h ↦ ⟨Set.univ, isOpen_univ, trivial, ?_⟩⟩
    have : U = ∅ := by
      by_contra hne
      exact h ((hη.mem_open_set_iff hU).mpr (by simpa using Set.nonempty_iff_ne_empty.mpr hne))
    simp [this]
  | union s _ t _ hs ht =>
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · rcases h with h | h
      · obtain ⟨U, hU, hηU, hUs⟩ := hs.1 h
        exact ⟨U, hU, hηU, hUs.trans Set.subset_union_left⟩
      · obtain ⟨U, hU, hηU, hUs⟩ := ht.1 h
        exact ⟨U, hU, hηU, hUs.trans Set.subset_union_right⟩
    · rw [Set.mem_union, not_or] at h
      obtain ⟨U, hU, hηU, hUs⟩ := hs.2 h.1
      obtain ⟨V, hV, hηV, hVt⟩ := ht.2 h.2
      refine ⟨U ∩ V, hU.inter hV, ⟨hηU, hηV⟩, ?_⟩
      rw [Set.compl_union]
      exact Set.inter_subset_inter hUs hVt
  | compl s _ hs =>
    refine ⟨hs.2, fun h ↦ ?_⟩
    simpa using hs.1 (not_not.mp h)

/-- A nonempty open subset of `Spec R` contains a principal open `D(r)` with `r ≠ 0`. -/
theorem exists_ne_zero_forall_mem_of_isOpen {R : Type u} [CommRing R]
    (V : Set (PrimeSpectrum R)) (hV : IsOpen V) (hne : V.Nonempty) :
    ∃ r : R, r ≠ 0 ∧ ∀ y : PrimeSpectrum R, r ∉ y.asIdeal → y ∈ V := by
  obtain ⟨y₀, hy₀⟩ := hne
  obtain ⟨_, ⟨r, rfl⟩, hy₀r, hrV⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hy₀ hV
  refine ⟨r, ?_, fun y hy ↦ hrV hy⟩
  rintro rfl
  exact hy₀r y₀.asIdeal.zero_mem

variable {R : Type u} [CommRing R] [IsDomain R] (F : Type u) [Field F] [Algebra R F]
  [IsFractionRing R F]

/-- The zero ideal of a domain is the generic point of its spectrum. -/
theorem isGenericPoint_bot_primeSpectrum :
    IsGenericPoint (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) Set.univ :=
  isGenericPoint_iff_specializes.mpr fun y ↦
    iff_of_true ((PrimeSpectrum.le_iff_specializes _ y).mp bot_le) trivial

/-- The image of `Spec F → Spec R`, for the fraction field `F` of a domain `R`, is the generic
point. -/
theorem range_spec_map_algebraMap_fractionRing :
    Set.range (Spec.map (CommRingCat.ofHom (algebraMap R F))) =
      {(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)} := by
  have key : ∀ p : PrimeSpectrum F, Spec.map (CommRingCat.ofHom (algebraMap R F)) p =
      (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) := fun p ↦ PrimeSpectrum.ext <| by
    change Ideal.comap (algebraMap R F) p.asIdeal = ⊥
    rw [Ideal.eq_bot_of_prime p.asIdeal, ← RingHom.ker_eq_comap_bot]
    exact (RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective R F)
  exact Set.eq_singleton_iff_unique_mem.mpr
    ⟨⟨⟨⊥, Ideal.isPrime_bot⟩, key _⟩, fun _ ⟨p, hp⟩ ↦ hp ▸ key p⟩

/-- If a morphism of finite presentation from a quasi-compact scheme to `Spec R`, `R` a domain,
misses the generic point, its image misses a principal open `D(r)` with `r ≠ 0`. -/
theorem exists_ne_zero_forall_mem_of_not_mem_range {W : Scheme.{u}}
    (f : W ⟶ Spec (CommRingCat.of R)) [LocallyOfFinitePresentation f] [CompactSpace W]
    (h : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) ∉ Set.range f) :
    ∃ r : R, r ≠ 0 ∧ ∀ x : W, r ∈ (f x).asIdeal := by
  have hc : IsConstructible (Set.range f) := by
    simpa only [Set.image_univ] using f.isConstructible_image IsConstructible.univ
  obtain ⟨U, hU, hηU, hUs⟩ :=
    (exists_isOpen_mem_subset_of_isConstructible isGenericPoint_bot_primeSpectrum hc).2 h
  obtain ⟨r, hr, hrU⟩ := exists_ne_zero_forall_mem_of_isOpen U hU ⟨_, hηU⟩
  refine ⟨r, hr, fun x ↦ ?_⟩
  by_contra hx
  exact hUs (hrU (f x) hx) ⟨x, rfl⟩

/-- The generic fibre `W ×_{Spec R} Spec F` is homeomorphic to the fibre of `f` over the generic
point; in particular they have the same dimension. -/
theorem topologicalKrullDim_pullback_eq_fiberDimension {W : Scheme.{u}}
    (f : W ⟶ Spec (CommRingCat.of R)) :
    topologicalKrullDim
        (Limits.pullback (C := Scheme.{u}) f (Spec.map (CommRingCat.ofHom (algebraMap R F)))) =
      f.fiberDimension (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) := by
  have : IsPreimmersion (Spec.map (CommRingCat.ofHom (algebraMap R F))) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  let e := (Limits.pullback.fst f
      (Spec.map (CommRingCat.ofHom (algebraMap R F)))).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr
      (by rw [Scheme.Pullback.range_fst, range_spec_map_algebraMap_fractionRing]))
  let e' := e.trans (f.fiberHomeo (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)).symm
  exact IsHomeomorph.topologicalKrullDim_eq e' e'.isHomeomorph

end GenericFibreHelpers

section FibreDimension

variable {R : Type u} [CommRing R] [IsDomain R] (F : Type u) [Field F] [Algebra R F]
  [IsFractionRing R F]

/-- **A generic fibre dimension bound holds after shrinking.** Let `R` be a domain with fraction
field `F` and `f : W ⟶ Spec R` locally of finite presentation with `W` quasi-compact and
quasi-separated. If the generic fibre `W_F = W ×_{Spec R} Spec F` has dimension at most `d`,
there is a nonzero `r ∈ R` such that every fibre of `f` over the principal open `D(r)` has
dimension at most `d`. -/
@[mmp "lem_mmp_generic_fibre_dimension_bound"]
theorem exists_forall_fiberDimension_le_of_genericFibre {W : Scheme.{u}}
    (f : W ⟶ Spec (CommRingCat.of R)) [LocallyOfFinitePresentation f]
    [CompactSpace W] [QuasiSeparatedSpace W] (d : ℕ)
    (hd : topologicalKrullDim
        (Limits.pullback (C := Scheme.{u}) f (Spec.map (CommRingCat.ofHom (algebraMap R F)))) ≤
      (d : WithBot ℕ∞)) :
    ∃ r : R, r ≠ 0 ∧ ∀ y : PrimeSpectrum R, r ∉ y.asIdeal →
      f.fiberDimension y ≤ (d : WithBot ℕ∞) := by
  rw [topologicalKrullDim_pullback_eq_fiberDimension F f] at hd
  by_cases hbot : f.fiberDimension (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) = ⊥
  · replace hbot := (Scheme.Hom.fiberDimension_eq_bot_iff_isEmpty f _).mp hbot
    obtain ⟨r, hr, hrf⟩ := exists_ne_zero_forall_mem_of_not_mem_range f (by
      rintro ⟨x, hx⟩
      exact hbot.false (hx ▸ f.asFiber x))
    refine ⟨r, hr, fun y hy ↦ ?_⟩
    have hempty : IsEmpty (f.fiber y) := by
      refine ⟨fun z ↦ hy ?_⟩
      rw [← Scheme.Hom.apply_fiberι f y z]
      exact hrf _
    exact ((Scheme.Hom.fiberDimension_eq_bot_iff_isEmpty f y).mpr hempty).trans_le bot_le
  · obtain ⟨a, ha⟩ := WithBot.ne_bot_iff_exists.mp hbot
    rw [← ha] at hd
    have had : a ≤ (d : ℕ∞) := WithBot.coe_le_coe.mp hd
    obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (ENat.natCast_ne_top d) had)
    have hnd : n ≤ d := by exact_mod_cast had
    obtain ⟨V, hVne, hV⟩ := exists_nonempty_open_fiberDimension_eq f n
      (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) isGenericPoint_bot_primeSpectrum ha.symm
    obtain ⟨r, hr, hrV⟩ := exists_ne_zero_forall_mem_of_isOpen (R := R) V.1 V.2 hVne
    refine ⟨r, hr, fun y hy ↦ ?_⟩
    rw [hV y (hrV y hy)]
    exact_mod_cast hnd

/-- **An empty generic fibre is empty after shrinking.** Let `R` be a domain with fraction field
`F` and `f : W ⟶ Spec R` locally of finite presentation with `W` quasi-compact and
quasi-separated. If the generic fibre `W_F` is empty, there is a nonzero `r ∈ R` such that `W`
has no point over the principal open `D(r)`, i.e. its base change to `Spec R[1/r]` is empty. -/
@[mmp "lem_mmp_generic_fibre_dimension_bound"]
theorem exists_isEmpty_of_isEmpty_genericFibre {W : Scheme.{u}}
    (f : W ⟶ Spec (CommRingCat.of R)) [LocallyOfFinitePresentation f]
    [CompactSpace W] [QuasiSeparatedSpace W]
    (hempty : IsEmpty
      (Limits.pullback (C := Scheme.{u}) f (Spec.map (CommRingCat.ofHom (algebraMap R F))))) :
    ∃ r : R, r ≠ 0 ∧ ∀ x : W, r ∈ (f x).asIdeal := by
  refine exists_ne_zero_forall_mem_of_not_mem_range f ?_
  rintro ⟨x, hx⟩
  obtain ⟨z, -⟩ : x ∈ Set.range (Limits.pullback.fst f
      (Spec.map (CommRingCat.ofHom (algebraMap R F)))) := by
    rwa [Scheme.Pullback.range_fst, range_spec_map_algebraMap_fractionRing]
  exact hempty.false z

end FibreDimension

end MMP.Threefold.Bridges
