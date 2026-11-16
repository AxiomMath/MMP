module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.LogResolution.Basic
import MMP.AlgebraicGeometry.Resolution.Principalization.ResolutionPrincipalization
import MMP.AlgebraicGeometry.Morphisms.ChowLemma
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import StacksFrontier.AlgebraicGeometry.Chow.ChernClassOfSection.Induction
import StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterion.PointClosureAssociatedPoints
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import MMP.AlgebraicGeometry.MMP.Models
import MMP.AlgebraicGeometry.Divisor.SNC
import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlops
import MMP.AlgebraicGeometry.Singularities.DiscrepancyDefs
import MMP.AlgebraicGeometry.Singularities.Snc.Basic
import MMP.AlgebraicGeometry.Singularities.Snc.LocalEquations
import MMP.AlgebraicGeometry.Singularities.LogResolution.ReducedUnion
import MMP.AlgebraicGeometry.Divisor.PullbackExistence
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Divisor.RegularWeilCartier
import MMP.AlgebraicGeometry.Morphisms.Birational.FiniteFibreLocus
import MMP.AlgebraicGeometry.Divisor.SmoothRDivisors
import MMP.AlgebraicGeometry.Divisor.EffectiveCartierCoheight

/-!
# Existence of embedded resolutions of effective Cartier divisors

Let `X` be a variety over a field `k` of characteristic zero and `D` an effective Cartier divisor
on `X`. Then `(X, D)` has an embedded (log) resolution: a projective birational morphism
`μ : X' ⟶ X` from a non-singular variety `X'` whose exceptional locus is empty or of pure
codimension one, such that `D' + E_μ` has simple normal crossing support for a pull-back `D'` of
`D` and the reduced divisor `E_μ` with support `Exc(μ)` (Hironaka; Lazarsfeld Thm. 4.1.3).

## Main results

* `MMP.Intersection.exists_isEmbeddedResolution`.

## Implementation notes

The auxiliary lemmas live in the namespace
`Proof_thm_mmp_lazarsfeld_embedded_resolution_dictionary`, named after the label and
opened only for the main result.

Chow's lemma gives a proper morphism `r : X₁ ⟶ X` from a variety quasi-projective over `k` which
is an isomorphism over a dense open subset. Principalizing on `X₁` the inverse image of
`I = I_W · I_{Sing X} · I_{Supp D}`, `W` the complement of the biregular locus of `r`, gives a
resolution `f : Y ⟶ X₁`, and `g = f ≫ r` is the required morphism: it is projective in the sense
of a closed immersion into some `ℙⁿ_X`, `Exc(g)` and `g⁻¹(Supp D)` lie in the snc divisor
`Ex(f) ∪ g⁻¹ V(I)`, and `Exc(g)` is empty or of pure codimension one. Purity is proved directly,
by Krull's principal ideal theorem over the singular locus and van der Waerden's purity argument
over the smooth locus, since the Chow modification is not a sequence of blow-ups.

Lazarsfeld works over `ℂ`; the statement is made over an arbitrary field of characteristic zero,
which is the generality of Hironaka's theorem. The resolution `X'` lives in the same universe as
`X`.

## References

* [R. Lazarsfeld, *Positivity in Algebraic Geometry I*][lazarsfeld2004], Thm. 4.1.3.
* [H. Hironaka, *Resolution of singularities of an algebraic variety over a field of
  characteristic zero*][hironaka1964].
* [J. Kollár, *Lectures on resolution of singularities*], 3.26, 3.36
* [Stacks Project, Tag 0200] (Chow's lemma)
-/

@[expose] public section

universe u

namespace Proof_thm_mmp_lazarsfeld_embedded_resolution_dictionary

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP MMP.Mori MMP.Intersection

/-! ### Prime divisors and generic points -/

/-- A prime divisor is determined by its support. -/
private theorem primeDivisor_eq_of_support_eq {X : Scheme.{u}} {P Q : Mori.PrimeDivisor X}
    (h : (P.support : Set X) = Q.support) : P = Q := by
  refine AlgebraicGeometry.PrimeDivisor.genericPoint_injective ?_
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
    AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h
  exact (inseparable_iff_closure_eq.2 h).eq

/-! ### Chow's lemma -/

/-- An immersion into `ℙⁿ_S` over `S` whose composite with the structure morphism is
quasi-compact exhibits that composite as H-quasi-projective. -/
private theorem isHQuasiProjective_of_isImmersion {Y S : Scheme.{u}} {n : ℕ}
    (j : Y ⟶ projectiveSpaceOver n S) [IsImmersion j] {h : Y ⟶ S} [QuasiCompact h]
    (heq : j ≫ (projectiveSpaceOver n S ↘ S) = h) : IsHQuasiProjective h := by
  have hqs : QuasiSeparated (projectiveSpaceOver n S ↘ S) :=
    @IsSeparated.instQuasiSeparated _ _ _ (Stacks.HProjective.isSeparated_over n S)
  have : QuasiCompact (j ≫ (projectiveSpaceOver n S ↘ S)) := by rw [heq]; infer_instance
  exact ⟨n, j, inferInstance, @QuasiCompact.of_comp _ _ _ _ _ this hqs, heq⟩

/-- **Chow's lemma for a variety.** A variety `X` over `k` is the target of a proper morphism
`r : X₁ ⟶ X` from a variety `X₁` which is H-quasi-projective over `k` and an isomorphism over a
nonempty open subset of `X`. -/
private theorem exists_isHQuasiProjective_isIso_morphismRestrict {k : Type u} [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (hX : Mori.IsVariety k sX) :
    ∃ (X₁ : Scheme.{u}) (r : X₁ ⟶ X) (U : X.Opens), Mori.IsVariety k (r ≫ sX) ∧ IsProper r ∧
      (U : Set X).Nonempty ∧ IsIso (r ∣_ U) ∧ IsHQuasiProjective (r ≫ sX) := by
  haveI : IsIntegral X := hX.toIsIntegral
  haveI : IsSeparated sX := hX.toIsSeparated
  haveI : LocallyOfFiniteType sX := hX.toLocallyOfFiniteType
  haveI : QuasiCompact sX := hX.toQuasiCompact
  obtain ⟨n, X', π, i, U, hπ, -, hi, hcomm, hdense, hiso⟩ := hasDenseChowModification sX
  have hUne : Nonempty U := hdense.nonempty.to_subtype
  have hVne : Nonempty (π ⁻¹ᵁ U) := ⟨(inv (π ∣_ U)).base hUne.some⟩
  haveI : IsIntegral (π ⁻¹ᵁ U) := isIntegral_of_isOpenImmersion (π ∣_ U)
  haveI : IsSeparated (π ≫ sX) := by rw [hcomm]; infer_instance
  haveI : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian (π ≫ sX)
  haveI : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace (π ≫ sX)
  haveI : IsNoetherian X' := ⟨⟩
  have hi1 : IsIso ((π ⁻¹ᵁ U).ι.imageι ∣_ (π ⁻¹ᵁ U)) :=
    Stacks.SchemeTheoreticImage.isIso_imageι_restrict _
  refine ⟨(π ⁻¹ᵁ U).ι.image, (π ⁻¹ᵁ U).ι.imageι ≫ π, U, ?_, inferInstance, hdense.nonempty,
    ?_, ?_⟩
  · rw [Category.assoc]
    exact Scheme.Hom.isVariety_image k _ (π ≫ sX)
  · rw [morphismRestrict_comp]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ hi1 hiso
  · have heq : ((π ⁻¹ᵁ U).ι.imageι ≫ i) ≫ (ProjectiveSpace n (Spec (.of k)) ↘ Spec (.of k)) =
        ((π ⁻¹ᵁ U).ι.imageι ≫ π) ≫ sX := by
      rw [Category.assoc, Category.assoc, hcomm]
    exact @isHQuasiProjective_of_isImmersion _ _ n _ (inferInstanceAs
      (IsImmersion ((π ⁻¹ᵁ U).ι.imageι ≫ i))) _ _ heq

/-- **A proper morphism whose composite with a separated morphism is H-quasi-projective is
H-projective.** -/
private theorem isProjectiveMorphism_of_isHQuasiProjective_comp {Y X S : Scheme.{u}}
    (g : Y ⟶ X) (s : X ⟶ S) [IsSeparated s] [IsProper g] (h : IsHQuasiProjective (g ≫ s)) :
    IsProjectiveMorphism g := by
  obtain ⟨n, i, hi, -, hif⟩ := h
  haveI := hi
  rw [isProjectiveMorphism_iff_isHQuasiProjective_and_isProper]
  refine ⟨?_, inferInstance⟩
  let l : Y ⟶ Limits.pullback (projectiveSpaceOver n S ↘ S) s := Limits.pullback.lift i g hif
  have : IsImmersion (l ≫ Limits.pullback.fst _ _) := by rwa [Limits.pullback.lift_fst]
  have : IsImmersion l := IsImmersion.of_comp l (Limits.pullback.fst _ _)
  exact isHQuasiProjective_of_isImmersion (l ≫ (projectiveSpaceOverBaseChangeIso n s).hom) (by
    rw [Category.assoc, projectiveSpaceOverBaseChangeIso_hom_over, Limits.pullback.lift_snd])

/-- A morphism of irreducible schemes which is an isomorphism over a nonempty open subset of the
target is birational. -/
private theorem isBirationalMorphism_of_isIso_morphismRestrict {X Y : Scheme.{u}}
    [IrreducibleSpace X] [IrreducibleSpace Y] (f : X ⟶ Y) (U : Y.Opens)
    (hU : (U : Set Y).Nonempty) [IsIso (f ∣_ U)] : IsBirationalMorphism f := by
  obtain ⟨y, hy⟩ := hU
  have hV : ((f ⁻¹ᵁ U : X.Opens) : Set X).Nonempty := ⟨_, ((inv (f ∣_ U)) ⟨y, hy⟩).2⟩
  refine MMP.Flips.isBirationalMorphism_of_isIso_resLE f (f ⁻¹ᵁ U) U hV ⟨y, hy⟩ le_rfl ?_
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  infer_instance

/-- A composite of birational morphisms of irreducible schemes is birational. -/
private theorem isBirationalMorphism_comp {V X' X : Scheme.{u}} [IrreducibleSpace V]
    [IrreducibleSpace X'] [IrreducibleSpace X] {g : V ⟶ X'} {μ : X' ⟶ X}
    (hg : MMP.Mori.IsBirationalMorphism g) (hμ : MMP.Mori.IsBirationalMorphism μ) :
    MMP.Mori.IsBirationalMorphism (g ≫ μ) := by
  have : Nonempty V := (IrreducibleSpace.isIrreducible_univ V).nonempty.to_subtype.map Subtype.val
  have : Nonempty X' :=
    (IrreducibleSpace.isIrreducible_univ X').nonempty.to_subtype.map Subtype.val
  obtain ⟨Wg, hWgne, hWg⟩ := MMP.Mori.IsBirationalMorphism.exists_isOpenImmersion hg
  obtain ⟨Wμ, hWμne, hWμ⟩ := MMP.Mori.IsBirationalMorphism.exists_isOpenImmersion hμ
  obtain ⟨x₀, hx₀⟩ := hWgne
  obtain ⟨y, ⟨w, rfl⟩, hy⟩ := nonempty_preirreducible_inter
    (Wg.ι ≫ g).isOpenEmbedding.isOpen_range Wμ.isOpen ⟨_, (⟨x₀, hx₀⟩ : Wg.toScheme), rfl⟩ hWμne
  let U : V.Opens := Wg ⊓ g ⁻¹ᵁ Wμ
  have hwU : w.1 ∈ U := ⟨w.2, hy⟩
  have h1 : IsOpenImmersion (U.ι ≫ g) := by
    rw [← Scheme.homOfLE_ι V (inf_le_left : U ≤ Wg), Category.assoc]
    infer_instance
  have hrange : Set.range (U.ι ≫ g) ⊆ Set.range Wμ.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact z.2.2
  have hfac := IsOpenImmersion.lift_fac Wμ.ι (U.ι ≫ g) hrange
  have : IsOpenImmersion (IsOpenImmersion.lift Wμ.ι (U.ι ≫ g) hrange ≫ Wμ.ι) := by
    rwa [hfac]
  have : IsOpenImmersion (IsOpenImmersion.lift Wμ.ι (U.ι ≫ g) hrange) :=
    IsOpenImmersion.of_comp _ Wμ.ι
  have hU : IsOpenImmersion (U.ι ≫ g ≫ μ) := by
    rw [← Category.assoc, ← hfac, Category.assoc]
    infer_instance
  let V' : X.Opens := (U.ι ≫ g ≫ μ).opensRange
  have hle : U ≤ (g ≫ μ) ⁻¹ᵁ V' := fun x hx => ⟨⟨x, hx⟩, rfl⟩
  refine MMP.Flips.isBirationalMorphism_of_isIso_resLE (g ≫ μ) U V' ⟨_, hwU⟩
    ⟨_, ⟨⟨w.1, hwU⟩, rfl⟩⟩ hle ?_
  have e : (g ≫ μ).resLE V' U hle = (U.ι ≫ g ≫ μ).isoOpensRange.hom := by
    rw [← cancel_mono V'.ι, Scheme.Hom.resLE_comp_ι, Scheme.Hom.isoOpensRange_hom_ι]
  rw [e]
  infer_instance

/-! ### Components of snc divisors -/

/-- The support of a prime divisor, as an irreducible closed subset. -/
private noncomputable def primeIrr {X : Scheme.{u}} (E : AlgebraicGeometry.PrimeDivisor X) :
    IrreducibleCloseds X :=
  IrreducibleCloseds.closureSingleton E.genericPoint

/-- The underlying set of `primeIrr E` is the support of `E`. -/
private theorem coe_primeIrr {X : Scheme.{u}} (E : AlgebraicGeometry.PrimeDivisor X) :
    (primeIrr E : Set X) = E.support := by
  rw [E.support_eq_closure]; rfl

/-- An irreducible closed subset of codimension one contained in the union of the supports of
finitely many prime divisors is the support of one of them. -/
private theorem exists_mem_support_eq {X : Scheme.{u}}
    {s : Finset (AlgebraicGeometry.PrimeDivisor X)} (W : IrreducibleCloseds X)
    (hW : (W : Set X) ⊆ ⋃ E ∈ s, E.support) (hW1 : codimension W = 1) :
    ∃ E ∈ s, (E.support : Set X) = W := by
  classical
  obtain ⟨z, hz, hWz⟩ := (isIrreducible_iff_sUnion_isClosed.mp W.isIrreducible)
    (s.image AlgebraicGeometry.PrimeDivisor.support)
    (by
      intro z hz
      obtain ⟨E, -, rfl⟩ := Finset.mem_image.mp hz
      rw [← coe_primeIrr]; exact (primeIrr E).isClosed)
    (by
      intro x hx
      obtain ⟨E, hE, hxE⟩ := Set.mem_iUnion₂.mp (hW hx)
      exact ⟨E.support, Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hE), hxE⟩)
  obtain ⟨E, hE, rfl⟩ := Finset.mem_image.mp hz
  have hWE : W ≤ primeIrr E := fun x hx ↦ by
    change x ∈ (primeIrr E : Set X); rw [coe_primeIrr]; exact hWz hx
  have hWE' : W = primeIrr E := by
    by_contra hne
    have hlt : W < primeIrr E := lt_of_le_of_ne hWE hne
    have := Order.coheight_add_one_le hlt
    rw [← codimension_eq_coheight, ← codimension_eq_coheight,
      show codimension (primeIrr E) = 1 from E.codimension_one, hW1] at this
    exact absurd this (by decide)
  exact ⟨E, hE, by rw [← coe_primeIrr, ← hWE']⟩

/-- The preimage in a subspace `C` of a preirreducible subset of `C` is preirreducible. -/
private theorem isPreirreducible_preimage_val {Y : Type*} [TopologicalSpace Y] {C W : Set Y}
    (hW : IsPreirreducible W) (hWC : W ⊆ C) : IsPreirreducible (Subtype.val ⁻¹' W : Set C) := by
  rintro u v hu hv ⟨a, ha, hau⟩ ⟨b, hb, hbv⟩
  obtain ⟨u', hu', rfl⟩ := isOpen_induced_iff.mp hu
  obtain ⟨v', hv', rfl⟩ := isOpen_induced_iff.mp hv
  obtain ⟨y, hyW, hyu, hyv⟩ := hW u' v' hu' hv' ⟨a, ha, hau⟩ ⟨b, hb, hbv⟩
  exact ⟨⟨y, hWC hyW⟩, hyW, hyu, hyv⟩

/-- An irreducible closed set contained in a closed set lies in an irreducible closed subset
maximal in it. -/
private theorem exists_maximal_irreducibleCloseds_subset_ge {Y : Type*} [TopologicalSpace Y]
    {C : Set Y} (hC : IsClosed C)
    (Z : IrreducibleCloseds Y) (hZ : (Z : Set Y) ⊆ C) :
    ∃ W : IrreducibleCloseds Y, Maximal (fun W' : IrreducibleCloseds Y ↦ (W' : Set Y) ⊆ C) W ∧
      Z ≤ W := by
  obtain ⟨t, ht, hxt, hmax⟩ := exists_preirreducible (Subtype.val ⁻¹' (Z : Set Y) : Set C)
    (isPreirreducible_preimage_val Z.isIrreducible.isPreirreducible hZ)
  obtain ⟨z, hz⟩ := Z.isIrreducible.nonempty
  let W : IrreducibleCloseds Y := ⟨closure (Subtype.val '' t),
    (IsIrreducible.closure ⟨⟨z, ⟨z, hZ hz⟩, hxt hz, rfl⟩,
      ht.image _ continuous_subtype_val.continuousOn⟩), isClosed_closure⟩
  have hWC : (W : Set Y) ⊆ C := closure_minimal (by rintro _ ⟨y, -, rfl⟩; exact y.2) hC
  refine ⟨W, ⟨hWC, fun W' hW'C hWW' y hy ↦ ?_⟩, fun y hy ↦ subset_closure ⟨⟨y, hZ hy⟩, hxt hy, rfl⟩⟩
  have := hmax _ (isPreirreducible_preimage_val W'.isIrreducible.isPreirreducible hW'C)
    fun y hy ↦ hWW' (subset_closure ⟨y, hy, rfl⟩)
  have : (⟨y, hW'C hy⟩ : C) ∈ t := by rwa [← this]
  exact subset_closure ⟨_, this, rfl⟩

/-- The coefficient of `P` in the reduced divisor with components `s` is `1` if `P ∈ s` and `0`
otherwise. -/
private theorem coeff_sum_single {X : Scheme.{u}} (s : Finset (Mori.PrimeDivisor X))
    (P : Mori.PrimeDivisor X) [Decidable (P ∈ s)] :
    (∑ E ∈ s, Finsupp.single E (1 : ℤ) : Divisor X).coeff P = if P ∈ s then 1 else 0 := by
  classical
  simp [DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply, Finsupp.single_apply]

/-- The reduced divisor with components `s` has coefficients `0` and `1`. -/
private theorem coeff_sum_single_eq_zero_or_eq_one {X : Scheme.{u}}
    (s : Finset (Mori.PrimeDivisor X)) (P : Mori.PrimeDivisor X) :
    (∑ E ∈ s, Finsupp.single E (1 : ℤ) : Divisor X).coeff P = 0 ∨
      (∑ E ∈ s, Finsupp.single E (1 : ℤ) : Divisor X).coeff P = 1 := by
  classical
  rw [coeff_sum_single]
  split_ifs <;> simp

/-- A prime divisor whose support lies in the union of the supports of the prime divisors of a
finite set `s` belongs to `s`. -/
private theorem mem_of_support_subset {X : Scheme.{u}} {s : Finset (Mori.PrimeDivisor X)}
    {P : Mori.PrimeDivisor X} (h : (P.support : Set X) ⊆ ⋃ E ∈ s, E.support) : P ∈ s := by
  obtain ⟨E, hE, hEP⟩ := exists_mem_support_eq (s := s) (primeIrr P)
    (by rw [coe_primeIrr]; exact h) P.codimension_one
  rw [coe_primeIrr] at hEP
  rwa [← primeDivisor_eq_of_support_eq hEP]

/-- Let `C` be a closed subset of pure codimension one, contained in the union of the supports
of a finite set `s` of prime divisors. The reduced divisor whose components are the members of
`s` with support in `C` has support `C`. -/
private theorem isReducedDivisorWithSupport_sum_filter {X : Scheme.{u}}
    {s : Finset (Mori.PrimeDivisor X)} {C : Set X}
    [DecidablePred fun E : Mori.PrimeDivisor X => (E.support : Set X) ⊆ C]
    (hC : IsClosed C) (hpure : IsPureCodimOne C) (hCs : C ⊆ ⋃ E ∈ s, E.support) :
    IsReducedDivisorWithSupport
      (∑ E ∈ s.filter (fun E => (E.support : Set X) ⊆ C), Finsupp.single E (1 : ℤ)) C := by
  refine ⟨coeff_sum_single_eq_zero_or_eq_one _, ?_⟩
  rw [DivisorWithCoeffs.coe_supp, ← reducedDivisorOf, support_reducedDivisorOf]
  ext y
  refine ⟨fun hy => ?_, fun hy => ?_⟩
  · obtain ⟨E, hE, hyE⟩ := Set.mem_iUnion₂.mp hy
    exact (Finset.mem_filter.mp hE).2 hyE
  · obtain ⟨W, hWmax, hyW⟩ := exists_maximal_irreducibleCloseds_subset_ge hC
      (IrreducibleCloseds.closureSingleton y)
      (closure_minimal (Set.singleton_subset_iff.mpr hy) hC)
    have hWmax' : Maximal (fun W : Set X => IsIrreducible W ∧ W ⊆ C) (W : Set X) := by
      refine ⟨⟨W.isIrreducible, hWmax.1⟩, fun W' hW' hle => ?_⟩
      let W'' : IrreducibleCloseds X := ⟨closure W', hW'.1.closure, isClosed_closure⟩
      have h1 : (W'' : Set X) ⊆ C := closure_minimal hW'.2 hC
      have h2 : W ≤ W'' := fun z hz => subset_closure (hle hz)
      exact subset_closure.trans (hWmax.2 h1 h2)
    obtain ⟨P, hP⟩ := hpure _ hWmax'
    have hPC : (P.support : Set X) ⊆ C := by rw [hP]; exact hWmax.1
    have hPs : P ∈ s := mem_of_support_subset (hPC.trans hCs)
    refine Set.mem_iUnion₂.mpr ⟨P, Finset.mem_filter.mpr ⟨hPs, hPC⟩, ?_⟩
    rw [hP]
    exact hyW (subset_closure rfl)

/-! ### Cartier divisors and their Weil divisors -/

/-- On an integral locally Noetherian scheme, a point of coheight zero lies in the support of no
Cartier divisor. -/
private theorem notMem_cartierSupport_of_coheight_eq_zero {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] (A : X.CartierDivisor) {x : X} (hx : Order.coheight x = 0) :
    x ∉ cartierSupport A := by
  have : IsArtinianRing (X.presheaf.stalk x) :=
    isArtinianRing_iff_krullDimLE_zero.mpr (krullDimLE_of_coheight_le (by simp [hx]))
  exact notMem_cartierSupport_of_isArtinianRing A x

/-- Every Cartier divisor on a Noetherian integral scheme has a Weil divisor. -/
private theorem exists_isWeilDivisorOfCartier {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [TopologicalSpace.NoetherianSpace X] (A : X.CartierDivisor) :
    ∃ w : Divisor X, IsWeilDivisorOfCartier A w := by
  have hfin := MMP.Mori.finite_setOf_genericPoint_mem (isClosed_cartierSupport A)
    (fun s hs h0 => notMem_cartierSupport_of_coheight_eq_zero A h0 hs)
  refine ⟨Finsupp.ofSupportFinite (fun P => primeDivisorOrder P A) (hfin.subset fun P hP => ?_),
    fun P => ?_⟩
  · by_contra h
    have hg : (primeDivisorSubvariety P).genericPoint = P.genericPoint := rfl
    refine hP ((isOrderAlong_primeDivisorOrder A P).eq_zero_of_not_subset fun h' => h ?_)
    change P.genericPoint ∈ cartierSupport A
    rw [← hg]
    exact genericPoint_mem_cartierSupport_iff.mpr h'
  · rw [MMP.Mori.DivisorWithCoeffs.coeff_apply, Finsupp.ofSupportFinite_coe]
    exact isOrderAlong_primeDivisorOrder A P

/-- The generic point of an integral scheme lies in the support of no Cartier divisor. -/
private theorem genericPoint_notMem_cartierSupport {X : Scheme.{u}} [IsIntegral X]
    (A : X.CartierDivisor) : genericPoint X ∉ cartierSupport A := by
  haveI : IsArtinianRing (X.presheaf.stalk (genericPoint X)) :=
    (inferInstance : IsArtinianRing X.functionField)
  exact notMem_cartierSupport_of_isArtinianRing A (genericPoint X)

/-- The generic point of an irreducible scheme lies in every nonempty open subset. -/
private theorem genericPoint_mem_of_opens_nonempty {X : Scheme.{u}} [IrreducibleSpace X]
    (U : X.Opens) (hU : (U : Set X).Nonempty) : genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).2 (by rwa [Set.univ_inter])

/-- A dominant morphism of integral locally Noetherian schemes satisfies the pull-back condition
for every Cartier divisor. -/
private theorem pullbackCondition_of_isDominant {X X' : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsIntegral X'] [IsLocallyNoetherian X'] (μ : X' ⟶ X) [IsDominant μ]
    (A : X.CartierDivisor) : PullbackCondition μ A := by
  intro η hη hμη
  rw [AlgebraicGeometry.schemeAssociatedPoints_eq_singleton_genericPoint] at hη
  rw [Set.mem_singleton_iff.mp hη] at hμη
  have hsub : (Set.univ : Set X') ⊆ μ ⁻¹' cartierSupport A := by
    rw [← genericPoint_spec X']
    exact closure_minimal (Set.singleton_subset_iff.mpr hμη)
      ((isClosed_cartierSupport A).preimage μ.continuous)
  have hdense : closure (Set.range μ) ⊆ cartierSupport A :=
    closure_minimal (by rintro _ ⟨y, rfl⟩; exact hsub (Set.mem_univ y))
      (isClosed_cartierSupport A)
  rw [μ.denseRange.closure_range] at hdense
  exact genericPoint_notMem_cartierSupport A (hdense (Set.mem_univ _))

/-- The support of a pull-back of `D` lies over the support of `D`. -/
private theorem cartierSupport_subset_preimage_of_isPullback {X Y : Scheme.{u}} {f : Y ⟶ X}
    {D : X.CartierDivisor} {D' : Y.CartierDivisor} (h : IsPullback f D D') :
    cartierSupport D' ⊆ f ⁻¹' cartierSupport D := by
  intro y hy
  by_contra hfy
  have h1 : IsFraction (1 : Y.totalQuotientSheaf.presheaf.stalk y) (f.stalkMap y 1)
      (f.stalkMap y 1) := by
    rw [map_one]; exact isFraction_one_one_one y
  exact notMem_cartierSupport_of_isLocalEquationAt_one
    (h.isLocalEquationAt (isLocalEquationAt_one_of_notMem_cartierSupport hfy)
      (isFraction_one_one_one _) h1) hy

/-! ### Snc divisors -/

/-- An injection `Fin m → Fin n` is the restriction of a permutation of `Fin n` along
`Fin.castLE`. -/
private theorem exists_perm_castLE_eq {m n : ℕ} (g : Fin m → Fin n) (hg : Function.Injective g) :
    ∃ (hk : m ≤ n) (π : Equiv.Perm (Fin n)), ∀ i, π (Fin.castLE hk i) = g i := by
  have hk : m ≤ n := by simpa using Fintype.card_le_of_injective g hg
  let e : {j : Fin n // j ∈ Set.range (Fin.castLE hk)} ≃ {j : Fin n // j ∈ Set.range g} :=
    (Equiv.ofInjective _ (Fin.castLE_injective hk)).symm.trans (Equiv.ofInjective g hg)
  refine ⟨hk, e.extendSubtype, fun i => ?_⟩
  rw [Equiv.extendSubtype_apply_of_mem e _ ⟨i, rfl⟩]
  simp [e]

/-- **Sub-divisors of snc divisors.** If the reduced divisor with components a finite set `s`
is snc in the sense of `MMP.Mori.DivisorWithCoeffs.IsSNC`, the reduced divisor with components
any `J ⊆ s` is an SNC divisor in the sense of Lazarsfeld. -/
private theorem isSNCDivisor_reducedDivisorOf_of_isSNC {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] {f : X ⟶ Y} {s J : Finset (Mori.PrimeDivisor X)}
    (hs : (∑ E ∈ s, Finsupp.single E (1 : ℤ) : Divisor X).IsSNC f) (hJ : J ⊆ s) :
    IsSNCDivisor f (reducedDivisorOf J) := by
  classical
  have h : (reducedDivisorOf J).support ⊆
      (∑ E ∈ s, Finsupp.single E (1 : ℤ) : Divisor X).support := by
    rwa [support_reducedDivisorOf, ← reducedDivisorOf, support_reducedDivisorOf]
  set D' := reducedDivisorOf J
  refine ⟨isReducedEffective_reducedDivisorOf J, fun E hE => hs.1 E (h hE), fun x hx => ?_⟩
  obtain ⟨n, w, σ, hw, hσ, hloc⟩ := hs.2 x
  have := MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hw
  have := IsRegularLocalRing.isDomain (X.presheaf.stalk x)
  set T := D'.support.filter fun E => x ∈ E.support with hT
  have hTD : ∀ E ∈ T, E ∈ (∑ E ∈ s, Finsupp.single E (1 : ℤ) : Divisor X).support ∧
      x ∈ E.support := fun E hE =>
    ⟨h (Finset.mem_filter.mp hE).1, (Finset.mem_filter.mp hE).2⟩
  let σ' : T → Fin n := fun E => σ ⟨E.1, hTD E.1 E.2⟩
  have hσ' : Function.Injective σ' := fun E E' hEE' => by
    have h' := congrArg Subtype.val (hσ hEE')
    exact Subtype.ext h'
  obtain ⟨hk, π, hπ⟩ := exists_perm_castLE_eq (σ' ∘ T.equivFin.symm)
    (hσ'.comp T.equivFin.symm.injective)
  refine ⟨n, w ∘ π, T.card, hk, ⟨?_, hw.2⟩, ?_⟩
  · rw [Set.range_comp, Equiv.range_eq_univ, Set.image_univ]
    exact hw.1
  · rw [stalk_suppIdeal, ← hT]
    let p : MMP.Mori.PrimeDivisor X → X.presheaf.stalk x := fun E =>
      if hE : E ∈ T then w (σ' ⟨E, hE⟩) else 1
    have hpT : ∀ E (hE : E ∈ T), p E = w (σ' ⟨E, hE⟩) := fun E hE => by simp [p, hE]
    have hspan : ∀ E ∈ T, IdealSheafData.stalk E.idealSheaf x = Ideal.span {p E} :=
      fun E hE => by rw [hpT E hE]; exact hloc ⟨E, hTD E hE⟩
    rw [Finset.inf_congr rfl hspan, finsetInf_span_singleton_eq_span_prod]
    · refine congrArg (fun r => Ideal.span {r}) ?_
      rw [← Finset.prod_coe_sort T]
      refine (Fintype.prod_equiv T.equivFin.symm (fun i => (w ∘ π) (Fin.castLE hk i))
        (fun E : T => p E) fun i => ?_).symm
      rw [Function.comp_apply, hπ i, hpT _ (T.equivFin.symm i).2]
      rfl
    · intro E hE
      rw [hpT E hE]
      exact prime_of_isRegularSystemOfParameters hw _
    · intro E hE E' hE' hass
      refine eq_of_stalk_idealSheaf_eq (hTD E hE).2 (hTD E' hE').2 ?_
      rw [hspan E hE, hspan E' hE']
      exact Ideal.span_singleton_eq_span_singleton.mpr hass

/-! ### Purity of the exceptional locus -/

/-- The exceptional locus is closed. -/
private theorem isClosed_exceptionalLocus {X' X : Scheme.{u}} (μ : X' ⟶ X) :
    IsClosed (exceptionalLocus μ) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  simp only [Set.mem_compl_iff, exceptionalLocus, Set.mem_setOf_eq, not_not] at hx
  obtain ⟨U, hxU, hU⟩ := hx
  refine ⟨U, fun x' hx' ↦ ?_, U.isOpen, hxU⟩
  simp only [Set.mem_compl_iff, exceptionalLocus, Set.mem_setOf_eq, not_not]
  exact ⟨U, hx', hU⟩

/-- In a factorial domain, a prime ideal containing two relatively prime elements, one of them
nonzero, has height at least two. -/
private theorem two_le_height_of_isRelPrime {B : Type*} [CommRing B] [IsDomain B]
    [UniqueFactorizationMonoid B] {q : Ideal B} [q.IsPrime] {a b : B} (hab : IsRelPrime a b)
    (ha : a ∈ q) (hb : b ∈ q) (hb0 : b ≠ 0) : 2 ≤ q.height := by
  have hq : q ≠ ⊥ := fun h => hb0 (by simpa [h] using hb)
  obtain ⟨π, hπq, hπ⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot ‹_› hq
  have hP : (Ideal.span {π}).IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).mpr hπ
  have h1 : (⊥ : Ideal B) < Ideal.span {π} := by
    rw [bot_lt_iff_ne_bot, Ne, Ideal.span_singleton_eq_bot]
    exact hπ.ne_zero
  have h2 : Ideal.span {π} < q := by
    refine lt_of_le_of_ne ((Ideal.span_singleton_le_iff_mem _).mpr hπq) fun h => ?_
    have hpa : π ∣ a := Ideal.mem_span_singleton.mp (h ▸ ha)
    have hpb : π ∣ b := Ideal.mem_span_singleton.mp (h ▸ hb)
    exact hπ.not_unit (hab hpa hpb)
  have e1 := Ideal.height_add_one_le_of_lt_of_isPrime h1
  rw [Ideal.height_bot, zero_add] at e1
  calc (2 : ℕ∞) = 1 + 1 := by norm_num
    _ ≤ (Ideal.span {π}).height + 1 := by gcongr
    _ ≤ q.height := Ideal.height_add_one_le_of_lt_of_isPrime h2

/-- Let `φ : B →+* A` be an injective local homomorphism from a factorial domain to a noetherian
domain, and `f ∈ A` a fraction `φ a / φ b` of elements of `B` which is not in the image of `φ`.
Then some prime of `A` of height at most one contracts to a prime of height at least two. -/
private theorem exists_height_le_one_and_two_le_height_comap {B A : Type*} [CommRing B]
    [CommRing A] [IsDomain B] [UniqueFactorizationMonoid B] [IsDomain A] [IsNoetherianRing A]
    (φ : B →+* A) [IsLocalHom φ] (hφ : Function.Injective φ) {f : A} {a b : B} (hb : b ≠ 0)
    (hf : φ a = f * φ b) (hfr : f ∉ φ.range) :
    ∃ p : Ideal A, p.IsPrime ∧ p.height ≤ 1 ∧ 2 ≤ (p.comap φ).height := by
  obtain ⟨a', b', c, hab, rfl, rfl⟩ := UniqueFactorizationMonoid.exists_reduced_factors' a b hb
  have hc : φ c ≠ 0 := fun h => hb (by rw [(map_eq_zero_iff φ hφ).mp h, zero_mul])
  have hf' : φ a' = f * φ b' := by
    apply mul_left_cancel₀ hc
    rw [← map_mul, hf, map_mul]
    ring
  have hb' : b' ≠ 0 := right_ne_zero_of_mul hb
  have hnu : ¬ IsUnit (φ b') := by
    intro hu
    have hu' : IsUnit b' := (isUnit_map_iff φ b').mp hu
    apply hfr
    refine ⟨a' * ↑hu'.unit⁻¹, ?_⟩
    rw [map_mul, hf', mul_assoc, ← map_mul, IsUnit.mul_val_inv, map_one, mul_one]
  obtain ⟨m, hm, hlm⟩ :=
    Ideal.exists_le_maximal _ (by rwa [Ne, Ideal.span_singleton_eq_top] : Ideal.span {φ b'} ≠ ⊤)
  obtain ⟨p, hp, -⟩ := Ideal.exists_minimalPrimes_le hlm
  have hpp : p.IsPrime := hp.1.1
  have hbp : φ b' ∈ p := hp.1.2 (Ideal.subset_span rfl)
  refine ⟨p, hpp, Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ p hp, ?_⟩
  exact two_le_height_of_isRelPrime hab (by simpa [hf'] using p.mul_mem_left f hbp) hbp hb'

/-- The coheight of a generization `y ⤳ x` is the height of its prime in `𝒪_{X,x}`. -/
private theorem coheight_eq_height_primeOfSpecializes {X : Scheme.{u}} {y x : X} (h : y ⤳ x) :
    (Order.coheight y : WithBot ℕ∞) = (MMP.Intersection.primeOfSpecializes h).height := by
  let := (X.presheaf.stalkSpecializes h).hom.toAlgebra
  have := MMP.Intersection.isLocalization_stalkSpecializes h
  have e := IsLocalization.AtPrime.ringKrullDim_eq_height
    (MMP.Intersection.primeOfSpecializes h) (X.presheaf.stalk y)
  rwa [ringKrullDim_stalk_eq_coheight] at e

/-- Every prime of `𝒪_{X,x}` is the prime of a generization of `x`. -/
private theorem exists_primeOfSpecializes_eq {X : Scheme.{u}} (x : X)
    (p : Ideal (X.presheaf.stalk x)) [p.IsPrime] :
    ∃ (y : X) (h : y ⤳ x), MMP.Intersection.primeOfSpecializes h = p := by
  have hy : X.fromSpecStalk x ⟨p, ‹_›⟩ ∈ {y | y ⤳ x} := by
    rw [← Scheme.range_fromSpecStalk]
    exact ⟨_, rfl⟩
  exact ⟨_, hy, congrArg PrimeSpectrum.asIdeal ((X.fromSpecStalk x).injective
    ((MMP.Intersection.fromSpecStalk_primeOfSpecializes hy).trans rfl))⟩

/-- At a point off the exceptional locus the morphism induces an isomorphism of local rings. -/
private theorem isIso_stalkMap_of_notMem_exceptionalLocus {X Y : Scheme.{u}} {g : Y ⟶ X} {y : Y}
    (hy : y ∉ exceptionalLocus g) : IsIso (g.stalkMap y) := by
  simp only [exceptionalLocus, Set.mem_setOf_eq, not_not] at hy
  obtain ⟨U, hyU, hU⟩ := hy
  obtain ⟨y₀, rfl⟩ : y ∈ Set.range U.ι := by rwa [Scheme.Opens.range_ι]
  have h1 : IsIso ((U.ι ≫ g).stalkMap y₀) :=
    @IsOpenImmersion.instIsIsoCommRingCatStalkMap _ _ _ hU y₀
  have h2 : IsIso (U.ι.stalkMap y₀) :=
    IsOpenImmersion.instIsIsoCommRingCatStalkMap U.ι y₀
  rw [Scheme.Hom.stalkMap_comp] at h1
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ h2 h1

/-- A point off the exceptional locus of a morphism from a smooth scheme lies over the smooth
locus: near it the morphism is an open immersion. -/
private theorem mem_smoothLocus_of_notMem_exceptionalLocus {k : Type u} [Field k]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) {g : Y ⟶ X}
    [LocallyOfFinitePresentation (g ≫ sX)] (hY : IsSmoothScheme (g ≫ sX)) {y : Y}
    (hy : y ∉ exceptionalLocus g) : g y ∈ smoothLocus sX := by
  simp only [exceptionalLocus, Set.mem_setOf_eq, not_not] at hy
  obtain ⟨U, hyU, hU⟩ := hy
  haveI : Smooth (g ≫ sX) := (isSmoothScheme_iff _).1 hY
  haveI : Smooth ((U.ι ≫ g) ≫ sX) := by rw [Category.assoc]; infer_instance
  refine le_smoothLocus sX (U := (U.ι ≫ g).opensRange) ?_ ⟨⟨y, hyU⟩, rfl⟩
  rw [← Scheme.Hom.isoOpensRange_inv_comp, Category.assoc]
  infer_instance

/-- If a morphism of integral schemes induces an isomorphism of local rings at the generic point
of the source, it induces injective maps of local rings at every point. -/
private theorem stalkMap_injective_of_isIso_genericPoint {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] (g : Y ⟶ X) (η : Y) [hψ : IsIso (g.stalkMap (genericPoint Y))] :
    Function.Injective (g.stalkMap η).hom := by
  have hηx : genericPoint Y ⤳ η := (genericPoint_spec Y).specializes trivial
  have hy := g.base.hom.map_specializes hηx
  have hcomm : ∀ b, g.stalkMap (genericPoint Y) (X.presheaf.stalkSpecializes hy b) =
      Y.presheaf.stalkSpecializes hηx (g.stalkMap η b) := fun b =>
    Scheme.Hom.stalkSpecializes_stalkMap_apply g _ η hηx b
  intro b₁ b₂ e
  apply MMP.Intersection.stalkSpecializes_injective hy
  apply ((ConcreteCategory.isIso_iff_bijective _).mp hψ).1
  change g.stalkMap _ (X.presheaf.stalkSpecializes hy b₁) =
    g.stalkMap _ (X.presheaf.stalkSpecializes hy b₂)
  rw [hcomm, hcomm]
  exact congrArg _ e

/-- The prime of the image `g y' ⤳ g η` of a generization `y' ⤳ η` is the contraction of the
prime of `y'` along the map of local rings at `η`. -/
private theorem primeOfSpecializes_map_eq_comap {X Y : Scheme.{u}} (g : Y ⟶ X) {y' η : Y}
    (hy' : y' ⤳ η) (h' : g.base y' ⤳ g.base η) :
    MMP.Intersection.primeOfSpecializes h' =
      (MMP.Intersection.primeOfSpecializes hy').comap (g.stalkMap η).hom := by
  let pt : Spec (Y.presheaf.stalk η) := ⟨MMP.Intersection.primeOfSpecializes hy', inferInstance⟩
  have e : X.fromSpecStalk (g.base η) ((Spec.map (g.stalkMap η)).base pt) =
      g.base (Y.fromSpecStalk η pt) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Scheme.SpecMap_stalkMap_fromSpecStalk]
  have e2 : (Spec.map (g.stalkMap η)).base pt =
      ⟨(MMP.Intersection.primeOfSpecializes hy').comap (g.stalkMap η).hom, inferInstance⟩ := rfl
  rw [e2, MMP.Intersection.fromSpecStalk_primeOfSpecializes hy',
    ← MMP.Intersection.fromSpecStalk_primeOfSpecializes h'] at e
  exact (congrArg PrimeSpectrum.asIdeal ((X.fromSpecStalk _).injective e)).symm

/-- If a morphism `g` of integral schemes induces isomorphisms of local rings at the generic point
and at every generization of `η` of coheight at most one, and `𝒪_{X, g η}` is factorial, then the
map of local rings at `η` is surjective. -/
private theorem stalkMap_surjective_of_forall_coheight_le_one {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] [IsLocallyNoetherian Y] (g : Y ⟶ X) (η : Y)
    [UniqueFactorizationMonoid (X.presheaf.stalk (g η))]
    [hψ : IsIso (g.stalkMap (genericPoint Y))]
    (h : ∀ y, y ⤳ η → Order.coheight y ≤ 1 → IsIso (g.stalkMap y)) :
    Function.Surjective (g.stalkMap η).hom := by
  have hηx : genericPoint Y ⤳ η := (genericPoint_spec Y).specializes trivial
  have hy := g.base.hom.map_specializes hηx
  have hcomm : ∀ b, g.stalkMap (genericPoint Y) (X.presheaf.stalkSpecializes hy b) =
      Y.presheaf.stalkSpecializes hηx (g.stalkMap η b) := fun b =>
    Scheme.Hom.stalkSpecializes_stalkMap_apply g _ η hηx b
  intro f
  by_contra hfr
  let := (X.presheaf.stalkSpecializes hy).hom.toAlgebra
  have := MMP.Intersection.isLocalization_stalkSpecializes hy
  obtain ⟨z, hz⟩ := ((ConcreteCategory.isIso_iff_bijective _).mp hψ).2
    (Y.presheaf.stalkSpecializes hηx f)
  obtain ⟨⟨a, s, hs⟩, e⟩ := IsLocalization.surj
    ((IsLocalRing.maximalIdeal (X.presheaf.stalk (g.base (genericPoint Y)))).comap
      (X.presheaf.stalkSpecializes hy).hom).primeCompl z
  have hs0 : s ≠ 0 := by rintro rfl; exact hs (zero_mem _)
  have key : (g.stalkMap η).hom a = f * (g.stalkMap η).hom s := by
    apply MMP.Intersection.stalkSpecializes_injective hηx
    have e' := congrArg (g.stalkMap (genericPoint Y)).hom e
    simp only [map_mul] at e'
    change _ * g.stalkMap _ (X.presheaf.stalkSpecializes hy s) =
      g.stalkMap _ (X.presheaf.stalkSpecializes hy a) at e'
    rw [hcomm, hcomm] at e'
    change (g.stalkMap _).hom z * _ = _ at e'
    rw [map_mul, ← e']
    exact congrArg (· * _) hz
  obtain ⟨p, hp, hp1, hp2⟩ := exists_height_le_one_and_two_le_height_comap
    (g.stalkMap η).hom (stalkMap_injective_of_isIso_genericPoint g η) hs0 key
    (fun ⟨a, ha⟩ => hfr ⟨a, ha⟩)
  obtain ⟨y', hy', rfl⟩ := exists_primeOfSpecializes_eq η p
  have h' : g.base y' ⤳ g.base η := hy'.map g.base.hom.continuous
  have hc := coheight_eq_height_primeOfSpecializes hy'
  have hc' := coheight_eq_height_primeOfSpecializes h'
  rw [primeOfSpecializes_map_eq_comap g hy' h'] at hc'
  have hco : Order.coheight y' ≤ 1 := by rwa [WithBot.coe_injective hc]
  haveI : IsIso (g.stalkMap y') := h y' hy' hco
  have e := ringKrullDim_eq_of_ringEquiv (asIso (g.stalkMap y')).commRingCatIsoToRingEquiv
  rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight, hc, hc'] at e
  have e' : (MMP.Intersection.primeOfSpecializes hy').height =
      ((MMP.Intersection.primeOfSpecializes hy').comap (g.stalkMap η).hom).height :=
    mod_cast e.symm
  rw [← e'] at hp2
  exact absurd (hp2.trans hp1) (by decide)

/-- **van der Waerden's purity argument.** Let `g : Y ⟶ X` be a morphism of integral schemes,
`Y` locally Noetherian, and `η ∈ Y` a point over which the local ring of `X` is factorial. If `g`
induces isomorphisms of local rings at every generization of `η` of coheight at most one, it
induces an isomorphism of local rings at `η`. -/
private theorem isIso_stalkMap_of_forall_coheight_le_one {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] [IsLocallyNoetherian Y] (g : Y ⟶ X) (η : Y)
    [UniqueFactorizationMonoid (X.presheaf.stalk (g η))]
    (h : ∀ y, y ⤳ η → Order.coheight y ≤ 1 → IsIso (g.stalkMap y)) :
    IsIso (g.stalkMap η) := by
  have hηx : genericPoint Y ⤳ η := (genericPoint_spec Y).specializes trivial
  haveI : IsIso (g.stalkMap (genericPoint Y)) := h _ hηx
    ((Order.coheight_eq_zero.mpr fun b _ => Scheme.le_iff_specializes.mpr
      ((genericPoint_spec Y).specializes trivial)).trans_le zero_le_one)
  exact (ConcreteCategory.isIso_iff_bijective _).mpr ⟨stalkMap_injective_of_isIso_genericPoint g η,
    stalkMap_surjective_of_forall_coheight_le_one g η h⟩

/-- On an integral scheme, a point of coheight zero is the generic point. -/
private theorem eq_genericPoint_of_coheight_eq_zero {Y : Scheme.{u}} [IsIntegral Y] {η : Y}
    (h0 : Order.coheight η = 0) : η = genericPoint Y := by
  have h1 : η ≤ genericPoint Y :=
    Scheme.le_iff_specializes.mpr ((genericPoint_spec Y).specializes trivial)
  exact ((Scheme.le_iff_specializes.mp (Order.coheight_eq_zero.mp h0 h1)).antisymm
    ((genericPoint_spec Y).specializes trivial)).eq

/-- The local ring of a `k`-scheme at a smooth point is factorial. -/
private theorem uniqueFactorizationMonoid_stalk_of_mem_smoothLocus {k : Type u} [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) {x : X} (hx : x ∈ smoothLocus sX) :
    UniqueFactorizationMonoid (X.presheaf.stalk x) := by
  obtain ⟨V, hxV, hV⟩ := mem_smoothLocus_iff.1 hx
  haveI : Smooth (V.ι ≫ sX) := hV
  haveI := isRegularLocalRing_stalk_of_smooth_over_field (V.ι ≫ sX) ⟨x, hxV⟩
  haveI := IsRegularLocalRing.uniqueFactorizationMonoid (V.toScheme.presheaf.stalk ⟨_, hxV⟩)
  exact MulEquiv.uniqueFactorizationMonoid
    (V.stalkIso ⟨_, hxV⟩).commRingCatIsoToRingEquiv.toMulEquiv inferInstance

/-- **Purity over the smooth locus** (van der Waerden). For a birational morphism `g : Y ⟶ X` of
integral schemes, a maximal point `η` of the exceptional locus lying over a smooth point of `X`
has coheight one. -/
private theorem coheight_eq_one_of_mem_smoothLocus {k : Type u} [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    [NoetherianSpace X] (g : Y ⟶ X) [LocallyOfFiniteType g] (hg : IsBirationalMorphism g)
    {η : Y} (hηE : η ∈ exceptionalLocus g) (hmax : ∀ y ∈ exceptionalLocus g, y ⤳ η → y = η)
    (hηs : g η ∈ smoothLocus sX) : Order.coheight η = 1 := by
  have hne0 : Order.coheight η ≠ 0 := fun h0 => by
    haveI : Nonempty Y := ⟨η⟩
    obtain ⟨W, hWne, hW⟩ := hg.exists_isOpenImmersion
    exact mem_exceptionalLocus_iff.mp (eq_genericPoint_of_coheight_eq_zero h0 ▸ hηE) W
      (genericPoint_mem_of_opens_nonempty W hWne) hW
  refine le_antisymm ?_ (ENat.one_le_iff_ne_zero.mpr hne0)
  by_contra h2
  have h2' : 2 ≤ Order.coheight η := Order.add_one_le_of_lt (not_le.mp h2)
  haveI := uniqueFactorizationMonoid_stalk_of_mem_smoothLocus sX hηs
  haveI : IsIso (g.stalkMap η) := isIso_stalkMap_of_forall_coheight_le_one g η
    fun y hy hy1 => isIso_stalkMap_of_notMem_exceptionalLocus fun hE => by
      rw [hmax y hE hy] at hy1
      exact absurd (h2'.trans hy1) (by decide)
  obtain ⟨U, hηU, hU⟩ := exists_isOpenImmersion_res_of_isIso_stalkMap g η
    NoetherianSpace.finite_irreducibleComponents inferInstance
  exact mem_exceptionalLocus_iff.mp hηE U hηU hU

/-- **Purity of the exceptional locus.** Let `g : Y ⟶ X` be a birational morphism of varieties
over a field of characteristic zero, with `Y` smooth, and suppose that `g⁻¹(Sing X)` is the
support of an effective Cartier divisor. Then `Exc(g)` is empty or of pure codimension one. -/
private theorem isPureCodimOne_exceptionalLocus {k : Type u} [Field k] [CharZero k]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (hX : Mori.IsVariety k sX) (g : Y ⟶ X)
    (hY : Mori.IsVariety k (g ≫ sX)) (hYsm : IsSmoothScheme (g ≫ sX))
    (hg : IsBirationalMorphism g) {C : Y.IdealSheafData}
    (hC : Stacks.Divisors.IsEffectiveCartierDivisor C)
    (hCsupp : (C.support : Set Y) = g ⁻¹' (singularLocus sX : Set X)) :
    IsPureCodimOne (exceptionalLocus g) := by
  intro Z hZ
  have hcl := isClosed_exceptionalLocus g
  haveI : IsIntegral Y := hY.toIsIntegral
  haveI : IsIntegral X := hX.toIsIntegral
  haveI : LocallyOfFiniteType (g ≫ sX) := hY.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType sX := hX.toLocallyOfFiniteType
  haveI : QuasiCompact sX := hX.toQuasiCompact
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (g ≫ sX)
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : AlgebraicGeometry.IsNoetherian X := {}
  haveI : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g sX
  have hZcl : IsClosed Z :=
    closure_subset_iff_isClosed.mp (hZ.2 ⟨hZ.1.1.closure, closure_minimal hZ.1.2 hcl⟩
      subset_closure)
  set η := hZ.1.1.genericPoint with hηdef
  have hηZ : closure {η} = Z := by
    have := hZ.1.1.isGenericPoint_genericPoint_closure
    rwa [hZcl.closure_eq] at this
  have hηE : η ∈ exceptionalLocus g := hZ.1.2 (hηZ ▸ subset_closure rfl)
  have hmax : ∀ y ∈ exceptionalLocus g, y ⤳ η → y = η := by
    intro y hy hyη
    have h1 : Z ⊆ closure {y} := hηZ ▸ specializes_iff_closure_subset.mp hyη
    have h2 := hZ.2 ⟨isIrreducible_singleton.closure,
      closure_minimal (Set.singleton_subset_iff.mpr hy) hcl⟩ h1
    have h3 : η ⤳ y := specializes_iff_mem_closure.mpr (by rw [hηZ]; exact h2 (subset_closure rfl))
    exact (hyη.antisymm h3).eq
  suffices h1 : Order.coheight η = 1 by
    refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne η h1, ?_⟩
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne, hηZ]
  by_cases hηs : g η ∈ smoothLocus sX
  · exact coheight_eq_one_of_mem_smoothLocus sX g hg hηE hmax hηs
  · letI : Y.Over (Spec (.of k)) := ⟨g ≫ sX⟩
    haveI : LocallyOfFiniteType (Y ↘ Spec (.of k)) := ‹LocallyOfFiniteType (g ≫ sX)›
    have hCE : ∀ y ∈ (C.support : Set Y), y ∈ exceptionalLocus g := fun y hy => by
      by_contra h
      rw [hCsupp] at hy
      exact hy (mem_smoothLocus_of_notMem_exceptionalLocus sX hYsm h)
    refine MMP.coheight_eq_one_of_isEffectiveCartierDivisor k hC ?_
      fun y hy hyη => hmax y (hCE y hy) hyη
    rw [← SetLike.mem_coe, hCsupp]
    exact hηs

/-- The exceptional locus of a morphism lies in its exceptional set. -/
private theorem exceptionalLocus_subset_exceptionalSet {X Y : Scheme.{u}} (f : X ⟶ Y) :
    exceptionalLocus f ⊆ (exceptionalSet f : Set X) := by
  intro x hx
  by_contra h
  have hU : x ∈ f ⁻¹ᵁ biregularLocus f := by
    simpa [exceptionalSet] using h
  have : IsIso (f ∣_ biregularLocus f) := isBiregular_biregularLocus f
  refine mem_exceptionalLocus_iff.mp hx _ hU ?_
  rw [← morphismRestrict_ι]
  infer_instance

/-- If `π` is an isomorphism off a closed set `Z`, and `B` contains both `Z` and the exceptional
set of `g`, then the exceptional set of `π ≫ g` lies in `π ⁻¹' B`. -/
private theorem exceptionalSet_comp_subset {X Y Y' : Scheme.{u}} (g : Y ⟶ X) [IsProper g]
    (π : Y' ⟶ Y) (Z : Closeds Y) (hπ : IsIso (π ∣_ ⟨(Z : Set Y)ᶜ, Z.isClosed.isOpen_compl⟩))
    {B : Set Y} (hB : (exceptionalSet g : Set Y) ⊆ B) (hZ : (Z : Set Y) ⊆ B) :
    (exceptionalSet (π ≫ g) : Set Y') ⊆ π ⁻¹' B := by
  intro y' hy'
  by_contra hyB
  apply hy'
  set V0 : X.Opens := biregularLocus g ⊓
    ⟨(g '' (Z : Set Y))ᶜ, (g.isClosedMap _ Z.isClosed).isOpen_compl⟩
  have hgV : IsBiregular g V0 := isBiregular_iff_le_biregularLocus.mpr inf_le_left
  have hπV : IsBiregular π (g ⁻¹ᵁ V0) := by
    refine isBiregular_iff_le_biregularLocus.mpr (le_trans ?_ (le_biregularLocus hπ))
    intro y hy hyZ
    exact hy.2 ⟨y, hyZ, rfl⟩
  have hV : IsBiregular (π ≫ g) V0 := by
    change IsIso ((π ≫ g) ∣_ V0)
    rw [morphismRestrict_comp]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ hπV hgV
  have hgb : π y' ∉ (exceptionalSet g : Set Y) := fun h => hyB (hB h)
  refine le_biregularLocus hV ⟨not_not.mp hgb, ?_⟩
  rintro ⟨c, hcZ, hc⟩
  rw [Scheme.Hom.comp_apply] at hc
  have hcB : g c ∈ biregularLocus g := by
    rw [hc]; exact not_not.mp hgb
  have hb' : g (π y') ∈ biregularLocus g := hc ▸ hcB
  have hinj : c = π y' :=
    ((MMP.Threefold.Resolution.specializes_of_mem_biregularLocus g hcB hb'
      (hc ▸ specializes_rfl)).antisymm
      (MMP.Threefold.Resolution.specializes_of_mem_biregularLocus g hb' hcB
        (hc ▸ specializes_rfl))).eq
  exact hyB (by rw [Set.mem_preimage, ← hinj]; exact hZ hcZ)

/-- The exceptional set of a composite `f ≫ r`, `r` proper, lies in the exceptional set of `f`
together with the preimage of the exceptional set of `r`. -/
private theorem exceptionalSet_comp_subset_union {Y X₁ X : Scheme.{u}} (f : Y ⟶ X₁) (r : X₁ ⟶ X)
    [IsProper r] :
    (exceptionalSet (f ≫ r) : Set Y) ⊆
      (exceptionalSet f : Set Y) ∪ f ⁻¹' (exceptionalSet r : Set X₁) := by
  set Z : Closeds X₁ := (biregularLocus f).compl
  have hZo : (⟨(Z : Set X₁)ᶜ, Z.isClosed.isOpen_compl⟩ : X₁.Opens) = biregularLocus f :=
    TopologicalSpace.Opens.ext (compl_compl _)
  have hπ : IsIso (f ∣_ ⟨(Z : Set X₁)ᶜ, Z.isClosed.isOpen_compl⟩) := by
    rw [hZo]; exact isBiregular_biregularLocus f
  exact exceptionalSet_comp_subset r f Z hπ (B := (Z : Set X₁) ∪ (exceptionalSet r : Set X₁))
    Set.subset_union_right Set.subset_union_left

/-- The support of a product of three vanishing ideals is the union of the three closed sets. -/
private theorem coe_support_vanishingIdeal_mul_mul {X : Scheme.{u}} (Z₁ Z₂ Z₃ : Closeds X) :
    ((Scheme.IdealSheafData.vanishingIdeal Z₁ * Scheme.IdealSheafData.vanishingIdeal Z₂ *
      Scheme.IdealSheafData.vanishingIdeal Z₃).support : Set X) =
      (Z₁ : Set X) ∪ Z₂ ∪ Z₃ := by
  rw [Scheme.IdealSheafData.support_mul, Scheme.IdealSheafData.support_mul, Closeds.coe_sup,
    Closeds.coe_sup, Scheme.IdealSheafData.coe_support_vanishingIdeal,
    Scheme.IdealSheafData.coe_support_vanishingIdeal,
    Scheme.IdealSheafData.coe_support_vanishingIdeal]

/-- If a morphism of integral schemes is an isomorphism over a nonempty open subset, the inverse
image of an ideal sheaf whose support misses the generic point is nonzero. -/
private theorem comap_ne_bot_of_genericPoint_notMem {X X₁ : Scheme.{u}} [IsIntegral X]
    (r : X₁ ⟶ X) (U : X.Opens) (hU : (U : Set X).Nonempty) [IsIso (r ∣_ U)]
    {I : X.IdealSheafData} (hI : genericPoint X ∉ (I.support : Set X)) : I.comap r ≠ ⊥ := by
  intro h
  have : Surjective (r ∣_ U) := AlgebraicGeometry.instSurjectiveOfIsIsoScheme _
  obtain ⟨a, ha⟩ := (r ∣_ U).surjective ⟨genericPoint X, genericPoint_mem_of_opens_nonempty U hU⟩
  have hra : r a.1 = genericPoint X := by rw [← morphismRestrict_base_coe, ha]
  have : a.1 ∈ ((I.comap r).support : Set X₁) := by
    rw [h, Scheme.IdealSheafData.support_bot]; trivial
  rw [Scheme.IdealSheafData.support_comap] at this
  exact hI (hra ▸ this)

/-- The generic point of an integral scheme of finite type over a field of characteristic zero
lies neither off the biregular locus of a morphism whose biregular locus contains a nonempty open
subset, nor in the singular locus, nor in the support of a Cartier divisor. -/
private theorem genericPoint_notMem_support_vanishingIdeal_mul {k : Type u} [Field k]
    [CharZero k] {X X₁ : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X]
    [LocallyOfFiniteType sX] (r : X₁ ⟶ X) {U : X.Opens} (hUne : (U : Set X).Nonempty)
    (hUB : U ≤ biregularLocus r) (D : X.CartierDivisor) :
    genericPoint X ∉ ((Scheme.IdealSheafData.vanishingIdeal (biregularLocus r).compl *
      Scheme.IdealSheafData.vanishingIdeal (singularLocus sX) *
      Scheme.IdealSheafData.vanishingIdeal ⟨cartierSupport D, isClosed_cartierSupport D⟩).support :
        Set X) := by
  rw [coe_support_vanishingIdeal_mul_mul]
  rintro ((h | h) | h)
  · exact h (hUB (genericPoint_mem_of_opens_nonempty U hUne))
  · exact h (genericPoint_mem_of_opens_nonempty _ (by
      rw [smoothLocus_eq_smoothLocus]
      exact (Scheme.Hom.dense_smoothLocus_of_perfectField sX).nonempty))
  · exact genericPoint_notMem_cartierSupport D h

/-- An snc subset of a smooth scheme is the union of the supports of a finite set of prime
divisors whose reduced divisor is snc. -/
private theorem exists_isSNC_of_isSNCSubset {k : Type u} [Field k] {Y : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [LocallyOfFinitePresentation sY] {S : Closeds Y}
    (hS : IsSNCSubset sY S) (hY : IsSmoothScheme sY) :
    ∃ s : Finset (Mori.PrimeDivisor Y), (⋃ E ∈ s, E.support) = (S : Set Y) ∧
      (∑ E ∈ s, Finsupp.single E (1 : ℤ) : Divisor Y).IsSNC sY := by
  rcases hS with h0 | h
  · refine ⟨∅, by rw [h0]; simp, ?_⟩
    rw [Finset.sum_empty]
    exact DivisorWithCoeffs.isSNC_zero_of_isSmoothScheme _ hY
  · exact h

/-- The Weil divisor of a pull-back of `D`, plus a reduced divisor with components among `s`,
has its components among `s` when the components of `s` cover the preimage of `Supp D`. -/
private theorem support_add_sum_filter_subset {X Y : Scheme.{u}} {g : Y ⟶ X}
    {D : X.CartierDivisor} {D' : Y.CartierDivisor} (hD' : IsPullback g D D') {wD' : Divisor Y}
    (hwD' : IsWeilDivisorOfCartier D' wD') {s : Finset (Mori.PrimeDivisor Y)} {C : Set Y}
    [DecidablePred fun E : Mori.PrimeDivisor Y => (E.support : Set Y) ⊆ C]
    (hDs : g ⁻¹' cartierSupport D ⊆ ⋃ E ∈ s, E.support) :
    (wD' + (∑ E ∈ s.filter (fun E => (E.support : Set Y) ⊆ C), Finsupp.single E (1 : ℤ) :
      Divisor Y)).support ⊆ s := by
  classical
  intro P hP
  have hP' : (wD' + (∑ E ∈ s.filter (fun E => (E.support : Set Y) ⊆ C),
      Finsupp.single E (1 : ℤ) : Divisor Y)).coeff P ≠ 0 := by
    rwa [DivisorWithCoeffs.coeff_apply, ← Finsupp.mem_support_iff]
  rw [DivisorWithCoeffs.coeff_add] at hP'
  by_cases hw : wD'.coeff P = 0
  · rw [hw, zero_add, coeff_sum_single] at hP'
    split_ifs at hP' with h
    · exact (Finset.mem_filter.mp h).1
    · exact absurd rfl hP'
  · exact mem_of_support_subset fun y hy => hDs (cartierSupport_subset_preimage_of_isPullback hD'
      (Classical.byContradiction (fun h => hw ((hwD' P).eq_zero_of_not_subset h)) hy))

/-- **The last step of the embedded resolution.** A resolution `g` of `X`, with `g⁻¹(Sing X)` the
support of an effective Cartier divisor, whose exceptional locus and preimage of `Supp D` lie in
an snc subset, is an embedded resolution of `D`. -/
private theorem isEmbeddedResolution_of_subset_isSNCSubset {k : Type u} [Field k] [CharZero k]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) {D : X.CartierDivisor} (hD : IsEffective D)
    {g : Y ⟶ X} (hg : IsResolution sX g) {S : Closeds Y} (hS : IsSNCSubset (g ≫ sX) S)
    (hExc : exceptionalLocus g ⊆ (S : Set Y)) (hDS : g ⁻¹' cartierSupport D ⊆ S)
    {C : Y.IdealSheafData} (hC : Stacks.Divisors.IsEffectiveCartierDivisor C)
    (hCsupp : (C.support : Set Y) = g ⁻¹' (singularLocus sX : Set X)) :
    IsEmbeddedResolution sX D g := by
  classical
  obtain ⟨hX, hYv, hgsm, -, hgbir⟩ := id hg
  haveI : IsIntegral X := hX.toIsIntegral
  haveI : LocallyOfFiniteType sX := hX.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  haveI : IsIntegral Y := hYv.toIsIntegral
  haveI : LocallyOfFiniteType (g ≫ sX) := hYv.toLocallyOfFiniteType
  haveI : QuasiCompact (g ≫ sX) := hYv.toQuasiCompact
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (g ≫ sX)
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (g ≫ sX)
  haveI : AlgebraicGeometry.IsNoetherian Y := {}
  haveI : IsDominant g := hgbir.isDominant
  have hpure := isPureCodimOne_exceptionalLocus sX hX g hYv hgsm hgbir hC hCsupp
  obtain ⟨D', hD'⟩ := exists_isPullback (pullbackCondition_of_isDominant g D)
  obtain ⟨wD', hwD'⟩ := exists_isWeilDivisorOfCartier D'
  obtain ⟨s, hs, hsnc⟩ := exists_isSNC_of_isSNCSubset hS hgsm
  exact ⟨hD, hg, hpure, D', wD', _, hD', hwD',
    isReducedDivisorWithSupport_sum_filter (isClosed_exceptionalLocus g) hpure (hs ▸ hExc),
    isSNCDivisor_reducedDivisorOf_of_isSNC hsnc
      (support_add_sum_filter_subset hD' hwD' fun y hy => hs ▸ hDS hy)⟩

end Proof_thm_mmp_lazarsfeld_embedded_resolution_dictionary

namespace MMP.Intersection

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP MMP.Mori MMP.Intersection
open Proof_thm_mmp_lazarsfeld_embedded_resolution_dictionary

/-- **Hironaka's embedded resolution** (Lazarsfeld Thm. 4.1.3): an effective Cartier divisor `D`
on a variety `X` over a field of characteristic zero has an embedded resolution
`μ : X' ⟶ X`, in the sense of `MMP.Intersection.IsEmbeddedResolution`. -/
@[mmp "thm_mmp_lazarsfeld_embedded_resolution_dictionary"]
public theorem exists_isEmbeddedResolution {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (hX : MMP.Mori.IsVariety k sX) (D : X.CartierDivisor)
    (hD : IsEffective D) :
    ∃ (X' : Scheme.{u}) (μ : X' ⟶ X), IsEmbeddedResolution sX D μ := by
  classical
  haveI : IsIntegral X := hX.toIsIntegral
  haveI : IsSeparated sX := hX.toIsSeparated
  haveI : LocallyOfFiniteType sX := hX.toLocallyOfFiniteType
  haveI : QuasiCompact sX := hX.toQuasiCompact
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  obtain ⟨X₁, r, U, hX₁, hrp, hUne, hrU, hrq⟩ :=
    exists_isHQuasiProjective_isIso_morphismRestrict sX hX
  haveI : IsIntegral X₁ := hX₁.toIsIntegral
  haveI := Stacks.Ample.isInvertibleModule_unit (Spec (.of k))
  obtain ⟨L, hL, hLa⟩ := exists_isAmple_of_isQuasiProjective (r ≫ sX) _
    (Stacks.Ample.isAmple_unitModule_of_isAffine _) (isQuasiProjective_of_isHQuasiProjective _ hrq)
  set IW : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal (biregularLocus r).compl
  set IS : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal (singularLocus sX) with hIS
  set ID : X.IdealSheafData :=
    Scheme.IdealSheafData.vanishingIdeal ⟨cartierSupport D, isClosed_cartierSupport D⟩
  set Itot : X.IdealSheafData := IW * IS * ID with hItot
  have hItot_supp : (Itot.support : Set X) =
      ((biregularLocus r : Set X)ᶜ ∪ (singularLocus sX : Set X)) ∪ cartierSupport D :=
    coe_support_vanishingIdeal_mul_mul _ _ _
  obtain ⟨Y, f, hYv, hfproj, hfbir, hfsm, -, hfcart, hfsnc, -⟩ :=
    MMP.Resolution.exists_isResolutionOfVariety_isEffectiveCartierDivisor_comap (r ≫ sX) hX₁
      (Itot.comap r) (comap_ne_bot_of_genericPoint_notMem r U hUne
        (genericPoint_notMem_support_vanishingIdeal_mul sX r hUne
          (isBiregular_iff_le_biregularLocus.mp hrU) D))
  set g : Y ⟶ X := f ≫ r
  have hgsX : g ≫ sX = f ≫ r ≫ sX := Category.assoc _ _ _
  have hYv' : Mori.IsVariety k (g ≫ sX) := by rwa [hgsX]
  have hgsm : IsSmoothScheme (g ≫ sX) := by rwa [hgsX]
  haveI : IsIntegral Y := hYv'.toIsIntegral
  have hJg : (Itot.comap r).comap f = Itot.comap g :=
    (Scheme.IdealSheafData.comap_comp Itot f r).symm
  have hgproj : IsProjectiveMorphism g := (isProjectiveMorphism_of_isProjective f L hLa hfproj).comp
    (isProjectiveMorphism_of_isHQuasiProjective_comp r sX hrq)
  have hgbir : IsBirationalMorphism g :=
    isBirationalMorphism_comp hfbir (isBirationalMorphism_of_isIso_morphismRestrict r U hUne)
  set S : Closeds Y := Mori.exceptionalSet f ⊔ (Itot.comap g).support with hSdef
  have hpre : ∀ y : Y, g y ∈ ((biregularLocus r : Set X)ᶜ ∪ (singularLocus sX : Set X)) ∪
      cartierSupport D → y ∈ (S : Set Y) := fun y hy => by
    right
    rw [Scheme.IdealSheafData.support_comap]
    exact (hItot_supp.symm ▸ hy : g y ∈ (Itot.support : Set X))
  have hExc : (Mori.exceptionalSet g : Set Y) ⊆ S := fun y hy =>
    (exceptionalSet_comp_subset_union f r hy).elim Or.inl fun h => hpre y (Or.inl (Or.inl h))
  rw [hJg, show Itot = IS * (IW * ID) by rw [hItot]; ring, comap_mul] at hfcart
  refine ⟨Y, g, isEmbeddedResolution_of_subset_isSNCSubset sX hD ⟨hX, hYv', hgsm, hgproj, hgbir⟩
    (by rwa [hgsX, hSdef, ← hJg]) ((exceptionalLocus_subset_exceptionalSet g).trans hExc)
    (fun y hy => hpre y (Or.inr hy))
    (isEffectiveCartierDivisor_left_of_mul _ _ hfcart) ?_⟩
  rw [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage, hIS,
    Scheme.IdealSheafData.coe_support_vanishingIdeal]

end MMP.Intersection

end
