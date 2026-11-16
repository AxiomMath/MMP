module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.BadSurface
public import MMP.AlgebraicGeometry.MMP.Fourfold.ElementaryDlt
public import MMP.AlgebraicGeometry.MMP.Fourfold.StepSequence
public import MMP.AlgebraicGeometry.MMP.Fourfold.WeakModel
public import MMP.AlgebraicGeometry.Divisor.DivisorialValuation
import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram.BadLocusDiscrepancy
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.JunctionLabels
import MMP.AlgebraicGeometry.RegularEmbedding.ExceptionalBundle
import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal
import MMP.AlgebraicGeometry.Morphisms.Birational.BiregularLocusCodimOnePoints
import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ExceptionalValuations
import MMP.AlgebraicTopology.BorelMoore.CycleSpanRestriction
import MMP.RingTheory.RegularLocalRing.FiniteFreeResolution
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
import MMP.AlgebraicGeometry.MMP.Fourfold.PreparedChainDifficulty
import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
import MMP.AlgebraicGeometry.SpreadingOut.CanonicalDivisor

/-!
# Step sequences of fourfolds: cycle ranks, bad surfaces and singularities

Let `(X_i, B_i) → Z_i ← (X_{i+1}, B_{i+1})` be a step sequence of complex projective fourfolds,
with negative and positive bad loci `W_i⁻ ⊆ X_i`, `W_i⁺ ⊆ X_{i+1}` and bad locus `Σ_i ⊆ Z_i` of
the base. This file proves the finiteness statements and the preservation of singularities that
the termination argument for such sequences rests on.

*Cycle ranks.* Off `W_i⁻` and `W_i⁺` the two sides of a step are identified with the common
biregular locus of `Z_i`, so their cycle ranks agree there. Removing a closed set of dimension
`< r` does not change `ρ_r`, and removing one with an `r`-dimensional component lowers it. Hence
the third cycle ranks `ρ_3(X_i)` are nonincreasing and drop at each step that loses a prime
divisor (`dim W_i⁺ ≤ 2` always), and along a small tail with no positive-side bad surface the
second cycle ranks `ρ_2(X_i)` are nonincreasing and drop at each step with a negative-side bad
surface. A nonincreasing sequence of natural numbers drops only finitely often.

*Singularities.* A step extracts no divisor, so the strict transform `B⁺ = (f⁺)⁻¹_* f⁻_* B⁻` is
a boundary and `K⁺ = (f⁺)⁻¹_* f⁻_* K⁻` is a canonical divisor (both are `div` of the pull-back of
one rational top form on `Z`). For a divisor over `X⁺` with a counterpart over `X⁻` of the same
valuation, `a(ξ; X⁻, B⁻) ≤ a(ξ; X⁺, B⁺)`: strictly if the centre on `X⁺` lies in `W⁺`, and with
equality otherwise, by locality of discrepancies along the identification over the common
biregular locus. So klt passes from `(X⁻, B⁻)` to `(X⁺, B⁺)`, and terminal does too when `f⁻` is
small, since then a valuation exceptional over `X⁺` is exceptional over `X⁻`.

*Surfaces suffice.* If no small step from `i₀` on has a positive-side bad surface, the sequence
is small from some index on (a non-small step loses a divisor), then has no negative-side bad
surface from some later index on, and then `dim W_i^± ≤ 1`, which the graph bound
`dim W_i⁻ + dim W_i⁺ ≥ 3` for `Σ_i ≠ ∅` rules out.

## Main results

* `MMP.Fourfold.StepSequence.finite_setOf_exists_primeDivisor_isExceptionalValuation`: only
  finitely many steps lose a prime divisor.
* `MMP.Fourfold.StepSequence.finite_setOf_exists_isNegativeBadSurface`: along a small tail with
  no positive-side bad surface, only finitely many steps have a negative-side bad surface.
* `MMP.Fourfold.IsFourfoldStepDiagram.isKltPair_flipTransform`: klt is preserved by a step.
* `MMP.Fourfold.IsFourfoldStepDiagram.isKltTerminalPair_flipTransform`: terminal is preserved by a
  small step.
* `MMP.Fourfold.StepSequence.eventually_badLocusBaseAt_eq_bot`: if no small step from `i₀` on has
  a positive-side bad surface, then `Σ_i = ∅` for all but finitely many `i`.

## Implementation notes

"`ord_E` is exceptional over `X_{i+1}`" is the existence of a valuation `ξ` of `k(X_{i+1})`
transported from `ord_E` (`MMP.Fourfold.StepSequence.IsTransportedValuation`) with
`MMP.Intersection.IsExceptionalValuation`; since the field maps are isomorphisms, such a `ξ` is
unique.

The source states the negative-side finiteness for a sequence small from the index `0` with no
positive-side bad surface at all; it is stated here from an arbitrary index `i₀`, which is the
source's statement applied to the tail `MMP.Fourfold.StepSequence.shift`.

The source deduces the comparison of log discrepancies from the identity
`a(ξ; X⁺, B⁺) - a(ξ; X⁻, B⁻) = ξ(H) ≥ 0` for the graph divisor `H`. Here the inequality is split
into the strict case over the bad locus
(`MMP.Fourfold.IsFourfoldStepDiagram.tfae_lt_and_centre_subset_badLocus`) and the equality case
off it.

## References

* [OpenAI, *Projective lc fourfolds*][OAI4]
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Fourfold

/-! ### Dimensions of closed subsets -/

/-- If every irreducible closed subset of a closed set `T` has codimension at least `c` in a space
of dimension at most `a + c`, then `T` has dimension at most `a`. -/
private theorem topologicalKrullDim_le_of_le_coheight {X : Type*} [TopologicalSpace X]
    {T : Set X} (hT : IsClosed T) {a c : ℕ} (hX : topologicalKrullDim X ≤ (a + c : ℕ))
    (hc : ∀ W : IrreducibleCloseds X, (W : Set X) ⊆ T → c ≤ Order.coheight W) :
    topologicalKrullDim T ≤ a := by
  let m := IrreducibleCloseds.map (Subtype.val : T → X) continuous_subtype_val
  rw [topologicalKrullDim, Order.krullDim_eq_iSup_height]
  refine iSup_le fun W => WithBot.coe_le_coe.mpr ?_
  have hW : Order.height (m W) + Order.coheight (m W) ≤ (a + c : ℕ) := by
    have : Nonempty (IrreducibleCloseds X) := ⟨m W⟩
    rw [topologicalKrullDim, Order.krullDim_eq_iSup_height_add_coheight_of_nonempty] at hX
    exact (le_iSup (fun V => Order.height V + Order.coheight V) (m W)).trans
      (WithBot.coe_le_coe.mp hX)
  refine (Order.height_le_height_apply_of_strictMono m
    (IrreducibleCloseds.map_strictMono_of_isInducing .subtypeVal) W).trans
    ((ENat.add_le_add_iff_right (ENat.coe_ne_top c)).mp ?_)
  refine (add_le_add le_rfl (hc (m W) ?_)).trans (by exact_mod_cast hW)
  rw [IrreducibleCloseds.coe_map]
  exact closure_minimal (Subtype.coe_image_subset _ _) hT

/-- A dimension `d ≤ 2` with `d ≠ 2` and `d + c = 4` forces the codimension `c ≥ 3`. -/
private theorem three_le_of_add_eq_four {d : WithBot ℕ∞} {c : ℕ∞} (hd : d ≤ 2) (hd2 : d ≠ 2)
    (h : d + c = 4) : 3 ≤ c := by
  lift d to ℕ∞ using by rintro rfl; simp at h
  rw [← WithBot.coe_add] at h
  replace h : d + c = 4 := WithBot.coe_inj.mp h
  have hd' : d < 2 := (WithBot.coe_le_coe.mp hd).lt_of_ne fun e => hd2 (by rw [e]; rfl)
  lift d to ℕ using hd'.ne_top
  induction c using ENat.recTopCoe with
  | top => exact le_top
  | coe c =>
    norm_cast at h hd' ⊢
    omega

/-- On a fourfold, a closed set of dimension at most two containing no irreducible closed subset
of dimension exactly two has dimension at most one. -/
private theorem topologicalKrullDim_le_one {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    [IsIntegral X] [LocallyOfFiniteType sX] (hX : topologicalKrullDim X = 4) {T : Set X}
    (hT : IsClosed T) (h2 : topologicalKrullDim T ≤ 2)
    (hno : ∀ V : IrreducibleCloseds X, (V : Set X) ⊆ T → topologicalKrullDim (V : Set X) ≠ 2) :
    topologicalKrullDim T ≤ 1 := by
  have h1 : topologicalKrullDim T ≤ (1 : ℕ) := by
    refine topologicalKrullDim_le_of_le_coheight (a := 1) (c := 3) hT (by rw [hX]; rfl)
      fun W hW => ?_
    rw [← codimension_eq_coheight, MMP.Flips.codimension_eq_coheight_genericPoint]
    have hsum := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX
      W.isIrreducible.genericPoint
    rw [W.isIrreducible.isGenericPoint_genericPoint W.isClosed, hX] at hsum
    exact three_le_of_add_eq_four
      ((Topology.IsEmbedding.inclusion hW).isInducing.topologicalKrullDim_le.trans h2)
      (hno W hW) hsum
  exact_mod_cast h1

/-- For `C ⊆ A`, the preimage of `C` in the subspace `A` is homeomorphic to `C`. -/
private theorem isHomeomorph_preimage_val {X : Type*} [TopologicalSpace X] {A C : Set X}
    (hCA : C ⊆ A) :
    IsHomeomorph (fun p : (Subtype.val ⁻¹' C : Set A) => (⟨p.1.1, p.2⟩ : C)) := by
  rw [isHomeomorph_iff_isEmbedding_surjective]
  refine ⟨?_, fun q => ⟨⟨⟨q.1, hCA q.2⟩, q.2⟩, rfl⟩⟩
  exact Topology.IsEmbedding.of_comp (by fun_prop) continuous_subtype_val
    ((Topology.IsEmbedding.subtypeVal (p := (· ∈ A))).comp
      (Topology.IsEmbedding.subtypeVal (p := (· ∈ (Subtype.val ⁻¹' C : Set A)))))

/-- An integral scheme of finite type over `ℂ` of dimension `r + 1` has a point of coheight one. -/
private theorem exists_coheight_eq_one (V : Scheme.{0}) [IsIntegral V] [CompactSpace V]
    (sV : V ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sV] {r : ℕ}
    (hdim : topologicalKrullDim V = (r + 1 : ℕ)) : ∃ y : V, Order.coheight y = 1 := by
  obtain ⟨x, -, hx⟩ := (isClosed_univ (X := V)).exists_closed_singleton Set.univ_nonempty
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sV x
  rw [hx.closure_eq, hdim] at h
  have : Nonempty (IrreducibleCloseds ({x} : Set V)) :=
    ⟨⟨{⟨x, rfl⟩}, isIrreducible_singleton, isClosed_discrete _⟩⟩
  rw [le_antisymm (topologicalKrullDim_zero_of_discreteTopology _) Order.krullDim_nonneg,
    zero_add] at h
  have hc : Order.coheight x = (r + 1 : ℕ) := by exact_mod_cast h
  rcases r.eq_zero_or_pos with rfl | hr
  · exact ⟨x, by simpa using hc⟩
  obtain ⟨y, -, hy⟩ := (Order.coe_lt_coheight_iff (n := 1) (by rw [hc]; exact ENat.coe_lt_top _)).mp
    (by rw [hc]; exact_mod_cast Nat.succ_lt_succ hr)
  exact ⟨y, by exact_mod_cast hy⟩

/-- On an irreducible scheme, a point of a closed proper subset has positive coheight. -/
private theorem one_le_coheight_of_mem {V : Scheme.{0}} [IrreducibleSpace V] {A : Set V}
    (hA : IsClosed A) (hAne : A ≠ Set.univ) {x : V} (hx : x ∈ A) : 1 ≤ Order.coheight x := by
  by_contra hlt
  have hmax : IsMax x := Order.coheight_eq_zero.mp (ENat.lt_one_iff_eq_zero.mp (not_le.mp hlt))
  have hg : genericPoint V ⤳ x := (genericPoint_spec V).specializes (Set.mem_univ x)
  have hgx : x ⤳ genericPoint V :=
    Scheme.le_iff_specializes.mp (hmax (Scheme.le_iff_specializes.mpr hg))
  apply hAne
  refine Set.eq_univ_of_forall fun z => ?_
  have hη : genericPoint V ∈ A := hgx.mem_closed hA hx
  exact ((genericPoint_spec V).specializes (Set.mem_univ z)).mem_closed hA hη

/-- An irreducible set `C ⊆ A` is irreducible as a subset of the subspace `A`. -/
private theorem isIrreducible_preimage_val {X : Type*} [TopologicalSpace X] {A C : Set X}
    (hCA : C ⊆ A) (hC : IsIrreducible C) : IsIrreducible (Subtype.val ⁻¹' C : Set A) := by
  have : (Subtype.val ⁻¹' C : Set A) = (fun q : C => (⟨q.1, hCA q.2⟩ : A)) '' Set.univ := by
    ext p
    exact ⟨fun hp => ⟨⟨p.1, hp⟩, trivial, rfl⟩, by rintro ⟨q, -, rfl⟩; exact q.2⟩
  rw [this]
  haveI := Subtype.irreducibleSpace hC
  exact (IrreducibleSpace.isIrreducible_univ C).image _ (by fun_prop : Continuous _).continuousOn

/-- An irreducible set `C ⊆ A` which is maximal among the irreducible subsets of `A` is, as a
subset of the subspace `A`, an irreducible component of `A`. -/
private theorem preimage_val_mem_irreducibleComponents {X : Type*} [TopologicalSpace X]
    {A C : Set X} (hCA : C ⊆ A) (hC : IsIrreducible C)
    (hmax : ∀ T : Set X, IsIrreducible T → C ⊆ T → T ⊆ A → T ⊆ C) :
    (Subtype.val ⁻¹' C : Set A) ∈ irreducibleComponents A := by
  refine ⟨isIrreducible_preimage_val hCA hC, fun T hT hZT p hp => ?_⟩
  exact hmax _ (hT.image _ continuous_subtype_val.continuousOn)
    (fun x hx => ⟨⟨x, hCA hx⟩, hZT hx, rfl⟩) (Subtype.coe_image_subset A T) ⟨p, hp, rfl⟩

/-- On an irreducible scheme, the closure of a point `y` of coheight one is maximal among the
irreducible subsets of a closed proper subset containing `y`. -/
private theorem subset_closure_singleton_of_coheight_eq_one {V : Scheme.{0}} [IrreducibleSpace V]
    {A : Set V} (hA : IsClosed A) (hAne : A ≠ Set.univ) {y : V} (hy : Order.coheight y = 1)
    {T : Set V} (hT : IsIrreducible T) (hyT : closure {y} ⊆ T) (hTA : T ⊆ A) :
    T ⊆ closure {y} := by
  have hG := hT.isGenericPoint_genericPoint_closure
  have hle : y ≤ hT.genericPoint :=
    Scheme.le_iff_specializes.mpr (hG.specializes (subset_closure (hyT (subset_closure rfl))))
  by_cases hGy : hT.genericPoint ≤ y
  · exact subset_closure.trans (hG.symm.subset.trans (closure_minimal
      (Set.singleton_subset_iff.mpr (Scheme.le_iff_specializes.mp hGy).mem_closure)
      isClosed_closure))
  · have h1 := Order.coheight_add_one_le (lt_of_le_not_ge hle hGy)
    have h2 := one_le_coheight_of_mem hA hAne (closure_minimal hTA hA hG.mem)
    rw [hy] at h1
    exact absurd ((add_le_add_left h2 1).trans h1) (by decide)

/-- An irreducible closed subset of dimension two of a closed set `A` of dimension at most two
lies in an irreducible component of `A` of dimension two. -/
private theorem exists_mem_irreducibleComponents {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : topologicalKrullDim A ≤ 2) (V : IrreducibleCloseds X) (hVA : (V : Set X) ⊆ A)
    (hV : topologicalKrullDim (V : Set X) = 2) :
    ∃ Z : Set A, Z ∈ irreducibleComponents A ∧ topologicalKrullDim Z = 2 := by
  obtain ⟨Z, hZ, hVZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _
    (isIrreducible_preimage_val hVA V.isIrreducible)
  refine ⟨Z, hZ, le_antisymm ((topologicalKrullDim_subspace_le A Z).trans hA) ?_⟩
  rw [← hV, ← (isHomeomorph_preimage_val hVA).topologicalKrullDim_eq]
  exact (Topology.IsEmbedding.inclusion hVZ).isInducing.topologicalKrullDim_le

/-! ### Cycle ranks along a step sequence -/

section CycleRank

open MMP.Analytic

/-- On a projective complex integral scheme of dimension `r + 1`, removing a closed proper subset
containing a point of coheight one strictly lowers the `r`-th cycle rank. -/
private theorem cycleRank_opens_lt_of_coheight_eq_one (V : Scheme.{0}) [V.Over (Spec (.of ℂ))]
    [MMP.IsComplexScheme V] [IsIntegral V]
    (hV : MMP.Mori.IsProjectiveVariety ℂ (V ↘ Spec (.of ℂ))) {r : ℕ}
    (hdim : topologicalKrullDim V = (r + 1 : ℕ)) {A : Set V} (hA : IsClosed A)
    (hAne : A ≠ Set.univ) {y : V} (hy : Order.coheight y = 1) (hyA : y ∈ A)
    (U : V.Opens) (hU : (U : Set V) = Aᶜ)
    [U.toScheme.Over (Spec (.of ℂ))] [U.ι.IsOver (Spec (.of ℂ))] :
    cycleRank U.toScheme r < cycleRank V r := by
  haveI : LocallyOfFiniteType (V ↘ Spec (.of ℂ)) := hV.toIsVariety.toLocallyOfFiniteType
  have hdimA : topologicalKrullDim A ≤ r := by
    refine topologicalKrullDim_le_of_le_coheight (c := 1) hA hdim.le fun W hW => ?_
    rw [← codimension_eq_coheight, MMP.Flips.codimension_eq_coheight_genericPoint]
    exact one_le_coheight_of_mem hA hAne
      (hW (W.isIrreducible.isGenericPoint_genericPoint W.isClosed).mem)
  have hdy : topologicalKrullDim (closure {y} : Set V) = r := by
    have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight (V ↘ Spec (.of ℂ)) y
    rw [hy, hdim] at h
    induction hd : topologicalKrullDim (closure {y} : Set V) using WithBot.recBotCoe with
    | bot =>
      rw [hd, WithBot.bot_add] at h
      exact absurd h.symm WithBot.coe_ne_bot
    | coe e =>
      rw [hd] at h
      norm_cast at h ⊢
      exact ENat.add_left_injective_of_ne_top ENat.one_ne_top (by simpa using h)
  have hCA : closure {y} ⊆ A := closure_minimal (Set.singleton_subset_iff.mpr hyA) hA
  exact cycleRank_opens_lt_of_mem_irreducibleComponents V hV hA hdimA
    (preimage_val_mem_irreducibleComponents hCA isIrreducible_singleton.closure
      fun T hT hyT hTA => subset_closure_singleton_of_coheight_eq_one hA hAne hy hT hyT hTA)
    (hdy ▸ (isHomeomorph_preimage_val hCA).topologicalKrullDim_eq _) U hU

/-- The `r`-th cycle span of a projective complex integral scheme of dimension `r + 1` is
finite-dimensional. -/
private theorem finiteDimensional_cycleSpan (V : Scheme.{0}) [V.Over (Spec (.of ℂ))]
    [MMP.IsComplexScheme V] [IsIntegral V] [CompactSpace V]
    (hV : MMP.Mori.IsProjectiveVariety ℂ (V ↘ Spec (.of ℂ))) {r : ℕ}
    (hdim : topologicalKrullDim V = (r + 1 : ℕ)) : FiniteDimensional ℚ (cycleSpan V r) := by
  haveI : LocallyOfFiniteType (V ↘ Spec (.of ℂ)) := hV.toIsVariety.toLocallyOfFiniteType
  obtain ⟨y, hy⟩ := exists_coheight_eq_one V (V ↘ Spec (.of ℂ)) hdim
  let U : V.Opens := ⟨(closure {y})ᶜ, isClosed_closure.isOpen_compl⟩
  letI : U.toScheme.Over (Spec (.of ℂ)) := ⟨U.ι ≫ V ↘ Spec (.of ℂ)⟩
  haveI : U.ι.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  have hne : closure {y} ≠ Set.univ := fun huniv => one_ne_zero <| hy ▸
    Order.coheight_eq_zero.mpr fun z _ => Scheme.le_iff_specializes.mpr
      (specializes_iff_mem_closure.mpr (huniv ▸ Set.mem_univ z))
  exact Module.finite_of_finrank_pos (Nat.zero_le _ |>.trans_lt <|
    cycleRank_opens_lt_of_coheight_eq_one V hV hdim isClosed_closure hne hy (subset_closure rfl)
      U rfl)

/-- In a step diagram of fourfolds the negative bad locus `W⁻` is a proper subset of `X⁻`: the
generic point of `Z` has codimension zero, so it lies in the common biregular locus. -/
private theorem badLocusMinus_ne_univ {Xm Xp Z : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm]
    [IsLocallyNoetherian Xm] [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp]
    [IsLocallyNoetherian Xp] [IsNormal Xp] {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    {sXp : Xp ⟶ Spec (.of ℂ)} {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp) :
    (badLocusMinus fm fp : Set Xm) ≠ Set.univ := by
  haveI : IsIntegral Z := h.isNormalVariety_target.1.toIsIntegral
  have hgen : ringKrullDim (Z.presheaf.stalk (genericPoint Z)) ≤ 1 := by
    rw [ringKrullDim_stalk_eq_coheight, Order.coheight_eq_zero.mpr fun z _ =>
      Scheme.le_iff_specializes.mpr ((genericPoint_spec Z).specializes (Set.mem_univ z))]
    exact_mod_cast zero_le_one
  haveI : IsProper fm := isProper_of_isProjectiveMorphism fm h.isProjectiveMorphism_minus
  haveI : IsProper fp := h.isProper_plus
  haveI : IsDominant fm := h.isBirationalMorphism_minus.isDominant
  have hU : genericPoint Z ∈ commonBiregularLocus fm fp :=
    ⟨mem_biregularLocus_of_ringKrullDim_stalk_le_one h.isNormalVariety_target fm
        (h.comp_eq_minus ▸ h.isNormalVariety_minus.1) h.isBirationalMorphism_minus hgen,
      mem_biregularLocus_of_ringKrullDim_stalk_le_one h.isNormalVariety_target fp
        (h.comp_eq_plus ▸ h.isNormalVariety_plus.1) h.isBirationalMorphism_plus hgen⟩
  obtain ⟨x, hx⟩ := fm.denseRange.exists_mem_open (commonBiregularLocus fm fp).isOpen ⟨_, hU⟩
  exact fun heq => (heq ▸ Set.mem_univ x : x ∈ (badLocusMinus fm fp : Set Xm)) hx

/-- One step of a step diagram of fourfolds does not increase the third cycle rank, and lowers it
strictly when the negative bad locus contains a prime divisor. -/
private theorem cycleRank_le_and_lt {Xm Xp Z : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm]
    [IsLocallyNoetherian Xm] [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp]
    [IsLocallyNoetherian Xp] [IsNormal Xp] [Xm.Over (Spec (.of ℂ))] [Xp.Over (Spec (.of ℂ))]
    [MMP.IsComplexScheme Xm] [MMP.IsComplexScheme Xp]
    {sZ : Z ⟶ Spec (.of ℂ)} {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (h : IsFourfoldStepDiagram (Xm ↘ Spec (.of ℂ)) sZ (Xp ↘ Spec (.of ℂ)) K B fm fp) :
    cycleRank Xp 3 ≤ cycleRank Xm 3 ∧
      ((∃ E : MMP.Mori.PrimeDivisor Xm, (E.support : Set Xm) ⊆ badLocusMinus fm fp) →
        cycleRank Xp 3 < cycleRank Xm 3) := by
  set U := commonBiregularLocus fm fp
  let Um : Xm.Opens := fm ⁻¹ᵁ U
  let Up : Xp.Opens := fp ⁻¹ᵁ U
  letI : Um.toScheme.Over (Spec (.of ℂ)) := ⟨Um.ι ≫ Xm ↘ Spec (.of ℂ)⟩
  haveI : Um.ι.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  letI : Up.toScheme.Over (Spec (.of ℂ)) := ⟨Up.ι ≫ Xp ↘ Spec (.of ℂ)⟩
  haveI : Up.ι.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  haveI : IsIso (fm ∣_ U) := isBiregular_commonBiregularLocus_left fm fp
  haveI : IsIso (fp ∣_ U) := isBiregular_commonBiregularLocus_right fm fp
  let φ : Um.toScheme ≅ Up.toScheme := asIso (fm ∣_ U) ≪≫ (asIso (fp ∣_ U)).symm
  have hφ : φ.hom ≫ (Up.toScheme ↘ Spec (.of ℂ)) = Um.toScheme ↘ Spec (.of ℂ) := by
    change φ.hom ≫ Up.ι ≫ Xp ↘ Spec (.of ℂ) = Um.ι ≫ Xm ↘ Spec (.of ℂ)
    simp only [φ, Iso.trans_hom, asIso_hom, Iso.symm_hom, asIso_inv, Category.assoc]
    rw [← h.comp_eq_plus, ← h.comp_eq_minus, ← morphismRestrict_ι_assoc,
      ← morphismRestrict_ι_assoc, IsIso.inv_hom_id_assoc]
  have hUm : cycleRank Um.toScheme 3 = cycleRank Up.toScheme 3 :=
    (cycleRank_eq_of_iso φ hφ).2.2.2 3
  have hUp : cycleRank Up.toScheme 3 = cycleRank Xp 3 := by
    refine cycleRank_eq_of_topologicalKrullDim_lt Xp h.isProjectiveVariety_plus
      (badLocusPlus fm fp).isClosed ?_ Up (compl_compl _).symm
    exact h.topologicalKrullDim_badLocusPlus_le_two.trans_lt (by exact_mod_cast (by decide : 2 < 3))
  have hle : cycleRank Um.toScheme 3 ≤ cycleRank Xm 3 := by
    rw [cycleRank, ← map_restrict_cycleSpan_compl Xm h.isProjectiveVariety_minus.isProjective
      (badLocusMinus fm fp) Um (compl_compl _).symm 3]
    exact @Submodule.finrank_map_le _ _
      ((MMP.Analytic.borelMooreHomology (Um.toScheme ↘ Spec (.of ℂ)) (2 * 3) : ModuleCat ℚ) : Type)
      _ _ _ _ _ _ _ _
      (finiteDimensional_cycleSpan Xm h.isProjectiveVariety_minus (r := 3) h.dim_minus)
  refine ⟨hUp ▸ hUm ▸ hle, fun ⟨E, hE⟩ => ?_⟩
  have hyA : E.genericPoint ∈ (badLocusMinus fm fp : Set Xm) :=
    hE (by rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl)
  have hlt := cycleRank_opens_lt_of_coheight_eq_one Xm h.isProjectiveVariety_minus (r := 3)
    h.dim_minus (badLocusMinus fm fp).isClosed (badLocusMinus_ne_univ h)
    (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint E) hyA Um (compl_compl _).symm
  exact hUp ▸ hUm ▸ hlt

/-- A function `ℕ → ℕ` nonincreasing from `i₀` on drops strictly at only finitely many indices
of a set `s`, provided it drops strictly at every index of `s` from `i₀` on. -/
private theorem finite_of_succ_lt {f : ℕ → ℕ} {s : Set ℕ} {i₀ : ℕ}
    (hle : ∀ i, i₀ ≤ i → f (i + 1) ≤ f i) (hlt : ∀ i, i₀ ≤ i → i ∈ s → f (i + 1) < f i) :
    s.Finite := by
  have hanti := antitoneOn_nat_Ici_of_succ_le hle
  have hinj : StrictAntiOn f (s ∩ Set.Ici i₀) := fun i hi j hj hij =>
    (hanti (hi.2.trans i.le_succ) hj.2 hij).trans_lt (hlt i hi.2 hi.1)
  refine ((Set.finite_Iio i₀).union (Set.Finite.of_finite_image ((Set.finite_Iic (f i₀)).subset ?_)
    hinj.injOn)).subset fun i hi => (lt_or_ge i i₀).imp id fun h => ⟨hi, h⟩
  rintro _ ⟨i, hi, rfl⟩
  exact hanti (le_refl i₀) hi.2 hi.2

/-- In a step sequence, only finitely many steps `i` lose a prime divisor: the set of indices `i`
for which some prime divisor `E` of `X_i` has `ord_E`, transported to `k(X_{i+1})`, exceptional
over `X_{i+1}` is finite. -/
@[mmp "lem_oai4_cycle_rank_b"]
public theorem StepSequence.finite_setOf_exists_primeDivisor_isExceptionalValuation
    (S : StepSequence) :
    {i : ℕ | ∃ (E : MMP.Mori.PrimeDivisor (S.X i))
      (ξ : Valuation (S.X (i + 1)).functionField (WithZero (Multiplicative ℤ))),
      S.IsTransportedValuation i E.divisorialValuation ξ ∧
        MMP.Intersection.IsExceptionalValuation ℂ (S.sX (i + 1)) ξ}.Finite := by
  letI : ∀ i, (S.X i).Over (Spec (.of ℂ)) := fun i => ⟨S.sX i⟩
  haveI : ∀ i, MMP.IsComplexScheme (S.X i) := fun i =>
    isComplexScheme_of_isProjectiveVariety _ (S.isFourfoldStepDiagram i).isProjectiveVariety_minus
  have hstep (i : ℕ) := cycleRank_le_and_lt (S.isFourfoldStepDiagram i)
  exact finite_of_succ_lt (f := fun i => cycleRank (S.X i) 3) (i₀ := 0) (fun i _ => (hstep i).1)
    fun i _ ⟨E, ξ, hξ, hex⟩ => (hstep i).2
      ⟨E, (S.isFourfoldStepDiagram i).support_subset_badLocusMinus E ⟨ξ, hξ, hex⟩⟩

/-- The second cycle rank `ρ_2(X_i)` of the `i`-th model of a step sequence. -/
private def secondCycleRank (S : StepSequence) (i : ℕ) : ℕ :=
  letI : (S.X i).Over (Spec (.of ℂ)) := ⟨S.sX i⟩
  haveI := isComplexScheme_of_isProjectiveVariety (S.X i)
    (S.isFourfoldStepDiagram i).isProjectiveVariety_minus
  cycleRank (S.X i) 2

/-- At a small step with no positive-side bad surface, the second cycle rank does not increase,
and it drops strictly when the step has a negative-side bad surface. -/
private theorem secondCycleRank_succ (S : StepSequence) (i : ℕ)
    (hm : IsSmallMorphism (S.sX i) (S.sZ i) (S.f i))
    (hp : ∀ V : IrreducibleCloseds (S.X (i + 1)), ¬ IsPositiveBadSurface (S.f i) (S.fp i) V) :
    secondCycleRank S (i + 1) ≤ secondCycleRank S i ∧
      ((∃ V : IrreducibleCloseds (S.X i), IsNegativeBadSurface (S.f i) (S.fp i) V) →
        secondCycleRank S (i + 1) < secondCycleRank S i) := by
  have hD := S.isFourfoldStepDiagram i
  have hD' := S.isFourfoldStepDiagram (i + 1)
  letI : (S.X i).Over (Spec (.of ℂ)) := ⟨S.sX i⟩
  letI : (S.X (i + 1)).Over (Spec (.of ℂ)) := ⟨S.sX (i + 1)⟩
  haveI := isComplexScheme_of_isProjectiveVariety (S.X i) hD.isProjectiveVariety_minus
  haveI := isComplexScheme_of_isProjectiveVariety (S.X (i + 1)) hD'.isProjectiveVariety_minus
  haveI : LocallyOfFiniteType (S.sX i) :=
    hD.isProjectiveVariety_minus.toIsVariety.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (S.sX (i + 1)) :=
    hD.isProjectiveVariety_plus.toIsVariety.toLocallyOfFiniteType
  set V := commonBiregularLocus (S.f i) (S.fp i)
  have hb := (isBiregular_and_isBiregular_iff (fm := S.f i) (fp := S.fp i) (V := V)).mpr le_rfl
  haveI : IsIso (S.f i ∣_ V) := hb.1
  haveI : IsIso (S.fp i ∣_ V) := hb.2
  let Um := S.f i ⁻¹ᵁ V
  let Up := S.fp i ⁻¹ᵁ V
  letI : Um.toScheme.Over (Spec (.of ℂ)) := ⟨Um.ι ≫ S.sX i⟩
  haveI : Um.ι.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  letI : Up.toScheme.Over (Spec (.of ℂ)) := ⟨Up.ι ≫ S.sX (i + 1)⟩
  haveI : Up.ι.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  let φ : Um.toScheme ≅ Up.toScheme := asIso (S.f i ∣_ V) ≪≫ (asIso (S.fp i ∣_ V)).symm
  have hφ : φ.hom ≫ (Up.toScheme ↘ Spec (.of ℂ)) = Um.toScheme ↘ Spec (.of ℂ) := by
    change φ.hom ≫ Up.ι ≫ S.sX (i + 1) = Um.ι ≫ S.sX i
    simp only [φ, Iso.trans_hom, asIso_hom, Iso.symm_hom, asIso_inv, Category.assoc]
    rw [← hD.comp_eq_plus, ← hD.comp_eq_minus, ← morphismRestrict_ι_assoc,
      ← morphismRestrict_ι_assoc, IsIso.inv_hom_id_assoc]
  have heq : cycleRank Um.toScheme 2 = cycleRank Up.toScheme 2 :=
    (cycleRank_eq_of_iso φ hφ).2.2.2 2
  have hUm : (Um : Set (S.X i)) = (badLocusMinus (S.f i) (S.fp i) : Set (S.X i))ᶜ :=
    (compl_compl _).symm
  have hUp : (Up : Set (S.X (i + 1))) = (badLocusPlus (S.f i) (S.fp i) : Set (S.X (i + 1)))ᶜ :=
    (compl_compl _).symm
  have hdimP : topologicalKrullDim (badLocusPlus (S.f i) (S.fp i) : Set (S.X (i + 1))) < (2 : ℕ) :=
    (topologicalKrullDim_le_one (S.sX (i + 1)) hD.dim_plus (badLocusPlus _ _).isClosed
      hD.topologicalKrullDim_badLocusPlus_le_two fun W hW h2 => hp W ⟨hW, h2⟩).trans_lt
        (by decide)
  have hPlus : cycleRank Up.toScheme 2 = secondCycleRank S (i + 1) :=
    cycleRank_eq_of_topologicalKrullDim_lt (S.X (i + 1)) hD'.isProjectiveVariety_minus
      (badLocusPlus _ _).isClosed hdimP Up hUp
  have hdimM := hD.topologicalKrullDim_badLocusMinus_le_two hm
  by_cases hneg : ∃ W : IrreducibleCloseds (S.X i), IsNegativeBadSurface (S.f i) (S.fp i) W
  · obtain ⟨W, hWsub, hWdim⟩ := hneg
    obtain ⟨Z, hZ, hZdim⟩ := exists_mem_irreducibleComponents hdimM W hWsub hWdim
    have hlt : cycleRank Um.toScheme 2 < secondCycleRank S i :=
      cycleRank_opens_lt_of_mem_irreducibleComponents (S.X i) hD.isProjectiveVariety_minus
        (badLocusMinus _ _).isClosed (r := 2) hdimM hZ hZdim Um hUm
    have : secondCycleRank S (i + 1) < secondCycleRank S i := by rwa [← hPlus, ← heq]
    exact ⟨this.le, fun _ => this⟩
  · have hdimM' : topologicalKrullDim (badLocusMinus (S.f i) (S.fp i) : Set (S.X i)) < (2 : ℕ) :=
      (topologicalKrullDim_le_one (S.sX i) hD.dim_minus (badLocusMinus _ _).isClosed
        hdimM fun W hW h2 => hneg ⟨W, hW, h2⟩).trans_lt (by decide)
    have hMinus : cycleRank Um.toScheme 2 = secondCycleRank S i :=
      cycleRank_eq_of_topologicalKrullDim_lt (S.X i) hD.isProjectiveVariety_minus
        (badLocusMinus _ _).isClosed hdimM' Um hUm
    exact ⟨by rw [← hPlus, ← heq, hMinus], fun h => absurd h hneg⟩

/-- In a step sequence small from the index `i₀` in which no step `i ≥ i₀` has a positive-side
bad surface, only finitely many steps have a negative-side bad surface: the set of indices `i`
such that `W_i⁻` contains an irreducible closed subset of dimension two is finite. -/
@[mmp "lem_oai4_cycle_rank_c"]
public theorem StepSequence.finite_setOf_exists_isNegativeBadSurface (S : StepSequence) {i₀ : ℕ}
    (hS : S.IsSmallFrom i₀)
    (hp : ∀ i, i₀ ≤ i → ∀ V : IrreducibleCloseds (S.X (i + 1)),
      ¬ IsPositiveBadSurface (S.f i) (S.fp i) V) :
    {i : ℕ | ∃ V : IrreducibleCloseds (S.X i), IsNegativeBadSurface (S.f i) (S.fp i) V}.Finite :=
  finite_of_succ_lt (f := secondCycleRank S)
    (fun i hi => (secondCycleRank_succ S i (hS i hi) (hp i hi)).1)
    fun i hi => (secondCycleRank_succ S i (hS i hi) (hp i hi)).2

end CycleRank

/-! ### Divisorial valuations on open subschemes -/

/-- The divisorial valuation of a prime divisor `E'` of an open subscheme `V ⊆ Y` is that of its
closure `E` in `Y`, through the identification `k(Y) ≅ k(V)`. -/
private theorem divisorialValuation_primeDivisorMap {Y V : Scheme.{u}} [IsIntegral Y]
    [IsIntegral V] [IsLocallyNoetherian Y] [IsLocallyNoetherian V] [IsNormal Y] [IsNormal V]
    (j : V ⟶ Y) [IsOpenImmersion j] [IsDominant j] (E' : MMP.Mori.PrimeDivisor V) :
    MMP.Mori.PrimeDivisor.divisorialValuation (OpenWeilRestriction.primeDivisorMap j E') =
      E'.divisorialValuation.comap (functionFieldMap j) := by
  ext g
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  have hg' : functionFieldMap j g ≠ 0 := (map_ne_zero _).2 hg
  rw [Valuation.comap_apply, MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg,
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg',
    MMP.Positivity.ord_functionFieldMap_of_isIso j E' _
      (OpenWeilRestriction.genericPoint_primeDivisorMap j E').symm]

/-! ### Rational forms along birational morphisms -/

section Forms

variable {k : Type u} [Field k] [PerfectField k] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  [IsIntegral X] [IsIntegral Y] [LocallyOfFiniteType sX] (f : Y ⟶ X) [IsDominant f]

/-- Along a birational morphism every rational `1`-canonical form is a pull-back. -/
private theorem exists_pullbackRationalPluriForms_eq
    (hbij : Function.Bijective (functionFieldMap f)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d)
    (ω : RationalPluriForms (f ≫ sX) d 1) :
    ∃ τ : RationalPluriForms sX d 1, pullbackRationalPluriForms sX f τ = ω := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  obtain ⟨ω', hω⟩ := exists_isPullbackGenerator_of_bijective sX f hbij hd
  obtain ⟨g, hg⟩ := hbij.2
    ((ZTensorPower.basis (basisOfSpanSingleton hω.2.1 hω.2.2) 1).repr ω ())
  refine ⟨g • ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) 1 (), ?_⟩
  change pullbackForms (K := X.functionField) (K' := Y.functionField) 1 _ = ω
  rw [pullbackForms_eq hω, pullbackFormsAlong]
  simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply,
    Finsupp.single_eq_same, smul_eq_mul, mul_one]
  change functionFieldMap f g • _ = ω
  rw [hg]
  exact basis_unit_repr_smul _ ω

/-- The pull-back of the zero form is zero. -/
private theorem pullbackRationalPluriForms_zero
    (hbij : Function.Bijective (functionFieldMap f)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d)
    {m : ℤ} : pullbackRationalPluriForms sX f (0 : RationalPluriForms sX d m) = 0 := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  obtain ⟨ω', hω⟩ := exists_isPullbackGenerator_of_bijective sX f hbij hd
  change pullbackForms (K := X.functionField) (K' := Y.functionField) m 0 = 0
  rw [pullbackForms_eq hω, pullbackFormsAlong]
  simp

/-- The pull-back of a nonzero rational form along a birational morphism is nonzero. -/
private theorem pullbackRationalPluriForms_ne_zero
    (hbij : Function.Bijective (functionFieldMap f)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d)
    {m : ℤ} {τ : RationalPluriForms sX d m} (hτ : τ ≠ 0) :
    pullbackRationalPluriForms sX f τ ≠ 0 := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX f hbij hd
  intro h0
  have h0' : pullbackFormsAlong hω m τ = 0 := (pullbackForms_eq hω m τ) ▸ h0
  have h1 : algebraMap X.functionField Y.functionField
      ((ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m).repr τ ()) = 0 := by
    rw [← repr_pullbackFormsAlong hω m τ, h0']
    simp
  exact repr_ne_zero_of_ne_zero _ hτ ((map_eq_zero_iff _ (algebraMap _ _).injective).mp h1)

end Forms

/-! ### Valuations over a proper model -/

section ValuationLift

/-- A valuation `ξ'` of `ℂ(X')` restricting on `ℂ(Z)` to the valuation of a divisor `D` over a
model `X ⟶ Z` is a divisor of the function field `ℂ(X')`: it is `ord_E` on the normal variety
`D.Y`, transported along `ℂ(X') ≅ ℂ(Z) ≅ ℂ(D.Y)`. -/
private theorem isDivisorOfFunctionField_of_comap_eq
    {X X' Z : Scheme.{0}} [IsIntegral X] [IsIntegral X'] [IsIntegral Z]
    {sZ : Z ⟶ Spec (.of ℂ)} (g : X ⟶ Z) (g' : X' ⟶ Z) [IsDominant g] [IsDominant g']
    (hg : IsBirationalMorphism g) (hg' : IsBirationalMorphism g')
    (D : DivisorOver ℂ (g ≫ sZ)) (ξ' : Valuation X'.functionField (WithZero (Multiplicative ℤ)))
    (h : ξ'.comap (functionFieldMap g') = D.valuation.comap (functionFieldMap g)) :
    MMP.Flips.IsDivisorOfFunctionField ℂ (g' ≫ sZ) ξ' := by
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  have hY : IsNormalVariety ℂ ((D.f ≫ g) ≫ sZ) := by
    simpa only [Category.assoc] using D.isNormalVariety
  have hbij : Function.Bijective (functionFieldMap (D.f ≫ g)) := by
    have : ⇑(functionFieldMap (D.f ≫ g)) = functionFieldMap D.f ∘ functionFieldMap g := by
      funext t
      exact (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply D.f g t).symm
    rw [this]
    exact D.isBirationalMorphism.functionFieldMap_bijective.comp hg.functionFieldMap_bijective
  refine ⟨D.Y, (D.f ≫ g) ≫ sZ, hY, D.E, ?_⟩
  letI := MMP.Mori.functionFieldAlgebra sZ
  letI := MMP.Mori.functionFieldAlgebra (g' ≫ sZ)
  letI := MMP.Mori.functionFieldAlgebra ((D.f ≫ g) ≫ sZ)
  let eP := MMP.Mori.functionFieldAlgEquiv sZ g' hg'.functionFieldMap_bijective
  let eY := MMP.Mori.functionFieldAlgEquiv sZ (D.f ≫ g) hbij
  refine ⟨eP.symm.trans eY, ?_⟩
  ext t
  obtain ⟨s, rfl⟩ := hg'.functionFieldMap_bijective.2 t
  have hs := congrArg (fun v => v s) h
  simp only [Valuation.comap_apply] at hs
  have h1 : eP.symm (functionFieldMap g' s) = s := eP.symm_apply_apply s
  change ξ' (functionFieldMap g' s) = D.E.divisorialValuation (eY (eP.symm (functionFieldMap g' s)))
  rw [h1, hs]
  change D.E.divisorialValuation (functionFieldMap D.f (functionFieldMap g s)) = _
  rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply D.f g s]
  rfl

/-- **The centre on a proper model.** Let `g : X ⟶ Z` and `g' : X' ⟶ Z` be dominant morphisms of
integral schemes with `g'` proper, and `D` a divisor over `X`. A valuation `ξ'` of `k(X')`
restricting on `k(Z)` to `ord_D` dominates the local ring of some point of `X'`: the valuation
ring of `ξ'` dominates `𝒪_{Z, g(c_X(D))}`, and the valuative criterion for `g'` lifts
`Spec 𝒪_{ξ'} ⟶ Z` to `X'`. -/
private theorem exists_dominated_point_of_comap_eq {k : Type} [Field k]
    {X X' Z : Scheme.{0}} [IsIntegral X] [IsIntegral X'] [IsIntegral Z] {sX : X ⟶ Spec (.of k)}
    (g : X ⟶ Z) (g' : X' ⟶ Z) [IsDominant g] [IsDominant g'] (hgp' : IsProper g')
    (D : DivisorOver k sX) (ξ' : Valuation X'.functionField (WithZero (Multiplicative ℤ)))
    (h : ξ'.comap (functionFieldMap g') = D.valuation.comap (functionFieldMap g)) :
    ∃ x : X', (∀ a : X'.presheaf.stalk x, ξ' (algebraMap _ X'.functionField a) ≤ 1) ∧
      ∀ a ∈ IsLocalRing.maximalIdeal (X'.presheaf.stalk x),
        ξ' (algebraMap _ X'.functionField a) < 1 := by
  set y := D.f D.E.genericPoint
  set z := g y
  have hw : ∀ b : Z.presheaf.stalk z,
      ξ' (functionFieldMap g' (algebraMap _ Z.functionField b)) =
        D.valuation (algebraMap _ X.functionField ((g.stalkMap y).hom b)) := by
    intro b
    have := congrArg (fun v => v (algebraMap _ Z.functionField b)) h
    simp only [Valuation.comap_apply] at this
    rw [this, functionFieldMap_algebraMap_stalk g y b]
  let R := ξ'.valuationSubring
  let φ : Z.presheaf.stalk z →+* R :=
    ((functionFieldMap g').comp (algebraMap (Z.presheaf.stalk z) Z.functionField)).codRestrict R
      fun b => (ξ'.mem_valuationSubring_iff _).2 (by
        rw [RingHom.comp_apply, hw]
        exact MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D y rfl _)
  have hgen : genericPoint Z ⤳ z := (genericPoint_spec Z).specializes trivial
  have hex : ValuativeCriterion.Existence g' := by
    have h : @IsProper _ _ g' := hgp'
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1.existence
  let S : ValuativeCommSq g' :=
    { R := R
      K := X'.functionField
      i₁ := X'.fromSpecStalk (genericPoint X')
      i₂ := Spec.map (CommRingCat.ofHom φ) ≫ Z.fromSpecStalk z
      commSq := ⟨by
        rw [← functionFieldMap_fromSpecStalk g',
          ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk hgen, ← Category.assoc,
          ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
        rfl⟩ }
  obtain ⟨⟨l, hl₁, -⟩⟩ := (hex S).exists_lift
  have hl₁' : Spec.map (CommRingCat.ofHom (algebraMap R X'.functionField)) ≫ l =
      X'.fromSpecStalk (genericPoint X') := hl₁
  set x := l (IsLocalRing.closedPoint R)
  have hx : genericPoint X' ⤳ x := (genericPoint_spec X').specializes trivial
  let f := Scheme.stalkClosedPointTo l
  have hf : f ≫ CommRingCat.ofHom (algebraMap R X'.functionField) =
      X'.presheaf.stalkSpecializes hx := by
    apply Spec.map_injective
    apply (cancel_mono (X'.fromSpecStalk x)).mp
    rw [Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk, hl₁',
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  have hfa : ∀ a : X'.presheaf.stalk x,
      algebraMap _ X'.functionField a = ((f.hom a : R) : X'.functionField) := fun a =>
    (congrArg (fun q => q.hom a) hf).symm
  refine ⟨x, fun a => ?_, fun a ha => ?_⟩
  · rw [hfa]
    exact (f.hom a).2
  · rw [hfa]
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp
      (fun hu => (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit f.hom a hu))

/-- Over a proper birational model `X' ⟶ Z` of a normal variety, a valuation `ξ'` of `ℂ(X')`
restricting on `ℂ(Z)` to the valuation of a divisor over another model `X ⟶ Z` is realized by a
proper divisor over `X'`. -/
private theorem exists_properDivisorOver_valuation_eq_of_comap_eq
    {X X' Z : Scheme.{0}} [IsIntegral X] [IsIntegral X'] [IsIntegral Z]
    {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    (hX' : IsNormalVariety ℂ sX') (g : X ⟶ Z) (g' : X' ⟶ Z) [IsDominant g] [IsDominant g']
    (hg : IsBirationalMorphism g) (hg' : IsBirationalMorphism g') (hgp' : IsProper g')
    (hc : g ≫ sZ = sX) (hc' : g' ≫ sZ = sX') (D : DivisorOver ℂ sX)
    (ξ' : Valuation X'.functionField (WithZero (Multiplicative ℤ)))
    (h : ξ'.comap (functionFieldMap g') = D.valuation.comap (functionFieldMap g)) :
    ∃ D' : DivisorOver ℂ sX', IsProper D'.f ∧ D'.valuation = ξ' := by
  obtain ⟨x, h1, h2⟩ := exists_dominated_point_of_comap_eq g g' hgp' D ξ' h
  haveI : AlgebraicGeometry.IsVariety ℂ sX' := hX'.1
  have hξ : MMP.Flips.IsDivisorOfFunctionField ℂ sX' ξ' := by
    subst hc hc'
    exact isDivisorOfFunctionField_of_comap_eq g g' hg hg' D ξ' h
  obtain ⟨D', -, hv, -⟩ :=
    MMP.Flips.exists_properDivisorOver_isProjective_of_dominates sX' hξ x h1 h2
  exact ⟨D'.toDivisorOver, D'.isProper, hv⟩

end ValuationLift

/-! ### Birational invariance of discrepancies -/

section Crepant

/-- Pulling valuations back along a surjective ring map is injective. -/
private theorem comap_injective_of_surjective {R S : Type*} [CommRing R] [CommRing S]
    {g : R →+* S} (hg : Function.Surjective g)
    {v w : Valuation S (WithZero (Multiplicative ℤ))} (h : v.comap g = w.comap g) : v = w := by
  ext t
  obtain ⟨s, rfl⟩ := hg t
  exact congrArg (fun u : Valuation R (WithZero (Multiplicative ℤ)) => u s) h

/-- The valuation of a prime divisor of `X`, regarded as a divisor over `X`. -/
private theorem valuation_ofPrimeDivisor {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX)
    (P : MMP.Mori.PrimeDivisor X) :
    (DivisorOver.ofPrimeDivisor k hX P).valuation = P.divisorialValuation := by
  ext t
  change P.divisorialValuation (functionFieldMap (𝟙 X) t) = _
  rw [functionFieldMap_id_apply]

/-- An open immersion of nonempty irreducible schemes is birational. -/
private theorem isBirationalMorphism_of_isOpenImmersion {W Y : Scheme.{0}} [IrreducibleSpace W]
    [IrreducibleSpace Y] [Nonempty W] (j : W ⟶ Y) [IsOpenImmersion j] :
    IsBirationalMorphism j := by
  let U : W.Opens := ⊤
  let V' : Y.Opens := (U.ι ≫ j).opensRange
  have hle : U ≤ j ⁻¹ᵁ V' := fun x hx => ⟨⟨x, hx⟩, rfl⟩
  obtain ⟨w⟩ := ‹Nonempty W›
  refine MMP.Flips.isBirationalMorphism_of_isIso_resLE j U V' ⟨w, trivial⟩
    ⟨_, ⟨⟨w, trivial⟩, rfl⟩⟩ hle ?_
  have e : j.resLE V' U hle = (U.ι ≫ j).isoOpensRange.hom := by
    rw [← cancel_mono V'.ι, Scheme.Hom.resLE_comp_ι, Scheme.Hom.isoOpensRange_hom_ι]
  rw [e]
  infer_instance

/-- `functionFieldMap` only depends on the morphism. -/
private theorem functionFieldMap_congr {A C : Scheme.{0}} [IsIntegral A] [IsIntegral C]
    {a b : A ⟶ C} (hab : a = b) [IsDominant a] [IsDominant b] (t : C.functionField) :
    functionFieldMap a t = functionFieldMap b t := by
  subst hab
  rfl

/-- **Crepant invariance**, with the structure morphism of the source given up to equality: if
`ΔY` is the crepant boundary of `(X, Δ)` along a birational `φ : Y ⟶ X`, divisors over `Y` and
over `X` with corresponding valuations have the same discrepancies. -/
private theorem isDiscrepancy_iff_of_crepant {X Y : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)} {n : ℕ} {KX : Divisor X} {Δ : QDivisor X}
    {KY : Divisor Y} {ΔY : QDivisor Y} (hP : MMP.Mori.IsPair sX Δ)
    (hKX : KX.IsCanonicalDivisor sX n) (φ : Y ⟶ X) [IsDominant φ] (hs : φ ≫ sX = sY)
    (hY : IsNormalVariety ℂ sY) (hφ : IsBirationalMorphism φ) (hKY : KY.IsCanonicalDivisor sY n)
    (hcb : ∀ (F : MMP.Mori.PrimeDivisor Y) (D : DivisorOver ℂ sX), D.valuation = F.valuationOver φ →
      IsDiscrepancy sX n KX Δ D (-ΔY.coeff F))
    (E : DivisorOver ℂ sY) (E' : DivisorOver ℂ sX)
    (hv : E'.valuation = E.valuation.comap (functionFieldMap φ)) (a : ℚ) :
    IsDiscrepancy sY n KY ΔY E a ↔ IsDiscrepancy sX n KX Δ E' a := by
  subst hs
  have hcb' : IsCrepantBoundary sX n KX Δ φ hY hφ ΔY := fun F => hcb F _ rfl
  exact (IsPair.isDiscrepancy_iff_of_crepant hP φ hY hφ hKX hKY (Or.inl hcb')).2 E E' hv a

end Crepant

/-! ### The step diagram -/

section StepDiagram

variable {Xm Xp Z : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
  [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]
  {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
  {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}

/-- **A step extracts no divisor.** Every prime divisor `P` of `X⁺` has a prime divisor `P⁻` of
`X⁻` with the same valuation on `k(Z)`, both lying over the generic point of one prime divisor
`Q` of `Z`, and the strict transform `(f⁺)⁻¹_* f⁻_* D` has the coefficient of `P⁻` in `D` at
`P`. -/
private theorem exists_primeDivisor (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp)
    (P : MMP.Mori.PrimeDivisor Xp) :
    haveI : IsIntegral Z := h.isNormalVariety_target.1.toIsIntegral
    haveI := h.isBirationalMorphism_minus.isDominant
    haveI := h.isBirationalMorphism_plus.isDominant
    ∃ (Pm : MMP.Mori.PrimeDivisor Xm) (Q : MMP.Mori.PrimeDivisor Z),
      Pm.valuationOver fm = P.valuationOver fp ∧ fm Pm.genericPoint = Q.genericPoint ∧
      fp P.genericPoint = Q.genericPoint ∧
      ∀ {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R Xm),
        (flipTransform fm fp D).coeff P = D.coeff Pm := by
  haveI : IsIntegral Z := h.isNormalVariety_target.1.toIsIntegral
  haveI := h.isBirationalMorphism_minus.isDominant
  haveI := h.isBirationalMorphism_plus.isDominant
  haveI : IsProper fm := isProper_of_isProjectiveMorphism fm h.isProjectiveMorphism_minus
  obtain ⟨Pm, Q, hv, hPmQ, hPQ⟩ := exists_primeDivisor_valuationOver_eq_of_isSmallMorphism
    h.isNormalVariety_target h.isBirationalMorphism_minus h.isSmallMorphism_plus P
  have hPmQ' := map_genericPoint_eq_of_image_eq Pm Q hPmQ
  have hPQ' := map_genericPoint_eq_of_image_eq P Q hPQ
  obtain ⟨Pm', hPm', hD⟩ := exists_eq_genericPoint_flipTransform_apply
    h.isBirationalMorphism_minus h.isSmallMorphism_plus P Pm.genericPoint (hPmQ'.trans hPQ'.symm)
  obtain rfl : Pm = Pm' := AlgebraicGeometry.PrimeDivisor.genericPoint_injective hPm'
  exact ⟨Pm, Q, hv, hPmQ', hPQ', hD⟩

/-- **The canonical divisor of `X⁺`.** The strict transform `K⁺ = (f⁺)⁻¹_* f⁻_* K⁻` of a
canonical divisor of `X⁻` is a canonical divisor of `X⁺`: if `K⁻ = div(f⁻^* τ)` for a rational top
form `τ` on `Z`, then `K⁺ = div(f⁺^* τ)`, since `f^±` are local isomorphisms over the generic
points of the prime divisors of `Z` that the prime divisors of `X⁺` lie over. -/
private theorem isCanonicalDivisor_flipTransform (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp) :
    Divisor.IsCanonicalDivisor sXp 4 (flipTransform fm fp K) := by
  haveI : IsIntegral Z := h.isNormalVariety_target.1.toIsIntegral
  haveI := h.isBirationalMorphism_minus.isDominant
  haveI := h.isBirationalMorphism_plus.isDominant
  haveI : IsNormal Z := h.isNormalVariety_target.2
  haveI : LocallyOfFiniteType sZ := h.isNormalVariety_target.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have hbm := h.isBirationalMorphism_minus
  have hbp := h.isBirationalMorphism_plus
  obtain ⟨m, hK⟩ := h.isCanonicalDivisor
  obtain rfl : m = 4 := by exact_mod_cast hK.topologicalKrullDim_eq.symm.trans h.dim_minus
  have hXp := h.isNormalVariety_plus
  haveI : LocallyOfFiniteType sXp := hXp.1.toLocallyOfFiniteType
  obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety sXp hXp (n := 4)
    (by exact_mod_cast h.dim_plus)
  obtain ⟨ω, hω0, hω⟩ :=
    MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq h.isNormalVariety_minus hK
  haveI : LocallyOfFiniteType sXm := h.isNormalVariety_minus.1.toLocallyOfFiniteType
  have hdm := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sXm) (d := 4)
    (by exact_mod_cast h.dim_minus)
  have hcm := h.comp_eq_minus
  have hcp := h.comp_eq_plus
  subst hcm hcp
  have hdZ : (letI := functionFieldAlgebra sZ; Algebra.trdeg ℂ Z.functionField).toNat = 4 := by
    rwa [trdeg_functionField_eq_of_bijective sZ fm hbm.functionFieldMap_bijective]
  obtain ⟨τ, hτ⟩ := exists_pullbackRationalPluriForms_eq sZ fm hbm.functionFieldMap_bijective hdZ ω
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    exact hω0 (hτ.symm.trans (pullbackRationalPluriForms_zero sZ fm hbm.functionFieldMap_bijective
      hdZ))
  have hτp0 := pullbackRationalPluriForms_ne_zero sZ fp hbp.functionFieldMap_bijective hdZ hτ0
  have hdiv : divisorOfForm (pullbackRationalPluriForms sZ fp τ) = flipTransform fm fp K := by
    ext P
    obtain ⟨Pm, Q, -, hPmQ, hPQ, hc⟩ := exists_primeDivisor h P
    change P.ordForm _ = (flipTransform fm fp K).coeff P
    haveI := isIso_stalkMap_of_map_eq_genericPoint hbp hPQ
    haveI := isIso_stalkMap_of_map_eq_genericPoint hbm hPmQ
    rw [hc K, MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso fp
      hbp.functionFieldMap_bijective hdZ P Q hPQ τ,
      ← MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso fm
        hbm.functionFieldMap_bijective hdZ Pm Q hPmQ τ, hτ, hω]
  have hle := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hXp hK₀ hτp0
  rw [one_smul, hdiv] at hle
  exact hK₀.of_linearlyEquivalent hle

/-- The pair `(X⁺, B⁺)` of a step diagram with `(X⁻, B⁻)` a pair. -/
private theorem isPair_flipTransform (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp)
    (hB : MMP.Fourfold.IsPair sXm B) : MMP.Fourfold.IsPair sXp (flipTransform fm fp B) := by
  refine ⟨hB.isAlgClosed, hB.charZero, ⟨h.isNormalVariety_plus, 4, _,
    isCanonicalDivisor_flipTransform h, h.isQCartier_plus⟩, fun P => ?_⟩
  obtain ⟨Pm, -, -, -, -, hc⟩ := exists_primeDivisor h P
  rw [hc B]
  exact h.nonneg Pm

/-- Every divisor `D⁺` over `X⁺` (with proper structure morphism) has a counterpart `D⁻` over
`X⁻`, proper, whose valuation agrees with that of `D⁺` on `k(Z)`. -/
private theorem exists_properDivisorOver_minus (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp)
    (D : DivisorOver ℂ sXp) :
    haveI : IsIntegral Z := h.isNormalVariety_target.1.toIsIntegral
    haveI := h.isBirationalMorphism_minus.isDominant
    haveI := h.isBirationalMorphism_plus.isDominant
    ∃ D' : DivisorOver ℂ sXm, IsProper D'.f ∧
      D.valuation.comap (functionFieldMap fp) = D'.valuation.comap (functionFieldMap fm) := by
  haveI : IsIntegral Z := h.isNormalVariety_target.1.toIsIntegral
  haveI := h.isBirationalMorphism_minus.isDominant
  haveI := h.isBirationalMorphism_plus.isDominant
  let e : Z.functionField ≃+* Xm.functionField :=
    RingEquiv.ofBijective (functionFieldMap fm)
      h.isBirationalMorphism_minus.functionFieldMap_bijective
  have hξ : ((D.valuation.comap (functionFieldMap fp)).comap e.symm.toRingHom).comap
      (functionFieldMap fm) = D.valuation.comap (functionFieldMap fp) := by
    ext t
    simp only [Valuation.comap_apply]
    congr 2
    exact e.symm_apply_apply t
  obtain ⟨D', hD'p, hD'v⟩ := exists_properDivisorOver_valuation_eq_of_comap_eq
    h.isNormalVariety_minus fp fm h.isSmallMorphism_plus.isBirationalMorphism
    h.isBirationalMorphism_minus (isProper_of_isProjectiveMorphism fm h.isProjectiveMorphism_minus)
    h.comp_eq_plus h.comp_eq_minus D _ hξ
  exact ⟨D', hD'p, by rw [hD'v, hξ]⟩

/-- On an open `V ⊆ X⁺` mapped into `X⁻` over `Z`, the restriction of the strict transform of
`B` is the crepant boundary of `(X⁻, B)`. -/
private theorem isDiscrepancy_restrictOpen_flipTransform
    (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp) (hB : MMP.Fourfold.IsPair sXm B)
    (hKm : K.IsCanonicalDivisor sXm 4) (V : Xp.Opens) [Nonempty V] [IsDominant V.ι]
    (φ : V.toScheme ⟶ Xm) [IsDominant φ] (hφ : φ ≫ fm = V.ι ≫ fp)
    (F : MMP.Mori.PrimeDivisor V.toScheme) (D : DivisorOver ℂ sXm)
    (hD : D.valuation = F.valuationOver φ) :
    IsDiscrepancy sXm 4 K B D (-((flipTransform fm fp B).restrictOpen V).coeff F) := by
  haveI : IsIntegral Z := h.isNormalVariety_target.1.toIsIntegral
  haveI := h.isBirationalMorphism_minus.isDominant
  haveI := h.isBirationalMorphism_plus.isDominant
  haveI : IsDominant (φ ≫ fm) := inferInstance
  haveI : IsDominant (V.ι ≫ fp) := inferInstance
  have hvF : (F.valuationOver φ).comap (functionFieldMap fm) =
      MMP.Mori.PrimeDivisor.valuationOver (OpenWeilRestriction.primeDivisorMap V.ι F) fp := by
    ext t
    simp only [MMP.Mori.PrimeDivisor.valuationOver, Valuation.comap_apply]
    rw [divisorialValuation_primeDivisorMap, Valuation.comap_apply,
      MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
      MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
      functionFieldMap_congr hφ]
  rw [DivisorWithCoeffs.coeff_restrictOpen]
  obtain ⟨Pm, -, hPm, -, -, hcoef⟩ := exists_primeDivisor h
    (OpenWeilRestriction.primeDivisorMap V.ι F)
  rw [hcoef B]
  obtain ⟨c₀, hc₀⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hB.isPair hKm
    (DivisorOver.ofPrimeDivisor ℂ h.isNormalVariety_minus Pm)
  obtain ⟨cD, hcD⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hB.isPair hKm D
  have hvD :
      D.valuation = (DivisorOver.ofPrimeDivisor ℂ h.isNormalVariety_minus Pm).valuation := by
    rw [valuation_ofPrimeDivisor, hD]
    apply comap_injective_of_surjective h.isBirationalMorphism_minus.functionFieldMap_bijective.2
    rw [hvF, ← hPm]
    rfl
  have e := MMP.Threefold.Mori.ModelIndependence.isDiscrepancy_eq_of_center_eq hvD
    (MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq h.isNormalVariety_minus hvD)
    hcD hc₀
  rw [← hc₀.eq_neg_coeff_of_ofPrimeDivisor h.isNormalVariety_minus, ← e]
  exact hcD

/-- Off the bad locus the log discrepancies of corresponding divisors agree. -/
private theorem eq_of_not_subset_badLocusPlus (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp)
    (hB : MMP.Fourfold.IsPair sXm B)
    (Dp : DivisorOver ℂ sXp) (Dm : DivisorOver ℂ sXm)
    (hv : haveI : IsIntegral Z := h.isNormalVariety_target.1.toIsIntegral
      haveI := h.isBirationalMorphism_minus.isDominant
      haveI := h.isBirationalMorphism_plus.isDominant
      Dp.valuation.comap (functionFieldMap fp) = Dm.valuation.comap (functionFieldMap fm))
    (hc : ¬ (Dp.center : Set Xp) ⊆ badLocusPlus fm fp)
    {n n' : ℕ} {ap am : ℝ}
    (hap : MMP.Intersection.IsLogDiscrepancy sXp n
      (QDivisor.toRDivisor (flipTransform fm fp B)) Dp ap)
    (ham : MMP.Intersection.IsLogDiscrepancy sXm n' (QDivisor.toRDivisor B) Dm am) :
    am = ap := by
  haveI : IsIntegral Z := h.isNormalVariety_target.1.toIsIntegral
  haveI := h.isBirationalMorphism_minus.isDominant
  haveI := h.isBirationalMorphism_plus.isDominant
  have hU : ((Dp.center : Set Xp) ∩ (fp ⁻¹ᵁ commonBiregularLocus fm fp : Set Xp)).Nonempty := by
    rw [Set.not_subset] at hc
    obtain ⟨x, hx, hxW⟩ := hc
    refine ⟨x, hx, ?_⟩
    rw [coe_badLocusPlus, coe_badLocusBase] at hxW
    simpa using hxW
  -- dimensions and canonical divisors
  have hKp := isCanonicalDivisor_flipTransform h
  obtain ⟨mm, hKm⟩ := h.isCanonicalDivisor
  obtain rfl : mm = 4 := by exact_mod_cast hKm.topologicalKrullDim_eq.symm.trans h.dim_minus
  obtain rfl : n = 4 := by
    exact_mod_cast (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq hap).symm.trans
      h.dim_plus
  obtain rfl : n' = 4 := by
    exact_mod_cast (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ham).symm.trans
      h.dim_minus
  have hPp : IsPairWith sXp 4 (flipTransform fm fp K) (flipTransform fm fp B) :=
    ⟨h.isNormalVariety_plus, hKp, h.isQCartier_plus⟩
  obtain ⟨cp, hcp⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hPp.isPair hKp Dp
  obtain ⟨cm, hcm⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hB.isPair hKm Dm
  rw [((MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy hcp ap).mp hap).2,
    ((MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy hcm am).mp ham).2]
  suffices hcc : cm = cp by rw [hcc]
  -- restriction of `Dp` to `V⁺ = (f⁺)⁻¹(U)`
  obtain ⟨hY, hf, E', -, hval, hiff⟩ := DivisorOver.exists_restrict_isDiscrepancy_iff hPp Dp _ hU
  have hcE := (hiff cp).mp hcp
  -- the identification `V⁺ ≅ V⁻ ⊆ X⁻` over `U`
  haveI : Nonempty (fp ⁻¹ᵁ commonBiregularLocus fm fp) := ⟨⟨hU.choose, hU.choose_spec.2⟩⟩
  haveI : IsIso (fm ∣_ commonBiregularLocus fm fp) := isBiregular_commonBiregularLocus_left fm fp
  haveI : IsIso (fp ∣_ commonBiregularLocus fm fp) := isBiregular_commonBiregularLocus_right fm fp
  let φ : (fp ⁻¹ᵁ commonBiregularLocus fm fp).toScheme ⟶ Xm :=
    (fp ∣_ commonBiregularLocus fm fp) ≫ inv (fm ∣_ commonBiregularLocus fm fp) ≫
      (fm ⁻¹ᵁ commonBiregularLocus fm fp).ι
  have hφ : φ ≫ fm = (fp ⁻¹ᵁ commonBiregularLocus fm fp).ι ≫ fp := by
    simp only [φ, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
  have hs : φ ≫ sXm = (fp ⁻¹ᵁ commonBiregularLocus fm fp).ι ≫ sXp := by
    rw [← h.comp_eq_minus, ← h.comp_eq_plus, ← Category.assoc, hφ, Category.assoc]
  haveI : IsOpenImmersion φ := by dsimp only [φ]; infer_instance
  have hφb : IsBirationalMorphism φ := isBirationalMorphism_of_isOpenImmersion φ
  haveI : IsDominant φ := hφb.isDominant
  haveI : IsDominant (fp ⁻¹ᵁ commonBiregularLocus fm fp).ι :=
    Opens.isDominant_ι ((fp ⁻¹ᵁ commonBiregularLocus fm fp).isOpen.dense
      ⟨hU.choose, hU.choose_spec.2⟩)
  haveI : IsDominant (φ ≫ fm) := inferInstance
  haveI : IsDominant ((fp ⁻¹ᵁ commonBiregularLocus fm fp).ι ≫ fp) := inferInstance
  have hfm := h.isBirationalMorphism_minus.functionFieldMap_bijective.2
  have hvE : Dm.valuation = (DivisorOver.valuation (⟨_, Dp.f ∣_ _, hY, hf, E'⟩ :
      DivisorOver ℂ ((fp ⁻¹ᵁ commonBiregularLocus fm fp).ι ≫ sXp))).comap
        (functionFieldMap φ) := by
    apply comap_injective_of_surjective hfm
    rw [← hv, hval]
    ext t
    simp only [Valuation.comap_apply]
    rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
      MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
      functionFieldMap_congr hφ]
  have hcrep := isDiscrepancy_iff_of_crepant hB.isPair hKm φ hs hcE.1 hφb hcE.2.1
    (isDiscrepancy_restrictOpen_flipTransform h hB hKm _ φ hφ)
    ⟨_, Dp.f ∣_ _, hY, hf, E'⟩ Dm hvE cp
  exact hcm.eq (hcrep.mp hcE)

/-- **The comparison** `a(ξ; X⁻, B⁻) ≤ a(ξ; X⁺, B⁺)`. -/
private theorem le_of_isLogDiscrepancy (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp)
    (hB : MMP.Fourfold.IsPair sXm B)
    (Dp : DivisorOver ℂ sXp) (Dm : DivisorOver ℂ sXm) (hDm : IsProper Dm.f)
    (hv : haveI : IsIntegral Z := h.isNormalVariety_target.1.toIsIntegral
      haveI := h.isBirationalMorphism_minus.isDominant
      haveI := h.isBirationalMorphism_plus.isDominant
      Dp.valuation.comap (functionFieldMap fp) = Dm.valuation.comap (functionFieldMap fm))
    {n n' : ℕ} {ap am : ℝ}
    (hap : MMP.Intersection.IsLogDiscrepancy sXp n
      (QDivisor.toRDivisor (flipTransform fm fp B)) Dp ap)
    (ham : MMP.Intersection.IsLogDiscrepancy sXm n' (QDivisor.toRDivisor B) Dm am) :
    am ≤ ap := by
  by_cases hc : (Dp.center : Set Xp) ⊆ badLocusPlus fm fp
  · have ham' : IsValuationLogDiscrepancy sXm B Dm.valuation am := ⟨n', Dm, hDm, rfl, ham⟩
    have hap' : IsValuationLogDiscrepancy sXp (flipTransform fm fp B) Dp.valuation ap :=
      ⟨n, Dp, hap.2.1, rfl, hap⟩
    have hCm : MMP.Intersection.IsCentre ℂ sXm Dm.valuation Dm.center := ⟨Dm, hDm, rfl, rfl⟩
    have hCp : MMP.Intersection.IsCentre ℂ sXp Dp.valuation Dp.center :=
      ⟨Dp, hap.2.1, rfl, rfl⟩
    have hT := IsFourfoldStepDiagram.tfae_lt_and_centre_subset_badLocus h hv
      ham' hap' hCm hCp
    exact (show am < ap from (hT.out 3 1).mp hc).le
  · exact (eq_of_not_subset_badLocusPlus h hB Dp Dm hv hc hap ham).le

/-- The log discrepancy of a proper divisor over a pair exists. -/
private theorem exists_isLogDiscrepancy (hB : MMP.Fourfold.IsPair sXm B) (Dm : DivisorOver ℂ sXm)
    (hDm : IsProper Dm.f) :
    ∃ (n : ℕ) (am : ℝ), MMP.Intersection.IsLogDiscrepancy sXm n (QDivisor.toRDivisor B) Dm am := by
  obtain ⟨-, n, K', hK', -⟩ := hB.isPair
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hB.isPair hK' Dm
  exact ⟨n, _, MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc hDm⟩

end StepDiagram

section

variable {Xm Xp Z : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
  [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]

/-- **Klt is preserved by fourfold steps.** In a step diagram `(X⁻, B⁻) → Z ← (X⁺, B⁺)` of
fourfolds with `(X⁻, B⁻)` klt, the pair `(X⁺, B⁺)` is klt. -/
@[mmp "lem_oai4_singularities_preserved_b"]
public theorem IsFourfoldStepDiagram.isKltPair_flipTransform
    {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
    {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp) (hklt : IsKltPair sXm B) :
    IsKltPair sXp (flipTransform fm fp B) :=
  ⟨isPair_flipTransform h hklt.1, fun _ D _ hap => by
    obtain ⟨Dm, hDm, hv⟩ := exists_properDivisorOver_minus h D
    obtain ⟨n', am, ham⟩ := exists_isLogDiscrepancy hklt.1 Dm hDm
    exact (hklt.2 n' Dm am ham).trans_le (le_of_isLogDiscrepancy h hklt.1 D Dm hDm hv hap ham)⟩

end

/-! ### Exceptional divisors along a small step -/

section Exceptional

variable {Xm Xp Z : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
  [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]
  {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
  {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}

/-- A divisor over a normal variety is exceptional exactly when its centre has codimension at
least two. -/
private theorem isExceptional_iff_two_le_codimension {k : Type} [Field k] {X : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX) (D : DivisorOver k sX) :
    D.IsExceptional ↔ 2 ≤ codimension D.center := by
  have := D.isLocallyNoetherian
  have := D.isNormal
  have : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated (X ↘ ⊤_ Scheme) := by
    rw [show (X ↘ ⊤_ Scheme) = sX ≫ (Spec (.of k) ↘ ⊤_ Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  unfold DivisorOver.IsExceptional
  rw [MMP.Positivity.isExceptional_toRationalMap_iff]
  have hcl : Closeds.closure (D.f '' (D.E.idealSheaf.support : Set D.Y)) =
      ⟨(D.center : Set X), D.center.isClosed⟩ := Closeds.ext rfl
  rw [hcl, closedsCodimension_coe]

/-- A normalized divisorial valuation realized by a proper divisor `D` over a variety is
exceptional iff the centre of `D` has codimension at least two. -/
private theorem isExceptionalValuation_valuation_iff {k : Type} [Field k] {X : Scheme.{0}}
    [IsIntegral X] {sX : X ⟶ Spec (.of k)} (hX : MMP.Mori.IsVariety k sX)
    (D : DivisorOver k sX) (hD : IsProper D.f) :
    MMP.Intersection.IsExceptionalValuation k sX D.valuation ↔ 2 ≤ codimension D.center := by
  refine ⟨fun ⟨D₁, _, h, hc⟩ => ?_, fun h => ⟨D, hD, rfl, h⟩⟩
  rwa [MMP.Positivity.DivisorOver.center_eq_of_valuation_eq hX h]

/-- When `f⁻` is small, a divisor over `X⁺` exceptional over `X⁺` has an exceptional
counterpart over `X⁻` (any proper divisor over `X⁻` with the same valuation on `k(Z)`). -/
private theorem isExceptional_of_isSmallMorphism
    (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp) (hsmall : IsSmallMorphism sXm sZ fm)
    (Dp : DivisorOver ℂ sXp) (hDp : IsProper Dp.f) (Dm : DivisorOver ℂ sXm) (hDm : IsProper Dm.f)
    (hv : haveI : IsIntegral Z := h.isNormalVariety_target.1.toIsIntegral
      haveI := h.isBirationalMorphism_minus.isDominant
      haveI := h.isBirationalMorphism_plus.isDominant
      Dp.valuation.comap (functionFieldMap fp) = Dm.valuation.comap (functionFieldMap fm))
    (he : Dp.IsExceptional) : Dm.IsExceptional := by
  have hT := (hsmall.isExceptionalValuation_iff h.isSmallMorphism_plus hv.symm).2
  rw [isExceptional_iff_two_le_codimension h.isNormalVariety_minus,
    ← isExceptionalValuation_valuation_iff h.isNormalVariety_minus.1 Dm hDm]
  exact hT <| (isExceptionalValuation_valuation_iff h.isNormalVariety_plus.1 Dp hDp).2 <|
    (isExceptional_iff_two_le_codimension h.isNormalVariety_plus Dp).1 he

end Exceptional

section

variable {Xm Xp Z : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
  [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]

/-- **Terminal is preserved by small fourfold steps.** In a step diagram
`(X⁻, B⁻) → Z ← (X⁺, B⁺)` of fourfolds with `f⁻` small and `(X⁻, B⁻)` terminal, the pair
`(X⁺, B⁺)` is terminal. -/
@[mmp "lem_oai4_singularities_preserved_c"]
public theorem IsFourfoldStepDiagram.isKltTerminalPair_flipTransform
    {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
    {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp) (hm : IsSmallMorphism sXm sZ fm)
    (hterm : IsKltTerminalPair sXm B) :
    IsKltTerminalPair sXp (flipTransform fm fp B) := by
  refine ⟨h.isKltPair_flipTransform hterm.1, fun _ Dp _ hex hap => ?_⟩
  obtain ⟨Dm, hDm, hv⟩ := exists_properDivisorOver_minus h Dp
  obtain ⟨n', am, ham⟩ := exists_isLogDiscrepancy hterm.1.1 Dm hDm
  exact (hterm.2 n' Dm am (isExceptional_of_isSmallMorphism h hm Dp hap.2.1 Dm hDm hv hex)
    ham).trans_le (le_of_isLogDiscrepancy h hterm.1.1 Dp Dm hDm hv hap ham)

end

/-! ### Positive-side bad surfaces suffice -/

/-- In a step diagram of fourfolds with `f⁻` small and no bad surface on either side, the bad
locus `Σ` of the base is empty. -/
private theorem badLocusBase_eq_bot {Xm Xp Z : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm]
    [IsLocallyNoetherian Xm] [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp]
    [IsLocallyNoetherian Xp] [IsNormal Xp]
    {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
    {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (hD : IsFourfoldStepDiagram sXm sZ sXp K B fm fp) (hsmall : IsSmallMorphism sXm sZ fm)
    (hm : ∀ V, ¬ IsNegativeBadSurface fm fp V) (hp : ∀ V, ¬ IsPositiveBadSurface fm fp V) :
    badLocusBase fm fp = ⊥ := by
  have := hD.isProjectiveVariety_minus.toIsVariety.toLocallyOfFiniteType
  have := hD.isProjectiveVariety_plus.toIsVariety.toLocallyOfFiniteType
  have h1m := topologicalKrullDim_le_one sXm hD.dim_minus (badLocusMinus _ _).isClosed
    (hD.topologicalKrullDim_badLocusMinus_le_two hsmall) fun V hV h2 => hm V ⟨hV, h2⟩
  have h1p := topologicalKrullDim_le_one sXp hD.dim_plus (badLocusPlus _ _).isClosed
    hD.topologicalKrullDim_badLocusPlus_le_two fun V hV h2 => hp V ⟨hV, h2⟩
  by_contra hne
  have h3 := hD.three_le_topologicalKrullDim_badLocusMinus_add
    (Set.nonempty_iff_ne_empty.mpr fun he => hne (Closeds.ext he))
  exact absurd ((add_le_add h1m h1p).trans' h3) (by decide)

/-- If, from some index `i₀` on, no step `i` of a step sequence with `f_i` small has a
positive-side bad surface (`MMP.Fourfold.IsPositiveBadSurface`), then the bad locus `Σ_i` of the
base (`MMP.Fourfold.StepSequence.badLocusBaseAt`) is empty for all but finitely many `i`. -/
@[mmp "lem_oai4_surfaces_suffice"]
public theorem StepSequence.eventually_badLocusBaseAt_eq_bot (S : StepSequence) (i₀ : ℕ)
    (h : ∀ i, i₀ ≤ i → IsSmallMorphism (S.sX i) (S.sZ i) (S.f i) →
      ∀ V : IrreducibleCloseds (S.X (i + 1)), ¬ IsPositiveBadSurface (S.f i) (S.fp i) V) :
    ∀ᶠ i in Filter.cofinite, S.badLocusBaseAt i = ⊥ := by
  obtain ⟨i₁', hi₁'⟩ := S.finite_setOf_exists_primeDivisor_isExceptionalValuation.bddAbove
  set i₁ := max i₀ (i₁' + 1)
  have hsmall : S.IsSmallFrom i₁ := fun i hi => by
    by_contra hn
    obtain ⟨E, v, hv, heq⟩ :=
      (S.isFourfoldStepDiagram i).exists_isExceptionalValuation_of_not_isSmallMorphism hn
    have := hi₁' ⟨E, v, heq, hv⟩
    omega
  have hp : ∀ i, i₁ ≤ i → ∀ V : IrreducibleCloseds (S.X (i + 1)),
      ¬ IsPositiveBadSurface (S.f i) (S.fp i) V := fun i hi =>
    h i (le_of_max_le_left hi) (hsmall i hi)
  obtain ⟨i₂', hi₂'⟩ := (S.finite_setOf_exists_isNegativeBadSurface hsmall hp).bddAbove
  rw [Nat.cofinite_eq_atTop, Filter.eventually_atTop]
  refine ⟨max i₁ (i₂' + 1), fun i hi => ?_⟩
  have hi₁ : i₁ ≤ i := le_of_max_le_left hi
  refine badLocusBase_eq_bot (S.isFourfoldStepDiagram i) (hsmall i hi₁) (fun V hV => ?_)
    (hp i hi₁)
  have := hi₂' ⟨V, hV⟩
  omega

end MMP.Fourfold
