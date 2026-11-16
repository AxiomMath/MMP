module

public import MMP.AlgebraicGeometry.Variety.ParameterPoint
public import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.ExceptionalFamilyTriviality
public import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.ExceptionalFibreGeneric
public import MMP.AlgebraicTopology.BorelMoore.FibreClassConstancy
public import MMP.AlgebraicGeometry.CycleMap.Stacks.FibreClassConstancy
public import MMP.AlgebraicGeometry.Intersection.CartierRestriction
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.RegularStalk
public import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.VerticalKernelBlowup
public import MMP.AlgebraicGeometry.Modules.CurveFibreLineBundle
import MMP.AlgebraicGeometry.Morphisms.GenericSmoothness
public import MMP.AlgebraicGeometry.Chow.FieldSituation
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.OpenSubscheme
public import MMP.Topology.KrullDimensionProperClosed
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NonemptyOpen
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
public import MMP.AlgebraicGeometry.ReducedSubschemeOver
public import MMP.AlgebraicGeometry.IdealSheafSubscheme
public import MMP.AlgebraicGeometry.SubschemeOver

/-!
# The algebraic family of the curves cut by a prime divisor on the fibres of `E`

Let `r : Z ⟶ Y` be a curve-and-point exceptional model, `T ⊆ Sing Y` a curve, `E` a component
of the exceptional divisor and `P` a prime divisor of `E` dominating `T`. Over a general open of
`T` the curves cut by `P` on the fibres of `E → T` form an algebraic family: a proper morphism
`ι : V → G` from a complex surface onto `P` into the family `g : G → B` of the fibres of `E` over
a non-singular curve `B`, whose fibres have one-dimensional components of multiplicity one
(generic smoothness on the smooth locus of `P`, the singular curves of `P` meeting the general
fibres in points). For such a family the sums of the classes of the fibre components are
constant along a local product structure of the ambient family `G`.

## Main definitions

* `PrimeDivisorFamily`: the algebraic family of a prime divisor of a component of
  `F` over a general open of `T`.

## Main results

* `finsum_pushforward_fibreTransportHom_fibreAmbientPointsHom_pointCycleClass_eq_of_mult`:
  sums of the cycle classes of the fibre components (generic points of the fibres) are constant
  along an ambient local trivialization, for fibres whose components of the relevant dimension
  have multiplicity one (Fulton, Lemma 19.1.3 and Lemma 19.2(c)).
* `componentMultiplicity_eq_one_of_smooth_open`: multiplicity one for the curve
  components of the fibres of a family which is smooth on an open of its total space.
* `exists_primeDivisorFamily`: a prime divisor of a component of `F` dominating `T`
  has an algebraic family over a general open of `T`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §1.5, §19.1–19.2.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace MMP Topology
open MMP.Intersection.Scheme (Subvariety dimension)
open MMP.UnderlyingSpace MMP.borelMooreHomology
open scoped MMP.SubschemeOver

namespace MMP.Fourfold

open MMP.Mori

/-! ### Points of immersions -/

/-- In a Noetherian space, the complement of a connected component of a closed set `S` in `S` is
closed: it is the union of the finitely many other components. -/
theorem isClosed_diff_connectedComponentIn'' {X : Type*} [TopologicalSpace X]
    [NoetherianSpace X] {S : Set X} (hS : IsClosed S) (x : X) :
    IsClosed (S \ connectedComponentIn S x) := by
  have hcc : ∀ y, IsClosed (connectedComponentIn S y) := fun y ↦ by
    by_cases hy : y ∈ S
    · refine closure_subset_iff_isClosed.1 ?_
      exact (isPreconnected_connectedComponentIn.closure).subset_connectedComponentIn
        (subset_closure (mem_connectedComponentIn hy))
        (closure_minimal (connectedComponentIn_subset S y) hS)
    · rw [connectedComponentIn_eq_empty hy]; exact isClosed_empty
  have hfin := DoubleSurface.finite_connectedComponentIn hS
  have heq : S \ connectedComponentIn S x =
      ⋃ K ∈ {K | ∃ y ∈ S, connectedComponentIn S y = K} ∩
        {K | Disjoint K (connectedComponentIn S x)}, K := by
    ext y
    simp only [Set.mem_diff, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq, exists_prop]
    constructor
    · rintro ⟨hyS, hyx⟩
      refine ⟨connectedComponentIn S y, ⟨⟨y, hyS, rfl⟩, ?_⟩, mem_connectedComponentIn hyS⟩
      rw [Set.disjoint_iff]
      rintro w ⟨hwy, hwx⟩
      exact hyx ((connectedComponentIn_eq hwy).trans (connectedComponentIn_eq hwx).symm ▸
        mem_connectedComponentIn hyS)
    · rintro ⟨K, ⟨⟨w, -, rfl⟩, hdisj⟩, hyK⟩
      exact ⟨connectedComponentIn_subset S w hyK, fun hyx ↦ Set.disjoint_left.1 hdisj hyK hyx⟩
  rw [heq]
  exact (hfin.subset Set.inter_subset_left).isClosed_biUnion fun K hK ↦ by
    obtain ⟨⟨w, -, rfl⟩, -⟩ := hK
    exact hcc w

/-- The preimage of an irreducible set lying in the image of an embedding is irreducible. -/
theorem isIrreducible_preimage_of_isEmbedding' {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] {φ : A → B} (hφ : Topology.IsEmbedding φ) {C : Set B}
    (hC : IsIrreducible C) (hCr : C ⊆ Set.range φ) : IsIrreducible (φ ⁻¹' C) := by
  refine ⟨?_, fun u v hu hv ⟨a, has, hau⟩ ⟨b, hbs, hbv⟩ ↦ ?_⟩
  · obtain ⟨c, hc⟩ := hC.nonempty
    obtain ⟨a, rfl⟩ := hCr hc
    exact ⟨a, hc⟩
  · obtain ⟨u', hu', rfl⟩ := hφ.isInducing.isOpen_iff.1 hu
    obtain ⟨v', hv', rfl⟩ := hφ.isInducing.isOpen_iff.1 hv
    obtain ⟨c, hcC, hcu, hcv⟩ := hC.2 u' v' hu' hv' ⟨φ a, has, hau⟩ ⟨φ b, hbs, hbv⟩
    obtain ⟨d, rfl⟩ := hCr hcC
    exact ⟨d, hcC, hcu, hcv⟩

/-- The point of `X'` under a complex point `g(q)` is the image of the point under `q`. -/
private theorem toHom_closedPoint_mapFun {K : Type} [Field K] {X X' : Scheme.{0}}
    [X.Over (Spec (.of K))] [X'.Over (Spec (.of K))] (g : X ⟶ X') [g.IsOver (Spec (.of K))]
    (q : UnderlyingSpace K X) :
    (mapFun g q).toHom (IsLocalRing.closedPoint K) = g.base (q.toHom (IsLocalRing.closedPoint K)) := by
  rw [toHom_mapFun]; rfl

private theorem range_mapFun_eq_pointsOver_of_isOpenImmersion {K : Type} [Field K]
    {X X' : Scheme.{0}} [X.Over (Spec (.of K))] [X'.Over (Spec (.of K))] (a : X ⟶ X')
    [IsOpenImmersion a] [a.IsOver (Spec (.of K))] :
    Set.range (mapFun (K := K) a) = pointsOver (Set.range a.base) := by
  rw [range_mapFun_of_isOpenImmersion]
  ext q
  simp only [Set.mem_setOf_eq, mem_pointsOver]
  haveI : Subsingleton (Spec (.of K)) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  constructor
  · intro h
    exact h (show IsLocalRing.closedPoint K ∈ (⊤ : (Spec (.of K)).Opens) from trivial)
  · intro h x _
    rw [Subsingleton.elim x (IsLocalRing.closedPoint K)]
    exact h

private theorem image_pointsOver_of_isClosedImmersion {K : Type} [Field K] [TopologicalSpace K]
    {X X' : Scheme.{0}} [X.Over (Spec (.of K))] [X'.Over (Spec (.of K))] (b : X ⟶ X')
    [IsClosedImmersion b] [b.IsOver (Spec (.of K))] (A : Set X) :
    mapFun (K := K) b '' pointsOver A = pointsOver (b.base '' A) := by
  ext q
  constructor
  · rintro ⟨q₀, hq₀, rfl⟩
    exact ⟨_, hq₀, (toHom_closedPoint_mapFun b q₀).symm⟩
  · rintro ⟨x, hx, hxq⟩
    have hq : q ∈ Set.range ⇑(map (K := K) b) := by
      rw [range_map_of_isClosedImmersion]; exact ⟨x, hxq⟩
    obtain ⟨q₀, rfl⟩ := hq
    refine ⟨q₀, ?_, rfl⟩
    change _ = (mapFun b q₀).toHom (IsLocalRing.closedPoint K) at hxq
    rw [toHom_closedPoint_mapFun] at hxq
    rw [mem_pointsOver, ← b.isClosedEmbedding.injective hxq]
    exact hx

private theorem mapFun_comp_eq {K : Type} [Field K] {X X' X'' : Scheme.{0}}
    [X.Over (Spec (.of K))] [X'.Over (Spec (.of K))] [X''.Over (Spec (.of K))] (a : X ⟶ X')
    (b : X' ⟶ X'') [a.IsOver (Spec (.of K))] [b.IsOver (Spec (.of K))] :
    mapFun (K := K) (a ≫ b) = mapFun b ∘ mapFun a :=
  funext fun q ↦ UnderlyingSpace.ext (by
    rw [toHom_mapFun, Function.comp_apply, toHom_mapFun, toHom_mapFun, Category.assoc])

/-- The complex points of an open subscheme of a closed subscheme. -/
theorem range_mapFun_comp_eq_pointsOver {K : Type} [Field K] [TopologicalSpace K]
    {X X' X'' : Scheme.{0}} [X.Over (Spec (.of K))] [X'.Over (Spec (.of K))]
    [X''.Over (Spec (.of K))] (a : X ⟶ X') (b : X' ⟶ X'') [IsOpenImmersion a]
    [IsClosedImmersion b] [a.IsOver (Spec (.of K))] [b.IsOver (Spec (.of K))] :
    Set.range (mapFun (K := K) (a ≫ b)) = pointsOver (Set.range (a ≫ b).base) ∧
      IsEmbedding (mapFun (K := K) (a ≫ b)) := by
  rw [mapFun_comp_eq]
  refine ⟨?_, (isClosedEmbedding_map_of_isClosedImmersion (K := K) b).isEmbedding.comp
    (isOpenEmbedding_map_of_isOpenImmersion (K := K) a).isEmbedding⟩
  rw [Set.range_comp, range_mapFun_eq_pointsOver_of_isOpenImmersion,
    image_pointsOver_of_isClosedImmersion, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]

/-- The fibres of a smooth family of curves on a surface: reduced, with pairwise disjoint
one-dimensional components. -/
theorem fibre_props_of_smooth {V B : Scheme.{0}} [V.Over (Spec (.of ℂ))]
    [B.Over (Spec (.of ℂ))] [IsIntegral V] [IsIntegral B]
    [LocallyOfFiniteType (V ↘ Spec (.of ℂ))] [QuasiCompact (V ↘ Spec (.of ℂ))]
    [LocallyOfFiniteType (B ↘ Spec (.of ℂ))] (f : V ⟶ B) [f.IsOver (Spec (.of ℂ))] [Smooth f]
    (hB : topologicalKrullDim B = ((1 : ℕ) : WithBot ℕ∞))
    (hV : topologicalKrullDim V = ((2 : ℕ) : WithBot ℕ∞)) (s : ParameterPoint B) :
    IsReduced (ParameterPoint.fibre f s) ∧
      (∀ A ∈ irreducibleComponents (ParameterPoint.fibre f s),
        ∀ A' ∈ irreducibleComponents (ParameterPoint.fibre f s), A ≠ A' → Disjoint A A') ∧
      ∀ A ∈ irreducibleComponents (ParameterPoint.fibre f s),
        topologicalKrullDim A = ((1 : ℕ) : WithBot ℕ∞) := by
  have hsm : Smooth (ParameterPoint.fibreProj f s) :=
    MMP.smooth_fiberToSpecResidueField_of_smooth_restrict f ⊤ s.point trivial
  refine ⟨AlgebraicGeometry.isReduced_of_smooth (ParameterPoint.fibreProj f s),
    fun A hA A' hA' hne ↦
      @MMP.Flips.ResolutionInputs.disjoint_of_mem_irreducibleComponents_of_smooth _ _ _
        (ParameterPoint.fibreProj f s) hsm _ _ hA hA' hne, fun A hA ↦ ?_⟩
  have hd := MMP.topologicalKrullDim_add_of_smooth_restrict (K := ℂ) f ⊤ s.point trivial A hA
  rw [hB, hV] at hd
  revert hd
  generalize topologicalKrullDim A = e
  intro hd
  induction e using WithBot.recBotCoe with
  | bot => simp at hd
  | coe e =>
    have h' : e + 1 = 2 := WithBot.coe_injective (by rw [WithBot.coe_add]; exact hd)
    induction e using ENat.recTopCoe with
    | top => simp at h'
    | coe e =>
      have : e + 1 = 2 := by exact_mod_cast h'
      rw [(by omega : e = 1)]
      rfl

/-- The `ℂ`-point of a closed point of a scheme locally of finite type over `ℂ`. -/
theorem exists_toHom_eq' {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] {x : X} (hx : IsClosed {x}) :
    ∃ p : UnderlyingSpace ℂ X, p.toHom (IsLocalRing.closedPoint ℂ) = x :=
  ⟨(equivClosedPoints (K := ℂ) X).symm ⟨x, hx⟩, by
    rw [← equivClosedPoints_apply, Equiv.apply_symm_apply]⟩

/-- A scheme point which is the point of a `ℂ`-point is closed. -/
private theorem isClosed_singleton_toHom' {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] (p : UnderlyingSpace ℂ X) :
    IsClosed {p.toHom (IsLocalRing.closedPoint ℂ)} := by
  have := ((equivClosedPoints (K := ℂ) X) p).2
  rwa [equivClosedPoints_apply] at this

/-- A closed set whose complex points lie in a closed set `B` lies in `B`. -/
private theorem subset_of_pointsOver_subset {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] {A B : Set X} (hA : IsClosed A) (hB : IsClosed B)
    (h : pointsOver (K := ℂ) A ⊆ pointsOver (K := ℂ) B) : A ⊆ B := by
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace (X ↘ Spec (.of ℂ))
  rw [← closure_inter_closedPoints hA]
  refine closure_minimal (fun a ⟨ha, hac⟩ ↦ ?_) hB
  obtain ⟨p, rfl⟩ := exists_toHom_eq' (X := X) hac
  exact h ha

section multFibre

/-- A component of a closed subscheme whose stalk at its generic point is a field has
multiplicity one (Stacks, Tag 02QU): the stalk is then a simple module over the stalk of the
ambient scheme, which maps onto it. -/
theorem componentMultiplicity_eq_one_of_isField_stalk {X W : Scheme.{0}} (i : W ⟶ X)
    [IsClosedImmersion i] (ξ : genericPoints W) (h : IsField (W.presheaf.stalk ξ.1)) :
    Stacks.Chow.componentMultiplicity i ξ = 1 := by
  let R := X.presheaf.stalk (i ξ.1)
  let M := W.presheaf.stalk ξ.1
  let : Algebra R M := (i.stalkMap ξ.1).hom.toAlgebra
  let : IsScalarTower R M M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hsimp : IsSimpleModule R M := by
    let := h.toField
    exact Stacks.Chow.isSimpleModule_of_surjective_toField (algebraMap R M)
      (i.stalkMap_surjective ξ.1)
  unfold Stacks.Chow.componentMultiplicity
  rw [show Module.length R M = 1 from Module.length_eq_one_iff.mpr hsimp]
  rfl

end multFibre

end MMP.Fourfold

namespace MMP.Chow

open Stacks.Chow

variable {R : Type} [CommRing R] {X W : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsComplexScheme X]

open Classical in
/-- **The class of a closed subscheme with multiplicity-one components, read through an additive
map.** For a closed immersion `j : W ⟶ X` whose components of delta-dimension `n` have
multiplicity one and an additive map `φ` out of `H_{2n}(X)`, `φ` of the class of `[j(W)]_n`
(Stacks, Tag 02QU) is the sum of `φ(cl_X(x))` over the images `x` of the generic points of `W`
of delta-dimension `n`. -/
private theorem map_cycleClass_cycleAssociatedToClosedSubscheme_of_mult {M : Type*}
    [AddCommGroup M] {n : ℕ} (φ : BMHomology R X (2 * n) →+ M) (j : W ⟶ X)
    [IsClosedImmersion j]
    (hmult : ∀ ξ : genericPoints W, relativeDimension (fieldChowSituation ℂ).dimensionFunction
      (X ↘ Spec (.of ℂ)) (j.base ξ.1) = n → componentMultiplicity j ξ = 1) :
    φ (cycleClass R n (cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ)
        (X ↘ Spec (.of ℂ)) j n)) =
      ∑ᶠ (x : {x : X // relativeDimension (fieldChowSituation ℂ).dimensionFunction
          (X ↘ Spec (.of ℂ)) x = n})
        (_ : ∃ ξ : genericPoints W, j.base ξ.1 = x.1), φ (pointCycleClass R x.1 x.2) := by
  set α := cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) j (n : ℤ)
  have hS := finite_support_cycle α
  have hval : ∀ x : X, relativeDimension (fieldChowSituation ℂ).dimensionFunction
      (X ↘ Spec (.of ℂ)) x = n →
      α.1 x = if ∃ ξ : genericPoints W, j.base ξ.1 = x then 1 else 0 := by
    intro x hx
    split_ifs with h
    · obtain ⟨ξ, rfl⟩ := h
      rw [cycleAssociatedToClosedSubscheme_apply (fieldChowSituation ℂ) _ j _ ξ hx, hmult ξ hx]
    · exact cycleAssociatedToClosedSubscheme_apply_eq_zero _ _ j _ x
        fun ⟨ξ, hξ, _⟩ ↦ h ⟨ξ, hξ⟩
  have hdim : ∀ x ∈ hS.toFinset, relativeDimension (fieldChowSituation ℂ).dimensionFunction
      (X ↘ Spec (.of ℂ)) x = n := fun x hx ↦
    (mem_cyclesOfDimension_iff_forall_point (fieldChowSituation ℂ) _ _ α.1).mp α.2 x
      (hS.mem_toFinset.mp hx)
  rw [cycleClass_eq_sum, map_sum,
    finsum_cond_eq_sum_of_cond_iff _ (t := hS.toFinset.subtype fun x ↦
      relativeDimension (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) x = n)
      fun {x} _ ↦ by
        rw [Finset.mem_subtype, hS.mem_toFinset, Function.mem_support, hval x.1 x.2]
        split_ifs with h
        · exact iff_of_true h one_ne_zero
        · exact iff_of_false h fun h' ↦ h' rfl]
  rw [show (∑ x ∈ hS.toFinset.subtype fun x ↦
        relativeDimension (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) x = n,
        φ (pointCycleClass R x.1 x.2)) =
      ∑ x ∈ hS.toFinset.subtype fun x ↦
        relativeDimension (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) x = n,
        φ (pointCycleClassOrZero R n x.1) from
      Finset.sum_congr rfl fun x _ ↦ by rw [pointCycleClassOrZero, dite_eq_left x.2],
    Finset.sum_subtype_eq_sum_filter (f := fun x ↦ φ (pointCycleClassOrZero R n x)),
    Finset.filter_true_of_mem hdim]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  have hne : α.1 x ≠ 0 := hS.mem_toFinset.mp hx
  rw [hval x (hdim x hx)] at hne ⊢
  rw [ite_eq_left (by by_contra h; exact hne (ite_eq_right h)), one_smul]

end MMP.Chow

namespace MMP.Fourfold

open MMP.Mori

section multFibre

open Stacks.Chow

variable {R : Type} [CommRing R] {T : Scheme.{0}} [T.Over (Spec (.of ℂ))]
  [IsSmoothVariety ℂ (T ↘ Spec (.of ℂ))] {V : Scheme.{0}} [V.Over (Spec (.of ℂ))] [IsComplexScheme V]
  [IsIntegral V] {G : Scheme.{0}} [G.Over (Spec (.of ℂ))] [IsComplexScheme G]

/-- **Sums of fibre component classes are constant along an ambient local trivialization**, for
fibres whose components of delta-dimension `n` have multiplicity one (Fulton, Lemma 19.1.3 and
Lemma 19.2(c)): the variant of
`MMP.Fourfold.finsum_pushforward_fibreTransportHom_fibreAmbientPointsHom_pointCycleClass_eq`
in which the fibres need not be reduced. -/
theorem finsum_pushforward_fibreTransportHom_fibreAmbientPointsHom_pointCycleClass_eq_of_mult
    (hT : SmoothOfRelativeDimension 1 (T ↘ Spec (.of ℂ))) (ι : V ⟶ G) [ι.IsOver (Spec (.of ℂ))]
    [IsProper ι] (g : G ⟶ T) [g.IsOver (Spec (.of ℂ))] (f : V ⟶ T) [f.IsOver (Spec (.of ℂ))]
    [IsDominant f] (hf : ι ≫ g = f) {n : ℕ} (hn : ((n + 1 : ℕ) : WithBot ℕ∞) = dimension V)
    {X : TopCat.{0}} [TopologicalSpace.MetrizableSpace X]
    (W : TopologicalSpace.Opens (TopCat.of (UnderlyingSpace ℂ T)))
    [ConnectedSpace W] (ψ : X × W ≃ₜ preimageOpens (TopCat.ofHom (map (K := ℂ) g)) W)
    (hψ : ∀ p, map (K := ℂ) g (ψ p : UnderlyingSpace ℂ G) = (p.2 : UnderlyingSpace ℂ T))
    (t t' : ParameterPoint T) (ht : t.complexPoint ∈ W) (ht' : t'.complexPoint ∈ W)
    (hmult : ∀ ξ : genericPoints (ParameterPoint.fibre f t),
      relativeDimension (fieldChowSituation ℂ).dimensionFunction
        (ParameterPoint.fibre f t ↘ Spec (.of ℂ)) ξ.1 = n →
      componentMultiplicity (𝟙 (ParameterPoint.fibre f t)) ξ = 1)
    (hmult' : ∀ ξ : genericPoints (ParameterPoint.fibre f t'),
      relativeDimension (fieldChowSituation ℂ).dimensionFunction
        (ParameterPoint.fibre f t' ↘ Spec (.of ℂ)) ξ.1 = n →
      componentMultiplicity (𝟙 (ParameterPoint.fibre f t')) ξ = 1) :
    ∑ᶠ (x : {x : ParameterPoint.fibre f t // relativeDimension
          (fieldChowSituation ℂ).dimensionFunction (ParameterPoint.fibre f t ↘ Spec (.of ℂ)) x =
            n})
        (_ : x.1 ∈ genericPoints (ParameterPoint.fibre f t)),
        (pushforward R (ModuleCat.of R R)
          (fibreAmbientPointsHom ι g hf t ≫ fibreTransportHom ψ hψ ht)
          ((isProperMap_fibreTransportHom ψ hψ ht).comp
            (isProperMap_fibreAmbientPointsHom ι g hf t)) (2 * n : ℕ)).hom
          (Chow.pointCycleClass R x.1 x.2) =
      ∑ᶠ (x : {x : ParameterPoint.fibre f t' // relativeDimension
          (fieldChowSituation ℂ).dimensionFunction (ParameterPoint.fibre f t' ↘ Spec (.of ℂ)) x =
            n})
        (_ : x.1 ∈ genericPoints (ParameterPoint.fibre f t')),
        (pushforward R (ModuleCat.of R R)
          (fibreAmbientPointsHom ι g hf t' ≫ fibreTransportHom ψ hψ ht')
          ((isProperMap_fibreTransportHom ψ hψ ht').comp
            (isProperMap_fibreAmbientPointsHom ι g hf t')) (2 * n : ℕ)).hom
          (Chow.pointCycleClass R x.1 x.2) := by
  have key : ∀ (s : ParameterPoint T) (hs : s.complexPoint ∈ W),
      (∀ ξ : genericPoints (ParameterPoint.fibre f s),
        relativeDimension (fieldChowSituation ℂ).dimensionFunction
          (ParameterPoint.fibre f s ↘ Spec (.of ℂ)) ξ.1 = n →
        componentMultiplicity (𝟙 (ParameterPoint.fibre f s)) ξ = 1) →
      (pushforward R (ModuleCat.of R R) (fibreTransportHom ψ hψ hs)
          (isProperMap_fibreTransportHom ψ hψ hs) (2 * n : ℕ)).hom
          ((pushforward R (ModuleCat.of R R) (fibreAmbientPointsHom ι g hf s)
            (isProperMap_fibreAmbientPointsHom ι g hf s) (2 * n : ℕ)).hom
            (Chow.cycleClass R n (cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ)
              (ParameterPoint.fibre f s ↘ Spec (.of ℂ)) (𝟙 _) n))) =
        ∑ᶠ (x : {x : ParameterPoint.fibre f s // relativeDimension
            (fieldChowSituation ℂ).dimensionFunction
              (ParameterPoint.fibre f s ↘ Spec (.of ℂ)) x = n})
          (_ : x.1 ∈ genericPoints (ParameterPoint.fibre f s)),
          (pushforward R (ModuleCat.of R R)
            (fibreAmbientPointsHom ι g hf s ≫ fibreTransportHom ψ hψ hs)
            ((isProperMap_fibreTransportHom ψ hψ hs).comp
              (isProperMap_fibreAmbientPointsHom ι g hf s)) (2 * n : ℕ)).hom
            (Chow.pointCycleClass R x.1 x.2) := by
    intro s hs hms
    have h := Chow.map_cycleClass_cycleAssociatedToClosedSubscheme_of_mult (R := R)
      ((pushforward R (ModuleCat.of R R)
        (fibreAmbientPointsHom ι g hf s ≫ fibreTransportHom ψ hψ hs)
        ((isProperMap_fibreTransportHom ψ hψ hs).comp
          (isProperMap_fibreAmbientPointsHom ι g hf s)) (2 * n : ℕ)).hom.toAddMonoidHom)
      (𝟙 (ParameterPoint.fibre f s)) fun ξ hξ ↦ hms ξ hξ
    rw [← pushforward_comp_apply']
    refine h.trans (finsum_congr fun x ↦ ?_)
    exact finsum_congr_Prop (propext ⟨fun ⟨ξ, hξ⟩ ↦ by rw [← hξ]; exact ξ.2,
      fun hx ↦ ⟨⟨_, hx⟩, rfl⟩⟩) fun _ ↦ rfl
  rw [← key t ht hmult, ← key t' ht' hmult']
  exact pushforward_fibreTransportHom_fibreAmbientPointsHom_cycleClass_eq hT ι g f hf hn W ψ hψ
    t t' ht ht'

end multFibre

section restrictFinsum

variable {R : Type} [CommRing R]

/-- **Restricting a finite sum of push-forwards to a clopen piece.** If each of finitely many
proper maps `k_i : A_i → X` lands in an open `Ω` or misses it, restricting `∑ k_{i*} a_i` to `Ω`
and pushing back keeps exactly the terms landing in `Ω`. -/
theorem pushforward_inclHom_restrict_finsum {X : TopCat.{0}} [T2Space X] {ι : Type*}
    {A : ι → TopCat.{0}} [∀ i, T2Space (A i)] (k : ∀ i, A i ⟶ X) (hk : ∀ i, IsProperMap (k i))
    (Ω : TopologicalSpace.Opens X) (hp : IsProperMap (inclHom Ω)) (j : ℤ)
    (a : ∀ i, borelMooreHomology R (ModuleCat.of R R) (A i) j) {J : Set ι} (hJ : J.Finite)
    (hdich : ∀ i ∈ J, Set.range (k i) ⊆ Ω ∨ Disjoint (Set.range (k i)) Ω) :
    (pushforward R (ModuleCat.of R R) (inclHom Ω) hp j).hom
        ((restrict R (ModuleCat.of R R) Ω j).hom
          (∑ᶠ i ∈ J, (pushforward R (ModuleCat.of R R) (k i) (hk i) j).hom (a i))) =
      ∑ᶠ i ∈ J ∩ {i | Set.range (k i) ⊆ Ω},
        (pushforward R (ModuleCat.of R R) (k i) (hk i) j).hom (a i) := by
  set g := ((pushforward R (ModuleCat.of R R) (inclHom Ω) hp j).hom.toAddMonoidHom).comp
    (restrict R (ModuleCat.of R R) Ω j).hom.toAddMonoidHom with hg
  have h1 := AddMonoidHom.map_finsum_mem
    (fun i ↦ (pushforward R (ModuleCat.of R R) (k i) (hk i) j).hom (a i)) g hJ
  change g _ = _
  rw [h1, ← finsum_mem_inter_add_sdiff (t := {i | Set.range (k i) ⊆ Ω}) hJ]
  rw [finsum_mem_of_eqOn_zero (s := J \ {i | Set.range (k i) ⊆ Ω}) (fun i hi ↦ ?_), add_zero]
  · refine finsum_mem_congr rfl fun i hi ↦ ?_
    exact pushforward_inclHom_restrict_pushforward_of_range_subset (k i) (hk i) Ω hi.2 hp j (a i)
  · have hd : Disjoint (Set.range (k i)) Ω := (hdich i hi.1).resolve_left hi.2
    change (pushforward R (ModuleCat.of R R) (inclHom Ω) hp j).hom
      ((restrict R (ModuleCat.of R R) Ω j).hom
        ((pushforward R (ModuleCat.of R R) (k i) (hk i) j).hom (a i))) = 0
    rw [restrict_pushforward_eq_zero_of_disjoint (k i) (hk i) Ω hd j (a i), map_zero]

end restrictFinsum

/-- The fibre of a morphism out of a scheme locally of finite type over `ℂ` is locally of finite
type over `ℂ`. -/
private theorem locallyOfFiniteType_fibre_over {V B : Scheme.{0}} [V.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (V ↘ Spec (.of ℂ))] (f : V ⟶ B) (s : ParameterPoint B) :
    LocallyOfFiniteType (ParameterPoint.fibre f s ↘ Spec (.of ℂ)) := by
  change LocallyOfFiniteType (ParameterPoint.fibreι f s ≫ V ↘ Spec (.of ℂ))
  infer_instance

/-- **Multiplicity one along a component meeting a smooth open.** If `f : V → B` is smooth on an
open `O ⊆ V`, every irreducible component of a fibre `V_s` whose generic point lies in `O` has
multiplicity one: the fibre of `O → B` is smooth, hence reduced, and is open in `V_s`. -/
theorem componentMultiplicity_eq_one_of_genericPoint_mem {V B : Scheme.{0}} (f : V ⟶ B)
    (O : V.Opens) [Smooth (O.ι ≫ f)] (s : ParameterPoint B)
    (ξ : genericPoints (ParameterPoint.fibre f s))
    (hη : (ParameterPoint.fibreι f s).base ξ.1 ∈ O) :
    Stacks.Chow.componentMultiplicity (𝟙 (ParameterPoint.fibre f s)) ξ = 1 := by
  haveI hm : IsOpenImmersion (ParameterPoint.fibreMap (p := O.ι ≫ f) (q := f) O.ι rfl s) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion)
      (ParameterPoint.isPullback_fibreMap (q := f) O.ι rfl s).flip inferInstance
  have hr := Scheme.Pullback.range_map (O.ι ≫ f) s.ι f s.ι O.ι (𝟙 _) (𝟙 _) (by simp) (by simp)
  have hrange : ξ.1 ∈
      Set.range (ParameterPoint.fibreMap (p := O.ι ≫ f) (q := f) O.ι rfl s).base := by
    have e : Set.range (ParameterPoint.fibreMap (p := O.ι ≫ f) (q := f) O.ι rfl s).base =
      Set.range (Limits.pullback.map (O.ι ≫ f) s.ι f s.ι O.ι (𝟙 _) (𝟙 _) (by simp)
        (by simp)).base := rfl
    rw [e, hr]
    refine ⟨?_, ?_⟩
    · change (ParameterPoint.fibreι f s).base _ ∈ Set.range O.ι.base
      rw [Scheme.Opens.range_ι]; exact hη
    · exact ⟨_, rfl⟩
  obtain ⟨η', hη'⟩ := hrange
  haveI : Smooth (ParameterPoint.fibreProj (O.ι ≫ f) s) :=
    MorphismProperty.of_isPullback (P := @Smooth)
      (ParameterPoint.isPullback_fibre (O.ι ≫ f) s) inferInstance
  haveI : IsReduced (ParameterPoint.fibre (O.ι ≫ f) s) :=
    AlgebraicGeometry.isReduced_of_smooth (ParameterPoint.fibreProj (O.ι ≫ f) s)
  set m := ParameterPoint.fibreMap (p := O.ι ≫ f) (q := f) O.ι rfl s with hmdef
  have hgen : closure {η'} ∈ irreducibleComponents (ParameterPoint.fibre (O.ι ≫ f) s) := by
    have hx : closure {m.base η'} ∈ irreducibleComponents (ParameterPoint.fibre f s) := by
      rw [hη']; exact ξ.2
    rw [m.isOpenEmbedding.closure_eq_preimage_closure_image, Set.image_singleton]
    exact preimage_mem_irreducibleComponents hx m.isOpenEmbedding
      ⟨m.base η', subset_closure rfl, _, rfl⟩
  have hF' := isField_stalk_of_closure_mem_irreducibleComponents _ η' hgen
  haveI : IsIso (m.stalkMap η') := IsOpenImmersion.instIsIsoCommRingCatStalkMap _ η'
  have hF : IsField ((ParameterPoint.fibre f s).presheaf.stalk (m.base η')) :=
    (asIso (m.stalkMap η')).commRingCatIsoToRingEquiv.isField hF'
  rw [hη'] at hF
  exact componentMultiplicity_eq_one_of_isField_stalk _ ξ hF

private theorem topologicalKrullDim_mono {X : Type*} [TopologicalSpace X] {A B : Set X}
    (h : A ⊆ B) :
    topologicalKrullDim A ≤ topologicalKrullDim B :=
  (Topology.IsInducing.of_comp (continuous_inclusion h) continuous_subtype_val
    Topology.IsInducing.subtypeVal).topologicalKrullDim_le

/-- **The fibres of a curve-dimensional closed set over a general point.** Let `p : X → C` be a
map from a Noetherian space to an irreducible space with more than one point, and `Z₀ ⊆ X` a
closed set whose irreducible components have dimension at most one. Over a nonempty open of
`C`, the fibres of `Z₀` over closed points contain no irreducible set of dimension `≥ 1`: the
components of `Z₀` contracted to points miss it, and the others meet every fibre in dimension
`0`. -/
theorem exists_isOpen_forall_topologicalKrullDim_lt_one {X C : Type*} [TopologicalSpace X]
    [TopologicalSpace C] [TopologicalSpace.NoetherianSpace X] [IrreducibleSpace C] [Nontrivial C]
    (p : X → C) (hp : Continuous p) {Z₀ : Set X} (hZ₀ : IsClosed Z₀)
    (hdim : ∀ Zi, Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ Z₀) Zi → topologicalKrullDim Zi ≤ 1) :
    ∃ W : Set C, IsOpen W ∧ W.Nonempty ∧ ∀ y ∈ W, IsClosed ({y} : Set C) → ∀ A ⊆ Z₀,
      IsIrreducible A → A ⊆ p ⁻¹' {y} → topologicalKrullDim A < 1 := by
  classical
  set M := {Zi | Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ Z₀) Zi ∧ closure (p '' Zi) ≠ Set.univ}
    with hM
  have hMfin : M.Finite := (finite_setOf_maximal Z₀).subset fun Zi h ↦ h.1
  set Bad := ⋃ Zi ∈ M, closure (p '' Zi) with hBad
  have hBadcl : IsClosed Bad := hMfin.isClosed_biUnion fun _ _ ↦ isClosed_closure
  have hBadne : Bad ≠ Set.univ := by
    intro h
    have hfin := hMfin.image (fun Zi ↦ closure (p '' Zi))
    have hu : (Set.univ : Set C) ⊆ ⋃₀ (↑hfin.toFinset : Set (Set C)) := by
      rw [Set.Finite.coe_toFinset, Set.sUnion_image, ← hBad, h]
    obtain ⟨t, ht, hsub⟩ := (isIrreducible_iff_sUnion_isClosed.1
      (IrreducibleSpace.isIrreducible_univ C)) hfin.toFinset
      (fun z hz ↦ by
        rw [Set.Finite.mem_toFinset] at hz
        obtain ⟨Zi, -, rfl⟩ := hz
        exact isClosed_closure) hu
    rw [Set.Finite.mem_toFinset] at ht
    obtain ⟨Zi, hZi, rfl⟩ := ht
    exact hZi.2 (Set.eq_univ_of_univ_subset hsub)
  refine ⟨Badᶜ, hBadcl.isOpen_compl, ?_, fun y hy hycl A hAZ hAirr hAy ↦ ?_⟩
  · by_contra h
    rw [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] at h
    exact hBadne h
  by_contra hA
  rw [not_lt] at hA
  obtain ⟨Zi, hAZi, hZi⟩ := exists_subset_maximal_of_isIrreducible hAirr hAZ
  have hZicl : IsClosed Zi := isClosed_of_maximal hZ₀ hZi
  have hcl : closure A = Zi := by
    by_contra hne
    have hlt := MMP.topologicalKrullDim_lt_of_subset_of_ne hZi.1.1 isClosed_closure
      (closure_minimal hAZi hZicl) hne (ne_top_of_le_ne_top (by decide) (hdim Zi hZi))
    have h1 := topologicalKrullDim_mono (subset_closure : A ⊆ closure A)
    exact lt_irrefl _ (hA.trans_lt (h1.trans_lt (hlt.trans_le (hdim Zi hZi))))
  have h2 : p '' A ⊆ {y} := by rintro _ ⟨x, hx, rfl⟩; exact hAy hx
  have h3 : p '' closure A ⊆ {y} :=
    (image_closure_subset_closure_image hp).trans (closure_minimal h2 hycl)
  have himg : closure (p '' Zi) ⊆ {y} := by
    rw [← hcl]; exact closure_minimal h3 hycl
  have hZiM : Zi ∈ M := by
    refine ⟨hZi, fun h ↦ ?_⟩
    obtain ⟨a, b, hab⟩ := exists_pair_ne C
    have ha : a ∈ ({y} : Set C) := himg (h ▸ Set.mem_univ a)
    have hb : b ∈ ({y} : Set C) := himg (h ▸ Set.mem_univ b)
    exact hab (ha.trans hb.symm)
  obtain ⟨x, hx⟩ := hAirr.nonempty
  apply hy
  refine Set.mem_biUnion hZiM (subset_closure ⟨x, hAZi hx, ?_⟩)
  exact hAy hx

/-- **Multiplicity one for the curve components of the fibres of a family generically smooth on
its total space.** If `f : V → B` is smooth on an open `O` and no fibre of the closed complement
of `O` contains an irreducible set of dimension `≥ 1`, every component of delta-dimension one of
every fibre has multiplicity one. -/
theorem componentMultiplicity_eq_one_of_smooth_open {V B : Scheme.{0}} [V.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (V ↘ Spec (.of ℂ))] (f : V ⟶ B)
    (O : V.Opens) [Smooth (O.ι ≫ f)]
    (hbad : ∀ (s : ParameterPoint B) (A : Set V), IsIrreducible A → A ⊆ (O : Set V)ᶜ →
      A ⊆ f.base ⁻¹' {s.point} → topologicalKrullDim A < 1)
    (s : ParameterPoint B) (ξ : genericPoints (ParameterPoint.fibre f s))
    (h1 : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (ParameterPoint.fibre f s ↘ Spec (.of ℂ)) ξ.1 = (1 : ℕ)) :
    Stacks.Chow.componentMultiplicity (𝟙 (ParameterPoint.fibre f s)) ξ = 1 := by
  by_cases hη : (ParameterPoint.fibreι f s).base ξ.1 ∈ O
  · exact componentMultiplicity_eq_one_of_genericPoint_mem f O s ξ hη
  exfalso
  set i := ParameterPoint.fibreι f s with hi
  set A := closure ({ξ.1} : Set (ParameterPoint.fibre f s)) with hAdef
  have hA : A ∈ irreducibleComponents (ParameterPoint.fibre f s) := ξ.2
  have hsub : i.base '' A ⊆ (O : Set V)ᶜ := by
    refine (image_closure_subset_closure_image i.continuous).trans (closure_minimal ?_
      O.isOpen.isClosed_compl)
    rintro _ ⟨x, rfl, rfl⟩
    exact hη
  have hfib : i.base '' A ⊆ f.base ⁻¹' {s.point} := by
    rintro _ ⟨x, -, rfl⟩
    have : i.base x ∈ Set.range i.base := ⟨x, rfl⟩
    rw [hi, ParameterPoint.range_fibreι] at this
    exact this
  have hdimA : topologicalKrullDim A = ((1 : ℕ) : WithBot ℕ∞) := by
    haveI := locallyOfFiniteType_fibre_over f s
    rw [hAdef, Stacks.Chow.topologicalKrullDim_closure_singleton_eq ℂ
      (ParameterPoint.fibre f s ↘ Spec (.of ℂ)) ξ.1, h1,
      Int.toNat_natCast]
  have hdim' : topologicalKrullDim (i.base '' A) = ((1 : ℕ) : WithBot ℕ∞) := by
    rw [← hdimA]
    exact ((i.isClosedEmbedding.isEmbedding.homeomorphImage A).isHomeomorph
      |>.topologicalKrullDim_eq).symm
  have h := hbad s _ (hA.1.image _ i.continuous.continuousOn) hsub hfib
  rw [hdim'] at h
  exact lt_irrefl _ h

/-- Over `ℂ`, a point whose closure has dimension `n` has relative dimension `n` (Stacks, Tag
02QO). -/
private theorem relativeDimension_eq_of_topologicalKrullDim_closure_eq' {X : Scheme.{0}}
    (p : X ⟶ Spec (.of ℂ)) [LocallyOfFiniteType p] (x : X) (n : ℕ)
    (h : topologicalKrullDim (closure ({x} : Set X)) = (n : WithBot ℕ∞)) :
    Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction p x =
      n := by
  have hnn := Stacks.Chow.relativeDimension_nonneg (Stacks.Chow.fieldChowSituation ℂ)
    (fun _ _ ↦ rfl) p x
  rw [Stacks.Chow.topologicalKrullDim_closure_singleton_eq ℂ p x] at h
  have h' : (Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      p x).toNat = n := by
    exact_mod_cast h
  omega

/-- The image of the closure of a point `x` of `X` under `h : X ⟶ X'` is the range of the
integral closed subscheme `closure {x}` (Stacks, `integralComponentAt`) followed by `h`. -/
theorem range_integralComponentAt_subschemeι_comp {X X' : Scheme.{0}} (x : X) (h : X ⟶ X') :
    Set.range ((Stacks.Chow.integralComponentAt x).subschemeι ≫ h).base =
      h.base '' closure {x} := by
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Scheme.IdealSheafData.range_subschemeι, Stacks.Chow.coe_support_integralComponentAt]

/-- **A curve of `S` over a point of the base is a component of the fibre** (fibre components of
dimension at most one). For an immersion
`j_V = a ≫ ι : V ⟶ Z` (open then closed) over a family `f : V ⟶ B` whose fibres have
one-dimensional components, a curve `c : C ⟶ Z` in `S ∩ r⁻¹(j_B(s))` is isomorphic to a
component of the fibre `V_s`, compatibly with `j_V`. -/
theorem exists_component_of_immersion_of_le {Z Y V B X₀ : Scheme.{0}} [Z.Over (Spec (.of ℂ))]
    [Y.Over (Spec (.of ℂ))] [V.Over (Spec (.of ℂ))] [B.Over (Spec (.of ℂ))]
    [IsSmoothVariety ℂ (B ↘ Spec (.of ℂ))]
    [LocallyOfFiniteType (Z ↘ Spec (.of ℂ))] [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))]
    {r : Z ⟶ Y} [r.IsOver (Spec (.of ℂ))] {S : Set Z} (hS : IsClosed S)
    (f : V ⟶ B) [f.IsOver (Spec (.of ℂ))] (jB : B ⟶ Y) [jB.IsOver (Spec (.of ℂ))]
    (hjBinj : Function.Injective jB.base) (jV : V ⟶ Z) [jV.IsOver (Spec (.of ℂ))]
    (a : V ⟶ X₀) [IsOpenImmersion a] (ι : X₀ ⟶ Z) [IsClosedImmersion ι] (hjV : jV = a ≫ ι)
    (comm : f ≫ jB = jV ≫ r)
    (hrange : S ∩ r.base ⁻¹' Set.range jB.base ⊆ Set.range jV.base)
    (s : ParameterPoint B)
    (hdim : ∀ A ∈ irreducibleComponents (ParameterPoint.fibre f s),
      topologicalKrullDim A ≤ ((1 : ℕ) : WithBot ℕ∞))
    (C : Scheme.{0}) [C.Over (Spec (.of ℂ))] [IsIntegral C]
    [LocallyOfFiniteType (C ↘ Spec (.of ℂ))] [QuasiCompact (C ↘ Spec (.of ℂ))] (c : C ⟶ Z)
    [IsClosedImmersion c]
    [c.IsOver (Spec (.of ℂ))] (hC1 : ((1 : ℕ) : WithBot ℕ∞) = dimension C)
    (hcS : pointsOver (K := ℂ) (Set.range c) ⊆ pointsOver (K := ℂ) S)
    (hcr : pointsOver (K := ℂ) (Set.range c) ⊆ mapFun r ⁻¹' {mapFun (K := ℂ) jB s.complexPoint}) :
    ∃ (y : ParameterPoint.fibre f s) (_ : y ∈ genericPoints (ParameterPoint.fibre f s))
      (_ : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
        (ParameterPoint.fibre f s ↘ Spec (.of ℂ)) y = (1 : ℕ))
      (g : C ⟶ (Stacks.Chow.integralComponentAt y).subscheme) (_ : IsIso g)
      (_ : g.IsOver (Spec (.of ℂ))),
      g ≫ (Stacks.Chow.integralComponentAt y).subschemeι ≫ ParameterPoint.fibreι f s ≫ jV = c := by
  classical
  haveI : LocallyOfFiniteType jV := by rw [hjV]; infer_instance
  haveI : LocallyOfFiniteType (V ↘ Spec (.of ℂ)) := by
    rw [← comp_over jV (Spec (.of ℂ))]; infer_instance
  set y := s.point with hydef
  have hy : (mapFun (K := ℂ) jB s.complexPoint).toHom (IsLocalRing.closedPoint ℂ) = jB.base y := by
    rw [toHom_closedPoint_mapFun, ParameterPoint.complexPoint_toHom_closedPoint]
  -- the curve lies in `S ∩ r⁻¹(j_B(s))`
  have hrc : Set.range c.base ⊆ S ∩ r.base ⁻¹' {jB.base y} := by
    refine subset_of_pointsOver_subset c.isClosedEmbedding.isClosed_range
      (hS.inter (hy ▸ (isClosed_singleton_toHom' _).preimage r.continuous)) fun q hq ↦ ?_
    refine ⟨hcS hq, ?_⟩
    have h2 : mapFun r q = mapFun (K := ℂ) jB s.complexPoint := hcr hq
    change r.base _ = _
    rw [← toHom_closedPoint_mapFun, h2, hy]
  have hrcV : Set.range c.base ⊆ Set.range jV.base := fun z hz ↦
    hrange ⟨(hrc hz).1, by rw [Set.mem_preimage, (hrc hz).2]; exact ⟨y, rfl⟩⟩
  -- lift `c` through `ι` and `a`
  have hkerι : ι.ker ≤ c.ker := by
    rw [c.ker_eq_vanishingIdeal_closure_range, ← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal]
    change closure (Set.range c.base) ⊆ (ι.ker.support : Set Z)
    rw [Scheme.Hom.support_ker]
    refine closure_mono (hrcV.trans ?_)
    rw [hjV, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    exact Set.image_subset_range _ _
  set c₁ := IsClosedImmersion.lift ι c hkerι with hc₁def
  have hc₁ : c₁ ≫ ι = c := IsClosedImmersion.lift_fac _ _ _
  have hrc₁ : Set.range c₁.base ⊆ Set.range a.base := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨v, hv⟩ := hrcV ⟨x, rfl⟩
    refine ⟨v, ι.isClosedEmbedding.injective ?_⟩
    change (a ≫ ι).base v = (c₁ ≫ ι).base x
    rw [← hjV, hc₁]
    exact hv
  set c₂ := IsOpenImmersion.lift a c₁ hrc₁ with hc₂def
  have hc₂ : c₂ ≫ jV = c := by
    rw [hjV, ← Category.assoc, IsOpenImmersion.lift_fac, hc₁]
  -- `c₂` lands in the fibre over `s`
  have hfc : ∀ x, f.base (c₂.base x) = y := fun x ↦ by
    apply hjBinj
    change (c₂ ≫ f ≫ jB).base x = _
    rw [comm, ← Category.assoc, hc₂]
    exact (hrc ⟨x, rfl⟩).2
  have hrange_cf : Set.range (c₂ ≫ f).base = {y} := by
    obtain ⟨x₀⟩ : Nonempty C := inferInstance
    ext w
    refine ⟨fun ⟨x, hx⟩ ↦ hx ▸ hfc x, fun hw ↦ ⟨x₀, (hfc x₀).trans hw.symm⟩⟩
  have hker_s : s.ι.ker ≤ (c₂ ≫ f).ker := by
    rw [(c₂ ≫ f).ker_eq_vanishingIdeal_closure_range, s.ι.ker_eq_vanishingIdeal_closure_range,
      hrange_cf, ParameterPoint.range_ι]
  set c₃' := IsClosedImmersion.lift s.ι (c₂ ≫ f) hker_s with hc₃'def
  have hc₃' : c₃' ≫ s.ι = c₂ ≫ f := IsClosedImmersion.lift_fac _ _ _
  set c₃ : C ⟶ ParameterPoint.fibre f s := Limits.pullback.lift c₂ c₃' hc₃'.symm with hc₃def
  have hc₃ : c₃ ≫ ParameterPoint.fibreι f s = c₂ := Limits.pullback.lift_fst _ _ _
  set g := ParameterPoint.fibreι f s ≫ jV with hgdef
  have hc : c₃ ≫ g = c := by rw [hgdef, ← Category.assoc, hc₃, hc₂]
  -- `c₃` is a closed immersion
  haveI : IsPreimmersion jV := by rw [hjV]; infer_instance
  haveI : IsPreimmersion (c₃ ≫ g) := by rw [hc]; infer_instance
  haveI : IsPreimmersion c₃ := IsPreimmersion.of_comp c₃ g
  have hginj : Function.Injective g.base := g.isEmbedding.injective
  have hrange₃ : Set.range c₃.base = g.base ⁻¹' Set.range c.base := by
    ext v
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, by rw [← hc]; rfl⟩
    · rintro ⟨x, hx⟩
      refine ⟨x, hginj ?_⟩
      change (c₃ ≫ g).base x = _
      rw [hc]
      exact hx
  haveI : IsClosedImmersion c₃ := .of_isPreimmersion c₃
    (hrange₃ ▸ c.isClosedEmbedding.isClosed_range.preimage g.continuous)
  -- its image is a component of the fibre
  set A := Set.range c₃.base with hAdef
  have hAirr : IsIrreducible A := by
    have := (irreducibleSpace_def C).1 inferInstance
    rw [hAdef, ← Set.image_univ]
    exact this.image _ c₃.continuous.continuousOn
  have hAcl : IsClosed A := c₃.isClosedEmbedding.isClosed_range
  have hAdim : topologicalKrullDim A = ((1 : ℕ) : WithBot ℕ∞) := by
    rw [hC1]
    exact c₃.isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph.topologicalKrullDim_eq.symm
  obtain ⟨A', hA', hAA'⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible A hAirr
  have hAeq : A = A' := by
    by_contra hne
    have hlt := MMP.topologicalKrullDim_lt_of_subset_of_ne hA'.1 hAcl hAA' hne
      (ne_top_of_le_ne_top (by decide) (hdim A' hA'))
    rw [hAdim] at hlt
    exact lt_irrefl _ (hlt.trans_le (hdim A' hA'))
  have hAc : A ∈ irreducibleComponents (ParameterPoint.fibre f s) := hAeq ▸ hA'
  haveI := locallyOfFiniteType_fibre_over f s
  set η := hAirr.genericPoint with hηdef
  have hyA : closure ({η} : Set (ParameterPoint.fibre f s)) = A := by
    have h := hAirr.isGenericPoint_genericPoint_closure
    rw [hAcl.closure_eq] at h
    exact h.def
  have hyg : η ∈ genericPoints (ParameterPoint.fibre f s) := by
    change closure ({η} : Set (ParameterPoint.fibre f s)) ∈
      irreducibleComponents (ParameterPoint.fibre f s)
    rw [hyA]
    exact hAc
  have hy1 : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (ParameterPoint.fibre f s ↘ Spec (.of ℂ)) η = (1 : ℕ) :=
    relativeDimension_eq_of_topologicalKrullDim_closure_eq' _ η 1 (by rw [hyA]; exact hAdim)
  have hcl : Closeds.closure (Set.range c₃.base) = Closeds.closure {η} :=
    Closeds.ext (by rw [Closeds.coe_closure, Closeds.coe_closure, hyA, hAcl.closure_eq])
  have hker' : (Stacks.Chow.integralComponentAt η).subschemeι.ker = c₃.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, c₃.ker_eq_vanishingIdeal_closure_range, hcl]
    rfl
  set g' := IsClosedImmersion.lift (Stacks.Chow.integralComponentAt η).subschemeι c₃ hker'.le
    with hg'def
  have hg' : g' ≫ (Stacks.Chow.integralComponentAt η).subschemeι = c₃ :=
    IsClosedImmersion.lift_fac _ _ _
  have hfin : g' ≫ (Stacks.Chow.integralComponentAt η).subschemeι ≫
      ParameterPoint.fibreι f s ≫ jV = c := by
    rw [← Category.assoc, hg', ← hgdef, hc]
  refine ⟨η, hyg, hy1, g', IsClosedImmersion.isIso_lift _ _ hker', ⟨?_⟩, hfin⟩
  change g' ≫ (Stacks.Chow.integralComponentAt η).subschemeι ≫ ParameterPoint.fibreι f s ≫
    V ↘ Spec (.of ℂ) = C ↘ Spec (.of ℂ)
  rw [← comp_over jV (Spec (.of ℂ)), ← comp_over c (Spec (.of ℂ)), ← hfin]
  simp only [Category.assoc]

/-- In an integral scheme of finite type over `ℂ` of dimension `n + 1`, a prime divisor has
dimension `n`. -/
theorem topologicalKrullDim_primeDivisor_support {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [IsIntegral X] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] {n : ℕ}
    (hX : topologicalKrullDim X = ((n + 1 : ℕ) : WithBot ℕ∞)) (D : Mori.PrimeDivisor X) :
    topologicalKrullDim (D.support : Set X) = ((n : ℕ) : WithBot ℕ∞) := by
  have h := ConductorBlowup.topologicalKrullDim_closure_add_coheight D.genericPoint
  rw [D.coheight_genericPoint, hX] at h
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  revert h
  generalize topologicalKrullDim (closure ({D.genericPoint} : Set X)) = e
  intro h
  induction e using WithBot.recBotCoe with
  | bot => exact (WithBot.bot_ne_coe (a := ((n + 1 : ℕ) : ℕ∞)) (by exact_mod_cast h)).elim
  | coe e =>
    have h' : e + 1 = ((n + 1 : ℕ) : ℕ∞) :=
      WithBot.coe_injective (by rw [WithBot.coe_add]; exact_mod_cast h)
    induction e using ENat.recTopCoe with
    | top => exact absurd h' (by rw [top_add]; exact ENat.top_ne_coe _)
    | coe e =>
      have : e + 1 = n + 1 := by exact_mod_cast h'
      rw [(by omega : e = n)]; rfl

/-- `x < 2` in `WithBot ℕ∞` means `x ≤ 1`. -/
private theorem withBot_le_one_of_lt_two {e : WithBot ℕ∞} (hlt : e < ((2 : ℕ) : WithBot ℕ∞)) :
    e ≤ ((1 : ℕ) : WithBot ℕ∞) := by
  induction e using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe e =>
    induction e using ENat.recTopCoe with
    | top => exact absurd hlt (by decide)
    | coe e =>
      have h0 : ((e : ℕ∞)) < ((2 : ℕ) : ℕ∞) := WithBot.coe_lt_coe.1 hlt
      have h1 : e < 2 := ENat.coe_lt_coe.1 h0
      have h2 : e ≤ 1 := by omega
      exact WithBot.coe_le_coe.2 (ENat.coe_le_coe.2 h2)

/-- The irreducible components of a proper fibre of a morphism from an irreducible surface have
dimension at most one. -/
theorem topologicalKrullDim_le_one_of_mem_irreducibleComponents_fibre {V B : Scheme.{0}}
    [IrreducibleSpace V] (f : V ⟶ B) (hV : topologicalKrullDim V = ((2 : ℕ) : WithBot ℕ∞))
    (s : ParameterPoint B) (hne : ∃ v, f.base v ≠ s.point)
    (A : Set (ParameterPoint.fibre f s))
    (hA : A ∈ irreducibleComponents (ParameterPoint.fibre f s)) :
    topologicalKrullDim A ≤ ((1 : ℕ) : WithBot ℕ∞) := by
  have h1 : topologicalKrullDim A ≤ topologicalKrullDim (ParameterPoint.fibre f s) :=
    topologicalKrullDim_subspace_le _ A
  have h2 : topologicalKrullDim (ParameterPoint.fibre f s) =
      topologicalKrullDim (f.base ⁻¹' {s.point}) :=
    (ParameterPoint.fibreHomeo f s).isHomeomorph.topologicalKrullDim_eq
  have hcl : IsClosed (f.base ⁻¹' {s.point}) := by
    rw [← ParameterPoint.range_fibreι]
    exact (ParameterPoint.fibreι f s).isClosedEmbedding.isClosed_range
  have hne' : f.base ⁻¹' {s.point} ≠ Set.univ := by
    obtain ⟨v, hv⟩ := hne
    exact fun h ↦ hv (h ▸ Set.mem_univ v : v ∈ f.base ⁻¹' {s.point})
  have hU : topologicalKrullDim (Set.univ : Set V) = ((2 : ℕ) : WithBot ℕ∞) := by
    rw [(Homeomorph.Set.univ V).isHomeomorph.topologicalKrullDim_eq, hV]
  have hlt := MMP.topologicalKrullDim_lt_of_subset_of_ne
    (IrreducibleSpace.isIrreducible_univ V) hcl (Set.subset_univ _) hne'
    (by rw [hU]; decide)
  rw [hU] at hlt
  exact withBot_le_one_of_lt_two (h1.trans_lt (h2 ▸ hlt))

/-- An immersion `ι ≫ j_G` restricted to a fibre of `f = ι ≫ g` is a closed immersion when its
image is the trace of a closed set over a closed point. -/
theorem isClosedImmersion_fibreι_comp_of_range {V G B Z Y : Scheme.{0}} (f : V ⟶ B)
    (ι : V ⟶ G) (jG : G ⟶ Z) [IsPreimmersion (ι ≫ jG)] (jB : B ⟶ Y) (r : Z ⟶ Y)
    (hjB : Function.Injective jB.base) (comm : f ≫ jB = (ι ≫ jG) ≫ r) {S : Set Z}
    (hS : IsClosed S) (h1 : Set.range (ι ≫ jG).base ⊆ S)
    (h2 : S ∩ r.base ⁻¹' Set.range jB.base ⊆ Set.range (ι ≫ jG).base) (s : ParameterPoint B)
    (hpt : IsClosed {jB.base s.point}) :
    IsClosedImmersion (ParameterPoint.fibreι f s ≫ ι ≫ jG) := by
  have hrange : Set.range (ParameterPoint.fibreι f s ≫ ι ≫ jG).base =
      S ∩ r.base ⁻¹' {jB.base s.point} := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨h1 ⟨_, rfl⟩, ?_⟩
      have hx : (ParameterPoint.fibreι f s).base x ∈ f.base ⁻¹' {s.point} := by
        rw [← ParameterPoint.range_fibreι]; exact ⟨x, rfl⟩
      change ((ParameterPoint.fibreι f s ≫ ι ≫ jG) ≫ r).base x = _
      rw [Category.assoc, Category.assoc, ← Category.assoc ι, ← comm]
      change jB.base (f.base ((ParameterPoint.fibreι f s).base x)) = _
      rw [show f.base ((ParameterPoint.fibreι f s).base x) = s.point from hx]
    · rintro ⟨hzS, hzr⟩
      obtain ⟨v, rfl⟩ := h2 ⟨hzS, by rw [Set.mem_preimage, hzr]; exact ⟨_, rfl⟩⟩
      have hv : f.base v = s.point := by
        apply hjB
        rw [← hzr]
        change (f ≫ jB).base v = ((ι ≫ jG) ≫ r).base v
        rw [comm]
      obtain ⟨w, hw⟩ : v ∈ Set.range (ParameterPoint.fibreι f s).base := by
        rw [ParameterPoint.range_fibreι]; exact hv
      refine ⟨w, ?_⟩
      change (ι ≫ jG).base ((ParameterPoint.fibreι f s).base w) = _
      rw [hw]
  exact .of_isPreimmersion _ (hrange ▸ hS.inter (hpt.preimage r.continuous))

section primeDivisorFamily

variable {Z Y : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))] [IsComplexScheme Z]
  [CompactSpace Z] [IsLocallyNoetherian Z] [IsNormal Z] [IsIntegral Y] [IsLocallyNoetherian Y]
  [IsNormal Y] {r : Z ⟶ Y} [r.IsOver (Spec (.of ℂ))] {F D : Divisor Z}

/-- **The algebraic family of a prime divisor of a component of `F` over a general open `U` of
`T`.** For a component `E` of `F` and a prime divisor `P` of `E`: a family `g : G → B` of the
fibres of `E` over a non-singular complex curve `B`, with `B(ℂ)` embedded onto `(U ∩ T)(ℂ)` and
`G(ℂ)` onto the points of `E` over `U`, and a proper `ι : V → G` from a complex surface onto `P`
over `U`, with `f = ι ≫ g` dominant, whose fibres have one-dimensional components of multiplicity
one, every curve of `P` over a point of `B` being one of them. -/
structure PrimeDivisorFamily (r : Z ⟶ Y) [r.IsOver (Spec (.of ℂ))] (T : IrreducibleCloseds Y)
    (E : Mori.PrimeDivisor Z) (P : Mori.PrimeDivisor E.idealSheaf.subscheme) (U : Y.Opens) where
  /-- The base curve. -/
  B : Scheme.{0}
  [overB : B.Over (Spec (.of ℂ))]
  [smoothB : IsSmoothVariety ℂ (B ↘ Spec (.of ℂ))]
  /-- The base is a smooth curve. -/
  dim_B : SmoothOfRelativeDimension 1 (B ↘ Spec (.of ℂ))
  /-- The base mapped to `Y`. -/
  jB : B ⟶ Y
  [isOver_jB : jB.IsOver (Spec (.of ℂ))]
  injective_jB : Function.Injective jB.base
  isEmbedding_jB : Topology.IsEmbedding (mapFun (K := ℂ) jB)
  /-- The complex points of `B` are the complex points of `Y` lying over `U ∩ T`. -/
  range_jB : Set.range (mapFun (K := ℂ) jB) = pointsOver (K := ℂ) ((U : Set Y) ∩ T)
  /-- The family of the fibres of `E`. -/
  G : Scheme.{0}
  [overG : G.Over (Spec (.of ℂ))]
  [complexG : IsComplexScheme G]
  /-- The projection of the family of fibres onto the base. -/
  g : G ⟶ B
  [isOver_g : g.IsOver (Spec (.of ℂ))]
  /-- The family of the fibres of `E` mapped to `Z`. -/
  jG : G ⟶ Z
  [isOver_jG : jG.IsOver (Spec (.of ℂ))]
  comm_G : g ≫ jB = jG ≫ r
  isEmbedding_jG : Topology.IsEmbedding (mapFun (K := ℂ) jG)
  /-- The complex points of `G` are the complex points of `E` lying over `U`. -/
  range_jG : Set.range (mapFun (K := ℂ) jG) =
    pointsOver (K := ℂ) (E.support : Set Z) ∩ mapFun r ⁻¹' pointsOver (K := ℂ) (U : Set Y)
  /-- The total space of the family of curves cut by `P`, a complex surface. -/
  V : Scheme.{0}
  [overV : V.Over (Spec (.of ℂ))]
  [complexV : IsComplexScheme V]
  [integralV : IsIntegral V]
  dimension_V : ((1 + 1 : ℕ) : WithBot ℕ∞) = dimension V
  /-- The surface mapped to the family of fibres of `E`. -/
  ι : V ⟶ G
  [isOver_ι : ι.IsOver (Spec (.of ℂ))]
  [isProper_ι : IsProper ι]
  /-- The family of curves. -/
  f : V ⟶ B
  [isOver_f : f.IsOver (Spec (.of ℂ))]
  [isDominant_f : IsDominant f]
  hf : ι ≫ g = f
  mult_fibre : ∀ (s : ParameterPoint B) (ξ : genericPoints (ParameterPoint.fibre f s)),
    Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (ParameterPoint.fibre f s ↘ Spec (.of ℂ)) ξ.1 = (1 : ℕ) →
    Stacks.Chow.componentMultiplicity (𝟙 (ParameterPoint.fibre f s)) ξ = 1
  /-- Each fibre of `f` is a closed subscheme of `Z` through `ι ≫ jG`. -/
  isClosedImmersion_fibre : ∀ s : ParameterPoint B,
    IsClosedImmersion (ParameterPoint.fibreι f s ≫ ι ≫ jG)
  range_subset : Set.range (ι ≫ jG).base ⊆ E.idealSheaf.subschemeι.base '' P.support
  subset_range : (E.idealSheaf.subschemeι.base '' P.support) ∩ r.base ⁻¹' Set.range jB.base ⊆
    Set.range (ι ≫ jG).base
  /-- A curve of `P` over a point `s` of `B` is a component of the fibre `V_s`. -/
  exists_component : ∀ (s : ParameterPoint B) (C : Scheme.{0}) [C.Over (Spec (.of ℂ))]
    [IsIntegral C] [LocallyOfFiniteType (C ↘ Spec (.of ℂ))] [QuasiCompact (C ↘ Spec (.of ℂ))]
    (c : C ⟶ Z) [IsClosedImmersion c] [c.IsOver (Spec (.of ℂ))],
    ((1 : ℕ) : WithBot ℕ∞) = dimension C →
    pointsOver (K := ℂ) (Set.range c) ⊆
      pointsOver (K := ℂ) (E.idealSheaf.subschemeι.base '' P.support) →
    pointsOver (K := ℂ) (Set.range c) ⊆ mapFun r ⁻¹' {mapFun (K := ℂ) jB s.complexPoint} →
    ∃ (y : ParameterPoint.fibre f s) (_ : y ∈ genericPoints (ParameterPoint.fibre f s))
      (_ : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
        (ParameterPoint.fibre f s ↘ Spec (.of ℂ)) y = (1 : ℕ))
      (e : C ⟶ (Stacks.Chow.integralComponentAt y).subscheme) (_ : IsIso e)
      (_ : e.IsOver (Spec (.of ℂ))),
      e ≫ (Stacks.Chow.integralComponentAt y).subschemeι ≫ ParameterPoint.fibreι f s ≫ ι ≫ jG = c

attribute [instance] PrimeDivisorFamily.overB PrimeDivisorFamily.smoothB
  PrimeDivisorFamily.isOver_jB PrimeDivisorFamily.overG PrimeDivisorFamily.complexG
  PrimeDivisorFamily.isOver_g PrimeDivisorFamily.isOver_jG PrimeDivisorFamily.overV
  PrimeDivisorFamily.complexV PrimeDivisorFamily.integralV PrimeDivisorFamily.isOver_ι
  PrimeDivisorFamily.isProper_ι PrimeDivisorFamily.isOver_f PrimeDivisorFamily.isDominant_f

variable {T : IrreducibleCloseds Y} {E : Mori.PrimeDivisor Z}
  {P : Mori.PrimeDivisor E.idealSheaf.subscheme} {U : Y.Opens}

/-- On complex points, `jG` followed by `r` equals `g` followed by `jB`. -/
theorem PrimeDivisorFamily.mapFun_r_jG (𝔉 : PrimeDivisorFamily r T E P U)
    (v : UnderlyingSpace ℂ 𝔉.G) :
    mapFun r (mapFun (K := ℂ) 𝔉.jG v) = mapFun (K := ℂ) 𝔉.jB (mapFun (K := ℂ) 𝔉.g v) := by
  apply UnderlyingSpace.ext
  change (v.toHom ≫ 𝔉.jG) ≫ r = (v.toHom ≫ 𝔉.g) ≫ 𝔉.jB
  rw [Category.assoc, Category.assoc, 𝔉.comm_G]

/-- The open of `B(ℂ)` over an open `O` of `Y(ℂ)`. -/
def PrimeDivisorFamily.baseOpens (𝔉 : PrimeDivisorFamily r T E P U)
    {O : Set (UnderlyingSpace ℂ Y)} (hO : IsOpen O) :
    TopologicalSpace.Opens (TopCat.of (UnderlyingSpace ℂ 𝔉.B)) :=
  ⟨mapFun (K := ℂ) 𝔉.jB ⁻¹' O, hO.preimage (continuous_mapFun _)⟩

/-- A complex point `w` of `B` lies in `baseOpens hO` iff its image in `Y(ℂ)` lies in `O` and over
`T`. -/
theorem PrimeDivisorFamily.mem_baseOpens_iff (𝔉 : PrimeDivisorFamily r T E P U)
    {O : Set (UnderlyingSpace ℂ Y)} (hO : IsOpen O) (w : UnderlyingSpace ℂ 𝔉.B) :
    w ∈ 𝔉.baseOpens hO ↔ mapFun (K := ℂ) 𝔉.jB w ∈ O ∩ pointsOver (K := ℂ) (T : Set Y) := by
  refine ⟨fun h ↦ ⟨h, ?_⟩, fun h ↦ h.1⟩
  have h1 : mapFun (K := ℂ) 𝔉.jB w ∈ pointsOver (K := ℂ) ((U : Set Y) ∩ T) :=
    𝔉.range_jB ▸ Set.mem_range_self w
  rw [pointsOver_inter] at h1
  exact h1.2

/-- The points of `E` in the fibre `F_b`. -/
abbrev fibrePointsIn (F : Divisor Z) (r : Z ⟶ Y) [r.IsOver (Spec (.of ℂ))] (E : Set Z)
    (b : UnderlyingSpace ℂ Y) : Set (UnderlyingSpace ℂ Z) :=
  pointsOver (K := ℂ) E ∩ (pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b})

end primeDivisorFamily

section familyLemmas

variable {Z Y : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))] [IsComplexScheme Z]
  [CompactSpace Z] [IsLocallyNoetherian Z] [IsNormal Z] [IsIntegral Y] [IsLocallyNoetherian Y]
  [IsNormal Y] {r : Z ⟶ Y} [r.IsOver (Spec (.of ℂ))] {F D : Divisor Z}
  {T : IrreducibleCloseds Y} {E : Mori.PrimeDivisor Z}
  {P : Mori.PrimeDivisor E.idealSheaf.subscheme} {U : Y.Opens}

/-- The image in `Z` of the fibre `V_u` lies in `P ∩ r⁻¹(j_B(u))`. -/
theorem PrimeDivisorFamily.range_fibre_subset (𝔉 : PrimeDivisorFamily r T E P U)
    (u : ParameterPoint 𝔉.B) :
    Set.range (ParameterPoint.fibreι 𝔉.f u ≫ 𝔉.ι ≫ 𝔉.jG).base ⊆
      E.idealSheaf.subschemeι.base '' P.support ∩ r.base ⁻¹' {𝔉.jB.base u.point} := by
  rintro _ ⟨x, rfl⟩
  refine ⟨𝔉.range_subset ⟨_, rfl⟩, ?_⟩
  change ((ParameterPoint.fibreι 𝔉.f u ≫ 𝔉.ι ≫ 𝔉.jG) ≫ r).base x = _
  have h : (ParameterPoint.fibreι 𝔉.f u ≫ 𝔉.ι ≫ 𝔉.jG) ≫ r =
      (ParameterPoint.fibreι 𝔉.f u ≫ 𝔉.f) ≫ 𝔉.jB := by
    rw [← 𝔉.hf]; simp only [Category.assoc, 𝔉.comm_G]
  rw [h]
  have hx : (ParameterPoint.fibreι 𝔉.f u).base x ∈ 𝔉.f.base ⁻¹' {u.point} := by
    rw [← ParameterPoint.range_fibreι]; exact ⟨x, rfl⟩
  change 𝔉.jB.base (𝔉.f.base ((ParameterPoint.fibreι 𝔉.f u).base x)) = _
  rw [show 𝔉.f.base ((ParameterPoint.fibreι 𝔉.f u).base x) = u.point from hx]

/-- Conversely, every point of `P ∩ r⁻¹(j_B(u))` lies in the image of the fibre `V_u`. -/
theorem PrimeDivisorFamily.subset_range_fibre (𝔉 : PrimeDivisorFamily r T E P U)
    (u : ParameterPoint 𝔉.B) :
    E.idealSheaf.subschemeι.base '' P.support ∩ r.base ⁻¹' {𝔉.jB.base u.point} ⊆
      Set.range (ParameterPoint.fibreι 𝔉.f u ≫ 𝔉.ι ≫ 𝔉.jG).base := by
  rintro z ⟨hzP, hzr⟩
  obtain ⟨v, rfl⟩ := 𝔉.subset_range ⟨hzP, by rw [Set.mem_preimage, hzr]; exact ⟨_, rfl⟩⟩
  have hv : 𝔉.f.base v = u.point := by
    apply 𝔉.injective_jB
    rw [← hzr]
    change (𝔉.f ≫ 𝔉.jB).base v = ((𝔉.ι ≫ 𝔉.jG) ≫ r).base v
    rw [← 𝔉.hf]; simp only [Category.assoc, 𝔉.comm_G]
  obtain ⟨w, hw⟩ : v ∈ Set.range (ParameterPoint.fibreι 𝔉.f u).base := by
    rw [ParameterPoint.range_fibreι]; exact hv
  refine ⟨w, ?_⟩
  change (𝔉.ι ≫ 𝔉.jG).base ((ParameterPoint.fibreι 𝔉.f u).base w) = _
  rw [hw]

/-- The image in `Z` of an irreducible closed subset of a fibre `V_u` lies in a component `G_u`
of `E_u` or misses it, when the components of `E_u` are pairwise disjoint. -/
theorem PrimeDivisorFamily.range_subset_or_disjoint (𝔉 : PrimeDivisorFamily r T E P U)
    (u : ParameterPoint 𝔉.B) (Gs : Subvariety E.idealSheaf.subscheme)
    (hGs : Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.idealSheaf.subschemeι ≫ r).base ⁻¹'
      {𝔉.jB.base u.point}) (Gs.support : Set _))
    (hdisj : ∀ (A B : Set E.idealSheaf.subscheme),
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.idealSheaf.subschemeι ≫ r).base ⁻¹'
        {𝔉.jB.base u.point}) A →
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.idealSheaf.subschemeι ≫ r).base ⁻¹'
        {𝔉.jB.base u.point}) B → A ≠ B → Disjoint A B)
    (y : ParameterPoint.fibre 𝔉.f u) :
    Set.range ((Stacks.Chow.integralComponentAt y).subschemeι ≫ ParameterPoint.fibreι 𝔉.f u ≫
        𝔉.ι ≫ 𝔉.jG).base ⊆ E.idealSheaf.subschemeι.base '' (Gs.support : Set _) ∨
      Disjoint (Set.range ((Stacks.Chow.integralComponentAt y).subschemeι ≫
          ParameterPoint.fibreι 𝔉.f u ≫ 𝔉.ι ≫ 𝔉.jG).base)
        (E.idealSheaf.subschemeι.base '' (Gs.support : Set _)) := by
  haveI := Stacks.Chow.isIntegral_integralComponentAt y
  set K := Set.range ((Stacks.Chow.integralComponentAt y).subschemeι ≫
    ParameterPoint.fibreι 𝔉.f u ≫ 𝔉.ι ≫ 𝔉.jG).base with hK
  have hKsub : K ⊆ E.idealSheaf.subschemeι.base '' P.support ∩
      r.base ⁻¹' {𝔉.jB.base u.point} := by
    rintro _ ⟨x, rfl⟩
    exact 𝔉.range_fibre_subset u ⟨(Stacks.Chow.integralComponentAt y).subschemeι.base x, rfl⟩
  have hKirr : IsIrreducible K := by
    rw [hK, ← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ (Scheme.Hom.continuous _).continuousOn
  have hKE : K ⊆ Set.range E.idealSheaf.subschemeι.base := fun z hz ↦ by
    obtain ⟨x, -, hx⟩ := (hKsub hz).1
    exact ⟨x, hx⟩
  set K' := E.idealSheaf.subschemeι.base ⁻¹' K with hK'
  have hK'irr : IsIrreducible K' :=
    isIrreducible_preimage_of_isEmbedding' E.idealSheaf.subschemeι.isClosedEmbedding.isEmbedding
      hKirr hKE
  have hK'sub : K' ⊆ (E.idealSheaf.subschemeι ≫ r).base ⁻¹' {𝔉.jB.base u.point} :=
    fun x hx ↦ (hKsub hx).2
  have hKK' : K = E.idealSheaf.subschemeι.base '' K' :=
    (Set.image_preimage_eq_of_subset hKE).symm
  obtain ⟨M, hK'M, hM⟩ := exists_subset_maximal_of_isIrreducible hK'irr hK'sub
  by_cases hMG : M = Gs.support
  · left
    rw [hKK']
    exact Set.image_mono (hMG ▸ hK'M)
  · right
    rw [hKK']
    exact (Set.disjoint_image_iff E.idealSheaf.subschemeι.isClosedEmbedding.injective).2
      ((hdisj M _ hM hGs hMG).mono_left hK'M)

/-- The range of `C.ι ≫ h`, for a subvariety `C` of `X`, is the image of the support of `C`. -/
theorem range_ι_comp_eq_image_support {X X' : Scheme.{0}} (C : Subvariety X) (h : X ⟶ X') :
    Set.range (C.ι ≫ h).base = h.base '' C.support := by
  rw [Subvariety.support_eq, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Scheme.IdealSheafData.range_subschemeι]

/-- **A component of `V_u` inside `G_u` is a curve cut on `G_u` by `P`.** A one-dimensional
irreducible component `C'` of the fibre `V_u` whose image in `Z` lies in a component `G_u` of
`E_u` is, as a subvariety of `G_u`, a maximal irreducible subset of `G_u ∩ P`. -/
theorem PrimeDivisorFamily.exists_subvariety_of_range_subset (𝔉 : PrimeDivisorFamily r T E P U)
    (u : ParameterPoint 𝔉.B) (Gs : Subvariety E.idealSheaf.subscheme)
    (hGs : (Gs.support : Set _) ⊆ (E.idealSheaf.subschemeι ≫ r).base ⁻¹' {𝔉.jB.base u.point})
    (y : ParameterPoint.fibre 𝔉.f u) (hC' : y ∈ genericPoints (ParameterPoint.fibre 𝔉.f u))
    (hy1 : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (ParameterPoint.fibre 𝔉.f u ↘ Spec (.of ℂ)) y = (1 : ℕ))
    (hsub : Set.range ((Stacks.Chow.integralComponentAt y).subschemeι ≫
      ParameterPoint.fibreι 𝔉.f u ≫ 𝔉.ι ≫ 𝔉.jG).base ⊆
      E.idealSheaf.subschemeι.base '' (Gs.support : Set _)) :
    ∃ C : {V : Subvariety Gs.toScheme // V.HasDim 1},
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ Gs.ι.base ⁻¹' (P.support : Set _))
        (C.1.support : Set _) ∧
      Set.range (C.1.ι ≫ Gs.ι ≫ E.idealSheaf.subschemeι).base =
        Set.range ((Stacks.Chow.integralComponentAt y).subschemeι ≫
          ParameterPoint.fibreι 𝔉.f u ≫ 𝔉.ι ≫ 𝔉.jG).base := by
  haveI := Stacks.Chow.isIntegral_integralComponentAt y
  set h := ParameterPoint.fibreι 𝔉.f u ≫ 𝔉.ι ≫ 𝔉.jG with hh
  haveI : IsClosedImmersion h := 𝔉.isClosedImmersion_fibre u
  set j := Gs.ι ≫ E.idealSheaf.subschemeι with hj
  set K := Set.range ((Stacks.Chow.integralComponentAt y).subschemeι ≫ h).base with hK
  have hK' : K = h.base '' closure {y} := range_integralComponentAt_subschemeι_comp _ _
  have hKcl : IsClosed K :=
    ((Stacks.Chow.integralComponentAt y).subschemeι ≫ h).isClosedEmbedding.isClosed_range
  have hKirr : IsIrreducible K := by
    rw [hK, ← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ (Scheme.Hom.continuous _).continuousOn
  have hrj : Set.range j.base = E.idealSheaf.subschemeι.base '' (Gs.support : Set _) :=
    range_ι_comp_eq_image_support Gs _
  have hKj : K ⊆ Set.range j.base := hrj ▸ hsub
  set S := j.base ⁻¹' K with hS
  have hSirr : IsIrreducible S :=
    isIrreducible_preimage_of_isEmbedding' j.isClosedEmbedding.isEmbedding hKirr hKj
  have hScl : IsClosed S := hKcl.preimage j.continuous
  have hjS : j.base '' S = K := Set.image_preimage_eq_of_subset hKj
  set C₀ := MMP.Intersection.Scheme.Subvariety.ofIrreducibleCloseds (⟨S, hSirr, hScl⟩ : IrreducibleCloseds Gs.toScheme)
  have hC₀ : (C₀.support : Set Gs.toScheme) = S := by
    rw [MMP.Intersection.Scheme.Subvariety.support_ofIrreducibleCloseds]; rfl
  have hdimS : topologicalKrullDim S = ((1 : ℕ) : WithBot ℕ∞) := by
    have h1 : topologicalKrullDim S = topologicalKrullDim K := by
      rw [← hjS]
      exact (j.isClosedEmbedding.isEmbedding.homeomorphImage S).isHomeomorph.topologicalKrullDim_eq
    have h2 : topologicalKrullDim K =
        topologicalKrullDim (closure {y} : Set (ParameterPoint.fibre 𝔉.f u)) := by
      rw [hK']
      exact ((h.isClosedEmbedding.isEmbedding.homeomorphImage
        (closure {y} : Set (ParameterPoint.fibre 𝔉.f u))).isHomeomorph.topologicalKrullDim_eq).symm
    rw [h1, h2, Stacks.Chow.topologicalKrullDim_closure_singleton_eq ℂ
      (ParameterPoint.fibre 𝔉.f u ↘ Spec (.of ℂ)) y, hy1,
      Int.toNat_natCast]
  have hC₀dim : C₀.HasDim 1 := by
    change MMP.Intersection.HasDim C₀.toScheme ((1 : ℕ) : ℤ)
    rw [MMP.Intersection.hasDim_natCast_iff]
    exact (Subvariety.dim_eq_topologicalKrullDim_support C₀).trans (by rw [hC₀]; exact hdimS)
  have hKP : K ⊆ E.idealSheaf.subschemeι.base '' P.support := fun z hz ↦ by
    obtain ⟨x, rfl⟩ := hz
    exact (𝔉.range_fibre_subset u ⟨(Stacks.Chow.integralComponentAt y).subschemeι.base x, rfl⟩).1
  refine ⟨⟨C₀, hC₀dim⟩, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rw [hC₀]; exact hSirr
  · rw [hC₀]
    intro x hx
    obtain ⟨p, hp, hpx⟩ := hKP hx
    have := E.idealSheaf.subschemeι.isClosedEmbedding.injective hpx
    subst this; exact hp
  · rintro A ⟨hAirr, hAP⟩ hSA
    rw [hC₀] at hSA ⊢
    set A' := j.base '' A with hA'
    have hA'irr : IsIrreducible A' := hAirr.image _ j.continuous.continuousOn
    have hA'sub : A' ⊆ Set.range h.base := by
      rintro _ ⟨x, hx, rfl⟩
      refine 𝔉.subset_range_fibre u ⟨⟨Gs.ι.base x, hAP hx, rfl⟩, ?_⟩
      have hx' : Gs.ι.base x ∈ (Gs.support : Set _) := by
        rw [MMP.Intersection.Scheme.Subvariety.support_eq, ← Scheme.IdealSheafData.range_subschemeι]; exact ⟨x, rfl⟩
      exact hGs hx'
    set A'' := h.base ⁻¹' A' with hA''
    have hA''irr : IsIrreducible A'' :=
      isIrreducible_preimage_of_isEmbedding' h.isClosedEmbedding.isEmbedding hA'irr hA'sub
    have hCA'' : (closure {y} : Set _) ⊆ A'' := fun w hw ↦ by
      have : h.base w ∈ K := hK' ▸ ⟨w, hw, rfl⟩
      rw [← hjS] at this
      exact Set.image_mono hSA this
    have hC'' : closure {y} ∈ irreducibleComponents (ParameterPoint.fibre 𝔉.f u) := hC'
    have hA''C := hC''.2 hA''irr hCA''
    intro x hx
    obtain ⟨w, hw⟩ := hA'sub ⟨x, hx, rfl⟩
    change j.base x ∈ K
    rw [hK', ← hw]
    exact ⟨w, hA''C (show h.base w ∈ A' from hw ▸ ⟨x, hx, rfl⟩), rfl⟩
  · rw [range_ι_comp_eq_image_support C₀ j, hC₀, hjS]

/-- The image of a complex point under `c` is a complex point over the range of `c`. -/
theorem mapFun_mem_pointsOver_range {A A' : Scheme.{0}} [A.Over (Spec (.of ℂ))]
    [A'.Over (Spec (.of ℂ))] (c : A ⟶ A') [c.IsOver (Spec (.of ℂ))] (y : UnderlyingSpace ℂ A) :
    mapFun (K := ℂ) c y ∈ pointsOver (K := ℂ) (Set.range c.base) :=
  ⟨_, by rw [toHom_mapFun]; rfl⟩

/-- Precomposing with an isomorphism does not change the range of the underlying map. -/
theorem range_comp_of_isIso {A A' A'' : Scheme.{0}} (e : A ⟶ A') [IsIso e] (k : A' ⟶ A'') :
    Set.range (e ≫ k).base = Set.range k.base :=
  range_eq_range_of_surjective (e ≫ k) k e rfl

/-- Two points of a fibre of `f` whose integral components have the same image in `Z` are equal. -/
theorem PrimeDivisorFamily.eq_of_range_fibre_eq (𝔉 : PrimeDivisorFamily r T E P U)
    (u : ParameterPoint 𝔉.B) (y₁ y₂ : ParameterPoint.fibre 𝔉.f u)
    (h12 : Set.range ((Stacks.Chow.integralComponentAt y₁).subschemeι ≫
        ParameterPoint.fibreι 𝔉.f u ≫ 𝔉.ι ≫ 𝔉.jG).base =
      Set.range ((Stacks.Chow.integralComponentAt y₂).subschemeι ≫
        ParameterPoint.fibreι 𝔉.f u ≫ 𝔉.ι ≫ 𝔉.jG).base) : y₁ = y₂ := by
  haveI := 𝔉.isClosedImmersion_fibre u
  rw [range_integralComponentAt_subschemeι_comp, range_integralComponentAt_subschemeι_comp] at h12
  exact (inseparable_iff_closure_eq.mpr ((Set.image_injective.2
    (ParameterPoint.fibreι 𝔉.f u ≫ 𝔉.ι ≫ 𝔉.jG).isClosedEmbedding.injective) h12)).eq

/-- Two curves in a subvariety `G` of `E` with the same image in `Z` are equal. -/
theorem eq_of_range_subvariety_eq {G : Subvariety E.idealSheaf.subscheme}
    (C₁ C₂ : {V : Subvariety G.toScheme // V.HasDim 1})
    (h12 : Set.range (C₁.1.ι ≫ G.ι ≫ E.idealSheaf.subschemeι).base =
      Set.range (C₂.1.ι ≫ G.ι ≫ E.idealSheaf.subschemeι).base) : C₁ = C₂ := by
  rw [range_ι_comp_eq_image_support, range_ι_comp_eq_image_support] at h12
  exact Subtype.ext (Subvariety.support_injective
    ((Set.image_injective.2 (G.ι ≫ E.idealSheaf.subschemeι).isClosedEmbedding.injective) h12))

/-- The image in `Z` of a subvariety of `G` lies in the image of the support of `G`. -/
theorem range_subvariety_subset (G : Subvariety E.idealSheaf.subscheme)
    (C : Subvariety G.toScheme) :
    Set.range (C.ι ≫ G.ι ≫ E.idealSheaf.subschemeι).base ⊆
      E.idealSheaf.subschemeι.base '' (G.support : Set _) := by
  rw [range_ι_comp_eq_image_support, ← range_ι_comp_eq_image_support G]
  exact Set.image_subset_range _ _

/-- **A fibre component is open in the fibre** when the components of the fibre are pairwise
disjoint: its complement is the finite union of the other components. -/
theorem isOpen_setOf_mem_pointsOver_fibreComponent [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))]
    {E : Mori.PrimeDivisor Z} {b : UnderlyingSpace ℂ Y} (G : Subvariety E.idealSheaf.subscheme)
    (hdisj : ∀ (A B : Set E.idealSheaf.subscheme),
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.idealSheaf.subschemeι ≫ r).base ⁻¹'
        {b.toHom (IsLocalRing.closedPoint ℂ)}) A →
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.idealSheaf.subschemeι ≫ r).base ⁻¹'
        {b.toHom (IsLocalRing.closedPoint ℂ)}) B → A ≠ B → Disjoint A B)
    (hG : Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.idealSheaf.subschemeι ≫ r).base ⁻¹'
        {b.toHom (IsLocalRing.closedPoint ℂ)}) (G.support : Set _)) :
    IsOpen {x : fibrePointsIn F r (E.support : Set Z) b |
      (x : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ)
        (E.idealSheaf.subschemeι.base '' (G.support : Set _))} := by
  haveI : TopologicalSpace.NoetherianSpace E.idealSheaf.subscheme :=
    noetherianSpace_of_isComplexScheme
  set Sb := (E.idealSheaf.subschemeι ≫ r).base ⁻¹' {b.toHom (IsLocalRing.closedPoint ℂ)} with hSb
  have hSbcl : IsClosed Sb := (isClosed_singleton_toHom' b).preimage (Scheme.Hom.continuous _)
  set S := {M | Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ Sb) M ∧ M ≠ (G.support : Set _)} with hS
  have hSfin : S.Finite := (finite_setOf_maximal Sb).subset fun M hM ↦ hM.1
  have heq : {x : fibrePointsIn F r (E.support : Set Z) b |
      (x : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ)
        (E.idealSheaf.subschemeι.base '' (G.support : Set _))}ᶜ =
      Subtype.val ⁻¹' ⋃ M ∈ S, pointsOver (K := ℂ) (E.idealSheaf.subschemeι.base '' M) := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_iUnion,
      exists_prop]
    constructor
    · intro hx
      have h1 : (x : UnderlyingSpace ℂ Z).toHom (IsLocalRing.closedPoint ℂ) ∈
          (E.idealSheaf.support : Set Z) := x.2.1
      rw [← Scheme.IdealSheafData.range_subschemeι] at h1
      obtain ⟨e, he⟩ := h1
      have heS : e ∈ Sb := by
        change r.base (E.idealSheaf.subschemeι.base e) = _
        rw [he]
        have h2 : mapFun r (x : UnderlyingSpace ℂ Z) = b := x.2.2.2
        have h3 : (mapFun r (x : UnderlyingSpace ℂ Z)).toHom (IsLocalRing.closedPoint ℂ) =
            b.toHom (IsLocalRing.closedPoint ℂ) := by rw [h2]
        rw [← h3, toHom_mapFun]; rfl
      obtain ⟨M, heM, hM⟩ := exists_subset_maximal_of_isIrreducible isIrreducible_singleton
        (Set.singleton_subset_iff.2 heS)
      refine ⟨M, ⟨hM, fun hMG ↦ hx ?_⟩, ⟨e, heM rfl, he⟩⟩
      exact ⟨e, hMG ▸ heM rfl, he⟩
    · rintro ⟨M, ⟨hM, hMG⟩, hxM⟩ hxG
      obtain ⟨e₁, he₁, h₁⟩ := hxM
      obtain ⟨e₂, he₂, h₂⟩ := hxG
      have := E.idealSheaf.subschemeι.isClosedEmbedding.injective (h₁.trans h₂.symm)
      exact Set.disjoint_left.1 (hdisj M _ hM hG hMG) he₁ (this ▸ he₂)
  rw [← isClosed_compl_iff, heq]
  refine IsClosed.preimage continuous_subtype_val (hSfin.isClosed_biUnion fun M hM ↦ ?_)
  exact isClosed_pointsOver (E.idealSheaf.subschemeι.isClosedMap _ (isClosed_of_maximal hSbcl hM.1))

end familyLemmas

section primeDivisorTransport

variable {Z Y : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))] [IsComplexScheme Z]
  [CompactSpace Z] [IsLocallyNoetherian Z] [IsNormal Z] [IsIntegral Y] [IsLocallyNoetherian Y]
  [IsNormal Y] {r : Z ⟶ Y} [r.IsOver (Spec (.of ℂ))] {F D : Divisor Z}

/-- **The algebraic family of a prime divisor of a component of `F` dominating `T`.** -/
theorem exists_primeDivisorFamily [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))]
    (hM : IsCurvePointExceptionalModel (Y ↘ Spec (.of ℂ)) r F D)
    (T : IrreducibleCloseds Y) (hT1 : topologicalKrullDim (T : Set Y) = 1)
    (E : Mori.PrimeDivisor Z) (hE : E ∈ F.support) (P : Mori.PrimeDivisor E.idealSheaf.subscheme)
    (hTP : (T : Set Y) ⊆ r.base '' (E.idealSheaf.subschemeι.base '' P.support)) :
    ∃ U : Y.Opens, ((U : Set Y) ∩ T).Nonempty ∧ Nonempty (PrimeDivisorFamily r T E P U) := by
  classical
  have hres := hM.isResolution
  haveI : MMP.Mori.IsVariety ℂ (Y ↘ Spec (.of ℂ)) := hres.1
  haveI : IsProper r := (IsProjectiveMorphism.isProjective hres.2.2.2.1).isProper
  haveI : MMP.Mori.IsVariety ℂ (r ≫ Y ↘ Spec (.of ℂ)) := hres.2.1
  have hdimZ : topologicalKrullDim Z = 4 := by
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (Y ↘ Spec (.of ℂ))
      (r ≫ Y ↘ Spec (.of ℂ)) hres.2.2.2.2]
    exact hM.topologicalKrullDim_eq
  haveI : LocallyOfFiniteType (Z ↘ Spec (.of ℂ)) := by
    rw [← hM.comp_eq]; exact AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
  have := noetherianSpace_of_isComplexScheme (X := Z)
  haveI : IsProper (Y ↘ Spec (.of ℂ)) :=
    (IsProjectiveMorphism.isProjective hM.isProjectiveVariety.isProjective).isProper
  haveI : IsProper (Z ↘ Spec (.of ℂ)) := by rw [← hM.comp_eq]; infer_instance
  -- `r(E) = r(P) = T`
  set jE := E.idealSheaf.subschemeι with hjE
  set PZ := jE.base '' P.support with hPZ
  have hPZE : PZ ⊆ (E.support : Set Z) := by
    rintro _ ⟨x, -, rfl⟩
    change _ ∈ (E.idealSheaf.support : Set Z)
    rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨x, rfl⟩
  have hET : r.base '' (E.support : Set Z) = (T : Set Y) := by
    set K : Set Y := r.base '' (E.support : Set Z)
    have hKirr : IsIrreducible K := by
      have : IsIrreducible (E.support : Set Z) := by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact isIrreducible_singleton.closure
      exact this.image _ r.continuous.continuousOn
    have hTK : (T : Set Y) ⊆ K := hTP.trans (Set.image_mono hPZE)
    by_contra hne
    have hlt := MMP.topologicalKrullDim_lt_of_subset_of_ne hKirr T.isClosed
      hTK (Ne.symm hne) (ne_top_of_le_ne_top (by decide) (hM.topologicalKrullDim_image_le E hE))
    rw [hT1] at hlt
    exact absurd (hlt.trans_le (hM.topologicalKrullDim_image_le E hE)) (lt_irrefl _)
  have hPT : r.base '' PZ = (T : Set Y) := le_antisymm (hET ▸ Set.image_mono hPZE) hTP
  -- the map `E ⟶ T`
  haveI : IsIntegral E.idealSheaf.subscheme := E.integral
  set j := curveι T with hj
  have hrangej : Set.range j.base = (T : Set Y) := by
    rw [hj, Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hrangeE : Set.range (jE ≫ r).base = (T : Set Y) := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hjE,
      Scheme.IdealSheafData.range_subschemeι]
    exact hET
  have hker : j.ker ≤ (jE ≫ r).ker := by
    rw [hj, Scheme.IdealSheafData.ker_subschemeι, Scheme.Hom.ker_eq_vanishingIdeal_closure_range]
    refine le_of_eq (congrArg _ (TopologicalSpace.Closeds.ext ?_))
    rw [TopologicalSpace.Closeds.coe_closure, hrangeE, T.isClosed.closure_eq]
    rfl
  let pE := IsClosedImmersion.lift j (jE ≫ r) hker
  have hpE : pE ≫ j = jE ≫ r := IsClosedImmersion.lift_fac _ _ _
  haveI : IsIntegral (curveScheme T) :=
    MMP.Fourfold.isIntegral_subscheme_vanishingIdeal ⟨(T : Set Y), T.isClosed⟩ T.isIrreducible
  haveI : pE.IsOver (Spec (.of ℂ)) := ⟨by
    change pE ≫ j ≫ Y ↘ Spec (.of ℂ) = jE ≫ Z ↘ Spec (.of ℂ)
    rw [← Category.assoc, hpE, Category.assoc, hM.comp_eq]⟩
  haveI : LocallyOfFiniteType ((curveScheme T) ↘ Spec (.of ℂ)) := by
    change LocallyOfFiniteType (j ≫ Y ↘ Spec (.of ℂ)); infer_instance
  haveI : QuasiCompact ((curveScheme T) ↘ Spec (.of ℂ)) := by
    change QuasiCompact (j ≫ Y ↘ Spec (.of ℂ)); infer_instance
  haveI : IsSeparated ((curveScheme T) ↘ Spec (.of ℂ)) := by
    change IsSeparated (j ≫ Y ↘ Spec (.of ℂ)); infer_instance
  -- the prime divisor `P` and its smooth locus
  set jP := P.idealSheaf.subschemeι with hjP
  haveI : IsIntegral P.idealSheaf.subscheme := P.integral
  set pP := jP ≫ pE with hpP
  haveI : LocallyOfFiniteType (P.idealSheaf.subscheme ↘ Spec (.of ℂ)) := by
    change LocallyOfFiniteType (jP ≫ jE ≫ Z ↘ Spec (.of ℂ)); infer_instance
  haveI : QuasiCompact (P.idealSheaf.subscheme ↘ Spec (.of ℂ)) := by
    change QuasiCompact (jP ≫ jE ≫ Z ↘ Spec (.of ℂ)); infer_instance
  have hpPsurj : Function.Surjective pP.base := by
    intro t
    have htK : j.base t ∈ Set.range (jP ≫ jE ≫ r).base := by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hjP,
        Scheme.IdealSheafData.range_subschemeι]
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.image_comp]
      change j.base t ∈ r.base '' PZ
      rw [hPT, ← hrangej]; exact ⟨t, rfl⟩
    obtain ⟨x, hx⟩ := htK
    refine ⟨x, j.isClosedEmbedding.injective ?_⟩
    change (pP ≫ j).base x = j.base t
    rw [hpP, Category.assoc, hpE]
    exact hx
  set Po := (P.idealSheaf.subscheme ↘ Spec (.of ℂ)).smoothLocus with hPo
  have hPone : genericPoint P.idealSheaf.subscheme ∈ Po :=
    Scheme.Hom.genericPoint_mem_smoothLocus_of_perfectField _
  letI : Po.toScheme.Over (Spec (.of ℂ)) := ⟨Po.ι ≫ P.idealSheaf.subscheme ↘ Spec (.of ℂ)⟩
  haveI : Po.ι.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  haveI : Smooth (Po.toScheme ↘ Spec (.of ℂ)) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff]
    change (Po.ι ≫ P.idealSheaf.subscheme ↘ Spec (.of ℂ)).smoothLocus = ⊤
    rw [← Scheme.Hom.preimage_smoothLocus_eq]
    exact eq_top_iff.2 fun x _ ↦ x.2
  haveI : Nonempty Po.toScheme := ⟨⟨_, hPone⟩⟩
  haveI : IsIntegral Po.toScheme := isIntegral_of_isOpenImmersion Po.ι
  haveI : LocallyOfFiniteType (Po.toScheme ↘ Spec (.of ℂ)) := by
    change LocallyOfFiniteType (Po.ι ≫ _); infer_instance
  haveI : QuasiCompact (Po.toScheme ↘ Spec (.of ℂ)) := by
    change QuasiCompact (Po.ι ≫ _); infer_instance
  set po := Po.ι ≫ pP with hpo
  haveI : po.IsOver (Spec (.of ℂ)) := by rw [hpo]; infer_instance
  obtain ⟨U₁, hU₁d, hU₁s, hU₁sm, -⟩ := MMP.exists_dense_smooth_restrict_of_smooth (K := ℂ) po
  -- dimensions
  haveI : IsComplexScheme E.idealSheaf.subscheme := IsComplexScheme.of_isClosedImmersion jE
  haveI : IsComplexScheme P.idealSheaf.subscheme := IsComplexScheme.of_isClosedImmersion jP
  haveI : TopologicalSpace.NoetherianSpace P.idealSheaf.subscheme :=
    noetherianSpace_of_isComplexScheme
  have hdE : topologicalKrullDim E.idealSheaf.subscheme = ((2 + 1 : ℕ) : WithBot ℕ∞) := by
    rw [MMP.Mori.topologicalKrullDim_subscheme_eq]
    exact ConductorBlowup.topologicalKrullDim_support_eq_three hdimZ E
  have hdP : topologicalKrullDim P.idealSheaf.subscheme = ((2 : ℕ) : WithBot ℕ∞) := by
    rw [MMP.Mori.topologicalKrullDim_subscheme_eq]
    exact topologicalKrullDim_primeDivisor_support hdE P
  have hdT : topologicalKrullDim (curveScheme T) = 1 := by
    rw [MMP.Mori.topologicalKrullDim_subscheme_eq,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact hT1
  haveI : Nontrivial (curveScheme T) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    have h0 := topologicalKrullDim_zero_of_discreteTopology (curveScheme T)
    rw [hdT] at h0
    exact absurd h0 (by decide)
  -- the complement of the smooth locus: curves meeting the general fibres in points
  have hZ₀ : IsClosed (Po : Set P.idealSheaf.subscheme)ᶜ := Po.isOpen.isClosed_compl
  have hdimZ₀ : ∀ Zi, Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (Po : Set P.idealSheaf.subscheme)ᶜ)
      Zi → topologicalKrullDim Zi ≤ 1 := by
    intro Zi hZi
    have hne : Zi ≠ Set.univ := fun h ↦ (hZi.1.2 (h ▸ Set.mem_univ _ :
      genericPoint P.idealSheaf.subscheme ∈ Zi)) hPone
    have hlt := MMP.topologicalKrullDim_lt_of_subset_of_ne
      (IrreducibleSpace.isIrreducible_univ _) (isClosed_of_maximal hZ₀ hZi) (Set.subset_univ _)
      hne (by
        rw [(Homeomorph.Set.univ P.idealSheaf.subscheme).isHomeomorph.topologicalKrullDim_eq, hdP]
        decide)
    rw [(Homeomorph.Set.univ P.idealSheaf.subscheme).isHomeomorph.topologicalKrullDim_eq, hdP]
      at hlt
    exact withBot_le_one_of_lt_two hlt
  obtain ⟨W₀, hW₀, hW₀ne, hW₀bad⟩ := exists_isOpen_forall_topologicalKrullDim_lt_one pP.base
    pP.continuous hZ₀ hdimZ₀
  set U' : (curveScheme T).Opens := U₁ ⊓ ⟨W₀, hW₀⟩ with hU'
  have hU'ne : (U' : Set (curveScheme T)).Nonempty := by
    obtain ⟨x, hxW, hxU⟩ := hU₁d.inter_open_nonempty W₀ hW₀ hW₀ne
    exact ⟨x, hxU, hxW⟩
  haveI : JacobsonSpace (curveScheme T) :=
    LocallyOfFiniteType.jacobsonSpace ((curveScheme T) ↘ Spec (.of ℂ))
  obtain ⟨d, hdU', hdcl⟩ := nonempty_inter_closedPoints hU'ne U'.isOpen.isLocallyClosed
  have hdη : d ≠ genericPoint (curveScheme T) := by
    intro h
    have hcl : IsClosed ({d} : Set (curveScheme T)) := hdcl
    have huniv := (genericPoint_spec (curveScheme T)).def
    rw [← h, hcl.closure_eq] at huniv
    obtain ⟨a, b, hab⟩ := exists_pair_ne (curveScheme T)
    have ha : a ∈ ({d} : Set (curveScheme T)) := huniv ▸ trivial
    have hb : b ∈ ({d} : Set (curveScheme T)) := huniv ▸ trivial
    exact hab (ha.trans hb.symm)
  letI : U'.toScheme.Over (Spec (.of ℂ)) := ⟨U'.ι ≫ (curveScheme T) ↘ Spec (.of ℂ)⟩
  obtain ⟨hBns, hBdim⟩ := isSmoothVariety_opens_of_le_smoothLocus ℂ hdT U'
    (inf_le_left.trans hU₁s) hdU' hdη
  haveI := hBns
  haveI : U'.ι.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  obtain ⟨W, hW, hWU⟩ := j.isClosedEmbedding.isInducing.isOpen_iff.1 U'.2
  have hmemW : ∀ t, j.base t ∈ W ↔ t ∈ U' := fun t ↦ by
    rw [← Set.mem_preimage, hWU]; rfl
  -- the family of fibres of `E` and the family of curves cut by `P`
  set GU : E.idealSheaf.subscheme.Opens := pE ⁻¹ᵁ U' with hGU
  letI : GU.toScheme.Over (Spec (.of ℂ)) := ⟨GU.ι ≫ E.idealSheaf.subscheme ↘ Spec (.of ℂ)⟩
  haveI : GU.ι.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  haveI : IsComplexScheme GU.toScheme := isComplexScheme_opens GU
  set g : GU.toScheme ⟶ U'.toScheme := pE ∣_ U' with hg
  have hgU : g ≫ U'.ι = GU.ι ≫ pE := morphismRestrict_ι pE U'
  haveI : g.IsOver (Spec (.of ℂ)) := ⟨by
    change g ≫ U'.ι ≫ _ = GU.ι ≫ _
    rw [← Category.assoc, hgU, Category.assoc, comp_over pE (Spec (.of ℂ))]⟩
  set jG : GU.toScheme ⟶ Z := GU.ι ≫ jE with hjG
  set VU : P.idealSheaf.subscheme.Opens := jP ⁻¹ᵁ GU with hVU
  letI : VU.toScheme.Over (Spec (.of ℂ)) := ⟨VU.ι ≫ P.idealSheaf.subscheme ↘ Spec (.of ℂ)⟩
  haveI : VU.ι.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  have hmemVU : ∀ x, x ∈ VU ↔ pP.base x ∈ U' := fun x ↦ Iff.rfl
  have hVne : (VU : Set P.idealSheaf.subscheme).Nonempty := by
    obtain ⟨x, hx⟩ := hpPsurj d
    exact ⟨x, (hmemVU x).2 (hx ▸ hdU')⟩
  haveI : Nonempty VU.toScheme := hVne.to_subtype
  haveI : IsIntegral VU.toScheme := isIntegral_of_isOpenImmersion VU.ι
  haveI : IsComplexScheme VU.toScheme := isComplexScheme_opens VU
  set ι : VU.toScheme ⟶ GU.toScheme := jP ∣_ GU with hι
  have hιG : ι ≫ GU.ι = VU.ι ≫ jP := morphismRestrict_ι jP GU
  haveI : ι.IsOver (Spec (.of ℂ)) := ⟨by
    change ι ≫ GU.ι ≫ _ = VU.ι ≫ _
    rw [← Category.assoc, hιG, Category.assoc, comp_over jP (Spec (.of ℂ))]⟩
  haveI : IsClosedImmersion ι := inferInstance
  set f : VU.toScheme ⟶ U'.toScheme := ι ≫ g with hf
  have hfU : f ≫ U'.ι = VU.ι ≫ pP := by
    rw [hf, Category.assoc, hgU, ← Category.assoc, hιG, Category.assoc]
  have hfsurj : Function.Surjective f.base := by
    intro y
    obtain ⟨x, hx⟩ := hpPsurj y.1
    refine ⟨⟨x, (hmemVU x).2 (hx ▸ y.2)⟩, U'.ι.isOpenEmbedding.injective ?_⟩
    change (f ≫ U'.ι).base _ = _
    rw [hfU]
    exact hx
  haveI : IsDominant f := ⟨hfsurj.denseRange⟩
  set jB : U'.toScheme ⟶ Y := U'.ι ≫ j with hjB
  have hcomm : g ≫ jB = jG ≫ r := by
    rw [hjB, ← Category.assoc, hgU, Category.assoc, hpE, hjG, Category.assoc]
  have hjV : ι ≫ jG = VU.ι ≫ jP ≫ jE := by
    rw [hjG, ← Category.assoc, hιG, Category.assoc]
  have hcommV : f ≫ jB = (ι ≫ jG) ≫ r := by
    rw [hf, Category.assoc, hcomm, Category.assoc]; rfl
  have hjBinj : Function.Injective jB.base :=
    j.isClosedEmbedding.injective.comp U'.ι.isOpenEmbedding.injective
  have hrangejB : Set.range jB.base = W ∩ (T : Set Y) := by
    rw [hjB, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
    ext y
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨(hmemW t).2 ht, hrangej ▸ ⟨t, rfl⟩⟩
    · rintro ⟨hyW, hyT⟩
      obtain ⟨t, rfl⟩ : y ∈ Set.range j.base := hrangej ▸ hyT
      exact ⟨t, (hmemW t).1 hyW, rfl⟩
  have hrangejG : Set.range jG.base = (E.support : Set Z) ∩ r.base ⁻¹' W := by
    rw [hjG, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
    ext z
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨?_, ?_⟩
      · change _ ∈ (E.idealSheaf.support : Set Z)
        rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨u, rfl⟩
      · change r.base (jE.base u) ∈ W
        rw [show r.base (jE.base u) = j.base (pE.base u) from
          (congrArg (fun φ ↦ φ.base u) hpE).symm, hmemW]
        exact hu
    · rintro ⟨hzE, hzW⟩
      obtain ⟨u, rfl⟩ : z ∈ Set.range jE.base := by
        rw [hjE, Scheme.IdealSheafData.range_subschemeι]; exact hzE
      refine ⟨u, ?_, rfl⟩
      change r.base (jE.base u) ∈ W at hzW
      rw [show r.base (jE.base u) = j.base (pE.base u) from
        (congrArg (fun φ ↦ φ.base u) hpE).symm, hmemW] at hzW
      exact hzW
  have hjBpts := range_mapFun_comp_eq_pointsOver (K := ℂ) U'.ι j
  have hjGpts := range_mapFun_comp_eq_pointsOver (K := ℂ) GU.ι jE
  -- the smooth part of the family
  set O : VU.toScheme.Opens := VU.ι ⁻¹ᵁ Po with hO
  have hk₁ : Set.range (O.ι ≫ VU.ι).base ⊆ Set.range Po.ι.base := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact x.2
  set k₁ := IsOpenImmersion.lift Po.ι (O.ι ≫ VU.ι) hk₁ with hk₁def
  have hk₁f : k₁ ≫ Po.ι = O.ι ≫ VU.ι := IsOpenImmersion.lift_fac _ _ _
  have hk₂ : Set.range k₁.base ⊆ Set.range (po ⁻¹ᵁ U₁).ι.base := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    change po.base (k₁.base x) ∈ U₁
    have : po.base (k₁.base x) = pP.base (VU.ι.base (O.ι.base x)) := by
      change (k₁ ≫ Po.ι ≫ pP).base x = _
      rw [← Category.assoc, hk₁f]; rfl
    rw [this]
    exact ((hmemVU _).1 (O.ι.base x).2).1
  set k := IsOpenImmersion.lift (po ⁻¹ᵁ U₁).ι k₁ hk₂ with hkdef
  have hkf : k ≫ (po ⁻¹ᵁ U₁).ι = k₁ := IsOpenImmersion.lift_fac _ _ _
  haveI : Smooth (O.ι ≫ f) := by
    haveI := hU₁sm
    have h : (O.ι ≫ f) ≫ U'.ι = k ≫ (po ∣_ U₁) ≫ U₁.ι := by
      rw [morphismRestrict_ι, ← Category.assoc k (po ⁻¹ᵁ U₁).ι po, hkf, hpo,
        ← Category.assoc k₁ Po.ι pP, hk₁f, Category.assoc O.ι VU.ι pP, ← hfU, Category.assoc]
    haveI hpost : MorphismProperty.HasOfPostcompProperty (@Smooth : MorphismProperty Scheme.{0})
        (@IsOpenImmersion : MorphismProperty Scheme.{0}) :=
      AlgebraicGeometry.instHasOfPostcompPropertySchemeIsOpenImmersionOfIsStableUnderBaseChange
        (@Smooth : MorphismProperty Scheme.{0})
    exact hpost.of_postcomp (O.ι ≫ f) U'.ι inferInstance (by rw [h]; infer_instance)
  have hbad : ∀ (s : ParameterPoint U'.toScheme) (A : Set VU.toScheme), IsIrreducible A →
      A ⊆ (O : Set VU.toScheme)ᶜ → A ⊆ f.base ⁻¹' {s.point} → topologicalKrullDim A < 1 := by
    intro s A hAirr hAO hAf
    have hpt : IsClosed ({U'.ι.base s.point} : Set (curveScheme T)) := by
      have := isClosed_singleton_toHom' (mapFun (K := ℂ) U'.ι s.complexPoint)
      rwa [toHom_closedPoint_mapFun, ParameterPoint.complexPoint_toHom_closedPoint] at this
    have hW : U'.ι.base s.point ∈ W₀ := s.point.2.2
    have h := hW₀bad _ hW hpt (VU.ι.base '' A) (by
        rintro _ ⟨x, hx, rfl⟩
        exact hAO hx)
      (hAirr.image _ VU.ι.continuous.continuousOn) (by
        rintro _ ⟨x, hx, rfl⟩
        change pP.base (VU.ι.base x) = U'.ι.base s.point
        have e : U'.ι.base (f.base x) = pP.base (VU.ι.base x) :=
          congrArg (fun φ : VU.toScheme ⟶ curveScheme T ↦ φ.base x) hfU
        rw [← e, show f.base x = s.point from hAf hx])
    rwa [← (VU.ι.isOpenEmbedding.isEmbedding.homeomorphImage A).isHomeomorph.topologicalKrullDim_eq]
      at h
  -- the remaining data
  have hPZcl : IsClosed PZ := jE.isClosedMap _ P.idealSheaf.support.isClosed
  have hr1 : Set.range (ι ≫ jG).base ⊆ PZ := by
    rw [hjV]
    rintro _ ⟨x, rfl⟩
    refine ⟨jP.base (VU.ι.base x), ?_, rfl⟩
    change _ ∈ (P.idealSheaf.support : Set E.idealSheaf.subscheme)
    rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨_, rfl⟩
  have hr2 : PZ ∩ r.base ⁻¹' Set.range jB.base ⊆ Set.range (ι ≫ jG).base := by
    rintro z ⟨⟨x, hx, rfl⟩, hzr⟩
    obtain ⟨x, rfl⟩ : x ∈ Set.range jP.base := by
      rw [hjP, Scheme.IdealSheafData.range_subschemeι]; exact hx
    obtain ⟨u, hu⟩ := hzr
    have hxV : x ∈ VU := by
      rw [hmemVU]
      have e1 : jB.base u = j.base u.1 := rfl
      have e2 : r.base (jE.base (jP.base x)) = j.base (pE.base (jP.base x)) :=
        (congrArg (fun φ ↦ φ.base (jP.base x)) hpE).symm
      rw [hu, e2] at e1
      have := j.isClosedEmbedding.injective e1
      change pE.base (jP.base x) ∈ U'
      exact this ▸ u.2
    refine ⟨⟨x, hxV⟩, ?_⟩
    rw [hjV]; rfl
  haveI : IsPreimmersion (ι ≫ jG) := by rw [hjV]; infer_instance
  have hpt : ∀ s : ParameterPoint U'.toScheme, IsClosed {jB.base s.point} := fun s ↦ by
    have := isClosed_singleton_toHom' (mapFun (K := ℂ) jB s.complexPoint)
    rwa [toHom_closedPoint_mapFun, ParameterPoint.complexPoint_toHom_closedPoint] at this
  have hdVU : topologicalKrullDim VU.toScheme = ((2 : ℕ) : WithBot ℕ∞) :=
    ((AlgebraicGeometry.topologicalKrullDim_eq_of_isOpen ℂ _ (_ ↘ Spec (.of ℂ)) _
        (TopologicalSpace.Opens.isOpen VU) hVne).symm).trans hdP
  haveI : Nontrivial U'.toScheme := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    have h0 := topologicalKrullDim_zero_of_discreteTopology U'.toScheme
    haveI := hBdim
    rw [topologicalKrullDim_eq_of_smoothOfRelativeDimension (K := ℂ) 1] at h0
    exact absurd h0 (by decide)
  haveI : IrreducibleSpace VU.toScheme := inferInstance
  have hne : ∀ s : ParameterPoint U'.toScheme, ∃ v, f.base v ≠ s.point := fun s ↦ by
    obtain ⟨b', hb'⟩ := exists_ne s.point
    obtain ⟨v, hv⟩ := hfsurj b'
    exact ⟨v, hv ▸ hb'⟩
  refine ⟨⟨W, hW⟩, ⟨j.base d, (hmemW d).2 hdU', hrangej ▸ ⟨d, rfl⟩⟩, ⟨{
    B := U'.toScheme
    dim_B := hBdim
    jB := jB
    injective_jB := hjBinj
    isEmbedding_jB := hjBpts.2
    range_jB := by rw [hjBpts.1, hrangejB]; rfl
    G := GU.toScheme
    g := g
    jG := jG
    comm_G := hcomm
    isEmbedding_jG := hjGpts.2
    range_jG := by rw [hjGpts.1, hrangejG, pointsOver_inter]; congr 1
    V := VU.toScheme
    dimension_V := by show _ = topologicalKrullDim _; rw [hdVU]
    ι := ι
    f := f
    hf := rfl
    mult_fibre := fun s ξ h1 ↦ componentMultiplicity_eq_one_of_smooth_open f O hbad s ξ h1
    isClosedImmersion_fibre := fun s ↦ isClosedImmersion_fibreι_comp_of_range f ι jG jB r hjBinj
      hcommV hPZcl hr1 hr2 s (hpt s)
    range_subset := hr1
    subset_range := hr2
    exists_component := fun s C _ _ _ _ c _ _ hC1 hcS hcr ↦
      exists_component_of_immersion_of_le hPZcl f jB hjBinj (ι ≫ jG) VU.ι (jP ≫ jE) hjV hcommV
        hr2 s (fun A hA ↦ topologicalKrullDim_le_one_of_mem_irreducibleComponents_fibre f hdVU s
          (hne s) A hA) C c hC1 hcS hcr }⟩⟩

end primeDivisorTransport

end MMP.Fourfold
