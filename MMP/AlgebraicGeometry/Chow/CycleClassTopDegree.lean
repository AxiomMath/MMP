module

public import MMP.AlgebraicGeometry.Chow.CycleClassRestrict
public import MMP.AlgebraicGeometry.CycleMap.TopClassComponentBasis

/-!
# The top-degree cycle class on Stacks points (Fulton, Lemma 19.1.1)

Let `X` be a complex scheme of dimension `≤ n` and `C = Stacks.Chow.fieldChowSituation ℂ`. The
points of `X` of delta-dimension `n` are the generic points of the `n`-dimensional irreducible
components of `X`, and their cycle classes `cl_X(x) ∈ H_{2n}(X; R)` are linearly independent and
span `H_{2n}(X; R)` (Fulton, Lemma 19.1.1). Equivalently, `x ↦ cl_X(x)` extends to a bijection
from the finitely supported `R`-combinations of points of delta-dimension `n` onto `H_{2n}(X; R)`.

For a component `Xⱼ` with generic point `ξⱼ`, let `Uⱼ(ℂ)` be the `ℂ`-points of `X` off the
singular stratum and off the other components. Restriction to `Uⱼ(ℂ)` kills `cl_X(ξᵢ)` for
`i ≠ j`, and carries `cl_X(ξⱼ)` to a fundamental class of the connected manifold `Uⱼ(ℂ)`, which
freely generates `H_{2n}(Uⱼ(ℂ); R)`; a class vanishing on every `Uⱼ(ℂ)` vanishes, since the
complement of their union has dimension `< n`.

## Main results

* `MMP.Chow.exists_componentGenericPoint_eq`: a point of delta-dimension `n` is the generic point
  of an irreducible component.
* `MMP.Chow.eq_zero_of_forall_restrict_singularStratumComplementPointsOpens_eq_zero`: a class of
  `H_{2n}(X; R)` vanishing on `Uⱼ(ℂ)` for every component `Xⱼ` whose generic point has
  delta-dimension `n` vanishes.
* `MMP.Chow.linearIndependent_and_span_eq_top_pointCycleClass`: the classes of the generic
  points of the `n`-dimensional components form a basis of `H_{2n}(X; R)`.
* `MMP.Chow.exists_mem_supported_linearCombination_eq`,
  `MMP.Chow.eq_zero_of_linearCombination_pointCycleClassOrZero_eq_zero`: the cycle class map on
  combinations of points of delta-dimension `n` is surjective and injective.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1, Lemma 19.1.1.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MMP MMP.UnderlyingSpace Stacks.Chow Set
open scoped MMP.SubschemeOver

namespace MMP.Chow

variable (R : Type) [CommRing R] {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsComplexScheme X]

/-- On a complex scheme of dimension `≤ n` every point has delta-dimension `≤ n`. -/
theorem relativeDimension_le_of_dimension_le {n : ℕ} (hX : topologicalKrullDim X ≤ n) (x : X) :
    relativeDimension (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) x ≤ n := by
  have h2 : topologicalKrullDim (closure ({x} : Set X)) ≤ n :=
    (topologicalKrullDim_subspace_le X _).trans hX
  rw [topologicalKrullDim_closure_singleton_eq ℂ (X ↘ Spec (.of ℂ)) x] at h2
  have h3 : (relativeDimension (fieldChowSituation ℂ).dimensionFunction
      (X ↘ Spec (.of ℂ)) x).toNat ≤ n := by exact_mod_cast h2
  have h0 := relativeDimension_nonneg (fieldChowSituation ℂ) (fun _ _ ↦ rfl) (X ↘ Spec (.of ℂ)) x
  omega

/-- The generic point of an irreducible component determines the component. -/
theorem componentGenericPoint_injective :
    Function.Injective (componentGenericPoint (X := X)) := fun j j' h ↦ Subtype.ext <| by
  rw [← closure_componentGenericPoint j, ← closure_componentGenericPoint j', h]

/-- **A point of delta-dimension `n` on a scheme of dimension `≤ n` is the generic point of an
irreducible component.** -/
theorem exists_componentGenericPoint_eq {n : ℕ} (hX : topologicalKrullDim X ≤ n) {x : X}
    (hx : relativeDimension (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) x = n) :
    ∃ j : irreducibleComponents X, componentGenericPoint j = x := by
  obtain ⟨Z, hZ, hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (closure ({x} : Set X)) isIrreducible_singleton.closure
  refine ⟨⟨Z, hZ⟩, ?_⟩
  by_contra hne
  have hspec : componentGenericPoint ⟨Z, hZ⟩ ⤳ x := by
    rw [specializes_iff_mem_closure, closure_componentGenericPoint]
    exact hsub (subset_closure rfl)
  have hlt := relativeDimension_lt_of_specializes (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) hspec
    hne
  have hle := relativeDimension_le_of_dimension_le hX (componentGenericPoint ⟨Z, hZ⟩)
  omega

/-- The integral closed subscheme at the generic point of a component is the component with its
reduced structure. -/
theorem integralComponentAt_componentGenericPoint (j : irreducibleComponents X) :
    integralComponentAt (componentGenericPoint j) =
      Scheme.IdealSheafData.vanishingIdeal ⟨j.1, isClosed_of_mem_irreducibleComponents _ j.2⟩ := by
  unfold integralComponentAt
  congr 1
  ext1
  exact closure_componentGenericPoint j

/-- A component has dimension `n` iff its generic point has delta-dimension `n`. -/
theorem relativeDimension_componentGenericPoint_eq_iff {n : ℕ} (j : irreducibleComponents X) :
    relativeDimension (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ))
        (componentGenericPoint j) = n ↔
      (n : WithBot ℕ∞) = topologicalKrullDim (irreducibleComponentScheme X j) := by
  have h := dimension_integralComponentAt (componentGenericPoint j)
  rw [integralComponentAt_componentGenericPoint] at h
  change topologicalKrullDim (irreducibleComponentScheme X j) = _ at h
  rw [h]
  have h0 := relativeDimension_nonneg (fieldChowSituation ℂ) (fun _ _ ↦ rfl) (X ↘ Spec (.of ℂ))
    (componentGenericPoint j)
  constructor
  · intro e
    rw [e]
    rfl
  · intro e
    have e' : n = (relativeDimension (fieldChowSituation ℂ).dimensionFunction
        (X ↘ Spec (.of ℂ)) (componentGenericPoint j)).toNat := by exact_mod_cast e
    omega

/-- The `ℂ`-points of `closure {ξⱼ}`, `ξⱼ` the generic point of a component `Xⱼ`, are the
`ℂ`-points of `X` lying over `Xⱼ`. -/
theorem range_mapFun_integralComponentAt_componentGenericPoint (j : irreducibleComponents X) :
    range (mapFun (K := ℂ) (integralComponentAt (componentGenericPoint j)).subschemeι) =
      {p | p.toHom (IsLocalRing.closedPoint ℂ) ∈ j.1} := by
  rw [range_mapFun_of_isClosedImmersion, Scheme.IdealSheafData.range_subschemeι,
    coe_support_integralComponentAt, closure_componentGenericPoint]

/-- `Uⱼ(ℂ)` misses `closure {ξᵢ}(ℂ)` for every other component `Xᵢ`. -/
theorem disjoint_singularStratumComplementPointsOpens_range_integralComponentAt
    {j i : irreducibleComponents X} (h : i ≠ j) :
    Disjoint (singularStratumComplementPointsOpens X j : Set (UnderlyingSpace ℂ X))
      (range (mapFun (K := ℂ) (integralComponentAt (componentGenericPoint i)).subschemeι)) := by
  rw [range_mapFun_integralComponentAt_componentGenericPoint]
  exact Set.disjoint_left.mpr fun p hp hp' ↦ hp (Or.inr (Set.mem_iUnion₂.mpr ⟨i, h, hp'⟩))

/-- `Uⱼ(ℂ)` lies in the image of the regular part of `closure {ξⱼ}`, and its preimage in
`closure {ξⱼ}(ℂ)` is connected. -/
theorem subset_image_regularPart_and_isConnected_preimage_singularStratumComplementPointsOpens
    (j : irreducibleComponents X) :
    (singularStratumComplementPointsOpens X j : Set (UnderlyingSpace ℂ X)) ⊆
        mapFun (K := ℂ) (integralComponentAt (componentGenericPoint j)).subschemeι ''
          regularPart ℂ (integralComponentAt (componentGenericPoint j)).subscheme ∧
      IsConnected (mapFun (K := ℂ) (integralComponentAt (componentGenericPoint j)).subschemeι ⁻¹'
        (singularStratumComplementPointsOpens X j : Set (UnderlyingSpace ℂ X))) := by
  suffices h : ∀ I : X.IdealSheafData,
      I = Scheme.IdealSheafData.vanishingIdeal ⟨j.1, isClosed_of_mem_irreducibleComponents _ j.2⟩ →
      (singularStratumComplementPointsOpens X j : Set (UnderlyingSpace ℂ X)) ⊆
          mapFun (K := ℂ) I.subschemeι '' regularPart ℂ I.subscheme ∧
        IsConnected (mapFun (K := ℂ) I.subschemeι ⁻¹'
          (singularStratumComplementPointsOpens X j : Set (UnderlyingSpace ℂ X))) from
    h _ (integralComponentAt_componentGenericPoint j)
  rintro I rfl
  exact ⟨singularStratumComplementPointsOpens_subset j,
    isConnected_preimage_singularStratumComplementPointsOpens j⟩

/-- **Top-dimensional homology is detected on the sets `Uⱼ(ℂ)`** (Fulton, proof of
Lemma 19.1.1). Let `X` be a complex scheme of dimension `≤ n`. If `d ∈ H_{2n}(X; R)` restricts
to `0` on `Uⱼ(ℂ)` for every component `Xⱼ` whose generic point has delta-dimension `n`, then
`d = 0`. -/
theorem eq_zero_of_forall_restrict_singularStratumComplementPointsOpens_eq_zero {n : ℕ}
    (hX : topologicalKrullDim X ≤ n) (d : BMHomology R X (2 * n))
    (hd : ∀ j : irreducibleComponents X,
      relativeDimension (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ))
          (componentGenericPoint j) = n →
        borelMooreHomology.restrict R (ModuleCat.of R R) (Y := TopCat.of (UnderlyingSpace ℂ X))
          (singularStratumComplementPointsOpens X j) (2 * n : ℕ) d = 0) :
    d = 0 :=
  MMP.eq_zero_of_forall_restrict_singularStratumComplementPointsOpens R hX d fun j hj ↦
    hd j ((relativeDimension_componentGenericPoint_eq_iff j).2 hj)

/-- **The top homology is free on the classes of the top-dimensional components** (Fulton,
Lemma 19.1.1): on a complex scheme of dimension `≤ n`, the cycle classes of the generic points
of the irreducible components of delta-dimension `n` are linearly independent and span
`H_{2n}(X; R)`. -/
theorem linearIndependent_and_span_eq_top_pointCycleClass {n : ℕ}
    (hX : topologicalKrullDim X ≤ n) :
    LinearIndependent R (fun j : {j : irreducibleComponents X //
        relativeDimension (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ))
          (componentGenericPoint j) = n} ↦ pointCycleClass R (componentGenericPoint j.1) j.2) ∧
      Submodule.span R (range fun j : {j : irreducibleComponents X //
        relativeDimension (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ))
          (componentGenericPoint j) = n} ↦ pointCycleClass R (componentGenericPoint j.1) j.2) =
        ⊤ := by
  classical
  have := (finite_irreducibleComponents_of_isAlgebraicScheme ℂ X).to_subtype
  let : Fintype (irreducibleComponents X) := Fintype.ofFinite _
  let ι := {j : irreducibleComponents X //
    relativeDimension (fieldChowSituation ℂ).dimensionFunction
      (X ↘ Spec (.of ℂ)) (componentGenericPoint j) = n}
  let a : ι → BMHomology R X (2 * n) := fun j ↦ pointCycleClass R (componentGenericPoint j.1) j.2
  let ρ : (j : ι) → BMHomology R X (2 * n) →ₗ[R] borelMooreHomology R (ModuleCat.of R R)
      (TopCat.of (singularStratumComplementPointsOpens X j.1)) (2 * n : ℕ) :=
    fun j ↦ (borelMooreHomology.restrict R (ModuleCat.of R R)
      (Y := TopCat.of (UnderlyingSpace ℂ X)) (singularStratumComplementPointsOpens X j.1)
      (2 * n : ℕ)).hom
  have hzero : ∀ j j' : ι, j' ≠ j → ρ j (a j') = 0 := fun j j' h ↦
    restrict_pointCycleClass_eq_zero R _ j'.2 _
      (disjoint_singularStratumComplementPointsOpens_range_integralComponentAt
        fun e ↦ h (Subtype.ext e))
  have hbij : ∀ j : ι, Function.Bijective fun r : R ↦ r • ρ j (a j) := fun j ↦
    bijective_smul_restrict_pushforward R
      (integralComponentAt (componentGenericPoint j.1)).subschemeι
      (existsUnique_isVarietyFundamentalClass R
        (natCast_eq_dimension_integralComponentAt _ j.2)).choose_spec.1 _
      (subset_image_regularPart_and_isConnected_preimage_singularStratumComplementPointsOpens
        j.1).1
      (subset_image_regularPart_and_isConnected_preimage_singularStratumComplementPointsOpens
        j.1).2
  have hsum : ∀ (g : ι → R) (j : ι), ρ j (∑ j', g j' • a j') = g j • ρ j (a j) := by
    intro g j
    rw [map_sum, Finset.sum_eq_single j (fun j' _ h ↦ by rw [map_smul, hzero j j' h, smul_zero])
      (fun h ↦ absurd (Finset.mem_univ j) h), map_smul]
  refine ⟨Fintype.linearIndependent_iff.2 fun g hg j ↦ ?_, eq_top_iff.2 fun x _ ↦ ?_⟩
  · have h := congrArg (ρ j) hg
    rw [hsum, map_zero] at h
    exact (hbij j).1 (h.trans (zero_smul R _).symm)
  · choose r hr using fun j : ι ↦ (hbij j).2 (ρ j x)
    have hd : x - ∑ j, r j • a j = 0 := by
      refine eq_zero_of_forall_restrict_singularStratumComplementPointsOpens_eq_zero R hX _
        fun j hj ↦ ?_
      change ρ ⟨j, hj⟩ _ = 0
      have h := hr ⟨j, hj⟩
      simp only at h
      rw [map_sub, hsum, h, sub_self]
    rw [sub_eq_zero.mp hd]
    exact Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

/-- **Surjectivity of the top-degree cycle class** (Fulton, Lemma 19.1.1): on a complex scheme of
dimension `≤ n`, every class of `H_{2n}(X; R)` is `∑ₓ β(x) cl_X(x)` for a combination `β` of
points of delta-dimension `n`. -/
theorem exists_mem_supported_linearCombination_eq {n : ℕ} (hX : topologicalKrullDim X ≤ n)
    (v : BMHomology R X (2 * n)) :
    ∃ β ∈ Finsupp.supported R R {x : X | relativeDimension (fieldChowSituation ℂ).dimensionFunction
        (X ↘ Spec (.of ℂ)) x = n},
      Finsupp.linearCombination R (pointCycleClassOrZero R n) β = v := by
  classical
  have hv : v ∈ Submodule.span R _ :=
    (linearIndependent_and_span_eq_top_pointCycleClass R hX).2 ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hv
  refine ⟨c.mapDomain fun j ↦ componentGenericPoint j.1, ?_, ?_⟩
  · intro x hx
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hx)
    exact j.2
  · rw [Finsupp.linearCombination_mapDomain, ← hc, Finsupp.linearCombination_apply]
    refine Finsupp.sum_congr fun j _ ↦ ?_
    rw [Function.comp_apply, pointCycleClassOrZero, dif_pos j.2]

/-- **Injectivity of the top-degree cycle class** (Fulton, Lemma 19.1.1): on a complex scheme of
dimension `≤ n`, a combination `β` of points of delta-dimension `n` with `∑ₓ β(x) cl_X(x) = 0`
vanishes. -/
theorem eq_zero_of_linearCombination_pointCycleClassOrZero_eq_zero {n : ℕ}
    (hX : topologicalKrullDim X ≤ n) {β : X →₀ R}
    (hβ : β ∈ Finsupp.supported R R {x : X |
      relativeDimension (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) x = n})
    (h0 : Finsupp.linearCombination R (pointCycleClassOrZero R n) β = 0) : β = 0 := by
  classical
  let f := fun j : {j : irreducibleComponents X //
      relativeDimension (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ))
        (componentGenericPoint j) = n} ↦ componentGenericPoint j.1
  have hf : Function.Injective f := fun j j' h ↦
    Subtype.ext (componentGenericPoint_injective h)
  have hsupp : (β.support : Set X) ⊆ range f := by
    intro x hx
    obtain ⟨j, rfl⟩ := exists_componentGenericPoint_eq hX (hβ hx)
    exact ⟨⟨j, hβ hx⟩, rfl⟩
  set c := Finsupp.comapDomain f β hf.injOn
  have hβc : Finsupp.mapDomain f c = β := Finsupp.mapDomain_comapDomain f hf β hsupp
  have hc : c = 0 := by
    refine linearIndependent_iff.1 (linearIndependent_and_span_eq_top_pointCycleClass R hX).1 _ ?_
    rw [← h0]
    conv_rhs => rw [← hβc]
    rw [Finsupp.linearCombination_mapDomain, Finsupp.linearCombination_apply,
      Finsupp.linearCombination_apply]
    refine Finsupp.sum_congr fun j _ ↦ ?_
    rw [Function.comp_apply, pointCycleClassOrZero, dif_pos j.2]
  rw [← hβc, hc, Finsupp.mapDomain_zero]

end MMP.Chow
