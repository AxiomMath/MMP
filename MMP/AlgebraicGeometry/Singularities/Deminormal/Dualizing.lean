/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.AlgebraicGeometry.Singularities.Adjunction.DifferentDefs
public import MMP.AlgebraicGeometry.Singularities.Deminormal.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.GorensteinDualizingInvertible
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingComplexOverFieldClauses
public import StacksFrontier.AlgebraicGeometry.Curves.NodalGorensteinReduced
public import StacksFrontier.AlgebraicGeometry.Duality.DualizingModuleMaximalDimension
public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverField.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DerivedStalkModel
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.StalkFunctorComparison
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FreeNeighbourhoodRank
public import StacksFrontier.AlgebraicGeometry.Properties.DimensionFunctionClosure
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineLocalFree

/-!
# The dualizing sheaf at Gorenstein points and on open subschemes

Let `X` be a scheme over a field `k`, of pure dimension `d`, with dualizing sheaf `ω`
(`MMP.Flips.IsDualizingSheaf`: `ω ≅ j^* H^{-d}(π̄^× k)` for a compactification `j : X ⟶ X̄`,
`π̄ : X̄ ⟶ Spec k` proper). This file proves:

* `ω` is invertible (free of rank one on a neighbourhood) at every point whose local ring is
  Gorenstein, in particular at every regular point and at every double-crossing point;
* the restriction of `ω` along an open immersion `U ⟶ X` is a dualizing sheaf of `U`.

## Main results

* `MMP.Flips.IsDualizingSheaf.exists_restrict_iso_free_of_isGorensteinLocalRing`: at a point with
  Gorenstein local ring, `ω` is free of rank one on a neighbourhood.
* `MMP.Flips.IsDualizingSheaf.exists_restrict_iso_free_of_isRegularLocalRing`,
  `MMP.Flips.IsDualizingSheaf.exists_restrict_iso_free_of_isDoubleCrossingPoint`,
  `MMP.Flips.IsDualizingSheaf.exists_restrict_iso_free_of_mem_doubleCrossingLocus`: the same at
  regular and double-crossing points.
* `MMP.Flips.IsDualizingSheaf.restrict`: `ω|_U` is a dualizing sheaf of `U` for an open
  immersion `U ⟶ X`; `MMP.Flips.IsDualizingSheaf.of_iso`: invariance under isomorphism of `ω`.

## The argument

Let `K = π̄^× k` on `X̄`. It is a dualizing complex (Stacks 0FVV) whose dimension function `δ`
vanishes at the closed points of `X̄`. At a point `x̄ = j(x)` with Gorenstein local ring the stalk
of `K` is concentrated in a single degree `n`, where it is `𝒪_{X̄,x̄}` (Stacks 0BFQ), and the stalk
of `H^{-dim 𝒪_{X̄,x̄} - δ(x̄)}(K)` is nonzero; so `n = -(dim 𝒪_{X,x} + δ(x̄))`. The composite
`δ ∘ j` grades the specialization order of `X` (an open subset is closed under generization, and
closed points of `X` are closed in `X̄`, which is a Jacobson space), so `δ(j(x))` is the height of
`x` in `X` and `δ(j(η)) = d` at the generic point `η` of every irreducible component of `X`. Hence
`dim 𝒪_{X,x} + δ(x̄) = coheight x + height x = d`, the stalk of `H^{-d}(K)` at `x̄` is free of rank
one, and `H^{-d}(K)` being coherent it is free of rank one near `x̄` (Stacks 0B8J); restrict to
`X`.

The same grading shows that every irreducible component of an open subscheme `U` of `X` has
dimension `d`, which is what `IsDualizingSheaf` asks of `U` besides the compactification
`U ⟶ X ⟶ X̄`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 2.6, 16.3.3
* [Stacks Project, Tag 0BFQ](https://stacks.math.columbia.edu/tag/0BFQ)
* [Stacks Project, Tag 0AWN](https://stacks.math.columbia.edu/tag/0AWN)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace IsLocalRing

-- The Stacks results used here are stated at the locally small models of `D(R)`, `D(𝒪_X)`
-- and `D(SheafOfModules R)`, which Stacks scopes
-- (`StacksFrontier.Homology.DerivedCategory.LocallySmall`).
open scoped Stacks.SmallDerivedModel

namespace MMP.Flips

/-! ### Dimension functions along an open immersion -/

section Grading

variable {Y V : Scheme.{u}} (i : V ⟶ Y) [IsOpenImmersion i]

/-- An open immersion preserves and reflects the specialization order. -/
theorem le_iff_base_le_base {a b : V} : a ≤ b ↔ i.base a ≤ i.base b := by
  rw [Scheme.le_iff_specializes, Scheme.le_iff_specializes]
  exact i.isOpenEmbedding.isInducing.specializes_iff.symm

/-- A generization of a point in the image of an open immersion lies in the image. -/
theorem exists_base_eq_of_base_le {a : V} {c : Y} (h : i.base a ≤ c) : ∃ c', i.base c' = c :=
  (Scheme.le_iff_specializes.mp h).mem_open i.isOpenEmbedding.isOpen_range ⟨a, rfl⟩

/-- The image of a closed point under an open immersion into a Jacobson scheme is closed. -/
theorem isClosed_singleton_base [JacobsonSpace Y] {a : V} (ha : IsClosed ({a} : Set V)) :
    IsClosed ({i.base a} : Set Y) :=
  (i.isOpenEmbedding.preimage_closedPoints ▸ ha : a ∈ i.base ⁻¹' closedPoints Y)

/-- A maximal point (a generic point of an irreducible component) is sent by an open immersion to
a maximal point. -/
theorem isMax_base {η : V} (hη : IsMax η) : IsMax (i.base η) := by
  intro c hc
  obtain ⟨c', rfl⟩ := exists_base_eq_of_base_le i hc
  exact (le_iff_base_le_base i).mp (hη ((le_iff_base_le_base i).mpr hc))

variable (D : DimensionFunction Y)

/-- A dimension function composed with an open immersion is strictly monotone for the
specialization order. -/
theorem strictMono_dimensionFunction_base :
    letI := Scheme.specializationPartialOrder V
    StrictMono (fun v ↦ D (i.base v)) := by
  letI := Scheme.specializationPartialOrder V
  letI := Scheme.specializationPartialOrder Y
  intro a b hab
  exact DimensionFunctionGrade.strictMono D (lt_of_le_of_ne ((le_iff_base_le_base i).mp hab.le)
    fun h ↦ hab.ne (i.isOpenEmbedding.injective h))

/-- A dimension function composed with an open immersion increases by one along a covering
relation of the specialization order. -/
theorem dimensionFunction_base_eq_add_one_of_covBy {a b : V}
    (h : letI := Scheme.specializationPartialOrder V; a ⋖ b) :
    D (i.base b) = D (i.base a) + 1 := by
  letI := Scheme.specializationPartialOrder V
  letI := Scheme.specializationPartialOrder Y
  refine DimensionFunctionGrade.covBy D ⟨lt_of_le_of_ne ((le_iff_base_le_base i).mp h.1.le)
    fun e ↦ h.1.ne (i.isOpenEmbedding.injective e), fun c hac hcb ↦ ?_⟩
  obtain ⟨c', rfl⟩ := exists_base_eq_of_base_le i hac.le
  exact h.2 (lt_of_le_of_ne ((le_iff_base_le_base i).mpr hac.le) fun e ↦ hac.ne (congrArg _ e))
    (lt_of_le_of_ne ((le_iff_base_le_base i).mpr hcb.le) fun e ↦ hcb.ne (congrArg _ e))

variable [JacobsonSpace Y] {D}

/-- If `D` vanishes at the closed points of the Jacobson scheme `Y`, then `D ∘ i` vanishes at the
minimal points of `V`. -/
theorem dimensionFunction_base_eq_zero_of_isMin (hD : ∀ y : Y, IsClosed ({y} : Set Y) → D y = 0)
    (a : V) (ha : letI := Scheme.specializationPartialOrder V; IsMin a) : D (i.base a) = 0 :=
  hD _ (isClosed_singleton_base i ((isMin_iff_isClosed_singleton a).mp ha))

variable [CompactSpace V]

/-- **A dimension function vanishing at closed points measures heights along an open
immersion.** If `Y` is Jacobson, `D` vanishes at the closed points of `Y` and `V` is quasi-compact,
then `0 ≤ D(i(v))` and the height of `v` in the specialization order of `V` is `D(i(v))`. -/
theorem height_eq_dimensionFunction_base (hD : ∀ y : Y, IsClosed ({y} : Set Y) → D y = 0) (v : V) :
    letI := Scheme.specializationPartialOrder V
    0 ≤ D (i.base v) ∧ Order.height v = ((D (i.base v)).toNat : ℕ∞) := by
  letI := Scheme.specializationPartialOrder V
  exact Order.height_eq_of_grade (strictMono_dimensionFunction_base i D)
    (fun _ _ h ↦ dimensionFunction_base_eq_add_one_of_covBy i D h)
    (dimensionFunction_base_eq_zero_of_isMin i hD) exists_isMin_le v

/-- If every irreducible component of `V` has dimension `d`, then `D(i(η)) = d` at every maximal
point `η` of `V`. -/
theorem dimensionFunction_base_eq_of_isMax (hD : ∀ y : Y, IsClosed ({y} : Set Y) → D y = 0)
    {d : ℕ} (hpure : ∀ Z ∈ irreducibleComponents V, topologicalKrullDim Z = d) {η : V}
    (hη : IsMax η) : D (i.base η) = d := by
  letI := Scheme.specializationPartialOrder V
  obtain ⟨h0, hh⟩ := height_eq_dimensionFunction_base i hD η
  have h1 := hpure _ ((isMax_iff_closure_mem_irreducibleComponents η).mp hη)
  rw [topologicalKrullDim_closure_singleton_eq_height, hh] at h1
  have h2 : (D (i.base η)).toNat = d := by exact_mod_cast h1
  omega

include i in
/-- **`height + coheight = d` on a scheme of pure dimension `d`**, for the specialization order,
given a compactification-type open immersion into a Jacobson scheme with a dimension function
vanishing at the closed points. -/
theorem height_add_coheight_eq_of_isOpenImmersion
    (hD : ∀ y : Y, IsClosed ({y} : Set Y) → D y = 0) {d : ℕ}
    (hpure : ∀ Z ∈ irreducibleComponents V, topologicalKrullDim Z = d) (v : V) :
    letI := Scheme.specializationPartialOrder V
    Order.height v + Order.coheight v = (d : ℕ∞) := by
  letI := Scheme.specializationPartialOrder V
  refine (Order.height_add_coheight_eq_iff_of_grade (strictMono_dimensionFunction_base i D)
    (fun _ _ h ↦ dimensionFunction_base_eq_add_one_of_covBy i D h)
    (dimensionFunction_base_eq_zero_of_isMin i hD)
    exists_isMin_le exists_le_isMax v d fun η _ hη ↦
      (dimensionFunction_base_eq_of_isMax i hD hpure hη).le).mpr ?_
  obtain ⟨η, hvη, hη⟩ := exists_le_isMax v
  exact ⟨η, hvη, hη, dimensionFunction_base_eq_of_isMax i hD hpure hη⟩

end Grading

/-! ### The dimension function of `π̄^× k` -/

section ProperOverField

variable {k : Type u} [Field k] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of k)) [IsProper f]

/-- A proper scheme over a field has a dimension function that agrees with the associated shift
function of the dualizing complex `f^× k` and vanishes at the closed points. -/
theorem exists_dimensionFunction_dualizingComplexOverField :
    letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
    ∃ D : DimensionFunction Y, (∀ y : Y, IsClosed ({y} : Set Y) → D y = 0) ∧
      ∀ y : Y, D y = Stacks.Duality.associatedShiftFunction
        (Stacks.Duality.dualizingComplexOverField f).obj y := by
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨-, -, D, hD⟩ :=
    Stacks.Duality.isUniversallyCatenary_and_isDimensionFunction_associatedShiftFunction
      (Stacks.Duality.isDualizingComplex_dualizingComplexOverField f)
  exact ⟨D, fun y hy ↦ (hD y).trans
    (Stacks.Duality.ProperOverField.associatedShiftFunction_eq_zero_of_charts
      (Stacks.Duality.ProperOverField.hasCharts f) y hy), hD⟩

include f in
/-- A scheme with an open immersion into a proper scheme over a field is quasi-compact. -/
theorem compactSpace_of_isOpenImmersion {V : Scheme.{u}} (i : V ⟶ Y) [IsOpenImmersion i] :
    CompactSpace V := by
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace f
  haveI : IsNoetherian Y := ⟨⟩
  haveI : NoetherianSpace V := i.isOpenEmbedding.isInducing.noetherianSpace
  infer_instance

end ProperOverField

/-! ### The dualizing sheaf -/

namespace IsDualizingSheaf

variable {k : Type u} [Field k] {X : Scheme.{u}} {π : X ⟶ Spec (.of k)} {d : ℕ} {ω : X.Modules}

/-- A module isomorphic to a dualizing sheaf is a dualizing sheaf. -/
theorem of_iso (hω : IsDualizingSheaf π d ω) {ω' : X.Modules} (e : ω ≅ ω') :
    IsDualizingSheaf π d ω' := by
  obtain ⟨hpure, Xbar, j, hj, πbar, hπbar, hcomp, ⟨e'⟩⟩ := hω
  exact ⟨hpure, Xbar, j, hj, πbar, hπbar, hcomp, ⟨e.symm ≪≫ e'⟩⟩

/-- **The dualizing sheaf restricts along open immersions** (FA 16.3.3): if `ω` is a dualizing
sheaf of `X` and `i : U ⟶ X` is an open immersion, then `ω|_U` is a dualizing sheaf of `U`, with
structure map `i ≫ π`. The compactification of `U` is `U ⟶ X ⟶ X̄`; the content is that `U` is
again of pure dimension `d`. -/
theorem restrict (hω : IsDualizingSheaf π d ω) {U : Scheme.{u}} (i : U ⟶ X) [IsOpenImmersion i] :
    IsDualizingSheaf (i ≫ π) d ((Scheme.Modules.restrictFunctor i).obj ω) := by
  obtain ⟨hpure, Xbar, j, hj, πbar, hπbar, hcomp, ⟨e⟩⟩ := hω
  refine ⟨?_, Xbar, i ≫ j, inferInstance, πbar, hπbar, by rw [Category.assoc, hcomp],
    ⟨(Scheme.Modules.restrictFunctor i).mapIso e ≪≫
      ((Scheme.Modules.restrictFunctorComp i j).app _).symm⟩⟩
  have := LocallyOfFiniteType.jacobsonSpace πbar
  have := compactSpace_of_isOpenImmersion πbar j
  have := compactSpace_of_isOpenImmersion πbar (i ≫ j)
  obtain ⟨D, hD, -⟩ := exists_dimensionFunction_dualizingComplexOverField πbar
  intro Z hZ
  obtain ⟨η, hη⟩ := QuasiSober.sober hZ.1 (isClosed_of_mem_irreducibleComponents Z hZ)
  have hηmax : IsMax η := by
    rwa [isMax_iff_closure_mem_irreducibleComponents, hη.def]
  have hd := dimensionFunction_base_eq_of_isMax j hD hpure (isMax_base i hηmax)
  let := Scheme.specializationPartialOrder U
  obtain ⟨-, hh⟩ := height_eq_dimensionFunction_base (i ≫ j) hD η
  rw [← hη.def, topologicalKrullDim_closure_singleton_eq_height, hh, Scheme.Hom.comp_apply,
    hd]
  rfl

/-- **The dualizing sheaf is invertible at Gorenstein points.** If `ω` is a dualizing sheaf of
`X` (pure of dimension `d` over a field) and the local ring `𝒪_{X,x}` is Gorenstein, then `ω` is
free of rank one on an open neighbourhood of `x`. -/
theorem exists_restrict_iso_free_of_isGorensteinLocalRing [IsLocallyNoetherian X]
    (hω : IsDualizingSheaf π d ω) (x : X)
    (hx : Dualizing.IsGorensteinLocalRing (X.presheaf.stalk x)) :
    ∃ (W : X.Opens) (_ : x ∈ W),
      Nonempty (ω.restrict W.ι ≅ SheafOfModules.free.{u} (ULift.{u} (Fin 1))) := by
  obtain ⟨hpure, Xbar, j, hj, πbar, hπbar, hcomp, ⟨e⟩⟩ := hω
  let : IsLocallyNoetherian Xbar := LocallyOfFiniteType.isLocallyNoetherian πbar
  have := LocallyOfFiniteType.jacobsonSpace πbar
  have := compactSpace_of_isOpenImmersion πbar j
  obtain ⟨D, hD, hDδ⟩ := exists_dimensionFunction_dualizingComplexOverField πbar
  set K := (Stacks.Duality.dualizingComplexOverField πbar).obj
  have hK : Stacks.Duality.IsDualizingComplex K :=
    Stacks.Duality.isDualizingComplex_dualizingComplexOverField πbar
  set x' := j.base x
  have : IsIso (j.stalkMap x) := (IsOpenImmersion.iff_isIso_stalkMap.mp hj).2 x
  let hstalk : Xbar.presheaf.stalk x' ≅ X.presheaf.stalk x := asIso (j.stalkMap x)
  have hG : Dualizing.IsGorensteinLocalRing (Xbar.presheaf.stalk x') :=
    Dualizing.isGorensteinLocalRing_of_ringEquiv hstalk.commRingCatIsoToRingEquiv hx
  obtain ⟨n, hz, ⟨e'⟩⟩ :=
    Stacks.Duality.exists_stalk_homology_concentrated_free_of_isGorensteinLocalRing hK x' hG
  obtain ⟨h, hh⟩ := Stacks.Duality.exists_natCast_ringKrullDim_stalk x'
  have hnz := Stacks.Duality.not_isZero_stalk_homology_of_isDualizingComplex hK x' h hh
  -- `dim 𝒪_{X̄,x̄} + δ(x̄) = d`
  have hdim : (h : ℤ) + D x' = d := by
    let := Scheme.specializationPartialOrder X
    have hsum := height_add_coheight_eq_of_isOpenImmersion j hD hpure x
    obtain ⟨h0, hht⟩ := height_eq_dimensionFunction_base j hD x
    have hc : (Order.coheight x : WithBot ℕ∞) = (h : WithBot ℕ∞) := by
      refine (ringKrullDim_stalk_eq_coheight x).symm.trans ?_
      rw [← hh]
      exact (ringKrullDim_eq_of_ringEquiv hstalk.commRingCatIsoToRingEquiv).symm
    have hc' : Order.coheight x = h := by exact_mod_cast hc
    rw [hht, hc'] at hsum
    have : (D x').toNat + h = d := by exact_mod_cast hsum
    have hx' : j x = x' := rfl
    rw [hx'] at h0
    omega
  have hn : n = -(d : ℤ) := by
    by_contra hne
    apply hnz
    have hdeg : -(h : ℤ) - Stacks.Duality.associatedShiftFunction K x' ≠ n := by
      rw [← hDδ]
      omega
    exact (hz _ hdeg).of_iso (Stacks.Duality.schemeStalkModuleIso x' _)
  subst hn
  -- `H^{-d}(K)` is free of rank one near `x̄`
  set M := Stacks.Duality.dualizingModuleOverField πbar d
  have hcoh : SheafOfModules.IsCoherent M :=
    Stacks.Duality.isCoherent_homology_of_isDualizingComplex hK _
  obtain ⟨W, hxW, ⟨eW⟩⟩ := Scheme.Modules.exists_free_restrict_of_stalk_basis M hcoh x'
    ((Module.Basis.singleton (Fin 1) (Xbar.presheaf.stalk x')).map e'.toLinearEquiv.symm)
  exact ⟨j ⁻¹ᵁ W, hxW, ⟨(Scheme.Modules.restrictFunctor (j ⁻¹ᵁ W).ι).mapIso e ≪≫
    ((Scheme.Modules.restrictFunctorComp (j ⁻¹ᵁ W).ι j).app M).symm ≪≫
    (Scheme.Modules.restrictFunctorCongr (morphismRestrict_ι j W).symm).app M ≪≫
    (Scheme.Modules.restrictFunctorComp (j ∣_ W) W.ι).app M ≪≫
    (Scheme.Modules.restrictFunctor (j ∣_ W)).mapIso eW ≪≫
    (Stacks.Modules.freeRestrictIso (j ∣_ W) _).symm⟩⟩

/-- **The dualizing sheaf is invertible at regular points.** If `ω` is a dualizing sheaf of `X`
and `𝒪_{X,x}` is regular, then `ω` is free of rank one on an open neighbourhood of `x`. -/
theorem exists_restrict_iso_free_of_isRegularLocalRing [IsLocallyNoetherian X]
    (hω : IsDualizingSheaf π d ω) (x : X) (hx : IsRegularLocalRing (X.presheaf.stalk x)) :
    ∃ (W : X.Opens) (_ : x ∈ W),
      Nonempty (ω.restrict W.ι ≅ SheafOfModules.free.{u} (ULift.{u} (Fin 1))) :=
  hω.exists_restrict_iso_free_of_isGorensteinLocalRing x
    (Dualizing.IsRegularLocalRing.isGorensteinLocalRing _)

end IsDualizingSheaf

/-! ### Double-crossing points are Gorenstein -/

/-- The power-series hypersurface `K[[x₀, …, x_{m+1}]]/(x₀x₁)` is a Gorenstein local ring. -/
theorem isGorensteinLocalRing_quotient_X_mul_X (K : Type u) [Field K] (m : ℕ) :
    letI R := MvPowerSeries (Fin (m + 2)) K
    letI f : R := MvPowerSeries.X 0 * MvPowerSeries.X 1
    ∃ (_ : IsLocalRing (R ⧸ Ideal.span {f})),
      Dualizing.IsGorensteinLocalRing (R ⧸ Ideal.span {f}) := by
  let R := MvPowerSeries (Fin (m + 2)) K
  let f : R := MvPowerSeries.X 0 * MvPowerSeries.X 1
  let _ : IsRegularLocalRing R := MvPowerSeries.isRegularLocalRing K (m + 2)
  let _ : IsDomain R := IsRegularLocalRing.isDomain _
  have hX : ∀ i : Fin (m + 2), (MvPowerSeries.X i : R) ≠ 0 := by
    intro i h
    have h' := congrArg (MvPowerSeries.coeff (R := K) (Finsupp.single i 1)) h
    simp [MvPowerSeries.coeff_X] at h'
  have hmem : f ∈ maximalIdeal R := by
    rw [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]
    simp [f]
  have hnzd : f ∈ nonZeroDivisors R :=
    mem_nonZeroDivisors_of_ne_zero (mul_ne_zero (hX 0) (hX 1))
  let _ : Nontrivial (R ⧸ Ideal.span {f}) :=
    Ideal.Quotient.nontrivial_iff.mpr
      (lt_of_le_of_lt (Ideal.span_le.2 (Set.singleton_subset_iff.mpr hmem))
        (inferInstance : (maximalIdeal R).IsMaximal).lt_top).ne
  let _ : IsLocalRing (R ⧸ Ideal.span {f}) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {f})) Ideal.Quotient.mk_surjective
  exact ⟨inferInstance, (Dualizing.isGorensteinLocalRing_quotient_span_singleton_iff R f hmem
    hnzd).mp (Dualizing.IsRegularLocalRing.isGorensteinLocalRing R)⟩

/-- **The local ring at a double-crossing point is Gorenstein.** If `x` is a double-crossing
point of a locally Noetherian scheme `X`, then `𝒪_{X,x}` is Gorenstein. -/
theorem isGorensteinLocalRing_stalk_of_isDoubleCrossingPoint {X : Scheme.{u}}
    [IsLocallyNoetherian X] {x : X} (hx : IsDoubleCrossingPoint x) :
    Dualizing.IsGorensteinLocalRing (X.presheaf.stalk x) := by
  obtain ⟨m, ⟨e⟩⟩ := hx
  obtain ⟨_, hQ⟩ := isGorensteinLocalRing_quotient_X_mul_X (X.residueField x) m
  have := AdicCompletion.isNoetherianRing (maximalIdeal (X.presheaf.stalk x))
  exact ((Dualizing.isGorensteinLocalRing_iff_of_flat _ _).mp
    (Dualizing.isGorensteinLocalRing_of_ringEquiv e hQ)).1

namespace IsDualizingSheaf

variable {k : Type u} [Field k] {X : Scheme.{u}} {π : X ⟶ Spec (.of k)} {d : ℕ} {ω : X.Modules}

/-- **The dualizing sheaf is invertible at double-crossing points.** If `x` is a double-crossing
point of `X`, then `ω` is free of rank one on an open neighbourhood of `x`. -/
theorem exists_restrict_iso_free_of_isDoubleCrossingPoint [IsLocallyNoetherian X]
    (hω : IsDualizingSheaf π d ω) {x : X} (hx : IsDoubleCrossingPoint x) :
    ∃ (W : X.Opens) (_ : x ∈ W),
      Nonempty (ω.restrict W.ι ≅ SheafOfModules.free.{u} (ULift.{u} (Fin 1))) :=
  hω.exists_restrict_iso_free_of_isGorensteinLocalRing x
    (isGorensteinLocalRing_stalk_of_isDoubleCrossingPoint hx)

/-- **The dualizing sheaf is invertible on `X°`** (FA Remark 2.6): at every point that is regular
or a double-crossing point, `ω` is free of rank one on a neighbourhood. -/
theorem exists_restrict_iso_free_of_mem_doubleCrossingLocus [IsLocallyNoetherian X]
    (hω : IsDualizingSheaf π d ω) {x : X} (hx : x ∈ doubleCrossingLocus X) :
    ∃ (W : X.Opens) (_ : x ∈ W),
      Nonempty (ω.restrict W.ι ≅ SheafOfModules.free.{u} (ULift.{u} (Fin 1))) :=
  hx.elim (hω.exists_restrict_iso_free_of_isRegularLocalRing x)
    hω.exists_restrict_iso_free_of_isDoubleCrossingPoint

end IsDualizingSheaf

end MMP.Flips
