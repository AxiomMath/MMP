module

public import MMP.AlgebraicGeometry.Chow.FirstChernClassTopAdditive
public import MMP.AlgebraicGeometry.Chow.CycleClassFundamental
public import MMP.AlgebraicGeometry.Intersection.InvertibleSheafCurveDegree
public import MMP.AlgebraicGeometry.SpecOverSpecSelf
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DegreeHomomorphism
public import StacksFrontier.AlgebraicGeometry.Intersection.ExteriorProductIntersection
public import StacksFrontier.AlgebraicGeometry.InvertibleClasses.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.RiemannRoch
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.RiemannRochInvertibleDegree
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.ChowDegree
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.Positivity
public import MMP.AlgebraicGeometry.Chow.CycleClassGenericPoint

/-!
# Degrees of zero-cycles and the cycle class map

Let `X` be a complex scheme, proper over `ℂ`. The cycle class `cl : A_0(X) → H_0(X(ℂ); ℚ)`
determines the degree of a zero-cycle class (Fulton, §19.1): pushing forward to `Spec ℂ`, where
the cycle class of the point is the fundamental class, `cl(a) = 0` forces `deg a = 0`. With
Fulton's Proposition 19.2 on Stacks cycles (`MMP.Chow.chowCycleClass_firstChernClassCap`) this
gives:

* the degree of an invertible module `M` on a proper curve carrying an ample invertible module
  vanishes when `c₁ᵗᵒᵖ(M) = 0`;
* on a complex scheme proper over `ℂ` with an ample invertible module `A`, the class of a
  closed subscheme of dimension `d` is non-zero in `H_{2d}`: otherwise the degree of
  `c₁(A)^d ∩ [Z]_d`, which is positive (Stacks 0BEV), would vanish.

## Main results

* `MMP.Chow.chowDegree_eq_zero_of_chowCycleClass_eq_zero`: `cl(a) = 0 → deg a = 0`.
* `MMP.Chow.invertibleCurveDegree_eq_zero_of_firstChernClassTop_eq_zero`: `c₁ᵗᵒᵖ(M) = 0` gives
  `deg M = 0` on a proper complex curve with an ample invertible module.
* `MMP.Chow.degreeOn_eq_zero_of_firstChernClassTop_eq_zero`: the same along a closed curve of
  a complex scheme with an ample invertible module.
* `MMP.Chow.cycleClass_cycleAssociatedToClosedSubscheme_ne_zero`,
  `MMP.Chow.pointCycleClass_ne_zero`: classes of closed subschemes and of points are non-zero.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1, Proposition 19.2.
* [Stacks Project, Tag 0AZ1](https://stacks.math.columbia.edu/tag/0AZ1)
* [Stacks Project, Tag 0BEV](https://stacks.math.columbia.edu/tag/0BEV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Set
open MMP.UnderlyingSpace

namespace MMP.Chow

open MMP MMP.Modules MMP.Analytic Stacks.Chow Stacks.Ample

/-! ### The degree of a zero-cycle class -/

section Degree

/-- `Spec ℂ` is a complex scheme. -/
private theorem isComplexScheme_spec : IsComplexScheme (Spec (.of ℂ)) :=
  haveI : IsSmoothVariety ℂ (Spec (.of ℂ) ↘ Spec (.of ℂ)) :=
    MMP.isSmoothVariety_of_eq_id (MMP.specOverSpec_over_self ℂ)
  IsComplexScheme.of_isSmoothVariety _

/-- The point of `Spec ℂ` has delta-dimension zero. -/
private theorem relativeDimension_spec (x : Spec (.of ℂ)) :
    relativeDimension (fieldChowSituation ℂ).dimensionFunction (Spec (.of ℂ) ↘ Spec (.of ℂ)) x =
      ((0 : ℕ) : ℤ) := by
  refine relativeDimension_eq_of_closure_eq_univ ℂ _
    (Set.eq_univ_of_forall fun y ↦ subset_closure (Subsingleton.elim y x ▸ rfl)) ?_
  change topologicalKrullDim (PrimeSpectrum ℂ) = _
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ringKrullDim_eq_zero_of_field]
  rfl

/-- The cycle class of the point of `Spec ℂ` is non-zero: it is the fundamental class of the
variety `Spec ℂ`, which spans `H_0(pt; ℚ)` freely. -/
private theorem pointCycleClass_spec_ne_zero (x : Spec (.of ℂ)) :
    haveI := isComplexScheme_spec
    pointCycleClass ℚ x (relativeDimension_spec x) ≠ 0 := by
  intro h0
  have := isComplexScheme_spec
  have hS : ((0 : ℕ) : WithBot ℕ∞) = topologicalKrullDim (Spec (.of ℂ)) := by
    change _ = topologicalKrullDim (PrimeSpectrum ℂ)
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ringKrullDim_eq_zero_of_field]
    rfl
  obtain ⟨cW, hcW, -, hbij⟩ := existsUnique_isVarietyFundamentalClass ℚ hS
  have h3 : pointCycleClass ℚ x (relativeDimension_spec x) = cW :=
    pointCycleClass_eq_of_closure_eq_univ x (relativeDimension_spec x)
      (Set.eq_univ_of_forall fun y ↦ subset_closure (Subsingleton.elim y x ▸ rfl)) hS hcW
  have h4 : cW = 0 := h3.symm.trans h0
  have := hbij.1 (show (1 : ℚ) • cW = (0 : ℚ) • cW by rw [h4, smul_zero, smul_zero])
  exact one_ne_zero this

/-- **The cycle class determines the degree of a zero-cycle class** (Fulton, §19.1). On a
complex scheme proper over `ℂ`, a zero-cycle class `a` with `cl(a) = 0` in `H_0(X(ℂ); ℚ)` has
degree `0` (Stacks 0AZ1). -/
theorem chowDegree_eq_zero_of_chowCycleClass_eq_zero {Y : Scheme.{0}} [Y.Over (Spec (.of ℂ))]
    [IsComplexScheme Y] [IsProper (Y ↘ Spec (.of ℂ))]
    (a : chowGroup (fieldChowSituation ℂ) (Y ↘ Spec (.of ℂ)) ((0 : ℕ) : ℤ))
    (h : chowCycleClass ℚ 0 a = 0) :
    chowDegree (fieldChowSituation ℂ) (fieldChowSituation_dimensionFunction_eq_zero ℂ)
      (Y ↘ Spec (.of ℂ)) (IsLocalRing.closedPoint ℂ) a = 0 := by
  classical
  have := isComplexScheme_spec
  induction a using QuotientAddGroup.induction_on with
  | H α =>
  rw [chowCycleClass_mk] at h
  haveI : (Y ↘ Spec (.of ℂ)).IsOver (Spec (.of ℂ)) :=
    ⟨by rw [MMP.specOverSpec_over_self, Category.comp_id]⟩
  have hp := cycleClass_properPushforward ℚ (Y ↘ Spec (.of ℂ)) α
  rw [h, map_zero] at hp
  set β := properPushforward (fieldChowSituation ℂ) (Y ↘ Spec (.of ℂ))
    (Spec (.of ℂ) ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)) (comp_over _ _) ((0 : ℕ) : ℤ) α
  have hcongr : ∀ (s s' : Spec (.of ℂ) ⟶ Spec (.of ℂ)) [LocallyOfFiniteType s]
      [LocallyOfFiniteType s'] (_ : s = s') (hf : (Y ↘ Spec (.of ℂ)) ≫ s = Y ↘ Spec (.of ℂ))
      (hf' : (Y ↘ Spec (.of ℂ)) ≫ s' = Y ↘ Spec (.of ℂ)),
      (properPushforward (fieldChowSituation ℂ) (Y ↘ Spec (.of ℂ)) s (Y ↘ Spec (.of ℂ)) hf 0
        α).1 =
      (properPushforward (fieldChowSituation ℂ) (Y ↘ Spec (.of ℂ)) s' (Y ↘ Spec (.of ℂ)) hf' 0
        α).1 := by
    intro s s' _ _ e _ _
    subst e
    rfl
  have hdeg : chowDegree (fieldChowSituation ℂ) (fieldChowSituation_dimensionFunction_eq_zero ℂ)
      (Y ↘ Spec (.of ℂ)) (IsLocalRing.closedPoint ℂ) (QuotientAddGroup.mk α) =
      β.1 (IsLocalRing.closedPoint ℂ) := by
    have e1 := Stacks.Chow.chowDegree_mk (fieldChowSituation ℂ)
      (fieldChowSituation_dimensionFunction_eq_zero ℂ) (Y ↘ Spec (.of ℂ))
      (IsLocalRing.closedPoint ℂ) α
    refine e1.trans ?_
    exact congrFun (congrArg DFunLike.coe
      (hcongr _ _ (MMP.specOverSpec_over_self ℂ).symm (Category.comp_id _) (comp_over _ _))) _
  refine hdeg.trans ?_
  suffices hq : ∀ q : Spec (.of ℂ), β.1 q = 0 from hq _
  intro q
  have hβ : cycleToFinsupp β = Finsupp.single q (β.1 q) := by
    refine Finsupp.ext fun y ↦ ?_
    obtain rfl : y = q := Subsingleton.elim _ _
    rw [cycleToFinsupp_apply, Finsupp.single_eq_same]
  have hcl : cycleClass ℚ 0 β = β.1 q • pointCycleClassOrZero ℚ 0 q := by
    change Finsupp.linearCombination ℤ (pointCycleClassOrZero ℚ 0) (cycleToFinsupp β) = _
    rw [hβ, Finsupp.linearCombination_single]
  rw [hp, pointCycleClassOrZero, dif_pos (relativeDimension_spec q)] at hcl
  by_contra hne
  rw [← Int.cast_smul_eq_zsmul ℚ] at hcl
  exact pointCycleClass_spec_ne_zero q
    ((smul_eq_zero.1 hcl.symm).resolve_left (by exact_mod_cast hne))

end Degree

/-! ### Degrees of invertible modules on curves -/

section Curve

/-- **Degrees of invertible modules with vanishing topological Chern class.** Let `C` be a
complex scheme of dimension at most one, proper over `ℂ`, carrying an ample invertible module.
An invertible module `M` on `C` with `c₁ᵗᵒᵖ(M) = 0` in `H²(C(ℂ); ℚ)` has degree `0`: its degree is
that of `c₁(M) ∩ [C]_1` (Riemann–Roch, Stacks 0AYQ), whose cycle class is `c₁ᵗᵒᵖ(M) ∩ cl(C) = 0`
(Fulton 19.2). -/
theorem invertibleCurveDegree_eq_zero_of_firstChernClassTop_eq_zero {C : Scheme.{0}}
    [C.Over (Spec (.of ℂ))] [IsComplexScheme C] [IsProper (C ↘ Spec (.of ℂ))]
    (hdim : topologicalKrullDim C ≤ 1) (A : C.Modules) [IsInvertibleModule C A]
    (hA : IsAmple C A) (M : C.Modules) [IsInvertibleModule C M]
    (hM : firstChernClassTop ℚ M = 0) :
    haveI : SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 M := ‹IsInvertibleModule C M›
    invertibleCurveDegree ℂ (C ↘ Spec (.of ℂ)) hdim M = 0 := by
  have : SheafOfModules.IsInvertible C.sheaf.obj C.ringCatSheaf.property M :=
    ‹IsInvertibleModule C M›
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} M 1 :=
    Stacks.InvertibleRankOneScheme.isFiniteLocallyFreeOfRank_one_of_isInvertibleModule
      (X := C) (L := M)
  rw [invertibleCurveDegree_eq_curveDegree_one, curveDegree_eq_curveChernDegree_of_isInvertible,
    curveChernDegree_eq_chowDegree_firstChernClassCapOfInvertible]
  apply chowDegree_eq_zero_of_chowCycleClass_eq_zero
  have h := chowCycleClass_firstChernClassCapOfInvertible ℚ M 0 A hA
    (cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ) (C ↘ Spec (.of ℂ)) (𝟙 C)
      ((0 + 1 : ℕ) : ℤ))
  dsimp only at h
  refine h.trans ?_
  simp only [firstChernClassTopCap, hM, LinearMap.comp_apply, map_zero, LinearMap.zero_apply]

/-- **Degrees along a curve with vanishing topological Chern class.** Let `W` be a complex
scheme carrying an ample invertible module, `L` an invertible module on `W` with
`c₁ᵗᵒᵖ(L) = 0` and `i : C ⟶ W` a closed immersion of a scheme of dimension at most one, proper
over `ℂ`. Then `deg_C(i^* L) = 0`. -/
theorem degreeOn_eq_zero_of_firstChernClassTop_eq_zero {W C : Scheme.{0}} [W.Over (Spec (.of ℂ))]
    [IsComplexScheme W] (A : W.Modules) [IsInvertibleModule W A] (hA : IsAmple W A)
    (L : W.Modules) [IsInvertibleModule W L] (hL : firstChernClassTop ℚ L = 0)
    (i : C ⟶ W) [IsClosedImmersion i] [IsProper (i ≫ W ↘ Spec (.of ℂ))]
    (hdim : topologicalKrullDim C ≤ 1) :
    haveI : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 L := ‹IsInvertibleModule W L›
    Mori.degreeOn ℂ (W ↘ Spec (.of ℂ)) i hdim L = 0 := by
  letI : C.Over (Spec (.of ℂ)) := ⟨i ≫ W ↘ Spec (.of ℂ)⟩
  haveI : i.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  haveI : IsComplexScheme C := isComplexScheme_of_isClosedImmersion i
  haveI : IsProper (C ↘ Spec (.of ℂ)) := ‹IsProper (i ≫ W ↘ Spec (.of ℂ))›
  have hA' : IsAmple C ((Scheme.Modules.pullback i).obj A) := by
    have : AlgebraicGeometry.SheafOfModules.IsInvertible W.toRingedSpace.presheaf
        (structureSheafRing W.toRingedSpace).property A := ‹IsInvertibleModule W A›
    have : AlgebraicGeometry.SheafOfModules.IsInvertible C.toRingedSpace.presheaf
        (structureSheafRing C.toRingedSpace).property ((Scheme.Modules.pullback i).obj A) :=
      isInvertibleModule_pullback i A
    exact (Stacks.AmpleBridge.isAmple_iff_isAmple _ _).mpr
      (Scheme.Modules.isAmple_pullback_of_isClosedImmersion i A
        ((Stacks.AmpleBridge.isAmple_iff_isAmple W A).mp hA))
  have hM : firstChernClassTop ℚ ((Scheme.Modules.pullback i).obj L) = 0 := by
    rw [← pullback_firstChernClassTop ℚ i L, hL, map_zero]
    rfl
  exact invertibleCurveDegree_eq_zero_of_firstChernClassTop_eq_zero hdim _ hA' _ hM

/-- `c₁ᵗᵒᵖ(L)` vanishes when the rational first Chern class of `L` on `X^an` does. -/
theorem firstChernClassTop_eq_zero_of_mapCoeff_eq_zero {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    (L : X.Modules) [IsInvertibleModule X L]
    (h : haveI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L :=
        ‹IsInvertibleModule X L›
      singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass L) = 0) :
    firstChernClassTop ℚ L = 0 := by
  have : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L := ‹IsInvertibleModule X L›
  rw [firstChernClassTop, topFirstChernClass_dual, h, map_zero]
  rfl

end Curve

/-! ### Non-vanishing of cycle classes -/

section NonVanishing

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsComplexScheme X] [IsProper (X ↘ Spec (.of ℂ))]
  (A : X.Modules) [IsInvertibleModule X A] (hA : IsAmple X A)

include hA in
/-- On a complex scheme proper over `ℂ` with an ample invertible module `A`, a class
`a ∈ A_d(X)` with `cl(a) = 0` has `deg(c₁(A)^d ∩ a) = 0`: by Fulton 19.2,
`cl(c₁(A)^d ∩ a) = c₁ᵗᵒᵖ(A)^d ∩ cl(a) = 0`. -/
theorem capDegree_eq_zero_of_chowCycleClass_eq_zero :
    ∀ (d : ℕ) (a : chowGroup (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) d),
      chowCycleClass ℚ d a = 0 →
        haveI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 A :=
          ‹IsInvertibleModule X A›
        capDegree ℂ (X ↘ Spec (.of ℂ)) (fun _ : Fin d ↦ A) a = 0
  | 0, a, h => by
    rw [capDegree_zero]
    exact chowDegree_eq_zero_of_chowCycleClass_eq_zero a h
  | d + 1, a, h => by
    have : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property A :=
      ‹IsInvertibleModule X A›
    rw [capDegree_succ]
    refine capDegree_eq_zero_of_chowCycleClass_eq_zero d _ ?_
    induction a using QuotientAddGroup.induction_on with
    | H α =>
    change chowCycleClass ℚ d ((invCap (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) A).capOnChow
      (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) (d : ℤ) (QuotientAddGroup.mk' _ α)) = 0
    rw [invCap_capOnChow_mk]
    have e := chowCycleClass_firstChernClassCapOfInvertible ℚ A d A hA α
    dsimp only at e
    rw [e]
    rw [chowCycleClass_mk] at h
    rw [h, map_zero]

include hA in
/-- **The class of a closed subscheme is non-zero** (Fulton, §19.1). On a complex scheme proper
over `ℂ` carrying an ample invertible module, the cycle class of the fundamental cycle `[Z]_d` of
a closed subscheme of dimension `d` is non-zero in `H_{2d}(X(ℂ); ℚ)`: the degree of
`c₁(A)^d ∩ [Z]_d` is positive (Stacks 0BEV), and it vanishes when `cl([Z]_d)` does. -/
theorem cycleClass_cycleAssociatedToClosedSubscheme_ne_zero {Z : Scheme.{0}} (i : Z ⟶ X)
    [IsClosedImmersion i] (d : ℕ) (hZ : topologicalKrullDim Z = (d : WithBot ℕ∞)) :
    cycleClass ℚ d (cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) i
      d) ≠ 0 := by
  intro h0
  have : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 A := ‹IsInvertibleModule X A›
  have hA' : Scheme.Modules.IsAmple X A := (Stacks.AmpleBridge.isAmple_iff_isAmple X A).mp hA
  have hpos := intersectionNumber_pos ℂ (X ↘ Spec (.of ℂ)) i d hZ (fun _ ↦ A) fun _ ↦ hA'
  rw [intersectionNumber_eq_capDegree_of_le ℂ d (X ↘ Spec (.of ℂ)) i hZ.le (fun _ ↦ A)] at hpos
  have h1 := capDegree_eq_zero_of_chowCycleClass_eq_zero A hA d
    (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ)
      (X ↘ Spec (.of ℂ)) i d)) (by rw [chowCycleClass_mk]; exact h0)
  rw [QuotientAddGroup.mk'_apply, h1] at hpos
  exact lt_irrefl _ hpos

include hA in
/-- **The cycle class of a point is non-zero.** On a complex scheme proper over `ℂ` carrying an
ample invertible module, `cl_X(x) ≠ 0` in `H_{2k}(X(ℂ); ℚ)` for every point `x` of
delta-dimension `k`. -/
theorem pointCycleClass_ne_zero {k : ℕ} (x : X)
    (hx : relativeDimension (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) x = k) :
    pointCycleClass ℚ x hx ≠ 0 := by
  have e := properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp
    (fieldChowSituation ℂ) ((integralComponentAt x).subscheme ↘ Spec (.of ℂ))
    (X ↘ Spec (.of ℂ)) (integralComponentAt x).subschemeι (comp_over _ _) (𝟙 _) k
  rw [cycleAssociatedToClosedSubscheme_congr (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) _ _
    (Category.id_comp (integralComponentAt x).subschemeι)] at e
  rw [← cycleClass_pointCycle, pointCycle_eq_properPushforward x hx, e]
  exact cycleClass_cycleAssociatedToClosedSubscheme_ne_zero A hA _ k
    (natCast_eq_dimension_integralComponentAt x hx).symm

end NonVanishing

end MMP.Chow
