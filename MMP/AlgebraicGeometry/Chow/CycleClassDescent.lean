module

public import MMP.AlgebraicGeometry.Chow.CycleClassFirstChern
public import MMP.AlgebraicGeometry.Chow.CycleClassRationalEquivalence
public import MMP.AlgebraicGeometry.Variety.SmoothVarietyConstructions
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.FibreDivisorPrincipal
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.ProductRegular
public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinityLift
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.GysinZeroSectionDischarge
public import StacksFrontier.AlgebraicGeometry.Chow.LocalEquationMultiplicity
public import StacksFrontier.AlgebraicGeometry.Curves.LinearSystemScheme.WeilDivisorClass
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierComplement
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeUnits
public import StacksFrontier.AlgebraicGeometry.Intersection.ProjectionFormulaFlat.ZeroFibreDegeneration.LineFamilyZeroSection

/-!
# The cycle class map descends to the Chow group

Let `X` be a complex scheme. By Stacks 02S4 a `k`-cycle on `X` rationally equivalent to zero is a
finite sum of fibre differences `[W₀]_k - [W_∞]_k`, for integral closed subschemes
`W ⊆ X ×_ℂ ℙ¹_ℂ` of dimension `k + 1` contained in neither distinguished section
(`MMP.Chow.cycleClass_eq_zero_of_forall_fibreDifference`). Following Fulton §19.1, the cycle
class of such a fibre difference vanishes: with `q : W ⟶ ℙ¹_ℂ` the second projection,
`W₀ = q⁻¹(D₀)` and `W_∞ = q⁻¹(D_∞)` are the zero schemes of the pulled-back canonical sections of
`𝒪(D₀)` and `𝒪(D_∞)`. On `ℙ¹_ℂ` these two invertible modules are isomorphic: the chart coordinate
`t` has `div(t) = [D₀] - [D_∞]`, and `ℙ¹_ℂ` is normal, so its Picard group injects into its Weil
divisor class group. Hence `W₀` and `W_∞` are zero schemes of non-zero sections of one invertible
module `L` on the complex variety `W` of dimension `k + 1`, and by Fulton 19.1.3
(`MMP.Chow.cycleClass_zeroScheme_eq_firstChernClassTopCap`) both cycle classes on `W` equal
`c₁ᵗᵒᵖ(L) ∩ cl(W)`. Pushing forward along the proper first projection `W ⟶ X` gives the claim.

## Main definitions

* `MMP.Chow.chowCycleClass`: the cycle class map `A_k(X) →+ H_{2k}(X(ℂ); R)` on Stacks' Chow
  group.

## Main results

* `MMP.Chow.linearlyEquivalent_lineZeroDivisor_lineInfinityDivisor`: `𝒪(D₀) ≅ 𝒪(D_∞)` on the
  projective line over a field.
* `MMP.Chow.isComplexScheme_familyBase`: a closed subscheme of `X ×_ℂ ℙ¹_ℂ` is a complex scheme.
* `MMP.Chow.cycleClass_fibreDifference_eq_zero`: the cycle class of a fibre difference vanishes.
* `MMP.Chow.cycleClass_eq_zero_of_isRationallyEquivalentToZero`: the cycle class map kills
  rationally trivial cycles.
* `MMP.Chow.chowCycleClass_mk`: `chowCycleClass` on the class of a cycle is its cycle class.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
* [Stacks Project, Tag 02S4](https://stacks.math.columbia.edu/tag/02S4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow MMP.UnderlyingSpace

namespace MMP.Chow

universe u

/-! ### `𝒪(D₀) ≅ 𝒪(D_∞)` on the projective line over a field -/

open Stacks.Divisors in
/-- On a Noetherian integral scheme `Y` of delta-dimension `n`, the coefficient of the cycle
`[D]_{n-1}` of an effective Cartier divisor `D` missing the generic point, at the generic point of
a prime divisor `Z`, is the coefficient of the Weil divisor of `D` at `Z`. -/
theorem cycleAssociatedToClosedSubscheme_apply_genericPoint_eq_effectiveCartierWeilDivisor
    (C : ChowSituation.{u}) {Y : Scheme.{u}} (p : Y ⟶ C.S) [LocallyOfFiniteType p]
    [IsIntegral Y] [IsNoetherian Y] {n : ℤ} (hn : schemeDeltaDimension C p = (n : EInt))
    (D : Y.IdealSheafData) (hD : IsEffectiveCartierDivisor D)
    (hgen : genericPoint Y ∉ (D.support : Set Y)) (Z : AlgebraicGeometry.PrimeDivisor Y) :
    (cycleAssociatedToClosedSubscheme C p D.subschemeι (n - 1)).1 Z.genericPoint =
      (effectiveCartierWeilDivisor D hD).1 Z := by
  have hgen' : genericPoint Y ∉ Set.range D.subschemeι.base := by
    rwa [Scheme.IdealSheafData.range_subschemeι]
  by_cases hZ : Z.genericPoint ∈ (D.support : Set Y)
  · obtain ⟨U, hxU, t, ht, hspan⟩ := exists_germ_span_eq_stalk_of_isLocallyPrincipal D
      (isLocallyPrincipal_of_isEffectiveCartierDivisor D hD) hgen Z.genericPoint
    have : Nonempty (U : Y.Opens) := ⟨⟨_, hxU⟩⟩
    rw [← principalDivisorCycle_apply_eq_cycleAssociatedToClosedSubscheme_apply C p hn D hgen'
      Z.coheight_genericPoint (by rwa [Scheme.IdealSheafData.range_subschemeι]) hxU t ht hspan,
      principalDivisorCycle_apply,
      effectiveCartierWeilDivisor_apply_of_stalk_eq_span D hD Z _ hspan]
    have hfin := length_quotient_idealSheafStalk_ne_top hD Z
    rw [hspan] at hfin
    exact ord_eq_ringOrd_germ Z.coheight_genericPoint hxU t ht (ENat.natCast_toNat hfin).symm
  · rw [cycleAssociatedToClosedSubscheme_apply_eq_zero_of_notMem_range C p _ _
      (by rwa [Scheme.IdealSheafData.range_subschemeι]), effectiveCartierWeilDivisor_apply,
      effectiveCartierMultiplicity_eq_zero_of_notMem_support D Z hZ]

/-- The generic point of an integral scheme lies in no proper closed subset. -/
private theorem genericPoint_notMem_of_ne_univ {Y : Scheme.{u}} [IsIntegral Y]
    (I : Y.IdealSheafData) (h : (I.support : Set Y) ≠ Set.univ) :
    genericPoint Y ∉ (I.support : Set Y) := by
  intro hmem
  refine h (Set.eq_univ_of_univ_subset ?_)
  rw [← (genericPoint_spec Y).def]
  exact (I.support.isClosed).closure_subset_iff.2 (Set.singleton_subset_iff.2 hmem)

/-- The generic point of `ℙ¹_K` does not lie on the zero divisor. -/
theorem genericPoint_notMem_support_lineZeroDivisor (K : Type u) [Field K] :
    genericPoint (relativeProjectiveLine (Spec (.of K))) ∉
      ((lineZeroDivisor (Spec (.of K))).support : Set (relativeProjectiveLine (Spec (.of K)))) := by
  let x : Spec (.of K) := Classical.arbitrary _
  refine genericPoint_notMem_of_ne_univ _ fun h ↦ ?_
  rw [coe_support_lineZeroDivisor] at h
  exact Set.disjoint_left.1 (disjoint_range_lineZeroSection_lineInfinitySection (Spec (.of K)))
    (h ▸ Set.mem_univ ((lineInfinitySection _).base x)) (Set.mem_range_self x)

/-- The generic point of `ℙ¹_K` does not lie on the infinity divisor. -/
theorem genericPoint_notMem_support_lineInfinityDivisor (K : Type u) [Field K] :
    genericPoint (relativeProjectiveLine (Spec (.of K))) ∉
      ((lineInfinityDivisor (Spec (.of K))).support :
        Set (relativeProjectiveLine (Spec (.of K)))) := by
  let x : Spec (.of K) := Classical.arbitrary _
  refine genericPoint_notMem_of_ne_univ _ fun h ↦ ?_
  rw [coe_support_lineInfinityDivisor] at h
  exact Set.disjoint_left.1 (disjoint_range_lineZeroSection_lineInfinitySection (Spec (.of K)))
    (Set.mem_range_self x) (h ▸ Set.mem_univ ((lineZeroSection _).base x))

/-- **`𝒪(D₀) ≅ 𝒪(D_∞)` on `ℙ¹_K`.** The zero and the infinity divisor of the projective line
over a field are linearly equivalent: the chart coordinate `t` has `div(t) = [D₀] - [D_∞]`, and
`ℙ¹_K` is normal, so its Picard group injects into its Weil divisor class group. -/
theorem linearlyEquivalent_lineZeroDivisor_lineInfinityDivisor (K : Type u) [Field K] :
    Stacks.Divisors.LinearlyEquivalent (lineZeroDivisor (Spec (.of K)))
      (lineInfinityDivisor (Spec (.of K))) := by
  let C := fieldChowSituation K
  let P := relativeProjectiveLine (Spec (.of K))
  let sP : P ⟶ C.S := P ↘ Spec (.of K)
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian sP
  have : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace sP
  have : IsNoetherian P := ⟨⟩
  have : IsNormal (Spec (.of K)) :=
    isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed K)
  have : IsNormal P := isNormal_of_smooth sP
  have h₀ := lineZeroDivisor_isEffectiveCartierDivisor (Spec (.of K))
  have hinf := lineInfinityDivisor_isEffectiveCartierDivisor (Spec (.of K))
  have hgen0 := genericPoint_notMem_support_lineZeroDivisor K
  have hgenInf := genericPoint_notMem_support_lineInfinityDivisor K
  have hη1 : genericPoint P ∈ (𝟙 P) ⁻¹ᵁ chartOpen (Spec (.of K)) := by
    by_contra h
    apply hgenInf
    rw [coe_support_lineInfinityDivisor, ← compl_range_affineChart]
    rintro ⟨y, hy⟩
    exact h ⟨y, trivial, hy⟩
  have hη2 : genericPoint P ∈ (𝟙 P) ⁻¹ᵁ yChartOpen (Spec (.of K)) := by
    by_contra h
    apply hgen0
    rw [coe_support_lineZeroDivisor, ← compl_range_affineYChart]
    rintro ⟨y, hy⟩
    exact h ⟨y, trivial, hy⟩
  obtain ⟨n, hdim⟩ : ∃ n : ℤ, schemeDeltaDimension C sP = n :=
    ⟨_, schemeDeltaDimension_eq_genericPoint C sP⟩
  have key := principalDivisorCycle_eq_sub_lineFibreCycles C sP (𝟙 P) hdim hη1 hη2
    (by rwa [Scheme.IdealSheafData.comap_id, Scheme.IdealSheafData.range_subschemeι])
    (by rwa [Scheme.IdealSheafData.comap_id, Scheme.IdealSheafData.range_subschemeι])
  rw [Scheme.IdealSheafData.comap_id, Scheme.IdealSheafData.comap_id] at key
  have hg : lineChartFunction (𝟙 P) hη1 ≠ 0 :=
    left_ne_zero_of_mul_eq_one (lineChartFunction_mul_lineYChartFunction (𝟙 P) hη1 hη2)
  let e := (rationalFunctionsEquivFunctionField P).1
  let u : (rationalFunctions P)ˣ :=
    Units.mk0 (e.symm (lineChartFunction (𝟙 P) hη1)) (by simpa using hg)
  rw [Stacks.Divisors.linearlyEquivalent_iff_weilDivisorClass_eq_of_isNormal,
    QuotientAddGroup.eq_iff_sub_mem]
  refine ⟨u, Subtype.ext (funext fun Z ↦ ?_)⟩
  rw [principalDivisor_apply]
  change P.ord (e (e.symm (lineChartFunction (𝟙 P) hη1))) Z.genericPoint = _
  rw [RingEquiv.apply_symm_apply, ← principalDivisorCycle_apply C sP hdim, key]
  change (cycleAssociatedToClosedSubscheme C sP _ (n - 1)).1 Z.genericPoint -
    (cycleAssociatedToClosedSubscheme C sP _ (n - 1)).1 Z.genericPoint = _
  rw [cycleAssociatedToClosedSubscheme_apply_genericPoint_eq_effectiveCartierWeilDivisor C sP hdim
      _ h₀ hgen0,
    cycleAssociatedToClosedSubscheme_apply_genericPoint_eq_effectiveCartierWeilDivisor C sP hdim
      _ hinf hgenInf]
  rfl

/-- The projective line over `ℂ` is a smooth variety. -/
instance isSmoothVariety_relativeProjectiveLine :
    IsSmoothVariety ℂ (relativeProjectiveLine (Spec (.of ℂ)) ↘ Spec (.of ℂ)) where

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsComplexScheme X]

/-- A closed subscheme `W` of `X ×_ℂ ℙ¹_ℂ`, over `ℂ` through `W ⟶ X ⟶ Spec ℂ`, is a complex
scheme: closed imbeddings `X ↪ V` give `W ↪ V ×_ℂ ℙ¹_ℂ`, a smooth variety. -/
theorem isComplexScheme_familyBase
    (W : (projectiveLineProduct (X ↘ Spec (.of ℂ))).IdealSheafData) :
    letI : W.subscheme.Over (Spec (.of ℂ)) := ⟨familyBase (X ↘ Spec (.of ℂ)) W⟩
    IsComplexScheme W.subscheme := by
  let : W.subscheme.Over (Spec (.of ℂ)) := ⟨familyBase (X ↘ Spec (.of ℂ)) W⟩
  obtain ⟨V, _, hV, i, hi, _⟩ := IsComplexScheme.exists_isClosedImmersion (X := X)
  let L := relativeProjectiveLine (Spec (.of ℂ))
  let : (pullback (V ↘ Spec (.of ℂ)) (L ↘ Spec (.of ℂ))).Over (Spec (.of ℂ)) :=
    ⟨pullback.fst _ _ ≫ V ↘ Spec (.of ℂ)⟩
  have e₁ : X ↘ Spec (.of ℂ) = i ≫ V ↘ Spec (.of ℂ) := hi.comp_over.symm
  have e₂ : L ↘ Spec (.of ℂ) = 𝟙 L ≫ L ↘ Spec (.of ℂ) := (Category.id_comp _).symm
  have : MorphismProperty.IsStableUnderComposition @IsClosedImmersion.{0} :=
    ⟨fun f g _ _ ↦ IsClosedImmersion.comp f g⟩
  have hj := MorphismProperty.pullbackMap (P := @IsClosedImmersion) (i₁ := i) (i₂ := 𝟙 L)
    inferInstance inferInstance e₁ e₂
  have hVL : IsSmoothVariety ℂ
      (pullback (V ↘ Spec (.of ℂ)) (L ↘ Spec (.of ℂ)) ↘ Spec (.of ℂ)) :=
    isSmoothVariety_pullback ℂ (V ↘ Spec (.of ℂ)) (L ↘ Spec (.of ℂ))
  refine
    { toLocallyOfFiniteType := show LocallyOfFiniteType (familyBase (X ↘ Spec (.of ℂ)) W) from
        inferInstance
      toQuasiCompact := show QuasiCompact (familyBase (X ↘ Spec (.of ℂ)) W) from inferInstance
      exists_isClosedImmersion := ⟨_, inferInstance, hVL, W.subschemeι ≫ pullback.map _ _ _ _ i
        (𝟙 L) (𝟙 _) (by rw [e₁, Category.comp_id]) (by rw [Category.comp_id, Category.id_comp]),
        ⟨?_⟩, @IsClosedImmersion.comp _ _ _ _ _ inferInstance hj⟩ }
  change (W.subschemeι ≫ pullback.map _ _ _ _ i (𝟙 L) (𝟙 _) _ _) ≫ pullback.fst _ _ ≫
      V ↘ Spec (.of ℂ) = W.subschemeι ≫ pullback.fst _ _ ≫ X ↘ Spec (.of ℂ)
  rw [Category.assoc, pullback.lift_fst_assoc, Category.assoc, ← e₁]

/-- An integral scheme locally of finite type over `ℂ` whose generic point has relative
dimension `n` has dimension `n`. -/
theorem natCast_eq_topologicalKrullDim_of_relativeDimension_genericPoint {Y : Scheme.{0}}
    [IsIntegral Y] (g : Y ⟶ Spec (.of ℂ)) [LocallyOfFiniteType g] {n : ℕ}
    (h : relativeDimension (fieldChowSituation ℂ).dimensionFunction g (genericPoint Y) = n) :
    (n : WithBot ℕ∞) = topologicalKrullDim Y := by
  have h1 := topologicalKrullDim_closure_singleton_eq ℂ g (genericPoint Y)
  rw [h, Int.toNat_natCast, (genericPoint_spec Y).def] at h1
  rw [← h1]
  exact IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ Y).isHomeomorph

variable (R : Type) [CommRing R]

/-- **The cycle class of a fibre difference vanishes** (Fulton, §19.1). Let
`W ⊆ X ×_ℂ ℙ¹_ℂ` be an integral closed subscheme of dimension `k + 1`, contained in neither
distinguished section. Then `cl([W₀]_k - [W_∞]_k) = 0` in `H_{2k}(X(ℂ); R)`. -/
theorem cycleClass_fibreDifference_eq_zero (k : ℕ)
    (W : (projectiveLineProduct (X ↘ Spec (.of ℂ))).IdealSheafData)
    (hInt : IsIntegral W.subscheme)
    (hDim : ∀ ξ : genericPoints W.subscheme,
      relativeDimension (fieldChowSituation ℂ).dimensionFunction
        (familyBase (X ↘ Spec (.of ℂ)) W) ξ.1 = k + 1)
    (h0 : ¬ Set.range W.subschemeι ⊆ Set.range (zeroSection (X ↘ Spec (.of ℂ))))
    (hInf : ¬ Set.range W.subschemeι ⊆ Set.range (infinitySection (X ↘ Spec (.of ℂ)))) :
    cycleClass R k (fibreDifference (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k W) = 0 := by
  have hP : Nonempty (Stacks.Divisors.divisorSheaf (lineZeroDivisor (Spec (.of ℂ))) ≅
      Stacks.Divisors.divisorSheaf (lineInfinityDivisor (Spec (.of ℂ)))) :=
    linearlyEquivalent_lineZeroDivisor_lineInfinityDivisor ℂ
  have := hInt
  let f := X ↘ Spec (.of ℂ)
  let Y := W.subscheme
  let : Y.Over (Spec (.of ℂ)) := ⟨familyBase f W⟩
  have : IsComplexScheme Y := isComplexScheme_familyBase W
  have : (fibreBaseProjection f W).IsOver (Spec (.of ℂ)) := ⟨fibreBaseProjection_comp f W⟩
  -- the dimension of `W`
  have hn : ((k + 1 : ℕ) : WithBot ℕ∞) = topologicalKrullDim Y :=
    natCast_eq_topologicalKrullDim_of_relativeDimension_genericPoint (familyBase f W)
      (by exact_mod_cast hDim ⟨genericPoint Y, genericPoint_mem_genericPoints Y⟩)
  obtain ⟨μ, hμ, -⟩ := existsUnique_isVarietyFundamentalClass R hn
  -- the two divisors as zero schemes of sections of one invertible module
  let φ := fibreLineProjection f W
  let e : lineZeroModule φ ≅ lineInfinityModule φ := (Scheme.Modules.pullback φ).mapIso hP.some
  let t₀ : Γ(lineInfinityModule φ, ⊤) := Scheme.Modules.Hom.app e.hom ⊤ (lineZeroModuleSection φ)
  have hZ₀ : Stacks.Divisors.zeroScheme Y (lineInfinityModule φ) t₀ = zeroDivisor f W := by
    rw [Stacks.Divisors.zeroScheme_congr_iso, zeroScheme_lineZeroModuleSection,
      zeroDivisor_eq_comap_lineZeroDivisor]
  have hZinf : Stacks.Divisors.zeroScheme Y (lineInfinityModule φ) (lineInfinityModuleSection φ) =
      infinityDivisor f W := by
    rw [zeroScheme_lineInfinityModuleSection, infinityDivisor_eq_comap_lineInfinityDivisor]
  have ht₀ : t₀ ≠ 0 := by
    intro h
    rw [h, Stacks.Divisors.zeroScheme_zero_eq_bot] at hZ₀
    exact zeroDivisor_ne_bot f W h0 hZ₀.symm
  have htinf : lineInfinityModuleSection φ ≠ 0 := by
    intro h
    rw [h, Stacks.Divisors.zeroScheme_zero_eq_bot] at hZinf
    exact infinityDivisor_ne_bot f W hInf hZinf.symm
  have : Stacks.Ample.IsInvertibleModule Y (lineInfinityModule φ) :=
    isInvertible_lineInfinityModule φ
  have c₀ : cycleClass R k (cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ)
      (familyBase f W) (Stacks.Divisors.zeroScheme Y (lineInfinityModule φ) t₀).subschemeι k) =
        firstChernClassTopCap R (lineInfinityModule φ) k μ :=
    cycleClass_zeroScheme_eq_firstChernClassTopCap R (lineInfinityModule φ) hn t₀ ht₀ hμ
  have cinf : cycleClass R k (cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ)
      (familyBase f W) (Stacks.Divisors.zeroScheme Y (lineInfinityModule φ)
        (lineInfinityModuleSection φ)).subschemeι k) =
        firstChernClassTopCap R (lineInfinityModule φ) k μ :=
    cycleClass_zeroScheme_eq_firstChernClassTopCap R (lineInfinityModule φ) hn
      (lineInfinityModuleSection φ) htinf hμ
  rw [hZ₀] at c₀
  rw [hZinf] at cinf
  rw [fibreDifference_eq_properPushforward_sub]
  refine (cycleClass_properPushforward R (fibreBaseProjection f W) _).trans ?_
  refine (congrArg _ ?_).trans (map_zero _)
  exact (map_sub (cycleClass (X := Y) R k) _ _).trans (sub_eq_zero.2 (c₀.trans cinf.symm))

/-- **The cycle class map kills rationally trivial cycles** (Fulton, §19.1): the cycle class of a
`k`-cycle on `X` rationally equivalent to zero vanishes in `H_{2k}(X(ℂ); R)`. -/
theorem cycleClass_eq_zero_of_isRationallyEquivalentToZero (k : ℕ)
    (α : CycleGroup (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k)
    (hα : IsRationallyEquivalentToZero (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k α) :
    cycleClass R k α = 0 :=
  cycleClass_eq_zero_of_forall_fibreDifference R k
    (cycleClass_fibreDifference_eq_zero R k) α hα

/-- **The cycle class map on the Chow group** `cl : A_k(X) →+ H_{2k}(X(ℂ); R)` (Fulton, §19.1):
the cycle class map of Stacks' cycles descends along rational equivalence. -/
def chowCycleClass (k : ℕ) :
    chowGroup (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k →+ BMHomology R X (2 * k) :=
  QuotientAddGroup.lift (rationalEquivalences (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k)
    (cycleClass R k) fun α hα ↦ cycleClass_eq_zero_of_isRationallyEquivalentToZero R k α hα

/-- The cycle class of the rational equivalence class of a cycle `α` is the cycle class of `α`. -/
@[simp]
theorem chowCycleClass_mk (k : ℕ) (α : CycleGroup (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k) :
    chowCycleClass R k (QuotientAddGroup.mk α) = cycleClass R k α :=
  rfl

end MMP.Chow
