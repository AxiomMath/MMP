module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.DiagonalUnit
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.RegularImmersionStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Chow.Intersection.CohenMacaulayIntersectionProduct
public import StacksFrontier.AlgebraicGeometry.Chow.Intersection.DiagonalGysinCapRegular
public import StacksFrontier.AlgebraicGeometry.Chow.DiagonalVirtualNormalBundle

/-!
# The fundamental class is the unit of the Stacks self-intersection product

Let `X` be a quasi-compact scheme smooth of relative dimension `n` over a field `K`, whose
diagonal `Δ : X ⟶ X ×_K X` is a regular closed immersion of codimension `n`. For the
intersection product `Stacks.Chow.selfIntersectionProduct` formed with the normal sheaf class
`c(Δ, 𝒩) = Stacks.Chow.regularNormalGysinClass` of the diagonal, the fundamental class
`[X] ∈ CH_n(X)` is a two-sided unit: `x · [X] = x` and `[X] · x = x` for `x ∈ CH_k(X)`.

Both products are bilinear, so it suffices to take `x = [V]_k` for an integral closed subscheme
`V ⊆ X` of `δ`-dimension `k` (`Stacks.Chow.cycleGroup_addMonoidHom_ext`, which needs `X`
quasi-compact). There Stacks 0FFD
(`Stacks.Chow.Intersection.selfIntersectionProduct_mk_cycleAssociatedToClosedSubscheme`) gives
`[V]_k · [X]_n = [V ×_X X]_k`: the class `c(Δ, 𝒩)` satisfies the Cohen–Macaulay form of Stacks
0FEA (`Stacks.Chow.BivariantClass.capCohenMacaulayFormula_of_capRegularFormula` from
`Stacks.Chow.virtualNormalGysinClass_capRegularFormula`), `V ×_X X ≅ V` has `δ`-dimension `k`,
and the only point of `V ×_X X` of `δ`-dimension `k` is the generic point of `V`, where `𝒪_V` is a
field and `𝒪_X` is Cohen–Macaulay because `X` is smooth over `K`.

## Main results

* `MMP.Chow.regularNormalGysinClass_capCohenMacaulayFormula`: `c(Δ, 𝒩)` satisfies the
  Cohen–Macaulay form of Stacks 0FEA in every degree.
* `MMP.Chow.selfIntersectionProduct_fundamentalChowClass_of_field` and
  `MMP.Chow.fundamentalChowClass_selfIntersectionProduct_of_field`: `x · [X] = x` and
  `[X] · x = x` over a field `K`.
* `MMP.Chow.selfIntersectionProduct_fundamentalChowClass` and
  `MMP.Chow.fundamentalChowClass_selfIntersectionProduct`: the same for a smooth complex scheme.

## References

* [Stacks Project, Tag 0FFD](https://stacks.math.columbia.edu/tag/0FFD)
* [Stacks Project, Tag 0FEA](https://stacks.math.columbia.edu/tag/0FEA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow
  Stacks.AlgebraicGeometry.RegularIdealSheaf

universe u

namespace MMP.Chow

/-- Additive maps out of the Chow group of a compact scheme agree if they agree on the classes of
the integral closed subschemes `closure {x}` of the points of the right relative dimension. -/
theorem chowGroup_apply_eq_of_forall_integralComponentAt {C : ChowSituation.{u}}
    {T : Scheme.{u}} (p : T ⟶ C.S) [LocallyOfFiniteType p] [CompactSpace T] {m : ℤ} {M : Type*}
    [AddCommGroup M] {φ ψ : chowGroup C p m →+ M}
    (h : ∀ x : T, relativeDimension C.dimensionFunction p x = m →
      φ (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme C p
        (integralComponentAt x).subschemeι m)) =
        ψ (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme C p
          (integralComponentAt x).subschemeι m)))
    (c : chowGroup C p m) : φ c = ψ c := by
  induction c using QuotientAddGroup.induction_on with
  | H α =>
    exact DFunLike.congr_fun (cycleGroup_addMonoidHom_ext
      (φ := φ.comp (QuotientAddGroup.mk' _)) (ψ := ψ.comp (QuotientAddGroup.mk' _)) h) α

/-- An additive endomorphism of the Chow group of a compact scheme is the identity if it fixes the
classes of the integral closed subschemes `closure {x}` of the points of the right relative
dimension. -/
theorem chowGroup_eq_of_forall_integralComponentAt {C : ChowSituation.{u}}
    {T : Scheme.{u}} (p : T ⟶ C.S) [LocallyOfFiniteType p] [CompactSpace T] {m : ℤ}
    (φ : chowGroup C p m →+ chowGroup C p m)
    (h : ∀ x : T, relativeDimension C.dimensionFunction p x = m →
      φ (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme C p
        (integralComponentAt x).subschemeι m)) =
        QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme C p
          (integralComponentAt x).subschemeι m))
    (c : chowGroup C p m) : φ c = c :=
  (chowGroup_apply_eq_of_forall_integralComponentAt (C := C) p (φ := φ) (ψ := AddMonoidHom.id _)
    (fun x hx ↦ by rw [AddMonoidHom.id_apply]; exact h x hx) c).trans (AddMonoidHom.id_apply _ c)

section Field

variable {K : Type u} [Field K] {X : Scheme.{u}} (sX : X ⟶ (fieldChowSituation K).S)
  [LocallyOfFiniteType sX] [IsClosedImmersion (pullback.diagonal sX)] {n : ℕ}
  (hΔ : IsRegularClosedImmersionOfCodim (pullback.diagonal sX) n)

/-- **Stacks 0FEA for the normal sheaf class of the diagonal.** The class
`c(Δ, 𝒩) ∈ A^n(X ⟶ X ×_K X)` of a diagonal that is a regular closed immersion of codimension `n`
satisfies the Cohen–Macaulay form of the excess intersection formula in every degree. -/
theorem regularNormalGysinClass_capCohenMacaulayFormula (m : ℤ) :
    (regularNormalGysinClass (fieldChowSituation K) sX (selfProductStructure _ sX)
        (pullback.diagonal sX) (diagonal_comp_selfProductStructure _ sX) hΔ).CapCohenMacaulayFormula
      (fieldChowSituation K) (gysinSystemOfInvertible _) sX (selfProductStructure _ sX)
      (pullback.diagonal sX) (diagonal_comp_selfProductStructure _ sX) n m := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have := hΔ.isFiniteLocallyFreeOfRank_conormalModule
  exact BivariantClass.capCohenMacaulayFormula_of_capRegularFormula (fieldChowSituation K)
    (gysinSystemOfInvertible _) sX (selfProductStructure _ sX) (pullback.diagonal sX)
    (diagonal_comp_selfProductStructure _ sX) n
    (VirtualNormalBundle.ofIsRegularImmersion _ hΔ.isRegularImmersion) inferInstance _
    (virtualNormalGysinClass_capRegularFormula (fieldChowSituation K) sX
      (selfProductStructure _ sX) (pullback.diagonal sX)
      (diagonal_comp_selfProductStructure _ sX) _ n m)

variable [Smooth sX] (hn : RelativeDimension sX n)

include hn

omit [IsClosedImmersion (pullback.diagonal sX)] [Smooth sX] in
/-- Every irreducible component of `X`, read through `𝟙 X ≫ sX`, has `δ`-dimension `n`. -/
theorem deltaDimension_id_comp_irreducibleComponent (T : irreducibleComponents X) :
    deltaDimension (fieldChowSituation K) (𝟙 X ≫ sX)
      ⟨T, T.2.1, isClosed_of_mem_irreducibleComponents _ T.2⟩ = n := by
  rw [Stacks.WeilCohomology.deltaDimension_congr (Category.id_comp sX)]
  exact Stacks.WeilCohomology.deltaDimension_irreducibleComponent_of_relativeDimension K sX n hn T

/-- **`[V]_m · [X]_n = [V]_m` for an integral closed subscheme `V`** (Stacks 0FFD with
`V ∩ X = V`). -/
theorem selfIntersectionProduct_mk_fundamentalChowClass {V : Scheme.{u}} [IsIntegral V]
    (i : V ⟶ X) [IsClosedImmersion i] (m : ℤ)
    (hV : schemeDeltaDimension (fieldChowSituation K) (i ≫ sX) = (m : EInt)) :
    chowGroupDegreeEquiv (fieldChowSituation K) sX (show m + n - n = m by ring)
        (selfIntersectionProduct (fieldChowSituation K)
          (Stacks.Chow.fieldChowSituation_dimensionFunction_of_isClosed K)
          (gysinSystemOfInvertible _) sX n
          (regularNormalGysinClass (fieldChowSituation K) sX (selfProductStructure _ sX)
            (pullback.diagonal sX) (diagonal_comp_selfProductStructure _ sX) hΔ) m n
          (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation K) sX i m))
          (fundamentalChowClass (fieldChowSituation K) sX n)) =
      QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation K) sX i m) := by
  have hgen := hV
  rw [schemeDeltaDimension_eq_genericPoint] at hgen
  replace hgen := WithBotTop.coe_injective hgen
  have hfund : fundamentalChowClass (fieldChowSituation K) sX n =
      QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation K) sX (𝟙 X) n) :=
    rfl
  rw [hfund]
  refine (Intersection.selfIntersectionProduct_mk_cycleAssociatedToClosedSubscheme K
    (gysinSystemOfInvertible _) sX n _ i (𝟙 X) m n m (by ring)
    (regularNormalGysinClass_capCohenMacaulayFormula sX hΔ _)
    (Stacks.WeilCohomology.deltaDimension_irreducibleComponent_of_irreducibleSpace _ hV)
    (deltaDimension_id_comp_irreducibleComponent sX hn) ?_ ?_).trans ?_
  · rw [Stacks.Chow.schemeDeltaDimension_congr _
        (show pullback.fst i (𝟙 X) ≫ i ≫ sX = (asIso (pullback.fst i (𝟙 X))).hom ≫ i ≫ sX
          from rfl),
      schemeDeltaDimension_comp_iso, hV]
  · intro ζ hζ
    refine ⟨Stacks.WeilCohomology.isCohenMacaulayLocalRing_stalk_of_relativeDimension_eq K
      (i ≫ sX) ?_, Stacks.WeilCohomology.isCohenMacaulayLocalRing_stalk_of_smooth K sX _⟩
    rw [hgen, ← relativeDimension_comp_closedImmersion]
    exact hζ
  · exact congrArg _ (cycleAssociatedToClosedSubscheme_eq_of_iso _ _ _ _
      (asIso (pullback.fst i (𝟙 X))) rfl _)

/-- **`[X]_n · [V]_m = [V]_m` for an integral closed subscheme `V`** (Stacks 0FFD with
`X ∩ V = V`). -/
theorem fundamentalChowClass_selfIntersectionProduct_mk {V : Scheme.{u}} [IsIntegral V]
    (i : V ⟶ X) [IsClosedImmersion i] (m : ℤ)
    (hV : schemeDeltaDimension (fieldChowSituation K) (i ≫ sX) = (m : EInt)) :
    chowGroupDegreeEquiv (fieldChowSituation K) sX (show n + m - n = m by ring)
        (selfIntersectionProduct (fieldChowSituation K)
          (Stacks.Chow.fieldChowSituation_dimensionFunction_of_isClosed K)
          (gysinSystemOfInvertible _) sX n
          (regularNormalGysinClass (fieldChowSituation K) sX (selfProductStructure _ sX)
            (pullback.diagonal sX) (diagonal_comp_selfProductStructure _ sX) hΔ) n m
          (fundamentalChowClass (fieldChowSituation K) sX n)
          (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation K) sX i m))) =
      QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation K) sX i m) := by
  have hgen := hV
  rw [schemeDeltaDimension_eq_genericPoint] at hgen
  replace hgen := WithBotTop.coe_injective hgen
  have hfund : fundamentalChowClass (fieldChowSituation K) sX n =
      QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation K) sX (𝟙 X) n) :=
    rfl
  rw [hfund]
  refine (Intersection.selfIntersectionProduct_mk_cycleAssociatedToClosedSubscheme K
    (gysinSystemOfInvertible _) sX n _ (𝟙 X) i n m m (by ring)
    (regularNormalGysinClass_capCohenMacaulayFormula sX hΔ _)
    (deltaDimension_id_comp_irreducibleComponent sX hn)
    (Stacks.WeilCohomology.deltaDimension_irreducibleComponent_of_irreducibleSpace _ hV)
    ?_ ?_).trans ?_
  · rw [Stacks.Chow.schemeDeltaDimension_congr _
        (show pullback.fst (𝟙 X) i ≫ 𝟙 X ≫ sX = (asIso (pullback.snd (𝟙 X) i)).hom ≫ i ≫ sX
          from pullback.condition_assoc sX),
      schemeDeltaDimension_comp_iso, hV]
  · intro ζ hζ
    refine ⟨Stacks.WeilCohomology.isCohenMacaulayLocalRing_stalk_of_smooth K sX _,
      Stacks.WeilCohomology.isCohenMacaulayLocalRing_stalk_of_relativeDimension_eq K
      (i ≫ sX) ?_⟩
    rw [hgen, ← relativeDimension_comp_closedImmersion, ← pullback.condition_assoc]
    exact hζ
  · exact congrArg _ (cycleAssociatedToClosedSubscheme_eq_of_iso _ _ _ _
      (asIso (pullback.snd (𝟙 X) i)) pullback.condition.symm _)

variable [CompactSpace X]

/-- **`x · [X] = x`** for the Stacks self-intersection product of a quasi-compact scheme smooth of
relative dimension `n` over a field, formed with the normal sheaf class of the diagonal. -/
theorem selfIntersectionProduct_fundamentalChowClass_of_field (m : ℤ)
    (x : chowGroup (fieldChowSituation K) sX m) :
    chowGroupDegreeEquiv (fieldChowSituation K) sX (show m + n - n = m by ring)
        (selfIntersectionProduct (fieldChowSituation K)
          (Stacks.Chow.fieldChowSituation_dimensionFunction_of_isClosed K)
          (gysinSystemOfInvertible _) sX n
          (regularNormalGysinClass (fieldChowSituation K) sX (selfProductStructure _ sX)
            (pullback.diagonal sX) (diagonal_comp_selfProductStructure _ sX) hΔ) m n
          x (fundamentalChowClass (fieldChowSituation K) sX n)) = x := by
  let φ : chowGroup (fieldChowSituation K) sX m →+ chowGroup (fieldChowSituation K) sX m :=
    AddMonoidHom.mk' (fun c : chowGroup (fieldChowSituation K) sX m ↦
      chowGroupDegreeEquiv (fieldChowSituation K) sX (show m + n - n = m by ring)
        (selfIntersectionProduct (fieldChowSituation K)
          (Stacks.Chow.fieldChowSituation_dimensionFunction_of_isClosed K)
          (gysinSystemOfInvertible _) sX n
          (regularNormalGysinClass (fieldChowSituation K) sX (selfProductStructure _ sX)
            (pullback.diagonal sX) (diagonal_comp_selfProductStructure _ sX) hΔ) m n
          c (fundamentalChowClass (fieldChowSituation K) sX n)))
      (fun c c' ↦ by simp only [map_add, LinearMap.add_apply])
  have hφ (c : chowGroup (fieldChowSituation K) sX m) : φ c = _ :=
    congrFun (AddMonoidHom.mk'_apply _ _) c
  have key := chowGroup_eq_of_forall_integralComponentAt sX φ (fun y hy ↦ by
    have := isIntegral_integralComponentAt y
    rw [hφ]
    exact selfIntersectionProduct_mk_fundamentalChowClass sX hΔ hn _ m
      (schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq _ _ y hy)) x
  rw [hφ] at key
  exact key

/-- **`[X] · x = x`** for the Stacks self-intersection product of a quasi-compact scheme smooth of
relative dimension `n` over a field, formed with the normal sheaf class of the diagonal. -/
theorem fundamentalChowClass_selfIntersectionProduct_of_field (m : ℤ)
    (x : chowGroup (fieldChowSituation K) sX m) :
    chowGroupDegreeEquiv (fieldChowSituation K) sX (show n + m - n = m by ring)
        (selfIntersectionProduct (fieldChowSituation K)
          (Stacks.Chow.fieldChowSituation_dimensionFunction_of_isClosed K)
          (gysinSystemOfInvertible _) sX n
          (regularNormalGysinClass (fieldChowSituation K) sX (selfProductStructure _ sX)
            (pullback.diagonal sX) (diagonal_comp_selfProductStructure _ sX) hΔ) n m
          (fundamentalChowClass (fieldChowSituation K) sX n) x) = x := by
  let φ : chowGroup (fieldChowSituation K) sX m →+ chowGroup (fieldChowSituation K) sX m :=
    AddMonoidHom.mk' (fun c : chowGroup (fieldChowSituation K) sX m ↦
      chowGroupDegreeEquiv (fieldChowSituation K) sX (show n + m - n = m by ring)
        (selfIntersectionProduct (fieldChowSituation K)
          (Stacks.Chow.fieldChowSituation_dimensionFunction_of_isClosed K)
          (gysinSystemOfInvertible _) sX n
          (regularNormalGysinClass (fieldChowSituation K) sX (selfProductStructure _ sX)
            (pullback.diagonal sX) (diagonal_comp_selfProductStructure _ sX) hΔ) n m
          (fundamentalChowClass (fieldChowSituation K) sX n) c))
      (fun c c' ↦ by simp only [map_add])
  have hφ (c : chowGroup (fieldChowSituation K) sX m) : φ c = _ :=
    congrFun (AddMonoidHom.mk'_apply _ _) c
  have key := chowGroup_eq_of_forall_integralComponentAt sX φ (fun y hy ↦ by
    have := isIntegral_integralComponentAt y
    rw [hφ]
    exact fundamentalChowClass_selfIntersectionProduct_mk sX hΔ hn _ m
      (schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq _ _ y hy)) x
  rw [hφ] at key
  exact key

end Field

section Complex

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsSeparated (X ↘ Spec (.of ℂ))]
  [CompactSpace X] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] {n : ℕ}
  [SmoothOfRelativeDimension n (X ↘ Spec (.of ℂ))]
  (hΔ : IsRegularClosedImmersionOfCodim (pullback.diagonal (X ↘ Spec (.of ℂ))) n)

/-- **`x · [X] = x`** (the fundamental class is a right unit of the Stacks self-intersection
product, formed with the normal sheaf class of the diagonal) on a quasi-compact separated scheme
smooth of relative dimension `n` over `ℂ`. -/
theorem selfIntersectionProduct_fundamentalChowClass (k : ℤ)
    (x : chowGroup (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k) :
    chowGroupDegreeEquiv (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) (by ring : k + n - n = k)
      (selfIntersectionProduct (fieldChowSituation ℂ)
        (fun s _ ↦ fieldChowSituation_dimensionFunction ℂ s) (gysinSystemOfInvertible _)
        (X ↘ Spec (.of ℂ)) n
        (regularNormalGysinClass (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ))
          (selfProductStructure _ (X ↘ Spec (.of ℂ))) (pullback.diagonal _)
          (diagonal_comp_selfProductStructure _ _) hΔ)
        k n x (fundamentalChowClass (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) n)) = x :=
  have : Smooth (X ↘ Spec (.of ℂ)) := SmoothOfRelativeDimension.smooth n _
  selfIntersectionProduct_fundamentalChowClass_of_field (X ↘ Spec (.of ℂ)) hΔ
    (SmoothOfRelativeDimension.relativeDimension n _) k x

/-- **`[X] · x = x`** (the fundamental class is a left unit of the Stacks self-intersection
product, formed with the normal sheaf class of the diagonal) on a quasi-compact separated scheme
smooth of relative dimension `n` over `ℂ`. -/
theorem fundamentalChowClass_selfIntersectionProduct (k : ℤ)
    (x : chowGroup (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k) :
    chowGroupDegreeEquiv (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) (by ring : n + k - n = k)
      (selfIntersectionProduct (fieldChowSituation ℂ)
        (fun s _ ↦ fieldChowSituation_dimensionFunction ℂ s) (gysinSystemOfInvertible _)
        (X ↘ Spec (.of ℂ)) n
        (regularNormalGysinClass (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ))
          (selfProductStructure _ (X ↘ Spec (.of ℂ))) (pullback.diagonal _)
          (diagonal_comp_selfProductStructure _ _) hΔ)
        n k (fundamentalChowClass (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) n) x) = x :=
  have : Smooth (X ↘ Spec (.of ℂ)) := SmoothOfRelativeDimension.smooth n _
  fundamentalChowClass_selfIntersectionProduct_of_field (X ↘ Spec (.of ℂ)) hΔ
    (SmoothOfRelativeDimension.relativeDimension n _) k x

end Complex

end MMP.Chow

end
