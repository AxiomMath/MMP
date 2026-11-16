module

public import MMP.AlgebraicGeometry.Positivity.RelativeAmplePullbackTwist
public import MMP.AlgebraicGeometry.Divisor.EffectiveCartierDivisorSupport
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.PositivityDivisor

/-!
# Closed subsets of a quasi-projective variety lie in effective Cartier divisors

## Main results

* `MMP.Threefold.Resolution.exists_isEffective_subset_cartierSupport_of_notMem`: a closed `T`
  lies in the support of an effective Cartier divisor avoiding a given point `y₀ ∉ T`.
* `MMP.Threefold.Resolution.exists_isEffective_subset_cartierSupport`: a proper closed subset
  `T ≠ Y` lies in the support of an effective Cartier divisor.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite RingedSpaceModuleAdjunction MMP.Mori Stacks.Ample

namespace MMP.Threefold.Resolution

section QuasiProjective

variable {k : Type u} [Field k] {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)}

/-- **A closed subset of a quasi-projective variety lies in an effective Cartier divisor
avoiding a given point.** If `Y` is a quasi-projective variety over `k`, `T ⊆ Y` is closed and
`y₀ ∉ T`, there is an effective Cartier divisor `D` on `Y` with `T ⊆ Supp D` and `y₀ ∉ Supp D`. -/
theorem exists_isEffective_subset_cartierSupport_of_notMem (hY : Mori.IsVariety k sY)
    (hYqp : Stacks.HProjective.IsHQuasiProjective sY) {T : Set Y} (hT : IsClosed T) {y₀ : Y}
    (hy₀ : y₀ ∉ T) :
    ∃ D : Y.CartierDivisor, MMP.Intersection.IsEffective D ∧
      T ⊆ MMP.Intersection.cartierSupport D ∧ y₀ ∉ MMP.Intersection.cartierSupport D := by
  have : IsIntegral Y := hY.toIsIntegral
  obtain ⟨-, L, hLinv, hLamp⟩ :=
    Stacks.HProjective.isQuasiProjective_of_isHQuasiProjective sY hYqp
  have hL : Stacks.Ample.IsAmple Y L :=
    Stacks.HProjective.isAmple_of_isRelativelyAmple_of_isAffine sY L hLamp
  -- a section `s` of some `L^n` whose nonvanishing locus contains `y₀` and misses `T`
  obtain ⟨n, -, s, -, hηs, hsT⟩ :=
    Stacks.AmpleFiniteAffineNonvanishing.exists_affine_nonvanishingOpen_containing_finite L hL
      (Set.finite_singleton y₀) ⟨Tᶜ, hT.isOpen_compl⟩
      (Set.singleton_subset_iff.2 hy₀)
  have : SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property
      (Stacks.Ample.tensorPowModule Y L (n : ℤ)) :=
    InvertibleSheafGeneral.isInvertible_of_isInvertibleModule _
  have hx₀ : y₀ ∈ Stacks.Ample.nonvanishingLocus
      (Stacks.Ample.tensorPowModule Y L (n : ℤ)) s :=
    (Stacks.AmpleTheory.coe_powNonvanishingOpen Y L n s) ▸ hηs rfl
  have hne0 : s ≠ 0 := by
    intro h
    rw [h, Stacks.Ample.mem_nonvanishingLocus_iff] at hx₀
    exact hx₀ (by simp)
  have hevaltop : (Stacks.SheafOfModules.sectionsOfTop
      (Stacks.Ample.tensorPowModule Y L (n : ℤ)) s).eval (op ⊤) = s :=
    Stacks.SheafOfModules.sectionsOfTop_eval_top _ s
  have hne0' : (Stacks.SheafOfModules.sectionsOfTop
      (Stacks.Ample.tensorPowModule Y L (n : ℤ)) s).eval (op ⊤) ≠ 0 := by
    rwa [hevaltop]
  -- `s` is regular, so its zero scheme is an effective Cartier divisor
  have hreg : IsRegularSection Y.sheaf.obj Y.ringCatSheaf.property
      (Stacks.SheafOfModules.sectionsOfTop (Stacks.Ample.tensorPowModule Y L (n : ℤ)) s) :=
    isRegularSection_of_eval_top_ne_zero _ _ hne0'
  have hZc : Stacks.Divisors.IsEffectiveCartierDivisor
      (zeroScheme Y (Stacks.Ample.tensorPowModule Y L (n : ℤ))
        ((Stacks.SheafOfModules.sectionsOfTop
          (Stacks.Ample.tensorPowModule Y L (n : ℤ)) s).eval (op ⊤))) :=
    (isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection Y _ _).2 hreg
  have hcompl := nonvanishingLocus_eq_compl_supportSet_zeroScheme
      (Stacks.Ample.tensorPowModule Y L (n : ℤ)) _ hne0'
  have hnv : Stacks.Ample.nonvanishingLocus (Stacks.Ample.tensorPowModule Y L (n : ℤ)) s =
      (zeroScheme Y (Stacks.Ample.tensorPowModule Y L (n : ℤ))
        ((Stacks.SheafOfModules.sectionsOfTop
          (Stacks.Ample.tensorPowModule Y L (n : ℤ)) s).eval (op ⊤))).supportSetᶜ := by
    rw [← hcompl]
    conv_lhs => rw [← hevaltop]
    rw [← Stacks.AmplePredicateBridge.coe_nonvanishingOpen_eval Y _
        (Stacks.SheafOfModules.sectionsOfTop (Stacks.Ample.tensorPowModule Y L (n : ℤ)) s)]
    rfl
  -- the Cartier divisor whose closed subscheme is the zero scheme of `s`
  obtain ⟨D, hD, hDZ⟩ :=
    (MMP.CartierDivisor.isEffectiveCartierDivisor_iff_exists_subscheme_eq _).1 hZc
  have h1 := MMP.CartierDivisor.coe_support_subscheme hD
  rw [hDZ] at h1
  refine ⟨D, hD, ?_, ?_⟩
  · intro x hx
    have hxZ : x ∈ ((zeroScheme Y (Stacks.Ample.tensorPowModule Y L (n : ℤ))
        ((Stacks.SheafOfModules.sectionsOfTop
          (Stacks.Ample.tensorPowModule Y L (n : ℤ)) s).eval (op ⊤))).support : Set Y) := by
      by_contra hxZ
      have hx' : x ∈ Stacks.Ample.nonvanishingLocus
          (Stacks.Ample.tensorPowModule Y L (n : ℤ)) s := by
        rwa [hnv]
      rw [← Stacks.AmpleTheory.coe_powNonvanishingOpen Y L n s] at hx'
      exact hsT hx' hx
    exact h1 ▸ hxZ
  · rw [← h1]
    rwa [hnv] at hx₀

/-- **Every proper closed subset of a quasi-projective variety lies in an effective Cartier
divisor.** If `Y` is a quasi-projective variety over `k` and `T ⊊ Y` is closed, there is an
effective Cartier divisor `D` on `Y` with `T ⊆ Supp D`. -/
@[mmp "lem_mmp_foundation_quasiprojective_closed_set_in_cartier"]
theorem exists_isEffective_subset_cartierSupport (hY : Mori.IsVariety k sY)
    (hYqp : Stacks.HProjective.IsHQuasiProjective sY) {T : Set Y} (hT : IsClosed T)
    (hTY : T ≠ Set.univ) :
    ∃ D : Y.CartierDivisor, MMP.Intersection.IsEffective D ∧
      T ⊆ MMP.Intersection.cartierSupport D := by
  have : IsIntegral Y := hY.toIsIntegral
  have hη : genericPoint Y ∉ T := by
    intro h
    apply hTY
    have := (genericPoint_spec Y).def ▸ (closure_minimal (Set.singleton_subset_iff.2 h) hT)
    exact Set.eq_univ_of_univ_subset this
  obtain ⟨D, hD, hTD, -⟩ := exists_isEffective_subset_cartierSupport_of_notMem hY hYqp hT hη
  exact ⟨D, hD, hTD⟩

end QuasiProjective

end MMP.Threefold.Resolution
