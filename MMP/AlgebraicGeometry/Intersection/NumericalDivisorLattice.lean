module

public import MMP.AlgebraicGeometry.Intersection.N1FiniteDimensionalProper

/-!
# `Num(X)` is a lattice in `N₁(X)^*`

Let `k` be an algebraically closed field of characteristic zero and `X` a proper variety over
`k`. The group `Num(X) ⊆ N₁(X)^*` of the degree forms `z ↦ (L · z)` of invertible sheaves `L`
(`MMP.Mori.numericalDivisorGroup`) is a free abelian group of finite rank equal to the Picard
number `ρ(X) = dim_ℝ N₁(X)` (`MMP.Mori.picardNumber`), and every `ℤ`-basis of `Num(X)` is an
`ℝ`-basis of the dual space `N₁(X)^*`. Only numerical equivalence is involved; nothing is
asserted about the Néron–Severi group.

## Main results

* `MMP.Mori.numericalDivisorGroup_free_finrank_and_basis`: `Num(X)` is a free, finitely
  generated `ℤ`-module of rank `ρ(X)`, and the image in `N₁(X)^*` of any `ℤ`-basis of `Num(X)`
  is linearly independent over `ℝ` and spans `N₁(X)^*`.

## Implementation notes

The integer-lattice step (a subgroup of `ℤ^ρ` is free of rank at most `ρ`, and integer-linear
independence of integer vectors survives to `ℝ`) is taken from Mathlib's theory of `ℤ`-lattices,
`IsZLattice`, `ZLattice.rank` and `Module.Basis.ofZLatticeBasis`, applied to the image of
`Num(X)` in `ℝ^ρ` under evaluation at a basis of `N₁(X)` made of classes of proper curves.

That `Num(X)` spans `N₁(X)^*` is read off from the definition of `N₁(X)` as the quotient by the
common kernel of the degree forms of all invertible sheaves, all of which lie in `Num(X)`.

## References

* [KM98] J. Kollár, S. Mori, *Birational geometry of algebraic varieties*, §3.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace MMP.Mori

section Helpers

open Module Submodule

/-- Let `V` be a finite-dimensional real vector space, spanned by a set `S`, and let `M` be a
subgroup of `V^*` whose forms take integer values on `S` and which spans `V^*` over `ℝ`. Then `M`
is a free abelian group of rank `dim V`, and every `ℤ`-basis of `M` is an `ℝ`-basis of `V^*`. -/
private theorem free_finite_finrank_eq_and_basis_of_span_dual {V : Type*} [AddCommGroup V]
    [Module ℝ V] [FiniteDimensional ℝ V]
    (S : Set V) (hS : span ℝ S = ⊤) (M : AddSubgroup (Dual ℝ V))
    (hint : ∀ φ ∈ M, ∀ v ∈ S, ∃ n : ℤ, φ v = n)
    (hspan : span ℝ (M : Set (Dual ℝ V)) = ⊤) :
    Module.Free ℤ M ∧ Module.Finite ℤ M ∧ finrank ℤ M = finrank ℝ V ∧
      ∀ {ι : Type*} (b : Basis ι ℤ M),
        LinearIndependent ℝ (fun i => (b i : Dual ℝ V)) ∧
          span ℝ (Set.range fun i => (b i : Dual ℝ V)) = ⊤ := by
  classical
  obtain ⟨T, hTS, hTspan, hTli⟩ := exists_linearIndependent ℝ S
  let e : Basis T ℝ V := Basis.mk hTli (by rw [Subtype.range_coe, hTspan, hS])
  have : Fintype T := FiniteDimensional.fintypeBasisIndex e
  let ev : Dual ℝ V ≃ₗ[ℝ] (T → ℝ) := e.dualBasis.equivFun
  have hev : ∀ φ i, ev φ i = φ (e i) := fun φ i => by simp [ev]
  let N : Submodule ℤ (T → ℝ) := (M.toIntSubmodule).map (ev.toLinearMap.restrictScalars ℤ)
  let f : M ≃ₗ[ℤ] N :=
    Submodule.equivMapOfInjective (ev.toLinearMap.restrictScalars ℤ) ev.injective M.toIntSubmodule
  have hf : ∀ φ : M, (f φ : T → ℝ) = ev φ := fun _ => rfl
  have hN : N ≤ span ℤ (Set.range (Pi.basisFun ℝ T)) := by
    rintro _ ⟨φ, hφ, rfl⟩
    rw [Basis.mem_span_iff_repr_mem]
    intro i
    obtain ⟨n, hn⟩ := hint φ hφ (e i) (hTS (by simp [e]))
    exact ⟨n, by simp [hev, hn]⟩
  have : DiscreteTopology N :=
    DiscreteTopology.of_subset (s := (span ℤ (Set.range (Pi.basisFun ℝ T)) : Set (T → ℝ)))
      (inferInstanceAs (DiscreteTopology (span ℤ (Set.range (Pi.basisFun ℝ T))))) hN
  have : IsZLattice ℝ N := ⟨by
    rw [show (N : Set (T → ℝ)) = (ev : Dual ℝ V →ₗ[ℝ] (T → ℝ)) '' (M : Set (Dual ℝ V)) from rfl,
      Submodule.span_image, hspan, Submodule.map_top, LinearEquiv.range]⟩
  refine ⟨Module.Free.of_equiv f.symm, Module.Finite.equiv f.symm, ?_, fun b => ?_⟩
  · rw [f.finrank_eq, ZLattice.rank ℝ N, Module.finrank_fintype_fun_eq_card,
      Module.finrank_eq_card_basis e]
  · let B := ((b.map f).ofZLatticeBasis ℝ N).map ev.symm
    have hB : (fun i => (b i : Dual ℝ V)) = B := funext fun i => by
      simp [B, Basis.ofZLatticeBasis_apply, hf]
    rw [hB]
    exact ⟨B.linearIndependent, B.span_eq⟩

variable {k : Type} [Field k] {X : Scheme.{0}} (sX : X ⟶ Spec (.of k))

/-- The classes of proper curves span `N₁(X)`. -/
private theorem span_range_numericalClass_cycle_eq_top :
    span ℝ (Set.range fun C : ProperCurve sX => OneCycle.numericalClass sX (C.cycle ℝ)) = ⊤ := by
  have : (Set.range fun C : ProperCurve sX => OneCycle.numericalClass sX (C.cycle ℝ)) =
      OneCycle.numericalClass sX '' Set.range (Finsupp.basisSingleOne (R := ℝ)) := by
    rw [← Set.range_comp]
    rfl
  rw [this, Submodule.span_image, Finsupp.basisSingleOne.span_eq, Submodule.map_top,
    LinearMap.range_eq_top]
  exact OneCycle.numericalClass_surjective sX

/-- Every form in `Num(X)` takes integer values on the classes of proper curves. -/
private theorem exists_int_of_mem_numericalDivisorGroup
    {φ : Module.Dual ℝ (NumericalCurveClasses sX)} (hφ : φ ∈ numericalDivisorGroup sX)
    (C : ProperCurve sX) : ∃ n : ℤ, φ (OneCycle.numericalClass sX (C.cycle ℝ)) = n := by
  induction hφ using AddSubgroup.closure_induction with
  | mem φ h =>
    obtain ⟨L, hL, rfl⟩ := h
    exact ⟨C.degree k L, by
      rw [NumericalCurveClasses.degree_numericalClass, OneCycle.degree_cycle]⟩
  | zero => exact ⟨0, by simp⟩
  | add φ ψ _ _ hφ hψ =>
    obtain ⟨n, hn⟩ := hφ
    obtain ⟨m, hm⟩ := hψ
    exact ⟨n + m, by simp [hn, hm]⟩
  | neg φ _ hφ =>
    obtain ⟨n, hn⟩ := hφ
    exact ⟨-n, by simp [hn]⟩

/-- `Num(X)` spans `N₁(X)^*` over `ℝ` when `N₁(X)` is finite dimensional. -/
private theorem span_numericalDivisorGroup_eq_top
    [FiniteDimensional ℝ (NumericalCurveClasses sX)] :
    span ℝ (numericalDivisorGroup sX : Set (Dual ℝ (NumericalCurveClasses sX))) = ⊤ := by
  set W := span ℝ (numericalDivisorGroup sX : Set (Dual ℝ (NumericalCurveClasses sX)))
  have hW : W.dualCoannihilator = ⊥ := by
    refine eq_bot_iff.mpr fun z hz => ?_
    obtain ⟨Z, rfl⟩ := OneCycle.numericalClass_surjective sX z
    rw [Submodule.mem_bot, OneCycle.numericalClass, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, OneCycle.mem_numericallyTrivial]
    intro L _
    rw [← NumericalCurveClasses.degree_numericalClass]
    exact (Submodule.mem_dualCoannihilator _).mp hz _
      (subset_span (AddSubgroup.subset_closure ⟨L, inferInstance, rfl⟩))
  rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := W), hW,
    Submodule.dualAnnihilator_bot]

end Helpers

/-- On a proper variety `X` over an algebraically closed field of characteristic zero, the group
`Num(X)` of degree forms of invertible sheaves on `N₁(X)` is a free abelian group of finite rank
`ρ(X)`, and every `ℤ`-basis of `Num(X)` is an `ℝ`-basis of `N₁(X)^*`. -/
@[mmp "lem_mmp_foundation_km3b_numerical_divisor_lattice"]
public theorem numericalDivisorGroup_free_finrank_and_basis
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [IsProperVariety k sX] :
    Module.Free ℤ (numericalDivisorGroup sX) ∧ Module.Finite ℤ (numericalDivisorGroup sX) ∧
      (Module.finrank ℤ (numericalDivisorGroup sX) : ℕ∞) = picardNumber sX ∧
      ∀ {ι : Type*} (b : Module.Basis ι ℤ (numericalDivisorGroup sX)),
        LinearIndependent ℝ (fun i => (b i : Module.Dual ℝ (NumericalCurveClasses sX))) ∧
          Submodule.span ℝ
              (Set.range fun i => (b i : Module.Dual ℝ (NumericalCurveClasses sX))) = ⊤ := by
  have := NumericalCurveClasses.finiteDimensional_of_isProperVariety sX
  obtain ⟨h1, h2, h3, h4⟩ := free_finite_finrank_eq_and_basis_of_span_dual _
    (span_range_numericalClass_cycle_eq_top sX) (numericalDivisorGroup sX)
    (fun _ hφ => Set.forall_mem_range.2 (exists_int_of_mem_numericalDivisorGroup sX hφ))
    (span_numericalDivisorGroup_eq_top sX)
  refine ⟨h1, h2, ?_, h4⟩
  rw [h3, picardNumber, ← Module.finrank_eq_rank, Cardinal.toENat_nat]

end MMP.Mori
