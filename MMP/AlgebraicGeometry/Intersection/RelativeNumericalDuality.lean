module

public import MMP.AlgebraicGeometry.Intersection.CurveClassesFiniteDim
public import MMP.AlgebraicGeometry.MMP.Fourfold.Positivity
public import MMP.AlgebraicGeometry.Intersection.PairingSeparation

/-!
# Numerical duality for a proper morphism of varieties in characteristic zero

Let `k` be an algebraically closed field of characteristic zero and `f : X ⟶ S` a proper
morphism of `k`-varieties. The relative curve space `N₁(X/S)`, real 1-cycles supported on curves
contracted by `f` modulo those of degree zero against every Cartier divisor, is
finite-dimensional, and every linear form on it is `z ↦ (z · D)` for some `ℝ`-Cartier divisor
`D` on `X`. Consequently the pairing identifies `N¹(X/S)`, the `ℝ`-Cartier divisors modulo those
of degree zero on every contracted curve, with the full dual of `N₁(X/S)`; in particular
`N¹(X/S)` is finite-dimensional and spanned by the classes of Cartier divisors. The source `X`
need not be proper over `k`.

## Main results

* `MMP.Mori.RelativeNumericalCurveClasses.exists_linearEquiv_dual_of_isProper`

## Implementation notes

`N₁(X/S)` is `MMP.Mori.RelativeNumericalCurveClasses`, its pairing with `ℝ`-Cartier divisors is
`MMP.Mori.RelativeNumericalCurveClasses.intersectionNumber`, and `N¹(X/S)` is
`MMP.Fourfold.RelativeNumericalDivisorClasses`. The identification of `N¹(X/S)` with the dual is
stated as a linear equivalence sending the class of every `ℝ`-Cartier divisor `D` to the form
`z ↦ (z · D)`, which determines it since every class is the class of a divisor.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 1.16, 2.16
-/

section

/-! ### Injectivity into `N₁(X)` and the divisor pairing -/

open CategoryTheory AlgebraicGeometry MMP.Mori

namespace MMP.Mori.RelativeNumericalCurveClasses

variable {k : Type} [Field k] {X S : Scheme.{0}}

/-- The natural map `N₁(X/S) → N₁(X)` is injective. -/
private theorem relativeToAbsolute_injective (sX : X ⟶ Spec (.of k)) (f : X ⟶ S) :
    Function.Injective (relativeToAbsolute sX f) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro z hz
  obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sX f z
  have hz' : OneCycle.numericalClass sX (Z : OneCycle ℝ sX) = 0 := LinearMap.mem_ker.mp hz
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    (mem_relativeNumericallyTrivial.mpr ((Submodule.Quotient.mk_eq_zero _).mp hz'))

/-- The pairing `D ↦ (z ↦ (z · D))` of `ℝ`-Cartier divisors with `N₁(X/S)`, linear in `D`. -/
private noncomputable def pairing (sX : X ⟶ Spec (.of k)) (f : X ⟶ S) :
    KCartierDivisor ℝ X →ₗ[ℝ] Module.Dual ℝ (RelativeNumericalCurveClasses sX f) where
  toFun D := RelativeNumericalCurveClasses.intersectionNumber D
  map_add' D D' := by
    apply Submodule.linearMap_qext
    ext Z
    simp [RelativeNumericalCurveClasses.intersectionNumber]
  map_smul' c D := by
    apply Submodule.linearMap_qext
    ext Z
    simp [RelativeNumericalCurveClasses.intersectionNumber]

/-- The pairing separates the points of `N₁(X/S)` on an integral scheme. -/
private theorem pairing_flip_injective (sX : X ⟶ Spec (.of k)) (f : X ⟶ S) [IsIntegral X] :
    Function.Injective (pairing sX f).flip := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro z hz
  obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sX f z
  refine (Submodule.Quotient.mk_eq_zero _).mpr (OneCycle.mem_numericallyTrivial.mpr fun L _ => ?_)
  obtain ⟨E, ⟨e⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf L
  have h0 : (Z : OneCycle ℝ sX).intersectionNumber (KCartierDivisor.ofCartier ℝ E) = 0 :=
    LinearMap.congr_fun (LinearMap.mem_ker.mp hz) (KCartierDivisor.ofCartier ℝ E)
  rw [OneCycle.intersectionNumber_ofCartier, OneCycle.cartierDegree] at h0
  rw [← h0, OneCycle.degree, OneCycle.degree]
  congr 2
  funext C
  exact congrArg _ (degreeOn_eq_of_iso k sX C.ι C.dim_le e)

/-- The kernel of the relative degree map on contracted curves equals the kernel of the pairing. -/
private theorem ker_relativeDegreeMap_eq_ker_pairing (sX : X ⟶ Spec (.of k)) (f : X ⟶ S) :
    LinearMap.ker (MMP.Fourfold.relativeDegreeMap sX f) = LinearMap.ker (pairing sX f) := by
  ext D
  simp only [LinearMap.mem_ker]
  refine ⟨fun h => ?_, fun h => funext fun C => LinearMap.congr_fun h (C.1.relativeClass f C.2)⟩
  apply Submodule.linearMap_qext
  ext ⟨Z, hZ⟩
  change OneCycle.intersectionPairing D Z = 0
  rw [relativeOneCycles, Finsupp.supported_eq_span_single] at hZ
  induction hZ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨C, hC, rfl⟩ := hx
    exact congrFun h ⟨C, hC⟩
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul a x _ hx => simp [hx]

end MMP.Mori.RelativeNumericalCurveClasses

end

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace MMP.Mori

namespace RelativeNumericalCurveClasses

/-- **Relative numerical duality.** Let `k` be algebraically closed of characteristic zero and
`f : X ⟶ S` a proper morphism of `k`-varieties. Then `N₁(X/S)` is finite-dimensional, every
real linear form on it is `z ↦ (z · D)` for an `ℝ`-Cartier divisor `D` on `X`, and
`[D] ↦ (z ↦ (z · D))` is a linear equivalence from `N¹(X/S)`
(`MMP.Fourfold.RelativeNumericalDivisorClasses`) onto the dual of `N₁(X/S)`; hence `N¹(X/S)`
is finite-dimensional and spanned by the classes of Cartier divisors. -/
@[mmp "lem_mmp_foundation_relative_numerical_duality_char_zero"]
theorem exists_linearEquiv_dual_of_isProper {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {X S : Scheme.{0}} (sX : X ⟶ Spec (.of k)) (sS : S ⟶ Spec (.of k))
    [IsVariety k sX] [IsVariety k sS] (f : X ⟶ S) [IsProper f] (_hf : f ≫ sS = sX) :
    FiniteDimensional ℝ (RelativeNumericalCurveClasses sX f) ∧
    (∀ φ : Module.Dual ℝ (RelativeNumericalCurveClasses sX f),
      ∃ D : KCartierDivisor ℝ X, intersectionNumber (sX := sX) (f := f) D = φ) ∧
    (∃ e : MMP.Fourfold.RelativeNumericalDivisorClasses sX f ≃ₗ[ℝ]
        Module.Dual ℝ (RelativeNumericalCurveClasses sX f),
      ∀ D : KCartierDivisor ℝ X,
        e (MMP.Fourfold.relativeNumericalDivisorClass sX f D) =
          intersectionNumber (sX := sX) (f := f) D) ∧
    FiniteDimensional ℝ (MMP.Fourfold.RelativeNumericalDivisorClasses sX f) ∧
    Submodule.span ℝ (Set.range fun E : X.CartierDivisor =>
      MMP.Fourfold.relativeNumericalDivisorClass sX f (KCartierDivisor.ofCartier ℝ E)) = ⊤ := by
  have := MMP.Mori.finiteDimensional_numericalCurveClasses sX
  have : FiniteDimensional ℝ (RelativeNumericalCurveClasses sX f) :=
    FiniteDimensional.of_injective _ (relativeToAbsolute_injective sX f)
  have hsurj : Function.Surjective (pairing sX f) :=
    LinearMap.flip_injective_iff₂.mp (pairing_flip_injective sX f)
  let e : MMP.Fourfold.RelativeNumericalDivisorClasses sX f ≃ₗ[ℝ]
      Module.Dual ℝ (RelativeNumericalCurveClasses sX f) :=
    (Submodule.quotEquivOfEq _ _ (ker_relativeDegreeMap_eq_ker_pairing sX f)).trans
      ((pairing sX f).quotKerEquivOfSurjective hsurj)
  refine ⟨inferInstance, hsurj, ⟨e, fun D => rfl⟩, LinearEquiv.finiteDimensional e.symm, ?_⟩
  have hspan : Submodule.span ℝ
      (Set.range fun E : X.CartierDivisor => KCartierDivisor.ofCartier ℝ E) = ⊤ :=
    Finsupp.basisSingleOne.span_eq
  rw [Set.range_comp' (MMP.Fourfold.relativeNumericalDivisorClass sX f), ← Submodule.map_span,
    hspan, Submodule.map_top, LinearMap.range_eq_top]
  exact Submodule.mkQ_surjective _

end RelativeNumericalCurveClasses

end MMP.Mori

end
