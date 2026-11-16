module

public import MMP.AlgebraicGeometry.MMP.Fourfold.Defs
public import MMP.AlgebraicGeometry.Divisor.InvertibleSheafCartier

/-!
# The intersection pairing separates numerical curve classes

On an integral `k`-scheme `X`, a numerical class `z ∈ N₁(X)_ℝ` with `(D · z) = 0` for every
`ℝ`-Cartier divisor `D` is zero: every invertible sheaf on an integral scheme is `𝒪_X(E)` for a
Cartier divisor `E` (Hartshorne II.6.15), and degrees on curves only depend on the isomorphism
class of the sheaf.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace MMP.Fourfold

open MMP.Mori

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))

/-- **Invertible sheaves on an integral scheme are `𝒪_X(E)`** (Hartshorne II.6.15): every
invertible sheaf `L` on an integral scheme is isomorphic to the sheaf `𝒪_X(E)` of a Cartier
divisor `E`. -/
theorem exists_nonempty_iso_cartierDivisor_sheaf [IsIntegral X] (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    ∃ E : X.CartierDivisor, Nonempty (L ≅ MMP.CartierDivisor.sheaf E) := by
  obtain ⟨E, ⟨e⟩⟩ := MMP.CartierDivisor.exists_nonempty_iso_sheaf L
  exact ⟨E, ⟨e⟩⟩

/-- The pairing separates the points of `N₁(X)_ℝ` on an integral scheme. -/
theorem numericalPairing_flip_injective [IsIntegral X] :
    Function.Injective (numericalPairing sX).flip := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro z hz
  obtain ⟨Z, rfl⟩ := OneCycle.numericalClass_surjective sX z
  refine (Submodule.Quotient.mk_eq_zero _).mpr (OneCycle.mem_numericallyTrivial.mpr fun L _ => ?_)
  obtain ⟨E, ⟨e⟩⟩ := exists_nonempty_iso_cartierDivisor_sheaf L
  have h0 : Z.intersectionNumber (KCartierDivisor.ofCartier ℝ E) = 0 :=
    LinearMap.congr_fun (LinearMap.mem_ker.mp hz)
      (numericalDivisorClass sX (KCartierDivisor.ofCartier ℝ E))
  rw [OneCycle.intersectionNumber_ofCartier, OneCycle.cartierDegree] at h0
  rw [← h0, OneCycle.degree, OneCycle.degree]
  congr 2
  funext C
  exact congrArg _ (degreeOn_eq_of_iso k sX C.ι C.dim_le e)

end MMP.Fourfold
