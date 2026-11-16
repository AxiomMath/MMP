module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.LogResolution.Basic
public import MMP.AlgebraicGeometry.Divisor.EffectiveCartierDivisor
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.FirstChernClassSurjective
public import StacksFrontier.AlgebraicGeometry.Properties.Regular
public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization
public import StacksFrontier.RingTheory.RegularLocalRing.UniqueFactorization

/-!
# Regular local rings are factorial; Weil divisors on regular schemes are Cartier

A regular local ring is a unique factorization domain (Stacks 0AG0, `IsRegularLocalRing.isDomain`
and `IsRegularLocalRing.uniqueFactorizationMonoid`). Consequently every Weil divisor on a regular
integral scheme is the Weil divisor of a Cartier divisor.

## Implementation notes

* A *regular* scheme is the Stacks project's `AlgebraicGeometry.IsRegular` (Tag 02IS): every point
  has an affine open neighbourhood whose ring of sections is a regular, in particular Noetherian,
  ring. So a regular scheme is locally Noetherian; no quasi-compactness is needed, since a Weil
  divisor is a finite combination of prime divisors.
* A Weil divisor is an element of `MMP.Mori.Divisor X`, the free abelian group on the prime
  divisors of `X`. "`w` is Cartier" is read as: `w` is the Weil divisor `[A] = ∑ ord_P(A) P` of
  some Cartier divisor `A` (`MMP.Intersection.IsWeilDivisorOfCartier`).
-/

@[expose] public section

universe u

open AlgebraicGeometry

namespace MMP.Resolution.Bridges

open MMP.Mori (Divisor)

open MMP.Intersection CategoryTheory

/-- If `D₁`, `D₂` have local equations `s₁`, `s₂` in `𝒪_X` near the generic point of `V`, whose
quotients of the stalk there have lengths `n₁`, `n₂`, then `D₁ - D₂` has order `n₁ - n₂` along
`V`. -/
theorem isOrderAlong_sub_of_localEquations {X : Scheme.{u}} {D₁ D₂ : X.CartierDivisor}
    {U₁ U₂ : X.Opens} {V : Scheme.Subvariety X} (h₁ : V.genericPoint ∈ U₁)
    (h₂ : V.genericPoint ∈ U₂) {s₁ : Γ(X, U₁)} {s₂ : Γ(X, U₂)}
    (hs₁ : IsUnit (toTotalQuotient U₁ s₁)) (hs₂ : IsUnit (toTotalQuotient U₂ s₂))
    (e₁ : IsLocalEquationOn D₁ U₁ hs₁.unit) (e₂ : IsLocalEquationOn D₂ U₂ hs₂.unit)
    {n₁ n₂ : ℕ}
    (l₁ : Module.length (X.presheaf.stalk V.genericPoint)
      (X.presheaf.stalk V.genericPoint ⧸
        Ideal.span {X.presheaf.germ U₁ V.genericPoint h₁ s₁}) = n₁)
    (l₂ : Module.length (X.presheaf.stalk V.genericPoint)
      (X.presheaf.stalk V.genericPoint ⧸
        Ideal.span {X.presheaf.germ U₂ V.genericPoint h₂ s₂}) = n₂) :
    IsOrderAlong (D₁ - D₂) V ((n₁ : ℤ) - n₂) := by
  set x := V.genericPoint
  have u₁ : IsUnit (stalkToTotalQuotient x (X.presheaf.germ U₁ x h₁ s₁)) := by
    rw [← germ_toTotalQuotient]; exact hs₁.map _
  have u₂ : IsUnit (stalkToTotalQuotient x (X.presheaf.germ U₂ x h₂ s₂)) := by
    rw [← germ_toTotalQuotient]; exact hs₂.map _
  have hxW : x ∈ U₁ ⊓ U₂ := ⟨h₁, h₂⟩
  refine ⟨_, _, mem_nonZeroDivisors_of_isUnit_stalkToTotalQuotient u₁,
    mem_nonZeroDivisors_of_isUnit_stalkToTotalQuotient u₂,
    ⟨X.totalQuotientSheaf.presheaf.germ (U₁ ⊓ U₂) x hxW
      ((resUnits inf_le_left hs₁.unit * (resUnits inf_le_right hs₂.unit)⁻¹ : _ˣ) : _), ?_, ?_⟩,
    n₁, n₂, l₁, l₂, rfl⟩
  · refine ⟨U₁ ⊓ U₂, hxW, _, ?_, rfl⟩
    rw [sub_eq_add_neg]
    exact (e₁.res inf_le_left).mul (e₂.res inf_le_right).inv
  · refine ⟨u₂, ?_⟩
    have c₁ : stalkToTotalQuotient x (X.presheaf.germ U₁ x h₁ s₁) =
        X.totalQuotientSheaf.presheaf.germ (U₁ ⊓ U₂) x hxW
          ((resUnits (inf_le_left : U₁ ⊓ U₂ ≤ U₁) hs₁.unit : _ˣ) : _) := by
      rw [← germ_toTotalQuotient]
      exact (TopCat.Presheaf.germ_res_apply X.totalQuotientSheaf.presheaf
        (homOfLE inf_le_left) x hxW (toTotalQuotient U₁ s₁)).symm
    have c₂ : stalkToTotalQuotient x (X.presheaf.germ U₂ x h₂ s₂) =
        X.totalQuotientSheaf.presheaf.germ (U₁ ⊓ U₂) x hxW
          ((resUnits (inf_le_right : U₁ ⊓ U₂ ≤ U₂) hs₂.unit : _ˣ) : _) := by
      rw [← germ_toTotalQuotient]
      exact (TopCat.Presheaf.germ_res_apply X.totalQuotientSheaf.presheaf
        (homOfLE inf_le_right) x hxW (toTotalQuotient U₂ s₂)).symm
    rw [c₁, c₂, ← map_mul, Units.val_mul, mul_left_comm, Units.mul_inv, mul_one]

/-- An effective Cartier divisor has, at every point, a local equation in `𝒪_X` generating the
stalk of its closed subscheme. -/
theorem exists_localEquation_stalk_subscheme {X : Scheme.{u}}
    {D : X.CartierDivisor} (hD : IsEffective D) (x : X) :
    ∃ (U : X.Opens) (hx : x ∈ U) (s : Γ(X, U)) (hs : IsUnit (toTotalQuotient U s)),
      IsLocalEquationOn D U hs.unit ∧
        AlgebraicGeometry.IdealSheafData.stalk (MMP.CartierDivisor.subscheme D hD) x =
          Ideal.span {X.presheaf.germ U x hx s} := by
  obtain ⟨U, ⟨g, hu, hg'⟩, hxU⟩ := MMP.CartierDivisor.exists_affineOpens_isEffectiveOn hD x
  refine ⟨U, hxU, g, hu, hg', ?_⟩
  rw [IdealSheafData.stalk_eq_map_germ _ x U hxU,
    MMP.CartierDivisor.ideal_subscheme_affine hD ⟨hu, hg'⟩, Ideal.map_span,
    Set.image_singleton]

/-- A Weil divisor on a locally Noetherian integral scheme with factorial local rings is the
Weil divisor of a Cartier divisor. -/
theorem exists_isOrderAlong_of_weilDivisor {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (hX : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) (w : WeilDivisor X) :
    ∃ A : X.CartierDivisor, ∀ P : PrimeDivisor X,
      IsOrderAlong A (primeDivisorSubvariety P) (w.val P) := by
  obtain ⟨D₁, hD₁, e₁⟩ := (MMP.CartierDivisor.isEffectiveCartierDivisor_iff_exists_subscheme_eq
    _).mp (positiveWeilIdeal_isEffectiveCartierDivisor hX w)
  obtain ⟨D₂, hD₂, e₂⟩ := (MMP.CartierDivisor.isEffectiveCartierDivisor_iff_exists_subscheme_eq
    _).mp (positiveWeilIdeal_isEffectiveCartierDivisor hX (-w))
  refine ⟨D₁ - D₂, fun P => ?_⟩
  obtain ⟨U₁, h₁, s₁, hs₁, l₁, st₁⟩ := exists_localEquation_stalk_subscheme hD₁ P.genericPoint
  obtain ⟨U₂, h₂, s₂, hs₂, l₂, st₂⟩ := exists_localEquation_stalk_subscheme hD₂ P.genericPoint
  rw [e₁, positiveWeilIdeal_stalk_genericPoint] at st₁
  rw [e₂, positiveWeilIdeal_stalk_genericPoint] at st₂
  haveI : IsNormal X :=
    { stalk_isDomain := fun _ => inferInstance
      stalk_normal := fun x => by haveI := hX x; infer_instance }
  haveI : IsDiscreteValuationRing (X.presheaf.stalk P.genericPoint) :=
    Stacks.AlgebraicGeometry.UnitsNormalProper.isDiscreteValuationRing_stalk
      (PrimeDivisor.coheight_genericPoint P)
  have len₁ := IsDiscreteValuationRing.length_quotient_pow_maximalIdeal
    (R := X.presheaf.stalk P.genericPoint) (w.val P).toNat
  have len₂ := IsDiscreteValuationRing.length_quotient_pow_maximalIdeal
    (R := X.presheaf.stalk P.genericPoint) ((-w).val P).toNat
  rw [st₁] at len₁
  rw [st₂] at len₂
  have := isOrderAlong_sub_of_localEquations (V := primeDivisorSubvariety P) h₁ h₂ hs₁ hs₂
    l₁ l₂ len₁ len₂
  convert this using 1
  have : (-w).val P = - w.val P := rfl
  omega

/-- **Regular local rings and Cartier Weil divisors.** A regular local ring is a unique
factorization domain. Consequently, on a regular integral scheme `X` every Weil divisor
`w` is Cartier: it is the Weil divisor `[A]` of some Cartier divisor `A` on `X`. (Regularity in
the sense of Stacks 02IS already makes `X` locally Noetherian, which is all that is used.) -/
@[mmp "lem_mmp_foundation_regular_local_factorial"]
theorem uniqueFactorization_and_exists_isWeilDivisorOfCartier :
    (∀ (R : Type u) [CommRing R] [IsRegularLocalRing R],
        IsDomain R ∧ UniqueFactorizationMonoid R) ∧
      ∀ (X : Scheme.{u}) [IsIntegral X], IsRegular X →
        ∀ w : Divisor X, ∃ A : X.CartierDivisor, IsWeilDivisorOfCartier A w :=
  ⟨fun R _ _ => ⟨IsRegularLocalRing.isDomain R, IsRegularLocalRing.uniqueFactorizationMonoid R⟩,
    fun X _ hX w => by
      obtain ⟨_, _⟩ := ((isRegular_tfae X).out 1 2 rfl rfl).mp hX
      exact exists_isOrderAlong_of_weilDivisor
        (fun x => IsRegularLocalRing.uniqueFactorizationMonoid (X.presheaf.stalk x))
        (⟨w, (mem_weilDivisor_iff _).mpr fun _ =>
          ⟨Set.univ, Filter.univ_mem, w.support.finite_toSet.subset fun Z hZ => by
            by_cases h : w Z = 0
            · simp [h] at hZ
            · simpa using h⟩⟩ : WeilDivisor X)⟩

end MMP.Resolution.Bridges
