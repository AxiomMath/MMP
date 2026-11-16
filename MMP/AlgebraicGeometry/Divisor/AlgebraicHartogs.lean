module

public import MMP.AlgebraicGeometry.Divisor.Pullback
public import MMP.AlgebraicGeometry.Divisor.DivisorialSheaf

/-!
# Algebraic Hartogs on a Noetherian normal scheme

Let `X` be a Noetherian normal scheme, not necessarily connected, with ring of rational functions
`K(X) = ∏_Z 𝒪_{X,η_Z}` (the product over the irreducible components `Z`, each factor the
function field of a component). If a unit `φ` of `K(X)` has nonnegative order `v_D(φ)` along
every prime divisor `D` meeting an open `U`, then the restriction of `φ` to `U` is regular: there
is a section `s ∈ 𝒪_X(U)` whose germ at the generic point of every component meeting `U` is the
corresponding component of `φ`.

## Main results

* `MMP.Mori.exists_germ_eq_of_forall_zero_le_ord`: algebraic Hartogs for units of `K(X)`.

## Implementation notes

The restriction `φ|_U ∈ 𝒦_X(U) = ∏_{η_Z ∈ U} 𝒪_{X,η_Z}` lying in `𝒪_X(U)` is stated componentwise:
for each irreducible component `Z` whose generic point lies in `U`, the germ of `s` at `η_Z` is
`φ_Z`. Since `𝒪_X(U) → 𝒦_X(U)` is injective on a normal scheme, such an `s` is unique.

The proof is the case `D = 0` of `MMP.Mori.Divisor.IsDivisorialSection.exists_eq`, applied to the
components of `φ` at the generic points in `U`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KM98], Notation 0.4
* [Stacks Project, Tag 031T](https://stacks.math.columbia.edu/tag/031T)
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace MMP.Mori

/-- If a unit `φ` of `K(X)` has `v_E(φ) ≥ 0`, then its component on `E` satisfies
`MMP.Mori.PrimeDivisor.OrdGE 0`. -/
private lemma ordGE_zero_of_zero_le_ord {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    {E : PrimeDivisor X} {φ : (RationalFunctions X)ˣ} (h : 0 ≤ E.ord φ) :
    E.OrdGE 0 ((φ : RationalFunctions X) E.component) := by
  obtain ⟨b, hb⟩ := E.exists_toComponent_eq_of_zero_le_ord h
  rcases eq_or_ne b 0 with rfl | hb0
  · exact Or.inl (by rw [← hb, map_zero])
  · exact Or.inr (hb ▸ E.one_le_valuation_toComponent hb0)

/-- **Algebraic Hartogs on a Noetherian normal scheme.** If a unit `φ` of the ring of rational
functions `K(X)` of a Noetherian normal scheme `X` has `v_D(φ) ≥ 0` along every prime divisor `D`
meeting the open `U`, then `φ|_U` is regular on `U`: some `s ∈ 𝒪_X(U)` has germ `φ_Z` at the
generic point of every irreducible component `Z` meeting `U`. -/
@[mmp "lem_mmp_threefold_normal_scheme_hartogs"]
public theorem exists_germ_eq_of_forall_zero_le_ord {X : Scheme.{u}} [IsLocallyNoetherian X]
    [CompactSpace X] [IsNormal X] (U : X.Opens) (φ : (RationalFunctions X)ˣ)
    (h : ∀ D : PrimeDivisor X, (D.support ∩ U).Nonempty → 0 ≤ D.ord φ) :
    ∃ s : Γ(X, U), ∀ (Z : irreducibleComponents X) (hZ : componentGenericPoint X Z ∈ U),
      X.presheaf.germ U (componentGenericPoint X Z) hZ s = (φ : RationalFunctions X) Z := by
  have hφ : (0 : Divisor X).IsDivisorialSection U fun Z => (φ : RationalFunctions X) Z.1 :=
    fun E hE => by simpa using ordGE_zero_of_zero_le_ord (h E hE)
  obtain ⟨s, hs⟩ := hφ.exists_eq
  exact ⟨s, fun Z hZ => congrFun hs ⟨Z, hZ⟩⟩

end MMP.Mori
