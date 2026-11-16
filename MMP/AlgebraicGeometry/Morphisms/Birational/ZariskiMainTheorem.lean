module
public import MMP.AlgebraicGeometry.Morphisms.ProjectiveFieldExtension
public import MMP.AlgebraicGeometry.Morphisms.Birational.FiniteFibreLocus

/-!
# Zariski's main theorem for proper birational morphisms to a normal variety

Let `f : Y ⟶ X` be a proper birational morphism of varieties over a field `k`, with `X` normal.
Then `f` is an isomorphism over the open `MMP.Mori.biregularLocus f`, whose complement has
codimension at least two; the canonical map `f.app U : Γ(X, U) ⟶ Γ(Y, f ⁻¹ᵁ U)` is an
isomorphism for every open `U` (that is, `f_* 𝒪_Y = 𝒪_X`); every fibre of `f` is connected;
and `f` is an isomorphism over a neighbourhood of every point with finite fibre.

## Main results

* `MMP.Mori.zariskiMain_of_isProper_of_isBirationalMorphism`

## Implementation notes

The open set of codimension-two complement is taken to be the largest open over which `f` is an
isomorphism, `MMP.Mori.biregularLocus f`, rather than an unspecified open; this is a sharper
form of the existence statement.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KM98]
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace MMP.Mori

/-- **Zariski's main theorem for a proper birational morphism to a normal variety.** Let
`f : Y ⟶ X` be a proper birational morphism of varieties over `k` with `X` normal. Then the
complement of `MMP.Mori.biregularLocus f` has codimension at least two and `f` restricts to an
isomorphism over it, `f.app U` is an isomorphism for every open `U ⊆ X`, every fibre of `f` is
connected, and every point of `X` with finite fibre has an open neighbourhood over which `f`
is an isomorphism. -/
@[mmp "lem_mmp_foundation_km5b_birational_zmt"]
public theorem zariskiMain_of_isProper_of_isBirationalMorphism {k : Type u} [Field k]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (f : Y ⟶ X) (hX : IsVariety k sX)
    (hY : IsVariety k (f ≫ sX)) [IsNormal X] [IsProper f] (hf : IsBirationalMorphism f) :
    2 ≤ closedsCodimension (biregularLocus f).compl ∧ IsIso (f ∣_ biregularLocus f) ∧
      (∀ U : X.Opens, IsIso (f.app U)) ∧ (∀ x : X, _root_.IsConnected (f ⁻¹' {x})) ∧
      ∀ x : X, (f ⁻¹' {x}).Finite → ∃ U : X.Opens, x ∈ U ∧ IsIso (f ∣_ U) := by
  have : IsIntegral Y := hY.toIsIntegral
  have : IsIntegral X := hX.toIsIntegral
  obtain ⟨happ, hconn⟩ := MMP.Resolution.Bridges.isIso_app_and_isConnected_of_isBirationalMorphism
    (f ≫ sX) sX hY ⟨hX, inferInstance⟩ f hf
  obtain ⟨hO, hiso⟩ := (MMP.Resolution.Bridges.isOpen_finiteFibreLocus_and_isIso f
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hf)).1 inferInstance
  exact ⟨two_le_closedsCodimension_compl_biregularLocus sX f (hY := hX) (hX := hY) hf,
    isBiregular_biregularLocus f, happ, hconn, fun x hx ↦ ⟨⟨_, hO⟩, hx, hiso⟩⟩

end MMP.Mori
