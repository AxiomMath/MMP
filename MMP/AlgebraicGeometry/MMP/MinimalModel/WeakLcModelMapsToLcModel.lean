module
public import MMP.AlgebraicGeometry.MMP.MinimalModel.WeakLcModelComparison
public import MMP.AlgebraicGeometry.MMP.MinimalModel.WeakLcModelLcModelMorphism

/-!
# A weak log canonical model maps to the log canonical model

Let `g : (Y, D_Y) ⟶ Z` be a weak log canonical model and `g^c : (Y^c, D^c) ⟶ Z` a log canonical
model of the same `f : (X, D_X) ⟶ Z`, through the rational maps `φ : X ⤏ Y` and `φ^c : X ⤏ Y^c`,
everything a variety over a field of characteristic zero. Then the birational map
`ρ = φ^c ∘ φ⁻¹ : Y ⤏ Y^c` is a morphism, and it is a morphism over `Z`: `g = ρ ≫ g^c`. It is the
unique morphism whose rational map is `ρ`, since `Y^c` is separated.

## Main results

* `MMP.Flips.IsWeakLogCanonicalModelOf.existsUnique_toRationalMap_eq_of_isLogCanonicalModelOf`.

## Implementation notes

The birational map `ρ = φ^c ∘ φ⁻¹` is described through isomorphisms of dense opens: if
`e : X.PartialIso Y` and `e^c : X.PartialIso Y^c` represent `φ` and `φ^c`, then `ρ` is the rational
map of `e.symm.trans e^c`; this does not depend on the representatives. The uniqueness asserted is
that of a morphism with rational map `ρ`; a morphism `h` with `h ≫ g^c = g` alone is not unique in
general (an automorphism of a curve of genus at least two over a point).

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 2.22.2
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace MMP.Flips

open MMP.Mori

/-- Two morphisms from a reduced scheme to a separated scheme with the same rational map are
equal. -/
private lemma eq_of_toRationalMap_eq {Y W : Scheme.{u}} [IsReduced Y] [W.IsSeparated]
    {h₁ h₂ : Y ⟶ W} (e : h₁.toRationalMap = h₂.toRationalMap) : h₁ = h₂ := by
  have := (Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ _)).mp
    (Scheme.PartialMap.toRationalMap_eq_iff.mp e)
  simp only [Scheme.Hom.toPartialMap] at this
  rw [← Scheme.topIso_hom] at this
  exact (cancel_epi _).mp this

/-- A scheme separated over a field is separated. -/
private lemma isSeparated_of_isVariety {k : Type u} [Field k] {W : Scheme.{u}}
    {s : W ⟶ Spec (.of k)} (hW : Mori.IsVariety k s) : W.IsSeparated := by
  haveI := hW.toIsSeparated
  constructor
  rw [← terminal.comp_from s]
  infer_instance

/-- **FA 2.22.2.** Over a field of characteristic zero, let `g : (Y, D_Y) ⟶ Z` be a weak log
canonical model (`MMP.Flips.IsWeakLogCanonicalModelOf`) and `gc : (Yc, Dc) ⟶ Z` a log canonical
model (`MMP.Flips.IsLogCanonicalModelOf`) of `f : (X, D_X) ⟶ Z`, through `φ : X ⤏ Y` and
`φc : X ⤏ Yc`, where `X`, `Y`, `Yc`, `Z` are varieties and `f`, `g`, `gc` morphisms over `k`. Let
`ρ : Y ⤏ Yc` be `φc ∘ φ⁻¹`, the rational map of `e.symm.trans ec` for partial isomorphisms `e`,
`ec` representing `φ`, `φc`. Then `ρ` is the rational map of a unique morphism `h : Y ⟶ Yc`, and
`h ≫ gc = g`. -/
@[mmp "thm_fa2_weak_lc_model_maps_to_lc_model"]
public theorem IsWeakLogCanonicalModelOf.existsUnique_toRationalMap_eq_of_isLogCanonicalModelOf
    {k : Type u} [Field k] [CharZero k] {X Y Yc Z : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} {sYc : Yc ⟶ Spec (.of k)}
    {sZ : Z ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    [QuasiCompact sX]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [LocallyOfFiniteType sY]
    [QuasiCompact sY]
    [IsIntegral Yc] [IsLocallyNoetherian Yc] [IsNormal Yc] [CompactSpace Yc]
    [LocallyOfFiniteType sYc] [QuasiCompact sYc]
    (hX : Mori.IsVariety k sX) (hY : Mori.IsVariety k sY) (hYc : Mori.IsVariety k sYc)
    (hZ : Mori.IsVariety k sZ)
    {f : X ⟶ Z} {g : Y ⟶ Z} {gc : Yc ⟶ Z} (hfZ : f ≫ sZ = sX) (hgZ : g ≫ sZ = sY)
    (hgcZ : gc ≫ sZ = sYc)
    {n : ℕ} {K_X : Divisor X} {D_X : RDivisor X} {K_Y : Divisor Y} {K_Yc : Divisor Yc}
    {φ : X.RationalMap Y} {φc : X.RationalMap Yc}
    {c : Mori.PrimeDivisor Y → ℝ} {cc : Mori.PrimeDivisor Yc → ℝ}
    {D_Y : RDivisor Y} {Dc : RDivisor Yc}
    (hg : IsWeakLogCanonicalModelOf sY sX n K_X D_X K_Y f g φ c D_Y)
    (hc : IsLogCanonicalModelOf sYc sX n K_X D_X K_Yc f gc φc cc Dc)
    {ρ : Y.RationalMap Yc}
    (hρ : ∃ (e : X.PartialIso Y) (ec : X.PartialIso Yc), e.toRationalMap = φ ∧
      ec.toRationalMap = φc ∧ (e.symm.trans ec).toRationalMap = ρ) :
    ∃! h : Y ⟶ Yc, h.toRationalMap = ρ ∧ h ≫ gc = g := by
  obtain ⟨c', hw⟩ := IsWeakLogCanonicalModelOf.exists_isWeakLogCanonicalModelOf_trans
    hX hY hYc hZ hfZ hgZ hgcZ hg hc.1 hρ
  obtain ⟨h, hh⟩ :=
    IsLogCanonicalModelOf.exists_toRationalMap_eq_of_isRelativeWeakLogCanonicalModel
      hY hYc hZ hgZ hgcZ hg.2.2.2.2.2.1
      (⟨hw, hc.2⟩ : IsLogCanonicalModelOf sYc sY n K_Y D_Y K_Yc g gc ρ c' Dc)
  haveI := isSeparated_of_isVariety hYc
  haveI := isSeparated_of_isVariety hZ
  refine ⟨h, ⟨hh, eq_of_toRationalMap_eq ?_⟩,
    fun h' ⟨hh', _⟩ => eq_of_toRationalMap_eq (hh'.trans hh.symm)⟩
  have hover := hw.2.2.1.2
  rwa [RationalMap.IsOver, ← hh] at hover

end MMP.Flips
