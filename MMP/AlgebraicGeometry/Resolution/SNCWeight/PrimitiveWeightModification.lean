module

public import MMP.AlgebraicGeometry.Resolution.SNCWeight.FinalModel

/-!
# A snc modification adapted to a primitive positive weight

Let `W` be a smooth variety over a field `k` of characteristic zero, `T = ∑ⱼ Tⱼ` a reduced
simple normal crossing divisor on `W`, `J` a nonempty set of components of `T` and `Z_J` an
irreducible component of `⋂_{j ∈ J} Tⱼ`, with generic point `η`, and `α ∈ ℤ_{>0}^J` a primitive
vector. There are an affine open neighbourhood `W°` of `η` meeting only the components `Tⱼ`,
`j ∈ J`, and a birational morphism `g : W' ⟶ W°` from a smooth variety, projective in the sense
of a closed immersion into some `ℙᴺ_{W°}`, which is a finite composite of blow-ups, each along the
(possibly disconnected) intersection of two components of the current reduced total boundary.
Its reduced total boundary `T'` is snc and log crepant, `K_{W'} + T' = g^*(K_{W°} + T|_{W°})`.
It has a component `E_α` whose valuation is monomial of weight `α` at `Z_J`, and every normalized
divisorial valuation centred at `Z_J` whose orders along the `Tⱼ` form a positive multiple of
`α` has its centre on `W'` inside `E_α` and in no other component of `T'`.

## Main results

* `MMP.Fourfold.exists_snc_modification_primitive_weight`.

## Implementation notes

* "Projective" is projectivity in the sense of Hartshorne
  (`AlgebraicGeometry.IsProjectiveMorphism`), a closed immersion into some `ℙᴺ_{W°}` over `W°`.
  This is why the neighbourhood `W°` is asserted to exist and to be affine rather than given:
  over an affine base each blow-up in the tower is cut out of a projective space by a Segre
  embedding, while over an arbitrary open subset of `W` the composite is only projective in the
  sense of EGA.
* The factorization of `g` into blow-ups is a blow-up sequence
  `MMP.Resolution.ClosedBlowupSequence` starting with `W°`, whose last scheme is `W'` and whose
  composite `toBase` is `g`. Its `i`-th centre, on the scheme `Yᵢ` over `W°` by `πᵢ`, is the
  intersection `D ∩ D'`, with its reduced structure (the vanishing ideal of its support), of two
  distinct irreducible components `D ≠ D'` of the reduced total boundary
  `πᵢ⁻¹(⋃_{j ∈ J} Tⱼ) ∪ Ex(πᵢ)` (`MMP.Fourfold.SNCWeight.BlowupTower.IsBoundaryStratumSequence`).
  The intersection is taken whole, so it may be disconnected.
* "Reduced total boundary" `T'` of `g` is a reduced divisor whose support is
  `g⁻¹(⋃_{j ∈ J} Tⱼ) ∪ Ex(g)`; this is stated as the two clauses `Supp T' = g⁻¹(⋃_{j ∈ J} Tⱼ)`
  and `Ex(g) ⊆ Supp T'`.
* The log crepancy `K_{W'} + T' = g^*(K_{W°} + T|_{W°})` is `MMP.Mori.IsCrepantBoundary` for the
  pair `(W°, T|_{W°})`, `T|_{W°}` the restriction along the open immersion
  (`MMP.Mori.inverseTransformDivisor`), for some canonical divisor of `W°`.
* Valuations of `k(W')` are compared with those of `k(W)` along the field map of `g ≫ ι`. The
  order of `ξ` along `Tⱼ` is its value on a local equation `zⱼ ∈ 𝒪_{W,η}` of `Tⱼ`.
* "Outside the other components" means that the centre `C'` is contained in no component of `T'`
  other than `E_α`, i.e. its generic point lies on `E_α` only.
* The modification is built in `MMP.Fourfold.SNCWeight` by the subtraction algorithm on `α`:
  while two boundary components through the tracked centre have positive weights `a ≤ b`, blow
  up the codimension-two stratum where they meet; the exceptional divisor gets weight `a` and the
  second component weight `b - a`. The sum of the weights drops and their gcd is unchanged, so the
  algorithm stops at a single component `E_α` of weight `1`, as `α` is primitive. Each chart
  computation is replaced by the valuative data it determines.
* `W°` is chosen so small that every intersection of some of the `Tⱼ` meets it in a connected
  set; this persists through the blow-ups for the intersections of the components with positive
  weight, so each blown-up stratum is the whole intersection of the two components.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped WithZero

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Fourfold

open MMP.Mori

variable {k : Type u} [Field k] {W : Scheme.{u}} (sW : W ⟶ Spec (.of k))
  [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]

/-- **A snc modification adapted to a primitive positive weight.** Let `W` be a smooth variety
over a field `k` of characteristic zero, `T` a reduced snc divisor, `J ⊆ Supp T` nonempty and `Z`
an irreducible component of `⋂_{j ∈ J} Tⱼ` with generic point `η`, and `α ∈ ℤ_{>0}^J` primitive.
Then there are an affine open `U ∋ η` meeting only the components `Tⱼ` with `j ∈ J`, a smooth
variety `W'`, a birational morphism `g : W' ⟶ U`, projective in the sense of a closed immersion
into some `ℙᴺ_U`, which is the composite of a blow-up sequence each of whose centres is the
intersection of two distinct components of the current reduced total boundary
(`MMP.Fourfold.SNCWeight.BlowupTower.IsBoundaryStratumSequence`), and a reduced snc divisor `T'`
on `W'`, the reduced total boundary of `g` (support `g⁻¹(⋃_{j ∈ J} Tⱼ)`, containing the
exceptional set of `g`), with
`K_{W'} + T' = g^*(K_U + T|_U)`, with a component `E` of `T'` such that `ord_E` is monomial of
weight `α` at `Z` (`MMP.Fourfold.IsMonomialValuationOfWeight`), and such that every normalized
divisorial valuation `ξ` of `k(W)` with centre `Z` and orders `ξ(Tⱼ) = d αⱼ`, `d > 0`, has
centre `C'` on `W'` with `C' ⊆ E` and `C' ⊄ F` for every other component `F` of `T'`. -/
@[mmp "thm_mmp_snc_primitive_weight_modification"]
public theorem exists_snc_modification_primitive_weight [CharZero k]
    (hW : MMP.Mori.IsVariety k sW) (hWs : IsSmoothScheme sW) (T : Divisor W)
    (hT : MMP.Intersection.IsReducedEffective T) (hTs : T.IsSNC sW)
    (J : Finset (MMP.Mori.PrimeDivisor W)) (hJ : J.Nonempty) (hJT : J ⊆ T.support)
    (Z : IrreducibleCloseds W)
    (hZ : Maximal (fun S : Set W => IsIrreducible S ∧ S ⊆ ⋂ E ∈ J, E.support) (Z : Set W))
    (α : J → ℕ) (hα : ∀ j, 0 < α j) (hαp : ∀ d : ℕ, (∀ j, d ∣ α j) → d = 1) :
    ∃ (U : W.Opens) (hηU : Z.isIrreducible.genericPoint ∈ U), IsAffineOpen U ∧
      (∀ E ∈ T.support, (E.support ∩ U).Nonempty → E ∈ J) ∧
    haveI : Nonempty U := ⟨⟨_, hηU⟩⟩
    ∃ (W' : Scheme.{u}) (_ : IsIntegral W') (_ : IsLocallyNoetherian W') (_ : IsNormal W')
      (g : W' ⟶ U) (hg : IsBirationalMorphism g) (_ : IsDominant (g ≫ U.ι))
      (hW' : IsNormalVariety k (g ≫ U.ι ≫ sW)) (T' : Divisor W'),
      IsProjectiveMorphism g ∧
      (∃ (B : MMP.Resolution.ClosedBlowupSequence U) (h : W' = B.target),
        eqToHom h ≫ B.toBase = g ∧
        SNCWeight.BlowupTower.IsBoundaryStratumSequence
          (U.ι.base ⁻¹' ⋃ E ∈ J, (E.support : Set W)) (𝟙 U.toScheme) B) ∧
      IsSmoothScheme (g ≫ U.ι ≫ sW) ∧
      MMP.Intersection.IsReducedEffective T' ∧ T'.IsSNC (g ≫ U.ι ≫ sW) ∧
      (⋃ F ∈ T'.support, (F.support : Set W')) =
        (g ≫ U.ι).base ⁻¹' (⋃ E ∈ J, (E.support : Set W)) ∧
      (exceptionalSet g : Set W') ⊆ ⋃ F ∈ T'.support, (F.support : Set W') ∧
      (∃ (n : ℕ) (K : Divisor U), K.IsCanonicalDivisor (U.ι ≫ sW) n ∧
        IsCrepantBoundary (U.ι ≫ sW) n K
          (Divisor.toQDivisor (inverseTransformDivisor U.ι T)) g hW' hg
          (Divisor.toQDivisor T')) ∧
      ∃ E ∈ T'.support,
        (∀ z : J → W.presheaf.stalk Z.isIrreducible.genericPoint,
          (∀ j : J, IdealSheafData.stalk j.1.idealSheaf Z.isIrreducible.genericPoint =
            Ideal.span {z j}) →
          IsMonomialValuationOfWeight sW T J Z z α
            (E.divisorialValuation.comap (functionFieldMap (g ≫ U.ι)))) ∧
        ∀ (ξ : Valuation W.functionField ℤᵐ⁰) (d : ℕ)
          (z : J → W.presheaf.stalk Z.isIrreducible.genericPoint),
          (∀ j : J, IdealSheafData.stalk j.1.idealSheaf Z.isIrreducible.genericPoint =
            Ideal.span {z j}) →
          MMP.Intersection.IsCentre k sW ξ Z → 0 < d →
          (∀ j, ξ (algebraMap _ W.functionField (z j)) = WithZero.exp (-((d * α j : ℕ) : ℤ))) →
          ∃ (ξ' : Valuation W'.functionField ℤᵐ⁰) (C' : IrreducibleCloseds W'),
            ξ'.comap (functionFieldMap (g ≫ U.ι)) = ξ ∧
            MMP.Intersection.IsCentre k (g ≫ U.ι ≫ sW) ξ' C' ∧
            (C' : Set W') ⊆ E.support ∧
            ∀ F ∈ T'.support, F ≠ E → ¬ (C' : Set W') ⊆ F.support := by
  obtain ⟨U, hηU, hUa, hU, hUc⟩ := SNCWeight.exists_isAffineOpen_nbhd hW hTs hJT hZ
  exact ⟨U, hηU, hUa, hU, SNCWeight.Restriction.exists_crepant_sncModel_monomialValuation sW hW hWs
    T hT hTs J hJ hJT Z hZ U hηU hU hUa hUc α hα hαp⟩

end MMP.Fourfold
