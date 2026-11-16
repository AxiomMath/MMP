module

public import MMP.AlgebraicGeometry.Morphisms.Birational.RationalMap
public import MMP.AlgebraicGeometry.Divisor.Basic

/-!
# Birational transforms and exceptional divisors

Let `f : X ⤏ Y` be a rational map and `Z ⊆ X` a closed subset. The *birational transform*
(proper or strict transform) of `Z` is the closed subset
`f_*(Z) = closure (⋃_{(U, f_U)} f_U(Z ∩ U)) ⊆ Y`, the union over all representatives
`(U, f_U)` of `f`, with its reduced structure. For a birational morphism `g : Y ⟶ X`, with `V_g`
the union of the `g`-biregular opens of `X`, the *birational transform of `Z` under `g⁻¹`* is
`g⁻¹_*(Z) = closure (g⁻¹(Z ∩ V_g)) ⊆ Y`.

The same notation is used for divisors: for `D = ∑ dᵢ Dᵢ` with distinct prime divisors `Dᵢ`,
`f_* D = ∑_{i ∈ J} dᵢ f_*(Dᵢ)`, where `J` is the set of `i` such that `f` is defined at the
generic point of `Dᵢ` and `f_*(Dᵢ)` is a prime divisor of `Y`; the other components are
dropped. Likewise `g⁻¹_* D = ∑_{i ∈ J} dᵢ g⁻¹_*(Dᵢ)`, where `J` is the set of `i` with
`Dᵢ ∩ V_g ≠ ∅` and `g⁻¹_*(Dᵢ)` a prime divisor of `Y`.

A prime divisor `E ⊆ X` is *exceptional* for a birational map `φ : X ⤏ X'` if either `φ` is not
defined at the generic point of `E`, or `φ` is defined there and `codim_{X'} φ_*(E) ≥ 2`.

## Main definitions

* `MMP.Mori.RationalMap.transform`: the birational transform `f_*(Z)` of a closed subset, with
  `MMP.Mori.RationalMap.transformIdeal` the ideal sheaf of its reduced structure.
* `MMP.Mori.inverseTransform`: the birational transform `g⁻¹_*(Z)` under the inverse of a
  morphism, with `MMP.Mori.inverseTransformIdeal`.
* `MMP.Mori.RationalMap.transformPrimeDivisor`, `MMP.Mori.inverseTransformPrimeDivisor`: the
  transform of a prime divisor, when it is one.
* `MMP.Mori.RationalMap.transformDivisor`, `MMP.Mori.inverseTransformDivisor`: the transforms
  `f_* D` and `g⁻¹_* D` of divisors with coefficients in any `R`, as additive maps, and their
  linear versions `MMP.Mori.RationalMap.transformDivisorₗ`, `MMP.Mori.inverseTransformDivisorₗ`.
* `MMP.Mori.closedsCodimension`: the codimension of a closed subset.
* `MMP.Mori.RationalMap.IsExceptional`: `φ`-exceptional prime divisors.

## Main results

* `MMP.Mori.RationalMap.transformPrimeDivisor_eq_some_iff`,
  `MMP.Mori.inverseTransformPrimeDivisor_eq_some_iff`: the transform of `D` is the prime
  divisor `E` exactly when `D` is not dropped and `E` is `f_*(D)` with its reduced structure.
* `MMP.Mori.RationalMap.transformDivisor_single`, `MMP.Mori.inverseTransformDivisor_single`:
  the transforms are the linear extensions of the transforms of prime divisors.
* `MMP.Mori.DivisorWithCoeffs.mapPrimeDivisors_nonneg`,
  `MMP.Mori.RationalMap.transformDivisor_nonneg`: transforms of effective divisors are effective.
* `MMP.Mori.closedsCodimension_coe`: for an irreducible closed subset the codimension is the
  usual one.

## Implementation notes

The source assumes that `Z ∩ dom f` is dense in `Z` (respectively that `Z ∩ V_g` is dense in
`Z`), which makes `Z` recoverable from its intersection with the domain; the definitions make
sense, and are given, for every closed subset. Likewise the transforms are defined for arbitrary
rational maps and morphisms of arbitrary schemes, and `IsExceptional` for any rational map; the
source states them for (birational) maps of normal schemes.

A closed subset with its reduced structure is the closed subscheme cut out by its vanishing
ideal, and the transform of a prime divisor `D` is a prime divisor `E` when the ideal sheaf of `E`
is the vanishing ideal of `f_*(D)`; a prime divisor is determined by its ideal sheaf
(`MMP.Mori.PrimeDivisor.ext_idealSheaf`), so `E` is unique.

The codimension of a closed subset `Z` is the infimum of the codimensions of the irreducible
closed subsets contained in `Z`; since codimension is antitone and every irreducible closed
subset lies in an irreducible component, this is the infimum over the irreducible components
of `Z`.

## References

* [J. Kollár and S. Mori, *Birational geometry of algebraic varieties*][KollarMori1998],
  Notation 0.4(11), 3.30, 3.50.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Mori

/-! ### Prime divisors and closed subsets -/

/-- A prime divisor is determined by its ideal sheaf. -/
theorem PrimeDivisor.ext_idealSheaf {X : Scheme.{u}} {D E : PrimeDivisor X}
    (h : D.idealSheaf = E.idealSheaf) : D = E := by
  cases D; cases E; cases h; rfl

/-- The *codimension* of a closed subset `Z` of a topological space: the infimum of the
codimensions of the irreducible closed subsets contained in `Z`, that is, of the irreducible
components of `Z`. -/
def closedsCodimension {T : Type*} [TopologicalSpace T] (Z : Closeds T) : ℕ∞ :=
  ⨅ (W : IrreducibleCloseds T) (_ : (W : Set T) ⊆ (Z : Set T)), codimension W

/-- `n ≤ closedsCodimension Z` if and only if every irreducible closed subset contained in `Z`
has codimension at least `n`. -/
theorem le_closedsCodimension_iff {T : Type*} [TopologicalSpace T] {Z : Closeds T} {n : ℕ∞} :
    n ≤ closedsCodimension Z ↔
      ∀ W : IrreducibleCloseds T, (W : Set T) ⊆ (Z : Set T) → n ≤ codimension W := by
  simp [closedsCodimension]

/-- For an irreducible closed subset, `closedsCodimension` is `codimension`. -/
theorem closedsCodimension_coe {T : Type*} [TopologicalSpace T] (W : IrreducibleCloseds T) :
    closedsCodimension (T := T) ⟨(W : Set T), W.isClosed⟩ = codimension W := by
  refine le_antisymm (iInf₂_le W fun _ h ↦ h) (le_closedsCodimension_iff.mpr fun W' hW' ↦ ?_)
  exact Order.coheight_anti (show W' ≤ W from hW')

/-! ### Birational transforms of closed subsets -/

variable {X Y : Scheme.{u}}

namespace RationalMap

/-- The *birational transform* (proper or strict transform) `f_*(Z)` of a closed subset `Z ⊆ X`
under a rational map `f : X ⤏ Y`: the closure of the union, over all representatives
`(U, f_U)` of `f`, of the images `f_U(Z ∩ U)`. -/
@[mmp "def_km0_birational_transform"]
def transform (f : RationalMap X Y) (Z : Closeds X) : Closeds Y :=
  Closeds.closure
    (⋃ g : {g : X.PartialMap Y // g.toRationalMap = f}, g.1.hom '' (g.1.domain.ι ⁻¹' Z))

/-- The ideal sheaf of the reduced structure on the birational transform `f_*(Z)`. -/
@[mmp "def_km0_birational_transform"]
def transformIdeal (f : RationalMap X Y) (Z : Closeds X) : Y.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (f.transform Z)

/-- For every representative `g` of `f`, the image `g(Z ∩ dom g)` is contained in `f_*(Z)`. -/
theorem image_subset_transform {f : RationalMap X Y} (g : X.PartialMap Y)
    (hg : g.toRationalMap = f) (Z : Closeds X) :
    g.hom '' (g.domain.ι ⁻¹' Z) ⊆ f.transform Z :=
  (Set.subset_iUnion (fun g : {g : X.PartialMap Y // g.toRationalMap = f} ↦
    g.1.hom '' (g.1.domain.ι ⁻¹' Z)) ⟨g, hg⟩).trans subset_closure

/-- `f_*(Z)` is contained in a closed subset `W` if and only if `g(Z ∩ dom g) ⊆ W` for every
representative `g` of `f`. -/
theorem transform_le_iff {f : RationalMap X Y} {Z : Closeds X} {W : Closeds Y} :
    f.transform Z ≤ W ↔
      ∀ g : X.PartialMap Y, g.toRationalMap = f → g.hom '' (g.domain.ι ⁻¹' Z) ⊆ W :=
  ⟨fun h g hg ↦ (image_subset_transform g hg Z).trans h,
    fun h ↦ W.isClosed.closure_subset_iff.mpr (Set.iUnion_subset fun g ↦ h g.1 g.2)⟩

/-- The birational transform of closed subsets is monotone. -/
theorem transform_mono (f : RationalMap X Y) : Monotone f.transform := fun _ _ hZ ↦
  transform_le_iff.mpr fun g hg ↦ (Set.image_mono (Set.preimage_mono hZ)).trans
    (image_subset_transform g hg _)

/-- The birational transform of the empty closed subset is empty. -/
@[simp]
theorem transform_bot (f : RationalMap X Y) : f.transform ⊥ = ⊥ :=
  le_bot_iff.mp (transform_le_iff.mpr fun _ _ ↦ by simp)

/-- The support of `f.transformIdeal Z` is the birational transform `f_*(Z)`. -/
@[simp]
theorem support_transformIdeal (f : RationalMap X Y) (Z : Closeds X) :
    (f.transformIdeal Z).support = f.transform Z :=
  Closeds.ext_iff.mpr rfl

end RationalMap

/-- The *birational transform of `Z` under `g⁻¹`* for a morphism `g : Y ⟶ X` and a closed
subset `Z ⊆ X`: the closure `g⁻¹_*(Z)` of `g⁻¹(Z ∩ V_g)` in `Y`, where `V_g` is the union of
the `g`-biregular opens of `X`. -/
@[mmp "def_km0_inverse_birational_transform"]
def inverseTransform (g : Y ⟶ X) (Z : Closeds X) : Closeds Y :=
  Closeds.closure (g ⁻¹' ((Z : Set X) ∩ biregularLocus g))

/-- The ideal sheaf of the reduced structure on the birational transform `g⁻¹_*(Z)`. -/
@[mmp "def_km0_inverse_birational_transform"]
def inverseTransformIdeal (g : Y ⟶ X) (Z : Closeds X) : Y.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (inverseTransform g Z)

/-- The preimage `g⁻¹(Z ∩ V_g)` is contained in `g⁻¹_*(Z)`. -/
theorem preimage_subset_inverseTransform (g : Y ⟶ X) (Z : Closeds X) :
    g ⁻¹' ((Z : Set X) ∩ biregularLocus g) ⊆ inverseTransform g Z :=
  subset_closure

/-- The birational transform `g⁻¹_*` of closed subsets is monotone. -/
theorem inverseTransform_mono (g : Y ⟶ X) : Monotone (inverseTransform g) := fun _ _ hZ ↦
  closure_mono (Set.preimage_mono (Set.inter_subset_inter_left _ hZ))

/-- The support of `inverseTransformIdeal g Z` is the birational transform `g⁻¹_*(Z)`. -/
@[simp]
theorem support_inverseTransformIdeal (g : Y ⟶ X) (Z : Closeds X) :
    (inverseTransformIdeal g Z).support = inverseTransform g Z :=
  Closeds.ext_iff.mpr rfl

/-! ### Transforms of divisors -/

namespace DivisorWithCoeffs

variable {R : Type*} [AddCommMonoid R]

/-- The linear extension `∑ dᵢ Dᵢ ↦ ∑_{φ Dᵢ ≠ none} dᵢ φ(Dᵢ)` of a partial map `φ` on prime
divisors, dropping the components on which `φ` is not defined. -/
def mapPrimeDivisors (φ : PrimeDivisor X → Option (PrimeDivisor Y)) :
    DivisorWithCoeffs R X →+ DivisorWithCoeffs R Y :=
  Finsupp.liftAddHom fun D ↦ (φ D).elim 0 Finsupp.singleAddHom

/-- `mapPrimeDivisors φ` sends `r • D` to `r • E` if `φ D = some E`, and to `0` if `φ D = none`. -/
theorem mapPrimeDivisors_single (φ : PrimeDivisor X → Option (PrimeDivisor Y))
    (D : PrimeDivisor X) (r : R) :
    mapPrimeDivisors φ (Finsupp.single D r) = (φ D).elim 0 (Finsupp.single · r) := by
  rw [mapPrimeDivisors, Finsupp.liftAddHom_apply_single]
  cases φ D <;> rfl

/-- The linear extension of a partial map on prime divisors sends effective divisors to effective
divisors. -/
theorem mapPrimeDivisors_nonneg [PartialOrder R] [IsOrderedAddMonoid R]
    (φ : PrimeDivisor X → Option (PrimeDivisor Y)) {D : DivisorWithCoeffs R X} (hD : 0 ≤ D) :
    0 ≤ mapPrimeDivisors φ D := by
  rw [mapPrimeDivisors, Finsupp.liftAddHom_apply]
  refine Finset.sum_nonneg fun P _ ↦ ?_
  dsimp only
  cases φ P
  · exact le_rfl
  · exact Finsupp.single_nonneg.mpr (hD P)

/-- If `φ D = some E`, then `mapPrimeDivisors φ` sends `r • D` to `r • E`. -/
theorem mapPrimeDivisors_single_of_eq_some {φ : PrimeDivisor X → Option (PrimeDivisor Y)}
    {D : PrimeDivisor X} {E : PrimeDivisor Y} (h : φ D = some E) (r : R) :
    mapPrimeDivisors φ (Finsupp.single D r) = Finsupp.single E r := by
  rw [mapPrimeDivisors_single, h]; rfl

/-- If `φ D = none`, then `mapPrimeDivisors φ` sends `r • D` to `0`. -/
theorem mapPrimeDivisors_single_of_eq_none {φ : PrimeDivisor X → Option (PrimeDivisor Y)}
    {D : PrimeDivisor X} (h : φ D = none) (r : R) :
    mapPrimeDivisors φ (Finsupp.single D r) = 0 := by
  rw [mapPrimeDivisors_single, h]; rfl

/-- `mapPrimeDivisors φ` commutes with scalar multiplication. -/
theorem mapPrimeDivisors_smul {S : Type*} [Monoid S] [DistribMulAction S R]
    (φ : PrimeDivisor X → Option (PrimeDivisor Y)) (s : S) (D : DivisorWithCoeffs R X) :
    mapPrimeDivisors φ (s • D) = s • mapPrimeDivisors φ D := by
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D D' h h' => rw [smul_add, map_add, map_add, h, h', smul_add]
  | single D r =>
    rw [Finsupp.smul_single, mapPrimeDivisors_single, mapPrimeDivisors_single]
    cases φ D
    · simp
    · simp [Finsupp.smul_single]

/-- `DivisorWithCoeffs.mapPrimeDivisors` as a linear map. -/
def mapPrimeDivisorsₗ (S : Type*) [Semiring S] [Module S R]
    (φ : PrimeDivisor X → Option (PrimeDivisor Y)) :
    DivisorWithCoeffs R X →ₗ[S] DivisorWithCoeffs R Y where
  toAddHom := (mapPrimeDivisors φ).toAddHom
  map_smul' := mapPrimeDivisors_smul φ

/-- `mapPrimeDivisorsₗ S φ` agrees with `mapPrimeDivisors φ`. -/
@[simp]
theorem mapPrimeDivisorsₗ_apply (S : Type*) [Semiring S] [Module S R]
    (φ : PrimeDivisor X → Option (PrimeDivisor Y)) (D : DivisorWithCoeffs R X) :
    mapPrimeDivisorsₗ S φ D = mapPrimeDivisors φ D := rfl

end DivisorWithCoeffs

open DivisorWithCoeffs

namespace RationalMap

open Classical in
/-- The transform of a prime divisor `D` under a rational map `f`: the prime divisor `f_*(D)`
when `f` is defined at the generic point of `D` and `f_*(D)`, with its reduced structure, is a
prime divisor of `Y`, and `none` otherwise. -/
@[mmp "def_km0_birational_transform_divisor"]
def transformPrimeDivisor (f : RationalMap X Y) (D : PrimeDivisor X) : Option (PrimeDivisor Y) :=
  if h : f.DefinedAt D.genericPoint ∧
      ∃ E : PrimeDivisor Y, E.idealSheaf = f.transformIdeal D.idealSheaf.support then
    some h.2.choose
  else none

/-- The transform of `D` is the prime divisor `E` if and only if `f` is defined at the generic
point of `D` and the ideal sheaf of `E` is that of the reduced structure on `f_*(D)`. -/
theorem transformPrimeDivisor_eq_some_iff {f : RationalMap X Y} {D : PrimeDivisor X}
    {E : PrimeDivisor Y} :
    f.transformPrimeDivisor D = some E ↔
      f.DefinedAt D.genericPoint ∧ E.idealSheaf = f.transformIdeal D.idealSheaf.support := by
  unfold transformPrimeDivisor
  split_ifs with h
  · refine ⟨fun h' ↦ ?_, fun h' ↦ ?_⟩
    · cases Option.some.inj h'
      exact ⟨h.1, h.2.choose_spec⟩
    · exact congrArg some (PrimeDivisor.ext_idealSheaf (h.2.choose_spec.trans h'.2.symm))
  · simp only [false_iff]
    exact fun h' ↦ h ⟨h'.1, E, h'.2⟩

/-- The transform of `D` is `none` if and only if `f` is not defined at the generic point of `D`
or `f_*(D)` with its reduced structure is not a prime divisor of `Y`. -/
theorem transformPrimeDivisor_eq_none_iff {f : RationalMap X Y} {D : PrimeDivisor X} :
    f.transformPrimeDivisor D = none ↔
      ¬ (f.DefinedAt D.genericPoint ∧
        ∃ E : PrimeDivisor Y, E.idealSheaf = f.transformIdeal D.idealSheaf.support) := by
  unfold transformPrimeDivisor
  split_ifs with h <;> simp [h]

/-- If the transform of `D` is the prime divisor `E`, then the support of `E` is `f_*(D)`. -/
theorem support_transformPrimeDivisor {f : RationalMap X Y} {D : PrimeDivisor X}
    {E : PrimeDivisor Y} (h : f.transformPrimeDivisor D = some E) :
    E.support = f.transform D.idealSheaf.support := by
  rw [PrimeDivisor.support, (transformPrimeDivisor_eq_some_iff.mp h).2, support_transformIdeal]

/-- The *birational transform* `f_* D = ∑_{i ∈ J} dᵢ f_*(Dᵢ)` of a divisor `D = ∑ dᵢ Dᵢ` with
coefficients in `R`, where `J` is the set of `i` such that `f` is defined at the generic point of
`Dᵢ` and `f_*(Dᵢ)` is a prime divisor of `Y`; the other components are dropped. -/
@[mmp "def_km0_birational_transform_divisor"]
def transformDivisor {R : Type*} [AddCommMonoid R] (f : RationalMap X Y) :
    DivisorWithCoeffs R X →+ DivisorWithCoeffs R Y :=
  mapPrimeDivisors f.transformPrimeDivisor

/-- The birational transform of divisors, as a linear map. -/
@[mmp "def_km0_birational_transform_divisor"]
def transformDivisorₗ (S : Type*) {R : Type*} [Semiring S] [AddCommMonoid R] [Module S R]
    (f : RationalMap X Y) : DivisorWithCoeffs R X →ₗ[S] DivisorWithCoeffs R Y :=
  mapPrimeDivisorsₗ S f.transformPrimeDivisor

/-- `transformDivisorₗ S f` agrees with `f.transformDivisor`. -/
@[simp]
theorem transformDivisorₗ_apply (S : Type*) {R : Type*} [Semiring S] [AddCommMonoid R]
    [Module S R] (f : RationalMap X Y) (D : DivisorWithCoeffs R X) :
    transformDivisorₗ S f D = f.transformDivisor D := rfl

/-- `f_*(r • D)` is `r • f_*(D)` if `D` has a transform, and `0` otherwise. -/
theorem transformDivisor_single {R : Type*} [AddCommMonoid R] (f : RationalMap X Y)
    (D : PrimeDivisor X) (r : R) :
    f.transformDivisor (Finsupp.single D r) =
      (f.transformPrimeDivisor D).elim 0 (Finsupp.single · r) :=
  mapPrimeDivisors_single _ D r

/-- The birational transform of an effective divisor is effective. -/
theorem transformDivisor_nonneg {R : Type*} [AddCommMonoid R] [PartialOrder R]
    [IsOrderedAddMonoid R] (f : RationalMap X Y) {D : DivisorWithCoeffs R X} (hD : 0 ≤ D) :
    0 ≤ f.transformDivisor D :=
  mapPrimeDivisors_nonneg _ hD

/-- If the transform of `D` is the prime divisor `E`, then `f_*(r • D) = r • E`. -/
theorem transformDivisor_single_of_eq_some {R : Type*} [AddCommMonoid R] {f : RationalMap X Y}
    {D : PrimeDivisor X} {E : PrimeDivisor Y} (h : f.transformPrimeDivisor D = some E) (r : R) :
    f.transformDivisor (Finsupp.single D r) = Finsupp.single E r :=
  mapPrimeDivisors_single_of_eq_some h r

/-- If `D` has no transform, then `f_*(r • D) = 0`. -/
theorem transformDivisor_single_of_eq_none {R : Type*} [AddCommMonoid R] {f : RationalMap X Y}
    {D : PrimeDivisor X} (h : f.transformPrimeDivisor D = none) (r : R) :
    f.transformDivisor (Finsupp.single D r) = 0 :=
  mapPrimeDivisors_single_of_eq_none h r

end RationalMap

open Classical in
/-- The transform of a prime divisor `D ⊆ X` under the inverse of a morphism `g : Y ⟶ X`: the
prime divisor `g⁻¹_*(D)` when `D` meets `V_g` and `g⁻¹_*(D)`, with its reduced structure, is a
prime divisor of `Y`, and `none` otherwise. -/
@[mmp "def_km0_inverse_birational_transform_divisor"]
def inverseTransformPrimeDivisor (g : Y ⟶ X) (D : PrimeDivisor X) : Option (PrimeDivisor Y) :=
  if h : (D.support ∩ biregularLocus g).Nonempty ∧
      ∃ E : PrimeDivisor Y, E.idealSheaf = inverseTransformIdeal g D.idealSheaf.support then
    some h.2.choose
  else none

/-- The transform of `D` under `g⁻¹` is the prime divisor `E` if and only if `D` meets `V_g` and
the ideal sheaf of `E` is that of the reduced structure on `g⁻¹_*(D)`. -/
theorem inverseTransformPrimeDivisor_eq_some_iff {g : Y ⟶ X} {D : PrimeDivisor X}
    {E : PrimeDivisor Y} :
    inverseTransformPrimeDivisor g D = some E ↔
      (D.support ∩ biregularLocus g).Nonempty ∧
        E.idealSheaf = inverseTransformIdeal g D.idealSheaf.support := by
  unfold inverseTransformPrimeDivisor
  split_ifs with h
  · refine ⟨fun h' ↦ ?_, fun h' ↦ ?_⟩
    · cases Option.some.inj h'
      exact ⟨h.1, h.2.choose_spec⟩
    · exact congrArg some (PrimeDivisor.ext_idealSheaf (h.2.choose_spec.trans h'.2.symm))
  · simp only [false_iff]
    exact fun h' ↦ h ⟨h'.1, E, h'.2⟩

/-- The transform of `D` under `g⁻¹` is `none` if and only if `D` does not meet `V_g` or
`g⁻¹_*(D)` with its reduced structure is not a prime divisor of `Y`. -/
theorem inverseTransformPrimeDivisor_eq_none_iff {g : Y ⟶ X} {D : PrimeDivisor X} :
    inverseTransformPrimeDivisor g D = none ↔
      ¬ ((D.support ∩ biregularLocus g).Nonempty ∧
        ∃ E : PrimeDivisor Y, E.idealSheaf = inverseTransformIdeal g D.idealSheaf.support) := by
  unfold inverseTransformPrimeDivisor
  split_ifs with h <;> simp [h]

/-- If the transform of `D` under `g⁻¹` is the prime divisor `E`, then the support of `E` is
`g⁻¹_*(D)`. -/
theorem support_inverseTransformPrimeDivisor {g : Y ⟶ X} {D : PrimeDivisor X}
    {E : PrimeDivisor Y} (h : inverseTransformPrimeDivisor g D = some E) :
    E.support = inverseTransform g D.idealSheaf.support := by
  rw [PrimeDivisor.support, (inverseTransformPrimeDivisor_eq_some_iff.mp h).2,
    support_inverseTransformIdeal]

/-- The *birational transform* `g⁻¹_* D = ∑_{i ∈ J} dᵢ g⁻¹_*(Dᵢ)` of a divisor `D = ∑ dᵢ Dᵢ` on
`X` with coefficients in `R` under the inverse of a morphism `g : Y ⟶ X`, where `J` is the set
of `i` with `Dᵢ ∩ V_g ≠ ∅` and `g⁻¹_*(Dᵢ)` a prime divisor of `Y`. -/
@[mmp "def_km0_inverse_birational_transform_divisor"]
def inverseTransformDivisor {R : Type*} [AddCommMonoid R] (g : Y ⟶ X) :
    DivisorWithCoeffs R X →+ DivisorWithCoeffs R Y :=
  mapPrimeDivisors (inverseTransformPrimeDivisor g)

/-- The birational transform of divisors under the inverse of a morphism, as a linear map. -/
@[mmp "def_km0_inverse_birational_transform_divisor"]
def inverseTransformDivisorₗ (S : Type*) {R : Type*} [Semiring S] [AddCommMonoid R] [Module S R]
    (g : Y ⟶ X) : DivisorWithCoeffs R X →ₗ[S] DivisorWithCoeffs R Y :=
  mapPrimeDivisorsₗ S (inverseTransformPrimeDivisor g)

/-- `inverseTransformDivisorₗ S g` agrees with `inverseTransformDivisor g`. -/
@[simp]
theorem inverseTransformDivisorₗ_apply (S : Type*) {R : Type*} [Semiring S] [AddCommMonoid R]
    [Module S R] (g : Y ⟶ X) (D : DivisorWithCoeffs R X) :
    inverseTransformDivisorₗ S g D = inverseTransformDivisor g D := rfl

/-- `g⁻¹_*(r • D)` is `r • g⁻¹_*(D)` if `D` has a transform under `g⁻¹`, and `0` otherwise. -/
theorem inverseTransformDivisor_single {R : Type*} [AddCommMonoid R] (g : Y ⟶ X)
    (D : PrimeDivisor X) (r : R) :
    inverseTransformDivisor g (Finsupp.single D r) =
      (inverseTransformPrimeDivisor g D).elim 0 (Finsupp.single · r) :=
  mapPrimeDivisors_single _ D r

/-- If the transform of `D` under `g⁻¹` is the prime divisor `E`, then `g⁻¹_*(r • D) = r • E`. -/
theorem inverseTransformDivisor_single_of_eq_some {R : Type*} [AddCommMonoid R] {g : Y ⟶ X}
    {D : PrimeDivisor X} {E : PrimeDivisor Y} (h : inverseTransformPrimeDivisor g D = some E)
    (r : R) : inverseTransformDivisor g (Finsupp.single D r) = Finsupp.single E r :=
  mapPrimeDivisors_single_of_eq_some h r

/-- If `D` has no transform under `g⁻¹`, then `g⁻¹_*(r • D) = 0`. -/
theorem inverseTransformDivisor_single_of_eq_none {R : Type*} [AddCommMonoid R] {g : Y ⟶ X}
    {D : PrimeDivisor X} (h : inverseTransformPrimeDivisor g D = none) (r : R) :
    inverseTransformDivisor g (Finsupp.single D r) = 0 :=
  mapPrimeDivisors_single_of_eq_none h r

/-! ### Exceptional divisors -/

namespace RationalMap

/-- A prime divisor `E ⊆ X` is *`φ`-exceptional* (an *exceptional divisor* of `φ : X ⤏ X'`) if
either `φ` is not defined at the generic point of `E`, or `φ` is defined there and the
birational transform `φ_*(E)` has codimension at least two in `X'`. -/
@[mmp "def_km0_exceptional_divisor"]
def IsExceptional (φ : RationalMap X Y) (E : PrimeDivisor X) : Prop :=
  ¬ φ.DefinedAt E.genericPoint ∨
    (φ.DefinedAt E.genericPoint ∧ 2 ≤ closedsCodimension (φ.transform E.idealSheaf.support))

/-- A prime divisor `E` is `φ`-exceptional if and only if, whenever `φ` is defined at the generic
point of `E`, the transform `φ_*(E)` has codimension at least two. -/
theorem isExceptional_iff {φ : RationalMap X Y} {E : PrimeDivisor X} :
    φ.IsExceptional E ↔
      (φ.DefinedAt E.genericPoint → 2 ≤ closedsCodimension (φ.transform E.idealSheaf.support)) := by
  unfold IsExceptional
  tauto

/-- A prime divisor at whose generic point `φ` is not defined is `φ`-exceptional. -/
theorem isExceptional_of_not_definedAt {φ : RationalMap X Y} {E : PrimeDivisor X}
    (h : ¬ φ.DefinedAt E.genericPoint) : φ.IsExceptional E :=
  Or.inl h

end RationalMap

end MMP.Mori
