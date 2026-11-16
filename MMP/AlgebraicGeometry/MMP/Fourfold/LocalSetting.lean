module

public import MMP.AlgebraicGeometry.MMP.Fourfold.BranchCounts
public import MMP.AlgebraicGeometry.Singularities.Semismooth.Defs
public import StacksFrontier.AlgebraicGeometry.NormalizationMono.GenericPoints
public import StacksFrontier.AlgebraicGeometry.Properties.Noetherian

/-!
# Local settings along a singular curve of a terminal fourfold, and conductor preimages

A *local setting* is a tuple `(Y, Θ, T, π)`: `Y` is a normal projective `ℚ`-factorial complex
fourfold, `(Y, Θ)` is an effective terminal pair with rational boundary, `T ⊆ Sing Y` is an
irreducible curve, and `π : Ỹ ⟶ Y` is a projective resolution which is an isomorphism over the
smooth locus `Y_reg`. Attached to it are the inclusion `j : Y_reg ⟶ Y`, the generic point `η_T`
of `T`, its residue field `K_T = κ(η_T)`, and the scheme fibres `F_y = Ỹ ×_Y Spec κ(y)`.

Let `R` be a reduced projective complex variety of pure dimension three with normalization
`ν_R : N_R ⟶ R`, and `A_R ⊆ R` a closed subset of dimension at most two, with its reduced
structure, such that `ν_R` is an isomorphism over `R ∖ A_R`. The *conductor preimage* is
`F_R = (ν_R⁻¹ A_R)_red`.

## Main definitions

* `MMP.Fourfold.IsLocalSetting`: local settings `(Y, Θ, T, π)`.
* `MMP.Fourfold.localSettingRegularInclusion`, `MMP.Fourfold.localSettingGenericPoint`,
  `MMP.Fourfold.localSettingFunctionField`: `j : Y_reg ⟶ Y`, `η_T` and `K_T`; the scheme fibre
  `F_y` is `MMP.Fourfold.pointSettingFibre`.
* `MMP.Fourfold.IsConductorPreimageSetting`: the data `(R, ν_R, A_R)` of a conductor preimage.
* `MMP.Fourfold.conductorPreimage`, `MMP.Fourfold.conductorPreimageScheme`: `F_R` as a closed
  subset of `N_R` and as a reduced closed subscheme of `N_R`.

## Implementation notes

* As for threefold point settings (`MMP.Fourfold.IsThreefoldPointSetting`), `ℚ`-factoriality is
  `MMP.Fourfold.IsQFactorial`, a projective resolution is `MMP.Intersection.IsResolution`, the
  smooth and singular loci are `MMP.Mori.smoothLocus` and `MMP.Mori.singularLocus`, and "an
  isomorphism over `Y_reg`" is `MMP.Mori.IsBiregular`. An effective terminal pair with rational
  boundary is `MMP.Fourfold.IsKltTerminalPair` for a `ℚ`-divisor `Θ`; it contains that `(Y, Θ)`
  is a pair (`MMP.Fourfold.IsPair`), so that `Θ` is effective and `K_Y + Θ` is `ℚ`-Cartier.
* An irreducible curve `T ⊆ Y` is an irreducible closed subset of dimension `1`, as for branch
  counts (`MMP.Fourfold.IsFourfoldBoundaryBranchCount`). Its generic point is the generic point
  of the irreducible closed subset `T` (schemes are quasi-sober).
* A reduced projective complex variety of pure dimension three is a reduced separated scheme of
  finite type over `ℂ` of pure dimension three (`MMP.Flips.IsNFold`) whose structure morphism is
  projective; it need not be irreducible. Its normalization is
  `Stacks.AlgebraicGeometry.Normalization.normalization`, the relative normalization in the
  spectra of the residue fields at the generic points; the local Noetherianity it is built from
  is a consequence of finite type over `ℂ`. A closed reduced subset is a closed subset, carrying
  its reduced structure, and "an isomorphism over `R ∖ A_R`" is `MMP.Mori.IsBiregular` over the
  complement of `A_R`. The reduced structure on `ν_R⁻¹ A_R` is the closed subscheme cut out by
  its vanishing ideal.
-/

@[expose] public noncomputable section

open AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori

/-! ### Local settings -/

section LocalSetting

variable {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
  (sY : Y ⟶ Spec (.of ℂ))

/-- A *local setting* `(Y, Θ, T, π)`: `Y` is a normal projective `ℚ`-factorial complex fourfold,
`(Y, Θ)` is an effective terminal pair with rational boundary, `T ⊆ Sing Y` is an irreducible
curve, and `π : Ỹ ⟶ Y` is a projective resolution which is an isomorphism over the smooth locus
`Y_reg`. -/
@[mmp "def_oai4_c2_local_setting"]
structure IsLocalSetting (Θ : QDivisor Y) (T : IrreducibleCloseds Y) (π : Yt ⟶ Y) : Prop where
  /-- `Y` is `ℚ`-factorial (in particular a normal variety). -/
  isQFactorial : IsQFactorial sY
  /-- `Y` is projective. -/
  isProjectiveVariety : MMP.Mori.IsProjectiveVariety ℂ sY
  /-- `Y` is a fourfold. -/
  topologicalKrullDim_eq : topologicalKrullDim Y = 4
  /-- `(Y, Θ)` is a terminal pair; in particular `Θ` is effective. -/
  isKltTerminalPair : IsKltTerminalPair sY Θ
  /-- `T` is a curve. -/
  topologicalKrullDim_curve : topologicalKrullDim (T : Set Y) = 1
  /-- `T` lies in the singular locus. -/
  subset_singularLocus : (T : Set Y) ⊆ singularLocus sY
  /-- `π` is a projective resolution. -/
  isResolution : MMP.Intersection.IsResolution sY π
  /-- `π` is an isomorphism over `Y_reg`. -/
  isBiregular : IsBiregular π (smoothLocus sY)

end LocalSetting

section LocalSettingNotation

variable {Y : Scheme.{0}}

/-- The open immersion `j : Y_reg ⟶ Y` of the smooth locus of `Y` over `ℂ`. -/
@[mmp "def_oai4_c2_local_setting"]
abbrev localSettingRegularInclusion (sY : Y ⟶ Spec (.of ℂ)) : (smoothLocus sY : Scheme.{0}) ⟶ Y :=
  (smoothLocus sY).ι

/-- The generic point `η_T` of an irreducible closed subset `T ⊆ Y`. -/
@[mmp "def_oai4_c2_local_setting"]
abbrev localSettingGenericPoint (T : IrreducibleCloseds Y) : Y :=
  T.isIrreducible.genericPoint

/-- The field `K_T = κ(η_T)`, the residue field at the generic point of `T`. -/
@[mmp "def_oai4_c2_local_setting"]
abbrev localSettingFunctionField (T : IrreducibleCloseds Y) : Type :=
  Y.residueField (localSettingGenericPoint T)

/-- `η_T` is a generic point of `T`. -/
theorem isGenericPoint_localSettingGenericPoint (T : IrreducibleCloseds Y) :
    IsGenericPoint (localSettingGenericPoint T) (T : Set Y) :=
  T.isIrreducible.isGenericPoint_genericPoint T.isClosed

end LocalSettingNotation

/- The scheme fibre `F_y = Ỹ ×_Y Spec κ(y)` of the resolution of a local setting is
`MMP.Fourfold.pointSettingFibre`. -/
attribute [mmp "def_oai4_c2_local_setting"] pointSettingFibre

/-! ### Conductor preimages -/

section ConductorPreimage

variable {R : Scheme.{0}} [IsLocallyNoetherian R]

/-- The normalization `ν_R : N_R ⟶ R` of a locally Noetherian scheme `R`. -/
abbrev conductorNormalization (R : Scheme.{0}) [IsLocallyNoetherian R] :
    Stacks.AlgebraicGeometry.Normalization.normalizationScheme R
      (finite_irreducibleComponents_of_isCompact R) ⟶ R :=
  Stacks.AlgebraicGeometry.Normalization.normalization R
    (finite_irreducibleComponents_of_isCompact R)

/-- The data `(R, ν_R, A_R)` of a conductor preimage: `R` is a reduced projective complex variety
of pure dimension three with normalization `ν_R : N_R ⟶ R`, and `A_R ⊆ R` is a closed (reduced)
subset of dimension at most two such that `ν_R` is an isomorphism over `R ∖ A_R`. -/
@[mmp "def_oai4_c2_normalization_preimage"]
structure IsConductorPreimageSetting (sR : R ⟶ Spec (.of ℂ)) (A : Closeds R) : Prop where
  /-- `R` is a reduced separated scheme of finite type over `ℂ` of pure dimension three. -/
  isNFold : MMP.Flips.IsNFold sR 3
  /-- `R` is projective over `ℂ`. -/
  isProjectiveMorphism : IsProjectiveMorphism sR
  /-- `A_R` has dimension at most two. -/
  topologicalKrullDim_le : topologicalKrullDim (A : Set R) ≤ 2
  /-- `ν_R` is an isomorphism over `R ∖ A_R`. -/
  isBiregular : IsBiregular (conductorNormalization R) A.compl

/-- The *conductor preimage* `F_R = (ν_R⁻¹ A_R)_red`, as a closed subset of the normalization
`N_R`. -/
@[mmp "def_oai4_c2_normalization_preimage"]
def conductorPreimage (A : Closeds R) :
    Closeds (Stacks.AlgebraicGeometry.Normalization.normalizationScheme R
      (finite_irreducibleComponents_of_isCompact R)) :=
  A.preimage (conductorNormalization R).continuous

/-- The *conductor preimage* `F_R = (ν_R⁻¹ A_R)_red` as a scheme: the reduced closed subscheme
of `N_R` on `ν_R⁻¹ A_R`. -/
@[mmp "def_oai4_c2_normalization_preimage"]
abbrev conductorPreimageScheme (A : Closeds R) : Scheme.{0} :=
  (Scheme.IdealSheafData.vanishingIdeal (conductorPreimage A)).subscheme

/-- The underlying set of `conductorPreimage A` is the preimage of `A` under `ν_R`. -/
@[simp]
theorem coe_conductorPreimage (A : Closeds R) :
    (conductorPreimage A : Set _) = (conductorNormalization R).base ⁻¹' A :=
  rfl

/-- A point lies in `conductorPreimage A` iff its image under `ν_R` lies in `A`. -/
@[simp]
theorem mem_conductorPreimage {A : Closeds R}
    {x : Stacks.AlgebraicGeometry.Normalization.normalizationScheme R
      (finite_irreducibleComponents_of_isCompact R)} :
    x ∈ conductorPreimage A ↔ (conductorNormalization R).base x ∈ A :=
  Iff.rfl

end ConductorPreimage

end MMP.Fourfold
