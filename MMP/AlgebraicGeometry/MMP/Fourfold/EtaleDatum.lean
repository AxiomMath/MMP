module

public import MMP.AlgebraicGeometry.MMP.Fourfold.LocalSetting
public import MMP.AlgebraicGeometry.MMP.Fourfold.Defs
public import MMP.AlgebraicGeometry.Morphisms.Birational.Transform
public import MMP.AlgebraicGeometry.Divisor.DivisorialSheaf
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.Henselization
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Normal
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal

/-!
# Local étale data along a singular curve, and transferred divisors

Let `(Y, Θ, T, π)` be a local setting (`MMP.Fourfold.IsLocalSetting`), with `η_T` the generic
point of `T`, `K_T = κ(η_T)` and `F_{η_T} = Ỹ ×_Y Spec K_T` the generic scheme fibre of
`π : Ỹ ⟶ Y`. For line bundles `L_1, …, L_b` on `F_{η_T}`, a *local étale datum* is a tuple
`(Y_e, q, η', L̃_1, …, L̃_b)`: `Y_e` is a normal integral quasi-projective variety, `q : Y_e ⟶ Y`
is étale, `η' ∈ Y_e` is a point over `η_T` with `κ(η_T) → κ(η')` an isomorphism, and the `L̃_i`
are line bundles on `Ỹ_e = Ỹ ×_Y Y_e` restricting to `L_i` on the scheme fibre
`Ỹ_e ×_{Y_e} Spec κ(η') = F_{η_T}`. We write `T'` for the closure of `η'`,
`π_e : Ỹ_e ⟶ Y_e` and `j_e : (Y_e)_reg ⟶ Y_e`.

Given moreover a projective small birational morphism `g : Y' ⟶ Y_e` and Cartier divisors `D̃_i`
on `Ỹ_e` with `𝒪(D̃_i) ≅ L̃_i`, the *transferred divisor* `D'_i` is the strict transform on `Y'`
of the Weil divisor `D_i = π_{e*} D̃_i` on `Y_e`.

## Main definitions

* `MMP.Fourfold.elementaryNeighborhoodSection`: the section `Spec κ(s) ⟶ U` of an elementary
  étale neighbourhood `(U, u)` of `(S, s)` through `u`.
* `MMP.Fourfold.localEtaleFibreMap`: the morphism `F_y ⟶ Ỹ ×_Y U` identifying `F_y` with the
  scheme fibre of `Ỹ ×_Y U ⟶ U` over the distinguished point.
* `MMP.Fourfold.LocalEtaleDatum`: local étale data `(Y_e, q, η', L̃_1, …, L̃_b)`, with the
  notation `LocalEtaleDatum.scheme` (`Y_e`), `LocalEtaleDatum.map` (`q`),
  `LocalEtaleDatum.point` (`η'`), `LocalEtaleDatum.resolution` (`Ỹ_e`),
  `LocalEtaleDatum.resolutionMap` (`π_e`), `LocalEtaleDatum.curve` (`T'`) and
  `LocalEtaleDatum.regularInclusion` (`j_e`).
* `MMP.Fourfold.LocalEtaleDatum.IsTransferSetting`: the data `(g, D̃_1, …, D̃_b)` of transferred
  divisors.
* `MMP.Fourfold.LocalEtaleDatum.transferredDivisor`: the transferred divisor
  `D' = g⁻¹_* π_{e*} D̃`.

## Main results

* `MMP.Fourfold.elementaryNeighborhoodSection_comp_toBase`: the section lies over
  `Spec κ(s) ⟶ S`.
* `MMP.Fourfold.IsLocalSetting.isNormal_resolution`: the resolution `Ỹ` of a local setting is
  normal; hence so is `Ỹ_e`, being étale over it
  (`MMP.Fourfold.LocalEtaleDatum.isNormal_resolution`).

## Implementation notes

* The triple `(Y_e, q, η')` is a pointed étale neighbourhood of `(Y, η_T)` whose residue field
  extension at `η'` is trivial, that is, an elementary étale neighbourhood
  (`AlgebraicGeometry.ElementaryEtaleNeighborhood`). `Y_e` is a variety over `ℂ` through
  `q ≫ s_Y`; a normal integral quasi-projective variety is a quasi-projective variety
  (`AlgebraicGeometry.IsQuasiProjectiveVariety`, which contains integrality) that is normal.
* Line bundles are invertible sheaves (`Stacks.Ample.IsInvertibleModule`), and the family
  `L_1, …, L_b` is indexed by `Fin b`. The local étale datum is defined for any `L_i`; it exists
  only when they are line bundles, since each is then isomorphic to the restriction of a line
  bundle.
* The identification `Ỹ_e ×_{Y_e} Spec κ(η') = F_{η_T}` comes from
  `Ỹ_e ×_{Y_e} Spec κ(η') = Ỹ ×_Y Spec κ(η')` and `κ(η_T) ≅ κ(η')`. Composed with the inclusion
  of the scheme fibre it is the morphism `F_{η_T} ⟶ Ỹ_e` which is the identity on the `Ỹ`
  factor and `Spec K_T ≅ Spec κ(η') ⟶ Y_e` on the other (`MMP.Fourfold.localEtaleFibreMap`);
  "`L̃_i` restricts to `L_i`" is that the pull-back of `L̃_i` along it is isomorphic to `L_i`.
* The datum and its notation are defined for every `(Y, T, π)`; a local setting is the context
  in which the source uses them.
* A Cartier divisor on `Ỹ_e`, which is normal, is a locally principal Weil divisor
  (`MMP.Mori.Divisor.IsCartier`), and `𝒪(D̃)` is its divisorial sheaf
  (`MMP.Mori.Divisor.divisorialSheaf`). The push-forward `π_{e*}` of a Weil divisor is the
  birational transform under the morphism `π_e`
  (`MMP.Mori.RationalMap.transformDivisor`), and the strict transform under `g` is
  `MMP.Mori.inverseTransformDivisor`. Normality of `Ỹ_e`, needed for Cartier divisors and their
  sheaves, is inherited from `Ỹ` along the étale morphism `Ỹ_e ⟶ Ỹ`; it is assumed of `Ỹ` as an
  instance and holds in a local setting (`MMP.Fourfold.IsLocalSetting.isNormal_resolution`).
* A projective small birational morphism is a small morphism (`MMP.Fourfold.IsSmallMorphism`,
  which is proper birational between normal varieties with exceptional locus of codimension at
  least two) that is projective.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori

/-! ### The section of an elementary étale neighbourhood -/

section Section

variable {S : Scheme.{0}} {s : S}

/-- The section `Spec κ(s) ⟶ U` through the distinguished point `u` of an elementary étale
neighbourhood `(U, u)` of `(S, s)`: the inverse of the isomorphism `κ(s) ≅ κ(u)`, followed by
`Spec κ(u) ⟶ U`. -/
def elementaryNeighborhoodSection (U : ElementaryEtaleNeighborhood S s) :
    Spec (S.residueField s) ⟶ U.obj.scheme :=
  haveI : IsIso U.obj.residueFieldMap := U.property
  Spec.map (inv U.obj.residueFieldMap) ≫ U.obj.scheme.fromSpecResidueField U.obj.point

/-- The section of an elementary étale neighbourhood lies over `Spec κ(s) ⟶ S`. -/
@[reassoc (attr := simp)]
theorem elementaryNeighborhoodSection_comp_toBase (U : ElementaryEtaleNeighborhood S s) :
    elementaryNeighborhoodSection U ≫ U.obj.toBase = S.fromSpecResidueField s := by
  have : IsIso U.obj.residueFieldMap := U.property
  have h : U.obj.toBase.residueFieldMap U.obj.point =
      (S.residueFieldCongr U.obj.map_point).hom ≫ U.obj.residueFieldMap := by
    rw [EtaleNeighborhood.residueFieldMap_def, Iso.hom_inv_id_assoc]
  rw [elementaryNeighborhoodSection, Category.assoc,
    ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, h, Spec.map_comp,
    Category.assoc, ← Category.assoc (Spec.map _), ← Spec.map_comp, IsIso.hom_inv_id,
    Spec.map_id, Category.id_comp, Scheme.residueFieldCongr_fromSpecResidueField]

end Section

/-! ### Local étale data -/

section LocalEtaleDatum

variable {Y Yt : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ))

/-- The morphism `F_y ⟶ Ỹ ×_Y U` from the scheme fibre `F_y = Ỹ ×_Y Spec κ(y)` of `π : Ỹ ⟶ Y`,
for an elementary étale neighbourhood `(U, u)` of `(Y, y)`: the identity on `Ỹ` and the section
`Spec κ(y) ⟶ U` through `u`. It identifies `F_y` with the scheme fibre
`(Ỹ ×_Y U) ×_U Spec κ(u)`. -/
def localEtaleFibreMap (π : Yt ⟶ Y) {y : Y} (U : ElementaryEtaleNeighborhood Y y) :
    pointSettingFibre π y ⟶ pullback π U.obj.toBase :=
  pullback.map π (Y.fromSpecResidueField y) π U.obj.toBase (𝟙 _)
    (elementaryNeighborhoodSection U) (𝟙 _) (by simp) (by simp)

/-- The morphism `F_y ⟶ Ỹ ×_Y U` is the identity on the `Ỹ` factor. -/
@[reassoc (attr := simp)]
theorem localEtaleFibreMap_fst (π : Yt ⟶ Y) {y : Y} (U : ElementaryEtaleNeighborhood Y y) :
    localEtaleFibreMap π U ≫ pullback.fst π U.obj.toBase = pullback.fst _ _ := by
  simp [localEtaleFibreMap]

/-- The morphism `F_y ⟶ Ỹ ×_Y U` is the section `Spec κ(y) ⟶ U` on the `U` factor. -/
@[reassoc (attr := simp)]
theorem localEtaleFibreMap_snd (π : Yt ⟶ Y) {y : Y} (U : ElementaryEtaleNeighborhood Y y) :
    localEtaleFibreMap π U ≫ pullback.snd π U.obj.toBase =
      pullback.snd _ _ ≫ elementaryNeighborhoodSection U := by
  simp [localEtaleFibreMap]

/-- A *local étale datum* `(Y_e, q, η', L̃_1, …, L̃_b)` for line bundles `L_1, …, L_b` on the
generic scheme fibre `F_{η_T} = Ỹ ×_Y Spec K_T` of `π : Ỹ ⟶ Y`: `Y_e` is a normal integral
quasi-projective variety, `q : Y_e ⟶ Y` is étale, `η' ∈ Y_e` is a point over `η_T` with
`κ(η_T) → κ(η')` an isomorphism, and the `L̃_i` are line bundles on `Ỹ_e = Ỹ ×_Y Y_e` restricting
to `L_i` on the scheme fibre `Ỹ_e ×_{Y_e} Spec κ(η') = F_{η_T}`. -/
@[mmp "def_oai4_c2_local_etale_datum"]
structure LocalEtaleDatum (T : IrreducibleCloseds Y) (π : Yt ⟶ Y) {b : ℕ}
    (L : Fin b → (pointSettingFibre π (localSettingGenericPoint T)).Modules) where
  /-- The pointed étale neighbourhood `(Y_e, η')` of `(Y, η_T)`, with `κ(η_T) ≅ κ(η')`. -/
  neighborhood : ElementaryEtaleNeighborhood Y (localSettingGenericPoint T)
  /-- `Y_e` is an integral quasi-projective variety over `ℂ`. -/
  isQuasiProjectiveVariety : IsQuasiProjectiveVariety ℂ (neighborhood.obj.toBase ≫ sY)
  /-- `Y_e` is normal. -/
  isNormal : IsNormal neighborhood.obj.scheme
  /-- The line bundles `L̃_i` on `Ỹ_e = Ỹ ×_Y Y_e`. -/
  bundle : Fin b → (pullback π neighborhood.obj.toBase).Modules
  /-- The `L̃_i` are line bundles. -/
  isInvertibleModule : ∀ i, Stacks.Ample.IsInvertibleModule _ (bundle i)
  /-- `L̃_i` restricts to `L_i` on the scheme fibre over `η'`, identified with `F_{η_T}`. -/
  restrict : ∀ i, Nonempty
    ((Scheme.Modules.pullback (localEtaleFibreMap π neighborhood)).obj (bundle i) ≅ L i)

namespace LocalEtaleDatum

variable {sY} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y} {b : ℕ}
  {L : Fin b → (pointSettingFibre π (localSettingGenericPoint T)).Modules}
  (E : LocalEtaleDatum sY T π L)

/-- The variety `Y_e` of a local étale datum. -/
@[mmp "def_oai4_c2_local_etale_datum"]
abbrev scheme : Scheme.{0} := E.neighborhood.obj.scheme

/-- The étale morphism `q : Y_e ⟶ Y` of a local étale datum. -/
@[mmp "def_oai4_c2_local_etale_datum"]
abbrev map : E.scheme ⟶ Y := E.neighborhood.obj.toBase

/-- The point `η' ∈ Y_e` over `η_T` of a local étale datum. -/
@[mmp "def_oai4_c2_local_etale_datum"]
abbrev point : E.scheme := E.neighborhood.obj.point

/-- The base change `Ỹ_e = Ỹ ×_Y Y_e` of the resolution. -/
@[mmp "def_oai4_c2_local_etale_datum"]
abbrev resolution : Scheme.{0} := pullback π E.map

/-- The morphism `π_e : Ỹ_e ⟶ Y_e`. -/
@[mmp "def_oai4_c2_local_etale_datum"]
abbrev resolutionMap : E.resolution ⟶ E.scheme := pullback.snd π E.map

/-- The curve `T' ⊆ Y_e`, the closure of `η'`. -/
@[mmp "def_oai4_c2_local_etale_datum"]
def curve : IrreducibleCloseds E.scheme :=
  ⟨closure {E.point}, isIrreducible_singleton.closure, isClosed_closure⟩

/-- The open immersion `j_e : (Y_e)_reg ⟶ Y_e` of the smooth locus of `Y_e` over `ℂ`. -/
@[mmp "def_oai4_c2_local_etale_datum"]
abbrev regularInclusion : (smoothLocus (E.map ≫ sY) : Scheme.{0}) ⟶ E.scheme :=
  (smoothLocus (E.map ≫ sY)).ι

/-- The underlying set of `T'` is the closure of `η'`. -/
@[simp]
theorem coe_curve : (E.curve : Set E.scheme) = closure {E.point} := rfl

/-- `η'` is the generic point of `T'`. -/
theorem isGenericPoint_point_curve : IsGenericPoint E.point (E.curve : Set E.scheme) := rfl

/-- `η'` lies over `η_T`. -/
theorem map_point : E.map E.point = localSettingGenericPoint T := E.neighborhood.obj.map_point

/-- `κ(η_T) → κ(η')` is an isomorphism. -/
theorem isIso_residueFieldMap : IsIso E.neighborhood.obj.residueFieldMap := E.neighborhood.property

/-- The line bundles `L̃_i` are invertible. -/
instance (i : Fin b) : Stacks.Ample.IsInvertibleModule _ (E.bundle i) := E.isInvertibleModule i

end LocalEtaleDatum

end LocalEtaleDatum

/-! ### Normality of the resolutions -/

section Normal

variable {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
  {sY : Y ⟶ Spec (.of ℂ)}

/-- The resolution `Ỹ` of a local setting is normal, being smooth over `ℂ`. -/
theorem IsLocalSetting.isNormal_resolution {Θ : QDivisor Y} {T : IrreducibleCloseds Y}
    {π : Yt ⟶ Y} (h : IsLocalSetting sY Θ T π) : IsNormal Yt := by
  obtain ⟨-, _, hsm, -, -⟩ := h.isResolution
  have : Smooth (π ≫ sY) := (isSmoothScheme_iff (π ≫ sY)).mp hsm
  have : IsNormal (Spec (.of ℂ)) :=
    isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed ℂ)
  exact isNormal_of_smooth (π ≫ sY)

/-- The resolution `Ỹ` of a local setting is locally Noetherian, being of finite type over
`ℂ`. -/
theorem IsLocalSetting.isLocallyNoetherian_resolution {Θ : QDivisor Y}
    {T : IrreducibleCloseds Y} {π : Yt ⟶ Y} (h : IsLocalSetting sY Θ T π) :
    IsLocallyNoetherian Yt := by
  obtain ⟨-, _, -, -, -⟩ := h.isResolution
  exact LocallyOfFiniteType.isLocallyNoetherian (π ≫ sY)

end Normal

namespace LocalEtaleDatum

variable {Y Yt : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y}
  {b : ℕ} {L : Fin b → (pointSettingFibre π (localSettingGenericPoint T)).Modules}
  (E : LocalEtaleDatum sY T π L)

/-- `Ỹ_e` is normal when `Ỹ` is, being étale over it. -/
instance isNormal_resolution [IsNormal Yt] : IsNormal E.resolution :=
  isNormal_of_etale (pullback.fst π E.map)

/-- `Ỹ_e` is locally Noetherian when `Ỹ` is, being étale over it. -/
instance isLocallyNoetherian_resolution [IsLocallyNoetherian Yt] :
    IsLocallyNoetherian E.resolution :=
  LocallyOfFiniteType.isLocallyNoetherian (pullback.fst π E.map)

/-! ### Transferred divisors -/

section Transfer

variable {Y' : Scheme.{0}}

/-- The *transferred divisor* `D' = g⁻¹_* π_{e*} D̃` on `Y'` of a divisor `D̃` on `Ỹ_e`, for
`g : Y' ⟶ Y_e`: the strict transform under `g` of the Weil divisor `π_{e*} D̃` on `Y_e`. -/
@[mmp "def_oai4_c2_transferred_divisor"]
def transferredDivisor (g : Y' ⟶ E.scheme) (D : Divisor E.resolution) : Divisor Y' :=
  inverseTransformDivisor g (RationalMap.transformDivisor E.resolutionMap.toRationalMap D)

/-- The transferred divisor is additive in `D̃`. -/
@[simp]
theorem transferredDivisor_add (g : Y' ⟶ E.scheme) (D D' : Divisor E.resolution) :
    E.transferredDivisor g (D + D') = E.transferredDivisor g D + E.transferredDivisor g D' := by
  simp [transferredDivisor]

variable [IsLocallyNoetherian Yt] [IsNormal Yt]

/-- The data `(g, D̃_1, …, D̃_b)` of transferred divisors for a local étale datum
`(Y_e, q, η', L̃_1, …, L̃_b)`: `g : Y' ⟶ Y_e` is a projective small birational morphism, and the
`D̃_i` are Cartier divisors on `Ỹ_e` with `𝒪(D̃_i) ≅ L̃_i`. -/
@[mmp "def_oai4_c2_transferred_divisor"]
structure IsTransferSetting (g : Y' ⟶ E.scheme) (D : Fin b → Divisor E.resolution) : Prop where
  /-- `g` is a small (proper birational) morphism of normal varieties over `ℂ`. -/
  isSmallMorphism : IsSmallMorphism (g ≫ E.map ≫ sY) (E.map ≫ sY) g
  /-- `g` is projective. -/
  isProjectiveMorphism : IsProjectiveMorphism g
  /-- The `D̃_i` are Cartier. -/
  isCartier : ∀ i, (D i).IsCartier
  /-- `𝒪(D̃_i) ≅ L̃_i`. -/
  divisorialSheaf_iso : ∀ i, Nonempty ((D i).divisorialSheaf ≅ E.bundle i)

end Transfer

end LocalEtaleDatum

end MMP.Fourfold
