module

public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldGraphDivisor
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
public import MMP.AlgebraicGeometry.MMP.Fourfold.WeakModel
public import MMP.AlgebraicGeometry.Singularities.LogResolution.Basic
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLine

/-!
# Branch counts of boundary unions and threefold point settings

Let `Y` be a normal variety and `Q = Q_1 ∪ ⋯ ∪ Q_m` a reduced union of distinct prime divisors of
`Y`, with normalizations `ν_j : Q_j^ν ⟶ Q_j`. For an irreducible closed subset `V ⊆ Q`, the
*branch count* `r_V` is the number of prime divisors of the disjoint union `∐_j Q_j^ν` mapping
onto `V`; a prime divisor mapping onto `V` with degree greater than one counts once. On a normal
complex threefold it is taken at irreducible curves `C ⊆ Q`, on a normal complex fourfold at
irreducible surfaces `V ⊆ Q`. It is the sum over `j` of the branch numbers of the `Q_j` along `V`
(`MMP.Fourfold.boundaryBranchCount_eq_sum`).

A *threefold point setting* is a triple `(Y, π, y)`: `Y` is a normal projective `ℚ`-factorial
complex threefold with `(Y, 0)` terminal, `π : Ỹ ⟶ Y` is a projective resolution which is an
isomorphism over the smooth locus `Y_reg`, and `y ∈ Sing Y` is a closed point. Attached to it are
the scheme fibre `F_y = Ỹ ×_Y Spec κ(y)`, the base change `Z = Ỹ ×_Y Spec A` to the local ring
`A = 𝒪_{Y,y}` with maximal ideal `𝔪`, its infinitesimal thickenings
`F_n = Z ×_A A/𝔪^{n+1}`, and the curve `T_y = {y} × ℙ¹ ⊆ Y × ℙ¹`.

## Main definitions

* `MMP.Fourfold.boundaryBranchCount`: the number of prime divisors of `∐_{S ∈ Q} S^ν` mapping
  onto a given subset.
* `MMP.Fourfold.IsThreefoldBoundaryBranchCount`: `r = r_C` for an irreducible curve `C ⊆ Q` on a
  normal complex threefold.
* `MMP.Fourfold.IsFourfoldBoundaryBranchCount`: `r = r_V` for an irreducible surface `V ⊆ Q` on a
  normal complex fourfold.
* `MMP.Fourfold.IsThreefoldPointSetting`: threefold point settings `(Y, π, y)`.
* `MMP.Fourfold.pointSettingFibre`, `MMP.Fourfold.pointSettingLocalization`,
  `MMP.Fourfold.pointSettingThickening`, `MMP.Fourfold.pointSettingCurve`: the schemes `F_y`, `Z`
  and `F_n`, and the subset `T_y ⊆ Y × ℙ¹`.

## Main results

* `MMP.Fourfold.boundaryBranchCount_eq_sum`: `r_V = ∑_j r_{V, Q_j}`, the sum of the branch numbers.
* `MMP.Fourfold.boundaryBranchCount_eq_zero_of_not_subset`: `r_V = 0` when `V ⊄ Q`.
* `MMP.Fourfold.pointSettingFibreIsoThickeningZero`: `F_0 = F_y`.
* `MMP.Fourfold.mem_pointSettingCurve_iff`: `t ∈ T_y` iff the first projection of `t` is `y`.

## Implementation notes

* The reduced union `Q` of distinct prime divisors is a finite set of prime divisors, so the `Q_j`
  are distinct; `Q` as a subset of `Y` is the union of their supports, and "`V ⊆ Q`" is
  containment in that union. The normalization of a prime divisor is
  `MMP.Fourfold.primeDivisorNormalization`, as for branch numbers. A prime divisor of the
  disjoint union `∐_j Q_j^ν` is a prime divisor of one `Q_j^ν`, so the prime divisors of the
  disjoint union are the pairs `(Q_j, P)` with `P` a prime divisor of `Q_j^ν`. The count is
  `Set.ncard` (`0` on an infinite set); the set is finite. Counting prime divisors, not their
  degrees, is what makes a divisor mapping with degree greater than one count once.
* The branch count `MMP.Fourfold.boundaryBranchCount` is defined for every scheme and every
  subset; the predicates `MMP.Fourfold.IsThreefoldBoundaryBranchCount` and
  `MMP.Fourfold.IsFourfoldBoundaryBranchCount` carry the setting of the source. A normal complex
  threefold (fourfold) is a normal variety (`MMP.Mori.IsNormalVariety`) over `ℂ` of dimension `3`
  (`4`), an irreducible curve (surface) is an irreducible closed subset of dimension `1` (`2`),
  and the branch count is taken along the subset itself.
* In a threefold point setting, `ℚ`-factoriality is `MMP.Fourfold.IsQFactorial`, terminality of
  `(Y, 0)` is `MMP.Fourfold.IsTerminalVariety` (which contains that `K_Y` is `ℚ`-Cartier), and a
  projective resolution is `MMP.Intersection.IsResolution` (a projective birational morphism from
  a non-singular variety). The smooth locus `Y_reg` is `MMP.Mori.smoothLocus` and
  `Sing Y = Y ∖ Y_reg` is `MMP.Mori.singularLocus`; "an isomorphism over `Y_reg`" is
  `MMP.Mori.IsBiregular`. A closed point is a point `y` with `{y}` closed.
* The fibre products are Mathlib's pull-backs: `Spec κ(y) ⟶ Y` is
  `AlgebraicGeometry.Scheme.fromSpecResidueField`, `Spec A ⟶ Y` is
  `AlgebraicGeometry.Scheme.fromSpecStalk`, and `Spec A/𝔪^{n+1} ⟶ Spec A` is induced by the
  quotient map. The projective line `ℙ¹_ℂ` is `AlgebraicGeometry.projectiveLine ℂ`, and
  `Y × ℙ¹` is the fibre product over `Spec ℂ`. The curve `T_y` is the preimage of `y` under the
  first projection, a subset of `Y × ℙ¹` (a closed subset carries its reduced structure). Its
  generic point `η_{T_y}` and the field `K_{T_y} = κ(η_{T_y})` are a generic point of that subset
  (`IsGenericPoint`) and its residue field `AlgebraicGeometry.Scheme.residueField`; they are not
  separate declarations.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Fourfold

open MMP.Mori

/-! ### Branch counts of a boundary union -/

section BoundaryBranchCount

variable {Y : Scheme.{u}}

/-- The *branch count* of a reduced union `Q = ⋃_{S ∈ Q} S` of distinct prime divisors of `Y`
along a subset `V ⊆ Y`: the number of prime divisors of the disjoint union `∐_{S ∈ Q} S^ν` of the
normalizations mapping onto `V`, that is, of pairs `(S, P)` with `S ∈ Q` and `P` a prime divisor
of `S^ν` with `ν_S(P) = V` for `ν_S : S^ν ⟶ S ⊆ Y` (`0` if there were infinitely many). -/
@[mmp "def_mmp_indexb_branch_count", mmp "def_oai4_branch_count"]
def boundaryBranchCount (Q : Finset (MMP.Mori.PrimeDivisor Y)) (V : Set Y) : ℕ :=
  {P : (S : Q) ×
      MMP.Mori.PrimeDivisor (primeDivisorNormalizationScheme (S : MMP.Mori.PrimeDivisor Y)) |
    primeDivisorNormalization (P.1 : MMP.Mori.PrimeDivisor Y) '' P.2.support = V}.ncard

/-- When every component has finitely many prime divisors of its normalization mapping onto `V`,
the branch count of `Q` along `V` is the sum over the components `S ∈ Q` of the branch numbers
`r_{V, S}`. -/
theorem boundaryBranchCount_eq_sum {Q : Finset (MMP.Mori.PrimeDivisor Y)} {V : Set Y}
    (hfin : ∀ S ∈ Q, {P : MMP.Mori.PrimeDivisor (primeDivisorNormalizationScheme S) |
      primeDivisorNormalization S '' P.support = V}.Finite) :
    boundaryBranchCount Q V = ∑ S ∈ Q, branchNumber S V := by
  let e : {P : (S : Q) ×
      MMP.Mori.PrimeDivisor (primeDivisorNormalizationScheme (S : MMP.Mori.PrimeDivisor Y)) |
      primeDivisorNormalization (P.1 : MMP.Mori.PrimeDivisor Y) '' P.2.support = V} ≃
      (S : Q) ×
        {P : MMP.Mori.PrimeDivisor
          (primeDivisorNormalizationScheme (S : MMP.Mori.PrimeDivisor Y)) |
        primeDivisorNormalization (S : MMP.Mori.PrimeDivisor Y) '' P.support = V} :=
    { toFun := fun P => ⟨P.1.1, P.1.2, P.2⟩
      invFun := fun P => ⟨⟨P.1, P.2.1⟩, P.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have : ∀ S : Q, Finite {P : MMP.Mori.PrimeDivisor
      (primeDivisorNormalizationScheme (S : MMP.Mori.PrimeDivisor Y)) |
        primeDivisorNormalization (S : MMP.Mori.PrimeDivisor Y) '' P.support = V} :=
    fun S => (hfin S.1 S.2).to_subtype
  rw [boundaryBranchCount, ← Nat.card_coe_set_eq, Nat.card_congr e, Nat.card_sigma,
    ← Finset.sum_coe_sort Q]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [branchNumber, ← Nat.card_coe_set_eq]

/-- The branch count of `Q` along a subset `V` not contained in `Q` vanishes. -/
theorem boundaryBranchCount_eq_zero_of_not_subset {Q : Finset (MMP.Mori.PrimeDivisor Y)}
    {V : Set Y} (hV : ¬ V ⊆ ⋃ S ∈ Q, (S.support : Set Y)) : boundaryBranchCount Q V = 0 := by
  have hempty : {P : (S : Q) × MMP.Mori.PrimeDivisor
      (primeDivisorNormalizationScheme (S : MMP.Mori.PrimeDivisor Y)) |
        primeDivisorNormalization (P.1 : MMP.Mori.PrimeDivisor Y) '' P.2.support = V} = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun P hP => hV ?_
    rw [← show primeDivisorNormalization (P.1 : MMP.Mori.PrimeDivisor Y) '' P.2.support = V from hP]
    exact ((Set.image_subset_range _ _).trans
      (range_primeDivisorNormalization_subset _)).trans
      (Set.subset_biUnion_of_mem
        (u := fun S : MMP.Mori.PrimeDivisor Y => (S.support : Set Y)) P.1.2)
  rw [boundaryBranchCount, hempty, Set.ncard_empty]

end BoundaryBranchCount

/-! ### Branch counts on complex threefolds and fourfolds -/

section ComplexBranchCount

variable {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ))

/-- `r` is the *branch count* `r_C` of a reduced union `Q = ⋃_{S ∈ Q} S` of distinct prime divisors
of a normal complex threefold `Y` at an irreducible curve `C ⊆ Q`: the number of prime divisors of
`∐_{S ∈ Q} S^ν` mapping onto `C` (`MMP.Fourfold.boundaryBranchCount`). -/
@[mmp "def_mmp_indexb_branch_count"]
def IsThreefoldBoundaryBranchCount (Q : Finset (MMP.Mori.PrimeDivisor Y)) (C : IrreducibleCloseds Y)
    (r : ℕ) : Prop :=
  IsNormalVariety ℂ sY ∧ topologicalKrullDim Y = 3 ∧ topologicalKrullDim (C : Set Y) = 1 ∧
    (C : Set Y) ⊆ ⋃ S ∈ Q, (S.support : Set Y) ∧ r = boundaryBranchCount Q C

/-- `r` is the *branch count* `r_V` of a reduced union `Q = ⋃_{S ∈ Q} S` of distinct prime divisors
of a normal complex fourfold `Y` at an irreducible surface `V ⊆ Q`: the number of prime divisors
of `∐_{S ∈ Q} S^ν` mapping onto `V` (`MMP.Fourfold.boundaryBranchCount`). -/
@[mmp "def_oai4_branch_count"]
def IsFourfoldBoundaryBranchCount (Q : Finset (MMP.Mori.PrimeDivisor Y)) (V : IrreducibleCloseds Y)
    (r : ℕ) : Prop :=
  IsNormalVariety ℂ sY ∧ topologicalKrullDim Y = 4 ∧ topologicalKrullDim (V : Set Y) = 2 ∧
    (V : Set Y) ⊆ ⋃ S ∈ Q, (S.support : Set Y) ∧ r = boundaryBranchCount Q V

variable {sY} {Q : Finset (MMP.Mori.PrimeDivisor Y)}

/-- The branch count `r_C` is unique. -/
theorem IsThreefoldBoundaryBranchCount.eq {C : IrreducibleCloseds Y} {r r' : ℕ}
    (h : IsThreefoldBoundaryBranchCount sY Q C r) (h' : IsThreefoldBoundaryBranchCount sY Q C r') :
    r = r' :=
  h.2.2.2.2.trans h'.2.2.2.2.symm

/-- The branch count `r_V` is unique. -/
theorem IsFourfoldBoundaryBranchCount.eq {V : IrreducibleCloseds Y} {r r' : ℕ}
    (h : IsFourfoldBoundaryBranchCount sY Q V r) (h' : IsFourfoldBoundaryBranchCount sY Q V r') :
    r = r' :=
  h.2.2.2.2.trans h'.2.2.2.2.symm

end ComplexBranchCount

/-! ### Threefold point settings -/

section PointSetting

variable {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
  (sY : Y ⟶ Spec (.of ℂ))

/-- A *threefold point setting* `(Y, π, y)`: `Y` is a normal projective `ℚ`-factorial complex
threefold such that `(Y, 0)` is terminal, `π : Ỹ ⟶ Y` is a projective resolution which is an
isomorphism over the smooth locus `Y_reg`, and `y ∈ Sing Y` is a closed point. -/
@[mmp "def_mmp_indexb_point_setting"]
structure IsThreefoldPointSetting (π : Yt ⟶ Y) (y : Y) : Prop where
  /-- `Y` is `ℚ`-factorial (in particular a normal variety). -/
  isQFactorial : IsQFactorial sY
  /-- `Y` is projective. -/
  isProjectiveVariety : MMP.Mori.IsProjectiveVariety ℂ sY
  /-- `Y` is a threefold. -/
  topologicalKrullDim_eq : topologicalKrullDim Y = 3
  /-- `(Y, 0)` is terminal. -/
  isTerminalVariety : IsTerminalVariety sY
  /-- `π` is a projective resolution. -/
  isResolution : MMP.Intersection.IsResolution sY π
  /-- `π` is an isomorphism over `Y_reg`. -/
  isBiregular : IsBiregular π (smoothLocus sY)
  /-- `y` is a singular point. -/
  mem_singularLocus : y ∈ singularLocus sY
  /-- `y` is a closed point. -/
  isClosed_singleton : IsClosed ({y} : Set Y)

end PointSetting

section PointSettingNotation

variable {Y Yt : Scheme.{0}} (π : Yt ⟶ Y) (y : Y)

/-- The scheme fibre `F_y = Ỹ ×_Y Spec κ(y)` of `π : Ỹ ⟶ Y` over `y`. -/
@[mmp "def_mmp_indexb_point_setting"]
abbrev pointSettingFibre : Scheme.{0} :=
  pullback π (Y.fromSpecResidueField y)

/-- The base change `Z = Ỹ ×_Y Spec A` of `π : Ỹ ⟶ Y` to the local ring `A = 𝒪_{Y,y}`. -/
@[mmp "def_mmp_indexb_point_setting"]
abbrev pointSettingLocalization : Scheme.{0} :=
  pullback π (Y.fromSpecStalk y)

/-- The thickening `F_n = Z ×_A A/𝔪^{n+1}` of the fibre of `π : Ỹ ⟶ Y` over `y`, where
`A = 𝒪_{Y,y}` has maximal ideal `𝔪` and `Z = Ỹ ×_Y Spec A`. -/
@[mmp "def_mmp_indexb_point_setting"]
abbrev pointSettingThickening (n : ℕ) : Scheme.{0} :=
  pullback (pullback.snd π (Y.fromSpecStalk y))
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk y) ^ (n + 1)))))

/-- The thickening `F_0 = Z ×_A A/𝔪` is the scheme fibre `F_y`, as `A/𝔪 = κ(y)`. -/
def pointSettingFibreIsoThickeningZero :
    pointSettingFibre π y ≅ pointSettingThickening π y 0 := by
  let φ : CommRingCat.of (Y.presheaf.stalk y ⧸
      IsLocalRing.maximalIdeal (Y.presheaf.stalk y) ^ (0 + 1))
      ≅ Y.residueField y :=
    (Ideal.quotEquivOfEq (by rw [zero_add, pow_one])).toCommRingCatIso
  have h : Y.fromSpecResidueField y = (Scheme.Spec.mapIso φ.op).hom ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (IsLocalRing.maximalIdeal (Y.presheaf.stalk y) ^ (0 + 1)))) ≫ Y.fromSpecStalk y := by
    rw [Scheme.fromSpecResidueField, ← Category.assoc]
    congr 1
    simp only [Functor.mapIso_hom, Iso.op_hom, Scheme.Spec_map, Quiver.Hom.unop_op]
    rw [← Spec.map_comp]
    congr 1
  refine pullback.congrHom rfl h ≪≫ ?_ ≪≫ (pullbackLeftPullbackSndIso π _ _).symm
  let k : Spec (CommRingCat.of (Y.presheaf.stalk y ⧸
      IsLocalRing.maximalIdeal (Y.presheaf.stalk y) ^ (0 + 1))) ⟶ Y :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk y) ^ (0 + 1)))) ≫ Y.fromSpecStalk y
  exact @asIso _ _ _ _ _ (pullback.map_isIso π ((Scheme.Spec.mapIso φ.op).hom ≫ k) π k (𝟙 _)
    (Scheme.Spec.mapIso φ.op).hom (𝟙 _) (by simp) (Category.comp_id _))

/-- The curve `T_y = {y} × ℙ¹ ⊆ Y × ℙ¹` (the fibre product over `Spec ℂ`): the preimage of `y`
under the first projection. -/
@[mmp "def_mmp_indexb_point_setting"]
def pointSettingCurve (sY : Y ⟶ Spec (.of ℂ)) (y : Y) :
    Set ↥(pullback sY (projectiveLine ℂ ↘ Spec (.of ℂ)) : Scheme.{0}) :=
  (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ))).base ⁻¹' {y}

/-- A point of `Y × ℙ¹` lies on `T_y` exactly when its first projection is `y`. -/
@[simp]
theorem mem_pointSettingCurve_iff {sY : Y ⟶ Spec (.of ℂ)} {y : Y}
    {t : ↥(pullback sY (projectiveLine ℂ ↘ Spec (.of ℂ)) : Scheme.{0})} :
    t ∈ pointSettingCurve sY y ↔ (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ))).base t = y :=
  Iff.rfl

end PointSettingNotation

end MMP.Fourfold
