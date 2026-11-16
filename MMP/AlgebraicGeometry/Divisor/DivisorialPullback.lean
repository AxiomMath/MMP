module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Divisor.Pullback
public import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
public import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
public import StacksFrontier.AlgebraicGeometry.NormInvertible.PullbackGenerator
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectFibreHomVanishing

/-!
# The divisorial sheaf of a pulled-back Cartier divisor

Let `f : X ⟶ Y` be a morphism of locally Noetherian normal schemes, quasi-compact, with `X`
integral, and `D` a Cartier divisor on `Y` such that `f` maps the generic point of `X` outside
`Supp D`. Then the divisorial sheaf of the pull-back `f^* D` is the pull-back of the divisorial
sheaf of `D`:

`𝒪_X(f^* D) ≅ f^* 𝒪_Y(D)`.

Choose, around every point `y` of `Y`, an open `U_y` with a local equation `φ_y` of `D`. Then
`φ_y⁻¹` freely generates `𝒪_Y(D)` over every open inside `U_y`, and on `U_y ∩ U_{y'}` the two
generators differ by the regular unit `φ_{y'} / φ_y`. The unit of `f^* ⊣ f_*` carries `φ_y⁻¹` to a
generator of `f^* 𝒪_Y(D)` over `f⁻¹(U_y)`, with transition units the pull-backs of those upstairs.
This is a local frame of the invertible sheaf `f^* 𝒪_Y(D)`, so `f^* 𝒪_Y(D) ≅ 𝒪_X(B)` for the
divisor `B` of the frame, whose coefficient along a prime divisor `E` is
`v_E(f^* φ_{f(η_E)}) - v_E(f^* φ_{y₀})` for the reference point `y₀ = f(η_X)`. Hence
`B + div(f^* φ_{y₀})` is the pull-back `f^* D`, and multiplication by `f^* φ_{y₀}` identifies
`𝒪_X(f^* D)` with `𝒪_X(B)`.

## Main definitions

* `MMP.Mori.Divisor.IsLocalEquation.generator`: the generator `φ⁻¹` of `𝒪_Y(D)` over `U`.
* `MMP.Mori.Divisor.IsCartier.pullbackFrame`: the pulled-back local frame of `f^* 𝒪_Y(D)`.

## Main results

* `MMP.Mori.Divisor.IsCartier.unit_pullbackFrame_apply`: the transition units of the
  pulled-back frame.
* `MMP.Mori.Divisor.IsCartier.isPullback_divisor_pullbackFrame`: the divisor of the frame,
  twisted by `f^* φ_{y₀}`, is `f^* D`.
* `MMP.Mori.Divisor.nonempty_divisorialSheaf_pullback_iso`: `𝒪_X(f^* D) ≅ f^* 𝒪_Y(D)`.

## Implementation notes

The pull-back of a generator is `Stacks.SheafOfModules.pullbackGenerator`, which is stated for
the pull-back functor `RingedSpaceModuleAdjunction.modulePullback` of the underlying ringed
spaces; `AlgebraicGeometry.modulePullbackIsoSchemePullback` identifies it with
`AlgebraicGeometry.Scheme.Modules.pullback`. The divisor of a local frame and the isomorphism
with its divisorial sheaf are `MMP.Mori.LocalFrame.divisor` and
`MMP.Mori.LocalFrame.isIso_toDivisorialSheaf`, which need `X` integral.

## References

* [R. Hartshorne, *Algebraic geometry*][Har77], II.6.13
* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Notation 0.4(5)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Mori

namespace Divisor

variable {Y : Scheme.{u}} [IsLocallyNoetherian Y] [IsNormal Y] {D : Divisor Y} {U : Y.Opens}
  {φ : (RationalFunctions Y)ˣ}

/-- A section of `𝒪_Y(D)`, read as a section of the sheaf of rational functions. -/
abbrev sectionVal {V : Y.Opens} (s : Γ(D.divisorialSheaf, V)) :
    ToType ((rationalFunctionsPresheaf Y).obj (op V)) :=
  (show D.divisorialSubmodule V from s).1

/-- The generator `φ⁻¹` of `𝒪_Y(D)` over `U`, for a local equation `φ` of `D` on `U`. -/
def IsLocalEquation.generator (hφ : D.IsLocalEquation U φ) :
    Stacks.SheafOfModules.GeneratorSections Y.toRingedSpace D.divisorialSheaf U :=
  ⟨hφ.invSection, hφ.isLocalGenerator_invSection⟩

variable (hD : D.IsCartier)

/-- A chosen open around `y` carrying a local equation of the Cartier divisor `D`. -/
def IsCartier.localOpen (y : Y) : Y.Opens := (hD y).choose

/-- The point `y` lies in the chosen open `hD.localOpen y`. -/
theorem IsCartier.mem_localOpen (y : Y) : y ∈ hD.localOpen y := (hD y).choose_spec.1

/-- The chosen local equation of `D` on `hD.localOpen y`. -/
def IsCartier.localEq (y : Y) : (RationalFunctions Y)ˣ := (hD y).choose_spec.2.choose

/-- `hD.localEq y` is a local equation of `D` on `hD.localOpen y`. -/
theorem IsCartier.isLocalEquation_localEq (y : Y) :
    D.IsLocalEquation (hD.localOpen y) (hD.localEq y) := (hD y).choose_spec.2.choose_spec

include hD in
/-- On a quasi-compact `Y`, the divisorial sheaf `𝒪_Y(D)` of a Cartier divisor `D` is
invertible. -/
theorem IsCartier.isInvertible_divisorialSheaf [CompactSpace Y] :
    Stacks.SheafOfModules.IsInvertible Y.presheaf
      (structureSheafRing Y.toRingedSpace).property
      D.divisorialSheaf :=
  hD.isInvertibleModule_divisorialSheaf

variable {X : Scheme.{u}} (f : X ⟶ Y) [CompactSpace Y]

/-- The local frame of `f^* 𝒪_Y(D)` pulled back from the frame `φ_y⁻¹` of `𝒪_Y(D)`. -/
def IsCartier.pullbackFrame (x₀ : X) :
    LocalFrame ((RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom).obj
      D.divisorialSheaf) where
  W x := f ⁻¹ᵁ hD.localOpen (f x)
  mem x := hD.mem_localOpen (f x)
  a x := (Stacks.SheafOfModules.pullbackGenerator f D.divisorialSheaf
    hD.isInvertible_divisorialSheaf _ (hD.isLocalEquation_localEq (f x)).generator).val
  isLocalGenerator x := (Stacks.SheafOfModules.pullbackGenerator f D.divisorialSheaf
    hD.isInvertible_divisorialSheaf _ (hD.isLocalEquation_localEq (f x)).generator).property
  base := x₀

/-- The two chosen generators of `𝒪_Y(D)` at `y` and `y'`, restricted to the overlap. -/
def IsCartier.ratio (y y' : Y) : (Γ(Y, hD.localOpen y ⊓ hD.localOpen y'))ˣ :=
  Stacks.SheafOfModules.generatorRatioUnit D.divisorialSheaf _
    (Stacks.SheafOfModules.generatorRestrict D.divisorialSheaf inf_le_right
      (hD.isLocalEquation_localEq y').generator)
    (Stacks.SheafOfModules.generatorRestrict D.divisorialSheaf inf_le_left
      (hD.isLocalEquation_localEq y).generator)

/-- The transition function of the pulled-back frame is the pull-back of the transition function
of the frame upstairs. -/
theorem IsCartier.transition_pullbackFrame (x₀ x : X) :
    (hD.pullbackFrame f x₀).transition x =
      f.app (hD.localOpen (f x) ⊓ hD.localOpen (f x₀)) (hD.ratio (f x) (f x₀)) := by
  refine IsLocalGenerator.coord_eq_of_smul_eq _ _ ?_
  have hL := hD.isInvertible_divisorialSheaf
  have key := Stacks.SheafOfModules.generatorRatio_spec _ _
    (Stacks.SheafOfModules.pullbackGenerator f D.divisorialSheaf hL _
      (Stacks.SheafOfModules.generatorRestrict D.divisorialSheaf inf_le_right
        (hD.isLocalEquation_localEq (f x₀)).generator))
    (Stacks.SheafOfModules.pullbackGenerator f D.divisorialSheaf hL _
      (Stacks.SheafOfModules.generatorRestrict D.divisorialSheaf inf_le_left
        (hD.isLocalEquation_localEq (f x)).generator))
  have hv := congrArg Units.val
    (Stacks.SheafOfModules.generatorRatioUnit_pullbackGenerator f D.divisorialSheaf hL _
      (Stacks.SheafOfModules.generatorRestrict D.divisorialSheaf inf_le_right
        (hD.isLocalEquation_localEq (f x₀)).generator)
      (Stacks.SheafOfModules.generatorRestrict D.divisorialSheaf inf_le_left
        (hD.isLocalEquation_localEq (f x)).generator))
  have e1 := (Stacks.SheafOfModules.generatorRatioUnit_val _ _ _ _).symm.trans hv
  have e2 := congrArg Subtype.val (Stacks.SheafOfModules.pullbackGenerator_restrict f
    D.divisorialSheaf hL (inf_le_right : hD.localOpen (f x) ⊓ hD.localOpen (f x₀) ≤ _)
    (hD.isLocalEquation_localEq (f x₀)).generator)
  have e3 := congrArg Subtype.val (Stacks.SheafOfModules.pullbackGenerator_restrict f
    D.divisorialSheaf hL (inf_le_left : hD.localOpen (f x) ⊓ hD.localOpen (f x₀) ≤ _)
    (hD.isLocalEquation_localEq (f x)).generator)
  rw [← e2, ← e3, e1] at key
  exact key.symm

omit [CompactSpace Y] in
/-- On the overlap of the two chosen opens, the transition function of the frame `φ_y⁻¹` is
`φ_{y'} / φ_y`, at every component meeting the overlap. -/
theorem IsCartier.germ_ratio (y y' : Y) (W : irreducibleComponents Y)
    (hW : componentGenericPoint Y W ∈ hD.localOpen y ⊓ hD.localOpen y') :
    Y.presheaf.germ _ _ hW ((hD.ratio y y' : Γ(Y, hD.localOpen y ⊓ hD.localOpen y'))) =
      ((hD.localEq y' * (hD.localEq y)⁻¹ : (RationalFunctions Y)ˣ) : RationalFunctions Y) W := by
  have key := Stacks.SheafOfModules.generatorRatio_spec D.divisorialSheaf _
    (Stacks.SheafOfModules.generatorRestrict D.divisorialSheaf inf_le_right
      (hD.isLocalEquation_localEq y').generator)
    (Stacks.SheafOfModules.generatorRestrict D.divisorialSheaf inf_le_left
      (hD.isLocalEquation_localEq y).generator)
  have h := congrFun (congrArg (fun s => sectionVal (D := D) s) key) ⟨W, hW⟩
  change ((hD.localEq y)⁻¹ : (RationalFunctions Y)ˣ).val W =
    Y.presheaf.germ _ _ hW (Stacks.SheafOfModules.generatorRatio D.divisorialSheaf _ _ _) *
      ((hD.localEq y')⁻¹ : (RationalFunctions Y)ˣ).val W at h
  have hv := Stacks.SheafOfModules.generatorRatioUnit_val D.divisorialSheaf _
    (Stacks.SheafOfModules.generatorRestrict D.divisorialSheaf inf_le_right
      (hD.isLocalEquation_localEq y').generator)
    (Stacks.SheafOfModules.generatorRestrict D.divisorialSheaf inf_le_left
      (hD.isLocalEquation_localEq y).generator)
  rw [IsCartier.ratio]
  erw [hv]
  rw [Units.val_mul, Pi.mul_apply]
  have hu : ((hD.localEq y')⁻¹ : (RationalFunctions Y)ˣ).val W *
      ((hD.localEq y' : (RationalFunctions Y)ˣ) : RationalFunctions Y) W = 1 := by
    rw [← Pi.mul_apply, Units.inv_mul, Pi.one_apply]
  rw [mul_comm, h, mul_assoc, hu, mul_one]

section Integral

variable [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  (hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ D.supp)

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- **The transition units of the pulled-back frame.** At the generic point of `X`, the transition
unit at `x` is `f^*φ_{y₀} · (f^*φ_{f x})⁻¹`, for the pull-backs `MMP.Mori.pullbackComponent` of the
chosen local equations. -/
theorem IsCartier.unit_pullbackFrame_apply (x₀ x : X) (Z : irreducibleComponents X)
    (hZ : componentGenericPoint X Z ∈ (hD.pullbackFrame f x₀).W x ⊓
      (hD.pullbackFrame f x₀).W (hD.pullbackFrame f x₀).base) :
    ((hD.pullbackFrame f x₀).unit x : RationalFunctions X) Z =
      ((pullbackComponent f hB (hD.isLocalEquation_localEq (f x₀)) Z hZ.2 *
        (pullbackComponent f hB (hD.isLocalEquation_localEq (f x)) Z hZ.1)⁻¹ :
          (X.presheaf.stalk (componentGenericPoint X Z))ˣ) :
        X.presheaf.stalk (componentGenericPoint X Z)) := by
  rw [LocalFrame.unit_apply _ x Z hZ, hD.transition_pullbackFrame f x₀ x]
  have hfZ : f (componentGenericPoint X Z) ∈ hD.localOpen (f x) ⊓ hD.localOpen (f x₀) := hZ
  refine (Scheme.Hom.germ_stalkMap_apply f _ _ hfZ
    (hD.ratio (f x) (f x₀) : Γ(Y, hD.localOpen (f x) ⊓ hD.localOpen (f x₀)))).symm.trans ?_
  have hW : f (componentGenericPoint X Z) ∈ (pointComponent (f (componentGenericPoint X Z))).1 :=
    mem_pointComponent _
  obtain ⟨a₀, ha₀⟩ := (hD.isLocalEquation_localEq (f x₀)).exists_unit_stalk hZ.2 (hB Z) hW
  obtain ⟨a, ha⟩ := (hD.isLocalEquation_localEq (f x)).exists_unit_stalk hZ.1 (hB Z) hW
  erw [pullbackComponent_eq hB (hD.isLocalEquation_localEq (f x₀)) hZ.2 hW a₀ ha₀,
    pullbackComponent_eq hB (hD.isLocalEquation_localEq (f x)) hZ.1 hW a ha, ← map_inv,
    ← map_mul]
  change _ = (f.stalkMap (componentGenericPoint X Z)).hom ((a₀ * a⁻¹ : (Y.presheaf.stalk _)ˣ) :
    Y.presheaf.stalk _)
  congr 1
  apply stalkToRationalFunctions_injective hW
  have hWV : componentGenericPoint Y (pointComponent (f (componentGenericPoint X Z))) ∈
      hD.localOpen (f x) ⊓ hD.localOpen (f x₀) :=
    ((isGenericPoint_componentGenericPoint Y _).specializes hW).mem_open (Opens.isOpen _) hfZ
  set W := pointComponent (f (componentGenericPoint X Z))
  set g := (stalkToRationalFunctions Y hW).hom
  have hl : g (Y.presheaf.germ _ _ hfZ
      (hD.ratio (f x) (f x₀) : Γ(Y, hD.localOpen (f x) ⊓ hD.localOpen (f x₀)))) =
      Y.presheaf.germ _ _ hWV
        (hD.ratio (f x) (f x₀) : Γ(Y, hD.localOpen (f x) ⊓ hD.localOpen (f x₀))) :=
    TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _
  rw [hl, hD.germ_ratio, Units.val_mul, Pi.mul_apply, Units.val_mul, map_mul, ha₀]
  congr 1
  refine left_inv_eq_right_inv (a := g a) ?_ (by rw [← map_mul, Units.mul_inv, map_one])
  rw [ha, ← Pi.mul_apply, Units.inv_mul, Pi.one_apply]

/-- The pull-back `f^*φ_{y₀}` of the chosen local equation of `D` at the image of the generic
point of `X`, a unit of `K(X)`. -/
def IsCartier.pullbackBaseEq : (RationalFunctions X)ˣ :=
  (RationalFunctions.unitsEquiv X).symm fun Z =>
    pullbackComponent f hB (hD.isLocalEquation_localEq (f (genericPoint X))) Z
      ((hD.pullbackFrame f (genericPoint X)).cgp_mem_base Z)

/-- The divisor of the pulled-back frame, twisted back by `f^*φ_{y₀}`, is the pull-back of `D`. -/
theorem IsCartier.isPullback_divisor_pullbackFrame [CompactSpace X] :
    D.IsPullback f hB ((hD.pullbackFrame f (genericPoint X)).divisor +
      principalDivisor (hD.pullbackBaseEq f hB)) := by
  set F := hD.pullbackFrame f (genericPoint X)
  refine IsPullback.of_forall_exists fun E => ?_
  have hE : (E.support ∩ f ⁻¹ᵁ hD.localOpen (f E.genericPoint)).Nonempty :=
    (E.genericPoint_mem_iff _).mp (hD.mem_localOpen _)
  refine ⟨_, _, hD.isLocalEquation_localEq (f E.genericPoint), hE, ?_⟩
  have hZ : componentGenericPoint X E.component ∈ F.W E.genericPoint ⊓ F.W F.base :=
    ⟨E.specializes_genericPoint.mem_open (F.W _).isOpen (F.mem _), F.cgp_mem_base _⟩
  have hu : Units.map (RationalFunctions.component X E.component).toMonoidHom
      (F.unit E.genericPoint) =
      pullbackComponent f hB (hD.isLocalEquation_localEq (f (genericPoint X))) E.component hZ.2 *
        (pullbackComponent f hB (hD.isLocalEquation_localEq (f E.genericPoint)) E.component
          hZ.1)⁻¹ :=
    Units.ext (hD.unit_pullbackFrame_apply f hB _ _ _ hZ)
  have hψ : Units.map (RationalFunctions.component X E.component).toMonoidHom
      (hD.pullbackBaseEq f hB) =
      pullbackComponent f hB (hD.isLocalEquation_localEq (f (genericPoint X))) E.component hZ.2 :=
    Units.ext rfl
  have hinv : ∀ v : (X.presheaf.stalk (componentGenericPoint X E.component))ˣ,
      E.ordUnit v⁻¹ = -E.ordUnit v := fun v => by
    have := E.ordUnit_mul v v⁻¹
    rw [mul_inv_cancel, PrimeDivisor.ordUnit_one] at this
    omega
  rw [DivisorWithCoeffs.coeff_add]
  erw [F.divisor_coeff E]
  rw [coeff_principalDivisor, PrimeDivisor.ord_eq_ordUnit, PrimeDivisor.ord_eq_ordUnit, hu, hψ,
    PrimeDivisor.ordUnit_mul, hinv]
  ring

/-- The pull-back of a Cartier divisor is Cartier: on `f⁻¹(U_y)` it has the local equation
`(f^*φ_y) / (f^*φ_{y₀}) · f^*φ_{y₀}`. -/
theorem IsCartier.isCartier_pullback [CompactSpace X] : (D.pullback hD hB).IsCartier := by
  set F := hD.pullbackFrame f (genericPoint X)
  rw [(hD.isPullback_divisor_pullbackFrame f hB).pullback_eq hD]
  intro x
  exact ⟨F.W x, F.mem x, _, (F.isLocalEquation_divisor x).add
    (isLocalEquation_principalDivisor (hD.pullbackBaseEq f hB) (F.W x))⟩

/-- **The divisorial sheaf of the pull-back of a Cartier divisor is the pull-back of its
divisorial sheaf**: `𝒪_X(f^*D) ≅ f^*𝒪_Y(D)`. -/
theorem nonempty_divisorialSheaf_pullback_iso [CompactSpace X] :
    Nonempty ((D.pullback hD hB).divisorialSheaf ≅
      (Scheme.Modules.pullback f).obj D.divisorialSheaf) := by
  set F := hD.pullbackFrame f (genericPoint X)
  rw [(hD.isPullback_divisor_pullbackFrame f hB).pullback_eq hD]
  have := F.isIso_toDivisorialSheaf
  exact ⟨divisorialSheafMulIso (hD.pullbackBaseEq f hB) (fun E => by
      rw [DivisorWithCoeffs.coeff_add, coeff_principalDivisor]) ≪≫
    (asIso F.toDivisorialSheaf).symm ≪≫
    (AlgebraicGeometry.modulePullbackIsoSchemePullback
      f).app _⟩

end Integral

end Divisor

end MMP.Mori
