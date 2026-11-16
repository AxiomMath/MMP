/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Intersection.CurveDegreeProjection
public import MMP.AlgebraicGeometry.Intersection.CurveDegreeAdditive
public import MMP.AlgebraicGeometry.Divisor.Pullback
public import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
public import StacksFrontier.AlgebraicGeometry.InvertiblePushforwardPullback

/-!
# Intersection numbers of pulled-back `ℚ`-Cartier divisors with curves

Let `u : V ⟶ W` be a morphism of normal varieties over a field `k`, `L` a `ℚ`-Cartier
`ℚ`-divisor on `W` whose support does not contain the image of the generic point of `V`, so that
the pull-back `u^*L` is defined, and `C` a proper curve over `k` mapping to `V` (for instance a
proper irreducible curve `C ⊆ V`). Then:

* if `u(C)` is a point, `(u^*L · C) = 0`;
* if `u(C)` is a curve, `(u^*L · C) = deg(C → u(C)) · (L · u(C))`, the degree being the field
  degree `[k(C) : k(u(C))]`.

The key input is the comparison `𝒪_V(u^*B) ≅ u^* 𝒪_W(B)` for a Cartier divisor `B` on `W` with
Weil-divisor pull-back `u^*B`. Choose local equations `ψ_w` of `B` on opens `U_w ∋ w`. Then
`ψ_w⁻¹` freely generates `𝒪_W(B)` over every open inside `U_w`, so its pull-back freely generates
`u^* 𝒪_W(B)` over every open inside `u⁻¹ U_w` [Stacks, Tag 0H78]. On `U_w ∩ U_{w₀}` one has
`ψ_w⁻¹ = g · ψ_{w₀}⁻¹` with `g` regular, so the transition functions of the pulled-back frame are
`u^♯ g = u^*ψ_{w₀} / u^*ψ_w`. The divisor of this frame is therefore `u^*B - div(u^*ψ_{w₀})`,
and an invertible module with a local frame is the divisorial sheaf of the divisor of the frame.
With `m` the Cartier index of `L`, `m u^*L` is the pull-back of the Cartier divisor `mL`, so
`(u^*L · C) = (1/m) deg_C 𝒪_V(m u^*L) = (1/m) deg_C u^* 𝒪_W(mL)`, and the two cases follow from
the corresponding statements for the invertible sheaf `𝒪_W(mL)`
(`MMP.Mori.degreeOn_eq_zero_of_range_eq_singleton`, `MMP.Mori.degreeOn_eq_degreeOver_mul`).

## Main definitions

* `MMP.Mori.pullbackLocalEquation`: the pull-back `u^*ψ ∈ K(V)^×` of a local equation.
* `MMP.Mori.pullbackFrame`: the local frame of `u^* 𝒪_W(B)` pulled back from local equations.

## Main results

* `MMP.Mori.Divisor.IsPullback.isCartier`: the pull-back of a Cartier divisor is Cartier.
* `MMP.Mori.QDivisor.IsPullback.isQCartier`: the pull-back of a `ℚ`-Cartier `ℚ`-divisor is
  `ℚ`-Cartier.
* `MMP.Mori.Divisor.IsPullback.divisorialSheafIso`: `𝒪_V(u^*B) ≅ u^* 𝒪_W(B)`.
* `MMP.Mori.intersectionNumber_pullback_eq_zero`: `(u^*L · C) = 0` when `u(C)` is a point.
* `MMP.Mori.intersectionNumber_pullback_eq_degreeOver_mul`:
  `(u^*L · C) = [k(C) : k(u(C))] · (L · u(C))` when `u(C)` is a curve.

## Implementation notes

"`u(C)` is a point" is `∃ w, Set.range (i ≫ u) = {w}` for the morphism `i : C ⟶ V`, and
"`u(C)` is a curve" is `IsCurve k ((i ≫ u).imageι ≫ s_W)` for the reduced image
`(i ≫ u).image`, the closure of `u(C)` with its reduced structure; `deg(C → u(C))` is
`AlgebraicGeometry.degreeOver (i ≫ u).toImage`. Divisors and their pull-backs live on normal
schemes, so `V` and `W` are normal varieties. The curve `C` is any proper curve over `k` with a
`k`-morphism to `V`; properness of `u` is not needed, since `C` is proper over `k` and `W` is
separated.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Notation 0.4
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
* [Stacks Project, Tag 0AYZ](https://stacks.math.columbia.edu/tag/0AYZ)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace MMP.Mori

section Generator

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] {B : Divisor X} {U : X.Opens}
  {ψ : (RationalFunctions X)ˣ}

/-- If `ψ` is a local equation of `B` on `U`, then `ψ⁻¹` is a section of `𝒪_X(B)` over `U`. -/
def Divisor.IsLocalEquation.invSection (hψ : B.IsLocalEquation U ψ) : Γ(B.divisorialSheaf, U) :=
  ⟨fun Z => ((ψ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) Z.1, fun E hE => Or.inr (by
    rw [PrimeDivisor.valuation_component, PrimeDivisor.ord_inv, hψ E hE])⟩

/-- The section `ψ⁻¹` of `𝒪_X(B)`, read in `𝒦_X(U)`. -/
theorem Divisor.IsLocalEquation.invSection_apply (hψ : B.IsLocalEquation U ψ)
    (Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U}) :
    (show B.divisorialSubmodule U from hψ.invSection).1 Z =
      ((ψ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) Z.1 := rfl

/-- If `ψ` is a local equation of `B` on `U`, then `ψ⁻¹` freely generates `𝒪_X(B)` over every
open `V ⊆ U`. -/
theorem Divisor.IsLocalEquation.isLocalGenerator_invSection (hψ : B.IsLocalEquation U ψ) :
    IsLocalGenerator B.divisorialSheaf U hψ.invSection := by
  intro V hV
  refine ⟨fun c c' h => ?_, fun φ => ?_⟩
  · apply toRationalFunctionsPresheaf_app_injective V
    funext Z
    have := congrFun (congrArg Subtype.val h) Z
    change X.presheaf.germ V _ Z.2 c * _ = X.presheaf.germ V _ Z.2 c' * _ at this
    have hu := (Pi.isUnit_iff.mp (ψ⁻¹).isUnit) Z.1
    exact hu.mul_left_injective this
  · have h0 : (0 : Divisor X).IsDivisorialSection V
        (fun Z => φ.1 Z * (ψ : RationalFunctions X) Z.1) := by
      intro E hE
      have h1 := φ.2 E hE
      have h2 : E.OrdGE (B.coeff E) ((ψ : RationalFunctions X) E.component) :=
        Or.inr (by rw [PrimeDivisor.valuation_component,
          hψ E (hE.mono (Set.inter_subset_inter_right _ hV))])
      refine (h1.mul h2).mono (le_of_eq ?_)
      rw [DivisorWithCoeffs.coeff_zero]
      ring
    obtain ⟨c, hc⟩ := h0.exists_eq
    refine ⟨c, Subtype.ext (funext fun Z => ?_)⟩
    change X.presheaf.germ V _ Z.2 c * ((ψ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) Z.1 =
      φ.1 Z
    have := congrFun hc Z
    rw [toRationalFunctionsPresheaf_app_apply] at this
    rw [this, mul_assoc, ← Pi.mul_apply (f := (ψ : RationalFunctions X)), ← Units.val_mul,
      mul_inv_cancel, Units.val_one, Pi.one_apply, mul_one]

/-- **Pulled-back generators.** If the section `a` freely generates the invertible module `A`
over every open inside `K`, then its image under the unit of `f^* ⊣ f_*` freely generates `f^*A`
over every open inside `f⁻¹ K`: it does not vanish at any point of `f⁻¹ K` [Stacks, Tag 0H78]. -/
theorem isLocalGenerator_pullback_unit {X Y : Scheme.{u}} (b : X ⟶ Y) (A : Y.Modules)
    [Stacks.Ample.IsInvertibleModule Y A] {K : Y.Opens} {a : Γ(A, K)}
    (ha : IsLocalGenerator A K a) :
    IsLocalGenerator ((Scheme.Modules.pullback b).obj A) (b ⁻¹ᵁ K)
      (((Scheme.Modules.pullbackPushforwardAdjunction b).unit.app A).app K a) := by
  intro V hle
  have hpb : Stacks.Ample.IsInvertibleModule X
      ((RingedSpaceModuleAdjunction.modulePullback b.toLRSHom.toShHom).obj A) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback b A
  have hpb' : Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property
      ((RingedSpaceModuleAdjunction.modulePullback b.toLRSHom.toShHom).obj A) :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr hpb
  refine Stacks.SheafOfModules.bijective_smul_of_forall_germ_notMem_maximalIdeal_smul_top
      (X := X.toRingedSpace) _ _ _ hle fun x hx => ?_
  have h1 := Scheme.Modules.germ_notMem_maximalSmul_of_bijective_smul A a ha (b.base x) (hle hx)
  rw [← Stacks.NonvanishingLocusRestrict.mem_maximalSmul_germ_pullbackUnit_iff b A a x
      (hle hx)] at h1
  rwa [Stacks.NonvanishingPullback.mem_maximalSmul_iff] at h1

end Generator

/-! ### Local equations of the pull-back -/

section PullbackEquation

variable {V W : Scheme.{u}} [IsLocallyNoetherian W] [IsNormal W] (u : V ⟶ W) {B : Divisor W}
  (hB : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ B.supp)
  {U : W.Opens} {ψ : (RationalFunctions W)ˣ}

open Classical in
/-- The pull-back `u^*ψ ∈ K(V)^×` of a local equation `ψ` of `B` on `U`: along each component
`V_i` with `u(η_i) ∈ U` it is `u^*_i ψ` (`MMP.Mori.pullbackComponent`), and `1` elsewhere. -/
def pullbackLocalEquation (hψ : B.IsLocalEquation U ψ) : (RationalFunctions V)ˣ :=
  (RationalFunctions.unitsEquiv V).symm fun Z =>
    if hZ : u (componentGenericPoint V Z) ∈ U then pullbackComponent u hB hψ Z hZ else 1

open Classical in
/-- Along a component `V_i` with `u(η_i) ∈ U`, `u^*ψ` is `u^*_i ψ`. -/
theorem pullbackLocalEquation_apply (hψ : B.IsLocalEquation U ψ) (Z : irreducibleComponents V)
    (hZ : u (componentGenericPoint V Z) ∈ U) :
    Units.map (RationalFunctions.component V Z).toMonoidHom (pullbackLocalEquation u hB hψ) =
      pullbackComponent u hB hψ Z hZ := by
  ext
  change (if hZ : u (componentGenericPoint V Z) ∈ U then pullbackComponent u hB hψ Z hZ
    else 1).val = _
  rw [dite_eq_left hZ]

variable [IsLocallyNoetherian V] [IsNormal V]

variable {u hB} in
/-- If `B'` is the pull-back of `B`, then the pull-back `u^*ψ` of a local equation `ψ` of `B` on
`U` is a local equation of `B'` on `u⁻¹ U`. -/
theorem Divisor.IsPullback.isLocalEquation {B' : Divisor V} (h : B.IsPullback u hB B')
    (hψ : B.IsLocalEquation U ψ) : B'.IsLocalEquation (u ⁻¹ᵁ U) (pullbackLocalEquation u hB hψ) := by
  intro E hE
  rw [h U ψ hψ E hE, PrimeDivisor.ord_eq_ordUnit,
    pullbackLocalEquation_apply u hB hψ _ (E.map_componentGenericPoint_mem u hE)]

variable {u hB} in
/-- **The pull-back of a Cartier divisor is Cartier.** -/
theorem Divisor.IsPullback.isCartier {B' : Divisor V} (h : B.IsPullback u hB B')
    (hBc : B.IsCartier) : B'.IsCartier := fun v => by
  obtain ⟨U, hU, ψ, hψ⟩ := hBc (u v)
  exact ⟨u ⁻¹ᵁ U, hU, _, h.isLocalEquation hψ⟩

end PullbackEquation

/-! ### The divisorial sheaf of the pull-back -/

section Comparison

variable {W : Scheme.{u}} [IsLocallyNoetherian W] [IsNormal W] {B : Divisor W}

/-- A chosen open neighbourhood of `w` on which the Cartier divisor `B` has a local equation. -/
def Divisor.IsCartier.chartOpen (hBc : B.IsCartier) (w : W) : W.Opens := (hBc w).choose

/-- A chosen local equation of the Cartier divisor `B` on `hBc.chartOpen w`. -/
def Divisor.IsCartier.chartEquation (hBc : B.IsCartier) (w : W) : (RationalFunctions W)ˣ :=
  (hBc w).choose_spec.2.choose

/-- `w` lies in its chosen chart. -/
theorem Divisor.IsCartier.mem_chartOpen (hBc : B.IsCartier) (w : W) : w ∈ hBc.chartOpen w :=
  (hBc w).choose_spec.1

/-- The chosen local equation is a local equation on the chosen chart. -/
theorem Divisor.IsCartier.isLocalEquation_chartEquation (hBc : B.IsCartier) (w : W) :
    B.IsLocalEquation (hBc.chartOpen w) (hBc.chartEquation w) :=
  (hBc w).choose_spec.2.choose_spec

variable [CompactSpace W] {V : Scheme.{u}} [IsIntegral V] (u : V ⟶ W) (hBc : B.IsCartier)

/-- The local frame of `u^* 𝒪_W(B)` given by the pull-backs of the inverses of the chosen local
equations of the Cartier divisor `B`. -/
def pullbackFrame : LocalFrame ((Scheme.Modules.pullback u).obj B.divisorialSheaf) :=
  haveI := hBc.isInvertibleModule_divisorialSheaf
  { W := fun v => u ⁻¹ᵁ hBc.chartOpen (u v)
    mem := fun v => hBc.mem_chartOpen (u v)
    a := fun v => ((Scheme.Modules.pullbackPushforwardAdjunction u).unit.app
      B.divisorialSheaf).app _ (hBc.isLocalEquation_chartEquation (u v)).invSection
    isLocalGenerator := fun v => isLocalGenerator_pullback_unit u _
      (hBc.isLocalEquation_chartEquation (u v)).isLocalGenerator_invSection
    base := (inferInstance : Nonempty V).some }

/-- The overlap of two charts of `MMP.Mori.pullbackFrame` is the preimage of the overlap of the
charts on `W`. -/
theorem pullbackFrame_W_inf_le (y : V) :
    (pullbackFrame u hBc).W y ⊓ (pullbackFrame u hBc).W (pullbackFrame u hBc).base ≤
      u ⁻¹ᵁ (hBc.chartOpen (u y) ⊓ hBc.chartOpen (u (pullbackFrame u hBc).base)) :=
  fun _ hx => hx

/-- The transition functions of `MMP.Mori.pullbackFrame` are pulled back from `W`: on
`U_y ∩ U_0` the generator `ψ_y⁻¹` is `g · ψ_0⁻¹` for a regular function `g`, and the transition
function is `u^♯ g`. -/
theorem pullbackFrame_transition (y : V) :
    ∃ g : Γ(W, hBc.chartOpen (u y) ⊓ hBc.chartOpen (u (pullbackFrame u hBc).base)),
      (pullbackFrame u hBc).transition y =
        V.presheaf.map (homOfLE (pullbackFrame_W_inf_le u hBc y)).op
          (u.app (hBc.chartOpen (u y) ⊓ hBc.chartOpen (u (pullbackFrame u hBc).base)) g) ∧
      ∀ (Z : irreducibleComponents W)
        (hZ : componentGenericPoint W Z ∈
          hBc.chartOpen (u y) ⊓ hBc.chartOpen (u (pullbackFrame u hBc).base)),
        W.presheaf.germ _ _ hZ g *
          (((hBc.chartEquation (u (pullbackFrame u hBc).base))⁻¹ : (RationalFunctions W)ˣ) :
            RationalFunctions W) Z =
          (((hBc.chartEquation (u y))⁻¹ : (RationalFunctions W)ˣ) : RationalFunctions W) Z := by
  have := hBc.isInvertibleModule_divisorialSheaf
  have hy := hBc.isLocalEquation_chartEquation (u y)
  have h0 := hBc.isLocalEquation_chartEquation (u (pullbackFrame u hBc).base)
  obtain ⟨g, hg⟩ := (h0.isLocalGenerator_invSection
    (hBc.chartOpen (u y) ⊓ hBc.chartOpen (u (pullbackFrame u hBc).base))
    inf_le_right).2 (B.divisorialSheaf.presheaf.map (homOfLE inf_le_left).op hy.invSection)
  refine ⟨g, ?_, fun Z hZ => congrFun (congrArg Subtype.val hg) ⟨Z, hZ⟩⟩
  unfold LocalFrame.transition LocalFrame.coordOf
  apply IsLocalGenerator.coord_eq_of_smul_eq
  have nat : ∀ (U U' : W.Opens) (h : U' ≤ U) (t : Γ(B.divisorialSheaf, U)),
      ((Scheme.Modules.pullback u).obj B.divisorialSheaf).presheaf.map
        (homOfLE ((Opens.map u.base).monotone h)).op
        (((Scheme.Modules.pullbackPushforwardAdjunction u).unit.app B.divisorialSheaf).app U t) =
      ((Scheme.Modules.pullbackPushforwardAdjunction u).unit.app B.divisorialSheaf).app U'
        (B.divisorialSheaf.presheaf.map (homOfLE h).op t) := fun U U' h t =>
    (PresheafOfModules.naturality_apply
      ((Scheme.Modules.pullbackPushforwardAdjunction u).unit.app B.divisorialSheaf).val
      (homOfLE h).op t).symm
  have e0 := nat _ _ (inf_le_right : hBc.chartOpen (u y) ⊓
    hBc.chartOpen (u (pullbackFrame u hBc).base) ≤ _) h0.invSection
  have ey := nat _ _ (inf_le_left : hBc.chartOpen (u y) ⊓
    hBc.chartOpen (u (pullbackFrame u hBc).base) ≤ _) hy.invSection
  have h1 := modules_res_res (L := (Scheme.Modules.pullback u).obj B.divisorialSheaf)
    (pullbackFrame_W_inf_le u hBc y) ((Opens.map u.base).monotone inf_le_right)
    (((Scheme.Modules.pullbackPushforwardAdjunction u).unit.app B.divisorialSheaf).app _
      h0.invSection)
  have h2 := modules_res_res (L := (Scheme.Modules.pullback u).obj B.divisorialSheaf)
    (pullbackFrame_W_inf_le u hBc y) ((Opens.map u.base).monotone inf_le_left)
    (((Scheme.Modules.pullbackPushforwardAdjunction u).unit.app B.divisorialSheaf).app _
      hy.invSection)
  refine ((congrArg (fun t => (V.presheaf.map (homOfLE (pullbackFrame_W_inf_le u hBc y)).op
    (u.app _ g)) • t) h1.symm).trans ?_).trans h2
  refine (congrArg (fun t => (V.presheaf.map (homOfLE (pullbackFrame_W_inf_le u hBc y)).op
    (u.app _ g)) • ((Scheme.Modules.pullback u).obj B.divisorialSheaf).presheaf.map
      (homOfLE (pullbackFrame_W_inf_le u hBc y)).op t) e0).trans ((?_ : _ = _).trans
    (congrArg (fun t => ((Scheme.Modules.pullback u).obj B.divisorialSheaf).presheaf.map
      (homOfLE (pullbackFrame_W_inf_le u hBc y)).op t) ey.symm))
  refine (modules_res_smul (L := (Scheme.Modules.pullback u).obj B.divisorialSheaf)
    (pullbackFrame_W_inf_le u hBc y) (u.app _ g)
    (show Γ((Scheme.Modules.pullback u).obj B.divisorialSheaf, u ⁻¹ᵁ _) from
      ((Scheme.Modules.pullbackPushforwardAdjunction u).unit.app B.divisorialSheaf).app _
        (B.divisorialSheaf.presheaf.map (homOfLE inf_le_right).op h0.invSection))).symm.trans
    (congrArg (fun t => ((Scheme.Modules.pullback u).obj B.divisorialSheaf).presheaf.map
      (homOfLE (pullbackFrame_W_inf_le u hBc y)).op t) ?_)
  rw [← hg]
  exact (Scheme.Modules.Hom.app_smul
    ((Scheme.Modules.pullbackPushforwardAdjunction u).unit.app B.divisorialSheaf) g
    (B.divisorialSheaf.presheaf.map (homOfLE inf_le_right).op h0.invSection)).symm

variable (hB : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ B.supp)

/-- The transition functions of `MMP.Mori.pullbackFrame`, as units of `K(V)`: on the chart
around `y`, the transition function is `u^*ψ_0 / u^*ψ_y` for the local equations `ψ_y`, `ψ_0` of
`B` around `u(y)` and around the image of the base point. -/
theorem pullbackFrame_unit (y : V) :
    (pullbackFrame u hBc).unit y =
      pullbackLocalEquation u hB
          (hBc.isLocalEquation_chartEquation (u (pullbackFrame u hBc).base)) *
        (pullbackLocalEquation u hB (hBc.isLocalEquation_chartEquation (u y)))⁻¹ := by
  obtain ⟨g, hgt, hgZ⟩ := pullbackFrame_transition u hBc y
  have hy := hBc.isLocalEquation_chartEquation (u y)
  have h0 := hBc.isLocalEquation_chartEquation (u (pullbackFrame u hBc).base)
  ext Z
  have hZ : componentGenericPoint V Z ∈
      (pullbackFrame u hBc).W y ⊓ (pullbackFrame u hBc).W (pullbackFrame u hBc).base :=
    ⟨LocalFrame.componentGenericPoint_mem_of_isIntegral Z ⟨y, (pullbackFrame u hBc).mem y⟩,
      (pullbackFrame u hBc).cgp_mem_base Z⟩
  have hZy : u (componentGenericPoint V Z) ∈ hBc.chartOpen (u y) := hZ.1
  have hZ0 : u (componentGenericPoint V Z) ∈ hBc.chartOpen (u (pullbackFrame u hBc).base) := hZ.2
  have hmem : u (componentGenericPoint V Z) ∈
      hBc.chartOpen (u y) ⊓ hBc.chartOpen (u (pullbackFrame u hBc).base) := ⟨hZy, hZ0⟩
  have e0 : (pullbackLocalEquation u hB h0 : RationalFunctions V) Z =
      (pullbackComponent u hB h0 Z hZ0).val :=
    congrArg Units.val (pullbackLocalEquation_apply u hB h0 Z hZ0)
  have ey : (((pullbackLocalEquation u hB hy)⁻¹ : (RationalFunctions V)ˣ) :
      RationalFunctions V) Z = ((pullbackComponent u hB hy Z hZy)⁻¹).val :=
    congrArg Units.val (show Units.map (RationalFunctions.component V Z).toMonoidHom
        (pullbackLocalEquation u hB hy)⁻¹ = (pullbackComponent u hB hy Z hZy)⁻¹ by
      rw [map_inv, pullbackLocalEquation_apply u hB hy Z hZy])
  have hW' := mem_pointComponent (u (componentGenericPoint V Z))
  obtain ⟨a0, ha0⟩ := h0.exists_unit_stalk hZ0 (hB Z) hW'
  obtain ⟨ay, hay⟩ := hy.exists_unit_stalk hZy (hB Z) hW'
  rw [pullbackComponent_eq hB h0 hZ0 hW' a0 ha0] at e0
  rw [pullbackComponent_eq hB hy hZy hW' ay hay] at ey
  set P := pointComponent (u (componentGenericPoint V Z))
  have hP : componentGenericPoint W P ∈
      hBc.chartOpen (u y) ⊓ hBc.chartOpen (u (pullbackFrame u hBc).base) :=
    ((isGenericPoint_componentGenericPoint W P).specializes hW').mem_open (Opens.isOpen _) hmem
  have hay' : (stalkToRationalFunctions W hW').hom (ay⁻¹ : (W.presheaf.stalk _)ˣ).val =
      (((hBc.chartEquation (u y))⁻¹ : (RationalFunctions W)ˣ) : RationalFunctions W) P := by
    have h1 : Units.map (stalkToRationalFunctions W hW').hom.toMonoidHom ay =
        Units.map (RationalFunctions.component W P).toMonoidHom (hBc.chartEquation (u y)) :=
      Units.ext hay
    have h2 := congrArg (fun v => (v⁻¹ : (W.presheaf.stalk (componentGenericPoint W P))ˣ).val) h1
    simp only [← map_inv] at h2
    exact h2
  have hr : (((hBc.chartEquation (u (pullbackFrame u hBc).base))⁻¹ : (RationalFunctions W)ˣ) :
        RationalFunctions W) P *
      ((hBc.chartEquation (u (pullbackFrame u hBc).base) : (RationalFunctions W)ˣ) :
        RationalFunctions W) P = 1 := by
    rw [← Pi.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one, Pi.one_apply]
  have hg' : (stalkToRationalFunctions W hW').hom (W.presheaf.germ _ _ hmem g) =
      W.presheaf.germ _ _ hP g :=
    TopCat.Presheaf.germ_stalkSpecializes_apply W.presheaf hmem _ g
  have key : W.presheaf.germ _ _ hmem g = a0.val * (ay⁻¹).val := by
    apply stalkToRationalFunctions_injective hW'
    rw [hg', map_mul, ha0, hay', mul_comm]
    calc W.presheaf.germ _ _ hP g = W.presheaf.germ _ _ hP g *
          (((hBc.chartEquation (u (pullbackFrame u hBc).base))⁻¹ : (RationalFunctions W)ˣ) :
            RationalFunctions W) P *
          ((hBc.chartEquation (u (pullbackFrame u hBc).base) : (RationalFunctions W)ˣ) :
            RationalFunctions W) P := by rw [mul_assoc, hr, mul_one]
      _ = _ := by rw [hgZ P hP]
  rw [(pullbackFrame u hBc).unit_apply y Z hZ, hgt, TopCat.Presheaf.germ_res_apply,
    ← Scheme.Hom.germ_stalkMap_apply u _ _ hmem, Units.val_mul, Pi.mul_apply, e0, ey, key,
    map_mul]
  rfl

variable [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V]

variable {u hBc hB} in
/-- The divisor of `MMP.Mori.pullbackFrame` is `u^*B - div(u^*ψ_0)`. -/
theorem Divisor.IsPullback.coeff_pullbackFrame_divisor {B' : Divisor V}
    (h : B.IsPullback u hB B') (E : PrimeDivisor V) :
    (pullbackFrame u hBc).divisor.coeff E = B'.coeff E -
      E.ord (pullbackLocalEquation u hB
        (hBc.isLocalEquation_chartEquation (u (pullbackFrame u hBc).base))) := by
  have hE : (E.support ∩ u ⁻¹ᵁ hBc.chartOpen (u E.genericPoint)).Nonempty :=
    (E.genericPoint_mem_iff _).mp (hBc.mem_chartOpen (u E.genericPoint))
  rw [LocalFrame.divisor_coeff, pullbackFrame_unit u hBc hB, PrimeDivisor.ord_mul,
    PrimeDivisor.ord_inv,
    h.isLocalEquation (hBc.isLocalEquation_chartEquation (u E.genericPoint)) E hE]
  ring

variable {u hBc hB} in
/-- **The divisorial sheaf of the pull-back is the pull-back of the divisorial sheaf.** For a
morphism `u : V ⟶ W` of normal schemes, `V` integral and Noetherian, `W` Noetherian, and a
Cartier divisor `B` on `W` whose support does not contain the image of the generic point of `V`,
`𝒪_V(u^*B) ≅ u^* 𝒪_W(B)`. -/
def Divisor.IsPullback.divisorialSheafIso {B' : Divisor V} (h : B.IsPullback u hB B') :
    B'.divisorialSheaf ≅ (Scheme.Modules.pullback u).obj B.divisorialSheaf :=
  Divisor.divisorialSheafMulIso (D' := (pullbackFrame u hBc).divisor)
      (pullbackLocalEquation u hB
        (hBc.isLocalEquation_chartEquation (u (pullbackFrame u hBc).base))) (fun E => by
        rw [h.coeff_pullbackFrame_divisor E]; ring) ≪≫
    (@asIso _ _ _ _ (pullbackFrame u hBc).toDivisorialSheaf
      (pullbackFrame u hBc).isIso_toDivisorialSheaf).symm

end Comparison

/-! ### The pull-back of a `ℚ`-Cartier `ℚ`-divisor is `ℚ`-Cartier -/

section QCartier

variable {V W : Scheme.{u}} [IsLocallyNoetherian V] [IsNormal V] [IsLocallyNoetherian W]
  [IsNormal W] {u : V ⟶ W} {L : QDivisor W}
  {hLB : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ L.supp} {L' : QDivisor V}

/-- If `L'` is the pull-back of the `ℚ`-Cartier `ℚ`-divisor `L`, then `m L'` is the pull-back of
the Cartier divisor `m L` for `m` the Cartier index of `L`. -/
theorem QDivisor.IsPullback.exists_cartierIndex (h : L.IsPullback u hLB L') (hL : L.IsQCartier) :
    ∃ (D : Divisor W) (D' : Divisor V) (_ : D.IsCartier) (hDB : ∀ Z : irreducibleComponents V,
        u (componentGenericPoint V Z) ∉ D.supp),
      Divisor.toQDivisor D = ((L.cartierIndex hL : ℕ) : ℤ) • L ∧
        Divisor.toQDivisor D' = ((L.cartierIndex hL : ℕ) : ℤ) • L' ∧ D.IsPullback u hDB D' := by
  obtain ⟨D, hD, hDc⟩ := QDivisor.isCartierDivisor_cartierIndex_smul hL
  obtain ⟨D', hD', hp⟩ := h _ (QDivisor.cartierIndex_pos hL) D hD hDc
  exact ⟨D, D', hDc, _, hD, hD', hp⟩

/-- **The pull-back of a `ℚ`-Cartier `ℚ`-divisor is `ℚ`-Cartier.** -/
theorem QDivisor.IsPullback.isQCartier (h : L.IsPullback u hLB L') (hL : L.IsQCartier) :
    L'.IsQCartier := by
  obtain ⟨D, D', hDc, hDB, -, hD', hp⟩ := h.exists_cartierIndex hL
  exact ⟨_, by exact_mod_cast (QDivisor.cartierIndex_pos hL).ne', D', hD', hp.isCartier hDc⟩

end QCartier

/-! ### Intersection numbers of pulled-back `ℚ`-Cartier divisors -/

section Projection

variable (k : Type u) [Field k] {V W C : Scheme.{u}} (sV : V ⟶ Spec (.of k))
  (sW : W ⟶ Spec (.of k)) [IsVariety k sV] [IsVariety k sW] [IsLocallyNoetherian V] [IsNormal V]
  [IsLocallyNoetherian W] [IsNormal W] (u : V ⟶ W) (hu : u ≫ sW = sV) (i : C ⟶ V)
  [IsCurve k (i ≫ sV)] [IsProper (i ≫ sV)] {L : QDivisor W} (hL : L.IsQCartier)
  {hLB : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ L.supp} {L' : QDivisor V}
  (h : L.IsPullback u hLB L')

include hu in
/-- **`(u^*L · C) = 0` when `u(C)` is a point.** Let `u : V ⟶ W` be a morphism of normal
varieties over `k`, `L` a `ℚ`-Cartier `ℚ`-divisor on `W` with pull-back `u^*L = L'` defined, and
`i : C ⟶ V` a proper curve (for instance a proper irreducible curve `C ⊆ V`). If `u(C)` is a
point, then `(u^*L · C) = 0`. -/
@[mmp "lem_mmp_foundation_q_cartier_curve_projection"]
theorem intersectionNumber_pullback_eq_zero (hpt : ∃ w : W, Set.range (i ≫ u) = {w}) :
    L'.intersectionNumber k sV i (IsCurve.topologicalKrullDim_eq_one (f := i ≫ sV)).le
      (h.isQCartier hL) = 0 := by
  have := QuasiCompact.compactSpace_of_compactSpace sV
  have := QuasiCompact.compactSpace_of_compactSpace sW
  obtain ⟨D, D', hDc, hDB, -, hD', hp⟩ := h.exists_cartierIndex hL
  have hD'c := hp.isCartier hDc
  have := hDc.isInvertibleModule_divisorialSheaf
  have := hD'c.isInvertibleModule_divisorialSheaf
  have e : (i ≫ u) ≫ sW = i ≫ sV := by rw [Category.assoc, hu]
  have : IsProper ((i ≫ u) ≫ sW) := e ▸ inferInstance
  have : IsCurve k ((i ≫ u) ≫ sW) := e ▸ inferInstance
  rw [QDivisor.intersectionNumber_eq_of_smul k sV i _ _ _ (QDivisor.cartierIndex_pos hL) D' hD'c
    hD', Divisor.degreeOn, degreeOn_eq_of_iso k sV i _ (hp.divisorialSheafIso (hBc := hDc)),
    degreeOn_pullback_eq_degreeOn_comp sV sW u i hu,
    degreeOn_eq_zero_of_range_eq_singleton sW (i ≫ u) _ hpt]
  simp

include hu in
/-- **`(u^*L · C) = deg(C → u(C)) · (L · u(C))` when `u(C)` is a curve.** Let `u : V ⟶ W` be a
morphism of normal varieties over `k`, `L` a `ℚ`-Cartier `ℚ`-divisor on `W` with pull-back
`u^*L = L'` defined, and `i : C ⟶ V` a proper curve (for instance a proper irreducible curve
`C ⊆ V`). If the reduced image `u(C)` of `C` is a curve, then
`(u^*L · C) = [k(C) : k(u(C))] · (L · u(C))`. -/
@[mmp "lem_mmp_foundation_q_cartier_curve_projection"]
theorem intersectionNumber_pullback_eq_degreeOver_mul
    (hcurve : IsCurve k ((i ≫ u).imageι ≫ sW)) :
    haveI : IsProper ((i ≫ u) ≫ sW) := by rw [Category.assoc, hu]; infer_instance
    haveI : IsProper (i ≫ u) := IsProper.of_comp (i ≫ u) sW
    haveI : IsProper ((i ≫ u).imageι ≫ sW) := isProper_imageι_comp (i ≫ u) sW
    L'.intersectionNumber k sV i (IsCurve.topologicalKrullDim_eq_one (f := i ≫ sV)).le
        (h.isQCartier hL) =
      (degreeOver (i ≫ u).toImage : ℚ) *
        L.intersectionNumber k sW (i ≫ u).imageι hcurve.topologicalKrullDim_eq_one.le hL := by
  have := QuasiCompact.compactSpace_of_compactSpace sV
  have := QuasiCompact.compactSpace_of_compactSpace sW
  obtain ⟨D, D', hDc, hDB, hD, hD', hp⟩ := h.exists_cartierIndex hL
  have hD'c := hp.isCartier hDc
  have := hDc.isInvertibleModule_divisorialSheaf
  have := hD'c.isInvertibleModule_divisorialSheaf
  have e : (i ≫ u) ≫ sW = i ≫ sV := by rw [Category.assoc, hu]
  have : IsProper ((i ≫ u) ≫ sW) := e ▸ inferInstance
  have : IsCurve k ((i ≫ u) ≫ sW) := e ▸ inferInstance
  have : IsProper (i ≫ u) := IsProper.of_comp (i ≫ u) sW
  have : IsProper ((i ≫ u).imageι ≫ sW) := isProper_imageι_comp (i ≫ u) sW
  have hnc : ¬ ∃ w : W, Set.range (i ≫ u) = {w} := by
    intro hpt
    have := subsingleton_image sW (i ≫ u) hpt
    have h1 := hcurve.topologicalKrullDim_eq_one
    have h0 : topologicalKrullDim (i ≫ u).image ≤ 0 :=
      topologicalKrullDim_zero_of_discreteTopology _
    rw [h1] at h0
    norm_num at h0
  rw [QDivisor.intersectionNumber_eq_of_smul k sV i _ _ _ (QDivisor.cartierIndex_pos hL) D' hD'c
    hD', QDivisor.intersectionNumber_eq_of_smul k sW (i ≫ u).imageι _ _ _
    (QDivisor.cartierIndex_pos hL) D hDc hD, Divisor.degreeOn,
    degreeOn_eq_of_iso k sV i _ (hp.divisorialSheafIso (hBc := hDc)),
    degreeOn_pullback_eq_degreeOn_comp sV sW u i hu,
    degreeOn_eq_degreeOver_mul sW (i ≫ u) _ hnc, Divisor.degreeOn]
  push_cast
  ring

end Projection

end MMP.Mori
