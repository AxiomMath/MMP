module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
public import MMP.AlgebraicGeometry.MMP.Fourfold.Singularities
public import MMP.AlgebraicGeometry.Divisor.Pullback
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.Intersection.PairingSeparation
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.Divisor.DivisorialPullback
import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleContractedCurve
import MMP.AlgebraicGeometry.Positivity.Kleiman.RelativeCartier
import MMP.AlgebraicGeometry.Morphisms.VarietyFibreDimension
import MMP.AlgebraicGeometry.Singularities.KltDiscrepancyBasics
import MMP.AlgebraicGeometry.MMP.Contraction.RelativeLineBundleDescent
import MMP.AlgebraicGeometry.Divisor.SmoothRDivisors
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
public import MMP.AlgebraicGeometry.Chow.FieldSituation
public import MMP.AlgebraicGeometry.Dimension.HeightCoheight

/-!
# Vertical prime divisors of a rank-one threefold Mori curve fibration

Let `r : Y ⟶ V` be a contraction (`MMP.Fourfold.IsContraction`: projective, surjective, between
normal varieties, with `r_* 𝒪_Y = 𝒪_V`) of a `ℚ`-factorial projective threefold onto a projective
surface, with `ρ(Y/V) = 1`, and suppose that some klt boundary `Γ` makes `-(K_Y + Γ)` relatively
ample. Then every fibre of `r` has pure dimension one, `V` is `ℚ`-factorial, and every vertical
prime divisor `E ⊆ Y` maps onto a prime divisor `C ⊆ V` with `E = a • r^*C` for some rational
`a > 0`; in particular `E` is the only prime divisor of `Y` lying over `C`.

The proof descends a Cartier multiple of `E`, which is trivial on the unique relative ray, along
the klt-negative contraction `r` (the contraction theorem), so that `𝒪_Y(mE) ≅ r^*M`; the zero set
of the descended section is a curve on the normal surface `V`.

## Main results

* `MMP.Fourfold.IsContraction.exists_eq_smul_pullback_of_relativePicardNumberN1_eq_one`.

## Implementation notes

The fibre over `v` is taken as the topological fibre `r ⁻¹' {v}`, which is homeomorphic to the
scheme-theoretic fibre. A prime divisor `E` is *vertical* when `r(E) ≠ V`; since `r` is proper
this is the same as `r(E)` not being dense. The pull-back `MMP.Mori.QDivisor.pullback` takes as
arguments that `C` is `ℚ`-Cartier and that the generic point of `Y` does not map into `C`; the
conclusion asserts both.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Theorem 3.7(4)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MMP.Mori

namespace MMP.Fourfold

open Opposite

universe u

section Support

variable {X : Scheme.{u}}

/-- An irreducible subset of the support of a divisor lies in the support of one of its prime
divisors. -/
private theorem exists_subset_support_of_isIrreducible {R : Type*} [Zero R]
    (D : DivisorWithCoeffs R X) {s : Set X} (hs : IsIrreducible s) (hsD : s ⊆ D.supp) :
    ∃ E, D.coeff E ≠ 0 ∧ s ⊆ E.support := by
  classical
  obtain ⟨z, hz, hsz⟩ := (isIrreducible_iff_sUnion_isClosed.mp hs)
    (D.support.image fun E => (E.support : Set X))
    (by
      intro z hz
      obtain ⟨E, -, rfl⟩ := Finset.mem_image.mp hz
      exact E.idealSheaf.support.isClosed)
    (by
      intro x hx
      obtain ⟨E, hE, hxE⟩ := DivisorWithCoeffs.mem_supp_iff.mp (hsD hx)
      exact ⟨E.support, Finset.mem_image.mpr ⟨E, Finsupp.mem_support_iff.mpr hE, rfl⟩, hxE⟩)
  obtain ⟨E, hE, rfl⟩ := Finset.mem_image.mp hz
  exact ⟨E, Finsupp.mem_support_iff.mp hE, hsz⟩

variable [IsLocallyNoetherian X] [IsNormal X]

/-- A divisor whose support is irreducible has a single prime component. -/
private theorem eq_single_of_isIrreducible_supp {R : Type*} [Zero R] (D : DivisorWithCoeffs R X)
    (hD : IsIrreducible (D.supp : Set X)) :
    ∃ C : MMP.Mori.PrimeDivisor X, (D.supp : Set X) = C.support ∧ D = Finsupp.single C (D C) := by
  obtain ⟨C, hC, hsub⟩ := exists_subset_support_of_isIrreducible D hD subset_rfl
  have hall : ∀ P, D.coeff P ≠ 0 → P = C := fun P hP =>
    (MMP.Threefold.Mori.primeDivisor_eq_of_genericPoint_mem_support C P
      (hsub (DivisorWithCoeffs.support_subset_supp hP
        (MMP.Flips.primeDivisor_genericPoint_mem_support P)))).symm
  refine ⟨C, subset_antisymm hsub (DivisorWithCoeffs.support_subset_supp hC), ?_⟩
  refine Finsupp.ext fun P => ?_
  by_cases hP : P = C
  · subst hP; simp
  · classical
    rw [Finsupp.single_apply, if_neg (Ne.symm hP)]
    by_contra h
    exact hP (hall P h)

end Support

section Pullback

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y]
  [IsNormal Y] {p : X ⟶ Y}

/-- The pull-back of a Cartier divisor `G` has coefficient zero along every prime divisor meeting
`p⁻¹(Y ∖ Supp G)`. -/
private theorem coeff_eq_zero_of_isPullback {G : Divisor Y}
    {hB : ∀ Z : irreducibleComponents X, p (componentGenericPoint X Z) ∉ G.supp} {G' : Divisor X}
    (h : G.IsPullback p hB G') {x : X} (hx : p x ∉ G.supp) (F : MMP.Mori.PrimeDivisor X)
    (hF : x ∈ F.support) : G'.coeff F = 0 := by
  let U : Y.Opens := ⟨(G.supp : Set Y)ᶜ, G.isClosed_supp.isOpen_compl⟩
  have hloc : G.IsLocalEquation U 1 := by
    intro E ⟨y, hyE, hyU⟩
    rw [PrimeDivisor.ord_one]
    by_contra hne
    exact hyU (DivisorWithCoeffs.support_subset_supp hne hyE)
  have hF' : (F.support ∩ p ⁻¹ᵁ U).Nonempty := ⟨x, hF, hx⟩
  rw [h U 1 hloc F hF', pullbackComponent_eq hB hloc _ (mem_pointComponent _) 1 (by simp),
    map_one, PrimeDivisor.ordUnit_one]

variable [IsIntegral X] [IsIntegral Y] [CompactSpace X] [CompactSpace Y] [IsDominant p]

omit [CompactSpace X] [CompactSpace Y] in
/-- A dominant morphism of integral schemes maps the generic point of `X` into every nonempty
open of `Y`. -/
private theorem map_componentGenericPoint_mem (Z : irreducibleComponents X) {U : Y.Opens}
    (hU : (U : Set Y).Nonempty) : p (componentGenericPoint X Z) ∈ U := by
  rw [componentGenericPoint_eq_genericPoint, map_genericPoint_of_isDominant]
  exact (genericPoint_spec Y).mem_open_set_iff U.isOpen |>.mpr (by simpa using hU)

omit [CompactSpace X] [CompactSpace Y] in
/-- For `p` dominant, `𝒪_{Y, p(η_X)}` is the function field of `Y`, so the stalk map at the
generic point of `X` is injective. -/
private theorem injective_stalkMap_componentGenericPoint (Z : irreducibleComponents X) :
    Function.Injective (p.stalkMap (componentGenericPoint X Z)).hom := by
  have hF : IsField (Y.presheaf.stalk (p (componentGenericPoint X Z))) := by
    have := RationalFunctions.isField_stalk Y (pointComponent (genericPoint Y))
    rwa [componentGenericPoint_eq_genericPoint, ← map_genericPoint_of_isDominant p,
      ← componentGenericPoint_eq_genericPoint Z] at this
  letI := hF.toField
  exact (p.stalkMap (componentGenericPoint X Z)).hom.injective

variable (hp : ∀ U : Y.Opens, IsIso (p.app U))

include hp

/-- **Descent of regular functions.** If `p_* 𝒪_X = 𝒪_Y`, a rational function on `X` with no
poles on `p⁻¹U` is the pull-back of a regular function on `U`. -/
private theorem exists_section_of_ord_nonneg (U : Y.Opens) (Z : irreducibleComponents X)
    (hZ : p (componentGenericPoint X Z) ∈ U) (χ : (RationalFunctions X)ˣ)
    (hχ : ∀ F : MMP.Mori.PrimeDivisor X, (F.support ∩ p ⁻¹ᵁ U).Nonempty → 0 ≤ F.ord χ) :
    ∃ u : Γ(Y, U),
      (p.stalkMap _).hom (Y.presheaf.germ U _ hZ u) = (χ : RationalFunctions X) Z := by
  have hφ : (0 : Divisor X).IsDivisorialSection (p ⁻¹ᵁ U)
      fun Z' => (χ : RationalFunctions X) Z'.1 :=
    isDivisorialSection_of_unit χ fun P hP => by simpa using hχ P hP
  obtain ⟨s, hs⟩ := hφ.exists_eq
  refine ⟨inv (p.app U) s, ?_⟩
  rw [Scheme.Hom.germ_stalkMap_apply, IsIso.inv_hom_id_apply]
  exact congrFun hs ⟨Z, hZ⟩

/-- If `p_* 𝒪_X = 𝒪_Y`, every rational function `ψ` on `X` with `p^* M + div ψ` effective is the
pull-back of a rational function on `Y`. -/
private theorem exists_pullbackRationalFunction_eq_of_isPullback {M : Divisor Y}
    (hMc : M.IsCartier)
    {hB : ∀ Z : irreducibleComponents X, p (componentGenericPoint X Z) ∉ M.supp} {M' : Divisor X}
    (h : M.IsPullback p hB M') (ψ : (RationalFunctions X)ˣ)
    (hψ : ∀ F : MMP.Mori.PrimeDivisor X, 0 ≤ M'.coeff F + F.ord ψ) :
    ∃ (φ : (RationalFunctions Y)ˣ) (hφ : ∀ Z : irreducibleComponents X,
      p (componentGenericPoint X Z) ∉ (principalDivisor φ).supp),
      pullbackRationalFunction p φ hφ = ψ := by
  have := subsingleton_irreducibleComponents (X := X)
  have := subsingleton_irreducibleComponents (X := Y)
  set Z : irreducibleComponents X := pointComponent (genericPoint X)
  let U : Y.Opens := ⟨(M.supp : Set Y)ᶜ, M.isClosed_supp.isOpen_compl⟩
  have hZU : p (componentGenericPoint X Z) ∈ U := hB Z
  obtain ⟨u, hu⟩ := exists_section_of_ord_nonneg hp U Z hZU ψ fun F ⟨x, hxF, hxU⟩ => by
    have := hψ F
    rwa [coeff_eq_zero_of_isPullback h hxU F hxF, zero_add] at this
  set b := Y.presheaf.germ U _ hZU u
  set W := pointComponent (p (componentGenericPoint X Z))
  have hW : p (componentGenericPoint X Z) ∈ W.1 := mem_pointComponent _
  have hb0 : (stalkToRationalFunctions Y hW).hom b ≠ 0 := by
    intro h0
    have hb : b = 0 := stalkToRationalFunctions_injective hW (h0.trans (map_zero _).symm)
    have := (ψ.isUnit.map (Pi.evalRingHom _ Z)).ne_zero
    rw [Pi.evalRingHom_apply, ← hu, hb, map_zero] at this
    exact this rfl
  let sY : RationalFunctions Y := fun W' => (stalkToRationalFunctions Y
    (mem_irreducibleComponent_of_irreducibleSpace W' (p (componentGenericPoint X Z)))).hom b
  have hsYW : sY W = (stalkToRationalFunctions Y hW).hom b := rfl
  have hsY : IsUnit sY := by
    refine Pi.isUnit_iff.mpr fun W' => ?_
    obtain rfl : W = W' := Subsingleton.elim _ _
    exact isUnit_of_ne_zero_stalk W hb0
  set φ := hsY.unit
  have hφ : (φ : RationalFunctions Y) = sY := hsY.unit_spec
  refine ⟨φ, map_componentGenericPoint_notMem_supp_of_isDominant p _, ?_⟩
  ext Z'
  obtain rfl : Z = Z' := Subsingleton.elim _ _
  obtain ⟨a', ha'⟩ := (Divisor.isLocalEquation_principalDivisor φ ⊤).exists_unit_stalk trivial
    (map_componentGenericPoint_notMem_supp_of_isDominant p _ Z) hW
  have haa : (a' : Y.presheaf.stalk _) = b :=
    stalkToRationalFunctions_injective hW (by rw [ha', hφ, hsYW])
  have hval : ((pullbackRationalFunction p φ
      (map_componentGenericPoint_notMem_supp_of_isDominant p _) : RationalFunctions X) Z) =
      (pullbackComponent p (map_componentGenericPoint_notMem_supp_of_isDominant p _)
        (Divisor.isLocalEquation_principalDivisor φ ⊤) Z trivial).val := rfl
  rw [hval]
  refine (congrArg Units.val (pullbackComponent_eq _ _ _ hW a' ha')).trans ?_
  change (p.stalkMap (componentGenericPoint X Z)).hom
    (a' : Y.presheaf.stalk (p (componentGenericPoint X Z))) = _
  rw [haa, hu]

/-- If `p_* 𝒪_X = 𝒪_Y`, a Cartier divisor whose pull-back is effective is effective. -/
private theorem coeff_nonneg_of_isPullback {G : Divisor Y} (hGc : G.IsCartier)
    {hB : ∀ Z : irreducibleComponents X, p (componentGenericPoint X Z) ∉ G.supp} {G' : Divisor X}
    (h : G.IsPullback p hB G') (hG' : 0 ≤ G') (E : MMP.Mori.PrimeDivisor Y) : 0 ≤ G.coeff E := by
  have := subsingleton_irreducibleComponents (X := Y)
  obtain ⟨U, hU, g, hg⟩ := hGc E.genericPoint
  set Z : irreducibleComponents X := pointComponent (genericPoint X)
  have hZU : p (componentGenericPoint X Z) ∈ U := map_componentGenericPoint_mem Z ⟨_, hU⟩
  have hg' := h.isLocalEquation hg
  obtain ⟨u, hu⟩ := exists_section_of_ord_nonneg hp U Z hZU (pullbackLocalEquation p hB hg)
    fun F hF => by rw [← hg' F hF]; exact hG' F
  have hpc := pullbackLocalEquation_apply p hB hg Z hZU
  have hspec := (hg.exists_unit_stalk hZU (hB Z) (mem_pointComponent _)).choose_spec
  have hua : Y.presheaf.germ U _ hZU u =
      (hg.exists_unit_stalk hZU (hB Z) (mem_pointComponent _)).choose := by
    apply injective_stalkMap_componentGenericPoint Z
    rw [hu]
    exact congrArg Units.val hpc
  have hEU : (E.support ∩ U).Nonempty := (E.genericPoint_mem_iff U).mp hU
  have hord := ((Divisor.structureSheafToDivisorialSheaf (le_refl (0 : Divisor Y))).app U u).2 E
    hEU
  rw [Divisor.coe_structureSheafToDivisorialSheaf_app] at hord
  have hall : ∀ (W' : irreducibleComponents Y) (hW' : componentGenericPoint Y W' ∈ U),
      Y.presheaf.germ U _ hW' u = (g : RationalFunctions Y) W' := by
    intro W' hW'
    obtain rfl : pointComponent (p (componentGenericPoint X Z)) = W' := Subsingleton.elim _ _
    rw [← hspec, ← hua, stalkToRationalFunctions, TopCat.Presheaf.germ_stalkSpecializes_apply]
  have hcomp : (toRationalFunctionsPresheaf Y).app (op U) u
      ⟨E.component, E.componentGenericPoint_mem_of_nonempty hEU⟩ =
      (g : RationalFunctions Y) E.component := by
    rw [toRationalFunctionsPresheaf_app_apply]
    exact hall _ _
  rw [hcomp] at hord
  rw [hg E hEU]
  rcases hord with h0 | h1
  · exact absurd h0 ((g.isUnit.map (Pi.evalRingHom _ E.component)).ne_zero)
  · rw [E.valuation_component, DivisorWithCoeffs.coeff_zero, neg_zero,
      WithZero.exp_le_exp] at h1
    exact h1

omit [IsIntegral X] [CompactSpace X] [IsDominant p] hp in
/-- On an integral normal Noetherian scheme every invertible sheaf is `𝒪_Y(D)` for a Cartier
divisor `D`. -/
private theorem exists_isCartier_divisorialSheaf_iso (L : Y.Modules)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L] :
    ∃ D : Divisor Y, D.IsCartier ∧ Nonempty (D.divisorialSheaf ≅ L) := by
  have := Stacks.SheafOfModules.isInvertible_of_tensorInvertible (X := Y.toRingedSpace) L
  have : ∀ z : Y.toRingedSpace.carrier,
      IsLocalRing (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk Y.toRingedSpace z) :=
    Y.isLocalRing
  choose W hW a ha using fun y : Y =>
    Stacks.SheafOfModules.exists_bijective_smul_of_isInvertible (X := Y.toRingedSpace) L y
  obtain ⟨y₀⟩ : Nonempty Y := inferInstance
  let F : LocalFrame L :=
    { W := W, mem := hW, a := a, isLocalGenerator := ha, base := y₀ }
  exact ⟨F.divisor, fun y => ⟨F.W y, F.mem y, _, F.isLocalEquation_divisor y⟩,
    ⟨(@asIso _ _ _ _ F.toDivisorialSheaf F.isIso_toDivisorialSheaf).symm⟩⟩

/-- **Descent of an effective divisor.** If `p_* 𝒪_X = 𝒪_Y` and the sheaf of an effective
Cartier divisor `D'` on `X` is the pull-back of an invertible sheaf on `Y`, then `D'` is the
pull-back of an effective Cartier divisor on `Y`. -/
private theorem exists_isPullback_of_iso_pullback {D' : Divisor X} (hD' : 0 ≤ D')
    (M : Y.Modules) [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 M]
    (e : D'.divisorialSheaf ≅ (Scheme.Modules.pullback p).obj M) :
    ∃ (G : Divisor Y) (_ : G.IsCartier)
      (hB : ∀ Z : irreducibleComponents X, p (componentGenericPoint X Z) ∉ G.supp),
      0 ≤ G ∧ G.IsPullback p hB D' := by
  obtain ⟨D, hD, ⟨eD⟩⟩ := exists_isCartier_divisorialSheaf_iso M
  have hBD := map_componentGenericPoint_notMem_supp_of_isDominant p D
  obtain ⟨eP⟩ := Divisor.nonempty_divisorialSheaf_pullback_iso hD p hBD
  have hlin := MMP.Flips.linearlyEquivalent_of_divisorialSheaf_iso
    (e ≪≫ (Scheme.Modules.pullback p).mapIso eD.symm ≪≫ eP.symm)
  obtain ⟨φ, hφ⟩ := hlin
  have hDp := Divisor.isPullback_pullback hD hBD
  have hD'eq : D' = D.pullback hD hBD + principalDivisor φ := by
    rw [← hφ]; abel
  obtain ⟨ψ, hψ, hψφ⟩ := exists_pullbackRationalFunction_eq_of_isPullback hp hD hDp φ
    fun F => by
      have : 0 ≤ DivisorWithCoeffs.coeff (D.pullback hD hBD + principalDivisor φ) F :=
        hD'eq ▸ hD' F
      rwa [DivisorWithCoeffs.coeff_add, coeff_principalDivisor] at this
  have hGc := hD.add (Divisor.isCartier_principalDivisor ψ)
  have hG := Divisor.IsPullback.add hD (Divisor.isCartier_principalDivisor ψ)
    (map_componentGenericPoint_notMem_supp_of_isDominant p _) hDp
    (Divisor.isPullback_principalDivisor ψ hψ)
  rw [hψφ, ← hD'eq] at hG
  exact ⟨_, hGc, _, fun E => coeff_nonneg_of_isPullback hp hGc hG hD' E, hG⟩

omit hp in
/-- If a Cartier divisor `G` is effective near `p x` and its pull-back has coefficient zero along
every prime divisor through `x`, then `G` has coefficient zero along every prime divisor through
`p x`. -/
private theorem coeff_eq_zero_of_isPullback_of_nonnegOn {G : Divisor Y} (hGc : G.IsCartier)
    {hB : ∀ Z : irreducibleComponents X, p (componentGenericPoint X Z) ∉ G.supp} {G' : Divisor X}
    (h : G.IsPullback p hB G') {x : X} {W : Y.Opens} (hxW : p x ∈ W)
    (hG : ∀ P : MMP.Mori.PrimeDivisor Y, (P.support ∩ W).Nonempty → 0 ≤ G.coeff P)
    (hx : ∀ F : MMP.Mori.PrimeDivisor X, x ∈ F.support → G'.coeff F = 0)
    (E : MMP.Mori.PrimeDivisor Y) (hE : p x ∈ E.support) : G.coeff E = 0 := by
  have := subsingleton_irreducibleComponents (X := Y)
  obtain ⟨U₀, hyU₀, g, hg₀⟩ := hGc (p x)
  set U : Y.Opens := U₀ ⊓ W
  have hyU : p x ∈ U := ⟨hyU₀, hxW⟩
  have hg : G.IsLocalEquation U g := hg₀.mono inf_le_left
  set Z : irreducibleComponents X := pointComponent (genericPoint X)
  have hxZ : x ∈ Z.1 := mem_irreducibleComponent_of_irreducibleSpace Z x
  have hZU : p (componentGenericPoint X Z) ∈ U := map_componentGenericPoint_mem Z ⟨_, hyU⟩
  have hyE : p x ∈ E.component.1 := mem_irreducibleComponent_of_irreducibleSpace _ _
  -- `g` is regular at `p x`
  have hsec : (0 : Divisor Y).IsDivisorialSection U fun W => (g : RationalFunctions Y) W.1 :=
    isDivisorialSection_of_unit g fun P hP => by
      rw [DivisorWithCoeffs.coeff_zero, zero_add, ← hg P hP]
      exact hG P (hP.mono (Set.inter_subset_inter_right _ inf_le_right))
  obtain ⟨r, hr0⟩ := hsec.exists_stalk_eq hyU (mem_irreducibleComponent_of_irreducibleSpace
    (pointComponent (p (componentGenericPoint X Z))) (p x))
  have hr : ∀ (W' : irreducibleComponents Y) (hW' : p x ∈ W'.1),
      (stalkToRationalFunctions Y hW').hom r = (g : RationalFunctions Y) W' := by
    intro W' hW'
    obtain rfl : pointComponent (p (componentGenericPoint X Z)) = W' := Subsingleton.elim _ _
    exact hr0
  -- `p^* g` is a unit at `x`
  have hg' := h.isLocalEquation hg
  obtain ⟨c, hc⟩ := exists_unit_stalk_of_forall_ord_eq_zero hxZ (pullbackLocalEquation p hB hg)
    fun F hF => by rw [← hg' F ⟨x, hF, hyU⟩]; exact hx F hF
  have hsp : componentGenericPoint X Z ⤳ x :=
    (isGenericPoint_componentGenericPoint X Z).specializes hxZ
  have hsp' : p (componentGenericPoint X Z) ⤳ p x := p.base.hom.map_specializes hsp
  have hspec := (hg.exists_unit_stalk hZU (hB Z) (mem_pointComponent _)).choose_spec
  have hra : (Y.presheaf.stalkSpecializes hsp').hom r =
      (hg.exists_unit_stalk hZU (hB Z) (mem_pointComponent _)).choose := by
    apply stalkToRationalFunctions_injective (mem_pointComponent _)
    rw [hspec]
    change (Y.presheaf.stalkSpecializes hsp' ≫ Y.presheaf.stalkSpecializes _).hom r = _
    rw [TopCat.Presheaf.stalkSpecializes_comp]
    exact hr _ (mem_irreducibleComponent_of_irreducibleSpace _ _)
  have hrc : (p.stalkMap x).hom r = c := by
    apply stalkToRationalFunctions_injective hxZ
    rw [hc]
    have hpc := congrArg Units.val (pullbackLocalEquation_apply p hB hg Z hZU)
    change _ = ((Units.map (RationalFunctions.component X Z).toMonoidHom
      (pullbackLocalEquation p hB hg) : (X.presheaf.stalk (componentGenericPoint X Z))ˣ) :
        X.presheaf.stalk (componentGenericPoint X Z))
    rw [hpc]
    change (X.presheaf.stalkSpecializes hsp).hom _ = (p.stalkMap _).hom _
    rw [← hra, Scheme.Hom.stalkSpecializes_stalkMap_apply]
  have hru : IsUnit r := isUnit_of_map_unit (p.stalkMap x).hom r (hrc ▸ c.isUnit)
  -- hence `g` has order zero along every prime divisor through `p x`
  have hEU : (E.support ∩ U).Nonempty := ⟨_, hE, hyU⟩
  rw [hg E hEU, PrimeDivisor.ord_eq_ordUnit]
  have hspE : E.genericPoint ⤳ p x := by
    rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact hE
  refine E.ordUnit_eq_zero_of_isUnit (a := (Y.presheaf.stalkSpecializes hspE).hom r)
    (hru.map _) ?_
  rw [E.toComponent_stalkSpecializes hspE hyE, hr]
  rfl

omit hp in
/-- For an effective Cartier divisor `G` with pull-back `G'`, `p⁻¹(Supp G) = Supp G'`. -/
private theorem preimage_supp_eq_of_isPullback {G : Divisor Y} (hGc : G.IsCartier) (hG : 0 ≤ G)
    {hB : ∀ Z : irreducibleComponents X, p (componentGenericPoint X Z) ∉ G.supp} {G' : Divisor X}
    (h : G.IsPullback p hB G') : p ⁻¹' (G.supp : Set Y) = G'.supp := by
  ext x
  constructor
  · intro hx
    obtain ⟨E, hE, hxE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hx
    by_contra hx'
    refine hE (coeff_eq_zero_of_isPullback_of_nonnegOn hGc h (W := ⊤) trivial
      (fun P _ => hG P) (fun F hF => ?_) E hxE)
    by_contra hne
    exact hx' (DivisorWithCoeffs.mem_supp_iff.mpr ⟨F, hne, hF⟩)
  · intro hx
    by_contra hx'
    obtain ⟨F, hF, hxF⟩ := DivisorWithCoeffs.mem_supp_iff.mp hx
    exact hF (coeff_eq_zero_of_isPullback h hx' F hxF)

omit hp in
/-- Over every prime divisor `C` of `Y` lies a prime divisor of `X`, when `p` is surjective: a
component through a point over `η_C` of the support of the pull-back of a rational function
with a simple zero along `C`. -/
private theorem exists_primeDivisor_subset_preimage (hs : Function.Surjective p)
    (C : MMP.Mori.PrimeDivisor Y) :
    ∃ F : MMP.Mori.PrimeDivisor X, (F.support : Set X) ⊆ p ⁻¹' C.support := by
  classical
  obtain ⟨φ, hφ⟩ := MMP.Flips.exists_primeDivisor_ord_eq C 1
  set D := principalDivisor φ
  have hDc : D.IsCartier := Divisor.isCartier_principalDivisor φ
  have hB := map_componentGenericPoint_notMem_supp_of_isDominant p D
  have hP := Divisor.isPullback_principalDivisor φ hB
  have hDC : D.coeff C = 1 := by rw [coeff_principalDivisor, hφ]
  set T : Divisor Y := D - Finsupp.single C (D.coeff C)
  let W : Y.Opens := ⟨(T.supp : Set Y)ᶜ, T.isClosed_supp.isOpen_compl⟩
  have hTC : T.coeff C = 0 := by
    simp [T, DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_single_self]
  have hηW : C.genericPoint ∈ W := by
    intro h
    obtain ⟨P, hP, hCP⟩ := DivisorWithCoeffs.mem_supp_iff.mp h
    rw [MMP.Threefold.Mori.primeDivisor_eq_of_genericPoint_mem_support P C hCP] at hP
    exact hP hTC
  have hG : ∀ P : MMP.Mori.PrimeDivisor Y, (P.support ∩ W).Nonempty → 0 ≤ D.coeff P := by
    intro P ⟨x, hxP, hxW⟩
    have hTP : T.coeff P = 0 := by
      by_contra h
      exact hxW (DivisorWithCoeffs.support_subset_supp h hxP)
    have : D.coeff P = T.coeff P +
        DivisorWithCoeffs.coeff (Finsupp.single C (D.coeff C) : Divisor Y) P := by
      rw [← DivisorWithCoeffs.coeff_add, sub_add_cancel]
    rw [this, hTP, zero_add]
    by_cases hPC : P = C
    · subst hPC; rw [DivisorWithCoeffs.coeff_single_self, hDC]; exact zero_le_one
    · rw [DivisorWithCoeffs.coeff_single_of_ne (Ne.symm hPC)]
  obtain ⟨y, hy⟩ := hs C.genericPoint
  obtain ⟨F, hF, hyF⟩ : ∃ F : MMP.Mori.PrimeDivisor X,
      (principalDivisor (pullbackRationalFunction p φ hB)).coeff F ≠ 0 ∧ y ∈ F.support := by
    by_contra hnone
    push Not at hnone
    have := coeff_eq_zero_of_isPullback_of_nonnegOn hDc hP (x := y) (W := W)
      (by rw [hy]; exact hηW) hG (fun F hF => by by_contra h; exact hnone F h hF)
      C (by rw [hy]; exact MMP.Flips.primeDivisor_genericPoint_mem_support C)
    rw [hDC] at this
    exact one_ne_zero this
  have hFsub : (F.support : Set X) ⊆ p ⁻¹' D.supp := by
    intro x hx
    by_contra hx'
    exact hF (coeff_eq_zero_of_isPullback hP hx' F hx)
  have hirr : IsIrreducible (p '' (F.support : Set X)) := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact isIrreducible_singleton.closure.image _ p.continuous.continuousOn
  obtain ⟨P, -, hPsub⟩ := exists_subset_support_of_isIrreducible D hirr
    (Set.image_subset_iff.mpr hFsub)
  have hPC : P = C := MMP.Threefold.Mori.primeDivisor_eq_of_genericPoint_mem_support P C
    (hy ▸ hPsub ⟨y, hyF, rfl⟩)
  subst hPC
  exact ⟨F, Set.image_subset_iff.mp hPsub⟩

end Pullback

section PicardNumberOne

/-- **Numerical triviality in relative Picard number one.** If `ρ(X/Z) = 1` and an invertible
sheaf `A` has nonzero degree on a contracted curve `γ₀` on which `L` has degree zero, then `L`
has degree zero on every contracted curve: modulo `f^* N¹(Z)`, which is zero on contracted
curves, the class of `L` is a multiple `c` of that of `A`, and `c = 0` on `γ₀`. -/
private theorem degree_eq_zero_of_relativePicardNumberN1_eq_one {k : Type} [Field k]
    {X Z : Scheme.{0}} [IsIntegral X] {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
    [IsSeparated sZ] [LocallyOfFiniteType sZ] {f : X ⟶ Z} (hf : f ≫ sZ = sX)
    (hρ : relativePicardNumberN1 sX f = 1) (A L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 A]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    {γ₀ : ProperCurve sX} (hγ₀ : γ₀.IsContractedBy f)
    (hA0 : γ₀.degree k A ≠ 0) (hL0 : γ₀.degree k L = 0)
    (γ : ProperCurve sX) (hγ : γ.IsContractedBy f) : γ.degree k L = 0 := by
  obtain ⟨EA, ⟨eA⟩⟩ := exists_nonempty_iso_cartierDivisor_sheaf A
  obtain ⟨EL, ⟨eL⟩⟩ := exists_nonempty_iso_cartierDivisor_sheaf L
  have hiso : ∀ (γ : ProperCurve sX) {M M' : X.Modules}
      [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]
      [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M'] (e : M ≅ M'),
      γ.degree k M = γ.degree k M' := fun γ M M' _ _ e =>
    degreeOn_eq_of_iso k sX γ.ι γ.dim_le e
  let ℓ : ProperCurve sX → (NumericalDivisorClasses sX →ₗ[ℝ] ℝ) := fun γ =>
    (numericalPairing sX).flip (OneCycle.numericalClass sX (γ.cycle ℝ))
  have key : ∀ (E : X.CartierDivisor) (γ : ProperCurve sX),
      ℓ γ (numericalDivisorClass sX (KCartierDivisor.ofCartier ℝ E)) =
        (γ.degree k (MMP.CartierDivisor.sheaf E) : ℝ) := by
    intro E γ
    simp only [ℓ, LinearMap.flip_apply]
    rw [numericalPairing_apply, OneCycle.intersectionNumber_ofCartier, OneCycle.cartierDegree,
      OneCycle.degree_cycle]
  have hP : ∀ γ : ProperCurve sX, γ.IsContractedBy f →
      pullbackNumericalClasses sX f ≤ LinearMap.ker (ℓ γ) := by
    intro γ hγ
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨E, M, hM, ⟨e⟩, rfl⟩
    change ℓ γ _ = 0
    rw [key, hiso γ e, ProperCurve.degree_pullback_eq_zero_of_isContractedBy f hf γ hγ M]
    simp
  have hrk : Module.finrank ℝ (NumericalDivisorClasses sX ⧸ pullbackNumericalClasses sX f) = 1 :=
    Module.rank_eq_one_iff_finrank_eq_one.mp (Cardinal.toENat_eq_one.mp hρ)
  have hℓ : ∀ (γ : ProperCurve sX) (hγ : γ.IsContractedBy f) (E : X.CartierDivisor),
      (pullbackNumericalClasses sX f).liftQ (ℓ γ) (hP γ hγ) ((pullbackNumericalClasses sX f).mkQ
        (numericalDivisorClass sX (KCartierDivisor.ofCartier ℝ E))) =
        (γ.degree k (MMP.CartierDivisor.sheaf E) : ℝ) := by
    intro γ hγ E
    rw [Submodule.mkQ_apply, Submodule.liftQ_apply, key]
  have ha0 : (pullbackNumericalClasses sX f).mkQ
      (numericalDivisorClass sX (KCartierDivisor.ofCartier ℝ EA)) ≠ 0 := by
    intro h
    have := hℓ γ₀ hγ₀ EA
    rw [h, map_zero, ← hiso γ₀ eA] at this
    exact hA0 (by exact_mod_cast this.symm)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ ha0).mp hrk
    ((pullbackNumericalClasses sX f).mkQ
      (numericalDivisorClass sX (KCartierDivisor.ofCartier ℝ EL)))
  have hlin : ∀ (γ : ProperCurve sX) (hγ : γ.IsContractedBy f),
      (γ.degree k L : ℝ) = c * γ.degree k A := by
    intro γ hγ
    rw [hiso γ eL, ← hℓ γ hγ EL, ← hc, map_smul, hℓ γ hγ EA, smul_eq_mul, hiso γ eA]
  have hc0 : c = 0 := by
    have := hlin γ₀ hγ₀
    rw [hL0, Int.cast_zero] at this
    rcases mul_eq_zero.mp this.symm with h | h
    · exact h
    · exact absurd (by exact_mod_cast h) hA0
  have := hlin γ hγ
  rw [hc0, zero_mul] at this
  exact_mod_cast this

end PicardNumberOne

section Specialization

open Order _root_.Topology

/-- **Chains of a subspace of a fibre.** If `g : W → Y` is an embedding into the fibre of `r`
over `v` and `n ≤ dim W`, there is a chain of `n` strict specializations of points of `Y` over
`v`: the generic points of the closures of a chain of irreducible closed subsets of `W`. -/
private theorem exists_ltSeries_of_le_topologicalKrullDim {W : Type*} [TopologicalSpace W]
    {Y V : Scheme} (r : Y ⟶ V) (v : V) {g : W → Y} (hg : IsInducing g)
    (hgv : ∀ t, r (g t) = v) {n : ℕ} (h : (n : WithBot ℕ∞) ≤ topologicalKrullDim W) :
    ∃ l : LTSeries Y, l.length = n ∧ ∀ i, r (l i) = v := by
  rw [topologicalKrullDim, le_krullDim_iff] at h
  obtain ⟨T, hT⟩ := h
  have hirr : ∀ T : TopologicalSpace.IrreducibleCloseds W, IsIrreducible (g '' (T : Set W)) :=
    fun T => T.isIrreducible.image _ hg.continuous.continuousOn
  let f : TopologicalSpace.IrreducibleCloseds W → Y := fun T => (hirr T).genericPoint
  have hf : ∀ T, closure {f T} = closure (g '' (T : Set W)) := fun T =>
    (hirr T).isGenericPoint_genericPoint_closure
  have hpre : ∀ T : TopologicalSpace.IrreducibleCloseds W,
      g ⁻¹' closure (g '' (T : Set W)) = (T : Set W) := by
    intro T
    rw [← hg.closure_eq_preimage_closure_image, T.isClosed.closure_eq]
  have hmono : StrictMono f := by
    intro T T' hTT'
    refine MMP.Intersection.lt_of_specializes_of_ne ?_ fun heq => hTT'.ne ?_
    · rw [specializes_iff_mem_closure, hf]
      have : f T ∈ closure (g '' (T : Set W)) := by rw [← hf]; exact subset_closure rfl
      exact closure_mono (Set.image_mono hTT'.le) this
    · have h1 := hf T
      rw [heq, hf T'] at h1
      apply TopologicalSpace.IrreducibleCloseds.ext
      rw [← hpre T, ← hpre T', h1]
  refine ⟨T.map f hmono, hT, fun i => ?_⟩
  change r (f (T i)) = v
  obtain ⟨x, hx⟩ := (T i).isIrreducible.nonempty
  have hsub : r '' closure (g '' ((T i : Set W))) ⊆ closure {v} := by
    refine (image_closure_subset_closure_image r.continuous).trans (closure_mono ?_)
    rintro _ ⟨_, ⟨y, -, rfl⟩, rfl⟩
    exact hgv y
  have h1 : r (f (T i)) ⤳ v := by
    rw [specializes_iff_mem_closure]
    have : r (g x) ∈ r '' closure {f (T i)} := by
      rw [hf]; exact ⟨g x, subset_closure ⟨x, hx, rfl⟩, rfl⟩
    rw [hgv x] at this
    have := image_closure_subset_closure_image r.continuous this
    rwa [Set.image_singleton] at this
  have h2 : v ⤳ r (f (T i)) := by
    rw [specializes_iff_mem_closure]
    refine hsub ⟨f (T i), ?_, rfl⟩
    rw [← hf]; exact subset_closure rfl
  exact (h1.antisymm h2).eq

/-- **Lifting specializations along a closed map.** If `r` is closed, the dimension of the
closure of `r y` is at most that of the closure of `y`. -/
private theorem height_apply_le_height_of_isClosedMap {Y V : Scheme} (r : Y ⟶ V)
    (hr : IsClosedMap r) (y : Y) (hfin : height (r y) < ⊤) : height (r y) ≤ height y := by
  have key : ∀ (n : ℕ) (y : Y), height (r y) < ⊤ → (n : ℕ∞) ≤ height (r y) →
      (n : ℕ∞) ≤ height y := by
    intro n
    induction n with
    | zero => intros; simp
    | succ n ih =>
      intro y hy hn
      have hlt : (n : ℕ∞) < height (r y) :=
        lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self n) hn
      obtain ⟨w, hw, hwn⟩ := (coe_lt_height_iff hy).mp hlt
      have hsp : r y ⤳ w := Scheme.le_iff_specializes.mp hw.le
      have hcl : w ∈ r '' closure {y} := by
        rw [← (hr _ (isClosed_closure (s := {y}))).closure_eq]
        refine closure_mono (Set.image_mono subset_closure) ?_
        rw [Set.image_singleton]
        exact specializes_iff_mem_closure.mp hsp
      obtain ⟨y', hy', rfl⟩ := hcl
      have hy'y : y' < y := by
        refine MMP.Intersection.lt_of_specializes_of_ne (specializes_iff_mem_closure.mpr hy') ?_
        rintro rfl
        exact hw.ne rfl
      have := ih y' (lt_of_le_of_lt (height_mono hw.le) hy) hwn.ge
      calc ((n + 1 : ℕ) : ℕ∞) = (n : ℕ∞) + 1 := by push_cast; rfl
        _ ≤ height y' + 1 := by gcongr
        _ ≤ height y := height_add_one_le hy'y
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hfin.ne
  rw [← hm]
  exact key m y hfin hm.le

/-- `3 ≤ d + 2` forces `1 ≤ d` in `WithBot ℕ∞`. -/
private theorem one_le_of_three_le_add_two {d : WithBot ℕ∞} (h : (3 : WithBot ℕ∞) ≤ d + 2) :
    1 ≤ d := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h
  | coe d =>
    rcases eq_or_ne d 0 with rfl | hd
    · exfalso
      have : ((0 : ℕ∞) : WithBot ℕ∞) + 2 = ((2 : ℕ∞) : WithBot ℕ∞) := by simp
      rw [this] at h
      have h' : (3 : ℕ∞) ≤ 2 := WithBot.coe_le_coe.mp h
      exact absurd h' (by decide)
    · exact WithBot.coe_le_coe.mpr (ENat.one_le_iff_ne_zero.mpr hd)

/-- **Fibres have dimension at least one.** For a dominant morphism from a threefold to a
surface, every irreducible component of every fibre has dimension at least one, by the lower
bound for the dimension of the fibres of the scheme-theoretic fibre. -/
private theorem one_le_topologicalKrullDim_of_mem_irreducibleComponents {Y V : Scheme.{0}}
    {sY : Y ⟶ Spec (.of ℂ)} {sV : V ⟶ Spec (.of ℂ)} [AlgebraicGeometry.IsVariety ℂ sY]
    [AlgebraicGeometry.IsVariety ℂ sV] (r : Y ⟶ V) (hrs : r ≫ sV = sY) [IsDominant r]
    (hdY : topologicalKrullDim Y = 3) (hdV : topologicalKrullDim V = 2) (v : V)
    (Z : Set (r ⁻¹' {v})) (hZ : Z ∈ irreducibleComponents (r ⁻¹' {v})) :
    1 ≤ topologicalKrullDim Z := by
  set e := r.fiberHomeo v
  have hZ' : e ⁻¹' Z ∈ irreducibleComponents (r.fiber v) :=
    preimage_mem_irreducibleComponents hZ e.isOpenEmbedding
      (by rw [e.surjective.range_eq, Set.inter_univ]; exact hZ.1.nonempty)
  have hdim : topologicalKrullDim (e ⁻¹' Z) = topologicalKrullDim Z := by
    have := IsHomeomorph.topologicalKrullDim_eq _ (e.image (e ⁻¹' Z)).isHomeomorph
    rwa [e.image_preimage] at this
  have h := (MMP.topologicalKrullDim_fiber_of_isDominant ℂ sY sV r hrs).1 v _ hZ'
  rw [hdY, hdV, hdim] at h
  exact one_le_of_three_le_add_two h

/-- **A contracted curve in a closed fibre.** Over a closed point `v` of the surface, the fibre
of `r` contains a proper curve, every point of which lies over `v`. -/
private theorem exists_properCurve_forall_specializes_eq {Y V : Scheme.{0}}
    [IsLocallyNoetherian Y] {sY : Y ⟶ Spec (.of ℂ)} {sV : V ⟶ Spec (.of ℂ)}
    [AlgebraicGeometry.IsProjectiveVariety ℂ sY] [AlgebraicGeometry.IsVariety ℂ sV]
    (r : Y ⟶ V) (hrs : r ≫ sV = sY) (hsurj : Function.Surjective r)
    (hdY : topologicalKrullDim Y = 3) (hdV : topologicalKrullDim V = 2) {v : V}
    (hv : IsClosed ({v} : Set V)) :
    ∃ γ : ProperCurve sY, γ.IsContractedBy r ∧ ∀ x, γ.point ⤳ x → r x = v := by
  haveI : IsDominant r := ⟨hsurj.denseRange⟩
  haveI : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace sY
  obtain ⟨y₀, hy₀⟩ := hsurj v
  obtain ⟨Z, hZ, -⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    ({⟨y₀, hy₀⟩} : Set (r ⁻¹' {v})) isIrreducible_singleton
  have h1 := one_le_topologicalKrullDim_of_mem_irreducibleComponents r hrs hdY hdV v Z hZ
  obtain ⟨l, hl, hlv⟩ := exists_ltSeries_of_le_topologicalKrullDim r v
    (g := fun z : Z => z.1.1) (IsInducing.subtypeVal.comp IsInducing.subtypeVal)
    (fun z => z.1.2) (n := 1) (by exact_mod_cast h1)
  set a := l 0
  set b := l (Fin.last l.length)
  have hab : a < b := l.strictMono (by simp [Fin.lt_def, hl])
  have hba : b ⤳ a := Scheme.le_iff_specializes.mp hab.le
  obtain ⟨p, hp, hpc⟩ :=
    nonempty_inter_closedPoints (⟨a, subset_closure rfl⟩ : (closure {a}).Nonempty)
    isClosed_closure.isLocallyClosed
  have hpc' : IsClosed ({p} : Set Y) := hpc
  have hap : a ⤳ p := specializes_iff_mem_closure.mpr hp
  have hbp : b ⤳ p := hba.trans hap
  have hbnp : b ∉ ({p} : Set Y) := by
    rintro rfl
    have : a ∈ closure ({b} : Set Y) := specializes_iff_mem_closure.mp hba
    rw [hpc'.closure_eq] at this
    exact hab.ne this
  obtain ⟨y, hby, -, -, hcurve⟩ :=
    MMP.Fourfold.exists_isProperCurve_of_specializes sY hbp hpc' hpc' rfl hbnp
  have hall : ∀ x, y ⤳ x → r x = v := by
    intro x hx
    have : r b ⤳ r x := (hby.trans hx).map r.continuous
    rw [show r b = v from hlv _, specializes_iff_mem_closure, hv.closure_eq] at this
    exact this
  refine ⟨⟨y, hcurve⟩, fun x hx => ?_, hall⟩
  rw [hall x (specializes_iff_mem_closure.mpr hx), hall y specializes_rfl]

end Specialization

section Negativity

/-- **A divisor with relatively ample negative is negative on the closed relative cone.** If
`-D` has an `f`-ample Cartier multiple, then `D` is negative on every nonzero class of
`NE̅(X/Y)`. -/
private theorem curveForm_relativeToAbsolute_neg {X Y : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)}
    {sY : Y ⟶ Spec (.of ℂ)} [AlgebraicGeometry.IsVariety ℂ sX] [AlgebraicGeometry.IsVariety ℂ sY]
    {f : X ⟶ Y} (hfp : IsProjective f) (hfs : f ≫ sY = sX) {D : QDivisor X}
    (hD : D.IsQCartier) (hDa : (-D).HasRelativelyAmpleMultiple f)
    (z : RelativeNumericalCurveClasses sX f) (hz : z ∈ relativeClosedConeOfCurves sX f)
    (hz0 : z ≠ 0) : (QDivisor.curveForm sX D hD ∘ₗ relativeToAbsolute sX f) z < 0 := by
  obtain ⟨mA, hmA, LA, hLAc, hLA, hamp⟩ := hDa
  haveI := hLAc.isInvertibleModule_divisorialSheaf
  obtain ⟨A, ⟨e⟩⟩ := exists_nonempty_iso_cartierDivisor_sheaf LA.divisorialSheaf
  have hampA : MMP.Mori.IsRelativelyAmple f (MMP.CartierDivisor.sheaf A) :=
    isRelativelyAmple_of_iso f e hamp
  have hpos := (isRelativelyAmple_cartierSheaf_iff_forall_relativeClosedConeOfCurves_pos sY sX f
    hfp hfs A).mp hampA z hz hz0
  have hneg : (-D).IsQCartier := ⟨mA, by exact_mod_cast hmA.ne', LA, hLA, hLAc⟩
  have hform : QDivisor.curveForm sX D hD = (-(1 / (mA : ℝ))) •
      NumericalCurveClasses.intersectionNumber (KCartierDivisor.ofCartier ℝ A) := by
    refine MMP.ProgramBaseChange.linearMap_ext_numericalClass_cycle sX fun C => ?_
    rw [MMP.ProgramBaseChange.curveForm_numericalClass_cycle, LinearMap.smul_apply,
      NumericalCurveClasses.intersectionNumber_numericalClass,
      OneCycle.intersectionNumber_ofCartier, OneCycle.cartierDegree, OneCycle.degree_cycle,
      show C.degree ℂ (MMP.CartierDivisor.sheaf A) = C.degree ℂ LA.divisorialSheaf
        from (degreeOn_eq_of_iso ℂ sX C.ι C.dim_le e).symm]
    have h1 := QDivisor.intersectionNumber_eq_of_toQDivisor_eq_smul ℂ sX C.ι C.dim_le
      (Divisor.degreeOn_add ℂ sX C.ι C.dim_le) (-D) hneg hmA LA hLAc hLA
    have h2 := MMP.Fourfold.intersectionNumber_smul sX C.ι C.dim_le (-D) hneg (-1)
      (by simpa using hD)
    rw [MMP.Fourfold.intersectionNumber_congr sX C.ι C.dim_le _ hD (by simp), h1] at h2
    rw [h2, ProperCurve.degree_divisorialSheaf C LA hLAc, smul_eq_mul]
    push_cast
    ring
  obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sX f z
  rw [LinearMap.comp_apply, isNaturalRelativeMap_relativeToAbsolute sX f Z, hform,
    LinearMap.smul_apply, NumericalCurveClasses.intersectionNumber_numericalClass]
  rw [RelativeNumericalCurveClasses.intersectionNumber_relativeNumericalClass] at hpos
  have : (0 : ℝ) < mA := by exact_mod_cast hmA
  rw [smul_eq_mul]
  nlinarith [div_pos one_pos this]

end Negativity

section Arithmetic

/-- `1 < d` forces `2 ≤ d` in `WithBot ℕ∞`. -/
private theorem two_le_of_one_lt {d : WithBot ℕ∞} (h : 1 < d) : 2 ≤ d := by
  induction d using WithBot.recBotCoe with
  | bot => exact absurd h (by simp)
  | coe d =>
    have h' : (1 : ℕ∞) < d := WithBot.coe_lt_coe.mp h
    have h2 : (1 : ℕ∞) + 1 ≤ d := Order.add_one_le_of_lt h'
    exact WithBot.coe_le_coe.mpr (by rwa [one_add_one_eq_two] at h2)

/-- Two elements of `ℕ∞` with finite sum are finite. -/
private theorem exists_eq_natCast_of_add_eq {a b : ℕ∞} {n : ℕ} (h : a + b = n) :
    ∃ a' b' : ℕ, a = a' ∧ b = b' ∧ a' + b' = n := by
  have ha : a ≠ ⊤ := fun ha => by simp [ha] at h
  have hb : b ≠ ⊤ := fun hb => by simp [hb] at h
  obtain ⟨a', rfl⟩ := ENat.ne_top_iff_exists.mp ha
  obtain ⟨b', rfl⟩ := ENat.ne_top_iff_exists.mp hb
  exact ⟨a', b', rfl, rfl, by exact_mod_cast h⟩

end Arithmetic

section Vertical

/-- **A vertical prime divisor is a multiple of a pull-back.** In the setting of
`IsContraction.exists_eq_smul_pullback_of_relativePicardNumberN1_eq_one`, a
prime divisor `E` of `Y` with `r(E) ≠ V` satisfies `mE = r^*(lC)` for a prime divisor `C` of
`V`, positive integers `l, m` with `lC` Cartier, and `r⁻¹(C) = E`.

A Cartier multiple `mE` has degree zero on a contracted curve in the fibre over a closed point
outside `r(E)`, on which the `r`-ample multiple of `-(K + Γ)` is positive; as `ρ(Y/V) = 1` it
has degree zero on every contracted curve, so it descends along the klt-negative contraction
`r`. The descended divisor `G` is effective with `r⁻¹(Supp G) = E`, so `Supp G = r(E)` is
irreducible and `G = lC`. -/
private theorem exists_isPullback_single_of_image_ne_univ {Y V : Scheme.{0}}
    [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V]
    {sY : Y ⟶ Spec (.of ℂ)} {sV : V ⟶ Spec (.of ℂ)} {r : Y ⟶ V}
    (hr : MMP.Fourfold.IsContraction sY sV r)
    (hY : MMP.Mori.IsProjectiveVariety ℂ sY) (hV : MMP.Mori.IsProjectiveVariety ℂ sV)
    (hdY : topologicalKrullDim Y = 3) (hdV : topologicalKrullDim V = 2)
    (hQ : MMP.Fourfold.IsQFactorial sY) (hρ : MMP.Fourfold.relativePicardNumberN1 sY r = 1)
    {n : ℕ} {K : MMP.Mori.Divisor Y} (hK : K.IsCanonicalDivisor sY n)
    {Γ : MMP.Mori.QDivisor Y} (hΓ : MMP.Fourfold.IsKltPair sY Γ)
    (hΓa : (-(MMP.Mori.Divisor.toQDivisor K + Γ)).HasRelativelyAmpleMultiple r)
    (E : MMP.Mori.PrimeDivisor Y) (hE : r '' (E.support : Set Y) ≠ Set.univ) :
    ∃ (C : MMP.Mori.PrimeDivisor V) (l m : ℕ) (hB : ∀ W : irreducibleComponents Y,
        r (componentGenericPoint Y W) ∉
          DivisorWithCoeffs.supp (Finsupp.single C (l : ℤ) : Divisor V)),
      0 < l ∧ 0 < m ∧ Divisor.IsCartier (Finsupp.single C (l : ℤ) : Divisor V) ∧
      Divisor.IsPullback r (Finsupp.single C (l : ℤ)) hB (Finsupp.single E (m : ℤ)) ∧
      r ⁻¹' (C.support : Set V) = E.support := by
  classical
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sY := hY
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sV := hV
  haveI : IsIntegral V := hr.isNormalVariety_target.1.toIsIntegral
  haveI : IsDominant r := ⟨hr.surjective.denseRange⟩
  have hrs := hr.comp_eq
  have hrp : IsProjective r := IsProjectiveMorphism.isProjective hr.isProjectiveMorphism
  haveI : IsProper r := hrp.isProper
  have hclosed : IsClosedMap r := r.isClosedMap
  -- a Cartier multiple `mE`
  obtain ⟨m, hm, hmc⟩ := hQ.2 (Finsupp.single E 1)
  set D' : Divisor Y := Finsupp.single E (m : ℤ)
  have hD'c : D'.IsCartier := by
    simpa [D', Finsupp.smul_single_one] using hmc
  have hD'0 : 0 ≤ D' := fun P => by
    by_cases hP : P = E
    · subst hP; simp [D']
    · simp [D', Finsupp.single_apply, Ne.symm hP]
  have hD'supp : (D'.supp : Set Y) = E.support := by
    refine subset_antisymm (DivisorWithCoeffs.supp_single_le E _) ?_
    refine DivisorWithCoeffs.support_subset_supp ?_
    rw [DivisorWithCoeffs.coeff_single_self]
    exact_mod_cast hm.ne'
  -- a contracted curve missing `E`
  have hrEc : IsClosed (r '' (E.support : Set Y)) := hclosed _ E.idealSheaf.support.isClosed
  haveI : JacobsonSpace V := LocallyOfFiniteType.jacobsonSpace sV
  obtain ⟨v, hvE, hvc⟩ := nonempty_inter_closedPoints (Set.nonempty_compl.mpr hE)
    hrEc.isOpen_compl.isLocallyClosed
  obtain ⟨γ₀, hγ₀, hγ₀v⟩ :=
    exists_properCurve_forall_specializes_eq r hrs hr.surjective hdY hdV (v := v) hvc
  -- the relatively ample multiple of `-(K + Γ)` is positive on `γ₀`
  obtain ⟨mA, hmA, LA, hLAc, hLA, hLAamp⟩ := id hΓa
  haveI := hLAc.isInvertibleModule_divisorialSheaf
  have hA0 : γ₀.degree ℂ LA.divisorialSheaf ≠ 0 :=
    (MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy r _ hLAamp γ₀
      hγ₀).ne'
  -- `mE` has degree zero on `γ₀`
  haveI := hD'c.isInvertibleModule_divisorialSheaf
  have hL0 : γ₀.degree ℂ D'.divisorialSheaf = 0 := by
    rw [ProperCurve.degree_divisorialSheaf γ₀ D' hD'c]
    have hq := MMP.Fourfold.isQCartier_of_isQFactorial sY hQ (Divisor.toQDivisor D')
    have h0 := MMP.Fourfold.intersectionNumber_eq_zero_of_disjoint sY hQ _ hq γ₀ fun x hx hxs => by
      rw [Divisor.supp_toQDivisor] at hxs
      have hxE : x ∈ (E.support : Set Y) := hD'supp ▸ hxs
      exact hvE ⟨x, hxE, hγ₀v x hx⟩
    rw [QDivisor.intersectionNumber_toQDivisor ℂ sY γ₀.ι γ₀.dim_le D' hD'c hq] at h0
    exact_mod_cast h0
  -- hence on every contracted curve
  have hL : ∀ γ : ProperCurve sY, γ.IsContractedBy r → γ.degree ℂ D'.divisorialSheaf = 0 :=
    degree_eq_zero_of_relativePicardNumberN1_eq_one hrs hρ _ _ hγ₀ hA0 hL0
  -- descent along the klt-negative contraction
  have hP := hΓ.1
  have hklt : MMP.Mori.IsKltPair sY n K Γ :=
    (MMP.Fourfold.isKltPair_iff_mori_isKltPair sY hK hP).mp hΓ
  have hset : IsProjectiveSetting ℂ sY sV r := ⟨inferInstance, inferInstance, hY, hV, hrs⟩
  have hB0 : 0 ≤ Γ := hP.nonneg
  set F := (relativeClosedConeOfCurves sY r : Set (RelativeNumericalCurveClasses sY r))
  have hFace : IsExtremalFace ℝ F F :=
    ⟨subset_rfl, isCone_coe _, fun u hu v hv => add_mem hu hv, fun u hu v hv _ => ⟨hu, hv⟩⟩
  have hF : IsNegativeExtremalFace ℝ F
      ((QDivisor.curveForm sY (Divisor.toQDivisor K + Γ) hklt.1.2.2).comp
        (relativeToAbsolute sY r)) F :=
    ⟨hFace, fun u hu v hv => add_mem hu hv, fun z hz hz0 =>
      curveForm_relativeToAbsolute_neg hrp hrs hklt.1.2.2 hΓa z hz hz0⟩
  have hψ : IsRelativeContractionOfFace r F r (𝟙 V) :=
    ⟨hFace, isProjectiveMorphism_id _, Category.comp_id r, hr.isIso_app, fun C hC =>
      ⟨fun _ => subset_closure (relativeClass_mem_relativeConeOfCurves hC), fun _ => hC⟩⟩
  obtain ⟨LZ, hLZ, ⟨e⟩⟩ := exists_isInvertible_iso_pullback_of_isRelativeContractionOfFace hset
    hklt hB0 hF hψ D'.divisorialSheaf (fun C hC _ => hL C hC)
  obtain ⟨G, hGc, hB, hG0, hGp⟩ := exists_isPullback_of_iso_pullback hr.isIso_app hD'0 LZ e
  -- the support of the descended divisor
  have hpre : r ⁻¹' (G.supp : Set V) = E.support := by
    rw [preimage_supp_eq_of_isPullback hGc hG0 hGp, hD'supp]
  have hGsupp : (G.supp : Set V) = r '' (E.support : Set Y) := by
    rw [← hpre, Set.image_preimage_eq _ hr.surjective]
  have hirr : IsIrreducible (G.supp : Set V) := by
    rw [hGsupp, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact isIrreducible_singleton.closure.image _ r.continuous.continuousOn
  obtain ⟨C, hCsupp, hGeq⟩ := eq_single_of_isIrreducible_supp G hirr
  have hGC : G C ≠ 0 := by
    intro h0
    rw [h0, Finsupp.single_zero] at hGeq
    have : (G.supp : Set V) = ∅ := by rw [hGeq]; simp
    rw [hGsupp] at this
    obtain ⟨x, hx⟩ := (AlgebraicGeometry.PrimeDivisor.support_eq_closure E ▸
      (⟨E.genericPoint, subset_closure rfl⟩ : (closure {E.genericPoint}).Nonempty))
    exact (Set.image_eq_empty.mp this).subset hx
  obtain ⟨l, hl⟩ : ∃ l : ℕ, G C = l := ⟨(G C).toNat, (Int.toNat_of_nonneg (hG0 C)).symm⟩
  have hl0 : 0 < l := by
    rcases Nat.eq_zero_or_pos l with h | h
    · exact absurd (by rw [hl, h]; rfl) hGC
    · exact h
  rw [hl] at hGeq
  subst hGeq
  exact ⟨C, l, m, hB, hl0, hm, hGc, hGp, by rw [← hCsupp, hpre]⟩

end Vertical

/-- **The vertical prime divisor `E` as a pull-back.** If `m E = r^*(l C)` with `l C` Cartier and
`r⁻¹(C) = E`, then `C = r(E)`, `C` is `ℚ`-Cartier, `E = (l/m) r^* C`, and `E` is the only prime
divisor in `r⁻¹(C)`. -/
private theorem exists_eq_smul_pullback_of_isPullback {Y V : Scheme.{0}}
    [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral V]
    [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V] {r : Y ⟶ V} [IsDominant r]
    (hs : Function.Surjective r)
    (E : MMP.Mori.PrimeDivisor Y) (C : MMP.Mori.PrimeDivisor V) {l m : ℕ} (hl : 0 < l)
    (hm : 0 < m) {hB : ∀ W : irreducibleComponents Y, r (componentGenericPoint Y W) ∉
      DivisorWithCoeffs.supp (Finsupp.single C (l : ℤ) : Divisor V)}
    (hCc : Divisor.IsCartier (Finsupp.single C (l : ℤ) : Divisor V))
    (hpull : Divisor.IsPullback r (Finsupp.single C (l : ℤ)) hB (Finsupp.single E (m : ℤ)))
    (hpre : r ⁻¹' (C.support : Set V) = E.support) :
    r '' (E.support : Set Y) = (C.support : Set V) ∧
      ∃ (hC : MMP.Mori.QDivisor.IsQCartier (Finsupp.single C (1 : ℚ) : MMP.Mori.QDivisor V))
        (hrC : ∀ W : irreducibleComponents Y,
          r (MMP.Mori.componentGenericPoint Y W) ∉
            MMP.Mori.DivisorWithCoeffs.supp (Finsupp.single C (1 : ℚ) : MMP.Mori.QDivisor V))
        (a : ℚ), 0 < a ∧
        (Finsupp.single E (1 : ℚ) : MMP.Mori.QDivisor Y) =
          a • MMP.Mori.QDivisor.pullback (f := r) (Finsupp.single C (1 : ℚ)) hC hrC ∧
        ∀ E' : MMP.Mori.PrimeDivisor Y,
          (E'.support : Set Y) ⊆ r ⁻¹' (C.support : Set V) → E' = E := by
  have hlq : (l : ℚ) ≠ 0 := by exact_mod_cast hl.ne'
  have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hC : MMP.Mori.QDivisor.IsQCartier (Finsupp.single C (1 : ℚ) : MMP.Mori.QDivisor V) :=
    ⟨(l : ℤ), by exact_mod_cast hl.ne', Finsupp.single C (l : ℤ), by
      rw [MMP.Threefold.Resolution.toQDivisor_single, Finsupp.smul_single]; simp, hCc⟩
  have hrC : ∀ W : irreducibleComponents Y, r (MMP.Mori.componentGenericPoint Y W) ∉
      MMP.Mori.DivisorWithCoeffs.supp (Finsupp.single C (1 : ℚ) : MMP.Mori.QDivisor V) :=
    MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' r _
  have hpb : MMP.Mori.QDivisor.IsPullback r (Finsupp.single C (1 : ℚ)) hrC
      (((m : ℚ) / l) • Finsupp.single E (1 : ℚ)) := by
    intro k hk D hD hDc
    have hBD := map_componentGenericPoint_notMem_supp_of_isDominant r D
    have hDeq : (l : ℤ) • D = (k : ℤ) • Finsupp.single C (l : ℤ) := by
      apply Divisor.toQDivisor_injective
      rw [map_zsmul, map_zsmul, hD, MMP.Threefold.Resolution.toQDivisor_single, smul_smul,
        Finsupp.smul_single, Finsupp.smul_single]
      congr 1
      simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_natCast, mul_one]
      ring
    have h1 := (Divisor.isPullback_pullback hDc hBD).zsmul hDc (l : ℤ)
      (map_componentGenericPoint_notMem_supp_of_isDominant r _)
    have h2 := (hpull.zsmul hCc (k : ℤ)
      (map_componentGenericPoint_notMem_supp_of_isDominant r _)).of_eq hDeq.symm
      (hB₂ := map_componentGenericPoint_notMem_supp_of_isDominant r _)
    have h3 : (l : ℤ) • D.pullback hDc hBD = (k : ℤ) • Finsupp.single E (m : ℤ) :=
      h1.eq (hDc.zsmul _) h2
    refine ⟨D.pullback hDc hBD, ?_, Divisor.isPullback_pullback hDc _⟩
    have h4 := congrArg Divisor.toQDivisor h3
    rw [map_zsmul, map_zsmul, MMP.Threefold.Resolution.toQDivisor_single] at h4
    have h5 : Divisor.toQDivisor (D.pullback hDc hBD) =
        ((l : ℚ)⁻¹ * k * m) • Finsupp.single E (1 : ℚ) := by
      have h6 := congrArg (fun G : MMP.Mori.QDivisor Y => (l : ℚ)⁻¹ • G) h4
      simp only [← Int.cast_smul_eq_zsmul ℚ, smul_smul, Int.cast_natCast] at h6
      rw [inv_mul_cancel₀ hlq, one_smul] at h6
      rw [h6, Finsupp.smul_single, Finsupp.smul_single]
      congr 1
      simp only [smul_eq_mul, mul_one]
    rw [h5, ← Int.cast_smul_eq_zsmul ℚ, smul_smul]
    congr 1
    push_cast
    field_simp
  refine ⟨by rw [← hpre, Set.image_preimage_eq _ hs], hC, hrC, (l : ℚ) / m, by positivity, ?_,
    fun E' hE' => ?_⟩
  · rw [MMP.Mori.QDivisor.IsPullback.pullback_eq hC hpb, smul_smul, div_mul_div_comm,
      mul_comm (l : ℚ),
      div_self (mul_ne_zero hmq hlq), one_smul]
  · have := hE' (MMP.Flips.primeDivisor_genericPoint_mem_support E')
    rw [hpre] at this
    exact (MMP.Threefold.Mori.primeDivisor_eq_of_genericPoint_mem_support E E' this).symm

/-- A normal variety on which every prime divisor has a Cartier multiple is `ℚ`-factorial. -/
private theorem isQFactorial_of_forall_isCartier_single {k : Type} [Field k] {V : Scheme.{0}}
    [IsLocallyNoetherian V] [IsNormal V] {sV : V ⟶ Spec (.of k)} (hN : IsNormalVariety k sV)
    (h : ∀ P : MMP.Mori.PrimeDivisor V, ∃ l : ℕ, 0 < l ∧
      Divisor.IsCartier (Finsupp.single P (l : ℤ) : Divisor V)) :
    MMP.Fourfold.IsQFactorial sV := by
  refine ⟨hN, fun D => ?_⟩
  refine Finsupp.induction D ⟨1, one_pos, by rw [smul_zero]; exact Divisor.isCartier_zero⟩ ?_
  intro P a D₀ _ _ ⟨m₀, hm₀, hc₀⟩
  obtain ⟨l, hl, hcl⟩ := h P
  refine ⟨l * m₀, Nat.mul_pos hl hm₀, ?_⟩
  have : ((l * m₀ : ℕ) : ℤ) • (Finsupp.single P a + D₀) =
      ((m₀ : ℤ) * a) • Finsupp.single P (l : ℤ) + (l : ℤ) • ((m₀ : ℤ) • D₀) := by
    rw [smul_add, Finsupp.smul_single, Finsupp.smul_single, smul_smul]
    congr 2
    simp only [smul_eq_mul]
    push_cast
    ring
  rw [this]
  exact (hcl.zsmul _).add (hc₀.zsmul _)

/-- On an integral variety of dimension `d` over `ℂ`, `height y + coheight y = d`. -/
private theorem height_add_coheight_eq {Y : Scheme.{0}} [IsIntegral Y] (sY : Y ⟶ Spec (.of ℂ))
    [LocallyOfFiniteType sY] {d : ℕ} (hd : topologicalKrullDim Y = d) (y : Y) :
    Order.height y + Order.coheight y = (d : ℕ∞) := by
  letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
  haveI : LocallyOfFiniteType (Y ↘ Spec (.of ℂ)) := (inferInstance : LocallyOfFiniteType sY)
  have := MMP.height_add_coheight_eq_krullDim ℂ y
  rw [Stacks.AlgebraicGeometry.AmpleDimensionOne.krullDim_eq_topologicalKrullDim, hd] at this
  exact WithBot.coe_injective (by rw [this]; rfl)

/-- **Fibres of a threefold over a surface are curves.** If `r : Y ⟶ V` is a closed surjection of
a threefold onto a surface over `ℂ` such that every prime divisor of `Y` not dominating `V` maps
onto a prime divisor of `V`, then every irreducible component of every fibre has dimension one:
a two-dimensional component lies over a closed point, and its closure is a prime divisor mapping
to that point. -/
private theorem topologicalKrullDim_eq_one_of_mem_irreducibleComponents {Y V : Scheme.{0}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral V]
    {sY : Y ⟶ Spec (.of ℂ)} {sV : V ⟶ Spec (.of ℂ)} [AlgebraicGeometry.IsVariety ℂ sY]
    [AlgebraicGeometry.IsVariety ℂ sV] (r : Y ⟶ V) (hrs : r ≫ sV = sY) [IsDominant r]
    (hclosed : IsClosedMap r) (hdY : topologicalKrullDim Y = 3) (hdV : topologicalKrullDim V = 2)
    [IsLocallyNoetherian V] [IsNormal V]
    (hvert : ∀ E : MMP.Mori.PrimeDivisor Y, r '' (E.support : Set Y) ≠ Set.univ →
      ∃ C : MMP.Mori.PrimeDivisor V, r '' (E.support : Set Y) = (C.support : Set V))
    (v : V) (Z : Set (r ⁻¹' {v})) (hZ : Z ∈ irreducibleComponents (r ⁻¹' {v})) :
    topologicalKrullDim Z = 1 := by
  refine le_antisymm ?_
    (one_le_topologicalKrullDim_of_mem_irreducibleComponents r hrs hdY hdV v Z hZ)
  by_contra hgt
  push Not at hgt
  obtain ⟨l, hl, hlv⟩ := exists_ltSeries_of_le_topologicalKrullDim r v
    (g := fun z : Z => z.1.1)
    (Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal)
    (fun z => z.1.2) (n := 2) (by exact_mod_cast two_le_of_one_lt hgt)
  let i₀ : Fin (l.length + 1) := ⟨0, by omega⟩
  let i₁ : Fin (l.length + 1) := ⟨1, by omega⟩
  let i₂ : Fin (l.length + 1) := ⟨2, by omega⟩
  have h01 : Order.height (l i₀) + 1 ≤ Order.height (l i₁) :=
    Order.height_add_one_le (l.strictMono (show i₀ < i₁ by simp [i₀, i₁, Fin.lt_def]))
  have h12 : Order.height (l i₁) + 1 ≤ Order.height (l i₂) :=
    Order.height_add_one_le (l.strictMono (show i₁ < i₂ by simp [i₁, i₂, Fin.lt_def]))
  obtain ⟨av, cv, hav, hcv, hsv⟩ := exists_eq_natCast_of_add_eq
    (height_add_coheight_eq sV (d := 2) (by rw [hdV]; rfl) v)
  obtain ⟨h₂, c₂, hh₂, hc₂, hs₂⟩ :=
    exists_eq_natCast_of_add_eq (height_add_coheight_eq sY (d := 3) (by rw [hdY]; rfl) (l i₂))
  have hv0 : Order.height v ≤ Order.height (l i₀) := by
    have := height_apply_le_height_of_isClosedMap r hclosed (l i₀)
      (by rw [hlv i₀, hav]; exact ENat.coe_lt_top av)
    rwa [hlv i₀] at this
  have hineq : Order.height v + 2 ≤ Order.height (l i₂) := by
    calc Order.height v + 2 ≤ Order.height (l i₀) + 1 + 1 := by
          rw [add_assoc, one_add_one_eq_two]; gcongr
      _ ≤ Order.height (l i₁) + 1 := by gcongr
      _ ≤ Order.height (l i₂) := h12
  rw [hav, hh₂] at hineq
  have hineq' : av + 2 ≤ h₂ := by exact_mod_cast hineq
  have hcoheight_generic : Order.coheight (genericPoint V) = 0 :=
    Order.coheight_eq_zero.mpr fun w _ =>
      Scheme.le_iff_specializes.mpr ((genericPoint_spec V).specializes (Set.mem_univ _))
  -- the most generic point of the chain is not the generic point of `Y`
  have hF1 : Order.coheight (l i₂) = 0 → Order.coheight v = 0 := by
    intro h0
    have hle : l i₂ ≤ genericPoint Y :=
      Scheme.le_iff_specializes.mpr ((genericPoint_spec Y).specializes (Set.mem_univ _))
    have heq : l i₂ = genericPoint Y :=
      ((Scheme.le_iff_specializes.mp (Order.coheight_eq_zero.mp h0 hle)).antisymm
        (Scheme.le_iff_specializes.mp hle)).eq
    rwa [← hlv i₂, heq, map_genericPoint_of_isDominant]
  -- a two-dimensional component over a closed point would be a vertical prime divisor
  have hF2 : Order.coheight (l i₂) = 1 → Order.height v = 0 → Order.coheight v = 2 →
      False := by
    intro h1 hv0' hcv2
    set E := AlgebraicGeometry.PrimeDivisor.ofCoheightOne (l i₂) h1
    have hEsupp : (E.support : Set Y) = closure {l i₂} := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
        AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
    have himg : r '' (E.support : Set Y) ⊆ {v} := by
      rintro _ ⟨x, hx, rfl⟩
      rw [hEsupp] at hx
      have hsp : v ⤳ r x := by
        rw [← hlv i₂]; exact (specializes_iff_mem_closure.mpr hx).map r.continuous
      have hle : r x ≤ v := Scheme.le_iff_specializes.mpr hsp
      exact (hsp.antisymm (Scheme.le_iff_specializes.mp
        (Order.height_eq_zero.mp hv0' hle))).eq.symm
    have hvE : r '' (E.support : Set Y) ≠ Set.univ := by
      intro h
      have hgv : genericPoint V = v := himg (h ▸ Set.mem_univ _)
      rw [← hgv, hcoheight_generic] at hcv2
      exact absurd hcv2 (by decide)
    obtain ⟨C, hC⟩ := hvert E hvE
    have hCv : AlgebraicGeometry.PrimeDivisor.genericPoint C = v :=
      himg (by rw [hC]; exact MMP.Flips.primeDivisor_genericPoint_mem_support C)
    have := AlgebraicGeometry.PrimeDivisor.coheight_genericPoint C
    rw [hCv, hcv2] at this
    exact absurd this (by decide)
  rcases (by omega : c₂ = 0 ∨ c₂ = 1) with h | h
  · have := hF1 (by rw [hc₂, h]; rfl)
    rw [hcv] at this
    have : cv = 0 := by exact_mod_cast this
    omega
  · have hav0 : av = 0 := by omega
    have hcv2 : cv = 2 := by omega
    exact hF2 (by rw [hc₂, h]; rfl) (by rw [hav, hav0]; rfl) (by rw [hcv, hcv2]; rfl)

/-- **Vertical prime divisors of a rank-one threefold Mori curve fibration.** Let
`r : Y ⟶ V` be a contraction of a `ℚ`-factorial projective threefold onto a projective surface
with `ρ(Y/V) = 1`, and let `Γ` be a klt boundary with `-(K + Γ)` relatively ample over `V`. Then
every irreducible component of every fibre of `r` has dimension one, `V` is `ℚ`-factorial, and
for every prime divisor `E` of `Y` with `r(E) ≠ V` the image `r(E)` is the support of a prime
divisor `C` of `V` such that `E = a • r^*C` for some rational `a > 0`, and `E` is the only prime
divisor of `Y` contained in `r⁻¹(C)`. -/
@[mmp "lem_fourfold_mori_threefold_vertical_prime_pullback"]
public theorem IsContraction.exists_eq_smul_pullback_of_relativePicardNumberN1_eq_one
    {Y V : Scheme.{0}}
    [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V]
    {sY : Y ⟶ Spec (.of ℂ)} {sV : V ⟶ Spec (.of ℂ)} {r : Y ⟶ V}
    (hr : IsContraction sY sV r)
    (hY : MMP.Mori.IsProjectiveVariety ℂ sY) (hV : MMP.Mori.IsProjectiveVariety ℂ sV)
    (hdY : topologicalKrullDim Y = 3) (hdV : topologicalKrullDim V = 2)
    (hQ : IsQFactorial sY) (hρ : relativePicardNumberN1 sY r = 1)
    {n : ℕ} {K : Divisor Y} (hK : K.IsCanonicalDivisor sY n)
    {Γ : QDivisor Y} (hΓ : IsKltPair sY Γ)
    (hΓa : (-(Divisor.toQDivisor K + Γ)).HasRelativelyAmpleMultiple r) :
    (∀ v : V, ∀ Z ∈ irreducibleComponents (r ⁻¹' {v}), topologicalKrullDim Z = 1) ∧
      IsQFactorial sV ∧
      ∀ E : MMP.Mori.PrimeDivisor Y, r '' (E.support : Set Y) ≠ Set.univ →
        ∃ C : MMP.Mori.PrimeDivisor V, r '' (E.support : Set Y) = (C.support : Set V) ∧
          ∃ (hC : QDivisor.IsQCartier (Finsupp.single C (1 : ℚ) : QDivisor V))
            (hrC : ∀ W : irreducibleComponents Y,
              r (componentGenericPoint Y W) ∉
                DivisorWithCoeffs.supp (Finsupp.single C (1 : ℚ) : QDivisor V))
            (a : ℚ), 0 < a ∧
            (Finsupp.single E (1 : ℚ) : QDivisor Y) =
              a • QDivisor.pullback (f := r) (Finsupp.single C (1 : ℚ)) hC hrC ∧
            ∀ E' : MMP.Mori.PrimeDivisor Y,
              (E'.support : Set Y) ⊆ r ⁻¹' (C.support : Set V) → E' = E := by
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sY := hY
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sV := hV
  haveI : IsIntegral V := hr.isNormalVariety_target.1.toIsIntegral
  haveI : IsDominant r := ⟨hr.surjective.denseRange⟩
  haveI : IsProper r := (IsProjectiveMorphism.isProjective hr.isProjectiveMorphism).isProper
  have hvert := exists_isPullback_single_of_image_ne_univ hr hY hV hdY hdV hQ hρ hK hΓ hΓa
  refine ⟨topologicalKrullDim_eq_one_of_mem_irreducibleComponents r hr.comp_eq r.isClosedMap
      hdY hdV
      fun E hE => ?_,
    isQFactorial_of_forall_isCartier_single hr.isNormalVariety_target fun P => ?_,
    fun E hE => ?_⟩
  · obtain ⟨C, l, m, _, hl, hm, hCc, hpull, hpre⟩ := hvert E hE
    exact ⟨C, (exists_eq_smul_pullback_of_isPullback hr.surjective E C hl hm hCc hpull hpre).1⟩
  · -- `P` lies under a prime divisor `F₀` of `Y`, and is `r(F₀)`
    obtain ⟨F₀, hF₀⟩ := exists_primeDivisor_subset_preimage hr.surjective P
    have hsub : r '' (F₀.support : Set Y) ⊆ P.support := Set.image_subset_iff.mpr hF₀
    have hvF : r '' (F₀.support : Set Y) ≠ Set.univ := fun h =>
      MMP.Flips.componentGenericPoint_notMem_support
        ⟨_, irreducibleComponent_mem_irreducibleComponents (genericPoint V)⟩ P
        (hsub (h ▸ Set.mem_univ _))
    obtain ⟨C, l, m, -, hl, -, hCc, -, hpre⟩ := hvert F₀ hvF
    have hCP : P = C := MMP.Threefold.Mori.primeDivisor_eq_of_genericPoint_mem_support P C
      (hsub (by rw [← hpre, Set.image_preimage_eq _ hr.surjective]
                exact MMP.Flips.primeDivisor_genericPoint_mem_support C))
    exact ⟨l, hl, hCP ▸ hCc⟩
  · obtain ⟨C, l, m, _, hl, hm, hCc, hpull, hpre⟩ := hvert E hE
    exact ⟨C, exists_eq_smul_pullback_of_isPullback hr.surjective E C hl hm hCc hpull hpre⟩

end MMP.Fourfold
