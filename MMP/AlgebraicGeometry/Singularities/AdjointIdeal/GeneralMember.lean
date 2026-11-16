module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.AdjointIdeal.ReducedSncBoundary
public import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupEmbedded
public import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.MMP.Steps
import MMP.AlgebraicGeometry.Resolution.DivisorialPart
import MMP.AlgebraicGeometry.Singularities.Bertini.GeneralMemberSNC

/-!
# A general member computes the boundary-zero adjoint ideal of a linear series

Let `X` be a smooth variety, projective over an affine variety `Z`, over an algebraically closed
field `k` of characteristic zero, let `V ⊆ H⁰(X, 𝒪_X(D))` be a nonzero linear series of an
integral Cartier divisor `D`, and let `0 < c < 1` be rational. On a log resolution `μ : Y → X` of
the series, `μ^*V = |M| + F` with `M` free and `F` the fixed divisor, and
`𝒥_{0,cV} = μ_*𝒪_Y(K_{Y/X} - ⌊cF⌋)`. Finitely many members `s₁, …, sₙ ∈ V` generate the base
ideal of `V`, and for a general `a ∈ kⁿ` the member `G = div(∑ aᵢ sᵢ) + D` satisfies
`𝒥_{0,cG} = μ_*𝒪_Y(K_{Y/X} - ⌊cF⌋)`, computed on the same resolution `μ`, and at any given point
`x` the general member has the minimum order at `x` of the base ideal.

## Main results

* `MMP.Mori.PrimeDivisor.ord_eq_ord_rationalFunctionsEquivFunctionField`,
  `MMP.Mori.coeff_principalDivisor_mk0`: the order along a prime divisor of a unit of `K(X)`,
  and the coefficient of its principal divisor, are the order of the rational function.
* `MMP.Fourfold.IsSeriesAdjointIdealOn.exists_isReducedAdjointIdealOn_of_general`: a general
  member of a linear series computes its boundary-zero adjoint ideal on the given log resolution,
  and has the order of the base ideal at a given point.

## Implementation notes

* Finite generation: on each of finitely many affine opens `U = Spec A` on which `D` has a local
  equation `ψ`, the `A`-module `ψ V` is an ideal of the Noetherian ring `A`.
* For a general member `g = ∑ aᵢ sᵢ`, the divided sections `μ^*sᵢ` generate `𝒪_Y(M)`, so the snc
  Bertini theorem (`MMP.Mori.exists_polynomial_pullback_zeroDivisor_eq_sum_isSNC`) makes
  `μ^*G = F + G'` with `G'` reduced, sharing no component with `F` or the exceptional divisors,
  and `G' + F + Ex(μ)` snc; as `0 < c < 1`, `⌊c(F + G')⌋ = ⌊cF⌋`.
* At a point `x`, the order of `g` is the least order `r` of the `sᵢ` as soon as the degree-`r`
  initial form of `∑ aᵢ sᵢ` is nonzero, a nontrivial linear condition on `a`; the order is a
  valuation on the regular local ring `𝒪_{X,x}`, so this does not depend on the local equation.
* Generality is stated as the non-vanishing locus of a nonzero polynomial `Q` on `kⁿ`; the base
  field `ℂ` of the source is generalized to an algebraically closed field of characteristic zero.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Positivity

open MMP.Mori

variable {X : Scheme.{u}} [IsIntegral X]

private theorem germ_eq_rationalFunctionsEquivFunctionField_symm (U : X.Opens) (s : Γ(X, U))
    (h : genericPoint X ∈ U) (Z : irreducibleComponents X) (hZ : componentGenericPoint X Z ∈ U) :
    (rationalFunctionsEquivFunctionField X).symm (X.presheaf.germ U (genericPoint X) h s) Z =
      X.presheaf.germ U (componentGenericPoint X Z) hZ s := by
  haveI : Finite (irreducibleComponents X) := by
    rw [irreducibleComponents_eq_singleton]
    infer_instance
  let D : Stacks.Chow.DenseOpen X := ⟨U, U.isOpen.dense ⟨_, h⟩⟩
  have key : (rationalFunctionsEquivFunctionField X).symm (X.presheaf.germ U (genericPoint X) h s)
      = (Stacks.Chow.rationalFunctionsEquivStalks X).1 (Stacks.Chow.ofSection X D s) := by
    rw [RingEquiv.symm_apply_eq, ← (Stacks.Chow.rationalFunctionsEquivFunctionField X).2 D s h]
    change _ = (Stacks.Chow.rationalFunctionsEquivFunctionField X).1
      ((Stacks.Chow.rationalFunctionsEquivStalks X).1.symm _)
    rw [RingEquiv.symm_apply_apply]
  rw [key]
  exact (Stacks.Chow.rationalFunctionsEquivStalks X).2 D s Z hZ

/-- The generization of the factor of `K(X)` along a component to the function field inverts
`MMP.Mori.rationalFunctionsEquivFunctionField`. -/
theorem componentToFunctionField_symm_apply (Z : irreducibleComponents X)
    (φ : X.functionField) :
    (componentToFunctionField Z).hom ((rationalFunctionsEquivFunctionField X).symm φ Z) = φ := by
  obtain ⟨U, hx, s, rfl⟩ := X.presheaf.germ_exist (x := genericPoint X) φ
  have hZ : componentGenericPoint X Z ∈ U :=
    (MMP.Fourfold.componentGenericPoint_eq_genericPoint Z) ▸ hx
  rw [germ_eq_rationalFunctionsEquivFunctionField_symm U s hx Z hZ,
    TopCat.Presheaf.germ_stalkSpecializes_apply]

/-- The generization to the function field of the factor of `u ∈ K(X)` along a component is
the rational function `MMP.Mori.rationalFunctionsEquivFunctionField X u`. -/
theorem componentToFunctionField_apply (Z : irreducibleComponents X)
    (u : RationalFunctions X) :
    (componentToFunctionField Z).hom (u Z) = rationalFunctionsEquivFunctionField X u := by
  conv_lhs => rw [← (rationalFunctionsEquivFunctionField X).symm_apply_apply u]
  exact componentToFunctionField_symm_apply Z _

end MMP.Positivity

namespace MMP.Mori

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- The order of a unit of `K(X)` along a prime divisor is that of the rational function. -/
theorem PrimeDivisor.ord_eq_ord_rationalFunctionsEquivFunctionField (P : PrimeDivisor X)
    (ψ : (RationalFunctions X)ˣ) :
    P.ord ψ = X.ord (rationalFunctionsEquivFunctionField X ψ) P.genericPoint := by
  rw [MMP.Positivity.ord_eq_ord_componentToFunctionField,
    MMP.Positivity.componentToFunctionField_apply]

/-- The coefficient of the divisor of a nonzero rational function is its order. -/
theorem coeff_principalDivisor_mk0 [CompactSpace X] (g : X.functionField) (hg : g ≠ 0)
    (P : PrimeDivisor X) :
    (principalDivisor (Units.map (rationalFunctionsEquivFunctionField X).symm.toMonoidHom
      (Units.mk0 g hg))).coeff P = X.ord g P.genericPoint := by
  rw [coeff_principalDivisor, P.ord_eq_ord_rationalFunctionsEquivFunctionField]
  simp

end MMP.Mori

namespace Proof_lem_mmp_adjoint_general_computing_member

open TopologicalSpace MMP.Fourfold MMP.Mori
open MMP.Mori.PrimeDivisor (ord_eq_ord_rationalFunctionsEquivFunctionField)
open MMP.Positivity (componentToFunctionField componentToFunctionField_symm_apply
  componentToFunctionField_apply)

/-! ### Rational functions and the function field -/

section RationalFunctions

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- A rational function is a section of `𝒪_X(D)` exactly when its order along every prime
divisor `P` is at least `-d_P`. -/
private theorem mem_sectionsIn_iff (D : Divisor X) (g : X.functionField) :
    g ∈ sectionsIn D ↔
      ∀ P : MMP.Mori.PrimeDivisor X, g = 0 ∨ -D.coeff P ≤ X.ord g P.genericPoint := by
  refine forall_congr' fun P => ?_
  by_cases hg : g = 0
  · simp [hg]
  · rw [P.divisorialValuation_eq_exp_neg_ord hg, WithZero.exp_le_exp]
    simp only [hg, false_or]
    omega

/-- `v_E(φ_{i(E)}) ≥ n` for the factor of a nonzero rational function `f` reads `ord_E f ≥ n`. -/
private theorem ordGE_symm_iff (E : MMP.Mori.PrimeDivisor X) (n : ℤ) {f : X.functionField}
    (hf : f ≠ 0) :
    E.OrdGE n ((rationalFunctionsEquivFunctionField X).symm f E.component) ↔
      n ≤ X.ord f E.genericPoint := by
  set u : (RationalFunctions X)ˣ :=
    Units.map (rationalFunctionsEquivFunctionField X).symm.toMonoidHom (Units.mk0 f hf)
  have hu : (u : RationalFunctions X) = (rationalFunctionsEquivFunctionField X).symm f := rfl
  have hne : (u : RationalFunctions X) E.component ≠ 0 :=
    ((Pi.isUnit_iff.mp u.isUnit) E.component).ne_zero
  have hord : E.ord u = X.ord f E.genericPoint := by
    rw [ord_eq_ord_rationalFunctionsEquivFunctionField, hu, RingEquiv.apply_symm_apply]
  rw [← hu]
  unfold MMP.Mori.PrimeDivisor.OrdGE
  rw [E.valuation_component, hord, WithZero.exp_le_exp]
  simp [hne]

/-- **Algebraic Hartogs on an open.** A rational function with nonnegative order along every
prime divisor meeting `U` is the germ of a regular function on `U`. -/
private theorem exists_germ_eq_of_forall_ord_nonneg {U : X.Opens} (hU : genericPoint X ∈ U)
    (f : X.functionField)
    (hf : ∀ E : MMP.Mori.PrimeDivisor X, (E.support ∩ U).Nonempty →
      0 ≤ X.ord f E.genericPoint) :
    ∃ a : Γ(X, U), X.presheaf.germ U (genericPoint X) hU a = f := by
  by_cases hf0 : f = 0
  · exact ⟨0, by rw [map_zero, hf0]⟩
  let φ : ToType ((rationalFunctionsPresheaf X).obj (Opposite.op U)) := fun Z =>
    (rationalFunctionsEquivFunctionField X).symm f Z.1
  have hφ : (0 : Divisor X).IsDivisorialSection U φ := fun E hE => by
    change E.OrdGE (-(0 : Divisor X).coeff E) ((rationalFunctionsEquivFunctionField X).symm f
      E.component)
    rw [ordGE_symm_iff E _ hf0, DivisorWithCoeffs.coeff_zero, neg_zero]
    exact hf E hE
  obtain ⟨a, ha⟩ := hφ.exists_eq
  refine ⟨a, ?_⟩
  set Z₀ : irreducibleComponents X := pointComponent (genericPoint X)
  have hZ₀ : componentGenericPoint X Z₀ ∈ U := (componentGenericPoint_eq_genericPoint Z₀) ▸ hU
  have h1 := congrFun ha ⟨Z₀, hZ₀⟩
  rw [toRationalFunctionsPresheaf_app_apply] at h1
  have h2 := congrArg (componentToFunctionField Z₀).hom h1
  rw [componentToFunctionField_symm_apply] at h2
  rw [← h2]
  exact (TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf hZ₀ _ a).symm

/-- **Finitely many members generate the base ideal.** -/
private theorem exists_finite_generators [CompactSpace X] (D : Divisor X) (hD : D.IsCartier)
    (V : AddSubgroup X.functionField) (hV : (V : Set X.functionField) ⊆ sectionsIn D) :
    ∃ (n : ℕ) (s : Fin n → X.functionField), (∀ i, s i ∈ V) ∧
      ∀ g ∈ V, ∀ x : X, ∃ r : Fin n → X.presheaf.stalk x,
        g = ∑ i, (X.presheaf.stalkSpecializes (genericPoint_specializes x)).hom (r i) * s i := by
  classical
  -- the local statement
  have hloc : ∀ x : X, ∃ (W : X.Opens) (_ : x ∈ W) (T : Finset X.functionField),
      (T : Set X.functionField) ⊆ V ∧ ∀ g ∈ V, ∀ y ∈ W,
        g ∈ Submodule.span (X.presheaf.stalk y) (T : Set X.functionField) := by
    intro x
    obtain ⟨U₀, hxU₀, ψu, hψu⟩ := hD x
    obtain ⟨W, hWa, hxW, hWU⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hxU₀
    have hηW : genericPoint X ∈ W :=
      ((genericPoint_spec X).mem_open_set_iff W.isOpen).mpr ⟨x, trivial, hxW⟩
    haveI : IsNoetherianRing Γ(X, W) := IsLocallyNoetherian.component_noetherian ⟨W, hWa⟩
    set ψ : X.functionField := rationalFunctionsEquivFunctionField X ψu
    have hψ0 : ψ ≠ 0 := (ψu.isUnit.map (rationalFunctionsEquivFunctionField X)).ne_zero
    set germ := X.presheaf.germ W (genericPoint X) hηW
    -- `g ψ` is regular on `W` for `g ∈ V`
    have hreg : ∀ g ∈ V, ∃ a : Γ(X, W), germ a = g * ψ := fun g hg => by
      refine exists_germ_eq_of_forall_ord_nonneg hηW _ fun E hE => ?_
      rcases eq_or_ne g 0 with rfl | hg0
      · simp
      have h1 := ((mem_sectionsIn_iff D g).mp (hV hg) E).resolve_left hg0
      have h2 : X.ord ψ E.genericPoint = D.coeff E := by
        rw [hψu E (hE.mono (Set.inter_subset_inter_right _ hWU)),
          ord_eq_ord_rationalFunctionsEquivFunctionField]
      rw [Scheme.ord_mul hg0 hψ0, h2]
      omega
    set S : Set Γ(X, W) := {a | ∃ g ∈ V, germ a = g * ψ}
    obtain ⟨T₀, hT₀S, hT₀⟩ := (Submodule.fg_span_iff_fg_span_finset_subset S).mp
      (IsNoetherian.noetherian (R := Γ(X, W)) (M := Γ(X, W)) _)
    let G : Γ(X, W) → X.functionField := fun a => if h : a ∈ S then h.choose else 0
    have hG : ∀ a ∈ S, G a ∈ V ∧ germ a = G a * ψ := fun a ha => by
      simp only [G, dif_pos ha]
      exact ha.choose_spec
    refine ⟨W, hxW, T₀.image G, fun f hf => ?_, fun g hg y hy => ?_⟩
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hf
      exact (hG a (hT₀S ha)).1
    obtain ⟨a, ha⟩ := hreg g hg
    have haN : a ∈ Submodule.span Γ(X, W) (T₀ : Set Γ(X, W)) :=
      hT₀ ▸ Submodule.subset_span ⟨g, hg, ha⟩
    obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.mp haN
    have hgsum : g = ∑ t ∈ T₀, germ (c t) * G t := by
      apply mul_right_cancel₀ hψ0
      rw [← ha, ← hc, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun t ht => ?_
      rw [smul_eq_mul, map_mul, (hG t (hT₀S ht)).2, mul_assoc]
    rw [hgsum]
    refine Submodule.sum_mem _ fun t ht => ?_
    have hgerm : germ (c t) = algebraMap (X.presheaf.stalk y) X.functionField
        (X.presheaf.germ W y hy (c t)) :=
      (TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf hy _ (c t)).symm
    rw [hgerm, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Finset.mem_image_of_mem G ht))
  choose W hxW T hTV hT using hloc
  obtain ⟨P, hP⟩ := isCompact_univ.elim_finite_subcover (fun x : X => (W x : Set X))
    (fun x => (W x).isOpen) (fun x _ => Set.mem_iUnion.mpr ⟨x, hxW x⟩)
  set S : Finset X.functionField := P.biUnion T
  refine ⟨S.card, fun i => (S.equivFin.symm i : X.functionField),
    fun i => ?_, fun g hg x => ?_⟩
  · obtain ⟨p, -, hp⟩ := Finset.mem_biUnion.mp (S.equivFin.symm i).2
    exact hTV p hp
  obtain ⟨p, hpP, hxp⟩ := Set.mem_iUnion₂.mp (hP (Set.mem_univ x))
  have hspan : g ∈ Submodule.span (X.presheaf.stalk x)
      (Set.range fun i => (S.equivFin.symm i : X.functionField)) := by
    have hrange : (Set.range fun i => (S.equivFin.symm i : X.functionField)) = S := by
      ext f
      refine ⟨fun ⟨i, hi⟩ => hi ▸ (S.equivFin.symm i).2, fun hf => ⟨S.equivFin ⟨f, hf⟩, ?_⟩⟩
      simp
    rw [hrange]
    exact Submodule.span_mono (fun f hf => Finset.mem_biUnion.mpr ⟨p, hpP, hf⟩) (hT p g hg x hxp)
  obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hspan
  exact ⟨r, hr.symm.trans (Finset.sum_congr rfl fun i _ => Algebra.smul_def _ _)⟩

end RationalFunctions

/-! ### Orders, stalks and pull-backs -/

section Pullback

/-- The valuation along `F` of a nonzero element of the factor of `K(X)` is the order of the
rational function it represents. -/
private theorem valuation_eq_exp_ord {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] (F : MMP.Mori.PrimeDivisor X)
    (c : X.presheaf.stalk (componentGenericPoint X F.component))
    (hc : (componentToFunctionField F.component).hom c ≠ 0) :
    F.valuation c =
      WithZero.exp (X.ord ((componentToFunctionField F.component).hom c) F.genericPoint) := by
  set χ := (componentToFunctionField F.component).hom c
  letI := (RationalFunctions.isField_stalk X F.component).toField
  have hcχ : c = (rationalFunctionsEquivFunctionField X).symm χ F.component :=
    RingHom.injective (componentToFunctionField F.component).hom
      (componentToFunctionField_symm_apply _ χ).symm
  set u : (RationalFunctions X)ˣ :=
    Units.map (rationalFunctionsEquivFunctionField X).symm.toMonoidHom (Units.mk0 χ hc)
  have hu : (u : RationalFunctions X) F.component = c := hcχ.symm
  rw [← hu, F.valuation_component, ord_eq_ord_rationalFunctionsEquivFunctionField]
  simp [u, χ]

/-- The coefficient along `F` of the pull-back of a Cartier divisor with local equation `ψ` near
`φ(η_F)` is the order of `φ^*ψ` along `F`. -/
private theorem coeff_eq_ord_of_isPullback {X Y : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (φ : X ⟶ Y) [IsDominant φ] {B : Divisor Y}
    {hB : ∀ Z : irreducibleComponents X, φ (componentGenericPoint X Z) ∉ B.supp}
    {B' : Divisor X} (h : B.IsPullback φ hB B') {U : Y.Opens} {ψ : (RationalFunctions Y)ˣ}
    (hψ : B.IsLocalEquation U ψ) (F : MMP.Mori.PrimeDivisor X) (hF : φ F.genericPoint ∈ U) :
    B'.coeff F =
      X.ord (functionFieldMap φ (rationalFunctionsEquivFunctionField Y ψ)) F.genericPoint := by
  have hFU : (F.support ∩ φ ⁻¹ᵁ U).Nonempty := (F.genericPoint_mem_iff (φ ⁻¹ᵁ U)).mp hF
  rw [h U ψ hψ F hFU]
  obtain ⟨W, hW⟩ := exists_mem_irreducibleComponents (φ (componentGenericPoint X F.component))
  have hmem := F.map_componentGenericPoint_mem φ hFU
  obtain ⟨a, ha⟩ := hψ.exists_unit_stalk hmem (hB _) hW
  rw [pullbackComponent_eq hB hψ hmem hW a ha]
  set χ := functionFieldMap φ (rationalFunctionsEquivFunctionField Y ψ)
  have hχ : χ ≠ 0 := (map_ne_zero_iff _ (functionFieldMap φ).injective).mpr
    (ψ.isUnit.map (rationalFunctionsEquivFunctionField Y)).ne_zero
  have hcχ : (componentToFunctionField F.component).hom
      ((φ.stalkMap (componentGenericPoint X F.component)).hom a) = χ := by
    change algebraMap (X.presheaf.stalk (componentGenericPoint X F.component)) X.functionField
      ((φ.stalkMap _).hom a) = χ
    rw [← functionFieldMap_algebraMap_stalk, ← MMP.Mori.algebraMap_stalkSpecializes
      ((isGenericPoint_componentGenericPoint Y W).specializes hW)]
    change functionFieldMap φ ((Y.presheaf.stalkSpecializes _).hom
      ((stalkToRationalFunctions Y hW).hom a)) = χ
    rw [ha]
    change functionFieldMap φ ((componentToFunctionField W).hom _) = χ
    rw [componentToFunctionField_apply]
  have h1 := F.valuation_eq_exp_ordUnit
    (Units.map (φ.stalkMap (componentGenericPoint X F.component)).hom.toMonoidHom a)
  rw [valuation_eq_exp_ord F _ (hcχ ▸ hχ)] at h1
  rw [← hcχ]
  exact (WithZero.exp_injective h1).symm

/-- An element of the local ring at `y` has nonnegative order along every prime divisor
through `y`. -/
private theorem ord_algebraMap_nonneg {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    {y : Y} (P : MMP.Mori.PrimeDivisor Y) (hP : y ∈ P.support) (a : Y.presheaf.stalk y)
    (ha : algebraMap (Y.presheaf.stalk y) Y.functionField a ≠ 0) :
    0 ≤ Y.ord (algebraMap (Y.presheaf.stalk y) Y.functionField a) P.genericPoint := by
  have hsp : P.genericPoint ⤳ y := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hP
    exact specializes_iff_mem_closure.mpr hP
  rw [← MMP.Mori.algebraMap_stalkSpecializes hsp] at ha ⊢
  set b := (Y.presheaf.stalkSpecializes hsp).hom a
  have hx := P.coheight_genericPoint
  rw [Scheme.le_ord_iff hx ha]
  have : Ring.KrullDimLE 1 (Y.presheaf.stalk P.genericPoint) := krullDimLE_of_coheight_le hx.le
  have hb0 : b ≠ 0 := fun hb => by simp [hb] at ha
  change _ ≤ Ring.ordFrac (Y.presheaf.stalk P.genericPoint) _
  rw [Ring.ordFrac_eq_ord _ hb0]
  have hnz : b ∈ nonZeroDivisors (Y.presheaf.stalk P.genericPoint) :=
    mem_nonZeroDivisors_of_ne_zero hb0
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (Ring.ord_ne_top hnz)
  simp only [Ring.ordMonoidWithZeroHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, hnz, if_true,
    ← hn]
  simp only [ENat.recTopCoe_coe, WithZero.one_le_coe]
  exact WithZero.coe_le_coe.mpr (Multiplicative.ofAdd_le.mpr (by exact_mod_cast Nat.zero_le n))

/-- A unit of the local ring at `y` has order zero along every prime divisor through `y`. -/
private theorem ord_algebraMap_eq_zero_of_isUnit {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] {y : Y} (P : MMP.Mori.PrimeDivisor Y) (hP : y ∈ P.support)
    {v : Y.presheaf.stalk y} (hv : IsUnit v) :
    Y.ord (algebraMap (Y.presheaf.stalk y) Y.functionField v) P.genericPoint = 0 := by
  obtain ⟨w, rfl⟩ := hv
  have h1 : algebraMap (Y.presheaf.stalk y) Y.functionField (w : Y.presheaf.stalk y) ≠ 0 :=
    (w.isUnit.map _).ne_zero
  have h2 : algebraMap (Y.presheaf.stalk y) Y.functionField ((w⁻¹ : (Y.presheaf.stalk y)ˣ) :
      Y.presheaf.stalk y) ≠ 0 := (w⁻¹.isUnit.map _).ne_zero
  have h3 := Scheme.ord_mul (x := P.genericPoint) h1 h2
  rw [← map_mul, Units.mul_inv, map_one, Scheme.ord_one] at h3
  have := ord_algebraMap_nonneg P hP _ h1
  have := ord_algebraMap_nonneg P hP _ h2
  omega

/-- **Algebraic Hartogs at a point.** On a normal integral locally Noetherian scheme, a rational
function with nonnegative order along every prime divisor through `x` lies in `𝒪_{X,x}`. -/
private theorem exists_algebraMap_stalk_eq_of_forall_ord_nonneg {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (x : X) {g : X.functionField}
    (h : ∀ Γ : MMP.Mori.PrimeDivisor X, x ∈ Γ.support → g = 0 ∨ 0 ≤ X.ord g Γ.genericPoint) :
    ∃ r : X.presheaf.stalk x, algebraMap (X.presheaf.stalk x) X.functionField r = g := by
  have : IsIntegrallyClosed (X.presheaf.stalk x) := IsNormal.stalk_normal x
  refine Stacks.AlgebraicGeometry.UnitsNormalProper.exists_algebraMap_eq_of_forall_height_eq_one
    X.functionField fun q hq => ?_
  have hξ1 : Order.coheight (X.fromSpecStalk x q) = 1 :=
    (Stacks.Chow.coheight_fromSpecStalk_eq_height x q).trans hq
  set E : MMP.Mori.PrimeDivisor X := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hξ1
  have hEξ : E.genericPoint = X.fromSpecStalk x q :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hξ1
  have hspec : E.genericPoint ⤳ x := hEξ ▸ Stacks.Chow.specializes_fromSpecStalk x q
  have hxE : x ∈ E.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact specializes_iff_mem_closure.mp hspec
  have hv : E.divisorialValuation g ≤ 1 := by
    rcases h E hxE with hg | hg
    · simp [hg]
    · by_cases hg0 : g = 0
      · simp [hg0]
      rw [E.divisorialValuation_eq_exp_neg_ord hg0, ← WithZero.exp_zero, WithZero.exp_le_exp]
      omega
  obtain ⟨b, hb⟩ := (E.divisorialValuation_le_one_iff g).mp hv
  let := (X.presheaf.stalkSpecializes hspec).hom.toAlgebra
  have hloc := Stacks.Chow.isLocalization_stalk_of_specializes hspec q hEξ.symm
  obtain ⟨⟨a, s⟩, hab⟩ := IsLocalization.mk'_surjective q.asIdeal.primeCompl b
  change IsLocalization.mk' E.localRing a s = b at hab
  refine ⟨a, s, s.2, ?_⟩
  have hspec' := IsLocalization.mk'_spec E.localRing a s
  rw [hab] at hspec'
  have h2 := congrArg (algebraMap E.localRing X.functionField) hspec'
  rw [map_mul, hb] at h2
  change g * algebraMap E.localRing X.functionField ((X.presheaf.stalkSpecializes hspec).hom s) =
    algebraMap E.localRing X.functionField ((X.presheaf.stalkSpecializes hspec).hom a) at h2
  rwa [MMP.Mori.algebraMap_stalkSpecializes, MMP.Mori.algebraMap_stalkSpecializes] at h2

/-- **Pull-back of a rational multiple of a Cartier divisor**: `f^*(cB) = c f^*B` for `c ∈ ℚ`. -/
private theorem isPullback_smul_toQDivisor {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace X] {f : X ⟶ Y} {B : Divisor Y}
    (hBc : B.IsCartier) {hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ B.supp}
    {B' : Divisor X} (h : B.IsPullback f hB B') (c : ℚ)
    (hcB : ∀ Z : irreducibleComponents X,
      f (componentGenericPoint X Z) ∉ (c • Divisor.toQDivisor B).supp) :
    (c • Divisor.toQDivisor B).IsPullback f hcB (c • Divisor.toQDivisor B') := by
  intro m hm D hD hDc
  have hm' : ((m : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hDB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ D.supp := fun Z hZ =>
    hcB Z (by rwa [QDivisor.supp_eq_of_toQDivisor_eq (by exact_mod_cast hm.ne') hD] at hZ)
  have hq : (c.den : ℚ) ≠ 0 := by exact_mod_cast c.den_ne_zero
  have hqc : (c.den : ℚ) * c = c.num := by rw [mul_comm]; exact Rat.mul_den_eq_num c
  have hkey : (c.den : ℤ) • D = ((m : ℤ) * c.num) • B := by
    apply Divisor.toQDivisor_injective
    ext E
    have := congrArg (fun G : QDivisor Y => G.coeff E) hD
    simp only [map_zsmul, DivisorWithCoeffs.coeff_smul, Divisor.coeff_toQDivisor, zsmul_eq_mul,
      smul_eq_mul] at this ⊢
    rw [this]
    push_cast
    rw [← hqc]
    ring
  set D' := D.pullback hDc hDB
  have hD' : D.IsPullback f hDB D' := Divisor.isPullback_pullback hDc hDB
  have hqD : ∀ Z : irreducibleComponents X,
      f (componentGenericPoint X Z) ∉ ((c.den : ℤ) • D).supp := fun Z hZ => hDB Z (by
    rwa [← Divisor.supp_toQDivisor, map_zsmul, QDivisor.supp_zsmul (by exact_mod_cast hq),
      Divisor.supp_toQDivisor] at hZ)
  have hmB : ∀ Z : irreducibleComponents X,
      f (componentGenericPoint X Z) ∉ (((m : ℤ) * c.num) • B).supp := by
    rw [← hkey]
    exact hqD
  have hqDc : ((c.den : ℤ) • D).IsCartier := fun x => by
    obtain ⟨U, hx, φ, hφ⟩ := hDc x
    exact ⟨U, hx, φ ^ (c.den : ℤ), hφ.zsmul _⟩
  have h1 := hD'.zsmul hDc (c.den : ℤ) hqD
  have h2 := (h.zsmul hBc ((m : ℤ) * c.num) hmB).of_eq hkey.symm (hB₂ := hqD)
  have heq := h1.eq hqDc h2
  refine ⟨D', ?_, hD'⟩
  ext E
  have := congrArg (fun G : Divisor X => (G.coeff E : ℚ)) heq
  simp only [DivisorWithCoeffs.coeff_smul, smul_eq_mul] at this
  simp only [map_zsmul, DivisorWithCoeffs.coeff_smul, Divisor.coeff_toQDivisor, zsmul_eq_mul,
    smul_eq_mul]
  push_cast at this
  rw [← hqc] at this
  apply mul_left_cancel₀ hq
  rw [this]
  push_cast
  ring

end Pullback

/-! ### The order of a general member at a point -/

section Order

open IsLocalRing

/-- `n ≤ mult f` exactly when `f ∈ 𝔪ⁿ`. -/
private theorem natCast_le_mult_iff {R : Type*} [CommRing R] [IsLocalRing R] (f : R) (n : ℕ) :
    (n : ℕ∞) ≤ MMP.Resolution.mult f ↔ f ∈ maximalIdeal R ^ n := by
  rw [MMP.Resolution.mult, MMP.Resolution.natCast_le_idealOrder_iff',
    Ideal.span_singleton_le_iff_mem]

/-- In a Noetherian local ring only `0` has infinite multiplicity (Krull's intersection
theorem). -/
private theorem eq_zero_of_mult_eq_top {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {f : R} (hf : MMP.Resolution.mult f = ⊤) : f = 0 := by
  have h : f ∈ ⨅ i : ℕ, maximalIdeal R ^ i :=
    Submodule.mem_iInf _ |>.mpr fun i => (natCast_le_mult_iff f i).mp (hf ▸ le_top)
  rwa [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal R).ne_top,
    Ideal.mem_bot] at h

/-- **A general linear combination has the least order.** Let `R` be a regular local ring with
fraction field `K`, `φ : k →+* R` a field of scalars and `s₁, …, sₙ ∈ K`, not all zero. There is
a nonzero (linear) polynomial `Q` such that for `Q(a) ≠ 0` the combination `g = ∑ aᵢ sᵢ` is
nonzero and, for any `h ∈ K` making `g h` and all `sᵢ h` regular, `mult (g h) ≤ mult (sᵢ h)`. -/
private theorem exists_polynomial_mult_le {R K k : Type*} [CommRing R] [IsRegularLocalRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] [Field k] (φ : k →+* R) {n : ℕ} (s : Fin n → K)
    (hs : ∃ i, s i ≠ 0) :
    ∃ Q : MvPolynomial (Fin n) k, Q ≠ 0 ∧ ∀ a : Fin n → k, MvPolynomial.eval a Q ≠ 0 →
      (∑ i, algebraMap R K (φ (a i)) * s i) ≠ 0 ∧
      ∀ (h : K) (b : R) (e : Fin n → R),
        algebraMap R K b = (∑ i, algebraMap R K (φ (a i)) * s i) * h →
        (∀ i, algebraMap R K (e i) = s i * h) →
        ∀ i, MMP.Resolution.mult b ≤ MMP.Resolution.mult (e i) := by
  classical
  set m := maximalIdeal R
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors R) Finset.univ s
  choose e₀ he₀ using fun i => hd i (Finset.mem_univ i)
  have hd0 : algebraMap R K (d : R) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2
  have he₀' : ∀ i, algebraMap R K (e₀ i) = algebraMap R K (d : R) * s i := fun i => by
    rw [he₀ i, Algebra.smul_def]
  obtain ⟨i₀, hi₀⟩ := hs
  obtain ⟨j, -, hj⟩ := Finset.exists_min_image Finset.univ (fun i => MMP.Resolution.mult (e₀ i))
    ⟨i₀, Finset.mem_univ _⟩
  have hjtop : MMP.Resolution.mult (e₀ j) ≠ ⊤ := by
    intro htop
    have h0 : e₀ i₀ = 0 :=
      eq_zero_of_mult_eq_top (top_le_iff.mp (htop ▸ hj i₀ (Finset.mem_univ _)))
    apply hi₀
    have := he₀' i₀
    rw [h0, map_zero] at this
    exact (mul_eq_zero.mp this.symm).resolve_left hd0
  obtain ⟨r, hr⟩ := ENat.ne_top_iff_exists.mp hjtop
  have hmem : ∀ i, e₀ i ∈ m ^ r := fun i =>
    (natCast_le_mult_iff _ r).mp (hr ▸ hj i (Finset.mem_univ _))
  have hjnot : e₀ j ∉ m ^ (r + 1) := fun h => by
    have := (natCast_le_mult_iff _ (r + 1)).mpr h
    rw [← hr] at this
    norm_cast at this
    omega
  let L : (Fin n → k) → R := fun a => ∑ i, φ (a i) * e₀ i
  let W : Submodule k (Fin n → k) :=
    { carrier := {a | L a ∈ m ^ (r + 1)}
      add_mem' := fun {a a'} ha ha' => by
        change ∑ i, φ ((a + a') i) * e₀ i ∈ m ^ (r + 1)
        simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
        exact add_mem ha ha'
      zero_mem' := by
        change ∑ i, φ ((0 : Fin n → k) i) * e₀ i ∈ m ^ (r + 1)
        simp
      smul_mem' := fun t a ha => by
        change ∑ i, φ ((t • a) i) * e₀ i ∈ m ^ (r + 1)
        simp only [Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc, ← Finset.mul_sum]
        exact Ideal.mul_mem_left _ _ ha }
  have hsingle : (Pi.single j (1 : k) : Fin n → k) ∉ W := by
    intro h
    apply hjnot
    change ∑ i, φ ((Pi.single j (1 : k) : Fin n → k) i) * e₀ i ∈ m ^ (r + 1) at h
    rwa [Finset.sum_eq_single j (fun i _ hij => by simp [Pi.single_apply, hij])
      (fun h => absurd (Finset.mem_univ j) h), Pi.single_eq_same, map_one, one_mul] at h
  obtain ⟨ℓ, hℓ, hWℓ⟩ := Submodule.exists_le_ker_of_notMem hsingle
  let Q : MvPolynomial (Fin n) k := ∑ i, MvPolynomial.C (ℓ (Pi.single i 1)) * MvPolynomial.X i
  have hQ : ∀ a, MvPolynomial.eval a Q = ℓ a := fun a => by
    have ha : a = ∑ i, a i • (Pi.single i (1 : k) : Fin n → k) := by
      ext i
      simp [Pi.single_apply]
    simp only [Q, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
    conv_rhs => rw [ha]
    simp [map_sum, mul_comm]
  refine ⟨Q, fun h0 => hℓ (by rw [← hQ, h0, map_zero]), fun a ha => ?_⟩
  rw [hQ] at ha
  have hLa : L a ∉ m ^ (r + 1) := fun h => ha (hWℓ h)
  have hLa' : L a ∈ m ^ r := Submodule.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hmem i)
  set g := ∑ i, algebraMap R K (φ (a i)) * s i with hg
  have hLg : algebraMap R K (L a) = g * algebraMap R K (d : R) := by
    simp only [L, map_sum, map_mul, he₀', hg, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hg0 : g ≠ 0 := by
    rintro hg0
    rw [hg0, zero_mul] at hLg
    exact hLa ((IsFractionRing.injective R K (hLg.trans (map_zero _).symm)) ▸ zero_mem _)
  refine ⟨hg0, fun h b e hb he i => ?_⟩
  by_contra! hlt
  obtain ⟨β, hβ⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_lt hlt)
  have he1 : e i ∈ m ^ β := (natCast_le_mult_iff _ β).mp hβ.le
  have he2 : e i ∉ m ^ (β + 1) := fun h' => by
    have := (natCast_le_mult_iff _ (β + 1)).mpr h'
    rw [← hβ] at this
    norm_cast at this
    omega
  have hb1 : b ∈ m ^ (β + 1) := (natCast_le_mult_iff _ (β + 1)).mp (by
    rw [← hβ] at hlt
    exact Order.add_one_le_of_lt hlt)
  have hprod : e₀ i * b = L a * e i := IsFractionRing.injective R K (by
    rw [map_mul, map_mul, he₀', hb, hLg, he i]; ring)
  have hin : e₀ i * b ∈ m ^ (r + β + 1) := by
    rw [add_assoc, pow_add]
    exact Ideal.mul_mem_mul (hmem i) hb1
  rw [hprod] at hin
  exact MMP.Flips.mul_notMem_maximalIdeal_pow_add_succ hLa' hLa he1 he2 hin

end Order

/-! ### A general member on the log resolution -/

section Bertini

/-- The valuation over `μ` of `g` is at most `exp n` exactly when `ord (μ^*g) ≥ -n`. -/
private theorem valuationOver_le_exp_iff {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (μ : Y ⟶ X) [IsDominant μ] (P : MMP.Mori.PrimeDivisor Y)
    {g : X.functionField} (hg : functionFieldMap μ g ≠ 0) (n : ℤ) :
    P.valuationOver μ g ≤ WithZero.exp n ↔ -n ≤ Y.ord (functionFieldMap μ g) P.genericPoint := by
  rw [MMP.Mori.PrimeDivisor.valuationOver_apply, P.divisorialValuation_eq_exp_neg_ord hg,
    WithZero.exp_le_exp]
  omega

/-- The valuation over `μ` of `g` is `exp n` exactly when `ord (μ^*g) = -n`. -/
private theorem valuationOver_eq_exp_iff {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (μ : Y ⟶ X) [IsDominant μ] (P : MMP.Mori.PrimeDivisor Y)
    {g : X.functionField} (hg : functionFieldMap μ g ≠ 0) (n : ℤ) :
    P.valuationOver μ g = WithZero.exp n ↔ Y.ord (functionFieldMap μ g) P.genericPoint = -n := by
  rw [MMP.Mori.PrimeDivisor.valuationOver_apply, P.divisorialValuation_eq_exp_neg_ord hg,
    WithZero.exp_inj]
  omega

/-- The coefficient of the divisor of zeros of a section read as the rational function `f`. -/
private theorem coeff_zeroDivisor {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [CompactSpace Y] (M : Divisor Y) (σ : M.divisorialSubmodule ⊤) (hσ : σ ≠ 0)
    {f : Y.functionField} (hf : Divisor.sectionToRationalFunctions σ =
      (rationalFunctionsEquivFunctionField Y).symm f) (P : MMP.Mori.PrimeDivisor Y) :
    (M.zeroDivisor σ hσ).coeff P = Y.ord f P.genericPoint + M.coeff P := by
  rw [Divisor.zeroDivisor_eq, DivisorWithCoeffs.coeff_add, coeff_principalDivisor,
    ord_eq_ord_rationalFunctionsEquivFunctionField]
  congr 2
  rw [IsUnit.unit_spec, hf, RingEquiv.apply_symm_apply]

/-- The pull-back of the germ at the generic point of a global function. -/
private theorem functionFieldMap_germ_top {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (μ : Y ⟶ X) [IsDominant μ] (t : Γ(X, ⊤)) :
    functionFieldMap μ (X.presheaf.germ ⊤ (genericPoint X) trivial t) =
      Y.presheaf.germ ⊤ (genericPoint Y) trivial (μ.appTop t) := by
  have h1 : X.presheaf.germ ⊤ (genericPoint X) trivial t =
      algebraMap (X.presheaf.stalk (μ (genericPoint Y))) X.functionField
        (X.presheaf.germ ⊤ (μ (genericPoint Y)) trivial t) :=
    (TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf _ _ t).symm
  have h2 := μ.germ_stalkMap_apply ⊤ (genericPoint Y) trivial t
  rw [h1, MMP.Mori.functionFieldMap_algebraMap_stalk, h2]
  exact TopCat.Presheaf.germ_stalkSpecializes_apply Y.presheaf _ _ _

private theorem support_sum_single {Y : Scheme.{u}} [DecidableEq (MMP.Mori.PrimeDivisor Y)]
    (S : Finset (MMP.Mori.PrimeDivisor Y)) :
    (∑ F ∈ S, Finsupp.single F (1 : ℤ)).support = S := by
  ext F
  simp [Finsupp.finsetSum_apply, Finsupp.single_apply]

/-- A prime divisor whose generic point lies on a prime divisor `E` is `E`. -/
private theorem eq_of_genericPoint_mem_support {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    {E F : MMP.Mori.PrimeDivisor Y} (hF : F.genericPoint ∈ E.support) : F = E := by
  apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hF
  have h1 : E.genericPoint ⤳ F.genericPoint := specializes_iff_mem_closure.mpr hF
  by_contra hne
  have hn : ¬ E.genericPoint ≤ F.genericPoint := fun h2 =>
    hne (Inseparable.eq (h1.antisymm h2)).symm
  have := Order.coheight_strictAnti
    (lt_of_le_not_ge (show F.genericPoint ≤ E.genericPoint from h1) hn)
  rw [E.coheight_genericPoint, F.coheight_genericPoint] at this
  exact lt_irrefl _ (this (by simp))

/-- `μ^*(D + div g) = μ^*D + div(μ^*g)`. -/
private theorem isPullback_add_principalDivisor {X Y : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [CompactSpace Y] (μ : Y ⟶ X) [IsDominant μ] {D : Divisor X} (hDc : D.IsCartier)
    {hD : ∀ Z : irreducibleComponents Y, μ (componentGenericPoint Y Z) ∉ D.supp} {Dμ : Divisor Y}
    (hpull : D.IsPullback μ hD Dμ) {g : X.functionField} (hg : g ≠ 0)
    (hg' : functionFieldMap μ g ≠ 0)
    (hB : ∀ Z : irreducibleComponents Y, μ (componentGenericPoint Y Z) ∉
      (D + MMP.Mori.principalDivisor
        (Units.map (rationalFunctionsEquivFunctionField X).symm.toMonoidHom
          (Units.mk0 g hg))).supp) :
    (D + MMP.Mori.principalDivisor
        (Units.map (rationalFunctionsEquivFunctionField X).symm.toMonoidHom
          (Units.mk0 g hg))).IsPullback μ hB
      (Dμ + MMP.Mori.principalDivisor (Units.map
        (rationalFunctionsEquivFunctionField Y).symm.toMonoidHom
          (Units.mk0 (functionFieldMap μ g) hg'))) := by
  set u := Units.map (rationalFunctionsEquivFunctionField X).symm.toMonoidHom (Units.mk0 g hg)
  have hBp : ∀ Z : irreducibleComponents Y,
      μ (componentGenericPoint Y Z) ∉ (MMP.Mori.principalDivisor u).supp :=
    fun Z => MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant μ _ Z
  obtain ⟨P', hP'⟩ := (Divisor.isCartier_principalDivisor u).exists_isPullback hBp
  have hP'eq : P' = MMP.Mori.principalDivisor (Units.map
      (rationalFunctionsEquivFunctionField Y).symm.toMonoidHom
        (Units.mk0 (functionFieldMap μ g) hg')) := by
    ext P
    rw [coeff_eq_ord_of_isPullback μ hP' (Divisor.isLocalEquation_principalDivisor u ⊤) P trivial,
      coeff_principalDivisor_mk0]
    simp [u]
  rw [← hP'eq]
  exact hpull.add hDc (Divisor.isCartier_principalDivisor u) hB hP'

/-- **The pulled-back generators have no base points modulo `F`.** If `s₁, …, sₙ` generate `V` at
every point and `μ^*V - F` is free, then at every `y ∈ Y` some `μ^*sᵢ` has order exactly
`coeff_P(F) - coeff_P(Dμ)` along every prime divisor `P ∋ y`. -/
private theorem exists_ord_eq_of_isFreeModuloFixedDivisor {X Y : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (μ : Y ⟶ X) [IsDominant μ] {V : Set X.functionField} {Dμ F : Divisor Y}
    (hfix : IsFixedDivisorOfPullback μ V Dμ F) (hfree : IsFreeModuloFixedDivisor μ V Dμ F)
    {n : ℕ} (s : Fin n → X.functionField) (hsV : ∀ i, s i ∈ V)
    (hgen : ∀ g ∈ V, ∀ x : X, ∃ r : Fin n → X.presheaf.stalk x,
      g = ∑ i, (X.presheaf.stalkSpecializes (genericPoint_specializes x)).hom (r i) * s i)
    (y : Y) :
    ∃ i, functionFieldMap μ (s i) ≠ 0 ∧ ∀ P : MMP.Mori.PrimeDivisor Y, y ∈ P.support →
      Y.ord (functionFieldMap μ (s i)) P.genericPoint = F.coeff P - Dμ.coeff P := by
  obtain ⟨g, hgV, hg0, hgP⟩ := hfree y
  obtain ⟨r, hr⟩ := hgen g hgV (μ y)
  set g' := functionFieldMap μ g
  have hg'0 : g' ≠ 0 := (map_ne_zero_iff _ (functionFieldMap μ).injective).mpr hg0
  have hordg : ∀ P : MMP.Mori.PrimeDivisor Y, y ∈ P.support →
      Y.ord g' P.genericPoint = F.coeff P - Dμ.coeff P := fun P hP => by
    rw [(valuationOver_eq_exp_iff μ P hg'0 _).mp (hgP P hP)]
    ring
  have hord_div : ∀ i (P : MMP.Mori.PrimeDivisor Y), functionFieldMap μ (s i) ≠ 0 →
      Y.ord (functionFieldMap μ (s i) / g') P.genericPoint =
        Y.ord (functionFieldMap μ (s i)) P.genericPoint - Y.ord g' P.genericPoint := by
    intro i P h0
    have h1 := Scheme.ord_mul (x := P.genericPoint) (div_ne_zero h0 hg'0) hg'0
    rw [div_mul_cancel₀ _ hg'0] at h1
    omega
  have hu : ∀ i, ∃ v : Y.presheaf.stalk y,
      algebraMap _ Y.functionField v = functionFieldMap μ (s i) / g' := by
    intro i
    refine exists_algebraMap_stalk_eq_of_forall_ord_nonneg y fun P hP => ?_
    by_cases h0 : functionFieldMap μ (s i) = 0
    · left
      rw [h0, zero_div]
    right
    rw [hord_div i P h0, hordg P hP]
    have := (valuationOver_le_exp_iff μ P h0 _).mp ((hfix P).1 (s i) (hsV i))
    omega
  choose v hv using hu
  have hsum : ∑ i, (μ.stalkMap y).hom (r i) * v i = 1 := by
    apply IsFractionRing.injective (Y.presheaf.stalk y) Y.functionField
    rw [map_one, map_sum]
    have : ∀ i, algebraMap _ Y.functionField ((μ.stalkMap y).hom (r i) * v i) =
        functionFieldMap μ ((X.presheaf.stalkSpecializes (genericPoint_specializes (μ y))).hom
          (r i) * s i) / g' := fun i => by
      rw [map_mul, hv i, ← functionFieldMap_algebraMap_stalk, map_mul, mul_div_assoc]
      rfl
    simp only [this, ← Finset.sum_div, ← map_sum, ← hr]
    exact div_self hg'0
  obtain ⟨i, -, hi⟩ := IsLocalRing.exists_of_isUnit_sum (hsum ▸ isUnit_one)
  replace hi := isUnit_of_mul_isUnit_right hi
  have hsi : functionFieldMap μ (s i) ≠ 0 := fun h0 => hi.ne_zero
    (IsFractionRing.injective _ Y.functionField (by rw [hv i, h0, zero_div, map_zero]))
  refine ⟨i, hsi, fun P hP => ?_⟩
  have h1 := ord_algebraMap_eq_zero_of_isUnit P hP hi
  rw [hv i, hord_div i P hsi, hordg P hP] at h1
  omega

/-- A divisor on a normal locally Noetherian scheme is its own pull-back along the identity. -/
private theorem divisor_isPullback_id {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    (D : Divisor X)
    (hD : ∀ C : irreducibleComponents X, (𝟙 X) (componentGenericPoint X C) ∉ D.supp) :
    D.IsPullback (𝟙 X) hD D := by
  intro U φ hφ E hE
  have hηU : componentGenericPoint X E.component ∈ U := E.map_componentGenericPoint_mem (𝟙 X) hE
  have hW : componentGenericPoint X E.component ∈ E.component.1 :=
    (isGenericPoint_componentGenericPoint X E.component).mem
  let a := Units.map (RationalFunctions.component X E.component).toMonoidHom φ
  have ha : (stalkToRationalFunctions X hW).hom a = (φ : RationalFunctions X) E.component := by
    simp [stalkToRationalFunctions, a, RationalFunctions.component]
  rw [pullbackComponent_eq hD hφ hηU hW a ha, hφ E hE, PrimeDivisor.ord_eq_ordUnit]
  congr 1
  ext
  simp [a]
  rfl

/-- The fixed divisor of the pullback of a linear series of sections of a Cartier divisor is
effective. -/
private theorem coeff_nonneg_of_isFixedDivisorOfPullback {X Y : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [CompactSpace Y] (μ : Y ⟶ X) [IsDominant μ] {D : Divisor X} (hDc : D.IsCartier)
    {hD : ∀ Z : irreducibleComponents Y, μ (componentGenericPoint Y Z) ∉ D.supp}
    {Dμ F : Divisor Y} (hpull : D.IsPullback μ hD Dμ) {V : Set X.functionField}
    (hVD : V ⊆ sectionsIn D) (hfix : IsFixedDivisorOfPullback μ V Dμ F)
    (P : MMP.Mori.PrimeDivisor Y) : 0 ≤ F.coeff P := by
  obtain ⟨g₀, hg₀V, hg₀, hval⟩ := (hfix P).2
  have hg₀' : functionFieldMap μ g₀ ≠ 0 :=
    (map_ne_zero_iff _ (functionFieldMap μ).injective).mpr hg₀
  have h := isPullback_add_principalDivisor μ hDc hpull hg₀ hg₀'
    (fun Z => MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant μ _ Z)
  have hnn := MMP.Fourfold.coeff_nonneg_of_isPullback_of_isEffectiveOn
    (hDc.add (Divisor.isCartier_principalDivisor _)) (V := ⊤)
    (fun Q _ => by
      rw [DivisorWithCoeffs.coeff_add, coeff_principalDivisor_mk0]
      have := ((mem_sectionsIn_iff D g₀).mp (hVD hg₀V) Q).resolve_left hg₀
      omega) h P
    ⟨P.genericPoint, MMP.Positivity.PrimeDivisor.genericPoint_mem_support' P, trivial⟩
  rw [DivisorWithCoeffs.coeff_add, coeff_principalDivisor_mk0] at hnn
  have := (valuationOver_eq_exp_iff μ P hg₀' _).mp hval
  omega

/-- **A general member is computed on the same log resolution.** For a log resolution `μ` of the
series `V` with fixed divisor `F`, on which `J = 𝒥_{0,cV}`, and members `s₁, …, sₙ` generating
`V`, a general `g = ∑ aᵢ sᵢ` has `μ^*(D + div g) = F + G'` with `G'` reduced and snc together
with `F` and the exceptional divisors, so `μ` computes `𝒥_{0,c(D + div g)} = J`. -/
private theorem exists_polynomial_isReducedAdjointIdealOn {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {D : Divisor X} {V : AddSubgroup X.functionField} {c : ℚ}
    (hc0 : 0 < c) (hc1 : c < 1) {Y : Scheme.{u}} {μ : Y ⟶ X}
    {J : X.Opens → Set X.functionField} (hJ : IsSeriesAdjointIdealOn sX 0 D V c μ J) {n : ℕ}
    (s : Fin n → X.functionField) (hsV : ∀ i, s i ∈ V)
    (hgen : ∀ g ∈ V, ∀ x : X, ∃ r : Fin n → X.presheaf.stalk x,
      g = ∑ i, (X.presheaf.stalkSpecializes (genericPoint_specializes x)).hom (r i) * s i) :
    ∃ Q : MvPolynomial (Fin n) k, Q ≠ 0 ∧ ∀ a : Fin n → k, MvPolynomial.eval a Q ≠ 0 →
      ∀ g ∈ V, g = ∑ i, baseFunction sX ((Scheme.ΓSpecIso (.of k)).inv.hom (a i)) * s i →
      ∀ hg : g ≠ 0,
        IsReducedAdjointIdealOn sX 0
          (c • Divisor.toQDivisor (D + MMP.Mori.principalDivisor
            (Units.map (rationalFunctionsEquivFunctionField X).symm.toMonoidHom
              (Units.mk0 g hg)))) μ J := by
  classical
  obtain ⟨hXv, hXs, hΔ, hDc, hVD, -, -, hYi, hYln, hYn, hμd, hY, hμ, hDμ, Dμ, F, Γ, Eadj, hpull,
    ⟨hlog, hfix, hfree, hsnc⟩, hΓ, hE, hJeq⟩ := hJ
  haveI := hYi
  haveI := hYln
  haveI := hYn
  haveI := hμd
  have hres := hlog.toIsLogResolution.toIsSmoothResolution
  haveI : IsProper μ := hres.isProper
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace μ
  haveI : AlgebraicGeometry.IsVariety k (μ ≫ sX) := hY.1
  haveI : Smooth (μ ≫ sX) := Scheme.Hom.smoothLocus_eq_top_iff.mp (by
    rw [← smoothLocus_eq_smoothLocus]; exact hres.isSmoothScheme)
  letI : Y.Over (Spec (.of k)) := ⟨μ ≫ sX⟩
  haveI : IsSmoothVariety k (Y ↘ Spec (.of k)) :=
    { toIsVariety := (inferInstance : AlgebraicGeometry.IsVariety k (μ ≫ sX)),
      toSmooth := (inferInstance : Smooth (μ ≫ sX)) }
  set eY := rationalFunctionsEquivFunctionField Y
  -- the moving part and the divided sections
  set M : Divisor Y := Dμ - F with hM
  let φ : Fin n → ToType ((rationalFunctionsPresheaf Y).obj (Opposite.op ⊤)) := fun i Z =>
    eY.symm (functionFieldMap μ (s i)) Z.1
  have hsec : ∀ i, M.IsDivisorialSection ⊤ (φ i) := by
    intro i E _
    change E.OrdGE (-M.coeff E) (eY.symm (functionFieldMap μ (s i)) E.component)
    by_cases h0 : functionFieldMap μ (s i) = 0
    · rw [h0, map_zero]
      exact MMP.Mori.PrimeDivisor.OrdGE.zero _
    rw [ordGE_symm_iff E _ h0]
    have h1 := (valuationOver_le_exp_iff μ E h0 _).mp ((hfix E).1 (s i) (hsV i))
    rw [hM, DivisorWithCoeffs.coeff_sub]
    omega
  let t : Fin n → M.divisorialSubmodule ⊤ := fun i => ⟨φ i, hsec i⟩
  have ht_rat : ∀ i, Divisor.sectionToRationalFunctions (t i) =
      eY.symm (functionFieldMap μ (s i)) := fun i => rfl
  have hfreeY : ∀ y : Y, ∃ (i : Fin n) (hi : t i ≠ 0), y ∉ (M.zeroDivisor (t i) hi).supp := by
    intro y
    obtain ⟨i, hsi, hord⟩ := exists_ord_eq_of_isFreeModuloFixedDivisor μ hfix hfree s hsV hgen y
    have hti : t i ≠ 0 := fun h => hsi (eY.symm.injective (by
      rw [← ht_rat, h, map_zero]; exact map_zero (rationalFunctionsPresheafTopEquiv Y)))
    refine ⟨i, hti, fun hmem => ?_⟩
    obtain ⟨P, hP0, hyP⟩ := DivisorWithCoeffs.mem_supp_iff.mp hmem
    rw [coeff_zeroDivisor M (t i) hti (ht_rat i) P, hord P hyP, hM,
      DivisorWithCoeffs.coeff_sub] at hP0
    exact hP0 (by ring)
  -- the fixed and exceptional components
  obtain ⟨B, hBset, hBsnc⟩ : ∃ B : Finset (MMP.Mori.PrimeDivisor Y),
      (⋃ E ∈ B, (E.support : Set Y)) = ((exceptionalSet μ ⊔
        (0 : Divisor X).supp.preimage μ.continuous ⊔ F.supp : Closeds Y) : Set Y) ∧
      DivisorWithCoeffs.IsSNC (Y ↘ Spec (.of k)) (∑ E ∈ B, Finsupp.single E (1 : ℤ)) := by
    rcases hsnc with h | hB
    · refine ⟨∅, ?_, ?_⟩
      · rw [h]
        simp
      · simpa using DivisorWithCoeffs.isSNC_zero (R := ℤ) (Y ↘ Spec (.of k))
    · exact hB
  have hid : IsSmoothResolution (Y ↘ Spec (.of k)) (𝟙 Y) :=
    ⟨inferInstance, isBirationalMorphism_of_isIso _, by
      rw [Category.id_comp]; exact hres.isSmoothScheme⟩
  obtain ⟨Q, hQ0, hQ'⟩ := MMP.Mori.exists_polynomial_pullback_zeroDivisor_eq_sum_isSNC
    (inferInstance : AlgebraicGeometry.IsVariety k (Y ↘ Spec (.of k))) hid
    t hfreeY B (by rw [Category.id_comp]; exact hBsnc)
  have hQ : ∀ c : Fin n → k, MvPolynomial.eval c Q ≠ 0 →
      ∀ hτ : (∑ i, scalarsToGlobalSections k (Y ↘ Spec (.of k)) (c i) • t i) ≠ 0,
        ∃ T : Finset (MMP.Mori.PrimeDivisor Y),
          M.zeroDivisor _ hτ = ∑ E ∈ T, Finsupp.single E (1 : ℤ) ∧ Disjoint T B ∧
          DivisorWithCoeffs.IsSNC (Y ↘ Spec (.of k)) (∑ E ∈ T ∪ B, Finsupp.single E (1 : ℤ)) ∧
          ∀ E ∈ T, ∀ E' ∈ T, E ≠ E' → Disjoint E.support E'.support := by
    intro c hc hτ
    have hB' : ∀ Z : irreducibleComponents Y,
        (𝟙 Y) (componentGenericPoint Y Z) ∉ (M.zeroDivisor _ hτ).supp := fun Z =>
      MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant (𝟙 Y) _ Z
    obtain ⟨T, hT, hTB, hsnc', hdisj⟩ := hQ' c hc hτ hB' _ (divisor_isPullback_id _ hB')
    exact ⟨T, hT, hTB, by rwa [Category.id_comp] at hsnc', hdisj⟩
  refine ⟨Q, hQ0, fun a ha g hgV hga hg => ?_⟩
  set eX := rationalFunctionsEquivFunctionField X
  set g' := functionFieldMap μ g with hg'def
  have hg'0 : g' ≠ 0 := (map_ne_zero_iff _ (functionFieldMap μ).injective).mpr hg
  set τ := ∑ i, scalarsToGlobalSections k (Y ↘ Spec (.of k)) (a i) • t i with hτdef
  have hscal : ∀ b : k, Y.presheaf.germ ⊤ (genericPoint Y) trivial
      (scalarsToGlobalSections k (Y ↘ Spec (.of k)) b) =
        functionFieldMap μ (baseFunction sX ((Scheme.ΓSpecIso (.of k)).inv.hom b)) := fun b => by
    rw [baseFunction, functionFieldMap_germ_top]
    congr 1
  have hrat_smul : ∀ (r : Γ(Y, ⊤)) (σ : M.divisorialSubmodule ⊤),
      Divisor.sectionToRationalFunctions (r • σ) =
        eY.symm (Y.presheaf.germ ⊤ (genericPoint Y) trivial r) *
          Divisor.sectionToRationalFunctions σ := fun r σ => by
    funext Z
    rw [Pi.mul_apply,
      MMP.Positivity.germ_eq_rationalFunctionsEquivFunctionField_symm ⊤ r trivial Z trivial]
    rfl
  have hτrat : Divisor.sectionToRationalFunctions τ = eY.symm g' := by
    change rationalFunctionsPresheafTopEquiv Y τ.1 = _
    rw [hτdef, Submodule.coe_sum, map_sum]
    change ∑ i, Divisor.sectionToRationalFunctions
      (scalarsToGlobalSections k (Y ↘ Spec (.of k)) (a i) • t i) = _
    simp only [hrat_smul, ht_rat, hscal]
    rw [hg'def, hga, map_sum, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_mul, map_mul]
  have hτ : τ ≠ 0 := fun h => hg'0 (eY.symm.injective (by
    rw [← hτrat, h, map_zero]; exact map_zero (rationalFunctionsPresheafTopEquiv Y)))
  obtain ⟨T, hT, hTB, hTBsnc, -⟩ := hQ a ha hτ
  set Zd := M.zeroDivisor τ hτ with hZd
  have hZcoeff : ∀ P, Zd.coeff P = Y.ord g' P.genericPoint + M.coeff P :=
    coeff_zeroDivisor M τ hτ hτrat
  set G := D + MMP.Mori.principalDivisor (Units.map eX.symm.toMonoidHom (Units.mk0 g hg)) with hG
  have hGcoeff : ∀ P, G.coeff P = D.coeff P + X.ord g P.genericPoint := fun P => by
    rw [hG, DivisorWithCoeffs.coeff_add, coeff_principalDivisor_mk0]
  have hGnn : ∀ P, 0 ≤ G.coeff P := fun P => by
    rw [hGcoeff]
    have := ((mem_sectionsIn_iff D g).mp (hVD hgV) P).resolve_left hg
    omega
  have hGc : G.IsCartier := hDc.add (Divisor.isCartier_principalDivisor _)
  have hBG : ∀ Z : irreducibleComponents Y, μ (componentGenericPoint Y Z) ∉ G.supp := fun Z =>
    MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant μ _ Z
  have hpullG : G.IsPullback μ hBG (F + Zd) := by
    have h := isPullback_add_principalDivisor μ hDc hpull hg hg'0 hBG
    convert h using 1
    ext P
    rw [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_add, hZcoeff,
      coeff_principalDivisor_mk0, hM, DivisorWithCoeffs.coeff_sub]
    ring
  have hF0 : ∀ P, 0 ≤ F.coeff P := coeff_nonneg_of_isFixedDivisorOfPullback μ hDc hpull hVD hfix
  have hZ0 : ∀ P, 0 ≤ Zd.coeff P := Divisor.zeroDivisor_nonneg M τ hτ
  have hZT : ∀ P, Zd.coeff P = if P ∈ T then 1 else 0 := fun P => by
    change Zd.coeff P = _
    rw [hT]
    simp [Finsupp.finsetSum_apply, Finsupp.single_apply, DivisorWithCoeffs.coeff_apply]
  have hZsupp : (Zd.supp : Set Y) = ⋃ E ∈ T, (E.support : Set Y) := by
    rw [DivisorWithCoeffs.coe_supp]
    change ⋃ E ∈ Zd.support, _ = _
    rw [hT, support_sum_single]
  have hFsupp : (F.supp : Set Y) ⊆ ⋃ E ∈ B, (E.support : Set Y) := by
    rw [hBset]
    intro y hy
    exact Or.inr hy
  have hFT : ∀ P ∈ T, F.coeff P = 0 := fun P hP => by
    by_contra hne
    obtain ⟨E, hEB, hPE⟩ := Set.mem_iUnion₂.mp
      (hFsupp (DivisorWithCoeffs.support_subset_supp hne
        (MMP.Positivity.PrimeDivisor.genericPoint_mem_support' P)))
    exact Finset.disjoint_left.mp hTB hP (by rw [eq_of_genericPoint_mem_support hPE]; exact hEB)
  -- supports
  have hc0' : (c : ℚ) ≠ 0 := hc0.ne'
  have hsuppQ : ∀ x : X, x ∈ (c • Divisor.toQDivisor G).supp ↔ x ∈ G.supp := fun x => by
    simp only [DivisorWithCoeffs.mem_supp_iff, DivisorWithCoeffs.coeff_smul,
      Divisor.coeff_toQDivisor, smul_eq_mul, ne_eq, mul_eq_zero, hc0', false_or, Int.cast_eq_zero]
  have hsuppR : ∀ x : X,
      x ∈ (QDivisor.toRDivisor (Divisor.toQDivisor 0 + c • Divisor.toQDivisor G)).supp ↔
        x ∈ G.supp := fun x => by
    simp only [DivisorWithCoeffs.mem_supp_iff, QDivisor.coeff_toRDivisor,
      DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, Divisor.coeff_toQDivisor,
      DivisorWithCoeffs.coeff_zero, smul_eq_mul, ne_eq, Rat.cast_eq_zero, Int.cast_zero, zero_add,
      mul_eq_zero, hc0', false_or, Int.cast_eq_zero]
  have hpre : μ.base ⁻¹' (G.supp : Set X) = (F.supp : Set Y) ∪ Zd.supp := by
    rw [← MMP.Flips.supp_eq_preimage_supp_of_isPullback hGc hGnn hpullG]
    ext y
    simp only [SetLike.mem_coe, Set.mem_union, DivisorWithCoeffs.mem_supp_iff,
      DivisorWithCoeffs.coeff_add]
    constructor
    · rintro ⟨P, hP, hyP⟩
      by_cases hF : F.coeff P = 0
      · exact Or.inr ⟨P, by rwa [hF, zero_add] at hP, hyP⟩
      · exact Or.inl ⟨P, hF, hyP⟩
    · rintro (⟨P, hP, hyP⟩ | ⟨P, hP, hyP⟩) <;>
        exact ⟨P, fun h => hP (by linarith [hF0 P, hZ0 P]), hyP⟩
  have hDq : ∀ Z : irreducibleComponents Y,
      μ (componentGenericPoint Y Z) ∉ (c • Divisor.toQDivisor G).supp := fun Z h =>
    hBG Z ((hsuppQ _).mp h)
  refine ⟨hXv, hXs, hΔ, fun P => ?_, ?_,
    ⟨⟨hres, hlog.toIsLogResolution.isPureCodimOne_exceptionalSet, Or.inr ⟨T ∪ B, ?_, hTBsnc⟩⟩,
      hlog.isProjectiveMorphism⟩, hYi, hYln, hYn, hμd, hY, hμ, hDq, Γ, Eadj,
    c • Divisor.toQDivisor (F + Zd), hΓ, hE, isPullback_smul_toQDivisor hGc hpullG c hDq, ?_⟩
  · rw [DivisorWithCoeffs.coeff_smul, Divisor.coeff_toQDivisor, smul_eq_mul]
    exact mul_nonneg hc0.le (by exact_mod_cast hGnn P)
  · rintro S ⟨J', hJ', hmax⟩ hsub
    have hJ'e : J' = ∅ := Finset.subset_empty.mp (by simpa using hJ')
    have huniv : Set.univ ⊆ S :=
      hmax.2 ⟨IrreducibleSpace.isIrreducible_univ X, by simp [hJ'e]⟩ (Set.subset_univ _)
    apply MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant (𝟙 X) G
      (pointComponent (genericPoint X))
    exact (hsuppQ _).mp (hsub (huniv (Set.mem_univ _)))
  · rw [Finset.set_biUnion_union, ← hZsupp, hBset]
    have hR : ∀ y : Y, y ∈ (((QDivisor.toRDivisor (Divisor.toQDivisor 0 +
        c • Divisor.toQDivisor G)).supp.preimage μ.continuous : Closeds Y) : Set Y) ↔
          (y ∈ (F.supp : Set Y) ∨ y ∈ (Zd.supp : Set Y)) := fun y => by
      rw [TopologicalSpace.Closeds.coe_preimage, Set.mem_preimage, SetLike.mem_coe, hsuppR,
        ← SetLike.mem_coe, ← Set.mem_preimage, hpre, Set.mem_union]
    have h0 : ∀ y : Y, y ∉ (((0 : Divisor X).supp.preimage μ.continuous : Closeds Y) : Set Y) :=
      fun y h => by
        rw [TopologicalSpace.Closeds.coe_preimage, DivisorWithCoeffs.supp_zero,
          TopologicalSpace.Closeds.coe_bot] at h
        exact h
    ext y
    simp only [Set.mem_union, TopologicalSpace.Closeds.coe_sup]
    rw [hR y]
    have := h0 y
    tauto
  · rw [hJeq]
    congr 2
    ext P
    simp only [MMP.Intersection.WeilRDivisor.coeff_roundDown, QDivisor.coeff_toRDivisor,
      DivisorWithCoeffs.coeff_smul, Divisor.coeff_toQDivisor, Divisor.coeff_toRDivisor,
      DivisorWithCoeffs.coeff_add, smul_eq_mul]
    by_cases hP : P ∈ T
    · rw [hFT P hP, hZT P, if_pos hP]
      have h1 : ⌊((c * ((0 : ℤ) + (1 : ℤ) : ℤ) : ℚ) : ℝ)⌋ = 0 := by
        rw [Int.floor_eq_zero_iff]
        push_cast
        rw [mul_one]
        constructor <;> [exact_mod_cast hc0.le; exact_mod_cast hc1]
      rw [h1]
      simp
    · rw [hZT P, if_neg hP]
      push_cast
      ring_nf

end Bertini

end Proof_lem_mmp_adjoint_general_computing_member

namespace MMP.Fourfold

open MMP.Mori
open Proof_lem_mmp_adjoint_general_computing_member

/-- **A general member computes the boundary-zero adjoint ideal.** Let `X` be a smooth variety
over an algebraically closed field `k` of characteristic zero, projective over an affine variety
`Z`, `D` an integral Cartier divisor, `V ⊆ H⁰(X, 𝒪_X(D))` a nonzero linear series, `0 < c < 1`
rational, and `μ : Y ⟶ X` a log resolution of `V` on which
`J = 𝒥_{0,cV} = μ_*𝒪_Y(K_{Y/X} - ⌊cF⌋)`, `F` the fixed divisor of `μ^*V`
(`MMP.Fourfold.IsSeriesAdjointIdealOn`). Then
1. finitely many `s₁, …, sₙ ∈ V` generate the base ideal of `V`;
2. for any such family and any point `x ∈ X`, there is a nonzero polynomial `Q` such that for
   every `a ∈ kⁿ` with `Q(a) ≠ 0` the member `g = ∑ aᵢ sᵢ` is nonzero, its divisor
   `G = div g + D` has `𝒥_{0,cG} = J`, computed on `μ` (`MMP.Fourfold.IsReducedAdjointIdealOn`),
   and the order of `G` at `x` is at most the order of every `sᵢ` (so it is the order at `x`
   of the base ideal). -/
@[mmp "lem_mmp_adjoint_general_computing_member"]
public theorem IsSeriesAdjointIdealOn.exists_isReducedAdjointIdealOn_of_general {k : Type u}
    [Field k] [IsAlgClosed k] [CharZero k] {X Z : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (sZ : Z ⟶ Spec (.of k)) (f : X ⟶ Z) (hf : f ≫ sZ = sX) [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] (hfp : IsProjectiveMorphism f)
    (hZ : IsAffine Z) (hZv : MMP.Mori.IsVariety k sZ) (hXs : IsSmoothScheme sX) (D : Divisor X)
    (hD : D.IsCartier)
    (V : AddSubgroup X.functionField) (hV : (V : Set X.functionField) ⊆ sectionsIn D)
    (hV0 : V ≠ ⊥)
    (hVk : ∀ (a : k) (g : X.functionField), g ∈ V →
      baseFunction sX ((Scheme.ΓSpecIso (.of k)).inv.hom a) * g ∈ V)
    (c : ℚ) (hc0 : 0 < c) (hc1 : c < 1) {Y : Scheme.{u}} (μ : Y ⟶ X)
    (J : X.Opens → Set X.functionField) (hJ : IsSeriesAdjointIdealOn sX 0 D V c μ J) :
    (∃ (n : ℕ) (s : Fin n → X.functionField), (∀ i, s i ∈ V) ∧
      ∀ g ∈ V, ∀ x : X, ∃ r : Fin n → X.presheaf.stalk x,
        g = ∑ i, (X.presheaf.stalkSpecializes (genericPoint_specializes x)).hom (r i) * s i) ∧
    ∀ (n : ℕ) (s : Fin n → X.functionField), (∀ i, s i ∈ V) →
      (∀ g ∈ V, ∀ x : X, ∃ r : Fin n → X.presheaf.stalk x,
        g = ∑ i, (X.presheaf.stalkSpecializes (genericPoint_specializes x)).hom (r i) * s i) →
      ∀ x : X, ∃ Q : MvPolynomial (Fin n) k, Q ≠ 0 ∧ ∀ a : Fin n → k, MvPolynomial.eval a Q ≠ 0 →
        let g : X.functionField :=
          ∑ i, baseFunction sX ((Scheme.ΓSpecIso (.of k)).inv.hom (a i)) * s i
        ∃ hg : g ≠ 0,
          IsReducedAdjointIdealOn sX 0
            (c • Divisor.toQDivisor (D + MMP.Mori.principalDivisor
              (Units.map (rationalFunctionsEquivFunctionField X).symm.toMonoidHom
                (Units.mk0 g hg)))) μ J ∧
          ∀ (h : X.functionField) (b : X.presheaf.stalk x) (e : Fin n → X.presheaf.stalk x),
            (X.presheaf.stalkSpecializes (genericPoint_specializes x)).hom b = g * h →
            (∀ i, (X.presheaf.stalkSpecializes (genericPoint_specializes x)).hom (e i) =
              s i * h) →
            ∀ i, MMP.Resolution.mult b ≤ MMP.Resolution.mult (e i) := by
  classical
  refine ⟨exists_finite_generators D hD V hV, fun n s hsV hgen x => ?_⟩
  have hs : ∃ i, s i ≠ 0 := by
    by_contra! h
    obtain ⟨g, hgV, hg0⟩ := (AddSubgroup.bot_or_exists_ne_zero V).resolve_left hV0
    obtain ⟨r, hr⟩ := hgen g hgV x
    exact hg0 (by simp [hr, h])
  haveI : AlgebraicGeometry.IsVariety k sX := hJ.1.1
  haveI : Smooth sX := Scheme.Hom.smoothLocus_eq_top_iff.mp (by
    rw [← smoothLocus_eq_smoothLocus]; exact hXs)
  haveI := isRegularLocalRing_stalk_of_smooth_over_field sX x
  let φ : k →+* X.presheaf.stalk x := (X.presheaf.germ ⊤ x trivial).hom.comp
    (sX.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)
  have hφ : ∀ a, algebraMap (X.presheaf.stalk x) X.functionField (φ a) =
      baseFunction sX ((Scheme.ΓSpecIso (.of k)).inv.hom a) := fun a =>
    TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf _ _ _
  obtain ⟨Q₁, hQ₁, hQ₁a⟩ := exists_polynomial_mult_le (K := X.functionField) φ s hs
  obtain ⟨Q₂, hQ₂, hQ₂a⟩ :=
    exists_polynomial_isReducedAdjointIdealOn sX hc0 hc1 hJ s hsV hgen
  refine ⟨Q₁ * Q₂, mul_ne_zero hQ₁ hQ₂, fun a ha => ?_⟩
  rw [map_mul] at ha
  obtain ⟨hg0, hmult⟩ := hQ₁a a (left_ne_zero_of_mul ha)
  simp only [hφ] at hg0 hmult
  intro g
  have hgV : g ∈ V := AddSubgroup.sum_mem _ fun i _ => hVk _ _ (hsV i)
  exact ⟨hg0, hQ₂a a (right_ne_zero_of_mul ha) g hgV rfl hg0, hmult⟩

end MMP.Fourfold
