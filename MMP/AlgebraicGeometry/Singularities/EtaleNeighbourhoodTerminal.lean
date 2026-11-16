module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.WeakModel
public import MMP.AlgebraicGeometry.Divisor.Pullback
public import MMP.AlgebraicGeometry.MMP.Fourfold.LocalSetting
public import MMP.AlgebraicGeometry.Divisor.DivisorialValuation
public import MMP.AlgebraicGeometry.Singularities.LogDiscrepancy
public import MMP.AlgebraicGeometry.Divisor.Canonical.Basic
import MMP.AlgebraicGeometry.Singularities.EtaleDiscrepancy
import MMP.AlgebraicGeometry.Divisor.ProductLineQFactorial
import MMP.AlgebraicGeometry.Singularities.DivisorialValuationFiniteRestriction
import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram.GraphDivisorBranchCounts
import MMP.AlgebraicGeometry.Morphisms.ProductWithLine
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.Basic
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
import MMP.AlgebraicGeometry.Morphisms.GenericallyFinite
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Resolution.BlowupSequence.PushforwardSmooth
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback

/-!
# Étale neighbourhoods of terminal varieties and the product local setting

This file collects three local facts from the index-bound part of the termination argument for
projective log canonical fourfolds.

*Étale neighbourhoods of a terminal variety are terminal.* Let `q : U ⟶ Y` be an étale morphism
of normal integral varieties over a field `k`, with `K_Y` `ℚ`-Cartier and `(Y, 0)` terminal.
The morphism `q` is flat, hence open and dominant. For a canonical divisor `K_Y = div ω`, the
divisor `div(q^*ω)` is the pull-back `q^*K_Y` (the tame order formula with ramification index
one); it is a canonical divisor of `U`, and it is `ℚ`-Cartier as a pull-back of a `ℚ`-Cartier
divisor. A proper divisor `D` over `U` realizing a valuation `w` has a divisor `D₀` over `Y`
realizing `w|_{k(Y)}` with the same log discrepancies. The morphism `q` maps the centre of `D` to
that of `D₀`, and a flat, locally quasi-finite morphism preserves coheights, so `D₀` is
exceptional when `D` is. Hence `(U, 0)` is terminal.

*The product local setting.* Let `(Y, π, y)` be a threefold point setting: `Y` is a normal
projective `ℚ`-factorial complex threefold with `(Y, 0)` terminal, `π : Ỹ ⟶ Y` a projective
resolution which is an isomorphism over `Y_reg`, and `y ∈ Sing Y` a closed point. Then
`(Y × ℙ¹, 0, T_y, π × id)` is a local setting, where `T_y = {y} × ℙ¹`. The morphism `π × id` is
the base change of `π` along the projection `Y × ℙ¹ ⟶ Y`, so its base change along
`{y} × V ⟶ Y × ℙ¹`, for any `V ⟶ ℙ¹`, is `F_y × V`, where `F_y = Ỹ ×_Y Spec κ(y)` is the scheme
fibre of `π` over `y` (here `κ(y) = ℂ`). In particular the scheme fibre of `π × id` over a
closed point of `T_y` is `F_y`, the one over the generic point `η` of `T_y` is
`F_y ×_ℂ Spec κ(η)`, and `dim F_y ≤ 2`.

*Log discrepancies of centred valuations.* Let `q : Y_e ⟶ Y_0` be a dominant étale morphism of
normal varieties over a field of characteristic zero, with `Y_0` `ℚ`-Gorenstein, and `η' ∈ Y_e`
with `κ(q η') → κ(η')` an isomorphism. For every normalized divisorial valuation `w` of `k(Y_e)`
with centre `closure {η'}`, `a(w; Y_e, 0) = a(w|_{k(Y_0)}; Y_0, 0)`.

## Main results

* `MMP.Fourfold.IsTerminalVariety.comp_etale`: `U` is a terminal variety, and `K_U = q^* K_Y`
  is a `ℚ`-Cartier canonical divisor.
* `MMP.Fourfold.IsThreefoldPointSetting.isLocalSetting_pullback_projectiveLine`: the product
  local setting and its fibres, stated about the identifications
  `MMP.Fourfold.productPointSettingBaseChangeIso`, `MMP.Fourfold.productPointSettingClosedFibreIso`
  and `MMP.Fourfold.productPointSettingGenericFibreIso`.
* `MMP.Intersection.isLogDiscrepancy_iff_of_etale_of_isCentre`: restriction along an étale map
  preserves log discrepancies of centred valuations.

## Implementation notes

* `U` is structured over `k` by `q ≫ s_Y`. The pull-back `q^* K_Y` is
  `MMP.Mori.QDivisor.IsPullback`, whose condition `(∗)` (the generic point of `U` maps outside
  `Supp K_Y`) is part of the conclusion; it holds because `q` is dominant. The source works over
  `ℂ`; the statement is over any field, since terminality already forces `k` to be algebraically
  closed of characteristic zero (`MMP.Fourfold.IsPair`).
* `ℙ¹_ℂ` is `AlgebraicGeometry.projectiveLine ℂ`; `Y × ℙ¹` and `Ỹ × ℙ¹` are fibre products over
  `Spec ℂ`, structured over `ℂ` through the first projection, and `π × id` is `pullback.map`.
  The integrality, local noetherianity and normality of `Y × ℙ¹`, on which
  `MMP.Fourfold.IsLocalSetting` depends, are part of the conclusion. The curve `T_y` is
  `MMP.Fourfold.pointSettingCurve`; the subscheme `{y} × V` is `Spec κ(y) ×_ℂ V`. Each
  isomorphism is pinned by its compatibility with the projections to `Ỹ` and to the base.
* "`Y_0` is `ℚ`-Gorenstein" is `MMP.Mori.IsPair s₀ 0`, the restriction `w|_{k(Y_0)}` is
  `w.comap (functionFieldMap q)`, and equality of log discrepancies is the equivalence of the
  predicates `MMP.Intersection.IsLogDiscrepancy` for any divisors over `Y_e` and `Y_0`, with
  proper structure maps, realizing `w` and its restriction; this is
  `MMP.Intersection.isLogDiscrepancy_iff_of_etale` applied to `w`.

## References

* [OpenAI, *Termination for projective log canonical fourfolds with rational boundary*][OAI4]
-/

@[expose] public noncomputable section

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

open CategoryTheory

namespace MMP.Fourfold

/-! ## Étale neighbourhoods of a terminal variety -/

section EtaleTerminal

open MMP.Mori
open AlgebraicGeometry hiding PrimeDivisor IsVariety

/-! ### Discrete valuation rings -/

section Algebra

open IsLocalRing KaehlerDifferential TensorProduct

/-- A field map `ι : K₁ → K₂` carrying the image of `A₁` into that of `A₂` restricts to a ring
map `A₁ → A₂`, for `A₂ ⊆ K₂` (a fraction ring). -/
private theorem exists_ringHom_of_range {K₁ K₂ A₁ A₂ : Type*} [Field K₁] [Field K₂] [CommRing A₁]
    [CommRing A₂] [Algebra A₁ K₁] [Algebra A₂ K₂] [IsFractionRing A₂ K₂] (ι : K₁ →+* K₂)
    (h : ∀ a₁ : A₁, ∃ a₂ : A₂, algebraMap A₂ K₂ a₂ = ι (algebraMap A₁ K₁ a₁)) :
    ∃ φ : A₁ →+* A₂, ∀ a, algebraMap A₂ K₂ (φ a) = ι (algebraMap A₁ K₁ a) := by
  choose φ hφ using h
  have inj : Function.Injective (algebraMap A₂ K₂) := IsFractionRing.injective A₂ K₂
  exact ⟨{ toFun := φ
           map_one' := inj (by rw [hφ]; simp)
           map_mul' := fun a b => inj (by rw [hφ]; simp [hφ])
           map_zero' := inj (by rw [hφ]; simp)
           map_add' := fun a b => inj (by rw [hφ]; simp [hφ]) }, hφ⟩

open Polynomial in
/-- **The residue extension of an algebraic extension of valuation rings is algebraic.** Let
`A → B` be a local homomorphism from a discrete valuation ring `A` to a local domain `B`, with
fraction fields `K` of `A` and `L ⊇ B`, compatibly with an algebraic extension `K → L`. Then
`κ(B)` is algebraic over `κ(A)`: an algebraic equation of `b ∈ B` over `A`, divided by its
content, has a unit coefficient, and reduces to a nonzero equation of `b̄` over `κ(A)`. -/
private theorem isAlgebraic_residueField_of_isAlgebraic {A B K L : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDomain B] [IsLocalRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra B L] [Algebra K L] [Algebra.IsAlgebraic K L]
    (hBL : Function.Injective (algebraMap B L))
    (hcomp : ∀ a, algebraMap B L (algebraMap A B a) = algebraMap K L (algebraMap A K a)) :
    Algebra.IsAlgebraic (ResidueField A) (ResidueField B) := by
  classical
  letI : Algebra A L := ((algebraMap K L).comp (algebraMap A K)).toAlgebra
  haveI : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower A B L := IsScalarTower.of_algebraMap_eq fun a => (hcomp a).symm
  letI := UniqueFactorizationMonoid.normalizationMonoid (α := A)
  letI := UniqueFactorizationMonoid.toNormalizedGCDMonoid A
  have hAL : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  have hAB : Function.Injective (algebraMap A B) := by
    intro x y hxy
    apply hAL
    rw [IsScalarTower.algebraMap_apply A B L, hxy, ← IsScalarTower.algebraMap_apply]
  refine ⟨fun y => ?_⟩
  obtain ⟨b, rfl⟩ := residue_surjective y
  obtain ⟨p, hp0, hpb⟩ : IsAlgebraic A (algebraMap B L b) :=
    (IsFractionRing.isAlgebraic_iff A K L).mpr (Algebra.IsAlgebraic.isAlgebraic _)
  have hp : aeval b p = 0 := hBL (by rwa [map_zero, ← aeval_algebraMap_apply])
  set q := p.primPart
  have hq : aeval b q = 0 := by
    have h1 := hp
    rw [p.eq_C_content_mul_primPart, map_mul, aeval_C] at h1
    refine (mul_eq_zero.mp h1).resolve_left ?_
    rw [map_eq_zero_iff _ hAB]
    exact (content_eq_zero_iff).not.mpr hp0
  have hqprim := p.isPrimitive_primPart
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hex : ∃ j, q.coeff j ∉ maximalIdeal A := by
    by_contra hcon
    push Not at hcon
    have hdvd : C ϖ ∣ q := by
      rw [C_dvd_iff_dvd_coeff]
      intro j
      have := hcon j
      rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ,
        Ideal.mem_span_singleton] at this
      exact this
    exact hϖ.not_isUnit (hqprim ϖ hdvd)
  obtain ⟨j, hj⟩ := hex
  refine ⟨q.map (residue A), fun h0 => hj ?_, ?_⟩
  · have := congrArg (fun r => r.coeff j) h0
    simp only [coeff_map, coeff_zero] at this
    exact (residue_eq_zero_iff _).mp this
  · have key : ∀ x : A, algebraMap (ResidueField A) (ResidueField B) (residue A x) =
        residue B (algebraMap A B x) := fun x => rfl
    rw [aeval_def, eval₂_map]
    have : (algebraMap (ResidueField A) (ResidueField B)).comp (residue A) =
        (residue B).comp (algebraMap A B) := RingHom.ext key
    rw [this, ← hom_eval₂, ← aeval_def, hq, map_zero]

/-- If `f` is onto modulo `x₀` (its kernel lies in `R ∙ x₀`) and the `f (y i)` span, then `x₀` and
the `y i` span. -/
private theorem span_cons_eq_top_of_ker_le {R V Q : Type*} [CommRing R] [AddCommGroup V]
    [Module R V] [AddCommGroup Q] [Module R Q] (f : V →ₗ[R] Q) (x₀ : V)
    (hker : LinearMap.ker f ≤ R ∙ x₀)
    {r : ℕ} (y : Fin r → V) (hy : Submodule.span R (Set.range (f ∘ y)) = ⊤) :
    Submodule.span R (Set.range (Fin.cons x₀ y : Fin (r + 1) → V)) = ⊤ := by
  refine eq_top_iff.mpr fun v _ => ?_
  have hv : f v ∈ (Submodule.span R (Set.range y)).map f := by
    rw [Submodule.map_span, ← Set.range_comp, hy]; trivial
  obtain ⟨w, hw, hfw⟩ := hv
  have hsub : Submodule.span R (Set.range y) ≤
      Submodule.span R (Set.range (Fin.cons x₀ y : Fin (r + 1) → V)) :=
    Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨i.succ, by simp⟩)
  have h0 : R ∙ x₀ ≤ Submodule.span R (Set.range (Fin.cons x₀ y : Fin (r + 1) → V)) :=
    Submodule.span_mono (by rintro _ rfl; exact ⟨0, by simp⟩)
  have : v - w ∈ LinearMap.ker f := by simp [hfw]
  have := h0 (hker this)
  simpa using Submodule.add_mem _ this (hsub hw)

/-- The wedge of a spanning family of `n` vectors generates the `n`-th exterior power. -/
private theorem span_singleton_ιMulti_eq_top {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] {n : ℕ} (v : Fin n → M) (hv : Submodule.span R (Set.range v) = ⊤) :
    Submodule.span R {exteriorPower.ιMulti R n v} = ⊤ := by
  refine eq_top_iff.mpr ((exteriorPower.ιMulti_span_of_span R n M hv).symm.le.trans ?_)
  rw [Submodule.span_le]
  rintro _ ⟨a, ha, rfl⟩
  have : ∀ i, ∃ j, v j = a i := fun i => ha (Set.mem_range_self i)
  choose g hg using this
  have ha' : a = v ∘ g := funext fun i => (hg i).symm
  subst ha'
  by_cases hinj : Function.Injective g
  · let σ := Equiv.ofBijective g (Finite.injective_iff_bijective.mp hinj)
    rw [show v ∘ g = v ∘ σ from rfl, AlternatingMap.map_perm]
    exact Submodule.smul_of_tower_mem _ _ (Submodule.mem_span_singleton_self _)
  · simp only [Function.Injective, not_forall] at hinj
    obtain ⟨i, j, hij, hne⟩ := hinj
    rw [AlternatingMap.map_eq_zero_of_eq _ _ (show (v ∘ g) i = (v ∘ g) j by simp [hij]) hne]
    exact Submodule.zero_mem _

/-- Changing the first vector by an element of the span of the others, and scaling it, scales the
wedge. -/
private theorem ιMulti_cons_eq_smul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {r : ℕ} (y : Fin r → M) {x x' : M} (c : R) (hx : x - c • x' ∈ Submodule.span R (Set.range y)) :
    exteriorPower.ιMulti R (r + 1) (Fin.cons x y) =
      c • exteriorPower.ιMulti R (r + 1) (Fin.cons x' y) := by
  let L : M →ₗ[R] ⋀[R]^(r + 1) M :=
    (exteriorPower.ιMulti R (r + 1)).toMultilinearMap.toLinearMap (Fin.cons 0 y) 0
  have hL : ∀ z, L z = exteriorPower.ιMulti R (r + 1) (Fin.cons z y) := fun z => by
    simp [L, MultilinearMap.toLinearMap_apply, Fin.update_cons_zero]
  have hker : Submodule.span R (Set.range y) ≤ LinearMap.ker L := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, hL]
    exact AlternatingMap.map_eq_zero_of_eq _ _ (i := 0) (j := i.succ) (by simp)
      (Fin.succ_ne_zero i).symm
  have := hker hx
  rw [LinearMap.mem_ker, map_sub, map_smul, sub_eq_zero] at this
  rw [← hL, ← hL, this]

/-- For a local ring with principal maximal ideal `(π)`, the kernel of
`κ ⊗ Ω_{R/k} → Ω_{κ/k}` is spanned by `1 ⊗ dπ`. -/
private theorem ker_mapBaseChange_le {k R : Type*} [CommRing k] [CommRing R] [IsLocalRing R]
    [Algebra k R] {π : R} (hπ : maximalIdeal R = Ideal.span {π}) :
    LinearMap.ker (mapBaseChange k R (ResidueField R)) ≤
      (ResidueField R) ∙ ((1 : ResidueField R) ⊗ₜ[R] D k R π) := by
  intro y hy
  obtain ⟨z, rfl⟩ := (exact_kerCotangentToTensor_mapBaseChange k R _ (residue_surjective) y).mp hy
  obtain ⟨⟨x, hx⟩, rfl⟩ := Ideal.toCotangent_surjective _ z
  have hx' : x ∈ maximalIdeal R := by
    rwa [← ker_residue]
  rw [hπ] at hx'
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hx'
  rw [kerCotangentToTensor_toCotangent, Derivation.leibniz, tmul_add, tmul_smul, tmul_smul,
    ← algebraMap_smul (ResidueField R) π, ← algebraMap_smul (ResidueField R) a]
  have : algebraMap R (ResidueField R) π = 0 := by
    rw [← RingHom.mem_ker, IsLocalRing.ResidueField.algebraMap_eq, ker_residue, hπ]
    exact Ideal.mem_span_singleton_self π
  rw [this, zero_smul, add_zero]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- If `R` and its residue field are formally smooth over `k`, then `1 ⊗ dπ ≠ 0` in
`κ ⊗ Ω_{R/k}` for `π ∈ 𝔪 \ 𝔪²`. -/
private theorem tmul_D_ne_zero {k R : Type*} [CommRing k] [CommRing R] [IsLocalRing R]
    [Algebra k R] [Algebra.FormallySmooth k R] [Algebra.FormallySmooth k (ResidueField R)]
    {π : R} (hπ : π ∈ maximalIdeal R) (hπ2 : π ∉ maximalIdeal R ^ 2) :
    ((1 : ResidueField R) ⊗ₜ[R] D k R π) ≠ 0 := by
  obtain ⟨l, hl⟩ := (Algebra.FormallySmooth.iff_split_injection (R := k) (P := R)
    (A := ResidueField R) residue_surjective).mp inferInstance
  intro h0
  have hmem : π ∈ RingHom.ker (algebraMap R (ResidueField R)) := by
    rwa [IsLocalRing.ResidueField.algebraMap_eq, ker_residue]
  have h1 : kerCotangentToTensor k R (ResidueField R)
      ((RingHom.ker (algebraMap R (ResidueField R))).toCotangent ⟨π, hmem⟩) = 0 := by
    rwa [kerCotangentToTensor_toCotangent]
  have h2 := congrArg l h1
  rw [← LinearMap.comp_apply, hl, LinearMap.id_apply, map_zero, Ideal.toCotangent_eq_zero] at h2
  apply hπ2
  have : RingHom.ker (algebraMap R (ResidueField R)) = maximalIdeal R := by
    rw [IsLocalRing.ResidueField.algebraMap_eq, ker_residue]
  rwa [← this]

/-- Nakayama for a free module of rank `r`: `r` vectors spanning `κ ⊗ M` span `M`. -/
private theorem span_eq_top_of_span_tmul {R M : Type*} [CommRing R] [IsLocalRing R] [AddCommGroup M]
    [Module R M] [Module.Finite R M] [Module.Free R M] {r : ℕ} (hr : Module.finrank R M = r)
    (v : Fin r → M)
    (hv : Submodule.span (ResidueField R) (Set.range fun i => (1 : ResidueField R) ⊗ₜ[R] v i) = ⊤) :
    Submodule.span R (Set.range v) = ⊤ := by
  have hfr : Module.finrank (ResidueField R) (ResidueField R ⊗[R] M) = r := by
    rw [Module.finrank_baseChange, hr]
  let b := basisOfTopLeSpanOfCardEqFinrank _ hv.ge (by simp [hfr])
  exact span_eq_top_of_tmul_eq_basis v b (fun i => by simp [b])

/-- **The tame computation.** For a local extension `A → B` of discrete valuation rings over a
field `k` of characteristic zero, with `Ω_{A/k}` and `Ω_{B/k}` free of rank `n` and separable
residue extension, if `t ↦ a s^e` for uniformizers `t`, `s` and a unit `a`, then some generators
of the top forms satisfy `h^* σ_A = w s^{e-1} σ_B` for a unit `w`. -/
private theorem exists_topFormsMap_eq_unit_mul_pow_smul {k A B : Type*} [Field k] [CharZero k]
    [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B] [IsLocalHom (algebraMap A B)]
    [Algebra.FormallySmooth k A] [Algebra.FormallySmooth k (ResidueField A)]
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)]
    [Module.Free A Ω[A⁄k]] [Module.Finite A Ω[A⁄k]] [Module.Free B Ω[B⁄k]] [Module.Finite B Ω[B⁄k]]
    {n : ℕ} (hA : Module.finrank A Ω[A⁄k] = n) (hB : Module.finrank B Ω[B⁄k] = n)
    {t : A} (ht : Irreducible t) {s : B} (hs : Irreducible s) {a : Bˣ} {e : ℕ}
    (he : algebraMap A B t = a * s ^ e) :
    ∃ σA : ⋀[A]^n Ω[A⁄k], Submodule.span A {σA} = ⊤ ∧
      ∃ σB : ⋀[B]^n Ω[B⁄k], Submodule.span B {σB} = ⊤ ∧
        ∃ w : Bˣ, topFormsMap k A B n σA = ((w : B) * s ^ (e - 1)) • σB := by
  classical
  have htm : t ∈ maximalIdeal A := (mem_maximalIdeal t).mpr ht.not_isUnit
  have hmA : maximalIdeal A = Ideal.span {t} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer t).mp ht
  have hmB : maximalIdeal B = Ideal.span {s} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer s).mp hs
  have ht2 : t ∉ maximalIdeal A ^ 2 := by
    rw [hmA, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    rintro ⟨c, hc⟩
    have : t * (1 - t * c) = 0 := by linear_combination hc
    rcases mul_eq_zero.mp this with h | h
    · exact ht.ne_zero h
    · exact ht.not_isUnit (isUnit_iff_exists_inv.mpr ⟨c, by linear_combination -h⟩)
  have hx₀ := tmul_D_ne_zero (k := k) htm ht2
  have hV : Module.finrank (ResidueField A) (ResidueField A ⊗[A] Ω[A⁄k]) = n := by
    rw [Module.finrank_baseChange, hA]
  obtain ⟨r, rfl⟩ : ∃ r, n = r + 1 := Nat.exists_eq_succ_of_ne_zero fun h0 => by
    rw [h0, Module.finrank_zero_iff] at hV
    exact hx₀ (Subsingleton.elim _ _)
  let fA := mapBaseChange k A (ResidueField A)
  have hfA : Function.Surjective fA := mapBaseChange_surjective k A _ residue_surjective
  have hfx₀ : fA ((1 : ResidueField A) ⊗ₜ[A] D k A t) = 0 := by
    simp [fA, mapBaseChange_tmul, (residue_eq_zero_iff t).mpr htm]
  have hkerA : LinearMap.ker fA = ResidueField A ∙ ((1 : ResidueField A) ⊗ₜ[A] D k A t) :=
    le_antisymm (ker_mapBaseChange_le hmA)
      ((Submodule.span_singleton_le_iff_mem _ _).mpr hfx₀)
  have hQ : Module.finrank (ResidueField A) Ω[ResidueField A⁄k] = r := by
    have h := LinearMap.finrank_range_add_finrank_ker fA
    rw [LinearMap.range_eq_top.mpr hfA, finrank_top, hkerA, finrank_span_singleton hx₀, hV] at h
    omega
  have : Module.Finite (ResidueField A) Ω[ResidueField A⁄k] := Module.Finite.of_surjective fA hfA
  have hspanQ : Submodule.span (ResidueField A)
      (Set.range fun x : A => D k (ResidueField A) (algebraMap A (ResidueField A) x)) = ⊤ := by
    refine eq_top_iff.mpr ((span_range_derivation k (ResidueField A)).symm.le.trans
      (Submodule.span_mono ?_))
    rintro _ ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := residue_surjective y
    exact ⟨x, rfl⟩
  obtain ⟨b, hbs, hbspan, hbli⟩ := exists_linearIndependent (ResidueField A)
    (Set.range fun x : A => D k (ResidueField A) (algebraMap A (ResidueField A) x))
  let bb := Module.Basis.mk hbli (by rw [Subtype.range_coe, hbspan, hspanQ])
  have : Finite b := Module.Finite.finite_basis bb
  have : Fintype b := Fintype.ofFinite b
  let eqv : Fin r ≃ b :=
    (Fintype.equivFinOfCardEq (by rw [← Module.finrank_eq_card_basis bb, hQ])).symm
  have hu : ∀ i, ∃ x : A, D k (ResidueField A) (algebraMap A (ResidueField A) x) = (eqv i).1 :=
    fun i => hbs (eqv i).2
  choose u hu using hu
  let bQ : Module.Basis (Fin r) (ResidueField A) Ω[ResidueField A⁄k] := bb.reindex eqv.symm
  have hbQ : ∀ i, bQ i = D k (ResidueField A) (algebraMap A (ResidueField A) (u i)) := fun i => by
    simp only [bQ, bb, Module.Basis.reindex_apply, Module.Basis.mk_apply, Equiv.symm_symm]
    exact (hu i).symm
  have hu' : Submodule.span (ResidueField A)
      (Set.range (fA ∘ fun i => (1 : ResidueField A) ⊗ₜ[A] D k A (u i))) = ⊤ := by
    rw [← bQ.span_eq]
    congr 1
    ext x
    simp [fA, mapBaseChange_tmul, hbQ]
  have hVspan := span_cons_eq_top_of_ker_le fA _ hkerA.le _ hu'
  set vA : Fin (r + 1) → Ω[A⁄k] := Fin.cons (D k A t) fun i => D k A (u i)
  have hvA : Submodule.span A (Set.range vA) = ⊤ := by
    refine span_eq_top_of_span_tmul hA vA ?_
    have : (fun i => (1 : ResidueField A) ⊗ₜ[A] vA i) =
        Fin.cons ((1 : ResidueField A) ⊗ₜ[A] D k A t) fun i => 1 ⊗ₜ[A] D k A (u i) := by
      funext i; cases i using Fin.cases <;> simp [vA]
    rwa [this]
  -- the side of `B`
  have : Algebra.FormallyEtale (ResidueField A) (ResidueField B) :=
    Algebra.FormallyEtale.of_isSeparable _ _
  let fB := mapBaseChange k B (ResidueField B)
  let bQ' := (KaehlerDifferential.isBaseChange_of_formallyEtale k (ResidueField A)
    (ResidueField B)).basis bQ
  have hu'B : Submodule.span (ResidueField B)
      (Set.range (fB ∘ fun i => (1 : ResidueField B) ⊗ₜ[B] D k B (algebraMap A B (u i)))) = ⊤ := by
    rw [← bQ'.span_eq]
    congr 1
    ext x
    simp [fB, bQ', mapBaseChange_tmul, hbQ, IsBaseChange.basis_apply]
  have hWspan := span_cons_eq_top_of_ker_le fB _ (ker_mapBaseChange_le (k := k) hmB) _ hu'B
  set vB : Fin (r + 1) → Ω[B⁄k] := Fin.cons (D k B s) fun i => D k B (algebraMap A B (u i))
  have hvB : Submodule.span B (Set.range vB) = ⊤ := by
    refine span_eq_top_of_span_tmul hB vB ?_
    have : (fun i => (1 : ResidueField B) ⊗ₜ[B] vB i) =
        Fin.cons ((1 : ResidueField B) ⊗ₜ[B] D k B s)
          fun i => 1 ⊗ₜ[B] D k B (algebraMap A B (u i)) := by
      funext i; cases i using Fin.cases <;> simp [vB]
    rwa [this]
  refine ⟨_, span_singleton_ιMulti_eq_top vA hvA, _, span_singleton_ιMulti_eq_top vB hvB, ?_⟩
  rw [topFormsMap_ιMulti]
  have hcomp : (fun i => KaehlerDifferential.map k k A B (vA i)) =
      Fin.cons (D k B (algebraMap A B t)) fun i => D k B (algebraMap A B (u i)) := by
    funext i; cases i using Fin.cases <;> simp [vA]
  rw [hcomp]
  obtain ⟨e, rfl⟩ : ∃ e', e = e' + 1 := Nat.exists_eq_succ_of_ne_zero fun h0 => by
    rw [h0, pow_zero, mul_one] at he
    exact ht.not_isUnit ((isUnit_map_iff (algebraMap A B) t).mp (he ▸ a.isUnit))
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun B).mp
    (hvB ▸ Submodule.mem_top : D k B (a : B) ∈ Submodule.span B (Set.range vB))
  have hsm : s * c 0 ∈ maximalIdeal B :=
    Ideal.mul_mem_right _ _ ((mem_maximalIdeal s).mpr hs.not_isUnit)
  have hek : IsUnit ((e + 1 : ℕ) : B) := by
    have : ((e + 1 : ℕ) : B) = algebraMap k B ((e + 1 : ℕ) : k) := by simp
    rw [this]
    exact (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero e))).map _
  have hw : IsUnit ((a : B) * ((e + 1 : ℕ) : B) + s * c 0) := by
    by_contra h
    have := (maximalIdeal B).sub_mem ((mem_maximalIdeal _).mpr h) hsm
    rw [add_sub_cancel_right, mem_maximalIdeal] at this
    exact this (a.isUnit.mul hek)
  refine ⟨hw.unit, ?_⟩
  rw [IsUnit.unit_spec, Nat.add_sub_cancel]
  apply ιMulti_cons_eq_smul
  rw [he, Derivation.leibniz, Derivation.leibniz_pow, ← hc, Fin.sum_univ_succ]
  have hv0 : vB 0 = D k B s := rfl
  have hvs : ∀ i, vB i.succ = D k B (algebraMap A B (u i)) := fun i => rfl
  simp only [hv0, hvs, Nat.add_sub_cancel]
  have : (a : B) • ((e + 1) • s ^ e • D k B s) +
      s ^ (e + 1) • (c 0 • D k B s + ∑ i : Fin r, c i.succ • D k B (algebraMap A B (u i))) -
      ((↑a * ((e + 1 : ℕ) : B) + s * c 0) * s ^ e) • D k B s =
      s ^ (e + 1) • ∑ i : Fin r, c i.succ • D k B (algebraMap A B (u i)) := by
    rw [← Nat.cast_smul_eq_nsmul B]
    module
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

end Algebra

/-- Pulling a form back along `A → K → K'` agrees with pulling it back along `A → B → K'` when
the two composites `A → K'` agree. -/
private theorem topFormsMap_topFormsMap_eq {k A B K K' : Type*} [CommRing k] [CommRing A]
    [CommRing B] [Field K] [Field K'] [Algebra k A] [Algebra k B] [Algebra k K] [Algebra k K']
    [Algebra A B] [Algebra A K] [Algebra B K'] [Algebra K K'] [IsScalarTower k A B]
    [IsScalarTower k A K] [IsScalarTower k B K'] [IsScalarTower k K K']
    (hφ : ∀ x : A, algebraMap B K' (algebraMap A B x) = algebraMap K K' (algebraMap A K x))
    {n : ℕ} (σ : ⋀[A]^n Ω[A⁄k]) :
    topFormsMap k K K' n (topFormsMap k A K n σ) =
      topFormsMap k B K' n (topFormsMap k A B n σ) := by
  have hΩ : ∀ y : Ω[A⁄k], KaehlerDifferential.map k k K K' (KaehlerDifferential.map k k A K y) =
      KaehlerDifferential.map k k B K' (KaehlerDifferential.map k k A B y) := by
    intro y
    have hy : y ∈ Submodule.span A (Set.range (KaehlerDifferential.D k A)) := by
      rw [KaehlerDifferential.span_range_derivation]; trivial
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      simp [hφ]
    | zero => simp
    | add x y _ _ hx hy => simp only [map_add, hx, hy]
    | smul a x _ hx =>
      have e1 : KaehlerDifferential.map k k A K (a • x) =
          algebraMap A K a • KaehlerDifferential.map k k A K x := by
        rw [map_smul, algebraMap_smul]
      have e2 : KaehlerDifferential.map k k A B (a • x) =
          algebraMap A B a • KaehlerDifferential.map k k A B x := by
        rw [map_smul, algebraMap_smul]
      rw [e1, e2, map_smul, map_smul, hx, ← algebraMap_smul K' (algebraMap A K a),
        ← algebraMap_smul K' (algebraMap A B a), hφ]
  have hs : σ ∈ Submodule.span A (Set.range (exteriorPower.ιMulti A n)) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    simp only [topFormsMap_ιMulti, hΩ]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul a x _ hx =>
    have e1 : topFormsMap k A K n (a • x) = algebraMap A K a • topFormsMap k A K n x := by
      rw [map_smul, algebraMap_smul]
    have e2 : topFormsMap k A B n (a • x) = algebraMap A B a • topFormsMap k A B n x := by
      rw [map_smul, algebraMap_smul]
    rw [e1, e2, map_smul, map_smul, hx, ← algebraMap_smul K' (algebraMap A K a),
      ← algebraMap_smul K' (algebraMap A B a), hφ]

/-- The order along a prime divisor of `u ϖ^n`, for a unit `u` and a uniformizer `ϖ`, is `n`. -/
private theorem ord_algebraMap_unit_mul_pow {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (E : PrimeDivisor Y) {ϖ : E.localRing} (hϖ : Irreducible ϖ)
    (w : E.localRingˣ) (n : ℕ) :
    Y.ord (algebraMap E.localRing Y.functionField (w * ϖ ^ n)) E.genericPoint = n := by
  have := E.isDiscreteValuationRing_localRing
  have hϖ0 : algebraMap E.localRing Y.functionField ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hϖ.ne_zero
  have h1 : Y.ord (algebraMap E.localRing Y.functionField ϖ) E.genericPoint = 1 := by
    have := E.divisorialValuation_algebraMap_of_irreducible hϖ
    rw [E.divisorialValuation_eq_exp_neg_ord hϖ0] at this
    have := WithZero.exp_injective this
    omega
  have hw0 : algebraMap E.localRing Y.functionField w ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr w.ne_zero
  rw [map_mul, map_pow, Scheme.ord_mul hw0 (pow_ne_zero _ hϖ0),
    E.ord_algebraMap_of_isUnit w.isUnit, ← zpow_natCast, ord_zpow _ hϖ0, h1]
  ring

/-- If `v_{E'}(x') = v_E(x) ^ e` for nonzero rational functions `x`, `x'`, then
`ord_{E'}(x') = e · ord_E(x)`. -/
private theorem ord_eq_mul_of_divisorialValuation_eq_pow {Y Y' : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y']
    (E : PrimeDivisor Y) (E' : PrimeDivisor Y') {x : Y.functionField} {x' : Y'.functionField}
    {e : ℕ} (h : E'.divisorialValuation x' = E.divisorialValuation x ^ e) (hx : x ≠ 0)
    (hx' : x' ≠ 0) : Y'.ord x' E'.genericPoint = e * Y.ord x E.genericPoint := by
  rw [E'.divisorialValuation_eq_exp_neg_ord hx', E.divisorialValuation_eq_exp_neg_ord hx,
    ← WithZero.exp_nsmul, WithZero.exp_inj, smul_neg, nsmul_eq_mul] at h
  linear_combination -h

section CanonicalDivisorExistence

open Opposite TopologicalSpace

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X]

/-- A nonempty open subscheme of an integral scheme has the same function field. -/
private theorem functionFieldMap_opens_ι_bijective {Y : Scheme.{u}} [IsIntegral Y] (V : Y.Opens)
    [Nonempty V] [IsDominant V.ι] : Function.Bijective (functionFieldMap V.ι) :=
  functionFieldMap_bijective_of_isOpenImmersion V.ι ⊤ ⟨Classical.arbitrary V, trivial⟩

/-- A nonempty open subscheme of a normal variety is a normal variety. -/
private theorem isNormalVariety_ι {Y : Scheme.{u}} {s : Y ⟶ Spec (.of k)}
    (h : IsNormalVariety k s) (V : Y.Opens) [Nonempty V] : IsNormalVariety k (V.ι ≫ s) := by
  have := h.1
  have := h.2
  have : IsIntegral Y := h.1.toIsIntegral
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace s
  have : IsNoetherian Y := {}
  exact ⟨⟨⟩, inferInstance⟩

/-- The divisorial valuation of a prime divisor `E'` of an open subscheme `V ⊆ Y` is that of its
closure `E` in `Y`, through the identification `k(Y) ≅ k(V)`. -/
private theorem divisorialValuation_primeDivisorMap {Y V : Scheme.{u}} [IsIntegral Y]
    [IsIntegral V] [IsLocallyNoetherian Y] [IsLocallyNoetherian V] [IsNormal Y] [IsNormal V]
    (j : V ⟶ Y) [IsOpenImmersion j] [IsDominant j] (E' : MMP.Mori.PrimeDivisor V) :
    MMP.Mori.PrimeDivisor.divisorialValuation (OpenWeilRestriction.primeDivisorMap j E') =
      E'.divisorialValuation.comap (functionFieldMap j) := by
  ext g
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  have hg' : functionFieldMap j g ≠ 0 := (map_ne_zero _).2 hg
  rw [Valuation.comap_apply, MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg,
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg',
    MMP.Positivity.ord_functionFieldMap_of_isIso j E' _
      (OpenWeilRestriction.genericPoint_primeDivisorMap j E').symm]

/-- A nonempty open subscheme of a variety has the dimension of the variety: both are the
transcendence degree of the common function field. -/
private theorem topologicalKrullDim_opens_eq (hX : IsNormalVariety k sX) (U : X.Opens)
    [Nonempty U] [IsDominant U.ι] : topologicalKrullDim U = topologicalKrullDim X := by
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hbij := functionFieldMap_opens_ι_bijective U
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (U.ι ≫ sX)
  rw [← toENat_trdeg_functionField (sX := U.ι ≫ sX),
    ← trdeg_functionField_eq_of_bijective sX U.ι hbij, toENat_trdeg_functionField (sX := sX)]

/-! ### The divisorial sheaf on an open subscheme -/

section DivisorialRestrict

/-- On an irreducible scheme every irreducible component is the whole space. -/
private theorem eq_univ_of_irreducibleComponents {Y : Scheme.{u}} [IrreducibleSpace Y]
    (Z : irreducibleComponents Y) : Z.1 = Set.univ :=
  Set.eq_univ_of_univ_subset
    (Z.2.2 (IrreducibleSpace.isIrreducible_univ Y) (Set.subset_univ _))

private theorem index_eq {Y : Scheme.{u}} [IrreducibleSpace Y] {W : Y.Opens}
    (Z Z' : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) : Z = Z' :=
  Subtype.ext (Subtype.ext ((eq_univ_of_irreducibleComponents _).trans
    (eq_univ_of_irreducibleComponents _).symm))

private theorem specializes_genericPoint {Y : Scheme.{u}} [IsIntegral Y]
    (Z : irreducibleComponents Y) : componentGenericPoint Y Z ⤳ genericPoint Y :=
  (Inseparable.of_eq (componentGenericPoint_eq_genericPoint Z)).specializes

private theorem stalkSpecializes_self_apply {Y : Scheme.{u}} {x : Y} (h : x ⤳ x)
    (s : Y.presheaf.stalk x) : (Y.presheaf.stalkSpecializes h).hom s = s := by
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  rfl

/-- The value in the function field of a section of `𝒦_Y` over an open set, read at the generic
point of an irreducible component meeting it. -/
private def evFF {Y : Scheme.{u}} [IsIntegral Y] {W : Y.Opens}
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (Z : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) : Y.functionField :=
  (Y.presheaf.stalkSpecializes (genericPoint_specializes _)).hom (φ Z)

private theorem evFF_eq {Y : Scheme.{u}} [IsIntegral Y] {W : Y.Opens}
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (Z Z' : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) :
    evFF φ Z = evFF φ Z' := by
  obtain rfl := index_eq Z Z'
  rfl

private theorem stalkSpecializes_injective {Y : Scheme.{u}} [IsIntegral Y]
    (Z : irreducibleComponents Y) :
    Function.Injective
      (Y.presheaf.stalkSpecializes (genericPoint_specializes (componentGenericPoint Y Z))).hom := by
  intro a b h
  have := congrArg (Y.presheaf.stalkSpecializes (specializes_genericPoint Z)).hom h
  rwa [TopCat.Presheaf.stalkSpecializes_comp_apply,
    TopCat.Presheaf.stalkSpecializes_comp_apply, stalkSpecializes_self_apply,
    stalkSpecializes_self_apply] at this

/-- `v_E` on the factor `𝒪_{Y,η}` of `𝒦_Y` is the inverse of the divisorial valuation of the
corresponding rational function. -/
private theorem valuation_eq_inv_divisorialValuation {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (E : MMP.Mori.PrimeDivisor Y)
    (s : Y.presheaf.stalk (componentGenericPoint Y E.component)) :
    E.valuation s = (E.divisorialValuation
      ((Y.presheaf.stalkSpecializes (genericPoint_specializes _)).hom s))⁻¹ := by
  rw [MMP.Threefold.Mori.Helpers.valuation_eq_ordFrac,
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_inv_ordHom, inv_inv]
  rfl

private theorem ordGE_iff {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (E : MMP.Mori.PrimeDivisor Y) (n : ℤ)
    (s : Y.presheaf.stalk (componentGenericPoint Y E.component)) :
    E.OrdGE n s ↔
      ((Y.presheaf.stalkSpecializes (genericPoint_specializes _)).hom s = 0 ∨
        WithZero.exp n ≤ (E.divisorialValuation
          ((Y.presheaf.stalkSpecializes (genericPoint_specializes _)).hom s))⁻¹) := by
  rw [MMP.Mori.PrimeDivisor.OrdGE, valuation_eq_inv_divisorialValuation,
    (injective_iff_map_eq_zero' _).1 (stalkSpecializes_injective E.component)]

private theorem ordGE_iff_evFF {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (E : MMP.Mori.PrimeDivisor Y) (n : ℤ) {W : Y.Opens}
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (h : componentGenericPoint Y E.component ∈ W) :
    E.OrdGE n (φ ⟨E.component, h⟩) ↔
      (evFF φ ⟨E.component, h⟩ = 0 ∨
        WithZero.exp n ≤ (E.divisorialValuation (evFF φ ⟨E.component, h⟩))⁻¹) :=
  ordGE_iff E n _

variable (U : X.Opens) [Nonempty U] [IsDominant U.ι]

private theorem genericPoint_mem_of_index {V : U.toScheme.Opens}
    (Z : {Z : irreducibleComponents U.toScheme // componentGenericPoint U.toScheme Z ∈ V}) :
    genericPoint U.toScheme ∈ V := by
  have := Z.2
  rwa [componentGenericPoint_eq_genericPoint] at this

private theorem genericPoint_mem_of_indexX {V : U.toScheme.Opens}
    (Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U.ι ''ᵁ V}) :
    genericPoint U.toScheme ∈ V := by
  have h := Z.2
  rw [componentGenericPoint_eq_genericPoint] at h
  obtain ⟨x, hx, hxe⟩ := h
  have hsp : genericPoint U.toScheme ⤳ x := (genericPoint_spec U.toScheme).specializes trivial
  exact hsp.mem_open V.isOpen hx

/-- The irreducible component `Set.univ` of an irreducible scheme `Y`. -/
private def topComponent (Y : Scheme.{u}) [IrreducibleSpace Y] : irreducibleComponents Y :=
  ⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; rfl⟩

private def indexX {V : U.toScheme.Opens} (h : genericPoint U.toScheme ∈ V) :
    {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U.ι ''ᵁ V} :=
  ⟨topComponent X, by
    rw [componentGenericPoint_eq_genericPoint, ← map_genericPoint_of_isDominant U.ι]
    exact ⟨_, h, rfl⟩⟩

private def indexU {V : U.toScheme.Opens} (h : genericPoint U.toScheme ∈ V) :
    {Z : irreducibleComponents U.toScheme // componentGenericPoint U.toScheme Z ∈ V} :=
  ⟨topComponent U.toScheme, by rwa [componentGenericPoint_eq_genericPoint]⟩

/-- The restriction `𝒦_X(U ∩ -) → 𝒦_U` of rational functions to an open subscheme, through the
identification `k(X) ≅ k(U)`. -/
private def restrictRF (V : U.toScheme.Opens)
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    ToType ((rationalFunctionsPresheaf U.toScheme).obj (op V)) :=
  fun Z => (U.toScheme.presheaf.stalkSpecializes (specializes_genericPoint Z.1)).hom
    (functionFieldMap U.ι (evFF ψ (indexX U (genericPoint_mem_of_index U Z))))

private theorem evFF_restrictRF (V : U.toScheme.Opens)
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V))))
    (Z : {Z : irreducibleComponents U.toScheme // componentGenericPoint U.toScheme Z ∈ V})
    (Z' : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U.ι ''ᵁ V}) :
    evFF (restrictRF U V ψ) Z = functionFieldMap U.ι (evFF ψ Z') := by
  rw [evFF, restrictRF, TopCat.Presheaf.stalkSpecializes_comp_apply,
    stalkSpecializes_self_apply, evFF_eq ψ _ Z']

private theorem restrictRF_injective (V : U.toScheme.Opens) :
    Function.Injective (restrictRF U V) := by
  intro ψ₁ ψ₂ h
  funext Z'
  have hV := genericPoint_mem_of_indexX U Z'
  have h1 := congrArg (fun φ => evFF φ (indexU U hV)) h
  simp only [evFF_restrictRF U V _ _ Z'] at h1
  exact stalkSpecializes_injective Z'.1 ((functionFieldMap U.ι).injective h1)

private theorem restrictRF_surjective (V : U.toScheme.Opens) :
    Function.Surjective (restrictRF U V) := by
  intro φ
  let e := RingEquiv.ofBijective (functionFieldMap U.ι) (functionFieldMap_opens_ι_bijective U)
  refine ⟨fun Z' => (X.presheaf.stalkSpecializes (specializes_genericPoint Z'.1)).hom
    (e.symm (evFF φ (indexU U (genericPoint_mem_of_indexX U Z')))), ?_⟩
  funext Z
  change (U.toScheme.presheaf.stalkSpecializes (specializes_genericPoint Z.1)).hom
    (functionFieldMap U.ι ((X.presheaf.stalkSpecializes (genericPoint_specializes _)).hom
      ((X.presheaf.stalkSpecializes (specializes_genericPoint _)).hom (e.symm _)))) = _
  rw [TopCat.Presheaf.stalkSpecializes_comp_apply, stalkSpecializes_self_apply]
  change (U.toScheme.presheaf.stalkSpecializes (specializes_genericPoint Z.1)).hom
    (e (e.symm _)) = _
  rw [RingEquiv.apply_symm_apply, evFF_eq φ _ Z, evFF,
    TopCat.Presheaf.stalkSpecializes_comp_apply, stalkSpecializes_self_apply]

/-- A section of `𝒦_X` over `U ∩ -` is a section of `𝒪_X(D)` exactly when its restriction is a
section of `𝒪_U(D|_U)`: the prime divisors of `U` meeting `V` are the restrictions of those of
`X` meeting `V`, with the same valuations and coefficients. -/
private theorem isDivisorialSection_restrictRF_iff (D : Divisor X) (V : U.toScheme.Opens)
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    Divisor.IsDivisorialSection (D.restrictOpen U) V (restrictRF U V ψ) ↔
      D.IsDivisorialSection (U.ι ''ᵁ V) ψ := by
  have key : ∀ (E' : MMP.Mori.PrimeDivisor U.toScheme) (hE' : (E'.support ∩ V).Nonempty)
      (hP : ((OpenWeilRestriction.primeDivisorMap U.ι E').support ∩ U.ι ''ᵁ V).Nonempty),
      E'.OrdGE (-(D.restrictOpen U).coeff E')
          (restrictRF U V ψ ⟨E'.component, E'.componentGenericPoint_mem_of_nonempty hE'⟩) ↔
        MMP.Mori.PrimeDivisor.OrdGE (OpenWeilRestriction.primeDivisorMap U.ι E')
          (-D.coeff (OpenWeilRestriction.primeDivisorMap U.ι E'))
          (ψ ⟨_, MMP.Mori.PrimeDivisor.componentGenericPoint_mem_of_nonempty
            (OpenWeilRestriction.primeDivisorMap U.ι E') hP⟩) := by
    intro E' hE' hP
    rw [ordGE_iff_evFF, ordGE_iff_evFF]
    rw [evFF_restrictRF U V ψ _ ⟨_, MMP.Mori.PrimeDivisor.componentGenericPoint_mem_of_nonempty
        (OpenWeilRestriction.primeDivisorMap U.ι E') hP⟩,
      divisorialValuation_primeDivisorMap, map_eq_zero_iff _ (functionFieldMap U.ι).injective,
      DivisorWithCoeffs.coeff_restrictOpen]
    rfl
  have hmem : ∀ E' : MMP.Mori.PrimeDivisor U.toScheme, (E'.support ∩ V).Nonempty ↔
      ((OpenWeilRestriction.primeDivisorMap U.ι E').support ∩ U.ι ''ᵁ V).Nonempty := by
    intro E'
    rw [← MMP.Mori.PrimeDivisor.genericPoint_mem_iff, ← MMP.Mori.PrimeDivisor.genericPoint_mem_iff,
      show MMP.Mori.PrimeDivisor.genericPoint (OpenWeilRestriction.primeDivisorMap U.ι E') =
        U.ι E'.genericPoint from OpenWeilRestriction.genericPoint_primeDivisorMap _ _]
    refine ⟨fun h => ⟨_, h, rfl⟩, ?_⟩
    rintro ⟨x, hx, hxe⟩
    rwa [U.ι.isOpenEmbedding.injective hxe] at hx
  constructor
  · intro h P hP
    have hPU : P.genericPoint ∈ Set.range U.ι.base := by
      rw [Scheme.Opens.range_ι]
      obtain ⟨x, -, hx⟩ := (MMP.Mori.PrimeDivisor.genericPoint_mem_iff P _).2 hP
      exact hx ▸ x.2
    obtain ⟨E', rfl⟩ := (OpenWeilRestriction.mem_range_primeDivisorMap_iff _ P).2 hPU
    exact (key E' ((hmem E').2 hP) hP).1 (h E' ((hmem E').2 hP))
  · intro h E' hE'
    exact (key E' hE' ((hmem E').1 hE')).2 (h _ ((hmem E').1 hE'))

private theorem functionFieldMap_germ_appIso_inv (V : U.toScheme.Opens) (r : Γ(U.toScheme, V))
    (h₁ : genericPoint X ∈ U.ι ''ᵁ V) (h₂ : genericPoint U.toScheme ∈ V) :
    functionFieldMap U.ι (X.presheaf.germ (U.ι ''ᵁ V) (genericPoint X) h₁
      ((U.ι.appIso V).inv r)) = U.toScheme.presheaf.germ V (genericPoint U.toScheme) h₂ r := by
  have h₃ : U.ι (genericPoint U.toScheme) ∈ U.ι ''ᵁ V := ⟨_, h₂, rfl⟩
  rw [functionFieldMap, CommRingCat.comp_apply, TopCat.Presheaf.stalkCongr_hom]
  erw [TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf h₁ _]
  erw [Scheme.Hom.germ_stalkMap_apply, ← CommRingCat.comp_apply (U.ι.appIso V).inv,
    Scheme.Hom.appIso_inv_app, TopCat.Presheaf.germ_res_apply]

private theorem restrictRF_smul (V : U.toScheme.Opens) (r : Γ(U.toScheme, V))
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    restrictRF U V ((U.ι.appIso V).inv r • ψ) = r • restrictRF U V ψ := by
  funext Z
  rw [rationalFunctions_smul_apply]
  simp only [restrictRF, evFF, rationalFunctions_smul_apply, map_mul]
  congr 1
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply, functionFieldMap_germ_appIso_inv U V r _
    (genericPoint_mem_of_index U Z), TopCat.Presheaf.germ_stalkSpecializes_apply]

private theorem restrictRF_zero (V : U.toScheme.Opens) : restrictRF U V 0 = 0 := by
  funext Z
  simp only [restrictRF, evFF]
  erw [Pi.zero_apply, map_zero, map_zero, map_zero]
  rfl

private theorem restrictRF_add (V : U.toScheme.Opens)
    (ψ₁ ψ₂ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    restrictRF U V (ψ₁ + ψ₂) = restrictRF U V ψ₁ + restrictRF U V ψ₂ := by
  funext Z
  simp only [restrictRF, evFF]
  erw [Pi.add_apply, map_add, map_add, map_add]
  rfl

/-- The restriction `𝒪_X(D)|_U ⟶ 𝒪_U(D|_U)` of divisorial sections to an open subscheme. -/
private def divisorialSheafRestrictHom (D : Divisor X) :
    D.divisorialSheaf.restrict U.ι ⟶ Divisor.divisorialSheaf (D.restrictOpen U) :=
  ⟨PresheafOfModules.homMk
    { app V := AddCommGrpCat.ofHom
        { toFun ψ := (⟨restrictRF U V.unop (ψ : D.divisorialSubmodule (U.ι ''ᵁ V.unop)).1,
            (isDivisorialSection_restrictRF_iff U D V.unop _).2
              (ψ : D.divisorialSubmodule (U.ι ''ᵁ V.unop)).2⟩ :
              Divisor.divisorialSubmodule (D.restrictOpen U) V.unop)
          map_zero' := Subtype.ext (restrictRF_zero U V.unop)
          map_add' ψ₁ ψ₂ := Subtype.ext (restrictRF_add U V.unop _ _) }
      naturality V V' i := by ext ψ; rfl }
    fun V r ψ => Subtype.ext (restrictRF_smul U V.unop r _)⟩

private theorem isIso_divisorialSheafRestrictHom (D : Divisor X) :
    IsIso (divisorialSheafRestrictHom U D) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro V
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun (ψ₁ ψ₂ : D.divisorialSubmodule (U.ι ''ᵁ V)) h => ?_, fun φ => ?_⟩
  · have h' : restrictRF U V ψ₁.1 = restrictRF U V ψ₂.1 := congrArg Subtype.val h
    exact Subtype.ext (restrictRF_injective U V h')
  · obtain ⟨ψ, hψ⟩ :=
      restrictRF_surjective U V (φ : Divisor.divisorialSubmodule (D.restrictOpen U) V).1
    refine ⟨(⟨ψ, (isDivisorialSection_restrictRF_iff U D V ψ).1
      (hψ ▸ (φ : Divisor.divisorialSubmodule (D.restrictOpen U) V).2)⟩ :
        D.divisorialSubmodule (U.ι ''ᵁ V)), Subtype.ext hψ⟩

end DivisorialRestrict

/-- The divisorial sheaf of the restriction `D|_U` of a divisor to an open subscheme is the
restriction `𝒪_X(D)|_U` of its divisorial sheaf. -/
private theorem nonempty_divisorialSheaf_restrictOpen_iso (D : Divisor X) (U : X.Opens)
    [Nonempty U] [IsDominant U.ι] :
    Nonempty (Divisor.divisorialSheaf (D.restrictOpen U) ≅ D.divisorialSheaf.restrict U.ι) :=
  ⟨(@asIso _ _ _ _ _ (isIso_divisorialSheafRestrictHom U D)).symm⟩

/-- Relative differential forms restrict along an open immersion: for `ψ : Z ⟶ Y` an open
immersion and `p' = ψ ≫ p`, `(Ω^n_{Y/S})|_Z ≅ Ω^n_{Z/S}`. -/
private theorem nonempty_restrict_relativeDifferentialForms_iso {Y Z S : Scheme.{u}}
    (ψ : Z ⟶ Y) [IsOpenImmersion ψ] (p : Y ⟶ S) (p' : Z ⟶ S) (h : ψ ≫ p = p') (n : ℤ) :
    Nonempty ((Scheme.Hom.relativeDifferentialForms p n).restrict ψ ≅
      Scheme.Hom.relativeDifferentialForms p' n) := by
  have hc : ψ ≫ p = p' ≫ 𝟙 S := by rw [h, Category.comp_id]
  have := Scheme.Hom.isIso_relativeDifferentialFormsMap_of_etale ψ p p' (𝟙 S) hc n
  exact ⟨(Scheme.Modules.restrictFunctorIsoPullback ψ).app _ ≪≫
    asIso (Scheme.Hom.relativeDifferentialFormsMap ψ p p' (𝟙 S) hc n)⟩

/-- **A normal variety over a perfect field has a canonical divisor.** On the smooth locus
`T = S_sm`, which contains the generic point, the canonical sheaf is `𝒪_T(K_T)` for a divisor
`K_T` of `T`; its closure `K_S` in `S` restricts to `K_T` on `T`, so
`𝒪_S(K_S)|_T ≅ 𝒪_T(K_T) ≅ ω_T`. -/
private theorem exists_isCanonicalDivisor {K : Type u} [Field K] [PerfectField K]
    {S : Scheme.{u}} (sS : S ⟶ Spec (.of K)) [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    [CompactSpace S] (hS : IsNormalVariety K sS) {n : ℕ} (hn : topologicalKrullDim S = n) :
    ∃ KS : MMP.Mori.Divisor S, KS.IsCanonicalDivisor sS n := by
  haveI : LocallyOfFiniteType sS := hS.1.toLocallyOfFiniteType
  set T := MMP.Mori.smoothLocus sS
  have hTeq : T = sS.smoothLocus := MMP.Mori.smoothLocus_eq_smoothLocus sS
  haveI : Nonempty T := ⟨⟨genericPoint S, hTeq ▸ sS.genericPoint_mem_smoothLocus_of_perfectField⟩⟩
  haveI : IsDominant T.ι := Opens.isDominant_ι (T.isOpen.dense ⟨_, (Classical.arbitrary T).2⟩)
  have hTv : IsNormalVariety K (T.ι ≫ sS) := isNormalVariety_ι hS T
  haveI : MMP.Mori.IsVariety K (T.ι ≫ sS) := hTv.1
  haveI : QuasiCompact (T.ι ≫ sS) := hTv.1.toQuasiCompact
  haveI : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace (T.ι ≫ sS)
  have hsm : MMP.Mori.IsSmoothScheme (T.ι ≫ sS) := by
    rw [MMP.Mori.isSmoothScheme_iff, ← Scheme.Hom.smoothLocus_eq_top_iff,
      ← Scheme.Hom.preimage_smoothLocus_eq, ← hTeq, Scheme.Opens.ι_preimage_self]
  have hdimT : topologicalKrullDim T = n :=
    (topologicalKrullDim_opens_eq hS T).trans hn
  obtain ⟨KT, hKT⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (T.ι ≫ sS) hsm hdimT
  classical
  let KS : MMP.Mori.Divisor S := Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap T.ι) KT
  have hKS : KS.restrictOpen T = KT := by
    ext W
    rw [MMP.Mori.DivisorWithCoeffs.coeff_restrictOpen]
    exact Finsupp.mapDomain_apply_of_injective (OpenWeilRestriction.primeDivisorMap_injective T.ι) KT W
  obtain ⟨e₀⟩ := nonempty_divisorialSheaf_restrictOpen_iso KS T
  set T' := MMP.Mori.smoothLocus (T.ι ≫ sS)
  obtain ⟨e₁⟩ := nonempty_restrict_relativeDifferentialForms_iso T'.ι
    (T.ι ≫ sS) (T'.ι ≫ T.ι ≫ sS) rfl n
  obtain ⟨e₂⟩ := MMP.Flips.nonempty_iso_of_restrict_iso (M := KT.divisorialSheaf)
    (N := Scheme.Hom.relativeDifferentialForms (T.ι ≫ sS) n) hsm (hKT.iso ≪≫ e₁.symm)
  refine ⟨KS, hn, ⟨e₀.symm ≪≫ ?_ ≪≫ e₂⟩⟩
  rw [hKS]

end CanonicalDivisorExistence

/-! ### Function fields and forms -/

section Forms

/-- A dominant, locally quasi-finite morphism of integral schemes, locally of finite type,
induces a finite extension of function fields: the generic point of the source is the only point
over the generic point of the target. -/
private theorem finite_functionField {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (h : Y ⟶ X)
    [IsDominant h] [LocallyQuasiFinite h] [LocallyOfFiniteType h] :
    letI := functionFieldMapAlgebra h
    Module.Finite X.functionField Y.functionField := by
  have hgen : ∀ x : Y, h x = genericPoint X → x = genericPoint Y := fun x hx => by
    have hsp := genericPoint_specializes x
    have h₀ : h (genericPoint Y) = genericPoint X :=
      ((hx ▸ hsp.map h.continuous).antisymm (genericPoint_specializes _)).eq
    exact (MMP.Flips.eq_of_specializes_of_locallyQuasiFinite h hsp (h₀.trans hx.symm)).symm
  have H := (trdeg_functionField_eq_zero_iff_finite h).mp
    (trdeg_functionField_eq_zero_of_eq_genericPoint h hgen)
  convert H using 3
  exact congrArg RingHom.toAlgebra (dominantFunctionFieldMap_eq_functionFieldMap h).symm

/-- The pull-back of a nonzero form along a pull-back generator is nonzero. -/
private theorem pullbackForms_ne_zero {k K K' : Type*} [CommRing k] [Field K] [Field K']
    [Algebra k K] [Algebra k K'] [Algebra K K'] [IsScalarTower k K K'] {d : ℕ}
    {ω : ⋀[K]^d Ω[K⁄k]} (hω : IsPullbackGenerator K' ω) {m : ℤ} {τ : PluriForms k K d m}
    (hτ : τ ≠ 0) : pullbackForms (K' := K') m τ ≠ 0 := by
  intro h0
  have h1 := repr_pullbackFormsAlong hω m τ
  rw [← pullbackForms_eq hω m τ, h0] at h1
  simp only [map_zero, Finsupp.zero_apply] at h1
  exact repr_ne_zero_of_ne_zero _ hτ ((map_eq_zero_iff _ (algebraMap K K').injective).mp h1.symm)

/-- The pull-back `ι^*τ` of rational `m`-canonical forms along a `k`-embedding
`ι : k(Y) → k(Y')` of function fields. -/
private def pullbackAlong {k : Type u} [Field k] {Y Y' : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) (sY' : Y' ⟶ Spec (.of k)) [IsIntegral Y] [IsIntegral Y']
    (ι : Y.functionField →+* Y'.functionField)
    (hι : letI := functionFieldAlgebra sY; letI := functionFieldAlgebra sY'
      ∀ c : k, algebraMap k Y'.functionField c = ι (algebraMap k Y.functionField c))
    {d : ℕ} {m : ℤ} (τ : RationalPluriForms sY d m) : RationalPluriForms sY' d m :=
  letI := functionFieldAlgebra sY
  letI := functionFieldAlgebra sY'
  letI := ι.toAlgebra
  haveI : IsScalarTower k Y.functionField Y'.functionField := IsScalarTower.of_algebraMap_eq hι
  pullbackForms (K := Y.functionField) (K' := Y'.functionField) m τ

/-- **The tame canonical-order formula along an extension of discrete valuations.** Let `Y`,
`Y'` be normal varieties of dimension `n` over a field `k` of characteristic zero, `ι` a
`k`-embedding `k(Y) → k(Y')` of their function fields, and `E`, `E'` prime divisors with
`v_{E'} ∘ ι = v_E ^ e`. Then every nonzero rational `m`-canonical form `τ` of `Y` satisfies
`ord_{E'}(ι^* τ) = e · ord_E(τ) + m (e - 1)`. -/
private theorem ordForm_pullbackAlong_eq {k : Type u} [Field k] [CharZero k]
    {Y Y' : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) (sY' : Y' ⟶ Spec (.of k))
    [IsIntegral Y] [IsIntegral Y'] [IsLocallyNoetherian Y] [IsLocallyNoetherian Y']
    [IsNormal Y] [IsNormal Y'] (hY : IsNormalVariety k sY) (hY' : IsNormalVariety k sY')
    {n : ℕ} (hd : letI := functionFieldAlgebra sY; (Algebra.trdeg k Y.functionField).toNat = n)
    (hd' : letI := functionFieldAlgebra sY'; (Algebra.trdeg k Y'.functionField).toNat = n)
    (htr : letI := functionFieldAlgebra sY; letI := functionFieldAlgebra sY'
      Algebra.trdeg k Y.functionField = Algebra.trdeg k Y'.functionField)
    (ι : Y.functionField →+* Y'.functionField)
    (hι : letI := functionFieldAlgebra sY; letI := functionFieldAlgebra sY'
      ∀ c : k, algebraMap k Y'.functionField c = ι (algebraMap k Y.functionField c))
    (E : PrimeDivisor Y) (E' : PrimeDivisor Y') {e : ℕ}
    (he : ∀ g, E'.divisorialValuation (ι g) = E.divisorialValuation g ^ e)
    {m : ℤ} {τ : RationalPluriForms sY n m} (hτ : τ ≠ 0) :
    E'.ordForm (pullbackAlong sY sY' ι hι τ) = e * E.ordForm τ + m * (e - 1) := by
  classical
  letI := functionFieldAlgebra sY
  letI := functionFieldAlgebra sY'
  letI := ι.toAlgebra
  haveI : IsScalarTower k Y.functionField Y'.functionField := IsScalarTower.of_algebraMap_eq hι
  haveI : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType sY' := hY'.1.toLocallyOfFiniteType
  haveI := essFiniteType_functionField (sX := sY)
  haveI : Algebra.IsAlgebraic Y.functionField Y'.functionField := isAlgebraic_of_trdeg_eq k htr
  letI := stalkAlgebra sY E.genericPoint
  letI := stalkAlgebra sY' E'.genericPoint
  haveI := isScalarTower_stalk_functionField sY E.genericPoint
  haveI := isScalarTower_stalk_functionField sY' E'.genericPoint
  haveI := E.isDiscreteValuationRing_localRing
  haveI := E'.isDiscreteValuationRing_localRing
  obtain ⟨_, _⟩ := E.formallySmooth_localRing (sX := sY)
  obtain ⟨_, _⟩ := E.free_kaehlerDifferential_localRing (sX := sY)
  obtain ⟨_, _⟩ := E'.free_kaehlerDifferential_localRing (sX := sY')
  have hrkA := (E.finrank_kaehlerDifferential_localRing (sX := sY)).trans hd
  have hrkB := (E'.finrank_kaehlerDifferential_localRing (sX := sY')).trans hd'
  have he0 : e ≠ 0 := by
    rintro rfl
    simpa using he 0
  have hord : ∀ g : Y.functionField, g ≠ 0 →
      Y'.ord (algebraMap Y.functionField Y'.functionField g) E'.genericPoint =
        e * Y.ord g E.genericPoint := fun g hg =>
    ord_eq_mul_of_divisorialValuation_eq_pow E E' (he g) hg ((map_ne_zero _).mpr hg)
  -- the local extension `𝒪_{Y,E} → 𝒪_{Y',E'}`
  obtain ⟨φ, hφ⟩ := exists_ringHom_of_range (A₁ := E.localRing) (A₂ := E'.localRing)
    (algebraMap Y.functionField Y'.functionField) fun a => by
      have h1 : E.divisorialValuation (algebraMap E.localRing Y.functionField a) ≤ 1 :=
        (E.divisorialValuation_le_one_iff _).mpr ⟨a, rfl⟩
      have h2 : E'.divisorialValuation (algebraMap Y.functionField Y'.functionField
          (algebraMap E.localRing Y.functionField a)) ≤ 1 := by
        change E'.divisorialValuation (ι _) ≤ 1
        rw [he]
        exact (pow_le_one_iff he0).mpr h1
      obtain ⟨b, hb⟩ := (E'.divisorialValuation_le_one_iff _).mp h2
      exact ⟨b, hb⟩
  letI : Algebra E.localRing E'.localRing := φ.toAlgebra
  have hφ' : ∀ x : E.localRing, algebraMap E'.localRing Y'.functionField
      (algebraMap E.localRing E'.localRing x) =
        algebraMap Y.functionField Y'.functionField (algebraMap E.localRing Y.functionField x) :=
    hφ
  haveI : IsScalarTower k E.localRing E'.localRing := by
    refine IsScalarTower.of_algebraMap_eq fun c =>
      IsFractionRing.injective E'.localRing Y'.functionField ?_
    rw [hφ', ← IsScalarTower.algebraMap_apply k E.localRing Y.functionField,
      ← IsScalarTower.algebraMap_apply k Y.functionField Y'.functionField,
      ← IsScalarTower.algebraMap_apply k E'.localRing Y'.functionField]
  haveI : IsLocalHom (algebraMap E.localRing E'.localRing) := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have h1 : E.divisorialValuation (algebraMap E.localRing Y.functionField a) < 1 :=
      (E.divisorialValuation_algebraMap_lt_one_iff a).mpr
        ((IsLocalRing.mem_maximalIdeal a).mpr hna)
    have h2 : E'.divisorialValuation (algebraMap E'.localRing Y'.functionField
        (algebraMap E.localRing E'.localRing a)) < 1 := by
      rw [hφ']
      change E'.divisorialValuation (ι _) < 1
      rw [he]
      exact (pow_lt_one_iff he0).mpr h1
    exact (IsLocalRing.mem_maximalIdeal _).mp
      ((E'.divisorialValuation_algebraMap_lt_one_iff _).mp h2) ha
  haveI : Algebra.FormallySmooth k (IsLocalRing.ResidueField E.localRing) := by
    haveI : Algebra.EssFiniteType k (IsLocalRing.ResidueField E.localRing) :=
      Algebra.EssFiniteType.comp k E.localRing _
    exact Algebra.FormallySmooth.of_perfectField
  haveI : Algebra.IsAlgebraic (IsLocalRing.ResidueField E.localRing)
      (IsLocalRing.ResidueField E'.localRing) :=
    isAlgebraic_residueField_of_isAlgebraic (K := Y.functionField) (L := Y'.functionField)
      (IsFractionRing.injective _ _) hφ'
  haveI : CharZero (IsLocalRing.ResidueField E.localRing) :=
    charZero_of_injective_algebraMap (algebraMap k _).injective
  haveI : Algebra.IsSeparable (IsLocalRing.ResidueField E.localRing)
      (IsLocalRing.ResidueField E'.localRing) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  -- uniformizers and the ramification index
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible E.localRing
  obtain ⟨s, hs⟩ := IsDiscreteValuationRing.exists_irreducible E'.localRing
  have hϖ1 : Y.ord (algebraMap E.localRing Y.functionField ϖ) E.genericPoint = 1 := by
    simpa using ord_algebraMap_unit_mul_pow E hϖ 1 1
  have hϖ0 : algebraMap E.localRing Y.functionField ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hϖ.ne_zero
  have hφϖ : algebraMap E.localRing E'.localRing ϖ ≠ 0 := by
    intro h0
    have := hφ' ϖ
    rw [h0, map_zero, eq_comm, map_eq_zero_iff _ (RingHom.injective _)] at this
    exact hϖ0 this
  obtain ⟨e₀, a, ha⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hφϖ hs
  have he₀ : e₀ = e := by
    have h1 := hord _ hϖ0
    rw [← hφ', ha, ord_algebraMap_unit_mul_pow E' hs, hϖ1, mul_one] at h1
    exact_mod_cast h1
  -- the top forms
  obtain ⟨σA, hσA, σB, hσB, w, hw⟩ :=
    exists_topFormsMap_eq_unit_mul_pow_smul (k := k) hrkA hrkB hϖ hs ha
  have h0A := E.topFormsMap_ne_zero (sX := sY) hd hσA
  have h0B := E'.topFormsMap_ne_zero (sX := sY') hd' hσB
  rw [E.ordForm_eq τ hσA h0A, E'.ordForm_eq _ hσB h0B]
  set c : Y'.functionField := algebraMap E'.localRing Y'.functionField (w * s ^ (e₀ - 1))
    with hc_def
  have hc : c ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
      (mul_ne_zero w.ne_zero (pow_ne_zero _ hs.ne_zero))
  have hcomp : topFormsMap k Y.functionField Y'.functionField n
      (topFormsMap k E.localRing Y.functionField n σA) =
      c • topFormsMap k E'.localRing Y'.functionField n σB := by
    rw [topFormsMap_topFormsMap_eq hφ', hw, map_smul, algebraMap_smul]
  have hωA : IsPullbackGenerator Y'.functionField
      (topFormsMap k E.localRing Y.functionField n σA) :=
    ⟨span_singleton_topFormsMap (nonZeroDivisors _) hσA, by
      rw [hcomp, Submodule.span_singleton_smul_eq (IsUnit.mk0 c hc),
        span_singleton_topFormsMap (nonZeroDivisors _) hσB], by
      rw [hcomp]
      exact smul_ne_zero hc h0B⟩
  have hpb : pullbackAlong sY sY' ι hι τ = pullbackFormsAlong hωA m τ := pullbackForms_eq hωA m τ
  rw [hpb]
  have hb : basisOfSpanSingleton hωA.2.1 hωA.2.2 () =
      c • topFormsBasis E'.localRing hσB h0B () := by
    simp [hcomp]
  have key := ZTensorPower.basis_repr_of_eq_smul hb m (pullbackFormsAlong hωA m τ)
  have hr := repr_pullbackFormsAlong hωA m τ
  have hfB : formCoeff E'.localRing hσB h0B (pullbackFormsAlong hωA m τ) =
      c ^ m * algebraMap Y.functionField Y'.functionField
        (formCoeff E.localRing hσA h0A τ) := by
    have h1 : formCoeff E'.localRing hσB h0B (pullbackFormsAlong hωA m τ) =
        c ^ m * (ZTensorPower.basis (basisOfSpanSingleton hωA.2.1 hωA.2.2) m).repr
          (pullbackFormsAlong hωA m τ) () := by
      unfold formCoeff
      rw [key, ← mul_assoc, mul_inv_cancel₀ (zpow_ne_zero m hc), one_mul]
    rw [h1, hr]
    rfl
  have hf : formCoeff E.localRing hσA h0A τ ≠ 0 := fun h0 =>
    hτ ((formCoeff_eq_zero_iff hσA h0A _).mp h0)
  rw [hfB, Scheme.ord_mul (zpow_ne_zero _ hc) ((map_ne_zero _).mpr hf), MMP.Mori.ord_zpow _ hc,
    hord _ hf, hc_def, ord_algebraMap_unit_mul_pow E' hs, he₀,
    Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr he0)]
  push_cast
  ring

end Forms

/-! ### Centres and pull-backs of Cartier divisors -/

section Centre

/-- **The centre upstairs lies over the centre downstairs.** If `D'` is a divisor over `Y` and
`D` one over a variety `X`, with `v_{D'} ∘ h^* = v_D`, then `h` maps the centre of `D'` on `Y`
to the centre of `D` on `X`. -/
private theorem map_center_eq_of_valuation_comp_eq {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} (h : Y ⟶ X) [IsIntegral X] [IsIntegral Y] [IsDominant h]
    (hX : MMP.Mori.IsVariety k sX) {D : DivisorOver k sX} {D' : DivisorOver k (h ≫ sX)}
    (he : ∀ g, D'.valuation (functionFieldMap h g) = D.valuation g) :
    h (D'.f D'.E.genericPoint) = D.f D.E.genericPoint := by
  haveI := hX.toIsSeparated
  refine (MMP.Positivity.DivisorOver.eq_of_dominates sX D.valuation (x := D.f D.E.genericPoint)
    (x' := h (D'.f D'.E.genericPoint))
    (MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D _ rfl)
    (MMP.Positivity.DivisorOver.valuation_algebraMap_lt_one D _ rfl) (fun a => ?_)
    (fun a ha => ?_)).symm
  · have h1 := MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D' _ rfl
      ((h.stalkMap (D'.f D'.E.genericPoint)).hom a)
    rwa [← functionFieldMap_algebraMap_stalk, he] at h1
  · have hmem : (h.stalkMap (D'.f D'.E.genericPoint)).hom a ∈ IsLocalRing.maximalIdeal _ :=
      (IsLocalRing.mem_maximalIdeal _).2 fun hu =>
        (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit _ _ hu)
    have h1 := MMP.Positivity.DivisorOver.valuation_algebraMap_lt_one D' _ rfl _ hmem
    rwa [← functionFieldMap_algebraMap_stalk, he] at h1

end Centre

/-! ### Function fields of the same transcendence degree -/

section TrDeg

/-- A dominant, locally quasi-finite morphism of integral `k`-schemes, locally of finite type,
preserves the transcendence degree of the function field, since `k(Y)` is finite over `k(X)`. -/
private theorem trdeg_functionField_eq_of_locallyQuasiFinite {k : Type u} [Field k]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (h : Y ⟶ X) [IsIntegral X] [IsIntegral Y]
    [IsDominant h] [LocallyQuasiFinite h] [LocallyOfFiniteType h] :
    letI := functionFieldAlgebra sX
    letI := functionFieldAlgebra (h ≫ sX)
    Algebra.trdeg k X.functionField = Algebra.trdeg k Y.functionField := by
  letI := functionFieldAlgebra sX
  letI := functionFieldAlgebra (h ≫ sX)
  letI := functionFieldMapAlgebra h
  haveI := isScalarTower_functionFieldMap sX h
  haveI := finite_functionField h
  haveI : Algebra.IsAlgebraic X.functionField Y.functionField := Algebra.IsAlgebraic.of_finite _ _
  have h1 := trdeg_add_eq k X.functionField (A := Y.functionField)
  rwa [(trdeg_eq_zero_iff (R := X.functionField) (A := Y.functionField)).mpr inferInstance,
    add_zero] at h1

/-- Integral schemes of finite type over a field whose function fields have the same
transcendence degree have the same dimension. -/
private theorem topologicalKrullDim_eq_of_trdeg_eq {k : Type u} [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [IsIntegral X] [IsIntegral Y]
    [LocallyOfFiniteType sX] [LocallyOfFiniteType sY]
    (htr : letI := functionFieldAlgebra sX; letI := functionFieldAlgebra sY
      Algebra.trdeg k X.functionField = Algebra.trdeg k Y.functionField) :
    topologicalKrullDim Y = topologicalKrullDim X := by
  letI := functionFieldAlgebra sX
  letI := functionFieldAlgebra sY
  have htr' : Algebra.trdeg k X.functionField = Algebra.trdeg k Y.functionField := htr
  rw [← toENat_trdeg_functionField (sX := sY), ← htr', toENat_trdeg_functionField (sX := sX)]

end TrDeg

/-! ### Étale morphisms and prime divisors -/

section Etale

open IsLocalRing

/-- **Unramified extensions of a discrete valuation ring.** Let `A → B` be a local,
formally unramified, essentially finite type homomorphism of local rings, with `A` a discrete
valuation ring and `B` a Noetherian domain. If a uniformizer `ϖ` of `A` does not vanish in `B`,
then the image of `ϖ` is irreducible in `B`. -/
private theorem irreducible_algebraMap_of_formallyUnramified {A B : Type*} [CommRing A]
    [CommRing B] [IsDomain A] [IsDiscreteValuationRing A] [IsDomain B] [IsNoetherianRing B]
    [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
    [Algebra.FormallyUnramified A B] [Algebra.EssFiniteType A B] {ϖ : A} (hϖ : Irreducible ϖ)
    (h0 : algebraMap A B ϖ ≠ 0) : Irreducible (algebraMap A B ϖ) := by
  have hmax : maximalIdeal B = Ideal.span {algebraMap A B ϖ} := by
    rw [← Algebra.FormallyUnramified.map_maximalIdeal (R := A),
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.map_span,
      Set.image_singleton]
  have hnf : ¬ IsField B := by
    rwa [isField_iff_maximalIdeal_eq, hmax, Ideal.span_singleton_eq_bot]
  have : IsDiscreteValuationRing B :=
    ((IsDiscreteValuationRing.TFAE B hnf).out 5 1).1 (⟨⟨_, hmax⟩⟩ : (maximalIdeal B).IsPrincipal)
  exact (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 hmax

/-- The local ring of a normal locally Noetherian integral scheme at the generic point of a
prime divisor `E` is a discrete valuation ring, with a uniformizer of `ord_E`-value `exp (-1)`. -/
private theorem exists_irreducible_divisorialValuation_eq {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (E : PrimeDivisor X) {z : X}
    (hz : z = E.genericPoint) :
    IsDiscreteValuationRing (X.presheaf.stalk z) ∧ ∃ ϖ : X.presheaf.stalk z, Irreducible ϖ ∧
      E.divisorialValuation (algebraMap _ X.functionField ϖ) = WithZero.exp (-1) := by
  subst hz
  have := E.isDiscreteValuationRing_localRing
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible E.localRing
  exact ⟨this, ϖ, hϖ, E.divisorialValuation_algebraMap_of_irreducible hϖ⟩

/-- `ord_E` is centred at the generic point of `E`: it is `≤ 1` on `𝒪_{X,E}` and `< 1` on its
maximal ideal. -/
private theorem divisorialValuation_centre {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (E : PrimeDivisor X) {z : X}
    (hz : z = E.genericPoint) :
    (∀ a : X.presheaf.stalk z, E.divisorialValuation (algebraMap _ X.functionField a) ≤ 1) ∧
      ∀ a ∈ maximalIdeal (X.presheaf.stalk z),
        E.divisorialValuation (algebraMap _ X.functionField a) < 1 := by
  subst hz
  exact ⟨fun a => (E.divisorialValuation_le_one_iff _).2 ⟨a, rfl⟩,
    fun a ha => (E.divisorialValuation_algebraMap_lt_one_iff a).2 ha⟩

/-- **Flat, locally quasi-finite morphisms preserve coheights.** Such a morphism is strictly
monotone for the specialization order (distinct points of a fibre are not specializations of
one another) and generizations lift along it. -/
private theorem coheight_apply_eq {X Y : Scheme.{u}} (h : Y ⟶ X) [Flat h]
    [LocallyQuasiFinite h] (y : Y) : Order.coheight (h y) = Order.coheight y := by
  refine (Order.coheight_eq_of_strictMono (⇑h) (fun a b hab => ?_) (fun a b hab => ?_) y).symm
  · have hba : b ⤳ a := Scheme.le_iff_specializes.mp hab.le
    refine lt_of_le_not_ge (Scheme.le_iff_specializes.mpr (hba.map h.continuous)) fun hle => ?_
    have heq : h b = h a :=
      ((hba.map h.continuous).antisymm (Scheme.le_iff_specializes.mp hle)).eq
    exact hab.ne (MMP.Flips.eq_of_specializes_of_locallyQuasiFinite h hba heq).symm
  · obtain ⟨a', ha', rfl⟩ := Flat.generalizingMap h (Scheme.le_iff_specializes.mp hab.le)
    refine ⟨a', lt_of_le_not_ge (Scheme.le_iff_specializes.mpr ha') fun hle => ?_, rfl⟩
    have heq : a' = a := (ha'.antisymm (Scheme.le_iff_specializes.mp hle)).eq
    rw [heq] at hab
    exact lt_irrefl _ hab

/-- **Prime divisors along an étale morphism.** Let `h : Y ⟶ X` be a dominant étale morphism of
normal locally Noetherian integral schemes and `Γ'` a prime divisor of `Y`. Then `h(η_{Γ'})` is
the generic point of a prime divisor `Γ` of `X`, and `v_{Γ'} ∘ h^* = v_Γ`: the local ring
`𝒪_{X,Γ} ⟶ 𝒪_{Y,Γ'}` is formally unramified, so a uniformizer of `𝒪_{X,Γ}` stays one. -/
private theorem exists_primeDivisor_divisorialValuation_eq {X Y : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (h : Y ⟶ X) [Etale h] [IsDominant h] (Γ' : PrimeDivisor Y) :
    ∃ Γ : PrimeDivisor X, Γ.genericPoint = h Γ'.genericPoint ∧
      ∀ g, Γ'.divisorialValuation (functionFieldMap h g) = Γ.divisorialValuation g := by
  have hco : Order.coheight (h Γ'.genericPoint) = 1 :=
    (coheight_apply_eq h _).trans Γ'.coheight_genericPoint
  let Γ : PrimeDivisor X := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco
  have hΓ : Γ.genericPoint = h Γ'.genericPoint :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
  refine ⟨Γ, hΓ, fun g => ?_⟩
  obtain ⟨hAdvr, ϖ, hϖ, hϖv⟩ := exists_irreducible_divisorialValuation_eq Γ hΓ.symm
  let φ := (h.stalkMap Γ'.genericPoint).hom
  letI : Algebra (X.presheaf.stalk (h Γ'.genericPoint)) (Y.presheaf.stalk Γ'.genericPoint) :=
    φ.toAlgebra
  have : Algebra.FormallyUnramified (X.presheaf.stalk (h Γ'.genericPoint))
      (Y.presheaf.stalk Γ'.genericPoint) :=
    AlgebraicGeometry.FormallyUnramified.stalkMap (f := h) _
  have : Algebra.EssFiniteType (X.presheaf.stalk (h Γ'.genericPoint))
      (Y.presheaf.stalk Γ'.genericPoint) :=
    LocallyOfFiniteType.stalkMap (f := h) _
  have : IsLocalHom (algebraMap (X.presheaf.stalk (h Γ'.genericPoint))
      (Y.presheaf.stalk Γ'.genericPoint)) := inferInstanceAs (IsLocalHom φ)
  have hφϖ : φ ϖ ≠ 0 := by
    intro h0
    have := MMP.Mori.functionFieldMap_algebraMap_stalk h Γ'.genericPoint ϖ
    rw [show (h.stalkMap Γ'.genericPoint).hom ϖ = 0 from h0, map_zero,
      map_eq_zero_iff _ (RingHom.injective _),
      map_eq_zero_iff _ (IsFractionRing.injective _ _)] at this
    exact hϖ.ne_zero this
  have hirr : Irreducible (φ ϖ) := irreducible_algebraMap_of_formallyUnramified hϖ hφϖ
  obtain ⟨hv1, hv2⟩ := divisorialValuation_centre Γ hΓ.symm
  have hw : Γ'.divisorialValuation.comap (functionFieldMap h) = Γ.divisorialValuation := by
    refine MMP.Positivity.DivisorOver.valuation_eq_of_isDiscreteValuationRing
      (R := X.presheaf.stalk (h Γ'.genericPoint)) (fun a => ?_) (fun a ha => ?_)
      ⟨algebraMap _ X.functionField ϖ, ?_⟩ hv1 hv2 ⟨_, hϖv⟩
    · rw [Valuation.comap_apply, MMP.Mori.functionFieldMap_algebraMap_stalk]
      exact (Γ'.divisorialValuation_le_one_iff _).2 ⟨_, rfl⟩
    · rw [Valuation.comap_apply, MMP.Mori.functionFieldMap_algebraMap_stalk]
      exact (Γ'.divisorialValuation_algebraMap_lt_one_iff _).2 (map_nonunit φ a ha)
    · rw [Valuation.comap_apply, MMP.Mori.functionFieldMap_algebraMap_stalk]
      exact Γ'.divisorialValuation_algebraMap_of_irreducible hirr
  exact congrArg (fun v => v g) hw

end Etale

/-- The coefficients of an integral divisor `M` with `M = m (K + B)` as `ℚ`-divisors. -/
private theorem coeff_eq_of_toQDivisor_eq_smul {X : Scheme.{u}} {M K : Divisor X}
    {B : QDivisor X} {m : ℕ} (hM : Divisor.toQDivisor M = (m : ℤ) • (Divisor.toQDivisor K + B))
    (Γ : PrimeDivisor X) : (M.coeff Γ : ℝ) = m * ((K.coeff Γ : ℝ) + (B.coeff Γ : ℝ)) := by
  have h1 := congrArg (fun G : QDivisor X => G.coeff Γ) hM
  simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add,
    zsmul_eq_mul, Int.cast_natCast] at h1
  exact_mod_cast h1

/-! ### The étale comparison -/

/-- **Orders of forms along an étale morphism.** Let `q : Yₑ ⟶ Y₀` be a dominant étale morphism
of normal varieties over a field of characteristic zero, and `Γ'`, `Γ` prime divisors of `Yₑ`,
`Y₀` with `v_{Γ'} ∘ q^* = v_Γ`. Then `ord_{Γ'}(q^*ω) = ord_Γ(ω)` for every nonzero rational top
form `ω` of `Y₀`: this is the tame formula with ramification index one. -/
private theorem ordForm_pullbackRationalPluriForms_of_etale {k : Type u} [Field k] [CharZero k]
    {Y₀ Yₑ : Scheme.{u}} [IsIntegral Y₀] [IsLocallyNoetherian Y₀] [IsNormal Y₀]
    [IsIntegral Yₑ] [IsLocallyNoetherian Yₑ] [IsNormal Yₑ]
    (s₀ : Y₀ ⟶ Spec (.of k)) (q : Yₑ ⟶ Y₀) [Etale q] [IsDominant q]
    (h₀ : IsNormalVariety k s₀) (hₑ : IsNormalVariety k (q ≫ s₀)) {n : ℕ}
    (hn : topologicalKrullDim Y₀ = n) {ω : RationalPluriForms s₀ n 1} (hω : ω ≠ 0)
    {Γ' : PrimeDivisor Yₑ} {Γ : PrimeDivisor Y₀}
    (hval : ∀ g, Γ'.divisorialValuation (functionFieldMap q g) = Γ.divisorialValuation g) :
    Γ'.ordForm (pullbackRationalPluriForms s₀ q ω) = Γ.ordForm ω := by
  haveI : LocallyOfFiniteType s₀ := h₀.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (q ≫ s₀) := hₑ.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType q := locallyOfFiniteType_of_comp q s₀
  have htr := trdeg_functionField_eq_of_locallyQuasiFinite s₀ q
  have hdimₑ := (topologicalKrullDim_eq_of_trdeg_eq s₀ (q ≫ s₀) htr).trans hn
  letI := functionFieldAlgebra s₀
  letI := functionFieldAlgebra (q ≫ s₀)
  letI := functionFieldMapAlgebra q
  haveI := isScalarTower_functionFieldMap s₀ q
  refine (ordForm_pullbackAlong_eq s₀ (q ≫ s₀) h₀ hₑ
    (toNat_trdeg_functionField_of_topologicalKrullDim_eq hn)
    (toNat_trdeg_functionField_of_topologicalKrullDim_eq hdimₑ) htr (functionFieldMap q)
    (IsScalarTower.algebraMap_apply k Y₀.functionField Yₑ.functionField) Γ Γ' (e := 1)
    (by simpa using hval) hω).trans ?_
  simp

/-- **The canonical divisor along an étale morphism.** Let `q : Yₑ ⟶ Y₀` be a dominant étale
morphism of normal varieties over a field of characteristic zero and `K_{Y₀} = div ω`. Then
`div(q^*ω)` is the pull-back of `K_{Y₀}`: the pull-back of a Cartier multiple `M = m K_{Y₀}` has,
along a prime divisor `Γ'` over `Γ`, the coefficient `ord_Γ(M) = m ord_Γ(ω) = m ord_{Γ'}(q^*ω)`. -/
private theorem isPullback_divisorOfForm_pullbackRationalPluriForms {k : Type u} [Field k]
    [CharZero k] {Y₀ Yₑ : Scheme.{u}} [IsIntegral Y₀] [IsLocallyNoetherian Y₀] [IsNormal Y₀]
    [IsIntegral Yₑ] [IsLocallyNoetherian Yₑ] [IsNormal Yₑ] [CompactSpace Yₑ]
    (s₀ : Y₀ ⟶ Spec (.of k)) (q : Yₑ ⟶ Y₀) [Etale q] [IsDominant q]
    [LocallyOfFiniteType (q ≫ s₀)]
    (h₀ : IsNormalVariety k s₀) (hₑ : IsNormalVariety k (q ≫ s₀)) {n : ℕ}
    (hn : topologicalKrullDim Y₀ = n) {ω : RationalPluriForms s₀ n 1} (hω0 : ω ≠ 0)
    {K₀ : Divisor Y₀} (hω : ∀ Γ, Γ.ordForm ω = K₀.coeff Γ) :
    ∃ hB, (Divisor.toQDivisor K₀ + 0).IsPullback q hB
      (Divisor.toQDivisor (divisorOfForm (pullbackRationalPluriForms s₀ q ω)) + 0) := by
  refine ⟨fun Z hZ => ?_, fun m hm M hM hMc => ?_⟩
  · rw [← QDivisor.supp_eq_of_toQDivisor_eq (D := K₀) (m := 1) one_ne_zero (by simp)] at hZ
    exact MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp q K₀ Z hZ
  obtain ⟨M', hM'⟩ := MMP.Threefold.Bridges.exists_isPullback_of_isDominant q hMc
  refine ⟨M', ?_, hM'⟩
  suffices M' = (m : ℤ) • divisorOfForm (pullbackRationalPluriForms s₀ q ω) by
    rw [this, add_zero, map_zsmul]
  refine DivisorWithCoeffs.ext' fun Γ' => ?_
  obtain ⟨Γ, hΓ, hval⟩ := exists_primeDivisor_divisorialValuation_eq q Γ'
  obtain ⟨U, hU, φ, hφ⟩ := hMc (q Γ'.genericPoint)
  have hg : MMP.Threefold.Mori.Helpers.evalFF Γ.component (φ : RationalFunctions Y₀) ≠ 0 :=
    (φ.isUnit.map _).ne_zero
  have hMK : (M.coeff Γ : ℝ) = m * K₀.coeff Γ := by
    simpa using coeff_eq_of_toQDivisor_eq_smul hM Γ
  have hMΓ : M.coeff Γ = Y₀.ord (MMP.Threefold.Mori.Helpers.evalFF Γ.component
      (φ : RationalFunctions Y₀)) Γ.genericPoint := by
    rw [hφ Γ ((Γ.genericPoint_mem_iff U).mp (hΓ ▸ hU)),
      MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord]
  rw [DivisorWithCoeffs.coeff_smul, smul_eq_mul, coeff_divisorOfForm,
    MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF hM' hφ Γ' hU Γ.component,
    ord_eq_mul_of_divisorialValuation_eq_pow Γ Γ' (e := 1) (by rw [pow_one]; exact hval _) hg
      ((map_ne_zero _).mpr hg), ← hMΓ,
    ordForm_pullbackRationalPluriForms_of_etale s₀ q h₀ hₑ hn hω0 hval, hω Γ]
  push_cast
  rw [one_mul]
  exact_mod_cast hMK

/-! ### Exceptional divisors -/

/-- A divisor over a normal variety is exceptional if and only if the image of the generic point
of the divisor has coheight at least two. -/
private theorem isExceptional_iff_two_le_coheight {k : Type u} [Field k] {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX) (D : DivisorOver k sX) :
    D.IsExceptional ↔ 2 ≤ Order.coheight (D.f D.E.genericPoint) := by
  have := D.isLocallyNoetherian
  have := D.isNormal
  have : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated (X ↘ ⊤_ Scheme) := by
    rw [show (X ↘ ⊤_ Scheme) = sX ≫ (Spec (.of k) ↘ ⊤_ Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  unfold DivisorOver.IsExceptional
  rw [MMP.Positivity.isExceptional_toRationalMap_iff]
  have hcl : TopologicalSpace.Closeds.closure (D.f '' (D.E.idealSheaf.support : Set D.Y)) =
      ⟨(D.center : Set X), D.center.isClosed⟩ := TopologicalSpace.Closeds.ext rfl
  rw [hcl, closedsCodimension_coe, MMP.Positivity.DivisorOver.codimension_center]

/-! ### Canonical divisors and divisors over an étale neighbourhood -/

/-- **Canonical divisors along an étale morphism.** Let `q : U ⟶ Y` be a dominant étale morphism
of normal varieties over a field of characteristic zero, with `K_Y` `ℚ`-Cartier. For every
canonical divisor `K_Y = div ω` of `Y`, the divisor `K_U = div(q^*ω)` is a canonical divisor of
`U`, it is the pull-back `q^*K_Y`, and it is `ℚ`-Cartier. -/
private theorem exists_isCanonicalDivisor_isPullback_of_etale {k : Type u} [Field k] [CharZero k]
    {U Y : Scheme.{u}} [IsIntegral U] [IsLocallyNoetherian U] [IsNormal U]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of k)} (q : U ⟶ Y) [Etale q] [IsDominant q]
    (hU : IsNormalVariety k (q ≫ sY)) (h₀ : MMP.Mori.IsPair sY (0 : QDivisor Y))
    {n : ℕ} {KY : Divisor Y} (hKY : KY.IsCanonicalDivisor sY n) :
    ∃ (hq : ∀ Z : irreducibleComponents U,
        q (componentGenericPoint U Z) ∉ (Divisor.toQDivisor KY).supp)
      (KU : Divisor U), KU.IsCanonicalDivisor (q ≫ sY) n ∧
        (Divisor.toQDivisor KY).IsPullback q hq (Divisor.toQDivisor KU) ∧
        (Divisor.toQDivisor KU).IsQCartier := by
  have hX₀ : IsNormalVariety k sY := h₀.1
  haveI : LocallyOfFiniteType sY := hX₀.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (q ≫ sY) := hU.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType q := locallyOfFiniteType_of_comp q sY
  haveI : CompactSpace Y := haveI := hX₀.1; QuasiCompact.compactSpace_of_compactSpace sY
  haveI : CompactSpace U := haveI := hU.1; QuasiCompact.compactSpace_of_compactSpace (q ≫ sY)
  have hn : topologicalKrullDim Y = n := hKY.topologicalKrullDim_eq
  have hdimU : topologicalKrullDim U = n :=
    (topologicalKrullDim_eq_of_trdeg_eq sY (q ≫ sY)
      (trdeg_functionField_eq_of_locallyQuasiFinite sY q)).trans hn
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX₀ hKY
  have hω' : pullbackRationalPluriForms sY q ω ≠ 0 := by
    letI := functionFieldAlgebra sY
    letI := functionFieldAlgebra (q ≫ sY)
    letI := functionFieldMapAlgebra q
    haveI := isScalarTower_functionFieldMap sY q
    obtain ⟨ωg, hωg⟩ := exists_isPullbackGenerator_of_topologicalKrullDim_eq sY q hn hdimU
    exact pullbackForms_ne_zero hωg hω0
  obtain ⟨KU₀, hKU₀⟩ := exists_isCanonicalDivisor (q ≫ sY) hU hdimU
  have hKcan : (divisorOfForm (pullbackRationalPluriForms sY q ω)).IsCanonicalDivisor
      (q ≫ sY) n :=
    hKU₀.of_linearlyEquivalent (by
      simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hU hKU₀ hω')
  obtain ⟨n₀, K₀, hK₀, hQ₀⟩ := h₀.2
  obtain ⟨hB, hpull⟩ :=
    isPullback_divisorOfForm_pullbackRationalPluriForms sY q hX₀ hU hn hω0 hω
  have hQU : (Divisor.toQDivisor (divisorOfForm (pullbackRationalPluriForms sY q ω)) +
      0).IsQCartier := by
    obtain ⟨m, hm, M, hM, hMc⟩ := (hQ₀.add_of_linearlyEquivalent
      (MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sY hX₀ hK₀ hKY)).exists_pos
    obtain ⟨M', hM', hMpb⟩ := hpull m hm M hM hMc
    exact ⟨m, by exact_mod_cast hm.ne', M', hM', hMpb.isCartier hMc⟩
  revert hB hQU
  rw [add_zero, add_zero]
  intro hB hpull hQU
  exact ⟨hB, _, hKcan, hpull, hQU⟩

/-- **Divisors over an étale neighbourhood.** Let `q : U ⟶ Y` be a dominant étale morphism of
normal varieties over a field of characteristic zero, with `K_Y` `ℚ`-Cartier. Every proper divisor
`D` over `U` has a divisor `D₀` over `Y` with the same log discrepancies, which is exceptional
whenever `D` is: `q` maps the centre of `D` to that of `D₀` and preserves coheights. -/
private theorem exists_divisorOver_isLogDiscrepancy_iff_of_etale {k : Type u} [Field k]
    [CharZero k] {U Y : Scheme.{u}} [IsIntegral U] [IsLocallyNoetherian U] [IsNormal U]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of k)} (q : U ⟶ Y) [Etale q] [IsDominant q]
    (hU : IsNormalVariety k (q ≫ sY)) (h₀ : MMP.Mori.IsPair sY (0 : QDivisor Y))
    (D : DivisorOver k (q ≫ sY)) (hD : IsProper D.f) :
    ∃ D₀ : DivisorOver k sY, (D.IsExceptional → D₀.IsExceptional) ∧ ∀ (n : ℕ) (a : ℝ),
      MMP.Intersection.IsLogDiscrepancy (q ≫ sY) n 0 D a ↔
        MMP.Intersection.IsLogDiscrepancy sY n 0 D₀ a := by
  obtain ⟨-, ⟨D₀, hD₀p, hD₀v⟩, hiff⟩ :=
    MMP.Intersection.isLogDiscrepancy_iff_of_etale sY q h₀ hU D.valuation ⟨D, hD, rfl⟩
  refine ⟨D₀, fun hex => ?_, hiff D D₀ hD hD₀p rfl hD₀v.symm⟩
  rw [isExceptional_iff_two_le_coheight h₀.1,
    ← map_center_eq_of_valuation_comp_eq (D := D₀) (D' := D) q h₀.1.1
      (fun g => by rw [← hD₀v, Valuation.comap_apply]), coheight_apply_eq]
  exact (isExceptional_iff_two_le_coheight hU D).1 hex

/-! ### The theorem -/

/-- **Étale neighbourhoods of a terminal variety are terminal.** Let `q : U ⟶ Y` be an étale
morphism of normal integral varieties over `k`, with `K_Y` `ℚ`-Cartier and `(Y, 0)` terminal.
Then `(U, 0)` is terminal, and for every canonical divisor `K_Y` of `Y` its pull-back
`q^* K_Y` is defined and is a `ℚ`-Cartier canonical divisor `K_U` of `U`. -/
@[mmp "lem_mmp_indexb_etale_terminal"]
public theorem IsTerminalVariety.comp_etale {k : Type u} [Field k] {U Y : Scheme.{u}}
    [IsIntegral U] [IsLocallyNoetherian U] [IsNormal U]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of k)} (q : U ⟶ Y) [Etale q]
    (hU : IsNormalVariety k (q ≫ sY)) (hY : IsTerminalVariety sY) :
    IsTerminalVariety (q ≫ sY) ∧
      ∀ (n : ℕ) (KY : Divisor Y), KY.IsCanonicalDivisor sY n →
        ∃ (hq : ∀ Z : irreducibleComponents U,
            q (componentGenericPoint U Z) ∉ (Divisor.toQDivisor KY).supp)
          (KU : Divisor U), KU.IsCanonicalDivisor (q ≫ sY) n ∧
          (Divisor.toQDivisor KY).IsPullback q hq (Divisor.toQDivisor KU) ∧
          (Divisor.toQDivisor KU).IsQCartier := by
  obtain ⟨⟨hpair, hklt⟩, hterm⟩ := hY
  haveI := hpair.charZero
  -- `q` is open, so its nonempty image is dense in the irreducible `Y`.
  haveI : IsDominant q := ⟨q.isOpenMap.isOpen_range.dense (Set.range_nonempty _)⟩
  have h₀ : MMP.Mori.IsPair sY (0 : QDivisor Y) := hpair.isPair
  obtain ⟨n₀, K₀, hK₀, -⟩ := h₀.2
  obtain ⟨-, KU, hKU, -, hKUq⟩ := exists_isCanonicalDivisor_isPullback_of_etale q hU h₀ hK₀
  have hpairU : IsPair (q ≫ sY) (0 : QDivisor U) :=
    { isAlgClosed := hpair.isAlgClosed
      charZero := hpair.charZero
      isPair := ⟨hU, n₀, KU, hKU, by rwa [add_zero]⟩
      nonneg := fun _ => le_rfl }
  refine ⟨⟨⟨hpairU, fun n D a ha => ?_⟩, fun n D a hD ha => ?_⟩,
    fun n KY => exists_isCanonicalDivisor_isPullback_of_etale q hU h₀⟩ <;>
  · rw [map_zero] at ha
    obtain ⟨D₀, hex, hiff⟩ := exists_divisorOver_isLogDiscrepancy_iff_of_etale q hU h₀ D ha.2.1
    have h := (hiff n a).1 ha
    rw [← map_zero QDivisor.toRDivisor] at h
    first
    | exact hklt n D₀ a h
    | exact hterm n D₀ a (hex hD) h

end EtaleTerminal

/-! ## The product local setting -/

section ProductLocalSetting

open AlgebraicGeometry Limits MMP.Mori TopologicalSpace

/-! ### Base change along the projection -/

section BaseChange

/-- `q × id_L : Y₁ × L ⟶ Y × L` is the base change of `q : Y₁ ⟶ Y` along the projection
`Y × L ⟶ Y`. -/
theorem isPullback_pullbackMap_comp_id {S Y L Y₁ : Scheme.{u}} (sY : Y ⟶ S) (sL : L ⟶ S)
    (q : Y₁ ⟶ Y) :
    IsPullback (pullback.map (q ≫ sY) sL sY sL q (𝟙 L) (𝟙 _) (by simp) (by simp))
      (pullback.fst (q ≫ sY) sL) (pullback.fst sY sL) q := by
  refine IsPullback.of_right ?_ (by simp) (IsPullback.of_hasPullback sY sL).flip
  simpa using (IsPullback.of_hasPullback (q ≫ sY) sL).flip

/-- If `m` is the base change of `g` along `p` and `c ≫ j = φ ≫ p`, the comparison morphism from
the base change of `m` along `φ` to the base change of `g` along `j`: its first component is
`pullback.fst m φ ≫ p'` and its second `pullback.snd m φ ≫ c`. -/
def pullbackLiftOfIsPullback {P' P Y₁ Y W K : Scheme.{u}} {m : P' ⟶ P}
    {p' : P' ⟶ Y₁} {p : P ⟶ Y} {g : Y₁ ⟶ Y} (H : IsPullback m p' p g) (φ : W ⟶ P)
    (j : K ⟶ Y) (c : W ⟶ K) (hc : c ≫ j = φ ≫ p) : pullback m φ ⟶ pullback g j :=
  pullback.lift (pullback.fst m φ ≫ p') (pullback.snd m φ ≫ c) (by
    rw [Category.assoc, ← H.w, pullback.condition_assoc, Category.assoc, hc])

/-- The first component of `pullbackLiftOfIsPullback H φ j c hc` is `pullback.fst m φ ≫ p'`. -/
@[reassoc (attr := simp)]
theorem pullbackLiftOfIsPullback_fst {P' P Y₁ Y W K : Scheme.{u}} {m : P' ⟶ P}
    {p' : P' ⟶ Y₁} {p : P ⟶ Y} {g : Y₁ ⟶ Y} (H : IsPullback m p' p g) (φ : W ⟶ P)
    (j : K ⟶ Y) (c : W ⟶ K) (hc : c ≫ j = φ ≫ p) :
    pullbackLiftOfIsPullback H φ j c hc ≫ pullback.fst g j = pullback.fst m φ ≫ p' :=
  pullback.lift_fst _ _ _

/-- The second component of `pullbackLiftOfIsPullback H φ j c hc` is `pullback.snd m φ ≫ c`. -/
@[reassoc (attr := simp)]
theorem pullbackLiftOfIsPullback_snd {P' P Y₁ Y W K : Scheme.{u}} {m : P' ⟶ P}
    {p' : P' ⟶ Y₁} {p : P ⟶ Y} {g : Y₁ ⟶ Y} (H : IsPullback m p' p g) (φ : W ⟶ P)
    (j : K ⟶ Y) (c : W ⟶ K) (hc : c ≫ j = φ ≫ p) :
    pullbackLiftOfIsPullback H φ j c hc ≫ pullback.snd g j = pullback.snd m φ ≫ c :=
  pullback.lift_snd _ _ _

/-- If `m` is the base change of `g` along `p`, then the base change of `m` along `φ` is the base
change of `g` along `φ ≫ p`; when `φ ≫ p = c ≫ j`, it is the base change along `c` of the base
change of `g` along `j`, via `pullbackLiftOfIsPullback`. -/
theorem isPullback_pullbackLiftOfIsPullback {P' P Y₁ Y W K : Scheme.{u}} {m : P' ⟶ P}
    {p' : P' ⟶ Y₁} {p : P ⟶ Y} {g : Y₁ ⟶ Y} (H : IsPullback m p' p g) (φ : W ⟶ P)
    (j : K ⟶ Y) (c : W ⟶ K) (hc : c ≫ j = φ ≫ p) :
    IsPullback (pullbackLiftOfIsPullback H φ j c hc) (pullback.snd m φ) (pullback.snd g j) c := by
  have H₁ : IsPullback (pullback.fst m φ ≫ p') (pullback.snd m φ) g (φ ≫ p) :=
    (IsPullback.of_hasPullback m φ).paste_horiz H.flip
  refine IsPullback.of_right ?_ (pullbackLiftOfIsPullback_snd H φ j c hc)
    (IsPullback.of_hasPullback g j)
  rw [pullbackLiftOfIsPullback_fst, hc]
  exact H₁

/-- For a morphism `f` with `f x = y`, the morphism `Spec κ(x) ⟶ Spec κ(y)` induced by `f`. -/
def specResidueFieldMapOfEq {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) {y : Y} (hy : f x = y) :
    Spec (X.residueField x) ⟶ Spec (Y.residueField y) :=
  Spec.map (f.residueFieldMap x) ≫ Spec.map (Y.residueFieldCongr hy.symm).hom

/-- The morphism `specResidueFieldMapOfEq f x hy` lies over `f`: composed with
`Spec κ(y) ⟶ Y` it equals `Spec κ(x) ⟶ X` composed with `f`. -/
@[reassoc (attr := simp)]
theorem specResidueFieldMapOfEq_fromSpecResidueField {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    {y : Y} (hy : f x = y) :
    specResidueFieldMapOfEq f x hy ≫ Y.fromSpecResidueField y = X.fromSpecResidueField x ≫ f := by
  simp [specResidueFieldMapOfEq]

/-- Biregularity over `V` is inherited by a base change, over the preimage of `V`. -/
private theorem isBiregular_preimage_of_isPullback {P' P Y₁ Y : Scheme.{u}} {m : P' ⟶ P}
    {p' : P' ⟶ Y₁} {p : P ⟶ Y} {g : Y₁ ⟶ Y} (H : IsPullback m p' p g) {V : Y.Opens}
    (hV : IsBiregular g V) : IsBiregular m (p ⁻¹ᵁ V) := by
  have hUY : m ⁻¹ᵁ (p ⁻¹ᵁ V) = m ⁻¹ᵁ (p ⁻¹ᵁ V) ⊓ p' ⁻¹ᵁ (g ⁻¹ᵁ V) := by
    refine (inf_eq_left.2 ?_).symm
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, H.w]
  have H' := Scheme.Hom.isPullback_resLE H (US := V) (UT := g ⁻¹ᵁ V) (UX := p ⁻¹ᵁ V)
    le_rfl le_rfl hUY
  have hg : IsIso (g.resLE V (g ⁻¹ᵁ V) le_rfl) := by
    rwa [Scheme.Hom.resLE_eq_morphismRestrict]
  have := MorphismProperty.of_isPullback (P := MorphismProperty.isomorphisms Scheme) H'.flip hg
  unfold IsBiregular
  rwa [← Scheme.Hom.resLE_eq_morphismRestrict]

end BaseChange

/-! ### Closed points over `ℂ` -/

/-- At a closed point `x` of a scheme locally of finite type over `ℂ`, `Spec κ(x) ⟶ Spec ℂ` is an
isomorphism. -/
private theorem isIso_fromSpecResidueField_comp {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    [LocallyOfFiniteType sX] {x : X} (hx : IsClosed ({x} : Set X)) :
    IsIso (X.fromSpecResidueField x ≫ sX) := by
  rw [← SpecMap_residueFieldIsoBase_inv sX x hx]
  infer_instance

/-! ### The fibres of the product family -/

private theorem projectiveLine_iso_or :
    (∃ e : projectiveLine ℂ ≅ projectiveLine ℂ,
      e.hom ≫ (projectiveLine ℂ ↘ Spec (.of ℂ)) = projectiveLine ℂ ↘ Spec (.of ℂ)) ∨
      ∃ e : projectiveLine ℂ ≅ 𝔸(PUnit.{1}; Spec (.of ℂ)),
        e.hom ≫ (𝔸(PUnit.{1}; Spec (.of ℂ)) ↘ Spec (.of ℂ)) = projectiveLine ℂ ↘ Spec (.of ℂ) :=
  Or.inl ⟨Iso.refl _, Category.id_comp _⟩

/-- A point of `T_y` lies over `y`. -/
theorem fst_eq_of_mem_pointSettingCurve {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)} {y : Y}
    {t : ↥(pullback sY (projectiveLine ℂ ↘ Spec (.of ℂ)))} (ht : t ∈ pointSettingCurve sY y) :
    pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) t = y :=
  ht

/-- At the closed point `y` of a threefold point setting, `Spec κ(y) ⟶ Spec ℂ` is an
isomorphism. -/
theorem IsThreefoldPointSetting.isIso_fromSpecResidueField_comp {Y Yt : Scheme.{0}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)} {π : Yt ⟶ Y}
    {y : Y} (h : IsThreefoldPointSetting sY π y) : IsIso (Y.fromSpecResidueField y ≫ sY) := by
  haveI : LocallyOfFiniteType sY := h.isQFactorial.1.1.toLocallyOfFiniteType
  exact MMP.Fourfold.isIso_fromSpecResidueField_comp sY h.isClosed_singleton

/-- **The base change of the product family to `{y} × V`.** For `g : V ⟶ ℙ¹`, the base change
of `π × id : Ỹ × ℙ¹ ⟶ Y × ℙ¹` along `{y} × V = Spec κ(y) ×_ℂ V ⟶ Y × ℙ¹` is `F_y ×_ℂ V`, the
identification being the canonical one of iterated fibre products (its projections are
`productPointSettingBaseChangeIso_hom_snd` and `productPointSettingBaseChangeIso_hom_fst_fst`). -/
def productPointSettingBaseChangeIso {Y Yt : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ)) (π : Yt ⟶ Y)
    (y : Y) {V : Scheme.{0}} (g : V ⟶ projectiveLine ℂ) :
    pullback
        (pullback.map (π ≫ sY) (projectiveLine ℂ ↘ Spec (.of ℂ)) sY
          (projectiveLine ℂ ↘ Spec (.of ℂ)) π (𝟙 _) (𝟙 _) (by simp) (by simp))
        (pullback.map (Y.fromSpecResidueField y ≫ sY) (g ≫ (projectiveLine ℂ ↘ Spec (.of ℂ)))
          sY (projectiveLine ℂ ↘ Spec (.of ℂ)) (Y.fromSpecResidueField y) g (𝟙 _)
          (by simp) (by simp)) ≅
      pullback (pullback.snd π (Y.fromSpecResidueField y) ≫ Y.fromSpecResidueField y ≫ sY)
        (g ≫ (projectiveLine ℂ ↘ Spec (.of ℂ))) :=
  ((isPullback_pullbackLiftOfIsPullback (isPullback_pullbackMap_comp_id sY _ π) _
    (Y.fromSpecResidueField y) (pullback.fst _ _) (by simp)).paste_vert
      (IsPullback.of_hasPullback _ _)).isoPullback

/-- `productPointSettingBaseChangeIso` is compatible with the projections to `V`. -/
@[reassoc (attr := simp)]
theorem productPointSettingBaseChangeIso_hom_snd {Y Yt : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ))
    (π : Yt ⟶ Y) (y : Y) {V : Scheme.{0}} (g : V ⟶ projectiveLine ℂ) :
    (productPointSettingBaseChangeIso sY π y g).hom ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ pullback.snd (Y.fromSpecResidueField y ≫ sY) _ := by
  rw [productPointSettingBaseChangeIso, IsPullback.isoPullback_hom_snd]

/-- `productPointSettingBaseChangeIso` is compatible with the projections to `Ỹ`. -/
@[reassoc (attr := simp)]
theorem productPointSettingBaseChangeIso_hom_fst_fst {Y Yt : Scheme.{0}}
    (sY : Y ⟶ Spec (.of ℂ)) (π : Yt ⟶ Y) (y : Y) {V : Scheme.{0}} (g : V ⟶ projectiveLine ℂ) :
    (productPointSettingBaseChangeIso sY π y g).hom ≫ pullback.fst _ _ ≫
        pullback.fst π (Y.fromSpecResidueField y) =
      pullback.fst _ _ ≫ pullback.fst (π ≫ sY) (projectiveLine ℂ ↘ Spec (.of ℂ)) := by
  rw [← Category.assoc, productPointSettingBaseChangeIso, IsPullback.isoPullback_hom_fst,
    pullbackLiftOfIsPullback_fst]

/-- Over a closed point `t ∈ T_y`, the comparison morphism from the scheme fibre of `π × id` to
`F_y` is an isomorphism. -/
theorem IsThreefoldPointSetting.isIso_pullbackLiftOfIsPullback_closedFibre {Y Yt : Scheme.{0}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)} {π : Yt ⟶ Y}
    {y : Y} (h : IsThreefoldPointSetting sY π y)
    (t : ↥(pullback sY (projectiveLine ℂ ↘ Spec (.of ℂ)))) (ht : t ∈ pointSettingCurve sY y)
    (htc : IsClosed ({t} : Set _)) :
    IsIso (pullbackLiftOfIsPullback
      (isPullback_pullbackMap_comp_id sY (projectiveLine ℂ ↘ Spec (.of ℂ)) π)
      ((pullback sY (projectiveLine ℂ ↘ Spec (.of ℂ))).fromSpecResidueField t)
      (Y.fromSpecResidueField y)
      (specResidueFieldMapOfEq _ t (fst_eq_of_mem_pointSettingCurve ht))
      (specResidueFieldMapOfEq_fromSpecResidueField _ t
        (fst_eq_of_mem_pointSettingCurve ht))) := by
  have hYn : IsNormalVariety ℂ sY := h.isQFactorial.1
  have hL := projectiveLine_iso_or
  haveI : LocallyOfFiniteType (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY) :=
    (product_line_basic sY _ hYn hL).1.2.2.1.1.toLocallyOfFiniteType
  haveI := h.isIso_fromSpecResidueField_comp
  haveI : IsIso (specResidueFieldMapOfEq _ t (fst_eq_of_mem_pointSettingCurve ht) ≫
      Y.fromSpecResidueField y ≫ sY) := by
    rw [specResidueFieldMapOfEq_fromSpecResidueField_assoc]
    exact MMP.Fourfold.isIso_fromSpecResidueField_comp _ htc
  haveI : IsIso (specResidueFieldMapOfEq _ t (fst_eq_of_mem_pointSettingCurve ht)) :=
    IsIso.of_isIso_comp_right _ (Y.fromSpecResidueField y ≫ sY)
  exact (isPullback_pullbackLiftOfIsPullback _ _ _ _ _).isIso_fst_of_isIso

/-- **The closed fibres of the product family.** Over a closed point `t ∈ T_y`, the scheme fibre
of `π × id : Ỹ × ℙ¹ ⟶ Y × ℙ¹` is `F_t ≅ F_y`, compatibly with the maps to `Ỹ`
(`productPointSettingClosedFibreIso_hom_fst`). -/
def productPointSettingClosedFibreIso {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)} {π : Yt ⟶ Y} {y : Y}
    (h : IsThreefoldPointSetting sY π y)
    (t : ↥(pullback sY (projectiveLine ℂ ↘ Spec (.of ℂ)))) (ht : t ∈ pointSettingCurve sY y)
    (htc : IsClosed ({t} : Set _)) :
    pullback
        (pullback.map (π ≫ sY) (projectiveLine ℂ ↘ Spec (.of ℂ)) sY
          (projectiveLine ℂ ↘ Spec (.of ℂ)) π (𝟙 _) (𝟙 _) (by simp) (by simp))
        ((pullback sY (projectiveLine ℂ ↘ Spec (.of ℂ))).fromSpecResidueField t) ≅
      pointSettingFibre π y :=
  haveI := h.isIso_pullbackLiftOfIsPullback_closedFibre t ht htc
  asIso (pullbackLiftOfIsPullback
    (isPullback_pullbackMap_comp_id sY (projectiveLine ℂ ↘ Spec (.of ℂ)) π)
    ((pullback sY (projectiveLine ℂ ↘ Spec (.of ℂ))).fromSpecResidueField t)
    (Y.fromSpecResidueField y) (specResidueFieldMapOfEq _ t (fst_eq_of_mem_pointSettingCurve ht))
    (specResidueFieldMapOfEq_fromSpecResidueField _ t (fst_eq_of_mem_pointSettingCurve ht)))

/-- `productPointSettingClosedFibreIso` is compatible with the maps to `Ỹ`. -/
@[reassoc (attr := simp)]
theorem productPointSettingClosedFibreIso_hom_fst {Y Yt : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)} {π : Yt ⟶ Y} {y : Y}
    (h : IsThreefoldPointSetting sY π y)
    (t : ↥(pullback sY (projectiveLine ℂ ↘ Spec (.of ℂ)))) (ht : t ∈ pointSettingCurve sY y)
    (htc : IsClosed ({t} : Set _)) :
    (productPointSettingClosedFibreIso h t ht htc).hom ≫ pullback.fst π (Y.fromSpecResidueField y) =
      pullback.fst _ _ ≫ pullback.fst (π ≫ sY) (projectiveLine ℂ ↘ Spec (.of ℂ)) := by
  simp [productPointSettingClosedFibreIso]

/-- **The generic fibre of the product family.** Over a generic point `η` of `T_y`, the scheme
fibre of `π × id : Ỹ × ℙ¹ ⟶ Y × ℙ¹` is `F_y ×_ℂ Spec κ(η)`, compatibly with the projections to
`Ỹ` and to `Spec κ(η)` (`productPointSettingGenericFibreIso_hom_fst_fst` and
`productPointSettingGenericFibreIso_hom_snd`). -/
def productPointSettingGenericFibreIso {Y Yt : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)} {π : Yt ⟶ Y} {y : Y}
    (h : IsThreefoldPointSetting sY π y) (η : ↥(pullback sY (projectiveLine ℂ ↘ Spec (.of ℂ))))
    (hη : IsGenericPoint η (pointSettingCurve sY y)) :
    pullback
        (pullback.map (π ≫ sY) (projectiveLine ℂ ↘ Spec (.of ℂ)) sY
          (projectiveLine ℂ ↘ Spec (.of ℂ)) π (𝟙 _) (𝟙 _) (by simp) (by simp))
        ((pullback sY (projectiveLine ℂ ↘ Spec (.of ℂ))).fromSpecResidueField η) ≅
      pullback (pullback.snd π (Y.fromSpecResidueField y) ≫ Y.fromSpecResidueField y ≫ sY)
        ((pullback sY (projectiveLine ℂ ↘ Spec (.of ℂ))).fromSpecResidueField η ≫
          pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY) :=
  haveI := h.isIso_fromSpecResidueField_comp
  ((isPullback_pullbackLiftOfIsPullback (isPullback_pullbackMap_comp_id sY _ π) _
    (Y.fromSpecResidueField y)
    (specResidueFieldMapOfEq _ η (fst_eq_of_mem_pointSettingCurve hη.mem))
    (specResidueFieldMapOfEq_fromSpecResidueField _ η
      (fst_eq_of_mem_pointSettingCurve hη.mem))).paste_vert
    (IsPullback.of_vert_isIso (snd := 𝟙 _) (f := Y.fromSpecResidueField y ≫ sY)
      (g := (pullback sY (projectiveLine ℂ ↘ Spec (.of ℂ))).fromSpecResidueField η ≫
        pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY) ⟨by simp⟩)).isoPullback

/-- `productPointSettingGenericFibreIso` is compatible with the projections to `Spec κ(η)`. -/
@[reassoc (attr := simp)]
theorem productPointSettingGenericFibreIso_hom_snd {Y Yt : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)} {π : Yt ⟶ Y} {y : Y}
    (h : IsThreefoldPointSetting sY π y) (η : ↥(pullback sY (projectiveLine ℂ ↘ Spec (.of ℂ))))
    (hη : IsGenericPoint η (pointSettingCurve sY y)) :
    (productPointSettingGenericFibreIso h η hη).hom ≫ pullback.snd _ _ = pullback.snd _ _ := by
  rw [productPointSettingGenericFibreIso, IsPullback.isoPullback_hom_snd, Category.comp_id]

/-- `productPointSettingGenericFibreIso` is compatible with the projections to `Ỹ`. -/
@[reassoc (attr := simp)]
theorem productPointSettingGenericFibreIso_hom_fst_fst {Y Yt : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)} {π : Yt ⟶ Y} {y : Y}
    (h : IsThreefoldPointSetting sY π y) (η : ↥(pullback sY (projectiveLine ℂ ↘ Spec (.of ℂ))))
    (hη : IsGenericPoint η (pointSettingCurve sY y)) :
    (productPointSettingGenericFibreIso h η hη).hom ≫ pullback.fst _ _ ≫
        pullback.fst π (Y.fromSpecResidueField y) =
      pullback.fst _ _ ≫ pullback.fst (π ≫ sY) (projectiveLine ℂ ↘ Spec (.of ℂ)) := by
  rw [← Category.assoc, productPointSettingGenericFibreIso, IsPullback.isoPullback_hom_fst,
    pullbackLiftOfIsPullback_fst]

/-- **The fibre `F_y` has dimension at most two.** For a threefold point setting `(Y, π, y)`, the
scheme fibre `F_y` of the resolution `π` over the singular point `y` has dimension `≤ 2`. -/
theorem IsThreefoldPointSetting.topologicalKrullDim_pointSettingFibre_le_two {Y Yt : Scheme.{0}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)} {π : Yt ⟶ Y}
    {y : Y} (h : IsThreefoldPointSetting sY π y) :
    topologicalKrullDim (pointSettingFibre π y) ≤ 2 := by
  obtain ⟨hvY, hvYt, -, -, hbirπ⟩ := h.isResolution
  haveI : IsIntegral Yt := hvYt.toIsIntegral
  haveI : LocallyOfFiniteType (π ≫ sY) := hvYt.toLocallyOfFiniteType
  haveI : QuasiCompact (π ≫ sY) := hvYt.toQuasiCompact
  haveI : IsLocallyNoetherian Yt := LocallyOfFiniteType.isLocallyNoetherian (π ≫ sY)
  haveI : CompactSpace Yt := QuasiCompact.compactSpace_of_compactSpace (π ≫ sY)
  haveI : IsNoetherian Yt := {}
  have hdim : topologicalKrullDim Y = topologicalKrullDim Yt :=
    MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sY (π ≫ sY) hbirπ
  have hS : IsClosed (π ⁻¹' {y}) := h.isClosed_singleton.preimage π.continuous
  have hne : π ⁻¹' {y} ≠ Set.univ := by
    intro hall
    obtain ⟨W, hWne, hW⟩ := hbirπ.exists_isOpenImmersion
    obtain ⟨w, hw⟩ := hWne
    have hrange : Set.range (W.ι ≫ π) = {y} := by
      refine Set.eq_singleton_iff_nonempty_unique_mem.2 ⟨⟨_, ⟨w, hw⟩, rfl⟩, ?_⟩
      rintro z ⟨w', rfl⟩
      have : W.ι w' ∈ π ⁻¹' {y} := hall ▸ Set.mem_univ _
      simpa using this
    have hopen : IsOpen ({y} : Set Y) := hrange ▸ (W.ι ≫ π).isOpenEmbedding.isOpen_range
    have hdense := hopen.dense (Set.singleton_nonempty y)
    have huniv : ({y} : Set Y) = Set.univ := by
      rw [← h.isClosed_singleton.closure_eq, hdense.closure_eq]
    haveI : Subsingleton Y := ⟨fun a b => by
      have ha : a ∈ ({y} : Set Y) := huniv ▸ Set.mem_univ a
      have hb : b ∈ ({y} : Set Y) := huniv ▸ Set.mem_univ b
      rw [Set.mem_singleton_iff.1 ha, Set.mem_singleton_iff.1 hb]⟩
    have h0 := topologicalKrullDim_zero_of_discreteTopology Y
    rw [h.topologicalKrullDim_eq] at h0
    exact absurd h0 (by decide)
  have hnd : IsNowhereDense (π ⁻¹' {y}) := by
    rw [hS.isNowhereDense_iff, interior_eq_empty_iff_dense_compl]
    exact hS.isOpen_compl.dense (Set.nonempty_compl.2 hne)
  have h2 := hnd.topologicalKrullDim_le_of_le_natCast_succ hS 2
    (by rw [← hdim, h.topologicalKrullDim_eq]; rfl)
  change topologicalKrullDim (π.fiber y) ≤ 2
  rw [IsHomeomorph.topologicalKrullDim_eq _ (π.fiberHomeo y).isHomeomorph]
  exact_mod_cast h2

/-- The product `Y × ℙ¹` of a threefold point setting, with the curve `T_y` and `π × id`, is a
local setting. -/
theorem IsThreefoldPointSetting.isLocalSetting_pointSettingCurve
    {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {π : Yt ⟶ Y} {y : Y} (h : IsThreefoldPointSetting sY π y)
    [IsIntegral (pullback sY (projectiveLine ℂ ↘ Spec (.of ℂ)))]
    [IsLocallyNoetherian (pullback sY (projectiveLine ℂ ↘ Spec (.of ℂ)))]
    [IsNormal (pullback sY (projectiveLine ℂ ↘ Spec (.of ℂ)))]
    (hirr : IsIrreducible (pointSettingCurve sY y)) (hclosed : IsClosed (pointSettingCurve sY y))
    (hdimT : topologicalKrullDim (pointSettingCurve sY y) = 1) :
    IsLocalSetting (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY) 0
      ⟨pointSettingCurve sY y, hirr, hclosed⟩
      (pullback.map (π ≫ sY) (projectiveLine ℂ ↘ Spec (.of ℂ)) sY
        (projectiveLine ℂ ↘ Spec (.of ℂ)) π (𝟙 _) (𝟙 _) (by simp) (by simp)) := by
  have hYn : IsNormalVariety ℂ sY := h.isQFactorial.1
  have hL := projectiveLine_iso_or
  have hB := product_line_basic sY _ hYn hL
  haveI : LocallyOfFiniteType sY := hYn.1.toLocallyOfFiniteType
  have H := isPullback_pullbackMap_comp_id sY (projectiveLine ℂ ↘ Spec (.of ℂ)) π
  haveI : LocallyOfFiniteType (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY) :=
    hB.1.2.2.1.1.toLocallyOfFiniteType
  obtain ⟨-, hvYt, hsmYt, hprojπ, hbirπ⟩ := h.isResolution
  have hsmπ : Smooth (π ≫ sY) := hsmYt.smooth
  have hNYt : IsNormal Yt :=
    (MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hsmYt).2
  have hπn : IsNormalVariety ℂ (π ≫ sY) := ⟨hvYt, hNYt⟩
  have hB' := product_line_basic (π ≫ sY) _ hπn hL
  obtain ⟨hpm, hbm, -, -⟩ := hB.2.2.2 π hπn hprojπ hbirπ
  have hw : pullback.map (π ≫ sY) (projectiveLine ℂ ↘ Spec (.of ℂ)) sY
        (projectiveLine ℂ ↘ Spec (.of ℂ)) π (𝟙 _) (𝟙 _) (by simp) (by simp) ≫
        pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY =
      pullback.fst (π ≫ sY) (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ π ≫ sY := by
    rw [← Category.assoc, H.w, Category.assoc]
  haveI : Smooth (pullback.fst (π ≫ sY) (projectiveLine ℂ ↘ Spec (.of ℂ))) := hB'.1.1
  have hsmP : Smooth (pullback.fst (π ≫ sY) (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ π ≫ sY) :=
    inferInstance
  have hsmooth : smoothLocus (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY) =
      pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ⁻¹ᵁ smoothLocus sY := by
    ext x
    have := congrArg (x ∈ ·) hB.2.1
    exact not_iff_not.1 (by simpa [MMP.Mori.singularLocus, mem_singularLocus_iff] using this)
  refine
    { isQFactorial := (isQFactorial_pullback_line sY _ hYn hL).2 h.isQFactorial
      isProjectiveVariety := hB.1.2.2.2.2.1 ⟨Iso.refl _, Category.id_comp _⟩
        h.isProjectiveVariety
      topologicalKrullDim_eq := ?_
      isKltTerminalPair := ?_
      topologicalKrullDim_curve := hdimT
      subset_singularLocus := ?_
      isResolution := ⟨hB.1.2.2.1.1, ?_, ?_, hpm, hbm⟩
      isBiregular := ?_ }
  · rw [hB.1.2.2.2.1, h.topologicalKrullDim_eq]
    rfl
  · exact (IsTerminalVariety.pullback_projectiveLine h.isTerminalVariety).2.2
  · intro x hx
    have hx' : x ∈ (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ))) ⁻¹'
        (singularLocus sY : Set Y) := by
      change pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) x ∈ (singularLocus sY : Set Y)
      rw [show pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) x = y from hx]
      exact h.mem_singularLocus
    rwa [← hB.2.1] at hx'
  · rw [hw]
    exact hB'.1.2.2.1.1
  · rw [hw]
    exact isSmoothScheme_of_smooth hsmP
  · rw [hsmooth]
    exact isBiregular_preimage_of_isPullback H h.isBiregular

/-- **The product local setting.** Let `(Y, π, y)` be a threefold point setting. Then
1. `Y × ℙ¹` is integral, locally noetherian and normal, and `(Y × ℙ¹, 0, T_y, π × id)` is a local
   setting, with `T_y = {y} × ℙ¹` (`MMP.Fourfold.pointSettingCurve`);
2. for every `g : V ⟶ ℙ¹`, the base change of `π × id` along `{y} × V = Spec κ(y) ×_ℂ V ⟶ Y × ℙ¹`
   is `F_y ×_ℂ V`, compatibly with the projections to `Ỹ` and to `V`;
3. the scheme fibre of `π × id` over a closed point `t ∈ T_y` is `F_y`, compatibly with the maps
   to `Ỹ`;
4. the scheme fibre of `π × id` over a generic point `η` of `T_y` is `F_y ×_ℂ Spec κ(η)`,
   compatibly with the projections to `Ỹ` and to `Spec κ(η)`;
5. `dim F_y ≤ 2`. -/
@[mmp "lem_mmp_indexb_product_local_setting"]
public theorem IsThreefoldPointSetting.isLocalSetting_pullback_projectiveLine
    {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {π : Yt ⟶ Y} {y : Y} (h : IsThreefoldPointSetting sY π y) :
    -- (1) the local setting
    (∃ (_ : IsIntegral (pullback sY (projectiveLine ℂ ↘ Spec (.of ℂ))))
      (_ : IsLocallyNoetherian (pullback sY (projectiveLine ℂ ↘ Spec (.of ℂ))))
      (_ : IsNormal (pullback sY (projectiveLine ℂ ↘ Spec (.of ℂ))))
      (T : TopologicalSpace.IrreducibleCloseds
        ↥(pullback sY (projectiveLine ℂ ↘ Spec (.of ℂ)))),
      (T : Set ↥(pullback sY (projectiveLine ℂ ↘ Spec (.of ℂ)))) = pointSettingCurve sY y ∧
      IsLocalSetting (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY) 0 T
        (pullback.map (π ≫ sY) (projectiveLine ℂ ↘ Spec (.of ℂ)) sY
          (projectiveLine ℂ ↘ Spec (.of ℂ)) π (𝟙 _) (𝟙 _) (by simp) (by simp))) ∧
    -- (2) base change along `{y} × V`
    (∀ {V : Scheme.{0}} (g : V ⟶ projectiveLine ℂ),
      (productPointSettingBaseChangeIso sY π y g).hom ≫ pullback.snd _ _ =
          pullback.snd _ _ ≫ pullback.snd (Y.fromSpecResidueField y ≫ sY) _ ∧
        (productPointSettingBaseChangeIso sY π y g).hom ≫ pullback.fst _ _ ≫
            pullback.fst π (Y.fromSpecResidueField y) =
          pullback.fst _ _ ≫ pullback.fst (π ≫ sY) (projectiveLine ℂ ↘ Spec (.of ℂ))) ∧
    -- (3) the closed fibres
    (∀ t (ht : t ∈ pointSettingCurve sY y) (htc : IsClosed ({t} : Set _)),
      (productPointSettingClosedFibreIso h t ht htc).hom ≫
          pullback.fst π (Y.fromSpecResidueField y) =
        pullback.fst _ _ ≫ pullback.fst (π ≫ sY) (projectiveLine ℂ ↘ Spec (.of ℂ))) ∧
    -- (4) the generic fibre
    (∀ η (hη : IsGenericPoint η (pointSettingCurve sY y)),
      (productPointSettingGenericFibreIso h η hη).hom ≫ pullback.snd _ _ = pullback.snd _ _ ∧
        (productPointSettingGenericFibreIso h η hη).hom ≫ pullback.fst _ _ ≫
            pullback.fst π (Y.fromSpecResidueField y) =
          pullback.fst _ _ ≫ pullback.fst (π ≫ sY) (projectiveLine ℂ ↘ Spec (.of ℂ))) ∧
    -- (5) the dimension of the fibre
    topologicalKrullDim (pointSettingFibre π y) ≤ 2 := by
  have hYn : IsNormalVariety ℂ sY := h.isQFactorial.1
  have hL := projectiveLine_iso_or
  have hB := product_line_basic sY _ hYn hL
  haveI : LocallyOfFiniteType sY := hYn.1.toLocallyOfFiniteType
  haveI : IsIso (Y.fromSpecResidueField y ≫ sY) := h.isIso_fromSpecResidueField_comp
  haveI : LocallyOfFiniteType (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY) :=
    hB.1.2.2.1.1.toLocallyOfFiniteType
  refine ⟨?_, fun g => ⟨productPointSettingBaseChangeIso_hom_snd sY π y g,
      productPointSettingBaseChangeIso_hom_fst_fst sY π y g⟩,
    fun t ht htc => productPointSettingClosedFibreIso_hom_fst h t ht htc,
    fun η hη => ⟨productPointSettingGenericFibreIso_hom_snd h η hη,
      productPointSettingGenericFibreIso_hom_fst_fst h η hη⟩,
    h.topologicalKrullDim_pointSettingFibre_le_two⟩
  · -- (1) the local setting
    have hIP : IsIntegral (pullback sY (projectiveLine ℂ ↘ Spec (.of ℂ))) :=
      hB.1.2.2.1.1.toIsIntegral
    have hLNP : IsLocallyNoetherian (pullback sY (projectiveLine ℂ ↘ Spec (.of ℂ))) :=
      LocallyOfFiniteType.isLocallyNoetherian
        (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY)
    have hNP : IsNormal (pullback sY (projectiveLine ℂ ↘ Spec (.of ℂ))) := hB.1.2.2.1.2
    -- the curve `T_y` is homeomorphic to `ℙ¹`
    obtain ⟨-, -, hv₁, hd₁⟩ := smooth_geometricallyIrreducible_isVariety_dim_line _ hL
    haveI : IsIntegral (projectiveLine ℂ) := hv₁.toIsIntegral
    have hsq : IsPullback
        (pullback.fst (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)))
          (Y.fromSpecResidueField y) ≫ pullback.snd sY (projectiveLine ℂ ↘ Spec (.of ℂ)))
        (pullback.snd (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)))
          (Y.fromSpecResidueField y))
        (projectiveLine ℂ ↘ Spec (.of ℂ)) (Y.fromSpecResidueField y ≫ sY) :=
      (IsPullback.of_hasPullback _ _).paste_horiz (IsPullback.of_hasPullback sY _).flip
    haveI := hsq.isIso_fst_of_isIso
    let e : pointSettingCurve sY y ≃ₜ projectiveLine ℂ :=
      ((pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ))).fiberHomeo y).symm.trans
        (asIso (pullback.fst (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)))
          (Y.fromSpecResidueField y) ≫
            pullback.snd sY (projectiveLine ℂ ↘ Spec (.of ℂ)))).hom.homeomorph
    have hirr : IsIrreducible (pointSettingCurve sY y) := by
      have := (IrreducibleSpace.isIrreducible_univ (projectiveLine ℂ)).image
        (fun p => (e.symm p).1) (by fun_prop : Continuous fun p => (e.symm p).1).continuousOn
      convert this using 1
      ext x
      refine ⟨fun hx => ⟨e ⟨x, hx⟩, trivial, by simp⟩, ?_⟩
      rintro ⟨p, -, rfl⟩
      exact (e.symm p).2
    have hclosed : IsClosed (pointSettingCurve sY y) :=
      h.isClosed_singleton.preimage (pullback.fst sY _).continuous
    have hdimT : topologicalKrullDim (pointSettingCurve sY y) = 1 := by
      rw [IsHomeomorph.topologicalKrullDim_eq e e.isHomeomorph, hd₁]
    exact ⟨hIP, hLNP, hNP, ⟨pointSettingCurve sY y, hirr, hclosed⟩, rfl,
      h.isLocalSetting_pointSettingCurve hirr hclosed hdimT⟩

end ProductLocalSetting

end MMP.Fourfold

/-! ## Log discrepancies of centred valuations along étale maps -/

namespace MMP.Intersection

section

open TopologicalSpace AlgebraicGeometry

/-- **Restriction along an étale map preserves log discrepancies.** Let `q : Y_e ⟶ Y_0` be a
dominant étale morphism of normal varieties over a field `k` of characteristic zero, with
`K_{Y_0}` `ℚ`-Cartier, and let `η' ∈ Y_e` be a point with `κ(q η') → κ(η')` an isomorphism. If
`w` is a normalized divisorial valuation of `k(Y_e)` with centre `closure {η'}`, then for divisors
`D_e` over `Y_e` and `D_0` over `Y_0` (with proper structure maps) realizing `w` and
`w.comap (functionFieldMap q)`, the log discrepancies agree: `a(D_e; Y_e, 0) = a(D_0; Y_0, 0)`. -/
@[mmp "lem_oai4_local_restriction_injective_c"]
public theorem isLogDiscrepancy_iff_of_etale_of_isCentre {k : Type u} [Field k] [CharZero k]
    {Y₀ Yₑ : Scheme.{u}} [IsIntegral Y₀] [IsLocallyNoetherian Y₀] [IsNormal Y₀]
    [IsIntegral Yₑ] [IsLocallyNoetherian Yₑ] [IsNormal Yₑ]
    (s₀ : Y₀ ⟶ Spec (.of k)) (q : Yₑ ⟶ Y₀) [Etale q] [IsDominant q]
    (h₀ : MMP.Mori.IsPair s₀ (0 : MMP.Mori.QDivisor Y₀))
    (hₑ : MMP.Mori.IsNormalVariety k (q ≫ s₀))
    (η' : Yₑ) (hκ : IsIso (q.residueFieldMap η'))
    (Zₑ : IrreducibleCloseds Yₑ) (hZₑ : (Zₑ : Set Yₑ) = closure {η'})
    (w : Valuation Yₑ.functionField (WithZero (Multiplicative ℤ)))
    (hw : IsCentre k (q ≫ s₀) w Zₑ) :
    ∀ (Dₑ : MMP.Mori.DivisorOver k (q ≫ s₀)) (D₀ : MMP.Mori.DivisorOver k s₀),
      IsProper Dₑ.f → IsProper D₀.f → Dₑ.valuation = w →
        D₀.valuation = w.comap (functionFieldMap q) →
        ∀ (n : ℕ) (a : ℝ), IsLogDiscrepancy (q ≫ s₀) n 0 Dₑ a ↔
          IsLogDiscrepancy s₀ n 0 D₀ a :=
  (isLogDiscrepancy_iff_of_etale s₀ q h₀ hₑ w <| hw.imp fun _ h ↦ ⟨h.1, h.2.1⟩).2.2

end

end MMP.Intersection
