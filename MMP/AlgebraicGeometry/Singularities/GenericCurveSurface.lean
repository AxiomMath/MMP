module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldTerminalChainLabel
public import MMP.AlgebraicGeometry.MMP.Fourfold.Singularities
public import MMP.AlgebraicGeometry.Divisor.DivisorialValuation
public import MMP.AlgebraicGeometry.Singularities.LogDiscrepancy
import MMP.AlgebraicGeometry.MMP.Fourfold.Defs
import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldStabilizedTail
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison
import MMP.AlgebraicGeometry.Singularities.Surface.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.Resolution.DivisorTupleRestrictionLift
public import MMP.AlgebraicGeometry.Chow.FieldSituation

/-!
# The surface at the generic point of a curve of a threefold

Let `(X, B)` be an effective pair on a normal complex threefold and `V ⊆ X` an irreducible closed
curve with generic point `η_V`. On an affine open neighbourhood `X° = Spec A` of `η_V` there is a
regular function `u`, transcendental over `ℂ`, whose generic fibre `S` (the fibre of
`u : X° ⟶ 𝔸¹` over the generic point `Spec ℂ(u) ⟶ 𝔸¹`) is a normal affine surface over
`K = ℂ(u)` with function field `ℂ(X)`. The generic fibre of `V` is a single closed point `x` of
`S` with `𝒪_{S,x} = 𝒪_{X,η_V}`, whose residue field `ℂ(V)` is finite separable over `K`. The
restriction `B_S` of `B` makes `(S, B_S)` an effective pair over `K`, and normalized divisorial
valuations over `S` and over `X°` correspond, with the same log discrepancies, the ones centred
at `x` corresponding to the ones centred at `V`. In particular `(S, B_S)` is klt when `(X, B)` is.

## Main results

* `MMP.Fourfold.exists_generic_surface_of_curve`.

## Implementation notes

* The auxiliary lemmas live in the namespace `Proof_lem_mmp_indexc_generic_curve_surface`,
  opened only for the main result. The generic fibre is built as `Spec` of the localization of
  `A = Γ(X, U)` at the nonzero polynomials in `u`; a divisor over `S` is spread out to a divisor
  over `U` by realizing its valuation on a projective model, and log discrepancies are compared
  between a divisor over `S` and its spread-out model.
* The affine neighbourhood `X°` is an affine open `U ∋ η_V`, and `u ∈ Γ(U, 𝒪)`. The generic
  fibre is pinned as a pullback square: `ι : S ⟶ U` and `s_S : S ⟶ Spec K` form the pullback of
  `u : U ⟶ 𝔸¹_ℂ` along the point `Spec K ⟶ 𝔸¹_ℂ` given by an element `t ∈ K` transcendental over
  `ℂ` and generating `K`, which is the generic point of `𝔸¹_ℂ`.
* `ℂ(X)` is regarded as the function field of `S` through `ι` (`functionFieldMap`), and
  `K ⊆ ℂ(X)` through `s_S`. A valuation `ξ` of `ℂ(X)` is a valuation of `K(S)`, compared with
  valuations of `k(X)` and `k(U)` by `Valuation.comap` along the function-field maps.
* The centre `x` and `V ∩ U` are the irreducible closed sets `closure {x}` and
  `closure {η_V}` of `S` and `U`.
* `B_S` is pinned by its coefficients: the coefficient along a prime divisor `P` of `S` is that of
  `B` along the prime divisor of `X` with generic point `ι(η_P)`.
* A log discrepancy is a predicate on its value for a divisor realizing the valuation
  (`MMP.Intersection.IsLogDiscrepancy`, with the forms of degree `dim X = 3` and `dim S = 2`).
  The equality `a(ξ; S, B_S) = a(ξ; X, B)` reads: for any divisors over `S` and over `X`
  (proper structure maps) realizing the valuation, a real number is a log discrepancy of one
  exactly when it is one of the other. Over `X°` the boundary is `B|_U`, the inverse transform
  of `B` along `U ⟶ X`.

## References

* [OpenAI, *Projective lc fourfolds*], the index chain: the surface at the generic point of a
  curve.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace Proof_lem_mmp_indexc_generic_curve_surface

open MMP.Mori (QDivisor DivisorOver IsNormalVariety)

/-! ### The commutative algebra of the generic surface -/

section Algebra

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A] {d : ℕ}

/-- The image in `A` of the nonzero polynomials in `t`. -/
private noncomputable def polySubmonoid (t : Fin d → A) : Submonoid A :=
  (nonZeroDivisors (MvPolynomial (Fin d) k)).map (MvPolynomial.aeval (R := k) t)

private lemma aeval_mk_comp (𝔭 : Ideal A) (t : Fin d → A) (P : MvPolynomial (Fin d) k) :
    MvPolynomial.aeval (Ideal.Quotient.mk 𝔭 ∘ t) P =
      Ideal.Quotient.mk 𝔭 (MvPolynomial.aeval t P) :=
  (MvPolynomial.comp_aeval_apply t (Ideal.Quotient.mkₐ k 𝔭) P).symm

private lemma disjoint_polySubmonoid {𝔭 : Ideal A} (t : Fin d → A)
    (ht : AlgebraicIndependent k (Ideal.Quotient.mk 𝔭 ∘ t)) :
    Disjoint (polySubmonoid (k := k) t : Set A) 𝔭 := by
  rw [Set.disjoint_left]
  rintro _ ⟨P, hP, rfl⟩ hmem
  have h0 : MvPolynomial.aeval (Ideal.Quotient.mk 𝔭 ∘ t) P = 0 := by
    rwa [aeval_mk_comp, Ideal.Quotient.eq_zero_iff_mem]
  exact nonZeroDivisors.ne_zero hP ((injective_iff_map_eq_zero _).1 ht P h0)

variable (k) in
/-- The map `k(t) → A[M⁻¹]`. -/
private noncomputable def fracToLoc (t : Fin d → A) :
    FractionRing (MvPolynomial (Fin d) k) →+* Localization (polySubmonoid (k := k) t) :=
  IsLocalization.lift (M := nonZeroDivisors (MvPolynomial (Fin d) k))
    (g := (algebraMap A (Localization (polySubmonoid (k := k) t))).comp
      (MvPolynomial.aeval (R := k) t).toRingHom)
    (fun y => IsLocalization.map_units (Localization (polySubmonoid (k := k) t))
      (⟨_, ⟨y, y.2, rfl⟩⟩ : polySubmonoid (k := k) t))

private lemma fracToLoc_algebraMap (t : Fin d → A) (P : MvPolynomial (Fin d) k) :
    fracToLoc k t (algebraMap _ _ P) = algebraMap A _ (MvPolynomial.aeval t P) := by
  simp [fracToLoc, IsLocalization.lift_eq]

private lemma fracToLoc_comp_algebraMap (t : Fin d → A) :
    (fracToLoc k t).comp (algebraMap k (FractionRing (MvPolynomial (Fin d) k))) =
      (algebraMap A (Localization (polySubmonoid (k := k) t))).comp (algebraMap k A) := by
  ext c
  simp only [RingHom.comp_apply]
  rw [IsScalarTower.algebraMap_apply k (MvPolynomial (Fin d) k), fracToLoc_algebraMap]
  simp

private lemma exists_fracToLoc_mul_eq_one (t : Fin d → A) (m : polySubmonoid (k := k) t) :
    ∃ c, fracToLoc k t c * algebraMap A _ (m : A) = 1 := by
  obtain ⟨_, ⟨P, hP, rfl⟩⟩ := m
  refine ⟨(algebraMap _ (FractionRing (MvPolynomial (Fin d) k)) P)⁻¹, ?_⟩
  have hne : algebraMap _ (FractionRing (MvPolynomial (Fin d) k)) P ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hP
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at *
  rw [← fracToLoc_algebraMap, ← map_mul, inv_mul_cancel₀ hne, map_one]

private lemma mk'_eq_fracToLoc_mul (t : Fin d → A) (a : A) (m : polySubmonoid (k := k) t) :
    ∃ c, IsLocalization.mk' (Localization (polySubmonoid (k := k) t)) a m =
      fracToLoc k t c * algebraMap A _ a := by
  obtain ⟨c, hc⟩ := exists_fracToLoc_mul_eq_one t m
  refine ⟨c, ?_⟩
  rw [← IsLocalization.mk'_spec (Localization (polySubmonoid (k := k) t)) a m]
  calc _ = IsLocalization.mk' (Localization (polySubmonoid (k := k) t)) a m *
        (fracToLoc k t c * algebraMap A _ (m : A)) := by rw [hc, mul_one]
    _ = _ := by ring

/-- If the images of `t` in `A ⧸ 𝔭` form a transcendence basis over `k`, then `𝔭` generates a
maximal ideal of `A[M⁻¹]`. -/
private lemma isMaximal_map_polySubmonoid {𝔭 : Ideal A} [𝔭.IsPrime] (t : Fin d → A)
    (ht : IsTranscendenceBasis k (Ideal.Quotient.mk 𝔭 ∘ t)) :
    (𝔭.map (algebraMap A (Localization (polySubmonoid (k := k) t)))).IsMaximal := by
  set R := Localization (polySubmonoid (k := k) t)
  set K := FractionRing (MvPolynomial (Fin d) k)
  set 𝔮 := 𝔭.map (algebraMap A R)
  have hq : 𝔮.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint _ R 𝔭 ‹_›
    (disjoint_polySubmonoid t ht.1)
  let Q := R ⧸ 𝔮
  letI : Algebra K Q := ((Ideal.Quotient.mk 𝔮).comp (fracToLoc k t)).toAlgebra
  have hinj : Function.Injective (algebraMap K Q) := (algebraMap K Q).injective
  let ψ : A ⧸ 𝔭 →+* Q := Ideal.quotientMap 𝔮 (algebraMap A R) Ideal.le_comap_map
  let B := Algebra.adjoin k (Set.range (Ideal.Quotient.mk 𝔭 ∘ t))
  have halg : Algebra.IsAlgebraic B (A ⧸ 𝔭) := ht.isAlgebraic
  let θ : B →+* K := (algebraMap (MvPolynomial (Fin d) k) K).comp
    (ht.1.aevalEquiv.symm : B ≃ₐ[k] MvPolynomial (Fin d) k).toRingEquiv.toRingHom
  have hθ : Function.Injective θ :=
    (IsFractionRing.injective (MvPolynomial (Fin d) k) K).comp
      (ht.1.aevalEquiv.symm.injective)
  have hcomp : (algebraMap K Q).comp θ = ψ.comp (algebraMap B (A ⧸ 𝔭)) := by
    ext b
    obtain ⟨P, rfl⟩ := ht.1.aevalEquiv.surjective b
    simp only [RingHom.comp_apply, θ]
    change Ideal.Quotient.mk 𝔮 (fracToLoc k t (algebraMap _ K
      (ht.1.aevalEquiv.symm (ht.1.aevalEquiv P)))) = ψ ((ht.1.aevalEquiv P : A ⧸ 𝔭))
    rw [AlgEquiv.symm_apply_apply, fracToLoc_algebraMap]
    change _ = ψ (algebraMap B (A ⧸ 𝔭) (ht.1.aevalEquiv P))
    rw [ht.1.algebraMap_aevalEquiv, aeval_mk_comp]
    rfl
  have hint_a : ∀ a : A, IsIntegral K (Ideal.Quotient.mk 𝔮 (algebraMap A R a)) := fun a =>
    (IsAlgebraic.ringHom_of_comp_eq θ ψ (halg.isAlgebraic (Ideal.Quotient.mk 𝔭 a)) hθ
      hcomp).isIntegral
  have hint : Algebra.IsIntegral K Q := by
    refine ⟨fun q => ?_⟩
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨⟨a, m⟩, rfl⟩ := IsLocalization.mk'_surjective (polySubmonoid (k := k) t) r
    obtain ⟨c, hc⟩ := mk'_eq_fracToLoc_mul t a m
    simp only at hc ⊢
    rw [hc, map_mul]
    exact (isIntegral_algebraMap (x := c)).mul (hint_a a)
  have hdom : IsDomain Q := Ideal.Quotient.isDomain 𝔮
  have hfield : IsField Q := (Algebra.IsIntegral.isField_iff_isField hinj).1 (Field.toIsField K)
  exact Ideal.Quotient.maximal_of_isField 𝔮 hfield

/-- `A[M⁻¹]` is of finite type over `k(t)`. -/
private lemma finiteType_fracToLoc [Algebra.FiniteType k A] (t : Fin d → A) :
    (fracToLoc k t).FiniteType := by
  classical
  letI : Algebra (FractionRing (MvPolynomial (Fin d) k))
      (Localization (polySubmonoid (k := k) t)) :=
    (fracToLoc k t).toAlgebra
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := k) (A := A)
  change Algebra.FiniteType _ _
  refine Algebra.FiniteType.mk ⟨s.image (algebraMap A _), ?_⟩
  rw [eq_top_iff]
  rintro r -
  set T := Algebra.adjoin (FractionRing (MvPolynomial (Fin d) k))
    (↑(s.image (algebraMap A (Localization (polySubmonoid (k := k) t)))) :
      Set (Localization (polySubmonoid (k := k) t)))
  have hA : ∀ a : A, algebraMap A _ a ∈ T := by
    intro a
    have ha : a ∈ Algebra.adjoin k (s : Set A) := hs ▸ Algebra.mem_top
    induction ha using Algebra.adjoin_induction with
    | mem x hx => exact Algebra.subset_adjoin (by simpa using ⟨x, hx, rfl⟩)
    | algebraMap c =>
      have : algebraMap A (Localization (polySubmonoid (k := k) t)) (algebraMap k A c) =
          algebraMap (FractionRing (MvPolynomial (Fin d) k)) _ (algebraMap k _ c) :=
        (congrArg (fun f => f c) (fracToLoc_comp_algebraMap (k := k) t)).symm
      rw [this]
      exact T.algebraMap_mem _
    | add x y _ _ hx hy => simpa only [map_add] using T.add_mem hx hy
    | mul x y _ _ hx hy => simpa only [map_mul] using T.mul_mem hx hy
  obtain ⟨⟨a, m⟩, rfl⟩ := IsLocalization.mk'_surjective (polySubmonoid (k := k) t) r
  obtain ⟨c, hc⟩ := mk'_eq_fracToLoc_mul t a m
  simp only at hc ⊢
  rw [hc]
  exact T.mul_mem (T.algebraMap_mem c) (hA a)

end Algebra

open MMP.Mori (sectionAlgebra)

section Scheme

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) {U : X.Opens}
  {d : ℕ} (t : Fin d → Γ(X, U))

/-- The submonoid of `Γ(X, U)` of nonzero polynomials in `t`. -/
private noncomputable def genSubmonoid : Submonoid Γ(X, U) :=
  @polySubmonoid k _ Γ(X, U) _ (sectionAlgebra sX U) d t

/-- The ring `Γ(X, U)[M⁻¹]` of the generic surface. -/
private noncomputable abbrev genRing : CommRingCat.{u} := .of (Localization (genSubmonoid sX t))

/-- The field `k(t)`. -/
private abbrev genField (k : Type u) [Field k] (d : ℕ) : Type u :=
  FractionRing (MvPolynomial (Fin d) k)

/-- The structure morphism of the generic surface. -/
private noncomputable def genStructure : Spec (genRing sX t) ⟶ Spec (.of (genField k d)) :=
  Spec.map (CommRingCat.ofHom (@fracToLoc k _ Γ(X, U) _ (sectionAlgebra sX U) d t))

/-- The morphism from the generic surface to `U`. -/
private noncomputable def genι (hU : IsAffineOpen U) : Spec (genRing sX t) ⟶ U :=
  Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization (genSubmonoid sX t)))) ≫
    hU.isoSpec.inv

private lemma isIso_stalkMap_genι (hU : IsAffineOpen U) (q : Spec (genRing sX t)) :
    IsIso ((genι sX t hU).stalkMap q) := by
  rw [genι, Scheme.Hom.stalkMap_comp]
  have h1 : IsIso ((Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U)
      (Localization (genSubmonoid sX t))))).stalkMap q) :=
    isIso_SpecMap_stakMap_localization Γ(X, U) (genSubmonoid sX t) q
  have h2 := @IsOpenImmersion.instIsIsoCommRingCatStalkMap _ _ hU.isoSpec.inv
    (IsOpenImmersion.of_isIso _) ((Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U)
      (Localization (genSubmonoid sX t))))) q)
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h2 h1

private lemma isNormal_of_isIso_stalkMap {S Y : Scheme.{u}} [IsNormal Y] (f : S ⟶ Y)
    (h : ∀ q, IsIso (f.stalkMap q)) : IsNormal S := by
  refine ⟨fun q => have := h q; ?_, fun q => have := h q; ?_⟩
  · exact MulEquiv.isDomain (Y.presheaf.stalk (f q))
      (asIso (f.stalkMap q)).commRingCatIsoToRingEquiv.symm.toMulEquiv
  · have := IsNormal.stalk_normal (X := Y) (f q)
    exact IsIntegrallyClosed.of_equiv (asIso (f.stalkMap q)).commRingCatIsoToRingEquiv

private lemma isDomain_genRing [IsIntegral X] [Nonempty U] {𝔭 : Ideal Γ(X, U)}
    (ht : letI := sectionAlgebra sX U; AlgebraicIndependent k (Ideal.Quotient.mk 𝔭 ∘ t)) :
    IsDomain (Localization (genSubmonoid sX t)) := by
  letI := sectionAlgebra sX U
  refine IsLocalization.isDomain_of_le_nonZeroDivisors _ (M := genSubmonoid sX t)
    (le_nonZeroDivisors_of_noZeroDivisors fun h0 => ?_)
  exact Set.disjoint_left.1 (disjoint_polySubmonoid t ht) h0 (Ideal.zero_mem 𝔭)

variable (hU : IsAffineOpen U) {x : X} (hxU : x ∈ U)

/-- The point `p = 𝔭 Γ(X, U)[M⁻¹]` of the generic surface. -/
private noncomputable def genPoint
    (ht : letI := sectionAlgebra sX U;
      AlgebraicIndependent k (Ideal.Quotient.mk (hU.primeIdealOf ⟨x, hxU⟩).asIdeal ∘ t)) :
    Spec (genRing sX t) :=
  ⟨(hU.primeIdealOf ⟨x, hxU⟩).asIdeal.map (algebraMap Γ(X, U) (Localization (genSubmonoid sX t))),
    letI := sectionAlgebra sX U
    IsLocalization.isPrime_of_isPrime_disjoint (genSubmonoid sX t) _ _ inferInstance
      (disjoint_polySubmonoid t ht)⟩

private lemma genι_genPoint
    (ht : letI := sectionAlgebra sX U;
      AlgebraicIndependent k (Ideal.Quotient.mk (hU.primeIdealOf ⟨x, hxU⟩).asIdeal ∘ t)) :
    genι sX t hU (genPoint sX t hU hxU ht) = ⟨x, hxU⟩ := by
  letI := sectionAlgebra sX U
  have h1 : (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U)
      (Localization (genSubmonoid sX t))))) (genPoint sX t hU hxU ht) =
      hU.primeIdealOf ⟨x, hxU⟩ :=
    PrimeSpectrum.ext (IsLocalization.comap_map_of_isPrime_disjoint (genSubmonoid sX t) _
      inferInstance (disjoint_polySubmonoid t ht))
  rw [genι, Scheme.Hom.comp_apply, h1, IsAffineOpen.primeIdealOf]
  change (hU.isoSpec.hom ≫ hU.isoSpec.inv) _ = _
  rw [Iso.hom_inv_id]
  rfl

private lemma isClosed_genPoint
    (ht : letI := sectionAlgebra sX U;
      IsTranscendenceBasis k (Ideal.Quotient.mk (hU.primeIdealOf ⟨x, hxU⟩).asIdeal ∘ t)) :
    IsClosed ({genPoint sX t hU hxU ht.1} : Set (Spec (genRing sX t))) := by
  letI := sectionAlgebra sX U
  exact (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2 (isMaximal_map_polySubmonoid t ht)

private lemma genι_comp_eq :
    genι sX t hU ≫ U.ι ≫ sX =
      genStructure sX t ≫ Spec.map (CommRingCat.ofHom (algebraMap k (genField k d))) := by
  letI := sectionAlgebra sX U
  rw [genι, Category.assoc, ← Category.assoc hU.isoSpec.inv, hU.isoSpec_inv_ι,
    ← IsAffineOpen.SpecMap_appLE_fromSpec sX (isAffineOpen_top _) hU (by simp),
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, genStructure, ← Spec.map_comp,
    ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext c
  exact (congrArg (fun f => f c) (fracToLoc_comp_algebraMap (k := k) t)).symm

private lemma locallyOfFiniteType_genStructure [LocallyOfFiniteType sX] (hU : IsAffineOpen U) :
    LocallyOfFiniteType (genStructure sX t) := by
  letI := sectionAlgebra sX U
  haveI := MMP.Mori.finiteType_sectionAlgebra sX hU
  exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2 (finiteType_fracToLoc t)

private lemma isDominant_genι [IsIntegral X] [Nonempty U] {𝔭 : Ideal Γ(X, U)}
    (ht : letI := sectionAlgebra sX U; AlgebraicIndependent k (Ideal.Quotient.mk 𝔭 ∘ t)) :
    IsDominant (genι sX t hU) := by
  letI := sectionAlgebra sX U
  have hle : genSubmonoid sX t ≤ nonZeroDivisors Γ(X, U) :=
    le_nonZeroDivisors_of_noZeroDivisors fun h0 =>
      Set.disjoint_left.1 (disjoint_polySubmonoid t ht) h0 (Ideal.zero_mem 𝔭)
  have hinj : Function.Injective (algebraMap Γ(X, U) (Localization (genSubmonoid sX t))) :=
    IsLocalization.injective _ hle
  have h1 : IsDominant (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(X, U) (Localization (genSubmonoid sX t))))) := by
    rw [isDominant_iff]
    refine (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 ?_
    intro a ha
    rw [RingHom.mem_ker] at ha
    rw [hinj (ha.trans (map_zero _).symm)]
    exact zero_mem _
  have h2 : IsDominant hU.isoSpec.inv := inferInstance
  rw [genι]
  haveI := h1
  exact (IsDominant.comp_iff (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(X, U) (Localization (genSubmonoid sX t))))) hU.isoSpec.inv).2 h2

private lemma isIso_stalkMap_genι_comp (hU : IsAffineOpen U) (q : Spec (genRing sX t)) :
    IsIso ((genι sX t hU ≫ U.ι).stalkMap q) := by
  rw [Scheme.Hom.stalkMap_comp]
  have h1 := isIso_stalkMap_genι sX t hU q
  have h2 := @IsOpenImmersion.instIsIsoCommRingCatStalkMap _ _ U.ι inferInstance (genι sX t hU q)
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h2 h1

private lemma injective_genι (hU : IsAffineOpen U) : Function.Injective (genι sX t hU ≫ U.ι) := by
  intro a b h
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at h
  have h1 := U.ι.isOpenEmbedding.injective h
  rw [genι, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at h1
  have h2 : hU.isoSpec.hom (hU.isoSpec.inv _) = hU.isoSpec.hom (hU.isoSpec.inv _) :=
    congrArg hU.isoSpec.hom h1
  change (hU.isoSpec.inv ≫ hU.isoSpec.hom) _ = (hU.isoSpec.inv ≫ hU.isoSpec.hom) _ at h2
  rw [Iso.inv_hom_id] at h2
  exact PrimeSpectrum.localization_comap_injective (Localization (genSubmonoid sX t))
    (genSubmonoid sX t) h2

end Scheme

private lemma coheight_eq_of_isIso_stalkMap {Y Z : Scheme.{u}} (f : Y ⟶ Z) (y : Y)
    (h : IsIso (f.stalkMap y)) : Order.coheight (f y) = Order.coheight y := by
  have h1 := ringKrullDim_stalk_eq_coheight (f y)
  have h2 := ringKrullDim_stalk_eq_coheight y
  rw [ringKrullDim_eq_of_ringEquiv (asIso (f.stalkMap y)).commRingCatIsoToRingEquiv, h2] at h1
  exact_mod_cast h1.symm

/-- The generic surface has the function field of `U`: `ι = genι` is an isomorphism on all
stalks, in particular at the generic point. -/
private lemma bijective_functionFieldMap_genι {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) {U : X.Opens} {d : ℕ} (t : Fin d → Γ(X, U)) (hU : IsAffineOpen U)
    [IsIntegral U] [IsIntegral (Spec (genRing sX t))] [IsDominant (genι sX t hU)] :
    Function.Bijective (functionFieldMap (genι sX t hU)) := by
  haveI := isIso_stalkMap_genι sX t hU (genericPoint (Spec (genRing sX t)))
  exact ConcreteCategory.bijective_of_isIso
    ((U.toScheme.presheaf.stalkCongr (Inseparable.of_eq
      (map_genericPoint_of_isDominant (genι sX t hU)).symm)).hom ≫
      (genι sX t hU).stalkMap (genericPoint _))

section Boundary

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) {U : X.Opens}
  {d : ℕ} (t : Fin d → Γ(X, U)) (hU : IsAffineOpen U)

/-- The prime divisor of `X` whose generic point is the image of that of a prime divisor `P` of
the generic surface. -/
private noncomputable def genPrimeDivisor (P : MMP.Mori.PrimeDivisor (Spec (genRing sX t))) :
    MMP.Mori.PrimeDivisor X :=
  PrimeDivisor.ofCoheightOne ((genι sX t hU ≫ U.ι) P.genericPoint) (by
    rw [coheight_eq_of_isIso_stalkMap _ _ (isIso_stalkMap_genι_comp sX t hU _)]
    exact PrimeDivisor.coheight_genericPoint P)

private lemma genericPoint_genPrimeDivisor (P : MMP.Mori.PrimeDivisor (Spec (genRing sX t))) :
    (genPrimeDivisor sX t hU P).genericPoint = U.ι (genι sX t hU P.genericPoint) :=
  PrimeDivisor.genericPoint_ofCoheightOne _ _

private lemma injective_genPrimeDivisor : Function.Injective (genPrimeDivisor sX t hU) := by
  intro P Q h
  have h1 := congrArg MMP.Mori.PrimeDivisor.genericPoint h
  simp only [MMP.Mori.PrimeDivisor.genericPoint, genPrimeDivisor,
    PrimeDivisor.genericPoint_ofCoheightOne] at h1
  exact PrimeDivisor.genericPoint_injective (injective_genι sX t hU h1)

/-- The boundary `B_S` of the generic surface: the coefficient of a prime divisor `P` is that of
`B` along `genPrimeDivisor P`. -/
private noncomputable def genBoundary (B : MMP.Mori.QDivisor X) :
    MMP.Mori.QDivisor (Spec (genRing sX t)) :=
  Finsupp.comapDomain (genPrimeDivisor sX t hU) B
    (injective_genPrimeDivisor sX t hU).injOn

private lemma coeff_genBoundary (B : MMP.Mori.QDivisor X)
    (P : MMP.Mori.PrimeDivisor (Spec (genRing sX t))) :
    (genBoundary sX t hU B).coeff P = B.coeff (genPrimeDivisor sX t hU P) :=
  Finsupp.comapDomain_apply _ _ _ _

end Boundary

private lemma surjective_residueFieldMap {Y Z : Scheme.{u}} (f : Y ⟶ Z) (y : Y)
    [IsIso (f.stalkMap y)] :
    Function.Surjective (f.residueFieldMap y) := by
  intro z
  obtain ⟨s, rfl⟩ := Y.residue_surjective y z
  refine ⟨Z.residue (f y) (inv (f.stalkMap y) s), ?_⟩
  rw [← CommRingCat.comp_apply, Scheme.residue_residueFieldMap, CommRingCat.comp_apply,
    ← CommRingCat.comp_apply (inv _), IsIso.inv_hom_id, CommRingCat.id_apply]

private lemma exists_fin_isTranscendenceBasis (k A : Type*) [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] :
    ∃ (d : ℕ) (x : Fin d → A), IsTranscendenceBasis k x := by
  have : FaithfulSMul k A := (faithfulSMul_iff_algebraMap_injective k A).2
    (algebraMap k A).injective
  obtain ⟨ι, x, hx⟩ := exists_isTranscendenceBasis' k A
  have h := hx.lift_cardinalMk_eq_trdeg
  rw [Cardinal.lift_id, Cardinal.lift_id] at h
  have : Finite ι := Cardinal.lt_aleph0_iff_finite.1 (h ▸ trdeg_lt_aleph0_of_finiteType)
  have := Fintype.ofFinite ι
  let e := Fintype.equivFin ι
  exact ⟨Fintype.card ι, x ∘ e.symm, hx.comp_equiv e.symm⟩

private lemma isTranscendenceBasis_genField (k : Type*) [Field k] (d : ℕ) :
    IsTranscendenceBasis k
      (fun i => algebraMap (MvPolynomial (Fin d) k) (FractionRing (MvPolynomial (Fin d) k))
        (MvPolynomial.X i)) :=
  have := IsLocalization.isAlgebraic (S := FractionRing (MvPolynomial (Fin d) k))
    (nonZeroDivisors (MvPolynomial (Fin d) k))
  (IsTranscendenceBasis.mvPolynomial (Fin d) k).algebraMap_comp

private lemma adjoin_genField_eq_top (k : Type*) [Field k] (d : ℕ) :
    IntermediateField.adjoin k (Set.range (fun i => algebraMap (MvPolynomial (Fin d) k)
      (FractionRing (MvPolynomial (Fin d) k)) (MvPolynomial.X i))) = ⊤ := by
  rw [eq_top_iff]
  intro z _
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial (Fin d) k) z
  have hmem : ∀ P : MvPolynomial (Fin d) k, algebraMap _ (FractionRing (MvPolynomial (Fin d) k)) P ∈
      IntermediateField.adjoin k (Set.range (fun i => algebraMap (MvPolynomial (Fin d) k)
        (FractionRing (MvPolynomial (Fin d) k)) (MvPolynomial.X i))) := by
    intro P
    induction P using MvPolynomial.induction_on with
    | C c =>
      rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
      exact IntermediateField.algebraMap_mem _ c
    | add p q hp hq => simpa only [map_add] using add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul]
      exact mul_mem hp (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
  exact div_mem (hmem a) (hmem b)

/-! ### Restriction to an open subscheme -/

section OpenRestriction

open MMP.Mori Opposite

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X]

/-- A nonempty open subscheme of an irreducible scheme is dense. -/
private theorem isDominant_opens_ι {Y : Scheme.{u}} [IrreducibleSpace Y] (V : Y.Opens)
    [Nonempty V] : IsDominant V.ι :=
  Opens.isDominant_ι (V.isOpen.dense ⟨_, (Classical.arbitrary V).2⟩)

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

/-- On an integral scheme the generic point of every irreducible component is the generic
point. -/
private theorem componentGenericPoint_eq_genericPoint {Y : Scheme.{u}} [IsIntegral Y]
    (Z : irreducibleComponents Y) : componentGenericPoint Y Z = genericPoint Y := by
  have h1 := isGenericPoint_componentGenericPoint Y Z
  rw [eq_univ_of_irreducibleComponents Z] at h1
  exact h1.eq (genericPoint_spec Y)

private theorem index_eq {Y : Scheme.{u}} [IrreducibleSpace Y] {W : Y.Opens}
    (Z Z' : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) : Z = Z' :=
  Subtype.ext (Subtype.ext ((eq_univ_of_irreducibleComponents _).trans
    (eq_univ_of_irreducibleComponents _).symm))

private theorem genericPoint_specializes {Y : Scheme.{u}} [IsIntegral Y]
    (Z : irreducibleComponents Y) : genericPoint Y ⤳ componentGenericPoint Y Z :=
  (genericPoint_spec Y).specializes trivial

private theorem specializes_genericPoint {Y : Scheme.{u}} [IsIntegral Y]
    (Z : irreducibleComponents Y) : componentGenericPoint Y Z ⤳ genericPoint Y :=
  (Inseparable.of_eq (componentGenericPoint_eq_genericPoint Z)).specializes

private theorem stalkSpecializes_stalkSpecializes_apply {Y : Scheme.{u}} {x y z : Y}
    (h : x ⤳ y) (h' : y ⤳ z) (h'' : x ⤳ z) (s : Y.presheaf.stalk z) :
    (Y.presheaf.stalkSpecializes h).hom ((Y.presheaf.stalkSpecializes h').hom s) =
      (Y.presheaf.stalkSpecializes h'').hom s :=
  TopCat.Presheaf.stalkSpecializes_comp_apply _ h h' s

private theorem stalkSpecializes_self_apply {Y : Scheme.{u}} {x : Y} (h : x ⤳ x)
    (s : Y.presheaf.stalk x) : (Y.presheaf.stalkSpecializes h).hom s = s := by
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  rfl

/-- The value in the function field of a section of `𝒦_Y` over an open set, read at the generic
point of an irreducible component meeting it. -/
private noncomputable def evFF {Y : Scheme.{u}} [IsIntegral Y] {W : Y.Opens}
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (Z : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) : Y.functionField :=
  (Y.presheaf.stalkSpecializes (genericPoint_specializes Z.1)).hom (φ Z)

private theorem evFF_eq {Y : Scheme.{u}} [IsIntegral Y] {W : Y.Opens}
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (Z Z' : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) :
    evFF φ Z = evFF φ Z' := by
  obtain rfl := index_eq Z Z'
  rfl

private theorem stalkSpecializes_injective {Y : Scheme.{u}} [IsIntegral Y]
    (Z : irreducibleComponents Y) :
    Function.Injective (Y.presheaf.stalkSpecializes (genericPoint_specializes Z)).hom := by
  intro a b h
  have := congrArg (Y.presheaf.stalkSpecializes (specializes_genericPoint Z)).hom h
  rwa [stalkSpecializes_stalkSpecializes_apply _ _ specializes_rfl,
    stalkSpecializes_stalkSpecializes_apply _ _ specializes_rfl, stalkSpecializes_self_apply,
    stalkSpecializes_self_apply] at this

/-- `v_E` on the factor `𝒪_{Y,η}` of `𝒦_Y` is the inverse of the divisorial valuation of the
corresponding rational function. -/
private theorem valuation_eq_inv_divisorialValuation {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (E : MMP.Mori.PrimeDivisor Y)
    (s : Y.presheaf.stalk (componentGenericPoint Y E.component)) :
    E.valuation s = (E.divisorialValuation
      ((Y.presheaf.stalkSpecializes (genericPoint_specializes E.component)).hom s))⁻¹ := by
  rw [MMP.Threefold.Mori.Helpers.valuation_eq_ordFrac,
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_inv_ordHom, inv_inv]
  rfl

private theorem ordGE_iff {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (E : MMP.Mori.PrimeDivisor Y) (n : ℤ)
    (s : Y.presheaf.stalk (componentGenericPoint Y E.component)) :
    E.OrdGE n s ↔
      ((Y.presheaf.stalkSpecializes (genericPoint_specializes E.component)).hom s = 0 ∨
        WithZero.exp n ≤ (E.divisorialValuation
          ((Y.presheaf.stalkSpecializes (genericPoint_specializes E.component)).hom s))⁻¹) := by
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

/-- The unique irreducible component `Y` of an irreducible scheme `Y`. -/
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
private noncomputable def restrictRF (V : U.toScheme.Opens)
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    ToType ((rationalFunctionsPresheaf U.toScheme).obj (op V)) :=
  fun Z => (U.toScheme.presheaf.stalkSpecializes (specializes_genericPoint Z.1)).hom
    (functionFieldMap U.ι (evFF ψ (indexX U (genericPoint_mem_of_index U Z))))

private theorem evFF_restrictRF (V : U.toScheme.Opens)
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V))))
    (Z : {Z : irreducibleComponents U.toScheme // componentGenericPoint U.toScheme Z ∈ V})
    (Z' : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U.ι ''ᵁ V}) :
    evFF (restrictRF U V ψ) Z = functionFieldMap U.ι (evFF ψ Z') := by
  rw [evFF, restrictRF, stalkSpecializes_stalkSpecializes_apply _ _ specializes_rfl,
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
  rw [stalkSpecializes_stalkSpecializes_apply _ _ specializes_rfl, stalkSpecializes_self_apply]
  change (U.toScheme.presheaf.stalkSpecializes (specializes_genericPoint Z.1)).hom
    (e (e.symm _)) = _
  rw [RingEquiv.apply_symm_apply, evFF_eq φ _ Z, evFF,
    stalkSpecializes_stalkSpecializes_apply _ _ specializes_rfl, stalkSpecializes_self_apply]

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
    exact ⟨fun h => ⟨_, h, rfl⟩, fun ⟨x, hx, hxe⟩ => by
      rwa [U.ι.isOpenEmbedding.injective hxe] at hx⟩
  constructor
  · intro h P hP
    have hPU : P.genericPoint ∈ Set.range U.ι.base := by
      rw [Scheme.Opens.range_ι]
      obtain ⟨x, -, hx⟩ := (MMP.Mori.PrimeDivisor.genericPoint_mem_iff P _).2 hP
      rw [← hx]
      exact x.2
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
private noncomputable def divisorialSheafRestrictHom (D : Divisor X) :
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

/-- The smooth locus of an open subscheme `U ⊆ X` lies in the smooth locus of `X`. -/
private theorem range_smoothLocus_subset (U : X.Opens) :
    Set.range ((smoothLocus (U.ι ≫ sX)).ι ≫ U.ι) ⊆ Set.range (smoothLocus sX).ι := by
  rintro _ ⟨x, rfl⟩
  rw [Scheme.Opens.range_ι]
  obtain ⟨W, hxW, hW⟩ := mem_smoothLocus_iff.1 x.2
  let V := (W.ι ≫ U.ι).opensRange
  have e : (W.ι ≫ U.ι).isoOpensRange.inv ≫ (W.ι ≫ U.ι) = V.ι := by
    rw [Iso.inv_comp_eq, Scheme.Hom.isoOpensRange_hom_ι]
  have hV : Smooth (V.ι ≫ sX) := by
    rw [← e, Category.assoc, Category.assoc]
    infer_instance
  exact le_smoothLocus sX hV ⟨⟨x.1, hxW⟩, rfl⟩

/-- On the smooth locus of a nonempty open subscheme `U`, the divisorial sheaf of `K|_U` is the
canonical sheaf when that of `K` is on the smooth locus of `X`. -/
private theorem nonempty_restrict_smoothLocus_iso {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX n) (U : X.Opens) [Nonempty U] [IsDominant U.ι] :
    Nonempty ((Divisor.divisorialSheaf (K.restrictOpen U)).restrict (smoothLocus (U.ι ≫ sX)).ι ≅
      canonicalSheaf (U.ι ≫ sX) n) := by
  obtain ⟨e₀⟩ := nonempty_divisorialSheaf_restrictOpen_iso K U
  let T := smoothLocus (U.ι ≫ sX)
  let S := smoothLocus sX
  let ψ : T.toScheme ⟶ S := IsOpenImmersion.lift S.ι (T.ι ≫ U.ι) (range_smoothLocus_subset U)
  have hψ : ψ ≫ S.ι = T.ι ≫ U.ι := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨e₁⟩ := nonempty_restrict_relativeDifferentialForms_iso ψ (S.ι ≫ sX)
    (T.ι ≫ U.ι ≫ sX) (by rw [← Category.assoc, hψ, Category.assoc]) n
  exact ⟨(Scheme.Modules.restrictFunctor T.ι).mapIso e₀ ≪≫
    (Scheme.Modules.restrictFunctorComp T.ι U.ι).symm.app _ ≪≫
    (Scheme.Modules.restrictFunctorCongr hψ.symm).app _ ≪≫
    (Scheme.Modules.restrictFunctorComp ψ S.ι).app _ ≪≫
    (Scheme.Modules.restrictFunctor ψ).mapIso hK.iso ≪≫ e₁⟩

/-- The restriction of a canonical divisor to a nonempty open subscheme is canonical. -/
private theorem isCanonicalDivisor_restrictOpen {n : ℕ} {K : Divisor X}
    (hX : IsNormalVariety k sX) (hK : K.IsCanonicalDivisor sX n) (U : X.Opens) [Nonempty U]
    [IsDominant U.ι] :
    Divisor.IsCanonicalDivisor (U.ι ≫ sX) n (K.restrictOpen U) :=
  ⟨(topologicalKrullDim_opens_eq hX U).trans hK.1, nonempty_restrict_smoothLocus_iso hK U⟩

/-- The closure in `X` of a prime divisor of `U` meeting `U ∩ V` meets `V`. -/
private theorem primeDivisorMap_support_inter_nonempty (U : X.Opens) [Nonempty U]
    [IsDominant U.ι] {V : X.Opens} (W : MMP.Mori.PrimeDivisor U.toScheme)
    (hW : (W.support ∩ U.ι ⁻¹ᵁ V).Nonempty) :
    ((OpenWeilRestriction.primeDivisorMap U.ι W).support ∩ V).Nonempty := by
  rw [← MMP.Mori.PrimeDivisor.genericPoint_mem_iff]
  exact (congrArg (· ∈ V) (OpenWeilRestriction.genericPoint_primeDivisorMap U.ι W)).mpr
    ((W.genericPoint_mem_iff _).2 hW)

/-- The restriction of a Cartier divisor to a dense open subscheme is Cartier: a local equation
`φ` of `D` on `V` gives the local equation `φ|_U` of `D|_U` on `U ∩ V`, since the closure in `X`
of a prime divisor of `U` has the same local ring. -/
private theorem isCartier_restrictOpen {D : Divisor X} (h : D.IsCartier) (U : X.Opens)
    [Nonempty U] [IsDominant U.ι] : Divisor.IsCartier (D.restrictOpen U) := by
  intro x
  obtain ⟨V, hxV, φ, hφ⟩ := h (U.ι x)
  obtain ⟨g, hg, hφg⟩ := MMP.Positivity.exists_ord_eq_of_units φ
  obtain ⟨φ', hφ'⟩ := MMP.Positivity.exists_units_of_ne_zero
    ((map_ne_zero (functionFieldMap U.ι)).2 hg)
  refine ⟨U.ι ⁻¹ᵁ V, hxV, φ', fun W hW => ?_⟩
  have hP := primeDivisorMap_support_inter_nonempty U W hW
  rw [DivisorWithCoeffs.coeff_restrictOpen, hφ _ hP, hφg, hφ',
    MMP.Positivity.ord_functionFieldMap_of_isIso U.ι W _
      (OpenWeilRestriction.genericPoint_primeDivisorMap _ _).symm]

/-- The restriction of a Cartier `ℚ`-divisor of the form `m(K + Δ)` is Cartier. -/
private theorem isCartierDivisor_smul_restrictOpen {K : Divisor X} {Δ : QDivisor X} {m : ℕ}
    (h : ((m : ℤ) • (Divisor.toQDivisor K + Δ)).IsCartierDivisor) (U : X.Opens) [Nonempty U]
    [IsDominant U.ι] :
    ((m : ℤ) • (Divisor.toQDivisor (K.restrictOpen U) + Δ.restrictOpen U)).IsCartierDivisor := by
  obtain ⟨D', hD', hC⟩ := h
  refine ⟨D'.restrictOpen U, ?_, isCartier_restrictOpen hC U⟩
  ext W
  have := congrArg
    (fun E => DivisorWithCoeffs.coeff E (OpenWeilRestriction.primeDivisorMap U.ι W)) hD'
  simpa using this

/-- The restriction of `V.ι` to the preimage of `V` is an isomorphism. -/
private lemma isIso_ι_morphismRestrict {Y : Scheme.{u}} (V : Y.Opens) : IsIso (V.ι ∣_ V) := by
  rw [isIso_iff_isOpenImmersion_and_surjective]
  refine ⟨inferInstance, ⟨fun y => ⟨(⟨y, by simp⟩ : (V.ι ⁻¹ᵁ V).toScheme),
    V.ι.isOpenEmbedding.injective ?_⟩⟩⟩
  have h := congrArg (fun f : (V.ι ⁻¹ᵁ V).toScheme ⟶ Y =>
    f (⟨y, by simp⟩ : (V.ι ⁻¹ᵁ V).toScheme)) (morphismRestrict_ι V.ι V)
  simp only [Scheme.Hom.comp_apply] at h
  exact h

/-- The inverse transform of a divisor along an open immersion is its restriction. -/
private lemma inverseTransformDivisor_ι_eq_restrictOpen {Y : Scheme.{u}} (V : Y.Opens)
    {R : Type*} [AddCommMonoid R] (B : DivisorWithCoeffs R Y) :
    MMP.Mori.inverseTransformDivisor V.ι B = B.restrictOpen V := by
  ext W
  change DivisorWithCoeffs.mapPrimeDivisors (MMP.Mori.inverseTransformPrimeDivisor V.ι) B W =
    (B.restrictOpen V).coeff W
  rw [DivisorWithCoeffs.coeff_restrictOpen]
  have hη : V.ι W.genericPoint = (OpenWeilRestriction.primeDivisorMap V.ι W).genericPoint :=
    (OpenWeilRestriction.genericPoint_primeDivisorMap _ _).symm
  have hV : V.ι W.genericPoint ∈ MMP.Mori.biregularLocus V.ι :=
    MMP.Mori.le_biregularLocus (isIso_ι_morphismRestrict V)
      (by
        have : V.ι W.genericPoint ∈ Set.range V.ι := Set.mem_range_self _
        rwa [Scheme.Opens.range_ι] at this)
  refine MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
    (MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint hη hV)
    (fun E' hE' => ?_) B
  have h1 := (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
    hE').1
  exact PrimeDivisor.genericPoint_injective (h1.symm.trans hη)

/-- `(U, B|_U)` is a pair when `(X, B)` is. -/
private lemma isPair_ι {B : QDivisor X} (hP : IsPair sX B) (U : X.Opens) [Nonempty U]
    [IsDominant U.ι] : IsPair (U.ι ≫ sX) (MMP.Mori.inverseTransformDivisor U.ι B) := by
  obtain ⟨hX, n, K, hK, hQ⟩ := hP
  obtain ⟨m, hm, hC⟩ := hQ.exists_pos
  rw [inverseTransformDivisor_ι_eq_restrictOpen]
  exact ⟨isNormalVariety_ι hX U, n, K.restrictOpen U, isCanonicalDivisor_restrictOpen hX hK U, m,
    by exact_mod_cast hm.ne', isCartierDivisor_smul_restrictOpen hC U⟩

end OpenRestriction

/-! ### The determinant comparison of top forms -/

section Determinant

open KaehlerDifferential
open MMP.Mori (topFormsMap topFormsBasis topFormsBasis_apply topFormsMap_ιMulti ordAt ordAt_eq
  formCoeff PluriForms ZTensorPower span_singleton_topFormsMap)

section Pair

variable {L M W : Type*} [Field L] [AddCommGroup M] [Module L M] [AddCommGroup W] [Module L W]

private lemma append_pair_update₀ {n : ℕ} (a : Fin n → M) (u u' w : M) :
    (Fin.append a ![u, w] : Fin (n + 2) → M) =
      Function.update (Fin.append a ![u', w]) (Fin.natAdd n 0) u := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [Function.update_of_ne (by simp [Fin.ext_iff]; omega)]
    simp
  · fin_cases j <;> simp [Function.update, Fin.ext_iff]

private lemma append_pair_update₁ {n : ℕ} (a : Fin n → M) (u w w' : M) :
    (Fin.append a ![u, w] : Fin (n + 2) → M) =
      Function.update (Fin.append a ![u, w']) (Fin.natAdd n 1) w := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [Function.update_of_ne (by simp [Fin.ext_iff]; omega)]
    simp
  · fin_cases j <;> simp [Function.update, Fin.ext_iff]

/-- The bilinear map `(u, w) ↦ g(a₁, …, aₙ, u, w)` of an alternating map `g` in `n + 2`
arguments with the first `n` fixed. -/
private noncomputable def pairMap {n : ℕ} (g : M [⋀^Fin (n + 2)]→ₗ[L] W) (a : Fin n → M) :
    M →ₗ[L] M →ₗ[L] W :=
  LinearMap.mk₂ L (fun u w => g (Fin.append a ![u, w]))
    (fun u₁ u₂ w => by
      rw [append_pair_update₀ a (u₁ + u₂) 0 w, append_pair_update₀ a u₁ 0 w,
        append_pair_update₀ a u₂ 0 w, g.map_update_add])
    (fun c u w => by
      rw [append_pair_update₀ a (c • u) 0 w, append_pair_update₀ a u 0 w, g.map_update_smul])
    (fun u w₁ w₂ => by
      rw [append_pair_update₁ a u (w₁ + w₂) 0, append_pair_update₁ a u w₁ 0,
        append_pair_update₁ a u w₂ 0, g.map_update_add])
    (fun c u w => by
      rw [append_pair_update₁ a u (c • w) 0, append_pair_update₁ a u w 0, g.map_update_smul])

private lemma pairMap_apply {n : ℕ} (g : M [⋀^Fin (n + 2)]→ₗ[L] W) (a : Fin n → M) (u w : M) :
    pairMap g a u w = g (Fin.append a ![u, w]) := rfl

private lemma pairMap_self {n : ℕ} (g : M [⋀^Fin (n + 2)]→ₗ[L] W) (a : Fin n → M) (u : M) :
    pairMap g a u u = 0 :=
  g.map_eq_zero_of_eq _ (i := Fin.natAdd n 0) (j := Fin.natAdd n 1) (by simp)
    (by simp [Fin.ext_iff])

private lemma pairMap_left_eq_zero {n : ℕ} (g : M [⋀^Fin (n + 2)]→ₗ[L] W) (a : Fin n → M)
    (i : Fin n) (w : M) : pairMap g a (a i) w = 0 :=
  g.map_eq_zero_of_eq _ (i := Fin.castAdd 2 i) (j := Fin.natAdd n 0) (by simp)
    (by simp [Fin.ext_iff]; omega)

/-- **The determinant of a bilinear alternating map.** If `B` is alternating and vanishes on
`Z` in its first argument, then
`B(z₀ + a x + b y, z₁ + c x + e y) = (a e - b c) B(x, y)` for `z₀, z₁ ∈ Z`. -/
private lemma bilin_eq_det_smul (B : M →ₗ[L] M →ₗ[L] W) (hB : ∀ u, B u u = 0)
    (Z : Submodule L M) (hZ : ∀ z ∈ Z, ∀ w, B z w = 0) {x y z₀ z₁ : M} (hz₀ : z₀ ∈ Z)
    (hz₁ : z₁ ∈ Z) (a b c e : L) :
    B (z₀ + a • x + b • y) (z₁ + c • x + e • y) = (a * e - b * c) • B x y := by
  have anti : ∀ u w, B w u = -B u w := by
    intro u w
    have h := hB (u + w)
    simp only [map_add, LinearMap.add_apply, hB, zero_add, add_zero] at h
    exact eq_neg_of_add_eq_zero_left h
  have hZ' : ∀ z ∈ Z, ∀ w, B w z = 0 := fun z hz w => by rw [anti, hZ z hz, neg_zero]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hZ z₀ hz₀,
    hZ' z₁ hz₁, hB, anti x y, smul_zero, zero_add, add_zero, smul_neg]
  module

end Pair

/-- In a free module of rank two with basis `b`, `b₀ ∧ b₁` spans `⋀²`. -/
private lemma span_ιMulti_basis_two {R N : Type*} [CommRing R] [AddCommGroup N] [Module R N]
    (b : Module.Basis (Fin 2) R N) :
    Submodule.span R {exteriorPower.ιMulti R 2 b} = ⊤ := by
  rw [eq_top_iff, ← exteriorPower.ιMulti_span_of_span R 2 N b.span_eq, Submodule.span_le]
  rintro _ ⟨v, hv, rfl⟩
  obtain ⟨i₀, hi₀⟩ := hv (Set.mem_range_self 0)
  obtain ⟨i₁, hi₁⟩ := hv (Set.mem_range_self 1)
  have hv' : v = ![b i₀, b i₁] := by
    funext j
    fin_cases j
    · exact hi₀.symm
    · exact hi₁.symm
  subst hv'
  have hrep : ∀ i : Fin 2, exteriorPower.ιMulti R 2 ![b i, b i] = 0 := fun i =>
    (exteriorPower.ιMulti R 2).map_eq_zero_of_eq ![b i, b i] (i := 0) (j := 1) rfl (by decide)
  fin_cases i₀ <;> fin_cases i₁
  · simp only [SetLike.mem_coe]
    rw [hrep]
    exact zero_mem _
  · have : (![b 0, b 1] : Fin 2 → N) = b := by
      funext j; fin_cases j <;> rfl
    simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, SetLike.mem_coe]
    rw [this]
    exact Submodule.mem_span_singleton_self _
  · have : (![b 1, b 0] : Fin 2 → N) = b ∘ Equiv.swap 0 1 := by
      funext j; fin_cases j <;> rfl
    simp only [Fin.mk_one, Fin.isValue, Fin.zero_eta, SetLike.mem_coe]
    rw [this, AlternatingMap.map_swap _ _ (by decide)]
    exact neg_mem (Submodule.mem_span_singleton_self _)
  · simp only [SetLike.mem_coe]
    rw [hrep]
    exact zero_mem _

section Split

variable {k K R L : Type*} [Field k] [Field K] [CommRing R] [Field L] [Algebra k K]
  [Algebra k R] [Algebra K R] [IsScalarTower k K R] [Algebra R L] [Algebra k L] [Algebra K L]
  [IsScalarTower k R L] [IsScalarTower K R L] [IsScalarTower k K L]

/-- `Ω_{R/k} → Ω_{L/k} → Ω_{L/K}` is `Ω_{R/k} → Ω_{R/K} → Ω_{L/K}`. -/
private lemma map_map_eq_map_map (ω : Ω[R⁄k]) :
    KaehlerDifferential.map k K L L (KaehlerDifferential.map k k R L ω) =
      KaehlerDifferential.map K K R L (KaehlerDifferential.map k K R R ω) := by
  have hw : ω ∈ Submodule.span R (Set.range (KaehlerDifferential.D k R)) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨x, rfl⟩ := hw
    simp [KaehlerDifferential.map_D]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
  | smul a x _ hx =>
    have e1 : KaehlerDifferential.map k k R L (a • x) =
        algebraMap R L a • KaehlerDifferential.map k k R L x := by
      rw [map_smul, algebraMap_smul]
    have e2 : KaehlerDifferential.map k K R R (a • x) = a • KaehlerDifferential.map k K R R x :=
      map_smul _ _ _
    rw [e1, map_smul (KaehlerDifferential.map k K L L), e2,
        map_smul (KaehlerDifferential.map K K R L),
      hx, algebraMap_smul]

variable [IsFractionRing R L] [Nontrivial R]

/-- **The determinant comparison at a local ring.** Let `R` be a `K`-algebra over `k` with
`Ω_{R/K}` free of rank two, whose transitivity sequence has kernel spanned by the `dsᵢ` and in
which `ds ∧ ω` generates `⋀^{d+2} Ω_{R/k}` exactly when `ω̄` generates `⋀² Ω_{R/K}`. For
`η : Fin 2 → Ω_{L/k}` on the fraction field `L`, the forms `ds ∧ η` and `η̄` are the same
multiple `c` of the images of generators `σ_k`, `σ_K`. -/
private theorem exists_eq_smul_topFormsMap (d : ℕ) (s : Fin d → K)
    (hker : ∀ ζ : Ω[R⁄k], KaehlerDifferential.map k K R R ζ = 0 →
      ζ ∈ Submodule.span R (Set.range fun i => KaehlerDifferential.D k R (algebraMap K R (s i))))
    (hsurj : Function.Surjective (KaehlerDifferential.map k K R R))
    [Module.Free R Ω[R⁄K]] [Module.Finite R Ω[R⁄K]] (hrank : Module.finrank R Ω[R⁄K] = 2)
    (hcrit : ∀ ω : Fin 2 → Ω[R⁄k],
      Submodule.span R {(exteriorPower.ιMulti R (d + 2)
        (Fin.append (fun i => KaehlerDifferential.D k R (algebraMap K R (s i))) ω))} = ⊤ ↔
      Submodule.span R {(exteriorPower.ιMulti R 2
        (fun j => KaehlerDifferential.map k K R R (ω j)))} = ⊤)
    (η : Fin 2 → Ω[L⁄k]) :
    ∃ (σk : ⋀[R]^(d + 2) Ω[R⁄k]) (σK : ⋀[R]^2 Ω[R⁄K]), Submodule.span R {σk} = ⊤ ∧
      Submodule.span R {σK} = ⊤ ∧ ∃ c : L,
        exteriorPower.ιMulti L (d + 2)
            (Fin.append (fun i => KaehlerDifferential.D k L (algebraMap K L (s i))) η) =
          c • topFormsMap k R L (d + 2) σk ∧
        exteriorPower.ιMulti L 2 (fun j => KaehlerDifferential.map k K L L (η j)) =
          c • topFormsMap K R L 2 σK := by
  let bK := Module.finBasisOfFinrankEq R Ω[R⁄K] hrank
  choose ω hω using fun j => hsurj (bK j)
  have hωb : (fun j => KaehlerDifferential.map k K R R (ω j)) = bK := funext hω
  have hσK : Submodule.span R {(exteriorPower.ιMulti R 2
      (fun j => KaehlerDifferential.map k K R R (ω j)))} = ⊤ := by
    rw [hωb]
    exact span_ιMulti_basis_two bK
  have hσk := (hcrit ω).2 hσK
  refine ⟨_, _, hσk, hσK, ?_⟩
  set x := KaehlerDifferential.map k k R L (ω 0)
  set y := KaehlerDifferential.map k k R L (ω 1)
  set a : Fin d → Ω[L⁄k] := fun i => KaehlerDifferential.D k L (algebraMap K L (s i))
  let Z : Submodule L Ω[L⁄k] := Submodule.span L (Set.range a)
  -- every differential of `R` is a combination of the `dsᵢ` and the `ωⱼ`
  have hR : ∀ ζ : Ω[R⁄k], ζ ∈ Submodule.span R
      (Set.range fun i => KaehlerDifferential.D k R (algebraMap K R (s i))) ⊔
        Submodule.span R {ω 0, ω 1} := by
    intro ζ
    set r := bK.repr (KaehlerDifferential.map k K R R ζ)
    have hz : KaehlerDifferential.map k K R R (ζ - (r 0 • ω 0 + r 1 • ω 1)) = 0 := by
      rw [map_sub, map_add, map_smul, map_smul, hω, hω, sub_eq_zero]
      have := bK.sum_repr (KaehlerDifferential.map k K R R ζ)
      rw [Fin.sum_univ_two] at this
      exact this.symm
    have := hker _ hz
    rw [show ζ = (ζ - (r 0 • ω 0 + r 1 • ω 1)) + (r 0 • ω 0 + r 1 • ω 1) by abel]
    exact Submodule.add_mem_sup this (Submodule.mem_span_pair.2 ⟨_, _, rfl⟩)
  have hdec : ∀ ζ : Ω[L⁄k], ∃ z ∈ Z, ∃ a₀ b₀ : L, ζ = z + a₀ • x + b₀ • y := by
    have htop : (⊤ : Submodule L Ω[L⁄k]) ≤ Z ⊔ Submodule.span L {x, y} := by
      rw [← KaehlerDifferential.span_range_map_derivation_of_isLocalization k R L
        (nonZeroDivisors R), Submodule.span_le]
      rintro _ ⟨r, rfl⟩
      obtain ⟨z, hz, w, hw, hzw⟩ := Submodule.mem_sup.1 (hR (KaehlerDifferential.D k R r))
      rw [SetLike.mem_coe, Function.comp_apply, ← hzw, map_add]
      clear hzw
      refine add_mem (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right ?_)
      · induction hz using Submodule.span_induction with
        | mem z hz =>
          obtain ⟨i, rfl⟩ := hz
          rw [KaehlerDifferential.map_D, ← IsScalarTower.algebraMap_apply]
          exact Submodule.subset_span ⟨i, rfl⟩
        | zero => simp
        | add u v _ _ hu hv => simpa only [map_add] using add_mem hu hv
        | smul c u _ hu =>
          rw [map_smul, ← algebraMap_smul L c]
          exact Submodule.smul_mem _ _ hu
      · obtain ⟨p, q, rfl⟩ := Submodule.mem_span_pair.1 hw
        rw [map_add, map_smul, map_smul, ← algebraMap_smul L p, ← algebraMap_smul L q]
        exact Submodule.mem_span_pair.2 ⟨_, _, rfl⟩
    intro ζ
    obtain ⟨z, hz, w, hw, rfl⟩ := Submodule.mem_sup.1 (htop (Submodule.mem_top (x := ζ)))
    obtain ⟨p, q, rfl⟩ := Submodule.mem_span_pair.1 hw
    exact ⟨z, hz, p, q, by abel⟩
  obtain ⟨z₀, hz₀, a₀, b₀, h₀⟩ := hdec (η 0)
  obtain ⟨z₁, hz₁, a₁, b₁, h₁⟩ := hdec (η 1)
  have hη : η = ![η 0, η 1] := by funext j; fin_cases j <;> rfl
  refine ⟨a₀ * b₁ - b₀ * a₁, ?_, ?_⟩
  · -- the form over `k`
    let B := pairMap (exteriorPower.ιMulti L (d + 2) (M := Ω[L⁄k])) a
    have hZ : ∀ z ∈ Z, ∀ w, B z w = 0 := by
      intro z hz w
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨i, rfl⟩ := hz
        exact pairMap_left_eq_zero _ a i w
      | zero => simp
      | add u v _ _ hu hv => rw [map_add, LinearMap.add_apply, hu, hv, add_zero]
      | smul c u _ hu => rw [map_smul, LinearMap.smul_apply, hu, smul_zero]
    have e := bilin_eq_det_smul B (pairMap_self _ a) Z hZ (x := x) (y := y) hz₀ hz₁ a₀ b₀ a₁ b₁
    rw [← h₀, ← h₁, pairMap_apply, ← hη] at e
    rw [e, pairMap_apply, topFormsMap_ιMulti]
    congr 2
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [a, KaehlerDifferential.map_D, ← IsScalarTower.algebraMap_apply]
    · fin_cases j <;> simp [x, y, Fin.append_right]
  · -- the form over `K`
    let g : Ω[L⁄k] [⋀^Fin (0 + 2)]→ₗ[L] ⋀[L]^2 Ω[L⁄K] :=
      (exteriorPower.ιMulti L 2 (M := Ω[L⁄K])).compLinearMap
        (KaehlerDifferential.map k K L L)
    let B := pairMap g Fin.elim0
    have hB : ∀ u w, B u w = exteriorPower.ιMulti L 2
        ![KaehlerDifferential.map k K L L u, KaehlerDifferential.map k K L L w] := by
      intro u w
      change exteriorPower.ιMulti L 2 _ = _
      congr 1
      funext j
      fin_cases j <;> rfl
    have hZ : ∀ z ∈ Z, ∀ w, B z w = 0 := by
      intro z hz w
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨i, rfl⟩ := hz
        rw [hB]
        have h0 : KaehlerDifferential.map k K L L (a i) = 0 := by
          simp only [a, KaehlerDifferential.map_D]
          exact Derivation.map_algebraMap _ _
        rw [h0]
        exact (exteriorPower.ιMulti L 2).map_coord_zero 0 rfl
      | zero => simp
      | add u v _ _ hu hv => rw [map_add, LinearMap.add_apply, hu, hv, add_zero]
      | smul c u _ hu => rw [map_smul, LinearMap.smul_apply, hu, smul_zero]
    have hself : ∀ u, B u u = 0 := fun u => by
      rw [hB]
      exact (exteriorPower.ιMulti L 2).map_eq_zero_of_eq _ (i := 0) (j := 1) rfl (by decide)
    have e := bilin_eq_det_smul B hself Z hZ (x := x) (y := y) hz₀ hz₁ a₀ b₀ a₁ b₁
    rw [← h₀, ← h₁, hB, hB] at e
    rw [show (fun j => KaehlerDifferential.map k K L L (η j)) =
      ![KaehlerDifferential.map k K L L (η 0), KaehlerDifferential.map k K L L (η 1)] by
        funext j; fin_cases j <;> rfl, e, topFormsMap_ιMulti]
    congr 2
    funext j
    fin_cases j
    · exact map_map_eq_map_map (ω 0)
    · exact map_map_eq_map_map (ω 1)

end Split

section Order

/-- A generator of `Ω^n_{R/A}` gives one of `Ω^n_{R'/A}` along a bijection `R → R'`. -/
private lemma span_topFormsMap_of_bijective {A R R' : Type*} [CommRing A] [CommRing R]
    [CommRing R'] [Algebra A R] [Algebra A R'] [Algebra R R'] [IsScalarTower A R R']
    (hbij : Function.Bijective (algebraMap R R')) {n : ℕ} {σ : ⋀[R]^n Ω[R⁄A]}
    (hσ : Submodule.span R {σ} = ⊤) :
    Submodule.span R' {topFormsMap A R R' n σ} = ⊤ := by
  letI : IsLocalization (⊥ : Submonoid R) R' := by
    let e : R ≃ₐ[R] R' := AlgEquiv.ofBijective (Algebra.ofId R R') hbij
    exact (IsLocalization.isLocalization_iff_of_algEquiv (⊥ : Submonoid R) e).mp
      (IsLocalization.self (R := R) (M := ⊥) (fun x hx => by
        rw [Submonoid.mem_bot.mp hx]; exact isUnit_one))
  exact span_singleton_topFormsMap (⊥ : Submonoid R) hσ

private lemma eq_inv_mul_smul_of_smul_eq {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    {c c' : F} {x y w : V} (hc0 : c ≠ 0) (hc : c • x = y) (h : y = c' • w) :
    x = (c⁻¹ * c') • w := by
  rw [mul_smul, ← h, ← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]

private lemma inv_smul_eq_mul_smul {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    {c c' : F} {y w : V} (h : y = c' • w) : c⁻¹ • y = (c⁻¹ * c') • w := by
  rw [mul_smul, h]

/-- A nonzero exterior power `⋀ⁿ M` contains a nonzero pure wedge `v₁ ∧ ⋯ ∧ vₙ`. -/
private lemma exists_ιMulti_ne_zero {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {n : ℕ} {w : ⋀[R]^n M} (hw : w ≠ 0) : ∃ v : Fin n → M, exteriorPower.ιMulti R n v ≠ 0 := by
  by_contra h
  push Not at h
  have hw' : w ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R n (M := M))) := by
    rw [exteriorPower.ιMulti_span]; trivial
  rw [Submodule.span_eq_bot.2 (by rintro _ ⟨v, rfl⟩; exact h v)] at hw'
  exact hw ((Submodule.mem_bot R).1 hw')

/-- A nonzero vector of a line with a basis spans it. -/
private lemma span_singleton_eq_top_of_basis_unit {F V : Type*} [DivisionRing F]
    [AddCommGroup V] [Module F V] (b : Module.Basis Unit F V) {v : V} (hv : v ≠ 0) :
    Submodule.span F {v} = ⊤ :=
  (finrank_eq_one_iff_of_nonzero v hv).1 (by simpa using Module.finrank_eq_card_basis b)

/-- **Orders along one local ring over two bases.** If bases `b` of `Ω^n_{L/k}` and `b'` of
`Ω^{n'}_{L/K}` are the same multiple `c` of the images of generators of `Ω^n_{R/k}` and
`Ω^{n'}_{R/K}`, then forms with the same coordinates along `b^{⊗m}` and `b'^{⊗m}` have the same
order along `R`. -/
private theorem ordAt_eq_ordAt_of_basis_eq_smul {k K R L : Type*} [CommRing k] [CommRing K]
    [CommRing R] [Field L] [Algebra k R] [Algebra k L] [Algebra R L] [IsScalarTower k R L]
    [Algebra K R] [Algebra K L] [IsScalarTower K R L] [IsFractionRing R L] {n n' : ℕ}
    {v : L → ℤ} (hmul : ∀ x y : L, x ≠ 0 → y ≠ 0 → v (x * y) = v x + v y)
    (hunit : ∀ a : R, IsUnit a → v (algebraMap R L a) = 0)
    {σ : ⋀[R]^n Ω[R⁄k]} (hσ : Submodule.span R {σ} = ⊤)
    {σ' : ⋀[R]^n' Ω[R⁄K]} (hσ' : Submodule.span R {σ'} = ⊤)
    (b : Module.Basis Unit L (⋀[L]^n Ω[L⁄k])) (b' : Module.Basis Unit L (⋀[L]^n' Ω[L⁄K]))
    (c : L) (hb : b () = c • topFormsMap k R L n σ) (hb' : b' () = c • topFormsMap K R L n' σ')
    (m : ℤ) (τ : PluriForms k L n m) (τ' : PluriForms K L n' m)
    (h : (ZTensorPower.basis b m).repr τ () = (ZTensorPower.basis b' m).repr τ' ()) :
    ordAt R v τ = ordAt R v τ' := by
  have hc : c ≠ 0 := by
    rintro rfl
    exact b.ne_zero () (by rw [hb, zero_smul])
  have h0 : topFormsMap k R L n σ ≠ 0 := by
    intro h0
    exact b.ne_zero () (by rw [hb, h0, smul_zero])
  have h0' : topFormsMap K R L n' σ' ≠ 0 := by
    intro h0
    exact b'.ne_zero () (by rw [hb', h0, smul_zero])
  have hb2 : topFormsBasis R hσ h0 () = c⁻¹ • b () := by
    rw [topFormsBasis_apply, hb, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hb2' : topFormsBasis R hσ' h0' () = c⁻¹ • b' () := by
    rw [topFormsBasis_apply, hb', smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [ordAt_eq hmul hunit hσ h0, ordAt_eq hmul hunit hσ' h0', formCoeff, formCoeff,
    ZTensorPower.basis_repr_of_eq_smul hb2, ZTensorPower.basis_repr_of_eq_smul hb2', h]

end Order

/-- **The determinant comparison along an isomorphism of local rings.** Let `Y` be a normal
variety of dimension `d + 2` over `k` (characteristic zero), `t₁, …, t_d ∈ 𝒪(Y)` algebraically
independent, `Γ` a prime divisor of `Y`, and `φ : 𝒪_{Y,Γ} ≅ R'` an isomorphism onto a
`K = k(t)`-algebra `R'` essentially of finite type, compatible with `k` and sending `tᵢ` to
`tᵢ ∈ K`. Then for `η : Fin 2 → Ω_{L/k}` on the fraction field `L` of `R'`, `dt ∧ η` and `η̄`
are the same multiple of the images of generators of `Ω^{d+2}_{R'/k}` and `Ω²_{R'/K}`
(`MMP.Mori.PrimeDivisor.exact_mapBaseChange_map_localRing`). -/
private theorem exists_eq_smul_topFormsMap_of_ringEquiv
    {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k))
    (hY : IsNormalVariety k sY) {d : ℕ} (hn : topologicalKrullDim Y = (d + 2 : ℕ))
    (t : Fin d → Γ(Y, ⊤)) (ht : letI := sectionAlgebra sY ⊤; AlgebraicIndependent k t)
    (Γ : MMP.Mori.PrimeDivisor Y)
    (K : Type u) [Field K] [Algebra k K] [Algebra (MvPolynomial (Fin d) k) K]
    [IsScalarTower k (MvPolynomial (Fin d) k) K] [IsFractionRing (MvPolynomial (Fin d) k) K]
    (R' : Type u) [CommRing R'] [Algebra k R'] [Algebra K R'] [IsScalarTower k K R']
    [Algebra.EssFiniteType K R'] (φ : Γ.localRing ≃+* R')
    (hφk : letI := MMP.Mori.stalkAlgebra sY Γ.genericPoint;
      ∀ c : k, φ (algebraMap k Γ.localRing c) = algebraMap k R' c)
    (hφt : ∀ i, φ (Y.presheaf.germ ⊤ Γ.genericPoint trivial (t i)) =
      algebraMap K R' (algebraMap (MvPolynomial (Fin d) k) K (.X i)))
    (L : Type u) [Field L] [Algebra R' L] [Algebra k L] [Algebra K L] [IsScalarTower k R' L]
    [IsScalarTower K R' L] [IsScalarTower k K L] [IsFractionRing R' L]
    (η : Fin 2 → Ω[L⁄k]) :
    ∃ (σk : ⋀[R']^(d + 2) Ω[R'⁄k]) (σK : ⋀[R']^2 Ω[R'⁄K]), Submodule.span R' {σk} = ⊤ ∧
      Submodule.span R' {σK} = ⊤ ∧ ∃ c : L,
        exteriorPower.ιMulti L (d + 2) (Fin.append (fun i => KaehlerDifferential.D k L
          (algebraMap K L (algebraMap (MvPolynomial (Fin d) k) K (.X i)))) η) =
          c • topFormsMap k R' L (d + 2) σk ∧
        exteriorPower.ιMulti L 2 (fun j => KaehlerDifferential.map k K L L (η j)) =
          c • topFormsMap K R' L 2 σK := by
  letI := MMP.Mori.stalkAlgebra sY Γ.genericPoint
  letI : Algebra K Γ.localRing := ((φ.symm : R' →+* Γ.localRing).comp (algebraMap K R')).toAlgebra
  have hφK : ∀ c : K, φ (algebraMap K Γ.localRing c) = algebraMap K R' c := fun c =>
    φ.apply_symm_apply _
  have hT : IsScalarTower k K Γ.localRing := by
    refine IsScalarTower.of_algebraMap_eq fun c => φ.injective ?_
    rw [hφk, hφK, ← IsScalarTower.algebraMap_apply]
  have hK : ∀ i, algebraMap K Γ.localRing (algebraMap (MvPolynomial (Fin d) k) K (.X i)) =
      Y.presheaf.germ ⊤ Γ.genericPoint trivial (t i) := fun i =>
    φ.injective (by rw [hφK, hφt])
  letI eK : Γ.localRing ≃ₐ[K] R' := { φ with commutes' := hφK }
  have hft : Algebra.EssFiniteType K Γ.localRing :=
    (Algebra.EssFiniteType.iff_of_algEquiv eK.symm).mp inferInstance
  obtain ⟨-, hexact, hsurj, ⟨b, hb⟩, -, ⟨hfree, hfin, hrank⟩, hcrit⟩ :=
    MMP.Mori.PrimeDivisor.exact_mapBaseChange_map_localRing sY hY hn t ht Γ K hT hK hft
  have h2 : d + 2 - d = 2 := Nat.add_sub_cancel_left d 2
  rw [h2] at hrank hcrit
  simp only [← hK] at hcrit
  have hker : ∀ ζ : Ω[Γ.localRing⁄k], KaehlerDifferential.map k K Γ.localRing Γ.localRing ζ = 0 →
      ζ ∈ Submodule.span Γ.localRing (Set.range fun i => KaehlerDifferential.D k Γ.localRing
        (algebraMap K Γ.localRing (algebraMap (MvPolynomial (Fin d) k) K (.X i)))) := by
    intro ζ hζ
    obtain ⟨y, rfl⟩ := (hexact ζ).1 hζ
    rw [← b.sum_repr y, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smul, hb, KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  letI : Algebra Γ.localRing L := ((algebraMap R' L).comp φ.toRingHom).toAlgebra
  have hT1 : IsScalarTower k Γ.localRing L := IsScalarTower.of_algebraMap_eq fun c => by
    change _ = algebraMap R' L (φ (algebraMap k Γ.localRing c))
    rw [hφk, ← IsScalarTower.algebraMap_apply]
  have hT2 : IsScalarTower K Γ.localRing L := IsScalarTower.of_algebraMap_eq fun c => by
    change _ = algebraMap R' L (φ (algebraMap K Γ.localRing c))
    rw [hφK, ← IsScalarTower.algebraMap_apply]
  have hfr : IsFractionRing Γ.localRing L :=
    (IsFractionRing.isFractionRing_iff_of_base_ringEquiv L φ.symm).1 ‹_›
  obtain ⟨σk, σK, hσk, hσK, c, h1, h3⟩ := exists_eq_smul_topFormsMap d
    (fun i => algebraMap (MvPolynomial (Fin d) k) K (.X i)) hker hsurj hrank hcrit η
  letI : Algebra Γ.localRing R' := φ.toRingHom.toAlgebra
  have hT3 : IsScalarTower k Γ.localRing R' := IsScalarTower.of_algebraMap_eq fun c => (hφk c).symm
  have hT4 : IsScalarTower K Γ.localRing R' := IsScalarTower.of_algebraMap_eq fun c => (hφK c).symm
  have hT5 : IsScalarTower Γ.localRing R' L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  refine ⟨topFormsMap k Γ.localRing R' (d + 2) σk, topFormsMap K Γ.localRing R' 2 σK,
    span_topFormsMap_of_bijective φ.bijective hσk, span_topFormsMap_of_bijective φ.bijective hσK,
    c, ?_, ?_⟩
  · rwa [MMP.Threefold.Mori.Helpers.topFormsMap_comp]
  · rwa [MMP.Threefold.Mori.Helpers.topFormsMap_comp]

end Determinant

/-! ### Local rings of the generic surface -/

section LocalRings

open MMP.Mori (stalkAlgebra functionFieldAlgebra)

/-- A germ of a global section, pushed through `stalkSpecializes ≫ stalkMap`. -/
private lemma stalkSpecializes_stalkMap_germ_top {S' Y' : Scheme.{u}} (f : S' ⟶ Y') (q : S')
    {y : Y'} (h : f q ⤳ y) (a : Γ(Y', ⊤)) :
    (Y'.presheaf.stalkSpecializes h ≫ f.stalkMap q).hom (Y'.presheaf.germ ⊤ y trivial a) =
      S'.presheaf.germ ⊤ q trivial (f.appTop.hom a) := by
  rw [← CommRingCat.comp_apply, ← Category.assoc]
  erw [TopCat.Presheaf.germ_stalkSpecializes]
  rw [Scheme.Hom.germ_stalkMap]
  rfl

/-- The local rings of a scheme locally of finite type over a field `k` are essentially of
finite type over `k`. -/
private theorem essFiniteType_stalkAlgebra {k : Type u} [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] (y : Y) :
    letI := stalkAlgebra sY y
    Algebra.EssFiniteType k (Y.presheaf.stalk y) := by
  letI := stalkAlgebra sY y
  have := (sY.base y).isPrime
  have h0 : (algebraMap k (Localization.AtPrime (sY.base y).asIdeal)).EssFiniteType := by
    rw [RingHom.essFiniteType_algebraMap]
    exact Algebra.EssFiniteType.of_isLocalization _ (sY.base y).asIdeal.primeCompl
  have hiso : (Spec.stalkIso (.of k) (sY.base y)).inv.hom.EssFiniteType :=
    (RingHom.FiniteType.of_surjective _
      (asIso (Spec.stalkIso (.of k) (sY.base y)).inv).commRingCatIsoToRingEquiv.surjective
      ).essFiniteType
  have h1 : ((Scheme.ΓSpecIso (.of k)).inv ≫
      (Spec (.of k)).presheaf.germ ⊤ (sY.base y) (by simp)).hom.EssFiniteType := by
    have e := congrArg CommRingCat.Hom.hom
      (Spec.algebraMap_stalkIso_inv (R := .of k) (x := sY.base y))
    rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom] at e
    rw [← e]
    exact h0.comp hiso
  have h2 := h1.comp (LocallyOfFiniteType.stalkMap sY y)
  rw [← RingHom.essFiniteType_algebraMap]
  convert h2 using 1
  change ((Scheme.ΓSpecIso (.of k)).inv ≫ sY.appTop ≫ Y.presheaf.germ ⊤ y (by simp)).hom = _
  rw [← CommRingCat.hom_comp, Category.assoc, Scheme.Hom.germ_stalkMap]
  rfl

/-- The `k`- and `K`-algebra structures of a local ring of a `K`-scheme over `k` form a tower. -/
private lemma isScalarTower_stalkAlgebra_comp {k K : Type u} [Field k] [Field K] [Algebra k K]
    {S' : Scheme.{u}} (sS : S' ⟶ Spec (.of K)) (f : S' ⟶ Spec (.of k))
    (hf : f = sS ≫ Spec.map (CommRingCat.ofHom (algebraMap k K))) (q : S') :
    letI := stalkAlgebra f q
    letI := stalkAlgebra sS q
    IsScalarTower k K (S'.presheaf.stalk q) := by
  letI := stalkAlgebra f q
  letI := stalkAlgebra sS q
  refine IsScalarTower.of_algebraMap_eq' ?_
  have : (Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ S'.presheaf.germ ⊤ q trivial =
      CommRingCat.ofHom (algebraMap k K) ≫ (Scheme.ΓSpecIso (.of K)).inv ≫
        sS.appTop ≫ S'.presheaf.germ ⊤ q trivial := by
    subst hf
    rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Category.assoc,
      ← Scheme.ΓSpecIso_inv_naturality, Category.assoc, Category.assoc]
  exact congrArg CommRingCat.Hom.hom this

private lemma appLE_top_top {X' Y' : Scheme.{u}} (f : X' ⟶ Y') (h) : f.appLE ⊤ ⊤ h = f.appTop := by
  rw [Scheme.Hom.appLE, show (homOfLE h).op = 𝟙 _ from rfl]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

/-- The structure morphism of `Spec Γ(X, U)` over `k`. -/
private lemma fromSpec_comp_eq {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    {U : X.Opens} (hU : IsAffineOpen U) :
    letI := sectionAlgebra sX U
    hU.fromSpec ≫ sX = Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, U))) := by
  letI := sectionAlgebra sX U
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec sX (isAffineOpen_top _) hU (by simp),
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  rfl

end LocalRings

/-! ### The determinant comparison on the generic surface -/

section PerDivisor

open MMP.Mori (stalkAlgebra functionFieldAlgebra topFormsMap)
open KaehlerDifferential

/-- **The determinant comparison at a prime divisor of the generic surface.** At a prime divisor
`P` of `S = Spec Γ(X, U)[M⁻¹]`, whose local ring is that of `Spec Γ(X, U)` at the image of `η_P`,
the forms `dt ∧ η` (over `k`) and `η̄` (over `K = k(t)`) on `K(S)` are the same multiple of the
images of generators of `Ω^{d+2}_{𝒪_{S,P}/k}` and `Ω²_{𝒪_{S,P}/K}`. -/
private theorem exists_eq_smul_topFormsMap_genSurface
    {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] (hXv : IsNormalVariety k sX)
    {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U] {d : ℕ} (t : Fin d → Γ(X, U))
    (ht : letI := sectionAlgebra sX U; AlgebraicIndependent k t)
    [IsIntegral (Spec (genRing sX t))]
    (hdimX : topologicalKrullDim X = (d + 2 : ℕ))
    (P : MMP.Mori.PrimeDivisor (Spec (genRing sX t)))
    [Algebra k P.localRing] [Algebra (genField k d) P.localRing]
    [IsScalarTower k (genField k d) P.localRing]
    [Algebra.EssFiniteType (genField k d) P.localRing]
    [Algebra k (Spec (genRing sX t)).functionField]
    [Algebra (genField k d) (Spec (genRing sX t)).functionField]
    [IsScalarTower k (genField k d) (Spec (genRing sX t)).functionField]
    [IsScalarTower k P.localRing (Spec (genRing sX t)).functionField]
    [IsScalarTower (genField k d) P.localRing (Spec (genRing sX t)).functionField]
    (hkR : ∀ c : k, algebraMap k P.localRing c =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ ((genι sX t hU ≫ U.ι) ≫ sX).appTop ≫
        (Spec (genRing sX t)).presheaf.germ ⊤ P.genericPoint trivial).hom c)
    (hKR : ∀ c : genField k d, algebraMap (genField k d) P.localRing c =
      ((Scheme.ΓSpecIso (.of (genField k d))).inv ≫ (genStructure sX t).appTop ≫
        (Spec (genRing sX t)).presheaf.germ ⊤ P.genericPoint trivial).hom c) :
    ∀ η : Fin 2 → Ω[(Spec (genRing sX t)).functionField⁄k],
      ∃ (σk : ⋀[P.localRing]^(d + 2) Ω[P.localRing⁄k])
        (σK : ⋀[P.localRing]^2 Ω[P.localRing⁄genField k d]),
        Submodule.span P.localRing {σk} = ⊤ ∧ Submodule.span P.localRing {σK} = ⊤ ∧
        ∃ c : (Spec (genRing sX t)).functionField,
          exteriorPower.ιMulti _ (d + 2) (Fin.append (fun i => KaehlerDifferential.D k _
            (algebraMap (genField k d) (Spec (genRing sX t)).functionField
              (algebraMap (MvPolynomial (Fin d) k) (genField k d) (.X i)))) η) =
            c • topFormsMap k P.localRing (Spec (genRing sX t)).functionField (d + 2) σk ∧
          exteriorPower.ιMulti _ 2 (fun j => KaehlerDifferential.map k (genField k d) _ _ (η j)) =
            c • topFormsMap (genField k d) P.localRing
                (Spec (genRing sX t)).functionField 2 σK := by
  intro η
  letI := sectionAlgebra sX U
  haveI : LocallyOfFiniteType sX := hXv.1.toLocallyOfFiniteType
  haveI : IsDomain Γ(X, U) := IsIntegral.component_integral U
  set sY : Spec Γ(X, U) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, U)))
    with hsY_def
  set ι₀ : Spec (genRing sX t) ⟶ Spec Γ(X, U) :=
    Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization (genSubmonoid sX t))))
    with hι₀
  have hsY : hU.fromSpec ≫ sX = sY := fromSpec_comp_eq sX hU
  have hfs : (genι sX t hU ≫ U.ι) ≫ sX = ι₀ ≫ sY := by
    rw [← hsY, ← hU.isoSpec_inv_ι]
    show ((ι₀ ≫ hU.isoSpec.inv) ≫ U.ι) ≫ sX = ι₀ ≫ (hU.isoSpec.inv ≫ U.ι) ≫ sX
    simp only [Category.assoc]
  have hYn : IsNormalVariety k sY := by
    haveI : IsNormal (Spec Γ(X, U)) :=
      isNormal_of_isIso_stalkMap hU.isoSpec.inv (fun _ => inferInstance)
    haveI : IsSeparated sX := hXv.1.toIsSeparated
    haveI : QuasiCompact sX := hXv.1.toQuasiCompact
    rw [← hsY]
    exact ⟨@IsVariety.mk _ _ _ _ inferInstance inferInstance inferInstance inferInstance,
      inferInstance⟩
  have hdimY : topologicalKrullDim (Spec Γ(X, U)) = (d + 2 : ℕ) := by
    rw [← IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso hU.isoSpec).isHomeomorph,
      topologicalKrullDim_opens_eq hXv U, hdimX]
  letI := sectionAlgebra sY ⊤
  let e : Γ(X, U) →ₐ[k] Γ(Spec Γ(X, U), ⊤) :=
    { (Scheme.ΓSpecIso Γ(X, U)).inv.hom with
      commutes' := fun c => by
        change _ = ((Scheme.ΓSpecIso (.of k)).inv ≫ sY.appLE ⊤ ⊤ _).hom c
        rw [appLE_top_top, ← Scheme.ΓSpecIso_inv_naturality]
        rfl }
  have hte : AlgebraicIndependent k (e ∘ t) :=
    ht.map' (f := e) (asIso (Scheme.ΓSpecIso Γ(X, U)).inv).commRingCatIsoToRingEquiv.injective
  have hstalk : IsIso (ι₀.stalkMap P.genericPoint) :=
    isIso_SpecMap_stakMap_localization Γ(X, U) (genSubmonoid sX t) P.genericPoint
  have hcoh : Order.coheight (ι₀ P.genericPoint) = 1 := by
    rw [coheight_eq_of_isIso_stalkMap ι₀ P.genericPoint hstalk]
    exact PrimeDivisor.coheight_genericPoint P
  let ΓY : MMP.Mori.PrimeDivisor (Spec Γ(X, U)) := PrimeDivisor.ofCoheightOne _ hcoh
  have hΓY : ΓY.genericPoint = ι₀ P.genericPoint := PrimeDivisor.genericPoint_ofCoheightOne _ _
  have hsp : ι₀ P.genericPoint ⤳ ΓY.genericPoint := by rw [hΓY]
  have hiso1 : IsIso ((Spec Γ(X, U)).presheaf.stalkSpecializes hsp) := by
    rw [show (Spec Γ(X, U)).presheaf.stalkSpecializes hsp =
      ((Spec Γ(X, U)).presheaf.stalkCongr (Inseparable.of_eq hΓY.symm)).inv from rfl]
    infer_instance
  let φh := (Spec Γ(X, U)).presheaf.stalkSpecializes hsp ≫ ι₀.stalkMap P.genericPoint
  haveI : IsIso φh := inferInstance
  let φ : ΓY.localRing ≃+* P.localRing := (asIso φh).commRingCatIsoToRingEquiv
  have hφapp : ∀ a, φ ((Spec Γ(X, U)).presheaf.germ ⊤ ΓY.genericPoint trivial a) =
      (Spec (genRing sX t)).presheaf.germ ⊤ P.genericPoint trivial (ι₀.appTop.hom a) :=
    fun a => stalkSpecializes_stalkMap_germ_top ι₀ P.genericPoint hsp a
  have hφk : letI := stalkAlgebra sY ΓY.genericPoint;
      ∀ c : k, φ (algebraMap k ΓY.localRing c) = algebraMap k P.localRing c := by
    intro c
    rw [hkR]
    change φ ((Spec Γ(X, U)).presheaf.germ ⊤ _ trivial
        (sY.appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom c))) =
      (Spec (genRing sX t)).presheaf.germ ⊤ P.genericPoint trivial
        (((genι sX t hU ≫ U.ι) ≫ sX).appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom c))
    rw [hφapp, hfs, Scheme.Hom.comp_appTop]
    rfl
  have hφt : ∀ i, φ ((Spec Γ(X, U)).presheaf.germ ⊤ ΓY.genericPoint trivial (e (t i))) =
      algebraMap (genField k d) P.localRing
        (algebraMap (MvPolynomial (Fin d) k) (genField k d) (.X i)) := by
    intro i
    rw [hφapp, hKR]
    change _ = (Spec (genRing sX t)).presheaf.germ ⊤ P.genericPoint trivial
      ((genStructure sX t).appTop.hom ((Scheme.ΓSpecIso (.of (genField k d))).inv.hom
        (algebraMap (MvPolynomial (Fin d) k) (genField k d) (.X i))))
    congr 1
    have h1 : ι₀.appTop.hom ((Scheme.ΓSpecIso Γ(X, U)).inv.hom (t i)) =
        (Scheme.ΓSpecIso (genRing sX t)).inv.hom
          (algebraMap Γ(X, U) (Localization (genSubmonoid sX t)) (t i)) := by
      rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]
      rfl
    have h2 : (genStructure sX t).appTop.hom ((Scheme.ΓSpecIso (.of (genField k d))).inv.hom
        (algebraMap (MvPolynomial (Fin d) k) (genField k d) (.X i))) =
        (Scheme.ΓSpecIso (genRing sX t)).inv.hom (fracToLoc k t
          (algebraMap (MvPolynomial (Fin d) k) (genField k d) (.X i))) := by
      rw [← CommRingCat.comp_apply, genStructure, ← Scheme.ΓSpecIso_inv_naturality]
      rfl
    rw [show e (t i) = (Scheme.ΓSpecIso Γ(X, U)).inv.hom (t i) from rfl, h1, h2,
      fracToLoc_algebraMap, MvPolynomial.aeval_X]
    rfl
  exact exists_eq_smul_topFormsMap_of_ringEquiv sY hYn hdimY (e ∘ t) hte ΓY (genField k d)
    P.localRing φ hφk hφt _ η

end PerDivisor

/-! ### Divisors of the function field from essentially finite type valuation rings -/

section Spreading

open MMP.Mori (functionFieldAlgebra IsBirationalMorphism)
open scoped WithZero

/-- Two `ℤᵐ⁰`-valued valuations of a field with the same valuation ring, both taking the value
`exp (-1)`, coincide. -/
private lemma valuation_eq_of_le_one_iff {L : Type*} [Field L] (v w : Valuation L ℤᵐ⁰)
    (h : ∀ g, v g ≤ 1 ↔ w g ≤ 1) (hv : ∃ π, v π = WithZero.exp (-1))
    (hw : ∃ π, w π = WithZero.exp (-1)) : v = w := by
  have he : v.IsEquiv w := Valuation.isEquiv_iff_val_le_one.2 (h _)
  obtain ⟨π, hπ⟩ := hv
  obtain ⟨π', hπ'⟩ := hw
  have hπ0 : π ≠ 0 := fun h0 => by
    simpa [h0] using hπ.symm
  have hπ'0 : π' ≠ 0 := fun h0 => by
    simpa [h0] using hπ'.symm
  have hexp : ∀ a n : ℤ, WithZero.exp a ^ n = WithZero.exp (n * a) := fun a n => by
    rw [← WithZero.exp_zsmul, smul_eq_mul]
  set b := WithZero.log (w π) with hb
  set c := WithZero.log (v π') with hc
  have hwπ : w π = WithZero.exp b := (WithZero.exp_log ((w.ne_zero_iff).2 hπ0)).symm
  have hvπ' : v π' = WithZero.exp c := (WithZero.exp_log ((v.ne_zero_iff).2 hπ'0)).symm
  have hlt : ∀ x, v x < 1 ↔ w x < 1 := fun x => by
    simpa using (Valuation.IsEquiv.lt_iff_lt he (x := x) (y := 1))
  have hb0 : b < 0 := by
    have : w π < 1 := (hlt π).1 (by rw [hπ]; exact WithZero.exp_lt_exp.2 (by norm_num))
    rwa [hwπ, ← WithZero.exp_zero, WithZero.exp_lt_exp] at this
  have hc0 : c < 0 := by
    have : v π' < 1 := (hlt π').2 (by rw [hπ']; exact WithZero.exp_lt_exp.2 (by norm_num))
    rwa [hvπ', ← WithZero.exp_zero, WithZero.exp_lt_exp] at this
  have hbc : b * c = 1 := by
    have e1 : v π' = v (π ^ (-c)) := by
      rw [map_zpow₀, hπ, hexp, hvπ']
      congr 1
      ring
    have e2 := (he.eq_iff).1 e1
    rw [hπ', map_zpow₀, hwπ, hexp, WithZero.exp_inj] at e2
    linarith
  have hb1 : b = -1 := (Int.eq_one_or_neg_one_of_mul_eq_one hbc).resolve_left (by omega)
  ext g
  by_cases hg : g = 0
  · simp [hg]
  set a := WithZero.log (v g)
  have hvg : v g = WithZero.exp a := (WithZero.exp_log ((v.ne_zero_iff).2 hg)).symm
  have e1 : v g = v (π ^ (-a)) := by
    rw [map_zpow₀, hπ, hexp, hvg]
    congr 1
    ring
  have e2 := (he.eq_iff).1 e1
  rw [e2, map_zpow₀, hwπ, hb1, hexp, hvg]
  congr 1
  ring

/-- An algebra essentially of finite type over `k` is a localization of a finitely generated
subalgebra at elements which become units. -/
private lemma exists_finset_mul_isUnit_eq (k O : Type*) [Field k] [CommRing O] [Algebra k O]
    [h : Algebra.EssFiniteType k O] :
    ∃ s : Finset O, ∀ o : O, ∃ a ∈ Algebra.adjoin k (s : Set O),
      ∃ u ∈ Algebra.adjoin k (s : Set O), IsUnit u ∧ o * u = a := by
  obtain ⟨s, hs⟩ := h.cond
  refine ⟨s, fun o => ?_⟩
  obtain ⟨⟨a, u⟩, hau⟩ := IsLocalization.surj
    ((IsUnit.submonoid O).comap (algebraMap (Algebra.adjoin k (s : Set O)) O)) o
  exact ⟨a, a.2, u, u.1.2, u.2, hau⟩

/-- A morphism of integral schemes, locally of finite type and birational in the sense of
`AlgebraicGeometry.IsBirational`, is a birational morphism. -/
private theorem isBirationalMorphism_of_isBirational' {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : IsBirational f) :
    IsBirationalMorphism f := by
  haveI : Finite (irreducibleComponents X) := by
    rw [irreducibleComponents_eq_singleton]
    exact Set.finite_singleton _
  haveI : Finite (irreducibleComponents Y) := by
    rw [irreducibleComponents_eq_singleton]
    exact Set.finite_singleton _
  obtain ⟨U, V, hUV, hU, hV, hiso⟩ :=
    exists_dense_opens_isIso_resLE_of_isBirational f hf (Or.inl ⟨inferInstance, inferInstance⟩)
  exact MMP.Flips.isBirationalMorphism_of_isIso_resLE f U V hU.nonempty hV.nonempty hUV hiso

/-- **The normalization step.** The normalization of a variety is a finite, hence projective,
birational morphism from a normal variety, and it is an isomorphism on local rings over a point
whose local ring is a valuation ring. -/
private theorem exists_normalization_isIso_stalkMap' {k : Type u} [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k sY] (q : Y)
    [ValuationRing (Y.presheaf.stalk q)] :
    ∃ (Z : Scheme.{u}) (ν : Z ⟶ Y), IsNormalVariety k (ν ≫ sY) ∧
      IsBirationalMorphism ν ∧ ∃ z : Z, ν z = q ∧ IsIso (ν.stalkMap z) := by
  let ν := normalizationOverField k sY
  have hX := finite_irreducibleComponents_of_locallyOfFiniteType k sY
  have hbir : IsBirational ν := Scheme.isBirational_normalization Y hX
  haveI : IsFinite ν := isFinite_normalizationOverField k sY
  haveI hvar : AlgebraicGeometry.IsVariety k (ν ≫ sY) := isVariety_normalizationOverField k sY
  haveI : IsIntegral (normalizationSchemeOverField k sY) := hvar.toIsIntegral
  have hνb : IsBirationalMorphism ν := isBirationalMorphism_of_isBirational' ν hbir
  haveI : IsDominant ν := hνb.isDominant
  obtain ⟨z, hz⟩ := (Scheme.surjective_normalization Y hX).surj q
  refine ⟨_, ν, ⟨hvar, Scheme.isNormal_normalizationScheme Y hX⟩, hνb, z, hz, ?_⟩
  subst hz
  exact MMP.Positivity.isIso_stalkMap_of_valuationRing ν hνb.functionFieldMap_bijective z

/-- The ideal `{c ∈ C | v c < 1}` of a subalgebra `C` on which `v ≤ 1`. -/
private def valuationLtOneIdeal {k K : Type*} [CommRing k] [Field K] [Algebra k K]
    (v : Valuation K ℤᵐ⁰) (C : Subalgebra k K) (hC : ∀ c ∈ C, v c ≤ 1) : Ideal C where
  carrier := {c | v (c : K) < 1}
  add_mem' := fun {_ _} ha hb => (v.map_add _ _).trans_lt (max_lt ha hb)
  zero_mem' := by simp
  smul_mem' := fun c a ha => by
    change v ((c : K) * a) < 1
    rw [v.map_mul]
    exact (mul_le_of_le_one_left' (hC c c.2)).trans_lt ha

private lemma isPrime_valuationLtOneIdeal {k K : Type*} [CommRing k] [Field K] [Algebra k K]
    (v : Valuation K ℤᵐ⁰) (C : Subalgebra k K) (hC : ∀ c ∈ C, v c ≤ 1) :
    (valuationLtOneIdeal v C hC).IsPrime := by
  refine ⟨fun h => ?_, fun {a b} hab => ?_⟩
  · have h1 : (1 : C) ∈ valuationLtOneIdeal v C hC := h ▸ Submodule.mem_top
    change v ((1 : C) : K) < 1 at h1
    simp at h1
  · change v ((a : K) * b) < 1 at hab
    change v (a : K) < 1 ∨ v (b : K) < 1
    by_contra hn
    push Not at hn
    rw [v.map_mul, le_antisymm (hC a a.2) hn.1, le_antisymm (hC b b.2) hn.2, one_mul] at hab
    exact lt_irrefl _ hab

private lemma mem_range_algebraMap_stalk_iff_of_isIso {Y Z : Scheme.{u}} [IsIntegral Y]
    [IsIntegral Z] (ν : Z ⟶ Y) [IsDominant ν] {z : Z} {y : Y} (hz : ν z = y)
    [IsIso (ν.stalkMap z)] (g : Y.functionField) :
    g ∈ Set.range (algebraMap (Y.presheaf.stalk y) Y.functionField) ↔
      functionFieldMap ν g ∈ Set.range (algebraMap (Z.presheaf.stalk z) Z.functionField) := by
  subst hz
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨_, (MMP.Mori.functionFieldMap_algebraMap_stalk ν _ a).symm⟩
  · rintro ⟨b, hb⟩
    refine ⟨(inv (ν.stalkMap z)).hom b, (functionFieldMap ν).injective ?_⟩
    rw [MMP.Mori.functionFieldMap_algebraMap_stalk, ← hb, ← CommRingCat.comp_apply,
      IsIso.inv_hom_id, CommRingCat.id_apply]

/-- **A valuation ring essentially of finite type is a divisor of the function field.** Let `v`
be a valuation of `k(X)` whose valuation ring is the image of a `k`-algebra `O` essentially of
finite type, and `T ⊆ k(X)` a finite set of `v`-integers generating `k(X)` as a field. The
`k`-algebra `C ⊆ k(X)` generated by `T` and the generators of `O` is finitely generated, with
fraction field `k(X)`, and its localization at `𝔮 = {v < 1}` is the valuation ring of `v`; the
normalization of `Spec C` carries a prime divisor over `𝔮` realizing `v`. -/
private theorem isDivisorOfFunctionField_of_essFiniteType {k : Type u} [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X]
    (v : Valuation X.functionField ℤᵐ⁰)
    (O : Type u) [CommRing O] [Algebra k O] [Algebra.EssFiniteType k O]
    (ρ : letI := functionFieldAlgebra sX; O →ₐ[k] X.functionField)
    (hρ : ∀ g, v g ≤ 1 ↔ g ∈ Set.range ρ)
    (T : Finset X.functionField) (hT : ∀ g ∈ T, v g ≤ 1)
    (hfrac : letI := functionFieldAlgebra sX; ∀ g : X.functionField,
      ∃ a ∈ Algebra.adjoin k (T : Set X.functionField),
        ∃ b ∈ Algebra.adjoin k (T : Set X.functionField), b ≠ 0 ∧ g * b = a)
    (hπ : ∃ π, v π = WithZero.exp (-1)) :
    MMP.Flips.IsDivisorOfFunctionField k sX v := by
  classical
  letI := functionFieldAlgebra sX
  obtain ⟨s, hs⟩ := exists_finset_mul_isUnit_eq k O
  let S : Finset X.functionField := s.image ρ ∪ T
  let C : Subalgebra k X.functionField := Algebra.adjoin k (S : Set X.functionField)
  have hle1 : ∀ g ∈ (S : Set X.functionField), v g ≤ 1 := by
    intro g hg
    rcases Finset.mem_union.1 hg with hg | hg
    · obtain ⟨o, -, rfl⟩ := Finset.mem_image.1 hg
      exact (hρ _).2 ⟨o, rfl⟩
    · exact hT g hg
  have hCle : ∀ c ∈ C, v c ≤ 1 := by
    intro c hc
    induction hc using Algebra.adjoin_induction with
    | mem x hx => exact hle1 x hx
    | algebraMap r => exact (hρ _).2 ⟨algebraMap k O r, ρ.commutes r⟩
    | add x y _ _ hx hy => exact (v.map_add x y).trans (max_le hx hy)
    | mul x y _ _ hx hy => exact (v.map_mul x y).trans_le (mul_le_one' hx hy)
  have hunit : ∀ u : O, IsUnit u → v (ρ u) = 1 := by
    intro u hu
    obtain ⟨w, hw⟩ := hu.exists_right_inv
    have h1 : v (ρ u) * v (ρ w) = 1 := by rw [← v.map_mul, ← map_mul, hw, map_one, v.map_one]
    have a1 := (hρ (ρ u)).2 ⟨u, rfl⟩
    have a2 := (hρ (ρ w)).2 ⟨w, rfl⟩
    refine le_antisymm a1 (not_lt.1 fun hlt => ?_)
    simpa [h1] using mul_lt_one_of_lt_of_le hlt a2
  have hmap : ∀ y ∈ Algebra.adjoin k (s : Set O), ρ y ∈ C := by
    intro y hy
    have h1 : ρ y ∈ (Algebra.adjoin k (s : Set O)).map ρ := ⟨y, hy, rfl⟩
    rw [AlgHom.map_adjoin] at h1
    refine Algebra.adjoin_mono ?_ h1
    rintro _ ⟨w, hw, rfl⟩
    exact Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hw))
  have hloc : ∀ g, v g ≤ 1 → ∃ a ∈ C, ∃ u ∈ C, v u = 1 ∧ g * u = a := by
    intro g hg
    obtain ⟨o, rfl⟩ := (hρ g).1 hg
    obtain ⟨a, ha, u, hu, hunit_u, hau⟩ := hs o
    exact ⟨ρ a, hmap a ha, ρ u, hmap u hu, hunit u hunit_u, by rw [← map_mul, hau]⟩
  have hTC : Algebra.adjoin k (T : Set X.functionField) ≤ C :=
    Algebra.adjoin_mono (fun g hg => Finset.mem_coe.2 (Finset.mem_union_right _ hg))
  -- `C` is a finitely generated domain with fraction field `k(X)`
  haveI : Algebra.FiniteType k C := (Subalgebra.fg_iff_finiteType C).1
      (Subalgebra.fg_adjoin_finset S)
  haveI : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing k C
  haveI hfr : IsFractionRing C X.functionField := by
    refine ⟨fun c => ?_, fun g => ?_, fun {a b} h => ⟨1, by simpa using Subtype.ext h⟩⟩
    · exact IsUnit.mk0 _ (fun h0 => nonZeroDivisors.ne_zero c.2 (Subtype.ext h0))
    · obtain ⟨a, ha, b, hb, hb0, hab⟩ := hfrac g
      exact ⟨⟨⟨a, hTC ha⟩, ⟨⟨b, hTC hb⟩, mem_nonZeroDivisors_of_ne_zero
        (fun h0 => hb0 (congrArg Subtype.val h0))⟩⟩, hab⟩
  -- the prime `𝔮 = {v < 1}` of `C`
  let 𝔮 : Ideal C := valuationLtOneIdeal v C hCle
  have h𝔮 : ∀ c : C, c ∈ 𝔮 ↔ v (c : X.functionField) < 1 := fun c => Iff.rfl
  have h𝔮p : 𝔮.IsPrime := isPrime_valuationLtOneIdeal v C hCle
  obtain ⟨q, hq⟩ : ∃ q : Spec (CommRingCat.of C), q = (⟨𝔮, h𝔮p⟩ : PrimeSpectrum C) := ⟨_, rfl⟩
  have hqv : ∀ c : C, c ∈ PrimeSpectrum.asIdeal q ↔ v (c : X.functionField) < 1 := by
    rwa [hq]
  -- `Spec C`, a variety over `k`
  haveI : IsDomain (CommRingCat.of C) := inferInstanceAs (IsDomain C)
  haveI : AlgebraicGeometry.IsIntegral (Spec (CommRingCat.of C)) := inferInstance
  let sY : Spec (CommRingCat.of C) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k C))
  haveI : LocallyOfFiniteType sY :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2
      (RingHom.finiteType_algebraMap.2 inferInstance)
  haveI : AlgebraicGeometry.IsVariety k sY := ⟨⟩
  letI : Algebra C (Spec (CommRingCat.of C)).functionField :=
    (StructureSheaf.toStalk C (genericPoint (Spec (CommRingCat.of C)))).hom.toAlgebra
  haveI : IsFractionRing C (Spec (CommRingCat.of C)).functionField :=
    functionField_isFractionRing_of_affine (CommRingCat.of C)
  -- the local ring at `q` is the valuation ring of `v`
  haveI : (PrimeSpectrum.asIdeal q).IsPrime := PrimeSpectrum.isPrime q
  letI : Algebra C ((Spec (CommRingCat.of C)).presheaf.stalk q) :=
    StructureSheaf.stalkAlgebra (CommRingCat.of C) q
  haveI : IsLocalization.AtPrime ((Spec (CommRingCat.of C)).presheaf.stalk q)
      (PrimeSpectrum.asIdeal q) :=
    StructureSheaf.IsLocalization.to_stalk (CommRingCat.of C) q
  haveI : IsScalarTower C ((Spec (CommRingCat.of C)).presheaf.stalk q)
      (Spec (CommRingCat.of C)).functionField :=
    IsScalarTower.of_algebraMap_eq fun c => by
      have h := congrArg (fun f => f.hom c) (StructureSheaf.toStalk_stalkSpecializes (R := C)
        ((genericPoint_spec (Spec (CommRingCat.of C))).specializes trivial
            : genericPoint (Spec (CommRingCat.of C)) ⤳ q))
      exact h.symm
  let χ := IsLocalization.algEquiv (nonZeroDivisors C) (Spec (CommRingCat.of C)).functionField
    X.functionField
  have hχ : ∀ c : C, χ (algebraMap C (Spec (CommRingCat.of C)).functionField c) = c := fun c =>
    χ.commutes c
  have hA : ∀ y : (Spec (CommRingCat.of C)).functionField,
      y ∈ Set.range (algebraMap ((Spec (CommRingCat.of C)).presheaf.stalk q)
          (Spec (CommRingCat.of C)).functionField) ↔
        v (χ y) ≤ 1 := by
    intro y
    constructor
    · rintro ⟨b, rfl⟩
      obtain ⟨⟨a, u⟩, rfl⟩ := IsLocalization.mk'_surjective (PrimeSpectrum.asIdeal q).primeCompl b
      have hu : v ((u : C) : X.functionField) = 1 :=
        le_antisymm (hCle _ (u : C).2) (not_lt.1 fun h => u.2 ((hqv _).2 h))
      have key : χ (algebraMap _ (Spec (CommRingCat.of C)).functionField
          (IsLocalization.mk' ((Spec (CommRingCat.of C)).presheaf.stalk q) a u))
              * ((u : C) : X.functionField) =
          (a : X.functionField) := by
        have h1 := congrArg (fun y => χ (algebraMap _ (Spec (CommRingCat.of C)).functionField y))
          (IsLocalization.mk'_spec ((Spec (CommRingCat.of C)).presheaf.stalk q) a u)
        simpa only [map_mul, ← IsScalarTower.algebraMap_apply, hχ] using h1
      have h2 : v (χ (algebraMap _ (Spec (CommRingCat.of C)).functionField
          (IsLocalization.mk' ((Spec (CommRingCat.of C)).presheaf.stalk q) a u)))
              * 1 = v (a : X.functionField) := by
        rw [← hu, ← v.map_mul, key]
      exact ((mul_one _).symm.trans h2).trans_le (hCle _ a.2)
    · intro hy
      obtain ⟨a, ha, u, hu, hvu, hau⟩ := hloc _ hy
      have hu' : (⟨u, hu⟩ : C) ∈ (PrimeSpectrum.asIdeal q).primeCompl := fun h =>
        ((hqv _).1 h).ne hvu
      refine ⟨IsLocalization.mk' ((Spec (CommRingCat.of C)).presheaf.stalk q)
          (⟨a, ha⟩ : C) ⟨_, hu'⟩, ?_⟩
      apply χ.injective
      have hu0 : (u : X.functionField) ≠ 0 := fun h0 => by
        simp [h0] at hvu
      refine mul_right_cancel₀ hu0 ?_
      have h1 := congrArg (fun y => χ (algebraMap _ (Spec (CommRingCat.of C)).functionField y))
        (IsLocalization.mk'_spec ((Spec (CommRingCat.of C)).presheaf.stalk q)
            (⟨a, ha⟩ : C) ⟨_, hu'⟩)
      simp only [map_mul, ← IsScalarTower.algebraMap_apply, hχ] at h1
      exact h1.trans hau.symm
  haveI : ValuationRing ((Spec (CommRingCat.of C)).presheaf.stalk q) := by
    rw [ValuationRing.iff_isInteger_or_isInteger _ (Spec (CommRingCat.of C)).functionField]
    intro y
    rcases le_total (v (χ y)) 1 with h | h
    · exact .inl ((hA y).2 h)
    · exact .inr ((hA y⁻¹).2 (by rw [map_inv₀, map_inv₀]; exact inv_le_one_of_one_le₀ h))
  -- the local ring at `q` is a discrete valuation ring
  haveI : IsNoetherianRing ((Spec (CommRingCat.of C)).presheaf.stalk q) :=
    IsLocalization.isNoetherianRing (PrimeSpectrum.asIdeal q).primeCompl _ inferInstance
  have hnf : IsLocalRing.maximalIdeal ((Spec (CommRingCat.of C)).presheaf.stalk q) ≠ ⊥ := by
    obtain ⟨π, hπv⟩ := hπ
    have hle : v π ≤ 1 := by
      rw [hπv, ← WithZero.exp_zero, WithZero.exp_le_exp]
      norm_num
    obtain ⟨a, ha, u, -, hvu, hau⟩ := hloc π hle
    have hva : v a = WithZero.exp (-1) := by rw [← hau, v.map_mul, hvu, mul_one, hπv]
    intro hbot
    have hmem : algebraMap C ((Spec (CommRingCat.of C)).presheaf.stalk q) ⟨a, ha⟩ ∈
        IsLocalRing.maximalIdeal ((Spec (CommRingCat.of C)).presheaf.stalk q) := by
      rw [IsLocalization.AtPrime.to_map_mem_maximal_iff _ (PrimeSpectrum.asIdeal q)]
      refine (hqv _).2 ?_
      change v a < 1
      rw [hva, ← WithZero.exp_zero, WithZero.exp_lt_exp]
      norm_num
    rw [hbot, Ideal.mem_bot] at hmem
    have h0 : (⟨a, ha⟩ : C) = 0 :=
      IsLocalization.injective ((Spec (CommRingCat.of C)).presheaf.stalk q)
        (PrimeSpectrum.asIdeal q).primeCompl_le_nonZeroDivisors (hmem.trans (map_zero _).symm)
    have h0' : (a : X.functionField) = 0 := congrArg Subtype.val h0
    rw [h0', map_zero] at hva
    exact WithZero.exp_ne_zero hva.symm
  haveI : IsDiscreteValuationRing ((Spec (CommRingCat.of C)).presheaf.stalk q) :=
    { not_a_field' := hnf }
  have hcq : Order.coheight q = 1 := by
    have h := ringKrullDim_stalk_eq_coheight q
    rw [IsDiscreteValuationRing.ringKrullDim_eq_one] at h
    exact_mod_cast h.symm
  -- the normalization
  obtain ⟨Z, ν, hZ, hνb, z, hz, hiso⟩ := exists_normalization_isIso_stalkMap' sY q
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType (ν ≫ sY) := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (ν ≫ sY)
  haveI : IsDominant ν := hνb.isDominant
  have hcz : Order.coheight z = 1 := by
    rw [← coheight_eq_of_isIso_stalkMap ν z hiso, hz, hcq]
  let E' : MMP.Mori.PrimeDivisor Z := PrimeDivisor.ofCoheightOne z hcz
  have hE'g : E'.genericPoint = z := PrimeDivisor.genericPoint_ofCoheightOne _ _
  have hq' : ν E'.genericPoint = q := by rw [hE'g, hz]
  haveI hiso' : IsIso (ν.stalkMap E'.genericPoint) := hE'g ▸ hiso
  have hrange : ∀ y : (Spec (CommRingCat.of C)).functionField,
      y ∈ Set.range (algebraMap ((Spec (CommRingCat.of C)).presheaf.stalk q) _) ↔
        functionFieldMap ν y ∈ Set.range (algebraMap E'.localRing Z.functionField) :=
    mem_range_algebraMap_stalk_iff_of_isIso ν hq'
  -- the identification of function fields and the valuation
  letI := functionFieldAlgebra sY
  letI := functionFieldAlgebra (ν ≫ sY)
  letI := MMP.Mori.functionFieldMapAlgebra ν
  haveI := MMP.Mori.isScalarTower_functionFieldMap sY ν
  haveI hTk : IsScalarTower k C (Spec (CommRingCat.of C)).functionField :=
    IsScalarTower.of_algebraMap_eq fun c => by
      change ((Scheme.ΓSpecIso (.of k)).inv ≫ sY.appTop ≫
        (Spec (CommRingCat.of C)).presheaf.germ ⊤ _ trivial).hom c = _
      rw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
      rfl
  let χk : (Spec (CommRingCat.of C)).functionField ≃ₐ[k] X.functionField := χ.restrictScalars k
  let νk : (Spec (CommRingCat.of C)).functionField ≃ₐ[k] Z.functionField :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom k _ _) hνb.functionFieldMap_bijective
  let e : X.functionField ≃ₐ[k] Z.functionField := χk.symm.trans νk
  have he : ∀ g, e g = functionFieldMap ν (χ.symm g) := fun g => rfl
  haveI := E'.isDiscreteValuationRing_localRing
  refine ⟨Z, ν ≫ sY, hZ, E', e, ?_⟩
  refine valuation_eq_of_le_one_iff v _ (fun g => ?_) hπ ?_
  · rw [Valuation.comap_apply, MMP.Mori.PrimeDivisor.divisorialValuation_le_one_iff]
    change v g ≤ 1 ↔ e g ∈ (algebraMap E'.localRing Z.functionField).range
    rw [he, RingHom.mem_range, ← Set.mem_range, ← hrange, hA]
    change _ ↔ v (χ (χ.symm g)) ≤ 1
    rw [AlgEquiv.apply_symm_apply]
  · obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible E'.localRing
    refine ⟨e.symm (algebraMap _ _ ϖ), ?_⟩
    rw [Valuation.comap_apply]
    change E'.divisorialValuation (e (e.symm _)) = _
    rw [AlgEquiv.apply_symm_apply]
    exact E'.divisorialValuation_algebraMap_of_irreducible hϖ

end Spreading

/-- Pulling back a global section commutes with the passage to the function field. -/
private lemma functionFieldMap_germToFunctionField_top {X' Y' : Scheme.{u}} [IsIntegral X']
    [IsIntegral Y'] (f : Y' ⟶ X') [IsDominant f] (a : Γ(X', ⊤)) :
    functionFieldMap f (X'.germToFunctionField ⊤ a)
        = Y'.germToFunctionField ⊤ (f.appTop.hom a) := by
  rw [← Scheme.algebraMap_germ_eq_germToFunctionField (X := X') (U := ⊤)
    (x := f (genericPoint Y')) (Opens.mem_top _) a, MMP.Mori.functionFieldMap_algebraMap_stalk,
    ← Scheme.algebraMap_germ_eq_germToFunctionField (X := Y') (U := ⊤) (x := genericPoint Y')
      (Opens.mem_top _)]
  congr 1
  rw [← CommRingCat.comp_apply, Scheme.Hom.germ_stalkMap]
  rfl

/-! ### The canonical divisor and the pair condition on the generic surface -/

/-- **A normal variety over a perfect field has a canonical divisor.** On the smooth locus
`T = S_sm` (nonempty, as it contains the generic point) the canonical sheaf is `𝒪_T(K_T)` for a
divisor `K_T` of `T`; its closure `K_S` in `S` restricts to `K_T` on `T`, so
`𝒪_S(K_S)|_T ≅ 𝒪_T(K_T) ≅ ω_T`. -/
private theorem exists_isCanonicalDivisor {K : Type u} [Field K] [PerfectField K]
    {S : Scheme.{u}} (sS : S ⟶ Spec (.of K)) [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    [CompactSpace S] (hS : IsNormalVariety K sS) {n : ℕ} (hn : topologicalKrullDim S = n) :
    ∃ KS : MMP.Mori.Divisor S, KS.IsCanonicalDivisor sS n := by
  haveI : LocallyOfFiniteType sS := hS.1.toLocallyOfFiniteType
  set T := MMP.Mori.smoothLocus sS with hT
  have hTeq : T = sS.smoothLocus := MMP.Mori.smoothLocus_eq_smoothLocus sS
  haveI : Nonempty T := ⟨⟨genericPoint S, hTeq ▸ sS.genericPoint_mem_smoothLocus_of_perfectField⟩⟩
  haveI : IsDominant T.ι := isDominant_opens_ι T
  have hTv : IsNormalVariety K (T.ι ≫ sS) := isNormalVariety_ι hS T
  haveI : MMP.Mori.IsVariety K (T.ι ≫ sS) := hTv.1
  haveI : IsIntegral T := inferInstance
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

/-- **The canonical forms of `X` and of the generic surface.** There are a nonzero rational
`(d + 2)`-form `ω` on `X` over `k` and a nonzero rational `2`-form `ω_S` on the generic surface
`S` over `K = k(t)` with `ord_P(ω_S) = ord_{ι(P)}(ω)` at every prime divisor `P` of `S`.

Take `ω = dt₁ ∧ ⋯ ∧ dt_d ∧ η₁ ∧ η₂` and `ω_S = η̄₁ ∧ η̄₂` (the images of `ηⱼ` in `Ω_{K(S)/K}`), for
1-forms `η₁, η₂` of `k(X) = K(S)`. Let `P` be a prime divisor of `S`, `Γ` the prime divisor of
`U` through `ι(η_P)` and `O = 𝒪_{U,Γ} ≅ 𝒪_{S,P}`. The split exact sequence
`MMP.Mori.PrimeDivisor.exact_mapBaseChange_map_localRing` (for `U`, `m = d`,
`n = d + 2`) gives `ω̃₁, ω̃₂ ∈ Ω_{O/k}` lifting a basis of `Ω_{O/K}` with
`dt ∧ ω̃` generating `Ω^{d+2}_{O/k}` and `ω̄̃` generating `Ω²_{O/K}`; after clearing a common
denominator `c ∈ O` of the `ηⱼ`, `ηⱼ ≡ ∑ βⱼᵢ ω̃ᵢ` modulo `span(dtᵢ)`, so both `ω` and `ω_S` are
`c⁻² det β` times the generator, and their orders along `P` agree. -/
private theorem exists_ordForm_genSurface_eq
    {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {B : QDivisor X} (hB : MMP.Fourfold.IsPair sX B) {x : X}
    {U : X.Opens} (hU : IsAffineOpen U) (hxU : x ∈ U) {d : ℕ} (t : Fin d → Γ(X, U))
    (ht : letI := sectionAlgebra sX U;
      IsTranscendenceBasis k (Ideal.Quotient.mk (hU.primeIdealOf ⟨x, hxU⟩).asIdeal ∘ t))
    [IsIntegral (Spec (genRing sX t))] [IsLocallyNoetherian (Spec (genRing sX t))]
    [IsNormal (Spec (genRing sX t))] (hdimX : topologicalKrullDim X = (d + 2 : ℕ))
    [IsDominant (genι sX t hU)]
    (hvar : IsNormalVariety (genField k d) (genStructure sX t))
    (hdimS : topologicalKrullDim (Spec (genRing sX t)) = 2) :
    ∃ (ω : MMP.Mori.RationalPluriForms sX (d + 2) 1)
      (ωS : MMP.Mori.RationalPluriForms (genStructure sX t) 2 1), ω ≠ 0 ∧ ωS ≠ 0 ∧
      ∀ P : MMP.Mori.PrimeDivisor (Spec (genRing sX t)),
        MMP.Mori.PrimeDivisor.ordForm P ωS =
          MMP.Mori.PrimeDivisor.ordForm (genPrimeDivisor sX t hU P) ω := by
  classical
  haveI := hB.charZero
  haveI : CharZero (genField k d) :=
    charZero_of_injective_algebraMap (algebraMap k (genField k d)).injective
  have hXv : IsNormalVariety k sX := hB.isPair.1
  haveI : LocallyOfFiniteType sX := hXv.1.toLocallyOfFiniteType
  haveI : Nonempty U := ⟨⟨x, hxU⟩⟩
  have htU : letI := sectionAlgebra sX U; AlgebraicIndependent k t :=
    letI := sectionAlgebra sX U
    AlgebraicIndependent.of_comp (Ideal.Quotient.mkₐ k (hU.primeIdealOf ⟨x, hxU⟩).asIdeal) ht.1
  set g := genι sX t hU ≫ U.ι with hg
  haveI : IsDominant g := (IsDominant.comp_iff (genι sX t hU) U.ι).2 (isDominant_opens_ι U)
  have hbij : Function.Bijective (functionFieldMap g) := by
    haveI := isIso_stalkMap_genι_comp sX t hU (genericPoint (Spec (genRing sX t)))
    exact ConcreteCategory.bijective_of_isIso
      ((X.presheaf.stalkCongr (Inseparable.of_eq (map_genericPoint_of_isDominant g).symm)).hom ≫
        g.stalkMap (genericPoint _))
  have hd := MMP.Mori.toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hdimX
  letI := MMP.Mori.functionFieldAlgebra sX
  letI := MMP.Mori.functionFieldAlgebra (g ≫ sX)
  letI := MMP.Mori.functionFieldMapAlgebra g
  haveI := MMP.Mori.isScalarTower_functionFieldMap sX g
  obtain ⟨ω₀, hω₀⟩ := MMP.Mori.exists_isPullbackGenerator_of_bijective (sX := sX) (f := g) hbij hd
  set bX := MMP.Mori.basisOfSpanSingleton hω₀.1 hω₀.ne_zero
  set bk := MMP.Mori.basisOfSpanSingleton hω₀.2.1 hω₀.2.2
  let ω : MMP.Mori.RationalPluriForms sX (d + 2) 1 := MMP.Mori.ZTensorPower.basis bX 1 ()
  have hpull : MMP.Mori.pullbackRationalPluriForms sX g ω
      = MMP.Mori.ZTensorPower.basis bk 1 () := by
    change MMP.Mori.pullbackForms (K' := (Spec (genRing sX t)).functionField) 1 ω = _
    rw [MMP.Mori.pullbackForms_eq hω₀]
    simp [MMP.Mori.pullbackFormsAlong, ω, bX, bk]
  letI := MMP.Mori.functionFieldAlgebra (genStructure sX t)
  haveI := isScalarTower_stalkAlgebra_comp (genStructure sX t) ((genι sX t hU ≫ U.ι) ≫ sX)
    (by rw [Category.assoc]; exact genι_comp_eq sX t hU) (genericPoint (Spec (genRing sX t)))
  obtain ⟨bS⟩ := MMP.Positivity.exists_basis_topForms hvar (n := 2) (by exact_mod_cast hdimS)
  obtain ⟨u, hu⟩ := exists_ιMulti_ne_zero (bS.ne_zero ())
  choose η hη using fun j => KaehlerDifferential.map_surjective k (genField k d)
    (Spec (genRing sX t)).functionField (u j)
  have hηu : (fun j => KaehlerDifferential.map k (genField k d) _ _ (η j)) = u := funext hη
  set a := exteriorPower.ιMulti (Spec (genRing sX t)).functionField (d + 2)
    (Fin.append (fun i => KaehlerDifferential.D k _
      (algebraMap (genField k d) (Spec (genRing sX t)).functionField
        (algebraMap (MvPolynomial (Fin d) k) (genField k d) (.X i)))) η) with ha
  obtain ⟨c, hc⟩ : ∃ c, c • bk () = a := by
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (hω₀.2.1 ▸ Submodule.mem_top (x := a))
    exact ⟨c, by rwa [MMP.Mori.basisOfSpanSingleton_apply]⟩
  haveI := locallyOfFiniteType_genStructure sX t hU
  by_cases hc0 : c = 0
  · refine ⟨ω, MMP.Mori.ZTensorPower.basis bS 1 (), (MMP.Mori.ZTensorPower.basis bX 1).ne_zero (),
      (MMP.Mori.ZTensorPower.basis bS 1).ne_zero (), fun P => ?_⟩
    exfalso
    letI := MMP.Mori.stalkAlgebra ((genι sX t hU ≫ U.ι) ≫ sX) P.genericPoint
    letI := MMP.Mori.stalkAlgebra (genStructure sX t) P.genericPoint
    haveI := isScalarTower_stalkAlgebra_comp (genStructure sX t) ((genι sX t hU ≫ U.ι) ≫ sX)
      (by rw [Category.assoc]; exact genι_comp_eq sX t hU) P.genericPoint
    haveI := MMP.Mori.isScalarTower_stalk_functionField ((genι sX t hU ≫ U.ι) ≫ sX)
      P.genericPoint
    haveI := MMP.Mori.isScalarTower_stalk_functionField (genStructure sX t) P.genericPoint
    haveI := essFiniteType_stalkAlgebra (genStructure sX t) P.genericPoint
    obtain ⟨σk, σK, hσk, hσK, cP, h1, h2⟩ :=
        exists_eq_smul_topFormsMap_genSurface sX hXv hU t htU hdimX P
      (fun _ => rfl) (fun _ => rfl) η
    rw [hηu] at h2
    have hcP : cP ≠ 0 := by
      rintro rfl
      rw [zero_smul] at h2
      exact hu h2
    have h0 : MMP.Mori.topFormsMap k P.localRing (Spec (genRing sX t)).functionField (d + 2) σk
        = 0 := by
      rw [← ha, ← hc, hc0, zero_smul] at h1
      exact (smul_eq_zero.1 h1.symm).resolve_left hcP
    have hspan := MMP.Mori.span_singleton_topFormsMap (K := (Spec (genRing sX t)).functionField)
      (nonZeroDivisors P.localRing) hσk
    rw [h0, Submodule.span_singleton_eq_bot.2 rfl] at hspan
    exact bk.ne_zero () (by
      have : bk () ∈ (⊤ : Submodule (Spec (genRing sX t)).functionField _) := trivial
      rw [← hspan] at this
      exact (Submodule.mem_bot _).1 this)
  · set vK := c⁻¹ • exteriorPower.ιMulti (Spec (genRing sX t)).functionField 2 u with hvK
    have hvK0 : vK ≠ 0 := smul_ne_zero (inv_ne_zero hc0) hu
    have hvKspan : Submodule.span (Spec (genRing sX t)).functionField {vK} = ⊤ :=
      span_singleton_eq_top_of_basis_unit bS hvK0
    obtain ⟨bK, hbK⟩ : ∃ bK : Module.Basis Unit (Spec (genRing sX t)).functionField
        (⋀[(Spec (genRing sX t)).functionField]^2
          Ω[(Spec (genRing sX t)).functionField⁄genField k d]), bK () = vK :=
      ⟨MMP.Mori.basisOfSpanSingleton hvKspan hvK0, MMP.Mori.basisOfSpanSingleton_apply _ _ _⟩
    refine ⟨ω, MMP.Mori.ZTensorPower.basis bK 1 (), (MMP.Mori.ZTensorPower.basis bX 1).ne_zero (),
      (MMP.Mori.ZTensorPower.basis bK 1).ne_zero (), fun P => ?_⟩
    letI := MMP.Mori.stalkAlgebra ((genι sX t hU ≫ U.ι) ≫ sX) P.genericPoint
    letI := MMP.Mori.stalkAlgebra (genStructure sX t) P.genericPoint
    haveI := isScalarTower_stalkAlgebra_comp (genStructure sX t) ((genι sX t hU ≫ U.ι) ≫ sX)
      (by rw [Category.assoc]; exact genι_comp_eq sX t hU) P.genericPoint
    haveI := MMP.Mori.isScalarTower_stalk_functionField ((genι sX t hU ≫ U.ι) ≫ sX)
      P.genericPoint
    haveI := MMP.Mori.isScalarTower_stalk_functionField (genStructure sX t) P.genericPoint
    haveI := essFiniteType_stalkAlgebra (genStructure sX t) P.genericPoint
    haveI := isIso_stalkMap_genι_comp sX t hU P.genericPoint
    rw [← MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso g hbij hd P
      (genPrimeDivisor sX t hU P) (by rw [genericPoint_genPrimeDivisor]; rfl) ω, hpull]
    obtain ⟨σk, σK, hσk, hσK, cP, h1, h2⟩ :=
        exists_eq_smul_topFormsMap_genSurface sX hXv hU t htU hdimX P
      (fun _ => rfl) (fun _ => rfl) η
    rw [hηu] at h2
    have hb : bk () = (c⁻¹ * cP) •
        MMP.Mori.topFormsMap k P.localRing (Spec (genRing sX t)).functionField (d + 2) σk :=
      eq_inv_mul_smul_of_smul_eq hc0 hc (ha.symm.trans h1)
    have hb' : bK () = (c⁻¹ * cP) • MMP.Mori.topFormsMap (genField k d) P.localRing
        (Spec (genRing sX t)).functionField 2 σK :=
      hbK.trans (hvK.trans (inv_smul_eq_mul_smul h2))
    symm
    exact ordAt_eq_ordAt_of_basis_eq_smul (MMP.Mori.PrimeDivisor.ord_mul_of_ne_zero P)
      (fun _ ha => MMP.Mori.PrimeDivisor.ord_algebraMap_of_isUnit P ha) hσk hσK bk bK _ hb hb' 1
      _ _ (by simp)

/-- **The pair condition for the generic surface.** With `B_S = genBoundary sX t hU B` the
boundary of the generic surface `S = Spec Γ(X, U)[M⁻¹]` over `K = k(t)`, `(S, B_S)` is a pair:
for the forms `ω, ω_S` of `exists_ordForm_genSurface_eq`, `div(ω_S)` is a canonical divisor of
`S` (linearly equivalent to the one of `exists_isCanonicalDivisor`), and `m(div(ω_S) + B_S)` is
the pull-back along `S ⟶ X` of the Cartier divisor `m(div(ω) + B)`, since all stalk maps of
`S ⟶ X` are isomorphisms. -/
private theorem isPair_genBoundary
    {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {B : QDivisor X} (hB : MMP.Fourfold.IsPair sX B) {x : X}
    {U : X.Opens} (hU : IsAffineOpen U) (hxU : x ∈ U) {d : ℕ} (t : Fin d → Γ(X, U))
    (ht : letI := sectionAlgebra sX U;
      IsTranscendenceBasis k (Ideal.Quotient.mk (hU.primeIdealOf ⟨x, hxU⟩).asIdeal ∘ t))
    [IsIntegral (Spec (genRing sX t))] [IsLocallyNoetherian (Spec (genRing sX t))]
    [IsNormal (Spec (genRing sX t))] [IsDominant (genι sX t hU)]
    (hvar : IsNormalVariety (genField k d) (genStructure sX t))
    (hdimS : topologicalKrullDim (Spec (genRing sX t)) = 2)
    (hdimX : topologicalKrullDim X = (d + 2 : ℕ)) :
    MMP.Mori.IsPair (genStructure sX t) (genBoundary sX t hU B) := by
  have := hB.charZero
  haveI : CharZero (genField k d) :=
    charZero_of_injective_algebraMap (algebraMap k (genField k d)).injective
  have hXv : IsNormalVariety k sX := hB.isPair.1
  haveI : LocallyOfFiniteType sX := hXv.1.toLocallyOfFiniteType
  haveI : QuasiCompact sX := hXv.1.toQuasiCompact
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : LocallyOfFiniteType (genStructure sX t) := hvar.1.toLocallyOfFiniteType
  obtain ⟨KS, hKS⟩ := exists_isCanonicalDivisor (genStructure sX t) hvar (n := 2) hdimS
  obtain ⟨ω, ωS, hω, hωS, hord⟩ := exists_ordForm_genSurface_eq sX hB hU hxU t ht hdimX hvar hdimS
  have h1 := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hvar hKS hωS
  rw [one_smul] at h1
  refine ⟨hvar, 2, MMP.Mori.divisorOfForm ωS, hKS.of_linearlyEquivalent h1, ?_⟩
  obtain ⟨-, n, KX, hKX, hQ⟩ := hB.isPair
  have hn : n = d + 2 := by
    have h := hKX.1.symm.trans hdimX
    exact_mod_cast h
  subst hn
  have h2 := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hXv hKX hω
  rw [one_smul] at h2
  obtain ⟨m, hm, C, hC, hCc⟩ := hQ.add_of_linearlyEquivalent h2.symm
  set g := genι sX t hU ≫ U.ι with hg
  haveI : Nonempty U := ⟨⟨x, hxU⟩⟩
  haveI : IsDominant g := by
    rw [hg]
    exact (IsDominant.comp_iff (genι sX t hU) U.ι).2 (isDominant_opens_ι U)
  have hgen : ∀ Z : irreducibleComponents (Spec (genRing sX t)),
      g (MMP.Mori.componentGenericPoint _ Z) ∉ C.supp :=
    MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant g C
  obtain ⟨C', hC'⟩ := hCc.exists_isPullback hgen
  refine ⟨m, hm, C', ?_, hC'.isCartier hCc⟩
  ext P
  haveI := isIso_stalkMap_genι_comp sX t hU P.genericPoint
  have hc := MMP.Positivity.coeff_eq_of_isPullback P (genPrimeDivisor sX t hU P)
    (genericPoint_genPrimeDivisor sX t hU P).symm hCc hC'
  have hc2 := congrArg (fun D => MMP.Mori.DivisorWithCoeffs.coeff D (genPrimeDivisor sX t hU P)) hC
  simp only [MMP.Mori.Divisor.coeff_toQDivisor, MMP.Mori.DivisorWithCoeffs.coeff_smul,
    MMP.Mori.DivisorWithCoeffs.coeff_add, MMP.Mori.coeff_divisorOfForm] at hc2 ⊢
  rw [hc, hc2, coeff_genBoundary, hord]

/-- A divisor over `S` whose centre is the point `q` has its generic point over `q`. -/
private lemma map_genericPoint_eq_of_center_eq_singleton {K : Type u} [Field K] {S : Scheme.{u}}
    {sS : S ⟶ Spec (.of K)} (D : DivisorOver K sS) {q : S} (hD : (D.center : Set S) = {q}) :
    D.f D.E.genericPoint = q := by
  have h := D.center_eq_closure_genericPoint
  rw [hD] at h
  have : D.f D.E.genericPoint ∈ closure {D.f D.E.genericPoint} := subset_closure rfl
  rwa [← h] at this

/-- **Spreading out a divisor over the generic surface.** A divisor `(T, g, E)` over the generic
surface `S` spreads to a divisor `(Y', f, F)` over `U` with `f` proper, the same valuation of the
common function field (through `ι = genι`) and `f(η_F) = ι(g(η_E))`: the local ring of `E` is
essentially of finite type over `k(t)`, hence over `k`, so its valuation is a divisor of `k(U)`
dominating the local ring of `U` at `ι(g(η_E))`. -/
private theorem exists_properDivisorOver_of_genSurface
    {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [IsIntegral X] (hXv : IsNormalVariety k sX)
    {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U] [IsIntegral U] {d : ℕ}
    (t : Fin d → Γ(X, U))
    [IsIntegral (Spec (genRing sX t))] [IsDominant (genι sX t hU)]
    (D : DivisorOver (genField k d) (genStructure sX t)) :
    ∃ D' : DivisorOver k (U.ι ≫ sX), IsProper D'.f ∧
      D'.valuation = D.valuation.comap (functionFieldMap (genι sX t hU)) ∧
      D'.f D'.E.genericPoint = genι sX t hU (D.f D.E.genericPoint) := by
  classical
  haveI : LocallyOfFiniteType sX := hXv.1.toLocallyOfFiniteType
  have hUv := isNormalVariety_ι hXv U
  haveI : AlgebraicGeometry.IsVariety k (U.ι ≫ sX) := hUv.1
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  haveI : LocallyOfFiniteType (D.f ≫ genStructure sX t) :=
    D.isNormalVariety.1.toLocallyOfFiniteType
  set xU := genι sX t hU (D.f D.E.genericPoint)
  have hxp : xU = genι sX t hU (D.f D.E.genericPoint) := rfl
  set v := D.valuation.comap (functionFieldMap (genι sX t hU)) with hv
  have hvapp : ∀ g, v g = D.E.divisorialValuation
      (functionFieldMap D.f (functionFieldMap (genι sX t hU) g)) := fun g => rfl
  have hstalk : ∀ a : U.toScheme.presheaf.stalk (genι sX t hU (D.f D.E.genericPoint)),
      functionFieldMap D.f (functionFieldMap (genι sX t hU)
        (algebraMap _ U.toScheme.functionField a)) =
        algebraMap D.E.localRing D.Y.functionField
          (D.f.stalkMap D.E.genericPoint ((genι sX t hU).stalkMap _ a)) := fun a => by
    rw [MMP.Mori.functionFieldMap_algebraMap_stalk, MMP.Mori.functionFieldMap_algebraMap_stalk]
  have hle : ∀ a : U.toScheme.presheaf.stalk xU,
      v (algebraMap _ U.toScheme.functionField a) ≤ 1 := by
    rw [hxp]
    intro a
    rw [hvapp, hstalk, MMP.Mori.PrimeDivisor.divisorialValuation_le_one_iff]
    exact ⟨_, rfl⟩
  have hlt : ∀ a ∈ IsLocalRing.maximalIdeal (U.toScheme.presheaf.stalk xU),
      v (algebraMap _ U.toScheme.functionField a) < 1 := by
    rw [hxp]
    intro a ha
    rw [hvapp, hstalk]
    have hm1 : ((genι sX t hU).stalkMap _ a) ∈
        IsLocalRing.maximalIdeal ((Spec (genRing sX t)).presheaf.stalk (D.f D.E.genericPoint)) :=
      (IsLocalRing.mem_maximalIdeal _).2 fun hu =>
        (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit _ a hu)
    have hm : D.f.stalkMap D.E.genericPoint ((genι sX t hU).stalkMap _ a) ∈
        IsLocalRing.maximalIdeal D.E.localRing :=
      (IsLocalRing.mem_maximalIdeal _).2 fun hu =>
        (IsLocalRing.mem_maximalIdeal _).1 hm1 (isUnit_of_map_unit _ _ hu)
    haveI := D.E.isDiscreteValuationRing_localRing
    exact (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem
      (IsDiscreteValuationRing.maximalIdeal D.E.localRing) _).2 hm
  -- the valuation ring of `v` is the local ring of `E`, essentially of finite type over `k`
  have hbijι := bijective_functionFieldMap_genι sX t hU
  let θ : U.toScheme.functionField →+* D.Y.functionField :=
    (functionFieldMap D.f).comp (functionFieldMap (genι sX t hU))
  have hθ : Function.Bijective θ := D.isBirationalMorphism.functionFieldMap_bijective.comp hbijι
  let θe := RingEquiv.ofBijective θ hθ
  letI : Algebra (genField k d) D.E.localRing :=
    MMP.Mori.stalkAlgebra (D.f ≫ genStructure sX t) D.E.genericPoint
  letI : Algebra k D.E.localRing :=
    ((algebraMap (genField k d) D.E.localRing).comp (algebraMap k (genField k d))).toAlgebra
  haveI : IsScalarTower k (genField k d) D.E.localRing :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.EssFiniteType (genField k d) D.E.localRing :=
    essFiniteType_stalkAlgebra (D.f ≫ genStructure sX t) D.E.genericPoint
  haveI : Algebra.EssFiniteType (MvPolynomial (Fin d) k) (genField k d) :=
    Algebra.EssFiniteType.of_isLocalization _ (nonZeroDivisors (MvPolynomial (Fin d) k))
  haveI : Algebra.EssFiniteType k (genField k d) :=
    Algebra.EssFiniteType.comp k (MvPolynomial (Fin d) k) (genField k d)
  haveI : Algebra.EssFiniteType k D.E.localRing :=
    Algebra.EssFiniteType.comp k (genField k d) D.E.localRing
  letI := MMP.Mori.functionFieldAlgebra (U.ι ≫ sX)
  letI := MMP.Mori.functionFieldAlgebra (genι sX t hU ≫ U.ι ≫ sX)
  letI := MMP.Mori.functionFieldMapAlgebra (genι sX t hU)
  haveI h1 := MMP.Mori.isScalarTower_functionFieldMap (U.ι ≫ sX) (genι sX t hU)
  letI := MMP.Mori.functionFieldAlgebra (genStructure sX t)
  haveI h2 := isScalarTower_stalkAlgebra_comp (genStructure sX t) (genι sX t hU ≫ U.ι ≫ sX)
    (genι_comp_eq sX t hU) (genericPoint (Spec (genRing sX t)))
  letI := MMP.Mori.functionFieldAlgebra (D.f ≫ genStructure sX t)
  letI := MMP.Mori.functionFieldMapAlgebra D.f
  haveI h3 := MMP.Mori.isScalarTower_functionFieldMap (genStructure sX t) D.f
  haveI h4 := MMP.Mori.isScalarTower_stalk_functionField (D.f ≫ genStructure sX t)
    D.E.genericPoint
  let ρ : D.E.localRing →ₐ[k] U.toScheme.functionField :=
    { toRingHom := (θe.symm : D.Y.functionField →+* U.toScheme.functionField).comp
        (algebraMap D.E.localRing D.Y.functionField)
      commutes' := fun c => θe.injective (by
        change θe (θe.symm _) = θ _
        rw [RingEquiv.apply_symm_apply]
        calc algebraMap D.E.localRing D.Y.functionField
              (algebraMap (genField k d) D.E.localRing (algebraMap k (genField k d) c))
            = algebraMap (genField k d) D.Y.functionField (algebraMap k (genField k d) c) :=
              (IsScalarTower.algebraMap_apply _ _ _ _).symm
          _ = algebraMap (Spec (genRing sX t)).functionField D.Y.functionField
              (algebraMap (genField k d) (Spec (genRing sX t)).functionField
                (algebraMap k (genField k d) c)) := IsScalarTower.algebraMap_apply _ _ _ _
          _ = algebraMap (Spec (genRing sX t)).functionField D.Y.functionField
              (algebraMap k (Spec (genRing sX t)).functionField c) := by
            rw [← IsScalarTower.algebraMap_apply k (genField k d)]
          _ = algebraMap (Spec (genRing sX t)).functionField D.Y.functionField
              (algebraMap U.toScheme.functionField (Spec (genRing sX t)).functionField
                (algebraMap k U.toScheme.functionField c)) := by
            rw [← IsScalarTower.algebraMap_apply k U.toScheme.functionField]
          _ = θ (algebraMap k U.toScheme.functionField c) := rfl) }
  have hρ : ∀ g, v g ≤ 1 ↔ g ∈ Set.range ρ := by
    intro g
    rw [hvapp, MMP.Mori.PrimeDivisor.divisorialValuation_le_one_iff]
    constructor
    · rintro ⟨o, ho⟩
      refine ⟨o, ?_⟩
      change θe.symm (algebraMap D.E.localRing D.Y.functionField o) = g
      rw [ho]
      exact θe.symm_apply_apply g
    · rintro ⟨o, rfl⟩
      exact ⟨o, (θe.apply_symm_apply _).symm⟩
  -- generators of `Γ(U, ⊤)` and the realization
  haveI : IsAffine U.toScheme := hU
  letI := sectionAlgebra (U.ι ≫ sX) ⊤
  haveI := MMP.Mori.finiteType_sectionAlgebra (U.ι ≫ sX) (isAffineOpen_top U.toScheme)
  obtain ⟨s₀, hs₀⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra k Γ(U.toScheme, ⊤)).FG)
  haveI := MMP.Mori.isScalarTower_section_functionField (U.ι ≫ sX) (⊤ : U.toScheme.Opens)
  let γ : Γ(U.toScheme, ⊤) →ₐ[k] U.toScheme.functionField := IsScalarTower.toAlgHom k _ _
  haveI : IsFractionRing Γ(U.toScheme, ⊤) U.toScheme.functionField :=
    functionField_isFractionRing_of_isAffineOpen U.toScheme ⊤ (isAffineOpen_top U.toScheme)
  have hγ : ∀ a, γ a ∈
      Algebra.adjoin k ((s₀.image γ : Finset _) : Set U.toScheme.functionField) := by
    intro a
    have h1 : γ a ∈ (Algebra.adjoin k (s₀ : Set Γ(U.toScheme, ⊤))).map γ := by
      rw [hs₀]
      exact ⟨a, trivial, rfl⟩
    rw [AlgHom.map_adjoin] at h1
    simpa using h1
  have hT : ∀ g ∈ s₀.image γ, v g ≤ 1 := by
    intro g hg
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hg
    change v (algebraMap Γ(U.toScheme, ⊤) U.toScheme.functionField a) ≤ 1
    rw [show algebraMap Γ(U.toScheme, ⊤) U.toScheme.functionField a =
      algebraMap _ U.toScheme.functionField (U.toScheme.presheaf.germ ⊤ xU trivial a) from
        (Scheme.algebraMap_germ_eq_germToFunctionField (X := U.toScheme) (U := ⊤) (x := xU)
          (Opens.mem_top xU) a).symm]
    exact hle _
  have hfrac : ∀ g : U.toScheme.functionField,
      ∃ a ∈ Algebra.adjoin k ((s₀.image γ : Finset _) : Set U.toScheme.functionField),
        ∃ b ∈ Algebra.adjoin k ((s₀.image γ : Finset _) : Set U.toScheme.functionField),
          b ≠ 0 ∧ g * b = a := by
    intro g
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := Γ(U.toScheme, ⊤)) g
    have hb0 : algebraMap Γ(U.toScheme, ⊤) U.toScheme.functionField b ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    exact ⟨_, hγ a, _, hγ b, hb0, div_mul_cancel₀ _ hb0⟩
  have hπ : ∃ π, v π = WithZero.exp (-1) := by
    haveI := D.E.isDiscreteValuationRing_localRing
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible D.E.localRing
    refine ⟨ρ ϖ, ?_⟩
    rw [hvapp]
    change D.E.divisorialValuation (θe (θe.symm _)) = _
    rw [RingEquiv.apply_symm_apply]
    exact D.E.divisorialValuation_algebraMap_of_irreducible hϖ
  have hdiv : MMP.Flips.IsDivisorOfFunctionField k (U.ι ≫ sX) v :=
    isDivisorOfFunctionField_of_essFiniteType (U.ι ≫ sX) v D.E.localRing ρ hρ (s₀.image γ) hT
      hfrac hπ
  obtain ⟨D'', -, hD''v, hD''x⟩ :=
    MMP.Flips.exists_properDivisorOver_isProjective_of_dominates (U.ι ≫ sX) hdiv xU hle hlt
  exact ⟨D''.toDivisorOver, D''.isProper, hD''v, hD''x⟩

/-- **The orders of the two bases agree at every prime divisor of the generic surface.** If
`c • bk = dt ∧ η` (over `k`) and `bK = c⁻¹ • η̄₁ ∧ η̄₂` (over `K = k(t)`) on `K(S)`, then the forms
`bk` and `bK` have the same order along every prime divisor `P` of the generic surface: both are
the same multiple of the images of generators of `Ω^{d+2}_{𝒪_{S,P}/k}` and `Ω²_{𝒪_{S,P}/K}`. -/
private theorem ordForm_basis_eq_ordForm_basis_genSurface
    {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] (hXv : IsNormalVariety k sX)
    {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U] {d : ℕ} (t : Fin d → Γ(X, U))
    (ht : letI := sectionAlgebra sX U; AlgebraicIndependent k t)
    [IsIntegral (Spec (genRing sX t))] [IsLocallyNoetherian (Spec (genRing sX t))]
    [IsNormal (Spec (genRing sX t))]
    (hdimX : topologicalKrullDim X = (d + 2 : ℕ))
    (P : MMP.Mori.PrimeDivisor (Spec (genRing sX t))) :
    letI := MMP.Mori.functionFieldAlgebra (genι sX t hU ≫ U.ι ≫ sX)
    letI := MMP.Mori.functionFieldAlgebra (genStructure sX t)
    haveI := isScalarTower_stalkAlgebra_comp (genStructure sX t) (genι sX t hU ≫ U.ι ≫ sX)
      (genι_comp_eq sX t hU) (genericPoint (Spec (genRing sX t)))
    ∀ (bk : Module.Basis Unit (Spec (genRing sX t)).functionField
        (⋀[(Spec (genRing sX t)).functionField]^(d + 2)
          Ω[(Spec (genRing sX t)).functionField⁄k]))
      (bK : Module.Basis Unit (Spec (genRing sX t)).functionField
        (⋀[(Spec (genRing sX t)).functionField]^2
          Ω[(Spec (genRing sX t)).functionField⁄genField k d]))
      (η : Fin 2 → Ω[(Spec (genRing sX t)).functionField⁄k])
      (c : (Spec (genRing sX t)).functionField), c ≠ 0 →
      c • bk () = exteriorPower.ιMulti _ (d + 2) (Fin.append (fun i => KaehlerDifferential.D k _
        (algebraMap (genField k d) (Spec (genRing sX t)).functionField
          (algebraMap (MvPolynomial (Fin d) k) (genField k d) (.X i)))) η) →
      bK () = c⁻¹ • exteriorPower.ιMulti (Spec (genRing sX t)).functionField 2
        (fun j => KaehlerDifferential.map k (genField k d) (Spec (genRing sX t)).functionField
            (Spec (genRing sX t)).functionField (η j)) →
      P.ordForm (@id (MMP.Mori.RationalPluriForms (genι sX t hU ≫ U.ι ≫ sX) (d + 2) 1)
          (MMP.Mori.ZTensorPower.basis bk 1 ())) =
        P.ordForm (@id (MMP.Mori.RationalPluriForms (genStructure sX t) 2 1)
          (MMP.Mori.ZTensorPower.basis bK 1 ())) := by
  intro bk bK η c hc0 hc hbK
  letI := MMP.Mori.functionFieldAlgebra (genι sX t hU ≫ U.ι ≫ sX)
  letI := MMP.Mori.functionFieldAlgebra (genStructure sX t)
  haveI := isScalarTower_stalkAlgebra_comp (genStructure sX t) (genι sX t hU ≫ U.ι ≫ sX)
    (genι_comp_eq sX t hU) (genericPoint (Spec (genRing sX t)))
  haveI : LocallyOfFiniteType sX := hXv.1.toLocallyOfFiniteType
  haveI := locallyOfFiniteType_genStructure sX t hU
  letI := MMP.Mori.stalkAlgebra (genι sX t hU ≫ U.ι ≫ sX) P.genericPoint
  letI := MMP.Mori.stalkAlgebra (genStructure sX t) P.genericPoint
  haveI := isScalarTower_stalkAlgebra_comp (genStructure sX t) (genι sX t hU ≫ U.ι ≫ sX)
    (genι_comp_eq sX t hU) P.genericPoint
  haveI := MMP.Mori.isScalarTower_stalk_functionField (genι sX t hU ≫ U.ι ≫ sX) P.genericPoint
  haveI := MMP.Mori.isScalarTower_stalk_functionField (genStructure sX t) P.genericPoint
  haveI := essFiniteType_stalkAlgebra (genStructure sX t) P.genericPoint
  obtain ⟨σk, σK, hσk, hσK, cP, h1, h2⟩ := exists_eq_smul_topFormsMap_genSurface sX hXv hU t ht
    hdimX P (fun _ => by rw [Category.assoc]; rfl) (fun _ => rfl) η
  have hb := eq_inv_mul_smul_of_smul_eq hc0 hc h1
  have hb' := hbK.trans (inv_smul_eq_mul_smul h2)
  exact ordAt_eq_ordAt_of_basis_eq_smul (MMP.Mori.PrimeDivisor.ord_mul_of_ne_zero P)
    (fun _ ha => MMP.Mori.PrimeDivisor.ord_algebraMap_of_isUnit P ha) hσk hσK bk bK _ hb hb' 1
    (MMP.Mori.ZTensorPower.basis bk 1 ()) (MMP.Mori.ZTensorPower.basis bK 1 ()) (by simp)

/-! ### Comparing log discrepancies through matching local data -/

/-- Along an isomorphism of fields, every generator of the top forms is a pull-back generator. -/
private lemma isPullbackGenerator_of_bijective_algebraMap {k K K' : Type*} [Field k]
    [PerfectField k] [Field K] [Field K'] [Algebra k K] [Algebra k K'] [Algebra K K']
    [IsScalarTower k K K'] [Algebra.EssFiniteType k K]
    (hf : Function.Bijective (algebraMap K K')) {d : ℕ} (hd : (Algebra.trdeg k K).toNat = d)
    {ω : ⋀[K]^d Ω[K⁄k]} (hω : Submodule.span K {ω} = ⊤) (h0 : ω ≠ 0) :
    MMP.Mori.IsPullbackGenerator K' ω := by
  have : Algebra.FormallyEtale K K' :=
    Algebra.FormallyEtale.of_equiv (AlgEquiv.ofBijective (Algebra.ofId K K') hf)
  have : FiniteDimensional K Ω[K⁄k] :=
    (trdeg_eq_finrank_kaehlerDifferential_sub_finrank_h1Cotangent k K).1
  obtain ⟨ω₁, hω₁⟩ := MMP.Mori.exists_isPullbackGenerator_of_formallyEtale (K' := K')
    ((MMP.Mori.finrank_kaehlerDifferential_eq_trdeg k K).trans hd)
  exact MMP.Threefold.Mori.Helpers.IsPullbackGenerator.of_span hω₁ hω h0

/-- A scalar `c` with `c • x = a` is nonzero when the image of `x` is, and that of `a` is a
nonzero multiple of a spanning vector. -/
private lemma ne_zero_of_map_eq_smul {F L M N G : Type*} [Field F] [Field L] [AddCommGroup M]
    [Module F M] [AddCommGroup N] [Module L N] [FunLike G M N] [AddMonoidHomClass G M N]
    (T : G) {c : F} {x a : M} {w s : N} {cE : L} (hc : c • x = a) (h1 : T a = w)
    (h2 : w = cE • s) (hcE : cE ≠ 0) (hs : Submodule.span L {s} = ⊤) (hx : T x ≠ 0) :
    c ≠ 0 := by
  rintro rfl
  rw [zero_smul] at hc
  subst hc
  rw [map_zero] at h1
  have hs0 : s = 0 := (smul_eq_zero.1 (h1.trans h2).symm).resolve_left hcE
  rw [hs0, Submodule.span_singleton_eq_bot.2 rfl] at hs
  apply hx
  have : T x ∈ (⊤ : Submodule L N) := trivial
  rw [← hs] at this
  exact (Submodule.mem_bot L).1 this

/-- If a nonzero vector `y` equals `cE • s`, then `cE ≠ 0`. -/
private lemma ne_zero_of_eq_smul {L N : Type*} [Field L] [AddCommGroup N] [Module L N]
    {y w s : N} {cE : L} (h1 : y = w) (h2 : w = cE • s) (hy : y ≠ 0) : cE ≠ 0 := by
  rintro rfl
  rw [zero_smul] at h2
  exact hy (h1.trans h2)

/-- If `c • x = a` and the image of `a` is `cE • s`, the image of `x` is `(c⁻¹ cE) • s`. -/
private lemma map_eq_inv_mul_smul {F L M N G : Type*} [Field F] [Field L] [Algebra F L]
    [AddCommGroup M] [Module F M] [AddCommGroup N] [Module L N] [Module F N]
    [IsScalarTower F L N] [FunLike G M N] [LinearMapClass G F M N]
    (T : G) {c : F} {x a : M} {w s : N} {cE : L} (hc0 : c ≠ 0) (hc : c • x = a)
    (h1 : T a = w) (h2 : w = cE • s) : T x = ((algebraMap F L c)⁻¹ * cE) • s := by
  have hx : x = c⁻¹ • a := by rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  rw [hx, map_smul, h1, h2, ← algebraMap_smul L c⁻¹, smul_smul, map_inv₀]

private lemma scheme_ord_one {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] (z : Y) :
    Y.ord (1 : Y.functionField) z = 0 := by
  have := Scheme.ord_mul (X := Y) (x := z) (one_ne_zero (α := Y.functionField)) one_ne_zero
  rw [mul_one] at this
  omega

/-- The order of a form along a prime divisor, through a basis of the top forms. -/
private lemma ordForm_eq_ord_repr_add_mul {k : Type u} [Field k] [PerfectField k] {Y : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [LocallyOfFiniteType sY] (Γ : MMP.Mori.PrimeDivisor Y) {n : ℕ}
    (hd : letI := MMP.Mori.functionFieldAlgebra sY; (Algebra.trdeg k Y.functionField).toNat = n)
    (b : letI := MMP.Mori.functionFieldAlgebra sY
      Module.Basis Unit Y.functionField (⋀[Y.functionField]^n Ω[Y.functionField⁄k]))
    {m : ℤ} (τ : MMP.Mori.RationalPluriForms sY n m) (hτ : τ ≠ 0) :
    letI := MMP.Mori.functionFieldAlgebra sY
    Γ.ordForm τ = Y.ord ((MMP.Mori.ZTensorPower.basis b m).repr τ ()) Γ.genericPoint +
      m * Γ.ordForm (@id (MMP.Mori.RationalPluriForms sY n 1)
          (MMP.Mori.ZTensorPower.basis b 1 ())) := by
  letI := MMP.Mori.functionFieldAlgebra sY
  obtain ⟨N, hN⟩ := Γ.exists_ordForm_eq_ord_add_mul hd b
  have h1 := hN 1 (MMP.Mori.ZTensorPower.basis b 1 ())
    ((MMP.Mori.ZTensorPower.basis b 1).ne_zero ())
  rw [Module.Basis.repr_self, Finsupp.single_eq_same, scheme_ord_one] at h1
  dsimp only [id]
  rw [hN m τ hτ, h1]
  ring

/-- The order of a pulled-back form along a divisor over `Y`, through a basis of the top
forms. -/
private lemma ordPullback_eq_ord_repr_add_mul {k : Type u} [Field k] [PerfectField k]
    {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] (hY : IsNormalVariety k sY) {n : ℕ}
    (hn : topologicalKrullDim Y = n) (D : DivisorOver k sY)
    (b : letI := MMP.Mori.functionFieldAlgebra sY
      Module.Basis Unit Y.functionField (⋀[Y.functionField]^n Ω[Y.functionField⁄k]))
    {m : ℤ} (τ : MMP.Mori.RationalPluriForms sY n m) (hτ : τ ≠ 0) :
    letI := MMP.Mori.functionFieldAlgebra sY
    haveI := D.isIntegral
    haveI := D.isDominant
    haveI := D.isLocallyNoetherian
    D.ordPullback τ =
      D.Y.ord (functionFieldMap D.f ((MMP.Mori.ZTensorPower.basis b m).repr τ ()))
        D.E.genericPoint +
      m * D.ordPullback (@id (MMP.Mori.RationalPluriForms sY n 1)
          (MMP.Mori.ZTensorPower.basis b 1 ())) := by
  letI := MMP.Mori.functionFieldAlgebra sY
  haveI := D.isIntegral
  haveI := D.isDominant
  haveI := D.isLocallyNoetherian
  obtain ⟨b₀, N, hN⟩ := D.exists_ordPullback_eq hY hn
  set c := b₀.repr (b ()) () with hcdef
  have hc : b () = c • b₀ () := (MMP.Mori.basis_unit_repr_smul b₀ (b ())).symm
  have hc0 : c ≠ 0 := by
    intro h
    exact b.ne_zero () (by rw [hc, h, zero_smul])
  have hfc : functionFieldMap D.f c ≠ 0 := (map_ne_zero _).2 hc0
  have key : ∀ (m : ℤ) (τ : MMP.Mori.RationalPluriForms sY n m), τ ≠ 0 →
      D.ordPullback τ =
        D.Y.ord (functionFieldMap D.f ((MMP.Mori.ZTensorPower.basis b m).repr τ ()))
          D.E.genericPoint + m * (D.Y.ord (functionFieldMap D.f c) D.E.genericPoint + N) := by
    intro m τ hτ
    have hr := MMP.Mori.repr_ne_zero_of_ne_zero b hτ
    have hrepr : (MMP.Mori.ZTensorPower.basis b₀ m).repr τ () =
        c ^ m * (MMP.Mori.ZTensorPower.basis b m).repr τ () := by
      rw [MMP.Mori.ZTensorPower.basis_repr_of_eq_smul hc m τ,
        mul_inv_cancel_left₀ (zpow_ne_zero m hc0)]
    rw [hN m τ hτ, hrepr, map_mul, map_zpow₀,
      Scheme.ord_mul (zpow_ne_zero _ hfc) ((map_ne_zero _).2 hr), MMP.Mori.ord_zpow _ hfc]
    ring
  dsimp only [id]
  rw [key m τ hτ, key 1 _ ((MMP.Mori.ZTensorPower.basis b 1).ne_zero ())]
  simp only [Module.Basis.repr_self, Finsupp.single_eq_same, map_one, scheme_ord_one]
  ring

/-- **Equal log discrepancies from matching local data.** -/
private theorem isLogDiscrepancy_iff_of_ordForm_eq {k K : Type u} [Field k] [CharZero k]
    [Field K] [CharZero K]
    {S U : Scheme.{u}} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    [IsIntegral U] [IsLocallyNoetherian U] [IsNormal U]
    (sS : S ⟶ Spec (.of K)) (sU : U ⟶ Spec (.of k)) (ι : S ⟶ U) [IsDominant ι] {n n' : ℕ}
    (hnS : topologicalKrullDim S = n) (hnU : topologicalKrullDim U = n')
    {BS : QDivisor S} {BU : QDivisor U} (hBS : MMP.Mori.IsPair sS BS)
    (hBU : MMP.Mori.IsPair sU BU)
    (D : DivisorOver K sS) (D' : DivisorOver k sU) (hDp : IsProper D.f) (hD'p : IsProper D'.f)
    (bS : letI := MMP.Mori.functionFieldAlgebra sS
      Module.Basis Unit S.functionField (⋀[S.functionField]^n Ω[S.functionField⁄K]))
    (bU : letI := MMP.Mori.functionFieldAlgebra sU
      Module.Basis Unit U.functionField (⋀[U.functionField]^n' Ω[U.functionField⁄k]))
    (hP : letI := MMP.Mori.functionFieldAlgebra sS; letI := MMP.Mori.functionFieldAlgebra sU;
      ∀ P : MMP.Mori.PrimeDivisor S, D.f D.E.genericPoint ∈ P.support →
      ∃ Γ : MMP.Mori.PrimeDivisor U, D'.f D'.E.genericPoint ∈ Γ.support ∧
        P.ordForm (@id (MMP.Mori.RationalPluriForms sS n 1) (MMP.Mori.ZTensorPower.basis bS 1 ())) =
          Γ.ordForm (@id (MMP.Mori.RationalPluriForms sU n' 1)
              (MMP.Mori.ZTensorPower.basis bU 1 ())) ∧
        BS.coeff P = BU.coeff Γ ∧
        ∀ g : U.functionField, g ≠ 0 →
          S.ord (functionFieldMap ι g) P.genericPoint = U.ord g Γ.genericPoint)
    (hE : letI := MMP.Mori.functionFieldAlgebra sS; letI := MMP.Mori.functionFieldAlgebra sU;
      D.ordPullback (@id (MMP.Mori.RationalPluriForms sS n 1)
          (MMP.Mori.ZTensorPower.basis bS 1 ())) =
      D'.ordPullback (@id (MMP.Mori.RationalPluriForms sU n' 1)
          (MMP.Mori.ZTensorPower.basis bU 1 ())))
    (hv : haveI := D.isIntegral; haveI := D.isDominant; haveI := D'.isIntegral;
      haveI := D'.isDominant; haveI := D.isLocallyNoetherian; haveI := D'.isLocallyNoetherian;
      ∀ g : U.functionField, g ≠ 0 →
        D.Y.ord (functionFieldMap D.f (functionFieldMap ι g)) D.E.genericPoint =
          D'.Y.ord (functionFieldMap D'.f g) D'.E.genericPoint) :
    ∀ a : ℝ, MMP.Intersection.IsLogDiscrepancy sS n (QDivisor.toRDivisor BS) D a ↔
      MMP.Intersection.IsLogDiscrepancy sU n' (QDivisor.toRDivisor BU) D' a := by
  classical
  intro a
  obtain ⟨hvS, nS, KS, hKS, -⟩ := id hBS
  obtain ⟨hvU, nU, KU, hKU, -⟩ := id hBU
  have hnS' : nS = n := by
    have := hKS.topologicalKrullDim_eq.symm.trans hnS
    exact_mod_cast this
  have hnU' : nU = n' := by
    have := hKU.topologicalKrullDim_eq.symm.trans hnU
    exact_mod_cast this
  subst hnS' hnU'
  obtain ⟨aS, haS⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hBS hKS D
  obtain ⟨aU, haU⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hBU hKU D'
  rw [MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy haS,
    MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy haU]
  suffices h : aS = aU by
    rw [h]
    exact ⟨fun h => ⟨hD'p, h.2⟩, fun h => ⟨hDp, h.2⟩⟩
  obtain ⟨-, -, mS, hmS, -, VS, hVS, τS, hτS, hmaS⟩ := haS
  obtain ⟨-, -, mU, hmU, -, VU, hVU, τU, hτU, hmaU⟩ := haU
  haveI := D.isIntegral
  haveI := D.isLocallyNoetherian
  haveI := D.isNormal
  haveI := D.isDominant
  haveI := D'.isIntegral
  haveI := D'.isLocallyNoetherian
  haveI := D'.isNormal
  haveI := D'.isDominant
  haveI : LocallyOfFiniteType sS := hvS.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType sU := hvU.1.toLocallyOfFiniteType
  letI := MMP.Mori.functionFieldAlgebra sS
  letI := MMP.Mori.functionFieldAlgebra sU
  have hdS := MMP.Mori.toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sS) hnS
  have hdU := MMP.Mori.toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sU) hnU
  set fS := (MMP.Mori.ZTensorPower.basis bS mS).repr τS () with hfSdef
  set fU := (MMP.Mori.ZTensorPower.basis bU mU).repr τU () with hfUdef
  have hfS : fS ≠ 0 := MMP.Mori.repr_ne_zero_of_ne_zero bS hτS.1
  have hfU : fU ≠ 0 := MMP.Mori.repr_ne_zero_of_ne_zero bU hτU.1
  have hιfU : functionFieldMap ι fU ≠ 0 := (map_ne_zero _).2 hfU
  have hsum := MMP.Threefold.Bridges.sum_ord_functionFieldMap_eq_zero (f := D.f) D.E
    ![fS, functionFieldMap ι fU] (fun j => by fin_cases j; exacts [hfS, hιfU])
    ![(mU : ℝ), -(mS : ℝ)] (fun P hPm => by
      obtain ⟨Γ, hΓ, hN, hB, hord⟩ := hP P hPm
      have e1 := ordForm_eq_ord_repr_add_mul P hdS bS τS hτS.1
      have e2 := hτS.2 P ⟨_, hPm, hVS⟩
      have e3 := ordForm_eq_ord_repr_add_mul Γ hdU bU τU hτU.1
      have e4 := hτU.2 Γ ⟨_, hΓ, hVU⟩
      rw [hN] at e1
      rw [hB] at e2
      have hq : (S.ord fS P.genericPoint : ℚ) * mU -
          (U.ord fU Γ.genericPoint : ℚ) * mS = 0 := by
        have e1' : (P.ordForm τS : ℚ) = S.ord fS P.genericPoint +
            (mS : ℚ) * Γ.ordForm (@id (MMP.Mori.RationalPluriForms sU _ 1)
                (MMP.Mori.ZTensorPower.basis bU 1 ())) := by
          exact_mod_cast e1
        have e3' : (Γ.ordForm τU : ℚ) = U.ord fU Γ.genericPoint +
            (mU : ℚ) * Γ.ordForm (@id (MMP.Mori.RationalPluriForms sU _ 1)
                (MMP.Mori.ZTensorPower.basis bU 1 ())) := by
          exact_mod_cast e3
        linear_combination (-(mU : ℚ)) * e1' + (mS : ℚ) * e3' + (mU : ℚ) * e2 - (mS : ℚ) * e4
      have hr : (S.ord fS P.genericPoint : ℝ) * mU -
          (U.ord fU Γ.genericPoint : ℝ) * mS = 0 := by exact_mod_cast hq
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      rw [hord fU hfU]
      linear_combination hr)
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons] at hsum
  rw [hv fU hfU] at hsum
  have f1 := ordPullback_eq_ord_repr_add_mul hvS hnS D bS τS hτS.1
  have f2 := ordPullback_eq_ord_repr_add_mul hvU hnU D' bU τU hτU.1
  rw [hE] at f1
  have hsQ : (D.Y.ord (functionFieldMap D.f fS) D.E.genericPoint : ℚ) * mU -
      (D'.Y.ord (functionFieldMap D'.f fU) D'.E.genericPoint : ℚ) * mS = 0 := by
    have : (D.Y.ord (functionFieldMap D.f fS) D.E.genericPoint : ℝ) * mU -
        (D'.Y.ord (functionFieldMap D'.f fU) D'.E.genericPoint : ℝ) * mS = 0 := by
      linear_combination hsum
    exact_mod_cast this
  have f1' : (D.ordPullback τS : ℚ) = D.Y.ord (functionFieldMap D.f fS) D.E.genericPoint +
      (mS : ℚ) * D'.ordPullback (@id (MMP.Mori.RationalPluriForms sU _ 1)
          (MMP.Mori.ZTensorPower.basis bU 1 ())) := by exact_mod_cast f1
  have f2' : (D'.ordPullback τU : ℚ) = D'.Y.ord (functionFieldMap D'.f fU) D'.E.genericPoint +
      (mU : ℚ) * D'.ordPullback (@id (MMP.Mori.RationalPluriForms sU _ 1)
          (MMP.Mori.ZTensorPower.basis bU 1 ())) := by exact_mod_cast f2
  have hm0 : ((mS : ℚ) * mU) ≠ 0 := by positivity
  have hfin : ((mS : ℚ) * mU) * (aS - aU) = 0 := by
    linear_combination (mU : ℚ) * hmaS - (mS : ℚ) * hmaU + (mU : ℚ) * f1' - (mS : ℚ) * f2' + hsQ
  have := (mul_eq_zero.1 hfin).resolve_left hm0
  linarith

/-- The pull-back of `b^{⊗1}` along the pull-back generator `b ()`. -/
private lemma pullbackForms_basis_one {k K K' : Type*} [CommRing k] [Field K] [Field K']
    [Algebra k K] [Algebra k K'] [Algebra K K'] [IsScalarTower k K K'] {d : ℕ}
    {ω : ⋀[K]^d Ω[K⁄k]} (hω : MMP.Mori.IsPullbackGenerator K' ω)
    (b : Module.Basis Unit K (⋀[K]^d Ω[K⁄k])) (hb : b () = ω) :
    MMP.Mori.pullbackForms (K' := K') 1 (MMP.Mori.ZTensorPower.basis b 1 ()) =
      MMP.Mori.ZTensorPower.basis (MMP.Mori.basisOfSpanSingleton hω.2.1 hω.2.2) 1 () := by
  have hb1 : MMP.Mori.basisOfSpanSingleton hω.1 hω.ne_zero = b :=
    Module.Basis.eq_of_apply_eq fun _ => (MMP.Mori.basisOfSpanSingleton_apply _ _ _).trans hb.symm
  rw [MMP.Mori.pullbackForms_eq hω, MMP.Mori.pullbackFormsAlong, hb1]
  simp

/-- The structure morphism to `k` of a scheme over the generic surface factors through `K`. -/
private lemma comp_genι_comp_eq {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    {U : X.Opens} (hU : IsAffineOpen U) {d : ℕ} (t : Fin d → Γ(X, U)) {Y : Scheme.{u}}
    (f : Y ⟶ Spec (genRing sX t)) :
    f ≫ genι sX t hU ≫ U.ι ≫ sX =
      (f ≫ genStructure sX t) ≫ Spec.map (CommRingCat.ofHom (algebraMap k (genField k d))) := by
  rw [genι_comp_eq, Category.assoc]

/-- The variables `tᵢ`, as functions on `U`, pull back along `ι = genι` to `tᵢ ∈ K ⊆ K(S)`. -/
private lemma functionFieldMap_genι_germ_tU {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) {U : X.Opens} (hU : IsAffineOpen U) [IsIntegral U] {d : ℕ}
    (t : Fin d → Γ(X, U)) [IsIntegral (Spec (genRing sX t))] [IsDominant (genι sX t hU)]
    (i : Fin d) :
    letI := MMP.Mori.functionFieldAlgebra (genStructure sX t)
    functionFieldMap (genι sX t hU) (U.toScheme.germToFunctionField ⊤
      (hU.isoSpec.hom.appTop.hom ((Scheme.ΓSpecIso Γ(X, U)).inv.hom (t i)))) =
      algebraMap (genField k d) (Spec (genRing sX t)).functionField
        (algebraMap (MvPolynomial (Fin d) k) (genField k d) (.X i)) := by
  letI := MMP.Mori.functionFieldAlgebra (genStructure sX t)
  have htU : (genι sX t hU).appTop.hom
      (hU.isoSpec.hom.appTop.hom ((Scheme.ΓSpecIso Γ(X, U)).inv.hom (t i))) =
      (Scheme.ΓSpecIso (genRing sX t)).inv.hom
        (algebraMap Γ(X, U) (Localization (genSubmonoid sX t)) (t i)) := by
    change (hU.isoSpec.inv.appTop ≫ (Spec.map _).appTop).hom
      (hU.isoSpec.hom.appTop.hom ((Scheme.ΓSpecIso Γ(X, U)).inv.hom (t i))) = _
    rw [CommRingCat.comp_apply, ← CommRingCat.comp_apply hU.isoSpec.hom.appTop,
      ← Scheme.Hom.comp_appTop, Iso.inv_hom_id, Scheme.Hom.id_appTop, CommRingCat.id_apply,
      ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]
    rfl
  rw [functionFieldMap_germToFunctionField_top, htU]
  symm
  change (Spec (genRing sX t)).presheaf.germ ⊤ _ _ ((genStructure sX t).appTop.hom
    ((Scheme.ΓSpecIso (.of (genField k d))).inv.hom _)) = _
  rw [← CommRingCat.comp_apply ((Scheme.ΓSpecIso _).inv), genStructure,
    ← Scheme.ΓSpecIso_inv_naturality]
  letI := sectionAlgebra sX U
  change (Spec (genRing sX t)).presheaf.germ ⊤ _ _ ((Scheme.ΓSpecIso (genRing sX t)).inv.hom
    (fracToLoc k t _)) = _
  rw [fracToLoc_algebraMap, MvPolynomial.aeval_X]
  rfl

/-- Elements whose images under an algebra map are algebraically independent elements of a
subfield are algebraically independent. -/
private lemma algebraicIndependent_of_algHom_apply_eq {k R K L : Type*} [Field k] [CommRing R]
    [Algebra k R] [Field K] [Algebra k K] [Field L] [Algebra k L] [Algebra K L]
    [IsScalarTower k K L] {d : ℕ} (f : R →ₐ[k] L) {t : Fin d → R} {s : Fin d → K}
    (hs : AlgebraicIndependent k s) (h : ∀ i, f (t i) = algebraMap K L (s i)) :
    AlgebraicIndependent k t := by
  refine AlgebraicIndependent.of_comp f ?_
  have : f ∘ t = algebraMap K L ∘ s := funext h
  rw [this]
  exact hs.map' (f := IsScalarTower.toAlgHom k K L) (algebraMap K L).injective

/-- **Prime divisors with the same valuation have isomorphic local rings.** If the function
fields of `Y'` and `Y` are identified with a field `L` (by `f'` and `θ`) so that the valuations of
prime divisors `E'` and `E` agree on `L`, then the identification `e : k(Y') → k(Y)` restricts to
an isomorphism `𝒪_{Y',E'} ≅ 𝒪_{Y,E}` of the valuation rings. -/
private lemma exists_ringHom_localRing_of_valuation_eq {L : Type*} [Field L] {Y Y' : Scheme.{u}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y'] [IsLocallyNoetherian Y']
    [IsNormal Y'] (E : MMP.Mori.PrimeDivisor Y) (E' : MMP.Mori.PrimeDivisor Y')
    (θ : L →+* Y.functionField) (hθ : Function.Surjective θ) (f' : L →+* Y'.functionField)
    (hf' : Function.Bijective f')
    (hv : ∀ g, E.divisorialValuation (θ g) = E'.divisorialValuation (f' g)) :
    ∃ (e : Y'.functionField →+* Y.functionField) (ψ : E'.localRing →+* E.localRing),
      (∀ g, e (f' g) = θ g) ∧ Function.Surjective e ∧
      (∀ y, E.divisorialValuation (e y) = E'.divisorialValuation y) ∧ Function.Bijective ψ ∧
      ∀ a, algebraMap E.localRing Y.functionField (ψ a) =
        e (algebraMap E'.localRing Y'.functionField a) := by
  let f'e := RingEquiv.ofBijective f' hf'
  let e : Y'.functionField →+* Y.functionField := θ.comp (f'e.symm : _ →+* _)
  have he : ∀ g, e (f' g) = θ g := fun g => congrArg θ (f'e.symm_apply_apply g)
  have hesurj : Function.Surjective e := fun y => by
    obtain ⟨g, rfl⟩ := hθ y
    exact ⟨_, he g⟩
  have hval : ∀ y, E.divisorialValuation (e y) = E'.divisorialValuation y := fun y => by
    obtain ⟨g, rfl⟩ := hf'.2 y
    rw [he, hv]
  obtain ⟨ψ, hψb, hψ⟩ := MMP.Threefold.Mori.ModelIndependence.exists_ringHom_bijective_of_range e
    (fun a₁ => (E.divisorialValuation_le_one_iff _).1
      (by rw [hval]; exact (E'.divisorialValuation_le_one_iff _).2 ⟨a₁, rfl⟩))
    (fun a₂ => by
      obtain ⟨y, hy⟩ := hesurj (algebraMap _ Y.functionField a₂)
      obtain ⟨a₁, rfl⟩ := (E'.divisorialValuation_le_one_iff y).1
        (by rw [← hval, hy]; exact (E.divisorialValuation_le_one_iff _).2 ⟨a₂, rfl⟩)
      exact ⟨a₁, hy⟩)
  exact ⟨e, ψ, he, hesurj, hval, hψb, hψ⟩

/-- **The determinant comparison at a divisor over the generic surface.** For a divisor `E` over
the generic surface `S` and a divisor `F` over `U` with the same valuation,
`𝒪_{D'.Y,F} ≅ 𝒪_{D.Y,E}` by an isomorphism compatible with `k` and sending `tᵢ` to `tᵢ ∈ K`; so the
forms `dt ∧ η` (over `k`) and `η̄` (over `K`) on `K(D.Y)` are the same multiple of the images of
generators of `Ω^{d+2}_{𝒪_E/k}` and `Ω²_{𝒪_E/K}` (`exists_eq_smul_topFormsMap_of_ringEquiv`). -/
private theorem exists_eq_smul_topFormsMap_genSurface_divisorOver
    {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {B : QDivisor X} (hB : MMP.Fourfold.IsPair sX B) {x : X}
    {U : X.Opens} (hU : IsAffineOpen U) (hxU : x ∈ U) [IsIntegral U] [IsLocallyNoetherian U]
    [IsNormal U] {d : ℕ} (t : Fin d → Γ(X, U))
    [IsIntegral (Spec (genRing sX t))] [IsLocallyNoetherian (Spec (genRing sX t))]
    [IsNormal (Spec (genRing sX t))] [IsDominant (genι sX t hU)]
    (D : DivisorOver (genField k d) (genStructure sX t))
    (D' : DivisorOver k (U.ι ≫ sX))
    (hD'v : D'.valuation = D.valuation.comap (functionFieldMap (genι sX t hU)))
    (hdimX : topologicalKrullDim X = (d + 2 : ℕ)) :
    haveI := D.isIntegral
    haveI := D.isLocallyNoetherian
    haveI := D.isDominant
    letI := MMP.Mori.functionFieldAlgebra (genι sX t hU ≫ U.ι ≫ sX)
    letI := MMP.Mori.functionFieldAlgebra (D.f ≫ genι sX t hU ≫ U.ι ≫ sX)
    letI := MMP.Mori.functionFieldAlgebra (D.f ≫ genStructure sX t)
    letI := MMP.Mori.functionFieldMapAlgebra D.f
    haveI := MMP.Mori.isScalarTower_functionFieldMap (genι sX t hU ≫ U.ι ≫ sX) D.f
    haveI := isScalarTower_stalkAlgebra_comp (D.f ≫ genStructure sX t)
      (D.f ≫ genι sX t hU ≫ U.ι ≫ sX) (comp_genι_comp_eq sX hU t D.f) (genericPoint D.Y)
    letI := MMP.Mori.stalkAlgebra (D.f ≫ genι sX t hU ≫ U.ι ≫ sX) D.E.genericPoint
    letI := MMP.Mori.stalkAlgebra (D.f ≫ genStructure sX t) D.E.genericPoint
    haveI := isScalarTower_stalkAlgebra_comp (D.f ≫ genStructure sX t)
      (D.f ≫ genι sX t hU ≫ U.ι ≫ sX) (comp_genι_comp_eq sX hU t D.f) D.E.genericPoint
    haveI := MMP.Mori.isScalarTower_stalk_functionField (D.f ≫ genι sX t hU ≫ U.ι ≫ sX)
      D.E.genericPoint
    haveI := MMP.Mori.isScalarTower_stalk_functionField (D.f ≫ genStructure sX t)
      D.E.genericPoint
    ∀ η : Fin 2 → Ω[(Spec (genRing sX t)).functionField⁄k],
      ∃ (σk : ⋀[D.E.localRing]^(d + 2) Ω[D.E.localRing⁄k])
        (σK : ⋀[D.E.localRing]^2 Ω[D.E.localRing⁄genField k d]),
        Submodule.span D.E.localRing {σk} = ⊤ ∧ Submodule.span D.E.localRing {σK} = ⊤ ∧
        ∃ cE : D.Y.functionField,
          exteriorPower.ιMulti D.Y.functionField (d + 2) (Fin.append (fun i =>
            KaehlerDifferential.D k D.Y.functionField (algebraMap (genField k d) D.Y.functionField
              (algebraMap (MvPolynomial (Fin d) k) (genField k d) (.X i))))
            (fun j => KaehlerDifferential.map k k (Spec (genRing sX t)).functionField
              D.Y.functionField (η j))) =
            cE • MMP.Mori.topFormsMap k D.E.localRing D.Y.functionField (d + 2) σk ∧
          exteriorPower.ιMulti D.Y.functionField 2 (fun j =>
            KaehlerDifferential.map k (genField k d) D.Y.functionField D.Y.functionField
              (KaehlerDifferential.map k k (Spec (genRing sX t)).functionField
                D.Y.functionField (η j))) =
            cE • MMP.Mori.topFormsMap (genField k d) D.E.localRing D.Y.functionField 2 σK := by
  intro η
  classical
  haveI := hB.charZero
  haveI : CharZero (genField k d) :=
    charZero_of_injective_algebraMap (algebraMap k (genField k d)).injective
  have hXv : IsNormalVariety k sX := hB.isPair.1
  haveI : LocallyOfFiniteType sX := hXv.1.toLocallyOfFiniteType
  haveI : Nonempty U := ⟨⟨x, hxU⟩⟩
  haveI : IsDominant U.ι := isDominant_opens_ι U
  have hUv := isNormalVariety_ι hXv U
  haveI : LocallyOfFiniteType (U.ι ≫ sX) := hUv.1.toLocallyOfFiniteType
  have hdimU : topologicalKrullDim U = (d + 2 : ℕ) :=
      (topologicalKrullDim_opens_eq hXv U).trans hdimX
  haveI : LocallyOfFiniteType (genStructure sX t) := locallyOfFiniteType_genStructure sX t hU
  have hbijι := bijective_functionFieldMap_genι sX t hU
  have hdU := MMP.Mori.toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := U.ι ≫ sX) hdimU
  letI := MMP.Mori.functionFieldAlgebra (U.ι ≫ sX)
  letI := MMP.Mori.functionFieldAlgebra (genι sX t hU ≫ U.ι ≫ sX)
  letI := MMP.Mori.functionFieldMapAlgebra (genι sX t hU)
  haveI := MMP.Mori.isScalarTower_functionFieldMap (U.ι ≫ sX) (genι sX t hU)
  letI := MMP.Mori.functionFieldAlgebra (genStructure sX t)
  haveI := isScalarTower_stalkAlgebra_comp (genStructure sX t) (genι sX t hU ≫ U.ι ≫ sX)
    (genι_comp_eq sX t hU) (genericPoint (Spec (genRing sX t)))
  -- the divisors `E` over `S` and `F` over `U`, and their common local ring
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  haveI : LocallyOfFiniteType (D.f ≫ genStructure sX t) := D.isNormalVariety.1.toLocallyOfFiniteType
  haveI := D'.isIntegral
  haveI := D'.isNormal
  haveI := D'.isLocallyNoetherian
  haveI := D'.isDominant
  haveI : LocallyOfFiniteType (D'.f ≫ U.ι ≫ sX) := D'.isNormalVariety.1.toLocallyOfFiniteType
  have hbD := D.isBirationalMorphism.functionFieldMap_bijective
  have hbD' := D'.isBirationalMorphism.functionFieldMap_bijective
  let θ : U.toScheme.functionField →+* D.Y.functionField :=
    (functionFieldMap D.f).comp (functionFieldMap (genι sX t hU))
  have hθ : Function.Bijective θ := hbD.comp hbijι
  obtain ⟨e', ψ, he', he'surj, hval, hψb, hψ⟩ := exists_ringHom_localRing_of_valuation_eq D.E D'.E
    θ hθ.2 (functionFieldMap D'.f) hbD' fun g => congrArg (fun w => w g) hD'v.symm
  -- the structures over `k` and `K` on `D.Y`
  letI := MMP.Mori.functionFieldAlgebra (D.f ≫ genι sX t hU ≫ U.ι ≫ sX)
  letI := MMP.Mori.functionFieldAlgebra (D.f ≫ genStructure sX t)
  letI := MMP.Mori.functionFieldMapAlgebra D.f
  letI := MMP.Mori.functionFieldAlgebra (D'.f ≫ U.ι ≫ sX)
  letI := MMP.Mori.functionFieldMapAlgebra D'.f
  haveI := MMP.Mori.isScalarTower_functionFieldMap (genι sX t hU ≫ U.ι ≫ sX) D.f
  haveI := MMP.Mori.isScalarTower_functionFieldMap (genStructure sX t) D.f
  haveI := MMP.Mori.isScalarTower_functionFieldMap (U.ι ≫ sX) D'.f
  haveI := isScalarTower_stalkAlgebra_comp (D.f ≫ genStructure sX t) _
    (comp_genι_comp_eq sX hU t D.f) (genericPoint D.Y)
  -- the variables `tᵢ` on `U`, on `D'.Y` and in the function fields
  let tU : Fin d → Γ(U.toScheme, ⊤) := fun i =>
    hU.isoSpec.hom.appTop.hom ((Scheme.ΓSpecIso Γ(X, U)).inv.hom (t i))
  have hG1 : ∀ i, θ (U.toScheme.germToFunctionField ⊤ (tU i)) =
      algebraMap (genField k d) D.Y.functionField
        (algebraMap (MvPolynomial (Fin d) k) (genField k d) (.X i)) := fun i => by
    change functionFieldMap D.f (functionFieldMap (genι sX t hU)
      (U.toScheme.germToFunctionField ⊤ (tU i))) = _
    rw [show functionFieldMap (genι sX t hU) (U.toScheme.germToFunctionField ⊤ (tU i)) =
        algebraMap (genField k d) (Spec (genRing sX t)).functionField
          (algebraMap (MvPolynomial (Fin d) k) (genField k d) (.X i)) from
        functionFieldMap_genι_germ_tU sX hU t i,
      IsScalarTower.algebraMap_apply (genField k d) (Spec (genRing sX t)).functionField
        D.Y.functionField]
    rfl
  let t' : Fin d → Γ(D'.Y, ⊤) := fun i => D'.f.appTop.hom (tU i)
  have hG2 : ∀ i, e' (D'.Y.germToFunctionField ⊤ (t' i)) =
      algebraMap (genField k d) D.Y.functionField
        (algebraMap (MvPolynomial (Fin d) k) (genField k d) (.X i)) := fun i => by
    rw [← functionFieldMap_germToFunctionField_top, he', hG1]
  have hG3 : ∀ c : k, e' (algebraMap k D'.Y.functionField c) = algebraMap k D.Y.functionField c :=
    fun c => by
      rw [IsScalarTower.algebraMap_apply k U.toScheme.functionField D'.Y.functionField]
      change e' (functionFieldMap D'.f _) = _
      rw [he', IsScalarTower.algebraMap_apply k (Spec (genRing sX t)).functionField
        D.Y.functionField, IsScalarTower.algebraMap_apply k U.toScheme.functionField
        (Spec (genRing sX t)).functionField]
      rfl
  have hn : topologicalKrullDim D'.Y = (d + 2 : ℕ) := by
    rw [← MMP.Mori.toENat_trdeg_functionField (sX := D'.f ≫ U.ι ≫ sX),
      ← MMP.Mori.trdeg_functionField_eq_of_bijective (U.ι ≫ sX) D'.f hbD',
      MMP.Mori.toENat_trdeg_functionField (sX := U.ι ≫ sX), hdimU]
  letI := sectionAlgebra (D'.f ≫ U.ι ≫ sX) ⊤
  haveI := MMP.Mori.isScalarTower_section_functionField (D'.f ≫ U.ι ≫ sX) (⊤ : D'.Y.Opens)
  let ek : D'.Y.functionField →ₐ[k] D.Y.functionField := { toRingHom := e', commutes' := hG3 }
  let gk : Γ(D'.Y, ⊤) →ₐ[k] D'.Y.functionField := IsScalarTower.toAlgHom k _ _
  have ht' : AlgebraicIndependent k t' :=
    algebraicIndependent_of_algHom_apply_eq (ek.comp gk) (isTranscendenceBasis_genField k d).1
      hG2
  -- the local rings of `E` over `k` and `K`, and the comparison at `E`
  letI := MMP.Mori.stalkAlgebra (D.f ≫ genι sX t hU ≫ U.ι ≫ sX) D.E.genericPoint
  letI := MMP.Mori.stalkAlgebra (D.f ≫ genStructure sX t) D.E.genericPoint
  haveI := isScalarTower_stalkAlgebra_comp (D.f ≫ genStructure sX t) _
    (comp_genι_comp_eq sX hU t D.f) D.E.genericPoint
  haveI := MMP.Mori.isScalarTower_stalk_functionField (D.f ≫ genι sX t hU ≫ U.ι ≫ sX)
    D.E.genericPoint
  haveI := MMP.Mori.isScalarTower_stalk_functionField (D.f ≫ genStructure sX t) D.E.genericPoint
  haveI := essFiniteType_stalkAlgebra (D.f ≫ genStructure sX t) D.E.genericPoint
  letI := MMP.Mori.stalkAlgebra (D'.f ≫ U.ι ≫ sX) D'.E.genericPoint
  haveI := MMP.Mori.isScalarTower_stalk_functionField (D'.f ≫ U.ι ≫ sX) D'.E.genericPoint
  let φ := RingEquiv.ofBijective ψ hψb
  have hφk : ∀ c : k, φ (algebraMap k D'.E.localRing c) = algebraMap k D.E.localRing c :=
    fun c => IsFractionRing.injective D.E.localRing D.Y.functionField (by
      change algebraMap _ _ (ψ _) = _
      rw [hψ, ← IsScalarTower.algebraMap_apply, hG3, ← IsScalarTower.algebraMap_apply])
  have hφt : ∀ i, φ (D'.Y.presheaf.germ ⊤ D'.E.genericPoint trivial (t' i)) =
      algebraMap (genField k d) D.E.localRing
        (algebraMap (MvPolynomial (Fin d) k) (genField k d) (.X i)) := fun i =>
    IsFractionRing.injective D.E.localRing D.Y.functionField (by
      change algebraMap _ _ (ψ _) = _
      rw [hψ, Scheme.algebraMap_germ_eq_germToFunctionField (X := D'.Y) (U := ⊤)
        (x := D'.E.genericPoint) (Opens.mem_top _), hG2,
        ← IsScalarTower.algebraMap_apply (genField k d) D.E.localRing D.Y.functionField])
  let ηDY : Fin 2 → Ω[D.Y.functionField⁄k] := fun j =>
    KaehlerDifferential.map k k (Spec (genRing sX t)).functionField D.Y.functionField (η j)
  exact exists_eq_smul_topFormsMap_of_ringEquiv
    (D'.f ≫ U.ι ≫ sX) D'.isNormalVariety hn t' ht' D'.E (genField k d) D.E.localRing φ hφk hφt
    D.Y.functionField ηDY

/-- **Transport of orders from `F` to `E`.** For a divisor `E` over the generic surface and a
divisor `F` over `U` with the same valuation (through `ι = genι`), the order along `F` of the
pull-back of a rational `(d + 2)`-form `ω` on `U` is the order along `E` of its pull-back along
`D.Y ⟶ S ⟶ U`: through the isomorphism `𝒪_{D'.Y,F} ≅ 𝒪_{D.Y,E}` of the valuation rings. -/
private theorem ordPullback_eq_ordForm_pullback_genSurface
    {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {B : QDivisor X} (hB : MMP.Fourfold.IsPair sX B) {x : X}
    {U : X.Opens} (hU : IsAffineOpen U) (hxU : x ∈ U) [IsIntegral U] [IsLocallyNoetherian U]
    [IsNormal U] {d : ℕ} (t : Fin d → Γ(X, U))
    [IsIntegral (Spec (genRing sX t))] [IsLocallyNoetherian (Spec (genRing sX t))]
    [IsNormal (Spec (genRing sX t))] [IsDominant (genι sX t hU)]
    (D : DivisorOver (genField k d) (genStructure sX t))
    (D' : DivisorOver k (U.ι ≫ sX))
    (hD'v : D'.valuation = D.valuation.comap (functionFieldMap (genι sX t hU)))
    (hdimX : topologicalKrullDim X = (d + 2 : ℕ)) :
    haveI := D.isIntegral
    haveI := D.isLocallyNoetherian
    haveI := D.isDominant
    ∀ ω : MMP.Mori.RationalPluriForms (U.ι ≫ sX) (d + 2) 1,
      D'.ordPullback ω = MMP.Mori.PrimeDivisor.ordForm (sX := D.f ≫ genι sX t hU ≫ U.ι ≫ sX) D.E
        (MMP.Mori.pullbackRationalPluriForms (genι sX t hU ≫ U.ι ≫ sX) D.f
          (MMP.Mori.pullbackRationalPluriForms (U.ι ≫ sX) (genι sX t hU) ω)) := by
  intro ω
  classical
  haveI := hB.charZero
  haveI : CharZero (genField k d) :=
    charZero_of_injective_algebraMap (algebraMap k (genField k d)).injective
  have hXv : IsNormalVariety k sX := hB.isPair.1
  haveI : LocallyOfFiniteType sX := hXv.1.toLocallyOfFiniteType
  haveI : Nonempty U := ⟨⟨x, hxU⟩⟩
  haveI : IsDominant U.ι := isDominant_opens_ι U
  have hUv := isNormalVariety_ι hXv U
  haveI : LocallyOfFiniteType (U.ι ≫ sX) := hUv.1.toLocallyOfFiniteType
  have hdimU : topologicalKrullDim U = (d + 2 : ℕ) :=
      (topologicalKrullDim_opens_eq hXv U).trans hdimX
  haveI : LocallyOfFiniteType (genStructure sX t) := locallyOfFiniteType_genStructure sX t hU
  have hbijι := bijective_functionFieldMap_genι sX t hU
  have hdU := MMP.Mori.toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := U.ι ≫ sX) hdimU
  letI := MMP.Mori.functionFieldAlgebra (U.ι ≫ sX)
  letI := MMP.Mori.functionFieldAlgebra (genι sX t hU ≫ U.ι ≫ sX)
  letI := MMP.Mori.functionFieldMapAlgebra (genι sX t hU)
  haveI := MMP.Mori.isScalarTower_functionFieldMap (U.ι ≫ sX) (genι sX t hU)
  -- the divisors `E` over `S` and `F` over `U`, and their common local ring
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  haveI : LocallyOfFiniteType (D.f ≫ genStructure sX t) := D.isNormalVariety.1.toLocallyOfFiniteType
  haveI := D'.isIntegral
  haveI := D'.isNormal
  haveI := D'.isLocallyNoetherian
  haveI := D'.isDominant
  haveI : LocallyOfFiniteType (D'.f ≫ U.ι ≫ sX) := D'.isNormalVariety.1.toLocallyOfFiniteType
  have hbD := D.isBirationalMorphism.functionFieldMap_bijective
  have hbD' := D'.isBirationalMorphism.functionFieldMap_bijective
  let θ : U.toScheme.functionField →+* D.Y.functionField :=
    (functionFieldMap D.f).comp (functionFieldMap (genι sX t hU))
  have hθ : Function.Bijective θ := hbD.comp hbijι
  obtain ⟨e', ψ, he', he'surj, hval, hψb, hψ⟩ := exists_ringHom_localRing_of_valuation_eq D.E D'.E
    θ hθ.2 (functionFieldMap D'.f) hbD' fun g => congrArg (fun w => w g) hD'v.symm
  -- the structures over `k` and `K` on `D.Y`
  letI := MMP.Mori.functionFieldAlgebra (D.f ≫ genι sX t hU ≫ U.ι ≫ sX)
  letI := MMP.Mori.functionFieldAlgebra (D.f ≫ genStructure sX t)
  letI := MMP.Mori.functionFieldMapAlgebra D.f
  letI := MMP.Mori.functionFieldAlgebra (D'.f ≫ U.ι ≫ sX)
  letI := MMP.Mori.functionFieldMapAlgebra D'.f
  haveI := MMP.Mori.isScalarTower_functionFieldMap (genι sX t hU ≫ U.ι ≫ sX) D.f
  haveI := MMP.Mori.isScalarTower_functionFieldMap (U.ι ≫ sX) D'.f
  have hG3 : ∀ c : k, e' (algebraMap k D'.Y.functionField c) = algebraMap k D.Y.functionField c :=
    fun c => by
      rw [IsScalarTower.algebraMap_apply k U.toScheme.functionField D'.Y.functionField]
      change e' (functionFieldMap D'.f _) = _
      rw [he', IsScalarTower.algebraMap_apply k (Spec (genRing sX t)).functionField
        D.Y.functionField, IsScalarTower.algebraMap_apply k U.toScheme.functionField
        (Spec (genRing sX t)).functionField]
      rfl
  have hn : topologicalKrullDim D'.Y = (d + 2 : ℕ) := by
    rw [← MMP.Mori.toENat_trdeg_functionField (sX := D'.f ≫ U.ι ≫ sX),
      ← MMP.Mori.trdeg_functionField_eq_of_bijective (U.ι ≫ sX) D'.f hbD',
      MMP.Mori.toENat_trdeg_functionField (sX := U.ι ≫ sX), hdimU]
  letI := MMP.Mori.stalkAlgebra (D.f ≫ genι sX t hU ≫ U.ι ≫ sX) D.E.genericPoint
  haveI := MMP.Mori.isScalarTower_stalk_functionField (D.f ≫ genι sX t hU ≫ U.ι ≫ sX)
    D.E.genericPoint
  letI := MMP.Mori.stalkAlgebra (D'.f ≫ U.ι ≫ sX) D'.E.genericPoint
  haveI := MMP.Mori.isScalarTower_stalk_functionField (D'.f ≫ U.ι ≫ sX) D'.E.genericPoint
  have hφk : ∀ c : k, ψ (algebraMap k D'.E.localRing c) = algebraMap k D.E.localRing c :=
    fun c => IsFractionRing.injective D.E.localRing D.Y.functionField (by
      rw [hψ, ← IsScalarTower.algebraMap_apply, hG3, ← IsScalarTower.algebraMap_apply])
  have hord : ∀ y : D'.Y.functionField,
      D.Y.ord (e' y) D.E.genericPoint = D'.Y.ord y D'.E.genericPoint := by
    intro y
    by_cases hy : y = 0
    · subst hy
      simp [Scheme.ord_zero]
    · have hey : e' y ≠ 0 := (map_ne_zero e').mpr hy
      have h1 := hval y
      rw [D.E.divisorialValuation_eq_exp_neg_ord hey, D'.E.divisorialValuation_eq_exp_neg_ord hy,
        WithZero.exp_inj] at h1
      omega
  -- the pull-back along `θ = D.f^* ∘ ι^*`
  letI : Algebra U.toScheme.functionField D.Y.functionField := θ.toAlgebra
  haveI hTUS : IsScalarTower U.toScheme.functionField (Spec (genRing sX t)).functionField
      D.Y.functionField := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI hTθ : IsScalarTower k U.toScheme.functionField D.Y.functionField :=
    IsScalarTower.of_algebraMap_eq fun z => by
      change _ = algebraMap (Spec (genRing sX t)).functionField D.Y.functionField
        (algebraMap U.toScheme.functionField (Spec (genRing sX t)).functionField
          (algebraMap k U.toScheme.functionField z))
      rw [IsScalarTower.algebraMap_apply k (Spec (genRing sX t)).functionField D.Y.functionField z,
        IsScalarTower.algebraMap_apply k U.toScheme.functionField
          (Spec (genRing sX t)).functionField z]
  haveI hfU := MMP.Mori.essFiniteType_functionField (sX := U.ι ≫ sX)
  obtain ⟨ω₀, hω₀⟩ := MMP.Mori.exists_isPullbackGenerator_of_bijective (sX := U.ι ≫ sX)
    (f := genι sX t hU) hbijι hdU
  have hθgen : MMP.Mori.IsPullbackGenerator D.Y.functionField ω₀ :=
    isPullbackGenerator_of_bijective_algebraMap hθ hdU hω₀.1 hω₀.ne_zero
  have hω₀' : MMP.Mori.IsPullbackGenerator D.Y.functionField
      (MMP.Mori.topFormsMap k U.toScheme.functionField (Spec (genRing sX t)).functionField (d + 2)
        ω₀) := by
    refine ⟨hω₀.2.1, ?_, ?_⟩
    · rw [MMP.Threefold.Mori.Helpers.topFormsMap_comp]
      exact hθgen.2.1
    · rw [MMP.Threefold.Mori.Helpers.topFormsMap_comp]
      exact hθgen.2.2
  have hcompS := MMP.Threefold.Mori.Helpers.pullbackForms_comp (K'' := D.Y.functionField)
    (d := d + 2) (m := 1) hω₀ hω₀' ω
  -- the transport along `e' : k(D'.Y) ≅ k(D.Y)` and `ψ : 𝒪_F ≅ 𝒪_E`
  letI : Algebra D'.Y.functionField D.Y.functionField := e'.toAlgebra
  haveI hT4 : IsScalarTower k D'.Y.functionField D.Y.functionField :=
    IsScalarTower.of_algebraMap_eq fun z => (hG3 z).symm
  haveI hT5 : IsScalarTower U.toScheme.functionField D'.Y.functionField D.Y.functionField :=
    IsScalarTower.of_algebraMap_eq fun g => (he' g).symm
  letI : Algebra D'.E.localRing D.E.localRing := ψ.toAlgebra
  letI : Algebra D'.E.localRing D.Y.functionField :=
    ((algebraMap D.E.localRing D.Y.functionField).comp ψ).toAlgebra
  haveI hS1 : IsScalarTower k D'.E.localRing D.E.localRing :=
    IsScalarTower.of_algebraMap_eq fun z => (hφk z).symm
  haveI hS2 : IsScalarTower D'.E.localRing D.E.localRing D.Y.functionField :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI hS3 : IsScalarTower D'.E.localRing D'.Y.functionField D.Y.functionField :=
    IsScalarTower.of_algebraMap_eq hψ
  haveI hS4 : IsScalarTower k D'.E.localRing D.Y.functionField := by
    refine IsScalarTower.of_algebraMap_eq fun z => ?_
    change _ = algebraMap D.E.localRing D.Y.functionField (ψ (algebraMap k D'.E.localRing z))
    rw [hφk z, ← IsScalarTower.algebraMap_apply]
  have hd1 : (Algebra.trdeg k D'.Y.functionField).toNat = d + 2 :=
    MMP.Mori.toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := D'.f ≫ U.ι ≫ sX) hn
  haveI hfD' := MMP.Mori.essFiniteType_functionField (sX := D'.f ≫ U.ι ≫ sX)
  have he'bij : Function.Bijective (algebraMap D'.Y.functionField D.Y.functionField) :=
    ⟨e'.injective, he'surj⟩
  obtain ⟨σF, hσF, h0σF⟩ := D'.E.exists_topForms_generator (sX := D'.f ≫ U.ι ≫ sX) hd1
  have hωT : MMP.Mori.IsPullbackGenerator D.Y.functionField
      (MMP.Mori.topFormsMap k D'.E.localRing D'.Y.functionField (d + 2) σF) :=
    isPullbackGenerator_of_bijective_algebraMap he'bij hd1
      (MMP.Mori.span_singleton_topFormsMap (nonZeroDivisors _) hσF) h0σF
  have key := MMP.Threefold.Mori.Helpers.ordAt_pullbackForms_eq (k := k)
    (K := D'.Y.functionField) (K' := D.Y.functionField) (A := D'.E.localRing)
    (A' := D.E.localRing) (d := d + 2) (m := 1) hψb
    (v := fun y => D'.Y.ord y D'.E.genericPoint) (v' := fun y => D.Y.ord y D.E.genericPoint)
    (fun x y hx hy => D'.E.ord_mul_of_ne_zero x y hx hy)
    (fun a ha => D'.E.ord_algebraMap_of_isUnit ha)
    (fun x y hx hy => D.E.ord_mul_of_ne_zero x y hx hy)
    (fun a ha => D.E.ord_algebraMap_of_isUnit ha) hord hσF hωT
    (MMP.Mori.pullbackForms (K' := D'.Y.functionField) 1 ω)
  have hωD' : MMP.Mori.IsPullbackGenerator D'.Y.functionField ω₀ :=
    isPullbackGenerator_of_bijective_algebraMap hbD' hdU hω₀.1 hω₀.ne_zero
  have hωD'' : MMP.Mori.IsPullbackGenerator D.Y.functionField
      (MMP.Mori.topFormsMap k U.toScheme.functionField D'.Y.functionField (d + 2) ω₀) :=
    isPullbackGenerator_of_bijective_algebraMap he'bij hd1 hωD'.2.1 hωD'.2.2
  have hcompD' := MMP.Threefold.Mori.Helpers.pullbackForms_comp (K'' := D.Y.functionField)
    (d := d + 2) (m := 1) hωD' hωD'' ω
  change MMP.Mori.ordAt (k := k) D'.E.localRing (fun f => D'.Y.ord f D'.E.genericPoint)
      (MMP.Mori.pullbackForms (K' := D'.Y.functionField) 1 ω) =
    MMP.Mori.ordAt (k := k) D.E.localRing (fun f => D.Y.ord f D.E.genericPoint)
      (MMP.Mori.pullbackForms (K' := D.Y.functionField) 1
        (MMP.Mori.pullbackForms (K' := (Spec (genRing sX t)).functionField) 1 ω))
  rw [← key, hcompD', hcompS]

/-- **The pulled-back forms at a divisor over the generic surface.** With `c • ι^*ω₀ = dt ∧ η`
and `η̄₁ ∧ η̄₂ ≠ 0`: `c ≠ 0`, `ι^*ω₀` pulls back to a generator of `Ω^{d+2}_{k(D.Y)/k}`, and the
pull-backs to `k(D.Y)` of `ι^*ω₀` and of any `v` with `c • v = η̄₁ ∧ η̄₂` are the same multiple of
the images of generators of `Ω^{d+2}_{𝒪_E/k}` and `Ω²_{𝒪_E/K}`. -/
private theorem exists_eq_smul_topFormsMap_genSurface_of_smul
    {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {B : QDivisor X} (hB : MMP.Fourfold.IsPair sX B) {x : X}
    {U : X.Opens} (hU : IsAffineOpen U) (hxU : x ∈ U) [IsIntegral U] [IsLocallyNoetherian U]
    [IsNormal U] {d : ℕ} (t : Fin d → Γ(X, U))
    [IsIntegral (Spec (genRing sX t))] [IsLocallyNoetherian (Spec (genRing sX t))]
    [IsNormal (Spec (genRing sX t))] [IsDominant (genι sX t hU)]
    (D : DivisorOver (genField k d) (genStructure sX t))
    (D' : DivisorOver k (U.ι ≫ sX))
    (hD'v : D'.valuation = D.valuation.comap (functionFieldMap (genι sX t hU)))
    (hdimX : topologicalKrullDim X = (d + 2 : ℕ))
    (hvar : IsNormalVariety (genField k d) (genStructure sX t))
    (hdimS : topologicalKrullDim (Spec (genRing sX t)) = 2) :
    letI := MMP.Mori.functionFieldAlgebra (U.ι ≫ sX)
    letI := MMP.Mori.functionFieldAlgebra (genι sX t hU ≫ U.ι ≫ sX)
    letI := MMP.Mori.functionFieldMapAlgebra (genι sX t hU)
    haveI := MMP.Mori.isScalarTower_functionFieldMap (U.ι ≫ sX) (genι sX t hU)
    letI := MMP.Mori.functionFieldAlgebra (genStructure sX t)
    haveI := isScalarTower_stalkAlgebra_comp (genStructure sX t) (genι sX t hU ≫ U.ι ≫ sX)
      (genι_comp_eq sX t hU) (genericPoint (Spec (genRing sX t)))
    haveI := D.isIntegral
    haveI := D.isLocallyNoetherian
    haveI := D.isDominant
    letI := MMP.Mori.functionFieldAlgebra (D.f ≫ genι sX t hU ≫ U.ι ≫ sX)
    letI := MMP.Mori.functionFieldAlgebra (D.f ≫ genStructure sX t)
    letI := MMP.Mori.functionFieldMapAlgebra D.f
    haveI := MMP.Mori.isScalarTower_functionFieldMap (genι sX t hU ≫ U.ι ≫ sX) D.f
    haveI := MMP.Mori.isScalarTower_functionFieldMap (genStructure sX t) D.f
    haveI := isScalarTower_stalkAlgebra_comp (D.f ≫ genStructure sX t)
      (D.f ≫ genι sX t hU ≫ U.ι ≫ sX) (comp_genι_comp_eq sX hU t D.f) (genericPoint D.Y)
    letI := MMP.Mori.stalkAlgebra (D.f ≫ genι sX t hU ≫ U.ι ≫ sX) D.E.genericPoint
    letI := MMP.Mori.stalkAlgebra (D.f ≫ genStructure sX t) D.E.genericPoint
    haveI := isScalarTower_stalkAlgebra_comp (D.f ≫ genStructure sX t)
      (D.f ≫ genι sX t hU ≫ U.ι ≫ sX) (comp_genι_comp_eq sX hU t D.f) D.E.genericPoint
    haveI := MMP.Mori.isScalarTower_stalk_functionField (D.f ≫ genι sX t hU ≫ U.ι ≫ sX)
      D.E.genericPoint
    haveI := MMP.Mori.isScalarTower_stalk_functionField (D.f ≫ genStructure sX t)
      D.E.genericPoint
    ∀ (ω₀ : ⋀[U.toScheme.functionField]^(d + 2) Ω[U.toScheme.functionField⁄k])
      (hω₀ : MMP.Mori.IsPullbackGenerator (Spec (genRing sX t)).functionField ω₀)
      (η : Fin 2 → Ω[(Spec (genRing sX t)).functionField⁄k])
      (c : (Spec (genRing sX t)).functionField),
      c • MMP.Mori.topFormsMap k U.toScheme.functionField (Spec (genRing sX t)).functionField
          (d + 2) ω₀ =
        exteriorPower.ιMulti (Spec (genRing sX t)).functionField (d + 2)
          (Fin.append (fun i => KaehlerDifferential.D k _
            (algebraMap (genField k d) (Spec (genRing sX t)).functionField
              (algebraMap (MvPolynomial (Fin d) k) (genField k d) (.X i)))) η) →
      exteriorPower.ιMulti (Spec (genRing sX t)).functionField 2
        (fun j => KaehlerDifferential.map k (genField k d) (Spec (genRing sX t)).functionField
          (Spec (genRing sX t)).functionField (η j)) ≠ 0 →
      c ≠ 0 ∧ MMP.Mori.IsPullbackGenerator D.Y.functionField
        (MMP.Mori.topFormsMap k U.toScheme.functionField (Spec (genRing sX t)).functionField
          (d + 2) ω₀) ∧
      ∃ (σk : ⋀[D.E.localRing]^(d + 2) Ω[D.E.localRing⁄k])
        (σK : ⋀[D.E.localRing]^2 Ω[D.E.localRing⁄genField k d]),
        Submodule.span D.E.localRing {σk} = ⊤ ∧ Submodule.span D.E.localRing {σK} = ⊤ ∧
        ∃ cE : D.Y.functionField,
          MMP.Mori.topFormsMap k (Spec (genRing sX t)).functionField D.Y.functionField (d + 2)
            (MMP.Mori.topFormsMap k U.toScheme.functionField (Spec (genRing sX t)).functionField
              (d + 2) ω₀) =
            ((algebraMap (Spec (genRing sX t)).functionField D.Y.functionField c)⁻¹ * cE) •
              MMP.Mori.topFormsMap k D.E.localRing D.Y.functionField (d + 2) σk ∧
          ∀ v : ⋀[(Spec (genRing sX t)).functionField]^2
              Ω[(Spec (genRing sX t)).functionField⁄genField k d],
            c • v = exteriorPower.ιMulti (Spec (genRing sX t)).functionField 2
              (fun j => KaehlerDifferential.map k (genField k d) (Spec (genRing sX t)).functionField
          (Spec (genRing sX t)).functionField (η j)) →
            MMP.Mori.topFormsMap (genField k d) (Spec (genRing sX t)).functionField
                D.Y.functionField 2 v =
              ((algebraMap (Spec (genRing sX t)).functionField D.Y.functionField c)⁻¹ * cE) •
                MMP.Mori.topFormsMap (genField k d) D.E.localRing D.Y.functionField 2 σK := by
  intro ω₀ hω₀ η c hc hu
  classical
  haveI := hB.charZero
  haveI : CharZero (genField k d) :=
    charZero_of_injective_algebraMap (algebraMap k (genField k d)).injective
  have hXv : IsNormalVariety k sX := hB.isPair.1
  haveI : LocallyOfFiniteType sX := hXv.1.toLocallyOfFiniteType
  haveI : Nonempty U := ⟨⟨x, hxU⟩⟩
  haveI : IsDominant U.ι := isDominant_opens_ι U
  have hUv := isNormalVariety_ι hXv U
  haveI : LocallyOfFiniteType (U.ι ≫ sX) := hUv.1.toLocallyOfFiniteType
  have hdimU : topologicalKrullDim U = (d + 2 : ℕ) :=
      (topologicalKrullDim_opens_eq hXv U).trans hdimX
  haveI : LocallyOfFiniteType (genStructure sX t) := locallyOfFiniteType_genStructure sX t hU
  have hbijι := bijective_functionFieldMap_genι sX t hU
  have hdU := MMP.Mori.toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := U.ι ≫ sX) hdimU
  letI := MMP.Mori.functionFieldAlgebra (U.ι ≫ sX)
  letI := MMP.Mori.functionFieldAlgebra (genι sX t hU ≫ U.ι ≫ sX)
  letI := MMP.Mori.functionFieldMapAlgebra (genι sX t hU)
  haveI := MMP.Mori.isScalarTower_functionFieldMap (U.ι ≫ sX) (genι sX t hU)
  letI := MMP.Mori.functionFieldAlgebra (genStructure sX t)
  haveI := isScalarTower_stalkAlgebra_comp (genStructure sX t) (genι sX t hU ≫ U.ι ≫ sX)
    (genι_comp_eq sX t hU) (genericPoint (Spec (genRing sX t)))
  have bS := Classical.choice
    (MMP.Positivity.exists_basis_topForms hvar (n := 2) (by exact_mod_cast hdimS))
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  haveI : LocallyOfFiniteType (D.f ≫ genStructure sX t) := D.isNormalVariety.1.toLocallyOfFiniteType
  have hbD := D.isBirationalMorphism.functionFieldMap_bijective
  let θ : U.toScheme.functionField →+* D.Y.functionField :=
    (functionFieldMap D.f).comp (functionFieldMap (genι sX t hU))
  have hθ : Function.Bijective θ := hbD.comp hbijι
  letI := MMP.Mori.functionFieldAlgebra (D.f ≫ genι sX t hU ≫ U.ι ≫ sX)
  letI := MMP.Mori.functionFieldAlgebra (D.f ≫ genStructure sX t)
  letI := MMP.Mori.functionFieldMapAlgebra D.f
  haveI := MMP.Mori.isScalarTower_functionFieldMap (genι sX t hU ≫ U.ι ≫ sX) D.f
  haveI := MMP.Mori.isScalarTower_functionFieldMap (genStructure sX t) D.f
  haveI := isScalarTower_stalkAlgebra_comp (D.f ≫ genStructure sX t) _
    (comp_genι_comp_eq sX hU t D.f) (genericPoint D.Y)
  letI := MMP.Mori.stalkAlgebra (D.f ≫ genι sX t hU ≫ U.ι ≫ sX) D.E.genericPoint
  letI := MMP.Mori.stalkAlgebra (D.f ≫ genStructure sX t) D.E.genericPoint
  haveI := isScalarTower_stalkAlgebra_comp (D.f ≫ genStructure sX t) _
    (comp_genι_comp_eq sX hU t D.f) D.E.genericPoint
  haveI := MMP.Mori.isScalarTower_stalk_functionField (D.f ≫ genι sX t hU ≫ U.ι ≫ sX)
    D.E.genericPoint
  haveI := MMP.Mori.isScalarTower_stalk_functionField (D.f ≫ genStructure sX t) D.E.genericPoint
  have hEx := exists_eq_smul_topFormsMap_genSurface_divisorOver sX hB hU hxU t D D' hD'v hdimX η
  have hσk := hEx.choose_spec.choose_spec.1
  have hσK := hEx.choose_spec.choose_spec.2.1
  have h1E := hEx.choose_spec.choose_spec.2.2.choose_spec.1
  have h2E := hEx.choose_spec.choose_spec.2.2.choose_spec.2
  -- the forms `dt ∧ η` and `η̄` pulled back to `D.Y`
  have hR1 : MMP.Mori.topFormsMap k (Spec (genRing sX t)).functionField D.Y.functionField (d + 2)
      (exteriorPower.ιMulti (Spec (genRing sX t)).functionField (d + 2)
        (Fin.append (fun i => KaehlerDifferential.D k _
          (algebraMap (genField k d) (Spec (genRing sX t)).functionField
            (algebraMap (MvPolynomial (Fin d) k) (genField k d) (.X i)))) η)) =
      exteriorPower.ιMulti D.Y.functionField (d + 2) (Fin.append (fun i =>
        KaehlerDifferential.D k D.Y.functionField (algebraMap (genField k d) D.Y.functionField
          (algebraMap (MvPolynomial (Fin d) k) (genField k d) (.X i))))
        (fun j => KaehlerDifferential.map k k (Spec (genRing sX t)).functionField
          D.Y.functionField (η j))) := by
    rw [MMP.Mori.topFormsMap_ιMulti]
    congr 1
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.append_left, KaehlerDifferential.map_D]
      rw [← IsScalarTower.algebraMap_apply (genField k d) (Spec (genRing sX t)).functionField
        D.Y.functionField]
    · simp only [Fin.append_right]
  have hR2 : MMP.Mori.topFormsMap (genField k d) (Spec (genRing sX t)).functionField
      D.Y.functionField 2 (exteriorPower.ιMulti (Spec (genRing sX t)).functionField 2
        (fun j => KaehlerDifferential.map k (genField k d) (Spec (genRing sX t)).functionField
          (Spec (genRing sX t)).functionField (η j))) =
      exteriorPower.ιMulti D.Y.functionField 2 (fun j =>
        KaehlerDifferential.map k (genField k d) D.Y.functionField D.Y.functionField
          (KaehlerDifferential.map k k (Spec (genRing sX t)).functionField
            D.Y.functionField (η j))) := by
    rw [MMP.Mori.topFormsMap_ιMulti]
    congr 1
    funext j
    exact (map_map_eq_map_map (η j)).symm
  -- pull-back generators along `D.f` and `D.f ≫ genι`
  have hpgK : ∀ v : ⋀[(Spec (genRing sX t)).functionField]^2
      Ω[(Spec (genRing sX t)).functionField⁄genField k d], v ≠ 0 →
      MMP.Mori.topFormsMap (genField k d) _ D.Y.functionField 2 v ≠ 0 := by
    intro v hv0
    have hdS := MMP.Mori.toNat_trdeg_functionField_of_topologicalKrullDim_eq
      (sX := genStructure sX t) (d := 2) (by exact_mod_cast hdimS)
    obtain ⟨ω₁, hω₁⟩ := MMP.Mori.exists_isPullbackGenerator_of_bijective (sX := genStructure sX t)
      (f := D.f) hbD hdS
    exact (MMP.Threefold.Mori.Helpers.IsPullbackGenerator.of_span hω₁
      (span_singleton_eq_top_of_basis_unit bS hv0) hv0).2.2

  -- the pull-back along `θ = D.f^* ∘ ι^*` over `k`, and `c ≠ 0`
  letI : Algebra U.toScheme.functionField D.Y.functionField := θ.toAlgebra
  haveI hTUS : IsScalarTower U.toScheme.functionField (Spec (genRing sX t)).functionField
      D.Y.functionField := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI hTθ : IsScalarTower k U.toScheme.functionField D.Y.functionField :=
    IsScalarTower.of_algebraMap_eq fun z => by
      change _ = algebraMap (Spec (genRing sX t)).functionField D.Y.functionField
        (algebraMap U.toScheme.functionField (Spec (genRing sX t)).functionField
          (algebraMap k U.toScheme.functionField z))
      rw [IsScalarTower.algebraMap_apply k (Spec (genRing sX t)).functionField D.Y.functionField z,
        IsScalarTower.algebraMap_apply k U.toScheme.functionField
          (Spec (genRing sX t)).functionField z]
  haveI hfU := MMP.Mori.essFiniteType_functionField (sX := U.ι ≫ sX)
  have hθgen : MMP.Mori.IsPullbackGenerator D.Y.functionField ω₀ :=
    isPullbackGenerator_of_bijective_algebraMap hθ hdU hω₀.1 hω₀.ne_zero
  have hbU : MMP.Mori.basisOfSpanSingleton hω₀.1 hω₀.ne_zero () = ω₀ :=
    MMP.Mori.basisOfSpanSingleton_apply _ _ _
  have hx0 : MMP.Mori.topFormsMap k (Spec (genRing sX t)).functionField D.Y.functionField (d + 2)
      (MMP.Mori.topFormsMap k U.toScheme.functionField (Spec (genRing sX t)).functionField (d + 2)
        ω₀) ≠ 0 := by
    rw [MMP.Threefold.Mori.Helpers.topFormsMap_comp]
    exact hθgen.2.2
  have hcE := ne_zero_of_eq_smul hR2 h2E (hpgK _ hu)
  have hcne : c ≠ 0 := ne_zero_of_map_eq_smul
    (MMP.Mori.topFormsMap k (Spec (genRing sX t)).functionField D.Y.functionField (d + 2)) hc hR1
    h1E hcE (MMP.Mori.span_singleton_topFormsMap (K := D.Y.functionField)
      (nonZeroDivisors D.E.localRing) hσk) hx0
  refine ⟨hcne, ⟨hω₀.2.1, ?_, ?_⟩, _, _, hσk, hσK, _, map_eq_inv_mul_smul _ hcne hc hR1 h1E,
    fun v hv => map_eq_inv_mul_smul _ hcne hv hR2 h2E⟩
  · rw [MMP.Threefold.Mori.Helpers.topFormsMap_comp]
    exact hθgen.2.1
  · rw [MMP.Threefold.Mori.Helpers.topFormsMap_comp]
    exact hθgen.2.2

/-- **The orders of the canonical forms along `E` and `F` agree.** For the pull-back generator
`ω₀` of `Ω^{d+2}_{k(U)/k}` along `ι = genι`, forms `η` on `K(S)` and `c` with
`c • ι^*ω₀ = dt ∧ η`, and a divisor `D` over the generic surface and `D'` over `U` with the same
valuation: `c ≠ 0`, and for a basis `bK` of `Ω²_{K(S)/K}` with `c • bK = η̄₁ ∧ η̄₂` the forms `bK`
and `ω₀` have the same order along `E` and `F`: both are the same multiple of the images of
generators of `Ω^{d+2}_{𝒪_E/k}` and `Ω²_{𝒪_E/K}`
(`exists_eq_smul_topFormsMap_genSurface_divisorOver`), and the order along `F` is read along `E`
(`ordPullback_eq_ordForm_pullback_genSurface`). -/
private theorem ordPullback_basis_eq_of_genSurface
    {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {B : QDivisor X} (hB : MMP.Fourfold.IsPair sX B) {x : X}
    {U : X.Opens} (hU : IsAffineOpen U) (hxU : x ∈ U) [IsIntegral U] [IsLocallyNoetherian U]
    [IsNormal U] {d : ℕ} (t : Fin d → Γ(X, U))
    [IsIntegral (Spec (genRing sX t))] [IsLocallyNoetherian (Spec (genRing sX t))]
    [IsNormal (Spec (genRing sX t))] [IsDominant (genι sX t hU)]
    (D : DivisorOver (genField k d) (genStructure sX t))
    (D' : DivisorOver k (U.ι ≫ sX))
    (hD'v : D'.valuation = D.valuation.comap (functionFieldMap (genι sX t hU)))
    (hdimX : topologicalKrullDim X = (d + 2 : ℕ))
    (hvar : IsNormalVariety (genField k d) (genStructure sX t))
    (hdimS : topologicalKrullDim (Spec (genRing sX t)) = 2) :
    letI := MMP.Mori.functionFieldAlgebra (U.ι ≫ sX)
    letI := MMP.Mori.functionFieldAlgebra (genι sX t hU ≫ U.ι ≫ sX)
    letI := MMP.Mori.functionFieldMapAlgebra (genι sX t hU)
    haveI := MMP.Mori.isScalarTower_functionFieldMap (U.ι ≫ sX) (genι sX t hU)
    letI := MMP.Mori.functionFieldAlgebra (genStructure sX t)
    haveI := isScalarTower_stalkAlgebra_comp (genStructure sX t) (genι sX t hU ≫ U.ι ≫ sX)
      (genι_comp_eq sX t hU) (genericPoint (Spec (genRing sX t)))
    ∀ (ω₀ : ⋀[U.toScheme.functionField]^(d + 2) Ω[U.toScheme.functionField⁄k])
      (hω₀ : MMP.Mori.IsPullbackGenerator (Spec (genRing sX t)).functionField ω₀)
      (η : Fin 2 → Ω[(Spec (genRing sX t)).functionField⁄k])
      (c : (Spec (genRing sX t)).functionField),
      c • MMP.Mori.topFormsMap k U.toScheme.functionField (Spec (genRing sX t)).functionField
          (d + 2) ω₀ =
        exteriorPower.ιMulti (Spec (genRing sX t)).functionField (d + 2)
          (Fin.append (fun i => KaehlerDifferential.D k _
            (algebraMap (genField k d) (Spec (genRing sX t)).functionField
              (algebraMap (MvPolynomial (Fin d) k) (genField k d) (.X i)))) η) →
      exteriorPower.ιMulti (Spec (genRing sX t)).functionField 2
        (fun j => KaehlerDifferential.map k (genField k d) (Spec (genRing sX t)).functionField
          (Spec (genRing sX t)).functionField (η j)) ≠ 0 →
      c ≠ 0 ∧ ∀ bK : Module.Basis Unit (Spec (genRing sX t)).functionField
          (⋀[(Spec (genRing sX t)).functionField]^2
            Ω[(Spec (genRing sX t)).functionField⁄genField k d]),
        c • bK () = exteriorPower.ιMulti (Spec (genRing sX t)).functionField 2
          (fun j => KaehlerDifferential.map k (genField k d) (Spec (genRing sX t)).functionField
          (Spec (genRing sX t)).functionField (η j)) →
        D.ordPullback (@id (MMP.Mori.RationalPluriForms (genStructure sX t) 2 1)
            (MMP.Mori.ZTensorPower.basis bK 1 ())) =
          D'.ordPullback (@id (MMP.Mori.RationalPluriForms (U.ι ≫ sX) (d + 2) 1)
            (MMP.Mori.ZTensorPower.basis (MMP.Mori.basisOfSpanSingleton hω₀.1 hω₀.ne_zero) 1
              ())) := by
  intro ω₀ hω₀ η c hc hu
  classical
  haveI := hB.charZero
  haveI : CharZero (genField k d) :=
    charZero_of_injective_algebraMap (algebraMap k (genField k d)).injective
  have hXv : IsNormalVariety k sX := hB.isPair.1
  haveI : LocallyOfFiniteType sX := hXv.1.toLocallyOfFiniteType
  haveI : Nonempty U := ⟨⟨x, hxU⟩⟩
  haveI : IsDominant U.ι := isDominant_opens_ι U
  have hUv := isNormalVariety_ι hXv U
  haveI : LocallyOfFiniteType (U.ι ≫ sX) := hUv.1.toLocallyOfFiniteType
  have hdimU : topologicalKrullDim U = (d + 2 : ℕ) :=
      (topologicalKrullDim_opens_eq hXv U).trans hdimX
  haveI : LocallyOfFiniteType (genStructure sX t) := locallyOfFiniteType_genStructure sX t hU
  have hbijι := bijective_functionFieldMap_genι sX t hU
  have hdU := MMP.Mori.toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := U.ι ≫ sX) hdimU
  letI := MMP.Mori.functionFieldAlgebra (U.ι ≫ sX)
  letI := MMP.Mori.functionFieldAlgebra (genι sX t hU ≫ U.ι ≫ sX)
  letI := MMP.Mori.functionFieldMapAlgebra (genι sX t hU)
  haveI := MMP.Mori.isScalarTower_functionFieldMap (U.ι ≫ sX) (genι sX t hU)
  letI := MMP.Mori.functionFieldAlgebra (genStructure sX t)
  haveI := isScalarTower_stalkAlgebra_comp (genStructure sX t) (genι sX t hU ≫ U.ι ≫ sX)
    (genι_comp_eq sX t hU) (genericPoint (Spec (genRing sX t)))
  have bS := Classical.choice
    (MMP.Positivity.exists_basis_topForms hvar (n := 2) (by exact_mod_cast hdimS))
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  haveI : LocallyOfFiniteType (D.f ≫ genStructure sX t) := D.isNormalVariety.1.toLocallyOfFiniteType
  have hbD := D.isBirationalMorphism.functionFieldMap_bijective
  letI := MMP.Mori.functionFieldAlgebra (D.f ≫ genι sX t hU ≫ U.ι ≫ sX)
  letI := MMP.Mori.functionFieldAlgebra (D.f ≫ genStructure sX t)
  letI := MMP.Mori.functionFieldMapAlgebra D.f
  haveI := MMP.Mori.isScalarTower_functionFieldMap (genι sX t hU ≫ U.ι ≫ sX) D.f
  haveI := MMP.Mori.isScalarTower_functionFieldMap (genStructure sX t) D.f
  haveI := isScalarTower_stalkAlgebra_comp (D.f ≫ genStructure sX t) _
    (comp_genι_comp_eq sX hU t D.f) (genericPoint D.Y)
  letI := MMP.Mori.stalkAlgebra (D.f ≫ genι sX t hU ≫ U.ι ≫ sX) D.E.genericPoint
  letI := MMP.Mori.stalkAlgebra (D.f ≫ genStructure sX t) D.E.genericPoint
  haveI := isScalarTower_stalkAlgebra_comp (D.f ≫ genStructure sX t) _
    (comp_genι_comp_eq sX hU t D.f) D.E.genericPoint
  haveI := MMP.Mori.isScalarTower_stalk_functionField (D.f ≫ genι sX t hU ≫ U.ι ≫ sX)
    D.E.genericPoint
  haveI := MMP.Mori.isScalarTower_stalk_functionField (D.f ≫ genStructure sX t) D.E.genericPoint
  obtain ⟨hcne, hgk, _, _, hσk, hσK, _, hb0, hb0'⟩ :=
    exists_eq_smul_topFormsMap_genSurface_of_smul sX hB hU hxU t D D' hD'v hdimX hvar
      hdimS ω₀ hω₀ η c hc hu
  refine ⟨hcne, fun bK hcK => ?_⟩
  have hdS := MMP.Mori.toNat_trdeg_functionField_of_topologicalKrullDim_eq
    (sX := genStructure sX t) (d := 2) (by exact_mod_cast hdimS)
  obtain ⟨_, hω₁⟩ := MMP.Mori.exists_isPullbackGenerator_of_bijective (sX := genStructure sX t)
    (f := D.f) hbD hdS
  have hgK : MMP.Mori.IsPullbackGenerator D.Y.functionField (bK ()) :=
    MMP.Threefold.Mori.Helpers.IsPullbackGenerator.of_span hω₁
      (span_singleton_eq_top_of_basis_unit bS (bK.ne_zero ())) (bK.ne_zero ())
  let ωU : MMP.Mori.RationalPluriForms (U.ι ≫ sX) (d + 2) 1 :=
    MMP.Mori.ZTensorPower.basis (MMP.Mori.basisOfSpanSingleton hω₀.1 hω₀.ne_zero) 1 ()
  let ωS : MMP.Mori.RationalPluriForms (genStructure sX t) 2 1 :=
    MMP.Mori.ZTensorPower.basis bK 1 ()
  have hpullU : MMP.Mori.pullbackRationalPluriForms (U.ι ≫ sX) (genι sX t hU) ωU =
      MMP.Mori.ZTensorPower.basis (MMP.Mori.basisOfSpanSingleton hω₀.2.1 hω₀.2.2) 1 () := by
    change MMP.Mori.pullbackForms (K' := (Spec (genRing sX t)).functionField) 1 ωU = _
    exact pullbackForms_basis_one hω₀ _ (MMP.Mori.basisOfSpanSingleton_apply _ _ _)
  have hpullk : MMP.Mori.pullbackRationalPluriForms (d := d + 2) (m := 1)
      (genι sX t hU ≫ U.ι ≫ sX) D.f
      (MMP.Mori.ZTensorPower.basis (MMP.Mori.basisOfSpanSingleton hω₀.2.1 hω₀.2.2) 1 ()) =
      MMP.Mori.ZTensorPower.basis (MMP.Mori.basisOfSpanSingleton hgk.2.1 hgk.2.2) 1 () := by
    change MMP.Mori.pullbackForms (K' := D.Y.functionField) 1 _ = _
    exact pullbackForms_basis_one hgk _ (MMP.Mori.basisOfSpanSingleton_apply _ _ _)
  have hpullS : MMP.Mori.pullbackRationalPluriForms (genStructure sX t) D.f ωS =
      MMP.Mori.ZTensorPower.basis (MMP.Mori.basisOfSpanSingleton hgK.2.1 hgK.2.2) 1 () := by
    change MMP.Mori.pullbackForms (K' := D.Y.functionField) 1 ωS = _
    exact pullbackForms_basis_one hgK bK rfl
  have hb := (MMP.Mori.basisOfSpanSingleton_apply hgk.2.1 hgk.2.2 ()).trans hb0
  have hb' := (MMP.Mori.basisOfSpanSingleton_apply hgK.2.1 hgK.2.2 ()).trans (hb0' _ hcK)
  have hθE := ordAt_eq_ordAt_of_basis_eq_smul (k := k) (K := genField k d)
    (R := D.E.localRing) (L := D.Y.functionField) (v := fun f => D.Y.ord f D.E.genericPoint)
    (D.E.ord_mul_of_ne_zero)
    (fun _ ha => D.E.ord_algebraMap_of_isUnit ha) hσk hσK _ _ _ hb hb' 1
    (MMP.Mori.ZTensorPower.basis (MMP.Mori.basisOfSpanSingleton hgk.2.1 hgk.2.2) 1 ())
    (MMP.Mori.ZTensorPower.basis (MMP.Mori.basisOfSpanSingleton hgK.2.1 hgK.2.2) 1 ()) (by simp)
  have e1 := ordPullback_eq_ordForm_pullback_genSurface sX hB hU hxU t D D' hD'v hdimX ωU
  refine (congrArg (MMP.Mori.PrimeDivisor.ordForm D.E) hpullS).trans (hθE.symm.trans ?_)
  refine ((congrArg (MMP.Mori.PrimeDivisor.ordForm D.E) hpullk).symm.trans ?_).trans e1.symm
  exact congrArg (fun τ => MMP.Mori.PrimeDivisor.ordForm D.E
    (MMP.Mori.pullbackRationalPluriForms (genι sX t hU ≫ U.ι ≫ sX) D.f τ)) hpullU.symm

/-- **The log discrepancies agree.** For a divisor `D` over the generic surface with `D.f` proper,
and a divisor `D'` over `U` with proper morphism, the same valuation (through `ι = genι`) and
generic point mapping to `ι(D.f(η_E))`, the log discrepancy of `D` for `(S, B_S)`
(dimension `2`, over `K`) and that of `D'` for `(U, B|_U)` (dimension `d + 2`, over `k`) coincide,
with either defined exactly when the other is. In the source: the determinant identity
`ω_X = dt₁ ∧ ⋯ ∧ dt_d ∧ ω_S` (`MMP.Mori.PrimeDivisor.exact_mapBaseChange_map_localRing`)
identifies the canonical
divisors and `K_S + B_S` with the restriction of `K_X + B`, and the order of the pulled-back
forms along `D` and `D'` is the same valuation. -/
private theorem isLogDiscrepancy_genSurface_iff
    {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {B : QDivisor X} (hB : MMP.Fourfold.IsPair sX B) {x : X} (hx : Order.coheight x = 2)
    {U : X.Opens} (hU : IsAffineOpen U) (hxU : x ∈ U) [IsIntegral U] [IsLocallyNoetherian U]
    [IsNormal U] {d : ℕ} (t : Fin d → Γ(X, U))
    (ht : letI := sectionAlgebra sX U;
      IsTranscendenceBasis k (Ideal.Quotient.mk (hU.primeIdealOf ⟨x, hxU⟩).asIdeal ∘ t))
    [IsIntegral (Spec (genRing sX t))] [IsLocallyNoetherian (Spec (genRing sX t))]
    [IsNormal (Spec (genRing sX t))] [IsDominant (genι sX t hU)]
    (hBS : MMP.Mori.IsPair (genStructure sX t) (genBoundary sX t hU B))
    (D : DivisorOver (genField k d) (genStructure sX t)) (hDp : IsProper D.f)
    (D' : DivisorOver k (U.ι ≫ sX)) (hD'p : IsProper D'.f)
    (hD'v : D'.valuation = D.valuation.comap (functionFieldMap (genι sX t hU)))
    (hD'x : D'.f D'.E.genericPoint = genι sX t hU (D.f D.E.genericPoint))
    (hdimX : topologicalKrullDim X = (d + 2 : ℕ))
    (hvar : IsNormalVariety (genField k d) (genStructure sX t))
    (hdimS : topologicalKrullDim (Spec (genRing sX t)) = 2) :
    ∀ a : ℝ, MMP.Intersection.IsLogDiscrepancy (genStructure sX t) 2
        (QDivisor.toRDivisor (genBoundary sX t hU B)) D a ↔
      MMP.Intersection.IsLogDiscrepancy (U.ι ≫ sX) (d + 2)
        (QDivisor.toRDivisor (MMP.Mori.inverseTransformDivisor U.ι B)) D' a := by
  classical
  haveI := hB.charZero
  haveI : CharZero (genField k d) :=
    charZero_of_injective_algebraMap (algebraMap k (genField k d)).injective
  have hXv : IsNormalVariety k sX := hB.isPair.1
  haveI : LocallyOfFiniteType sX := hXv.1.toLocallyOfFiniteType
  haveI : Nonempty U := ⟨⟨x, hxU⟩⟩
  haveI : IsDominant U.ι := isDominant_opens_ι U
  have hUv := isNormalVariety_ι hXv U
  haveI : LocallyOfFiniteType (U.ι ≫ sX) := hUv.1.toLocallyOfFiniteType
  have hdimU : topologicalKrullDim U = (d + 2 : ℕ) :=
      (topologicalKrullDim_opens_eq hXv U).trans hdimX
  have hPU := isPair_ι hB.isPair U
  haveI : LocallyOfFiniteType (genStructure sX t) := locallyOfFiniteType_genStructure sX t hU
  have hbijι := bijective_functionFieldMap_genι sX t hU
  have hdU := MMP.Mori.toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := U.ι ≫ sX) hdimU
  letI := MMP.Mori.functionFieldAlgebra (U.ι ≫ sX)
  letI := MMP.Mori.functionFieldAlgebra (genι sX t hU ≫ U.ι ≫ sX)
  letI := MMP.Mori.functionFieldMapAlgebra (genι sX t hU)
  haveI := MMP.Mori.isScalarTower_functionFieldMap (U.ι ≫ sX) (genι sX t hU)
  obtain ⟨ω₀, hω₀⟩ := MMP.Mori.exists_isPullbackGenerator_of_bijective (sX := U.ι ≫ sX)
    (f := genι sX t hU) hbijι hdU
  set bU := MMP.Mori.basisOfSpanSingleton hω₀.1 hω₀.ne_zero
  set bkS := MMP.Mori.basisOfSpanSingleton hω₀.2.1 hω₀.2.2
  letI := MMP.Mori.functionFieldAlgebra (genStructure sX t)
  haveI := isScalarTower_stalkAlgebra_comp (genStructure sX t) (genι sX t hU ≫ U.ι ≫ sX)
    (genι_comp_eq sX t hU) (genericPoint (Spec (genRing sX t)))
  obtain ⟨bS⟩ := MMP.Positivity.exists_basis_topForms hvar (n := 2) (by exact_mod_cast hdimS)
  obtain ⟨u, hu⟩ := exists_ιMulti_ne_zero (bS.ne_zero ())
  choose η hη using fun j => KaehlerDifferential.map_surjective k (genField k d)
    (Spec (genRing sX t)).functionField (u j)
  have hηu : (fun j => KaehlerDifferential.map k (genField k d) _ _ (η j)) = u := funext hη
  set a := exteriorPower.ιMulti (Spec (genRing sX t)).functionField (d + 2)
    (Fin.append (fun i => KaehlerDifferential.D k _
      (algebraMap (genField k d) (Spec (genRing sX t)).functionField
        (algebraMap (MvPolynomial (Fin d) k) (genField k d) (.X i)))) η) with ha
  obtain ⟨c, hc⟩ : ∃ c, c • bkS () = a := by
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (hω₀.2.1 ▸ Submodule.mem_top (x := a))
    exact ⟨c, by rwa [MMP.Mori.basisOfSpanSingleton_apply]⟩
  have hu' : exteriorPower.ιMulti (Spec (genRing sX t)).functionField 2
      (fun j => KaehlerDifferential.map k (genField k d) (Spec (genRing sX t)).functionField
          (Spec (genRing sX t)).functionField (η j)) ≠ 0 := by
    rwa [hηu]
  have hbkS : bkS () = MMP.Mori.topFormsMap k U.toScheme.functionField
      (Spec (genRing sX t)).functionField (d + 2) ω₀ := MMP.Mori.basisOfSpanSingleton_apply _ _ _
  obtain ⟨hcne, hE⟩ := ordPullback_basis_eq_of_genSurface sX hB hU hxU t D D' hD'v hdimX hvar
    hdimS ω₀ hω₀ η c (by rwa [← hbkS]) hu'
  have hvK0 : c⁻¹ • exteriorPower.ιMulti (Spec (genRing sX t)).functionField 2
      (fun j => KaehlerDifferential.map k (genField k d) (Spec (genRing sX t)).functionField
          (Spec (genRing sX t)).functionField (η j)) ≠ 0 :=
    smul_ne_zero (inv_ne_zero hcne) hu'
  obtain ⟨bK, hcK, hbK'⟩ : ∃ bK : Module.Basis Unit (Spec (genRing sX t)).functionField
      (⋀[(Spec (genRing sX t)).functionField]^2
        Ω[(Spec (genRing sX t)).functionField⁄genField k d]),
      c • bK () = exteriorPower.ιMulti (Spec (genRing sX t)).functionField 2
        (fun j => KaehlerDifferential.map k (genField k d) (Spec (genRing sX t)).functionField
          (Spec (genRing sX t)).functionField (η j)) ∧
      bK () = c⁻¹ • exteriorPower.ιMulti (Spec (genRing sX t)).functionField 2
        (fun j => KaehlerDifferential.map k (genField k d) (Spec (genRing sX t)).functionField
          (Spec (genRing sX t)).functionField (η j)) :=
    ⟨MMP.Mori.basisOfSpanSingleton (span_singleton_eq_top_of_basis_unit bS hvK0) hvK0,
      by rw [MMP.Mori.basisOfSpanSingleton_apply, smul_smul, mul_inv_cancel₀ hcne, one_smul],
      MMP.Mori.basisOfSpanSingleton_apply _ _ _⟩
  let ωU : MMP.Mori.RationalPluriForms (U.ι ≫ sX) (d + 2) 1 := MMP.Mori.ZTensorPower.basis bU 1 ()
  let ωS : MMP.Mori.RationalPluriForms (genStructure sX t) 2 1 :=
    MMP.Mori.ZTensorPower.basis bK 1 ()
  have hpullU : MMP.Mori.pullbackRationalPluriForms (U.ι ≫ sX) (genι sX t hU) ωU =
      MMP.Mori.ZTensorPower.basis bkS 1 () := by
    change MMP.Mori.pullbackForms (K' := (Spec (genRing sX t)).functionField) 1 ωU = _
    rw [MMP.Mori.pullbackForms_eq hω₀]
    simp [MMP.Mori.pullbackFormsAlong, ωU, bU, bkS]
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  haveI := D'.isIntegral
  haveI := D'.isNormal
  haveI := D'.isLocallyNoetherian
  haveI := D'.isDominant
  have htalg : letI := sectionAlgebra sX U; AlgebraicIndependent k t :=
    letI := sectionAlgebra sX U
    AlgebraicIndependent.of_comp (Ideal.Quotient.mkₐ k (hU.primeIdealOf ⟨x, hxU⟩).asIdeal) ht.1
  refine isLogDiscrepancy_iff_of_ordForm_eq (genStructure sX t) (U.ι ≫ sX) (genι sX t hU)
    (n := 2) (n' := d + 2) (by exact_mod_cast hdimS) hdimU hBS hPU D D'
    hDp hD'p bK bU ?_ (hE bK hcK) ?_
  · -- the prime divisors of `S` through `p`
    intro P hPm
    have hcohΓ : Order.coheight (genι sX t hU P.genericPoint) = 1 := by
      rw [coheight_eq_of_isIso_stalkMap _ _ (isIso_stalkMap_genι sX t hU _)]
      exact PrimeDivisor.coheight_genericPoint P
    haveI := isIso_stalkMap_genι sX t hU P.genericPoint
    refine ⟨PrimeDivisor.ofCoheightOne _ hcohΓ, ?_, ?_, ?_, fun g _ =>
      MMP.Positivity.ord_functionFieldMap_of_isIso (genι sX t hU) P _
        (PrimeDivisor.genericPoint_ofCoheightOne _ _).symm g⟩
    · rw [hD'x,
        AlgebraicGeometry.PrimeDivisor.support_eq_closure, PrimeDivisor.genericPoint_ofCoheightOne,
        ← specializes_iff_mem_closure]
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← specializes_iff_mem_closure] at hPm
      exact hPm.map (genι sX t hU).continuous
    · change P.ordForm ωS = MMP.Mori.PrimeDivisor.ordForm (PrimeDivisor.ofCoheightOne _ hcohΓ) ωU
      rw [← MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso (genι sX t hU) hbijι hdU P
        (PrimeDivisor.ofCoheightOne _ hcohΓ) (PrimeDivisor.genericPoint_ofCoheightOne _ hcohΓ).symm
        ωU,
        hpullU]
      exact (ordForm_basis_eq_ordForm_basis_genSurface sX hXv hU t htalg hdimX P bkS bK η c
        hcne hc hbK').symm
    · rw [coeff_genBoundary, inverseTransformDivisor_ι_eq_restrictOpen,
        MMP.Mori.DivisorWithCoeffs.coeff_restrictOpen]
      congr 1
      apply PrimeDivisor.genericPoint_injective
      refine (genericPoint_genPrimeDivisor sX t hU P).trans ?_
      rw [OpenWeilRestriction.genericPoint_primeDivisorMap, PrimeDivisor.genericPoint_ofCoheightOne]
  · intro g hg
    have h : D.E.divisorialValuation (functionFieldMap D.f (functionFieldMap (genι sX t hU) g)) =
        D'.E.divisorialValuation (functionFieldMap D'.f g) := congrArg (fun w => w g) hD'v.symm
    rw [D.E.divisorialValuation_eq_exp_neg_ord ((map_ne_zero _).2 ((map_ne_zero _).2 hg)),
      D'.E.divisorialValuation_eq_exp_neg_ord ((map_ne_zero _).2 hg), WithZero.exp_inj] at h
    omega

section Chart

open MMP.Mori (sectionAlgebra)

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) {U : X.Opens}
  {d : ℕ} (t : Fin d → Γ(X, U)) (hU : IsAffineOpen U)

/-- The morphism `φ = (t₁, …, t_d) : U ⟶ 𝔸^d_k`. -/
private noncomputable def genφ {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    {U : X.Opens} {d : ℕ} (t : Fin d → Γ(X, U)) (hU : IsAffineOpen U) :
    (U : Scheme.{u}) ⟶ Spec (.of (MvPolynomial (Fin d) k)) :=
  letI := sectionAlgebra sX U
  hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := k) t).toRingHom)

private lemma genφ_comp :
    genφ sX t hU ≫ Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin d) k))) =
      U.ι ≫ sX := by
  letI := sectionAlgebra sX U
  rw [← cancel_epi hU.isoSpec.inv, genφ, Category.assoc, Iso.inv_hom_id_assoc, ← Spec.map_comp,
    ← Category.assoc, hU.isoSpec_inv_ι,
    ← IsAffineOpen.SpecMap_appLE_fromSpec sX (isAffineOpen_top _) hU (by simp),
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  congr 1
  ext c
  exact (MvPolynomial.aeval t).commutes c

private lemma isPullback_genι :
    IsPullback (genι sX t hU) (genStructure sX t) (genφ sX t hU)
      (Spec.map (CommRingCat.ofHom (algebraMap (MvPolynomial (Fin d) k)
        (FractionRing (MvPolynomial (Fin d) k))))) := by
  letI := sectionAlgebra sX U
  letI : Algebra (MvPolynomial (Fin d) k) Γ(X, U) := (MvPolynomial.aeval t).toRingHom.toAlgebra
  letI : Algebra (FractionRing (MvPolynomial (Fin d) k)) (Localization (genSubmonoid sX t)) :=
    (fracToLoc k t).toAlgebra
  haveI : IsScalarTower (MvPolynomial (Fin d) k) (FractionRing (MvPolynomial (Fin d) k))
      (Localization (genSubmonoid sX t)) :=
    IsScalarTower.of_algebraMap_eq fun c => by
      rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin d) k) Γ(X, U)]
      exact (fracToLoc_algebraMap t c).symm
  haveI : IsLocalization (Algebra.algebraMapSubmonoid Γ(X, U)
      (nonZeroDivisors (MvPolynomial (Fin d) k))) (Localization (genSubmonoid sX t)) := by
    change IsLocalization (genSubmonoid sX t) _
    infer_instance
  haveI := Algebra.isPushout_of_isLocalization (R := MvPolynomial (Fin d) k)
    (nonZeroDivisors (MvPolynomial (Fin d) k)) (FractionRing (MvPolynomial (Fin d) k))
    Γ(X, U) (Localization (genSubmonoid sX t))
  have hpo := CommRingCat.isPushout_of_isPushout (MvPolynomial (Fin d) k) Γ(X, U)
    (FractionRing (MvPolynomial (Fin d) k)) (Localization (genSubmonoid sX t))
  refine (isPullback_SpecMap_of_isPushout _ _ _ _ hpo).of_iso (Iso.refl _) hU.isoSpec.symm
    (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp [genι]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp, genStructure]
    try rfl
  · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom, genφ, Iso.inv_hom_id_assoc]
    try rfl
  · simp

end Chart

section ChartPoint

open MMP.Mori (sectionAlgebra)

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) {U : X.Opens}
  {d : ℕ} (t : Fin d → Γ(X, U)) (hU : IsAffineOpen U)

private lemma isInducing_genι_comp : Topology.IsInducing (genι sX t hU ≫ U.ι) := by
  letI := sectionAlgebra sX U
  have h1 : Topology.IsInducing (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(X, U) (Localization (genSubmonoid sX t))))) :=
    PrimeSpectrum.localization_comap_isInducing (Localization (genSubmonoid sX t))
      (genSubmonoid sX t)
  rw [genι, Category.assoc]
  exact (hU.isoSpec.inv ≫ U.ι).isOpenEmbedding.isInducing.comp h1

private lemma preimage_eq_singleton_genPoint {x : X} (hxU : x ∈ U)
    (ht : letI := sectionAlgebra sX U;
      IsTranscendenceBasis k (Ideal.Quotient.mk (hU.primeIdealOf ⟨x, hxU⟩).asIdeal ∘ t))
    {V : Set X} (hV : closure {x} = V) :
    genι sX t hU ⁻¹' (U.ι ⁻¹' V) = {genPoint sX t hU hxU ht.1} := by
  ext q
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  have hp : (genι sX t hU ≫ U.ι) (genPoint sX t hU hxU ht.1) = x := by
    rw [Scheme.Hom.comp_apply, genι_genPoint]; rfl
  constructor
  · intro hq
    have hsp : (genι sX t hU ≫ U.ι) (genPoint sX t hU hxU ht.1) ⤳ (genι sX t hU ≫ U.ι) q := by
      rw [specializes_iff_mem_closure, hp, hV]
      exact hq
    have h := ((isInducing_genι_comp sX t hU).specializes_iff).1 hsp
    exact h.mem_closed (isClosed_genPoint sX t hU hxU ht) rfl
  · rintro rfl
    change (genι sX t hU ≫ U.ι) _ ∈ V
    rw [hp, ← hV]
    exact subset_closure rfl

end ChartPoint

private lemma finite_residueFieldMap_of_isClosed {K : Type u} [Field K] {S : Scheme.{u}}
    (sS : S ⟶ Spec (.of K)) [LocallyOfFiniteType sS] (p : S) (hp : IsClosed ({p} : Set S)) :
    (sS.residueFieldMap p).hom.Finite := by
  have h1 : IsFinite (S.fromSpecResidueField p ≫ sS) := by
    rw [isClosed_singleton_iff_isClosedImmersion] at hp
    rw [isFinite_iff_locallyOfFiniteType_of_jacobsonSpace]
    infer_instance
  rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField] at h1
  have h2 : IsFinite (Spec.map (sS.residueFieldMap p)) := IsFinite.of_comp _
    ((Spec (.of K)).fromSpecResidueField (sS p))
  exact (IsFinite.SpecMap_iff _).1 h2

/-! ### Divisors over `X` centred at `V` and divisors over the generic surface -/

section Places

private lemma valuation_comap_injective {L L' : Type u} [Field L] [Field L'] (f : L →+* L')
    (hf : Function.Surjective f) :
    Function.Injective (fun v : Valuation L' (WithZero (Multiplicative ℤ)) => v.comap f) := by
  intro v w h
  ext g
  obtain ⟨g, rfl⟩ := hf g
  exact congrArg (fun u : Valuation L (WithZero (Multiplicative ℤ)) => u g) h

private lemma comap_functionFieldMap_comp {A B C : Scheme.{u}} [IsIntegral A] [IsIntegral B]
    [IsIntegral C] (a : A ⟶ B) (b : B ⟶ C) [IsDominant a] [IsDominant b] [IsDominant (a ≫ b)]
    (w : Valuation A.functionField (WithZero (Multiplicative ℤ))) :
    (w.comap (functionFieldMap a)).comap (functionFieldMap b) =
      w.comap (functionFieldMap (a ≫ b)) := by
  ext g
  exact congrArg w (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply a b g)

/-- The valuation of a divisor over `X` dominates the local ring of `X` at the image of the generic
point of the divisor. -/
private lemma divisorOver_dominates {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] (D : DivisorOver k sX) {y : X}
    (hy : D.f D.E.genericPoint = y) :
    (∀ a : X.presheaf.stalk y, D.valuation (algebraMap _ X.functionField a) ≤ 1) ∧
      ∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk y),
        D.valuation (algebraMap _ X.functionField a) < 1 := by
  subst hy
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  have happ : ∀ a : X.presheaf.stalk (D.f D.E.genericPoint),
      D.valuation (algebraMap _ X.functionField a) = D.E.divisorialValuation
        (algebraMap D.E.localRing D.Y.functionField ((D.f.stalkMap D.E.genericPoint).hom a)) :=
    fun a => by
      change D.E.divisorialValuation (functionFieldMap D.f _) = _
      rw [MMP.Mori.functionFieldMap_algebraMap_stalk]
  refine ⟨fun a => ?_, fun a ha => ?_⟩
  · rw [happ, MMP.Mori.PrimeDivisor.divisorialValuation_le_one_iff]
    exact ⟨_, rfl⟩
  · rw [happ]
    have hm : (D.f.stalkMap D.E.genericPoint).hom a ∈ IsLocalRing.maximalIdeal D.E.localRing :=
      (IsLocalRing.mem_maximalIdeal _).2 fun hu =>
        (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit _ _ hu)
    haveI := D.E.isDiscreteValuationRing_localRing
    exact (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem
      (IsDiscreteValuationRing.maximalIdeal D.E.localRing) _).2 hm

/-- Domination of local rings passes to the restriction of a valuation along a dominant
morphism. -/
private lemma dominates_comap {Y Z : Scheme.{u}} [IsIntegral Y] [IsIntegral Z] (f : Y ⟶ Z)
    [IsDominant f] (w : Valuation Y.functionField (WithZero (Multiplicative ℤ))) (y : Y)
    (hle : ∀ a : Y.presheaf.stalk y, w (algebraMap _ Y.functionField a) ≤ 1)
    (hlt : ∀ a ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y),
      w (algebraMap _ Y.functionField a) < 1) :
    (∀ a : Z.presheaf.stalk (f y),
        (w.comap (functionFieldMap f)) (algebraMap _ Z.functionField a) ≤ 1) ∧
      ∀ a ∈ IsLocalRing.maximalIdeal (Z.presheaf.stalk (f y)),
        (w.comap (functionFieldMap f)) (algebraMap _ Z.functionField a) < 1 := by
  refine ⟨fun a => ?_, fun a ha => ?_⟩
  · rw [Valuation.comap_apply, MMP.Mori.functionFieldMap_algebraMap_stalk]
    exact hle _
  · rw [Valuation.comap_apply, MMP.Mori.functionFieldMap_algebraMap_stalk]
    exact hlt _ ((IsLocalRing.mem_maximalIdeal _).2 fun hu =>
      (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit _ a hu))

/-- The valuation of a divisor over `Y`, restricted along a birational dominant `f : Y ⟶ X`, is a
divisor of the function field of `X`. -/
private lemma isDivisorOfFunctionField_comap {k : Type u} [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsIntegral Y] (f : Y ⟶ X) [IsDominant f]
    (hf : Function.Bijective (functionFieldMap f)) (D : DivisorOver k (f ≫ sX)) :
    MMP.Flips.IsDivisorOfFunctionField k sX (D.valuation.comap (functionFieldMap f)) := by
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  letI := MMP.Mori.functionFieldAlgebra sX
  letI := MMP.Mori.functionFieldAlgebra (f ≫ sX)
  letI := MMP.Mori.functionFieldAlgebra (D.f ≫ f ≫ sX)
  letI := MMP.Mori.functionFieldMapAlgebra f
  letI := MMP.Mori.functionFieldMapAlgebra D.f
  haveI := MMP.Mori.isScalarTower_functionFieldMap sX f
  haveI := MMP.Mori.isScalarTower_functionFieldMap (f ≫ sX) D.f
  let e₀ : X.functionField →ₐ[k] D.Y.functionField :=
    (IsScalarTower.toAlgHom k Y.functionField D.Y.functionField).comp
      (IsScalarTower.toAlgHom k X.functionField Y.functionField)
  have he : Function.Bijective e₀ := D.isBirationalMorphism.functionFieldMap_bijective.comp hf
  refine ⟨D.Y, D.f ≫ f ≫ sX, D.isNormalVariety, D.E, AlgEquiv.ofBijective e₀ he, ?_⟩
  ext g
  rfl

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) {U : X.Opens}
  {d : ℕ} (t : Fin d → Γ(X, U)) (hU : IsAffineOpen U)

private lemma bijective_functionFieldMap_genι_comp [IsIntegral X] [Nonempty U]
    [IsIntegral (Spec (genRing sX t))] [IsDominant (genι sX t hU)]
    [IsDominant (genι sX t hU ≫ U.ι)] :
    Function.Bijective (functionFieldMap (genι sX t hU ≫ U.ι)) := by
  haveI := isDominant_opens_ι U
  have h := (bijective_functionFieldMap_genι sX t hU).comp (functionFieldMap_opens_ι_bijective U)
  convert h using 1
  funext a
  exact (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply _ _ a).symm

end Places

/-- **A divisor over the generic surface gives a divisor over `X`.** The spread divisor over `U`
has a valuation of `k(X)` which is a divisor of the function field dominating the local ring of
`X` at the image `y` of the generic point; it is realized by a proper divisor over `X` whose
generic point maps to `y`. -/
private theorem exists_properDivisorOver_X_of_genSurface
    {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [IsIntegral X] (hXv : IsNormalVariety k sX)
    {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U] [IsIntegral U] {d : ℕ}
    (t : Fin d → Γ(X, U))
    [IsIntegral (Spec (genRing sX t))] [IsDominant (genι sX t hU)]
    [IsDominant (genι sX t hU ≫ U.ι)]
    (D : DivisorOver (genField k d) (genStructure sX t)) :
    ∃ D'' : DivisorOver k sX, IsProper D''.f ∧
      D''.valuation = D.valuation.comap (functionFieldMap (genι sX t hU ≫ U.ι)) ∧
      D''.f D''.E.genericPoint = U.ι (genι sX t hU (D.f D.E.genericPoint)) := by
  haveI : AlgebraicGeometry.IsVariety k sX := hXv.1
  haveI := isDominant_opens_ι U
  obtain ⟨D', -, hD'v, hD'x⟩ := exists_properDivisorOver_of_genSurface sX hXv hU t D
  have hv : D'.valuation.comap (functionFieldMap U.ι) =
      D.valuation.comap (functionFieldMap (genι sX t hU ≫ U.ι)) := by
    rw [hD'v, comap_functionFieldMap_comp]
  have hdiv := isDivisorOfFunctionField_comap sX U.ι (functionFieldMap_opens_ι_bijective U) D'
  have hdom := dominates_comap U.ι D'.valuation _ (divisorOver_dominates D' hD'x).1
    (divisorOver_dominates D' hD'x).2
  obtain ⟨D'', -, hD''v, hD''x⟩ :=
    MMP.Flips.exists_properDivisorOver_isProjective_of_dominates sX hdiv _ hdom.1 hdom.2
  exact ⟨D''.toDivisorOver, D''.isProper, hD''v.trans hv, hD''x⟩

/-- **A divisor over `X` centred at `V` gives a divisor over the generic surface centred at `p`.**
Transported along `k(X) ≅ k(S)`, its valuation `v` dominates `𝒪_{S,p} ≅ 𝒪_{X,x}`, is trivial on
`K`, and its valuation ring is essentially of finite type over `k`, hence over `K`; so it is a
divisor of `K(S)`, realized by a proper divisor over `S` with centre `p`. -/
private theorem exists_divisorOver_genSurface_of_divisorOver
    {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [IsIntegral X] (hXv : IsNormalVariety k sX)
    {x : X} {U : X.Opens} (hU : IsAffineOpen U) (hxU : x ∈ U) [IsIntegral U] {d : ℕ}
    (t : Fin d → Γ(X, U))
    (ht : letI := sectionAlgebra sX U;
      IsTranscendenceBasis k (Ideal.Quotient.mk (hU.primeIdealOf ⟨x, hxU⟩).asIdeal ∘ t))
    [IsIntegral (Spec (genRing sX t))] [IsDominant (genι sX t hU)]
    [IsDominant (genι sX t hU ≫ U.ι)]
    (hvar : IsNormalVariety (genField k d) (genStructure sX t))
    (D' : DivisorOver k sX) (hD'x : D'.f D'.E.genericPoint = x) :
    ∃ D : DivisorOver (genField k d) (genStructure sX t), IsProper D.f ∧
      (D.center : Set (Spec (genRing sX t))) = {genPoint sX t hU hxU ht.1} ∧
      D.valuation.comap (functionFieldMap (genι sX t hU ≫ U.ι)) = D'.valuation := by
  classical
  haveI : LocallyOfFiniteType sX := hXv.1.toLocallyOfFiniteType
  haveI : Nonempty U := ⟨⟨x, hxU⟩⟩
  haveI := isDominant_opens_ι U
  haveI := D'.isIntegral
  haveI := D'.isNormal
  haveI := D'.isLocallyNoetherian
  haveI := D'.isDominant
  haveI : LocallyOfFiniteType (D'.f ≫ sX) := D'.isNormalVariety.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (genStructure sX t) := locallyOfFiniteType_genStructure sX t hU
  haveI : AlgebraicGeometry.IsVariety (genField k d) (genStructure sX t) := hvar.1
  set S := Spec (genRing sX t) with hSdef
  set K := genField k d with hKdef
  set p := genPoint sX t hU hxU ht.1 with hp
  set g := genι sX t hU ≫ U.ι with hg
  have hgp : g p = x := by rw [hg, Scheme.Hom.comp_apply, genι_genPoint]; rfl
  haveI hiso : IsIso (g.stalkMap p) := isIso_stalkMap_genι_comp sX t hU p
  have hθ : Function.Bijective (functionFieldMap g) := bijective_functionFieldMap_genι_comp sX t hU
  set θe := RingEquiv.ofBijective (functionFieldMap g) hθ with hθe
  set v : Valuation S.functionField (WithZero (Multiplicative ℤ)) :=
    D'.valuation.comap (θe.symm : S.functionField →+* X.functionField) with hv
  have hvθ : v.comap (functionFieldMap g) = D'.valuation := by
    ext a
    change D'.valuation (θe.symm (θe a)) = _
    rw [RingEquiv.symm_apply_apply]
  -- domination of `𝒪_{S,p}`
  have hdom := divisorOver_dominates D' (hD'x.trans hgp.symm)
  have hvst : ∀ b : X.presheaf.stalk (g p),
      v (algebraMap _ S.functionField ((g.stalkMap p).hom b)) =
        D'.valuation (algebraMap _ X.functionField b) := by
    intro b
    rw [← MMP.Mori.functionFieldMap_algebraMap_stalk]
    change D'.valuation (θe.symm (θe _)) = _
    rw [RingEquiv.symm_apply_apply]
  have hpre : ∀ a : S.presheaf.stalk p, ∃ b, (g.stalkMap p).hom b = a := fun a =>
    ⟨(inv (g.stalkMap p)).hom a, by
      rw [← CommRingCat.comp_apply, IsIso.inv_hom_id, CommRingCat.id_apply]⟩
  have hle : ∀ a : S.presheaf.stalk p, v (algebraMap _ S.functionField a) ≤ 1 := by
    intro a
    obtain ⟨b, rfl⟩ := hpre a
    rw [hvst]
    exact hdom.1 b
  have hlt : ∀ a ∈ IsLocalRing.maximalIdeal (S.presheaf.stalk p),
      v (algebraMap _ S.functionField a) < 1 := by
    intro a ha
    obtain ⟨b, rfl⟩ := hpre a
    rw [hvst]
    exact hdom.2 b ((IsLocalRing.mem_maximalIdeal _).2 fun hu =>
      (IsLocalRing.mem_maximalIdeal _).1 ha (hu.map _))
  -- the valuation ring as a `K`-subalgebra
  letI := MMP.Mori.functionFieldAlgebra (genStructure sX t)
  letI := MMP.Mori.stalkAlgebra (genStructure sX t) p
  haveI := MMP.Mori.isScalarTower_stalk_functionField (genStructure sX t) p
  have hK : ∀ c : K, v (algebraMap K S.functionField c) ≤ 1 := by
    intro c
    rw [IsScalarTower.algebraMap_apply K (S.presheaf.stalk p)]
    exact hle _
  let O : Subalgebra K S.functionField :=
    { toSubsemiring := v.integer.toSubsemiring, algebraMap_mem' := hK }
  let ρ : O →ₐ[K] S.functionField := O.val
  have hρ : ∀ a, v a ≤ 1 ↔ a ∈ Set.range ρ := fun a =>
    ⟨fun h => ⟨⟨a, h⟩, rfl⟩, by rintro ⟨o, rfl⟩; exact o.2⟩
  -- `O` is the image of `𝒪_{Y,E}`, essentially of finite type over `k`
  set φD := RingEquiv.ofBijective (functionFieldMap D'.f)
    D'.isBirationalMorphism.functionFieldMap_bijective
  let ψ0 : D'.E.localRing →+* S.functionField :=
    (θe : X.functionField →+* S.functionField).comp
      ((φD.symm : D'.Y.functionField →+* X.functionField).comp
        (algebraMap D'.E.localRing D'.Y.functionField))
  have hψv : ∀ o, v (ψ0 o) =
      D'.E.divisorialValuation (algebraMap D'.E.localRing D'.Y.functionField o) := by
    intro o
    change D'.valuation (θe.symm (θe _)) = _
    rw [RingEquiv.symm_apply_apply]
    change D'.E.divisorialValuation (φD (φD.symm _)) = _
    rw [RingEquiv.apply_symm_apply]
  have hψO : ∀ o, ψ0 o ∈ O := fun o => by
    change v (ψ0 o) ≤ 1
    rw [hψv, MMP.Mori.PrimeDivisor.divisorialValuation_le_one_iff]
    exact ⟨o, rfl⟩
  have hψsurj : ∀ a ∈ O, ∃ o, ψ0 o = a := by
    intro a ha
    have h : D'.E.divisorialValuation (φD (θe.symm a)) ≤ 1 := ha
    obtain ⟨o, ho⟩ := (MMP.Mori.PrimeDivisor.divisorialValuation_le_one_iff _ _).1 h
    refine ⟨o, ?_⟩
    change θe (φD.symm (algebraMap _ _ o)) = a
    rw [ho, RingEquiv.symm_apply_apply, RingEquiv.apply_symm_apply]
  letI : Algebra k O := ((algebraMap K O).comp (algebraMap k K)).toAlgebra
  haveI : IsScalarTower k K O := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI := MMP.Mori.stalkAlgebra (D'.f ≫ sX) D'.E.genericPoint
  haveI : Algebra.EssFiniteType k D'.E.localRing :=
    essFiniteType_stalkAlgebra (D'.f ≫ sX) D'.E.genericPoint
  have hψk : ∀ c : k, ψ0 (algebraMap k D'.E.localRing c) =
      algebraMap K S.functionField (algebraMap k K c) := by
    intro c
    letI := MMP.Mori.functionFieldAlgebra sX
    letI := MMP.Mori.functionFieldAlgebra (D'.f ≫ sX)
    letI := MMP.Mori.functionFieldMapAlgebra D'.f
    haveI h1 := MMP.Mori.isScalarTower_stalk_functionField (D'.f ≫ sX) D'.E.genericPoint
    haveI h2 := MMP.Mori.isScalarTower_functionFieldMap sX D'.f
    have e1 : algebraMap D'.E.localRing D'.Y.functionField (algebraMap k D'.E.localRing c) =
        φD (algebraMap k X.functionField c) := by
      rw [← IsScalarTower.algebraMap_apply k D'.E.localRing D'.Y.functionField,
        IsScalarTower.algebraMap_apply k X.functionField D'.Y.functionField]
      rfl
    change θe (φD.symm _) = _
    rw [e1, RingEquiv.symm_apply_apply]
    letI := MMP.Mori.functionFieldAlgebra (g ≫ sX)
    letI := MMP.Mori.functionFieldMapAlgebra g
    haveI h3 := MMP.Mori.isScalarTower_functionFieldMap sX g
    haveI h4 := isScalarTower_stalkAlgebra_comp (genStructure sX t) (g ≫ sX)
      (by rw [hg, Category.assoc]; exact genι_comp_eq sX t hU) (genericPoint S)
    change algebraMap X.functionField S.functionField (algebraMap k X.functionField c) = _
    rw [← IsScalarTower.algebraMap_apply k X.functionField S.functionField,
      IsScalarTower.algebraMap_apply k K S.functionField]
  let ψ : D'.E.localRing →ₐ[k] O :=
    { toRingHom := ψ0.codRestrict O hψO
      commutes' := fun c => Subtype.ext (hψk c) }
  have hsurj : Function.Surjective ψ := by
    rintro ⟨a, ha⟩
    obtain ⟨o, ho⟩ := hψsurj a ha
    exact ⟨o, Subtype.ext ho⟩
  haveI : Algebra.EssFiniteType k O := Algebra.EssFiniteType.of_surjective ψ hsurj
  haveI : Algebra.EssFiniteType K O := Algebra.EssFiniteType.of_comp k K O
  -- generators of `Γ(S, ⊤)` over `K`
  letI := sectionAlgebra (genStructure sX t) ⊤
  haveI := MMP.Mori.finiteType_sectionAlgebra (genStructure sX t) (isAffineOpen_top S)
  obtain ⟨s₀, hs₀⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra K Γ(S, ⊤)).FG)
  haveI := MMP.Mori.isScalarTower_section_functionField (genStructure sX t) (⊤ : S.Opens)
  let γ : Γ(S, ⊤) →ₐ[K] S.functionField := IsScalarTower.toAlgHom K _ _
  haveI : IsFractionRing Γ(S, ⊤) S.functionField :=
    functionField_isFractionRing_of_isAffineOpen S ⊤ (isAffineOpen_top S)
  have hγ : ∀ a, γ a ∈ Algebra.adjoin K ((s₀.image γ : Finset _) : Set S.functionField) := by
    intro a
    have h1 : γ a ∈ (Algebra.adjoin K (s₀ : Set Γ(S, ⊤))).map γ := by
      rw [hs₀]
      exact ⟨a, trivial, rfl⟩
    rw [AlgHom.map_adjoin] at h1
    simpa using h1
  have hT : ∀ b ∈ s₀.image γ, v b ≤ 1 := by
    intro b hb
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hb
    change v (algebraMap Γ(S, ⊤) S.functionField a) ≤ 1
    rw [show algebraMap Γ(S, ⊤) S.functionField a =
      algebraMap _ S.functionField (S.presheaf.germ ⊤ p trivial a) from
        (Scheme.algebraMap_germ_eq_germToFunctionField (X := S) (U := ⊤) (x := p)
          (Opens.mem_top p) a).symm]
    exact hle _
  have hfrac : ∀ b : S.functionField,
      ∃ a ∈ Algebra.adjoin K ((s₀.image γ : Finset _) : Set S.functionField),
        ∃ c ∈ Algebra.adjoin K ((s₀.image γ : Finset _) : Set S.functionField),
          c ≠ 0 ∧ b * c = a := by
    intro b
    obtain ⟨a, c, hc, rfl⟩ := IsFractionRing.div_surjective (A := Γ(S, ⊤)) b
    have hc0 : algebraMap Γ(S, ⊤) S.functionField c ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hc
    exact ⟨_, hγ a, _, hγ c, hc0, div_mul_cancel₀ _ hc0⟩
  have hπ : ∃ π, v π = WithZero.exp (-1) := by
    haveI := D'.E.isDiscreteValuationRing_localRing
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible D'.E.localRing
    exact ⟨ψ0 ϖ, by rw [hψv]; exact D'.E.divisorialValuation_algebraMap_of_irreducible hϖ⟩
  have hdiv : MMP.Flips.IsDivisorOfFunctionField K (genStructure sX t) v :=
    isDivisorOfFunctionField_of_essFiniteType (genStructure sX t) v O ρ hρ (s₀.image γ) hT
      hfrac hπ
  obtain ⟨D, -, hDv, hDx⟩ :=
    MMP.Flips.exists_properDivisorOver_isProjective_of_dominates (genStructure sX t) hdiv p hle hlt
  refine ⟨D.toDivisorOver, D.isProper, ?_, ?_⟩
  · rw [D.toDivisorOver.center_eq_closure_genericPoint]
    change closure {D.f D.E.genericPoint} = _
    rw [hDx, (isClosed_genPoint sX t hU hxU ht).closure_eq]
  · change D.valuation.comap _ = _
    rw [hDv]
    exact hvθ

/-- **Log discrepancies over an open subscheme.** For a pair `(X, B)`, a proper divisor `D` over
`X` whose centre meets `U` and a proper divisor `D'` over `U` with the same valuation have the same
log discrepancies, for `B` and `B|_U` respectively. -/
private theorem isLogDiscrepancy_open_iff {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {B : QDivisor X} (hB : MMP.Mori.IsPair sX B) {n : ℕ} (hn : topologicalKrullDim X = n)
    (U : X.Opens) [Nonempty U] [IsIntegral U] [IsLocallyNoetherian U] [IsNormal U]
    (D : DivisorOver k sX) (hDp : IsProper D.f) (hDU : D.f D.E.genericPoint ∈ U)
    (D' : DivisorOver k (U.ι ≫ sX)) (hD'p : IsProper D'.f)
    (hv : D.valuation = D'.valuation.comap (functionFieldMap U.ι)) (a : ℝ) :
    MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B) D a ↔
      MMP.Intersection.IsLogDiscrepancy (U.ι ≫ sX) n
        (QDivisor.toRDivisor (MMP.Mori.inverseTransformDivisor U.ι B)) D' a := by
  classical
  haveI := isDominant_opens_ι U
  obtain ⟨hXv, n0, K, hK, hQ⟩ := hB
  have hn0 : n0 = n := by exact_mod_cast hK.topologicalKrullDim_eq.symm.trans hn
  subst hn0
  have hPW : MMP.Mori.IsPairWith sX n0 K B := ⟨hXv, hK, hQ⟩
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy ⟨hXv, n0, K, hK, hQ⟩ hK D
  have hcen : ((D.center : Set X) ∩ U).Nonempty :=
    ⟨_, by rw [D.center_eq_closure_genericPoint]; exact subset_closure rfl, hDU⟩
  obtain ⟨hY, hf, E', -, hval, hiff⟩ :=
    MMP.Mori.DivisorOver.exists_restrict_isDiscrepancy_iff hPW D U hcen
  have hcU := (hiff c).1 hc
  haveI : IsProper (D.f ∣_ U) := by haveI := hDp; infer_instance
  obtain ⟨c', hc'⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hcU.isPair hcU.2.1 D'
  have hDUv : DivisorOver.valuation (⟨_, D.f ∣_ U, hY, hf, E'⟩ : DivisorOver k (U.ι ≫ sX)) =
      D'.valuation :=
    valuation_comap_injective (functionFieldMap U.ι) (functionFieldMap_opens_ι_bijective U).2
      (hval.symm.trans hv)
  have hcc : (c' : ℝ) = c := by
    have h1 := (MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy hc' (1 + c')).2
      ⟨hD'p, rfl⟩
    have h2 := (MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy hcU (1 + c)).2
      ⟨inferInstance, rfl⟩
    have := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq h1 h2 hDUv.symm
    linarith
  rw [MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy hc,
    inverseTransformDivisor_ι_eq_restrictOpen,
    MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy hc', hcc]
  exact ⟨fun h => ⟨hD'p, h.2⟩, fun h => ⟨hDp, h.2⟩⟩

/-! ### Centres, constants and the residue field -/

/-- The centre of a divisor over a scheme is the closure of a point `y` exactly when the generic
point of the divisor maps to `y`. -/
private lemma irreducibleSetEquivPoints_symm_eq_center_iff {k : Type u} [Field k]
    {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} (D : DivisorOver k sY) (y : Y) :
    irreducibleSetEquivPoints.symm y = D.center ↔ D.f D.E.genericPoint = y := by
  constructor
  · intro h
    have h' : closure ({y} : Set Y) = closure {D.f D.E.genericPoint} := by
      rw [← D.center_eq_closure_genericPoint, ← h]
      rfl
    exact ((inseparable_iff_closure_eq.2 h').eq).symm
  · intro h
    refine SetLike.coe_injective ?_
    change closure {y} = (D.center : Set Y)
    rw [D.center_eq_closure_genericPoint, h]

/-- The valuation of a prime divisor is trivial on the germs of global units. -/
private lemma divisorialValuation_germToFunctionField_of_isUnit {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (E : MMP.Mori.PrimeDivisor Y) {b : Γ(Y, ⊤)}
    (hb : IsUnit b) : E.divisorialValuation (Y.germToFunctionField ⊤ b) = 1 := by
  have hle : ∀ c : Γ(Y, ⊤), E.divisorialValuation (Y.germToFunctionField ⊤ c) ≤ 1 := by
    intro c
    rw [MMP.Mori.PrimeDivisor.divisorialValuation_le_one_iff,
      ← Scheme.algebraMap_germ_eq_germToFunctionField (X := Y) (U := ⊤) (x := E.genericPoint)
        (Opens.mem_top _) c]
    exact ⟨_, rfl⟩
  obtain ⟨b, rfl⟩ := hb
  refine le_antisymm (hle _) ?_
  calc (1 : WithZero (Multiplicative ℤ))
    _ = E.divisorialValuation (Y.germToFunctionField ⊤ ↑b) *
        E.divisorialValuation (Y.germToFunctionField ⊤ ↑b⁻¹) := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    _ ≤ E.divisorialValuation (Y.germToFunctionField ⊤ ↑b) * 1 := by
      gcongr
      exact hle _
    _ = _ := mul_one _

/-- **The valuation of a divisor over a `K`-scheme is trivial on `K^*`.** -/
private lemma valuation_const_eq_one_of_divisorOver {K : Type u} [Field K] {S : Scheme.{u}}
    {sS : S ⟶ Spec (.of K)} [IsIntegral S] (D : DivisorOver K sS) {c : K} (hc : c ≠ 0) :
    D.valuation (S.germToFunctionField ⊤ (sS.appTop ((Scheme.ΓSpecIso (.of K)).inv c))) = 1 := by
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  change D.E.divisorialValuation (functionFieldMap D.f _) = 1
  rw [functionFieldMap_germToFunctionField_top]
  refine divisorialValuation_germToFunctionField_of_isUnit D.E ?_
  exact (((isUnit_iff_ne_zero.2 hc).map (Scheme.ΓSpecIso (.of K)).inv.hom).map
    sS.appTop.hom).map D.f.appTop.hom

/-- The residue field of `Spec K` at its point is `K`. -/
private lemma surjective_ΓSpecIso_inv_Γevaluation (K : Type u) [Field K] (q : Spec (.of K)) :
    Function.Surjective ((Scheme.ΓSpecIso (.of K)).inv ≫ (Spec (.of K)).Γevaluation q) := by
  haveI : q.asIdeal.IsPrime := q.2
  have h := Scheme.Spec.algebraMap_residueFieldIso_inv (.of K) q
  have e : (Scheme.ΓSpecIso (.of K)).inv ≫ (Spec (.of K)).Γevaluation q =
      CommRingCat.ofHom (algebraMap K q.asIdeal.ResidueField) ≫
        (Scheme.Spec.residueFieldIso (.of K) q).inv := by
    rw [h]; rfl
  haveI : q.asIdeal.IsMaximal := q.isPrime.isMaximal'
  rw [e]
  exact ((ConcreteCategory.bijective_of_isIso (Scheme.Spec.residueFieldIso (.of K) q).inv).2).comp
    (Ideal.algebraMap_residueField_surjective _)

/-- **The residue field of a closed point of a scheme of finite type over `K` is finite and
separable over `K`** (characteristic zero). -/
private lemma finite_isSeparable_residueField_of_isClosed {K : Type u} [Field K] [CharZero K]
    {S : Scheme.{u}} (sS : S ⟶ Spec (.of K)) [LocallyOfFiniteType sS] (p : S)
    (hp : IsClosed ({p} : Set S)) :
    letI : Algebra K (S.residueField p) :=
      ((S.Γevaluation p).hom.comp
        (sS.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom)).toAlgebra
    Module.Finite K (S.residueField p) ∧ Algebra.IsSeparable K (S.residueField p) := by
  letI : Algebra K (S.residueField p) :=
    ((S.Γevaluation p).hom.comp
      (sS.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom)).toAlgebra
  have h1 := finite_residueFieldMap_of_isClosed sS p hp
  have h2 : ((Scheme.ΓSpecIso (.of K)).inv ≫ (Spec (.of K)).Γevaluation (sS p)).hom.Finite :=
    RingHom.Finite.of_surjective _ (surjective_ΓSpecIso_inv_Γevaluation K (sS p))
  have he : algebraMap K (S.residueField p) = (sS.residueFieldMap p).hom.comp
      ((Scheme.ΓSpecIso (.of K)).inv ≫ (Spec (.of K)).Γevaluation (sS p)).hom := by
    have := Scheme.Γevaluation_naturality sS p
    rw [← CommRingCat.hom_comp, Category.assoc, this]
    rfl
  have hfin : Module.Finite K (S.residueField p) := by
    change (algebraMap K (S.residueField p)).Finite
    rw [he]
    exact h1.comp h2
  refine ⟨hfin, ?_⟩
  haveI := hfin
  exact Algebra.IsAlgebraic.isSeparable_of_perfectField

/-! ### The generic fibre of a function, as a fibre product with the affine line -/

section AffineLine

/-- `Spec k[t₁] ≅ 𝔸¹_k`. -/
private noncomputable def specMvPolynomialFinOneIso (k : Type) [Field k] :
    Spec (.of (MvPolynomial (Fin 1) k)) ≅ AffineSpace Unit (Spec (.of k)) :=
  Scheme.Spec.mapIso
      (MvPolynomial.renameEquiv k finOneEquiv.symm).toRingEquiv.toCommRingCatIso.op ≪≫
    (AffineSpace.SpecIso Unit (.of k)).symm

private lemma specMvPolynomialFinOneIso_hom_over (k : Type) [Field k] :
    (specMvPolynomialFinOneIso k).hom ≫ AffineSpace Unit (Spec (.of k)) ↘ Spec (.of k) =
      Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin 1) k))) := by
  simp only [specMvPolynomialFinOneIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    AffineSpace.SpecIso_inv_over]
  simp only [Scheme.Spec_map, Functor.mapIso_hom, Iso.op_hom, Quiver.Hom.unop_op,
    ← Spec.map_comp]
  congr 1
  ext c
  simp [MvPolynomial.algebraMap_eq]

private lemma specMvPolynomialFinOneIso_hom_appTop_coord (k : Type) [Field k] :
    (specMvPolynomialFinOneIso k).hom.appTop (AffineSpace.coord (Spec (.of k)) ()) =
      (Scheme.ΓSpecIso _).inv (MvPolynomial.X 0) := by
  rw [specMvPolynomialFinOneIso, Iso.trans_hom, Iso.symm_hom, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply, AffineSpace.SpecIso_inv_appTop_coord]
  simp only [Scheme.Spec_map, Functor.mapIso_hom, Iso.op_hom, Quiver.Hom.unop_op]
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
  congr 1
  simp only [AlgEquiv.toRingEquiv_toRingHom, RingEquiv.toCommRingCatIso_hom,
    CommRingCat.hom_ofHom, RingHom.coe_coe, MvPolynomial.renameEquiv_apply,
    MvPolynomial.rename_X]
  exact congrArg MvPolynomial.X (Subsingleton.elim _ _)

private lemma SpecMap_algebraMap_comp_specMvPolynomialFinOneIso {k : Type} [Field k] (K : Type)
    [Field K] [Algebra (MvPolynomial (Fin 1) k) K] [Algebra k K]
    [IsScalarTower k (MvPolynomial (Fin 1) k) K] :
    Spec.map (CommRingCat.ofHom (algebraMap (MvPolynomial (Fin 1) k) K)) ≫
        (specMvPolynomialFinOneIso k).hom =
      AffineSpace.homOfVector (Spec.map (CommRingCat.ofHom (algebraMap k K)))
        (fun _ : Unit => (Scheme.ΓSpecIso (.of K)).inv
          (algebraMap (MvPolynomial (Fin 1) k) K (MvPolynomial.X 0))) := by
  ext1
  · rw [Category.assoc, specMvPolynomialFinOneIso_hom_over, AffineSpace.homOfVector_over,
      ← Spec.map_comp]
    congr 1
    ext c
    exact (IsScalarTower.algebraMap_apply k (MvPolynomial (Fin 1) k) K c).symm
  · rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, specMvPolynomialFinOneIso_hom_appTop_coord,
      AffineSpace.homOfVector_appTop_coord, ← CommRingCat.comp_apply,
      ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
    rfl

open MMP.Mori (sectionAlgebra) in
/-- The structure morphism `Γ(X, U) ← k`, transported to `Γ(U, ⊤)`, is that of `U ⟶ Spec k`. -/
private lemma sectionAlgebra_comp_topIso_inv {k : Type} [Field k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) (U : X.Opens) :
    (((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appLE ⊤ U (by simp)) ≫ U.topIso.inv) =
      (Scheme.ΓSpecIso (.of k)).inv ≫ (U.ι ≫ sX).appTop := by
  rw [Category.assoc, Scheme.Hom.comp_appTop]
  congr 1
  simp only [Scheme.Hom.appLE, Scheme.Opens.topIso_inv, Scheme.Opens.ι_appTop, Scheme.Hom.appTop]
  refine (Category.assoc _ _ _).trans ?_
  congr 1
  refine (X.presheaf.map_comp _ _).symm.trans ?_
  rfl

private lemma genφ_comp_specMvPolynomialFinOneIso {k : Type} [Field k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) {U : X.Opens} (t : Fin 1 → Γ(X, U)) (hU : IsAffineOpen U) :
    genφ sX t hU ≫ (specMvPolynomialFinOneIso k).hom =
      AffineSpace.homOfVector (U.ι ≫ sX) (fun _ : Unit => U.topIso.inv (t 0)) := by
  ext1
  · rw [Category.assoc, specMvPolynomialFinOneIso_hom_over, AffineSpace.homOfVector_over,
      genφ_comp]
  · rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, specMvPolynomialFinOneIso_hom_appTop_coord,
      AffineSpace.homOfVector_appTop_coord, genφ, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      ← CommRingCat.comp_apply _ (Spec.map _).appTop, ← Scheme.ΓSpecIso_inv_naturality,
      CommRingCat.comp_apply]
    letI := MMP.Mori.sectionAlgebra sX U
    have : (CommRingCat.ofHom (MvPolynomial.aeval (R := k) t).toRingHom) (MvPolynomial.X 0) =
        t 0 := MvPolynomial.aeval_X t 0
    rw [this, IsAffineOpen.isoSpec_hom_appTop, CommRingCat.comp_apply, Iso.inv_hom_id_apply]

end AffineLine

end Proof_lem_mmp_indexc_generic_curve_surface

namespace MMP.Fourfold

open MMP.Mori (QDivisor DivisorOver IsNormalVariety)
open Proof_lem_mmp_indexc_generic_curve_surface
open MMP.Mori (sectionAlgebra)

/-- **The surface at the generic point of a curve.** Let `(X, B)` be an effective pair on a
normal threefold over `ℂ` (`MMP.Fourfold.IsPair`) and `V ⊆ X` an irreducible closed curve with
generic point `η_V`. There are an affine open `U ∋ η_V`, a regular function `u` on `U`
transcendental over `ℂ`, a field `K = ℂ(t)` and the generic fibre `S` of `u : U ⟶ 𝔸¹` (the
pullback along `t : Spec K ⟶ 𝔸¹`, with projections `ι : S ⟶ U` and `s_S : S ⟶ Spec K`) such that:
1. `S` is a normal affine surface over `K` whose function field is `ℂ(X)` through `ι`, and
   `ι⁻¹(V) = {x}` for a closed point `x` with `ι x = η_V`, `𝒪_{S,x} ≅ 𝒪_{X,η_V}` through `ι`,
   and residue field finite separable over `K`; `x` is the only point over `η_V`;
2. there is an effective pair `(S, B_S)` over `K` (`MMP.Fourfold.IsCharZeroPair`) whose
   coefficient along a prime divisor `P` of `S` is that of `B` along the prime divisor of `X`
   with generic point `ι(η_P)`;
3. every normalized divisorial valuation `ξ` of `ℂ(X)` with centre `V` is trivial on `K^*`, is a
   normalized divisorial valuation over `S` with centre `x`, and `a(ξ; S, B_S) = a(ξ; X, B)`;
4. every normalized divisorial valuation `w` of `K(S) = ℂ(X)` over `S` is a normalized divisorial
   valuation over `U` with `a(w; U, B|_U) = a(w; S, B_S)`, and its centre on `S` is `x` if and
   only if its centre on `U` is `V ∩ U`.
In particular a valuation of `ℂ(X)` has centre `x` on `S` if and only if it has centre `V` on
`X`, and `(S, B_S)` is klt (`MMP.Fourfold.IsCharZeroKltPair`) when `(X, B)` is klt. -/
@[mmp "lem_mmp_indexc_generic_curve_surface"]
public theorem exists_generic_surface_of_curve
    {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {B : QDivisor X} (hB : IsPair sX B) (hX : topologicalKrullDim X = 3)
    (V : IrreducibleCloseds X) (hV : topologicalKrullDim (V : Set X) = 1) :
    ∃ (U : X.Opens) (hU : V.isIrreducible.genericPoint ∈ U), IsAffineOpen U ∧
      ∃ (_ : IsIntegral U) (_ : IsLocallyNoetherian U) (_ : IsNormal U),
      ∃ u : Γ(U, ⊤),
        (letI : Algebra ℂ Γ(U, ⊤) :=
          ((U.ι ≫ sX).appTop.hom.comp (Scheme.ΓSpecIso (.of ℂ)).inv.hom).toAlgebra
         Transcendental ℂ u) ∧
      ∃ (K : Type) (_ : Field K) (_ : Algebra ℂ K) (t : K),
        Transcendental ℂ t ∧ IntermediateField.adjoin ℂ {t} = ⊤ ∧
      ∃ (S : Scheme.{0}) (ι : S ⟶ U) (sS : S ⟶ Spec (.of K)),
        IsPullback ι sS (AffineSpace.homOfVector (U.ι ≫ sX) (fun _ : Unit => u))
          (AffineSpace.homOfVector (Spec.map (CommRingCat.ofHom (algebraMap ℂ K)))
            (fun _ : Unit => (Scheme.ΓSpecIso (.of K)).inv t)) ∧
      ∃ (_ : IsIntegral S) (_ : IsLocallyNoetherian S) (_ : IsNormal S) (_ : IsDominant ι),
        -- (1)
        IsAffine S ∧ IsNormalVariety K sS ∧ topologicalKrullDim S = 2 ∧
        Function.Bijective (functionFieldMap (ι ≫ U.ι)) ∧
      ∃ x : S, IsClosed ({x} : Set S) ∧ ι ⁻¹' (U.ι ⁻¹' (V : Set X)) = {x} ∧
        ι x = ⟨V.isIrreducible.genericPoint, hU⟩ ∧ IsIso (ι.stalkMap x) ∧
        (∀ y : S, ι y = ⟨V.isIrreducible.genericPoint, hU⟩ → y = x) ∧
        (letI : Algebra K (S.residueField x) :=
          ((S.Γevaluation x).hom.comp
            (sS.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom)).toAlgebra
         Module.Finite K (S.residueField x) ∧ Algebra.IsSeparable K (S.residueField x)) ∧
      -- (2)
      ∃ BS : QDivisor S, IsCharZeroPair sS BS ∧
        (∀ P : MMP.Mori.PrimeDivisor S, ∃ P' : MMP.Mori.PrimeDivisor X,
          P'.genericPoint = U.ι (ι P.genericPoint) ∧ BS.coeff P = B.coeff P') ∧
      -- (3)
      (∀ ξ : Valuation S.functionField (WithZero (Multiplicative ℤ)),
        MMP.Intersection.IsCentre ℂ sX (ξ.comap (functionFieldMap (ι ≫ U.ι))) V →
          (∀ c : K, c ≠ 0 → ξ (S.germToFunctionField ⊤
            (sS.appTop ((Scheme.ΓSpecIso (.of K)).inv c))) = 1) ∧
          MMP.Intersection.IsNormalizedDivisorialValuation K sS ξ ∧
          MMP.Intersection.IsCentre K sS ξ (irreducibleSetEquivPoints.symm x) ∧
          ∀ (D : DivisorOver K sS) (D' : DivisorOver ℂ sX), IsProper D.f → IsProper D'.f →
            D.valuation = ξ → D'.valuation = ξ.comap (functionFieldMap (ι ≫ U.ι)) →
            ∀ a : ℝ, MMP.Intersection.IsLogDiscrepancy sS 2 (QDivisor.toRDivisor BS) D a ↔
              MMP.Intersection.IsLogDiscrepancy sX 3 (QDivisor.toRDivisor B) D' a) ∧
      -- (4)
      (∀ w : Valuation S.functionField (WithZero (Multiplicative ℤ)),
        MMP.Intersection.IsNormalizedDivisorialValuation K sS w →
          MMP.Intersection.IsNormalizedDivisorialValuation ℂ (U.ι ≫ sX)
              (w.comap (functionFieldMap ι)) ∧
          (∀ (D : DivisorOver K sS) (D' : DivisorOver ℂ (U.ι ≫ sX)), IsProper D.f →
            IsProper D'.f → D.valuation = w → D'.valuation = w.comap (functionFieldMap ι) →
            ∀ a : ℝ, MMP.Intersection.IsLogDiscrepancy sS 2 (QDivisor.toRDivisor BS) D a ↔
              MMP.Intersection.IsLogDiscrepancy (U.ι ≫ sX) 3
                (QDivisor.toRDivisor (MMP.Mori.inverseTransformDivisor U.ι B)) D' a) ∧
          (MMP.Intersection.IsCentre K sS w (irreducibleSetEquivPoints.symm x) ↔
            MMP.Intersection.IsCentre ℂ (U.ι ≫ sX) (w.comap (functionFieldMap ι))
              (irreducibleSetEquivPoints.symm ⟨V.isIrreducible.genericPoint, hU⟩))) ∧
      -- in particular
      (∀ ξ : Valuation S.functionField (WithZero (Multiplicative ℤ)),
        MMP.Intersection.IsCentre K sS ξ (irreducibleSetEquivPoints.symm x) ↔
          MMP.Intersection.IsCentre ℂ sX (ξ.comap (functionFieldMap (ι ≫ U.ι))) V) ∧
      (IsKltPair sX B → IsCharZeroKltPair sS BS) := by
  classical
  have hXv : IsNormalVariety ℂ sX := hB.isPair.1
  haveI : LocallyOfFiniteType sX := hXv.1.toLocallyOfFiniteType
  have hX' : topologicalKrullDim X = ((1 + 2 : ℕ) : WithBot ℕ∞) := by rw [hX]; rfl
  have hxV : IsGenericPoint V.isIrreducible.genericPoint (V : Set X) := by
    have h := V.isIrreducible.isGenericPoint_genericPoint_closure
    rwa [V.isClosed.closure_eq] at h
  set x := V.isIrreducible.genericPoint with hxdef
  have hV' : topologicalKrullDim (V : Set X) = ((1 : ℕ) : WithBot ℕ∞) := by rw [hV]; rfl
  -- the generic point `x` of `V` has codimension two
  have hx : Order.coheight x = 2 := by
    have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX x
    rw [isGenericPoint_def.1 hxV, hV', hX'] at h
    generalize Order.coheight x = c at h ⊢
    have h1 : (((1 : ℕ) : ℕ∞) + c : ℕ∞) = ((1 + 2 : ℕ) : ℕ∞) := by
      rw [← WithBot.coe_natCast, ← WithBot.coe_add, ← WithBot.coe_natCast] at h
      exact WithBot.coe_injective h
    induction c using ENat.recTopCoe with
    | top => exact (ENat.coe_ne_top (1 + 2) (by simpa using h1.symm)).elim
    | coe c =>
      have h'' : 1 + c = 1 + 2 := by exact_mod_cast h1
      have : c = 2 := by omega
      rw [this]; rfl
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
  haveI : Nonempty U := ⟨⟨x, hxU⟩⟩
  letI := sectionAlgebra sX U
  haveI : Algebra.FiniteType ℂ Γ(X, U) := MMP.Mori.finiteType_sectionAlgebra sX hU
  haveI : IsDomain Γ(X, U) := IsIntegral.component_integral U
  haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  obtain ⟨d', tb, htb⟩ := exists_fin_isTranscendenceBasis ℂ
    (Γ(X, U) ⧸ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal)
  choose t ht using fun i => Ideal.Quotient.mk_surjective
    (I := (hU.primeIdealOf ⟨x, hxU⟩).asIdeal) (tb i)
  have htt : IsTranscendenceBasis ℂ
      (Ideal.Quotient.mk (hU.primeIdealOf ⟨x, hxU⟩).asIdeal ∘ t) := by
    have : Ideal.Quotient.mk (hU.primeIdealOf ⟨x, hxU⟩).asIdeal ∘ t = tb := funext ht
    rwa [this]
  haveI : IsDomain (Localization (genSubmonoid sX t)) := isDomain_genRing sX t htt.1
  haveI : IsNoetherianRing (Localization (genSubmonoid sX t)) :=
    IsLocalization.isNoetherianRing (genSubmonoid sX t) _ inferInstance
  haveI hSi : IsIntegral (Spec (genRing sX t)) := inferInstance
  haveI hSl : IsLocallyNoetherian (Spec (genRing sX t)) := inferInstance
  have hstalk := isIso_stalkMap_genι sX t hU
  haveI hSn : IsNormal (Spec (genRing sX t)) := isNormal_of_isIso_stalkMap _ hstalk
  haveI hft : LocallyOfFiniteType (genStructure sX t) := locallyOfFiniteType_genStructure sX t hU
  haveI hdom : IsDominant (genι sX t hU) := isDominant_genι sX t hU htt.1
  have hpcl := isClosed_genPoint sX t hU hxU htt
  have hcomm := genι_comp_eq sX t hU
  have hιp := genι_genPoint sX t hU hxU htt.1
  set p := genPoint sX t hU hxU htt.1 with hp
  set g := genι sX t hU ≫ U.ι with hg
  have hgp : g p = x := by rw [hg, Scheme.Hom.comp_apply, hιp]; rfl
  have hcohp : Order.coheight p = 2 := by
    rw [← coheight_eq_of_isIso_stalkMap g p (isIso_stalkMap_genι_comp sX t hU p), hgp]
    exact hx
  have hdim0 : topologicalKrullDim (closure ({p} : Set (Spec (genRing sX t)))) = 0 := by
    rw [hpcl.closure_eq]
    exact topologicalKrullDim_eq_zero_of_subsingleton
  have hdimS : topologicalKrullDim (Spec (genRing sX t)) = 2 := by
    have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight (genStructure sX t) p
    rw [hdim0, hcohp, zero_add] at h
    exact h.symm
  -- transcendence degrees
  set K := genField ℂ d'
  set sS' := genStructure sX t ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ K)) with hsS'
  have hgs : g ≫ sX = sS' := by rw [hg, Category.assoc, hcomm]
  have h3 := MMP.Flips.trdeg_residueField_add sS' sX g hgs p
  letI : Algebra (X.residueField (g p)) ((Spec (genRing sX t)).residueField p) :=
    (g.residueFieldMap p).hom.toAlgebra
  have hsurj : Function.Surjective
      (Algebra.ofId (X.residueField (g p)) ((Spec (genRing sX t)).residueField p)) :=
    @surjective_residueFieldMap _ _ g p (isIso_stalkMap_genι_comp sX t hU p)
  haveI : Algebra.IsIntegral (X.residueField (g p)) ((Spec (genRing sX t)).residueField p) :=
    Algebra.IsIntegral.of_surjective _ hsurj
  rw [trdeg_eq_zero (R := X.residueField (g p)) (A := (Spec (genRing sX t)).residueField p),
    add_zero] at h3
  letI : Algebra K ((Spec (genRing sX t)).residueField p) :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ (genStructure sX t).appTop ≫
      (Spec (genRing sX t)).Γevaluation p).hom.toAlgebra
  letI : Algebra ℂ ((Spec (genRing sX t)).residueField p) :=
    ((Scheme.ΓSpecIso (.of ℂ)).inv ≫ sS'.appTop ≫
      (Spec (genRing sX t)).Γevaluation p).hom.toAlgebra
  haveI : IsScalarTower ℂ K ((Spec (genRing sX t)).residueField p) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    have : (Scheme.ΓSpecIso (.of ℂ)).inv ≫ sS'.appTop ≫ (Spec (genRing sX t)).Γevaluation p =
        CommRingCat.ofHom (algebraMap ℂ K) ≫ (Scheme.ΓSpecIso (.of K)).inv ≫
          (genStructure sX t).appTop ≫ (Spec (genRing sX t)).Γevaluation p := by
      rw [hsS', Scheme.Hom.comp_appTop, ← Category.assoc, ← Category.assoc,
        ← Scheme.ΓSpecIso_inv_naturality, Category.assoc, Category.assoc]
    exact congrArg CommRingCat.Hom.hom this
  haveI : FaithfulSMul ℂ K := (faithfulSMul_iff_algebraMap_injective ℂ K).2
    (algebraMap ℂ K).injective
  haveI : FaithfulSMul K ((Spec (genRing sX t)).residueField p) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2
      (RingHom.injective (algebraMap K ((Spec (genRing sX t)).residueField p)))
  have h4 := trdeg_add_eq ℂ K (A := (Spec (genRing sX t)).residueField p)
  have h5 : Algebra.trdeg K ((Spec (genRing sX t)).residueField p) = 0 := by
    have h := topologicalKrullDim_closure_singleton_eq_trdeg K (Spec (genRing sX t))
      (genStructure sX t) p
    rw [hdim0] at h
    have h' : Cardinal.toENat (Algebra.trdeg K ((Spec (genRing sX t)).residueField p)) = 0 := by
      exact_mod_cast h.symm
    exact Cardinal.toENat_eq_zero.1 h'
  have h6 : Algebra.trdeg ℂ K = d' := by
    have h := (isTranscendenceBasis_genField ℂ d').lift_cardinalMk_eq_trdeg
    rw [Cardinal.mk_fin, Cardinal.lift_natCast] at h
    exact (Cardinal.lift_eq_nat_iff.1 h.symm)
  rw [h5, add_zero, h6] at h4
  have h7 := topologicalKrullDim_closure_singleton_eq_trdeg ℂ X sX (g p)
  rw [h3, ← h4] at h7
  have hx' : Order.coheight (g p) = 2 := by rwa [hgp]
  have hdimX : topologicalKrullDim X = (d' + 2 : ℕ) := by
    have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX (g p)
    rw [h7, hx', Cardinal.toENat_nat] at h
    rw [← h]
    norm_cast
  have hvar : IsNormalVariety K (genStructure sX t) :=
    ⟨@IsVariety.mk _ _ _ _ hSi inferInstance hft inferInstance, hSn⟩
  have hdd : d' = 1 := by
    have h := hdimX.symm.trans hX'
    have h' : d' + 2 = 1 + 2 := by exact_mod_cast h
    omega
  subst hdd
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℂ K).injective
  have htalg : AlgebraicIndependent ℂ t :=
    AlgebraicIndependent.of_comp (Ideal.Quotient.mkₐ ℂ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal) htt.1
  haveI := isDominant_opens_ι U
  haveI hdomg : IsDominant (genι sX t hU ≫ U.ι) := inferInstance
  have hBS := isPair_genBoundary sX hB hU hxU t htt hvar hdimS hdimX
  have hθs := (bijective_functionFieldMap_genι_comp sX t hU).2
  have hUv := isNormalVariety_ι hXv U
  have hpairS : MMP.Fourfold.IsCharZeroPair (genStructure sX t) (genBoundary sX t hU B) :=
    ⟨inferInstance, hBS, fun P => by rw [coeff_genBoundary]; exact hB.nonneg _⟩
  -- the function `u` and the generic fibre as a fibre product
  have htu : (letI : Algebra ℂ Γ(U, ⊤) :=
      ((U.ι ≫ sX).appTop.hom.comp (Scheme.ΓSpecIso (.of ℂ)).inv.hom).toAlgebra
      Transcendental ℂ (U.topIso.inv (t 0))) := by
    letI : Algebra ℂ Γ(U, ⊤) :=
      ((U.ι ≫ sX).appTop.hom.comp (Scheme.ΓSpecIso (.of ℂ)).inv.hom).toAlgebra
    have h0 : Transcendental ℂ (t 0) := htalg.transcendental 0
    have he := congrArg CommRingCat.Hom.hom (sectionAlgebra_comp_topIso_inv sX U)
    exact h0.ringHom_of_comp_eq (RingHom.id ℂ) U.topIso.inv.hom Function.surjective_id
      (ConcreteCategory.bijective_of_isIso U.topIso.inv).1 he.symm
  have hadj : IntermediateField.adjoin ℂ
      {algebraMap (MvPolynomial (Fin 1) ℂ) K (MvPolynomial.X 0)} = ⊤ := by
    have h := adjoin_genField_eq_top ℂ 1
    rwa [Set.range_unique] at h
  have hpb : IsPullback (genι sX t hU) (genStructure sX t)
      (AffineSpace.homOfVector (U.ι ≫ sX) (fun _ : Unit => U.topIso.inv (t 0)))
      (AffineSpace.homOfVector (Spec.map (CommRingCat.ofHom (algebraMap ℂ K)))
        (fun _ : Unit => (Scheme.ΓSpecIso (.of K)).inv
          (algebraMap (MvPolynomial (Fin 1) ℂ) K (MvPolynomial.X 0)))) := by
    refine (isPullback_genι sX t hU).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (specMvPolynomialFinOneIso ℂ) (by simp) (by simp) ?_ ?_
    · rw [Iso.refl_hom, Category.id_comp, genφ_comp_specMvPolynomialFinOneIso]
    · rw [Iso.refl_hom, Category.id_comp, SpecMap_algebraMap_comp_specMvPolynomialFinOneIso]
  have huniq : ∀ y : Spec (genRing sX t), genι sX t hU y = ⟨x, hxU⟩ → y = p := by
    intro y hy
    apply injective_genι sX t hU
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hy, hιp]
  -- (3): divisors over `X` centred at `V`
  have hthree : ∀ ξ : Valuation (Spec (genRing sX t)).functionField (WithZero (Multiplicative ℤ)),
      MMP.Intersection.IsCentre ℂ sX (ξ.comap (functionFieldMap (genι sX t hU ≫ U.ι))) V →
        (∀ c : K, c ≠ 0 → ξ ((Spec (genRing sX t)).germToFunctionField ⊤
          ((genStructure sX t).appTop ((Scheme.ΓSpecIso (.of K)).inv c))) = 1) ∧
        MMP.Intersection.IsNormalizedDivisorialValuation K (genStructure sX t) ξ ∧
        MMP.Intersection.IsCentre K (genStructure sX t) ξ (irreducibleSetEquivPoints.symm p) ∧
        ∀ (D : DivisorOver K (genStructure sX t)) (D' : DivisorOver ℂ sX), IsProper D.f →
          IsProper D'.f → D.valuation = ξ →
          D'.valuation = ξ.comap (functionFieldMap (genι sX t hU ≫ U.ι)) →
          ∀ a : ℝ, MMP.Intersection.IsLogDiscrepancy (genStructure sX t) 2
              (QDivisor.toRDivisor (genBoundary sX t hU B)) D a ↔
            MMP.Intersection.IsLogDiscrepancy sX 3 (QDivisor.toRDivisor B) D' a := by
    rintro ξ ⟨D₀', -, hξ, hV₀⟩
    have hD₀'x : D₀'.f D₀'.E.genericPoint = x := by
      have hgen : IsGenericPoint (D₀'.f D₀'.E.genericPoint) (V : Set X) := by
        rw [isGenericPoint_def, ← D₀'.center_eq_closure_genericPoint, hV₀]
      exact hgen.eq hxV
    obtain ⟨D₀, hD₀p, hD₀c, hD₀v⟩ :=
      exists_divisorOver_genSurface_of_divisorOver sX hXv hU hxU t htt hvar D₀' hD₀'x
    have hξD : ξ = D₀.valuation := valuation_comap_injective _ hθs (hξ.trans hD₀v.symm)
    have hD₀x := map_genericPoint_eq_of_center_eq_singleton D₀ hD₀c
    refine ⟨fun c hc => by rw [hξD]; exact valuation_const_eq_one_of_divisorOver D₀ hc,
      ⟨D₀, hD₀p, hξD⟩,
      ⟨D₀, hD₀p, hξD, (irreducibleSetEquivPoints_symm_eq_center_iff D₀ p).2 hD₀x⟩, ?_⟩
    intro D D' hDp hD'p hDv hD'v a
    have hD'x : D'.f D'.E.genericPoint = x :=
      (MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq hXv
        (hD'v.trans hξ)).trans hD₀'x
    obtain ⟨DU, hDUp, hDUv, hDUx⟩ := exists_properDivisorOver_of_genSurface sX hXv hU t D
    have h1 := isLogDiscrepancy_genSurface_iff sX hB hx hU hxU t htt hBS D hDp DU hDUp hDUv
      hDUx hdimX hvar hdimS a
    have h2 := isLogDiscrepancy_open_iff sX hB.isPair hX U D' hD'p (by rw [hD'x]; exact hxU) DU
      hDUp (by rw [hD'v, hDUv, comap_functionFieldMap_comp, hDv]) a
    exact h1.trans h2.symm
  -- (4): divisors over the generic surface
  have hfour : ∀ w : Valuation (Spec (genRing sX t)).functionField (WithZero (Multiplicative ℤ)),
      MMP.Intersection.IsNormalizedDivisorialValuation K (genStructure sX t) w →
        MMP.Intersection.IsNormalizedDivisorialValuation ℂ (U.ι ≫ sX)
            (w.comap (functionFieldMap (genι sX t hU))) ∧
        (∀ (D : DivisorOver K (genStructure sX t)) (D' : DivisorOver ℂ (U.ι ≫ sX)),
          IsProper D.f → IsProper D'.f → D.valuation = w →
          D'.valuation = w.comap (functionFieldMap (genι sX t hU)) →
          ∀ a : ℝ, MMP.Intersection.IsLogDiscrepancy (genStructure sX t) 2
              (QDivisor.toRDivisor (genBoundary sX t hU B)) D a ↔
            MMP.Intersection.IsLogDiscrepancy (U.ι ≫ sX) 3
              (QDivisor.toRDivisor (MMP.Mori.inverseTransformDivisor U.ι B)) D' a) ∧
        (MMP.Intersection.IsCentre K (genStructure sX t) w (irreducibleSetEquivPoints.symm p) ↔
          MMP.Intersection.IsCentre ℂ (U.ι ≫ sX) (w.comap (functionFieldMap (genι sX t hU)))
            (irreducibleSetEquivPoints.symm ⟨x, hxU⟩)) := by
    rintro w ⟨D₀, hD₀p, hwD⟩
    obtain ⟨DU₀, hDU₀p, hDU₀v, hDU₀x⟩ := exists_properDivisorOver_of_genSurface sX hXv hU t D₀
    refine ⟨⟨DU₀, hDU₀p, by rw [hDU₀v, hwD]⟩, ?_, ?_⟩
    · intro D D' hDp hD'p hDv hD'v a
      obtain ⟨DU, -, hDUv, hDUx⟩ := exists_properDivisorOver_of_genSurface sX hXv hU t D
      have hD'x : D'.f D'.E.genericPoint = genι sX t hU (D.f D.E.genericPoint) :=
        (MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq hUv
          (by rw [hD'v, hDUv, hDv])).trans hDUx
      exact isLogDiscrepancy_genSurface_iff sX hB hx hU hxU t htt hBS D hDp D' hD'p
        (by rw [hD'v, hDv]) hD'x hdimX hvar hdimS a
    · constructor
      · rintro ⟨D, -, hwD', hDc⟩
        have hDx := (irreducibleSetEquivPoints_symm_eq_center_iff D p).1 hDc
        obtain ⟨DU, hDUp, hDUv, hDUx⟩ := exists_properDivisorOver_of_genSurface sX hXv hU t D
        exact ⟨DU, hDUp, by rw [hDUv, ← hwD'],
          (irreducibleSetEquivPoints_symm_eq_center_iff DU _).2 (by rw [hDUx, hDx, hιp])⟩
      · rintro ⟨D', -, hwD', hD'c⟩
        have hD'x := (irreducibleSetEquivPoints_symm_eq_center_iff D' _).1 hD'c
        have h1 : DU₀.f DU₀.E.genericPoint = D'.f D'.E.genericPoint :=
          MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq hUv
            (by rw [hDU₀v, ← hwD, hwD'])
        have hD₀x : D₀.f D₀.E.genericPoint = p := by
          apply injective_genι sX t hU
          rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, ← hDU₀x, h1, hD'x, hιp]
        exact ⟨D₀, hD₀p, hwD, (irreducibleSetEquivPoints_symm_eq_center_iff D₀ p).2 hD₀x⟩
  -- the bijection of centres
  have hpart : ∀ ξ : Valuation (Spec (genRing sX t)).functionField (WithZero (Multiplicative ℤ)),
      MMP.Intersection.IsCentre K (genStructure sX t) ξ (irreducibleSetEquivPoints.symm p) ↔
        MMP.Intersection.IsCentre ℂ sX (ξ.comap (functionFieldMap (genι sX t hU ≫ U.ι))) V := by
    intro ξ
    refine ⟨?_, fun h => (hthree ξ h).2.2.1⟩
    rintro ⟨D, -, hξD, hDc⟩
    have hDx := (irreducibleSetEquivPoints_symm_eq_center_iff D p).1 hDc
    obtain ⟨D'', hD''p, hD''v, hD''x⟩ := exists_properDivisorOver_X_of_genSurface sX hXv hU t D
    refine ⟨D'', hD''p, by rw [hD''v, ← hξD], SetLike.coe_injective ?_⟩
    rw [D''.center_eq_closure_genericPoint, hD''x, hDx, hιp]
    exact (isGenericPoint_def.1 hxV).symm
  -- klt
  have hklt : MMP.Fourfold.IsKltPair sX B →
      MMP.Fourfold.IsCharZeroKltPair (genStructure sX t) (genBoundary sX t hU B) := by
    intro hK
    refine ⟨hpairS, ?_⟩
    intro n D a hLD
    have hn : n = 2 := by
      have h := (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq hLD).symm.trans
        hdimS
      exact_mod_cast h
    subst hn
    have hDp : IsProper D.f := by
      obtain ⟨-, hDp, -⟩ := hLD
      exact hDp
    obtain ⟨DU, hDUp, hDUv, hDUx⟩ := exists_properDivisorOver_of_genSurface sX hXv hU t D
    obtain ⟨D'', hD''p, hD''v, hD''x⟩ := exists_properDivisorOver_X_of_genSurface sX hXv hU t D
    have h1 := (isLogDiscrepancy_genSurface_iff sX hB hx hU hxU t htt hBS D hDp DU hDUp hDUv
      hDUx hdimX hvar hdimS a).1 hLD
    have h2 := (isLogDiscrepancy_open_iff sX hB.isPair hX U D'' hD''p
      (by rw [hD''x]; exact (genι sX t hU (D.f D.E.genericPoint)).2) DU hDUp
      (by rw [hD''v, hDUv, comap_functionFieldMap_comp]) a).2 h1
    exact hK.2 3 D'' a h2
  refine ⟨U, hxU, hU, inferInstance, inferInstance, inferInstance, U.topIso.inv (t 0), htu,
    K, inferInstance, inferInstance, algebraMap (MvPolynomial (Fin 1) ℂ) K (MvPolynomial.X 0),
    (isTranscendenceBasis_genField ℂ 1).1.transcendental 0, hadj,
    Spec (genRing sX t), genι sX t hU, genStructure sX t, hpb, hSi, hSl, hSn, hdom,
    inferInstance, hvar, hdimS, bijective_functionFieldMap_genι_comp sX t hU, p, hpcl,
    preimage_eq_singleton_genPoint sX t hU hxU htt (isGenericPoint_def.1 hxV), hιp, hstalk p,
    huniq, finite_isSeparable_residueField_of_isClosed _ p hpcl, genBoundary sX t hU B,
    hpairS, fun P => ⟨genPrimeDivisor sX t hU P, genericPoint_genPrimeDivisor sX t hU P,
      coeff_genBoundary sX t hU B P⟩, hthree, hfour, hpart, hklt⟩

end MMP.Fourfold

end
