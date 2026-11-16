/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Resolution.Surface.CurveMultiplicity
public import MMP.AlgebraicGeometry.Divisor.Basic
public import MMP.AlgebraicGeometry.Resolution.Surface.SemilocalRing
public import MMP.RingTheory.ElementMultiplicity
public import Mathlib.RingTheory.LocalRing.Length
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import StacksFrontier.AlgebraicGeometry.FunctionField.SectionsIntersectionStalks
public import StacksFrontier.AlgebraicGeometry.AmpleDimensionOne.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClosedPointCodimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.QuasiProjective
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.NormalizationDescent
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ZeroCycleDegreeClosedSubscheme

/-!
# Rational functions on projective curves have degree zero (Kollár 1.20.5)

A rational function `g` on a projective curve `C` over `k`, transcendental over `k` and with no
point where both `g` and `g⁻¹` are irregular, is regular on an affine open `C₀` whose coordinate
ring is finite over `k[g]`: the map `C₀ ⟶ 𝔸¹_k` given by `g` is proper and quasi-finite, hence
finite. For `f ∈ k(C)^×` the multiplicities `e_p(f)` vanish at all but finitely many closed
points and sum to `0`: at a closed point `e_p(f) = ord_p(f) · [κ(p) : k]`, and the degree of a
principal divisor on a proper curve is `0`.

## Main results

* `MMP.Resolution.exists_isAffineOpen_regularLocus_finite`: a transcendental rational function
  with no point where both it and its inverse are irregular is regular on an affine open whose
  coordinate ring is finite over `k[g]`.
* `MMP.Resolution.exists_finset_sum_eMultAt_eq_zero`: the multiplicities `e_p(f)` vanish at all
  but finitely many closed points and sum to `0`.
* `MMP.Resolution.eMultAt_singleton_eq`: `e_p(f) = ord_p(f) · [κ(p) : k]`.

## References

* [J. Kollár, *Lectures on resolution of singularities*][KollarResolution], 1.20.5
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Polynomial TopologicalSpace IsLocalRing Module

namespace MMP.Resolution

/-! ### Lengths over a local algebra -/

/-- For a local `k`-algebra `O` and an `O`-module `M` finite-dimensional over `k`,
`dim_k M = length_O(M) · [κ(O) : k]`. -/
theorem finrank_eq_length_toNat_mul (k : Type*) [Field k] {O : Type*} [CommRing O] [IsLocalRing O]
    [Algebra k O] (M : Type*) [AddCommGroup M] [Module O M] [Module k M] [IsScalarTower k O M]
    [Module.Finite k M] :
    finrank k M = (Module.length O M).toNat * finrank k (ResidueField O) := by
  have h := IsLocalRing.length_restrictScalars k O M
  rw [Module.length_eq_finrank] at h
  have h2 : Module.length (ResidueField k) (ResidueField O) = Module.length k (ResidueField O) :=
    (Module.length_eq_of_surjective (S := k) (R := ResidueField k)
      IsLocalRing.residue_surjective).symm
  rw [h2, Module.length_eq_rank] at h
  by_cases hfin : Module.Finite k (ResidueField O)
  · rw [← Module.finrank_eq_rank, Cardinal.toENat_nat] at h
    have hpos : 0 < finrank k (ResidueField O) := Module.finrank_pos
    have hne : Module.length O M ≠ ⊤ := by
      intro ht
      rw [ht, ENat.top_mul (by exact_mod_cast hpos.ne')] at h
      exact ENat.natCast_ne_top _ h
    lift Module.length O M to ℕ using hne with n
    simp only [ENat.toNat_natCast]
    exact_mod_cast h
  · have htop : (Module.rank k (ResidueField O)).toENat = ⊤ := by
      rw [Cardinal.toENat_eq_top]
      exact not_lt.1 (fun hlt => hfin (Module.rank_lt_aleph0_iff.1 hlt))
    rw [htop] at h
    rw [Module.finrank_of_not_finite hfin, mul_zero]
    by_cases h0 : Module.length O M = 0
    · rw [h0, zero_mul] at h
      exact_mod_cast h
    · rw [ENat.mul_top h0] at h
      exact absurd h (ENat.natCast_ne_top _)

variable {k : Type u} [Field k] {C : Scheme.{u}} (sC : C ⟶ Spec (.of k))

/-! ### The chart of a rational function -/

/-- On an integral scheme, the algebra map from the stalk at the generic point to the function
field is the identity. -/
theorem algebraMap_stalk_genericPoint_apply [IsIntegral C]
    (a : C.presheaf.stalk (genericPoint C)) :
    @algebraMap (C.presheaf.stalk (genericPoint C)) C.functionField _ _
      (stalkFunctionFieldAlgebra C (genericPoint C)) a = a := by
  have h : C.presheaf.stalkSpecializes ((genericPoint_spec C).specializes trivial) = 𝟙 _ :=
    TopCat.Presheaf.stalkSpecializes_refl _ _
  simp only [RingHom.algebraMap_toAlgebra, h]
  rfl

/-- The set of points of an integral scheme at whose local ring a rational function `g` is regular
is open. -/
theorem isOpen_setOf_mem_range [IsIntegral C] (g : C.functionField) :
    IsOpen {x : C | g ∈ (algebraMap (C.presheaf.stalk x) C.functionField).range} := by
  rw [isOpen_iff_forall_mem_open]
  rintro x ⟨a, ha⟩
  obtain ⟨W, hxW, t, ht⟩ := C.presheaf.exists_germ_eq a
  have : Nonempty W := ⟨⟨x, hxW⟩⟩
  refine ⟨W, fun y hy => ⟨C.presheaf.germ W y hy t, ?_⟩, W.isOpen, hxW⟩
  rw [Scheme.algebraMap_germ_eq_germToFunctionField, ← ha, ← ht,
    Scheme.algebraMap_germ_eq_germToFunctionField]

section Chart

variable (U : C.Opens) (s : Γ(C, U))

/-- The ring map `k[X] → Γ(C, U)` sending `X` to `s`. -/
def chartRingHom : k[X] →+* Γ(C, U) :=
  Polynomial.eval₂RingHom ((sC.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom) s

/-- The morphism `U → 𝔸¹_k` given by `s`. -/
def chartHom : U.toScheme ⟶ Spec (.of k[X]) :=
  U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (chartRingHom sC U s))

@[simp]
theorem chartRingHom_X : chartRingHom sC U s Polynomial.X = s := by
  simp [chartRingHom]

@[simp]
theorem chartRingHom_C (c : k) :
    chartRingHom sC U s (Polynomial.C c) =
      (sC.appLE ⊤ U le_top).hom ((Scheme.ΓSpecIso (.of k)).inv.hom c) := by
  simp [chartRingHom]

/-- A morphism `f : Y ⟶ Spec R` factors as `Y ⟶ Spec Γ(Y, ⊤) ⟶ Spec Γ(Spec R, ⊤) ≅ Spec R`. -/
theorem eq_toSpecΓ_comp {R : CommRingCat.{u}} (Y : Scheme.{u}) (f : Y ⟶ Spec R) :
    f = Y.toSpecΓ ≫ Spec.map f.appTop ≫ Spec.map (Scheme.ΓSpecIso R).inv := by
  rw [← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-- Composing `chartHom sC U s` with the structure map `𝔸¹_k ⟶ Spec k` gives the restriction of
`sC` to `U`. -/
@[reassoc]
theorem chartHom_comp :
    chartHom sC U s ≫ Spec.map (CommRingCat.ofHom Polynomial.C) = U.ι ≫ sC := by
  conv_rhs => rw [eq_toSpecΓ_comp C sC]
  rw [← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top_assoc, chartHom, Category.assoc,
    ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
  congr 2
  ext c
  change chartRingHom sC U s (Polynomial.C c) = _
  rw [chartRingHom_C]
  rfl

/-- A polynomial `P` lies in the prime of `k[X]` that is the image of `x` under `chartHom sC U s`
iff `P(s)` vanishes at `x`. -/
theorem mem_chartHom_asIdeal_iff (x : U.toScheme) (P : k[X]) :
    P ∈ (chartHom sC U s x).asIdeal ↔ x.1 ∉ C.basicOpen (chartRingHom sC U s P) := by
  have h : x ∈ U.toSpecΓ ⁻¹ᵁ PrimeSpectrum.basicOpen (chartRingHom sC U s P) ↔
      x ∈ U.ι ⁻¹ᵁ C.basicOpen (chartRingHom sC U s P) := by
    rw [Scheme.Opens.toSpecΓ_preimage_basicOpen U (chartRingHom sC U s P)]
  change chartRingHom sC U s P ∈ (U.toSpecΓ x).asIdeal ↔ _
  rw [← not_iff_not, not_not]
  exact h

/-- If `C` is locally of finite type over `k`, then `chartHom sC U s` is locally of finite type. -/
theorem locallyOfFiniteType_chartHom [LocallyOfFiniteType sC] :
    LocallyOfFiniteType (chartHom sC U s) := by
  have : LocallyOfFiniteType (chartHom sC U s ≫ Spec.map (CommRingCat.ofHom Polynomial.C)) := by
    rw [chartHom_comp]
    infer_instance
  exact locallyOfFiniteType_of_comp _ (Spec.map (CommRingCat.ofHom Polynomial.C))

/-- On a Noetherian integral curve, if `P(s) ≠ 0` for every nonzero `P ∈ k[X]`, then
`chartHom sC U s` is locally quasi-finite. -/
theorem locallyQuasiFinite_chartHom [IsIntegral C] [IsNoetherian C] [LocallyOfFiniteType sC]
    (hdim : topologicalKrullDim C = 1) (hs : ∀ P : k[X], P ≠ 0 → chartRingHom sC U s P ≠ 0) :
    LocallyQuasiFinite (chartHom sC U s) := by
  have := locallyOfFiniteType_chartHom sC U s
  refine LocallyQuasiFinite.of_finite_preimage_singleton _ fun y => ?_
  by_cases hy : ∃ P ∈ y.asIdeal, P ≠ 0
  · obtain ⟨P, hPy, hP0⟩ := hy
    have hfin := Stacks.AlgebraicGeometry.AmpleDimensionOne.finite_compl_of_ne_bot C hdim
      (C.basicOpen (chartRingHom sC U s P))
      (by rw [Ne, basicOpen_eq_bot_iff]; exact hs P hP0)
    refine (hfin.preimage U.ι.isOpenEmbedding.injective.injOn).subset fun x hx => ?_
    have hx : chartHom sC U s x = y := hx
    exact (mem_chartHom_asIdeal_iff sC U s x P).1 (hx ▸ hPy)
  · push Not at hy
    have hbot : y.asIdeal = ⊥ := (Submodule.eq_bot_iff _).2 hy
    refine Set.Subsingleton.finite fun x hx x' hx' => ?_
    have key : ∀ z : U.toScheme, chartHom sC U s z = y → z.1 = genericPoint C := by
      intro z hz
      by_contra hne
      have hcl : IsClosed ({z.1} : Set C) :=
        Stacks.AlgebraicGeometry.AmpleDimensionOne.isClosed_singleton_of_ne_genericPoint C hdim hne
      have hcl' : IsClosed ({z} : Set U.toScheme) := by
        have := hcl.preimage U.ι.continuous
        convert this
        ext w
        simp only [Set.mem_singleton_iff, Set.mem_preimage]
        exact ⟨fun h => h ▸ rfl, fun h => U.ι.isOpenEmbedding.injective h⟩
      have := (chartHom sC U s).closePoints_subset_preimage_closedPoints hcl'
      rw [Set.mem_preimage, hz, mem_closedPoints_iff] at this
      have := (PrimeSpectrum.isClosed_singleton_iff_isMaximal (R := k[X]) y).1 this
      rw [hbot] at this
      exact Polynomial.not_isField k ((Ring.isField_iff_maximal_bot).2 this)
    exact U.ι.isOpenEmbedding.injective ((key x hx).trans (key x' hx').symm)

/-- For a specialization `x ⤳ y` on an integral scheme, the specialization map of stalks is
compatible with the algebra maps to the function field. -/
theorem algebraMap_stalkSpecializes_apply [IsIntegral C] {x y : C} (h : x ⤳ y)
    (a : C.presheaf.stalk y) :
    algebraMap (C.presheaf.stalk x) C.functionField (C.presheaf.stalkSpecializes h a) =
      algebraMap (C.presheaf.stalk y) C.functionField a := by
  simp only [RingHom.algebraMap_toAlgebra]
  exact TopCat.Presheaf.stalkSpecializes_comp_apply _ _ _ a

/-- In the setting of `valuativeExistence_chartHom`, a lift `l` of a valuative square for
`chartHom sC U s` to `C` sends the closed point into `U`. -/
theorem closedPoint_mem_of_valuativeLift [IsIntegral C]
    (hdim : topologicalKrullDim C = 1) (g : C.functionField) (hη : genericPoint C ∈ U)
    (hsg : ∀ x (hx : x ∈ U), algebraMap (C.presheaf.stalk x) C.functionField
      (C.presheaf.germ U x hx s) = g)
    (hUset : ∀ x, g ∈ (algebraMap (C.presheaf.stalk x) C.functionField).range → x ∈ U)
    (hpole : ∀ p : C, IsClosed ({p} : Set C) →
      g ∈ (algebraMap (C.presheaf.stalk p) C.functionField).range ∨
        g⁻¹ ∈ (algebraMap (C.presheaf.stalk p) C.functionField).range)
    (hg0 : g ≠ 0) (S : ValuativeCommSq (chartHom sC U s)) (l : Spec (.of S.R) ⟶ C)
    (hl₁ : Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) ≫ l = S.i₁ ≫ U.ι) :
    l (IsLocalRing.closedPoint S.R) ∈ U := by
  obtain ⟨v₀, hv₀⟩ := Spec.map_surjective S.i₂
  by_contra hcU
  have hcη : l (IsLocalRing.closedPoint S.R) ≠ genericPoint C := fun h => hcU (h ▸ hη)
  have hccl := Stacks.AlgebraicGeometry.AmpleDimensionOne.isClosed_singleton_of_ne_genericPoint
    C hdim hcη
  obtain ⟨t, ht⟩ := (hpole _ hccl).resolve_left (fun h => hcU (hUset _ h))
  have htu : ¬ IsUnit t := by
    intro hu
    refine hcU (hUset (l (IsLocalRing.closedPoint S.R))
      ⟨(hu.unit⁻¹ : (C.presheaf.stalk (l (IsLocalRing.closedPoint S.R)))ˣ).1, ?_⟩)
    have h2 : algebraMap (C.presheaf.stalk _) C.functionField
        (hu.unit⁻¹ : (C.presheaf.stalk (l (IsLocalRing.closedPoint S.R)))ˣ).1 * g⁻¹ = 1 := by
      rw [← ht, ← map_mul, IsUnit.val_inv_mul, map_one]
    exact (mul_inv_eq_one₀ hg0).1 h2
  let j := S.i₁ ≫ U.ι
  have hu : j (IsLocalRing.closedPoint S.K) ∈ U := (S.i₁ (IsLocalRing.closedPoint S.K)).2
  have huc : j (IsLocalRing.closedPoint S.K) ⤳ l (IsLocalRing.closedPoint S.R) := by
    have : j (IsLocalRing.closedPoint S.K) =
        l (Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) (IsLocalRing.closedPoint S.K)) :=
      (congrArg (fun f : Spec (.of S.K) ⟶ C => f (IsLocalRing.closedPoint S.K)) hl₁).symm
    rw [this]
    exact (IsLocalRing.specializes_closedPoint _).map l.continuous
  let ψc := Scheme.stalkClosedPointTo l
  let χ := Scheme.stalkClosedPointTo j
  have hF3 : ψc ≫ CommRingCat.ofHom (algebraMap S.R S.K) =
      C.presheaf.stalkSpecializes huc ≫ χ := by
    have hl : Spec.map ψc ≫ C.fromSpecStalk _ = l :=
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk l
    have hj : Spec.map χ ≫ C.fromSpecStalk _ = j := Scheme.Spec_stalkClosedPointTo_fromSpecStalk j
    have key : Spec.map (ψc ≫ CommRingCat.ofHom (algebraMap S.R S.K)) ≫
        C.fromSpecStalk (l (IsLocalRing.closedPoint S.R)) =
        Spec.map (C.presheaf.stalkSpecializes huc ≫ χ) ≫
          C.fromSpecStalk (l (IsLocalRing.closedPoint S.R)) := by
      rw [Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc, hl, hl₁,
        Scheme.SpecMap_stalkSpecializes_fromSpecStalk, hj]
    exact Spec.map_injective ((cancel_mono _).1 key)
  have hF4 : C.presheaf.germ U _ hu s * C.presheaf.stalkSpecializes huc t = 1 := by
    apply IsFractionRing.injective (C.presheaf.stalk _) C.functionField
    rw [map_mul, hsg, algebraMap_stalkSpecializes_apply, ht, map_one, mul_inv_cancel₀ hg0]
  have hF5 : ∃ v : S.R, algebraMap S.R S.K v = χ (C.presheaf.germ U _ hu s) := by
    have hi : Spec.map χ ≫ U.fromSpecStalkOfMem _ hu = S.i₁ := by
      rw [← cancel_mono U.ι, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]
      exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk j
    have hsq : Spec.map (CommRingCat.ofHom (chartRingHom sC U s) ≫
        C.presheaf.germ U _ hu ≫ χ) =
        Spec.map (v₀ ≫ CommRingCat.ofHom (algebraMap S.R S.K)) := by
      rw [Spec.map_comp, Spec.map_comp, Spec.map_comp, hv₀, ← S.commSq.w, ← hi]
      dsimp only [chartHom]
      simp only [Category.assoc, Scheme.Opens.fromSpecStalkOfMem_toSpecΓ_assoc]
    have := congrArg (fun f => f.hom Polynomial.X) (Spec.map_injective hsq)
    refine ⟨v₀.hom Polynomial.X, ?_⟩
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
    rw [← this, chartRingHom_X]
  obtain ⟨v, hv⟩ := hF5
  have hmul : ψc t * v = 1 := by
    apply IsFractionRing.injective S.R S.K
    have h3 := congrArg (fun f => f.hom t) hF3
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h3
    rw [map_mul, hv, h3, ← map_mul, mul_comm, hF4, map_one, map_one]
  exact htu ((IsUnit.of_mul_eq_one v hmul).of_map ψc.hom)

/-- If `C` is universally closed over `k` of dimension one, `U` is the regular locus of a nonzero
rational function `g` with section `s`, and at every closed point `g` or `g⁻¹` is regular, then
`chartHom sC U s` satisfies the existence part of the valuative criterion. -/
theorem valuativeExistence_chartHom [IsIntegral C] [UniversallyClosed sC]
    (hdim : topologicalKrullDim C = 1) (g : C.functionField) (hη : genericPoint C ∈ U)
    (hsg : ∀ x (hx : x ∈ U), algebraMap (C.presheaf.stalk x) C.functionField
      (C.presheaf.germ U x hx s) = g)
    (hUset : ∀ x, g ∈ (algebraMap (C.presheaf.stalk x) C.functionField).range → x ∈ U)
    (hpole : ∀ p : C, IsClosed ({p} : Set C) →
      g ∈ (algebraMap (C.presheaf.stalk p) C.functionField).range ∨
        g⁻¹ ∈ (algebraMap (C.presheaf.stalk p) C.functionField).range)
    (hg0 : g ≠ 0) :
    ValuativeCriterion.Existence (chartHom sC U s) := by
  intro S
  have hex : ValuativeCriterion.Existence sC := by
    have h : (ValuativeCriterion.Existence ⊓ @QuasiCompact) sC := by
      rw [← UniversallyClosed.eq_valuativeCriterion]
      infer_instance
    exact h.1
  let π : Spec (.of k[X]) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom Polynomial.C)
  let S' : ValuativeCommSq sC :=
    { R := S.R
      K := S.K
      i₁ := S.i₁ ≫ U.ι
      i₂ := S.i₂ ≫ π
      commSq := ⟨by
        rw [Category.assoc, ← chartHom_comp, ← Category.assoc, S.commSq.w, Category.assoc]⟩ }
  obtain ⟨l, hl₁, -⟩ := (hex S').exists_lift
  change Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) ≫ l = S.i₁ ≫ U.ι at hl₁
  obtain ⟨v₀, hv₀⟩ := Spec.map_surjective S.i₂
  have hrange : Set.range l ⊆ U := by
    rintro _ ⟨z, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint z).map l.continuous).mem_open U.isOpen
      (closedPoint_mem_of_valuativeLift sC U s hdim g hη hsg hUset hpole hg0 S l hl₁)
  let l' := IsOpenImmersion.lift U.ι l (by rwa [Scheme.Opens.range_ι])
  have hl' : l' ≫ U.ι = l := IsOpenImmersion.lift_fac _ _ _
  have h1 : Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) ≫ l' = S.i₁ := by
    rw [← cancel_mono U.ι, Category.assoc, hl', hl₁]
  refine ⟨⟨l', h1, ?_⟩⟩
  obtain ⟨w, hw⟩ := Spec.map_surjective (l' ≫ chartHom sC U s)
  have : Spec.map (w ≫ CommRingCat.ofHom (algebraMap S.R S.K)) =
      Spec.map (v₀ ≫ CommRingCat.ofHom (algebraMap S.R S.K)) := by
    rw [Spec.map_comp, Spec.map_comp, hw, hv₀, ← S.commSq.w, ← h1, Category.assoc]
  have := Spec.map_injective this
  rw [← hw, ← hv₀]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext fun P =>
    IsFractionRing.injective S.R S.K (congrArg (fun f => f.hom P) this))

/-- The image of `P(s)` in the function field is `P` evaluated at the image of `s`. -/
theorem germToFunctionField_chartRingHom [IsIntegral C] [Nonempty U] (P : k[X]) :
    letI := MMP.Mori.functionFieldAlgebra sC
    C.germToFunctionField U (chartRingHom sC U s P) =
      Polynomial.aeval (C.germToFunctionField U s) P := by
  let := MMP.Mori.functionFieldAlgebra sC
  change ((C.germToFunctionField U).hom.comp (chartRingHom sC U s)) P =
    (Polynomial.aeval (C.germToFunctionField U s)).toRingHom P
  congr 1
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Polynomial.aeval_C, chartRingHom, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
    change (C.presheaf.germ U _ _).hom ((sC.appTop ≫ C.presheaf.map (homOfLE le_top).op).hom
      ((Scheme.ΓSpecIso (.of k)).inv.hom a)) = _
    rw [CommRingCat.hom_comp, RingHom.comp_apply, ← CommRingCat.comp_apply,
      TopCat.Presheaf.germ_res]
    rfl
  · simp

/-- If `C` is a proper Noetherian integral curve over `k`, `U` is the regular locus of a nonzero
rational function `g` with section `s`, at every closed point `g` or `g⁻¹` is regular, and
`P(s) ≠ 0` for every nonzero `P ∈ k[X]`, then `chartHom sC U s : U ⟶ 𝔸¹_k` is finite. -/
theorem isFinite_chartHom [IsIntegral C] [IsNoetherian C] [IsProper sC]
    (hdim : topologicalKrullDim C = 1) (g : C.functionField) (hη : genericPoint C ∈ U)
    (hsg : ∀ x (hx : x ∈ U), algebraMap (C.presheaf.stalk x) C.functionField
      (C.presheaf.germ U x hx s) = g)
    (hUset : ∀ x, g ∈ (algebraMap (C.presheaf.stalk x) C.functionField).range → x ∈ U)
    (hpole : ∀ p : C, IsClosed ({p} : Set C) →
      g ∈ (algebraMap (C.presheaf.stalk p) C.functionField).range ∨
        g⁻¹ ∈ (algebraMap (C.presheaf.stalk p) C.functionField).range)
    (hg0 : g ≠ 0) (hs : ∀ P : k[X], P ≠ 0 → chartRingHom sC U s P ≠ 0) :
    IsFinite (chartHom sC U s) := by
  have := locallyOfFiniteType_chartHom sC U s
  have := locallyQuasiFinite_chartHom sC U s hdim hs
  have : IsSeparated (chartHom sC U s ≫ Spec.map (CommRingCat.ofHom Polynomial.C)) := by
    rw [chartHom_comp]
    infer_instance
  have : IsSeparated (chartHom sC U s) :=
    IsSeparated.of_comp _ (Spec.map (CommRingCat.ofHom Polynomial.C))
  have : NoetherianSpace U.toScheme :=
    TopologicalSpace.NoetherianSpace.set (U : Set C)
  have : UniversallyClosed (chartHom sC U s) :=
    UniversallyClosed.of_valuativeCriterion _
      (valuativeExistence_chartHom sC U s hdim g hη hsg hUset hpole hg0)
  have : IsProper (chartHom sC U s) := ⟨⟩
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

end Chart

/-- **A pole-free rational-function chart of a projective curve is finite affine.** Let `C` be a
projective curve over `k` and `g ∈ k(C)` transcendental over `k` such that `g ∈ 𝒪_{p,C}` or
`g⁻¹ ∈ 𝒪_{p,C}` for every closed point `p`. Let `C₀ ⊆ C` be the set of points at whose local ring
`g` is regular. Then `C₀` is an affine open subscheme of `C`, `g` is a section `s` of `𝒪_C` over
`C₀`, and `𝒪(C₀)` is a finitely generated `k[g]`-module (`k[X]` acting through `X ↦ s`). -/
@[mmp "lem_mmp_foundation_projective_curve_rational_function_finite"]
theorem exists_isAffineOpen_regularLocus_finite [MMP.Mori.IsCurve k sC]
    [MMP.Mori.IsProjectiveVariety k sC] (g : C.functionField)
    (hg : letI := MMP.Mori.functionFieldAlgebra sC; Transcendental k g)
    (hpole : ∀ p : C, IsClosed ({p} : Set C) →
      g ∈ (algebraMap (C.presheaf.stalk p) C.functionField).range ∨
        g⁻¹ ∈ (algebraMap (C.presheaf.stalk p) C.functionField).range) :
    ∃ U : C.Opens,
      (U : Set C) = {x | g ∈ (algebraMap (C.presheaf.stalk x) C.functionField).range} ∧
      IsAffineOpen U ∧ ∃ s : Γ(C, U),
        (∀ x (hx : x ∈ U), algebraMap (C.presheaf.stalk x) C.functionField
          (C.presheaf.germ U x hx s) = g) ∧
        letI : Algebra k[X] Γ(C, U) := (chartRingHom sC U s).toAlgebra
        Module.Finite k[X] Γ(C, U) := by
  have hcurve : MMP.Mori.IsCurve k sC := inferInstance
  have : IsIntegral C := hcurve.toIsIntegral
  have hdim : topologicalKrullDim C = 1 := hcurve.topologicalKrullDim_eq_one
  have hproj : IsProjectiveMorphism sC := IsProjectiveVariety.isProjective (k := k)
  have : IsProper sC := isProper_of_isProjectiveMorphism sC hproj
  have : LocallyOfFiniteType sC := hcurve.toLocallyOfFiniteType
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian sC
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace sC
  have : IsNoetherian C := ⟨⟩
  let U : C.Opens := ⟨{x | g ∈ (algebraMap (C.presheaf.stalk x) C.functionField).range},
    isOpen_setOf_mem_range g⟩
  have hη : genericPoint C ∈ U := ⟨g, algebraMap_stalk_genericPoint_apply g⟩
  have : Nonempty U := ⟨⟨_, hη⟩⟩
  obtain ⟨s, hs⟩ := exists_germToFunctionField_eq_of_forall_mem_range C U g (fun x => x.2)
  have hsg : ∀ x (hx : x ∈ U), algebraMap (C.presheaf.stalk x) C.functionField
      (C.presheaf.germ U x hx s) = g := by
    intro x hx
    rw [Scheme.algebraMap_germ_eq_germToFunctionField, hs]
  let := MMP.Mori.functionFieldAlgebra sC
  have hg0 : g ≠ 0 := hg.ne_zero
  have hP : ∀ P : k[X], P ≠ 0 → chartRingHom sC U s P ≠ 0 := by
    intro P hP0 h0
    apply hP0
    refine transcendental_iff.1 hg P ?_
    rw [← hs, ← germToFunctionField_chartRingHom, h0, map_zero]
  have hfin := isFinite_chartHom sC U s hdim g hη hsg (fun x hx => hx) hpole hg0 hP
  have hUaff : IsAffine U.toScheme := isAffine_of_isAffineHom (chartHom sC U s)
  refine ⟨U, rfl, hUaff, s, hsg, ?_⟩
  have : IsIso U.toSpecΓ := by
    unfold Scheme.Opens.toSpecΓ
    infer_instance
  have h2 : IsFinite (Spec.map (CommRingCat.ofHom (chartRingHom sC U s))) := by
    have e : Spec.map (CommRingCat.ofHom (chartRingHom sC U s)) =
        inv U.toSpecΓ ≫ chartHom sC U s := by
      simp [chartHom]
    rw [e]
    infer_instance
  rwa [IsFinite.SpecMap_iff] at h2

/-! ### Multiplicities at closed points and orders of vanishing -/

/-- A rational function lies in the semi-local ring of `{p}` iff it lies in the image of the local
ring at `p`. -/
theorem mem_semilocalRing_singleton [IsIntegral C] (p : C) (x : C.functionField) :
    x ∈ semilocalRing ({p} : Finset C) ↔
      x ∈ (algebraMap (C.presheaf.stalk p) C.functionField).range := by
  simp [semilocalRing]

/-- The local ring at `p` is isomorphic to the semi-local ring of `{p}`. -/
def stalkEquivSemilocalRing [IsIntegral C] (p : C) :
    C.presheaf.stalk p ≃+* semilocalRing ({p} : Finset C) :=
  RingEquiv.ofBijective
    ((algebraMap (C.presheaf.stalk p) C.functionField).codRestrict _
      fun a => (mem_semilocalRing_singleton p _).2 ⟨a, rfl⟩)
    ⟨fun a b h => IsFractionRing.injective (C.presheaf.stalk p) C.functionField
      (congrArg Subtype.val h), fun ⟨x, hx⟩ => by
        obtain ⟨a, ha⟩ := (mem_semilocalRing_singleton p x).1 hx
        exact ⟨a, Subtype.ext ha⟩⟩

/-- The image of `a` under `stalkEquivSemilocalRing p` is `a` viewed in the function field. -/
@[simp]
theorem coe_stalkEquivSemilocalRing [IsIntegral C] (p : C) (a : C.presheaf.stalk p) :
    (stalkEquivSemilocalRing p a : C.functionField) =
      algebraMap (C.presheaf.stalk p) C.functionField a := rfl

/-- The local ring at `p` is `k`-algebra isomorphic to the semi-local ring of `{p}`. -/
def stalkAlgEquivSemilocalRing [IsIntegral C] (p : C) :
    letI := MMP.Mori.stalkAlgebra sC p
    letI := semilocalRingAlgebra sC ({p} : Finset C)
    C.presheaf.stalk p ≃ₐ[k] semilocalRing ({p} : Finset C) :=
  letI := MMP.Mori.stalkAlgebra sC p
  letI := semilocalRingAlgebra sC ({p} : Finset C)
  AlgEquiv.ofRingEquiv (f := stalkEquivSemilocalRing p) fun c => by
    let := MMP.Mori.functionFieldAlgebra sC
    have := MMP.Mori.isScalarTower_stalk_functionField sC p
    apply Subtype.ext
    rw [coe_stalkEquivSemilocalRing, ← IsScalarTower.algebraMap_apply]
    rfl

@[simp]
theorem stalkAlgEquivSemilocalRing_apply [IsIntegral C] (p : C) (a : C.presheaf.stalk p) :
    letI := MMP.Mori.stalkAlgebra sC p
    letI := semilocalRingAlgebra sC ({p} : Finset C)
    stalkAlgEquivSemilocalRing sC p a = stalkEquivSemilocalRing p a :=
  rfl

/-- At a point `p` of codimension one, `ord_p(a / b) = ord(a) - ord(b)` for nonzero `a`, `b` in
the local ring at `p`. -/
theorem ord_div_eq_sub [IsIntegral C] [IsLocallyNoetherian C] {p : C}
    (hz : Order.coheight p = 1) {a b : C.presheaf.stalk p} (ha : a ≠ 0) (hb : b ≠ 0) :
    C.ord (algebraMap _ C.functionField a / algebraMap _ C.functionField b) p =
      ((Ring.ord (C.presheaf.stalk p) a).toNat : ℤ) - (Ring.ord (C.presheaf.stalk p) b).toNat := by
  have : Ring.KrullDimLE 1 (C.presheaf.stalk p) := krullDimLE_of_coheight_le hz.le
  have hinj := IsFractionRing.injective (C.presheaf.stalk p) C.functionField
  have hne : algebraMap _ C.functionField a / algebraMap _ C.functionField b ≠ 0 :=
    div_ne_zero ((map_ne_zero_iff _ hinj).2 ha) ((map_ne_zero_iff _ hinj).2 hb)
  rw [Scheme.ord_eq_iff hz hne]
  unfold Scheme.ordHom
  have ha' := mem_nonZeroDivisors_of_ne_zero ha
  have hb' := mem_nonZeroDivisors_of_ne_zero hb
  rw [map_div₀, Ring.ordFrac_eq_ord _ ha, Ring.ordFrac_eq_ord _ hb,
    Ring.ordMonoidWithZeroHom_eq_coe _ ha' (ENat.natCast_toNat (Ring.ord_ne_top ha')).symm,
    Ring.ordMonoidWithZeroHom_eq_coe _ hb' (ENat.natCast_toNat (Ring.ord_ne_top hb')).symm,
    ← WithZero.coe_div, ← ofAdd_sub]

/-- On an irreducible quasi-sober space of dimension one, a closed point is not the generic
point. -/
theorem ne_genericPoint_of_isClosed_of_dim_eq_one {X : Type*} [TopologicalSpace X] [QuasiSober X]
    [IrreducibleSpace X] (hdim : topologicalKrullDim X = 1) {p : X}
    (hp : IsClosed ({p} : Set X)) : p ≠ genericPoint X := by
  rintro rfl
  have hsub : Subsingleton X := ⟨fun x y => by
    have hx : x ∈ ({genericPoint X} : Set X) := by
      rw [← hp.closure_eq]
      exact (genericPoint_specializes x).mem_closure
    have hy : y ∈ ({genericPoint X} : Set X) := by
      rw [← hp.closure_eq]
      exact (genericPoint_specializes y).mem_closure
    rw [hx, hy]⟩
  have := topologicalKrullDim_zero_of_discreteTopology X
  rw [hdim] at this
  exact absurd this (by norm_num)

/-- **Kollár's multiplicity at a closed point of a curve.** At a closed point `p` of a
quasi-projective curve, `e_p(f) = e_{𝒪_{p,C}}(f) = ord_p(f) · [κ(p) : k]` for `f ∈ k(C)^×`. -/
theorem eMultAt_singleton_eq [MMP.Mori.IsCurve k sC] [IsLocallyNoetherian C]
    (hC : Stacks.HProjective.IsQuasiProjective sC) {p : C}
    (hp : IsClosed ({p} : Set C)) {f : C.functionField} (hf : f ≠ 0) :
    eMultAt sC {p} f = C.ord f p * (sC.residueDegree p : ℤ) := by
  have hcurve : MMP.Mori.IsCurve k sC := inferInstance
  have : IsIntegral C := hcurve.toIsIntegral
  have hdim : topologicalKrullDim C = 1 := hcurve.topologicalKrullDim_eq_one
  have hpη := ne_genericPoint_of_isClosed_of_dim_eq_one hdim hp
  have hpc : ∀ q ∈ ({p} : Finset C), IsClosed ({q} : Set C) := by
    intro q hq
    rwa [Finset.mem_singleton.1 hq]
  obtain ⟨-, -, hfr, -, -, hcol⟩ := semilocalRing_properties sC hC hdim ({p} : Finset C)
    (Finset.singleton_nonempty p) hpc
  let := MMP.Mori.stalkAlgebra sC p
  let := semilocalRingAlgebra sC ({p} : Finset C)
  let e := stalkAlgEquivSemilocalRing sC p
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (C.presheaf.stalk p) f
  have hinj := IsFractionRing.injective (C.presheaf.stalk p) C.functionField
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hB : algebraMap (C.presheaf.stalk p) C.functionField b ≠ 0 :=
    (map_ne_zero_iff _ hinj).2 hb0
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hab
    exact hf hab.symm
  have hea : e a ∈ nonZeroDivisors (semilocalRing ({p} : Finset C)) :=
    mem_nonZeroDivisors_of_ne_zero (by simpa using ha0)
  have heb : e b ∈ nonZeroDivisors (semilocalRing ({p} : Finset C)) :=
    mem_nonZeroDivisors_of_ne_zero (by simpa using hb0)
  have hkey : algebraMap (semilocalRing ({p} : Finset C)) C.functionField (e a) =
      f * algebraMap (semilocalRing ({p} : Finset C)) C.functionField (e b) := by
    change algebraMap (C.presheaf.stalk p) C.functionField a =
      f * algebraMap (C.presheaf.stalk p) C.functionField b
    rw [← hab, div_mul_cancel₀ _ hB]
  have h1 := (Kollar.eMultFrac_eq_of_eq_mul k C.functionField hcol hea heb hkey).2
  have hq : ∀ c : C.presheaf.stalk p, c ∈ nonZeroDivisors (C.presheaf.stalk p) →
      Module.Finite k (C.presheaf.stalk p ⧸ Ideal.span {c}) ∧
      eMult k (e c) = Module.finrank k (C.presheaf.stalk p ⧸ Ideal.span {c}) := by
    intro c hc
    have hc' : e c ∈ nonZeroDivisors (semilocalRing ({p} : Finset C)) :=
      mem_nonZeroDivisors_of_ne_zero (by simpa using nonZeroDivisors.ne_zero hc)
    let q := Ideal.quotientEquivAlg (R₁ := k) (Ideal.span {c}) (Ideal.span {e c}) e
      (by rw [Ideal.map_span, Set.image_singleton]; rfl)
    have := hcol (e c) hc'
    exact ⟨Module.Finite.equiv q.symm.toLinearEquiv, q.toLinearEquiv.finrank_eq.symm⟩
  have hz : Order.coheight p = 1 := IsCurve.coheight_eq_one sC hpη
  obtain ⟨hfa, hea'⟩ := hq a (mem_nonZeroDivisors_of_ne_zero ha0)
  obtain ⟨hfb, heb'⟩ := hq b hb
  rw [show eMultAt sC {p} f = eMultFrac k C.functionField f (R := semilocalRing ({p} : Finset C))
    from rfl, h1, hea', heb', finrank_eq_length_toNat_mul k (O := C.presheaf.stalk p),
    finrank_eq_length_toNat_mul k (O := C.presheaf.stalk p) (C.presheaf.stalk p ⧸ Ideal.span {b}),
    ← hab, ord_div_eq_sub hz ha0 hb0, Stacks.Chow.residueDegree_eq_finrank_residueField k sC p]
  push_cast
  rw [sub_mul]
  rfl

/-- **Kollár Lemma 1.20.5, p. 19: a rational function on a projective curve has degree `0`.** Let
`C` be a projective curve over `k` and `f ∈ k(C)^×`. Then there is a finite set `F` of closed
points of `C` with `e_p(f) = 0` for every closed point `p ∉ F` and `∑_{p ∈ F} e_p(f) = 0`.
Here `e_p(f) = eMultAt sC {p} f` is Kollár's
local multiplicity `e_R(f)` computed in the local ring `R = 𝒪_{p,C}` (the semi-local ring
`semilocalRing {p}`, through which `eMultAt` depends on `p`); at a closed point it equals
`ord_p(f) · [κ(p) : k]` (`MMP.Resolution.eMultAt_singleton_eq`). -/
@[mmp "lem_kr1a_degree_zero_sum_of_rational_function"]
theorem exists_finset_sum_eMultAt_eq_zero [MMP.Mori.IsCurve k sC]
    [MMP.Mori.IsProjectiveVariety k sC] (f : C.functionField) (hf : f ≠ 0) :
    ∃ F : Finset C, (∀ p ∈ F, IsClosed ({p} : Set C)) ∧
      (∀ p : C, IsClosed ({p} : Set C) → p ∉ F → eMultAt sC {p} f = 0) ∧
      ∑ p ∈ F, eMultAt sC {p} f = 0 := by
  classical
  have hcurve : MMP.Mori.IsCurve k sC := inferInstance
  have : IsIntegral C := hcurve.toIsIntegral
  have hdim : topologicalKrullDim C = 1 := hcurve.topologicalKrullDim_eq_one
  have hproj : IsProjectiveMorphism sC := IsProjectiveVariety.isProjective (k := k)
  have hC : Stacks.HProjective.IsQuasiProjective sC :=
    (isQuasiProjective_iff_hProjectiveIsQuasiProjective sC).mp hproj.isQuasiProjective
  have hproper : IsProper sC := isProper_of_isProjectiveMorphism sC hproj
  have : LocallyOfFiniteType sC := hcurve.toLocallyOfFiniteType
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian sC
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace sC
  let : C.Over (Spec (.of k)) := ⟨sC⟩
  have h0 := @Stacks.Chow.principalDivisorDegree_eq_zero k _ C _ hcurve hproper _ f hf
  have hfin := Stacks.Chow.finite_support_ord (X := C) f
  have hne : ∀ x : C, C.ord f x ≠ 0 → x ≠ genericPoint C := by
    intro x hx hxη
    apply hx
    apply Scheme.ord_eq_zero_of_coheight_neq_one
    rw [hxη]
    intro h
    have : IsMax (genericPoint C) := fun b _ => genericPoint_specializes b
    rw [Order.coheight_eq_zero.2 this] at h
    exact zero_ne_one h
  refine ⟨hfin.toFinset, fun p hp =>
    Stacks.AlgebraicGeometry.AmpleDimensionOne.isClosed_singleton_of_ne_genericPoint C hdim
      (hne p ((hfin.mem_toFinset).1 hp)), fun p hp hpF => ?_, ?_⟩
  · rw [eMultAt_singleton_eq sC hC hp hf]
    have : C.ord f p = 0 := by simpa [hfin.mem_toFinset] using hpF
    rw [this, zero_mul]
  · unfold Stacks.Chow.principalDivisorDegree at h0
    rw [finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) (by
      intro x hx
      simp only [Function.mem_support] at hx
      simp only [Set.Finite.coe_toFinset, Function.mem_support]
      exact left_ne_zero_of_mul hx)] at h0
    rw [← h0]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hpη := hne p ((hfin.mem_toFinset).1 hp)
    exact eMultAt_singleton_eq sC hC
      (Stacks.AlgebraicGeometry.AmpleDimensionOne.isClosed_singleton_of_ne_genericPoint C hdim hpη)
      hf

end MMP.Resolution
