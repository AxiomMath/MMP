module
public import MMP.AlgebraicGeometry.Singularities.Semismooth.DoubleCoverFlat
import all MMP.AlgebraicGeometry.Singularities.Semismooth.DoubleCoverFlat
import all MMP.AlgebraicGeometry.Singularities.Semismooth.SingularLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.Characterization

/-!
# The branch locus of the double cover `D_ν → D_X` of a semismooth `n`-fold

A closed point of the reduced singular locus `D_X` of a semismooth `n`-fold is not a smooth point,
so it is a double normal crossing point or a pinch point. Over a double normal crossing point the
restriction `D_ν → D_X` of the normalization is, after completion, two copies of an isomorphism,
hence étale; over a pinch point it is `k[[x₁, x₃, …]] → k[[u, x₃, …]]`, `x₁ ↦ u²`, whose closed
fibre `k[u]/(u²)` is not reduced, so it is not étale.

## Main results

* `MMP.Flips.BranchLocus.exists_etale_of_isDoubleNormalCrossingPoint`: over a double normal
  crossing point, `D_ν → D_X` is étale on a neighbourhood.
* `MMP.Flips.BranchLocus.not_etale_of_isPinchPoint`: over a pinch point, `D_ν → D_X` is étale on
  no neighbourhood.

## Implementation notes

Over a pinch point the completed local ring of `X^ν` at a point `y` over `x` is identified, as
an algebra over `𝒪̂_{X,x} ≅ k[[x]]/(x₀² - x₁x₂²)`, with `k[[x₂, …]][[u]]`, `x₀ ↦ u x₂`, `x₁ ↦ u²`.
The map `k[[x₂, …]][[u]] → k[u]/(u²)` killing `x₂, …` kills the image of `𝔪_x` and the ideal of
`D_ν` (which lies in the prime `(x₂, …)` over the singular locus), but not `u`; so `𝔪_x` does not
generate the maximal ideal of `𝒪_{D_ν,y}`, and `D_ν → D_X` is ramified at `y`.

Over a double normal crossing point the étale locus of `D_ν → D_X` is open and `D_ν → D_X` is
finite, hence closed, so étaleness at the points over `x` gives étaleness over a neighbourhood.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 12.2.1
-/

namespace MMP.Flips.BranchLocus

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Flips MMP.Flips.Normalization

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}

section PinchAlgebra

open PowerSeries

variable {k' : Type*} [Field k'] (m : ℕ)

/-- The test map `B⟦u⟧ → k⟦u⟧ ⧸ (u²)`, `B = k[[x₂, …]]`: the variables of `B` go to `0`. -/
private noncomputable def pinchTest : (MvPowerSeries (Fin (m + 1)) k')⟦X⟧ →+* k'⟦X⟧ ⧸
    Ideal.span {(PowerSeries.X : k'⟦X⟧) ^ 2} :=
  (Ideal.Quotient.mk _).comp (PowerSeries.map MvPowerSeries.constantCoeff)

private theorem pinchModelEquiv_mk_of_eq (f : MvPowerSeries (Fin (m + 3)) k')
    (p : Polynomial (MvPowerSeries (Fin (m + 1)) k')⟦X⟧)
    (hf : pinchTowerEquiv k' m f = (p : (MvPowerSeries (Fin (m + 1)) k')⟦X⟧⟦X⟧)) :
    pinchModelEquiv k' m (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ p := by
  simp only [pinchModelEquiv, AlgEquiv.ofRingEquiv_apply, RingEquiv.trans_apply,
    AlgEquiv.coe_ringEquiv]
  erw [Ideal.quotientEquivAlg_mk]
  rw [hf]
  exact pinchWeierstrassEquiv_mk k' m _

/-- The composite of the pinch model with the test map kills every variable. -/
private theorem pinchTest_pinchMap_mk_X (i : Fin (m + 3)) :
    pinchTest m (pinchMap (MvPowerSeries.X 0 : MvPowerSeries (Fin (m + 1)) k')
      (pinchModelEquiv k' m (Ideal.Quotient.mk _ (MvPowerSeries.X i)))) = 0 := by
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
  · rw [pinchModelEquiv_mk_of_eq m _ Polynomial.X (by
      simp only [pinchTowerEquiv, AlgEquiv.trans_apply, MvPowerSeries.finSuccEquiv_X_zero]
      simp [powerSeriesMapAlgEquiv, mapAlgHom_apply]), pinchMap_mk_X]
    simp [pinchTest]
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
  · rw [pinchModelEquiv_mk_of_eq m _ (Polynomial.C PowerSeries.X) (by
      simp only [pinchTowerEquiv, AlgEquiv.trans_apply, MvPowerSeries.finSuccEquiv_X_succ]
      simp [powerSeriesMapAlgEquiv, mapAlgHom_apply, MvPowerSeries.finSuccEquiv_X_zero]),
      pinchMap_mk_C]
    simp only [pinchTest, RingHom.comp_apply, expand_X, map_pow, map_X]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  · rw [pinchModelEquiv_mk_of_eq m _ (Polynomial.C (PowerSeries.C (MvPowerSeries.X j'))) (by
      simp only [pinchTowerEquiv, AlgEquiv.trans_apply, MvPowerSeries.finSuccEquiv_X_succ]
      simp [powerSeriesMapAlgEquiv, mapAlgHom_apply, MvPowerSeries.finSuccEquiv_X_succ]),
      pinchMap_mk_C]
    simp [pinchTest]

/-- **The test map on a factor of the normalization of a pinch model.** Let `L` be a local normal
domain receiving `ψ : k[[x₀, …, x_{m+2}]]/(x₀² - x₁x₂²) → L`, integral and birational, with no
non-zero-divisor in its kernel, so that `L ≅ k[[u, x₂, …]]` with `x₀ ↦ u x₂`, `x₁ ↦ u²`. There is
a ring map `τ : L → k[u]/(u²)` that kills `ψ(𝔪)`, kills a prime of `L` containing `ψ x₀` and
`ψ x₂`, and does not kill some element of `𝔪_L` (the image of `u`). -/
private theorem exists_pinchTest {L : Type*} [CommRing L] [IsLocalRing L] [IsDomain L]
    [IsIntegrallyClosed L]
    (ψ : (MvPowerSeries (Fin (m + 3)) k' ⧸ Ideal.span
      {(MvPowerSeries.X 0 ^ 2 - MvPowerSeries.X 1 * MvPowerSeries.X 2 ^ 2 :
        MvPowerSeries (Fin (m + 3)) k')}) →+* L)
    (hint : ∀ l, ψ.IsIntegralElem l)
    (hbir : ∀ l, ∃ r s, s ∈ nonZeroDivisors _ ∧ ψ s * l = ψ r)
    (hnz : ∀ s ∈ nonZeroDivisors _, ψ s ≠ 0) :
    ∃ τ : L →+* k'⟦X⟧ ⧸ Ideal.span {(PowerSeries.X : k'⟦X⟧) ^ 2},
      (∀ f ∈ IsLocalRing.maximalIdeal (MvPowerSeries (Fin (m + 3)) k'),
        τ (ψ (Ideal.Quotient.mk _ f)) = 0) ∧
      (∃ P : Ideal L, P.IsPrime ∧ P ≤ RingHom.ker τ ∧
        ψ (Ideal.Quotient.mk _ (MvPowerSeries.X 0)) ∈ P ∧
        ψ (Ideal.Quotient.mk _ (MvPowerSeries.X 2)) ∈ P) ∧
      (∃ l ∈ IsLocalRing.maximalIdeal L, τ l ≠ 0) := by
  set B := MvPowerSeries (Fin (m + 1)) k'
  set b : B := MvPowerSeries.X 0
  have : IsRegularLocalRing B := MvPowerSeries.isRegularLocalRing k' (m + 1)
  have : IsDomain B := IsRegularLocalRing.isDomain B
  have hb : b ≠ 0 := fun h => by
    have := congrArg (MvPowerSeries.coeff (Finsupp.single 0 1)) h
    simp [b, MvPowerSeries.coeff_X] at this
  set ι := pinchModelEquiv k' m
  have : IsDomain (PinchRing b) := (pinchMap_injective b hb).isDomain
  have : IsDomain (MvPowerSeries (Fin (m + 3)) k' ⧸ Ideal.span
      {(MvPowerSeries.X 0 ^ 2 - MvPowerSeries.X 1 * MvPowerSeries.X 2 ^ 2 :
        MvPowerSeries (Fin (m + 3)) k')}) := ι.toRingEquiv.toMulEquiv.isDomain
  set ψ' : PinchRing b →+* L := ψ.comp ι.symm.toRingEquiv.toRingHom
  have hψ' : ∀ r, ψ' (ι r) = ψ r := fun r => by simp [ψ']
  have hψ'inj : Function.Injective ψ' := by
    rw [injective_iff_map_eq_zero]
    intro r hr
    by_contra hr0
    refine hnz (ι.symm r) ?_ hr
    exact mem_nonZeroDivisors_of_ne_zero (by simpa using hr0)
  let : Algebra (PinchRing b) L := ψ'.toAlgebra
  have hal : ∀ r, algebraMap (PinchRing b) L r = ψ' r := fun r => by
    rw [RingHom.algebraMap_toAlgebra]
  have : FaithfulSMul (PinchRing b) L := (faithfulSMul_iff_algebraMap_injective _ _).2 hψ'inj
  have : Algebra.IsIntegral (PinchRing b) L := ⟨fun l => by
    obtain ⟨p, hp, hpl⟩ := hint l
    refine ⟨p.map ι.toRingEquiv.toRingHom, hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    convert hpl using 2
    all_goals try rfl
    ext r
    exact (hal _).trans (hψ' r)⟩
  have hL : ∀ l : L, ∃ r s : PinchRing b, s ≠ 0 ∧
      algebraMap (PinchRing b) L s * l = algebraMap (PinchRing b) L r := fun l => by
    obtain ⟨r, s, hs, h⟩ := hbir l
    refine ⟨ι r, ι s, by simpa using nonZeroDivisors.ne_zero hs, ?_⟩
    rw [hal, hal, hψ', hψ']
    exact h
  let : Algebra (PinchRing b) B⟦X⟧ := (pinchMap b).toAlgebra
  have : FaithfulSMul (PinchRing b) B⟦X⟧ :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (pinchMap_injective b hb)
  have : Algebra.IsIntegral (PinchRing b) B⟦X⟧ := ⟨fun f => pinchMap_isIntegralElem b f⟩
  have : IsRegularLocalRing B⟦X⟧ := PowerSeries.isRegularLocalRing B
  have : IsDomain B⟦X⟧ := IsRegularLocalRing.isDomain _
  have : UniqueFactorizationMonoid B⟦X⟧ := IsRegularLocalRing.uniqueFactorizationMonoid _
  obtain ⟨σ⟩ := nonempty_algEquiv_of_isIntegrallyClosed_of_birational (PinchRing b) L B⟦X⟧ hL
    (fun f => by
      obtain ⟨r, s, hs, h⟩ := pinchMap_birational hb f
      exact ⟨r, s, fun h0 => hs (by rw [h0, map_zero]), h⟩)
  have hσ : ∀ a, σ (ψ a) = pinchMap b (ι a) := fun a => by
    rw [← hψ', ← hal, AlgEquiv.commutes]
    rfl
  set χ : B⟦X⟧ →+* k'⟦X⟧ := PowerSeries.map MvPowerSeries.constantCoeff
  have hτ : ∀ l, (pinchTest m).comp σ.toRingEquiv.toRingHom l = Ideal.Quotient.mk _ (χ (σ l)) :=
    fun _ => rfl
  refine ⟨(pinchTest m).comp σ.toRingEquiv.toRingHom, ?_, ?_, ?_⟩
  · intro f hf
    have hmax : Ideal.span (Set.range (MvPowerSeries.X : Fin (m + 3) →
        MvPowerSeries (Fin (m + 3)) k')) = IsLocalRing.maximalIdeal _ := by
      rw [MvPowerSeries.span_X_eq_ker_constantCoeff,
        IsLocalRing.ker_eq_maximalIdeal (MvPowerSeries.constantCoeff :
          MvPowerSeries (Fin (m + 3)) k' →+* k') fun c => ⟨MvPowerSeries.C c, by simp⟩]
    rw [← hmax] at hf
    have hle : Ideal.span (Set.range (MvPowerSeries.X : Fin (m + 3) →
        MvPowerSeries (Fin (m + 3)) k')) ≤
        RingHom.ker (((pinchTest m).comp σ.toRingEquiv.toRingHom).comp
          (ψ.comp (Ideal.Quotient.mk _))) := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      change pinchTest m (σ (ψ (Ideal.Quotient.mk _ (MvPowerSeries.X i)))) = 0
      rw [hσ]
      exact pinchTest_pinchMap_mk_X m i
    exact hle hf
  · refine ⟨RingHom.ker (χ.comp σ.toRingEquiv.toRingHom), RingHom.ker_isPrime _, fun l hl => ?_,
      ?_, ?_⟩
    · rw [RingHom.mem_ker] at hl ⊢
      rw [hτ]
      change Ideal.Quotient.mk _ (χ (σ l)) = 0
      rw [show χ (σ l) = 0 from hl, map_zero]
    · rw [RingHom.mem_ker]
      change χ (σ (ψ _)) = 0
      rw [hσ, pinchModelEquiv_mk_X_zero, pinchMap_mk_X]
      simp only [χ, b, map_mul, PowerSeries.map_X, PowerSeries.map_C]
      erw [MvPowerSeries.constantCoeff_X]
      simp
    · rw [RingHom.mem_ker]
      change χ (σ (ψ _)) = 0
      rw [hσ, pinchModelEquiv_mk_X_two, pinchMap_mk_C]
      simp only [χ, PowerSeries.map_C, expand_C]
      erw [MvPowerSeries.constantCoeff_X]
      simp
  · refine ⟨σ.symm PowerSeries.X, ?_, ?_⟩
    · rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro h
      have := (h.map σ)
      rw [AlgEquiv.apply_symm_apply, PowerSeries.isUnit_iff_constantCoeff] at this
      simp at this
    · rw [hτ]
      change Ideal.Quotient.mk _ (χ (σ (σ.symm PowerSeries.X))) ≠ 0
      rw [AlgEquiv.apply_symm_apply]
      simp only [χ, PowerSeries.map_X, ne_eq, Ideal.Quotient.eq_zero_iff_mem,
        Ideal.mem_span_singleton]
      rintro ⟨g, hg⟩
      have := congrArg (PowerSeries.coeff 1) hg
      rw [pow_two, mul_assoc, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_X_mul] at this
      simp at this

end PinchAlgebra

section Glue

open IsLocalRing

/-- **The algebraic contradiction.** Let `f : R → S` and `π : S ↠ T` be maps of local rings
with `𝔪_R` generating `𝔪_T`. A ring map `τ` on `S` killing `ker π` and `f(𝔪_R)` kills `𝔪_S`. -/
private theorem eq_zero_of_map_maximalIdeal {R S T C : Type*} [CommRing R] [CommRing S]
    [CommRing T] [CommRing C] [IsLocalRing R] [IsLocalRing S] [IsLocalRing T]
    (f : R →+* S) (π : S →+* T) (hπ : Function.Surjective π)
    (hm : (maximalIdeal R).map (π.comp f) = maximalIdeal T)
    (τ : S →+* C) (hK : ∀ s, π s = 0 → τ s = 0)
    (hf : ∀ r ∈ maximalIdeal R, τ (f r) = 0)
    {s : S} (hs : s ∈ maximalIdeal S) : τ s = 0 := by
  have := IsLocalHom.of_surjective π hπ
  have h1 : π s ∈ maximalIdeal T := map_nonunit π s hs
  rw [← hm, ← Ideal.map_map] at h1
  obtain ⟨s', hs', he⟩ := (Ideal.mem_map_iff_of_surjective π hπ).mp h1
  have h2 : τ (s - s') = 0 := hK _ (by rw [map_sub, he, sub_self])
  have h3 : τ s' = 0 :=
    (Ideal.map_le_iff_le_comap.mpr hf : (maximalIdeal R).map f ≤ RingHom.ker τ) hs'
  rwa [map_sub, h3, sub_zero] at h2

/-- **Unramifiedness on stalks.** In a commutative square `φ ≫ ι_B = ι_A ≫ ν` with `ι_B` a closed
immersion and `φ` locally of finite type and unramified at `y`, the maximal ideal of `𝒪_{X,x}`,
`x = ν (ι_A y)`, generates the maximal ideal of `𝒪_{A,y}`. -/
private theorem map_maximalIdeal_eq_of_formallyUnramified {A' B' Y X : Scheme.{u}}
    (φ : A' ⟶ B') (ιA : A' ⟶ Y) (ιB : B' ⟶ X) (ν : Y ⟶ X) [IsClosedImmersion ιB]
    [LocallyOfFiniteType φ] (hφ : φ ≫ ιB = ιA ≫ ν) (y : A')
    (hfu : (φ.stalkMap y).hom.FormallyUnramified) :
    (maximalIdeal (X.presheaf.stalk (ν (ιA y)))).map
        ((ιA.stalkMap y).hom.comp (ν.stalkMap (ιA y)).hom) =
      maximalIdeal (A'.presheaf.stalk y) := by
  have hft : (φ.stalkMap y).hom.EssFiniteType := LocallyOfFiniteType.stalkMap φ y
  let := (φ.stalkMap y).hom.toAlgebra
  have : Algebra.FormallyUnramified (B'.presheaf.stalk (φ y)) (A'.presheaf.stalk y) := hfu
  have : Algebra.EssFiniteType (B'.presheaf.stalk (φ y)) (A'.presheaf.stalk y) := by
    rw [← RingHom.essFiniteType_algebraMap]; exact hft
  have : IsLocalHom (algebraMap (B'.presheaf.stalk (φ y)) (A'.presheaf.stalk y)) :=
    inferInstanceAs <| IsLocalHom (φ.stalkMap y).hom
  have h1 := Algebra.FormallyUnramified.map_maximalIdeal
    (R := B'.presheaf.stalk (φ y)) (S := A'.presheaf.stalk y)
  rw [← map_maximalIdeal_of_surjective _ (ιB.stalkMap_surjective (φ y)), Ideal.map_map] at h1
  have h2 := Scheme.Hom.stalkMap_comp φ ιB y
  have h3 := Scheme.Hom.stalkMap_congr_hom (φ ≫ ιB) (ιA ≫ ν) hφ y
  have h4 := Scheme.Hom.stalkMap_comp ιA ν y
  rw [h2] at h3
  rw [h4] at h3
  have h5 : (algebraMap (B'.presheaf.stalk (φ y)) (A'.presheaf.stalk y)).comp
      (ιB.stalkMap (φ y)).hom = ((ιA.stalkMap y).hom.comp (ν.stalkMap (ιA y)).hom).comp
        (X.presheaf.stalkCongr (.of_eq (by rw [← Scheme.Hom.comp_apply, hφ,
          Scheme.Hom.comp_apply]))).hom.hom := by
    rw [RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp, h3]
    rfl
  rw [h5, ← Ideal.map_map, map_maximalIdeal_of_surjective _
    (X.presheaf.stalkCongr _).commRingCatIsoToRingEquiv.surjective] at h1
  exact h1

end Glue

/-- A point of the reduced singular locus maps to a point of `X` outside the smooth locus. -/
public theorem subschemeι_notMem_smoothLocus
    (z : (MMP.Resolution.reducedSingularLocus sX).subscheme) :
    (MMP.Resolution.reducedSingularLocus sX).subschemeι z ∉ MMP.Mori.smoothLocus sX := by
  have hz : (MMP.Resolution.reducedSingularLocus sX).subschemeι z ∈
      ((MMP.Resolution.reducedSingularLocus sX).support : Set X) := by
    rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨z, rfl⟩
  rw [MMP.Resolution.support_reducedSingularLocus] at hz
  exact hz

/-- Regularity of the localization at equal primes. -/
private theorem isRegularLocalRing_localization_congr {R : Type*} [CommRing R] {I J : Ideal R}
    [I.IsPrime] [J.IsPrime] (h : I = J) :
    IsRegularLocalRing (Localization.AtPrime I) ↔ IsRegularLocalRing (Localization.AtPrime J) := by
  subst h; rfl

/-- **The contradiction at a point of `X^ν` over a pinch point.** Let `y ∈ X^ν` lie over a pinch
point `x`, and `π : 𝒪_{X^ν,y} ↠ T` a quotient whose kernel lies in every prime whose point maps
to the singular locus. Then `𝔪_x` does not generate `𝔪_T`. -/
private theorem false_of_pinch_model [IsReduced X] [LocallyOfFiniteType sX] {m : ℕ}
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (hsing : ∀ w : X, w ∈ MMP.Mori.smoothLocus sX ↔ IsRegularLocalRing (X.presheaf.stalk w))
    (y : Scheme.normalizationScheme X hX)
    (hmod : HasCompletedLocalModel sX (X.normalization hX y)
      (MvPowerSeries.X 0 ^ 2 - MvPowerSeries.X 1 * MvPowerSeries.X 2 ^ 2 :
        MvPowerSeries (Fin (m + 3)) k))
    {T : Type u} [CommRing T] [IsLocalRing T]
    (π : (X.normalizationScheme hX).presheaf.stalk y →+* T) (hπ : Function.Surjective π)
    (hK : ∀ (p : Ideal ((X.normalizationScheme hX).presheaf.stalk y)) [p.IsPrime],
      X.normalization hX ((X.normalizationScheme hX).fromSpecStalk y ⟨p, inferInstance⟩) ∉
        MMP.Mori.smoothLocus sX → RingHom.ker π ≤ p)
    (hm : (IsLocalRing.maximalIdeal (X.presheaf.stalk (X.normalization hX y))).map
      (π.comp ((X.normalization hX).stalkMap y).hom) = IsLocalRing.maximalIdeal T) : False := by
  obtain ⟨hND, ψ₀, hint, hbir, hnz, hψ₀alg⟩ :=
    exists_completion_factor_normalization (sX := sX) hX y
  have hexcX := SingLoc.isExcellent_stalk' (sX := sX) (X.normalization hX y)
  have : IsNoetherianRing (X.presheaf.stalk (X.normalization hX y)) := hexcX.1.1
  have hG : IsGRing (X.presheaf.stalk (X.normalization hX y)) := hexcX.1.2.1
  have : LocallyOfFiniteType (X.normalization hX ≫ sX) := by
    have : IsFinite (X.normalization hX) := Scheme.isFinite_normalization
      (isNagataScheme_of_locallyOfFiniteType_over_field k sX) hX
    infer_instance
  have hexc := SingLoc.isExcellent_stalk' (sX := X.normalization hX ≫ sX) y
  have : IsNoetherianRing ((X.normalizationScheme hX).presheaf.stalk y) := hexc.1.1
  let := (stalkStructureMap sX (X.normalization hX y)).toAlgebra
  obtain ⟨e⟩ := hmod
  obtain ⟨h₁, h₂, h₃⟩ := props_comp_symm_of_ringEquiv ψ₀ e.toRingEquiv hint hbir hnz
  obtain ⟨τ, hτm, ⟨P, hP, hPτ, hP0, hP2⟩, l, hl, hl'⟩ := exists_pinchTest m _ h₁ h₂ h₃
  have hψe : ∀ a, (ψ₀.comp e.toRingEquiv.symm.toRingHom) (e a) = ψ₀ a := fun a => by simp
  -- `τ` kills the image of `𝔪_x`
  have hf : ∀ r ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (X.normalization hX y)),
      (τ.comp (algebraMap _ _)) (((X.normalization hX).stalkMap y).hom r) = 0 := by
    intro r hr
    rw [RingHom.comp_apply]
    erw [← hψ₀alg r]
    rw [← hψe]
    obtain ⟨f, hf⟩ := Ideal.Quotient.mk_surjective (e (algebraMap _ _ r))
    have hfm : f ∈ IsLocalRing.maximalIdeal _ := by
      by_contra hfn
      have hu := IsLocalRing.notMem_maximalIdeal.mp hfn
      have h2 : IsUnit (algebraMap (X.presheaf.stalk (X.normalization hX y))
          (CompletedLocalRing X (X.normalization hX y)) r) := by
        have := (hu.map (Ideal.Quotient.mk _)).map e.symm
        rwa [hf, AlgEquiv.symm_apply_apply] at this
      have h3 := map_nonunit (algebraMap (X.presheaf.stalk (X.normalization hX y))
          (CompletedLocalRing X (X.normalization hX y))) r hr
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h3
      exact h3 h2
    rw [← hf]
    exact hτm f hfm
  -- `τ` kills the kernel of `π`
  have hKτ : ∀ s, π s = 0 → (τ.comp (algebraMap _ _)) s = 0 := by
    intro s hs
    obtain ⟨p, hpdef⟩ : ∃ p, p = P.comap (algebraMap ((X.normalizationScheme hX).presheaf.stalk y)
        (AdicCompletion (IsLocalRing.maximalIdeal ((X.normalizationScheme hX).presheaf.stalk y))
          ((X.normalizationScheme hX).presheaf.stalk y))) := ⟨_, rfl⟩
    have hpr : p.IsPrime := hpdef ▸ Ideal.IsPrime.comap _
    have hmem : s ∈ p := hK p ?_ (RingHom.mem_ker.mpr hs)
    · rw [hpdef] at hmem
      exact hPτ hmem
    have hpt := congrArg (fun g => g (⟨p, hpr⟩ : PrimeSpectrum _))
      (Scheme.SpecMap_stalkMap_fromSpecStalk (f := X.normalization hX) (x := y))
    intro hsm
    have h1 : X.fromSpecStalk (X.normalization hX y)
        (⟨p.comap ((X.normalization hX).stalkMap y).hom, Ideal.IsPrime.comap _⟩ :
          PrimeSpectrum _) ∈ MMP.Mori.smoothLocus sX := by
      convert hsm using 1
      exact hpt
    rw [hsing, isRegularLocalRing_stalk_fromSpecStalk_iff] at h1
    have hQ : (P.comap ψ₀).comap (algebraMap _ (CompletedLocalRing X (X.normalization hX y))) =
        p.comap ((X.normalization hX).stalkMap y).hom := by
      rw [hpdef, Ideal.comap_comap, Ideal.comap_comap]
      congr 1
      exact RingHom.ext hψ₀alg
    have hQ' : (P.comap (ψ₀.comp e.toRingEquiv.symm.toRingHom)).comap e.toRingEquiv =
        P.comap ψ₀ := by
      ext a
      simp only [Ideal.mem_comap]
      erw [hψe]
    have : (P.comap ψ₀).IsPrime := Ideal.IsPrime.comap _
    have : (P.comap (ψ₀.comp e.toRingEquiv.symm.toRingHom)).IsPrime := Ideal.IsPrime.comap _
    rw [← isRegularLocalRing_localization_congr hQ,
      ← SingLoc.isRegularLocalRing_localization_adicCompletion_iff hG,
      ← isRegularLocalRing_localization_congr hQ',
      SingLoc.isRegularLocalRing_localization_comap_iff] at h1
    exact (SingLoc.Pub.isRegularLocalRing_localization_pinch_iff (m := m) _).mp h1 ⟨hP0, hP2⟩
  have hle : (IsLocalRing.maximalIdeal ((X.normalizationScheme hX).presheaf.stalk y)).map
      (algebraMap _ (AdicCompletion (IsLocalRing.maximalIdeal
        ((X.normalizationScheme hX).presheaf.stalk y))
        ((X.normalizationScheme hX).presheaf.stalk y))) ≤ RingHom.ker τ :=
    Ideal.map_le_iff_le_comap.mpr fun _ hs => eq_zero_of_map_maximalIdeal _ π hπ hm _ hKτ hf hs
  rw [AdicCompletion.maximalIdeal_eq_map] at hl
  exact hl' (hle hl)

open Stacks.AlgebraicGeometry.Normalization in
/-- **Over a pinch point `D_ν → D_X` is ramified**, for any `D_X` through the pinch point and
`D_ν` with underlying set the preimage of the singular locus. -/
private theorem not_etale_restrict_of_isPinchPoint [LocallyOfFiniteType sX] [IsReduced X] {n : ℕ}
    (hpts : ∀ x : X, IsClosed ({x} : Set X) →
      x ∈ MMP.Mori.smoothLocus sX ∨ IsDoubleNormalCrossingPoint sX n x ∨ IsPinchPoint sX n x)
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (D : X.IdealSheafData) (E : (normalizationScheme X hX).IdealSheafData)
    (hE : ∀ w, w ∈ Set.range E.subschemeι ↔ normalization X hX w ∉ MMP.Mori.smoothLocus sX)
    (φ : E.subscheme ⟶ D.subscheme) (hφ : φ ≫ D.subschemeι = E.subschemeι ≫ normalization X hX)
    (z : D.subscheme) (hz : D.subschemeι z ∉ MMP.Mori.smoothLocus sX)
    (hp : IsPinchPoint sX n (D.subschemeι z))
    (U : D.subscheme.Opens) (hzU : z ∈ U) : ¬ Etale (φ ∣_ U) := by
  intro hU
  have hsing := mem_smoothLocus_iff_isRegularLocalRing hpts
  have : IsFinite (normalization X hX) := Scheme.isFinite_normalization
    (isNagataScheme_of_locallyOfFiniteType_over_field k sX) hX
  -- a point `y` of `D_ν` over `z`
  obtain ⟨y', hy'⟩ := (Scheme.surjective_normalization X hX).surj (D.subschemeι z)
  obtain ⟨y, rfl⟩ := (hE y').mpr (by
    rw [show normalization X hX y' = D.subschemeι z from hy']
    exact hz)
  have hyz : φ y = z := D.subschemeι.isEmbedding.injective (by
    rw [← Scheme.Hom.comp_apply, hφ, Scheme.Hom.comp_apply]; exact hy')
  subst hyz
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by have := hp.1; omega⟩
  have hmod : HasCompletedLocalModel sX (normalization X hX (E.subschemeι y))
      (MvPowerSeries.X 0 ^ 2 - MvPowerSeries.X 1 * MvPowerSeries.X 2 ^ 2 :
        MvPowerSeries (Fin (m + 3)) k) := by
    rw [show normalization X hX (E.subschemeι y) = D.subschemeι (φ y) from hy']
    exact hp.2.2.2
  -- `φ` is unramified at `y`
  have : FormallyUnramified (φ ∣_ U) := inferInstance
  have hfu : (φ.stalkMap y).hom.FormallyUnramified :=
    (RingHom.FormallyUnramified.respectsIso.arrow_mk_iso_iff
      (morphismRestrictStalkMap φ U ⟨y, hzU⟩)).mp (FormallyUnramified.stalkMap _ _)
  have : LocallyOfFiniteType (φ ≫ D.subschemeι) := by rw [hφ]; infer_instance
  have : LocallyOfFiniteType φ := LocallyOfFiniteType.of_comp (f := φ) (g := D.subschemeι) this
  have hm := map_maximalIdeal_eq_of_formallyUnramified φ E.subschemeι D.subschemeι
    (normalization X hX) hφ y hfu
  exact false_of_pinch_model (sX := sX) hX hsing (E.subschemeι y) hmod
    (E.subschemeι.stalkMap y).hom (E.subschemeι.stalkMap_surjective y)
    (fun p hp' hp => (@ker_stalkMap_le_iff_mem_range _ _ E.subschemeι _ y p hp').mpr
      ((hE _).mpr hp)) hm

/-- If the completed local ring of a reduced scheme of finite type over `k` at `x` has the model
`x₀x₁` in `n + 1` variables, then `n = m + 1` for some `m`. -/
private theorem exists_eq_add_one_of_dnc [IsReduced X] [LocallyOfFiniteType sX]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    {x : X} {n : ℕ}
    (hmod : HasCompletedLocalModel sX x
      (MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin (n + 1)) k)) :
    ∃ m, n = m + 1 := by
  rcases n with _ | m
  · exfalso
    have hred := (MMP.Resolution.isReduced_adicCompletion_stalk_and_normalization_completion
      X sX hX x).1
    let := (stalkStructureMap sX x).toAlgebra
    obtain ⟨e⟩ := hmod
    have h10 : (1 : Fin 1) = 0 := Subsingleton.elim _ _
    have hsq : (MvPowerSeries.X 0 * MvPowerSeries.X 0 : MvPowerSeries (Fin (0 + 1)) k) =
        MvPowerSeries.X 0 * MvPowerSeries.X 1 := by rw [h10]
    set u := e.symm (Ideal.Quotient.mk _ (MvPowerSeries.X 0))
    have hu : u ^ 2 = 0 := by
      rw [← map_pow, ← map_pow, pow_two, hsq,
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _), map_zero]
    have hu0 : u = 0 := IsReduced.eq_zero u ⟨2, hu⟩
    have hmk : Ideal.Quotient.mk (Ideal.span {(MvPowerSeries.X 0 * MvPowerSeries.X 1 :
        MvPowerSeries (Fin (0 + 1)) k)}) (MvPowerSeries.X 0) = 0 := by
      have := congrArg e hu0
      rwa [AlgEquiv.apply_symm_apply, map_zero] at this
    have hdvd := (Ideal.Quotient.eq_zero_iff_dvd _ _).mp hmk
    rw [← hsq, ← pow_two, MvPowerSeries.X_pow_dvd_iff] at hdvd
    have := hdvd (Finsupp.single 0 1) (by simp)
    simp [MvPowerSeries.coeff_X] at this
  · exact ⟨m, rfl⟩

/-- **Over a double normal crossing point `D_ν → D_X` is flat and unramified** at every point
`y` of `D_ν` over `z`. -/
private theorem flat_and_formallyUnramified_stalkMap_of_dnc [LocallyOfFiniteType sX] [IsReduced X]
    {n : ℕ}
    (hpts : ∀ x : X, IsClosed ({x} : Set X) →
      x ∈ MMP.Mori.smoothLocus sX ∨ IsDoubleNormalCrossingPoint sX n x ∨ IsPinchPoint sX n x)
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (D : X.IdealSheafData) (E : (X.normalizationScheme hX).IdealSheafData)
    [IsReduced D.subscheme]
    (hD : ∀ w, w ∈ Set.range D.subschemeι ↔ w ∉ MMP.Mori.smoothLocus sX)
    (hE : ∀ w, w ∈ Set.range E.subschemeι ↔ X.normalization hX w ∉ MMP.Mori.smoothLocus sX)
    (φ : E.subscheme ⟶ D.subscheme) (hφ : φ ≫ D.subschemeι = E.subschemeι ≫ X.normalization hX)
    (y : E.subscheme) (hdnc : IsDoubleNormalCrossingPoint sX n (D.subschemeι (φ y))) :
    (φ.stalkMap y).hom.Flat ∧ (φ.stalkMap y).hom.FormallyUnramified := by
  have hsing := mem_smoothLocus_iff_isRegularLocalRing hpts
  have : IsFinite (X.normalization hX) := Scheme.isFinite_normalization
    (isNagataScheme_of_locallyOfFiniteType_over_field k sX) hX
  have : LocallyOfFiniteType (φ ≫ D.subschemeι) := by rw [hφ]; infer_instance
  have : LocallyOfFiniteType φ := LocallyOfFiniteType.of_comp (f := φ) (g := D.subschemeι) this
  have hexc : ∀ {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] (t : Y),
      IsExcellent (Y.presheaf.stalk t) := fun sY _ t => SingLoc.isExcellent_stalk' (sX := sY) t
  have hpt : X.normalization hX (E.subschemeι y) = D.subschemeι (φ y) := by
    rw [← Scheme.Hom.comp_apply, ← hφ, Scheme.Hom.comp_apply]
  -- the rings of the square
  set w := E.subschemeι y
  set z := φ y
  have : IsNoetherianRing (X.presheaf.stalk (X.normalization hX w)) := (hexc sX _).1.1
  have hG : IsGRing (X.presheaf.stalk (X.normalization hX w)) := (hexc sX _).1.2.1
  have : IsNoetherianRing ((X.normalizationScheme hX).presheaf.stalk w) :=
    (hexc (X.normalization hX ≫ sX) w).1.1
  have : IsNoetherianRing (D.subscheme.presheaf.stalk z) := (hexc (D.subschemeι ≫ sX) z).1.1
  have : IsNoetherianRing (E.subscheme.presheaf.stalk y) :=
    (hexc (E.subschemeι ≫ X.normalization hX ≫ sX) y).1.1
  have : IsReduced (D.subscheme.presheaf.stalk z) := isReduced_stalk_of_isReduced _ z
  have h5 : (φ.stalkMap y).hom.comp (D.subschemeι.stalkMap z).hom =
      (((E.subschemeι.stalkMap y).hom).comp ((X.normalization hX).stalkMap w).hom).comp
      (X.presheaf.stalkCongr (.of_eq hpt.symm)).hom.hom := by
    have h2 := Scheme.Hom.stalkMap_comp φ D.subschemeι y
    have h3 := Scheme.Hom.stalkMap_congr_hom (φ ≫ D.subschemeι)
      (E.subschemeι ≫ X.normalization hX) hφ y
    have h4 := Scheme.Hom.stalkMap_comp E.subschemeι (X.normalization hX) y
    rw [h2, h4] at h3
    rw [← CommRingCat.hom_comp, h3]
    rfl
  set g := ((X.normalization hX).stalkMap w).hom
  set πB := (E.subschemeι.stalkMap y).hom
  set f := (φ.stalkMap y).hom
  set c := (X.presheaf.stalkCongr (.of_eq hpt.symm)).commRingCatIsoToRingEquiv
  set πA := (D.subschemeι.stalkMap z).hom.comp c.symm.toRingHom
  have hsq : f.comp πA = πB.comp g := by
    refine RingHom.ext fun r => ?_
    have := RingHom.congr_fun h5 (c.symm r)
    simp only [RingHom.comp_apply] at this ⊢
    change f ((D.subschemeι.stalkMap z).hom (c.symm r)) = _
    rw [this]
    congr 2
    exact c.apply_symm_apply r
  have hπA : Function.Surjective πA :=
    (D.subschemeι.stalkMap_surjective z).comp c.symm.surjective
  have hπB : Function.Surjective πB := E.subschemeι.stalkMap_surjective y
  -- the kernel of `πA` cuts out the non-regular locus
  have hD' : ∀ t : X, t ∈ (D.support : Set X) ↔ t ∉ MMP.Mori.smoothLocus sX := fun t => by
    rw [← D.range_subschemeι]; exact hD t
  have hI : ∀ (p : Ideal (X.presheaf.stalk (X.normalization hX w))) [p.IsPrime],
      RingHom.ker πA ≤ p ↔ ¬ IsRegularLocalRing (Localization.AtPrime p) := by
    intro p _
    have hk : RingHom.ker πA = (RingHom.ker (D.subschemeι.stalkMap z).hom).map c := by
      rw [← Ideal.comap_symm]
      ext r
      rw [Ideal.mem_comap, RingHom.mem_ker, RingHom.mem_ker]
      rfl
    rw [hk, Ideal.map_le_iff_le_comap, SingLoc.ker_le_iff_not_isRegularLocalRing hsing D hD' z,
      SingLoc.isRegularLocalRing_localization_comap_iff c p]
  -- the kernel of `πB` lies in every prime over the non-regular locus
  have hJ : ∀ (q : Ideal ((X.normalizationScheme hX).presheaf.stalk w)) [q.IsPrime],
      ¬ IsRegularLocalRing (Localization.AtPrime (q.comap g)) → RingHom.ker πB ≤ q := by
    intro q hq hreg
    refine (ker_stalkMap_le_iff_mem_range E.subschemeι y q).mpr
      ((hE _).mpr fun hsm => hreg ?_)
    have hpt' := congrArg (fun t => t (⟨q, hq⟩ : PrimeSpectrum _))
      (Scheme.SpecMap_stalkMap_fromSpecStalk (f := X.normalization hX) (x := w))
    have h1 : X.fromSpecStalk (X.normalization hX w)
        (⟨q.comap g, Ideal.IsPrime.comap _⟩ : PrimeSpectrum _) ∈ MMP.Mori.smoothLocus sX := by
      convert hsm using 1
      exact hpt'
    rwa [hsing, isRegularLocalRing_stalk_fromSpecStalk_iff] at h1
  -- the model
  rw [← hpt] at hdnc
  obtain ⟨m, rfl⟩ := exists_eq_add_one_of_dnc (sX := sX) hX hdnc.2.2
  obtain ⟨hND, ψ₀, hint, hbir, hnz, hψ₀alg⟩ :=
    exists_completion_factor_normalization (sX := sX) hX w
  have hψ₀ : ψ₀ = adicCompletionMap g _ _ (IsLocalRing.map_maximalIdeal_le g) :=
    eq_adicCompletionMap_of_apply_algebraMap g _ _ _
      (IsLocalRing.maximalIdeal _).fg_of_isNoetherianRing ψ₀ hψ₀alg
  let := (stalkStructureMap sX (X.normalization hX w)).toAlgebra
  obtain ⟨e⟩ := hdnc.2.2
  set e' := e.toRingEquiv
  obtain ⟨h₁, h₂, h₃⟩ := props_comp_symm_of_ringEquiv ψ₀ e' hint hbir hnz
  have hloc := AdicCompletion.isLocalRing_of_fg
    (IsNoetherian.noetherian
      (IsLocalRing.maximalIdeal ((X.normalizationScheme hX).presheaf.stalk w)))
  obtain ⟨hsurj, Q, hQ, hQc⟩ := @surjective_and_comap_of_dnc k _ m _ _ hloc hND.isDomain
    hND.isIntegrallyClosed _ h₁ h₂ h₃
  have hψe : ∀ a, (ψ₀.comp e'.symm.toRingHom) (e' a) = ψ₀ a := fun a => by simp
  set Q₀' : Ideal (MvPowerSeries (Fin (m + 1 + 1)) k ⧸ Ideal.span {SingLoc.Pub.dncEq k m}) :=
    (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin (m + 1 + 1)) k),
      MvPowerSeries.X 1}).map (Ideal.Quotient.mk _)
  set Q₀ := Q₀'.comap e'
  have hQ₀c : Q.comap ψ₀ = Q₀ := by
    ext a
    change ψ₀ a ∈ Q ↔ e' a ∈ Q₀'
    rw [← hQc, Ideal.mem_comap, hψe]
  have : Q₀.IsPrime := hQ₀c ▸ Ideal.IsPrime.comap _
  have hQ₀ : ∀ (P : Ideal (AdicCompletion (IsLocalRing.maximalIdeal
      (X.presheaf.stalk (X.normalization hX w))) (X.presheaf.stalk (X.normalization hX w))))
      [P.IsPrime], IsRegularLocalRing (Localization.AtPrime P) ↔ ¬ Q₀ ≤ P := by
    intro P _
    obtain ⟨q, hq, rfl⟩ : ∃ q : Ideal (MvPowerSeries (Fin (m + 1 + 1)) k ⧸
        Ideal.span {SingLoc.Pub.dncEq k m}), q.IsPrime ∧ q.comap e' = P :=
      ⟨P.map e', Ideal.map_isPrime_of_equiv _, Ideal.comap_map_of_bijective _ e'.bijective⟩
    rw [SingLoc.isRegularLocalRing_localization_comap_iff e' q,
      SingLoc.Pub.isRegularLocalRing_localization_dnc_iff q,
      Ideal.comap_le_comap_iff_of_surjective _ e'.surjective, SingLoc.map_span_pair_le_iff]
  set I := RingHom.ker πA
  have eA : X.presheaf.stalk (X.normalization hX w) ⧸ I ≃+* D.subscheme.presheaf.stalk z :=
    RingHom.quotientKerEquivOfSurjective hπA
  have : Nontrivial (X.presheaf.stalk (X.normalization hX w) ⧸ I) := eA.toEquiv.nontrivial
  have : IsLocalRing (X.presheaf.stalk (X.normalization hX w) ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have : IsReduced (X.presheaf.stalk (X.normalization hX w) ⧸ I) :=
    isReduced_of_injective eA.toRingHom eA.injective
  have hIQ := SingLoc.map_eq_of_regularLocus hG I hI Q₀ hQ₀
  -- the completed square
  have hbij := bijective_adicCompletionMap_of_comm_sq πA hπA πB hπB g f hsq
    (by
      rw [← hψ₀]
      intro l
      obtain ⟨r, hr⟩ := hsurj l
      exact ⟨e'.symm r, hr⟩)
    (by
      rw [← hψ₀]
      intro r hr
      rw [hIQ, ← hQ₀c, Ideal.mem_comap]
      refine (Ideal.map_le_iff_le_comap.mpr ?_) hr
      refine hJ _ fun hreg => ?_
      have hcq : (Q.comap (algebraMap _ (AdicCompletion (IsLocalRing.maximalIdeal
          ((X.normalizationScheme hX).presheaf.stalk w))
          ((X.normalizationScheme hX).presheaf.stalk w)))).comap g =
          Q₀.comap (algebraMap _ (AdicCompletion (IsLocalRing.maximalIdeal
            (X.presheaf.stalk (X.normalization hX w)))
            (X.presheaf.stalk (X.normalization hX w)))) := by
        rw [← hQ₀c, Ideal.comap_comap, Ideal.comap_comap]
        congr 1
        exact RingHom.ext fun a => (hψ₀alg a).symm
      rw [isRegularLocalRing_localization_congr hcq,
        ← SingLoc.isRegularLocalRing_localization_adicCompletion_iff hG, hQ₀] at hreg
      exact hreg le_rfl)
  obtain ⟨hfl, hfu, -⟩ := RingHom.isEtaleLocalHom_of_bijective_adicCompletionMap f
    (LocallyOfFiniteType.stalkMap φ y) hbij
  exact ⟨hfl, hfu⟩

open Stacks.AlgebraicGeometry.Normalization in
/-- **Over a double normal crossing point `D_ν → D_X` is étale on a neighbourhood** of `z`. -/
private theorem exists_etale_restrict_of_isDoubleNormalCrossingPoint [LocallyOfFiniteType sX]
    [IsReduced X] {n : ℕ}
    (hpts : ∀ x : X, IsClosed ({x} : Set X) →
      x ∈ MMP.Mori.smoothLocus sX ∨ IsDoubleNormalCrossingPoint sX n x ∨ IsPinchPoint sX n x)
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (D : X.IdealSheafData) (E : (normalizationScheme X hX).IdealSheafData)
    (hD : ∀ w, w ∈ Set.range D.subschemeι ↔ w ∉ MMP.Mori.smoothLocus sX)
    (hE : ∀ w, w ∈ Set.range E.subschemeι ↔ normalization X hX w ∉ MMP.Mori.smoothLocus sX)
    (φ : E.subscheme ⟶ D.subscheme) (hφ : φ ≫ D.subschemeι = E.subschemeι ≫ normalization X hX)
    [IsReduced D.subscheme]
    (z : D.subscheme) (hdnc : IsDoubleNormalCrossingPoint sX n (D.subschemeι z)) :
    ∃ U : D.subscheme.Opens, z ∈ U ∧ Etale (φ ∣_ U) := by
  have : IsFinite (normalization X hX) := Scheme.isFinite_normalization
    (isNagataScheme_of_locallyOfFiniteType_over_field k sX) hX
  have : IsFinite (φ ≫ D.subschemeι) := by rw [hφ]; infer_instance
  have : IsFinite φ := IsFinite.of_comp φ D.subschemeι
  have : IsLocallyNoetherian D.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (D.subschemeι ≫ sX)
  -- the étale locus of `φ`
  set W : Set E.subscheme := {y | EtaleAt φ y}
  have hWo : IsOpen W := by
    rw [isOpen_iff_forall_mem_open]
    rintro y ⟨U, hU, hyU, V, hV, e, h⟩
    exact ⟨U, fun y' hy' => ⟨U, hU, hy', V, hV, e, h⟩, U.2, hyU⟩
  have hfib : ∀ y, φ y = z → y ∈ W := by
    rintro y rfl
    obtain ⟨h1, h2⟩ := flat_and_formallyUnramified_stalkMap_of_dnc hpts hX D E hD hE φ hφ y hdnc
    exact (isEtaleAt_iff_etaleAt φ y).mp ⟨h1, h2, LocallyOfFiniteType.stalkMap φ y⟩
  have hcl : IsClosed (φ '' Wᶜ) := φ.isClosedMap _ hWo.isClosed_compl
  refine ⟨⟨(φ '' Wᶜ)ᶜ, hcl.isOpen_compl⟩, fun ⟨w, hw, hwz⟩ => hw (hfib w hwz), ?_⟩
  rw [etale_iff_forall_etaleAt]
  intro x
  have hxW : x.1 ∈ W := by
    by_contra hx
    exact x.2 ⟨x.1, hx, rfl⟩
  have hx : IsEtaleAt φ x.1 := (isEtaleAt_iff_etaleAt φ x.1).mpr hxW
  obtain ⟨h1, h2, h3⟩ := hx
  refine (isEtaleAt_iff_etaleAt _ x).mp ⟨?_, ?_, ?_⟩
  · exact (RingHom.Flat.respectsIso.arrow_mk_iso_iff (morphismRestrictStalkMap φ _ x)).mpr h1
  · exact (RingHom.FormallyUnramified.respectsIso.arrow_mk_iso_iff
      (morphismRestrictStalkMap φ _ x)).mpr h2
  · exact (RingHom.EssFiniteType.respectsIso.arrow_mk_iso_iff
      (morphismRestrictStalkMap φ _ x)).mpr h3

/-- Over a double normal crossing point the restriction of the normalization to the double
locus is étale on a neighbourhood. -/
public theorem exists_etale_of_isDoubleNormalCrossingPoint {n : ℕ} (h : IsSemismooth sX n)
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (φ : (Scheme.IdealSheafData.vanishingIdeal
        ((MMP.Mori.singularLocus sX).preimage
          (Stacks.AlgebraicGeometry.Normalization.normalization X hX).continuous)).subscheme ⟶
      (MMP.Resolution.reducedSingularLocus sX).subscheme)
    (hφ : φ ≫ (MMP.Resolution.reducedSingularLocus sX).subschemeι =
      (Scheme.IdealSheafData.vanishingIdeal
        ((MMP.Mori.singularLocus sX).preimage
          (Stacks.AlgebraicGeometry.Normalization.normalization X hX).continuous)).subschemeι ≫
        Stacks.AlgebraicGeometry.Normalization.normalization X hX)
    (z : (MMP.Resolution.reducedSingularLocus sX).subscheme)
    (hdnc : IsDoubleNormalCrossingPoint sX n
      ((MMP.Resolution.reducedSingularLocus sX).subschemeι z)) :
    ∃ U : (MMP.Resolution.reducedSingularLocus sX).subscheme.Opens, z ∈ U ∧ Etale (φ ∣_ U) := by
  obtain ⟨⟨⟨-, hlft, -⟩, hred, -⟩, hpts⟩ := h
  have : LocallyOfFiniteType sX := hlft
  have : IsReduced (MMP.Resolution.reducedSingularLocus sX).subscheme := by
    change IsReduced (Scheme.IdealSheafData.vanishingIdeal _).subscheme
    infer_instance
  refine exists_etale_restrict_of_isDoubleNormalCrossingPoint hpts hX _ _ (fun w => ?_)
    (fun w => ?_) φ hφ z hdnc
  · rw [Scheme.IdealSheafData.range_subschemeι, MMP.Resolution.support_reducedSingularLocus]
    rfl
  · rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl

/-- Over a pinch point the restriction of the normalization to the double locus is not étale
on any neighbourhood. -/
public theorem not_etale_of_isPinchPoint {n : ℕ} (h : IsSemismooth sX n)
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (φ : (Scheme.IdealSheafData.vanishingIdeal
        ((MMP.Mori.singularLocus sX).preimage
          (Stacks.AlgebraicGeometry.Normalization.normalization X hX).continuous)).subscheme ⟶
      (MMP.Resolution.reducedSingularLocus sX).subscheme)
    (hφ : φ ≫ (MMP.Resolution.reducedSingularLocus sX).subschemeι =
      (Scheme.IdealSheafData.vanishingIdeal
        ((MMP.Mori.singularLocus sX).preimage
          (Stacks.AlgebraicGeometry.Normalization.normalization X hX).continuous)).subschemeι ≫
        Stacks.AlgebraicGeometry.Normalization.normalization X hX)
    (z : (MMP.Resolution.reducedSingularLocus sX).subscheme)
    (hp : IsPinchPoint sX n ((MMP.Resolution.reducedSingularLocus sX).subschemeι z))
    (U : (MMP.Resolution.reducedSingularLocus sX).subscheme.Opens) (hzU : z ∈ U) :
    ¬ Etale (φ ∣_ U) := by
  obtain ⟨⟨⟨-, hlft, -⟩, hred, -⟩, hpts⟩ := h
  have : LocallyOfFiniteType sX := hlft
  refine not_etale_restrict_of_isPinchPoint hpts hX _ _ (fun w => ?_) φ hφ z
    (subschemeι_notMem_smoothLocus z) hp U hzU
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl

end MMP.Flips.BranchLocus
