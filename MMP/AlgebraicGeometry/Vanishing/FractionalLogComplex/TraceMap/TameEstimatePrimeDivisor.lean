module

public import MMP.RingTheory.Kaehler.FormsTraceHeightOne
public import MMP.RingTheory.Ideal.HeightOfLiesOver
public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Basic

/-!
# The tame trace estimate at a prime divisor, for a finite cover

Let `f : Y ⟶ X` be a finite surjective morphism of integral schemes over a field `k`, with `X`
normal and locally Noetherian, `K ⊆ L` their function fields, `E` a prime divisor of `X` with
uniformizer `t` of `𝒪_{X,E}`, and `b` a basis of `Ω_{K/k}`. If a `p`-form `ω` of `L` is such that,
at every point `y` of `Y` over the generic point of `E`, `t` times each coordinate of `ω` in the
wedges of the pulled-back basis comes from the maximal ideal of `𝒪_{Y,y}`, then every coordinate
of `Tr_{L/K} ω` in the wedges of `b` lies in `𝒪_{X,E}`.

On an affine open `W` of `X` containing the generic point of `E` this is
`MMP.FourfoldProofs.FractionalLogComplexProof.exists_mul_formsTrace_repr_eq_of_forall_isPrime` for
`Γ(X, W) ⊆ Γ(Y, f⁻¹ W)` and the prime of `E`: the primes of `Γ(Y, f⁻¹ W)` over it are the points
of `Y` over the generic point of `E`, with local rings the localizations.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.formsTrace_repr_mem_range_localRing`: the estimate.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite IsLocalRing

namespace MMP.FourfoldProofs.FractionalLogComplexProof

open _root_.Topology

universe u

/-- **The tame trace estimate at a prime divisor, for a finite cover.** If, at every point of `Y`
over the generic point of `E`, `t` times each coordinate of `ω` in the wedges of
`pullbackBasis b` comes from the maximal ideal of the stalk, then every coordinate of
`formsTrace k K L p ω` in the wedges of `b` lies in the image of `𝒪_{X,E}`. -/
theorem formsTrace_repr_mem_range_localRing {k : Type u} [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (f : Y ⟶ X) [IsIntegral X] [IsIntegral Y] [IsFinite f]
    [Surjective f] [IsLocallyNoetherian X] [IsNormal X]
    (hfd : letI := MMP.Mori.functionFieldMapAlgebra f
      FiniteDimensional X.functionField Y.functionField)
    (hsep : letI := MMP.Mori.functionFieldMapAlgebra f
      Algebra.IsSeparable X.functionField Y.functionField)
    (E : MMP.Mori.PrimeDivisor X) (W : X.affineOpens) (hEW : E.genericPoint ∈ (W : X.Opens))
    (t : Γ(X, W)) (ht : maximalIdeal E.localRing =
      Ideal.span {X.presheaf.germ (W : X.Opens) E.genericPoint hEW t})
    {ι : Type*} [LinearOrder ι] [Finite ι]
    (b : letI := MMP.Mori.functionFieldAlgebra sX
      Module.Basis ι X.functionField Ω[X.functionField⁄k]) (p : ℕ)
    (ω : letI := MMP.Mori.functionFieldAlgebra (f ≫ sX)
      ⋀[Y.functionField]^p Ω[Y.functionField⁄k])
    (hω : letI := MMP.Mori.functionFieldAlgebra sX
      letI := MMP.Mori.functionFieldAlgebra (f ≫ sX)
      letI := MMP.Mori.functionFieldMapAlgebra f
      haveI := MMP.Mori.isScalarTower_functionFieldMap sX f
      haveI : Nonempty (W : X.Opens) := ⟨⟨_, hEW⟩⟩
      ∀ y : Y, f y = E.genericPoint → ∀ S, ∃ r ∈ maximalIdeal (Y.presheaf.stalk y),
        algebraMap (Y.presheaf.stalk y) Y.functionField r =
          AlgebraicGeometry.functionFieldMap f (X.germToFunctionField (W : X.Opens) t) *
            ((pullbackBasis (L := Y.functionField) b).exteriorPower p).repr ω S)
    (S : Set.powersetCard ι p) :
    letI := MMP.Mori.functionFieldAlgebra sX
    letI := MMP.Mori.functionFieldAlgebra (f ≫ sX)
    letI := MMP.Mori.functionFieldMapAlgebra f
    haveI := MMP.Mori.isScalarTower_functionFieldMap sX f
    haveI := hfd
    haveI := hsep
    (b.exteriorPower p).repr (formsTrace k X.functionField Y.functionField p ω) S ∈
      (algebraMap E.localRing X.functionField).range := by
  let := MMP.Mori.functionFieldAlgebra sX
  let := MMP.Mori.functionFieldAlgebra (f ≫ sX)
  let := MMP.Mori.functionFieldMapAlgebra f
  have := MMP.Mori.isScalarTower_functionFieldMap sX f
  have := hfd
  have := hsep
  have : Nonempty (W : X.Opens) := ⟨⟨_, hEW⟩⟩
  have hV : IsAffineOpen (f ⁻¹ᵁ (W : X.Opens)) := W.2.preimage f
  obtain ⟨y₀, hy₀⟩ := f.surjective E.genericPoint
  have : Nonempty (f ⁻¹ᵁ (W : X.Opens)) := ⟨⟨y₀, show f y₀ ∈ (W : X.Opens) from hy₀ ▸ hEW⟩⟩
  have : IsDomain Γ(X, W) := IsIntegral.component_integral _
  have : IsDomain Γ(Y, f ⁻¹ᵁ (W : X.Opens)) := IsIntegral.component_integral _
  let : Algebra Γ(X, W) Γ(Y, f ⁻¹ᵁ (W : X.Opens)) := (f.app W).hom.toAlgebra
  have : Module.Finite Γ(X, W) Γ(Y, f ⁻¹ᵁ (W : X.Opens)) := f.finite_app W W.2
  have hcompat : ∀ a : Γ(X, W), AlgebraicGeometry.functionFieldMap f
      (X.germToFunctionField (W : X.Opens) a) =
      Y.germToFunctionField (f ⁻¹ᵁ (W : X.Opens)) (f.app W a) := fun a => by
    rw [Scheme.Hom.app_eq_appLE]
    simp only [AlgebraicGeometry.functionFieldMap, Scheme.germToFunctionField,
      TopCat.Presheaf.stalkCongr_hom, Scheme.Hom.appLE, ← ConcreteCategory.comp_apply,
      Category.assoc, TopCat.Presheaf.germ_res,
      TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.Hom.germ_stalkMap]
    erw [TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.Hom.germ_stalkMap]
  let : Algebra Γ(X, W) Y.functionField :=
    ((AlgebraicGeometry.functionFieldMap f).comp
      (X.germToFunctionField (W : X.Opens)).hom).toAlgebra
  have : IsScalarTower Γ(X, W) X.functionField Y.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower Γ(X, W) Γ(Y, f ⁻¹ᵁ (W : X.Opens)) Y.functionField :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext hcompat)
  have : IsFractionRing Γ(X, W) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X (W : X.Opens) W.2
  have : IsFractionRing Γ(Y, f ⁻¹ᵁ (W : X.Opens)) Y.functionField :=
    functionField_isFractionRing_of_isAffineOpen Y _ hV
  -- the prime of `E`
  let xE : (W : X.Opens) := ⟨E.genericPoint, hEW⟩
  let 𝔭 := (W.2.primeIdealOf xE).asIdeal
  let : Algebra Γ(X, W) E.localRing := TopCat.Presheaf.algebra_section_stalk X.presheaf xE
  have : IsScalarTower Γ(X, W) E.localRing X.functionField :=
    IsScalarTower.of_algebraMap_eq fun a =>
      (Scheme.algebraMap_germ_eq_germToFunctionField (X := X) hEW a).symm
  have hloc : IsLocalization.AtPrime E.localRing 𝔭 := W.2.isLocalization_stalk xE
  let e : Localization.AtPrime 𝔭 ≃ₐ[Γ(X, W)] E.localRing :=
    IsLocalization.algEquiv 𝔭.primeCompl _ _
  have := E.isDiscreteValuationRing_localRing
  have : IsDiscreteValuationRing (Localization.AtPrime 𝔭) :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e.symm.toRingEquiv
  have hm : maximalIdeal (Localization.AtPrime 𝔭) =
      Ideal.span {algebraMap Γ(X, W) (Localization.AtPrime 𝔭) t} := by
    rw [← IsLocalRing.map_ringEquiv_maximalIdeal e.symm.toRingEquiv, ht, Ideal.map_span,
      Set.image_singleton]
    congr 2
    exact e.symm.commutes t
  -- the points over the generic point of `E`
  have hx : ∀ Q : Ideal Γ(Y, f ⁻¹ᵁ (W : X.Opens)), Q.IsPrime →
      Q.comap (algebraMap Γ(X, W) Γ(Y, f ⁻¹ᵁ (W : X.Opens))) = 𝔭 → ∀ S, ∃ x ∈ Q, ∃ c ∉ Q,
        algebraMap Γ(Y, f ⁻¹ᵁ (W : X.Opens)) Y.functionField c *
          (algebraMap Γ(X, W) Y.functionField t *
            ((pullbackBasis (L := Y.functionField) b).exteriorPower p).repr ω S) =
        algebraMap Γ(Y, f ⁻¹ᵁ (W : X.Opens)) Y.functionField x := by
    intro Q hQ hQ𝔭 S
    let y := hV.fromSpec ⟨Q, hQ⟩
    have hy : y ∈ f ⁻¹ᵁ (W : X.Opens) := by
      change y ∈ ((f ⁻¹ᵁ (W : X.Opens) : Y.Opens) : Set Y)
      rw [← hV.range_fromSpec]
      exact ⟨_, rfl⟩
    have hfy : f y = E.genericPoint := by
      have hpt : Spec.map (f.appLE W (f ⁻¹ᵁ (W : X.Opens)) le_rfl) ⟨Q, hQ⟩ =
          W.2.primeIdealOf xE := by
        apply PrimeSpectrum.ext
        refine Eq.trans ?_ hQ𝔭
        rw [← Scheme.Hom.app_eq_appLE]
        rfl
      rw [show f y = W.2.fromSpec (Spec.map (f.appLE W (f ⁻¹ᵁ (W : X.Opens)) le_rfl) ⟨Q, hQ⟩)
        from (congrArg (fun g : Spec Γ(Y, f ⁻¹ᵁ (W : X.Opens)) ⟶ X => g ⟨Q, hQ⟩)
          (IsAffineOpen.SpecMap_appLE_fromSpec f W.2 hV le_rfl)).symm, hpt,
        W.2.fromSpec_primeIdealOf xE]
    obtain ⟨r, hr, hr'⟩ := hω y hfy S
    let : Algebra Γ(Y, f ⁻¹ᵁ (W : X.Opens)) (Y.presheaf.stalk y) :=
      TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨y, hy⟩
    have hlocy : IsLocalization.AtPrime (Y.presheaf.stalk y) Q :=
      hV.isLocalization_stalk' ⟨Q, hQ⟩ hy
    have : IsScalarTower Γ(Y, f ⁻¹ᵁ (W : X.Opens)) (Y.presheaf.stalk y) Y.functionField :=
      IsScalarTower.of_algebraMap_eq fun a =>
        (Scheme.algebraMap_germ_eq_germToFunctionField (X := Y) hy a).symm
    exact exists_mem_mul_eq_of_mem_maximalIdeal (R := Y.presheaf.stalk y) Q hr hr'
  obtain ⟨a, s, hs, has⟩ := exists_mul_formsTrace_repr_eq_of_forall_isPrime (k := k)
    (A₀ := Γ(X, W)) (B₀ := Γ(Y, f ⁻¹ᵁ (W : X.Opens))) (K := X.functionField)
    (L := Y.functionField) 𝔭 hm b p ω hx S
  -- `a / s` lies in `𝒪_{X,E}`
  refine ⟨IsLocalization.mk' E.localRing a (⟨s, hs⟩ : 𝔭.primeCompl), ?_⟩
  have hs0 : algebraMap Γ(X, W) X.functionField s ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective Γ(X, W) X.functionField)).mpr
      fun h0 => hs (h0 ▸ 𝔭.zero_mem)
  refine mul_left_cancel₀ hs0 ?_
  rw [has, mul_comm, IsScalarTower.algebraMap_apply Γ(X, W) E.localRing X.functionField s,
    IsScalarTower.algebraMap_apply Γ(X, W) E.localRing X.functionField a, ← map_mul,
    IsLocalization.mk'_spec]

end MMP.FourfoldProofs.FractionalLogComplexProof
