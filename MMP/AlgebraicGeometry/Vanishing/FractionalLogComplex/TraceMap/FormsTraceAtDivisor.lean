module

public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.TraceMap.TameEstimatePrimeDivisor
public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.TraceMap.TameEstimateInputs
public import MMP.AlgebraicGeometry.Morphisms.FiniteCodimOnePoints
public import MMP.AlgebraicGeometry.Morphisms.PointLocalHom
public import MMP.AlgebraicGeometry.FunctionField.FiniteCover

/-!
# The trace of forms at a prime divisor, from local lattices on the cover

Let `f : Y ⟶ X` be a finite surjective morphism of normal integral schemes over a field `k` of
characteristic zero, `E` a prime divisor of `X` with uniformizer `t` and adapted basis
`dt, dx₁, …, dxₘ` of `Ω_{𝒪_{X,E}/k}`, and `ω` a `p`-form of the function field of `Y`.

* If at every point `y` over the generic point of `E`, `t ω = ρ η` with `ρ ∈ 𝔪_y` and `η` in the
  wedges of the logarithmic forms `s⁻¹ ds, dy₁, …, dyₘ` of an adapted basis at `y`, then the trace
  of `ω` has its coordinates in the logarithmic adapted basis in `𝒪_{X,E}`.
* If at every such `y`, `ω = ρ η` with `ρ ∈ 𝒪_{Y,y}` and `η` in the wedges of the regular forms
  of an adapted basis at `y`, then the trace of `ω` has its coordinates in the regular adapted
  basis in `𝒪_{X,E}`.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.formsTrace_repr_logBasis_mem_range`: the logarithmic
  case.
* `MMP.FourfoldProofs.FractionalLogComplexProof.formsTrace_repr_regBasis_mem_range`: the regular case.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite IsLocalRing KaehlerDifferential

namespace MMP.FourfoldProofs.FractionalLogComplexProof

open _root_.Topology

universe u

variable {k : Type u} [Field k] [CharZero k] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  (f : Y ⟶ X) [IsIntegral X] [IsIntegral Y] [IsFinite f] [Surjective f]
  [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y]

/-- The image of a uniformizer of a discrete valuation ring in its fraction field is nonzero. -/
theorem algebraMap_ne_zero_of_maximalIdeal_eq_span {R K : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] {s : R}
    (h : maximalIdeal R = Ideal.span {s}) : algebraMap R K s ≠ 0 := by
  refine (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 ?_
  rintro rfl
  rw [Ideal.span_singleton_eq_bot.2 rfl] at h
  exact IsDiscreteValuationRing.not_a_field R h

/-- **The trace at a prime divisor, logarithmic case.** If at every point `y` over the generic
point of `E` one has `t • ω = ρ • η` with `ρ ∈ 𝔪_y` and `η` in the `p`-th wedge of the logarithmic
forms of an adapted basis at `y`, then the coordinates of `formsTrace ω` in the `p`-th exterior
power of `logBasis k bA htK` lie in `𝒪_{X,E}`. -/
theorem formsTrace_repr_logBasis_mem_range (E : MMP.Mori.PrimeDivisor X) (W : X.affineOpens)
    (hEW : E.genericPoint ∈ (W : X.Opens)) (t : Γ(X, W))
    (ht : maximalIdeal E.localRing =
      Ideal.span {X.presheaf.germ (W : X.Opens) E.genericPoint hEW t})
    {m : ℕ} (x : Fin m → E.localRing)
    (bA : letI := MMP.Mori.stalkAlgebra sX E.genericPoint
      Module.Basis (Fin (m + 1)) E.localRing Ω[E.localRing⁄k])
    (hbA : letI := MMP.Mori.stalkAlgebra sX E.genericPoint
      ∀ i, bA i = D k E.localRing ((Fin.cons (X.presheaf.germ (W : X.Opens) E.genericPoint hEW t)
        x : Fin (m + 1) → E.localRing) i))
    (htK : algebraMap E.localRing X.functionField
      (X.presheaf.germ (W : X.Opens) E.genericPoint hEW t) ≠ 0)
    (p : ℕ) (ω : letI := MMP.Mori.functionFieldAlgebra (f ≫ sX)
      ⋀[Y.functionField]^p Ω[Y.functionField⁄k])
    (hω : ∀ y : Y, f y = E.genericPoint →
      letI := MMP.Mori.stalkAlgebra (f ≫ sX) y
      letI := MMP.Mori.functionFieldAlgebra (f ≫ sX)
      haveI := MMP.Mori.isScalarTower_stalk_functionField (f ≫ sX) y
      haveI : Nonempty (W : X.Opens) := ⟨⟨_, hEW⟩⟩
      ∃ (s : Y.presheaf.stalk y) (_ : maximalIdeal (Y.presheaf.stalk y) = Ideal.span {s})
        (yv : Fin m → Y.presheaf.stalk y)
        (bR : Module.Basis (Fin (m + 1)) (Y.presheaf.stalk y) Ω[Y.presheaf.stalk y⁄k])
        (_ : ∀ i, bR i = D k (Y.presheaf.stalk y)
          ((Fin.cons s yv : Fin (m + 1) → Y.presheaf.stalk y) i))
        (ρ : Y.presheaf.stalk y) (_ : ρ ∈ maximalIdeal (Y.presheaf.stalk y))
        (η : ⋀[Y.functionField]^p Ω[Y.functionField⁄k])
        (_ : η ∈ wedgeSpan (Y.presheaf.stalk y) (Submodule.span (Y.presheaf.stalk y)
          (Set.range (Fin.cons
            ((algebraMap (Y.presheaf.stalk y) Y.functionField s)⁻¹ •
              D k Y.functionField (algebraMap (Y.presheaf.stalk y) Y.functionField s))
            fun j => D k Y.functionField (algebraMap (Y.presheaf.stalk y) Y.functionField (yv j))
              : Fin (m + 1) → Ω[Y.functionField⁄k]))) p),
        AlgebraicGeometry.functionFieldMap f (X.germToFunctionField (W : X.Opens) t) • ω =
          algebraMap (Y.presheaf.stalk y) Y.functionField ρ • η)
    (S : Set.powersetCard (Fin (m + 1)) p) :
    letI := MMP.Mori.stalkAlgebra sX E.genericPoint
    letI := MMP.Mori.functionFieldAlgebra sX
    letI := MMP.Mori.functionFieldAlgebra (f ≫ sX)
    letI := MMP.Mori.functionFieldMapAlgebra f
    haveI := MMP.Mori.isScalarTower_functionFieldMap sX f
    haveI := MMP.Mori.isScalarTower_stalk_functionField sX E.genericPoint
    haveI := finiteDimensional_functionFieldMap f
    haveI := isSeparable_functionFieldMap sX f
    ((logBasis k bA htK).exteriorPower p).repr (formsTrace k X.functionField Y.functionField p ω)
      S ∈ (algebraMap E.localRing X.functionField).range := by
  have : Nonempty (W : X.Opens) := ⟨⟨_, hEW⟩⟩
  let := MMP.Mori.stalkAlgebra sX E.genericPoint
  let := MMP.Mori.functionFieldAlgebra sX
  let := MMP.Mori.functionFieldAlgebra (f ≫ sX)
  let := MMP.Mori.functionFieldMapAlgebra f
  have := MMP.Mori.isScalarTower_functionFieldMap sX f
  have := MMP.Mori.isScalarTower_stalk_functionField sX E.genericPoint
  have := finiteDimensional_functionFieldMap f
  have := isSeparable_functionFieldMap sX f
  refine formsTrace_repr_mem_range_localRing sX f ‹_› ‹_› E W hEW t ht (logBasis k bA htK) p ω
    ?_ S
  intro y hy S'
  obtain ⟨s, hmR, yv, bR, hbR, ρ, hρ, η, hη, heq⟩ := hω y hy
  let := MMP.Mori.stalkAlgebra (f ≫ sX) y
  have := MMP.Mori.isScalarTower_stalk_functionField (f ≫ sX) y
  let : Algebra E.localRing (Y.presheaf.stalk y) := (placeHom f hy).hom.toAlgebra
  let : Algebra E.localRing Y.functionField :=
    ((algebraMap X.functionField Y.functionField).comp
      (algebraMap E.localRing X.functionField)).toAlgebra
  have : IsScalarTower E.localRing X.functionField Y.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower E.localRing (Y.presheaf.stalk y) Y.functionField :=
    IsScalarTower.of_algebraMap_eq fun a => (algebraMap_placeHom f hy a).symm
  have : IsScalarTower k E.localRing (Y.presheaf.stalk y) := isScalarTower_placeHom f sX hy
  have : IsScalarTower k E.localRing Y.functionField := IsScalarTower.to₁₂₄ k E.localRing
    X.functionField Y.functionField
  have : IsLocalHom (algebraMap E.localRing (Y.presheaf.stalk y)) := isLocalHom_placeHom f hy
  have := isSeparable_residueField_placeHom f sX hy
  have := isDiscreteValuationRing_stalk_of_map_eq_genericPoint f E hy
  have hinj : Function.Injective (algebraMap E.localRing (Y.presheaf.stalk y)) :=
    Function.Injective.of_comp (f := algebraMap (Y.presheaf.stalk y) Y.functionField) <| by
      rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq]
      exact (algebraMap X.functionField Y.functionField).injective.comp
        (IsFractionRing.injective E.localRing X.functionField)
  have htm : X.presheaf.germ (W : X.Opens) E.genericPoint hEW t ∈ maximalIdeal E.localRing :=
    ht ▸ Ideal.mem_span_singleton_self _
  have ht0 : X.presheaf.germ (W : X.Opens) E.genericPoint hEW t ≠ 0 := fun h0 =>
    htK (by rw [h0, map_zero])
  obtain ⟨uu, huu, e, he, hts⟩ := exists_isUnit_mul_pow_of_mem_maximalIdeal
    (algebraMap E.localRing (Y.presheaf.stalk y)) hinj hmR htm ht0
  have hs : algebraMap (Y.presheaf.stalk y) Y.functionField s ≠ 0 :=
    algebraMap_ne_zero_of_maximalIdeal_eq_span hmR
  have htL : algebraMap E.localRing Y.functionField
      (X.presheaf.germ (W : X.Opens) E.genericPoint hEW t) =
      AlgebraicGeometry.functionFieldMap f (X.germToFunctionField (W : X.Opens) t) :=
    congrArg (algebraMap X.functionField Y.functionField)
      (Scheme.algebraMap_germ_eq_germToFunctionField X hEW t)
  rw [← htL] at heq ⊢
  exact exists_mem_maximalIdeal_mul_repr_logBasis_of_smul k ht x bA hbA hmR yv bR hbR huu he hts
    htK hs hρ hη heq S'

/-- **The trace at a prime divisor, regular case.** If at every point `y` over the generic point
of `E` one has `ω = ρ • η` with `ρ ∈ 𝒪_{Y,y}` and `η` in the `p`-th wedge of the regular forms of
an adapted basis at `y`, then the coordinates of `formsTrace ω` in the `p`-th exterior power of
`regBasis k bA` lie in `𝒪_{X,E}`. -/
theorem formsTrace_repr_regBasis_mem_range (E : MMP.Mori.PrimeDivisor X) (W : X.affineOpens)
    (hEW : E.genericPoint ∈ (W : X.Opens)) (t : Γ(X, W))
    (ht : maximalIdeal E.localRing =
      Ideal.span {X.presheaf.germ (W : X.Opens) E.genericPoint hEW t})
    {m : ℕ} (x : Fin m → E.localRing)
    (bA : letI := MMP.Mori.stalkAlgebra sX E.genericPoint
      Module.Basis (Fin (m + 1)) E.localRing Ω[E.localRing⁄k])
    (hbA : letI := MMP.Mori.stalkAlgebra sX E.genericPoint
      ∀ i, bA i = D k E.localRing ((Fin.cons (X.presheaf.germ (W : X.Opens) E.genericPoint hEW t)
        x : Fin (m + 1) → E.localRing) i))
    (htK : algebraMap E.localRing X.functionField
      (X.presheaf.germ (W : X.Opens) E.genericPoint hEW t) ≠ 0)
    (p : ℕ) (ω : letI := MMP.Mori.functionFieldAlgebra (f ≫ sX)
      ⋀[Y.functionField]^p Ω[Y.functionField⁄k])
    (hω : ∀ y : Y, f y = E.genericPoint →
      letI := MMP.Mori.stalkAlgebra (f ≫ sX) y
      letI := MMP.Mori.functionFieldAlgebra (f ≫ sX)
      haveI := MMP.Mori.isScalarTower_stalk_functionField (f ≫ sX) y
      haveI : Nonempty (W : X.Opens) := ⟨⟨_, hEW⟩⟩
      ∃ (s : Y.presheaf.stalk y) (_ : maximalIdeal (Y.presheaf.stalk y) = Ideal.span {s})
        (yv : Fin m → Y.presheaf.stalk y)
        (bR : Module.Basis (Fin (m + 1)) (Y.presheaf.stalk y) Ω[Y.presheaf.stalk y⁄k])
        (_ : ∀ i, bR i = D k (Y.presheaf.stalk y)
          ((Fin.cons s yv : Fin (m + 1) → Y.presheaf.stalk y) i))
        (ρ : Y.presheaf.stalk y) (η : ⋀[Y.functionField]^p Ω[Y.functionField⁄k])
        (_ : η ∈ wedgeSpan (Y.presheaf.stalk y) (Submodule.span (Y.presheaf.stalk y)
          (Set.range fun j => D k Y.functionField (algebraMap (Y.presheaf.stalk y) Y.functionField
            ((Fin.cons s yv : Fin (m + 1) → Y.presheaf.stalk y) j)))) p),
        ω = algebraMap (Y.presheaf.stalk y) Y.functionField ρ • η)
    (S : Set.powersetCard (Fin (m + 1)) p) :
    letI := MMP.Mori.stalkAlgebra sX E.genericPoint
    letI := MMP.Mori.functionFieldAlgebra sX
    letI := MMP.Mori.functionFieldAlgebra (f ≫ sX)
    letI := MMP.Mori.functionFieldMapAlgebra f
    haveI := MMP.Mori.isScalarTower_functionFieldMap sX f
    haveI := MMP.Mori.isScalarTower_stalk_functionField sX E.genericPoint
    haveI := finiteDimensional_functionFieldMap f
    haveI := isSeparable_functionFieldMap sX f
    ((regBasis k (K := X.functionField) bA).exteriorPower p).repr
      (formsTrace k X.functionField Y.functionField p ω)
      S ∈ (algebraMap E.localRing X.functionField).range := by
  have : Nonempty (W : X.Opens) := ⟨⟨_, hEW⟩⟩
  let := MMP.Mori.stalkAlgebra sX E.genericPoint
  let := MMP.Mori.functionFieldAlgebra sX
  let := MMP.Mori.functionFieldAlgebra (f ≫ sX)
  let := MMP.Mori.functionFieldMapAlgebra f
  have := MMP.Mori.isScalarTower_functionFieldMap sX f
  have := MMP.Mori.isScalarTower_stalk_functionField sX E.genericPoint
  have := finiteDimensional_functionFieldMap f
  have := isSeparable_functionFieldMap sX f
  refine formsTrace_repr_mem_range_localRing sX f ‹_› ‹_› E W hEW t ht
    (regBasis k (K := X.functionField) bA) p ω ?_ S
  intro y hy S'
  obtain ⟨s, hmR, yv, bR, hbR, ρ, η, hη, heq⟩ := hω y hy
  let := MMP.Mori.stalkAlgebra (f ≫ sX) y
  have := MMP.Mori.isScalarTower_stalk_functionField (f ≫ sX) y
  let : Algebra E.localRing (Y.presheaf.stalk y) := (placeHom f hy).hom.toAlgebra
  let : Algebra E.localRing Y.functionField :=
    ((algebraMap X.functionField Y.functionField).comp
      (algebraMap E.localRing X.functionField)).toAlgebra
  have : IsScalarTower E.localRing X.functionField Y.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower E.localRing (Y.presheaf.stalk y) Y.functionField :=
    IsScalarTower.of_algebraMap_eq fun a => (algebraMap_placeHom f hy a).symm
  have : IsScalarTower k E.localRing (Y.presheaf.stalk y) := isScalarTower_placeHom f sX hy
  have : IsScalarTower k E.localRing Y.functionField := IsScalarTower.to₁₂₄ k E.localRing
    X.functionField Y.functionField
  have : IsLocalHom (algebraMap E.localRing (Y.presheaf.stalk y)) := isLocalHom_placeHom f hy
  have := isSeparable_residueField_placeHom f sX hy
  have := isDiscreteValuationRing_stalk_of_map_eq_genericPoint f E hy
  have hinj : Function.Injective (algebraMap E.localRing (Y.presheaf.stalk y)) :=
    Function.Injective.of_comp (f := algebraMap (Y.presheaf.stalk y) Y.functionField) <| by
      rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq]
      exact (algebraMap X.functionField Y.functionField).injective.comp
        (IsFractionRing.injective E.localRing X.functionField)
  have htm : X.presheaf.germ (W : X.Opens) E.genericPoint hEW t ∈ maximalIdeal E.localRing :=
    ht ▸ Ideal.mem_span_singleton_self _
  have ht0 : X.presheaf.germ (W : X.Opens) E.genericPoint hEW t ≠ 0 := fun h0 =>
    htK (by rw [h0, map_zero])
  obtain ⟨uu, huu, e, he, hts⟩ := exists_isUnit_mul_pow_of_mem_maximalIdeal
    (algebraMap E.localRing (Y.presheaf.stalk y)) hinj hmR htm ht0
  have hs : algebraMap (Y.presheaf.stalk y) Y.functionField s ≠ 0 :=
    algebraMap_ne_zero_of_maximalIdeal_eq_span hmR
  have htL : algebraMap E.localRing Y.functionField
      (X.presheaf.germ (W : X.Opens) E.genericPoint hEW t) =
      AlgebraicGeometry.functionFieldMap f (X.germToFunctionField (W : X.Opens) t) :=
    congrArg (algebraMap X.functionField Y.functionField)
      (Scheme.algebraMap_germ_eq_germToFunctionField X hEW t)
  rw [← htL]
  exact exists_mem_maximalIdeal_mul_repr_regBasis_of_smul k ht x bA hbA hmR yv bR hbR huu he hts
    htK hs hη heq S'

end MMP.FourfoldProofs.FractionalLogComplexProof
