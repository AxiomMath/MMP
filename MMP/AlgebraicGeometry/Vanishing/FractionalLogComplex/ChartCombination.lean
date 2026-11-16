module

public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.RationalFormWellDefined

/-!
# Rational forms of combinations of wedges of chart forms

Let `X` be an integral scheme over a field `k` and `O ⊆ O₀` opens with `O` affine and non-empty.
A combination `∑_K c_K · θ_{K}` over `O₀`, with `c_K` functions and `θ_K` products of forms of
non-negative degree, restricts to `O` and has rational form `∑_K c_K · β_K`, where `β_K` is the
product of the rational forms of the factors. For the factors `s · dt` with `s t = 1` and `dt`
the rational forms are `t⁻¹ dt` and `dt`. These are the rational forms of the bases of the
logarithmic forms on a chart of a relative simple normal crossing divisor.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.ratTotal_totalRestrict_sum`: the rational form of a
  restricted combination.
* `MMP.FourfoldProofs.FractionalLogComplexProof.ratTotal_totalRestrict_logOne`: the rational form of
  `s · dt` with `s t = 1` is `t⁻¹ dt`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite KaehlerDifferential

namespace MMP.FourfoldProofs.FractionalLogComplexProof

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))

/-- Restricting the product of a list of forms gives the product of the restricted forms. -/
theorem totalRestrict_list_prod {O₀ O : X.Opens} (hO : O ≤ O₀)
    (l : List ((Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.Total
      (op O₀))) :
    (Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.totalRestrict
        (homOfLE hO).op l.prod =
      (l.map ((Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.totalRestrict
        (homOfLE hO).op)).prod :=
  map_list_prod
    ((Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.totalRestrictRingHom
    (homOfLE hO).op) l

/-- **The rational form of a restricted combination of products of forms.** -/
theorem ratTotal_totalRestrict_sum [IsIntegral X] {O₀ : X.Opens} {O : X.affineOpens}
    (hO : (O : X.Opens) ≤ O₀) [Nonempty (O : X.Opens)] {ι κ : Type*} (s : Finset ι)
    (c : ι → Γ(X, O₀))
    (θ : κ → (Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.Total
      (op O₀)) (l : ι → List κ)
    (hθ : ∀ j,
      (Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.totalRestrict
      (homOfLE hO).op (θ j) ∈ nonnegForms sX O) :
    letI := MMP.Mori.functionFieldAlgebra sX
    ratTotal sX O
      ((Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.totalRestrict
        (homOfLE hO).op (∑ K ∈ s,
          (Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.structureMap
            (op O₀) (c K) * ((l K).map θ).prod)) =
      ∑ K ∈ s, algebraMap X.functionField (ExteriorAlgebra X.functionField Ω[X.functionField⁄k])
          (X.germToFunctionField O (X.presheaf.map (homOfLE hO).op (c K))) *
        ((l K).map fun j => ratTotal sX O
          ((Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.totalRestrict
            (homOfLE hO).op (θ j))).prod := by
  let := MMP.Mori.functionFieldAlgebra sX
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun K _ => ?_
  have hsm : (Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.totalRestrict
      (homOfLE hO).op
      ((Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.structureMap
        (op O₀) (c K)) =
      (Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.structureMap
        (op (O : X.Opens)) (X.presheaf.map (homOfLE hO).op (c K)) :=
    Stacks.GradedAlgebra.structureMap_naturality _ _ _
  rw [Stacks.GradedAlgebra.totalRestrict_mul, hsm, totalRestrict_list_prod, List.map_map]
  have hl : ∀ z ∈ (l K).map
      (((Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.totalRestrict
      (homOfLE hO).op) ∘ θ), z ∈ nonnegForms sX O := by
    intro z hz
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hz
    exact hθ j
  rw [ratTotal_mul sX O (structureMap_mem_nonnegForms sX O _)
    (list_prod_mem_nonnegForms sX O _ hl), ratTotal_structureMap, ratTotal_list_prod sX O _ hl,
    List.map_map]
  rfl

/-- Restricting `d t` from `O₀` to `O` gives `d` of the restriction of `t`. -/
theorem totalRestrict_exactOne {O₀ O : X.Opens} (hO : O ≤ O₀) (t : Γ(X, O₀)) :
    (Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.totalRestrict
        (homOfLE hO).op
        ((Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.incl 1
          ((Scheme.Modules.exteriorGenerator (Scheme.Hom.relativeDifferentials sX)).val.app
            (op O₀) ((Scheme.Hom.universalRelativeDerivation sX).d (X := op O₀) t))) =
        (Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.incl 1
          ((Scheme.Modules.exteriorGenerator (Scheme.Hom.relativeDifferentials sX)).val.app
            (op O) ((Scheme.Hom.universalRelativeDerivation sX).d (X := op O)
              (X.presheaf.map (homOfLE hO).op t))) :=
  (Stacks.GradedAlgebra.totalRestrict_incl _ _ 1 _).trans
    (congrArg ((Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.incl 1)
      (exactOne_restrict sX hO t))

/-- Restricting `s · d t` from `O₀` to `O` gives `s|_O · d (t|_O)`. -/
theorem totalRestrict_structureMap_mul_exactOne {O₀ O : X.Opens} (hO : O ≤ O₀) (s t : Γ(X, O₀)) :
    (Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.totalRestrict
        (homOfLE hO).op
        ((Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.structureMap
          (op O₀) s *
        (Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.incl 1
          ((Scheme.Modules.exteriorGenerator (Scheme.Hom.relativeDifferentials sX)).val.app
            (op O₀) ((Scheme.Hom.universalRelativeDerivation sX).d (X := op O₀) t))) =
      (Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.structureMap
          (op O) (X.presheaf.map (homOfLE hO).op s) *
        (Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.incl 1
          ((Scheme.Modules.exteriorGenerator (Scheme.Hom.relativeDifferentials sX)).val.app
            (op O) ((Scheme.Hom.universalRelativeDerivation sX).d (X := op O)
              (X.presheaf.map (homOfLE hO).op t))) := by
  have hsm : (Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.totalRestrict
      (homOfLE hO).op
      ((Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.structureMap
        (op O₀) s) =
      (Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.structureMap
        (op O) (X.presheaf.map (homOfLE hO).op s) :=
    Stacks.GradedAlgebra.structureMap_naturality _ _ _
  rw [Stacks.GradedAlgebra.totalRestrict_mul, hsm]
  exact congrArg (_ * ·) (totalRestrict_exactOne sX hO t)

/-- **The rational form of `s · d t` with `s t = 1` is `t⁻¹ d t`.** -/
theorem ratTotal_totalRestrict_logOne [IsIntegral X] {O₀ : X.Opens} {O : X.affineOpens}
    (hO : (O : X.Opens) ≤ O₀) [Nonempty (O : X.Opens)] {s t : Γ(X, O₀)} (hst : s * t = 1) :
    letI := MMP.Mori.functionFieldAlgebra sX
    ratTotal sX O
      ((Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.totalRestrict
        (homOfLE hO).op
        ((Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.structureMap
          (op O₀) s *
        (Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.incl 1
          ((Scheme.Modules.exteriorGenerator (Scheme.Hom.relativeDifferentials sX)).val.app
            (op O₀) ((Scheme.Hom.universalRelativeDerivation sX).d (X := op O₀) t)))) =
      ExteriorAlgebra.ι X.functionField
        ((X.germToFunctionField O (X.presheaf.map (homOfLE hO).op t))⁻¹ •
          D k X.functionField (X.germToFunctionField O (X.presheaf.map (homOfLE hO).op t))) := by
  let := MMP.Mori.functionFieldAlgebra sX
  rw [totalRestrict_structureMap_mul_exactOne, ratTotal_structureMap_mul_exactOne, map_smul,
    Algebra.smul_def]
  congr 2
  refine (eq_inv_of_mul_eq_one_left ?_)
  rw [← map_mul, ← map_mul, hst, map_one, map_one]

/-- The rational form of `d t` is `d t`. -/
theorem ratTotal_totalRestrict_exactOne [IsIntegral X] {O₀ : X.Opens} {O : X.affineOpens}
    (hO : (O : X.Opens) ≤ O₀) [Nonempty (O : X.Opens)] (t : Γ(X, O₀)) :
    letI := MMP.Mori.functionFieldAlgebra sX
    ratTotal sX O
      ((Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.totalRestrict
        (homOfLE hO).op
        ((Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.incl 1
          ((Scheme.Modules.exteriorGenerator (Scheme.Hom.relativeDifferentials sX)).val.app
            (op O₀) ((Scheme.Hom.universalRelativeDerivation sX).d (X := op O₀) t)))) =
      ExteriorAlgebra.ι X.functionField
        (D k X.functionField (X.germToFunctionField O (X.presheaf.map (homOfLE hO).op t))) := by
  rw [totalRestrict_exactOne]
  exact ratTotal_incl_exactOne sX O _

end MMP.FourfoldProofs.FractionalLogComplexProof
