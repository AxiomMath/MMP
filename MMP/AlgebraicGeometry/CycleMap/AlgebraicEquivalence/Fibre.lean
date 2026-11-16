module

public import MMP.AlgebraicGeometry.Variety.ParameterPoint
public import MMP.AlgebraicTopology.PoincareDuality.AlexanderFiveLemma
public import MMP.AlgebraicTopology.OrientationClass.CapProductPointClass
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.ParameterPointFibre
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.ComplexSchemeSubscheme
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.Finite

/-!
# Fibres over a point of a curve

Let `f : V → T` be a morphism of complex schemes, `T` a non-singular complex curve, and `t ∈ T` a
parameter point, with complex point `t ∈ T(ℂ)`. The complex points of the scheme-theoretic fibre
`V_t = f⁻¹(t)` map homeomorphically onto `f⁻¹(t) ⊆ V(ℂ)`, which has arbitrarily small proper
neighbourhood deformations; so for `u ∈ H²(T, T - t)` and `μ ∈ H_m V` the cap product
`f^*(u) ∩ μ ∈ H_{m-2}(f⁻¹ t)` is defined and can be compared with classes on `V_t`.

## Main results

* `MMP.Scheme.Hom.isDominant_of_flat`: a flat morphism to an irreducible scheme
  from a non-empty scheme is dominant.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1, Lemma 19.1.3 and Prop. 19.1.1.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits Set
open MMP.UnderlyingSpace

namespace MMP

/-- A flat morphism from a non-empty scheme to an irreducible scheme is dominant: flat morphisms
are generalizing, so the generic point of the target is in the image. -/
theorem Scheme.Hom.isDominant_of_flat {V T : Scheme.{0}} [IrreducibleSpace T] [Nonempty V]
    (f : V ⟶ T) [Flat f] : IsDominant f := by
  obtain ⟨x⟩ := ‹Nonempty V›
  have hη : genericPoint T ⤳ f x := (genericPoint_spec T).specializes (by simp)
  obtain ⟨x', -, hx'⟩ := Flat.generalizingMap f hη
  refine ⟨?_⟩
  rw [DenseRange, dense_iff_closure_eq, eq_univ_iff_forall]
  intro y
  have hsub : closure {genericPoint T} ⊆ closure (range f) :=
    closure_mono (singleton_subset_iff.2 ⟨x', hx'⟩)
  exact hsub (by rw [(genericPoint_spec T).def]; trivial)

/-- The fibre `Y_t` of a `K`-scheme `𝒴` locally of finite type over `K` is locally of finite type
over `K`: `Y_t → 𝒴` is a closed immersion. -/
instance ParameterPoint.locallyOfFiniteType_fibre (K : Type) [Field K] {V T : Scheme.{0}}
    [V.Over (Spec (.of K))] [LocallyOfFiniteType (V ↘ Spec (.of K))] (f : V ⟶ T)
    (t : ParameterPoint T) : LocallyOfFiniteType (ParameterPoint.fibre f t ↘ Spec (.of K)) :=
  inferInstanceAs (LocallyOfFiniteType (ParameterPoint.fibreι f t ≫ V ↘ Spec (.of K)))

/-- The fibre `Y_t` of a `K`-scheme `𝒴` quasi-compact over `K` is quasi-compact over `K`:
`Y_t → 𝒴` is a closed immersion. -/
instance ParameterPoint.quasiCompact_fibre (K : Type) [Field K] {V T : Scheme.{0}}
    [V.Over (Spec (.of K))] [QuasiCompact (V ↘ Spec (.of K))] (f : V ⟶ T)
    (t : ParameterPoint T) : QuasiCompact (ParameterPoint.fibre f t ↘ Spec (.of K)) :=
  inferInstanceAs (QuasiCompact (ParameterPoint.fibreι f t ≫ V ↘ Spec (.of K)))

end MMP
