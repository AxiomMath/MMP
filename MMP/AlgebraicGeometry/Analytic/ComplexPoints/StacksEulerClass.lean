module

public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.StacksThomClass
public import MMP.AlgebraicGeometry.CycleMap.Stacks.LocalizedFirstChern.ThomChartGeneric
public import MMP.AlgebraicTopology.ThomClass.Gysin

/-!
# The Euler class of a Stacks vector bundle (Fulton, §19.1)

For a quasi-coherent `𝒪_X`-module `ℰ`, finite locally free of rank `r`, on a scheme over `ℂ`, the
Euler class `e(𝐕(ℰ)(ℂ)) = 0^* u ∈ H^{2r}(X(ℂ))` of the complex topological vector bundle
`𝐕(ℰ)(ℂ) → X(ℂ)` (`MMP.Topology.eulerClass`) is the pull-back along the zero section
`0 : X ⟶ 𝐕(ℰ)` of the Thom class `u_ℰ` of `𝐕(ℰ)` (`MMP.Modules.thomClass`). For `r = 1` this is
the topological first Chern class `c₁(𝐕(ℰ))`
(`ComplexLineBundle.congrIndex_eulerClass_eq_firstChernClass`).

## Main results

* `MMP.Modules.cast_eulerClass_eq_map_thomClass`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
* [J. Milnor, J. Stasheff, *Characteristic classes*][milnorstasheff1974], §9.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Set

namespace MMP.Modules

open UnderlyingSpace relativeSingularCohomology

variable (R : Type) [CommRing R]

/-- `relativeSingularCohomology.map` commutes with the identification of the degrees `2a = 2b`
for `a = b`. -/
lemma cast_map_two_mul {Y' Y : TopCat.{0}} (f : Y' ⟶ Y) {A' : Set Y'} {A : Set Y}
    (hf : A' ⊆ f ⁻¹' A) {a b : ℕ} (h : a = b)
    (u : relativeSingularCohomology R (ModuleCat.of R R) Y A (2 * a : ℕ)) :
    cast (congrArg (fun n : ℕ ↦ (relativeSingularCohomology R (ModuleCat.of R R) Y' A'
        (2 * n : ℕ) : Type)) h) ((map R (ModuleCat.of R R) f hf (2 * a : ℕ)).hom u) =
      (map R (ModuleCat.of R R) f hf (2 * b : ℕ)).hom
        (cast (congrArg (fun n : ℕ ↦ (relativeSingularCohomology R (ModuleCat.of R R) Y A
          (2 * n : ℕ) : Type)) h) u) := by
  subst h
  rfl

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] (E : X.Modules) [E.IsQuasicoherent] (r : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E r]

/-- The zero section `0 : X(ℂ) → 𝐕(ℰ)(ℂ)`, as a map of spaces. -/
def zeroSectionHom :
    TopCat.of (UnderlyingSpace ℂ X) ⟶ TopCat.of (UnderlyingSpace ℂ (totalSpace E)) :=
  TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (zeroSection E))

/-- The zero section of `𝐕(ℰ)(ℂ)`, read in the topological bundle, is its zero section. -/
lemma zeroSectionHom_totalSpaceInv :
    zeroSectionHom E ≫ totalSpaceInv E r = MMP.Topology.bundleZeroSection (Fin r → ℂ) (Fibre E r) := by
  refine ConcreteCategory.hom_ext _ _ fun x ↦ ?_
  change (totalSpaceHomeomorph E r).symm (mapFun (zeroSection E) x) = ⟨x, 0⟩
  rw [Homeomorph.symm_apply_eq]
  exact (zero_fibre_val E x).symm

/-- **The Euler class of `𝐕(ℰ)(ℂ)` is the zero-section pull-back of the Thom class of `𝐕(ℰ)`**:
`e(𝐕(ℰ)(ℂ)) = 0^* u_ℰ` in `H^{2r}(X(ℂ))`. -/
theorem cast_eulerClass_eq_map_thomClass :
    cast (congrArg (fun n : ℕ ↦ (cohomologyWithSupports R (ModuleCat.of R R)
        (TopCat.of (UnderlyingSpace ℂ X)) univ (2 * n : ℕ) : Type))
        (Module.finrank_fin_fun ℂ (n := r)))
      (MMP.Topology.eulerClass R (Fin r → ℂ) (Fibre E r)) =
      (map R (ModuleCat.of R R) (zeroSectionHom E) (A' := univᶜ)
        (fun x hx ↦ (hx (mem_univ x)).elim) (2 * r : ℕ)).hom (thomClass R E r) := by
  rw [thomClass_eq_pullbackAlg R E r, ← map_hom_comp_apply R (zeroSectionHom E)
    (totalSpaceInv E r) (fun x hx ↦ (hx (mem_univ x)).elim) _
    (fun x hx ↦ (hx (mem_univ x)).elim)]
  refine Eq.trans ?_ (congrArg (fun φ ↦ ModuleCat.Hom.hom φ _)
    (map_eq_map_of_hom_eq R (zeroSectionHom_totalSpaceInv E r) _
      (fun x hx ↦ (hx (mem_univ x)).elim) _)).symm
  exact cast_map_two_mul R (MMP.Topology.bundleZeroSection (Fin r → ℂ) (Fibre E r))
    (fun x hx ↦ (hx (mem_univ x)).elim) (Module.finrank_fin_fun ℂ) _

end MMP.Modules
