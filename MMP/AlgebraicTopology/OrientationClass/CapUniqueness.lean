module

public import MMP.AlgebraicTopology.PoincareDuality.TopDegree
public import MMP.AlgebraicTopology.PoincareDuality.LocalPackage
public import MMP.AlgebraicTopology.FundamentalClass.Locality

/-!
# Uniqueness of the fundamental class of a connected manifold

On a connected, Hausdorff, second countable real `n`-manifold `Y` (`n ≥ 1`), oriented in its
charts by a basis `b`, two fundamental classes are equal: by Poincaré duality in top degree
(`MMP.PoincareDuality.topHomologyFreeOnFundamentalClass_of_manifold`) the second
is `r • μ`, and pairing with a relative cocycle of `(Y, Y - y)` which is `1` on an oriented chart
simplex at `y` gives `r = 1`. This is the step "`(f^* μ_P)|_Ω = (μ_U × μ_F)|_Ω`" of
`lem_ext_c19_orientation_class_cap_fundamental`.

## Main results

* `MMP.FundamentalClass.IsLocallyClassOf.eq_one_of_smul`: if `ν` and `r • ν` are
  both locally the class of `Δ` at `x`, and some relative cocycle is `1` on `Δ`, then `r = 1`.
* `MMP.IsFundamentalClass.eq_of_connectedSpace`: uniqueness of the fundamental
  class of a connected manifold.
-/

@[expose] public noncomputable section

open CategoryTheory Set Topology Opposite Simplicial
open MMP.SingularChain MMP.SingularCochain
  MMP.ThomClass

universe u v

namespace MMP

namespace FundamentalClass

variable {R : Type u} [CommRing R] {X : TopCat.{u}}

/-- If `ν` and `r • ν` are both locally the class of the simplex `Δ` at `x`, and some relative
cocycle of `(X, X - x)` takes the value `1` on `Δ`, then `r = 1`. -/
theorem IsLocallyClassOf.eq_one_of_smul {n : ℕ}
    {ν : borelMooreHomology R (ModuleCat.of R R) X n} {x : X} {Δ : Simplex X n} {r : R}
    (hν : IsLocallyClassOf R ν x Δ) (hrν : IsLocallyClassOf R (r • ν) x Δ)
    {φ : Simplex X n → R} (hφ : φ ∈ relCocycles R ({x}ᶜ : Set X) n) (hφ1 : φ Δ = 1) :
    r = 1 := by
  set C := borelMooreChainComplex R (ModuleCat.of R R) X
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective (C.homologyπ n)).1 inferInstance
    ((borelMooreHomologyIsoOfNat R (ModuleCat.of R R) X n).hom ν)
  have hrz : C.homologyπ n (r • z) =
      (borelMooreHomologyIsoOfNat R (ModuleCat.of R R) X n).hom (r • ν) := by
    rw [map_smul, hz, map_smul]
  have h1 := hν z hz φ hφ
  have h2 := hrν (r • z) hrz φ hφ
  rw [← chainPairing_apply hφ.1, map_smul, map_smul, chainPairing_apply hφ.1, h1, hφ1,
    smul_eq_mul, mul_one] at h2
  exact h2

end FundamentalClass

open FundamentalClass

variable {R : Type u} [CommRing R] {H : Type v} [AddCommGroup H] [Module ℝ H]
  [TopologicalSpace H] [ContinuousAdd H] [ContinuousSMul ℝ H] [T2Space H]
  {Y : Type u} [TopologicalSpace Y] [T2Space Y] [ChartedSpace H Y]

/-- **Uniqueness of the fundamental class.** On a connected, Hausdorff, second countable real
`(m + 1)`-manifold `Y`, oriented in its charts by the basis `b`, any two fundamental classes are
equal. -/
theorem IsFundamentalClass.eq_of_connectedSpace [SecondCountableTopology Y] [ConnectedSpace Y]
    {m : ℕ} {b : Module.Basis (Fin (m + 1)) ℝ H}
    {μ μ' : borelMooreHomology R (ModuleCat.of R R) (TopCat.of Y) (m + 1 : ℕ)}
    (hμ : IsFundamentalClass R b μ) (hμ' : IsFundamentalClass R b μ') : μ' = μ := by
  obtain ⟨r, hr⟩ := (PoincareDuality.topHomologyFreeOnFundamentalClass_of_manifold
    (R := R) (Y := Y) b μ hμ).2 μ'
  simp only at hr
  obtain ⟨y⟩ : Nonempty Y := inferInstance
  set e := chartAt H y
  have hy : y ∈ e.source := mem_chart_source H y
  obtain ⟨v, hv, hvt⟩ := exists_isOrientedSimplexAroundZero_subset b (e y)
    (e.open_target.mem_nhds (e.map_source hy))
  have h1 := IsLocallyClassOf.of_restrict (chartOpens e)
    (hμ e (chart_mem_atlas H y) ⟨y, hy⟩ v hv hvt)
  have h2 := IsLocallyClassOf.of_restrict (chartOpens e)
    (hμ' e (chart_mem_atlas H y) ⟨y, hy⟩ v hv hvt)
  rw [← hr] at h2
  obtain ⟨φ, hφ, hφ1⟩ := SingularChain.exists_mem_relCocycles_eval_chartSimplexIn (R := R) b e hy
    hv hvt
  have hφ1' : φ (inclChainSimplex (chartOpens e) (chartSimplex e v hvt)) = 1 := by
    rw [← hφ1]
    simp [chartSimplexIn, inclChainSimplex]
    rfl
  rw [← hr, h1.eq_one_of_smul h2 hφ hφ1', one_smul]

end MMP
