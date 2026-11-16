module

public import MMP.AlgebraicTopology.PoincareDuality.AlexanderFiveLemma
public import MMP.AlgebraicTopology.PoincareDuality.AlexanderCocycleDuality
public import MMP.Topology.Manifold.NeighbourhoodRetract.Basic
public import MMP.AlgebraicTopology.PoincareDuality.TopDegree
/-!
# Alexander duality for an oriented real manifold (Fulton, §19.1, (3))

Let `M` be a Hausdorff, second countable real `n`-manifold, connected or not, with fundamental
class `μ` (`IsFundamentalClass`), and `X ⊆ M` closed with arbitrarily small proper neighbourhood
deformations (`HasProperNeighbourhoodDeformations`; for instance `X` closed and locally
contractible). Then `c ↦ c ∩ μ`, `H^{n-k}(M, M - X) → H_k X`, is bijective for every `k`
(`MMP.borelMooreHomology.bijective_dualityMap_of_isFundamentalClass`), and every
`a ∈ H_k X` has exactly one dual class
(`MMP.borelMooreHomology.existsUnique_isDualClassWithSupports_of_isFundamentalClass`).

Proof: Poincaré duality on `M` and on the open submanifold `U = M - X` with `μ|_U`
(`PoincareAlexander.bijective_capProduct_univ_of_dualityAt`), and the five lemma
(`bijective_dualityMap_of_bijective_capProduct`), with the proper deformations of
neighbourhoods of `X`, which fix `X` (`HasProperNeighbourhoodDeformations`).

Tagged: `thm_ext_c19_alexander_duality_general`, `thm_ext_c19_poincare_alexander_duality`,
`lem_c19_topological_dual_class_well_defined`.
-/

@[expose] public noncomputable section

open CategoryTheory Set

universe u v

namespace MMP

namespace borelMooreHomology

open BorelMooreCross PoincareAlexander

variable {R : Type u} [CommRing R]
  {H : Type v} [NormedAddCommGroup H] [NormedSpace ℝ H] {M : Type u} [TopologicalSpace M]
  [T2Space M] [SecondCountableTopology M] [ChartedSpace H M]

/-- Poincaré duality on Fulton's groups for a fundamental class: `c ↦ c ∩ μ`, `H^j M → H_{n-j} M`,
is bijective for every `j`. -/
theorem bijective_capProduct_univ_of_isFundamentalClass {n : ℕ} (b : Module.Basis (Fin n) ℝ H)
    (μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of M) n) (hμ : IsFundamentalClass R b μ)
    (j : ℤ) : Function.Bijective fun c ↦ capProduct R (TopCat.of M) univ j n c μ := by
  obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (homologyEquiv R (TopCat.of M) n μ)
  exact bijective_capProduct_univ_of_dualityAt hz.symm
    (dualityAt_of_isFundamentalClass b μ hμ z hz.symm) j

/-- **Alexander duality** (Fulton, §19.1, (3); [BT] 4.1.3, Bredon VI.8). Let `M` be a Hausdorff,
second countable real `n`-manifold, connected or not, with fundamental class `μ`, and `X ⊆ M`
closed with arbitrarily small proper neighbourhood deformations (for instance `X` closed and
locally contractible, `hasProperNeighbourhoodDeformations_of_chartedSpace`). Then `c ↦ c ∩ μ`,
`H^{n-k}(M, M - X) → H_k X`, is bijective for every `k`. -/
theorem bijective_dualityMap_of_isFundamentalClass {n : ℕ} (b : Module.Basis (Fin n) ℝ H)
    (μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of M) n) (hμ : IsFundamentalClass R b μ)
    {X : Set (TopCat.of M)} (hX : IsClosed X) (hXd : HasProperNeighbourhoodDeformations X)
    (k : ℤ) : Function.Bijective (dualityMap R hX hXd μ k) := by
  obtain ⟨N, hN, hXN, -, r, hr, hrX, G, hG, hG0, hG1, hGX, -⟩ := hXd univ Filter.univ_mem
  obtain ⟨N', hN', hXN', hN'N, -⟩ := hXd _ (isOpen_interior.mem_nhdsSet.2 hXN)
  have hq : IsRelativeQuasiIso R (ModuleCat.of R R) hX :=
    isRelativeQuasiIso_of_homotopy R _ hX hN hN' hXN' hN'N hG hG0
      (fun y ↦ (hG1 y).symm ▸ (r y).2) hGX
  let U : TopologicalSpace.Opens M := complOpens hX
  refine bijective_dualityMap_of_bijective_capProduct hX hq hXd hN hXN hr hrX hG hGX hG0 hG1 μ
    (bijective_capProduct_univ_of_isFundamentalClass b μ hμ) ?_ k
  exact bijective_capProduct_univ_of_isFundamentalClass (M := U) b _ (hμ.restrict U)

/-- **Poincaré–Alexander duality** (Fulton, §19.1, (3); [BT] 4.1.3). Let `M` be a connected,
Hausdorff, second countable real `n`-manifold. Then every fundamental class `μ_M` freely
generates `H_n M`, and for every closed `X ⊆ M` with arbitrarily small proper neighbourhood
deformations (for instance `X` closed and locally contractible) and every `k`,
`c ↦ c ∩ μ_M`, `H^{n-k}(M, M - X) → H_k X`, is bijective. -/
theorem topHomologyFreeOnFundamentalClass_and_bijective_dualityMap [ConnectedSpace M] {n : ℕ}
    (b : Module.Basis (Fin n) ℝ H) :
    TopHomologyFreeOnFundamentalClass R M b ∧
      ∀ μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of M) n, IsFundamentalClass R b μ →
        ∀ (X : Set (TopCat.of M)) (hX : IsClosed X) (hXd : HasProperNeighbourhoodDeformations X)
          (k : ℤ), Function.Bijective (dualityMap R hX hXd μ k) :=
  ⟨PoincareDuality.topHomologyFreeOnFundamentalClass_of_manifold b,
    fun μ hμ _ hX hXd k ↦ bijective_dualityMap_of_isFundamentalClass b μ hμ hX hXd k⟩

/-- **The dual class** (Fulton, Example 19.1.10). Let `M` be a Hausdorff, second countable real
`n`-manifold with fundamental class `μ_M`, and `A ⊆ M` closed with arbitrarily small proper
neighbourhood deformations (the setting of `IsDualClassWithSupports`). Every `a ∈ H_k A` has
exactly one dual class `c ∈ H^{n-k}(M, M - A)`, `c ∩ μ_M = a`. -/
theorem existsUnique_isDualClassWithSupports_of_isFundamentalClass {n : ℕ}
    (b : Module.Basis (Fin n) ℝ H)
    (μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of M) n) (hμ : IsFundamentalClass R b μ)
    {A : Set (TopCat.of M)} (hA : IsClosed A) (hAd : HasProperNeighbourhoodDeformations A) {k : ℤ}
    (a : borelMooreHomology R (ModuleCat.of R R) (TopCat.of A) k) :
    ∃! c : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of M) A (n - k),
      IsDualClassWithSupports R hA hAd μ c a :=
  existsUnique_isDualClassWithSupports_of_bijective
    (bijective_dualityMap_of_isFundamentalClass b μ hμ hA hAd k) a

end borelMooreHomology

end MMP
