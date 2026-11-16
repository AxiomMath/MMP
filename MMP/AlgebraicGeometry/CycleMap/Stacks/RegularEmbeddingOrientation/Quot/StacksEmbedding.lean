module

public import MMP.Topology.VectorBundle.FiniteTrivializingEmbedding
public import MMP.AlgebraicGeometry.CycleMap.Stacks.RegularEmbeddingOrientation.StacksNormalFibreChart
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.LocallyContractible
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# A Hermitian embedding of a Stacks vector bundle on a complex scheme

Let `ℰ` be a quasi-coherent `𝒪_Y`-module, finite locally free of rank `r`, on a complex scheme
`Y`, with vector bundle `π : 𝐕(ℰ) ⟶ Y`. Finitely many charts `c = (V, b)` cover `Y` (`Y` is
quasi-compact), and `Y(ℂ)` is paracompact and normal, so a partition of unity `ρ` subordinate to
the chart domains `V(ℂ)` glues the chart trivializations of the topological bundle
`𝐕(ℰ)(ℂ) → Y(ℂ)` (`MMP.Modules.chartTrivialization`) to a continuous map `ι : 𝐕(ℰ)(ℂ) → ℂᵐ`
which is linear and injective on each fibre (`MMP.bundleEmbedding`). In the coordinates of a
chart `c`, `ι` is a family `Φ_c(y) : ℂʳ → ℂᵐ` of injective linear maps, continuous on `V(ℂ)`.

## Main results

* `MMP.Modules.chartInv_eq_chartInv`: `φ_c⁻¹(y, w) = φ_{c'}⁻¹(y, g(y) w)`.
* `MMP.Modules.exists_hermitianEmbedding`: the embedding `ι` and its chart expressions `Φ_c`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Bundle Set Topology

namespace MMP.Modules

open UnderlyingSpace
open scoped Matrix

variable {Y : Scheme.{0}} [Y.Over (Spec (.of ℂ))] {E : Y.Modules} [E.IsQuasicoherent] {r : ℕ}

/-- `φ_c⁻¹(y, w) = φ_{c'}⁻¹(y, g(y) w)`, `g = transition c c'`. -/
lemma chartInv_eq_chartInv (c c' : Chart E r) {y : UnderlyingSpace ℂ Y}
    (hy : ⊤ ≤ y.toHom ⁻¹ᵁ c.1.1) (hy' : ⊤ ≤ y.toHom ⁻¹ᵁ c'.1.1) (w : Fin r → ℂ) :
    chartInv c y hy w = chartInv c' y hy' (transition c c' y *ᵥ w) := by
  have key : ∀ (z : UnderlyingSpace ℂ Y) (hz : z = y) (h : ⊤ ≤ z.toHom ⁻¹ᵁ c'.1.1)
      (v : Fin r → ℂ), chartInv c' z h v = chartInv c' y hy' v := by
    rintro _ rfl _ _
    rfl
  have h1 := chartInv_mapFun_proj_coord c' (chartInv c y hy w) (by
    intro z hz
    change proj E ((chartInv c y hy w).toHom z) ∈ c'.1.1
    rw [← Scheme.Hom.comp_apply, toHom_chartInv_proj]
    exact hy' hz)
  rw [key _ (mapFun_proj_chartInv c y hy w), coord_chartInv_of_mem c c' hy hy'] at h1
  exact h1.symm

variable [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E r]

/-- On the base set of the chart `c`, the inverse of the trivialization
`chartTrivialization c` sends `w` to the fibre point `fibreChartInv c y hy w`. -/
lemma symm_chartTrivialization (c : Chart E r) {y : UnderlyingSpace ℂ Y}
    (hy : y ∈ chartBase c) (w : Fin r → ℂ) :
    (chartTrivialization c).symm y w = fibreChartInv c y hy w := by
  have h := (chartTrivialization c).mk_symm hy w
  rw [← chartFibrePoint_of_mem c hy]
  exact TotalSpace.mk_inj.1 h

variable (E r) in
/-- **A Hermitian embedding of `𝐕(ℰ)(ℂ)`.** There are a continuous map `ι : 𝐕(ℰ)(ℂ) → ℂᵐ`
and, for each chart `c = (V, b)`, a family `Φ_c(y) : ℂʳ → ℂᵐ` of linear maps, continuous on
`V(ℂ)` and injective there, with `ι(φ_c⁻¹(y, w)) = Φ_c(y) w`. -/
theorem exists_hermitianEmbedding [IsComplexScheme Y] :
    ∃ (m : ℕ) (ιE : UnderlyingSpace ℂ (totalSpace E) → EuclideanSpace ℂ (Fin m))
      (Φ : Chart E r → UnderlyingSpace ℂ Y → (Fin r → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin m)),
      Continuous ιE ∧
      (∀ (c : Chart E r) (y : UnderlyingSpace ℂ Y) (hy : ⊤ ≤ y.toHom ⁻¹ᵁ c.1.1)
        (w : Fin r → ℂ), ιE (chartInv c y hy w) = Φ c y w) ∧
      (∀ (c : Chart E r) (y : UnderlyingSpace ℂ Y), y ∈ chartBase c →
        Function.Injective (Φ c y)) ∧
      ∀ c : Chart E r, ContinuousOn (Φ c) (chartBase c) := by
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of ℂ))
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover (fun c : Chart E r ↦ (c.1.1 : Set Y))
    (fun c ↦ c.1.1.isOpen) (fun q _ ↦ by
      obtain ⟨c, hc⟩ := exists_chart_mem (E := E) r q
      exact mem_iUnion.2 ⟨c, hc⟩)
  let t : S → Trivialization (Fin r → ℂ)
      (TotalSpace.proj : TotalSpace (Fin r → ℂ) (Fibre E r) → _) :=
    fun l ↦ chartTrivialization l.1
  haveI : ∀ l : S, (t l).IsLinear ℂ := fun l ↦
    inferInstanceAs ((chartTrivialization l.1).IsLinear ℂ)
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate (X := UnderlyingSpace ℂ Y) isClosed_univ
    (fun l : S ↦ (t l).baseSet) (fun l ↦ (t l).open_baseSet) (fun y _ ↦ by
      obtain ⟨c, hc, hyc⟩ := mem_iUnion₂.1 (hS (mem_univ (y.toHom (IsLocalRing.closedPoint ℂ))))
      exact mem_iUnion.2 ⟨⟨c, hc⟩, (top_le_preimage_iff y _).2 hyc⟩)
  set m := Module.finrank ℂ (S → Fin r → ℂ)
  let L : (S → Fin r → ℂ) ≃L[ℂ] EuclideanSpace ℂ (Fin m) :=
    (LinearEquiv.ofFinrankEq _ _ finrank_euclideanSpace_fin.symm).toContinuousLinearEquiv
  let ιE : UnderlyingSpace ℂ (totalSpace E) → EuclideanSpace ℂ (Fin m) := fun p ↦
    L (bundleEmbedding (𝕜 := ℂ) t ρ ((totalSpaceEquiv E r).symm p))
  let Φ : Chart E r → UnderlyingSpace ℂ Y → (Fin r → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin m) :=
    fun c y ↦ LinearMap.toContinuousLinearMap ((L : (S → Fin r → ℂ) →ₗ[ℂ] _) ∘ₗ
      bundleEmbeddingL (𝕜 := ℂ) t ρ y ∘ₗ (chartTrivialization c).symmₗ ℂ y)
  have hcont : Continuous ιE :=
    L.continuous.comp ((continuous_bundleEmbedding hρ).comp
      (totalSpaceHomeomorph E r).symm.continuous)
  have hpt : ∀ (c : Chart E r) (y : UnderlyingSpace ℂ Y) (hy : ⊤ ≤ y.toHom ⁻¹ᵁ c.1.1)
      (w : Fin r → ℂ), ιE (chartInv c y hy w) = Φ c y w := by
    intro c y hy w
    have h1 : (totalSpaceEquiv E r).symm (chartInv c y hy w) = ⟨y, fibreChartInv c y hy w⟩ :=
      (totalSpaceEquiv E r).symm_apply_eq.2 rfl
    change L (bundleEmbedding (𝕜 := ℂ) t ρ ((totalSpaceEquiv E r).symm _)) = _
    rw [h1, bundleEmbedding_mk hρ]
    change _ = L (bundleEmbeddingL (𝕜 := ℂ) t ρ y ((chartTrivialization c).symmₗ ℂ y w))
    rw [Trivialization.symmₗ_apply _ (show y ∈ (chartTrivialization c).baseSet from hy),
      symm_chartTrivialization c hy]
  have hinj : ∀ (c : Chart E r) (y : UnderlyingSpace ℂ Y), y ∈ chartBase c →
      Function.Injective (Φ c y) := by
    intro c y hy
    have h2 : Function.Injective ((chartTrivialization c).symmₗ ℂ y) :=
      Function.LeftInverse.injective (g := (chartTrivialization c).linearMapAt ℂ y)
        fun w ↦ (chartTrivialization c).linearMapAt_symmₗ hy w
    intro a b hab
    simp only [Φ, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_comp,
      Function.comp_apply] at hab
    exact h2 (injective_bundleEmbeddingL hρ y (L.injective hab))
  clear_value ιE Φ
  have hco : ∀ c : Chart E r, ContinuousOn (Φ c) (chartBase c) := by
    intro c
    refine continuousOn_clm_apply.2 fun w ↦ ?_
    rw [continuousOn_iff_continuous_restrict]
    have h2 : Continuous fun y : {x : UnderlyingSpace ℂ Y // ⊤ ≤ x.toHom ⁻¹ᵁ c.1.1} ↦ (y, w) :=
      continuous_id.prodMk continuous_const
    have this := hcont.comp ((continuous_chartInv c).comp h2)
    simp only [Function.comp_def] at this
    exact this.congr fun y ↦ hpt c y.1 y.2 w
  exact ⟨m, ιE, Φ, hcont, hpt, hinj, hco⟩

end MMP.Modules
