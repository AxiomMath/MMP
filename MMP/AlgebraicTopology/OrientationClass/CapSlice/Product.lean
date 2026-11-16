module

public import MMP.AlgebraicTopology.OrientationClass.CapSlice.Orientation
public import MMP.AlgebraicTopology.OrientationClass.CapDeformation
public import MMP.AlgebraicTopology.OrientationClass.CapProductPointClass

/-!
# The product fundamental class on the slice core (Fulton, §19.1)

For a fundamental class `μ_U` of `U` (complex orientation of the model `E'`) and `μ_F` of `F`
(complex orientation), the restriction of `μ_U × μ_F` to `Ω = U × ball(0, 1/2)`, put in degree
`2 dim E` when `dim E' + dim F = dim E`, is a fundamental class of `Ω` for the complex
orientation `complexRealBasis c` of `E' × F`, `c` the product of the complex bases of `E'`
and `F`.

## Main results

* `MMP.IsFundamentalClass.congrDegree_reindex`: fundamental classes under a change of the name of
  the dimension.
* `MMP.complexRealBasis_reindex_finCongr`: the real basis of a reindexed complex basis is the
  reindexed real basis.
* `MMP.IsFundamentalClass.restrict_sliceCore_exteriorProduct`: the restriction of `μ_U × μ_F` to
  `Ω` is a fundamental class of `Ω`.
* `MMP.hasProperNeighbourhoodDeformations_sliceCore_zero`: the slice `Ω ∩ (U × {0})` has
  arbitrarily small proper neighbourhood deformations in `Ω`.
-/

@[expose] public noncomputable section

open Set Topology Manifold

universe u

namespace MMP

open FundamentalClass BorelMooreCross

/-- A fundamental class in dimension `n` is a fundamental class in any dimension `n' = n`, for
the reindexed basis. -/
theorem IsFundamentalClass.congrDegree_reindex {R : Type u} [CommRing R] {H : Type*}
    [AddCommGroup H] [Module ℝ H] [TopologicalSpace H] [ContinuousAdd H] [ContinuousSMul ℝ H]
    {M : Type u} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] {n n' : ℕ} (h : n = n')
    {b : Module.Basis (Fin n) ℝ H} {μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of M) n}
    (hμ : IsFundamentalClass R b μ) :
    IsFundamentalClass R (b.reindex (finCongr h))
      (congrDegree R _ (congrArg Nat.cast h) μ) := by
  subst h
  rw [congrDegree_self]
  simpa using hμ

/-- For `h : r = r'`, the real basis `complexRealBasis` of the complex basis `c` reindexed along
`finCongr h` is `complexRealBasis c` reindexed along `finCongr` of `2 * r = 2 * r'`. -/
lemma complexRealBasis_reindex_finCongr {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {r r' : ℕ} (h : r = r') (c : Module.Basis (Fin r) ℂ V) :
    complexRealBasis (c.reindex (finCongr h)) =
      (complexRealBasis c).reindex (finCongr (congrArg (2 * ·) h)) := by
  subst h
  simp

variable (R : Type u) [CommRing R]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] [FiniteDimensional ℂ E']
  {F : Type u} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  {U : Type u} [TopologicalSpace U] [T2Space U] [ChartedSpace E' U]

/-- The complex basis of `E' × F` whose real basis orients the slice core: the product of the
standard complex bases of `E'` and `F`, indexed by `Fin d` for `dim E' + dim F = d`. -/
def sliceCoreBasis {d : ℕ} (hd : Module.finrank ℂ E' + Module.finrank ℂ F = d) :
    Module.Basis (Fin d) ℂ (E' × F) :=
  (((Module.finBasis ℂ E').prod (Module.finBasis ℂ F)).reindex finSumFinEquiv).reindex
    (finCongr hd)

/-- **The product fundamental class on the slice core.** For fundamental classes `μ_U` of `U`
and `μ_F` of `F` (complex orientations) and `dim E' + dim F = d`, the restriction of
`μ_U × μ_F` to `Ω = U × ball(0, 1/2)`, in degree `2 d`, is a fundamental class of `Ω` for the
complex orientation `complexRealBasis (sliceCoreBasis hd)` of `E' × F`. -/
theorem IsFundamentalClass.restrict_sliceCore_exteriorProduct {d : ℕ}
    (hd : Module.finrank ℂ E' + Module.finrank ℂ F = d)
    {μU : borelMooreHomology R (ModuleCat.of R R) (TopCat.of U) (2 * Module.finrank ℂ E' : ℕ)}
    (hμU : IsFundamentalClass R (complexOrientationBasisOf E') μU)
    {μF : borelMooreHomology R (ModuleCat.of R R) (TopCat.of F) (2 * Module.finrank ℂ F : ℕ)}
    (hμF : IsFundamentalClass R (complexOrientationBasisOf F) μF) :
    IsFundamentalClass (H := ModelProd E' F) R
      (complexRealBasis (sliceCoreBasis hd) : Module.Basis _ ℝ (E' × F))
      (borelMooreHomology.restrict R (ModuleCat.of R R) (Y := TopCat.of (U × F)) (sliceCore U F)
        (2 * d : ℕ)
        (congrDegree R _ (congrArg Nat.cast (show 2 * Module.finrank ℂ E' +
            2 * Module.finrank ℂ F = 2 * d by omega))
          (congrDegree R _ (Nat.cast_add _ _).symm
            (borelMooreHomology.exteriorProduct R (TopCat.of U) (TopCat.of F)
              (2 * Module.finrank ℂ E' : ℕ) (2 * Module.finrank ℂ F : ℕ) (μU ⊗ₜ μF))))) := by
  have h := (hμU.exteriorProduct R hμF).congrDegree_reindex
    (show 2 * Module.finrank ℂ E' + 2 * Module.finrank ℂ F = 2 * d by omega)
  have hb : (((complexOrientationBasisOf E').prod (complexOrientationBasisOf F)).reindex
      finSumFinEquiv).reindex (finCongr (show 2 * Module.finrank ℂ E' +
        2 * Module.finrank ℂ F = 2 * d by omega)) =
      complexRealBasis (sliceCoreBasis hd) := by
    rw [complexOrientationBasisOf_eq_complexRealBasis, complexOrientationBasisOf_eq_complexRealBasis,
      prod_complexRealBasis, sliceCoreBasis, complexRealBasis_reindex_finCongr]
    refine Module.Basis.eq_of_apply_eq fun i ↦ ?_
    simp only [Module.Basis.reindex_apply]
    rfl
  rw [hb] at h
  exact h.restrict (sliceCore U F)

section Deformation

variable (U : Type u) [TopologicalSpace U] (F : Type u) [NormedAddCommGroup F]

/-- The ball `ball(0, 1/2)` of `F`, as an open set. -/
def sliceBall : TopologicalSpace.Opens F := ⟨Metric.ball 0 (1 / 2), Metric.isOpen_ball⟩

/-- The homeomorphism `Ω = U × ball(0, 1/2) ≅ U × ball(0, 1/2)` from the open set of `U × F` to
the product. -/
def sliceCoreProdHomeomorph : sliceCore U F ≃ₜ U × sliceBall F where
  toFun p := ((p : U × F).1, ⟨(p : U × F).2, mem_ball_zero_iff.2 p.2⟩)
  invFun q := ⟨(q.1, (q.2 : F)), show ‖(q.2 : F)‖ < 1 / 2 from mem_ball_zero_iff.1 q.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_fst.comp continuous_subtype_val).prodMk
    ((continuous_snd.comp continuous_subtype_val).subtype_mk _)
  continuous_invFun := (continuous_fst.prodMk
    (continuous_subtype_val.comp continuous_snd)).subtype_mk _

/-- For `U` metrizable, the slice `Ω ∩ (U × {0})` has arbitrarily small proper neighbourhood
deformations in `Ω = U × ball(0, 1/2)`. -/
theorem hasProperNeighbourhoodDeformations_sliceCore_zero [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace.MetrizableSpace U] :
    HasProperNeighbourhoodDeformations {p : sliceCore U F | (p : U × F).2 = 0} := by
  have h := (borelMooreHomology.hasProperNeighbourhoodDeformations_prodSnd_preimage_singleton
    (TopCat.of U)
    (T := TopCat.of (sliceBall F)) F
    (⟨0, Metric.mem_ball_self (by norm_num)⟩ : sliceBall F)).preimage_homeomorph
    (sliceCoreProdHomeomorph U F)
  convert h using 1
  ext p
  simp only [mem_setOf_eq, mem_preimage, mem_singleton_iff]
  constructor
  · intro hp
    exact Subtype.ext hp
  · intro hp
    exact congrArg Subtype.val hp

end Deformation

end MMP
