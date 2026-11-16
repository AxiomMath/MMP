module

public import MMP.AlgebraicTopology.SingularHomology.ShuffleSumCornerPath
public import MMP.AlgebraicTopology.SingularHomology.CrossProduct
public import MMP.AlgebraicTopology.BorelMoore.ExteriorProductNatural

/-!
# The shuffle sum against a point

The shuffle sum `∇_{p,0}` is the single path `(0, 0), (1, 0), …, (p, 0)` (the corner path of
`[p] × [0]`) with coefficient `1`: the cross product of a `p`-simplex with a `0`-simplex is one
simplex. Consequently, for the slice inclusion `ι : Y → Y × {pt}`, `μ × [pt] = ι_* μ`, on
simplices, on locally finite chains and on Borel–Moore homology.

## Main definitions

* `SingularCross.sliceSimplex`: the slice simplex `t ↦ (σ t, y)` of `X × Y`.

## Main results

* `LatticePath.shuffleSum_self_cornerPath_zero`: `∇_{p,0}` is the single corner path.
* `SingularCross.crossSimplex_zero_right`: the cross product with a `0`-simplex `τ` is the slice
  simplex at the point of `τ`.
* `BorelMooreCross.crossChain_eq_chainMap_slice`: the cross product of a locally finite chain
  with a single point is its push-forward along the slice.
* `borelMooreHomology.exteriorProduct_tmul_pointCycle`: `a × [τ] = s_* a`, where `s x = (x, τ)`.
-/

@[expose] public section

namespace MMP

namespace LatticePath

/-- `∇_{p,0}` is the single path `(0, 0), …, (p, 0)`. -/
lemma shuffleSum_self_cornerPath_zero (p : ℕ) :
    shuffleSum p p 0 = Finsupp.single (cornerPath p 0) 1 := by
  induction p with
  | zero => simp [shuffleSum, sndPath]
  | succ p ih =>
    rw [shuffleSum_succ, lowerFst_succ, lowerSnd_zero, ih]
    simp [lmap]

end LatticePath

namespace SingularCross

open CategoryTheory Opposite Simplicial LatticePath

universe u

variable {X Y : TopCat.{u}}

/-- The slice simplex `t ↦ (σ t, y)` of `X × Y`. -/
noncomputable def sliceSimplex {p : ℕ} (σ : Simp X p) (y : Y) : Simp (TopCat.of (X × Y)) p :=
  (TopCat.toSSetObjEquiv (TopCat.of (X × Y)) (op ⦋p⦌)).symm
    ((toC σ).prodMk (ContinuousMap.const _ y))

/-- The underlying map of `sliceSimplex σ y` is `t ↦ (σ t, y)`. -/
lemma toC_sliceSimplex {p : ℕ} (σ : Simp X p) (y : Y) :
    toC (sliceSimplex σ y) = (toC σ).prodMk (ContinuousMap.const _ y) :=
  Equiv.apply_symm_apply _ _

/-- The affine map of standard simplices induced by the first coordinates of the corner path of
`[p] × [0]` is the identity. -/
lemma vtxMap_cornerPath_zero (p : ℕ) :
    vtxMap p p (fun j ↦ ((cornerPath p 0).getD j (0, 0)).1) = ContinuousMap.id _ := by
  ext1 t
  change Convexity.StdSimplex.map _ t = t
  have : vtx p p (fun j ↦ ((cornerPath p 0).getD j (0, 0)).1) = id := by
    funext j
    ext
    simp only [vtx, id]
    rw [getD_cornerPath p 0 (by simpa using j.isLt)]
    simp [Nat.le_of_lt_succ j.isLt]
  rw [this, Convexity.StdSimplex.map_id]

/-- **The cross product with a `0`-simplex** `τ` is the slice simplex at the point of `τ`. -/
lemma crossSimplex_zero_right {p : ℕ} (σ : Simp X p) (τ : Simp Y 0) :
    crossSimplex p σ τ = Finsupp.single (sliceSimplex σ (toC τ (Convexity.StdSimplex.single 0))) 1 := by
  rw [crossSimplex, shuffleSum_self_cornerPath_zero, Finsupp.mapDomain_single]
  congr 1
  apply toC_injective
  rw [toC_pathSimplex, vtxMap_cornerPath_zero, toC_sliceSimplex]
  ext1 t
  exact Prod.ext rfl (congrArg (toC τ) (Subsingleton.elim _ _))

end SingularCross

namespace BorelMooreCross

open CategoryTheory Opposite Simplicial SingularCross LocallyFiniteChain

universe u

variable (R : Type u) [CommRing R] {X Y : TopCat.{u}}

/-- For a fixed point `y`, the map `σ ↦ sliceSimplex σ y` is injective. -/
lemma sliceSimplex_injective {p : ℕ} (y : Y) :
    Function.Injective fun σ : Simp X p ↦ sliceSimplex σ y := by
  intro σ σ' h
  apply toC_injective
  ext1 t
  simpa [toC_sliceSimplex] using congrArg Prod.fst (DFunLike.congr_fun (congrArg toC h) t)

/-- **The cross product with a point, on locally finite chains.** For a `0`-chain `d` which is
the single simplex `τ`, `c × d` is the push-forward of `c` along the slice `x ↦ (x, τ)`. -/
lemma crossChain_eq_chainMap_slice {p : ℕ} (s : X ⟶ TopCat.of (X × Y)) (hs : IsProperMap s)
    (τ : Simp Y 0) (hsτ : ∀ x, s x = (x, toC τ (Convexity.StdSimplex.single 0)))
    (c : (BM R X).X p) (d : (BM R Y).X 0) (hd : coeff R d τ = 1)
    (hd₀ : ∀ τ', τ' ≠ τ → coeff R d τ' = 0) :
    crossChain R p p 0 c d =
      ((borelMooreHomology.chainMap R (ModuleCat.of R R) s hs).f p).hom c := by
  classical
  set y := toC τ (Convexity.StdSimplex.single 0)
  have hmap : ∀ σ : Simp X p, (TopCat.toSSet.map s).app (op ⦋p⦌) σ = sliceSimplex σ y := by
    intro σ
    apply toC_injective
    rw [toC_sliceSimplex]
    ext1 t
    exact hsτ _
  apply coeff_injective
  rw [coeff_crossChain, coeff_chainMap_f]
  funext t
  simp only [crossFun, lfTransferFun, crossFamily, lfTensor, pushforwardFun, hmap,
    crossSimplex_zero_right]
  by_cases ht : ∃ σ : Simp X p, sliceSimplex σ y = t
  · obtain ⟨σ, rfl⟩ := ht
    rw [finsum_eq_single _ (σ, τ), finsum_eq_single _ σ]
    · simp [y, hd]
    · intro σ' hσ'
      rw [ite_eq_right fun h ↦ hσ' (sliceSimplex_injective y h)]
    · rintro ⟨σ', τ'⟩ hne
      by_cases hτ : τ' = τ
      · subst hτ
        have : σ' ≠ σ := fun h ↦ hne (by rw [h])
        rw [Finsupp.single_apply, ite_eq_right fun h ↦ this (sliceSimplex_injective y h)]
        simp
      · simp [hd₀ _ hτ]
  · push Not at ht
    rw [finsum_eq_zero_of_forall_eq_zero, finsum_eq_zero_of_forall_eq_zero]
    · intro σ
      rw [ite_eq_right (ht σ)]
    · rintro ⟨σ', τ'⟩
      by_cases hτ : τ' = τ
      · subst hτ
        rw [Finsupp.single_apply, ite_eq_right (ht σ')]
        simp
      · simp [hd₀ _ hτ]

end BorelMooreCross

namespace borelMooreHomology

open CategoryTheory Opposite Simplicial SingularCross BorelMooreCross TensorProduct

universe u

variable (R : Type u) [CommRing R] {X Y : TopCat.{u}}

/-- **The exterior product with the class of a point is the push-forward along the slice.** For
the `0`-cycle `d` of `Y` given by a single `0`-simplex `τ` with coefficient `1`, and the slice
`s : X → X × Y`, `x ↦ (x, τ)`: `a × [d] = s_* a`. -/
theorem exteriorProduct_tmul_pointCycle (s : X ⟶ TopCat.of (X × Y)) (hs : IsProperMap s)
    (τ : Simp Y 0) (hsτ : ∀ x, s x = (x, toC τ (Convexity.StdSimplex.single 0)))
    (d : Cyc (R := R) Y 0) (hd : coeff R d.1 τ = 1) (hd₀ : ∀ τ', τ' ≠ τ → coeff R d.1 τ' = 0)
    (p : ℕ) (a : borelMooreHomology R (ModuleCat.of R R) X p) :
    exteriorProduct R X Y p (0 : ℕ)
        (a ⊗ₜ (homologyEquiv R Y 0).symm (Submodule.Quotient.mk d)) =
      congrDegree R (TopCat.of (X × Y)) (by simp)
        ((pushforward R (ModuleCat.of R R) s hs p).hom a) := by
  have key : ∀ x : HomQ (R := R) X p,
      exteriorProduct R X Y p (0 : ℕ)
        ((homologyEquiv R X p).symm x ⊗ₜ (homologyEquiv R Y 0).symm (Submodule.Quotient.mk d)) =
      congrDegree R (TopCat.of (X × Y)) (by simp)
        ((pushforward R (ModuleCat.of R R) s hs p).hom ((homologyEquiv R X p).symm x)) := by
    intro x
    induction x using Submodule.Quotient.induction_on with | H z => ?_
    rw [exteriorProduct_tmul]
    erw [exteriorProductBilin_natCast R X Y p 0, crossHomQ_mk]
    rw [pushforward_eq_homologyMap]
    erw [homologyMap_homologyEquiv_symm_mk]
    have e : (Submodule.Quotient.mk ⟨crossChain R (p + 0) p 0 z.1 d.1, crossChain_mem_cyc p 0 z d⟩ :
        HomQ (R := R) (TopCat.of (X × Y)) (p + 0)) =
        Submodule.Quotient.mk
          ⟨((borelMooreHomology.chainMap R (ModuleCat.of R R) s hs).f p).hom z.1,
            chainMap_mem_cyc R _ z⟩ :=
      congrArg _ (Subtype.ext (crossChain_eq_chainMap_slice R s hs τ hsτ z.1 d.1 hd hd₀))
    erw [e]
    rfl
  simpa using key (homologyEquiv R X p a)

end borelMooreHomology

end MMP
