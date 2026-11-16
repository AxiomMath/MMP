/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Basic
public import MMP.AlgebraicGeometry.Intersection.CurveDegreeProjection
public import StacksFrontier.AlgebraicGeometry.Variety.Frobenius.RelativeFrobeniusDegree
public import StacksFrontier.AlgebraicGeometry.FunctionField.DominantMap
public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent
public import StacksFrontier.AlgebraicGeometry.CoherentPushforwardCriteria.ClosureSubscheme

/-!
# Push-forward of 1-cycles and numerical classes

Let `f : X ⟶ Y` be a morphism of proper varieties over a field `k`. The push-forward of 1-cycles
`f_*[C] = [k(C) : k(f(C))] · [f(C)]` (or `0` when `f(C)` is a point) satisfies the *projection
formula* `(M · f_* z) = (f^* M · z)` for every real 1-cycle `z` on `X` and every Cartier divisor
(indeed every invertible sheaf) `M` on `Y`. Consequently numerically trivial cycles push forward
to numerically trivial cycles, so `f_*` descends to a unique linear map
`f_* : N₁(X) ⟶ N₁(Y)` with `f_*[z] = [f_* z]`. This map carries the cone of curves `NE(X)` into
`NE(Y)`, and, being continuous for the numerical topologies, the closed cone `NE̅(X)` into
`NE̅(Y)`.

## Main results

* `MMP.Mori.ProperCurve.degree_pushforward_eq_degree_pullback`: the projection formula for one
  curve, `deg_{f_*[C]} L = deg_C f^* L`.
* `MMP.Mori.OneCycle.degree_pushforward`: the projection formula `(L · f_* z) = (f^* L · z)` for
  invertible sheaves `L` on `Y`.
* `MMP.Mori.OneCycle.intersectionNumber_pushforward_ofCartier`: the projection formula
  `(M · f_* z) = (f^* M · z)` for Cartier divisors `M` on `Y`.
* `MMP.Mori.existsUnique_isNumericalPushforward`: there is exactly one push-forward
  `f_* : N₁(X) ⟶ N₁(Y)` for `f`.
* `MMP.Mori.image_coneOfCurves_subset`: `f_* NE(X) ⊆ NE(Y)`.
* `MMP.Mori.image_closedConeOfCurves_subset`: `f_* NE̅(X) ⊆ NE̅(Y)`.

## Implementation notes

As in `MMP.Foundations.Mori.Cycles`, intersection numbers of 1-cycles are degrees of invertible
sheaves along curves, and `(f^* M · C)` is the degree on `C` of the invertible sheaf
`f^* 𝒪_Y(M)`, since `f^* M` need not be defined as a divisor when `f` contracts curves
([KM, Notation 0.4(5)]). The intersection number of a 1-cycle with a Cartier divisor `M` is
`MMP.Mori.OneCycle.intersectionNumber` of `MMP.Mori.KCartierDivisor.ofCartier ℝ M`, whose value
is the degree of `𝒪_Y(M)`.

The statements need less than the source's hypotheses: `Y` is only assumed separated and locally
of finite type over `k`, and `X` is an arbitrary `k`-scheme (its proper curves are the ones
entering 1-cycles); a proper variety satisfies these. The continuity of `f_*` is proved directly
from the definition of the numerical topology (each `z ↦ (L · f_* z)` is `z ↦ (f^* L · z)`), so
no finite-dimensionality of `N₁` is needed.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Proposition 3.27
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace MMP.Mori

variable {k : Type u} [Field k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  {sY : Y ⟶ Spec (.of k)} (f : X ⟶ Y)

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-! ### The projection formula for one curve -/

/-- A proper curve, the reduced closed subscheme on the closure of a point, is integral. -/
instance ProperCurve.isIntegral_scheme (C : ProperCurve sX) : IsIntegral C.scheme :=
  Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure C.point

/-- The degree of an invertible sheaf along the reduced closed subscheme of an ideal sheaf depends
only on the ideal sheaf. -/
theorem degreeOn_subschemeι_congr {I J : Y.IdealSheafData} (h : I = J)
    [IsProper (I.subschemeι ≫ sY)] [IsProper (J.subschemeι ≫ sY)]
    (hI : topologicalKrullDim I.subscheme ≤ 1) (hJ : topologicalKrullDim J.subscheme ≤ 1)
    (L : Y.Modules) [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L] :
    degreeOn k sY I.subschemeι hI L = degreeOn k sY J.subschemeι hJ L := by
  subst h
  rfl

/-- The closed immersion of a proper curve carries its generic point to the point recording the
curve. -/
theorem ProperCurve.ι_genericPoint (C : ProperCurve sX) :
    C.ι (genericPoint C.scheme) = C.point :=
  Scheme.IdealSheafData.subschemeι_genericPoint_vanishingIdeal_closure C.point

/-- The range of the closed immersion `curveSubschemeAtι y` is the closure of `{y}`. -/
theorem range_curveSubschemeAtι (y : Y) : Set.range (curveSubschemeAtι y) = closure {y} := by
  unfold curveSubschemeAtι
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl

/-- The underlying set of a proper curve `C ⊆ X` is the closure of its generic point. -/
theorem ProperCurve.range_ι (C : ProperCurve sX) : Set.range C.ι = closure {C.point} :=
  range_curveSubschemeAtι C.point

/-- The closure of the image `f(C)` of a proper curve `C ⊆ X` is the closure of the image of its
generic point. -/
theorem ProperCurve.closure_range_comp (C : ProperCurve sX) :
    closure (Set.range (C.ι ≫ f)) = closure {f C.point} := by
  apply le_antisymm
  · refine closure_minimal ?_ isClosed_closure
    rintro _ ⟨c, rfl⟩
    have hc : C.ι c ∈ closure {C.point} := C.range_ι ▸ ⟨c, rfl⟩
    have := image_closure_subset_closure_image f.continuous ⟨_, hc, rfl⟩
    rwa [Set.image_singleton] at this
  · refine closure_mono ?_
    rintro _ rfl
    exact ⟨genericPoint C.scheme, by rw [Scheme.Hom.comp_apply, C.ι_genericPoint]⟩

/-! ### Push-forward of the cone of curves -/

/-- The class of the push-forward `g_*[{x}⁻]` of the closure of a point lies in `NE(Y)`: it is `0`
or a nonnegative multiple of the class of the curve `{g(x)}⁻`. -/
theorem numericalClass_cyclePushforwardOfPoint_mem_coneOfCurves (g : X ⟶ Y) (x : X) :
    OneCycle.numericalClass sY (cyclePushforwardOfPoint ℝ sY g x) ∈ coneOfCurves sY := by
  unfold cyclePushforwardOfPoint
  split_ifs with h
  · have hd : (Finsupp.single (⟨g x, h⟩ : ProperCurve sY) (residueFieldDegree g x : ℝ) :
        OneCycle ℝ sY) = (residueFieldDegree g x : ℝ) • (⟨g x, h⟩ : ProperCurve sY).cycle ℝ := by
      rw [ProperCurve.cycle, Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hd, map_smul]
    exact Submodule.smul_mem (coneOfCurves sY)
      (⟨(residueFieldDegree g x : ℝ), Nat.cast_nonneg _⟩ : {r : ℝ // 0 ≤ r})
      (numericalClass_cycle_mem_coneOfCurves sY ⟨g x, h⟩)
  · rw [map_zero]
    exact zero_mem _

/-- **KM Proposition 3.27(2), first part.** Let `f : X ⟶ Y` be a morphism of `k`-schemes and
`φ : N₁(X) ⟶ N₁(Y)` a push-forward for `f`. Then `φ(NE(X)) ⊆ NE(Y)`. -/
@[mmp "lem_km3b_pushforward_cone"]
theorem image_coneOfCurves_subset
    {φ : NumericalCurveClasses sX →ₗ[ℝ] NumericalCurveClasses sY}
    (hφ : IsNumericalPushforward sY f φ) :
    φ '' (coneOfCurves sX : Set (NumericalCurveClasses sX)) ⊆ coneOfCurves sY := by
  rintro _ ⟨z, hz, rfl⟩
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨C, rfl⟩ := hx
    rw [hφ, OneCycle.pushforward_cycle]
    exact numericalClass_cyclePushforwardOfPoint_mem_coneOfCurves f C.point
  | zero =>
    rw [map_zero]
    exact zero_mem _
  | add x y _ _ hx hy =>
    rw [map_add]
    exact add_mem hx hy
  | smul c x _ hx =>
    change φ ((c : ℝ) • x) ∈ coneOfCurves sY
    rw [map_smul]
    exact Submodule.smul_mem _ c hx

section Curve

variable [IsSeparated sY] [LocallyOfFiniteType sY]

/-- A proper curve `C ⊆ X` with the induced `k`-structure is a curve over `k`. -/
theorem ProperCurve.isCurve (C : ProperCurve sX) : IsCurve k (C.ι ≫ sX) :=
  { toIsIntegral := inferInstance
    toIsSeparated := inferInstance
    toLocallyOfFiniteType := inferInstance
    toQuasiCompact := inferInstance
    topologicalKrullDim_eq_one := C.dim_eq }

/-- The image `f(C)` of a proper curve `C ⊆ X` under a `k`-morphism to a separated `k`-scheme is
the closure of the image of its generic point. -/
theorem ProperCurve.range_comp (hf : f ≫ sY = sX) (C : ProperCurve sX) :
    Set.range (C.ι ≫ f) = closure {f C.point} := by
  have : IsProper ((C.ι ≫ f) ≫ sY) := by rw [Category.assoc, hf]; infer_instance
  have : IsProper (C.ι ≫ f) := IsProper.of_comp _ sY
  rw [← C.closure_range_comp f, (C.ι ≫ f).isClosedMap.isClosed_range.closure_eq]

/-- The scheme-theoretic image of a proper curve `C ⊆ X` under `f` is the reduced closure of the
image of its generic point. -/
theorem ProperCurve.ker_comp (C : ProperCurve sX) :
    (C.ι ≫ f).ker = Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {f C.point}) := by
  rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range]
  congr 1
  exact Closeds.ext (by rw [Closeds.coe_closure, Closeds.coe_closure, C.closure_range_comp f])

/-- **The projection formula for one curve.** Let `f : X ⟶ Y` be a `k`-morphism to a separated
`k`-scheme locally of finite type, `C ⊆ X` a proper curve and `L` an invertible sheaf on `Y`. Then
the degree of `L` on the push-forward `f_*[C]` (which is `[k(C) : k(f(C))] · [f(C)]` or `0`) is
the degree of `f^* L` on `C`. -/
theorem ProperCurve.degree_pushforward_eq_degree_pullback (hf : f ≫ sY = sX)
    (C : ProperCurve sX) (L : Y.Modules)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L] :
    OneCycle.degree ℝ sY L (cyclePushforwardOfPoint ℝ sY f C.point) =
      (C.degree k ((Scheme.Modules.pullback f).obj L) : ℝ) := by
  set φ := C.ι ≫ f with hφdef
  have hφ : φ ≫ sY = C.ι ≫ sX := by rw [hφdef, Category.assoc, hf]
  have : IsProper (φ ≫ sY) := hφ ▸ inferInstance
  have : IsProper φ := IsProper.of_comp _ sY
  have := C.isCurve
  have : IsCurve k (φ ≫ sY) := hφ ▸ inferInstance
  have hL : C.degree k ((Scheme.Modules.pullback f).obj L) =
      degreeOn k sY φ (IsCurve.topologicalKrullDim_eq_one (f := φ ≫ sY)).le L :=
    degreeOn_pullback_eq_degreeOn_comp sX sY f C.ι hf C.dim_le L
  rw [hL]
  by_cases hpt : ∃ y : Y, Set.range φ = {y}
  · rw [degreeOn_eq_zero_of_range_eq_singleton sY φ L hpt]
    have hnot : ¬ IsProperCurve sY (f C.point) := by
      intro h
      obtain ⟨y, hy⟩ := hpt
      have hr : ∀ t, curveSubschemeAtι (f C.point) t = y := fun t => by
        have ht : curveSubschemeAtι (f C.point) t ∈ closure {f C.point} :=
          range_curveSubschemeAtι (f C.point) ▸ ⟨t, rfl⟩
        rw [← C.range_comp f hf, ← hφdef, hy] at ht
        exact ht
      have : Subsingleton (curveSubschemeAt (f C.point)) :=
        ⟨fun a b => (curveSubschemeAtι (f C.point)).isEmbedding.injective ((hr a).trans (hr b).symm)⟩
      have h1 := h.dim_eq
      have h0 : topologicalKrullDim (curveSubschemeAt (f C.point)) ≤ 0 := by
        have : DiscreteTopology (curveSubschemeAt (f C.point)) := inferInstance
        exact topologicalKrullDim_zero_of_discreteTopology _
      rw [h1] at h0
      norm_num at h0
    simp [cyclePushforwardOfPoint, hnot]
  · have hcurve := isCurve_imageι_comp sY φ hpt
    have hker := C.ker_comp f
    rw [← hφdef] at hker
    have hdim : topologicalKrullDim (curveSubschemeAt (f C.point)) = 1 := by
      have h1 := hcurve.topologicalKrullDim_eq_one
      change topologicalKrullDim φ.ker.subscheme = 1 at h1
      rwa [hker] at h1
    have hprop : IsProper (curveSubschemeAtι (f C.point) ≫ sY) := by
      have h1 : IsProper (φ.imageι ≫ sY) := isProper_imageι_comp φ sY
      change IsProper (φ.ker.subschemeι ≫ sY) at h1
      rwa [hker] at h1
    have hC' : IsProperCurve sY (f C.point) := ⟨hdim, hprop⟩
    have : IsProper (φ.imageι ≫ sY) := isProper_imageι_comp φ sY
    rw [degreeOn_eq_degreeOver_mul sY φ L hpt]
    simp only [cyclePushforwardOfPoint, dif_pos hC', OneCycle.degree,
      Finsupp.linearCombination_single, smul_eq_mul]
    have hdeg : residueFieldDegree f C.point = degreeOver φ.toImage := by
      have h1 := residueDegree_comp C.ι f (genericPoint C.scheme)
      rw [C.ι_genericPoint, Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion C.ι, mul_one]
        at h1
      have h2 := residueDegree_comp φ.toImage φ.imageι (genericPoint C.scheme)
      rw [Scheme.Hom.toImage_imageι,
        Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion φ.imageι,
        one_mul, residueDegree_genericPoint_eq_degreeOver φ.toImage] at h2
      exact h1.symm.trans h2
    have hdeg' : (⟨f C.point, hC'⟩ : ProperCurve sY).degree k L =
        degreeOn k sY φ.imageι (topologicalKrullDim_image_le_one sY φ) L :=
      degreeOn_subschemeι_congr hker.symm _ _ L
    rw [hdeg', hdeg]
    push_cast
    rfl

/-! ### The projection formula -/

/-- **The projection formula for 1-cycles.** Let `f : X ⟶ Y` be a `k`-morphism to a separated
`k`-scheme locally of finite type (for instance a morphism of proper varieties), `z` a real
1-cycle on `X` and `L` an invertible sheaf on `Y` (for instance `𝒪_Y(M)` for a Cartier divisor
`M`). Then `(L · f_* z) = (f^* L · z)`. -/
@[mmp "lem_km3b_pushforward_projection_formula"]
theorem OneCycle.degree_pushforward (hf : f ≫ sY = sX) (L : Y.Modules)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L] (z : OneCycle ℝ sX) :
    OneCycle.degree ℝ sY L (OneCycle.pushforward ℝ sX sY f z) =
      OneCycle.degree ℝ sX ((Scheme.Modules.pullback f).obj L) z := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => simp only [map_add, hz, hw]
  | single C r =>
    rw [OneCycle.pushforward, Finsupp.linearCombination_single, map_smul,
      C.degree_pushforward_eq_degree_pullback f hf L, OneCycle.degree_apply,
      Finsupp.sum_single_index (by simp), smul_eq_mul]

/-- **The projection formula for 1-cycles and Cartier divisors.** Let `f : X ⟶ Y` be a `k`-morphism
to a separated `k`-scheme locally of finite type (for instance a morphism of proper varieties),
`z` a real 1-cycle on `X` and `M` a Cartier divisor on `Y`. Then `(M · f_* z) = (f^* M · z)`, where
`(f^* M · z)` is the degree on `z` of the invertible sheaf `f^* 𝒪_Y(M)`. -/
@[mmp "lem_km3b_pushforward_projection_formula"]
theorem OneCycle.intersectionNumber_pushforward_ofCartier (hf : f ≫ sY = sX)
    (M : Y.CartierDivisor) (z : OneCycle ℝ sX) :
    (OneCycle.pushforward ℝ sX sY f z).intersectionNumber (KCartierDivisor.ofCartier ℝ M) =
      OneCycle.degree ℝ sX
        ((Scheme.Modules.pullback f).obj (MMP.CartierDivisor.sheaf M)) z := by
  rw [OneCycle.intersectionNumber_ofCartier, OneCycle.cartierDegree,
    OneCycle.degree_pushforward f hf]

/-! ### Push-forward of numerical classes -/

/-- A numerically trivial real 1-cycle pushes forward to a numerically trivial 1-cycle. -/
theorem OneCycle.pushforward_mem_numericallyTrivial (hf : f ≫ sY = sX) {z : OneCycle ℝ sX}
    (hz : z ∈ OneCycle.numericallyTrivial sX) :
    OneCycle.pushforward ℝ sX sY f z ∈ OneCycle.numericallyTrivial sY := by
  rw [OneCycle.mem_numericallyTrivial]
  intro L _
  rw [OneCycle.degree_pushforward f hf]
  exact OneCycle.mem_numericallyTrivial.mp hz _

/-- The push-forward `f_* : N₁(X) ⟶ N₁(Y)`, `[z] ↦ [f_* z]`, of a `k`-morphism `f` to a
separated `k`-scheme locally of finite type. -/
def NumericalCurveClasses.pushforward (hf : f ≫ sY = sX) :
    NumericalCurveClasses sX →ₗ[ℝ] NumericalCurveClasses sY :=
  (OneCycle.numericallyTrivial sX).liftQ
    ((OneCycle.numericalClass sY).comp (OneCycle.pushforward ℝ sX sY f)) fun _ hz => by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, OneCycle.numericalClass, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      exact OneCycle.pushforward_mem_numericallyTrivial f hf hz

/-- `f_*` sends the class of a 1-cycle `z` to the class of `f_* z`. -/
@[simp]
theorem NumericalCurveClasses.pushforward_numericalClass (hf : f ≫ sY = sX)
    (z : OneCycle ℝ sX) :
    NumericalCurveClasses.pushforward f hf (OneCycle.numericalClass sX z) =
      OneCycle.numericalClass sY (OneCycle.pushforward ℝ sX sY f z) :=
  rfl

/-- `NumericalCurveClasses.pushforward f` is a push-forward for `f`. -/
theorem NumericalCurveClasses.isNumericalPushforward_pushforward (hf : f ≫ sY = sX) :
    IsNumericalPushforward sY f (NumericalCurveClasses.pushforward f hf) :=
  fun _ => rfl

/-- **KM Proposition 3.27(1).** Let `f : X ⟶ Y` be a `k`-morphism to a separated `k`-scheme
locally of finite type (for instance a morphism of proper varieties). There is exactly one
push-forward `f_* : N₁(X) ⟶ N₁(Y)` for `f`, that is, exactly one linear map with
`f_*[z] = [f_* z]` for every real 1-cycle `z`. -/
@[mmp "lem_km3b_pushforward_numerical"]
theorem existsUnique_isNumericalPushforward (hf : f ≫ sY = sX) :
    ∃! φ : NumericalCurveClasses sX →ₗ[ℝ] NumericalCurveClasses sY,
      IsNumericalPushforward sY f φ :=
  ⟨_, NumericalCurveClasses.isNumericalPushforward_pushforward f hf, fun _ hψ =>
    Submodule.linearMap_qext _ (LinearMap.ext hψ)⟩

/-- The projection formula on `N₁`: `(L · f_* z) = (f^* L · z)` for a numerical class `z`. -/
theorem NumericalCurveClasses.degree_pushforward (hf : f ≫ sY = sX) (L : Y.Modules)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L]
    (z : NumericalCurveClasses sX) :
    NumericalCurveClasses.degree sY L (NumericalCurveClasses.pushforward f hf z) =
      NumericalCurveClasses.degree sX ((Scheme.Modules.pullback f).obj L) z := by
  obtain ⟨z, rfl⟩ := OneCycle.numericalClass_surjective sX z
  exact OneCycle.degree_pushforward f hf L z

/-- The push-forward `f_* : N₁(X) ⟶ N₁(Y)` is continuous for the numerical topologies. -/
theorem NumericalCurveClasses.continuous_pushforward (hf : f ≫ sY = sX) :
    Continuous (NumericalCurveClasses.pushforward f hf) := by
  refine continuous_iInf_rng.2 fun L => continuous_iInf_rng.2 fun h =>
    continuous_induced_rng.2 ?_
  have := h
  have he : ⇑(NumericalCurveClasses.degree sY L) ∘ ⇑(NumericalCurveClasses.pushforward f hf) =
      NumericalCurveClasses.degree sX ((Scheme.Modules.pullback f).obj L) :=
    funext (NumericalCurveClasses.degree_pushforward f hf L)
  rw [he]
  exact NumericalCurveClasses.continuous_degree sX _

/-- **KM Proposition 3.27(2), second part.** Let `f : X ⟶ Y` be a `k`-morphism to a separated
`k`-scheme locally of finite type (for instance a morphism of proper varieties) and
`φ : N₁(X) ⟶ N₁(Y)` the push-forward for `f`. Then `φ(NE̅(X)) ⊆ NE̅(Y)`. -/
@[mmp "lem_km3b_pushforward_closed_cone"]
theorem image_closedConeOfCurves_subset (hf : f ≫ sY = sX)
    {φ : NumericalCurveClasses sX →ₗ[ℝ] NumericalCurveClasses sY}
    (hφ : IsNumericalPushforward sY f φ) :
    φ '' (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) ⊆ closedConeOfCurves sY := by
  have hφeq : φ = NumericalCurveClasses.pushforward f hf :=
    (existsUnique_isNumericalPushforward f hf).unique hφ
      (NumericalCurveClasses.isNumericalPushforward_pushforward f hf)
  have hc : Continuous φ := hφeq ▸ NumericalCurveClasses.continuous_pushforward f hf
  rw [coe_closedConeOfCurves, coe_closedConeOfCurves]
  exact (image_closure_subset_closure_image hc).trans (closure_mono (image_coneOfCurves_subset f hφ))

end Curve

end MMP.Mori
