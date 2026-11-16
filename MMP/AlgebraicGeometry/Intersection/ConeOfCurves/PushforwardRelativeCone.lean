module

public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Relative
public import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.AlgebraicGeometry.ProjectiveSpace.ProductProjectiveLine

/-!
# Push-forward of relative cones of curves along a surjection

Let `S` be a projective variety over a field `k` and `p : W ⟶ X` a surjective morphism of
projective `k`-varieties over `S`, with structure maps `πW : W ⟶ S` and `πX : X ⟶ S`. A curve on
`W` contracted by `πW` maps to a point or onto a curve contracted by `πX`, so the push-forward of
1-cycles `p_*` carries relative 1-cycles to relative 1-cycles. By the projection formula
`(D · p_* z) = (p^* D · z)` it descends to a linear map `p_* : N₁(W/S) → N₁(X/S)`. Every curve
`C ⊆ X` contracted by `πX` is the image of a curve `Γ ⊆ W`, finite over `C`, so
`p_*[Γ] = d [C]` with `d > 0`; hence `p_*` is surjective, carries `NE(W/S)` onto `NE(X/S)`, and
`NE̅(X/S)` is the closure of `p_* NE̅(W/S)`, which it contains. The same lifting shows that an
`ℝ`-Cartier divisor `D` on `X` is nef over `S` exactly when `p^* D` is nef over `S`.

## Main results

* `MMP.Mori.exists_relativeNumericalPushforward_of_surjective`: the push-forward
  `p_* : N₁(W/S) → N₁(X/S)` exists, is surjective, maps `NE(W/S)` onto `NE(X/S)` and `NE̅(W/S)`
  into `NE̅(X/S) = closure (p_* NE̅(W/S))`, and nefness over `S` is detected by pull-back.

## Implementation notes

The push-forward is pinned by its value on classes: `p_*[Z] = [Z']` whenever the relative
1-cycle `Z'` on `X` is the push-forward `p_* Z` of the relative 1-cycle `Z` on `W`. Since
`N₁(W/S)` is spanned by such classes, this determines the map.

The pull-back `p^* D` of an `ℝ`-Cartier divisor `D = ∑ⱼ cⱼ Dⱼ` enters only through its degrees
`(p^* D · Γ) = ∑ⱼ cⱼ deg_Γ p^* 𝒪_X(Dⱼ)` on curves `Γ ⊆ W`, as in `[KM, Notation 0.4(5)]`, so no
pull-back of Cartier divisors needs to be defined. The statement is for `ℝ`-Cartier divisors;
a `ℚ`-Cartier divisor is the case of rational coefficients.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori],
  Proposition 3.27
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe w

namespace MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

section Helpers

variable {k : Type w} [Field k] {X Y : Scheme.{w}} {sX : X ⟶ Spec (.of k)}
  {sY : Y ⟶ Spec (.of k)}

/-- The image of a proper curve that is not a point has a positive residue degree. -/
private lemma residueFieldDegree_pos [IsSeparated sY] [LocallyOfFiniteType sY] (f : X ⟶ Y)
    (hf : f ≫ sY = sX) (C : ProperCurve sX) (hpt : ¬ ∃ y : Y, Set.range (C.ι ≫ f) = {y}) :
    0 < residueFieldDegree f C.point := by
  set φ := C.ι ≫ f with hφdef
  have hφ : φ ≫ sY = C.ι ≫ sX := by rw [hφdef, Category.assoc, hf]
  have : IsProper (φ ≫ sY) := hφ ▸ inferInstance
  have : IsProper φ := IsProper.of_comp _ sY
  have := C.isCurve
  have : AlgebraicGeometry.IsCurve k (φ ≫ sY) := hφ ▸ inferInstance
  have hdeg : residueFieldDegree f C.point = degreeOver φ.toImage := by
    have h1 := residueDegree_comp C.ι f (genericPoint C.scheme)
    rw [C.ι_genericPoint, Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion C.ι, mul_one]
      at h1
    have h2 := residueDegree_comp φ.toImage φ.imageι (genericPoint C.scheme)
    rw [Scheme.Hom.toImage_imageι,
      Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion φ.imageι,
      one_mul, residueDegree_genericPoint_eq_degreeOver φ.toImage] at h2
    exact h1.symm.trans h2
  rw [hdeg]
  apply degreeOver_pos
  rw [dominantFunctionFieldMap_eq_functionFieldMap (f := φ.toImage)]
  exact finite_functionField_image sY φ hpt

/-- The closure of a point of a proper curve is not a point. -/
private lemma closure_point_ne_singleton (C : ProperCurve sX) (y : X) :
    closure ({C.point} : Set X) ≠ {y} := by
  intro hy
  have hr : ∀ t, C.ι t = y := fun t => by
    have ht : C.ι t ∈ closure {C.point} := C.range_ι ▸ ⟨t, rfl⟩
    rw [hy] at ht
    exact ht
  have : Subsingleton C.scheme :=
    ⟨fun a b => C.ι.isEmbedding.injective ((hr a).trans (hr b).symm)⟩
  have h0 : topologicalKrullDim C.scheme ≤ 0 := topologicalKrullDim_zero_of_discreteTopology _
  rw [C.dim_eq] at h0
  norm_num at h0

variable {S : Scheme.{w}} {πX : X ⟶ S} {πY : Y ⟶ S}

/-- The image of a curve contracted over `S`, when it is a curve, is contracted over `S`. -/
private lemma isContractedBy_image [IsSeparated sY] [LocallyOfFiniteType sY] (f : X ⟶ Y)
    (hf : f ≫ sY = sX) (hfπ : f ≫ πY = πX) {C : ProperCurve sX} (hC : C.IsContractedBy πX)
    (h : IsProperCurve sY (f C.point)) :
    (⟨f C.point, h⟩ : ProperCurve sY).IsContractedBy πY := by
  intro x hx
  change x ∈ closure {f C.point} at hx
  rw [← C.range_comp f hf] at hx
  obtain ⟨c, rfl⟩ := hx
  have hc : C.ι c ∈ closure {C.point} := C.range_ι ▸ ⟨c, rfl⟩
  change πY (f (C.ι c)) = πY (f C.point)
  have e : ∀ y, πY (f y) = πX y := fun y => by rw [← Scheme.Hom.comp_apply, hfπ]
  rw [e, e]
  exact hC _ hc

/-- The push-forward of a contracted curve is `0` or a nonnegative multiple of a contracted
curve. -/
private lemma cyclePushforwardOfPoint_eq [IsSeparated sY] [LocallyOfFiniteType sY] (f : X ⟶ Y)
    (hf : f ≫ sY = sX) (hfπ : f ≫ πY = πX) {C : ProperCurve sX} (hC : C.IsContractedBy πX) :
    cyclePushforwardOfPoint ℝ sY f C.point = 0 ∨
      ∃ (C' : ProperCurve sY) (hC' : C'.IsContractedBy πY) (r : ℝ), 0 ≤ r ∧
        cyclePushforwardOfPoint ℝ sY f C.point = r • C'.cycle ℝ := by
  unfold cyclePushforwardOfPoint
  split_ifs with h
  · refine Or.inr ⟨⟨f C.point, h⟩, isContractedBy_image f hf hfπ hC h,
      residueFieldDegree f C.point, Nat.cast_nonneg _, ?_⟩
    rw [ProperCurve.cycle, Finsupp.smul_single, smul_eq_mul, mul_one]
  · exact Or.inl rfl

/-- The push-forward of a contracted curve is a relative 1-cycle. -/
private lemma cyclePushforwardOfPoint_mem [IsSeparated sY] [LocallyOfFiniteType sY] (f : X ⟶ Y)
    (hf : f ≫ sY = sX) (hfπ : f ≫ πY = πX) {C : ProperCurve sX} (hC : C.IsContractedBy πX) :
    cyclePushforwardOfPoint ℝ sY f C.point ∈ relativeOneCycles sY πY := by
  rcases cyclePushforwardOfPoint_eq f hf hfπ hC with h | ⟨C', hC', r, -, h⟩
  · rw [h]
    exact zero_mem _
  · rw [h]
    exact Submodule.smul_mem _ r (C'.cycle_mem_relativeOneCycles hC')

/-- The push-forward of a relative 1-cycle is a relative 1-cycle. -/
private lemma pushforward_mem [IsSeparated sY] [LocallyOfFiniteType sY] (f : X ⟶ Y)
    (hf : f ≫ sY = sX) (hfπ : f ≫ πY = πX) {Z : OneCycle ℝ sX}
    (hZ : Z ∈ relativeOneCycles sX πX) :
    OneCycle.pushforward ℝ sX sY f Z ∈ relativeOneCycles sY πY := by
  rw [OneCycle.pushforward, Finsupp.linearCombination_apply]
  exact Submodule.sum_mem _ fun C hC =>
    Submodule.smul_mem _ _ (cyclePushforwardOfPoint_mem f hf hfπ (hZ hC))

/-- **Lifting contracted curves.** Through a surjective morphism of projective varieties over
`S`, every curve contracted over `S` is the image of a contracted curve. -/
private lemma exists_lift {W : Scheme.{w}} {sW : W ⟶ Spec (.of k)} {πW : W ⟶ S}
    (hW : IsProjectiveVariety k sW) (hX : IsProjectiveVariety k sX)
    (p : W ⟶ X) (hpk : p ≫ sX = sW) (hp : p ≫ πX = πW) [Surjective p] {C : ProperCurve sX}
    (hC : C.IsContractedBy πX) :
    ∃ Γ : ProperCurve sW, Γ.IsContractedBy πW ∧ p Γ.point = C.point := by
  have : IsProper sW := isProper_of_isProjectiveMorphism sW hW.isProjective
  obtain ⟨Γ, q, ⟨hΓi, hΓd⟩, hq, -, hsurj⟩ :=
    IsCurveIn.exists_isCurveIn_isFinite_surjective hW hX p hpk
      (C := Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {C.point}))
      ⟨inferInstance, C.dim_eq⟩
  set g := genericPoint Γ.subscheme
  set w := Γ.subschemeι g with hwdef
  have hqg : q g = genericPoint C.scheme := map_genericPoint_of_isDominant q
  have hpw : p w = C.point := by
    have h := congrArg (fun φ => φ g) hq
    simp only [Scheme.Hom.comp_apply] at h
    rw [hwdef, ← h, hqg]
    exact C.ι_genericPoint
  have hcl : closure ({w} : Set W) = (Γ.support : Set W) := by
    rw [← Γ.range_subschemeι, ← Set.image_univ, ← (genericPoint_spec Γ.subscheme).def,
      ← Γ.subschemeι.isClosedEmbedding.closure_image_eq, Set.image_singleton]
  have hdim : topologicalKrullDim (curveSubschemeAt w) = 1 := by
    have e1 : topologicalKrullDim (curveSubschemeAt w) =
        topologicalKrullDim (closure ({w} : Set W)) := by
      change topologicalKrullDim
        ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {w})).support : Set W) = _
      rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
      rfl
    have e2 : topologicalKrullDim Γ.subscheme = topologicalKrullDim (Γ.support : Set W) := rfl
    rw [e1, hcl, ← e2, hΓd]
  refine ⟨⟨w, isProperCurve_of_isProper sW hdim⟩, fun x hx => ?_, hpw⟩
  have e : ∀ y, πW y = πX (p y) := fun y => by rw [← Scheme.Hom.comp_apply, hp]
  change πW x = πW w
  rw [e, e, hpw]
  apply hC
  have := image_closure_subset_closure_image p.continuous ⟨x, hx, rfl⟩
  rwa [Set.image_singleton, hpw] at this

/-- A lifted curve pushes forward to a positive multiple of the curve it lifts. -/
private lemma exists_lift_pushforward {W : Scheme.{w}} {sW : W ⟶ Spec (.of k)} {πW : W ⟶ S}
    (hW : IsProjectiveVariety k sW) (hX : IsProjectiveVariety k sX)
    (p : W ⟶ X) (hpk : p ≫ sX = sW) (hp : p ≫ πX = πW) [Surjective p] {C : ProperCurve sX}
    (hC : C.IsContractedBy πX) :
    ∃ (Γ : ProperCurve sW) (_ : Γ.IsContractedBy πW) (d : ℝ), 0 < d ∧
      OneCycle.pushforward ℝ sW sX p (Γ.cycle ℝ) = d • C.cycle ℝ := by
  have : AlgebraicGeometry.IsVariety k sX := hX.toIsVariety
  obtain ⟨Γ, hΓ, hpw⟩ := exists_lift hW hX p hpk hp hC
  have hpt : ¬ ∃ y : X, Set.range (Γ.ι ≫ p) = {y} := by
    rintro ⟨y, hy⟩
    rw [Γ.range_comp p hpk, hpw] at hy
    exact closure_point_ne_singleton C y hy
  have hPC : IsProperCurve sX (p Γ.point) := hpw ▸ C.isProperCurve
  have hCeq : (⟨p Γ.point, hPC⟩ : ProperCurve sX) = C := ProperCurve.ext hpw
  refine ⟨Γ, hΓ, residueFieldDegree p Γ.point,
    by exact_mod_cast residueFieldDegree_pos p hpk Γ hpt, ?_⟩
  rw [OneCycle.pushforward_cycle, cyclePushforwardOfPoint, dif_pos hPC, hCeq, ProperCurve.cycle,
    Finsupp.smul_single, smul_eq_mul, mul_one]

/-- The intersection number of a push-forward with an `ℝ`-Cartier divisor, through the
projection formula. -/
private lemma intersectionNumber_pushforward [IsSeparated sY] [LocallyOfFiniteType sY]
    (f : X ⟶ Y) (hf : f ≫ sY = sX) (z : OneCycle ℝ sX) (D : KCartierDivisor ℝ Y) :
    (OneCycle.pushforward ℝ sX sY f z).intersectionNumber D =
      D.sum fun E c => c * OneCycle.degree ℝ sX
        ((Scheme.Modules.pullback f).obj (MMP.CartierDivisor.sheaf E)) z := by
  simp only [OneCycle.intersectionNumber, OneCycle.intersectionPairing,
    Finsupp.linearCombination_apply, Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul]
  refine Finset.sum_congr rfl fun E _ => ?_
  rw [OneCycle.cartierDegree, OneCycle.degree_pushforward f hf]

/-- The class of `r` times a contracted curve is `r` times its class. -/
private lemma relativeNumericalClass_smul_cycle {f : X ⟶ S} {C : ProperCurve sX}
    (hC : C.IsContractedBy f) (r : ℝ) (h : r • C.cycle ℝ ∈ relativeOneCycles sX f) :
    relativeNumericalClass sX f ⟨r • C.cycle ℝ, h⟩ = r • C.relativeClass f hC := by
  rw [ProperCurve.relativeClass, ← map_smul]
  rfl

/-- The classes of contracted curves span `N₁(X/S)`. -/
private lemma span_relativeClass (f : X ⟶ S) :
    Submodule.span ℝ (Set.range fun C : {C : ProperCurve sX // C.IsContractedBy f} =>
      C.1.relativeClass f C.2) = ⊤ := by
  have hb := (Finsupp.basisSingleOne.map (show _ ≃ₗ[ℝ] relativeOneCycles sX f from
    (Finsupp.supportedEquivFinsupp {C : ProperCurve sX | C.IsContractedBy f}).symm)).span_eq
  rw [← LinearMap.range_eq_top.2 (relativeNumericalClass_surjective sX f), LinearMap.range_eq_map,
    ← hb, Submodule.map_span, ← Set.range_comp]
  refine congrArg (fun g => Submodule.span ℝ (Set.range g)) (funext fun C => ?_)
  exact congrArg _ (Subtype.ext (Finsupp.supportedEquivFinsupp_symm_single _ C 1).symm)

/-- A linear map carrying `NE(W/S)` onto `NE(X/S)` is surjective. -/
private lemma surjective_of_map_relativeConeOfCurves {W : Scheme.{w}} {sW : W ⟶ Spec (.of k)}
    {πW : W ⟶ S} {φ : RelativeNumericalCurveClasses sW πW →ₗ[ℝ] RelativeNumericalCurveClasses sX πX}
    (h : (relativeConeOfCurves sW πW).map φ = relativeConeOfCurves sX πX) :
    Function.Surjective φ := by
  refine LinearMap.range_eq_top.1 (top_unique ?_)
  rw [← span_relativeClass πX, Submodule.span_le]
  rintro _ ⟨⟨C, hC⟩, rfl⟩
  obtain ⟨y, -, hy⟩ := h ▸ relativeClass_mem_relativeConeOfCurves hC
  exact ⟨y, hy⟩

section Pinned

/-! A linear map `φ : N₁(W/S) → N₁(X/S)` *pinned* by the push-forward: `φ [Z] = [p_* Z]`. -/

variable {W : Scheme.{w}} {sW : W ⟶ Spec (.of k)} {πW : W ⟶ S} {p : W ⟶ X}
  {φ : RelativeNumericalCurveClasses sW πW →ₗ[ℝ] RelativeNumericalCurveClasses sX πX}

/-- A pinned map sends the class of a contracted curve to `0` or to a nonnegative multiple of
the class of a contracted curve. -/
private lemma map_relativeClass_eq_zero_or [IsSeparated sX] [LocallyOfFiniteType sX]
    (hpk : p ≫ sX = sW) (hp : p ≫ πX = πW)
    (hφ : ∀ (Z : relativeOneCycles sW πW) (Z' : relativeOneCycles sX πX),
      (Z' : OneCycle ℝ sX) = OneCycle.pushforward ℝ sW sX p Z →
        φ (relativeNumericalClass sW πW Z) = relativeNumericalClass sX πX Z')
    {Γ : ProperCurve sW} (hΓ : Γ.IsContractedBy πW) :
    φ (Γ.relativeClass πW hΓ) = 0 ∨
      ∃ (C' : ProperCurve sX) (hC' : C'.IsContractedBy πX) (r : ℝ), 0 ≤ r ∧
        φ (Γ.relativeClass πW hΓ) = r • C'.relativeClass πX hC' := by
  rcases cyclePushforwardOfPoint_eq p hpk hp hΓ with h | ⟨C', hC', r, hr, h⟩
  · exact .inl ((hφ _ 0 ((OneCycle.pushforward_cycle ℝ sX p Γ).trans h).symm).trans (map_zero _))
  · refine .inr ⟨C', hC', r, hr, ?_⟩
    rw [ProperCurve.relativeClass, hφ _ ⟨r • C'.cycle ℝ,
      Submodule.smul_mem _ r (C'.cycle_mem_relativeOneCycles hC')⟩
      ((OneCycle.pushforward_cycle ℝ sX p Γ).trans h).symm, relativeNumericalClass_smul_cycle hC']

/-- A pinned map sends the class of some contracted curve to a positive multiple of the class
of a given contracted curve. -/
private lemma exists_map_relativeClass_eq_smul (hW : IsProjectiveVariety k sW)
    (hX : IsProjectiveVariety k sX) (hpk : p ≫ sX = sW) (hp : p ≫ πX = πW)
    [Surjective p]
    (hφ : ∀ (Z : relativeOneCycles sW πW) (Z' : relativeOneCycles sX πX),
      (Z' : OneCycle ℝ sX) = OneCycle.pushforward ℝ sW sX p Z →
        φ (relativeNumericalClass sW πW Z) = relativeNumericalClass sX πX Z')
    {C : ProperCurve sX} (hC : C.IsContractedBy πX) :
    ∃ (Γ : ProperCurve sW) (hΓ : Γ.IsContractedBy πW) (d : ℝ), 0 < d ∧
      φ (Γ.relativeClass πW hΓ) = d • C.relativeClass πX hC := by
  obtain ⟨Γ, hΓ, d, hd, heq⟩ := exists_lift_pushforward hW hX p hpk hp hC
  refine ⟨Γ, hΓ, d, hd, ?_⟩
  rw [ProperCurve.relativeClass, hφ _ ⟨d • C.cycle ℝ,
    Submodule.smul_mem _ d (C.cycle_mem_relativeOneCycles hC)⟩ heq.symm,
    relativeNumericalClass_smul_cycle hC]

/-- **Push-forward of cones of curves.** A pinned map carries `NE(W/S)` onto `NE(X/S)`. -/
private lemma map_relativeConeOfCurves (hW : IsProjectiveVariety k sW)
    (hX : IsProjectiveVariety k sX) (hpk : p ≫ sX = sW) (hp : p ≫ πX = πW)
    [Surjective p]
    (hφ : ∀ (Z : relativeOneCycles sW πW) (Z' : relativeOneCycles sX πX),
      (Z' : OneCycle ℝ sX) = OneCycle.pushforward ℝ sW sX p Z →
        φ (relativeNumericalClass sW πW Z) = relativeNumericalClass sX πX Z') :
    (relativeConeOfCurves sW πW).map φ = relativeConeOfCurves sX πX := by
  have : AlgebraicGeometry.IsVariety k sX := hX.toIsVariety
  rw [relativeConeOfCurves, relativeConeOfCurves, PointedCone.hull, PointedCone.hull,
    PointedCone.map, Submodule.map_span]
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨_, ⟨⟨Γ, hΓ⟩, rfl⟩, rfl⟩
    change φ (Γ.relativeClass πW hΓ) ∈ _
    rcases map_relativeClass_eq_zero_or hpk hp hφ hΓ with h | ⟨C', hC', r, hr, h⟩
    · rw [h]
      exact zero_mem _
    · rw [h]
      exact Submodule.smul_mem _ (⟨r, hr⟩ : NNReal) (Submodule.subset_span ⟨⟨C', hC'⟩, rfl⟩)
  · rintro _ ⟨⟨C, hC⟩, rfl⟩
    obtain ⟨Γ, hΓ, d, hd, h⟩ := exists_map_relativeClass_eq_smul hW hX hpk hp hφ hC
    change C.relativeClass πX hC ∈ _
    rw [show C.relativeClass πX hC = d⁻¹ • φ (Γ.relativeClass πW hΓ) by
      rw [h, inv_smul_smul₀ hd.ne']]
    exact Submodule.smul_mem _ (⟨d⁻¹, inv_nonneg.mpr hd.le⟩ : NNReal)
      (Submodule.subset_span ⟨_, ⟨⟨Γ, hΓ⟩, rfl⟩, rfl⟩)

/-- A pinned map is continuous. -/
private lemma continuous_of_pinned [IsSeparated sX] [LocallyOfFiniteType sX]
    (hpk : p ≫ sX = sW) (hp : p ≫ πX = πW)
    (hφ : ∀ (Z : relativeOneCycles sW πW) (Z' : relativeOneCycles sX πX),
      (Z' : OneCycle ℝ sX) = OneCycle.pushforward ℝ sW sX p Z →
        φ (relativeNumericalClass sW πW Z) = relativeNumericalClass sX πX Z') :
    Continuous φ := by
  refine continuous_iInf_rng.2 fun L => continuous_iInf_rng.2 fun h =>
    continuous_induced_rng.2 ?_
  have := h
  have he : ⇑(RelativeNumericalCurveClasses.degree sX πX L) ∘ ⇑φ =
      RelativeNumericalCurveClasses.degree sW πW ((Scheme.Modules.pullback p).obj L) :=
    funext fun z => by
      obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sW πW z
      rw [Function.comp_apply, hφ Z ⟨_, pushforward_mem p hpk hp Z.2⟩ rfl]
      exact OneCycle.degree_pushforward p hpk L Z
  rw [he]
  exact RelativeNumericalCurveClasses.continuous_degree sW πW _

end Pinned

/-- **Nefness is detected by pull-back** along a surjection of projective varieties over `S`. -/
private lemma isRelativelyNef_iff {W : Scheme.{w}} {sW : W ⟶ Spec (.of k)} {πW : W ⟶ S}
    (hW : IsProjectiveVariety k sW) (hX : IsProjectiveVariety k sX)
    {p : W ⟶ X} (hpk : p ≫ sX = sW) (hp : p ≫ πX = πW) [Surjective p]
    (D : KCartierDivisor ℝ X) :
    D.IsRelativelyNef sX πX ↔
      ∀ Γ : ProperCurve sW, Γ.IsContractedBy πW →
        0 ≤ D.sum fun E c => c * OneCycle.degree ℝ sW
          ((Scheme.Modules.pullback p).obj (MMP.CartierDivisor.sheaf E))
          (Γ.cycle ℝ) := by
  have : AlgebraicGeometry.IsVariety k sX := hX.toIsVariety
  refine ⟨fun hD Γ hΓ => ?_, fun h C hC => ?_⟩
  · rw [← intersectionNumber_pushforward p hpk, OneCycle.pushforward_cycle]
    rcases cyclePushforwardOfPoint_eq p hpk hp hΓ with h | ⟨C', hC', r, hr, h⟩
    · simp [h, OneCycle.intersectionNumber]
    · have := hD C' hC'
      simp only [h, OneCycle.intersectionNumber, map_smul, smul_eq_mul] at this ⊢
      exact mul_nonneg hr this
  · obtain ⟨Γ, hΓ, d, hd, heq⟩ := exists_lift_pushforward hW hX p hpk hp hC
    have := h Γ hΓ
    rw [← intersectionNumber_pushforward p hpk, heq] at this
    simp only [OneCycle.intersectionNumber, map_smul, smul_eq_mul] at this ⊢
    exact (mul_nonneg_iff_of_pos_left hd).mp this

end Helpers

/-- **Push-forward of relative cones along a surjection.** Let `p : W ⟶ X` be a surjective
morphism of projective `k`-varieties over a projective `k`-variety `S`. There is a linear map
`φ = p_* : N₁(W/S) → N₁(X/S)` with `φ [Z] = [p_* Z]` for every relative 1-cycle `Z` on `W`; it
is surjective, maps `NE(W/S)` onto `NE(X/S)`, satisfies
`φ (NE̅(W/S)) ⊆ NE̅(X/S) = closure (φ (NE̅(W/S)))`, and an `ℝ`-Cartier divisor `D` on `X` is
nef over `S` if and only if `(p^* D · Γ) = ∑ⱼ cⱼ deg_Γ p^* 𝒪_X(Dⱼ) ≥ 0` for every curve
`Γ ⊆ W` contracted to a point of `S`. -/
@[mmp "lem_mmp_projective_pushforward_curve_cones"]
theorem exists_relativeNumericalPushforward_of_surjective {k : Type w} [Field k]
    {W X S : Scheme.{w}} {sW : W ⟶ Spec (.of k)} {sX : X ⟶ Spec (.of k)}
    {sS : S ⟶ Spec (.of k)} (hW : IsProjectiveVariety k sW) (hX : IsProjectiveVariety k sX)
    (hS : IsProjectiveVariety k sS) {πW : W ⟶ S} {πX : X ⟶ S} (hπW : πW ≫ sS = sW)
    (hπX : πX ≫ sS = sX) {p : W ⟶ X} (hp : p ≫ πX = πW) [Surjective p] :
    ∃ φ : RelativeNumericalCurveClasses sW πW →ₗ[ℝ] RelativeNumericalCurveClasses sX πX,
      (∀ (Z : relativeOneCycles sW πW) (Z' : relativeOneCycles sX πX),
        (Z' : OneCycle ℝ sX) = OneCycle.pushforward ℝ sW sX p Z →
          φ (relativeNumericalClass sW πW Z) = relativeNumericalClass sX πX Z') ∧
      Function.Surjective φ ∧
      (relativeConeOfCurves sW πW).map φ = relativeConeOfCurves sX πX ∧
      φ '' (relativeClosedConeOfCurves sW πW : Set (RelativeNumericalCurveClasses sW πW)) ⊆
        relativeClosedConeOfCurves sX πX ∧
      (relativeClosedConeOfCurves sX πX : Set (RelativeNumericalCurveClasses sX πX)) =
        closure (φ '' relativeClosedConeOfCurves sW πW) ∧
      ∀ D : KCartierDivisor ℝ X,
        D.IsRelativelyNef sX πX ↔
          ∀ Γ : ProperCurve sW, Γ.IsContractedBy πW →
            0 ≤ D.sum fun E c => c * OneCycle.degree ℝ sW
              ((Scheme.Modules.pullback p).obj (MMP.CartierDivisor.sheaf E))
              (Γ.cycle ℝ) := by
  have : AlgebraicGeometry.IsVariety k sX := hX.toIsVariety
  have hpk : p ≫ sX = sW := by rw [← hπX, ← Category.assoc, hp, hπW]
  let φ := (relativeNumericallyTrivial sW πW).mapQ (relativeNumericallyTrivial sX πX)
    (((OneCycle.pushforward ℝ sW sX p).comp (relativeOneCycles sW πW).subtype).codRestrict _
      fun Z => pushforward_mem p hpk hp Z.2)
    fun Z hZ => OneCycle.pushforward_mem_numericallyTrivial p hpk hZ
  have hφ : ∀ (Z : relativeOneCycles sW πW) (Z' : relativeOneCycles sX πX),
      (Z' : OneCycle ℝ sX) = OneCycle.pushforward ℝ sW sX p Z →
        φ (relativeNumericalClass sW πW Z) = relativeNumericalClass sX πX Z' :=
    fun _ _ hZ => congrArg _ (Subtype.ext hZ.symm)
  have hcone := map_relativeConeOfCurves hW hX hpk hp hφ
  have hconeset : φ '' (relativeConeOfCurves sW πW : Set _) = relativeConeOfCurves sX πX := by
    rw [← hcone]
    rfl
  have hclosed : φ '' (relativeClosedConeOfCurves sW πW : Set _) ⊆
      relativeClosedConeOfCurves sX πX := by
    rw [coe_relativeClosedConeOfCurves, coe_relativeClosedConeOfCurves, ← hconeset]
    exact image_closure_subset_closure_image (continuous_of_pinned hpk hp hφ)
  refine ⟨φ, hφ, surjective_of_map_relativeConeOfCurves hcone, hcone, hclosed,
    le_antisymm ?_ (closure_minimal hclosed ?_), isRelativelyNef_iff hW hX hpk hp⟩
  · rw [coe_relativeClosedConeOfCurves, ← hconeset]
    exact closure_mono (Set.image_mono subset_closure)
  · rw [coe_relativeClosedConeOfCurves]
    exact isClosed_closure

end MMP.Mori
