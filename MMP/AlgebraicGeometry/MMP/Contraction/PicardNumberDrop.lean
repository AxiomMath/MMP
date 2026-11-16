module

public import MMP.AlgebraicGeometry.MMP.Contraction.RayLineBundleDescent
public import MMP.Analysis.Complex.CauchyTransformRungeMontel
public import MMP.AlgebraicGeometry.Positivity.RelativeAmpleContractedCurve

/-!
# Contracting a negative extremal ray drops the Picard number by one

Let `X` be a projective variety over an algebraically closed field `k` of characteristic zero
and `(X, Δ)` a klt pair with `Δ` effective, `R` an extremal ray of the closed cone of curves
`NE̅(X)` on which `K_X + Δ` is negative away from `0`, and `g : X ⟶ Z` a contraction of `R`.
Then `ρ(Z) = ρ(X) - 1`.

## Main results

* `MMP.Mori.picardNumber_add_one_eq_of_isContractionOfFace`: the statement above.

## Implementation notes

The Picard number is `MMP.Mori.picardNumber`, valued in `ℕ∞`; the conclusion is written
`ρ(Z) + 1 = ρ(X)`, which avoids truncated subtraction in `ℕ∞`. The negativity of `K_X + Δ` on
`R ∖ {0}` is read through the linear form `MMP.Fourfold.QDivisor.curveForm` attached to the
`ℚ`-Cartier witness carried by the klt hypothesis.

The push-forward `g_* : N₁(X) ⟶ N₁(Z)` is surjective, since every curve of `Z` is the image of
a curve of `X`, and its kernel is the line `ℝ · [C]` spanned by a curve `C` with
`R = ℝ_{≥0} [C]`: a class `z` with `g_* z = 0` is killed by every pulled-back line bundle, hence,
by exactness of `Pic Z → Pic X → ℤ`, by every line bundle of degree zero on `C`, and this forces
`z ∈ ℝ · [C]`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Corollary 3.17
-/

open CategoryTheory AlgebraicGeometry MMP.Mori

namespace MMP.FourfoldProofs.Km3bPicardNumberDropsProof

section Helpers

variable {k : Type} [Field k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)}

/-- A numerical class on which every invertible sheaf has degree zero is zero. -/
private theorem eq_zero_of_forall_degree_eq_zero {z : NumericalCurveClasses sX}
    (h : ∀ (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L],
      NumericalCurveClasses.degree sX L z = 0) : z = 0 := by
  obtain ⟨Z, rfl⟩ := OneCycle.numericalClass_surjective sX z
  exact (Submodule.Quotient.mk_eq_zero _).mpr (OneCycle.mem_numericallyTrivial.mpr fun L _ => h L)

/-- The degree form on `N₁(X)` of an invertible sheaf depends only on its isomorphism class. -/
private theorem degree_eq_of_iso {L L' : X.Modules}
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L'] (e : L ≅ L') :
    NumericalCurveClasses.degree sX L = NumericalCurveClasses.degree sX L' := by
  apply Submodule.linearMap_qext
  ext C
  simp [NumericalCurveClasses.degree, OneCycle.degree, ProperCurve.degree,
    degreeOn_eq_of_iso k sX C.ι C.dim_le e]

/-- `deg_C 𝒪_X(E + E') = deg_C 𝒪_X(E) + deg_C 𝒪_X(E')` along a proper curve. -/
private theorem degree_cartierSheaf_add (C : ProperCurve sX) (E E' : X.CartierDivisor) :
    C.degree k (MMP.CartierDivisor.sheaf (E + E')) =
      C.degree k (MMP.CartierDivisor.sheaf E) +
        C.degree k (MMP.CartierDivisor.sheaf E') := by
  haveI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.toRingedSpace.presheaf,
        X.toRingedSpace.IsSheaf⟩).obj (MMP.CartierDivisor.sheaf E)).obj
          (MMP.CartierDivisor.sheaf E')) :=
    Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible X.presheaf X.ringCatSheaf.2 _ _
  unfold ProperCurve.degree
  rw [← degreeOn_tensorSheaf]
  exact (degreeOn_eq_of_iso k sX C.ι C.dim_le
    (MMP.CartierDivisorSheaf.sheafMulIso E E')).symm

/-- The degree forms of Cartier divisors on `N₁(X)`, as an additive map. -/
private noncomputable def cartierDegreeForm (sX : X ⟶ Spec (.of k)) :
    X.CartierDivisor →+ (NumericalCurveClasses sX →ₗ[ℝ] ℝ) :=
  AddMonoidHom.mk' (fun E => NumericalCurveClasses.degree sX
      (MMP.CartierDivisor.sheaf E)) fun E E' => by
    apply Submodule.linearMap_qext
    ext C
    simp [NumericalCurveClasses.degree, OneCycle.degree, degree_cartierSheaf_add]

private theorem cartierDegreeForm_apply (E : X.CartierDivisor) :
    cartierDegreeForm sX E =
      NumericalCurveClasses.degree sX (MMP.CartierDivisor.sheaf E) := rfl

/-- The value of a degree form at the class of a proper curve is the degree along the curve. -/
private theorem degree_numericalClass_cycle (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (C : ProperCurve sX) :
    NumericalCurveClasses.degree sX L (OneCycle.numericalClass sX (C.cycle ℝ)) = C.degree k L := by
  rw [NumericalCurveClasses.degree_numericalClass, OneCycle.degree_cycle]

/-- On a projective variety the class of a proper curve in `N₁(X)` is nonzero. -/
private theorem numericalClass_cycle_ne_zero [AlgebraicGeometry.IsProjectiveVariety k sX]
    (C : ProperCurve sX) : OneCycle.numericalClass sX (C.cycle ℝ) ≠ 0 := by
  have hproj : IsProjectiveMorphism sX := AlgebraicGeometry.IsProjectiveVariety.isProjective
  obtain ⟨L, hL, hLa⟩ := exists_isAmple_of_isQuasiProjective sX
    (Stacks.Ample.unitModule (Spec (.of k)))
    (Stacks.Ample.isAmple_unitModule_of_isAffine _)
    (isQuasiProjective_of_isHQuasiProjective sX hproj.isHQuasiProjective)
  have hpos := MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy sX L
    (MMP.Threefold.Resolution.isRelativelyAmple_of_isAmple sX L hLa) C
    (fun _ _ => Subsingleton.elim _ _)
  intro h0
  have h := degree_numericalClass_cycle L C
  rw [h0, map_zero] at h
  have : (0 : ℝ) < (C.degree k L : ℝ) := by exact_mod_cast hpos
  linarith

/-- A class on which every invertible sheaf of degree zero along the proper curve `C` has degree
zero lies on the line spanned by the class of `C`. -/
private theorem mem_span_numericalClass_of_forall_degree_eq_zero [IsIntegral X]
    [AlgebraicGeometry.IsProjectiveVariety k sX] (C : ProperCurve sX)
    {z : NumericalCurveClasses sX}
    (hz : ∀ (M : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M],
      C.degree k M = 0 → NumericalCurveClasses.degree sX M z = 0) :
    z ∈ Submodule.span ℝ {OneCycle.numericalClass sX (C.cycle ℝ)} := by
  set c := OneCycle.numericalClass sX (C.cycle ℝ) with hc
  have hc0 : c ≠ 0 := numericalClass_cycle_ne_zero C
  obtain ⟨E₀, hE₀⟩ : ∃ E₀ : X.CartierDivisor, C.degree k (MMP.CartierDivisor.sheaf E₀) ≠ 0 := by
    by_contra! h
    apply hc0
    refine eq_zero_of_forall_degree_eq_zero fun L _ => ?_
    obtain ⟨E, ⟨e⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf L
    rw [degree_eq_of_iso e, degree_numericalClass_cycle, h E, Int.cast_zero]
  set a : ℤ := C.degree k (MMP.CartierDivisor.sheaf E₀)
  have ha : (a : ℝ) ≠ 0 := by exact_mod_cast hE₀
  set t : ℝ := cartierDegreeForm sX E₀ z / a
  have key : ∀ E : X.CartierDivisor, cartierDegreeForm sX E (z - t • c) = 0 := by
    intro E
    set b : ℤ := C.degree k (MMP.CartierDivisor.sheaf E)
    have h1 : C.degree k (MMP.CartierDivisor.sheaf (a • E - b • E₀)) = 0 := by
      have h := congrArg (fun φ => φ c) (map_sub (cartierDegreeForm sX) (a • E) (b • E₀))
      simp only [map_zsmul, LinearMap.sub_apply, LinearMap.smul_apply, cartierDegreeForm_apply,
        hc, degree_numericalClass_cycle, zsmul_eq_mul] at h
      have h' : ((C.degree k (MMP.CartierDivisor.sheaf (a • E - b • E₀)) : ℤ) : ℝ) = 0 := by
        rw [h]
        push_cast
        ring
      exact_mod_cast h'
    have h2 := hz _ h1
    rw [← cartierDegreeForm_apply, map_sub, map_zsmul, map_zsmul] at h2
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, zsmul_eq_mul] at h2
    have hb : cartierDegreeForm sX E c = b := degree_numericalClass_cycle _ C
    have ha' : cartierDegreeForm sX E₀ c = a := degree_numericalClass_cycle _ C
    rw [map_sub, map_smul, hb, smul_eq_mul]
    simp only [t]
    field_simp
    linarith
  have : z - t • c = 0 := eq_zero_of_forall_degree_eq_zero fun L _ => by
    obtain ⟨E, ⟨e⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf L
    rw [degree_eq_of_iso e, ← cartierDegreeForm_apply, key]
  exact Submodule.mem_span_singleton.mpr ⟨t, (sub_eq_zero.mp this).symm⟩

end Helpers

/-- If `c = s • v` is a nonzero point of the ray `ℝ≥0 v`, then that ray is also `ℝ≥0 c`. -/
private theorem ray_eq_of_mem {V : Type*} [AddCommGroup V] [Module ℝ V] {v c : V}
    (hc : ∃ s : ℝ, 0 ≤ s ∧ s • v = c) (hc0 : c ≠ 0) :
    {w | ∃ t : ℝ, 0 ≤ t ∧ t • v = w} = {w | ∃ t : ℝ, 0 ≤ t ∧ t • c = w} := by
  obtain ⟨s, hs, hsv⟩ := hc
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hsv
    exact hc0 hsv.symm
  ext w
  refine ⟨fun ⟨t, ht, htw⟩ => ⟨t / s, div_nonneg ht hs, ?_⟩,
    fun ⟨t, ht, htw⟩ => ⟨t * s, mul_nonneg ht hs, ?_⟩⟩
  · rw [← hsv, smul_smul, div_mul_cancel₀ t hs0, htw]
  · rw [← htw, ← hsv, smul_smul]

section Pushforward

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

variable {k : Type} [Field k] {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
  {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY]

/-- The residue degree of `f` at the generic point of a proper curve `C` is the degree of
`C ⟶ f(C)`, the corestriction of `C.ι ≫ f` to its scheme-theoretic image. -/
private theorem residueFieldDegree_eq_degreeOver_toImage (f : X ⟶ Y) (C : ProperCurve sX)
    [IsProper (C.ι ≫ f)] [IsIntegral (C.ι ≫ f).image] :
    residueFieldDegree f C.point = degreeOver (C.ι ≫ f).toImage := by
  have h1 := residueDegree_comp C.ι f (genericPoint C.scheme)
  rw [C.ι_genericPoint, Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion C.ι, mul_one]
    at h1
  have h2 := residueDegree_comp (C.ι ≫ f).toImage (C.ι ≫ f).imageι (genericPoint C.scheme)
  rw [Scheme.Hom.toImage_imageι,
    Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion (C.ι ≫ f).imageι,
    one_mul, AlgebraicGeometry.residueDegree_genericPoint_eq_degreeOver (C.ι ≫ f).toImage] at h2
  exact h1.symm.trans h2

/-- If the image of a proper curve `C` under `f` is again a proper curve, the degree
`[k(C) : k(f(C))]` is positive. -/
private theorem residueFieldDegree_pos (f : X ⟶ Y) (hf : f ≫ sY = sX) (C : ProperCurve sX)
    (hC' : IsProperCurve sY (f C.point)) : 0 < residueFieldDegree f C.point := by
  set φ := C.ι ≫ f with hφdef
  have hφ : φ ≫ sY = C.ι ≫ sX := by rw [hφdef, Category.assoc, hf]
  have : IsProper (φ ≫ sY) := hφ ▸ inferInstance
  have : IsProper φ := IsProper.of_comp _ sY
  have := C.isCurve
  have : AlgebraicGeometry.IsCurve k (φ ≫ sY) := hφ ▸ inferInstance
  have hpt : ¬ ∃ y : Y, Set.range φ = {y} := by
    rintro ⟨y, hy⟩
    have hr : ∀ t, curveSubschemeAtι (f C.point) t = y := fun t => by
      have ht : curveSubschemeAtι (f C.point) t ∈ closure {f C.point} :=
        range_curveSubschemeAtι (f C.point) ▸ ⟨t, rfl⟩
      rwa [← C.range_comp f hf, ← hφdef, hy] at ht
    have : Subsingleton (curveSubschemeAt (f C.point)) :=
      ⟨fun a b => (curveSubschemeAtι (f C.point)).isEmbedding.injective
        ((hr a).trans (hr b).symm)⟩
    have h1 := hC'.dim_eq
    have h0 : topologicalKrullDim (curveSubschemeAt (f C.point)) ≤ 0 :=
      topologicalKrullDim_zero_of_discreteTopology _
    rw [h1] at h0
    norm_num at h0
  rw [residueFieldDegree_eq_degreeOver_toImage]
  apply degreeOver_pos
  rw [dominantFunctionFieldMap_eq_functionFieldMap (f := φ.toImage)]
  exact finite_functionField_image sY φ hpt

/-- Push-forward of real 1-cycles along a proper surjective morphism `τ` of varieties over `k`
is surjective: every proper curve `C' ⊆ Y` is the image of a proper curve `C ⊆ X`, and
`τ_* C = d · C'` with `d = [k(C) : k(C')] > 0`. -/
private theorem pushforward_surjective (hX : MMP.Mori.IsVariety k sX)
    (hY : MMP.Mori.IsVariety k sY) (τ : X ⟶ Y) (hτ : τ ≫ sY = sX) [IsProper τ] [Surjective τ] :
    Function.Surjective (OneCycle.pushforward ℝ sX sY τ) := by
  rw [← LinearMap.range_eq_top, eq_top_iff]
  rintro z -
  induction z using Finsupp.induction_linear with
  | zero => exact zero_mem _
  | add z w hz hw => exact add_mem hz hw
  | single C' r =>
    obtain ⟨C, hC⟩ := ProperCurve.exists_image_closure_eq_of_surjective hX hY τ hτ C'
    have hpt : τ C.point = C'.point := by
      have h1 : τ C.point ∈ closure {C'.point} := hC ▸ ⟨C.point, subset_closure rfl, rfl⟩
      have h2 : C'.point ∈ closure {τ C.point} := by
        have : C'.point ∈ τ '' closure {C.point} := hC ▸ subset_closure rfl
        obtain ⟨c, hc, hc'⟩ := this
        rw [← hc']
        have := image_closure_subset_closure_image (s := {C.point}) τ.continuous ⟨c, hc, rfl⟩
        rwa [Set.image_singleton] at this
      exact ((specializes_iff_mem_closure.mpr h2).antisymm
        (specializes_iff_mem_closure.mpr h1)).eq
    have hC' : IsProperCurve sY (τ C.point) := hpt ▸ C'.isProperCurve
    have hd' : (residueFieldDegree τ C.point : ℝ) ≠ 0 := by
      exact_mod_cast (residueFieldDegree_pos τ hτ C hC').ne'
    have he : (⟨τ C.point, hC'⟩ : ProperCurve sY) = C' := ProperCurve.ext hpt
    refine LinearMap.mem_range.mpr ⟨Finsupp.single C (r / residueFieldDegree τ C.point), ?_⟩
    rw [OneCycle.pushforward, Finsupp.linearCombination_single, cyclePushforwardOfPoint,
      dif_pos hC', he, Finsupp.smul_single, smul_eq_mul, div_mul_cancel₀ r hd']

/-- Push-forward of numerical classes along a proper surjective morphism of varieties over `k`
is surjective. -/
private theorem numericalPushforward_surjective (hX : MMP.Mori.IsVariety k sX)
    (hY : MMP.Mori.IsVariety k sY) (τ : X ⟶ Y) (hτ : τ ≫ sY = sX) [IsProper τ] [Surjective τ] :
    Function.Surjective (NumericalCurveClasses.pushforward τ hτ) := by
  intro w
  obtain ⟨W, rfl⟩ := OneCycle.numericalClass_surjective sY w
  obtain ⟨V, rfl⟩ := pushforward_surjective hX hY τ hτ W
  exact ⟨OneCycle.numericalClass sX V, rfl⟩

end Pushforward

end MMP.FourfoldProofs.Km3bPicardNumberDropsProof

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace MMP.Mori

open MMP.FourfoldProofs.Km3bPicardNumberDropsProof in
/-- **The Picard number drops by one** (Kollár–Mori 3.17). Let `X` be a projective variety over
an algebraically closed field `k` of characteristic zero, `(X, Δ)` a klt pair with canonical
divisor `K` and `Δ` effective, `R` an extremal ray of `NE̅(X)` with `(K + Δ) · z < 0` for every
nonzero `z ∈ R`, and `g : X ⟶ Z` a contraction of `R`. Then `ρ(Z) + 1 = ρ(X)`. -/
@[mmp "thm_km3b_picard_number_drops"]
public theorem picardNumber_add_one_eq_of_isContractionOfFace {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]
    [AlgebraicGeometry.IsProjectiveVariety k sX] {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    (hklt : IsKltPair sX n K Δ) (hΔ : Δ.IsEffective) {R : Set (NumericalCurveClasses sX)}
    (hR : IsExtremalRay ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) R)
    (hneg : ∀ z ∈ R, z ≠ 0 →
      MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hklt.1.2.2 z < 0)
    {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of k)} {g : X ⟶ Z} (hg : IsContractionOfFace k sX sZ R g) :
    picardNumber sZ + 1 = picardNumber sX := by
  have hpZ := hg.isProjectiveVariety_target
  haveI : AlgebraicGeometry.IsProjectiveVariety k sZ := hpZ
  haveI : AlgebraicGeometry.IsVariety k sZ := hpZ.toIsVariety
  haveI : IsIntegral Z := hpZ.toIsVariety.toIsIntegral
  haveI : IsProper (g ≫ sZ) := hg.comp_eq ▸ inferInstance
  haveI : IsProper g := IsProper.of_comp g sZ
  haveI : Surjective g := Scheme.Hom.surjective_of_isIso_app g hg.isIso_app
  haveI := NumericalCurveClasses.finiteDimensional_of_isProperVariety sX
  haveI := NumericalCurveClasses.finiteDimensional_of_isProperVariety sZ
  have hF : IsNegativeExtremalFace ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX))
      (MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hklt.1.2.2) R :=
    ⟨hR.1, hR.1.2.2.1, hneg⟩
  obtain ⟨v, hv0, hRv⟩ := hR.2
  have hvR : v ∈ R := hRv ▸ ⟨1, zero_le_one, one_smul ℝ v⟩
  have hF0 : R ≠ {0} := fun h => hv0 (h ▸ hvR : v ∈ ({0} : Set _))
  obtain ⟨C, hCR⟩ :=
    exists_properCurve_numericalClass_mem_of_isNegativeExtremalFace hklt hΔ hF hF0
  set c := OneCycle.numericalClass sX (C.cycle ℝ)
  have hc0 : c ≠ 0 := numericalClass_cycle_ne_zero C
  have hC : R = {w | ∃ t : ℝ, 0 ≤ t ∧ t • c = w} := by
    rw [hRv] at hCR ⊢
    exact ray_eq_of_mem hCR hc0
  set π := NumericalCurveClasses.pushforward g hg.comp_eq with hπ
  have hsurj : Function.Surjective π := numericalPushforward_surjective
    hg.isProjectiveVariety_source.toIsVariety hpZ.toIsVariety g hg.comp_eq
  have hdeg0 : ∀ (M : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M],
      C.degree k M = 0 ↔
        ∃ L : Z.Modules, SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 L ∧
          Nonempty (M ≅ (Scheme.Modules.pullback g).obj L) := fun M _ =>
    degree_eq_zero_iff_exists_iso_pullback_of_isContractionOfFace hklt hΔ hR hneg hg C hC M
  have hker : LinearMap.ker π = Submodule.span ℝ {c} := by
    apply le_antisymm
    · intro z hz
      rw [LinearMap.mem_ker] at hz
      refine mem_span_numericalClass_of_forall_degree_eq_zero C fun M _ hM => ?_
      obtain ⟨L, _, ⟨e⟩⟩ := (hdeg0 M).mp hM
      rw [degree_eq_of_iso e, ← NumericalCurveClasses.degree_pushforward g hg.comp_eq, ← hπ, hz,
        map_zero]
    · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker]
      refine eq_zero_of_forall_degree_eq_zero fun L _ => ?_
      rw [hπ, NumericalCurveClasses.degree_pushforward, degree_numericalClass_cycle,
        (hdeg0 _).mpr ⟨L, inferInstance, ⟨Iso.refl _⟩⟩, Int.cast_zero]
  have hrank := LinearMap.finrank_range_add_finrank_ker π
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, hker, finrank_span_singleton hc0] at hrank
  simp only [picardNumber, ← Module.finrank_eq_rank, Cardinal.toENat_nat]
  rw [← hrank]
  push_cast
  rfl

end MMP.Mori

end
