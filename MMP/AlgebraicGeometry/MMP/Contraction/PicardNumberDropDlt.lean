module

public import MMP.AlgebraicGeometry.MMP.ConeTheorem.DltRelativeConeTheorem
public import MMP.AlgebraicGeometry.MMP.Contraction.DltLineBundleDescent
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.PushforwardRelativeCone
public import MMP.AlgebraicGeometry.FiberSpace.NumericallyTrivialDescent

/-!
# Contracting a negative extremal ray of a dlt pair drops the Picard number by one

Let `(X, Δ)` be a projective `ℚ`-factorial dlt pair over an algebraically closed field `k` of
characteristic zero, `R ⊆ NE̅(X)` a `(K_X + Δ)`-negative extremal ray and `g : X ⟶ Y` a
contraction of `R`. Then `ρ(Y) = ρ(X) - 1`. Kollár–Mori state this for divisorial and for
fiber type contractions; the proof uses neither, so it is stated for every contraction of `R`.

Over the one-point base `Spec k` the relative and absolute spaces of curve classes agree, so
the dlt cone theorem shows that `R = ℝ_{≥0} [C]` for a curve `C`, and the dlt contraction
theorem shows that every invertible sheaf of degree zero on the curves of `R` is a pull-back
from `Y`. The push-forward `g_* : N₁(X) → N₁(Y)` is surjective (every curve of `Y` is the image
of a curve of `X`) and kills `[C]`. Conversely, if `g_* z = 0` and `z ∉ ℝ [C]`, choose a Cartier
divisor `D₀` with `(D₀ · C) ≠ 0` and a Cartier divisor `D₁` with
`(D₁ · ((D₀ · C) z - (D₀ · z) [C])) ≠ 0`; then `M = (D₀ · C) D₁ - (D₁ · C) D₀` has degree zero
on `C`, hence `𝒪_X(M) ≅ g^* L`, and the projection formula gives `(M · z) = (L · g_* z) = 0`,
a contradiction. So `ker g_* = ℝ [C]` and `dim N₁(X) = dim N₁(Y) + 1`.

## Main results

* `MMP.Mori.IsDltPair.picardNumber_add_one_eq_of_isContractionOfFace`: the statement above.

## Implementation notes

The dlt condition is `MMP.Mori.IsDltPair`, which includes `0 ≤ Δ ≤ 1` and the `ℚ`-Cartier
property of `K + Δ`; negativity of `R` is the pairing `MMP.Fourfold.QDivisor.curveForm` with
`K + Δ`, through that `ℚ`-Cartier witness. A contraction of `R` is
`MMP.Mori.IsContractionOfFace` for the ray `R`. The equation `ρ(Y) = ρ(X) - 1` is stated as
`ρ(Y) + 1 = ρ(X)` in `ℕ∞`, which is stronger than truncated subtraction.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori],
  Corollary 3.17 and Proposition 3.36(2)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace MMP.Mori

section Helpers

variable {k : Type} [Field k]

/-- The point `Spec k` is a projective variety over `k`. -/
private theorem isProjectiveVariety_id : MMP.Mori.IsProjectiveVariety k (𝟙 (Spec (.of k))) :=
  (AlgebraicGeometry.isProjectiveVariety_iff k _).mpr
    ⟨(MMP.Mori.isVariety_iff k _).mpr ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩,
      MMP.isProjectiveMorphism_of_isClosedImmersion _⟩

/-- Every 1-cycle of a `k`-scheme is a relative 1-cycle over `Spec k`. -/
private theorem mem_relativeOneCycles_self {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
    (Z : OneCycle ℝ sX) : Z ∈ relativeOneCycles sX sX :=
  (Finsupp.mem_supported ℝ Z).mpr fun _ _ _ _ => Subsingleton.elim _ _

/-- Over the one-point base, the natural map `N₁(X/Spec k) → N₁(X)` is bijective. -/
private theorem relativeToAbsolute_self_bijective {X : Scheme.{0}} (sX : X ⟶ Spec (.of k)) :
    Function.Bijective (relativeToAbsolute sX sX) :=
  ⟨(existsUnique_isNaturalRelativeMap_and_injective sX sX).2 _
      (isNaturalRelativeMap_relativeToAbsolute sX sX),
    fun w => by
      obtain ⟨Z, rfl⟩ := OneCycle.numericalClass_surjective sX w
      exact ⟨relativeNumericalClass sX sX ⟨Z, mem_relativeOneCycles_self Z⟩, rfl⟩⟩

/-- A contraction of a face is surjective. -/
private theorem surjective_of_isContractionOfFace {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
    {sY : Y ⟶ Spec (.of k)} {F : Set (NumericalCurveClasses sX)} {g : X ⟶ Y}
    (hg : IsContractionOfFace k sX sY F g) : Surjective g := by
  have hY := hg.isProjectiveVariety_target
  haveI : IsIntegral Y := hY.toIsVariety.toIsIntegral
  haveI : IsSeparated sY := hY.toIsVariety.toIsSeparated
  haveI : IsProper sX :=
    isProper_of_isProjectiveMorphism sX hg.isProjectiveVariety_source.isProjective
  haveI : IsProper (g ≫ sY) := by
    rw [hg.comp_eq]
    infer_instance
  haveI : IsProper g := IsProper.of_comp g sY
  haveI := MMP.Flips.isDominant_of_forall_isIso_app g hg.isIso_app
  infer_instance

/-- The push-forward `g_* : N₁(X) → N₁(Y)` along a contraction is surjective: every curve of `Y`
is, up to a positive multiple, the push-forward of a curve of `X`. -/
private theorem surjective_pushforward {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
    {sY : Y ⟶ Spec (.of k)} {F : Set (NumericalCurveClasses sX)} {g : X ⟶ Y}
    [IsSeparated sY] [LocallyOfFiniteType sY] (hg : IsContractionOfFace k sX sY F g) :
    Function.Surjective (NumericalCurveClasses.pushforward g hg.comp_eq) := by
  haveI := surjective_of_isContractionOfFace hg
  obtain ⟨φ, hφ, hsurj, -⟩ := exists_relativeNumericalPushforward_of_surjective
    hg.isProjectiveVariety_source hg.isProjectiveVariety_target isProjectiveVariety_id
    (Category.comp_id sX) (Category.comp_id sY) hg.comp_eq
  intro w
  obtain ⟨Z', rfl⟩ := OneCycle.numericalClass_surjective sY w
  obtain ⟨u, hu⟩ := hsurj (relativeNumericalClass sY sY ⟨Z', mem_relativeOneCycles_self Z'⟩)
  obtain ⟨⟨Z, hZ⟩, rfl⟩ := relativeNumericalClass_surjective sX sX u
  refine ⟨OneCycle.numericalClass sX Z, ?_⟩
  have h1 := hφ ⟨Z, hZ⟩ ⟨_, mem_relativeOneCycles_self (OneCycle.pushforward ℝ sX sY g Z)⟩ rfl
  exact congrArg (relativeToAbsolute sY sY) (h1.symm.trans hu)

/-- Every element of an extremal ray is a multiple of any nonzero element of it. -/
private theorem exists_eq_smul_of_mem {V : Type*} [AddCommGroup V] [Module ℝ V] {N R : Set V}
    (hR : IsExtremalRay ℝ N R) {a x : V} (ha : a ∈ R) (ha0 : a ≠ 0) (hx : x ∈ R) :
    ∃ t : ℝ, x = t • a := by
  obtain ⟨-, v, -, rfl⟩ := hR
  obtain ⟨c, -, rfl⟩ := hx
  obtain ⟨ca, -, rfl⟩ := ha
  have hca : ca ≠ 0 := by
    rintro rfl
    exact ha0 (zero_smul ℝ v)
  exact ⟨c / ca, by rw [smul_smul, div_mul_cancel₀ c hca]⟩

/-- Over the one-point base, `NE̅(X/Spec k)` maps onto `NE̅(X)`. -/
private theorem image_relativeToAbsolute_self [IsAlgClosed k] [CharZero k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [AlgebraicGeometry.IsProjectiveVariety k sX] :
    relativeToAbsolute sX sX '' (relativeClosedConeOfCurves sX sX : Set _) =
      (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) := by
  haveI : AlgebraicGeometry.IsProjectiveVariety k (𝟙 (Spec (.of k))) := isProjectiveVariety_id
  have := image_relativeClosedConeOfCurves_eq_inter_range sX (𝟙 (Spec (.of k))) sX
    (Category.comp_id sX)
  rwa [(relativeToAbsolute_self_bijective sX).2.range_eq, Set.inter_univ] at this

/-- Over the one-point base, a contraction of an extremal ray `R` of `NE̅(X)` is a relative
contraction of the corresponding ray of `NE̅(X/Spec k)`. -/
private theorem isRelativeContractionOfFace_preimage [IsAlgClosed k] [CharZero k]
    {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [AlgebraicGeometry.IsProjectiveVariety k sX]
    {sY : Y ⟶ Spec (.of k)} {R : Set (NumericalCurveClasses sX)}
    (hR : IsExtremalRay ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) R)
    {g : X ⟶ Y} (hg : IsContractionOfFace k sX sY R g) :
    IsRelativeContractionOfFace sX (relativeToAbsolute sX sX ⁻¹' R) g sY where
  isExtremalFace := by
    set E := LinearEquiv.ofBijective _ (relativeToAbsolute_self_bijective sX)
    have himg : E '' (relativeClosedConeOfCurves sX sX : Set _) =
        (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) :=
      image_relativeToAbsolute_self sX
    have h := (MMP.ProgramBaseChange.isExtremalRay_image E.symm hR).1
    rwa [← himg, ← Set.image_comp, show ⇑E.symm ∘ ⇑E = id from funext E.symm_apply_apply,
      Set.image_id, LinearEquiv.image_symm_eq_preimage] at h
  isProjectiveMorphism := hg.isProjectiveVariety_target.isProjective
  comp_eq := hg.comp_eq
  isIso_app := hg.isIso_app
  isContractedBy_iff C _ := hg.isContractedBy_iff C

/-- A contraction of a face kills the class of every curve whose class lies in the face. -/
private theorem pushforward_eq_zero_of_mem {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
    {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY]
    {F : Set (NumericalCurveClasses sX)} {g : X ⟶ Y} (hg : IsContractionOfFace k sX sY F g)
    {C : ProperCurve sX} (hCF : OneCycle.numericalClass sX (C.cycle ℝ) ∈ F) :
    NumericalCurveClasses.pushforward g hg.comp_eq (OneCycle.numericalClass sX (C.cycle ℝ)) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr (OneCycle.mem_numericallyTrivial.mpr fun L _ => by
    rw [OneCycle.degree_pushforward g hg.comp_eq, OneCycle.degree_cycle,
      ProperCurve.degree_pullback_eq_zero_of_isContractedBy g hg.comp_eq C
        ((hg.isContractedBy_iff C).mpr hCF) L, Int.cast_zero])

section CartierForm

variable {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  (sX : X ⟶ Spec (.of k))

/-- The degree form `z ↦ (D · z)` on `N₁(X)` of a Cartier divisor `D`. -/
private noncomputable def cartierForm (D : Divisor X) (hD : D.IsCartier) :
    NumericalCurveClasses sX →ₗ[ℝ] ℝ :=
  haveI := hD.isInvertibleModule_divisorialSheaf
  NumericalCurveClasses.degree sX D.divisorialSheaf

variable [QuasiCompact sX]

private theorem cartierForm_numericalClass_cycle (D : Divisor X) (hD : D.IsCartier)
    (C : ProperCurve sX) :
    cartierForm sX D hD (OneCycle.numericalClass sX (C.cycle ℝ)) =
      (D.degreeOn k sX C.ι C.dim_le hD : ℝ) := by
  haveI := hD.isInvertibleModule_divisorialSheaf
  exact OneCycle.degree_cycle ℝ D.divisorialSheaf C

private theorem cartierForm_zsmul_add (D E : Divisor X) (hD : D.IsCartier) (hE : E.IsCartier)
    (m n : ℤ) (z : NumericalCurveClasses sX) :
    cartierForm sX (m • D + n • E) ((hD.zsmul m).add (hE.zsmul n)) z =
      m * cartierForm sX D hD z + n * cartierForm sX E hE z := by
  have h : cartierForm sX (m • D + n • E) ((hD.zsmul m).add (hE.zsmul n)) =
      (m : ℝ) • cartierForm sX D hD + (n : ℝ) • cartierForm sX E hE := by
    refine MMP.ProgramBaseChange.linearMap_ext_numericalClass_cycle sX fun C => ?_
    rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply,
      cartierForm_numericalClass_cycle, cartierForm_numericalClass_cycle,
      cartierForm_numericalClass_cycle, Divisor.degreeOn_add k sX C.ι C.dim_le _ _ (hD.zsmul m)
        (hE.zsmul n), MMP.Fourfold.degreeOn_zsmul sX C.ι C.dim_le D hD m,
      MMP.Fourfold.degreeOn_zsmul sX C.ι C.dim_le E hE n]
    push_cast
    simp [smul_eq_mul]
  simp [h]

private theorem cartierForm_eq_degree_of_iso (D : Divisor X) (hD : D.IsCartier) {L : X.Modules}
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (e : D.divisorialSheaf ≅ L) :
    cartierForm sX D hD = NumericalCurveClasses.degree sX L := by
  haveI := hD.isInvertibleModule_divisorialSheaf
  refine MMP.ProgramBaseChange.linearMap_ext_numericalClass_cycle sX fun C => ?_
  change OneCycle.degree ℝ sX D.divisorialSheaf (C.cycle ℝ) = OneCycle.degree ℝ sX L (C.cycle ℝ)
  rw [OneCycle.degree_cycle, OneCycle.degree_cycle, ProperCurve.degree, ProperCurve.degree,
    degreeOn_eq_of_iso k sX C.ι C.dim_le e]

variable [IsIntegral X]

/-- The degree forms of Cartier divisors separate the points of `N₁(X)`. -/
private theorem exists_cartierForm_ne_zero {w : NumericalCurveClasses sX} (hw : w ≠ 0) :
    ∃ (D : Divisor X) (hD : D.IsCartier), cartierForm sX D hD w ≠ 0 := by
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  obtain ⟨Z, rfl⟩ := OneCycle.numericalClass_surjective sX w
  refine hw ((Submodule.Quotient.mk_eq_zero _).mpr
    (OneCycle.mem_numericallyTrivial.mpr fun L _ => ?_))
  obtain ⟨D, hD, ⟨e⟩⟩ := exists_isCartier_divisorialSheaf_iso L
  have := hcon D hD
  rwa [cartierForm_eq_degree_of_iso sX D hD e] at this

/-- **The kernel step of KM 3.17.** A class `z ∈ N₁(X)` on which every Cartier divisor of degree
zero on the curve `C` has degree zero is a multiple of `[C]`. Otherwise, choose `D₀` with
`(D₀ · C) ≠ 0` and `D₁` with `(D₁ · ((D₀ · C) z - (D₀ · z) [C])) ≠ 0`; then
`(D₀ · C) D₁ - (D₁ · C) D₀` has degree zero on `C` but not on `z`. -/
private theorem mem_span_of_forall_cartierForm_eq_zero {C : ProperCurve sX}
    (hC : OneCycle.numericalClass sX (C.cycle ℝ) ≠ 0) {z : NumericalCurveClasses sX}
    (hz : ∀ (M : Divisor X) (hM : M.IsCartier),
      cartierForm sX M hM (OneCycle.numericalClass sX (C.cycle ℝ)) = 0 →
        cartierForm sX M hM z = 0) :
    z ∈ Submodule.span ℝ {OneCycle.numericalClass sX (C.cycle ℝ)} := by
  set a := OneCycle.numericalClass sX (C.cycle ℝ)
  by_contra hza
  obtain ⟨D₀, hD₀, h0⟩ := exists_cartierForm_ne_zero sX hC
  have hw : cartierForm sX D₀ hD₀ a • z - cartierForm sX D₀ hD₀ z • a ≠ 0 := by
    intro hw0
    refine hza (Submodule.mem_span_singleton.mpr
      ⟨(cartierForm sX D₀ hD₀ a)⁻¹ * cartierForm sX D₀ hD₀ z, ?_⟩)
    rw [mul_smul, ← sub_eq_zero.mp hw0, smul_smul, inv_mul_cancel₀ h0, one_smul]
  obtain ⟨D₁, hD₁, h1⟩ := exists_cartierForm_ne_zero sX hw
  set n₀ := D₀.degreeOn k sX C.ι C.dim_le hD₀
  set n₁ := D₁.degreeOn k sX C.ι C.dim_le hD₁
  have hl₀ : cartierForm sX D₀ hD₀ a = n₀ := cartierForm_numericalClass_cycle sX D₀ hD₀ C
  have hl₁ : cartierForm sX D₁ hD₁ a = n₁ := cartierForm_numericalClass_cycle sX D₁ hD₁ C
  have h := hz _ ((hD₁.zsmul n₀).add (hD₀.zsmul (-n₁)))
    (by
      rw [cartierForm_zsmul_add sX D₁ D₀ hD₁ hD₀, hl₀, hl₁]
      push_cast
      ring)
  rw [cartierForm_zsmul_add sX D₁ D₀ hD₁ hD₀] at h
  apply h1
  rw [map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hl₀, hl₁]
  push_cast at h ⊢
  linarith

end CartierForm

/-- If `e` maps the cone spanned by `f` into `N`, and `R` is a face of `N` stable under positive
scaling, then every element of the cone mapped into `R` is mapped to zero, or some generator is
mapped to a nonzero element of `R`. -/
private theorem eq_zero_or_exists_of_mem_hull {V W ι : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (e : V →ₗ[ℝ] W) (f : ι → V) {N R : Set W}
    (hN : ∀ y ∈ PointedCone.hull ℝ (Set.range f), e y ∈ N)
    (hRs : ∀ v ∈ R, ∀ c : ℝ, 0 < c → c • v ∈ R)
    (hRext : ∀ u ∈ N, ∀ v ∈ N, u + v ∈ R → u ∈ R ∧ v ∈ R) :
    ∀ y ∈ PointedCone.hull ℝ (Set.range f), e y ∈ R → e y = 0 ∨ ∃ j, e (f j) ∈ R ∧ e (f j) ≠ 0 := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact fun hj => or_iff_not_imp_left.mpr fun h0 => ⟨j, hj, h0⟩
  | zero => exact fun _ => Or.inl (map_zero e)
  | add x y hx hy ihx ihy =>
    intro hxy
    rw [map_add] at hxy
    obtain ⟨hxF, hyF⟩ := hRext _ (hN x hx) _ (hN y hy) hxy
    rcases ihx hxF with h1 | h1
    · rcases ihy hyF with h2 | h2
      · exact Or.inl (by rw [map_add, h1, h2, add_zero])
      · exact Or.inr h2
    · exact Or.inr h1
  | smul c x hx ihx =>
    intro hcx
    by_cases hc : c = 0
    · exact Or.inl (by rw [hc, zero_smul, map_zero])
    · have hc' : (0 : ℝ) < c := lt_of_le_of_ne c.2 fun h => hc (Subtype.ext h.symm)
      have hcx' : e (c • x) = (c : ℝ) • e x := map_smul e (c : ℝ) x
      have hxF : e x ∈ R := by
        have h1 := hRs _ hcx ((c : ℝ)⁻¹) (inv_pos.mpr hc')
        rwa [hcx', smul_smul, inv_mul_cancel₀ hc'.ne', one_smul] at h1
      rcases ihx hxF with h1 | h1
      · exact Or.inl (by rw [hcx', h1, smul_zero])
      · exact Or.inr h1

/-- A `(K + Δ)`-negative extremal ray of a projective `ℚ`-factorial dlt pair is spanned by the
class of a curve: by the dlt cone theorem over `Spec k`. -/
private theorem exists_curve [IsAlgClosed k] [CharZero k] {X : Scheme.{0}}
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)}
    [AlgebraicGeometry.IsProjectiveVariety k sX] {n : ℕ} {K : Divisor X}
    {Δ : QDivisor X} (hdlt : IsDltPair sX n K Δ) (hQ : MMP.Fourfold.IsQFactorial sX)
    {R : Set (NumericalCurveClasses sX)}
    (hR : IsExtremalRay ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) R)
    (hneg : ∀ z ∈ R, z ≠ 0 →
      MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hdlt.1.2.2 z < 0) :
    ∃ C : ProperCurve sX, OneCycle.numericalClass sX (C.cycle ℝ) ∈ R ∧
      OneCycle.numericalClass sX (C.cycle ℝ) ≠ 0 := by
  classical
  haveI : AlgebraicGeometry.IsProjectiveVariety k (𝟙 (Spec (.of k))) := isProjectiveVariety_id
  obtain ⟨ι, -, C, hC, -, -, hdec⟩ := IsDltPair.exists_relativeClosedConeOfCurves_eq_add_hull
    (𝟙 (Spec (.of k))) sX (Category.comp_id sX) hdlt hQ
  have himg := image_relativeToAbsolute_self sX
  set e := relativeToAbsolute sX sX
  have hmemN : ∀ u ∈ (relativeClosedConeOfCurves sX sX : Set _),
      e u ∈ (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) :=
    fun u hu => himg ▸ ⟨u, hu, rfl⟩
  obtain ⟨⟨hRN, ⟨-, hRs⟩, -, hRext⟩, v, hv0, hRv⟩ := hR
  have hvR : v ∈ R := hRv ▸ ⟨1, zero_le_one, one_smul _ _⟩
  obtain ⟨u, hu, rfl⟩ : v ∈ e '' (relativeClosedConeOfCurves sX sX : Set _) :=
    himg ▸ hRN hvR
  set H := PointedCone.hull ℝ (Set.range fun j => (C j).relativeClass sX (hC j))
  have hHN : ∀ y ∈ H, y ∈ (relativeClosedConeOfCurves sX sX : Set _) := fun y hy => by
    change y ∈ (relativeClosedConeOfCurves sX sX : Set _)
    rw [hdec]
    exact ⟨0, ⟨(relativeClosedConeOfCurves sX sX).zero_mem, by simp⟩, y, hy, zero_add y⟩
  rw [hdec] at hu
  obtain ⟨a, ⟨haN, ha0⟩, h', hh, hah⟩ := hu
  replace hah : a + h' = u := hah
  have hsum : e a + e h' ∈ R := by rwa [← map_add, hah]
  obtain ⟨haR, hhR⟩ := hRext _ (hmemN a haN) _ (hmemN h' (hHN h' hh)) hsum
  have ha : e a = 0 := by
    by_contra ha
    have h1 := hneg _ haR ha
    have h2 : MMP.Fourfold.QDivisor.relativeCurveForm sX sX (Divisor.toQDivisor K + Δ)
        hdlt.1.2.2 a =
        MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hdlt.1.2.2 (e a) := by
      rw [QDivisor.relativeCurveForm_eq_comp]
      rfl
    exact absurd ha0 (not_le.mpr (h2 ▸ h1))
  rcases eq_zero_or_exists_of_mem_hull e _ (fun y hy => hmemN y (hHN y hy)) hRs hRext h' hh hhR
    with h0 | ⟨j, hjR, hj0⟩
  · exact absurd (by rw [← hah, map_add, ha, h0, add_zero]) hv0
  · exact ⟨C j, hjR, hj0⟩

/-- **The projection formula step of KM 3.17.** Let `R = ℝ_{≥0} [C]` be a `(K + Δ)`-negative
extremal ray of a projective `ℚ`-factorial dlt pair and `g` a contraction of `R`. A Cartier
divisor `M` of degree zero on `C` is, by the dlt contraction theorem, a pull-back `g^* L`, so
`(M · z) = (L · g_* z)` vanishes on the kernel of `g_*`. -/
private theorem cartierForm_eq_zero_of_pushforward_eq_zero [IsAlgClosed k] [CharZero k]
    {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sX : X ⟶ Spec (.of k)} [AlgebraicGeometry.IsProjectiveVariety k sX]
    {n : ℕ} {K : Divisor X} {Δ : QDivisor X} (hdlt : IsDltPair sX n K Δ)
    (hQ : MMP.Fourfold.IsQFactorial sX) {R : Set (NumericalCurveClasses sX)}
    (hR : IsExtremalRay ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) R)
    (hneg : ∀ z ∈ R, z ≠ 0 →
      MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hdlt.1.2.2 z < 0)
    {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY]
    {g : X ⟶ Y} (hg : IsContractionOfFace k sX sY R g) {C : ProperCurve sX}
    (hCR : OneCycle.numericalClass sX (C.cycle ℝ) ∈ R)
    (hC0 : OneCycle.numericalClass sX (C.cycle ℝ) ≠ 0) (M : Divisor X) (hM : M.IsCartier)
    (hMC : cartierForm sX M hM (OneCycle.numericalClass sX (C.cycle ℝ)) = 0)
    {z : NumericalCurveClasses sX} (hz : NumericalCurveClasses.pushforward g hg.comp_eq z = 0) :
    cartierForm sX M hM z = 0 := by
  haveI : AlgebraicGeometry.IsProjectiveVariety k (𝟙 (Spec (.of k))) := isProjectiveVariety_id
  haveI := hM.isInvertibleModule_divisorialSheaf
  have hdeg (C' : ProperCurve sX) (hC' : OneCycle.numericalClass sX (C'.cycle ℝ) ∈ R) :
      M.degreeOn k sX C'.ι C'.dim_le hM = 0 := by
    obtain ⟨t, ht⟩ := exists_eq_smul_of_mem hR hCR hC0 hC'
    have h := cartierForm_numericalClass_cycle sX M hM C'
    rw [ht, map_smul, hMC, smul_zero] at h
    exact_mod_cast h.symm
  obtain ⟨L, hL, ⟨e⟩⟩ :=
    IsDltPair.exists_isInvertible_nonempty_iso_pullback_of_isRelativeContractionOfFace
      (𝟙 (Spec (.of k))) sX (Category.comp_id sX) hdlt hQ
      (fun w hw hw0 => by
        rw [QDivisor.relativeCurveForm_eq_comp]
        exact hneg _ hw fun h =>
          hw0 ((relativeToAbsolute_self_bijective sX).1 (h.trans (map_zero _).symm)))
      (isRelativeContractionOfFace_preimage hR hg) M.divisorialSheaf
      (fun C' _ hC' => hdeg C' hC')
  haveI := hL
  rw [cartierForm_eq_degree_of_iso sX M hM e,
    ← NumericalCurveClasses.degree_pushforward g hg.comp_eq, hz, map_zero]

end Helpers

/-- **Contracting a negative extremal ray of a `ℚ`-factorial dlt pair drops the Picard number
by one** (Kollár–Mori 3.36(2)). Let `(X, Δ)` be a projective `ℚ`-factorial dlt pair over an
algebraically closed field of characteristic zero, `R` an extremal ray of `NE̅(X)` with
`((K + Δ) · z) < 0` for every nonzero `z ∈ R`, and `g : X ⟶ Y` a contraction of `R`. Then
`ρ(Y) + 1 = ρ(X)`. -/
@[mmp "prop_km3c_divisorial_or_fano_contraction_picard_number"]
public theorem IsDltPair.picardNumber_add_one_eq_of_isContractionOfFace {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] {sX : X ⟶ Spec (.of k)} [AlgebraicGeometry.IsProjectiveVariety k sX] {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    (hdlt : IsDltPair sX n K Δ) (hQ : MMP.Fourfold.IsQFactorial sX)
    {R : Set (NumericalCurveClasses sX)}
    (hR : IsExtremalRay ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) R)
    (hneg : ∀ z ∈ R, z ≠ 0 →
      MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hdlt.1.2.2 z < 0)
    {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of k)} {g : X ⟶ Y} (hg : IsContractionOfFace k sX sY R g) :
    picardNumber sY + 1 = picardNumber sX := by
  haveI : IsSeparated sY := hg.isProjectiveVariety_target.toIsVariety.toIsSeparated
  haveI : LocallyOfFiniteType sY := hg.isProjectiveVariety_target.toIsVariety.toLocallyOfFiniteType
  obtain ⟨C, hCR, hC0⟩ := exists_curve hdlt hQ hR hneg
  have hker : LinearMap.ker (NumericalCurveClasses.pushforward g hg.comp_eq) =
      Submodule.span ℝ {OneCycle.numericalClass sX (C.cycle ℝ)} :=
    le_antisymm (fun z hz => mem_span_of_forall_cartierForm_eq_zero sX hC0 fun M hM hMC =>
        cartierForm_eq_zero_of_pushforward_eq_zero hdlt hQ hR hneg hg hCR hC0 M hM hMC hz)
      ((Submodule.span_singleton_le_iff_mem _ _).mpr (pushforward_eq_zero_of_mem hg hCR))
  have hrank := LinearMap.rank_range_add_rank_ker (NumericalCurveClasses.pushforward g hg.comp_eq)
  rw [LinearMap.range_eq_top.mpr (surjective_pushforward hg), rank_top, hker,
    rank_span_set ((linearIndepOn_singleton_iff (R := ℝ)
      (v := (id : NumericalCurveClasses sX → NumericalCurveClasses sX))).mpr hC0),
    Cardinal.mk_singleton] at hrank
  rw [picardNumber, picardNumber, ← hrank]
  simp

end MMP.Mori
