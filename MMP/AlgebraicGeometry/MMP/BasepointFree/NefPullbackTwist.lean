module

public import MMP.AlgebraicGeometry.MMP.ConeTheorem.AmplePerturbationFiniteRays

section

/-!
# A large pull-back twist makes an `f`-nef divisor nef

Let `(X, Δ)` be a klt pair with `Δ ≥ 0` and `f : X ⟶ Y` a morphism of projective varieties over
an algebraically closed field of characteristic zero. Let `H` be an ample Cartier divisor on `Y`,
`G` a Cartier divisor on `X` with `𝒪_X(G) ≅ f^*𝒪_Y(H)`, `D` an `f`-nef Cartier divisor and
`a > 0` rational with `A' = aD - K_X - Δ` ample. Then `D + mG` is nef for `m ≫ 0`.

Since `aD = K_X + Δ + A'`, the cone theorem gives
`NE̅(X) = NE̅(X)_{aD ≥ 0} + ∑_{C ∈ S} ℝ_{≥0}[C]` for a finite set `S` of curves. The form of `G`
is nonnegative on `NE̅(X)`, and at least one on every curve not contracted by `f`; on a curve
contracted by `f`, `D` is nonnegative. So `D + mG` is nonnegative on each `[C]`, `C ∈ S`, as soon
as `m ≥ -(D · C)`, and it is nonnegative on `NE̅(X)_{aD ≥ 0}` for every `m ≥ 0`. Hence it is
nonnegative on `NE̅(X)`, in particular on every curve.

## Main results

* `MMP.Mori.exists_forall_ge_isNef_add_nsmul_pullback`: the statement above.

## Implementation notes

The pull-back `f^*H` enters only through its invertible sheaf: it is a Cartier divisor `G` on `X`
with `𝒪_X(G) ≅ f^*𝒪_Y(H)`. Such a `G` is determined up to linear equivalence, which does not
change nefness, and it exists without moving `H` off the image of the generic point of `X`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 3.26
-/

open AlgebraicGeometry CategoryTheory MMP.Mori MMP.Fourfold

namespace MMP.FourfoldProofs.Km3bRelativeBpfMakeNefProof

variable {k : Type} [Field k] {X : Scheme.{0}}

/-- An integral one-dimensional closed subscheme `i : C ⟶ X`, proper over `k`, is a proper curve
`T` of `X`, with `C ≅ T` over `X`. -/
private theorem exists_properCurve_iso {sX : X ⟶ Spec (.of k)} {C : Scheme.{0}} (i : C ⟶ X)
    [IsClosedImmersion i] [IsIntegral C] [IsProper (i ≫ sX)] (hC : topologicalKrullDim C = 1) :
    ∃ (T : ProperCurve sX) (e : C ≅ T.scheme), e.hom ≫ T.ι = i := by
  set x := i (genericPoint C) with hx
  have hrange : Set.range i = closure {x} := by
    rw [hx, ← Set.image_singleton, i.isClosedEmbedding.closure_image_eq,
      (genericPoint_spec C).def]
    simp
  have hker : i.ker = (curveSubschemeAtι x).ker := by
    rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range, Scheme.IdealSheafData.ker_subschemeι]
    congr 1
    apply TopologicalSpace.Closeds.ext
    rw [TopologicalSpace.Closeds.coe_closure, TopologicalSpace.Closeds.coe_closure, hrange,
      closure_closure]
  haveI : IsIso (IsClosedImmersion.lift (curveSubschemeAtι x) i hker.ge) :=
    IsClosedImmersion.isIso_of_ker_eq i (curveSubschemeAtι x) _
      (IsClosedImmersion.lift_fac _ _ _) hker
  let e : C ≅ curveSubschemeAt x := asIso (IsClosedImmersion.lift (curveSubschemeAtι x) i hker.ge)
  have he : e.hom ≫ curveSubschemeAtι x = i := IsClosedImmersion.lift_fac _ _ _
  have hdim : topologicalKrullDim (curveSubschemeAt x) = 1 := by
    rw [← (Scheme.homeoOfIso e).isHomeomorph.topologicalKrullDim_eq, hC]
  have hprop : IsProper (curveSubschemeAtι x ≫ sX) := by
    rw [← (Iso.inv_comp_eq e).mpr he.symm, Category.assoc]
    infer_instance
  exact ⟨⟨x, ⟨hdim, hprop⟩⟩, e, he⟩

variable {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]

/-- The intersection number along a curve is unchanged by an isomorphism of curves over `X`. -/
private theorem intersectionNumber_eq_of_iso {C C' : Scheme.{0}} (i : C ⟶ X) (i' : C' ⟶ X)
    [IsProper (i ≫ sX)] [IsProper (i' ≫ sX)] (hdim : topologicalKrullDim C ≤ 1)
    (hdim' : topologicalKrullDim C' ≤ 1) (e : C ≅ C') (he : e.hom ≫ i' = i) {D : QDivisor X}
    (hD : D.IsQCartier) :
    D.intersectionNumber k sX i hdim hD = D.intersectionNumber k sX i' hdim' hD := by
  have := QuasiCompact.compactSpace_of_compactSpace sX
  have := (QDivisor.isCartierDivisor_cartierIndex_smul hD).isCartier_toDivisor
    |>.isInvertibleModule_divisorialSheaf
  simp only [QDivisor.intersectionNumber, Divisor.degreeOn]
  rw [MMP.Threefold.Resolution.degreeOn_eq_of_iso_comp k sX i i' hdim hdim' e he]

/-- If `𝒪_X(G) ≅ M`, then `(G · T) = deg_T M`. -/
private theorem intersectionNumber_toQDivisor_eq_degree_of_iso {G : Divisor X} (hGc : G.IsCartier)
    {M : X.Modules} [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]
    (hG : Nonempty (G.divisorialSheaf ≅ M)) (T : ProperCurve sX) :
    (Divisor.toQDivisor G).intersectionNumber k sX T.ι T.dim_le
        (QDivisor.isQCartier_toQDivisor hGc) = T.degree k M := by
  rw [QDivisor.intersectionNumber_toQDivisor k sX T.ι T.dim_le G hGc]
  have := QuasiCompact.compactSpace_of_compactSpace sX
  have := hGc.isInvertibleModule_divisorialSheaf
  obtain ⟨e⟩ := hG
  show ((degreeOn k sX T.ι T.dim_le G.divisorialSheaf : ℤ) : ℚ) = _
  rw [degreeOn_eq_of_iso k sX T.ι T.dim_le e]
  rfl

/-- The linear form of a `ℚ`-Cartier divisor is continuous for the numerical topology. -/
private theorem continuous_curveForm [CompactSpace X] (D : QDivisor X) (h : D.IsQCartier) :
    Continuous (QDivisor.curveForm sX D h) := by
  unfold QDivisor.curveForm Finsupp.sum
  refine Finset.sum_induction _ (fun g : NumericalCurveClasses sX →ₗ[ℝ] ℝ => Continuous g)
    (fun a b ha hb => ?_) ?_ fun E _ => ?_
  · rw [LinearMap.coe_add]
    exact ha.add hb
  · exact (continuous_const : Continuous fun _ : NumericalCurveClasses sX => (0 : ℝ))
  · haveI := (Divisor.mem_cartierSubgroup.mp E.2).isInvertibleModule_divisorialSheaf
    rw [LinearMap.coe_smul]
    exact (NumericalCurveClasses.continuous_degree sX _).const_smul _

/-- A linear form nonnegative on a set is nonnegative on its cone hull. -/
private theorem nonneg_of_mem_hull {E : Type*} [AddCommGroup E] [Module ℝ E] {φ : E →ₗ[ℝ] ℝ}
    {s : Set E} (hs : ∀ x ∈ s, 0 ≤ φ x) {z : E} (hz : z ∈ PointedCone.hull ℝ s) : 0 ≤ φ z :=
  (Submodule.span_le (p := (PointedCone.positive ℝ ℝ).comap φ)).mpr hs hz

/-- A `ℚ`-Cartier divisor nonnegative on every proper curve is nonnegative on `NE̅(X)`. -/
private theorem curveForm_nonneg_of_mem_closedConeOfCurves [CompactSpace X] (D : QDivisor X)
    (h : D.IsQCartier)
    (hD : ∀ T : ProperCurve sX,
      0 ≤ QDivisor.curveForm sX D h (OneCycle.numericalClass sX (T.cycle ℝ)))
    {z : NumericalCurveClasses sX} (hz : z ∈ closedConeOfCurves sX) :
    0 ≤ QDivisor.curveForm sX D h z :=
  closure_minimal (t := {z | 0 ≤ QDivisor.curveForm sX D h z})
    (fun _ hx => nonneg_of_mem_hull (s := Set.range fun T : ProperCurve sX =>
      OneCycle.numericalClass sX (T.cycle ℝ)) (by rintro _ ⟨T, rfl⟩; exact hD T) hx)
    (isClosed_le continuous_const (continuous_curveForm D h)) hz

/-- If `E₁ + E₂ = a • F`, then the forms satisfy `E₁ + E₂ = a • F` on `N₁(X)`. -/
private theorem curveForm_add_eq_smul [CompactSpace X] {E₁ E₂ F : QDivisor X}
    (h₁ : E₁.IsQCartier) (h₂ : E₂.IsQCartier) (hF : F.IsQCartier) {a : ℚ}
    (haF : (a • F).IsQCartier) (h : E₁ + E₂ = a • F) :
    QDivisor.curveForm sX E₁ h₁ + QDivisor.curveForm sX E₂ h₂ =
      (a : ℝ) • QDivisor.curveForm sX F hF := by
  refine MMP.ProgramBaseChange.linearMap_ext_numericalClass_cycle sX fun T => ?_
  rw [LinearMap.add_apply, LinearMap.smul_apply,
    MMP.ProgramBaseChange.curveForm_numericalClass_cycle,
    MMP.ProgramBaseChange.curveForm_numericalClass_cycle,
    MMP.ProgramBaseChange.curveForm_numericalClass_cycle, smul_eq_mul]
  have h₃ := QDivisor.intersectionNumber_add' k sX T.ι T.dim_le _ _ h₁ h₂ (h₁.add h₂)
  rw [MMP.Fourfold.intersectionNumber_congr sX T.ι T.dim_le _ haF h,
    MMP.Fourfold.intersectionNumber_smul sX T.ι T.dim_le _ hF a haF] at h₃
  rw [← Rat.cast_add, ← h₃, Rat.cast_mul]

omit [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X] in
/-- The degree of the pull-back of an ample Cartier divisor `A` on a projective variety `Z` along
a morphism over `k` is nonnegative on every proper curve, and at least one on a curve that is not
contracted. -/
private theorem degree_pullback_nonneg_and_one_le_of_not_isContractedBy {Z : Scheme.{0}}
    {sZ : Z ⟶ Spec (.of k)} [AlgebraicGeometry.IsProjectiveVariety k sZ] {f : X ⟶ Z}
    (hf : f ≫ sZ = sX) (A : Z.CartierDivisor)
    (hA : Stacks.Ample.IsAmple Z (MMP.CartierDivisor.sheaf A))
    (T : ProperCurve sX) :
    0 ≤ T.degree k ((Scheme.Modules.pullback f).obj (MMP.CartierDivisor.sheaf A)) ∧
      (¬ T.IsContractedBy f → 1 ≤ T.degree k ((Scheme.Modules.pullback f).obj
        (MMP.CartierDivisor.sheaf A))) := by
  have hpos : ∀ h : IsProperCurve sZ (f T.point),
      0 < (⟨f T.point, h⟩ : ProperCurve sZ).degree k (MMP.CartierDivisor.sheaf A) :=
    fun h => MMP.Threefold.Mori.degreeOn_cartierSheaf_pos_of_isAmple inferInstance A hA _
  have hnn : 0 ≤ T.degree k ((Scheme.Modules.pullback f).obj
      (MMP.CartierDivisor.sheaf A)) := by
    rw [ProperCurve.degree_pullback f hf T]
    split_ifs with h
    · exact mul_nonneg (Nat.cast_nonneg _) (hpos h).le
    · exact le_rfl
  refine ⟨hnn, fun hc => ?_⟩
  have hAmp : Scheme.Modules.IsAmple Z (MMP.CartierDivisor.sheaf A) :=
    (Stacks.AmpleBridge.isAmple_iff_isAmple Z _).mp hA
  have hne : T.degree k ((Scheme.Modules.pullback f).obj
      (MMP.CartierDivisor.sheaf A)) ≠ 0 := fun h0 =>
    hc (MMP.ProgramBaseChange.isContractedBy_of_degree_pullback_eq_zero f hf _ hAmp T h0)
  omega

/-- If `𝒪_X(G) ≅ f^*𝒪_Z(A)` with `A` ample on a projective variety `Z`, the form of `G` is
nonnegative on `NE̅(X)` and at least one on every curve not contracted by `f`. -/
private theorem curveForm_nonneg_and_one_le_of_iso_pullback [CompactSpace X] {Z : Scheme.{0}}
    {sZ : Z ⟶ Spec (.of k)} [AlgebraicGeometry.IsProjectiveVariety k sZ] {f : X ⟶ Z}
    (hf : f ≫ sZ = sX) (A : Z.CartierDivisor)
    (hA : Stacks.Ample.IsAmple Z (MMP.CartierDivisor.sheaf A)) {G : Divisor X} (hGc : G.IsCartier)
    (hG : Nonempty (G.divisorialSheaf ≅
      (Scheme.Modules.pullback f).obj (MMP.CartierDivisor.sheaf A))) :
    (∀ z ∈ closedConeOfCurves sX, 0 ≤ QDivisor.curveForm sX (Divisor.toQDivisor G)
        (QDivisor.isQCartier_toQDivisor hGc) z) ∧
      ∀ T : ProperCurve sX, ¬ T.IsContractedBy f → 1 ≤ QDivisor.curveForm sX
        (Divisor.toQDivisor G) (QDivisor.isQCartier_toQDivisor hGc)
          (OneCycle.numericalClass sX (T.cycle ℝ)) := by
  have gT : ∀ T : ProperCurve sX, QDivisor.curveForm sX (Divisor.toQDivisor G)
      (QDivisor.isQCartier_toQDivisor hGc) (OneCycle.numericalClass sX (T.cycle ℝ)) =
        (T.degree k ((Scheme.Modules.pullback f).obj (MMP.CartierDivisor.sheaf A)) : ℝ) :=
    fun T => by
      rw [MMP.ProgramBaseChange.curveForm_numericalClass_cycle,
        intersectionNumber_toQDivisor_eq_degree_of_iso hGc hG T]
      push_cast
      rfl
  refine ⟨fun z => curveForm_nonneg_of_mem_closedConeOfCurves _ _ fun T => ?_, fun T hT => ?_⟩ <;>
    rw [gT]
  · exact_mod_cast (degree_pullback_nonneg_and_one_le_of_not_isContractedBy hf A hA T).1
  · exact_mod_cast (degree_pullback_nonneg_and_one_le_of_not_isContractedBy hf A hA T).2 hT

/-- If `D` is `f`-nef and `G` is nonnegative on `NE̅(X)` and at least one on every curve not
contracted by `f`, then `D + mG` is nonnegative on a curve `C` as soon as `-(D · C) ≤ m`. -/
private theorem curveForm_add_mul_nonneg [CompactSpace X] {Y : Scheme.{0}} {f : X ⟶ Y}
    {D : Divisor X} (hDc : D.IsCartier) (hD : (Divisor.toQDivisor D).IsRelativelyNef sX f)
    {G : QDivisor X} (hG : G.IsQCartier)
    (hGnn : ∀ z ∈ closedConeOfCurves sX, 0 ≤ QDivisor.curveForm sX G hG z)
    (hG₁ : ∀ T : ProperCurve sX, ¬ T.IsContractedBy f →
      1 ≤ QDivisor.curveForm sX G hG (OneCycle.numericalClass sX (T.cycle ℝ)))
    {C : ProperCurve sX} {m : ℝ} (hm₀ : 0 ≤ m)
    (hm : -QDivisor.curveForm sX (Divisor.toQDivisor D) (QDivisor.isQCartier_toQDivisor hDc)
      (OneCycle.numericalClass sX (C.cycle ℝ)) ≤ m) :
    0 ≤ QDivisor.curveForm sX (Divisor.toQDivisor D) (QDivisor.isQCartier_toQDivisor hDc)
        (OneCycle.numericalClass sX (C.cycle ℝ)) +
      m * QDivisor.curveForm sX G hG (OneCycle.numericalClass sX (C.cycle ℝ)) := by
  by_cases hc : C.IsContractedBy f
  · refine add_nonneg ?_ (mul_nonneg hm₀ (hGnn _
      (coneOfCurves_le_closedConeOfCurves sX (numericalClass_cycle_mem_coneOfCurves sX C))))
    rw [MMP.ProgramBaseChange.curveForm_numericalClass_cycle]
    exact_mod_cast QDivisor.IsRelativelyNef.intersectionNumber_nonneg sX hD
      (QDivisor.isQCartier_toQDivisor hDc) C hc
  · have := mul_le_mul_of_nonneg_left (hG₁ C hc) hm₀
    linarith

omit [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X] in
open scoped Pointwise in
/-- A linear form nonnegative on `P` and on the curves of `S` is nonnegative on
`NE̅(X) = P + ∑_{C ∈ S} ℝ_{≥0}[C]`. -/
private theorem nonneg_of_closedConeOfCurves_eq_add_hull
    {φ : NumericalCurveClasses sX →ₗ[ℝ] ℝ} {P : Set (NumericalCurveClasses sX)}
    {S : Finset (ProperCurve sX)}
    (hcone : (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) = P +
      (PointedCone.hull ℝ
        ((fun C : ProperCurve sX => OneCycle.numericalClass sX (C.cycle ℝ)) '' ↑S) :
          Set (NumericalCurveClasses sX)))
    (hP : ∀ z ∈ P, 0 ≤ φ z) (hS : ∀ C ∈ S, 0 ≤ φ (OneCycle.numericalClass sX (C.cycle ℝ)))
    {z : NumericalCurveClasses sX} (hz : z ∈ closedConeOfCurves sX) : 0 ≤ φ z := by
  rw [← SetLike.mem_coe, hcone] at hz
  obtain ⟨z₁, hz₁, z₂, hz₂, rfl⟩ := Set.mem_add.mp hz
  rw [map_add]
  exact add_nonneg (hP z₁ hz₁) (nonneg_of_mem_hull (by rintro _ ⟨C, hC, rfl⟩; exact hS C hC) hz₂)

/-- If the form of `D + mG` is nonnegative on every proper curve, then `D + mG` is nef. -/
private theorem isNef_add_nsmul_of_curveForm_nonneg [CompactSpace X] {D G : Divisor X}
    (hDc : D.IsCartier) (hGc : G.IsCartier) (m : ℕ)
    (h : ∀ T : ProperCurve sX,
      0 ≤ QDivisor.curveForm sX (Divisor.toQDivisor D) (QDivisor.isQCartier_toQDivisor hDc)
          (OneCycle.numericalClass sX (T.cycle ℝ)) +
        (m : ℝ) * QDivisor.curveForm sX (Divisor.toQDivisor G)
          (QDivisor.isQCartier_toQDivisor hGc) (OneCycle.numericalClass sX (T.cycle ℝ))) :
    (Divisor.toQDivisor (D + m • G)).IsNef k sX := by
  refine ⟨QDivisor.isQCartier_toQDivisor (hDc.add (hGc.nsmul m)), fun C i _ _ _ hC => ?_⟩
  obtain ⟨T₀, e, he⟩ := exists_properCurve_iso (sX := sX) i hC
  rw [intersectionNumber_eq_of_iso i T₀.ι hC.le T₀.dim_le e he,
    QDivisor.intersectionNumber_toQDivisor k sX T₀.ι T₀.dim_le _ (hDc.add (hGc.nsmul m)),
    Divisor.degreeOn_add k sX T₀.ι T₀.dim_le _ _ hDc (hGc.nsmul m),
    Divisor.degreeOn_nsmul' k sX T₀.ι T₀.dim_le G hGc m]
  have key := h T₀
  rw [MMP.ProgramBaseChange.curveForm_numericalClass_cycle,
    MMP.ProgramBaseChange.curveForm_numericalClass_cycle,
    QDivisor.intersectionNumber_toQDivisor k sX T₀.ι T₀.dim_le D hDc,
    QDivisor.intersectionNumber_toQDivisor k sX T₀.ι T₀.dim_le G hGc] at key
  push_cast at key ⊢
  exact_mod_cast key

end MMP.FourfoldProofs.Km3bRelativeBpfMakeNefProof

end

section

public section

open AlgebraicGeometry CategoryTheory

namespace MMP.Mori

open MMP.Fourfold MMP.FourfoldProofs.Km3bRelativeBpfMakeNefProof in
/-- **A large pull-back twist makes an `f`-nef divisor nef** (Kollár–Mori 3.26). Let
`f : X ⟶ Y` be a morphism of projective varieties over an algebraically closed field `k` of
characteristic zero, `(X, Δ)` a klt pair with `Δ ≥ 0` and canonical divisor `K`, `H` an ample
Cartier divisor on `Y` and `G` a Cartier divisor on `X` with `𝒪_X(G) ≅ f^*𝒪_Y(H)`. Let `D` be an
`f`-nef Cartier divisor and `a > 0` rational with `aD - K - Δ` ample. Then there is `m₀` such that
`D + mG` is nef for every `m ≥ m₀`. -/
@[mmp "lem_km3b_relative_bpf_make_nef"]
public theorem exists_forall_ge_isNef_add_nsmul_pullback {k : Type} [Field k]
    {X Y : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] {sY : Y ⟶ Spec (.of k)} {f : X ⟶ Y}
    (hf : IsProjectiveSetting k sX sY f)
    {n : ℕ} {K : Divisor X} {Δ : QDivisor X} (hklt : IsKltPair sX n K Δ) (hΔ : 0 ≤ Δ)
    (H : Y.CartierDivisor) (hH : Stacks.Ample.IsAmple Y (MMP.CartierDivisor.sheaf H))
    {G : Divisor X} (hGc : G.IsCartier)
    (hG : Nonempty (G.divisorialSheaf ≅
      (Scheme.Modules.pullback f).obj (MMP.CartierDivisor.sheaf H)))
    {D : Divisor X} (hDc : D.IsCartier) (hD : (Divisor.toQDivisor D).IsRelativelyNef sX f)
    {a : ℚ} (ha : 0 < a)
    (hA : (a • Divisor.toQDivisor D - Divisor.toQDivisor K - Δ).IsAmple) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → (Divisor.toQDivisor (D + m • G)).IsNef k sX := by
  haveI := hf.isAlgClosed
  haveI := hf.charZero
  haveI : AlgebraicGeometry.IsProjectiveVariety k sX := hf.isProjectiveVariety_source
  haveI : AlgebraicGeometry.IsProjectiveVariety k sY := hf.isProjectiveVariety_target
  have hDq : (Divisor.toQDivisor D).IsQCartier := QDivisor.isQCartier_toQDivisor hDc
  have hGq : (Divisor.toQDivisor G).IsQCartier := QDivisor.isQCartier_toQDivisor hGc
  have hKΔ : (Divisor.toQDivisor K + Δ).IsQCartier := hklt.1.2.2
  set A' := a • Divisor.toQDivisor D - Divisor.toQDivisor K - Δ with hA'
  have hA'q : A'.IsQCartier := by
    obtain ⟨m, hm, E, hEA, hEc, -⟩ := hA
    exact ⟨m, by exact_mod_cast hm.ne', E,
      by rw [hEA, natCast_zsmul, Nat.cast_smul_eq_nsmul], hEc⟩
  have hsum : Divisor.toQDivisor K + Δ + A' = a • Divisor.toQDivisor D := by rw [hA']; abel
  have haDq : (a • Divisor.toQDivisor D).IsQCartier := by
    rw [← hsum]
    exact hKΔ.add hA'q
  obtain ⟨S, -, hcone⟩ := exists_finset_isRationalCurve_closedConeOfCurves_eq hklt
    (DivisorWithCoeffs.isEffective_iff_nonneg.mpr hΔ) one_pos hA
  have hform : ∀ z, QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hKΔ z +
      1 * QDivisor.curveForm sX A' hA'q z =
        (a : ℝ) * QDivisor.curveForm sX (Divisor.toQDivisor D) hDq z := fun z => by
    rw [one_mul, ← LinearMap.add_apply, curveForm_add_eq_smul hKΔ hA'q hDq haDq hsum,
      LinearMap.smul_apply, smul_eq_mul]
  obtain ⟨hGnn, hG₁⟩ := curveForm_nonneg_and_one_le_of_iso_pullback hf.comp_eq H hH hGc hG
  set dC : ProperCurve sX → ℝ := fun C =>
    QDivisor.curveForm sX (Divisor.toQDivisor D) hDq (OneCycle.numericalClass sX (C.cycle ℝ))
  refine ⟨S.sup fun C => ⌈-dC C⌉₊, fun m hm => ?_⟩
  set φ : NumericalCurveClasses sX →ₗ[ℝ] ℝ :=
    QDivisor.curveForm sX (Divisor.toQDivisor D) hDq +
      (m : ℝ) • QDivisor.curveForm sX (Divisor.toQDivisor G) hGq with hφ
  have hφapp : ∀ z, φ z = QDivisor.curveForm sX (Divisor.toQDivisor D) hDq z +
      (m : ℝ) * QDivisor.curveForm sX (Divisor.toQDivisor G) hGq z := fun z => by
    rw [hφ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  have hray : ∀ C ∈ S, 0 ≤ φ (OneCycle.numericalClass sX (C.cycle ℝ)) := fun C hC => by
    rw [hφapp]
    exact curveForm_add_mul_nonneg hDc hD hGq hGnn hG₁ m.cast_nonneg <| (Nat.le_ceil _).trans <|
      by exact_mod_cast (Finset.le_sup (f := fun C => ⌈-dC C⌉₊) hC).trans hm
  have hnn : ∀ z ∈ closedConeOfCurves sX, 0 ≤ φ z := by
    refine fun _ => nonneg_of_closedConeOfCurves_eq_add_hull hcone (fun z hz => ?_) hray
    obtain ⟨hz, hz'⟩ := hz
    have h : 0 ≤ (a : ℝ) * QDivisor.curveForm sX (Divisor.toQDivisor D) hDq z := by
      rw [← hform]
      exact hz'
    rw [hφapp]
    exact add_nonneg (nonneg_of_mul_nonneg_right h (by exact_mod_cast ha))
      (mul_nonneg m.cast_nonneg (hGnn z hz))
  refine isNef_add_nsmul_of_curveForm_nonneg hDc hGc m fun T => ?_
  rw [← hφapp]
  exact hnn _ (coneOfCurves_le_closedConeOfCurves sX (numericalClass_cycle_mem_coneOfCurves sX T))

end MMP.Mori

end
