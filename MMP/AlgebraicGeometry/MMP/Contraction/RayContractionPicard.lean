module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Contraction.RayLineBundleDescent
public import MMP.AlgebraicGeometry.MMP.Contraction.PicardNumberDrop
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Basic
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Relative
public import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
public import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
public import MMP.AlgebraicGeometry.Intersection.CurveDegreeProjection
public import MMP.AlgebraicGeometry.Intersection.CurveDegreeAdditive
public import MMP.AlgebraicGeometry.Intersection.PairingSeparation
public import MMP.AlgebraicGeometry.ProjectiveSpace.ProductProjectiveLine
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.PushforwardRelativeCone
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheafMul

section

/-!
## Proof outline

Let `g : X ⟶ Z` contract an extremal ray `R = ℝ_{≥0}[C]` of `NE̅(X)` and have the pullback
property. An invertible sheaf `M` on `X` has `(M · C) = 0` exactly when it is pulled back from
`Z`, and `ρ(Z) = ρ(X) - 1`.

The second statement is proved on curve classes: the push-forward `g_* : N₁(X) ⟶ N₁(Z)` is
surjective, since every curve of `Z` is the image of a curve of `X`, and its kernel is the line
`ℝ[C]`. A class `z` with `g_* z = 0` is killed by every pulled-back degree form, by the projection
formula. Choosing `M₀` with `a = (M₀ · C) ≠ 0` and putting `w = z - ((M₀ · z) / a) [C]`, every
invertible sheaf `M` with `b = (M · C)` gives the sheaf `M^a ⊗ M₀^{-b}` of degree zero on `C`,
hence a pullback by the first statement, so `a (M · w) = 0` and `w` is numerically trivial. This is
the dual form of the argument of [KollarMori, 3.17], which shows that `N₁(Z)^* ⟶ N₁(X)^*` is
injective with image the hyperplane `[C]^⊥`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Corollary 3.17
-/

namespace MMP.FourfoldProofs.Km3cRayContractionPicardOverKProof

open CategoryTheory AlgebraicGeometry MMP.Mori TopologicalSpace

section Degrees

variable {k : Type} [Field k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)}

variable (k) in
/-- The degree of `𝒪_X(E)` along a proper curve is additive in the Cartier divisor `E`. -/
private lemma degree_sheaf_add (C : ProperCurve sX) (E E' : X.CartierDivisor) :
    C.degree k (MMP.CartierDivisor.sheaf (E + E')) =
      C.degree k (MMP.CartierDivisor.sheaf E) +
        C.degree k (MMP.CartierDivisor.sheaf E') := by
  have : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.toRingedSpace.presheaf,
        X.toRingedSpace.IsSheaf⟩).obj (MMP.CartierDivisor.sheaf E)).obj
          (MMP.CartierDivisor.sheaf E')) :=
    Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible X.presheaf X.ringCatSheaf.2 _ _
  rw [ProperCurve.degree, ProperCurve.degree, ProperCurve.degree, ← degreeOn_tensorSheaf]
  exact degreeOn_eq_of_iso k sX C.ι C.dim_le
    (MMP.CartierDivisorSheaf.sheafMulIso E E').symm

/-- The degree of an invertible sheaf along a proper curve is its degree on the curve's class. -/
private lemma degree_eq_degree_numericalClass (C : ProperCurve sX) (N : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N] :
    (C.degree k N : ℝ) =
      NumericalCurveClasses.degree sX N (OneCycle.numericalClass sX (C.cycle ℝ)) := by
  rw [NumericalCurveClasses.degree_numericalClass, OneCycle.degree_cycle]

/-- A degree form on `N₁(X)` is determined by its values on the classes of proper curves. -/
private lemma degree_eq_of_forall (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (φ : NumericalCurveClasses sX →ₗ[ℝ] ℝ)
    (h : ∀ C : ProperCurve sX, (C.degree k L : ℝ) = φ (OneCycle.numericalClass sX (C.cycle ℝ))) :
    NumericalCurveClasses.degree sX L = φ := by
  refine Submodule.linearMap_qext _ (Finsupp.lhom_ext fun C r => ?_)
  have hs : Finsupp.single C r = r • C.cycle ℝ := by
    simp [ProperCurve.cycle, Finsupp.smul_single]
  change NumericalCurveClasses.degree sX L (OneCycle.numericalClass sX (Finsupp.single C r)) =
    φ (OneCycle.numericalClass sX (Finsupp.single C r))
  rw [hs, map_smul, map_smul, map_smul, ← degree_eq_degree_numericalClass, h]

/-- A numerical class killed by every degree form is zero. -/
private lemma eq_zero_of_forall_degree {w : NumericalCurveClasses sX}
    (h : ∀ (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L],
      NumericalCurveClasses.degree sX L w = 0) : w = 0 := by
  obtain ⟨W, rfl⟩ := OneCycle.numericalClass_surjective sX w
  rw [OneCycle.numericalClass, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    OneCycle.mem_numericallyTrivial]
  exact fun L _ => h L

end Degrees

section Lifting

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

variable {k : Type} [Field k] {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
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

/-- The closure of the generic point of a proper curve is not a point. -/
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

/-- Through a surjective morphism of projective varieties, every proper curve is the image of a
proper curve. -/
private lemma ProperCurve.exists_point_eq_of_surjective {W : Scheme.{0}}
    {sW : W ⟶ Spec (.of k)} (hW : MMP.Mori.IsProjectiveVariety k sW)
    (hX : MMP.Mori.IsProjectiveVariety k sX) (p : W ⟶ X) (hpk : p ≫ sX = sW) [Surjective p]
    (C : ProperCurve sX) : ∃ Γ : ProperCurve sW, p Γ.point = C.point := by
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
  exact ⟨⟨w, isProperCurve_of_isProper sW hdim⟩, hpw⟩

/-- Through a surjective morphism of projective varieties, a positive multiple of every proper
curve is the push-forward of a proper curve. -/
private lemma ProperCurve.exists_pushforward_cycle_eq_smul {W : Scheme.{0}}
    {sW : W ⟶ Spec (.of k)} (hW : MMP.Mori.IsProjectiveVariety k sW)
    (hX : MMP.Mori.IsProjectiveVariety k sX) (p : W ⟶ X) (hpk : p ≫ sX = sW) [Surjective p]
    (C : ProperCurve sX) :
    ∃ (Γ : ProperCurve sW) (d : ℝ), 0 < d ∧
      OneCycle.pushforward ℝ sW sX p (Γ.cycle ℝ) = d • C.cycle ℝ := by
  have : AlgebraicGeometry.IsVariety k sX := hX.toIsVariety
  obtain ⟨Γ, hpw⟩ := ProperCurve.exists_point_eq_of_surjective hW hX p hpk C
  have hpt : ¬ ∃ y : X, Set.range (Γ.ι ≫ p) = {y} := by
    rintro ⟨y, hy⟩
    rw [Γ.range_comp p hpk, hpw] at hy
    exact closure_point_ne_singleton C y hy
  have hPC : IsProperCurve sX (p Γ.point) := hpw ▸ C.isProperCurve
  have hCeq : (⟨p Γ.point, hPC⟩ : ProperCurve sX) = C := MMP.Mori.ProperCurve.ext hpw
  refine ⟨Γ, residueFieldDegree p Γ.point,
    by exact_mod_cast residueFieldDegree_pos p hpk Γ hpt, ?_⟩
  rw [OneCycle.pushforward_cycle, cyclePushforwardOfPoint, dif_pos hPC, hCeq, ProperCurve.cycle,
    Finsupp.smul_single, smul_eq_mul, mul_one]

/-- Push-forward of numerical curve classes along a surjective morphism of projective varieties
is surjective. -/
private lemma pushforward_surjective [IsSeparated sY] [LocallyOfFiniteType sY]
    (hX : MMP.Mori.IsProjectiveVariety k sX) (hY : MMP.Mori.IsProjectiveVariety k sY)
    (f : X ⟶ Y) (hf : f ≫ sY = sX) [Surjective f] :
    Function.Surjective (NumericalCurveClasses.pushforward f hf) := by
  suffices h : ∀ W : OneCycle ℝ sY,
      OneCycle.numericalClass sY W ∈ LinearMap.range (NumericalCurveClasses.pushforward f hf) by
    intro w
    obtain ⟨W, rfl⟩ := OneCycle.numericalClass_surjective sY w
    exact h W
  intro W
  induction W using Finsupp.induction_linear with
  | zero =>
    rw [map_zero]
    exact zero_mem _
  | add a b ha hb =>
    rw [map_add]
    exact add_mem ha hb
  | single C r =>
    obtain ⟨Γ, d, hd, hΓ⟩ := ProperCurve.exists_pushforward_cycle_eq_smul hX hY f hf C
    refine ⟨(r / d) • OneCycle.numericalClass sX (Γ.cycle ℝ), ?_⟩
    rw [map_smul]
    change (r / d) •
      OneCycle.numericalClass sY (OneCycle.pushforward ℝ sX sY f (Γ.cycle ℝ)) = _
    rw [hΓ, map_smul, smul_smul, div_mul_cancel₀ r hd.ne', ← map_smul]
    congr 1
    simp [ProperCurve.cycle, Finsupp.smul_single]

end Lifting

section Kernel

variable {k : Type} [Field k] {X Z : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
  {sZ : Z ⟶ Spec (.of k)} {g : X ⟶ Z}

/-- With the pullback property, an invertible sheaf has degree zero on a contracted curve
spanning the ray exactly when it is pulled back. -/
private lemma degree_eq_zero_iff_exists_iso_pullback [IsSeparated sZ] [LocallyOfFiniteType sZ]
    (hgc : g ≫ sZ = sX) {R : Set (NumericalCurveClasses sX)}
    (hpb : ∀ (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L],
      (∀ C' : ProperCurve sX, OneCycle.numericalClass sX (C'.cycle ℝ) ∈ R → C'.degree k L = 0) →
      ∃ LZ : Z.Modules, SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 LZ ∧
        Nonempty (L ≅ (Scheme.Modules.pullback g).obj LZ))
    (C : ProperCurve sX)
    (hC : R = {w | ∃ c : ℝ, 0 ≤ c ∧ c • OneCycle.numericalClass sX (C.cycle ℝ) = w})
    (hCR : C.IsContractedBy g) (M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] :
    C.degree k M = 0 ↔
      ∃ L : Z.Modules, SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 L ∧
        Nonempty (M ≅ (Scheme.Modules.pullback g).obj L) := by
  constructor
  · intro h0
    refine hpb M fun C' hC' => ?_
    rw [hC] at hC'
    obtain ⟨c, -, hc⟩ := hC'
    have h := degree_eq_degree_numericalClass C' M
    rw [← hc, map_smul, ← degree_eq_degree_numericalClass C M, h0, Int.cast_zero, smul_zero] at h
    exact_mod_cast h
  · rintro ⟨L, hL, ⟨e⟩⟩
    rw [show C.degree k M = C.degree k ((Scheme.Modules.pullback g).obj L) from
      degreeOn_eq_of_iso k sX C.ι C.dim_le e]
    exact C.degree_pullback_eq_zero_of_isContractedBy g hgc hCR L

/-- If every invertible sheaf of degree zero on `C` is pulled back along `g`, a class killed by
every pulled-back degree form and by one sheaf `M₀` of nonzero degree on `C` is zero. -/
private lemma eq_zero_of_forall_degree_pullback [IsIntegral X] (C : ProperCurve sX)
    (h1 : ∀ (M : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M],
      C.degree k M = 0 →
        ∃ L : Z.Modules, SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 L ∧
          Nonempty (M ≅ (Scheme.Modules.pullback g).obj L))
    {M₀ : X.Modules} [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M₀]
    (hM₀ : C.degree k M₀ ≠ 0) {w : NumericalCurveClasses sX}
    (hw0 : NumericalCurveClasses.degree sX M₀ w = 0)
    (hpw : ∀ (L : Z.Modules) [SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 L],
      NumericalCurveClasses.degree sX ((Scheme.Modules.pullback g).obj L) w = 0) :
    w = 0 := by
  refine eq_zero_of_forall_degree fun M _ => ?_
  set a := C.degree k M₀ with hadef
  set b := C.degree k M with hbdef
  obtain ⟨EM, ⟨eM⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf M
  obtain ⟨E₀, ⟨e₀⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf M₀
  let δ : ProperCurve sX → X.CartierDivisor →+ ℤ := fun C' =>
    AddMonoidHom.mk' (fun E => C'.degree k (MMP.CartierDivisor.sheaf E)) (degree_sheaf_add k C')
  set N := MMP.CartierDivisor.sheaf (a • EM - b • E₀) with hNdef
  have hN : ∀ C' : ProperCurve sX, (C'.degree k N : ℝ) =
      ((a : ℝ) • NumericalCurveClasses.degree sX M -
        (b : ℝ) • NumericalCurveClasses.degree sX M₀)
          (OneCycle.numericalClass sX (C'.cycle ℝ)) := by
    intro C'
    have hM : C'.degree k M = δ C' EM := degreeOn_eq_of_iso k sX C'.ι C'.dim_le eM
    have hM0 : C'.degree k M₀ = δ C' E₀ := degreeOn_eq_of_iso k sX C'.ι C'.dim_le e₀
    have hNd : C'.degree k N = δ C' (a • EM - b • E₀) := rfl
    rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.smul_apply,
      ← degree_eq_degree_numericalClass, ← degree_eq_degree_numericalClass, hNd, map_sub,
      map_zsmul, map_zsmul, ← hM, ← hM0]
    simp only [smul_eq_mul]
    push_cast
    ring
  have hNC : C.degree k N = 0 := by
    have h := hN C
    rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.smul_apply,
      ← degree_eq_degree_numericalClass, ← degree_eq_degree_numericalClass, smul_eq_mul,
      smul_eq_mul, ← hadef, ← hbdef, mul_comm, sub_self] at h
    exact_mod_cast h
  obtain ⟨L, hL, ⟨eN⟩⟩ := h1 N hNC
  have hNL : NumericalCurveClasses.degree sX N =
      NumericalCurveClasses.degree sX ((Scheme.Modules.pullback g).obj L) :=
    degree_eq_of_forall N _ fun C' => by
      rw [← degree_eq_degree_numericalClass]
      exact congrArg (Int.cast : ℤ → ℝ) (degreeOn_eq_of_iso k sX C'.ι C'.dim_le eN)
  have hNw : NumericalCurveClasses.degree sX N w = 0 := by rw [hNL, hpw]
  rw [degree_eq_of_forall N _ hN, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.smul_apply, hw0, smul_zero, sub_zero, smul_eq_mul] at hNw
  exact (mul_eq_zero.mp hNw).resolve_left (Int.cast_ne_zero.mpr hM₀)

/-- If every invertible sheaf of degree zero on `C` is pulled back along `g` and `g_* [C] = 0`,
the kernel of `g_* : N₁(X) ⟶ N₁(Z)` lies in the line `ℝ [C]`. -/
private lemma ker_pushforward_le_span [IsIntegral X] [IsSeparated sZ] [LocallyOfFiniteType sZ]
    (hgc : g ≫ sZ = sX) (C : ProperCurve sX)
    (h1 : ∀ (M : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M],
      C.degree k M = 0 →
        ∃ L : Z.Modules, SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 L ∧
          Nonempty (M ≅ (Scheme.Modules.pullback g).obj L))
    (hc0 : OneCycle.numericalClass sX (C.cycle ℝ) ≠ 0)
    (hπc : NumericalCurveClasses.pushforward g hgc (OneCycle.numericalClass sX (C.cycle ℝ)) = 0) :
    LinearMap.ker (NumericalCurveClasses.pushforward g hgc) ≤
      ℝ ∙ OneCycle.numericalClass sX (C.cycle ℝ) := by
  intro z hz
  rw [LinearMap.mem_ker] at hz
  obtain ⟨M₀, _, hM₀⟩ : ∃ (M₀ : X.Modules)
      (_ : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M₀), C.degree k M₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    refine hc0 (eq_zero_of_forall_degree fun L _ => ?_)
    rw [← degree_eq_degree_numericalClass C L, hcon L inferInstance, Int.cast_zero]
  set t := NumericalCurveClasses.degree sX M₀ z / C.degree k M₀ with htdef
  refine Submodule.mem_span_singleton.mpr
    ⟨t, (sub_eq_zero.mp (eq_zero_of_forall_degree_pullback C h1 hM₀ ?_ fun L _ => ?_)).symm⟩
  · rw [map_sub, map_smul, ← degree_eq_degree_numericalClass C M₀, smul_eq_mul, htdef,
      div_mul_cancel₀ _ (Int.cast_ne_zero.mpr hM₀), sub_self]
  · rw [map_sub, map_smul, ← NumericalCurveClasses.degree_pushforward g hgc,
      ← NumericalCurveClasses.degree_pushforward g hgc, hz, hπc, map_zero, smul_zero, sub_zero]

end Kernel

end MMP.FourfoldProofs.Km3cRayContractionPicardOverKProof

end

section

/-!
# Contractions of extremal rays with the pullback property

Let `X` be a normal projective variety over an algebraically closed field `k` of characteristic
zero, `R` an extremal ray of the closed cone of curves `NE̅(X)`, and `g : X ⟶ Z` a contraction of
`R`. The pair `(R, g)` has the *pullback property* if every invertible sheaf `L` on `X` with
`(L · C') = 0` for every irreducible curve `C'` with `[C'] ∈ R` is isomorphic to `g^* L_Z` for an
invertible sheaf `L_Z` on `Z`. If it does, and `C ⊆ X` is an irreducible curve with
`R = ℝ_{≥0}[C]`, then an invertible sheaf `M` on `X` has `(M · C) = 0` if and only if
`M ≅ g^* L` for an invertible sheaf `L` on `Z`, and `ρ(Z) = ρ(X) - 1`.

No singularity hypothesis on `X` and no negativity of `R` is assumed: the pullback property
replaces the descent theorem for line bundles, which is where such hypotheses enter in
`MMP.Mori.degree_eq_zero_iff_exists_iso_pullback_of_isContractionOfFace` and
`MMP.Mori.picardNumber_add_one_eq_of_isContractionOfFace`.

## Main results

* `MMP.Mori.degree_eq_zero_iff_and_picardNumber_add_one_eq_of_isContractionOfFace`: the
  statement above.

## Implementation notes

An irreducible curve is a `MMP.Mori.ProperCurve`, its class is
`OneCycle.numericalClass sX (C.cycle ℝ)`, and `(M · C)` is `MMP.Mori.ProperCurve.degree`. A
contraction of `R` is `MMP.Mori.IsContractionOfFace` for the ray `R`. A line bundle is an
invertible sheaf of `𝒪`-modules and `g^*` is `AlgebraicGeometry.Scheme.Modules.pullback g`.
The equation `ρ(Z) = ρ(X) - 1` is stated as `ρ(Z) + 1 = ρ(X)` in `ℕ∞`, which is stronger than
truncated subtraction.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Corollary 3.17
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace MMP.Mori

open MMP.FourfoldProofs.Km3cRayContractionPicardOverKProof in
/-- **Contractions of extremal rays with the pullback property** (Kollár–Mori 3.17). Let `X` be
a normal projective variety over an algebraically closed field `k` of characteristic zero, `R` an
extremal ray of `NE̅(X)`, and `g : X ⟶ Z` a contraction of `R` such that every invertible sheaf
on `X` of degree `0` on every curve with class in `R` is the pullback along `g` of an invertible
sheaf on `Z`. Let `C ⊆ X` be a curve with `R = ℝ_{≥0}[C]`. Then an invertible sheaf `M` on `X`
has `deg_C M = 0` if and only if `M ≅ g^* L` for an invertible sheaf `L` on `Z`, and
`ρ(Z) + 1 = ρ(X)`. -/
@[mmp "lem_km3c_ray_contraction_picard_over_k"]
public theorem degree_eq_zero_iff_and_picardNumber_add_one_eq_of_isContractionOfFace
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    [AlgebraicGeometry.IsProjectiveVariety k sX]
    {R : Set (NumericalCurveClasses sX)}
    (hR : IsExtremalRay ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) R)
    {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of k)} {g : X ⟶ Z} (hg : IsContractionOfFace k sX sZ R g)
    (hpb : ∀ (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L],
      (∀ C' : ProperCurve sX, OneCycle.numericalClass sX (C'.cycle ℝ) ∈ R → C'.degree k L = 0) →
      ∃ LZ : Z.Modules, SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 LZ ∧
        Nonempty (L ≅ (Scheme.Modules.pullback g).obj LZ))
    (C : ProperCurve sX)
    (hC : R = {w | ∃ c : ℝ, 0 ≤ c ∧ c • OneCycle.numericalClass sX (C.cycle ℝ) = w}) :
    (∀ (M : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M],
      C.degree k M = 0 ↔
        ∃ L : Z.Modules, SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 L ∧
          Nonempty (M ≅ (Scheme.Modules.pullback g).obj L)) ∧
    picardNumber sZ + 1 = picardNumber sX := by
  have hpX := hg.isProjectiveVariety_source
  have hpZ := hg.isProjectiveVariety_target
  have : AlgebraicGeometry.IsVariety k sZ := hpZ.toIsVariety
  have : IsProper (g ≫ sZ) := hg.comp_eq ▸ inferInstance
  have : IsProper g := IsProper.of_comp g sZ
  have : Surjective g := Scheme.Hom.surjective_of_isIso_app g hg.isIso_app
  have hCR : C.IsContractedBy g :=
    (hg.isContractedBy_iff C).mpr (hC ▸ ⟨1, zero_le_one, one_smul _ _⟩)
  have h1 : ∀ (M : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M],
      C.degree k M = 0 ↔
        ∃ L : Z.Modules, SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 L ∧
          Nonempty (M ≅ (Scheme.Modules.pullback g).obj L) := fun M _ =>
    degree_eq_zero_iff_exists_iso_pullback hg.comp_eq hpb C hC hCR M
  refine ⟨h1, ?_⟩
  set c := OneCycle.numericalClass sX (C.cycle ℝ) with hcdef
  have hc0 : c ≠ 0 := by
    obtain ⟨v, hv, hRv⟩ := hR.2
    have hvR : v ∈ R := hRv ▸ ⟨1, zero_le_one, one_smul _ _⟩
    rw [hC] at hvR
    obtain ⟨t, -, ht⟩ := hvR
    intro h
    rw [h, smul_zero] at ht
    exact hv ht.symm
  set π := NumericalCurveClasses.pushforward g hg.comp_eq with hπdef
  have hπc : π c = 0 := by
    change OneCycle.numericalClass sZ (OneCycle.pushforward ℝ sX sZ g (C.cycle ℝ)) = 0
    rw [C.pushforward_cycle_eq_zero_of_isContractedBy ℝ g hg.comp_eq hCR, map_zero]
  have hker : LinearMap.ker π = ℝ ∙ c :=
    le_antisymm (ker_pushforward_le_span hg.comp_eq C (fun M _ => (h1 M).mp) hc0 hπc)
      ((Submodule.span_singleton_le_iff_mem _ _).mpr hπc)
  have hrank := Submodule.rank_quotient_add_rank (LinearMap.ker π)
  have hline : Module.rank ℝ (ℝ ∙ c) = 1 := by
    rw [← Module.finrank_eq_rank, finrank_span_singleton hc0, Nat.cast_one]
  rw [(π.quotKerEquivOfSurjective (pushforward_surjective hpX hpZ g hg.comp_eq)).rank_eq, hker,
    hline] at hrank
  rw [picardNumber, picardNumber, ← hrank, map_add, map_one]

end MMP.Mori

end
