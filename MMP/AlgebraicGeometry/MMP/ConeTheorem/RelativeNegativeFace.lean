module

public import MMP.AlgebraicGeometry.MMP.ConeTheorem.AmplePerturbationFiniteRays
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.RelativeConeInAbsolute
public import MMP.AlgebraicGeometry.Positivity.RelativeKodairaDecomposition

section

/-!
# Relative negative extremal faces are absolute negative extremal faces

Let `f : X ⟶ Y` be a morphism of projective varieties over an algebraically closed field of
characteristic zero, `(X, Δ)` a klt pair with `Δ ≥ 0`, `K = K_X + Δ`, and `F` a `K`-negative
extremal face of `NE̅(X/Y)`. Then `ι(F)` is a `K`-negative extremal face of `NE̅(X)`, where
`ι : N₁(X/Y) → N₁(X)` is the natural (injective) map.

Only extremality needs an argument. Let `H` be an ample divisor on `X`. The face `ι(F)` is a
closed convex cone on which `K < 0` off `0`, so `K + εH < 0` on `ι(F) ∖ {0}` for some `ε > 0`.
By the cone theorem, `NE̅(X) = NE̅(X)_{K + εH ≥ 0} + ∑ ℝ_{≥0}[Cᵢ]` for finitely many curves `Cᵢ`.
Let `u, v ∈ NE̅(X)` with `u + v ∈ ι(F)`, and write `u = a + b`, `v = a' + b'` accordingly. The
push-forward `f_*` vanishes on `ι(N₁(X/Y))` and maps `NE̅(X)` into `NE̅(Y)`, which contains no
line; so `f_* b = f_* b' = 0`, which forces every curve occurring in `b`, `b'` to be contracted
by `f` (an ample divisor on `Y` has positive degree on its image otherwise). Hence `b, b'` lie
in `ι(NE(X/Y))`, so does `a + a' = (u + v) - b - b'` (as `ι(NE̅(X/Y)) = NE̅(X) ∩ ι(N₁(X/Y))`),
and extremality of `F` puts `a + a'` in `ι(F)`. As `K + εH ≥ 0` at `a + a'`, it is `0`, so
`a = a' = 0` (`NE̅(X)` contains no line), and `u = b`, `v = b'` lie in `ι(F)`.

## Main results

* `MMP.Mori.isNegativeExtremalFace_image_relativeToAbsolute`: the statement above.

## Implementation notes

The source first builds a relative supporting divisor of `F`, makes it nef by twisting with
pull-backs of an ample divisor of `Y`, and identifies `ι(F)` with the face of the twisted
divisor. The argument here replaces that construction by the decomposition of `NE̅(X)` given by
the cone theorem with an ample perturbation.

The natural map is `MMP.Mori.relativeToAbsolute`, the unique linear map sending the relative
class of a relative 1-cycle to its absolute class
(`MMP.Mori.isNaturalRelativeMap_relativeToAbsolute`, `MMP.Mori.IsNaturalRelativeMap.unique`).
The form `w ↦ ((K_X + Δ) · w)` on `N₁(X/Y)` is the absolute form
`MMP.Fourfold.QDivisor.curveForm` of `K_X + Δ` composed with this map: the intersection number
of a relative 1-cycle with a divisor is that of the underlying 1-cycle.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 3.21, 3.25
-/

open CategoryTheory AlgebraicGeometry MMP.Mori

namespace MMP.FourfoldProofs.Km3bRelativeNegativeFaceIsAbsoluteProof

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

section Cones

variable {U W : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup W] [Module ℝ W]

/-- The preimage of an extremal face under a linear map is an extremal face of the preimage. -/
private theorem isExtremalFace_preimage (g : U →ₗ[ℝ] W) {C F : Set W}
    (hF : IsExtremalFace ℝ C F) : IsExtremalFace ℝ (g ⁻¹' C) (g ⁻¹' F) := by
  obtain ⟨hFC, hFcone, hFadd, hFext⟩ := hF
  refine ⟨fun z hz => hFC hz, MMP.Positivity.isCone_preimage hFcone g,
    fun u hu v hv => ?_, fun u hu v hv huv => ?_⟩
  · simpa using hFadd _ hu _ hv
  · exact hFext _ hu _ hv (by simpa using huv)

/-- The image of an extremal face under an injective linear map is an extremal face of the
image. -/
private theorem isExtremalFace_image (g : U →ₗ[ℝ] W) (hg : Function.Injective g) {C F : Set U}
    (hF : IsExtremalFace ℝ C F) : IsExtremalFace ℝ (g '' C) (g '' F) := by
  obtain ⟨hFC, ⟨hF0, hFs⟩, hFadd, hFext⟩ := hF
  refine ⟨Set.image_mono hFC, ⟨⟨0, hF0, map_zero g⟩, ?_⟩, ?_, ?_⟩
  · rintro _ ⟨v, hv, rfl⟩ c hc
    exact ⟨c • v, hFs v hv c hc, map_smul g c v⟩
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    exact ⟨u + v, hFadd u hu v hv, map_add g u v⟩
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ ⟨w, hw, hwe⟩
    obtain rfl : w = u + v := hg (by rw [hwe, map_add])
    obtain ⟨huF, hvF⟩ := hFext u hu v hv hw
    exact ⟨⟨u, huF, rfl⟩, ⟨v, hvF, rfl⟩⟩

/-- In a pointed cone containing no line, `x + y = 0` forces `x = 0`. -/
private theorem eq_zero_of_add_eq_zero {P : PointedCone ℝ W} (hP : P.lineal = ⊥) {x y : W}
    (hx : x ∈ P) (hy : y ∈ P) (h : x + y = 0) : x = 0 := by
  rw [← Submodule.mem_bot ℝ, ← hP]
  exact PointedCone.mem_lineal.2 ⟨hx, by rwa [neg_eq_of_add_eq_zero_right h]⟩

/-- **A uniform perturbation of a negative form on a closed face.** Let `F` be an extremal
face of a cone `C` in a finite-dimensional real vector space, `C` closed for the canonical
topology (expressed through the linear coordinate maps `ℝⁿ → V`), and `K` a linear form with
`K < 0` on `F ∖ {0}`. Then for every linear form `H` there is `ε > 0` with `K + εH < 0` on
`F ∖ {0}`. -/
private theorem exists_pos_forall_add_smul_neg [FiniteDimensional ℝ W] {C F : Set W}
    (hCcl : ∀ g : (Fin (Module.finrank ℝ W) → ℝ) →ₗ[ℝ] W, IsClosed (g ⁻¹' C))
    (hF : IsExtremalFace ℝ C F) {K : Module.Dual ℝ W} (hK : ∀ z ∈ F, z ≠ 0 → K z < 0)
    (H : Module.Dual ℝ W) : ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ F, z ≠ 0 → K z + ε * H z < 0 := by
  set e := (Module.finBasis ℝ W).equivFun
  set g : (Fin (Module.finrank ℝ W) → ℝ) →ₗ[ℝ] W := e.symm.toLinearMap
  have hg0 : ∀ z, g z = 0 → z = 0 := fun z hz => e.symm.injective (by simpa [g] using hz)
  have hF' := isExtremalFace_preimage g hF
  have hFconv : Convex ℝ (g ⁻¹' F) := by
    obtain ⟨P, hP⟩ := (isCone_and_add_mem_iff (g ⁻¹' F)).1 ⟨hF'.2.1, hF'.2.2.1⟩
    rw [← hP]
    exact P.convex
  have hFcl : IsClosed (g ⁻¹' F) := MMP.Positivity.IsExtremalFace.isClosed (hCcl g) hF' hFconv
  have hl : ∀ z ∈ g ⁻¹' F, 0 ≤ (-(K ∘ₗ g)) z := by
    intro z hz
    by_cases hz0 : g z = 0
    · simp [hz0]
    · simpa using (hK _ hz hz0).le
  have hlF : {z | z ∈ g ⁻¹' F ∧ (-(K ∘ₗ g)) z = 0} = {0} := by
    ext z
    refine ⟨fun ⟨h1, h2⟩ => ?_, fun h => ?_⟩
    · by_contra hz0
      exact (hK _ h1 fun h => hz0 (hg0 z h)).ne (by simpa using h2)
    · obtain rfl : z = 0 := h
      exact ⟨by simpa using hF.2.1.1, by simp⟩
  have hsal : g ⁻¹' F ∩ -(g ⁻¹' F) = {0} := by
    ext z
    refine ⟨fun ⟨h1, h2⟩ => ?_, fun h => ?_⟩
    · by_contra hz0
      have hgz : g z ≠ 0 := fun h => hz0 (hg0 z h)
      have a := hK _ h1 hgz
      have b := hK (g (-z)) h2 (by simpa using hgz)
      rw [map_neg, map_neg] at b
      linarith
    · obtain rfl : z = 0 := h
      exact ⟨by simpa using hF.2.1.1, by simpa using hF.2.1.1⟩
  obtain ⟨m₀, hm₀⟩ := MMP.Positivity.exists_forall_ge_pos_smul_sub hF'.2.1 hFconv hFcl hsal hl
    hlF (K := H ∘ₗ g) fun z hz hz0 => absurd hz hz0
  set m : ℝ := max m₀ 1
  have hm : 0 < m := one_pos.trans_le (le_max_right _ _)
  refine ⟨m⁻¹, inv_pos.2 hm, fun z hz hz0 => ?_⟩
  have hez : g (e z) = z := e.symm_apply_apply z
  have h := hm₀ m (le_max_left _ _) (e z) (by rwa [Set.mem_preimage, hez])
    (fun h => hz0 (by rw [← hez, h, map_zero]))
  simp only [LinearMap.neg_apply, LinearMap.comp_apply, hez] at h
  have : m * (K z + m⁻¹ * H z) < 0 := by
    rw [mul_add, ← mul_assoc, mul_inv_cancel₀ hm.ne', one_mul]
    linarith
  exact neg_of_mul_neg_right this hm.le

/-- **The extremality step.** Let `ι : U → W` be injective, `F` an extremal face of a pointed
cone `C ⊆ U`, `D ⊆ W` a pointed cone containing no line and `φ` a form with `φ < 0` on
`ι(F) ∖ {0}`. If `ι w = (a + ι c) + (a' + ι c')` with `w ∈ F`, `c, c' ∈ C`, `a, a' ∈ D`,
`φ a, φ a' ≥ 0` and `a + a' ∈ ι(C)`, then `a + ι c` and `a' + ι c'` lie in `ι(F)`. -/
private theorem add_mem_image_of_extremalFace (ι : U →ₗ[ℝ] W) (hinj : Function.Injective ι)
    {C : PointedCone ℝ U} {F : Set U} (hF : IsExtremalFace ℝ (C : Set U) F) {D : PointedCone ℝ W}
    (hD : D.lineal = ⊥) {φ : Module.Dual ℝ W} (hφ : ∀ z ∈ ι '' F, z ≠ 0 → φ z < 0) {a a' : W}
    (ha : a ∈ D) (ha' : a' ∈ D) (hφa : 0 ≤ φ a) (hφa' : 0 ≤ φ a') {d c c' w : U} (hd : d ∈ C)
    (hdaa : ι d = a + a') (hc : c ∈ C) (hc' : c' ∈ C) (hwF : w ∈ F)
    (hw : ι w = a + ι c + (a' + ι c')) : a + ι c ∈ ι '' F ∧ a' + ι c' ∈ ι '' F := by
  have hwd : w = d + (c + c') := hinj (by rw [hw, map_add, map_add, hdaa]; abel)
  have hdF := (hF.2.2.2 d hd (c + c') (add_mem hc hc') (hwd ▸ hwF)).1
  have haa0 : a + a' = 0 := by
    by_contra hne
    have h := hφ (a + a') ⟨d, hdF, hdaa⟩ hne
    rw [map_add] at h
    linarith
  have ha0 := eq_zero_of_add_eq_zero hD ha ha' haa0
  rw [ha0, zero_add] at haa0
  subst ha0 haa0
  have hwc : w = c + c' := hinj (by rw [hw, map_add, zero_add, zero_add])
  obtain ⟨hcF, hc'F⟩ := hF.2.2.2 c hc c' hc' (hwc ▸ hwF)
  exact ⟨⟨c, hcF, (zero_add _).symm⟩, ⟨c', hc'F, (zero_add _).symm⟩⟩

end Cones

/-- Every linear map from a coordinate space into `N₁(X)` is continuous for the numerical
topology. -/
private theorem continuous_linearMap_numericalCurveClasses {k : Type} [Field k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) {n : ℕ} (g : (Fin n → ℝ) →ₗ[ℝ] NumericalCurveClasses sX) :
    Continuous g := by
  refine continuous_iInf_rng.2 fun L => continuous_iInf_rng.2 fun h =>
    continuous_induced_rng.2 ?_
  have := h
  exact LinearMap.continuous_of_finiteDimensional ((NumericalCurveClasses.degree sX L).comp g)

/-- The image of `NE̅(X/Y)` in `N₁(X)` has closed preimages under linear maps from coordinate
spaces. -/
private theorem isClosed_preimage_image_relativeClosedConeOfCurves {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {X Y : Scheme.{0}} (sX : X ⟶ Spec (.of k))
    (sY : Y ⟶ Spec (.of k)) [AlgebraicGeometry.IsProjectiveVariety k sX]
    [AlgebraicGeometry.IsProjectiveVariety k sY] (f : X ⟶ Y)
    (hf : f ≫ sY = sX) {n : ℕ} (g : (Fin n → ℝ) →ₗ[ℝ] NumericalCurveClasses sX) :
    IsClosed (g ⁻¹' (relativeToAbsolute sX f '' (relativeClosedConeOfCurves sX f : Set _))) := by
  rw [image_relativeClosedConeOfCurves_eq_inter_range sX sY f hf, Set.preimage_inter]
  exact (isClosed_closure.preimage (continuous_linearMap_numericalCurveClasses sX g)).inter
    (Submodule.comap g (LinearMap.range (relativeToAbsolute sX f))).closed_of_finiteDimensional

/-- The cone spanned by classes of curves lies in `NE̅(X)`. -/
private theorem hull_numericalClass_le_closedConeOfCurves {k : Type} [Field k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) (T : Set (ProperCurve sX)) :
    PointedCone.hull ℝ ((fun C : ProperCurve sX => OneCycle.numericalClass sX (C.cycle ℝ)) '' T) ≤
      closedConeOfCurves sX :=
  le_trans (Submodule.span_le.2 (by
    rintro _ ⟨C, -, rfl⟩
    exact numericalClass_cycle_mem_coneOfCurves sX C)) (coneOfCurves_le_closedConeOfCurves sX)

/-- The push-forward maps `NE̅(X)` into `NE̅(Y)`. -/
private theorem pushforward_mem_closedConeOfCurves {k : Type} [Field k] {X Y : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY]
    (f : X ⟶ Y) (hf : f ≫ sY = sX) {x : NumericalCurveClasses sX}
    (hx : x ∈ closedConeOfCurves sX) :
    NumericalCurveClasses.pushforward f hf x ∈ closedConeOfCurves sY :=
  image_closedConeOfCurves_subset f hf
    (NumericalCurveClasses.isNumericalPushforward_pushforward f hf) ⟨x, hx, rfl⟩

/-- If the push-forward of the class of a curve vanishes, the curve is contracted: an ample
invertible sheaf on the target has positive degree on the image of a curve which is not. -/
private theorem isContractedBy_of_pushforward_eq_zero {k : Type} [Field k] {X Y : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY]
    (f : X ⟶ Y) (hf : f ≫ sY = sX) (L : Y.Modules)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L] (hL : Scheme.Modules.IsAmple Y L)
    (C : ProperCurve sX)
    (h : NumericalCurveClasses.pushforward f hf (OneCycle.numericalClass sX (C.cycle ℝ)) = 0) :
    C.IsContractedBy f := by
  have hdeg := congrArg (NumericalCurveClasses.degree sY L) h
  rw [NumericalCurveClasses.degree_pushforward, map_zero,
    NumericalCurveClasses.degree_numericalClass, OneCycle.degree_cycle] at hdeg
  exact MMP.ProgramBaseChange.isContractedBy_of_degree_pullback_eq_zero f hf L hL C
    (by exact_mod_cast hdeg)

/-- A class in the cone spanned by curve classes whose push-forward vanishes is the image of a
class of `NE(X/Y)`: since `NE̅(Y)` contains no line, every curve occurring in it has vanishing
push-forward, hence is contracted. -/
private theorem mem_image_relativeConeOfCurves_of_pushforward_eq_zero {k : Type} [Field k]
    {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} [IsSeparated sY]
    [LocallyOfFiniteType sY] (f : X ⟶ Y) (hf : f ≫ sY = sX) (L : Y.Modules)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L] (hL : Scheme.Modules.IsAmple Y L)
    (hY : (closedConeOfCurves sY).lineal = ⊥) (T : Set (ProperCurve sX))
    {b : NumericalCurveClasses sX}
    (hb : b ∈ PointedCone.hull ℝ
      ((fun C : ProperCurve sX => OneCycle.numericalClass sX (C.cycle ℝ)) '' T))
    (h0 : NumericalCurveClasses.pushforward f hf b = 0) :
    b ∈ relativeToAbsolute sX f '' (relativeConeOfCurves sX f : Set _) := by
  have hsub := hull_numericalClass_le_closedConeOfCurves sX T
  have hπ := fun x (hx : x ∈ closedConeOfCurves sX) => pushforward_mem_closedConeOfCurves f hf hx
  revert h0
  induction hb using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨C, -, rfl⟩ := hx
    intro h0
    have hC := isContractedBy_of_pushforward_eq_zero f hf L hL C h0
    exact ⟨C.relativeClass f hC, relativeClass_mem_relativeConeOfCurves hC, rfl⟩
  | zero => exact fun _ => ⟨0, zero_mem _, map_zero _⟩
  | add x y hx hy ihx ihy =>
    intro h0
    rw [map_add] at h0
    have hx0 := eq_zero_of_add_eq_zero hY (hπ x (hsub hx)) (hπ y (hsub hy)) h0
    rw [hx0, zero_add] at h0
    obtain ⟨x', hx', rfl⟩ := ihx hx0
    obtain ⟨y', hy', rfl⟩ := ihy h0
    exact ⟨x' + y', add_mem hx' hy', map_add _ _ _⟩
  | smul c x hx ih =>
    intro h0
    rcases eq_or_ne c 0 with rfl | hc
    · exact ⟨0, zero_mem _, by rw [map_zero, zero_smul]⟩
    · rw [LinearMap.map_smul_of_tower, smul_eq_zero] at h0
      obtain ⟨x', hx', rfl⟩ := ih (h0.resolve_left hc)
      exact ⟨c • x', Submodule.smul_mem _ c hx', LinearMap.map_smul_of_tower _ _ _⟩

/-- If `a + b + (a' + b')` has vanishing push-forward, with `a, a' ∈ NE̅(X)` and `b, b'` in the
cone spanned by finitely many curve classes, then `b` and `b'` are images of classes of
`NE(X/Y)`. -/
private theorem mem_image_relativeConeOfCurves_of_pushforward_add_eq_zero {k : Type} [Field k]
    {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} [IsSeparated sY]
    [LocallyOfFiniteType sY] (f : X ⟶ Y) (hf : f ≫ sY = sX) (L : Y.Modules)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L] (hL : Scheme.Modules.IsAmple Y L)
    (hY : (closedConeOfCurves sY).lineal = ⊥) (T : Set (ProperCurve sX))
    {a a' b b' : NumericalCurveClasses sX} (ha : a ∈ closedConeOfCurves sX)
    (ha' : a' ∈ closedConeOfCurves sX)
    (hb : b ∈ PointedCone.hull ℝ
      ((fun C : ProperCurve sX => OneCycle.numericalClass sX (C.cycle ℝ)) '' T))
    (hb' : b' ∈ PointedCone.hull ℝ
      ((fun C : ProperCurve sX => OneCycle.numericalClass sX (C.cycle ℝ)) '' T))
    (h0 : NumericalCurveClasses.pushforward f hf (a + b + (a' + b')) = 0) :
    b ∈ relativeToAbsolute sX f '' (relativeConeOfCurves sX f : Set _) ∧
      b' ∈ relativeToAbsolute sX f '' (relativeConeOfCurves sX f : Set _) := by
  have hbC := pushforward_mem_closedConeOfCurves f hf
    (hull_numericalClass_le_closedConeOfCurves sX T hb)
  have hb'C := pushforward_mem_closedConeOfCurves f hf
    (hull_numericalClass_le_closedConeOfCurves sX T hb')
  simp only [map_add] at h0
  rw [add_add_add_comm] at h0
  rw [eq_zero_of_add_eq_zero hY (add_mem (pushforward_mem_closedConeOfCurves f hf ha)
    (pushforward_mem_closedConeOfCurves f hf ha')) (add_mem hbC hb'C) h0, zero_add] at h0
  have hb0 := eq_zero_of_add_eq_zero hY hbC hb'C h0
  rw [hb0, zero_add] at h0
  exact ⟨mem_image_relativeConeOfCurves_of_pushforward_eq_zero f hf L hL hY T hb hb0,
    mem_image_relativeConeOfCurves_of_pushforward_eq_zero f hf L hL hY T hb' h0⟩

end MMP.FourfoldProofs.Km3bRelativeNegativeFaceIsAbsoluteProof

end

section

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace MMP.Mori

open MMP.FourfoldProofs.Km3bRelativeNegativeFaceIsAbsoluteProof

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- **Relative negative extremal faces are absolute** (Kollár–Mori 3.25, setting (3.21.0)). Let
`f : X ⟶ Y` be a morphism of projective varieties over an algebraically closed field `k` of
characteristic zero and `(X, Δ)` a klt pair with canonical divisor `K` and `Δ ≥ 0`. If `F` is a
`(K + Δ)`-negative extremal face of `NE̅(X/Y)`, the form being `w ↦ ((K + Δ) · ι w)`, then its
image `ι '' F` under the natural map `ι = MMP.Mori.relativeToAbsolute sX f` is a
`(K + Δ)`-negative extremal face of `NE̅(X)`. -/
@[mmp "lem_km3b_relative_negative_face_is_absolute"]
public theorem isNegativeExtremalFace_image_relativeToAbsolute {k : Type} [Field k]
    {X Y : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] {sY : Y ⟶ Spec (.of k)} {f : X ⟶ Y}
    (hf : IsProjectiveSetting k sX sY f)
    {n : ℕ} {K : Divisor X} {Δ : QDivisor X} (hklt : IsKltPair sX n K Δ) (hΔ : 0 ≤ Δ)
    {F : Set (RelativeNumericalCurveClasses sX f)}
    (hF : IsNegativeExtremalFace ℝ
      (relativeClosedConeOfCurves sX f : Set (RelativeNumericalCurveClasses sX f))
      ((MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hklt.1.2.2).comp
        (relativeToAbsolute sX f)) F) :
    IsNegativeExtremalFace ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX))
      (MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hklt.1.2.2)
      (relativeToAbsolute sX f '' F) := by
  have := hf.isAlgClosed
  have := hf.charZero
  have : AlgebraicGeometry.IsProjectiveVariety k sX := hf.isProjectiveVariety_source
  have : AlgebraicGeometry.IsProjectiveVariety k sY := hf.isProjectiveVariety_target
  have := NumericalCurveClasses.finiteDimensional_of_isProjectiveVariety sX
  set ι := relativeToAbsolute sX f
  set φ := MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hklt.1.2.2
  set π := NumericalCurveClasses.pushforward f hf.comp_eq
  have hinj : Function.Injective ι :=
    (existsUnique_isNaturalRelativeMap_and_injective sX f).2 _
      (isNaturalRelativeMap_relativeToAbsolute sX f)
  obtain ⟨hFe, -, hFneg⟩ := hF
  have hrel := image_relativeClosedConeOfCurves_eq_inter_range sX sY f hf.comp_eq
  have hface := isExtremalFace_image ι hinj hFe
  have hneg : ∀ z ∈ ι '' F, z ≠ 0 → φ z < 0 := by
    rintro _ ⟨z, hz, rfl⟩ hz0
    exact hFneg z hz fun h => hz0 (by rw [h, map_zero])
  obtain ⟨H, hHc, -, hHa⟩ := exists_isCartier_isEffective_isAmple sX
  have hHA : (Divisor.toQDivisor H).IsAmple :=
    ⟨1, one_pos, H, by rw [Nat.cast_one, one_smul], hHc, hHa⟩
  set ψ := MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor H) hHA.isQCartier
  obtain ⟨ε, hε, hεF⟩ := exists_pos_forall_add_smul_neg
    (isClosed_preimage_image_relativeClosedConeOfCurves sX sY f hf.comp_eq) hface hneg ψ
  obtain ⟨S, -, hdec⟩ := exists_finset_isRationalCurve_closedConeOfCurves_eq hklt
    (DivisorWithCoeffs.isEffective_iff_nonneg.2 hΔ) hε hHA
  obtain ⟨L, _, hL⟩ := MMP.ProgramBaseChange.exists_isAmple_of_isProjectiveVariety
    hf.isProjectiveVariety_target
  have hπι : ∀ z, π (ι z) = 0 := fun z =>
    LinearMap.mem_ker.1 (range_relativeToAbsolute_le_ker_pushforward f hf.comp_eq ⟨z, rfl⟩)
  refine ⟨⟨hface.1.trans (hrel.le.trans Set.inter_subset_left), hface.2.1, hface.2.2.1, ?_⟩,
    hface.2.2.1, hneg⟩
  rintro u hu v hv ⟨w, hwF, hw⟩
  rw [hdec] at hu hv
  obtain ⟨a, ⟨haC, haK⟩, b, hb, rfl⟩ := Set.mem_add.1 hu
  obtain ⟨a', ⟨ha'C, ha'K⟩, b', hb', rfl⟩ := Set.mem_add.1 hv
  obtain ⟨⟨c, hc, rfl⟩, ⟨c', hc', rfl⟩⟩ :=
    mem_image_relativeConeOfCurves_of_pushforward_add_eq_zero f hf.comp_eq L hL
      (lineal_closedConeOfCurves_eq_bot sY) _ haC ha'C hb hb' (hw ▸ hπι w)
  have hcR : c ∈ relativeClosedConeOfCurves sX f := subset_closure hc
  have hc'R : c' ∈ relativeClosedConeOfCurves sX f := subset_closure hc'
  obtain ⟨d, hd, hdaa⟩ : a + a' ∈ ι '' (relativeClosedConeOfCurves sX f : Set _) := by
    rw [hrel]
    refine ⟨add_mem haC ha'C, w - c - c', ?_⟩
    rw [map_sub, map_sub, hw]
    abel
  exact add_mem_image_of_extremalFace ι hinj hFe (lineal_closedConeOfCurves_eq_bot sX)
    (φ := φ + ε • ψ) (fun z hz hz0 => by simpa using hεF z hz hz0) haC ha'C (by simpa using haK)
    (by simpa using ha'K) hd hdaa hcR hc'R hwF hw

end MMP.Mori

end
