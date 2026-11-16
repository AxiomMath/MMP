module

public import MMP.AlgebraicGeometry.Analytic.JacobianLogarithm.EtaleCoordinates

/-!
# Logarithmic derivatives of transition units, and parametric integrals

Auxiliary results for the holomorphic logarithm of the family of degree-zero classes of a curve.
On standard covers of the boxes `A × V`, `V` carrying étale coordinates, the logarithmic
derivatives along `V` of the transition units of local generators of an invertible module are
regular functions, additive in the units. Čech acyclicity of standard affine covers, in pointwise
form, writes them as a separable part `∑ p(x) q(t)` plus a Čech coboundary. Parametric integrals
of holomorphic functions are holomorphic, and integrating a decomposed logarithmic derivative
along a segment recovers the transition units.

## Main results

* `MMP.JacobianLogarithm.Fam.exists_logDeriv_decomposition`: decomposition of the logarithmic
  derivatives of the transition units.

## References

* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][griffithsharris1978], Ch. 2 §6.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace Filter Topology
open MMP.Analytic MMP.Analytic.Analytification MMP.Analytic.ComplexPoints

namespace MMP.JacobianLogarithm

attribute [local instance] hasExt_of_enoughInjectives
attribute [local implicit_reducible] TopCat.Sheaf
attribute [local instance] CategoryTheory.Hom.group

section FamilyLogarithm

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Filter Topology Limits
open MMP.Analytic MMP.Analytic.Analytification MMP.Analytic.ComplexPoints
open scoped Manifold ContDiff Interval
open KaehlerDifferential TensorProduct MeasureTheory Set intervalIntegral

namespace Fam

universe u

open Stacks.CategoryTheory.CechComplex

section Kappa

variable {C J : Scheme.{0}} {f : C ⟶ Spec (.of ℂ)} {sJ : J ⟶ Spec (.of ℂ)}

/-- The morphism `t ↦ (x, t)` of `J` into `C ×_ℂ J`. -/
noncomputable def slice (x : ComplexPoints f) : J ⟶ pullback f sJ :=
  pullback.lift (sJ ≫ x.hom) (𝟙 J) (by rw [Category.assoc, x.hom_comp_structure,
    Category.comp_id, Category.id_comp])

/-- The slice `slice x` is a morphism over `Spec ℂ`: its composite with the structure morphism
of `C ×_ℂ J` is the structure morphism of `J`. -/
theorem slice_comp (x : ComplexPoints f) : slice (sJ := sJ) x ≫ prodHom f sJ = sJ := by
  rw [slice, prodHom, ← Category.assoc, pullback.lift_snd, Category.id_comp]

/-- On complex points, `slice x` sends `t` to the pair `(x, t)`. -/
theorem realize_slice (x : ComplexPoints f) (t : ComplexPoints sJ) :
    realize (slice x) (slice_comp x) t = pair x t := by
  apply ComplexPoints.ext
  apply pullback.hom_ext
  · simp only [realize_hom, slice, Category.assoc, pullback.lift_fst, pair_hom_fst]
    rw [← Category.assoc, t.hom_comp_structure, Category.id_comp]
  · simp only [realize_hom, slice, Category.assoc, pullback.lift_snd, pair_hom_snd,
      Category.comp_id]

/-- The map `t ↦ (x, t)` on complex points is continuous. -/
theorem continuous_pair_right (x : ComplexPoints f) :
    Continuous (fun t : ComplexPoints sJ => pair x t) :=
  (continuous_realize (slice x) (slice_comp x)).congr fun t => realize_slice x t

/-- If `(x, t)` lies in the chart of the box `A × V`, then `x` lies in the chart of `A` and `t`
in the chart of `V`. -/
theorem mem_chart_of_pair_mem_box {A : C.Opens} {V : J.Opens} {x : ComplexPoints f}
    {t : ComplexPoints sJ}
    (h : pair x t ∈ chart (sX := prodHom f sJ) (box (f := f) (sJ := sJ) A V)) :
    x ∈ chart A ∧ t ∈ chart V := by
  rw [mem_chart_iff] at h
  have e1 : pullback.fst f sJ (pair x t).toScheme = x.toScheme := by
    simp only [toScheme, ← Scheme.Hom.comp_apply, pair_hom_fst]
  have e2 : pullback.snd f sJ (pair x t).toScheme = t.toScheme := by
    simp only [toScheme, ← Scheme.Hom.comp_apply, pair_hom_snd]
  exact ⟨mem_chart_iff.2 (e1 ▸ h.1), mem_chart_iff.2 (e2 ▸ h.2)⟩

/-- Evaluating `∑ₗ pₗ ⊗ qₗ` on the box `A × V` at `(x, t)` gives `∑ₗ pₗ(x) qₗ(t)`. -/
theorem eval_sum_box {A : C.Opens} {V : J.Opens} {m : ℕ} (p : Fin m → Γ(C, A))
    (q : Fin m → Γ(J, V)) {x : ComplexPoints f} {t : ComplexPoints sJ} (hx : x ∈ chart A)
    (ht : t ∈ chart V) :
    eval (box (f := f) (sJ := sJ) A V) (∑ l, (pullback.fst f sJ).appLE A
        (box (f := f) (sJ := sJ) A V) inf_le_left (p l) *
        (pullback.snd f sJ).appLE V (box (f := f) (sJ := sJ) A V) inf_le_right (q l))
      ⟨pair x t, mem_chart_box hx ht⟩ = ∑ l, eval A (p l) ⟨x, hx⟩ * eval V (q l) ⟨t, ht⟩ := by
  change evalHom _ _ _ = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul]
  exact congrArg₂ (· * ·) (eval_fst_pair (p l) hx ht) (eval_snd_pair (q l) hx ht)

/-- A function on the target of an open partial homeomorphism `φ` which agrees, along `φ`, with
a function defined on an open set `S` agrees with it near `φ t` for every `t ∈ φ.source ∩ S`. -/
theorem eventually_exists_eq_of_mem_source {X E β : Type*} [TopologicalSpace X]
    [TopologicalSpace E] (φ : OpenPartialHomeomorph X E) {S : Set X} (hS : IsOpen S) {t : X}
    (ht : t ∈ φ.source) (htS : t ∈ S) (H : E → β) (g : ∀ y, y ∈ S → β)
    (hg : ∀ y (hy : y ∈ φ.source) (hyS : y ∈ S), H (φ y) = g y hyS) :
    ∀ᶠ w in 𝓝 (φ t), ∃ hw : φ.symm w ∈ S, H w = g _ hw := by
  have hmem : φ t ∈ φ.target ∩ φ.symm ⁻¹' S := by
    refine ⟨φ.map_source ht, ?_⟩
    rw [Set.mem_preimage, φ.left_inv ht]
    exact htS
  filter_upwards [(φ.isOpen_inter_preimage_symm hS).mem_nhds hmem] with w ⟨hwT, hw⟩
  have := hg _ (φ.map_target hwT) hw
  rw [φ.right_inv hwT] at this
  exact ⟨hw, this⟩

/-- A combination `∑ₗ eₗ Qₗ` of functions differentiable at `p` has derivative
`∑ₗ eₗ • Qₗ'(p)` at `p`. -/
theorem hasFDerivAt_sum_const_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {m : ℕ}
    {Q : Fin m → E → ℂ} {p : E} (hQ : ∀ l, DifferentiableAt ℂ (Q l) p) (e : Fin m → ℂ) :
    HasFDerivAt (fun w => ∑ l, e l * Q l w) (∑ l, e l • fderiv ℂ (Q l) p) p :=
  HasFDerivAt.fun_sum fun l _ => (hQ l).hasFDerivAt.const_mul (e l)

/-- The value of the inverse of a unit restricted from `U` to `V` is the inverse of the value. -/
theorem evalHom_inv_res {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {U V : X.Opens} (h : V ≤ U)
    (x : chart (sX := sX) V) (b : Γ(X, U)) (hb : IsUnit (X.presheaf.map (homOfLE h).op b)) :
    evalHom V x ((hb.unit⁻¹ : Γ(X, V)ˣ) : Γ(X, V)) = (eval U b ⟨x.1, chart_mono h x.2⟩)⁻¹ := by
  rw [map_units_inv, IsUnit.unit_spec]
  exact congrArg (·⁻¹) (evalHom_res h x b).symm

/-- **Logarithmic derivatives along `J` of units on a basic open of a box.** For a unit `u` on
`D(G) ⊆ A × V`, `V` carrying étale coordinates `z`, there are regular functions `κ i` on `D(G)`
which at every `ℂ`-point `(x, t)` are the logarithmic partial derivatives of `u (x, ·)` in the
coordinates `z`, in every étale chart built from `(V, z)`. -/
theorem exists_logDeriv_box {n : ℕ} [SmoothOfRelativeDimension n sJ] {A : C.Opens}
    (hA : IsAffineOpen A) {V : J.Opens} (hV : IsAffineOpen V) (z : Fin n → Γ(J, V))
    (hz : Etale (AffineSpace.homOfVector (V.ι ≫ sJ)
      (fun i : ULift.{0} (Fin n) ↦ V.topIso.inv (z i.down))))
    (G : Γ(pullback f sJ, box (f := f) (sJ := sJ) A V))
    (u : (Γ(pullback f sJ, (pullback f sJ).basicOpen G))ˣ) :
    ∃ κ : Fin n → Γ(pullback f sJ, (pullback f sJ).basicOpen G),
      ∀ (x : ComplexPoints f) (t : ComplexPoints sJ)
        (hq : pair x t ∈ chart (sX := prodHom f sJ) ((pullback f sJ).basicOpen G))
        (W : Set (ComplexPoints sJ)) (hWsub : W ⊆ chart V) (hWo : IsOpen W) (hne : W.Nonempty)
        (hemb : Topology.IsOpenEmbedding (fun y : W ↦ fun i ↦ eval V (z i) ⟨y.1, hWsub y.2⟩))
        (_ : t ∈ W),
        ∃ (F : (Fin n → ℂ) → ℂ) (F' : (Fin n → ℂ) →L[ℂ] ℂ),
          HasFDerivAt F F'
            ((EtaleCoordinateChart.mk V z hz W hWsub hWo hne hemb).toOpenPartialHomeomorph t) ∧
          (∀ᶠ w in 𝓝 ((EtaleCoordinateChart.mk V z hz W hWsub hWo hne hemb).toOpenPartialHomeomorph
              t), ∃ hw : pair x ((EtaleCoordinateChart.mk V z hz W hWsub hWo hne
                hemb).toOpenPartialHomeomorph.symm w) ∈
                chart (sX := prodHom f sJ) ((pullback f sJ).basicOpen G),
              F w = eval _ (u : Γ(pullback f sJ, (pullback f sJ).basicOpen G)) ⟨_, hw⟩) ∧
          ∀ i, F' (Pi.single i 1) =
            eval _ (κ i) ⟨pair x t, hq⟩ *
              eval _ (u : Γ(pullback f sJ, (pullback f sJ).basicOpen G)) ⟨pair x t, hq⟩ := by
  classical
  have hB : IsAffineOpen (box (f := f) (sJ := sJ) A V) := isAffineOpen_box hA hV
  let ρ : Γ(pullback f sJ, box (f := f) (sJ := sJ) A V) →+*
      Γ(pullback f sJ, (pullback f sJ).basicOpen G) :=
    ((pullback f sJ).presheaf.map (homOfLE ((pullback f sJ).basicOpen_le G)).op).hom
  letI : Algebra Γ(pullback f sJ, box (f := f) (sJ := sJ) A V)
      Γ(pullback f sJ, (pullback f sJ).basicOpen G) := ρ.toAlgebra
  haveI : IsLocalization.Away G Γ(pullback f sJ, (pullback f sJ).basicOpen G) :=
    hB.isLocalization_basicOpen G
  obtain ⟨k, a, hau⟩ : ∃ (k : ℕ) (a : Γ(pullback f sJ, box (f := f) (sJ := sJ) A V)),
      (u : Γ(pullback f sJ, (pullback f sJ).basicOpen G)) * ρ G ^ k = ρ a :=
    IsLocalization.Away.surj G _
  have hGu : IsUnit (ρ G) := IsLocalization.Away.algebraMap_isUnit G
  have hau' : IsUnit (ρ a) := hau ▸ (u.isUnit.mul (hGu.pow k))
  obtain ⟨m₁, p₁, q₁, ha⟩ := exists_sum_box hA hV a
  obtain ⟨m₂, p₂, q₂, hG⟩ := exists_sum_box hA hV G
  let D := etaleDerivation V hV z hz
  let Dlift : ∀ {m : ℕ} (_ : Fin m → Γ(C, A)) (_ : Fin m → Γ(J, V)),
      Fin n → Γ(pullback f sJ, box (f := f) (sJ := sJ) A V) := fun p q i =>
    ∑ l, (pullback.fst f sJ).appLE A (box (f := f) (sJ := sJ) A V) inf_le_left (p l) *
      (pullback.snd f sJ).appLE V (box (f := f) (sJ := sJ) A V) inf_le_right (D i (q l))
  let κ : Fin n → Γ(pullback f sJ, (pullback f sJ).basicOpen G) := fun i =>
    ρ (Dlift p₁ q₁ i) * ↑(hau'.unit⁻¹) - (k : Γ(pullback f sJ, (pullback f sJ).basicOpen G)) *
      ρ (Dlift p₂ q₂ i) * ↑(hGu.unit⁻¹)
  refine ⟨κ, fun x t hq W hWsub hWo hne hemb ht => ?_⟩
  set c := EtaleCoordinateChart.mk V z hz W hWsub hWo hne hemb with hc
  set φ := c.toOpenPartialHomeomorph with hφ
  have hsrc : φ.source = W := c.source_toOpenPartialHomeomorph
  have hqB : pair x t ∈ chart (sX := prodHom f sJ) (box (f := f) (sJ := sJ) A V) :=
    chart_mono ((pullback f sJ).basicOpen_le G) hq
  obtain ⟨hxA, htV⟩ := mem_chart_of_pair_mem_box hqB
  choose Q₁ hQ₁a hQ₁e hQ₁d using fun l => exists_derivation_etaleChart c hV (q₁ l)
  choose Q₂ hQ₂a hQ₂e hQ₂d using fun l => exists_derivation_etaleChart c hV (q₂ l)
  let Ax : (Fin n → ℂ) → ℂ := fun w => ∑ l, eval A (p₁ l) ⟨x, hxA⟩ * Q₁ l w
  let Gx : (Fin n → ℂ) → ℂ := fun w => ∑ l, eval A (p₂ l) ⟨x, hxA⟩ * Q₂ l w
  have htT : φ t ∈ φ.target := φ.map_source (hsrc ▸ ht)
  have hAx : ∀ t' (ht' : t' ∈ W), Ax (φ t') =
      eval _ a ⟨pair x t', mem_chart_box hxA (hWsub ht')⟩ := by
    intro t' ht'
    rw [ha, eval_sum_box p₁ q₁ hxA (hWsub ht')]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hQ₁e l t' ht']
  have hGx : ∀ t' (ht' : t' ∈ W), Gx (φ t') =
      eval _ G ⟨pair x t', mem_chart_box hxA (hWsub ht')⟩ := by
    intro t' ht'
    rw [hG, eval_sum_box p₂ q₂ hxA (hWsub ht')]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hQ₂e l t' ht']
  have hres : ∀ (b : Γ(pullback f sJ, box (f := f) (sJ := sJ) A V)) (t' : ComplexPoints sJ)
      (hw : pair x t' ∈ chart (sX := prodHom f sJ) ((pullback f sJ).basicOpen G)),
      eval _ (ρ b) ⟨pair x t', hw⟩ =
        eval _ b ⟨pair x t', chart_mono ((pullback f sJ).basicOpen_le G) hw⟩ := fun b t' hw =>
    (evalHom_res ((pullback f sJ).basicOpen_le G) ⟨pair x t', hw⟩ b).symm
  have hGne : ∀ t' (hw : pair x t' ∈ chart (sX := prodHom f sJ) ((pullback f sJ).basicOpen G)),
      eval _ G ⟨pair x t', chart_mono ((pullback f sJ).basicOpen_le G) hw⟩ ≠ 0 := fun t' hw =>
    (toScheme_mem_basicOpen_iff ⟨pair x t', chart_mono ((pullback f sJ).basicOpen_le G) hw⟩ G).1
      (mem_chart_iff.1 hw)
  have hu_val : ∀ t' (hw : pair x t' ∈ chart (sX := prodHom f sJ) ((pullback f sJ).basicOpen G)),
      eval _ (u : Γ(pullback f sJ, (pullback f sJ).basicOpen G)) ⟨pair x t', hw⟩ =
        eval _ a ⟨pair x t', chart_mono ((pullback f sJ).basicOpen_le G) hw⟩ /
          eval _ G ⟨pair x t', chart_mono ((pullback f sJ).basicOpen_le G) hw⟩ ^ k := by
    intro t' hw
    have h1 := congrArg (fun r => evalHom _ ⟨pair x t', hw⟩ r) hau
    simp only [map_mul, map_pow] at h1
    change ComplexPoints.eval _ _ _ * ComplexPoints.eval _ (ρ G) _ ^ k =
      ComplexPoints.eval _ (ρ a) _ at h1
    rw [hres, hres] at h1
    rw [eq_div_iff (pow_ne_zero _ (hGne t' hw)), h1]
  have hG0 : Gx (φ t) ≠ 0 := hGx t ht ▸ hGne t hq
  obtain ⟨F', hF', hF'e⟩ := hasFDerivAt_div_pow
    (hasFDerivAt_sum_const_mul (fun l => (hQ₁a l _ htT).differentiableAt) _)
    (hasFDerivAt_sum_const_mul (fun l => (hQ₂a l _ htT).differentiableAt) _) hG0 k
  refine ⟨fun w => Ax w / Gx w ^ k, F', hF', ?_, fun i => ?_⟩
  · refine eventually_exists_eq_of_mem_source φ
      ((isOpen_chart _ _).preimage (continuous_pair_right x)) (hsrc ▸ ht) hq _
      (fun y hy => eval _ (u : Γ(pullback f sJ, (pullback f sJ).basicOpen G)) ⟨pair x y, hy⟩)
      fun y hy hyS => ?_
    rw [hAx _ (hsrc ▸ hy), hGx _ (hsrc ▸ hy), hu_val _ hyS]
  · rw [hF'e]
    have hd : ∀ {m : ℕ} (p : Fin m → Γ(C, A)) (q : Fin m → Γ(J, V)) (Q : Fin m → (Fin n → ℂ) → ℂ),
        (∀ l, fderiv ℂ (Q l) (φ t) (Pi.single i 1) =
          ComplexPoints.eval V (D i (q l)) ⟨t, htV⟩) →
        (∑ l, ComplexPoints.eval A (p l) ⟨x, hxA⟩ • fderiv ℂ (Q l) (φ t)) (Pi.single i 1) =
          ComplexPoints.eval _ (Dlift p q i) ⟨pair x t, mem_chart_box hxA htV⟩ := by
      intro m p q Q hQ
      rw [ContinuousLinearMap.sum_apply]
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [eval_sum_box p (fun l => D i (q l)) hxA htV]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hQ l]
    rw [hd p₁ q₁ Q₁ (fun l => hQ₁d l t ht i), hd p₂ q₂ Q₂ (fun l => hQ₂d l t ht i)]
    have hinv : ∀ (b : Γ(pullback f sJ, box (f := f) (sJ := sJ) A V)) (hb : IsUnit (ρ b)),
        evalHom _ ⟨pair x t, hq⟩ ((hb.unit⁻¹ : (Γ(pullback f sJ,
          (pullback f sJ).basicOpen G))ˣ) : Γ(pullback f sJ, (pullback f sJ).basicOpen G)) =
          (ComplexPoints.eval _ b
            ⟨pair x t, chart_mono ((pullback f sJ).basicOpen_le G) hq⟩)⁻¹ := fun b hb =>
      evalHom_inv_res _ _ b hb
    have hκv : ComplexPoints.eval _ (κ i) ⟨pair x t, hq⟩ =
        ComplexPoints.eval _ (Dlift p₁ q₁ i) ⟨pair x t, mem_chart_box hxA htV⟩ *
            (ComplexPoints.eval _ a ⟨pair x t, mem_chart_box hxA htV⟩)⁻¹ -
          k * ComplexPoints.eval _ (Dlift p₂ q₂ i) ⟨pair x t, mem_chart_box hxA htV⟩ *
            (ComplexPoints.eval _ G ⟨pair x t, mem_chart_box hxA htV⟩)⁻¹ := by
      change evalHom _ _ (κ i) = _
      simp only [κ, map_sub, map_mul, map_natCast]
      rw [hinv a hau', hinv G hGu]
      change ComplexPoints.eval _ (ρ _) _ * _ - _ * ComplexPoints.eval _ (ρ _) _ * _ = _
      rw [hres, hres]
    have hA' : (∑ l, ComplexPoints.eval A (p₁ l) ⟨x, hxA⟩ * Q₁ l (φ t)) = _ := hAx t ht
    have hG' : (∑ l, ComplexPoints.eval A (p₂ l) ⟨x, hxA⟩ * Q₂ l (φ t)) = _ := hGx t ht
    rw [hκv, hu_val t hq, hA', hG']
    have hG0' := hGne t hq
    have ha0 : ComplexPoints.eval _ a ⟨pair x t, chart_mono ((pullback f sJ).basicOpen_le G) hq⟩
        ≠ 0 := fun h0 =>
      (u.isUnit.map (evalHom _ ⟨pair x t, hq⟩)).ne_zero
        (by rw [evalHom_apply, hu_val t hq, h0, zero_div])
    field_simp
    ring

/-- **Local generators of an invertible module on a standard cover of an affine open.** -/
theorem exists_standardCover_generators (X : Scheme.{0})
    (L : SheafOfModules.{0} (structureSheaf X.toRingedSpace.sheaf))
    (hL : Stacks.SheafOfModules.IsInvertible X.toRingedSpace.sheaf.obj
      (structureSheaf X.toRingedSpace.sheaf).property L)
    {B : X.Opens} (hB : IsAffineOpen B) :
    ∃ (s : ℕ) (F : Fin s → Γ(X, B)), Ideal.span (Set.range F) = ⊤ ∧
      Nonempty (∀ m, Stacks.SheafOfModules.GeneratorSections X.toRingedSpace L
        (X.basicOpen (F m))) := by
  classical
  let T := Stacks.Cohomology.Generators.generatorTorsorOfInvertible X.toRingedSpace L hL
  -- a generator near every point of `B`, on a basic open of `B`
  have hloc : ∀ q : B, ∃ g : Γ(X, B), q.1 ∈ X.basicOpen g ∧
      Nonempty (Stacks.SheafOfModules.GeneratorSections X.toRingedSpace L (X.basicOpen g)) := by
    intro q
    obtain ⟨U, hqU, ⟨s0⟩⟩ := T.isTorsor.2 q.1
    obtain ⟨g, hgU, hqg⟩ := hB.exists_basicOpen_le ⟨q.1, hqU⟩ q.2
    exact ⟨g, hqg, ⟨Stacks.SheafOfModules.generatorRestrict L hgU (T.sectionsEquiv U s0)⟩⟩
  choose g hqg hgen using hloc
  have hspan : Ideal.span (Set.range g) = ⊤ := by
    rw [← hB.self_le_iSup_basicOpen_iff]
    intro p hp
    exact Opens.mem_iSup.2 ⟨⟨g ⟨p, hp⟩, ⟨p, hp⟩, rfl⟩, hqg ⟨p, hp⟩⟩
  obtain ⟨S, hSsub, hS1⟩ := Submodule.mem_span_finite_of_mem_span
    (show (1 : Γ(X, B)) ∈ Submodule.span Γ(X, B) (Set.range g) by
      rw [show Submodule.span Γ(X, B) (Set.range g) = Ideal.span (Set.range g) from rfl, hspan]
      exact Submodule.mem_top)
  have hSmem : ∀ y ∈ S, ∃ q, g q = y := fun y hy => hSsub hy
  choose qS hqS using hSmem
  let F : Fin S.card → Γ(X, B) := fun m => (S.equivFin.symm m).1
  refine ⟨S.card, F, ?_, ⟨fun m => ?_⟩⟩
  · rw [eq_top_iff, ← Ideal.span_singleton_one, Ideal.span_le, Set.singleton_subset_iff]
    refine Submodule.span_mono ?_ hS1
    intro y hy
    exact ⟨S.equivFin ⟨y, hy⟩, by simp [F]⟩
  · have hgen' := (hgen (qS (S.equivFin.symm m).1 (S.equivFin.symm m).2)).some
    rwa [hqS (S.equivFin.symm m).1 (S.equivFin.symm m).2] at hgen'

/-- `exists_logDeriv_box` for an open equal to the basic open. -/
theorem exists_logDeriv_of_eq_basicOpen {n : ℕ} [SmoothOfRelativeDimension n sJ] {A : C.Opens}
    (hA : IsAffineOpen A) {V : J.Opens} (hV : IsAffineOpen V) (z : Fin n → Γ(J, V))
    (hz : Etale (AffineSpace.homOfVector (V.ι ≫ sJ)
      (fun i : ULift.{0} (Fin n) ↦ V.topIso.inv (z i.down))))
    (G : Γ(pullback f sJ, box (f := f) (sJ := sJ) A V)) (N : (pullback f sJ).Opens)
    (hN : N = (pullback f sJ).basicOpen G) (u : (Γ(pullback f sJ, N))ˣ) :
    ∃ κ : Fin n → Γ(pullback f sJ, N),
      ∀ (x : ComplexPoints f) (t : ComplexPoints sJ)
        (hq : pair x t ∈ chart (sX := prodHom f sJ) N)
        (W : Set (ComplexPoints sJ)) (hWsub : W ⊆ chart V) (hWo : IsOpen W) (hne : W.Nonempty)
        (hemb : Topology.IsOpenEmbedding (fun y : W ↦ fun i ↦ eval V (z i) ⟨y.1, hWsub y.2⟩))
        (_ : t ∈ W),
        ∃ (F : (Fin n → ℂ) → ℂ) (F' : (Fin n → ℂ) →L[ℂ] ℂ),
          HasFDerivAt F F'
            ((EtaleCoordinateChart.mk V z hz W hWsub hWo hne hemb).toOpenPartialHomeomorph t) ∧
          (∀ᶠ w in 𝓝 ((EtaleCoordinateChart.mk V z hz W hWsub hWo hne hemb).toOpenPartialHomeomorph
              t), ∃ hw : pair x ((EtaleCoordinateChart.mk V z hz W hWsub hWo hne
                hemb).toOpenPartialHomeomorph.symm w) ∈ chart (sX := prodHom f sJ) N,
              F w = eval _ (u : Γ(pullback f sJ, N)) ⟨_, hw⟩) ∧
          ∀ i, F' (Pi.single i 1) =
            eval _ (κ i) ⟨pair x t, hq⟩ * eval _ (u : Γ(pullback f sJ, N)) ⟨pair x t, hq⟩ := by
  subst hN
  exact exists_logDeriv_box hA hV z hz G u

/-- The box over `A ⊓ A'` is the intersection of the boxes over `A` and `A'`. -/
theorem box_inf (A A' : C.Opens) (V : J.Opens) :
    box (f := f) (sJ := sJ) (A ⊓ A') V =
      box (f := f) (sJ := sJ) A V ⊓ box (f := f) (sJ := sJ) A' V := by
  simp only [box, Scheme.Hom.preimage_inf]
  ext q
  simp only [Opens.coe_inf, Set.mem_inter_iff, SetLike.mem_coe]
  tauto

/-- The intersection of two basic opens of boxes is a basic open of the box of the
intersection. -/
theorem basicOpen_inf_eq {A A' : C.Opens} {V : J.Opens}
    (F₁ : Γ(pullback f sJ, box (f := f) (sJ := sJ) A V))
    (F₂ : Γ(pullback f sJ, box (f := f) (sJ := sJ) A' V)) :
    (pullback f sJ).basicOpen F₁ ⊓ (pullback f sJ).basicOpen F₂ =
      (pullback f sJ).basicOpen
        ((pullback f sJ).presheaf.map (homOfLE ((box_inf A A' V).le.trans inf_le_left :
          box (f := f) (sJ := sJ) (A ⊓ A') V ≤ box (f := f) (sJ := sJ) A V)).op F₁ *
        (pullback f sJ).presheaf.map (homOfLE ((box_inf A A' V).le.trans inf_le_right :
          box (f := f) (sJ := sJ) (A ⊓ A') V ≤ box (f := f) (sJ := sJ) A' V)).op F₂) := by
  rw [Scheme.basicOpen_mul, Scheme.basicOpen_res, Scheme.basicOpen_res, box_inf]
  have h1 := (pullback f sJ).basicOpen_le F₁
  have h2 := (pullback f sJ).basicOpen_le F₂
  exact le_antisymm
    (le_inf (le_inf (le_inf (inf_le_left.trans h1) (inf_le_right.trans h2)) inf_le_left)
      (le_inf (le_inf (inf_le_left.trans h1) (inf_le_right.trans h2)) inf_le_right))
    (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right))

/-- **Additivity of logarithmic derivatives.** -/
theorem logDeriv_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {p : E}
    {F₁ F₂ F₃ : E → ℂ} {F₁' F₂' F₃' : E →L[ℂ] ℂ} (h₁ : HasFDerivAt F₁ F₁' p)
    (h₂ : HasFDerivAt F₂ F₂' p) (h₃ : HasFDerivAt F₃ F₃' p)
    (h : (fun w => F₁ w * F₂ w) =ᶠ[𝓝 p] F₃) {e : E} {κ₁ κ₂ κ₃ : ℂ}
    (hk₁ : F₁' e = κ₁ * F₁ p) (hk₂ : F₂' e = κ₂ * F₂ p) (hk₃ : F₃' e = κ₃ * F₃ p)
    (h0 : F₃ p ≠ 0) : κ₁ + κ₂ = κ₃ := by
  have hp : F₁ p * F₂ p = F₃ p := h.self_of_nhds
  have hmul := (h₁.mul h₂).congr_of_eventuallyEq h.symm
  have huniq := hmul.unique h₃
  have := congrArg (fun T : E →L[ℂ] ℂ => T e) huniq
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    hk₁, hk₂, hk₃] at this
  apply mul_right_cancel₀ h0
  rw [← hp] at this ⊢
  linear_combination this

/-- The basic open `N j` of the standard cover of the box `A j.1 × V`. -/
noncomputable abbrev Nopen {r : ℕ} {A : Fin r → C.Opens} {V : J.Opens} {s : Fin r → ℕ}
    (F : ∀ c, Fin (s c) → Γ(pullback f sJ, box (f := f) (sJ := sJ) (A c) V))
    (j : Σ c, Fin (s c)) : (pullback f sJ).Opens :=
  (pullback f sJ).basicOpen (F j.1 j.2)

/-- The transition unit of the generators on `N j ⊓ N k`. -/
noncomputable abbrev transUnit {r : ℕ} {A : Fin r → C.Opens} {V : J.Opens} {s : Fin r → ℕ}
    (F : ∀ c, Fin (s c) → Γ(pullback f sJ, box (f := f) (sJ := sJ) (A c) V))
    (M : SheafOfModules.{0} (structureSheaf (pullback f sJ).toRingedSpace.sheaf))
    (ε : ∀ j : Σ c, Fin (s c), Stacks.SheafOfModules.GeneratorSections
      (pullback f sJ).toRingedSpace M (Nopen F j)) (j k : Σ c, Fin (s c)) :
    (Γ(pullback f sJ, Nopen F j ⊓ Nopen F k))ˣ :=
  Stacks.SheafOfModules.generatorRatioUnit M (Nopen F j ⊓ Nopen F k)
    (Stacks.SheafOfModules.generatorRestrict M inf_le_left (ε j))
    (Stacks.SheafOfModules.generatorRestrict M inf_le_right (ε k))

/-- The cocycle identity for the transition units: at a point of the triple overlap,
`transUnit j k · transUnit k l = transUnit j l`. -/
theorem transUnit_mul_apply {r : ℕ} {A : Fin r → C.Opens} {V : J.Opens} {s : Fin r → ℕ}
    (F : ∀ c, Fin (s c) → Γ(pullback f sJ, box (f := f) (sJ := sJ) (A c) V))
    (M : SheafOfModules.{0} (structureSheaf (pullback f sJ).toRingedSpace.sheaf))
    (ε : ∀ j : Σ c, Fin (s c), Stacks.SheafOfModules.GeneratorSections
      (pullback f sJ).toRingedSpace M (Nopen F j)) (j k l : Σ c, Fin (s c))
    (q : ComplexPoints (prodHom f sJ)) (h1 : q ∈ chart (Nopen F j)) (h2 : q ∈ chart (Nopen F k))
    (h3 : q ∈ chart (Nopen F l)) :
    eval _ (transUnit F M ε j k : Γ(pullback f sJ, Nopen F j ⊓ Nopen F k))
        ⟨q, mem_chart_iff.2 ⟨mem_chart_iff.1 h1, mem_chart_iff.1 h2⟩⟩ *
      eval _ (transUnit F M ε k l : Γ(pullback f sJ, Nopen F k ⊓ Nopen F l))
        ⟨q, mem_chart_iff.2 ⟨mem_chart_iff.1 h2, mem_chart_iff.1 h3⟩⟩ =
      eval _ (transUnit F M ε j l : Γ(pullback f sJ, Nopen F j ⊓ Nopen F l))
        ⟨q, mem_chart_iff.2 ⟨mem_chart_iff.1 h1, mem_chart_iff.1 h3⟩⟩ := by
  set T := Nopen F j ⊓ Nopen F k ⊓ Nopen F l
  have hq : q ∈ chart (sX := prodHom f sJ) T :=
    mem_chart_iff.2 ⟨⟨mem_chart_iff.1 h1, mem_chart_iff.1 h2⟩, mem_chart_iff.1 h3⟩
  have r1 : T ≤ Nopen F j ⊓ Nopen F k := inf_le_left
  have r2 : T ≤ Nopen F k ⊓ Nopen F l := le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have r3 : T ≤ Nopen F j ⊓ Nopen F l := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  -- the three transition units restricted to `T`, evaluated at `q`
  have e : ∀ {a b : Σ c, Fin (s c)} (hab : T ≤ Nopen F a ⊓ Nopen F b),
      evalHom T ⟨q, hq⟩ (Stacks.SheafOfModules.generatorRatioUnit M T
        (Stacks.SheafOfModules.generatorRestrict M (hab.trans inf_le_left) (ε a))
        (Stacks.SheafOfModules.generatorRestrict M (hab.trans inf_le_right) (ε b))).val =
      evalHom (Nopen F a ⊓ Nopen F b) ⟨q, chart_mono hab hq⟩
        (transUnit F M ε a b : Γ(pullback f sJ, Nopen F a ⊓ Nopen F b)) := by
    intro a b hab
    rw [← Stacks.SheafOfModules.generatorRestrict_trans M inf_le_left hab,
      ← Stacks.SheafOfModules.generatorRestrict_trans M inf_le_right hab,
      Stacks.SheafOfModules.generatorRatioUnit_restrict]
    exact (evalHom_res hab ⟨q, hq⟩ _).symm
  have hcomp := Stacks.SheafOfModules.generatorRatioUnit_comp M T
    (Stacks.SheafOfModules.generatorRestrict M (r1.trans inf_le_left) (ε j))
    (Stacks.SheafOfModules.generatorRestrict M (r1.trans inf_le_right) (ε k))
    (Stacks.SheafOfModules.generatorRestrict M (r2.trans inf_le_right) (ε l))
  have hv := congrArg (fun w => evalHom T ⟨q, hq⟩ w.val) hcomp
  simp only [Units.val_mul, map_mul] at hv
  rw [mul_comm]
  exact (congrArg₂ (· * ·) (e r2).symm (e r1).symm).trans
    ((map_mul (evalHom T ⟨q, hq⟩) _ _).symm.trans (hv.trans (e r3)))

/-- **Čech `H¹` of a standard affine cover vanishes, pointwise form.** A family of functions on
the pairwise intersections of a standard cover of an affine open whose values satisfy the cocycle
identity at every `ℂ`-point is, pointwise, a coboundary of functions on the members. -/
theorem exists_coboundary_pointwise {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sX] [QuasiCompact sX] [IsReduced X] {U : X.Opens} (hU : IsAffineOpen U)
    {s : ℕ} (g : Fin s → Γ(X, U)) (hg : Ideal.span (Set.range g) = ⊤)
    (κ : ∀ m m' : Fin s, Γ(X, X.basicOpen (g m) ⊓ X.basicOpen (g m')))
    (hcoc : ∀ (m m' m'' : Fin s) (y : ComplexPoints sX) (h1 : y ∈ chart (X.basicOpen (g m)))
      (h2 : y ∈ chart (X.basicOpen (g m'))) (h3 : y ∈ chart (X.basicOpen (g m''))),
      eval _ (κ m m') ⟨y, mem_chart_iff.2 ⟨mem_chart_iff.1 h1, mem_chart_iff.1 h2⟩⟩ +
        eval _ (κ m' m'') ⟨y, mem_chart_iff.2 ⟨mem_chart_iff.1 h2, mem_chart_iff.1 h3⟩⟩ =
      eval _ (κ m m'') ⟨y, mem_chart_iff.2 ⟨mem_chart_iff.1 h1, mem_chart_iff.1 h3⟩⟩) :
    ∃ h : ∀ m : Fin s, Γ(X, X.basicOpen (g m)),
      ∀ (m m' : Fin s) (y : ComplexPoints sX) (h1 : y ∈ chart (X.basicOpen (g m)))
        (h2 : y ∈ chart (X.basicOpen (g m'))),
        eval _ (κ m m') ⟨y, mem_chart_iff.2 ⟨mem_chart_iff.1 h1, mem_chart_iff.1 h2⟩⟩ =
          eval _ (h m') ⟨y, h2⟩ - eval _ (h m) ⟨y, h1⟩ := by
  classical
  let Vf : Fin s → X.Opens := fun m => X.basicOpen (g m)
  have hle2 : ∀ x : Fin 2 → Fin s,
      Stacks.CategoryTheory.CechComplex.inter Vf x ≤ Vf (x 0) ⊓ Vf (x 1) := by
    intro x
    rw [Stacks.CategoryTheory.CechComplex.inter_eq_iInf]
    exact le_inf (iInf_le _ 0) (iInf_le _ 1)
  have hmem : ∀ {k : ℕ} (x : Fin (k + 1) → Fin s) (y : ComplexPoints sX),
      (∀ a, y ∈ chart (Vf (x a))) → y ∈ chart (Stacks.CategoryTheory.CechComplex.inter Vf x) := by
    intro k x y hy
    rw [mem_chart_iff, Stacks.CategoryTheory.CechComplex.inter_eq_iInf, ← SetLike.mem_coe,
      Opens.coe_iInf]
    exact Set.mem_iInter.2 fun a => mem_chart_iff.1 (hy a)
  have hmem' : ∀ {k : ℕ} (x : Fin (k + 1) → Fin s) (y : ComplexPoints sX) (a : Fin (k + 1)),
      y ∈ chart (Stacks.CategoryTheory.CechComplex.inter Vf x) → y ∈ chart (Vf (x a)) := by
    intro k x y a hy
    rw [mem_chart_iff, Stacks.CategoryTheory.CechComplex.inter_eq_iInf, ← SetLike.mem_coe,
      Opens.coe_iInf] at hy
    exact mem_chart_iff.2 (Set.mem_iInter.1 hy a)
  have hinterAff : ∀ {k : ℕ} (x : Fin (k + 1) → Fin s),
      IsAffineOpen (Stacks.CategoryTheory.CechComplex.inter Vf x) := by
    intro k x
    rw [Stacks.Cohomology.Cech.inter_eq_basicOpen g x]
    exact hU.basicOpen _
  let κc : ∀ x : Fin 2 → Fin s, Γ(X, Stacks.CategoryTheory.CechComplex.inter Vf x) := fun x =>
    X.presheaf.map (homOfLE (hle2 x)).op (κ (x 0) (x 1))
  -- values of `κc`
  have hκc : ∀ (x : Fin 2 → Fin s) (y : ComplexPoints sX)
      (hy : y ∈ chart (Stacks.CategoryTheory.CechComplex.inter Vf x)),
      evalHom _ ⟨y, hy⟩ (κc x) = eval _ (κ (x 0) (x 1)) ⟨y, mem_chart_iff.2
        ⟨mem_chart_iff.1 (hmem' x y 0 hy), mem_chart_iff.1 (hmem' x y 1 hy)⟩⟩ :=
    fun x y hy => (evalHom_res (hle2 x) ⟨y, hy⟩ _).symm
  -- the cocycle identity in the form required by `exists_coboundary_of_standardCover`
  have hcocY : ∀ y : Fin 3 → Fin s,
      X.presheaf.map (homOfLE (Stacks.Cohomology.Cech.inter_le_inter g y 0)).op
          (κc fun i ↦ y ((0 : Fin 3).succAbove i)) -
        X.presheaf.map (homOfLE (Stacks.Cohomology.Cech.inter_le_inter g y 1)).op
          (κc fun i ↦ y ((1 : Fin 3).succAbove i)) +
        X.presheaf.map (homOfLE (Stacks.Cohomology.Cech.inter_le_inter g y 2)).op
          (κc fun i ↦ y ((2 : Fin 3).succAbove i)) = 0 := by
    intro y
    apply eq_zero_of_forall_evalHom_eq_zero (sX := sX) (hinterAff y)
    intro ⟨q, hq⟩
    have hy : ∀ a, q ∈ chart (Vf (y a)) := fun a => hmem' y q a hq
    have hterm : ∀ j : Fin 3, evalHom _ ⟨q, hq⟩
        (X.presheaf.map (homOfLE (Stacks.Cohomology.Cech.inter_le_inter g y j)).op
          (κc fun i ↦ y (j.succAbove i))) =
        eval _ (κ (y (j.succAbove 0)) (y (j.succAbove 1))) ⟨q, mem_chart_iff.2
          ⟨mem_chart_iff.1 (hy _), mem_chart_iff.1 (hy _)⟩⟩ := by
      intro j
      rw [← evalHom_res]
      exact hκc _ _ _
    have m01 : q ∈ chart (X.basicOpen (g (y 0)) ⊓ X.basicOpen (g (y 1))) :=
      mem_chart_iff.2 ⟨mem_chart_iff.1 (hy 0), mem_chart_iff.1 (hy 1)⟩
    have m02 : q ∈ chart (X.basicOpen (g (y 0)) ⊓ X.basicOpen (g (y 2))) :=
      mem_chart_iff.2 ⟨mem_chart_iff.1 (hy 0), mem_chart_iff.1 (hy 2)⟩
    have m12 : q ∈ chart (X.basicOpen (g (y 1)) ⊓ X.basicOpen (g (y 2))) :=
      mem_chart_iff.2 ⟨mem_chart_iff.1 (hy 1), mem_chart_iff.1 (hy 2)⟩
    have t0 : evalHom _ ⟨q, hq⟩
        (X.presheaf.map (homOfLE (Stacks.Cohomology.Cech.inter_le_inter g y 0)).op
          (κc fun i ↦ y ((0 : Fin 3).succAbove i))) = eval _ (κ (y 1) (y 2)) ⟨q, m12⟩ := hterm 0
    have t1 : evalHom _ ⟨q, hq⟩
        (X.presheaf.map (homOfLE (Stacks.Cohomology.Cech.inter_le_inter g y 1)).op
          (κc fun i ↦ y ((1 : Fin 3).succAbove i))) = eval _ (κ (y 0) (y 2)) ⟨q, m02⟩ := hterm 1
    have t2 : evalHom _ ⟨q, hq⟩
        (X.presheaf.map (homOfLE (Stacks.Cohomology.Cech.inter_le_inter g y 2)).op
          (κc fun i ↦ y ((2 : Fin 3).succAbove i))) = eval _ (κ (y 0) (y 1)) ⟨q, m01⟩ := hterm 2
    rw [map_add, map_sub, t0, t1, t2]
    linear_combination hcoc (y 0) (y 1) (y 2) q (hy 0) (hy 1) (hy 2)
  obtain ⟨h0, hh0⟩ := exists_coboundary_of_standardCover hU g hg κc hcocY
  have hle1 : ∀ m, Vf m ≤ Stacks.CategoryTheory.CechComplex.inter Vf (fun _ : Fin 1 => m) := by
    intro m
    rw [Stacks.CategoryTheory.CechComplex.inter_eq_iInf]
    exact le_iInf fun _ => le_rfl
  refine ⟨fun m => X.presheaf.map (homOfLE (hle1 m)).op (h0 m), fun m m' y h1 h2 => ?_⟩
  have hyx : y ∈ chart (Stacks.CategoryTheory.CechComplex.inter Vf ![m, m']) :=
    hmem _ y (fun a => by fin_cases a; exacts [h1, h2])
  have hv := congrArg (evalHom _ ⟨y, hyx⟩) (hh0 ![m, m'])
  rw [hκc, map_sub, ← evalHom_res, ← evalHom_res] at hv
  refine hv.trans ?_
  congr 1
  · exact evalHom_res (hle1 m') ⟨y, h2⟩ (h0 m')
  · exact evalHom_res (hle1 m) ⟨y, h1⟩ (h0 m)

/-- **Gluing of functions, pointwise form.** On an affine open `U` covered by the basic opens of
sections `g₁, …, gₛ` generating the unit ideal, functions on the members whose values agree at
every `ℂ`-point of the overlaps glue to a function on `U`. -/
theorem exists_glue_pointwise {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sX] [QuasiCompact sX] [IsReduced X] {U : X.Opens} (hU : IsAffineOpen U)
    {s : ℕ} (g : Fin s → Γ(X, U)) (hg : Ideal.span (Set.range g) = ⊤)
    (σ : ∀ m : Fin s, Γ(X, X.basicOpen (g m)))
    (hcomp : ∀ (m m' : Fin s) (y : ComplexPoints sX) (h1 : y ∈ chart (X.basicOpen (g m)))
      (h2 : y ∈ chart (X.basicOpen (g m'))), eval _ (σ m) ⟨y, h1⟩ = eval _ (σ m') ⟨y, h2⟩) :
    ∃ τ : Γ(X, U), ∀ (m : Fin s) (y : ComplexPoints sX) (h : y ∈ chart (X.basicOpen (g m))),
      eval U τ ⟨y, chart_mono (X.basicOpen_le (g m)) h⟩ = eval _ (σ m) ⟨y, h⟩ := by
  have hcover : U ≤ ⨆ m, X.basicOpen (g m) := by
    have := (hU.self_le_iSup_basicOpen_iff (s := Set.range g)).2 hg
    refine this.trans (iSup_le fun ⟨_, ⟨m, hm⟩⟩ => ?_)
    subst hm
    exact le_iSup (fun m => X.basicOpen (g m)) m
  have hc : TopCat.Presheaf.IsCompatible X.sheaf.1 (fun m => X.basicOpen (g m)) σ := by
    intro m m'
    have hA : IsAffineOpen (X.basicOpen (g m) ⊓ X.basicOpen (g m')) := by
      rw [← Scheme.basicOpen_mul]
      exact hU.basicOpen _
    have inj : ∀ a b : Γ(X, X.basicOpen (g m) ⊓ X.basicOpen (g m')),
        (∀ y : chart (sX := sX) (X.basicOpen (g m) ⊓ X.basicOpen (g m')),
          evalHom _ y a = evalHom _ y b) → a = b := by
      intro a b hab
      rw [← sub_eq_zero]
      apply eq_zero_of_forall_evalHom_eq_zero (sX := sX) hA
      intro y
      rw [map_sub, hab, sub_self]
    apply inj
    intro ⟨y, hy⟩
    have e1 := evalHom_res (inf_le_left : X.basicOpen (g m) ⊓ X.basicOpen (g m') ≤ _) ⟨y, hy⟩ (σ m)
    have e2 := evalHom_res (inf_le_right : X.basicOpen (g m) ⊓ X.basicOpen (g m') ≤ _) ⟨y, hy⟩
      (σ m')
    exact (e1.symm.trans (hcomp m m' y _ _)).trans e2
  obtain ⟨τ, hτ, -⟩ := X.sheaf.existsUnique_gluing' (fun m => X.basicOpen (g m)) U
    (fun m => homOfLE (X.basicOpen_le (g m))) hcover σ hc
  refine ⟨τ, fun m y h => ?_⟩
  rw [← hτ m]
  exact evalHom_res (X.basicOpen_le (g m)) ⟨y, h⟩ τ

/-- Gluing on the intersection of two affine opens covered by standard covers: functions on the
pairwise intersections of the members, agreeing pointwise, glue. -/
theorem exists_glue_inf_pointwise {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sX] [QuasiCompact sX] [IsReduced X] {U U' : X.Opens}
    (hUU' : IsAffineOpen (U ⊓ U')) {s s' : ℕ} (g : Fin s → Γ(X, U)) (g' : Fin s' → Γ(X, U'))
    (hg : Ideal.span (Set.range g) = ⊤) (hg' : Ideal.span (Set.range g') = ⊤)
    (σ : ∀ m m', Γ(X, X.basicOpen (g m) ⊓ X.basicOpen (g' m')))
    (hcomp : ∀ (m₁ m₂ : Fin s) (m₁' m₂' : Fin s') (y : ComplexPoints sX)
      (h₁ : y ∈ chart (X.basicOpen (g m₁) ⊓ X.basicOpen (g' m₁')))
      (h₂ : y ∈ chart (X.basicOpen (g m₂) ⊓ X.basicOpen (g' m₂'))),
      eval _ (σ m₁ m₁') ⟨y, h₁⟩ = eval _ (σ m₂ m₂') ⟨y, h₂⟩) :
    ∃ τ : Γ(X, U ⊓ U'), ∀ (m : Fin s) (m' : Fin s') (y : ComplexPoints sX)
      (h : y ∈ chart (X.basicOpen (g m) ⊓ X.basicOpen (g' m'))),
      eval (U ⊓ U') τ ⟨y, chart_mono (inf_le_inf (X.basicOpen_le (g m)) (X.basicOpen_le (g' m')))
        h⟩ = eval _ (σ m m') ⟨y, h⟩ := by
  classical
  let r : Γ(X, U) →+* Γ(X, U ⊓ U') := (X.presheaf.map (homOfLE inf_le_left).op).hom
  let r' : Γ(X, U') →+* Γ(X, U ⊓ U') := (X.presheaf.map (homOfLE inf_le_right).op).hom
  let G : Fin (s * s') → Γ(X, U ⊓ U') := fun k =>
    r (g (finProdFinEquiv.symm k).1) * r' (g' (finProdFinEquiv.symm k).2)
  have hGb : ∀ k, X.basicOpen (G k) =
      X.basicOpen (g (finProdFinEquiv.symm k).1) ⊓ X.basicOpen (g' (finProdFinEquiv.symm k).2) := by
    intro k
    simp only [G, r, r', Scheme.basicOpen_mul, RingHom.coe_mk]
    erw [Scheme.basicOpen_res, Scheme.basicOpen_res]
    have h1 := X.basicOpen_le (g (finProdFinEquiv.symm k).1)
    have h2 := X.basicOpen_le (g' (finProdFinEquiv.symm k).2)
    exact le_antisymm (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right))
      (le_inf (le_inf (le_inf (inf_le_left.trans h1) (inf_le_right.trans h2)) inf_le_left)
        (le_inf (le_inf (inf_le_left.trans h1) (inf_le_right.trans h2)) inf_le_right))
  have hG : Ideal.span (Set.range G) = ⊤ := by
    have e1 : Ideal.span (Set.range (r ∘ g)) = ⊤ := by
      rw [Set.range_comp, ← Ideal.map_span, hg, Ideal.map_top]
    have e2 : Ideal.span (Set.range (r' ∘ g')) = ⊤ := by
      rw [Set.range_comp, ← Ideal.map_span, hg', Ideal.map_top]
    have e3 : (⊤ : Ideal Γ(X, U ⊓ U')) =
        Ideal.span (Set.range (r ∘ g)) * Ideal.span (Set.range (r' ∘ g')) := by
      rw [e1, e2, Ideal.top_mul]
    rw [eq_top_iff, e3, Ideal.span_mul_span']
    apply Ideal.span_mono
    rintro _ ⟨a, ⟨m, rfl⟩, b, ⟨m', rfl⟩, rfl⟩
    refine ⟨finProdFinEquiv (m, m'), ?_⟩
    simp only [G, Equiv.symm_apply_apply, Function.comp_apply]
  let σ' : ∀ k, Γ(X, X.basicOpen (G k)) := fun k =>
    X.presheaf.map (homOfLE (hGb k).le).op (σ _ _)
  have hσ' : ∀ k (y : ComplexPoints sX) (hy : y ∈ chart (X.basicOpen (G k))),
      eval _ (σ' k) ⟨y, hy⟩ = eval _ (σ _ _) ⟨y, chart_mono (hGb k).le hy⟩ :=
    fun k y hy => (evalHom_res (hGb k).le ⟨y, hy⟩ _).symm
  obtain ⟨τ, hτ⟩ := exists_glue_pointwise (sX := sX) hUU' G hG σ' (fun k k' y h1 h2 => by
    rw [hσ', hσ']
    exact hcomp _ _ _ _ y _ _)
  refine ⟨τ, fun m m' y h => ?_⟩
  have hk : y ∈ chart (X.basicOpen (G (finProdFinEquiv (m, m')))) := by
    rw [hGb]
    simpa only [Equiv.symm_apply_apply] using h
  have := hτ _ y hk
  rw [hσ'] at this
  exact this.trans (hcomp _ _ _ _ y _ _)

/-- Gluing on a pair of boxes: a pointwise cocycle `κ` on the standard covers of the boxes
`A c × V`, minus the coboundary of pointwise primitives `h` on each box, glues to a function on
the box over `A c ⊓ A d`. -/
theorem exists_glue_box_inf [IsReduced (pullback f sJ)] [LocallyOfFiniteType (prodHom f sJ)]
    [QuasiCompact (prodHom f sJ)] {V : J.Opens} (hV : IsAffineOpen V) {r : ℕ}
    {A : Fin r → C.Opens} (hA2 : ∀ c d, IsAffineOpen (A c ⊓ A d)) {s : Fin r → ℕ}
    {F : ∀ c, Fin (s c) → Γ(pullback f sJ, box (f := f) (sJ := sJ) (A c) V)}
    (hF : ∀ c, Ideal.span (Set.range (F c)) = ⊤)
    (κ : ∀ j k : Σ c, Fin (s c), Γ(pullback f sJ, Nopen F j ⊓ Nopen F k))
    (hcoc : ∀ (j k l : Σ c, Fin (s c)) (q : ComplexPoints (prodHom f sJ))
      (h1 : q ∈ chart (sX := prodHom f sJ) (Nopen F j))
      (h2 : q ∈ chart (sX := prodHom f sJ) (Nopen F k))
      (h3 : q ∈ chart (sX := prodHom f sJ) (Nopen F l)),
      eval _ (κ j k) ⟨q, mem_chart_iff.2 ⟨mem_chart_iff.1 h1, mem_chart_iff.1 h2⟩⟩ +
        eval _ (κ k l) ⟨q, mem_chart_iff.2 ⟨mem_chart_iff.1 h2, mem_chart_iff.1 h3⟩⟩ =
      eval _ (κ j l) ⟨q, mem_chart_iff.2 ⟨mem_chart_iff.1 h1, mem_chart_iff.1 h3⟩⟩)
    (h : ∀ j : Σ c, Fin (s c), Γ(pullback f sJ, Nopen F j))
    (hh : ∀ (c : Fin r) (m m' : Fin (s c)) (y : ComplexPoints (prodHom f sJ))
      (h1 : y ∈ chart (sX := prodHom f sJ) (Nopen F ⟨c, m⟩))
      (h2 : y ∈ chart (sX := prodHom f sJ) (Nopen F ⟨c, m'⟩)),
      eval _ (κ ⟨c, m⟩ ⟨c, m'⟩) ⟨y, mem_chart_iff.2 ⟨mem_chart_iff.1 h1, mem_chart_iff.1 h2⟩⟩ =
        eval _ (h ⟨c, m'⟩) ⟨y, h2⟩ - eval _ (h ⟨c, m⟩) ⟨y, h1⟩)
    (c d : Fin r) :
    ∃ τ : Γ(pullback f sJ, box (f := f) (sJ := sJ) (A c ⊓ A d) V),
      ∀ (m : Fin (s c)) (m' : Fin (s d)) (y : ComplexPoints (prodHom f sJ))
        (hy : y ∈ chart (sX := prodHom f sJ) (Nopen F ⟨c, m⟩ ⊓ Nopen F ⟨d, m'⟩))
        (hy' : y ∈ chart (sX := prodHom f sJ) (box (f := f) (sJ := sJ) (A c ⊓ A d) V)),
        eval _ τ ⟨y, hy'⟩ = eval _ (κ ⟨c, m⟩ ⟨d, m'⟩) ⟨y, hy⟩ -
          eval _ (h ⟨d, m'⟩) ⟨y, chart_mono inf_le_right hy⟩ +
          eval _ (h ⟨c, m⟩) ⟨y, chart_mono inf_le_left hy⟩ := by
  let σ : ∀ m m', Γ(pullback f sJ,
      (pullback f sJ).basicOpen (F c m) ⊓ (pullback f sJ).basicOpen (F d m')) :=
    fun m m' => κ ⟨c, m⟩ ⟨d, m'⟩ -
      (pullback f sJ).presheaf.map (homOfLE inf_le_right).op (h ⟨d, m'⟩) +
      (pullback f sJ).presheaf.map (homOfLE inf_le_left).op (h ⟨c, m⟩)
  have hσ : ∀ m m' (y : ComplexPoints (prodHom f sJ))
      (hy : y ∈ chart (sX := prodHom f sJ)
        ((pullback f sJ).basicOpen (F c m) ⊓ (pullback f sJ).basicOpen (F d m'))),
      eval _ (σ m m') ⟨y, hy⟩ = eval _ (κ ⟨c, m⟩ ⟨d, m'⟩) ⟨y, hy⟩ -
        eval _ (h ⟨d, m'⟩) ⟨y, chart_mono inf_le_right hy⟩ +
        eval _ (h ⟨c, m⟩) ⟨y, chart_mono inf_le_left hy⟩ := by
    intro m m' y hy
    rw [← evalHom_apply, map_add, map_sub, ← evalHom_res, ← evalHom_res]
    rfl
  have hAff : IsAffineOpen
      (box (f := f) (sJ := sJ) (A c) V ⊓ box (f := f) (sJ := sJ) (A d) V) := by
    rw [← box_inf]
    exact isAffineOpen_box (hA2 c d) hV
  obtain ⟨τ, hτ⟩ := exists_glue_inf_pointwise (sX := prodHom f sJ) hAff (F c) (F d) (hF c)
    (hF d) σ (by
      intro m₁ m₂ m₁' m₂' y h₁ h₂
      rw [hσ, hσ]
      have a1 := hcoc ⟨c, m₁⟩ ⟨c, m₂⟩ ⟨d, m₂'⟩ y (chart_mono inf_le_left h₁)
        (chart_mono inf_le_left h₂) (chart_mono inf_le_right h₂)
      have a2 := hcoc ⟨c, m₁⟩ ⟨d, m₂'⟩ ⟨d, m₁'⟩ y (chart_mono inf_le_left h₁)
        (chart_mono inf_le_right h₂) (chart_mono inf_le_right h₁)
      have b1 := hh c m₁ m₂ y (chart_mono inf_le_left h₁) (chart_mono inf_le_left h₂)
      have b2 := hh d m₂' m₁' y (chart_mono inf_le_right h₂) (chart_mono inf_le_right h₁)
      linear_combination b1 + b2 - a1 - a2)
  refine ⟨(pullback f sJ).presheaf.map (homOfLE (box_inf _ _ _).le).op τ,
    fun m m' y hy hy' => ?_⟩
  rw [← evalHom_apply, ← evalHom_res, evalHom_apply, hτ m m' y hy, hσ]

/-- **Čech decomposition on boxes.** A pointwise cocycle `κ` on the standard covers of the boxes
`A c × V` is, at every point, a separable part `∑ P(x) R(t)` on each pair of boxes plus a Čech
coboundary. -/
theorem exists_sum_add_coboundary [IsReduced (pullback f sJ)] [LocallyOfFiniteType (prodHom f sJ)]
    [QuasiCompact (prodHom f sJ)] {V : J.Opens} (hV : IsAffineOpen V) {r : ℕ}
    {A : Fin r → C.Opens} (hA : ∀ c, IsAffineOpen (A c))
    (hA2 : ∀ c d, IsAffineOpen (A c ⊓ A d)) {s : Fin r → ℕ}
    {F : ∀ c, Fin (s c) → Γ(pullback f sJ, box (f := f) (sJ := sJ) (A c) V)}
    (hF : ∀ c, Ideal.span (Set.range (F c)) = ⊤)
    (κ : ∀ j k : Σ c, Fin (s c), Γ(pullback f sJ, Nopen F j ⊓ Nopen F k))
    (hcoc : ∀ (j k l : Σ c, Fin (s c)) (q : ComplexPoints (prodHom f sJ))
      (h1 : q ∈ chart (sX := prodHom f sJ) (Nopen F j))
      (h2 : q ∈ chart (sX := prodHom f sJ) (Nopen F k))
      (h3 : q ∈ chart (sX := prodHom f sJ) (Nopen F l)),
      eval _ (κ j k) ⟨q, mem_chart_iff.2 ⟨mem_chart_iff.1 h1, mem_chart_iff.1 h2⟩⟩ +
        eval _ (κ k l) ⟨q, mem_chart_iff.2 ⟨mem_chart_iff.1 h2, mem_chart_iff.1 h3⟩⟩ =
      eval _ (κ j l) ⟨q, mem_chart_iff.2 ⟨mem_chart_iff.1 h1, mem_chart_iff.1 h3⟩⟩) :
    ∃ (h : ∀ j : Σ c, Fin (s c), Γ(pullback f sJ, Nopen F j))
      (L : Fin r → Fin r → ℕ) (P : ∀ c d, Fin (L c d) → Γ(C, A c ⊓ A d))
      (R : ∀ c d, Fin (L c d) → Γ(J, V)),
      ∀ (j k : Σ c, Fin (s c)) (x : ComplexPoints f) (t : ComplexPoints sJ)
        (hqj : pair x t ∈ chart (sX := prodHom f sJ) (Nopen F j))
        (hqk : pair x t ∈ chart (sX := prodHom f sJ) (Nopen F k))
        (hx : x ∈ chart (A j.1 ⊓ A k.1)) (ht : t ∈ chart V),
        eval _ (κ j k) ⟨pair x t, mem_chart_iff.2 ⟨mem_chart_iff.1 hqj, mem_chart_iff.1 hqk⟩⟩ =
          (∑ l, eval _ (P j.1 k.1 l) ⟨x, hx⟩ * eval _ (R j.1 k.1 l) ⟨t, ht⟩) +
            eval _ (h k) ⟨pair x t, hqk⟩ - eval _ (h j) ⟨pair x t, hqj⟩ := by
  -- Leray on each box
  choose hc hhc using fun c : Fin r =>
    exists_coboundary_pointwise (X := pullback f sJ) (sX := prodHom f sJ)
      (U := box (f := f) (sJ := sJ) (A c) V) (isAffineOpen_box (hA c) hV) (F c) (hF c)
      (fun m m' => κ ⟨c, m⟩ ⟨c, m'⟩) fun m m' m'' y => hcoc ⟨c, m⟩ ⟨c, m'⟩ ⟨c, m''⟩ y
  -- gluing on each pair of boxes
  choose τ hτ using exists_glue_box_inf hV hA2 hF κ hcoc (fun j => hc j.1 j.2) hhc
  choose L P R hPR using fun c d => exists_sum_box (hA2 c d) hV (τ c d)
  refine ⟨fun j => hc j.1 j.2, L, P, R, ?_⟩
  rintro ⟨c, m⟩ ⟨d, m'⟩ x t hqj hqk hx ht
  have hy : pair x t ∈ chart (sX := prodHom f sJ) (Nopen F ⟨c, m⟩ ⊓ Nopen F ⟨d, m'⟩) :=
    mem_chart_iff.2 ⟨mem_chart_iff.1 hqj, mem_chart_iff.1 hqk⟩
  have e := hτ c d m m' (pair x t) hy (mem_chart_box hx ht)
  rw [hPR, ← evalHom_apply, map_sum] at e
  simp only [map_mul, evalHom_apply] at e
  have hs : ∑ l, eval (box (f := f) (sJ := sJ) (A c ⊓ A d) V)
        ((pullback.fst f sJ).appLE (A c ⊓ A d) (box (f := f) (sJ := sJ) (A c ⊓ A d) V)
          inf_le_left (P c d l)) ⟨pair x t, mem_chart_box hx ht⟩ *
      eval (box (f := f) (sJ := sJ) (A c ⊓ A d) V)
        ((pullback.snd f sJ).appLE V (box (f := f) (sJ := sJ) (A c ⊓ A d) V)
          inf_le_right (R c d l)) ⟨pair x t, mem_chart_box hx ht⟩ =
      ∑ l, eval _ (P c d l) ⟨x, hx⟩ * eval _ (R c d l) ⟨t, ht⟩ :=
    Finset.sum_congr rfl fun l _ =>
      congrArg₂ (· * ·) (eval_fst_pair _ hx ht) (eval_snd_pair _ hx ht)
  linear_combination hs - e

/-- **Decomposition of the logarithmic derivatives of the transition units.** The logarithmic
derivatives `κ` of the transition units of local generators on standard covers of the boxes
`A c × V` split, at every point, into a function of `x` times a function of `t` on each pair of
boxes, plus a Čech coboundary. -/
theorem exists_logDeriv_decomposition {n : ℕ} [SmoothOfRelativeDimension n sJ]
    [IsReduced (pullback f sJ)] [LocallyOfFiniteType (prodHom f sJ)]
    [QuasiCompact (prodHom f sJ)]
    {V : J.Opens} (hV : IsAffineOpen V) (z : Fin n → Γ(J, V))
    (hz : Etale (AffineSpace.homOfVector (V.ι ≫ sJ)
      (fun i : ULift.{0} (Fin n) ↦ V.topIso.inv (z i.down))))
    {r : ℕ} (A : Fin r → C.Opens) (hA : ∀ c, IsAffineOpen (A c))
    (hA2 : ∀ c d, IsAffineOpen (A c ⊓ A d)) {s : Fin r → ℕ}
    (F : ∀ c, Fin (s c) → Γ(pullback f sJ, box (f := f) (sJ := sJ) (A c) V))
    (hF : ∀ c, Ideal.span (Set.range (F c)) = ⊤)
    (M : SheafOfModules.{0} (structureSheaf (pullback f sJ).toRingedSpace.sheaf))
    (ε : ∀ j : Σ c, Fin (s c), Stacks.SheafOfModules.GeneratorSections
      (pullback f sJ).toRingedSpace M (Nopen F j)) :
    ∃ (κ : Fin n → ∀ j k : Σ c, Fin (s c), Γ(pullback f sJ, Nopen F j ⊓ Nopen F k))
      (h : Fin n → ∀ j : Σ c, Fin (s c), Γ(pullback f sJ, Nopen F j))
      (L : Fin n → Fin r → Fin r → ℕ) (P : ∀ i c d, Fin (L i c d) → Γ(C, A c ⊓ A d))
      (R : ∀ i c d, Fin (L i c d) → Γ(J, V)),
      (∀ (j k : Σ c, Fin (s c)) (x : ComplexPoints f) (t : ComplexPoints sJ)
        (hq : pair x t ∈ chart (sX := prodHom f sJ) (Nopen F j ⊓ Nopen F k))
        (W : Set (ComplexPoints sJ)) (hWsub : W ⊆ chart V) (hWo : IsOpen W) (hne : W.Nonempty)
        (hemb : Topology.IsOpenEmbedding (fun y : W ↦ fun i ↦ eval V (z i) ⟨y.1, hWsub y.2⟩))
        (_ : t ∈ W),
        ∃ (Fu : (Fin n → ℂ) → ℂ) (Fu' : (Fin n → ℂ) →L[ℂ] ℂ),
          HasFDerivAt Fu Fu'
            ((EtaleCoordinateChart.mk V z hz W hWsub hWo hne hemb).toOpenPartialHomeomorph t) ∧
          (∀ᶠ w in 𝓝 ((EtaleCoordinateChart.mk V z hz W hWsub hWo hne hemb).toOpenPartialHomeomorph
              t), ∃ hw : pair x ((EtaleCoordinateChart.mk V z hz W hWsub hWo hne
                hemb).toOpenPartialHomeomorph.symm w) ∈
                chart (sX := prodHom f sJ) (Nopen F j ⊓ Nopen F k),
              Fu w = eval _ (transUnit F M ε j k : Γ(pullback f sJ, Nopen F j ⊓ Nopen F k))
                ⟨_, hw⟩) ∧
          ∀ i, Fu' (Pi.single i 1) = eval _ (κ i j k) ⟨pair x t, hq⟩ *
            eval _ (transUnit F M ε j k : Γ(pullback f sJ, Nopen F j ⊓ Nopen F k))
              ⟨pair x t, hq⟩) ∧
      (∀ (i : Fin n) (j k l : Σ c, Fin (s c)) (q : ComplexPoints (prodHom f sJ))
        (h1 : q ∈ chart (sX := prodHom f sJ) (Nopen F j))
        (h2 : q ∈ chart (sX := prodHom f sJ) (Nopen F k))
        (h3 : q ∈ chart (sX := prodHom f sJ) (Nopen F l)),
        eval _ (κ i j k) ⟨q, mem_chart_iff.2 ⟨mem_chart_iff.1 h1, mem_chart_iff.1 h2⟩⟩ +
          eval _ (κ i k l) ⟨q, mem_chart_iff.2 ⟨mem_chart_iff.1 h2, mem_chart_iff.1 h3⟩⟩ =
        eval _ (κ i j l) ⟨q, mem_chart_iff.2 ⟨mem_chart_iff.1 h1, mem_chart_iff.1 h3⟩⟩) ∧
      ∀ (i : Fin n) (j k : Σ c, Fin (s c)) (x : ComplexPoints f) (t : ComplexPoints sJ)
        (hqj : pair x t ∈ chart (sX := prodHom f sJ) (Nopen F j))
        (hqk : pair x t ∈ chart (sX := prodHom f sJ) (Nopen F k))
        (hx : x ∈ chart (A j.1 ⊓ A k.1)) (ht : t ∈ chart V),
        eval _ (κ i j k) ⟨pair x t, mem_chart_iff.2 ⟨mem_chart_iff.1 hqj, mem_chart_iff.1 hqk⟩⟩ =
          (∑ l, eval _ (P i j.1 k.1 l) ⟨x, hx⟩ * eval _ (R i j.1 k.1 l) ⟨t, ht⟩) +
            eval _ (h i k) ⟨pair x t, hqk⟩ - eval _ (h i j) ⟨pair x t, hqj⟩ := by
  classical
  -- logarithmic derivatives of the transition units
  choose κ0 hκ0 using fun j k : Σ c, Fin (s c) =>
    exists_logDeriv_of_eq_basicOpen (hA2 j.1 k.1) hV z hz _ (Nopen F j ⊓ Nopen F k)
      (basicOpen_inf_eq (F j.1 j.2) (F k.1 k.2)) (transUnit F M ε j k)
  let κ : Fin n → ∀ j k : Σ c, Fin (s c), Γ(pullback f sJ, Nopen F j ⊓ Nopen F k) :=
    fun i j k => κ0 j k i
  -- the pointwise cocycle identity of the logarithmic derivatives
  have hcoc : ∀ (i : Fin n) (j k l : Σ c, Fin (s c)) (x : ComplexPoints f) (t : ComplexPoints sJ)
      (h1 : pair x t ∈ chart (sX := prodHom f sJ) (Nopen F j))
      (h2 : pair x t ∈ chart (sX := prodHom f sJ) (Nopen F k))
      (h3 : pair x t ∈ chart (sX := prodHom f sJ) (Nopen F l)),
      eval _ (κ i j k) ⟨pair x t, mem_chart_iff.2 ⟨mem_chart_iff.1 h1, mem_chart_iff.1 h2⟩⟩ +
        eval _ (κ i k l) ⟨pair x t, mem_chart_iff.2 ⟨mem_chart_iff.1 h2, mem_chart_iff.1 h3⟩⟩ =
      eval _ (κ i j l) ⟨pair x t, mem_chart_iff.2 ⟨mem_chart_iff.1 h1, mem_chart_iff.1 h3⟩⟩ := by
    intro i j k l x t h1 h2 h3
    have htV : t ∈ chart V :=
      (mem_chart_of_pair_mem_box (chart_mono ((pullback f sJ).basicOpen_le _) h1)).2
    obtain ⟨W, hW, hWo, htW, hemb⟩ := (etaleCoordinate_atlas_of_smooth sJ).2.1 V z hz t htV
    have hne : W.Nonempty := ⟨t, htW⟩
    obtain ⟨F₁, F₁', hF₁, hF₁e, hF₁v⟩ := hκ0 j k x t _ W hW hWo hne hemb htW
    obtain ⟨F₂, F₂', hF₂, hF₂e, hF₂v⟩ := hκ0 k l x t _ W hW hWo hne hemb htW
    obtain ⟨F₃, F₃', hF₃, hF₃e, hF₃v⟩ := hκ0 j l x t _ W hW hWo hne hemb htW
    set φ := (EtaleCoordinateChart.mk V z hz W hW hWo hne hemb).toOpenPartialHomeomorph
    have hφt : φ.symm (φ t) = t := φ.left_inv (by
      rwa [EtaleCoordinateChart.source_toOpenPartialHomeomorph])
    have hpt : ∀ {a b : Σ c, Fin (s c)} (Fu : (Fin n → ℂ) → ℂ)
        (hFe : ∀ᶠ w in 𝓝 (φ t), ∃ hw : pair x (φ.symm w) ∈
          chart (sX := prodHom f sJ) (Nopen F a ⊓ Nopen F b),
          Fu w = eval _ (transUnit F M ε a b : Γ(pullback f sJ, Nopen F a ⊓ Nopen F b)) ⟨_, hw⟩)
        (hq : pair x t ∈ chart (sX := prodHom f sJ) (Nopen F a ⊓ Nopen F b)),
        Fu (φ t) = eval _ (transUnit F M ε a b : Γ(pullback f sJ, Nopen F a ⊓ Nopen F b))
          ⟨pair x t, hq⟩ := by
      intro a b Fu hFe hq
      obtain ⟨hw, e⟩ := hFe.self_of_nhds
      exact e.trans (congrArg _ (Subtype.ext (congrArg (pair x) hφt)))
    refine logDeriv_add hF₁ hF₂ hF₃ ?_ ((hF₁v i).trans (by rw [hpt F₁ hF₁e]))
      ((hF₂v i).trans (by rw [hpt F₂ hF₂e])) ((hF₃v i).trans (by rw [hpt F₃ hF₃e])) ?_
    · filter_upwards [hF₁e, hF₂e, hF₃e] with w ⟨hw₁, e₁⟩ ⟨hw₂, e₂⟩ ⟨hw₃, e₃⟩
      rw [e₁, e₂, e₃]
      exact transUnit_mul_apply F M ε j k l _ (chart_mono inf_le_left hw₁)
        (chart_mono inf_le_right hw₁) (chart_mono inf_le_right hw₂)
    · rw [hpt F₃ hF₃e (mem_chart_iff.2 ⟨mem_chart_iff.1 h1, mem_chart_iff.1 h3⟩)]
      exact ((transUnit F M ε j l).isUnit.map (evalHom _ _)).ne_zero
  -- the cocycle identity at arbitrary points
  have hcocq : ∀ (i : Fin n) (j k l : Σ c, Fin (s c)) (q : ComplexPoints (prodHom f sJ))
      (h1 : q ∈ chart (sX := prodHom f sJ) (Nopen F j))
      (h2 : q ∈ chart (sX := prodHom f sJ) (Nopen F k))
      (h3 : q ∈ chart (sX := prodHom f sJ) (Nopen F l)),
      eval _ (κ i j k) ⟨q, mem_chart_iff.2 ⟨mem_chart_iff.1 h1, mem_chart_iff.1 h2⟩⟩ +
        eval _ (κ i k l) ⟨q, mem_chart_iff.2 ⟨mem_chart_iff.1 h2, mem_chart_iff.1 h3⟩⟩ =
      eval _ (κ i j l) ⟨q, mem_chart_iff.2 ⟨mem_chart_iff.1 h1, mem_chart_iff.1 h3⟩⟩ := by
    intro i j k l q
    rw [← pair_realize q]
    exact hcoc i j k l _ _
  choose h L P R hPR using fun i => exists_sum_add_coboundary hV hA hA2 hF (κ i) (hcocq i)
  exact ⟨κ, h, L, P, R, fun j k => hκ0 j k, hcocq, hPR⟩

end Kappa

section AnaSec

open MeasureTheory Set Metric Filter Topology intervalIntegral

namespace Ana

/-- A parametric interval integral of a function continuous on `U × [0, 1]` is continuous
on `U`. -/
theorem continuousOn_intervalIntegral {X : Type*} [TopologicalSpace X] {U : Set X}
    {F : X → ℝ → ℂ} (hc : ContinuousOn (Function.uncurry F) (U ×ˢ Icc 0 1)) :
    ContinuousOn (fun x => ∫ s in (0 : ℝ)..1, F x s) U := by
  rw [continuousOn_iff_continuous_restrict]
  let F' : U → ℝ → ℂ := fun x s => F x (projIcc 0 1 zero_le_one s)
  have hF' : Continuous (Function.uncurry F') := by
    have h2 : Continuous fun p : U × ℝ => ((p.1 : X), ((projIcc 0 1 zero_le_one p.2 : ℝ))) :=
      by fun_prop
    exact hc.comp_continuous h2 fun p => ⟨p.1.2, (projIcc 0 1 zero_le_one p.2).2⟩
  refine (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume)
    hF' 0 1).congr fun x => ?_
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le zero_le_one] at ht
  simp only [F', projIcc_of_mem _ ht]

/-- The integrand of Cauchy's formula for a parametric family is continuous on
`[0, 1] × [0, 2π]`. -/
theorem continuousOn_circleIntegrand {U : Set ℂ} {F : ℂ → ℝ → ℂ}
    (hc : ContinuousOn (Function.uncurry F) (U ×ˢ Icc 0 1)) {z0 w : ℂ} {R : ℝ} (hR : 0 < R)
    (hRU : closedBall z0 R ⊆ U) (hw : w ∈ ball z0 R) :
    ContinuousOn (fun p : ℝ × ℝ => (deriv (circleMap z0 R) p.2 * (circleMap z0 R p.2 - w)⁻¹) *
      F (circleMap z0 R p.2) p.1) (Icc 0 1 ×ˢ Icc 0 (2 * Real.pi)) := by
  have hne : ∀ θ, circleMap z0 R θ - w ≠ 0 := fun θ h => by
    have h2 := circleMap_mem_sphere z0 hR.le θ
    rw [sub_eq_zero.1 h, mem_sphere] at h2
    rw [mem_ball] at hw
    linarith
  refine ContinuousOn.mul (Continuous.continuousOn (Continuous.mul ?_
    (Continuous.inv₀ (by fun_prop) fun p => hne p.2))) ?_
  · simp only [deriv_circleMap]
    fun_prop
  · refine hc.comp (Continuous.continuousOn
      (by fun_prop : Continuous fun p : ℝ × ℝ => (circleMap z0 R p.2, p.1))) fun p hp => ?_
    exact ⟨hRU (sphere_subset_closedBall (circleMap_mem_sphere z0 hR.le p.2)), hp.1⟩

/-- **Cauchy's integral formula for a parametric interval integral.** -/
theorem intervalIntegral_eq_circleIntegral {U : Set ℂ} {F : ℂ → ℝ → ℂ}
    (hc : ContinuousOn (Function.uncurry F) (U ×ˢ Icc 0 1))
    (hd : ∀ s ∈ Icc (0 : ℝ) 1, DifferentiableOn ℂ (fun z => F z s) U) {z0 w : ℂ} {R : ℝ}
    (hR : 0 < R) (hRU : closedBall z0 R ⊆ U) (hw : w ∈ ball z0 R) :
    ∫ s in (0 : ℝ)..1, F w s = (2 * Real.pi * Complex.I)⁻¹ •
      ∮ z in C(z0, R), (z - w)⁻¹ • ∫ s in (0 : ℝ)..1, F z s := by
  have h1 : ∫ s in (0 : ℝ)..1, F w s = ∫ s in (0 : ℝ)..1,
      (2 * Real.pi * Complex.I)⁻¹ • ∮ z in C(z0, R), (z - w)⁻¹ • F z s := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le zero_le_one] at hs
    exact ((((hd s hs).mono hRU).diffContOnCl_ball subset_rfl)
      |>.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hw).symm
  rw [h1, intervalIntegral.integral_smul]
  congr 1
  simp only [circleIntegral, smul_eq_mul]
  have hint : Integrable (Function.uncurry fun (s : ℝ) (θ : ℝ) =>
      deriv (circleMap z0 R) θ * ((circleMap z0 R θ - w)⁻¹ * F (circleMap z0 R θ) s))
      ((volume.restrict (uIoc 0 1)).prod (volume.restrict (Ioc 0 (2 * Real.pi)))) := by
    rw [Measure.prod_restrict, uIoc_of_le zero_le_one, ← Measure.volume_eq_prod]
    have hco : IntegrableOn (fun p : ℝ × ℝ => (deriv (circleMap z0 R) p.2 *
        (circleMap z0 R p.2 - w)⁻¹) * F (circleMap z0 R p.2) p.1)
        (Icc 0 1 ×ˢ Icc 0 (2 * Real.pi)) volume :=
      (continuousOn_circleIntegrand hc hR hRU hw).integrableOn_compact
        (isCompact_Icc.prod isCompact_Icc)
    exact (hco.mono_set (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)).congr_fun
      (fun p _ => by simp only [Function.uncurry_def]; ring)
      (measurableSet_Ioc.prod measurableSet_Ioc)
  have e1 : ∀ s : ℝ, (∫ θ in (0 : ℝ)..2 * Real.pi,
      deriv (circleMap z0 R) θ * ((circleMap z0 R θ - w)⁻¹ * F (circleMap z0 R θ) s)) =
      ∫ θ, deriv (circleMap z0 R) θ * ((circleMap z0 R θ - w)⁻¹ * F (circleMap z0 R θ) s)
        ∂(volume.restrict (Ioc 0 (2 * Real.pi))) := fun s =>
    intervalIntegral.integral_of_le (by positivity)
  simp_rw [e1]
  rw [MeasureTheory.intervalIntegral_integral_swap hint,
    ← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]

/-- **A parametric integral of holomorphic functions is holomorphic.** If `F` is continuous on
`U × [0, 1]` and holomorphic in its first variable on the open set `U`, then
`z ↦ ∫₀¹ F z s ds` is holomorphic on `U`. -/
theorem differentiableOn_intervalIntegral {U : Set ℂ} (hU : IsOpen U) {F : ℂ → ℝ → ℂ}
    (hc : ContinuousOn (Function.uncurry F) (U ×ˢ Icc 0 1))
    (hd : ∀ s ∈ Icc (0 : ℝ) 1, DifferentiableOn ℂ (fun z => F z s) U) :
    DifferentiableOn ℂ (fun z => ∫ s in (0 : ℝ)..1, F z s) U := by
  intro z0 hz0
  obtain ⟨R₀, hR₀, hR₀U⟩ := Metric.isOpen_iff.1 hU z0 hz0
  set R : ℝ := R₀ / 2 with hRdef
  have hR : 0 < R := by positivity
  have hRU : closedBall z0 R ⊆ U := (closedBall_subset_ball (by linarith)).trans hR₀U
  set g := fun z => ∫ s in (0 : ℝ)..1, F z s with hg
  have hci : CircleIntegrable g z0 (⟨R, hR.le⟩ : NNReal) :=
    ContinuousOn.circleIntegrable hR.le
      ((continuousOn_intervalIntegral hc).mono (sphere_subset_closedBall.trans hRU))
  have hps := hasFPowerSeriesOn_cauchy_integral hci (show (0 : NNReal) < ⟨R, hR.le⟩ from hR)
  have heq : (fun w => (2 * Real.pi * Complex.I)⁻¹ • ∮ z in C(z0, (⟨R, hR.le⟩ : NNReal)),
      (z - w)⁻¹ • g z) =ᶠ[𝓝 z0] g := by
    filter_upwards [ball_mem_nhds z0 hR] with w hw
    exact (intervalIntegral_eq_circleIntegral hc hd hR hRU hw).symm
  exact (hps.analyticAt.differentiableAt.congr_of_eventuallyEq heq.symm).differentiableWithinAt

open scoped Manifold ContDiff in
/-- **A parametric integral of holomorphic functions on a Riemann surface is holomorphic.** -/
theorem contMDiffOn_intervalIntegral {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin 1)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin 1)) ∞ M] {U : Set M} (hU : IsOpen U)
    {G : M → ℝ → ℂ}
    (hc : ContinuousOn (Function.uncurry G) (U ×ˢ Icc 0 1))
    (hd : ∀ s ∈ Icc (0 : ℝ) 1,
      ContMDiffOn 𝓘(ℂ, EuclideanSpace ℂ (Fin 1)) 𝓘(ℂ, ℂ) ∞ (fun x => G x s) U) :
    ContMDiffOn 𝓘(ℂ, EuclideanSpace ℂ (Fin 1)) 𝓘(ℂ, ℂ) ∞
      (fun x => ∫ s in (0 : ℝ)..1, G x s) U := by
  rw [contMDiffOn_iff]
  refine ⟨continuousOn_intervalIntegral hc, fun x y => ?_⟩
  simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, PartialEquiv.refl_source,
    preimage_univ, inter_univ, Function.id_comp]
  set e := extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin 1)) x
  set S := e.target ∩ e.symm ⁻¹' U
  have hSo : IsOpen S :=
    (continuousOn_extChartAt_symm x).isOpen_inter_preimage (isOpen_extChartAt_target x) hU
  have hdS : ∀ s ∈ Icc (0 : ℝ) 1, DifferentiableOn ℂ (fun ξ => G (e.symm ξ) s) S := by
    intro s hs
    have h := ((contMDiffOn_iff.1 (hd s hs)).2 x y)
    simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, PartialEquiv.refl_source,
      preimage_univ, inter_univ, Function.id_comp] at h
    exact h.differentiableOn (by simp)
  let L : ℂ ≃L[ℂ] EuclideanSpace ℂ (Fin 1) :=
    (ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ).symm.trans
      (EuclideanSpace.equiv (Fin 1) ℂ).symm
  let F : ℂ → ℝ → ℂ := fun z s => G (e.symm (L z)) s
  have hU' : IsOpen (L ⁻¹' S) := hSo.preimage L.continuous
  have hcF : ContinuousOn (Function.uncurry F) ((L ⁻¹' S) ×ˢ Icc 0 1) := by
    have h1 : ContinuousOn (fun p : ℂ × ℝ => (e.symm (L p.1), p.2)) ((L ⁻¹' S) ×ˢ Icc 0 1) :=
      ((continuousOn_extChartAt_symm x).comp (L.continuous.comp continuous_fst).continuousOn
        fun p hp => hp.1.1).prodMk continuous_snd.continuousOn
    exact hc.comp h1 fun p hp => ⟨hp.1.2, hp.2⟩
  have hdF : ∀ s ∈ Icc (0 : ℝ) 1, DifferentiableOn ℂ (fun z => F z s) (L ⁻¹' S) := fun s hs =>
    (hdS s hs).comp L.differentiableOn (fun z hz => hz)
  have hint := (differentiableOn_intervalIntegral hU' hcF hdF).contDiffOn hU' (n := ∞)
  have h2 := hint.comp_continuousLinearMap (L.symm : EuclideanSpace ℂ (Fin 1) →L[ℂ] ℂ)
  have hpre : (L.symm : EuclideanSpace ℂ (Fin 1) →L[ℂ] ℂ) ⁻¹' (L ⁻¹' S) = S := by
    ext ξ
    simp
  rw [hpre] at h2
  refine h2.congr fun ξ _ => ?_
  simp [F]

/-- **Integrating a logarithmic derivative along a segment.** If `U` is differentiable on a
convex open set `B` with `∂ᵢ U = κᵢ U`, then
`U w = U p · exp ∫₀¹ ∑ᵢ (w - p)ᵢ κᵢ (p + s (w - p))`. -/
theorem eq_mul_exp_of_hasFDerivAt {n : ℕ} {B : Set (Fin n → ℂ)} (hBc : Convex ℝ B)
    (hBo : IsOpen B) {p w : Fin n → ℂ} (hp : p ∈ B) (hw : w ∈ B) {U : (Fin n → ℂ) → ℂ}
    {κ : Fin n → (Fin n → ℂ) → ℂ} (hκ : ∀ i, ContinuousOn (κ i) B)
    (hU : ∀ v ∈ B, ∃ U' : (Fin n → ℂ) →L[ℂ] ℂ, HasFDerivAt U U' v ∧
      ∀ i, U' (Pi.single i 1) = κ i v * U v) :
    U w = U p * Complex.exp (∫ s in (0 : ℝ)..1, ∑ i, (w - p) i * κ i (p + s • (w - p))) := by
  let γ : ℝ → (Fin n → ℂ) := fun s => p + s • (w - p)
  have hγB : ∀ s ∈ Icc (0 : ℝ) 1, γ s ∈ B := fun s hs => by
    simpa [γ] using hBc.add_smul_sub_mem hp hw hs
  let k : ℝ → ℂ := fun s => ∑ i, (w - p) i * κ i (γ (projIcc 0 1 zero_le_one s))
  have hk : Continuous k := by
    refine continuous_finset_sum _ fun i _ => continuous_const.mul ?_
    exact (hκ i).comp_continuous (by fun_prop) fun s => hγB _ (projIcc 0 1 zero_le_one s).2
  let G : ℝ → ℂ := fun s => U (γ s)
  have hG : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt G (G s * k s) s := by
    intro s hs
    obtain ⟨U', hU', hU'i⟩ := hU (γ s) (hγB s hs)
    have hγd : HasDerivAt γ (w - p) s := by
      simpa [γ] using ((hasDerivAt_id s).smul_const (w - p)).const_add p
    have h := (hU'.restrictScalars ℝ).comp_hasDerivAt s hγd
    have hval : (U'.restrictScalars ℝ) (w - p) = G s * k s := by
      simp only [ContinuousLinearMap.coe_restrictScalars']
      have hv : w - p = ∑ i, (w - p) i • (Pi.single i (1 : ℂ) : Fin n → ℂ) := by
        ext j
        simp [Finset.sum_apply, Pi.single_apply]
      rw [hv, map_sum]
      simp only [map_smul, hU'i, smul_eq_mul, k, projIcc_of_mem _ hs, G, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rwa [hval] at h
  have h0 : G 0 = U p := by simp [G, γ]
  have h1 : G 1 = U w := by simp [G, γ]
  rw [← h0, ← h1, eq_mul_exp_integral_of_hasDerivAt hG hk]
  congr 2
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le zero_le_one] at hs
  simp only [k, projIcc_of_mem _ hs, γ]

/-- **Integrating a decomposed logarithmic derivative.** -/
theorem eq_mul_exp_of_decomposition {n : ℕ} {Ω : Set (Fin n → ℂ)} (hΩc : Convex ℝ Ω)
    (hΩo : IsOpen Ω) {p w : Fin n → ℂ} (hp : p ∈ Ω) (hw : w ∈ Ω) {U : (Fin n → ℂ) → ℂ}
    {κ : Fin n → (Fin n → ℂ) → ℂ}
    (hU : ∀ v ∈ Ω, ∃ U' : (Fin n → ℂ) →L[ℂ] ℂ, HasFDerivAt U U' v ∧
      ∀ i, U' (Pi.single i 1) = κ i v * U v)
    {Lc : Fin n → ℕ} (Pv : ∀ i, Fin (Lc i) → ℂ) (Gv : ∀ i, Fin (Lc i) → (Fin n → ℂ) → ℂ)
    (hGc : ∀ i l, ContinuousOn (Gv i l) Ω) (H₀ H₁ : Fin n → (Fin n → ℂ) → ℂ)
    (hH₀ : ∀ i, ContinuousOn (H₀ i) Ω) (hH₁ : ∀ i, ContinuousOn (H₁ i) Ω)
    (hdec : ∀ i, ∀ v ∈ Ω, κ i v = (∑ l, Pv i l * Gv i l v) + H₁ i v - H₀ i v) :
    U w = U p * Complex.exp ((∑ i, ∑ l, Pv i l *
        ∫ s in (0 : ℝ)..1, (w - p) i * Gv i l (p + s • (w - p))) +
      (∫ s in (0 : ℝ)..1, ∑ i, (w - p) i * H₁ i (p + s • (w - p))) -
      ∫ s in (0 : ℝ)..1, ∑ i, (w - p) i * H₀ i (p + s • (w - p))) := by
  have hγ : ∀ s ∈ Icc (0 : ℝ) 1, p + s • (w - p) ∈ Ω := fun s hs =>
    hΩc.add_smul_sub_mem hp hw hs
  have hcomp : ∀ {g : (Fin n → ℂ) → ℂ}, ContinuousOn g Ω →
      ContinuousOn (fun s : ℝ => g (p + s • (w - p))) (Icc 0 1) := fun hg =>
    hg.comp (Continuous.continuousOn (by fun_prop)) fun s hs => hγ s hs
  have hint : ∀ {g : ℝ → ℂ}, ContinuousOn g (Icc 0 1) → IntervalIntegrable g volume 0 1 :=
    fun hg => hg.intervalIntegrable_of_Icc zero_le_one
  have hκc : ∀ i, ContinuousOn (κ i) Ω := by
    intro i
    have : ContinuousOn (fun v => (∑ l, Pv i l * Gv i l v) + H₁ i v - H₀ i v) Ω :=
      ((continuousOn_finset_sum _ fun l _ => continuousOn_const.mul (hGc i l)).add
        (hH₁ i)).sub (hH₀ i)
    exact this.congr fun v hv => hdec i v hv
  rw [eq_mul_exp_of_hasFDerivAt hΩc hΩo hp hw hκc hU]
  congr 2
  have e1 : ∀ s ∈ uIcc (0 : ℝ) 1, (∑ i, (w - p) i * κ i (p + s • (w - p))) =
      (∑ i, ∑ l, Pv i l * ((w - p) i * Gv i l (p + s • (w - p)))) +
        (∑ i, (w - p) i * H₁ i (p + s • (w - p))) -
        ∑ i, (w - p) i * H₀ i (p + s • (w - p)) := by
    intro s hs
    rw [uIcc_of_le zero_le_one] at hs
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hdec i _ (hγ s hs), mul_sub, mul_add, Finset.mul_sum]
    congr 2
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [intervalIntegral.integral_congr e1]
  have hA : IntervalIntegrable (fun s : ℝ => ∑ i, ∑ l, Pv i l * ((w - p) i *
      Gv i l (p + s • (w - p)))) volume 0 1 :=
    hint (continuousOn_finset_sum _ fun i _ => continuousOn_finset_sum _ fun l _ =>
      continuousOn_const.mul (continuousOn_const.mul (hcomp (hGc i l))))
  have hB : ∀ H : Fin n → (Fin n → ℂ) → ℂ, (∀ i, ContinuousOn (H i) Ω) →
      IntervalIntegrable (fun s : ℝ => ∑ i, (w - p) i * H i (p + s • (w - p))) volume 0 1 :=
    fun H hH => hint (continuousOn_finset_sum _ fun i _ => continuousOn_const.mul (hcomp (hH i)))
  rw [intervalIntegral.integral_sub (hA.add (hB H₁ hH₁)) (hB H₀ hH₀),
    intervalIntegral.integral_add hA (hB H₁ hH₁)]
  congr 2
  rw [intervalIntegral.integral_finset_sum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [intervalIntegral.integral_finset_sum]
    · refine Finset.sum_congr rfl fun l _ => ?_
      rw [intervalIntegral.integral_const_mul]
    · intro l _
      exact hint (continuousOn_const.mul (continuousOn_const.mul (hcomp (hGc i l))))
  · intro i _
    exact hint (continuousOn_finset_sum _ fun l _ =>
      continuousOn_const.mul (continuousOn_const.mul (hcomp (hGc i l))))

/-- Exchanging finite sums and a segment integral. -/
theorem sum_sum_mul_integral {n : ℕ} {Ω : Set (Fin n → ℂ)} (hΩc : Convex ℝ Ω)
    {p w : Fin n → ℂ} (hp : p ∈ Ω) (hw : w ∈ Ω) {Lc : Fin n → ℕ} (a : ∀ i, Fin (Lc i) → ℂ)
    (G : ∀ i, Fin (Lc i) → (Fin n → ℂ) → ℂ) (hG : ∀ i l, ContinuousOn (G i l) Ω) :
    (∑ i, ∑ l, a i l * ∫ s in (0 : ℝ)..1, (w - p) i * G i l (p + s • (w - p))) =
      ∫ s in (0 : ℝ)..1, ∑ i, (w - p) i * ∑ l, a i l * G i l (p + s • (w - p)) := by
  have hγ : ∀ s ∈ Icc (0 : ℝ) 1, p + s • (w - p) ∈ Ω := fun s hs =>
    hΩc.add_smul_sub_mem hp hw hs
  have hc : ∀ i l, IntervalIntegrable (fun s : ℝ => G i l (p + s • (w - p))) volume 0 1 :=
    fun i l => ((hG i l).comp (Continuous.continuousOn (by fun_prop))
      fun s hs => hγ s hs).intervalIntegrable_of_Icc zero_le_one
  rw [intervalIntegral.integral_finset_sum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    have e1 : (∫ s in (0 : ℝ)..1, (w - p) i * ∑ l, a i l * G i l (p + s • (w - p))) =
        ∫ s in (0 : ℝ)..1, ∑ l, a i l * ((w - p) i * G i l (p + s • (w - p))) := by
      refine intervalIntegral.integral_congr fun s _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
    rw [e1, intervalIntegral.integral_finset_sum]
    · refine Finset.sum_congr rfl fun l _ => ?_
      simp only [intervalIntegral.integral_const_mul]
    · intro l _
      exact ((hc i l).const_mul _).const_mul _
  · intro i _
    exact IntervalIntegrable.const_mul ((continuousOn_finset_sum _ fun l _ =>
      continuousOn_const.mul ((hG i l).comp (Continuous.continuousOn (by fun_prop))
        fun s hs => hγ s hs)).intervalIntegrable_of_Icc zero_le_one) _

end Ana

end AnaSec

end Fam

end FamilyLogarithm

end MMP.JacobianLogarithm

end
