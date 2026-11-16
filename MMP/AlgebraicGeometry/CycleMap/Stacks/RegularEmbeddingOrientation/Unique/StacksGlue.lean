module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.RegularEmbeddingOrientation.Unique.StacksLocal
public import MMP.AlgebraicGeometry.CycleMap.Stacks.RegularEmbeddingOrientation.Quot.StacksExists
public import Mathlib.Topology.PartitionOfUnity

/-!
# Gluing the local comparison maps (Stacks bundles)

Let `D₁`, `D₂` be orientation data of a regular closed imbedding `i : X → Y` of complex schemes
(`MMP.Modules.RegularImbeddingOrientationDatum`). The local comparison maps `Q₁ → Q₂` near the
points of `X(ℂ)` (`MMP.Modules.RegularImbeddingOrientationDatum.exists_local_bundleMap`), glued
with a partition of unity on `Y(ℂ)` subordinate to their domains and normalised by the sum of the
weights, give a fibrewise linear map `φ : Q₁ → Q₂` on a neighbourhood of `X(ℂ)`, continuous on the
total space and carrying `σ̄₁` to `σ̄₂`. Both conditions, and compatibility with presentations at
the points of `X(ℂ)`, are affine, so they survive the gluing; compatibility makes `φ` an
isomorphism at the points of `X(ℂ)`, hence near `X(ℂ)`.

## Main results

* `MMP.Modules.RegularImbeddingOrientationDatum.IsPresentationCompatible.injective`
* `MMP.Modules.RegularImbeddingOrientationDatum.exists_glued_bundleMap`
* `MMP.Modules.IsRegularImbeddingOrientationClass.eq`: uniqueness of orientation classes.
* `MMP.Modules.existsUnique_isRegularImbeddingOrientationClass`: every regular closed imbedding
  of complex schemes has exactly one orientation class.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Set Bundle Topology Filter

namespace MMP.Modules

/-- A finitely supported combination `∑ᶠ i, cᵢ • ψᵢ` with `∑ᶠ cᵢ = 1` takes `w` to `z` if every
`ψᵢ` with `cᵢ ≠ 0` does. -/
lemma finsum_smul_apply_eq {R ι M N : Type*} [CommSemiring R] [AddCommMonoid M]
    [AddCommMonoid N] [Module R M] [Module R N] {c : ι → R} (hc : (Function.support c).Finite)
    (hc1 : ∑ᶠ i, c i = 1) (ψ : ι → M →ₗ[R] N) {w : M} {z : N} (h : ∀ i, c i ≠ 0 → ψ i w = z) :
    (∑ᶠ i, c i • ψ i) w = z := by
  classical
  have hs : Function.support (fun i ↦ c i • ψ i) ⊆ hc.toFinset := fun i hi ↦
    hc.mem_toFinset.2 fun h0 ↦ hi (by simp [h0])
  rw [finsum_eq_sum_of_support_subset _ hs, LinearMap.sum_apply]
  rw [finsum_eq_sum_of_support_subset _ (Finite.coe_toFinset hc).symm.subset] at hc1
  calc ∑ i ∈ hc.toFinset, (c i • ψ i) w = ∑ i ∈ hc.toFinset, c i • z := by
        refine Finset.sum_congr rfl fun i hi ↦ ?_
        rw [LinearMap.smul_apply, h i ((Finite.mem_toFinset hc).1 hi)]
    _ = z := by rw [← Finset.sum_smul, hc1, one_smul]

open UnderlyingSpace
open Stacks.AlgebraicGeometry.RegularIdealSheaf (IsRegularClosedImmersionOfCodim)

variable {X Y : Scheme.{0}} [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))]

namespace RegularImbeddingOrientationDatum

variable {i : X ⟶ Y} [i.IsOver (Spec (.of ℂ))] {d : ℕ}
  {D₁ D₂ : RegularImbeddingOrientationDatum i d}

/-- The fibres of the bundle `Q` of an orientation datum have dimension `d`. -/
lemma finrank_Q (D : RegularImbeddingOrientationDatum i d) (y : D.nbhd) :
    Module.finrank ℂ (D.Q y) = d := by
  rw [((trivializationAt D.F D.Q y).continuousLinearEquivAt ℂ y
    (FiberBundle.mem_baseSet_trivializationAt D.F D.Q y)).toLinearEquiv.finrank_eq, D.finrank_F]

/-- The fibres of the bundle `Q` of an orientation datum are finite-dimensional. -/
instance finiteDimensional_Q (D : RegularImbeddingOrientationDatum i d) (y : D.nbhd) :
    FiniteDimensional ℂ (D.Q y) :=
  Module.Finite.equiv ((trivializationAt D.F D.Q y).continuousLinearEquivAt ℂ y
    (FiberBundle.mem_baseSet_trivializationAt D.F D.Q y)).toLinearEquiv.symm

/-- **Compatible maps are injective at the points of `X(ℂ)`.** -/
theorem IsPresentationCompatible.injective [IsClosedImmersion i]
    (hi : IsRegularClosedImmersionOfCodim i d)
    {b : ↥(D₁.nbhd ∩ D₂.nbhd)} (hb : b.1 ∈ range (UnderlyingSpace.map i))
    {ψ : D₁.Q (interIncl₁ D₁ D₂ b) →ₗ[ℂ] D₂.Q (interIncl₂ D₁ D₂ b)}
    (h : IsPresentationCompatible D₁ D₂ b ψ) : Function.Injective ψ := by
  obtain ⟨x, hx⟩ := hb
  obtain ⟨W, hW₁, hW₂, hxW, M₁, G₁, M₂, G₂, f, hP⟩ := exists_isLocalRegularPresentation_pair i hi
    D₁.comp_proj D₁.zeroLocus_eq D₂.comp_proj D₂.zeroLocus_eq (chartAt D₁.E D₁.rank b.1)
    (chartAt D₂.E D₂.rank b.1) x (hx ▸ mem_chartBase_chartAt D₁.E D₁.rank b.1)
    (hx ▸ mem_chartBase_chartAt D₂.E D₂.rank b.1)
  obtain ⟨k₁, k₂⟩ := hP x hxW
  have hb₁ : ⊤ ≤ b.1.toHom ⁻¹ᵁ (chartAt D₁.E D₁.rank b.1).1.1 :=
    mem_chartBase_chartAt D₁.E D₁.rank b.1
  have hb₂ : ⊤ ≤ b.1.toHom ⁻¹ᵁ (chartAt D₂.E D₂.rank b.1).1.1 :=
    mem_chartBase_chartAt D₂.E D₂.rank b.1
  obtain ⟨y, hy⟩ := b
  change UnderlyingSpace.map i x = y at hx
  subst hx
  set A₁ := D₁.chartL (chartAt D₁.E D₁.rank (mapFun i x)) (interIncl₁ D₁ D₂ ⟨_, hy⟩) ∘ₗ
    evalMatrix (mapFun i x) hxW M₁
  set A₂ := D₂.chartL (chartAt D₂.E D₂.rank (mapFun i x)) (interIncl₂ D₁ D₂ ⟨_, hy⟩) ∘ₗ
    evalMatrix (mapFun i x) hxW M₂
  have hA₁ : Function.Injective A₁ := injective_comp_evalMatrix k₁ _
    (D₁.isCompl_ker_chartL _ _ hb₁ ⟨x, rfl⟩)
  have hA₂ : Function.Injective A₂ := injective_comp_evalMatrix k₂ _
    (D₂.isCompl_ker_chartL _ _ hb₂ ⟨x, rfl⟩)
  have hA₁s : Function.Surjective A₁ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [Module.finrank_fin_fun, finrank_Q])).1 hA₁
  have hψ : ∀ u, ψ (A₁ u) = A₂ u := fun u ↦ h _ _ W hW₁ hW₂ hxW M₁ G₁ M₂ G₂ f k₁ k₂ u
  intro w w' hww'
  obtain ⟨u, rfl⟩ := hA₁s w
  obtain ⟨u', rfl⟩ := hA₁s w'
  rw [hψ, hψ] at hww'
  rw [hA₂ hww']

variable (D₁ D₂) in
/-- **The glued comparison map.** There are an open neighbourhood `W` of `X(ℂ)` in `V₁ ∩ V₂` and a
fibrewise linear map `φ : Q₁ → Q₂` over `V₁ ∩ V₂`, continuous on the total space over `W`,
injective on the fibres over `W` and carrying `s̄₁` to `s̄₂` over `W`. -/
theorem exists_glued_bundleMap [IsComplexScheme Y] [IsClosedImmersion i]
    (hi : IsRegularClosedImmersionOfCodim i d) :
    ∃ W : Set ↥(D₁.nbhd ∩ D₂.nbhd), IsOpen W ∧
      (∀ b : ↥(D₁.nbhd ∩ D₂.nbhd), b.1 ∈ range (UnderlyingSpace.map i) → b ∈ W) ∧
      ∃ φ : ∀ b : ↥(D₁.nbhd ∩ D₂.nbhd), D₁.Q (interIncl₁ D₁ D₂ b) →ₗ[ℂ] D₂.Q (interIncl₂ D₁ D₂ b),
        (∀ p : TotalSpace D₁.F (⇑(interIncl₁ D₁ D₂) *ᵖ D₁.Q), p.proj ∈ W →
          ContinuousAt (totalSpaceMap D₂.F (E₁ := ⇑(interIncl₁ D₁ D₂) *ᵖ D₁.Q)
            (E₂ := ⇑(interIncl₂ D₁ D₂) *ᵖ D₂.Q) φ) p) ∧
        (∀ b ∈ W, Function.Injective (φ b)) ∧
        (∀ b ∈ W, ∀ v, D₁.sectionBar (interIncl₁ D₁ D₂ b) = ⟨interIncl₁ D₁ D₂ b, v⟩ →
            D₂.sectionBar (interIncl₂ D₁ D₂ b) = ⟨interIncl₂ D₁ D₂ b, φ b v⟩) := by
  classical
  choose O hO hxO φl hφc hφs hφcomp using fun x ↦ exists_local_bundleMap D₁ D₂ hi x
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate (X := UnderlyingSpace ℂ Y)
    isClosed_range_map O hO (range_subset_iff.2 fun x ↦ mem_iUnion.2 ⟨x, hxO x⟩)
  set S : UnderlyingSpace ℂ Y → ℝ := fun y ↦ ∑ᶠ x, ρ x y
  have hS : Continuous S := continuous_finsum (fun x ↦ (ρ x).continuous) ρ.locallyFinite
  have hS1 : ∀ y ∈ range (UnderlyingSpace.map (K := ℂ) i), S y = 1 := fun y hy ↦ ρ.sum_eq_one hy
  let w : UnderlyingSpace ℂ X → ↥(D₁.nbhd ∩ D₂.nbhd) → ℂ :=
    fun x b ↦ (ρ x b.1 : ℂ) * ((S b.1 : ℂ))⁻¹
  let φ : ∀ b : ↥(D₁.nbhd ∩ D₂.nbhd), D₁.Q (interIncl₁ D₁ D₂ b) →ₗ[ℂ] D₂.Q (interIncl₂ D₁ D₂ b) :=
    fun b ↦ ∑ᶠ x, w x b • φl x b
  let G : Set ↥(D₁.nbhd ∩ D₂.nbhd) := {b | S b.1 ≠ 0}
  have hG : IsOpen G := isOpen_ne_fun (hS.comp continuous_subtype_val) continuous_const
  have hwfin : ∀ b, (Function.support fun x ↦ w x b).Finite := fun b ↦
    (ρ.locallyFinite.point_finite b.1).subset fun x hx h0 ↦ hx (by simp [w, h0])
  have hwsum : ∀ b ∈ G, ∑ᶠ x, w x b = 1 := by
    intro b hb
    have h1 : ∑ᶠ x, (ρ x b.1 : ℂ) = (S b.1 : ℂ) := by
      rw [← Complex.ofRealHom_eq_coe, map_finsum _ (ρ.locallyFinite.point_finite b.1)]
      rfl
    simp only [w]
    rw [← finsum_mul, h1, mul_inv_cancel₀ (Complex.ofReal_ne_zero.2 hb)]
  have hwO : ∀ x b, w x b ≠ 0 → b.1 ∈ O x := fun x b h ↦
    hρ x (subset_tsupport _ fun h0 ↦ h (by simp [w, h0]))
  have hX : ∀ b : ↥(D₁.nbhd ∩ D₂.nbhd), b.1 ∈ range (UnderlyingSpace.map i) → b ∈ G :=
    fun b hb ↦ by simp [G, hS1 b.1 hb]
  have hcomp : ∀ b : ↥(D₁.nbhd ∩ D₂.nbhd), b.1 ∈ range (UnderlyingSpace.map i) →
      IsPresentationCompatible D₁ D₂ b (φ b) := by
    intro b hb j₁ j₂ W hW₁ hW₂ hxW M₁ G₁ M₂ G₂ f h₁ h₂ v
    exact finsum_smul_apply_eq (hwfin b) (hwsum b (hX b hb)) _ fun x hx ↦
      hφcomp x b (hwO x b hx) hb j₁ j₂ W hW₁ hW₂ hxW M₁ G₁ M₂ G₂ f h₁ h₂ v
  have hcont : ∀ p : TotalSpace D₁.F (⇑(interIncl₁ D₁ D₂) *ᵖ D₁.Q), p.proj ∈ G →
      ContinuousAt (totalSpaceMap D₂.F (E₁ := ⇑(interIncl₁ D₁ D₂) *ᵖ D₁.Q)
        (E₂ := ⇑(interIncl₂ D₁ D₂) *ᵖ D₂.Q) φ) p := by
    intro p hp
    have hlf : LocallyFinite fun x ↦ Function.support (w x) :=
      (ρ.locallyFinite.preimage_continuous continuous_subtype_val).subset fun x b hb h0 ↦
        hb (by simp [w, h0])
    refine continuousAt_totalSpace_finsum_smul (F₂ := D₂.F)
      (E₁ := ⇑(interIncl₁ D₁ D₂) *ᵖ D₁.Q) (E₂ := ⇑(interIncl₂ D₁ D₂) *ᵖ D₂.Q) w hlf φl p
      fun x hx ↦ ⟨?_, ?_⟩
    · exact (Complex.continuous_ofReal.continuousAt.comp
        ((ρ x).continuous.comp continuous_subtype_val).continuousAt).mul
        ((Complex.continuous_ofReal.continuousAt.comp
          (hS.comp continuous_subtype_val).continuousAt).inv₀ (Complex.ofReal_ne_zero.2 hp))
    · have hts : tsupport (w x) ⊆ Subtype.val ⁻¹' tsupport (ρ x) :=
        closure_minimal (fun b hb ↦ subset_tsupport _ (show b.1 ∈ Function.support (ρ x) from
            fun h0 ↦ hb (by simp [w, h0])))
          ((isClosed_tsupport _).preimage continuous_subtype_val)
      exact hφc x p (hρ x (hts hx))
  refine ⟨interior {b | b ∈ G ∧ Function.Injective (φ b)}, isOpen_interior, ?_, φ,
    fun p hp ↦ hcont p (interior_subset hp).1, fun b hb ↦ (interior_subset hb).2, ?_⟩
  · intro b hb
    rw [mem_interior_iff_mem_nhds]
    exact Filter.Eventually.and (hG.mem_nhds (hX b hb))
      (eventually_injective_of_continuousAt_totalSpace
        (E₁ := ⇑(interIncl₁ D₁ D₂) *ᵖ D₁.Q) (E₂ := ⇑(interIncl₂ D₁ D₂) *ᵖ D₂.Q)
        (D₁.finrank_F.trans D₂.finrank_F.symm) φ (fun v ↦ hcont _ (hX b hb))
        ((hcomp b hb).injective hi hb))
  · intro b hb v hv
    have hbG := (interior_subset hb).1
    obtain ⟨x₀, hx₀⟩ : ∃ x, w x b ≠ 0 := by
      by_contra! h
      simpa [h] using hwsum b hbG
    have h₀ := hφs x₀ b (hwO x₀ b hx₀) v hv
    rw [h₀]
    congr 1
    exact (finsum_smul_apply_eq (hwfin b) (hwsum b hbG) _ fun x hx ↦
      TotalSpace.mk_inj.1 ((hφs x b (hwO x b hx) v hv).symm.trans h₀)).symm

variable (R : Type) [CommRing R]

/-- **Uniqueness of the orientation class**: two orientation classes of a regular imbedding of
complex schemes are equal. -/
theorem _root_.MMP.Modules.IsRegularImbeddingOrientationClass.eq [IsComplexScheme Y]
    [IsClosedImmersion i] (hi : IsRegularClosedImmersionOfCodim i d)
    {u₁ u₂ : cohomologyWithSupports R (ModuleCat.of R R)
      (TopCat.of (UnderlyingSpace ℂ Y)) (range (UnderlyingSpace.map i)) (2 * d : ℕ)}
    (h₁ : IsRegularImbeddingOrientationClass R i d u₁)
    (h₂ : IsRegularImbeddingOrientationClass R i d u₂) : u₁ = u₂ := by
  obtain ⟨D₁, uQ₁, hQ₁, hu₁⟩ := h₁
  obtain ⟨D₂, uQ₂, hQ₂, hu₂⟩ := h₂
  obtain ⟨WB, hWB, hXW, φ, hφc, hφi, hφs⟩ := exists_glued_bundleMap D₁ D₂ hi
  set Wset : Set (UnderlyingSpace ℂ Y) := Subtype.val '' WB
  have hWo : IsOpen Wset := (D₁.isOpen_nbhd.inter D₂.isOpen_nbhd).isOpenMap_subtype_val _ hWB
  have hXW' : range (UnderlyingSpace.map (K := ℂ) i) ⊆ Wset := fun y hy ↦
    ⟨⟨y, D₁.range_subset_nbhd hy, D₂.range_subset_nbhd hy⟩, hXW _ hy, rfl⟩
  have hW₁ : Wset ⊆ D₁.nbhd := image_subset_iff.2 fun b _ ↦ b.2.1
  have hW₂ : Wset ⊆ D₂.nbhd := image_subset_iff.2 fun b _ ↦ b.2.2
  let toB : Wset → ↥(D₁.nbhd ∩ D₂.nbhd) := fun y ↦ ⟨y.1, hW₁ y.2, hW₂ y.2⟩
  have htoB : ∀ y : Wset, toB y ∈ WB := fun y ↦ mem_of_val_mem_image (S := D₁.nbhd ∩ D₂.nbhd) y.2
  have hbij : ∀ y : Wset, Function.Bijective (φ (toB y)) := fun y ↦
    ⟨hφi _ (htoB y), (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [finrank_Q, finrank_Q])).1 (hφi _ (htoB y))⟩
  let ψ : ∀ y : Wset, D₁.Q ⟨y, hW₁ y.2⟩ ≃L[ℂ] D₂.Q ⟨y, hW₂ y.2⟩ := fun y ↦
    fibreContinuousLinearEquiv D₁.F D₂.F (E₁ := ⇑(interIncl₁ D₁ D₂) *ᵖ D₁.Q)
      (E₂ := ⇑(interIncl₂ D₁ D₂) *ᵖ D₂.Q) (LinearEquiv.ofBijective (φ (toB y)) (hbij y))
  let J : TotalSpace D₁.F (⇑(ContinuousMap.inclusion hW₁) *ᵖ D₁.Q) →
      TotalSpace D₁.F (⇑(interIncl₁ D₁ D₂) *ᵖ D₁.Q) := fun p ↦ ⟨toB p.proj, p.2⟩
  have hJ : Continuous J := by
    have hproj : Continuous (TotalSpace.proj :
        TotalSpace D₁.F (⇑(ContinuousMap.inclusion hW₁) *ᵖ D₁.Q) → Wset) :=
      Pullback.continuous_proj D₁.F D₁.Q _
    have hlift : Continuous (Pullback.lift (ContinuousMap.inclusion hW₁) :
        TotalSpace D₁.F (⇑(ContinuousMap.inclusion hW₁) *ᵖ D₁.Q) → TotalSpace D₁.F D₁.Q) :=
      Pullback.continuous_lift D₁.F D₁.Q _
    change Continuous[_, pullbackTopology D₁.F D₁.Q (interIncl₁ D₁ D₂)] J
    rw [pullbackTopology_def]
    exact continuous_inf_rng.2 ⟨continuous_induced_rng.2
      ((continuous_subtype_val.comp hproj).subtype_mk _),
      continuous_induced_rng.2 (by exact hlift)⟩
  have hφ : Continuous fun p : TotalSpace D₁.F (⇑(ContinuousMap.inclusion hW₁) *ᵖ D₁.Q) ↦
      (⟨⟨p.proj, hW₂ p.proj.2⟩, ψ p.proj p.2⟩ : TotalSpace D₂.F D₂.Q) :=
    continuous_iff_continuousAt.2 fun p ↦
      (Pullback.continuous_lift D₂.F D₂.Q (interIncl₂ D₁ D₂)).continuousAt.comp
        ((hφc (J p) (htoB p.proj)).comp hJ.continuousAt)
  exact eq_of_continuous_equiv R D₁ D₂ hWo hXW' hW₁ hW₂ ψ hφ
    (fun y v hv ↦ hφs (toB y) (htoB y) v hv) hQ₁ hQ₂ hu₁ hu₂

end RegularImbeddingOrientationDatum

/-- **The orientation class of a regular imbedding** (Fulton, §19.2): a regular imbedding
`i : X → Y` of codimension `d` of complex schemes has exactly one orientation class
`u_{X,Y} ∈ H^{2d}(Y, Y - X)`: orientation data `(E, s, V, C)` exist, and all of them give the same
class. -/
theorem existsUnique_isRegularImbeddingOrientationClass {i : X ⟶ Y} [i.IsOver (Spec (.of ℂ))]
    {d : ℕ} (R : Type) [CommRing R] [IsComplexScheme Y] [IsClosedImmersion i]
    (hi : IsRegularClosedImmersionOfCodim i d) :
    ∃! u, IsRegularImbeddingOrientationClass R i d u := by
  obtain ⟨u, hu⟩ := exists_isRegularImbeddingOrientationClass R hi
  exact ⟨u, hu, fun u' hu' ↦ hu'.eq R hi hu⟩

end MMP.Modules
