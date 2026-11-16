module

public import MMP.AlgebraicGeometry.MMP.ConeTheorem.KltConeDatum
public import MMP.AlgebraicGeometry.MMP.ConeTheorem.AbstractConeTheorem

@[expose] public section

/-!
# Negative extremal faces of the cone of curves are rational polyhedral

Let `(X, Δ)` be a klt pair, `X` projective over `k`, `Δ ≥ 0`, and `F` a `(K_X + Δ)`-negative
extremal face of `NE̅(X)`. If `K_X + Δ` is nef then `F = {0}`. Otherwise `NE̅(X)` is the cone of
a cone datum on `N₁(X)_ℤ`; a form `G` positive on `NE̅ ∖ {0}` and `ε > 0` below the minimum of
`-(K_X + Δ)` on the compact slice `F ∩ {G = 1}` give `F ∩ NE̅_{K+εG≥0} = {0}`, so the abstract
cone theorem writes `F` as the sum of the finitely many rays of `𝓡(NE̅, K)` it contains, each
spanned by a lattice point.

## Main results

* `MMP.Mori.exists_eq_hull_of_isNegativeExtremalFace`: every `(K_X + Δ)`-negative extremal face
  `F` of `NE̅(X)` is `ℝ_{≥0} ξ₁ + ⋯ + ℝ_{≥0} ξ_m` for finitely many `ξⱼ ∈ N₁(X)_ℤ`, each spanning
  a `(K_X + Δ)`-negative extremal ray.

## Implementation notes

The argument is carried out in `ℝ ⊗_ℤ N₁(X)_ℤ` with the cone of the cone datum and transported
along the isomorphism `ℝ ⊗_ℤ N₁(X)_ℤ ≅ N₁(X)`. The positive form `G` is taken from the salience
`NE̅ ∩ (-NE̅) = {0}` of the cone datum rather than from an ample divisor; only its positivity on
`NE̅ ∖ {0}` is used.

The sum `∑ ℝ_{≥0} ξⱼ` is the pointed cone `PointedCone.hull ℝ` of the `ξⱼ`, and the ray
`ℝ_{≥0} ξⱼ` is the set `{c • ξⱼ | c ≥ 0}`. The form `z ↦ ((K_X + Δ) · z)` is
`MMP.Fourfold.QDivisor.curveForm` of `K_X + Δ`, which is `ℚ`-Cartier by the pair condition; a
`(K_X + Δ)`-negative extremal ray is `MMP.Fourfold.IsNegativeExtremalRayOf`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 3.3 Step 6
-/

namespace MMP.FourfoldProofs.Km3bNegativeFaceFinitelyGeneratedProof

open CategoryTheory AlgebraicGeometry MMP.Mori
open scoped TensorProduct

section Nef

variable {k : Type} [Field k] {X : Scheme.{0}} [CompactSpace X] [IsLocallyNoetherian X]
  [IsNormal X] (sX : X ⟶ Spec (.of k)) [QuasiCompact sX]

/-- The curve form of a `ℚ`-Cartier `ℚ`-divisor is continuous for the numerical topology. -/
private theorem continuous_curveForm (D : QDivisor X) (h : D.IsQCartier) :
    Continuous (MMP.Fourfold.QDivisor.curveForm sX D h) := by
  rw [MMP.Fourfold.QDivisor.curveForm, Finsupp.sum]
  refine (continuous_finset_sum _ fun E _ => ?_).congr fun z => (LinearMap.sum_apply _ _ z).symm
  haveI := (Divisor.mem_cartierSubgroup.mp E.2).isInvertibleModule_divisorialSheaf
  exact continuous_const.mul (NumericalCurveClasses.continuous_degree sX _)

/-- A nef `ℚ`-divisor is nonnegative on the closed cone of curves. -/
private theorem curveForm_nonneg_of_isNef {D : QDivisor X} (hD : QDivisor.IsNef k sX D)
    (h : D.IsQCartier) {z : NumericalCurveClasses sX} (hz : z ∈ closedConeOfCurves sX) :
    0 ≤ MMP.Fourfold.QDivisor.curveForm sX D h z := by
  obtain ⟨hD', hnef⟩ := hD
  have hcl : IsClosed {z | 0 ≤ MMP.Fourfold.QDivisor.curveForm sX D h z} :=
    isClosed_le continuous_const (continuous_curveForm sX D h)
  let P : PointedCone ℝ (NumericalCurveClasses sX) :=
    { carrier := {z | 0 ≤ MMP.Fourfold.QDivisor.curveForm sX D h z}
      zero_mem' := by simp
      add_mem' := fun ha hb => by
        simp only [Set.mem_setOf_eq, map_add] at *
        linarith
      smul_mem' := fun c x hx => by
        simp only [Set.mem_setOf_eq] at *
        rw [show c • x = (c : ℝ) • x from rfl, map_smul, smul_eq_mul]
        exact mul_nonneg c.2 hx }
  have hle : coneOfCurves sX ≤ P := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨C, rfl⟩
    show 0 ≤ MMP.Fourfold.QDivisor.curveForm sX D h _
    rw [MMP.ProgramBaseChange.curveForm_numericalClass_cycle sX D h C]
    exact_mod_cast hnef C.scheme C.ι C.dim_eq
  exact closure_minimal (fun x hx => hle hx) hcl hz

/-- A `D`-negative extremal face of the closed cone of curves is `{0}` when `D` is nef. -/
theorem eq_singleton_zero_of_isNef {D : QDivisor X} (hD : QDivisor.IsNef k sX D)
    (h : D.IsQCartier) {F : Set (NumericalCurveClasses sX)}
    (hF : IsNegativeExtremalFace ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX))
      (MMP.Fourfold.QDivisor.curveForm sX D h) F) : F = {0} := by
  ext z
  simp only [Set.mem_singleton_iff]
  refine ⟨fun hz => ?_, fun hz => hz ▸ hF.1.2.1.1⟩
  by_contra hz0
  exact (hF.2.2 z hz hz0).not_ge (curveForm_nonneg_of_isNef sX hD _ (hF.1.1 hz))

end Nef

section Abstract

open MMP.Positivity TensorProduct

variable {N : Type} [AddCommGroup N] [Module.Free ℤ N] [Module.Finite ℤ N]

/-- Negative extremal faces pull back along a linear equivalence carrying one cone onto the other
and one form to the other. -/
theorem isNegativeExtremalFace_preimage {U W : Type*} [AddCommGroup U] [Module ℝ U]
    [AddCommGroup W] [Module ℝ W] (φ : U ≃ₗ[ℝ] W) {C : Set U} {C' : Set W} (hC : C' = φ '' C)
    {K : Module.Dual ℝ U} {K' : Module.Dual ℝ W} (hK : ∀ v, K v = K' (φ v)) {F : Set W}
    (hF : IsNegativeExtremalFace ℝ C' K' F) : IsNegativeExtremalFace ℝ C K (φ ⁻¹' F) := by
  obtain ⟨hFe, hFadd, hFneg⟩ := hF
  have hmem : ∀ v, v ∈ C ↔ φ v ∈ C' := fun v => by rw [hC, φ.injective.mem_set_image]
  refine ⟨⟨fun v hv => (hmem v).2 (hFe.1 hv), ⟨by simpa using hFe.2.1.1, fun v hv c hc => ?_⟩,
    fun u hu v hv => ?_, fun u hu v hv huv => ?_⟩, fun u hu v hv => ?_, fun z hz hz0 => ?_⟩
  · simpa using hFe.2.1.2 _ hv c hc
  · simpa using hFe.2.2.1 _ hu _ hv
  · exact hFe.2.2.2 _ ((hmem u).1 hu) _ ((hmem v).1 hv) (by simpa using huv)
  · simpa using hFadd _ hu _ hv
  · rw [hK]
    exact hFneg _ hz (by simpa using hz0)

/-- If `G` is positive on a closed cone `C ∖ {0}` and `K` is negative on a closed extremal face
`F ∖ {0}`, then `K + εG` is still negative on `F ∖ {0}` for some `ε > 0`. -/
theorem exists_pos_add_mul_neg_of_isExtremalFace {V : Type*} [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V]
    [FiniteDimensional ℝ V] {C F : Set V} (hCc : IsCone ℝ C) (hCcl : IsClosed C)
    {G K : Module.Dual ℝ V} (hG : ∀ z ∈ C, z ≠ 0 → 0 < G z) (hFe : IsExtremalFace ℝ C F)
    (hFcl : IsClosed F) (hFneg : ∀ z ∈ F, z ≠ 0 → K z < 0) :
    ∃ ε > 0, ∀ z ∈ F, z ≠ 0 → K z + ε * G z < 0 := by
  have hKc : Continuous K := LinearMap.continuous_of_finiteDimensional K
  have hGc : Continuous G := LinearMap.continuous_of_finiteDimensional G
  obtain ⟨κ, hκ, hκF⟩ : ∃ κ : ℝ, 0 < κ ∧ ∀ z ∈ F, G z = 1 → κ ≤ -K z := by
    set T := {z | z ∈ F ∧ G z = 1} with hTdef
    have hT : IsCompact T :=
      (isCompact_slice hCc hCcl hG 1).of_isClosed_subset
        (hFcl.inter (isClosed_eq hGc continuous_const)) fun z hz => ⟨hFe.1 hz.1, hz.2.le⟩
    rcases T.eq_empty_or_nonempty with hTe | hTn
    · refine ⟨1, one_pos, fun z hz hz1 => ?_⟩
      have : z ∈ T := ⟨hz, hz1⟩
      rw [hTe] at this
      exact this.elim
    · obtain ⟨z₀, hz₀, hmin⟩ := hT.exists_isMinOn hTn (continuous_neg.comp hKc).continuousOn
      refine ⟨-K z₀, ?_, fun z hz hz1 => hmin ⟨hz, hz1⟩⟩
      have hz₀0 : z₀ ≠ 0 := by
        rintro rfl
        simp [hTdef] at hz₀
      linarith [hFneg z₀ hz₀.1 hz₀0]
  refine ⟨κ / 2, half_pos hκ, fun z hz hz0 => ?_⟩
  have hGz := hG z (hFe.1 hz) hz0
  have h := hκF ((G z)⁻¹ • z) (hFe.2.1.2 z hz _ (inv_pos.2 hGz))
    (by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hGz.ne'])
  rw [map_smul, smul_eq_mul] at h
  have h' : κ * G z ≤ -K z := by
    have := mul_le_mul_of_nonneg_right h hGz.le
    rwa [neg_mul_eq_mul_neg, mul_comm (G z)⁻¹, mul_assoc, inv_mul_cancel₀ hGz.ne',
      mul_one] at this
  nlinarith

/-- A choice of one element in each set of a finite family `S` of rays, summed, is the same as a
choice of one element in each ray of a reindexing `v` of `S`. -/
theorem exists_sum_finset_iff_exists_sum {V : Type*} [AddCommGroup V] [Module ℝ V]
    {S : Finset (Set V)} {ι : Type*} [Fintype ι] (e : ι ≃ S) (v : ι → V)
    (hv : ∀ i, ray (v i) = e i) (p : V → Prop) :
    (∃ r : Set V → V, (∀ R ∈ S, r R ∈ R) ∧ p (∑ R ∈ S, r R)) ↔
      ∃ r : ι → V, (∀ i, r i ∈ ray (v i)) ∧ p (∑ i, r i) := by
  classical
  constructor
  · rintro ⟨r, hr, hp⟩
    refine ⟨fun i => r (e i), fun i => (hv i).symm ▸ hr _ (e i).2, ?_⟩
    rwa [← Finset.sum_coe_sort S r, ← e.sum_comp] at hp
  · rintro ⟨r, hr, hp⟩
    refine ⟨fun R => if h : R ∈ S then r (e.symm ⟨R, h⟩) else 0, fun R hR => ?_, ?_⟩
    · dsimp only
      rw [dif_pos hR]
      have := hr (e.symm ⟨R, hR⟩)
      rwa [hv, Equiv.apply_symm_apply] at this
    · rw [← Finset.sum_coe_sort S, ← e.sum_comp]
      exact (congrArg p (Finset.sum_congr rfl fun i _ => by simp)).mpr hp

/-- A cone `F` which is the sum of those of the rays `ℝ_{≥0} vᵢ` contained in it is the cone
spanned by any family `w` of vectors of `F` whose span contains each such `vᵢ`. -/
theorem eq_hull_of_eq_sum_rays {V : Type*} [AddCommGroup V] [Module ℝ V] {F : Set V}
    (hF : IsCone ℝ F) (hFadd : ∀ u ∈ F, ∀ v ∈ F, u + v ∈ F) {k : ℕ} {v : Fin k → V}
    (hFeq : F = {x | ∃ r : Fin k → V, (∀ i, r i ∈ ray (v i)) ∧
      (∀ i, ¬ ray (v i) ⊆ F → r i = 0) ∧ x = ∑ i, r i})
    {ι : Type*} (w : ι → V) (hwF : ∀ j, w j ∈ F)
    (hvw : ∀ i, ray (v i) ⊆ F → v i ∈ PointedCone.hull ℝ (Set.range w)) :
    F = PointedCone.hull ℝ (Set.range w) := by
  apply Set.Subset.antisymm
  · intro x hx
    rw [hFeq] at hx
    obtain ⟨r, hr, hr0, rfl⟩ := hx
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hi : ray (v i) ⊆ F
    · obtain ⟨c, hc, hci⟩ := hr i
      rw [← hci]
      exact Submodule.smul_mem _ (⟨c, hc⟩ : {c : ℝ // 0 ≤ c}) (hvw i hi)
    · rw [hr0 i hi]
      exact zero_mem _
  · obtain ⟨P, hP⟩ := (isCone_and_add_mem_iff F).1 ⟨hF, hFadd⟩
    have hle : PointedCone.hull ℝ (Set.range w) ≤ P := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨j, rfl⟩
      rw [hP]
      exact hwF j
    rw [← hP]
    exact SetLike.coe_subset_coe.2 hle

/-- Every ray in the finite set `S` of the abstract cone theorem is spanned by a lattice point
`ξ` with `K(ξ) < 0` and is an extremal face of `NE̅`. -/
theorem exists_generator_isExtremalFace_of_mem_negativeRationalRays (D : ConeDatum N)
    {R : Set (ℝ ⊗[ℤ] N)} (hR : R ∈ D.negativeRationalRays) :
    ∃ ξ : N, realOfRatForm N D.form ((1 : ℝ) ⊗ₜ[ℤ] ξ) < 0 ∧ R = ray ((1 : ℝ) ⊗ₜ[ℤ] ξ) ∧
      IsExtremalFace ℝ (D.cone : Set (ℝ ⊗[ℤ] N)) R := by
  let := moduleTopology ℝ (ℝ ⊗[ℤ] N)
  obtain ⟨h₁, h₂, h₃⟩ := moduleTopology_isTopologicalAddGroup_continuousSMul_t2Space (ℝ ⊗[ℤ] N)
  obtain ⟨ξ, hξ, hRξ⟩ := ConeDatum.exists_integral_generator D hR
  obtain ⟨-, -, -, L, hL, hRL⟩ := hR
  refine ⟨ξ, hξ, hRξ, ?_⟩
  rw [hRL]
  exact (isClosed_convex_isExtremalFace_faceOfNefForm (isCone_coe D.cone) D.cone.convex
    D.isClosed_cone hL).2.2

/-- **KM 3.3 Step 6, for a cone datum.** Let `(N_ℤ, NE̅, K, a)` be a cone datum and `F` a
`K`-negative extremal face of `NE̅`. Then `F = ℝ_{≥0} ξ₁ + ⋯ + ℝ_{≥0} ξ_m` for finitely many
`ξⱼ ∈ N_ℤ`, each spanning an extremal ray of `NE̅` with `K(ξⱼ) < 0`. -/
private theorem exists_eq_hull_of_isNegativeExtremalFace_coneDatum (D : ConeDatum N)
    {F : Set (ℝ ⊗[ℤ] N)}
    (hF : IsNegativeExtremalFace ℝ (D.cone : Set (ℝ ⊗[ℤ] N)) (realOfRatForm N D.form) F) :
    ∃ (m : ℕ) (ξ : Fin m → N),
      F = (PointedCone.hull ℝ (Set.range fun j => (1 : ℝ) ⊗ₜ[ℤ] ξ j) : Set (ℝ ⊗[ℤ] N)) ∧
      ∀ j, IsExtremalRay ℝ (D.cone : Set (ℝ ⊗[ℤ] N)) (ray ((1 : ℝ) ⊗ₜ[ℤ] ξ j)) ∧
        realOfRatForm N D.form ((1 : ℝ) ⊗ₜ[ℤ] ξ j) < 0 := by
  classical
  let := moduleTopology ℝ (ℝ ⊗[ℤ] N)
  obtain ⟨h₁, h₂, h₃⟩ := moduleTopology_isTopologicalAddGroup_continuousSMul_t2Space (ℝ ⊗[ℤ] N)
  set C : Set (ℝ ⊗[ℤ] N) := (D.cone : Set (ℝ ⊗[ℤ] N)) with hCdef
  set K := realOfRatForm N D.form
  have hCc : IsCone ℝ C := isCone_coe D.cone
  have hCv : Convex ℝ C := D.cone.convex
  have hCcl : IsClosed C := D.isClosed_cone
  obtain ⟨hFe, hFadd, hFneg⟩ := hF
  have hFv : Convex ℝ F := by
    obtain ⟨P, hP⟩ := (isCone_and_add_mem_iff F).1 ⟨hFe.2.1, hFadd⟩
    rw [← hP]
    exact P.convex
  obtain ⟨G, hG⟩ := exists_dual_pos_of_salient hCc hCv hCcl D.inter_neg_eq
  obtain ⟨ε, hε, hneg⟩ := exists_pos_add_mul_neg_of_isExtremalFace hCc hCcl hG hFe
    (IsExtremalFace.isClosed hCcl hFe hFv) hFneg
  obtain ⟨S, hS, hCsum⟩ := ConeDatum.cone_eq_nonneg_add_sum_rays D hG hε
  have hgen : ∀ R ∈ S, ∃ ξ : N, K ((1 : ℝ) ⊗ₜ[ℤ] ξ) < 0 ∧ R = ray ((1 : ℝ) ⊗ₜ[ℤ] ξ) ∧
      IsExtremalFace ℝ C R := fun R hR => by
    have : R ∈ (↑S : Set (Set (ℝ ⊗[ℤ] N))) := hR
    rw [hS] at this
    exact exists_generator_isExtremalFace_of_mem_negativeRationalRays D this.1
  choose! ξR hξR using hgen
  let e : Fin S.card ≃ S := S.equivFin.symm
  let v : Fin S.card → ℝ ⊗[ℤ] N := fun i => (1 : ℝ) ⊗ₜ[ℤ] ξR (e i)
  have hvR : ∀ i, ray (v i) = (e i : Set (ℝ ⊗[ℤ] N)) := fun i => ((hξR _ (e i).2).2.1).symm
  have hvC : ∀ i, ray (v i) ⊆ C := fun i => hvR i ▸ (hξR _ (e i).2).2.2.1
  set C' : Set (ℝ ⊗[ℤ] N) := {c | c ∈ C ∧ 0 ≤ K c + ε * G c}
  have hsum : C = {x | ∃ c ∈ C', ∃ r : Fin S.card → ℝ ⊗[ℤ] N, (∀ i, r i ∈ ray (v i)) ∧
      x = c + ∑ i, r i} := by
    rw [hCdef, hCsum]
    ext x
    constructor
    · rintro ⟨c, hc, hc', hr⟩
      exact ⟨c, ⟨hc, hc'⟩, (exists_sum_finset_iff_exists_sum e v hvR (x = c + ·)).1 hr⟩
    · rintro ⟨c, ⟨hc, hc'⟩, hr⟩
      exact ⟨c, hc, hc', (exists_sum_finset_iff_exists_sum e v hvR (x = c + ·)).2 hr⟩
  have hFC' : F ∩ C' = {0} := Set.eq_singleton_iff_unique_mem.2
    ⟨⟨hFe.2.1.1, hCc.1, by simp⟩, fun z ⟨hz, _, hz'⟩ => by
      by_contra hz0
      linarith [hneg z hz hz0]⟩
  have hFeq := IsExtremalFace.eq_sum_rays hCc hCv (fun c hc => hc.1) v hvC hsum hFe hFv hFC'
  let J := {i : Fin S.card // ray (v i) ⊆ F}
  let eJ : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  refine ⟨Fintype.card J, fun j => ξR (e (eJ.symm j)).1, eq_hull_of_eq_sum_rays hFe.2.1 hFadd hFeq
    _ (fun j => (eJ.symm j).2 ⟨1, zero_le_one, one_smul _ _⟩)
    fun i hi => Submodule.subset_span ⟨eJ ⟨i, hi⟩, by simp [v]⟩, fun j => ?_⟩
  obtain ⟨hξK, hξray, hξext⟩ := hξR _ (e (eJ.symm j).1).2
  refine ⟨⟨(by rwa [← hξray]), (1 : ℝ) ⊗ₜ[ℤ] ξR (e (eJ.symm j).1), fun h0 => ?_, rfl⟩, hξK⟩
  simp [h0] at hξK

end Abstract

end MMP.FourfoldProofs.Km3bNegativeFaceFinitelyGeneratedProof

open CategoryTheory AlgebraicGeometry

namespace MMP.Mori

open MMP.FourfoldProofs.Km3bNegativeFaceFinitelyGeneratedProof in
open scoped TensorProduct in
/-- **Negative extremal faces are finitely generated** (Kollár–Mori 3.3, Step 6). Let `X` be a
projective variety over an algebraically closed field `k` of characteristic zero, `(X, Δ)` a klt
pair with canonical divisor `K` and `Δ` effective, and `F` a `(K + Δ)`-negative extremal face of
`NE̅(X)`. Then there are finitely many `ξ₁, …, ξ_m ∈ N₁(X)_ℤ` with `F = ∑ ℝ_{≥0} ξⱼ` and each
`ℝ_{≥0} ξⱼ` a `(K + Δ)`-negative extremal ray of `NE̅(X)`. -/
@[mmp "lem_km3b_negative_face_finitely_generated"]
public theorem exists_eq_hull_of_isNegativeExtremalFace {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]
    [AlgebraicGeometry.IsProjectiveVariety k sX] {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    (hklt : IsKltPair sX n K Δ) (hΔ : Δ.IsEffective) {F : Set (NumericalCurveClasses sX)}
    (hF : IsNegativeExtremalFace ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX))
      (MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hklt.1.2.2) F) :
    ∃ (m : ℕ) (ξ : Fin m → numericalCurveLattice sX),
      F = (PointedCone.hull ℝ (Set.range fun j => (ξ j : NumericalCurveClasses sX)) :
        Set (NumericalCurveClasses sX)) ∧
      ∀ j, MMP.Fourfold.IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + Δ)
        {w | ∃ c : ℝ, 0 ≤ c ∧ c • (ξ j : NumericalCurveClasses sX) = w} := by
  classical
  set Kc := MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hklt.1.2.2
  by_cases hnef : QDivisor.IsNef k sX (Divisor.toQDivisor K + Δ)
  · refine ⟨0, Fin.elim0, ?_, fun j => j.elim0⟩
    rw [eq_singleton_zero_of_isNef sX hnef _ hF, Set.range_eq_empty, PointedCone.hull,
      Submodule.span_empty]
    rfl
  obtain ⟨a, ha, hCart⟩ := hklt.1.2.2.exists_pos
  obtain ⟨_, _, hbij, -, D, hDcone, hDform, -⟩ :=
    exists_coneDatum_numericalCurveLattice_of_isKltPair hklt hΔ hnef (a := (a : ℤ))
      (by exact_mod_cast ha) hCart
  set φ := LinearEquiv.ofBijective _ hbij with hφdef
  have hφ : ∀ (r : ℝ) (z : numericalCurveLattice sX),
      φ (r ⊗ₜ[ℤ] z) = r • (z : NumericalCurveClasses sX) := fun r z => by
    simp [hφdef, LinearMap.liftBaseChange_tmul]
  have hK : ∀ v, realOfRatForm _ D.form v = Kc (φ v) := by
    intro v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul r z =>
      rw [hφ, map_smul, smul_eq_mul, ← hDform z]
      simp [realOfRatForm, LinearMap.liftBaseChange_tmul]
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  have hC : (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) = φ '' D.cone := by
    rw [hDcone]
    exact (Set.image_preimage_eq _ φ.surjective).symm
  obtain ⟨m, ξ, hFeq, hray⟩ := exists_eq_hull_of_isNegativeExtremalFace_coneDatum D
    (isNegativeExtremalFace_preimage φ hC hK hF)
  have himage : ∀ j, φ '' MMP.Positivity.ray ((1 : ℝ) ⊗ₜ[ℤ] ξ j) =
      {w | ∃ c : ℝ, 0 ≤ c ∧ c • (ξ j : NumericalCurveClasses sX) = w} := fun j => by
    ext w
    simp [MMP.Positivity.ray, ← TensorProduct.smul_tmul', hφ]
  refine ⟨m, ξ, ?_, fun j => ⟨hklt.1.2.2, ?_, ?_⟩⟩
  · rw [← Set.image_preimage_eq F φ.surjective, hFeq]
    have := congrArg SetLike.coe
      (Submodule.map_span ((φ : _ →ₗ[ℝ] NumericalCurveClasses sX).restrictScalars
        {c : ℝ // 0 ≤ c}) (Set.range fun j => (1 : ℝ) ⊗ₜ[ℤ] ξ j))
    rw [Submodule.map_coe] at this
    refine this.trans ?_
    congr 2
    ext w
    simp [hφ]
  · rw [hC, ← himage]
    exact MMP.ProgramBaseChange.isExtremalRay_image φ (hray j).1
  · rintro _ ⟨c, hc, rfl⟩ hu0
    have hc0 : 0 < c := hc.lt_of_ne' fun h => hu0 (by rw [h, zero_smul])
    have h := (hray j).2
    rw [hK, hφ, one_smul] at h
    rw [map_smul, smul_eq_mul]
    exact mul_neg_of_pos_of_neg hc0 h

end MMP.Mori
