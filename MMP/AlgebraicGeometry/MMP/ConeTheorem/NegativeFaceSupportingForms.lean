module

public import MMP.AlgebraicGeometry.MMP.ConeTheorem.KltConeDatum
public import MMP.AlgebraicGeometry.MMP.ConeTheorem.AbstractConeTheorem
public import MMP.Analysis.Convex.Cone.FaceSupportingForms

@[expose] public section

section

/-!
# Supporting forms of a negative extremal face of the cone of curves

Let `(X, Δ)` be a klt pair, `X` projective over `k`, `Δ` effective and `K_X + Δ` not nef, and
`F` a `(K_X + Δ)`-negative extremal face of `NE̅(X)`. The linear forms on `N₁(X)` which are
nonnegative on `NE̅(X)` and whose zero set on `NE̅(X)` is `F` form a nonempty subset of
`⟨F⟩^⊥`, open in `⟨F⟩^⊥` and stable under positive scaling.

The proof transports the cone datum `(N₁(X)_ℤ, NE̅(X), K_X + Δ, (a(n+1))!)` to `N₁(X)` along
the canonical isomorphism `ℝ ⊗ N₁(X)_ℤ ≅ N₁(X)`, chooses `G > 0` on `NE̅(X) ∖ {0}` and
`0 < ε` with `K + εG < 0` on `F ∖ {0}` (by compactness of the slice `F ∩ {G = 1}`), writes
`NE̅(X) = NE̅(X)_{K+εG≥0} + R₁ + ⋯ + R_k` by the abstract cone theorem, and applies
`MMP.Positivity.IsExtremalFace.supportingForms_nonempty_isOpen`.

## Implementation notes

The positive form `G` is any form positive on `NE̅(X) ∖ {0}`, which exists because `NE̅(X)` is
a closed cone containing no line (`MMP.Positivity.exists_dual_pos_of_salient`); the source takes
`G = (H · _)` for an ample `H`. All topological statements on `N₁(X)` are for its canonical
topology as a finite-dimensional real vector space.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 3.3 Step 6
-/

open CategoryTheory AlgebraicGeometry TensorProduct MMP.Mori MMP.Positivity

namespace MMP.FourfoldProofs.Km3bNegativeFaceSupportingConeProof

/-- If `G` is positive and `K` negative on the nonzero elements of a closed cone `F`, then
`K + εG` is still negative on `F ∖ {0}` for some `ε > 0`: `K` attains a negative maximum on the
compact slice `F ∩ {G = 1}`. -/
private theorem exists_pos_add_mul_neg {V : Type*} [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V]
    [FiniteDimensional ℝ V] {F : Set V} (hF : IsCone ℝ F) (hFcl : IsClosed F)
    {G K : Module.Dual ℝ V} (hG : ∀ z ∈ F, z ≠ 0 → 0 < G z) (hK : ∀ z ∈ F, z ≠ 0 → K z < 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ F, z ≠ 0 → K z + ε * G z < 0 := by
  set S := {z | z ∈ F ∧ G z = 1}
  have hSmem : ∀ z ∈ F, z ≠ 0 → (G z)⁻¹ • z ∈ S := fun z hzF hz0 => by
    have hGz := hG z hzF hz0
    exact ⟨hF.2 z hzF _ (inv_pos.2 hGz), by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hGz.ne']⟩
  have hScpt : IsCompact S :=
    (isCompact_slice hF hFcl hG 1).of_isClosed_subset
      (hFcl.inter (isClosed_eq (LinearMap.continuous_of_finiteDimensional G) continuous_const))
      fun z hz => ⟨hz.1, hz.2.le⟩
  rcases S.eq_empty_or_nonempty with hS | hS
  · exact ⟨1, one_pos, fun z hzF hz0 => by simpa [hS] using hSmem z hzF hz0⟩
  obtain ⟨z₀, hz₀, hmax⟩ :=
    hScpt.exists_isMaxOn hS (LinearMap.continuous_of_finiteDimensional K).continuousOn
  have hκ : K z₀ < 0 := hK z₀ hz₀.1 fun h => by simp [S, h] at hz₀
  refine ⟨-K z₀ / 2, by linarith, fun z hzF hz0 => ?_⟩
  have hGz := hG z hzF hz0
  have h : K ((G z)⁻¹ • z) ≤ K z₀ := hmax (hSmem z hzF hz0)
  rw [map_smul, smul_eq_mul, inv_mul_le_iff₀ hGz] at h
  nlinarith [mul_pos hGz (neg_pos.2 hκ)]

/-- The abstract cone theorem `MMP.Positivity.ConeDatum.cone_eq_nonneg_add_sum_rays`, carried
along a linear isomorphism `ψ : ℝ ⊗ N ≅ V`: for `G > 0` on `C ∖ {0}` and `ε > 0`,
`C = C_{K+εG≥0} + R₁ + ⋯ + R_k` for finitely many rays `Rᵢ ⊆ C`. -/
private theorem exists_rays_cone_eq_nonneg_add_sum {N : Type} [AddCommGroup N] [Module.Free ℤ N]
    [Module.Finite ℤ N] {V : Type*} [AddCommGroup V] [Module ℝ V] (D : ConeDatum N)
    (ψ : ℝ ⊗[ℤ] N ≃ₗ[ℝ] V) (C : PointedCone ℝ V)
    (hC : ψ ⁻¹' (C : Set V) = (D.cone : Set (ℝ ⊗[ℤ] N))) (K : Module.Dual ℝ V)
    (hK : ∀ w, realOfRatForm N D.form w = K (ψ w)) {G : Module.Dual ℝ V}
    (hG : ∀ z ∈ C, z ≠ 0 → 0 < G z) {ε : ℝ} (hε : 0 < ε) :
    ∃ (k : ℕ) (v : Fin k → V), (∀ i, ray (v i) ⊆ (C : Set V)) ∧
      (C : Set V) = {x | ∃ c ∈ {c | c ∈ (C : Set V) ∧ 0 ≤ K c + ε * G c},
        ∃ r : Fin k → V, (∀ i, r i ∈ ray (v i)) ∧ x = c + ∑ i, r i} := by
  classical
  have hCeq : (C : Set V) = ψ.symm ⁻¹' (D.cone : Set (ℝ ⊗[ℤ] N)) := by
    rw [← hC]; ext x; simp
  let G' : Module.Dual ℝ (ℝ ⊗[ℤ] N) := G ∘ₗ ψ.toLinearMap
  have hG' : ∀ z ∈ D.cone, z ≠ 0 → 0 < G' z := fun z hz hz0 =>
    hG (ψ z) (show ψ z ∈ (C : Set V) by rw [hCeq]; simpa using hz) (by simpa using hz0)
  obtain ⟨S, hS, hcone⟩ := ConeDatum.cone_eq_nonneg_add_sum_rays D hG' hε
  have hray : ∀ R : S, ∃ ξ : ℝ ⊗[ℤ] N, (R : Set (ℝ ⊗[ℤ] N)) = {w | ∃ c : ℝ, 0 ≤ c ∧ c • ξ = w} ∧
      (R : Set (ℝ ⊗[ℤ] N)) ⊆ D.cone := by
    intro R
    have hR : (R : Set (ℝ ⊗[ℤ] N)) ∈ (↑S : Set (Set (ℝ ⊗[ℤ] N))) := R.2
    rw [hS] at hR
    obtain ⟨⟨ξ, -, hRξ, L, -, hRL⟩, -⟩ := hR
    exact ⟨ξ, hRξ, hRL ▸ fun z hz => hz.1⟩
  choose ξ hξ hξC using hray
  let e : Fin S.card ≃ S := S.equivFin.symm
  let v : Fin S.card → V := fun i => ψ (ξ (e i))
  have hvC : ∀ i, ray (v i) ⊆ (C : Set V) := by
    rintro i _ ⟨c, hc, rfl⟩
    have hm : c • ξ (e i) ∈ (e i : Set (ℝ ⊗[ℤ] N)) := by rw [hξ]; exact ⟨c, hc, rfl⟩
    rw [hCeq]
    simpa [v] using hξC _ hm
  refine ⟨S.card, v, hvC, Set.Subset.antisymm (fun x hx => ?_) ?_⟩
  · rw [hCeq, Set.mem_preimage, hcone] at hx
    obtain ⟨c, hc, hc0, r, hr, hxr⟩ := hx
    refine ⟨ψ c, ⟨by simpa [hCeq] using hc, by simpa [hK, G'] using hc0⟩,
      fun i => ψ (r (e i)), fun i => ?_, ?_⟩
    · obtain ⟨t, ht, htr⟩ : r (e i) ∈ {w | ∃ c : ℝ, 0 ≤ c ∧ c • ξ (e i) = w} :=
        hξ (e i) ▸ hr _ (e i).2
      exact ⟨t, ht, show t • ψ (ξ (e i)) = ψ (r (e i)) by rw [← htr, map_smul]⟩
    · rw [← ψ.apply_symm_apply x, hxr, map_add, map_sum, ← Finset.sum_coe_sort S,
        ← e.sum_comp (fun R => ψ (r R))]
  · rintro _ ⟨c, hc, r, hr, rfl⟩
    exact C.add_mem hc.1 (C.sum_mem fun i _ => hvC i (hr i))

/-- The abstract form of the statement: a cone `C ⊆ V` carried by a linear isomorphism
`ψ : ℝ ⊗ N ≅ V` onto the cone of a cone datum, with form `K ∘ ψ`. -/
private theorem supportingForms_of_coneDatum {N : Type} [AddCommGroup N] [Module.Free ℤ N]
    [Module.Finite ℤ N] {V : Type*} [AddCommGroup V] [Module ℝ V] (D : ConeDatum N)
    (ψ : ℝ ⊗[ℤ] N ≃ₗ[ℝ] V) (C : PointedCone ℝ V)
    (hC : ψ ⁻¹' (C : Set V) = (D.cone : Set (ℝ ⊗[ℤ] N))) (K : Module.Dual ℝ V)
    (hK : ∀ w, realOfRatForm N D.form w = K (ψ w)) {F : Set V}
    (hF : IsNegativeExtremalFace ℝ (C : Set V) K F) :
    {l : Module.Dual ℝ V | (∀ z ∈ C, 0 ≤ l z) ∧ {z | z ∈ C ∧ l z = 0} = F}.Nonempty ∧
      {l : Module.Dual ℝ V | (∀ z ∈ C, 0 ≤ l z) ∧ {z | z ∈ C ∧ l z = 0} = F} ⊆
        (Submodule.span ℝ F).dualAnnihilator ∧
      @IsOpen _ (moduleTopology ℝ (Submodule.span ℝ F).dualAnnihilator)
        {μ : (Submodule.span ℝ F).dualAnnihilator |
          (∀ z ∈ C, 0 ≤ (μ : Module.Dual ℝ V) z) ∧
            {z | z ∈ C ∧ (μ : Module.Dual ℝ V) z = 0} = F} ∧
      ∀ l : Module.Dual ℝ V, (∀ z ∈ C, 0 ≤ l z) → {z | z ∈ C ∧ l z = 0} = F →
        ∀ t : ℝ, 0 < t → (∀ z ∈ C, 0 ≤ (t • l) z) ∧ {z | z ∈ C ∧ (t • l) z = 0} = F := by
  classical
  haveI : FiniteDimensional ℝ V := LinearEquiv.finiteDimensional ψ
  letI : TopologicalSpace (ℝ ⊗[ℤ] N) := moduleTopology ℝ _
  haveI : IsModuleTopology ℝ (ℝ ⊗[ℤ] N) := ⟨rfl⟩
  letI : TopologicalSpace V := moduleTopology ℝ V
  haveI : IsModuleTopology ℝ V := ⟨rfl⟩
  obtain ⟨h₁, h₂, h₃⟩ := moduleTopology_isTopologicalAddGroup_continuousSMul_t2Space V
  obtain ⟨h₄, h₅, h₆⟩ := moduleTopology_isTopologicalAddGroup_continuousSMul_t2Space (ℝ ⊗[ℤ] N)
  have hψs : Continuous ψ.symm := IsModuleTopology.continuous_of_linearMap ψ.symm.toLinearMap
  have hCeq : (C : Set V) = ψ.symm ⁻¹' (D.cone : Set (ℝ ⊗[ℤ] N)) := by
    rw [← hC]; ext x; simp
  have hCcl : IsClosed (C : Set V) := hCeq ▸ D.isClosed_cone.preimage hψs
  have hCs : (C : Set V) ∩ -(C : Set V) = {0} := by
    have hneg : -(C : Set V) = ψ.symm ⁻¹' (-(D.cone : Set (ℝ ⊗[ℤ] N))) := by
      rw [hCeq]; ext; simp
    rw [hneg, hCeq, ← Set.preimage_inter, D.inter_neg_eq]
    ext; simp
  obtain ⟨G, hG⟩ := exists_dual_pos_of_salient (isCone_coe C) C.convex hCcl hCs
  obtain ⟨hFext, hFadd, hFneg⟩ := hF
  have hFc : Convex ℝ F := by
    obtain ⟨P, hP⟩ := (isCone_and_add_mem_iff F).1 ⟨hFext.2.1, hFadd⟩
    exact hP ▸ P.convex
  have hFcl : IsClosed F := MMP.Positivity.IsExtremalFace.isClosed hCcl hFext hFc
  obtain ⟨ε, hε, hεF⟩ := exists_pos_add_mul_neg hFext.2.1 hFcl
    (fun z hz => hG z (hFext.1 hz)) hFneg
  obtain ⟨k, v, hvC, hsum⟩ := exists_rays_cone_eq_nonneg_add_sum D ψ C hC K hK hG hε
  set C' : Set V := {c | c ∈ (C : Set V) ∧ 0 ≤ K c + ε * G c}
  have hC' : IsCone ℝ C' := ⟨⟨C.zero_mem, by simp⟩, fun x hx c hc => ⟨C.smul_mem hc.le hx.1, by
    simp only [map_smul, smul_eq_mul]
    nlinarith [mul_nonneg hc.le hx.2]⟩⟩
  have hC'c : Convex ℝ C' :=
    C.convex.inter (convex_halfSpace_ge (K + ε • G).isLinear 0)
  have hC'cl : IsClosed C' :=
    hCcl.inter (isClosed_le continuous_const ((LinearMap.continuous_of_finiteDimensional K).add
      (continuous_const.mul (LinearMap.continuous_of_finiteDimensional G))))
  have hFC' : F ∩ C' = {0} :=
    Set.eq_singleton_iff_unique_mem.2 ⟨⟨hFext.2.1.1, C.zero_mem, by simp⟩,
      fun z ⟨hzF, hzC'⟩ => by_contra fun hz0 => by linarith [hεF z hzF hz0, hzC'.2]⟩
  exact IsExtremalFace.supportingForms_nonempty_isOpen (isCone_coe C) C.convex hCcl hCs hC' hC'c
    hC'cl (fun z hz => hz.1) v hvC hsum hFext hFc hFC'

end MMP.FourfoldProofs.Km3bNegativeFaceSupportingConeProof

end

section

/-!
# Supporting forms of a negative extremal face of the cone of curves

Let `X` be a projective variety over an algebraically closed field `k` of characteristic zero
and `(X, Δ)` a klt pair with `Δ` effective and `K_X + Δ` not nef. For a `(K_X + Δ)`-negative
extremal face `F` of the closed cone of curves `NE̅(X) ⊆ N₁(X)`, the linear forms `λ` on `N₁(X)`
which are nonnegative on `NE̅(X)` and whose zero set on `NE̅(X)` is exactly `F` form a nonempty
subset of the annihilator `⟨F⟩^⊥` of the span of `F`, open in `⟨F⟩^⊥` and stable under
multiplication by positive reals.

## Main results

* `MMP.Mori.supportingForms_nonempty_isOpen_of_isNegativeExtremalFace`: the statement above.

## Implementation notes

The annihilator `⟨F⟩^⊥` is `(Submodule.span ℝ F).dualAnnihilator ⊆ Module.Dual ℝ N₁(X)`, and
openness in it is for its canonical topology `moduleTopology ℝ`, as in the abstract cone
statement `MMP.Positivity.IsExtremalFace.supportingForms_nonempty_isOpen`. The form
`z ↦ ((K_X + Δ) · z)` is `MMP.Fourfold.QDivisor.curveForm` of `K_X + Δ`, which is `ℚ`-Cartier
by the pair condition.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 3.3 Step 6
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace MMP.Mori

/-- **Supporting forms of a negative extremal face** (Kollár–Mori 3.3, Step 6). Let `X` be a
projective variety over an algebraically closed field `k` of characteristic zero, `(X, Δ)` a
klt pair with canonical divisor `K`, `Δ` effective and `K + Δ` not nef, and `F` a
`(K + Δ)`-negative extremal face of `NE̅(X)`. Then the set of linear forms `λ` on `N₁(X)` with
`λ ≥ 0` on `NE̅(X)` and `{z ∈ NE̅(X) | λ z = 0} = F` is nonempty, contained in
`(span F)^⊥`, open in `(span F)^⊥`, and stable under multiplication by positive reals. -/
@[mmp "lem_km3b_negative_face_supporting_cone"]
public theorem supportingForms_nonempty_isOpen_of_isNegativeExtremalFace {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]
    [AlgebraicGeometry.IsProjectiveVariety k sX] {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    (hklt : IsKltPair sX n K Δ) (hΔ : Δ.IsEffective)
    (hnef : ¬ QDivisor.IsNef k sX (Divisor.toQDivisor K + Δ))
    {F : Set (NumericalCurveClasses sX)}
    (hF : IsNegativeExtremalFace ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX))
      (MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hklt.1.2.2) F) :
    {l : Module.Dual ℝ (NumericalCurveClasses sX) |
        (∀ z ∈ closedConeOfCurves sX, 0 ≤ l z) ∧
          {z | z ∈ closedConeOfCurves sX ∧ l z = 0} = F}.Nonempty ∧
      {l : Module.Dual ℝ (NumericalCurveClasses sX) |
          (∀ z ∈ closedConeOfCurves sX, 0 ≤ l z) ∧
            {z | z ∈ closedConeOfCurves sX ∧ l z = 0} = F} ⊆
        (Submodule.span ℝ F).dualAnnihilator ∧
      @IsOpen _ (moduleTopology ℝ (Submodule.span ℝ F).dualAnnihilator)
        {μ : (Submodule.span ℝ F).dualAnnihilator |
          (∀ z ∈ closedConeOfCurves sX,
              0 ≤ (μ : Module.Dual ℝ (NumericalCurveClasses sX)) z) ∧
            {z | z ∈ closedConeOfCurves sX ∧
              (μ : Module.Dual ℝ (NumericalCurveClasses sX)) z = 0} = F} ∧
      ∀ l : Module.Dual ℝ (NumericalCurveClasses sX),
        (∀ z ∈ closedConeOfCurves sX, 0 ≤ l z) →
          {z | z ∈ closedConeOfCurves sX ∧ l z = 0} = F →
        ∀ t : ℝ, 0 < t → (∀ z ∈ closedConeOfCurves sX, 0 ≤ (t • l) z) ∧
          {z | z ∈ closedConeOfCurves sX ∧ (t • l) z = 0} = F := by
  obtain ⟨m, hm, hCart⟩ := hklt.1.2.2.exists_pos
  obtain ⟨_, _, hbij, -, D, hDcone, hDform, -⟩ :=
    exists_coneDatum_numericalCurveLattice_of_isKltPair hklt hΔ hnef (a := (m : ℤ))
      (by exact_mod_cast hm) hCart
  refine MMP.FourfoldProofs.Km3bNegativeFaceSupportingConeProof.supportingForms_of_coneDatum D
    (LinearEquiv.ofBijective _ hbij) _ hDcone.symm _ (fun w => ?_) hF
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul r z =>
    simp [MMP.Positivity.realOfRatForm_tmul, LinearEquiv.ofBijective_apply,
      LinearMap.liftBaseChange_tmul, hDform]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

end MMP.Mori

end
