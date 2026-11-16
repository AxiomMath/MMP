module

public import MMP.AlgebraicTopology.ComplexProjectiveSpace.Cohomology
public import MMP.AlgebraicTopology.ThomClass.Gysin
public import MMP.AlgebraicTopology.ThomClass.Natural
public import Mathlib.Topology.VectorBundle.Basic

/-!
# The tautological line bundle on `ℙⁿ(ℂ)` and its Euler class

On complex projective space `ℙⁿ(ℂ)`, realized as the space of rank-one orthogonal projections
`P = v v^* / (v^* v)` of `ℂⁿ⁺¹`, the tautological line bundle `O(-1)` has fibre the line `ℂ v`.
Over the chart `Uᵢ = {P i i ≠ 0}` the line is spanned by `vᵢ = (P k i / P i i)_k`, and since
`P` has rank one, `vᵢ = (P j i / P i i) vⱼ`; these are the coordinate changes of a vector bundle
core.

The total space minus the zero section is `ℂⁿ⁺¹ - 0`, by `⟨P, λ vᵢ⟩ ↦ λ vᵢ` (for `n = 1` this
is the Hopf fibration `S³ → S²` up to homotopy). Since `H¹(ℂⁿ⁺¹ - 0; ℚ) = 0` for `n ≥ 1`, the
sequence of the pair `(E, E - 0)` shows that the Thom class `u ≠ 0` stays nonzero in `H²(E)`,
and `E` retracts onto its zero section, so the Euler class `0^* u` is nonzero in `H²(ℙⁿ(ℂ); ℚ)`.

## Main definitions

* `MMP.Topology.tautologicalCore`, `MMP.Topology.TautologicalBundle`: the tautological line
  bundle.
* `MMP.Topology.tautologicalComplHomeomorph`: its total space minus the zero section is
  `ℂⁿ⁺¹ - 0`.
* `MMP.Topology.zeroSectionHomotopy`: the fibrewise scaling homotopy from `0 ∘ π` to the
  identity of the total space of a line bundle.

## Main results

* `MMP.Topology.eulerClass_ne_zero_of_subsingleton`: a complex line bundle with `H¹(E - 0) = 0`
  over a nonempty space has nonzero rational Euler class.
* `MMP.Topology.subsingleton_cohomology_complexSpace_compl_zero`: `H¹(ℂᵐ⁺¹ - 0; ℚ) = 0`, `m ≥ 1`.
* `MMP.Topology.eulerClass_tautologicalBundle_ne_zero`: `e(O(-1)) ≠ 0` in `H²(ℙⁿ(ℂ); ℚ)`, `n ≥ 1`.

## Implementation notes

The Euler class is `MMP.Topology.eulerClass`, the pull-back of the Thom class along the zero
section. The preferred chart at `P` is the first index with `P i i ≠ 0`.

## References

* [J. Milnor, J. Stasheff, *Characteristic classes*][milnorstasheff1974], §§9–12.
-/

@[expose] public noncomputable section

open Bundle ComplexConjugate Topology Set

namespace MMP.Topology

variable {n : ℕ}

section RankOne

/-- The entries of a rank-one projection satisfy `P a b · P c d = P a d · P c b`. -/
lemma lineProjections_mul_mul_eq {P : Fin (n + 1) → Fin (n + 1) → ℂ} (hP : P ∈ lineProjections n)
    (a b c d : Fin (n + 1)) : P a b * P c d = P a d * P c b := by
  obtain ⟨v, hv, rfl⟩ := hP
  have h := sum_mul_conj_ne_zero hv
  simp only [lineProjection]
  field_simp

/-- A line projection is Hermitian: `P b a = conj (P a b)`. -/
lemma lineProjections_apply_swap {P : Fin (n + 1) → Fin (n + 1) → ℂ} (hP : P ∈ lineProjections n)
    (a b : Fin (n + 1)) : P b a = conj (P a b) := by
  obtain ⟨v, hv, rfl⟩ := hP
  simp only [lineProjection, map_div₀, map_mul, Complex.conj_conj, sum_mul_conj_eq_ofReal,
    Complex.conj_ofReal]
  ring

/-- Some diagonal entry of a line projection is nonzero. -/
lemma lineProjections_exists_diag_ne_zero {P : Fin (n + 1) → Fin (n + 1) → ℂ}
    (hP : P ∈ lineProjections n) : ∃ i, P i i ≠ 0 := by
  obtain ⟨v, hv, rfl⟩ := hP
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
  exact ⟨i, div_ne_zero (mul_ne_zero hi ((map_ne_zero _).2 hi)) (sum_mul_conj_ne_zero hv)⟩

end RankOne

section Core

/-- The indices of the nonzero diagonal entries of a line projection. -/
def diagSupport (P : lineProjections n) : Finset (Fin (n + 1)) :=
  Finset.univ.filter fun i ↦ P.1 i i ≠ 0

/-- `i` lies in `diagSupport P` iff the diagonal entry `P i i` is nonzero. -/
@[simp] lemma mem_diagSupport {P : lineProjections n} {i : Fin (n + 1)} :
    i ∈ diagSupport P ↔ P.1 i i ≠ 0 := by
  simp [diagSupport]

/-- Every line projection has a nonzero diagonal entry, so `diagSupport P` is nonempty. -/
lemma diagSupport_nonempty (P : lineProjections n) : (diagSupport P).Nonempty := by
  obtain ⟨i, hi⟩ := lineProjections_exists_diag_ne_zero P.2
  exact ⟨i, mem_diagSupport.2 hi⟩

/-- The preferred chart at a point `P` of `ℙⁿ(ℂ)`: the first `i` with `P i i ≠ 0`. -/
def chartIndex (P : lineProjections n) : Fin (n + 1) :=
  (diagSupport P).min' (diagSupport_nonempty P)

/-- The diagonal entry of `P` at its preferred chart index is nonzero. -/
lemma chartIndex_diag_ne_zero (P : lineProjections n) :
    P.1 (chartIndex P) (chartIndex P) ≠ 0 :=
  mem_diagSupport.1 (Finset.min'_mem _ (diagSupport_nonempty P))

variable (n) in
/-- **The tautological line bundle on `ℙⁿ(ℂ)`**, as a vector bundle core. Over the chart
`Uᵢ = {P | P i i ≠ 0}` the line of `P` is spanned by its `i`-th column normalised to have `i`-th
entry `1`, `vᵢ = (P k i / P i i)_k`, and a vector `λ vᵢ` has coordinate `λ`. Since
`vᵢ = (P j i / P i i) vⱼ`, the coordinate changes are multiplication by `P j i / P i i`. -/
def tautologicalCore : VectorBundleCore ℂ (lineProjections n) ℂ (Fin (n + 1)) where
  baseSet i := {P | P.1 i i ≠ 0}
  isOpen_baseSet i :=
    isOpen_compl_singleton.preimage (continuous_entry continuous_subtype_val i i)
  indexAt := chartIndex
  mem_baseSet_at := chartIndex_diag_ne_zero
  coordChange i j P := (P.1 j i / P.1 i i) • ContinuousLinearMap.id ℂ ℂ
  coordChange_self i P hP v := by
    simp [div_self (show P.1 i i ≠ 0 from hP)]
  continuousOn_coordChange i j :=
    (((continuous_entry continuous_subtype_val j i).continuousOn).div
      (continuous_entry continuous_subtype_val i i).continuousOn
      (fun P hP ↦ hP.1)).smul continuousOn_const
  coordChange_comp i j k P hP v := by
    obtain ⟨⟨hi, hj⟩, -⟩ := hP
    change P.1 i i ≠ 0 at hi
    change P.1 j j ≠ 0 at hj
    have h := lineProjections_mul_mul_eq P.2 k j j i
    simp only [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.id_apply,
      smul_eq_mul]
    field_simp
    rw [h]
    ring

variable (n) in
/-- The fibres of the tautological line bundle on `ℙⁿ(ℂ)`. -/
abbrev TautologicalBundle : lineProjections n → Type := (tautologicalCore n).Fiber

/-- The coordinate change of `tautologicalCore n` from chart `i` to chart `j` at `P` is
multiplication by `P j i / P i i`. -/
lemma tautologicalCore_coordChange_apply (i j : Fin (n + 1)) (P : lineProjections n) (v : ℂ) :
    (tautologicalCore n).coordChange i j P v = P.1 j i / P.1 i i * v := by
  simp [tautologicalCore]

end Core

section EulerNonzero

open CategoryTheory MMP.cohomologyWithSupports MMP.SingularCochain

variable {B : Type} [TopologicalSpace B] {E : B → Type} [∀ b, AddCommGroup (E b)]
  [∀ b, Module ℂ (E b)] [TopologicalSpace (TotalSpace ℂ E)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle ℂ E] [_root_.VectorBundle ℂ ℂ E]

variable (E) in
/-- The fibrewise scaling homotopy `(t, p) ↦ t p` from `0 ∘ π` to the identity of the total space
of a complex line bundle. -/
def zeroSectionHomotopy :
    TopCat.Homotopy (bundleProj ℂ E ≫ bundleZeroSection ℂ E) (𝟙 (TopCat.of (TotalSpace ℂ E))) where
  toFun q := ⟨q.2.proj, ((q.1 : ℝ) : ℂ) • q.2.2⟩
  continuous_toFun := by
    refine continuous_iff_continuousAt.2 fun q₀ ↦ ?_
    rw [FiberBundle.continuousAt_totalSpace]
    refine ⟨((FiberBundle.continuous_proj ℂ E).comp continuous_snd).continuousAt, ?_⟩
    set e := trivializationAt ℂ E q₀.2.proj
    have hsrc : q₀.2 ∈ e.source := e.mem_source.2 (mem_baseSet_trivializationAt ℂ E _)
    have hc : ContinuousAt (fun q : unitInterval × TotalSpace ℂ E ↦
        ((q.1 : ℝ) : ℂ) • (e q.2).2) q₀ :=
      ((Complex.continuous_ofReal.comp
        (continuous_subtype_val.comp continuous_fst)).continuousAt).smul
        (continuous_snd.continuousAt.comp ((e.continuousOn.continuousAt
          (e.open_source.mem_nhds hsrc)).comp continuous_snd.continuousAt))
    refine hc.congr ?_
    have hU : ∀ᶠ q in 𝓝 q₀, q.2.proj ∈ e.baseSet :=
      ((FiberBundle.continuous_proj ℂ E).comp continuous_snd).continuousAt.preimage_mem_nhds
        (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt ℂ E _))
    filter_upwards [hU] with q hq
    change ((q.1 : ℝ) : ℂ) • (e q.2).2 = (e ⟨q.2.proj, ((q.1 : ℝ) : ℂ) • q.2.2⟩).2
    rw [← e.continuousLinearMapAt_apply_of_mem (R := ℂ) hq (((q.1 : ℝ) : ℂ) • q.2.2), map_smul,
      e.continuousLinearMapAt_apply_of_mem (R := ℂ) hq]
  map_zero_left q := by
    change (⟨q.proj, ((0 : ℝ) : ℂ) • q.2⟩ : TotalSpace ℂ E) = ⟨q.proj, 0⟩
    rw [Complex.ofReal_zero, zero_smul]
  map_one_left q := by
    change (⟨q.proj, ((1 : ℝ) : ℂ) • q.2⟩ : TotalSpace ℂ E) = q
    rw [Complex.ofReal_one, one_smul]

/-- The Thom class of a complex line bundle on a nonempty space is nonzero. -/
theorem thomClass_ne_zero [Nonempty B] : ThomClass.thomClass ℚ ℂ E ≠ 0 := by
  intro h
  obtain ⟨x⟩ := ‹Nonempty B›
  let ψ₀ : E x ≃L[ℂ] ℂ := (trivializationAt ℂ E x).continuousLinearEquivAt ℂ x
    (mem_baseSet_trivializationAt ℂ E x)
  let φ : (Fin (Module.finrank ℂ ℂ) → ℂ) ≃L[ℂ] ℂ :=
    (LinearEquiv.ofFinrankEq _ _ (by simp)).toContinuousLinearEquiv
  obtain ⟨v, hv⟩ := ThomClass.exists_isOrientedSimplexAroundZero
    (ThomClass.complexOrientationBasis (Module.finrank ℂ ℂ))
  have := ThomClass.isThomClass_thomClass (R := ℚ) ℂ E x (φ.trans ψ₀.symm) v hv
  rw [h, map_zero, map_zero] at this
  exact zero_ne_one this

/-- If `H^m(Y - X) = 0`, then `H^{m+1}(Y, Y - X) → H^{m+1}(Y)` is injective. -/
theorem injective_toCohomology_of_subsingleton {Y : TopCat.{0}} (X : Set Y) {j : ℤ} {m : ℕ}
    (hj : j = ((m + 1 : ℕ) : ℤ))
    (h : Subsingleton (cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) (TopCat.of ↥Xᶜ) univ m)) :
    Function.Injective (toCohomology ℚ (ModuleCat.of ℚ ℚ) Y X j).hom := by
  subst hj
  exact injective_of_exact_of_subsingleton (f := (delta ℚ Y X m).toAddMonoidHom)
    (g := (toCohomology ℚ (ModuleCat.of ℚ ℚ) Y X (m + 1 : ℕ)).hom.toAddMonoidHom)
    (exact_delta_toCohomology ℚ Y X m)

/-- **The Euler class of a complex line bundle is nonzero** when the base is nonempty and the
complement of the zero section has vanishing first rational cohomology. -/
theorem eulerClass_ne_zero_of_subsingleton [Nonempty B]
    (h : Subsingleton (cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.of ↥(range (zeroSection ℂ E))ᶜ) univ (1 : ℕ))) :
    eulerClass ℚ ℂ E ≠ 0 := by
  have hj : ((2 * Module.finrank ℂ ℂ : ℕ) : ℤ) = ((1 + 1 : ℕ) : ℤ) := by simp
  have h1 := injective_toCohomology_of_subsingleton (Y := TopCat.of (TotalSpace ℂ E))
    (range (zeroSection ℂ E)) hj h
  let I := cohomologyIsoOfHomotopy ℚ (bundleZeroSection ℂ E) (bundleProj ℂ E)
    (bundleZeroSection_comp_bundleProj ℂ E) (zeroSectionHomotopy E)
    ((2 * Module.finrank ℂ ℂ : ℕ) : ℤ)
  have h2 : Function.Injective I.hom.hom := I.toLinearEquiv.injective
  have he : eulerClass ℚ ℂ E = I.hom.hom ((toCohomology ℚ (ModuleCat.of ℚ ℚ) _ _ _).hom
      (ThomClass.thomClass ℚ ℂ E)) := by
    rw [eulerClass, toCohomology, cohomologyWithSupports.forget]
    symm
    change (relativeSingularCohomology.map ℚ _ (bundleZeroSection ℂ E) _ _).hom
      ((relativeSingularCohomology.map ℚ _ (𝟙 _) _ _).hom _) = _
    have hu : ∀ {Z : Type} (S : Set Z), (univ : Set Z)ᶜ ⊆ S := fun _ x hx ↦ (hx (mem_univ x)).elim
    exact (relativeSingularCohomology_map_map_apply ℚ (bundleZeroSection ℂ E) (𝟙 _)
      (A'' := univᶜ) (A' := univᶜ) (A := (range (zeroSection ℂ E))ᶜ) (hu _)
      (Set.compl_subset_compl.mpr (subset_univ _)) (hu _) _ _).trans
      (congrArg (fun m ↦ (ModuleCat.Hom.hom m) (ThomClass.thomClass ℚ ℂ E))
        (relativeSingularCohomology_map_congr ℚ (Category.comp_id (bundleZeroSection ℂ E))
          (hu _) (hu _) _))
  rw [he, ne_eq, map_eq_zero_iff _ h2, map_eq_zero_iff _ h1]
  exact thomClass_ne_zero

end EulerNonzero

section PuncturedSpace

open CategoryTheory MMP.cohomologyWithSupports

/-- `ℂᵐ⁺¹` and `ℝ^{2(m+1)}` have the same real dimension. -/
theorem finrank_real_complexSpace (m : ℕ) :
    Module.finrank ℝ (Fin (m + 1) → ℂ) = Module.finrank ℝ (Fin (2 * (m + 1)) → ℝ) := by
  rw [Module.finrank_pi_fintype]
  simp [Complex.finrank_real_complex]
  ring

/-- The rational cohomology of `ℂᵐ⁺¹` vanishes in positive degrees. -/
theorem subsingleton_cohomology_complexSpace (m k : ℕ) :
    Subsingleton (cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (Fin (m + 1) → ℂ))
      univ (k + 1 : ℕ)) :=
  subsingleton_cohomology_of_homeomorph_euclidean ℚ
    (ContinuousLinearEquiv.ofFinrankEq (finrank_real_complexSpace m)).toHomeomorph k

/-- `H²(ℂᵐ⁺¹, ℂᵐ⁺¹ - 0; ℚ) = 0` for `m ≥ 1`: `ℂᵐ⁺¹ ≅ ℝ^{2m+2}` with `2 ≠ 2m + 2`. -/
theorem subsingleton_cohomologyWithSupports_complexSpace_two {m : ℕ} (hm : 1 ≤ m) :
    Subsingleton (cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (Fin (m + 1) → ℂ))
      {0} (1 + 1 : ℕ)) := by
  let h : (Fin (m + 1) → ℂ) ≃L[ℝ] (Fin (2 * (m + 1)) → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (finrank_real_complexSpace m)
  let e : TopCat.of (Fin (m + 1) → ℂ) ≅ TopCat.of (Fin (2 * (m + 1)) → ℝ) :=
    TopCat.isoOfHomeo h.toHomeomorph
  have hpre : e.hom ⁻¹' ({0} : Set (Fin (2 * (m + 1)) → ℝ)) = {0} := by
    ext w
    exact h.map_eq_zero_iff
  have h' := (relativeSingularCohomologyIsoOfIso ℚ e ({0} : Set (Fin (2 * (m + 1)) → ℝ))ᶜ
    (1 + 1 : ℕ)).toLinearEquiv.toEquiv.subsingleton_congr.1
    (subsingleton_cohomologyWithSupports_euclidean ℚ (m := 2 * (m + 1)) (by omega) (k := 1 + 1)
      (by omega))
  rwa [Set.preimage_compl, hpre] at h'

/-- `H¹(ℂᵐ⁺¹ - 0; ℚ) = 0` for `m ≥ 1`. -/
theorem subsingleton_cohomology_complexSpace_compl_zero {m : ℕ} (hm : 1 ≤ m) :
    Subsingleton (cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.of ↥({0} : Set (TopCat.of (Fin (m + 1) → ℂ)))ᶜ) univ (1 : ℕ)) := by
  have := subsingleton_cohomology_complexSpace m 0
  have := subsingleton_cohomologyWithSupports_complexSpace_two hm
  refine subsingleton_of_forall_eq 0 fun y ↦ ?_
  obtain ⟨x, rfl⟩ := (exact_restrictCompl_delta ℚ (TopCat.of (Fin (m + 1) → ℂ)) {0} 1 y).1
    (Subsingleton.elim _ _)
  rw [Subsingleton.elim x 0, map_zero]

end PuncturedSpace

section Hopf

/-- The coordinate in `ℂ` of a point of the total space of the tautological bundle, in the
preferred chart of its base point. -/
def fibreCoord (p : TotalSpace ℂ (TautologicalBundle n)) : ℂ := p.2

/-- The fibre coordinate of `⟨P, v⟩` is `v`. -/
@[simp] lemma fibreCoord_mk (P : lineProjections n) (v : TautologicalBundle n P) :
    fibreCoord (⟨P, v⟩ : TotalSpace ℂ (TautologicalBundle n)) = v := rfl

variable (n) in
/-- The vector of `ℂⁿ⁺¹` represented by a point of the total space of the tautological bundle:
`⟨P, λ⟩ ↦ λ vᵢ`, with `vᵢ = (P k i / P i i)_k` for the preferred chart `i` of `P`. -/
def tautologicalVector (p : TotalSpace ℂ (TautologicalBundle n)) : Fin (n + 1) → ℂ :=
  fun k ↦ fibreCoord p * (p.1.1 k (chartIndex p.1) / p.1.1 (chartIndex p.1) (chartIndex p.1))

/-- The coordinate of a point `p` of the tautological bundle in the chart `Uⱼ` is
`P j i / P i i · fibreCoord p`, where `P` is the base point and `i` its preferred chart. -/
lemma localTriv_snd_tautological (j : Fin (n + 1)) (p : TotalSpace ℂ (TautologicalBundle n)) :
    ((tautologicalCore n).localTriv j p).2 =
      p.1.1 j (chartIndex p.1) / p.1.1 (chartIndex p.1) (chartIndex p.1) * fibreCoord p := by
  rw [VectorBundleCore.localTriv_apply]
  exact tautologicalCore_coordChange_apply _ _ _ _

/-- For a line projection `P` with `P i i ≠ 0` and `P j j ≠ 0`, the vectors
`vᵢ = (P k i / P i i)_k` and `vⱼ` satisfy `a vᵢ = (P j i / P i i) a vⱼ`, coordinatewise. -/
lemma rankOne_ratio_mul {P : lineProjections n} {i j : Fin (n + 1)} (hi : P.1 i i ≠ 0)
    (hj : P.1 j j ≠ 0) (a : ℂ) (k : Fin (n + 1)) :
    a * (P.1 k i / P.1 i i) = P.1 j i / P.1 i i * a * (P.1 k j / P.1 j j) := by
  have h := lineProjections_mul_mul_eq P.2 k j j i
  field_simp
  linear_combination (-a) * h

/-- In any chart `Uⱼ` containing `P`, the vector of `⟨P, λ⟩` is `λⱼ vⱼ`. -/
lemma tautologicalVector_eq (j : Fin (n + 1)) (p : TotalSpace ℂ (TautologicalBundle n))
    (hj : p.1.1 j j ≠ 0) (k : Fin (n + 1)) :
    tautologicalVector n p k =
      ((tautologicalCore n).localTriv j p).2 * (p.1.1 k j / p.1.1 j j) := by
  rw [localTriv_snd_tautological]
  exact rankOne_ratio_mul (chartIndex_diag_ne_zero p.1) hj _ k

/-- The map `tautologicalVector n` from the total space of the tautological bundle to `ℂⁿ⁺¹` is
continuous. -/
theorem continuous_tautologicalVector : Continuous (tautologicalVector n) := by
  refine continuous_iff_continuousAt.2 fun p₀ ↦ ?_
  set j := chartIndex p₀.1
  have hj := chartIndex_diag_ne_zero p₀.1
  have hsrc : p₀ ∈ ((tautologicalCore n).localTriv j).source := hj
  have hU : ∀ᶠ p in 𝓝 p₀, p.1.1 j j ≠ 0 :=
    (FiberBundle.continuous_proj ℂ (TautologicalBundle n)).continuousAt.preimage_mem_nhds
      (((tautologicalCore n).isOpen_baseSet j).mem_nhds hj)
  have hp : Continuous fun p : TotalSpace ℂ (TautologicalBundle n) ↦ p.1.1 :=
    continuous_subtype_val.comp (FiberBundle.continuous_proj ℂ (TautologicalBundle n))
  have hc : ContinuousAt (fun (p : TotalSpace ℂ (TautologicalBundle n)) (k : Fin (n + 1)) ↦
      ((tautologicalCore n).localTriv j p).2 * (p.1.1 k j / p.1.1 j j)) p₀ :=
    continuousAt_pi.2 fun k ↦ (continuous_snd.continuousAt.comp
      ((((tautologicalCore n).localTriv j).continuousOn.continuousAt
        (((tautologicalCore n).localTriv j).open_source.mem_nhds hsrc)))).mul
      ((continuous_entry hp k j).continuousAt.div (continuous_entry hp j j).continuousAt hj)
  refine hc.congr ?_
  filter_upwards [hU] with p hp
  exact funext fun k ↦ (tautologicalVector_eq j p hp k).symm

/-- The coordinate of `tautologicalVector n p` at the preferred chart index of its base point is
`fibreCoord p`. -/
lemma tautologicalVector_chartIndex (p : TotalSpace ℂ (TautologicalBundle n)) :
    tautologicalVector n p (chartIndex p.1) = fibreCoord p := by
  change fibreCoord p * (_ / _) = _
  rw [div_self (chartIndex_diag_ne_zero p.1), mul_one]

/-- A point of the tautological bundle lies on the zero section if and only if its fibre
coordinate vanishes. -/
lemma mem_range_zeroSection_tautological_iff (p : TotalSpace ℂ (TautologicalBundle n)) :
    p ∈ range (zeroSection ℂ (TautologicalBundle n)) ↔ fibreCoord p = 0 := by
  obtain ⟨P, v⟩ := p
  constructor
  · rintro ⟨x, hx⟩
    obtain rfl : x = P := congrArg TotalSpace.proj hx
    exact ((TotalSpace.mk_inj).1 hx).symm
  · rintro (rfl : v = 0)
    exact ⟨P, rfl⟩

/-- The vector of a point of the tautological bundle off the zero section is nonzero. -/
lemma tautologicalVector_ne_zero {p : TotalSpace ℂ (TautologicalBundle n)}
    (hp : p ∉ range (zeroSection ℂ (TautologicalBundle n))) : tautologicalVector n p ≠ 0 := by
  intro h
  apply hp
  rw [mem_range_zeroSection_tautological_iff, ← tautologicalVector_chartIndex, h]
  rfl

/-- The point of `ℙⁿ(ℂ)` of a nonzero vector. -/
def lineOf {w : Fin (n + 1) → ℂ} (hw : w ≠ 0) : lineProjections n :=
  ⟨lineProjection w, lineProjection_mem_lineProjections hw⟩

/-- The line of a nonzero vector `w` is the projection `lineProjection w`. -/
@[simp] lemma lineOf_coe {w : Fin (n + 1) → ℂ} (hw : w ≠ 0) :
    (lineOf hw).1 = lineProjection w := rfl

/-- A nonzero vector `w` has nonzero coordinate at the preferred chart index of its line. -/
lemma apply_chartIndex_ne_zero {w : Fin (n + 1) → ℂ} (hw : w ≠ 0) :
    w (chartIndex (lineOf hw)) ≠ 0 := by
  intro h
  apply chartIndex_diag_ne_zero (lineOf hw)
  change lineProjection w _ _ = 0
  simp [lineProjection, h]

/-- For a nonzero vector `w` with line `P` and preferred chart `i`,
`w i · (P k i / P i i) = w k`. -/
lemma apply_chartIndex_mul_ratio {w : Fin (n + 1) → ℂ} (hw : w ≠ 0) (k : Fin (n + 1)) :
    w (chartIndex (lineOf hw)) * (lineProjection w k (chartIndex (lineOf hw)) /
      lineProjection w (chartIndex (lineOf hw)) (chartIndex (lineOf hw))) = w k := by
  rw [lineProjection_div_apply hw (apply_chartIndex_ne_zero hw),
    mul_div_cancel₀ _ (apply_chartIndex_ne_zero hw)]

/-- An element of the complement of `{0}` in `ℂⁿ⁺¹` is nonzero. -/
lemma ne_zero_of_mem_compl (w : ↥({0} : Set (Fin (n + 1) → ℂ))ᶜ) : w.1 ≠ 0 := w.2

variable (n) in
/-- The point `⟨[w], w⟩` of the total space of the tautological bundle over a nonzero vector. -/
def tautologicalPoint (w : ↥({0} : Set (Fin (n + 1) → ℂ))ᶜ) :
    TotalSpace ℂ (TautologicalBundle n) :=
  ⟨lineOf (ne_zero_of_mem_compl w), w.1 (chartIndex (lineOf (ne_zero_of_mem_compl w)))⟩

/-- The vector of the point `tautologicalPoint n w` is `w`. -/
@[simp] lemma tautologicalVector_tautologicalPoint (w : ↥({0} : Set (Fin (n + 1) → ℂ))ᶜ) :
    tautologicalVector n (tautologicalPoint n w) = w.1 :=
  funext fun k ↦ apply_chartIndex_mul_ratio (ne_zero_of_mem_compl w) k

/-- The coordinate of `tautologicalPoint n w` in the chart `Uⱼ` is `w j`. -/
lemma localTriv_tautologicalPoint (j : Fin (n + 1)) (w : ↥({0} : Set (Fin (n + 1) → ℂ))ᶜ) :
    ((tautologicalCore n).localTriv j (tautologicalPoint n w)).2 = w.1 j := by
  rw [localTriv_snd_tautological, mul_comm]
  exact apply_chartIndex_mul_ratio (ne_zero_of_mem_compl w) j

/-- The map `tautologicalPoint n` from `ℂⁿ⁺¹ - 0` to the total space of the tautological bundle is
continuous. -/
theorem continuous_tautologicalPoint : Continuous (tautologicalPoint n) := by
  refine continuous_iff_continuousAt.2 fun w₀ ↦ ?_
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨((continuous_lineProjection_comp continuous_subtype_val
    ne_zero_of_mem_compl).subtype_mk _).continuousAt, ?_⟩
  change ContinuousAt (fun w ↦ ((tautologicalCore n).localTriv
    (chartIndex (lineOf (ne_zero_of_mem_compl w₀))) (tautologicalPoint n w)).2) w₀
  simp_rw [localTriv_tautologicalPoint]
  exact ((continuous_apply _).comp continuous_subtype_val).continuousAt

/-- A point `p` of the tautological bundle off the zero section is the point
`tautologicalPoint n` of its vector `tautologicalVector n p`. -/
lemma tautologicalPoint_tautologicalVector (p : TotalSpace ℂ (TautologicalBundle n))
    (hp : p ∉ range (zeroSection ℂ (TautologicalBundle n))) :
    tautologicalPoint n ⟨tautologicalVector n p, tautologicalVector_ne_zero hp⟩ = p := by
  have hv : fibreCoord p ≠ 0 := fun h ↦ hp ((mem_range_zeroSection_tautological_iff _).2 h)
  have hline : lineOf (tautologicalVector_ne_zero hp) = p.1 := by
    obtain ⟨⟨P, hP⟩, v⟩ := p
    obtain ⟨u, hu, rfl⟩ := hP
    set i := chartIndex (⟨lineProjection u, lineProjection_mem_lineProjections hu⟩ :
      lineProjections n)
    have hui : u i ≠ 0 := apply_chartIndex_ne_zero hu
    have heq : tautologicalVector n ⟨⟨lineProjection u, _⟩, v⟩ =
        (fibreCoord (⟨⟨lineProjection u, _⟩, v⟩ : TotalSpace ℂ (TautologicalBundle n)) / u i) •
          u := by
      funext k
      change fibreCoord _ * (lineProjection u k i / lineProjection u i i) = _
      rw [lineProjection_div_apply hu hui, Pi.smul_apply, smul_eq_mul]
      ring
    refine Subtype.ext ?_
    change lineProjection (tautologicalVector n _) = _
    rw [heq, lineProjection_smul hu (div_ne_zero hv hui)]
  have key : ∀ (Q : lineProjections n) (hQ : Q = p.1) (a : ℂ) (ha : a = fibreCoord p),
      (⟨Q, a⟩ : TotalSpace ℂ (TautologicalBundle n)) = p := by
    rintro _ rfl _ rfl
    rfl
  refine key _ hline _ ?_
  change tautologicalVector n p (chartIndex (lineOf (tautologicalVector_ne_zero hp))) = _
  rw [hline]
  exact tautologicalVector_chartIndex p

variable (n) in
/-- **The tautological bundle minus its zero section is `ℂⁿ⁺¹ - 0`** (the Hopf fibration, for
`n = 1`): `⟨P, λ⟩ ↦ λ vᵢ`. -/
def tautologicalComplHomeomorph :
    ↥(range (zeroSection ℂ (TautologicalBundle n)))ᶜ ≃ₜ ↥({0} : Set (Fin (n + 1) → ℂ))ᶜ where
  toFun p := ⟨tautologicalVector n p.1, tautologicalVector_ne_zero p.2⟩
  invFun w := ⟨tautologicalPoint n w, fun h ↦ apply_chartIndex_ne_zero (ne_zero_of_mem_compl w)
    ((mem_range_zeroSection_tautological_iff _).1 h)⟩
  left_inv p := Subtype.ext (tautologicalPoint_tautologicalVector p.1 p.2)
  right_inv w := Subtype.ext (tautologicalVector_tautologicalPoint w)
  continuous_toFun := (continuous_tautologicalVector.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := continuous_tautologicalPoint.subtype_mk _

/-- The homeomorphism `tautologicalComplHomeomorph n` sends `p` to its vector. -/
@[simp] lemma tautologicalComplHomeomorph_apply_coe
    (p : ↥(range (zeroSection ℂ (TautologicalBundle n)))ᶜ) :
    (tautologicalComplHomeomorph n p : Fin (n + 1) → ℂ) = tautologicalVector n p.1 := rfl

/-- The inverse of `tautologicalComplHomeomorph n` sends `w` to `tautologicalPoint n w`. -/
@[simp] lemma tautologicalComplHomeomorph_symm_apply_coe (w : ↥({0} : Set (Fin (n + 1) → ℂ))ᶜ) :
    ((tautologicalComplHomeomorph n).symm w : TotalSpace ℂ (TautologicalBundle n)) =
      tautologicalPoint n w := rfl

end Hopf

section Euler

open CategoryTheory

/-- Complex projective space `ℙⁿ(ℂ)` is nonempty. -/
instance : Nonempty (lineProjections n) :=
  ⟨lineOf (w := Pi.single 0 1) (by simp)⟩

/-- **The Euler class of the tautological line bundle on `ℙⁿ(ℂ)` is nonzero** in
`H²(ℙⁿ(ℂ); ℚ)` for `n ≥ 1`. -/
theorem eulerClass_tautologicalBundle_ne_zero (hn : 1 ≤ n) :
    eulerClass ℚ ℂ (TautologicalBundle n) ≠ 0 := by
  apply eulerClass_ne_zero_of_subsingleton
  let e : TopCat.of ↥(range (zeroSection ℂ (TautologicalBundle n)))ᶜ ≅
      TopCat.of ↥({0} : Set (Fin (n + 1) → ℂ))ᶜ :=
    TopCat.isoOfHomeo (X := TopCat.of ↥(range (zeroSection ℂ (TautologicalBundle n)))ᶜ)
      (Y := TopCat.of ↥({0} : Set (Fin (n + 1) → ℂ))ᶜ) (tautologicalComplHomeomorph n)
  have h' := (relativeSingularCohomologyIsoOfIso ℚ e (univ : Set (TopCat.of
    ↥({0} : Set (Fin (n + 1) → ℂ))ᶜ))ᶜ (1 : ℕ)).toLinearEquiv.toEquiv.subsingleton_congr.1
    (subsingleton_cohomology_complexSpace_compl_zero hn)
  rwa [Set.preimage_compl, Set.preimage_univ] at h'

end Euler

end MMP.Topology
