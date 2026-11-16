module

public import MMP.RingTheory.Presentation.RegularPartDenseAlgebra
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.HypersurfaceComplement
public import Mathlib.Analysis.Normed.Field.Approximation
public import Mathlib.Analysis.Polynomial.CauchyBound
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# The nonvanishing locus of a regular function is dense in the classical topology

Let `A` be a finitely generated `ℂ`-algebra which is a domain, and give its set of `ℂ`-points
`ψ : A → ℂ` the topology of pointwise convergence (the topology of `ℂ^A`). For `h ≠ 0` in `A`,
the points with `ψ(h) ≠ 0` are dense.

Choose a Noether normalization `ℂ[x₁, …, xₛ] ⊆ A`. Some `b ≠ 0` in `ℂ[x]` is a multiple of `h`,
and `{b ≠ 0}` is dense in `ℂˢ`. Given a point `φ`, separate it from the rest of its fibre by an
element `a`. As `z → φ(x)`, a root of the minimal polynomial of `a` specialised at `z` tends to
`φ(a)` (continuity of roots), and lifts to a point `ψ` over `z` with `ψ(a)` that root (lying
over). The points over a compact neighbourhood of `φ(x)` form a compact set (their coordinates
are bounded by Cauchy's bound), on which `(proj, a)` takes the value `(φ(x), φ(a))` only at `φ`;
so these `ψ` converge to `φ`.

## Main results

* `MMP.RegularPartDense.isClosed_range_coe_algHom`: the `k`-points of `A` form a
  closed subset of `k^A`.
* `MMP.RegularPartDense.eventually_exists_root_near`: continuity of the roots of a
  monic polynomial over `ℂ[xᵢ]` specialised at `z ∈ ℂˢ`.
* `MMP.RegularPartDense.mem_closure_image_setOf_apply_ne_zero`: every `ℂ`-point
  of `A` is a limit of points at which `h ≠ 0` does not vanish.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
* [I. R. Shafarevich, *Basic Algebraic Geometry 2*], Chapter VII, §2.
-/

public noncomputable section

open Polynomial Filter Topology Metric

namespace MMP.RegularPartDense

/-- The `k`-algebra homomorphisms `A → k` form a closed subset of `k^A`. -/
theorem isClosed_range_coe_algHom (k A : Type*) [Field k] [TopologicalSpace k]
    [IsTopologicalRing k] [T2Space k] [CommRing A] [Algebra k A] :
    IsClosed (Set.range ((⇑) : (A →ₐ[k] k) → A → k)) := by
  have : Set.range ((⇑) : (A →ₐ[k] k) → A → k) =
      {f : A → k | f 1 = 1} ∩ {f | ∀ x y : A, f (x * y) = f x * f y} ∩
        {f | ∀ x y : A, f (x + y) = f x + f y} ∩
          {f | ∀ (c : k) (x : A), f (c • x) = id c • f x} := by
    ext f
    constructor
    · rintro ⟨ψ, rfl⟩
      exact ⟨⟨⟨map_one ψ, map_mul ψ⟩, map_add ψ⟩, fun c x ↦ by simp⟩
    · rintro ⟨⟨⟨h1, hmul⟩, hadd⟩, hsmul⟩
      have h0 : f 0 = 0 := by simpa using hadd 0 0
      let ψ : A →ₐ[k] k :=
        { toFun := f
          map_one' := h1
          map_mul' := hmul
          map_zero' := h0
          map_add' := hadd
          commutes' := fun c ↦ by
            change f (algebraMap k A c) = c
            rw [Algebra.algebraMap_eq_smul_one, hsmul c 1, h1, id, smul_eq_mul, mul_one] }
      exact ⟨ψ, rfl⟩
  rw [this]
  exact (((isClosed_setOf_map_one A k).inter (isClosed_setOf_map_mul A k)).inter
    (isClosed_setOf_map_add A k)).inter (isClosed_setOf_map_smul A k id)

/-- **Continuity of roots.** Let `M` be a monic polynomial over `ℂ[xᵢ]` and `t₀` a root of `M`
specialised at `z₀ ∈ ℂ^σ`. For `z` near `z₀`, `M` specialised at `z` has a root near `t₀`. -/
theorem eventually_exists_root_near {σ : Type*} {M : (MvPolynomial σ ℂ)[X]} (hM : M.Monic)
    {z₀ : σ → ℂ} {t₀ : ℂ} (ht₀ : (M.map (MvPolynomial.eval z₀)).eval t₀ = 0) {δ : ℝ}
    (hδ : 0 < δ) :
    ∀ᶠ z in 𝓝 z₀, ∃ t, (M.map (MvPolynomial.eval z)).eval t = 0 ∧ ‖t₀ - t‖ < δ := by
  set f := M.map (MvPolynomial.eval z₀)
  have hfm : f.Monic := hM.map _
  have hfd : f.natDegree = M.natDegree := hM.natDegree_map _
  set d := M.natDegree
  have hd : d ≠ 0 := by
    intro h0
    simp [hfm.natDegree_eq_zero.mp (hfd.trans h0)] at ht₀
  set C := max ‖t₀‖ 1
  have hC : 0 < C := lt_max_of_lt_right one_pos
  set ε := (δ / (2 * C)) ^ d / (d + 1)
  have hε : 0 < ε := by positivity
  have hεeq : ((f.natDegree + 1 : ℝ) * ε) ^ (f.natDegree : ℝ)⁻¹ * C = δ / 2 := by
    rw [hfd]
    have : ((d + 1 : ℝ) * ε) = (δ / (2 * C)) ^ d := by
      simp only [ε]
      field_simp
    rw [this, Real.pow_rpow_inv_natCast (by positivity) hd]
    field_simp
  have hev : ∀ᶠ z in 𝓝 z₀, ∀ i ∈ Finset.range (d + 1),
      ‖MvPolynomial.eval z (M.coeff i) - MvPolynomial.eval z₀ (M.coeff i)‖ < ε := by
    refine (Finset.eventually_all _).mpr fun i _ ↦ ?_
    filter_upwards [((MvPolynomial.continuous_eval (M.coeff i)).continuousAt (x := z₀)).eventually
      (ball_mem_nhds _ hε)] with z hz
    rwa [dist_eq_norm] at hz
  filter_upwards [hev] with z hz
  set g := M.map (MvPolynomial.eval z)
  have hgm : g.Monic := hM.map _
  have hcoeff : ∀ i, ‖g.coeff i - f.coeff i‖ < ε := by
    intro i
    simp only [g, f, coeff_map]
    by_cases hi : i ≤ d
    · exact hz i (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
    · rw [coeff_eq_zero_of_natDegree_lt (not_le.mp hi)]
      simpa using hε
  obtain ⟨b, hb, hb'⟩ := exists_roots_norm_sub_lt_of_norm_coeff_sub_lt hε ht₀ hfm hgm
    ((hM.natDegree_map _).trans hfd.symm) hcoeff (IsAlgClosed.splits g)
  refine ⟨b, (mem_roots hgm.ne_zero).mp hb, ?_⟩
  rw [hεeq] at hb'
  linarith

section Points

variable {A : Type*} [CommRing A] [Algebra ℂ A]

/-- The values at a `ℂ`-point `ψ` of an element `x` of an algebra `A`, integral over `ℂ[xᵢ]`, are
bounded when `proj σ ψ` stays in a compact set. -/
theorem exists_bound_of_isCompact {σ : Type*} [Algebra (MvPolynomial σ ℂ) A]
    [IsScalarTower ℂ (MvPolynomial σ ℂ) A] [Algebra.IsIntegral (MvPolynomial σ ℂ) A]
    {S : Set (σ → ℂ)} (hS : IsCompact S) (x : A) :
    ∃ C, ∀ ψ : A →ₐ[ℂ] ℂ, proj σ ψ ∈ S → ‖ψ x‖ ≤ C := by
  set Q := minpoly (MvPolynomial σ ℂ) x
  have hQ : Q.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral x)
  let F : (σ → ℂ) → ℝ := fun z ↦
    ∑ i ∈ Finset.range Q.natDegree, ‖MvPolynomial.eval z (Q.coeff i)‖
  have hF : Continuous F := continuous_finset_sum _ fun i _ ↦
    (MvPolynomial.continuous_eval _).norm
  obtain ⟨C₀, hC₀⟩ := hS.exists_bound_of_continuousOn hF.continuousOn
  refine ⟨C₀ + 1, fun ψ hψ ↦ ?_⟩
  set p := Q.map (MvPolynomial.eval (proj σ ψ))
  have hpm : p.Monic := hQ.map _
  have hroot : p.IsRoot (ψ x) := by
    rw [IsRoot.def, ← apply_aeval, minpoly.aeval, map_zero]
  have hcb : (cauchyBound p : ℝ) ≤ F (proj σ ψ) + 1 := by
    rw [cauchyBound, hpm.leadingCoeff, nnnorm_one, div_one, NNReal.coe_add, NNReal.coe_one,
      add_le_add_iff_right, hQ.natDegree_map]
    refine (NNReal.coe_le_coe.mpr (Finset.sup_le fun i hi ↦
      Finset.single_le_sum (f := fun i ↦ ‖p.coeff i‖₊) (fun _ _ ↦ bot_le) hi)).trans ?_
    simp [F, p, coeff_map]
  have h1 : F (proj σ ψ) ≤ C₀ := (le_abs_self _).trans (hC₀ _ hψ)
  have h2 : ‖ψ x‖ < cauchyBound p := hroot.norm_lt_cauchyBound hpm.ne_zero
  linarith

/-- The `ℂ`-points of an algebra `A`, integral over `ℂ[xᵢ]`, lying over a compact set of `ℂ^σ`
form a compact subset of `ℂ^A`. -/
theorem isCompact_range_coe_algHom_inter_preimage {σ : Type*} [Algebra (MvPolynomial σ ℂ) A]
    [IsScalarTower ℂ (MvPolynomial σ ℂ) A] [Algebra.IsIntegral (MvPolynomial σ ℂ) A]
    {S : Set (σ → ℂ)} (hS : IsCompact S) :
    IsCompact (Set.range ((⇑) : (A →ₐ[ℂ] ℂ) → A → ℂ) ∩
      (fun f i ↦ f (algebraMap (MvPolynomial σ ℂ) A (MvPolynomial.X i))) ⁻¹' S) := by
  choose C hC using fun x : A ↦ exists_bound_of_isCompact hS x
  refine (isCompact_univ_pi fun x ↦ isCompact_closedBall (0 : ℂ) (C x)).of_isClosed_subset
    ((isClosed_range_coe_algHom ℂ A).inter
      (hS.isClosed.preimage (continuous_pi fun i ↦ continuous_apply _))) ?_
  rintro _ ⟨⟨ψ, rfl⟩, hψ⟩ x -
  rw [mem_closedBall, dist_zero_right]
  exact hC x ψ hψ

/-- **The nonvanishing locus of a nonzero function is dense.** Let `A` be a finitely generated
`ℂ`-algebra which is a domain and `h ≠ 0` in `A`. Every `ℂ`-point `φ` of `A` is, in the topology
of pointwise convergence on `A`, a limit of `ℂ`-points `ψ` with `ψ(h) ≠ 0`. -/
theorem mem_closure_image_setOf_apply_ne_zero [IsDomain A] [Algebra.FiniteType ℂ A] {h : A}
    (hh : h ≠ 0) (φ : A →ₐ[ℂ] ℂ) :
    (⇑φ : A → ℂ) ∈ closure ((⇑) '' {ψ : A →ₐ[ℂ] ℂ | ψ h ≠ 0}) := by
  obtain ⟨s, g, hginj, hgfin⟩ := exists_finite_inj_algHom_of_fg ℂ A
  letI : Algebra (MvPolynomial (Fin s) ℂ) A := g.toRingHom.toAlgebra
  haveI : IsScalarTower ℂ (MvPolynomial (Fin s) ℂ) A :=
    IsScalarTower.of_algebraMap_eq fun c ↦ (g.commutes c).symm
  haveI : Algebra.IsIntegral (MvPolynomial (Fin s) ℂ) A := ⟨fun x ↦ hgfin.to_isIntegral x⟩
  haveI : Module.IsTorsionFree (MvPolynomial (Fin s) ℂ) A :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hginj
  set z₀ := proj (Fin s) φ
  obtain ⟨b, hbmem, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (Ideal.comap_ne_bot_of_integral_mem hh (Ideal.mem_span_singleton_self h)
      (Algebra.IsIntegral.isIntegral (R := MvPolynomial (Fin s) ℂ) h))
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (Ideal.mem_comap.mp hbmem)
  obtain ⟨a, ha⟩ := exists_separating (σ := Fin s) φ
  have hM := minpoly.monic (Algebra.IsIntegral.isIntegral (R := MvPolynomial (Fin s) ℂ) a)
  have ht₀ : ((minpoly (MvPolynomial (Fin s) ℂ) a).map (MvPolynomial.eval z₀)).eval (φ a) = 0 := by
    rw [← apply_aeval, minpoly.aeval, map_zero]
  let P : (A → ℂ) → Fin s → ℂ := fun f i ↦
    f (algebraMap (MvPolynomial (Fin s) ℂ) A (MvPolynomial.X i))
  have hP : Continuous P := continuous_pi fun i ↦ continuous_apply _
  have hPψ : ∀ ψ : A →ₐ[ℂ] ℂ, P ψ = proj (Fin s) ψ := fun ψ ↦ rfl
  let K := Set.range ((⇑) : (A →ₐ[ℂ] ℂ) → A → ℂ) ∩ P ⁻¹' closedBall z₀ 1
  have hK : IsCompact K := isCompact_range_coe_algHom_inter_preimage (isCompact_closedBall z₀ 1)
  refine _root_.mem_closure_iff.mpr fun o ho hφo ↦ ?_
  let G : (A → ℂ) → (Fin s → ℂ) × ℂ := fun f ↦ (P f, f a)
  have hKo : IsClosed (G '' (K \ o)) :=
    ((hK.diff ho).image (hP.prodMk (continuous_apply a))).isClosed
  have hnot : (z₀, φ a) ∉ G '' (K \ o) := by
    rintro ⟨_, ⟨⟨⟨ψ, rfl⟩, -⟩, hψo⟩, hG'⟩
    simp only [G, Prod.mk.injEq, hPψ] at hG'
    exact hψo (ha ψ hG'.1 hG'.2 ▸ hφo)
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hKo.isOpen_compl _ hnot
  obtain ⟨U, hUsub, hUo, hz₀U⟩ := _root_.mem_nhds_iff.mp (eventually_exists_root_near hM ht₀ hδ)
  obtain ⟨z, ⟨hzU, hzball⟩, hzb⟩ :=
    (SmoothLocusConnected.dense_setOf_eval_ne_zero hb0).inter_open_nonempty
      (U ∩ ball z₀ (min δ 1)) (hUo.inter isOpen_ball)
      ⟨z₀, hz₀U, mem_ball_self (lt_min hδ one_pos)⟩
  obtain ⟨t, ht, htd⟩ := hUsub hzU
  obtain ⟨ψ, hψz, hψa⟩ := exists_algHom_lyingOver a z t ht
  refine ⟨ψ, ?_, ψ, fun h0 ↦ hzb ?_, rfl⟩
  · by_contra hψo
    have hzd : dist z z₀ < min δ 1 := hzball
    refine hball ?_ ⟨ψ, ⟨⟨⟨ψ, rfl⟩, ?_⟩, hψo⟩, rfl⟩
    · rw [mem_ball, Prod.dist_eq]
      simp only [G, hPψ, hψz, hψa]
      refine max_lt (hzd.trans_le (min_le_left _ _)) ?_
      rwa [dist_comm, dist_eq_norm]
    · rw [Set.mem_preimage, hPψ, hψz, mem_closedBall]
      exact (hzd.trans_le (min_le_right _ _)).le
  · rw [← hψz, ← apply_algebraMap, ← hc, map_mul, h0, mul_zero]

end Points

end MMP.RegularPartDense
