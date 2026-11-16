module
import MMP.AlgebraicGeometry.SpecOverSpecSelf
import StacksFrontier.AlgebraicGeometry.AffineClosedUnion.Global
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.ConductorDefect
import MMP.AlgebraicGeometry.Analytic.CartierDivisorDictionary
import MMP.AlgebraicGeometry.Intersection.ThreefoldHodgeIndex
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.VerticalKernelBlowup
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.WeightedSurfaceIdentity
import MMP.AlgebraicGeometry.Resolution.BlowupChartClosedImmersion
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.PrimeDivisorCurveFamily
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Resolution.SNCPullback
import MMP.AlgebraicGeometry.SpreadingOut.CoefficientModelsModules
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite
import MMP.AlgebraicGeometry.Intersection.Surface.RiemannRochHodgeIndex
public import MMP.AlgebraicGeometry.ReducedSubschemeOver
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheafMul
public import MMP.AlgebraicGeometry.SubschemeOver
public import MMP.AlgebraicGeometry.Chow.CapDegreeDivisorGysin
import MMP.AlgebraicGeometry.Chow.CapDegreeDivisorGysinComponent
import MMP.AlgebraicGeometry.RegularImmersion.OfSmooth

/-!
# thm mmp conductor isolated point algebraic kernel

Chain fold of: `thm_mmp_conductor_isolated_point_algebraic_kernel`.
-/

/-! ### `thm_mmp_conductor_isolated_point_algebraic_kernel` -/

open AlgebraicGeometry CategoryTheory MMP
open scoped MMP.SubschemeOver

namespace MMP.Fold06.ThmMmpConductorIsolatedPointAlgebraicKernel

open MMP.Fourfold MMP.Mori

/-! ### The numerical core -/

section Algebra

variable {Z : Scheme.{0}} (F : MMP.Mori.Divisor Z) [Fintype (DoubleSurface F)] [DecidableEq F.support]
  {V : F.support → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℚ (V i)]

public abbrev fstS (σ : DoubleSurface F) : F.support := ⟨σ.fst, σ.fst_mem⟩
public abbrev sndS (σ : DoubleSurface F) : F.support := ⟨σ.snd, σ.snd_mem⟩

private def swapPerm : Equiv.Perm (DoubleSurface F) :=
  Function.Involutive.toPerm _ fun σ : DoubleSurface F => DoubleSurface.swap_swap σ

private theorem sum_swap {M : Type*} [AddCommMonoid M] (g : DoubleSurface F → M) :
    ∑ σ : DoubleSurface F, g σ.swap = ∑ σ : DoubleSurface F, g σ :=
  Fintype.sum_equiv (swapPerm F) _ _ fun _ => rfl

/-- The linear map `a ↦ (UA_σ(Z_fst a)/m_fst - UA_{σ'}(Z_snd a)/m_snd)_σ`. -/
private def orthMap (m : F.support → ℚ) (Zl : (DoubleSurface F → ℚ) →ₗ[ℚ] (∀ i, V i))
    (UA : ∀ σ : DoubleSurface F, V (fstS F σ) →ₗ[ℚ] ℚ) :
    (DoubleSurface F → ℚ) →ₗ[ℚ] (DoubleSurface F → ℚ) :=
  LinearMap.pi fun σ : DoubleSurface F =>
    (m (fstS F σ))⁻¹ • (UA σ ∘ₗ LinearMap.proj (fstS F σ) ∘ₗ Zl) -
      (m (sndS F σ))⁻¹ • (UA σ.swap ∘ₗ LinearMap.proj (sndS F σ) ∘ₗ Zl)

private theorem orthMap_apply (m : F.support → ℚ) (Zl : (DoubleSurface F → ℚ) →ₗ[ℚ] (∀ i, V i))
    (UA : ∀ σ : DoubleSurface F, V (fstS F σ) →ₗ[ℚ] ℚ) (a : DoubleSurface F → ℚ)
    (σ : DoubleSurface F) :
    orthMap F m Zl UA a σ = UA σ (Zl a (fstS F σ)) / m (fstS F σ) -
      UA σ.swap (Zl a (sndS F σ)) / m (sndS F σ) := by
  change (m (fstS F σ))⁻¹ * UA σ (Zl a (fstS F σ)) -
    (m (sndS F σ))⁻¹ * UA σ.swap (Zl a (sndS F σ)) = _
  ring

private theorem orthMap_swap (m : F.support → ℚ) (Zl : (DoubleSurface F → ℚ) →ₗ[ℚ] (∀ i, V i))
    (UA : ∀ σ : DoubleSurface F, V (fstS F σ) →ₗ[ℚ] ℚ) (a : DoubleSurface F → ℚ)
    (σ : DoubleSurface F) :
    orthMap F m Zl UA a σ.swap = - orthMap F m Zl UA a σ := by
  rw [orthMap_apply, orthMap_apply]
  change UA σ.swap (Zl a (sndS F σ)) / m (sndS F σ) - UA σ (Zl a (fstS F σ)) / m (fstS F σ) = _
  ring

private theorem sum_mul_orthMap (m : F.support → ℚ) (Zl : (DoubleSurface F → ℚ) →ₗ[ℚ] (∀ i, V i))
    (UA : ∀ σ : DoubleSurface F, V (fstS F σ) →ₗ[ℚ] ℚ) (ρv : ∀ σ : DoubleSurface F, V (fstS F σ))
    (B : ∀ i, V i →ₗ[ℚ] V i →ₗ[ℚ] ℚ)
    (hZlin : ∀ (f : ∀ i, V i →ₗ[ℚ] ℚ) (a : DoubleSurface F → ℚ),
      ∑ i, f i (Zl a i) = ∑ σ : DoubleSurface F, a σ * f (fstS F σ) (ρv σ))
    (hRA : ∀ (σ : DoubleSurface F) x, UA σ x = B (fstS F σ) x (ρv σ))
    {a : DoubleSurface F → ℚ} (ha : a ∈ orientedSurfaceCoefficients F) :
    ∑ σ : DoubleSurface F, a σ * orthMap F m Zl UA a σ =
      2 * ∑ i, B i (Zl a i) (Zl a i) / m i := by
  set X : DoubleSurface F → ℚ := fun σ => UA σ (Zl a (fstS F σ)) / m (fstS F σ) with hX
  have h1 : ∀ σ : DoubleSurface F, orthMap F m Zl UA a σ = X σ - X σ.swap := fun σ => by
    rw [orthMap_apply]; rfl
  have h2 : ∑ σ : DoubleSurface F, a σ * X σ.swap = - ∑ σ : DoubleSurface F, a σ * X σ := by
    rw [← sum_swap F (fun σ => a σ * X σ.swap)]
    simp only [DoubleSurface.swap_swap, (mem_orientedSurfaceCoefficients F).1 ha, neg_mul,
      Finset.sum_neg_distrib]
  have h3 : ∑ σ : DoubleSurface F, a σ * X σ = ∑ i, B i (Zl a i) (Zl a i) / m i := by
    have := hZlin (fun i => (m i)⁻¹ • B i (Zl a i)) a
    simp only [LinearMap.smul_apply, smul_eq_mul] at this
    simp only [div_eq_inv_mul]
    rw [this]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [hX]
    simp only [hRA, div_eq_inv_mul]
  simp_rw [h1, mul_sub, Finset.sum_sub_distrib, h2, h3]
  ring

private theorem exists_mem_orientedSurfaceCoefficients_orth (m : F.support → ℚ)
    (Zl : (DoubleSurface F → ℚ) →ₗ[ℚ] (∀ i, V i))
    (UA : ∀ σ : DoubleSurface F, V (fstS F σ) →ₗ[ℚ] ℚ) (ρv : ∀ σ : DoubleSurface F, V (fstS F σ))
    (B : ∀ i, V i →ₗ[ℚ] V i →ₗ[ℚ] ℚ)
    (hZlin : ∀ (f : ∀ i, V i →ₗ[ℚ] ℚ) (a : DoubleSurface F → ℚ),
      ∑ i, f i (Zl a i) = ∑ σ : DoubleSurface F, a σ * f (fstS F σ) (ρv σ))
    (hRA : ∀ (σ : DoubleSurface F) x, UA σ x = B (fstS F σ) x (ρv σ))
    (hWI : ∀ a ∈ orientedSurfaceCoefficients F,
      ∑ i, B i (Zl a i) (Zl a i) / m i = 0 → a = 0) (L : ∀ i, V i) :
    ∃ a ∈ orientedSurfaceCoefficients F, ∀ σ : DoubleSurface F,
      UA σ ((L - Zl a) (fstS F σ)) / m (fstS F σ) =
        UA σ.swap ((L - Zl a) (sndS F σ)) / m (sndS F σ) := by
  set O := orientedSurfaceCoefficients F
  set T := orthMap F m Zl UA
  have hTO : ∀ a, T a ∈ O := fun a σ => orthMap_swap F m Zl UA a σ
  let T' : O →ₗ[ℚ] O := (T.domRestrict O).codRestrict O fun a => hTO a
  have hinj : Function.Injective T' := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨a, ha⟩ h
    have hT : T a = 0 := congrArg Subtype.val h
    have hs := sum_mul_orthMap F m Zl UA ρv B hZlin hRA ha
    rw [show orthMap F m Zl UA a = 0 from hT] at hs
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero] at hs
    exact Subtype.ext (hWI a ha (by linarith))
  have hsurj : Function.Surjective T' := LinearMap.injective_iff_surjective.1 hinj
  set c : DoubleSurface F → ℚ := fun σ => UA σ (L (fstS F σ)) / m (fstS F σ) -
    UA σ.swap (L (sndS F σ)) / m (sndS F σ) with hc
  have hcO : c ∈ O := fun σ => by
    change UA σ.swap (L (sndS F σ)) / m (sndS F σ) - UA σ (L (fstS F σ)) / m (fstS F σ) = _
    rw [hc]; ring
  obtain ⟨⟨a, ha⟩, hTa⟩ := hsurj ⟨c, hcO⟩
  have hTa' : ∀ σ, T a σ = c σ := fun σ => congrFun (congrArg Subtype.val hTa) σ
  refine ⟨a, ha, fun σ => ?_⟩
  have h := hTa' σ
  rw [orthMap_apply] at h
  have e1 : UA σ ((L - Zl a) (fstS F σ)) = UA σ (L (fstS F σ)) - UA σ (Zl a (fstS F σ)) :=
    map_sub _ _ _
  have e2 : UA σ.swap ((L - Zl a) (sndS F σ)) =
      UA σ.swap (L (sndS F σ)) - UA σ.swap (Zl a (sndS F σ)) :=
    map_sub (UA σ.swap) (L (sndS F σ)) (Zl a (sndS F σ))
  rw [e1, e2]
  rw [hc] at h
  simp only at h
  linear_combination -h

private theorem lam_eq_zero_of_orth (m : F.support → ℚ) (hm : ∀ i, 0 < m i)
    (Lam GA : ∀ i, V i →ₗ[ℚ] ℚ) (UA : ∀ σ : DoubleSurface F, V (fstS F σ) →ₗ[ℚ] ℚ)
    (hGA : ∀ (x : ∀ i, V i) i, -m i * GA i (x i) = Lam i (x i) +
      ∑ σ : DoubleSurface F, if fstS F σ = i then m (sndS F σ) * UA σ (x (fstS F σ)) else 0)
    (M : ∀ i, V i)
    (horth : ∀ σ : DoubleSurface F, UA σ (M (fstS F σ)) / m (fstS F σ) =
      UA σ.swap (M (sndS F σ)) / m (sndS F σ))
    (hE1 : ∀ i, GA i (M i) +
      ∑ σ : DoubleSurface F, (if sndS F σ = i then UA σ (M (fstS F σ)) else 0) = 0) (i : F.support) :
    Lam i (M i) = 0 := by
  have h1 := hGA M i
  have h2 := hE1 i
  have hsw : ∑ σ : DoubleSurface F, (if sndS F σ = i then UA σ (M (fstS F σ)) else 0) =
      ∑ σ : DoubleSurface F, (if fstS F σ = i then UA σ.swap (M (sndS F σ)) else 0) :=
    (sum_swap F (fun σ => if sndS F σ = i then UA σ (M (fstS F σ)) else 0)).symm
  have hterm : ∀ σ : DoubleSurface F,
      (if fstS F σ = i then m (sndS F σ) * UA σ (M (fstS F σ)) else 0) =
        m i * (if fstS F σ = i then UA σ.swap (M (sndS F σ)) else 0) := by
    intro σ
    split_ifs with h
    · subst h
      have := horth σ
      have h1 := (hm (fstS F σ)).ne'
      have h2 := (hm (sndS F σ)).ne'
      field_simp at this
      linear_combination this
    · ring
  rw [Finset.sum_congr rfl fun σ _ => hterm σ, ← Finset.mul_sum] at h1
  rw [hsw] at h2
  linear_combination -h1 - m i * h2

private theorem forall_of_orth (m : F.support → ℚ) (hm : ∀ i, 0 < m i)
    (B G : ∀ i, V i →ₗ[ℚ] V i →ₗ[ℚ] ℚ) (Lam GA : ∀ i, V i →ₗ[ℚ] ℚ)
    (U : ∀ σ : DoubleSurface F, V (fstS F σ) →ₗ[ℚ] V (fstS F σ) →ₗ[ℚ] ℚ)
    (C : ∀ σ : DoubleSurface F, V (fstS F σ) →ₗ[ℚ] V (sndS F σ) →ₗ[ℚ] ℚ)
    (UA : ∀ σ : DoubleSurface F, V (fstS F σ) →ₗ[ℚ] ℚ) (Q : ∀ i, V i → Prop)
    (hGA : ∀ (x : ∀ i, V i) i, -m i * GA i (x i) = Lam i (x i) +
      ∑ σ : DoubleSurface F, if fstS F σ = i then m (sndS F σ) * UA σ (x (fstS F σ)) else 0)
    (hG : ∀ (x : ∀ i, V i) i, -m i * G i (x i) (x i) = B i (x i) (x i) +
      ∑ σ : DoubleSurface F,
        if fstS F σ = i then m (sndS F σ) * U σ (x (fstS F σ)) (x (fstS F σ)) else 0)
    (hSI : ∀ (σ : DoubleSurface F) x y, UA σ x = UA σ.swap y →
      U σ x x - 2 * C σ x y + U σ.swap y y ≤ 0)
    (hTI : ∀ i x, Lam i x = 0 → B i x x ≤ 0 ∧ (B i x x = 0 → Q i x))
    (M : ∀ i, V i)
    (horth : ∀ σ : DoubleSurface F, UA σ (M (fstS F σ)) / m (fstS F σ) =
      UA σ.swap (M (sndS F σ)) / m (sndS F σ))
    (hE1 : ∀ i, GA i (M i) +
      ∑ σ : DoubleSurface F, (if sndS F σ = i then UA σ (M (fstS F σ)) else 0) = 0)
    (hE2 : ∑ i, G i (M i) (M i) +
      ∑ σ : DoubleSurface F, C σ (M (fstS F σ)) (M (sndS F σ)) = 0) :
    ∀ i, Q i ((m i)⁻¹ • M i) := by
  classical
  set δ : ∀ i, V i := fun i => (m i)⁻¹ • M i with hδ
  have hMδ : ∀ i, M i = m i • δ i := fun i => by
    rw [hδ]; simp only [smul_smul, mul_inv_cancel₀ (hm i).ne', one_smul]
  -- the first identity: `(δᵢ · A²) = 0`
  have hLam : ∀ i, Lam i (δ i) = 0 := fun i => by
    rw [hδ]; simp only [map_smul, lam_eq_zero_of_orth F m hm Lam GA UA hGA M horth hE1 i,
      smul_zero]
  have hB : ∀ i, B i (δ i) (δ i) ≤ 0 := fun i => (hTI i _ (hLam i)).1
  -- orthogonality for `δ`
  have horthδ : ∀ σ : DoubleSurface F, UA σ (δ (fstS F σ)) = UA σ.swap (δ (sndS F σ)) := by
    intro σ
    have e1 : UA σ (δ (fstS F σ)) = UA σ (M (fstS F σ)) / m (fstS F σ) := by
      rw [hδ]; simp only [map_smul, smul_eq_mul]; ring
    have e2 : UA σ.swap (δ (sndS F σ)) = UA σ.swap (M (sndS F σ)) / m (sndS F σ) := by
      calc UA σ.swap (δ (sndS F σ)) = (m (sndS F σ))⁻¹ • UA σ.swap (M (sndS F σ)) :=
            LinearMap.map_smul (UA σ.swap) _ (M (sndS F σ))
        _ = _ := by rw [smul_eq_mul]; ring
    rw [e1, e2, horth σ]
  have hW : ∀ σ : DoubleSurface F, U σ (δ (fstS F σ)) (δ (fstS F σ)) -
      2 * C σ (δ (fstS F σ)) (δ (sndS F σ)) + U σ.swap (δ (sndS F σ)) (δ (sndS F σ)) ≤ 0 :=
    fun σ => hSI σ _ _ (horthδ σ)
  -- the second identity, in terms of `δ`
  have hGi : ∀ i, G i (M i) (M i) = -(m i * B i (δ i) (δ i)) -
      ∑ σ : DoubleSurface F, if fstS F σ = i then
        m (fstS F σ) * m (sndS F σ) * U σ (δ (fstS F σ)) (δ (fstS F σ)) else 0 := by
    intro i
    have h := hG δ i
    have hmi := (hm i).ne'
    have e : G i (M i) (M i) = m i * m i * G i (δ i) (δ i) := by
      rw [hMδ i]; simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]; ring
    have e' : ∀ σ : DoubleSurface F, (if fstS F σ = i then
        m (fstS F σ) * m (sndS F σ) * U σ (δ (fstS F σ)) (δ (fstS F σ)) else 0) =
        m i * (if fstS F σ = i then m (sndS F σ) * U σ (δ (fstS F σ)) (δ (fstS F σ)) else 0) := by
      intro σ; split_ifs with hσ
      · subst hσ; ring
      · ring
    rw [Finset.sum_congr rfl fun σ _ => e' σ, ← Finset.mul_sum, e]
    linear_combination (-m i) * h
  have hCσ : ∀ σ : DoubleSurface F, C σ (M (fstS F σ)) (M (sndS F σ)) =
      m (fstS F σ) * m (sndS F σ) * C σ (δ (fstS F σ)) (δ (sndS F σ)) := by
    intro σ
    rw [hMδ (fstS F σ), hMδ (sndS F σ)]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]; ring
  have hfib : ∑ i, (∑ σ : DoubleSurface F, if fstS F σ = i then
      m (fstS F σ) * m (sndS F σ) * U σ (δ (fstS F σ)) (δ (fstS F σ)) else 0) =
      ∑ σ : DoubleSurface F, m (fstS F σ) * m (sndS F σ) * U σ (δ (fstS F σ)) (δ (fstS F σ)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.sum_ite_eq]; simp
  have hUsym : ∑ σ : DoubleSurface F, m (fstS F σ) * m (sndS F σ) *
      U σ (δ (fstS F σ)) (δ (fstS F σ)) =
      ∑ σ : DoubleSurface F, m (fstS F σ) * m (sndS F σ) *
        U σ.swap (δ (sndS F σ)) (δ (sndS F σ)) := by
    rw [← sum_swap F]
    refine Finset.sum_congr rfl fun σ _ => ?_
    exact (by ring : m (sndS F σ) * m (fstS F σ) * U σ.swap (δ (sndS F σ)) (δ (sndS F σ)) =
      m (fstS F σ) * m (sndS F σ) * U σ.swap (δ (sndS F σ)) (δ (sndS F σ)))
  have hkey : ∑ i, m i * B i (δ i) (δ i) + (1 / 2 : ℚ) * ∑ σ : DoubleSurface F,
      m (fstS F σ) * m (sndS F σ) * (U σ (δ (fstS F σ)) (δ (fstS F σ)) -
        2 * C σ (δ (fstS F σ)) (δ (sndS F σ)) + U σ.swap (δ (sndS F σ)) (δ (sndS F σ))) = 0 := by
    simp_rw [hGi, hCσ, Finset.sum_sub_distrib, Finset.sum_neg_distrib, hfib] at hE2
    have : ∑ σ : DoubleSurface F, m (fstS F σ) * m (sndS F σ) *
        (U σ (δ (fstS F σ)) (δ (fstS F σ)) - 2 * C σ (δ (fstS F σ)) (δ (sndS F σ)) +
          U σ.swap (δ (sndS F σ)) (δ (sndS F σ))) =
        ∑ σ : DoubleSurface F, m (fstS F σ) * m (sndS F σ) * U σ (δ (fstS F σ)) (δ (fstS F σ)) -
        2 * ∑ σ : DoubleSurface F, m (fstS F σ) * m (sndS F σ) *
          C σ (δ (fstS F σ)) (δ (sndS F σ)) +
        ∑ σ : DoubleSurface F, m (fstS F σ) * m (sndS F σ) *
          U σ.swap (δ (sndS F σ)) (δ (sndS F σ)) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun σ _ => ?_
      ring
    rw [this, ← hUsym]
    linear_combination -hE2
  have hnn1 : ∀ i ∈ (Finset.univ : Finset F.support), 0 ≤ -(m i * B i (δ i) (δ i)) :=
    fun i _ => by nlinarith [hm i, hB i]
  have hnn2 : ∀ σ ∈ (Finset.univ : Finset (DoubleSurface F)),
      0 ≤ -(m (fstS F σ) * m (sndS F σ) * (U σ (δ (fstS F σ)) (δ (fstS F σ)) -
        2 * C σ (δ (fstS F σ)) (δ (sndS F σ)) + U σ.swap (δ (sndS F σ)) (δ (sndS F σ)))) :=
    fun σ _ => by
      have := mul_pos (hm (fstS F σ)) (hm (sndS F σ))
      nlinarith [hW σ]
  have hs1 := Finset.sum_nonneg hnn1
  have hs2 := Finset.sum_nonneg hnn2
  rw [Finset.sum_neg_distrib] at hs1 hs2
  have h0 : ∑ i, -(m i * B i (δ i) (δ i)) = 0 := by
    rw [Finset.sum_neg_distrib]; linarith
  intro i
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn1).1 h0 i (Finset.mem_univ i)
  exact (hTI i _ (hLam i)).2
    ((mul_eq_zero.1 (neg_eq_zero.1 this)).resolve_left (hm i).ne')

/-- **The numerical core.** -/
private theorem exists_of_numerical (m : F.support → ℚ) (hm : ∀ i, 0 < m i)
    (Zl : (DoubleSurface F → ℚ) →ₗ[ℚ] (∀ i, V i)) (ρv : ∀ σ : DoubleSurface F, V (fstS F σ))
    (B G : ∀ i, V i →ₗ[ℚ] V i →ₗ[ℚ] ℚ) (Lam GA : ∀ i, V i →ₗ[ℚ] ℚ)
    (U : ∀ σ : DoubleSurface F, V (fstS F σ) →ₗ[ℚ] V (fstS F σ) →ₗ[ℚ] ℚ)
    (C : ∀ σ : DoubleSurface F, V (fstS F σ) →ₗ[ℚ] V (sndS F σ) →ₗ[ℚ] ℚ)
    (UA : ∀ σ : DoubleSurface F, V (fstS F σ) →ₗ[ℚ] ℚ) (Q : ∀ i, V i → Prop)
    (hZlin : ∀ (f : ∀ i, V i →ₗ[ℚ] ℚ) (a : DoubleSurface F → ℚ),
      ∑ i, f i (Zl a i) = ∑ σ : DoubleSurface F, a σ * f (fstS F σ) (ρv σ))
    (hRA : ∀ (σ : DoubleSurface F) x, UA σ x = B (fstS F σ) x (ρv σ))
    (hWI : ∀ a ∈ orientedSurfaceCoefficients F,
      ∑ i, B i (Zl a i) (Zl a i) / m i = 0 → a = 0)
    (hGA : ∀ (x : ∀ i, V i) i, -m i * GA i (x i) = Lam i (x i) +
      ∑ σ : DoubleSurface F, if fstS F σ = i then m (sndS F σ) * UA σ (x (fstS F σ)) else 0)
    (hG : ∀ (x : ∀ i, V i) i, -m i * G i (x i) (x i) = B i (x i) (x i) +
      ∑ σ : DoubleSurface F,
        if fstS F σ = i then m (sndS F σ) * U σ (x (fstS F σ)) (x (fstS F σ)) else 0)
    (hSI : ∀ (σ : DoubleSurface F) x y, UA σ x = UA σ.swap y →
      U σ x x - 2 * C σ x y + U σ.swap y y ≤ 0)
    (hTI : ∀ i x, Lam i x = 0 → B i x x ≤ 0 ∧ (B i x x = 0 → Q i x))
    (L : ∀ i, V i)
    (hKB : ∀ a ∈ orientedSurfaceCoefficients F,
      (∀ i, GA i ((L - Zl a) i) + ∑ σ : DoubleSurface F,
        (if sndS F σ = i then UA σ ((L - Zl a) (fstS F σ)) else 0) = 0) ∧
      ∑ i, G i ((L - Zl a) i) ((L - Zl a) i) +
        ∑ σ : DoubleSurface F, C σ ((L - Zl a) (fstS F σ)) ((L - Zl a) (sndS F σ)) = 0) :
    ∃ a ∈ orientedSurfaceCoefficients F, ∀ i, Q i ((m i)⁻¹ • (L i - Zl a i)) := by
  obtain ⟨a, ha, horth⟩ :=
    exists_mem_orientedSurfaceCoefficients_orth F m Zl UA ρv B hZlin hRA hWI L
  obtain ⟨hE1, hE2⟩ := hKB a ha
  exact ⟨a, ha, forall_of_orth F m hm B G Lam GA U C UA Q hGA hG hSI hTI (L - Zl a) horth hE1 hE2⟩

end Algebra

/-! ### Components and double surfaces of an snc divisor -/

section SNC

open MMP TopologicalSpace

/-- The Cartier divisor `εᵢ` of a component `Eᵢ` of `B` is effective with closed subscheme
`Eᵢ`. -/
private theorem exists_isEffective_eps (k : Type) [Field k] {Z : Scheme.{0}}
    (sZ : Z ⟶ Spec (.of k)) (hvar : Mori.IsVariety k sZ) (hsm : IsSmoothScheme sZ)
    {B : Divisor Z} (ε : B.support → Z.CartierDivisor)
    (hε : ∀ i, MMP.Intersection.IsWeilDivisorOfCartier (ε i) (Finsupp.single i.1 1))
    (i : B.support) :
    ∃ h : MMP.Intersection.IsEffective (ε i),
      MMP.CartierDivisor.subscheme (ε i) h = i.1.idealSheaf :=
  haveI := hvar
  let ⟨h, e⟩ := (hε i).isEffective_and_subscheme_eq_of_isSmoothScheme sZ hsm
  ⟨h, e⟩

/-- The Cartier divisor `π_P` of a prime divisor `P` of a component `Eᵢ` is effective with closed
subscheme `P`: the component is a smooth variety. -/
public theorem exists_isEffective_pi (k : Type) [Field k] {Z : Scheme.{0}}
    (sZ : Z ⟶ Spec (.of k)) [IsProper sZ] {B : Divisor Z} (hB : B.IsSNC sZ)
    (π : ∀ i : B.support, Mori.PrimeDivisor i.1.idealSheaf.subscheme →
      i.1.idealSheaf.subscheme.CartierDivisor)
    (hπ : ∀ i P, MMP.Intersection.IsWeilDivisorOfCartier (π i P) (Finsupp.single P 1))
    (i : B.support) (P : Mori.PrimeDivisor i.1.idealSheaf.subscheme) :
    ∃ h : MMP.Intersection.IsEffective (π i P),
      MMP.CartierDivisor.subscheme (π i P) h = P.idealSheaf := by
  have := i.1.integral
  have : AlgebraicGeometry.IsVariety k (i.1.idealSheaf.subschemeι ≫ sZ) := ⟨⟩
  obtain ⟨h, e⟩ := (hπ i P).isEffective_and_subscheme_eq_of_isSmoothScheme _ (hB.1 i.1 i.2)
  exact ⟨h, e⟩

/-- A component `E_b` of an snc divisor has simple normal crossings with the other components. -/
private theorem hasSNCWith_component {k : Type} [Field k] {Z : Scheme.{0}}
    {sZ : Z ⟶ Spec (.of k)} {B : Divisor Z}
    (hB : B.IsSNC sZ) (b : B.support) :
    MMP.Resolution.HasSNCWith (fun c : {c : B.support // c ≠ b} => c.1.1.idealSheaf)
      b.1.idealSheaf := by
  intro x hx
  obtain ⟨n, z, j, hz, hj, hI⟩ := hB.2 x
  refine ⟨n, z, fun i => j ⟨i.1.1.1, i.1.1.2, i.2⟩, {j ⟨b.1, b.2, hx⟩}, hz,
    fun i => hI ⟨i.1.1.1, i.1.1.2, i.2⟩, ?_, ?_⟩
  · intro i i' h
    have := hj h
    exact Subtype.ext (Subtype.ext (Subtype.ext (Subtype.mk.inj this)))
  · rw [Finset.coe_singleton, Set.image_singleton]
    exact hI ⟨b.1, b.2, hx⟩

/-- Distinct prime divisors do not contain one another. -/
private theorem not_support_subset_of_ne {Z : Scheme.{0}} {E E' : Mori.PrimeDivisor Z}
    (h : E ≠ E') : ¬ (E.support ⊆ E'.support) := by
  intro hsub
  have hη : E.genericPoint ∈ E'.support := hsub (by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl)
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hη
  have hsp : E'.genericPoint ⤳ E.genericPoint := specializes_iff_mem_closure.2 hη
  by_cases he : E.genericPoint = E'.genericPoint
  · exact h (AlgebraicGeometry.PrimeDivisor.genericPoint_injective he)
  · have h2 := Order.coheight_add_one_le
      (MMP.Intersection.lt_of_specializes_of_ne hsp he)
    rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint,
      AlgebraicGeometry.PrimeDivisor.coheight_genericPoint] at h2
    exact absurd h2 (by decide)

/-- No other component contains an irreducible component of `E_b`. -/
private theorem not_component_subset {Z : Scheme.{0}} {B : Divisor Z} (b : B.support)
    (c : {c : B.support // c ≠ b}) :
    ∀ W ∈ MMP.Resolution.componentsOf (b.1.idealSheaf.support : Set Z),
      ¬ W ⊆ (c.1.1.idealSheaf.support : Set Z) := by
  intro W hW hWc
  have hirr : IsIrreducible (b.1.idealSheaf.support : Set Z) := by
    change IsIrreducible (b.1.support : Set Z)
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact isIrreducible_singleton.closure
  have hWb : (b.1.idealSheaf.support : Set Z) ⊆ W := hW.2 ⟨hirr, le_rfl⟩ hW.1.2
  exact not_support_subset_of_ne (fun e => c.2 (Subtype.ext e.symm)) (hWb.trans hWc)

/-- **`E_a ∩ E_b` as a divisor on `E_b`.** For components `a ≠ b` of a reduced snc divisor, the
inverse image of `E_a` in `E_b` is a reduced effective Cartier divisor on `E_b`. -/
private theorem isEffectiveCartierDivisor_comap_component {k : Type} [Field k] {Z : Scheme.{0}}
    {sZ : Z ⟶ Spec (.of k)} [IsProper sZ] {B : Divisor Z} (hB : B.IsSNC sZ) {a b : B.support}
    (hab : a ≠ b) :
    Stacks.Divisors.IsEffectiveCartierDivisor (a.1.idealSheaf.comap b.1.idealSheaf.subschemeι) ∧
      IsReduced (a.1.idealSheaf.comap b.1.idealSheaf.subschemeι).subscheme := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  exact MMP.Resolution.isEffectiveCartierDivisor_and_isReduced_comap_of_hasSNCWith
    (hasSNCWith_component hB b) (not_component_subset b) ⟨a, hab⟩

/-- **`𝒪(εₐ)|_{E_b} ≅ 𝒪_{E_b}(Eₐ ∩ E_b)`** for components `a ≠ b`. -/
private theorem nonempty_pullback_eps_iso (k : Type) [Field k] {Z : Scheme.{0}}
    (sZ : Z ⟶ Spec (.of k)) [IsProper sZ] (hvar : Mori.IsVariety k sZ) (hsm : IsSmoothScheme sZ)
    {B : Divisor Z} (hB : B.IsSNC sZ) (ε : B.support → Z.CartierDivisor)
    (hε : ∀ i, MMP.Intersection.IsWeilDivisorOfCartier (ε i) (Finsupp.single i.1 1))
    {a b : B.support} (hab : a ≠ b) :
    Nonempty ((Scheme.Modules.pullback b.1.idealSheaf.subschemeι).obj
        (MMP.CartierDivisor.sheaf (ε a)) ≅
      (Stacks.Divisors.invertibleSheaf' (a.1.idealSheaf.comap b.1.idealSheaf.subschemeι) :
        b.1.idealSheaf.subscheme.Modules)) := by
  obtain ⟨he, hsub⟩ := exists_isEffective_eps k sZ hvar hsm ε hε a
  have hE : Stacks.Divisors.IsEffectiveCartierDivisor a.1.idealSheaf :=
    hsub ▸ MMP.CartierDivisor.isEffectiveCartierDivisor_subscheme he
  have hP : Stacks.Divisors.IsPullbackDefined b.1.idealSheaf.subschemeι a.1.idealSheaf :=
    (isEffectiveCartierDivisor_comap_component hB hab).1
  exact ⟨(Scheme.Modules.pullback b.1.idealSheaf.subschemeι).mapIso
      (MMP.CartierDivisor.sheafIsoInvertibleSheaf (ε a) he ≪≫
        eqToIso (congrArg Stacks.Divisors.invertibleSheaf' hsub)) ≪≫
    Stacks.Divisors.invertibleSheafPullbackIso b.1.idealSheaf.subschemeι a.1.idealSheaf⟩

/-- At each point of `Eₐ ∩ E_b`, the ideal of `Eₐ ∩ E_b` in `E_b` is generated by one member of a
regular system of parameters. -/
private theorem stalk_comap_component {k : Type} [Field k] {Z : Scheme.{0}}
    {sZ : Z ⟶ Spec (.of k)} [IsProper sZ] {B : Divisor Z} (hB : B.IsSNC sZ) {a b : B.support}
    (hab : a ≠ b) :
    ∀ y ∈ (a.1.idealSheaf.comap b.1.idealSheaf.subschemeι).support, ∃ (m : ℕ)
      (w : Fin m → b.1.idealSheaf.subscheme.presheaf.stalk y) (j : Fin m),
      Mori.IsRegularSystemOfParameters w ∧
        IdealSheafData.stalk (a.1.idealSheaf.comap b.1.idealSheaf.subschemeι) y =
          Ideal.span {w j} := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  intro y hy
  obtain ⟨m, w, c', hw, hc, -⟩ := MMP.Resolution.exists_coordinates_comap_subschemeι_of_hasSNCWith
    (hasSNCWith_component hB b) (not_component_subset b) y
  exact ⟨m, w, c' ⟨⟨a, hab⟩, hy⟩, hw, hc ⟨⟨a, hab⟩, hy⟩⟩

/-- Every double surface `S ⊆ Eᵢ ∩ Eⱼ` is (the image of) a prime divisor of `Eᵢ`: `S` is a
connected component of `Eⱼ ∩ Eᵢ` read on `Eᵢ`, a divisor cut out by regular parameters. -/
public theorem exists_primeDivisor_image_support_eq {k : Type} [Field k] {Z : Scheme.{0}}
    {sZ : Z ⟶ Spec (.of k)} [IsProper sZ] {B : Divisor Z} (hB : B.IsSNC sZ)
    (σ : DoubleSurface B) :
    ∃ P : Mori.PrimeDivisor σ.fst.idealSheaf.subscheme,
      σ.fst.idealSheaf.subschemeι '' P.support = σ.carrier := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  have : IsNoetherian Z := ⟨⟩
  set ι := σ.fst.idealSheaf.subschemeι
  have : IsLocallyNoetherian σ.fst.idealSheaf.subscheme :=
    isLocallyNoetherian_of_isClosedImmersion ι
  have : NoetherianSpace σ.fst.idealSheaf.subscheme :=
    ι.isClosedEmbedding.isEmbedding.noetherianSpace
  have hab : (⟨σ.snd, σ.snd_mem⟩ : B.support) ≠ ⟨σ.fst, σ.fst_mem⟩ :=
    fun h => σ.fst_ne_snd (congrArg Subtype.val h).symm
  set D' := σ.snd.idealSheaf.comap ι
  obtain ⟨x, hx, hxc⟩ := σ.isComponent
  have hrange : Set.range ι = (σ.fst.idealSheaf.support : Set Z) := by
    rw [← σ.fst.idealSheaf.range_subschemeι]
  obtain ⟨y, rfl⟩ : x ∈ Set.range ι := hrange ▸ hx.1
  have hyD : y ∈ (D'.support : Set _) := by
    rw [Scheme.IdealSheafData.support_comap]; exact hx.2
  have hD := stalk_comap_component (B := B) hB (a := ⟨σ.snd, σ.snd_mem⟩)
    (b := ⟨σ.fst, σ.fst_mem⟩) hab
  obtain ⟨P, hP⟩ := MMP.Mori.exists_primeDivisor_support_eq_connectedComponentIn D' hD hyD
  refine ⟨P, ?_⟩
  have himg : ι '' (D'.support : Set _) = σ.fst.support ∩ σ.snd.support := by
    apply subset_antisymm
    · rintro _ ⟨w, hw, rfl⟩
      refine ⟨(hrange ▸ ⟨w, rfl⟩ : ι w ∈ (σ.fst.idealSheaf.support : Set Z)), ?_⟩
      have hw' : w ∈ ((σ.snd.idealSheaf.comap ι).support : Set _) := hw
      rw [Scheme.IdealSheafData.support_comap] at hw'
      exact hw'
    · rintro z ⟨h1, h2⟩
      obtain ⟨w, rfl⟩ : z ∈ Set.range ι := hrange ▸ h1
      refine ⟨w, ?_, rfl⟩
      change w ∈ ((σ.snd.idealSheaf.comap ι).support : Set _)
      rw [Scheme.IdealSheafData.support_comap]
      exact h2
  rw [hP, MMP.Mori.image_connectedComponentIn_of_isEmbedding ι.isClosedEmbedding.isEmbedding hyD,
    himg, hxc]

/-- The prime divisor `ρ(σ)` of `Eᵢ` underlying a double surface `σ` of `(Eᵢ, Eⱼ)`. -/
@[expose]
public noncomputable def rho {k : Type} [Field k] {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of k)}
    [IsProper sZ] {B : Divisor Z} (hB : B.IsSNC sZ) (σ : DoubleSurface B) :
    Mori.PrimeDivisor σ.fst.idealSheaf.subscheme :=
  (exists_primeDivisor_image_support_eq hB σ).choose

public theorem image_support_rho {k : Type} [Field k] {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of k)}
    [IsProper sZ] {B : Divisor Z} (hB : B.IsSNC sZ) (σ : DoubleSurface B) :
    σ.fst.idealSheaf.subschemeι '' (rho hB σ).support = σ.carrier :=
  (exists_primeDivisor_image_support_eq hB σ).choose_spec

/-- The closure of the image of the generic point of `ρ(σ)` is the double surface. -/
private theorem closure_genericPoint_rho {k : Type} [Field k] {Z : Scheme.{0}}
    {sZ : Z ⟶ Spec (.of k)} [IsProper sZ] {B : Divisor Z} (hB : B.IsSNC sZ)
    (σ : DoubleSurface B) :
    closure {σ.fst.idealSheaf.subschemeι (rho hB σ).genericPoint} = σ.carrier := by
  rw [← Set.image_singleton, σ.fst.idealSheaf.subschemeι.isClosedEmbedding.closure_image_eq,
    ← AlgebraicGeometry.PrimeDivisor.support_eq_closure, image_support_rho]

/-- **Double surfaces of a component are determined by their surface.** Two double surfaces with
the same first component and the same surface are equal: were their second components distinct,
the surface would lie in three components, and at its generic point, of coheight one on `Eᵢ`,
two distinct members of a regular system of parameters of `𝒪_{Eᵢ}` would cut out the other two. -/
private theorem eq_of_fst_eq_of_carrier_eq {k : Type} [Field k] {Z : Scheme.{0}}
    {sZ : Z ⟶ Spec (.of k)} [IsProper sZ] {B : Divisor Z} (hB : B.IsSNC sZ)
    {σ τ : DoubleSurface B} (h₁ : σ.fst = τ.fst) (h₃ : σ.carrier = τ.carrier) : σ = τ := by
  by_cases h₂ : σ.snd = τ.snd
  · exact DoubleSurface.ext h₁ h₂ h₃
  exfalso
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  set b : B.support := ⟨σ.fst, σ.fst_mem⟩
  set ι := σ.fst.idealSheaf.subschemeι
  set η := (rho hB σ).genericPoint
  have hηS : ι η ∈ σ.carrier := by
    rw [← image_support_rho hB σ]
    refine ⟨η, ?_, rfl⟩
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  have hτS : ι η ∈ τ.carrier := h₃ ▸ hηS
  obtain ⟨m, w, c', hw, -, hinj⟩ := MMP.Resolution.exists_coordinates_comap_subschemeι_of_hasSNCWith
    (hasSNCWith_component hB b) (not_component_subset b) η
  have hne1 : (⟨σ.snd, σ.snd_mem⟩ : B.support) ≠ b :=
    fun h => σ.fst_ne_snd (congrArg Subtype.val h).symm
  have hne2 : (⟨τ.snd, τ.snd_mem⟩ : B.support) ≠ b :=
    fun h => τ.fst_ne_snd (h₁ ▸ (congrArg Subtype.val h).symm)
  have hm1 : η ∈ ((σ.snd.idealSheaf.comap ι).support : Set _) := by
    rw [Scheme.IdealSheafData.support_comap]; exact (σ.carrier_subset hηS).2
  have hm2 : η ∈ ((τ.snd.idealSheaf.comap ι).support : Set _) := by
    rw [Scheme.IdealSheafData.support_comap]; exact (τ.carrier_subset hτS).2
  have hc : c' ⟨⟨_, hne1⟩, hm1⟩ ≠ c' ⟨⟨_, hne2⟩, hm2⟩ := fun h =>
    h₂ (congrArg (fun e => e.1.1.1) (hinj h))
  have hdim := hw.2
  rw [ringKrullDim_stalk_eq_coheight, AlgebraicGeometry.PrimeDivisor.coheight_genericPoint] at hdim
  have hm : m = 1 := by exact_mod_cast hdim.symm
  subst hm
  exact hc (Subsingleton.elim _ _)

/-- A double surface is closed. -/
private theorem isClosed_carrier {Z : Scheme.{0}} {B : Divisor Z} (σ : DoubleSurface B) :
    IsClosed σ.carrier := by
  obtain ⟨x, hx, hxc⟩ := σ.isComponent
  rw [← hxc, connectedComponentIn_eq_image hx]
  exact (σ.fst.idealSheaf.support.isClosed.inter
    σ.snd.idealSheaf.support.isClosed).isClosedEmbedding_subtypeVal.isClosedMap _
    isClosed_connectedComponent

/-- On a Noetherian scheme the rest of `Eᵢ ∩ Eⱼ` off a double surface is closed: it is the union of
the finitely many other connected components. -/
private theorem isClosed_inter_diff_carrier {Z : Scheme.{0}} [NoetherianSpace Z] {B : Divisor Z}
    (σ : DoubleSurface B) :
    IsClosed ((σ.fst.support ∩ σ.snd.support) \ σ.carrier) := by
  have hF : IsClosed (σ.fst.support ∩ σ.snd.support) :=
    σ.fst.idealSheaf.support.isClosed.inter σ.snd.idealSheaf.support.isClosed
  have hfin := DoubleSurface.finite_connectedComponentIn hF
  have heq : (σ.fst.support ∩ σ.snd.support) \ σ.carrier =
      ⋃ C ∈ {C | ∃ x ∈ σ.fst.support ∩ σ.snd.support,
        connectedComponentIn (σ.fst.support ∩ σ.snd.support) x = C} \ {σ.carrier}, C := by
    ext z
    simp only [Set.mem_sdiff, Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_singleton_iff,
      exists_prop]
    constructor
    · rintro ⟨hz, hzc⟩
      refine ⟨_, ⟨⟨z, hz, rfl⟩, fun h => hzc (h ▸ mem_connectedComponentIn hz)⟩,
        mem_connectedComponentIn hz⟩
    · rintro ⟨C, ⟨⟨x, hx, rfl⟩, hne⟩, hzC⟩
      refine ⟨connectedComponentIn_subset _ _ hzC, fun hzc => hne ?_⟩
      rw [σ.carrier_eq_connectedComponentIn hzc, connectedComponentIn_eq hzC]
  rw [heq]
  refine hfin.sdiff.isClosed_biUnion fun C hC => ?_
  obtain ⟨⟨x, hx, rfl⟩, -⟩ := hC
  rw [connectedComponentIn_eq_image hx]
  exact hF.isClosedEmbedding_subtypeVal.isClosedMap _ isClosed_connectedComponent

/-- `Eⱼ ∩ Eᵢ = ρ(σ) ⊔ T'` on `Eᵢ`, with `T'` (the other connected components) disjoint from
`ρ(σ)`. -/
private theorem exists_closeds_sup_rho {k : Type} [Field k] {Z : Scheme.{0}}
    {sZ : Z ⟶ Spec (.of k)} [IsProper sZ] {B : Divisor Z} (hB : B.IsSNC sZ)
    (σ : DoubleSurface B) :
    ∃ T' : Closeds σ.fst.idealSheaf.subscheme,
      (rho hB σ).idealSheaf.support ⊔ T' =
        (σ.snd.idealSheaf.comap σ.fst.idealSheaf.subschemeι).support ∧
      Disjoint (rho hB σ).idealSheaf.support T' := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  have : IsNoetherian Z := ⟨⟩
  set ι := σ.fst.idealSheaf.subschemeι
  set P := rho hB σ
  have hrange : Set.range ι = (σ.fst.idealSheaf.support : Set Z) := by
    rw [← σ.fst.idealSheaf.range_subschemeι]
  have hPS : (P.support : Set _) = ι ⁻¹' σ.carrier := by
    rw [← image_support_rho hB σ, Set.preimage_image_eq _ ι.isClosedEmbedding.injective]
  let T' : TopologicalSpace.Closeds σ.fst.idealSheaf.subscheme :=
    ⟨ι ⁻¹' ((σ.fst.support ∩ σ.snd.support) \ σ.carrier),
      (isClosed_inter_diff_carrier σ).preimage ι.continuous⟩
  refine ⟨T', ?_, ?_⟩
  · apply TopologicalSpace.Closeds.ext
    rw [TopologicalSpace.Closeds.coe_sup]
    change (P.support : Set _) ∪ _ = ((σ.snd.idealSheaf.comap ι).support : Set _)
    rw [Scheme.IdealSheafData.support_comap, hPS]
    ext z
    simp only [T', TopologicalSpace.Closeds.coe_mk, TopologicalSpace.Closeds.coe_preimage,
      Set.mem_union, Set.mem_preimage, Set.mem_sdiff, Set.mem_inter_iff]
    have hz : ι z ∈ (σ.fst.idealSheaf.support : Set Z) := hrange ▸ ⟨z, rfl⟩
    constructor
    · rintro (h | h)
      · exact (σ.carrier_subset h).2
      · exact h.1.2
    · intro h
      by_cases hc : ι z ∈ σ.carrier
      · exact Or.inl hc
      · exact Or.inr ⟨⟨hz, h⟩, hc⟩
  · rw [disjoint_iff]
    apply TopologicalSpace.Closeds.ext
    rw [TopologicalSpace.Closeds.coe_inf, TopologicalSpace.Closeds.coe_bot]
    change (P.support : Set _) ∩ _ = ∅
    rw [hPS]
    ext z
    simp only [T', TopologicalSpace.Closeds.coe_mk, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_sdiff, Set.mem_empty_iff_false, iff_false, not_and, not_not]
    exact fun h _ => h

/-- The coefficient of `Zᵢ(a)` along `ρ(σ)` is `a σ`. -/
private theorem surfaceCoefficientCoeff_rho {k : Type} [Field k] {Z : Scheme.{0}}
    {sZ : Z ⟶ Spec (.of k)} [IsProper sZ] {B : Divisor Z} (hB : B.IsSNC sZ)
    (a : DoubleSurface B → ℚ) (σ : DoubleSurface B) :
    surfaceCoefficientCoeff a σ.fst (rho hB σ) = a σ := by
  rw [surfaceCoefficientCoeff]
  have hcl := closure_genericPoint_rho hB σ
  refine (finsum_eq_single _ ⟨σ, rfl, hcl.symm⟩ fun τ hτ => absurd ?_ hτ).trans rfl
  exact Subtype.ext (eq_of_fst_eq_of_carrier_eq hB τ.2.1 (τ.2.2.trans hcl))

/-- The surface of a double surface `σ` of `(Eᵢ, Eⱼ)` is the image of `ρ(σ)` in `Z`. -/
private theorem range_comp_rho {k : Type} [Field k] {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of k)}
    [IsProper sZ] {B : Divisor Z} (hB : B.IsSNC sZ) (σ : DoubleSurface B) :
    Set.range ((rho hB σ).idealSheaf.subschemeι ≫ σ.fst.idealSheaf.subschemeι) = σ.carrier := by
  rw [← image_support_rho hB σ, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  congr 1
  exact (rho hB σ).idealSheaf.range_subschemeι

/-- `ρ(σ)` read on a component `E` equal to the first component of `σ`. -/
private noncomputable def rhoOf {k : Type} [Field k] {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of k)}
    [IsProper sZ] {B : Divisor Z} (hB : B.IsSNC sZ) {E : Mori.PrimeDivisor Z}
    (σ : DoubleSurface B) (h : σ.fst = E) : Mori.PrimeDivisor E.idealSheaf.subscheme :=
  h ▸ rho hB σ

private theorem image_support_rhoOf {k : Type} [Field k] {Z : Scheme.{0}}
    {sZ : Z ⟶ Spec (.of k)} [IsProper sZ] {B : Divisor Z} (hB : B.IsSNC sZ)
    {E : Mori.PrimeDivisor Z} (σ : DoubleSurface B) (h : σ.fst = E) :
    E.idealSheaf.subschemeι '' (rhoOf hB σ h).support = σ.carrier := by
  subst h; exact image_support_rho hB σ

private theorem surfaceCoefficientCoeff_rhoOf {k : Type} [Field k] {Z : Scheme.{0}}
    {sZ : Z ⟶ Spec (.of k)} [IsProper sZ] {B : Divisor Z} (hB : B.IsSNC sZ)
    (a : DoubleSurface B → ℚ) {E : Mori.PrimeDivisor Z} (σ : DoubleSurface B) (h : σ.fst = E) :
    surfaceCoefficientCoeff a E (rhoOf hB σ h) = a σ := by
  subst h; exact surfaceCoefficientCoeff_rho hB a σ

/-- The image of the support of a prime divisor of `E` is the closure of the image of its generic
point. -/
private theorem image_support_eq_closure {Z : Scheme.{0}} {E : Mori.PrimeDivisor Z}
    (P : Mori.PrimeDivisor E.idealSheaf.subscheme) :
    E.idealSheaf.subschemeι '' P.support = closure {E.idealSheaf.subschemeι P.genericPoint} := by
  rw [← Set.image_singleton, E.idealSheaf.subschemeι.isClosedEmbedding.closure_image_eq,
    ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]

/-- Prime divisors of `E` with the same image in `Z` are equal. -/
private theorem eq_of_image_support_eq {Z : Scheme.{0}} {E : Mori.PrimeDivisor Z}
    {P Q : Mori.PrimeDivisor E.idealSheaf.subscheme}
    (h : E.idealSheaf.subschemeι '' P.support = E.idealSheaf.subschemeι '' Q.support) : P = Q := by
  rw [image_support_eq_closure, image_support_eq_closure] at h
  have hQ : IsGenericPoint (E.idealSheaf.subschemeι Q.genericPoint)
      (closure {E.idealSheaf.subschemeι P.genericPoint}) := by
    rw [h]; exact isGenericPoint_closure
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (E.idealSheaf.subschemeι.isClosedEmbedding.injective (isGenericPoint_closure.eq hQ))

private theorem rhoOf_injective {k : Type} [Field k] {Z : Scheme.{0}}
    {sZ : Z ⟶ Spec (.of k)} [IsProper sZ] {B : Divisor Z} (hB : B.IsSNC sZ)
    {E : Mori.PrimeDivisor Z} {σ τ : DoubleSurface B} (h : σ.fst = E) (h' : τ.fst = E)
    (he : rhoOf hB σ h = rhoOf hB τ h') : σ = τ := by
  refine eq_of_fst_eq_of_carrier_eq hB (h.trans h'.symm) ?_
  rw [← image_support_rhoOf hB σ h, ← image_support_rhoOf hB τ h', he]

/-- **(2c) The coefficient of `Zᵢ(a)` vanishes off the prime divisors `ρ(σ)`.** -/
private theorem surfaceCoefficientCoeff_eq_zero {k : Type} [Field k] {Z : Scheme.{0}}
    {sZ : Z ⟶ Spec (.of k)} [IsProper sZ] {B : Divisor Z} (hB : B.IsSNC sZ)
    (a : DoubleSurface B → ℚ) {E : Mori.PrimeDivisor Z}
    (P : Mori.PrimeDivisor E.idealSheaf.subscheme)
    (hP : ∀ (σ : DoubleSurface B) (h : σ.fst = E), rhoOf hB σ h ≠ P) :
    surfaceCoefficientCoeff a E P = 0 := by
  rw [surfaceCoefficientCoeff]
  have : IsEmpty {σ : DoubleSurface B // σ.fst = E ∧
      σ.carrier = closure {E.idealSheaf.subschemeι P.genericPoint}} := by
    refine ⟨fun σ => hP σ.1 σ.2.1 (eq_of_image_support_eq ?_)⟩
    rw [image_support_rhoOf, σ.2.2, image_support_eq_closure]
  exact finsum_of_isEmpty _

/-- **(2d) `Zᵢ(a) = ∑_{σ ⊆ Eᵢ} a_σ ρ(σ)`**, as an expansion of finitely supported sums. -/
private theorem sum_surfaceCoefficientDivisor {k : Type} [Field k] {Z : Scheme.{0}}
    {sZ : Z ⟶ Spec (.of k)} [IsProper sZ] {B : Divisor Z} (hB : B.IsSNC sZ)
    (a : DoubleSurface B → ℚ) (E : Mori.PrimeDivisor Z)
    [Fintype {σ : DoubleSurface B // σ.fst = E}]
    {M : Type*} [AddCommMonoid M] (f : Mori.PrimeDivisor E.idealSheaf.subscheme → ℚ → M)
    (hf : ∀ P, f P 0 = 0) :
    (surfaceCoefficientDivisor a E).sum f =
      ∑ σ : {σ : DoubleSurface B // σ.fst = E}, f (rhoOf hB σ.1 σ.2) (a σ.1) := by
  classical
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  have : IsNoetherian Z := ⟨⟩
  have hsub : (surfaceCoefficientDivisor a E).support ⊆
      Finset.univ.image fun σ : {σ : DoubleSurface B // σ.fst = E} => rhoOf hB σ.1 σ.2 := by
    intro P hP
    by_contra hnot
    refine Finsupp.mem_support_iff.mp hP ?_
    rw [← DivisorWithCoeffs.coeff_apply, coeff_surfaceCoefficientDivisor]
    refine surfaceCoefficientCoeff_eq_zero hB a P fun σ h he => hnot ?_
    exact Finset.mem_image.mpr ⟨⟨σ, h⟩, Finset.mem_univ _, he⟩
  rw [Finsupp.sum_of_support_subset _ hsub _ fun P _ => hf P, Finset.sum_image
    fun σ _ τ _ he => Subtype.ext (rhoOf_injective hB σ.2 τ.2 he)]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← DivisorWithCoeffs.coeff_apply, coeff_surfaceCoefficientDivisor,
    surfaceCoefficientCoeff_rhoOf]

/-- Distinct double surfaces of the same ordered pair `(Eᵢ, Eⱼ)` give disjoint prime divisors
`ρ` of `Eᵢ`. -/
private theorem disjoint_support_rhoOf {k : Type} [Field k] {Z : Scheme.{0}}
    {sZ : Z ⟶ Spec (.of k)} [IsProper sZ] {B : Divisor Z} (hB : B.IsSNC sZ)
    {E : Mori.PrimeDivisor Z} {σ τ : DoubleSurface B} (h : σ.fst = E) (h' : τ.fst = E)
    (h₂ : σ.snd = τ.snd) (hne : σ ≠ τ) :
    Disjoint (rhoOf hB σ h).support (rhoOf hB τ h').support := by
  have hd := DoubleSurface.disjoint_carrier (h.trans h'.symm) h₂ hne
  rw [← image_support_rhoOf hB σ h, ← image_support_rhoOf hB τ h'] at hd
  exact (Set.disjoint_image_iff E.idealSheaf.subschemeι.isClosedEmbedding.injective).mp hd

/-- At a point of `ρ(σ)`, the ideal of `ρ(σ)` is that of `Eⱼ ∩ Eᵢ` on `Eᵢ`. -/
private theorem stalk_rho {k : Type} [Field k] {Z : Scheme.{0}}
    {sZ : Z ⟶ Spec (.of k)} [IsProper sZ] {B : Divisor Z} (hB : B.IsSNC sZ)
    (σ : DoubleSurface B) {x : σ.fst.idealSheaf.subscheme} (hx : x ∈ (rho hB σ).support) :
    IdealSheafData.stalk (rho hB σ).idealSheaf x =
      IdealSheafData.stalk (σ.snd.idealSheaf.comap σ.fst.idealSheaf.subschemeι) x := by
  have hab : (⟨σ.snd, σ.snd_mem⟩ : B.support) ≠ ⟨σ.fst, σ.fst_mem⟩ :=
    fun h => σ.fst_ne_snd (congrArg Subtype.val h).symm
  have := (isEffectiveCartierDivisor_comap_component hB hab).2
  have := (rho hB σ).integral
  obtain ⟨T', hST, hdisj⟩ := exists_closeds_sup_rho hB σ
  have hPV : (rho hB σ).idealSheaf =
      Scheme.IdealSheafData.vanishingIdeal (rho hB σ).idealSheaf.support :=
    Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme _ _ rfl
  rw [hPV]
  refine MMP.Mori.stalk_vanishingIdeal_eq_stalk_of_sup_eq _ _ T' hST fun hT => ?_
  have : x ∈ (((rho hB σ).idealSheaf.support ⊓ T' : Closeds _) : Set _) := ⟨hx, hT⟩
  rw [hdisj.eq_bot] at this
  exact this

private theorem mem_support_comap_snd_of_mem_rhoOf {k : Type} [Field k] {Z : Scheme.{0}}
    {sZ : Z ⟶ Spec (.of k)} [IsProper sZ] {B : Divisor Z} (hB : B.IsSNC sZ)
    {E : Mori.PrimeDivisor Z} (σ : DoubleSurface B) (h : σ.fst = E)
    {x : E.idealSheaf.subscheme} (hx : x ∈ (rhoOf hB σ h).support) :
    x ∈ (σ.snd.idealSheaf.comap E.idealSheaf.subschemeι).support := by
  have hxσ : E.idealSheaf.subschemeι x ∈ σ.carrier := by
    rw [← image_support_rhoOf hB σ h]
    exact ⟨x, hx, rfl⟩
  change x ∈ ((σ.snd.idealSheaf.comap E.idealSheaf.subschemeι).support : Set _)
  rw [Scheme.IdealSheafData.support_comap]
  exact (σ.carrier_subset hxσ).2

end SNC

/-- On a smooth complex variety every divisor `w` is the Weil divisor of a Cartier divisor. -/
private theorem exists_isWeilDivisorOfCartier {W : Scheme.{0}} [W.Over (Spec (.of ℂ))]
    [hv : MMP.Mori.IsVariety ℂ (W ↘ Spec (.of ℂ))]
    (hsm : MMP.Mori.IsSmoothScheme (W ↘ Spec (.of ℂ))) (w : MMP.Mori.Divisor W) :
    ∃ A : W.CartierDivisor, MMP.Intersection.IsWeilDivisorOfCartier A w := by
  haveI : IsIntegral W := hv.toIsIntegral
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (W ↘ Spec (.of ℂ))
  have hUFD := MMP.Intersection.uniqueFactorizationMonoid_stalk_of_isSmoothScheme hsm
  obtain ⟨A, hA⟩ := MMP.Resolution.Bridges.exists_isOrderAlong_of_weilDivisor hUFD
    (⟨fun P => w P, (mem_weilDivisor_iff _).mpr fun x =>
      ⟨Set.univ, Filter.univ_mem, w.support.finite_toSet.subset fun Z hZ => by
          by_cases h : w Z = 0
          · simp [h] at hZ
          · exact Finsupp.mem_support_iff.mpr h⟩⟩ : WeilDivisor W)
  exact ⟨A, hA⟩

private theorem isWeilDivisorOfCartier_add {W : Scheme.{0}} {A B : W.CartierDivisor}
    {w w' : MMP.Mori.Divisor W} (hA : MMP.Intersection.IsWeilDivisorOfCartier A w)
    (hB : MMP.Intersection.IsWeilDivisorOfCartier B w') :
    MMP.Intersection.IsWeilDivisorOfCartier (A + B) (w + w') := fun P =>
  (hA P).add (hB P)

private theorem isWeilDivisorOfCartier_nsmul {W : Scheme.{0}} {A : W.CartierDivisor}
    {w : MMP.Mori.Divisor W} (hA : MMP.Intersection.IsWeilDivisorOfCartier A w) (n : ℕ) :
    MMP.Intersection.IsWeilDivisorOfCartier (n • A) (n • w) := by
  induction n with
  | zero =>
    intro P
    simpa using MMP.Intersection.isOrderAlong_zero (MMP.Intersection.primeDivisorSubvariety P)
  | succ n ih =>
    rw [succ_nsmul, succ_nsmul]
    exact isWeilDivisorOfCartier_add ih hA

private theorem isWeilDivisorOfCartier_sum {W : Scheme.{0}} {ι : Type*} (s : Finset ι)
    {A : ι → W.CartierDivisor} {w : ι → MMP.Mori.Divisor W}
    (hA : ∀ l ∈ s, MMP.Intersection.IsWeilDivisorOfCartier (A l) (w l)) :
    MMP.Intersection.IsWeilDivisorOfCartier (∑ l ∈ s, A l) (∑ l ∈ s, w l) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro P
    simpa using MMP.Intersection.isOrderAlong_zero (MMP.Intersection.primeDivisorSubvariety P)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact isWeilDivisorOfCartier_add (hA a (Finset.mem_insert_self a s))
      (ih fun l hl => hA l (Finset.mem_insert_of_mem hl))

section Linearity

variable {k : Type} [Field k] {X Y W : Scheme.{0}} (f : X ⟶ Spec (.of k)) [IsProper f]
  (i : Y ⟶ X) [IsClosedImmersion i] (d : ℕ) (hd : topologicalKrullDim Y ≤ d)
  (L : Fin d → X.Modules) [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L q)]
  (j : Fin d) (g : X ⟶ W)

/-- `C ↦ (L₁ ⋯ g^*𝒪(C) ⋯ L_d · Y)`, `g^*𝒪(C)` in the `j`-th slot: an additive map on the Cartier
divisors of `W`. -/
@[expose]
public noncomputable def slotHom : W.CartierDivisor →+ ℤ :=
  AddMonoidHom.mk' (fun C => @sheafIntersectionNumber k _ X Y f _ i _ d hd
      (Function.update L j ((Scheme.Modules.pullback g).obj (MMP.CartierDivisor.sheaf C)))
      (isInvertible_update L j _)) (by
    intro C C'
    have h1 := @intersectionNumber_update_tensor k _ X Y f _ i _ d hd j
      (Function.update L j ((Scheme.Modules.pullback g).obj (MMP.CartierDivisor.sheaf (C + C'))))
      (isInvertible_update L j _) ((Scheme.Modules.pullback g).obj (MMP.CartierDivisor.sheaf C))
      ((Scheme.Modules.pullback g).obj (MMP.CartierDivisor.sheaf C')) _ _
      (eqToIso (Function.update_self _ _ _) ≪≫
        (Scheme.Modules.pullback g).mapIso (MMP.CartierDivisorSheaf.sheafMulIso C C').symm ≪≫
        Stacks.Chow.pullbackTensorObjIso g _ _)
    simp only [Function.update_idem] at h1
    rw [Snapper.sheafIntersectionNumber_eq_intersectionNumber,
      Snapper.sheafIntersectionNumber_eq_intersectionNumber,
      Snapper.sheafIntersectionNumber_eq_intersectionNumber]
    exact h1)

public theorem slotHom_apply (C : W.CartierDivisor) :
    slotHom f i d hd L j g C = @sheafIntersectionNumber k _ X Y f _ i _ d hd
      (Function.update L j ((Scheme.Modules.pullback g).obj (MMP.CartierDivisor.sheaf C)))
      (isInvertible_update L j _) := rfl

/-- If `𝒪(H + ∑ nₗ εₗ)` is trivial, then `(⋯ g^*𝒪(H) ⋯) = -∑ nₗ (⋯ g^*𝒪(εₗ) ⋯)`. -/
private theorem slotHom_eq_neg_sum {ι : Type*} (s : Finset ι) (H : W.CartierDivisor)
    (ε : ι → W.CartierDivisor) (n : ι → ℕ)
    (hH : Nonempty (MMP.CartierDivisor.sheaf (H + ∑ l ∈ s, n l • ε l) ≅
      SheafOfModules.unit W.ringCatSheaf)) :
    slotHom f i d hd L j g H = -∑ l ∈ s, (n l : ℤ) * slotHom f i d hd L j g (ε l) := by
  obtain ⟨e⟩ := hH
  have h0 : slotHom f i d hd L j g (H + ∑ l ∈ s, n l • ε l) = 0 := by
    rw [slotHom_apply]
    exact @MMP.Mori.sheafIntersectionNumber_eq_zero_of_iso_unit k _ X Y f _ i _ d hd _
      (isInvertible_update L j _) j (eqToIso (Function.update_self _ _ _) ≪≫
        (Scheme.Modules.pullback g).mapIso e ≪≫ Stacks.FundamentalGroup.pullbackUnitIso g)
  rw [map_add, map_sum] at h0
  simp only [map_nsmul, nsmul_eq_mul] at h0
  linarith

end Linearity

/-- **`∑ᵢ fᵢ(Zᵢ(a)) = ∑_σ a_σ f_{fst σ}(ρ(σ))`** for linear forms `fᵢ` on the `ℚ`-divisors of the
components. -/
public theorem sum_apply_surfaceCoefficientDivisor {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of ℂ)}
    [IsProper sZ] {F : MMP.Mori.Divisor Z} (hB : F.IsSNC sZ) [Fintype (DoubleSurface F)]
    (f : ∀ i : F.support, MMP.Mori.QDivisor i.1.idealSheaf.subscheme →ₗ[ℚ] ℚ)
    (a : DoubleSurface F → ℚ) :
    ∑ i, f i (surfaceCoefficientDivisor a i.1) =
      ∑ σ : DoubleSurface F, a σ * f (fstS F σ) (Finsupp.single (rho hB σ) 1) := by
  classical
  have h1 : ∀ i : F.support, f i (surfaceCoefficientDivisor a i.1) =
      ∑ σ : {σ : DoubleSurface F // σ.fst = i.1},
        a σ.1 * f i (Finsupp.single (rhoOf hB σ.1 σ.2) 1) := by
    intro i
    conv_lhs => rw [← Finsupp.sum_single (surfaceCoefficientDivisor a i.1)]
    rw [map_finsuppSum (f i), sum_surfaceCoefficientDivisor hB a i.1
      (fun P c => f i (Finsupp.single P c)) (fun P => by simp)]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [show Finsupp.single (rhoOf hB σ.1 σ.2) (a σ.1) =
      a σ.1 • Finsupp.single (rhoOf hB σ.1 σ.2) (1 : ℚ) by simp, map_smul, smul_eq_mul]
  simp_rw [h1]
  have h2 : ∀ i : F.support, ∑ σ : {σ : DoubleSurface F // σ.fst = i.1},
      a σ.1 * f i (Finsupp.single (rhoOf hB σ.1 σ.2) 1) =
      ∑ σ : {σ : DoubleSurface F // fstS F σ = i},
        a σ.1 * f (fstS F σ.1) (Finsupp.single (rho hB σ.1) 1) := by
    rintro ⟨E, hE⟩
    refine Fintype.sum_equiv (Equiv.subtypeEquivRight
      (p := fun σ : DoubleSurface F => σ.fst = E) (q := fun σ => fstS F σ = ⟨E, hE⟩) fun σ =>
        ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩) _ _ fun σ => ?_
    obtain ⟨σ, hσ⟩ := σ
    subst hσ
    rfl
  simp_rw [h2]
  exact Fintype.sum_fiberwise (fstS F) fun σ => a σ * f (fstS F σ) (Finsupp.single (rho hB σ) 1)

/-! ### The geometry of the components and double surfaces -/

section Geometry

open TopologicalSpace

variable {Z : Scheme.{0}} [Z.Over (Spec (.of ℂ))] {F : MMP.Mori.Divisor Z}

/-- The ideal of a double surface `S`, with its reduced structure. -/
public noncomputable abbrev dsIdeal (σ : DoubleSurface F) : Z.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (Closeds.closure σ.carrier)

public theorem fst_idealSheaf_le_dsIdeal (σ : DoubleSurface F) :
    σ.fst.idealSheaf ≤ dsIdeal σ := by
  have := σ.fst.integral
  rw [Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme σ.fst.idealSheaf
    σ.fst.idealSheaf.support rfl]
  refine Scheme.IdealSheafData.vanishingIdeal_antimono ?_
  change closure σ.carrier ⊆ (σ.fst.idealSheaf.support : Set Z)
  exact closure_minimal (fun y hy => (σ.carrier_subset hy).1) σ.fst.idealSheaf.support.isClosed

/-- The inclusion of a double surface `S ⊆ Eᵢ ∩ Eⱼ` in its first component `Eᵢ`. -/
public noncomputable abbrev sι (σ : DoubleSurface F) :
    (dsIdeal σ).subscheme ⟶ σ.fst.idealSheaf.subscheme :=
  Scheme.IdealSheafData.inclusion (fst_idealSheaf_le_dsIdeal σ)

/-- The inclusion of a double surface `S ⊆ Eᵢ ∩ Eⱼ` in its second component `Eⱼ`. -/
public noncomputable abbrev tι (σ : DoubleSurface F) :
    (dsIdeal σ).subscheme ⟶ σ.snd.idealSheaf.subscheme :=
  sι σ.swap

public theorem sι_comp (σ : DoubleSurface F) :
    sι σ ≫ σ.fst.idealSheaf.subschemeι = (dsIdeal σ).subschemeι :=
  Scheme.IdealSheafData.inclusion_subschemeι _

variable [IsProper (Z ↘ Spec (.of ℂ))] (hB : F.IsSNC (Z ↘ Spec (.of ℂ)))

include hB in
/-- The double surface `S`, as a closed subscheme of `Z`, is cut out by the kernel of the
inclusion of the prime divisor `ρ(σ)` of its first component. -/
private theorem ker_rho_comp (σ : DoubleSurface F) :
    ((rho hB σ).idealSheaf.subschemeι ≫ σ.fst.idealSheaf.subschemeι).ker = dsIdeal σ := by
  have := (rho hB σ).integral
  rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range, range_comp_rho hB σ]

/-- The isomorphism from the prime divisor `ρ(σ)` of the first component onto the double
surface `S ⊆ Z`. -/
private noncomputable def eρ (σ : DoubleSurface F) :
    (rho hB σ).idealSheaf.subscheme ⟶ (dsIdeal σ).subscheme :=
  IsClosedImmersion.lift (dsIdeal σ).subschemeι
    ((rho hB σ).idealSheaf.subschemeι ≫ σ.fst.idealSheaf.subschemeι)
    (by rw [Scheme.IdealSheafData.ker_subschemeι, ker_rho_comp hB σ])

private theorem eρ_comp (σ : DoubleSurface F) :
    eρ hB σ ≫ (dsIdeal σ).subschemeι =
      (rho hB σ).idealSheaf.subschemeι ≫ σ.fst.idealSheaf.subschemeι :=
  IsClosedImmersion.lift_fac _ _ _

private theorem isIso_eρ (σ : DoubleSurface F) : IsIso (eρ hB σ) :=
  IsClosedImmersion.isIso_lift _ _ (by rw [Scheme.IdealSheafData.ker_subschemeι, ker_rho_comp hB σ])

private theorem eρ_sι (σ : DoubleSurface F) :
    eρ hB σ ≫ sι σ = (rho hB σ).idealSheaf.subschemeι := by
  rw [← cancel_mono σ.fst.idealSheaf.subschemeι, Category.assoc, sι_comp, eρ_comp]

/-- A component `Eᵢ` of `F` is a threefold. -/
public theorem topologicalKrullDim_component [IsIntegral Z] (hdim : topologicalKrullDim Z = 4)
    (i : F.support) : topologicalKrullDim i.1.idealSheaf.subscheme = 3 := by
  rw [MMP.Mori.topologicalKrullDim_subscheme_eq]
  exact MMP.Fourfold.topologicalKrullDim_primeDivisor_support (n := 3) hdim i.1

include hB in
/-- The prime divisor `ρ(σ)` of the first component of a double surface is smooth. -/
private theorem isSmoothScheme_rho (σ : DoubleSurface F) :
    MMP.Mori.IsSmoothScheme ((rho hB σ).idealSheaf.subschemeι ≫
      σ.fst.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ)) := by
  have hab : (⟨σ.snd, σ.snd_mem⟩ : F.support) ≠ ⟨σ.fst, σ.fst_mem⟩ :=
    fun h => σ.fst_ne_snd (congrArg Subtype.val h).symm
  refine MMP.Resolution.isSmoothScheme_subscheme_of_stalk_eq_span_parameter
    (σ.fst.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ)) _ fun y hy => ?_
  obtain ⟨m, w, j, hw, hc⟩ := stalk_comap_component hB hab y
    (mem_support_comap_snd_of_mem_rhoOf hB σ rfl hy)
  exact ⟨m, w, j, hw, (stalk_rho hB σ hy).trans hc⟩

include hB in
public theorem isIntegral_dsIdeal (σ : DoubleSurface F) :
    IsIntegral (dsIdeal σ).subscheme := by
  haveI := isIso_eρ hB σ
  haveI := (rho hB σ).integral
  haveI : Nonempty (dsIdeal σ).subscheme :=
    ⟨eρ hB σ (Nonempty.some (inferInstance : Nonempty (rho hB σ).idealSheaf.subscheme))⟩
  exact isIntegral_of_isOpenImmersion (inv (eρ hB σ))

include hB in
public theorem smooth_dsIdeal (σ : DoubleSurface F) :
    Smooth ((dsIdeal σ).subschemeι ≫ Z ↘ Spec (.of ℂ)) := by
  haveI := isIso_eρ hB σ
  haveI hlft : LocallyOfFiniteType ((rho hB σ).idealSheaf.subschemeι ≫
      σ.fst.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ)) := inferInstance
  haveI hlfp : LocallyOfFinitePresentation ((rho hB σ).idealSheaf.subschemeι ≫
      σ.fst.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ)) :=
    @AlgebraicGeometry.instLocallyOfFinitePresentationOfIsLocallyNoetherianOfLocallyOfFiniteType
      _ _ _ inferInstance hlft
  haveI : Smooth ((rho hB σ).idealSheaf.subschemeι ≫ σ.fst.idealSheaf.subschemeι ≫
      Z ↘ Spec (.of ℂ)) := (@MMP.Mori.isSmoothScheme_iff _ _ _ hlfp).1 (isSmoothScheme_rho hB σ)
  have e : (dsIdeal σ).subschemeι ≫ Z ↘ Spec (.of ℂ) = inv (eρ hB σ) ≫
      ((rho hB σ).idealSheaf.subschemeι ≫ σ.fst.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ)) := by
    rw [IsIso.eq_inv_comp, ← Category.assoc, ← Category.assoc, eρ_comp, Category.assoc]
  rw [e]
  infer_instance

include hB in
public theorem topologicalKrullDim_dsIdeal [IsIntegral Z] (hdim : topologicalKrullDim Z = 4)
    (σ : DoubleSurface F) : topologicalKrullDim (dsIdeal σ).subscheme = 2 := by
  have h3 := topologicalKrullDim_component hdim (fstS F σ)
  haveI : IsIntegral σ.fst.idealSheaf.subscheme := σ.fst.integral
  have h2 : topologicalKrullDim (rho hB σ).idealSheaf.subscheme = 2 := by
    rw [MMP.Mori.topologicalKrullDim_subscheme_eq]
    exact MMP.Fourfold.topologicalKrullDim_primeDivisor_support (n := 2) h3 (rho hB σ)
  rw [← h2, MMP.Mori.topologicalKrullDim_subscheme_eq,
    ((rho hB σ).idealSheaf.subschemeι ≫ σ.fst.idealSheaf.subschemeι).isClosedEmbedding.toIsEmbedding.toHomeomorph.isHomeomorph.topologicalKrullDim_eq,
    range_comp_rho hB σ, Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_closure,
    (isClosed_carrier σ).closure_eq]

end Geometry

/-! ### Intersection numbers on the components and double surfaces -/

section Numbers

open TopologicalSpace

/-- `(L₁ · L₂ · L₃)` on a scheme `W` proper over `ℂ` of dimension at most three, and `0` on a
scheme of larger dimension. -/
@[expose]
public noncomputable def num3 (W : Scheme.{0}) (f : W ⟶ Spec (.of ℂ)) [IsProper f]
    (L₁ L₂ L₃ : W.Modules) [h₁ : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 L₁]
    [h₂ : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 L₂]
    [h₃ : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 L₃] : ℚ := by
  classical
  exact if h : topologicalKrullDim W ≤ (3 : ℕ) then
    (@sheafIntersectionNumber ℂ _ W W f _ (𝟙 W) _ 3 h ![L₁, L₂, L₃]
      (fun t => by fin_cases t; exacts [h₁, h₂, h₃]) : ℚ) else 0

/-- `(L₁ · L₂)` on a scheme `W` proper over `ℂ` of dimension at most two, and `0` on a scheme of
larger dimension. -/
@[expose]
public noncomputable def num2 (W : Scheme.{0}) (f : W ⟶ Spec (.of ℂ)) [IsProper f]
    (L₁ L₂ : W.Modules) [h₁ : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 L₁]
    [h₂ : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 L₂] : ℚ := by
  classical
  exact if h : topologicalKrullDim W ≤ (2 : ℕ) then
    (@sheafIntersectionNumber ℂ _ W W f _ (𝟙 W) _ 2 h ![L₁, L₂]
      (fun t => by fin_cases t; exacts [h₁, h₂]) : ℚ) else 0

/-- The bilinear form `(x, y) ↦ ∑ x_P y_Q b(P, Q)` on finitely supported families. -/
@[expose]
public noncomputable def bilin {α β : Type*} (b : α → β → ℚ) :
    (α →₀ ℚ) →ₗ[ℚ] (β →₀ ℚ) →ₗ[ℚ] ℚ :=
  Finsupp.linearCombination ℚ fun P => Finsupp.linearCombination ℚ (b P)

public theorem bilin_apply {α β : Type*} (b : α → β → ℚ) (x : α →₀ ℚ) (y : β →₀ ℚ) :
    bilin b x y = ∑ P ∈ x.support, ∑ Q ∈ y.support, x P * y Q * b P Q := by
  rw [bilin, Finsupp.linearCombination_apply, Finsupp.sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [LinearMap.smul_apply, Finsupp.linearCombination_apply, Finsupp.sum, smul_eq_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun Q _ => ?_
  rw [smul_eq_mul]; ring

public theorem bilin_add {α β : Type*} (b b' : α → β → ℚ) (x : α →₀ ℚ) (y : β →₀ ℚ) :
    bilin (fun P Q => b P Q + b' P Q) x y = bilin b x y + bilin b' x y := by
  simp only [bilin_apply, mul_add, Finset.sum_add_distrib]

public theorem bilin_smul {α β : Type*} (c : ℚ) (b : α → β → ℚ) (x : α →₀ ℚ) (y : β →₀ ℚ) :
    bilin (fun P Q => c * b P Q) x y = c * bilin b x y := by
  simp only [bilin_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun P _ => Finset.sum_congr rfl fun Q _ => ?_
  ring

public theorem bilin_sum {α β ι : Type*} (s : Finset ι) (b : ι → α → β → ℚ) (x : α →₀ ℚ)
    (y : β →₀ ℚ) : bilin (fun P Q => ∑ σ ∈ s, b σ P Q) x y = ∑ σ ∈ s, bilin (b σ) x y := by
  simp only [bilin_apply, Finset.mul_sum]
  symm
  rw [Finset.sum_comm (s := s) (t := x.support)]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [Finset.sum_comm (s := s) (t := y.support)]

public theorem bilin_zero {α β : Type*} (x : α →₀ ℚ) (y : β →₀ ℚ) :
    bilin (fun (_ : α) (_ : β) => (0 : ℚ)) x y = 0 := by
  simp [bilin_apply]

public theorem lin_add {α : Type*} (b b' : α → ℚ) (x : α →₀ ℚ) :
    Finsupp.linearCombination ℚ (fun P => b P + b' P) x =
      Finsupp.linearCombination ℚ b x + Finsupp.linearCombination ℚ b' x := by
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, smul_eq_mul, mul_add,
    Finset.sum_add_distrib]

public theorem lin_smul {α : Type*} (c : ℚ) (b : α → ℚ) (x : α →₀ ℚ) :
    Finsupp.linearCombination ℚ (fun P => c * b P) x = c * Finsupp.linearCombination ℚ b x := by
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun P _ => ?_
  ring

private theorem bilin_single_right {α β : Type*} (b : α → β → ℚ) (x : α →₀ ℚ) (Q : β) :
    bilin b x (Finsupp.single Q 1) = Finsupp.linearCombination ℚ (fun P => b P Q) x := by
  simp [bilin, Finsupp.linearCombination_apply, Finsupp.sum]

public theorem lin_sum {α ι : Type*} (s : Finset ι) (b : ι → α → ℚ) (x : α →₀ ℚ) :
    Finsupp.linearCombination ℚ (fun P => ∑ σ ∈ s, b σ P) x =
      ∑ σ ∈ s, Finsupp.linearCombination ℚ (b σ) x := by
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

variable {Z : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [IsProper (Z ↘ Spec (.of ℂ))]
  {F : MMP.Mori.Divisor Z}

variable (π : ∀ i : F.support, MMP.Mori.PrimeDivisor i.1.idealSheaf.subscheme →
    i.1.idealSheaf.subscheme.CartierDivisor) (ε : F.support → Z.CartierDivisor)
  (Hc : Z.CartierDivisor)

/-- `(π_P · π_Q · A|_{Eᵢ})` on the component `Eᵢ`. -/
@[expose]
public noncomputable def bB (i : F.support) (P Q : MMP.Mori.PrimeDivisor i.1.idealSheaf.subscheme) :
    ℚ :=
  num3 i.1.idealSheaf.subscheme (i.1.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ))
    (MMP.CartierDivisor.sheaf (π i P)) (MMP.CartierDivisor.sheaf (π i Q))
    ((Scheme.Modules.pullback i.1.idealSheaf.subschemeι).obj (MMP.CartierDivisor.sheaf Hc))

/-- `(π_P · A|_{Eᵢ} · A|_{Eᵢ})` on the component `Eᵢ`. -/
@[expose]
public noncomputable def bLam (i : F.support) (P : MMP.Mori.PrimeDivisor i.1.idealSheaf.subscheme) :
    ℚ :=
  num3 i.1.idealSheaf.subscheme (i.1.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ))
    (MMP.CartierDivisor.sheaf (π i P))
    ((Scheme.Modules.pullback i.1.idealSheaf.subschemeι).obj (MMP.CartierDivisor.sheaf Hc))
    ((Scheme.Modules.pullback i.1.idealSheaf.subschemeι).obj (MMP.CartierDivisor.sheaf Hc))

/-- `(π_P · π_Q · Eᵢ|_{Eᵢ})` on the component `Eᵢ`. -/
@[expose]
public noncomputable def bG (i : F.support) (P Q : MMP.Mori.PrimeDivisor i.1.idealSheaf.subscheme) :
    ℚ :=
  num3 i.1.idealSheaf.subscheme (i.1.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ))
    (MMP.CartierDivisor.sheaf (π i P)) (MMP.CartierDivisor.sheaf (π i Q))
    ((Scheme.Modules.pullback i.1.idealSheaf.subschemeι).obj (MMP.CartierDivisor.sheaf (ε i)))

/-- `(π_P · A|_{Eᵢ} · Eᵢ|_{Eᵢ})` on the component `Eᵢ`. -/
@[expose]
public noncomputable def bGA (i : F.support) (P : MMP.Mori.PrimeDivisor i.1.idealSheaf.subscheme) :
    ℚ :=
  num3 i.1.idealSheaf.subscheme (i.1.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ))
    (MMP.CartierDivisor.sheaf (π i P))
    ((Scheme.Modules.pullback i.1.idealSheaf.subschemeι).obj (MMP.CartierDivisor.sheaf Hc))
    ((Scheme.Modules.pullback i.1.idealSheaf.subschemeι).obj (MMP.CartierDivisor.sheaf (ε i)))

/-- `(π_P|_S · π_Q|_S)` on a double surface `S`, both from its first component. -/
@[expose]
public noncomputable def bU (σ : DoubleSurface F)
    (P Q : MMP.Mori.PrimeDivisor σ.fst.idealSheaf.subscheme) : ℚ :=
  num2 (dsIdeal σ).subscheme ((dsIdeal σ).subschemeι ≫ Z ↘ Spec (.of ℂ))
    ((Scheme.Modules.pullback (sι σ)).obj (MMP.CartierDivisor.sheaf (π (fstS F σ) P)))
    ((Scheme.Modules.pullback (sι σ)).obj (MMP.CartierDivisor.sheaf (π (fstS F σ) Q)))

/-- `(π_P|_S · π_Q|_S)` on a double surface `S`, from its first and its second component. -/
@[expose]
public noncomputable def bC (σ : DoubleSurface F)
    (P : MMP.Mori.PrimeDivisor σ.fst.idealSheaf.subscheme)
    (Q : MMP.Mori.PrimeDivisor σ.snd.idealSheaf.subscheme) : ℚ :=
  num2 (dsIdeal σ).subscheme ((dsIdeal σ).subschemeι ≫ Z ↘ Spec (.of ℂ))
    ((Scheme.Modules.pullback (sι σ)).obj (MMP.CartierDivisor.sheaf (π (fstS F σ) P)))
    ((Scheme.Modules.pullback (tι σ)).obj (MMP.CartierDivisor.sheaf (π (sndS F σ) Q)))

/-- `(π_P|_S · A|_S)` on a double surface `S`. -/
@[expose]
public noncomputable def bUA (σ : DoubleSurface F)
    (P : MMP.Mori.PrimeDivisor σ.fst.idealSheaf.subscheme) : ℚ :=
  num2 (dsIdeal σ).subscheme ((dsIdeal σ).subschemeι ≫ Z ↘ Spec (.of ℂ))
    ((Scheme.Modules.pullback (sι σ)).obj (MMP.CartierDivisor.sheaf (π (fstS F σ) P)))
    ((Scheme.Modules.pullback (dsIdeal σ).subschemeι).obj (MMP.CartierDivisor.sheaf Hc))

public theorem num3_eq {W : Scheme.{0}} (f : W ⟶ Spec (.of ℂ)) [IsProper f]
    (L₁ L₂ L₃ : W.Modules) [h₁ : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 L₁]
    [h₂ : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 L₂]
    [h₃ : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 L₃]
    (h : topologicalKrullDim W ≤ (3 : ℕ)) :
    num3 W f L₁ L₂ L₃ = (@sheafIntersectionNumber ℂ _ W W f _ (𝟙 W) _ 3 h ![L₁, L₂, L₃]
      (fun t => by fin_cases t; exacts [h₁, h₂, h₃]) : ℚ) := by
  rw [num3, dif_pos h]

public theorem num2_eq {W : Scheme.{0}} (f : W ⟶ Spec (.of ℂ)) [IsProper f]
    (L₁ L₂ : W.Modules) [h₁ : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 L₁]
    [h₂ : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 L₂]
    (h : topologicalKrullDim W ≤ (2 : ℕ)) :
    num2 W f L₁ L₂ = (@sheafIntersectionNumber ℂ _ W W f _ (𝟙 W) _ 2 h ![L₁, L₂]
      (fun t => by fin_cases t; exacts [h₁, h₂]) : ℚ) := by
  rw [num2, dif_pos h]

end Numbers

/-! ### Transport of intersection numbers -/

section Transport

variable {k : Type} [Field k]

public theorem sIN_congr_family {X Y : Scheme.{0}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (i : Y ⟶ X) [IsClosedImmersion i] (d : ℕ) (hd : topologicalKrullDim Y ≤ d)
    {L L' : Fin d → X.Modules} [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)]
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L' j)] (h : L = L') :
    sheafIntersectionNumber k f i d hd L = sheafIntersectionNumber k f i d hd L' := by
  subst h; rfl

public theorem sIN_perm {X Y : Scheme.{0}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (i : Y ⟶ X) [IsClosedImmersion i] (d : ℕ) (hd : topologicalKrullDim Y ≤ d)
    (L : Fin d → X.Modules) [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)]
    (σ : Equiv.Perm (Fin d)) :
    sheafIntersectionNumber k f i d hd (fun j => L (σ j)) = sheafIntersectionNumber k f i d hd L := by
  rw [Snapper.sheafIntersectionNumber_eq_intersectionNumber,
    Snapper.sheafIntersectionNumber_eq_intersectionNumber]
  exact AlgebraicGeometry.intersectionNumber_comp_perm k f i d hd L σ

/-- **Reading a number on a closed subscheme on the subscheme itself.** If closed immersions
`a : A ⟶ X` and `b : B ⟶ X` have the same kernel, then `(L₁ ⋯ L_d · A)_X` is the number of the
pull-backs `b^* Lⱼ` on `B`. -/
private theorem sIN_eq_of_ker_eq {X A B : Scheme.{0}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (a : A ⟶ X) [IsClosedImmersion a] (b : B ⟶ X) [IsClosedImmersion b] (h : a.ker = b.ker)
    (fB : B ⟶ Spec (.of k)) [IsProper fB] (hfB : b ≫ f = fB) (d : ℕ)
    (hd : topologicalKrullDim A ≤ d) (hd' : topologicalKrullDim B ≤ d) (L : Fin d → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)] :
    sheafIntersectionNumber k f a d hd L =
      sheafIntersectionNumber k fB (𝟙 B) d hd' (fun t => (Scheme.Modules.pullback b).obj (L t)) := by
  subst hfB
  rw [MMP.Mori.sheafIntersectionNumber_eq_of_ker_eq k f a b h d hd hd' L,
    MMP.Mori.sheafIntersectionNumber_congr_hom k f (Category.id_comp b).symm]
  exact MMP.Mori.sheafIntersectionNumber_comp_eq_of_iso k f b (𝟙 B) d hd' L _ fun t => Iso.refl _

/-- Intersection numbers only depend on the isomorphism classes of the invertible sheaves. -/
public theorem sIN_congr_iso {X Y : Scheme.{0}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (i : Y ⟶ X) [IsClosedImmersion i] (d : ℕ) (hd : topologicalKrullDim Y ≤ d)
    (L M : Fin d → X.Modules) [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L q)]
    [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (M q)]
    (e : ∀ q, Nonempty (L q ≅ M q)) :
    sheafIntersectionNumber k f i d hd L = sheafIntersectionNumber k f i d hd M := by
  classical
  rw [Snapper.sheafIntersectionNumber_eq_intersectionNumber,
    Snapper.sheafIntersectionNumber_eq_intersectionNumber]
  let G : Finset (Fin d) → Fin d → X.Modules := fun s q => if q ∈ s then M q else L q
  have hG : ∀ s q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (G s q) := by
    intro s q
    by_cases h : q ∈ s
    · simp only [G, if_pos h]; infer_instance
    · simp only [G, if_neg h]; infer_instance
  have key : ∀ s : Finset (Fin d),
      AlgebraicGeometry.intersectionNumber k f i d hd (G ∅) =
        AlgebraicGeometry.intersectionNumber k f i d hd (G s) := by
    intro s
    induction s using Finset.induction_on with
    | empty => rfl
    | insert a s has ih =>
      refine ih.trans (AlgebraicGeometry.intersectionNumber_eq_of_iso_at k f i d hd _ _ a
        (fun q hq => ?_) ?_)
      · simp [G, Finset.mem_insert, hq]
      · exact eqToIso (by simp [G, has]) ≪≫ (e a).some ≪≫ eqToIso (by simp [G])
  have h0 : G ∅ = L := funext fun q => by simp [G]
  have h1 : G Finset.univ = M := funext fun q => by simp [G]
  rw [← AlgebraicGeometry.intersectionNumber_congr_family k f i d hd h0,
    ← AlgebraicGeometry.intersectionNumber_congr_family k f i d hd h1]
  exact key Finset.univ

end Transport

section NumAPI

variable {W : Scheme.{0}} (f : W ⟶ Spec (.of ℂ)) [IsProper f]

public theorem inv_vec2 {L₁ L₂ : W.Modules}
    [h₁ : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 L₁]
    [h₂ : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 L₂] :
    ∀ q : Fin 2, SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 (![L₁, L₂] q) :=
  fun q => by fin_cases q; exacts [h₁, h₂]

public theorem inv_vec3 {L₁ L₂ L₃ : W.Modules}
    [h₁ : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 L₁]
    [h₂ : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 L₂]
    [h₃ : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 L₃] :
    ∀ q : Fin 3, SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 (![L₁, L₂, L₃] q) :=
  fun q => by fin_cases q; exacts [h₁, h₂, h₃]

public theorem inv_vec1 {L : W.Modules}
    [h : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 L] :
    ∀ q : Fin 1, SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 (![L] q) :=
  fun q => by fin_cases q; exact h

attribute [local instance] inv_vec1 inv_vec2 inv_vec3

public theorem num2_congr (L₁ L₂ M₁ M₂ : W.Modules)
    [h₁ : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 L₁]
    [h₂ : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 L₂]
    [g₁ : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 M₁]
    [g₂ : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 M₂]
    (e₁ : Nonempty (L₁ ≅ M₁)) (e₂ : Nonempty (L₂ ≅ M₂)) : num2 W f L₁ L₂ = num2 W f M₁ M₂ := by
  unfold num2
  split_ifs with h
  · congr 1
    exact @sIN_congr_iso ℂ _ W W f _ (𝟙 W) _ 2 h _ _ inv_vec2 inv_vec2
      fun q => by fin_cases q; exacts [e₁, e₂]
  · rfl

public theorem num2_comm (L₁ L₂ : W.Modules)
    [h₁ : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 L₁]
    [h₂ : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 L₂] :
    num2 W f L₁ L₂ = num2 W f L₂ L₁ := by
  unfold num2
  split_ifs with h
  · congr 1
    rw [← sIN_perm _ _ _ _ ![L₁, L₂] (Equiv.swap 0 1)]
    exact @sIN_congr_family ℂ _ W W f _ (𝟙 W) _ 2 h _ _ _ inv_vec2
      (funext fun t => by fin_cases t <;> rfl)
  · rfl

public theorem num3_congr (L₁ L₂ L₃ M₁ M₂ M₃ : W.Modules)
    [h₁ : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 L₁]
    [h₂ : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 L₂]
    [h₃ : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 L₃]
    [g₁ : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 M₁]
    [g₂ : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 M₂]
    [g₃ : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 M₃]
    (e₁ : Nonempty (L₁ ≅ M₁)) (e₂ : Nonempty (L₂ ≅ M₂)) (e₃ : Nonempty (L₃ ≅ M₃)) :
    num3 W f L₁ L₂ L₃ = num3 W f M₁ M₂ M₃ := by
  unfold num3
  split_ifs with h
  · congr 1
    exact @sIN_congr_iso ℂ _ W W f _ (𝟙 W) _ 3 h _ _ inv_vec3 inv_vec3
      fun q => by fin_cases q; exacts [e₁, e₂, e₃]
  · rfl

/-- `num3` is invariant under a permutation of its three entries. -/
public theorem num3_perm (L : Fin 3 → W.Modules)
    [hL : ∀ q, SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 (L q)]
    (σ : Equiv.Perm (Fin 3)) :
    num3 W f (L (σ 0)) (L (σ 1)) (L (σ 2)) = num3 W f (L 0) (L 1) (L 2) := by
  unfold num3
  split_ifs with h
  · congr 1
    have e1 := @sIN_perm ℂ _ W W f _ (𝟙 W) _ 3 h L hL σ
    have e2 : ![L (σ 0), L (σ 1), L (σ 2)] = fun j => L (σ j) :=
      funext fun t => by fin_cases t <;> rfl
    have e3 : ![L 0, L 1, L 2] = L := funext fun t => by fin_cases t <;> rfl
    refine (@sIN_congr_family ℂ _ W W f _ (𝟙 W) _ 3 h _ _ inv_vec3 (fun j => hL (σ j)) e2).trans ?_
    exact e1.trans (@sIN_congr_family ℂ _ W W f _ (𝟙 W) _ 3 h _ _ hL inv_vec3 e3.symm)
  · rfl

public theorem num3_comm12 (L₁ L₂ L₃ : W.Modules)
    [h₁ : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 L₁]
    [h₂ : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 L₂]
    [h₃ : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 L₃] :
    num3 W f L₁ L₂ L₃ = num3 W f L₂ L₁ L₃ :=
  (@num3_perm W f _ ![L₁, L₂, L₃] inv_vec3 (Equiv.swap 0 1)).symm

public theorem num3_comm23 (L₁ L₂ L₃ : W.Modules)
    [h₁ : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 L₁]
    [h₂ : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 L₂]
    [h₃ : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 L₃] :
    num3 W f L₁ L₂ L₃ = num3 W f L₁ L₃ L₂ :=
  (@num3_perm W f _ ![L₁, L₂, L₃] inv_vec3 (Equiv.swap 1 2)).symm

/-- `(M · A · A)` for a rational combination `M = ∑ cⱼ Mⱼ`. -/
public theorem comb_one_eq {s : ℕ} (c : Fin s → ℚ) (M : Fin s → W.Modules)
    [hM : ∀ j, SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 (M j)] (A : W.Modules)
    [hA : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 A]
    (hd : topologicalKrullDim W ≤ ((1 + 2 : ℕ) : WithBot ℕ∞)) :
    MMP.Mori.sheafCombinationIntersectionNumber ℂ f (𝟙 W) ℚ c M 1 ![A, A] hd =
      ∑ j, c j * num3 W f (M j) A A := by
  rw [MMP.Mori.sheafCombinationIntersectionNumber,
    ← (Equiv.funUnique (Fin 1) (Fin s)).symm.sum_comp]
  refine Fintype.sum_congr _ _ fun j => ?_
  rw [Fin.prod_univ_one, num3_eq _ _ _ _ hd]
  refine congrArg₂ (· * ·) rfl (congrArg (fun z : ℤ => (z : ℚ)) ?_)
  exact @sIN_congr_family ℂ _ W W f _ (𝟙 W) _ 3 hd _ _
    (MMP.Mori.isInvertible_finAppend (a := 1) (b := 2) _ _) inv_vec3 (funext fun t => by fin_cases t <;> rfl)

/-- `(M · M · A)` for a rational combination `M = ∑ cⱼ Mⱼ`. -/
public theorem comb_two_eq {s : ℕ} (c : Fin s → ℚ) (M : Fin s → W.Modules)
    [hM : ∀ j, SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 (M j)] (A : W.Modules)
    [hA : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 A]
    (hd : topologicalKrullDim W ≤ ((2 + 1 : ℕ) : WithBot ℕ∞)) :
    MMP.Mori.sheafCombinationIntersectionNumber ℂ f (𝟙 W) ℚ c M 2 ![A] hd =
      ∑ j, ∑ k, c j * c k * num3 W f (M j) (M k) A := by
  rw [MMP.Mori.sheafCombinationIntersectionNumber, ← Fintype.sum_prod_type',
    ← (finTwoArrowEquiv (Fin s)).symm.sum_comp]
  refine Fintype.sum_congr _ _ fun p => ?_
  rw [Fin.prod_univ_two, num3_eq _ _ _ _ hd]
  refine congrArg₂ (· * ·) rfl (congrArg (fun z : ℤ => (z : ℚ)) ?_)
  exact @sIN_congr_family ℂ _ W W f _ (𝟙 W) _ 3 hd _ _
    (MMP.Mori.isInvertible_finAppend (a := 2) (b := 1) _ _) inv_vec3 (funext fun t => by fin_cases t <;> rfl)

/-- `(M · A)` for a rational combination `M = ∑ cⱼ Mⱼ` on a surface. -/
public theorem comb_one_eq_two {s : ℕ} (c : Fin s → ℚ) (M : Fin s → W.Modules)
    [hM : ∀ j, SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 (M j)] (A : W.Modules)
    [hA : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 A]
    (hd : topologicalKrullDim W ≤ ((1 + 1 : ℕ) : WithBot ℕ∞)) :
    MMP.Mori.sheafCombinationIntersectionNumber ℂ f (𝟙 W) ℚ c M 1 ![A] hd =
      ∑ j, c j * num2 W f (M j) A := by
  rw [MMP.Mori.sheafCombinationIntersectionNumber,
    ← (Equiv.funUnique (Fin 1) (Fin s)).symm.sum_comp]
  refine Fintype.sum_congr _ _ fun j => ?_
  rw [Fin.prod_univ_one, num2_eq _ _ _ hd]
  refine congrArg₂ (· * ·) rfl (congrArg (fun z : ℤ => (z : ℚ)) ?_)
  exact @sIN_congr_family ℂ _ W W f _ (𝟙 W) _ 2 hd _ _
    (MMP.Mori.isInvertible_finAppend (a := 1) (b := 1) _ _) inv_vec2 (funext fun t => by fin_cases t <;> rfl)

/-- `(M · M)` for a rational combination `M = ∑ cⱼ Mⱼ` on a surface. -/
public theorem comb_two_eq_two {s : ℕ} (c : Fin s → ℚ) (M : Fin s → W.Modules)
    [hM : ∀ j, SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 (M j)]
    (hd : topologicalKrullDim W ≤ ((2 + 0 : ℕ) : WithBot ℕ∞)) :
    haveI : ∀ j : Fin 0, SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2
        ((![] : Fin 0 → W.Modules) j) := fun j => j.elim0
    MMP.Mori.sheafCombinationIntersectionNumber ℂ f (𝟙 W) ℚ c M 2 ![] hd =
      ∑ j, ∑ k, c j * c k * num2 W f (M j) (M k) := by
  haveI : ∀ j : Fin 0, SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2
      ((![] : Fin 0 → W.Modules) j) := fun j => j.elim0
  rw [MMP.Mori.sheafCombinationIntersectionNumber, ← Fintype.sum_prod_type',
    ← (finTwoArrowEquiv (Fin s)).symm.sum_comp]
  refine Fintype.sum_congr _ _ fun p => ?_
  rw [Fin.prod_univ_two, num2_eq _ _ _ hd]
  refine congrArg₂ (· * ·) rfl (congrArg (fun z : ℤ => (z : ℚ)) ?_)
  exact @sIN_congr_family ℂ _ W W f _ (𝟙 W) _ 2 hd _ _
    (MMP.Mori.isInvertible_finAppend (a := 2) (b := 0) _ _) inv_vec2 (funext fun t => by fin_cases t <;> rfl)

end NumAPI

attribute [local instance] inv_vec1 inv_vec2 inv_vec3

/-! ### Ampleness on the exceptional components -/

section Ample

open RingedSpaceModuleAdjunction

/-- The ringed-space pull-back of a module along a morphism of schemes is the scheme pull-back. -/
private noncomputable def modulePullbackIso' {X Y : Scheme.{0}} (f : X ⟶ Y) (G : Y.Modules) :
    (modulePullback f.toLRSHom.toShHom).obj G ≅ (Scheme.Modules.pullback f).obj G :=
  (Adjunction.leftAdjointUniq (modulePullbackPushforwardAdjunction f.toLRSHom.toShHom)
    (Scheme.Modules.pullbackPushforwardAdjunction f)).app G

/-- An irreducible subset of a finite set of closed points lies in one point. -/
private theorem exists_subset_singleton_of_isIrreducible {Y : Type*} [TopologicalSpace Y]
    {S T : Set Y} (hS : IsIrreducible S) (hST : S ⊆ T) (hT : T.Finite)
    (hcl : ∀ y ∈ T, IsClosed ({y} : Set Y)) : ∃ y, S ⊆ {y} := by
  obtain ⟨y, hy⟩ := hS.nonempty
  refine ⟨y, ?_⟩
  have hcl' : IsClosed (T \ {y}) := by
    have : T \ {y} = ⋃ z ∈ T \ {y}, ({z} : Set Y) := by ext; simp
    rw [this]
    exact (hT.diff).isClosed_biUnion fun z hz => hcl z hz.1
  rcases isPreirreducible_iff_isClosed_union_isClosed.1 hS.2 _ _ (hcl y (hST hy)) hcl'
      (fun z hz => by
        by_cases h : z = y
        · exact Or.inl h
        · exact Or.inr ⟨hST hz, h⟩) with h | h
  · exact h
  · exact absurd (h hy).2 (by simp)

/-- **A relatively ample sheaf is ample on what is contracted to one point.** If the image in `Y`
of the support of `F` is a finite set of closed points and `𝒜` is `r`-ample, then `𝒜` is ample on
every closed subscheme of `Z` lying in a component of `F`. -/
private theorem isAmple_pullback_of_range_subset {Z Y : Scheme.{0}} (r : Z ⟶ Y)
    (F : MMP.Mori.Divisor Z) (hfin : (r.base '' (F.supp : Set Z)).Finite)
    (hclosed : ∀ y ∈ r.base '' (F.supp : Set Z), IsClosed ({y} : Set Y)) (𝒜 : Z.Modules)
    [Stacks.Ample.IsInvertibleModule Z 𝒜] (h𝒜 : MMP.Mori.IsRelativelyAmple r 𝒜)
    (E : MMP.Mori.PrimeDivisor Z) (hE : E ∈ F.support) {W : Scheme.{0}} (g : W ⟶ Z)
    [IsClosedImmersion g] (hg : Set.range g ⊆ E.support) :
    Stacks.Ample.IsAmple W ((Scheme.Modules.pullback g).obj 𝒜) := by
  have hEsupp : E.support ⊆ (F.supp : Set Z) :=
    MMP.Mori.DivisorWithCoeffs.support_subset_supp (Finsupp.mem_support_iff.1 hE)
  have hirr : IsIrreducible (r.base '' E.support) := by
    refine IsIrreducible.image ?_ _ r.base.hom.continuous.continuousOn
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact isIrreducible_singleton.closure
  obtain ⟨y, hy⟩ := exists_subset_singleton_of_isIrreducible hirr
    (Set.image_mono hEsupp) hfin hclosed
  obtain ⟨V, hV, hyV, hAV⟩ := h𝒜 y
  have hrange : Set.range g ⊆ Set.range (r ⁻¹ᵁ V).ι := by
    rw [Scheme.Opens.range_ι]
    intro z hz
    have : r.base z ∈ ({y} : Set Y) := hy ⟨z, hg hz, rfl⟩
    rw [Set.mem_singleton_iff] at this
    change r.base z ∈ V
    rw [this]; exact hyV
  set j := IsOpenImmersion.lift (r ⁻¹ᵁ V).ι g hrange
  have hj : j ≫ (r ⁻¹ᵁ V).ι = g := IsOpenImmersion.lift_fac _ _ _
  haveI : IsClosedImmersion (j ≫ (r ⁻¹ᵁ V).ι) := by rw [hj]; infer_instance
  haveI : IsClosedImmersion j := IsClosedImmersion.of_comp j (r ⁻¹ᵁ V).ι
  have h1 := Stacks.AmplePullbackCovering.isAmple_modulePullback_of_immersion_or_isEmbedding j _
    hAV (Or.inl ⟨inferInstance, inferInstance⟩)
  exact (Stacks.RelativeVeryAmple.isAmple_congr _ _
    (modulePullbackIso' j _ ≪≫ (Scheme.Modules.pullback j).mapIso (modulePullbackIso' _ 𝒜) ≪≫
      (Scheme.Modules.pullbackComp j (r ⁻¹ᵁ V).ι).app 𝒜 ≪≫
      (Scheme.Modules.pullbackCongr hj).app 𝒜)).1 h1

end Ample

/-! ### Restriction to a double surface -/

section Restrict

variable {Z : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [IsProper (Z ↘ Spec (.of ℂ))] [IsIntegral Z]
  {F : MMP.Mori.Divisor Z} (hB : F.IsSNC (Z ↘ Spec (.of ℂ))) (hdim : topologicalKrullDim Z = 4)
  (π : ∀ i : F.support, MMP.Mori.PrimeDivisor i.1.idealSheaf.subscheme →
    i.1.idealSheaf.subscheme.CartierDivisor)
  (hπ : ∀ i P, MMP.Intersection.IsWeilDivisorOfCartier (π i P) (Finsupp.single P 1))

include hB hdim hπ in
/-- **Restriction to a double surface.** `(M₁ · M₂ · ρ(σ))_{Eᵢ} = (M₁|_S · M₂|_S)_S`. -/
private theorem num3_rho (σ : DoubleSurface F) (M₁ M₂ : σ.fst.idealSheaf.subscheme.Modules)
    [SheafOfModules.IsInvertible σ.fst.idealSheaf.subscheme.presheaf
      σ.fst.idealSheaf.subscheme.ringCatSheaf.2 M₁]
    [SheafOfModules.IsInvertible σ.fst.idealSheaf.subscheme.presheaf
      σ.fst.idealSheaf.subscheme.ringCatSheaf.2 M₂] :
    num3 σ.fst.idealSheaf.subscheme (σ.fst.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ)) M₁ M₂
        (MMP.CartierDivisor.sheaf (π (fstS F σ) (rho hB σ))) =
      num2 (dsIdeal σ).subscheme ((dsIdeal σ).subschemeι ≫ Z ↘ Spec (.of ℂ))
        ((Scheme.Modules.pullback (sι σ)).obj M₁) ((Scheme.Modules.pullback (sι σ)).obj M₂) := by
  have h3 : topologicalKrullDim σ.fst.idealSheaf.subscheme ≤ (3 : ℕ) :=
    (topologicalKrullDim_component hdim (fstS F σ)).le
  have h2 : topologicalKrullDim (dsIdeal σ).subscheme ≤ (2 : ℕ) :=
    (topologicalKrullDim_dsIdeal hB hdim σ).le
  rw [num3_eq _ _ _ _ h3, num2_eq _ _ _ h2]
  congr 1
  obtain ⟨hPe, hPsub⟩ :=
    exists_isEffective_pi ℂ (Z ↘ Spec (.of ℂ)) hB π hπ (fstS F σ) (rho hB σ)
  haveI := isIso_eρ hB σ
  rw [← sIN_perm _ (𝟙 _) 3 h3 _ (finRotate 3).symm]
  rw [sIN_congr_family _ (𝟙 _) 3 h3 (L' := ![CartierDivisor.sheaf (π (fstS F σ) (rho hB σ)), M₁, M₂])
    (funext fun t => by fin_cases t <;> rfl)]
  rw [MMP.Mori.sheafIntersectionNumber_eq_of_isEffective ℂ _ (𝟙 _) 2 h3 _ (π (fstS F σ) (rho hB σ))
    hPe ((Scheme.Modules.pullbackId _).app _)]
  have hker : ((MMP.CartierDivisor.subscheme (π (fstS F σ) (rho hB σ)) hPe).subschemeι ≫
      𝟙 _).ker =
      (sι σ).ker := by
    rw [Category.comp_id, Scheme.IdealSheafData.ker_subschemeι, hPsub,
      ← Scheme.Hom.ker_comp_of_isIso (eρ hB σ) (sι σ), eρ_sι, Scheme.IdealSheafData.ker_subschemeι]
  rw [sIN_eq_of_ker_eq _ _ (sι σ) hker ((dsIdeal σ).subschemeι ≫ Z ↘ Spec (.of ℂ))
    (by rw [← Category.assoc, sι_comp]) 2 _ h2]
  exact sIN_congr_family _ _ _ _ (funext fun t => by fin_cases t <;> rfl)

include hB hdim hπ in
/-- `(π_P|_S · A|_S)_S = (π_P · π_{ρ(σ)} · A|_{Eᵢ})_{Eᵢ}`. -/
public theorem bUA_eq_bB (Hc : Z.CartierDivisor) (σ : DoubleSurface F)
    (P : MMP.Mori.PrimeDivisor σ.fst.idealSheaf.subscheme) :
    bUA π Hc σ P = bB π Hc (fstS F σ) P (rho hB σ) := by
  unfold bUA bB
  rw [num3_comm23, num3_rho hB hdim π hπ σ]
  exact num2_congr _ _ _ _ _ ⟨Iso.refl _⟩
    ⟨((Scheme.Modules.pullbackComp (sι σ) σ.fst.idealSheaf.subschemeι).app _ ≪≫
      (Scheme.Modules.pullbackCongr (sι_comp σ)).app _).symm⟩

/-- The inclusion of a double surface `S` with first component `E`, into `E`. -/
public noncomputable abbrev sιOf {E : MMP.Mori.PrimeDivisor Z} (σ : DoubleSurface F)
    (h : σ.fst = E) : (dsIdeal σ).subscheme ⟶ E.idealSheaf.subscheme :=
  Scheme.IdealSheafData.inclusion (h ▸ fst_idealSheaf_le_dsIdeal σ)

include hB in
private theorem ker_sιOf (σ : DoubleSurface F) {E : MMP.Mori.PrimeDivisor Z} (h : σ.fst = E) :
    (sιOf σ h).ker = (rhoOf hB σ h).idealSheaf := by
  subst h
  haveI := isIso_eρ hB σ
  rw [← Scheme.Hom.ker_comp_of_isIso (eρ hB σ) (sι σ), eρ_sι, Scheme.IdealSheafData.ker_subschemeι]
  rfl

variable [Fintype (DoubleSurface F)] (hvar : MMP.Mori.IsVariety ℂ (Z ↘ Spec (.of ℂ)))
  (hsm : MMP.Mori.IsSmoothScheme (Z ↘ Spec (.of ℂ))) (ε : F.support → Z.CartierDivisor)
  (hε : ∀ i, MMP.Intersection.IsWeilDivisorOfCartier (ε i) (Finsupp.single i.1 1))

include hB hdim hvar hsm hε in
open Classical in
/-- **`Eₗ|_{Eᵢ}` is the sum of the double surfaces of `(Eᵢ, Eₗ)`**:
`(M₁ · M₂ · Eₗ|_{Eᵢ})_{Eᵢ} = ∑_{S ⊆ Eᵢ ∩ Eₗ} (M₁|_S · M₂|_S)_S` for `l ≠ i`. -/
private theorem num3_eps_eq_sum (i l : F.support) (hil : l ≠ i)
    (M₁ M₂ : i.1.idealSheaf.subscheme.Modules)
    [SheafOfModules.IsInvertible i.1.idealSheaf.subscheme.presheaf
      i.1.idealSheaf.subscheme.ringCatSheaf.2 M₁]
    [SheafOfModules.IsInvertible i.1.idealSheaf.subscheme.presheaf
      i.1.idealSheaf.subscheme.ringCatSheaf.2 M₂] :
    num3 i.1.idealSheaf.subscheme (i.1.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ)) M₁ M₂
        ((Scheme.Modules.pullback i.1.idealSheaf.subschemeι).obj (MMP.CartierDivisor.sheaf (ε l))) =
      ∑ σ : DoubleSurface F, if h : σ.fst = i.1 ∧ σ.snd = l.1 then
        num2 (dsIdeal σ).subscheme ((dsIdeal σ).subschemeι ≫ Z ↘ Spec (.of ℂ))
          ((Scheme.Modules.pullback (sιOf σ h.1)).obj M₁)
          ((Scheme.Modules.pullback (sιOf σ h.1)).obj M₂) else 0 := by
  classical
  obtain ⟨E, hE⟩ := i
  have h3 : topologicalKrullDim E.idealSheaf.subscheme ≤ (3 : ℕ) :=
    (topologicalKrullDim_component hdim ⟨E, hE⟩).le
  have hEl : l.1 ≠ E := fun h => hil (Subtype.ext h)
  rw [num3_comm23, num3_comm12, num3_eq _ _ _ _ h3]
  obtain ⟨e⟩ := nonempty_pullback_eps_iso ℂ (Z ↘ Spec (.of ℂ)) hvar hsm hB ε hε hil
  have hD := stalk_comap_component hB hil
  set ι := E.idealSheaf.subschemeι
  let sF : Finset (DoubleSurface F) := Finset.univ.filter fun σ => σ.fst = E ∧ σ.snd = l.1
  let T : DoubleSurface F → TopologicalSpace.Closeds E.idealSheaf.subscheme := fun σ =>
    if h : σ.fst = E then (rhoOf hB σ h).idealSheaf.support else ⊥
  have hTE : ∀ σ (h : σ.fst = E), (T σ : Set E.idealSheaf.subscheme) = (rhoOf hB σ h).support :=
    fun σ h => by simp only [T, dif_pos h]
  have hT : ((l.1.idealSheaf.comap ι).support : Set E.idealSheaf.subscheme) =
      ⋃ σ ∈ sF, (T σ : Set E.idealSheaf.subscheme) := by
    ext x
    rw [Scheme.IdealSheafData.support_comap]
    constructor
    · intro hx
      have hxE : ι x ∈ E.support := by
        change ι x ∈ (E.idealSheaf.support : Set Z)
        rw [← E.idealSheaf.range_subschemeι]
        exact ⟨x, rfl⟩
      let σ : DoubleSurface F := ⟨E, l.1, hE, l.2, hEl.symm,
        connectedComponentIn (E.support ∩ l.1.support) (ι x), ⟨ι x, ⟨hxE, hx⟩, rfl⟩⟩
      refine Set.mem_biUnion (x := σ) (Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl, rfl⟩) ?_
      rw [hTE σ rfl]
      have hmem : ι x ∈ σ.carrier := mem_connectedComponentIn ⟨hxE, hx⟩
      rw [← image_support_rhoOf hB σ rfl] at hmem
      obtain ⟨x', hx', hxx'⟩ := hmem
      rwa [ι.isClosedEmbedding.injective hxx'] at hx'
    · intro hx
      obtain ⟨σ, hσ, hxσ⟩ := Set.mem_iUnion₂.1 hx
      obtain ⟨-, h1, h2⟩ := Finset.mem_filter.1 hσ
      rw [hTE σ h1] at hxσ
      have : ι x ∈ σ.carrier := by
        rw [← image_support_rhoOf hB σ h1]
        exact ⟨x, hxσ, rfl⟩
      exact h2 ▸ (σ.carrier_subset this).2
  have hdisj : (sF : Set (DoubleSurface F)).PairwiseDisjoint
      fun σ => (T σ : Set E.idealSheaf.subscheme) := by
    intro σ hσ τ hτ hne
    obtain ⟨-, hσ1, hσ2⟩ := Finset.mem_filter.1 hσ
    obtain ⟨-, hτ1, hτ2⟩ := Finset.mem_filter.1 hτ
    rw [Function.onFun, hTE σ hσ1, hTE τ hτ1]
    exact disjoint_support_rhoOf hB hσ1 hτ1 (hσ2.trans hτ2.symm) hne
  have hdT : ∀ σ, topologicalKrullDim
      (Scheme.IdealSheafData.vanishingIdeal (T σ)).subscheme ≤ ((2 : ℕ) : WithBot ℕ∞) := by
    intro σ
    rw [MMP.Mori.topologicalKrullDim_subscheme_eq,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    by_cases h : σ.fst = E
    · rw [hTE σ h]
      haveI : IsIntegral E.idealSheaf.subscheme := E.integral
      exact (MMP.Fourfold.topologicalKrullDim_primeDivisor_support (n := 2)
        (topologicalKrullDim_component hdim ⟨E, hE⟩) (rhoOf hB σ h)).le
    · rw [show T σ = ⊥ from dif_neg h, TopologicalSpace.Closeds.coe_bot, topologicalKrullDim,
        Order.krullDim_eq_bot_iff.2 ⟨fun W => (W.isIrreducible.nonempty.some).2.elim⟩]
      exact bot_le
  rw [MMP.Mori.sheafIntersectionNumber_eq_sum_of_support_eq_iUnion ℂ _ 2 h3 _ _ hD e sF T hT
    hdisj hdT]
  push_cast
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun σ _ => ?_
  by_cases h : σ.fst = E ∧ σ.snd = l.1
  · rw [if_pos h, dif_pos h]
    have hker : (Scheme.IdealSheafData.vanishingIdeal (T σ)).subschemeι.ker =
        (sιOf σ h.1).ker := by
      rw [Scheme.IdealSheafData.ker_subschemeι, ker_sιOf hB σ h.1]
      have := (rhoOf hB σ h.1).integral
      rw [show T σ = (rhoOf hB σ h.1).idealSheaf.support from dif_pos h.1]
      exact (Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme _ _ rfl).symm
    have h2 : topologicalKrullDim (dsIdeal σ).subscheme ≤ (2 : ℕ) :=
      (topologicalKrullDim_dsIdeal hB hdim σ).le
    rw [num2_eq _ _ _ h2, sIN_eq_of_ker_eq _ _ (sιOf σ h.1) hker
      ((dsIdeal σ).subschemeι ≫ Z ↘ Spec (.of ℂ))
      (by rw [← Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]) 2 _ h2]
    exact congrArg (fun z : ℤ => (z : ℚ))
      (sIN_congr_family _ _ _ _ (funext fun t => by fin_cases t <;> rfl))
  · rw [if_neg h, dif_neg h]

variable (Hc : Z.CartierDivisor) (n : F.support → ℕ)
  (hHc : Nonempty (MMP.CartierDivisor.sheaf (Hc + ∑ l : F.support, n l • ε l) ≅
    SheafOfModules.unit Z.ringCatSheaf))

include hHc in
/-- `(M₁ · M₂ · A|_{Eᵢ}) = -∑ₗ nₗ (M₁ · M₂ · Eₗ|_{Eᵢ})`. -/
public theorem num3_A_eq (i : F.support) (M₁ M₂ : i.1.idealSheaf.subscheme.Modules)
    [h₁ : SheafOfModules.IsInvertible i.1.idealSheaf.subscheme.presheaf
      i.1.idealSheaf.subscheme.ringCatSheaf.2 M₁]
    [h₂ : SheafOfModules.IsInvertible i.1.idealSheaf.subscheme.presheaf
      i.1.idealSheaf.subscheme.ringCatSheaf.2 M₂] :
    num3 i.1.idealSheaf.subscheme (i.1.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ)) M₁ M₂
        ((Scheme.Modules.pullback i.1.idealSheaf.subschemeι).obj (MMP.CartierDivisor.sheaf Hc)) =
      -∑ l : F.support, (n l : ℚ) *
        num3 i.1.idealSheaf.subscheme (i.1.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ)) M₁ M₂
          ((Scheme.Modules.pullback i.1.idealSheaf.subschemeι).obj
            (MMP.CartierDivisor.sheaf (ε l))) := by
  unfold num3
  split_ifs with h
  · have key := slotHom_eq_neg_sum (i.1.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ)) (𝟙 _) 3 h
      ![M₁, M₂, (Scheme.Modules.pullback i.1.idealSheaf.subschemeι).obj (CartierDivisor.sheaf Hc)]
      2 i.1.idealSheaf.subschemeι Finset.univ Hc ε n hHc
    simp only [slotHom_apply] at key
    have hfam : ∀ C : Z.CartierDivisor,
        Function.update ![M₁, M₂,
          (Scheme.Modules.pullback i.1.idealSheaf.subschemeι).obj (MMP.CartierDivisor.sheaf Hc)] 2
          ((Scheme.Modules.pullback i.1.idealSheaf.subschemeι).obj (MMP.CartierDivisor.sheaf C)) =
        ![M₁, M₂, (Scheme.Modules.pullback i.1.idealSheaf.subschemeι).obj
          (MMP.CartierDivisor.sheaf C)] := fun C => by
      funext t; fin_cases t <;> rfl
    have e : ∀ C : Z.CartierDivisor, sheafIntersectionNumber ℂ
        (i.1.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ)) (𝟙 _) 3 h
        ![M₁, M₂, (Scheme.Modules.pullback i.1.idealSheaf.subschemeι).obj
          (MMP.CartierDivisor.sheaf C)] =
      @sheafIntersectionNumber ℂ _ _ _ (i.1.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ)) _ (𝟙 _) _
        3 h (Function.update ![M₁, M₂,
          (Scheme.Modules.pullback i.1.idealSheaf.subschemeι).obj (MMP.CartierDivisor.sheaf Hc)] 2
          ((Scheme.Modules.pullback i.1.idealSheaf.subschemeι).obj (MMP.CartierDivisor.sheaf C)))
        (isInvertible_update _ _ _) := fun C =>
      @sIN_congr_family ℂ _ _ _ _ _ (𝟙 _) _ 3 h _ _ inv_vec3 (isInvertible_update _ _ _)
        (hfam C).symm
    rw [e Hc, key]
    push_cast
    simp_rw [e]
  · simp

open Classical in
include hB hdim hvar hsm hε hHc in
/-- **`-mᵢ (M₁ · M₂ · Eᵢ|_{Eᵢ}) = (M₁ · M₂ · A|_{Eᵢ}) + ∑_{S ⊆ Eᵢ} m_{S'} (M₁|_S · M₂|_S)`.** -/
public theorem num3_self_eq (i : F.support) (M₁ M₂ : i.1.idealSheaf.subscheme.Modules)
    [h₁ : SheafOfModules.IsInvertible i.1.idealSheaf.subscheme.presheaf
      i.1.idealSheaf.subscheme.ringCatSheaf.2 M₁]
    [h₂ : SheafOfModules.IsInvertible i.1.idealSheaf.subscheme.presheaf
      i.1.idealSheaf.subscheme.ringCatSheaf.2 M₂] :
    -(n i : ℚ) * num3 i.1.idealSheaf.subscheme (i.1.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ))
        M₁ M₂ ((Scheme.Modules.pullback i.1.idealSheaf.subschemeι).obj
          (MMP.CartierDivisor.sheaf (ε i))) =
      num3 i.1.idealSheaf.subscheme (i.1.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ)) M₁ M₂
        ((Scheme.Modules.pullback i.1.idealSheaf.subschemeι).obj (MMP.CartierDivisor.sheaf Hc)) +
      ∑ σ : DoubleSurface F, if h : σ.fst = i.1 then (n (sndS F σ) : ℚ) *
        num2 (dsIdeal σ).subscheme ((dsIdeal σ).subschemeι ≫ Z ↘ Spec (.of ℂ))
          ((Scheme.Modules.pullback (sιOf σ h)).obj M₁)
          ((Scheme.Modules.pullback (sιOf σ h)).obj M₂) else 0 := by
  rw [num3_A_eq ε Hc n hHc i M₁ M₂, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have hsplit : ∑ l ∈ Finset.univ.erase i, (n l : ℚ) *
      num3 i.1.idealSheaf.subscheme (i.1.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ)) M₁ M₂
        ((Scheme.Modules.pullback i.1.idealSheaf.subschemeι).obj (MMP.CartierDivisor.sheaf (ε l))) =
      ∑ σ : DoubleSurface F, if h : σ.fst = i.1 then (n (sndS F σ) : ℚ) *
        num2 (dsIdeal σ).subscheme ((dsIdeal σ).subschemeι ≫ Z ↘ Spec (.of ℂ))
          ((Scheme.Modules.pullback (sιOf σ h)).obj M₁)
          ((Scheme.Modules.pullback (sιOf σ h)).obj M₂) else 0 := by
    rw [Finset.sum_congr rfl fun l hl => by
      rw [num3_eps_eq_sum hB hdim hvar hsm ε hε i l (Finset.ne_of_mem_erase hl) M₁ M₂,
        Finset.mul_sum]]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    by_cases h : σ.fst = i.1
    · rw [dif_pos h]
      have hne : sndS F σ ≠ i := fun e => σ.fst_ne_snd (h.trans (congrArg Subtype.val e).symm)
      rw [Finset.sum_eq_single (sndS F σ)
        (fun l _ hl => by rw [dif_neg fun h' => hl (Subtype.ext h'.2.symm), mul_zero])
        (fun hmem => absurd (Finset.mem_erase.2 ⟨hne, Finset.mem_univ _⟩) hmem),
        dif_pos ⟨h, rfl⟩]
    · rw [dif_neg h]
      exact Finset.sum_eq_zero fun l _ => by rw [dif_neg fun h' => h h'.1, mul_zero]
  rw [hsplit]
  ring

include hB hdim hvar hsm hε hHc in
/-- The family form of `num3_self_eq` for the bilinear forms of the components. -/
public theorem bilin_bG_eq [DecidableEq F.support]
    (x : ∀ i : F.support, MMP.Mori.QDivisor i.1.idealSheaf.subscheme) (i : F.support) :
    -(n i : ℚ) * bilin (bG π ε i) (x i) (x i) = bilin (bB π Hc i) (x i) (x i) +
      ∑ σ : DoubleSurface F, if fstS F σ = i then
        (n (sndS F σ) : ℚ) * bilin (bU π σ) (x (fstS F σ)) (x (fstS F σ)) else 0 := by
  classical
  rw [← bilin_smul]
  have hrel : ∀ P Q, -(n i : ℚ) * bG π ε i P Q = bB π Hc i P Q +
      ∑ σ : DoubleSurface F, if h : σ.fst = i.1 then (n (sndS F σ) : ℚ) *
        num2 (dsIdeal σ).subscheme ((dsIdeal σ).subschemeι ≫ Z ↘ Spec (.of ℂ))
          ((Scheme.Modules.pullback (sιOf σ h)).obj (MMP.CartierDivisor.sheaf (π i P)))
          ((Scheme.Modules.pullback (sιOf σ h)).obj (MMP.CartierDivisor.sheaf (π i Q))) else 0 :=
    fun P Q => num3_self_eq hB hdim hvar hsm ε hε Hc n hHc i _ _
  rw [show (fun P Q => -(n i : ℚ) * bG π ε i P Q) = _ from funext₂ hrel, bilin_add, bilin_sum]
  refine congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun σ _ => ?_)
  by_cases h : fstS F σ = i
  · subst h
    rw [if_pos rfl]
    simp only [dif_pos (rfl : σ.fst = σ.fst)]
    exact bilin_smul _ (bU π σ) _ _
  · rw [if_neg h]
    have h' : ¬ σ.fst = i.1 := fun e => h (Subtype.ext e)
    simp only [dif_neg h']
    exact bilin_zero _ _

include hB hdim hvar hsm hε hHc in
/-- The family form of `num3_self_eq` for the linear forms `(· · A · Eᵢ|_{Eᵢ})`. -/
public theorem lin_bGA_eq [DecidableEq F.support]
    (x : ∀ i : F.support, MMP.Mori.QDivisor i.1.idealSheaf.subscheme) (i : F.support) :
    -(n i : ℚ) * Finsupp.linearCombination ℚ (bGA π ε Hc i) (x i) =
      Finsupp.linearCombination ℚ (bLam π Hc i) (x i) +
      ∑ σ : DoubleSurface F, if fstS F σ = i then
        (n (sndS F σ) : ℚ) * Finsupp.linearCombination ℚ (bUA π Hc σ) (x (fstS F σ)) else 0 := by
  classical
  rw [← lin_smul]
  have hrel : ∀ P, -(n i : ℚ) * bGA π ε Hc i P = bLam π Hc i P +
      ∑ σ : DoubleSurface F, if h : σ.fst = i.1 then (n (sndS F σ) : ℚ) *
        num2 (dsIdeal σ).subscheme ((dsIdeal σ).subschemeι ≫ Z ↘ Spec (.of ℂ))
          ((Scheme.Modules.pullback (sιOf σ h)).obj (MMP.CartierDivisor.sheaf (π i P)))
          ((Scheme.Modules.pullback (sιOf σ h)).obj
            ((Scheme.Modules.pullback i.1.idealSheaf.subschemeι).obj
              (MMP.CartierDivisor.sheaf Hc))) else 0 :=
    fun P => num3_self_eq hB hdim hvar hsm ε hε Hc n hHc i _ _
  rw [show (fun P => -(n i : ℚ) * bGA π ε Hc i P) = _ from funext hrel, lin_add, lin_sum]
  refine congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun σ _ => ?_)
  by_cases h : fstS F σ = i
  · subst h
    rw [if_pos rfl]
    simp only [dif_pos (rfl : σ.fst = σ.fst), dite_true]
    rw [lin_smul]
    refine congrArg (fun z => (n (sndS F σ) : ℚ) * z)
      (congrArg (fun b => Finsupp.linearCombination ℚ b (x (fstS F σ))) (funext fun P => ?_))
    exact num2_congr _ _ _ _ _ ⟨Iso.refl _⟩
      ⟨(Scheme.Modules.pullbackComp (sι σ) σ.fst.idealSheaf.subschemeι).app _ ≪≫
        (Scheme.Modules.pullbackCongr (sι_comp σ)).app _⟩
  · rw [if_neg h]
    have h' : ¬ σ.fst = i.1 := fun e => h (Subtype.ext e)
    simp only [dif_neg h']
    simp [Finsupp.linearCombination_apply]

end Restrict

/-! ### The index theorems and negative definiteness -/

section Index

variable {Z : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [IsComplexScheme Z]
  [IsProper (Z ↘ Spec (.of ℂ))] [IsIntegral Z]
  {F : MMP.Mori.Divisor Z} (hB : F.IsSNC (Z ↘ Spec (.of ℂ))) (hdim : topologicalKrullDim Z = 4)
  (π : ∀ i : F.support, MMP.Mori.PrimeDivisor i.1.idealSheaf.subscheme →
    i.1.idealSheaf.subscheme.CartierDivisor)
  (hπ : ∀ i P, MMP.Intersection.IsWeilDivisorOfCartier (π i P) (Finsupp.single P 1))

include hB hdim hπ in
/-- **The threefold index theorem on a component.** If `(x · A²) = 0` then `(x² · A) ≤ 0`, and
equality forces `[x] = 0` in `H_4(Eᵢ, ℚ)`. -/
public theorem threefold_index (hZp : IsProjectiveMorphism (Z ↘ Spec (.of ℂ)))
    (Hc : Z.CartierDivisor) (i : F.support)
    (hAi : Stacks.Ample.IsAmple i.1.idealSheaf.subscheme
      ((Scheme.Modules.pullback i.1.idealSheaf.subschemeι).obj (MMP.CartierDivisor.sheaf Hc)))
    (x : MMP.Mori.QDivisor i.1.idealSheaf.subscheme)
    (hx : Finsupp.linearCombination ℚ (bLam π Hc i) x = 0) :
    bilin (bB π Hc i) x x ≤ 0 ∧
      (bilin (bB π Hc i) x x = 0 → MMP.Chow.divisorClass i.1.idealSheaf.subscheme x = 0) := by
  classical
  haveI : IsIntegral i.1.idealSheaf.subscheme := i.1.integral
  haveI hvX : MMP.Mori.IsVariety ℂ (i.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) :=
    (⟨⟩ : AlgebraicGeometry.IsVariety ℂ (i.1.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ)))
  have hsmX : MMP.Mori.IsSmoothScheme (i.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) := hB.1 i.1 i.2
  haveI : Smooth (i.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) := (MMP.Mori.isSmoothScheme_iff _).1 hsmX
  have hW : MMP.Mori.IsProjectiveVariety ℂ (i.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) :=
    (MMP.Mori.isProjectiveVariety_iff _ _).2
      ⟨hvX, isProjectiveMorphism_isClosedImmersion_comp _ _ hZp⟩
  have hdim3 := topologicalKrullDim_component hdim i
  set A := (Scheme.Modules.pullback i.1.idealSheaf.subschemeι).obj (MMP.CartierDivisor.sheaf Hc)
  set e := x.support.equivFin
  let P : Fin x.support.card → MMP.Mori.PrimeDivisor i.1.idealSheaf.subscheme :=
    fun j => (e.symm j).1
  let l : Fin x.support.card → ℚ := fun j => x (P j)
  let L : Fin x.support.card → i.1.idealSheaf.subscheme.Modules :=
    fun j => MMP.CartierDivisor.sheaf (π i (P j))
  have hreidx : ∀ {N : Type} [AddCommMonoid N] (g : MMP.Mori.PrimeDivisor i.1.idealSheaf.subscheme → N),
      ∑ j, g (P j) = ∑ Q ∈ x.support, g Q := fun g => by
    rw [← Finset.sum_coe_sort x.support]
    exact Fintype.sum_equiv e.symm _ _ fun j => rfl
  have key := MMP.Mori.sheafCombinationIntersectionNumber_two_nonpos_of_isAmple_of_dim_eq_three
    hW hdim3 A hAi l L
  have h1 : MMP.Mori.sheafCombinationIntersectionNumber ℂ (i.1.idealSheaf.subscheme ↘ Spec (.of ℂ))
      (𝟙 _) ℚ l L 1 ![A, A] (by rw [hdim3]; rfl) =
      Finsupp.linearCombination ℚ (bLam π Hc i) x := by
    rw [comb_one_eq, Finsupp.linearCombination_apply, Finsupp.sum]
    exact hreidx fun Q => x Q * bLam π Hc i Q
  have h2 : MMP.Mori.sheafCombinationIntersectionNumber ℂ (i.1.idealSheaf.subscheme ↘ Spec (.of ℂ))
      (𝟙 _) ℚ l L 2 ![A] (by rw [hdim3]; rfl) = bilin (bB π Hc i) x x := by
    rw [comb_two_eq, bilin_apply, ← hreidx fun Q => ∑ Q' ∈ x.support, x Q * x Q' * bB π Hc i Q Q']
    refine Finset.sum_congr rfl fun j _ => ?_
    exact hreidx fun Q' => x (P j) * x Q' * bB π Hc i (P j) Q'
  obtain ⟨hle, heq⟩ := key (h1.trans hx)
  rw [h2] at hle
  refine ⟨hle, fun h0 => ?_⟩
  obtain ⟨-, hc⟩ := heq (h2.trans h0)
  rw [hreidx fun Q => x Q • MMP.Analytic.singularCohomology.mapCoeff (Int.castRingHom ℚ) 2
    (MMP.Analytic.algebraicFirstChernClass (MMP.CartierDivisor.sheaf (π i Q)))] at hc
  haveI : IsLocallyNoetherian i.1.idealSheaf.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (i.1.idealSheaf.subscheme ↘ Spec (.of ℂ))
  haveI : IsNormal i.1.idealSheaf.subscheme :=
    isNormal_of_smooth_over_field (i.1.idealSheaf.subscheme ↘ Spec (.of ℂ))
  haveI : CompactSpace i.1.idealSheaf.subscheme :=
    (quasiCompact_iff_compactSpace (i.1.idealSheaf.subscheme ↘ Spec (.of ℂ))).mp inferInstance
  have hdimX : topologicalKrullDim i.1.idealSheaf.subscheme = ((2 + 1 : ℕ) : WithBot ℕ∞) := by
    rw [hdim3]
    rfl
  have hξ : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (i.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) (genericPoint i.1.idealSheaf.subscheme) =
        ((2 + 1 : ℕ) : ℤ) :=
    MMP.Chow.relativeDimension_genericPoint_eq ℂ _ hdimX
  let Ψ := (BorelMooreCross.congrDegree ℚ (TopCat.of (UnderlyingSpace ℂ i.1.idealSheaf.subscheme))
      (by norm_num : ((2 * (2 + 1) : ℕ) : ℤ) - 2 = ((2 * 2 : ℕ) : ℤ))).toLinearMap ∘ₗ
    (borelMooreHomology.capProductPullback ℚ
      (TopCat.ofHom ⟨_, MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace.symm.continuous⟩ :
        TopCat.of (UnderlyingSpace ℂ i.1.idealSheaf.subscheme) ⟶ MMP.Analytic.Analytification.space (i.1.idealSheaf.subscheme ↘ Spec (.of ℂ)))
      Set.univ 2 ((2 * (2 + 1) : ℕ) : ℤ)).flip (MMP.Chow.rationalCycleClass i.1.idealSheaf.subscheme (2 + 1)
        (MMP.Chow.rationalPointCycle (Stacks.Chow.fieldChowSituation ℂ)
          (i.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) ((2 + 1 : ℕ) : ℤ)
          (genericPoint i.1.idealSheaf.subscheme) hξ))
  have hQ : ∀ Q : MMP.Mori.PrimeDivisor i.1.idealSheaf.subscheme, MMP.Chow.divisorClass i.1.idealSheaf.subscheme (Finsupp.single Q 1) =
      Ψ (MMP.Analytic.singularCohomology.mapCoeff (Int.castRingHom ℚ) 2
        (MMP.Analytic.algebraicFirstChernClass (MMP.CartierDivisor.sheaf (π i Q)))) := by
    intro Q
    have hcQ := MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsmX
      (Finsupp.single Q 1 : MMP.Mori.Divisor i.1.idealSheaf.subscheme)
    haveI := hcQ.isInvertibleModule_divisorialSheaf
    have hsingle : MMP.Mori.Divisor.toQDivisor (Finsupp.single Q (1 : ℤ)) =
        ((1 : ℕ) : ℤ) • (Finsupp.single Q (1 : ℚ)) := by
      rw [Nat.cast_one, one_smul]
      ext E
      change ((Finsupp.single Q (1 : ℤ) E : ℤ) : ℚ) = _
      by_cases h : Q = E <;> simp [Finsupp.single_apply, h, DivisorWithCoeffs.coeff_apply]
    have h := (smul_rationalCycleClass_eq_capProductPullback hW hsmX hdimX
      (Finsupp.single Q 1) one_pos (Finsupp.single Q 1) hsingle _ hξ).1
    rw [Nat.cast_one, one_smul] at h
    obtain ⟨eQ⟩ := (hπ i Q).nonempty_sheaf_iso_divisorialSheaf
    rw [MMP.Analytic.algebraicFirstChernClass_eq_of_iso eQ]
    exact h
  have hx' : x = ∑ Q ∈ x.support, x Q • Finsupp.single Q (1 : ℚ) := by
    conv_lhs => rw [← Finsupp.sum_single x]
    rw [Finsupp.sum]
    exact Finset.sum_congr rfl fun Q _ => (Finsupp.smul_single_one _ _).symm
  rw [hx', map_sum]
  simp_rw [map_smul, hQ, ← map_smul, ← map_sum]
  rw [hc, map_zero]

include hB hdim in
/-- **The surface index theorem on a double surface.** For `x` on the first component and `y` on
the second, if `(x|_S · A) = (y|_S · A)` then `((x - y)|_S)² ≤ 0`. -/
public theorem surface_index (hZp : IsProjectiveMorphism (Z ↘ Spec (.of ℂ)))
    (Hc : Z.CartierDivisor) (σ : DoubleSurface F)
    (hAS : Stacks.Ample.IsAmple (dsIdeal σ).subscheme
      ((Scheme.Modules.pullback (dsIdeal σ).subschemeι).obj (MMP.CartierDivisor.sheaf Hc)))
    (x : MMP.Mori.QDivisor σ.fst.idealSheaf.subscheme)
    (y : MMP.Mori.QDivisor σ.snd.idealSheaf.subscheme)
    (hxy : Finsupp.linearCombination ℚ (bUA π Hc σ) x =
      Finsupp.linearCombination ℚ (bUA π Hc σ.swap) y) :
    bilin (bU π σ) x x - 2 * bilin (bC π σ) x y + bilin (bU π σ.swap) y y ≤ 0 := by
  classical
  haveI : IsIntegral (dsIdeal σ).subscheme := isIntegral_dsIdeal hB σ
  haveI : Smooth ((dsIdeal σ).subscheme ↘ Spec (.of ℂ)) := smooth_dsIdeal hB σ
  have hvS : MMP.Mori.IsVariety ℂ ((dsIdeal σ).subscheme ↘ Spec (.of ℂ)) :=
    (⟨⟩ : AlgebraicGeometry.IsVariety ℂ ((dsIdeal σ).subschemeι ≫ Z ↘ Spec (.of ℂ)))
  have hW : MMP.Mori.IsProjectiveVariety ℂ ((dsIdeal σ).subscheme ↘ Spec (.of ℂ)) :=
    (MMP.Mori.isProjectiveVariety_iff _ _).2
      ⟨hvS, isProjectiveMorphism_isClosedImmersion_comp _ _ hZp⟩
  have hdim2 := topologicalKrullDim_dsIdeal hB hdim σ
  set A := (Scheme.Modules.pullback (dsIdeal σ).subschemeι).obj (MMP.CartierDivisor.sheaf Hc)
  set e₁ := x.support.equivFin
  set e₂ := y.support.equivFin
  let P₁ : Fin x.support.card → MMP.Mori.PrimeDivisor σ.fst.idealSheaf.subscheme :=
    fun j => (e₁.symm j).1
  let P₂ : Fin y.support.card → MMP.Mori.PrimeDivisor σ.snd.idealSheaf.subscheme :=
    fun j => (e₂.symm j).1
  have hre₁ : ∀ {N : Type} [AddCommMonoid N]
      (g : MMP.Mori.PrimeDivisor σ.fst.idealSheaf.subscheme → N),
      ∑ j, g (P₁ j) = ∑ Q ∈ x.support, g Q := fun g => by
    rw [← Finset.sum_coe_sort x.support]
    exact Fintype.sum_equiv e₁.symm _ _ fun j => rfl
  have hre₂ : ∀ {N : Type} [AddCommMonoid N]
      (g : MMP.Mori.PrimeDivisor σ.snd.idealSheaf.subscheme → N),
      ∑ j, g (P₂ j) = ∑ Q ∈ y.support, g Q := fun g => by
    rw [← Finset.sum_coe_sort y.support]
    exact Fintype.sum_equiv e₂.symm _ _ fun j => rfl
  let M : Fin (x.support.card + y.support.card) → (dsIdeal σ).subscheme.Modules :=
    Fin.append (fun j => (Scheme.Modules.pullback (sι σ)).obj
        (MMP.CartierDivisor.sheaf (π (fstS F σ) (P₁ j))))
      (fun j => (Scheme.Modules.pullback (tι σ)).obj
        (MMP.CartierDivisor.sheaf (π (sndS F σ) (P₂ j))))
  let c : Fin (x.support.card + y.support.card) → ℚ :=
    Fin.append (fun j => x (P₁ j)) (fun j => -y (P₂ j))
  haveI : ∀ j, SheafOfModules.IsInvertible (dsIdeal σ).subscheme.presheaf
      (dsIdeal σ).subscheme.ringCatSheaf.2 (M j) := MMP.Mori.isInvertible_finAppend _ _
  have key := MMP.Mori.sheafCombinationIntersectionNumber_two_nonpos_of_isAmple ℂ
    ((dsIdeal σ).subscheme ↘ Spec (.of ℂ)) hW hdim2 A hAS c M
  have hx1 : ∑ j, x (P₁ j) * num2 (dsIdeal σ).subscheme ((dsIdeal σ).subscheme ↘ Spec (.of ℂ))
      ((Scheme.Modules.pullback (sι σ)).obj (MMP.CartierDivisor.sheaf (π (fstS F σ) (P₁ j)))) A =
      Finsupp.linearCombination ℚ (bUA π Hc σ) x :=
    (hre₁ (fun Q => x Q * bUA π Hc σ Q)).trans (Finsupp.linearCombination_apply ℚ x).symm
  have hy1 : ∑ j, y (P₂ j) * num2 (dsIdeal σ).subscheme ((dsIdeal σ).subscheme ↘ Spec (.of ℂ))
      ((Scheme.Modules.pullback (tι σ)).obj (MMP.CartierDivisor.sheaf (π (sndS F σ) (P₂ j)))) A =
      Finsupp.linearCombination ℚ (bUA π Hc σ.swap) y :=
    (hre₂ (fun Q => y Q * bUA π Hc σ.swap Q)).trans (Finsupp.linearCombination_apply ℚ y).symm
  have h1 : MMP.Mori.sheafCombinationIntersectionNumber ℂ ((dsIdeal σ).subscheme ↘ Spec (.of ℂ))
      (𝟙 _) ℚ c M 1 ![A] (by rw [hdim2]; rfl) =
      Finsupp.linearCombination ℚ (bUA π Hc σ) x -
        Finsupp.linearCombination ℚ (bUA π Hc σ.swap) y := by
    rw [comb_one_eq_two, Fin.sum_univ_add]
    simp only [c, M, Fin.append_left, Fin.append_right]
    rw [← hx1, ← hy1, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    simp only [neg_mul]
  haveI : ∀ j : Fin 0, SheafOfModules.IsInvertible (dsIdeal σ).subscheme.presheaf
      (dsIdeal σ).subscheme.ringCatSheaf.2 ((![] : Fin 0 → (dsIdeal σ).subscheme.Modules) j) :=
    fun j => j.elim0
  have hxx : ∑ j, ∑ k, x (P₁ j) * x (P₁ k) * num2 (dsIdeal σ).subscheme
      ((dsIdeal σ).subscheme ↘ Spec (.of ℂ))
      ((Scheme.Modules.pullback (sι σ)).obj (MMP.CartierDivisor.sheaf (π (fstS F σ) (P₁ j))))
      ((Scheme.Modules.pullback (sι σ)).obj (MMP.CartierDivisor.sheaf (π (fstS F σ) (P₁ k)))) =
      bilin (bU π σ) x x := by
    refine Eq.trans ?_ (bilin_apply (bU π σ) x x).symm
    rw [← hre₁]
    exact Finset.sum_congr rfl fun j _ => hre₁ (fun Q => x (P₁ j) * x Q * bU π σ (P₁ j) Q)
  have hxy' : ∑ j, ∑ k, x (P₁ j) * y (P₂ k) * num2 (dsIdeal σ).subscheme
      ((dsIdeal σ).subscheme ↘ Spec (.of ℂ))
      ((Scheme.Modules.pullback (sι σ)).obj (MMP.CartierDivisor.sheaf (π (fstS F σ) (P₁ j))))
      ((Scheme.Modules.pullback (tι σ)).obj (MMP.CartierDivisor.sheaf (π (sndS F σ) (P₂ k)))) =
      bilin (bC π σ) x y := by
    refine Eq.trans ?_ (bilin_apply (bC π σ) x y).symm
    rw [← hre₁]
    exact Finset.sum_congr rfl fun j _ => hre₂ (fun Q => x (P₁ j) * y Q * bC π σ (P₁ j) Q)
  have hyy : ∑ j, ∑ k, y (P₂ j) * y (P₂ k) * num2 (dsIdeal σ).subscheme
      ((dsIdeal σ).subscheme ↘ Spec (.of ℂ))
      ((Scheme.Modules.pullback (tι σ)).obj (MMP.CartierDivisor.sheaf (π (sndS F σ) (P₂ j))))
      ((Scheme.Modules.pullback (tι σ)).obj (MMP.CartierDivisor.sheaf (π (sndS F σ) (P₂ k)))) =
      bilin (bU π σ.swap) y y := by
    refine Eq.trans ?_ (bilin_apply (bU π σ.swap) y y).symm
    refine (Finset.sum_congr rfl fun j _ =>
      hre₂ (fun Q => y (P₂ j) * y Q * bU π σ.swap (P₂ j) Q)).trans ?_
    exact hre₂ (fun P => ∑ Q ∈ y.support, y P * y Q * bU π σ.swap P Q)
  have hyx : ∑ j, ∑ k, y (P₂ j) * x (P₁ k) * num2 (dsIdeal σ).subscheme
      ((dsIdeal σ).subscheme ↘ Spec (.of ℂ))
      ((Scheme.Modules.pullback (tι σ)).obj (MMP.CartierDivisor.sheaf (π (sndS F σ) (P₂ j))))
      ((Scheme.Modules.pullback (sι σ)).obj (MMP.CartierDivisor.sheaf (π (fstS F σ) (P₁ k)))) =
      ∑ j, ∑ k, x (P₁ j) * y (P₂ k) * num2 (dsIdeal σ).subscheme
      ((dsIdeal σ).subscheme ↘ Spec (.of ℂ))
      ((Scheme.Modules.pullback (sι σ)).obj (MMP.CartierDivisor.sheaf (π (fstS F σ) (P₁ j))))
      ((Scheme.Modules.pullback (tι σ)).obj (MMP.CartierDivisor.sheaf (π (sndS F σ) (P₂ k)))) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [num2_comm, mul_comm (y (P₂ k))]
  have h2 : MMP.Mori.sheafCombinationIntersectionNumber ℂ ((dsIdeal σ).subscheme ↘ Spec (.of ℂ))
      (𝟙 _) ℚ c M 2 ![] (by rw [hdim2]; rfl) =
      bilin (bU π σ) x x - 2 * bilin (bC π σ) x y + bilin (bU π σ.swap) y y := by
    rw [comb_two_eq_two, Fin.sum_univ_add]
    simp only [Fin.sum_univ_add, c, M, Fin.append_left, Fin.append_right]
    rw [← hxx, ← hxy', ← hyy]
    simp only [Finset.sum_add_distrib, neg_mul, mul_neg, neg_neg, Finset.sum_neg_distrib]
    rw [hyx]
    ring
  rw [h1, hxy, sub_self] at key
  rw [← h2]
  exact key rfl

include hB hdim hπ in
/-- **Negative definiteness on the oriented systems**, from the weighted surface identity. -/
public theorem weighted_negdef [Fintype (DoubleSurface F)]
    (hvar : MMP.Mori.IsVariety ℂ (Z ↘ Spec (.of ℂ)))
    (hsm : MMP.Mori.IsSmoothScheme (Z ↘ Spec (.of ℂ)))
    (hZp : IsProjectiveMorphism (Z ↘ Spec (.of ℂ))) (hBred : ∀ E ∈ F.support, F E = 1)
    (ε : F.support → Z.CartierDivisor)
    (hε : ∀ i, MMP.Intersection.IsWeilDivisorOfCartier (ε i) (Finsupp.single i.1 1))
    (Hc : Z.CartierDivisor) (n : F.support → ℕ) (hn : ∀ i, 0 < n i)
    (hHc : Nonempty (MMP.CartierDivisor.sheaf (Hc + ∑ l : F.support, n l • ε l) ≅
      SheafOfModules.unit Z.ringCatSheaf))
    (hAmp : ∀ i : F.support, Stacks.Ample.IsAmple i.1.idealSheaf.subscheme
      ((Scheme.Modules.pullback i.1.idealSheaf.subschemeι).obj (MMP.CartierDivisor.sheaf Hc)))
    (a : DoubleSurface F → ℚ) (ha : a ∈ orientedSurfaceCoefficients F)
    (h0 : ∑ i : F.support, bilin (bB π Hc i) (surfaceCoefficientDivisor a i.1)
      (surfaceCoefficientDivisor a i.1) / (n i : ℚ) = 0) : a = 0 := by
  classical
  letI : LinearOrder F.support :=
    LinearOrder.lift' (Fintype.equivFin F.support) (Fintype.equivFin F.support).injective
  have W := sum_sq_mul_intersectionNumber_doubleSurface_eq ℂ (Z ↘ Spec (.of ℂ)) hvar hsm hZp hdim
    F hBred hB a ha (fun i => (n i : ℚ)) (fun i => by exact_mod_cast hn i)
    (Finsupp.single Hc 1) ε hε π hπ
  simp only [Finsupp.sum_single_index, zero_mul, mul_zero, one_mul, mul_one] at W
  -- the first term of the right side is the form `P(Z(a))`, which vanishes
  have hR1 : ∑ x : F.support, 1 / (n x : ℚ) *
      Finsupp.sum (surfaceCoefficientDivisor a x.1) (fun P cP =>
        Finsupp.sum (surfaceCoefficientDivisor a x.1) fun Q cQ => cP * cQ *
          (@sheafIntersectionNumber ℂ _ _ _ (x.1.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ)) _
            (𝟙 _) _ 3 (topologicalKrullDim_component hdim x).le
            ![MMP.CartierDivisor.sheaf (π x P), MMP.CartierDivisor.sheaf (π x Q),
              (Scheme.Modules.pullback x.1.idealSheaf.subschemeι).obj (MMP.CartierDivisor.sheaf Hc)]
            inv_vec3 : ℚ)) = 0 := by
    rw [← h0]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [bilin_apply, one_div, div_eq_inv_mul]
    congr 1
    simp only [Finsupp.sum]
    refine Finset.sum_congr rfl fun P _ => Finset.sum_congr rfl fun Q _ => ?_
    unfold bB
    rw [num3_eq _ _ _ _ (topologicalKrullDim_component hdim x).le]
  rw [show (∑ x : F.support, 1 / (n x : ℚ) * _) = (0 : ℚ) from hR1, zero_add] at W
  -- `(A · T) ≥ 0` on the triple curves
  have hTnn : ∀ (x : F.support) (T : Set Z) (_ : T ⊆ x.1.support)
      (hdT : topologicalKrullDim
        (Scheme.IdealSheafData.vanishingIdeal (TopologicalSpace.Closeds.closure T)).subscheme ≤
          ((1 : ℕ) : WithBot ℕ∞)),
      (0 : ℚ) ≤ (sheafIntersectionNumber ℂ (Z ↘ Spec (.of ℂ))
        (Scheme.IdealSheafData.vanishingIdeal (TopologicalSpace.Closeds.closure T)).subschemeι 1 hdT
        (fun _ => MMP.CartierDivisor.sheaf Hc) : ℚ) := by
    intro x T hTx hdT
    have hle : x.1.idealSheaf ≤
        Scheme.IdealSheafData.vanishingIdeal (TopologicalSpace.Closeds.closure T) := by
      have := x.1.integral
      rw [Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme x.1.idealSheaf
        x.1.idealSheaf.support rfl]
      refine Scheme.IdealSheafData.vanishingIdeal_antimono ?_
      change closure T ⊆ (x.1.idealSheaf.support : Set Z)
      exact closure_minimal hTx x.1.idealSheaf.support.isClosed
    rw [MMP.Mori.sheafIntersectionNumber_congr_hom ℂ _
      (Scheme.IdealSheafData.inclusion_subschemeι hle).symm,
      MMP.Mori.sheafIntersectionNumber_comp_eq_of_iso ℂ _ x.1.idealSheaf.subschemeι
        (Scheme.IdealSheafData.inclusion hle) 1 hdT _
        (fun _ => (Scheme.Modules.pullback x.1.idealSheaf.subschemeι).obj
          (MMP.CartierDivisor.sheaf Hc)) (fun _ => Iso.refl _),
      MMP.Mori.Snapper.sheafIntersectionNumber_eq_intersectionNumber]
    exact_mod_cast MMP.Threefold.Mori.intersectionNumber_nonneg_of_isAmple ℂ _
      ((Scheme.Modules.pullback x.1.idealSheaf.subschemeι).obj (MMP.CartierDivisor.sheaf Hc))
      ((Scheme.Modules.pullback x.1.idealSheaf.subschemeι).obj (MMP.CartierDivisor.sheaf Hc))
      (hAmp x) 0
      (fun W i _ _ hW => by
        rw [AlgebraicGeometry.intersectionNumber_zero_eq_finrank_globalSections]
        exact_mod_cast Nat.zero_le _)
      (Scheme.IdealSheafData.inclusion hle) 1 hdT _ Finset.univ (fun _ _ => rfl)
      (fun q hq => absurd (Finset.mem_univ q) hq) (by simp)
  have hR2 : 0 ≤ ∑ x : F.support, ∑ x₁ : F.support, ∑ x₂ : F.support,
      if h : x < x₁ then if h₁ : x₁ < x₂ then
        ∑ᶠ (T : Set Z) (h₂ : T.Nonempty ∧ T ⊆ x.1.support ∩ x₁.1.support ∩ x₂.1.support ∧
          ∃ x₃ ∈ x.1.support ∩ x₁.1.support ∩ x₂.1.support,
            connectedComponentIn (x.1.support ∩ x₁.1.support ∩ x₂.1.support) x₃ = T),
          (n x : ℚ) * n x₁ * n x₂ *
            (coeffAlong a x.2 x₁.2 (fun e => h.ne (Subtype.ext e)) h₂.1
                (fun y hy => (h₂.2.1 hy).1) / (n x * n x₁) -
              coeffAlong a x.2 x₂.2 (fun e => (h.trans h₁).ne (Subtype.ext e)) h₂.1
                (fun y hy => ⟨(h₂.2.1 hy).1.1, (h₂.2.1 hy).2⟩) / (n x * n x₂) +
              coeffAlong a x₁.2 x₂.2 (fun e => h₁.ne (Subtype.ext e)) h₂.1
                (fun y hy => ⟨(h₂.2.1 hy).1.2, (h₂.2.1 hy).2⟩) / (n x₁ * n x₂)) ^ 2 *
            (sheafIntersectionNumber ℂ (Z ↘ Spec (.of ℂ))
              (Scheme.IdealSheafData.vanishingIdeal (TopologicalSpace.Closeds.closure T)).subschemeι 1
              (topologicalKrullDim_tripleCurve_le ℂ _ hvar hdim hB x x₁ x₂ h h₁ T h₂.2.1)
              (fun _ => MMP.CartierDivisor.sheaf Hc) : ℚ)
        else 0 else 0 := by
    refine Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun x₁ _ =>
      Finset.sum_nonneg fun x₂ _ => ?_
    split_ifs with h h₁
    · refine finsum_nonneg fun T => finsum_nonneg fun h₂ => ?_
      refine mul_nonneg (mul_nonneg (by positivity) (sq_nonneg _)) ?_
      exact hTnn x T (fun y hy => (h₂.2.1 hy).1.1) _
    · exact le_rfl
    · exact le_rfl
  -- `∑ₗ mₗ (Eₗ · A · S) = -(A² · S)` with `(A² · S) > 0`
  have hq : ∀ σ : DoubleSurface F, ∃ q : ℚ, 0 < q ∧ ∑ x : F.support, (n x : ℚ) *
      (sheafIntersectionNumber ℂ (Z ↘ Spec (.of ℂ))
        (Scheme.IdealSheafData.vanishingIdeal (TopologicalSpace.Closeds.closure σ.carrier)).subschemeι
        2 (topologicalKrullDim_doubleSurface_le ℂ _ hvar hdim hB σ)
        (fun t => MMP.CartierDivisor.sheaf (![ε x, Hc] t)) : ℚ) = -q := by
    intro σ
    have hS := topologicalKrullDim_doubleSurface_le ℂ _ hvar hdim hB σ
    let Ls : Fin 2 → Z.Modules := fun t => MMP.CartierDivisor.sheaf (![Hc, Hc] t)
    have hslot : ∀ C : Z.CartierDivisor,
        (slotHom (Z ↘ Spec (.of ℂ)) (dsIdeal σ).subschemeι 2 hS Ls 0 (𝟙 Z) C : ℤ) =
          sheafIntersectionNumber ℂ (Z ↘ Spec (.of ℂ)) (dsIdeal σ).subschemeι 2 hS
            (fun t => MMP.CartierDivisor.sheaf (![C, Hc] t)) := by
      intro C
      rw [slotHom_apply]
      refine @sIN_congr_iso ℂ _ Z _ _ _ _ _ 2 hS _ _ (isInvertible_update Ls 0 _)
        (fun t => MMP.Mori.isInvertible_cartierSheaf _) fun q => ?_
      fin_cases q
      · exact ⟨eqToIso (Function.update_self _ _ _) ≪≫ (Scheme.Modules.pullbackId Z).app _⟩
      · exact ⟨eqToIso (Function.update_of_ne (by decide) _ _)⟩
    have key := slotHom_eq_neg_sum (Z ↘ Spec (.of ℂ)) (dsIdeal σ).subschemeι 2 hS Ls 0 (𝟙 Z)
      Finset.univ Hc ε n hHc
    simp only [hslot] at key
    refine ⟨(sheafIntersectionNumber ℂ (Z ↘ Spec (.of ℂ)) (dsIdeal σ).subschemeι 2 hS
      (fun t => MMP.CartierDivisor.sheaf (![Hc, Hc] t)) : ℚ), ?_, ?_⟩
    · haveI : IsIntegral (dsIdeal σ).subscheme := isIntegral_dsIdeal hB σ
      rw [MMP.Mori.sheafIntersectionNumber_congr_hom ℂ _ (sι_comp σ).symm,
        MMP.Mori.sheafIntersectionNumber_comp_eq_of_iso ℂ _ σ.fst.idealSheaf.subschemeι (sι σ) 2
          _ _ (fun t => (Scheme.Modules.pullback σ.fst.idealSheaf.subschemeι).obj
            (MMP.CartierDivisor.sheaf (![Hc, Hc] t))) (fun t => Iso.refl _)]
      have hpos := MMP.Threefold.Mori.sheafSelfIntersectionNumber_pos_of_isAmple ℂ
        (σ.fst.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ))
        ((Scheme.Modules.pullback σ.fst.idealSheaf.subschemeι).obj (MMP.CartierDivisor.sheaf Hc))
        (hAmp (fstS F σ)) (dsIdeal σ).subscheme (sι σ) 2 (topologicalKrullDim_dsIdeal hB hdim σ)
      unfold MMP.Mori.sheafSelfIntersectionNumber at hpos
      rw [sIN_congr_family _ _ _ _ (funext fun t => by fin_cases t <;> rfl :
        (fun _ : Fin 2 => (Scheme.Modules.pullback σ.fst.idealSheaf.subschemeι).obj
          (MMP.CartierDivisor.sheaf Hc)) = fun t => (Scheme.Modules.pullback
            σ.fst.idealSheaf.subschemeι).obj (MMP.CartierDivisor.sheaf (![Hc, Hc] t)))] at hpos
      exact_mod_cast hpos
    · have := congrArg (fun z : ℤ => (z : ℚ)) key
      push_cast at this
      linarith
  choose q hqpos hqeq using hq
  simp only [hqeq] at W
  rw [finsum_eq_sum_of_fintype] at W
  simp only [finsum_eq_if] at W
  have hnn : ∀ σ : DoubleSurface F, (if (⟨σ.fst, σ.fst_mem⟩ : F.support) < ⟨σ.snd, σ.snd_mem⟩ then
      (n ⟨σ.fst, σ.fst_mem⟩ : ℚ) * n ⟨σ.snd, σ.snd_mem⟩ *
        (a σ / (n ⟨σ.fst, σ.fst_mem⟩ * n ⟨σ.snd, σ.snd_mem⟩)) ^ 2 * -q σ else 0) ≤ 0 := by
    intro σ
    split_ifs
    · have h1 : (0 : ℚ) < n ⟨σ.fst, σ.fst_mem⟩ := by exact_mod_cast hn _
      have h2 : (0 : ℚ) < n ⟨σ.snd, σ.snd_mem⟩ := by exact_mod_cast hn _
      exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (mul_nonneg h1.le h2.le) (sq_nonneg _))
        (neg_nonpos.2 (hqpos σ).le)
    · exact le_rfl
  have hsum0 := le_antisymm (Finset.sum_nonpos fun σ _ => hnn σ) (W ▸ hR2)
  have hzero := (Finset.sum_eq_zero_iff_of_nonpos fun σ _ => hnn σ).1 hsum0
  have hlt : ∀ σ : DoubleSurface F, (⟨σ.fst, σ.fst_mem⟩ : F.support) < ⟨σ.snd, σ.snd_mem⟩ →
      a σ = 0 := by
    intro σ hσ
    have h := hzero σ (Finset.mem_univ σ)
    rw [if_pos hσ] at h
    have h1 : (n ⟨σ.fst, σ.fst_mem⟩ : ℚ) ≠ 0 := by exact_mod_cast (hn _).ne'
    have h2 : (n ⟨σ.snd, σ.snd_mem⟩ : ℚ) ≠ 0 := by exact_mod_cast (hn _).ne'
    simpa [h1, h2, (hqpos σ).ne'] using h
  funext σ
  rcases lt_trichotomy (⟨σ.fst, σ.fst_mem⟩ : F.support) ⟨σ.snd, σ.snd_mem⟩ with h | h | h
  · exact hlt σ h
  · exact absurd (congrArg Subtype.val h) σ.fst_ne_snd
  · have := hlt σ.swap h
    have hs := (mem_orientedSurfaceCoefficients F).1 ha σ
    rw [this] at hs
    simpa using hs.symm

end Index

/-! ### Closed subschemes over `ℂ` -/

/-- A closed subscheme of a complete scheme over `ℂ` is complete. -/
public theorem isComplete_subscheme {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [MMP.Intersection.IsComplete ℂ X] (I : X.IdealSheafData) :
    MMP.Intersection.IsComplete ℂ I.subscheme :=
  inferInstanceAs (IsProper (I.subschemeι ≫ X ↘ Spec (.of ℂ)))

/-! ### Intersection numbers as degrees on Stacks' Chow groups -/

section ToNum

open Stacks.Chow

variable {W : Scheme.{0}} [W.Over (Spec (.of ℂ))] [IsProper (W ↘ Spec (.of ℂ))]

/-- `deg(c₁(L₀) c₁(L₁) c₁(L₂) ∩ [W]) = (L₀ · L₁ · L₂)` on a scheme of dimension three. -/
public theorem capDegree_fundamentalChowClass_eq_num3 (L : Fin (1 + 1 + 1) → W.Modules)
    [hL : ∀ j, SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 (L j)]
    (hd : topologicalKrullDim W = (1 + 1 + 1 : ℕ)) :
    (AlgebraicGeometry.capDegree ℂ (W ↘ Spec (.of ℂ)) L
      (fundamentalChowClass (fieldChowSituation ℂ) (W ↘ Spec (.of ℂ)) ((1 + 1 + 1 : ℕ) : ℤ)) :
        ℚ) = num3 W (W ↘ Spec (.of ℂ)) (L 0) (L 1) (L 2) := by
  rw [MMP.Chow.capDegree_fundamentalChowClass_eq_sheafIntersectionNumber (1 + 1 + 1) hd,
    num3_eq _ _ _ _ hd.le]
  exact congrArg (fun z : ℤ => (z : ℚ)) (sIN_congr_family _ _ _ _
    (funext fun t => by fin_cases t <;> rfl))

/-- `deg(c₁(L₀) c₁(L₁) ∩ [W]) = (L₀ · L₁)` on a scheme of dimension two. -/
public theorem capDegree_fundamentalChowClass_eq_num2 (L : Fin (1 + 1) → W.Modules)
    [∀ j, SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 (L j)]
    (hd : topologicalKrullDim W = (1 + 1 : ℕ)) :
    (AlgebraicGeometry.capDegree ℂ (W ↘ Spec (.of ℂ)) L
      (fundamentalChowClass (fieldChowSituation ℂ) (W ↘ Spec (.of ℂ)) ((1 + 1 : ℕ) : ℤ)) : ℚ) =
      num2 W (W ↘ Spec (.of ℂ)) (L 0) (L 1) := by
  rw [MMP.Chow.capDegree_fundamentalChowClass_eq_sheafIntersectionNumber (1 + 1) hd,
    num2_eq _ _ _ hd.le]
  exact congrArg (fun z : ℤ => (z : ℚ)) (sIN_congr_family _ _ _ _
    (funext fun t => by fin_cases t <;> rfl))

/-- `deg(c₁(A) c₁(B) c₁(C) ∩ [W]) = (A · B · C)` for the family `(A, B, C)`. -/
public theorem capDegree_snoc_snoc_eq_num3 (A B C : W.Modules)
    [SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 A]
    [SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 B]
    [SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 C]
    (hd : topologicalKrullDim W = (1 + 1 + 1 : ℕ)) :
    (AlgebraicGeometry.capDegree ℂ (W ↘ Spec (.of ℂ))
      (Fin.snoc (Fin.snoc (fun _ : Fin 1 => A) B : Fin (1 + 1) → W.Modules) C)
      (fundamentalChowClass (fieldChowSituation ℂ) (W ↘ Spec (.of ℂ)) ((1 + 1 + 1 : ℕ) : ℤ)) :
        ℚ) = num3 W (W ↘ Spec (.of ℂ)) A B C :=
  (capDegree_fundamentalChowClass_eq_num3 _ hd).trans
    (num3_congr _ _ _ _ _ _ _ ⟨Iso.refl _⟩ ⟨Iso.refl _⟩ ⟨Iso.refl _⟩)

/-- `deg(c₁(g^*A) c₁(g^*B) ∩ [S]) = (g^*A · g^*B)` for the pulled-back family `(A, B)`. -/
public theorem capDegree_pullback_snoc_eq_num2 {S : Scheme.{0}} [S.Over (Spec (.of ℂ))]
    [IsProper (S ↘ Spec (.of ℂ))] (g : S ⟶ W) (A B : W.Modules)
    [SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 A]
    [SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 B]
    [∀ k, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2
      ((Scheme.Modules.pullback g).obj
        ((Fin.snoc (fun _ : Fin 1 => A) B : Fin (1 + 1) → W.Modules) k))]
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 ((Scheme.Modules.pullback g).obj A)]
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 ((Scheme.Modules.pullback g).obj B)]
    (hd : topologicalKrullDim S = (1 + 1 : ℕ)) :
    (AlgebraicGeometry.capDegree ℂ (S ↘ Spec (.of ℂ))
      (fun k => (Scheme.Modules.pullback g).obj
        ((Fin.snoc (fun _ : Fin 1 => A) B : Fin (1 + 1) → W.Modules) k))
      (fundamentalChowClass (fieldChowSituation ℂ) (S ↘ Spec (.of ℂ)) ((1 + 1 : ℕ) : ℤ)) : ℚ) =
      num2 S (S ↘ Spec (.of ℂ)) ((Scheme.Modules.pullback g).obj A)
        ((Scheme.Modules.pullback g).obj B) :=
  (capDegree_fundamentalChowClass_eq_num2 _ hd).trans
    (num2_congr _ _ _ _ _ ⟨Iso.refl _⟩ ⟨Iso.refl _⟩)

end ToNum

/-! ### The key identity: intersecting a homologically trivial class with a component -/

section Key

open Stacks.Chow CategoryTheory.Limits

attribute [local instance] MMP.Chow.fibreProductOver MMP.Chow.isOver_fibreProduct_fst
  MMP.Chow.isOver_fibreProduct_snd MMP.Chow.isComplexScheme_fibreProduct

variable {Z : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [IsComplexScheme Z]
  [IsProper (Z ↘ Spec (.of ℂ))] [IsIntegral Z] {F : MMP.Mori.Divisor Z}
  (hB : F.IsSNC (Z ↘ Spec (.of ℂ))) (hdim : topologicalKrullDim Z = 4)
  [Fintype (DoubleSurface F)]
  (hvar : MMP.Mori.IsVariety ℂ (Z ↘ Spec (.of ℂ)))
  (hsm : MMP.Mori.IsSmoothScheme (Z ↘ Spec (.of ℂ)))
  (ε : F.support → Z.CartierDivisor)
  (hε : ∀ i, MMP.Intersection.IsWeilDivisorOfCartier (ε i) (Finsupp.single i.1 1))
  (π : ∀ i : F.support, MMP.Mori.PrimeDivisor i.1.idealSheaf.subscheme →
    i.1.idealSheaf.subscheme.CartierDivisor)
  (hπ : ∀ i P, MMP.Intersection.IsWeilDivisorOfCartier (π i P) (Finsupp.single P 1))

/-- The inclusion of a double surface `S` with second component `E`, into `E`. -/
public noncomputable abbrev tιOf {E : MMP.Mori.PrimeDivisor Z} (σ : DoubleSurface F)
    (h : σ.snd = E) : (dsIdeal σ).subscheme ⟶ E.idealSheaf.subscheme :=
  Scheme.IdealSheafData.inclusion (h ▸ fst_idealSheaf_le_dsIdeal σ.swap)

/-- The pull-back of an invertible module is invertible, for schemes in general. -/
private theorem isInvertible_pullback_presheaf {X Y : Scheme.{0}} (g : Y ⟶ X) (L : X.Modules)
    [h : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 ((Scheme.Modules.pullback g).obj L) :=
  have : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L := h
  GenuineChern.isInvertible_pullback g L

/-- The base change `Eᵢ ×_Z Z` of a component is proper over `ℂ`. -/
public theorem isProper_pullback_fst_id_comp (i : F.support) :
    IsProper (pullback.fst i.1.idealSheaf.subschemeι (𝟙 Z) ≫
      i.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) := by
  have : IsIso (pullback.fst i.1.idealSheaf.subschemeι (𝟙 Z)) := inferInstance
  have : IsProper (i.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) :=
    inferInstanceAs (IsProper (i.1.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ)))
  infer_instance

/-- The sheaf `𝒪(D)` of a Cartier divisor is invertible, in the form taken by
`MMP.Chow.pushforwardFirstChernCapFundamental`. -/
public theorem isInvertible_sheafObj_cartierDivisorSheaf {X : Scheme.{0}} (D : X.CartierDivisor) :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (MMP.CartierDivisor.sheaf D) :=
  inferInstance

/-- The class `(ιⱼ)_*(c₁(𝒪(π_P)) ∩ [Eⱼ]) ∈ A_2(Z)` of a prime divisor `P` of a component `Eⱼ`. -/
@[expose]
public noncomputable def piClass (j : F.support)
    (P : MMP.Mori.PrimeDivisor j.1.idealSheaf.subscheme) :
    chowGroup (fieldChowSituation ℂ) (Z ↘ Spec (.of ℂ)) ((1 + 1 : ℕ) : ℤ) :=
  haveI : IsComplexScheme j.1.idealSheaf.subscheme :=
    IsComplexScheme.of_isClosedImmersion j.1.idealSheaf.subschemeι
  haveI := isInvertible_sheafObj_cartierDivisorSheaf (π j P)
  MMP.Chow.pushforwardFirstChernCapFundamental j.1.idealSheaf.subschemeι 1
    (MMP.CartierDivisor.sheaf (π j P))

include hB hdim in
/-- A component `Eⱼ` is smooth of relative dimension three. -/
private theorem smoothOfRelativeDimension_component (j : F.support) :
    SmoothOfRelativeDimension 3 (j.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) := by
  haveI : IsIntegral j.1.idealSheaf.subscheme := j.1.integral
  haveI : IsComplexScheme j.1.idealSheaf.subscheme :=
    IsComplexScheme.of_isClosedImmersion j.1.idealSheaf.subschemeι
  exact MMP.Fourfold.ConductorBlowup.smoothOfRelativeDimension_of_isSmoothScheme
    (⟨⟩ : AlgebraicGeometry.IsVariety ℂ (j.1.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ)))
    (hB.1 j.1 j.2) 3 (topologicalKrullDim_component hdim j)

include hB hdim hπ in
/-- The class of `(ιⱼ)_*(c₁(𝒪(π_P)) ∩ [Eⱼ])` is `(ιⱼ)_*[P]`. -/
private theorem chowCycleClass_piClass (hZp : IsProjectiveMorphism (Z ↘ Spec (.of ℂ)))
    (j : F.support) (P : MMP.Mori.PrimeDivisor j.1.idealSheaf.subscheme) :
    MMP.Chow.chowCycleClass ℚ (1 + 1) (piClass π j P) =
      componentHomologyMap j.1 4 (MMP.Chow.divisorClass j.1.idealSheaf.subscheme
        (Finsupp.single P 1)) := by
  classical
  haveI : IsIntegral j.1.idealSheaf.subscheme := j.1.integral
  haveI : IsComplexScheme j.1.idealSheaf.subscheme :=
    IsComplexScheme.of_isClosedImmersion j.1.idealSheaf.subschemeι
  have hvX : MMP.Mori.IsVariety ℂ (j.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) :=
    (⟨⟩ : AlgebraicGeometry.IsVariety ℂ (j.1.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ)))
  have hsmX : MMP.Mori.IsSmoothScheme (j.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) := hB.1 j.1 j.2
  haveI : Smooth (j.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) :=
    (MMP.Mori.isSmoothScheme_iff _).1 hsmX
  have hW : MMP.Mori.IsProjectiveVariety ℂ (j.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) :=
    (MMP.Mori.isProjectiveVariety_iff _ _).2
      ⟨hvX, isProjectiveMorphism_isClosedImmersion_comp _ _ hZp⟩
  haveI : IsLocallyNoetherian j.1.idealSheaf.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (j.1.idealSheaf.subscheme ↘ Spec (.of ℂ))
  haveI : IsNormal j.1.idealSheaf.subscheme :=
    isNormal_of_smooth_over_field (j.1.idealSheaf.subscheme ↘ Spec (.of ℂ))
  have h3 : topologicalKrullDim j.1.idealSheaf.subscheme = ((2 + 1 : ℕ) : WithBot ℕ∞) := by
    rw [topologicalKrullDim_component hdim j]; rfl
  rw [piClass, MMP.Chow.pushforwardFirstChernCapFundamental,
    MMP.Chow.chowCycleClass_properChowPushforward_of_isProper]
  have h := MMP.Chow.chowCycleClass_firstChernClassCapChow_fundamentalChowClass hW hsmX h3 P
    (π j P) (hπ j P)
  exact congrArg (componentHomologyMap j.1 4) h

include hvar hsm hε in
/-- **The normal sheaf of a component** `Eᵢ ⊆ Z` is `𝒪(εᵢ)|_{Eᵢ}`: the conormal sheaf of the
divisor is `ιᵢ^*𝒪_Z(Eᵢ)^∨` (`MMP.Chow.conormalModuleIsoPullbackDivisorDualSheaf`), and
`𝒪(εᵢ) ≅ 𝒪_Z(Eᵢ)` for the effective Cartier divisor `εᵢ` cutting out `Eᵢ`. -/
private theorem nonempty_dualSheaf_conormalModule_iso (i : F.support)
    (hreg : Stacks.AlgebraicGeometry.RegularIdealSheaf.IsRegularClosedImmersionOfCodim
      i.1.idealSheaf.subschemeι 1) :
    Nonempty (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf
        (Stacks.Chow.conormalModule i.1.idealSheaf.subschemeι) ≅
      (Scheme.Modules.pullback i.1.idealSheaf.subschemeι).obj (MMP.CartierDivisor.sheaf (ε i))) := by
  set f := i.1.idealSheaf.subschemeι
  obtain ⟨hD, hsub⟩ := exists_isEffective_eps ℂ (Z ↘ Spec (.of ℂ)) hvar hsm ε hε i
  have hker : f.ker = i.1.idealSheaf := Scheme.IdealSheafData.ker_subschemeι _
  haveI : Stacks.Divisors.IsEffectiveCartierDivisor f.ker :=
    MMP.isEffectiveCartierDivisor_ker_of_isRegularClosedImmersionOfCodim_one f hreg
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (Z ↘ Spec (.of ℂ))
  have hL : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{0, 0, 0}
      (Stacks.Divisors.divisorSheaf f.ker) :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ 1
      (hM := Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_one_of_isInvertible _
        (Stacks.Divisors.isInvertible_divisorSheaf f.ker))
  have hLd : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{0, 0, 0}
      (Scheme.Modules.dual (Stacks.Divisors.divisorSheaf f.ker)) :=
    Stacks.Chow.isFiniteLocallyFree_dualSheaf' (Stacks.Divisors.divisorSheaf f.ker) (h := hL)
  haveI := Stacks.Chow.isIso_toDoubleDual_of_isFiniteLocallyFree _ hL
  exact ⟨Stacks.AlgebraicGeometry.ReflexiveModules.dualSheafIsoOfIso
      (MMP.Chow.conormalModuleIsoPullbackDivisorDualSheaf f).symm ≪≫
    (Stacks.FundamentalGroup.pullbackDualSheafIso f _ hLd).symm ≪≫
    (Scheme.Modules.pullback f).mapIso
      ((asIso (Stacks.AlgebraicGeometry.ReflexiveModules.toDoubleDual
          (Stacks.Divisors.divisorSheaf f.ker))).symm ≪≫
        eqToIso (congrArg Stacks.Divisors.invertibleSheaf' (hker.trans hsub.symm)) ≪≫
        (MMP.CartierDivisor.sheafIsoInvertibleSheaf (ε i) hD).symm)⟩

include hB hdim hvar hsm hε hπ in
/-- **The self term**: `deg(c₁(H) ∩ Eᵢ^!((ιᵢ)_*(c₁(π_P) ∩ [Eᵢ]))) = (H · π_P · Eᵢ|_{Eᵢ})`. -/
private theorem capDegree_divisorGysin_piClass_self (i : F.support)
    (hreg : Stacks.AlgebraicGeometry.RegularIdealSheaf.IsRegularClosedImmersionOfCodim
      i.1.idealSheaf.subschemeι 1)
    (H : i.1.idealSheaf.subscheme.Modules)
    [hH : SheafOfModules.IsInvertible i.1.idealSheaf.subscheme.presheaf
      i.1.idealSheaf.subscheme.ringCatSheaf.2 H]
    (P : MMP.Mori.PrimeDivisor i.1.idealSheaf.subscheme)
    {pq : IsProper (pullback.fst i.1.idealSheaf.subschemeι (𝟙 Z) ≫
      i.1.idealSheaf.subscheme ↘ Spec (.of ℂ))}
    {hK : ∀ j : Fin 1, SheafOfModules.IsInvertible
        (pullback i.1.idealSheaf.subschemeι (𝟙 Z)).presheaf
        (pullback i.1.idealSheaf.subschemeι (𝟙 Z)).ringCatSheaf.2
        ((fun _ : Fin 1 =>
          (Scheme.Modules.pullback (pullback.fst i.1.idealSheaf.subschemeι (𝟙 Z))).obj H) j)} :
    (@AlgebraicGeometry.capDegree ℂ _ _
      (pullback.fst i.1.idealSheaf.subschemeι (𝟙 Z) ≫ i.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) pq 1
      (fun _ : Fin 1 =>
        (Scheme.Modules.pullback (pullback.fst i.1.idealSheaf.subschemeι (𝟙 Z))).obj H) hK
      (MMP.Chow.divisorGysin i.1.idealSheaf.subschemeι hreg 1 (piClass π i P)) : ℚ) =
      num3 i.1.idealSheaf.subscheme (i.1.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ)) H
        (MMP.CartierDivisor.sheaf (π i P))
        ((Scheme.Modules.pullback i.1.idealSheaf.subschemeι).obj
          (MMP.CartierDivisor.sheaf (ε i))) := by
  classical
  set f := i.1.idealSheaf.subschemeι
  haveI : IsIntegral i.1.idealSheaf.subscheme := i.1.integral
  haveI : IsComplexScheme i.1.idealSheaf.subscheme := IsComplexScheme.of_isClosedImmersion f
  haveI : IsProper (i.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) :=
    inferInstanceAs (IsProper (f ≫ Z ↘ Spec (.of ℂ)))
  have hdim3 : topologicalKrullDim i.1.idealSheaf.subscheme = (1 + 1 + 1 : ℕ) := by
    rw [topologicalKrullDim_component hdim i]; rfl
  haveI := isInvertible_sheafObj_cartierDivisorSheaf (π i P)
  haveI : SheafOfModules.IsInvertible i.1.idealSheaf.subscheme.presheaf
      i.1.idealSheaf.subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback f).obj (MMP.CartierDivisor.sheaf (ε i))) :=
    isInvertible_pullback_presheaf f _
  obtain ⟨eN⟩ := nonempty_dualSheaf_conormalModule_iso hvar hsm ε hε i hreg
  exact (congrArg (Int.cast : ℤ → ℚ) ((MMP.Chow.capDegree_congr _ (by rfl) (by rfl)).trans
    ((MMP.Chow.capDegree_divisorGysin_pushforwardFirstChernCapFundamental_self f hreg hdim3 H
      (MMP.CartierDivisor.sheaf (π i P))
      ((Scheme.Modules.pullback f).obj (MMP.CartierDivisor.sheaf (ε i))) ⟨eN⟩).trans
      (MMP.Chow.capDegree_congr _ (by rfl) (by rfl))))).trans
    ((capDegree_snoc_snoc_eq_num3 _ _ _ hdim3).trans
      (num3_congr _ _ _ _ _ _ _ ⟨Iso.refl _⟩ ⟨Iso.refl _⟩ ⟨Iso.refl _⟩))

/-- The cycle of a closed subscheme only depends on its ideal. -/
private theorem cycleAssociatedToClosedSubscheme_ideal_congr {Y : Scheme.{0}}
    (q : Y ⟶ (fieldChowSituation ℂ).S) [LocallyOfFiniteType q] {I J : Y.IdealSheafData}
    (h : I = J) (d : ℤ) :
    cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ) q I.subschemeι d =
      cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ) q J.subschemeι d := by
  subst h
  rfl

/-- The cycle of a closed immersion only depends on the morphism. -/
private theorem cycleAssociatedToClosedSubscheme_congr_hom' {Y W : Scheme.{0}}
    (q : Y ⟶ (fieldChowSituation ℂ).S) [LocallyOfFiniteType q] {a b : W ⟶ Y}
    [IsClosedImmersion a] [IsClosedImmersion b] (hab : a = b) (d : ℤ) :
    cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ) q a d =
      cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ) q b d := by
  subst hab
  rfl

/-- The cycle of the vanishing ideal of a finite union of pairwise disjoint closed sets is the sum
of the cycles of the vanishing ideals of the pieces (Stacks 02QU for a disjoint union). -/
private theorem cycleAssociatedToClosedSubscheme_vanishingIdeal_finsetSup {X : Scheme.{0}}
    (sX : X ⟶ (Stacks.Chow.fieldChowSituation ℂ).S) [LocallyOfFiniteType sX] {ι : Type*}
    (s : Finset ι) (T : ι → TopologicalSpace.Closeds X)
    (hdisj : (s : Set ι).PairwiseDisjoint fun a => (T a : Set X)) (k : ℤ) :
    cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ) sX
        (Scheme.IdealSheafData.vanishingIdeal (s.sup T)).subschemeι k =
      ∑ a ∈ s, cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ) sX
        (Scheme.IdealSheafData.vanishingIdeal (T a)).subschemeι k := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sup_empty, Finset.sum_empty, Scheme.IdealSheafData.vanishingIdeal_bot]
    refine Subtype.ext (Function.locallyFinsuppWithin.ext fun y => ?_)
    rw [Stacks.Chow.cycleAssociatedToClosedSubscheme_apply_eq_zero_of_notMem_range _ _ _ k
      (by rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_top]
          exact id)]
    rfl
  | insert a s ha ih =>
    rw [Finset.sup_insert, Scheme.IdealSheafData.vanishingIdeal_sup,
      cycleAssociatedToClosedSubscheme_inf (fieldChowSituation ℂ) sX _ _ k ?_,
      ih (hdisj.subset (Finset.coe_subset.2 (Finset.subset_insert a s))), Finset.sum_insert ha]
    intro x hx
    exfalso
    rw [Scheme.IdealSheafData.support_sup] at hx
    obtain ⟨hxa, hxs⟩ := hx
    have hxa' : x ∈ (T a : Set X) := by
      rw [← Scheme.IdealSheafData.coe_support_vanishingIdeal (T a)]; exact hxa
    have hxs' : x ∈ ((s.sup T : TopologicalSpace.Closeds X) : Set X) := by
      rw [← Scheme.IdealSheafData.coe_support_vanishingIdeal (s.sup T)]; exact hxs
    rw [TopologicalSpace.Closeds.coe_finset_sup, Finset.sup_set_eq_biUnion, Set.mem_iUnion₂] at hxs'
    replace hxa := hxa'
    replace hxs := hxs'
    obtain ⟨b, hb, hxb⟩ := hxs
    exact Set.disjoint_left.1 (hdisj (Finset.mem_coe.2 (Finset.mem_insert_self a s))
      (Finset.mem_coe.2 (Finset.mem_insert_of_mem hb)) (fun h => ha (h ▸ hb))) hxa hxb

include hB in
open Classical in
/-- **`Eᵢ ∩ Eⱼ` as a cycle on `Eⱼ` is the sum of its double surfaces**:
`[Eᵢ|_{Eⱼ}]_k = ∑_{S ⊆ Eⱼ ∩ Eᵢ} [S]_k`. -/
private theorem cycleAssociatedToClosedSubscheme_comap_eq_sum (i j : F.support) (hji : j ≠ i)
    (k : ℤ) :
    cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ)
        (j.1.idealSheaf.subscheme ↘ Spec (.of ℂ))
        (i.1.idealSheaf.comap j.1.idealSheaf.subschemeι).subschemeι k =
      ∑ σ : {σ : DoubleSurface F // σ.fst = j.1 ∧ σ.snd = i.1},
        cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ)
          (j.1.idealSheaf.subscheme ↘ Spec (.of ℂ))
          (rhoOf hB σ.1 σ.2.1).idealSheaf.subschemeι k := by
  classical
  obtain ⟨E, hE⟩ := j
  have hEi : i.1 ≠ E := fun h => hji (Subtype.ext h.symm)
  have hred := (isEffectiveCartierDivisor_comap_component hB
    (a := i) (b := ⟨E, hE⟩) (fun h => hji h.symm)).2
  set ι := E.idealSheaf.subschemeι
  let T : {σ : DoubleSurface F // σ.fst = E ∧ σ.snd = i.1} →
      TopologicalSpace.Closeds E.idealSheaf.subscheme := fun σ =>
    (rhoOf hB σ.1 σ.2.1).idealSheaf.support
  have hT : ((i.1.idealSheaf.comap ι).support : Set E.idealSheaf.subscheme) =
      ⋃ σ ∈ (Finset.univ : Finset {σ : DoubleSurface F // σ.fst = E ∧ σ.snd = i.1}),
        (T σ : Set E.idealSheaf.subscheme) := by
    ext x
    rw [Scheme.IdealSheafData.support_comap]
    constructor
    · intro hx
      have hxE : ι x ∈ E.support := by
        change ι x ∈ (E.idealSheaf.support : Set Z)
        rw [← E.idealSheaf.range_subschemeι]
        exact ⟨x, rfl⟩
      let σ : DoubleSurface F := ⟨E, i.1, hE, i.2, hEi.symm,
        connectedComponentIn (E.support ∩ i.1.support) (ι x), ⟨ι x, ⟨hxE, hx⟩, rfl⟩⟩
      refine Set.mem_biUnion (x := ⟨σ, rfl, rfl⟩) (Finset.mem_univ _) ?_
      have hmem : ι x ∈ σ.carrier := mem_connectedComponentIn ⟨hxE, hx⟩
      rw [← image_support_rhoOf hB σ rfl] at hmem
      obtain ⟨x', hx', hxx'⟩ := hmem
      change x ∈ ((rhoOf hB σ rfl).idealSheaf.support : Set _)
      rw [← ι.isClosedEmbedding.injective hxx']
      exact hx'
    · intro hx
      obtain ⟨σ, -, hxσ⟩ := Set.mem_iUnion₂.1 hx
      change x ∈ ((rhoOf hB σ.1 σ.2.1).idealSheaf.support : Set _) at hxσ
      have : ι x ∈ σ.1.carrier := by
        rw [← image_support_rhoOf hB σ.1 σ.2.1]
        exact ⟨x, hxσ, rfl⟩
      exact σ.2.2 ▸ (σ.1.carrier_subset this).2
  have hdisj : ((Finset.univ : Finset {σ : DoubleSurface F // σ.fst = E ∧ σ.snd = i.1}) :
      Set {σ : DoubleSurface F // σ.fst = E ∧ σ.snd = i.1}).PairwiseDisjoint
      fun σ => (T σ : Set E.idealSheaf.subscheme) := by
    intro σ _ τ _ hne
    exact disjoint_support_rhoOf hB σ.2.1 τ.2.1 (σ.2.2.trans τ.2.2.symm)
      (fun h => hne (Subtype.ext h))
  have hD : i.1.idealSheaf.comap ι = Scheme.IdealSheafData.vanishingIdeal (Finset.univ.sup T) := by
    rw [Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme _
      (i.1.idealSheaf.comap ι).support rfl]
    congr 1
    refine TopologicalSpace.Closeds.ext (hT.trans ?_)
    rw [TopologicalSpace.Closeds.coe_finset_sup, Finset.sup_set_eq_biUnion]
    rfl
  have hρ : ∀ σ : {σ : DoubleSurface F // σ.fst = E ∧ σ.snd = i.1},
      (rhoOf hB σ.1 σ.2.1).idealSheaf = Scheme.IdealSheafData.vanishingIdeal (T σ) := fun σ => by
    have := (rhoOf hB σ.1 σ.2.1).integral
    exact Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme _ _ rfl
  rw [hD, cycleAssociatedToClosedSubscheme_vanishingIdeal_finsetSup _ _ _ hdisj k]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← hρ σ]

/-- Rewriting the class in a degree, keeping the degree's own proofs of properness and
invertibility: the kernel then compares the classes alone. -/
private theorem capDegree_congr_arg {X : Scheme.{0}} (q : X ⟶ Spec (.of ℂ)) {p : IsProper q}
    {d : ℕ} (L : Fin d → X.Modules)
    {h : ∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)}
    {a b : chowGroup (fieldChowSituation ℂ) q d} (hab : a = b) :
    @AlgebraicGeometry.capDegree ℂ _ X q p d L h a = @AlgebraicGeometry.capDegree ℂ _ X q p d L h b :=
  congrArg _ hab

/-- `Int.cast_sum` into `ℚ`, stated with the cast `(· : ℚ)` that statements in this file elaborate
to, so that a rewrite with it leaves the cast of each summand in that form. -/
private theorem intCast_sum_rat {ι : Type*} (s : Finset ι) (g : ι → ℤ) :
    ((∑ x ∈ s, g x : ℤ) : ℚ) = ∑ x ∈ s, (g x : ℚ) :=
  Int.cast_sum s g

/-- The double surface `S` of `(Eⱼ, Eᵢ)`, as a closed subscheme of `Eᵢ ×_Z Eⱼ`. -/
private noncomputable def dsLift (i j : F.support)
    (σ : {σ : DoubleSurface F // σ.fst = j.1 ∧ σ.snd = i.1}) :
    (dsIdeal σ.1).subscheme ⟶
      pullback i.1.idealSheaf.subschemeι (j.1.idealSheaf.subschemeι ≫ 𝟙 Z) :=
  pullback.lift (tιOf σ.1 σ.2.2) (sιOf σ.1 σ.2.1) (by
    rw [Category.comp_id, Scheme.IdealSheafData.inclusion_subschemeι,
      Scheme.IdealSheafData.inclusion_subschemeι])

private theorem dsLift_fst (i j : F.support)
    (σ : {σ : DoubleSurface F // σ.fst = j.1 ∧ σ.snd = i.1}) :
    dsLift i j σ ≫ pullback.fst _ _ = tιOf σ.1 σ.2.2 :=
  pullback.lift_fst _ _ _

private theorem dsLift_snd (i j : F.support)
    (σ : {σ : DoubleSurface F // σ.fst = j.1 ∧ σ.snd = i.1}) :
    dsLift i j σ ≫ pullback.snd _ _ = sιOf σ.1 σ.2.1 :=
  pullback.lift_snd _ _ _

private instance isClosedImmersion_dsLift (i j : F.support)
    (σ : {σ : DoubleSurface F // σ.fst = j.1 ∧ σ.snd = i.1}) :
    IsClosedImmersion (dsLift i j σ) := by
  haveI : IsClosedImmersion (dsLift i j σ ≫ pullback.snd i.1.idealSheaf.subschemeι
      (j.1.idealSheaf.subschemeι ≫ 𝟙 Z)) := by
    rw [dsLift_snd]; infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _
    (pullback.snd i.1.idealSheaf.subschemeι (j.1.idealSheaf.subschemeι ≫ 𝟙 Z))

private theorem dsLift_comp_over (i j : F.support)
    (σ : {σ : DoubleSurface F // σ.fst = j.1 ∧ σ.snd = i.1}) :
    dsLift i j σ ≫ (pullback.fst i.1.idealSheaf.subschemeι (j.1.idealSheaf.subschemeι ≫ 𝟙 Z) ≫
      i.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) = (dsIdeal σ.1).subscheme ↘ Spec (.of ℂ) := by
  rw [← Category.assoc, dsLift_fst]
  change tιOf σ.1 σ.2.2 ≫ i.1.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ) =
    (dsIdeal σ.1).subschemeι ≫ Z ↘ Spec (.of ℂ)
  rw [← Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]

private theorem pullback_snd_comp_over (i j : F.support) :
    pullback.snd i.1.idealSheaf.subschemeι (j.1.idealSheaf.subschemeι ≫ 𝟙 Z) ≫
        j.1.idealSheaf.subscheme ↘ Spec (.of ℂ) =
      pullback.fst i.1.idealSheaf.subschemeι (j.1.idealSheaf.subschemeι ≫ 𝟙 Z) ≫
        i.1.idealSheaf.subscheme ↘ Spec (.of ℂ) := by
  change pullback.snd _ _ ≫ j.1.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ) =
    pullback.fst _ _ ≫ i.1.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ)
  rw [← Category.assoc, ← Category.assoc, pullback.condition]
  simp

/-- **A fundamental class from a decomposition of its image cycle.** If a closed immersion
`p : P ⟶ E` carries `[P]_k` to `∑ₐ [Sₐ]_k` for closed subschemes `κₐ : Sₐ ⟶ P`, then
`[P]_k = ∑ₐ (κₐ)_*[Sₐ]_k` in `A_k(P)`: proper push-forward along a closed immersion is injective
on cycles. -/
private theorem fundamentalChowClass_eq_sum_of_cycle {P E : Scheme.{0}}
    (sP : P ⟶ (fieldChowSituation ℂ).S) [LocallyOfFiniteType sP]
    (sE : E ⟶ (fieldChowSituation ℂ).S) [LocallyOfFiniteType sE] (p : P ⟶ E)
    [IsClosedImmersion p] (hp : p ≫ sE = sP) {ι : Type} [Fintype ι] (S : ι → Scheme.{0})
    (sS : ∀ a, S a ⟶ (fieldChowSituation ℂ).S) [∀ a, LocallyOfFiniteType (sS a)]
    (κ : ∀ a, S a ⟶ P) [∀ a, IsClosedImmersion (κ a)] [∀ a, IsClosedImmersion (κ a ≫ p)]
    (hκ : ∀ a, κ a ≫ sP = sS a) (k : ℤ)
    (h : cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ) sE p k =
      ∑ a, cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ) sE (κ a ≫ p) k) :
    fundamentalChowClass (fieldChowSituation ℂ) sP k =
      ∑ a, properChowPushforward (fieldChowSituation ℂ) (sS a) sP (κ a) (hκ a) k
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _)
        (fundamentalChowClass (fieldChowSituation ℂ) (sS a) k) := by
  simp only [fundamentalChowClass, properChowPushforward_mk, ← map_sum]
  congr 1
  apply properPushforward_injective_of_isClosedImmersion (fieldChowSituation ℂ) sP sE p hp k
  rw [← properPushforwardHom_apply (fieldChowSituation ℂ) _ _ p hp k (∑ a, _), map_sum]
  simp only [properPushforwardHom_apply]
  rw [Stacks.Chow.fundamentalCycle,
    properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp,
    cycleAssociatedToClosedSubscheme_congr_hom' _ (Category.id_comp _), h]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hc := congrFun (properPushforward_comp (fieldChowSituation ℂ) _ _ sE (κ a) p (hκ a) hp k)
    (Stacks.Chow.fundamentalCycle (fieldChowSituation ℂ) (sS a) k)
  rw [Function.comp_apply] at hc
  rw [hc, Stacks.Chow.fundamentalCycle,
    properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp,
    cycleAssociatedToClosedSubscheme_congr_hom' _ (Category.id_comp _)]

include hB in
open Classical in
/-- **`[Eᵢ ×_Z Eⱼ]_k = ∑_{S ⊆ Eⱼ ∩ Eᵢ} [S]_k`** in `A_k(Eᵢ ×_Z Eⱼ)`. -/
private theorem fundamentalChowClass_pullback_eq_sum (i j : F.support) (hji : j ≠ i) (k : ℤ) :
    fundamentalChowClass (fieldChowSituation ℂ)
        (pullback.fst i.1.idealSheaf.subschemeι (j.1.idealSheaf.subschemeι ≫ 𝟙 Z) ≫
          i.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) k =
      ∑ σ : {σ : DoubleSurface F // σ.fst = j.1 ∧ σ.snd = i.1},
        properChowPushforward (fieldChowSituation ℂ) ((dsIdeal σ.1).subscheme ↘ Spec (.of ℂ))
          (pullback.fst i.1.idealSheaf.subschemeι (j.1.idealSheaf.subschemeι ≫ 𝟙 Z) ≫
            i.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) (dsLift i j σ) (dsLift_comp_over i j σ) k
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _)
          (fundamentalChowClass (fieldChowSituation ℂ) ((dsIdeal σ.1).subscheme ↘ Spec (.of ℂ))
            k) := by
  classical
  refine fundamentalChowClass_eq_sum_of_cycle _ (j.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) _
    (pullback_snd_comp_over i j) _ _ (dsLift i j) (dsLift_comp_over i j) k ?_
  rw [cycleAssociatedToClosedSubscheme_ker, Stacks.IdealSheaf.ker_pullback_snd,
    Scheme.IdealSheafData.ker_subschemeι,
    cycleAssociatedToClosedSubscheme_ideal_congr _
      (show i.1.idealSheaf.comap (j.1.idealSheaf.subschemeι ≫ 𝟙 Z) =
        i.1.idealSheaf.comap j.1.idealSheaf.subschemeι by rw [Category.comp_id]),
    cycleAssociatedToClosedSubscheme_comap_eq_sum hB i j hji k]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [cycleAssociatedToClosedSubscheme_ker (fieldChowSituation ℂ) _ (dsLift i j σ ≫ _),
    show (dsLift i j σ ≫ pullback.snd _ _).ker = (rhoOf hB σ.1 σ.2.1).idealSheaf by
      rw [dsLift_snd, ker_sιOf hB]]

/-- `deg(c₁(L) ∩ a)` only depends on the data: any two instance arguments, and equal classes,
give the same degree. Proved under `congrArg`, so that the kernel compares the instance
arguments by proof irrelevance and never unfolds `capDegree` under the coercion to a function. -/
private theorem intCast_capDegree_congr {W : Scheme.{0}} {q : W ⟶ Spec (.of ℂ)}
    (h₁ h₂ : IsProper q) {d : ℕ} {L : Fin d → W.Modules}
    (i₁ i₂ : ∀ j, SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 (L j))
    {a b : chowGroup (fieldChowSituation ℂ) q d} (hab : a = b) :
    ((@AlgebraicGeometry.capDegree ℂ _ W q h₁ d L i₁ a : ℤ) : ℚ) =
      ((@AlgebraicGeometry.capDegree ℂ _ W q h₂ d L i₂ b : ℤ) : ℚ) := by
  subst hab
  exact (congrArg (fun h => ((@AlgebraicGeometry.capDegree ℂ _ W q h d L i₁ a : ℤ) : ℚ))
    (rfl : h₁ = h₂)).trans
    (congrArg (fun i => ((@AlgebraicGeometry.capDegree ℂ _ W q h₂ d L i a : ℤ) : ℚ))
      (rfl : i₁ = i₂))

/-- `deg(c₁(L) ∩ a) = deg(c₁(L) ∩ b)` for `a = b`, under `congrArg`. -/
private theorem intCast_capDegree_congr_arg {W : Scheme.{0}} {q : W ⟶ Spec (.of ℂ)}
    (h : IsProper q) {d : ℕ} {L : Fin d → W.Modules}
    (i : ∀ j, SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 (L j))
    {a b : chowGroup (fieldChowSituation ℂ) q d} (hab : a = b) :
    ((@AlgebraicGeometry.capDegree ℂ _ W q h d L i a : ℤ) : ℚ) =
      ((@AlgebraicGeometry.capDegree ℂ _ W q h d L i b : ℤ) : ℚ) :=
  congrArg (fun x => ((@AlgebraicGeometry.capDegree ℂ _ W q h d L i x : ℤ) : ℚ)) hab

/-- `deg(c₁(L) ∩ g_* β) = deg(c₁(g^*L) ∩ β)` (Stacks 02SU), with every instance argument
explicit. -/
private theorem intCast_capDegree_properChowPushforward {W S : Scheme.{0}}
    (q : W ⟶ Spec (.of ℂ)) (hq : IsProper q) (fS : S ⟶ Spec (.of ℂ)) (hS : IsProper fS)
    (g : S ⟶ W) (hgp : IsProper g) (hg : g ≫ q = fS) {d : ℕ} (L : Fin d → W.Modules)
    (iL : ∀ j, SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 (L j))
    (ipb : ∀ j, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2
      ((Scheme.Modules.pullback g).obj (L j)))
    (lS : LocallyOfFiniteType fS) (lq : LocallyOfFiniteType q)
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence (fieldChowSituation ℂ) fS q g hg d)
    (β : chowGroup (fieldChowSituation ℂ) fS d) :
    ((@AlgebraicGeometry.capDegree ℂ _ W q hq d L iL
        (@properChowPushforward (fieldChowSituation ℂ) S W fS lS q lq g hgp hg d hfac β) : ℤ) :
          ℚ) =
      ((@AlgebraicGeometry.capDegree ℂ _ S fS hS d (fun j => (Scheme.Modules.pullback g).obj (L j))
        ipb β : ℤ) : ℚ) := by
  refine Eq.trans (intCast_capDegree_congr hq hq iL iL ?_)
    (Eq.trans (congrArg (Int.cast : ℤ → ℚ) (capDegree_properChowPushforward ℂ q fS g hg L β)).symm
      (intCast_capDegree_congr _ hS _ ipb rfl))
  rfl
 

/-- `deg(c₁(g^*A₀) c₁(g^*B) ∩ [S]) = (g^*A₀ · g^*B)` on a surface, with every instance argument
explicit. -/
private theorem intCast_capDegree_pullback_snoc_eq_num2 {S W : Scheme.{0}}
    [S.Over (Spec (.of ℂ))] (g : S ⟶ W) (A : Fin 1 → W.Modules) (B : W.Modules)
    (hS : IsProper (S ↘ Spec (.of ℂ)))
    (ipb : ∀ k, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2
      ((Scheme.Modules.pullback g).obj ((Fin.snoc A B : Fin (1 + 1) → W.Modules) k)))
    (lS : LocallyOfFiniteType (S ↘ Spec (.of ℂ)))
    (hA : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2
      ((Scheme.Modules.pullback g).obj (A 0)))
    (hB : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2
      ((Scheme.Modules.pullback g).obj B))
    (hd : topologicalKrullDim S = (1 + 1 : ℕ)) :
    ((@AlgebraicGeometry.capDegree ℂ _ S (S ↘ Spec (.of ℂ)) hS (1 + 1)
        (fun k => (Scheme.Modules.pullback g).obj ((Fin.snoc A B : Fin (1 + 1) → W.Modules) k)) ipb
        (@fundamentalChowClass (fieldChowSituation ℂ) S (S ↘ Spec (.of ℂ)) lS
          ((1 + 1 : ℕ) : ℤ)) : ℤ) : ℚ) =
      @num2 S (S ↘ Spec (.of ℂ)) hS ((Scheme.Modules.pullback g).obj (A 0))
        ((Scheme.Modules.pullback g).obj B) hA hB := by
  refine Eq.trans (intCast_capDegree_congr hS hS ipb ipb ?_)
    (Eq.trans (@capDegree_fundamentalChowClass_eq_num2 S _ hS _ ipb hd)
      (@num2_congr S _ hS _ _ _ _ (ipb 0) (ipb 1) hA hB ⟨Iso.refl _⟩ ⟨Iso.refl _⟩))
  rfl
 

open Classical in
include hB hdim hvar hsm hε hπ in
/-- **The cross terms**: for `j ≠ i`,
`deg(c₁(H) ∩ Eᵢ^!((ιⱼ)_*(c₁(π_P) ∩ [Eⱼ]))) = ∑_{S ⊆ Eⱼ ∩ Eᵢ} (H|_S · π_P|_S)`. -/
private theorem capDegree_divisorGysin_piClass_ne (i j : F.support) (hji : j ≠ i)
    (hreg : Stacks.AlgebraicGeometry.RegularIdealSheaf.IsRegularClosedImmersionOfCodim
      i.1.idealSheaf.subschemeι 1)
    (H : i.1.idealSheaf.subscheme.Modules)
    [hH : SheafOfModules.IsInvertible i.1.idealSheaf.subscheme.presheaf
      i.1.idealSheaf.subscheme.ringCatSheaf.2 H]
    (P : MMP.Mori.PrimeDivisor j.1.idealSheaf.subscheme)
    (K : Fin 1 → (pullback i.1.idealSheaf.subschemeι (𝟙 Z)).Modules)
    {pq : IsProper (pullback.fst i.1.idealSheaf.subschemeι (𝟙 Z) ≫
      i.1.idealSheaf.subscheme ↘ Spec (.of ℂ))}
    {hK : ∀ k, SheafOfModules.IsInvertible (pullback i.1.idealSheaf.subschemeι (𝟙 Z)).presheaf
      (pullback i.1.idealSheaf.subschemeι (𝟙 Z)).ringCatSheaf.2 (K k)}
    (eK : ∀ k, Nonempty ((Scheme.Modules.pullback
      (pullback.fst i.1.idealSheaf.subschemeι (𝟙 Z))).obj H ≅ K k)) :
    (@AlgebraicGeometry.capDegree ℂ _ _
      (pullback.fst i.1.idealSheaf.subschemeι (𝟙 Z) ≫ i.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) pq 1
      K hK (MMP.Chow.divisorGysin i.1.idealSheaf.subschemeι hreg 1 (piClass π j P)) : ℚ) =
      ∑ σ : {σ : DoubleSurface F // σ.fst = j.1 ∧ σ.snd = i.1},
        num2 (dsIdeal σ.1).subscheme ((dsIdeal σ.1).subschemeι ≫ Z ↘ Spec (.of ℂ))
          ((Scheme.Modules.pullback (tιOf σ.1 σ.2.2)).obj H)
          ((Scheme.Modules.pullback (sιOf σ.1 σ.2.1)).obj (MMP.CartierDivisor.sheaf (π j P))) := by
  classical
  revert K
  set f := i.1.idealSheaf.subschemeι
  set t := j.1.idealSheaf.subschemeι
  intro K hK eK
  haveI : IsIntegral j.1.idealSheaf.subscheme := j.1.integral
  haveI : IsComplexScheme j.1.idealSheaf.subscheme := IsComplexScheme.of_isClosedImmersion t
  haveI : IsProper (i.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) :=
    inferInstanceAs (IsProper (f ≫ Z ↘ Spec (.of ℂ)))
  have hV : topologicalKrullDim j.1.idealSheaf.subscheme = (1 + 1 + 1 : ℕ) := by
    rw [topologicalKrullDim_component hdim j]; rfl
  -- the base change `Eᵢ ×_Z Eⱼ ⟶ Eⱼ` is again a divisor: `Eⱼ ⊄ Eᵢ`
  have ht : Stacks.AlgebraicGeometry.RegularIdealSheaf.IsRegularClosedImmersionOfCodim
      (pullback.snd f (t ≫ 𝟙 Z)) 1 := by
    rcases MMP.Chow.isIso_or_isRegularClosedImmersionOfCodim_one_pullback_snd f (t ≫ 𝟙 Z) hreg
      with h | h
    · exfalso
      refine not_support_subset_of_ne (fun e => hji (Subtype.ext e)) ?_
      intro x hx
      have hx' : x ∈ Set.range t.base := by
        rw [Scheme.IdealSheafData.range_subschemeι]; exact hx
      obtain ⟨y, rfl⟩ := hx'
      have he : t = (inv (pullback.snd f (t ≫ 𝟙 Z)) ≫ pullback.fst f (t ≫ 𝟙 Z)) ≫ f := by
        rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc, Category.comp_id]
      change t.base y ∈ (i.1.idealSheaf.support : Set Z)
      rw [← Scheme.IdealSheafData.range_subschemeι, he, Scheme.Hom.comp_base, TopCat.coe_comp]
      exact Set.mem_range_self _
    · exact h
  haveI := isInvertible_sheafObj_cartierDivisorSheaf (π j P)
  haveI : IsProper (pullback f (t ≫ 𝟙 Z) ↘ Spec (.of ℂ)) :=
    inferInstanceAs (IsProper (pullback.fst f (t ≫ 𝟙 Z) ≫ i.1.idealSheaf.subscheme ↘ Spec (.of ℂ)))
  haveI : ∀ k, SheafOfModules.IsInvertible
      (pullback f (t ≫ 𝟙 Z)).presheaf (pullback f (t ≫ 𝟙 Z)).ringCatSheaf.2
      ((Scheme.Modules.pullback (bivariantBaseChangeMap f (𝟙 Z) t)).obj (K k)) := fun k =>
    isInvertible_pullback_presheaf _ _
  haveI : SheafOfModules.IsInvertible
      (pullback f (t ≫ 𝟙 Z)).presheaf (pullback f (t ≫ 𝟙 Z)).ringCatSheaf.2
      ((Scheme.Modules.pullback (pullback.snd f (t ≫ 𝟙 Z))).obj (MMP.CartierDivisor.sheaf (π j P))) :=
    isInvertible_pullback_presheaf _ _
  refine (congrArg (Int.cast : ℤ → ℚ) ((MMP.Chow.capDegree_congr _ (by rfl) (by rfl)).trans
    (MMP.Chow.capDegree_divisorGysin_pushforwardFirstChernCapFundamental_of_isRegular f hreg t hV ht
      (MMP.CartierDivisor.sheaf (π j P)) K))).trans ?_
  -- the summands as an opaque function, so that `map_sum` produces no redexes under the degree
  obtain ⟨φ, hφ, hφσ⟩ : ∃ φ : {σ : DoubleSurface F // σ.fst = j.1 ∧ σ.snd = i.1} →
      chowGroup (fieldChowSituation ℂ)
        (pullback.fst f (t ≫ 𝟙 Z) ≫ i.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) ((1 + 1 : ℕ) : ℤ),
      fundamentalChowClass (fieldChowSituation ℂ)
          (pullback.fst f (t ≫ 𝟙 Z) ≫ i.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) ((1 + 1 : ℕ) : ℤ) =
        ∑ σ, φ σ ∧
      ∀ σ, φ σ = properChowPushforward (fieldChowSituation ℂ)
        ((dsIdeal σ.1).subscheme ↘ Spec (.of ℂ))
        (pullback.fst f (t ≫ 𝟙 Z) ≫ i.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) (dsLift i j σ)
        (dsLift_comp_over i j σ) ((1 + 1 : ℕ) : ℤ)
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _)
        (fundamentalChowClass (fieldChowSituation ℂ) ((dsIdeal σ.1).subscheme ↘ Spec (.of ℂ))
          ((1 + 1 : ℕ) : ℤ)) :=
    ⟨_, fundamentalChowClass_pullback_eq_sum hB i j hji _, fun _ => rfl⟩
  refine (congrArg (Int.cast : ℤ → ℚ) ((capDegree_congr_arg _ _ (by exact hφ)).trans (map_sum _ _ _))).trans ?_
  rw [intCast_sum_rat]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [hφσ σ]
  haveI : IsProper ((dsIdeal σ.1).subscheme ↘ Spec (.of ℂ)) :=
    inferInstanceAs (IsProper ((dsIdeal σ.1).subschemeι ≫ Z ↘ Spec (.of ℂ)))
  haveI hA : SheafOfModules.IsInvertible
      (pullback f (t ≫ 𝟙 Z)).presheaf (pullback f (t ≫ 𝟙 Z)).ringCatSheaf.2
      ((Scheme.Modules.pullback (bivariantBaseChangeMap f (𝟙 Z) t)).obj ((Scheme.Modules.pullback (pullback.fst f (𝟙 Z))).obj H)) :=
    isInvertible_pullback_presheaf (bivariantBaseChangeMap f (𝟙 Z) t) _
  haveI hB' : SheafOfModules.IsInvertible
      (pullback f (t ≫ 𝟙 Z)).presheaf (pullback f (t ≫ 𝟙 Z)).ringCatSheaf.2
      ((Scheme.Modules.pullback (pullback.snd f (t ≫ 𝟙 Z))).obj (MMP.CartierDivisor.sheaf (π j P))) :=
    isInvertible_pullback_presheaf _ _
  haveI : ∀ k, SheafOfModules.IsInvertible (dsIdeal σ.1).subscheme.presheaf
      (dsIdeal σ.1).subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback (dsLift i j σ)).obj
        ((Fin.snoc (fun k => (Scheme.Modules.pullback (bivariantBaseChangeMap f (𝟙 Z) t)).obj (K k))
          ((Scheme.Modules.pullback (pullback.snd f (t ≫ 𝟙 Z))).obj
            (MMP.CartierDivisor.sheaf (π j P))) : Fin (1 + 1) → _) k)) :=
    fun k => isInvertible_pullback_presheaf _ _
  haveI : ∀ k, SheafOfModules.IsInvertible (dsIdeal σ.1).subscheme.presheaf
      (dsIdeal σ.1).subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback (dsLift i j σ)).obj
        ((Fin.snoc (fun _ : Fin 1 => (Scheme.Modules.pullback (bivariantBaseChangeMap f (𝟙 Z) t)).obj
          ((Scheme.Modules.pullback (pullback.fst f (𝟙 Z))).obj H))
          ((Scheme.Modules.pullback (pullback.snd f (t ≫ 𝟙 Z))).obj
            (MMP.CartierDivisor.sheaf (π j P))) : Fin (1 + 1) → _) k)) :=
    fun k => isInvertible_pullback_presheaf _ _
  haveI := isInvertible_pullback_presheaf (dsLift i j σ) ((Scheme.Modules.pullback (bivariantBaseChangeMap f (𝟙 Z) t)).obj
    ((Scheme.Modules.pullback (pullback.fst f (𝟙 Z))).obj H))
  haveI := isInvertible_pullback_presheaf (dsLift i j σ)
    ((Scheme.Modules.pullback (pullback.snd f (t ≫ 𝟙 Z))).obj (MMP.CartierDivisor.sheaf (π j P)))
  have hA : SheafOfModules.IsInvertible (dsIdeal σ.1).subscheme.presheaf
      (dsIdeal σ.1).subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback (dsLift i j σ)).obj
        ((Scheme.Modules.pullback (bivariantBaseChangeMap f (𝟙 Z) t)).obj (K 0))) :=
    isInvertible_pullback_presheaf _ _ (h := isInvertible_pullback_presheaf _ _)
  have hB'' : SheafOfModules.IsInvertible (dsIdeal σ.1).subscheme.presheaf
      (dsIdeal σ.1).subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback (dsLift i j σ)).obj
        ((Scheme.Modules.pullback (pullback.snd f (t ≫ 𝟙 Z))).obj
          (MMP.CartierDivisor.sheaf (π j P)))) :=
    isInvertible_pullback_presheaf _ _ (h := isInvertible_pullback_presheaf _ _)
  refine Eq.trans (intCast_capDegree_congr_arg _ _ ?_)
    (Eq.trans (intCast_capDegree_properChowPushforward _ _ _ inferInstance (dsLift i j σ)
      inferInstance (by exact dsLift_comp_over i j σ) _ _
      (fun _ => isInvertible_pullback_presheaf _ _) inferInstance inferInstance
      (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _)
      (fundamentalChowClass (fieldChowSituation ℂ) ((dsIdeal σ.1).subscheme ↘ Spec (.of ℂ))
        ((1 + 1 : ℕ) : ℤ)))
    (Eq.trans (intCast_capDegree_pullback_snoc_eq_num2 (dsLift i j σ) _ _ inferInstance _ _ hA hB''
      (by rw [topologicalKrullDim_dsIdeal hB hdim σ.1]; rfl)) ?_))
  · rfl
  have h1 : (dsLift i j σ ≫ bivariantBaseChangeMap f (𝟙 Z) t) ≫ pullback.fst f (𝟙 Z) = tιOf σ.1 σ.2.2 := by
    rw [Category.assoc, bivariantBaseChangeMap_fst, dsLift_fst]
  exact num2_congr _ _ _ _ _
    ⟨(Scheme.Modules.pullbackComp _ _).app _ ≪≫
      (Scheme.Modules.pullback _).mapIso (eK 0).some.symm ≪≫
      (Scheme.Modules.pullbackComp _ _).app H ≪≫ (Scheme.Modules.pullbackCongr h1).app H⟩
    ⟨(Scheme.Modules.pullbackComp _ _).app _ ≪≫
      (Scheme.Modules.pullbackCongr (dsLift_snd i j σ)).app _⟩

include hB hdim hvar hsm hε hπ in
open Classical in
/-- **Intersecting a homologically trivial class with a component.** For integral divisors
`cⱼ` on the components with `∑ⱼ (ιⱼ)_* [cⱼ] = 0` in `H₄(Z, ℚ)` and an invertible module `H` on
`Eᵢ`: `∑_P cᵢ(P) (H · π_P · Eᵢ|_{Eᵢ}) + ∑_{j ≠ i} ∑_{S ⊆ Eⱼ ∩ Eᵢ} ∑_P cⱼ(P) (H|_S · π_P|_S) = 0`.
The proof intersects `α = ∑ⱼ (ιⱼ)_*(∑_P cⱼ(P) c₁(π_P) ∩ [Eⱼ])` with the divisor `Eᵢ`: by Fulton's
Theorem 19.2 for a divisor `cl(Eᵢ^! α) = 0`, so `deg(c₁(H) ∩ Eᵢ^! α) = 0`, and the Gysin map is
computed at full excess on `Eᵢ` and at vanishing excess on the other components. -/
public theorem key_identity (hZp : IsProjectiveMorphism (Z ↘ Spec (.of ℂ)))
    (c : ∀ j : F.support, MMP.Mori.PrimeDivisor j.1.idealSheaf.subscheme →₀ ℤ)
    (hx : ∑ j : F.support, ∑ P ∈ (c j).support, (c j P : ℚ) • componentHomologyMap j.1 4
      (MMP.Chow.divisorClass j.1.idealSheaf.subscheme (Finsupp.single P 1)) = 0)
    (i : F.support) (H : i.1.idealSheaf.subscheme.Modules)
    [hH : SheafOfModules.IsInvertible i.1.idealSheaf.subscheme.presheaf
      i.1.idealSheaf.subscheme.ringCatSheaf.2 H] :
    ∑ P ∈ (c i).support, (c i P : ℚ) * num3 i.1.idealSheaf.subscheme
        (i.1.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ)) H
        (MMP.CartierDivisor.sheaf (π i P))
        ((Scheme.Modules.pullback i.1.idealSheaf.subschemeι).obj (MMP.CartierDivisor.sheaf (ε i))) +
      ∑ j ∈ Finset.univ.erase i, ∑ σ : {σ : DoubleSurface F // σ.fst = j.1 ∧ σ.snd = i.1},
        ∑ P ∈ (c j).support, (c j P : ℚ) * num2 (dsIdeal σ.1).subscheme
          ((dsIdeal σ.1).subschemeι ≫ Z ↘ Spec (.of ℂ))
          ((Scheme.Modules.pullback (tιOf σ.1 σ.2.2)).obj H)
          ((Scheme.Modules.pullback (sιOf σ.1 σ.2.1)).obj
            (MMP.CartierDivisor.sheaf (π j P))) = 0 := by
  classical
  set f := i.1.idealSheaf.subschemeι
  haveI : SmoothOfRelativeDimension 4 (Z ↘ Spec (.of ℂ)) :=
    MMP.Fourfold.ConductorBlowup.smoothOfRelativeDimension_of_isSmoothScheme hvar hsm 4 hdim
  haveI : SmoothOfRelativeDimension (3 + 1) (Z ↘ Spec (.of ℂ)) :=
    ‹SmoothOfRelativeDimension 4 (Z ↘ Spec (.of ℂ))›
  haveI : SmoothOfRelativeDimension 3 (f ≫ Z ↘ Spec (.of ℂ)) :=
    smoothOfRelativeDimension_component hB hdim i
  have hreg : Stacks.AlgebraicGeometry.RegularIdealSheaf.IsRegularClosedImmersionOfCodim f 1 :=
    isRegularClosedImmersionOfCodim_of_smoothOfRelativeDimension f (Z ↘ Spec (.of ℂ)) (n := 3)
  -- an ample invertible module on `Z` and on `Eᵢ ×_Z Z`
  obtain ⟨A, hAi, hA⟩ := MMP.Chow.exists_isAmple_of_isProjective (Z ↘ Spec (.of ℂ)) hZp
  have : SheafOfModules.IsInvertible Z.toRingedSpace.presheaf
      (structureSheafRing Z.toRingedSpace).property A := hAi
  have hA'i : Stacks.Ample.IsInvertibleModule (pullback f (𝟙 Z))
      ((Scheme.Modules.pullback (pullback.snd f (𝟙 Z))).obj A) :=
    isInvertibleModule_pullback _ _
  have : SheafOfModules.IsInvertible (pullback f (𝟙 Z)).toRingedSpace.presheaf
      (structureSheafRing (pullback f (𝟙 Z)).toRingedSpace).property
      ((Scheme.Modules.pullback (pullback.snd f (𝟙 Z))).obj A) := hA'i
  have hA' : Stacks.Ample.IsAmple (pullback f (𝟙 Z))
      ((Scheme.Modules.pullback (pullback.snd f (𝟙 Z))).obj A) :=
    (Stacks.AmpleBridge.isAmple_iff_isAmple _ _).mpr
      (Scheme.Modules.isAmple_pullback_of_isClosedImmersion (pullback.snd f (𝟙 Z)) A
        ((Stacks.AmpleBridge.isAmple_iff_isAmple Z A).mp hA))
  haveI : IsProper (i.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) :=
    inferInstanceAs (IsProper (i.1.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ)))
  -- the class `α` and its vanishing cycle class
  set α := ∑ j : F.support, ∑ P ∈ (c j).support, c j P • piClass π j P with hαdef
  have hα : MMP.Chow.chowCycleClass ℚ (1 + 1) α = 0 := by
    simp only [hαdef, map_sum, map_zsmul, chowCycleClass_piClass hB hdim π hπ hZp]
    rw [← hx]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun P _ =>
      (Int.cast_smul_eq_zsmul ℚ _ _).symm
  have hcl := MMP.Chow.chowCycleClass_divisorGysin_eq_zero f hreg A hA α hα
  haveI hK : ∀ j : Fin 1, SheafOfModules.IsInvertible (pullback f (𝟙 Z)).presheaf
      (pullback f (𝟙 Z)).ringCatSheaf.2
      ((fun _ : Fin 1 => (Scheme.Modules.pullback (pullback.fst f (𝟙 Z))).obj H) j) :=
    fun _ => isInvertible_pullback_presheaf _ _
  have h0 := @MMP.Chow.capDegree_eq_zero_of_chowCycleClass_eq_zero_of_isAmple _ _ _
    (isProper_pullback_fst_id_comp i) _ _ hA' 1
    (fun _ : Fin 1 => (Scheme.Modules.pullback (pullback.fst f (𝟙 Z))).obj H) _ _ hcl
  have h0' : ∑ j : F.support, ∑ P ∈ (c j).support, (c j P : ℚ) *
      (AlgebraicGeometry.capDegree ℂ (pullback.fst f (𝟙 Z) ≫ i.1.idealSheaf.subscheme ↘ Spec (.of ℂ))
        (fun _ : Fin 1 => (Scheme.Modules.pullback (pullback.fst f (𝟙 Z))).obj H)
        (MMP.Chow.divisorGysin f hreg 1 (piClass π j P)) : ℚ) = 0 := by
    have h1 := congrArg (fun z : ℤ => (z : ℚ)) h0
    simp only [Int.cast_zero] at h1
    set D := AlgebraicGeometry.capDegree ℂ
      (pullback.fst f (𝟙 Z) ≫ i.1.idealSheaf.subscheme ↘ Spec (.of ℂ))
      (fun _ : Fin 1 => (Scheme.Modules.pullback (pullback.fst f (𝟙 Z))).obj H)
    set G := MMP.Chow.divisorGysin f hreg 1
    change ((D (G α) : ℤ) : ℚ) = 0 at h1
    rw [← h1, hαdef, map_sum G, map_sum D, Int.cast_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_sum G, map_sum D, Int.cast_sum]
    refine Finset.sum_congr rfl fun P _ => ?_
    rw [map_zsmul G, map_zsmul D, smul_eq_mul, Int.cast_mul]
  have h2 := h0'
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at h2
  refine Eq.trans ?_ h2
  refine congrArg₂ (HAdd.hAdd : ℚ → ℚ → ℚ) (Finset.sum_congr rfl fun P _ => ?_)
    (Finset.sum_congr rfl fun j hj => ?_)
  · rw [capDegree_divisorGysin_piClass_self hB hdim hvar hsm ε hε π hπ i hreg H P]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun P _ => ?_
    rw [capDegree_divisorGysin_piClass_ne hB hdim hvar hsm ε hε π hπ i j
      (Finset.ne_of_mem_erase hj) hreg H P
      (fun _ : Fin 1 => (Scheme.Modules.pullback (pullback.fst f (𝟙 Z))).obj H)
      (fun _ => ⟨Iso.refl _⟩), Finset.mul_sum]

end Key

/-! ### The ambient class of a homologically trivial family -/

section AmbientVanishing

variable {Z : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [IsComplexScheme Z] {F : MMP.Mori.Divisor Z}

/-- **The integral multiple `n₀ y` of a homologically trivial family is homologically trivial**:
if `∑ⱼ (ιⱼ)_* [yⱼ] = 0` and `cⱼ = n₀ yⱼ`, then `∑ⱼ ∑_P cⱼ(P) (ιⱼ)_*[P] = 0`. -/
private theorem sum_smul_componentHomologyMap_eq_zero
    (c : ∀ j : F.support, MMP.Mori.PrimeDivisor j.1.idealSheaf.subscheme →₀ ℤ)
    (y : ∀ j : F.support, MMP.Mori.QDivisor j.1.idealSheaf.subscheme) (n₀ : ℕ)
    (hc : ∀ j, (c j).mapRange (Int.cast : ℤ → ℚ) Int.cast_zero = (n₀ : ℚ) • y j)
    (hy : ∑ j : F.support, componentHomologyMap j.1 4
      (MMP.Chow.divisorClass j.1.idealSheaf.subscheme (y j)) = 0) :
    ∑ j : F.support, ∑ P ∈ (c j).support, (c j P : ℚ) • componentHomologyMap j.1 4
      (MMP.Chow.divisorClass j.1.idealSheaf.subscheme (Finsupp.single P 1)) = 0 := by
  classical
  have hj : ∀ j : F.support, ∑ P ∈ (c j).support, (c j P : ℚ) • componentHomologyMap j.1 4
      (MMP.Chow.divisorClass j.1.idealSheaf.subscheme (Finsupp.single P 1)) =
        (n₀ : ℚ) • componentHomologyMap j.1 4
          (MMP.Chow.divisorClass j.1.idealSheaf.subscheme (y j)) := by
    intro j
    let X : MMP.Mori.QDivisor j.1.idealSheaf.subscheme →ₗ[ℚ] RationalHomology Z 4 :=
      (componentHomologyMap j.1 4).comp (MMP.Chow.divisorClass j.1.idealSheaf.subscheme)
    change ∑ P ∈ (c j).support, (c j P : ℚ) • X (Finsupp.single P 1) = (n₀ : ℚ) • X (y j)
    have hm : (c j).mapRange (Int.cast : ℤ → ℚ) Int.cast_zero =
        ∑ P ∈ (c j).support, ((c j P : ℤ) : ℚ) • Finsupp.single P (1 : ℚ) := by
      refine Finsupp.ext fun Q => ?_
      simp only [Finsupp.mapRange_apply, Finsupp.coe_finset_sum, Finset.sum_apply,
        Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq']
      split_ifs with h
      · rfl
      · rw [Finsupp.notMem_support_iff.1 h, Int.cast_zero]
    rw [← map_smul, ← hc j, hm, map_sum]
    refine Finset.sum_congr rfl fun P _ => ?_
    rw [map_smul]
  rw [Finset.sum_congr rfl fun j _ => hj j, ← Finset.smul_sum, hy, smul_zero]

end AmbientVanishing

section Scaling

/-- Finitely many rational divisors become integral after multiplication by one `n₀ ≠ 0`. -/
public theorem exists_nat_smul_eq_mapRange {ι : Type*} [Fintype ι] {α : ι → Type*}
    (y : ∀ j, α j →₀ ℚ) :
    ∃ n₀ : ℕ, n₀ ≠ 0 ∧ ∃ c : ∀ j, α j →₀ ℤ,
      ∀ j, (c j).mapRange (Int.cast : ℤ → ℚ) Int.cast_zero = (n₀ : ℚ) • y j := by
  classical
  refine ⟨∏ j, ∏ P ∈ (y j).support, (y j P).den, ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.2 fun j _ => Finset.prod_ne_zero_iff.2 fun P _ =>
      (y j P).den_nz
  · set n₀ := ∏ j, ∏ P ∈ (y j).support, (y j P).den
    have hint : ∀ j P, ∃ z : ℤ, (z : ℚ) = (n₀ : ℚ) * y j P := by
      intro j P
      by_cases hP : P ∈ (y j).support
      · obtain ⟨k, hk⟩ : (y j P).den ∣ n₀ :=
          (Finset.dvd_prod_of_mem (fun P => (y j P).den) hP).trans
            (Finset.dvd_prod_of_mem (fun j => ∏ P ∈ (y j).support, (y j P).den) (Finset.mem_univ j))
        refine ⟨k * (y j P).num, ?_⟩
        rw [hk, Nat.cast_mul, Int.cast_mul, Int.cast_natCast, ← Rat.mul_den_eq_num]
        ring
      · rw [Finsupp.notMem_support_iff.1 hP, mul_zero]
        exact ⟨0, by simp⟩
    choose z hz using hint
    refine ⟨fun j => Finsupp.mapRange (fun q : ℚ => ⌊(n₀ : ℚ) * q⌋) (by simp) (y j), fun j => ?_⟩
    refine Finsupp.ext fun P => ?_
    rw [Finsupp.mapRange_apply, Finsupp.mapRange_apply, Finsupp.smul_apply, smul_eq_mul,
      ← hz j P, Int.floor_intCast]

/-- `∑_{P ∈ supp c} c(P) f(P) = n₀ ∑_P y(P) f(P)` when `c = n₀ y`. -/
public theorem sum_support_mul_eq {α : Type*} (c : α →₀ ℤ) (y : α →₀ ℚ) {n₀ : ℕ}
    (hn₀ : n₀ ≠ 0) (hc : c.mapRange (Int.cast : ℤ → ℚ) Int.cast_zero = (n₀ : ℚ) • y)
    (f : α → ℚ) :
    ∑ P ∈ c.support, (c P : ℚ) * f P = n₀ * Finsupp.linearCombination ℚ f y := by
  have hP : ∀ P, (c P : ℚ) = n₀ * y P := fun P => by
    have := congrArg (fun g : α →₀ ℚ => g P) hc
    simpa using this
  have hsupp : c.support = y.support := by
    ext P
    rw [Finsupp.mem_support_iff, Finsupp.mem_support_iff, ne_eq, ne_eq, ← Int.cast_eq_zero (α := ℚ),
      hP, mul_eq_zero, not_or]
    exact ⟨fun h => h.2, fun h => ⟨by exact_mod_cast hn₀, h⟩⟩
  rw [Finsupp.linearCombination_apply, Finsupp.sum, Finset.mul_sum, hsupp]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [hP, smul_eq_mul]
  ring

/-- The bilinear version: `∑∑ c(P) c'(Q) b(P, Q) = n₀² B(y, y')`. -/
private theorem sum_support_mul_mul_eq {α β : Type*} (c : α →₀ ℤ) (y : α →₀ ℚ) (c' : β →₀ ℤ)
    (y' : β →₀ ℚ) {n₀ : ℕ} (hn₀ : n₀ ≠ 0)
    (hc : c.mapRange (Int.cast : ℤ → ℚ) Int.cast_zero = (n₀ : ℚ) • y)
    (hc' : c'.mapRange (Int.cast : ℤ → ℚ) Int.cast_zero = (n₀ : ℚ) • y') (b : α → β → ℚ) :
    ∑ P ∈ c.support, (c P : ℚ) * ∑ Q ∈ c'.support, (c' Q : ℚ) * b P Q =
      n₀ * n₀ * bilin b y y' := by
  have e : bilin b y y' =
      Finsupp.linearCombination ℚ (fun P => Finsupp.linearCombination ℚ (b P) y') y := by
    simp only [bilin, Finsupp.linearCombination_apply, Finsupp.sum, LinearMap.sum_apply,
      Finset.sum_apply, LinearMap.smul_apply]
  simp_rw [sum_support_mul_eq c' y' hn₀ hc']
  have e2 : ∑ P ∈ c.support, (c P : ℚ) * (n₀ * Finsupp.linearCombination ℚ (b P) y') =
      n₀ * ∑ P ∈ c.support, (c P : ℚ) * Finsupp.linearCombination ℚ (b P) y' := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun P _ => by ring
  rw [e2, sum_support_mul_eq c y hn₀ hc, e]
  ring

/-- A sum over a subtype is the sum of the dependent indicator. -/
private theorem sum_subtype_eq_sum_dite {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p]
    (g : {a // p a} → ℚ) :
    ∑ a : {a // p a}, g a = ∑ a, if h : p a then g ⟨a, h⟩ else 0 := by
  rw [← Fintype.sum_subtype_add_sum_subtype p]
  have h1 : ∀ a : {a // p a}, (if h : p a.1 then g ⟨a.1, h⟩ else 0) = g a := fun a => by
    rw [dif_pos a.2]
  have h2 : ∀ a : {a // ¬ p a}, (if h : p a.1 then g ⟨a.1, h⟩ else 0) = 0 := fun a => by
    rw [dif_neg a.2]
  rw [Finset.sum_congr rfl fun a _ => h1 a, Finset.sum_congr rfl fun a _ => h2 a,
    Finset.sum_const_zero, add_zero]

end Scaling

section Regroup

variable {Z : Scheme.{0}} {F : MMP.Mori.Divisor Z} [Fintype (DoubleSurface F)]

open Classical in
/-- `∑_{j ≠ i} ∑_{σ : (Eⱼ, Eᵢ)} f j σ = ∑_{σ, snd σ = i} f (fst σ) σ`. -/
private theorem sum_erase_sum_subtype_eq (i : F.support)
    (f : ∀ (j : F.support) (σ : DoubleSurface F), σ.fst = j.1 → σ.snd = i.1 → ℚ) :
    ∑ j ∈ Finset.univ.erase i, ∑ σ : {σ : DoubleSurface F // σ.fst = j.1 ∧ σ.snd = i.1},
        f j σ.1 σ.2.1 σ.2.2 =
      ∑ σ : DoubleSurface F, if h : σ.snd = i.1 then f (fstS F σ) σ rfl h else 0 := by
  simp_rw [sum_subtype_eq_sum_dite (fun σ : DoubleSurface F => σ.fst = _ ∧ σ.snd = i.1)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  by_cases hs : σ.snd = i.1
  · rw [dif_pos hs]
    have hfi : fstS F σ ≠ i := fun h => σ.fst_ne_snd (by rw [hs, ← h])
    rw [Finset.sum_eq_single_of_mem (fstS F σ) (Finset.mem_erase.2 ⟨hfi, Finset.mem_univ _⟩)]
    · rw [dif_pos ⟨rfl, hs⟩]
    · intro j _ hj
      rw [dif_neg]
      rintro ⟨h1, -⟩
      exact hj (Subtype.ext h1.symm)
  · rw [dif_neg hs]
    exact Finset.sum_eq_zero fun j _ => dif_neg fun h => hs h.2

end Regroup

section Identities

variable {Z : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [IsComplexScheme Z]
  [IsProper (Z ↘ Spec (.of ℂ))] [IsIntegral Z] {F : MMP.Mori.Divisor Z}
  (hB : F.IsSNC (Z ↘ Spec (.of ℂ))) (hdim : topologicalKrullDim Z = 4)
  [Fintype (DoubleSurface F)]
  (hvar : MMP.Mori.IsVariety ℂ (Z ↘ Spec (.of ℂ)))
  (hsm : MMP.Mori.IsSmoothScheme (Z ↘ Spec (.of ℂ)))
  (ε : F.support → Z.CartierDivisor)
  (hε : ∀ i, MMP.Intersection.IsWeilDivisorOfCartier (ε i) (Finsupp.single i.1 1))
  (π : ∀ i : F.support, MMP.Mori.PrimeDivisor i.1.idealSheaf.subscheme →
    i.1.idealSheaf.subscheme.CartierDivisor)
  (hπ : ∀ i P, MMP.Intersection.IsWeilDivisorOfCartier (π i P) (Finsupp.single P 1))

open Classical in
/-- Regrouping the double-surface terms of the weighted self-intersection by the double
surface. -/
public theorem sum_sum_doubleSurface_num2_eq
    (c : ∀ i : F.support, MMP.Mori.PrimeDivisor i.1.idealSheaf.subscheme →₀ ℤ)
    (y : ∀ j : F.support, MMP.Mori.QDivisor j.1.idealSheaf.subscheme) {n₀ : ℕ} (hn₀ : n₀ ≠ 0)
    (hc : ∀ j, (c j).mapRange (Int.cast : ℤ → ℚ) Int.cast_zero = (n₀ : ℚ) • y j) :
    ∑ i : F.support, ∑ Q ∈ (c i).support, (c i Q : ℚ) *
        ∑ σ : DoubleSurface F, (if h : σ.snd = i.1 then
          ∑ P ∈ (c (fstS F σ)).support, (c (fstS F σ) P : ℚ) *
            num2 (dsIdeal σ).subscheme ((dsIdeal σ).subschemeι ≫ Z ↘ Spec (.of ℂ))
              ((Scheme.Modules.pullback (tιOf σ h)).obj (MMP.CartierDivisor.sheaf (π i Q)))
              ((Scheme.Modules.pullback (sι σ)).obj (MMP.CartierDivisor.sheaf (π (fstS F σ) P)))
          else 0) =
        ∑ σ : DoubleSurface F, (n₀ : ℚ) * n₀ * bilin (bC π σ) (y (fstS F σ)) (y (sndS F σ)) := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hpull : ∀ i : F.support, ∑ Q ∈ (c i).support, (c i Q : ℚ) *
      (if h : σ.snd = i.1 then
        ∑ P ∈ (c (fstS F σ)).support, (c (fstS F σ) P : ℚ) *
          num2 (dsIdeal σ).subscheme ((dsIdeal σ).subschemeι ≫ Z ↘ Spec (.of ℂ))
            ((Scheme.Modules.pullback (tιOf σ h)).obj (MMP.CartierDivisor.sheaf (π i Q)))
            ((Scheme.Modules.pullback (sι σ)).obj (MMP.CartierDivisor.sheaf (π (fstS F σ) P)))
        else 0) =
      if h : σ.snd = i.1 then ∑ Q ∈ (c i).support, (c i Q : ℚ) *
        ∑ P ∈ (c (fstS F σ)).support, (c (fstS F σ) P : ℚ) *
          num2 (dsIdeal σ).subscheme ((dsIdeal σ).subschemeι ≫ Z ↘ Spec (.of ℂ))
            ((Scheme.Modules.pullback (tιOf σ h)).obj (MMP.CartierDivisor.sheaf (π i Q)))
            ((Scheme.Modules.pullback (sι σ)).obj (MMP.CartierDivisor.sheaf (π (fstS F σ) P)))
      else 0 := by
    intro i
    by_cases hs : σ.snd = i.1
    · simp only [dif_pos hs]
    · simp only [dif_neg hs, mul_zero, Finset.sum_const_zero]
  rw [Finset.sum_congr rfl fun i _ => hpull i,
    Finset.sum_eq_single_of_mem (sndS F σ) (Finset.mem_univ _)
      (fun i _ hi => dif_neg fun h => hi (Subtype.ext h).symm),
    dif_pos rfl, sum_support_mul_mul_eq _ _ _ _ hn₀ (hc _) (hc _)]
  refine congrArg (fun t => (n₀ : ℚ) * n₀ * t) ?_
  rw [bilin_apply, bilin_apply, Finset.sum_comm]
  refine Finset.sum_congr rfl fun P _ => Finset.sum_congr rfl fun Q _ => ?_
  rw [mul_comm (y (sndS F σ) Q)]
  refine congrArg (fun t => y (fstS F σ) P * y (sndS F σ) Q * t) ?_
  unfold bC
  exact num2_comm _ _ _

include hB hdim hvar hsm hε hπ in
/-- **The linear intersection equation of a homologically trivial family** (the ambient
intersection with `A · Eᵢ`). -/
public theorem kernel_identities_lin [DecidableEq F.support]
    (hZp : IsProjectiveMorphism (Z ↘ Spec (.of ℂ))) (Hc : Z.CartierDivisor)
    (y : ∀ j : F.support, MMP.Mori.QDivisor j.1.idealSheaf.subscheme)
    (hy : ∑ j : F.support, componentHomologyMap j.1 4
      (MMP.Chow.divisorClass j.1.idealSheaf.subscheme (y j)) = 0) :
    ∀ i, Finsupp.linearCombination ℚ (bGA π ε Hc i) (y i) +
    ∑ σ : DoubleSurface F, (if sndS F σ = i then
      Finsupp.linearCombination ℚ (bUA π Hc σ) (y (fstS F σ)) else 0) = 0 := by
  classical
  obtain ⟨n₀, hn₀, c, hc⟩ := exists_nat_smul_eq_mapRange y
  have hn₀' : (n₀ : ℚ) ≠ 0 := by exact_mod_cast hn₀
  have hx := sum_smul_componentHomologyMap_eq_zero c y n₀ hc hy
  have K := key_identity hB hdim hvar hsm ε hε π hπ hZp c hx
  intro i
  have h := K i ((Scheme.Modules.pullback i.1.idealSheaf.subschemeι).obj
    (MMP.CartierDivisor.sheaf Hc))
  have hreg := sum_erase_sum_subtype_eq i (fun j σ h₁ h₂ => ∑ P ∈ (c j).support, (c j P : ℚ) *
    num2 (dsIdeal σ).subscheme ((dsIdeal σ).subschemeι ≫ Z ↘ Spec (.of ℂ))
      ((Scheme.Modules.pullback (tιOf σ h₂)).obj
        ((Scheme.Modules.pullback i.1.idealSheaf.subschemeι).obj (MMP.CartierDivisor.sheaf Hc)))
      ((Scheme.Modules.pullback (sιOf σ h₁)).obj (MMP.CartierDivisor.sheaf (π j P))))
  beta_reduce at hreg
  rw [hreg, sum_support_mul_eq (c i) (y i) hn₀ (hc i)] at h
  refine (mul_eq_zero.1 (?_ : (n₀ : ℚ) * _ = 0)).resolve_left hn₀'
  rw [mul_add, Finset.mul_sum]
  refine Eq.trans (congrArg₂ (· + ·) ?_ (Finset.sum_congr rfl fun σ _ => ?_)) h
  · refine congrArg (fun b => (n₀ : ℚ) * Finsupp.linearCombination ℚ b (y i))
      (funext fun P => ?_)
    unfold bGA
    rw [num3_comm12]
  · by_cases hs : σ.snd = i.1
    · rw [if_pos (Subtype.ext hs), dif_pos hs, sum_support_mul_eq _ _ hn₀ (hc _)]
      refine congrArg (fun b => (n₀ : ℚ) * Finsupp.linearCombination ℚ b (y (fstS F σ)))
        (funext fun P => ?_)
      unfold bUA
      rw [num2_comm]
      exact num2_congr _ _ _ _ _
        ⟨((Scheme.Modules.pullbackComp _ _).app _ ≪≫
          (Scheme.Modules.pullbackCongr (Scheme.IdealSheafData.inclusion_subschemeι _)).app _).symm⟩
        ⟨Iso.refl _⟩
    · rw [if_neg (fun h => hs (congrArg Subtype.val h)), dif_neg hs, mul_zero]

include hB hdim hvar hsm hε hπ in
/-- **The self-intersection equation of a homologically trivial family**. -/
public theorem kernel_identities_bilin [DecidableEq F.support]
    (hZp : IsProjectiveMorphism (Z ↘ Spec (.of ℂ)))
    (y : ∀ j : F.support, MMP.Mori.QDivisor j.1.idealSheaf.subscheme)
    (hy : ∑ j : F.support, componentHomologyMap j.1 4
      (MMP.Chow.divisorClass j.1.idealSheaf.subscheme (y j)) = 0) :
    ∑ i, bilin (bG π ε i) (y i) (y i) +
      ∑ σ : DoubleSurface F, bilin (bC π σ) (y (fstS F σ)) (y (sndS F σ)) = 0 := by
  classical
  obtain ⟨n₀, hn₀, c, hc⟩ := exists_nat_smul_eq_mapRange y
  have hn₀' : (n₀ : ℚ) ≠ 0 := by exact_mod_cast hn₀
  have hx := sum_smul_componentHomologyMap_eq_zero c y n₀ hc hy
  have K := key_identity hB hdim hvar hsm ε hε π hπ hZp c hx
  have hKQ : ∀ (i : F.support) (Q : MMP.Mori.PrimeDivisor i.1.idealSheaf.subscheme),
      ∑ P ∈ (c i).support, (c i P : ℚ) * bG π ε i Q P +
        ∑ σ : DoubleSurface F, (if h : σ.snd = i.1 then
          ∑ P ∈ (c (fstS F σ)).support, (c (fstS F σ) P : ℚ) *
            num2 (dsIdeal σ).subscheme ((dsIdeal σ).subschemeι ≫ Z ↘ Spec (.of ℂ))
              ((Scheme.Modules.pullback (tιOf σ h)).obj (MMP.CartierDivisor.sheaf (π i Q)))
              ((Scheme.Modules.pullback (sι σ)).obj (MMP.CartierDivisor.sheaf (π (fstS F σ) P)))
          else 0) = 0 := by
    intro i Q
    have h := K i (MMP.CartierDivisor.sheaf (π i Q))
    have hreg := sum_erase_sum_subtype_eq i (fun j σ h₁ h₂ => ∑ P ∈ (c j).support,
      (c j P : ℚ) * num2 (dsIdeal σ).subscheme ((dsIdeal σ).subschemeι ≫ Z ↘ Spec (.of ℂ))
        ((Scheme.Modules.pullback (tιOf σ h₂)).obj (MMP.CartierDivisor.sheaf (π i Q)))
        ((Scheme.Modules.pullback (sιOf σ h₁)).obj (MMP.CartierDivisor.sheaf (π j P))))
    beta_reduce at hreg
    rw [hreg] at h
    refine Eq.trans (congrArg₂ (· + ·) (Finset.sum_congr rfl fun P _ => ?_)
      (Finset.sum_congr rfl fun σ _ => ?_)) h
    · rfl
    · by_cases hs : σ.snd = i.1
      · simp only [dif_pos hs]
      · simp only [dif_neg hs]
  have htot : ∑ i : F.support, ∑ Q ∈ (c i).support, (c i Q : ℚ) *
      (∑ P ∈ (c i).support, (c i P : ℚ) * bG π ε i Q P +
        ∑ σ : DoubleSurface F, (if h : σ.snd = i.1 then
          ∑ P ∈ (c (fstS F σ)).support, (c (fstS F σ) P : ℚ) *
            num2 (dsIdeal σ).subscheme ((dsIdeal σ).subschemeι ≫ Z ↘ Spec (.of ℂ))
              ((Scheme.Modules.pullback (tιOf σ h)).obj (MMP.CartierDivisor.sheaf (π i Q)))
              ((Scheme.Modules.pullback (sι σ)).obj (MMP.CartierDivisor.sheaf (π (fstS F σ) P)))
          else 0)) = 0 :=
    Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun Q _ => by rw [hKQ i Q, mul_zero]
  simp only [mul_add, Finset.sum_add_distrib] at htot
  rw [Finset.sum_congr rfl fun i _ =>
    sum_support_mul_mul_eq (c i) (y i) (c i) (y i) hn₀ (hc i) (hc i) (bG π ε i)] at htot
  rw [sum_sum_doubleSurface_num2_eq π c y hn₀ hc, ← Finset.mul_sum, ← Finset.mul_sum,
    ← mul_add] at htot
  exact (mul_eq_zero.1 htot).resolve_left (mul_ne_zero hn₀' hn₀')

include hB hdim hvar hsm hε hπ in
/-- **The two intersection equations of a homologically trivial family** (the ambient
intersection with `A · Eᵢ`, and the self-intersection). -/
public theorem kernel_identities [DecidableEq F.support]
    (hZp : IsProjectiveMorphism (Z ↘ Spec (.of ℂ))) (Hc : Z.CartierDivisor)
    (y : ∀ j : F.support, MMP.Mori.QDivisor j.1.idealSheaf.subscheme)
    (hy : ∑ j : F.support, componentHomologyMap j.1 4
      (MMP.Chow.divisorClass j.1.idealSheaf.subscheme (y j)) = 0) :
    (∀ i, Finsupp.linearCombination ℚ (bGA π ε Hc i) (y i) +
        ∑ σ : DoubleSurface F, (if sndS F σ = i then
          Finsupp.linearCombination ℚ (bUA π Hc σ) (y (fstS F σ)) else 0) = 0) ∧
      ∑ i, bilin (bG π ε i) (y i) (y i) +
        ∑ σ : DoubleSurface F, bilin (bC π σ) (y (fstS F σ)) (y (sndS F σ)) = 0 :=
  ⟨kernel_identities_lin hB hdim hvar hsm ε hε π hπ hZp Hc y hy,
    kernel_identities_bilin hB hdim hvar hsm ε hε π hπ hZp y hy⟩

end Identities

/-- A divisor supported on `F.support` with positive coefficients there is the sum of its
coefficients times the components. -/
public theorem neg_add_sum_toNat_smul_single_eq_zero {Z : Scheme.{0}} {F D : MMP.Mori.Divisor Z}
    (hDpos : ∀ P ∈ F.support, 0 < D.coeff P) (hDzero : ∀ P ∉ F.support, D.coeff P = 0) :
    -D + ∑ l : F.support,
      (D.coeff l.1).toNat • (Finsupp.single l.1 1 : MMP.Mori.Divisor Z) = 0 := by
  classical
  refine Finsupp.ext fun P => ?_
  rw [Finsupp.add_apply, Finsupp.neg_apply, Finsupp.finset_sum_apply, Finsupp.coe_zero,
    Pi.zero_apply]
  by_cases hP : P ∈ F.support
  · rw [Finset.sum_eq_single (⟨P, hP⟩ : F.support) (fun l _ hl => by
      rw [Finsupp.smul_apply, Finsupp.single_apply, if_neg (fun h => hl (Subtype.ext h)),
        smul_zero]) (fun h => absurd (Finset.mem_univ _) h)]
    rw [Finsupp.smul_apply, Finsupp.single_eq_same, nsmul_eq_mul, mul_one,
      Int.toNat_of_nonneg (hDpos P hP).le]
    exact neg_add_cancel _
  · rw [Finset.sum_eq_zero fun l _ => by
      rw [Finsupp.smul_apply, Finsupp.single_apply,
        if_neg (fun (h : l.1 = P) => hP (h ▸ l.2)), smul_zero]]
    change -D.coeff P + 0 = 0
    rw [hDzero P hP, neg_zero, add_zero]

/-- **The forward inclusion `K(r) ⊆ B(r)`.** -/
private theorem forward
    {Z Y : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [IsComplexScheme Z] [CompactSpace Z]
    [IsLocallyNoetherian Z] [IsNormal Z]
    (sY : Y ⟶ Spec (.of ℂ)) (r : Z ⟶ Y) (F D : MMP.Mori.Divisor Z)
    (hcomp : r ≫ sY = Z ↘ Spec (.of ℂ))
    (hres : MMP.Intersection.IsResolution sY r)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ (Z ↘ Spec (.of ℂ)))
    (hdim : topologicalKrullDim Z = 4)
    (hFred : MMP.Intersection.IsReducedEffective F)
    (hFsnc : MMP.Mori.DivisorWithCoeffs.IsSNC (r ≫ sY) F)
    (hfin : (r.base '' (F.supp : Set Z)).Finite)
    (hclosed : ∀ y ∈ r.base '' (F.supp : Set Z), IsClosed ({y} : Set Y))
    (hDpos : ∀ P ∈ F.support, 0 < D.coeff P)
    (hDzero : ∀ P ∉ F.support, D.coeff P = 0)
    (hA : ∃ h : (-D).IsCartier, (-D).IsRelativelyAmple r h)
    (L : ∀ E : F.support, MMP.Mori.QDivisor E.1.idealSheaf.subscheme)
    (hL : ∑ E : F.support, componentHomologyMap E.1 4
      (MMP.Chow.divisorClass E.1.idealSheaf.subscheme (L E)) = 0) :
    ∃ a ∈ orientedSurfaceCoefficients F, ∀ E : F.support,
      MMP.Chow.divisorClass E.1.idealSheaf.subscheme (L E) =
        MMP.Chow.divisorClass E.1.idealSheaf.subscheme (surfaceCoefficientDivisor a E.1) := by
  classical
  have hZv := (MMP.Mori.isProjectiveVariety_iff _ _).1 hZ
  haveI : IsProjective (Z ↘ Spec (.of ℂ)) := hZv.2.isProjective
  haveI hvarZ : MMP.Mori.IsVariety ℂ (Z ↘ Spec (.of ℂ)) := hZv.1
  have hsmZ : MMP.Mori.IsSmoothScheme (Z ↘ Spec (.of ℂ)) := hcomp ▸ hres.2.2.1
  have hB : F.IsSNC (Z ↘ Spec (.of ℂ)) := hcomp ▸ hFsnc
  haveI : IsIntegral Z := hZv.1.toIsIntegral
  haveI : TopologicalSpace.NoetherianSpace Z := noetherianSpace_of_isComplexScheme
  haveI : Fintype (DoubleSurface F) :=
    @Fintype.ofFinite _ (MMP.Fourfold.DoubleSurface.finite (B := F))
  choose ε hε using fun i : F.support =>
    exists_isWeilDivisorOfCartier hsmZ (Finsupp.single i.1 1)
  have hXvar : ∀ i : F.support,
      MMP.Mori.IsVariety ℂ (i.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) := fun i => by
    haveI := i.1.integral
    exact (⟨⟩ : AlgebraicGeometry.IsVariety ℂ (i.1.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ)))
  choose π hπ using fun (i : F.support) (P : MMP.Mori.PrimeDivisor i.1.idealSheaf.subscheme) =>
    @exists_isWeilDivisorOfCartier _ _ (hXvar i) (hB.1 i.1 i.2) (Finsupp.single P 1)
  set n : F.support → ℕ := fun i => (D.coeff i.1).toNat with hn_def
  set m : F.support → ℚ := fun i => (n i : ℚ) with hm_def
  have hm : ∀ i, 0 < m i := fun i => by
    simp only [hm_def, hn_def]
    exact_mod_cast Int.lt_toNat.2 (hDpos i.1 i.2)
  obtain ⟨Hc, hHcW⟩ := exists_isWeilDivisorOfCartier hsmZ (-D)
  have hHc : Nonempty (MMP.CartierDivisor.sheaf (Hc + ∑ l : F.support, n l • ε l) ≅
      SheafOfModules.unit Z.ringCatSheaf) := by
    have hW := isWeilDivisorOfCartier_add hHcW (isWeilDivisorOfCartier_sum Finset.univ
      fun l _ => isWeilDivisorOfCartier_nsmul (hε l) (n l))
    have h0 : -D + ∑ l : F.support, n l • (Finsupp.single l.1 1 : MMP.Mori.Divisor Z) = 0 :=
      neg_add_sum_toNat_smul_single_eq_zero hDpos hDzero
    rw [h0] at hW
    obtain ⟨e⟩ := MMP.Intersection.IsWeilDivisorOfCartier.nonempty_sheaf_iso_divisorialSheaf hW
    exact ⟨e ≪≫ MMP.Mori.Divisor.divisorialSheafZeroIso⟩
  let Zl : (DoubleSurface F → ℚ) →ₗ[ℚ]
      (∀ i : F.support, MMP.Mori.QDivisor i.1.idealSheaf.subscheme) :=
    LinearMap.pi fun i => surfaceCoefficientDivisorLinearMap F i.1
  have hZl : ∀ a i, Zl a i = surfaceCoefficientDivisor a i.1 := fun _ _ => rfl
  let ρv : ∀ σ : DoubleSurface F, MMP.Mori.QDivisor σ.fst.idealSheaf.subscheme :=
    fun σ => Finsupp.single (rho hB σ) 1
  have hZlin : ∀ (f : ∀ i : F.support, MMP.Mori.QDivisor i.1.idealSheaf.subscheme →ₗ[ℚ] ℚ)
      (a : DoubleSurface F → ℚ),
      ∑ i, f i (Zl a i) = ∑ σ : DoubleSurface F, a σ * f (fstS F σ) (ρv σ) :=
    fun f a => sum_apply_surfaceCoefficientDivisor hB f a
  have hRA : ∀ (σ : DoubleSurface F) x,
      Finsupp.linearCombination ℚ (bUA π Hc σ) x = bilin (bB π Hc (fstS F σ)) x (ρv σ) := by
    intro σ x
    rw [bilin_single_right]
    exact congrArg (fun b => Finsupp.linearCombination ℚ b x)
      (funext fun P => bUA_eq_bB hB hdim π hπ Hc σ P)
  have hAHc : MMP.Mori.IsRelativelyAmple r (MMP.CartierDivisor.sheaf Hc) := by
    obtain ⟨hc, hrel⟩ := hA
    haveI := hc.isInvertibleModule_divisorialSheaf
    obtain ⟨e⟩ := MMP.Intersection.IsWeilDivisorOfCartier.nonempty_sheaf_iso_divisorialSheaf hHcW
    exact MMP.Mori.IsRelativelyAmple.of_iso e.symm hrel
  have hAmpX : ∀ i : F.support, Stacks.Ample.IsAmple i.1.idealSheaf.subscheme
      ((Scheme.Modules.pullback i.1.idealSheaf.subschemeι).obj (MMP.CartierDivisor.sheaf Hc)) :=
    fun i => isAmple_pullback_of_range_subset r F hfin hclosed _ hAHc i.1 i.2
      i.1.idealSheaf.subschemeι (by rw [i.1.idealSheaf.range_subschemeι])
  have hAmpS : ∀ σ : DoubleSurface F, Stacks.Ample.IsAmple (dsIdeal σ).subscheme
      ((Scheme.Modules.pullback (dsIdeal σ).subschemeι).obj (MMP.CartierDivisor.sheaf Hc)) :=
    fun σ => isAmple_pullback_of_range_subset r F hfin hclosed _ hAHc σ.fst σ.fst_mem
      (dsIdeal σ).subschemeι (by
        rw [← sι_comp σ, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
        refine (Set.image_subset_range _ _).trans ?_
        rw [σ.fst.idealSheaf.range_subschemeι])
  have hBred : ∀ E ∈ F.support, F E = 1 := fun E hE =>
    (hFred E).resolve_left (Finsupp.mem_support_iff.1 hE)
  have hWI : ∀ a ∈ orientedSurfaceCoefficients F,
      ∑ i, bilin (bB π Hc i) (Zl a i) (Zl a i) / m i = 0 → a = 0 :=
    fun a ha h0 => weighted_negdef hB hdim π hπ hvarZ hsmZ hZv.2 hBred ε hε Hc n
      (fun i => Int.lt_toNat.2 (hDpos i.1 i.2)) hHc hAmpX a ha h0
  have hGA : ∀ (x : ∀ i : F.support, MMP.Mori.QDivisor i.1.idealSheaf.subscheme) i,
      -m i * Finsupp.linearCombination ℚ (bGA π ε Hc i) (x i) =
        Finsupp.linearCombination ℚ (bLam π Hc i) (x i) +
      ∑ σ : DoubleSurface F, if fstS F σ = i then
        m (sndS F σ) * Finsupp.linearCombination ℚ (bUA π Hc σ) (x (fstS F σ)) else 0 :=
    fun x i => lin_bGA_eq hB hdim π hvarZ hsmZ ε hε Hc n hHc x i
  have hG : ∀ (x : ∀ i : F.support, MMP.Mori.QDivisor i.1.idealSheaf.subscheme) i,
      -m i * bilin (bG π ε i) (x i) (x i) = bilin (bB π Hc i) (x i) (x i) +
      ∑ σ : DoubleSurface F, if fstS F σ = i then
        m (sndS F σ) * bilin (bU π σ) (x (fstS F σ)) (x (fstS F σ)) else 0 :=
    fun x i => bilin_bG_eq hB hdim π hvarZ hsmZ ε hε Hc n hHc x i
  have hSI : ∀ (σ : DoubleSurface F) x y,
      Finsupp.linearCombination ℚ (bUA π Hc σ) x =
        Finsupp.linearCombination ℚ (bUA π Hc σ.swap) y →
      bilin (bU π σ) x x - 2 * bilin (bC π σ) x y + bilin (bU π σ.swap) y y ≤ 0 :=
    fun σ x y hxy => surface_index hB hdim π hZv.2 Hc σ (hAmpS σ) x y hxy
  have hTI : ∀ i x, Finsupp.linearCombination ℚ (bLam π Hc i) x = 0 →
      bilin (bB π Hc i) x x ≤ 0 ∧
        (bilin (bB π Hc i) x x = 0 → MMP.Chow.divisorClass i.1.idealSheaf.subscheme x = 0) :=
    fun i x hx => threefold_index hB hdim π hπ hZv.2 Hc i (hAmpX i) x hx
  have hKB : ∀ a ∈ orientedSurfaceCoefficients F,
      (∀ i, Finsupp.linearCombination ℚ (bGA π ε Hc i) ((L - Zl a) i) +
        ∑ σ : DoubleSurface F, (if sndS F σ = i then
          Finsupp.linearCombination ℚ (bUA π Hc σ) ((L - Zl a) (fstS F σ)) else 0) = 0) ∧
      ∑ i, bilin (bG π ε i) ((L - Zl a) i) ((L - Zl a) i) +
        ∑ σ : DoubleSurface F,
          bilin (bC π σ) ((L - Zl a) (fstS F σ)) ((L - Zl a) (sndS F σ)) = 0 := by
    intro a ha
    refine kernel_identities hB hdim hvarZ hsmZ ε hε π hπ hZv.2 Hc (L - Zl a) ?_
    simp only [Pi.sub_apply, map_sub, Finset.sum_sub_distrib, hZl]
    rw [hL, ConductorBlowup.sum_componentHomologyMap_divisorClass_eq_zero_of_topologicalKrullDim_eq_four
      hdim F a ha, sub_zero]
  obtain ⟨a, ha, hQ⟩ := exists_of_numerical F m hm Zl ρv
    (fun i => bilin (bB π Hc i)) (fun i => bilin (bG π ε i))
    (fun i => Finsupp.linearCombination ℚ (bLam π Hc i))
    (fun i => Finsupp.linearCombination ℚ (bGA π ε Hc i))
    (fun σ => bilin (bU π σ)) (fun σ => bilin (bC π σ))
    (fun σ => Finsupp.linearCombination ℚ (bUA π Hc σ))
    (fun i x => MMP.Chow.divisorClass i.1.idealSheaf.subscheme x = 0)
    hZlin hRA hWI hGA hG hSI hTI L hKB
  refine ⟨a, ha, fun E => ?_⟩
  have h := hQ E
  simp only [map_smul, map_sub, hZl] at h
  have hmE : (m E)⁻¹ ≠ 0 := inv_ne_zero (hm E).ne'
  exact sub_eq_zero.1 ((smul_eq_zero.1 h).resolve_left hmE)

private theorem solution :
    ∀ {Z Y : Scheme.{0}} [inst : Z.Over (Spec (.of ℂ))] [inst_1 : IsComplexScheme Z]
      [inst_2 : CompactSpace Z] [inst_3 : IsLocallyNoetherian Z] [inst_4 : IsNormal Z]
      (sY : Y ⟶ Spec (.of ℂ)) (r : Z ⟶ Y) (F D : MMP.Mori.Divisor Z),
      r ≫ sY = Z ↘ Spec (.of ℂ) →
      MMP.Intersection.IsResolution sY r →
      MMP.Mori.IsProjectiveVariety ℂ (Z ↘ Spec (.of ℂ)) →
      topologicalKrullDim Z = 4 →
      MMP.Intersection.IsReducedEffective F →
      MMP.Mori.DivisorWithCoeffs.IsSNC (r ≫ sY) F →
      (F.supp : Set Z) = MMP.Mori.exceptionalSet r →
      (r.base '' (F.supp : Set Z)).Finite →
      (∀ y ∈ r.base '' (F.supp : Set Z), IsClosed ({y} : Set Y)) →
      (∀ P ∈ F.support, 0 < D.coeff P) →
      (∀ P ∉ F.support, D.coeff P = 0) →
      (∃ h : (-D).IsCartier, (-D).IsRelativelyAmple r h) →
      algebraicKernel F = orientedSurfaceClasses F := by
  intro Z Y _ _ _ _ _ sY r F D hcomp hres hZ hdim hFred hFsnc _hFex hfin hclosed hDpos hDzero hA
  have : IsIntegral Z := ((MMP.Mori.isProjectiveVariety_iff _ _).1 hZ).1.toIsIntegral
  apply le_antisymm
  · intro x hx
    obtain ⟨hC, hsum⟩ := (mem_exceptionalKernel F).1 hx
    choose L hL using fun E => (hC E : x E ∈ divisorClasses _)
    obtain ⟨a, ha, haE⟩ := forward sY r F D hcomp hres hZ hdim hFred hFsnc hfin hclosed hDpos
      hDzero hA L (by simpa [hL] using hsum)
    exact (mem_orientedSurfaceClasses F).2 ⟨a, ha, fun E => (hL E).symm.trans (haE E)⟩
  · intro x hx
    obtain ⟨a, ha, hxa⟩ := (mem_orientedSurfaceClasses F).1 hx
    refine (mem_exceptionalKernel F).2 ⟨fun E => hxa E ▸ LinearMap.mem_range_self _ _, ?_⟩
    simp_rw [hxa]
    exact ConductorBlowup.sum_componentHomologyMap_divisorClass_eq_zero_of_topologicalKrullDim_eq_four
      hdim F a ha

end MMP.Fold06.ThmMmpConductorIsolatedPointAlgebraicKernel

open AlgebraicGeometry CategoryTheory MMP

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori

/-- **The algebraic middle-form kernel for an isolated exceptional fibre.** Let `Z` be a smooth
projective complex fourfold and `r : Z ⟶ Y` a projective birational morphism whose exceptional
divisor `F = ∑ᵢ Fᵢ` is a reduced snc divisor whose image in `Y` is a finite set of closed points.
Let `D = ∑ᵢ mᵢ Fᵢ` with all `mᵢ > 0` and `-D` relatively ample over `Y`. Then the kernel `K(r)` of
`⨁ᵢ Cᵢ → H_4(Z, ℚ)`, `Cᵢ` the classes of `ℚ`-divisors on `Fᵢ`, equals the space
`B(r) = {([Zᵢ(a)])ᵢ}` of classes of oriented double-surface systems: whenever
`∑ᵢ (ιᵢ)_* [Lᵢ] = 0` there is an oriented `a` with `[Lᵢ] = [Zᵢ(a)]` in `H_4(Fᵢ, ℚ)` for all `i`, and
conversely `∑ᵢ (ιᵢ)_* [Zᵢ(a)] = 0` for every oriented `a`. -/
@[mmp "thm_mmp_conductor_isolated_point_algebraic_kernel"]
public theorem algebraicKernel_eq_orientedSurfaceClasses_of_finite_image
    {Z Y : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [IsComplexScheme Z] [CompactSpace Z]
    [IsLocallyNoetherian Z] [IsNormal Z]
    (sY : Y ⟶ Spec (.of ℂ)) (r : Z ⟶ Y) (F D : Divisor Z)
    (hcomp : r ≫ sY = Z ↘ Spec (.of ℂ))
    (hres : MMP.Intersection.IsResolution sY r)
    (hZ : Mori.IsProjectiveVariety ℂ (Z ↘ Spec (.of ℂ)))
    (hdim : topologicalKrullDim Z = 4)
    (hFred : MMP.Intersection.IsReducedEffective F)
    (hFsnc : DivisorWithCoeffs.IsSNC (r ≫ sY) F)
    (hFex : (F.supp : Set Z) = Mori.exceptionalSet r)
    (hfin : (r.base '' (F.supp : Set Z)).Finite)
    (hclosed : ∀ y ∈ r.base '' (F.supp : Set Z), IsClosed ({y} : Set Y))
    (hDpos : ∀ P ∈ F.support, 0 < D.coeff P)
    (hDzero : ∀ P ∉ F.support, D.coeff P = 0)
    (hA : ∃ h : (-D).IsCartier, (-D).IsRelativelyAmple r h) :
    algebraicKernel F = orientedSurfaceClasses F :=
  MMP.Fold06.ThmMmpConductorIsolatedPointAlgebraicKernel.solution sY r F D hcomp hres hZ hdim hFred hFsnc hFex hfin hclosed hDpos hDzero hA

end MMP.Fourfold
