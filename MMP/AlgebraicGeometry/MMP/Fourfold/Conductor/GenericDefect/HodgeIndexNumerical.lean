module

public import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor
public import Mathlib.Algebra.Ring.IsFormallyReal

/-!
# The Hodge index argument for the generic algebraic defect

Let `r : Z ⟶ Y` be a curve-and-point exceptional model with exceptional divisor
`F = ∑ᵢ Fᵢ`, `D = ∑ᵢ mᵢ Fᵢ` with `-D` relatively ample, `H = r^* H_Y` the pull-back of an ample
divisor and `A = N H - D` ample on every component. For a family `(Mᵢ)ᵢ` of divisors on the
components with zero ambient class in `H_4(Z, ℚ)` and zero classes on the general fibres over the
singular curves, the Hodge index theorem on the components and on the double surfaces shows that
`([Mᵢ])ᵢ` is the class tuple of an oriented double-surface system.

This file isolates the numerical part of that argument. The divisor spaces of the components are
abstract `ℚ`-vector spaces `Vᵢ`, the intersection numbers are abstract linear and bilinear forms,
and the geometric inputs (the adjunction identities for `Fᵢ|_{Fᵢ}` with `D = N H - A`, the
identities obtained by intersecting the zero ambient class with `Fᵢ · A` and with itself, the
threefold and surface index theorems, and the weighted surface identity) are hypotheses. The
conclusion is the existence of an oriented system `a`, supported on the double surfaces mapping to
points, with `Mᵢ - Zᵢ(a)` in a given subspace `Kᵢ` (in the application, the divisors of class
zero).

The argument: subtract the orthogonal projection, for the form `P((Mᵢ)ᵢ) = ∑ᵢ Mᵢ² A / mᵢ`, onto the
point-edge systems, which is nondegenerate there; put `Mᵢ = mᵢ δᵢ`. Every `δᵢ² A` is nonpositive by
the threefold index theorems (ordinary on the point components, isotropic with respect to `H` on
the curve components), every `((δᵢ - δⱼ)|_S)²` is nonpositive by the surface index theorems, and
the self-intersection identity of the zero ambient class makes their weighted sum zero. The
equality cases give `δᵢ ∈ Kᵢ` on point components and `δᵢ - cᵢ Hᵢ ∈ Kᵢ` on curve components, and
the identity of the ambient class tested against `∑ᵢ mᵢ cᵢ Fᵢ · A` forces every `cᵢ = 0`.

## Main results

* `MMP.Fourfold.exists_mem_orientedSurfaceCoefficients_orth_of_pointEdges`: the orthogonal
  projection onto the point-edge systems.
* `MMP.Fourfold.exists_mem_orientedSurfaceCoefficients_forall_sub_mem_of_hodgeIndex`: the
  numerical form of the Hodge index argument.
-/

public section

open AlgebraicGeometry

universe u

namespace MMP.Fourfold

open MMP.Mori

variable {Z : Scheme.{u}} {B : Divisor Z}

namespace DoubleSurface

/-- The first component of a double surface, as an element of the support of the divisor. -/
abbrev fstComponent (σ : DoubleSurface B) : B.support := ⟨σ.fst, σ.fst_mem⟩

/-- The second component of a double surface, as an element of the support of the divisor. -/
abbrev sndComponent (σ : DoubleSurface B) : B.support := ⟨σ.snd, σ.snd_mem⟩

/-- The first component of the swapped double surface is the second component. -/
@[simp] theorem swap_fstComponent (σ : DoubleSurface B) :
    σ.swap.fstComponent = σ.sndComponent := rfl

/-- The second component of the swapped double surface is the first component. -/
@[simp] theorem swap_sndComponent (σ : DoubleSurface B) :
    σ.swap.sndComponent = σ.fstComponent := rfl

/-- Summing over the swapped double surfaces is summing over the double surfaces. -/
theorem sum_comp_swap [Fintype (DoubleSurface B)] {M : Type*} [AddCommMonoid M]
    (g : DoubleSurface B → M) : ∑ σ : DoubleSurface B, g σ.swap = ∑ σ, g σ :=
  Fintype.sum_equiv (Function.Involutive.toPerm _ swap_swap) _ _ fun _ => rfl

end DoubleSurface

section Numerical

variable [Fintype (DoubleSurface B)] {V : B.support → Type*} [∀ i, AddCommGroup (V i)]
  [∀ i, Module ℚ (V i)]

/-- **The orthogonal projection onto the point-edge systems.** Let `Zl a = (Zᵢ(a))ᵢ` be the
divisors of the coefficient systems, `ρ_σ` the surface `S` on the first component of `σ`,
`B_i` the forms `x · y · A` and `UA_σ x = x|_S · A|_S = x · S · A`. If the weighted form
`∑ᵢ (Zᵢ(a))² A / mᵢ` vanishes on no nonzero oriented system supported on the point edges, then
every family `L` differs from `Zl a`, for such an `a`, by a family that is orthogonal on the point
edges: `(L - Zl a)ᵢ|_S · A / mᵢ = (L - Zl a)ⱼ|_S · A / mⱼ`. -/
theorem exists_mem_orientedSurfaceCoefficients_orth_of_pointEdges
    (m : B.support → ℚ) (pt : DoubleSurface B → Prop) (hpt : ∀ σ, pt σ.swap ↔ pt σ)
    (Zl : (DoubleSurface B → ℚ) →ₗ[ℚ] (∀ i, V i))
    (ρv : ∀ σ : DoubleSurface B, V σ.fstComponent)
    (Bf : ∀ i, V i →ₗ[ℚ] V i →ₗ[ℚ] ℚ) (UA : ∀ σ : DoubleSurface B, V σ.fstComponent →ₗ[ℚ] ℚ)
    (hZlin : ∀ (f : ∀ i, V i →ₗ[ℚ] ℚ) (a : DoubleSurface B → ℚ),
      ∑ i, f i (Zl a i) = ∑ σ : DoubleSurface B, a σ * f σ.fstComponent (ρv σ))
    (hRA : ∀ (σ : DoubleSurface B) x, UA σ x = Bf σ.fstComponent x (ρv σ))
    (hWI : ∀ a ∈ orientedSurfaceCoefficients B, (∀ σ, ¬ pt σ → a σ = 0) →
      ∑ i, Bf i (Zl a i) (Zl a i) / m i = 0 → a = 0)
    (L : ∀ i, V i) :
    ∃ a ∈ orientedSurfaceCoefficients B, (∀ σ, ¬ pt σ → a σ = 0) ∧
      ∀ σ, pt σ → UA σ ((L - Zl a) σ.fstComponent) / m σ.fstComponent =
        UA σ.swap ((L - Zl a) σ.sndComponent) / m σ.sndComponent := by
  classical
  let O : Submodule ℚ (DoubleSurface B → ℚ) :=
    { carrier := {a | (∀ σ, a σ.swap = -a σ) ∧ ∀ σ, ¬ pt σ → a σ = 0}
      add_mem' := fun {a b} ha hb =>
        ⟨fun σ => by simp [ha.1 σ, hb.1 σ, add_comm], fun σ h => by simp [ha.2 σ h, hb.2 σ h]⟩
      zero_mem' := ⟨fun σ => by simp, fun σ _ => rfl⟩
      smul_mem' := fun c a ha => ⟨fun σ => by simp [ha.1 σ], fun σ h => by simp [ha.2 σ h]⟩ }
  let g : (∀ i, V i) →ₗ[ℚ] (DoubleSurface B → ℚ) :=
    LinearMap.pi fun σ => if pt σ then
      (m σ.fstComponent)⁻¹ • (UA σ ∘ₗ LinearMap.proj σ.fstComponent) -
        (m σ.sndComponent)⁻¹ • (UA σ.swap ∘ₗ LinearMap.proj σ.sndComponent) else 0
  have hg : ∀ x σ, g x σ = if pt σ then UA σ (x σ.fstComponent) / m σ.fstComponent -
      UA σ.swap (x σ.sndComponent) / m σ.sndComponent else 0 := by
    intro x σ
    simp only [g, LinearMap.pi_apply]
    split_ifs
    · simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply,
        LinearMap.proj_apply, smul_eq_mul, div_eq_inv_mul]
      rfl
    · rfl
  have hgO : ∀ x, g x ∈ O := by
    intro x
    refine ⟨fun σ => ?_, fun σ h => ?_⟩
    · rw [hg, hg]
      by_cases h : pt σ
      · simp only [(hpt σ).2 h, h, ↓reduceIte]
        change UA σ.swap (x σ.sndComponent) / m σ.sndComponent -
            UA σ (x σ.fstComponent) / m σ.fstComponent =
          -(UA σ (x σ.fstComponent) / m σ.fstComponent -
            UA σ.swap (x σ.sndComponent) / m σ.sndComponent)
        ring
      · simp only [mt (hpt σ).1 h, h, ↓reduceIte, neg_zero]
    · simp only [hg, h, ↓reduceIte]
  let T : O →ₗ[ℚ] O := ((g ∘ₗ Zl).domRestrict O).codRestrict O fun a => hgO _
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    have h0 : ∀ σ, g (Zl a.1) σ = 0 := fun σ => congrFun (congrArg Subtype.val ha) σ
    let X : DoubleSurface B → ℚ := fun σ => UA σ (Zl a.1 σ.fstComponent) / m σ.fstComponent
    have h1 : ∀ σ, a.1 σ * g (Zl a.1) σ = a.1 σ * X σ - a.1 σ * X σ.swap := by
      intro σ
      rw [hg]
      by_cases h : pt σ
      · simp only [h, ↓reduceIte]
        change a.1 σ * (UA σ (Zl a.1 σ.fstComponent) / m σ.fstComponent -
            UA σ.swap (Zl a.1 σ.sndComponent) / m σ.sndComponent) =
          a.1 σ * (UA σ (Zl a.1 σ.fstComponent) / m σ.fstComponent) -
            a.1 σ * (UA σ.swap (Zl a.1 σ.sndComponent) / m σ.sndComponent)
        ring
      · simp only [h, ↓reduceIte, a.2.2 σ h]
        ring
    have h2 : ∑ σ : DoubleSurface B, a.1 σ * X σ.swap = -∑ σ : DoubleSurface B, a.1 σ * X σ := by
      rw [← DoubleSurface.sum_comp_swap (fun σ => a.1 σ * X σ.swap)]
      simp only [DoubleSurface.swap_swap, a.2.1, neg_mul, Finset.sum_neg_distrib]
    have h3 : ∑ σ : DoubleSurface B, a.1 σ * X σ = ∑ i, Bf i (Zl a.1 i) (Zl a.1 i) / m i := by
      have := hZlin (fun i => (m i)⁻¹ • Bf i (Zl a.1 i)) a.1
      simp only [LinearMap.smul_apply, smul_eq_mul] at this
      simp only [X, hRA, div_eq_inv_mul]
      rw [this]
    have hsum : ∑ σ : DoubleSurface B, a.1 σ * g (Zl a.1) σ =
        2 * ∑ i, Bf i (Zl a.1 i) (Zl a.1 i) / m i := by
      rw [Finset.sum_congr rfl fun σ _ => h1 σ, Finset.sum_sub_distrib, h2, h3]
      ring
    simp only [h0, mul_zero, Finset.sum_const_zero] at hsum
    exact Subtype.ext (hWI a.1 a.2.1 a.2.2 (by linarith))
  obtain ⟨a, ha⟩ := (LinearMap.injective_iff_surjective.1 hinj) ⟨g L, hgO L⟩
  refine ⟨a.1, a.2.1, a.2.2, fun σ hσ => ?_⟩
  have h := congrFun (congrArg Subtype.val ha) σ
  change g (Zl a.1) σ = g L σ at h
  simp only [hg, hσ, ↓reduceIte] at h
  have e : UA σ.swap (L σ.sndComponent - Zl a.1 σ.sndComponent) =
      UA σ.swap (L σ.sndComponent) - UA σ.swap (Zl a.1 σ.sndComponent) :=
    (UA σ.swap).map_sub _ _
  simp only [Pi.sub_apply, map_sub, sub_div]
  rw [e, sub_div]
  linarith

/-- **The numerical form of the Hodge index argument for the generic algebraic defect.**

The data: positive multiplicities `mᵢ` (`D = ∑ mᵢ Fᵢ`) and a rational `N` (`A = N H - D`); the curve
components `cur` and the point edges `pt` (double surfaces mapping to points); the divisor
spaces `Vᵢ`, subspaces `Kᵢ` (divisors of class zero) and the divisors `hvᵢ = H|_{Fᵢ}`; on `Fᵢ` the
forms `Bf x y = x·y·A`, `BH x y = x·y·H`, `G x y = x·y·Fᵢ`, `Lam x = x·A²`, `LamH x = x·H·A`,
`GA x = x·A·Fᵢ`; on a double surface `S` of `(Fᵢ, Fⱼ)` the forms `U x x' = x|_S·x'|_S`,
`C x y = x|_S·y|_S`, `UA x = x|_S·A|_S`, `UH x = x|_S·H|_S`.

The hypotheses: `hGA`, `hG` are `mᵢ Fᵢ|_{Fᵢ} = N H - A - ∑_{j ≠ i} mⱼ Fⱼ|_{Fᵢ}`; `hKB` are the
identities of the zero ambient class intersected with `Fᵢ · A` and with itself, for `L - Zl a`
and every point-edge system `a`; `hvan` is the vanishing on the general fibres over the singular
curves; `hTIp`, `hTIc` are the threefold index theorems (ordinary, and isotropic with respect to
`H`), `hSIp`, `hSIc` the surface index theorems, `hWI` the weighted surface identity; the
remaining hypotheses are the positivity and vanishing of the intersection numbers of `H`.

The conclusion: an oriented system `a` supported on the point edges with every
`Lᵢ - Zᵢ(a) ∈ Kᵢ`. -/
theorem exists_mem_orientedSurfaceCoefficients_forall_sub_mem_of_hodgeIndex
    [DecidableEq B.support] (m : B.support → ℚ) (hm : ∀ i, 0 < m i) (N : ℚ)
    (cur : B.support → Prop) (pt : DoubleSurface B → Prop) (hpt : ∀ σ, pt σ.swap ↔ pt σ)
    (hptc : ∀ σ : DoubleSurface B, ¬ cur σ.fstComponent → pt σ)
    (K : ∀ i, Submodule ℚ (V i)) (hv : ∀ i, V i)
    (Zl : (DoubleSurface B → ℚ) →ₗ[ℚ] (∀ i, V i))
    (ρv : ∀ σ : DoubleSurface B, V σ.fstComponent)
    (Bf BH G : ∀ i, V i →ₗ[ℚ] V i →ₗ[ℚ] ℚ) (Lam LamH GA : ∀ i, V i →ₗ[ℚ] ℚ)
    (U : ∀ σ : DoubleSurface B, V σ.fstComponent →ₗ[ℚ] V σ.fstComponent →ₗ[ℚ] ℚ)
    (C : ∀ σ : DoubleSurface B, V σ.fstComponent →ₗ[ℚ] V σ.sndComponent →ₗ[ℚ] ℚ)
    (UA UH : ∀ σ : DoubleSurface B, V σ.fstComponent →ₗ[ℚ] ℚ)
    (hZlin : ∀ (f : ∀ i, V i →ₗ[ℚ] ℚ) (a : DoubleSurface B → ℚ),
      ∑ i, f i (Zl a i) = ∑ σ : DoubleSurface B, a σ * f σ.fstComponent (ρv σ))
    (hRA : ∀ (σ : DoubleSurface B) x, UA σ x = Bf σ.fstComponent x (ρv σ))
    (hWI : ∀ a ∈ orientedSurfaceCoefficients B, (∀ σ, ¬ pt σ → a σ = 0) →
      ∑ i, Bf i (Zl a i) (Zl a i) / m i = 0 → a = 0)
    (hGA : ∀ (x : ∀ i, V i) i, -m i * GA i (x i) = Lam i (x i) - N * LamH i (x i) +
      ∑ σ : DoubleSurface B, if σ.fstComponent = i then
        m σ.sndComponent * UA σ (x σ.fstComponent) else 0)
    (hG : ∀ (x : ∀ i, V i) i, -m i * G i (x i) (x i) =
      Bf i (x i) (x i) - N * BH i (x i) (x i) +
      ∑ σ : DoubleSurface B, if σ.fstComponent = i then
        m σ.sndComponent * U σ (x σ.fstComponent) (x σ.fstComponent) else 0)
    (hpoint : ∀ i, ¬ cur i → ∀ x, LamH i x = 0 ∧ BH i x x = 0)
    (hTIp : ∀ i, ¬ cur i → ∀ x, Lam i x = 0 → Bf i x x ≤ 0 ∧ (Bf i x x = 0 → x ∈ K i))
    (hTIc : ∀ i, cur i → ∀ x, LamH i x = 0 → BH i x x = 0 →
      Bf i x x ≤ 0 ∧ (Bf i x x = 0 → ∃ c : ℚ, x - c • hv i ∈ K i))
    (hSIp : ∀ σ, pt σ → ∀ x y, UA σ x = UA σ.swap y →
      U σ x x - 2 * C σ x y + U σ.swap y y ≤ 0)
    (hSIc : ∀ σ, ¬ pt σ → ∀ x y, UH σ x = 0 → UH σ.swap y = 0 →
      U σ x x - 2 * C σ x y + U σ.swap y y ≤ 0)
    (hK : ∀ i, ∀ k ∈ K i, GA i k = 0)
    (hKU : ∀ σ : DoubleSurface B, ∀ k ∈ K σ.fstComponent, UA σ k = 0)
    (hHA : ∀ i, cur i → 0 < Lam i (hv i)) (hHH : ∀ i, cur i → LamH i (hv i) = 0)
    (hHsym : ∀ σ : DoubleSurface B, UA σ (hv σ.fstComponent) = UA σ.swap (hv σ.sndComponent))
    (hHnn : ∀ σ : DoubleSurface B, 0 ≤ UA σ (hv σ.fstComponent))
    (L : ∀ i, V i)
    (hvan : ∀ a ∈ orientedSurfaceCoefficients B, (∀ σ, ¬ pt σ → a σ = 0) →
      (∀ i, cur i → LamH i ((L - Zl a) i) = 0 ∧ BH i ((L - Zl a) i) ((L - Zl a) i) = 0) ∧
      ∀ σ, ¬ pt σ → UH σ ((L - Zl a) σ.fstComponent) = 0)
    (hKB : ∀ a ∈ orientedSurfaceCoefficients B, (∀ σ, ¬ pt σ → a σ = 0) →
      (∀ i, GA i ((L - Zl a) i) + ∑ σ : DoubleSurface B,
        (if σ.sndComponent = i then UA σ ((L - Zl a) σ.fstComponent) else 0) = 0) ∧
      ∑ i, G i ((L - Zl a) i) ((L - Zl a) i) + ∑ σ : DoubleSurface B,
        C σ ((L - Zl a) σ.fstComponent) ((L - Zl a) σ.sndComponent) = 0) :
    ∃ a ∈ orientedSurfaceCoefficients B, (∀ σ, ¬ pt σ → a σ = 0) ∧ ∀ i, L i - Zl a i ∈ K i := by
  classical
  obtain ⟨a, ha, hapt, horth⟩ :=
    exists_mem_orientedSurfaceCoefficients_orth_of_pointEdges m pt hpt Zl ρv Bf UA hZlin hRA
      hWI L
  obtain ⟨hvc, hvs⟩ := hvan a ha hapt
  obtain ⟨hE1, hE2⟩ := hKB a ha hapt
  set M : ∀ i, V i := L - Zl a with hM
  set δ : ∀ i, V i := fun i => (m i)⁻¹ • M i with hδ
  have hMδ : ∀ i, M i = m i • δ i := fun i => by
    simp only [hδ, smul_smul, mul_inv_cancel₀ (hm i).ne', one_smul]
  have horthδ : ∀ σ, pt σ → UA σ (δ σ.fstComponent) = UA σ.swap (δ σ.sndComponent) := by
    intro σ hσ
    have e1 : UA σ (δ σ.fstComponent) = UA σ (M σ.fstComponent) / m σ.fstComponent := by
      simp only [hδ, map_smul, smul_eq_mul]; ring
    have e2 : UA σ.swap (δ σ.sndComponent) =
        UA σ.swap (M σ.sndComponent) / m σ.sndComponent := by
      calc UA σ.swap (δ σ.sndComponent) =
            (m σ.sndComponent)⁻¹ • UA σ.swap (M σ.sndComponent) :=
            (UA σ.swap).map_smul _ (M σ.sndComponent)
        _ = _ := by rw [smul_eq_mul]; ring
    rw [e1, e2]
    exact horth σ hσ
  have hLamH : ∀ i, LamH i (δ i) = 0 := by
    intro i
    by_cases hi : cur i
    · simp [hδ, (hvc i hi).1]
    · exact (hpoint i hi _).1
  have hBH : ∀ i, BH i (δ i) (δ i) = 0 := by
    intro i
    by_cases hi : cur i
    · simp [hδ, (hvc i hi).2]
    · exact (hpoint i hi _).2
  have hUH : ∀ σ, ¬ pt σ → UH σ (δ σ.fstComponent) = 0 := fun σ h => by
    simp [hδ, hvs σ h]
  have hLam : ∀ i, ¬ cur i → Lam i (δ i) = 0 := by
    intro i hi
    have h1 := hGA δ i
    have h2 := hE1 i
    rw [hLamH i, mul_zero, sub_zero] at h1
    have hsw : ∑ σ : DoubleSurface B,
        (if σ.sndComponent = i then UA σ (M σ.fstComponent) else 0) =
        ∑ σ : DoubleSurface B,
          (if σ.fstComponent = i then UA σ.swap (M σ.sndComponent) else 0) :=
      (DoubleSurface.sum_comp_swap
        (fun σ => if σ.sndComponent = i then UA σ (M σ.fstComponent) else 0)).symm
    have hterm : ∀ σ : DoubleSurface B,
        (if σ.fstComponent = i then m σ.sndComponent * UA σ (δ σ.fstComponent) else 0) =
          (if σ.fstComponent = i then UA σ.swap (M σ.sndComponent) else 0) := by
      intro σ
      split_ifs with h
      · subst h
        rw [horthδ σ (hptc σ hi), hMδ σ.sndComponent]
        exact ((UA σ.swap).map_smul _ _).symm
      · rfl
    rw [hsw, hMδ i, map_smul, smul_eq_mul] at h2
    rw [Finset.sum_congr rfl fun σ _ => hterm σ] at h1
    linear_combination -h1 - h2
  have hBle : ∀ i, Bf i (δ i) (δ i) ≤ 0 := by
    intro i
    by_cases hi : cur i
    · exact (hTIc i hi _ (hLamH i) (hBH i)).1
    · exact (hTIp i hi _ (hLam i hi)).1
  have hW : ∀ σ : DoubleSurface B, U σ (δ σ.fstComponent) (δ σ.fstComponent) -
      2 * C σ (δ σ.fstComponent) (δ σ.sndComponent) +
        U σ.swap (δ σ.sndComponent) (δ σ.sndComponent) ≤ 0 := by
    intro σ
    by_cases h : pt σ
    · exact hSIp σ h _ _ (horthδ σ h)
    · exact hSIc σ h _ _ (hUH σ h) (hUH σ.swap (mt (hpt σ).1 h))
  have hGi : ∀ i, G i (M i) (M i) = -(m i * Bf i (δ i) (δ i)) -
      ∑ σ : DoubleSurface B, if σ.fstComponent = i then
        m σ.fstComponent * m σ.sndComponent * U σ (δ σ.fstComponent) (δ σ.fstComponent)
        else 0 := by
    intro i
    have h := hG δ i
    rw [hBH i, mul_zero, sub_zero] at h
    have e : G i (M i) (M i) = m i * m i * G i (δ i) (δ i) := by
      rw [hMδ i]
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
      ring
    have e' : ∀ σ : DoubleSurface B, (if σ.fstComponent = i then
        m σ.fstComponent * m σ.sndComponent * U σ (δ σ.fstComponent) (δ σ.fstComponent)
        else 0) = m i * (if σ.fstComponent = i then
          m σ.sndComponent * U σ (δ σ.fstComponent) (δ σ.fstComponent) else 0) := by
      intro σ
      split_ifs with hσ
      · subst hσ; ring
      · ring
    rw [Finset.sum_congr rfl fun σ _ => e' σ, ← Finset.mul_sum, e]
    linear_combination (-m i) * h
  have hCσ : ∀ σ : DoubleSurface B, C σ (M σ.fstComponent) (M σ.sndComponent) =
      m σ.fstComponent * m σ.sndComponent * C σ (δ σ.fstComponent) (δ σ.sndComponent) := by
    intro σ
    rw [hMδ σ.fstComponent, hMδ σ.sndComponent]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  have hfib : ∑ i, (∑ σ : DoubleSurface B, if σ.fstComponent = i then
      m σ.fstComponent * m σ.sndComponent * U σ (δ σ.fstComponent) (δ σ.fstComponent)
      else 0) = ∑ σ : DoubleSurface B,
        m σ.fstComponent * m σ.sndComponent * U σ (δ σ.fstComponent) (δ σ.fstComponent) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.sum_ite_eq]
    simp
  have hUsym : ∑ σ : DoubleSurface B, m σ.fstComponent * m σ.sndComponent *
      U σ (δ σ.fstComponent) (δ σ.fstComponent) =
      ∑ σ : DoubleSurface B, m σ.fstComponent * m σ.sndComponent *
        U σ.swap (δ σ.sndComponent) (δ σ.sndComponent) := by
    rw [← DoubleSurface.sum_comp_swap]
    refine Finset.sum_congr rfl fun σ _ => ?_
    exact (by ring : m σ.sndComponent * m σ.fstComponent *
        U σ.swap (δ σ.sndComponent) (δ σ.sndComponent) =
      m σ.fstComponent * m σ.sndComponent * U σ.swap (δ σ.sndComponent) (δ σ.sndComponent))
  have hkey : ∑ i, m i * Bf i (δ i) (δ i) + (1 / 2 : ℚ) * ∑ σ : DoubleSurface B,
      m σ.fstComponent * m σ.sndComponent * (U σ (δ σ.fstComponent) (δ σ.fstComponent) -
        2 * C σ (δ σ.fstComponent) (δ σ.sndComponent) +
          U σ.swap (δ σ.sndComponent) (δ σ.sndComponent)) = 0 := by
    simp_rw [hGi, hCσ, Finset.sum_sub_distrib, Finset.sum_neg_distrib, hfib] at hE2
    have : ∑ σ : DoubleSurface B, m σ.fstComponent * m σ.sndComponent *
        (U σ (δ σ.fstComponent) (δ σ.fstComponent) -
          2 * C σ (δ σ.fstComponent) (δ σ.sndComponent) +
          U σ.swap (δ σ.sndComponent) (δ σ.sndComponent)) =
        ∑ σ : DoubleSurface B, m σ.fstComponent * m σ.sndComponent *
          U σ (δ σ.fstComponent) (δ σ.fstComponent) -
        2 * ∑ σ : DoubleSurface B, m σ.fstComponent * m σ.sndComponent *
          C σ (δ σ.fstComponent) (δ σ.sndComponent) +
        ∑ σ : DoubleSurface B, m σ.fstComponent * m σ.sndComponent *
          U σ.swap (δ σ.sndComponent) (δ σ.sndComponent) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun σ _ => ?_
      ring
    rw [this, ← hUsym]
    linear_combination -hE2
  have hnn1 : ∀ i ∈ (Finset.univ : Finset B.support), 0 ≤ -(m i * Bf i (δ i) (δ i)) :=
    fun i _ => by nlinarith [hm i, hBle i]
  have hnn2 : ∀ σ ∈ (Finset.univ : Finset (DoubleSurface B)),
      0 ≤ -(m σ.fstComponent * m σ.sndComponent * (U σ (δ σ.fstComponent) (δ σ.fstComponent) -
        2 * C σ (δ σ.fstComponent) (δ σ.sndComponent) +
          U σ.swap (δ σ.sndComponent) (δ σ.sndComponent))) := fun σ _ => by
    have := mul_pos (hm σ.fstComponent) (hm σ.sndComponent)
    nlinarith [hW σ]
  have hs1 := Finset.sum_nonneg hnn1
  have hs2 := Finset.sum_nonneg hnn2
  rw [Finset.sum_neg_distrib] at hs1 hs2
  have h0 : ∑ i, -(m i * Bf i (δ i) (δ i)) = 0 := by
    rw [Finset.sum_neg_distrib]; linarith
  have hB0 : ∀ i, Bf i (δ i) (δ i) = 0 := fun i => by
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn1).1 h0 i (Finset.mem_univ i)
    exact (mul_eq_zero.1 (neg_eq_zero.1 this)).resolve_left (hm i).ne'
  have hc : ∀ i, ∃ c : ℚ, δ i - c • hv i ∈ K i ∧ (¬ cur i → c = 0) := by
    intro i
    by_cases hi : cur i
    · obtain ⟨c, hc⟩ := (hTIc i hi _ (hLamH i) (hBH i)).2 (hB0 i)
      exact ⟨c, hc, fun h => absurd hi h⟩
    · exact ⟨0, by simpa using (hTIp i hi _ (hLam i hi)).2 (hB0 i), fun _ => rfl⟩
  choose c hcK hc0 using hc
  have hMK : ∀ i, M i - (m i * c i) • hv i ∈ K i := fun i => by
    have : M i - (m i * c i) • hv i = m i • (δ i - c i • hv i) := by
      simp only [hδ, smul_sub, smul_smul, mul_inv_cancel₀ (hm i).ne', one_smul]
    rw [this]
    exact (K i).smul_mem _ (hcK i)
  have hGAM : ∀ i, GA i (M i) = m i * c i * GA i (hv i) := fun i => by
    have := hK i _ (hMK i)
    rw [map_sub, map_smul, smul_eq_mul] at this
    linarith
  have hUAM : ∀ σ : DoubleSurface B, UA σ (M σ.fstComponent) =
      m σ.fstComponent * c σ.fstComponent * UA σ (hv σ.fstComponent) := fun σ => by
    have := hKU σ _ (hMK σ.fstComponent)
    rw [map_sub, map_smul, smul_eq_mul] at this
    linarith
  set s : DoubleSurface B → ℚ := fun σ => UA σ (hv σ.fstComponent) with hs
  have hss : ∀ σ, s σ.swap = s σ := fun σ => (hHsym σ).symm
  have hcμ : ∀ i, c i * LamH i (hv i) = 0 := fun i => by
    by_cases hi : cur i
    · rw [hHH i hi, mul_zero]
    · rw [hc0 i hi, zero_mul]
  have hE1' : ∀ i, m i * c i * GA i (hv i) + ∑ σ : DoubleSurface B,
      (if σ.sndComponent = i then m σ.fstComponent * c σ.fstComponent * s σ else 0) = 0 := by
    intro i
    have := hE1 i
    rw [hGAM] at this
    simpa only [hUAM] using this
  have hgi : ∀ i, m i * c i * (m i * c i * GA i (hv i)) =
      -(m i * c i ^ 2 * Lam i (hv i)) - ∑ σ : DoubleSurface B, if σ.fstComponent = i then
        m σ.fstComponent * m σ.sndComponent * c σ.fstComponent ^ 2 * s σ else 0 := by
    intro i
    have h := hGA hv i
    have e' : ∀ σ : DoubleSurface B, (if σ.fstComponent = i then
        m σ.fstComponent * m σ.sndComponent * c σ.fstComponent ^ 2 * s σ else 0) =
        m i * c i ^ 2 * (if σ.fstComponent = i then
          m σ.sndComponent * UA σ (hv σ.fstComponent) else 0) := by
      intro σ
      split_ifs with hσ
      · subst hσ; simp only [hs]; ring
      · ring
    rw [Finset.sum_congr rfl fun σ _ => e' σ, ← Finset.mul_sum]
    linear_combination (-(m i * c i ^ 2)) * h + N * m i * c i * hcμ i
  have hsum2 : ∑ i, m i * c i * (∑ σ : DoubleSurface B,
      (if σ.sndComponent = i then m σ.fstComponent * c σ.fstComponent * s σ else 0)) =
      ∑ σ : DoubleSurface B, m σ.fstComponent * m σ.sndComponent * c σ.fstComponent *
        c σ.sndComponent * s σ := by
    simp only [Finset.mul_sum, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, ↓reduceIte]
    ring
  have hsum3 : ∑ i, (∑ σ : DoubleSurface B, if σ.fstComponent = i then
      m σ.fstComponent * m σ.sndComponent * c σ.fstComponent ^ 2 * s σ else 0) =
      ∑ σ : DoubleSurface B, m σ.fstComponent * m σ.sndComponent * c σ.fstComponent ^ 2 *
        s σ := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.sum_ite_eq]
    simp
  have hsum4 : ∑ σ : DoubleSurface B, m σ.fstComponent * m σ.sndComponent *
      c σ.fstComponent ^ 2 * s σ = ∑ σ : DoubleSurface B, m σ.fstComponent *
        m σ.sndComponent * c σ.sndComponent ^ 2 * s σ := by
    rw [← DoubleSurface.sum_comp_swap]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [hss σ]
    change m σ.sndComponent * m σ.fstComponent * c σ.sndComponent ^ 2 * s σ = _
    ring
  have htot : ∑ i, m i * c i * (m i * c i * GA i (hv i) + ∑ σ : DoubleSurface B,
      (if σ.sndComponent = i then m σ.fstComponent * c σ.fstComponent * s σ else 0)) = 0 := by
    simp [hE1']
  simp only [mul_add, Finset.sum_add_distrib, hgi, Finset.sum_sub_distrib,
    Finset.sum_neg_distrib, hsum3] at htot
  rw [hsum2] at htot
  have hsq : ∑ σ : DoubleSurface B, m σ.fstComponent * m σ.sndComponent *
      (c σ.fstComponent - c σ.sndComponent) ^ 2 * s σ =
      ∑ σ : DoubleSurface B, m σ.fstComponent * m σ.sndComponent * c σ.fstComponent ^ 2 * s σ +
      ∑ σ : DoubleSurface B, m σ.fstComponent * m σ.sndComponent * c σ.sndComponent ^ 2 * s σ -
      2 * ∑ σ : DoubleSurface B, m σ.fstComponent * m σ.sndComponent * c σ.fstComponent *
        c σ.sndComponent * s σ := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    ring
  have hq1 : ∀ i ∈ (Finset.univ : Finset B.support), 0 ≤ m i * c i ^ 2 * Lam i (hv i) := by
    intro i _
    by_cases hi : cur i
    · exact mul_nonneg (mul_nonneg (hm i).le (sq_nonneg _)) (hHA i hi).le
    · rw [hc0 i hi]; simp
  have hq2 : ∀ σ ∈ (Finset.univ : Finset (DoubleSurface B)), 0 ≤ m σ.fstComponent *
      m σ.sndComponent * (c σ.fstComponent - c σ.sndComponent) ^ 2 * s σ := fun σ _ =>
    mul_nonneg (mul_nonneg (mul_pos (hm _) (hm _)).le (sq_nonneg _)) (hHnn σ)
  have hQ1 := Finset.sum_nonneg hq1
  have hQ2 := Finset.sum_nonneg hq2
  have hQ0 : ∑ i, m i * c i ^ 2 * Lam i (hv i) = 0 := by
    rw [← hsum4] at hsq
    linarith
  have hc0' : ∀ i, c i = 0 := by
    intro i
    by_cases hi : cur i
    · have := (Finset.sum_eq_zero_iff_of_nonneg hq1).1 hQ0 i (Finset.mem_univ i)
      have : c i ^ 2 = 0 := by
        by_contra hne
        have := mul_pos (mul_pos (hm i) (lt_of_le_of_ne (sq_nonneg (c i)) (Ne.symm hne)))
          (hHA i hi)
        linarith
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    · exact hc0 i hi
  refine ⟨a, ha, hapt, fun i => ?_⟩
  have hδK : δ i ∈ K i := by simpa [hc0' i] using hcK i
  show M i ∈ K i
  rw [hMδ i]
  exact (K i).smul_mem _ hδK

end Numerical

end MMP.Fourfold
