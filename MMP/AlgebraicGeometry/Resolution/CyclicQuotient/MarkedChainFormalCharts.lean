module

public import MMP.AlgebraicGeometry.Resolution.CyclicQuotient.ProjectiveLineCharts
public import MMP.AlgebraicGeometry.MMP.Models
public import MMP.AlgebraicGeometry.Intersection.Surface.Symmetry
public import StacksFrontier.AlgebraicGeometry.Curves.ProjectiveLineCriterion.ProjectiveLine
public import StacksFrontier.AlgebraicGeometry.Curves.ProjectiveLineCriterion.ProjectiveLineProperties
public import StacksFrontier.AlgebraicGeometry.Variety.SeparatingPointsTangentVectors.Canonical
public import StacksFrontier.AlgebraicGeometry.Curves.LinearSeriesChartRatio
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.RelativeProjModuleSheafDegreeZeroMap
public import StacksFrontier.AlgebraicGeometry.ProjLargeDegreeSections.Noetherian
public import StacksFrontier.AlgebraicGeometry.ProjLargeDegreeSections.KernelData
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.StableImageExtension
public import StacksFrontier.AlgebraicGeometry.PicSurjectiveOpen.AffineGenerator
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.SchemeRepresentation
public import MMP.AlgebraicGeometry.CohenMacaulay.SerreDuality
public import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.Basic
public import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.OrderOnePullback
public import MMP.AlgebraicGeometry.Curves.Maps.TwoStageObstruction
public import MMP.AlgebraicGeometry.Resolution.CyclicQuotient.ChartTransitions

/-!
# Formal coordinate charts along a doubly marked chain of rational curves

Let `X` be a smooth surface over an algebraically closed field `K` of characteristic zero and
`E = E₁ + ⋯ + E_r` a chain of smooth rational curves on `X` with simple normal crossings and
`Eᵢ² = -bᵢ`, whose two ends are marked by smooth formal curve germs transverse to `E₁` and `E_r`,
away from the other components and at distinct points. The formal completion of `X` along `E`
is covered by `r + 1` formal coordinate charts `(xⱼ, yⱼ)`, `0 ≤ j ≤ r`: the exceptional ideal is
`(y₀)` in the first chart, `(x_r)` in the last one and `(xⱼ yⱼ)` in the others, the markings are
`(x₀)` and `(y_r)`, consecutive charts meet along the formal neighbourhood of
`𝔾_m ⊆ Eⱼ`, non-consecutive ones do not meet, and after rescaling the coordinates the
transitions have the normalized initial data
`xⱼ ≡ x_{j-1}^{bⱼ} y_{j-1} (mod y_{j-1}²)` and `yⱼ ≡ x_{j-1}⁻¹ (mod y_{j-1})`.

## Main results

* `MMP.Mori.exists_formalCoordinateCharts_of_isSNCChain`: the charts and their normalized
  initial transition data.

## Implementation notes

*The formal completion.* The completion `X̂` of `X` along `E` is the colimit of the
thickenings `(n+1)E`, the closed subschemes cut out by the powers `I_E ^ (n + 1)` of the ideal
`I_E = ∏ᵢ I_{Eᵢ}`. A formal function on the formal open over an open `V ⊆ X` is a compatible
family of sections of the thickenings over `V`, and a formal chart isomorphic to the completion
of `𝔸²_K` along the ideal `J` is a pair of such families `(x, y)` such that, at every level, the
thickening over `V` is affine and `K[X₀, X₁] → Γ((n+1)E, V)`, `X₀ ↦ x`, `X₁ ↦ y`, is
surjective with kernel `J ^ (n + 1)`. Overlaps, markings and initial data are likewise read off
at finite levels: the first transition formula lives on the second thickening `2E`, where the
normal coordinate `y_{j-1}` is retained although it vanishes on `E`, and the second on `E`.

*The markings.* A smooth formal curve germ `D̂` at `p` transverse to `E` is recorded by its
traces `Zₙ = D̂ ∩ (n+1)E`: closed subschemes `Zₙ ⊆ (n+1)E` with `Zₙ = Zₙ₊₁ ∩ (n+1)E`,
`Z₀ = {p}` and `Zₙ ≅ Spec K[t]/(t^(n+1))` over `K`; conversely such a family is the trace
family of the germ `D̂ = lim Zₙ` of the completed local ring at `p`, which is smooth since
`lim K[t]/(t^(n+1)) = K⟦t⟧` and transverse to `E` since `D̂ ∩ E = Z₀` is a reduced point.
In particular the two markings may be two formal branches of one algebraic curve.

*The chain.* The chain condition is recorded by intersection numbers: on a smooth surface,
`(Eᵢ · Eᵢ₊₁) = 1` says that consecutive components meet transversally in exactly one point,
and non-consecutive components are disjoint.
-/

universe u

open AlgebraicGeometry hiding PrimeDivisor
open CategoryTheory Opposite MMP.Mori

open MMP.Resolution.MarkedChain

namespace MMP.Mori.MarkedChainCharts

private theorem J_castSucc_le {K : Type u} [Field K] {r : ℕ} (j : Fin r) :
    ((if (j.castSucc : Fin (r + 1)) = 0 then Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 2) K)}
      else if (j.castSucc : Fin (r + 1)) = Fin.last r then Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin 2) K)}
      else Ideal.span {(MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) K)}) ^ (0 + 1)) ≤
      Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 2) K)} := by
  split_ifs with h1 h2
  · simp
  · exact absurd h2 (Fin.castSucc_lt_last j).ne
  · rw [zero_add, pow_one, Ideal.span_singleton_le_span_singleton]
    exact Dvd.intro_left _ rfl

private theorem J_succ_le {K : Type u} [Field K] {r : ℕ} (j : Fin r) :
    ((if (j.succ : Fin (r + 1)) = 0 then Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 2) K)}
      else if (j.succ : Fin (r + 1)) = Fin.last r then Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin 2) K)}
      else Ideal.span {(MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) K)}) ^ (0 + 1)) ≤
      Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin 2) K)} := by
  split_ifs with h1 h2
  · exact absurd h1 (Fin.succ_ne_zero j)
  · simp
  · rw [zero_add, pow_one, Ideal.span_singleton_le_span_singleton]
    exact Dvd.intro _ rfl

private theorem incl_trans {Y : Scheme.{u}} {I₂ I₁ Ej : Y.IdealSheafData} (h₂₁ : I₂ ≤ I₁) (h₁E : I₁ ≤ Ej)
    (U : Y.Opens) (a : Γ(I₂.subscheme, I₂.subschemeι ⁻¹ᵁ U)) :
    inclSections (h₂₁.trans h₁E) U a = inclSections h₁E U (inclSections h₂₁ U a) := by
  have c1 := Scheme.Hom.appLE_comp_appLE (Scheme.IdealSheafData.inclusion h₁E)
    (Scheme.IdealSheafData.inclusion h₂₁) (I₂.subschemeι ⁻¹ᵁ U) (I₁.subschemeι ⁻¹ᵁ U)
    (Ej.subschemeι ⁻¹ᵁ U)
    (by rw [← Scheme.Hom.comp_preimage, Scheme.IdealSheafData.inclusion_subschemeι])
    (by rw [← Scheme.Hom.comp_preimage, Scheme.IdealSheafData.inclusion_subschemeι])
  have c2 := appLE_congr_morphism (U := I₂.subschemeι ⁻¹ᵁ U) (V := Ej.subschemeι ⁻¹ᵁ U)
    (Scheme.IdealSheafData.inclusion_comp h₂₁ h₁E)
    (by rw [← Scheme.Hom.comp_preimage]
        simp only [Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]; exact le_rfl)
    (by rw [← Scheme.Hom.comp_preimage, Scheme.IdealSheafData.inclusion_subschemeι])
  exact (congrArg (fun φ => φ.hom a) (c1.trans c2)).symm

/-- Restricting a chart `K[x, y] → Γ(I₂, U)` along `I₂ ≤ I₁` is the chart of the restricted
coordinates. -/
private theorem inclSections_comp_eval₂Hom {K : Type u} [Field K] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of K)) {I₂ I₁ : Y.IdealSheafData} (h : I₂ ≤ I₁) (U : Y.Opens)
    {x y : Γ(I₂.subscheme, I₂.subschemeι ⁻¹ᵁ U)} {x0 y0 : Γ(I₁.subscheme, I₁.subschemeι ⁻¹ᵁ U)}
    (hx : inclSections h U x = x0) (hy : inclSections h U y = y0) :
    (inclSections h U).comp (MvPolynomial.eval₂Hom (sigmaSub sY I₂ U) ![x, y]) =
      MvPolynomial.eval₂Hom (sigmaSub sY I₁ U) ![x0, y0] := by
  refine MvPolynomial.ringHom_ext (fun k => ?_) (fun i => ?_)
  · simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
    exact inclSections_sigma sY h U k
  · fin_cases i
    · simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
      exact hx
    · simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
      exact hy

/-- Every element of a square-zero ideal is nilpotent. -/
private theorem isNilpotent_of_sq_eq_bot {A : Type*} [CommRing A] {N : Ideal A} (h : N ^ 2 = ⊥) :
    ∀ n ∈ N, IsNilpotent n := fun n hn => ⟨2, by simpa [h] using Ideal.pow_mem_pow hn 2⟩

private theorem chart_ring_facts {K : Type u} [Field K] {A1 A0 : Type u} [CommRing A1] [CommRing A0]
    (φ1 : MvPolynomial (Fin 2) K →+* A1) (φ0 : MvPolynomial (Fin 2) K →+* A0) (ρ : A1 →+* A0)
    (hρ : ρ.comp φ1 = φ0) (hs1 : Function.Surjective φ1)
    {J : Ideal (MvPolynomial (Fin 2) K)} (hk1 : RingHom.ker φ1 = J ^ 2) (hk0 : RingHom.ker φ0 = J)
    (hJ : J = Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 2) K)} ∨
      J = Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin 2) K)} ∨
      J = Ideal.span {(MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) K)}) :
    (RingHom.ker ρ) ^ 2 = ⊥ ∧
      (∀ (M' : Type u) [AddCommGroup M'] [Module (A1 ⧸ RingHom.ker ρ) M']
        [Module.Invertible (A1 ⧸ RingHom.ker ρ) M'], Module.Free (A1 ⧸ RingHom.ker ρ) M') := by
  have hker : ∀ p, φ1 p ∈ RingHom.ker ρ ↔ p ∈ J := by
    intro p
    rw [RingHom.mem_ker, ← hk0, RingHom.mem_ker, ← hρ]
    rfl
  constructor
  · rw [pow_two, ← le_bot_iff, Ideal.mul_le]
    intro n hn m hm
    obtain ⟨p, rfl⟩ := hs1 n
    obtain ⟨q, rfl⟩ := hs1 m
    have hp := (hker p).1 hn
    have hq := (hker q).1 hm
    rw [Ideal.mem_bot, ← map_mul, ← RingHom.mem_ker, hk1, pow_two]
    exact Ideal.mul_mem_mul hp hq
  · intro M' _ _ _
    refine free_of_invertible_chart ((Ideal.Quotient.mk (RingHom.ker ρ)).comp φ1)
      ((Ideal.Quotient.mk_surjective).comp hs1) (J := J) ?_ hJ M'
    ext p
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    exact hker p

section

open Stacks.SheafOfModules Stacks.SheafOfModules.TensorStalkRingedSpace Stacks.Divisors

private theorem exists_chart_gen {K : Type u} [Field K] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of K))
    (D : Y.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D]
    {I₁ I₂ : Y.IdealSheafData} (h₂₁ : I₂ ≤ I₁) (h₁D : I₁ ≤ D) (U : Y.Opens)
    (hA : IsAffineOpen (I₂.subschemeι ⁻¹ᵁ U))
    (xa ya : Γ(I₂.subscheme, I₂.subschemeι ⁻¹ᵁ U)) (xa0 ya0 : Γ(I₁.subscheme, I₁.subschemeι ⁻¹ᵁ U))
    (hx : inclSections h₂₁ U xa = xa0) (hy : inclSections h₂₁ U ya = ya0)
    {J : Ideal (MvPolynomial (Fin 2) K)}
    (hs1 : Function.Surjective (MvPolynomial.eval₂Hom (sigmaSub sY I₂ U) ![xa, ya]))
    (hk1 : RingHom.ker (MvPolynomial.eval₂Hom (sigmaSub sY I₂ U) ![xa, ya]) = J ^ 2)
    (hk0 : RingHom.ker (MvPolynomial.eval₂Hom (sigmaSub sY I₁ U) ![xa0, ya0]) = J)
    (hJ : J = Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 2) K)} ∨
      J = Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin 2) K)} ∨
      J = Ideal.span {(MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) K)})
    (v u : Fin 2) (huv : u ≠ v)
    (hJv : J = Ideal.span {(MvPolynomial.X v : MvPolynomial (Fin 2) K)} ∨
      J = Ideal.span {(MvPolynomial.X u * MvPolynomial.X v : MvPolynomial (Fin 2) K)})
    (w : Γ(I₂.subscheme, I₂.subschemeι ⁻¹ᵁ U))
    (hw : MvPolynomial.eval₂Hom (sigmaSub sY I₂ U) ![xa, ya] (MvPolynomial.X v) = w)
    (hker : RingHom.ker (inclSections (h₂₁.trans h₁D) U) = Ideal.span {w}) :
    ∃ G : GeneratorSections I₂.subscheme.toRingedSpace
      ((Scheme.Modules.pullback I₂.subschemeι).obj (Stacks.Divisors.modulesInvertibleSheaf D))
      (I₂.subschemeι ⁻¹ᵁ U),
      ((Scheme.Modules.pullback I₂.subschemeι).obj
          (Stacks.Divisors.modulesInvertibleSheaf D)).presheaf.map (homOfLE le_top).op
        (pullbackGlobalSections I₂.subschemeι (Stacks.Divisors.modulesInvertibleSheaf D)
          (Stacks.Divisors.canonicalSection D)) =
        w • (show Γ((Scheme.Modules.pullback I₂.subschemeι).obj
            (Stacks.Divisors.modulesInvertibleSheaf D), I₂.subschemeι ⁻¹ᵁ U) from G.val) := by
  subst hw
  let φ1 := MvPolynomial.eval₂Hom (sigmaSub sY I₂ U) ![xa, ya]
  let φ0 := MvPolynomial.eval₂Hom (sigmaSub sY I₁ U) ![xa0, ya0]
  have hρ : (inclSections h₂₁ U).comp φ1 = φ0 := inclSections_comp_eval₂Hom sY h₂₁ U hx hy
  obtain ⟨hN2, hfree⟩ := chart_ring_facts φ1 φ0 (inclSections h₂₁ U) hρ hs1 hk1 hk0 hJ
  have hann : ∀ z, z * φ1 (MvPolynomial.X v) = 0 → inclSections h₂₁ U z = 0 :=
    fun z hz => hann_chart hJv φ1 φ0 (inclSections h₂₁ U) hρ hs1 hk1 hk0 z hz
  obtain ⟨G0⟩ := nonempty_generatorSections_of_free_quot
    ((Scheme.Modules.pullback I₂.subschemeι).obj (Stacks.Divisors.modulesInvertibleSheaf D))
    hA (RingHom.ker (inclSections h₂₁ U)) ⟨2, hN2⟩ hfree
  exact exists_coeff_generator D h₂₁ h₁D U hA G0 _ hker hann (isNilpotent_of_sq_eq_bot hN2)

end

section

open Stacks.SheafOfModules Stacks.SheafOfModules.TensorStalkRingedSpace

private theorem ratio_incl {K : Type u} [Field K] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of K))
    {I₂ I₁ Ej : Y.IdealSheafData} (h₂₁ : I₂ ≤ I₁) (h₁E : I₁ ≤ Ej)
    (L : _root_.SheafOfModules.{u} (structureSheaf I₂.subscheme.toRingedSpace.sheaf))
    (W : Y.Opens)
    (Ga Gb : GeneratorSections I₂.subscheme.toRingedSpace L (I₂.subschemeι ⁻¹ᵁ W))
    (y x : Γ(I₂.subscheme, I₂.subschemeι ⁻¹ᵁ W))
    (hcoef : (show (structureSheaf I₂.subscheme.toRingedSpace.sheaf).obj.obj (op (I₂.subschemeι ⁻¹ᵁ W)) from y) • Ga.val = (show (structureSheaf I₂.subscheme.toRingedSpace.sheaf).obj.obj (op (I₂.subschemeι ⁻¹ᵁ W)) from x) • Gb.val)
    (c : K) (u : (Γ(I₂.subscheme, I₂.subschemeι ⁻¹ᵁ W))ˣ) (n : ℤ)
    (hu2 : x = sigmaSub sY I₂ W c * ((u ^ n : (Γ(I₂.subscheme, I₂.subschemeι ⁻¹ᵁ W))ˣ) :
      Γ(I₂.subscheme, I₂.subschemeι ⁻¹ᵁ W)) * y)
    (hann : ∀ z : Γ(I₂.subscheme, I₂.subschemeι ⁻¹ᵁ W), z * y = 0 → inclSections h₂₁ W z = 0) :
    inclSections (h₂₁.trans h₁E) W
        ((generatorRatioUnit L (I₂.subschemeι ⁻¹ᵁ W) Gb Ga).val :
          Γ(I₂.subscheme, I₂.subschemeι ⁻¹ᵁ W)) =
      sigmaSub sY Ej W c *
        ((Units.map (inclSections (h₂₁.trans h₁E) W).toMonoidHom u ^ n :
          (Γ(Ej.subscheme, Ej.subschemeι ⁻¹ᵁ W))ˣ) : Γ(Ej.subscheme, Ej.subschemeι ⁻¹ᵁ W)) := by
  have hm := mul_ratio_eq L (I₂.subschemeι ⁻¹ᵁ W) Gb Ga (show (structureSheaf I₂.subscheme.toRingedSpace.sheaf).obj.obj (op (I₂.subschemeι ⁻¹ᵁ W)) from x)
    (show (structureSheaf I₂.subscheme.toRingedSpace.sheaf).obj.obj (op (I₂.subschemeι ⁻¹ᵁ W)) from y)
    hcoef.symm
  have hv := generatorRatioUnit_val L (I₂.subschemeι ⁻¹ᵁ W) Gb Ga
  set ρ : Γ(I₂.subscheme, I₂.subschemeι ⁻¹ᵁ W) := (generatorRatioUnit L (I₂.subschemeι ⁻¹ᵁ W) Gb Ga).val
    with hρ
  have hz : (ρ - sigmaSub sY I₂ W c * ((u ^ n : (Γ(I₂.subscheme, I₂.subschemeι ⁻¹ᵁ W))ˣ) :
      Γ(I₂.subscheme, I₂.subschemeι ⁻¹ᵁ W))) * y = 0 := by
    have h1 : x = y * ρ := by rwa [hv]
    rw [h1] at hu2
    linear_combination hu2
  have hz0 := hann _ hz
  rw [map_sub, sub_eq_zero] at hz0
  rw [incl_trans h₂₁ h₁E W, hz0, ← incl_trans h₂₁ h₁E W, map_mul,
    inclSections_sigma sY (h₂₁.trans h₁E) W c]
  congr 1
  exact congrArg Units.val (map_zpow (Units.map (inclSections (h₂₁.trans h₁E) W).toMonoidHom) u n)

end

section

open Stacks.SheafOfModules Stacks.SheafOfModules.TensorStalkRingedSpace Stacks.Divisors
  AlgebraicGeometry.ProjectiveSpectrum.Proj Stacks.PicardUFD Stacks.ProjectiveChart
  RingedSpaceModuleAdjunction

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

private theorem d2_final {K : Type u} [Field K] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of K))
    (Ej : Y.IdealSheafData) [IsEffectiveCartierDivisor Ej] {I₁ I₂ : Y.IdealSheafData}
    (h₂₁ : I₂ ≤ I₁) (h₁E : I₁ ≤ Ej) (Va Vb : Y.Opens)
    (hU0 : IsAffineOpen (Ej.subschemeι ⁻¹ᵁ Va)) (hU1 : IsAffineOpen (Ej.subschemeι ⁻¹ᵁ Vb))
    (Ga : GeneratorSections I₂.subscheme.toRingedSpace
      ((Scheme.Modules.pullback I₂.subschemeι).obj (modulesInvertibleSheaf Ej)) (I₂.subschemeι ⁻¹ᵁ Va))
    (Gb : GeneratorSections I₂.subscheme.toRingedSpace
      ((Scheme.Modules.pullback I₂.subschemeι).obj (modulesInvertibleSheaf Ej)) (I₂.subschemeι ⁻¹ᵁ Vb))
    (y : Γ(I₂.subscheme, I₂.subschemeι ⁻¹ᵁ Va)) (x : Γ(I₂.subscheme, I₂.subschemeι ⁻¹ᵁ Vb))
    (hGa : ((Scheme.Modules.pullback I₂.subschemeι).obj (modulesInvertibleSheaf Ej)).presheaf.map
        (homOfLE le_top).op
        (pullbackGlobalSections I₂.subschemeι (modulesInvertibleSheaf Ej) (canonicalSection Ej)) =
      y • (show Γ((Scheme.Modules.pullback I₂.subschemeι).obj (modulesInvertibleSheaf Ej),
        I₂.subschemeι ⁻¹ᵁ Va) from Ga.val))
    (hGb : ((Scheme.Modules.pullback I₂.subschemeι).obj (modulesInvertibleSheaf Ej)).presheaf.map
        (homOfLE le_top).op
        (pullbackGlobalSections I₂.subschemeι (modulesInvertibleSheaf Ej) (canonicalSection Ej)) =
      x • (show Γ((Scheme.Modules.pullback I₂.subschemeι).obj (modulesInvertibleSheaf Ej),
        I₂.subschemeι ⁻¹ᵁ Vb) from Gb.val))
    (g : projectiveLine K ⟶ Ej.subscheme)
    (e0 : Polynomial K ≃+* Γ(Ej.subscheme, Ej.subschemeι ⁻¹ᵁ Va))
    (e1 : Polynomial K ≃+* Γ(Ej.subscheme, Ej.subschemeι ⁻¹ᵁ Vb))
    (hg0c : projectiveLineXChart K ≫ g = chartMap hU0 e0)
    (hg1c : projectiveLineYChart K ≫ g = chartMap hU1 e1)
    (c : K) (hc : c ≠ 0) (n : ℤ)
    (u : (Γ(I₂.subscheme, I₂.subschemeι ⁻¹ᵁ (Va ⊓ Vb)))ˣ)
    (hu2 : (I₂.subscheme.presheaf.map (homOfLE (Scheme.Hom.preimage_mono _
        (inf_le_right : Va ⊓ Vb ≤ Vb))).op) x =
      sigmaSub sY I₂ (Va ⊓ Vb) c * ((u ^ n : (Γ(I₂.subscheme, I₂.subschemeι ⁻¹ᵁ (Va ⊓ Vb)))ˣ) :
        Γ(I₂.subscheme, I₂.subschemeι ⁻¹ᵁ (Va ⊓ Vb))) *
        (I₂.subscheme.presheaf.map (homOfLE (Scheme.Hom.preimage_mono _
          (inf_le_left : Va ⊓ Vb ≤ Va))).op) y)
    (hann : ∀ z : Γ(I₂.subscheme, I₂.subschemeι ⁻¹ᵁ (Va ⊓ Vb)),
      z * (I₂.subscheme.presheaf.map (homOfLE (Scheme.Hom.preimage_mono _
          (inf_le_left : Va ⊓ Vb ≤ Va))).op) y = 0 → inclSections h₂₁ (Va ⊓ Vb) z = 0)
    (huE : (Units.map (inclSections (h₂₁.trans h₁E) (Va ⊓ Vb)).toMonoidHom u :
        Γ(Ej.subscheme, Ej.subschemeι ⁻¹ᵁ (Va ⊓ Vb))) =
      (Ej.subscheme.presheaf.map (homOfLE (Scheme.Hom.preimage_mono Ej.subschemeι
        (inf_le_left : Va ⊓ Vb ≤ Va))).op).hom (e0 Polynomial.X)) :
    Nonempty ((Scheme.Modules.pullback ((projectiveLineIsoProj K).inv ≫ g)).obj
        ((Scheme.Modules.pullback Ej.subschemeι).obj (invertibleSheaf' Ej : Y.Modules)) ≅
      ProjectiveSpectrum.Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin 2) K) (-n)) := by
  let h₂E : I₂ ≤ Ej := h₂₁.trans h₁E
  let M : Y.Modules := modulesInvertibleSheaf Ej
  let M₁ := (Scheme.Modules.pullback I₂.subschemeι).obj M
  let ι := Scheme.IdealSheafData.inclusion h₂E
  have hpre : ∀ A : Y.Opens, ι ⁻¹ᵁ (I₂.subschemeι ⁻¹ᵁ A) = Ej.subschemeι ⁻¹ᵁ A := fun A => by
    rw [← Scheme.Hom.comp_preimage, Scheme.IdealSheafData.inclusion_subschemeι]
  let uE : (Γ(Ej.subscheme, Ej.subschemeι ⁻¹ᵁ (Va ⊓ Vb)))ˣ :=
    Units.map (inclSections h₂E (Va ⊓ Vb)).toMonoidHom u
  obtain ⟨Ca, Cb, hCab⟩ := exists_pullback_generators ι M₁ inferInstance
    (I₂.subschemeι ⁻¹ᵁ Va) (I₂.subschemeι ⁻¹ᵁ Vb) Ga Gb (Ej.subschemeι ⁻¹ᵁ Va) (Ej.subschemeι ⁻¹ᵁ Vb)
    (le_of_eq (hpre Va).symm) (le_of_eq (hpre Vb).symm)
  have hA := coef_restrict M₁ (Scheme.Hom.preimage_mono I₂.subschemeι
    (inf_le_left : Va ⊓ Vb ≤ Va)) _ y Ga hGa
  have hB := coef_restrict M₁ (Scheme.Hom.preimage_mono I₂.subschemeι
    (inf_le_right : Va ⊓ Vb ≤ Vb)) _ x Gb hGb
  have hratZ := ratio_incl sY h₂₁ h₁E M₁ (Va ⊓ Vb)
    (generatorRestrict M₁ (Scheme.Hom.preimage_mono I₂.subschemeι (inf_le_left : Va ⊓ Vb ≤ Va)) Ga)
    (generatorRestrict M₁ (Scheme.Hom.preimage_mono I₂.subschemeι (inf_le_right : Va ⊓ Vb ≤ Vb)) Gb)
    _ _ (hA.symm.trans hB) c u n hu2 hann
  have hrel := (congrArg Units.val hCab).trans hratZ
  have hM : IsInvertible I₂.subscheme.presheaf (structureSheafRing I₂.subscheme.toRingedSpace).property M₁ :=
    inferInstance
  have hL' : IsInvertible Ej.subscheme.presheaf (structureSheafRing Ej.subscheme.toRingedSpace).property
      ((modulePullback ι.toLRSHom.toShHom).obj M₁) :=
    @Stacks.RingedSpace.isInvertible_modulePullback _ _ ι.toLRSHom.toShHom M₁ hM
  obtain ⟨e⟩ := final_iso_core2 sY Ej ((modulePullback ι.toLRSHom.toShHom).obj M₁) hL' Va Vb Ca Cb g
    hU0 hU1 e0 e1 hg0c hg1c c hc n uE huE hrel
  let isoC : (Scheme.Modules.pullback Ej.subschemeι).obj (invertibleSheaf' Ej : Y.Modules) ≅
      (Scheme.Modules.pullback ι).obj M₁ :=
    ((Scheme.Modules.pullbackCongr (Scheme.IdealSheafData.inclusion_subschemeι h₂E).symm).app
      (invertibleSheaf' Ej : Y.Modules)) ≪≫
      ((Scheme.Modules.pullbackComp ι I₂.subschemeι).app (invertibleSheaf' Ej : Y.Modules)).symm
  exact ⟨((Scheme.Modules.pullback ((projectiveLineIsoProj K).inv ≫ g)).mapIso isoC) ≪≫ e⟩

end

open MMP.Resolution.Bridges MMP.Mori in
private theorem pullback_invertibleSheaf_iso_twist
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 2 sX]
    [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]
    {r : ℕ} (hr : 0 < r) (E : Fin r → PrimeDivisor X) (b : Fin r → ℤ)
    (hinj : Function.Injective E)
    (hrat : ∀ i, IsSmoothRationalCurve sX (E i).idealSheaf)
    (hself : ∀ i, IsIntersectionNumber sX (Finsupp.single (E i) 1) (E i).idealSheaf (-(b i)))
    (hadj : ∀ i j : Fin r, i.val + 1 = j.val →
      IsIntersectionNumber sX (Finsupp.single (E i) 1) (E j).idealSheaf 1)
    (hfar : ∀ i j : Fin r, i.val + 1 < j.val → Disjoint (E i).support (E j).support)
    (pL pR : X) (hpLR : pL ≠ pR)
    (hpL : pL ∈ (E ⟨0, hr⟩).support) (hpL' : ∀ i, i ≠ ⟨0, hr⟩ → pL ∉ (E i).support)
    (hpR : pR ∈ (E ⟨r - 1, by omega⟩).support)
    (hpR' : ∀ i, i ≠ ⟨r - 1, by omega⟩ → pR ∉ (E i).support)
    (ZL ZR : ℕ → X.IdealSheafData)
    (hZL : ∀ n, (∏ i, (E i).idealSheaf) ^ (n + 1) ≤ ZL n)
    (hZR : ∀ n, (∏ i, (E i).idealSheaf) ^ (n + 1) ≤ ZR n)
    (hZL_succ : ∀ n, ZL n = ZL (n + 1) ⊔ (∏ i, (E i).idealSheaf) ^ (n + 1))
    (hZR_succ : ∀ n, ZR n = ZR (n + 1) ⊔ (∏ i, (E i).idealSheaf) ^ (n + 1))
    (hZL_zero : ((ZL 0).support : Set X) = {pL}) (hZR_zero : ((ZR 0).support : Set X) = {pR})
    (hZL_curvilinear : ∀ n, ∃ e : (ZL n).subscheme ≅
      Spec (.of (Polynomial K ⧸ Ideal.span {(Polynomial.X : Polynomial K) ^ (n + 1)})),
      e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K _)) = (ZL n).subschemeι ≫ sX)
    (hZR_curvilinear : ∀ n, ∃ e : (ZR n).subscheme ≅
      Spec (.of (Polynomial K ⧸ Ideal.span {(Polynomial.X : Polynomial K) ^ (n + 1)})),
      e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K _)) = (ZR n).subschemeι ≫ sX) :
    let I := ∏ i, (E i).idealSheaf
    -- the `(n+1)`-st thickening `(n+1)E` and the trace on it of an open of `X`
    let S : ℕ → Scheme.{u} := fun n => (I ^ (n + 1)).subscheme
    let tr : ∀ n, X.Opens → (S n).Opens := fun n V => (I ^ (n + 1)).subschemeι ⁻¹ᵁ V
    -- the constants `K → Γ((n+1)E, U)`
    let σ : ∀ n (U : (S n).Opens), K →+* Γ(S n, U) := fun n U =>
      ((Scheme.ΓSpecIso (.of K)).inv ≫
        ((I ^ (n + 1)).subschemeι ≫ sX).appLE ⊤ U le_top).hom
    -- the restriction `(n+2)E → (n+1)E`
    let ρ : ∀ n (V : X.Opens), Γ(S (n + 1), tr (n + 1) V) → Γ(S n, tr n V) := fun n V =>
      ((Scheme.IdealSheafData.inclusion (pow_le_pow_right_of_le_one' le_top
          (Nat.le_succ (n + 1)) : I ^ (n + 1 + 1) ≤ I ^ (n + 1))).appLE (tr (n + 1) V) (tr n V)
        (by
          simp only [tr, ← Scheme.Hom.comp_preimage,
            Scheme.IdealSheafData.inclusion_subschemeι, le_refl])).hom
    -- restriction to a smaller open of `X`
    let res : ∀ n (V W : X.Opens), W ≤ V → Γ(S n, tr n V) → Γ(S n, tr n W) :=
      fun n _ _ h => ((S n).presheaf.map (homOfLE (Scheme.Hom.preimage_mono _ h)).op).hom
    -- the exceptional ideal of chart `j`: `(y)`, `(x y)` or `(x)`
    let J : Fin (r + 1) → Ideal (MvPolynomial (Fin 2) K) := fun j =>
      if j = 0 then Ideal.span {MvPolynomial.X 1}
      else if j = Fin.last r then Ideal.span {MvPolynomial.X 0}
      else Ideal.span {MvPolynomial.X 0 * MvPolynomial.X 1}
    ∀ (V : Fin (r + 1) → X.Opens) (x y : ∀ j n, Γ(S n, tr n (V j))),
      (((I.support : Set X) ⊆ ⋃ j, (V j : Set X)) ∧
      (pL ∈ V 0 ∧ pR ∈ V (Fin.last r) ∧ (RingHom.ker ((Scheme.IdealSheafData.inclusion (hZL 0)).app (tr 0 (V 0))).hom =
            Ideal.span {(fun j => x j 0) 0} ∧
          RingHom.ker ((Scheme.IdealSheafData.inclusion (hZR 0)).app
            (tr 0 (V (Fin.last r)))).hom = Ideal.span {(fun j => y j 0) (Fin.last r)})) ∧
      (∀ j, IsAffineOpen (tr 0 (V j)) ∧
      Function.Surjective (MvPolynomial.eval₂Hom (σ 0 (tr 0 (V j))) ![(fun j => x j 0) j, (fun j => y j 0) j]) ∧
      RingHom.ker (MvPolynomial.eval₂Hom (σ 0 (tr 0 (V j))) ![(fun j => x j 0) j, (fun j => y j 0) j]) = J j ^ (0 + 1)) ∧
      (∀ j : Fin r, ((V j.castSucc ⊓ V j.succ : X.Opens) : Set X) ∩ I.support ⊆ (E j).support) ∧ (∀ j : Fin r, tr 0 (V j.castSucc ⊓ V j.succ) = (S 0).basicOpen ((fun j => x j 0) j.castSucc) ∧
        tr 0 (V j.castSucc ⊓ V j.succ) = (S 0).basicOpen ((fun j => y j 0) j.succ)) ∧ (∀ j k : Fin (r + 1), j.val + 2 ≤ k.val →
      ((V j ⊓ V k : X.Opens) : Set X) ∩ I.support = ∅) ∧ (∀ j : Fin r, ∃ d : K, d ≠ 0 ∧
        res 0 (V j.succ) (V j.castSucc ⊓ V j.succ) inf_le_right ((fun j => y j 0) j.succ) *
          res 0 (V j.castSucc) (V j.castSucc ⊓ V j.succ) inf_le_left ((fun j => x j 0) j.castSucc) = σ 0 (tr 0 (V j.castSucc ⊓ V j.succ)) d) ∧
      LocalEquations E V (fun j => x j 0) (fun j => y j 0)) →
      (∀ n, LevelEq E V n (fun j => x j n) (fun j => y j n)) →
      (∀ j n, ρ n (V j) (x j (n + 1)) = x j n ∧ ρ n (V j) (y j (n + 1)) = y j n) →
      (∀ j n, IsAffineOpen (tr n (V j)) ∧
      Function.Surjective (MvPolynomial.eval₂Hom (σ n (tr n (V j))) ![x j n, y j n]) ∧
      RingHom.ker (MvPolynomial.eval₂Hom (σ n (tr n (V j))) ![x j n, y j n]) = J j ^ (n + 1)) → (∀ j : Fin r, ∀ n, tr n (V j.castSucc ⊓ V j.succ) = (S n).basicOpen (x j.castSucc n) ∧
        tr n (V j.castSucc ⊓ V j.succ) = (S n).basicOpen (y j.succ n)) →
      ∀ (j : Fin r) (c : K) (n : ℤ) (u : (Γ(S 1, tr 1 (V j.castSucc ⊓ V j.succ)))ˣ), c ≠ 0 →
        (u : Γ(S 1, tr 1 (V j.castSucc ⊓ V j.succ))) =
            res 1 (V j.castSucc) (V j.castSucc ⊓ V j.succ) inf_le_left (x j.castSucc 1) ∧
          res 1 (V j.succ) (V j.castSucc ⊓ V j.succ) inf_le_right (x j.succ 1) =
            σ 1 (tr 1 (V j.castSucc ⊓ V j.succ)) c * ↑(u ^ n) *
              res 1 (V j.castSucc) (V j.castSucc ⊓ V j.succ) inf_le_left (y j.castSucc 1) →
      (∀ z : Γ(S 1, tr 1 (V j.castSucc ⊓ V j.succ)),
        z * res 1 (V j.castSucc) (V j.castSucc ⊓ V j.succ) inf_le_left (y j.castSucc 1) = 0 →
          ρ 0 (V j.castSucc ⊓ V j.succ) z = 0) →
      ∃ ε : projectiveLineProj K ≅ (E j).idealSheaf.subscheme,
        ε.hom ≫ (E j).idealSheaf.subschemeι ≫ sX =
          Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff K 1 ∧
        Nonempty ((Scheme.Modules.pullback ε.hom).obj
            ((Scheme.Modules.pullback (E j).idealSheaf.subschemeι).obj
              (Stacks.Divisors.invertibleSheaf' (E j).idealSheaf : X.Modules)) ≅
          ProjectiveSpectrum.Proj.twistingSheaf
            (MvPolynomial.homogeneousSubmodule (Fin 2) K) (-n)) := by
  intro I S tr σ ρ res J V x y hP hlev hcomp hchart hov j c n u hc ⟨hu1, hu2⟩ hann
  obtain ⟨hcovI, ⟨hpL0, hpR0, hker⟩, hch, hovsup, hbas, hfar', hd0, hLE⟩ := hP
  obtain ⟨hsupp, -⟩ := hLE
  obtain ⟨d, hd, hxy⟩ := hd0 j
  have hIE : I ^ (0 + 1) ≤ (E j).idealSheaf := pow_le_divisor E 0 j
  have hρ0 : I ^ (0 + 1 + 1) ≤ I ^ (0 + 1) := pow_le_pow_right_of_le_one' le_top (Nat.le_succ (0 + 1))
  have hIE₂ : I ^ (1 + 1) ≤ (E j).idealSheaf := hρ0.trans hIE
  obtain ⟨g, hU0, hU1, e0, e1, hgiso, hgc, hg0c, hg1c, he0X, he1X, he0c, he1c⟩ :=
    exists_epsilon_data' sX (I ^ (0 + 1)) (E j).idealSheaf hIE (V j.castSucc) (V j.succ)
      (hch j.castSucc).1 (hch j.succ).1
      (x j.castSucc 0) (y j.castSucc 0) (x j.succ 0) (y j.succ 0)
      (hch j.castSucc).2.1
      (by rw [(hch j.castSucc).2.2]; exact J_castSucc_le j)
      (hch j.succ).2.1
      (by rw [(hch j.succ).2.2]; exact J_succ_le j)
      ((hlev 0) j).1 ((hlev 0) j).2 (hbas j).1 (hbas j).2 d hd hxy (hsupp j)
  have hYreg := ((isRegular_iff_regular_stalks X).1
    (isRegular_of_isSmoothScheme sX (smoothScheme_of_smooth sX))).2
  haveI hcart : Stacks.Divisors.IsEffectiveCartierDivisor (E j).idealSheaf :=
    PrimeDivisor.isEffectiveCartierDivisor_idealSheaf
      (fun x => by
        have := hYreg x
        exact IsRegularLocalRing.uniqueFactorizationMonoid _) (E j)
  -- generators of the pulled back line bundle on the second thickening, over the two charts
  obtain ⟨Ga, hGa⟩ := exists_chart_gen sX (E j).idealSheaf (I₁ := I ^ (0 + 1)) (I₂ := I ^ (1 + 1))
    hρ0 hIE (V j.castSucc) (isAffineOpen_tr_pow I 1 _ (hch j.castSucc).1)
    (x j.castSucc 1) (y j.castSucc 1) (x j.castSucc 0) (y j.castSucc 0)
    (hcomp j.castSucc 0).1 (hcomp j.castSucc 0).2 (hchart j.castSucc 1).2.1
    (hchart j.castSucc 1).2.2
    (by rw [(hch j.castSucc).2.2, zero_add, pow_one])
    (J_castSucc_cases j |>.elim Or.inl fun h => Or.inr (Or.inr h)) 1 0 (by decide)
    (J_castSucc_cases j)
    _ (MvPolynomial.eval₂Hom_X' _ _ _) ((hlev 1) j).1
  obtain ⟨Gb, hGb⟩ := exists_chart_gen sX (E j).idealSheaf (I₁ := I ^ (0 + 1)) (I₂ := I ^ (1 + 1))
    hρ0 hIE (V j.succ) (isAffineOpen_tr_pow I 1 _ (hch j.succ).1)
    (x j.succ 1) (y j.succ 1) (x j.succ 0) (y j.succ 0)
    (hcomp j.succ 0).1 (hcomp j.succ 0).2 (hchart j.succ 1).2.1
    (hchart j.succ 1).2.2
    (by rw [(hch j.succ).2.2, zero_add, pow_one])
    (J_succ_cases j |>.elim (fun h => Or.inr (Or.inl h)) fun h => Or.inr (Or.inr (by rw [mul_comm]; exact h))) 0 1 (by decide)
    (J_succ_cases j)
    _ (MvPolynomial.eval₂Hom_X' _ _ _) ((hlev 1) j).2
  have h1 : inclSections hIE₂ (V j.castSucc) (x j.castSucc 1) = e0 Polynomial.X := by
    rw [he0X]
    have := incl_trans hρ0 hIE (V j.castSucc) (x j.castSucc 1)
    refine this.trans ?_
    have h2 : inclSections hρ0 (V j.castSucc) (x j.castSucc 1) = x j.castSucc 0 :=
      (hcomp j.castSucc 0).1
    rw [h2]
  have huE : (Units.map (inclSections (hρ0.trans hIE) (V j.castSucc ⊓ V j.succ)).toMonoidHom
      (u : (Γ(S 1, tr 1 (V j.castSucc ⊓ V j.succ)))ˣ) :
        Γ((E j).idealSheaf.subscheme, (E j).idealSheaf.subschemeι ⁻¹ᵁ (V j.castSucc ⊓ V j.succ))) =
      ((E j).idealSheaf.subscheme.presheaf.map (homOfLE (Scheme.Hom.preimage_mono
        (E j).idealSheaf.subschemeι (inf_le_left : V j.castSucc ⊓ V j.succ ≤ V j.castSucc))).op).hom
        (e0 Polynomial.X) := by
    have h3 := inclSections_restrict hIE₂ (inf_le_left : V j.castSucc ⊓ V j.succ ≤ V j.castSucc)
      (x j.castSucc 1)
    rw [h1] at h3
    change (inclSections hIE₂ (V j.castSucc ⊓ V j.succ)) (u : Γ(S 1, tr 1 (V j.castSucc ⊓ V j.succ))) = _
    rw [hu1]
    exact h3.symm
  haveI := hgiso
  refine ⟨(projectiveLineIsoProj K).symm ≪≫ asIso g, ?_, ?_⟩
  · simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc, hgc]
    rw [← projectiveLineIsoProj_hom_comp_projToSpecCoeff, Iso.inv_hom_id_assoc]
  · exact d2_final sX (E j).idealSheaf hρ0 hIE (V j.castSucc) (V j.succ) hU0 hU1 Ga Gb
      (y j.castSucc 1) (x j.succ 1) hGa hGb g e0 e1 hg0c hg1c c hc n u hu2 hann huE

/-- kernel of the comparison of sections is the section-ideal of the pulled back ideal sheaf -/
private theorem ker_inclSections_eq_comap {Y : Scheme.{u}} {I₂ D : Y.IdealSheafData} (h : I₂ ≤ D)
    (U : Y.Opens) (hU : IsAffineOpen (I₂.subschemeι ⁻¹ᵁ U)) :
    RingHom.ker (inclSections h U) = (D.comap I₂.subschemeι).ideal ⟨_, hU⟩ := by
  rw [ker_inclSections_eq_ker_app, comap_eq_ker_inclusion D I₂ h, Scheme.Hom.ker_apply]

private theorem ker_inclSections_pow {Y : Scheme.{u}} {I₂ D : Y.IdealSheafData} {k : ℕ} (h : I₂ ≤ D ^ k)
    (U : Y.Opens) (hU : IsAffineOpen (I₂.subschemeι ⁻¹ᵁ U)) :
    RingHom.ker (inclSections h U) = ((D.comap I₂.subschemeι).ideal ⟨_, hU⟩) ^ k := by
  rw [ker_inclSections_eq_comap h U hU, Stacks.IdealSheaf.comap_pow]
  rfl

private theorem ideal_prod_apply {Z : Scheme.{u}} {ι : Type*} (s : Finset ι) (C : ι → Z.IdealSheafData)
    (U : Z.affineOpens) : (∏ i ∈ s, C i).ideal U = ∏ i ∈ s, (C i).ideal U := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a t ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, ih]

/-- The graded induction step for a nilpotent thickening: if `A'` is a thickening of
`A = P/(q^(n+1))` whose kernel is generated by `h^(n+1)` with `h = φ' q` having `h^(n+2) = 0` and
`ann (h^(n+1)) = (h)`, then `P/(q^(n+2)) ≅ A'`. -/
private theorem chart_levels_nil {P A A' : Type*} [CommRing P] [CommRing A] [CommRing A']
    (φ : P →+* A) (φ' : P →+* A') (ρ : A' →+* A) (hρ : ρ.comp φ' = φ) (q : P) (n : ℕ)
    (hρs : Function.Surjective ρ) (hφs : Function.Surjective φ)
    (hφk : RingHom.ker φ = Ideal.span {q ^ (n + 1)})
    (hN : RingHom.ker ρ = Ideal.span {(φ' q) ^ (n + 1)})
    (hnil : (φ' q) ^ (n + 2) = 0)
    (hann : ∀ z : A', z * (φ' q) ^ (n + 1) = 0 → z ∈ Ideal.span {φ' q}) :
    Function.Surjective φ' ∧ RingHom.ker φ' = Ideal.span {q ^ (n + 2)} := by
  subst hρ
  set h := φ' q with hh
  have hqq : ∀ p, (ρ.comp φ') p = 0 ↔ p ∈ Ideal.span {q ^ (n + 1)} := fun p => by
    rw [← hφk, RingHom.mem_ker]
  have hsplit : ∀ a : A', ∃ p, a - φ' p ∈ RingHom.ker ρ := by
    intro a
    obtain ⟨p, hp⟩ := hφs (ρ a)
    refine ⟨p, ?_⟩
    rw [RingHom.mem_ker, map_sub]
    simp only [RingHom.comp_apply] at hp
    rw [hp, sub_self]
  have hpow : h ^ (2 * n + 2) = 0 := by
    have : 2 * n + 2 = (n + 2) + n := by omega
    rw [this, pow_add, hnil, zero_mul]
  have hker_mem : ∀ a : A', a ∈ RingHom.ker ρ → ∃ c, a = h ^ (n + 1) * c := by
    intro a ha
    rw [hN] at ha
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 ha
    exact ⟨c, by rw [← hc, mul_comm]⟩
  have hsurj : Function.Surjective φ' := by
    intro a
    obtain ⟨p, hp⟩ := hsplit a
    obtain ⟨c, hc⟩ := hker_mem _ hp
    obtain ⟨p2, hp2⟩ := hsplit c
    obtain ⟨e, he⟩ := hker_mem _ hp2
    refine ⟨p + q ^ (n + 1) * p2, ?_⟩
    have h1 : c = φ' p2 + h ^ (n + 1) * e := by rw [← he]; ring
    have h2 : h ^ (n + 1) * c = φ' (q ^ (n + 1) * p2) := by
      rw [h1, map_mul, map_pow, ← hh]
      have : h ^ (n + 1) * (h ^ (n + 1) * e) = 0 := by
        rw [← mul_assoc, ← pow_add]
        have : n + 1 + (n + 1) = 2 * n + 2 := by omega
        rw [this, hpow, zero_mul]
      rw [mul_add, this, add_zero]
    rw [map_add, ← h2, ← hc]; ring
  refine ⟨hsurj, le_antisymm ?_ ?_⟩
  · intro p hp
    rw [RingHom.mem_ker] at hp
    have hp0 : (ρ.comp φ') p = 0 := by rw [RingHom.comp_apply, hp, map_zero]
    obtain ⟨p1, hp1⟩ := Ideal.mem_span_singleton'.1 ((hqq p).1 hp0)
    -- p = p1 * q^(n+1)
    have hz : φ' p1 * h ^ (n + 1) = 0 := by
      rw [← hp, ← hp1, map_mul, map_pow, ← hh, mul_comm]
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (hann _ hz)
    -- φ' p1 = c * h
    obtain ⟨p2, hp2⟩ := hsplit c
    obtain ⟨e, he⟩ := hker_mem _ hp2
    have h1 : c = φ' p2 + h ^ (n + 1) * e := by rw [← he]; ring
    have h3 : φ' p1 = φ' (q * p2) := by
      rw [← hc, h1, map_mul, ← hh]
      have : h * (h ^ (n + 1) * e) = 0 := by
        rw [← mul_assoc, ← pow_succ']
        rw [show n + 1 + 1 = n + 2 by omega, hnil, zero_mul]
      rw [add_mul, mul_comm (φ' p2) h]
      have : (h ^ (n + 1) * e) * h = 0 := by rw [mul_comm, this]
      rw [this, add_zero]
    have h4 : (ρ.comp φ') (p1 - q * p2) = 0 := by
      rw [RingHom.comp_apply, map_sub, h3, sub_self, map_zero]
    have h5 : p1 - q * p2 ∈ Ideal.span {q ^ (n + 1)} := (hqq _).1 h4
    have h6 : p1 ∈ Ideal.span {q} := by
      have : p1 = (p1 - q * p2) + q * p2 := by ring
      rw [this]
      refine Ideal.add_mem _ ?_ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self q))
      exact Ideal.span_singleton_le_span_singleton.2 (dvd_pow_self q (Nat.succ_ne_zero n)) h5
    obtain ⟨p3, hp3⟩ := Ideal.mem_span_singleton'.1 h6
    refine Ideal.mem_span_singleton'.2 ⟨p3, ?_⟩
    rw [← hp1, ← hp3]; ring
  · rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, map_pow, ← hh, hnil]

private theorem ker_inclSections_prod_pow {Y : Scheme.{u}} {ι : Type*} [Fintype ι] (E : ι → Y.IdealSheafData)
    {I₂ : Y.IdealSheafData} (k : ℕ) (h : I₂ ≤ (∏ i, E i) ^ k)
    (U : Y.Opens) (hU : IsAffineOpen (I₂.subschemeι ⁻¹ᵁ U)) :
    RingHom.ker (inclSections h U) =
      (∏ i, ((E i).comap I₂.subschemeι).ideal ⟨_, hU⟩) ^ k := by
  rw [ker_inclSections_pow h U hU, Stacks.IdealSheaf.comap_finset_prod, ideal_prod_apply]

private theorem comap_self_eq_bot {Y : Scheme.{u}} (I₂ : Y.IdealSheafData) :
    I₂.comap I₂.subschemeι = ⊥ := by
  refine le_antisymm ?_ bot_le
  rw [← Scheme.IdealSheafData.le_map_iff_comap_le, Scheme.IdealSheafData.map_bot,
    Scheme.IdealSheafData.ker_subschemeι]

private theorem prod_pow_ideal_eq_bot {Y : Scheme.{u}} {ι : Type*} [Fintype ι] (E : ι → Y.IdealSheafData)
    (k : ℕ) (U : Y.Opens) (hU : IsAffineOpen (((∏ i, E i) ^ k).subschemeι ⁻¹ᵁ U)) :
    (∏ i, ((E i).comap ((∏ i, E i) ^ k).subschemeι).ideal ⟨_, hU⟩) ^ k = ⊥ := by
  rw [← ideal_prod_apply, ← Stacks.IdealSheaf.comap_finset_prod]
  have : ((∏ i ∈ Finset.univ, E i).comap ((∏ i, E i) ^ k).subschemeι).ideal ⟨_, hU⟩ ^ k =
      (((∏ i ∈ Finset.univ, E i).comap ((∏ i, E i) ^ k).subschemeι) ^ k).ideal ⟨_, hU⟩ := rfl
  rw [this, ← Stacks.IdealSheaf.comap_pow, comap_self_eq_bot]
  rfl

private theorem preimage_eq_bot_of_disjoint {Y : Scheme.{u}} (Z : Y.IdealSheafData) (V : Y.Opens)
    (h : ∀ y ∈ V, y ∉ (Z.support : Set Y)) : Z.subschemeι ⁻¹ᵁ V = ⊥ := by
  refine eq_bot_iff.2 fun s hs => ?_
  exfalso
  have h1 : Z.subschemeι s ∈ (V : Set Y) := hs
  refine h _ h1 ?_
  rw [← Z.range_subschemeι]
  exact ⟨s, rfl⟩

private theorem ker_inclSections_eq_top {Y : Scheme.{u}} {I Ej : Y.IdealSheafData} (h : I ≤ Ej)
    (U : Y.Opens) (hU : Ej.subschemeι ⁻¹ᵁ U = ⊥) :
    RingHom.ker (inclSections h U) = ⊤ := by
  haveI : Subsingleton Γ(Ej.subscheme, Ej.subschemeι ⁻¹ᵁ U) := by rw [hU]; infer_instance
  rw [Ideal.eq_top_iff_one, RingHom.mem_ker]
  exact Subsingleton.elim _ _

section LocalAnn

open Stacks.Divisors

private theorem local_ann {Y : Scheme.{u}} (D Z : Y.IdealSheafData) (n : ℕ) (hZ : Z = D ^ (n + 2))
    (hD2 : Z ≤ D) (V : Y.Opens)
    (hV : IsAffineOpen (Z.subschemeι ⁻¹ᵁ V))
    (h : Γ(Z.subscheme, Z.subschemeι ⁻¹ᵁ V))
    (hh : RingHom.ker (inclSections hD2 V) = Ideal.span {h})
    (W : Y.Opens) (hW : IsAffineOpen W) (hWV : W ≤ V)
    (f : Γ(Y, W)) (hf : IsRegular f) (hfD : D.ideal ⟨W, hW⟩ = Ideal.span {f})
    (z : Γ(Z.subscheme, Z.subschemeι ⁻¹ᵁ V))
    (hz : z * h ^ (n + 1) = 0) :
    inclSections hD2 W ((Z.subscheme.presheaf.map
      (homOfLE (Scheme.Hom.preimage_mono _ hWV)).op).hom z) = 0 := by
  have hO : IsAffineOpen (Z.subschemeι ⁻¹ᵁ W) := hW.preimage Z.subschemeι
  have hker1 : RingHom.ker (inclSections hD2 W) = (D.comap Z.subschemeι).ideal ⟨_, hO⟩ :=
    ker_inclSections_eq_comap hD2 W hO
  have hker0 : (D.comap Z.subschemeι).ideal ⟨_, hV⟩ = Ideal.span {h} := by
    rw [← ker_inclSections_eq_comap hD2 V hV, hh]
  have hker2 : (D.comap Z.subschemeι).ideal ⟨_, hO⟩ = Ideal.map (Z.subscheme.presheaf.map
      (homOfLE (Scheme.Hom.preimage_mono _ hWV)).op).hom (Ideal.span {h}) := by
    rw [← hker0]
    exact ((D.comap Z.subschemeι).map_ideal (U := ⟨_, hO⟩) (V := ⟨_, hV⟩)
      (Scheme.Hom.preimage_mono _ hWV)).symm
  have hker3 : (D.comap Z.subschemeι).ideal ⟨_, hO⟩ =
      Ideal.map (Z.subschemeι.appLE W _ le_rfl).hom (Ideal.span {f}) := by
    rw [← hfD]
    exact Stacks.IdealSheaf.ideal_comap_appLE D Z.subschemeι ⟨W, hW⟩ ⟨_, hO⟩ le_rfl
  rw [Ideal.map_span, Set.image_singleton] at hker2 hker3
  generalize hres : (Z.subscheme.presheaf.map
      (homOfLE (Scheme.Hom.preimage_mono _ hWV)).op).hom = res at *
  generalize hq : (Z.subschemeι.appLE W _ le_rfl).hom = q at *
  have hqf : q f ∈ Ideal.span {res h} := by
    rw [← hker2, hker3]; exact Ideal.mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hqf
  have e : q = (Z.subschemeι.app W).hom := by
    rw [← hq, Scheme.Hom.appLE_eq_app]
  have hqs : Function.Surjective q := by
    rw [e]; exact Z.subschemeι_app_surjective ⟨W, hW⟩
  have hqk : RingHom.ker q = Ideal.span {f} ^ (n + 2) := by
    rw [e, Z.ker_subschemeι_app ⟨W, hW⟩, hZ, ← hfD]
    rfl
  obtain ⟨t, ht⟩ := hqs (res z)
  have hz' : res z * (res h) ^ (n + 1) = 0 := by
    rw [← map_pow, ← map_mul, hz, map_zero]
  have h1 : t * f ^ (n + 1) ∈ RingHom.ker q := by
    rw [RingHom.mem_ker]
    calc q (t * f ^ (n + 1)) = q t * (q f) ^ (n + 1) := by rw [map_mul, map_pow]
      _ = res z * (c * res h) ^ (n + 1) := by rw [ht, hc]
      _ = c ^ (n + 1) * (res z * res h ^ (n + 1)) := by ring
      _ = 0 := by rw [hz', mul_zero]
  rw [hqk, Ideal.span_singleton_pow] at h1
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 h1
  have h2 : t = s * f := by
    refine (hf.pow (n + 1)).left ?_
    have : f ^ (n + 2) = f ^ (n + 1) * f := by ring
    rw [this] at hs
    calc f ^ (n + 1) * t = t * f ^ (n + 1) := by ring
      _ = s * (f ^ (n + 1) * f) := hs.symm
      _ = f ^ (n + 1) * (s * f) := by ring
  have h3 : res z ∈ Ideal.span {res h} := by
    rw [← ht, h2, map_mul, ← hc]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))
  rwa [← hker2, ← hker1] at h3

end LocalAnn

section LocalGen

open Stacks.Divisors

private theorem isRegular_restrict_of_le' {X : Scheme.{u}} {A W : X.affineOpens} (hAW : A ≤ W) {b : Γ(X, W.1)}
    (hb : IsRegular b) :
    IsRegular ((X.presheaf.map (homOfLE (show A.1 ≤ W.1 from hAW)).op).hom b) := by
  letI : Algebra Γ(X, W.1) Γ(X, A.1) :=
    (X.presheaf.map (homOfLE (show A.1 ≤ W.1 from hAW)).op).hom.toAlgebra
  have he : A.1 ≤ (𝟙 X) ⁻¹ᵁ W.1 := show A.1 ≤ W.1 from hAW
  have heq : (Scheme.Hom.appLE (𝟙 X) W.1 A.1 he).hom =
      (X.presheaf.map (homOfLE (show A.1 ≤ W.1 from hAW)).op).hom := rfl
  have hflat : Module.Flat Γ(X, W.1) Γ(X, A.1) := by
    rw [← RingHom.flat_algebraMap_iff, RingHom.algebraMap_toAlgebra, ← heq]
    exact AlgebraicGeometry.Flat.flat_appLE (𝟙 X) W.2 A.2 he
  have hsmul : IsSMulRegular Γ(X, A.1) b := Module.Flat.isSMulRegular_of_isRegular hb
  have hleft : IsLeftRegular
      ((X.presheaf.map (homOfLE (show A.1 ≤ W.1 from hAW)).op).hom b) := by
    intro p r hpr
    refine hsmul ?_
    simpa only [Algebra.smul_def, RingHom.algebraMap_toAlgebra] using hpr
  exact ⟨hleft, fun p r hpr => hleft (by simpa only [mul_comm] using hpr)⟩

private theorem exists_local_gen {Y : Scheme.{u}} (D : Y.IdealSheafData)
    [IsEffectiveCartierDivisor D] (V : Y.Opens) (y : Y) (hy : y ∈ V) :
    ∃ (W : Y.Opens) (hW : IsAffineOpen W), y ∈ W ∧ W ≤ V ∧
      ∃ f : Γ(Y, W), IsRegular f ∧ D.ideal ⟨W, hW⟩ = Ideal.span {f} := by
  obtain ⟨U, hU, hyU, f, hf, hfD⟩ :=
    exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor D inferInstance y
  obtain ⟨-, ⟨A, hA, rfl⟩, hyA, hAsub⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (show y ∈ (U : Set Y) ∩ (V : Set Y) from ⟨hyU, hy⟩) (U.isOpen.inter V.isOpen)
  have hAU : (⟨A, hA⟩ : Y.affineOpens) ≤ ⟨U, hU⟩ := fun z hz => (hAsub hz).1
  refine ⟨A, hA, hyA, fun z hz => (hAsub hz).2, (Y.presheaf.map (homOfLE hAU).op).hom f,
    isRegular_restrict_of_le' hAU hf, ?_⟩
  rw [← D.map_ideal (U := ⟨A, hA⟩) (V := ⟨U, hU⟩) hAU, hfD, Ideal.map_span, Set.image_singleton]

end LocalGen

section AnnPow

open Stacks.Divisors

private theorem ann_pow_mem_ker {Y : Scheme.{u}} (D Z : Y.IdealSheafData)
    [IsEffectiveCartierDivisor D] (n : ℕ) (hZ : Z = D ^ (n + 2)) (hD2 : Z ≤ D) (V : Y.Opens)
    (hV : IsAffineOpen (Z.subschemeι ⁻¹ᵁ V))
    (h : Γ(Z.subscheme, Z.subschemeι ⁻¹ᵁ V))
    (hh : RingHom.ker (inclSections hD2 V) = Ideal.span {h})
    (z : Γ(Z.subscheme, Z.subschemeι ⁻¹ᵁ V)) (hz : z * h ^ (n + 1) = 0) :
    inclSections hD2 V z = 0 := by
  have hloc : ∀ p : {p : D.subscheme // p ∈ D.subschemeι ⁻¹ᵁ V},
      ∃ (W : Y.Opens) (hW : IsAffineOpen W), D.subschemeι p.1 ∈ W ∧ W ≤ V ∧
        ∃ f : Γ(Y, W), IsRegular f ∧ D.ideal ⟨W, hW⟩ = Ideal.span {f} :=
    fun p => exists_local_gen D V _ p.2
  choose W hW hpW hWV f hf hfD using hloc
  refine TopCat.Sheaf.eq_of_locally_eq' (F := D.subscheme.sheaf)
    (U := fun p => D.subschemeι ⁻¹ᵁ W p) (D.subschemeι ⁻¹ᵁ V)
    (fun p => homOfLE (Scheme.Hom.preimage_mono _ (hWV p))) ?_ _ 0 ?_
  · intro p hp
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨p, hp⟩, hpW ⟨p, hp⟩⟩
  · intro p
    have := local_ann D Z n hZ hD2 V hV h hh (W p) (hW p) (hWV p) (f p) (hf p) (hfD p) z hz
    change (D.subscheme.presheaf.map (homOfLE (Scheme.Hom.preimage_mono _ (hWV p))).op).hom
      (inclSections hD2 V z) = (D.subscheme.presheaf.map
        (homOfLE (Scheme.Hom.preimage_mono _ (hWV p))).op).hom 0
    exact (inclSections_restrict hD2 (hWV p) z).trans (this.trans (map_zero _).symm)

end AnnPow

section ChartStepGeom

open Stacks.Divisors

private theorem isEffectiveCartierDivisor_prod {Y : Scheme.{u}} {ι : Type*} (s : Finset ι)
    (C : ι → Y.IdealSheafData) (h : ∀ i ∈ s, IsEffectiveCartierDivisor (C i)) :
    IsEffectiveCartierDivisor (∏ i ∈ s, C i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Scheme.IdealSheafData.one_eq_top]; infer_instance
  | insert a t ha ih =>
    rw [Finset.prod_insert ha]
    haveI := h a (Finset.mem_insert_self a t)
    haveI := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    infer_instance

/-- Geometric input of the graded lifting step on one chart. -/
private theorem chart_step_geom {Y : Scheme.{u}} {ι : Type*} [Fintype ι] (C : ι → Y.IdealSheafData)
    [hC : ∀ i, IsEffectiveCartierDivisor (C i)] (n : ℕ) (V : Y.Opens)
    (hV : IsAffineOpen (((∏ i, C i) ^ (n + 2)).subschemeι ⁻¹ᵁ V))
    (h : Γ(((∏ i, C i) ^ (n + 2)).subscheme, ((∏ i, C i) ^ (n + 2)).subschemeι ⁻¹ᵁ V))
    (hh : RingHom.ker (inclSections (pow_le_pow_right_of_le_one' le_top (by omega : 1 ≤ n + 2) :
        (∏ i, C i) ^ (n + 2) ≤ (∏ i, C i) ^ 1) V) = Ideal.span {h}) :
    (RingHom.ker (inclSections (pow_le_pow_right_of_le_one' le_top (by omega : n + 1 ≤ n + 2) :
        (∏ i, C i) ^ (n + 2) ≤ (∏ i, C i) ^ (n + 1)) V) = Ideal.span {h} ^ (n + 1)) ∧
    h ^ (n + 2) = 0 ∧
    (∀ z, z * h ^ (n + 1) = 0 → z ∈ Ideal.span {h}) := by
  haveI : IsEffectiveCartierDivisor (∏ i, C i) :=
    isEffectiveCartierDivisor_prod Finset.univ C fun i _ => hC i
  have hD2 : (∏ i, C i) ^ (n + 2) ≤ (∏ i, C i) ^ 1 :=
    pow_le_pow_right_of_le_one' le_top (by omega : 1 ≤ n + 2)
  have hk1 := ker_inclSections_prod_pow C 1 hD2 V hV
  have hk2 := ker_inclSections_prod_pow C (n + 1)
    (pow_le_pow_right_of_le_one' le_top (by omega : n + 1 ≤ n + 2)) V hV
  rw [hh, pow_one] at hk1
  refine ⟨?_, ?_, ?_⟩
  · rw [hk2, ← hk1]
  · have h0 := prod_pow_ideal_eq_bot C (n + 2) V hV
    rwa [← hk1, Ideal.span_singleton_pow, Ideal.span_singleton_eq_bot] at h0
  · intro z hz
    rw [← hh, RingHom.mem_ker]
    haveI : IsEffectiveCartierDivisor ((∏ i, C i) ^ 1) := inferInstance
    exact ann_pow_mem_ker ((∏ i, C i) ^ 1) _ n (by rw [pow_one]) hD2 V hV h hh z hz

end ChartStepGeom

/-- Any lift generates, once the kernel is inside the `(n+1)`-st power of the ideal and
square-zero. -/
private theorem span_lift_eq_of_nilsq {A A0 : Type*} [CommRing A] [CommRing A0] (ρ : A →+* A0)
    (hρs : Function.Surjective ρ) (𝔟 : Ideal A) (y : A0) (y' : A) (hy' : ρ y' = y)
    (hb : 𝔟 = (Ideal.span {y}).comap ρ) (n : ℕ) (hn : 1 ≤ n)
    (hN : RingHom.ker ρ ≤ 𝔟 ^ (n + 1)) (hN2 : (RingHom.ker ρ) ^ 2 = ⊥) :
    𝔟 = Ideal.span {y'} := by
  have h1 : 𝔟 ≤ Ideal.span {y'} ⊔ RingHom.ker ρ := by
    intro a ha
    rw [hb, Ideal.mem_comap, ← hy', Ideal.mem_span_singleton'] at ha
    obtain ⟨c, hc⟩ := ha
    obtain ⟨c', rfl⟩ := hρs c
    have : a - c' * y' ∈ RingHom.ker ρ := by
      rw [RingHom.mem_ker, map_sub, map_mul, hy', ← hy', hc, sub_self]
    have e : a = c' * y' + (a - c' * y') := by ring
    rw [e]
    exact Submodule.add_mem_sup (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self y')) this
  have h2 : 𝔟 ^ 2 ≤ Ideal.span {y'} := by
    calc 𝔟 ^ 2 ≤ (Ideal.span {y'} ⊔ RingHom.ker ρ) ^ 2 := Ideal.pow_right_mono h1 2
      _ ≤ Ideal.span {y'} := by
        rw [pow_two, Ideal.mul_le]
        intro a ha b hb
        obtain ⟨s1, hs1, n1, hn1, rfl⟩ := Submodule.mem_sup.1 ha
        obtain ⟨s2, hs2, n2, hn2, rfl⟩ := Submodule.mem_sup.1 hb
        have hnn : n1 * n2 = 0 := by
          rw [← Ideal.mem_bot, ← hN2, pow_two]
          exact Ideal.mul_mem_mul hn1 hn2
        have e : (s1 + n1) * (s2 + n2) = s1 * (s2 + n2) + n1 * s2 + n1 * n2 := by ring
        rw [e, hnn, add_zero]
        exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hs1) (Ideal.mul_mem_left _ _ hs2)
  apply le_antisymm
  · intro a ha
    rw [hb, Ideal.mem_comap, ← hy', Ideal.mem_span_singleton'] at ha
    obtain ⟨c, hc⟩ := ha
    obtain ⟨c', rfl⟩ := hρs c
    have hk : a - c' * y' ∈ RingHom.ker ρ := by
      rw [RingHom.mem_ker, map_sub, map_mul, hy', ← hy', hc, sub_self]
    have hk2 : a - c' * y' ∈ Ideal.span {y'} :=
      h2 ((pow_le_pow_right_of_le_one' (by simp) (by omega : 2 ≤ n + 1) : 𝔟 ^ (n + 1) ≤ 𝔟 ^ 2) (hN hk))
    have e : a = c' * y' + (a - c' * y') := by ring
    rw [e]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self y')) hk2
  · rw [Ideal.span_singleton_le_iff_mem, hb, Ideal.mem_comap, hy']
    exact Ideal.mem_span_singleton_self y

section LiftGen

/-- For `n ≥ 1`, any lift of a generator of the ideal of `E_i` at level `n` generates it at
level `n+1`. -/
private theorem lift_gen_pos {Y : Scheme.{u}} {ι : Type*} [Fintype ι] (C : ι → Y.IdealSheafData)
    (n : ℕ) (hn : 1 ≤ n) (V : Y.Opens)
    (hV : IsAffineOpen (((∏ i, C i) ^ (n + 2)).subschemeι ⁻¹ᵁ V)) (i : ι)
    (hCi : (∏ i, C i) ^ (n + 1 + 1) ≤ C i)
    (hCi' : (∏ i, C i) ^ (n + 1) ≤ C i)
    (y : Γ(((∏ i, C i) ^ (n + 1)).subscheme, ((∏ i, C i) ^ (n + 1)).subschemeι ⁻¹ᵁ V))
    (hy : RingHom.ker (inclSections hCi' V) = Ideal.span {y})
    (y' : Γ(((∏ i, C i) ^ (n + 2)).subscheme, ((∏ i, C i) ^ (n + 2)).subschemeι ⁻¹ᵁ V))
    (hy' : inclSections (pow_le_pow_right_of_le_one' le_top (by omega : n + 1 ≤ n + 2) :
        (∏ i, C i) ^ (n + 2) ≤ (∏ i, C i) ^ (n + 1)) V y' = y) :
    RingHom.ker (inclSections hCi V) = Ideal.span {y'} := by
  have hle : (∏ i, C i) ^ (n + 2) ≤ (∏ i, C i) ^ (n + 1) :=
    pow_le_pow_right_of_le_one' le_top (by omega : n + 1 ≤ n + 2)
  refine span_lift_eq_of_nilsq (inclSections hle V) (inclSections_surjective hle V hV)
    (RingHom.ker (inclSections hCi V)) y y' hy' ?_ n hn ?_ ?_
  · rw [← hy]
    ext a
    rw [RingHom.mem_ker, Ideal.mem_comap, RingHom.mem_ker]
    rw [show (n + 1 + 1) = n + 2 from rfl] at hCi
    have := incl_trans hle hCi' V a
    exact (by rw [this] : inclSections hCi V a = 0 ↔ _)
  · rw [ker_inclSections_prod_pow C (n + 1) hle V hV, ker_inclSections_eq_comap hCi V hV]
    refine Ideal.pow_right_mono ?_ (n + 1)
    classical
    rw [← Finset.mul_prod_erase Finset.univ (fun j => ((C j).comap ((∏ i, C i) ^ (n + 2)).subschemeι).ideal
      ⟨_, hV⟩) (Finset.mem_univ i)]
    exact Ideal.mul_le_left
  · rw [ker_inclSections_prod_pow C (n + 1) hle V hV, ← pow_mul]
    refine le_bot_iff.1 ?_
    rw [← prod_pow_ideal_eq_bot C (n + 2) V hV]
    exact Ideal.pow_le_pow_right (by omega)

end LiftGen

section UnitLemma

open MvPolynomial

private theorem sub_eval_mem_span_X {K : Type u} [Field K] (u : Fin 2) (a : MvPolynomial (Fin 2) K) :
    a - MvPolynomial.eval₂Hom (MvPolynomial.C : K →+* MvPolynomial (Fin 2) K)
      (fun i => if i = u then 0 else MvPolynomial.X i) a ∈ Ideal.span {(MvPolynomial.X u : MvPolynomial (Fin 2) K)} := by
  set ε := MvPolynomial.eval₂Hom (MvPolynomial.C : K →+* MvPolynomial (Fin 2) K)
      (fun i => if i = u then 0 else MvPolynomial.X i) with hε
  have h : (Ideal.Quotient.mk (Ideal.span {(MvPolynomial.X u : MvPolynomial (Fin 2) K)})).comp ε =
      Ideal.Quotient.mk (Ideal.span {(MvPolynomial.X u : MvPolynomial (Fin 2) K)}) := by
    refine MvPolynomial.ringHom_ext (fun k => ?_) (fun i => ?_)
    · simp [hε]
    · by_cases hi : i = u
      · subst hi
        simp only [RingHom.comp_apply, hε, MvPolynomial.eval₂Hom_X', ite_true, map_zero]
        symm
        exact (Ideal.Quotient.eq_zero_iff_mem).2 (Ideal.mem_span_singleton_self _)
      · simp [hε, hi]
  have := congrArg (fun f => f a) h
  simp only [RingHom.comp_apply] at this
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, this, sub_self]

private theorem unit_of_span_eq {K : Type u} [Field K] {A0 : Type u} [CommRing A0]
    (φ0 : MvPolynomial (Fin 2) K →+* A0) (hs : Function.Surjective φ0)
    {J : Ideal (MvPolynomial (Fin 2) K)} (hk : RingHom.ker φ0 = J) {v u : Fin 2} (huv : u ≠ v)
    (hJv : J = Ideal.span {X v} ∨ J = Ideal.span {X u * X v})
    (g : A0) (hg : Ideal.span {g} = Ideal.span {φ0 (X v)}) :
    ∃ w : A0ˣ, (w : A0) * g = φ0 (X v) := by
  have hXv : (X v : MvPolynomial (Fin 2) K) ≠ 0 := X_prime.ne_zero
  rcases hJv with rfl | rfl
  · have h0 : φ0 (X v) = 0 := by
      rw [← RingHom.mem_ker, hk]; exact Ideal.mem_span_singleton_self _
    rw [h0, Ideal.span_singleton_eq_bot.2 rfl, Ideal.span_singleton_eq_bot] at hg
    exact ⟨1, by rw [hg, h0, mul_zero]⟩
  · obtain ⟨p, rfl⟩ := hs g
    have h1 : φ0 (X v) ∈ Ideal.span {φ0 p} := hg ▸ Ideal.mem_span_singleton_self _
    have h2 : φ0 p ∈ Ideal.span {φ0 (X v)} := hg.symm ▸ Ideal.mem_span_singleton_self _
    obtain ⟨b0, hb0⟩ := Ideal.mem_span_singleton'.1 h1
    obtain ⟨a0, ha0⟩ := Ideal.mem_span_singleton'.1 h2
    obtain ⟨b', rfl⟩ := hs b0
    obtain ⟨a, rfl⟩ := hs a0
    have e1 : b' * p - X v ∈ Ideal.span {X u * X v} := by
      rw [← hk, RingHom.mem_ker, map_sub, map_mul, hb0, sub_self]
    have e2 : a * X v - p ∈ Ideal.span {X u * X v} := by
      rw [← hk, RingHom.mem_ker, map_sub, map_mul, ha0, sub_self]
    obtain ⟨s, hs'⟩ := Ideal.mem_span_singleton'.1 e1
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 e2
    have e3 : b' * a = 1 + X u * (s + b' * t) := by
      apply mul_right_cancel₀ hXv
      linear_combination (-1 : MvPolynomial (Fin 2) K) * hs' + (-b') * ht
    set ε := MvPolynomial.eval₂Hom (MvPolynomial.C : K →+* MvPolynomial (Fin 2) K)
      (fun i => if i = u then 0 else MvPolynomial.X i) with hε
    have hεu : ε (X u) = 0 := by simp [hε]
    have e4 : ε b' * ε a = 1 := by
      rw [← map_mul, e3, map_add, map_one, map_mul, hεu, zero_mul, add_zero]
    have hunit : IsUnit (ε a) := IsUnit.of_mul_eq_one (ε b') (by rw [mul_comm]; exact e4)
    obtain ⟨c, hc, hca⟩ := (MvPolynomial.isUnit_iff_eq_C_of_isReduced).1 hunit
    have e5 : a - C c ∈ Ideal.span {X u} := by
      rw [← hca]; exact sub_eval_mem_span_X u a
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 e5
    -- p ≡ C c * X v modulo J
    have e6 : p - C c * X v ∈ RingHom.ker φ0 := by
      rw [hk, Ideal.mem_span_singleton']
      refine ⟨d - t, ?_⟩
      have : a = C c + d * X u := by linear_combination -hd
      linear_combination (-1 : MvPolynomial (Fin 2) K) * ht + X v * hd
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at e6
    have hcu : IsUnit (φ0 (C c)) := hc.map (φ0.comp C)
    refine ⟨hcu.unit⁻¹, ?_⟩
    calc ((hcu.unit⁻¹ : A0ˣ) : A0) * φ0 p
        = ((hcu.unit⁻¹ : A0ˣ) : A0) * ((hcu.unit : A0) * φ0 (X v)) := by
          rw [e6, map_mul]; rfl
      _ = φ0 (X v) := by rw [← mul_assoc, Units.inv_mul, one_mul]

end UnitLemma

private theorem exists_unit_lift {A A0 : Type*} [CommRing A] [CommRing A0] (ρ : A →+* A0)
    (hρs : Function.Surjective ρ) (hnil : ∀ n ∈ RingHom.ker ρ, IsNilpotent n) (w : A0ˣ) :
    ∃ w' : Aˣ, ρ w' = w := by
  obtain ⟨a, ha⟩ := hρs (w : A0)
  obtain ⟨b, hb⟩ := hρs ((w⁻¹ : A0ˣ) : A0)
  have h1 : a * b - 1 ∈ RingHom.ker ρ := by
    rw [RingHom.mem_ker, map_sub, map_mul, ha, hb, Units.mul_inv, map_one, sub_self]
  have hu : IsUnit (a * b) := by
    have := (hnil _ h1).neg.isUnit_one_sub
    have e : (1 : A) - -(a * b - 1) = a * b := by ring
    rwa [e] at this
  exact ⟨(isUnit_of_mul_isUnit_left hu).unit, by rw [IsUnit.unit_spec, ha]⟩

private theorem prod_adjacent_eq {A : Type*} [CommRing A] {r : ℕ} (hr : 0 < r) (𝔞 : Fin r → Ideal A)
    (c : Fin (r + 1)) (x' y' : A)
    (h1 : ∀ i : Fin r, i.succ ≠ c → i.castSucc ≠ c → 𝔞 i = ⊤)
    (h2 : ∀ i : Fin r, i.succ = c → 𝔞 i = Ideal.span {x'})
    (h3 : ∀ i : Fin r, i.castSucc = c → 𝔞 i = Ideal.span {y'}) :
    ∏ i, 𝔞 i = Ideal.span {if c = 0 then y' else if c = Fin.last r then x' else x' * y'} := by
  classical
  by_cases hc0 : c = 0
  · subst hc0
    rw [if_pos rfl]
    have hne : ∀ i : Fin r, i ≠ ⟨0, hr⟩ → 𝔞 i = ⊤ := by
      intro i hi
      refine h1 i (Fin.succ_ne_zero i) ?_
      intro h
      apply hi
      ext
      have := congrArg Fin.val h
      simpa using this
    rw [Finset.prod_eq_single (⟨0, hr⟩ : Fin r) (fun i _ hi => by rw [Ideal.one_eq_top]; exact hne i hi) (by simp)]
    exact h3 _ rfl
  · by_cases hcl : c = Fin.last r
    · subst hcl
      rw [if_neg hc0, if_pos rfl]
      have hne : ∀ i : Fin r, i ≠ ⟨r - 1, by omega⟩ → 𝔞 i = ⊤ := by
        intro i hi
        refine h1 i ?_ (Fin.castSucc_lt_last i).ne
        intro h
        apply hi
        ext
        have := congrArg Fin.val h
        simp only [Fin.val_succ, Fin.val_last] at this
        simp only; omega
      rw [Finset.prod_eq_single (⟨r - 1, by omega⟩ : Fin r) (fun i _ hi => by rw [Ideal.one_eq_top]; exact hne i hi) (by simp)]
      exact h2 _ (by ext; simp; omega)
    · rw [if_neg hc0, if_neg hcl]
      have hc1 : 0 < c.val := by
        rcases Nat.eq_zero_or_pos c.val with h | h
        · exact absurd (Fin.ext h) hc0
        · exact h
      have hc2 : c.val < r := by
        have := c.isLt
        have h' : c.val ≠ r := fun h => hcl (Fin.ext (by simpa using h))
        omega
      let i1 : Fin r := ⟨c.val - 1, by omega⟩
      let i2 : Fin r := ⟨c.val, hc2⟩
      have hne : i1 ≠ i2 := by intro h; have := congrArg Fin.val h; simp [i1, i2] at this; omega
      rw [Finset.prod_eq_mul i1 i2 hne ?_ (by simp) (by simp)]
      · rw [h2 i1 (by ext; simp [i1]; omega), h3 i2 (by ext; simp [i2]), Ideal.span_singleton_mul_span_singleton]
      · intro i _ hi
        rw [Ideal.one_eq_top]
        refine h1 i ?_ ?_
        · intro h; apply hi.1; ext; have := congrArg Fin.val h; simp [i1] at this ⊢; omega
        · intro h; apply hi.2; ext; have := congrArg Fin.val h; simp [i2] at this ⊢; omega

section LiftGenZero

open Stacks.SheafOfModules Stacks.SheafOfModules.TensorStalkRingedSpace Stacks.Divisors

private theorem exists_ker_span {Y : Scheme.{u}} (D : Y.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D]
    {I₂ : Y.IdealSheafData} (h : I₂ ≤ D) (U : Y.Opens)
    (hU : IsAffineOpen (I₂.subschemeι ⁻¹ᵁ U))
    (G0 : GeneratorSections I₂.subscheme.toRingedSpace
      ((Scheme.Modules.pullback I₂.subschemeι).obj (Stacks.Divisors.modulesInvertibleSheaf D))
      (I₂.subschemeι ⁻¹ᵁ U)) :
    ∃ a : Γ(I₂.subscheme, I₂.subschemeι ⁻¹ᵁ U),
      RingHom.ker (inclSections h U) = Ideal.span {a} := by
  have hbij : Function.Bijective (fun r : Γ(I₂.subscheme, I₂.subschemeι ⁻¹ᵁ U) =>
      r • (show Γ((Scheme.Modules.pullback I₂.subschemeι).obj
          (Stacks.Divisors.modulesInvertibleSheaf D), I₂.subschemeι ⁻¹ᵁ U) from G0.val)) := by
    have h0 := generator_restrict_self (X := I₂.subscheme.toRingedSpace)
      ((Scheme.Modules.pullback I₂.subschemeι).obj (Stacks.Divisors.modulesInvertibleSheaf D))
      (I₂.subschemeι ⁻¹ᵁ U) G0
    have := G0.property (I₂.subschemeι ⁻¹ᵁ U) le_rfl
    rw [h0] at this
    exact this
  let M := (Scheme.Modules.pullback I₂.subschemeι).obj (Stacks.Divisors.modulesInvertibleSheaf D)
  let U' := I₂.subschemeι ⁻¹ᵁ U
  let χ₁ : Γ(M, U') := M.presheaf.map (homOfLE (le_top : U' ≤ ⊤)).op
    (pullbackGlobalSections I₂.subschemeι (Stacks.Divisors.modulesInvertibleSheaf D)
      (Stacks.Divisors.canonicalSection D))
  obtain ⟨a, ha⟩ := hbij.2 χ₁
  let e : Γ(M, U') ≃ₗ[Γ(I₂.subscheme, U')] Γ(I₂.subscheme, U') :=
    (LinearEquiv.ofBijective (LinearMap.toSpanSingleton Γ(I₂.subscheme, U') Γ(M, U')
      (show Γ(M, U') from G0.val)) (show Function.Bijective (LinearMap.toSpanSingleton Γ(I₂.subscheme, U') Γ(M, U')
        (show Γ(M, U') from G0.val)) from hbij)).symm
  have he : e χ₁ = a := by
    rw [LinearEquiv.symm_apply_eq]
    exact ha.symm
  have hk := ker_inclusion_app_eq_span D I₂ h ⟨U', hU⟩ e a he
  rw [← ker_inclSections_eq_ker_app] at hk
  exact ⟨a, hk⟩

private theorem lift_gen_zero {K : Type u} [Field K] {Y : Scheme.{u}} {ι : Type*} [Fintype ι]
    (C : ι → Y.IdealSheafData) [hC : ∀ i, Stacks.Divisors.IsEffectiveCartierDivisor (C i)]
    (V : Y.Opens)
    (hV1 : IsAffineOpen (((∏ i, C i) ^ (0 + 1 + 1)).subschemeι ⁻¹ᵁ V))
    (i : ι) (hCi : (∏ i, C i) ^ (0 + 1 + 1) ≤ C i) (hCi' : (∏ i, C i) ^ (0 + 1) ≤ C i)
    {J : Ideal (MvPolynomial (Fin 2) K)}
    (φ0 : MvPolynomial (Fin 2) K →+*
      Γ(((∏ i, C i) ^ (0 + 1)).subscheme, ((∏ i, C i) ^ (0 + 1)).subschemeι ⁻¹ᵁ V))
    (hs0 : Function.Surjective φ0) (hk0 : RingHom.ker φ0 = J)
    (hJ : J = Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 2) K)} ∨
      J = Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin 2) K)} ∨
      J = Ideal.span {(MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) K)})
    (v u : Fin 2) (huv : u ≠ v)
    (hJv : J = Ideal.span {(MvPolynomial.X v : MvPolynomial (Fin 2) K)} ∨
      J = Ideal.span {(MvPolynomial.X u * MvPolynomial.X v : MvPolynomial (Fin 2) K)})
    (y : Γ(((∏ i, C i) ^ (0 + 1)).subscheme, ((∏ i, C i) ^ (0 + 1)).subschemeι ⁻¹ᵁ V))
    (hy : φ0 (MvPolynomial.X v) = y)
    (hker : RingHom.ker (inclSections hCi' V) = Ideal.span {y}) :
    ∃ y' : Γ(((∏ i, C i) ^ (0 + 1 + 1)).subscheme, ((∏ i, C i) ^ (0 + 1 + 1)).subschemeι ⁻¹ᵁ V),
      inclSections (pow_le_pow_right_of_le_one' le_top (by omega : 0 + 1 ≤ 0 + 1 + 1) :
        (∏ i, C i) ^ (0 + 1 + 1) ≤ (∏ i, C i) ^ (0 + 1)) V y' = y ∧
      RingHom.ker (inclSections hCi V) = Ideal.span {y'} := by
  have hle : (∏ i, C i) ^ (0 + 1 + 1) ≤ (∏ i, C i) ^ (0 + 1) :=
    pow_le_pow_right_of_le_one' le_top (by omega : 0 + 1 ≤ 0 + 1 + 1)
  have hρs := inclSections_surjective hle V hV1
  have hN2 : (RingHom.ker (inclSections hle V)) ^ 2 = ⊥ := by
    rw [ker_inclSections_prod_pow C (0 + 1) hle V hV1, ← pow_mul]
    exact prod_pow_ideal_eq_bot C 2 V hV1
  have hfree : ∀ (M' : Type u) [AddCommGroup M'] [Module (Γ(((∏ i, C i) ^ (0 + 1 + 1)).subscheme,
      ((∏ i, C i) ^ (0 + 1 + 1)).subschemeι ⁻¹ᵁ V) ⧸ RingHom.ker (inclSections hle V)) M']
      [Module.Invertible (Γ(((∏ i, C i) ^ (0 + 1 + 1)).subscheme,
      ((∏ i, C i) ^ (0 + 1 + 1)).subschemeι ⁻¹ᵁ V) ⧸ RingHom.ker (inclSections hle V)) M'],
      Module.Free (Γ(((∏ i, C i) ^ (0 + 1 + 1)).subscheme,
      ((∏ i, C i) ^ (0 + 1 + 1)).subschemeι ⁻¹ᵁ V) ⧸ RingHom.ker (inclSections hle V)) M' := by
    intro M' _ _ _
    let e := RingHom.quotientKerEquivOfSurjective hρs
    refine free_of_invertible_chart ((e.symm : _ →+* _).comp φ0)
      (e.symm.surjective.comp hs0) (J := J) ?_ hJ M'
    rw [RingHom.ker_comp_of_injective _ e.symm.injective, hk0]
  obtain ⟨G0⟩ := nonempty_generatorSections_of_free_quot
    ((Scheme.Modules.pullback ((∏ i, C i) ^ (0 + 1 + 1)).subschemeι).obj
      (Stacks.Divisors.modulesInvertibleSheaf (C i)))
    hV1 (RingHom.ker (inclSections hle V)) ⟨2, hN2⟩ hfree
  obtain ⟨a, ha⟩ := exists_ker_span (C i) hCi V hV1 G0
  have hb : RingHom.ker (inclSections hCi V) = (Ideal.span {y}).comap (inclSections hle V) := by
    rw [← hker]
    ext z
    rw [RingHom.mem_ker, Ideal.mem_comap, RingHom.mem_ker]
    have := incl_trans hle hCi' V z
    rw [show (hle.trans hCi') = hCi from rfl] at this
    rw [this]
  have hg : Ideal.span {inclSections hle V a} = Ideal.span {φ0 (MvPolynomial.X v)} := by
    have e : Ideal.map (inclSections hle V) (Ideal.span {a}) = Ideal.span {inclSections hle V a} := by
      rw [Ideal.map_span, Set.image_singleton]
    rw [hy, ← e, ← ha, hb, Ideal.map_comap_of_surjective _ hρs]
  obtain ⟨w, hw⟩ := unit_of_span_eq φ0 hs0 hk0 huv hJv _ hg
  obtain ⟨w', hw'⟩ := exists_unit_lift (inclSections hle V) hρs (isNilpotent_of_sq_eq_bot hN2) w
  refine ⟨(w' : Γ(((∏ i, C i) ^ (0 + 1 + 1)).subscheme, ((∏ i, C i) ^ (0 + 1 + 1)).subschemeι ⁻¹ᵁ V)) * a, ?_, ?_⟩
  · rw [map_mul, hw', hw, hy]
  · rw [ha, Ideal.span_singleton_mul_left_unit w'.isUnit]

end LiftGenZero

section ChartSurjKer

open Stacks.Divisors

/-- The generator of the exceptional ideal of chart `c`. -/
private noncomputable def qchart (K : Type u) [Field K] (r : ℕ) (c : Fin (r + 1)) : MvPolynomial (Fin 2) K :=
  if c = 0 then MvPolynomial.X 1 else if c = Fin.last r then MvPolynomial.X 0
  else MvPolynomial.X 0 * MvPolynomial.X 1

private theorem chart_surj_ker {K : Type u} [Field K] {Y : Scheme.{u}} {r : ℕ} (hr : 0 < r)
    (C : Fin r → Y.IdealSheafData) [hC : ∀ i, IsEffectiveCartierDivisor (C i)] (n : ℕ)
    (c : Fin (r + 1)) (V : Y.Opens)
    (hV : IsAffineOpen (((∏ i, C i) ^ (n + 2)).subschemeι ⁻¹ᵁ V))
    (hdisj : ∀ k : Fin r, k.castSucc ≠ c → k.succ ≠ c → ∀ y ∈ V, y ∉ (C k).support)
    (hCi : ∀ i, (∏ i, C i) ^ (n + 2) ≤ C i)
    (φ : MvPolynomial (Fin 2) K →+*
      Γ(((∏ i, C i) ^ (n + 1)).subscheme, ((∏ i, C i) ^ (n + 1)).subschemeι ⁻¹ᵁ V))
    (φ' : MvPolynomial (Fin 2) K →+*
      Γ(((∏ i, C i) ^ (n + 2)).subscheme, ((∏ i, C i) ^ (n + 2)).subschemeι ⁻¹ᵁ V))
    (hρ : (inclSections (pow_le_pow_right_of_le_one' le_top (by omega : n + 1 ≤ n + 2) :
        (∏ i, C i) ^ (n + 2) ≤ (∏ i, C i) ^ (n + 1)) V).comp φ' = φ)
    (hφs : Function.Surjective φ)
    (hφk : RingHom.ker φ = Ideal.span {qchart K r c} ^ (n + 1))
    (x' y' : Γ(((∏ i, C i) ^ (n + 2)).subscheme, ((∏ i, C i) ^ (n + 2)).subschemeι ⁻¹ᵁ V))
    (hx' : φ' (MvPolynomial.X 0) = x') (hy' : φ' (MvPolynomial.X 1) = y')
    (hker_x : ∀ i : Fin r, i.succ = c → RingHom.ker (inclSections (hCi i) V) = Ideal.span {x'})
    (hker_y : ∀ i : Fin r, i.castSucc = c → RingHom.ker (inclSections (hCi i) V) = Ideal.span {y'}) :
    Function.Surjective φ' ∧ RingHom.ker φ' = Ideal.span {qchart K r c} ^ (n + 2) := by
  have hprod := prod_adjacent_eq hr (fun i => RingHom.ker (inclSections (hCi i) V)) c x' y'
    (fun i h1 h2 => by
      rw [ker_inclSections_eq_top]
      exact preimage_eq_bot_of_disjoint _ V (hdisj i h2 h1))
    hker_x hker_y
  have hφ'q : φ' (qchart K r c) = if c = 0 then y' else if c = Fin.last r then x' else x' * y' := by
    unfold qchart
    split_ifs <;> simp [hx', hy']
  have hh : RingHom.ker (inclSections (pow_le_pow_right_of_le_one' le_top (by omega : 1 ≤ n + 2) :
      (∏ i, C i) ^ (n + 2) ≤ (∏ i, C i) ^ 1) V) = Ideal.span {φ' (qchart K r c)} := by
    rw [ker_inclSections_prod_pow C 1 _ V hV, pow_one, hφ'q, ← hprod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [ker_inclSections_eq_comap]
  obtain ⟨hN, hnil, hann⟩ := chart_step_geom C n V hV (φ' (qchart K r c)) hh
  obtain ⟨hs, hk⟩ := chart_levels_nil φ φ' _ hρ (qchart K r c) n (inclSections_surjective _ V hV) hφs
    (by rw [hφk, Ideal.span_singleton_pow]) (by rw [hN, Ideal.span_singleton_pow]) hnil hann
  exact ⟨hs, by rw [hk, Ideal.span_singleton_pow]⟩

end ChartSurjKer

/-- Along a surjective morphism, a basic open is detected by its preimage. -/
private theorem eq_basicOpen_of_preimage {A B : Scheme.{u}} (f : A ⟶ B) (hf : Function.Surjective f)
    {T : B.Opens} {W' : A.Opens} (hW' : W' ≤ f ⁻¹ᵁ T) (a : Γ(B, T)) (W : B.Opens) (hWT : W ≤ T)
    (hW : f ⁻¹ᵁ W = A.basicOpen (f.appLE T W' hW' a)) (hW'T : W' = f ⁻¹ᵁ T) :
    W = B.basicOpen a := by
  rw [Scheme.basicOpen_appLE, hW'T] at hW
  have h1 : f ⁻¹ᵁ B.basicOpen a ≤ f ⁻¹ᵁ T := Scheme.Hom.preimage_mono _ (Scheme.basicOpen_le B a)
  have : f ⁻¹ᵁ W = f ⁻¹ᵁ B.basicOpen a := by
    rw [hW]
    exact inf_eq_right.2 h1
  exact TopologicalSpace.Opens.ext
    ((Set.preimage_injective.2 hf) (congrArg (fun U : A.Opens => (U : Set A)) this))

private theorem exists_lift_gen {K : Type u} [Field K] {Y : Scheme.{u}} {ι : Type*} [Fintype ι]
    (C : ι → Y.IdealSheafData) [hC : ∀ i, Stacks.Divisors.IsEffectiveCartierDivisor (C i)]
    (n : ℕ) (V : Y.Opens)
    (hV1 : IsAffineOpen (((∏ i, C i) ^ (n + 2)).subschemeι ⁻¹ᵁ V)) (i : ι)
    (hCi : (∏ i, C i) ^ (n + 1 + 1) ≤ C i) (hCi' : (∏ i, C i) ^ (n + 1) ≤ C i)
    (y : Γ(((∏ i, C i) ^ (n + 1)).subscheme, ((∏ i, C i) ^ (n + 1)).subschemeι ⁻¹ᵁ V))
    (hker : RingHom.ker (inclSections hCi' V) = Ideal.span {y})
    (h0 : n = 0 → ∃ (J : Ideal (MvPolynomial (Fin 2) K))
      (φ0 : MvPolynomial (Fin 2) K →+*
        Γ(((∏ i, C i) ^ (n + 1)).subscheme, ((∏ i, C i) ^ (n + 1)).subschemeι ⁻¹ᵁ V)),
      Function.Surjective φ0 ∧ RingHom.ker φ0 = J ∧
      (J = Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 2) K)} ∨
        J = Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin 2) K)} ∨
        J = Ideal.span {(MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) K)}) ∧
      ∃ v u : Fin 2, u ≠ v ∧
        (J = Ideal.span {(MvPolynomial.X v : MvPolynomial (Fin 2) K)} ∨
          J = Ideal.span {(MvPolynomial.X u * MvPolynomial.X v : MvPolynomial (Fin 2) K)}) ∧
        φ0 (MvPolynomial.X v) = y) :
    ∃ y' : Γ(((∏ i, C i) ^ (n + 2)).subscheme, ((∏ i, C i) ^ (n + 2)).subschemeι ⁻¹ᵁ V),
      inclSections (pow_le_pow_right_of_le_one' le_top (by omega : n + 1 ≤ n + 2) :
        (∏ i, C i) ^ (n + 2) ≤ (∏ i, C i) ^ (n + 1)) V y' = y ∧
      RingHom.ker (inclSections hCi V) = Ideal.span {y'} := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain ⟨J, φ0, hs0, hk0, hJ, v, u, huv, hJv, hy⟩ := h0 rfl
    exact lift_gen_zero C V hV1 i hCi hCi' φ0 hs0 hk0 hJ v u huv hJv y hy hker
  · obtain ⟨y1, hy1⟩ := inclSections_surjective
      (pow_le_pow_right_of_le_one' le_top (by omega : n + 1 ≤ n + 2) :
        (∏ i, C i) ^ (n + 2) ≤ (∏ i, C i) ^ (n + 1)) V hV1 y
    exact ⟨y1, hy1, lift_gen_pos C n hn V hV1 i hCi hCi' y hker y1 hy1⟩

/-- The invariant of the lifting induction at level `n`: the charts are the completions of `𝔸²`
along `J j` at level `n`, the markings are the axes, and the consecutive charts overlap along
the formal neighbourhood of `𝔾_m`. -/
private def ChartInv {K : Type u} [Field K] {X : Scheme.{u}} (sX : X ⟶ Spec (.of K)) {r : ℕ}
    (E : Fin r → PrimeDivisor X) (ZL ZR : ℕ → X.IdealSheafData)
    (hZL : ∀ n, (∏ i, (E i).idealSheaf) ^ (n + 1) ≤ ZL n)
    (hZR : ∀ n, (∏ i, (E i).idealSheaf) ^ (n + 1) ≤ ZR n)
    (V : Fin (r + 1) → X.Opens)
    (n : ℕ)
    (x y : ∀ j, Γ(((∏ i, (E i).idealSheaf) ^ (n + 1)).subscheme,
      ((∏ i, (E i).idealSheaf) ^ (n + 1)).subschemeι ⁻¹ᵁ (V j))) : Prop :=
  let I := ∏ i, (E i).idealSheaf
  let S : ℕ → Scheme.{u} := fun n => (I ^ (n + 1)).subscheme
  let tr : ∀ n, X.Opens → (S n).Opens := fun n V => (I ^ (n + 1)).subschemeι ⁻¹ᵁ V
  let σ : ∀ n (U : (S n).Opens), K →+* Γ(S n, U) := fun n U =>
    ((Scheme.ΓSpecIso (.of K)).inv ≫
      ((I ^ (n + 1)).subschemeι ≫ sX).appLE ⊤ U le_top).hom
  let J : Fin (r + 1) → Ideal (MvPolynomial (Fin 2) K) := fun j =>
    if j = 0 then Ideal.span {MvPolynomial.X 1}
    else if j = Fin.last r then Ideal.span {MvPolynomial.X 0}
    else Ideal.span {MvPolynomial.X 0 * MvPolynomial.X 1}
  (∀ j, Function.Surjective (MvPolynomial.eval₂Hom (σ n (tr n (V j))) ![x j, y j]) ∧
    RingHom.ker (MvPolynomial.eval₂Hom (σ n (tr n (V j))) ![x j, y j]) = J j ^ (n + 1)) ∧
  (RingHom.ker ((Scheme.IdealSheafData.inclusion (hZL n)).app (tr n (V 0))).hom =
      Ideal.span {x 0} ∧
    RingHom.ker ((Scheme.IdealSheafData.inclusion (hZR n)).app
      (tr n (V (Fin.last r)))).hom = Ideal.span {y (Fin.last r)}) ∧
  (∀ j : Fin r, tr n (V j.castSucc ⊓ V j.succ) = (S n).basicOpen (x j.castSucc) ∧
    tr n (V j.castSucc ⊓ V j.succ) = (S n).basicOpen (y j.succ)) ∧
  LevelEq E V n x y

section MarkingPieces

open CategoryTheory

private theorem mv_decomp {K : Type u} [Field K] (p : MvPolynomial (Fin 2) K) :
    ∃ (c : K) (p' p'' : MvPolynomial (Fin 2) K),
      p = MvPolynomial.C c + MvPolynomial.X 0 * p' + MvPolynomial.X 1 * p'' := by
  have h : MvPolynomial.constantCoeff (p - MvPolynomial.C (MvPolynomial.constantCoeff p)) = 0 := by
    simp
  have hm := mem_span_X_of_constantCoeff _ h
  rw [Set.insert_eq, Ideal.span_union, Submodule.mem_sup] at hm
  obtain ⟨u, hu, v, hv, huv⟩ := hm
  rw [Ideal.mem_span_singleton'] at hu hv
  obtain ⟨a, rfl⟩ := hu
  obtain ⟨b, rfl⟩ := hv
  exact ⟨_, a, b, by rw [add_assoc, mul_comm _ a, mul_comm _ b, huv]; ring⟩

private theorem marking_alg {K R A : Type*} [Field K] [CommRing R] [CommRing A] (σ : K →+* R)
    (ρ : R →+* A) (a1 b1 : R) (n : ℕ)
    (hgen : ∀ a : R, ∃ (c : K) (a' a'' : R), a = σ c + a1 * a' + b1 * a'')
    (hnil : b1 ^ (n + 2) = 0)
    (hN : RingHom.ker ρ = Ideal.span {b1 ^ (n + 1)})
    (𝔨 : Ideal R) (hk1 : ∃ k ∈ 𝔨, ρ k = ρ a1)
    (hk2 : ∀ z ∈ 𝔨, ∃ r, ρ z = ρ a1 * ρ r)
    (hnot : b1 ^ (n + 1) ∉ 𝔨) :
    ∃ k, ρ k = ρ a1 ∧ 𝔨 = Ideal.span {k} := by
  obtain ⟨k, hk, hρk⟩ := hk1
  refine ⟨k, hρk, le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem _).2 hk)⟩
  intro z hz
  obtain ⟨r, hr⟩ := hk2 z hz
  have hzk : z - k * r ∈ RingHom.ker ρ := by
    rw [RingHom.mem_ker, map_sub, map_mul, hr, hρk, sub_self]
  rw [hN, Ideal.mem_span_singleton'] at hzk
  obtain ⟨a, ha⟩ := hzk
  have hz' : a * b1 ^ (n + 1) ∈ 𝔨 := by
    rw [ha]; exact 𝔨.sub_mem hz (𝔨.mul_mem_right _ hk)
  have hx1 : a1 * b1 ^ (n + 1) = k * b1 ^ (n + 1) := by
    have : k - a1 ∈ RingHom.ker ρ := by rw [RingHom.mem_ker, map_sub, hρk, sub_self]
    rw [hN, Ideal.mem_span_singleton'] at this
    obtain ⟨d, hd⟩ := this
    have h2 : (k - a1) * b1 ^ (n + 1) = 0 := by
      rw [← hd, mul_assoc, ← pow_add]
      have : b1 ^ (n + 1 + (n + 1)) = 0 := pow_eq_zero_of_le (by omega) hnil
      rw [this, mul_zero]
    rw [sub_mul, sub_eq_zero] at h2
    exact h2.symm
  obtain ⟨c, a', a'', hca⟩ := hgen a
  have hexp : a * b1 ^ (n + 1) = σ c * b1 ^ (n + 1) + k * (a' * b1 ^ (n + 1)) := by
    rw [hca]; linear_combination a' * hx1 + a'' * hnil
  by_cases hc : c = 0
  · subst hc
    have hz2 : z = k * r + a * b1 ^ (n + 1) := by rw [ha]; ring
    rw [hz2, hexp, map_zero, zero_mul, zero_add]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self k))
      (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self k))
  · exfalso
    have h1 : σ c * b1 ^ (n + 1) ∈ 𝔨 := by
      have : σ c * b1 ^ (n + 1) = a * b1 ^ (n + 1) - k * (a' * b1 ^ (n + 1)) := by rw [hexp]; ring
      rw [this]; exact 𝔨.sub_mem hz' (𝔨.mul_mem_right _ hk)
    apply hnot
    have h2 := 𝔨.mul_mem_left (σ c⁻¹) h1
    rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul] at h2

private theorem no_ringEquiv_quot {K : Type u} [Field K] (n : ℕ) :
    IsEmpty (Polynomial K ⧸ Ideal.span {(Polynomial.X : Polynomial K) ^ (n + 1 + 1)} ≃+*
      Polynomial K ⧸ Ideal.span {(Polynomial.X : Polynomial K) ^ (n + 1)}) := by
  refine ⟨fun e => ?_⟩
  let a : Polynomial K ⧸ Ideal.span {(Polynomial.X : Polynomial K) ^ (n + 1 + 1)} :=
    Ideal.Quotient.mk _ Polynomial.X
  have ha1 : a ^ (n + 1 + 1) = 0 := by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.mem_span_singleton_self _
  have ha2 : a ^ (n + 1) ≠ 0 := by
    rw [← map_pow, Ne, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    intro h
    rw [Polynomial.X_pow_dvd_iff] at h
    have := h (n + 1) (by omega)
    simp at this
  have hb : (e a) ^ (n + 1 + 1) = 0 := by rw [← map_pow, ha1, map_zero]
  obtain ⟨f, hf⟩ := Ideal.Quotient.mk_surjective (e a)
  rw [← hf, ← map_pow, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hb
  have hX : (Polynomial.X : Polynomial K) ∣ f := by
    have : (Polynomial.X : Polynomial K) ∣ f ^ (n + 1 + 1) :=
      (dvd_pow_self _ (by omega)).trans hb
    exact Polynomial.prime_X.dvd_of_dvd_pow this
  obtain ⟨g, rfl⟩ := hX
  have : (e a) ^ (n + 1) = 0 := by
    rw [← hf, ← map_pow, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    exact ⟨g ^ (n + 1), by ring⟩
  apply ha2
  apply e.injective
  rw [map_pow, this, map_zero]

private theorem ringEquiv_of_iso_top {Z : Scheme.{u}} {Q : CommRingCat.{u}} (e : Z ≅ Spec Q)
    (U : Z.Opens) (hU : U = ⊤) : Nonempty (Γ(Z, U) ≃+* Q) := by
  subst hU
  let i : Γ(Z, ⊤) ≅ Q := (Scheme.Γ.mapIso e.op).symm ≪≫ Scheme.ΓSpecIso Q
  exact ⟨i.commRingCatIsoToRingEquiv⟩

private theorem subsingleton_primeSpectrum_quot {K : Type u} [Field K] (m : ℕ) :
    Subsingleton (PrimeSpectrum (Polynomial K ⧸ Ideal.span {(Polynomial.X : Polynomial K) ^ (m + 1)})) := by
  let Q := Polynomial K ⧸ Ideal.span {(Polynomial.X : Polynomial K) ^ (m + 1)}
  let ε : Q →+* K := Ideal.Quotient.lift _ (Polynomial.evalRingHom 0) (by
    intro f hf
    rw [Ideal.mem_span_singleton] at hf
    obtain ⟨g, rfl⟩ := hf
    simp)
  have hεs : Function.Surjective ε := fun k => ⟨Ideal.Quotient.mk _ (Polynomial.C k), by
    have hε : ∀ f, ε (Ideal.Quotient.mk _ f) = Polynomial.eval 0 f := fun f => rfl
    rw [hε]; simp⟩
  have hmax : (RingHom.ker ε).IsMaximal := RingHom.ker_isMaximal_of_surjective ε hεs
  have key : ∀ P : PrimeSpectrum Q, P.asIdeal = RingHom.ker ε := by
    intro P
    have hX : Ideal.Quotient.mk (Ideal.span {(Polynomial.X : Polynomial K) ^ (m + 1)}) Polynomial.X ∈ P.asIdeal := by
      apply P.isPrime.mem_of_pow_mem (m + 1)
      have h0 : Ideal.Quotient.mk (Ideal.span {(Polynomial.X : Polynomial K) ^ (m + 1)})
          (Polynomial.X ^ (m + 1)) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
      rw [← map_pow, h0]; exact P.asIdeal.zero_mem
    have hle : RingHom.ker ε ≤ P.asIdeal := by
      intro z hz
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective z
      rw [RingHom.mem_ker] at hz
      have hε : ∀ f, ε (Ideal.Quotient.mk _ f) = Polynomial.eval 0 f := fun f => rfl
      rw [hε] at hz
      have : (Polynomial.X : Polynomial K) ∣ f := by
        rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero]; exact hz
      obtain ⟨g, rfl⟩ := this
      rw [map_mul]
      exact P.asIdeal.mul_mem_right _ hX
    exact (hmax.eq_of_le P.isPrime.ne_top hle).symm
  exact ⟨fun P P' => PrimeSpectrum.ext ((key P).trans (key P').symm)⟩

private theorem subschemeι_preimage_eq_top {X : Scheme.{u}} {D D0 : X.IdealSheafData} (h : D ≤ D0)
    {Q : CommRingCat.{u}} (e : D.subscheme ≅ Spec Q) (hQ : Subsingleton (PrimeSpectrum Q))
    (V0 : X.Opens) (hsup : ((D0.support : Set X)) ⊆ V0) (hne : ((D0.support : Set X)).Nonempty) :
    D.subschemeι ⁻¹ᵁ V0 = ⊤ := by
  obtain ⟨p, hp⟩ := hne
  rw [← Scheme.IdealSheafData.range_subschemeι] at hp
  obtain ⟨w, rfl⟩ := hp
  refine top_le_iff.1 (fun z _ => ?_)
  have hz : z = Scheme.IdealSheafData.inclusion h w :=
    e.hom.homeomorph.injective (Subsingleton.elim (α := PrimeSpectrum Q) _ _)
  show D.subschemeι z ∈ V0
  rw [hz, ← Scheme.Hom.comp_apply, Scheme.IdealSheafData.inclusion_subschemeι]
  apply hsup
  rw [← Scheme.IdealSheafData.range_subschemeι]
  exact ⟨w, rfl⟩

end MarkingPieces

section MarkingCore

open CategoryTheory

private theorem ker_inclSections_sup {Y : Scheme.{u}} {I₂ D D1 D2 : Y.IdealSheafData}
    (hD : D = D1 ⊔ D2) (h : I₂ ≤ D) (h1 : I₂ ≤ D1) (h2 : I₂ ≤ D2)
    (U : Y.Opens) (hU : IsAffineOpen (I₂.subschemeι ⁻¹ᵁ U)) :
    RingHom.ker (inclSections h U) =
      RingHom.ker (inclSections h1 U) ⊔ RingHom.ker (inclSections h2 U) := by
  subst hD
  rw [ker_inclSections_eq_comap h U hU, ker_inclSections_eq_comap h1 U hU,
    ker_inclSections_eq_comap h2 U hU, Scheme.IdealSheafData.comap_sup]
  rfl

private theorem marking_core {K : Type u} [Field K] {X : Scheme.{u}} {r : ℕ}
    (E : Fin r → PrimeDivisor X) (ZL : ℕ → X.IdealSheafData)
    (hZL : ∀ n, (∏ i, (E i).idealSheaf) ^ (n + 1) ≤ ZL n)
    (hZL_succ : ∀ n, ZL n = ZL (n + 1) ⊔ (∏ i, (E i).idealSheaf) ^ (n + 1))
    (sX : X ⟶ Spec (.of K))
    (hZL_curvilinear : ∀ n, ∃ e : (ZL n).subscheme ≅
      Spec (.of (Polynomial K ⧸ Ideal.span {(Polynomial.X : Polynomial K) ^ (n + 1)})),
      e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K _)) = (ZL n).subschemeι ≫ sX)
    (pL : X) (hZL_zero : ((ZL 0).support : Set X) = {pL})
    (V0 : X.Opens) (hpL : pL ∈ V0) (n : ℕ)
    (hV0 : IsAffineOpen (((∏ i, (E i).idealSheaf) ^ (n + 1 + 1)).subschemeι ⁻¹ᵁ V0))
    (a : Γ(((∏ i, (E i).idealSheaf) ^ (n + 1)).subscheme,
      ((∏ i, (E i).idealSheaf) ^ (n + 1)).subschemeι ⁻¹ᵁ V0))
    (hmk : RingHom.ker ((Scheme.IdealSheafData.inclusion (hZL n)).app
      (((∏ i, (E i).idealSheaf) ^ (n + 1)).subschemeι ⁻¹ᵁ V0)).hom = Ideal.span {a})
    (a1 b1 : Γ(((∏ i, (E i).idealSheaf) ^ (n + 1 + 1)).subscheme,
      ((∏ i, (E i).idealSheaf) ^ (n + 1 + 1)).subschemeι ⁻¹ᵁ V0))
    (hle : (∏ i, (E i).idealSheaf) ^ (n + 1 + 1) ≤ (∏ i, (E i).idealSheaf) ^ (n + 1))
    (hρa : inclSections hle V0 a1 = a)
    (σ : K →+* Γ(((∏ i, (E i).idealSheaf) ^ (n + 1 + 1)).subscheme,
      ((∏ i, (E i).idealSheaf) ^ (n + 1 + 1)).subschemeι ⁻¹ᵁ V0))
    (hgen : ∀ c : Γ(((∏ i, (E i).idealSheaf) ^ (n + 1 + 1)).subscheme,
      ((∏ i, (E i).idealSheaf) ^ (n + 1 + 1)).subschemeι ⁻¹ᵁ V0),
      ∃ (k : K) (c' c'' : _), c = σ k + a1 * c' + b1 * c'')
    (hnil : b1 ^ (n + 2) = 0)
    (hN : RingHom.ker (inclSections hle V0) = Ideal.span {b1 ^ (n + 1)}) :
    ∃ k, inclSections hle V0 k = a ∧
      RingHom.ker ((Scheme.IdealSheafData.inclusion (hZL (n + 1))).app
        (((∏ i, (E i).idealSheaf) ^ (n + 1 + 1)).subschemeι ⁻¹ᵁ V0)).hom = Ideal.span {k} := by
  classical
  have hρs := inclSections_surjective hle V0 hV0
  have h2 : (∏ i, (E i).idealSheaf) ^ (n + 1 + 1) ≤ ZL n := hle.trans (hZL n)
  have hsum : RingHom.ker (inclSections h2 V0) =
      RingHom.ker (inclSections (hZL (n + 1)) V0) ⊔ RingHom.ker (inclSections hle V0) :=
    ker_inclSections_sup (hZL_succ n) h2 (hZL (n + 1))
      ((hZL n).trans le_rfl |> fun _ => hle) V0 hV0
  have hmkr : RingHom.ker (inclSections (hZL n) V0) = Ideal.span {a} := by
    rw [ker_inclSections_eq_ker_app]; exact hmk
  have hπ : ∀ z, inclSections h2 V0 z = inclSections (hZL n) V0 (inclSections hle V0 z) :=
    fun z => incl_trans hle (hZL n) V0 z
  have hmem : ∀ z, z ∈ RingHom.ker (inclSections h2 V0) ↔
      inclSections hle V0 z ∈ Ideal.span {a} := by
    intro z
    rw [RingHom.mem_ker, hπ, ← RingHom.mem_ker, hmkr]
  have hk2 : ∀ z ∈ RingHom.ker (inclSections (hZL (n + 1)) V0), ∃ s,
      inclSections hle V0 z = inclSections hle V0 a1 * inclSections hle V0 s := by
    intro z hz
    have hz' : z ∈ RingHom.ker (inclSections h2 V0) := by
      rw [hsum]; exact Ideal.mem_sup_left hz
    rw [hmem, Ideal.mem_span_singleton'] at hz'
    obtain ⟨t, ht⟩ := hz'
    obtain ⟨s, rfl⟩ := hρs t
    exact ⟨s, by rw [← ht, hρa, mul_comm]⟩
  have hk1 : ∃ k ∈ RingHom.ker (inclSections (hZL (n + 1)) V0),
      inclSections hle V0 k = inclSections hle V0 a1 := by
    have : a1 ∈ RingHom.ker (inclSections h2 V0) := by
      rw [hmem, hρa]; exact Ideal.mem_span_singleton_self a
    rw [hsum, Submodule.mem_sup] at this
    obtain ⟨u, hu, v, hv, huv⟩ := this
    refine ⟨u, hu, ?_⟩
    have hv0 : inclSections hle V0 v = 0 := hv
    rw [← huv, map_add, hv0, add_zero]
  have hnot : b1 ^ (n + 1) ∉ RingHom.ker (inclSections (hZL (n + 1)) V0) := by
    intro hb
    have hN_le : RingHom.ker (inclSections hle V0) ≤
        RingHom.ker (inclSections (hZL (n + 1)) V0) := by
      rw [hN, Ideal.span_le]; exact Set.singleton_subset_iff.2 hb
    have heq : RingHom.ker (inclSections (hZL (n + 1)) V0) =
        RingHom.ker (inclSections h2 V0) := by
      rw [hsum]; exact (sup_eq_left.2 hN_le).symm
    have hs1 := inclSections_surjective (hZL (n + 1)) V0 hV0
    have hs2 := inclSections_surjective h2 V0 hV0
    let g := (RingHom.quotientKerEquivOfSurjective hs1).symm.trans
      ((Ideal.quotEquivOfEq heq).trans (RingHom.quotientKerEquivOfSurjective hs2))
    have hanti : ∀ i, ZL i ≤ ZL 0 := by
      intro i
      induction i with
      | zero => exact le_rfl
      | succ i ih => exact ((le_sup_left : ZL (i + 1) ≤ ZL (i + 1) ⊔ _).trans_eq
          (hZL_succ i).symm).trans ih
    have hsup : ((ZL 0).support : Set X) ⊆ V0 := by
      rw [hZL_zero]; exact Set.singleton_subset_iff.2 hpL
    have hne : ((ZL 0).support : Set X).Nonempty := by
      rw [hZL_zero]; exact ⟨pL, rfl⟩
    have htop : ∀ i, (ZL i).subschemeι ⁻¹ᵁ V0 = ⊤ := fun i => by
      obtain ⟨e, -⟩ := hZL_curvilinear i
      exact subschemeι_preimage_eq_top (hanti i) e (subsingleton_primeSpectrum_quot i) V0 hsup hne
    obtain ⟨e1, -⟩ := hZL_curvilinear (n + 1)
    obtain ⟨e0, -⟩ := hZL_curvilinear n
    obtain ⟨f1⟩ := ringEquiv_of_iso_top e1 _ (htop (n + 1))
    obtain ⟨f0⟩ := ringEquiv_of_iso_top e0 _ (htop n)
    exact (no_ringEquiv_quot (K := K) n).false (f1.symm.trans (g.trans f0))
  obtain ⟨k, hk, hkk⟩ := marking_alg σ (inclSections hle V0) a1 b1 n hgen hnil hN _ hk1 hk2 hnot
  refine ⟨k, hk.trans hρa, ?_⟩
  rw [← ker_inclSections_eq_ker_app]; exact hkk

end MarkingCore

private theorem ker_rho_eq {P R A : Type*} [CommRing P] [CommRing R] [CommRing A] (φ : P →+* R)
    (hs : Function.Surjective φ) (ρ : R →+* A) (q : P) (n : ℕ)
    (hq : RingHom.ker (ρ.comp φ) = Ideal.span {q} ^ (n + 1)) :
    RingHom.ker ρ = Ideal.span {φ q ^ (n + 1)} := by
  rw [Ideal.span_singleton_pow] at hq
  apply le_antisymm
  · intro z hz
    obtain ⟨p, rfl⟩ := hs z
    have : p ∈ RingHom.ker (ρ.comp φ) := hz
    rw [hq, Ideal.mem_span_singleton'] at this
    obtain ⟨s, rfl⟩ := this
    rw [map_mul, map_pow]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  · rw [Ideal.span_le, Set.singleton_subset_iff, ← map_pow]
    have : q ^ (n + 1) ∈ RingHom.ker (ρ.comp φ) := by
      rw [hq]; exact Ideal.mem_span_singleton_self _
    exact this

private theorem marking_left {K : Type u} [Field K] {X : Scheme.{u}} {r : ℕ}
    (E : Fin r → PrimeDivisor X) (ZL : ℕ → X.IdealSheafData)
    (hZL : ∀ n, (∏ i, (E i).idealSheaf) ^ (n + 1) ≤ ZL n)
    (hZL_succ : ∀ n, ZL n = ZL (n + 1) ⊔ (∏ i, (E i).idealSheaf) ^ (n + 1))
    (sX : X ⟶ Spec (.of K))
    (hZL_curvilinear : ∀ n, ∃ e : (ZL n).subscheme ≅
      Spec (.of (Polynomial K ⧸ Ideal.span {(Polynomial.X : Polynomial K) ^ (n + 1)})),
      e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K _)) = (ZL n).subschemeι ≫ sX)
    (pL : X) (hZL_zero : ((ZL 0).support : Set X) = {pL})
    (V0 : X.Opens) (hpL : pL ∈ V0) (n : ℕ)
    (hV0 : IsAffineOpen (((∏ i, (E i).idealSheaf) ^ (n + 1 + 1)).subschemeι ⁻¹ᵁ V0))
    (x y : Γ(((∏ i, (E i).idealSheaf) ^ (n + 1)).subscheme,
      ((∏ i, (E i).idealSheaf) ^ (n + 1)).subschemeι ⁻¹ᵁ V0))
    (hmk : RingHom.ker ((Scheme.IdealSheafData.inclusion (hZL n)).app
      (((∏ i, (E i).idealSheaf) ^ (n + 1)).subschemeι ⁻¹ᵁ V0)).hom = Ideal.span {x})
    (hkn : RingHom.ker (MvPolynomial.eval₂Hom (sigmaSub sX ((∏ i, (E i).idealSheaf) ^ (n + 1)) V0) ![x, y]) =
      Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 2) K)} ^ (n + 1))
    (x1 y1 : Γ(((∏ i, (E i).idealSheaf) ^ (n + 1 + 1)).subscheme,
      ((∏ i, (E i).idealSheaf) ^ (n + 1 + 1)).subschemeι ⁻¹ᵁ V0))
    (hx1 : inclSections (pow_le_pow_right_of_le_one' le_top (by omega : n + 1 ≤ n + 1 + 1) :
        (∏ i, (E i).idealSheaf) ^ (n + 1 + 1) ≤ (∏ i, (E i).idealSheaf) ^ (n + 1)) V0 x1 = x)
    (hy1 : inclSections (pow_le_pow_right_of_le_one' le_top (by omega : n + 1 ≤ n + 1 + 1) :
        (∏ i, (E i).idealSheaf) ^ (n + 1 + 1) ≤ (∏ i, (E i).idealSheaf) ^ (n + 1)) V0 y1 = y)
    (hs : Function.Surjective (MvPolynomial.eval₂Hom (sigmaSub sX ((∏ i, (E i).idealSheaf) ^ (n + 1 + 1)) V0) ![x1, y1]))
    (hk : RingHom.ker (MvPolynomial.eval₂Hom (sigmaSub sX ((∏ i, (E i).idealSheaf) ^ (n + 1 + 1)) V0) ![x1, y1]) =
      Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 2) K)} ^ (n + 1 + 1)) :
    ∃ x'' : Γ(((∏ i, (E i).idealSheaf) ^ (n + 1 + 1)).subscheme,
        ((∏ i, (E i).idealSheaf) ^ (n + 1 + 1)).subschemeι ⁻¹ᵁ V0),
      inclSections (pow_le_pow_right_of_le_one' le_top (by omega : n + 1 ≤ n + 1 + 1) :
        (∏ i, (E i).idealSheaf) ^ (n + 1 + 1) ≤ (∏ i, (E i).idealSheaf) ^ (n + 1)) V0 x'' = x ∧
      RingHom.ker ((Scheme.IdealSheafData.inclusion (hZL (n + 1))).app
        (((∏ i, (E i).idealSheaf) ^ (n + 1 + 1)).subschemeι ⁻¹ᵁ V0)).hom = Ideal.span {x''} := by
  set hle : (∏ i, (E i).idealSheaf) ^ (n + 1 + 1) ≤ (∏ i, (E i).idealSheaf) ^ (n + 1) :=
    pow_le_pow_right_of_le_one' le_top (by omega : n + 1 ≤ n + 1 + 1) with hle_def
  set φ := MvPolynomial.eval₂Hom (sigmaSub sX ((∏ i, (E i).idealSheaf) ^ (n + 1 + 1)) V0) ![x1, y1]
    with hφ
  have hN := ker_rho_eq φ hs (inclSections hle V0) (MvPolynomial.X 1) n
    (by rw [inclSections_comp_eval₂Hom sX hle V0 hx1 hy1]; exact hkn)
  have hφX1 : φ (MvPolynomial.X 1) = y1 := by simp [hφ]
  have hnil : y1 ^ (n + 2) = 0 := by
    rw [← hφX1, ← map_pow]
    have : (MvPolynomial.X 1 : MvPolynomial (Fin 2) K) ^ (n + 2) ∈ RingHom.ker φ := by
      rw [hk, Ideal.span_singleton_pow]; exact Ideal.mem_span_singleton_self _
    exact this
  refine marking_core E ZL hZL hZL_succ sX hZL_curvilinear pL hZL_zero V0 hpL n hV0 x hmk x1 y1 hle hx1
    (sigmaSub sX ((∏ i, (E i).idealSheaf) ^ (n + 1 + 1)) V0) ?_ hnil (by rwa [hφX1] at hN)
  intro c
  obtain ⟨p, rfl⟩ := hs c
  obtain ⟨k, p', p'', hp⟩ := mv_decomp p
  refine ⟨k, φ p', φ p'', ?_⟩
  rw [hp]
  simp [hφ]

private theorem marking_right {K : Type u} [Field K] {X : Scheme.{u}} {r : ℕ}
    (E : Fin r → PrimeDivisor X) (ZR : ℕ → X.IdealSheafData)
    (hZR : ∀ n, (∏ i, (E i).idealSheaf) ^ (n + 1) ≤ ZR n)
    (hZR_succ : ∀ n, ZR n = ZR (n + 1) ⊔ (∏ i, (E i).idealSheaf) ^ (n + 1))
    (sX : X ⟶ Spec (.of K))
    (hZR_curvilinear : ∀ n, ∃ e : (ZR n).subscheme ≅
      Spec (.of (Polynomial K ⧸ Ideal.span {(Polynomial.X : Polynomial K) ^ (n + 1)})),
      e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K _)) = (ZR n).subschemeι ≫ sX)
    (pR : X) (hZR_zero : ((ZR 0).support : Set X) = {pR})
    (Vl : X.Opens) (hpR : pR ∈ Vl) (n : ℕ)
    (hVl : IsAffineOpen (((∏ i, (E i).idealSheaf) ^ (n + 1 + 1)).subschemeι ⁻¹ᵁ Vl))
    (x y : Γ(((∏ i, (E i).idealSheaf) ^ (n + 1)).subscheme,
      ((∏ i, (E i).idealSheaf) ^ (n + 1)).subschemeι ⁻¹ᵁ Vl))
    (hmk : RingHom.ker ((Scheme.IdealSheafData.inclusion (hZR n)).app
      (((∏ i, (E i).idealSheaf) ^ (n + 1)).subschemeι ⁻¹ᵁ Vl)).hom = Ideal.span {y})
    (hkn : RingHom.ker (MvPolynomial.eval₂Hom (sigmaSub sX ((∏ i, (E i).idealSheaf) ^ (n + 1)) Vl) ![x, y]) =
      Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin 2) K)} ^ (n + 1))
    (x1 y1 : Γ(((∏ i, (E i).idealSheaf) ^ (n + 1 + 1)).subscheme,
      ((∏ i, (E i).idealSheaf) ^ (n + 1 + 1)).subschemeι ⁻¹ᵁ Vl))
    (hx1 : inclSections (pow_le_pow_right_of_le_one' le_top (by omega : n + 1 ≤ n + 1 + 1) :
        (∏ i, (E i).idealSheaf) ^ (n + 1 + 1) ≤ (∏ i, (E i).idealSheaf) ^ (n + 1)) Vl x1 = x)
    (hy1 : inclSections (pow_le_pow_right_of_le_one' le_top (by omega : n + 1 ≤ n + 1 + 1) :
        (∏ i, (E i).idealSheaf) ^ (n + 1 + 1) ≤ (∏ i, (E i).idealSheaf) ^ (n + 1)) Vl y1 = y)
    (hs : Function.Surjective (MvPolynomial.eval₂Hom (sigmaSub sX ((∏ i, (E i).idealSheaf) ^ (n + 1 + 1)) Vl) ![x1, y1]))
    (hk : RingHom.ker (MvPolynomial.eval₂Hom (sigmaSub sX ((∏ i, (E i).idealSheaf) ^ (n + 1 + 1)) Vl) ![x1, y1]) =
      Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin 2) K)} ^ (n + 1 + 1)) :
    ∃ y'' : Γ(((∏ i, (E i).idealSheaf) ^ (n + 1 + 1)).subscheme,
        ((∏ i, (E i).idealSheaf) ^ (n + 1 + 1)).subschemeι ⁻¹ᵁ Vl),
      inclSections (pow_le_pow_right_of_le_one' le_top (by omega : n + 1 ≤ n + 1 + 1) :
        (∏ i, (E i).idealSheaf) ^ (n + 1 + 1) ≤ (∏ i, (E i).idealSheaf) ^ (n + 1)) Vl y'' = y ∧
      RingHom.ker ((Scheme.IdealSheafData.inclusion (hZR (n + 1))).app
        (((∏ i, (E i).idealSheaf) ^ (n + 1 + 1)).subschemeι ⁻¹ᵁ Vl)).hom = Ideal.span {y''} := by
  set hle : (∏ i, (E i).idealSheaf) ^ (n + 1 + 1) ≤ (∏ i, (E i).idealSheaf) ^ (n + 1) :=
    pow_le_pow_right_of_le_one' le_top (by omega : n + 1 ≤ n + 1 + 1) with hle_def
  set φ := MvPolynomial.eval₂Hom (sigmaSub sX ((∏ i, (E i).idealSheaf) ^ (n + 1 + 1)) Vl) ![x1, y1]
    with hφ
  have hN := ker_rho_eq φ hs (inclSections hle Vl) (MvPolynomial.X 0) n
    (by rw [inclSections_comp_eval₂Hom sX hle Vl hx1 hy1]; exact hkn)
  have hφX0 : φ (MvPolynomial.X 0) = x1 := by simp [hφ]
  have hnil : x1 ^ (n + 2) = 0 := by
    rw [← hφX0, ← map_pow]
    have : (MvPolynomial.X 0 : MvPolynomial (Fin 2) K) ^ (n + 2) ∈ RingHom.ker φ := by
      rw [hk, Ideal.span_singleton_pow]; exact Ideal.mem_span_singleton_self _
    exact this
  refine marking_core E ZR hZR hZR_succ sX hZR_curvilinear pR hZR_zero Vl hpR n hVl y hmk y1 x1 hle hy1
    (sigmaSub sX ((∏ i, (E i).idealSheaf) ^ (n + 1 + 1)) Vl) ?_ hnil (by rwa [hφX0] at hN)
  intro c
  obtain ⟨p, rfl⟩ := hs c
  obtain ⟨k, p', p'', hp⟩ := mv_decomp p
  refine ⟨k, φ p'', φ p', ?_⟩
  have e : φ (MvPolynomial.C k + MvPolynomial.X 0 * p' + MvPolynomial.X 1 * p'') =
      sigmaSub sX ((∏ i, (E i).idealSheaf) ^ (n + 1 + 1)) Vl k + x1 * φ p' + y1 * φ p'' := by
    simp [hφ]
  rw [hp, e]
  exact add_right_comm _ _ _

private theorem lift_chart_step
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 2 sX]
    [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]
    {r : ℕ} (hr : 0 < r) (E : Fin r → PrimeDivisor X) (b : Fin r → ℤ)
    (hinj : Function.Injective E)
    (hrat : ∀ i, IsSmoothRationalCurve sX (E i).idealSheaf)
    (hself : ∀ i, IsIntersectionNumber sX (Finsupp.single (E i) 1) (E i).idealSheaf (-(b i)))
    (hadj : ∀ i j : Fin r, i.val + 1 = j.val →
      IsIntersectionNumber sX (Finsupp.single (E i) 1) (E j).idealSheaf 1)
    (hfar : ∀ i j : Fin r, i.val + 1 < j.val → Disjoint (E i).support (E j).support)
    (pL pR : X) (hpLR : pL ≠ pR)
    (hpL : pL ∈ (E ⟨0, hr⟩).support) (hpL' : ∀ i, i ≠ ⟨0, hr⟩ → pL ∉ (E i).support)
    (hpR : pR ∈ (E ⟨r - 1, by omega⟩).support)
    (hpR' : ∀ i, i ≠ ⟨r - 1, by omega⟩ → pR ∉ (E i).support)
    (ZL ZR : ℕ → X.IdealSheafData)
    (hZL : ∀ n, (∏ i, (E i).idealSheaf) ^ (n + 1) ≤ ZL n)
    (hZR : ∀ n, (∏ i, (E i).idealSheaf) ^ (n + 1) ≤ ZR n)
    (hZL_succ : ∀ n, ZL n = ZL (n + 1) ⊔ (∏ i, (E i).idealSheaf) ^ (n + 1))
    (hZR_succ : ∀ n, ZR n = ZR (n + 1) ⊔ (∏ i, (E i).idealSheaf) ^ (n + 1))
    (hZL_zero : ((ZL 0).support : Set X) = {pL}) (hZR_zero : ((ZR 0).support : Set X) = {pR})
    (hZL_curvilinear : ∀ n, ∃ e : (ZL n).subscheme ≅
      Spec (.of (Polynomial K ⧸ Ideal.span {(Polynomial.X : Polynomial K) ^ (n + 1)})),
      e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K _)) = (ZL n).subschemeι ≫ sX)
    (hZR_curvilinear : ∀ n, ∃ e : (ZR n).subscheme ≅
      Spec (.of (Polynomial K ⧸ Ideal.span {(Polynomial.X : Polynomial K) ^ (n + 1)})),
      e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K _)) = (ZR n).subschemeι ≫ sX) :
    let I := ∏ i, (E i).idealSheaf
    -- the `(n+1)`-st thickening `(n+1)E` and the trace on it of an open of `X`
    let S : ℕ → Scheme.{u} := fun n => (I ^ (n + 1)).subscheme
    let tr : ∀ n, X.Opens → (S n).Opens := fun n V => (I ^ (n + 1)).subschemeι ⁻¹ᵁ V
    -- the constants `K → Γ((n+1)E, U)`
    let σ : ∀ n (U : (S n).Opens), K →+* Γ(S n, U) := fun n U =>
      ((Scheme.ΓSpecIso (.of K)).inv ≫
        ((I ^ (n + 1)).subschemeι ≫ sX).appLE ⊤ U le_top).hom
    -- the restriction `(n+2)E → (n+1)E`
    let ρ : ∀ n (V : X.Opens), Γ(S (n + 1), tr (n + 1) V) → Γ(S n, tr n V) := fun n V =>
      ((Scheme.IdealSheafData.inclusion (pow_le_pow_right_of_le_one' le_top
          (Nat.le_succ (n + 1)) : I ^ (n + 1 + 1) ≤ I ^ (n + 1))).appLE (tr (n + 1) V) (tr n V)
        (by
          simp only [tr, ← Scheme.Hom.comp_preimage,
            Scheme.IdealSheafData.inclusion_subschemeι, le_refl])).hom
    -- restriction to a smaller open of `X`
    let res : ∀ n (V W : X.Opens), W ≤ V → Γ(S n, tr n V) → Γ(S n, tr n W) :=
      fun n _ _ h => ((S n).presheaf.map (homOfLE (Scheme.Hom.preimage_mono _ h)).op).hom
    -- the exceptional ideal of chart `j`: `(y)`, `(x y)` or `(x)`
    let J : Fin (r + 1) → Ideal (MvPolynomial (Fin 2) K) := fun j =>
      if j = 0 then Ideal.span {MvPolynomial.X 1}
      else if j = Fin.last r then Ideal.span {MvPolynomial.X 0}
      else Ideal.span {MvPolynomial.X 0 * MvPolynomial.X 1}
    ∀ (V : Fin (r + 1) → X.Opens) (x0 y0 : ∀ j, Γ(S 0, tr 0 (V j))),
      (((I.support : Set X) ⊆ ⋃ j, (V j : Set X)) ∧
      (pL ∈ V 0 ∧ pR ∈ V (Fin.last r) ∧ (RingHom.ker ((Scheme.IdealSheafData.inclusion (hZL 0)).app (tr 0 (V 0))).hom =
            Ideal.span {x0 0} ∧
          RingHom.ker ((Scheme.IdealSheafData.inclusion (hZR 0)).app
            (tr 0 (V (Fin.last r)))).hom = Ideal.span {y0 (Fin.last r)})) ∧
      (∀ j, IsAffineOpen (tr 0 (V j)) ∧
      Function.Surjective (MvPolynomial.eval₂Hom (σ 0 (tr 0 (V j))) ![x0 j, y0 j]) ∧
      RingHom.ker (MvPolynomial.eval₂Hom (σ 0 (tr 0 (V j))) ![x0 j, y0 j]) = J j ^ (0 + 1)) ∧
      (∀ j : Fin r, ((V j.castSucc ⊓ V j.succ : X.Opens) : Set X) ∩ I.support ⊆ (E j).support) ∧ (∀ j : Fin r, tr 0 (V j.castSucc ⊓ V j.succ) = (S 0).basicOpen (x0 j.castSucc) ∧
        tr 0 (V j.castSucc ⊓ V j.succ) = (S 0).basicOpen (y0 j.succ)) ∧ (∀ j k : Fin (r + 1), j.val + 2 ≤ k.val →
      ((V j ⊓ V k : X.Opens) : Set X) ∩ I.support = ∅) ∧ (∀ j : Fin r, ∃ d : K, d ≠ 0 ∧
        res 0 (V j.succ) (V j.castSucc ⊓ V j.succ) inf_le_right (y0 j.succ) *
          res 0 (V j.castSucc) (V j.castSucc ⊓ V j.succ) inf_le_left (x0 j.castSucc) = σ 0 (tr 0 (V j.castSucc ⊓ V j.succ)) d) ∧
      LocalEquations E V x0 y0) →
    ∀ (n : ℕ) (x y : ∀ j, Γ(S n, tr n (V j))), ChartInv sX E ZL ZR hZL hZR V n x y →
      ∃ x' y' : ∀ j, Γ(S (n + 1), tr (n + 1) (V j)),
        (∀ j, ρ n (V j) (x' j) = x j ∧ ρ n (V j) (y' j) = y j) ∧
        ChartInv sX E ZL ZR hZL hZR V (n + 1) x' y' := by
  intro I S tr σ ρ res J V x0 y0 hP n x y hInv
  obtain ⟨hcov, ⟨hpL0, hpR0, hmk0⟩, hch0, hovsup, hbas, hfar', hd0, hsupp, hlev0, hdisj⟩ := hP
  obtain ⟨hchn, hmkn, hovn, hlevn⟩ := hInv
  have hYreg := ((isRegular_iff_regular_stalks X).1
    (MMP.Resolution.Bridges.isRegular_of_isSmoothScheme sX (smoothScheme_of_smooth sX))).2
  haveI hcart : ∀ i, Stacks.Divisors.IsEffectiveCartierDivisor (E i).idealSheaf := fun i =>
    PrimeDivisor.isEffectiveCartierDivisor_idealSheaf
      (fun x => by have := hYreg x; exact IsRegularLocalRing.uniqueFactorizationMonoid _) (E i)
  have hA1 : ∀ c, IsAffineOpen (((∏ i, (E i).idealSheaf) ^ (n + 2)).subschemeι ⁻¹ᵁ V c) := fun c =>
    isAffineOpen_tr_pow _ (n + 1) _ (hch0 c).1
  have hsurj : ∀ c, Function.Surjective (ρ n (V c)) := fun c =>
    inclSections_surjective (pow_le_pow_right_of_le_one' le_top (by omega : n + 1 ≤ n + 1 + 1) :
        (∏ i, (E i).idealSheaf) ^ (n + 1 + 1) ≤ (∏ i, (E i).idealSheaf) ^ (n + 1)) (V c) (hA1 c)
  have liftx : ∀ c : Fin (r + 1), ∃ xc : Γ(S (n + 1), tr (n + 1) (V c)), ρ n (V c) xc = x c ∧
      ∀ j : Fin r, j.succ = c →
        RingHom.ker (inclSections (pow_le_divisor E (n + 1) j) (V c)) = Ideal.span {xc} := by
    intro c
    by_cases hc : ∃ j : Fin r, j.succ = c
    · obtain ⟨j, rfl⟩ := hc
      obtain ⟨x', hx', hk⟩ := exists_lift_gen (K := K) (fun i => (E i).idealSheaf) n (V j.succ)
        (hA1 _) j (pow_le_divisor E (n + 1) j) (pow_le_divisor E n j) (x j.succ) (hlevn j).2 (by
          intro hn0
          subst hn0
          refine ⟨J j.succ, MvPolynomial.eval₂Hom (σ 0 (tr 0 (V j.succ))) ![x j.succ, y j.succ],
            (hchn j.succ).1, by have h := (hchn j.succ).2; rw [zero_add, pow_one] at h; exact h, ?_, 0, 1, by decide, ?_, by simp⟩
          · exact (J_succ_cases j).elim (fun h => Or.inr (Or.inl h))
              (fun h => Or.inr (Or.inr (h.trans (by rw [mul_comm]))))
          · exact J_succ_cases j)
      refine ⟨x', hx', fun j' hj' => ?_⟩
      have : j' = j := Fin.succ_injective _ hj'
      subst this; exact hk
    · obtain ⟨x1, hx1⟩ := hsurj c (x c)
      exact ⟨x1, hx1, fun j hj => absurd ⟨j, hj⟩ hc⟩
  have lifty : ∀ c : Fin (r + 1), ∃ yc : Γ(S (n + 1), tr (n + 1) (V c)), ρ n (V c) yc = y c ∧
      ∀ j : Fin r, j.castSucc = c →
        RingHom.ker (inclSections (pow_le_divisor E (n + 1) j) (V c)) = Ideal.span {yc} := by
    intro c
    by_cases hc : ∃ j : Fin r, j.castSucc = c
    · obtain ⟨j, rfl⟩ := hc
      obtain ⟨y', hy', hk⟩ := exists_lift_gen (K := K) (fun i => (E i).idealSheaf) n (V j.castSucc)
        (hA1 _) j (pow_le_divisor E (n + 1) j) (pow_le_divisor E n j) (y j.castSucc) (hlevn j).1 (by
          intro hn0
          subst hn0
          refine ⟨J j.castSucc, MvPolynomial.eval₂Hom (σ 0 (tr 0 (V j.castSucc))) ![x j.castSucc, y j.castSucc],
            (hchn j.castSucc).1, by have h := (hchn j.castSucc).2; rw [zero_add, pow_one] at h; exact h, ?_, 1, 0, by decide, ?_, by simp⟩
          · exact (J_castSucc_cases j).elim Or.inl (fun h => Or.inr (Or.inr h))
          · exact J_castSucc_cases j)
      refine ⟨y', hy', fun j' hj' => ?_⟩
      have : j' = j := Fin.castSucc_injective _ hj'
      subst this; exact hk
    · obtain ⟨y1, hy1⟩ := hsurj c (y c)
      exact ⟨y1, hy1, fun j hj => absurd ⟨j, hj⟩ hc⟩
  have hJq : ∀ c, J c = Ideal.span {qchart K r c} := by
    intro c; simp only [J, qchart]; split_ifs <;> rfl
  have hle : (∏ i, (E i).idealSheaf) ^ (n + 1 + 1) ≤ (∏ i, (E i).idealSheaf) ^ (n + 1) :=
    pow_le_pow_right_of_le_one' le_top (by omega : n + 1 ≤ n + 1 + 1)
  have hchart : ∀ (c : Fin (r + 1)) (xc yc : Γ(S (n + 1), tr (n + 1) (V c))),
      ρ n (V c) xc = x c → ρ n (V c) yc = y c →
      (∀ j : Fin r, j.succ = c →
        RingHom.ker (inclSections (pow_le_divisor E (n + 1) j) (V c)) = Ideal.span {xc}) →
      (∀ j : Fin r, j.castSucc = c →
        RingHom.ker (inclSections (pow_le_divisor E (n + 1) j) (V c)) = Ideal.span {yc}) →
      Function.Surjective (MvPolynomial.eval₂Hom (σ (n + 1) (tr (n + 1) (V c))) ![xc, yc]) ∧
        RingHom.ker (MvPolynomial.eval₂Hom (σ (n + 1) (tr (n + 1) (V c))) ![xc, yc]) =
          J c ^ (n + 1 + 1) := by
    intro c xc yc hxc hyc hkx hky
    have hρ : (inclSections hle (V c)).comp
        (MvPolynomial.eval₂Hom (σ (n + 1) (tr (n + 1) (V c))) ![xc, yc]) =
        MvPolynomial.eval₂Hom (σ n (tr n (V c))) ![x c, y c] :=
      inclSections_comp_eval₂Hom sX hle (V c) hxc hyc
    obtain ⟨hs, hk⟩ := chart_surj_ker (K := K) hr (fun i => (E i).idealSheaf) n c (V c) (hA1 c)
      (fun k h1 h2 => hdisj c k h1 h2) (fun i => pow_le_divisor E (n + 1) i) _ _ hρ
      (hchn c).1 ((hchn c).2.trans (congrArg (fun I => I ^ (n + 1)) (hJq c))) xc yc (by simp) (by simp) hkx hky
    exact ⟨hs, by rw [hk, hJq]⟩
  have hfinal : ∀ c : Fin (r + 1), ∃ xc yc : Γ(S (n + 1), tr (n + 1) (V c)),
      ρ n (V c) xc = x c ∧ ρ n (V c) yc = y c ∧
      (∀ j : Fin r, j.succ = c →
        RingHom.ker (inclSections (pow_le_divisor E (n + 1) j) (V c)) = Ideal.span {xc}) ∧
      (∀ j : Fin r, j.castSucc = c →
        RingHom.ker (inclSections (pow_le_divisor E (n + 1) j) (V c)) = Ideal.span {yc}) ∧
      (c = 0 → RingHom.ker ((Scheme.IdealSheafData.inclusion (hZL (n + 1))).app
        (tr (n + 1) (V c))).hom = Ideal.span {xc}) ∧
      (c = Fin.last r → RingHom.ker ((Scheme.IdealSheafData.inclusion (hZR (n + 1))).app
        (tr (n + 1) (V c))).hom = Ideal.span {yc}) := by
    intro c
    obtain ⟨x1, hx1, hkx⟩ := liftx c
    obtain ⟨y1, hy1, hky⟩ := lifty c
    by_cases h0 : c = 0
    · subst h0
      obtain ⟨hs, hk⟩ := hchart 0 x1 y1 hx1 hy1 hkx hky
      obtain ⟨x'', hx'', hmk''⟩ := marking_left E ZL hZL hZL_succ sX hZL_curvilinear pL hZL_zero
        (V 0) hpL0 n (hA1 0) (x 0) (y 0) hmkn.1
        (((hchn 0).2.trans (congrArg (fun I => I ^ (n + 1)) (hJq 0))).trans (by simp [qchart]))
        x1 y1 hx1 hy1 hs
        (by rw [hk, hJq]; simp [qchart])
      refine ⟨x'', y1, hx'', hy1, fun j hj => absurd hj (Fin.succ_ne_zero j), hky, fun _ => hmk'', ?_⟩
      intro hl
      exact absurd hl (by
        intro h
        have := congrArg Fin.val h
        simp at this
        omega)
    · by_cases hl : c = Fin.last r
      · subst hl
        obtain ⟨hs, hk⟩ := hchart (Fin.last r) x1 y1 hx1 hy1 hkx hky
        obtain ⟨y'', hy'', hmk''⟩ := marking_right E ZR hZR hZR_succ sX hZR_curvilinear pR hZR_zero
          (V (Fin.last r)) hpR0 n (hA1 _) (x (Fin.last r)) (y (Fin.last r)) hmkn.2
          (((hchn (Fin.last r)).2.trans (congrArg (fun I => I ^ (n + 1)) (hJq _))).trans (by
            simp [qchart, h0]))
          x1 y1 hx1 hy1 hs
          (by rw [hk, hJq]; simp [qchart, h0])
        refine ⟨x1, y'', hx1, hy'', hkx, fun j hj => absurd hj (Fin.castSucc_lt_last j).ne,
          fun h => absurd h h0, fun _ => hmk''⟩
      · exact ⟨x1, y1, hx1, hy1, hkx, hky, fun h => absurd h h0, fun h => absurd h hl⟩
  choose xf yf hxf hyf hkxf hkyf hmL hmR using hfinal
  have hpre : ∀ W : X.Opens, (Scheme.IdealSheafData.inclusion hle) ⁻¹ᵁ (tr (n + 1) W) = tr n W := by
    intro W
    rw [← Scheme.Hom.comp_preimage]
    exact congrArg (fun f => f ⁻¹ᵁ W) (Scheme.IdealSheafData.inclusion_subschemeι hle)
  have hsurjf : Function.Surjective (Scheme.IdealSheafData.inclusion hle) :=
    (surjective_inclusion hle ((Scheme.IdealSheafData.support_pow_succ _ (n + 1)).trans
      (Scheme.IdealSheafData.support_pow_succ _ n).symm)).surj
  refine ⟨xf, yf, fun j => ⟨hxf j, hyf j⟩, ?_⟩
  refine ⟨fun j => hchart j (xf j) (yf j) (hxf j) (hyf j) (hkxf j) (hkyf j),
    ⟨hmL 0 rfl, hmR (Fin.last r) rfl⟩, fun j => ⟨?_, ?_⟩, fun j => ⟨hkyf j.castSucc j rfl, hkxf j.succ j rfl⟩⟩
  · refine eq_basicOpen_of_preimage (Scheme.IdealSheafData.inclusion hle) hsurjf
      (T := tr (n + 1) (V j.castSucc)) (W' := tr n (V j.castSucc)) (le_of_eq (hpre _).symm)
      (xf j.castSucc) (tr (n + 1) (V j.castSucc ⊓ V j.succ))
      (Scheme.Hom.preimage_mono _ inf_le_left) ?_ (hpre _).symm
    rw [hpre]
    exact (hovn j).1.trans (congrArg _ (hxf j.castSucc).symm)
  · refine eq_basicOpen_of_preimage (Scheme.IdealSheafData.inclusion hle) hsurjf
      (T := tr (n + 1) (V j.succ)) (W' := tr n (V j.succ)) (le_of_eq (hpre _).symm)
      (yf j.succ) (tr (n + 1) (V j.castSucc ⊓ V j.succ))
      (Scheme.Hom.preimage_mono _ inf_le_right) ?_ (hpre _).symm
    rw [hpre]
    exact (hovn j).2.trans (congrArg _ (hyf j.succ).symm)

private theorem lift_charts_to_thickenings
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 2 sX]
    [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]
    {r : ℕ} (hr : 0 < r) (E : Fin r → PrimeDivisor X) (b : Fin r → ℤ)
    (hinj : Function.Injective E)
    (hrat : ∀ i, IsSmoothRationalCurve sX (E i).idealSheaf)
    (hself : ∀ i, IsIntersectionNumber sX (Finsupp.single (E i) 1) (E i).idealSheaf (-(b i)))
    (hadj : ∀ i j : Fin r, i.val + 1 = j.val →
      IsIntersectionNumber sX (Finsupp.single (E i) 1) (E j).idealSheaf 1)
    (hfar : ∀ i j : Fin r, i.val + 1 < j.val → Disjoint (E i).support (E j).support)
    (pL pR : X) (hpLR : pL ≠ pR)
    (hpL : pL ∈ (E ⟨0, hr⟩).support) (hpL' : ∀ i, i ≠ ⟨0, hr⟩ → pL ∉ (E i).support)
    (hpR : pR ∈ (E ⟨r - 1, by omega⟩).support)
    (hpR' : ∀ i, i ≠ ⟨r - 1, by omega⟩ → pR ∉ (E i).support)
    (ZL ZR : ℕ → X.IdealSheafData)
    (hZL : ∀ n, (∏ i, (E i).idealSheaf) ^ (n + 1) ≤ ZL n)
    (hZR : ∀ n, (∏ i, (E i).idealSheaf) ^ (n + 1) ≤ ZR n)
    (hZL_succ : ∀ n, ZL n = ZL (n + 1) ⊔ (∏ i, (E i).idealSheaf) ^ (n + 1))
    (hZR_succ : ∀ n, ZR n = ZR (n + 1) ⊔ (∏ i, (E i).idealSheaf) ^ (n + 1))
    (hZL_zero : ((ZL 0).support : Set X) = {pL}) (hZR_zero : ((ZR 0).support : Set X) = {pR})
    (hZL_curvilinear : ∀ n, ∃ e : (ZL n).subscheme ≅
      Spec (.of (Polynomial K ⧸ Ideal.span {(Polynomial.X : Polynomial K) ^ (n + 1)})),
      e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K _)) = (ZL n).subschemeι ≫ sX)
    (hZR_curvilinear : ∀ n, ∃ e : (ZR n).subscheme ≅
      Spec (.of (Polynomial K ⧸ Ideal.span {(Polynomial.X : Polynomial K) ^ (n + 1)})),
      e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K _)) = (ZR n).subschemeι ≫ sX) :
    let I := ∏ i, (E i).idealSheaf
    -- the `(n+1)`-st thickening `(n+1)E` and the trace on it of an open of `X`
    let S : ℕ → Scheme.{u} := fun n => (I ^ (n + 1)).subscheme
    let tr : ∀ n, X.Opens → (S n).Opens := fun n V => (I ^ (n + 1)).subschemeι ⁻¹ᵁ V
    -- the constants `K → Γ((n+1)E, U)`
    let σ : ∀ n (U : (S n).Opens), K →+* Γ(S n, U) := fun n U =>
      ((Scheme.ΓSpecIso (.of K)).inv ≫
        ((I ^ (n + 1)).subschemeι ≫ sX).appLE ⊤ U le_top).hom
    -- the restriction `(n+2)E → (n+1)E`
    let ρ : ∀ n (V : X.Opens), Γ(S (n + 1), tr (n + 1) V) → Γ(S n, tr n V) := fun n V =>
      ((Scheme.IdealSheafData.inclusion (pow_le_pow_right_of_le_one' le_top
          (Nat.le_succ (n + 1)) : I ^ (n + 1 + 1) ≤ I ^ (n + 1))).appLE (tr (n + 1) V) (tr n V)
        (by
          simp only [tr, ← Scheme.Hom.comp_preimage,
            Scheme.IdealSheafData.inclusion_subschemeι, le_refl])).hom
    -- restriction to a smaller open of `X`
    let res : ∀ n (V W : X.Opens), W ≤ V → Γ(S n, tr n V) → Γ(S n, tr n W) :=
      fun n _ _ h => ((S n).presheaf.map (homOfLE (Scheme.Hom.preimage_mono _ h)).op).hom
    -- the exceptional ideal of chart `j`: `(y)`, `(x y)` or `(x)`
    let J : Fin (r + 1) → Ideal (MvPolynomial (Fin 2) K) := fun j =>
      if j = 0 then Ideal.span {MvPolynomial.X 1}
      else if j = Fin.last r then Ideal.span {MvPolynomial.X 0}
      else Ideal.span {MvPolynomial.X 0 * MvPolynomial.X 1}
    ∀ (V : Fin (r + 1) → X.Opens) (x0 y0 : ∀ j, Γ(S 0, tr 0 (V j))),
      (((I.support : Set X) ⊆ ⋃ j, (V j : Set X)) ∧
      (pL ∈ V 0 ∧ pR ∈ V (Fin.last r) ∧ (RingHom.ker ((Scheme.IdealSheafData.inclusion (hZL 0)).app (tr 0 (V 0))).hom =
            Ideal.span {x0 0} ∧
          RingHom.ker ((Scheme.IdealSheafData.inclusion (hZR 0)).app
            (tr 0 (V (Fin.last r)))).hom = Ideal.span {y0 (Fin.last r)})) ∧
      (∀ j, IsAffineOpen (tr 0 (V j)) ∧
      Function.Surjective (MvPolynomial.eval₂Hom (σ 0 (tr 0 (V j))) ![x0 j, y0 j]) ∧
      RingHom.ker (MvPolynomial.eval₂Hom (σ 0 (tr 0 (V j))) ![x0 j, y0 j]) = J j ^ (0 + 1)) ∧
      (∀ j : Fin r, ((V j.castSucc ⊓ V j.succ : X.Opens) : Set X) ∩ I.support ⊆ (E j).support) ∧ (∀ j : Fin r, tr 0 (V j.castSucc ⊓ V j.succ) = (S 0).basicOpen (x0 j.castSucc) ∧
        tr 0 (V j.castSucc ⊓ V j.succ) = (S 0).basicOpen (y0 j.succ)) ∧ (∀ j k : Fin (r + 1), j.val + 2 ≤ k.val →
      ((V j ⊓ V k : X.Opens) : Set X) ∩ I.support = ∅) ∧ (∀ j : Fin r, ∃ d : K, d ≠ 0 ∧
        res 0 (V j.succ) (V j.castSucc ⊓ V j.succ) inf_le_right (y0 j.succ) *
          res 0 (V j.castSucc) (V j.castSucc ⊓ V j.succ) inf_le_left (x0 j.castSucc) = σ 0 (tr 0 (V j.castSucc ⊓ V j.succ)) d) ∧
      LocalEquations E V x0 y0) →
    ∃ x y : ∀ j n, Γ(S n, tr n (V j)),
      (∀ j, x j 0 = x0 j ∧ y j 0 = y0 j) ∧ (∀ j n, ρ n (V j) (x j (n + 1)) = x j n ∧ ρ n (V j) (y j (n + 1)) = y j n) ∧
      (∀ j n, IsAffineOpen (tr n (V j)) ∧
      Function.Surjective (MvPolynomial.eval₂Hom (σ n (tr n (V j))) ![x j n, y j n]) ∧
      RingHom.ker (MvPolynomial.eval₂Hom (σ n (tr n (V j))) ![x j n, y j n]) = J j ^ (n + 1)) ∧ (∀ n, RingHom.ker ((Scheme.IdealSheafData.inclusion (hZL n)).app (tr n (V 0))).hom =
            Ideal.span {x 0 n} ∧
          RingHom.ker ((Scheme.IdealSheafData.inclusion (hZR n)).app
            (tr n (V (Fin.last r)))).hom = Ideal.span {y (Fin.last r) n}) ∧ (∀ j : Fin r, ∀ n, tr n (V j.castSucc ⊓ V j.succ) = (S n).basicOpen (x j.castSucc n) ∧
        tr n (V j.castSucc ⊓ V j.succ) = (S n).basicOpen (y j.succ n)) ∧
      (∀ n, LevelEq E V n (fun j => x j n) (fun j => y j n)) := by
  intro I S tr σ ρ res J V x0 y0 hP
  have hstep := lift_chart_step sX hr E b hinj hrat hself hadj hfar pL pR hpLR hpL hpL' hpR hpR' ZL ZR hZL hZR hZL_succ hZR_succ hZL_zero hZR_zero hZL_curvilinear hZR_curvilinear V x0 y0 hP
  have hP0 : ∀ j, IsAffineOpen (tr 0 (V j)) ∧ _ := hP.2.2.1
  have base : ChartInv sX E ZL ZR hZL hZR V 0 x0 y0 := by
    obtain ⟨-, ⟨-, -, hmk⟩, hch, -, hov, -, -, hLE⟩ := hP
    exact ⟨fun j => ⟨(hch j).2.1, (hch j).2.2⟩, hmk, hov, hLE.2.1⟩
  let seq : ∀ n, {p : (∀ j, Γ(S n, tr n (V j))) × (∀ j, Γ(S n, tr n (V j))) //
      ChartInv sX E ZL ZR hZL hZR V n p.1 p.2} := fun n =>
    Nat.rec ⟨(x0, y0), base⟩ (fun n ih =>
      ⟨(Classical.choose (hstep n ih.1.1 ih.1.2 ih.2),
        Classical.choose (Classical.choose_spec (hstep n ih.1.1 ih.1.2 ih.2))),
        (Classical.choose_spec (Classical.choose_spec (hstep n ih.1.1 ih.1.2 ih.2))).2⟩) n
  have hseq : ∀ n j, ρ n (V j) ((seq (n + 1)).1.1 j) = (seq n).1.1 j ∧
      ρ n (V j) ((seq (n + 1)).1.2 j) = (seq n).1.2 j := fun n j =>
    (Classical.choose_spec (Classical.choose_spec (hstep n (seq n).1.1 (seq n).1.2 (seq n).2))).1 j
  refine ⟨fun j n => (seq n).1.1 j, fun j n => (seq n).1.2 j, fun j => ⟨rfl, rfl⟩,
    fun j n => hseq n j,
    fun j n => ⟨isAffineOpen_tr_pow _ n _ (hP0 j).1, ((seq n).2.1 j).1, ((seq n).2.1 j).2⟩,
    fun n => (seq n).2.2.1,
    fun j n => ((seq n).2.2.2.1 j), fun n => (seq n).2.2.2.2⟩

private theorem transition_constants
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 2 sX]
    [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]
    {r : ℕ} (hr : 0 < r) (E : Fin r → PrimeDivisor X) (b : Fin r → ℤ)
    (hinj : Function.Injective E)
    (hrat : ∀ i, IsSmoothRationalCurve sX (E i).idealSheaf)
    (hself : ∀ i, IsIntersectionNumber sX (Finsupp.single (E i) 1) (E i).idealSheaf (-(b i)))
    (hadj : ∀ i j : Fin r, i.val + 1 = j.val →
      IsIntersectionNumber sX (Finsupp.single (E i) 1) (E j).idealSheaf 1)
    (hfar : ∀ i j : Fin r, i.val + 1 < j.val → Disjoint (E i).support (E j).support)
    (pL pR : X) (hpLR : pL ≠ pR)
    (hpL : pL ∈ (E ⟨0, hr⟩).support) (hpL' : ∀ i, i ≠ ⟨0, hr⟩ → pL ∉ (E i).support)
    (hpR : pR ∈ (E ⟨r - 1, by omega⟩).support)
    (hpR' : ∀ i, i ≠ ⟨r - 1, by omega⟩ → pR ∉ (E i).support)
    (ZL ZR : ℕ → X.IdealSheafData)
    (hZL : ∀ n, (∏ i, (E i).idealSheaf) ^ (n + 1) ≤ ZL n)
    (hZR : ∀ n, (∏ i, (E i).idealSheaf) ^ (n + 1) ≤ ZR n)
    (hZL_succ : ∀ n, ZL n = ZL (n + 1) ⊔ (∏ i, (E i).idealSheaf) ^ (n + 1))
    (hZR_succ : ∀ n, ZR n = ZR (n + 1) ⊔ (∏ i, (E i).idealSheaf) ^ (n + 1))
    (hZL_zero : ((ZL 0).support : Set X) = {pL}) (hZR_zero : ((ZR 0).support : Set X) = {pR})
    (hZL_curvilinear : ∀ n, ∃ e : (ZL n).subscheme ≅
      Spec (.of (Polynomial K ⧸ Ideal.span {(Polynomial.X : Polynomial K) ^ (n + 1)})),
      e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K _)) = (ZL n).subschemeι ≫ sX)
    (hZR_curvilinear : ∀ n, ∃ e : (ZR n).subscheme ≅
      Spec (.of (Polynomial K ⧸ Ideal.span {(Polynomial.X : Polynomial K) ^ (n + 1)})),
      e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K _)) = (ZR n).subschemeι ≫ sX) :
    let I := ∏ i, (E i).idealSheaf
    -- the `(n+1)`-st thickening `(n+1)E` and the trace on it of an open of `X`
    let S : ℕ → Scheme.{u} := fun n => (I ^ (n + 1)).subscheme
    let tr : ∀ n, X.Opens → (S n).Opens := fun n V => (I ^ (n + 1)).subschemeι ⁻¹ᵁ V
    -- the constants `K → Γ((n+1)E, U)`
    let σ : ∀ n (U : (S n).Opens), K →+* Γ(S n, U) := fun n U =>
      ((Scheme.ΓSpecIso (.of K)).inv ≫
        ((I ^ (n + 1)).subschemeι ≫ sX).appLE ⊤ U le_top).hom
    -- the restriction `(n+2)E → (n+1)E`
    let ρ : ∀ n (V : X.Opens), Γ(S (n + 1), tr (n + 1) V) → Γ(S n, tr n V) := fun n V =>
      ((Scheme.IdealSheafData.inclusion (pow_le_pow_right_of_le_one' le_top
          (Nat.le_succ (n + 1)) : I ^ (n + 1 + 1) ≤ I ^ (n + 1))).appLE (tr (n + 1) V) (tr n V)
        (by
          simp only [tr, ← Scheme.Hom.comp_preimage,
            Scheme.IdealSheafData.inclusion_subschemeι, le_refl])).hom
    -- restriction to a smaller open of `X`
    let res : ∀ n (V W : X.Opens), W ≤ V → Γ(S n, tr n V) → Γ(S n, tr n W) :=
      fun n _ _ h => ((S n).presheaf.map (homOfLE (Scheme.Hom.preimage_mono _ h)).op).hom
    -- the exceptional ideal of chart `j`: `(y)`, `(x y)` or `(x)`
    let J : Fin (r + 1) → Ideal (MvPolynomial (Fin 2) K) := fun j =>
      if j = 0 then Ideal.span {MvPolynomial.X 1}
      else if j = Fin.last r then Ideal.span {MvPolynomial.X 0}
      else Ideal.span {MvPolynomial.X 0 * MvPolynomial.X 1}
    ∀ (V : Fin (r + 1) → X.Opens) (x y : ∀ j n, Γ(S n, tr n (V j))),
      (((I.support : Set X) ⊆ ⋃ j, (V j : Set X)) ∧
      (pL ∈ V 0 ∧ pR ∈ V (Fin.last r) ∧ (RingHom.ker ((Scheme.IdealSheafData.inclusion (hZL 0)).app (tr 0 (V 0))).hom =
            Ideal.span {(fun j => x j 0) 0} ∧
          RingHom.ker ((Scheme.IdealSheafData.inclusion (hZR 0)).app
            (tr 0 (V (Fin.last r)))).hom = Ideal.span {(fun j => y j 0) (Fin.last r)})) ∧
      (∀ j, IsAffineOpen (tr 0 (V j)) ∧
      Function.Surjective (MvPolynomial.eval₂Hom (σ 0 (tr 0 (V j))) ![(fun j => x j 0) j, (fun j => y j 0) j]) ∧
      RingHom.ker (MvPolynomial.eval₂Hom (σ 0 (tr 0 (V j))) ![(fun j => x j 0) j, (fun j => y j 0) j]) = J j ^ (0 + 1)) ∧
      (∀ j : Fin r, ((V j.castSucc ⊓ V j.succ : X.Opens) : Set X) ∩ I.support ⊆ (E j).support) ∧ (∀ j : Fin r, tr 0 (V j.castSucc ⊓ V j.succ) = (S 0).basicOpen ((fun j => x j 0) j.castSucc) ∧
        tr 0 (V j.castSucc ⊓ V j.succ) = (S 0).basicOpen ((fun j => y j 0) j.succ)) ∧ (∀ j k : Fin (r + 1), j.val + 2 ≤ k.val →
      ((V j ⊓ V k : X.Opens) : Set X) ∩ I.support = ∅) ∧ (∀ j : Fin r, ∃ d : K, d ≠ 0 ∧
        res 0 (V j.succ) (V j.castSucc ⊓ V j.succ) inf_le_right ((fun j => y j 0) j.succ) *
          res 0 (V j.castSucc) (V j.castSucc ⊓ V j.succ) inf_le_left ((fun j => x j 0) j.castSucc) = σ 0 (tr 0 (V j.castSucc ⊓ V j.succ)) d) ∧
      LocalEquations E V (fun j => x j 0) (fun j => y j 0)) →
      (∀ n, LevelEq E V n (fun j => x j n) (fun j => y j n)) →
      (∀ j n, ρ n (V j) (x j (n + 1)) = x j n ∧ ρ n (V j) (y j (n + 1)) = y j n) →
      (∀ j n, IsAffineOpen (tr n (V j)) ∧
      Function.Surjective (MvPolynomial.eval₂Hom (σ n (tr n (V j))) ![x j n, y j n]) ∧
      RingHom.ker (MvPolynomial.eval₂Hom (σ n (tr n (V j))) ![x j n, y j n]) = J j ^ (n + 1)) → (∀ j : Fin r, ∀ n, tr n (V j.castSucc ⊓ V j.succ) = (S n).basicOpen (x j.castSucc n) ∧
        tr n (V j.castSucc ⊓ V j.succ) = (S n).basicOpen (y j.succ n)) →
      (∀ j : Fin r, ∃ c d : K, c ≠ 0 ∧ d ≠ 0 ∧
        res 0 (V j.succ) (V j.castSucc ⊓ V j.succ) inf_le_right (y j.succ 0) *
          res 0 (V j.castSucc) (V j.castSucc ⊓ V j.succ) inf_le_left (x j.castSucc 0) =
            σ 0 (tr 0 (V j.castSucc ⊓ V j.succ)) d ∧
        ∃ u : (Γ(S 1, tr 1 (V j.castSucc ⊓ V j.succ)))ˣ,
          (u : Γ(S 1, tr 1 (V j.castSucc ⊓ V j.succ))) =
            res 1 (V j.castSucc) (V j.castSucc ⊓ V j.succ) inf_le_left (x j.castSucc 1) ∧
          res 1 (V j.succ) (V j.castSucc ⊓ V j.succ) inf_le_right (x j.succ 1) =
            σ 1 (tr 1 (V j.castSucc ⊓ V j.succ)) c * ↑(u ^ b j) *
              res 1 (V j.castSucc) (V j.castSucc ⊓ V j.succ) inf_le_left (y j.castSucc 1)) := by
  intro I S tr σ ρ res J V x y hP hlev hcomp hchart hov j
  obtain ⟨c, d, hc, hd, h0, n, u, hu1, hu2, hann⟩ :=
    exists_transition_exponent sX hr E b hinj hrat hself hadj hfar pL pR hpLR hpL hpL' hpR hpR' ZL ZR hZL hZR hZL_succ hZR_succ hZL_zero hZR_zero hZL_curvilinear hZR_curvilinear V x y hP hlev hcomp hchart hov j
  obtain ⟨ε, hε, h2⟩ := pullback_invertibleSheaf_iso_twist sX hr E b hinj hrat hself hadj hfar pL pR hpLR hpL hpL' hpR hpR' ZL ZR hZL hZR hZL_succ hZR_succ hZL_zero hZR_zero hZL_curvilinear hZR_curvilinear V x y hP hlev hcomp hchart hov j c n u hc ⟨hu1, hu2⟩ hann
  have h3 := normal_pullback_twist sX (smoothScheme_of_smooth sX) (E j) (b j) (hself j) ε hε
  obtain ⟨φ2⟩ := h2
  obtain ⟨φ3⟩ := h3
  have hn : n = b j := by
    have := twist_iso_unique _ _ (φ2.symm ≪≫ φ3)
    omega
  subst hn
  exact ⟨c, d, hc, hd, h0, u, hu1, hu2⟩

private theorem primeDivisor_eq_of_support_subset {Y : Scheme.{u}} (Ea Eb : PrimeDivisor Y)
    (h : ((Eb.idealSheaf.support : Set Y)) ⊆ (Ea.idealSheaf.support : Set Y)) : Ea = Eb := by
  have hEa : (Ea.idealSheaf.support : Set Y) = closure {Ea.genericPoint} := Ea.support_eq_closure
  have hEb : (Eb.idealSheaf.support : Set Y) = closure {Eb.genericPoint} := Eb.support_eq_closure
  have hb : Eb.genericPoint ∈ (Ea.idealSheaf.support : Set Y) := h (by
    rw [hEb]; exact subset_closure rfl)
  rw [hEa] at hb
  have hs : Ea.genericPoint ⤳ Eb.genericPoint := specializes_iff_mem_closure.2 hb
  by_contra hne
  have hne' : Ea.genericPoint ≠ Eb.genericPoint := fun h => hne (PrimeDivisor.genericPoint_injective h)
  letI := specializationOrder Y
  have h1 := Ea.coheight_genericPoint
  have h2 := Eb.coheight_genericPoint
  have hle : Eb.genericPoint ≤ Ea.genericPoint := hs
  have hlt : Eb.genericPoint < Ea.genericPoint := lt_of_le_of_ne hle (Ne.symm hne')
  have := Order.coheight_strictAnti hlt (by rw [h1]; exact ENat.natCast_lt_top 1)
  rw [h1, h2] at this
  exact lt_irrefl _ this

private theorem ideal_top_or_prime {Y : Scheme.{u}} (D : PrimeDivisor Y) (W : Y.affineOpens) :
    D.idealSheaf.ideal W = ⊤ ∨ ((D.idealSheaf.ideal W).IsPrime ∧
      ∃ p, p ∈ W.1 ∧ p ∈ (D.idealSheaf.support : Set Y)) := by
  have hint := D.integral
  rw [← Scheme.IdealSheafData.ker_subschemeι_app (I := D.idealSheaf) W]
  by_cases hne : Nonempty (D.idealSheaf.subschemeι ⁻¹ᵁ W.1)
  · right
    haveI : IsDomain Γ(D.idealSheaf.subscheme, D.idealSheaf.subschemeι ⁻¹ᵁ W.1) := inferInstance
    refine ⟨RingHom.ker_isPrime _, ?_⟩
    obtain ⟨s, hs⟩ := hne
    refine ⟨D.idealSheaf.subschemeι s, hs, ?_⟩
    rw [← D.idealSheaf.range_subschemeι]; exact ⟨s, rfl⟩
  · left
    haveI : IsEmpty (D.idealSheaf.subschemeι ⁻¹ᵁ W.1) := not_nonempty_iff.1 hne
    haveI : Subsingleton Γ(D.idealSheaf.subscheme, D.idealSheaf.subschemeι ⁻¹ᵁ W.1) := by
      have : D.idealSheaf.subschemeι ⁻¹ᵁ W.1 = ⊥ := by
        refine eq_bot_iff.2 fun s hs => ?_
        exact (hne ⟨(⟨s, hs⟩ : D.idealSheaf.subschemeι ⁻¹ᵁ W.1)⟩).elim
      rw [this]; infer_instance
    rw [Ideal.eq_top_iff_one, RingHom.mem_ker]
    exact Subsingleton.elim _ _

section InfMul

private theorem inf_le_mul_primeDivisor {Y : Scheme.{u}} (Ea Eb : PrimeDivisor Y)
    [Stacks.Divisors.IsEffectiveCartierDivisor Ea.idealSheaf] (hne : Ea ≠ Eb) :
    Ea.idealSheaf ⊓ Eb.idealSheaf ≤ Ea.idealSheaf * Eb.idealSheaf := by
  have hloc : ∀ y : Y, ∃ (W : Y.Opens) (hW : IsAffineOpen W), y ∈ W ∧
      ∃ f : Γ(Y, W), Ea.idealSheaf.ideal ⟨W, hW⟩ = Ideal.span {f} := fun y => by
    obtain ⟨W, hW, hy, -, f, -, h⟩ := exists_local_gen Ea.idealSheaf ⊤ y trivial
    exact ⟨W, hW, hy, f, h⟩
  choose W hW hyW f hf using hloc
  refine Scheme.IdealSheafData.le_of_iSup_eq_top (fun y => ⟨W y, hW y⟩) ?_ ?_
  · refine eq_top_iff.2 fun y _ => ?_
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨y, hyW y⟩
  · intro y
    rw [Scheme.IdealSheafData.ideal_inf, Scheme.IdealSheafData.ideal_mul]
    rintro x ⟨hxa, hxb⟩
    have hxa' : x ∈ Ideal.span {f y} := by rw [← hf y]; exact hxa
    rw [Ideal.mem_span_singleton'] at hxa'
    obtain ⟨u, rfl⟩ := hxa'
    rcases ideal_top_or_prime Eb ⟨W y, hW y⟩ with htop | ⟨hp, p, hpW, hpS⟩
    · rw [Pi.mul_apply, htop, Ideal.mul_top]; exact hxa
    · by_cases hfb : f y ∈ Eb.idealSheaf.ideal ⟨W y, hW y⟩
      · exfalso
        have hle : Ea.idealSheaf.ideal ⟨W y, hW y⟩ ≤ Eb.idealSheaf.ideal ⟨W y, hW y⟩ := by
          rw [hf y, Ideal.span_le]; simpa using hfb
        have hsub : ∀ q, q ∈ (W y) → q ∈ (Eb.idealSheaf.support : Set Y) →
            q ∈ (Ea.idealSheaf.support : Set Y) := by
          intro q hq hqb
          have hqb' : q ∈ Eb.idealSheaf.supportSet := hqb
          show q ∈ Ea.idealSheaf.supportSet
          rw [Scheme.IdealSheafData.mem_supportSet_iff_of_mem (U := ⟨W y, hW y⟩) hq] at hqb' ⊢
          exact Y.zeroLocus_mono (U := W y) (s := (Ea.idealSheaf.ideal ⟨W y, hW y⟩ : Set _)) (t := (Eb.idealSheaf.ideal ⟨W y, hW y⟩ : Set _)) hle hqb'
        have hEb : (Eb.idealSheaf.support : Set Y) = closure {Eb.genericPoint} := Eb.support_eq_closure
        have hη : Eb.genericPoint ∈ W y := by
          have hp' : p ∈ closure {Eb.genericPoint} := by rw [← hEb]; exact hpS
          by_contra hn
          have := (mem_closure_iff.1 hp') (W y : Set Y) (W y).isOpen hpW
          obtain ⟨z, hz1, hz2⟩ := this
          rw [Set.mem_singleton_iff] at hz2; subst hz2; exact hn hz1
        have hηa : Eb.genericPoint ∈ (Ea.idealSheaf.support : Set Y) :=
          hsub _ hη (by rw [hEb]; exact subset_closure rfl)
        have : (Eb.idealSheaf.support : Set Y) ⊆ (Ea.idealSheaf.support : Set Y) := by
          rw [hEb]
          exact closure_minimal (by simpa using hηa) Ea.idealSheaf.support.isClosed
        exact hne (primeDivisor_eq_of_support_subset Ea Eb this)
      · have hu : u ∈ Eb.idealSheaf.ideal ⟨W y, hW y⟩ := by
          rcases hp.mem_or_mem hxb with h | h
          · exact h
          · exact absurd h hfb
        rw [Pi.mul_apply, mul_comm u (f y)]
        exact Ideal.mul_mem_mul (by rw [hf y]; exact Ideal.mem_span_singleton_self _) hu

end InfMul

private theorem map_comap_eq {Y : Scheme.{u}} {I₂ D : Y.IdealSheafData} (h : I₂ ≤ D) :
    (D.comap I₂.subschemeι).map I₂.subschemeι = D := by
  rw [comap_eq_ker_inclusion D I₂ h, Scheme.IdealSheafData.map_ker,
    Scheme.IdealSheafData.inclusion_subschemeι, Scheme.IdealSheafData.ker_subschemeι]

private theorem ker_inf_eq_bot {Y : Scheme.{u}} {I₂ Ea Eb : Y.IdealSheafData} (ha : I₂ ≤ Ea)
    (hb : I₂ ≤ Eb) (V : Y.Opens)
    (hW : ∀ W : Y.affineOpens, W.1 ≤ V → Ea.ideal W ⊓ Eb.ideal W ≤ I₂.ideal W) :
    RingHom.ker (inclSections ha V) ⊓ RingHom.ker (inclSections hb V) = ⊥ := by
  rw [eq_bot_iff]
  rintro z ⟨hza, hzb⟩
  have hloc : ∀ p : (I₂.subschemeι ⁻¹ᵁ V : I₂.subscheme.Opens),
      ∃ (W : Y.Opens) (hW : IsAffineOpen W), I₂.subschemeι p.1 ∈ W ∧ W ≤ V := by
    intro p
    obtain ⟨-, ⟨A, hA, rfl⟩, hpA, hAsub⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
      (show I₂.subschemeι p.1 ∈ (V : Set Y) from p.2) V.isOpen
    exact ⟨A, hA, hpA, hAsub⟩
  choose W hWaff hpW hWV using hloc
  refine TopCat.Sheaf.eq_of_locally_eq' (F := I₂.subscheme.sheaf)
    (U := fun p => I₂.subschemeι ⁻¹ᵁ W p) (I₂.subschemeι ⁻¹ᵁ V)
    (fun p => homOfLE (Scheme.Hom.preimage_mono _ (hWV p))) ?_ _ 0 ?_
  · intro p hp
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨p, hp⟩, hpW ⟨p, hp⟩⟩
  · intro p
    set Wp : Y.affineOpens := ⟨W p, hWaff p⟩
    have hU : IsAffineOpen (I₂.subschemeι ⁻¹ᵁ W p) := (hWaff p).preimage _
    set zW := (I₂.subscheme.presheaf.map (homOfLE (Scheme.Hom.preimage_mono _ (hWV p))).op).hom z
    have hza' : zW ∈ RingHom.ker (inclSections ha (W p)) := by
      rw [RingHom.mem_ker, ← inclSections_restrict ha (hWV p) z]
      have : inclSections ha V z = 0 := hza
      rw [this, map_zero]
    have hzb' : zW ∈ RingHom.ker (inclSections hb (W p)) := by
      rw [RingHom.mem_ker, ← inclSections_restrict hb (hWV p) z]
      have : inclSections hb V z = 0 := hzb
      rw [this, map_zero]
    obtain ⟨w, hw⟩ := Scheme.IdealSheafData.subschemeι_app_surjective (I := I₂) Wp zW
    have hmem : ∀ (D : Y.IdealSheafData) (hD : I₂ ≤ D),
        zW ∈ RingHom.ker (inclSections hD (W p)) → w ∈ D.ideal Wp := by
      intro D hD hz
      rw [ker_inclSections_eq_comap hD (W p) hU] at hz
      have := Scheme.IdealSheafData.ideal_map (D.comap I₂.subschemeι) I₂.subschemeι Wp hU
      rw [map_comap_eq hD] at this
      rw [this]
      show (I₂.subschemeι.app Wp).hom w ∈ (D.comap I₂.subschemeι).ideal ⟨_, hU⟩
      rw [hw]; exact hz
    have hwI : w ∈ I₂.ideal Wp := hW Wp (hWV p) ⟨hmem Ea ha hza', hmem Eb hb hzb'⟩
    rw [← Scheme.IdealSheafData.ker_subschemeι_app, RingHom.mem_ker] at hwI
    change zW = _
    rw [← hw]; exact (hwI.trans (map_zero _).symm)

private theorem ideal_eq_top_of_disjoint {Y : Scheme.{u}} (D : Y.IdealSheafData) (W : Y.affineOpens)
    (h : ∀ y ∈ W.1, y ∉ (D.support : Set Y)) : D.ideal W = ⊤ := by
  have hb : D.subschemeι ⁻¹ᵁ W.1 = ⊥ := preimage_eq_bot_of_disjoint D W.1 h
  rw [← Scheme.IdealSheafData.ker_subschemeι_app (I := D) W]
  haveI : Subsingleton Γ(D.subscheme, D.subschemeι ⁻¹ᵁ W.1) := by rw [hb]; infer_instance
  rw [Ideal.eq_top_iff_one, RingHom.mem_ker]
  exact Subsingleton.elim _ _

private theorem inf_ideal_le_prod {Y : Scheme.{u}} {r : ℕ} (E : Fin r → PrimeDivisor Y) (a b : Fin r)
    (hab : a ≠ b) [Stacks.Divisors.IsEffectiveCartierDivisor (E a).idealSheaf]
    (hne : E a ≠ E b) (W : Y.affineOpens)
    (hother : ∀ k, k ≠ a → k ≠ b → (E k).idealSheaf.ideal W = ⊤) :
    (E a).idealSheaf.ideal W ⊓ (E b).idealSheaf.ideal W ≤ (∏ i, (E i).idealSheaf).ideal W := by
  have h1 := inf_le_mul_primeDivisor (E a) (E b) hne
  have h2 : (E a).idealSheaf.ideal W ⊓ (E b).idealSheaf.ideal W ≤
      (E a).idealSheaf.ideal W * (E b).idealSheaf.ideal W := by
    have := Scheme.IdealSheafData.le_def.1 h1 W
    simpa only [Scheme.IdealSheafData.ideal_inf, Scheme.IdealSheafData.ideal_mul, Pi.inf_apply,
      Pi.mul_apply] using this
  rw [ideal_prod_apply Finset.univ (fun i => (E i).idealSheaf) W,
    Finset.prod_eq_mul a b hab (fun c _ hc => (hother c hc.1 hc.2).trans Ideal.one_eq_top.symm) (fun h => absurd (Finset.mem_univ a) h) (fun h => absurd (Finset.mem_univ b) h)]
  exact h2

private theorem exists_basis_first {k : Type u} [Field k] {M : Type*} [AddCommGroup M] [Module k M]
    (hfin : Module.finrank k M = 2) (χ : M) (hχ : χ ≠ 0) :
    ∃ b : Module.Basis (Fin (1 + 1)) k M, b 0 = χ := by
  have : Module.Finite k M := Module.finite_of_finrank_eq_succ hfin
  have hspan : Submodule.span k {χ} ≠ ⊤ := by
    intro h
    have := finrank_span_singleton (K := k) hχ
    rw [h, finrank_top, hfin] at this
    omega
  obtain ⟨v, hv⟩ : ∃ v, v ∉ Submodule.span k {χ} := by
    by_contra hcon
    exact hspan (eq_top_iff.2 fun v _ => by_contra fun hv => hcon ⟨v, hv⟩)
  have hli : LinearIndependent k ![χ, v] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero, smul_eq_zero] at hst
      exact ⟨hst.resolve_right hχ, rfl⟩
    · exfalso
      apply hv
      have : v = (-(t⁻¹ * s)) • χ :=
        calc v = t⁻¹ • (t • v) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
          _ = _ := by rw [eq_neg_of_add_eq_zero_right hst, smul_neg, smul_smul, neg_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self χ)
  have hcard : Fintype.card (Fin (1 + 1)) = Module.finrank k M := by simp [hfin]
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli hcard, ?_⟩
  simp

open Stacks.ProjectiveFromSections Stacks.AlgebraicGeometry.ProjPolyChart
  AlgebraicGeometry.ProjectiveLineCriterion in
private theorem p1_core {K : Type u} [Field K] {C : Scheme.{u}} (f : C ⟶ Spec (.of K))
    [IsProper f] [AlgebraicGeometry.IsIntegral C]
    [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop)] (hdim : topologicalKrullDim C ≤ 1)
    (hgenus : genus f = 0) (L : C.Modules) [Stacks.Ample.IsInvertibleModule C L]
    (hdeg : invertibleCurveDegree K f hdim L = 1) (χ : Γ(L, ⊤)) (hχ : χ ≠ 0) :
    IsAffineOpen (nvOpen L χ) ∧ ∃ e : Γ(C, nvOpen L χ) ≃+* Polynomial K,
      ∀ c, e (((Scheme.ΓSpecIso (.of K)).inv ≫ f.appLE ⊤ (nvOpen L χ) le_top).hom c) =
        Polynomial.C c := by
  let M := (restrictScalarsOverBase K f).obj
    ((SheafOfModules.evaluation C.ringCatSheaf (op (⊤ : C.Opens))).obj L)
  have hfin : Module.finrank K M = 2 := by
    have := AlgebraicGeometry.finrank_globalSections_eq_invertibleCurveDegree_add_one K f hdim L
      hgenus (by rw [hdeg]; norm_num)
    rw [hdeg] at this
    exact_mod_cast this
  obtain ⟨b, hb⟩ := exists_basis_first hfin (show M from χ) hχ
  obtain ⟨hs, -⟩ := isClosedImmersion_toPolynomialModel_of_basis f hdim hgenus L
    (d := 1) (by exact_mod_cast hdeg) one_pos b
  have hiso := isIso_toPolynomialModel_of_degree_eq_one f hdim hgenus L hdeg b hs
  set φ := Stacks.ProjectiveSpaceChartRatio.toPolynomialModel
    (fun j => (show Γ(L, ⊤) from b j)) hs f with hφ
  have hpre := AlgebraicGeometry.PlaneConic.preimage_basicOpen_toPolynomialModel
    (fun j => (show Γ(L, ⊤) from b j)) hs f 0
  have hdeg0 := X_mem_one K 1 0
  set D : (AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) K)).Opens :=
    Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) K) (MvPolynomial.X 0) with hD
  have hDaff : IsAffineOpen D := by
    have := Proj.opensRange_awayι (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) K)
      (MvPolynomial.X 0) hdeg0 Nat.one_pos
    rw [hD, ← this]; exact isAffineOpen_opensRange _
  have hU : nvOpen L χ = φ ⁻¹ᵁ D := by
    rw [hD]
    refine Eq.trans ?_ hpre.symm
    show nvOpen L χ = nvOpen L (b 0)
    rw [hb]
  haveI := hiso
  refine ⟨hU ▸ hDaff.preimage φ, ?_⟩
  haveI : IsIso (φ.app D) := inferInstance
  let eG : Γ(AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) K), D) ≃+*
      Γ(C, φ ⁻¹ᵁ D) := (asIso (φ.app D)).commRingCatIsoToRingEquiv
  have hcomp : φ ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff K 1 = f :=
    Stacks.ProjectiveSpaceChartRatio.toPolynomialModel_comp_projToSpecCoeff _ hs f
  suffices H : ∀ U : C.Opens, U = φ ⁻¹ᵁ D → ∃ e : Γ(C, U) ≃+* Polynomial K,
      ∀ c, e (((Scheme.ΓSpecIso (.of K)).inv ≫ f.appLE ⊤ U le_top).hom c) = Polynomial.C c from
    H _ hU
  intro U hUe
  subst hUe
  refine ⟨eG.symm.trans ((Stacks.ProjectiveChart.sectionsChartEquiv K 0).symm.trans
    (MvPolynomial.uniqueAlgEquiv K (Fin 1)).toRingEquiv), fun c => ?_⟩
  have key := map_constants_hom f (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff K 1) φ
    hcomp (φ ⁻¹ᵁ D) D le_rfl c
  have h1 : eG (((Scheme.ΓSpecIso (.of K)).inv ≫
      (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff K 1).appLE ⊤ D le_top).hom c) =
      ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appLE ⊤ (φ ⁻¹ᵁ D) le_top).hom c := by
    rw [← map_constants_hom f (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff K 1) φ
      hcomp (φ ⁻¹ᵁ D) D le_rfl c, Scheme.Hom.appLE_eq_app]
    rfl
  have h2 := Stacks.ProjectiveChart.sectionsChartEquiv_C (R := K) (n := 1) 0 c
  rw [← h1]
  simp only [RingEquiv.trans_apply, RingEquiv.symm_apply_apply]
  have h3 : ((Scheme.ΓSpecIso (.of K)).inv ≫
      (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff K 1).appLE ⊤ D le_top).hom c =
      Stacks.ProjectiveChart.sectionsChartEquiv K 0 (MvPolynomial.C c) := h2.symm
  rw [h3, RingEquiv.symm_apply_apply]
  simp

open Stacks.ProjectiveFromSections Stacks.Divisors in
private theorem nvOpen_eq_compl {C : Scheme.{u}} [AlgebraicGeometry.IsIntegral C] (L : C.Modules)
    [SheafOfModules.IsInvertible C.sheaf.obj C.ringCatSheaf.property L]
    [Stacks.Ample.IsInvertibleModule C L] (s : L.sections) (hs : s.eval (op ⊤) ≠ 0) :
    ((nvOpen L (s.eval (op ⊤)) : C.Opens) : Set C) =
      ((Stacks.Divisors.zeroScheme C L (s.eval (op ⊤))).supportSet)ᶜ := by
  have hcompl := AlgebraicGeometry.nonvanishingLocus_eq_compl_supportSet_zeroScheme L s hs
  rw [Stacks.NonvanishingSpelling.stalkNonvanishingLocus_eq C L s] at hcompl
  exact hcompl

open Stacks.AlgebraicGeometry.ProjPolyChart CategoryTheory.Limits in
private theorem over_iso_of_rational {K : Type u} [Field K] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of K))
    {C : Y.IdealSheafData} (hrat : IsSmoothRationalCurve sY C) :
    Nonempty (Over.mk (C.subschemeι ≫ sY) ≅
      Over.mk (projectiveSpaceOver 1 (Spec (.of K)) ↘ Spec (.of K))) := by
  obtain ⟨eP, heP⟩ := hrat.2
  let e : C.subscheme ≅ AlgebraicGeometry.Proj (polyGrading K 1) :=
    eP.symm ≪≫ projectiveLineIsoProj K
  have he : e.hom ≫ projToSpecCoeff K 1 = C.subschemeι ≫ sY := by
    simp only [e, Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [projectiveLineIsoProj_hom_comp_projToSpecCoeff, ← heP, Iso.inv_hom_id_assoc]
  let c := (Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison K 1).iso
  refine ⟨Over.isoMk (e ≪≫ c.symm) ?_⟩
  change (e.hom ≫ c.inv) ≫ pullback.fst _ _ = _
  rw [← he, Category.assoc,
    ← Stacks.ProjectiveSpaceChartRatio.polynomialComparison_iso_hom_comp_projToSpecCoeff K 1,
    Iso.inv_hom_id_assoc]
  rfl

open MMP.Resolution.Bridges MMP.Mori Stacks.ProjectiveFromSections
  AlgebraicGeometry.ProjectiveLineCriterion in
private theorem p1_node {K : Type u} [Field K] [IsAlgClosed K] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of K)) [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y]
    (hsm : IsSmoothScheme sY) (Ea Eb : PrimeDivisor Y)
    [hcart : Stacks.Divisors.IsEffectiveCartierDivisor Ea.idealSheaf]
    (hrat : IsSmoothRationalCurve sY Eb.idealSheaf)
    (hDC : ¬ Eb.idealSheaf.supportSet ⊆ Ea.idealSheaf.supportSet)
    (hnum : IsIntersectionNumber sY (Finsupp.single Ea 1) Eb.idealSheaf (1 : ℤ))
    (V : Y.Opens) (hV : ∀ z : Eb.idealSheaf.subscheme,
      Eb.idealSheaf.subschemeι z ∈ V ↔ Eb.idealSheaf.subschemeι z ∉ (Ea.idealSheaf.support : Set Y)) :
    IsAffineOpen (Eb.idealSheaf.subschemeι ⁻¹ᵁ V) ∧
      ∃ e : Γ(Eb.idealSheaf.subscheme, Eb.idealSheaf.subschemeι ⁻¹ᵁ V) ≃+* Polynomial K,
        ∀ c, e (sigmaSub sY Eb.idealSheaf V c) = Polynomial.C c := by
  obtain ⟨hprop, hdim1, hdeg⟩ := degreeOn_invertibleSheaf_eq sY hsm Ea Eb.idealSheaf 1 (by exact_mod_cast hnum)
  obtain ⟨eO⟩ := over_iso_of_rational sY hrat
  haveI := isProper_of_iso_projectiveLine eO
  haveI := isCurve_of_iso_projectiveLine eO
  haveI : AlgebraicGeometry.IsIntegral Eb.idealSheaf.subscheme := Eb.integral
  haveI := isIso_globalSections_of_iso_projectiveLine eO
  have hgenus := genus_of_iso_projectiveLine eO
  set L := (Scheme.Modules.pullback Eb.idealSheaf.subschemeι).obj
    (Stacks.Divisors.invertibleSheaf' Ea.idealSheaf) with hL
  have hdeg2 : invertibleCurveDegree K (Eb.idealSheaf.subschemeι ≫ sY) hdim1 L = 1 := hdeg
  have hχ := Stacks.Models.pullbackCanonicalSection_subschemeι_ne_zero Eb.idealSheaf Ea.idealSheaf hDC
  set χ := Stacks.Divisors.pullbackCanonicalSection Eb.idealSheaf.subschemeι Ea.idealSheaf with hχdef
  have hs0 : (Stacks.Divisors.sectionsOfTop L χ).eval (op ⊤) = χ :=
    Stacks.Divisors.sectionsOfTop_eval_top _ _
  have hs1 : (Stacks.Divisors.sectionsOfTop L χ).eval (op ⊤) ≠ 0 := by rw [hs0]; exact hχ
  have hset := nvOpen_eq_compl L (Stacks.Divisors.sectionsOfTop L χ) hs1
  rw [hs0] at hset
  have hzs := Stacks.Divisors.zeroScheme_sectionsOfTop_pullbackCanonicalSection
    Eb.idealSheaf.subschemeι Ea.idealSheaf
  rw [hs0] at hzs
  rw [hzs] at hset
  have hU : nvOpen L χ = Eb.idealSheaf.subschemeι ⁻¹ᵁ V := by
    refine SetLike.coe_injective ?_
    rw [hset]
    ext z
    simp only [Set.mem_compl_iff]
    have h1 : z ∈ (Ea.idealSheaf.comap Eb.idealSheaf.subschemeι).supportSet ↔
        Eb.idealSheaf.subschemeι z ∈ (Ea.idealSheaf.support : Set Y) := by
      have := Scheme.IdealSheafData.support_comap Ea.idealSheaf Eb.idealSheaf.subschemeι
      constructor
      · intro h
        have h' : z ∈ ((Ea.idealSheaf.comap Eb.idealSheaf.subschemeι).support : Set _) := h
        rw [this] at h'; exact h'
      · intro h
        show z ∈ ((Ea.idealSheaf.comap Eb.idealSheaf.subschemeι).support : Set _)
        rw [this]; exact h
    rw [h1]
    exact (hV z).symm
  obtain ⟨hA, e, he⟩ := p1_core (Eb.idealSheaf.subschemeι ≫ sY) hdim1 hgenus L hdeg2 χ hχ
  rw [hU] at hA
  refine ⟨hA, ?_⟩
  suffices H : ∀ U : Y.Opens, ∀ Ue : (Eb.idealSheaf.subscheme).Opens, Ue = nvOpen L χ → Ue = Eb.idealSheaf.subschemeι ⁻¹ᵁ V →
    ∃ e : Γ(Eb.idealSheaf.subscheme, Ue) ≃+* Polynomial K, ∀ c, e (((Scheme.ΓSpecIso (.of K)).inv ≫
      (Eb.idealSheaf.subschemeι ≫ sY).appLE ⊤ Ue le_top).hom c) = Polynomial.C c from
    H V _ hU.symm rfl
  intro U Ue h1 h2
  subst h1
  exact ⟨e, he⟩

open MMP.Resolution.Bridges MMP.Mori Stacks.ProjectiveFromSections
  AlgebraicGeometry.ProjectiveLineCriterion AlgebraicGeometry in
private theorem p1_point_aux {K : Type u} [Field K] [IsAlgClosed K] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of K))
    (eO : Over.mk f ≅ Over.mk (projectiveSpaceOver 1 (Spec (.of K)) ↘ Spec (.of K)))
    (q : C) (hq : IsClosed ({q} : Set C)) (U : C.Opens) (hU : ∀ z : C, z ∈ U ↔ z ≠ q) :
    IsAffineOpen U ∧ ∃ e : Γ(C, U) ≃+* Polynomial K,
        ∀ c, e (((Scheme.ΓSpecIso (.of K)).inv ≫ f.appLE ⊤ U le_top).hom c) = Polynomial.C c := by
  haveI := isProper_of_iso_projectiveLine eO
  haveI := isCurve_of_iso_projectiveLine eO
  haveI := smooth_of_iso_projectiveLine eO
  haveI := isIso_globalSections_of_iso_projectiveLine eO
  have hgenus := genus_of_iso_projectiveLine eO
  have hdim : topologicalKrullDim C ≤ 1 :=
    le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := f))
  let s := pointOfClosedPoint f q hq
  have hs : s ≫ f = 𝟙 _ := pointOfClosedPoint_comp f q hq
  obtain ⟨p⟩ : Nonempty (Spec (.of K)) := inferInstance
  obtain ⟨hcl, hnorm, hfin⟩ := normalRationalPoint_of_section f s hs p
  have hsp : s p = q := pointOfClosedPoint_apply f q hq p
  rw [hsp] at hcl hnorm hfin
  haveI hC : Stacks.Divisors.IsEffectiveCartierDivisor
      (Scheme.IdealSheafData.vanishingIdeal (⟨{q}, hq⟩ : TopologicalSpace.Closeds C)) :=
    ((isEffectiveCartierDivisor_closedPoint_tfae_of_isCurve K f hq).out 2 4).mp hnorm
  set D := Scheme.IdealSheafData.vanishingIdeal (⟨{q}, hq⟩ : TopologicalSpace.Closeds C) with hDdef
  set L := Stacks.Divisors.modulesInvertibleSheaf D with hLdef
  set s' := Stacks.Divisors.canonicalSections D with hsdef
  haveI hLs : SheafOfModules.IsInvertible C.sheaf.obj C.ringCatSheaf.property L :=
    Stacks.Divisors.isInvertible_invertibleSheaf D
  obtain ⟨y, hyx⟩ := Stacks.ProjectiveSpaceSections.exists_ne_of_isCurve f q
  have hs0 : s'.eval (op ⊤) ≠ 0 := by
    refine eval_top_ne_zero_of_mem_nonvanishingLocus L s' (x := y) ?_
    change y ∈ Stacks.SheafOfModules.nonvanishingLocus (X := C.toRingedSpace)
      (Stacks.Divisors.invertibleSheaf D) (Stacks.Divisors.canonicalSections D)
    rw [Stacks.Divisors.nonvanishingLocus_canonicalSections, hDdef,
      supportSet_vanishingIdeal_singleton hq]
    exact hyx
  have hdeg := invertibleCurveDegree_modulesInvertibleSheaf_vanishingIdeal_singleton f hdim hq
  have hdeg1 : invertibleCurveDegree K f hdim L = 1 := by
    rw [hdeg]; exact_mod_cast hfin
  have hset := nvOpen_eq_compl L s' hs0
  have hz : Stacks.Divisors.zeroScheme C L (s'.eval (op ⊤)) = D :=
    Stacks.Divisors.zeroScheme_canonicalSections D
  have hsupp : D.supportSet = {q} := supportSet_vanishingIdeal_singleton hq
  rw [hz, hsupp] at hset
  have hUe : nvOpen L (s'.eval (op ⊤)) = U := by
    refine SetLike.coe_injective ?_
    rw [hset]
    ext z
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact (hU z).symm
  obtain ⟨hA, e, he⟩ := p1_core f hdim hgenus L hdeg1 (s'.eval (op ⊤)) hs0
  subst hUe
  exact ⟨hA, e, he⟩

private theorem p1_point {K : Type u} [Field K] [IsAlgClosed K] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of K)) {C : Y.IdealSheafData} (hrat : IsSmoothRationalCurve sY C)
    (q : C.subscheme) (hq : IsClosed ({q} : Set C.subscheme)) (V : Y.Opens)
    (hV : ∀ z : C.subscheme, C.subschemeι z ∈ V ↔ z ≠ q) :
    IsAffineOpen (C.subschemeι ⁻¹ᵁ V) ∧
      ∃ e : Γ(C.subscheme, C.subschemeι ⁻¹ᵁ V) ≃+* Polynomial K,
        ∀ c, e (sigmaSub sY C V c) = Polynomial.C c := by
  obtain ⟨eO⟩ := over_iso_of_rational sY hrat
  exact p1_point_aux (C.subschemeι ≫ sY) eO q hq (C.subschemeι ⁻¹ᵁ V) hV

section Union

open CategoryTheory.Limits

private theorem isAffineOpen_of_two {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    {I Ea Eb : Y.IdealSheafData} (ha : I ≤ Ea) (hb : I ≤ Eb) (V : Y.Opens)
    (hsupp : ∀ y ∈ V, y ∈ (I.support : Set Y) →
      y ∈ (Ea.support : Set Y) ∨ y ∈ (Eb.support : Set Y))
    (hA : IsAffineOpen (Ea.subschemeι ⁻¹ᵁ V)) (hB : IsAffineOpen (Eb.subschemeι ⁻¹ᵁ V)) :
    IsAffineOpen (I.subschemeι ⁻¹ᵁ V) := by
  set U := I.subschemeι ⁻¹ᵁ V with hU
  let fa := Scheme.IdealSheafData.inclusion ha
  let fb := Scheme.IdealSheafData.inclusion hb
  have hpa : fa ⁻¹ᵁ U = Ea.subschemeι ⁻¹ᵁ V := by
    rw [hU, ← Scheme.Hom.comp_preimage, Scheme.IdealSheafData.inclusion_subschemeι]
  have hpb : fb ⁻¹ᵁ U = Eb.subschemeι ⁻¹ᵁ V := by
    rw [hU, ← Scheme.Hom.comp_preimage, Scheme.IdealSheafData.inclusion_subschemeι]
  haveI : IsAffine (fa ⁻¹ᵁ U) := by rw [hpa]; exact hA
  haveI : IsAffine (fb ⁻¹ᵁ U) := by rw [hpb]; exact hB
  let g : (fa ⁻¹ᵁ U).toScheme ⨿ (fb ⁻¹ᵁ U).toScheme ⟶ U.toScheme :=
    coprod.desc (fa ∣_ U) (fb ∣_ U)
  haveI : IsFinite g := inferInstance
  have hsurj : Function.Surjective g := by
    intro u
    have hu : I.subschemeι u.1 ∈ V := u.2
    have hu' : I.subschemeι u.1 ∈ (I.support : Set Y) := by
      rw [← I.range_subschemeι]
      exact ⟨u.1, rfl⟩
    rcases hsupp _ hu hu' with h | h
    · rw [← Ea.range_subschemeι] at h
      obtain ⟨z, hz⟩ := h
      have hfz : fa z = u.1 := by
        apply I.subschemeι.isEmbedding.injective
        rw [← Scheme.Hom.comp_apply, Scheme.IdealSheafData.inclusion_subschemeι]
        exact hz
      have hzU : z ∈ fa ⁻¹ᵁ U := by
        change fa z ∈ U
        rw [hfz]
        exact u.2
      let p : (fa ⁻¹ᵁ U).toScheme := ⟨z, hzU⟩
      refine ⟨coprodMk _ _ (Sum.inl p), ?_⟩
      rw [coprodMk_inl (X := (fa ⁻¹ᵁ U).toScheme) (Y := (fb ⁻¹ᵁ U).toScheme) p,
        ← Scheme.Hom.comp_apply]
      have e1 : (coprod.inl : (fa ⁻¹ᵁ U).toScheme ⟶ _) ≫ g = fa ∣_ U := coprod.inl_desc _ _
      rw [e1]
      apply Subtype.ext
      rw [morphismRestrict_base_coe]
      exact hfz
    · rw [← Eb.range_subschemeι] at h
      obtain ⟨z, hz⟩ := h
      have hfz : fb z = u.1 := by
        apply I.subschemeι.isEmbedding.injective
        rw [← Scheme.Hom.comp_apply, Scheme.IdealSheafData.inclusion_subschemeι]
        exact hz
      have hzU : z ∈ fb ⁻¹ᵁ U := by
        change fb z ∈ U
        rw [hfz]
        exact u.2
      let p : (fb ⁻¹ᵁ U).toScheme := ⟨z, hzU⟩
      refine ⟨coprodMk _ _ (Sum.inr p), ?_⟩
      rw [coprodMk_inr (X := (fa ⁻¹ᵁ U).toScheme) (Y := (fb ⁻¹ᵁ U).toScheme) p,
        ← Scheme.Hom.comp_apply]
      have e1 : (coprod.inr : (fb ⁻¹ᵁ U).toScheme ⟶ _) ≫ g = fb ∣_ U := coprod.inr_desc _ _
      rw [e1]
      apply Subtype.ext
      rw [morphismRestrict_base_coe]
      exact hfz
  haveI : Surjective g := ⟨hsurj⟩
  haveI : IsNoetherian U.toScheme := by
    haveI hLN : IsLocallyNoetherian I.subscheme := LocallyOfFiniteType.isLocallyNoetherian I.subschemeι
    haveI hLN' : IsLocallyNoetherian U := inferInstance
    have hc : CompactSpace U := Function.Surjective.compactSpace g.continuous hsurj
    exact { __ := hLN' }
  exact Stacks.AlgebraicGeometry.Tag01YQClauseThree.isAffine_of_isFinite_surjective g

end Union

open LaurentPolynomial in
private theorem T_ne_C {K : Type u} [Field K] (m : ℤ) (hm : m ≠ 0) (a : K) :
    (T m : LaurentPolynomial K) ≠ LaurentPolynomial.C a := by
  intro h
  by_cases ha : a = 0
  · subst ha
    have h1 := LaurentPolynomial.degree_T (R := K) m
    rw [h, map_zero, LaurentPolynomial.degree_zero] at h1
    exact absurd h1 (by simp)
  · have h1 := LaurentPolynomial.degree_T (R := K) m
    rw [h, LaurentPolynomial.degree_C ha] at h1
    exact hm (by exact_mod_cast h1.symm)

open LaurentPolynomial in
private theorem laurent_transition_neg {K G : Type u} [Field K] [CommRing G] [Algebra K G]
    (Λ Λ' : LaurentPolynomial K ≃+* G)
    (hΛ : ∀ k : K, Λ (LaurentPolynomial.C k) = algebraMap K G k)
    (hΛ' : ∀ k : K, Λ' (LaurentPolynomial.C k) = algebraMap K G k)
    (H : ∀ p q : Polynomial K, Λ (Polynomial.toLaurent p) = Λ' (Polynomial.toLaurent q) →
      ∃ k : K, Λ (Polynomial.toLaurent p) = algebraMap K G k) :
    ∃ (c : K) (N : ℕ), c ≠ 0 ∧ 1 ≤ N ∧ Λ' (T 1) * Λ (T 1) ^ N = algebraMap K G c := by
  have hu : IsUnit (Λ.symm (Λ' (T 1))) := by
    have : IsUnit (T 1 : LaurentPolynomial K) := ⟨⟨T 1, T (-1), by rw [← T_add]; simp, by rw [← T_add]; simp⟩, rfl⟩
    exact (this.map Λ').map Λ.symm
  obtain ⟨c, n, hc, hcn⟩ := laurent_unit hu.unit
  have hcn' : Λ.symm (Λ' (T 1)) = LaurentPolynomial.C c * T n := by simpa using hcn
  have hη : Λ' (T 1) = algebraMap K G c * Λ (T n) := by
    have := congrArg Λ hcn'
    rw [RingEquiv.apply_symm_apply, map_mul, hΛ] at this
    exact this
  rcases le_or_gt 0 n with hn | hn
  · exfalso
    obtain ⟨N, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    have h1 : Λ (Polynomial.toLaurent (Polynomial.C c * Polynomial.X ^ N)) =
        Λ' (Polynomial.toLaurent Polynomial.X) := by
      rw [Polynomial.toLaurent_C_mul_X_pow, Polynomial.toLaurent_X, hη, map_mul, hΛ]
    obtain ⟨k, hk⟩ := H _ _ h1
    have hk' : Λ' (Polynomial.toLaurent Polynomial.X) = algebraMap K G k := h1.symm.trans hk
    rw [← hΛ' k] at hk'
    have := Λ'.injective hk'
    rw [Polynomial.toLaurent_X] at this
    exact T_ne_C 1 one_ne_zero k this
  · obtain ⟨N, hN⟩ : ∃ N : ℕ, n = -(N : ℤ) := ⟨(-n).toNat, by omega⟩
    have hN1 : 1 ≤ N := by omega
    refine ⟨c, N, hc, hN1, ?_⟩
    rw [hη, hN, mul_assoc, ← map_pow, ← map_mul, T_pow, ← T_add]
    have : (-(N : ℤ) + (N : ℤ) * 1) = 0 := by ring
    rw [this]
    simp

open LaurentPolynomial in
/-- The transition between the two Laurent coordinates `ξ = Λ T`, `η = Λ' T` of a ring `G`, whose
polynomial subrings meet only in the constants, is a constant. -/
private theorem laurent_transition {K G : Type u} [Field K] [CommRing G] [Algebra K G]
    (Λ Λ' : LaurentPolynomial K ≃+* G)
    (hΛ : ∀ k : K, Λ (LaurentPolynomial.C k) = algebraMap K G k)
    (hΛ' : ∀ k : K, Λ' (LaurentPolynomial.C k) = algebraMap K G k)
    (H : ∀ p q : Polynomial K, Λ (Polynomial.toLaurent p) = Λ' (Polynomial.toLaurent q) →
      ∃ k : K, Λ (Polynomial.toLaurent p) = algebraMap K G k) :
    ∃ c : K, c ≠ 0 ∧ Λ (T 1) * Λ' (T 1) = algebraMap K G c := by
  obtain ⟨c, N, hc, hN1, hN⟩ := laurent_transition_neg Λ Λ' hΛ hΛ' H
  obtain ⟨c', M, hc', hM1, hM⟩ := laurent_transition_neg Λ' Λ hΛ' hΛ (fun p q h => by
    obtain ⟨k, hk⟩ := H q p h.symm
    exact ⟨k, h.trans hk⟩)
  set ξ := Λ (T 1) with hξ
  set η := Λ' (T 1) with hη
  have key : algebraMap K G c' * ξ ^ (N * M) = algebraMap K G (c ^ M) * ξ := by
    calc algebraMap K G c' * ξ ^ (N * M) = (ξ * η ^ M) * ξ ^ (N * M) := by rw [hM]
      _ = ξ * ((η * ξ ^ N) ^ M) := by rw [mul_pow, ← pow_mul]; ring
      _ = _ := by rw [hN, map_pow]; ring
  have hpow : ξ ^ (N * M) = Λ (T ((N * M : ℕ) : ℤ)) := by
    rw [hξ, ← map_pow, T_pow]; simp
  have hNM : N * M = 1 := by
    by_contra hne
    have h2 : Λ (LaurentPolynomial.C c' * T ((N * M : ℕ) : ℤ)) =
        Λ (LaurentPolynomial.C (c ^ M) * T 1) := by
      rw [map_mul, map_mul, hΛ, hΛ, ← hpow]
      exact key
    have h3 := Λ.injective h2
    have h4 := congrArg LaurentPolynomial.degree h3
    rw [degree_C_mul_T _ _ hc', degree_C_mul_T _ _ (pow_ne_zero _ hc)] at h4
    exact hne (by exact_mod_cast h4)
  have hN' : N = 1 := Nat.eq_one_of_mul_eq_one_right hNM
  subst hN'
  exact ⟨c, hc, by rw [pow_one] at hN; rw [mul_comm]; exact hN⟩

/-- The opens `V j`: the points of `X` lying on no exceptional curve other than `E_{j-1}`, `E_j`,
and different from the markings `pL` (for `j ≥ 1`) and `pR` (for `j < r`). -/
private theorem exists_chart_opens {X : Scheme.{u}} {r : ℕ} (E : Fin r → PrimeDivisor X)
    (pL pR : X) (hL : IsClosed ({pL} : Set X)) (hR : IsClosed ({pR} : Set X)) :
    ∃ V : Fin (r + 1) → X.Opens, ∀ (j : Fin (r + 1)) (y : X), y ∈ V j ↔
      ((∀ k : Fin r, y ∈ (E k).idealSheaf.support → k.val + 1 = j.val ∨ k.val = j.val) ∧
        (1 ≤ j.val → y ≠ pL) ∧ (j.val < r → y ≠ pR)) := by
  classical
  have hF : ∀ j : Fin (r + 1), IsClosed ((⋃ k : Fin r, if (k.val + 1 = j.val ∨ k.val = j.val)
      then (∅ : Set X) else ((E k).idealSheaf.support : Set X)) ∪
      (if 1 ≤ j.val then {pL} else ∅) ∪ (if j.val < r then {pR} else ∅) : Set X) := by
    intro j
    refine ((isClosed_iUnion_of_finite fun k => ?_).union ?_).union ?_
    · split_ifs
      · exact isClosed_empty
      · exact (E k).idealSheaf.support.isClosed
    · split_ifs
      · exact hL
      · exact isClosed_empty
    · split_ifs
      · exact hR
      · exact isClosed_empty
  refine ⟨fun j => ⟨_, (hF j).isOpen_compl⟩, fun j y => ?_⟩
  change y ∉ (_ : Set X) ↔ _
  simp only [Set.mem_union, Set.mem_iUnion, not_or, not_exists, and_assoc]
  refine and_congr ?_ (and_congr ?_ ?_)
  · constructor
    · intro h k hk
      by_contra hc
      exact h k (by rw [if_neg hc]; exact hk)
    · intro h k hk
      split_ifs at hk with hc
      · exact hk
      · exact hc (h k hk)
  · by_cases h : 1 ≤ j.val
    · rw [if_pos h, Set.mem_singleton_iff]; exact ⟨fun hy _ => hy, fun hh => hh h⟩
    · rw [if_neg h]; exact ⟨fun _ hh => absurd hh h, fun _ => Set.notMem_empty y⟩
  · by_cases h : j.val < r
    · rw [if_pos h, Set.mem_singleton_iff]; exact ⟨fun hy _ => hy, fun hh => hh h⟩
    · rw [if_neg h]; exact ⟨fun _ hh => absurd hh h, fun _ => Set.notMem_empty y⟩

/-- The zero locus of a generator `s` of the kernel of `Γ(I, tr W) → Γ(D, tr W)` is the part of `I`
lying over `D`. -/
private theorem mem_basicOpen_iff {Y : Scheme.{u}} {I D : Y.IdealSheafData} (h : I ≤ D)
    (W : Y.Opens) (hW : IsAffineOpen (I.subschemeι ⁻¹ᵁ W))
    (s : Γ(I.subscheme, I.subschemeι ⁻¹ᵁ W))
    (hs : RingHom.ker (inclSections h W) = Ideal.span {s}) (z : I.subscheme)
    (hz : z ∈ I.subschemeι ⁻¹ᵁ W) :
    z ∈ I.subscheme.basicOpen s ↔ I.subschemeι z ∉ (D.support : Set Y) := by
  set f := Scheme.IdealSheafData.inclusion h with hf
  have hrange : ∀ z : I.subscheme, z ∈ Set.range f ↔ I.subschemeι z ∈ (D.support : Set Y) := by
    intro z
    constructor
    · rintro ⟨w, rfl⟩
      rw [← Scheme.Hom.comp_apply, Scheme.IdealSheafData.inclusion_subschemeι, ← D.range_subschemeι]
      exact ⟨w, rfl⟩
    · intro hzD
      rw [← D.range_subschemeι] at hzD
      obtain ⟨w, hw⟩ := hzD
      refine ⟨w, I.subschemeι.isEmbedding.injective ?_⟩
      rw [← Scheme.Hom.comp_apply, Scheme.IdealSheafData.inclusion_subschemeι, hw]
  have hclosed : IsClosed (Set.range f) := by
    have : Set.range f = I.subschemeι ⁻¹' (D.support : Set Y) := by
      ext z; rw [hrange z]; rfl
    rw [this]
    exact D.support.isClosed.preimage I.subschemeι.continuous
  have hsupp : (f.ker.support : Set I.subscheme) = Set.range f := by
    rw [Scheme.Hom.support_ker]
    exact hclosed.closure_eq
  have hker : f.ker.ideal ⟨_, hW⟩ = Ideal.span {s} := by
    rw [← hs, ker_inclSections_eq_ker_app, Scheme.Hom.ker_apply]
  have hmem := Scheme.IdealSheafData.mem_support_iff_of_mem (I := f.ker) (U := ⟨_, hW⟩) hz
  have hsupp' : z ∈ f.ker.support ↔ z ∈ Set.range f := by rw [← SetLike.mem_coe, hsupp]
  rw [hsupp', hker, Scheme.zeroLocus_span] at hmem
  rw [← hrange z, hmem, Scheme.mem_zeroLocus_iff]
  simp only [Set.mem_singleton_iff, forall_eq, not_not]

private theorem bijective_comp_of_ker_eq {R B1 B2 K : Type*} [Field K] [CommRing R] [CommRing B1]
    [CommRing B2] (f1 : R →+* B1) (f2 : R →+* B2) (h1 : Function.Surjective f1)
    (h2 : Function.Surjective f2) (hk : RingHom.ker f1 = RingHom.ker f2) (σ : K →+* R)
    (h : Function.Bijective (f2.comp σ)) : Function.Bijective (f1.comp σ) := by
  have hmem : ∀ x : R, f1 x = 0 ↔ f2 x = 0 := fun x => by
    rw [← RingHom.mem_ker, ← RingHom.mem_ker, hk]
  refine ⟨?_, ?_⟩
  · intro a b hab
    have hab' : f1 (σ a) = f1 (σ b) := hab
    have h0 : f1 (σ a - σ b) = 0 := by rw [map_sub, hab', sub_self]
    have h0' := (hmem _).1 h0
    rw [map_sub, sub_eq_zero] at h0'
    exact h.1 h0'
  · intro b
    obtain ⟨p, rfl⟩ := h1 b
    obtain ⟨c, hc⟩ := h.2 (f2 p)
    refine ⟨c, ?_⟩
    have : f2 (σ c - p) = 0 := by simpa [map_sub, sub_eq_zero] using hc
    have := (hmem _).2 this
    simpa [map_sub, sub_eq_zero] using this

open MMP.Resolution.Bridges MMP.Mori in
/-- The constants map isomorphically onto the sections of the intersection `Ea ∩ Eb` of two curves
meeting with intersection number one, over a neighbourhood `V` of the intersection. -/
private theorem bijective_sigma_sup {K : Type u} [Field K] [IsAlgClosed K] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of K)) [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y]
    (hsm : IsSmoothScheme sY) (Ea Eb : PrimeDivisor Y)
    [hcart : Stacks.Divisors.IsEffectiveCartierDivisor Ea.idealSheaf]
    (hDC : ¬ Eb.idealSheaf.supportSet ⊆ Ea.idealSheaf.supportSet)
    (hnum : IsIntersectionNumber sY (Finsupp.single Ea 1) Eb.idealSheaf (1 : ℤ))
    (V : Y.Opens) (hVb : IsAffineOpen (Eb.idealSheaf.subschemeι ⁻¹ᵁ V))
    (hnode : ∀ y, y ∈ Ea.idealSheaf.support → y ∈ Eb.idealSheaf.support → y ∈ V) :
    Function.Bijective (sigmaSub sY (Ea.idealSheaf ⊔ Eb.idealSheaf) V) := by
  haveI : AlgebraicGeometry.IsIntegral Eb.idealSheaf.subscheme := Eb.integral
  have hbij := bijective_comap_intersection sY hsm Ea Eb.idealSheaf hDC hnum
  set D := Ea.idealSheaf ⊔ Eb.idealSheaf with hD
  have hb : Eb.idealSheaf ≤ D := le_sup_right
  set M := Ea.idealSheaf.comap Eb.idealSheaf.subschemeι with hM
  set Ub := Eb.idealSheaf.subschemeι ⁻¹ᵁ V with hUb
  -- the kernels agree
  have hker1 : RingHom.ker (inclSections hb V) = M.ideal ⟨Ub, hVb⟩ := by
    rw [ker_inclSections_eq_comap hb V hVb, hD, Scheme.IdealSheafData.comap_sup,
      comap_self_eq_bot, sup_bot_eq]
  have hker2 : RingHom.ker (M.subschemeι.app Ub).hom = M.ideal ⟨Ub, hVb⟩ :=
    Scheme.IdealSheafData.ker_subschemeι_app (I := M) ⟨Ub, hVb⟩
  have hs1 : Function.Surjective (inclSections hb V) := inclSections_surjective hb V hVb
  have hs2 : Function.Surjective (M.subschemeι.app Ub).hom :=
    Scheme.IdealSheafData.subschemeι_app_surjective (I := M) ⟨Ub, hVb⟩
  -- the intersection lies over `V`
  have hTop : M.subschemeι ⁻¹ᵁ Ub = ⊤ := by
    refine eq_top_iff.2 fun w _ => ?_
    have h1 : M.subschemeι w ∈ (M.support : Set Eb.idealSheaf.subscheme) := by
      rw [← M.range_subschemeι]; exact ⟨w, rfl⟩
    have h1 := (Set.ext_iff.1 (congrArg SetLike.coe
      (Scheme.IdealSheafData.support_comap Ea.idealSheaf Eb.idealSheaf.subschemeι))
      (M.subschemeι w)).1 h1
    have h2 : Eb.idealSheaf.subschemeι (M.subschemeι w) ∈ (Eb.idealSheaf.support : Set Y) := by
      rw [← Eb.idealSheaf.range_subschemeι]; exact ⟨_, rfl⟩
    exact hnode _ h1 h2
  -- the two composites with the constants
  set σ1 := sigmaSub sY Eb.idealSheaf V with hσ1
  have hσD : ∀ c, sigmaSub sY D V c = inclSections hb V (σ1 c) := fun c =>
    (inclSections_sigma sY hb V c).symm
  have hσZ : ∀ c, ((Scheme.ΓSpecIso (.of K)).inv ≫
      (M.subschemeι ≫ Eb.idealSheaf.subschemeι ≫ sY).appLE ⊤ (M.subschemeι ⁻¹ᵁ Ub) le_top).hom c =
      (M.subschemeι.app Ub).hom (σ1 c) := by
    intro c
    have := map_constants_hom (M.subschemeι ≫ Eb.idealSheaf.subschemeι ≫ sY)
      (Eb.idealSheaf.subschemeι ≫ sY) M.subschemeι rfl (M.subschemeι ⁻¹ᵁ Ub) Ub le_rfl c
    rw [← this]
    have e : M.subschemeι.appLE Ub (M.subschemeι ⁻¹ᵁ Ub) le_rfl = M.subschemeι.app Ub := by
      simp [Scheme.Hom.appLE]
    rw [e]
  have hZ : Function.Bijective (fun c : K => ((Scheme.ΓSpecIso (.of K)).inv ≫
      (M.subschemeι ≫ Eb.idealSheaf.subschemeι ≫ sY).appLE ⊤ (M.subschemeι ⁻¹ᵁ Ub) le_top).hom c) := by
    rw [hTop]
    have e : (M.subschemeι ≫ Eb.idealSheaf.subschemeι ≫ sY).appLE ⊤ ⊤ le_top =
        (M.subschemeι ≫ Eb.idealSheaf.subschemeι ≫ sY).appTop := by
      simp [Scheme.Hom.appLE]
    rw [e]
    exact hbij
  have hcomp : Function.Bijective ((M.subschemeι.app Ub).hom.comp σ1) := by
    have heq : (fun c : K => (M.subschemeι.app Ub).hom (σ1 c)) = fun c : K => ((Scheme.ΓSpecIso (.of K)).inv ≫
      (M.subschemeι ≫ Eb.idealSheaf.subschemeι ≫ sY).appLE ⊤ (M.subschemeι ⁻¹ᵁ Ub) le_top).hom c :=
      funext fun c => (hσZ c).symm
    rw [← heq] at hZ
    exact hZ
  have hfin := bijective_comp_of_ker_eq (inclSections hb V) (M.subschemeι.app Ub).hom hs1 hs2
    (hker1.trans hker2.symm) σ1 hcomp
  have : (sigmaSub sY D V : K → _) = ⇑((inclSections hb V).comp σ1) := by
    funext c; exact hσD c
  rw [this]
  exact hfin

open MMP.Resolution.Bridges MMP.Mori in
/-- Algebra of a node chart: the sections of the union of two curves `Ea ∪ Eb` of the exceptional
locus over `V` form the node ring `K[x, y] / (x y)`, `x` and `y` generating the ideals of `Ea` and
`Eb`. -/
private theorem node_chart {K : Type u} [Field K] [IsAlgClosed K] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of K)) [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y]
    (hsm : IsSmoothScheme sY) (Ea Eb : PrimeDivisor Y)
    [hcart : Stacks.Divisors.IsEffectiveCartierDivisor Ea.idealSheaf]
    (hDC : ¬ Eb.idealSheaf.supportSet ⊆ Ea.idealSheaf.supportSet)
    (hnum : IsIntersectionNumber sY (Finsupp.single Ea 1) Eb.idealSheaf (1 : ℤ))
    (I : Y.IdealSheafData) (ha : I ≤ Ea.idealSheaf) (hb : I ≤ Eb.idealSheaf) (V : Y.Opens)
    (hAa : IsAffineOpen (Ea.idealSheaf.subschemeι ⁻¹ᵁ V))
    (hAb : IsAffineOpen (Eb.idealSheaf.subschemeι ⁻¹ᵁ V))
    (eaK : ∃ e : Γ(Ea.idealSheaf.subscheme, Ea.idealSheaf.subschemeι ⁻¹ᵁ V) ≃+* Polynomial K,
      ∀ c, e (sigmaSub sY Ea.idealSheaf V c) = Polynomial.C c)
    (ebK : ∃ e : Γ(Eb.idealSheaf.subscheme, Eb.idealSheaf.subschemeι ⁻¹ᵁ V) ≃+* Polynomial K,
      ∀ c, e (sigmaSub sY Eb.idealSheaf V c) = Polynomial.C c)
    (hsupp : ∀ y ∈ V, y ∈ (I.support : Set Y) →
      y ∈ (Ea.idealSheaf.support : Set Y) ∨ y ∈ (Eb.idealSheaf.support : Set Y))
    (hW : ∀ W : Y.affineOpens, W.1 ≤ V → Ea.idealSheaf.ideal W ⊓ Eb.idealSheaf.ideal W ≤ I.ideal W)
    (hnode : ∀ y, y ∈ Ea.idealSheaf.support → y ∈ Eb.idealSheaf.support → y ∈ V) :
    IsAffineOpen (I.subschemeι ⁻¹ᵁ V) ∧
    ∃ x y : Γ(I.subscheme, I.subschemeι ⁻¹ᵁ V),
      RingHom.ker (inclSections ha V) = Ideal.span {x} ∧
      RingHom.ker (inclSections hb V) = Ideal.span {y} ∧
      Function.Surjective (MvPolynomial.eval₂Hom (sigmaSub sY I V) ![x, y]) ∧
      RingHom.ker (MvPolynomial.eval₂Hom (sigmaSub sY I V) ![x, y]) =
        Ideal.span {(MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) K)} := by
  have hT : IsAffineOpen (I.subschemeι ⁻¹ᵁ V) := isAffineOpen_of_two ha hb V hsupp hAa hAb
  refine ⟨hT, ?_⟩
  obtain ⟨ea, hea⟩ := eaK
  obtain ⟨eb, heb⟩ := ebK
  have hD : I ≤ Ea.idealSheaf ⊔ Eb.idealSheaf := ha.trans le_sup_left
  have hbij := bijective_sigma_sup sY hsm Ea Eb hDC hnum V hAb hnode
  let e := RingEquiv.ofBijective (sigmaSub sY (Ea.idealSheaf ⊔ Eb.idealSheaf) V) hbij
  let ε : Γ(I.subscheme, I.subschemeι ⁻¹ᵁ V) →+* K :=
    e.symm.toRingHom.comp (inclSections hD V)
  have hε : ∀ c, ε (sigmaSub sY I V c) = c := by
    intro c
    show e.symm (inclSections hD V (sigmaSub sY I V c)) = c
    rw [inclSections_sigma]
    exact e.symm_apply_apply c
  have hker : RingHom.ker ε = RingHom.ker (inclSections ha V) ⊔ RingHom.ker (inclSections hb V) := by
    rw [← ker_inclSections_sup rfl hD ha hb V hT]
    ext z
    simp only [RingHom.mem_ker, ε, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingHom.coe_coe, EmbeddingLike.map_eq_zero_iff]
  exact node_alg (sigmaSub sY I V) (inclSections ha V) (inclSections hb V)
    (inclSections_surjective ha V hT) (inclSections_surjective hb V hT) ea eb
    (fun c => by rw [inclSections_sigma]; exact hea c)
    (fun c => by rw [inclSections_sigma]; exact heb c)
    (ker_inf_eq_bot ha hb V hW) ε hε hker

private theorem bijective_algebraMap_quot_X {K : Type u} [Field K] :
    Function.Bijective (algebraMap K (Polynomial K ⧸ Ideal.span {(Polynomial.X : Polynomial K) ^ (0 + 1)})) := by
  let Q := Polynomial K ⧸ Ideal.span {(Polynomial.X : Polynomial K) ^ (0 + 1)}
  have hX : (Polynomial.X : Polynomial K) ^ (0 + 1) = Polynomial.X := by simp
  have hne : Nontrivial Q := by
    refine (Ideal.Quotient.lift _ (Polynomial.evalRingHom 0) (fun a ha => ?_) : Q →+* K).domain_nontrivial
    rw [hX, Ideal.mem_span_singleton'] at ha
    obtain ⟨b, rfl⟩ := ha
    simp
  refine ⟨(algebraMap K Q).injective, fun q => ?_⟩
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
  refine ⟨p.coeff 0, ?_⟩
  have : Polynomial.X ∣ p - Polynomial.C (p.coeff 0) := by
    rw [Polynomial.X_dvd_iff]; simp
  obtain ⟨b, hb⟩ := this
  show Ideal.Quotient.mk _ (Polynomial.C (p.coeff 0)) = Ideal.Quotient.mk _ p
  rw [Ideal.Quotient.eq, hX, Ideal.mem_span_singleton']
  exact ⟨-b, by rw [neg_mul, ← neg_sub, hb]; ring⟩

/-- The constants of a curvilinear point (of length one) over `K` are all of its sections. -/
private theorem bijective_sigma_zero {K : Type u} [Field K] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of K)) (Z : Y.IdealSheafData)
    (e : Z.subscheme ≅ Spec (.of (Polynomial K ⧸ Ideal.span {(Polynomial.X : Polynomial K) ^ (0 + 1)})))
    (he : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K _)) = Z.subschemeι ≫ sY)
    (V : Y.Opens) (hV : Z.subschemeι ⁻¹ᵁ V = ⊤) :
    Function.Bijective (sigmaSub sY Z V) := by
  have key : ∀ (W : Z.subscheme.Opens) (hW : W = ⊤),
      Function.Bijective ((Scheme.ΓSpecIso (.of K)).inv ≫
        (Z.subschemeι ≫ sY).appLE ⊤ W le_top).hom := by
    intro W hW
    subst hW
    have e1 : (Z.subschemeι ≫ sY).appLE ⊤ ⊤ le_top = (Z.subschemeι ≫ sY).appTop := by
      simp [Scheme.Hom.appLE]
    rw [e1, ← he, Scheme.Hom.comp_appTop, ← Category.assoc,
      show (Scheme.ΓSpecIso (.of K)).inv ≫ (Spec.map (CommRingCat.ofHom (algebraMap K _))).appTop =
        CommRingCat.ofHom (algebraMap K _) ≫ (Scheme.ΓSpecIso _).inv from
        (Scheme.ΓSpecIso_inv_naturality _).symm]
    have h1 : IsIso e.hom.appTop := inferInstanceAs (IsIso (Scheme.Γ.map e.hom.op))
    have h2 : Function.Bijective (e.hom.appTop).hom := (asIso e.hom.appTop).commRingCatIsoToRingEquiv.bijective
    have h3 : Function.Bijective (Scheme.ΓSpecIso (.of (Polynomial K ⧸ Ideal.span
        {(Polynomial.X : Polynomial K) ^ (0 + 1)}))).inv.hom :=
      (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv.bijective
    simp only [Category.assoc, CommRingCat.hom_comp]
    exact h2.comp (h3.comp bijective_algebraMap_quot_X)
  exact key _ hV

/-- Algebra of an end chart: over `V`, the thickening `I` agrees with the curve `Eb`, and the
marking `Z` cuts out a reduced point, so the coordinate ring is `K[x]` with `x` generating the
ideal of the marking. -/
private theorem end_chart_core {K : Type u} [Field K] {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (sY : Y ⟶ Spec (.of K)) (I Eb Z : Y.IdealSheafData) (hb : I ≤ Eb) (hZ : I ≤ Z)
    (V : Y.Opens) (hAb : IsAffineOpen (Eb.subschemeι ⁻¹ᵁ V))
    (ebK : ∃ e : Γ(Eb.subscheme, Eb.subschemeι ⁻¹ᵁ V) ≃+* Polynomial K,
      ∀ c, e (sigmaSub sY Eb V c) = Polynomial.C c)
    (hinj : RingHom.ker (inclSections hb V) = ⊥)
    (hsupp : ∀ y ∈ V, y ∈ (I.support : Set Y) → y ∈ (Eb.support : Set Y))
    (e0 : Z.subscheme ≅ Spec (.of (Polynomial K ⧸ Ideal.span {(Polynomial.X : Polynomial K) ^ (0 + 1)})))
    (he0 : e0.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K _)) = Z.subschemeι ≫ sY)
    (hZV : Z.subschemeι ⁻¹ᵁ V = ⊤) :
    IsAffineOpen (I.subschemeι ⁻¹ᵁ V) ∧
    (∃ x : Γ(I.subscheme, I.subschemeι ⁻¹ᵁ V), RingHom.ker (inclSections hZ V) = Ideal.span {x} ∧
      Function.Surjective (MvPolynomial.eval₂Hom (sigmaSub sY I V) ![x, 0]) ∧
      RingHom.ker (MvPolynomial.eval₂Hom (sigmaSub sY I V) ![x, 0]) =
        Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 2) K)}) ∧
    (∃ x : Γ(I.subscheme, I.subschemeι ⁻¹ᵁ V), RingHom.ker (inclSections hZ V) = Ideal.span {x} ∧
      Function.Surjective (MvPolynomial.eval₂Hom (sigmaSub sY I V) ![0, x]) ∧
      RingHom.ker (MvPolynomial.eval₂Hom (sigmaSub sY I V) ![0, x]) =
        Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin 2) K)}) := by
  have hT : IsAffineOpen (I.subschemeι ⁻¹ᵁ V) := isAffineOpen_of_two hb hb V
    (fun y hy hI => Or.inl (hsupp y hy hI)) hAb hAb
  obtain ⟨eb, heb⟩ := ebK
  have hπ : Function.Bijective (inclSections hb V) :=
    ⟨(RingHom.injective_iff_ker_eq_bot _).2 hinj, inclSections_surjective hb V hT⟩
  let e' : Γ(I.subscheme, I.subschemeι ⁻¹ᵁ V) ≃+* Polynomial K :=
    (RingEquiv.ofBijective _ hπ).trans eb
  have he' : ∀ c, e' (sigmaSub sY I V c) = Polynomial.C c := fun c => by
    show eb (inclSections hb V (sigmaSub sY I V c)) = _
    rw [inclSections_sigma]; exact heb c
  have hbij := bijective_sigma_zero sY Z e0 he0 V hZV
  let eZ := RingEquiv.ofBijective (sigmaSub sY Z V) hbij
  let ε : Γ(I.subscheme, I.subschemeι ⁻¹ᵁ V) →+* K := eZ.symm.toRingHom.comp (inclSections hZ V)
  have hε : ∀ c, ε (sigmaSub sY I V c) = c := fun c => by
    show eZ.symm (inclSections hZ V (sigmaSub sY I V c)) = c
    rw [inclSections_sigma]; exact eZ.symm_apply_apply c
  have hker : RingHom.ker ε = RingHom.ker (inclSections hZ V) := by
    ext z
    simp only [RingHom.mem_ker, ε, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingHom.coe_coe, EmbeddingLike.map_eq_zero_iff]
  refine ⟨hT, ?_, ?_⟩
  · obtain ⟨x, hx, h1, h2⟩ := end_alg0 (sigmaSub sY I V) e' he' ε hε
    exact ⟨x, hker ▸ hx, h1, h2⟩
  · obtain ⟨x, hx, h1, h2⟩ := end_alg1 (sigmaSub sY I V) e' he' ε hε
    exact ⟨x, hker ▸ hx, h1, h2⟩

/-- The standing combinatorial hypotheses on the chain of exceptional curves and the markings. -/
private structure ChainData {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    [IsLocallyNoetherian X] [IsNormal X] (sX : X ⟶ Spec (.of K)) [QuasiCompact sX]
    {r : ℕ} (E : Fin r → PrimeDivisor X) (pL pR : X) : Prop where
  inj : Function.Injective E
  rat : ∀ i, IsSmoothRationalCurve sX (E i).idealSheaf
  adj : ∀ i j : Fin r, i.val + 1 = j.val →
    IsIntersectionNumber sX (Finsupp.single (E i) 1) (E j).idealSheaf 1
  far : ∀ i j : Fin r, i.val + 1 < j.val → Disjoint ((E i).idealSheaf.support : Set X) ((E j).idealSheaf.support : Set X)
  hpLR : pL ≠ pR
  pL_ex : ∃ i : Fin r, i.val = 0 ∧ pL ∈ (E i).support
  pL_only : ∀ i : Fin r, pL ∈ (E i).support → i.val = 0
  pR_ex : ∃ i : Fin r, i.val + 1 = r ∧ pR ∈ (E i).support
  pR_only : ∀ i : Fin r, pR ∈ (E i).support → i.val + 1 = r

private def ChartOpens {X : Scheme.{u}} {r : ℕ} (E : Fin r → PrimeDivisor X) (pL pR : X)
    (V : Fin (r + 1) → X.Opens) : Prop :=
  ∀ (j : Fin (r + 1)) (y : X), y ∈ V j ↔
    ((∀ k : Fin r, y ∈ (E k).support → k.val + 1 = j.val ∨ k.val = j.val) ∧
      (1 ≤ j.val → y ≠ pL) ∧ (j.val < r → y ≠ pR))

section Topology

variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of K)} [QuasiCompact sX] {r : ℕ}
  {E : Fin r → PrimeDivisor X} {pL pR : X} {V : Fin (r + 1) → X.Opens}

private theorem ChainData.near (hC : ChainData sX E pL pR) {k m : Fin r} {y : X}
    (hk : y ∈ (E k).support) (hm : y ∈ (E m).support) : k.val ≤ m.val + 1 ∧ m.val ≤ k.val + 1 := by
  constructor
  · by_contra h
    exact Set.disjoint_left.1 (hC.far m k (by omega)) hm hk
  · by_contra h
    exact Set.disjoint_left.1 (hC.far k m (by omega)) hk hm

private theorem pL_mem_V (hC : ChainData sX E pL pR) (hV : ChartOpens E pL pR V) :
    pL ∈ V 0 := by
  rw [hV]
  refine ⟨fun k hk => Or.inr (by simpa using hC.pL_only k hk), fun h => by simp at h, fun _ => hC.hpLR⟩

private theorem pR_mem_V (hC : ChainData sX E pL pR) (hV : ChartOpens E pL pR V) :
    pR ∈ V (Fin.last r) := by
  rw [hV]
  refine ⟨fun k hk => Or.inl (by simpa using hC.pR_only k hk), fun _ => hC.hpLR.symm,
    fun h => by simp at h⟩

private theorem mem_V_node (hC : ChainData sX E pL pR) (hV : ChartOpens E pL pR V)
    (a b : Fin r) (hab : a.val + 1 = b.val) (c : Fin (r + 1)) (hc : c.val = b.val) {y : X}
    (ha : y ∈ (E a).support) (hb : y ∈ (E b).support) : y ∈ V c := by
  rw [hV]
  refine ⟨fun k hk => ?_, fun h hy => ?_, fun h hy => ?_⟩
  · have h1 := hC.near hk ha
    have h2 := hC.near hk hb
    omega
  · have := hC.pL_only b (hy ▸ hb)
    omega
  · have h1 := hC.pR_only a (hy ▸ ha)
    have h2 := hC.pR_only b (hy ▸ hb)
    omega

private theorem val_succ_eq_or_eq_of_mem_V (hV : ChartOpens E pL pR V) {c : Fin (r + 1)} {y : X}
    (hy : y ∈ V c) {k : Fin r} (hk : y ∈ (E k).support) : k.val + 1 = c.val ∨ k.val = c.val :=
  ((hV c y).1 hy).1 k hk

end Topology

private theorem mem_support_prod {X : Scheme.{u}} {r : ℕ} (E : Fin r → PrimeDivisor X) (y : X) :
    y ∈ ((∏ i, (E i).idealSheaf).support : Set X) ↔ ∃ k, y ∈ (E k).support := by
  classical
  have : ∀ s : Finset (Fin r), y ∈ ((∏ i ∈ s, (E i).idealSheaf).support : Set X) ↔
      ∃ k ∈ s, y ∈ (E k).support := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Scheme.IdealSheafData.support_mul]
      simp only [TopologicalSpace.Closeds.coe_sup, Set.mem_union, Finset.mem_insert,
        exists_eq_or_imp]
      rw [← ih]
  simpa using this Finset.univ

section Topology2

variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of K)} [QuasiCompact sX] {r : ℕ}
  {E : Fin r → PrimeDivisor X} {pL pR : X} {V : Fin (r + 1) → X.Opens}

private theorem disj_of_V (hV : ChartOpens E pL pR V) (c : Fin (r + 1)) (k : Fin r)
    (h1 : k.castSucc ≠ c) (h2 : k.succ ≠ c) {y : X} (hy : y ∈ V c) : y ∉ (E k).support := by
  intro hk
  rcases val_succ_eq_or_eq_of_mem_V hV hy hk with h | h
  · exact h2 (Fin.ext (by simpa using h))
  · exact h1 (Fin.ext (by simpa using h))

private theorem cover_E (hC : ChainData sX E pL pR) (hV : ChartOpens E pL pR V) (j : Fin r) :
    (E j).support ⊆ (V j.castSucc : Set X) ∪ (V j.succ : Set X) := by
  intro y hy
  by_cases hc : y ∈ V j.castSucc
  · exact Or.inl hc
  right
  have hF1 : y = pL → j.val = 0 := fun h => hC.pL_only j (h ▸ hy)
  have hF2 : y = pR → j.val + 1 = r := fun h => hC.pR_only j (h ▸ hy)
  have hc' : ¬ ((∀ k : Fin r, y ∈ (E k).support → k.val + 1 = j.val ∨ k.val = j.val) ∧
      (1 ≤ j.val → y ≠ pL) ∧ (j.val < r → y ≠ pR)) :=
    fun h => hc ((hV j.castSucc y).2 h)
  change y ∈ V j.succ
  rw [hV]
  have hcases : (∃ k : Fin r, y ∈ (E k).support ∧ ¬ (k.val + 1 = j.val ∨ k.val = j.val)) ∨
      (1 ≤ j.val ∧ y = pL) ∨ y = pR := by
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2, h3⟩ := hcon
    exact hc' ⟨h1, h2, fun _ => h3⟩
  simp only [Fin.val_succ]
  rcases hcases with ⟨k', hk', hne⟩ | ⟨h1pos, hpl⟩ | hpr
  · have hn' := hC.near hk' hy
    have hk'j : k'.val = j.val + 1 := by omega
    refine ⟨fun k hk => ?_, fun _ hh => ?_, fun h hh => ?_⟩
    · have hn := hC.near hk hy
      by_contra hcon
      have : k.val + 1 = j.val := by omega
      exact Set.disjoint_left.1 (hC.far k k' (by omega)) hk hk'
    · have := hC.pL_only k' (hh ▸ hk')
      omega
    · have := hF2 hh
      omega
  · exact absurd (hF1 hpl) (by omega)
  · have hj := hF2 hpr
    refine ⟨fun k hk => ?_, fun _ hh => hC.hpLR (hh.symm.trans hpr), fun h hh => by omega⟩
    have := hC.pR_only k (hpr ▸ hk)
    omega

end Topology2

section Topology3

variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of K)} [QuasiCompact sX] {r : ℕ}
  {E : Fin r → PrimeDivisor X} {pL pR : X} {V : Fin (r + 1) → X.Opens}

private theorem supp_of_V (hV : ChartOpens E pL pR V) (c : Fin (r + 1)) {y : X} (hy : y ∈ V c)
    (hI : y ∈ ((∏ i, (E i).idealSheaf).support : Set X)) :
    ∃ k : Fin r, (k.castSucc = c ∨ k.succ = c) ∧ y ∈ (E k).support := by
  obtain ⟨k, hk⟩ := (mem_support_prod E y).1 hI
  refine ⟨k, ?_, hk⟩
  rcases val_succ_eq_or_eq_of_mem_V hV hy hk with h | h
  · exact Or.inr (Fin.ext (by simpa using h))
  · exact Or.inl (Fin.ext (by simpa using h))

private theorem supp_cover (hC : ChainData sX E pL pR) (hV : ChartOpens E pL pR V) {y : X}
    (hI : y ∈ ((∏ i, (E i).idealSheaf).support : Set X)) : ∃ j, y ∈ V j := by
  obtain ⟨k, hk⟩ := (mem_support_prod E y).1 hI
  rcases cover_E hC hV k hk with h | h
  · exact ⟨_, h⟩
  · exact ⟨_, h⟩

private theorem overlap_supp (hC : ChainData sX E pL pR) (hV : ChartOpens E pL pR V) (j : Fin r)
    {y : X} (hy1 : y ∈ V j.castSucc) (hy2 : y ∈ V j.succ)
    (hI : y ∈ ((∏ i, (E i).idealSheaf).support : Set X)) : y ∈ (E j).support := by
  obtain ⟨k, hk⟩ := (mem_support_prod E y).1 hI
  have h1 := val_succ_eq_or_eq_of_mem_V hV hy1 hk
  have h2 := val_succ_eq_or_eq_of_mem_V hV hy2 hk
  have : k = j := Fin.ext (by simp at h1 h2; omega)
  exact this ▸ hk

private theorem far_supp (hV : ChartOpens E pL pR V) (j k : Fin (r + 1)) (hjk : j.val + 2 ≤ k.val)
    {y : X} (hy1 : y ∈ V j) (hy2 : y ∈ V k)
    (hI : y ∈ ((∏ i, (E i).idealSheaf).support : Set X)) : False := by
  obtain ⟨m, hm⟩ := (mem_support_prod E y).1 hI
  have h1 := val_succ_eq_or_eq_of_mem_V hV hy1 hm
  have h2 := val_succ_eq_or_eq_of_mem_V hV hy2 hm
  omega

private theorem mem_V_right_node (hC : ChainData sX E pL pR) (hV : ChartOpens E pL pR V)
    (j k : Fin r) (hk : k.val = j.val + 1) {y : X} (hy : y ∈ (E j).support) :
    y ∈ V j.castSucc ↔ y ∉ (E k).support := by
  constructor
  · intro h hk'
    have := val_succ_eq_or_eq_of_mem_V hV h hk'
    simp at this; omega
  · intro h
    rw [hV]
    refine ⟨fun k' hk' => ?_, fun h1 hh => ?_, fun h1 hh => ?_⟩
    · have hn := hC.near hk' hy
      by_contra hcon
      have : k' = k := Fin.ext (by simp at hcon ⊢; omega)
      exact h (this ▸ hk')
    · have := hC.pL_only j (hh ▸ hy)
      simp at h1; omega
    · have := hC.pR_only j (hh ▸ hy)
      omega

private theorem mem_V_right_point (hC : ChainData sX E pL pR) (hV : ChartOpens E pL pR V)
    (j : Fin r) (hj : j.val + 1 = r) {y : X} (hy : y ∈ (E j).support) :
    y ∈ V j.castSucc ↔ y ≠ pR := by
  constructor
  · intro h hh
    exact ((hV _ _).1 h).2.2 (by simp) hh
  · intro h
    rw [hV]
    refine ⟨fun k' hk' => ?_, fun h1 hh => ?_, fun _ => h⟩
    · have hn := hC.near hk' hy
      have := k'.isLt
      simp; omega
    · have := hC.pL_only j (hh ▸ hy)
      simp at h1; omega

private theorem mem_V_left_node (hC : ChainData sX E pL pR) (hV : ChartOpens E pL pR V)
    (m k : Fin r) (hk : k.val + 1 = m.val) {y : X} (hy : y ∈ (E m).support) :
    y ∈ V m.succ ↔ y ∉ (E k).support := by
  constructor
  · intro h hk'
    have := val_succ_eq_or_eq_of_mem_V hV h hk'
    simp at this; omega
  · intro h
    rw [hV]
    refine ⟨fun k' hk' => ?_, fun h1 hh => ?_, fun h1 hh => ?_⟩
    · have hn := hC.near hk' hy
      by_contra hcon
      have : k' = k := Fin.ext (by simp at hcon ⊢; omega)
      exact h (this ▸ hk')
    · have := hC.pL_only m (hh ▸ hy)
      omega
    · have := hC.pR_only m (hh ▸ hy)
      simp at h1; omega

private theorem mem_V_left_point (hC : ChainData sX E pL pR) (hV : ChartOpens E pL pR V)
    (m : Fin r) (hm : m.val = 0) {y : X} (hy : y ∈ (E m).support) :
    y ∈ V m.succ ↔ y ≠ pL := by
  constructor
  · intro h hh
    exact ((hV _ _).1 h).2.1 (by simp) hh
  · intro h
    rw [hV]
    refine ⟨fun k' hk' => ?_, fun _ => h, fun h1 hh => ?_⟩
    · have hn := hC.near hk' hy
      simp; omega
    · have := hC.pR_only m (hh ▸ hy)
      simp at h1; omega

end Topology3

open TopologicalSpace in
private theorem vanishingIdeal_closure_genericPoint_eq {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    [IsNormal Y] (E : PrimeDivisor Y) :
    Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({E.genericPoint} : Set Y)) =
      E.idealSheaf := by
  have := E.integral
  rw [Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme E.idealSheaf _ rfl]
  congr 1
  apply Closeds.ext
  rw [Closeds.coe_closure]
  exact (AlgebraicGeometry.PrimeDivisor.support_eq_closure E).symm

open MMP.Resolution.Bridges MMP.Mori TopologicalSpace in
private theorem isIntersectionNumber_of_properCurve' {k : Type u} [Field k] {Y : Scheme.{u}}
    {s : Y ⟶ Spec (.of k)} [QuasiCompact s] [IsLocallyNoetherian Y] [IsNormal Y]
    (D : QDivisor Y) (hD : D.IsQCartier)
    (C : ProperCurve s) (E : PrimeDivisor Y) (hC : C.point = E.genericPoint) :
    IsIntersectionNumber s D E.idealSheaf (D.intersectionNumber k s C.ι C.dim_le hD) := by
  have h : Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({C.point} : Set Y)) =
      E.idealSheaf := by
    rw [hC]; exact vanishingIdeal_closure_genericPoint_eq E
  have : IsIntersectionNumber s D
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({C.point} : Set Y)))
      (D.intersectionNumber k s C.ι C.dim_le hD) := ⟨C.isProper_ι_comp, C.dim_le, hD, rfl⟩
  rwa [h] at this

open MMP.Resolution.Bridges MMP.Mori Stacks.ProjectiveFromSections TopologicalSpace
  AlgebraicGeometry.ProjectiveLineCriterion in
private theorem isProperCurve_of_rational {K : Type u} [Field K] [IsAlgClosed K] {Y : Scheme.{u}}
    [IsLocallyNoetherian Y] [IsNormal Y]
    (sY : Y ⟶ Spec (.of K)) (P : PrimeDivisor Y) (hP : IsSmoothRationalCurve sY P.idealSheaf) :
    IsProperCurve sY P.genericPoint := by
  have key : ∀ I : Y.IdealSheafData, I = P.idealSheaf →
      topologicalKrullDim I.subscheme = 1 ∧ IsProper (I.subschemeι ≫ sY) := by
    rintro I rfl
    obtain ⟨eO⟩ := over_iso_of_rational sY hP
    haveI := isProper_of_iso_projectiveLine eO
    haveI := isCurve_of_iso_projectiveLine eO
    exact ⟨IsCurve.topologicalKrullDim_eq_one (f := P.idealSheaf.subschemeι ≫ sY), inferInstance⟩
  have := key _ (vanishingIdeal_closure_genericPoint_eq P)
  exact ⟨this.1, this.2⟩

open MMP.Resolution.Bridges MMP.Mori TopologicalSpace in
/-- The intersection number one of two distinct curves of the chain is symmetric. -/
private theorem adj_symm {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of K)} [QuasiCompact sX]
    (hsm : IsSmoothScheme sX) (P Q : PrimeDivisor X)
    (hP : IsSmoothRationalCurve sX P.idealSheaf) (hQ : IsSmoothRationalCurve sX Q.idealSheaf)
    (h : IsIntersectionNumber sX (Finsupp.single P 1) Q.idealSheaf 1) :
    IsIntersectionNumber sX (Finsupp.single Q 1) P.idealSheaf 1 := by
  let CP : ProperCurve sX := ⟨P.genericPoint, isProperCurve_of_rational sX P hP⟩
  let CQ : ProperCurve sX := ⟨Q.genericPoint, isProperCurve_of_rational sX Q hQ⟩
  haveI := CP.isProper_ι_comp
  haveI := CQ.isProper_ι_comp
  have hq : ∀ C : PrimeDivisor X, (MMP.Mori.Divisor.toQDivisor (Finsupp.single C 1 : MMP.Mori.Divisor X)) =
      (Finsupp.single C 1 : MMP.Mori.QDivisor X) := by
    intro C
    refine Finsupp.ext fun E => ?_
    change ((Finsupp.single C (1 : ℤ) E : ℤ) : ℚ) = Finsupp.single C (1 : ℚ) E
    by_cases h : C = E
    · subst h; simp
    · simp [h]
  have hQc : MMP.Mori.QDivisor.IsQCartier (Finsupp.single Q 1 : MMP.Mori.QDivisor X) :=
    hq Q ▸ MMP.Threefold.Mori.isQCartier_single_of_isSmoothScheme hsm Q
  have hPc : MMP.Mori.QDivisor.IsQCartier (Finsupp.single P 1 : MMP.Mori.QDivisor X) :=
    hq P ▸ MMP.Threefold.Mori.isQCartier_single_of_isSmoothScheme hsm P
  have h1 := isIntersectionNumber_of_properCurve' (k := K) (Finsupp.single P 1) hPc CQ Q rfl
  have h2 : (MMP.Mori.QDivisor.intersectionNumber K sX CQ.ι CQ.dim_le (Finsupp.single P 1 : MMP.Mori.QDivisor X) hPc) = 1 :=
    IsIntersectionNumber.unique h1 h
  have hcomm := MMP.Threefold.Resolution.intersectionNumber_single_comm hsm P Q CP CQ rfl rfl
  have h3 := isIntersectionNumber_of_properCurve' (k := K) (Finsupp.single Q 1) hQc CP P rfl
  have e3 : MMP.Mori.QDivisor.intersectionNumber K sX CP.ι CP.dim_le (Finsupp.single Q 1 : MMP.Mori.QDivisor X) hQc = 1 := by
    have key : ∀ (C : ProperCurve sX) (D D' : MMP.Mori.QDivisor X) (e : D = D')
        (hD : MMP.Mori.QDivisor.IsQCartier D) (hD' : MMP.Mori.QDivisor.IsQCartier D'),
        MMP.Mori.QDivisor.intersectionNumber K sX C.ι C.dim_le D hD =
          MMP.Mori.QDivisor.intersectionNumber K sX C.ι C.dim_le D' hD' := by
      intro C D D' e; subst e; intros; rfl
    calc _ = MMP.Mori.QDivisor.intersectionNumber K sX CP.ι CP.dim_le
          (MMP.Mori.Divisor.toQDivisor (Finsupp.single Q 1 : MMP.Mori.Divisor X))
          (MMP.Threefold.Mori.isQCartier_single_of_isSmoothScheme hsm Q) :=
          key CP _ _ (hq Q).symm _ _
      _ = MMP.Mori.QDivisor.intersectionNumber K sX CQ.ι CQ.dim_le
          (MMP.Mori.Divisor.toQDivisor (Finsupp.single P 1 : MMP.Mori.Divisor X))
          (MMP.Threefold.Mori.isQCartier_single_of_isSmoothScheme hsm P) := hcomm
      _ = _ := key CQ _ _ (hq P) _ _
      _ = 1 := h2
  rwa [e3] at h3

private theorem exists_closed_point_over {X : Scheme.{u}} (C : X.IdealSheafData) (p : X)
    (hp : p ∈ (C.support : Set X)) (hcl : IsClosed ({p} : Set X)) :
    ∃ q : C.subscheme, C.subschemeι q = p ∧ IsClosed ({q} : Set C.subscheme) ∧
      ∀ z : C.subscheme, C.subschemeι z = p ↔ z = q := by
  rw [← C.range_subschemeι] at hp
  obtain ⟨q, hq⟩ := hp
  have hu : ∀ z : C.subscheme, C.subschemeι z = p ↔ z = q := fun z =>
    ⟨fun h => C.subschemeι.isEmbedding.injective (h.trans hq.symm), fun h => h ▸ hq⟩
  refine ⟨q, hq, ?_, hu⟩
  have : ({q} : Set C.subscheme) = C.subschemeι ⁻¹' {p} := by
    ext z; exact (hu z).symm
  rw [this]
  exact hcl.preimage C.subschemeι.continuous

section CurveOpen

variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of K)} [QuasiCompact sX] {r : ℕ}
  {E : Fin r → PrimeDivisor X} {pL pR : X} {V : Fin (r + 1) → X.Opens}

open MMP.Resolution.Bridges MMP.Mori in
private theorem curve_right_ok (hsm : IsSmoothScheme sX) (hC : ChainData sX E pL pR)
    (hV : ChartOpens E pL pR V) (hpR : IsClosed ({pR} : Set X)) (j : Fin r) :
    IsAffineOpen ((E j).idealSheaf.subschemeι ⁻¹ᵁ V j.castSucc) ∧
      ∃ e : Γ((E j).idealSheaf.subscheme, (E j).idealSheaf.subschemeι ⁻¹ᵁ V j.castSucc) ≃+*
        Polynomial K, ∀ c, e (sigmaSub sX (E j).idealSheaf (V j.castSucc) c) = Polynomial.C c := by
  have hrange : ∀ z : (E j).idealSheaf.subscheme, (E j).idealSheaf.subschemeι z ∈ (E j).support := by
    intro z
    rw [PrimeDivisor.support, ← (E j).idealSheaf.range_subschemeι]; exact ⟨z, rfl⟩
  by_cases hj : j.val + 1 < r
  · let k : Fin r := ⟨j.val + 1, hj⟩
    haveI := MMP.Threefold.Resolution.isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme (sX := sX) hsm (E k)
    have hne : E k ≠ E j := fun h => by
      have := congrArg Fin.val (hC.inj h); simp [k] at this
    have hDC : ¬ (E j).idealSheaf.supportSet ⊆ (E k).idealSheaf.supportSet := fun h =>
      hne (primeDivisor_eq_of_support_subset (E k) (E j) h)
    exact p1_node sX hsm (E k) (E j) (hC.rat j) hDC
      (adj_symm hsm (E j) (E k) (hC.rat j) (hC.rat k) (hC.adj j k rfl)) (V j.castSucc)
      (fun z => mem_V_right_node hC hV j k rfl (hrange z))
  · have hj' : j.val + 1 = r := by omega
    obtain ⟨q, hq, hqc, hu⟩ := exists_closed_point_over (E j).idealSheaf pR (by
      have := (hC.pR_ex); obtain ⟨i, hi, hmem⟩ := this
      have : i = j := Fin.ext (by omega)
      exact this ▸ hmem) hpR
    exact p1_point sX (hC.rat j) q hqc (V j.castSucc) (fun z => by
      rw [mem_V_right_point hC hV j hj' (hrange z)]
      exact not_congr (hu z))

open MMP.Resolution.Bridges MMP.Mori in
private theorem curve_left_ok (hsm : IsSmoothScheme sX) (hC : ChainData sX E pL pR)
    (hV : ChartOpens E pL pR V) (hpL : IsClosed ({pL} : Set X)) (m : Fin r) :
    IsAffineOpen ((E m).idealSheaf.subschemeι ⁻¹ᵁ V m.succ) ∧
      ∃ e : Γ((E m).idealSheaf.subscheme, (E m).idealSheaf.subschemeι ⁻¹ᵁ V m.succ) ≃+*
        Polynomial K, ∀ c, e (sigmaSub sX (E m).idealSheaf (V m.succ) c) = Polynomial.C c := by
  have hrange : ∀ z : (E m).idealSheaf.subscheme, (E m).idealSheaf.subschemeι z ∈ (E m).support := by
    intro z
    rw [PrimeDivisor.support, ← (E m).idealSheaf.range_subschemeι]; exact ⟨z, rfl⟩
  by_cases hm : 1 ≤ m.val
  · let k : Fin r := ⟨m.val - 1, by omega⟩
    haveI := MMP.Threefold.Resolution.isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme (sX := sX) hsm (E k)
    have hne : E k ≠ E m := fun h => by
      have := congrArg Fin.val (hC.inj h); simp [k] at this; omega
    have hDC : ¬ (E m).idealSheaf.supportSet ⊆ (E k).idealSheaf.supportSet := fun h =>
      hne (primeDivisor_eq_of_support_subset (E k) (E m) h)
    exact p1_node sX hsm (E k) (E m) (hC.rat m) hDC (hC.adj k m (by simp [k]; omega))
      (V m.succ) (fun z => mem_V_left_node hC hV m k (by simp [k]; omega) (hrange z))
  · have hm' : m.val = 0 := by omega
    obtain ⟨q, hq, hqc, hu⟩ := exists_closed_point_over (E m).idealSheaf pL (by
      obtain ⟨i, hi, hmem⟩ := hC.pL_ex
      have : i = m := Fin.ext (by omega)
      exact this ▸ hmem) hpL
    exact p1_point sX (hC.rat m) q hqc (V m.succ) (fun z => by
      rw [mem_V_left_point hC hV m hm' (hrange z)]
      exact not_congr (hu z))

end CurveOpen

section ChartData

variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of K)} [QuasiCompact sX] {r : ℕ}
  {E : Fin r → PrimeDivisor X} {pL pR : X} {V : Fin (r + 1) → X.Opens}

/-- On an affine open meeting no other exceptional curve, the ideal of the exceptional locus is
that of the single curve `E j`. -/
private theorem ideal_chainIdeal_eq (E : Fin r → PrimeDivisor X) (W : X.affineOpens) (j : Fin r)
    (hother : ∀ k, k ≠ j → (E k).idealSheaf.ideal W = ⊤) :
    ((∏ i, (E i).idealSheaf) ^ (0 + 1)).ideal W = (E j).idealSheaf.ideal W := by
  rw [zero_add, pow_one, ideal_prod_apply Finset.univ (fun i => (E i).idealSheaf) W]
  exact Finset.prod_eq_single j (fun k _ hk => (hother k hk).trans Ideal.one_eq_top.symm)
    (fun h => absurd (Finset.mem_univ j) h)

private theorem ker_incl_end_bot (hV : ChartOpens E pL pR V) (j : Fin r) (c : Fin (r + 1))
    (hall : ∀ k : Fin r, k.castSucc = c ∨ k.succ = c → k = j)
    (hb : (∏ i, (E i).idealSheaf) ^ (0 + 1) ≤ (E j).idealSheaf) :
    RingHom.ker (inclSections hb (V c)) = ⊥ := by
  have := ker_inf_eq_bot hb hb (V c) (fun W hW => by
    rw [inf_idem, ideal_chainIdeal_eq E W j (fun k hk => ideal_eq_top_of_disjoint _ W (fun y hy =>
      disj_of_V hV c k (fun h => hk (hall k (Or.inl h))) (fun h => hk (hall k (Or.inr h)))
        (hW hy)))])
  rwa [inf_idem] at this

end ChartData

private abbrev chainIdeal {X : Scheme.{u}} {r : ℕ} (E : Fin r → PrimeDivisor X) : X.IdealSheafData :=
  (∏ i, (E i).idealSheaf) ^ (0 + 1)

section ChartData2

variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of K)} [QuasiCompact sX] {r : ℕ}
  {E : Fin r → PrimeDivisor X} {pL pR : X} {V : Fin (r + 1) → X.Opens}

private theorem ZL_preimage_top (hC : ChainData sX E pL pR) (hV : ChartOpens E pL pR V)
    (Z : X.IdealSheafData) (hZ0 : (Z.support : Set X) = {pL}) (c : Fin (r + 1)) (hc : pL ∈ V c)
    (e : Z.subscheme ≅ Spec (.of (Polynomial K ⧸ Ideal.span {(Polynomial.X : Polynomial K) ^ (0 + 1)}))) :
    Z.subschemeι ⁻¹ᵁ V c = ⊤ :=
  subschemeι_preimage_eq_top le_rfl e (subsingleton_primeSpectrum_quot 0) (V c)
    (by rw [hZ0]; exact Set.singleton_subset_iff.2 hc) (by rw [hZ0]; exact ⟨pL, rfl⟩)

private theorem chart_left_end (hsm : IsSmoothScheme sX) (hC : ChainData sX E pL pR)
    (hV : ChartOpens E pL pR V) (hr : 0 < r) (hpR : IsClosed ({pR} : Set X))
    (ZL : ℕ → X.IdealSheafData) (hZL : ∀ n, (∏ i, (E i).idealSheaf) ^ (n + 1) ≤ ZL n)
    (hZL_zero : ((ZL 0).support : Set X) = {pL})
    (hZL_curvilinear : ∀ n, ∃ e : (ZL n).subscheme ≅
      Spec (.of (Polynomial K ⧸ Ideal.span {(Polynomial.X : Polynomial K) ^ (n + 1)})),
      e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K _)) = (ZL n).subschemeι ≫ sX) :
    IsAffineOpen ((chainIdeal E).subschemeι ⁻¹ᵁ V 0) ∧
    ∃ x : Γ((chainIdeal E).subscheme, (chainIdeal E).subschemeι ⁻¹ᵁ V 0),
      Function.Surjective (MvPolynomial.eval₂Hom (sigmaSub sX (chainIdeal E) (V 0)) ![x, 0]) ∧
      RingHom.ker (MvPolynomial.eval₂Hom (sigmaSub sX (chainIdeal E) (V 0)) ![x, 0]) =
        Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 2) K)} ∧
      (∀ b : Fin r, b.castSucc = 0 →
        RingHom.ker (inclSections (pow_le_divisor E 0 b) (V 0)) = ⊥) ∧
      RingHom.ker ((Scheme.IdealSheafData.inclusion (hZL 0)).app ((chainIdeal E).subschemeι ⁻¹ᵁ V 0)).hom =
        Ideal.span {x} := by
  let j : Fin r := ⟨0, hr⟩
  have hj : j.castSucc = 0 := Fin.ext (by simp [j])
  have hb := pow_le_divisor E 0 j
  obtain ⟨hAb, ebK⟩ := curve_right_ok hsm hC hV hpR j
  rw [hj] at hAb ebK
  have hall : ∀ k : Fin r, k.castSucc = 0 ∨ k.succ = 0 → k = j := by
    intro k hk
    rcases hk with h | h
    · exact Fin.ext (by simpa [j] using congrArg Fin.val h)
    · exact absurd (congrArg Fin.val h) (by simp)
  have hinj := ker_incl_end_bot hV j 0 hall hb
  have hsupp : ∀ y ∈ V 0, y ∈ ((chainIdeal E).support : Set X) → y ∈ ((E j).idealSheaf.support : Set X) := by
    intro y hy hI
    obtain ⟨k, hk, hmem⟩ := supp_of_V hV 0 hy (show y ∈ ((∏ i, (E i).idealSheaf).support : Set X) from hI)
    exact hall k hk ▸ hmem
  obtain ⟨e0, he0⟩ := hZL_curvilinear 0
  have hZV := ZL_preimage_top hC hV (ZL 0) hZL_zero 0 (pL_mem_V hC hV) e0
  obtain ⟨hT, ⟨x, hx, h1, h2⟩, -⟩ := end_chart_core sX (chainIdeal E) (E j).idealSheaf (ZL 0) hb (hZL 0)
    (V 0) hAb ebK hinj hsupp e0 he0 hZV
  refine ⟨hT, x, h1, h2, ?_, ?_⟩
  · intro b hb'
    have : b = j := hall b (Or.inl hb')
    subst this
    exact hinj
  · rw [← ker_inclSections_eq_ker_app]; exact hx

end ChartData2

section ChartData3

variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of K)} [QuasiCompact sX] {r : ℕ}
  {E : Fin r → PrimeDivisor X} {pL pR : X} {V : Fin (r + 1) → X.Opens}

private theorem chart_right_end (hsm : IsSmoothScheme sX) (hC : ChainData sX E pL pR)
    (hV : ChartOpens E pL pR V) (hr : 0 < r) (hpL : IsClosed ({pL} : Set X))
    (ZR : ℕ → X.IdealSheafData) (hZR : ∀ n, (∏ i, (E i).idealSheaf) ^ (n + 1) ≤ ZR n)
    (hZR_zero : ((ZR 0).support : Set X) = {pR})
    (hZR_curvilinear : ∀ n, ∃ e : (ZR n).subscheme ≅
      Spec (.of (Polynomial K ⧸ Ideal.span {(Polynomial.X : Polynomial K) ^ (n + 1)})),
      e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K _)) = (ZR n).subschemeι ≫ sX) :
    IsAffineOpen ((chainIdeal E).subschemeι ⁻¹ᵁ V (Fin.last r)) ∧
    ∃ y : Γ((chainIdeal E).subscheme, (chainIdeal E).subschemeι ⁻¹ᵁ V (Fin.last r)),
      Function.Surjective (MvPolynomial.eval₂Hom (sigmaSub sX (chainIdeal E) (V (Fin.last r))) ![0, y]) ∧
      RingHom.ker (MvPolynomial.eval₂Hom (sigmaSub sX (chainIdeal E) (V (Fin.last r))) ![0, y]) =
        Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin 2) K)} ∧
      (∀ a : Fin r, a.succ = Fin.last r →
        RingHom.ker (inclSections (pow_le_divisor E 0 a) (V (Fin.last r))) = ⊥) ∧
      RingHom.ker ((Scheme.IdealSheafData.inclusion (hZR 0)).app
        ((chainIdeal E).subschemeι ⁻¹ᵁ V (Fin.last r))).hom = Ideal.span {y} := by
  let j : Fin r := ⟨r - 1, by omega⟩
  have hj : j.succ = Fin.last r := Fin.ext (by simp [j]; omega)
  have hb := pow_le_divisor E 0 j
  obtain ⟨hAb, ebK⟩ := curve_left_ok hsm hC hV hpL j
  rw [hj] at hAb ebK
  have hall : ∀ k : Fin r, k.castSucc = Fin.last r ∨ k.succ = Fin.last r → k = j := by
    intro k hk
    rcases hk with h | h
    · exact absurd (congrArg Fin.val h) (by have := k.isLt; simp; omega)
    · exact Fin.ext (by have := congrArg Fin.val h; simp at this; simp [j]; omega)
  have hinj := ker_incl_end_bot hV j (Fin.last r) hall hb
  have hsupp : ∀ y ∈ V (Fin.last r), y ∈ ((chainIdeal E).support : Set X) →
      y ∈ ((E j).idealSheaf.support : Set X) := by
    intro y hy hI
    obtain ⟨k, hk, hmem⟩ := supp_of_V hV (Fin.last r) hy
      (show y ∈ ((∏ i, (E i).idealSheaf).support : Set X) from hI)
    exact hall k hk ▸ hmem
  obtain ⟨e0, he0⟩ := hZR_curvilinear 0
  have hZV : (ZR 0).subschemeι ⁻¹ᵁ V (Fin.last r) = ⊤ :=
    subschemeι_preimage_eq_top le_rfl e0 (subsingleton_primeSpectrum_quot 0) (V (Fin.last r))
      (by rw [hZR_zero]; exact Set.singleton_subset_iff.2 (pR_mem_V hC hV))
      (by rw [hZR_zero]; exact ⟨pR, rfl⟩)
  obtain ⟨hT, -, ⟨x, hx, h1, h2⟩⟩ := end_chart_core sX (chainIdeal E) (E j).idealSheaf (ZR 0) hb (hZR 0)
    (V (Fin.last r)) hAb ebK hinj hsupp e0 he0 hZV
  refine ⟨hT, x, h1, h2, ?_, ?_⟩
  · intro a ha
    have : a = j := hall a (Or.inr ha)
    subst this
    exact hinj
  · rw [← ker_inclSections_eq_ker_app]; exact hx

end ChartData3

section ChartData4

variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of K)} [QuasiCompact sX] {r : ℕ}
  {E : Fin r → PrimeDivisor X} {pL pR : X} {V : Fin (r + 1) → X.Opens}

private theorem chart_mid (hsm : IsSmoothScheme sX) (hC : ChainData sX E pL pR)
    (hV : ChartOpens E pL pR V) (hpL : IsClosed ({pL} : Set X)) (hpR : IsClosed ({pR} : Set X))
    (c : Fin (r + 1)) (hc0 : 0 < c.val) (hcr : c.val < r) :
    IsAffineOpen ((chainIdeal E).subschemeι ⁻¹ᵁ V c) ∧
    ∃ x y : Γ((chainIdeal E).subscheme, (chainIdeal E).subschemeι ⁻¹ᵁ V c),
      Function.Surjective (MvPolynomial.eval₂Hom (sigmaSub sX (chainIdeal E) (V c)) ![x, y]) ∧
      RingHom.ker (MvPolynomial.eval₂Hom (sigmaSub sX (chainIdeal E) (V c)) ![x, y]) =
        Ideal.span {(MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) K)} ∧
      (∀ b : Fin r, b.castSucc = c →
        RingHom.ker (inclSections (pow_le_divisor E 0 b) (V c)) = Ideal.span {y}) ∧
      (∀ a : Fin r, a.succ = c →
        RingHom.ker (inclSections (pow_le_divisor E 0 a) (V c)) = Ideal.span {x}) := by
  let a : Fin r := ⟨c.val - 1, by omega⟩
  let b : Fin r := ⟨c.val, hcr⟩
  have hac : a.succ = c := Fin.ext (by simp [a]; omega)
  have hbc : b.castSucc = c := Fin.ext (by simp [b])
  have hab : a.val + 1 = b.val := by simp [a, b]; omega
  have hne : E a ≠ E b := fun h => by
    have := congrArg Fin.val (hC.inj h); simp [a, b] at this; omega
  haveI := MMP.Threefold.Resolution.isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme
    (sX := sX) hsm (E a)
  have hDC : ¬ (E b).idealSheaf.supportSet ⊆ (E a).idealSheaf.supportSet := fun h =>
    hne (primeDivisor_eq_of_support_subset (E a) (E b) h)
  obtain ⟨hAa, eaK⟩ := curve_left_ok hsm hC hV hpL a
  obtain ⟨hAb, ebK⟩ := curve_right_ok hsm hC hV hpR b
  rw [hac] at hAa eaK
  rw [hbc] at hAb ebK
  have hall : ∀ k : Fin r, k.castSucc = c ∨ k.succ = c → k = a ∨ k = b := by
    intro k hk
    rcases hk with h | h
    · exact Or.inr (Fin.castSucc_injective _ (h.trans hbc.symm))
    · exact Or.inl (Fin.succ_injective _ (h.trans hac.symm))
  have hsupp : ∀ y ∈ V c, y ∈ ((chainIdeal E).support : Set X) →
      y ∈ ((E a).idealSheaf.support : Set X) ∨ y ∈ ((E b).idealSheaf.support : Set X) := by
    intro y hy hI
    obtain ⟨k, hk, hmem⟩ := supp_of_V hV c hy
      (show y ∈ ((∏ i, (E i).idealSheaf).support : Set X) from hI)
    rcases hall k hk with rfl | rfl
    · exact Or.inl hmem
    · exact Or.inr hmem
  have hW : ∀ W : X.affineOpens, W.1 ≤ V c →
      (E a).idealSheaf.ideal W ⊓ (E b).idealSheaf.ideal W ≤ (chainIdeal E).ideal W := by
    intro W hW
    show _ ≤ ((∏ i, (E i).idealSheaf) ^ (0 + 1)).ideal W
    rw [zero_add, pow_one]
    refine inf_ideal_le_prod E a b (fun h => hne (h ▸ rfl)) hne W (fun k hka hkb => ?_)
    refine ideal_eq_top_of_disjoint _ W (fun y hy => disj_of_V hV c k (fun h => ?_) (fun h => ?_) (hW hy))
    · rcases hall k (Or.inl h) with h' | h'
      · exact hka h'
      · exact hkb h'
    · rcases hall k (Or.inr h) with h' | h'
      · exact hka h'
      · exact hkb h'
  have hnode := fun y => mem_V_node hC hV a b hab c (y := y) (by simp [b])
  obtain ⟨hT, x, y, hxa, hyb, hsurj, hker⟩ := node_chart sX hsm (E a) (E b) hDC (hC.adj a b hab)
    (chainIdeal E) (pow_le_divisor E 0 a) (pow_le_divisor E 0 b) (V c) hAa hAb eaK ebK hsupp hW
    (fun y h1 h2 => hnode y h1 h2)
  refine ⟨hT, x, y, hsurj, hker, ?_, ?_⟩
  · intro b' hb'
    have : b' = b := Fin.castSucc_injective _ (hb'.trans hbc.symm)
    subst this
    exact hyb
  · intro a' ha'
    have : a' = a := Fin.succ_injective _ (ha'.trans hac.symm)
    subst this
    exact hxa

end ChartData4

section Overlap

variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of K)} [QuasiCompact sX] {r : ℕ}
  {E : Fin r → PrimeDivisor X} {pL pR : X} {V : Fin (r + 1) → X.Opens}

/-- The open `T ⊓ W` of the thickening is the non-vanishing locus of a generator of the ideal of
`D` on `T`, provided `D` and `W` cut the same part of the exceptional locus inside `T`. -/
private theorem trace_inf_eq_basicOpen {D : X.IdealSheafData} (hD : chainIdeal E ≤ D) (T W : X.Opens)
    (hT : IsAffineOpen ((chainIdeal E).subschemeι ⁻¹ᵁ T))
    (s : Γ((chainIdeal E).subscheme, (chainIdeal E).subschemeι ⁻¹ᵁ T))
    (hs : RingHom.ker (inclSections hD T) = Ideal.span {s})
    (hiff : ∀ y ∈ T, y ∈ ((chainIdeal E).support : Set X) → (y ∈ W ↔ y ∉ (D.support : Set X))) :
    (chainIdeal E).subschemeι ⁻¹ᵁ (T ⊓ W) = (chainIdeal E).subscheme.basicOpen s := by
  refine SetLike.ext fun z => ?_
  have hrange : (chainIdeal E).subschemeι z ∈ ((chainIdeal E).support : Set X) := by
    rw [← (chainIdeal E).range_subschemeι]; exact ⟨z, rfl⟩
  constructor
  · intro hz
    have hzT : z ∈ (chainIdeal E).subschemeι ⁻¹ᵁ T := hz.1
    rw [mem_basicOpen_iff hD T hT s hs z hzT, ← hiff _ hz.1 hrange]
    exact hz.2
  · intro hz
    have hzT : z ∈ (chainIdeal E).subschemeι ⁻¹ᵁ T := (Scheme.basicOpen_le _ _) hz
    rw [mem_basicOpen_iff hD T hT s hs z hzT, ← hiff _ hzT hrange] at hz
    exact ⟨hzT, hz⟩

private theorem hiff_left_node (hC : ChainData sX E pL pR) (hV : ChartOpens E pL pR V)
    (j a : Fin r) (haj : a.val + 1 = j.val) :
    ∀ y ∈ V j.castSucc, y ∈ ((chainIdeal E).support : Set X) →
      (y ∈ V j.succ ↔ y ∉ ((E a).idealSheaf.support : Set X)) := by
  intro y hy hI
  by_cases hya : y ∈ ((E a).idealSheaf.support : Set X)
  · refine iff_of_false (fun h => ?_) (fun h => h hya)
    have := val_succ_eq_or_eq_of_mem_V hV h hya
    simp at this; omega
  · obtain ⟨k, hk, hmem⟩ := supp_of_V hV _ hy (show y ∈ ((∏ i, (E i).idealSheaf).support : Set X) from hI)
    have hkj : k = j := by
      rcases hk with h | h
      · exact Fin.castSucc_injective _ h
      · exact absurd (by
          have : k = a := Fin.ext (by have := congrArg Fin.val h; simp at this; omega)
          exact this ▸ hmem) hya
    subst hkj
    exact mem_V_left_node hC hV k a haj hmem

private theorem hiff_left_point (hC : ChainData sX E pL pR) (hV : ChartOpens E pL pR V)
    (j : Fin r) (hj : j.val = 0) (Z : X.IdealSheafData) (hZ : (Z.support : Set X) = {pL}) :
    ∀ y ∈ V j.castSucc, y ∈ ((chainIdeal E).support : Set X) →
      (y ∈ V j.succ ↔ y ∉ (Z.support : Set X)) := by
  intro y hy hI
  obtain ⟨k, hk, hmem⟩ := supp_of_V hV _ hy (show y ∈ ((∏ i, (E i).idealSheaf).support : Set X) from hI)
  have hkj : k = j := by
    rcases hk with h | h
    · exact Fin.castSucc_injective _ h
    · exact absurd (congrArg Fin.val h) (by simp [hj])
  subst hkj
  rw [mem_V_left_point hC hV k hj hmem, hZ]
  simp only [Set.mem_singleton_iff]

private theorem hiff_right_node (hC : ChainData sX E pL pR) (hV : ChartOpens E pL pR V)
    (j k : Fin r) (hkj : k.val = j.val + 1) :
    ∀ y ∈ V j.succ, y ∈ ((chainIdeal E).support : Set X) →
      (y ∈ V j.castSucc ↔ y ∉ ((E k).idealSheaf.support : Set X)) := by
  intro y hy hI
  by_cases hyk : y ∈ ((E k).idealSheaf.support : Set X)
  · refine iff_of_false (fun h => ?_) (fun h => h hyk)
    have := val_succ_eq_or_eq_of_mem_V hV h hyk
    simp at this; omega
  · obtain ⟨k', hk', hmem⟩ := supp_of_V hV _ hy (show y ∈ ((∏ i, (E i).idealSheaf).support : Set X) from hI)
    have hk'j : k' = j := by
      rcases hk' with h | h
      · exact absurd (by
          have : k' = k := Fin.ext (by have := congrArg Fin.val h; simp at this; omega)
          exact this ▸ hmem) hyk
      · exact Fin.succ_injective _ h
    subst hk'j
    exact mem_V_right_node hC hV k' k hkj hmem

private theorem hiff_right_point (hC : ChainData sX E pL pR) (hV : ChartOpens E pL pR V)
    (j : Fin r) (hj : j.val + 1 = r) (Z : X.IdealSheafData) (hZ : (Z.support : Set X) = {pR}) :
    ∀ y ∈ V j.succ, y ∈ ((chainIdeal E).support : Set X) →
      (y ∈ V j.castSucc ↔ y ∉ (Z.support : Set X)) := by
  intro y hy hI
  obtain ⟨k', hk', hmem⟩ := supp_of_V hV _ hy (show y ∈ ((∏ i, (E i).idealSheaf).support : Set X) from hI)
  have hk'j : k' = j := by
    rcases hk' with h | h
    · exact absurd (congrArg Fin.val h) (by have := k'.isLt; simp; omega)
    · exact Fin.succ_injective _ h
  subst hk'j
  rw [mem_V_right_point hC hV k' hj hmem, hZ]
  simp only [Set.mem_singleton_iff]

end Overlap

private theorem bijective_constants_of_eq_top {K : Type u} [Field K] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of K)) (hbij : Function.Bijective ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop).hom)
    (W : C.Opens) (hW : W = ⊤) :
    Function.Bijective ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appLE ⊤ W le_top).hom := by
  subst hW
  have e : f.appLE ⊤ ⊤ le_top = f.appTop := Scheme.Hom.appLE_eq_app f
  rw [e]; exact hbij

/-- A section of a scheme with only constants as global sections, given on two opens covering the
scheme and agreeing on the overlap, is constant. -/
private theorem glue_global_const {K : Type u} [Field K] {C : Scheme.{u}} (f : C ⟶ Spec (.of K))
    (hbij : Function.Bijective ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop).hom)
    (U1 U2 : C.Opens) (hcov : U1 ⊔ U2 = ⊤) (s1 : Γ(C, U1)) (s2 : Γ(C, U2))
    (hs : (C.presheaf.map (homOfLE inf_le_left).op).hom s1 =
      (C.presheaf.map (homOfLE inf_le_right).op).hom s2) :
    ∃ k : K, s1 = ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appLE ⊤ U1 le_top).hom k ∧
      s2 = ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appLE ⊤ U2 le_top).hom k := by
  let F := C.sheaf
  let x := (⟨(s1, s2), hs⟩ : RingHom.eqLocus
      (RingHom.comp (F.obj.map (homOfLE inf_le_left : U1 ⊓ U2 ⟶ U1).op).hom
        (RingHom.fst (F.obj.obj <| Opposite.op U1) (F.obj.obj <| Opposite.op U2)))
      (RingHom.comp (F.obj.map (homOfLE inf_le_right : U1 ⊓ U2 ⟶ U2).op).hom
        (RingHom.snd (F.obj.obj <| Opposite.op U1) (F.obj.obj <| Opposite.op U2))))
  let g := ((F.objSupIsoProdEqLocus U1 U2).inv x : F.1.obj (Opposite.op (U1 ⊔ U2)))
  have h1 : (C.presheaf.map (homOfLE le_sup_left).op).hom g = s1 :=
    TopCat.Sheaf.objSupIsoProdEqLocus_inv_fst F U1 U2 x
  have h2 : (C.presheaf.map (homOfLE le_sup_right).op).hom g = s2 :=
    TopCat.Sheaf.objSupIsoProdEqLocus_inv_snd F U1 U2 x
  obtain ⟨k, hk⟩ := (bijective_constants_of_eq_top f hbij (U1 ⊔ U2) hcov).2 g
  refine ⟨k, ?_, ?_⟩
  · rw [← h1, ← hk]
    exact (map_constants_restrict f (U1 ⊔ U2) U1 le_sup_left k).symm ▸ rfl
  · rw [← h2, ← hk]
    exact (map_constants_restrict f (U1 ⊔ U2) U2 le_sup_right k).symm ▸ rfl

section TransitionAlg

open MvPolynomial

private theorem transition_zero_alg {K : Type u} [Field K]
    {B1 B2 G : Type u} [CommRing B1] [CommRing B2] [CommRing G] [Algebra K B1] [Algebra K B2]
    [Algebra K G] [Algebra B1 G] [Algebra B2 G] [IsScalarTower K B1 G] [IsScalarTower K B2 G]
    (J1 J2 : Ideal (MvPolynomial (Fin 2) K))
    (hJ1 : J1 = Ideal.span {X 1} ∨ J1 = Ideal.span {X 0 * X 1})
    (hJ2 : J2 = Ideal.span {X 0} ∨ J2 = Ideal.span {X 1 * X 0})
    (e1 : MvPolynomial (Fin 2) K →ₐ[K] B1) (e2 : MvPolynomial (Fin 2) K →ₐ[K] B2)
    (h1s : Function.Surjective e1) (h2s : Function.Surjective e2)
    (h1k : RingHom.ker e1 = J1) (h2k : RingHom.ker e2 = J2)
    [IsLocalization.Away (e1 (X 0)) G] [IsLocalization.Away (e2 (X 1)) G]
    (H : ∀ p q : Polynomial K,
      algebraMap B1 G (Polynomial.aeval (e1 (X 0)) p) = algebraMap B2 G (Polynomial.aeval (e2 (X 1)) q) →
        ∃ k : K, algebraMap B1 G (Polynomial.aeval (e1 (X 0)) p) = algebraMap K G k) :
    ∃ d : K, d ≠ 0 ∧ algebraMap B2 G (e2 (X 1)) * algebraMap B1 G (e1 (X 0)) = algebraMap K G d := by
  obtain ⟨Λ, hΛT, hΛC⟩ := model_laurent e1 hJ1 (by decide) h1s h1k (A0 := G)
  obtain ⟨Λ', hΛ'T, hΛ'C⟩ := model_laurent e2 hJ2 (by decide) h2s h2k (A0 := G)
  have hP : ∀ (B : Type u) [CommRing B] [Algebra K B] [Algebra B G] [IsScalarTower K B G]
      (Λ : LaurentPolynomial K ≃+* G) (b : B)
      (hT : Λ (LaurentPolynomial.T 1) = algebraMap B G b)
      (hC : ∀ k : K, Λ (LaurentPolynomial.C k) = algebraMap K G k) (p : Polynomial K),
      Λ (Polynomial.toLaurent p) = algebraMap B G (Polynomial.aeval b p) := by
    intro B _ _ _ _ Λ b hT hC p
    have : (Λ.toRingHom.comp (Polynomial.toLaurent : Polynomial K →+* LaurentPolynomial K)) =
        (algebraMap B G).comp (Polynomial.aeval b : Polynomial K →ₐ[K] B).toRingHom := by
      refine Polynomial.ringHom_ext (fun k => ?_) ?_
      · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
          Polynomial.toLaurent_C, hC]
        simp [← IsScalarTower.algebraMap_apply]
      · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
          Polynomial.toLaurent_X, hT]
        simp
    exact congrArg (fun F => F p) this
  obtain ⟨d, hd, hdd⟩ := laurent_transition Λ Λ' hΛC hΛ'C (fun p q hpq => by
    have h1 := hP B1 Λ _ hΛT hΛC p
    have h2 := hP B2 Λ' _ hΛ'T hΛ'C q
    rw [h1, h2] at hpq
    obtain ⟨k, hk⟩ := H p q hpq
    exact ⟨k, h1.trans hk⟩)
  refine ⟨d, hd, ?_⟩
  rw [hΛT, hΛ'T] at hdd
  rw [mul_comm]; exact hdd

end TransitionAlg

section TransitionGeo

variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of K)} [QuasiCompact sX] {r : ℕ}
  {E : Fin r → PrimeDivisor X} {pL pR : X} {V : Fin (r + 1) → X.Opens}

open Stacks.ProjectiveFromSections AlgebraicGeometry.ProjectiveLineCriterion in
private theorem exists_transition_const (hC : ChainData sX E pL pR) (hV : ChartOpens E pL pR V)
    (j : Fin r)
    (x1 y1 : Γ((chainIdeal E).subscheme, (chainIdeal E).subschemeι ⁻¹ᵁ V j.castSucc))
    (x2 y2 : Γ((chainIdeal E).subscheme, (chainIdeal E).subschemeι ⁻¹ᵁ V j.succ))
    (hT1 : IsAffineOpen ((chainIdeal E).subschemeι ⁻¹ᵁ V j.castSucc))
    (hT2 : IsAffineOpen ((chainIdeal E).subschemeι ⁻¹ᵁ V j.succ))
    (J1 J2 : Ideal (MvPolynomial (Fin 2) K))
    (hJ1 : J1 = Ideal.span {MvPolynomial.X 1} ∨ J1 = Ideal.span {MvPolynomial.X 0 * MvPolynomial.X 1})
    (hJ2 : J2 = Ideal.span {MvPolynomial.X 0} ∨ J2 = Ideal.span {MvPolynomial.X 1 * MvPolynomial.X 0})
    (h1s : Function.Surjective (MvPolynomial.eval₂Hom (sigmaSub sX (chainIdeal E) (V j.castSucc)) ![x1, y1]))
    (h1k : RingHom.ker (MvPolynomial.eval₂Hom (sigmaSub sX (chainIdeal E) (V j.castSucc)) ![x1, y1]) = J1)
    (h2s : Function.Surjective (MvPolynomial.eval₂Hom (sigmaSub sX (chainIdeal E) (V j.succ)) ![x2, y2]))
    (h2k : RingHom.ker (MvPolynomial.eval₂Hom (sigmaSub sX (chainIdeal E) (V j.succ)) ![x2, y2]) = J2)
    (hy1 : RingHom.ker (inclSections (pow_le_divisor E 0 j) (V j.castSucc)) = Ideal.span {y1})
    (hx2 : RingHom.ker (inclSections (pow_le_divisor E 0 j) (V j.succ)) = Ideal.span {x2})
    (hov1 : (chainIdeal E).subschemeι ⁻¹ᵁ (V j.castSucc ⊓ V j.succ) = (chainIdeal E).subscheme.basicOpen x1)
    (hov2 : (chainIdeal E).subschemeι ⁻¹ᵁ (V j.castSucc ⊓ V j.succ) = (chainIdeal E).subscheme.basicOpen y2) :
    ∃ d : K, d ≠ 0 ∧
      ((chainIdeal E).subscheme.presheaf.map (homOfLE (Scheme.Hom.preimage_mono _
        (inf_le_right : V j.castSucc ⊓ V j.succ ≤ V j.succ))).op).hom y2 *
      ((chainIdeal E).subscheme.presheaf.map (homOfLE (Scheme.Hom.preimage_mono _
        (inf_le_left : V j.castSucc ⊓ V j.succ ≤ V j.castSucc))).op).hom x1 =
        sigmaSub sX (chainIdeal E) (V j.castSucc ⊓ V j.succ) d := by
  classical
  have hmul : ∀ (J : Ideal (MvPolynomial (Fin 2) K)),
      (J = Ideal.span {MvPolynomial.X 1} ∨ J = Ideal.span {MvPolynomial.X 0 * MvPolynomial.X 1}) →
      (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) K) ∈ J := by
    intro J hJ
    rcases hJ with rfl | rfl
    · exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    · exact Ideal.mem_span_singleton_self _
  have hxy1 : x1 * y1 = 0 := by
    have := hmul J1 hJ1
    rw [← h1k, RingHom.mem_ker] at this
    simp only [map_mul, MvPolynomial.eval₂Hom_X', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons] at this
    exact this
  letI algK : ∀ U : X.Opens, Algebra K Γ((chainIdeal E).subscheme, (chainIdeal E).subschemeι ⁻¹ᵁ U) :=
    fun U => (sigmaSub sX (chainIdeal E) U).toAlgebra
  have halg : ∀ U (k : K), algebraMap K Γ((chainIdeal E).subscheme, (chainIdeal E).subschemeι ⁻¹ᵁ U) k =
      sigmaSub sX (chainIdeal E) U k := fun _ _ => rfl
  letI alg1 : Algebra Γ((chainIdeal E).subscheme, (chainIdeal E).subschemeι ⁻¹ᵁ V j.castSucc)
      Γ((chainIdeal E).subscheme, (chainIdeal E).subschemeι ⁻¹ᵁ (V j.castSucc ⊓ V j.succ)) :=
    (((chainIdeal E).subscheme.presheaf.map (homOfLE (Scheme.Hom.preimage_mono _
      (inf_le_left : V j.castSucc ⊓ V j.succ ≤ V j.castSucc))).op).hom).toAlgebra
  letI alg2 : Algebra Γ((chainIdeal E).subscheme, (chainIdeal E).subschemeι ⁻¹ᵁ V j.succ)
      Γ((chainIdeal E).subscheme, (chainIdeal E).subschemeι ⁻¹ᵁ (V j.castSucc ⊓ V j.succ)) :=
    (((chainIdeal E).subscheme.presheaf.map (homOfLE (Scheme.Hom.preimage_mono _
      (inf_le_right : V j.castSucc ⊓ V j.succ ≤ V j.succ))).op).hom).toAlgebra
  haveI : IsScalarTower K Γ((chainIdeal E).subscheme, (chainIdeal E).subschemeι ⁻¹ᵁ V j.castSucc)
      Γ((chainIdeal E).subscheme, (chainIdeal E).subschemeι ⁻¹ᵁ (V j.castSucc ⊓ V j.succ)) :=
    IsScalarTower.of_algebraMap_eq fun k => (sigmaSub_restrict sX (chainIdeal E) inf_le_left k).symm
  haveI : IsScalarTower K Γ((chainIdeal E).subscheme, (chainIdeal E).subschemeι ⁻¹ᵁ V j.succ)
      Γ((chainIdeal E).subscheme, (chainIdeal E).subschemeι ⁻¹ᵁ (V j.castSucc ⊓ V j.succ)) :=
    IsScalarTower.of_algebraMap_eq fun k => (sigmaSub_restrict sX (chainIdeal E) inf_le_right k).symm
  let e1 : MvPolynomial (Fin 2) K →ₐ[K] Γ((chainIdeal E).subscheme, (chainIdeal E).subschemeι ⁻¹ᵁ V j.castSucc) :=
    MvPolynomial.aeval ![x1, y1]
  let e2 : MvPolynomial (Fin 2) K →ₐ[K] Γ((chainIdeal E).subscheme, (chainIdeal E).subschemeι ⁻¹ᵁ V j.succ) :=
    MvPolynomial.aeval ![x2, y2]
  have he1 : e1 (MvPolynomial.X 0) = x1 := by simp [e1]
  have he2 : e2 (MvPolynomial.X 1) = y2 := by simp [e2]
  haveI : IsLocalization.Away (e1 (MvPolynomial.X 0))
      Γ((chainIdeal E).subscheme, (chainIdeal E).subschemeι ⁻¹ᵁ (V j.castSucc ⊓ V j.succ)) := by
    rw [he1]
    exact hT1.isLocalization_of_eq_basicOpen x1
      (homOfLE (Scheme.Hom.preimage_mono _ (inf_le_left : V j.castSucc ⊓ V j.succ ≤ V j.castSucc)))
      hov1
  haveI : IsLocalization.Away (e2 (MvPolynomial.X 1))
      Γ((chainIdeal E).subscheme, (chainIdeal E).subschemeι ⁻¹ᵁ (V j.castSucc ⊓ V j.succ)) := by
    rw [he2]
    exact hT2.isLocalization_of_eq_basicOpen y2
      (homOfLE (Scheme.Hom.preimage_mono _ (inf_le_right : V j.castSucc ⊓ V j.succ ≤ V j.succ)))
      hov2
  have hux : IsUnit (algebraMap Γ((chainIdeal E).subscheme, (chainIdeal E).subschemeι ⁻¹ᵁ V j.castSucc)
      Γ((chainIdeal E).subscheme, (chainIdeal E).subschemeι ⁻¹ᵁ (V j.castSucc ⊓ V j.succ)) x1) := by
    have := IsLocalization.Away.algebraMap_isUnit (S := Γ((chainIdeal E).subscheme, (chainIdeal E).subschemeι ⁻¹ᵁ
      (V j.castSucc ⊓ V j.succ))) (e1 (MvPolynomial.X 0))
    rwa [he1] at this
  have hy1G : algebraMap Γ((chainIdeal E).subscheme, (chainIdeal E).subschemeι ⁻¹ᵁ V j.castSucc)
      Γ((chainIdeal E).subscheme, (chainIdeal E).subschemeι ⁻¹ᵁ (V j.castSucc ⊓ V j.succ)) y1 = 0 := by
    refine (hux.mul_right_eq_zero).1 ?_
    rw [← map_mul, hxy1, map_zero]
  -- the sections on the curve `E j`
  obtain ⟨eO⟩ := over_iso_of_rational sX (hC.rat j)
  haveI := isIso_globalSections_of_iso_projectiveLine eO
  have hbij : Function.Bijective ((Scheme.ΓSpecIso (.of K)).inv ≫
      ((E j).idealSheaf.subschemeι ≫ sX).appTop).hom :=
    (asIso ((Scheme.ΓSpecIso (.of K)).inv ≫
      ((E j).idealSheaf.subschemeι ≫ sX).appTop)).commRingCatIsoToRingEquiv.bijective
  have hrange : ∀ z : (E j).idealSheaf.subscheme,
      (E j).idealSheaf.subschemeι z ∈ (E j).support := by
    intro z
    rw [PrimeDivisor.support, ← (E j).idealSheaf.range_subschemeι]; exact ⟨z, rfl⟩
  have hcov : (E j).idealSheaf.subschemeι ⁻¹ᵁ V j.castSucc ⊔ (E j).idealSheaf.subschemeι ⁻¹ᵁ V j.succ =
      ⊤ := by
    refine eq_top_iff.2 fun z _ => ?_
    rcases cover_E hC hV j (hrange z) with h | h
    · exact Or.inl h
    · exact Or.inr h
  have H : ∀ p q : Polynomial K,
      algebraMap Γ((chainIdeal E).subscheme, (chainIdeal E).subschemeι ⁻¹ᵁ V j.castSucc)
        Γ((chainIdeal E).subscheme, (chainIdeal E).subschemeι ⁻¹ᵁ (V j.castSucc ⊓ V j.succ))
        (Polynomial.aeval (e1 (MvPolynomial.X 0)) p) =
      algebraMap Γ((chainIdeal E).subscheme, (chainIdeal E).subschemeι ⁻¹ᵁ V j.succ)
        Γ((chainIdeal E).subscheme, (chainIdeal E).subschemeι ⁻¹ᵁ (V j.castSucc ⊓ V j.succ))
        (Polynomial.aeval (e2 (MvPolynomial.X 1)) q) →
      ∃ k : K, algebraMap Γ((chainIdeal E).subscheme, (chainIdeal E).subschemeι ⁻¹ᵁ V j.castSucc)
        Γ((chainIdeal E).subscheme, (chainIdeal E).subschemeι ⁻¹ᵁ (V j.castSucc ⊓ V j.succ))
        (Polynomial.aeval (e1 (MvPolynomial.X 0)) p) =
        algebraMap K Γ((chainIdeal E).subscheme, (chainIdeal E).subschemeι ⁻¹ᵁ (V j.castSucc ⊓ V j.succ)) k := by
    intro p q hpq
    set a := Polynomial.aeval (e1 (MvPolynomial.X 0)) p with ha
    set b := Polynomial.aeval (e2 (MvPolynomial.X 1)) q with hb
    have hE := pow_le_divisor E 0 j
    have hs : ((E j).idealSheaf.subscheme.presheaf.map (homOfLE (inf_le_left :
          (E j).idealSheaf.subschemeι ⁻¹ᵁ V j.castSucc ⊓ (E j).idealSheaf.subschemeι ⁻¹ᵁ V j.succ ≤
            (E j).idealSheaf.subschemeι ⁻¹ᵁ V j.castSucc)).op).hom
          (inclSections hE (V j.castSucc) a) =
        ((E j).idealSheaf.subscheme.presheaf.map (homOfLE (inf_le_right :
          (E j).idealSheaf.subschemeι ⁻¹ᵁ V j.castSucc ⊓ (E j).idealSheaf.subschemeι ⁻¹ᵁ V j.succ ≤
            (E j).idealSheaf.subschemeι ⁻¹ᵁ V j.succ)).op).hom
          (inclSections hE (V j.succ) b) := by
      have h1 := inclSections_restrict hE (inf_le_left : V j.castSucc ⊓ V j.succ ≤ V j.castSucc) a
      have h2 := inclSections_restrict hE (inf_le_right : V j.castSucc ⊓ V j.succ ≤ V j.succ) b
      refine h1.trans (Eq.trans ?_ h2.symm)
      congr 1
    obtain ⟨k, hk1, -⟩ := glue_global_const ((E j).idealSheaf.subschemeι ≫ sX) hbij _ _ hcov _ _ hs
    have hmem : a - sigmaSub sX (chainIdeal E) (V j.castSucc) k ∈
        RingHom.ker (inclSections hE (V j.castSucc)) := by
      rw [RingHom.mem_ker, map_sub, inclSections_sigma, hk1, sub_self]
    rw [hy1, Ideal.mem_span_singleton'] at hmem
    obtain ⟨t, ht⟩ := hmem
    refine ⟨k, ?_⟩
    have : a = t * y1 + sigmaSub sX (chainIdeal E) (V j.castSucc) k := by rw [ht]; ring
    rw [this, map_add, map_mul, hy1G, mul_zero, zero_add, halg]
    exact sigmaSub_restrict sX (chainIdeal E) inf_le_left k
  obtain ⟨d, hd, hdd⟩ := transition_zero_alg J1 J2 hJ1 hJ2 e1 e2 h1s h2s h1k h2k H
  refine ⟨d, hd, ?_⟩
  rw [he1, he2] at hdd
  exact hdd

end TransitionGeo

private theorem exists_level_zero_charts
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 2 sX]
    [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]
    {r : ℕ} (hr : 0 < r) (E : Fin r → PrimeDivisor X) (b : Fin r → ℤ)
    (hinj : Function.Injective E)
    (hrat : ∀ i, IsSmoothRationalCurve sX (E i).idealSheaf)
    (hself : ∀ i, IsIntersectionNumber sX (Finsupp.single (E i) 1) (E i).idealSheaf (-(b i)))
    (hadj : ∀ i j : Fin r, i.val + 1 = j.val →
      IsIntersectionNumber sX (Finsupp.single (E i) 1) (E j).idealSheaf 1)
    (hfar : ∀ i j : Fin r, i.val + 1 < j.val → Disjoint (E i).support (E j).support)
    (pL pR : X) (hpLR : pL ≠ pR)
    (hpL : pL ∈ (E ⟨0, hr⟩).support) (hpL' : ∀ i, i ≠ ⟨0, hr⟩ → pL ∉ (E i).support)
    (hpR : pR ∈ (E ⟨r - 1, by omega⟩).support)
    (hpR' : ∀ i, i ≠ ⟨r - 1, by omega⟩ → pR ∉ (E i).support)
    (ZL ZR : ℕ → X.IdealSheafData)
    (hZL : ∀ n, (∏ i, (E i).idealSheaf) ^ (n + 1) ≤ ZL n)
    (hZR : ∀ n, (∏ i, (E i).idealSheaf) ^ (n + 1) ≤ ZR n)
    (hZL_succ : ∀ n, ZL n = ZL (n + 1) ⊔ (∏ i, (E i).idealSheaf) ^ (n + 1))
    (hZR_succ : ∀ n, ZR n = ZR (n + 1) ⊔ (∏ i, (E i).idealSheaf) ^ (n + 1))
    (hZL_zero : ((ZL 0).support : Set X) = {pL}) (hZR_zero : ((ZR 0).support : Set X) = {pR})
    (hZL_curvilinear : ∀ n, ∃ e : (ZL n).subscheme ≅
      Spec (.of (Polynomial K ⧸ Ideal.span {(Polynomial.X : Polynomial K) ^ (n + 1)})),
      e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K _)) = (ZL n).subschemeι ≫ sX)
    (hZR_curvilinear : ∀ n, ∃ e : (ZR n).subscheme ≅
      Spec (.of (Polynomial K ⧸ Ideal.span {(Polynomial.X : Polynomial K) ^ (n + 1)})),
      e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K _)) = (ZR n).subschemeι ≫ sX) :
    let I := ∏ i, (E i).idealSheaf
    -- the `(n+1)`-st thickening `(n+1)E` and the trace on it of an open of `X`
    let S : ℕ → Scheme.{u} := fun n => (I ^ (n + 1)).subscheme
    let tr : ∀ n, X.Opens → (S n).Opens := fun n V => (I ^ (n + 1)).subschemeι ⁻¹ᵁ V
    -- the constants `K → Γ((n+1)E, U)`
    let σ : ∀ n (U : (S n).Opens), K →+* Γ(S n, U) := fun n U =>
      ((Scheme.ΓSpecIso (.of K)).inv ≫
        ((I ^ (n + 1)).subschemeι ≫ sX).appLE ⊤ U le_top).hom
    -- the restriction `(n+2)E → (n+1)E`
    let ρ : ∀ n (V : X.Opens), Γ(S (n + 1), tr (n + 1) V) → Γ(S n, tr n V) := fun n V =>
      ((Scheme.IdealSheafData.inclusion (pow_le_pow_right_of_le_one' le_top
          (Nat.le_succ (n + 1)) : I ^ (n + 1 + 1) ≤ I ^ (n + 1))).appLE (tr (n + 1) V) (tr n V)
        (by
          simp only [tr, ← Scheme.Hom.comp_preimage,
            Scheme.IdealSheafData.inclusion_subschemeι, le_refl])).hom
    -- restriction to a smaller open of `X`
    let res : ∀ n (V W : X.Opens), W ≤ V → Γ(S n, tr n V) → Γ(S n, tr n W) :=
      fun n _ _ h => ((S n).presheaf.map (homOfLE (Scheme.Hom.preimage_mono _ h)).op).hom
    -- the exceptional ideal of chart `j`: `(y)`, `(x y)` or `(x)`
    let J : Fin (r + 1) → Ideal (MvPolynomial (Fin 2) K) := fun j =>
      if j = 0 then Ideal.span {MvPolynomial.X 1}
      else if j = Fin.last r then Ideal.span {MvPolynomial.X 0}
      else Ideal.span {MvPolynomial.X 0 * MvPolynomial.X 1}
    ∃ (V : Fin (r + 1) → X.Opens) (x0 y0 : ∀ j, Γ(S 0, tr 0 (V j))),
      (((I.support : Set X) ⊆ ⋃ j, (V j : Set X)) ∧
      (pL ∈ V 0 ∧ pR ∈ V (Fin.last r) ∧ (RingHom.ker ((Scheme.IdealSheafData.inclusion (hZL 0)).app (tr 0 (V 0))).hom =
            Ideal.span {x0 0} ∧
          RingHom.ker ((Scheme.IdealSheafData.inclusion (hZR 0)).app
            (tr 0 (V (Fin.last r)))).hom = Ideal.span {y0 (Fin.last r)})) ∧
      (∀ j, IsAffineOpen (tr 0 (V j)) ∧
      Function.Surjective (MvPolynomial.eval₂Hom (σ 0 (tr 0 (V j))) ![x0 j, y0 j]) ∧
      RingHom.ker (MvPolynomial.eval₂Hom (σ 0 (tr 0 (V j))) ![x0 j, y0 j]) = J j ^ (0 + 1)) ∧
      (∀ j : Fin r, ((V j.castSucc ⊓ V j.succ : X.Opens) : Set X) ∩ I.support ⊆ (E j).support) ∧ (∀ j : Fin r, tr 0 (V j.castSucc ⊓ V j.succ) = (S 0).basicOpen (x0 j.castSucc) ∧
        tr 0 (V j.castSucc ⊓ V j.succ) = (S 0).basicOpen (y0 j.succ)) ∧ (∀ j k : Fin (r + 1), j.val + 2 ≤ k.val →
      ((V j ⊓ V k : X.Opens) : Set X) ∩ I.support = ∅) ∧ (∀ j : Fin r, ∃ d : K, d ≠ 0 ∧
        res 0 (V j.succ) (V j.castSucc ⊓ V j.succ) inf_le_right (y0 j.succ) *
          res 0 (V j.castSucc) (V j.castSucc ⊓ V j.succ) inf_le_left (x0 j.castSucc) = σ 0 (tr 0 (V j.castSucc ⊓ V j.succ)) d) ∧
      LocalEquations E V x0 y0) := by
  intro I S tr σ ρ res J
  have hsm : IsSmoothScheme sX := smoothScheme_of_smooth sX
  have hC : ChainData sX E pL pR :=
    { inj := hinj
      rat := hrat
      adj := hadj
      far := hfar
      hpLR := hpLR
      pL_ex := ⟨⟨0, hr⟩, rfl, hpL⟩
      pL_only := fun i hi => by
        by_contra h
        exact hpL' i (fun h' => h (by rw [h'])) hi
      pR_ex := ⟨⟨r - 1, by omega⟩, by simp; omega, hpR⟩
      pR_only := fun i hi => by
        by_contra h
        exact hpR' i (fun h' => h (by rw [h']; simp; omega)) hi }
  have hpLc : IsClosed ({pL} : Set X) := hZL_zero ▸ (ZL 0).support.isClosed
  have hpRc : IsClosed ({pR} : Set X) := hZR_zero ▸ (ZR 0).support.isClosed
  obtain ⟨V, hV⟩ := exists_chart_opens E pL pR hpLc hpRc
  have hchart : ∀ c : Fin (r + 1), ∃ x y : Γ((chainIdeal E).subscheme, (chainIdeal E).subschemeι ⁻¹ᵁ V c),
      IsAffineOpen ((chainIdeal E).subschemeι ⁻¹ᵁ V c) ∧
      Function.Surjective (MvPolynomial.eval₂Hom (sigmaSub sX (chainIdeal E) (V c)) ![x, y]) ∧
      RingHom.ker (MvPolynomial.eval₂Hom (sigmaSub sX (chainIdeal E) (V c)) ![x, y]) =
        (if c = 0 then Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 2) K)}
          else if c = Fin.last r then Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin 2) K)}
          else Ideal.span {(MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) K)}) ∧
      (∀ b : Fin r, b.castSucc = c →
        RingHom.ker (inclSections (pow_le_divisor E 0 b) (V c)) = Ideal.span {y}) ∧
      (∀ a : Fin r, a.succ = c →
        RingHom.ker (inclSections (pow_le_divisor E 0 a) (V c)) = Ideal.span {x}) ∧
      (c = 0 → RingHom.ker ((Scheme.IdealSheafData.inclusion (hZL 0)).app
        ((chainIdeal E).subschemeι ⁻¹ᵁ V c)).hom = Ideal.span {x}) ∧
      (c = Fin.last r → RingHom.ker ((Scheme.IdealSheafData.inclusion (hZR 0)).app
        ((chainIdeal E).subschemeι ⁻¹ᵁ V c)).hom = Ideal.span {y}) := by
    intro c
    have hr0 : (0 : Fin (r + 1)) ≠ Fin.last r := fun h => by
      have := congrArg Fin.val h; simp at this; omega
    by_cases h0 : c = 0
    · subst h0
      obtain ⟨hT, x, hs, hk, hb, hm⟩ := chart_left_end hsm hC hV hr hpRc ZL hZL hZL_zero
        hZL_curvilinear
      refine ⟨x, 0, hT, hs, ?_, fun b hb' => ?_, fun a ha => ?_, fun _ => hm, fun h => absurd h hr0⟩
      · rw [if_pos rfl]; exact hk
      · rw [hb b hb']; exact Ideal.span_zero.symm
      · exact absurd ha (Fin.succ_ne_zero a)
    by_cases hl : c = Fin.last r
    · subst hl
      obtain ⟨hT, y, hs, hk, ha, hm⟩ := chart_right_end hsm hC hV hr hpLc ZR hZR hZR_zero
        hZR_curvilinear
      refine ⟨0, y, hT, hs, ?_, fun b hb' => ?_, fun a ha' => ?_, fun h => absurd h h0, fun _ => hm⟩
      · rw [if_neg h0, if_pos rfl]; exact hk
      · exact absurd hb' (Fin.castSucc_lt_last b).ne
      · rw [ha a ha']; exact Ideal.span_zero.symm
    · have hc0 : 0 < c.val := by
        rcases Nat.eq_zero_or_pos c.val with h | h
        · exact absurd (Fin.ext (by simpa using h)) h0
        · exact h
      have hcr : c.val < r := by
        have := c.isLt
        rcases Nat.lt_or_ge c.val r with h | h
        · exact h
        · exact absurd (Fin.ext (by simp; omega)) hl
      obtain ⟨hT, x, y, hs, hk, hb, ha⟩ := chart_mid hsm hC hV hpLc hpRc c hc0 hcr
      exact ⟨x, y, hT, hs, by rw [if_neg h0, if_neg hl]; exact hk, hb, ha,
        fun h => absurd h h0, fun h => absurd h hl⟩
  choose x0 y0 hP using hchart
  have hE : ∀ j : Fin r, (chainIdeal E).subschemeι ⁻¹ᵁ (V j.castSucc ⊓ V j.succ) =
        (chainIdeal E).subscheme.basicOpen (x0 j.castSucc) ∧
      (chainIdeal E).subschemeι ⁻¹ᵁ (V j.castSucc ⊓ V j.succ) = (chainIdeal E).subscheme.basicOpen (y0 j.succ) := by
    intro j
    constructor
    · by_cases hj0 : j.val = 0
      · have hc1 : j.castSucc = 0 := Fin.ext (by simp [hj0])
        have hmk := (hP j.castSucc).2.2.2.2.2.1 hc1
        rw [← ker_inclSections_eq_ker_app] at hmk
        exact trace_inf_eq_basicOpen (hZL 0) _ _ (hP j.castSucc).1 _ hmk
          (hiff_left_point hC hV j hj0 (ZL 0) hZL_zero)
      · let a : Fin r := ⟨j.val - 1, by omega⟩
        have haj : a.succ = j.castSucc := Fin.ext (by simp [a]; omega)
        have hxa := (hP j.castSucc).2.2.2.2.1 a haj
        exact trace_inf_eq_basicOpen (pow_le_divisor E 0 a) _ _ (hP j.castSucc).1 _ hxa
          (hiff_left_node hC hV j a (by simp [a]; omega))
    · by_cases hj1 : j.val + 1 < r
      · let k : Fin r := ⟨j.val + 1, hj1⟩
        have hkj : k.castSucc = j.succ := Fin.ext (by simp [k])
        have hy := (hP j.succ).2.2.2.1 k hkj
        have := trace_inf_eq_basicOpen (pow_le_divisor E 0 k) (V j.succ) (V j.castSucc)
          (hP j.succ).1 _ hy (hiff_right_node hC hV j k rfl)
        rwa [inf_comm] at this
      · have hl : j.succ = Fin.last r := Fin.ext (by simp; omega)
        have hmk := (hP j.succ).2.2.2.2.2.2 hl
        rw [← ker_inclSections_eq_ker_app] at hmk
        have := trace_inf_eq_basicOpen (hZR 0) (V j.succ) (V j.castSucc) (hP j.succ).1 _ hmk
          (hiff_right_point hC hV j (by omega) (ZR 0) hZR_zero)
        rwa [inf_comm] at this
  refine ⟨V, x0, y0, ?_, ?_, ?_, ?_, hE, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨j, hj⟩ := supp_cover hC hV (show y ∈ ((∏ i, (E i).idealSheaf).support : Set X) from hy)
    exact Set.mem_iUnion.2 ⟨j, hj⟩
  · exact ⟨pL_mem_V hC hV, pR_mem_V hC hV, (hP 0).2.2.2.2.2.1 rfl,
      (hP (Fin.last r)).2.2.2.2.2.2 rfl⟩
  · intro j
    obtain ⟨hT, hs, hk, -⟩ := hP j
    refine ⟨hT, hs, ?_⟩
    simp only [J, zero_add, pow_one]
    exact hk
  · intro j y hy
    exact overlap_supp hC hV j hy.1.1 hy.1.2 hy.2
  · intro j k hjk
    exact Set.eq_empty_iff_forall_notMem.2 fun y hy => far_supp hV j k hjk hy.1.1 hy.1.2 hy.2
  · intro j
    have hl1 : j.castSucc ≠ Fin.last r := (Fin.castSucc_lt_last j).ne
    have hn2 : j.succ ≠ 0 := Fin.succ_ne_zero j
    obtain ⟨hT1, hs1, hk1, hb1, -, -, -⟩ := hP j.castSucc
    obtain ⟨hT2, hs2, hk2, -, ha2, -, -⟩ := hP j.succ
    exact exists_transition_const hC hV j (x0 j.castSucc) (y0 j.castSucc) (x0 j.succ) (y0 j.succ)
      hT1 hT2 _ _
      (by by_cases h : j.castSucc = 0
          · left; rw [if_pos h]
          · right; rw [if_neg h, if_neg hl1])
      (by by_cases h : j.succ = Fin.last r
          · left; rw [if_neg hn2, if_pos h]
          · right; rw [if_neg hn2, if_neg h, mul_comm])
      hs1 hk1 hs2 hk2 (hb1 j rfl) (ha2 j rfl) (hE j).1 (hE j).2
  · exact ⟨fun j => cover_E hC hV j,
      fun j => ⟨(hP j.castSucc).2.2.2.1 j rfl, (hP j.succ).2.2.2.2.1 j rfl⟩,
      fun c k h1 h2 y hy => disj_of_V hV c k h1 h2 hy⟩

private theorem exists_charts_with_constants
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 2 sX]
    [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]
    {r : ℕ} (hr : 0 < r) (E : Fin r → PrimeDivisor X) (b : Fin r → ℤ)
    (hinj : Function.Injective E)
    (hrat : ∀ i, IsSmoothRationalCurve sX (E i).idealSheaf)
    (hself : ∀ i, IsIntersectionNumber sX (Finsupp.single (E i) 1) (E i).idealSheaf (-(b i)))
    (hadj : ∀ i j : Fin r, i.val + 1 = j.val →
      IsIntersectionNumber sX (Finsupp.single (E i) 1) (E j).idealSheaf 1)
    (hfar : ∀ i j : Fin r, i.val + 1 < j.val → Disjoint (E i).support (E j).support)
    (pL pR : X) (hpLR : pL ≠ pR)
    (hpL : pL ∈ (E ⟨0, hr⟩).support) (hpL' : ∀ i, i ≠ ⟨0, hr⟩ → pL ∉ (E i).support)
    (hpR : pR ∈ (E ⟨r - 1, by omega⟩).support)
    (hpR' : ∀ i, i ≠ ⟨r - 1, by omega⟩ → pR ∉ (E i).support)
    (ZL ZR : ℕ → X.IdealSheafData)
    (hZL : ∀ n, (∏ i, (E i).idealSheaf) ^ (n + 1) ≤ ZL n)
    (hZR : ∀ n, (∏ i, (E i).idealSheaf) ^ (n + 1) ≤ ZR n)
    (hZL_succ : ∀ n, ZL n = ZL (n + 1) ⊔ (∏ i, (E i).idealSheaf) ^ (n + 1))
    (hZR_succ : ∀ n, ZR n = ZR (n + 1) ⊔ (∏ i, (E i).idealSheaf) ^ (n + 1))
    (hZL_zero : ((ZL 0).support : Set X) = {pL}) (hZR_zero : ((ZR 0).support : Set X) = {pR})
    (hZL_curvilinear : ∀ n, ∃ e : (ZL n).subscheme ≅
      Spec (.of (Polynomial K ⧸ Ideal.span {(Polynomial.X : Polynomial K) ^ (n + 1)})),
      e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K _)) = (ZL n).subschemeι ≫ sX)
    (hZR_curvilinear : ∀ n, ∃ e : (ZR n).subscheme ≅
      Spec (.of (Polynomial K ⧸ Ideal.span {(Polynomial.X : Polynomial K) ^ (n + 1)})),
      e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K _)) = (ZR n).subschemeι ≫ sX) :
    let I := ∏ i, (E i).idealSheaf
    -- the `(n+1)`-st thickening `(n+1)E` and the trace on it of an open of `X`
    let S : ℕ → Scheme.{u} := fun n => (I ^ (n + 1)).subscheme
    let tr : ∀ n, X.Opens → (S n).Opens := fun n V => (I ^ (n + 1)).subschemeι ⁻¹ᵁ V
    -- the constants `K → Γ((n+1)E, U)`
    let σ : ∀ n (U : (S n).Opens), K →+* Γ(S n, U) := fun n U =>
      ((Scheme.ΓSpecIso (.of K)).inv ≫
        ((I ^ (n + 1)).subschemeι ≫ sX).appLE ⊤ U le_top).hom
    -- the restriction `(n+2)E → (n+1)E`
    let ρ : ∀ n (V : X.Opens), Γ(S (n + 1), tr (n + 1) V) → Γ(S n, tr n V) := fun n V =>
      ((Scheme.IdealSheafData.inclusion (pow_le_pow_right_of_le_one' le_top
          (Nat.le_succ (n + 1)) : I ^ (n + 1 + 1) ≤ I ^ (n + 1))).appLE (tr (n + 1) V) (tr n V)
        (by
          simp only [tr, ← Scheme.Hom.comp_preimage,
            Scheme.IdealSheafData.inclusion_subschemeι, le_refl])).hom
    -- restriction to a smaller open of `X`
    let res : ∀ n (V W : X.Opens), W ≤ V → Γ(S n, tr n V) → Γ(S n, tr n W) :=
      fun n _ _ h => ((S n).presheaf.map (homOfLE (Scheme.Hom.preimage_mono _ h)).op).hom
    -- the exceptional ideal of chart `j`: `(y)`, `(x y)` or `(x)`
    let J : Fin (r + 1) → Ideal (MvPolynomial (Fin 2) K) := fun j =>
      if j = 0 then Ideal.span {MvPolynomial.X 1}
      else if j = Fin.last r then Ideal.span {MvPolynomial.X 0}
      else Ideal.span {MvPolynomial.X 0 * MvPolynomial.X 1}
    ∃ (V : Fin (r + 1) → X.Opens) (x y : ∀ j n, Γ(S n, tr n (V j))),
      -- the charts cover `E`
      ((I.support : Set X) ⊆ ⋃ j, (V j : Set X)) ∧
      -- `x j`, `y j` are formal functions: compatible along the thickenings
      (∀ j n, ρ n (V j) (x j (n + 1)) = x j n ∧ ρ n (V j) (y j (n + 1)) = y j n) ∧
      -- chart `j` is the completion of `𝔸²` along `J j`
      (∀ j n, IsAffineOpen (tr n (V j)) ∧
        Function.Surjective (MvPolynomial.eval₂Hom (σ n (tr n (V j))) ![x j n, y j n]) ∧
        RingHom.ker (MvPolynomial.eval₂Hom (σ n (tr n (V j))) ![x j n, y j n]) = J j ^ (n + 1))
      ∧
      -- the markings are the axes `x 0 = 0` and `y r = 0`
      (pL ∈ V 0 ∧ pR ∈ V (Fin.last r) ∧
        ∀ n, RingHom.ker ((Scheme.IdealSheafData.inclusion (hZL n)).app (tr n (V 0))).hom =
            Ideal.span {x 0 n} ∧
          RingHom.ker ((Scheme.IdealSheafData.inclusion (hZR n)).app
            (tr n (V (Fin.last r)))).hom = Ideal.span {y (Fin.last r) n}) ∧
      -- consecutive charts meet along the formal neighbourhood of `𝔾_m ⊆ E j`
      (∀ j : Fin r, (((V j.castSucc ⊓ V j.succ : X.Opens) : Set X) ∩ I.support ⊆ (E j).support) ∧
        ∀ n, tr n (V j.castSucc ⊓ V j.succ) = (S n).basicOpen (x j.castSucc n) ∧
          tr n (V j.castSucc ⊓ V j.succ) = (S n).basicOpen (y j.succ n)) ∧
      -- non-consecutive charts do not meet
      (∀ j k : Fin (r + 1), j.val + 2 ≤ k.val →
        ((V j ⊓ V k : X.Opens) : Set X) ∩ I.support = ∅) ∧
      -- the initial data of the transitions, with constants `c, d`
      (∀ j : Fin r, ∃ c d : K, c ≠ 0 ∧ d ≠ 0 ∧
        res 0 (V j.succ) (V j.castSucc ⊓ V j.succ) inf_le_right (y j.succ 0) *
          res 0 (V j.castSucc) (V j.castSucc ⊓ V j.succ) inf_le_left (x j.castSucc 0) =
            σ 0 (tr 0 (V j.castSucc ⊓ V j.succ)) d ∧
        ∃ u : (Γ(S 1, tr 1 (V j.castSucc ⊓ V j.succ)))ˣ,
          (u : Γ(S 1, tr 1 (V j.castSucc ⊓ V j.succ))) =
            res 1 (V j.castSucc) (V j.castSucc ⊓ V j.succ) inf_le_left (x j.castSucc 1) ∧
          res 1 (V j.succ) (V j.castSucc ⊓ V j.succ) inf_le_right (x j.succ 1) =
            σ 1 (tr 1 (V j.castSucc ⊓ V j.succ)) c * ↑(u ^ b j) *
              res 1 (V j.castSucc) (V j.castSucc ⊓ V j.succ) inf_le_left (y j.castSucc 1)) := by
  intro I S tr σ ρ res J
  obtain ⟨V, x0, y0, hP⟩ := exists_level_zero_charts sX hr E b hinj hrat hself hadj hfar pL pR hpLR hpL hpL' hpR hpR' ZL ZR hZL hZR hZL_succ hZR_succ hZL_zero hZR_zero hZL_curvilinear hZR_curvilinear
  obtain ⟨x, y, hxy, hcomp, hchart, hmark, hov, hlev⟩ := lift_charts_to_thickenings sX hr E b hinj hrat hself hadj hfar pL pR hpLR hpL hpL' hpR hpR' ZL ZR hZL hZR hZL_succ hZR_succ hZL_zero hZR_zero hZL_curvilinear hZR_curvilinear V x0 y0 hP
  have hx : ∀ j, x j 0 = x0 j := fun j => (hxy j).1
  have hy : ∀ j, y j 0 = y0 j := fun j => (hxy j).2
  have htr := transition_constants sX hr E b hinj hrat hself hadj hfar pL pR hpLR hpL hpL' hpR hpR' ZL ZR hZL hZR hZL_succ hZR_succ hZL_zero hZR_zero hZL_curvilinear hZR_curvilinear V x y (by simp only [hx, hy]; exact hP) hlev hcomp hchart hov
  obtain ⟨hcov, ⟨hL, hR, -⟩, -, hovsup, -, hnon, -⟩ := hP
  exact ⟨V, x, y, hcov, hcomp, hchart, ⟨hL, hR, hmark⟩, fun j => ⟨hovsup j, hov j⟩, hnon, htr⟩

end MMP.Mori.MarkedChainCharts

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite

namespace MMP.Mori

namespace MarkedChainCharts

/-- Given nonzero constants `c j`, `d j`, there are nonzero rescalings `a j`, `h j` of the
coordinates of `r + 1` consecutive charts normalizing the transitions
`x (j+1) = c j * x j ^ b j * y j` and `y (j+1) * x j = d j` to constant one. -/
theorem exists_rescaling_constants {K : Type*} [Field K] {r : ℕ} (b : Fin r → ℤ)
    (c d : Fin r → K) (hc : ∀ j, c j ≠ 0) (hd : ∀ j, d j ≠ 0) :
    ∃ a h : Fin (r + 1) → K, (∀ j, a j ≠ 0) ∧ (∀ j, h j ≠ 0) ∧
      (∀ j : Fin r, a j.succ * c j = a j.castSucc ^ b j * h j.castSucc) ∧
      ∀ j : Fin r, h j.succ * (d j * a j.castSucc) = 1 := by
  let c' : ℕ → K := fun m => if hm : m < r then c ⟨m, hm⟩ else 1
  let d' : ℕ → K := fun m => if hm : m < r then d ⟨m, hm⟩ else 1
  let b' : ℕ → ℤ := fun m => if hm : m < r then b ⟨m, hm⟩ else 0
  have hc' : ∀ m, c' m ≠ 0 := fun m => by
    by_cases hm : m < r <;> simp [c', hm, hc]
  have hd' : ∀ m, d' m ≠ 0 := fun m => by
    by_cases hm : m < r <;> simp [d', hm, hd]
  let ah : ℕ → K × K := fun m => Nat.rec (1, 1)
    (fun m p => (p.1 ^ b' m * p.2 / c' m, (d' m * p.1)⁻¹)) m
  have hah : ∀ m, (ah m).1 ≠ 0 ∧ (ah m).2 ≠ 0 := by
    intro m
    induction m with
    | zero => simp [ah]
    | succ m ih =>
      change (ah m).1 ^ b' m * (ah m).2 / c' m ≠ 0 ∧ (d' m * (ah m).1)⁻¹ ≠ 0
      exact ⟨div_ne_zero (mul_ne_zero (zpow_ne_zero _ ih.1) ih.2) (hc' m),
        inv_ne_zero (mul_ne_zero (hd' m) ih.1)⟩
  refine ⟨fun j => (ah j.val).1, fun j => (ah j.val).2, fun j => (hah j.val).1,
    fun j => (hah j.val).2, fun j => ?_, fun j => ?_⟩
  · change (ah (j.val + 1)).1 * c j = (ah j.val).1 ^ b j * (ah j.val).2
    have e1 : (ah (j.val + 1)).1 = (ah j.val).1 ^ b' j.val * (ah j.val).2 / c' j.val := rfl
    have hb : b' j.val = b j := by simp [b', j.isLt]
    have hcj : c' j.val = c j := by simp [c', j.isLt]
    rw [e1, hb, hcj]
    have := hc j
    field_simp
  · change (d' (j.val) * (ah j.val).1)⁻¹ * (d j * (ah j.val).1) = 1
    have hdj : d' j.val = d j := by simp [d', j.isLt]
    rw [hdj]
    have := hd j
    have := (hah j.val).1
    field_simp

/-- Rescaling `y` by `σ e` and `x` by `σ a`, where `e * (d * a) = 1`, turns the relation
`y * x = σ d` into `y * x = 1`. -/
theorem rescale_mul_eq_one {K R : Type*} [CommRing K] [CommRing R] (σ : K →+* R) {y x : R}
    {d e a : K} (hyx : y * x = σ d) (hk : e * (d * a) = 1) : σ e * y * (σ a * x) = 1 := by
  have h := congrArg σ hk
  rw [map_mul, map_mul, map_one] at h
  linear_combination (σ e * σ a) * hyx + h

/-- Evaluating `𝔸²` at the rescaled coordinates `(σ a * x, σ h * y)` is evaluation at `(x, y)`
after the coordinate rescaling `scale a h`. -/
theorem eval₂Hom_scale {K : Type u} {R : Type*} [Field K] [CommRing R] (σ : K →+* R)
    (a h : K) (x y : R) :
    MvPolynomial.eval₂Hom σ ![σ a * x, σ h * y] =
      (MvPolynomial.eval₂Hom σ ![x, y]).comp (MMP.Resolution.MarkedChain.scale a h) := by
  refine MvPolynomial.ringHom_ext (fun k => ?_) (fun i => ?_)
  · simp [MMP.Resolution.MarkedChain.scale_C]
  · fin_cases i
    · change _ = MvPolynomial.eval₂Hom σ ![x, y]
        (MMP.Resolution.MarkedChain.scale a h (MvPolynomial.X 0))
      rw [MMP.Resolution.MarkedChain.scale_X0]
      simp
    · change _ = MvPolynomial.eval₂Hom σ ![x, y]
        (MMP.Resolution.MarkedChain.scale a h (MvPolynomial.X 1))
      rw [MMP.Resolution.MarkedChain.scale_X1]
      simp

/-- Rescaling `x` by `σ a` and `x'` by `σ a'`, where `a' * c = a ^ b * h`, turns the transition
`x' = σ c * u ^ b * y` into `x' = (σ a * u) ^ b * (σ h * y)`. -/
theorem rescale_transition {K R : Type*} [Field K] [CommRing R] (σ : K →+* R) (u : Rˣ)
    {x' y : R} {a a' c h : K} {b : ℤ} (ha : a ≠ 0) (hx : x' = σ c * ↑(u ^ b) * y)
    (hk : a' * c = a ^ b * h) :
    σ a' * x' = ↑((Units.map (σ : K →* R) (Units.mk0 a ha) * u) ^ b) * (σ h * y) := by
  rw [hx, mul_zpow, Units.val_mul]
  have hz : ((Units.map (σ : K →* R) (Units.mk0 a ha) ^ b : Rˣ) : R) = σ (a ^ b) := by
    rw [← map_zpow, Units.coe_map, Units.val_zpow_eq_zpow_val, Units.val_mk0]
    rfl
  rw [hz]
  have key := congrArg σ hk
  rw [map_mul, map_mul] at key
  linear_combination ((u ^ b : Rˣ) : R) * y * key

end MarkedChainCharts

open MarkedChainCharts MMP.Resolution.MarkedChain in
/-- The formal completion of a smooth surface along a doubly marked chain of smooth rational
curves `E₀, …, E_{r-1}` with `(Eᵢ · Eᵢ) = -bᵢ` has `r + 1` formal coordinate charts
`(x j, y j)`, given level by level on the thickenings `(n+1)E`, with exceptional ideals `(y)`,
`(x y)`, `(x)`, the markings as the axes `x 0 = 0` and `y r = 0`, consecutive charts meeting
along the formal neighbourhood of `𝔾_m ⊆ Eⱼ` and transitions with initial data
`x (j+1) ≡ x j ^ bⱼ * y j (mod (y j)²)` and `y (j+1) * x j ≡ 1 (mod y j)`. -/
@[mmp "lem_mmp_foundation_marked_chain_initial_formal_coordinates"]
public theorem exists_formalCoordinateCharts_of_isSNCChain
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 2 sX]
    [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]
    {r : ℕ} (hr : 0 < r) (E : Fin r → PrimeDivisor X) (b : Fin r → ℤ)
    (hinj : Function.Injective E)
    (hrat : ∀ i, IsSmoothRationalCurve sX (E i).idealSheaf)
    (hself : ∀ i, IsIntersectionNumber sX (Finsupp.single (E i) 1) (E i).idealSheaf (-(b i)))
    (hadj : ∀ i j : Fin r, i.val + 1 = j.val →
      IsIntersectionNumber sX (Finsupp.single (E i) 1) (E j).idealSheaf 1)
    (hfar : ∀ i j : Fin r, i.val + 1 < j.val → Disjoint (E i).support (E j).support)
    (pL pR : X) (hpLR : pL ≠ pR)
    (hpL : pL ∈ (E ⟨0, hr⟩).support) (hpL' : ∀ i, i ≠ ⟨0, hr⟩ → pL ∉ (E i).support)
    (hpR : pR ∈ (E ⟨r - 1, by omega⟩).support)
    (hpR' : ∀ i, i ≠ ⟨r - 1, by omega⟩ → pR ∉ (E i).support)
    (ZL ZR : ℕ → X.IdealSheafData)
    (hZL : ∀ n, (∏ i, (E i).idealSheaf) ^ (n + 1) ≤ ZL n)
    (hZR : ∀ n, (∏ i, (E i).idealSheaf) ^ (n + 1) ≤ ZR n)
    (hZL_succ : ∀ n, ZL n = ZL (n + 1) ⊔ (∏ i, (E i).idealSheaf) ^ (n + 1))
    (hZR_succ : ∀ n, ZR n = ZR (n + 1) ⊔ (∏ i, (E i).idealSheaf) ^ (n + 1))
    (hZL_zero : ((ZL 0).support : Set X) = {pL}) (hZR_zero : ((ZR 0).support : Set X) = {pR})
    (hZL_curvilinear : ∀ n, ∃ e : (ZL n).subscheme ≅
      Spec (.of (Polynomial K ⧸ Ideal.span {(Polynomial.X : Polynomial K) ^ (n + 1)})),
      e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K _)) = (ZL n).subschemeι ≫ sX)
    (hZR_curvilinear : ∀ n, ∃ e : (ZR n).subscheme ≅
      Spec (.of (Polynomial K ⧸ Ideal.span {(Polynomial.X : Polynomial K) ^ (n + 1)})),
      e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K _)) = (ZR n).subschemeι ≫ sX) :
    let I := ∏ i, (E i).idealSheaf
    -- the `(n+1)`-st thickening `(n+1)E` and the trace on it of an open of `X`
    let S : ℕ → Scheme.{u} := fun n => (I ^ (n + 1)).subscheme
    let tr : ∀ n, X.Opens → (S n).Opens := fun n V => (I ^ (n + 1)).subschemeι ⁻¹ᵁ V
    -- the constants `K → Γ((n+1)E, U)`
    let σ : ∀ n (U : (S n).Opens), K →+* Γ(S n, U) := fun n U =>
      ((Scheme.ΓSpecIso (.of K)).inv ≫
        ((I ^ (n + 1)).subschemeι ≫ sX).appLE ⊤ U le_top).hom
    -- the restriction `(n+2)E → (n+1)E`
    let ρ : ∀ n (V : X.Opens), Γ(S (n + 1), tr (n + 1) V) → Γ(S n, tr n V) := fun n V =>
      ((Scheme.IdealSheafData.inclusion (pow_le_pow_right_of_le_one' le_top
          (Nat.le_succ (n + 1)) : I ^ (n + 1 + 1) ≤ I ^ (n + 1))).appLE (tr (n + 1) V) (tr n V)
        (by
          simp only [tr, ← Scheme.Hom.comp_preimage,
            Scheme.IdealSheafData.inclusion_subschemeι, le_refl])).hom
    -- restriction to a smaller open of `X`
    let res : ∀ n (V W : X.Opens), W ≤ V → Γ(S n, tr n V) → Γ(S n, tr n W) :=
      fun n _ _ h => ((S n).presheaf.map (homOfLE (Scheme.Hom.preimage_mono _ h)).op).hom
    -- the exceptional ideal of chart `j`: `(y)`, `(x y)` or `(x)`
    let J : Fin (r + 1) → Ideal (MvPolynomial (Fin 2) K) := fun j =>
      if j = 0 then Ideal.span {MvPolynomial.X 1}
      else if j = Fin.last r then Ideal.span {MvPolynomial.X 0}
      else Ideal.span {MvPolynomial.X 0 * MvPolynomial.X 1}
    ∃ (V : Fin (r + 1) → X.Opens) (x y : ∀ j n, Γ(S n, tr n (V j))),
      -- the charts cover `E`
      ((I.support : Set X) ⊆ ⋃ j, (V j : Set X)) ∧
      -- `x j`, `y j` are formal functions: compatible along the thickenings
      (∀ j n, ρ n (V j) (x j (n + 1)) = x j n ∧ ρ n (V j) (y j (n + 1)) = y j n) ∧
      -- chart `j` is the completion of `𝔸²` along `J j`
      (∀ j n, IsAffineOpen (tr n (V j)) ∧
        Function.Surjective (MvPolynomial.eval₂Hom (σ n (tr n (V j))) ![x j n, y j n]) ∧
        RingHom.ker (MvPolynomial.eval₂Hom (σ n (tr n (V j))) ![x j n, y j n]) = J j ^ (n + 1))
      ∧
      -- the markings are the axes `x 0 = 0` and `y r = 0`
      (pL ∈ V 0 ∧ pR ∈ V (Fin.last r) ∧
        ∀ n, RingHom.ker ((Scheme.IdealSheafData.inclusion (hZL n)).app (tr n (V 0))).hom =
            Ideal.span {x 0 n} ∧
          RingHom.ker ((Scheme.IdealSheafData.inclusion (hZR n)).app
            (tr n (V (Fin.last r)))).hom = Ideal.span {y (Fin.last r) n}) ∧
      -- consecutive charts meet along the formal neighbourhood of `𝔾_m ⊆ E j`
      (∀ j : Fin r, (((V j.castSucc ⊓ V j.succ : X.Opens) : Set X) ∩ I.support ⊆ (E j).support) ∧
        ∀ n, tr n (V j.castSucc ⊓ V j.succ) = (S n).basicOpen (x j.castSucc n) ∧
          tr n (V j.castSucc ⊓ V j.succ) = (S n).basicOpen (y j.succ n)) ∧
      -- non-consecutive charts do not meet
      (∀ j k : Fin (r + 1), j.val + 2 ≤ k.val →
        ((V j ⊓ V k : X.Opens) : Set X) ∩ I.support = ∅) ∧
      -- the normalized initial data of the transitions
      (∀ j : Fin r,
        res 0 (V j.succ) (V j.castSucc ⊓ V j.succ) inf_le_right (y j.succ 0) *
          res 0 (V j.castSucc) (V j.castSucc ⊓ V j.succ) inf_le_left (x j.castSucc 0) = 1 ∧
        ∃ u : (Γ(S 1, tr 1 (V j.castSucc ⊓ V j.succ)))ˣ,
          (u : Γ(S 1, tr 1 (V j.castSucc ⊓ V j.succ))) =
            res 1 (V j.castSucc) (V j.castSucc ⊓ V j.succ) inf_le_left (x j.castSucc 1) ∧
          res 1 (V j.succ) (V j.castSucc ⊓ V j.succ) inf_le_right (x j.succ 1) =
            ↑(u ^ b j) *
              res 1 (V j.castSucc) (V j.castSucc ⊓ V j.succ) inf_le_left (y j.castSucc 1)) := by
  intro I S tr σ ρ res J
  have hρσ : ∀ n (V : X.Opens) (k : K), ρ n V (σ (n + 1) (tr (n + 1) V) k) = σ n (tr n V) k := by
    intro n V k
    refine map_constants_hom ((I ^ (n + 1)).subschemeι ≫ sX) ((I ^ (n + 1 + 1)).subschemeι ≫ sX)
      (Scheme.IdealSheafData.inclusion (pow_le_pow_right_of_le_one' le_top
          (Nat.le_succ (n + 1)) : I ^ (n + 1 + 1) ≤ I ^ (n + 1)))
      (by rw [← Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]) _ _ _ k
  have hresσ : ∀ n (V W : X.Opens) (h : W ≤ V) (k : K),
      res n V W h (σ n (tr n V) k) = σ n (tr n W) k := fun n V W h k =>
    map_constants_restrict _ _ _ _ k
  have hρmul : ∀ n V (p q : Γ(S (n + 1), tr (n + 1) V)), ρ n V (p * q) = ρ n V p * ρ n V q :=
    fun n V p q => map_mul _ _ _
  have hresmul : ∀ n V W h (p q : Γ(S n, tr n V)),
      res n V W h (p * q) = res n V W h p * res n V W h q := fun n V W h p q => map_mul _ _ _
  have hσunit : ∀ n U (k : K), k ≠ 0 → IsUnit (σ n U k) := fun n U k hk =>
    (isUnit_iff_ne_zero.2 hk).map (σ n U)
  obtain ⟨V, x, y, hcov, hcomp, hchart, hmark, hov, hnon, htr⟩ :=
    exists_charts_with_constants sX hr E b hinj hrat hself hadj hfar pL pR hpLR hpL hpL' hpR hpR'
      ZL ZR hZL hZR hZL_succ hZR_succ hZL_zero hZR_zero hZL_curvilinear hZR_curvilinear
  choose c d hc hd h0 hu using htr
  obtain ⟨a, h, ha, hh, hasucc, hhsucc⟩ := exists_rescaling_constants b c d hc hd
  have hbo : ∀ n U (k : K) (z : Γ(S n, U)), k ≠ 0 →
      (S n).basicOpen (σ n U k * z) = (S n).basicOpen z := by
    intro n U k z hk
    rw [Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ (hσunit n U k hk)]
    exact inf_eq_right.2 (Scheme.basicOpen_le _ _)
  refine ⟨V, fun j n => σ n (tr n (V j)) (a j) * x j n, fun j n => σ n (tr n (V j)) (h j) * y j n,
    hcov, ?_, ?_, ?_, ?_, hnon, ?_⟩
  · intro j n
    obtain ⟨h1, h2⟩ : ρ n (V j) (x j (n + 1)) = x j n ∧ ρ n (V j) (y j (n + 1)) = y j n :=
      hcomp j n
    exact ⟨by rw [hρmul, hρσ, h1], by rw [hρmul, hρσ, h2]⟩
  · intro j n
    obtain ⟨haff, hsurj, hker⟩ := hchart j n
    have hker : RingHom.ker (MvPolynomial.eval₂Hom (σ n (tr n (V j))) ![x j n, y j n]) =
        J j ^ (n + 1) := hker
    rw [eval₂Hom_scale]
    refine ⟨haff, ?_, ?_⟩
    · exact hsurj.comp (fun z => ⟨scale (a j)⁻¹ (h j)⁻¹ z, scale_scale' (ha j) (hh j) z⟩)
    · rw [← RingHom.comap_ker, hker]
      exact scale_exceptional_ideal (ha j) (hh j) j (n + 1)
  · obtain ⟨hL, hR, hm⟩ := hmark
    refine ⟨hL, hR, fun n => ?_⟩
    obtain ⟨hm1, hm2⟩ := hm n
    exact ⟨by rw [hm1, Ideal.span_singleton_mul_left_unit (hσunit _ _ _ (ha 0))],
      by rw [hm2, Ideal.span_singleton_mul_left_unit (hσunit _ _ _ (hh _))]⟩
  · intro j
    obtain ⟨h1, h2⟩ := hov j
    refine ⟨h1, fun n => ?_⟩
    obtain ⟨e1, e2⟩ := h2 n
    exact ⟨e1.trans (hbo _ _ _ _ (ha _)).symm, e2.trans (hbo _ _ _ _ (hh _)).symm⟩
  · intro j
    have h0j : res 0 (V j.succ) (V j.castSucc ⊓ V j.succ) inf_le_right (y j.succ 0) *
        res 0 (V j.castSucc) (V j.castSucc ⊓ V j.succ) inf_le_left (x j.castSucc 0) =
          σ 0 (tr 0 (V j.castSucc ⊓ V j.succ)) (d j) := h0 j
    obtain ⟨u, hu1, hu2⟩ : ∃ u : (Γ(S 1, tr 1 (V j.castSucc ⊓ V j.succ)))ˣ,
          (u : Γ(S 1, tr 1 (V j.castSucc ⊓ V j.succ))) =
            res 1 (V j.castSucc) (V j.castSucc ⊓ V j.succ) inf_le_left (x j.castSucc 1) ∧
          res 1 (V j.succ) (V j.castSucc ⊓ V j.succ) inf_le_right (x j.succ 1) =
            σ 1 (tr 1 (V j.castSucc ⊓ V j.succ)) (c j) * ↑(u ^ b j) *
              res 1 (V j.castSucc) (V j.castSucc ⊓ V j.succ) inf_le_left (y j.castSucc 1) := hu j
    constructor
    · rw [hresmul _ _ _ inf_le_right, hresmul _ _ _ inf_le_left, hresσ 0 _ _ inf_le_right,
        hresσ 0 _ _ inf_le_left]
      exact rescale_mul_eq_one _ h0j (hhsucc j)
    · refine ⟨Units.map (σ 1 (tr 1 (V j.castSucc ⊓ V j.succ)) : K →* _)
        (Units.mk0 (a j.castSucc) (ha _)) * u, ?_, ?_⟩
      · rw [Units.val_mul, hu1, hresmul _ _ _ inf_le_left, hresσ 1 _ _ inf_le_left]
        rfl
      · rw [hresmul _ _ _ inf_le_right, hresσ 1 _ _ inf_le_right, hresmul _ _ _ inf_le_left,
          hresσ 1 _ _ inf_le_left]
        exact rescale_transition _ u (ha _) hu2 (hasucc j)

end MMP.Mori

end
