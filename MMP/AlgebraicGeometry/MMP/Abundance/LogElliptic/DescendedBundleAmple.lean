module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Abundance.Defs
import MMP.AlgebraicGeometry.Positivity.SurfaceNakaiCriterion
import MMP.AlgebraicGeometry.FiberSpace.NumericallyTrivialDescent
import MMP.AlgebraicGeometry.Resolution.SmoothBlowupCanonical
import MMP.AlgebraicGeometry.Intersection.CurveDegreeProjection
import MMP.AlgebraicGeometry.MMP.Abundance.ComplementedNefThreefold
import MMP.AlgebraicGeometry.CohenMacaulay.SerreDuality
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Divisor.AmpleSectionDivisor
import MMP.AlgebraicGeometry.ChowForm.FibreDegreeRank
import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
import MMP.AlgebraicGeometry.Positivity.SerreAmpleCartier
import MMP.AlgebraicGeometry.Modules.CurveFibreLineBundle
import MMP.AlgebraicGeometry.Resolution.BlowupChartClosedImmersion
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
import MMP.AlgebraicGeometry.Singularities.Surface.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Positivity.FreePencilCrepant
import MMP.AlgebraicGeometry.Morphisms.ChowLemma
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import MMP.AlgebraicGeometry.Divisor.LinearSystem
import MMP.AlgebraicGeometry.MMP.Threefold.SurfaceLocalRings
import MMP.AlgebraicGeometry.Divisor.Canonical.PluricanonicalForms
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlops
import MMP.AlgebraicGeometry.Morphisms.Smooth.RegularParameters
import MMP.AlgebraicGeometry.Morphisms.Smooth.SmoothFlagParameters
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.MMP.Fourfold.WeakModel
import MMP.AlgebraicGeometry.Singularities.Snc.Basic
import MMP.AlgebraicGeometry.Singularities.Snc.LocalEquations
import MMP.AlgebraicGeometry.ProjectiveSpace.LinearProjection
import MMP.AlgebraicGeometry.Resolution.DisjoiningSequence
import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.ConstructionCenters
import MMP.AlgebraicGeometry.Resolution.MonomialIdealSNC
import MMP.AlgebraicGeometry.Resolution.OneBlowupTotalTransform
import MMP.AlgebraicGeometry.Resolution.OrderReduction.RegularStalkComponents
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite
import MMP.AlgebraicGeometry.Divisor.LocalSectionDivisor
import MMP.AlgebraicGeometry.Resolution.SncPreservingLogResolution
import MMP.AlgebraicGeometry.Intersection.ThreefoldEffectiveIntersection
import MMP.AlgebraicGeometry.Positivity.NakaiMoishezonKleiman
public import MMP.AlgebraicGeometry.Chow.FieldSituation
import MMP.AlgebraicGeometry.Normalization.IntegralScheme

/-!
# Log elliptic fiber spaces (FA, Chapter 15)

Two steps of the abundance argument for log elliptic fiber spaces in FA Chapter 15. Throughout,
`L = K_X + Δ_X` for a canonical divisor `K_X` and a `ℚ`-divisor `Δ_X` on a normal projective
variety `X`.

**Lemma 15.7.** Let `X` be `ℚ`-factorial over an algebraically closed field, `L` nef with
`h⁰(X, 𝒪_X(m₀ L)) ≥ 2` for a Cartier `m₀ L`, and `D` an `L`-trivially connected prime divisor.
Then either `L` is eventually free and composed of a pencil, or some member `d D + D'` of a
linear system `|m L|`, `d ≥ 1`, has `D ⊄ Supp D'` and `D ∩ Supp D' ≠ ∅`.

**Lemma 15.13.** Let `(X, Δ_X)` satisfy the assumptions of 15.4, with no `L`-trivially connected
prime divisor and numerical dimension `ν(X, L) ≥ 2`, and let `f : X ⟶ Z̄` extend the elliptic
fibration of (15.4.3) to a normal projective surface, with `f_* 𝒪_X = 𝒪_{Z̄}` and connected
fibres of pure dimension one (FA Thm. 15.10). If `𝒪_X(n L) ≅ f^* 𝓛` for a line bundle `𝓛` on
`Z̄` and `n > 0`, then `𝓛` is ample. By the Nakai criterion on `Z̄` it suffices that `(𝓛²) > 0`
and `(𝓛 · C) > 0` for every curve `C ⊆ Z̄`:

* `(𝓛²) > 0`: for `H` ample on `X`, `(L² · H) > 0` since `ν(L) ≥ 2`, and
  `n² (L² · H) = (f^*𝓛 · f^*𝓛 · H) = (𝓛²) · deg(H|_{X_η})` with `deg(H|_{X_η}) > 0` on the
  generic fibre `X_η` of `f`;
* `(𝓛 · C) ≥ 0`: a proper curve `Γ ⊆ f⁻¹(C)` dominating `C` has
  `0 ≤ n (L · Γ) = deg_Γ f^*𝓛 = [k(Γ) : k(C)] (𝓛 · C)`;
* `(𝓛 · C) ≠ 0`: otherwise every proper curve in an irreducible surface `S ⊆ f⁻¹(C)` dominating
  `C` is `L`-trivial, and any two closed points of `S` lie on a connected finite union of proper
  curves in `S`, so `S` is an `L`-trivially connected prime divisor.

## Main results

* `MMP.Flips.isAmple_of_divisorialSheaf_iso_pullback`: FA 15.13, the descended bundle `𝓛` is
  ample.
* `MMP.Flips.isEventuallyFreePencil_or_exists_mem_linearSystem_of_isTriviallyConnected`:
  FA 15.7, the dichotomy for an `L`-trivially connected prime divisor.

## Implementation notes

The source works over `ℂ`. Lemma 15.13 is stated over an algebraically closed field `k` of
characteristic zero, as is FA Thm. 15.10
(`MMP.Flips.exists_extension_of_forall_not_isTriviallyConnected`), whose conclusion is taken
as hypotheses on `f`. Lemma 15.7 is stated over any algebraically closed field; some such
hypothesis is needed, since an integral projective `k`-scheme need not be geometrically integral:
for `X = ℙ²_ℂ` over `ℝ` with `L = 0` one has `h⁰(X, 𝒪_X) = 2` while both conclusions fail for a
line. A prime divisor `D` is `Finsupp.single E 1` for
`E : MMP.Mori.PrimeDivisor X`; `n L` is an integral Weil divisor `M` with `M = n • L` as
`ℚ`-divisors, `𝒪_X(M)` is `MMP.Mori.Divisor.divisorialSheaf`, and `d D + D' ∈ |m L|` is a linear
equivalence `d D + D' ∼ M` with `D'` effective.

For 15.13, points of `X` are handled through the specialization order: the closure of `x` has
dimension `height x`. Over the generic point of `C`, a one-dimensional component of the fibre
gives points `y₀ ⤳ y₁` of heights `2` and `1`; `Γ = {y₁}⁻` is a curve dominating `C` and
`S = {y₀}⁻` a prime divisor. Two closed points of `S` are joined on the normalization `S^ν`,
with the pull-back `A` of an ample sheaf of `X`: a divisor of a power of `A` through points over
both of them (and a third closed point) has connected support, as `S^ν` is a normal surface, and
its one-dimensional pieces map to proper curves of `S`. This replaces the source's
`K₁ ∪ (S ∩ A) ∪ K₂`, with `K_i` fibre components of `S → C`.

For 15.7, the source resolves the rational map of the whole of `|M|`, `M = m₀ L`, and separates
`dim φ(X) ≥ 2` from `dim φ(X) = 1`. Here only a pencil `⟨Z₀, Z₁⟩ ⊆ |M|` with
`mult_D Z₀ < mult_D Z₁` is resolved, so its image is `ℙ¹` and the first case does not arise. If no
member as in the second alternative exists, every member of `|M|` meets `D` only along `D`; a
base point of the pencil then lies, with `D`, in one connected fibre of the Stein factorization of
the graph closure, inside `Supp Z₁`, a contradiction. A pencil with disjoint moving parts is a
fibration `p : X ⟶ C` onto a smooth projective curve; Zariski's lemma makes the fixed part a
pull-back, and `L` is `ℚ`-linearly equivalent to the pull-back of an ample divisor on `C`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 15.7, 15.13
-/

open CategoryTheory AlgebraicGeometry

universe u v

namespace MMP.Flips

open MMP.Mori

/-! ### Heights of points of schemes

For a point `x` of a scheme, `Order.height x` (for the specialization order, `x ≤ y ↔ y ⤳ x`) is
the dimension of the closure of `x`. -/

section Heights

variable {X : Scheme.{u}}

/-- The height of a point bounds by the dimension of the scheme. -/
private lemma height_le_topologicalKrullDim (x : X) :
    (Order.height x : WithBot ℕ∞) ≤ topologicalKrullDim X := by
  rw [← topologicalKrullDim_closure_singleton_eq_height]
  exact topologicalKrullDim_subspace_le X _

/-- The height of the generic point of an irreducible scheme is its dimension. -/
private lemma height_genericPoint [IrreducibleSpace X] :
    (Order.height (genericPoint X) : WithBot ℕ∞) = topologicalKrullDim X := by
  rw [← topologicalKrullDim_closure_singleton_eq_height, (genericPoint_spec X).def]
  exact IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ X).isHomeomorph

/-- If `1 ≤ a` and `a + 1 ≤ 2` in `ℕ∞`, then `a = 1`. -/
private lemma ENat.eq_one_of_one_le_of_add_one_le_two {a : ℕ∞} (ha : 1 ≤ a) (h : a + 1 ≤ 2) :
    a = 1 := by
  induction a using ENat.recTopCoe with
  | top => simp at h
  | coe a => norm_cast at *; omega

/-- Two heights strictly between `0` and `3`, the second above the first, are `1` and `2`. -/
private lemma ENat.eq_one_and_eq_two {a b : ℕ∞} (ha : 1 ≤ a) (hab : a + 1 ≤ b)
    (hb : b + 1 ≤ 3) : a = 1 ∧ b = 2 := by
  induction b using ENat.recTopCoe with
  | top => simp at hb
  | coe b =>
    induction a using ENat.recTopCoe with
    | top => simp at hab
    | coe a => norm_cast at *; omega

/-- The closure of a point of height one, in a proper `k`-scheme, is a proper curve. -/
private def properCurveOfHeight {k : Type u} [Field k] (sX : X ⟶ Spec (.of k)) [IsProper sX]
    (x : X) (hx : Order.height x = 1) : ProperCurve sX :=
  ⟨x, isProperCurve_of_isProper sX (by
    rw [MMP.Chow.topologicalKrullDim_curveSubschemeAt_eq,
      topologicalKrullDim_closure_singleton_eq_height, hx]; rfl)⟩

/-- The generic point of `properCurveOfHeight sX x hx` is `x`. -/
private lemma properCurveOfHeight_point {k : Type u} [Field k] (sX : X ⟶ Spec (.of k))
    [IsProper sX] (x : X) (hx : Order.height x = 1) : (properCurveOfHeight sX x hx).point = x :=
  rfl

end Heights

/-! ### Specializations inside a fibre -/

section Fibre

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The generic point of the closure of a nonempty irreducible subset of a fibre `f⁻¹(z)` lies in
that fibre. -/
private lemma apply_genericPoint_closure_eq {z : Y} {A : Set X} (hA : IsIrreducible A)
    (hAz : A ⊆ f.base ⁻¹' {z}) : f hA.genericPoint = z := by
  have hg := hA.isGenericPoint_genericPoint_closure
  have h1 : z ⤳ f hA.genericPoint := by
    rw [specializes_iff_mem_closure]
    have hsub : closure A ⊆ f.base ⁻¹' closure {z} :=
      closure_minimal (hAz.trans (Set.preimage_mono subset_closure))
        (isClosed_closure.preimage f.base.hom.continuous)
    exact hsub (hg.mem)
  obtain ⟨a, ha⟩ := hA.nonempty
  have h2 : hA.genericPoint ⤳ a := hg.specializes (subset_closure ha)
  have h3 : f hA.genericPoint ⤳ z := by
    have := h2.map f.base.hom.continuous
    rwa [show f a = z from hAz ha] at this
  exact (h3.antisymm h1).eq

/-- If an irreducible component of the fibre `f⁻¹(z)` through a point has dimension one, the
fibre contains two distinct points `a ⤳ b`. -/
private lemma exists_specializes_ne_of_fiber {z : Y} {x : X} (hx : f x = z)
    (hfib : ∀ W ∈ irreducibleComponents (f.base ⁻¹' {z}), topologicalKrullDim W = 1) :
    ∃ a b : X, a ⤳ b ∧ a ≠ b ∧ f a = z ∧ f b = z := by
  set P := f.base ⁻¹' {z}
  obtain ⟨W, hW, -⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    ({⟨x, hx⟩} : Set P) isIrreducible_singleton
  have h1 : ((1 : ℕ) : WithBot ℕ∞) ≤ Order.krullDim (TopologicalSpace.IrreducibleCloseds W) := by
    have := hfib W hW
    unfold topologicalKrullDim at this
    rw [this]
    rfl
  obtain ⟨p, hp⟩ := Order.le_krullDim_iff.mp h1
  set φ : W → X := fun w => (w.1.1 : X) with hφ
  have hφc : Continuous φ := continuous_subtype_val.comp continuous_subtype_val
  have hφi : Topology.IsInducing φ :=
    Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal
  have hφP : ∀ w, φ w ∈ P := fun w => w.1.2
  set Z₀ := p 0
  set Z₁ := p (Fin.last _)
  have hlt : Z₀ < Z₁ := p.strictMono (show (0 : Fin (p.length + 1)) < Fin.last _ by
    simp [Fin.lt_def, hp])
  have hA₀ : IsIrreducible (φ '' (Z₀ : Set W)) := Z₀.isIrreducible.image φ hφc.continuousOn
  have hA₁ : IsIrreducible (φ '' (Z₁ : Set W)) := Z₁.isIrreducible.image φ hφc.continuousOn
  have hsub : ∀ Z : TopologicalSpace.IrreducibleCloseds W, φ '' (Z : Set W) ⊆ P := by
    rintro Z _ ⟨w, -, rfl⟩
    exact hφP w
  refine ⟨hA₁.genericPoint, hA₀.genericPoint, ?_, ?_, apply_genericPoint_closure_eq f hA₁ (hsub _),
    apply_genericPoint_closure_eq f hA₀ (hsub _)⟩
  · rw [specializes_iff_mem_closure, hA₁.isGenericPoint_genericPoint_closure.def]
    exact closure_mono (Set.image_mono hlt.le) hA₀.isGenericPoint_genericPoint_closure.mem
  · intro heq
    have hcl : closure (φ '' (Z₁ : Set W)) = closure (φ '' (Z₀ : Set W)) := by
      rw [← hA₁.isGenericPoint_genericPoint_closure.def,
        ← hA₀.isGenericPoint_genericPoint_closure.def, heq]
    obtain ⟨y, hy₁, hy₀⟩ := Set.exists_of_ssubset (show (Z₀ : Set W) ⊂ Z₁ from hlt)
    apply hy₀
    have : y ∈ closure (Z₀ : Set W) := by
      rw [hφi.closure_eq_preimage_closure_image, ← hcl]
      exact subset_closure ⟨y, hy₁, rfl⟩
    rwa [Z₀.isClosed.closure_eq] at this

/-- Under a locally quasi-finite morphism, a point over a closed point is closed: its closure
lies in the fibre, which is discrete. -/
private lemma isClosed_singleton_of_isClosed_image (φ : X ⟶ Y) [LocallyQuasiFinite φ] {t : X}
    (ht : IsClosed ({φ t} : Set Y)) : IsClosed ({t} : Set X) := by
  rw [← closure_subset_iff_isClosed]
  intro t' ht'
  have hsp : t ⤳ t' := specializes_iff_mem_closure.mpr ht'
  have hφ : φ t' = φ t := by
    have := specializes_iff_mem_closure.mp (hsp.map φ.base.hom.continuous)
    rwa [ht.closure_eq] at this
  have hdisc := (φ.isDiscrete_preimage_singleton (φ t)).to_subtype
  have hsub : (⟨t, rfl⟩ : φ.base ⁻¹' {φ t}) ⤳ ⟨t', hφ⟩ :=
    Topology.IsInducing.subtypeVal.specializes_iff.mp hsp
  have := hsub.mem_open (@isOpen_discrete _ _ hdisc {⟨t', hφ⟩}) rfl
  exact (congrArg Subtype.val (Set.mem_singleton_iff.mp this)).symm

end Fibre

/-! ### Connected sets covered by finitely many closed sets -/

/-- A preconnected set with two distinct points, covered by finitely many closed sets, is covered
by those of them that are not subsingletons. -/
private lemma subset_sUnion_not_subsingleton {α : Type*} [TopologicalSpace α] {A : Set α}
    (hA : IsPreconnected A) {a b : α} (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b)
    {𝒲 : Set (Set α)} (h𝒲 : 𝒲.Finite) (hcl : ∀ W ∈ 𝒲, IsClosed W) (hcov : A ⊆ ⋃₀ 𝒲) :
    A ⊆ ⋃₀ {W ∈ 𝒲 | ¬ W.Subsingleton} := by
  intro p hp
  by_contra hpn
  have hsub : ∀ W ∈ 𝒲, p ∈ W → W = {p} := by
    intro W hW hpW
    have hs : W.Subsingleton := by
      by_contra hns
      exact hpn ⟨W, ⟨hW, hns⟩, hpW⟩
    exact hs.eq_singleton_of_mem hpW
  obtain ⟨W₀, hW₀, hpW₀⟩ := hcov hp
  have hpcl : IsClosed ({p} : Set α) := hsub W₀ hW₀ hpW₀ ▸ hcl W₀ hW₀
  set C := ⋃₀ {W ∈ 𝒲 | p ∉ W}
  have hCcl : IsClosed C :=
    (h𝒲.subset fun W hW => hW.1).isClosed_sUnion fun W hW => hcl W hW.1
  have hpC : p ∉ C := by
    rintro ⟨W, ⟨-, hpW⟩, hpW'⟩
    exact hpW hpW'
  have hAC : A ⊆ {p} ∪ C := by
    intro q hq
    obtain ⟨W, hW, hqW⟩ := hcov hq
    by_cases hpW : p ∈ W
    · left
      rw [hsub W hW hpW] at hqW
      exact hqW
    · exact Or.inr ⟨W, ⟨hW, hpW⟩, hqW⟩
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp hA {p} C hpcl hCcl hAC (by
    ext q
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false,
      not_and]
    rintro - rfl hqC
    exact hpC hqC) with h | h
  · exact hab ((h ha).trans (h hb).symm)
  · exact hpC (h hp)

/-! ### Joining points of a surface by curves -/

section Join

variable {X : Scheme.{u}}

/-- A point of height zero is closed. -/
private lemma isClosed_singleton_of_height_eq_zero {t : X} (ht : Order.height t = 0) :
    IsClosed ({t} : Set X) := by
  rw [← closure_subset_iff_isClosed]
  intro p hp
  have hsp : t ⤳ p := specializes_iff_mem_closure.mpr hp
  have hsp' : p ⤳ t :=
    Scheme.le_iff_specializes.mp (Order.height_eq_zero.mp ht (Scheme.le_iff_specializes.mpr hsp))
  exact (hsp.antisymm hsp').eq ▸ rfl

/-- A strict specialization is strictly smaller in the specialization order. -/
private lemma lt_of_specializes_of_ne {a b : X} (h : a ⤳ b) (hne : a ≠ b) : b < a :=
  lt_of_le_not_ge (Scheme.le_iff_specializes.mpr h)
    fun h' => hne (h.antisymm (Scheme.le_iff_specializes.mp h')).eq

variable {k : Type u} [Field k] (sX : X ⟶ Spec (.of k)) [IsProper sX]

/-- **Joining points by curves on a normal surface.** Let `φ : T ⟶ X` be a finite morphism from a
normal integral surface `T`, proper over `k` through `φ ≫ s_X`, carrying an ample invertible sheaf.
Any two closed points of `T` map into one connected finite union of proper curves of `X` contained
in the image of `φ`: the support of an effective Cartier divisor with ample sheaf through the two
points (and a third closed point) is connected, as `T` is normal of dimension two, and its
irreducible components are curves whose images are proper curves of `X`. -/
private lemma exists_isConnected_curveUnion_of_isFinite {T : Scheme.{u}} [IsIntegral T]
    [IsNormal T] (φ : T ⟶ X) [IsFinite φ] (hT : topologicalKrullDim T = 2) (A : T.Modules)
    [Stacks.Ample.IsInvertibleModule T A] (hA : Stacks.Ample.IsAmple T A) {t₁ t₂ : T}
    (ht₁ : IsClosed ({t₁} : Set T)) (ht₂ : IsClosed ({t₂} : Set T)) :
    ∃ S : Finset (ProperCurve sX), _root_.IsConnected (curveUnion sX S) ∧
      curveUnion sX S ⊆ Set.range φ ∧ φ t₁ ∈ curveUnion sX S ∧ φ t₂ ∈ curveUnion sX S := by
  classical
  set sT := φ ≫ sX
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian sT
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace sT
  have : JacobsonSpace T := LocallyOfFiniteType.jacobsonSpace sT
  have : IsNoetherian T := {}
  have hηh : Order.height (genericPoint T) = 2 :=
    WithBot.coe_injective ((height_genericPoint (X := T)).trans hT)
  have hne : ∀ t : T, IsClosed ({t} : Set T) → genericPoint T ≠ t := by
    rintro t ht rfl
    rw [Scheme.height_of_isClosed ht] at hηh
    exact absurd hηh (by decide)
  -- a third closed point, different from `t₁`
  obtain ⟨t₃, ht₃ne, ht₃⟩ : ∃ t₃ : T, t₃ ≠ t₁ ∧ IsClosed ({t₃} : Set T) := by
    obtain ⟨t₃, ht₃, ht₃c⟩ := nonempty_inter_closedPoints (Z := ({t₁}ᶜ : Set T))
      ⟨genericPoint T, hne t₁ ht₁⟩ ht₁.isOpen_compl.isLocallyClosed
    exact ⟨t₃, ht₃, ht₃c⟩
  -- an effective Cartier divisor through the three points, with ample sheaf
  have hT₀ : IsClosed ({t₁, t₂, t₃} : Set T) :=
    ht₁.union (ht₂.union ht₃)
  have hη : genericPoint T ∉ ({t₁, t₂, t₃} : Set T) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hne t₁ ht₁, hne t₂ ht₂, hne t₃ ht₃⟩
  obtain ⟨I, hI, hT₀I, hηI, m, hm, ⟨eI⟩⟩ :=
    MMP.Threefold.Resolution.exists_isEffectiveCartierDivisor_of_isAmple A hA hT₀ hη
  have := hI
  have := Stacks.Divisors.isInvertible_divisorSheaf I
  have hIa : Stacks.Ample.IsAmple T (Stacks.Divisors.divisorSheaf I) :=
    (Stacks.RelativeVeryAmple.isAmple_congr _ _ eI).mp
      (Stacks.AmplePositivePower.isAmple_tensorPowModule_of_isAmple A m hm hA)
  have hconn : _root_.IsConnected (I.support : Set T) := by
    refine MMP.Mori.isConnected_support_of_two_le_depth sT (fun x hx ↦ ?_) I hIa
    refine VectorBundleCodimensionOne.two_le_depth_stalk_of_isNormal x ?_
    rw [← topologicalKrullDimAt_eq_krullDimOfRing_stalk k T sT x hx,
      topologicalKrullDimAt_eq_topologicalKrullDim_of_equidimensional k T sT
        (.of_preirreducibleSpace T) x, hT]
    rfl
  -- the irreducible pieces of `Supp I`
  obtain ⟨𝒲, h𝒲, h𝒲cl, h𝒲irr, h𝒲eq⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible I.support.isClosed
  set 𝒲₁ := {W ∈ 𝒲 | ¬ W.Subsingleton}
  have hsupp : (I.support : Set T) = ⋃₀ 𝒲₁ := by
    refine le_antisymm ?_ ?_
    · exact subset_sUnion_not_subsingleton hconn.isPreconnected (hT₀I (by simp))
        (hT₀I (by simp)) ht₃ne.symm h𝒲 h𝒲cl h𝒲eq.le
    · rw [h𝒲eq]
      exact Set.sUnion_mono fun W hW => hW.1
  choose! gen hgen using fun W (hW : W ∈ 𝒲₁) => QuasiSober.sober (h𝒲irr W hW.1) (h𝒲cl W hW.1)
  have hφc : Continuous φ := φ.base.hom.continuous
  have hφcl : IsClosedMap φ := φ.isClosedMap
  -- the generic points of the pieces have height one, and so do their images
  have hh : ∀ W ∈ 𝒲₁, Order.height (φ (gen W)) = 1 := by
    intro W hW
    have hgW := hgen W hW
    have hmem : gen W ∈ (I.support : Set T) := by
      rw [h𝒲eq]
      exact ⟨W, hW.1, hgW.mem⟩
    have hlt : gen W < genericPoint T :=
      lt_of_specializes_of_ne ((genericPoint_spec T).specializes (Set.mem_univ _))
        fun h => hηI (h ▸ hmem)
    have h1 : Order.height (gen W) + 1 ≤ 2 := hηh ▸ Order.height_add_one_le hlt
    have h2 : 1 ≤ Order.height (gen W) := by
      obtain ⟨a, ha, b, hb, hab⟩ := Set.not_subsingleton_iff.mp hW.2
      obtain ⟨p, hp, hpne⟩ : ∃ p ∈ W, p ≠ gen W := by
        by_cases h : a = gen W
        · exact ⟨b, hb, fun hb' => hab (h.trans hb'.symm)⟩
        · exact ⟨a, ha, h⟩
      have hplt : p < gen W := lt_of_specializes_of_ne (hgW.specializes hp) hpne.symm
      exact le_trans (by simp) (Order.height_add_one_le hplt)
    have hw1 : Order.height (gen W) = 1 := ENat.eq_one_of_one_le_of_add_one_le_two h2 h1
    refine le_antisymm ?_ ?_
    · have := topologicalKrullDim_closure_singleton_image_le k φ sT sX rfl (gen W)
      rw [topologicalKrullDim_closure_singleton_eq_height,
        topologicalKrullDim_closure_singleton_eq_height, hw1] at this
      exact_mod_cast this
    · rw [Order.one_le_iff_pos, pos_iff_ne_zero]
      intro h0
      have hc := isClosed_singleton_of_isClosed_image φ (isClosed_singleton_of_height_eq_zero h0)
      rw [Scheme.height_of_isClosed hc] at hw1
      exact absurd hw1 (by decide)
  -- the curves
  set P : Set X := (fun W => φ (gen W)) '' 𝒲₁
  have hPfin : P.Finite := (h𝒲.subset fun W hW => hW.1).image _
  have hSfin : {C : ProperCurve sX | C.point ∈ P}.Finite :=
    hPfin.preimage fun C _ D _ h => ProperCurve.ext h
  refine ⟨hSfin.toFinset, ?_⟩
  have hU : curveUnion sX hSfin.toFinset = φ '' (I.support : Set T) := by
    ext x
    simp only [curveUnion, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨C, ⟨W, hW, hCW⟩, hx⟩
      have hx' : x ∈ φ '' closure {gen W} := by
        rw [← hφcl.closure_image_eq_of_continuous hφc, Set.image_singleton]
        simp only at hCW
        rwa [hCW]
      rw [(hgen W hW).def] at hx'
      obtain ⟨y, hy, rfl⟩ := hx'
      exact ⟨y, hsupp ▸ ⟨W, hW, hy⟩, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      rw [hsupp] at hy
      obtain ⟨W, hW, hyW⟩ := hy
      refine ⟨properCurveOfHeight sX (φ (gen W)) (hh W hW), ⟨W, hW, rfl⟩, ?_⟩
      rw [properCurveOfHeight_point, ← Set.image_singleton,
        hφcl.closure_image_eq_of_continuous hφc, (hgen W hW).def]
      exact ⟨y, hyW, rfl⟩
  rw [hU]
  refine ⟨hconn.image _ hφc.continuousOn, Set.image_subset_range _ _,
    ⟨t₁, hT₀I (by simp), rfl⟩, ⟨t₂, hT₀I (by simp), rfl⟩⟩

/-- **Any two closed points of a surface in `X` are joined by curves on it.** Let `X` be separated
and proper over `k` with an ample invertible sheaf, and `S = {y}⁻ ⊆ X` an irreducible closed
subset of dimension two. Any two closed points of `S` lie on a connected finite union of proper
curves contained in `S`: apply `exists_isConnected_curveUnion_of_isFinite` to the normalization
`S^ν ⟶ S ⊆ X`, which is finite, with the pull-back of the ample sheaf. -/
private lemma exists_isConnected_curveUnion_of_height_eq_two [IsSeparated sX] (H : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 H] (hH : Stacks.Ample.IsAmple X H)
    {y : X} (hy : Order.height y = 2) {s₁ s₂ : X} (hs₁ : s₁ ∈ closure {y})
    (hs₂ : s₂ ∈ closure {y}) (hc₁ : IsClosed ({s₁} : Set X)) (hc₂ : IsClosed ({s₂} : Set X)) :
    ∃ S : Finset (ProperCurve sX), _root_.IsConnected (curveUnion sX S) ∧
      curveUnion sX S ⊆ closure {y} ∧ s₁ ∈ curveUnion sX S ∧ s₂ ∈ curveUnion sX S := by
  set W := curveSubschemeAt y
  set ι := curveSubschemeAtι y
  have : IsIntegral W :=
    StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible _
      isIrreducible_singleton.closure
  have : AlgebraicGeometry.IsVariety k (ι ≫ sX) := {}
  obtain ⟨⟨hvar, hnorm, hfin, hsurj, -⟩, -⟩ := MMP.Threefold.normalization_spec (ι ≫ sX)
  set ν := W.normalization
    (MMP.finite_irreducibleComponents_of_isIntegral W)
  have := hvar.toIsIntegral
  have := hnorm
  have := hfin
  have := hsurj
  have hrange : Set.range ι = closure {y} := MMP.Mori.range_curveSubschemeAtι y
  have hdimT : topologicalKrullDim (W.normalizationScheme
      (MMP.finite_irreducibleComponents_of_isIntegral W)) = 2 := by
    rw [topologicalKrullDim_eq_of_isFinite_of_isDominant ν,
      MMP.Chow.topologicalKrullDim_curveSubschemeAt_eq,
      topologicalKrullDim_closure_singleton_eq_height, hy]
    rfl
  have hA := (Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple _ _).mp
    (isAmple_pullback_of_isFinite (ν ≫ ι) H
      ((Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple _ _).mpr hH))
  have hpt : ∀ s ∈ closure ({y} : Set X), IsClosed ({s} : Set X) →
      ∃ t, IsClosed ({t} : Set _) ∧ (ν ≫ ι) t = s := by
    intro s hs hc
    rw [← hrange] at hs
    obtain ⟨w, rfl⟩ := hs
    obtain ⟨t, rfl⟩ := ν.surjective w
    exact ⟨t, isClosed_singleton_of_isClosed_image (ν ≫ ι) (by rwa [Scheme.Hom.comp_apply]),
      Scheme.Hom.comp_apply _ _ _⟩
  obtain ⟨t₁, ht₁c, rfl⟩ := hpt s₁ hs₁ hc₁
  obtain ⟨t₂, ht₂c, rfl⟩ := hpt s₂ hs₂ hc₂
  obtain ⟨S, hS, hSr, h₁, h₂⟩ :=
    exists_isConnected_curveUnion_of_isFinite sX (ν ≫ ι) hdimT _ hA ht₁c ht₂c
  refine ⟨S, hS, hSr.trans ?_, h₁, h₂⟩
  rw [← hrange]
  rintro _ ⟨t, rfl⟩
  exact ⟨ν t, (Scheme.Hom.comp_apply _ _ _).symm⟩

end Join

/-! ### Degrees along curves mapping into a curve -/

section Degree

variable {k : Type u} [Field k] {X Z : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  {sZ : Z ⟶ Spec (.of k)}

/-- A proper curve on a separated `k`-scheme of finite type is a curve over `k`. -/
private lemma isCurve_properCurve [IsSeparated sX] [LocallyOfFiniteType sX] [QuasiCompact sX]
    (Γ : ProperCurve sX) : AlgebraicGeometry.IsCurve k (Γ.ι ≫ sX) :=
  have : IsIntegral Γ.scheme :=
    StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible _
      isIrreducible_singleton.closure
  { toIsIntegral := inferInstance
    toIsSeparated := inferInstance
    toLocallyOfFiniteType := inferInstance
    toQuasiCompact := inferInstance
    topologicalKrullDim_eq_one := Γ.dim_eq }

/-- **The degree of a pulled-back bundle along a curve over a curve.** Let `f : X ⟶ Z` be a
`k`-morphism, `C ⊆ Z` an integral proper curve and `Γ ⊆ X` a proper curve with `f(Γ) ⊆ C`. Then
`deg_Γ f^*𝓛 = d · deg_C 𝓛` for a natural number `d`, with `d > 0` if `f|_Γ` is not constant
(`d = [k(Γ) : k(C)]`, and `d = 0` if `f(Γ)` is a point). -/
private lemma exists_degreeOn_pullback_eq_mul [IsSeparated sX] [LocallyOfFiniteType sX]
    [QuasiCompact sX] [IsSeparated sZ] [LocallyOfFiniteType sZ] (f : X ⟶ Z) (hf : f ≫ sZ = sX)
    {C : Scheme.{u}} (i : C ⟶ Z) [IsClosedImmersion i] [IsIntegral C] [IsProper (i ≫ sZ)]
    (hC : topologicalKrullDim C = 1) (𝓛 : Z.Modules)
    [SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 𝓛]
    (Γ : ProperCurve sX) (hΓ : Set.range (Γ.ι ≫ f) ⊆ Set.range i) :
    ∃ d : ℕ, degreeOn k sX Γ.ι Γ.dim_le ((Scheme.Modules.pullback f).obj 𝓛) =
        d * degreeOn k sZ i hC.le 𝓛 ∧ ((¬ ∃ z : Z, ∀ x, (Γ.ι ≫ f) x = z) → 0 < d) := by
  classical
  have hΓc : AlgebraicGeometry.IsCurve k (Γ.ι ≫ sX) := isCurve_properCurve Γ
  have : IsIntegral Γ.scheme := hΓc.toIsIntegral
  have : AlgebraicGeometry.IsCurve k (i ≫ sZ) :=
    { toIsIntegral := inferInstance
      toIsSeparated := inferInstance
      toLocallyOfFiniteType := inferInstance
      toQuasiCompact := inferInstance
      topologicalKrullDim_eq_one := hC }
  have hH : i.ker ≤ (Γ.ι ≫ f).ker := by
    rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range i,
      Scheme.Hom.ker_eq_vanishingIdeal_closure_range (Γ.ι ≫ f)]
    refine Scheme.IdealSheafData.vanishingIdeal_antimono ?_
    exact closure_mono hΓ
  set g := IsClosedImmersion.lift i (Γ.ι ≫ f) hH
  have hg : g ≫ i = Γ.ι ≫ f := IsClosedImmersion.lift_fac _ _ _
  have hgs : g ≫ i ≫ sZ = Γ.ι ≫ sX := by
    rw [← Category.assoc, hg, Category.assoc, hf]
  have : AlgebraicGeometry.IsCurve k (g ≫ i ≫ sZ) := hgs ▸ hΓc
  have : IsProper (g ≫ i ≫ sZ) := hgs ▸ (inferInstance : IsProper (Γ.ι ≫ sX))
  have : IsProper ((Γ.ι ≫ f) ≫ sZ) := by rw [Category.assoc, hf]; infer_instance
  have key : degreeOn k sX Γ.ι Γ.dim_le ((Scheme.Modules.pullback f).obj 𝓛) =
      degreeOn k (i ≫ sZ) g Γ.dim_le ((Scheme.Modules.pullback i).obj 𝓛) := by
    let e : (Scheme.Modules.pullback (Γ.ι ≫ f)).obj 𝓛 ≅
        (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback i).obj 𝓛) :=
      (Scheme.Modules.pullbackCongr hg.symm).app 𝓛 ≪≫
        ((Scheme.Modules.pullbackComp g i).app 𝓛).symm
    rw [degreeOn_pullback_eq_degreeOn_comp sX sZ f Γ.ι hf, degreeOn, degreeOn,
      invertibleCurveDegree_eq_of_iso k _ _ e]
    exact invertibleCurveDegree_congr_structure (by rw [← Category.assoc g, hg, Category.assoc])
      _ _
  by_cases hnc : ∃ z : C, ∀ x, g x = z
  · refine ⟨0, ?_, fun hnc' => absurd ?_ hnc'⟩
    · rw [key, Nat.cast_zero, zero_mul]
      obtain ⟨z, hz⟩ := hnc
      exact degreeOn_eq_zero_of_range_eq_singleton (i ≫ sZ) g _
        ⟨z, Set.eq_singleton_iff_unique_mem.mpr
          ⟨⟨genericPoint Γ.scheme, hz _⟩, by rintro _ ⟨x, rfl⟩; exact hz x⟩⟩
    · obtain ⟨z, hz⟩ := hnc
      exact ⟨i z, fun x => by rw [← hg, Scheme.Hom.comp_apply, hz]⟩
  · refine ⟨@degreeOver _ _ g _ _
      (locallyOfFiniteType_of_isCurve_comp k (g ≫ i ≫ sZ) (i ≫ sZ) g rfl)
      (isDominant_of_not_constant k (g ≫ i ≫ sZ) (i ≫ sZ) g hnc), ?_,
      fun _ => degreeOver_pos_of_not_constant k (g ≫ i ≫ sZ) (i ≫ sZ) g rfl hnc⟩
    rw [key, degreeOn, degreeOn, invertibleCurveDegree_eq_curveDegree_one,
      invertibleCurveDegree_eq_curveDegree_one]
    exact curveDegree_pullback_eq_degreeOver_mul k (g ≫ i ≫ sZ) (i ≫ sZ) g rfl hnc
      ((Scheme.Modules.pullback i).obj 𝓛) 1

/-- **The intersection number with `L` from the descended bundle.** If `M = n L` is Cartier and
`𝒪_X(M) ≅ f^* 𝓛`, then `(L · Γ) = deg_Γ (f^* 𝓛) / n` along every curve `Γ` proper over `k`. -/
private lemma intersectionNumber_eq_degreeOn_pullback_div [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [QuasiCompact sX] {L : QDivisor X} (hL : L.IsQCartier) {n : ℕ} (hn : 0 < n)
    {M : Divisor X} (hMc : M.IsCartier) (hM : Divisor.toQDivisor M = (n : ℚ) • L) (f : X ⟶ Z)
    (𝓛 : Z.Modules) [SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 𝓛]
    (e : M.divisorialSheaf ≅ (Scheme.Modules.pullback f).obj 𝓛) {Γ : Scheme.{u}} (ι : Γ ⟶ X)
    [IsProper (ι ≫ sX)] (hdim : topologicalKrullDim Γ ≤ 1) :
    L.intersectionNumber k sX ι hdim hL =
      (degreeOn k sX ι hdim ((Scheme.Modules.pullback f).obj 𝓛) : ℚ) / n := by
  have := hMc.isInvertibleModule_divisorialSheaf
  rw [QDivisor.intersectionNumber_eq_of_smul k sX ι hdim L hL hn M hMc hM, Divisor.degreeOn,
    degreeOn, degreeOn, invertibleCurveDegree_eq_of_iso k _ _
      ((Scheme.Modules.pullback ι).mapIso e)]

end Degree

/-! ### Contractions are surjective -/

/-- A proper morphism `f : X ⟶ Y` of schemes with `𝒪_Y ⟶ f_* 𝒪_X` an isomorphism is surjective:
an open of `Y` missing `f(X)` has no sections upstairs. -/
private lemma surjective_of_isIso_app {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (hf : ∀ U : Y.Opens, IsIso (f.app U)) : Surjective f := by
  have hdom : IsDominant f := by
    refine ⟨dense_iff_inter_open.mpr fun V hV hVne => ?_⟩
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    let V' : Y.Opens := ⟨V, hV⟩
    have hbot : f ⁻¹ᵁ V' = ⊥ := by
      refine TopologicalSpace.Opens.ext ?_
      rw [TopologicalSpace.Opens.coe_bot, Set.eq_empty_iff_forall_notMem]
      intro y hy
      exact (Set.eq_empty_iff_forall_notMem.mp hempty) (f y) ⟨hy, y, rfl⟩
    have hsub : Subsingleton Γ(X, f ⁻¹ᵁ V') := by rw [hbot]; infer_instance
    have : Subsingleton Γ(Y, V') :=
      (ConcreteCategory.bijective_of_isIso (f.app V')).1.subsingleton
    obtain ⟨x, hx⟩ := hVne
    have h10 := congrArg (Y.presheaf.germ V' x hx).hom (Subsingleton.elim (1 : Γ(Y, V')) 0)
    rw [map_one, map_zero] at h10
    exact one_ne_zero h10
  have hrange : Set.range f = Set.univ := by
    rw [← (f.isClosedMap.isClosed_range).closure_eq, hdom.denseRange.closure_range]
  exact ⟨Set.range_eq_univ.mp hrange⟩

/-! ### The self-intersection of the descended bundle -/

/-- Intersection numbers depend on the structure morphism only through its value. -/
private lemma sheafIntersectionNumber_congr_structure {k : Type u} [Field k] {X Z : Scheme.{u}}
    {g g' : X ⟶ Spec (.of k)} (h : g = g') [IsProper g] [IsProper g'] (i : Z ⟶ X)
    [IsClosedImmersion i] (d : ℕ) (hd : topologicalKrullDim Z ≤ d) (L : Fin d → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)] :
    sheafIntersectionNumber k g i d hd L = sheafIntersectionNumber k g' i d hd L := by
  subst h
  rfl

/-- A divisor whose divisorial sheaf is isomorphic to an invertible sheaf is Cartier. -/
private lemma isCartier_of_divisorialSheaf_iso {X : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral X] [CompactSpace X] {D : Divisor X} (H : X.Modules)
    [Stacks.Ample.IsInvertibleModule X H] (e : D.divisorialSheaf ≅ H) : D.IsCartier := by
  intro x
  obtain ⟨U, hxU, ψ, hψ⟩ := MMP.Fourfold.exists_isLocalEquation_preimage_of_iso_pullback (𝟙 X) H
    (e ≪≫ ((Scheme.Modules.pullbackId X).app H).symm) x
  exact ⟨_, hxU, ψ, hψ⟩

/-- **`(𝓛²) > 0`** (FA 15.13). With `H` ample on `X`, `(L² · H) > 0` as `ν(L) ≥ 2`, and
`(f^*𝓛 · f^*𝓛 · H) = (𝓛²) · deg(H|_{X_η})` with `deg(H|_{X_η}) > 0` on the generic fibre. -/
private lemma sheafSelfIntersectionNumber_pos {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [hXP : Mori.IsProjectiveVariety k sX]
    [IsLocallyNoetherian X] [CompactSpace X] [IsNormal X] (hX3 : topologicalKrullDim X = 3)
    {L : QDivisor X} (hL : L.IsNef k sX) (hν : 2 ≤ numericalDimension k sX inferInstance L hL)
    {Zbar : Scheme.{u}} (sZbar : Zbar ⟶ Spec (.of k)) [Mori.IsProjectiveVariety k sZbar]
    [IsNormal Zbar] (hdim : topologicalKrullDim Zbar = 2) (f : X ⟶ Zbar) (hfs : f ≫ sZbar = sX)
    [Surjective f]
    (hfib : ∀ z : Zbar, ∀ Y ∈ irreducibleComponents (f.base ⁻¹' {z}), topologicalKrullDim Y = 1)
    (𝓛 : Zbar.Modules) [SheafOfModules.IsInvertible Zbar.presheaf Zbar.ringCatSheaf.2 𝓛]
    {n : ℕ} (hn : 0 < n) (M : Divisor X) (hMc : M.IsCartier)
    (hM : Divisor.toQDivisor M = (n : ℚ) • L)
    (e : M.divisorialSheaf ≅ (Scheme.Modules.pullback f).obj 𝓛) :
    0 < sheafSelfIntersectionNumber k sZbar (𝟙 Zbar) 2 hdim.le 𝓛 := by
  classical
  have : IsIntegral X := hXP.toIsIntegral
  have : IsIntegral Zbar := (inferInstance : Mori.IsProjectiveVariety k sZbar).toIsIntegral
  have : IsProper sX := ((isProjectiveVariety_iff_isProjective' k sX).1 inferInstance).2.isProper
  have : IsProper (f ≫ sZbar) := by rw [hfs]; infer_instance
  have : IsProper f := IsProper.of_comp f sZbar
  -- an ample Cartier divisor `F` on `X`
  obtain ⟨H, hHinv, hHa⟩ := AlgebraicGeometry.exists_isAmple_of_isProjectiveMorphism sX
    (Stacks.Ample.unitModule (Spec (.of k))) (Stacks.Ample.isAmple_unitModule_of_isAffine _)
    hXP.isProjective
  obtain ⟨F, ⟨eF⟩⟩ := MMP.Mori.exists_divisorialSheaf_iso_of_isInvertible H
  have hFc : F.IsCartier := isCartier_of_divisorialSheaf_iso H eF
  have := hFc.isInvertibleModule_divisorialSheaf
  have := hMc.isInvertibleModule_divisorialSheaf
  have hFa : Stacks.Ample.IsAmple X F.divisorialSheaf :=
    (Stacks.RelativeVeryAmple.isAmple_congr _ _ eF).mpr hHa
  have hHq : (Divisor.toQDivisor F).IsAmple := ⟨1, one_pos, F, by simp, hFc, hFa⟩
  have hpos := MMP.Flips.intersectionNumberOn_pos_of_two_le_numericalDimension sX hX3 hL hν hHq
    hn one_pos M F hMc hFc hM (by simp)
  -- the pull-back formula
  have : Mori.IsProjectiveVariety k (f ≫ sZbar) := hfs ▸ hXP
  have hfib' : ∀ s : Zbar, topologicalKrullDim (f.fiber s) = 1 := by
    intro s
    rw [IsHomeomorph.topologicalKrullDim_eq _ (f.fiberHomeo s).isHomeomorph]
    obtain ⟨x, hx⟩ := f.surjective s
    have : Nonempty (f.base ⁻¹' {s}) := ⟨⟨x, hx⟩⟩
    exact topologicalKrullDim_eq_one_of_forall_mem_irreducibleComponents (hfib s)
  have hform := MMP.Flips.sheafIntersectionNumber_pullback_pullback_eq_mul_invertibleCurveDegree
    sZbar f hX3 hdim f.surjective hfib' 𝓛 𝓛 F.divisorialSheaf
  -- the degree on the generic fibre is positive
  have : IsProper (f.fiberToSpecResidueField (genericPoint Zbar)) :=
    AlgebraicGeometry.isProper_fiberToSpecResidueField f (genericPoint Zbar)
  have : IsAffineHom (f.fiberι (genericPoint Zbar)) := by
    have : IsAffineHom (Zbar.fromSpecResidueField (genericPoint Zbar)) :=
      IsAffineHom.of_comp _ sZbar
    exact isAffineHom_isStableUnderBaseChange.of_isPullback
      (CategoryTheory.IsPullback.of_hasPullback f
        (Zbar.fromSpecResidueField (genericPoint Zbar))).flip this
  have hdeg := invertibleCurveDegree_pullback_pos_of_isAmple_of_isAffineHom
    (Zbar.residueField (genericPoint Zbar)) (f.fiberToSpecResidueField (genericPoint Zbar))
    (hfib' _) (f.fiberι (genericPoint Zbar)) F.divisorialSheaf
    ((Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple _ _).mpr hFa)
  -- comparing the intersection numbers on `X`
  have h3 : ∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (![(Scheme.Modules.pullback f).obj 𝓛, (Scheme.Modules.pullback f).obj 𝓛,
        F.divisorialSheaf] j) := by
    intro j; fin_cases j <;> dsimp <;> infer_instance
  have hcmp : Divisor.intersectionNumberOn k sX (𝟙 X) 3 hX3.le ![M, M, F]
      (by intro j; fin_cases j <;> assumption) =
      sheafIntersectionNumber k (f ≫ sZbar) (𝟙 X) 3 hX3.le
        ![(Scheme.Modules.pullback f).obj 𝓛, (Scheme.Modules.pullback f).obj 𝓛,
          F.divisorialSheaf] := by
    have e' : ∀ t, Nonempty ((![M, M, F] t).divisorialSheaf ≅
        ![(Scheme.Modules.pullback f).obj 𝓛, (Scheme.Modules.pullback f).obj 𝓛,
          F.divisorialSheaf] t) := by
      intro t; fin_cases t
      exacts [⟨e⟩, ⟨e⟩, ⟨Iso.refl _⟩]
    have hMMF : ∀ t, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
        ((![M, M, F] t).divisorialSheaf) := by
      intro t; fin_cases t <;> dsimp <;> infer_instance
    have hdef : Divisor.intersectionNumberOn k sX (𝟙 X) 3 hX3.le ![M, M, F]
        (by intro j; fin_cases j <;> assumption) =
        sheafIntersectionNumber k sX (𝟙 X) 3 hX3.le fun j => (![M, M, F] j).divisorialSheaf :=
      rfl
    rw [hdef,
      sheafIntersectionNumber_congr_hom k sX (i := 𝟙 X) (i' := 𝟙 X ≫ 𝟙 X)
        (Category.id_comp _).symm,
      sheafIntersectionNumber_comp_eq_of_iso k sX (𝟙 X) (𝟙 X) 3 hX3.le
        (fun j => (![M, M, F] j).divisorialSheaf)
        ![(Scheme.Modules.pullback f).obj 𝓛, (Scheme.Modules.pullback f).obj 𝓛,
          F.divisorialSheaf] (fun t => (Scheme.Modules.pullbackId X).app _ ≪≫ (e' t).some)]
    exact sheafIntersectionNumber_congr_structure (by rw [Category.id_comp, hfs]) _ _ _ _
  rw [hcmp, hform] at hpos
  have h2 : ∀ j, SheafOfModules.IsInvertible Zbar.presheaf Zbar.ringCatSheaf.2 (![𝓛, 𝓛] j) := by
    intro j; fin_cases j <;> dsimp <;> infer_instance
  have hss : sheafSelfIntersectionNumber k sZbar (𝟙 Zbar) 2 hdim.le 𝓛 =
      sheafIntersectionNumber k sZbar (𝟙 Zbar) 2 hdim.le ![𝓛, 𝓛] := by
    unfold sheafSelfIntersectionNumber
    congr 1
    funext j
    fin_cases j <;> rfl
  rw [hss]
  by_contra hle
  push Not at hle
  nlinarith

/-! ### Positivity on curves -/

section Points

variable {X : Scheme.{u}} [IsIntegral X]

/-- In an irreducible scheme of dimension three, a point of height two has coheight one: its
closure is a prime divisor. -/
private lemma coheight_eq_one_of_height_eq_two (hX : topologicalKrullDim X = 3) {y : X}
    (hy : Order.height y = 2) : Order.coheight y = 1 := by
  have hlt : y < genericPoint X := by
    refine lt_of_specializes_of_ne ((genericPoint_spec X).specializes (Set.mem_univ y)) ?_
    intro he
    have := height_genericPoint (X := X)
    rw [he, hy, hX] at this
    exact absurd this (by decide)
  refine le_antisymm ?_ ?_
  · rw [show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) from rfl, Order.coheight_le_coe_iff]
    intro b hb
    rw [Order.coheight_eq_zero.mpr fun c hbc => ?_]
    · exact zero_lt_one
    by_contra hcb
    have h3 : Order.height c ≤ 3 := by
      have := height_le_topologicalKrullDim c
      rw [hX] at this
      exact WithBot.coe_le_coe.mp this
    have h4 := ((add_le_add_left (Order.height_add_one_le hb) 1).trans
      (Order.height_add_one_le (lt_of_le_not_ge hbc hcb))).trans h3
    rw [hy] at h4
    exact absurd h4 (by decide)
  · rw [Order.one_le_iff_pos, pos_iff_ne_zero]
    intro h0
    exact (not_le_of_gt hlt) (Order.coheight_eq_zero.mp h0 hlt.le)

/-- **A surface over a curve.** Let `f : X ⟶ Z` be a closed surjection from an integral
threefold onto an integral surface whose fibres have pure dimension one, and `z ∈ Z` a point of
height one. Then there are points `y₀ ⤳ y₁` over `z` with `height y₁ = 1` and `height y₀ = 2`:
the generic points of a one-dimensional component of `f⁻¹(z)` and of a curve in it. -/
private lemma exists_specializes_height_two_height_one {Z : Scheme.{u}} [IsIntegral Z]
    (f : X ⟶ Z) [UniversallyClosed f] [Surjective f] (hX : topologicalKrullDim X = 3)
    (hZ : topologicalKrullDim Z = 2)
    (hfib : ∀ z : Z, ∀ Y ∈ irreducibleComponents (f.base ⁻¹' {z}), topologicalKrullDim Y = 1)
    {z : Z} (hz : Order.height z = 1) :
    ∃ y₀ y₁ : X, y₀ ⤳ y₁ ∧ f y₀ = z ∧ f y₁ = z ∧ Order.height y₁ = 1 ∧
      Order.height y₀ = 2 := by
  obtain ⟨x, hx⟩ := f.surjective z
  obtain ⟨y₀, y₁, hsp, hne, hf₀, hf₁⟩ := exists_specializes_ne_of_fiber f hx (hfib z)
  refine ⟨y₀, y₁, hsp, hf₀, hf₁, ENat.eq_one_and_eq_two ?_
    (Order.height_add_one_le (lt_of_specializes_of_ne hsp hne)) ?_⟩
  · rw [Order.one_le_iff_pos, pos_iff_ne_zero]
    intro h0
    have hc := f.isClosedMap _ (isClosed_singleton_of_height_eq_zero h0)
    rw [Set.image_singleton, hf₁] at hc
    rw [Scheme.height_of_isClosed hc] at hz
    exact absurd hz (by decide)
  · have hη : Order.height (genericPoint X) = 3 := by
      have := height_genericPoint (X := X)
      rw [hX] at this
      exact WithBot.coe_injective this
    refine hη ▸ Order.height_add_one_le (lt_of_specializes_of_ne
      ((genericPoint_spec X).specializes (Set.mem_univ y₀)) fun hy => ?_)
    have hηZ := height_genericPoint (X := Z)
    rw [← genericPoint_eq_of_isDominant f, hy, hf₀, hz, hZ] at hηZ
    exact absurd hηZ (by decide)

end Points

/-- The support of `Finsupp.single E 1` is `E`. -/
private lemma coe_supp_single_one {X : Scheme.{u}} (E : Mori.PrimeDivisor X) :
    ((DivisorWithCoeffs.supp (Finsupp.single E 1 : Divisor X)) : Set X) = E.support := by
  refine Set.Subset.antisymm (DivisorWithCoeffs.supp_single_le E 1) ?_
  exact DivisorWithCoeffs.support_subset_supp (by simp [DivisorWithCoeffs.coeff_single_self])

/-- **`𝓛` is positive on curves** (FA 15.13). Let `f : X ⟶ Z̄` be surjective with fibres of pure
dimension one, `𝒪_X(n(K_X + Δ_X)) ≅ f^* 𝓛`, and `C ⊆ Z̄` an integral curve. A curve `Γ ⊆ X` over
`C` gives `0 ≤ n (L · Γ) = deg(Γ/C) (𝓛 · C)`, so `𝓛 · C ≥ 0`. If `𝓛 · C = 0`, every curve in a
surface `S ⊆ f⁻¹(C)` over `C` is `L`-trivial and any two points of `S` are joined by such curves,
so the prime divisor `S` is `L`-trivially connected, which is excluded. -/
private lemma degreeOn_pos {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    [QuasiCompact sX] {K : Divisor X} {Δ : QDivisor X} (h : SatisfiesAbundanceAssumptions k sX K Δ)
    (hD : ∀ D : Mori.PrimeDivisor X, ¬ IsTriviallyConnected k sX 3 K Δ (Finsupp.single D 1))
    {Zbar : Scheme.{u}} (sZbar : Zbar ⟶ Spec (.of k)) [IsIntegral Zbar] [IsSeparated sZbar]
    [LocallyOfFiniteType sZbar] [IsProper sZbar] (hdim : topologicalKrullDim Zbar = 2)
    (f : X ⟶ Zbar)
    (hfs : f ≫ sZbar = sX) [IsProper f] [Surjective f]
    (hfib : ∀ z : Zbar, ∀ Y ∈ irreducibleComponents (f.base ⁻¹' {z}), topologicalKrullDim Y = 1)
    (𝓛 : Zbar.Modules) [SheafOfModules.IsInvertible Zbar.presheaf Zbar.ringCatSheaf.2 𝓛]
    {n : ℕ} (hn : 0 < n) (M : Divisor X) (hMc : M.IsCartier)
    (hM : Divisor.toQDivisor M = (n : ℚ) • (Divisor.toQDivisor K + Δ))
    (e : M.divisorialSheaf ≅ (Scheme.Modules.pullback f).obj 𝓛)
    (C : Scheme.{u}) (i : C ⟶ Zbar) [IsClosedImmersion i] [IsIntegral C] [IsProper (i ≫ sZbar)]
    (hC : topologicalKrullDim C = 1) : 0 < degreeOn k sZbar i hC.le 𝓛 := by
  classical
  have hXP : Mori.IsProjectiveVariety k sX := h.isProjectiveVariety
  have : IsSeparated sX := hXP.toIsSeparated
  have : IsProper sX := hfs ▸ (inferInstance : IsProper (f ≫ sZbar))
  have hLq := h.isQCartier
  have hint := fun (Γ : ProperCurve sX) =>
    intersectionNumber_eq_degreeOn_pullback_div (k := k) (sX := sX) hLq hn hMc hM f 𝓛 e Γ.ι
      Γ.dim_le
  -- the generic point of `C`
  set ηC := i (genericPoint C)
  have hclC : closure ({ηC} : Set Zbar) = Set.range i := by
    rw [← Set.image_singleton, i.isClosedEmbedding.closure_image_eq, (genericPoint_spec C).def,
      Set.image_univ]
  have hηC : Order.height ηC = 1 := by
    have := topologicalKrullDim_closure_singleton_eq_height ηC
    rw [hclC, topologicalKrullDim_range_eq, hC] at this
    exact (WithBot.coe_injective this).symm
  -- a surface `{y₀}⁻` over `C` containing a curve `{y₁}⁻` over `C`
  obtain ⟨y₀, y₁, hsp, hf₀, hf₁, hy₁, hy₀⟩ :=
    exists_specializes_height_two_height_one f h.dim_eq hdim hfib hηC
  have hfcl : IsClosedMap f := f.isClosedMap
  -- curves over `C`
  have hrange : ∀ Γ : ProperCurve sX, closure {Γ.point} ⊆ closure ({y₀} : Set X) →
      Set.range (Γ.ι ≫ f) ⊆ Set.range i := by
    intro Γ hΓ
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Hom.comp_apply, ← hclC, ← hf₀]
    have hx : Γ.ι x ∈ closure ({y₀} : Set X) := hΓ (by
      rw [← MMP.Mori.range_curveSubschemeAtι]; exact ⟨x, rfl⟩)
    exact specializes_iff_mem_closure.mp
      ((specializes_iff_mem_closure.mpr hx).map f.base.hom.continuous)
  -- `𝓛 · C ≥ 0`
  set Γ₁ := properCurveOfHeight sX y₁ hy₁
  have hΓ₁ : closure {Γ₁.point} ⊆ closure ({y₀} : Set X) :=
    closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hsp))
      isClosed_closure
  obtain ⟨d, hd, hdpos⟩ := exists_degreeOn_pullback_eq_mul f hfs i hC 𝓛 Γ₁ (hrange Γ₁ hΓ₁)
  have hdpos : 0 < d := hdpos (by
    rintro ⟨z, hz⟩
    -- the image of `Γ₁` is closed and contains `ηC`, hence all of `C`
    have himg : f '' closure {y₁} = Set.range (Γ₁.ι ≫ f) := by
      rw [← MMP.Mori.range_curveSubschemeAtι y₁, ← Set.range_comp]; rfl
    have hcl : closure ({ηC} : Set Zbar) ⊆ f '' closure {y₁} := by
      refine closure_minimal ?_ (hfcl _ isClosed_closure)
      rw [Set.singleton_subset_iff, ← hf₁]
      exact ⟨y₁, subset_closure rfl, rfl⟩
    have hsub : closure ({ηC} : Set Zbar) ⊆ {z} := by
      rw [himg] at hcl
      refine hcl.trans ?_
      rintro _ ⟨x, rfl⟩
      exact hz x
    have hcz : closure ({ηC} : Set Zbar) = {ηC} :=
      Set.Subset.antisymm (fun w hw => (hsub hw).trans (hsub (subset_closure rfl)).symm)
        subset_closure
    rw [Scheme.height_of_isClosed (closure_eq_iff_isClosed.mp hcz)] at hηC
    exact absurd hηC (by decide))
  have hnef : 0 ≤ (Divisor.toQDivisor K + Δ).intersectionNumber k sX Γ₁.ι Γ₁.dim_le hLq := by
    obtain ⟨hq, hq'⟩ := h.isNef
    have : IsIntegral Γ₁.scheme := (isCurve_properCurve Γ₁).toIsIntegral
    exact hq' Γ₁.scheme Γ₁.ι Γ₁.dim_eq
  rw [hint Γ₁, hd] at hnef
  have hC0 : 0 ≤ degreeOn k sZbar i hC.le 𝓛 := by
    have h1 : (0 : ℚ) ≤ d * degreeOn k sZbar i hC.le 𝓛 := by
      simpa [div_nonneg_iff, hn.ne'] using hnef
    exact_mod_cast nonneg_of_mul_nonneg_right h1 (by exact_mod_cast hdpos)
  refine lt_of_le_of_ne hC0 fun hzero => ?_
  -- `𝓛 · C = 0`: the surface `S = {y₀}⁻` is `L`-trivially connected
  set P : Mori.PrimeDivisor X := AlgebraicGeometry.PrimeDivisor.ofCoheightOne y₀
    (coheight_eq_one_of_height_eq_two h.dim_eq hy₀)
  have hPsupp : (P.support : Set X) = closure {y₀} := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
  obtain ⟨H, hHinv, hHa⟩ := AlgebraicGeometry.exists_isAmple_of_isProjectiveMorphism sX
    (Stacks.Ample.unitModule (Spec (.of k))) (Stacks.Ample.isAmple_unitModule_of_isAffine _)
    hXP.isProjective
  refine hD P ⟨h.isQFactorial.1, inferInstance, h.isKawamataLogTerminal.2.1, hLq,
    fun E => ?_, ?_⟩
  · rw [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply]
    split_ifs <;> norm_num
  · rw [coe_supp_single_one, hPsupp]
    intro x₁ hx₁ x₂ hx₂ hc₁ hc₂
    obtain ⟨S, hS, hSy, h₁, h₂⟩ :=
      exists_isConnected_curveUnion_of_height_eq_two sX H hHa hy₀ hx₁ hx₂ hc₁ hc₂
    refine ⟨S, hS, hSy, h₁, h₂, fun Γ hΓ => ?_⟩
    have hΓy : closure {Γ.point} ⊆ closure ({y₀} : Set X) :=
      (Set.subset_biUnion_of_mem (u := fun C : ProperCurve sX => closure {C.point}) hΓ).trans hSy
    obtain ⟨d', hd', -⟩ := exists_degreeOn_pullback_eq_mul f hfs i hC 𝓛 Γ (hrange Γ hΓy)
    rw [hint Γ, hd', hzero.symm, mul_zero, Int.cast_zero, zero_div]

/-- **The descended line bundle is ample** (FA 15.13). Let `(X, Δ_X)`, with `K_X` a canonical
divisor, satisfy the assumptions of 15.4 (`MMP.Flips.SatisfiesAbundanceAssumptions`) over an
algebraically closed field `k` of characteristic zero, with no `(K_X + Δ_X)`-trivially connected
prime divisor (`MMP.Flips.IsTriviallyConnected`) and `ν(X, K_X + Δ_X) ≥ 2`
(`MMP.Flips.numericalDimension`). Let `f_U : U ⟶ Z` be the log elliptic fiber space of (15.4.3),
and `f : X ⟶ Z̄` a morphism to a normal projective surface `Z̄` over `k` with `f_* 𝒪_X = 𝒪_{Z̄}`
(`MMP.Flips.IsContraction`), all of whose fibres are connected of pure dimension one, such that
`f = f_U` on `f_U⁻¹(Z₀)` for a nonempty open `Z₀ ⊆ Z` with an open immersion `j : Z₀ ⟶ Z̄` over
`k`. If `𝓛` is a line bundle on `Z̄` and `𝒪_X(M) ≅ f^* 𝓛` for the divisor `M = n(K_X + Δ_X)`,
`n > 0`, then `𝓛` is ample. -/
@[mmp "lem_fa15_descended_line_bundle_ample"]
public theorem isAmple_of_divisorialSheaf_iso_pullback
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [LocallyOfFiniteType sX] [QuasiCompact sX] {K : Divisor X} {Δ : QDivisor X}
    (h : SatisfiesAbundanceAssumptions k sX K Δ)
    (hD : ∀ D : Mori.PrimeDivisor X, ¬ IsTriviallyConnected k sX 3 K Δ (Finsupp.single D 1))
    (hν : haveI := h.isProjectiveVariety
      2 ≤ numericalDimension k sX inferInstance (Divisor.toQDivisor K + Δ) h.isNef)
    (U : X.Opens) (hU : (U : Set X).Nonempty) {Z : Scheme.{u}} (sZ : Z ⟶ Spec (.of k))
    (fU : U.toScheme ⟶ Z)
    (hfU : IsLogEllipticFiberSpace k (U.ι ≫ sX) sZ 3 (DivisorWithCoeffs.restrict U.ι K)
      (DivisorWithCoeffs.restrict U.ι Δ) fU)
    {Zbar : Scheme.{u}} (sZbar : Zbar ⟶ Spec (.of k)) (Z₀ : Z.Opens) (j : Z₀.toScheme ⟶ Zbar)
    (f : X ⟶ Zbar) (hZbar : IsNormalVariety k sZbar) (hZbarP : Mori.IsProjectiveVariety k sZbar)
    (hdim : topologicalKrullDim Zbar = 2) (hZ₀ : (Z₀ : Set Z).Nonempty) [IsOpenImmersion j]
    (hj : j ≫ sZbar = Z₀.ι ≫ sZ) (hf : IsContraction k sZbar sX f)
    (hconn : ∀ z : Zbar, _root_.IsConnected (f.base ⁻¹' {z}))
    (hfib : ∀ z : Zbar, ∀ Y ∈ irreducibleComponents (f.base ⁻¹' {z}), topologicalKrullDim Y = 1)
    (hfU_eq : (fU ⁻¹ᵁ Z₀).ι ≫ U.ι ≫ f = (fU ∣_ Z₀) ≫ j)
    (𝓛 : Zbar.Modules) [SheafOfModules.IsInvertible Zbar.presheaf Zbar.ringCatSheaf.2 𝓛]
    {n : ℕ} (hn : 0 < n) (M : Divisor X)
    (hM : Divisor.toQDivisor M = (n : ℤ) • (Divisor.toQDivisor K + Δ))
    (e : M.divisorialSheaf ≅ (Scheme.Modules.pullback f).obj 𝓛) :
    Stacks.Ample.IsAmple Zbar 𝓛 := by
  have hXP : Mori.IsProjectiveVariety k sX := h.isProjectiveVariety
  have : Mori.IsProjectiveVariety k sZbar := hZbarP
  have : IsProper sZbar :=
    ((isProjectiveVariety_iff_isProjective' k sZbar).1 inferInstance).2.isProper
  have : IsIntegral Zbar := hZbarP.toIsIntegral
  have : IsSeparated sZbar := hZbarP.toIsSeparated
  have : LocallyOfFiniteType sZbar := hZbarP.toLocallyOfFiniteType
  have : IsNormal Zbar := hZbar.2
  have : IsProper f := hf.isProper
  have hfs : f ≫ sZbar = sX := hf.comp_eq
  have : Surjective f := surjective_of_isIso_app f hf.isIso_app
  have hMc : M.IsCartier := fun x => by
    obtain ⟨V, hxV, ψ, hψ⟩ :=
      MMP.Fourfold.exists_isLocalEquation_preimage_of_iso_pullback f 𝓛 e (f x)
    exact ⟨f ⁻¹ᵁ V, hxV, ψ, hψ⟩
  have hM' : Divisor.toQDivisor M = (n : ℚ) • (Divisor.toQDivisor K + Δ) := by
    rw [hM, ← Int.cast_smul_eq_zsmul ℚ, Int.cast_natCast]
  refine isAmple_of_sheafSelfIntersectionNumber_pos_of_degreeOn_pos sZbar hdim 𝓛 ?_ ?_
  · exact sheafSelfIntersectionNumber_pos sX h.dim_eq h.isNef hν sZbar hdim f hfs hfib 𝓛 hn M
      hMc hM' e
  · intro C i _ _ _ hC
    exact degreeOn_pos sX h hD sZbar hdim f hfs hfib 𝓛 hn M hMc hM' e C i hC

/-! ## The trivially connected dichotomy (FA 15.7) -/

/-! ### Linear systems on a curve -/

section Curve

open Stacks.ProjectiveFromSections Stacks.ProjectiveSpaceModuli

/-- Dimension of the closure of the range of a map. -/
private noncomputable def rdim {A B : Type*} [TopologicalSpace B] (f : A → B) : WithBot ℕ∞ :=
  topologicalKrullDim (closure (Set.range f))

private theorem rdim_comp_surjective {A A' B : Type*} [TopologicalSpace B] (f : A → B)
    {h : A' → A} (hh : Function.Surjective h) : rdim (f ∘ h) = rdim f := by
  unfold rdim
  rw [hh.range_comp]

private theorem rdim_homeomorph_comp {A B C : Type*} [TopologicalSpace B] [TopologicalSpace C]
    (f : A → B) (e : B ≃ₜ C) : rdim (e ∘ f) = rdim f := by
  unfold rdim
  rw [Set.range_comp, ← e.image_closure]
  exact ((e.image _).isHomeomorph.topologicalKrullDim_eq).symm

/-- The global sections of an invertible sheaf on a proper `k`-scheme are finite-dimensional. -/
private theorem finiteDimensional_globalSections (k : Type v) [Field k] {X : Scheme.{v}}
    (sX : X ⟶ Spec (.of k)) [IsProper sX] [IsLocallyNoetherian X] (F : X.Modules)
    [Stacks.Ample.IsInvertibleModule X F] :
    letI : X.Over (Spec (.of k)) := ⟨sX⟩
    letI := Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.globalSectionsModule k X F
    FiniteDimensional k Γ(F, ⊤) := by
  letI : X.Over (Spec (.of k)) := ⟨sX⟩
  have hinv : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 F :=
    ‹Stacks.Ample.IsInvertibleModule X F›
  have : F.IsCoherent := Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible X F
  have := finiteDimensional_cohomologyOverField_of_isProper k sX F 0
  have e := (cohomologyOverFieldZeroLinearIso k sX F).toLinearEquiv
  have hEq : sX.appLE ⊤ ⊤ (by simp) = sX.appTop := by
    simp only [Scheme.Hom.appLE, TopologicalSpace.Opens.map_top, homOfLE_refl, op_id,
      CategoryTheory.Functor.map_id]
    exact Category.comp_id _
  have key : ∀ φ : k →+* Γ(X, ⊤),
      φ = ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appLE ⊤ ⊤ (by simp)).hom →
        (letI := Module.compHom Γ(F, ⊤) φ; FiniteDimensional k Γ(F, ⊤)) := by
    rintro φ rfl
    -- elaborated before the goal's `letI` instance is in scope
    have h := Module.Finite.equiv e
    exact h
  refine key _ ?_
  change ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ sX.appTop).hom = _
  rw [hEq]

attribute [local instance]
  Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.globalSectionsModule

private theorem topologicalKrullDim_linearSystemImage (k : Type v) [Field k] {X : Scheme.{v}}
    [X.Over (Spec (.of k))] (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] {ι : Type v}
    (b : Module.Basis ι k Γ(L, ⊤)) :
    topologicalKrullDim (linearSystemImage k L b) = rdim (linearSystemMap k L b).base := by
  have hemb := (linearSystemImageIdeal k L b).subschemeι.isClosedEmbedding.isEmbedding
  rw [hemb.toHomeomorph.isHomeomorph.topologicalKrullDim_eq, rdim]
  have : Set.range (linearSystemImageIdeal k L b).subschemeι.base =
      closure (Set.range (linearSystemMap k L b).base) := by
    rw [Scheme.IdealSheafData.range_subschemeι, linearSystemImageIdeal,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  rw [this]

open Stacks.AlgebraicGeometry.ProjectiveSpaceCoordinateSquare in
private theorem linearSystemMap_comp_basisIso (k : Type v) [Field k] {X : Scheme.{v}}
    [X.Over (Spec (.of k))] (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] {ι : Type v}
    (b : Module.Basis ι k Γ(L, ⊤)) {n : ℕ} (e : Fin (n + 1) ≃ ι)
    (hgen : GeneratesStalks (fun i => b (e i))) :
    linearSystemMap k L b ≫
        (AlgebraicGeometry.basisProjectiveSpaceOfModuleIso
          ((Finsupp.basisSingleOne (R := k) (ι := ι)).reindex e.symm)).hom.left =
      (linearSystemLocus k L b).ι ≫
        toProjectiveSpaceOver (fun i => b (e i)) hgen (X ↘ Spec (.of k)) := by
  rw [linearSystemMap, morphismOfGeneratingSections_comp_basisProjectiveSpaceOfModuleIso]
  refine CategoryTheory.Limits.pullback.hom_ext ?_ ?_
  · rw [toProjectiveSpaceOver_fst, Category.assoc, toProjectiveSpaceOver_fst]
    rfl
  · rw [toProjectiveSpaceOver_snd, Category.assoc, toProjectiveSpaceOver_snd,
      comp_toProjectiveSpaceAtUniverse _ _ _
        (pullbackTuple (linearSystemLocus k L b).ι ⟨L, ‹_›, _, hgen⟩).generates]
    congr 1
    funext i
    simp [Stacks.AlgebraicGeometry.ProjectiveSpaceCoordinateSquare.basisSections,
      linearSystemRestrict]
    rfl

private theorem topologicalKrullDim_linearSystemImage_eq (k : Type v) [Field k] {X : Scheme.{v}}
    [X.Over (Spec (.of k))] (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] {ι : Type v}
    (b : Module.Basis ι k Γ(L, ⊤)) {n : ℕ} (e : Fin (n + 1) ≃ ι)
    (hgen : GeneratesStalks (fun i => b (e i))) (htop : linearSystemLocus k L b = ⊤) :
    topologicalKrullDim (linearSystemImage k L b) =
      rdim (toProjectiveSpaceOver (fun i => b (e i)) hgen (X ↘ Spec (.of k))).base := by
  rw [topologicalKrullDim_linearSystemImage]
  let E := (Over.forget _).mapIso (AlgebraicGeometry.basisProjectiveSpaceOfModuleIso
    ((Finsupp.basisSingleOne (R := k) (ι := ι)).reindex e.symm))
  refine (rdim_homeomorph_comp _ (Scheme.homeoOfIso E)).symm.trans ?_
  have h1 : ⇑(Scheme.homeoOfIso E) ∘ ⇑(linearSystemMap k L b).base =
      ⇑(linearSystemMap k L b ≫ E.hom).base := rfl
  have hE : E.hom = (AlgebraicGeometry.basisProjectiveSpaceOfModuleIso
    ((Finsupp.basisSingleOne (R := k) (ι := ι)).reindex e.symm)).hom.left := rfl
  rw [h1, hE, linearSystemMap_comp_basisIso k L b e hgen]
  refine rdim_comp_surjective
    (⇑(toProjectiveSpaceOver (fun i => b (e i)) hgen (X ↘ Spec (.of k))).base)
    (h := ⇑(linearSystemLocus k L b).ι.base) ?_
  rw [← Set.range_eq_univ, Scheme.Opens.range_ι, htop]
  rfl

private theorem generatesStalks_of_linearSystemLocus_eq_top (k : Type v) [Field k]
    {X : Scheme.{v}} [X.Over (Spec (.of k))] (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] {ι : Type v} (b : Module.Basis ι k Γ(L, ⊤)) {n : ℕ}
    (e : Fin (n + 1) ≃ ι) (htop : linearSystemLocus k L b = ⊤) :
    GeneratesStalks (fun i => b (e i)) :=
  Stacks.AmpleImmersionReduction.generatesStalks_of_forall_exists_mem _ fun x => by
    obtain ⟨j, hj⟩ := (mem_linearSystemLocus_iff k L b x).1 (htop ▸ trivial)
    exact ⟨e.symm j, show x ∈ Stacks.NonvanishingOpen.nonvanishingOpen X L (b (e (e.symm j))) by
      rwa [Equiv.apply_symm_apply]⟩

/-- A basis of the sections of an invertible sheaf on a nonempty scheme with `U = X` is indexed by
a type equivalent to some `Fin (n + 1)`, when the sections are finite-dimensional. -/
private theorem exists_equiv_fin_of_linearSystemLocus_eq_top (k : Type v) [Field k]
    {X : Scheme.{v}} [Nonempty X] [X.Over (Spec (.of k))] (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] {ι : Type v} (b : Module.Basis ι k Γ(L, ⊤))
    [FiniteDimensional k Γ(L, ⊤)] (htop : linearSystemLocus k L b = ⊤) :
    ∃ n : ℕ, Nonempty (Fin (n + 1) ≃ ι) := by
  have : Finite ι := Module.Finite.finite_basis b
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨j, -⟩ := (mem_linearSystemLocus_iff k L b x).1 (htop ▸ trivial)
  cases m with
  | zero => exact (e j).elim0
  | succ n => exact ⟨n, ⟨e.symm⟩⟩

/-- The range of a closed map has dimension at most that of its source. -/
private theorem topologicalKrullDim_range_le_of_isClosedMap {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] [QuasiSober B] [T0Space B] (f : A → B) (hf : Continuous f)
    (hc : IsClosedMap f) :
    topologicalKrullDim (Set.range f) ≤ topologicalKrullDim A := by
  have : QuasiSober (Set.range f) := hc.isClosed_range.isClosedEmbedding_subtypeVal.quasiSober
  refine Topology.topologicalKrullDim_le_of_surjective_of_specializingMap_or_generalizingMap
    (Set.rangeFactorization f) (hf.subtype_mk _) Set.rangeFactorization_surjective (Or.inl ?_)
  intro a y hy
  have hy' : f a ⤳ y.1 := hy.map continuous_subtype_val
  obtain ⟨a', ha', hfa'⟩ := hc.specializingMap hy'
  exact ⟨a', ha', Subtype.ext hfa'⟩

/-- An irreducible sober space of dimension at most zero is a point. -/
private theorem subsingleton_of_topologicalKrullDim_le_zero {S : Type*} [TopologicalSpace S]
    [IrreducibleSpace S] [QuasiSober S] [T0Space S] (h : topologicalKrullDim S ≤ 0) :
    Subsingleton S := by
  have key : ∀ p : S, closure {p} = Set.univ := by
    intro p
    by_contra hne
    let Zp : TopologicalSpace.IrreducibleCloseds S :=
      ⟨closure {p}, isIrreducible_singleton.closure, isClosed_closure⟩
    let Zt : TopologicalSpace.IrreducibleCloseds S :=
      ⟨Set.univ, IrreducibleSpace.isIrreducible_univ S, isClosed_univ⟩
    have hlt : Zp < Zt := by
      refine lt_of_le_of_ne (fun x _ => Set.mem_univ x) fun heq => hne ?_
      exact congrArg (fun Z : TopologicalSpace.IrreducibleCloseds S => (Z : Set S)) heq
    exact (Order.krullDim_nonpos_iff_forall_isMax.mp h Zp).not_lt hlt
  exact ⟨fun p q => IsGenericPoint.eq (key p) (key q)⟩

private theorem eq_one_of_le_one_of_not_le_zero {d : WithBot ℕ∞} (h1 : d ≤ 1) (h0 : ¬ d ≤ 0) :
    d = 1 := by
  induction d using WithBot.recBotCoe with
  | bot => exact absurd bot_le h0
  | coe e =>
    induction e using ENat.recTopCoe with
    | top => exact absurd h1 (by decide)
    | coe m =>
      obtain rfl : m = 1 := by
        have : m ≤ 1 := by exact_mod_cast h1
        have : ¬ m ≤ 0 := fun h => h0 (by exact_mod_cast h)
        omega
      rfl

/-- If the image of `φ_s` is a point, some `sⱼ` vanishes nowhere. -/
private theorem exists_forall_mem_nonvanishingLocus_of_subsingleton {Z S : Scheme.{v}}
    [Nonempty Z] {n : ℕ} {L : Z.Modules} [Stacks.Ample.IsInvertibleModule Z L]
    (s : Fin (n + 1) → Γ(L, ⊤)) (hs : GeneratesStalks s) (f : Z ⟶ S)
    (h : (Set.range (toProjectiveSpaceOver s hs f).base).Subsingleton) :
    ∃ j, ∀ z, z ∈ Stacks.Ample.nonvanishingLocus L (s j) := by
  obtain ⟨z₀⟩ := ‹Nonempty Z›
  obtain ⟨j, hj⟩ := exists_mem_nvCover_of_generatesStalks s hs z₀
  have hpre := Stacks.AmpleImmersionReduction.preimage_standardChart s hs
    (toProjectiveSpaceOver s hs f) (fun i => ι_toProjectiveSpaceOver s hs f i) j
  refine ⟨j, fun z => ?_⟩
  have h0 : z₀ ∈ (toProjectiveSpaceOver s hs f) ⁻¹ᵁ projectiveSpaceOver.standardChart n S j := by
    rwa [hpre]
  have hz : z ∈ (toProjectiveSpaceOver s hs f) ⁻¹ᵁ projectiveSpaceOver.standardChart n S j := by
    rw [Scheme.Hom.mem_preimage] at h0 ⊢
    rwa [h ⟨z, rfl⟩ ⟨z₀, rfl⟩]
  rwa [hpre] at hz

private theorem isClosedMap_toProjectiveSpaceOver {Z S : Scheme.{v}} (f : Z ⟶ S) [IsProper f]
    {n : ℕ} {L : Z.Modules} [Stacks.Ample.IsInvertibleModule Z L] (s : Fin (n + 1) → Γ(L, ⊤))
    (hs : GeneratesStalks s) : IsClosedMap (toProjectiveSpaceOver s hs f).base := by
  have : IsProper (toProjectiveSpaceOver s hs f ≫ CategoryTheory.Limits.pullback.fst
      (CategoryTheory.Limits.terminal.from S)
      (CategoryTheory.Limits.terminal.from (projectiveSpaceAtUniverse.{v} n))) := by
    rw [toProjectiveSpaceOver_fst]
    infer_instance
  have := IsProper.of_comp (toProjectiveSpaceOver s hs f) (CategoryTheory.Limits.pullback.fst
      (CategoryTheory.Limits.terminal.from S)
      (CategoryTheory.Limits.terminal.from (projectiveSpaceAtUniverse.{v} n)))
  exact (toProjectiveSpaceOver s hs f).isClosedMap

/-- A basis of the sections of an invertible sheaf generating it at every point gives the whole
space as the open of the linear system. -/
private theorem linearSystemLocus_eq_top_of_forall (k : Type v) [Field k] {X : Scheme.{v}}
    [X.Over (Spec (.of k))] (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] {ι : Type v}
    (b : Module.Basis ι k Γ(L, ⊤))
    (h : ∀ x : X, ∃ s : Γ(L, ⊤), x ∈ Stacks.Ample.nonvanishingLocus L s) :
    linearSystemLocus k L b = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  rw [mem_linearSystemLocus_iff]
  by_contra hx
  push Not at hx
  obtain ⟨s, hs⟩ := h x
  let V : Submodule k Γ(L, ⊤) :=
    { carrier := {t | x ∉ Stacks.Ample.nonvanishingLocus L t}
      add_mem' := fun ha hb hab => (Stacks.Ample.nonvanishingLocus_add_subset L _ _ hab).elim ha hb
      zero_mem' := by simp
      smul_mem' := fun c t ht hct => ht (Stacks.Ample.nonvanishingLocus_smul_subset L
        (Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.baseRingHom k X c) t hct) }
  have hV : (⊤ : Submodule k Γ(L, ⊤)) ≤ V := by
    rw [← b.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hx i
  exact (hV (Submodule.mem_top (x := s))) hs

open Stacks.Ample Stacks.RelativeVeryAmple in
/-- `𝒪_X(E)^{⊗ n} ≅ 𝒪_X(nE)` for a Cartier divisor `E`. -/
private noncomputable def tensorPowDivisorialIso {X : Scheme.{v}} [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] (E : Divisor X) (hE : E.IsCartier)
    [IsInvertibleModule X E.divisorialSheaf] :
    (n : ℕ) → tensorPowModule X E.divisorialSheaf (n : ℤ) ≅ (n • E).divisorialSheaf
  | 0 => tensorPowModuleZeroIso X E.divisorialSheaf ≪≫
      (eqToIso rfl : unitModule X ≅ MMP.Mori.structureSheafModule X) ≪≫
      (Divisor.divisorialSheafZeroIso (X := X)).symm ≪≫
      eqToIso (by rw [zero_nsmul])
  | (n + 1) =>
      tensorPowModuleCongr X E.divisorialSheaf
          (show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 by push_cast; ring) ≪≫
        (tensorPowModuleAddIso X E.divisorialSheaf (n : ℤ) 1).symm ≪≫
        tensorModulesMapIso X (tensorPowDivisorialIso E hE n)
          (tensorPowModuleOneIso X E.divisorialSheaf) ≪≫
        (hE.nsmul n).divisorialSheafTensorIso hE ≪≫
        eqToIso (by rw [succ_nsmul])

/-- **The curve part.** A `ℚ`-divisor on a normal projective curve having an ample Cartier
multiple is eventually free and composed of a pencil. -/
private theorem isEventuallyFreePencil_of_isAmple_of_curve {k : Type v} [Field k]
    [IsAlgClosed k] {C : Scheme.{v}} [IsLocallyNoetherian C] [IsNormal C] [CompactSpace C]
    (sC : C ⟶ Spec (.of k)) (hC : MMP.Mori.IsProjectiveVariety k sC)
    (hdim : topologicalKrullDim C = 1) (N : QDivisor C) (n : ℕ) (hn : 0 < n) (A : Divisor C)
    (hA : Divisor.toQDivisor A = (n : ℚ) • N) (hAc : A.IsCartier) (hAa : A.IsAmple hAc) :
    IsEventuallyFreePencil k sC N := by
  classical
  have := hC.toIsIntegral
  have : IsProper sC := isProper_of_isProjectiveMorphism sC hC.isProjective
  have : AlgebraicGeometry.IsVariety k sC := hC.toIsVariety
  have : AlgebraicGeometry.IsCurve k sC := ⟨hdim⟩
  letI : C.Over (Spec (.of k)) := ⟨sC⟩
  have := hAc.isInvertibleModule_divisorialSheaf
  obtain ⟨N₀, r, s, hN₀, hgen, haff⟩ :=
    Stacks.AmpleImmersionReduction.exists_generating_family_of_isAmple _ hAa
  have hEc : (N₀ • A).IsCartier := hAc.nsmul N₀
  have := hEc.isInvertibleModule_divisorialSheaf
  set e := tensorPowDivisorialIso A hAc N₀
  set t : Fin (r + 1) → Γ((N₀ • A).divisorialSheaf, ⊤) := fun i => e.hom.app ⊤ (s i)
  have ht : ∀ i, Stacks.Ample.nonvanishingLocus _ (t i) =
      Stacks.Ample.nonvanishingLocus _ (s i) :=
    fun i => Stacks.CokernelSupport.nonvanishingLocus_iso_app e (s i)
  refine ⟨N₀ * n, Nat.mul_pos (by omega) hn, N₀ • A, ?_, hC, hEc, ?_⟩
  · rw [map_nsmul, hA, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, ← Int.cast_smul_eq_zsmul ℚ]
    push_cast
    rfl
  have := finiteDimensional_globalSections k sC (N₀ • A).divisorialSheaf
  let b := Module.Basis.ofVectorSpace k Γ((N₀ • A).divisorialSheaf, ⊤)
  have hloc : linearSystemLocus k _ b = ⊤ :=
    linearSystemLocus_eq_top_of_forall k _ b fun x => by
      obtain ⟨i, hi⟩ := exists_mem_nvCover_of_generatesStalks s hgen x
      exact ⟨t i, by rwa [ht]⟩
  refine ⟨_, b, hloc, ?_⟩
  obtain ⟨m, ⟨e'⟩⟩ := exists_equiv_fin_of_linearSystemLocus_eq_top k _ b hloc
  have hg := generatesStalks_of_linearSystemLocus_eq_top k _ b e' hloc
  rw [topologicalKrullDim_linearSystemImage_eq k _ b e' hg hloc]
  have hφc := isClosedMap_toProjectiveSpaceOver sC (fun i => b (e' i)) hg
  unfold rdim
  change topologicalKrullDim (closure (Set.range
    (toProjectiveSpaceOver (fun i => b (e' i)) hg sC).base)) = 1
  rw [hφc.isClosed_range.closure_eq]
  refine eq_one_of_le_one_of_not_le_zero ?_ fun h0 => ?_
  · exact (topologicalKrullDim_range_le_of_isClosedMap _
      (toProjectiveSpaceOver (fun i => b (e' i)) hg sC).continuous hφc).trans hdim.le
  have : QuasiSober (Set.range (toProjectiveSpaceOver (fun i => b (e' i)) hg sC).base) :=
    hφc.isClosed_range.isClosedEmbedding_subtypeVal.quasiSober
  have : IrreducibleSpace
      (Set.range (toProjectiveSpaceOver (fun i => b (e' i)) hg sC).base) := by
    refine Subtype.irreducibleSpace ?_
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ C).image _
      (toProjectiveSpaceOver (fun i => b (e' i)) hg sC).continuous.continuousOn
  have hsub := (Set.subsingleton_coe _).1 (subsingleton_of_topologicalKrullDim_le_zero h0)
  obtain ⟨j, hj⟩ := exists_forall_mem_nonvanishingLocus_of_subsingleton _ hg _ hsub
  -- every section is a multiple of the nowhere vanishing `b (e' j)`
  obtain ⟨x₀⟩ : Nonempty C := inferInstance
  obtain ⟨i₀, hi₀⟩ := exists_mem_nvCover_of_generatesStalks s hgen x₀
  have hle : (⊤ : C.Opens) ≤ Stacks.NonvanishingOpen.nonvanishingOpen C _ (b (e' j)) :=
    fun z _ => hj z
  obtain ⟨a, ha⟩ := (Stacks.NonvanishingSpelling.bijective_smul C (N₀ • A).divisorialSheaf
    (b (e' j)) hle).2 (t i₀)
  have hres : (N₀ • A).divisorialSheaf.presheaf.map
      (homOfLE (le_refl (⊤ : C.Opens))).op (b (e' j)) = b (e' j) := by
    rw [show homOfLE (le_refl (⊤ : C.Opens)) = 𝟙 ⊤ from rfl, op_id,
      CategoryTheory.Functor.map_id]
    rfl
  simp only [hres] at ha
  have hfield : IsField Γ(C, ⊤) := Stacks.Models.isField_globalSections_of_connectedSpace k sC
  have hloc0 : Stacks.Ample.nonvanishingLocus _ (t i₀) = (C.basicOpen a : Set C) := by
    rw [← ha, Stacks.Ample.nonvanishingLocus_smul]
    exact Set.inter_eq_left.mpr fun z _ => hj z
  have ha0 : a ≠ 0 := by
    rintro rfl
    have : x₀ ∈ Stacks.Ample.nonvanishingLocus _ (t i₀) := by rwa [ht]
    rwa [hloc0, Scheme.basicOpen_zero] at this
  obtain ⟨a', ha'⟩ := hfield.mul_inv_cancel ha0
  have hu : IsUnit a := IsUnit.of_mul_eq_one a' ha'
  have htop : nvCover s i₀ = ⊤ := by
    refine eq_top_iff.mpr fun z _ => ?_
    change z ∈ Stacks.Ample.nonvanishingLocus _ (s i₀)
    rw [← ht, hloc0, Scheme.basicOpen_of_isUnit _ hu]
    trivial
  exact IsAffineOpen.ne_top_of_isCurve k sC (haff i₀) htop

end Curve

/-! ### Sections and their divisors of zeros -/

section ZeroDivisor

variable {X : Scheme.{v}} [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X] [CompactSpace X]

/-- A nonzero section `σ` of `𝒪_X(M)` is the rational function `φ` with `div φ + M = (σ)₀`;
multiplication by `φ⁻¹` carries it to the section `1` of `𝒪_X((σ)₀)`. -/
private theorem divisorialSheafMulIso_app_eq_oneSection {M : Divisor X}
    (σ : M.divisorialSubmodule ⊤) (hσ : σ ≠ 0) :
    ((Divisor.divisorialSheafMulIso (D := M) (D' := M.zeroDivisor σ hσ)
        (Divisor.isUnit_sectionToRationalFunctions hσ).unit⁻¹ fun E => by
          rw [Divisor.zeroDivisor_eq, DivisorWithCoeffs.coeff_add, coeff_principalDivisor,
            PrimeDivisor.ord_inv]; ring).hom.app ⊤ σ) =
      MMP.Threefold.Mori.oneSection (M.zeroDivisor_nonneg σ hσ) := by
  refine Subtype.ext (funext fun Z => ?_)
  change ((Divisor.isUnit_sectionToRationalFunctions hσ).unit⁻¹ : (RationalFunctions X)ˣ).1 Z.1 *
      σ.1 Z = ((Divisor.structureSheafToDivisorialSheaf _).app ⊤ (1 : Γ(X, ⊤))).1 Z
  rw [Divisor.coe_structureSheafToDivisorialSheaf_app, map_one]
  have h1 : σ.1 Z = ((Divisor.isUnit_sectionToRationalFunctions hσ).unit :
      RationalFunctions X) Z.1 := rfl
  rw [h1, ← Pi.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  rfl

/-- **The nonvanishing locus of a section is the complement of its divisor of zeros**, for a
Cartier divisor `M`. -/
private theorem nonvanishingLocus_eq_compl_supp_zeroDivisor {M : Divisor X} (hM : M.IsCartier)
    (σ : M.divisorialSubmodule ⊤) (hσ : σ ≠ 0) :
    have := hM.isInvertibleModule_divisorialSheaf
    Stacks.Ample.nonvanishingLocus M.divisorialSheaf σ = ((M.zeroDivisor σ hσ).supp : Set X)ᶜ := by
  have := hM.isInvertibleModule_divisorialSheaf
  have hZc : (M.zeroDivisor σ hσ).IsCartier := by
    rw [Divisor.zeroDivisor_eq]
    exact (Divisor.isCartier_principalDivisor _).add hM
  have := hZc.isInvertibleModule_divisorialSheaf
  rw [← Stacks.CokernelSupport.nonvanishingLocus_iso_app (Divisor.divisorialSheafMulIso (D := M)
    (D' := M.zeroDivisor σ hσ) (Divisor.isUnit_sectionToRationalFunctions hσ).unit⁻¹ fun E => by
      rw [Divisor.zeroDivisor_eq, DivisorWithCoeffs.coeff_add, coeff_principalDivisor,
        PrimeDivisor.ord_inv]; ring) σ]
  rw [divisorialSheafMulIso_app_eq_oneSection σ hσ]
  exact MMP.Threefold.Mori.nonvanishingLocus_oneSection _ hZc

end ZeroDivisor

/-! ### From a free pencil to a curve -/

section Pencil

open Stacks.ProjectiveFromSections Stacks.ProjectiveSpaceModuli

/-- The projective line over a field has dimension one. -/
private theorem topologicalKrullDim_projectiveSpaceOver_one (k : Type v) [Field k] :
    topologicalKrullDim (projectiveSpaceOver.{v} 1 (Spec (.of k))) = 1 := by
  let b := Finsupp.basisSingleOne (R := k) (ι := Fin 2)
  let e := Scheme.homeoOfIso ((Over.forget _).mapIso (basisProjectiveSpaceOfModuleIso b))
  have h : topologicalKrullDim (projectiveSpaceOfModule k (Fin 2 →₀ k)) = ((1 : ℕ) : WithBot ℕ∞) :=
    topologicalKrullDim_projectiveSpaceOfModule_of_finrank_eq (by simp)
  exact e.isHomeomorph.topologicalKrullDim_eq.symm.trans h

/-- **A free pencil defines a fibration over a curve.** Let `X` be a normal projective variety
and `σ₁, σ₂` sections of `𝒪_X(M)`, `M` Cartier, with disjoint nonempty divisors of zeros. The
morphism `X ⟶ ℙ¹` they define has a Stein factorization `p : X ⟶ C` onto a smooth projective
curve with `p_* 𝒪_X = 𝒪_C`, and every irreducible closed subset of `X` missing `(σ₁)₀` or `(σ₂)₀`
is mapped by `p` to a point. -/
private theorem exists_curve_of_pencil {k : Type v} [Field k] [IsAlgClosed k] {X : Scheme.{v}}
    {sX : X ⟶ Spec (.of k)} [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X]
    [CompactSpace X] (hX : MMP.Mori.IsProjectiveVariety k sX)
    {M : Divisor X} (hM : M.IsCartier) (σ₁ σ₂ : M.divisorialSubmodule ⊤) (hσ₁ : σ₁ ≠ 0)
    (hσ₂ : σ₂ ≠ 0)
    (hdisj : Disjoint ((M.zeroDivisor σ₁ hσ₁).supp : Set X) (M.zeroDivisor σ₂ hσ₂).supp)
    (hne₁ : ((M.zeroDivisor σ₁ hσ₁).supp : Set X).Nonempty)
    (hne₂ : ((M.zeroDivisor σ₂ hσ₂).supp : Set X).Nonempty) :
    ∃ (C : Scheme.{v}) (_ : IsLocallyNoetherian C) (_ : IsNormal C) (_ : CompactSpace C)
      (sC : C ⟶ Spec (.of k)) (_ : MMP.Mori.IsProjectiveVariety k sC)
      (_ : topologicalKrullDim C = 1) (_ : IsSmoothScheme sC) (p : X ⟶ C) (_ : p ≫ sC = sX)
      (_ : ∀ U : C.Opens, IsIso (p.app U)) (_ : Surjective p) (_ : IsProjectiveMorphism p),
      (∀ x y : X, p x = p y → (x ∈ ((M.zeroDivisor σ₁ hσ₁).supp : Set X) ↔
        y ∈ ((M.zeroDivisor σ₁ hσ₁).supp : Set X))) ∧
      (∀ x y : X, p x = p y → (x ∈ ((M.zeroDivisor σ₂ hσ₂).supp : Set X) ↔
        y ∈ ((M.zeroDivisor σ₂ hσ₂).supp : Set X))) ∧
      (∀ T : Set X, IsIrreducible T → IsClosed T →
        Disjoint T (M.zeroDivisor σ₁ hσ₁).supp → (p '' T).Subsingleton) ∧
      ∀ T : Set X, IsIrreducible T → IsClosed T →
        Disjoint T (M.zeroDivisor σ₂ hσ₂).supp → (p '' T).Subsingleton := by
  classical
  have : IsProper sX := isProper_of_isProjectiveMorphism sX hX.isProjective
  have : AlgebraicGeometry.IsVariety k sX := hX.toIsVariety
  letI : X.Over (Spec (.of k)) := ⟨sX⟩
  have := hM.isInvertibleModule_divisorialSheaf
  -- the pencil and the morphism `φ : X ⟶ ℙ¹` it defines
  set s : Fin 2 → Γ(M.divisorialSheaf, ⊤) := ![σ₁, σ₂] with hs_def
  have hnv₁ : ∀ x : X, x ∈ nvCover s 0 ↔ x ∉ ((M.zeroDivisor σ₁ hσ₁).supp : Set X) := fun x => by
    change x ∈ Stacks.Ample.nonvanishingLocus M.divisorialSheaf σ₁ ↔ _
    rw [nonvanishingLocus_eq_compl_supp_zeroDivisor hM σ₁ hσ₁]
    rfl
  have hnv₂ : ∀ x : X, x ∈ nvCover s 1 ↔ x ∉ ((M.zeroDivisor σ₂ hσ₂).supp : Set X) := fun x => by
    change x ∈ Stacks.Ample.nonvanishingLocus M.divisorialSheaf σ₂ ↔ _
    rw [nonvanishingLocus_eq_compl_supp_zeroDivisor hM σ₂ hσ₂]
    rfl
  have hgen : GeneratesStalks s :=
    Stacks.AmpleImmersionReduction.generatesStalks_of_forall_exists_mem _ fun x => by
      by_cases hx : x ∈ ((M.zeroDivisor σ₁ hσ₁).supp : Set X)
      · exact ⟨1, (hnv₂ x).2 (Set.disjoint_left.mp hdisj hx)⟩
      · exact ⟨0, (hnv₁ x).2 hx⟩
  set φ := toProjectiveSpaceOver s hgen sX with hφ
  let sP := CategoryTheory.Limits.pullback.fst
    (CategoryTheory.Limits.terminal.from (Spec (.of k)))
    (CategoryTheory.Limits.terminal.from (projectiveSpaceAtUniverse.{v} 1))
  have hφP : φ ≫ sP = sX := toProjectiveSpaceOver_fst _ _ _
  have : IsProper (φ ≫ sP) := by rw [hφP]; infer_instance
  have : IsProper φ := IsProper.of_comp φ sP
  have hpre : ∀ i, φ ⁻¹ᵁ projectiveSpaceOver.standardChart 1 (Spec (.of k)) i = nvCover s i :=
    Stacks.AmpleImmersionReduction.preimage_standardChart s hgen φ
      (fun i => ι_toProjectiveSpaceOver s hgen sX i)
  -- the Stein factorization `φ = g ∘ q`
  obtain ⟨C, q, g, ⟨hS⟩, hqP, hqs, hqiso, -, hgfin, -, hYproj, hYnorm, -, -⟩ :=
    MMP.Resolution.Bridges.exists_steinFactorization_of_isVariety sX sP φ hφP
  have hcomp : q ≫ g = φ := hS.comp
  have hqg : ∀ x : X, g (q x) = φ x := fun x => by rw [← hcomp]; rfl
  set sC := g ≫ sP with hsC
  have hC : MMP.Mori.IsProjectiveVariety k sC :=
    hYproj (isProjectiveMorphism_projectiveSpaceOver 1 (Spec (.of k)))
  have : IsNormal C := hYnorm inferInstance
  have := hC.toIsIntegral
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian sC
  have : CompactSpace C := by
    have := hC.toQuasiCompact
    exact QuasiCompact.compactSpace_of_compactSpace sC
  have hps : q ≫ sC = sX := by rw [hsC, ← Category.assoc, hcomp, hφP]
  have hqproj : IsProjectiveMorphism q := by
    refine IsProjectiveMorphism.of_comp q sC ?_
    rw [hps]
    exact hX.isProjective
  -- two points of `X` with distinct images
  obtain ⟨x₁, hx₁⟩ := hne₁
  obtain ⟨x₂, hx₂⟩ := hne₂
  have hchart : ∀ i (x : X),
      φ x ∈ projectiveSpaceOver.standardChart 1 (Spec (.of k)) i ↔ x ∈ nvCover s i :=
    fun i x => by rw [← hpre i]; rfl
  have hx₁₀ : φ x₁ ∉ projectiveSpaceOver.standardChart 1 (Spec (.of k)) 0 := fun h' =>
    (hnv₁ x₁).1 ((hchart 0 x₁).1 h') hx₁
  have hx₁₁ : φ x₁ ∈ projectiveSpaceOver.standardChart 1 (Spec (.of k)) 1 :=
    (hchart 1 x₁).2 ((hnv₂ x₁).2 (Set.disjoint_left.mp hdisj hx₁))
  have hx₂₁ : φ x₂ ∉ projectiveSpaceOver.standardChart 1 (Spec (.of k)) 1 := fun h' =>
    (hnv₂ x₂).1 ((hchart 1 x₂).1 h') hx₂
  have hq₁₂ : q x₁ ≠ q x₂ := fun h' => hx₂₁ (by rwa [← hqg, ← h', hqg])
  -- `C` is a curve
  obtain ⟨y₀, hy₀⟩ : ∃ y : C, y ≠ genericPoint C := by
    by_cases h' : q x₁ = genericPoint C
    · exact ⟨q x₂, fun h'' => hq₁₂ (h'.trans h''.symm)⟩
    · exact ⟨q x₁, h'⟩
  have hdimC : topologicalKrullDim C = 1 := by
    refine le_antisymm ((MMP.Fourfold.topologicalKrullDim_le_of_isFinite g
      (T := Set.univ) fun _ => trivial).trans ?_)
      (one_le_topologicalKrullDim_of_specializes_of_ne
        ((genericPoint_spec C).specializes trivial) (Ne.symm hy₀))
    rw [(Homeomorph.Set.univ _).isHomeomorph.topologicalKrullDim_eq]
    exact (topologicalKrullDim_projectiveSpaceOver_one k).le
  have hCvar : MMP.Mori.IsVariety k sC := hC.toIsVariety
  have hCsm : IsSmoothScheme sC := by
    have hcl : ∀ y : C, y ≠ genericPoint C → y ∈ smoothLocus sC := fun y hy => by
      set Qy : MMP.Mori.PrimeDivisor C := AlgebraicGeometry.PrimeDivisor.ofCoheightOne y
        (MMP.Fourfold.coheight_eq_one_of_ne_genericPoint hdimC hy)
      have hQy : Qy.genericPoint = y :=
        AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
      have := MMP.Threefold.Mori.CanonUniq.genericPoint_mem_smoothLocus (f := sC) hCvar Qy
      rwa [hQy] at this
    refine eq_top_iff.mpr fun y _ => ?_
    by_cases hy : y = genericPoint C
    · rw [hy]
      exact ((genericPoint_spec C).specializes trivial : genericPoint C ⤳ y₀).mem_open
        (smoothLocus sC).isOpen (hcl y₀ hy₀)
    · exact hcl y hy
  -- verticality
  have hvert : ∀ (i : Fin 2) (x₀ : X), φ x₀ ∉ projectiveSpaceOver.standardChart 1 (Spec (.of k)) i →
      ∀ T : Set X, IsIrreducible T → IsClosed T → (∀ t ∈ T, t ∈ nvCover s i) →
        (q '' T).Subsingleton := by
    intro i x₀ hx₀ T hT hTc hTd
    have hI : IsIrreducible (q '' T) := hT.image q q.continuous.continuousOn
    have hcl : IsClosed (q '' T) := q.isClosedMap T hTc
    obtain ⟨ξ, hξ⟩ := QuasiSober.sober hI hcl
    by_cases hξg : ξ = genericPoint C
    · exfalso
      have hmem : q x₀ ∈ q '' T := by
        rw [← hξ.def, hξg, (genericPoint_spec C).def]; trivial
      obtain ⟨t, ht, hteq⟩ := hmem
      have h1 : φ t ∈ projectiveSpaceOver.standardChart 1 (Spec (.of k)) i :=
        (hchart i t).2 (hTd t ht)
      rw [← hqg, hteq, hqg] at h1
      exact hx₀ h1
    · have hcl' := Stacks.AlgebraicGeometry.AmpleDimensionOne.isClosed_singleton_of_ne_genericPoint
        C hdimC hξg
      rw [← hξ.def, hcl'.closure_eq]
      exact Set.subsingleton_singleton
  have hsat : ∀ (i : Fin 2) (x y : X), q x = q y →
      (x ∈ nvCover s i ↔ y ∈ nvCover s i) := by
    intro i x y hxy
    have hφ : φ x = φ y := by rw [← hqg, hxy, hqg]
    rw [← hchart i x, ← hchart i y, hφ]
  refine ⟨C, inferInstance, inferInstance, inferInstance, sC, hC, hdimC, hCsm, q, hps, hqiso, hqs,
    hqproj, fun x y hxy => ?_, fun x y hxy => ?_, ?_, ?_⟩
  · have := hsat 0 x y hxy
    rw [hnv₁, hnv₁] at this
    exact not_iff_not.mp this
  · have := hsat 1 x y hxy
    rw [hnv₂, hnv₂] at this
    exact not_iff_not.mp this
  · intro T hT hTc hTd
    exact hvert 0 x₁ hx₁₀ T hT hTc fun t ht => (hnv₁ t).2 (Set.disjoint_left.mp hTd ht)
  · intro T hT hTc hTd
    exact hvert 1 x₂ hx₂₁ T hT hTc fun t ht => (hnv₂ t).2 (Set.disjoint_left.mp hTd ht)

end Pencil

/-! ### Sections of divisorial sheaves as rational functions -/

section Rational

variable {X : Scheme.{v}} [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X] [CompactSpace X]

/-- The valuation along `E` of the component of a unit of `K(X)` is `exp (v_E φ)`. -/
private theorem valuation_component_eq_exp_ord (E : MMP.Mori.PrimeDivisor X)
    (φ : (RationalFunctions X)ˣ) :
    E.valuation ((φ : RationalFunctions X) E.component) = WithZero.exp (E.ord φ) := by
  rw [E.ord_eq_ordUnit, ← E.valuation_eq_exp_ordUnit]
  rfl

/-- A rational function `φ` with `div φ + D ≥ 0` is a global section of `𝒪_X(D)`. -/
private theorem symm_mem_divisorialSubmodule_of_nonneg {D : Divisor X}
    (φ : (RationalFunctions X)ˣ) (hφ : 0 ≤ principalDivisor φ + D) :
    (rationalFunctionsPresheafTopEquiv X).symm (φ : RationalFunctions X) ∈
      D.divisorialSubmodule ⊤ := by
  intro E _
  refine Or.inr ?_
  change WithZero.exp (-D.coeff E) ≤ E.valuation ((φ : RationalFunctions X) E.component)
  rw [valuation_component_eq_exp_ord, WithZero.exp_le_exp]
  have := hφ E
  change 0 ≤ (principalDivisor φ).coeff E + D.coeff E at this
  rw [coeff_principalDivisor] at this
  omega

/-- **A rational function with `div φ + D ≥ 0` is a section of `𝒪_X(D)`**: the section whose
rational function is `φ`, with divisor of zeros `div φ + D`. -/
private theorem exists_section_of_nonneg {D : Divisor X} (φ : (RationalFunctions X)ˣ)
    (hφ : 0 ≤ principalDivisor φ + D) :
    ∃ (τ : D.divisorialSubmodule ⊤) (hτ : τ ≠ 0), D.zeroDivisor τ hτ = principalDivisor φ + D ∧
      Divisor.sectionToRationalFunctions τ = φ := by
  let e := rationalFunctionsPresheafTopEquiv X
  set τ : D.divisorialSubmodule ⊤ := ⟨_, symm_mem_divisorialSubmodule_of_nonneg φ hφ⟩
  have hτφ : Divisor.sectionToRationalFunctions τ = φ := e.apply_symm_apply _
  have hτ : τ ≠ 0 := fun h0 => by
    have h1 : Divisor.sectionToRationalFunctions τ = 0 := by rw [h0]; exact map_zero e
    rw [hτφ] at h1
    have : Nontrivial (RationalFunctions X) :=
      (rationalFunctionsEquivFunctionField X).toEquiv.nontrivial
    exact φ.ne_zero h1
  refine ⟨τ, hτ, ?_, hτφ⟩
  rw [Divisor.zeroDivisor_eq]
  congr 2
  exact Units.ext ((Divisor.isUnit_sectionToRationalFunctions hτ).unit_spec.trans hτφ)

end Rational

/-! ### Two sections with incomparable divisors of zeros -/

section Sections

variable {k : Type v} [Field k] [IsAlgClosed k] {X : Scheme.{v}} {sX : X ⟶ Spec (.of k)}
  [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X] [CompactSpace X]

/-- The global sections of `𝒪_X(D)`, `D` Cartier on a proper `k`-scheme, are a finite
`k`-module. -/
private theorem finite_divisorialSubmodule_top (sX : X ⟶ Spec (.of k)) [IsProper sX]
    {D : Divisor X} (hD : D.IsCartier) :
    letI := Module.compHom (D.divisorialSubmodule ⊤) (scalarsToGlobalSections k sX);
    Module.Finite k (D.divisorialSubmodule ⊤) := by
  have := hD.isInvertibleModule_divisorialSheaf
  exact finiteDimensional_globalSections k sX D.divisorialSheaf

/-- **Comparable divisors of zeros come from proportional sections.** If `(σ)₀ ≤ (σ')₀` for
nonzero sections of `𝒪_X(D)` on a proper normal variety over an algebraically closed field, then
`σ' = c σ` for a scalar `c`: the ratio `σ'/σ` has `div(σ'/σ) = (σ')₀ - (σ)₀ ≥ 0`, so it lies in
the finite `k`-algebra `H⁰(X, 𝒪_X)`, a domain, which is `k`. -/
private theorem exists_eq_smul_of_zeroDivisor_le (sX : X ⟶ Spec (.of k)) [IsProper sX]
    {D : Divisor X} {σ σ' : D.divisorialSubmodule ⊤} (hσ : σ ≠ 0) (hσ' : σ' ≠ 0)
    (hle : D.zeroDivisor σ hσ ≤ D.zeroDivisor σ' hσ') :
    ∃ c : k, σ' = scalarsToGlobalSections k sX c • σ := by
  let T := ToType ((rationalFunctionsPresheaf X).obj (Opposite.op ⊤))
  let e := rationalFunctionsPresheafTopEquiv X
  set ψ := (Divisor.isUnit_sectionToRationalFunctions hσ).unit
  set ψ' := (Divisor.isUnit_sectionToRationalFunctions hσ').unit
  have hu : 0 ≤ principalDivisor (ψ' * ψ⁻¹) + 0 := by
    have h := sub_nonneg.mpr hle
    rw [Divisor.zeroDivisor_eq, Divisor.zeroDivisor_eq] at h
    rw [add_zero, MMP.Mori.principalDivisor_mul, MMP.Mori.principalDivisor_inv]
    convert h using 1
    abel
  have hmem := symm_mem_divisorialSubmodule_of_nonneg _ hu
  have h1 : (1 : T) ∈ (0 : Divisor X).divisorialSubmodule ⊤ := by
    have := symm_mem_divisorialSubmodule_of_nonneg (D := (0 : Divisor X)) 1
      (by rw [MMP.Mori.principalDivisor_one, add_zero])
    rwa [Units.val_one, map_one] at this
  letI : Algebra k T := ((algebraMap Γ(X, ⊤) T).comp (scalarsToGlobalSections k sX)).toAlgebra
  let S : Subalgebra k T :=
    { carrier := (0 : Divisor X).divisorialSubmodule ⊤
      mul_mem' := fun {a b} ha hb => by
        have := Divisor.IsDivisorialSection.mul ha hb
        rwa [add_zero] at this
      add_mem' := fun ha hb => Submodule.add_mem _ ha hb
      algebraMap_mem' := fun c => by
        change algebraMap Γ(X, ⊤) T (scalarsToGlobalSections k sX c) ∈ _
        rw [← mul_one (algebraMap Γ(X, ⊤) T _), ← Algebra.smul_def]
        exact Submodule.smul_mem _ _ h1 }
  letI := Module.compHom ((0 : Divisor X).divisorialSubmodule ⊤) (scalarsToGlobalSections k sX)
  have := finite_divisorialSubmodule_top sX (Divisor.isCartier_zero (X := X))
  let g : ((0 : Divisor X).divisorialSubmodule ⊤) ≃ₗ[k] S :=
    { toFun := fun t => ⟨t.1, t.2⟩
      invFun := fun t => ⟨t.1, t.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have : Module.Finite k S := Module.Finite.equiv g
  have : IsDomain T :=
    Function.Injective.isDomain (e.trans (rationalFunctionsEquivFunctionField X))
      (e.trans (rationalFunctionsEquivFunctionField X)).injective
  have : Algebra.IsIntegral k S := Algebra.IsIntegral.of_finite k S
  obtain ⟨c, hc⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := S)).2
    ⟨_, hmem⟩
  refine ⟨c, Subtype.ext ?_⟩
  have hc' : algebraMap k T c =
      e.symm ((ψ' * ψ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) :=
    congrArg Subtype.val hc
  change σ'.1 = algebraMap Γ(X, ⊤) T (scalarsToGlobalSections k sX c) * σ.1
  rw [show algebraMap Γ(X, ⊤) T (scalarsToGlobalSections k sX c) = algebraMap k T c from rfl, hc']
  apply e.injective
  rw [map_mul, e.apply_symm_apply]
  have hψ : e σ.1 = (ψ : RationalFunctions X) :=
    ((Divisor.isUnit_sectionToRationalFunctions hσ).unit_spec).symm
  have hψ' : e σ'.1 = (ψ' : RationalFunctions X) :=
    ((Divisor.isUnit_sectionToRationalFunctions hσ').unit_spec).symm
  rw [hψ, hψ', Units.val_mul, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]

end Sections

/-! ### The moving part of the pencil -/

section Moving

variable {X : Scheme.{v}} [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X] [CompactSpace X]

/-- **The moving part of a pencil.** Let `Z₂ = Z₁ + div ψ` be effective divisors and
`F = min(Z₁, Z₂)`. If `M₁ = Z₁ - F` and `M₂ = Z₂ - F` have disjoint supports, then `M₁` is Cartier
(it is `0` off `Supp M₁` and `-div ψ` off `Supp M₂`), and `1`, `ψ` are sections of `𝒪_X(M₁)` with
divisors of zeros `M₁` and `M₂`. -/
private theorem exists_sections_of_disjoint {Z₁ Z₂ : Divisor X} (hZ₁ : 0 ≤ Z₁) (hZ₂ : 0 ≤ Z₂)
    (ψ : (RationalFunctions X)ˣ) (hψ : Z₂ = principalDivisor ψ + Z₁)
    (hdisj : Disjoint ((Z₁ - Z₁ ⊓ Z₂).supp : Set X) (Z₂ - Z₁ ⊓ Z₂).supp) :
    (Z₁ - Z₁ ⊓ Z₂).IsCartier ∧ ∃ (τ₁ τ₂ : (Z₁ - Z₁ ⊓ Z₂).divisorialSubmodule ⊤) (hτ₁ : τ₁ ≠ 0)
      (hτ₂ : τ₂ ≠ 0), (Z₁ - Z₁ ⊓ Z₂).zeroDivisor τ₁ hτ₁ = Z₁ - Z₁ ⊓ Z₂ ∧
        (Z₁ - Z₁ ⊓ Z₂).zeroDivisor τ₂ hτ₂ = Z₂ - Z₁ ⊓ Z₂ := by
  set M₁ := Z₁ - Z₁ ⊓ Z₂
  set M₂ := Z₂ - Z₁ ⊓ Z₂
  have hM₁ : 0 ≤ M₁ := sub_nonneg.mpr inf_le_left
  have hM₂ : 0 ≤ M₂ := sub_nonneg.mpr inf_le_right
  have hM₂₁ : M₂ = principalDivisor ψ + M₁ := by
    simp only [M₁, M₂]
    rw [hψ]
    abel_nf
  -- a coefficient is zero along a prime divisor meeting the complement of the support
  have hcoeff : ∀ (G : Divisor X) (E : MMP.Mori.PrimeDivisor X),
      (E.support ∩ ((G.supp : Set X)ᶜ)).Nonempty → G.coeff E = 0 := by
    rintro G E ⟨x, hxE, hxG⟩
    by_contra hne
    exact hxG (DivisorWithCoeffs.mem_supp_iff.mpr ⟨E, hne, hxE⟩)
  refine ⟨fun x => ?_, ?_⟩
  · by_cases hx : x ∈ (M₁.supp : Set X)
    · have hx₂ : x ∉ (M₂.supp : Set X) := Set.disjoint_left.mp hdisj hx
      refine ⟨⟨(M₂.supp : Set X)ᶜ, M₂.isClosed_supp.isOpen_compl⟩, hx₂, ψ⁻¹, fun E hE => ?_⟩
      have h2 := hcoeff M₂ E hE
      have h3 := congrArg (fun G : Divisor X => G.coeff E) hM₂₁
      simp only [DivisorWithCoeffs.coeff_add, coeff_principalDivisor, h2] at h3
      rw [MMP.Mori.PrimeDivisor.ord_inv]
      omega
    · refine ⟨⟨(M₁.supp : Set X)ᶜ, M₁.isClosed_supp.isOpen_compl⟩, hx, 1, fun E hE => ?_⟩
      rw [hcoeff M₁ E hE, MMP.Mori.PrimeDivisor.ord_one]
  · obtain ⟨τ₁, hτ₁, he₁, -⟩ := exists_section_of_nonneg (D := M₁) 1
      (by rwa [MMP.Mori.principalDivisor_one, zero_add])
    obtain ⟨τ₂, hτ₂, he₂, -⟩ := exists_section_of_nonneg (D := M₁) ψ (hM₂₁ ▸ hM₂)
    refine ⟨τ₁, τ₂, hτ₁, hτ₂, ?_, ?_⟩
    · rw [he₁, MMP.Mori.principalDivisor_one, zero_add]
    · rw [he₂, hM₂₁]

end Moving

section ToQ

variable {X : Scheme.{v}} [IsLocallyNoetherian X] [IsNormal X]

private theorem toQDivisor_apply (G : Divisor X) (E : MMP.Mori.PrimeDivisor X) :
    (Divisor.toQDivisor G) E = (G E : ℚ) := by
  rw [← DivisorWithCoeffs.coeff_apply, Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_apply]

end ToQ

/-! ### Divisors on a smooth projective curve and their pull-backs -/

section CurveDivisors

/-- A closed embedding `f : Y → X` into an irreducible space with `dim X ≤ n ≤ dim Y` is
surjective: otherwise the image of a chain of length `n` in `Y`, followed by `X`, is a chain
of length `n + 1` in `X`. -/
private theorem surjective_of_topologicalKrullDim_le {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [IrreducibleSpace X] {f : Y → X} (hf : Topology.IsClosedEmbedding f)
    {n : ℕ} (hX : topologicalKrullDim X ≤ n) (hY : (n : WithBot ℕ∞) ≤ topologicalKrullDim Y) :
    Function.Surjective f := by
  by_contra hns
  have hne : Set.range f ≠ Set.univ := fun h => hns (Set.range_eq_univ.mp h)
  obtain ⟨l, hl⟩ := Order.le_krullDim_iff.mp hY
  let φ : TopologicalSpace.IrreducibleCloseds Y → TopologicalSpace.IrreducibleCloseds X :=
    fun Z => ⟨f '' Z, Z.isIrreducible.image f hf.continuous.continuousOn,
      hf.isClosedMap _ Z.isClosed⟩
  have hφ : StrictMono φ := fun a b hab =>
    (hf.injective.image_strictMono : StrictMono (f '' ·)) (show (a : Set Y) < b from hab)
  let top : TopologicalSpace.IrreducibleCloseds X :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  have hlt : φ l.last < top := by
    show f '' (l.last : Set Y) < Set.univ
    exact lt_of_le_of_lt (Set.image_subset_range f _) (Set.ssubset_univ_iff.mpr hne)
  have h := Order.LTSeries.length_le_krullDim ((l.map φ hφ).snoc top hlt)
  have hlen : ((l.map φ hφ).snoc top hlt).length = n + 1 := by
    change l.length + 1 = n + 1
    omega
  rw [hlen] at h
  exact absurd (h.trans hX) (by exact_mod_cast Nat.not_succ_le_self n)

/-- **An effective nonzero Cartier divisor on a projective curve is ample**, by the Nakai
criterion: its degree on the curve is positive. -/
private theorem isAmple_of_nonneg_of_ne_zero {k : Type v} [Field k] {C : Scheme.{v}}
    [IsLocallyNoetherian C] [IsNormal C] [CompactSpace C] [IsIntegral C]
    (sC : C ⟶ Spec (.of k)) (hC : MMP.Mori.IsProjectiveVariety k sC)
    (hdim : topologicalKrullDim C = 1) (A : Divisor C) (hAc : A.IsCartier) (h0 : 0 ≤ A)
    (hne : A ≠ 0) : A.IsAmple hAc := by
  have : IsProper sC := isProper_of_isProjectiveMorphism sC hC.isProjective
  have := hAc.isInvertibleModule_divisorialSheaf
  have hP : IsProjective sC := ((isProjectiveVariety_iff_isProjective' k sC).1 hC).2
  refine isAmple_of_sheafSelfIntersectionNumber_pos_of_dim_pos k sC hP _
    fun V i _ _ d hd hd0 => ?_
  have hVS : topologicalKrullDim V ≤ 1 :=
    ((topologicalKrullDim_range_eq i).symm.le.trans (topologicalKrullDim_subspace_le C _)).trans
      hdim.le
  have hd1 : d ≤ 1 := by
    rw [hd] at hVS
    exact_mod_cast hVS
  obtain rfl : d = 1 := by omega
  have hV : topologicalKrullDim V = 1 := by rw [hd]; rfl
  have hsurj : Function.Surjective i := surjective_of_topologicalKrullDim_le i.isClosedEmbedding
    (n := 1) (by rw [hdim]; rfl) (by rw [hd])
  obtain ⟨E, hE⟩ := DFunLike.ne_iff.mp hne
  have hEx : E.genericPoint ∈ (A.supp : Set C) := DivisorWithCoeffs.mem_supp_iff.mpr ⟨E, hE, by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl⟩
  obtain ⟨c₁, hc₁⟩ := hsurj E.genericPoint
  obtain ⟨c₀, hc₀⟩ := hsurj (genericPoint C)
  obtain ⟨hnn, hiff⟩ := MMP.Threefold.Mori.degreeOn_nonneg_and_eq_zero_iff sC i hV.le A hAc h0
    ⟨c₀, by rw [hc₀]; exact MMP.Fourfold.genericPoint_notMem_supp A⟩
  have hpos : 0 < A.degreeOn k sC i hV.le hAc :=
    lt_of_le_of_ne hnn fun h => hiff.1 h.symm c₁ (by rwa [hc₁])
  have h3 : A.degreeOn k sC i hV.le hAc =
      invertibleCurveDegree k (i ≫ sC) hV.le ((Scheme.Modules.pullback i).obj A.divisorialSheaf) :=
    rfl
  rw [h3, ← intersectionNumber_one_eq_invertibleCurveDegree] at hpos
  rw [sheafSelfIntersectionNumber, Snapper.sheafIntersectionNumber_eq_intersectionNumber]
  exact hpos

variable {X C : Scheme.{v}} [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  [IsIntegral C] [IsLocallyNoetherian C] [IsNormal C] [CompactSpace C]
  (hC : topologicalKrullDim C = 1) (p : X ⟶ C)
  (hη : ∀ (D : Divisor C) (Z : irreducibleComponents X), p (componentGenericPoint X Z) ∉ D.supp)
  (hcart : ∀ D : Divisor C, D.IsCartier)

include hC in
/-- On a curve the generic point of a prime divisor is a closed point. -/
private theorem isClosed_singleton_genericPoint (Q : MMP.Mori.PrimeDivisor C) :
    IsClosed ({Q.genericPoint} : Set C) :=
  Stacks.AlgebraicGeometry.AmpleDimensionOne.isClosed_singleton_of_ne_genericPoint C hC
    fun h => by
      have h1 := Q.coheight_genericPoint
      rw [h, Order.coheight_eq_zero.mpr fun b _ => (genericPoint_spec C).specializes trivial]
        at h1
      exact zero_ne_one h1

include hC hcart in
/-- **The coefficients of a pull-back from a curve.** If `p(η_E) = η_Q`, the coefficient of
`p^*G` along `E` is `G(Q) · (p^*Q)(E)`. -/
private theorem coeff_isPullback_eq_mul {G : Divisor C} {G' : Divisor X}
    (hG' : G.IsPullback p (hη G) G') (E : MMP.Mori.PrimeDivisor X)
    (Q : MMP.Mori.PrimeDivisor C) (hEQ : p E.genericPoint = Q.genericPoint) :
    G'.coeff E = G.coeff Q *
      (Divisor.pullback (f := p) (Finsupp.single Q 1 : Divisor C) (hcart _) (hη _)).coeff E := by
  classical
  set F : MMP.Mori.PrimeDivisor C → Divisor X := fun Q =>
    Divisor.pullback (f := p) (Finsupp.single Q 1 : Divisor C) (hcart _) (hη _)
  have hF : ∀ Q, Divisor.IsPullback p (Finsupp.single Q 1 : Divisor C) (hη _) (F Q) := fun Q =>
    Divisor.isPullback_pullback (hcart _) (hη _)
  have hGsum : G = ∑ Q ∈ G.support, G Q • (Finsupp.single Q 1 : Divisor C) := by
    refine Finsupp.ext fun Q => ?_
    simp only [Finset.sum_apply', Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul,
      mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · exact (Finsupp.notMem_support_iff.mp h)
  have hpb := (MMP.Fourfold.isPullback_sum_smul_single p hη hcart F hF G.support G).of_eq
    hGsum.symm (hB₂ := hη G)
  have hG'eq : G' = ∑ Q ∈ G.support, G Q • F Q := hG'.eq (hcart G) hpb
  have hcoeff : G'.coeff E = ∑ Q' ∈ G.support, G Q' * (F Q').coeff E := by
    rw [hG'eq]
    simp only [DivisorWithCoeffs.coeff_apply, Finset.sum_apply', Finsupp.smul_apply, smul_eq_mul]
  rw [hcoeff, Finset.sum_eq_single Q]
  · rfl
  · intro Q' _ hQ'
    rw [MMP.Fourfold.coeff_eq_zero_of_isPullback_single p Q'
      (isClosed_singleton_genericPoint hC Q') (hF Q') E fun h => hQ'
        (AlgebraicGeometry.PrimeDivisor.genericPoint_injective (h.symm.trans hEQ)), mul_zero]
  · intro hQ
    rw [Finsupp.notMem_support_iff.mp hQ, zero_mul]

include hC hη hcart in
/-- Over every closed point of the curve there is a prime divisor of `X`. -/
private theorem exists_primeDivisor_genericPoint_eq [Surjective p]
    (Q : MMP.Mori.PrimeDivisor C) :
    ∃ E : MMP.Mori.PrimeDivisor X, p E.genericPoint = Q.genericPoint := by
  obtain ⟨x, hx⟩ := p.surjective Q.genericPoint
  have hF := Divisor.isPullback_pullback (f := p) (hcart (Finsupp.single Q 1 : Divisor C))
    (hη _)
  have hxs := MMP.Fourfold.mem_supp_of_isPullback_single p Q hF hx
  obtain ⟨E, hE, -⟩ := DivisorWithCoeffs.mem_supp_iff.mp hxs
  by_contra h
  push Not at h
  exact hE (MMP.Fourfold.coeff_eq_zero_of_isPullback_single p Q
    (isClosed_singleton_genericPoint hC Q) hF E (h E))

include hη hcart in
/-- `p^*(q B) = q p^*B` for a divisor `B` on `C` and `q ∈ ℚ`. -/
private theorem isPullback_smul_toQDivisor {B : Divisor C} {B' : Divisor X}
    (hB' : B.IsPullback p (hη B) B') (q : ℚ)
    (hBq : ∀ Z : irreducibleComponents X,
      p (componentGenericPoint X Z) ∉ (q • Divisor.toQDivisor B).supp) :
    (q • Divisor.toQDivisor B).IsPullback p hBq (q • Divisor.toQDivisor B') := by
  intro m hm D hD hDc
  refine ⟨D.pullback hDc (hη D), ?_, Divisor.isPullback_pullback hDc (hη D)⟩
  have key : (q.den : ℤ) • D = ((m : ℤ) * q.num) • B := by
    apply Divisor.toQDivisor_injective
    rw [map_zsmul, map_zsmul, hD]
    ext E
    simp only [DivisorWithCoeffs.coeff_smul, zsmul_eq_mul, smul_eq_mul]
    push_cast
    have := Rat.mul_den_eq_num q
    rw [← this]
    ring
  have h1 := (Divisor.isPullback_pullback hDc (hη D)).zsmul hDc (q.den : ℤ) (hη _)
  have h2 := (hB'.zsmul (hcart B) ((m : ℤ) * q.num) (hη _)).of_eq key.symm (hB₂ := hη _)
  have h3 : (q.den : ℤ) • D.pullback hDc (hη D) = ((m : ℤ) * q.num) • B' :=
    h1.eq (hDc.zsmul _) h2
  have h4 := congrArg Divisor.toQDivisor h3
  rw [map_zsmul, map_zsmul] at h4
  ext E
  have h5 := congrArg (fun G : QDivisor X => G.coeff E) h4
  simp only [DivisorWithCoeffs.coeff_smul, zsmul_eq_mul, smul_eq_mul] at h5 ⊢
  push_cast at h5
  have hd : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_pos.ne'
  conv_rhs => rw [← Rat.num_div_den q]
  field_simp
  linear_combination h5

end CurveDivisors

/-! ### Descent to the curve -/

section Descent

variable {k : Type v} [Field k] [IsAlgClosed k] {X : Scheme.{v}} {sX : X ⟶ Spec (.of k)}
  [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X] [CompactSpace X]

/-- **Descent of the pencil to the curve.** Let `Z₁ = div ψ₁ + D` and `Z₂ = div ψ + Z₁` be
effective, `D = m L` Cartier with `L` nef, `F = Z₁ ⊓ Z₂`, and `M_i = Z_i - F` with disjoint
supports, each component of `F` missing `Supp M₁` or `Supp M₂`. Let `p : X ⟶ C` be the
fibration of the free pencil `|M₁|` onto a smooth projective curve with `p_* 𝒪_X = 𝒪_C`, such
that irreducible closed sets missing `Supp M₁` or `Supp M₂` lie in fibres. Then every component
of `Z₁ = M₁ + F` is vertical. For a divisor `G` on `C` with `p^*G ≥ Z₁`, `A = p^*G - Z₁` is
effective and vertical, and `-A ∼ D - p^*G` is `p`-nef since `D` is nef and `p^*G` is trivial on
the fibres; Zariski's lemma
(`MMP.Fourfold.exists_eq_pullback_of_isVertical_of_isRelativelyNef_neg`) gives `A = p^*P`. So
`Z₁ = p^*(G - P)`, `L ∼_ℚ p^*N` with `N = (G - P)/m`, and `G - P` is effective and nonzero, hence
ample on the curve. -/
private theorem exists_pullback_of_pencil (hX : MMP.Mori.IsProjectiveVariety k sX)
    (hQ : MMP.Fourfold.IsQFactorial sX) {L : QDivisor X} (hL : L.IsNef k sX) {m : ℕ}
    (hm : 0 < m) {D : Divisor X} (hDc : D.IsCartier) (hDL : Divisor.toQDivisor D = (m : ℤ) • L)
    {Z₁ Z₂ : Divisor X} (hZ₁ : 0 ≤ Z₁) (hZ₂ : 0 ≤ Z₂) (ψ₁ ψ : (RationalFunctions X)ˣ)
    (hψ₁ : Z₁ = principalDivisor ψ₁ + D) (hψ : Z₂ = principalDivisor ψ + Z₁)
    (hne : Z₁ - Z₁ ⊓ Z₂ ≠ 0)
    (hdisj : Disjoint ((Z₁ - Z₁ ⊓ Z₂).supp : Set X) (Z₂ - Z₁ ⊓ Z₂).supp)
    (hF : ∀ E : MMP.Mori.PrimeDivisor X, (Z₁ ⊓ Z₂) E ≠ 0 →
      Disjoint (E.support : Set X) (Z₁ - Z₁ ⊓ Z₂).supp ∨
        Disjoint (E.support : Set X) (Z₂ - Z₁ ⊓ Z₂).supp)
    {C : Scheme.{v}} [IsLocallyNoetherian C] [IsNormal C] [CompactSpace C]
    (sC : C ⟶ Spec (.of k)) (hC : MMP.Mori.IsProjectiveVariety k sC)
    (hdimC : topologicalKrullDim C = 1) (hCsm : IsSmoothScheme sC) (p : X ⟶ C) (hps : p ≫ sC = sX)
    (hp : ∀ U : C.Opens, IsIso (p.app U)) [Surjective p] (hpp : IsProjectiveMorphism p)
    (hvert₁ : ∀ T : Set X, IsIrreducible T → IsClosed T →
      Disjoint T (Z₁ - Z₁ ⊓ Z₂).supp → (p '' T).Subsingleton)
    (hvert₂ : ∀ T : Set X, IsIrreducible T → IsClosed T →
      Disjoint T (Z₂ - Z₁ ⊓ Z₂).supp → (p '' T).Subsingleton) :
    ∃ (N : QDivisor C) (hN : N.IsQCartier) (n : ℕ) (_ : 0 < n) (A : Divisor C)
      (_ : Divisor.toQDivisor A = (n : ℚ) • N) (hAc : A.IsCartier) (_ : A.IsAmple hAc),
      ∃ hB : ∀ Z : irreducibleComponents X, p (componentGenericPoint X Z) ∉ N.supp,
        L.QLinearlyEquivalent (N.pullback hN hB) := by
  classical
  have := hC.toIsIntegral
  have : IsProper sX := isProper_of_isProjectiveMorphism sX hX.isProjective
  have : IsProper p := (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mp hpp).2
  set F := Z₁ ⊓ Z₂ with hFdef
  set M₁ := Z₁ - F with hM₁def
  set M₂ := Z₂ - F with hM₂def
  -- `p` maps the generic point of `X` to that of `C`
  have hgenX : ∀ Z : irreducibleComponents X, p (componentGenericPoint X Z) = genericPoint C := by
    intro Z
    have hZ : Z.1 = Set.univ := by
      have h : Z.1 ∈ ({Set.univ} : Set (Set X)) :=
        (irreducibleComponents_eq_singleton (X := X)) ▸ Z.2
      exact h
    have hgp := isGenericPoint_componentGenericPoint X Z
    rw [hZ] at hgp
    refine IsGenericPoint.eq ?_ (genericPoint_spec C)
    refine Set.eq_univ_of_forall fun y => ?_
    obtain ⟨x, rfl⟩ := p.surjective y
    have hx : x ∈ closure {componentGenericPoint X Z} := by rw [hgp.def]; trivial
    have := image_closure_subset_closure_image p.continuous ⟨x, hx, rfl⟩
    rwa [Set.image_singleton] at this
  have hη : ∀ (G : Divisor C) (Z : irreducibleComponents X),
      p (componentGenericPoint X Z) ∉ G.supp := fun G Z => by
    rw [hgenX]; exact MMP.Fourfold.genericPoint_notMem_supp G
  have hcart : ∀ G : Divisor C, G.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hCsm
  have hmemη : ∀ E : MMP.Mori.PrimeDivisor X, E.genericPoint ∈ (E.support : Set X) := fun E => by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  have hsub : ∀ (G : Divisor X) (E : MMP.Mori.PrimeDivisor X), G E ≠ 0 →
      (E.support : Set X) ⊆ G.supp := fun G E hG x hx =>
    DivisorWithCoeffs.mem_supp_iff.mpr ⟨E, hG, hx⟩
  have hF0 : 0 ≤ F := le_inf hZ₁ hZ₂
  -- the components of `Z₁` are vertical
  have hvertZ : ∀ E : MMP.Mori.PrimeDivisor X, Z₁ E ≠ 0 →
      (p '' (E.support : Set X)).Subsingleton := by
    intro E hE
    have hirr : IsIrreducible (E.support : Set X) := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact isIrreducible_singleton.closure
    have hcl : IsClosed (E.support : Set X) := E.idealSheaf.support.isClosed
    by_cases hM : M₁ E = 0
    · have hFE : F E ≠ 0 := by
        intro h0
        apply hE
        have : M₁ E = Z₁ E - F E := rfl
        omega
      rcases hF E hFE with h | h
      · exact hvert₁ _ hirr hcl h
      · exact hvert₂ _ hirr hcl h
    · exact hvert₂ _ hirr hcl (hdisj.mono_left (hsub M₁ E hM))
  have hvertpt : ∀ E : MMP.Mori.PrimeDivisor X, Z₁ E ≠ 0 →
      ∀ x ∈ (E.support : Set X), p x = p E.genericPoint := fun E hE x hx =>
    hvertZ E hE ⟨x, hx, rfl⟩ ⟨_, hmemη E, rfl⟩
  have hnotgen : ∀ E : MMP.Mori.PrimeDivisor X, Z₁ E ≠ 0 → p E.genericPoint ≠ genericPoint C := by
    intro E hE h
    have himg : p '' (E.support : Set X) = {p E.genericPoint} := by
      refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨E.genericPoint, hmemη E, rfl⟩, ?_⟩
      rintro _ ⟨x, hx, rfl⟩; exact hvertpt E hE x hx
    have hcl := p.isClosedMap _ E.idealSheaf.support.isClosed
    change IsClosed (p '' (E.support : Set X)) at hcl
    rw [himg, h] at hcl
    exact MMP.Fourfold.not_isClosed_genericPoint hdimC hcl
  -- the points of `C` below the components of `Z₁`, and a pull-back `G' = p^*G ≥ Z₁`
  set T : Set (MMP.Mori.PrimeDivisor C) :=
    {Q | ∃ E, Z₁ E ≠ 0 ∧ p E.genericPoint = Q.genericPoint}
  have hT : T.Finite :=
    ((Z₁.support.finite_toSet.image fun E => p E.genericPoint).preimage
      AlgebraicGeometry.PrimeDivisor.genericPoint_injective.injOn).subset
      fun Q ⟨E, hE, h⟩ => ⟨E, Finsupp.mem_support_iff.mpr hE, h⟩
  set K : ℤ := ∑ E ∈ Z₁.support, Z₁ E
  have hK : ∀ E, Z₁ E ≤ K := fun E => by
    by_cases hE : E ∈ Z₁.support
    · exact Finset.single_le_sum (f := ⇑Z₁) (fun E _ => hZ₁ E) hE
    · rw [Finsupp.notMem_support_iff.mp hE]
      exact Finset.sum_nonneg fun E _ => hZ₁ E
  set G : Divisor C := ∑ Q ∈ hT.toFinset, Finsupp.single Q K
  have hG : ∀ Q, G Q = if Q ∈ T then K else 0 := by
    intro Q
    simp only [G, Finset.sum_apply', Finsupp.single_apply]
    rw [Finset.sum_ite_eq']
    simp
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun E _ => hZ₁ E
  have hG0 : 0 ≤ G := fun Q => by
    change (0 : ℤ) ≤ G Q
    rw [hG]; split_ifs <;> omega
  set G' := G.pullback (hcart G) (hη G) with hG'def
  have hG' : G.IsPullback p (hη G) G' := Divisor.isPullback_pullback (hcart G) (hη G)
  have hFpos : ∀ (Q : MMP.Mori.PrimeDivisor C) (E : MMP.Mori.PrimeDivisor X),
      p E.genericPoint = Q.genericPoint →
      0 < (Divisor.pullback (f := p) (Finsupp.single Q 1 : Divisor C) (hcart _) (hη _)).coeff E :=
    fun Q E hE => MMP.Fourfold.coeff_pos_of_isPullback_single p Q
      (Divisor.isPullback_pullback (hcart _) (hη _)) E hE
  have hGZ : ∀ E, Z₁ E ≤ G' E := by
    intro E
    by_cases hE : Z₁ E = 0
    · rw [hE]
      exact (MMP.Fourfold.coeff_isPullback_nonneg_and_eq_zero hdimC p hη hcart hG' E).1
        fun Q _ => hG0 Q
    · set Q := AlgebraicGeometry.PrimeDivisor.ofCoheightOne (p E.genericPoint)
        (MMP.Fourfold.coheight_eq_one_of_ne_genericPoint hdimC (hnotgen E hE))
      have hQ : Q.genericPoint = p E.genericPoint :=
        AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
      have hQT : Q ∈ T := ⟨E, hE, hQ.symm⟩
      have h1 := coeff_isPullback_eq_mul hdimC p hη hcart hG' E Q hQ.symm
      have h2 := hFpos Q E hQ.symm
      rw [DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.coeff_apply, hG, if_pos hQT] at h1
      rw [h1]
      have := hK E
      nlinarith
  -- `A = p^*G - Z₁` is effective, vertical, and `-A` is `p`-nef
  set A : QDivisor X := Divisor.toQDivisor G' - Divisor.toQDivisor Z₁ with hAdef
  have hAcoeff : ∀ E, A E = (G' E : ℚ) - (Z₁ E : ℚ) := fun E => by
    simp only [A, Finsupp.coe_sub, Pi.sub_apply]
    rw [toQDivisor_apply, toQDivisor_apply]
  have hA0 : 0 ≤ A := fun E => by
    change (0 : ℚ) ≤ A E
    rw [hAcoeff]
    have := hGZ E
    have : ((Z₁ E : ℤ) : ℚ) ≤ (G' E : ℚ) := by exact_mod_cast this
    linarith
  have hAv : MMP.Fourfold.QDivisor.IsVertical p A := by
    intro E hE x hx
    by_cases hZ : Z₁ E = 0
    · have hG'E : G'.coeff E ≠ 0 := by
        intro h
        apply hE
        rw [hAcoeff, hZ, ← DivisorWithCoeffs.coeff_apply, h]
        simp
      by_contra hne'
      have hall : ∀ Q : MMP.Mori.PrimeDivisor C, p E.genericPoint = Q.genericPoint →
          G.coeff Q = 0 := by
        intro Q hQ
        exfalso
        apply hne'
        have hx' : E.genericPoint ⤳ x := by
          rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hx
          exact specializes_iff_mem_closure.mpr hx
        have h2 := hx'.map p.continuous
        rw [hQ] at h2
        have h3 := specializes_iff_mem_closure.mp h2
        rw [(isClosed_singleton_genericPoint hdimC Q).closure_eq] at h3
        rw [h3, hQ]
      exact hG'E ((MMP.Fourfold.coeff_isPullback_nonneg_and_eq_zero hdimC p hη hcart hG' E).2 hall)
    · exact hvertpt E hZ x hx
  have hnef : (-A).IsRelativelyNef sX p := by
    have hAq := MMP.Fourfold.isQCartier_of_isQFactorial sX hQ (-A)
    refine MMP.Fourfold.QDivisor.isRelativelyNef_of_intersectionNumber_nonneg sX hAq
      fun γ hγ => ?_
    set R : Divisor X := principalDivisor ψ₁ - G'
    have hdecomp : -A = Divisor.toQDivisor D + Divisor.toQDivisor R := by
      rw [hAdef, hψ₁]
      simp only [R, map_add, map_sub]
      abel
    have hDq := QDivisor.isQCartier_toQDivisor hDc
    have hRq := MMP.Fourfold.isQCartier_of_isQFactorial sX hQ (Divisor.toQDivisor R)
    rw [MMP.Fourfold.intersectionNumber_congr sX γ.ι γ.dim_le hAq (hDq.add hRq) hdecomp,
      QDivisor.intersectionNumber_add' k sX γ.ι γ.dim_le _ _ hDq hRq]
    have hloc : ∀ z : C, ∃ U : C.Opens, z ∈ U ∧ ∃ ψ : (RationalFunctions X)ˣ,
        R.IsLocalEquation (p ⁻¹ᵁ U) ψ := by
      intro z
      obtain ⟨U, hzU, φ, hφ⟩ := hcart G z
      obtain ⟨ψ, hψ, -⟩ := MMP.Fourfold.exists_isLocalEquation_of_isPullback p (hη G) hG' hφ
      refine ⟨U, hzU, ψ₁ * ψ⁻¹, fun E hE => ?_⟩
      rw [DivisorWithCoeffs.coeff_sub, hψ E hE, coeff_principalDivisor,
        MMP.Mori.PrimeDivisor.ord_mul, MMP.Mori.PrimeDivisor.ord_inv]
      ring
    have hR0 := MMP.Fourfold.intersectionNumber_eq_zero_of_isLocalEquation_preimage sX hQ p hRq
      (N := 1) one_pos (L := R) (by simp) hloc γ hγ
    rw [hR0, add_zero]
    obtain ⟨hL', hLn⟩ := hL
    have hLγ := hLn γ.scheme γ.ι γ.dim_eq
    have hDL' : Divisor.toQDivisor D = (m : ℚ) • L := by
      rw [hDL, ← Int.cast_smul_eq_zsmul ℚ]; push_cast; rfl
    rw [MMP.Fourfold.intersectionNumber_congr sX γ.ι γ.dim_le hDq (hDL' ▸ hDq) hDL',
      MMP.Fourfold.intersectionNumber_smul sX γ.ι γ.dim_le L hL' (m : ℚ) (hDL' ▸ hDq)]
    exact mul_nonneg (by positivity) hLγ
  -- Zariski's lemma: `A = p^*P`
  have hCcurve : MMP.Mori.IsCurve k sC := (MMP.Mori.isCurve_iff k sC).mpr ⟨hC.toIsVariety, hdimC⟩
  obtain ⟨P, hP, hPB, -, hAP⟩ :=
    MMP.Fourfold.exists_eq_pullback_of_isVertical_of_isRelativelyNef_neg sX sC hQ hX hCcurve
      hCsm p hpp hp A hA0 hAv hnef
  obtain ⟨N₀, hN₀, P₀, hP₀⟩ := MMP.Flips.exists_pos_smul_eq_toQDivisor P
  obtain ⟨D', hD', hD'pb⟩ := QDivisor.isPullback_pullback hP hPB N₀ hN₀ P₀ hP₀ (hcart P₀)
  -- `Z₁` is the pull-back of `B = N₀ G - P₀` divided by `N₀`
  set B : Divisor C := (N₀ : ℤ) • G + (-1 : ℤ) • P₀
  have hBpb0 : B.IsPullback p (hη B) ((N₀ : ℤ) • G' + (-1 : ℤ) • D') :=
    Divisor.IsPullback.add (hcart _) (hcart _) (hη _) (hG'.zsmul (hcart G) N₀ (hη _))
      (hD'pb.zsmul (hcart P₀) (-1) (hη _))
  have hBZ : (N₀ : ℤ) • G' + (-1 : ℤ) • D' = (N₀ : ℤ) • Z₁ := by
    apply Divisor.toQDivisor_injective
    rw [map_add, map_zsmul, map_zsmul, map_zsmul, hD', ← hAP, hAdef]
    simp only [smul_sub, neg_one_smul]
    abel
  have hBpb : B.IsPullback p (hη B) ((N₀ : ℤ) • Z₁) := hBZ ▸ hBpb0
  set n : ℕ := N₀ * m
  have hn : 0 < n := Nat.mul_pos hN₀ hm
  set N : QDivisor C := ((n : ℚ)⁻¹) • Divisor.toQDivisor B
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hNB : Divisor.toQDivisor B = (n : ℚ) • N := by
    simp only [N, smul_smul, mul_inv_cancel₀ hnq, one_smul]
  have hN : N.IsQCartier :=
    ⟨n, by exact_mod_cast hn.ne', B, by rw [hNB, ← Int.cast_smul_eq_zsmul ℚ]; push_cast; rfl,
      hcart B⟩
  have hB : ∀ Z : irreducibleComponents X, p (componentGenericPoint X Z) ∉ N.supp := fun Z => by
    rw [hgenX]; exact MMP.Fourfold.genericPoint_notMem_supp N
  have hNpb : N.pullback hN hB = ((n : ℚ)⁻¹) • Divisor.toQDivisor ((N₀ : ℤ) • Z₁) :=
    QDivisor.IsPullback.pullback_eq hN (isPullback_smul_toQDivisor p hη hcart hBpb _ hB)
  -- `B` is effective and nonzero, hence ample
  have hB0 : 0 ≤ B := by
    intro Q
    change (0 : ℤ) ≤ B Q
    obtain ⟨E, hE⟩ := exists_primeDivisor_genericPoint_eq hdimC p hη hcart Q
    have h1 := coeff_isPullback_eq_mul hdimC p hη hcart hBpb E Q hE
    have h2 := hFpos Q E hE
    have h3 : (0 : ℤ) ≤ ((N₀ : ℤ) • Z₁).coeff E := by
      rw [DivisorWithCoeffs.coeff_smul, smul_eq_mul]
      exact mul_nonneg (by positivity) (hZ₁ E)
    rw [h1] at h3
    exact (mul_nonneg_iff_of_pos_right h2).mp h3
  have hBne : B ≠ 0 := by
    intro hB0'
    obtain ⟨E₀, hE₀⟩ := DFunLike.ne_iff.mp hne
    have hZE : Z₁ E₀ ≠ 0 := by
      intro h0
      apply hE₀
      have h1 := hF0 E₀
      have h2 : F E₀ ≤ Z₁ E₀ := (inf_le_left : F ≤ Z₁) E₀
      change Z₁ E₀ - F E₀ = 0
      change (0 : ℤ) ≤ F E₀ at h1
      omega
    have := (MMP.Fourfold.coeff_isPullback_nonneg_and_eq_zero hdimC p hη hcart hBpb E₀).2
      fun Q _ => by rw [hB0']; rfl
    rw [DivisorWithCoeffs.coeff_smul, smul_eq_mul] at this
    rcases mul_eq_zero.mp this with h | h
    · exact (by exact_mod_cast hN₀.ne' : (N₀ : ℤ) ≠ 0) h
    · exact hZE h
  refine ⟨N, hN, n, hn, B, hNB, hcart B,
    isAmple_of_nonneg_of_ne_zero sC hC hdimC B (hcart B) hB0 hBne, hB, ?_⟩
  -- `L ∼_ℚ (1/m) Z₁ = p^*N`
  rw [hNpb]
  refine ⟨m, hm, ψ₁⁻¹, ?_⟩
  ext E
  have h1 := congrArg (fun G : QDivisor X => G.coeff E) hDL
  have h2 := congrArg (fun G : Divisor X => G.coeff E) hψ₁
  simp only [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_sub, Divisor.coeff_toQDivisor,
    coeff_principalDivisor, MMP.Mori.PrimeDivisor.ord_inv, DivisorWithCoeffs.coeff_add,
    zsmul_eq_mul, smul_eq_mul] at h1 h2 ⊢
  push_cast at h1 h2 ⊢
  have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hN₀q : (N₀ : ℚ) ≠ 0 := by exact_mod_cast hN₀.ne'
  simp only [n]
  push_cast
  field_simp
  rw [h2] at *
  push_cast
  rw [h1]
  ring

end Descent

/-! ### A base point of the pencil, topologically -/

section Topo

open Set Topology TopologicalSpace

/-- A point in the closure of `A \ A'` lifts along a closed map `μ` to a point outside
`(σ ∘ p)⁻¹' V`, when a section `γ` of `μ` off `U ⊇ A \ A'` sends `x` into `(σ ∘ p)⁻¹' V` exactly
when `x ∉ A`. -/
private theorem exists_preimage_notMem_of_mem_closure_diff {X Xt Xp P : Type*}
    [TopologicalSpace X] [TopologicalSpace Xt] [TopologicalSpace Xp] [TopologicalSpace P]
    {μ : Xt → X} (hμ : IsClosedMap μ) {p : Xt → Xp} (hpc : Continuous p) {σ : Xp → P}
    (hσ : Continuous σ) {γ : X → Xt} {U : Set X} (hγμ : ∀ x, x ∉ U → μ (γ x) = x)
    {V : Set P} {A A' : Set X} (hVo : IsOpen V) (hγV : ∀ x, x ∉ U → (σ (p (γ x)) ∈ V ↔ x ∉ A))
    (hsub : A \ A' ⊆ Uᶜ) {b : X} (hbA : b ∈ closure (A \ A')) :
    ∃ y, μ y = b ∧ σ (p y) ∉ V := by
  have hsub' : A \ A' ⊆ μ '' ((σ ∘ p) ⁻¹' Vᶜ) := by
    intro x hx
    refine ⟨γ x, ?_, hγμ x (hsub hx)⟩
    change σ (p (γ x)) ∉ V
    rw [hγV x (hsub hx)]
    exact not_not.mpr hx.1
  obtain ⟨y, hyW, hyb⟩ :=
    closure_minimal hsub' (hμ _ (hVo.isClosed_compl.preimage (hσ.comp hpc))) hbA
  exact ⟨y, hyb, hyW⟩

/-- A closed point in the closures of both `A₀ \ A₁` and `A₁ \ A₀` lies under every fibre
of `p`. -/
private theorem mem_image_preimage_of_mem_closure_diff {X Xt Xp P : Type*} [TopologicalSpace X]
    [TopologicalSpace Xt] [TopologicalSpace Xp] [TopologicalSpace P]
    (μ : Xt → X) (hμc : Continuous μ) (hμ : IsClosedMap μ)
    (p : Xt → Xp) (hpc : Continuous p) (hp : IsClosedMap p) (σ : Xp → P) (hσ : Continuous σ)
    (A₀ A₁ : Set X) (V₀ V₁ : Set P) (hV₀o : IsOpen V₀) (hV₁o : IsOpen V₁)
    (hV : V₀ ∪ V₁ = univ)
    (γ : X → Xt) (hγμ : ∀ x, x ∉ A₀ ∩ A₁ → μ (γ x) = x)
    (hγV₀ : ∀ x, x ∉ A₀ ∩ A₁ → (σ (p (γ x)) ∈ V₀ ↔ x ∉ A₀))
    (hγV₁ : ∀ x, x ∉ A₀ ∩ A₁ → (σ (p (γ x)) ∈ V₁ ↔ x ∉ A₁))
    (hXp : ∀ S : Set Xp, IsClosed S → IsPreconnected S → S ≠ univ → S.Subsingleton)
    (hμf : ∀ x, IsPreconnected (μ ⁻¹' {x}))
    (b : X) (hb : IsClosed ({b} : Set X)) (hb₀ : b ∈ closure (A₀ \ A₁))
    (hb₁ : b ∈ closure (A₁ \ A₀)) (c : Xp) : b ∈ μ '' (p ⁻¹' {c}) := by
  obtain ⟨y₀, hy₀b, hy₀⟩ := exists_preimage_notMem_of_mem_closure_diff hμ hpc hσ hγμ hV₁o
    hγV₁ (fun x hx h => hx.2 h.1) hb₁
  obtain ⟨y₁, hy₁b, hy₁⟩ := exists_preimage_notMem_of_mem_closure_diff hμ hpc hσ hγμ hV₀o
    hγV₀ (fun x hx h => hx.2 h.2) hb₀
  have hne : p y₀ ≠ p y₁ := by
    intro h
    rcases (hV ▸ Set.mem_univ _ : σ (p y₀) ∈ V₀ ∪ V₁) with h0 | h1
    · exact hy₁ (h ▸ h0)
    · exact hy₀ h1
  have hSuniv : p '' (μ ⁻¹' {b}) = univ := by
    by_contra hS
    exact hne (hXp _ (hp _ (hb.preimage hμc)) ((hμf b).image p hpc.continuousOn) hS
      ⟨y₀, hy₀b, rfl⟩ ⟨y₁, hy₁b, rfl⟩)
  obtain ⟨y, hyb, hyc⟩ := (hSuniv.symm ▸ Set.mem_univ c : c ∈ p '' (μ ⁻¹' {b}))
  exact ⟨y, hyc, hyb⟩

/-- **The base-point argument, topologically.** Let `μ : X̃ → X` be closed with preconnected
fibres and a section `γ` off `A₀ ∩ A₁`, and `p : X̃ → X'` closed with preconnected fibres onto a
space whose proper closed preconnected subsets are subsingletons, followed by `σ : X' → P` with
`P = V₀ ∪ V₁` and `σ ∘ p ∘ γ ∈ V_i` exactly off `A_i`. If a closed preconnected `D ≠ ∅` lies in
`A₁ \ A₀` with `A₁ ⊆ D ⊔ B`, `B` closed, and `A₁ ≠ X`, then no closed point lies in the
closures of both `A₀ \ A₁` and `A₁ \ A₀`. -/
private theorem false_of_mem_closure_diff_of_mem_closure_diff {X Xt Xp P : Type*}
    [TopologicalSpace X] [TopologicalSpace Xt] [TopologicalSpace Xp] [TopologicalSpace P]
    (μ : Xt → X) (hμc : Continuous μ) (hμ : IsClosedMap μ)
    (p : Xt → Xp) (hpc : Continuous p) (hp : IsClosedMap p) (σ : Xp → P) (hσ : Continuous σ)
    (A₀ A₁ : Set X) (hA₀ : IsClosed A₀) (V₀ V₁ : Set P) (hV₀o : IsOpen V₀) (hV₁o : IsOpen V₁)
    (hV : V₀ ∪ V₁ = univ)
    (γ : X → Xt) (hγμ : ∀ x, x ∉ A₀ ∩ A₁ → μ (γ x) = x)
    (hγ : ∀ y, μ y ∉ A₀ ∩ A₁ → y = γ (μ y))
    (hγc : ContinuousOn γ (A₀ ∩ A₁)ᶜ)
    (hγV₀ : ∀ x, x ∉ A₀ ∩ A₁ → (σ (p (γ x)) ∈ V₀ ↔ x ∉ A₀))
    (hγV₁ : ∀ x, x ∉ A₀ ∩ A₁ → (σ (p (γ x)) ∈ V₁ ↔ x ∉ A₁))
    (hXp : ∀ S : Set Xp, IsClosed S → IsPreconnected S → S ≠ univ → S.Subsingleton)
    (hpf : ∀ c, IsPreconnected (p ⁻¹' {c}))
    (hμf : ∀ x, IsPreconnected (μ ⁻¹' {x}))
    (D B : Set X) (hD : IsClosed D) (hDc : IsPreconnected D) (hDne : D.Nonempty)
    (hB : IsClosed B) (hDB : Disjoint D B) (hDA₀ : Disjoint D A₀) (hDA₁ : D ⊆ A₁)
    (hA₁DB : A₁ ⊆ D ∪ B) (x₁ : X) (hx₁ : x₁ ∉ A₁)
    (b : X) (hb : IsClosed ({b} : Set X)) (hb₀ : b ∈ closure (A₀ \ A₁))
    (hb₁ : b ∈ closure (A₁ \ A₀)) : False := by
  have hDU : D ⊆ (A₀ ∩ A₁)ᶜ := fun d hd h => Set.disjoint_left.mp hDA₀ hd h.1
  have hpre : μ ⁻¹' D = γ '' D := by
    ext y
    refine ⟨fun hy => ⟨μ y, hy, (hγ y (hDU hy)).symm⟩, ?_⟩
    rintro ⟨d, hd, rfl⟩
    rwa [Set.mem_preimage, hγμ d (hDU hd)]
  set S₀ := p '' (γ '' D) with hS₀
  have hS₀c : IsClosed S₀ := by
    rw [hS₀, ← hpre]
    exact hp _ (hD.preimage hμc)
  have hS₀p : IsPreconnected S₀ :=
    (hDc.image γ (hγc.mono hDU)).image p hpc.continuousOn
  have hd1 : ∀ d ∈ D, σ (p (γ d)) ∉ V₁ := fun d hd h =>
    ((hγV₁ d (hDU hd)).mp h) (hDA₁ hd)
  have hx₁U : x₁ ∉ A₀ ∩ A₁ := fun h => hx₁ h.2
  have hS₀ne : S₀ ≠ univ := by
    intro h
    obtain ⟨_, ⟨d, hd, rfl⟩, hdx⟩ := (h.symm ▸ Set.mem_univ (p (γ x₁)) : p (γ x₁) ∈ S₀)
    exact hd1 d hd (hdx ▸ (hγV₁ x₁ hx₁U).mpr hx₁)
  obtain ⟨d₀, hd₀⟩ := hDne
  set c := p (γ d₀) with hc
  have hS₀eq : S₀ = {c} := by
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨γ d₀, ⟨d₀, hd₀, rfl⟩, rfl⟩, fun z hz => ?_⟩
    exact hXp S₀ hS₀c hS₀p hS₀ne hz ⟨γ d₀, ⟨d₀, hd₀, rfl⟩, rfl⟩
  have hcc : IsClosed ({c} : Set Xp) := hS₀eq ▸ hS₀c
  have hσc : σ c ∉ V₁ := hd1 d₀ hd₀
  set T := μ '' (p ⁻¹' {c}) with hT
  have hTp : IsPreconnected T := (hpf c).image μ hμc.continuousOn
  have hDT : D ⊆ T := by
    intro d hd
    refine ⟨γ d, ?_, hγμ d (hDU hd)⟩
    have : p (γ d) ∈ S₀ := ⟨γ d, ⟨d, hd, rfl⟩, rfl⟩
    rwa [hS₀eq] at this
  have hTA₁ : T ⊆ A₁ := by
    rintro _ ⟨y, hy, rfl⟩
    by_contra hyA
    have hU : μ y ∉ A₀ ∩ A₁ := fun h => hyA h.2
    have h1 := (hγV₁ (μ y) hU).mpr hyA
    rw [← hγ y hU, show p y = c from hy] at h1
    exact hσc h1
  have hbT : b ∈ T := mem_image_preimage_of_mem_closure_diff μ hμc hμ p hpc hp σ hσ A₀ A₁
    V₀ V₁ hV₀o hV₁o hV γ hγμ hγV₀ hγV₁ hXp hμf b hb hb₀ hb₁ c
  have hbA₀ : b ∈ A₀ := closure_minimal Set.diff_subset hA₀ hb₀
  have hbD : b ∉ D := fun h => Set.disjoint_left.mp hDA₀ h hbA₀
  have hTDB : T ⊆ D ∪ B := hTA₁.trans hA₁DB
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hTp) D B hD hB hTDB
      (by rw [Set.disjoint_iff_inter_eq_empty.mp hDB, Set.inter_empty]) with h | h
  · exact hbD (h hbT)
  · exact Set.disjoint_left.mp hDB hd₀ (h (hDT hd₀))

/-- In an irreducible T0 space of dimension at most one, every point of a proper closed subset
is closed. -/
private theorem closure_singleton_eq_of_mem_of_ne_univ {Y : Type*} [TopologicalSpace Y]
    [IrreducibleSpace Y] [T0Space Y] (hdim : topologicalKrullDim Y ≤ 1) {S : Set Y}
    (hS : IsClosed S) (hne : S ≠ univ) {s : Y} (hs : s ∈ S) : closure ({s} : Set Y) = {s} := by
  have hsub : closure ({s} : Set Y) ⊆ S := closure_minimal (singleton_subset_iff.2 hs) hS
  refine Set.Subset.antisymm (fun t ht => ?_) subset_closure
  by_contra hts
  have hts' : t ≠ s := hts
  let Zt : IrreducibleCloseds Y :=
    ⟨closure {t}, isIrreducible_singleton.closure, isClosed_closure⟩
  let Zs : IrreducibleCloseds Y :=
    ⟨closure {s}, isIrreducible_singleton.closure, isClosed_closure⟩
  let Zu : IrreducibleCloseds Y := ⟨univ, IrreducibleSpace.isIrreducible_univ Y, isClosed_univ⟩
  have h1 : Zt < Zs := by
    refine lt_of_le_of_ne ?_ fun h => hts' ?_
    · change closure {t} ⊆ closure {s}
      exact closure_minimal (singleton_subset_iff.2 ht) isClosed_closure
    · have : closure ({t} : Set Y) = closure {s} :=
        congrArg (fun Z : IrreducibleCloseds Y => (Z : Set Y)) h
      exact (inseparable_iff_closure_eq.mpr this).eq
  have h2 : Zs < Zu := by
    refine lt_of_le_of_ne (fun _ _ => mem_univ _) fun h => hne ?_
    have : closure ({s} : Set Y) = univ :=
      congrArg (fun Z : IrreducibleCloseds Y => (Z : Set Y)) h
    exact Set.eq_univ_of_univ_subset (this ▸ hsub)
  let l : LTSeries (IrreducibleCloseds Y) :=
    ⟨2, ![Zt, Zs, Zu], fun i => by fin_cases i <;> simp [h1, h2]⟩
  have h3 : ((2 : ℕ) : WithBot ℕ∞) ≤ 1 := (Order.LTSeries.length_le_krullDim l).trans hdim
  exact absurd h3 (by decide)

private theorem subsingleton_of_isClosed_of_isPreconnected {Y : Type*} [TopologicalSpace Y]
    [NoetherianSpace Y] [IrreducibleSpace Y] [QuasiSober Y] [T0Space Y]
    (hdim : topologicalKrullDim Y ≤ 1) (S : Set Y) (hS : IsClosed S) (hSp : IsPreconnected S)
    (hne : S ≠ univ) : S.Subsingleton := by
  have hpt : ∀ s ∈ S, closure ({s} : Set Y) = {s} := fun s hs =>
    closure_singleton_eq_of_mem_of_ne_univ hdim hS hne hs
  obtain ⟨T, hTf, hTc, hTi, hST⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hS
  have hfin : S.Finite := by
    have : S ⊆ ⋃ t ∈ T, t := by rw [hST, Set.sUnion_eq_biUnion]
    refine Set.Finite.subset (hTf.biUnion fun t ht => ?_) this
    obtain ⟨η, hη⟩ := QuasiSober.sober (hTi t ht) (hTc t ht)
    have hηS : η ∈ S := by
      rw [hST]; exact ⟨t, ht, hη.mem⟩
    rw [← hη.def, hpt η hηS]
    exact Set.finite_singleton η
  intro a ha c hc
  by_contra hac
  have hA : IsClosed ({a} : Set Y) := by rw [← hpt a ha]; exact isClosed_closure
  have hB : IsClosed (S \ {a}) := by
    have : S \ {a} = ⋃ x ∈ (hfin.diff (t := {a})).toFinset, ({x} : Set Y) := by
      ext y; simp
    rw [this]
    exact isClosed_biUnion_finset fun x hx => by
      rw [Set.Finite.mem_toFinset] at hx
      rw [← hpt x hx.1]; exact isClosed_closure
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hSp) {a} (S \ {a}) hA hB
      (fun y hy => by by_cases h : y = a <;> simp_all)
      (by ext y; simp) with h | h
  · exact hac (h hc).symm
  · exact (h ha).2 rfl

end Topo

/-! ### A pencil whose moving parts meet -/

section BasePoint

open CategoryTheory.Limits Stacks.ProjectiveFromSections Stacks.ProjectiveSpaceModuli
open Stacks.NonvanishingOpen (nonvanishingOpen)

private theorem exists_pencilMap {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] (s₀ s₁ : Γ(L, ⊤)) (U : X.Opens)
    (hU : U = nonvanishingOpen X L s₀ ⊔ nonvanishingOpen X L s₁) :
    ∃ φ : U.toScheme ⟶ projectiveSpaceOver 1 (Spec (.of k)),
      φ ≫ pullback.fst (terminal.from (Spec (.of k)))
          (terminal.from (projectiveSpaceAtUniverse.{u} 1)) = U.ι ≫ sX ∧
      ∀ u : U.toScheme,
        (φ u ∈ projectiveSpaceOver.standardChart 1 (Spec (.of k)) 0 ↔
          u.1 ∈ Stacks.Ample.nonvanishingLocus L s₀) ∧
        (φ u ∈ projectiveSpaceOver.standardChart 1 (Spec (.of k)) 1 ↔
          u.1 ∈ Stacks.Ample.nonvanishingLocus L s₁) := by
  classical
  set L' := (Scheme.Modules.pullback U.ι).obj L
  set s : Fin 2 → Γ(L', ⊤) := ![pullbackGlobalSections U.ι L s₀, pullbackGlobalSections U.ι L s₁]
    with hs
  have hnv : ∀ (i : Fin 2) (u : U.toScheme), u ∈ nvCover s i ↔
      u.1 ∈ Stacks.Ample.nonvanishingLocus L (![s₀, s₁] i) := by
    intro i u
    have h :=
      Stacks.AlgebraicGeometry.GeneratingSectionsRestrict.nonvanishingOpen_pullbackGlobalSections
      U.ι L (![s₀, s₁] i)
    have hsi : s i = pullbackGlobalSections U.ι L (![s₀, s₁] i) := by
      fin_cases i <;> rfl
    change u ∈ Stacks.Ample.nonvanishingLocus L' (s i) ↔ _
    rw [hsi]
    change u ∈ (nonvanishingOpen U.toScheme L' (pullbackGlobalSections U.ι L (![s₀, s₁] i)) :
      Set U.toScheme) ↔ _
    rw [h]
    rfl
  have hgen : GeneratesStalks s :=
    Stacks.AmpleImmersionReduction.generatesStalks_of_forall_exists_mem _ fun u => by
      have hu : (u.1 : X) ∈ (nonvanishingOpen X L s₀ ⊔ nonvanishingOpen X L s₁ : X.Opens) := by
        simpa only [hU] using u.2
      rcases (TopologicalSpace.Opens.mem_sup).mp hu with h | h
      · exact ⟨0, (hnv 0 u).2 h⟩
      · exact ⟨1, (hnv 1 u).2 h⟩
  set φ := toProjectiveSpaceOver s hgen (U.ι ≫ sX) with hφ
  have hpre : ∀ i, φ ⁻¹ᵁ projectiveSpaceOver.standardChart 1 (Spec (.of k)) i = nvCover s i :=
    Stacks.AmpleImmersionReduction.preimage_standardChart s hgen φ
      (fun i => ι_toProjectiveSpaceOver s hgen (U.ι ≫ sX) i)
  refine ⟨φ, toProjectiveSpaceOver_fst _ _ _, fun u => ⟨?_, ?_⟩⟩
  · have : φ u ∈ projectiveSpaceOver.standardChart 1 (Spec (.of k)) 0 ↔ u ∈ nvCover s 0 := by
      rw [← hpre 0]; rfl
    rw [this, hnv 0 u]; rfl
  · have : φ u ∈ projectiveSpaceOver.standardChart 1 (Spec (.of k)) 1 ↔ u ∈ nvCover s 1 := by
      rw [← hpre 1]; rfl
    rw [this, hnv 1 u]; rfl

private theorem exists_graph_resolution {k : Type u} [Field k] {X P : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (sP : P ⟶ Spec (.of k)) (hX : MMP.Mori.IsNormalVariety k sX)
    [IsProper sP] (U : X.Opens) (hU : (U : Set X).Nonempty) (φ : U.toScheme ⟶ P)
    (hφ : U.ι ≫ sX = φ ≫ sP) :
    ∃ (Xt : Scheme.{u}) (μ : Xt ⟶ X) (φt : Xt ⟶ P) (γ : U.toScheme ⟶ Xt),
      IsProper μ ∧ γ ≫ μ = U.ι ∧ γ ≫ φt = φ ∧
      (∀ y : Xt, μ y ∈ U → ∃ u : U.toScheme, γ u = y) ∧ (∀ x, _root_.IsConnected (μ ⁻¹' {x})) ∧
      MMP.Mori.IsVariety k (μ ≫ sX) ∧ φt ≫ sP = μ ≫ sX := by
  obtain ⟨hXv, hXn⟩ := hX
  have : IsIntegral X := hXv.toIsIntegral
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : CompactSpace X := (quasiCompact_iff_compactSpace sX).mp inferInstance
  have : IsNoetherian X := ⟨⟩
  have hUr : IsRetrocompact (U : Set X) := noetherianSpace_isRetrocompact X U
  have : Nonempty U := hU.to_subtype
  set q : U.toScheme ⟶ pullback sX sP := pullback.lift U.ι φ hφ with hq
  have : QuasiCompact U.ι := (quasiCompact_iff_isSpectralMap).2
    ((IsRetrocompact_iff_isSpectralMap_subtypeVal).mp hUr)
  have : QuasiCompact q := by
    have : QuasiCompact (q ≫ pullback.fst sX sP) := by rw [hq, pullback.lift_fst]; infer_instance
    exact QuasiCompact.of_comp q (pullback.fst sX sP)
  set μ : q.image ⟶ X := q.imageι ≫ pullback.fst sX sP with hμ
  set φt : q.image ⟶ P := q.imageι ≫ pullback.snd sX sP with hφt
  have hγμ : q.toImage ≫ μ = U.ι := by
    rw [hμ, ← Category.assoc, Scheme.Hom.toImage_imageι, pullback.lift_fst]
  have hγφ : q.toImage ≫ φt = φ := by
    rw [hφt, ← Category.assoc, Scheme.Hom.toImage_imageι, pullback.lift_snd]
  have hiso : IsIso (μ ∣_ U) :=
    isIso_morphismRestrict_imageι_comp_fst_of_isSeparated sX sP U hUr φ hφ
  have hvar : MMP.Mori.IsVariety k (μ ≫ sX) := by
    have := Scheme.Hom.isVariety_image k q (pullback.fst sX sP ≫ sX)
    simpa [hμ, Category.assoc] using this
  have : IsProper μ := by rw [hμ]; infer_instance
  have hpts : ∀ y : q.image, μ y ∈ U → ∃ u : U.toScheme, q.toImage u = y := by
    intro y hy
    let u : U.toScheme := ⟨μ y, hy⟩
    refine ⟨u, ?_⟩
    have hu : μ (q.toImage u) = μ y := by
      change (q.toImage ≫ μ) u = μ y
      rw [hγμ]; rfl
    have hmem : q.toImage u ∈ μ ⁻¹ᵁ U := by
      change μ (q.toImage u) ∈ U
      rwa [hu]
    have hinj : Function.Injective (μ ∣_ U) := (μ ∣_ U).homeomorph.injective
    exact congrArg Subtype.val (@hinj ⟨q.toImage u, hmem⟩ ⟨y, hy⟩ <| Subtype.ext <| by
      rw [morphismRestrict_base_coe μ U ⟨q.toImage u, hmem⟩, morphismRestrict_base_coe μ U ⟨y, hy⟩,
        hu])
  have : IsIntegral q.image := hvar.toIsIntegral
  have hbir : MMP.Mori.IsBirationalMorphism μ := by
    obtain ⟨u⟩ := ‹Nonempty U›
    refine MMP.Flips.isBirationalMorphism_of_isIso_resLE μ (μ ⁻¹ᵁ U) U
      ⟨q.toImage u, ?_⟩ hU le_rfl ?_
    · change (q.toImage ≫ μ) u ∈ U
      rw [hγμ]; exact u.2
    · rw [Scheme.Hom.resLE_eq_morphismRestrict]; exact hiso
  have hconn := (MMP.Resolution.Bridges.isIso_app_and_isConnected_of_isBirationalMorphism
    (μ ≫ sX) sX hvar ⟨hXv, hXn⟩ μ hbir).2
  refine ⟨q.image, μ, φt, q.toImage, inferInstance, hγμ, hγφ, hpts, hconn, hvar, ?_⟩
  rw [hφt, hμ, Category.assoc, Category.assoc, pullback.condition]

private theorem false_of_pencil_basePoint {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (hX : MMP.Mori.IsNormalVariety k sX) [IsProper sX]
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] (s₀ s₁ : Γ(L, ⊤)) (A₀ A₁ : Set X)
    (hA₀ : Stacks.Ample.nonvanishingLocus L s₀ = A₀ᶜ)
    (hA₁ : Stacks.Ample.nonvanishingLocus L s₁ = A₁ᶜ)
    (D B : Set X) (hD : IsClosed D) (hDc : _root_.IsPreconnected D) (hDne : D.Nonempty)
    (hB : IsClosed B) (hDB : Disjoint D B) (hDA₀ : Disjoint D A₀) (hDA₁ : D ⊆ A₁)
    (hA₁DB : A₁ ⊆ D ∪ B) (x₁ : X) (hx₁ : x₁ ∉ A₁)
    (b : X) (hb : IsClosed ({b} : Set X)) (hb₀ : b ∈ closure (A₀ \ A₁))
    (hb₁ : b ∈ closure (A₁ \ A₀)) : False := by
  classical
  have hXv := hX.1
  have : IsIntegral X := hXv.toIsIntegral
  set U : X.Opens := nonvanishingOpen X L s₀ ⊔ nonvanishingOpen X L s₁ with hUdef
  have hUA : ∀ x : X, x ∈ U ↔ x ∉ A₀ ∩ A₁ := by
    intro x
    rw [hUdef, TopologicalSpace.Opens.mem_sup]
    change x ∈ Stacks.Ample.nonvanishingLocus L s₀ ∨ x ∈ Stacks.Ample.nonvanishingLocus L s₁ ↔ _
    rw [hA₀, hA₁]
    simp only [Set.mem_compl_iff, Set.mem_inter_iff, not_and_or]
  have hUne : (U : Set X).Nonempty := ⟨x₁, (hUA x₁).2 fun h => hx₁ h.2⟩
  obtain ⟨φ, hφs, hφc⟩ := exists_pencilMap sX L s₀ s₁ U hUdef
  set sP : projectiveSpaceOver.{u} 1 (Spec (.of k)) ⟶ Spec (.of k) :=
    pullback.fst (terminal.from (Spec (.of k)))
    (terminal.from (projectiveSpaceAtUniverse.{u} 1))
  have : IsProper sP :=
    isProper_of_isProjectiveMorphism sP (isProjectiveMorphism_projectiveSpaceOver 1 (Spec (.of k)))
  obtain ⟨Xt, μ, φt, γ, hμp, hγμ, hγφ, hpts, hμf, hXtv, hφtμ⟩ :=
    exists_graph_resolution sX sP hX U hUne φ hφs.symm
  have := hμp
  have : MMP.Mori.IsVariety k (μ ≫ sX) := hXtv
  have : IsProper (φt ≫ sP) := by rw [hφtμ]; infer_instance
  have : IsProper φt := IsProper.of_comp φt sP
  obtain ⟨X', p, σ, ⟨hS⟩, hpP, hps, hpiso, hpconn, hσfin, hX'v, -, -, -, -⟩ :=
    MMP.Resolution.Bridges.exists_steinFactorization_of_isVariety (μ ≫ sX) sP φt hφtμ
  have hcomp : p ≫ σ = φt := hS.comp
  have := hpP
  have := hσfin
  -- the curve property of `X'`
  have : IsIntegral X' := hX'v.toIsIntegral
  have : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian (σ ≫ sP)
  have : CompactSpace X' := (quasiCompact_iff_compactSpace (σ ≫ sP)).mp inferInstance
  have : AlgebraicGeometry.IsNoetherian X' := ⟨⟩
  have : TopologicalSpace.NoetherianSpace X' := inferInstance
  have hdim : topologicalKrullDim X' ≤ 1 := by
    refine (MMP.Fourfold.topologicalKrullDim_le_of_isFinite σ (T := Set.univ)
      fun _ => trivial).trans ?_
    rw [(Homeomorph.Set.univ _).isHomeomorph.topologicalKrullDim_eq]
    exact (topologicalKrullDim_projectiveSpaceOver_one k).le
  -- the section `γ` extended to `X`
  obtain ⟨u₀⟩ : Nonempty U.toScheme := hUne.to_subtype
  let γ' : X → Xt := fun x => if h : x ∈ U then γ ⟨x, h⟩ else γ u₀
  have hγ'U : ∀ x (h : x ∈ U), γ' x = γ ⟨x, h⟩ := fun x h => dif_pos h
  have hμγ : ∀ u : U.toScheme, μ (γ u) = u.1 := fun u => by
    change (γ ≫ μ) u = u.1
    rw [hγμ]; rfl
  have hφγ : ∀ u : U.toScheme, σ (p (γ u)) = φ u := fun u => by
    change (γ ≫ p ≫ σ) u = φ u
    rw [hcomp, hγφ]
  have hA₀c : IsClosed A₀ := by
    rw [← compl_compl A₀, ← hA₀]; exact (nonvanishingOpen X L s₀).isOpen.isClosed_compl
  have hcover : (projectiveSpaceOver.standardChart 1 (Spec (.of k)) 0 :
      Set (projectiveSpaceOver.{u} 1 (Spec (.of k)))) ∪
      projectiveSpaceOver.standardChart 1 (Spec (.of k)) 1 = Set.univ := by
    refine Set.eq_univ_of_forall fun z => ?_
    have hz : z ∈ (⨆ i, projectiveSpaceOver.standardChart 1 (Spec (.of k)) i) := by
      rw [projectiveSpaceOver.iSup_standardChart]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hz
    fin_cases i
    · exact Or.inl hi
    · exact Or.inr hi
  have hγμ' : ∀ x, x ∉ A₀ ∩ A₁ → μ (γ' x) = x := fun x hx => by
    rw [hγ'U x ((hUA x).2 hx)]; exact hμγ _
  have hγ' : ∀ y, μ y ∉ A₀ ∩ A₁ → y = γ' (μ y) := fun y hy => by
    have hyU := (hUA (μ y)).2 hy
    obtain ⟨u, hu⟩ := hpts y hyU
    rw [hγ'U _ hyU]
    have hu1 : u.1 = μ y := by rw [← hu]; exact (hμγ u).symm
    have : u = (⟨μ y, hyU⟩ : U.toScheme) := Subtype.ext hu1
    rw [← this, hu]
  have hset : (A₀ ∩ A₁)ᶜ = (U : Set X) := by
    ext x; exact ((hUA x).trans Iff.rfl).symm
  have hγc : ContinuousOn γ' (A₀ ∩ A₁)ᶜ := by
    rw [hset, continuousOn_iff_continuous_restrict]
    exact γ.continuous.congr fun x => (hγ'U x.1 x.2).symm
  have hV : ∀ (A : Set X) (s : Γ(L, ⊤)) (i : Fin 2),
      Stacks.Ample.nonvanishingLocus L s = Aᶜ →
      (∀ u : U.toScheme, φ u ∈ projectiveSpaceOver.standardChart 1 (Spec (.of k)) i ↔
        u.1 ∈ Stacks.Ample.nonvanishingLocus L s) →
      ∀ x, x ∉ A₀ ∩ A₁ → (σ (p (γ' x)) ∈ projectiveSpaceOver.standardChart 1 (Spec (.of k)) i ↔
        x ∉ A) := by
    intro A s i hA hi x hx
    rw [hγ'U x ((hUA x).2 hx)]
    have h1 := hφγ ⟨x, (hUA x).2 hx⟩
    have h2 := hi ⟨x, (hUA x).2 hx⟩
    rw [hA] at h2
    exact h1 ▸ h2
  exact false_of_mem_closure_diff_of_mem_closure_diff μ μ.continuous μ.isClosedMap p p.continuous
    p.isClosedMap σ σ.continuous A₀ A₁ hA₀c _ _
    (projectiveSpaceOver.standardChart 1 (Spec (.of k)) 0).isOpen
    (projectiveSpaceOver.standardChart 1 (Spec (.of k)) 1).isOpen hcover γ' hγμ' hγ' hγc
    (hV A₀ s₀ 0 hA₀ fun u => (hφc u).1) (hV A₁ s₁ 1 hA₁ fun u => (hφc u).2)
    (subsingleton_of_isClosed_of_isPreconnected hdim) (fun c => (hpconn c).isPreconnected)
    (fun x => (hμf x).isPreconnected) D B hD hDc hDne hB hDB hDA₀ hDA₁ hA₁DB x₁ hx₁ b hb hb₀ hb₁

end BasePoint

/-! ### Members of `|M|` meeting `D` only along `D` -/

section Members

/-- A divisor whose support contains a prime divisor `E` has a nonzero coefficient along `E`. -/
private theorem coeff_ne_zero_of_support_subset_supp {X : Scheme.{u}} {E : Mori.PrimeDivisor X}
    {G : Divisor X} (h : (E.support : Set X) ⊆ G.supp) : G E ≠ 0 := by
  have hη : E.genericPoint ∈ (G.supp : Set X) := h (primeDivisor_genericPoint_mem_support E)
  obtain ⟨P, hP, hPη⟩ := DivisorWithCoeffs.mem_supp_iff.mp hη
  rwa [← eq_of_genericPoint_mem_primeDivisor_support hPη] at hP

/-- Removing the component along `E` keeps an effective divisor effective. -/
private theorem sub_single_coeff_nonneg {X : Scheme.{u}} {Z : Divisor X} (hZ : 0 ≤ Z)
    (E : Mori.PrimeDivisor X) : 0 ≤ Z - Finsupp.single E (Z E) := fun P => by
  by_cases hP : P = E
  · subst hP; simp
  · simpa [Finsupp.single_eq_of_ne' (Ne.symm hP)] using hZ P

/-- The support of `Z` is `E` together with the support of `Z - mult_E(Z) E`. -/
private theorem supp_subset_union_supp_sub_single {X : Scheme.{u}} (Z : Divisor X)
    (E : Mori.PrimeDivisor X) :
    (Z.supp : Set X) ⊆ E.support ∪ (Z - Finsupp.single E (Z E)).supp := by
  intro x hx
  obtain ⟨P, hP, hxP⟩ := DivisorWithCoeffs.mem_supp_iff.mp hx
  by_cases hPE : P = E
  · subst hPE
    exact Or.inl hxP
  · refine Or.inr (DivisorWithCoeffs.mem_supp_iff.mpr ⟨P, ?_, hxP⟩)
    simpa [DivisorWithCoeffs.coeff_apply, Finsupp.single_eq_of_ne' (Ne.symm hPE)] using hP

private theorem disjoint_support_supp_sub_single {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [QuasiCompact sX] (n : ℕ) (K : Divisor X) (Δ : QDivisor X) (E : Mori.PrimeDivisor X)
    (hD : IsTriviallyConnected k sX n K Δ (Finsupp.single E 1)) {m₀ : ℕ} (hm₀ : 0 < m₀)
    {M : Divisor X} (hML : Divisor.toQDivisor M = (m₀ : ℤ) • (Divisor.toQDivisor K + Δ))
    (hMc : M.IsCartier)
    (hno : ¬ ∃ D' : Divisor X, D'.IsEffective ∧ ∃ d m : ℕ, 1 ≤ d ∧ 0 < m ∧ ∃ M : Divisor X,
        Divisor.toQDivisor M = (m : ℤ) • (Divisor.toQDivisor K + Δ) ∧
        Divisor.LinearlyEquivalent ((d : ℤ) • (Finsupp.single E 1 : Divisor X) + D') M ∧
        ¬ (DivisorWithCoeffs.supp (Finsupp.single E 1 : Divisor X) : Set X) ⊆
          (DivisorWithCoeffs.supp D' : Set X) ∧
        ((DivisorWithCoeffs.supp (Finsupp.single E 1 : Divisor X) : Set X) ∩
          (DivisorWithCoeffs.supp D' : Set X)).Nonempty)
    {Z : Divisor X} (hZ : 0 ≤ Z) (hZM : Z.LinearlyEquivalent M) :
    Disjoint (E.support : Set X) ((Z - Finsupp.single E (Z E)).supp : Set X) := by
  classical
  rw [Set.disjoint_iff_inter_eq_empty, ← Set.not_nonempty_iff_eq_empty]
  intro hmeet
  set D' := Z - Finsupp.single E (Z E) with hD'
  have hD'E : D' E = 0 := by simp [hD']
  have hD'0 : 0 ≤ D' := sub_single_coeff_nonneg hZ E
  have hnot : ¬ (E.support : Set X) ⊆ D'.supp := fun h =>
    coeff_ne_zero_of_support_subset_supp h hD'E
  by_cases hZE : 1 ≤ Z E
  · apply hno
    refine ⟨D', (DivisorWithCoeffs.isEffective_iff_nonneg).2 hD'0, (Z E).toNat, m₀, by omega,
      hm₀, M, hML,
      ?_, ?_, ?_⟩
    · have : ((Z E).toNat : ℤ) • (Finsupp.single E 1 : Divisor X) + D' = Z := by
        rw [hD', Int.toNat_of_nonneg (by omega), Finsupp.smul_single, smul_eq_mul, mul_one]
        abel
      rwa [this]
    · rwa [coe_supp_single_one]
    · rwa [coe_supp_single_one]
  · have hZE0 : Z E = 0 := le_antisymm (by omega) (hZ E)
    obtain ⟨⟨hXv, -⟩, hP, -, hL, -, -⟩ := id hD
    have hZc : Z.IsCartier := Divisor.IsCartier.of_linearlyEquivalent hZM hMc
    have hZq := QDivisor.isQCartier_toQDivisor hZc
    have hcoe : ∀ G : Divisor X, ((Divisor.toQDivisor G).supp : Set X) = G.supp := by
      intro G
      ext x
      simp only [SetLike.mem_coe, DivisorWithCoeffs.mem_supp_iff, Divisor.coeff_toQDivisor, ne_eq,
        Int.cast_eq_zero]
    have h0 : 0 ≤ Divisor.toQDivisor Z := fun P => by
      have := hZ P
      change (0 : ℚ) ≤ (Divisor.toQDivisor Z).coeff P
      rw [Divisor.coeff_toQDivisor]
      exact_mod_cast this
    have : IsProper sX := hP
    have hBL : ∀ Γ : ProperCurve sX,
        (Divisor.toQDivisor K + Δ).intersectionNumber k sX Γ.ι Γ.dim_le hL = 0 →
          (Divisor.toQDivisor Z).intersectionNumber k sX Γ.ι Γ.dim_le hZq = 0 := by
      intro Γ hΓ
      have hZMc : (Z - M).IsCartier := Divisor.IsCartier.of_linearlyEquivalent
        (show (Z - M).LinearlyEquivalent 0 from by
          obtain ⟨φ, hφ⟩ := hZM; exact ⟨φ, by rw [sub_zero, hφ]⟩) Divisor.isCartier_zero
      have hZMq := QDivisor.isQCartier_toQDivisor hZMc
      have hmL : (m₀ : ℤ) • (Divisor.toQDivisor K + Δ) =
          (m₀ : ℚ) • (Divisor.toQDivisor K + Δ) := by
        rw [← Int.cast_smul_eq_zsmul ℚ]; push_cast; rfl
      have hMq : ((m₀ : ℚ) • (Divisor.toQDivisor K + Δ)).IsQCartier := by
        rw [← hmL, ← hML]; exact QDivisor.isQCartier_toQDivisor hMc
      have hsplit : Divisor.toQDivisor Z =
          Divisor.toQDivisor (Z - M) + (m₀ : ℚ) • (Divisor.toQDivisor K + Δ) := by
        rw [← hmL, ← hML, map_sub, sub_add_cancel]
      rw [QDivisor.intersectionNumber_congr sX Γ.ι Γ.dim_le hsplit hZq (hZMq.add hMq),
        QDivisor.intersectionNumber_add' k sX Γ.ι Γ.dim_le _ _ hZMq hMq,
        QDivisor.intersectionNumber_toQDivisor k sX Γ.ι Γ.dim_le _ hZMc,
        Divisor.degreeOn_eq_zero_of_linearlyEquivalent sX Γ.ι Γ.dim_le hZMc
          (show (Z - M).LinearlyEquivalent 0 from by
            obtain ⟨φ, hφ⟩ := hZM; exact ⟨φ, by rw [sub_zero, hφ]⟩),
        MMP.Fourfold.intersectionNumber_smul sX Γ.ι Γ.dim_le _ hL _ hMq, hΓ]
      simp
    have hsub := supp_subset_supp_of_isTriviallyConnected sX n K Δ E hD hL
      (Divisor.toQDivisor Z) hZq h0 hBL (by
        rw [coe_supp_single_one, hcoe]
        have : D' = Z := by rw [hD', hZE0, Finsupp.single_zero, sub_zero]
        rw [← this]; exact hmeet)
    rw [coe_supp_single_one, hcoe] at hsub
    exact coeff_ne_zero_of_support_subset_supp hsub hZE0

/-- The support of an effective divisor is contained in that of a larger one. -/
private theorem supp_subset_supp_of_le {X : Scheme.{u}} {A B : Divisor X} (hA : 0 ≤ A)
    (hAB : A ≤ B) :
    (A.supp : Set X) ⊆ B.supp := by
  intro x hx
  obtain ⟨P, hP, hxP⟩ := DivisorWithCoeffs.mem_supp_iff.mp hx
  refine DivisorWithCoeffs.mem_supp_iff.mpr ⟨P, ?_, hxP⟩
  have h1 := hA P
  have h2 := hAB P
  change A P ≠ 0 at hP
  change B P ≠ 0
  simp only [Finsupp.coe_zero, Pi.zero_apply] at h1
  omega

/-- A nonzero multiple of a divisor has the same support. -/
private theorem supp_zsmul {X : Scheme.{u}} {n : ℤ} (hn : n ≠ 0) (A : Divisor X) :
    ((n • A).supp : Set X) = A.supp := by
  ext x
  simp only [SetLike.mem_coe, DivisorWithCoeffs.mem_supp_iff, DivisorWithCoeffs.coeff_apply,
    Finsupp.smul_apply, smul_eq_mul, ne_eq, mul_eq_zero, hn, false_or]

/-- A point of the support of `A` lies in the closure of the points of `Supp A` off `Supp B`, when
`A` and `B` have no common component. -/
private theorem mem_closure_supp_diff {X : Scheme.{u}} {A B : Divisor X}
    (hAB : ∀ P, A P = 0 ∨ B P = 0)
    {b : X} (hb : b ∈ (A.supp : Set X)) : b ∈ closure ((A.supp : Set X) \ B.supp) := by
  obtain ⟨P, hP, hbP⟩ := DivisorWithCoeffs.mem_supp_iff.mp hb
  have hη : P.genericPoint ∈ (A.supp : Set X) :=
    DivisorWithCoeffs.support_subset_supp hP (MMP.Flips.primeDivisor_genericPoint_mem_support P)
  have hηB : P.genericPoint ∉ (B.supp : Set X) := by
    intro h
    obtain ⟨Q, hQ, hQη⟩ := DivisorWithCoeffs.mem_supp_iff.mp h
    rw [← eq_of_genericPoint_mem_primeDivisor_support hQη] at hQ
    rcases hAB P with h0 | h0
    · exact hP h0
    · exact hQ h0
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hbP
  exact closure_mono (Set.singleton_subset_iff.mpr
    (show P.genericPoint ∈ (A.supp : Set X) \ B.supp from ⟨hη, hηB⟩)) hbP

private theorem supp_sub_inf_subset_supp_sub_single {X : Scheme.{u}} {Z₀ Z₁ : Divisor X}
    (hZ₀ : 0 ≤ Z₀) (hZ₁ : 0 ≤ Z₁) (E : Mori.PrimeDivisor X) (hle : Z₀ E ≤ Z₁ E) :
    ((Z₀ - Z₀ ⊓ Z₁).supp : Set X) ⊆ (Z₀ - Finsupp.single E (Z₀ E)).supp := by
  refine supp_subset_supp_of_le (sub_nonneg.mpr inf_le_left) fun P => ?_
  by_cases hP : P = E
  · subst hP
    simp only [Finsupp.coe_sub, Pi.sub_apply, Finsupp.inf_apply, Finsupp.single_eq_same, sub_self,
      tsub_le_iff_right, zero_add, le_inf_iff, Std.le_refl, true_and]
    omega
  · simp [Finsupp.inf_apply, Finsupp.single_eq_of_ne' (Ne.symm hP)]
    have := hZ₀ P; have := hZ₁ P
    simp only [Finsupp.coe_zero, Pi.zero_apply] at *
    omega

private theorem supp_sub_inf_subset_union {X : Scheme.{u}} {Z₀ Z₁ : Divisor X}
    (hZ₀ : 0 ≤ Z₀) (hZ₁ : 0 ≤ Z₁) (E : Mori.PrimeDivisor X) :
    ((Z₁ - Z₀ ⊓ Z₁).supp : Set X) ⊆ E.support ∪ (Z₁ - Finsupp.single E (Z₁ E)).supp :=
  (supp_subset_supp_of_le (sub_nonneg.mpr inf_le_right) (sub_le_self _ (le_inf hZ₀ hZ₁))).trans
    (supp_subset_union_supp_sub_single Z₁ E)

private theorem principalDivisor_pow {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] (φ : (RationalFunctions X)ˣ) (n : ℕ) :
    principalDivisor (φ ^ n) = n • principalDivisor φ := by
  ext E
  change E.ord (φ ^ n) = (n • principalDivisor φ) E
  rw [Finsupp.smul_apply, MMP.Mori.PrimeDivisor.ord_pow]
  rfl

private theorem disjoint_supp_sub_inf {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)}
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X] [CompactSpace X]
    (hX : Mori.IsProjectiveVariety k sX) (hQ : Fourfold.IsQFactorial sX)
    {Z₀ Z₁ : Divisor X} (hZ₀ : 0 ≤ Z₀) (hZ₁ : 0 ≤ Z₁) (ψ : (RationalFunctions X)ˣ)
    (hψ : Z₁ = principalDivisor ψ + Z₀) (E : Mori.PrimeDivisor X) (hlt : Z₀ E < Z₁ E)
    (h₀ : Disjoint (E.support : Set X) ((Z₀ - Finsupp.single E (Z₀ E)).supp : Set X))
    (h₁ : Disjoint (E.support : Set X) ((Z₁ - Finsupp.single E (Z₁ E)).supp : Set X)) :
    Disjoint ((Z₀ - Z₀ ⊓ Z₁).supp : Set X) ((Z₁ - Z₀ ⊓ Z₁).supp : Set X) := by
  classical
  set M₀ := Z₀ - Z₀ ⊓ Z₁ with hM₀def
  set M₁ := Z₁ - Z₀ ⊓ Z₁ with hM₁def
  have hcoe₀ : ∀ P, M₀ P = Z₀ P - min (Z₀ P) (Z₁ P) := fun P => by
    simp [hM₀def, Finsupp.inf_apply]
  have hcoe₁ : ∀ P, M₁ P = Z₁ P - min (Z₀ P) (Z₁ P) := fun P => by
    simp [hM₁def, Finsupp.inf_apply]
  have hM₀ : 0 ≤ M₀ := fun P => by
    have := hcoe₀ P; simp only [Finsupp.coe_zero, Pi.zero_apply]; omega
  have hM₁ : 0 ≤ M₁ := fun P => by
    have := hcoe₁ P; simp only [Finsupp.coe_zero, Pi.zero_apply]; omega
  have hinf : ∀ P, M₀ P = 0 ∨ M₁ P = 0 := fun P => by
    rw [hcoe₀, hcoe₁]; omega
  have hM₁₀ : M₁ = principalDivisor ψ + M₀ := by
    rw [hM₁def, hM₀def, hψ]; abel
  have hM₁E : M₁ E ≠ 0 := by rw [hcoe₁]; omega
  have hM₀B₀ : M₀ ≤ Z₀ - Finsupp.single E (Z₀ E) := fun P => by
    by_cases hP : P = E
    · subst hP
      rw [hcoe₀]
      simp only [Finsupp.coe_sub, Pi.sub_apply, Finsupp.single_eq_same, sub_self, tsub_le_iff_right,
        zero_add, le_inf_iff, Std.le_refl, true_and]
      omega
    · rw [hcoe₀]
      simp only [Finsupp.coe_sub, Pi.sub_apply, Finsupp.single_eq_of_ne' (Ne.symm hP), sub_zero,
        tsub_le_iff_right, le_add_iff_nonneg_right, le_inf_iff]
      have := hZ₀ P; have := hZ₁ P
      simp only [Finsupp.coe_zero, Pi.zero_apply] at *
      omega
  -- a closed base point
  rw [Set.disjoint_iff_inter_eq_empty, ← Set.not_nonempty_iff_eq_empty]
  intro hne
  have hXv := hX.toIsVariety
  have : LocallyOfFiniteType sX := hXv.toLocallyOfFiniteType
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  have : IsProper sX := isProper_of_isProjectiveMorphism sX hX.isProjective
  obtain ⟨b, ⟨hb₀, hb₁⟩, hbc⟩ := nonempty_inter_closedPoints hne
    (M₀.isClosed_supp.inter M₁.isClosed_supp).isLocallyClosed
  -- the pencil in `|N M₀|`
  obtain ⟨N, hN, hNc⟩ := hQ.2 M₀
  have hN0 : ((N : ℤ)) ≠ 0 := by exact_mod_cast hN.ne'
  have := hNc.isInvertibleModule_divisorialSheaf
  obtain ⟨τ₀, hτ₀, he₀, -⟩ := exists_section_of_nonneg (D := (N : ℤ) • M₀) 1
    (by rw [MMP.Mori.principalDivisor_one, zero_add]; exact smul_nonneg (by positivity) hM₀)
  have hpow : principalDivisor (ψ ^ N) + (N : ℤ) • M₀ = (N : ℤ) • M₁ := by
    rw [principalDivisor_pow, hM₁₀, smul_add]; simp only [natCast_zsmul]
  obtain ⟨τ₁, hτ₁, he₁, -⟩ := exists_section_of_nonneg (D := (N : ℤ) • M₀) (ψ ^ N)
    (by rw [hpow]; exact smul_nonneg (by positivity) hM₁)
  have hA₀ := nonvanishingLocus_eq_compl_supp_zeroDivisor hNc τ₀ hτ₀
  rw [he₀, MMP.Mori.principalDivisor_one, zero_add, supp_zsmul hN0] at hA₀
  have hA₁ := nonvanishingLocus_eq_compl_supp_zeroDivisor hNc τ₁ hτ₁
  rw [he₁, hpow, supp_zsmul hN0] at hA₁
  have hEc : IsClosed (E.support : Set X) := E.idealSheaf.support.isClosed
  have hEp : _root_.IsPreconnected (E.support : Set X) := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact isIrreducible_singleton.closure.isConnected.isPreconnected
  exact false_of_pencil_basePoint sX ⟨hXv, inferInstance⟩ ((N : ℤ) • M₀).divisorialSheaf τ₀ τ₁
    _ _ hA₀ hA₁ _ _ hEc hEp
    ⟨E.genericPoint, MMP.Flips.primeDivisor_genericPoint_mem_support E⟩
    (DivisorWithCoeffs.isClosed_supp _) h₁ (h₀.mono_right (supp_subset_supp_of_le hM₀ hM₀B₀))
    (DivisorWithCoeffs.support_subset_supp hM₁E)
    (supp_sub_inf_subset_union hZ₀ hZ₁ E) (genericPoint X)
    (MMP.Fourfold.genericPoint_notMem_supp M₁) b hbc
    (mem_closure_supp_diff hinf hb₀)
    (mem_closure_supp_diff (fun P => (hinf P).symm) hb₁)

end Members

/-! ### Evaluating sections at a closed point -/

section Evaluation

/-- The rational function underlying a section of `𝒪_X(D)`. -/
private def secVal {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] {D : Divisor X}
    {W : X.Opens} (m : D.divisorialSheaf.val.obj (Opposite.op W)) :
    ToType ((rationalFunctionsPresheaf X).obj (Opposite.op W)) :=
  (show D.divisorialSubmodule W from m).1

private theorem secVal_map {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] {D : Divisor X}
    {W W' : X.Opens} (h : W' ⟶ W) (m : D.divisorialSheaf.val.obj (Opposite.op W)) (Z) :
    secVal (D.divisorialSheaf.val.map h.op m) Z = secVal m ⟨Z.1, h.le Z.2⟩ := rfl

private theorem secVal_smul {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] {D : Divisor X}
    {W : X.Opens} (r : X.ringCatSheaf.obj.obj (Opposite.op W))
    (m : D.divisorialSheaf.val.obj (Opposite.op W)) (Z) :
    secVal (r • m) Z = X.presheaf.germ W _ Z.2 r * secVal m Z := rfl

private theorem secVal_injective {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    {D : Divisor X} {W : X.Opens} :
    Function.Injective (secVal (D := D) (W := W)) := fun _ _ h => Subtype.ext h

/-- The local generator `ψ⁻¹` of `𝒪_X(D)` over an open on which `ψ` is a local equation. -/
private noncomputable def localGen {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    {D : Divisor X} {U : X.Opens} {ψ : (RationalFunctions X)ˣ}
    (hψ : D.IsLocalEquation U ψ) : D.divisorialSheaf.val.obj (Opposite.op U) :=
  (⟨fun Z => ((ψ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) Z.1, fun E hE => Or.inr (by
    rw [E.valuation_component, PrimeDivisor.ord_inv, hψ E hE])⟩ : D.divisorialSubmodule U)

private theorem secVal_localGen {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    {D : Divisor X} {U : X.Opens} {ψ : (RationalFunctions X)ˣ}
    (hψ : D.IsLocalEquation U ψ) (Z) :
    secVal (localGen hψ) Z = ((ψ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) Z.1 := rfl

private theorem bijective_smul_localGen {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    {D : Divisor X} {U : X.Opens} {ψ : (RationalFunctions X)ˣ}
    (hψ : D.IsLocalEquation U ψ) {W : X.Opens} (h : W ⟶ U) :
    Function.Bijective (fun r : X.ringCatSheaf.obj.obj (Opposite.op W) =>
      r • D.divisorialSheaf.val.map h.op (localGen hψ)) := by
  refine ⟨fun r r' hrr => ?_, fun m => ?_⟩
  · apply toRationalFunctionsPresheaf_app_injective W
    funext Z
    have := congrFun (congrArg secVal hrr) Z
    have hu : IsUnit (((ψ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) Z.1) :=
      ⟨RationalFunctions.unitsEquiv X ψ⁻¹ Z.1, rfl⟩
    exact hu.mul_left_injective this
  · let φ : ToType ((rationalFunctionsPresheaf X).obj (Opposite.op W)) :=
      fun Z => (ψ : RationalFunctions X) Z.1 * secVal m Z
    have hφ : (0 : Divisor X).IsDivisorialSection W φ := by
      intro E hE
      have h1 : E.OrdGE (E.ord ψ) ((ψ : RationalFunctions X) E.component) :=
        Or.inr (E.valuation_component ψ).ge
      have h2 := (show D.divisorialSubmodule W from m).2 E hE
      have h3 := h1.mul h2
      refine h3.mono (le_of_eq ?_)
      rw [hψ E (hE.mono (Set.inter_subset_inter_right _ h.le)),
        DivisorWithCoeffs.coeff_zero]
      ring
    obtain ⟨a, ha⟩ := Divisor.IsDivisorialSection.exists_eq hφ
    refine ⟨a, secVal_injective (funext fun Z => ?_)⟩
    have hZ := congrFun ha Z
    rw [toRationalFunctionsPresheaf_app_apply] at hZ
    refine (secVal_smul (D := D) (W := W) a _ Z).trans ?_
    rw [secVal_map, secVal_localGen, hZ]
    simp only [φ]
    rw [mul_comm, ← mul_assoc, ← Pi.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Pi.one_apply, one_mul]

/-- The coordinate of a section of `𝒪_X(D)` with respect to the local generator. -/
private noncomputable def localCoord {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    {D : Divisor X} {U : X.Opens} {ψ : (RationalFunctions X)ˣ}
    (hψ : D.IsLocalEquation U ψ) {W : X.Opens} (h : W ⟶ U) :
    (D.divisorialSheaf.val.obj (Opposite.op W) : Type u) ≃ₗ[
      (X.ringCatSheaf.obj.obj (Opposite.op W) : Type u)]
      (X.ringCatSheaf.obj.obj (Opposite.op W) : Type u) :=
  (LinearEquiv.ofBijective
    (LinearMap.toSpanSingleton _ _ (D.divisorialSheaf.val.map h.op (localGen hψ)))
    (bijective_smul_localGen hψ h)).symm

private theorem eq_localCoord_smul {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    {D : Divisor X} {U : X.Opens} {ψ : (RationalFunctions X)ˣ}
    (hψ : D.IsLocalEquation U ψ) {W : X.Opens} (h : W ⟶ U)
    (m : D.divisorialSheaf.val.obj (Opposite.op W)) :
    m = localCoord hψ h m • D.divisorialSheaf.val.map h.op (localGen hψ) :=
  ((LinearEquiv.ofBijective
    (LinearMap.toSpanSingleton _ _ (D.divisorialSheaf.val.map h.op (localGen hψ)))
    (bijective_smul_localGen hψ h)).apply_symm_apply m).symm

private theorem localCoord_smul {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    {D : Divisor X} {U : X.Opens} {ψ : (RationalFunctions X)ˣ}
    (hψ : D.IsLocalEquation U ψ) {W : X.Opens} (h : W ⟶ U)
    (r : X.ringCatSheaf.obj.obj (Opposite.op W)) :
    localCoord hψ h (r • D.divisorialSheaf.val.map h.op (localGen hψ)) = r :=
  (LinearEquiv.ofBijective
    (LinearMap.toSpanSingleton _ _ (D.divisorialSheaf.val.map h.op (localGen hψ)))
    (bijective_smul_localGen hψ h)).symm_apply_apply r

/-- The sectionwise trivialization of `𝒪_X(D)` over an open carrying a local equation. -/
private noncomputable def localTriv {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    {D : Divisor X} {U : X.Opens} {ψ : (RationalFunctions X)ˣ}
    (hψ : D.IsLocalEquation U ψ) :
    Stacks.SheafDescent.Trivialization X.presheaf D.divisorialSheaf.val U where
  θ W h := localCoord hψ h
  θ_naturality {W W'} h h' m := by
    have key : D.divisorialSheaf.val.map h'.op m =
        X.ringCatSheaf.obj.map h'.op (localCoord hψ h m) •
          D.divisorialSheaf.val.map (h' ≫ h).op (localGen hψ) := by
      refine (congrArg (D.divisorialSheaf.val.map h'.op) (eq_localCoord_smul hψ h m)).trans ?_
      refine (PresheafOfModules.map_smul D.divisorialSheaf.val h'.op _ _).trans ?_
      congr 1
    exact (congrArg (localCoord hψ (h' ≫ h)) key).trans (localCoord_smul _ _ _)

/-- **Nonvanishing of a section of `𝒪_X(D)` read on a local equation.** If `ψ` is a local equation
of `D` on `U` and `a` is the regular function `ψ σ` on `U`, then `σ` does not vanish at `y ∈ U`
exactly when `a` is a unit at `y`. -/
private theorem mem_nonvanishingLocus_iff_isUnit_germ {X : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] {D : Divisor X} {U : X.Opens}
    {ψ : (RationalFunctions X)ˣ} (hψ : D.IsLocalEquation U ψ)
    (σ : D.divisorialSheaf.val.obj (Opposite.op ⊤)) (a : Γ(X, U))
    (ha : ∀ Z, X.presheaf.germ U _ Z.2 a = (ψ : RationalFunctions X) Z.1 *
      secVal (D.divisorialSheaf.val.map (homOfLE (le_top : U ≤ ⊤)).op σ) Z)
    {y : X} (hy : y ∈ U) :
    y ∈ Stacks.Ample.nonvanishingLocus D.divisorialSheaf σ ↔
      IsUnit (X.presheaf.germ U y hy a) := by
  rw [Stacks.NonvanishingOpen.mem_nonvanishingLocus_iff_isUnit (localTriv hψ) σ hy]
  suffices h : Stacks.NonvanishingOpen.trivTop (localTriv hψ) σ = a by rw [h]
  change localCoord hψ (𝟙 U) (D.divisorialSheaf.val.map (homOfLE (le_top : U ≤ ⊤)).op σ) = a
  apply (bijective_smul_localGen hψ (𝟙 U)).1
  refine secVal_injective (funext fun Z => ?_)
  refine (congrFun (congrArg secVal (eq_localCoord_smul hψ (𝟙 U) _).symm) Z).trans ?_
  refine Eq.trans ?_ (show X.presheaf.germ U _ Z.2 a *
    ((ψ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) Z.1 = _ from rfl)
  rw [ha, mul_comm, ← mul_assoc, ← Pi.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Pi.one_apply, one_mul]

/-- On an open carrying a local equation `ψ` of `D`, the product `ψ σ` of a global section of
`𝒪_X(D)` is a regular function. -/
private theorem exists_germ_eq_mul {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    {D : Divisor X} {U : X.Opens} {ψ : (RationalFunctions X)ˣ}
    (hψ : D.IsLocalEquation U ψ) (σ : D.divisorialSheaf.val.obj (Opposite.op ⊤)) :
    ∃ a : Γ(X, U), ∀ Z, X.presheaf.germ U _ Z.2 a = (ψ : RationalFunctions X) Z.1 *
      secVal (D.divisorialSheaf.val.map (homOfLE (le_top : U ≤ ⊤)).op σ) Z := by
  let φ : ToType ((rationalFunctionsPresheaf X).obj (Opposite.op U)) := fun Z =>
    (ψ : RationalFunctions X) Z.1 *
      secVal (D.divisorialSheaf.val.map (homOfLE (le_top : U ≤ ⊤)).op σ) Z
  have hφ : (0 : Divisor X).IsDivisorialSection U φ := by
    intro E hE
    have h1 : E.OrdGE (E.ord ψ) ((ψ : RationalFunctions X) E.component) :=
      Or.inr (E.valuation_component ψ).ge
    have h2 := (show D.divisorialSubmodule U from
      D.divisorialSheaf.val.map (homOfLE (le_top : U ≤ ⊤)).op σ).2 E hE
    refine (h1.mul h2).mono (le_of_eq ?_)
    rw [hψ E hE, DivisorWithCoeffs.coeff_zero]
    ring
  obtain ⟨a, ha⟩ := Divisor.IsDivisorialSection.exists_eq hφ
  exact ⟨a, fun Z => (toRationalFunctionsPresheaf_app_apply a Z).symm.trans (congrFun ha Z)⟩

/-- **Evaluation at a closed point.** If `s` generates `𝒪_X(G)` at a closed point `x` of a
variety over an algebraically closed field, then some `t - c s`, `c ∈ k`, vanishes at `x`. -/
private theorem exists_notMem_nonvanishingLocus_sub_smul {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] [IsLocallyNoetherian X]
    [IsNormal X] {G : Divisor X} (hG : G.IsCartier)
    (s t : G.divisorialSheaf.val.obj (Opposite.op ⊤)) {x : X} (hx : IsClosed ({x} : Set X))
    (hs : x ∈ Stacks.Ample.nonvanishingLocus G.divisorialSheaf s) :
    ∃ c : k, x ∉ Stacks.Ample.nonvanishingLocus G.divisorialSheaf
      (t - (show X.ringCatSheaf.obj.obj (Opposite.op ⊤) from
        scalarsToGlobalSections k sX c) • s) := by
  obtain ⟨U, hxU, ψ, hψ⟩ := hG x
  obtain ⟨a, ha⟩ := exists_germ_eq_mul hψ s
  obtain ⟨b, hb⟩ := exists_germ_eq_mul hψ t
  have hua : IsUnit (X.presheaf.germ U x hxU a) :=
    (mem_nonvanishingLocus_iff_isUnit_germ hψ s a ha hxU).1 hs
  letI := stalkAlgebra sX x
  obtain ⟨c, hc⟩ := MMP.Mori.SurfaceAux.residue_surjective sX x hx
    (Ideal.Quotient.mk _ (X.presheaf.germ U x hxU b * ↑(hua.unit⁻¹)))
  refine ⟨c, ?_⟩
  set rr : X.ringCatSheaf.obj.obj (Opposite.op ⊤) := scalarsToGlobalSections k sX c with hrr
  set r' : Γ(X, U) := X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
    (scalarsToGlobalSections k sX c) with hr'
  have ha' : ∀ Z, X.presheaf.germ U _ Z.2 (b - r' * a) = (ψ : RationalFunctions X) Z.1 *
      secVal (G.divisorialSheaf.val.map (homOfLE (le_top : U ≤ ⊤)).op (t - rr • s)) Z := by
    intro Z
    rw [map_sub, map_mul, hb Z, ha Z, map_sub, PresheafOfModules.map_smul]
    change _ = (ψ : RationalFunctions X) Z.1 *
      (secVal (G.divisorialSheaf.val.map (homOfLE (le_top : U ≤ ⊤)).op t) Z -
        X.presheaf.germ U _ Z.2 r' *
          secVal (G.divisorialSheaf.val.map (homOfLE (le_top : U ≤ ⊤)).op s) Z)
    ring
  rw [mem_nonvanishingLocus_iff_isUnit_germ hψ _ _ ha' hxU]
  intro hunit
  rw [map_sub, map_mul] at hunit
  have hr'x : X.presheaf.germ U x hxU r' = algebraMap k _ c := by
    rw [hr', TopCat.Presheaf.germ_res_apply]; rfl
  rw [hr'x] at hunit
  have hm : X.presheaf.germ U x hxU b * ↑(hua.unit⁻¹) - algebraMap k _ c ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ← hc, Ideal.Quotient.mk_algebraMap, sub_self]
  have heq : X.presheaf.germ U x hxU b - algebraMap k _ c * X.presheaf.germ U x hxU a =
      (X.presheaf.germ U x hxU b * ↑(hua.unit⁻¹) - algebraMap k _ c) *
        X.presheaf.germ U x hxU a := by
    have h1 : (↑(hua.unit⁻¹) : X.presheaf.stalk x) * X.presheaf.germ U x hxU a = 1 :=
      hua.val_inv_mul
    rw [sub_mul, mul_assoc, h1, mul_one]
  rw [heq] at hunit
  exact (IsLocalRing.mem_maximalIdeal _).mp (Ideal.mul_mem_right _ _ hm) hunit

end Evaluation

/-! ### The free pencil -/

section Conclusion

/-- The rational function of `a - r • b` is that of `a` minus `r` times that of `b`. -/
private theorem sectionToRationalFunctions_sub_smul {X : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral X] [CompactSpace X] (r : Γ(X, ⊤)) {D : Divisor X}
    (a b : D.divisorialSubmodule ⊤) :
    Divisor.sectionToRationalFunctions (a - r • b) = Divisor.sectionToRationalFunctions a -
      rationalFunctionsPresheafTopEquiv X (algebraMap Γ(X, ⊤) _ r) *
        Divisor.sectionToRationalFunctions b := by
  change rationalFunctionsPresheafTopEquiv X (a.1 - algebraMap Γ(X, ⊤) _ r * b.1) = _
  rw [map_sub, map_mul]
  rfl

/-- A point of `D` in the support of `n B + (Z - d D)`, with `B` and `Z - mult_D Z · D` disjoint
from `D` and `B` not containing `D`, forces `d < mult_D Z`. -/
private theorem lt_coeff_of_mem_supp {X : Scheme.{u}} (E : Mori.PrimeDivisor X)
    {B Z : Divisor X} {n d : ℤ} {x : X} (hxE : x ∈ (E.support : Set X))
    (hB : Disjoint (E.support : Set X) (B.supp : Set X)) (hBE : B E = 0)
    (hZ : Disjoint (E.support : Set X) ((Z - Finsupp.single E (Z E)).supp : Set X))
    (h0 : 0 ≤ n • B + (Z - Finsupp.single E d))
    (hx : x ∈ ((n • B + (Z - Finsupp.single E d)).supp : Set X)) : d < Z E := by
  have hxZ : x ∈ ((Z - Finsupp.single E d).supp : Set X) := by
    rcases DivisorWithCoeffs.supp_add_le _ _ hx with h | h
    · obtain ⟨P, hP, hxP⟩ := DivisorWithCoeffs.mem_supp_iff.mp h
      change n * B P ≠ 0 at hP
      exact absurd (DivisorWithCoeffs.mem_supp_iff.mpr ⟨P, right_ne_zero_of_mul hP, hxP⟩)
        (Set.disjoint_left.mp hB hxE)
    · exact h
  have hge := h0 E
  simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.add_apply, Finsupp.sub_apply,
    Finsupp.smul_apply, smul_eq_mul, hBE, mul_zero, zero_add, Finsupp.single_eq_same] at hge
  refine lt_of_le_of_ne (by omega) fun hEq => ?_
  rw [hEq] at hxZ
  exact Set.disjoint_left.mp hZ hxE hxZ

/-- **Evaluating the ratio at a point of `D`.** With `G = N M - N d D`, sections `s₀ ↦ σ^N` and
`s₁ ↦ σ^{N-1} τ` of `𝒪_X(G)` and `x₀ ∈ D` a zero of `s₁ - c s₀`, the member `τ - c σ` has
multiplicity along `D` larger than `d = mult_D (σ)₀`. -/
private theorem coeff_lt_of_notMem_nonvanishingLocus {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X] [CompactSpace X]
    {M : Divisor X} (E : Mori.PrimeDivisor X)
    (hstar : ∀ (σ : M.divisorialSubmodule ⊤) (hσ : σ ≠ 0), Disjoint (E.support : Set X)
      ((M.zeroDivisor σ hσ - Finsupp.single E (M.zeroDivisor σ hσ E)).supp : Set X))
    {σ τ : M.divisorialSubmodule ⊤} (hσ : σ ≠ 0) (hτ : τ ≠ 0) {x₀ : X}
    (hx₀E : x₀ ∈ (E.support : Set X)) {N : ℕ} (hN : 0 < N) {G : Divisor X}
    (hG : G = (N : ℤ) • M - M.zeroDivisor σ hσ E • ((N : ℤ) • Finsupp.single E 1))
    (hGc : G.IsCartier) (s₀ s₁ : G.divisorialSubmodule ⊤)
    (hs₀φ : Divisor.sectionToRationalFunctions s₀ =
      ((Divisor.isUnit_sectionToRationalFunctions hσ).unit ^ N : (RationalFunctions X)ˣ))
    (hs₁φ : Divisor.sectionToRationalFunctions s₁ =
      ((Divisor.isUnit_sectionToRationalFunctions hσ).unit ^ (N - 1) *
        (Divisor.isUnit_sectionToRationalFunctions hτ).unit : (RationalFunctions X)ˣ))
    (c : k) (hc : x₀ ∉ Stacks.Ample.nonvanishingLocus G.divisorialSheaf
      (s₁ - (scalarsToGlobalSections k sX c : Γ(X, ⊤)) • s₀ : G.divisorialSubmodule ⊤))
    (hτ'0 : τ - (scalarsToGlobalSections k sX c : Γ(X, ⊤)) • σ ≠ 0) :
    M.zeroDivisor σ hσ E < M.zeroDivisor _ hτ'0 E := by
  classical
  have := hGc.isInvertibleModule_divisorialSheaf
  set d := M.zeroDivisor σ hσ E with hd
  set ψσ := (Divisor.isUnit_sectionToRationalFunctions hσ).unit with hψσ
  set ψτ := (Divisor.isUnit_sectionToRationalFunctions hτ).unit with hψτ
  set Bσ := M.zeroDivisor σ hσ - Finsupp.single E d with hBσ
  set r : Γ(X, ⊤) := scalarsToGlobalSections k sX c with hr
  set τ' : M.divisorialSubmodule ⊤ := τ - r • σ with hτ'
  set s' : G.divisorialSubmodule ⊤ := s₁ - r • s₀ with hs'def
  have hN1 : ((N - 1 : ℕ) : ℤ) = (N : ℤ) - 1 := by omega
  have hτ'φ : Divisor.sectionToRationalFunctions τ' =
      (ψτ : RationalFunctions X) - rationalFunctionsPresheafTopEquiv X
        (algebraMap Γ(X, ⊤) _ r) * (ψσ : RationalFunctions X) := by
    rw [hτ', sectionToRationalFunctions_sub_smul,
      (Divisor.isUnit_sectionToRationalFunctions hτ).unit_spec,
      (Divisor.isUnit_sectionToRationalFunctions hσ).unit_spec]
  have hs'φ : Divisor.sectionToRationalFunctions s' =
      ((ψσ ^ (N - 1) : (RationalFunctions X)ˣ) : RationalFunctions X) *
        Divisor.sectionToRationalFunctions τ' := by
    rw [hs'def, sectionToRationalFunctions_sub_smul, hs₀φ, hs₁φ, hτ'φ]
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    simp only [Nat.add_sub_cancel, Units.val_mul, Units.val_pow_eq_pow_val, pow_succ]
    ring
  have : Nontrivial (RationalFunctions X) :=
    (rationalFunctionsEquivFunctionField X).toEquiv.nontrivial
  have hs' : s' ≠ 0 := by
    intro h
    have h0 : Divisor.sectionToRationalFunctions s' = 0 := by rw [h]; exact map_zero _
    rw [hs'φ] at h0
    exact ((ψσ ^ (N - 1)).isUnit.mul
      (Divisor.isUnit_sectionToRationalFunctions hτ'0)).ne_zero h0
  have hunit : (Divisor.isUnit_sectionToRationalFunctions hs').unit =
      ψσ ^ (N - 1) * (Divisor.isUnit_sectionToRationalFunctions hτ'0).unit := by
    ext
    rw [(Divisor.isUnit_sectionToRationalFunctions hs').unit_spec, Units.val_mul,
      (Divisor.isUnit_sectionToRationalFunctions hτ'0).unit_spec, hs'φ]
  have hZs' : G.zeroDivisor s' hs' =
      ((N : ℤ) - 1) • Bσ + (M.zeroDivisor τ' hτ'0 - Finsupp.single E d) := by
    rw [Divisor.zeroDivisor_eq, hunit, MMP.Mori.principalDivisor_mul, principalDivisor_pow,
      M.zeroDivisor_eq τ' hτ'0, hG, hBσ, M.zeroDivisor_eq σ hσ]
    refine Finsupp.ext fun P => ?_
    simp only [Finsupp.add_apply, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul,
      nsmul_eq_mul, Finsupp.single_apply, hN1]
    split_ifs <;> ring
  have hx₀s' : x₀ ∈ ((G.zeroDivisor s' hs').supp : Set X) := by
    have hc' : x₀ ∉ Stacks.Ample.nonvanishingLocus G.divisorialSheaf s' := hc
    rw [nonvanishingLocus_eq_compl_supp_zeroDivisor hGc s' hs'] at hc'
    simpa using hc'
  rw [hZs'] at hx₀s'
  exact lt_coeff_of_mem_supp E hx₀E (hstar σ hσ) (by simp [hBσ, hd]) (hstar τ' hτ'0)
    (hZs' ▸ G.zeroDivisor_nonneg s' hs') hx₀s'

/-- **Equal multiplicities along `D`.** If `(σ)₀` and `(τ)₀` have the same multiplicity along `D`
and every member of `|M|` meets `D` only along `D`, some member `τ - c σ` of the pencil has
larger multiplicity along `D` than `(σ)₀`. -/
private theorem exists_coeff_lt_sub_smul_of_coeff_eq {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X]
    [CompactSpace X] (hX : Mori.IsProjectiveVariety k sX) (hQ : Fourfold.IsQFactorial sX)
    {M : Divisor X} (hMc : M.IsCartier) (E : Mori.PrimeDivisor X)
    (hstar : ∀ (σ : M.divisorialSubmodule ⊤) (hσ : σ ≠ 0), Disjoint (E.support : Set X)
      ((M.zeroDivisor σ hσ - Finsupp.single E (M.zeroDivisor σ hσ E)).supp : Set X))
    {σ τ : M.divisorialSubmodule ⊤} (hσ : σ ≠ 0) (hτ : τ ≠ 0)
    (heq : M.zeroDivisor σ hσ E = M.zeroDivisor τ hτ E) :
    ∃ c : k, ∀ hτ' : τ - (scalarsToGlobalSections k sX c : Γ(X, ⊤)) • σ ≠ 0,
      M.zeroDivisor σ hσ E < M.zeroDivisor _ hτ' E := by
  classical
  have : LocallyOfFiniteType sX := hX.toIsVariety.toLocallyOfFiniteType
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  set d := M.zeroDivisor σ hσ E
  have hEc : IsClosed (E.support : Set X) := E.idealSheaf.support.isClosed
  obtain ⟨x₀, hx₀E, hx₀c⟩ := nonempty_inter_closedPoints
    ⟨E.genericPoint, MMP.Flips.primeDivisor_genericPoint_mem_support E⟩ hEc.isLocallyClosed
  obtain ⟨N, hN, hNc⟩ := hQ.2 (Finsupp.single E 1)
  set G : Divisor X := (N : ℤ) • M - d • ((N : ℤ) • Finsupp.single E 1) with hG
  have hGc : G.IsCartier := (hMc.zsmul _).sub (hNc.zsmul d)
  have := hGc.isInvertibleModule_divisorialSheaf
  set ψσ := (Divisor.isUnit_sectionToRationalFunctions hσ).unit with hψσ
  set ψτ := (Divisor.isUnit_sectionToRationalFunctions hτ).unit with hψτ
  set Bσ := M.zeroDivisor σ hσ - Finsupp.single E d with hBσ
  set Bτ := M.zeroDivisor τ hτ - Finsupp.single E d with hBτ
  have hBσ0 : 0 ≤ Bσ := sub_single_coeff_nonneg (M.zeroDivisor_nonneg σ hσ) E
  have hBτ0 : 0 ≤ Bτ := by
    have := sub_single_coeff_nonneg (M.zeroDivisor_nonneg τ hτ) E
    rwa [← heq] at this
  have hN1 : ((N - 1 : ℕ) : ℤ) = (N : ℤ) - 1 := by omega
  have hdiv₀ : principalDivisor (ψσ ^ N) + G = (N : ℤ) • Bσ := by
    rw [principalDivisor_pow, hG, hBσ, M.zeroDivisor_eq σ hσ]
    refine Finsupp.ext fun P => ?_
    simp only [Finsupp.add_apply, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul,
      nsmul_eq_mul, Finsupp.single_apply]
    split_ifs <;> ring
  have hdiv₁ : principalDivisor (ψσ ^ (N - 1) * ψτ) + G = ((N : ℤ) - 1) • Bσ + Bτ := by
    rw [MMP.Mori.principalDivisor_mul, principalDivisor_pow, hG, hBσ, hBτ,
      M.zeroDivisor_eq σ hσ, M.zeroDivisor_eq τ hτ]
    refine Finsupp.ext fun P => ?_
    simp only [Finsupp.add_apply, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul,
      nsmul_eq_mul, Finsupp.single_apply, hN1]
    split_ifs <;> ring
  obtain ⟨s₀, hs₀, hs₀e, hs₀φ⟩ := exists_section_of_nonneg (D := G) (ψσ ^ N)
    (by rw [hdiv₀]; exact smul_nonneg (by positivity) hBσ0)
  obtain ⟨s₁, -, -, hs₁φ⟩ := exists_section_of_nonneg (D := G) (ψσ ^ (N - 1) * ψτ)
    (by rw [hdiv₁]; exact add_nonneg (smul_nonneg (by omega) hBσ0) hBτ0)
  have hx₀s₀ : x₀ ∈ Stacks.Ample.nonvanishingLocus G.divisorialSheaf s₀ := by
    rw [nonvanishingLocus_eq_compl_supp_zeroDivisor hGc s₀ hs₀, hs₀e, hdiv₀,
      supp_zsmul (by exact_mod_cast hN.ne')]
    exact fun h => Set.disjoint_left.mp (hstar σ hσ) hx₀E h
  obtain ⟨c, hc⟩ := exists_notMem_nonvanishingLocus_sub_smul sX hGc s₀ s₁ hx₀c hx₀s₀
  exact ⟨c, coeff_lt_of_notMem_nonvanishingLocus E hstar hσ hτ hx₀E hN hG hGc s₀ s₁ hs₀φ hs₁φ
    c hc⟩

/-- **Two members with different multiplicities along `D`.** If `h⁰(X, 𝒪_X(M)) ≥ 2` and every
member of `|M|` meets `D` only along `D`, there are two members `Z₀ ≰ Z₁` with
`mult_D Z₀ < mult_D Z₁`. -/
private theorem exists_sections_coeff_lt {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X] [CompactSpace X]
    (hX : Mori.IsProjectiveVariety k sX) (hQ : Fourfold.IsQFactorial sX) {M : Divisor X}
    (hMc : M.IsCartier) (h2 : 2 ≤ M.h0 k sX) (E : Mori.PrimeDivisor X)
    (hstar : ∀ (σ : M.divisorialSubmodule ⊤) (hσ : σ ≠ 0), Disjoint (E.support : Set X)
      ((M.zeroDivisor σ hσ - Finsupp.single E (M.zeroDivisor σ hσ E)).supp : Set X)) :
    ∃ (σ₀ σ₁ : M.divisorialSubmodule ⊤) (hσ₀ : σ₀ ≠ 0) (hσ₁ : σ₁ ≠ 0),
      ¬ M.zeroDivisor σ₀ hσ₀ ≤ M.zeroDivisor σ₁ hσ₁ ∧
        M.zeroDivisor σ₀ hσ₀ E < M.zeroDivisor σ₁ hσ₁ E := by
  classical
  have : IsProper sX := isProper_of_isProjectiveMorphism sX hX.isProjective
  letI := Module.compHom (M.divisorialSubmodule ⊤) (scalarsToGlobalSections k sX)
  have h2' : 1 < Module.finrank k (M.divisorialSubmodule ⊤) := h2
  have : Module.Finite k (M.divisorialSubmodule ⊤) :=
    Module.finite_of_finrank_pos (lt_trans zero_lt_one h2')
  have : Nontrivial (M.divisorialSubmodule ⊤) :=
    Module.nontrivial_of_finrank_pos (R := k) (lt_trans zero_lt_one h2')
  obtain ⟨σ, hσ⟩ := exists_ne (0 : M.divisorialSubmodule ⊤)
  obtain ⟨τ, hli⟩ := exists_linearIndependent_pair_of_one_lt_finrank h2' hσ
  have hτ : τ ≠ 0 := by simpa using hli.ne_zero 1
  have hpair := LinearIndependent.pair_iff.mp hli
  have hnotle : ∀ (ρ : M.divisorialSubmodule ⊤) (hρ : ρ ≠ 0) (c' : k), ρ = τ - c' • σ →
      ¬ M.zeroDivisor σ hσ ≤ M.zeroDivisor ρ hρ ∧ ¬ M.zeroDivisor ρ hρ ≤ M.zeroDivisor σ hσ := by
    intro ρ hρ c' hρe
    refine ⟨fun hle => ?_, fun hle => ?_⟩
    · obtain ⟨c, hc⟩ := exists_eq_smul_of_zeroDivisor_le sX hσ hρ hle
      have hc' : ρ = c • σ := hc
      have hτe : τ = (c + c') • σ := by rw [add_smul, ← hc', hρe, sub_add_cancel]
      exact one_ne_zero (hpair (-(c + c')) 1 (by
        rw [hτe, one_smul, ← add_smul, neg_add_cancel, zero_smul])).2
    · obtain ⟨c, hc⟩ := exists_eq_smul_of_zeroDivisor_le sX hρ hσ hle
      have hc' : σ = c • ρ := hc
      obtain ⟨h₁, h₂⟩ := hpair (1 + c * c') (-c) (by
        have h1 : (1 + c * c') • σ + (-c) • τ = σ - c • (τ - c' • σ) := by
          rw [smul_sub, smul_smul, add_smul, one_smul, neg_smul]
          abel
        rw [h1, ← hρe, ← hc', sub_self])
      rw [neg_eq_zero.mp h₂, zero_mul, add_zero] at h₁
      exact one_ne_zero h₁
  rcases lt_trichotomy (M.zeroDivisor σ hσ E) (M.zeroDivisor τ hτ E) with hlt | heq | hgt
  · exact ⟨σ, τ, hσ, hτ, (hnotle τ hτ 0 (by rw [zero_smul, sub_zero])).1, hlt⟩
  · obtain ⟨c, hc⟩ := exists_coeff_lt_sub_smul_of_coeff_eq hX hQ hMc E hstar hσ hτ heq
    have hτ'0 : τ - c • σ ≠ 0 := fun h =>
      one_ne_zero (hpair (-c) 1 (by rw [one_smul, neg_smul, neg_add_eq_sub]; exact h)).2
    exact ⟨σ, τ - c • σ, hσ, hτ'0, (hnotle _ hτ'0 c rfl).1, hc hτ'0⟩
  · exact ⟨τ, σ, hτ, hσ, (hnotle τ hτ 0 (by rw [zero_smul, sub_zero])).2, hgt⟩

/-- A nonzero divisor has nonempty support. -/
private theorem nonempty_supp_of_ne_zero {X : Scheme.{u}} {G : Divisor X} (hG : G ≠ 0) :
    (G.supp : Set X).Nonempty := by
  obtain ⟨P, hP⟩ := DFunLike.ne_iff.mp hG
  refine ⟨P.genericPoint, DivisorWithCoeffs.mem_supp_iff.mpr ⟨P, hP, ?_⟩⟩
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact subset_closure rfl

/-- **Fixed components avoid one moving part.** For the pencil spanned by `Z₀, Z₁` with moving
parts `Z_i - Z₀ ⊓ Z₁` disjoint and defining `p : X ⟶ C`, every fixed component `P` is disjoint
from one of the moving parts. -/
private theorem disjoint_or_disjoint_of_inf_ne_zero {k : Type u} [Field k] {X C : Scheme.{u}}
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian C] [CompactSpace C] {sC : C ⟶ Spec (.of k)}
    (hC : Mori.IsProjectiveVariety k sC) (hdimC : topologicalKrullDim C = 1) (p : X ⟶ C)
    (hp : ∀ U : C.Opens, IsIso (p.app U)) (hpp : IsProjectiveMorphism p) {Z₀ Z₁ : Divisor X}
    (hZ₀0 : 0 ≤ Z₀) (hZ₁0 : 0 ≤ Z₁) (E : Mori.PrimeDivisor X) (hlt : Z₀ E < Z₁ E)
    (h₀ : Disjoint (E.support : Set X) ((Z₀ - Finsupp.single E (Z₀ E)).supp : Set X))
    (h₁ : Disjoint (E.support : Set X) ((Z₁ - Finsupp.single E (Z₁ E)).supp : Set X))
    (hdisj : Disjoint ((Z₀ - Z₀ ⊓ Z₁).supp : Set X) ((Z₁ - Z₀ ⊓ Z₁).supp : Set X))
    (hsat₁ : ∀ x y : X, p x = p y →
      (x ∈ ((Z₁ - Z₀ ⊓ Z₁).supp : Set X) ↔ y ∈ ((Z₁ - Z₀ ⊓ Z₁).supp : Set X)))
    (hvert₀ : ∀ T : Set X, IsIrreducible T → IsClosed T →
      Disjoint T (Z₀ - Z₀ ⊓ Z₁).supp → (p '' T).Subsingleton)
    (P : Mori.PrimeDivisor X) (hP : (Z₀ ⊓ Z₁) P ≠ 0) :
    Disjoint (P.support : Set X) (Z₀ - Z₀ ⊓ Z₁).supp ∨
      Disjoint (P.support : Set X) (Z₁ - Z₀ ⊓ Z₁).supp := by
  have hZ₀P : Z₀ P ≠ 0 := by
    have h1 := hZ₀0 P
    have h2 := hZ₁0 P
    simp only [Finsupp.coe_zero, Pi.zero_apply] at h1 h2
    rw [Finsupp.inf_apply] at hP
    omega
  have hM₁E : (Z₁ - Z₀ ⊓ Z₁) E ≠ 0 := by
    simp only [Finsupp.coe_sub, Pi.sub_apply, Finsupp.inf_apply]
    omega
  have hsuppc : ∀ Q : Mori.PrimeDivisor X, IsClosed (Q.support : Set X) := fun Q =>
    Q.idealSheaf.support.isClosed
  have hsuppi : ∀ Q : Mori.PrimeDivisor X, IsIrreducible (Q.support : Set X) := fun Q => by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact isIrreducible_singleton.closure
  have hM₀E : Disjoint (E.support : Set X) (Z₀ - Z₀ ⊓ Z₁).supp :=
    h₀.mono_right (supp_sub_inf_subset_supp_sub_single hZ₀0 hZ₁0 E hlt.le)
  by_cases hPE : P = E
  · subst hPE
    exact Or.inl hM₀E
  have hPsub : (P.support : Set X) ⊆ (Z₀ - Finsupp.single E (Z₀ E)).supp :=
    DivisorWithCoeffs.support_subset_supp (by
      simpa [DivisorWithCoeffs.coeff_apply, Finsupp.single_eq_of_ne' (Ne.symm hPE)] using hZ₀P)
  have hPE' : Disjoint (P.support : Set X) E.support := (h₀.mono_right hPsub).symm
  by_cases hsub : (p '' P.support).Subsingleton
  · by_contra hcon
    rw [not_or, Set.not_disjoint_iff, Set.not_disjoint_iff] at hcon
    obtain ⟨⟨x, hxP, hx₀⟩, ⟨y, hyP, hy₁⟩⟩ := hcon
    exact Set.disjoint_left.mp hdisj hx₀
      ((hsat₁ x y (hsub ⟨x, hxP, rfl⟩ ⟨y, hyP, rfl⟩)).2 hy₁)
  exfalso
  have : IsIntegral C := hC.toIsVariety.toIsIntegral
  have : AlgebraicGeometry.IsNoetherian C := ⟨⟩
  have : IsProper p := (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mp hpp).2
  have himg : p '' P.support = Set.univ := by
    by_contra h
    exact hsub (subsingleton_of_isClosed_of_isPreconnected hdimC.le _
      (p.isClosedMap _ (hsuppc P))
      ((hsuppi P).image p p.continuous.continuousOn).isConnected.isPreconnected h)
  have hξ : E.genericPoint ∈ (E.support : Set X) :=
    MMP.Flips.primeDivisor_genericPoint_mem_support E
  obtain ⟨y, hyP, hyξ⟩ : p E.genericPoint ∈ p '' P.support := by rw [himg]; trivial
  have hfib : _root_.IsConnected (p ⁻¹' {p E.genericPoint}) :=
    p.isConnected_preimage_singleton_of_isIso_app hp _
  have hEM₁ : (E.support : Set X) ⊆ (Z₁ - Z₀ ⊓ Z₁).supp :=
    DivisorWithCoeffs.support_subset_supp hM₁E
  have hfibM₁ : p ⁻¹' {p E.genericPoint} ⊆ (Z₁ - Z₀ ⊓ Z₁).supp := fun z hz =>
    (hsat₁ z E.genericPoint hz).2 (hEM₁ hξ)
  have hEfib : (E.support : Set X) ⊆ p ⁻¹' {p E.genericPoint} := fun e he =>
    hvert₀ E.support (hsuppi E) (hsuppc E) hM₀E ⟨e, he, rfl⟩ ⟨E.genericPoint, hξ, rfl⟩
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hfib.isPreconnected) _ _ (hsuppc E)
      (DivisorWithCoeffs.isClosed_supp _) (hfibM₁.trans (supp_sub_inf_subset_union hZ₀0 hZ₁0 E))
      (by rw [Set.disjoint_iff_inter_eq_empty.mp h₁, Set.inter_empty]) with h | h
  · exact Set.disjoint_left.mp hPE' hyP (h hyξ)
  · exact Set.disjoint_left.mp h₁ hξ (h (hEfib hξ))

/-- **The free pencil.** Two members `Z₀ ≰ Z₁` of `|M|`, `M = m L`, with
`mult_D Z₀ < mult_D Z₁`, each meeting `D` only along `D`, span a pencil whose moving parts are
disjoint; it defines a fibration onto a smooth projective curve along which `L` is
`ℚ`-linearly equivalent to the pull-back of an ample divisor. -/
private theorem isEventuallyFreePencil_of_coeff_lt {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X]
    [CompactSpace X] [QuasiCompact sX]
    (hX : Mori.IsProjectiveVariety k sX) (hQ : Fourfold.IsQFactorial sX) {L : QDivisor X}
    (hL : L.IsNef k sX) {m : ℕ} (hm : 0 < m) {M : Divisor X} (hMc : M.IsCartier)
    (hML : Divisor.toQDivisor M = (m : ℤ) • L) (E : Mori.PrimeDivisor X)
    (σ₀ σ₁ : M.divisorialSubmodule ⊤) (hσ₀ : σ₀ ≠ 0) (hσ₁ : σ₁ ≠ 0)
    (hle : ¬ M.zeroDivisor σ₀ hσ₀ ≤ M.zeroDivisor σ₁ hσ₁)
    (hlt : M.zeroDivisor σ₀ hσ₀ E < M.zeroDivisor σ₁ hσ₁ E)
    (h₀ : Disjoint (E.support : Set X) ((M.zeroDivisor σ₀ hσ₀ -
      Finsupp.single E (M.zeroDivisor σ₀ hσ₀ E)).supp : Set X))
    (h₁ : Disjoint (E.support : Set X) ((M.zeroDivisor σ₁ hσ₁ -
      Finsupp.single E (M.zeroDivisor σ₁ hσ₁ E)).supp : Set X)) :
    IsEventuallyFreePencil k sX L := by
  classical
  set Z₀ := M.zeroDivisor σ₀ hσ₀ with hZ₀def
  set Z₁ := M.zeroDivisor σ₁ hσ₁ with hZ₁def
  set ψ₀ := (Divisor.isUnit_sectionToRationalFunctions hσ₀).unit
  set ψ₁ := (Divisor.isUnit_sectionToRationalFunctions hσ₁).unit
  have hψ₀ : Z₀ = principalDivisor ψ₀ + M := M.zeroDivisor_eq σ₀ hσ₀
  have hψ₁ : Z₁ = principalDivisor ψ₁ + M := M.zeroDivisor_eq σ₁ hσ₁
  have hψ : Z₁ = principalDivisor (ψ₁ * ψ₀⁻¹) + Z₀ := by
    rw [hψ₁, hψ₀, MMP.Mori.principalDivisor_mul, MMP.Mori.principalDivisor_inv]
    abel
  have hZ₀0 : 0 ≤ Z₀ := M.zeroDivisor_nonneg σ₀ hσ₀
  have hZ₁0 : 0 ≤ Z₁ := M.zeroDivisor_nonneg σ₁ hσ₁
  have hdisj := disjoint_supp_sub_inf hX hQ hZ₀0 hZ₁0 _ hψ E hlt h₀ h₁
  have hne₀ : Z₀ - Z₀ ⊓ Z₁ ≠ 0 := fun h0 => hle (sub_eq_zero.mp h0 ▸ inf_le_right)
  have hM₁E : (Z₁ - Z₀ ⊓ Z₁) E ≠ 0 := by
    simp only [Finsupp.coe_sub, Pi.sub_apply, Finsupp.inf_apply]
    omega
  have hne₁ : Z₁ - Z₀ ⊓ Z₁ ≠ 0 := fun h => hM₁E (by rw [h]; rfl)
  obtain ⟨hMc', τ₀, τ₁, hτ₀, hτ₁, hτ₀e, hτ₁e⟩ := exists_sections_of_disjoint hZ₀0 hZ₁0 _ hψ hdisj
  obtain ⟨C, _, _, _, sC, hC, hdimC, hCsm, p, hps, hp, hpsurj, hpp, hsat₀, hsat₁, hvert₀,
      hvert₁⟩ :=
    exists_curve_of_pencil hX hMc' τ₀ τ₁ hτ₀ hτ₁ (by rwa [hτ₀e, hτ₁e])
      (by rw [hτ₀e]; exact nonempty_supp_of_ne_zero hne₀)
      (by rw [hτ₁e]; exact nonempty_supp_of_ne_zero hne₁)
  rw [hτ₀e] at hsat₀ hvert₀
  rw [hτ₁e] at hsat₁ hvert₁
  have hF := disjoint_or_disjoint_of_inf_ne_zero hC hdimC p hp hpp hZ₀0 hZ₁0 E hlt h₀ h₁ hdisj
    hsat₁ hvert₀
  have := hpsurj
  obtain ⟨N, hN, n, hn, A, hA, hAc, hAa, hB, hLN⟩ := exists_pullback_of_pencil hX hQ hL hm hMc hML
    hZ₀0 hZ₁0 ψ₀ _ hψ₀ hψ hne₀ hdisj hF sC hC hdimC hCsm p hps hp hpp hvert₀ hvert₁
  exact (isEventuallyFreePencil_iff_of_qLinearlyEquivalent_pullback k sX sC hX hC p hps hp hL.1 hN
    ⟨hB, hLN⟩).mpr (isEventuallyFreePencil_of_isAmple_of_curve sC hC hdimC N n hn A hA hAc hAa)

end Conclusion

/-- **FA Lemma 15.7.** Let `X` be a normal projective `ℚ`-factorial variety over an algebraically
closed field `k`, `K_X` a canonical divisor and `Δ_X` a `ℚ`-divisor with `L = K_X + Δ_X` nef,
and suppose `h⁰(X, 𝒪_X(M)) ≥ 2` for the Cartier divisor `M = m₀ L`, `m₀ > 0`. Let `D` be an
`L`-trivially connected prime divisor (`MMP.Flips.IsTriviallyConnected`). Then either `L` is
eventually free and composed of a pencil (`MMP.Flips.IsEventuallyFreePencil`), or there are an
effective divisor `D'` and integers `d ≥ 1`, `m > 0` such that `m L` is an integral divisor `M`
with `d D + D' ∼ M`, `D ⊄ Supp D'` and `D ∩ Supp D' ≠ ∅`. -/
@[mmp "lem_fa15_trivially_connected_dichotomy"]
public theorem isEventuallyFreePencil_or_exists_mem_linearSystem_of_isTriviallyConnected
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [QuasiCompact sX] (hX : Mori.IsProjectiveVariety k sX) (hQ : Fourfold.IsQFactorial sX)
    (n : ℕ) (K : Divisor X) (Δ : QDivisor X)
    (hnef : (Divisor.toQDivisor K + Δ).IsNef k sX)
    (hm₀ : ∃ m₀ : ℕ, 0 < m₀ ∧ ∃ M : Divisor X,
      Divisor.toQDivisor M = (m₀ : ℤ) • (Divisor.toQDivisor K + Δ) ∧ M.IsCartier ∧
        2 ≤ M.h0 k sX)
    (E : Mori.PrimeDivisor X) (hD : IsTriviallyConnected k sX n K Δ (Finsupp.single E 1)) :
    IsEventuallyFreePencil k sX (Divisor.toQDivisor K + Δ) ∨
      ∃ D' : Divisor X, D'.IsEffective ∧ ∃ d m : ℕ, 1 ≤ d ∧ 0 < m ∧ ∃ M : Divisor X,
        Divisor.toQDivisor M = (m : ℤ) • (Divisor.toQDivisor K + Δ) ∧
        Divisor.LinearlyEquivalent ((d : ℤ) • (Finsupp.single E 1 : Divisor X) + D') M ∧
        ¬ (DivisorWithCoeffs.supp (Finsupp.single E 1 : Divisor X) : Set X) ⊆
          (DivisorWithCoeffs.supp D' : Set X) ∧
        ((DivisorWithCoeffs.supp (Finsupp.single E 1 : Divisor X) : Set X) ∩
          (DivisorWithCoeffs.supp D' : Set X)).Nonempty := by
  classical
  refine or_iff_not_imp_right.mpr fun hB => ?_
  have : IsIntegral X := hX.toIsVariety.toIsIntegral
  obtain ⟨m₀, hm₀pos, M, hML, hMc, h2⟩ := hm₀
  have hstar : ∀ (σ : M.divisorialSubmodule ⊤) (hσ : σ ≠ 0), Disjoint (E.support : Set X)
      ((M.zeroDivisor σ hσ - Finsupp.single E (M.zeroDivisor σ hσ E)).supp : Set X) :=
    fun σ hσ => disjoint_support_supp_sub_single sX n K Δ E hD hm₀pos hML hMc hB
      (M.zeroDivisor_nonneg σ hσ) ⟨(Divisor.isUnit_sectionToRationalFunctions hσ).unit, by
        rw [M.zeroDivisor_eq σ hσ, add_sub_cancel_right]⟩
  obtain ⟨σ₀, σ₁, hσ₀, hσ₁, hle, hlt⟩ := exists_sections_coeff_lt hX hQ hMc h2 E hstar
  exact isEventuallyFreePencil_of_coeff_lt hX hQ hnef hm₀pos hMc hML E σ₀ σ₁ hσ₀ hσ₁ hle hlt
    (hstar σ₀ hσ₀) (hstar σ₁ hσ₁)

end MMP.Flips
