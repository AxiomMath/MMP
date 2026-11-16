module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Contraction.LineBundleDescent
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
public import MMP.AlgebraicGeometry.MMP.Fourfold.Singularities
public import MMP.AlgebraicGeometry.Intersection.RCartierCurveDegree
public import MMP.AlgebraicGeometry.CohenMacaulay.SerreDuality
public import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
public import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms
public import MMP.AlgebraicGeometry.Positivity.RelativeAmpleExceptionalCurve
public import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
public import MMP.AlgebraicGeometry.Morphisms.GenericallyFinite
public import MMP.AlgebraicGeometry.MMP.Threefold.SurfaceLocalRings
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.DimensionFormula
public import MMP.AlgebraicGeometry.MMP.Abundance.Basic
public import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
public import MMP.AlgebraicGeometry.Curves.NormalizationLiftInvertible
public import MMP.AlgebraicGeometry.Curves.RationalFunctionDegree
public import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
public import MMP.AlgebraicGeometry.SpreadingOut.CartesianFibres
public import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
public import MMP.AlgebraicGeometry.Positivity.Kleiman.RelativeCartier
public import MMP.AlgebraicGeometry.Divisor.ExceptionalEffectivePushforward
public import MMP.AlgebraicGeometry.Resolution.TransformRestriction
public import MMP.AlgebraicGeometry.MMP.MinimalModel.NefWeakModelStep
public import MMP.AlgebraicGeometry.Chow.FieldSituation

section

/-!
# The connected-floor cases of a threefold Mori endpoint

Let `r : Y ⟶ V` be the contraction of an extremal ray `R` of a `ℚ`-factorial projective threefold
over an algebraically closed field of characteristic zero, `B ≥ 0` a `ℚ`-divisor with `K + B`
numerically `r`-trivial, and `ε > 0` such that `-(K + B - ε⌊B⌋)` is `r`-ample. Put `T = ⌊B⌋`. If
`dim V ≤ 1`, or `dim V = 2` and the horizontal part of `T` has degree one over `V`, then every
fibre of `T ⟶ V` is connected and nonempty and `r_* 𝒪_T = 𝒪_V`.

The floor is positive on every contracted curve, since `ε T ≡_r -(K + B - ε T)`. Since the
contracted classes span the ray `R`, a prime divisor `E` with `r(E) ≠ V` is trivial on
contracted curves: it misses a curve in a fibre away from `r(E)`. Hence `E` contains every closed
fibre that it meets. Otherwise a curve in that connected fibre, through a closed point of `E` and
not contained in `E`, would meet `E` positively. Over a curve this makes every closed fibre the
support of one prime divisor. Over a surface it makes a fibre either lie inside `T` or meet `T`
only in the unique horizontal component `S`. That component is birational to the normal surface
`V`, so its fibres are connected by Zariski's main theorem.

In fibre dimension at least two a multiple of `T` is `r`-ample, by the relative Kleiman
criterion: relative curve classes form one ray. On the normalization of an irreducible closed
fibre that meets `T` properly, the pulled-back canonical section of this multiple is a regular
section of an ample line bundle. The normalization has depth at least two at its closed points,
so the zero scheme of the section is connected. That zero scheme maps onto the intersection of
`T` with the fibre.

Finally, a proper morphism from a reduced scheme onto a normal variety whose closed fibres are
connected and nonempty has `f_* 𝒪 = 𝒪`. Its Stein factorization is finite, bijective and
integral, so it is an isomorphism. Connectedness of all fibres then follows from `f_* 𝒪 = 𝒪`.

## Main results

* `MMP.Fourfold.IsContractionOfRay.isConnected_fibre_floor_and_isIso_app`: the connected-floor
  statement above.

## Implementation notes

The source works in characteristic zero over `ℂ`. Here the field is any field `k`, which the klt
hypothesis forces to be algebraically closed of characteristic zero. In the case `dim V = 2` the
source shows that the horizontal component `S` has connected fibres by the relative
connectedness theorem for the pair `(1 - δ)B + δS`. Here this follows instead from the
birationality of `S ⟶ V`, as degree one gives `κ(η_S) = κ(η_V)`, together with Zariski's main
theorem. In fibre dimension at least two the source applies the Cohen–Macaulay ample divisor
lemma to the scheme-theoretic fibres. Here the ample divisor is pulled back to the normalization
of the irreducible fibre, which has depth at least two at its closed points by normality.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips]
-/

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Fourfold

namespace MMP.FourfoldProofs.FourfoldMoriThreefoldConnectedFloorCasesProof

/-- A finite morphism is a closed map sending the closure of a point onto the closure of its
image. -/
private theorem image_closure_singleton_of_isFinite {W Z : Scheme.{0}} (κ : W ⟶ Z) [IsFinite κ]
    (x : W) : κ '' closure ({x} : Set W) = closure {κ x} := by
  have hcl : IsClosedMap κ := κ.isClosedMap
  refine le_antisymm ?_ ?_
  · rintro _ ⟨y, hy, rfl⟩
    exact (specializes_iff_mem_closure.mpr hy).map κ.continuous |>.mem_closure
  · refine closure_minimal ?_ (hcl _ isClosed_closure)
    rintro _ rfl
    exact ⟨x, subset_closure rfl, rfl⟩

/-- **A finite morphism with one point over every closed point is injective.** Let `κ : W ⟶ Z` be
a finite morphism, `W` a Jacobson space, such that every closed point of `Z` has at most one
preimage. Then `κ` is injective. -/
private theorem injective_of_isFinite_of_subsingleton {W Z : Scheme.{0}} (κ : W ⟶ Z)
    [IsFinite κ] [JacobsonSpace W]
    (h : ∀ z : Z, IsClosed ({z} : Set Z) → (κ ⁻¹' {z}).Subsingleton) :
    Function.Injective κ := by
  -- every closed point in the closure of `x` lies in the closure of `y` when `κ x = κ y`
  have key : ∀ x y : W, κ x = κ y → closure ({x} : Set W) ⊆ closure {y} := by
    intro x y hxy
    have hsub : closure ({x} : Set W) ∩ closedPoints W ⊆ closure {y} := by
      rintro c ⟨hc, hcc⟩
      have hκc : IsClosed ({κ c} : Set Z) := by
        rw [← Set.image_singleton]; exact κ.isClosedMap _ hcc
      have hcz : κ c ∈ closure ({κ y} : Set Z) := by
        rw [← hxy, ← image_closure_singleton_of_isFinite κ x]; exact ⟨c, hc, rfl⟩
      rw [← image_closure_singleton_of_isFinite κ y] at hcz
      obtain ⟨d, hd, hdc⟩ := hcz
      rw [h (κ c) hκc hdc rfl] at hd
      exact hd
    calc closure ({x} : Set W) = closure (closure ({x} : Set W) ∩ closedPoints W) :=
          ((JacobsonSpace.closure_inter_closedPoints_eq_closure
            isClosed_closure.isLocallyClosed).trans closure_closure).symm
      _ ⊆ closure {y} := closure_minimal hsub isClosed_closure
  intro x y hxy
  have h1 : x ⤳ y := specializes_iff_closure_subset.mpr (key y x hxy.symm)
  have h2 : y ⤳ x := specializes_iff_closure_subset.mpr (key x y hxy)
  exact (h1.antisymm h2).eq

/-- **Stein step.** A proper morphism `f : T ⟶ V` from a reduced Noetherian scheme onto a normal
variety over an algebraically closed field of characteristic zero, all of whose closed fibres are
connected and nonempty, satisfies `f_* 𝒪_T = 𝒪_V`. -/
private theorem isIso_app_of_isConnected_closed_fibres {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {T V : Scheme.{0}} (sV : V ⟶ Spec (.of k)) (hV : IsNormalVariety k sV)
    (f : T ⟶ V) [IsProper f] [IsReduced T] [IsNoetherian T]
    (hfib : ∀ v : V, IsClosed ({v} : Set V) → _root_.IsConnected (f.base ⁻¹' {v}))
    (U : V.Opens) : IsIso (f.app U) := by
  have hVv := hV.1
  have : IsIntegral V := hVv.toIsIntegral
  have : LocallyOfFiniteType sV := hVv.toLocallyOfFiniteType
  have : QuasiCompact sV := hVv.toQuasiCompact
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian sV
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace sV
  have : IsNoetherian V := ⟨⟩
  obtain ⟨Z', h', s, ⟨hS⟩, he⟩ := MMP.exists_isSteinFactorization_and_connectedComponents_equiv f
  have := hS.isFinite
  have := hS.isProper
  have hcomp : h' ≫ s = f := hS.comp
  -- one point of `Z'` over every closed point of `V`
  have hone : ∀ v : V, IsClosed ({v} : Set V) → ∃! z : Z', s z = v := by
    intro v hv
    obtain ⟨e, -⟩ := he v
    have hc := hfib v hv
    have : ConnectedSpace (f ⁻¹' {v}) := isConnected_iff_connectedSpace.mp hc
    have : Nonempty (_root_.ConnectedComponents (f ⁻¹' {v})) := by
      obtain ⟨x⟩ := hc.nonempty.to_subtype
      exact ⟨_root_.ConnectedComponents.mk x⟩
    have : Subsingleton (_root_.ConnectedComponents (f ⁻¹' {v})) := inferInstance
    obtain ⟨c⟩ := ‹Nonempty (_root_.ConnectedComponents (f ⁻¹' {v}))›
    refine ⟨(e c).1, (e c).2, fun z hz => ?_⟩
    have := e.surjective ⟨z, hz⟩
    obtain ⟨c', hc'⟩ := this
    rw [Subsingleton.elim c' c] at hc'
    exact congrArg Subtype.val hc'.symm
  have : LocallyOfFiniteType (s ≫ sV) := inferInstance
  have : JacobsonSpace Z' := LocallyOfFiniteType.jacobsonSpace (s ≫ sV)
  have : JacobsonSpace V := LocallyOfFiniteType.jacobsonSpace sV
  have hinj : Function.Injective s := injective_of_isFinite_of_subsingleton s fun v hv a ha b hb =>
    ((hone v hv).unique ha hb)
  have hsurj : Function.Surjective s := by
    have hrange : IsClosed (Set.range s) := s.isClosedMap.isClosed_range
    have : closedPoints V ⊆ Set.range s := fun v hv => ⟨_, (hone v hv).exists.choose_spec⟩
    have := closure_minimal this hrange
    rw [closure_closedPoints] at this
    exact fun v => this (Set.mem_univ v)
  have : Surjective s := ⟨hsurj⟩
  -- `Z'` is integral: reduced since its sections are those of `T`, irreducible since `s` is a
  -- homeomorphism
  have : IsReduced Z' := by
    refine ⟨fun W => ?_⟩
    have := hS.structureSheaf
    have : IsIso (h'.app W) := NatIso.isIso_app_of_isIso h'.c (Opposite.op W)
    exact isReduced_of_injective (h'.app W).hom
      ((ConcreteCategory.isIso_iff_bijective _).mp this).1
  have : IrreducibleSpace Z' := by
    have hhomeo : IsHomeomorph s := (isHomeomorph_iff_continuous_isClosedMap_bijective).mpr
      ⟨s.continuous, s.isClosedMap, hinj, hsurj⟩
    have e := (hhomeo.homeomorph s).symm
    have h := (IrreducibleSpace.isIrreducible_univ V).image e e.continuous.continuousOn
    rw [Set.image_univ, e.surjective.range_eq] at h
    exact (irreducibleSpace_def _).mpr h
  have : IsIntegral Z' := isIntegral_of_irreducibleSpace_of_isReduced Z'
  have := MMP.Flips.isIso_of_isFinite_of_injective sV s hV hinj
  have := hS.structureSheaf
  have hiso2 : IsIso (h'.app (s ⁻¹ᵁ U)) := NatIso.isIso_app_of_isIso h'.c (Opposite.op _)
  have hs : IsIso (s.app U) := inferInstance
  rw [← hcomp, Scheme.Hom.comp_app]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ hs hiso2

/-- **A connected closed set leaving a closed set specializes into it.** In a Noetherian
quasi-sober space, let `F` be closed and preconnected, meeting the closed set `E` without being
contained in it. Then some point `η ∈ F \ E` specializes to a point `q ∈ F ∩ E`. -/
private theorem exists_specializes_of_isPreconnected {X : Type*} [TopologicalSpace X]
    [TopologicalSpace.NoetherianSpace X] [QuasiSober X] {F E : Set X} (hF : IsClosed F)
    (hFc : _root_.IsPreconnected F) (hE : IsClosed E) (hFE : (F ∩ E).Nonempty) (hFE' : ¬ F ⊆ E) :
    ∃ η ∈ F, η ∉ E ∧ ∃ q ∈ F ∩ E, η ⤳ q := by
  classical
  set W := F \ E with hW
  have hWF : closure W ⊆ F := closure_minimal Set.diff_subset hF
  obtain ⟨S, hSf, hScl, hSirr, hSeq⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible
      (isClosed_closure (s := W))
  set S' := {t ∈ S | ¬ t ⊆ E} with hS'
  have hS'f : S'.Finite := hSf.subset fun t ht => ht.1
  have hWS' : W ⊆ ⋃₀ S' := by
    intro w hw
    have : w ∈ ⋃₀ S := hSeq ▸ subset_closure hw
    obtain ⟨t, ht, hwt⟩ := this
    exact ⟨t, ⟨ht, fun h => hw.2 (h hwt)⟩, hwt⟩
  have hS'cl : IsClosed (⋃₀ S') := hS'f.isClosed_sUnion fun t ht => hScl t ht.1
  have hS'F : ⋃₀ S' ⊆ F := fun x ⟨t, ht, hxt⟩ =>
    hWF (hSeq ▸ (⟨t, ht.1, hxt⟩ : x ∈ ⋃₀ S))
  obtain ⟨w, hwF, hwE⟩ := Set.not_subset.mp hFE'
  have hcover : F ⊆ E ∪ ⋃₀ S' := fun x hx => by
    by_cases hxE : x ∈ E
    · exact Or.inl hxE
    · exact Or.inr (hWS' ⟨hx, hxE⟩)
  obtain ⟨q, hqF, hqE, hqS⟩ := (isPreconnected_closed_iff.mp hFc) E (⋃₀ S') hE hS'cl hcover
    hFE ⟨w, hwF, hWS' ⟨hwF, hwE⟩⟩
  obtain ⟨t, ⟨htS, htE⟩, hqt⟩ := hqS
  have hirr := hSirr t htS
  have hgen := hirr.isGenericPoint_genericPoint_closure
  rw [(hScl t htS).closure_eq] at hgen
  refine ⟨hirr.genericPoint, hS'F ⟨t, ⟨htS, htE⟩, hgen.mem⟩, fun h => htE ?_, q, ⟨hqF, hqE⟩,
    hgen.specializes hqt⟩
  rw [← hgen.def]
  exact closure_minimal (Set.singleton_subset_iff.mpr h) hE

/-- **A divisor trivial on the contracted curves contains the fibres it meets.** Let
`r : Y ⟶ V` be proper with `r_* 𝒪_Y = 𝒪_V`, `Y` proper over `k`, and `E` a `ℚ`-Cartier prime
divisor of `Y` with `(E · C) = 0` for every proper curve `C` contracted by `r`. If `E` meets the
fibre over a closed point `v`, it contains it: otherwise a curve in the (connected) fibre through a
closed point of `E`, not contained in `E`, would meet `E` positively. -/
private theorem preimage_subset_of_intersectionNumber_eq_zero {k : Type} [Field k]
    {Y V : Scheme.{0}} (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y] [QuasiCompact sY] [IsProper sY] (r : Y ⟶ V) [IsProper r]
    (hr : ∀ U : V.Opens, IsIso (r.app U)) (E : MMP.Mori.PrimeDivisor Y)
    (hE : QDivisor.IsQCartier (Finsupp.single E (1 : ℚ) : QDivisor Y))
    (h0 : ∀ C : ProperCurve sY, C.IsContractedBy r →
      QDivisor.intersectionNumber k sY C.ι C.dim_le (Finsupp.single E (1 : ℚ)) hE = 0)
    {v : V} (hv : IsClosed ({v} : Set V)) (hvE : ∃ e ∈ (E.support : Set Y), r e = v) :
    r ⁻¹' {v} ⊆ E.support := by
  by_contra hsub
  have hF : IsClosed (r ⁻¹' {v}) := hv.preimage r.continuous
  have : IsNoetherian Y := ⟨⟩
  have hFc : _root_.IsPreconnected (r ⁻¹' {v}) :=
    (r.isConnected_preimage_singleton_of_isIso_app hr v).2
  have hEc : IsClosed (E.support : Set Y) := E.idealSheaf.support.isClosed
  obtain ⟨e, heE, hev⟩ := hvE
  obtain ⟨η, hηF, hηE, q, ⟨hqF, hqE⟩, hηq⟩ :=
    exists_specializes_of_isPreconnected hF hFc hEc ⟨e, hev, heE⟩ hsub
  obtain ⟨p, hpq, hp⟩ : ∃ p ∈ closure ({q} : Set Y), IsClosed ({p} : Set Y) :=
    isClosed_closure.exists_closed_singleton ⟨q, subset_closure rfl⟩
  have hqp : q ⤳ p := specializes_iff_mem_closure.mpr hpq
  have hpE : p ∈ (E.support : Set Y) := hqp.mem_closed hEc hqE
  have hpF : p ∈ r ⁻¹' {v} := hqp.mem_closed hF hqF
  obtain ⟨y, hηy, hyp, hyE, hy⟩ :=
    MMP.Fourfold.exists_isProperCurve_of_specializes sY (hηq.trans hqp) hp hEc hpE hηE
  set C : ProperCurve sY := ⟨y, hy⟩
  have hyF : y ∈ r ⁻¹' {v} := hηy.mem_closed hF hηF
  have hC : C.IsContractedBy r := fun x hx => by
    have hxF : x ∈ r ⁻¹' {v} := (specializes_iff_mem_closure.mpr hx).mem_closed hF hyF
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hxF hyF
    exact hxF.trans hyF.symm
  have hsupp : ∀ x : Y,
      x ∈ DivisorWithCoeffs.supp (Finsupp.single E (1 : ℚ) : QDivisor Y) ↔ x ∈ E.support := by
    intro x
    rw [DivisorWithCoeffs.mem_supp_iff]
    constructor
    · rintro ⟨E', hE', hx⟩
      by_cases h : E' = E
      · exact h ▸ hx
      · exact absurd (DivisorWithCoeffs.coeff_single_of_ne (Ne.symm h) _) hE'
    · intro hx
      exact ⟨E, by simp [DivisorWithCoeffs.coeff_single_self], hx⟩
  have hnn := MMP.Fourfold.intersectionNumber_nonneg_and_eq_zero_iff sY _ hE
    (Finsupp.single_nonneg.mpr zero_le_one) C (by rw [hsupp]; exact hyE)
  exact ((hnn.2.mp (h0 C hC)) p hyp) ((hsupp p).mpr hpE)

/-! ### Intersection numbers with contracted curves -/

section Numbers

variable {k : Type} [Field k] {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of k)) [IsLocallyNoetherian Y]
  [IsNormal Y] [QuasiCompact sY]

/-- On a `ℚ`-factorial variety, `((D - D') · C) = (D · C) - (D' · C)`. -/
private theorem intersectionNumber_sub_of_isQFactorial (hQ : IsQFactorial sY)
    (C : ProperCurve sY) (D D' : QDivisor Y) :
    QDivisor.intersectionNumber k sY C.ι C.dim_le (D - D')
        (MMP.Fourfold.isQCartier_of_isQFactorial sY hQ _) =
      QDivisor.intersectionNumber k sY C.ι C.dim_le D
          (MMP.Fourfold.isQCartier_of_isQFactorial sY hQ _) -
        QDivisor.intersectionNumber k sY C.ι C.dim_le D'
          (MMP.Fourfold.isQCartier_of_isQFactorial sY hQ _) := by
  have h := QDivisor.intersectionNumber_add' k sY C.ι C.dim_le D' (D - D')
    (MMP.Fourfold.isQCartier_of_isQFactorial sY hQ _)
    (MMP.Fourfold.isQCartier_of_isQFactorial sY hQ _)
    (MMP.Fourfold.isQCartier_of_isQFactorial sY hQ _)
  rw [MMP.Fourfold.intersectionNumber_congr sY C.ι C.dim_le _
    (MMP.Fourfold.isQCartier_of_isQFactorial sY hQ D) (add_sub_cancel D' D)] at h
  linarith

/-- On a `ℚ`-factorial variety, `((q • D) · C) = q (D · C)`. -/
private theorem intersectionNumber_smul_of_isQFactorial (hQ : IsQFactorial sY)
    (C : ProperCurve sY) (q : ℚ) (D : QDivisor Y) :
    QDivisor.intersectionNumber k sY C.ι C.dim_le (q • D)
        (MMP.Fourfold.isQCartier_of_isQFactorial sY hQ _) =
      q * QDivisor.intersectionNumber k sY C.ι C.dim_le D
          (MMP.Fourfold.isQCartier_of_isQFactorial sY hQ _) :=
  MMP.Fourfold.intersectionNumber_smul sY C.ι C.dim_le D _ q _

/-- **Divisors are proportional along an extremal ray.** Let the proper curves contracted by `r`
be those whose classes lie in the ray `R = ℝ_{≥0} v₀`. If `(D · γ₀) = 0` for a contracted curve
`γ₀` with `(G · γ₀) ≠ 0` for some `G`, then `(D · C) = 0` for every contracted curve `C`. -/
private theorem intersectionNumber_eq_zero_of_ray [IsIntegral Y] [CompactSpace Y]
    {V : Scheme.{0}} (r : Y ⟶ V)
    (R : Set (NumericalCurveClasses sY)) {v₀ : NumericalCurveClasses sY}
    (hR : R = {w | ∃ c : ℝ, 0 ≤ c ∧ c • v₀ = w})
    (hcon : ∀ C : ProperCurve sY,
      C.IsContractedBy r ↔ OneCycle.numericalClass sY (C.cycle ℝ) ∈ R)
    (D G : QDivisor Y) (hD : D.IsQCartier) (hG : G.IsQCartier)
    (γ₀ : ProperCurve sY) (hγ₀ : γ₀.IsContractedBy r)
    (hD0 : QDivisor.intersectionNumber k sY γ₀.ι γ₀.dim_le D hD = 0)
    (hG0 : QDivisor.intersectionNumber k sY γ₀.ι γ₀.dim_le G hG ≠ 0)
    (C : ProperCurve sY) (hC : C.IsContractedBy r) :
    QDivisor.intersectionNumber k sY C.ι C.dim_le D hD = 0 := by
  have h₀ := (hcon γ₀).mp hγ₀
  have h₁ := (hcon C).mp hC
  rw [hR] at h₀ h₁
  obtain ⟨c₀, -, hc₀⟩ := h₀
  obtain ⟨c, -, hc⟩ := h₁
  have hG' := MMP.ProgramBaseChange.curveForm_numericalClass_cycle sY G hG γ₀
  have hD' := MMP.ProgramBaseChange.curveForm_numericalClass_cycle sY D hD γ₀
  have hDC := MMP.ProgramBaseChange.curveForm_numericalClass_cycle sY D hD C
  rw [← hc₀, map_smul, smul_eq_mul] at hG' hD'
  rw [← hc, map_smul, smul_eq_mul] at hDC
  have hc₀0 : c₀ ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hG'
    exact hG0 (by exact_mod_cast hG'.symm)
  have hv : QDivisor.curveForm sY D hD v₀ = 0 := by
    rw [hD0, Rat.cast_zero] at hD'
    exact (mul_eq_zero.mp hD').resolve_left hc₀0
  rw [hv, mul_zero] at hDC
  exact_mod_cast hDC.symm

end Numbers

/-- A `ℚ`-Cartier `ℚ`-divisor numerically trivial over `r` has intersection number zero with every
proper curve contracted by `r`. -/
private theorem intersectionNumber_eq_zero_of_isNumericallyTrivialOver {k : Type} [Field k]
    {Y V : Scheme.{0}} (sY : Y ⟶ Spec (.of k)) [QuasiCompact sY] [IsLocallyNoetherian Y]
    [IsNormal Y] (r : Y ⟶ V) (D : QDivisor Y) (hD : D.IsQCartier)
    (hnum : MMP.Flips.IsNumericallyTrivialOver k sY r (QDivisor.toRDivisor D))
    (C : ProperCurve sY) (hC : C.IsContractedBy r) :
    QDivisor.intersectionNumber k sY C.ι C.dim_le D hD = 0 := by
  set hF := QDivisor.isCartierDivisor_cartierIndex_smul hD
  set F := hF.toDivisor
  set n := D.cartierIndex hD
  have hn : (0 : ℝ) < n := by exact_mod_cast QDivisor.cartierIndex_pos hD
  have hpres := MMP.Flips.isRIntersectionNumber_sum_degreeOn k sY C (m := 1) ![(n : ℝ)⁻¹] ![F]
    (fun j => by rw [Subsingleton.elim j 0]; exact hF.isCartier_toDivisor)
  have hDF : QDivisor.toRDivisor D = ∑ j, (![(n : ℝ)⁻¹] : Fin 1 → ℝ) j •
      Divisor.toRDivisor ((![F] : Fin 1 → Divisor Y) j) := by
    rw [Fin.sum_univ_one]
    simp only [Matrix.cons_val_zero]
    rw [← QDivisor.toRDivisor_toQDivisor, hF.toQDivisor_toDivisor, map_zsmul,
      ← Int.cast_smul_eq_zsmul ℝ, smul_smul]
    push_cast
    rw [inv_mul_cancel₀ hn.ne', one_smul]
  have h0 : MMP.Flips.IsRIntersectionNumber k sY (0 : RDivisor Y) (m := 0) Fin.elim0
      Fin.elim0 C 0 := ⟨fun j => j.elim0, fun j => j.elim0, by simp, fun j => j.elim0, by simp⟩
  have hx := hnum.2.2 C hC 1 _ _ _ 0 Fin.elim0 Fin.elim0 0 (hDF ▸ hpres) h0
  simp only [Fin.sum_univ_one, Matrix.cons_val_zero] at hx
  have hdeg : (F.degreeOn k sY C.ι C.dim_le hF.isCartier_toDivisor : ℝ) = 0 := by
    rcases mul_eq_zero.mp hx with h | h
    · exact absurd h (inv_ne_zero hn.ne')
    · exact h
  rw [QDivisor.intersectionNumber_eq_of_toQDivisor_eq k sY C.ι C.dim_le D hD F
    hF.isCartier_toDivisor hF.toQDivisor_toDivisor]
  have : (F.degreeOn k sY C.ι C.dim_le hF.isCartier_toDivisor : ℤ) = 0 := by exact_mod_cast hdeg
  rw [this]
  simp

/-- **The floor is positive on the contracted curves.** If `K + B` is numerically trivial over
`r` and `-(K + B - ε⌊B⌋)` has an `r`-ample Cartier multiple, with `ε > 0`, then `(⌊B⌋ · C) > 0`
for every proper curve `C` contracted by `r`. -/
private theorem intersectionNumber_roundDown_pos {k : Type} [Field k] {Y V : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [QuasiCompact sY] (hYv : AlgebraicGeometry.IsVariety k sY) (hQ : IsQFactorial sY)
    (K : Divisor Y) (B : QDivisor Y) (r : Y ⟶ V)
    (hnum : MMP.Flips.IsNumericallyTrivialOver k sY r
      (QDivisor.toRDivisor (Divisor.toQDivisor K + B)))
    (ε : ℚ) (hε : 0 < ε)
    (hamp : (-(Divisor.toQDivisor K +
      (B - ε • Divisor.toQDivisor (DivisorWithCoeffs.roundDown B)))).HasRelativelyAmpleMultiple r)
    (C : ProperCurve sY) (hC : C.IsContractedBy r) :
    0 < QDivisor.intersectionNumber k sY C.ι C.dim_le
      (Divisor.toQDivisor (DivisorWithCoeffs.roundDown B))
      (MMP.Fourfold.isQCartier_of_isQFactorial sY hQ _) := by
  obtain ⟨m, hm, L, hL, hLeq, hLamp⟩ := hamp
  set T := Divisor.toQDivisor (DivisorWithCoeffs.roundDown B)
  set D₁ := Divisor.toQDivisor K + B
  have hpos : 0 < L.degreeOn k sY C.ι C.dim_le hL := by
    haveI := hL.isInvertibleModule_divisorialSheaf
    exact MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple hYv r L.divisorialSheaf
      hLamp C hC
  have hLC : QDivisor.intersectionNumber k sY C.ι C.dim_le (Divisor.toQDivisor L)
      (MMP.Fourfold.isQCartier_of_isQFactorial sY hQ _) = L.degreeOn k sY C.ι C.dim_le hL :=
    QDivisor.intersectionNumber_toQDivisor k sY C.ι C.dim_le L hL _
  have hD₁ := intersectionNumber_eq_zero_of_isNumericallyTrivialOver sY r D₁
    (MMP.Fourfold.isQCartier_of_isQFactorial sY hQ _) hnum C hC
  have heq : Divisor.toQDivisor L = (m : ℚ) • (ε • T - D₁) := by
    rw [hLeq]
    simp only [D₁, T]
    rw [← Int.cast_smul_eq_zsmul ℚ]
    push_cast
    congr 1
    abel
  rw [MMP.Fourfold.intersectionNumber_congr sY C.ι C.dim_le _
    (MMP.Fourfold.isQCartier_of_isQFactorial sY hQ _) heq,
    intersectionNumber_smul_of_isQFactorial sY hQ, intersectionNumber_sub_of_isQFactorial sY hQ,
    intersectionNumber_smul_of_isQFactorial sY hQ, hD₁] at hLC
  have hm' : (0 : ℚ) < m := by exact_mod_cast hm
  have : (0 : ℚ) < (m : ℚ) * (ε * QDivisor.intersectionNumber k sY C.ι C.dim_le T
      (MMP.Fourfold.isQCartier_of_isQFactorial sY hQ _) - 0) := by
    rw [hLC]; exact_mod_cast hpos
  rw [sub_zero] at this
  have h2 := pos_of_mul_pos_right this hm'.le
  exact pos_of_mul_pos_right h2 hε.le

/-- **Vertical prime divisors contain the fibres they meet.** Let `r : Y ⟶ V` be the contraction
of an extremal ray `R = ℝ_{≥0} v₀` of a `ℚ`-factorial projective variety, with `dim V < dim Y`,
and suppose the floor of `B` is positive on the contracted curves. A prime divisor `E` with
`r(E) ≠ V` has `(E · C) = 0` on every contracted curve (it misses a contracted curve, whose class
spans `R`), hence contains every fibre over a closed point that it meets. -/
private theorem preimage_subset_support_of_map_genericPoint_ne {k : Type} [Field k]
    {Y V : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) (sV : V ⟶ Spec (.of k)) [IsIntegral Y] [CompactSpace Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [QuasiCompact sY] [IsIntegral V]
    (hY : MMP.Mori.IsProjectiveVariety k sY) (hQ : IsQFactorial sY)
    (K : Divisor Y) (R : Set (NumericalCurveClasses sY)) (r : Y ⟶ V)
    (hr : IsContractionOfRay sY sV R r) {v₀ : NumericalCurveClasses sY}
    (hR : R = {w | ∃ c : ℝ, 0 ≤ c ∧ c • v₀ = w}) (B : QDivisor Y)
    (hnum : MMP.Flips.IsNumericallyTrivialOver k sY r
      (QDivisor.toRDivisor (Divisor.toQDivisor K + B)))
    (ε : ℚ) (hε : 0 < ε)
    (hamp : (-(Divisor.toQDivisor K +
      (B - ε • Divisor.toQDivisor (DivisorWithCoeffs.roundDown B)))).HasRelativelyAmpleMultiple r)
    (hdim : topologicalKrullDim V < topologicalKrullDim Y)
    (E : MMP.Mori.PrimeDivisor Y) (hEv : r E.genericPoint ≠ genericPoint V)
    {v : V} (hv : IsClosed ({v} : Set V)) (hvE : ∃ e ∈ (E.support : Set Y), r e = v) :
    r ⁻¹' {v} ⊆ E.support := by
  have hYv : AlgebraicGeometry.IsVariety k sY := hY.toIsVariety
  have hVv : AlgebraicGeometry.IsVariety k sV := hr.isNormalVariety_target.1
  have : IsProper r :=
    (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mp hr.isProjectiveMorphism).2
  have : IsProper sY :=
    (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mp hY.isProjective).2
  have : Surjective r := ⟨hr.surjective⟩
  have : IsDominant r := inferInstance
  have hEc : IsClosed (E.support : Set Y) := E.idealSheaf.support.isClosed
  set Bs : Set Y := r ⁻¹' (r '' E.support) with hBs
  have hBc : IsClosed Bs := (r.isClosedMap _ hEc).preimage r.continuous
  have hηB : genericPoint Y ∉ Bs := by
    rintro ⟨e, he, hre⟩
    rw [map_genericPoint_of_isDominant] at hre
    have h1 : E.genericPoint ⤳ e := specializes_iff_mem_closure.mpr
      ((AlgebraicGeometry.PrimeDivisor.support_eq_closure E) ▸ he)
    have h2 : r E.genericPoint ⤳ genericPoint V := hre ▸ h1.map r.continuous
    have h3 : genericPoint V ⤳ r E.genericPoint := (genericPoint_spec V).specializes trivial
    exact hEv (h2.antisymm h3).eq
  obtain ⟨γ₀, hγ₀, hγ₀B⟩ := MMP.Fourfold.exists_properCurve_isContractedBy_of_lt hYv hVv r
    hr.comp_eq hdim hBc hηB
  have hE := MMP.Fourfold.isQCartier_of_isQFactorial sY hQ (Finsupp.single E (1 : ℚ))
  have hdisj : ∀ x : Y, γ₀.point ⤳ x →
      x ∉ DivisorWithCoeffs.supp (Finsupp.single E (1 : ℚ) : QDivisor Y) := by
    intro x hx hxE
    obtain ⟨E', hE', hxE'⟩ := DivisorWithCoeffs.mem_supp_iff.mp hxE
    have hE'E : E' = E := by
      by_contra h
      exact hE' (DivisorWithCoeffs.coeff_single_of_ne (Ne.symm h) _)
    subst hE'E
    exact hγ₀B ⟨x, hxE', (hγ₀ x (specializes_iff_mem_closure.mp hx))⟩
  have hE0 := MMP.Fourfold.intersectionNumber_eq_zero_of_disjoint sY hQ _ hE γ₀ hdisj
  have hT0 := (intersectionNumber_roundDown_pos sY hYv hQ K B r hnum ε hε hamp γ₀ hγ₀).ne'
  have h0 := intersectionNumber_eq_zero_of_ray sY r R hR hr.isContractedBy_iff _ _ hE _ γ₀ hγ₀
    hE0 hT0
  exact preimage_subset_of_intersectionNumber_eq_zero sY r hr.isIso_app E hE h0 hv hvE

/-! ### Fibre dimension one -/

/-- A prime divisor `P` of `Y` dominating `V`, with `dim Y = dim V + 1`, has a finite residue
field extension `κ(η_V) ⊆ κ(η_P)`: its transcendence degree vanishes by the dimension formula. -/
private theorem residueFieldDegree_ne_zero_of_map_genericPoint_eq {k : Type} [Field k]
    {Y V : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) (sV : V ⟶ Spec (.of k)) [IsIntegral Y] [IsIntegral V]
    (hYv : AlgebraicGeometry.IsVariety k sY) (hVv : AlgebraicGeometry.IsVariety k sV)
    (r : Y ⟶ V) (hrs : r ≫ sV = sY) [IsDominant r]
    (hdimY : topologicalKrullDim Y = 3) (hdimV : topologicalKrullDim V = 2)
    (P : MMP.Mori.PrimeDivisor Y) (hP : r.base P.genericPoint = genericPoint V) :
    MMP.Mori.residueFieldDegree r P.genericPoint ≠ 0 := by
  have : LocallyOfFiniteType sV := hVv.toLocallyOfFiniteType
  have : LocallyOfFiniteType sY := hYv.toLocallyOfFiniteType
  have : LocallyOfFiniteType r := by
    have : LocallyOfFiniteType (r ≫ sV) := hrs ▸ inferInstance
    exact locallyOfFiniteType_of_comp r sV
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian sV
  have hUC := Scheme.isUniversallyCatenary_of_locallyOfFiniteType_over_field k sV
  have e1 := localDimension_add_trdeg_eq r hUC P.genericPoint
  have e2 := localDimension_add_trdeg_eq r hUC (genericPoint Y)
  have hηY : r.base (genericPoint Y) = genericPoint V := map_genericPoint_of_isDominant r
  -- the local dimensions
  have hmax : ∀ (Z : Scheme.{0}) [IsIntegral Z],
      ringKrullDim (Z.presheaf.stalk (genericPoint Z)) = 0 := fun Z _ => by
    rw [ringKrullDim_stalk_eq_coheight]
    have : Order.coheight (genericPoint Z) = 0 :=
      Order.coheight_eq_zero.mpr fun b _ =>
        Scheme.le_iff_specializes.mpr (genericPoint_specializes b)
    rw [this]; rfl
  have hP1 : ringKrullDim (Y.presheaf.stalk P.genericPoint) = 1 := by
    rw [ringKrullDim_stalk_eq_coheight]
    have h := MMP.Mori.PrimeDivisor.codimension_closure_genericPoint P
    rw [Stacks.Divisors.PrimeDivisor.codimension_closureSingleton] at h
    rw [h]; rfl
  have hV0 : ringKrullDim (V.presheaf.stalk (r.base P.genericPoint)) = 0 := by
    rw [hP]; exact hmax V
  have hV0' : ringKrullDim (V.presheaf.stalk (r.base (genericPoint Y))) = 0 := by
    rw [hηY]; exact hmax V
  rw [hP1, hV0] at e1
  rw [hmax Y, hV0'] at e2
  -- the transcendence degree of `κ(η_Y)` over `κ(η_V)` is one
  have hadd := MMP.Flips.trdeg_residueField_add sY sV r hrs (genericPoint Y)
  have hdY := topologicalKrullDim_eq_trdeg_residueField k Y sY (genericPoint Y)
    (genericPoint_spec Y)
  have hdV := topologicalKrullDim_eq_trdeg_residueField k V sV (r.base (genericPoint Y))
    (by rw [hηY]; exact genericPoint_spec V)
  rw [hdimY] at hdY
  rw [hdimV] at hdV
  letI : Algebra k (Y.residueField (genericPoint Y)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ sY.appTop ≫ Y.Γevaluation (genericPoint Y)).hom.toAlgebra
  letI : Algebra k (V.residueField (r.base (genericPoint Y))) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ sV.appTop ≫
      V.Γevaluation (r.base (genericPoint Y))).hom.toAlgebra
  letI : Algebra (V.residueField (r.base (genericPoint Y))) (Y.residueField (genericPoint Y)) :=
    (r.residueFieldMap (genericPoint Y)).hom.toAlgebra
  have hadd' := congrArg Cardinal.toENat hadd
  rw [map_add] at hadd'
  have hc : Cardinal.toENat (Algebra.trdeg k (Y.residueField (genericPoint Y))) = 3 := by
    have h := hdY.symm
    rw [show (3 : WithBot ℕ∞) = ((3 : ℕ∞) : WithBot ℕ∞) from rfl] at h
    exact WithBot.coe_injective h
  have ha : Cardinal.toENat (Algebra.trdeg k (V.residueField (r.base (genericPoint Y)))) = 2 := by
    have h := hdV.symm
    rw [show (2 : WithBot ℕ∞) = ((2 : ℕ∞) : WithBot ℕ∞) from rfl] at h
    exact WithBot.coe_injective h
  rw [hc, ha] at hadd'
  have hb : Cardinal.toENat (Algebra.trdeg (V.residueField (r.base (genericPoint Y)))
      (Y.residueField (genericPoint Y))) = 1 := by
    generalize Cardinal.toENat _ = b at hadd' ⊢
    cases b using ENat.recTopCoe with
    | top => simp at hadd'
    | coe b => norm_cast at hadd' ⊢; omega
  rw [hb, zero_add, zero_add] at e2
  rw [← e2, zero_add] at e1
  letI := (r.residueFieldMap P.genericPoint).hom.toAlgebra
  have ht : Cardinal.toENat (Algebra.trdeg (V.residueField (r.base P.genericPoint))
      (Y.residueField P.genericPoint)) = 0 := by
    generalize Cardinal.toENat _ = t at e1 ⊢
    cases t using ENat.recTopCoe with
    | top => exact absurd e1 (by decide)
    | coe t =>
      have : ((1 + t : ℕ) : WithBot ℕ∞) = ((1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast e1
      have : 1 + t = 1 := by exact_mod_cast this
      norm_cast; omega
  have h0 : Algebra.trdeg (V.residueField (r.base P.genericPoint))
      (Y.residueField P.genericPoint) = 0 := by
    have := Cardinal.toENat_eq_zero.mp ht
    exact this
  have halg : Algebra.IsAlgebraic (V.residueField (r.base P.genericPoint))
      (Y.residueField P.genericPoint) := trdeg_eq_zero_iff.mp h0
  haveI : Algebra.EssFiniteType (V.residueField (r.base P.genericPoint))
      (Y.residueField P.genericPoint) :=
    RingHom.EssFiniteType.residueFieldMap (LocallyOfFiniteType.stalkMap r P.genericPoint)
  haveI : Module.Finite (V.residueField (r.base P.genericPoint))
      (Y.residueField P.genericPoint) := Algebra.finite_of_essFiniteType_of_isAlgebraic
  exact (Module.finrank_pos (R := V.residueField (r.base P.genericPoint))
    (M := Y.residueField P.genericPoint)).ne'

open scoped Classical in
/-- **The horizontal floor of degree one.** If `B ≥ 0`, every horizontal prime divisor has a
finite residue field extension over `V`, and the horizontal part of `⌊B⌋` has degree one, then
`⌊B⌋` has exactly one horizontal component `S`, and `κ(η_S) = κ(η_V)`. -/
private theorem exists_unique_horizontal_of_sum_eq_one {Y V : Scheme.{0}} [IsIntegral V]
    (r : Y ⟶ V) (B : QDivisor Y) (hB : 0 ≤ B)
    (hfin : ∀ P : MMP.Mori.PrimeDivisor Y, r.base P.genericPoint = genericPoint V →
      MMP.Mori.residueFieldDegree r P.genericPoint ≠ 0)
    (hdeg : ∑ P ∈ (DivisorWithCoeffs.roundDown B).support with
            r.base P.genericPoint = genericPoint V,
          (DivisorWithCoeffs.roundDown B).coeff P *
            (MMP.Mori.residueFieldDegree r P.genericPoint : ℤ) = 1) :
    ∃ S ∈ (DivisorWithCoeffs.roundDown B).support, r.base S.genericPoint = genericPoint V ∧
      MMP.Mori.residueFieldDegree r S.genericPoint = 1 ∧
      ∀ P ∈ (DivisorWithCoeffs.roundDown B).support,
        r.base P.genericPoint = genericPoint V → P = S := by
  set T₀ := DivisorWithCoeffs.roundDown B
  set H := T₀.support.filter fun P => r.base P.genericPoint = genericPoint V
  -- every term of the sum is a positive integer
  have hpos : ∀ P ∈ H, 1 ≤ T₀.coeff P * (MMP.Mori.residueFieldDegree r P.genericPoint : ℤ) := by
    intro P hP
    rw [Finset.mem_filter] at hP
    have hc : T₀.coeff P ≠ 0 := Finsupp.mem_support_iff.mp hP.1
    have hc0 : 0 ≤ T₀.coeff P := by
      rw [DivisorWithCoeffs.coeff_roundDown]
      exact Int.floor_nonneg.mpr (hB P)
    have hd : (1 : ℤ) ≤ MMP.Mori.residueFieldDegree r P.genericPoint := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (hfin P hP.2)
    nlinarith [lt_of_le_of_ne hc0 (Ne.symm hc)]
  have hne : H.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [h, Finset.sum_empty] at hdeg
    exact zero_ne_one hdeg
  obtain ⟨S, hS⟩ := hne
  have hle : ∀ P ∈ H, P ≠ S → False := by
    intro P hP hPS
    have h2 : ∑ Q ∈ ({P, S} : Finset _), T₀.coeff Q *
        (MMP.Mori.residueFieldDegree r Q.genericPoint : ℤ) ≤
        ∑ Q ∈ H, T₀.coeff Q * (MMP.Mori.residueFieldDegree r Q.genericPoint : ℤ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (by
        intro Q hQ
        rcases Finset.mem_insert.mp hQ with rfl | hQ
        · exact hP
        · rw [Finset.mem_singleton.mp hQ]; exact hS)
        (fun Q hQ _ => by linarith [hpos Q hQ])
    rw [Finset.sum_pair hPS] at h2
    have := hpos P hP
    have := hpos S hS
    change _ ≤ ∑ Q ∈ H, _ at h2
    linarith
  have hHS : H = {S} := Finset.eq_singleton_iff_unique_mem.mpr
    ⟨hS, fun P hP => by_contra fun h => hle P hP h⟩
  rw [show (∑ P ∈ T₀.support with r.base P.genericPoint = genericPoint V,
      T₀.coeff P * (MMP.Mori.residueFieldDegree r P.genericPoint : ℤ)) =
      ∑ P ∈ H, T₀.coeff P * (MMP.Mori.residueFieldDegree r P.genericPoint : ℤ) from rfl,
    hHS, Finset.sum_singleton] at hdeg
  rw [Finset.mem_filter] at hS
  have hc0 : 0 ≤ T₀.coeff S := by
    rw [DivisorWithCoeffs.coeff_roundDown]
    exact Int.floor_nonneg.mpr (hB S)
  have hd : (0 : ℤ) ≤ MMP.Mori.residueFieldDegree r S.genericPoint := by positivity
  refine ⟨S, hS.1, hS.2, ?_, fun P hP hPh => by_contra fun h =>
    hle P (Finset.mem_filter.mpr ⟨hP, hPh⟩) h⟩
  have := Int.eq_one_of_mul_eq_one_left hd hdeg
  exact_mod_cast this

/-- The residue map at the generic point of an integral scheme is bijective. -/
private theorem residue_bijective_of_eq_genericPoint {X : Scheme.{0}} [IsIntegral X] {x : X}
    (hx : x = genericPoint X) : Function.Bijective (X.residue x) := by
  subst hx
  exact ⟨RingHom.injective _, X.residue_surjective _⟩

/-- **A horizontal prime divisor of degree one has connected fibres.** If `κ(η_S) = κ(η_V)`, the
proper morphism `S ⟶ V` is birational onto the normal variety `V`, so by Zariski's main theorem
every fibre of `S ⟶ V` is connected. -/
private theorem isConnected_support_inter_preimage_of_residueFieldDegree_eq_one {k : Type} [Field k]
    {Y V : Scheme.{0}} (sY : Y ⟶ Spec (.of k)) (sV : V ⟶ Spec (.of k)) [IsIntegral Y]
    [IsIntegral V] (hYv : AlgebraicGeometry.IsVariety k sY) (hVn : IsNormalVariety k sV)
    (r : Y ⟶ V) (hrs : r ≫ sV = sY) [IsProper r]
    (S : MMP.Mori.PrimeDivisor Y) (hS : r.base S.genericPoint = genericPoint V)
    (hdeg : MMP.Mori.residueFieldDegree r S.genericPoint = 1) (v : V) :
    _root_.IsConnected ((S.support : Set Y) ∩ r ⁻¹' {v}) := by
  have := S.integral
  set ι := S.idealSheaf.subschemeι
  set g := ι ≫ r
  set x := genericPoint S.idealSheaf.subscheme
  have hιx : ι.base x = S.genericPoint := rfl
  have hgx : g.base x = genericPoint V := by
    change r.base (ι.base x) = _
    rw [hιx, hS]
  have hgs : g ≫ sV = ι ≫ sY := by rw [Category.assoc, hrs]
  have : LocallyOfFiniteType sY := hYv.toLocallyOfFiniteType
  have : IsSeparated sY := hYv.toIsSeparated
  have : QuasiCompact sY := hYv.toQuasiCompact
  have hSv : AlgebraicGeometry.IsVariety k (g ≫ sV) := by
    rw [hgs]
    exact @AlgebraicGeometry.IsVariety.mk _ _ _ _ S.integral inferInstance inferInstance
      inferInstance
  have : IsProper g := inferInstance
  have : IsDominant g := by
    refine ⟨dense_iff_closure_eq.mpr (Set.eq_univ_of_univ_subset ?_)⟩
    have : genericPoint V ∈ Set.range g := ⟨x, hgx⟩
    rw [← (genericPoint_spec V).def]
    exact closure_mono (Set.singleton_subset_iff.mpr this)
  have : Surjective g := by
    have hcl : IsClosed (Set.range g) := g.isClosedMap.isClosed_range
    have : Set.range g = Set.univ := by
      rw [← hcl.closure_eq]
      exact g.denseRange.closure_range
    exact ⟨Set.range_eq_univ.mp this⟩
  -- `g` is an isomorphism at the generic point
  have h1 : Function.Bijective (r.residueFieldMap (ι.base x)) := by
    letI := (r.residueFieldMap S.genericPoint).hom.toAlgebra
    exact (Algebra.finrank_eq_one_iff_bijective_algebraMap).mp hdeg
  have h2 : Function.Bijective (ι.residueFieldMap x) := by
    refine ⟨RingHom.injective _, ?_⟩
    have h := Scheme.residue_residueFieldMap ι x
    have hs : Function.Surjective ((ι.stalkMap x ≫ S.idealSheaf.subscheme.residue x).hom) := by
      rw [CommRingCat.hom_comp, RingHom.coe_comp]
      exact (S.idealSheaf.subscheme.residue_surjective x).comp (ι.stalkMap_surjective x)
    rw [← h, CommRingCat.hom_comp, RingHom.coe_comp] at hs
    exact hs.of_comp
  have hres : Function.Bijective (g.residueFieldMap x) := by
    have e := Scheme.residueFieldMap_comp ι r x
    have : Function.Bijective (r.residueFieldMap (ι.base x) ≫ ι.residueFieldMap x) := by
      change Function.Bijective (⇑(ι.residueFieldMap x).hom ∘ ⇑(r.residueFieldMap (ι.base x)).hom)
      exact h2.comp h1
    exact e ▸ this
  have hstalk : Function.Bijective (g.stalkMap x) := by
    have h := Scheme.residue_residueFieldMap g x
    have hcomp : Function.Bijective ((g.stalkMap x ≫ S.idealSheaf.subscheme.residue x).hom) := by
      rw [← h, CommRingCat.hom_comp, RingHom.coe_comp]
      exact hres.comp (residue_bijective_of_eq_genericPoint (X := V) hgx)
    rw [CommRingCat.hom_comp, RingHom.coe_comp] at hcomp
    exact (Function.Bijective.of_comp_iff'
      (residue_bijective_of_eq_genericPoint (X := S.idealSheaf.subscheme) (x := x) rfl) _).mp hcomp
  have : IsIso (g.stalkMap (genericPoint S.idealSheaf.subscheme)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hstalk
  have : LocallyOfFiniteType g := by
    have : LocallyOfFiniteType (g ≫ sV) := hSv.toLocallyOfFiniteType
    exact locallyOfFiniteType_of_comp g sV
  have hbir : IsBirationalMorphism g := by
    have hb : IsBirational g := isBirational_of_isIso_stalkMap_genericPoint g
    haveI : Finite (irreducibleComponents S.idealSheaf.subscheme) := by
      rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
    haveI : Finite (irreducibleComponents V) := by
      rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
    obtain ⟨U, W, hUW, hU, hW, hiso⟩ :=
      exists_dense_opens_isIso_resLE_of_isBirational g hb (Or.inl ⟨inferInstance, inferInstance⟩)
    exact MMP.Flips.isBirationalMorphism_of_isIso_resLE g U W hU.nonempty hW.nonempty hUW hiso
  obtain ⟨-, hconn⟩ := MMP.Resolution.Bridges.isIso_app_and_isConnected_of_isBirationalMorphism
    (g ≫ sV) sV hSv hVn g hbir
  have heq : (S.support : Set Y) ∩ r ⁻¹' {v} = ι '' (g ⁻¹' {v}) := by
    rw [show g = ι ≫ r from rfl, Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp,
      Set.image_preimage_eq_inter_range, Scheme.IdealSheafData.range_subschemeι, Set.inter_comm]
  rw [heq]
  exact (hconn v).image _ ι.continuous.continuousOn

open scoped Classical in
/-- **The connected floor over a surface.** In the setting of the main theorem with `dim V = 2`
and horizontal floor of degree one, every closed fibre of `⌊B⌋ ⟶ V` is connected and nonempty:
it is the whole fibre if it meets a vertical component of `⌊B⌋`, and otherwise the fibre of the
unique horizontal component, which is birational to `V`. -/
private theorem isConnected_floor_inter_fibre_of_eq_two {k : Type} [Field k] {Y V : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) (sV : V ⟶ Spec (.of k)) [IsIntegral Y] [CompactSpace Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [QuasiCompact sY] [IsIntegral V]
    (hY : MMP.Mori.IsProjectiveVariety k sY) (hdimY : topologicalKrullDim Y = 3)
    (hQ : IsQFactorial sY) (K : Divisor Y) (R : Set (NumericalCurveClasses sY)) (r : Y ⟶ V)
    (hr : IsContractionOfRay sY sV R r) {v₀ : NumericalCurveClasses sY}
    (hR : R = {w | ∃ c : ℝ, 0 ≤ c ∧ c • v₀ = w}) (B : QDivisor Y) (hB : 0 ≤ B)
    (hnum : MMP.Flips.IsNumericallyTrivialOver k sY r
      (QDivisor.toRDivisor (Divisor.toQDivisor K + B)))
    (ε : ℚ) (hε : 0 < ε)
    (hamp : (-(Divisor.toQDivisor K +
      (B - ε • Divisor.toQDivisor (DivisorWithCoeffs.roundDown B)))).HasRelativelyAmpleMultiple r)
    (hdimV : topologicalKrullDim V = 2)
    (hdeg : ∑ P ∈ (DivisorWithCoeffs.roundDown B).support with
            r.base P.genericPoint = genericPoint V,
          (DivisorWithCoeffs.roundDown B).coeff P *
            (letI := (r.residueFieldMap P.genericPoint).hom.toAlgebra
             (Module.finrank (V.residueField (r.base P.genericPoint))
              (Y.residueField P.genericPoint) : ℤ)) = 1)
    (v : V) (hv : IsClosed ({v} : Set V)) :
    _root_.IsConnected (((DivisorWithCoeffs.roundDown B).supp : Set Y) ∩ r ⁻¹' {v}) := by
  have hYv : AlgebraicGeometry.IsVariety k sY := hY.toIsVariety
  have hVn : IsNormalVariety k sV := hr.isNormalVariety_target
  have : IsProper r :=
    (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mp hr.isProjectiveMorphism).2
  have : Surjective r := ⟨hr.surjective⟩
  have : IsDominant r := inferInstance
  set T₀ := DivisorWithCoeffs.roundDown B
  obtain ⟨S, hST, hSh, hSdeg, huniq⟩ := exists_unique_horizontal_of_sum_eq_one r B hB
    (fun P hP => residueFieldDegree_ne_zero_of_map_genericPoint_eq sY sV hYv hVn.1 r hr.comp_eq
      hdimY hdimV P hP)
    hdeg
  have hdim : topologicalKrullDim V < topologicalKrullDim Y := by
    rw [hdimV, hdimY]; exact_mod_cast (by norm_num : (2 : ℕ) < 3)
  by_cases hvert : ∃ P ∈ T₀.support, P ≠ S ∧ ∃ e ∈ (P.support : Set Y), r e = v
  · obtain ⟨P, hP, hPS, hvP⟩ := hvert
    have hPv : r.base P.genericPoint ≠ genericPoint V := fun h => hPS (huniq P hP h)
    have hsub := preimage_subset_support_of_map_genericPoint_ne sY sV hY hQ K R r hr hR B hnum ε hε
      hamp hdim P hPv hv hvP
    have hPT : (P.support : Set Y) ⊆ T₀.supp :=
      DivisorWithCoeffs.support_subset_supp (Finsupp.mem_support_iff.mp hP)
    rw [Set.inter_eq_right.mpr (hsub.trans hPT)]
    exact r.isConnected_preimage_singleton_of_isIso_app hr.isIso_app v
  · have heq : (T₀.supp : Set Y) ∩ r ⁻¹' {v} = (S.support : Set Y) ∩ r ⁻¹' {v} := by
      ext y
      refine ⟨fun ⟨hy, hyv⟩ => ⟨?_, hyv⟩, fun ⟨hy, hyv⟩ =>
        ⟨DivisorWithCoeffs.support_subset_supp (Finsupp.mem_support_iff.mp hST) hy, hyv⟩⟩
      obtain ⟨P, hP, hyP⟩ := DivisorWithCoeffs.mem_supp_iff.mp hy
      by_cases hPS : P = S
      · exact hPS ▸ hyP
      · exact absurd ⟨P, Finsupp.mem_support_iff.mpr hP, hPS, y, hyP, hyv⟩ hvert
    rw [heq]
    exact isConnected_support_inter_preimage_of_residueFieldDegree_eq_one sY sV hYv hVn r
      hr.comp_eq S hSh hSdeg v

/-! ### Connectedness of an ample floor -/

/-- On a normal scheme, irreducible and locally of finite type over a field, of dimension at
least two, the local ring at every closed point has depth at least two (Serre's `S₂`). -/
private theorem two_le_depth_stalk_of_isNormal {k : Type} [Field k] {N : Scheme.{0}}
    (sN : N ⟶ Spec (.of k)) [LocallyOfFiniteType sN] [IrreducibleSpace N]
    [IsLocallyNoetherian N] [IsNormal N] (hdim : 2 ≤ topologicalKrullDim N)
    (x : N) (hx : IsClosed ({x} : Set N)) :
    (2 : ℕ∞) ≤ Module.depth (N.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (N.presheaf.stalk x)) (N.presheaf.stalk x) := by
  have h := (hasPropertySk_iff N 2).mp (hasPropertySk_two_of_isNormal N) x
  rw [← topologicalKrullDimAt_eq_krullDimOfRing_stalk k N sN x hx,
    topologicalKrullDimAt_eq_topologicalKrullDim_of_equidimensional k N sN
      (TopologicalSpace.Equidimensional.of_preirreducibleSpace N) x, Nat.cast_ofNat,
    min_eq_left hdim] at h
  exact WithBot.coe_le_coe.1 h

/-- **An ample effective divisor pulled back to a normal scheme of dimension at
least two is connected.** Let `W` be an
integral normal scheme, proper over `k`, of dimension at least two, `φ : W ⟶ Y` a morphism and `M`
an effective Cartier divisor on `Y` such that `φ^* 𝒪_Y(M)` is ample and `φ(W) ⊄ Supp M`. Then
`φ⁻¹(Supp M)` is connected (in particular nonempty): it is the zero scheme of the pulled-back
canonical section, a regular section of an ample invertible sheaf on a scheme of depth at least
two at its closed points. -/
private theorem isConnected_preimage_supp_of_isAmple_pullback {k : Type} [Field k]
    {W Y : Scheme.{0}} (fW : W ⟶ Spec (.of k)) [IsProper fW] [IsIntegral W] [IsNormal W]
    (hdimW : 2 ≤ topologicalKrullDim W) [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    (φ : W ⟶ Y)
    (M : Divisor Y) (hM : M.IsCartier) (hM0 : 0 ≤ M)
    (hamp : haveI := hM.isInvertibleModule_divisorialSheaf
      Scheme.Modules.IsAmple W ((Scheme.Modules.pullback φ).obj M.divisorialSheaf))
    (hgen : ∃ w : W, φ w ∉ (M.supp : Set Y)) :
    _root_.IsConnected (φ ⁻¹' (M.supp : Set Y)) := by
  haveI := hM.isInvertibleModule_divisorialSheaf
  have : LocallyOfFiniteType fW := inferInstance
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian fW
  set L := M.divisorialSheaf
  set σ := MMP.Threefold.Mori.oneSection hM0
  haveI hLW : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2
      ((Scheme.Modules.pullback φ).obj L) := MMP.Mori.isInvertible_pullback_obj φ L
  set s := (Stacks.NonvanishingSpelling.sectionsEquiv W ((Scheme.Modules.pullback φ).obj L)).symm
    (Stacks.NonvanishingPullback.pullbackGlobalSection φ L σ)
  have hc : ∃ c : W, φ c ∈ Stacks.Ample.nonvanishingLocus L σ := by
    obtain ⟨w, hw⟩ := hgen
    exact ⟨w, MMP.Threefold.Mori.mem_nonvanishingLocus_oneSection_of_notMem_supp hM0 hw⟩
  have hs : s.eval (Opposite.op ⊤) ≠ 0 := MMP.Threefold.Mori.eval_pullbackSection_ne_zero φ L σ hc
  have hreg := isRegularSection_of_eval_top_ne_zero _ s hs
  have hconn := Stacks.AmpleSectionConnected.connectedSpace_zeroScheme_of_isAmple k fW
    ((Scheme.Modules.pullback φ).obj L) hamp s hreg
    (two_le_depth_stalk_of_isNormal fW hdimW)
  have hsupp : ((zeroScheme W ((Scheme.Modules.pullback φ).obj L) (s.eval (Opposite.op ⊤))).support
      : Set W) = φ ⁻¹' (M.supp : Set Y) := by
    have h1 := nonvanishingLocus_eq_compl_supportSet_zeroScheme _ s hs
    rw [MMP.Threefold.Mori.nonvanishingLocus_pullbackSection,
      MMP.Threefold.Mori.nonvanishingLocus_oneSection hM0 hM] at h1
    rw [← compl_compl (φ ⁻¹' (M.supp : Set Y)), ← Set.preimage_compl, h1, compl_compl]
    rfl
  rw [← hsupp, ← Scheme.IdealSheafData.range_subschemeι]
  exact isConnected_range (Scheme.Hom.continuous _)

/-! ### The floor is relatively ample -/

/-- The natural map `N₁(Y/V) → N₁(Y)` is injective: a relative class is numerically trivial on
`Y` exactly when it is so as a relative class. -/
private theorem relativeToAbsolute_injective {k : Type} [Field k] {Y V : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) (r : Y ⟶ V) :
    Function.Injective (relativeToAbsolute sY r) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro z hz
  obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sY r z
  rw [LinearMap.mem_ker] at hz
  change (OneCycle.numericallyTrivial sY).mkQ (Z : OneCycle ℝ sY) = 0 at hz
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hz
  change (relativeNumericallyTrivial sY r).mkQ Z = 0
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact mem_relativeNumericallyTrivial.mpr hz

/-- **Relative classes along an extremal ray are multiples of one curve.** If every curve
contracted by `r` has its class in the ray `R = ℝ_{≥0} v₀`, and `γ₀` is a contracted curve with
nonzero class, then every class of `N₁(Y/V)` is a real multiple of `[γ₀]`. -/
private theorem exists_eq_smul_relativeClass {k : Type} [Field k] {Y V : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) (r : Y ⟶ V) (R : Set (NumericalCurveClasses sY))
    {v₀ : NumericalCurveClasses sY} (hR : R = {w | ∃ c : ℝ, 0 ≤ c ∧ c • v₀ = w})
    (hcon : ∀ C : ProperCurve sY,
      C.IsContractedBy r ↔ OneCycle.numericalClass sY (C.cycle ℝ) ∈ R)
    (γ₀ : ProperCurve sY) (hγ₀ : γ₀.IsContractedBy r) (hne : γ₀.relativeClass r hγ₀ ≠ 0)
    (z : RelativeNumericalCurveClasses sY r) :
    ∃ t : ℝ, z = t • γ₀.relativeClass r hγ₀ := by
  set a := relativeToAbsolute sY r
  have hcl : ∀ (C : ProperCurve sY) (hC : C.IsContractedBy r),
      a (C.relativeClass r hC) = OneCycle.numericalClass sY (C.cycle ℝ) := fun _ _ => rfl
  have hspan : ∀ w : RelativeNumericalCurveClasses sY r, a w ∈ Submodule.span ℝ {v₀} := by
    intro w
    obtain ⟨⟨Z, hZ⟩, rfl⟩ := relativeNumericalClass_surjective sY r w
    change OneCycle.numericalClass sY Z ∈ _
    rw [← Finsupp.sum_single Z, map_finsuppSum]
    refine Submodule.sum_mem _ fun C hC => ?_
    have hCc : C.IsContractedBy r := hZ hC
    have hmem := (hcon C).mp hCc
    rw [hR] at hmem
    obtain ⟨c, -, hc⟩ := hmem
    show OneCycle.numericalClass sY (Finsupp.single C (Z C)) ∈ _
    rw [show (Finsupp.single C (Z C) : OneCycle ℝ sY) = Z C • C.cycle ℝ by
      rw [ProperCurve.cycle, Finsupp.smul_single, smul_eq_mul, mul_one], map_smul, ← hc,
      smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v₀)
  obtain ⟨c₀, hc₀⟩ := Submodule.mem_span_singleton.mp (hspan (γ₀.relativeClass r hγ₀))
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hspan z)
  have hc₀0 : c₀ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc₀
    exact hne (relativeToAbsolute_injective sY r (by rw [← hc₀, map_zero]))
  refine ⟨c / c₀, relativeToAbsolute_injective sY r ?_⟩
  rw [map_smul, ← hc₀, ← hc, smul_smul, div_mul_cancel₀ c hc₀0]

/-- **The floor is relatively ample.** In the setting of the main theorem, some positive
multiple `M = n⌊B⌋` is an `r`-ample Cartier divisor: it is positive on every contracted curve, and
the relative classes form a single ray, so the relative Kleiman criterion applies. -/
private theorem exists_isRelativelyAmple_floor {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {Y V : Scheme.{0}} (sY : Y ⟶ Spec (.of k)) (sV : V ⟶ Spec (.of k)) [IsIntegral Y]
    [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y] [QuasiCompact sY]
    (hY : MMP.Mori.IsProjectiveVariety k sY) (hQ : IsQFactorial sY)
    (K : Divisor Y) (R : Set (NumericalCurveClasses sY)) (r : Y ⟶ V)
    (hr : IsContractionOfRay sY sV R r) {v₀ : NumericalCurveClasses sY}
    (hR : R = {w | ∃ c : ℝ, 0 ≤ c ∧ c • v₀ = w}) (B : QDivisor Y) (hB : 0 ≤ B)
    (hnum : MMP.Flips.IsNumericallyTrivialOver k sY r
      (QDivisor.toRDivisor (Divisor.toQDivisor K + B)))
    (ε : ℚ) (hε : 0 < ε)
    (hamp : (-(Divisor.toQDivisor K +
      (B - ε • Divisor.toQDivisor (DivisorWithCoeffs.roundDown B)))).HasRelativelyAmpleMultiple r)
    (hdim : topologicalKrullDim V < topologicalKrullDim Y) :
    ∃ (M : Divisor Y) (hM : M.IsCartier), 0 ≤ M ∧
      M.supp = (DivisorWithCoeffs.roundDown B).supp ∧ M.IsRelativelyAmple r hM := by
  have hYv : AlgebraicGeometry.IsVariety k sY := hY.toIsVariety
  have hVv : AlgebraicGeometry.IsVariety k sV := hr.isNormalVariety_target.1
  have : IsIntegral V := hVv.toIsIntegral
  have : IsProper sY :=
    (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mp hY.isProjective).2
  have : IsProper r :=
    (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mp hr.isProjectiveMorphism).2
  have : Surjective r := ⟨hr.surjective⟩
  have : IsDominant r := inferInstance
  set T₀ := DivisorWithCoeffs.roundDown B
  have hT := MMP.Fourfold.isQCartier_of_isQFactorial sY hQ (Divisor.toQDivisor T₀)
  set n := (Divisor.toQDivisor T₀).cartierIndex hT
  have hn : 0 < n := QDivisor.cartierIndex_pos hT
  set hF := QDivisor.isCartierDivisor_cartierIndex_smul hT
  set M := hF.toDivisor
  have hMc : M.IsCartier := hF.isCartier_toDivisor
  have hMeq : M = (n : ℤ) • T₀ := Divisor.toQDivisor_injective (by
    rw [hF.toQDivisor_toDivisor, map_zsmul])
  have hcoeff : ∀ P, M.coeff P = (n : ℤ) * T₀.coeff P := fun P => by
    rw [hMeq]; rfl
  refine ⟨M, hMc, fun P => ?_, ?_, ?_⟩
  · change 0 ≤ M.coeff P
    rw [hcoeff, DivisorWithCoeffs.coeff_roundDown]
    exact mul_nonneg (by positivity) (Int.floor_nonneg.mpr (hB P))
  · ext y
    simp only [SetLike.mem_coe, DivisorWithCoeffs.mem_supp_iff, hcoeff]
    exact exists_congr fun P => and_congr_left' (mul_ne_zero_iff_left (by exact_mod_cast hn.ne'))
  -- positivity of `M` on contracted curves
  have hpos : ∀ C : ProperCurve sY, C.IsContractedBy r →
      0 < M.degreeOn k sY C.ι C.dim_le hMc := by
    intro C hC
    have h := intersectionNumber_roundDown_pos sY hYv hQ K B r hnum ε hε hamp C hC
    rw [QDivisor.intersectionNumber_eq_of_toQDivisor_eq k sY C.ι C.dim_le _ hT M hMc
      hF.toQDivisor_toDivisor] at h
    have hn' : (0 : ℚ) < n := by exact_mod_cast hn
    have := (div_pos_iff_of_pos_right hn').mp h
    exact_mod_cast this
  haveI := hMc.isInvertibleModule_divisorialSheaf
  obtain ⟨E, ⟨e⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf M.divisorialSheaf
  set I := RelativeNumericalCurveClasses.intersectionNumber (sX := sY) (f := r)
    (KCartierDivisor.ofCartier ℝ E)
  have hIC : ∀ (C : ProperCurve sY) (hC : C.IsContractedBy r),
      I (C.relativeClass r hC) = (M.degreeOn k sY C.ι C.dim_le hMc : ℝ) := by
    intro C hC
    change (C.cycle ℝ).intersectionNumber (KCartierDivisor.ofCartier ℝ E) = _
    rw [OneCycle.intersectionNumber_ofCartier, OneCycle.cartierDegree, OneCycle.degree_cycle]
    exact_mod_cast (degreeOn_eq_of_iso k sY C.ι C.dim_le e).symm
  have hIdeg : I = RelativeNumericalCurveClasses.degree sY r
      (MMP.CartierDivisor.sheaf E) := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun Z => ?_)
    change (Z : OneCycle ℝ sY).intersectionNumber (KCartierDivisor.ofCartier ℝ E) = _
    rw [OneCycle.intersectionNumber_ofCartier]
    rfl
  have hcont : Continuous I := by
    rw [hIdeg]; exact RelativeNumericalCurveClasses.continuous_degree sY r _
  obtain ⟨γ₀, hγ₀, -⟩ :=
    MMP.Fourfold.exists_properCurve_isContractedBy_of_lt hYv hVv r hr.comp_eq hdim
      (B := ∅) isClosed_empty (Set.notMem_empty _)
  have hγ₀pos : 0 < I (γ₀.relativeClass r hγ₀) := by
    rw [hIC]; exact_mod_cast hpos γ₀ hγ₀
  have hγ₀ne : γ₀.relativeClass r hγ₀ ≠ 0 := fun h => by
    rw [h, map_zero] at hγ₀pos; exact lt_irrefl _ hγ₀pos
  have hcone : (relativeClosedConeOfCurves sY r : Set (RelativeNumericalCurveClasses sY r)) ⊆
      {z | 0 ≤ I z} := by
    rw [coe_relativeClosedConeOfCurves]
    refine closure_minimal ?_ (isClosed_le continuous_const hcont)
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨C, hC⟩, rfl⟩ := hx
      show 0 ≤ I (C.relativeClass r hC)
      rw [hIC C hC]; exact_mod_cast (hpos C hC).le
    | zero => simp
    | add x y _ _ hx hy => simp only [Set.mem_setOf_eq, map_add] at hx hy ⊢; linarith
    | smul c x _ hx =>
      simp only [Set.mem_setOf_eq] at hx ⊢
      rw [show c • x = (c : ℝ) • x from rfl, map_smul, smul_eq_mul]
      exact mul_nonneg c.2 hx
  have hkle := MMP.Mori.isRelativelyAmple_cartierSheaf_iff_forall_relativeClosedConeOfCurves_pos
    sV sY r hr.isProjectiveMorphism.isProjective hr.comp_eq E
  have hampE := hkle.mpr fun z hz hz0 => by
    obtain ⟨t, rfl⟩ := exists_eq_smul_relativeClass sY r R hR hr.isContractedBy_iff γ₀ hγ₀
      hγ₀ne z
    have h0 := hcone hz
    simp only [Set.mem_setOf_eq, map_smul, smul_eq_mul] at h0
    change 0 < I (t • γ₀.relativeClass r hγ₀)
    rw [map_smul, smul_eq_mul]
    have ht : t ≠ 0 := fun h => hz0 (by rw [h, zero_smul])
    have ht' : 0 ≤ t := nonneg_of_mul_nonneg_left h0 hγ₀pos
    exact mul_pos (lt_of_le_of_ne ht' (Ne.symm ht)) hγ₀pos
  intro y
  obtain ⟨U, hU, hyU, hUa⟩ := hampE y
  refine ⟨U, hU, hyU, ?_⟩
  exact (Stacks.RelativeVeryAmple.isAmple_congr _ _
    ((RingedSpaceModuleAdjunction.modulePullback (r ⁻¹ᵁ U).ι.toLRSHom.toShHom).mapIso e)).mpr hUa

/-! ### Fibre dimension two -/

/-- If the generic point of the prime divisor `P` is closed, then `single P 1` is Cartier. -/
private theorem isCartier_single_of_isClosed {C : Scheme.{0}} [IsLocallyNoetherian C] [IsNormal C]
    [CompactSpace C] (P : MMP.Mori.PrimeDivisor C) (hc : IsClosed ({P.genericPoint} : Set C)) :
    Divisor.IsCartier (Finsupp.single P 1 : Divisor C) := by
  intro x
  by_cases hx : x = P.genericPoint
  · obtain ⟨U, -, φ, hxU, -, -, hφ⟩ :=
      MMP.Fourfold.exists_isLocalEquation_single_of_eq P x hx.symm
    exact ⟨U, hxU, φ, hφ⟩
  · refine ⟨⟨{P.genericPoint}ᶜ, hc.isOpen_compl⟩, hx, 1, ?_⟩
    rintro E' ⟨y, hyE', hyU⟩
    have hE'P : E' ≠ P := by
      rintro rfl
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, hc.closure_eq] at hyE'
      exact hyU hyE'
    rw [DivisorWithCoeffs.coeff_single_of_ne (Ne.symm hE'P), PrimeDivisor.ord_one]

/-- **The fibres over a curve are vertical prime divisors.** In the setting of the main theorem
with `dim V = 1`, the fibre of `r` over a closed point `v` is the support of a prime divisor:
it lies in the support of the fibre divisor `r^* v`, whose components over `v` are vertical and
therefore contain the whole fibre. -/
private theorem exists_primeDivisor_preimage_eq {k : Type} [Field k] {Y V : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) (sV : V ⟶ Spec (.of k)) [IsIntegral Y] [CompactSpace Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [QuasiCompact sY] [IsIntegral V]
    (hY : MMP.Mori.IsProjectiveVariety k sY) (hQ : IsQFactorial sY)
    (K : Divisor Y) (R : Set (NumericalCurveClasses sY)) (r : Y ⟶ V)
    (hr : IsContractionOfRay sY sV R r) {v₀ : NumericalCurveClasses sY}
    (hR : R = {w | ∃ c : ℝ, 0 ≤ c ∧ c • v₀ = w}) (B : QDivisor Y)
    (hnum : MMP.Flips.IsNumericallyTrivialOver k sY r
      (QDivisor.toRDivisor (Divisor.toQDivisor K + B)))
    (ε : ℚ) (hε : 0 < ε)
    (hamp : (-(Divisor.toQDivisor K +
      (B - ε • Divisor.toQDivisor (DivisorWithCoeffs.roundDown B)))).HasRelativelyAmpleMultiple r)
    (hdimY : topologicalKrullDim Y = 3) (hdimV : topologicalKrullDim V = 1)
    (v : V) (hv : IsClosed ({v} : Set V)) :
    ∃ E : MMP.Mori.PrimeDivisor Y, r ⁻¹' {v} = E.support := by
  have hVn : IsNormalVariety k sV := hr.isNormalVariety_target
  have hVv := hVn.1
  have := hVn.2
  have : LocallyOfFiniteType sV := hVv.toLocallyOfFiniteType
  have : QuasiCompact sV := hVv.toQuasiCompact
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian sV
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace sV
  have : Surjective r := ⟨hr.surjective⟩
  have : IsDominant r := inferInstance
  have hvη : v ≠ genericPoint V := fun h =>
    MMP.Fourfold.not_isClosed_genericPoint hdimV (h ▸ hv)
  set P : MMP.Mori.PrimeDivisor V := AlgebraicGeometry.PrimeDivisor.ofCoheightOne v
    (MMP.Fourfold.coheight_eq_one_of_ne_genericPoint hdimV hvη)
  have hPv : P.genericPoint = v := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
  have hPc : IsClosed ({P.genericPoint} : Set V) := hPv ▸ hv
  have hPC := isCartier_single_of_isClosed P hPc
  have hηY : r.base (genericPoint Y) = genericPoint V := map_genericPoint_of_isDominant r
  have hB : ∀ Z : irreducibleComponents Y,
      r (componentGenericPoint Y Z) ∉ DivisorWithCoeffs.supp (Finsupp.single P 1 : Divisor V) := by
    intro Z h
    rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint, hηY] at h
    obtain ⟨E', hE', hE'η⟩ := DivisorWithCoeffs.mem_supp_iff.mp h
    obtain rfl : E' = P := by
      by_contra hne
      exact hE' (DivisorWithCoeffs.coeff_single_of_ne (Ne.symm hne) _)
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, hPc.closure_eq,
      Set.mem_singleton_iff, hPv] at hE'η
    exact hvη hE'η.symm
  have hF := Divisor.isPullback_pullback (f := r) hPC hB
  set F := Divisor.pullback (f := r) (Finsupp.single P 1) hPC hB
  obtain ⟨y₀, hy₀⟩ := hr.surjective v
  have hy₀F := MMP.Fourfold.mem_supp_of_isPullback_single r P hF (x := y₀) (hy₀.trans hPv.symm)
  obtain ⟨E, hE, hy₀E⟩ := DivisorWithCoeffs.mem_supp_iff.mp hy₀F
  have hEv : r.base E.genericPoint = v := by
    by_contra h
    exact hE (MMP.Fourfold.coeff_eq_zero_of_isPullback_single r P hPc hF E (hPv ▸ h))
  have hdim : topologicalKrullDim V < topologicalKrullDim Y := by
    rw [hdimV, hdimY]; exact_mod_cast (by norm_num : (1 : ℕ) < 3)
  have hsub := preimage_subset_support_of_map_genericPoint_ne sY sV hY hQ K R r hr hR B hnum ε hε
    hamp hdim E (hEv.trans_ne hvη) hv ⟨y₀, hy₀E, hy₀⟩
  refine ⟨E, le_antisymm hsub fun x hx => ?_⟩
  have h1 : E.genericPoint ⤳ x := specializes_iff_mem_closure.mpr
    ((AlgebraicGeometry.PrimeDivisor.support_eq_closure E) ▸ hx)
  have h2 : v ⤳ r.base x := hEv ▸ h1.map r.continuous
  have := specializes_iff_mem_closure.mp h2
  rw [hv.closure_eq] at this
  exact this

/-- **The floor meets an irreducible fibre in a connected set.** Let `r : Y ⟶ V` be proper with
`r_* 𝒪_Y = 𝒪_V`, `M` an effective `r`-ample Cartier divisor, and `v` a closed point whose fibre
`Z = r⁻¹(v)` is irreducible of dimension `n ≥ 2`. Then `Supp M ∩ Z` is connected and nonempty:
either `Z ⊆ Supp M`, or `M` pulls back to an effective ample divisor on the normalization of `Z`,
whose support is connected, and maps onto `Supp M ∩ Z`. -/
private theorem isConnected_supp_inter_of_isIrreducible {k : Type} [Field k] {Y V : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (hYv : AlgebraicGeometry.IsVariety k sY) [IsProper sY] (r : Y ⟶ V)
    (hr : ∀ U : V.Opens, IsIso (r.app U)) [IsProper r]
    (M : Divisor Y) (hM : M.IsCartier) (hM0 : 0 ≤ M) (hMa : M.IsRelativelyAmple r hM)
    {v : V} (hv : IsClosed ({v} : Set V)) (hZirr : IsIrreducible (r ⁻¹' {v}))
    {n : ℕ} (hn : 2 ≤ n) (hZdim : topologicalKrullDim (r ⁻¹' {v}) = n) :
    _root_.IsConnected ((M.supp : Set Y) ∩ r ⁻¹' {v}) := by
  by_cases hsub : r ⁻¹' {v} ⊆ (M.supp : Set Y)
  · rw [Set.inter_eq_right.mpr hsub]
    exact r.isConnected_preimage_singleton_of_isIso_app hr v
  have hZc : IsClosed (r ⁻¹' {v}) := hv.preimage r.continuous
  set Zc : TopologicalSpace.Closeds Y := ⟨r ⁻¹' {v}, hZc⟩
  set I := Scheme.IdealSheafData.vanishingIdeal Zc
  have : IsIntegral I.subscheme :=
    StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible Zc hZirr
  set ιZ := I.subschemeι
  have hrange : Set.range ιZ = r ⁻¹' {v} := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have : LocallyOfFiniteType sY := hYv.toLocallyOfFiniteType
  have : IsSeparated sY := hYv.toIsSeparated
  have : QuasiCompact sY := hYv.toQuasiCompact
  set p := ιZ ≫ sY
  haveI hpv : AlgebraicGeometry.IsVariety k p :=
    @AlgebraicGeometry.IsVariety.mk _ _ _ _ inferInstance inferInstance inferInstance
      inferInstance
  set Zn := normalizationSchemeOverField k p
  set ν := normalizationOverField k p
  haveI : IsFinite ν := isFinite_normalizationOverField k p
  haveI hZnv : AlgebraicGeometry.IsVariety k (ν ≫ p) := isVariety_normalizationOverField k p
  haveI : IsIntegral Zn := hZnv.toIsIntegral
  haveI : IsNormal Zn := Scheme.isNormal_normalizationScheme _ _
  haveI : IsDominant ν := isDominant_normalizationOverField k p
  have hνs : Function.Surjective ν := by
    have hcl : IsClosed (Set.range ν) := ν.isClosedMap.isClosed_range
    have : Set.range ν = Set.univ := by
      rw [← hcl.closure_eq]; exact ν.denseRange.closure_range
    exact Set.range_eq_univ.mp this
  have hdimZn : topologicalKrullDim Zn = n := by
    have hI : topologicalKrullDim I.subscheme = n := by
      rw [MMP.Mori.topologicalKrullDim_subscheme_eq,
        Scheme.IdealSheafData.coe_support_vanishingIdeal]
      exact hZdim
    rw [topologicalKrullDim_normalizationSchemeOverField k p, hI]
  haveI : IsProper (ν ≫ p) := by
    change IsProper (ν ≫ ιZ ≫ sY); infer_instance
  set φ := ν ≫ ιZ
  -- the ample restriction of `𝒪_Y(M)` near the fibre
  haveI := hM.isInvertibleModule_divisorialSheaf
  obtain ⟨U, -, hvU, hUa⟩ := hMa v
  have hZU : Set.range ιZ ⊆ Set.range (r ⁻¹ᵁ U).ι := by
    rw [hrange, Scheme.Opens.range_ι]
    intro y hy
    show r y ∈ U
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hy
    rw [hy]; exact hvU
  set j := IsOpenImmersion.lift (r ⁻¹ᵁ U).ι ιZ hZU
  have hj : j ≫ (r ⁻¹ᵁ U).ι = ιZ := IsOpenImmersion.lift_fac _ _ _
  haveI : IsClosedImmersion (j ≫ (r ⁻¹ᵁ U).ι) := by rw [hj]; infer_instance
  haveI : IsClosedImmersion j := IsClosedImmersion.of_comp j (r ⁻¹ᵁ U).ι
  set L := M.divisorialSheaf
  set L' := (RingedSpaceModuleAdjunction.modulePullback (r ⁻¹ᵁ U).ι.toLRSHom.toShHom).obj L
  haveI hL'inv : SheafOfModules.IsInvertible (r ⁻¹ᵁ U).toScheme.presheaf
      (r ⁻¹ᵁ U).toScheme.ringCatSheaf.2 L' :=
    Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry
      (r ⁻¹ᵁ U).ι.toLRSHom.toShHom _ inferInstance
  have h1 : Scheme.Modules.IsAmple (r ⁻¹ᵁ U).toScheme L' :=
    (Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple _ _).mpr hUa
  have h2 := isAmple_pullback_of_isFinite (ν ≫ j) L' h1
  let e : (Scheme.Modules.pullback (ν ≫ j)).obj L' ≅ (Scheme.Modules.pullback φ).obj L :=
    (Scheme.Modules.pullback (ν ≫ j)).mapIso
        ((AlgebraicGeometry.modulePullbackIsoSchemePullback (r ⁻¹ᵁ U).ι).app L) ≪≫
      (Scheme.Modules.pullbackComp (ν ≫ j) (r ⁻¹ᵁ U).ι).app L ≪≫
        eqToIso (by rw [Category.assoc, hj])
  have hamp : Scheme.Modules.IsAmple Zn ((Scheme.Modules.pullback φ).obj L) := by
    haveI := MMP.Mori.isInvertible_pullback_obj (ν ≫ j) L'
    haveI := MMP.Mori.isInvertible_pullback_obj φ L
    haveI := Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _
      (MMP.Mori.isInvertible_pullback_obj (ν ≫ j) L')
    haveI := Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _
      (MMP.Mori.isInvertible_pullback_obj φ L)
    rw [Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple] at h2 ⊢
    exact (Stacks.RelativeVeryAmple.isAmple_congr _ _ e).mp h2
  -- the generic point of the fibre is not in `Supp M`
  have hgen : ∃ w : Zn, φ w ∉ (M.supp : Set Y) := by
    obtain ⟨y, hyZ, hyM⟩ := Set.not_subset.mp hsub
    rw [← hrange] at hyZ
    obtain ⟨z, rfl⟩ := hyZ
    obtain ⟨w, rfl⟩ := hνs z
    exact ⟨w, hyM⟩
  have hdim2 : 2 ≤ topologicalKrullDim Zn := by
    rw [hdimZn]; exact_mod_cast hn
  have hconn := isConnected_preimage_supp_of_isAmple_pullback (ν ≫ p) hdim2 φ M hM hM0 hamp hgen
  have himg : φ '' (φ ⁻¹' (M.supp : Set Y)) = (M.supp : Set Y) ∩ r ⁻¹' {v} := by
    rw [Set.image_preimage_eq_inter_range]
    congr 1
    change Set.range (ν ≫ ιZ) = _
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hνs.range_eq, Set.image_univ,
      hrange]
  rw [← himg]
  exact hconn.image _ φ.continuous.continuousOn

open scoped Classical in
/-- Let `r : Y ⟶ V` be the contraction of a `(K + B - ε⌊B⌋)`-negative extremal ray `R` of a
`ℚ`-factorial projective threefold `Y`, where `K + B` is numerically `r`-trivial, `(Y, B)` is log
canonical, `(Y, B - ε⌊B⌋)` is klt and `-(K + B - ε⌊B⌋)` is `r`-ample. If `dim V ≤ 1`, or
`dim V = 2` and the components of `⌊B⌋` dominating `V` have total degree one over `V`, then every
fibre of `⌊B⌋ ⟶ V` is connected and the restriction of `r` to `⌊B⌋` induces an isomorphism on
sections of the structure sheaf over every open subset of `V`. -/
theorem isConnected_fibre_floor_and_isIso_app
    {k : Type} [Field k] {Y V : Scheme.{0}} (sY : Y ⟶ Spec (.of k)) (sV : V ⟶ Spec (.of k))
    [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y] [QuasiCompact sY]
    [IsIntegral V]
    (hY : MMP.Mori.IsProjectiveVariety k sY) (hdimY : topologicalKrullDim Y = 3)
    (hQ : IsQFactorial sY)
    (K : Divisor Y) (hK : K.IsCanonicalDivisor sY 3)
    (R : Set (NumericalCurveClasses sY)) (r : Y ⟶ V) (hr : IsContractionOfRay sY sV R r)
    (hρ : relativePicardNumberN1 sY r = 1)
    (B : QDivisor Y) (hB : 0 ≤ B) (hlc : MMP.Intersection.IsLogCanonicalPair sY B)
    (hnum : MMP.Flips.IsNumericallyTrivialOver k sY r
      (QDivisor.toRDivisor (Divisor.toQDivisor K + B)))
    (ε : ℚ) (hε : 0 < ε)
    (hklt : IsKltPair sY (B - ε • Divisor.toQDivisor (DivisorWithCoeffs.roundDown B)))
    (hR : IsNegativeExtremalRayOf sY
      (Divisor.toQDivisor K + (B - ε • Divisor.toQDivisor (DivisorWithCoeffs.roundDown B))) R)
    (hamp : (-(Divisor.toQDivisor K +
      (B - ε • Divisor.toQDivisor (DivisorWithCoeffs.roundDown B)))).HasRelativelyAmpleMultiple r)
    (hcase : topologicalKrullDim V ≤ 1 ∨
      (topologicalKrullDim V = 2 ∧
        ∑ P ∈ (DivisorWithCoeffs.roundDown B).support with
            r.base P.genericPoint = genericPoint V,
          (DivisorWithCoeffs.roundDown B).coeff P *
            (letI := (r.residueFieldMap P.genericPoint).hom.toAlgebra
             (Module.finrank (V.residueField (r.base P.genericPoint))
              (Y.residueField P.genericPoint) : ℤ)) = 1)) :
    (∀ v : V, _root_.IsConnected
      (((DivisorWithCoeffs.roundDown B).suppIdeal.subschemeι ≫ r).base ⁻¹' {v})) ∧
    ∀ U : V.Opens, IsIso (((DivisorWithCoeffs.roundDown B).suppIdeal.subschemeι ≫ r).app U) := by
  have hkac : IsAlgClosed k := hklt.1.isAlgClosed
  have hk0 : CharZero k := hklt.1.charZero
  obtain ⟨-, ⟨-, v₀, -, hRv⟩, -⟩ := hR
  set D := DivisorWithCoeffs.roundDown B with hD
  set ι := D.suppIdeal.subschemeι with hι
  have hVn : IsNormalVariety k sV := hr.isNormalVariety_target
  have : IsProper r :=
    (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mp hr.isProjectiveMorphism).2
  have : IsNoetherian Y := ⟨⟩
  have : IsReduced D.suppIdeal.subscheme :=
    Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  have : IsLocallyNoetherian D.suppIdeal.subscheme := LocallyOfFiniteType.isLocallyNoetherian ι
  have : CompactSpace D.suppIdeal.subscheme := QuasiCompact.compactSpace_of_compactSpace ι
  have : IsNoetherian D.suppIdeal.subscheme := ⟨⟩
  have hclosed : ∀ v : V, IsClosed ({v} : Set V) →
      _root_.IsConnected ((D.supp : Set Y) ∩ r.base ⁻¹' {v}) := by
    intro v hv
    rcases hcase with h01 | ⟨h2, hdeg⟩
    · have hYv : AlgebraicGeometry.IsVariety k sY := hY.toIsVariety
      have : IsProper sY :=
        (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mp hY.isProjective).2
      have hdimlt : topologicalKrullDim V < topologicalKrullDim Y := by
        refine lt_of_le_of_lt h01 ?_
        rw [hdimY]; exact_mod_cast (by norm_num : (1 : ℕ) < 3)
      obtain ⟨M, hM, hM0, hMsupp, hMa⟩ :=
        exists_isRelativelyAmple_floor sY sV hY hQ K R r hr hRv B hB hnum ε hε hamp hdimlt
      rw [← hMsupp]
      have hVv := hVn.1
      have : LocallyOfFiniteType sV := hVv.toLocallyOfFiniteType
      have : LocallyOfFiniteType sY := hYv.toLocallyOfFiniteType
      -- `dim V` is `0` or `1`
      have hV01 : topologicalKrullDim V = 0 ∨ topologicalKrullDim V = 1 := by
        have h0 : (0 : WithBot ℕ∞) ≤ topologicalKrullDim V := by
          haveI : Nonempty (TopologicalSpace.IrreducibleCloseds V) :=
            ⟨⟨Set.univ, IrreducibleSpace.isIrreducible_univ V, isClosed_univ⟩⟩
          exact Order.krullDim_nonneg
        induction h : topologicalKrullDim V using WithBot.recBotCoe with
        | bot => rw [h] at h0; exact absurd h0 (by decide)
        | coe d =>
          rw [h] at h01
          induction d using ENat.recTopCoe with
          | top => exact absurd h01 (by decide)
          | coe d =>
            have : d ≤ 1 := by exact_mod_cast h01
            interval_cases d
            · left; rfl
            · right; rfl
      rcases hV01 with h0 | h1
      · -- `V` is a point: the fibre is all of `Y`
        have hall : r.base ⁻¹' {v} = Set.univ := by
          have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sV v
          rw [hv.closure_eq, h0] at h
          have : Subsingleton ({v} : Set V) := Set.subsingleton_singleton.coe_sort
          have : Nonempty ({v} : Set V) := ⟨⟨v, rfl⟩⟩
          rw [topologicalKrullDim_eq_zero_of_subsingleton, zero_add] at h
          have hcoh : Order.coheight v = 0 := by exact_mod_cast h
          have hvη : v = genericPoint V := by
            have hle : v ≤ genericPoint V :=
              Scheme.le_iff_specializes.mpr ((genericPoint_spec V).specializes trivial)
            have := Order.coheight_eq_zero.mp hcoh hle
            exact ((Scheme.le_iff_specializes.mp this).antisymm
              (Scheme.le_iff_specializes.mp hle)).eq
          refine Set.eq_univ_of_forall fun y => ?_
          have : r.base y ∈ closure ({genericPoint V} : Set V) := by
            rw [(genericPoint_spec V).def]; trivial
          rw [← hvη, hv.closure_eq] at this
          exact this
        refine isConnected_supp_inter_of_isIrreducible sY hYv r hr.isIso_app M hM hM0 hMa hv
          (hall ▸ IrreducibleSpace.isIrreducible_univ Y) (n := 3) (by norm_num) ?_
        rw [hall, (Homeomorph.Set.univ Y).isHomeomorph.topologicalKrullDim_eq, hdimY]
        rfl
      · obtain ⟨E, hE⟩ := exists_primeDivisor_preimage_eq sY sV hY hQ K R r hr hRv B hnum ε hε
          hamp hdimY h1 v hv
        have hEirr : IsIrreducible (E.support : Set Y) := by
          rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
          exact isIrreducible_singleton.closure
        refine isConnected_supp_inter_of_isIrreducible sY hYv r hr.isIso_app M hM hM0 hMa hv
          (hE ▸ hEirr) (n := 2) le_rfl ?_
        rw [hE, (MMP.Spreading.topologicalKrullDim_support sY (d := 3) hdimY E).2]
    · exact isConnected_floor_inter_fibre_of_eq_two sY sV hY hdimY hQ K R r hr hRv B hB hnum ε hε
        hamp h2 hdeg v hv
  have hfib : ∀ v : V, IsClosed ({v} : Set V) →
      _root_.IsConnected ((ι ≫ r).base ⁻¹' {v}) := by
    intro v hv
    have himg : ι.base '' ((ι ≫ r).base ⁻¹' {v}) = (D.supp : Set Y) ∩ r.base ⁻¹' {v} := by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp,
        Set.image_preimage_eq_inter_range, Scheme.IdealSheafData.range_subschemeι,
        DivisorWithCoeffs.coe_support_suppIdeal, Set.inter_comm]
    have hc := hclosed v hv
    rw [← himg] at hc
    exact ⟨hc.nonempty.of_image, ι.isClosedEmbedding.isInducing.isPreconnected_image.mp hc.2⟩
  have hiso := isIso_app_of_isConnected_closed_fibres sV hVn (ι ≫ r) hfib
  exact ⟨(ι ≫ r).isConnected_preimage_singleton_of_isIso_app hiso, hiso⟩

end MMP.FourfoldProofs.FourfoldMoriThreefoldConnectedFloorCasesProof

end

section

/-!
# The connected-floor cases of a threefold Mori endpoint

Let `Y` be a `ℚ`-factorial normal projective threefold over an algebraically closed field of
characteristic zero, with canonical divisor `K`, and let `r : Y ⟶ V` be the contraction of an
extremal ray `R` with `ρ(Y/V) = 1`. Let `B ≥ 0` be a `ℚ`-divisor with `(Y, B)` lc and
`K + B ≡_r 0`, and let `0 < ε` be such that the lowered pair `(Y, B - ε⌊B⌋)` is klt, `R` is
`(K + B - ε⌊B⌋)`-negative and `-(K + B - ε⌊B⌋)` is `r`-ample. Write `T = ⌊B⌋`, with its reduced
structure. If `dim V ≤ 1` (fibres of dimension at least two), or if `dim V = 2` (the generic fibre
is a curve) and the horizontal part of `T` has degree one over `V`, then every fibre of
`T ⟶ V` is connected and nonempty, and `r_* 𝒪_T = 𝒪_V`.

## Main results

* `MMP.Fourfold.IsContractionOfRay.isConnected_fibre_floor_and_isIso_app`

## Implementation notes

The source works over `ℂ`; the statement is over any field `k`, and the klt hypothesis
(`MMP.Fourfold.IsKltPair`) makes `k` algebraically closed of characteristic zero. The fibre
dimension of the fibre-type contraction `r` is `dim Y - dim V = 3 - dim V`. The reduced floor is
`MMP.Mori.DivisorWithCoeffs.suppScheme` of `⌊B⌋`. The degree of the horizontal floor is the degree
of `⌊B⌋` restricted to the generic fibre: `∑ ⌊B⌋_P · [κ(η_P) : κ(η_V)]` over the prime divisors
`P` of `⌊B⌋` whose generic point maps to the generic point of `V`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips]
-/

open CategoryTheory AlgebraicGeometry MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open scoped Classical in
/-- **The connected-floor cases of a threefold Mori endpoint.** Let `Y` be a `ℚ`-factorial normal
projective threefold with canonical divisor `K`, `r : Y ⟶ V` the contraction of an extremal ray
`R` with `ρ(Y/V) = 1`, `B ≥ 0` a `ℚ`-divisor with `(Y, B)` lc and `K + B ≡_r 0`, and `0 < ε` with
`(Y, B - ε⌊B⌋)` klt, `R` negative for `K + B - ε⌊B⌋` and `-(K + B - ε⌊B⌋)` `r`-ample. Let
`ι : T ⟶ Y` be the reduced floor `T = ⌊B⌋`. If `dim V ≤ 1`, or `dim V = 2` and the horizontal
part of `⌊B⌋` has degree one over `V`, then every fibre of `ι ≫ r` is connected and nonempty and
`(ι ≫ r)_* 𝒪_T = 𝒪_V`. -/
@[mmp "lem_fourfold_mori_threefold_connected_floor_cases"]
public theorem IsContractionOfRay.isConnected_fibre_floor_and_isIso_app
    {k : Type} [Field k] {Y V : Scheme.{0}} (sY : Y ⟶ Spec (.of k)) (sV : V ⟶ Spec (.of k))
    [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y] [QuasiCompact sY]
    [IsIntegral V]
    (hY : MMP.Mori.IsProjectiveVariety k sY) (hdimY : topologicalKrullDim Y = 3)
    (hQ : IsQFactorial sY)
    (K : Divisor Y) (hK : K.IsCanonicalDivisor sY 3)
    (R : Set (NumericalCurveClasses sY)) (r : Y ⟶ V) (hr : IsContractionOfRay sY sV R r)
    (hρ : relativePicardNumberN1 sY r = 1)
    (B : QDivisor Y) (hB : 0 ≤ B) (hlc : MMP.Intersection.IsLogCanonicalPair sY B)
    (hnum : MMP.Flips.IsNumericallyTrivialOver k sY r
      (QDivisor.toRDivisor (Divisor.toQDivisor K + B)))
    (ε : ℚ) (hε : 0 < ε)
    (hklt : IsKltPair sY (B - ε • Divisor.toQDivisor (DivisorWithCoeffs.roundDown B)))
    (hR : IsNegativeExtremalRayOf sY
      (Divisor.toQDivisor K + (B - ε • Divisor.toQDivisor (DivisorWithCoeffs.roundDown B))) R)
    (hamp : (-(Divisor.toQDivisor K +
      (B - ε • Divisor.toQDivisor (DivisorWithCoeffs.roundDown B)))).HasRelativelyAmpleMultiple r)
    (hcase : topologicalKrullDim V ≤ 1 ∨
      (topologicalKrullDim V = 2 ∧
        ∑ P ∈ (DivisorWithCoeffs.roundDown B).support with
            r.base P.genericPoint = genericPoint V,
          (DivisorWithCoeffs.roundDown B).coeff P *
            (letI := (r.residueFieldMap P.genericPoint).hom.toAlgebra
             (Module.finrank (V.residueField (r.base P.genericPoint))
              (Y.residueField P.genericPoint) : ℤ)) = 1)) :
    (∀ v : V, _root_.IsConnected
      (((DivisorWithCoeffs.roundDown B).suppIdeal.subschemeι ≫ r).base ⁻¹' {v})) ∧
    ∀ U : V.Opens, IsIso (((DivisorWithCoeffs.roundDown B).suppIdeal.subschemeι ≫ r).app U) :=
  MMP.FourfoldProofs.FourfoldMoriThreefoldConnectedFloorCasesProof.isConnected_fibre_floor_and_isIso_app
    sY sV hY hdimY hQ K hK R r hr hρ B hB hlc hnum ε hε hklt hR hamp hcase

end MMP.Fourfold

end
