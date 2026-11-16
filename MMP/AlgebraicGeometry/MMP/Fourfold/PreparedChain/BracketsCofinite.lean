module

public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChainBracket
public import Mathlib
public import MMP.Attr
import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldBadBranchCount
import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Singularities.Deminormal.Basic
import MMP.AlgebraicGeometry.Singularities.Semismooth.SingularLocus
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.MMP.Fourfold.Echoes
import MMP.AlgebraicGeometry.Singularities.Terminal.PairSmoothCodimTwo
import MMP.AlgebraicGeometry.MMP.Fourfold.SurfaceEchoLogDiscrepancy
import MMP.AlgebraicGeometry.Singularities.WeightedMonomialValuation
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.PrimeDivisorPersistence
import MMP.AlgebraicGeometry.Resolution.SmoothBlowupCanonical
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleEmbedding
import MMP.AlgebraicGeometry.MMP.Fourfold.Termination.PreparedChainTerminal
import MMP.AlgebraicGeometry.Normalization.IntegralScheme

/-!
# Surface brackets vanish at almost every surface

Let `(Y, Θ)` be a model of a prepared chain of fourfolds. The bracket
`β_V(Y, Θ) = ∑_{c_Y(v) = V} w_v - ∑_h r_{V,h} d_h` is `0` at every irreducible surface
`V ⊆ Y` outside a finite set.

The pair `(Y, Θ)` is terminal, `ℚ`-factorial and projective, so `Y` is smooth in codimension two,
and off a finite set `𝒮` of surfaces every valuation with centre `V` and log discrepancy `< 2`
is an echo `ξ_j` of a label `S_h` through `V`, with `η_V` in the one-label smooth locus. Off `𝒮`
either no valuation with centre `V` has `a < 2`: then all weights at `V` vanish, and a label
through `V` with positive coefficient `b_h` would give, through the monomial valuation of
weights `(1, 1)` at `η_V`, a valuation with centre `V` and `a ≤ 2 - b_h < 2`, so every label
through `V` has `b_h = 0` and `d_h = d(0) = 0`. Or the valuations of nonzero weight at `V` are
the echoes `ξ_j` of the unique label `S_h` through `η_V`, with `a(ξ_j) = 1 + j (1 - b_h)`; their
weights sum to `d(b_h) = d_h`, and `r_{V,h} = 1` because `S_h` is regular at `η_V`.

## Main results

* `MMP.Fourfold.StabilizedSmallKltTail.PreparedChain.finite_setOf_not_isSurfaceBracket_zero`:
  only finitely many irreducible surfaces `V` of a model fail to have bracket `0`.

## Implementation notes

The bracket is the predicate
`MMP.Fourfold.StabilizedSmallKltTail.PreparedChain.IsSurfaceBracket` on its value. The result
is stated as finiteness of the set of irreducible closed subsets `V` with
`topologicalKrullDim V = 2` at which `0` is *not* a bracket; off this set the bracket exists
and equals `0`.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.OAI4C2BracketsCofinite

open MMP.Fourfold MMP.Fourfold.StabilizedSmallKltTail MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-! ### Dimension arithmetic -/

/-- In `WithBot ℕ∞`, `a + c = a + n` with `a, n` natural numbers forces `c = n`. -/
private theorem eq_of_natCast_add_eq {a n : ℕ} {c : ℕ∞}
    (h : ((a : ℕ∞) : WithBot ℕ∞) + (c : WithBot ℕ∞) = (((a + n : ℕ) : ℕ∞) : WithBot ℕ∞)) :
    c = n := by
  have h' : (a : ℕ∞) + c = ((a + n : ℕ) : ℕ∞) := WithBot.coe_injective (by simpa using h)
  induction c using ENat.recTopCoe with
  | top =>
    rw [add_top] at h'
    exact absurd h' (ENat.top_ne_coe _)
  | coe m =>
    have : a + m = a + n := by exact_mod_cast h'
    exact_mod_cast (Nat.add_left_cancel this)

/-- On a fourfold of finite type over `ℂ`, the generic point of an irreducible closed surface has
coheight two. -/
private theorem coheight_genericPoint_eq_two {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ))
    [IsIntegral Y] [LocallyOfFiniteType sY] (hdim : topologicalKrullDim Y = 4)
    {V : IrreducibleCloseds Y} (hV : topologicalKrullDim (V : Set Y) = 2) :
    Order.coheight V.isIrreducible.genericPoint = 2 := by
  have hdf := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY
    V.isIrreducible.genericPoint
  rw [(V.isIrreducible.isGenericPoint_genericPoint V.isClosed).def, hV, hdim] at hdf
  exact eq_of_natCast_add_eq (a := 2) (n := 2) hdf

/-- In `WithBot ℕ∞`, `d + 1 = n + 1` forces `d = n`. -/
private theorem eq_of_add_one_eq {d : WithBot ℕ∞} {n : ℕ} (h : d + 1 = ((n + 1 : ℕ) : ℕ∞)) :
    d = (n : ℕ∞) := by
  induction d using WithBot.recBotCoe with
  | bot => exact (WithBot.bot_ne_coe h).elim
  | coe e =>
    induction e using ENat.recTopCoe with
    | top => exact (ENat.top_ne_coe (n + 1) (WithBot.coe_injective h)).elim
    | coe m =>
      have h' : ((m + 1 : ℕ) : ℕ∞) = ((n + 1 : ℕ) : ℕ∞) := WithBot.coe_injective (by simpa using h)
      rw [Nat.succ_injective (by exact_mod_cast h' : m + 1 = n + 1)]

/-! ### Regularity in codimension two -/

/-- On a terminal `ℚ`-factorial pair `(Y, Θ)` on a fourfold over `ℂ`, the local ring of `Y` at
the generic point of an irreducible closed surface is regular: the singular locus of `Y` has
codimension at least three. -/
private theorem isRegularLocalRing_stalk_genericPoint {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)} {Θ : MMP.Mori.QDivisor Y}
    (hΘ : MMP.Fourfold.IsKltTerminalPair sY Θ) (hQf : IsQFactorial sY)
    (hdim : topologicalKrullDim Y = 4) {V : IrreducibleCloseds Y}
    (hV : topologicalKrullDim (V : Set Y) = 2) :
    IsRegularLocalRing (Y.presheaf.stalk V.isIrreducible.genericPoint) := by
  have hlft : LocallyOfFiniteType sY := hΘ.1.1.isPair.1.1.toLocallyOfFiniteType
  obtain ⟨-, n, K, hK, -⟩ := hΘ.1.1.isPair
  have h3 := (hΘ.isTerminalVariety_and_three_le_closedsCodimension_singularLocus
    (isQCartier_of_isQFactorial sY hQf Θ) hK (isQCartier_of_isQFactorial sY hQf _)).2
  have hη : V.isIrreducible.genericPoint ∈ smoothLocus sY := by
    by_contra h
    have h' := MMP.Flips.le_closedsCodimension_iff_le_coheight.mp h3 _
      (mem_singularLocus_iff.mpr h)
    rw [coheight_genericPoint_eq_two sY hdim hV] at h'
    exact absurd h' (by decide)
  obtain ⟨U, hyU, hU⟩ := mem_smoothLocus_iff.mp hη
  have : Smooth (U.ι ≫ sY) := hU
  have := isRegularLocalRing_stalk_of_smooth_over_field (U.ι ≫ sY) ⟨_, hyU⟩
  exact IsRegularLocalRing.of_ringEquiv (U.stalkIso ⟨_, hyU⟩).commRingCatIsoToRingEquiv

/-! ### A low-discrepancy valuation along a surface inside a boundary component -/

/-- The order-reversing monoid map `WithTop ℤ → ℤᵐ⁰`, `n ↦ exp (-n)`, `⊤ ↦ 0`. -/
private def expNeg : WithTop ℤ → (WithZero (Multiplicative ℤ))
  | ⊤ => 0
  | (n : ℤ) => WithZero.exp (-n)

private theorem expNeg_coe (n : ℤ) : expNeg n = WithZero.exp (-n) := rfl

private theorem expNeg_top : expNeg ⊤ = 0 := rfl

private theorem expNeg_add (a b : WithTop ℤ) : expNeg (a + b) = expNeg a * expNeg b := by
  cases a <;> cases b <;>
    simp [expNeg_top, ← WithTop.coe_add, expNeg_coe, neg_add, WithZero.exp_add, mul_comm]

private theorem expNeg_antitone : Antitone expNeg := by
  intro a b h
  cases b with
  | top => simp [expNeg_top]
  | coe n =>
    cases a with
    | top => simp at h
    | coe m =>
      simp only [expNeg_coe, WithZero.exp_le_exp, neg_le_neg_iff]
      exact_mod_cast h

/-- The multiplicative valuation `z ↦ exp (-V z)` attached to an additive valuation `V`. -/
private def valuationOfAddValuation {R : Type*} [Ring R] (V : AddValuation R (WithTop ℤ)) :
    Valuation R (WithZero (Multiplicative ℤ)) where
  toFun z := expNeg (V z)
  map_zero' := by simp [expNeg_top]
  map_one' := by simp [← WithTop.coe_zero, expNeg_coe]
  map_mul' a b := by simp [V.map_mul, expNeg_add]
  map_add_le_max' a b := by
    rw [← expNeg_antitone.map_min]
    exact expNeg_antitone (V.map_add a b)

private theorem valuationOfAddValuation_apply {R : Type*} [Ring R]
    (V : AddValuation R (WithTop ℤ)) (z : R) :
    valuationOfAddValuation V z = expNeg (V z) := rfl

private theorem isRegularSystemOfParameters_swap {R : Type*} [CommRing R] [IsLocalRing R]
    {x y : R} (hxy : MMP.Mori.IsRegularSystemOfParameters ![x, y]) :
    MMP.Mori.IsRegularSystemOfParameters ![y, x] := by
  refine ⟨?_, hxy.2⟩
  rw [← hxy.1]
  congr 1
  ext
  simp [Matrix.range_cons, Set.pair_comm]

/-- At a point with regular local ring, every prime divisor has a local equation: its stalk
ideal is principal, generated by a nonzero element. -/
private theorem exists_stalk_idealSheaf_eq_span {X : Scheme.{0}} [IsIntegral X] {η : X}
    [IsRegularLocalRing (X.presheaf.stalk η)] (S : MMP.Mori.PrimeDivisor X) :
    ∃ g : X.presheaf.stalk η, g ≠ 0 ∧ IdealSheafData.stalk S.idealSheaf η = Ideal.span {g} := by
  have : IsDomain (X.presheaf.stalk η) := IsRegularLocalRing.isDomain _
  have : UniqueFactorizationMonoid (X.presheaf.stalk η) :=
    IsRegularLocalRing.uniqueFactorizationMonoid _
  by_cases hS : η ∈ S.support
  · obtain ⟨q, -, hq, hh⟩ := MMP.Intersection.exists_stalk_idealSheaf_eq_of_mem_support S hS
    obtain ⟨g, hg⟩ := (UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hh).principal
    refine ⟨g, ?_, hq.trans hg⟩
    rintro rfl
    exact q.asIdeal.ne_bot_of_height_eq_one hh (by rw [hg, Ideal.span_singleton_eq_bot])
  · exact ⟨1, one_ne_zero, (MMP.Intersection.stalk_idealSheaf_eq_top_of_notMem_support S hS).trans
      Ideal.span_singleton_one.symm⟩

/-- **A low-discrepancy valuation along a surface in the boundary.** Let `(Y, Θ)` be a pair on a
normal fourfold, regular at the generic point `η_V` of an irreducible closed surface `V`, and let
`V ⊆ S` for a prime divisor `S` with `Θ(S) > 0`. Then some valuation with centre `V` has log
discrepancy `< 2` with respect to `(Y, Θ)`; it is realised by the monomial valuation with weights
`(1, 1)` at `η_V`. -/
private theorem exists_isCentre_hasLogDiscrepancy_lt_two {Y : Scheme.{0}}
    {sY : Y ⟶ Spec (.of ℂ)} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {Θ : MMP.Mori.QDivisor Y} (hΘ : MMP.Fourfold.IsPair sY Θ)
    (hdim : topologicalKrullDim Y = 4)
    {V : IrreducibleCloseds Y} (hV : topologicalKrullDim (V : Set Y) = 2)
    [IsRegularLocalRing (Y.presheaf.stalk V.isIrreducible.genericPoint)]
    {S : MMP.Mori.PrimeDivisor Y} (hVS : (V : Set Y) ⊆ S.support) (hb : 0 < Θ.coeff S) :
    ∃ v : Valuation Y.functionField (WithZero (Multiplicative ℤ)),
      MMP.Intersection.IsCentre ℂ sY v V ∧ ∃ a < 2, MMP.Fourfold.HasLogDiscrepancy sY Θ v a := by
  classical
  have hlft : LocallyOfFiniteType sY := hΘ.isPair.1.1.toLocallyOfFiniteType
  have hgen := V.isIrreducible.isGenericPoint_genericPoint V.isClosed
  have hcoh := coheight_genericPoint_eq_two sY hdim hV
  have hdim2 : ringKrullDim (Y.presheaf.stalk V.isIrreducible.genericPoint) = 2 := by
    rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight, hcoh]
    rfl
  obtain ⟨n, z, hz⟩ :=
    MMP.Mori.exists_isRegularSystemOfParameters (Y.presheaf.stalk V.isIrreducible.genericPoint)
  obtain rfl : n = 2 := by
    have h := hz.2
    rw [hdim2] at h
    exact_mod_cast h.symm
  have hxt : MMP.Mori.IsRegularSystemOfParameters ![z 0, z 1] := by
    convert hz using 1
    ext i
    fin_cases i <;> rfl
  obtain ⟨hfin, -, -, W, hW, -⟩ := MMP.Resolution.exists_addValuation_monomialValuation
    Y.functionField (isRegularSystemOfParameters_swap hxt) (le_refl 1)
  have hvalW : ∀ f : Y.presheaf.stalk V.isIrreducible.genericPoint, f ≠ 0 →
      ∃ M : ℕ, MMP.Resolution.monomialValuation (z 1) (z 0) 1 f = M ∧
        valuationOfAddValuation W (algebraMap _ Y.functionField f) =
          WithZero.exp (-(M : ℤ)) := by
    intro f hf
    obtain ⟨M, hM⟩ := ENat.ne_top_iff_exists.mp (hfin f hf)
    refine ⟨M, hM.symm, ?_⟩
    rw [valuationOfAddValuation_apply, hW, ← hM]
    rfl
  have hv : IsWeightedMonomialValuation sY V (z 0) (z 1) 1 (valuationOfAddValuation W) := by
    refine ⟨hΘ.isPair.1, ?_, inferInstance, hxt, le_rfl, hvalW⟩
    rw [MMP.Flips.codimension_eq_coheight_genericPoint]
    exact hcoh
  have hvc := hv.isNormalizedDivisorialValuation_and_isCentre.2
  choose f hf0 hf using fun P : MMP.Mori.PrimeDivisor Y =>
    exists_stalk_idealSheaf_eq_span (η := V.isIrreducible.genericPoint) P
  have hla := hv.hasLogDiscrepancy hΘ f (fun P _ => hf P)
  refine ⟨_, hvc, _, ?_, hla⟩
  -- the order of a local equation is a natural number, at least `1` along `S`
  have hM : ∀ P : MMP.Mori.PrimeDivisor Y,
      0 ≤ -WithZero.log (valuationOfAddValuation W (algebraMap _ Y.functionField (f P))) ∧
        (V.isIrreducible.genericPoint ∈ P.support →
          1 ≤ -WithZero.log (valuationOfAddValuation W (algebraMap _ Y.functionField (f P)))) := by
    intro P
    obtain ⟨M, hMv, hvM⟩ := hvalW (f P) (hf0 P)
    rw [hvM, WithZero.log_exp, neg_neg]
    refine ⟨Int.natCast_nonneg M, fun hP => ?_⟩
    obtain ⟨q, -, hq, -⟩ := MMP.Intersection.exists_stalk_idealSheaf_eq_of_mem_support P hP
    have hmem : f P ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk V.isIrreducible.genericPoint) := by
      have : f P ∈ q.asIdeal := by
        rw [← hq, hf P]
        exact Ideal.mem_span_singleton_self _
      exact IsLocalRing.le_maximalIdeal q.isPrime.ne_top this
    have h1 : (1 : ℕ∞) ≤ M := by
      rw [← hMv, monomialValuation_one_eq_iSup hxt]
      exact le_iSup₂_of_le (f := fun (n : ℕ) (_ : f P ∈
        IsLocalRing.maximalIdeal (Y.presheaf.stalk V.isIrreducible.genericPoint) ^ n) =>
          (n : ℕ∞)) 1 (by rwa [pow_one]) le_rfl
    exact_mod_cast h1
  have hle : (Θ.coeff S : ℝ) ≤ ∑ P ∈ Θ.support, (Θ.coeff P : ℝ) *
      ((-WithZero.log (valuationOfAddValuation W (algebraMap _ Y.functionField (f P))) : ℤ) :
        ℝ) := by
    refine le_trans ?_ (Finset.single_le_sum (f := fun P => (Θ.coeff P : ℝ) *
      ((-WithZero.log (valuationOfAddValuation W (algebraMap _ Y.functionField (f P))) : ℤ) : ℝ))
      (fun P _ => mul_nonneg (by exact_mod_cast hΘ.nonneg P) (by exact_mod_cast (hM P).1))
      (Finsupp.mem_support_iff.mpr hb.ne'))
    exact le_mul_of_one_le_right (by exact_mod_cast hΘ.nonneg S)
      (by exact_mod_cast (hM S).2 (hVS hgen.mem))
  have hbR : (0 : ℝ) < (Θ.coeff S : ℝ) := by exact_mod_cast hb
  rw [Nat.cast_one]
  linarith

/-! ### Branch numbers at a regular point of a prime divisor -/

/-- **Branch number one at a regular point.** Let `S` be a prime divisor of a fourfold `Y` and
`V ⊆ S` an irreducible closed surface at whose generic point `S` is regular. Then exactly one
prime divisor of the normalization `S^ν` maps onto `V`: `r_V = 1`. -/
private theorem branchNumber_eq_one {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)}
    [AlgebraicGeometry.IsVariety ℂ sY] (hdim : topologicalKrullDim Y = 4)
    (S : MMP.Mori.PrimeDivisor Y)
    {V : IrreducibleCloseds Y} (hV : topologicalKrullDim (V : Set Y) = 2)
    (hVS : (V : Set Y) ⊆ S.support)
    (hreg : V.isIrreducible.genericPoint ∉
      S.idealSheaf.subschemeι '' singularLocus S.idealSheaf.subscheme) :
    branchNumber S V = 1 := by
  classical
  haveI : IsIntegral Y := (inferInstance : AlgebraicGeometry.IsVariety ℂ sY).toIsIntegral
  haveI := S.integral
  haveI hvarS : AlgebraicGeometry.IsVariety ℂ (S.idealSheaf.subschemeι ≫ sY) :=
    (MMP.Mori.isVariety_iff ℂ _).mpr ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  obtain ⟨⟨-, -, hfinν, hsurj, -⟩, ⟨U, hU, hiso⟩, -⟩ :=
    MMP.Threefold.normalization_spec (S.idealSheaf.subschemeι ≫ sY)
  set ν := S.idealSheaf.subscheme.normalization
    (MMP.finite_irreducibleComponents_of_isIntegral
      S.idealSheaf.subscheme) with hν
  set ι := S.idealSheaf.subschemeι with hι
  have hgen := V.isIrreducible.isGenericPoint_genericPoint V.isClosed
  -- the point `s` of `S` over `η_V`
  obtain ⟨s, hs⟩ : V.isIrreducible.genericPoint ∈ Set.range ι := by
    rw [hι, Scheme.IdealSheafData.range_subschemeι]
    exact hVS hgen.mem
  have hsreg : IsRegularLocalRing (S.idealSheaf.subscheme.presheaf.stalk s) := by
    by_contra h
    exact hreg ⟨s, h, hs⟩
  have hsU : s ∈ U := by
    rw [← SetLike.mem_coe, hU]
    haveI := IsRegularLocalRing.isDomain (S.idealSheaf.subscheme.presheaf.stalk s)
    haveI := IsRegularLocalRing.uniqueFactorizationMonoid
      (S.idealSheaf.subscheme.presheaf.stalk s)
    exact (inferInstance : IsIntegrallyClosed (S.idealSheaf.subscheme.presheaf.stalk s))
  -- `S` is a threefold and `closure {s}` a surface, so `s` has coheight one in `S`
  have hdimS : topologicalKrullDim S.idealSheaf.subscheme = 3 := by
    have hdP := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY S.genericPoint
    rw [← AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      AlgebraicGeometry.PrimeDivisor.coheight_genericPoint, hdim] at hdP
    let e := ι.isClosedEmbedding.isEmbedding.toHomeomorph
    let e' := e.trans (Homeomorph.setCongr (Scheme.IdealSheafData.range_subschemeι S.idealSheaf))
    exact (IsHomeomorph.topologicalKrullDim_eq e' e'.isHomeomorph).trans
      (eq_of_add_one_eq (n := 3) hdP)
  have hdimCs : topologicalKrullDim (closure ({s} : Set S.idealSheaf.subscheme)) = 2 := by
    rw [← hV]
    have hemb : Topology.IsEmbedding
        (fun p : closure ({s} : Set S.idealSheaf.subscheme) => ι p.1) :=
      ι.isClosedEmbedding.isEmbedding.comp Topology.IsEmbedding.subtypeVal
    have hrange : Set.range (fun p : closure ({s} : Set S.idealSheaf.subscheme) => ι p.1) =
        (V : Set Y) := by
      rw [show (fun p : closure ({s} : Set S.idealSheaf.subscheme) => ι p.1) = ι ∘ Subtype.val
        from rfl, Set.range_comp, Subtype.range_coe,
        ← ι.isClosedEmbedding.closure_image_eq, Set.image_singleton, hs, hgen.def]
    exact IsHomeomorph.topologicalKrullDim_eq _
      (hemb.toHomeomorph.trans (Homeomorph.setCongr hrange)).isHomeomorph
  have hcohs : Order.coheight s = 1 := by
    have hdS := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight
      (S.idealSheaf.subschemeι ≫ sY) s
    rw [hdimS, hdimCs] at hdS
    exact eq_of_natCast_add_eq (a := 2) (n := 1) hdS
  -- over `U` the normalization is an isomorphism
  haveI := hsurj
  haveI := hiso
  haveI := hfinν
  obtain ⟨z₀, hz₀⟩ := ν.surjective s
  have hcomm : ∀ p, U.ι ((ν ∣_ U) p) = ν ((ν ⁻¹ᵁ U).ι p) := fun p => by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
  have hlift : ∀ z, ν z = s → ∃ p, (ν ⁻¹ᵁ U).ι p = z := fun z hz => by
    have : z ∈ Set.range (ν ⁻¹ᵁ U).ι := by
      rw [Scheme.Opens.range_ι]
      show ν z ∈ U
      rw [hz]
      exact hsU
    exact this
  obtain ⟨p₀, hp₀⟩ := hlift z₀ hz₀
  have huniq : ∀ z, ν z = s → z = z₀ := by
    intro z hz
    obtain ⟨p, hp⟩ := hlift z hz
    have h1 : U.ι ((ν ∣_ U) p) = U.ι ((ν ∣_ U) p₀) := by rw [hcomm, hcomm, hp, hp₀, hz, hz₀]
    have h2 := (ν ∣_ U).isOpenEmbedding.injective (U.ι.isOpenEmbedding.injective h1)
    rw [← hp, ← hp₀, h2]
  have hcoh0 : Order.coheight z₀ = 1 := by
    calc Order.coheight z₀ = Order.coheight ((ν ⁻¹ᵁ U).ι p₀) := by rw [hp₀]
      _ = Order.coheight p₀ := coheight_eq_of_isOpenImmersion _
      _ = Order.coheight ((ν ∣_ U) p₀) := (coheight_eq_of_isOpenImmersion _).symm
      _ = Order.coheight (U.ι ((ν ∣_ U) p₀)) := (coheight_eq_of_isOpenImmersion _).symm
      _ = Order.coheight s := by rw [hcomm, hp₀, hz₀]
      _ = 1 := hcohs
  -- the images of prime divisors of `S^ν`
  have hfun : ⇑(ν ≫ ι) = ⇑ι ∘ ⇑ν := funext fun _ => rfl
  have hcl : IsClosedMap (ν ≫ ι) := by
    rw [hfun]
    exact ι.isClosedEmbedding.isClosedMap.comp ν.isClosedMap
  have himg : ∀ Q : MMP.Mori.PrimeDivisor (S.idealSheaf.subscheme.normalizationScheme
      (MMP.finite_irreducibleComponents_of_isIntegral
        S.idealSheaf.subscheme)),
      (ν ≫ ι) '' Q.support = closure {ι (ν Q.genericPoint)} := by
    intro Q
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      ← hcl.closure_image_eq_of_continuous (ν ≫ ι).continuous, Set.image_singleton]
    rfl
  have hset : {Q : MMP.Mori.PrimeDivisor (S.idealSheaf.subscheme.normalizationScheme
      (MMP.finite_irreducibleComponents_of_isIntegral
        S.idealSheaf.subscheme)) | (ν ≫ ι) '' Q.support = (V : Set Y)} =
        {AlgebraicGeometry.PrimeDivisor.ofCoheightOne z₀ hcoh0} := by
    ext Q
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    rw [himg]
    constructor
    · intro hQ
      have hQη : ι (ν Q.genericPoint) = V.isIrreducible.genericPoint :=
        (inseparable_iff_closure_eq.mpr (hQ.trans hgen.def.symm)).eq
      apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      rw [AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
      exact huniq _ (ι.isClosedEmbedding.injective (hQη.trans hs.symm))
    · rintro rfl
      have hg0 : MMP.Mori.PrimeDivisor.genericPoint
          (AlgebraicGeometry.PrimeDivisor.ofCoheightOne z₀ hcoh0) = z₀ :=
        AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
      rw [hg0, hz₀, hs, hgen.def]
  change {Q : MMP.Mori.PrimeDivisor (S.idealSheaf.subscheme.normalizationScheme
      (MMP.finite_irreducibleComponents_of_isIntegral
        S.idealSheaf.subscheme)) | (ν ≫ ι) '' Q.support = (V : Set Y)}.ncard = 1
  rw [hset, Set.ncard_singleton]

/-! ### Sums and defaults -/

/-- A sum over `t` is the sum over `s` along an injection `g : s → t` whose image contains the
support of the summand on `t`. -/
private theorem finsum_mem_eq_finsum_mem_comp {α ι M : Type*} [AddCommMonoid M] {f : α → M}
    {g : ι → α} {s : Set ι} {t : Set α} (hg : Set.InjOn g s) (hst : g '' s ⊆ t)
    (hts : t ∩ Function.support f ⊆ g '' s) :
    ∑ᶠ a ∈ t, f a = ∑ᶠ i ∈ s, f (g i) := by
  rw [← finsum_mem_image hg, ← finsum_mem_inter_support, ← finsum_mem_inter_support (s := g '' s),
    (Set.subset_inter hts Set.inter_subset_right).antisymm
      (Set.inter_subset_inter_left _ hst)]

/-- The default echo weight of coefficient zero vanishes: `d(0) = ∑_{j ≥ 1} w(1 - j) = 0`. -/
private theorem defaultWeight_zero (N : ℕ) : defaultWeight N 0 = 0 :=
  finsum_eq_zero_of_forall_eq_zero fun j => by
    rw [finsum_eq_if]
    split_ifs with hj
    · exact difficultyWeight_of_nonpos (by rw [sub_zero, mul_one, sub_nonpos]; exact_mod_cast hj)
    · rfl

/-- A prime divisor `P` contributes `r_{V,P} d(b) = 0` to a bracket at `V` unless `V ⊆ P` and
`b ≠ 0`: the branch number vanishes off `P`, and `d(0) = 0`. -/
private theorem branchNumber_mul_defaultWeight_eq_zero {Y : Scheme.{0}} (N : ℕ)
    {P : MMP.Mori.PrimeDivisor Y} {V : Set Y} {b : ℚ} (h : V ⊆ P.support → b = 0) :
    branchNumber P V * defaultWeight N b = 0 := by
  by_cases hVP : V ⊆ P.support
  · rw [h hVP, Rat.cast_zero, defaultWeight_zero, mul_zero]
  · rw [branchNumber_eq_zero_of_not_subset hVP, zero_mul]

/-! ### Weights of valuations along a surface -/

/-- **Weights along a surface.** On a model `(Y, Θ)` of a terminal chain, the valuations with
centre an irreducible surface `V` carry weights `w_v`, with `w_v = w(2 - a)` for the log
discrepancy `a` of `v`; in particular `w_v ≠ 0` only if `a(v; Y, Θ) < 2`. -/
private theorem exists_valuationWeight {T : StabilizedSmallKltTail} {C : TerminalChain T}
    {x : C.ModelIndex} (hpair : MMP.Fourfold.IsPair (C.modelStructure x) (C.modelBoundary x))
    (hdim : topologicalKrullDim (C.model x) = 4) (N : ℕ) {V : IrreducibleCloseds (C.model x)}
    (hV : topologicalKrullDim (V : Set (C.model x)) = 2) :
    ∃ w : Valuation (C.model x).functionField (WithZero (Multiplicative ℤ)) → ℕ,
      (∀ v, MMP.Intersection.IsCentre ℂ (C.modelStructure x) v V →
        C.IsValuationWeight N x v (w v)) ∧
      (∀ v, MMP.Intersection.IsCentre ℂ (C.modelStructure x) v V →
        ∀ a, HasLogDiscrepancy (C.modelStructure x) (C.modelBoundary x) v a →
          w v = difficultyWeight N (2 - a)) ∧
      (∀ v, MMP.Intersection.IsCentre ℂ (C.modelStructure x) v V → w v ≠ 0 →
        ∃ a < 2, HasLogDiscrepancy (C.modelStructure x) (C.modelBoundary x) v a) := by
  classical
  have hlft : LocallyOfFiniteType (C.modelStructure x) := hpair.isPair.1.1.toLocallyOfFiniteType
  have hlog : ∀ v, MMP.Intersection.IsCentre ℂ (C.modelStructure x) v V →
      ∃ a, IsValuationLogDiscrepancy (C.modelStructure x) (C.modelBoundary x) v a := by
    rintro v ⟨D, hDp, rfl, -⟩
    obtain ⟨n, K, hK, -⟩ := hpair.isPair.2
    obtain ⟨b, hb⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hpair.isPair hK D
    exact ⟨_, n, D, hDp, rfl,
      MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hb hDp⟩
  let w : Valuation (C.model x).functionField (WithZero (Multiplicative ℤ)) → ℕ := fun v =>
    if h : ∃ a, IsValuationLogDiscrepancy (C.modelStructure x) (C.modelBoundary x) v a then
      difficultyWeight N (2 - h.choose) else 0
  have hw : ∀ v, MMP.Intersection.IsCentre ℂ (C.modelStructure x) v V →
      C.IsValuationWeight N x v (w v) := by
    intro v hv
    refine ⟨?_, (hlog v hv).choose, (hlog v hv).choose_spec, dif_pos (hlog v hv)⟩
    obtain ⟨D, hD, rfl, hVD⟩ := hv
    refine ⟨D, hD, rfl, ?_⟩
    rw [← hVD, MMP.Flips.codimension_eq_coheight_genericPoint,
      coheight_genericPoint_eq_two (C.modelStructure x) hdim hV]
  refine ⟨w, hw, fun v hv a ha => ?_, fun v hv hne => ?_⟩
  · obtain ⟨-, a', ⟨n', D', -, hD'v, hD'⟩, h⟩ := hw v hv
    obtain ⟨n, D, hDv, hD⟩ := ha
    rw [h, MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq_of_isPair hpair.isPair hD'
      hD (hD'v.trans hDv.symm)]
  · obtain ⟨-, a, ⟨n, D, -, hDv, hD⟩, h⟩ := hw v hv
    exact ⟨a, lt_of_not_ge fun h2 =>
      hne (h.trans (difficultyWeight_of_nonpos (sub_nonpos.mpr h2))), n, D, hDv, hD⟩

/-- **The weights along a surface of echoes are the default.** Let `(Y, Θ)` be a pair on a
normal fourfold with all coefficients `< 1`, and `V ⊆ S` an irreducible surface in a component
`S` of `Θ`, with `η_V` in the one-label smooth locus of `Supp Θ`. If every valuation with centre
`V` and log discrepancy `a < 2` is an echo `ξ_j` of a component of `Θ` through `V`, then the
weights `w_v = w(2 - a(v))` of the valuations with centre `V` sum to the default echo weight
`d(Θ(S)) = ∑_{j ≥ 1} w(1 - j (1 - Θ(S)))`. -/
private theorem finsum_isCentre_eq_defaultWeight {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {Θ : MMP.Mori.QDivisor Y}
    (hpair : MMP.Fourfold.IsPair sY Θ) (hdim : topologicalKrullDim Y = 4)
    (hlt : ∀ P ∈ Θ.support, Θ.coeff P < 1) {V : IrreducibleCloseds Y}
    (hV : topologicalKrullDim (V : Set Y) = 2) {S : MMP.Mori.PrimeDivisor Y}
    (hS : S ∈ Θ.support) (hVS : (V : Set Y) ⊆ S.support)
    (hη : V.isIrreducible.genericPoint ∈ oneLabelSmoothLocus Θ.support)
    (hecho : ∀ ξ, MMP.Intersection.IsCentre ℂ sY ξ V → ∀ a < 2, HasLogDiscrepancy sY Θ ξ a →
      ∃ (P : MMP.Mori.PrimeDivisor Y) (j : ℕ), IsSurfaceEcho sY Θ.support P V j ξ ∧
        a = 1 + j * (1 - (Θ.coeff P : ℝ)))
    {N : ℕ} {w : Valuation Y.functionField (WithZero (Multiplicative ℤ)) → ℕ}
    (hwv : ∀ v, MMP.Intersection.IsCentre ℂ sY v V → ∀ a, HasLogDiscrepancy sY Θ v a →
      w v = difficultyWeight N (2 - a))
    (hwpos : ∀ v, MMP.Intersection.IsCentre ℂ sY v V → w v ≠ 0 →
      ∃ a < 2, HasLogDiscrepancy sY Θ v a) :
    ∑ᶠ v ∈ {v | MMP.Intersection.IsCentre ℂ sY v V}, w v = defaultWeight N (Θ.coeff S) := by
  classical
  have hb1 : ((Θ.coeff S : ℚ) : ℝ) < 1 := by exact_mod_cast hlt S hS
  have hex := fun j (hj : 1 ≤ j) => exists_isSurfaceEcho hpair.isPair.1 hdim hS hVS hV hη hj
  -- `g j` is the echo `ξ_j`, for `j ≥ 1`
  obtain ⟨g, hg⟩ : ∃ g : ℕ → Valuation Y.functionField (WithZero (Multiplicative ℤ)),
      ∀ j, 1 ≤ j → IsSurfaceEcho sY Θ.support S V j (g j) :=
    ⟨fun j => if hj : 1 ≤ j then (hex j hj).choose else 1, fun j hj => by
      simpa only [dif_pos hj] using (hex j hj).choose_spec⟩
  have hgc : ∀ j, 1 ≤ j → MMP.Intersection.IsCentre ℂ sY (g j) V := fun j hj =>
    (hg j hj).2.2.2.2.2.2.2.1
  have hga : ∀ j, 1 ≤ j → HasLogDiscrepancy sY Θ (g j) (1 + j * (1 - (Θ.coeff S : ℝ))) :=
    fun j hj => (hg j hj).hasLogDiscrepancy hpair subset_rfl hlt
  rw [finsum_mem_eq_finsum_mem_comp (g := g) (s := {j | 1 ≤ j})]
  · refine finsum_congr fun j => finsum_congr fun hj => ?_
    rw [hwv _ (hgc j hj) _ (hga j hj)]
    congr 1
    ring
  · -- distinct echoes have distinct log discrepancies
    intro j hj j' hj' hjj
    obtain ⟨n, D, hDv, hD⟩ := hga j hj
    obtain ⟨n', D', hD'v, hD'⟩ := hga j' hj'
    have h := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq_of_isPair
      hpair.isPair hD hD' (hDv.trans (hjj.trans hD'v.symm))
    exact_mod_cast mul_right_cancel₀ (sub_pos.mpr hb1).ne' (by linarith : (j : ℝ) * _ = j' * _)
  · rintro _ ⟨j, hj, rfl⟩
    exact hgc j hj
  · rintro v ⟨hv, hwv0⟩
    obtain ⟨a, ha2, hla⟩ := hwpos v hv hwv0
    obtain ⟨P, j, hPj, -⟩ := hecho v hv a ha2 hla
    obtain ⟨-, -, hPL, hVP, -, -, hj, -⟩ := id hPj
    have hηV := (V.isIrreducible.isGenericPoint_genericPoint V.isClosed).mem
    obtain rfl := eq_of_mem_oneLabelSmoothLocus hη hPL hS (hVP hηV) (hVS hηV)
    exact ⟨j, hj, (hg j hj).eq hPj⟩

/-! ### Centres of labels -/

/-- On every model of a terminal chain, every label has exactly one centre, and distinct labels
have distinct centres: the centre relation is the graph of an injection. -/
private theorem exists_equiv_isLabelCentre_iff {T : StabilizedSmallKltTail}
    (C : TerminalChain T) (x : C.ModelIndex) :
    ∃ e : MMP.Mori.PrimeDivisor (C.junction 0).Y ≃ MMP.Mori.PrimeDivisor (C.model x),
      ∀ (S : C.Label) (P : MMP.Mori.PrimeDivisor (C.model x)),
        C.IsLabelCentre S x P ↔ e S.1 = P := by
  have he := TerminalChain.isPrimeDivisorCentre_iff_primeDivisorEquivModel_eq C x
  rcases x with ⟨i, _ | k⟩ <;> exact ⟨_, fun S P => he S.1 P⟩

/-! ### Brackets off a finite set of surfaces -/

end MMP.OAI4C2BracketsCofinite

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Fourfold.StabilizedSmallKltTail.PreparedChain

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral in
open MMP.OAI4C2BracketsCofinite MMP.Fourfold MMP.Mori in
/-- On a model `(Y, Θ)` of a prepared chain, the bracket `β_V(Y, Θ)`
(`MMP.Fourfold.StabilizedSmallKltTail.PreparedChain.IsSurfaceBracket`) is `0` at every
irreducible surface `V ⊆ Y` outside a finite set. -/
@[mmp "lem_oai4_c2_brackets_cofinite"]
public theorem finite_setOf_not_isSurfaceBracket_zero {T : StabilizedSmallKltTail}
    (Q : PreparedChain T) (x : Q.ModelIndex) :
    {V : IrreducibleCloseds (Q.chain.model x.1) |
      topologicalKrullDim (V : Set (Q.chain.model x.1)) = 2 ∧
        ¬ Q.IsSurfaceBracket x V 0}.Finite := by
  classical
  obtain ⟨hproj, hQf, hdim, hΘ, -, hlab, hIco⟩ :=
    PreparedChain.isKltTerminalPair_modelBoundary Q x
  set Y := Q.chain.model x.1
  set Θ := Q.chain.modelBoundary x.1
  have hpair := hΘ.1.1
  obtain ⟨𝒮, -, h𝒮⟩ := hΘ.exists_finset_forall_isSurfaceEcho hproj hQf hdim
    (L := Θ.support) subset_rfl
  refine 𝒮.finite_toSet.subset fun V ⟨hV, hne⟩ => by_contra fun hV𝒮 => hne ?_
  -- the centres `c S` of the labels: every label has one, and distinct labels have distinct ones
  obtain ⟨e, he⟩ := exists_equiv_isLabelCentre_iff Q.chain x.1
  set c : Q.chain.Label → MMP.Mori.PrimeDivisor Y := fun S => e S.1
  have hcc : ∀ S, Q.chain.IsLabelCentre S x.1 (c S) := fun S => (he S _).2 rfl
  have hlabel : ∀ P ∈ Θ.support, ∃ S, c S = P := fun P hP => by
    obtain ⟨S, hS⟩ := hlab P (Finsupp.mem_support_iff.mp hP)
    exact ⟨S, (he S P).1 hS⟩
  have hlt : ∀ P ∈ Θ.support, Θ.coeff P < 1 := fun P hP => by
    obtain ⟨S, hS⟩ := hlab P (Finsupp.mem_support_iff.mp hP)
    exact (hIco S _ (TerminalChain.isLabelCoefficient_of_isLabelCentre hS)).2
  have h𝒮V := h𝒮 V hV (mt Finset.mem_coe.mpr hV𝒮)
  obtain ⟨w, hw, hwv, hwpos⟩ := exists_valuationWeight hpair hdim Q.scale hV
  refine ⟨w, fun S => branchNumber (c S) (V : Set Y),
    fun S => defaultWeight Q.scale (Θ.coeff (c S)), hw,
    fun S => Or.inl ⟨c S, hcc S, rfl⟩, fun S => ⟨_, Or.inl ⟨c S, hcc S, rfl⟩, rfl⟩, ?_⟩
  rw [eq_comm, sub_eq_zero, Nat.cast_inj]
  change ∑ᶠ v ∈ {v | MMP.Intersection.IsCentre ℂ _ v V}, w v = _
  by_cases hcase : ∃ ξ, MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) ξ V ∧
    ∃ a < 2, HasLogDiscrepancy (Q.chain.modelStructure x.1) Θ ξ a
  · -- some valuation with centre `V` has `a < 2`: it is an echo of the unique label through `V`
    obtain ⟨ξ, hξc, a, ha2, hla⟩ := hcase
    obtain ⟨S₀, -, ⟨-, -, hS₀L, hVS₀, -, hη, -⟩, -⟩ := h𝒮V ξ hξc a ha2 hla
    obtain ⟨h₀, rfl⟩ := hlabel _ hS₀L
    haveI : AlgebraicGeometry.IsVariety ℂ (Q.chain.modelStructure x.1) := hpair.isPair.1.1
    have hηV := (V.isIrreducible.isGenericPoint_genericPoint V.isClosed).mem
    rw [finsum_isCentre_eq_defaultWeight hpair hdim hlt hV hS₀L hVS₀ hη h𝒮V hwv hwpos,
      finsum_eq_single (fun S => branchNumber (c S) (V : Set Y) *
        defaultWeight Q.scale (Θ.coeff (c S))) h₀ fun S hS =>
          branchNumber_mul_defaultWeight_eq_zero _ fun hVS =>
            by_contra fun hb => hS (Subtype.ext (e.injective (eq_of_mem_oneLabelSmoothLocus hη
              (Finsupp.mem_support_iff.mpr hb) hS₀L (hVS hηV) (hVS₀ hηV)))),
      branchNumber_eq_one (sY := Q.chain.modelStructure x.1) hdim (c h₀) hV hVS₀
        ((mem_oneLabelSmoothLocus_iff.mp hη).2.1 _ hS₀L), one_mul]
  · -- no valuation with centre `V` has `a < 2`: then every label through `V` has coefficient
    -- `0`, and all weights and defaults vanish
    push Not at hcase
    haveI := isRegularLocalRing_stalk_genericPoint hΘ hQf hdim hV
    rw [finsum_mem_eq_zero_of_forall_eq_zero
        (s := {v | MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v V})
        fun v hv => by_contra fun hne =>
          let ⟨a, ha, hla⟩ := hwpos v hv hne; hcase v hv a ha hla,
      finsum_eq_zero_of_forall_eq_zero fun S => branchNumber_mul_defaultWeight_eq_zero _
        fun hVS => by_contra fun hb =>
          let ⟨v, hvc, a, ha, hla⟩ := exists_isCentre_hasLogDiscrepancy_lt_two hpair
            hdim hV hVS (lt_of_le_of_ne (hpair.nonneg (c S)) (Ne.symm hb))
          hcase v hvc a ha hla]

end MMP.Fourfold.StabilizedSmallKltTail.PreparedChain
