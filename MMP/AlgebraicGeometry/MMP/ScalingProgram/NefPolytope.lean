module

public import MMP.AlgebraicGeometry.MMP.ScalingProgram.PolytopeFiniteRays
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.RelativeConeExtremalRays
public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas

section

/-!
# The nef region on a fixed model is a rational polytope

Let `f : X ⟶ Z` be a morphism of projective varieties over an algebraically closed field of
characteristic zero, with `X` normal and `ℚ`-factorial, `A` an `f`-ample `ℚ`-Cartier divisor and
`P` the convex hull of finitely many klt boundaries `B_j`. The `f`-nef region
`N = {B ∈ P | K_X + A + B is f-nef}` is cut out inside `P` by finitely many rational affine
inequalities, and it is the convex hull of finitely many `ℚ`-divisors.

Write `B = ∑ⱼ tⱼ Bⱼ` with `t` in the standard simplex. On a contracted curve `C` the intersection
number of `K_X + A + B` is `∑ⱼ tⱼ ((K_X + A + Bⱼ) · C)`, computed from the presentation
`K_X + A + B = ∑ⱼ (tⱼ / mⱼ) (mⱼ (K_X + A + Bⱼ))` by Cartier indices. Every class of the closed
relative cone `NE̅(X/Z)` is a sum of elements of extremal rays, so `K_X + A + B` is `f`-nef if and
only if it is nonnegative on every `(K_X + A + B)`-negative extremal ray; by the finiteness of
candidate rays these are among finitely many rays `ℝ_{≥0} ξ`, `ξ` in the curve lattice. Conversely
nonnegativity on contracted curves passes to the closure `NE̅(X/Z)` by continuity. On each `ξ` the
degree is the affine function `B ↦ (K_X + A) · ξ + ∑_E B(E) (E · ξ)`, whose coefficients are
rational because `ξ` has integral degrees against Cartier divisors.

For the second part, `N` is the image under `t ↦ ∑ⱼ tⱼ Bⱼ` of a bounded polyhedron of `ℝ^ι` with
rational data. Its extreme points are finitely many (each is determined by its set of tight
inequalities, whose normals span) and rational (the unique solution of a rational linear system),
so by Krein–Milman it is the convex hull of finitely many rational points.

## Main results

* `MMP.Fourfold.exists_finset_rationalAffine_nefRegion_eq_of_isKltPair`.

## Implementation notes

The source deduces rationality of the polytope by Fourier–Motzkin elimination of the weights
`tⱼ`; here the vertices of the polyhedron in the weights are shown to be rational instead, which
gives the convex-hull description directly. The source finds a negative extremal ray through a
strictly positive functional (relative Kleiman); here the decomposition of `NE̅(X/Z)` into extremal
rays, `MMP.Mori.exists_sum_mem_isExtremalRay_relativeClosedConeOfCurves`, is used instead.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 3.7 and 3.25
-/

open AlgebraicGeometry CategoryTheory MMP.Mori MMP.Fourfold

namespace MMP.FourfoldProofs.FourfoldFixedModelNefPolytopeProof

section Polyhedra

open Filter Topology

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The polyhedron `{t | ∀ i, ∑ⱼ aᵢⱼ tⱼ ≤ bᵢ}` in `ℝ^ι`. -/
private def polyhedron (a : κ → ι → ℝ) (b : κ → ℝ) : Set (ι → ℝ) :=
  {t | ∀ i, ∑ j, a i j * t j ≤ b i}

private theorem eq_zero_of_mem_extremePoints {a : κ → ι → ℝ} {b : κ → ℝ} {x : ι → ℝ}
    (hx : x ∈ (polyhedron a b).extremePoints ℝ) {y : ι → ℝ}
    (hy : ∀ i, ∑ j, a i j * x j = b i → ∑ j, a i j * y j = 0) : y = 0 := by
  have hev : ∀ s : ℝ, ∀ᶠ ε in 𝓝 (0 : ℝ), x + (s * ε) • y ∈ polyhedron a b := by
    intro s
    refine eventually_all.2 fun i => ?_
    have hlin : ∀ ε : ℝ, ∑ j, a i j * (x + (s * ε) • y) j =
        ∑ j, a i j * x j + (s * ε) * ∑ j, a i j * y j := by
      intro ε
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib,
        Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by ring
    by_cases hi : ∑ j, a i j * x j = b i
    · exact Eventually.of_forall fun ε => by rw [hlin, hy i hi, mul_zero, add_zero, hi]
    · have hlt : ∑ j, a i j * x j < b i := lt_of_le_of_ne (hx.1 i) hi
      have hc : Continuous fun ε : ℝ => ∑ j, a i j * x j + (s * ε) * ∑ j, a i j * y j := by
        fun_prop
      have := hc.continuousAt (x := 0) |>.eventually_lt continuousAt_const (by simpa using hlt)
      exact this.mono fun ε hε => (hlin ε).trans_le hε.le
  obtain ⟨ε, ⟨h1, h2⟩, hε⟩ := ((hev 1).and (hev (-1))).filter_mono nhdsWithin_le_nhds
    |>.and (self_mem_nhdsWithin (s := Set.Ioi (0 : ℝ)) (a := 0)) |>.exists
  have hseg : x ∈ openSegment ℝ (x + (1 * ε) • y) (x + (-1 * ε) • y) :=
    ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by
      ext j; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring⟩
  have := hx.2 h1 h2 hseg
  ext j
  have := congrFun this j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul, add_eq_left] at this
  simpa [hε.ne'] using this

private theorem finite_extremePoints (a : κ → ι → ℝ) (b : κ → ℝ) :
    ((polyhedron a b).extremePoints ℝ).Finite := by
  classical
  let τ : (ι → ℝ) → Finset κ := fun x => Finset.univ.filter fun i => ∑ j, a i j * x j = b i
  refine Set.Finite.of_finite_image (f := τ) (Set.toFinite _) fun x hx x' hx' hτ => ?_
  have h := eq_zero_of_mem_extremePoints hx (y := x - x') fun i hi => by
    have hi' : i ∈ τ x' := by
      rw [← show τ x = τ x' from hτ]; simpa [τ] using hi
    simp only [τ, Finset.mem_filter, Finset.mem_univ, true_and] at hi'
    simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, hi, hi', sub_self]
  exact sub_eq_zero.mp h

private theorem exists_rat_of_mem_extremePoints {a : κ → ι → ℚ} {b : κ → ℚ} {x : ι → ℝ}
    (hx : x ∈ (polyhedron (fun i j => (a i j : ℝ)) (fun i => (b i : ℝ))).extremePoints ℝ) :
    ∃ q : ι → ℚ, x = fun j => (q j : ℝ) := by
  classical
  let I : Set κ := {i | ∑ j, (a i j : ℝ) * x j = b i}
  let φ : (ι → ℚ) →ₗ[ℚ] (I → ℚ) :=
    { toFun := fun q i => ∑ j, a i j * q j
      map_add' := fun q q' => by ext i; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun c q => by
        ext i
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring }
  have hb : (fun i : I => b i) ∈ LinearMap.range φ := by
    by_contra hb
    obtain ⟨f, hf, hle⟩ := Submodule.exists_le_ker_of_notMem hb
    set μ : I → ℚ := fun i => f (Pi.single i 1) with hμ
    have hf' : ∀ v : I → ℚ, f v = ∑ i, μ i * v i := fun v => by
      conv_lhs => rw [show v = ∑ i, v i • Pi.single i 1 by
        ext i
        simp [Finset.sum_apply, Pi.single_apply]]
      simp [map_sum, map_smul, hμ, mul_comm]
    have hcol : ∀ j, ∑ i, μ i * a i j = 0 := fun j => by
      have := hle (LinearMap.mem_range_self φ (Pi.single j 1))
      rw [LinearMap.mem_ker, hf'] at this
      simpa [φ, Pi.single_apply] using this
    apply hf
    rw [hf']
    have : ((∑ i, μ i * b i : ℚ) : ℝ) = 0 := by
      push_cast
      calc ∑ i : I, (μ i : ℝ) * (b i : ℝ)
          = ∑ i : I, (μ i : ℝ) * ∑ j, (a i j : ℝ) * x j :=
            Finset.sum_congr rfl fun i _ => by rw [i.2]
        _ = ∑ j, (∑ i : I, (μ i : ℝ) * a i j) * x j := by
            simp only [Finset.mul_sum, Finset.sum_mul]
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
        _ = 0 := Finset.sum_eq_zero fun j _ => by
            rw [show (∑ i : I, (μ i : ℝ) * a i j) = ((∑ i : I, μ i * a i j : ℚ) : ℝ) by
              push_cast; rfl, hcol j]
            simp
    exact_mod_cast this
  obtain ⟨q, hq⟩ := hb
  refine ⟨q, sub_eq_zero.mp (eq_zero_of_mem_extremePoints hx fun i hi => ?_)⟩
  have hqi : ∑ j, (a i j : ℝ) * (q j : ℝ) = b i := by exact_mod_cast congrFun hq ⟨i, hi⟩
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, hi, hqi, sub_self]

private theorem exists_finset_polyhedron_eq_convexHull (a : κ → ι → ℚ) (b : κ → ℚ)
    (hT : Bornology.IsBounded (polyhedron (fun i j => (a i j : ℝ)) (fun i => (b i : ℝ)))) :
    ∃ W : Finset (ι → ℚ), polyhedron (fun i j => (a i j : ℝ)) (fun i => (b i : ℝ)) =
      convexHull ℝ ((fun w j => (w j : ℝ)) '' (W : Set (ι → ℚ))) := by
  classical
  set T := polyhedron (fun i j => (a i j : ℝ)) (fun i => (b i : ℝ)) with hTdef
  let c : (ι → ℚ) → (ι → ℝ) := fun w j => (w j : ℝ)
  have hc : Function.Injective c := fun w w' h => funext fun j => by
    simpa [c] using congrFun h j
  have hclosed : IsClosed T := by
    simp only [hTdef, polyhedron, Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_le (by fun_prop) continuous_const
  have hconv : Convex ℝ T := by
    simp only [hTdef, polyhedron, Set.setOf_forall]
    refine convex_iInter fun i => ?_
    exact convex_halfSpace_le (f := fun t : ι → ℝ => ∑ j, (a i j : ℝ) * t j)
      ⟨fun t t' => by simp [mul_add, Finset.sum_add_distrib],
        fun r t => by simp [Finset.mul_sum, mul_left_comm]⟩ _
  have hcomp : IsCompact T := Metric.isCompact_of_isClosed_isBounded hclosed hT
  have hfin : (c ⁻¹' T.extremePoints ℝ).Finite :=
    (finite_extremePoints _ _).preimage hc.injOn
  refine ⟨hfin.toFinset, Set.Subset.antisymm ?_ ?_⟩
  · have hsub : T.extremePoints ℝ ⊆ c '' (hfin.toFinset : Set (ι → ℚ)) := fun x hx => by
      obtain ⟨q, rfl⟩ := exists_rat_of_mem_extremePoints hx
      exact ⟨q, by simpa using hx, rfl⟩
    calc T = closure (convexHull ℝ (T.extremePoints ℝ)) :=
          (closure_convexHull_extremePoints hcomp hconv).symm
      _ ⊆ _ := closure_minimal (convexHull_mono hsub) ?_
    exact ((Set.toFinite _).isCompact_convexHull (𝕜 := ℝ)).isClosed
  · refine convexHull_min ?_ hconv
    rintro _ ⟨q, hq, rfl⟩
    exact (show c q ∈ T.extremePoints ℝ by simpa using hq).1

/-- The convex hull of finitely many points `vⱼ` is the image of the standard simplex under
`t ↦ ∑ⱼ tⱼ vⱼ`. -/
private theorem convexHull_range_eq_image_stdSimplex {E : Type*} [AddCommGroup E] [Module ℝ E]
    {ι : Type*} [Fintype ι] (v : ι → E) :
    convexHull ℝ (Set.range v) = Fintype.linearCombination ℝ v '' stdSimplex ℝ ι := by
  classical
  rw [← convexHull_rangle_single_eq_stdSimplex, LinearMap.image_convexHull, ← Set.range_comp]
  congr 2
  funext j
  simp [Fintype.linearCombination_apply_single]

/-- The standard simplex cut by finitely many inequalities is again a polyhedron. -/
private theorem polyhedron_sum_elim_eq {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (a : κ → ι → ℚ) (b : κ → ℚ) :
    polyhedron (fun i j => ((Sum.elim (fun l j => if l = j then (-1 : ℚ) else 0)
        (Sum.elim (fun (s : Bool) _ => if s then (1 : ℚ) else -1) a) i j : ℚ) : ℝ))
      (fun i => ((Sum.elim (fun _ => (0 : ℚ))
        (Sum.elim (fun s : Bool => if s then (1 : ℚ) else -1) b) i : ℚ) : ℝ)) =
      stdSimplex ℝ ι ∩ polyhedron (fun i j => (a i j : ℝ)) (fun i => (b i : ℝ)) := by
  ext t
  simp only [polyhedron, Set.mem_setOf_eq, Set.mem_inter_iff, stdSimplex, Sum.forall,
    Sum.elim_inl, Sum.elim_inr, Bool.forall_bool]
  simp only [apply_ite (fun q : ℚ => (q : ℝ)), Rat.cast_neg, Rat.cast_one, Rat.cast_zero,
    ite_mul, neg_one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, one_mul,
    Bool.false_eq_true, if_false, Finset.sum_neg_distrib, neg_le_neg_iff, neg_nonpos]
  constructor
  · rintro ⟨h0, ⟨h1, h2⟩, h3⟩
    exact ⟨⟨h0, le_antisymm h2 h1⟩, h3⟩
  · rintro ⟨⟨h0, h1⟩, h3⟩
    exact ⟨h0, ⟨h1.ge, h1.le⟩, h3⟩

private theorem coeff_linearCombination {X : Scheme} {ι : Type*} [Fintype ι] (B : ι → QDivisor X)
    (t : ι → ℝ) (E : MMP.Mori.PrimeDivisor X) :
    (Fintype.linearCombination ℝ (fun j => QDivisor.toRDivisor (B j)) t).coeff E =
      ∑ j, t j * ((B j).coeff E : ℝ) := by
  rw [Fintype.linearCombination_apply, DivisorWithCoeffs.coeff_apply, Finset.sum_apply']
  rfl

private theorem exists_finset_convexHull_eq_inter {X : Scheme} {ι : Type*} [Fintype ι]
    (B : ι → QDivisor X) (S : Finset ((MMP.Mori.PrimeDivisor X →₀ ℚ) × ℚ)) :
    ∃ V : Finset (QDivisor X),
      convexHull ℝ (Set.range fun j => QDivisor.toRDivisor (B j)) ∩
          {D | ∀ p ∈ S, 0 ≤ (p.1.sum fun E c => (c : ℝ) * D.coeff E) + (p.2 : ℝ)} =
        convexHull ℝ (QDivisor.toRDivisor '' (V : Set (QDivisor X))) := by
  classical
  set Φ : (ι → ℝ) →ₗ[ℝ] RDivisor X :=
    Fintype.linearCombination ℝ fun j => QDivisor.toRDivisor (B j)
  set α : S → ι → ℚ := fun p j => (p.1.1.sum fun E c => c * (B j).coeff E)
  have hℓ : ∀ (p : (MMP.Mori.PrimeDivisor X →₀ ℚ) × ℚ) (t : ι → ℝ),
      (p.1.sum fun E c => (c : ℝ) * (Φ t).coeff E) =
        ∑ j, ((p.1.sum fun E c => c * (B j).coeff E : ℚ) : ℝ) * t j := by
    intro p t
    simp only [Φ, coeff_linearCombination, Finsupp.sum, Rat.cast_sum, Rat.cast_mul, Finset.mul_sum,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  set a : S → ι → ℚ := fun p j => -α p j
  set b : S → ℚ := fun p => p.1.2
  have hT := polyhedron_sum_elim_eq a b
  set T := stdSimplex ℝ ι ∩ polyhedron (fun i j => (a i j : ℝ)) (fun i => (b i : ℝ))
  obtain ⟨W, hW⟩ := exists_finset_polyhedron_eq_convexHull _ _
    (show Bornology.IsBounded _ by
      rw [hT]
      exact (bounded_stdSimplex ι).subset Set.inter_subset_left)
  rw [hT] at hW
  refine ⟨W.image fun w => ∑ j, w j • B j, ?_⟩
  have hN : convexHull ℝ (Set.range fun j => QDivisor.toRDivisor (B j)) ∩
      {D | ∀ p ∈ S, 0 ≤ (p.1.sum fun E c => (c : ℝ) * D.coeff E) + (p.2 : ℝ)} = Φ '' T := by
    rw [convexHull_range_eq_image_stdSimplex]
    ext D
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, hD⟩
      refine ⟨t, ⟨ht, fun p => ?_⟩, rfl⟩
      have := hD p.1 p.2
      rw [hℓ] at this
      simp only [a, b, α, Rat.cast_neg, neg_mul, Finset.sum_neg_distrib, neg_le]
      linarith
    · rintro ⟨t, ⟨ht, htp⟩, rfl⟩
      refine ⟨⟨t, ht, rfl⟩, fun p hp => ?_⟩
      have := htp ⟨p, hp⟩
      rw [hℓ]
      simp only [a, b, α, Rat.cast_neg, neg_mul, Finset.sum_neg_distrib, neg_le] at this
      linarith
  rw [hN, hW, LinearMap.image_convexHull, ← Set.image_comp, Finset.coe_image, ← Set.image_comp]
  congr 1
  refine Set.image_congr fun w _ => ?_
  ext E
  change (Φ _).coeff E = (QDivisor.toRDivisor _).coeff E
  rw [coeff_linearCombination, QDivisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_apply,
    Finsupp.coe_finset_sum, Finset.sum_apply]
  simp [DivisorWithCoeffs.coeff_apply]

end Polyhedra

/-! ### Intersection numbers with contracted curves -/

section Curves

variable {k : Type} [Field k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)}

/-- Every Cartier divisor has an intersection number with every proper curve. -/
private theorem exists_isCartierIntersectionNumber [QuasiCompact sX] [IsLocallyNoetherian X]
    [IsNormal X] (C : ProperCurve sX) (L : Divisor X)
    (hL : L.IsCartier) : ∃ d, MMP.Flips.IsCartierIntersectionNumber k sX C L hL d := by
  let p := C.ι ≫ sX
  haveI : AlgebraicGeometry.IsCurve k p := C.isCurve
  have hX := finite_irreducibleComponents_of_locallyOfFiniteType k p
  haveI hvar : AlgebraicGeometry.IsVariety k (normalizationOverField k p ≫ p) :=
    isVariety_normalizationOverField k p
  haveI : IsIntegral (normalizationSchemeOverField k p) := hvar.toIsIntegral
  haveI : IsFinite (normalizationOverField k p) := isFinite_normalizationOverField k p
  have hν : MMP.Flips.IsCurveNormalization (normalizationOverField k p) :=
    { isIntegral := inferInstance
      isNormal := Scheme.isNormal_normalizationScheme C.scheme hX
      isFinite := inferInstance
      isBirationalMorphism := by
        haveI : Finite (irreducibleComponents (normalizationSchemeOverField k p)) := by
          rw [irreducibleComponents_eq_singleton]
          exact Set.finite_singleton _
        haveI : Finite (irreducibleComponents C.scheme) := by
          rw [irreducibleComponents_eq_singleton]
          exact Set.finite_singleton _
        obtain ⟨U, V, hUV, hU, hV, hiso⟩ := exists_dense_opens_isIso_resLE_of_isBirational
          (normalizationOverField k p) (Scheme.isBirational_normalization C.scheme hX)
          (Or.inl ⟨inferInstance, inferInstance⟩)
        exact MMP.Flips.isBirationalMorphism_of_isIso_resLE _ U V hU.nonempty hV.nonempty hUV
          hiso }
  exact ⟨_, _, _, hν, (topologicalKrullDim_normalizationSchemeOverField k p).le.trans C.dim_le,
    rfl⟩

end Curves

/-! ### Curve forms -/

section CurveForm

variable {k : Type} [Field k] {X : Scheme.{0}} (sX : X ⟶ Spec (.of k))
  [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [QuasiCompact sX]

/-- The curve form is additive in the divisor. -/
private theorem curveForm_add (D D' : QDivisor X) (hD : D.IsQCartier) (hD' : D'.IsQCartier)
    (hDD' : (D + D').IsQCartier) :
    QDivisor.curveForm sX (D + D') hDD' =
      QDivisor.curveForm sX D hD + QDivisor.curveForm sX D' hD' := by
  refine MMP.ProgramBaseChange.linearMap_ext_numericalClass_cycle sX fun C => ?_
  rw [LinearMap.add_apply, MMP.ProgramBaseChange.curveForm_numericalClass_cycle,
    MMP.ProgramBaseChange.curveForm_numericalClass_cycle,
    MMP.ProgramBaseChange.curveForm_numericalClass_cycle,
    QDivisor.intersectionNumber_add' k sX C.ι C.dim_le D D' hD hD' hDD']
  push_cast
  rfl

/-- The curve form is `ℚ`-homogeneous in the divisor. -/
private theorem curveForm_smul (q : ℚ) (D : QDivisor X) (hD : D.IsQCartier)
    (hqD : (q • D).IsQCartier) :
    QDivisor.curveForm sX (q • D) hqD = (q : ℝ) • QDivisor.curveForm sX D hD := by
  refine MMP.ProgramBaseChange.linearMap_ext_numericalClass_cycle sX fun C => ?_
  rw [LinearMap.smul_apply, MMP.ProgramBaseChange.curveForm_numericalClass_cycle,
    MMP.ProgramBaseChange.curveForm_numericalClass_cycle,
    QDivisor.intersectionNumber_smul k sX C.ι C.dim_le q D hD hqD]
  push_cast
  rfl

/-- On a class of the curve lattice the curve form of a `ℚ`-Cartier divisor is rational. -/
private theorem exists_rat_curveForm_eq (D : QDivisor X) (h : D.IsQCartier)
    {z : NumericalCurveClasses sX} (hz : z ∈ numericalCurveLattice sX) :
    ∃ q : ℚ, QDivisor.curveForm sX D h z = q := by
  have :=
    (Divisor.mem_cartierSubgroup.mp (D.cartierIndexSMul h).2).isInvertibleModule_divisorialSheaf
  obtain ⟨n, hn⟩ := hz ((D.cartierIndexSMul h : Divisor X).divisorialSheaf)
  refine ⟨1 / (D.cartierIndex h : ℚ) * n, ?_⟩
  rw [QDivisor.curveForm, QDivisor.associatedCartier, CartierDivisorWithCoeffs.ofCartier,
    Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.sum_single_index (by simp),
    LinearMap.smul_apply, hn, smul_eq_mul]
  push_cast
  rfl

end CurveForm

/-! ### A presentation by Cartier indices -/

section Presentation

variable {k : Type} [Field k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
  [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [QuasiCompact sX]
  {ι : Type*} [Fintype ι]

/-- For `ℚ`-Cartier divisors `Mⱼ` with Cartier indices `mⱼ` and real weights `tⱼ`, the presentation
`∑ⱼ tⱼ Mⱼ = ∑ⱼ (tⱼ / mⱼ) (mⱼ Mⱼ)` computes `(∑ⱼ tⱼ Mⱼ) · C = ∑ⱼ tⱼ (Mⱼ · C)` on every proper
curve `C`. -/
private theorem exists_presentation (M : ι → QDivisor X) (hM : ∀ j, (M j).IsQCartier)
    (t : ι → ℝ) :
    ∃ (n : ℕ) (r : Fin n → ℝ) (L : Fin n → Divisor X), (∀ i, (L i).IsCartier) ∧
      ∑ j, t j • QDivisor.toRDivisor (M j) = ∑ i, r i • Divisor.toRDivisor (L i) ∧
      ∀ C : ProperCurve sX, MMP.Flips.IsRIntersectionNumber k sX
        (∑ j, t j • QDivisor.toRDivisor (M j)) r L C
        (∑ j, t j *
          QDivisor.curveForm sX (M j) (hM j) (OneCycle.numericalClass sX (C.cycle ℝ))) := by
  classical
  set e := Fintype.equivFin ι
  set m : ι → ℕ := fun j => (M j).cartierIndex (hM j)
  have hm : ∀ j, (m j : ℝ) ≠ 0 := fun j => by
    exact_mod_cast (QDivisor.cartierIndex_pos (hM j)).ne'
  set L' : ι → Divisor X := fun j => ((M j).cartierIndexSMul (hM j) : Divisor X)
  have hL' : ∀ j, (L' j).IsCartier := fun j => ((M j).cartierIndexSMul (hM j)).2
  have hLM : ∀ j P, ((L' j).coeff P : ℝ) = m j * ((M j).coeff P : ℝ) := fun j P => by
    have := congrArg (fun G : QDivisor X => G.coeff P)
      (QDivisor.toQDivisor_cartierIndexSMul (M j) (hM j))
    simp only [Divisor.coeff_toQDivisor] at this
    rw [← Rat.cast_intCast, this]
    simp [DivisorWithCoeffs.coeff_apply, zsmul_eq_mul, m]
  have hdeg : ∀ (j) (C : ProperCurve sX), QDivisor.curveForm sX (M j) (hM j)
      (OneCycle.numericalClass sX (C.cycle ℝ)) =
        ((L' j).degreeOn k sX C.ι C.dim_le (hL' j) : ℝ) / m j := fun j C => by
    rw [MMP.ProgramBaseChange.curveForm_numericalClass_cycle,
      QDivisor.intersectionNumber_eq_of_toQDivisor_eq k sX C.ι C.dim_le (M j) (hM j) _ (hL' j)
        (QDivisor.toQDivisor_cartierIndexSMul (M j) (hM j))]
    push_cast
    rfl
  have heq : ∑ j, t j • QDivisor.toRDivisor (M j) =
      ∑ i, (t (e.symm i) / m (e.symm i)) • Divisor.toRDivisor (L' (e.symm i)) := by
    rw [e.symm.sum_comp (fun j => (t j / m j) • Divisor.toRDivisor (L' j))]
    refine Finset.sum_congr rfl fun j _ => ?_
    ext P
    simp only [DivisorWithCoeffs.coeff_smul, QDivisor.coeff_toRDivisor, Divisor.coeff_toRDivisor,
      smul_eq_mul, hLM]
    field_simp [hm j]
  refine ⟨Fintype.card ι, fun i => t (e.symm i) / m (e.symm i), fun i => L' (e.symm i),
    fun i => hL' _, heq, fun C => ?_⟩
  choose d hd using fun i => exists_isCartierIntersectionNumber C (L' (e.symm i)) (hL' _)
  refine ⟨fun i => hL' _, d, heq, hd, ?_⟩
  simp only [fun i => MMP.Fourfold.Oai4C1.Negativity.eq_degreeOn_of_isCartierIntersectionNumber
    (hd i)]
  rw [e.symm.sum_comp (fun j => t j / m j * ((L' j).degreeOn k sX C.ι C.dim_le (hL' j) : ℝ))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hdeg]
  ring

end Presentation

/-! ### Nefness through curve forms -/

section Nef

variable {k : Type} [Field k] {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
  [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [QuasiCompact sX]
  {ι : Type*} [Fintype ι]

/-- A real combination `∑ⱼ tⱼ Mⱼ` of `ℚ`-Cartier divisors is nef over `Y` if and only if
`∑ⱼ tⱼ (Mⱼ · C) ≥ 0` for every curve `C` contracted to a point of `Y`. -/
private theorem isRelativelyNef_sum_smul_iff (g : X ⟶ Y) (M : ι → QDivisor X)
    (hM : ∀ j, (M j).IsQCartier) (t : ι → ℝ) :
    MMP.Flips.IsRelativelyNef k sX g (∑ j, t j • QDivisor.toRDivisor (M j)) ↔
      ∀ C : ProperCurve sX, C.IsContractedBy g →
        0 ≤ ∑ j, t j * QDivisor.curveForm sX (M j) (hM j)
          (OneCycle.numericalClass sX (C.cycle ℝ)) := by
  obtain ⟨n, r, L, hL, hD, hx⟩ := exists_presentation (sX := sX) M hM t
  refine ⟨fun ⟨n', r', L', hL', hD', hnn⟩ C hC => ?_,
    fun h => ⟨n, r, L, hL, hD, fun C hC x hx' => ?_⟩⟩
  · choose d hd using fun i => exists_isCartierIntersectionNumber C (L' i) (hL' i)
    have hx' : MMP.Flips.IsRIntersectionNumber k sX _ r' L' C (∑ i, r' i * (d i : ℝ)) :=
      ⟨hL', d, hD', hd, rfl⟩
    rw [← (MMP.Flips.IsRIntersectionNumber.eq_and_linear k sX C).1 _ r' L' r L _ _ hx' (hx C)]
    exact hnn C hC _ hx'
  · rw [(MMP.Flips.IsRIntersectionNumber.eq_and_linear k sX C).1 _ r L r L _ _ hx' (hx C)]
    exact h C hC

end Nef

/-! ### The relative cone -/

section Relative

variable {k : Type} [Field k] {X Z : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {f : X ⟶ Z}

/-- The natural map `N₁(X/Z) → N₁(X)` on the class of a contracted curve. -/
private theorem relativeToAbsolute_relativeClass (C : ProperCurve sX) (hC : C.IsContractedBy f) :
    relativeToAbsolute sX f (C.relativeClass f hC) = OneCycle.numericalClass sX (C.cycle ℝ) :=
  rfl

/-- The degree form of an invertible sheaf on `N₁(X)`, pulled back to `N₁(X/Z)`, is its degree
form on `N₁(X/Z)`. -/
private theorem degree_relativeToAbsolute (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (z : RelativeNumericalCurveClasses sX f) :
    NumericalCurveClasses.degree sX L (relativeToAbsolute sX f z) =
      RelativeNumericalCurveClasses.degree sX f L z := by
  obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sX f z
  rfl

variable [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]

/-- The curve form of a `ℚ`-Cartier divisor is continuous on `N₁(X/Z)`. -/
private theorem continuous_curveForm_relativeToAbsolute (D : QDivisor X) (h : D.IsQCartier) :
    Continuous fun z : RelativeNumericalCurveClasses sX f =>
      QDivisor.curveForm sX D h (relativeToAbsolute sX f z) := by
  simp only [QDivisor.curveForm, Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul]
  apply continuous_finset_sum
  intro E _
  have := (Divisor.mem_cartierSubgroup.mp E.2).isInvertibleModule_divisorialSheaf
  simp only [degree_relativeToAbsolute]
  exact continuous_const.mul (RelativeNumericalCurveClasses.continuous_degree sX f _)

/-- **Testing nefness on finitely many rays.** Let `ψ` be a continuous linear form on `N₁(X/Z)`
and `S` a finite subset of `NE̅(X/Z)` containing a generator of every `ψ`-negative extremal ray.
Then `ψ` is nonnegative on every contracted curve if and only if it is nonnegative on `S`. -/
private theorem forall_relativeClass_nonneg_iff [IsAlgClosed k] [CharZero k]
    (sZ : Z ⟶ Spec (.of k)) [MMP.Mori.IsProjectiveVariety k sX]
    [MMP.Mori.IsProjectiveVariety k sZ]
    (hfs : f ≫ sZ = sX) (ψ : RelativeNumericalCurveClasses sX f →ₗ[ℝ] ℝ) (hψ : Continuous ψ)
    (S : Finset (RelativeNumericalCurveClasses sX f))
    (hS : ∀ ξ ∈ S, ξ ∈ relativeClosedConeOfCurves sX f)
    (hray : ∀ R : Set (RelativeNumericalCurveClasses sX f),
      IsExtremalRay ℝ (relativeClosedConeOfCurves sX f : Set _) R →
        (∀ u ∈ R, u ≠ 0 → ψ u < 0) → ∃ ξ ∈ S, R = {w | ∃ c : ℝ, 0 ≤ c ∧ c • ξ = w}) :
    (∀ (C : ProperCurve sX) (hC : C.IsContractedBy f), 0 ≤ ψ (C.relativeClass f hC)) ↔
      ∀ ξ ∈ S, 0 ≤ ψ ξ := by
  constructor
  · intro h ξ hξ
    have hcl : ξ ∈ closure (relativeConeOfCurves sX f : Set _) := by
      rw [← coe_relativeClosedConeOfCurves]
      exact hS ξ hξ
    refine closure_minimal (fun z hz => ?_) (isClosed_le continuous_const hψ) hcl
    change z ∈ PointedCone.hull ℝ _ at hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨C, hC⟩, rfl⟩ := hx
      exact h C hC
    | zero => simp
    | add x y _ _ hx hy => exact (add_nonneg hx hy).trans_eq (map_add ψ x y).symm
    | smul a x _ hx =>
      change 0 ≤ ψ (a • x)
      rw [LinearMap.map_smul_of_tower]
      change 0 ≤ (a : ℝ) * ψ x
      exact mul_nonneg a.2 hx
  · intro h C hC
    have hz : C.relativeClass f hC ∈ relativeClosedConeOfCurves sX f := by
      rw [← SetLike.mem_coe, coe_relativeClosedConeOfCurves]
      exact subset_closure (relativeClass_mem_relativeConeOfCurves hC)
    obtain ⟨s, R, w, hRw, hsum⟩ :=
      exists_sum_mem_isExtremalRay_relativeClosedConeOfCurves sX sZ f hfs hz
    rw [hsum, map_sum]
    refine Finset.sum_nonneg fun i _ => ?_
    by_contra hneg
    push Not at hneg
    obtain ⟨hext, v, hv0, hRv⟩ := (hRw i).1
    obtain ⟨c, hc, hcv⟩ : w i ∈ {w | ∃ c : ℝ, 0 ≤ c ∧ c • v = w} := hRv ▸ (hRw i).2
    have hψv : ψ v < 0 := neg_of_mul_neg_right (by rwa [← hcv, map_smul, smul_eq_mul] at hneg) hc
    have hneg' : ∀ u ∈ R i, u ≠ 0 → ψ u < 0 := by
      intro u hu hu0
      rw [hRv] at hu
      obtain ⟨c', hc', rfl⟩ := hu
      have hc'0 : c' ≠ 0 := by
        rintro rfl
        simp at hu0
      rw [map_smul, smul_eq_mul]
      exact mul_neg_of_pos_of_neg (hc'.lt_of_ne' hc'0) hψv
    obtain ⟨ξ, hξS, hRξ⟩ := hray (R i) (hRw i).1 hneg'
    obtain ⟨c'', hc'', hξw⟩ : w i ∈ {w | ∃ c : ℝ, 0 ≤ c ∧ c • ξ = w} := hRξ ▸ (hRw i).2
    rw [← hξw, map_smul, smul_eq_mul] at hneg
    exact absurd hneg (not_lt.mpr (mul_nonneg hc'' (h ξ hξS)))

end Relative

/-! ### The curve form along the boundary polytope -/

section Affine

variable {k : Type} [Field k] {X Z : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {f : X ⟶ Z}
  {ι : Type*} [Fintype ι]

/-- An additive, `ℚ`-homogeneous function of `ℚ`-divisors is determined by its values on prime
divisors. -/
private theorem apply_eq_sum_coeff_mul {v : QDivisor X → ℝ}
    (hadd : ∀ Q Q', v (Q + Q') = v Q + v Q') (hsmul : ∀ (c : ℚ) Q, v (c • Q) = c * v Q)
    {D : QDivisor X} {S : Finset (MMP.Mori.PrimeDivisor X)} (hS : D.support ⊆ S) :
    v D = ∑ E ∈ S, (D.coeff E : ℝ) * v (Finsupp.single E 1) := by
  have hdec : D = ∑ E ∈ S, D.coeff E • Finsupp.single E (1 : ℚ) := by
    conv_lhs => rw [← Finsupp.sum_single D]
    rw [Finsupp.sum_of_support_subset D hS _ (by simp)]
    refine Finset.sum_congr rfl fun E _ => ?_
    rw [Finsupp.smul_single_one]
    rfl
  change AddMonoidHom.mk' v hadd D = _
  conv_lhs => rw [hdec]
  rw [map_sum]
  exact Finset.sum_congr rfl fun E _ => hsmul _ _

/-- For weights summing to one, `K₀ + ∑ⱼ tⱼ Bⱼ = ∑ⱼ tⱼ (K₀ + Bⱼ)`. -/
private theorem toRDivisor_add_linearCombination (K0 : QDivisor X) (B : ι → QDivisor X)
    {t : ι → ℝ} (ht : ∑ j, t j = 1) :
    QDivisor.toRDivisor K0 + Fintype.linearCombination ℝ (fun j => QDivisor.toRDivisor (B j)) t =
      ∑ j, t j • QDivisor.toRDivisor (K0 + B j) := by
  ext P
  simp only [DivisorWithCoeffs.coeff_apply, Fintype.linearCombination_apply, Finsupp.coe_add,
    Finsupp.coe_finset_sum, Pi.add_apply, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul,
    map_add]
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, ht, one_mul]

variable [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [QuasiCompact sX]

/-- For weights `tⱼ` summing to one, `∑ⱼ tⱼ ((K₀ + Bⱼ) · z)` is the affine function of the
coefficients of `∑ⱼ tⱼ Bⱼ` whose coefficients are the values `ρ` of the curve forms at `z`. -/
private theorem sum_mul_curveForm_add_eq (hq : ∀ Q : QDivisor X, Q.IsQCartier)
    (z : NumericalCurveClasses sX) {ρ : QDivisor X → ℚ}
    (hρ : ∀ Q, QDivisor.curveForm sX Q (hq Q) z = ρ Q) (K0 : QDivisor X) (B : ι → QDivisor X)
    {S : Finset (MMP.Mori.PrimeDivisor X)} (hS : ∀ j, (B j).support ⊆ S) {t : ι → ℝ}
    (ht : ∑ j, t j = 1) {D : RDivisor X} (hD : ∀ E, D.coeff E = ∑ j, t j * ((B j).coeff E : ℝ)) :
    ∑ j, t j * QDivisor.curveForm sX (K0 + B j) (hq (K0 + B j)) z =
      ((∑ E ∈ S, Finsupp.single E (ρ (Finsupp.single E 1))).sum fun E c =>
        (c : ℝ) * D.coeff E) + (ρ K0 : ℝ) := by
  set v : QDivisor X → ℝ := fun Q => QDivisor.curveForm sX Q (hq Q) z
  have hadd : ∀ Q Q', v (Q + Q') = v Q + v Q' := fun Q Q' => by
    simp only [v, curveForm_add sX Q Q' (hq Q) (hq Q') (hq (Q + Q')), LinearMap.add_apply]
  have hsmul : ∀ (c : ℚ) Q, v (c • Q) = c * v Q := fun c Q => by
    simp only [v, curveForm_smul sX c Q (hq Q) (hq (c • Q)), LinearMap.smul_apply, smul_eq_mul]
  have hB : ∀ j, v (B j) = ∑ E ∈ S, ((B j).coeff E : ℝ) * v (Finsupp.single E 1) :=
    fun j => apply_eq_sum_coeff_mul hadd hsmul (hS j)
  have hρE : ∀ Q, ((ρ Q : ℚ) : ℝ) = v Q := fun Q => (hρ Q).symm
  have hsum1 : ((∑ E ∈ S, Finsupp.single E (ρ (Finsupp.single E 1))).sum fun E c =>
      (c : ℝ) * D.coeff E) = ∑ E ∈ S, (ρ (Finsupp.single E 1) : ℝ) * D.coeff E := by
    rw [← Finsupp.sum_finset_sum_index (fun _ => by simp) (fun _ _ _ => by push_cast; ring)]
    exact Finset.sum_congr rfl fun E _ => Finsupp.sum_single_index (by simp)
  change ∑ j, t j * v (K0 + B j) = _
  calc ∑ j, t j * v (K0 + B j)
      = ∑ j, t j * (v K0 + ∑ E ∈ S, ((B j).coeff E : ℝ) * v (Finsupp.single E 1)) := by
        simp only [hadd, hB]
    _ = (∑ j, t j) * v K0 +
          ∑ E ∈ S, v (Finsupp.single E 1) * ∑ j, t j * ((B j).coeff E : ℝ) := by
        simp only [mul_add, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
        congr 1
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    _ = _ := by
        rw [ht, one_mul, hsum1, add_comm]
        simp only [hρE, hD]

/-- Given finitely many classes `Sξ` of `NE̅(X/Z)` among which every extremal ray negative for
`∑ⱼ tⱼ Mⱼ` is spanned, `∑ⱼ tⱼ Mⱼ` is nef over `Z` if and only if it is nonnegative on `Sξ`. -/
private theorem isRelativelyNef_sum_smul_iff_forall_mem [IsAlgClosed k] [CharZero k]
    (sZ : Z ⟶ Spec (.of k)) [MMP.Mori.IsProjectiveVariety k sX]
    [MMP.Mori.IsProjectiveVariety k sZ] (hfs : f ≫ sZ = sX) (M : ι → QDivisor X)
    (hM : ∀ j, (M j).IsQCartier) (t : ι → ℝ) (Sξ : Finset (RelativeNumericalCurveClasses sX f))
    (hS : ∀ ξ ∈ Sξ, ξ ∈ relativeClosedConeOfCurves sX f)
    (hray : ∀ R : Set (RelativeNumericalCurveClasses sX f),
      IsExtremalRay ℝ (relativeClosedConeOfCurves sX f : Set _) R →
        (∀ u ∈ R, u ≠ 0 →
          ∑ j, t j * QDivisor.curveForm sX (M j) (hM j) (relativeToAbsolute sX f u) < 0) →
        ∃ ξ ∈ Sξ, R = {w | ∃ c : ℝ, 0 ≤ c ∧ c • ξ = w}) :
    MMP.Flips.IsRelativelyNef k sX f (∑ j, t j • QDivisor.toRDivisor (M j)) ↔
      ∀ ξ ∈ Sξ, 0 ≤ ∑ j, t j * QDivisor.curveForm sX (M j) (hM j) (relativeToAbsolute sX f ξ) := by
  set ψ : RelativeNumericalCurveClasses sX f →ₗ[ℝ] ℝ :=
    ∑ j, t j • (QDivisor.curveForm sX (M j) (hM j) ∘ₗ relativeToAbsolute sX f)
  have hψ : ∀ u, ψ u =
      ∑ j, t j * QDivisor.curveForm sX (M j) (hM j) (relativeToAbsolute sX f u) := fun u => by
    simp [ψ, LinearMap.sum_apply]
  have hψc : Continuous ψ := by
    rw [show (ψ : RelativeNumericalCurveClasses sX f → ℝ) = fun u => ∑ j,
      t j * QDivisor.curveForm sX (M j) (hM j) (relativeToAbsolute sX f u) from funext hψ]
    exact continuous_finset_sum _ fun j _ =>
      continuous_const.mul (continuous_curveForm_relativeToAbsolute _ _)
  have hcurves := forall_relativeClass_nonneg_iff sZ hfs ψ hψc Sξ hS fun R hR hneg =>
    hray R hR fun u hu hu0 => by simpa only [hψ] using hneg u hu hu0
  simp only [hψ, relativeToAbsolute_relativeClass] at hcurves
  rw [isRelativelyNef_sum_smul_iff f M hM t]
  exact hcurves

end Affine

end MMP.FourfoldProofs.FourfoldFixedModelNefPolytopeProof

end

section

/-!
# The nef region on a fixed model is a rational polytope

Let `f : X ⟶ Z` be a morphism of projective varieties over an algebraically closed field of
characteristic zero, with `X` normal and `ℚ`-factorial and canonical divisor `K`, let `A` be an
`f`-ample `ℚ`-Cartier `ℚ`-divisor, and let `B₁, …, B_s` be boundaries such that every `(X, Bⱼ)` is
klt. Inside the real convex hull `P` of the `Bⱼ`, taken in the real vector space of `ℝ`-divisors
(the coefficient space of the common support of the `Bⱼ`), the nef region
`N = {B ∈ P | K + A + B is f-nef}` is cut out by finitely many affine inequalities with rational
coefficients; consequently `N` is the convex hull of finitely many `ℚ`-divisors, a rational
polytope, possibly empty.

## Main results

* `MMP.Fourfold.exists_finset_rationalAffine_nefRegion_eq_of_isKltPair`: the statement above.

## Implementation notes

An affine inequality with rational coefficients is a pair `(c, d)` with `c` a finitely supported
`ℚ`-valued function on prime divisors and `d ∈ ℚ`, read as
`0 ≤ ∑_E c(E) · coeff_E(D) + d` for an `ℝ`-divisor `D`. Only the coefficients along the common
support of the `Bⱼ` matter on `P`, so no restriction is placed on the support of `c`. Points of `P`
are real `ℝ`-divisors, and relative nefness of the `ℝ`-Cartier divisor `K + A + D` is
`MMP.Flips.IsRelativelyNef`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 3.7 and 3.25
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori

open MMP.FourfoldProofs.FourfoldFixedModelNefPolytopeProof in
/-- **The nef region on a fixed model is a rational polytope.** Let `f : X ⟶ Z` be a morphism of
projective varieties over an algebraically closed field of characteristic zero, with `X` normal
and `ℚ`-factorial and canonical divisor `K`, let `A` be an `f`-ample `ℚ`-Cartier `ℚ`-divisor and
let `Bⱼ` (`j ∈ ι`, finitely many) be boundaries with every `(X, Bⱼ)` klt. Then there is a finite
set `S` of rational affine forms `(c, d)` such that a real divisor `D` in the convex hull of the
`Bⱼ` has `K + A + D` `f`-nef if and only if `0 ≤ ∑_E c(E) D(E) + d` for every `(c, d) ∈ S`; and
this nef region is the convex hull of a finite set of `ℚ`-divisors. -/
@[mmp "prop_fourfold_fixed_model_nef_polytope"]
public theorem exists_finset_rationalAffine_nefRegion_eq_of_isKltPair
    {k : Type} [Field k] {X Z : Scheme.{0}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k)) (f : X ⟶ Z)
    (hf : IsProjectiveSetting k sX sZ f) (hX : IsQFactorial sX)
    {K : Divisor X} (hK : ∃ n : ℕ, K.IsCanonicalDivisor sX n)
    {A : QDivisor X} (hA : A.IsQCartier) (hAf : A.HasRelativelyAmpleMultiple f)
    {ι : Type*} [Fintype ι] (B : ι → QDivisor X) (hB : ∀ j P, (B j).coeff P ≤ 1)
    (hklt : ∀ j, IsKltPair sX (B j)) :
    ∃ S : Finset ((MMP.Mori.PrimeDivisor X →₀ ℚ) × ℚ),
      {D ∈ convexHull ℝ (Set.range fun j => QDivisor.toRDivisor (B j)) |
          MMP.Flips.IsRelativelyNef k sX f (QDivisor.toRDivisor (Divisor.toQDivisor K + A) + D)} =
        convexHull ℝ (Set.range fun j => QDivisor.toRDivisor (B j)) ∩
          {D | ∀ p ∈ S, 0 ≤ (p.1.sum fun E c => (c : ℝ) * D.coeff E) + (p.2 : ℝ)} ∧
      ∃ V : Finset (QDivisor X),
        {D ∈ convexHull ℝ (Set.range fun j => QDivisor.toRDivisor (B j)) |
            MMP.Flips.IsRelativelyNef k sX f
              (QDivisor.toRDivisor (Divisor.toQDivisor K + A) + D)} =
          convexHull ℝ (QDivisor.toRDivisor '' (V : Set (QDivisor X))) := by
  classical
  haveI := hf.isAlgClosed
  haveI := hf.charZero
  haveI : MMP.Mori.IsProjectiveVariety k sX := hf.isProjectiveVariety_source
  haveI : MMP.Mori.IsProjectiveVariety k sZ := hf.isProjectiveVariety_target
  have hq : ∀ D : QDivisor X, D.IsQCartier := isQCartier_of_isQFactorial sX hX
  set K0 : QDivisor X := Divisor.toQDivisor K + A
  set M : ι → QDivisor X := fun j => Divisor.toQDivisor K + A + B j
  obtain ⟨Sξ, hSξ, hray⟩ :=
    exists_finset_isExtremalRay_of_isKltPair sX sZ f hf hX hK hA hAf B hB hklt
  have hrat : ∀ ξ ∈ Sξ, ∀ Q : QDivisor X, ∃ q : ℚ,
      QDivisor.curveForm sX Q (hq Q) (relativeToAbsolute sX f ξ) = q :=
    fun ξ hξ Q => exists_rat_curveForm_eq sX Q (hq Q) (hSξ ξ hξ).2.2.1
  choose! ρ hρ using hrat
  set Ssupp : Finset (MMP.Mori.PrimeDivisor X) := Finset.univ.biUnion fun j => (B j).support
  set pform : RelativeNumericalCurveClasses sX f → (MMP.Mori.PrimeDivisor X →₀ ℚ) × ℚ :=
    fun ξ => (∑ E ∈ Ssupp, Finsupp.single E (ρ ξ (Finsupp.single E 1)), ρ ξ K0)
  set Φ : (ι → ℝ) →ₗ[ℝ] RDivisor X :=
    Fintype.linearCombination ℝ fun j => QDivisor.toRDivisor (B j)
  have hval : ∀ ξ ∈ Sξ, ∀ t : ι → ℝ, ∑ j, t j = 1 →
      ∑ j, t j * QDivisor.curveForm sX (M j) (hq (M j)) (relativeToAbsolute sX f ξ) =
        ((pform ξ).1.sum fun E c => (c : ℝ) * (Φ t).coeff E) + ((pform ξ).2 : ℝ) :=
    fun ξ hξ t ht => sum_mul_curveForm_add_eq hq _ (hρ ξ hξ) K0 B (S := Ssupp)
      (fun j _ hE => Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hE⟩) ht
      (coeff_linearCombination B t)
  have hfirst : {D ∈ convexHull ℝ (Set.range fun j => QDivisor.toRDivisor (B j)) |
      MMP.Flips.IsRelativelyNef k sX f (QDivisor.toRDivisor (Divisor.toQDivisor K + A) + D)} =
        convexHull ℝ (Set.range fun j => QDivisor.toRDivisor (B j)) ∩
          {D | ∀ p ∈ Sξ.image pform,
            0 ≤ (p.1.sum fun E c => (c : ℝ) * D.coeff E) + (p.2 : ℝ)} := by
    ext D
    simp only [Set.mem_sep_iff, Set.mem_inter_iff, Set.mem_setOf_eq]
    refine and_congr_right fun hD => ?_
    rw [convexHull_range_eq_image_stdSimplex] at hD
    obtain ⟨t, ht, rfl⟩ := hD
    have hsum : QDivisor.toRDivisor K0 + Φ t = ∑ j, t j • QDivisor.toRDivisor (M j) :=
      toRDivisor_add_linearCombination K0 B ht.2
    rw [hsum, isRelativelyNef_sum_smul_iff_forall_mem sZ hf.comp_eq M (fun j => hq (M j)) t Sξ
      (fun ξ hξ => (hSξ ξ hξ).2.1) fun R hR hneg =>
        hray t ht.1 ht.2 R hR ⟨fun j => hq (M j), hneg⟩, Finset.forall_mem_image]
    exact forall₂_congr fun ξ hξ => by rw [hval ξ hξ t ht.2]
  exact ⟨_, hfirst, hfirst ▸ exists_finset_convexHull_eq_inter B _⟩

end MMP.Fourfold

end
