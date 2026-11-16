module

public import MMP.AlgebraicGeometry.Divisor.MeromorphicFunctionField
public import MMP.AlgebraicGeometry.MMP.Fourfold.Defs
import MMP.AlgebraicGeometry.Divisor.LinearSystem
import MMP.AlgebraicGeometry.Positivity.SerreAmpleCartier
import MMP.AlgebraicGeometry.MMP.Fourfold.AffineBaseRegularGeneration
import MMP.AlgebraicGeometry.MMP.Threefold.SurfaceLocalRings
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LargeModuleUniverse
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.AsymptoticRiemannRoch
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheafSections

/-!
# Concentrating an ample `ℚ`-Cartier divisor at a smooth point

Let `W` be an integral projective variety of dimension `d > 0` over an algebraically closed
field `k`, let `N` be an ample `ℚ`-Cartier divisor on `W` and let `x` be a smooth closed point of
`W`. If `N^d > d^d`, then there is an effective `ℚ`-Cartier divisor `G ∼_ℚ N` with
`mult_x G > d`.

The proof compares the growth of `h⁰(W, 𝒪_W(nE)) = (E^d)/d! ⬝ n^d + O(n^{d-1})`, for a Cartier
multiple `E = mN`, with the dimension `binom(nmd + d, d)` of the jet space
`𝒪_{W,x}/𝔪_x^{nmd+1}`: a section `σ` whose product with a local equation of `nE` at `x` lies in
`𝔪_x^{nmd+1}` gives the effective Cartier divisor `D = nE + div σ ∼ nE`, and `G = D/(nm)`.

## Main results

* `MMP.Mori.KCartierDivisor.exists_isEffective_linearlyEquivalent_mem_maximalIdeal_pow`: the
  concentration statement.

## Implementation notes

A `ℚ`-Cartier divisor is an element of `KCartierDivisor ℚ W`, a formal `ℚ`-linear
combination of Cartier divisors, and is ample when some positive multiple with integral
coefficients is a Cartier divisor with ample invertible sheaf
(`MMP.Fourfold.KCartierDivisor.IsRelativelyAmpleQ` over `Spec k`). No normality of `W` is needed.

An effective `ℚ`-Cartier divisor `G ∼_ℚ N` is written `G = D/q`, with `q > 0` such that `qN` has
integral coefficients and `D` an effective Cartier divisor linearly equivalent to the Cartier
divisor `qN`. The multiplicity of an effective Cartier divisor `D` at `x` is the order in
`𝒪_{W,x}` of a local equation `a` of `D` at `x`, so `mult_x G > d` reads `a ∈ 𝔪_x^{qd+1}`.

The self-intersection `N^d` is read through a Cartier multiple: for `m > 0` with `mN` integral
and `E` the Cartier divisor `mN`, `N^d = (E^d)/m^d`, so `N^d > d^d` means `(md)^d < (E^d)`, where
`(E^d)` is the intersection number `MMP.Mori.sheafSelfIntersectionNumber` of `d` copies of the
invertible sheaf `𝒪_W(E)`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 2.61, 3.5
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing MMP.Intersection Opposite

namespace MMP.Mori.KCartierDivisor

/-! ### Realizations of multiples -/

/-- The realization of an integral `ℚ`-Cartier divisor is computed by any integral lift. -/
private theorem realization_eq_sum_of_eq {X : Scheme.{u}} {c : KCartierDivisor ℚ X}
    (hc : ∀ D, ∃ n : ℤ, c D = n) {n : X.CartierDivisor →₀ ℤ}
    (hn : c = n.mapRange (Int.cast : ℤ → ℚ) Int.cast_zero) :
    realization c hc = n.sum fun D k => k • D := by
  subst hn
  exact realization_eq_sum n

/-- The realization depends only on the `ℚ`-Cartier divisor, not on the integrality witness. -/
private theorem realization_congr {X : Scheme.{u}} {c c' : KCartierDivisor ℚ X}
    (e : c = c') (hc : ∀ D, ∃ n : ℤ, c D = n) (hc' : ∀ D, ∃ n : ℤ, c' D = n) :
    realization c hc = realization c' hc' := by
  subst e
  rfl

/-- If `b • c` has integral coefficients, so does `(ab) • c`. -/
private theorem exists_int_natCast_mul_smul_apply {X : Scheme.{u}}
    {c : KCartierDivisor ℚ X} {b : ℕ} (hb : ∀ D, ∃ n : ℤ, ((b : ℚ) • c) D = n)
    (a : ℕ) : ∀ D, ∃ n : ℤ, (((a * b : ℕ) : ℚ) • c) D = n := fun D => by
  obtain ⟨z, hz⟩ := hb D
  refine ⟨a * z, ?_⟩
  simp only [Finsupp.smul_apply, smul_eq_mul] at hz ⊢
  push_cast
  rw [mul_assoc, hz]

/-- `realization ((ab) • c) = a • realization (b • c)`. -/
private theorem realization_natCast_mul_smul {X : Scheme.{u}} (c : KCartierDivisor ℚ X)
    (a b : ℕ) (hb : ∀ D, ∃ n : ℤ, ((b : ℚ) • c) D = n)
    (h : ∀ D, ∃ n : ℤ, (((a * b : ℕ) : ℚ) • c) D = n) :
    realization _ h = a • realization _ hb := by
  set n : X.CartierDivisor →₀ ℤ := ((b : ℚ) • c).mapRange Int.floor (by simp) with hn
  have hbn : (b : ℚ) • c = n.mapRange (Int.cast : ℤ → ℚ) Int.cast_zero := by
    ext D
    obtain ⟨z, hz⟩ := hb D
    simp [hn, hz]
  have habn :
      ((a * b : ℕ) : ℚ) • c = ((a : ℤ) • n).mapRange (Int.cast : ℤ → ℚ) Int.cast_zero := by
    ext D
    have := congrArg (fun F => F D) hbn
    simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.mapRange_apply] at this ⊢
    push_cast
    rw [mul_assoc, this]
  rw [realization_eq_sum_of_eq h habn, realization_eq_sum_of_eq hb hbn]
  change Finsupp.linearCombination ℤ id ((a : ℤ) • n) = a • Finsupp.linearCombination ℤ id n
  rw [map_smul, natCast_zsmul]

/-! ### Ampleness of a Cartier multiple -/

/-- Over the spectrum of a field, relative ampleness is ampleness. -/
private theorem isAmple_of_isRelativelyAmple {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) (N : X.Modules) [Stacks.Ample.IsInvertibleModule X N]
    (h : MMP.Mori.IsRelativelyAmple s N) : Stacks.Ample.IsAmple X N := by
  obtain ⟨V, -, hyV, hA⟩ := h (IsLocalRing.closedPoint _)
  have hV : V = ⊤ := TopologicalSpace.Opens.ext (Set.eq_univ_of_forall fun z => by
    rwa [Subsingleton.elim z (IsLocalRing.closedPoint _)])
  subst hV
  have : IsIso (s ⁻¹ᵁ (⊤ : (Spec (.of k)).Opens)).ι := inferInstanceAs (IsIso X.topIso.hom)
  exact Stacks.RelativeAmpleAffineBase.isAmple_of_isAmple_modulePullback _ N hA

/-- Every Cartier multiple `mN` of an ample `ℚ`-Cartier divisor `N` is ample. -/
private theorem isAmple_lineBundle_realization {k : Type u} [Field k] {X : Scheme.{u}}
    [IsNoetherian X] (s : X ⟶ Spec (.of k)) (N : KCartierDivisor ℚ X)
    (hN : MMP.Fourfold.KCartierDivisor.IsRelativelyAmpleQ s N) (m : ℕ) (hm : 0 < m)
    (hmN : ∀ E, ∃ n : ℤ, ((m : ℚ) • N) E = n) :
    Scheme.Modules.IsAmple X (MMP.CartierDivisor.sheaf (realization _ hmN)) := by
  obtain ⟨m', hm', h', hA⟩ := hN
  have hA' := isAmple_of_isRelativelyAmple s _ hA
  rw [MMP.Resolution.Bridges.isAmple_lineBundle_iff_nsmul _ m hm] at hA'
  have e : m • realization _ h' = m' • realization _ hmN := by
    rw [← realization_natCast_mul_smul N m m' h' (exists_int_natCast_mul_smul_apply h' m),
      ← realization_natCast_mul_smul N m' m hmN (exists_int_natCast_mul_smul_apply hmN m')]
    exact realization_congr (by rw [mul_comm]) _ _
  rw [e, ← MMP.Resolution.Bridges.isAmple_lineBundle_iff_nsmul _ m' hm'] at hA'
  exact Stacks.PowerFamilyBridge.modulesIsAmple_of_isAmple X _ hA'

/-! ### Growth of the sections -/

/-- The `k`-dimension of `H⁰(X, 𝒪_X(D))`, a `k`-vector space through `s : X ⟶ Spec k`. -/
private noncomputable def sectionsFinrank {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) (D : X.CartierDivisor) : ℕ :=
  letI : Module k (Γ(MMP.CartierDivisor.sheaf D, ⊤)) :=
    Module.compHom _ (MMP.Mori.scalarsToGlobalSections k s)
  Module.finrank k (Γ(MMP.CartierDivisor.sheaf D, ⊤))

/-- The `k`-dimension of the global sections of `𝒪_X(D)`, read through
`AlgebraicGeometry.globalSectionsOverField`, is `sectionsFinrank`. -/
private theorem finrank_globalSectionsOverField_eq_sectionsFinrank {k : Type u} [Field k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) (D : X.CartierDivisor) :
    Module.finrank k (globalSectionsOverField k s (MMP.CartierDivisor.sheaf D)) =
      sectionsFinrank s D := by
  have key : ∀ φ : k →+* Γ(X, ⊤), φ = MMP.Mori.scalarsToGlobalSections k s →
      (letI : Module k (Γ(MMP.CartierDivisor.sheaf D, ⊤)) := Module.compHom _ φ
       Module.finrank k (Γ(MMP.CartierDivisor.sheaf D, ⊤))) = sectionsFinrank s D := by
    rintro φ rfl
    rfl
  refine key _ ?_
  have : s.appLE ⊤ ⊤ (by simp) = s.appTop := by
    simp only [Scheme.Hom.appLE, TopologicalSpace.Opens.map_top, homOfLE_refl, op_id,
      CategoryTheory.Functor.map_id]
    exact Category.comp_id _
  rw [this]
  rfl

open Filter in
/-- A polynomial of degree `< d` is eventually bounded below by `-ε n^d`. -/
private theorem eventually_neg_mul_pow_le_eval {d : ℕ} (P : Polynomial ℚ)
    (hP : P.degree < (d : WithBot ℕ)) {ε : ℚ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, -ε * (n : ℚ) ^ d ≤ P.eval (n : ℚ) := by
  have hdeg : P.degree < (Polynomial.X ^ d : Polynomial ℚ).degree := by
    rwa [Polynomial.degree_X_pow]
  have h := (Polynomial.div_tendsto_atTop_zero_of_degree_lt P (Polynomial.X ^ d) hdeg).comp
    tendsto_natCast_atTop_atTop
  filter_upwards [h.eventually (lt_mem_nhds (neg_lt_zero.mpr hε)), eventually_ge_atTop 1]
    with n hn hn1
  simp only [Function.comp, Polynomial.eval_pow, Polynomial.eval_X] at hn
  have hpos : (0 : ℚ) < (n : ℚ) ^ d := by
    have : (1 : ℚ) ≤ n := by exact_mod_cast hn1
    positivity
  rw [lt_div_iff₀ hpos] at hn
  linarith

open Filter in
/-- **The counting estimate.** If `c^d/d! < a` and `P` has degree `< d`, then for all large `n`
the binomial coefficient `binom(nc + d, d)` is smaller than `a n^d + P(n)`. -/
private theorem eventually_choose_lt (d : ℕ) (hd : 0 < d) (c : ℕ) (a : ℚ)
    (ha : (c : ℚ) ^ d / d.factorial < a) (P : Polynomial ℚ) (hP : P.degree < (d : WithBot ℕ)) :
    ∀ᶠ n : ℕ in atTop, ((((n * c + d).choose d : ℕ)) : ℚ) < a * (n : ℚ) ^ d + P.eval (n : ℚ) := by
  set δ := a - (c : ℚ) ^ d / d.factorial with hδ
  have hδpos : 0 < δ := by linarith
  have hfac : (0 : ℚ) < d.factorial := by exact_mod_cast Nat.factorial_pos d
  have hlow := eventually_neg_mul_pow_le_eval P hP (half_pos hδpos)
  have hlim : Tendsto (fun n : ℕ => ((c : ℚ) + (d : ℚ) / n) ^ d) atTop (nhds ((c : ℚ) ^ d)) := by
    simpa using ((tendsto_const_nhds (x := (c : ℚ))).add
      (tendsto_const_div_atTop_nhds_zero_nat (d : ℚ))).pow d
  have hup : ∀ᶠ n : ℕ in atTop, ((c : ℚ) + (d : ℚ) / n) ^ d < (c : ℚ) ^ d + d.factorial * (δ / 4) :=
    hlim.eventually (gt_mem_nhds (by
      have : 0 < (d.factorial : ℚ) * (δ / 4) := by positivity
      linarith))
  filter_upwards [hlow, hup, Filter.eventually_ge_atTop 1] with n hn hu hn1
  have hn0 : (0 : ℚ) < n := by exact_mod_cast hn1
  have hnd : (0 : ℚ) < (n : ℚ) ^ d := by positivity
  have hchoose : ((((n * c + d).choose d : ℕ)) : ℚ) ≤ (((n * c + d : ℕ) : ℚ)) ^ d / d.factorial :=
    Nat.choose_le_pow_div d (n * c + d)
  have hrw : (((n * c + d : ℕ) : ℚ)) ^ d = (n : ℚ) ^ d * ((c : ℚ) + (d : ℚ) / n) ^ d := by
    rw [← mul_pow]
    congr 1
    push_cast
    field_simp
  rw [hrw] at hchoose
  have h3 : (n : ℚ) ^ d * ((c : ℚ) + (d : ℚ) / n) ^ d / d.factorial ≤
      (n : ℚ) ^ d * (((c : ℚ) ^ d + d.factorial * (δ / 4)) / d.factorial) := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hu.le hfac.le) hnd.le
  have h4 : ((c : ℚ) ^ d + d.factorial * (δ / 4)) / d.factorial =
      (c : ℚ) ^ d / d.factorial + δ / 4 := by
    field_simp
  rw [h4] at h3
  have h5 : (n : ℚ) ^ d * ((c : ℚ) ^ d / d.factorial + δ / 4) <
      a * (n : ℚ) ^ d + P.eval (n : ℚ) := by
    have : a = (c : ℚ) ^ d / d.factorial + δ := by linarith
    rw [this]
    nlinarith
  linarith

open Filter in
/-- **Growth of the sections.** If `E` is an ample Cartier divisor with `(md)^d < (E^d)`, then
for some `n > 0`, `h⁰(nE) > binom(nmd + d, d)`: by asymptotic Riemann–Roch
`h⁰(nE) = (E^d)/d! ⬝ n^d + O(n^{d-1})`. -/
private theorem exists_choose_lt_sectionsFinrank (k : Type u) [Field k] {W : Scheme.{u}}
    (sW : W ⟶ Spec (.of k)) [IsProper sW] (d : ℕ) (hd0 : 0 < d)
    (hd : topologicalKrullDim W = d) (E : W.CartierDivisor)
    (hamp : Scheme.Modules.IsAmple W (MMP.CartierDivisor.sheaf E)) (m : ℕ)
    (hvol : ((m * d : ℕ) : ℤ) ^ d <
      MMP.Mori.sheafSelfIntersectionNumber k sW (𝟙 W) d hd.le (MMP.CartierDivisor.sheaf E)) :
    ∃ n : ℕ, 0 < n ∧ (n * (m * d) + d).choose d < sectionsFinrank sW (n • E) := by
  obtain ⟨-, P, hPdeg, hev⟩ := asymptotic_riemann_roch k sW d hd _ hamp
  have hdeg : degreeWithRespectTo k sW (𝟙 W) d hd (MMP.CartierDivisor.sheaf E) hamp =
      MMP.Mori.sheafSelfIntersectionNumber k sW (𝟙 W) d hd.le (MMP.CartierDivisor.sheaf E) := by
    rw [degreeWithRespectTo_eq_selfIntersectionNumber]
    unfold selfIntersectionNumber
    rw [← MMP.Mori.Snapper.sheafIntersectionNumber_eq_intersectionNumber]
    rfl
  have ha : (((m * d : ℕ) : ℚ)) ^ d / d.factorial <
      (degreeWithRespectTo k sW (𝟙 W) d hd (MMP.CartierDivisor.sheaf E) hamp : ℚ) /
        d.factorial := by
    refine div_lt_div_of_pos_right ?_ (by exact_mod_cast Nat.factorial_pos d)
    rw [hdeg]
    exact_mod_cast hvol
  obtain ⟨n, h1, h2, h3⟩ := (hev.and ((eventually_choose_lt d hd0 (m * d) _ ha P hPdeg).and
    (eventually_ge_atTop 1))).exists
  refine ⟨n, h3, ?_⟩
  obtain ⟨e⟩ := MMP.Fourfold.nonempty_lineBundle_nat_smul_iso E n
  have hfin : Module.finrank k (globalSectionsOverField k sW
      (Stacks.SheafOfModules.Invertible.tensorPower W.presheaf W.ringCatSheaf.2
        (MMP.CartierDivisor.sheaf E) (n : ℤ))) = sectionsFinrank sW (n • E) := by
    rw [← finrank_globalSectionsOverField_eq_sectionsFinrank]
    exact ((ModuleCat.restrictScalars _).mapIso
      ((SheafOfModules.evaluation _ (Opposite.op ⊤)).mapIso
        (Stacks.PowerFamilyBridge.invertibleTensorPowerModuleIso W (MMP.CartierDivisor.sheaf E) n ≪≫
          e.symm))).toLinearEquiv.finrank_eq
  rw [← hfin]
  exact_mod_cast h2.trans_eq h1.symm

section Jets

variable {k R : Type*} [Field k] [CommRing R] [IsLocalRing R] [Algebra k R] {d : ℕ}
  (x : Fin d → R)

/-- The monomial `x^α = ∏ᵢ xᵢ^{αᵢ}`. -/
private def jetMonomial (α : Fin d → ℕ) : R := ∏ i, x i ^ α i

/-- The monomials of degree exactly `j`. -/
private def jetMonomials (j : ℕ) : Set R :=
  {r | ∃ α : Fin d → ℕ, ∑ i, α i = j ∧ r = jetMonomial x α}

/-- The monomials of degree `< j`. -/
private def jetMonomialsLT (j : ℕ) : Set R :=
  {r | ∃ α : Fin d → ℕ, ∑ i, α i < j ∧ r = jetMonomial x α}

private theorem pow_le_span_jetMonomials (hx : Ideal.span (Set.range x) = maximalIdeal R)
    (j : ℕ) : maximalIdeal R ^ j ≤ Ideal.span (jetMonomials x j) := by
  induction j with
  | zero =>
    rw [pow_zero, Ideal.one_eq_top, top_le_iff, Ideal.eq_top_iff_one]
    exact Ideal.subset_span ⟨0, by simp, by simp [jetMonomial]⟩
  | succ j ih =>
    rw [pow_succ]
    refine (Ideal.mul_mono_left ih).trans ?_
    rw [← hx, Ideal.span_mul_span]
    refine Ideal.span_mono ?_
    rintro _ ⟨a, ⟨α, hα, rfl⟩, b, ⟨i, rfl⟩, rfl⟩
    refine ⟨α + Pi.single i 1, ?_, ?_⟩
    · simp only [Pi.add_apply]
      rw [Finset.sum_add_distrib, hα]
      simp
    · simp only [jetMonomial, Pi.add_apply, pow_add, Finset.prod_mul_distrib]
      congr 1
      rw [Finset.prod_eq_single i]
      · simp
      · intro b _ hb
        simp [hb]
      · simp

private theorem jetMonomial_mem_pow (hx : Ideal.span (Set.range x) = maximalIdeal R)
    (α : Fin d → ℕ) : jetMonomial x α ∈ maximalIdeal R ^ (∑ i, α i) := by
  rw [← Finset.prod_pow_eq_pow_sum, jetMonomial]
  exact Ideal.prod_mem_prod fun i _ =>
    Ideal.pow_mem_pow (hx ▸ Ideal.subset_span ⟨i, rfl⟩) _

private theorem exists_sub_mem_pow_succ
    (hres : Function.Surjective (algebraMap k (R ⧸ maximalIdeal R)))
    (hx : Ideal.span (Set.range x) = maximalIdeal R) (j : ℕ) {t : R}
    (ht' : t ∈ Ideal.span (jetMonomials x j)) :
    ∃ s ∈ Submodule.span k (jetMonomials x j), t - s ∈ maximalIdeal R ^ (j + 1) := by
  induction ht' using Submodule.span_induction with
  | mem t ht => exact ⟨t, Submodule.subset_span ht, by simp⟩
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨s, hs, hs'⟩ := ha
    obtain ⟨s', hs2, hs2'⟩ := hb
    refine ⟨s + s', add_mem hs hs2, ?_⟩
    convert add_mem hs' hs2' using 1
    ring
  | smul c t htm ih =>
    obtain ⟨s, hs, hs'⟩ := ih
    obtain ⟨a, ha⟩ := hres (Ideal.Quotient.mk _ c)
    have hca : c - algebraMap k R a ∈ maximalIdeal R := by
      rw [← Ideal.Quotient.eq, ← ha]
      rfl
    have htj : t ∈ maximalIdeal R ^ j := by
      refine Submodule.span_le.mpr ?_ htm
      rintro _ ⟨α, hα, rfl⟩
      rw [← hα]
      exact jetMonomial_mem_pow x hx α
    refine ⟨a • s, Submodule.smul_mem _ _ hs, ?_⟩
    have h1 : (c - algebraMap k R a) * t ∈ maximalIdeal R ^ (j + 1) := by
      rw [pow_succ']
      exact Ideal.mul_mem_mul hca htj
    convert add_mem h1 (Ideal.mul_mem_left _ (algebraMap k R a) hs') using 1
    rw [smul_eq_mul, Algebra.smul_def]
    ring

private theorem exists_sub_mem_pow
    (hres : Function.Surjective (algebraMap k (R ⧸ maximalIdeal R)))
    (hx : Ideal.span (Set.range x) = maximalIdeal R) (j : ℕ) (r : R) :
    ∃ s ∈ Submodule.span k (jetMonomialsLT x j), r - s ∈ maximalIdeal R ^ j := by
  induction j with
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | succ j ih =>
    obtain ⟨s, hs, hrs⟩ := ih
    obtain ⟨s', hs', hrs'⟩ := exists_sub_mem_pow_succ x hres hx j
      (pow_le_span_jetMonomials x hx j hrs)
    refine ⟨s + s', add_mem (Submodule.span_mono ?_ hs) (Submodule.span_mono ?_ hs'), ?_⟩
    · rintro _ ⟨α, hα, rfl⟩
      exact ⟨α, by omega, rfl⟩
    · rintro _ ⟨α, hα, rfl⟩
      exact ⟨α, by omega, rfl⟩
    · convert hrs' using 1
      ring

/-- **The jet space is small.** If the residue field of the local ring `R` is the image of `k`
and the maximal ideal is generated by `d` elements, then `R/𝔪^{K+1}` is spanned over `k` by at
most `binom(K + d, d)` elements, the classes of the monomials of degree `≤ K` in the generators. -/
private theorem exists_finset_card_le_span_eq_top
    (hres : Function.Surjective (algebraMap k (R ⧸ maximalIdeal R)))
    (hx : Ideal.span (Set.range x) = maximalIdeal R) (K : ℕ) :
    ∃ t : Finset (R ⧸ maximalIdeal R ^ (K + 1)), t.card ≤ (K + d).choose d ∧
      Submodule.span k (t : Set (R ⧸ maximalIdeal R ^ (K + 1))) = ⊤ := by
  classical
  set q := Ideal.Quotient.mkₐ k (maximalIdeal R ^ (K + 1)) with hq
  let S : Finset (Fin (d + 1) →₀ ℕ) := (Finset.univ : Finset (Fin (d + 1))).finsuppAntidiag K
  let f : S → R ⧸ maximalIdeal R ^ (K + 1) := fun α =>
    q (jetMonomial x (fun i => α.1 i.castSucc))
  have hspan : Submodule.span k (Set.range f) = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨s, hs, hrs⟩ := exists_sub_mem_pow x hres hx (K + 1) r
    have h1 : Ideal.Quotient.mk (maximalIdeal R ^ (K + 1)) r = q s := by
      rwa [hq, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq]
    rw [h1]
    have h2 : q s ∈ (Submodule.span k (jetMonomialsLT x (K + 1))).map q.toLinearMap :=
      Submodule.mem_map_of_mem hs
    rw [Submodule.map_span] at h2
    refine Submodule.span_mono ?_ h2
    rintro _ ⟨_, ⟨α, hα, rfl⟩, rfl⟩
    let β : Fin (d + 1) →₀ ℕ :=
      Finsupp.equivFunOnFinite.symm (Fin.snoc α (K - ∑ i, α i))
    have hβ : β ∈ S := by
      rw [Finset.mem_finsuppAntidiag]
      refine ⟨?_, by simp⟩
      simp only [β, Finsupp.coe_equivFunOnFinite_symm, Fin.sum_univ_castSucc,
        Fin.snoc_castSucc, Fin.snoc_last]
      omega
    refine ⟨⟨β, hβ⟩, ?_⟩
    simp only [f, β, Finsupp.coe_equivFunOnFinite_symm, Fin.snoc_castSucc]
    rfl
  have hcard : Fintype.card S = (K + d).choose d := by
    rw [Fintype.card_coe, Finset.card_finsuppAntidiag_nat_eq_choose, Finset.card_univ,
      Fintype.card_fin, show d + 1 + K - 1 = K + d by omega, Nat.choose_symm_add]
  refine ⟨Finset.univ.image f, ?_, ?_⟩
  · exact Finset.card_image_le.trans (by rw [Finset.card_univ, hcard])
  · rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, hspan]

/-- The jet space `R/𝔪^{K+1}` is finite-dimensional over `k`, of dimension at most
`binom(K + d, d)`, when the residue field is the image of `k` and `𝔪` has `d` generators. -/
private theorem finite_and_finrank_quotient_pow_le
    (hres : Function.Surjective (algebraMap k (R ⧸ maximalIdeal R)))
    (hx : Ideal.span (Set.range x) = maximalIdeal R) (K : ℕ) :
    Module.Finite k (R ⧸ maximalIdeal R ^ (K + 1)) ∧
      Module.finrank k (R ⧸ maximalIdeal R ^ (K + 1)) ≤ (K + d).choose d := by
  obtain ⟨t, htc, htspan⟩ := exists_finset_card_le_span_eq_top x hres hx K
  refine ⟨⟨⟨t, htspan⟩⟩, ?_⟩
  have h1 := finrank_span_finset_le_card (R := k) t
  rw [Set.finrank, htspan, finrank_top] at h1
  exact h1.trans htc

end Jets

/-! ### Sections vanishing to high order at a point -/

/-- If `u` is the value of a global section `σ` of `𝒪_W(D)`, then `D + div u` is effective. -/
private theorem isEffective_add_principalDivisor {W : Scheme.{u}} (D : W.CartierDivisor)
    (σ : Γ(MMP.CartierDivisor.sheaf D, ⊤)) (u : (W.totalQuotientSheaf.obj.obj (op ⊤))ˣ)
    (huv : (u : W.totalQuotientSheaf.obj.obj (op ⊤)) = MMP.CartierDivisorSheaf.sectionVal σ) :
    IsEffective (D + Intersection.principalDivisor u) := by
  intro y
  obtain ⟨Uy, hyU, gy, hgy⟩ := MMP.Intersection.exists_isLocalEquationOn D y
  obtain ⟨b, hb⟩ := MMP.CartierDivisor.sectionVal_mem_lineBundleSections σ y trivial _ ⟨Uy, hyU,
      gy, hgy, rfl⟩
  obtain ⟨V, hyV, r, rfl⟩ := W.presheaf.exists_germ_eq b
  let τ : W.totalQuotientSheaf.obj.obj (op Uy) :=
    ((gy * resUnit (homOfLE le_top) u : (W.totalQuotientSheaf.obj.obj (op Uy))ˣ) : _)
  have hτ : W.totalQuotientSheaf.presheaf.germ V y hyV (toTotalQuotient V r) =
      W.totalQuotientSheaf.presheaf.germ Uy y hyU τ := by
    rw [germ_toTotalQuotient, hb]
    simp only [τ, Units.val_mul, map_mul]
    erw [TopCat.Presheaf.germ_res_apply]
    rw [huv]
    ring
  obtain ⟨V', hyV', i₁, i₂, heq⟩ :=
    W.totalQuotientSheaf.presheaf.germ_eq y hyV hyU _ _ hτ
  let w := MMP.Intersection.resUnit i₂ (gy * resUnit (homOfLE le_top) u)
  have hsw : toTotalQuotient V' (W.presheaf.map i₁.op r) =
      (w : W.totalQuotientSheaf.obj.obj (op V')) := by
    rwa [MMP.Mori.toTotalQuotient_map]
  have hsu : IsUnit (toTotalQuotient V' (W.presheaf.map i₁.op r)) := hsw ▸ w.isUnit
  refine ⟨V', hyV', W.presheaf.map i₁.op r, hsu, ?_⟩
  rw [show hsu.unit = w from Units.ext (by rw [IsUnit.unit_spec, hsw])]
  exact MMP.Intersection.isLocalEquationOn_resUnit i₂
    (hgy.mul (isLocalEquationOn_principalDivisor_res u Uy))

section Evaluation

variable {k : Type u} [Field k] {W : Scheme.{u}} (sW : W ⟶ Spec (.of k)) [IsIntegral W] {x : W}

/-- On an integral scheme a nonzero global section of `𝓜_W` is a unit. -/
private theorem isUnit_of_ne_zero {σ : W.totalQuotientSheaf.obj.obj (op ⊤)} (hσ : σ ≠ 0) :
    IsUnit σ := by
  let e := RingEquiv.ofBijective _ (MMP.CartierDivisorSheaf.ofFunctionField_bijective (X := W) ⊤
    ⟨genericPoint W, trivial⟩)
  have h0 : e.symm σ ≠ 0 := fun h => hσ (by simpa using congrArg e h)
  simpa using (isUnit_iff_ne_zero.mpr h0).map e

/-- **Sections vanishing to order `K` at `x`.** If `h⁰(D)` exceeds the `k`-dimension of the jet
space `𝒪_{W,x}/𝔪_x^K`, then there is an effective Cartier divisor `D' ∼ D` with a local equation
at `x` in `𝔪_x^K`. With `ψ` a local equation of `D` at `x`, `σ ↦ σψ` is a `k`-linear map
`H⁰(W, 𝒪_W(D)) → 𝒪_{W,x}`; a nonzero `σ` in the kernel of its composite with the projection to
`𝒪_{W,x}/𝔪_x^K` gives `D' = D + div σ`, with local equation `σψ` at `x`. -/
private theorem exists_isEffective_linearlyEquivalent_of_finrank_lt (D : W.CartierDivisor)
    (K : ℕ)
    (hfin : letI := MMP.Mori.stalkAlgebra sW x
      Module.Finite k (W.presheaf.stalk x ⧸ maximalIdeal (W.presheaf.stalk x) ^ K))
    (hlt : (letI := MMP.Mori.stalkAlgebra sW x
      Module.finrank k (W.presheaf.stalk x ⧸ maximalIdeal (W.presheaf.stalk x) ^ K)) <
      sectionsFinrank sW D) :
    ∃ D' : W.CartierDivisor, IsEffective D' ∧ LinearlyEquivalent D' D ∧
      ∃ a ∈ maximalIdeal (W.presheaf.stalk x) ^ K,
        IsLocalEquationAt D' x (stalkToTotalQuotient x a) := by
  classical
  let := MMP.Mori.stalkAlgebra sW x
  let : Module k (Γ(MMP.CartierDivisor.sheaf D, ⊤)) :=
    Module.compHom _ (MMP.Mori.scalarsToGlobalSections k sW)
  obtain ⟨U, hxU, g, hg⟩ := MMP.Intersection.exists_isLocalEquationOn D x
  set f := W.totalQuotientSheaf.presheaf.germ U x hxU (g : _) with hf
  have hA : ∀ σ : Γ(MMP.CartierDivisor.sheaf D, ⊤), ∃ a : W.presheaf.stalk x,
      stalkToTotalQuotient x a = W.totalQuotientSheaf.presheaf.germ ⊤ x trivial
          (MMP.CartierDivisorSheaf.sectionVal σ) * f :=
    fun σ => MMP.CartierDivisor.sectionVal_mem_lineBundleSections σ x trivial f
      ⟨U, hxU, g, hg, rfl⟩
  choose ev hev using hA
  have inj := stalkToTotalQuotient_injective x
  have hevadd : ∀ σ τ, ev (σ + τ) = ev σ + ev τ := fun σ τ => inj (by
    rw [hev, map_add, hev, hev, MMP.CartierDivisor.sectionVal_add, map_add, add_mul])
  have hevsmul : ∀ (c : k) σ, ev (c • σ) = c • ev σ := fun c σ => inj (by
    rw [hev, Algebra.smul_def, map_mul, hev]
    change W.totalQuotientSheaf.presheaf.germ ⊤ x trivial
      (toTotalQuotient ⊤ (MMP.Mori.scalarsToGlobalSections k sW c) *
          MMP.CartierDivisorSheaf.sectionVal σ) * f = _
    rw [map_mul, mul_assoc]
    congr 1
    exact germ_toTotalQuotient (TopologicalSpace.Opens.mem_top x) _)
  let L : Γ(MMP.CartierDivisor.sheaf D, ⊤) →ₗ[k] W.presheaf.stalk x :=
    { toFun := ev, map_add' := hevadd, map_smul' := hevsmul }
  let Φ := (Ideal.Quotient.mkₐ k (maximalIdeal (W.presheaf.stalk x) ^ K)).toLinearMap ∘ₗ L
  have hlt' : Module.finrank k (W.presheaf.stalk x ⧸ maximalIdeal (W.presheaf.stalk x) ^ K) <
      Module.finrank k (Γ(MMP.CartierDivisor.sheaf D, ⊤)) := hlt
  have : Module.Finite k (Γ(MMP.CartierDivisor.sheaf D, ⊤)) :=
    Module.finite_of_finrank_pos ((Nat.zero_le _).trans_lt hlt')
  obtain ⟨σ, hσker, hσ0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := Φ) hlt')
  have hσ1 : (MMP.CartierDivisorSheaf.sectionVal σ) ≠ 0 := fun h =>
    hσ0 (MMP.CartierDivisorSheaf.sectionVal_injective (h.trans
        MMP.CartierDivisor.sectionVal_zero.symm))
  obtain ⟨u, huv⟩ := isUnit_of_ne_zero hσ1
  refine ⟨D + Intersection.principalDivisor u, isEffective_add_principalDivisor D σ u huv, ?_,
    ev σ, Ideal.Quotient.eq_zero_iff_mem.1 hσker, ?_⟩
  · change D + Intersection.principalDivisor u - D ∈ principalSubgroup W
    rw [add_sub_cancel_left]
    exact principalDivisor_mem u
  · refine ⟨U, hxU, _, hg.mul (isLocalEquationOn_principalDivisor_res u U), ?_⟩
    rw [hev, hf]
    simp only [Units.val_mul, map_mul]
    erw [TopCat.Presheaf.germ_res_apply]
    rw [huv]
    ring

end Evaluation

/-! ### The concentration statement -/

/-- The stalk at a point of the smooth locus is a regular local ring. -/
private theorem isRegularLocalRing_stalk_of_mem_smoothLocus {k : Type u} [Field k]
    {W : Scheme.{u}} (sW : W ⟶ Spec (.of k)) {x : W} (hxs : x ∈ MMP.Mori.smoothLocus sW) :
    IsRegularLocalRing (W.presheaf.stalk x) := by
  obtain ⟨U, hxU, hU⟩ := MMP.Mori.mem_smoothLocus_iff.mp hxs
  have : Smooth (U.ι ≫ sW) := hU
  have := isRegularLocalRing_stalk_of_smooth_over_field (U.ι ≫ sW) ⟨x, hxU⟩
  exact IsRegularLocalRing.of_ringEquiv (U.stalkIso ⟨x, hxU⟩).commRingCatIsoToRingEquiv

/-- On a scheme of dimension `d`, the maximal ideal of a regular stalk has at most `d`
generators. -/
private theorem exists_le_span_range_eq_maximalIdeal {W : Scheme.{u}} [IsLocallyNoetherian W]
    {d : ℕ} (hd : topologicalKrullDim W = d) (x : W) [IsRegularLocalRing (W.presheaf.stalk x)] :
    ∃ e ≤ d, ∃ g : Fin e → W.presheaf.stalk x,
      Ideal.span (Set.range g) = maximalIdeal (W.presheaf.stalk x) := by
  obtain ⟨s, hs, hspan⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank
    (IsNoetherian.noetherian (maximalIdeal (W.presheaf.stalk x)))
  refine ⟨s.card, ?_, fun i => (s.equivFin.symm i : W.presheaf.stalk x), ?_⟩
  · have h2 : ringKrullDim (W.presheaf.stalk x) ≤ d := by
      rw [← hd, topologicalKrullDim_eq_iSup_krullDimOfRing_stalk]
      exact le_iSup (fun y : W => ringKrullDim (W.presheaf.stalk y)) x
    rw [← IsRegularLocalRing.spanFinrank_maximalIdeal (R := W.presheaf.stalk x), ← hs] at h2
    exact_mod_cast h2
  · rw [← hspan]
    congr 1
    ext y
    simp only [Set.mem_range, Finset.mem_coe]
    exact ⟨fun ⟨i, hi⟩ => hi ▸ (s.equivFin.symm i).2,
      fun hy => ⟨s.equivFin ⟨y, hy⟩, by simp⟩⟩

/-- Let `W` be an integral projective variety of dimension `d > 0` over an algebraically closed
field `k`, `N` an ample `ℚ`-Cartier divisor on `W`, and `x` a closed point of the smooth locus of
`W`. If `N^d > d^d`, read through a Cartier multiple `E = mN` (`m > 0`) as `(md)^d < (E^d)`, then
there is an effective `ℚ`-Cartier divisor `G ∼_ℚ N` with `mult_x G > d`: there are `q > 0` with
`qN` integral and an effective Cartier divisor `D ∼ qN` with a local equation at `x` in
`𝔪_x^{qd+1}`, and `G = D/q`. -/
@[mmp "lem_mmp_lc_bpf_point_concentration"]
public theorem exists_isEffective_linearlyEquivalent_mem_maximalIdeal_pow
    (k : Type u) [Field k] [IsAlgClosed k] {W : Scheme.{u}}
    (sW : W ⟶ Spec (.of k)) [IsProper sW] [IsIntegral W]
    (hW : MMP.Mori.IsProjectiveVariety k sW) (d : ℕ) (hd0 : 0 < d)
    (hd : topologicalKrullDim W = d)
    (N : KCartierDivisor ℚ W) (hN : MMP.Fourfold.KCartierDivisor.IsRelativelyAmpleQ sW N)
    (m : ℕ) (hm : 0 < m) (hmN : ∀ E, ∃ n : ℤ, ((m : ℚ) • N) E = n)
    (hvol : ((m * d : ℕ) : ℤ) ^ d < MMP.Mori.sheafSelfIntersectionNumber k sW (𝟙 W) d hd.le
      (MMP.CartierDivisor.sheaf (realization ((m : ℚ) • N) hmN)))
    (x : W) (hx : IsClosed ({x} : Set W)) (hxs : x ∈ MMP.Mori.smoothLocus sW) :
    ∃ q : ℕ, 0 < q ∧ ∃ hq : ∀ E, ∃ n : ℤ, ((q : ℚ) • N) E = n,
      ∃ D : W.CartierDivisor, IsEffective D ∧
        LinearlyEquivalent D (realization ((q : ℚ) • N) hq) ∧
        ∃ a ∈ maximalIdeal (W.presheaf.stalk x) ^ (q * d + 1),
          IsLocalEquationAt D x (stalkToTotalQuotient x a) := by
  have : AlgebraicGeometry.IsVariety k sW := hW.toIsVariety
  have : LocallyOfFiniteType sW := AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
  have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian sW
  have : IsNoetherian W := ⟨⟩
  set E := realization ((m : ℚ) • N) hmN
  have hamp : Scheme.Modules.IsAmple W (MMP.CartierDivisor.sheaf E) :=
    isAmple_lineBundle_realization sW N hN m hm hmN
  have := isRegularLocalRing_stalk_of_mem_smoothLocus sW hxs
  obtain ⟨n, hn, hlt⟩ := exists_choose_lt_sectionsFinrank k sW d hd0 hd E hamp m hvol
  let := MMP.Mori.stalkAlgebra sW x
  have hres := MMP.Mori.SurfaceAux.residue_surjective sW x hx
  obtain ⟨e, hed, g, hg⟩ := exists_le_span_range_eq_maximalIdeal hd x
  set K := n * (m * d) with hK
  obtain ⟨hfin, hjet⟩ := finite_and_finrank_quotient_pow_le g hres hg K
  have hchoose : (K + e).choose e ≤ (K + d).choose d := by
    rw [← Nat.choose_symm_add, ← Nat.choose_symm_add]
    exact Nat.choose_le_choose K (by omega)
  obtain ⟨D, hD, hDE, a, ha, hloc⟩ :=
    exists_isEffective_linearlyEquivalent_of_finrank_lt sW (n • E) (K + 1) hfin
      ((hjet.trans hchoose).trans_lt hlt)
  have hq := exists_int_natCast_mul_smul_apply hmN n
  refine ⟨n * m, Nat.mul_pos hn hm, hq, D, hD, ?_, a, ?_, hloc⟩
  · rwa [realization_natCast_mul_smul N n m hmN hq]
  · rw [hK] at ha
    convert ha using 2
    ring

end MMP.Mori.KCartierDivisor

end
