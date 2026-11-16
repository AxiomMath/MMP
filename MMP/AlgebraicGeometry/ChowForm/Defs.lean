module

public import MMP.AlgebraicGeometry.ChowForm.FibreKoszulBase
public import MMP.AlgebraicGeometry.Chow.FieldSituation
public import MMP.AlgebraicGeometry.ProjectiveSpace.ProjComparison
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Dimension.AffineCone

/-!
# Definitions and points of projective space for the Chow-form morphism

For a curve `C` in `ℙᴺ_k` over an algebraically closed field of characteristic zero, the pairs of
hyperplanes `(u, v)` meeting `C` form an irreducible hypersurface in `k^{2(N+1)}`, cut out by an
incidence form unique up to a scalar. The product of the incidence forms of the components of a
1-cycle, with multiplicities, is a point of the projective space of `(d, d)`-forms. A morphism to
that space whose value at each closed point is the point of the fundamental cycle of the fibre is
the Chow-form morphism of the family; it is unique, compatible with base change, and glues from
an open cover.

## Main definitions

* `cyc`: the push-forward to `ℙᴺ_k` of the fundamental 1-cycle of a fibre.
* `IncForm`: an irreducible polynomial whose zero locus is the incidence locus of a curve.
* `ChowAt`: a point of the space of `(d, d)`-forms is the class of the product of incidence forms
  of a cycle.
* `ChowMor`: a morphism to the space of `(d, d)`-forms takes the Chow point of the fibre at each
  closed point.
* `incIdeal`: the ideal of the incidence locus of a homogeneous prime.

## Main results

* `exists_incForm`: every proper curve in `ℙᴺ_k` has an incidence form.
* `incForm_unique`: an incidence form is unique up to a nonzero scalar.
* `chowAt_unique`: the Chow point of a cycle is unique.
* `chowMor_unique`: the Chow-form morphism over a reduced base of finite type is unique.
* `chowMor_baseChange`: the Chow-form morphism is compatible with base change.
* `exists_chowMor_of_cover`: the Chow-form morphism glues from an open cover.

## References

* [J. Kollár, *Rational curves on algebraic varieties*][Kollar1996], I.3
-/

@[expose] public section

universe u

namespace MMP.Chow.DeterminantCurveForm

open MMP CategoryTheory Limits AlgebraicGeometry Stacks.AlgebraicGeometry.ProjPolyChart MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

section Defs

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {Y : Scheme.{u}} {N : ℕ}

/-- The push-forward to `ℙᴺ_k` of the fundamental 1-cycle of the fibre of `ρ` over `s`. -/
noncomputable def cyc (g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N))
    {T 𝒟 : Scheme.{u}} (sT : T ⟶ Spec (.of k)) (ρ : 𝒟 ⟶ T) (r : 𝒟 ⟶ Y) (s : T) :
    Mori.OneCycle ℤ (projToSpecCoeff k N) :=
  ∑ᶠ C : {C : Mori.ProperCurve (ρ.fiberι s ≫ ρ ≫ sT) //
          closure {C.point} ∈ irreducibleComponents (ρ.fiber s)},
    ((Module.length ((ρ.fiber s).presheaf.stalk C.1.point)
        ((ρ.fiber s).presheaf.stalk C.1.point)).toNat : ℤ) •
      Mori.cyclePushforwardOfPoint ℤ (projToSpecCoeff k N) (ρ.fiberι s ≫ r ≫ g) C.1.point

/-- The monomials of bidegree `(d, d)` in `(u, v)`. -/
abbrev Bi (N d : ℕ) := {e : (Fin (N + 1) ⊕ Fin (N + 1)) →₀ ℕ //
  (∑ j, e (Sum.inl j)) = d ∧ (∑ j, e (Sum.inr j)) = d}

/-- There are finitely many monomials of bidegree `(d, d)`. -/
instance finite_Bi (N d : ℕ) : Finite (Bi N d) := by
  have : ∀ (e : Bi N d) (j : Fin (N + 1) ⊕ Fin (N + 1)), e.1 j < d + 1 := by
    intro e j
    rcases j with j | j
    · have := Finset.single_le_sum (f := fun j => e.1 (Sum.inl j)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ j)
      have := e.2.1
      omega
    · have := Finset.single_le_sum (f := fun j => e.1 (Sum.inr j)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ j)
      have := e.2.2
      omega
  refine Finite.of_injective (fun (e : Bi N d) (j : Fin (N + 1) ⊕ Fin (N + 1)) =>
    (⟨e.1 j, this e j⟩ : Fin (d + 1))) ?_
  intro e e' h
  apply Subtype.ext
  ext j
  simpa using congrFun h j

/-- `G` is an irreducible polynomial whose zero locus is the incidence locus of the curve `C`. -/
def IncForm (C : Mori.ProperCurve (projToSpecCoeff k N))
    (G : MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k) : Prop :=
  Irreducible G ∧
    ∀ u v : Fin (N + 1) → k, eval (Sum.elim u v) G = 0 ↔
      ∃ p ∈ closure ({C.point} : Set (AlgebraicGeometry.Proj (polyGrading k N))),
        (∑ j, MvPolynomial.C (u j) * X j) ∈ ProjectiveSpectrum.asHomogeneousIdeal p ∧
        (∑ j, MvPolynomial.C (v j) * X j) ∈ ProjectiveSpectrum.asHomogeneousIdeal p

/-- The point `x` of the space of `(d, d)`-forms is the class of the product of incidence forms
of the cycle `z`. -/
def ChowAt (d : ℕ) (z : Mori.OneCycle ℤ (projToSpecCoeff k N))
    (x : Intersection.ProjSpace k (ULift.{u} (Bi N d))) : Prop :=
  ∀ G : Mori.ProperCurve (projToSpecCoeff k N) → MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k,
    (∀ C ∈ z.support, IncForm C (G C)) →
    let F := ∏ C ∈ z.support, G C ^ (z C).toNat
    (∀ e ∈ F.support, (∑ j, e (Sum.inl j)) = d ∧ (∑ j, e (Sum.inr j)) = d) ∧
    ∀ b b' : ULift.{u} (Bi N d), F.coeff b'.down.1 • X b - F.coeff b.down.1 • X b' ∈
      ProjectiveSpectrum.asHomogeneousIdeal x

/-- The morphism `φ : T ⟶ ℙ(Bi N d)` is a `k`-morphism whose value at every closed point `s` is the
Chow point of the cycle `cyc g sT ρ r s`. -/
def ChowMor (g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N)) (d : ℕ)
    {T 𝒟 : Scheme.{u}} (sT : T ⟶ Spec (.of k)) (ρ : 𝒟 ⟶ T) (r : 𝒟 ⟶ Y)
    (φ : T ⟶ Intersection.ProjSpace k (ULift.{u} (Bi N d))) : Prop :=
  φ ≫ Intersection.ProjSpace.toSpec k _ = sT ∧
    ∀ s, IsClosed ({s} : Set T) → ChowAt d (cyc g sT ρ r s) (φ s)

/-! ### Points of projective space -/

section ProjPts

/-- The irrelevant ideal of `MvPolynomial ι k` lies in the ideal generated by the variables. -/
theorem irrelevant_le_span_X {ι k : Type*} [Field k] :
    (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule ι k)).toIdeal ≤
      Ideal.span (Set.range (X : ι → MvPolynomial ι k)) := by
  rw [HomogeneousIdeal.irrelevant_eq_span]
  refine Ideal.span_le.mpr ?_
  intro f hf
  simp only [Set.mem_iUnion] at hf
  obtain ⟨m, hm, hf⟩ := hf
  have := (MvPolynomial.mem_ideal_span_X_image (x := f) (s := (Set.univ : Set ι))).mpr ?_
  · simpa [← Set.image_univ] using this
  · intro e he
    rw [MvPolynomial.mem_support_iff] at he
    have hw := (MvPolynomial.mem_homogeneousSubmodule _ _).mp hf he
    by_contra hcon
    push Not at hcon
    have : e = 0 := by
      ext i
      simpa using hcon i (Set.mem_univ i)
    subst this
    simp at hw
    omega

/-- If a point of `Proj` contains every `c b' • X b - c b • X b'` and `c b0 ≠ 0`, it does not
contain `X b0`. -/
theorem X_not_mem {ι k : Type*} [Field k] [DecidableEq ι] (c : ι → k) (b0 : ι) (hb0 : c b0 ≠ 0)
    (p : ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule ι k))
    (hp : ∀ b b', c b' • (X b : MvPolynomial ι k) - c b • X b' ∈ p.asHomogeneousIdeal) :
    (X b0 : MvPolynomial ι k) ∉ p.asHomogeneousIdeal := by
  intro h0
  apply p.not_irrelevant_le
  refine irrelevant_le_span_X.trans (Ideal.span_le.mpr ?_)
  rintro _ ⟨b, rfl⟩
  have h2 : c b0 • (X b : MvPolynomial ι k) ∈ p.asHomogeneousIdeal := by
    rw [show c b0 • (X b : MvPolynomial ι k) = (c b0 • X b - c b • X b0) + c b • X b0 by simp]
    refine add_mem (hp b b0) ?_
    rw [smul_eq_C_mul]
    exact Ideal.mul_mem_left p.asHomogeneousIdeal.toIdeal _ h0
  simpa [smul_eq_C_mul, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hb0] using
    Ideal.mul_mem_left p.asHomogeneousIdeal.toIdeal (C (c b0)⁻¹) h2

/-- Substituting `r b * X b0` for each `X b` in a form of degree `m` gives
`f(r) * X b0 ^ m`. -/
theorem aeval_smul_homog {ι k : Type*} [Field k] (r : ι → k) (b0 : ι) {m : ℕ} {f : MvPolynomial ι k}
    (hf : f.IsHomogeneous m) :
    aeval (fun b => (C (r b) * X b0 : MvPolynomial ι k)) f =
      C (eval r f) * X b0 ^ m := by
  rw [aeval_def, eval₂_eq, eval_eq, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hw := hf (mem_support_iff.mp hd)
  have hdeg : ∑ i ∈ d.support, d i = m := by
    simpa [Finsupp.weight_apply, Finsupp.sum] using hw
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg, map_mul,
    map_prod, map_pow, algebraMap_eq]
  ring

/-- Modulo a point of `Proj` containing every `c b' • X b - c b • X b'`, a polynomial is congruent
to its substitution `X b ↦ (c b / c b0) * X b0`. -/
theorem sub_aeval_mem {ι k : Type*} [Field k] [DecidableEq ι] (c : ι → k) (b0 : ι) (hb0 : c b0 ≠ 0)
    (p : ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule ι k))
    (hp : ∀ b b', c b' • (X b : MvPolynomial ι k) - c b • X b' ∈ p.asHomogeneousIdeal)
    (f : MvPolynomial ι k) :
    f - aeval (fun b => (C (c b / c b0) * X b0 : MvPolynomial ι k)) f ∈
      p.asHomogeneousIdeal.toIdeal := by
  have hp' : ∀ b b', c b' • (X b : MvPolynomial ι k) - c b • X b' ∈ p.asHomogeneousIdeal.toIdeal :=
    hp
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg =>
    simpa [sub_add_sub_comm] using add_mem hf hg
  | mul_X f b hf =>
    have hX : (X b : MvPolynomial ι k) - C (c b / c b0) * X b0 ∈ p.asHomogeneousIdeal.toIdeal := by
      have := Ideal.mul_mem_left p.asHomogeneousIdeal.toIdeal (C (c b0)⁻¹) (hp' b b0)
      convert this using 1
      simp only [smul_eq_C_mul, mul_sub, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hb0, C_1, one_mul,
        div_eq_inv_mul]
    have h2 := add_mem (Ideal.mul_mem_right (X b : MvPolynomial ι k) _ hf)
      (Ideal.mul_mem_left p.asHomogeneousIdeal.toIdeal
        (aeval (fun b => (C (c b / c b0) * X b0 : MvPolynomial ι k)) f) hX)
    convert h2 using 1
    simp only [map_mul, aeval_X]
    ring

/-- A form lies in the point of `Proj` cut out by the linear relations `c b' • X b - c b • X b'`
if and only if it vanishes at `c / c b0`. -/
theorem mem_iff_eval_of_homogeneous {ι k : Type*} [Field k] [DecidableEq ι] (c : ι → k) (b0 : ι)
    (hb0 : c b0 ≠ 0)
    (p : ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule ι k))
    (hp : ∀ b b', c b' • (X b : MvPolynomial ι k) - c b • X b' ∈ p.asHomogeneousIdeal)
    {m : ℕ} {f : MvPolynomial ι k} (hf : f.IsHomogeneous m) :
    f ∈ p.asHomogeneousIdeal ↔ eval (fun b => c b / c b0) f = 0 := by
  have h1 := sub_aeval_mem c b0 hb0 p hp f
  rw [aeval_smul_homog _ b0 hf] at h1
  have hX := X_not_mem c b0 hb0 p hp
  have hXm : (X b0 : MvPolynomial ι k) ^ m ∉ p.asHomogeneousIdeal :=
    fun h => hX (p.isPrime.mem_of_pow_mem _ h)
  refine ⟨fun hmem => ?_, fun h0 => ?_⟩
  · by_contra hne
    have : C (eval (fun b => c b / c b0) f) * (X b0 : MvPolynomial ι k) ^ m ∈
        p.asHomogeneousIdeal.toIdeal := by
      simpa using sub_mem (show f ∈ p.asHomogeneousIdeal.toIdeal from hmem) h1
    have h3 := Ideal.mul_mem_left p.asHomogeneousIdeal.toIdeal
      (C (eval (fun b => c b / c b0) f)⁻¹) this
    rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ hne, C_1, one_mul] at h3
    exact hXm h3
  · rw [h0] at h1
    simpa using h1

/-- For `c ≠ 0`, at most one point of `Proj` contains every `c b' • X b - c b • X b'`. -/
theorem projectiveSpectrum_ext_of_linear {ι k : Type*} [Field k] [DecidableEq ι] (c : ι → k)
    (b0 : ι) (hb0 : c b0 ≠ 0)
    (p p' : ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule ι k))
    (hp : ∀ b b', c b' • (X b : MvPolynomial ι k) - c b • X b' ∈ p.asHomogeneousIdeal)
    (hp' : ∀ b b', c b' • (X b : MvPolynomial ι k) - c b • X b' ∈ p'.asHomogeneousIdeal) :
    p = p' := by
  have key : ∀ f : MvPolynomial ι k, f ∈ p.asHomogeneousIdeal ↔ f ∈ p'.asHomogeneousIdeal := by
    intro f
    have hh : ∀ (q : ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule ι k)),
        (∀ b b', c b' • (X b : MvPolynomial ι k) - c b • X b' ∈ q.asHomogeneousIdeal) →
        (f ∈ q.asHomogeneousIdeal ↔
          ∀ m, eval (fun b => c b / c b0) (homogeneousComponent m f) = 0) := by
      intro q hq
      rw [show f ∈ q.asHomogeneousIdeal ↔ f ∈ q.asHomogeneousIdeal.toIdeal from Iff.rfl,
        q.asHomogeneousIdeal.isHomogeneous.mem_iff]
      refine forall_congr' fun m => ?_
      rw [← mem_iff_eval_of_homogeneous c b0 hb0 q hq (homogeneousComponent_isHomogeneous m f)]
      have e : ((DirectSum.decompose (MvPolynomial.homogeneousSubmodule ι k) f m : _) :
          MvPolynomial ι k) = homogeneousComponent m f :=
        MvPolynomial.decomposition.decompose'_apply f m
      rw [e]
      exact Iff.rfl
    rw [hh p hp, hh p' hp']
  exact ProjectiveSpectrum.ext (HomogeneousIdeal.ext (Ideal.ext key))

/-- Over an algebraically closed field, two irreducible polynomials with the same zeros differ by a
nonzero scalar. -/
theorem assoc_of_same_zeros {k σ : Type*} [Field k] [IsAlgClosed k] [Finite σ]
    {G G' : MvPolynomial σ k} (hG : Irreducible G)
    (h : ∀ x : σ → k, eval x G = 0 ↔ eval x G' = 0) (hG' : Irreducible G') :
    ∃ c : kˣ, G' = C (c : k) * G := by
  have key : ∀ {A B : MvPolynomial σ k}, Irreducible A →
      (∀ x : σ → k, eval x A = 0 → eval x B = 0) → A ∣ B := by
    intro A B hA hAB
    have hB : B ∈ vanishingIdeal k (zeroLocus k (Ideal.span {A})) := by
      rw [mem_vanishingIdeal_iff]
      intro x hx
      rw [show (aeval x) B = eval x B from rfl]
      apply hAB
      rw [mem_zeroLocus_iff] at hx
      simpa using hx A (Ideal.subset_span rfl)
    have hp : (Ideal.span {A}).IsPrime := (Ideal.span_singleton_prime hA.ne_zero).mpr hA.prime
    rw [MvPolynomial.IsPrime.vanishingIdeal_zeroLocus] at hB
    exact Ideal.mem_span_singleton.mp hB
  obtain ⟨u, hu⟩ := associated_of_dvd_dvd (key hG fun x hx => (h x).mp hx)
    (key hG' fun x hx => (h x).mpr hx)
  obtain ⟨c, hc⟩ : ∃ c : kˣ, (u : MvPolynomial σ k) = C (c : k) := by
    obtain ⟨r, hrU, hr⟩ := (MvPolynomial.isUnit_iff_eq_C_of_isReduced (R := k)).mp u.isUnit
    exact ⟨hrU.unit, hr⟩
  refine ⟨c, ?_⟩
  rw [← hu, hc]
  ring

/-- Restricting a form of degree `m` to the line `t ↦ t • q` gives `f(q) * t ^ m`. -/
theorem aeval_line_homog {ι k : Type*} [Field k] (q : ι → k) {m : ℕ} {f : MvPolynomial ι k}
    (hf : f.IsHomogeneous m) :
    aeval (fun i => (Polynomial.C (q i) * Polynomial.X : Polynomial k)) f =
      Polynomial.C (eval q f) * Polynomial.X ^ m := by
  rw [aeval_def, eval₂_eq, eval_eq, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hw := hf (mem_support_iff.mp hd)
  have hdeg : ∑ i ∈ d.support, d i = m := by
    simpa [Finsupp.weight_apply, Finsupp.sum] using hw
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg, map_mul,
    map_prod, map_pow]
  simp [Polynomial.C_mul]
  ring

/-- The ideal of polynomials vanishing on the line `t ↦ t • q`. -/
noncomputable def lineIdeal {ι k : Type*} [Field k] (q : ι → k) : Ideal (MvPolynomial ι k) :=
  RingHom.ker (aeval (fun i => (Polynomial.C (q i) * Polynomial.X : Polynomial k)) :
    MvPolynomial ι k →ₐ[k] Polynomial k)

/-- The restriction of `f` to the line `t ↦ t • q` is `∑ m, f_m(q) * t ^ m`, with `f_m` the
homogeneous components of `f`. -/
theorem aeval_line_eq_sum {ι k : Type*} [Field k] (q : ι → k) (f : MvPolynomial ι k) :
    aeval (fun i => (Polynomial.C (q i) * Polynomial.X : Polynomial k)) f =
      ∑ m ∈ Finset.range (f.totalDegree + 1),
        Polynomial.C (eval q (homogeneousComponent m f)) * Polynomial.X ^ m := by
  conv_lhs => rw [← sum_homogeneousComponent f]
  rw [map_sum]
  exact Finset.sum_congr rfl fun m _ => aeval_line_homog q (homogeneousComponent_isHomogeneous m f)

/-- A polynomial vanishes on the line through `q` if and only if each of its homogeneous
components vanishes at `q`. -/
theorem mem_lineIdeal_iff {ι k : Type*} [Field k] (q : ι → k) (f : MvPolynomial ι k) :
    f ∈ lineIdeal q ↔ ∀ m, eval q (homogeneousComponent m f) = 0 := by
  rw [lineIdeal, RingHom.mem_ker, aeval_line_eq_sum]
  refine ⟨fun h m => ?_, fun h => Finset.sum_eq_zero fun m _ => by simp [h m]⟩
  by_cases hm : m < f.totalDegree + 1
  · simpa only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_range, hm, ite_true,
      Polynomial.coeff_zero] using congrArg (fun P => Polynomial.coeff P m) h
  · have : homogeneousComponent m f = 0 := homogeneousComponent_eq_zero _ _ (by omega)
    simp [this]

/-- The linear form `∑ j, w j X_j` vanishes on the line through `q` when `∑ j, w j q j = 0`. -/
theorem sum_C_mul_X_mem_lineIdeal {ι k : Type*} [Fintype ι] [Field k] {q w : ι → k}
    (hw : ∑ j, w j * q j = 0) :
    (∑ j, MvPolynomial.C (w j) * (X j : MvPolynomial ι k)) ∈ lineIdeal q := by
  rw [mem_lineIdeal_iff]
  intro m
  have hh : (∑ j, MvPolynomial.C (w j) * (X j : MvPolynomial ι k)).IsHomogeneous 1 :=
    IsHomogeneous.sum _ _ _ fun j _ => by simpa using (isHomogeneous_X k j).C_mul (w j)
  rw [homogeneousComponent_of_mem hh]
  by_cases hm : m = 1
  · simp [hm, hw]
  · simp [hm]

/-- The ideal of a line through the origin is homogeneous. -/
theorem lineIdeal_isHomogeneous {ι k : Type*} [Field k] [DecidableEq ι] (q : ι → k) :
    (lineIdeal q).IsHomogeneous (MvPolynomial.homogeneousSubmodule ι k) := by
  intro i r hr
  rw [mem_lineIdeal_iff] at hr ⊢
  intro m
  have e : ((DirectSum.decompose (MvPolynomial.homogeneousSubmodule ι k) r i : _) :
      MvPolynomial ι k) = homogeneousComponent i r :=
    MvPolynomial.decomposition.decompose'_apply r i
  rw [e, homogeneousComponent_of_mem (homogeneousComponent_mem i r)]
  by_cases h : m = i
  · subst h
    simpa using hr m
  · simp [h]

/-- For `q ≠ 0`, the ideal of the line through `q` is a point of `Proj`. -/
theorem exists_point_of_line {ι k : Type*} [Field k] [DecidableEq ι] (q : ι → k) (hq : q ≠ 0) :
    ∃ p : ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule ι k),
      ∀ f, f ∈ p.asHomogeneousIdeal ↔ f ∈ lineIdeal q := by
  have hprime : (lineIdeal q).IsPrime := RingHom.ker_isPrime _
  refine ⟨⟨⟨lineIdeal q, lineIdeal_isHomogeneous q⟩, hprime, ?_⟩, fun f => Iff.rfl⟩
  intro hle
  obtain ⟨i, hi⟩ : ∃ i, q i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hq (funext hcon)
  have hX : (X i : MvPolynomial ι k) ∈
      HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule ι k) :=
    HomogeneousIdeal.mem_irrelevant_of_mem _ Nat.one_pos (isHomogeneous_X k i)
  have := hle hX
  rw [show (X i : MvPolynomial ι k) ∈ (⟨lineIdeal q, lineIdeal_isHomogeneous q⟩ :
    HomogeneousIdeal (MvPolynomial.homogeneousSubmodule ι k)) ↔ X i ∈ lineIdeal q from Iff.rfl,
    mem_lineIdeal_iff] at this
  exact hi (by simpa [homogeneousComponent_of_mem (isHomogeneous_X k i)] using this 1)

/-- Over an algebraically closed field, every point of `Proj` has a nonzero common zero. -/
theorem exists_zero_of_prime {ι k : Type*} [Field k] [IsAlgClosed k] [Finite ι]
    [DecidableEq ι] (p : ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule ι k)) :
    ∃ q : ι → k, q ≠ 0 ∧ ∀ f ∈ p.asHomogeneousIdeal, eval q f = 0 := by
  by_contra hcon
  push Not at hcon
  have hp : p.asHomogeneousIdeal.toIdeal.IsPrime := p.isPrime
  have hrad : vanishingIdeal k (zeroLocus k p.asHomogeneousIdeal.toIdeal) =
      p.asHomogeneousIdeal.toIdeal := by
    rw [vanishingIdeal_zeroLocus_eq_radical, hp.radical]
  apply p.not_irrelevant_le
  refine irrelevant_le_span_X.trans (Ideal.span_le.mpr ?_)
  rintro _ ⟨i, rfl⟩
  have : (X i : MvPolynomial ι k) ∈ p.asHomogeneousIdeal.toIdeal := by
    rw [← hrad, mem_vanishingIdeal_iff]
    intro x hx
    rw [mem_zeroLocus_iff] at hx
    by_cases hx0 : x = 0
    · subst hx0; simp
    · exfalso
      obtain ⟨f, hf, hfx⟩ := hcon x hx0
      exact hfx (by simpa using hx f hf)
  exact this

end ProjPts

/-! ### Invariance of fundamental cycles under isomorphism -/

section CycleIso

/-- An isomorphism carries the vanishing ideal of `closure {x}` to that of `closure {e.hom x}`. -/
lemma vanishing_map_iso {X X' : Scheme.{u}} (e : X ≅ X') (x : X) :
    (Scheme.IdealSheafData.vanishingIdeal
        (TopologicalSpace.Closeds.closure ({x} : Set X))).map e.hom =
      Scheme.IdealSheafData.vanishingIdeal
        (TopologicalSpace.Closeds.closure ({e.hom x} : Set X')) := by
  rw [Scheme.IdealSheafData.map_vanishingIdeal]
  congr 1
  ext y
  simp only [TopologicalSpace.Closeds.coe_closure]
  have h1 : (e.hom '' closure ({x} : Set X)) = closure ({e.hom x} : Set X') := by
    have := (Scheme.homeoOfIso e).image_closure ({x} : Set X)
    rw [Set.image_singleton] at this
    exact this
  rw [h1, closure_closure]

/-- An isomorphism `e : X ≅ X'` induces an isomorphism of the reduced closed subschemes
`closure {x}` and `closure {e.hom x}`. -/
noncomputable def curveIso {X X' : Scheme.{u}} (e : X ≅ X') (x : X) :
    Mori.curveSubschemeAt x ≅ Mori.curveSubschemeAt (e.hom x) := by
  have h1 := vanishing_map_iso e x
  have h2 := vanishing_map_iso e.symm (e.hom x)
  have hx : e.symm.hom (e.hom x) = x := by
    rw [← Scheme.Hom.comp_apply]; simp
  rw [hx] at h2
  refine
    { hom := Scheme.IdealSheafData.subschemeMap _ _ e.hom h1.ge
      inv := Scheme.IdealSheafData.subschemeMap _ _ e.symm.hom h2.ge
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · rw [← cancel_mono (Scheme.IdealSheafData.subschemeι _)]
    simp
  · rw [← cancel_mono (Scheme.IdealSheafData.subschemeι _)]
    simp

/-- `curveIso e x` commutes with the closed immersions into `X` and `X'`. -/
@[reassoc]
theorem curveIso_hom_ι {X X' : Scheme.{u}} (e : X ≅ X') (x : X) :
    (curveIso e x).hom ≫ Mori.curveSubschemeAtι (e.hom x) = Mori.curveSubschemeAtι x ≫ e.hom := by
  simp [curveIso]

/-- An isomorphism over `k` carries a point with proper one-dimensional closure to such a point. -/
theorem isProperCurve_iso {k : Type u} [Field k] {X X' : Scheme.{u}} (e : X ≅ X')
    (sX : X ⟶ Spec (.of k)) (sX' : X' ⟶ Spec (.of k)) (hs : e.hom ≫ sX' = sX) (x : X)
    (h : Mori.IsProperCurve sX x) : Mori.IsProperCurve sX' (e.hom x) := by
  refine ⟨?_, ?_⟩
  · rw [← h.dim_eq]
    exact (IsHomeomorph.topologicalKrullDim_eq _ (curveIso e x).hom.homeomorph.isHomeomorph).symm
  · have : Mori.curveSubschemeAtι (e.hom x) ≫ sX' =
        (curveIso e x).inv ≫ Mori.curveSubschemeAtι x ≫ sX := by
      have key : (curveIso e x).inv ≫ Mori.curveSubschemeAtι x ≫ e.hom =
          Mori.curveSubschemeAtι (e.hom x) := by
        rw [← curveIso_hom_ι]; simp
      rw [← hs, ← Category.assoc, ← Category.assoc]
      simp only [Category.assoc]
      rw [← Category.assoc (Mori.curveSubschemeAtι x) e.hom, ← key]
      simp
    rw [this]
    have := h.isProper
    infer_instance

/-- Isomorphic rings have the same length as modules over themselves. -/
theorem length_ringEquiv {R R' : Type*} [CommRing R] [CommRing R'] (f : R' ≃+* R) :
    Module.length R R = Module.length R' R' := by
  letI : Algebra R' R := f.toRingHom.toAlgebra
  have h1 : Module.length R' R = Module.length R R :=
    Module.length_eq_of_surjective (S := R') (R := R) (M := R) f.surjective
  rw [← h1]
  exact (LinearEquiv.length_eq (R := R') (M := R') (N := R)
    { f.toAddEquiv with map_smul' := fun a b => by simp [Algebra.smul_def]; rfl }).symm

/-- Composing a field extension `K → L'` with an isomorphism `L' ≃ L` does not change its
degree. -/
theorem finrank_congr_equiv {K L' L : Type*} [Field K] [Field L'] [Field L] (φ : K →+* L')
    (ψ : L' ≃+* L) :
    @Module.finrank K L _ _ (@Algebra.toModule _ _ _ _ (ψ.toRingHom.comp φ).toAlgebra) =
    @Module.finrank K L' _ _ (@Algebra.toModule _ _ _ _ φ.toAlgebra) := by
  letI := φ.toAlgebra
  letI := (ψ.toRingHom.comp φ).toAlgebra
  let a : L' ≃ₐ[K] L := { ψ with commutes' := fun r => rfl }
  exact (a.toLinearEquiv.finrank_eq).symm

/-- An isomorphism of schemes induces isomorphisms of stalks. -/
theorem stalkMap_isIso_of_iso {X X' : Scheme.{u}} (e : X ≅ X') (x : X) :
    IsIso (e.hom.stalkMap x) :=
  ((IsOpenImmersion.iff_isIso_stalkMap (f := e.hom)).mp inferInstance).2 x

/-- An isomorphism of schemes induces bijections of residue fields. -/
theorem residueFieldMap_bijective_of_iso {X X' : Scheme.{u}} (e : X ≅ X') (x : X) :
    Function.Bijective (e.hom.residueFieldMap x) := by
  have hb : Function.Bijective (e.hom.stalkMap x).hom :=
    (ConcreteCategory.isIso_iff_bijective _).mp (stalkMap_isIso_of_iso e x)
  refine ⟨RingHom.injective _, fun z => ?_⟩
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective z
  obtain ⟨b, rfl⟩ := hb.2 a
  exact ⟨IsLocalRing.residue _ b, IsLocalRing.ResidueField.map_residue _ _⟩

/-- Precomposing with an isomorphism does not change residue field degrees. -/
theorem residueFieldDegree_comp_iso {X X' Y : Scheme.{u}} (e : X ≅ X') (p' : X' ⟶ Y) (x : X) :
    Mori.residueFieldDegree (e.hom ≫ p') x = Mori.residueFieldDegree p' (e.hom x) := by
  unfold Mori.residueFieldDegree
  rw [Scheme.residueFieldMap_comp]
  exact finrank_congr_equiv (p'.residueFieldMap (e.hom x)).hom
    (RingEquiv.ofBijective (e.hom.residueFieldMap x).hom (residueFieldMap_bijective_of_iso e x))

/-- If `closure {e.hom x}` is an irreducible component of `X'`, then `closure {x}` is an
irreducible component of `X`. -/
theorem mem_irreducibleComponents_iso {X X' : Scheme.{u}} (e : X ≅ X') (x : X)
    (h : closure ({e.hom x} : Set X') ∈ irreducibleComponents X') :
    closure ({x} : Set X) ∈ irreducibleComponents X := by
  have hpre : (Scheme.homeoOfIso e) ⁻¹' ({e.hom x} : Set X') = {x} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun h => (Scheme.homeoOfIso e).injective h, fun h => h ▸ rfl⟩
  have hc : closure ({x} : Set X) = e.hom ⁻¹' closure ({e.hom x} : Set X') := by
    have := (Scheme.homeoOfIso e).preimage_closure ({e.hom x} : Set X')
    rw [hpre] at this
    exact this.symm
  rw [hc]
  exact preimage_mem_irreducibleComponents h (Scheme.homeoOfIso e).isOpenEmbedding
    ⟨e.hom x, subset_closure rfl, ⟨x, rfl⟩⟩

/-- `closure {e.hom x}` is an irreducible component of `X'` if and only if `closure {x}` is one
of `X`. -/
theorem mem_irreducibleComponents_iso_iff {X X' : Scheme.{u}} (e : X ≅ X') (x : X) :
    closure ({e.hom x} : Set X') ∈ irreducibleComponents X' ↔
      closure ({x} : Set X) ∈ irreducibleComponents X := by
  refine ⟨mem_irreducibleComponents_iso e x, fun h => ?_⟩
  have hx : e.symm.hom (e.hom x) = x := by
    rw [← Scheme.Hom.comp_apply]
    simp
  exact mem_irreducibleComponents_iso e.symm (e.hom x) (by rwa [hx])

/-- The push-forward of a point along `e.hom ≫ p'` is that of `e.hom x` along `p'`. -/
theorem cyclePushforwardOfPoint_iso {k : Type u} [Field k] {X X' Y : Scheme.{u}} (e : X ≅ X')
    (sY : Y ⟶ Spec (.of k)) (p' : X' ⟶ Y) (x : X) :
    Mori.cyclePushforwardOfPoint ℤ sY (e.hom ≫ p') x =
      Mori.cyclePushforwardOfPoint ℤ sY p' (e.hom x) := by
  unfold Mori.cyclePushforwardOfPoint
  rw [residueFieldDegree_comp_iso]
  rfl

/-- The push-forward along `p` of the fundamental 1-cycle of `X`, the sum of its one-dimensional
irreducible components weighted by the lengths of their local rings. -/
noncomputable def cycleOf {k : Type u} [Field k] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (sY : Y ⟶ Spec (.of k)) (p : X ⟶ Y) : Mori.OneCycle ℤ sY :=
  ∑ᶠ C : {C : Mori.ProperCurve sX // closure {C.point} ∈ irreducibleComponents X},
    ((Module.length (X.presheaf.stalk C.1.point) (X.presheaf.stalk C.1.point)).toNat : ℤ) •
      Mori.cyclePushforwardOfPoint ℤ sY p C.1.point

/-- The push-forward of the fundamental cycle is invariant under isomorphism over `k`. -/
theorem cycleOf_iso {k : Type u} [Field k] {X X' Y : Scheme.{u}} (e : X ≅ X')
    (sX : X ⟶ Spec (.of k)) (sX' : X' ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    (p' : X' ⟶ Y) (hs : e.hom ≫ sX' = sX) :
    cycleOf sX sY (e.hom ≫ p') = cycleOf sX' sY p' := by
  have hs' : e.inv ≫ sX = sX' := by rw [← hs]; simp
  let E : {C : Mori.ProperCurve sX // closure {C.point} ∈ irreducibleComponents X} ≃
      {C : Mori.ProperCurve sX' // closure {C.point} ∈ irreducibleComponents X'} :=
    { toFun := fun C => ⟨⟨e.hom C.1.point, isProperCurve_iso e sX sX' hs _ C.1.isProperCurve⟩,
        (mem_irreducibleComponents_iso_iff e _).mpr C.2⟩
      invFun := fun C => ⟨⟨e.inv C.1.point,
          isProperCurve_iso e.symm sX' sX hs' _ C.1.isProperCurve⟩, by
        have hx : e.hom (e.inv C.1.point) = C.1.point := by
          rw [← Scheme.Hom.comp_apply]
          simp
        exact (mem_irreducibleComponents_iso_iff e (e.inv C.1.point)).mp (by rw [hx]; exact C.2)⟩
      left_inv := fun C => by
        apply Subtype.ext
        apply Mori.ProperCurve.ext
        simp
      right_inv := fun C => by
        apply Subtype.ext
        apply Mori.ProperCurve.ext
        simp }
  unfold cycleOf
  rw [← finsum_comp_equiv E]
  refine finsum_congr fun C => ?_
  have hlen : Module.length (X.presheaf.stalk C.1.point) (X.presheaf.stalk C.1.point) =
      Module.length (X'.presheaf.stalk (E C).1.point) (X'.presheaf.stalk (E C).1.point) :=
    length_ringEquiv (haveI := stalkMap_isIso_of_iso e C.1.point
      asIso (e.hom.stalkMap C.1.point)).commRingCatIsoToRingEquiv
  rw [hlen, cyclePushforwardOfPoint_iso]
  rfl

end CycleIso

/-! ### Skeleton -/

/-- The incidence relation of the affine cone of a prime `𝔭` with two linear forms. -/
def ConeInc (𝔭 : Ideal (MvPolynomial (Fin (N + 1)) k)) (u v : Fin (N + 1) → k) : Prop :=
  ∃ q : Fin (N + 1) → k, q ≠ 0 ∧ (∀ f ∈ 𝔭, eval q f = 0) ∧ (∑ j, u j * q j = 0) ∧
    (∑ j, v j * q j = 0)

/-- Scheme points of `closure {x}` through two hyperplanes are the same as nonzero points of the
affine cone through them (Nullstellensatz). -/
theorem incForm_of_cone (C : Mori.ProperCurve (projToSpecCoeff k N))
    (G : MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k) (hG : Irreducible G)
    (h : ∀ u v : Fin (N + 1) → k, eval (Sum.elim u v) G = 0 ↔
      ConeInc (C.point.asHomogeneousIdeal.toIdeal) u v) : IncForm C G := by
  classical
  refine ⟨hG, fun u v => (h u v).trans ?_⟩
  constructor
  · rintro ⟨q, hq0, hq𝔭, hu, hv⟩
    obtain ⟨p, hp⟩ := exists_point_of_line q hq0
    refine ⟨p, ?_, (hp _).mpr (sum_C_mul_X_mem_lineIdeal hu),
      (hp _).mpr (sum_C_mul_X_mem_lineIdeal hv)⟩
    refine (ProjectiveSpectrum.le_iff_mem_closure
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) C.point p).mp ?_
    intro f hf
    show f ∈ p.asHomogeneousIdeal
    rw [hp, mem_lineIdeal_iff]
    intro m
    have e : ((DirectSum.decompose (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) f m : _) :
        MvPolynomial (Fin (N + 1)) k) = homogeneousComponent m f :=
      MvPolynomial.decomposition.decompose'_apply f m
    exact hq𝔭 _ (e ▸ C.point.asHomogeneousIdeal.isHomogeneous m hf)
  · rintro ⟨p, hpc, hu, hv⟩
    have hpc := (ProjectiveSpectrum.le_iff_mem_closure
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) C.point p).mpr hpc
    obtain ⟨q, hq0, hq⟩ := exists_zero_of_prime p
    exact ⟨q, hq0, fun f hf => hq f (hpc hf), by simpa using hq _ hu, by simpa using hq _ hv⟩

/-- Dimension of the affine cone in terms of the closure of the point. -/
theorem ringKrullDim_cone_of_closure (x : ProjectiveSpectrum
    (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k))
    (hx : topologicalKrullDim (closure ({x} : Set (ProjectiveSpectrum
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)))) = 1) :
    ringKrullDim (MvPolynomial (Fin (N + 1)) k ⧸ x.asHomogeneousIdeal.toIdeal) = 2 := by
  classical
  have hZ : (ProjectiveSpectrum.zeroLocus (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)
      (x.asHomogeneousIdeal.toIdeal : Set (MvPolynomial (Fin (N + 1)) k))) =
      closure ({x} : Set (ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule
        (Fin (N + 1)) k))) := by
    ext y
    rw [(ProjectiveSpectrum.le_iff_mem_closure _ x y).symm, ProjectiveSpectrum.mem_zeroLocus]
    exact Iff.rfl
  have hne : (ProjectiveSpectrum.zeroLocus (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)
      (x.asHomogeneousIdeal.toIdeal : Set (MvPolynomial (Fin (N + 1)) k))).Nonempty :=
    ⟨x, by rw [ProjectiveSpectrum.mem_zeroLocus]; exact fun f hf => hf⟩
  haveI : x.asHomogeneousIdeal.toIdeal.IsPrime := x.isPrime
  have h1 := Stacks.ProjectiveSpace.topologicalKrullDim_projectiveSpectrum_zeroLocus_add_one
    (x.asHomogeneousIdeal.toIdeal) x.asHomogeneousIdeal.isHomogeneous hne
  rw [hZ, hx] at h1
  rw [← h1]
  exact one_add_one_eq_two

/-- The affine cone of a proper curve has dimension two. -/
theorem ringKrullDim_properCurve (C : Mori.ProperCurve (projToSpecCoeff k N)) :
    ringKrullDim (MvPolynomial (Fin (N + 1)) k ⧸ C.point.asHomogeneousIdeal.toIdeal) = 2 := by
  refine ringKrullDim_cone_of_closure C.point ?_
  have hrange : Set.range (Mori.curveSubschemeAtι C.point) =
      closure ({C.point} : Set (AlgebraicGeometry.Proj (polyGrading k N))) := by
    unfold Mori.curveSubschemeAtι
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  rw [← C.dim_eq]
  exact IsHomeomorph.topologicalKrullDim_eq _
    ((Mori.curveSubschemeAtι C.point).isClosedEmbedding.isEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr hrange)).isHomeomorph

/-! ### Elimination: the incidence locus is closed -/

/-- The degree `n + 1` component of `a * X j` is the degree `n` component of `a` times `X j`. -/
theorem homogeneousComponent_mul_X {σ k : Type*} [CommSemiring k] (a : MvPolynomial σ k) (j : σ)
    (n : ℕ) :
    homogeneousComponent (n + 1) (a * X j) = homogeneousComponent n a * X j := by
  classical
  ext d
  rw [coeff_homogeneousComponent, coeff_mul_X', coeff_mul_X']
  by_cases hj : j ∈ d.support
  · simp only [hj, ite_true]
    rw [coeff_homogeneousComponent]
    have hle : Finsupp.single j 1 ≤ d := by
      rw [Finsupp.single_le_iff]; exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hj)
    have hdeg : d.degree = (d - Finsupp.single j 1).degree + 1 := by
      conv_lhs => rw [← tsub_add_cancel_of_le hle]
      rw [map_add, Finsupp.degree_single]
    rw [hdeg]
    simp
  · simp [hj]

/-- If no nonzero point of the cone lies on both hyperplanes, a power of the maximal ideal of the
origin lies in `𝔭 + (ℓu, ℓv)`. -/
theorem exists_monomial_mem {k : Type*} [Field k] [IsAlgClosed k] {n : ℕ} [NeZero n]
    (𝔭 : Ideal (MvPolynomial (Fin n) k)) (u v : Fin n → k)
    (hno : ¬ ∃ q : Fin n → k, q ≠ 0 ∧ (∀ f ∈ 𝔭, eval q f = 0) ∧ (∑ j, u j * q j = 0) ∧
      (∑ j, v j * q j = 0)) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ α : Fin n →₀ ℕ, α.degree = D →
      (monomial α (1 : k)) ∈ 𝔭 ⊔ Ideal.span {∑ j, C (u j) * (X j : MvPolynomial (Fin n) k),
        ∑ j, C (v j) * (X j : MvPolynomial (Fin n) k)} := by
  set J := 𝔭 ⊔ Ideal.span {∑ j, C (u j) * (X j : MvPolynomial (Fin n) k),
        ∑ j, C (v j) * (X j : MvPolynomial (Fin n) k)} with hJ
  have hX : ∀ i, ∃ m : ℕ, 1 ≤ m ∧ (X i : MvPolynomial (Fin n) k) ^ m ∈ J := by
    intro i
    have h1 : (X i : MvPolynomial (Fin n) k) ∈ vanishingIdeal k (zeroLocus k J) := by
      rw [mem_vanishingIdeal_iff]
      intro q hq
      rw [mem_zeroLocus_iff] at hq
      by_cases hq0 : q = 0
      · subst hq0; simp
      · exfalso
        apply hno
        refine ⟨q, hq0, fun f hf => ?_, ?_, ?_⟩
        · simpa using hq f (Ideal.mem_sup_left hf)
        · simpa using hq _ (Ideal.mem_sup_right (Ideal.subset_span (Set.mem_insert _ _)))
        · simpa using hq _ (Ideal.mem_sup_right (Ideal.subset_span
            (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
    rw [vanishingIdeal_zeroLocus_eq_radical] at h1
    obtain ⟨m, hm⟩ := h1
    refine ⟨m + 1, by omega, ?_⟩
    rw [pow_succ]
    exact J.mul_mem_right _ hm
  choose m hm1 hmJ using hX
  refine ⟨∑ i, m i, ?_, ?_⟩
  · exact (hm1 0).trans
      (Finset.single_le_sum (f := m) (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0))
  · intro α hα
    obtain ⟨i, hi⟩ : ∃ i, m i ≤ α i := by
      by_contra hcon
      push Not at hcon
      have : α.degree < ∑ i, m i := by
        rw [Finsupp.degree_eq_sum]
        exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i _ => hcon i)
      omega
    have hle : Finsupp.single i (m i) ≤ α := by
      rwa [Finsupp.single_le_iff]
    have : (monomial α (1 : k)) = (X i) ^ (m i) * monomial (α - Finsupp.single i (m i)) 1 := by
      rw [X_pow_eq_monomial, monomial_mul, one_mul, add_tsub_cancel_of_le hle]
    rw [this]
    exact J.mul_mem_right _ (hmJ i)

/-- The degree `n + 1` component of `a * ℓ`, for a linear form `ℓ`, is the degree `n` component of
`a` times `ℓ`. -/
theorem homogeneousComponent_mul_linear {σ k : Type*} [CommSemiring k] [Fintype σ] (w : σ → k)
    (a : MvPolynomial σ k) (n : ℕ) :
    homogeneousComponent (n + 1) (a * ∑ j, C (w j) * (X j : MvPolynomial σ k)) =
      homogeneousComponent n a * ∑ j, C (w j) * (X j : MvPolynomial σ k) := by
  simp only [Finset.mul_sum, map_sum, mul_left_comm a (C _), homogeneousComponent_C_mul,
    homogeneousComponent_mul_X]
  simp [Finset.mul_sum, mul_left_comm]

/-- For a homogeneous ideal `𝔭`, a monomial of degree `D' + 1` in `𝔭 + (ℓu, ℓv)` is congruent
modulo `𝔭` to `a * ℓu + b * ℓv` with `a` and `b` forms of degree `D'`. -/
theorem exists_hom_refine {k : Type*} [Field k] {n : ℕ}
    (𝔭 : Ideal (MvPolynomial (Fin n) k))
    (h𝔭 : 𝔭.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) k))
    (u v : Fin n → k) (D' : ℕ) (α : Fin n →₀ ℕ) (hα : α.degree = D' + 1)
    (hmem : (monomial α (1 : k)) ∈ 𝔭 ⊔ Ideal.span {∑ j, C (u j) * (X j : MvPolynomial (Fin n) k),
        ∑ j, C (v j) * (X j : MvPolynomial (Fin n) k)}) :
    ∃ a b : MvPolynomial (Fin n) k, a.IsHomogeneous D' ∧ b.IsHomogeneous D' ∧
      monomial α (1 : k) - a * (∑ j, C (u j) * (X j : MvPolynomial (Fin n) k)) -
        b * (∑ j, C (v j) * (X j : MvPolynomial (Fin n) k)) ∈ 𝔭 := by
  classical
  obtain ⟨p, hp, y, hy, hpy⟩ := Submodule.mem_sup.mp hmem
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hy
  refine ⟨homogeneousComponent D' a, homogeneousComponent D' b,
    homogeneousComponent_isHomogeneous _ _, homogeneousComponent_isHomogeneous _ _, ?_⟩
  have hD := congrArg (homogeneousComponent (D' + 1)) hpy
  rw [← hab, map_add, map_add, homogeneousComponent_mul_linear,
    homogeneousComponent_mul_linear,
    homogeneousComponent_of_mem (isHomogeneous_monomial _ hα)] at hD
  simp only [if_true] at hD
  have hpD : homogeneousComponent (D' + 1) p ∈ 𝔭 := by
    have e : ((DirectSum.decompose (MvPolynomial.homogeneousSubmodule (Fin n) k) p (D' + 1) : _) :
        MvPolynomial (Fin n) k) = homogeneousComponent (D' + 1) p :=
      MvPolynomial.decomposition.decompose'_apply p (D' + 1)
    exact e ▸ h𝔭 (D' + 1) hp
  have : monomial α (1 : k) -
      homogeneousComponent D' a * ∑ j, C (u j) * (X j : MvPolynomial (Fin n) k)
      - homogeneousComponent D' b * ∑ j, C (v j) * (X j : MvPolynomial (Fin n) k) =
      homogeneousComponent (D' + 1) p := by
    rw [← hD]
    ring
  rwa [this]

section Nak

variable {k : Type*} [Field k] [IsAlgClosed k] {n : ℕ} [NeZero n]

/-- If no nonzero point of the cone of the homogeneous ideal `𝔭` lies on both hyperplanes
`(u0, v0)`, some polynomial in `(u, v)` equals `1` at `(u0, v0)` and vanishes at every pair of
hyperplanes meeting the cone away from the origin. -/
theorem exists_witness (𝔭 : Ideal (MvPolynomial (Fin n) k))
    (h𝔭 : 𝔭.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) k)) (u0 v0 : Fin n → k)
    (hno : ¬ ∃ q : Fin n → k, q ≠ 0 ∧ (∀ f ∈ 𝔭, eval q f = 0) ∧ (∑ j, u0 j * q j = 0) ∧
      (∑ j, v0 j * q j = 0)) :
    ∃ r : MvPolynomial (Fin n ⊕ Fin n) k, eval (Sum.elim u0 v0) r = 1 ∧
      ∀ u v q : Fin n → k, q ≠ 0 → (∀ f ∈ 𝔭, eval q f = 0) → (∑ j, u j * q j = 0) →
        (∑ j, v j * q j = 0) → eval (Sum.elim u v) r = 0 := by
  classical
  obtain ⟨D, hD1, hDmem⟩ := exists_monomial_mem 𝔭 u0 v0 hno
  obtain ⟨D', rfl⟩ : ∃ D', D = D' + 1 := ⟨D - 1, by omega⟩
  let R := MvPolynomial (Fin n ⊕ Fin n) k
  let S := MvPolynomial (Fin n) R
  let φ : MvPolynomial (Fin n) k →+* S := MvPolynomial.map (C : k →+* R)
  let h1 : S := ∑ j, C (X (Sum.inl j)) * X j
  let h2 : S := ∑ j, C (X (Sum.inr j)) * X j
  let 𝔞 : Ideal S := Ideal.map φ 𝔭 ⊔ Ideal.span {h1, h2}
  let m : Ideal R := RingHom.ker (eval (Sum.elim u0 v0) : R →+* k)
  let gen : {α : Fin n →₀ ℕ // α.degree = D' + 1} → S ⧸ 𝔞 := fun α =>
    Ideal.Quotient.mk 𝔞 (monomial α.1 (1 : R))
  let N : Submodule R (S ⧸ 𝔞) := Submodule.span R (Set.range gen)
  have hfin : Finite {α : Fin n →₀ ℕ // α.degree = D' + 1} := by
    have := Finsupp.finite_of_nat_weight_eq (σ := Fin n) (fun _ => 1) (fun _ => one_ne_zero)
      (D' + 1)
    simp only [Finsupp.degree_eq_weight_one]
    exact this.to_subtype
  have hfg : N.FG := Submodule.fg_span (Set.finite_range gen)
  have hgenN : ∀ γ : Fin n →₀ ℕ, γ.degree = D' + 1 → Ideal.Quotient.mk 𝔞 (monomial γ (1 : R)) ∈ N :=
    fun γ hγ => Submodule.subset_span ⟨⟨γ, hγ⟩, rfl⟩
  have hmulX : ∀ (a : MvPolynomial (Fin n) k), a.IsHomogeneous D' → ∀ j : Fin n,
      Ideal.Quotient.mk 𝔞 (φ a * X j) ∈ N := by
    intro a ha j
    rw [a.as_sum, map_sum, Finset.sum_mul, map_sum]
    refine Submodule.sum_mem _ fun β hβ => ?_
    have hdeg : β.degree = D' := by
      have := ha (mem_support_iff.mp hβ)
      rwa [Finsupp.degree_eq_weight_one]
    have hdeg' : (β + Finsupp.single j 1).degree = D' + 1 := by
      rw [map_add, Finsupp.degree_single, hdeg]
    have e1 : φ (monomial β (a.coeff β)) * X j =
        C (C (a.coeff β)) * monomial (β + Finsupp.single j 1) (1 : R) := by
      have e0 : φ (monomial β (a.coeff β)) = monomial β (C (a.coeff β)) :=
        MvPolynomial.map_monomial _ _ _
      rw [e0, MvPolynomial.X, monomial_mul_monomial, mul_one, C_mul_monomial, mul_one]
    rw [e1]
    have : Ideal.Quotient.mk 𝔞 (C (C (a.coeff β)) * monomial (β + Finsupp.single j 1) (1 : R)) =
        (C (a.coeff β) : R) • Ideal.Quotient.mk 𝔞 (monomial (β + Finsupp.single j 1) (1 : R)) := by
      rw [← MvPolynomial.smul_eq_C_mul]; rfl
    rw [this]
    exact Submodule.smul_mem _ _ (hgenN _ hdeg')
  have hterm : ∀ (a : MvPolynomial (Fin n) k), a.IsHomogeneous D' → ∀ (w : Fin n → k)
      (x : Fin n → R), (∀ j, C (w j) - x j ∈ m) → (∑ j, C (x j) * X j : S) ∈ 𝔞 →
      Ideal.Quotient.mk 𝔞 (φ a * φ (∑ j, C (w j) * (X j : MvPolynomial (Fin n) k))) ∈ m • N := by
    intro a ha w x hxm hxA
    have e1 : φ a * φ (∑ j, C (w j) * (X j : MvPolynomial (Fin n) k)) =
        φ a * (∑ j, C (C (w j) - x j) * X j : S) + φ a * (∑ j, C (x j) * X j : S) := by
      rw [← mul_add, ← Finset.sum_add_distrib]
      congr 1
      simp only [φ, map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.map_X, map_sub]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [MvPolynomial.map_C, MvPolynomial.map_X]
      ring
    rw [e1, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_mem_left 𝔞 _ hxA), add_zero,
      Finset.mul_sum, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    have : Ideal.Quotient.mk 𝔞 (φ a * (C (C (w j) - x j) * X j)) =
        (C (w j) - x j) • Ideal.Quotient.mk 𝔞 (φ a * X j) := by
      rw [show φ a * (C (C (w j) - x j) * X j) = C (C (w j) - x j) * (φ a * X j) by ring,
        ← MvPolynomial.smul_eq_C_mul]
      rfl
    rw [this]
    exact Submodule.smul_mem_smul (hxm j) (hmulX a ha j)
  have hin : N ≤ m • N := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨⟨α, hα⟩, rfl⟩
    obtain ⟨a, b, ha, hb, hE⟩ := exists_hom_refine 𝔭 h𝔭 u0 v0 D' α hα (hDmem α hα)
    have hE' : φ (monomial α (1 : k) - a * (∑ j, C (u0 j) * (X j : MvPolynomial (Fin n) k)) -
        b * (∑ j, C (v0 j) * (X j : MvPolynomial (Fin n) k))) ∈ 𝔞 :=
      Ideal.mem_sup_left (Ideal.mem_map_of_mem φ hE)
    have hgen : gen ⟨α, hα⟩ =
        Ideal.Quotient.mk 𝔞 (φ a * φ (∑ j, C (u0 j) * (X j : MvPolynomial (Fin n) k))) +
        Ideal.Quotient.mk 𝔞 (φ b * φ (∑ j, C (v0 j) * (X j : MvPolynomial (Fin n) k))) := by
      have h0 := Ideal.Quotient.eq_zero_iff_mem.mpr hE'
      have e : (monomial α (1 : R) : S) = φ (monomial α (1 : k)) := by
        rw [show φ (monomial α (1 : k)) = monomial α (C 1) from MvPolynomial.map_monomial _ _ _,
          C_1]
      show Ideal.Quotient.mk 𝔞 (monomial α (1 : R)) = _
      rw [e]
      simp only [map_sub, map_mul] at h0 ⊢
      linear_combination h0
    rw [hgen]
    refine add_mem (hterm a ha u0 (fun j => X (Sum.inl j)) (fun j => ?_)
      (Ideal.mem_sup_right (Ideal.subset_span (Set.mem_insert _ _)))) (hterm b hb v0
      (fun j => X (Sum.inr j)) (fun j => ?_)
      (Ideal.mem_sup_right (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))))
    · show eval (Sum.elim u0 v0) (C (u0 j) - X (Sum.inl j)) = 0
      simp
    · show eval (Sum.elim u0 v0) (C (v0 j) - X (Sum.inr j)) = 0
      simp
  obtain ⟨r, hr1, hr0⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m N hfg hin
  refine ⟨r, ?_, ?_⟩
  · have : eval (Sum.elim u0 v0) (r - 1) = 0 := hr1
    simpa [sub_eq_zero] using this
  · intro u v q hq0 hq𝔭 hu hv
    let ev : R →+* k := eval (Sum.elim u v)
    let ψ : S →+* k := MvPolynomial.eval₂Hom ev q
    have hψC : ∀ r : R, ψ (C r) = ev r := fun r => by
      show eval₂ ev q (C r) = _
      rw [eval₂_C]
    have hψX : ∀ j, ψ (X j) = q j := fun j => by
      show eval₂ ev q (X j) = _
      rw [eval₂_X]
    have hψφ : ψ.comp φ = (eval q : MvPolynomial (Fin n) k →+* k) := by
      apply MvPolynomial.ringHom_ext
      · intro a
        show ψ (φ (C a)) = _
        rw [show φ (C a) = C (C a) from MvPolynomial.map_C _ _, hψC]
        show eval (Sum.elim u v) (C a) = eval q (C a)
        rw [eval_C, eval_C]
      · intro j
        show ψ (φ (X j)) = _
        rw [show φ (X j) = X j from MvPolynomial.map_X _ _, hψX]
        simp
    have hψ𝔞 : 𝔞 ≤ RingHom.ker ψ := by
      refine sup_le ?_ ?_
      · rw [Ideal.map_le_iff_le_comap]
        intro f hf
        show ψ (φ f) = 0
        have := congrArg (fun g => g f) hψφ
        simp only [RingHom.comp_apply] at this
        rw [this]
        exact hq𝔭 f hf
      · refine Ideal.span_le.mpr ?_
        intro x hx
        rcases hx with rfl | rfl
        · show ψ (∑ j, C (X (Sum.inl j)) * X j) = 0
          simp only [map_sum, map_mul, hψC, hψX]
          exact (Finset.sum_congr rfl fun x _ => by rw [MvPolynomial.eval_X]; rfl).trans hu
        · show ψ (∑ j, C (X (Sum.inr j)) * X j) = 0
          simp only [map_sum, map_mul, hψC, hψX]
          exact (Finset.sum_congr rfl fun x _ => by rw [MvPolynomial.eval_X]; rfl).trans hv
    let Ψ : S ⧸ 𝔞 →+* k := Ideal.Quotient.lift 𝔞 ψ (fun x hx => hψ𝔞 hx)
    obtain ⟨i, hi⟩ : ∃ i, q i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hq0 (funext hcon)
    have h0 := hr0 _ (hgenN (Finsupp.single i (D' + 1)) (by simp))
    have h2 := congrArg Ψ h0
    have e : r • Ideal.Quotient.mk 𝔞 (monomial (Finsupp.single i (D' + 1)) (1 : R)) =
        Ideal.Quotient.mk 𝔞 (C r * monomial (Finsupp.single i (D' + 1)) (1 : R)) := by
      rw [← MvPolynomial.smul_eq_C_mul]; rfl
    rw [e] at h2
    have h3 : ψ (C r * monomial (Finsupp.single i (D' + 1)) (1 : R)) = 0 := h2
    rw [map_mul, hψC] at h3
    have h4 : ψ (monomial (Finsupp.single i (D' + 1)) (1 : R)) = q i ^ (D' + 1) := by
      show eval₂ ev q _ = _
      rw [eval₂_monomial, Finsupp.prod_single_index (by simp)]
      simp [ev]
    rw [h4] at h3
    exact (mul_eq_zero.mp h3).resolve_right (pow_ne_zero _ hi)

end Nak

/-- The incidence locus in `k^{2(N+1)}`. -/
def incSet (𝔭 : Ideal (MvPolynomial (Fin (N + 1)) k)) :
    Set (Fin (N + 1) ⊕ Fin (N + 1) → k) :=
  {x | ConeInc 𝔭 (fun j => x (Sum.inl j)) (fun j => x (Sum.inr j))}

/-- The ideal of the incidence locus. -/
noncomputable def incIdeal (𝔭 : Ideal (MvPolynomial (Fin (N + 1)) k)) :
    Ideal (MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k) :=
  vanishingIdeal k (incSet 𝔭)

section PrimeIdeal

variable (𝔭 : Ideal (MvPolynomial (Fin (N + 1)) k)) [𝔭.IsPrime]

/-- The homogeneous coordinate ring `k[x_0, …, x_N] / 𝔭` of the cone. -/
abbrev Aq := MvPolynomial (Fin (N + 1)) k ⧸ 𝔭

/-- The class of the variable `x_i` in `Aq 𝔭`. -/
noncomputable def xq (i : Fin (N + 1)) : Aq 𝔭 := Ideal.Quotient.mk 𝔭 (X i)

/-- The localization of `Aq 𝔭` at `x_j`. -/
abbrev Aj (j : Fin (N + 1)) := Localization.Away (xq 𝔭 j)

/-- The structure map `k → Aq 𝔭`. -/
noncomputable def kapA : k →+* Aq 𝔭 := (Ideal.Quotient.mk 𝔭).comp C

/-- The structure map `k → Aj 𝔭 j`. -/
noncomputable def kapJ (j : Fin (N + 1)) : k →+* Aj 𝔭 j :=
  (algebraMap (Aq 𝔭) (Aj 𝔭 j)).comp (kapA 𝔭)

/-- The ratio `x_i / x_j` in `Aj 𝔭 j`. -/
noncomputable def sJ (j i : Fin (N + 1)) : Aj 𝔭 j :=
  algebraMap (Aq 𝔭) (Aj 𝔭 j) (xq 𝔭 i) * IsLocalization.Away.invSelf (xq 𝔭 j)

/-- The chart map on the `j`-th chart, substituting the ratios `x_i / x_j` into a polynomial in
`(u, v)`. -/
noncomputable def PhiJ (j : Fin (N + 1)) :=
  chartMap (kapJ 𝔭 j) j (sJ 𝔭 j)

/-- Evaluation `Aq 𝔭 → k` at a zero `q` of `𝔭`. -/
noncomputable def evA (q : Fin (N + 1) → k) (hq : ∀ f ∈ 𝔭, eval q f = 0) : Aq 𝔭 →+* k :=
  Ideal.Quotient.lift 𝔭 (eval q) hq

/-- Evaluation `Aj 𝔭 j → k` at a zero `q` of `𝔭` with `q j ≠ 0`. -/
noncomputable def evJ (q : Fin (N + 1) → k) (hq : ∀ f ∈ 𝔭, eval q f = 0) (j : Fin (N + 1))
    (hj : q j ≠ 0) : Aj 𝔭 j →+* k :=
  IsLocalization.Away.lift (xq 𝔭 j) (g := evA 𝔭 q hq) (by
    simpa [evA, xq] using Ne.isUnit hj)

/-- `evJ` restricts to `evA` on `Aq 𝔭`. -/
theorem evJ_alg (q : Fin (N + 1) → k) (hq : ∀ f ∈ 𝔭, eval q f = 0) (j : Fin (N + 1))
    (hj : q j ≠ 0) (a : Aq 𝔭) : evJ 𝔭 q hq j hj (algebraMap (Aq 𝔭) (Aj 𝔭 j) a) = evA 𝔭 q hq a := by
  simp [evJ]

/-- `evJ` is the identity on constants. -/
theorem evJ_kapJ (q : Fin (N + 1) → k) (hq : ∀ f ∈ 𝔭, eval q f = 0) (j : Fin (N + 1))
    (hj : q j ≠ 0) (r : k) : evJ 𝔭 q hq j hj (kapJ 𝔭 j r) = r := by
  simp [kapJ, kapA, evJ_alg, evA]

/-- `evJ` sends the ratio `x_i / x_j` to `q i / q j`. -/
theorem evJ_sJ (q : Fin (N + 1) → k) (hq : ∀ f ∈ 𝔭, eval q f = 0) (j : Fin (N + 1))
    (hj : q j ≠ 0) (i : Fin (N + 1)) : evJ 𝔭 q hq j hj (sJ 𝔭 j i) = q i / q j := by
  have h1 : evJ 𝔭 q hq j hj (IsLocalization.Away.invSelf (xq 𝔭 j)) = (q j)⁻¹ := by
    have := IsLocalization.Away.mul_invSelf (S := Aj 𝔭 j) (xq 𝔭 j)
    have h2 := congrArg (evJ 𝔭 q hq j hj) this
    rw [map_mul, evJ_alg, map_one] at h2
    simp only [evA, xq, Ideal.Quotient.lift_mk, RingHom.coe_coe, eval_X] at h2
    exact eq_inv_of_mul_eq_one_right h2
  rw [sJ, map_mul, evJ_alg, h1]
  simp [evA, xq, div_eq_mul_inv]

/-- If `PhiJ 𝔭 j f = 0`, then `f` vanishes at every pair of hyperplanes through a zero `q` of `𝔭`
with `q j ≠ 0`. -/
theorem PhiJ_forward (j : Fin (N + 1)) (f : MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k)
    (hf : PhiJ 𝔭 j f = 0) (q : Fin (N + 1) → k) (hq : ∀ f ∈ 𝔭, eval q f = 0) (hj : q j ≠ 0)
    (w : Fin (N + 1) ⊕ Fin (N + 1) → k) (hu : ∑ l, w (Sum.inl l) * q l = 0)
    (hv : ∑ l, w (Sum.inr l) * q l = 0) : eval w f = 0 := by
  have := eval_map_chartMap (kapJ 𝔭 j) (evJ 𝔭 q hq j hj) (evJ_kapJ 𝔭 q hq j hj) j (sJ 𝔭 j)
    (fun l => q l / q j) (evJ_sJ 𝔭 q hq j hj) w f
  change eval w (map _ (PhiJ 𝔭 j f)) = _ at this
  rw [hf, map_zero, map_zero, chartPt_of_orth j q hj w hu hv] at this
  exact this.symm

/-- For `x_j ∉ 𝔭`, an element of `Aj 𝔭 j` killed by every evaluation `evJ` is zero. -/
theorem eq_zero_of_evJ (j : Fin (N + 1)) (hx : (X j : MvPolynomial (Fin (N + 1)) k) ∉ 𝔭)
    (c : Aj 𝔭 j)
    (h : ∀ (q : Fin (N + 1) → k) (hq : ∀ f ∈ 𝔭, eval q f = 0) (hj : q j ≠ 0),
      evJ 𝔭 q hq j hj c = 0) : c = 0 := by
  obtain ⟨n, a, hna⟩ := IsLocalization.Away.surj (S := Aj 𝔭 j) (xq 𝔭 j) c
  obtain ⟨a0, rfl⟩ := Ideal.Quotient.mk_surjective a
  have h1 : a0 * X j ∈ 𝔭 := by
    have h2 : a0 * X j ∈ vanishingIdeal k (zeroLocus k 𝔭) := by
      rw [mem_vanishingIdeal_iff]
      intro q hq
      rw [mem_zeroLocus_iff] at hq
      have hq' : ∀ f ∈ 𝔭, eval q f = 0 := fun f hf => by simpa using hq f hf
      by_cases hj : q j = 0
      · simp [hj]
      · have h3 := congrArg (evJ 𝔭 q hq' j hj) hna
        rw [map_mul, h q hq' hj, zero_mul, evJ_alg] at h3
        have h4 : eval q a0 = 0 := by
          simpa [evA] using h3.symm
        simp [h4]
    rwa [vanishingIdeal_zeroLocus_eq_radical, Ideal.IsPrime.radical (I := 𝔭) inferInstance] at h2
  have h5 : a0 ∈ 𝔭 := (Ideal.IsPrime.mem_or_mem inferInstance h1).resolve_right hx
  have h6 : (Ideal.Quotient.mk 𝔭 a0 : Aq 𝔭) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr h5
  rw [h6, map_zero] at hna
  have hu : IsUnit (algebraMap (Aq 𝔭) (Aj 𝔭 j) (xq 𝔭 j) ^ n) :=
    (IsLocalization.Away.algebraMap_isUnit (xq 𝔭 j)).pow n
  exact (hu.mul_left_eq_zero).mp hna

/-- For `x_j ∉ 𝔭`, the chart map `PhiJ 𝔭 j` kills the ideal of the incidence locus. -/
theorem PhiJ_eq_zero_of_mem (j : Fin (N + 1)) (hx : (X j : MvPolynomial (Fin (N + 1)) k) ∉ 𝔭)
    (f : MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k) (hf : f ∈ incIdeal 𝔭) :
    PhiJ 𝔭 j f = 0 := by
  ext m
  rw [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  refine eq_zero_of_evJ 𝔭 j hx _ fun q hq hj => ?_
  have hmap : map (evJ 𝔭 q hq j hj) (PhiJ 𝔭 j f) = 0 := by
    refine MvPolynomial.funext fun w => ?_
    have := eval_map_chartMap (kapJ 𝔭 j) (evJ 𝔭 q hq j hj) (evJ_kapJ 𝔭 q hq j hj) j (sJ 𝔭 j)
      (fun l => q l / q j) (evJ_sJ 𝔭 q hq j hj) w f
    change eval w (map _ (PhiJ 𝔭 j f)) = _ at this
    rw [this, map_zero]
    have hmem : chartPt j (fun l => q l / q j) w ∈ incSet 𝔭 := by
      refine ⟨q, fun h => hj (by simp [h]), hq, ?_⟩
      exact (chartPt_orth j q hj w)
    simpa using (mem_vanishingIdeal_iff.mp hf) _ hmem
  simpa [coeff_map] using congrArg (fun g => g.coeff m) hmap

section Transfer

/-- The class of `x_j` is nonzero if and only if `x_j ∉ 𝔭`. -/
theorem xq_ne_zero_iff (j : Fin (N + 1)) :
    xq 𝔭 j ≠ 0 ↔ (X j : MvPolynomial (Fin (N + 1)) k) ∉ 𝔭 := by
  rw [xq, Ne, Ideal.Quotient.eq_zero_iff_mem]

/-- The embedding of `Aj 𝔭 j` into the fraction field of `Aq 𝔭`, for `x_j ≠ 0`. -/
noncomputable def iotaJ (j : Fin (N + 1)) (hx : xq 𝔭 j ≠ 0) :
    Aj 𝔭 j →+* FractionRing (Aq 𝔭) :=
  IsLocalization.Away.lift (xq 𝔭 j) (g := algebraMap (Aq 𝔭) (FractionRing (Aq 𝔭)))
    (isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _
      (IsFractionRing.injective (Aq 𝔭) (FractionRing (Aq 𝔭)))).mpr hx))

/-- `iotaJ` restricts to the canonical map `Aq 𝔭 → FractionRing (Aq 𝔭)`. -/
theorem iotaJ_alg (j : Fin (N + 1)) (hx : xq 𝔭 j ≠ 0) (a : Aq 𝔭) :
    iotaJ 𝔭 j hx (algebraMap (Aq 𝔭) (Aj 𝔭 j) a) = algebraMap (Aq 𝔭) (FractionRing (Aq 𝔭)) a := by
  simp [iotaJ]

/-- `iotaJ` is injective. -/
theorem iotaJ_injective (j : Fin (N + 1)) (hx : xq 𝔭 j ≠ 0) :
    Function.Injective (iotaJ 𝔭 j hx) := by
  refine (IsLocalization.lift_injective_iff (M := Submonoid.powers (xq 𝔭 j)) _).mpr ?_
  intro x y
  refine ⟨fun h => by simpa [iotaJ_alg] using congrArg (iotaJ 𝔭 j hx) h, fun h => ?_⟩
  rw [IsFractionRing.injective (Aq 𝔭) (FractionRing (Aq 𝔭)) h]

/-- `iotaJ` sends `1 / x_j` to the inverse of `x_j` in the fraction field. -/
theorem iotaJ_invSelf (j : Fin (N + 1)) (hx : xq 𝔭 j ≠ 0) :
    iotaJ 𝔭 j hx (IsLocalization.Away.invSelf (xq 𝔭 j)) =
      (algebraMap (Aq 𝔭) (FractionRing (Aq 𝔭)) (xq 𝔭 j))⁻¹ := by
  have := IsLocalization.Away.mul_invSelf (S := Aj 𝔭 j) (xq 𝔭 j)
  have h2 := congrArg (iotaJ 𝔭 j hx) this
  rw [map_mul, iotaJ_alg, map_one] at h2
  exact eq_inv_of_mul_eq_one_right h2

/-- The structure map from `k` to the fraction field of `Aq 𝔭`. -/
noncomputable def kapK : k →+* FractionRing (Aq 𝔭) :=
  (algebraMap (Aq 𝔭) (FractionRing (Aq 𝔭))).comp (kapA 𝔭)

/-- The image of `x_i` in the fraction field of `Aq 𝔭`. -/
noncomputable def xK (i : Fin (N + 1)) : FractionRing (Aq 𝔭) :=
  algebraMap (Aq 𝔭) (FractionRing (Aq 𝔭)) (xq 𝔭 i)

/-- The image of `x_j` in the fraction field is nonzero when `x_j` is. -/
theorem xK_ne_zero (j : Fin (N + 1)) (hx : xq 𝔭 j ≠ 0) : xK 𝔭 j ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective (Aq 𝔭) (FractionRing (Aq 𝔭)))).mpr hx

/-- Followed by `iotaJ`, the chart map `PhiJ 𝔭 j` is the chart map over the fraction field with
the ratios `xK i / xK j`. -/
theorem map_iota_PhiJ (j : Fin (N + 1)) (hx : xq 𝔭 j ≠ 0)
    (f : MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k) :
    map (iotaJ 𝔭 j hx) (PhiJ 𝔭 j f) = chartMap (kapK 𝔭) j (fun i => xK 𝔭 i * (xK 𝔭 j)⁻¹) f := by
  have := RingHom.congr_fun (map_chartMap (iotaJ 𝔭 j hx) (kapJ 𝔭 j) j (sJ 𝔭 j)) f
  have e1 : (iotaJ 𝔭 j hx).comp (kapJ 𝔭 j) = kapK 𝔭 := by
    ext r; simp [kapJ, kapK, iotaJ_alg]
  have e2 : (iotaJ 𝔭 j hx) ∘ (sJ 𝔭 j) = fun i => xK 𝔭 i * (xK 𝔭 j)⁻¹ := by
    funext i
    simp [sJ, iotaJ_alg, iotaJ_invSelf, xK]
  rwa [e1, e2] at this

/-- If `x_{j0}` and `x_j` are nonzero, the kernel of `PhiJ 𝔭 j0` lies in that of `PhiJ 𝔭 j`. -/
theorem PhiJ_transfer (j0 j : Fin (N + 1)) (hj : j ≠ j0) (h0 : xq 𝔭 j0 ≠ 0) (h1 : xq 𝔭 j ≠ 0)
    (f : MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k) (hf : PhiJ 𝔭 j0 f = 0) : PhiJ 𝔭 j f = 0 := by
  have a := map_iota_PhiJ 𝔭 j0 h0 f
  rw [hf, map_zero] at a
  have b := RingHom.congr_fun (eval₂Hom_chartSub_comp_chartMap (kapK 𝔭) j0 j (xK 𝔭) hj
    (xK_ne_zero 𝔭 j0 h0) (xK_ne_zero 𝔭 j h1)) f
  simp only [RingHom.comp_apply] at b
  rw [← a, map_zero] at b
  have c := map_iota_PhiJ 𝔭 j h1 f
  rw [← b] at c
  exact (MvPolynomial.map_injective _ (iotaJ_injective 𝔭 j h1)) (by rw [c, map_zero])

/-- For `x_{j0} ∉ 𝔭`, the ideal of the incidence locus is the kernel of the chart map
`PhiJ 𝔭 j0`. -/
theorem incIdeal_eq_ker (j0 : Fin (N + 1)) (hx0 : (X j0 : MvPolynomial (Fin (N + 1)) k) ∉ 𝔭) :
    incIdeal 𝔭 = RingHom.ker (PhiJ 𝔭 j0) := by
  ext f
  rw [RingHom.mem_ker]
  refine ⟨PhiJ_eq_zero_of_mem 𝔭 j0 hx0 f, fun hf => ?_⟩
  · rw [incIdeal, mem_vanishingIdeal_iff]
    rintro x ⟨q, hq0, hq, hu, hv⟩
    obtain ⟨j, hj⟩ : ∃ j, q j ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hq0 (funext hcon)
    have hxj : (X j : MvPolynomial (Fin (N + 1)) k) ∉ 𝔭 := fun hm => hj (by simpa using hq _ hm)
    have hf' : PhiJ 𝔭 j f = 0 := by
      by_cases hjj : j = j0
      · exact hjj ▸ hf
      · exact PhiJ_transfer 𝔭 j0 j hjj ((xq_ne_zero_iff 𝔭 j0).mpr hx0)
          ((xq_ne_zero_iff 𝔭 j).mpr hxj) f hf
    simpa using PhiJ_forward 𝔭 j f hf' q hq hj x hu hv

/-- A prime not containing the irrelevant ideal omits some variable. -/
theorem exists_notMem_X (hirr : ¬ (HomogeneousIdeal.irrelevant
    (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)).toIdeal ≤ 𝔭) :
    ∃ j, (X j : MvPolynomial (Fin (N + 1)) k) ∉ 𝔭 := by
  by_contra hcon
  push Not at hcon
  exact hirr (irrelevant_le_span_X.trans (Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hcon i)))

/-- For a prime not containing the irrelevant ideal, the ideal of the incidence locus is prime. -/
theorem incIdeal_isPrime (hirr : ¬ (HomogeneousIdeal.irrelevant
    (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)).toIdeal ≤ 𝔭) : (incIdeal 𝔭).IsPrime := by
  obtain ⟨j0, hx0⟩ := exists_notMem_X 𝔭 hirr
  rw [incIdeal_eq_ker 𝔭 j0 hx0]
  haveI : IsDomain (Aj 𝔭 j0) :=
    IsLocalization.isDomain_localization (M := Submonoid.powers (xq 𝔭 j0))
      (powers_le_nonZeroDivisors_of_noZeroDivisors ((xq_ne_zero_iff 𝔭 j0).mpr hx0))
  exact RingHom.ker_isPrime _

end Transfer

/-- The scaling `x_i ↦ c * x_i` of the variables. -/
noncomputable def scal (c : k) : MvPolynomial (Fin (N + 1)) k →ₐ[k] MvPolynomial (Fin (N + 1)) k :=
  aeval (fun i => C c * X i)

/-- Scaling the variables by `c` multiplies a form of degree `m` by `c ^ m`. -/
theorem scal_homogeneous (c : k) {m : ℕ} {g : MvPolynomial (Fin (N + 1)) k}
    (hg : g.IsHomogeneous m) :
    scal c g = C (c ^ m) * g := by
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdm : d.degree = m := by
    have := hg (mem_support_iff.mp hd)
    rwa [Finsupp.degree_eq_weight_one]
  simp only [scal, aeval_monomial, algebraMap_eq]
  rw [monomial_eq]
  simp only [mul_pow, Finsupp.prod_mul, ← C_pow]
  have : (d.prod fun i e => C (c ^ e) : MvPolynomial (Fin (N + 1)) k) = C (c ^ m) := by
    rw [Finsupp.prod, ← hdm, Finsupp.degree_eq_sum]
    simp [Finset.prod_pow_eq_pow_sum]
    congr 1
    exact Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => by simpa using hi)
  rw [this]; ring

/-- A homogeneous ideal is stable under scaling of the variables. -/
theorem scal_mem (h𝔭 : 𝔭.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k))
    (c : k) {f : MvPolynomial (Fin (N + 1)) k} (hf : f ∈ 𝔭) : scal c f ∈ 𝔭 := by
  rw [← sum_homogeneousComponent f, map_sum]
  refine Ideal.sum_mem _ fun m _ => ?_
  rw [scal_homogeneous c (homogeneousComponent_isHomogeneous m f)]
  refine Ideal.mul_mem_left _ _ ?_
  have e : ((DirectSum.decompose (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) f m : _) :
      MvPolynomial (Fin (N + 1)) k) = homogeneousComponent m f :=
    MvPolynomial.decomposition.decompose'_apply f m
  exact e ▸ h𝔭 m hf

/-- The scaling of `Aq 𝔭` induced by `x_i ↦ c * x_i`, for `𝔭` homogeneous. -/
noncomputable def scA (h𝔭 : 𝔭.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k))
    (c : k) : Aq 𝔭 →ₐ[k] Aq 𝔭 :=
  Ideal.Quotient.liftₐ 𝔭 ((Ideal.Quotient.mkₐ k 𝔭).comp (scal c)) (fun f hf => by
    simpa using Ideal.Quotient.eq_zero_iff_mem.mpr (scal_mem 𝔭 h𝔭 c hf))

/-- The scaling `scA 𝔭 h𝔭 c` sends `x_i` to `c • x_i`. -/
theorem scA_xq (h𝔭 : 𝔭.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k))
    (c : k) (i : Fin (N + 1)) : scA 𝔭 h𝔭 c (xq 𝔭 i) = c • xq 𝔭 i := by
  have h1 : scA 𝔭 h𝔭 c (Ideal.Quotient.mk 𝔭 (X i)) = Ideal.Quotient.mk 𝔭 (scal c (X i)) := rfl
  rw [xq, h1]
  change Ideal.Quotient.mkₐ k 𝔭 (scal c (X i)) = c • Ideal.Quotient.mkₐ k 𝔭 (X i)
  rw [← map_smul]
  congr 1
  simp [scal, smul_eq_C_mul]

variable (h𝔭 : 𝔭.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k))

/-- `kapJ 𝔭 j` is the algebra map `k → Aj 𝔭 j`. -/
theorem kapJ_eq (j : Fin (N + 1)) (r : k) : kapJ 𝔭 j r = algebraMap k (Aj 𝔭 j) r := by
  rw [IsScalarTower.algebraMap_apply k (Aq 𝔭) (Aj 𝔭 j)]
  rfl

/-- The scaling of `Aj 𝔭 j` induced by `x_i ↦ c * x_i`, for `c ≠ 0`. -/
noncomputable def sclJ (j : Fin (N + 1)) (c : k) (hc : c ≠ 0) : Aj 𝔭 j →ₐ[k] Aj 𝔭 j :=
  IsLocalization.liftAlgHom (M := Submonoid.powers (xq 𝔭 j))
    (f := (IsScalarTower.toAlgHom k (Aq 𝔭) (Aj 𝔭 j)).comp (scA 𝔭 h𝔭 c)) (by
      rintro ⟨y, m, rfl⟩
      simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', map_pow, scA_xq 𝔭 h𝔭]
      refine IsUnit.pow _ ?_
      have : algebraMap (Aq 𝔭) (Aj 𝔭 j) (c • xq 𝔭 j) =
          c • algebraMap (Aq 𝔭) (Aj 𝔭 j) (xq 𝔭 j) :=
        _root_.map_smul (IsScalarTower.toAlgHom k (Aq 𝔭) (Aj 𝔭 j)) c _
      rw [this, Algebra.smul_def]
      exact ((IsUnit.mk0 c hc).map (algebraMap k (Aj 𝔭 j))).mul
        (IsLocalization.Away.algebraMap_isUnit (xq 𝔭 j)))

/-- `sclJ` restricts to `scA` on `Aq 𝔭`. -/
theorem sclJ_alg (j : Fin (N + 1)) (c : k) (hc : c ≠ 0) (a : Aq 𝔭) :
    sclJ 𝔭 h𝔭 j c hc (algebraMap (Aq 𝔭) (Aj 𝔭 j) a) =
      algebraMap (Aq 𝔭) (Aj 𝔭 j) (scA 𝔭 h𝔭 c a) := by
  simp [sclJ]

/-- `(x_i / x_j) * x_j = x_i` in `Aj 𝔭 j`. -/
theorem sJ_mul_x (j i : Fin (N + 1)) :
    sJ 𝔭 j i * algebraMap (Aq 𝔭) (Aj 𝔭 j) (xq 𝔭 j) = algebraMap (Aq 𝔭) (Aj 𝔭 j) (xq 𝔭 i) := by
  rw [sJ, mul_assoc, mul_comm (IsLocalization.Away.invSelf _), IsLocalization.Away.mul_invSelf,
    mul_one]

/-- The localization map `Aq 𝔭 → Aj 𝔭 j` is `k`-linear. -/
theorem alg_smul (j : Fin (N + 1)) (c : k) (a : Aq 𝔭) :
    algebraMap (Aq 𝔭) (Aj 𝔭 j) (c • a) = c • algebraMap (Aq 𝔭) (Aj 𝔭 j) a :=
  _root_.map_smul (IsScalarTower.toAlgHom k (Aq 𝔭) (Aj 𝔭 j)) c a

/-- `sclJ` sends `x_j` to `c • x_j`. -/
theorem sclJ_x (j : Fin (N + 1)) (c : k) (hc : c ≠ 0) :
    sclJ 𝔭 h𝔭 j c hc (algebraMap (Aq 𝔭) (Aj 𝔭 j) (xq 𝔭 j)) =
      c • algebraMap (Aq 𝔭) (Aj 𝔭 j) (xq 𝔭 j) := by
  rw [sclJ_alg, scA_xq, alg_smul]

/-- `sclJ` fixes the ratios `x_i / x_j`. -/
theorem sclJ_sJ (j i : Fin (N + 1)) (c : k) (hc : c ≠ 0) :
    sclJ 𝔭 h𝔭 j c hc (sJ 𝔭 j i) = sJ 𝔭 j i := by
  have hu : IsUnit (c • algebraMap (Aq 𝔭) (Aj 𝔭 j) (xq 𝔭 j)) := by
    rw [Algebra.smul_def]
    exact ((IsUnit.mk0 c hc).map (algebraMap k (Aj 𝔭 j))).mul
      (IsLocalization.Away.algebraMap_isUnit (xq 𝔭 j))
  have h1 := congrArg (sclJ 𝔭 h𝔭 j c hc) (sJ_mul_x 𝔭 j i)
  rw [map_mul, sclJ_x, sclJ_alg, scA_xq] at h1
  have h2 : algebraMap (Aq 𝔭) (Aj 𝔭 j) (c • xq 𝔭 i) =
      sJ 𝔭 j i * (c • algebraMap (Aq 𝔭) (Aj 𝔭 j) (xq 𝔭 j)) := by
    rw [alg_smul, ← sJ_mul_x 𝔭 j i, mul_smul_comm]
  rw [h2] at h1
  exact (hu.mul_left_inj).mp h1

/-- The subalgebra generated by the ratios `x_i / x_j`. -/
noncomputable def ratioAlg (j : Fin (N + 1)) : Subalgebra k (Aj 𝔭 j) :=
  Algebra.adjoin k (Set.range (sJ 𝔭 j))

/-- `sclJ` fixes the subalgebra `ratioAlg 𝔭 j` generated by the ratios. -/
theorem sclJ_fix (j : Fin (N + 1)) (c : k) (hc : c ≠ 0) (b : Aj 𝔭 j) (hb : b ∈ ratioAlg 𝔭 j) :
    sclJ 𝔭 h𝔭 j c hc b = b := by
  have : ratioAlg 𝔭 j ≤ AlgHom.equalizer (sclJ 𝔭 h𝔭 j c hc) (AlgHom.id k _) := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨i, rfl⟩
    exact sclJ_sJ 𝔭 h𝔭 j i c hc
  exact this hb

include h𝔭 in
/-- For `x_j ≠ 0`, the element `x_j` of `Aj 𝔭 j` is transcendental over `ratioAlg 𝔭 j`. -/
theorem x_transcendental (j : Fin (N + 1)) (hx : xq 𝔭 j ≠ 0) :
    Transcendental (ratioAlg 𝔭 j) (algebraMap (Aq 𝔭) (Aj 𝔭 j) (xq 𝔭 j)) := by
  haveI : IsDomain (Aj 𝔭 j) :=
    IsLocalization.isDomain_localization (M := Submonoid.powers (xq 𝔭 j))
      (powers_le_nonZeroDivisors_of_noZeroDivisors hx)
  intro ⟨p, hp0, hp⟩
  set x := algebraMap (Aq 𝔭) (Aj 𝔭 j) (xq 𝔭 j) with hxdef
  have hroot : ∀ c : k, c ≠ 0 → (p.map (algebraMap (ratioAlg 𝔭 j) (Aj 𝔭 j))).IsRoot (c • x) := by
    intro c hc
    let σ : Aj 𝔭 j →ₐ[ratioAlg 𝔭 j] Aj 𝔭 j :=
      { toRingHom := (sclJ 𝔭 h𝔭 j c hc).toRingHom
        commutes' := fun b => sclJ_fix 𝔭 h𝔭 j c hc b b.2 }
    have h1 : Polynomial.aeval (σ x) p = σ (Polynomial.aeval x p) :=
      Polynomial.aeval_algHom_apply σ x p
    have h2 : σ x = c • x := sclJ_x 𝔭 h𝔭 j c hc
    rw [hp, map_zero, h2] at h1
    rwa [Polynomial.IsRoot, Polynomial.eval_map]
  have hne : p.map (algebraMap (ratioAlg 𝔭 j) (Aj 𝔭 j)) ≠ 0 := by
    rwa [Ne, Polynomial.map_eq_zero_iff Subtype.val_injective]
  refine hne (Polynomial.eq_zero_of_infinite_isRoot _ ?_)
  have hinf : ({c : k | c ≠ 0}).Infinite :=
    Set.infinite_univ.diff (Set.finite_singleton 0) |>.mono fun c hc => by simpa using hc
  have hunit : IsUnit x := IsLocalization.Away.algebraMap_isUnit (xq 𝔭 j)
  refine (Set.Infinite.image (f := fun c : k => c • x) ?_ hinf).mono ?_
  · intro a _ b _ hab
    have : algebraMap k (Aj 𝔭 j) a * x = algebraMap k (Aj 𝔭 j) b * x := by
      simpa only [Algebra.smul_def] using hab
    exact (algebraMap k (Aj 𝔭 j)).injective (hunit.mul_left_inj.mp this)
  · rintro _ ⟨c, hc, rfl⟩
    exact hroot c hc

/-- If `Aq 𝔭` has dimension two, its fraction field has transcendence degree two over `k`. -/
theorem trdeg_K (hdim : ringKrullDim (Aq 𝔭) = 2) :
    Cardinal.toENat (Algebra.trdeg k (FractionRing (Aq 𝔭))) = 2 := by
  haveI : Algebra.FiniteType k (Aq 𝔭) := inferInstance
  have := (ringKrullDim_eq_trdeg_and_ringKrullDim_localization_eq_trdeg.{_, _, _, 0} k (Aq 𝔭)
    (FractionRing (Aq 𝔭))).1
  rw [hdim] at this
  have h2 : ((2 : ℕ∞) : WithBot ℕ∞) =
      (Cardinal.toENat (Algebra.trdeg k (FractionRing (Aq 𝔭))) : WithBot ℕ∞) := this
  exact (WithBot.coe_injective h2).symm

/-- The embedding `iotaJ` as a `k`-algebra map. -/
noncomputable def iotaAlg (j : Fin (N + 1)) (hx : xq 𝔭 j ≠ 0) :
    Aj 𝔭 j →ₐ[k] FractionRing (Aq 𝔭) :=
  IsLocalization.liftAlgHom (M := Submonoid.powers (xq 𝔭 j))
    (f := IsScalarTower.toAlgHom k (Aq 𝔭) (FractionRing (Aq 𝔭))) (by
      rintro ⟨y, m, rfl⟩
      have hu : IsUnit (algebraMap (Aq 𝔭) (FractionRing (Aq 𝔭)) (xq 𝔭 j)) :=
        isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _
          (IsFractionRing.injective (Aq 𝔭) (FractionRing (Aq 𝔭)))).mpr hx)
      simpa using hu.pow m)

include h𝔭 in
/-- If `Aq 𝔭` has dimension two, the subalgebra `ratioAlg 𝔭 j` has transcendence degree at
most one. -/
theorem trdeg_ratioAlg_le (hdim : ringKrullDim (Aq 𝔭) = 2) (j : Fin (N + 1)) (hx : xq 𝔭 j ≠ 0) :
    Cardinal.toENat (Algebra.trdeg k (ratioAlg 𝔭 j)) ≤ 1 := by
  haveI : IsDomain (Aj 𝔭 j) :=
    IsLocalization.isDomain_localization (M := Submonoid.powers (xq 𝔭 j))
      (powers_le_nonZeroDivisors_of_noZeroDivisors hx)
  have htr := x_transcendental 𝔭 h𝔭 j hx
  have hinj : Function.Injective
      ((Polynomial.aeval (algebraMap (Aq 𝔭) (Aj 𝔭 j) (xq 𝔭 j)) :
        Polynomial (ratioAlg 𝔭 j) →ₐ[ratioAlg 𝔭 j] Aj 𝔭 j).restrictScalars k) :=
    transcendental_iff_injective.mp htr
  have e1 : Algebra.trdeg k (Polynomial (ratioAlg 𝔭 j)) ≤ Algebra.trdeg k (Aj 𝔭 j) :=
    trdeg_le_of_injective _ hinj
  have e2 : Algebra.trdeg k (Aj 𝔭 j) ≤ Algebra.trdeg k (FractionRing (Aq 𝔭)) :=
    trdeg_le_of_injective (iotaAlg 𝔭 j hx) (iotaJ_injective 𝔭 j hx)
  haveI : Nontrivial (ratioAlg 𝔭 j) := inferInstance
  haveI : FaithfulSMul k (ratioAlg 𝔭 j) :=
    (faithfulSMul_iff_algebraMap_injective k (ratioAlg 𝔭 j)).mpr
      (algebraMap k (ratioAlg 𝔭 j)).injective
  haveI : FaithfulSMul (ratioAlg 𝔭 j) (Polynomial (ratioAlg 𝔭 j)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr Polynomial.C_injective
  have e3 := trdeg_add_eq k (ratioAlg 𝔭 j) (A := Polynomial (ratioAlg 𝔭 j))
  rw [Polynomial.trdeg_of_isDomain] at e3
  have e4 := OrderHomClass.mono Cardinal.toENat (e1.trans e2)
  rw [← e3, map_add, map_one, trdeg_K 𝔭 hdim] at e4
  have : Cardinal.toENat (Algebra.trdeg k (ratioAlg 𝔭 j)) + 1 ≤ 1 + 1 := by
    simpa [one_add_one_eq_two] using e4
  exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp this

section Psi

variable (j0 : Fin (N + 1))

/-- The variables other than `u_{j0}`, `v_{j0}`. -/
abbrev Idx' := {a : Fin (N + 1) ⊕ Fin (N + 1) // a ≠ Sum.inl j0 ∧ a ≠ Sum.inr j0}

/-- The variable `a` of `MvPolynomial (Idx' j0) (ratioAlg 𝔭 j0)`, or `0` for
`a = u_{j0}, v_{j0}`. -/
noncomputable def varI (a : Fin (N + 1) ⊕ Fin (N + 1)) :
    MvPolynomial (Idx' j0) (ratioAlg 𝔭 j0) :=
  if h : a ≠ Sum.inl j0 ∧ a ≠ Sum.inr j0 then X ⟨a, h⟩ else 0

/-- The ratio `x_i / x_{j0}` as an element of `ratioAlg 𝔭 j0`. -/
noncomputable def sB (i : Fin (N + 1)) : ratioAlg 𝔭 j0 :=
  ⟨sJ 𝔭 j0 i, Algebra.subset_adjoin ⟨i, rfl⟩⟩

/-- The substitution `u_{j0} ↦ -∑_{l ≠ j0} (x_l / x_{j0}) u_l` and
`v_{j0} ↦ -∑_{l ≠ j0} (x_l / x_{j0}) v_l`, fixing the other variables. -/
noncomputable def gPsi : Fin (N + 1) ⊕ Fin (N + 1) → MvPolynomial (Idx' j0) (ratioAlg 𝔭 j0)
  | Sum.inl i => if i = j0 then -∑ l ∈ Finset.univ.erase j0, C (sB 𝔭 j0 l) * varI 𝔭 j0 (Sum.inl l)
      else varI 𝔭 j0 (Sum.inl i)
  | Sum.inr i => if i = j0 then -∑ l ∈ Finset.univ.erase j0, C (sB 𝔭 j0 l) * varI 𝔭 j0 (Sum.inr l)
      else varI 𝔭 j0 (Sum.inr i)

/-- The `k`-algebra map given by the substitution `gPsi`. -/
noncomputable def psi :
    MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k →ₐ[k] MvPolynomial (Idx' j0) (ratioAlg 𝔭 j0) :=
  aeval (gPsi 𝔭 j0)

/-- The inclusion of `MvPolynomial (Idx' j0) (ratioAlg 𝔭 j0)` into polynomials in all the
variables over `Aj 𝔭 j0`. -/
noncomputable def embM :
    MvPolynomial (Idx' j0) (ratioAlg 𝔭 j0) →+* MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) (Aj 𝔭 j0) :=
  (rename (Subtype.val : Idx' j0 → _)).toRingHom.comp (map (ratioAlg 𝔭 j0).val.toRingHom)

/-- `embM` is injective. -/
theorem embM_injective : Function.Injective (embM 𝔭 j0) :=
  (rename_injective _ Subtype.val_injective).comp
    (MvPolynomial.map_injective _ Subtype.val_injective)

/-- `embM` sends the variable `varI 𝔭 j0 a` to `X a`. -/
theorem embM_varI (a : Fin (N + 1) ⊕ Fin (N + 1)) (h : a ≠ Sum.inl j0 ∧ a ≠ Sum.inr j0) :
    embM 𝔭 j0 (varI 𝔭 j0 a) = X a := by
  simp [embM, varI, h]

/-- `embM` sends a constant `b` to the constant `b`. -/
theorem embM_C (b : ratioAlg 𝔭 j0) : embM 𝔭 j0 (C b) = C (b : Aj 𝔭 j0) := by
  simp [embM]

/-- `embM` sends each substituted variable to the corresponding value of `chartAux`. -/
theorem embM_gPsi (e : Fin (N + 1) → Fin (N + 1) ⊕ Fin (N + 1))
    (he : ∀ l, l ≠ j0 → e l ≠ Sum.inl j0 ∧ e l ≠ Sum.inr j0) (i : Fin (N + 1)) :
    embM 𝔭 j0 (if i = j0 then -∑ l ∈ Finset.univ.erase j0, C (sB 𝔭 j0 l) * varI 𝔭 j0 (e l)
      else varI 𝔭 j0 (e i)) = chartAux e j0 (sJ 𝔭 j0) i := by
  haveI : AddMonoidHomClass (MvPolynomial (Idx' j0) (ratioAlg 𝔭 j0) →+*
      MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) (Aj 𝔭 j0)) (MvPolynomial (Idx' j0) (ratioAlg 𝔭 j0))
      (MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) (Aj 𝔭 j0)) :=
    RingHomClass.toAddMonoidHomClass
  by_cases h : i = j0
  · rw [if_pos h, chartAux, if_pos h, RingHom.map_neg]
    have hsum : embM 𝔭 j0 (∑ l ∈ Finset.univ.erase j0, C (sB 𝔭 j0 l) * varI 𝔭 j0 (e l)) =
        ∑ l ∈ Finset.univ.erase j0, C (sJ 𝔭 j0 l) * (X (e l) : MvPolynomial _ (Aj 𝔭 j0)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun l hl => ?_
      rw [map_mul, embM_C, embM_varI 𝔭 j0 _ (he l (Finset.ne_of_mem_erase hl))]
      rfl
    rw [hsum]
  · rw [if_neg h, chartAux, if_neg h, embM_varI 𝔭 j0 _ (he i h)]

/-- `psi` followed by `embM` is the chart map `PhiJ 𝔭 j0`. -/
theorem embM_psi (f : MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k) :
    embM 𝔭 j0 (psi 𝔭 j0 f) = PhiJ 𝔭 j0 f := by
  rcases subsingleton_or_nontrivial (Aj 𝔭 j0) with hsub | hnt
  · haveI : Subsingleton (MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) (Aj 𝔭 j0)) :=
      inferInstance
    exact Subsingleton.elim _ _
  haveI : Nontrivial (MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) (Aj 𝔭 j0)) :=
    MvPolynomial.nontrivial_of_nontrivial _ _
  have : (embM 𝔭 j0).comp (psi 𝔭 j0 : _ →+* _) = PhiJ 𝔭 j0 := by
    refine ringHom_ext (fun r => ?_) (fun a => ?_)
    · simp [psi,PhiJ, chartMap, embM, kapJ_eq]
    · rcases a with i | i
      · have := embM_gPsi 𝔭 j0 Sum.inl (fun l hl => ⟨fun h => hl (Sum.inl_injective h), by simp⟩) i
        simpa [psi,PhiJ, chartMap, chartSub, gPsi] using this
      · have := embM_gPsi 𝔭 j0 Sum.inr (fun l hl => ⟨by simp, fun h => hl (Sum.inr_injective h)⟩) i
        simpa [psi,PhiJ, chartMap, chartSub, gPsi] using this
  exact RingHom.congr_fun this f

end Psi

/-- Over an algebraically closed field, an algebraic element of a domain is a constant. -/
theorem mem_range_of_isAlgebraic {K : Type*} [Ring K] [IsDomain K] [Algebra k K] (y : K)
    (h : IsAlgebraic k y) : y ∈ Set.range (algebraMap k K) := by
  have hi : IsIntegral k y := h.isIntegral
  refine ⟨-(minpoly k y).coeff 0, ?_⟩
  have hq : (minpoly k y).leadingCoeff = 1 := minpoly.monic hi
  have h1 : (minpoly k y).degree = 1 :=
    IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hi)
  have : Polynomial.aeval y (minpoly k y) = 0 := minpoly.aeval k y
  rw [Polynomial.eq_X_add_C_of_degree_eq_one h1, hq, Polynomial.C_1, one_mul, map_add,
    Polynomial.aeval_X, Polynomial.aeval_C, add_eq_zero_iff_eq_neg] at this
  rw [map_neg]
  exact this.symm

section EvalGen

variable {n : ℕ} {T : Type*} [CommRing T]

/-- The point `w` with `u_j` and `v_j` replaced by `-∑_{l ≠ j} s l * u_l` and
`-∑_{l ≠ j} s l * v_l`. -/
noncomputable def chartPtT (j : Fin n) (s : Fin n → T) (w : Fin n ⊕ Fin n → T) :
    Fin n ⊕ Fin n → T
  | Sum.inl i => if i = j then -∑ l ∈ Finset.univ.erase j, s l * w (Sum.inl l) else w (Sum.inl i)
  | Sum.inr i => if i = j then -∑ l ∈ Finset.univ.erase j, s l * w (Sum.inr l) else w (Sum.inr i)

/-- Evaluating `chartMap κ j s f` at `w` is evaluating `f` at `chartPtT j s w`. -/
theorem eval_chartMap (κ : k →+* T) (j : Fin n) (s : Fin n → T) (w : Fin n ⊕ Fin n → T)
    (f : MvPolynomial (Fin n ⊕ Fin n) k) :
    eval w (chartMap κ j s f) = eval₂ κ (chartPtT j s w) f := by
  have : (eval w).comp (chartMap κ j s) = eval₂Hom κ (chartPtT j s w) := by
    refine ringHom_ext (fun r => ?_) (fun i => ?_)
    · simp [chartMap]
    · rcases i with i | i <;> by_cases h : i = j <;>
        simp [chartMap, chartSub, chartAux, chartPtT, h, map_sum]
  exact RingHom.congr_fun this f

end EvalGen

/-- If `Aq 𝔭` has dimension two and `x_j ≠ 0`, some ratio `x_l / x_j` is not a constant. -/
theorem exists_notMem_range (hdim : ringKrullDim (Aq 𝔭) = 2) (j : Fin (N + 1))
    (hx : xq 𝔭 j ≠ 0) : ∃ l, sJ 𝔭 j l ∉ Set.range (algebraMap k (Aj 𝔭 j)) := by
  by_contra hcon
  push Not at hcon
  have hinj : Function.Injective (algebraMap (Aq 𝔭) (Aj 𝔭 j)) :=
    IsLocalization.injective (Aj 𝔭 j) (powers_le_nonZeroDivisors_of_noZeroDivisors hx)
  have hl : ∀ l, ∃ r : k, xq 𝔭 l = r • xq 𝔭 j := by
    intro l
    obtain ⟨r, hr⟩ := hcon l
    refine ⟨r, hinj ?_⟩
    rw [alg_smul, ← sJ_mul_x 𝔭 j l, ← hr, Algebra.smul_def]
  have hsurj : Function.Surjective (Polynomial.aeval (xq 𝔭 j) : Polynomial k →ₐ[k] Aq 𝔭) := by
    intro a
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
    induction f using MvPolynomial.induction_on with
    | C r => exact ⟨Polynomial.C r, by simp <;> rfl⟩
    | add p q hp hq =>
      obtain ⟨p', hp'⟩ := hp
      obtain ⟨q', hq'⟩ := hq
      exact ⟨p' + q', by simp [hp', hq']⟩
    | mul_X p l hp =>
      obtain ⟨p', hp'⟩ := hp
      obtain ⟨r, hr⟩ := hl l
      refine ⟨p' * (Polynomial.C r * Polynomial.X), ?_⟩
      simp only [map_mul, hp', Polynomial.aeval_C, Polynomial.aeval_X]
      rw [show Ideal.Quotient.mk 𝔭 (X l) = xq 𝔭 l from rfl, hr]
      congr 1
      exact (Algebra.smul_def r (xq 𝔭 j)).symm
  have h1 := ringKrullDim_le_of_surjective
    (Polynomial.aeval (xq 𝔭 j) : Polynomial k →ₐ[k] Aq 𝔭).toRingHom hsurj
  rw [hdim, Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field] at h1
  norm_num at h1

section Lower

variable (j0 : Fin (N + 1))

/-- The variables other than `v_{j0}`. -/
abbrev Idx1 := {a : Fin (N + 1) ⊕ Fin (N + 1) // a ≠ Sum.inr j0}

/-- `x_j / x_j = 1`. -/
theorem sJ_self (j : Fin (N + 1)) : sJ 𝔭 j j = 1 := by
  rw [sJ, IsLocalization.Away.mul_invSelf]

/-- The linear map `c ↦ ∑_{l ≠ j0} c_l (x_l / x_{j0})`. -/
noncomputable def ratioLinearMap : (Fin (N + 1) → k) →ₗ[k] Aj 𝔭 j0 :=
  ∑ l ∈ Finset.univ.erase j0, (LinearMap.proj l : (Fin (N + 1) → k) →ₗ[k] k).smulRight (sJ 𝔭 j0 l)

/-- The value of `ratioLinearMap` at `c`. -/
theorem ratioLinearMap_apply (c : Fin (N + 1) → k) :
    ratioLinearMap 𝔭 j0 c = ∑ l ∈ Finset.univ.erase j0, c l • sJ 𝔭 j0 l := by
  simp [ratioLinearMap, LinearMap.sum_apply]

/-- If `PhiJ 𝔭 j0` kills `g`, then for every `k`-point `pt1`, the restriction of `g` to the line
through `pt1` in the `u_{j0}` direction has `-ratioLinearMap 𝔭 j0 (pt1 ∘ inl)` as a root. -/
theorem eval_PhiJ_pt (pt1 : Idx1 j0 → k) (g : MvPolynomial (Idx1 j0) k)
    (hg : PhiJ 𝔭 j0 (rename Subtype.val g) = 0) :
    Polynomial.aeval (-(ratioLinearMap 𝔭 j0 (fun l => pt1 ⟨Sum.inl l, by simp⟩)))
      (aeval (fun a : Idx1 j0 =>
          if a.1 = Sum.inl j0 then Polynomial.X else Polynomial.C (pt1 a)) g :
        Polynomial k) = 0 := by
  classical
  set ptT : Fin (N + 1) ⊕ Fin (N + 1) → Aj 𝔭 j0 :=
    fun a => if h : a ≠ Sum.inr j0 then algebraMap k (Aj 𝔭 j0) (pt1 ⟨a, h⟩) else 0 with hptT
  have h1 : eval ptT (PhiJ 𝔭 j0 (rename Subtype.val g)) = 0 := by rw [hg, map_zero]
  have h2 : eval ptT (PhiJ 𝔭 j0 (rename Subtype.val g)) =
      eval₂ (kapJ 𝔭 j0) ((chartPtT j0 (sJ 𝔭 j0) ptT) ∘ Subtype.val) g := by
    rw [PhiJ, eval_chartMap, eval₂_rename]
  have hk : kapJ 𝔭 j0 = algebraMap k (Aj 𝔭 j0) := RingHom.ext (kapJ_eq 𝔭 j0)
  rw [h2, hk] at h1
  rw [MvPolynomial.comp_aeval_apply (φ := Polynomial.aeval _) (p := g)]
  rw [← h1, aeval_def]
  congr 1
  funext a
  rcases a with ⟨a, ha⟩
  rcases a with i | i
  · by_cases hi : i = j0
    · subst hi
      simp only [if_true, Polynomial.aeval_X, Function.comp, chartPtT, ptT]
      congr 1
      rw [ratioLinearMap_apply]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [dif_pos (by simp), Algebra.smul_def, mul_comm]
    · simp [Function.comp, chartPtT, ptT, hi, ha]
  · have hi : i ≠ j0 := fun h => ha (by rw [h])
    simp [Function.comp, chartPtT, ptT, hi, ha]

/-- `ratioLinearMap` sends the basis vector at `l ≠ j0` to `x_l / x_{j0}`. -/
theorem ratioLinearMap_single (l : Fin (N + 1)) (hl : l ≠ j0) :
    ratioLinearMap 𝔭 j0 (Pi.single l (1 : k)) = sJ 𝔭 j0 l := by
  rw [ratioLinearMap_apply, Finset.sum_eq_single l]
  · simp
  · exact fun b _ hb => by simp [Pi.single_apply, hb]
  · exact fun h => absurd (Finset.mem_erase.mpr ⟨hl, Finset.mem_univ l⟩) h

/-- If `PhiJ 𝔭 j0` kills `g` and `-ratioLinearMap 𝔭 j0 (pt1 ∘ inl)` is transcendental over `k`,
then `g` vanishes at `pt1`. -/
theorem eval_eq_zero_of_transcendental (pt1 : Idx1 j0 → k) (g : MvPolynomial (Idx1 j0) k)
    (hg : PhiJ 𝔭 j0 (rename Subtype.val g) = 0)
    (htr : Transcendental k (-(ratioLinearMap 𝔭 j0 (fun l => pt1 ⟨Sum.inl l, by simp⟩)))) :
    eval pt1 g = 0 := by
  classical
  have h0 := eval_PhiJ_pt 𝔭 j0 pt1 g hg
  set G : Idx1 j0 → Polynomial k :=
    fun a => if a.1 = Sum.inl j0 then Polynomial.X else Polynomial.C (pt1 a) with hG
  have hh : (aeval G g : Polynomial k) = 0 :=
    (transcendental_iff_injective.mp htr) (by rw [h0, map_zero])
  have hev : Polynomial.eval (pt1 ⟨Sum.inl j0, by simp⟩) (aeval G g) = eval pt1 g := by
    rw [← Polynomial.coe_aeval_eq_eval,
      MvPolynomial.comp_aeval_apply (φ := Polynomial.aeval _) (p := g), aeval_def,
      Algebra.algebraMap_self, MvPolynomial.eval]
    congr 1
    funext a
    by_cases ha : a.1 = Sum.inl j0
    · obtain rfl : a = ⟨Sum.inl j0, by simp⟩ := Subtype.ext ha
      simp [hG]
    · simp [hG, ha]
  rw [← hev, hh]
  simp

/-- Evaluating the linear form `∑ l, lam (e_l) u_l` gives `lam` applied to the `u`-coordinates. -/
theorem eval_sum_C_lam_mul_X (lam : (Fin (N + 1) → k) →ₗ[k] k) (pt1 : Idx1 j0 → k) :
    eval pt1 (∑ l, C (lam (fun j => if l = j then (1 : k) else 0)) *
      X (⟨Sum.inl l, by simp⟩ : Idx1 j0)) = lam (fun l => pt1 ⟨Sum.inl l, by simp⟩) := by
  simp only [map_sum, map_mul, eval_C, eval_X]
  rw [LinearMap.pi_apply_eq_sum_univ lam]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [smul_eq_mul, mul_comm]

/-- The linear form `∑ l, lam (e_l) u_l` of a nonzero functional `lam` is nonzero. -/
theorem sum_C_lam_mul_X_ne_zero {lam : (Fin (N + 1) → k) →ₗ[k] k} (hlam0 : lam ≠ 0) :
    (∑ l, C (lam (fun j => if l = j then (1 : k) else 0)) *
      X (⟨Sum.inl l, by simp⟩ : Idx1 j0) : MvPolynomial (Idx1 j0) k) ≠ 0 := by
  obtain ⟨c, hc⟩ : ∃ c, lam c ≠ 0 := by
    by_contra h
    push Not at h
    exact hlam0 (LinearMap.ext h)
  intro h0
  have := eval_sum_C_lam_mul_X j0 lam fun a => match a.1 with
    | Sum.inl l => c l
    | Sum.inr _ => 0
  rw [h0, map_zero] at this
  exact hc this.symm

/-- If `Aq 𝔭` has dimension two and `x_{j0} ≠ 0`, no nonzero polynomial in the variables other
than `v_{j0}` lies in the kernel of `PhiJ 𝔭 j0`. -/
theorem lower_bound (hdim : ringKrullDim (Aq 𝔭) = 2) (hx0 : xq 𝔭 j0 ≠ 0)
    (g : MvPolynomial (Idx1 j0) k) (hg : PhiJ 𝔭 j0 (rename Subtype.val g) = 0) : g = 0 := by
  classical
  haveI : IsDomain (Aj 𝔭 j0) :=
    IsLocalization.isDomain_localization (M := Submonoid.powers (xq 𝔭 j0))
      (powers_le_nonZeroDivisors_of_noZeroDivisors hx0)
  obtain ⟨l1, hl1⟩ := exists_notMem_range 𝔭 hdim j0 hx0
  have hl1j : l1 ≠ j0 := by
    rintro rfl
    exact hl1 ⟨1, by simp [sJ_self]⟩
  let S0 : Submodule k (Fin (N + 1) → k) :=
    Submodule.comap (ratioLinearMap 𝔭 j0) (LinearMap.range (Algebra.linearMap k (Aj 𝔭 j0)))
  have hmemS0 : ∀ c, c ∈ S0 ↔ ratioLinearMap 𝔭 j0 c ∈ Set.range (algebraMap k (Aj 𝔭 j0)) := by
    intro c
    simp only [S0, Submodule.mem_comap, LinearMap.mem_range, Algebra.linearMap_apply, Set.mem_range]
  have hS0 : S0 < ⊤ := by
    refine lt_top_iff_ne_top.mpr (fun h => ?_)
    have : (Pi.single l1 (1 : k) : Fin (N + 1) → k) ∈ S0 := by rw [h]; trivial
    rw [hmemS0, ratioLinearMap_single 𝔭 j0 l1 hl1j] at this
    exact hl1 this
  obtain ⟨lam, hlam0, hlam⟩ := Submodule.exists_le_ker_of_lt_top S0 hS0
  have hA : ∀ pt1 : Idx1 j0 → k, (fun l => pt1 ⟨Sum.inl l, by simp⟩) ∉ S0 → eval pt1 g = 0 := by
    intro pt1 hc
    refine eval_eq_zero_of_transcendental 𝔭 j0 pt1 g hg fun hal => ?_
    obtain ⟨r, hr⟩ := mem_range_of_isAlgebraic _ hal
    exact hc ((hmemS0 _).mpr ⟨-r, by rw [map_neg, hr, neg_neg]⟩)
  have hprod : (∑ l, C (lam (fun j => if l = j then (1 : k) else 0)) *
      X (⟨Sum.inl l, by simp⟩ : Idx1 j0)) * g = 0 := by
    refine MvPolynomial.funext fun pt1 => ?_
    rw [map_mul, map_zero, eval_sum_C_lam_mul_X]
    by_cases hc : (fun l => pt1 ⟨Sum.inl l, by simp⟩) ∈ S0
    · have := hlam hc
      rw [LinearMap.mem_ker] at this
      rw [this, zero_mul]
    · rw [hA pt1 hc, mul_zero]
  exact (mul_eq_zero.mp hprod).resolve_left (sum_C_lam_mul_X_ne_zero j0 hlam0)

end Lower

/-- There are `2 * N + 1` variables other than `v_{j0}`. -/
theorem card_Idx1 (j0 : Fin (N + 1)) :
    Fintype.card (Idx1 j0) = 2 * N + 1 := by
  classical
  rw [Fintype.card_subtype_compl, Fintype.card_sum]
  simp
  omega

/-- There are `2 * N` variables other than `u_{j0}` and `v_{j0}`. -/
theorem card_Idx' (j0 : Fin (N + 1)) :
    Fintype.card (Idx' j0) = 2 * N := by
  classical
  rw [Fintype.card_subtype]
  have : (Finset.univ.filter fun a : Fin (N + 1) ⊕ Fin (N + 1) => a ≠ Sum.inl j0 ∧ a ≠ Sum.inr j0) =
      Finset.univ \ {Sum.inl j0, Sum.inr j0} := by
    ext a; simp
  rw [this, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  simp
  omega

/-- For `x_{j0} ∉ 𝔭`, the kernel of `psi 𝔭 j0` is the ideal of the incidence locus. -/
theorem ker_psi (j0 : Fin (N + 1)) (hx0 : (X j0 : MvPolynomial (Fin (N + 1)) k) ∉ 𝔭) :
    RingHom.ker (psi 𝔭 j0) = incIdeal 𝔭 := by
  rw [incIdeal_eq_ker 𝔭 j0 hx0]
  ext f
  simp only [RingHom.mem_ker]
  rw [← (embM_injective 𝔭 j0).eq_iff, embM_psi, map_zero]

/-- A domain and its fraction field have the same transcendence degree over `k`. -/
theorem trdeg_fractionRing_eq (D : Type*) [CommRing D] [IsDomain D] [Algebra k D] :
    Algebra.trdeg k (FractionRing D) = Algebra.trdeg k D := by
  haveI : FaithfulSMul k D := (faithfulSMul_iff_algebraMap_injective k D).mpr
    (algebraMap k D).injective
  haveI : FaithfulSMul D (FractionRing D) := (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (IsFractionRing.injective D (FractionRing D))
  haveI : Algebra.IsAlgebraic D (FractionRing D) := IsLocalization.isAlgebraic _ (nonZeroDivisors D)
  have h := trdeg_add_eq k D (A := FractionRing D)
  rw [trdeg_eq_zero (R := D) (A := FractionRing D), add_zero] at h
  exact h.symm

include h𝔭 in
/-- If `Aq 𝔭` has dimension two, `MvPolynomial (Idx' j0) (ratioAlg 𝔭 j0)` has transcendence degree
at most `2 * N + 1` over `k`. -/
theorem trdeg_M_le (hdim : ringKrullDim (Aq 𝔭) = 2) (j0 : Fin (N + 1)) (hx : xq 𝔭 j0 ≠ 0) :
    Cardinal.toENat (Algebra.trdeg k (MvPolynomial (Idx' j0) (ratioAlg 𝔭 j0))) ≤
      ((2 * N + 1 : ℕ) : ℕ∞) := by
  haveI : IsDomain (Aj 𝔭 j0) :=
    IsLocalization.isDomain_localization (M := Submonoid.powers (xq 𝔭 j0))
      (powers_le_nonZeroDivisors_of_noZeroDivisors hx)
  haveI : FaithfulSMul k (ratioAlg 𝔭 j0) :=
    (faithfulSMul_iff_algebraMap_injective k (ratioAlg 𝔭 j0)).mpr
      (algebraMap k (ratioAlg 𝔭 j0)).injective
  haveI := (faithfulSMul_iff_algebraMap_injective (ratioAlg 𝔭 j0)
    (MvPolynomial (Idx' j0) (ratioAlg 𝔭 j0))).mpr (C_injective _ _)
  have h := trdeg_add_eq k (ratioAlg 𝔭 j0) (A := MvPolynomial (Idx' j0) (ratioAlg 𝔭 j0))
  rw [MvPolynomial.trdeg_of_isDomain] at h
  have h2 := congrArg Cardinal.toENat h
  rw [map_add] at h2
  have h3 :
      Cardinal.toENat (Cardinal.lift.{u, 0} (Cardinal.mk (Idx' j0))) = ((2 * N : ℕ) : ℕ∞) := by
    rw [Cardinal.mk_fintype, card_Idx']
    simp
  rw [h3] at h2
  rw [← h2]
  calc _ ≤ (1 : ℕ∞) + ((2 * N : ℕ) : ℕ∞) := add_le_add_left (trdeg_ratioAlg_le 𝔭 h𝔭 hdim j0 hx) _
    _ = _ := by push_cast; ring

/-- If `Aq 𝔭` has dimension two and `x_{j0} ∉ 𝔭`, the classes of the variables other than `v_{j0}`
are algebraically independent modulo `incIdeal 𝔭`. -/
theorem algebraicIndependent_mk_X (hdim : ringKrullDim (Aq 𝔭) = 2) (j0 : Fin (N + 1))
    (hx0 : (X j0 : MvPolynomial (Fin (N + 1)) k) ∉ 𝔭) :
    AlgebraicIndependent k fun a : Idx1 j0 => Ideal.Quotient.mk (incIdeal 𝔭) (X a.1) := by
  rw [algebraicIndependent_iff_injective_aeval, injective_iff_map_eq_zero]
  intro g hg
  have h1 : aeval (fun a : Idx1 j0 => Ideal.Quotient.mk (incIdeal 𝔭) (X a.1)) g =
      Ideal.Quotient.mk _ (rename Subtype.val g) := by
    have : (aeval fun a : Idx1 j0 => Ideal.Quotient.mk (incIdeal 𝔭) (X a.1)) =
        (Ideal.Quotient.mkₐ k (incIdeal 𝔭)).comp (rename Subtype.val) := by
      ext a
      simp
    exact AlgHom.congr_fun this g
  rw [h1, Ideal.Quotient.eq_zero_iff_mem, incIdeal_eq_ker 𝔭 j0 hx0, RingHom.mem_ker] at hg
  exact lower_bound 𝔭 j0 hdim ((xq_ne_zero_iff 𝔭 j0).mpr hx0) g hg

/-- If the incidence quotient has dimension `2 * N + 1`, the ideal of the incidence locus has
height one. -/
theorem incIdeal_height_of_ringKrullDim
    (hirr : ¬ (HomogeneousIdeal.irrelevant
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)).toIdeal ≤ 𝔭)
    (hD : ringKrullDim (MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k ⧸ incIdeal 𝔭) =
      (((2 * N + 1 : ℕ) : ℕ∞) : WithBot ℕ∞)) :
    (incIdeal 𝔭).height = 1 := by
  haveI hprime := incIdeal_isPrime 𝔭 hirr
  have hform :=
    Stacks.Spectrum.LocalDimensionFormula.ringKrullDim_eq_height_add_ringKrullDim_quotient
    k (MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k) (incIdeal 𝔭)
  have hP : ringKrullDim (MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k) =
      (((2 * N + 2 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp [Nat.card_eq_fintype_card]
    ring
  rw [hP, hD] at hform
  have h5 : ((2 * N + 2 : ℕ) : ℕ∞) = (incIdeal 𝔭).height + ((2 * N + 1 : ℕ) : ℕ∞) := by
    exact_mod_cast hform
  have hne : (incIdeal 𝔭).height ≠ ⊤ := by
    intro h
    rw [h, top_add] at h5
    exact ENat.coe_ne_top _ h5
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hne
  rw [← hm] at h5 ⊢
  have h6 : 2 * N + 2 = m + (2 * N + 1) := by exact_mod_cast h5
  obtain rfl : m = 1 := by omega
  rfl

include h𝔭 in
/-- For a homogeneous prime `𝔭` of dimension two not containing the irrelevant ideal, the ideal of
the incidence locus has height one. -/
theorem incIdeal_height (hdim : ringKrullDim (Aq 𝔭) = 2)
    (hirr : ¬ (HomogeneousIdeal.irrelevant
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)).toIdeal ≤ 𝔭) :
    (incIdeal 𝔭).height = 1 := by
  obtain ⟨j0, hx0⟩ := exists_notMem_X 𝔭 hirr
  have hx : xq 𝔭 j0 ≠ 0 := (xq_ne_zero_iff 𝔭 j0).mpr hx0
  haveI : IsDomain (Aj 𝔭 j0) :=
    IsLocalization.isDomain_localization (M := Submonoid.powers (xq 𝔭 j0))
      (powers_le_nonZeroDivisors_of_noZeroDivisors hx)
  haveI := incIdeal_isPrime 𝔭 hirr
  have hker := ker_psi 𝔭 j0 hx0
  let ι : (MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k ⧸ incIdeal 𝔭) →ₐ[k]
      MvPolynomial (Idx' j0) (ratioAlg 𝔭 j0) :=
    (Ideal.kerLiftAlg (psi 𝔭 j0)).comp (Ideal.quotientEquivAlgOfEq k hker.symm).toAlgHom
  have hι : Function.Injective ι :=
    (Ideal.kerLiftAlg_injective (psi 𝔭 j0)).comp (Ideal.quotientEquivAlgOfEq k hker.symm).injective
  set D := MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k ⧸ incIdeal 𝔭 with hD
  have e1 : Algebra.trdeg k D ≤ Algebra.trdeg k (MvPolynomial (Idx' j0) (ratioAlg 𝔭 j0)) :=
    trdeg_le_of_injective ι hι
  have hup : Cardinal.toENat (Algebra.trdeg k D) ≤ ((2 * N + 1 : ℕ) : ℕ∞) :=
    le_trans (OrderHomClass.mono Cardinal.toENat e1) (trdeg_M_le 𝔭 h𝔭 hdim j0 hx)
  have hlow : ((2 * N + 1 : ℕ) : ℕ∞) ≤ Cardinal.toENat (Algebra.trdeg k D) := by
    have h2 := (algebraicIndependent_mk_X 𝔭 hdim j0 hx0).lift_cardinalMk_le_trdeg
    have h3 := OrderHomClass.mono Cardinal.toENat h2
    rw [Cardinal.toENat_lift, Cardinal.toENat_lift, Cardinal.mk_fintype, card_Idx1] at h3
    simpa using h3
  have hdimD : ringKrullDim D = (((2 * N + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
    have h00 := (ringKrullDim_eq_trdeg_and_ringKrullDim_localization_eq_trdeg.{_, _, _, 0} k D
      (FractionRing D)).1
    rw [h00, trdeg_fractionRing_eq, le_antisymm hup hlow]
  exact incIdeal_height_of_ringKrullDim 𝔭 hirr hdimD

end PrimeIdeal

section IncIdeal

variable (𝔭 : Ideal (MvPolynomial (Fin (N + 1)) k)) [𝔭.IsPrime]
  (h𝔭 : 𝔭.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k))

include h𝔭 in
/-- The incidence locus is Zariski closed (elimination theory). -/
theorem zeroLocus_incIdeal : zeroLocus k (incIdeal 𝔭) = incSet 𝔭 := by
  ext x
  refine ⟨fun hx => ?_, fun hx =>
    mem_zeroLocus_iff.mpr fun f hf => mem_vanishingIdeal_iff.mp hf x hx⟩
  by_contra hno
  have hno' : ¬ ∃ q : Fin (N + 1) → k, q ≠ 0 ∧ (∀ f ∈ 𝔭, eval q f = 0) ∧
      (∑ j, x (Sum.inl j) * q j = 0) ∧ (∑ j, x (Sum.inr j) * q j = 0) := hno
  obtain ⟨r, hr1, hr0⟩ := exists_witness 𝔭 h𝔭 (fun j => x (Sum.inl j)) (fun j => x (Sum.inr j))
    hno'
  have hxe : Sum.elim (fun j => x (Sum.inl j)) (fun j => x (Sum.inr j)) = x := by
    ext (j | j) <;> rfl
  have hr : r ∈ incIdeal 𝔭 := by
    rw [incIdeal, mem_vanishingIdeal_iff]
    intro y hy
    obtain ⟨q, hq0, hq𝔭, hu, hv⟩ := hy
    have := hr0 _ _ q hq0 hq𝔭 hu hv
    rw [show (aeval y) r = eval y r from rfl]
    rwa [show Sum.elim (fun j => y (Sum.inl j)) (fun j => y (Sum.inr j)) = y by
      ext (j | j) <;> rfl] at this
  have h2 := (mem_zeroLocus_iff.mp hx) r hr
  rw [show (aeval x) r = eval x r from rfl, ← hxe, hr1] at h2
  exact one_ne_zero h2

end IncIdeal

/-- The incidence locus of a two-dimensional cone is an irreducible hypersurface. -/
theorem exists_irreducible_coneInc (𝔭 : Ideal (MvPolynomial (Fin (N + 1)) k))
    [𝔭.IsPrime] (h𝔭 : 𝔭.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k))
    (hirr : ¬ (HomogeneousIdeal.irrelevant
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)).toIdeal ≤ 𝔭)
    (hdim : ringKrullDim (MvPolynomial (Fin (N + 1)) k ⧸ 𝔭) = 2) :
    ∃ G : MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k, Irreducible G ∧
      ∀ u v : Fin (N + 1) → k, eval (Sum.elim u v) G = 0 ↔ ConeInc 𝔭 u v := by
  haveI := incIdeal_isPrime 𝔭 hirr
  have hht := incIdeal_height 𝔭 h𝔭 hdim hirr
  obtain ⟨G, hG0⟩ := UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hht
  have hG : incIdeal 𝔭 = Ideal.span {G} := hG0
  have hne : G ≠ 0 := by
    rintro rfl
    exact (incIdeal 𝔭).ne_bot_of_height_eq_one hht (by simpa using hG)
  have hpr : Prime G := (Ideal.span_singleton_prime hne).mp (hG ▸ this)
  refine ⟨G, hpr.irreducible, fun u v => ?_⟩
  have hx : Sum.elim u v ∈ zeroLocus k (incIdeal 𝔭) ↔ eval (Sum.elim u v) G = 0 := by
    rw [mem_zeroLocus_iff, hG]
    refine ⟨fun h => by simpa using h G (Ideal.mem_span_singleton_self G), fun h f hf => ?_⟩
    · obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hf
      simp [h]
  rw [← hx, zeroLocus_incIdeal 𝔭 h𝔭]
  exact Iff.rfl

/-- Every proper curve in `ℙᴺ_k` has an incidence form. -/
theorem exists_incForm (C : Mori.ProperCurve (projToSpecCoeff k N)) :
    ∃ G, IncForm C G := by
  haveI : C.point.asHomogeneousIdeal.toIdeal.IsPrime := C.point.isPrime
  obtain ⟨G, hG, h⟩ := exists_irreducible_coneInc (C.point.asHomogeneousIdeal.toIdeal)
    (C.point.asHomogeneousIdeal.isHomogeneous) C.point.not_irrelevant_le
    (ringKrullDim_properCurve C)
  exact ⟨G, incForm_of_cone C G hG h⟩

/-- An incidence form is determined up to a nonzero scalar. -/
theorem incForm_unique {C : Mori.ProperCurve (projToSpecCoeff k N)}
    {G G' : MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k} (h : IncForm C G) (h' : IncForm C G') :
    ∃ c : kˣ, G' = MvPolynomial.C (c : k) * G := by
  refine assoc_of_same_zeros h.1 (fun x => ?_) h'.1
  have hx : x = Sum.elim (fun j => x (Sum.inl j)) (fun j => x (Sum.inr j)) := by
    ext (j | j) <;> rfl
  rw [hx, h.2, h'.2]

/-- The class of the product of incidence forms is determined by the cycle. -/
theorem chowAt_unique {d : ℕ} {z : Mori.OneCycle ℤ (projToSpecCoeff k N)}
    {x x' : Intersection.ProjSpace k (ULift.{u} (Bi N d))} (h : ChowAt d z x)
    (h' : ChowAt d z x') : x = x' := by
  classical
  choose G hG using exists_incForm (k := k) (N := N)
  have hGz : ∀ C ∈ z.support, IncForm C (G C) := fun C _ => hG C
  obtain ⟨hb, hx⟩ := h G hGz
  obtain ⟨-, hx'⟩ := h' G hGz
  have hF : ∏ C ∈ z.support, G C ^ (z C).toNat ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun C _ => pow_ne_zero _ (hG C).1.ne_zero
  obtain ⟨e, he⟩ : (∏ C ∈ z.support, G C ^ (z C).toNat).support.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr fun h => hF (MvPolynomial.support_eq_empty.mp h)
  exact projectiveSpectrum_ext_of_linear (fun b : ULift.{u} (Bi N d) =>
    (∏ C ∈ z.support, G C ^ (z C).toNat).coeff b.down.1) ⟨⟨e, hb e he⟩⟩
    (MvPolynomial.mem_support_iff.mp he) x x' hx hx'

/-- Two `k`-morphisms from a variety to a projective space agreeing on closed points agree. -/
theorem morphism_ext {S : Scheme.{u}} (sS : S ⟶ Spec (.of k))
    [IsReduced S] [LocallyOfFiniteType sS]
    {d : ℕ} {ψ φ : S ⟶ Intersection.ProjSpace k (ULift.{u} (Bi N d))}
    (hψ : ψ ≫ Intersection.ProjSpace.toSpec k _ = sS)
    (hφ : φ ≫ Intersection.ProjSpace.toSpec k _ = sS)
    (h : ∀ s : S, IsClosed ({s} : Set S) → ψ s = φ s) : ψ = φ := by
  have : LocallyOfFiniteType (ψ ≫ Intersection.ProjSpace.toSpec k _) := by
    rw [hψ]
    infer_instance
  exact ext_of_apply_eq (Intersection.ProjSpace.toSpec k (ULift.{u} (Bi N d))) Set.univ
    isOpen_univ.isLocallyClosed dense_univ (fun x _ hx => h x hx) (hψ.trans hφ.symm)

/-- Uniqueness of the Chow-form morphism. -/
theorem chowMor_unique {S 𝒞 : Scheme.{u}} (sS : S ⟶ Spec (.of k))
    [IsReduced S] [LocallyOfFiniteType sS] (g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N))
    (d : ℕ) (π : 𝒞 ⟶ S) (q : 𝒞 ⟶ Y) {ψ φ : S ⟶ Intersection.ProjSpace k (ULift.{u} (Bi N d))}
    (hψ : ChowMor g d sS π q ψ) (hφ : ChowMor g d sS π q φ) : ψ = φ :=
  morphism_ext sS hψ.1 hφ.1 fun s hs => chowAt_unique (hψ.2 s hs) (hφ.2 s hs)

/-- A morphism of varieties sends closed points to closed points. -/
theorem isClosed_image_of_isClosed {S S' : Scheme.{u}} (sS : S ⟶ Spec (.of k))
    (sS' : S' ⟶ Spec (.of k)) [LocallyOfFiniteType sS] [LocallyOfFiniteType sS']
    (h : S' ⟶ S) (hh : h ≫ sS = sS') (s' : S') (hs' : IsClosed ({s'} : Set S')) :
    IsClosed ({h s'} : Set S) := by
  have hc : LocallyOfFiniteType (h ≫ sS) := by
    rw [hh]
    infer_instance
  have : LocallyOfFiniteType h := @LocallyOfFiniteType.of_comp _ _ _ h sS hc
  have : JacobsonSpace S := LocallyOfFiniteType.jacobsonSpace sS
  exact h.closePoints_subset_preimage_closedPoints hs'

/-- A `k`-morphism of schemes locally of finite type induces an isomorphism on the spectra of the
residue fields at a closed point and its image. -/
theorem isIso_specMap_residueFieldMap {S S' : Scheme.{u}} (sS : S ⟶ Spec (.of k))
    (sS' : S' ⟶ Spec (.of k)) [LocallyOfFiniteType sS] [LocallyOfFiniteType sS']
    (h : S' ⟶ S) (hh : h ≫ sS = sS') (s' : S') (hs' : IsClosed ({s'} : Set S'))
    (hs : IsClosed ({h s'} : Set S)) : IsIso (Spec.map (h.residueFieldMap s')) := by
  have h1 := SpecMap_residueFieldIsoBase_inv sS (h s') hs
  have h2 := SpecMap_residueFieldIsoBase_inv sS' s' hs'
  have key : Spec.map (h.residueFieldMap s') ≫ Spec.map (residueFieldIsoBase sS (h s') hs).inv =
      Spec.map (residueFieldIsoBase sS' s' hs').inv := by
    rw [h1, h2, ← hh, ← Category.assoc, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
      Category.assoc]
  have : Spec.map (h.residueFieldMap s') = Spec.map (residueFieldIsoBase sS' s' hs').inv ≫
      inv (Spec.map (residueFieldIsoBase sS (h s') hs).inv) := by
    rwa [IsIso.eq_comp_inv]
  rw [this]
  infer_instance

/-- At a closed point `s'`, the fibre of the base change of `π` along `h` is isomorphic to the
fibre of `π` at `h s'`, compatibly with the maps to `𝒞`. -/
theorem exists_fiber_iso {S S' 𝒞 : Scheme.{u}} (sS : S ⟶ Spec (.of k))
    (sS' : S' ⟶ Spec (.of k)) [LocallyOfFiniteType sS] [LocallyOfFiniteType sS']
    (π : 𝒞 ⟶ S) (h : S' ⟶ S) (hh : h ≫ sS = sS') (s' : S') (hs' : IsClosed ({s'} : Set S')) :
    ∃ e : (pullback.snd π h).fiber s' ≅ π.fiber (h s'),
      e.hom ≫ π.fiberι (h s') = (pullback.snd π h).fiberι s' ≫ pullback.fst π h := by
  have hs : IsClosed ({h s'} : Set S) := isClosed_image_of_isClosed sS sS' h hh s' hs'
  have hP := isPullback_fiberToSpecResidueField_of_isPullback (IsPullback.of_hasPullback π h) s'
  haveI := isIso_specMap_residueFieldMap sS sS' h hh s' hs' hs
  refine ⟨@asIso _ _ _ _ _ (IsPullback.isIso_fst_of_isIso hP), ?_⟩
  simp only [Scheme.Hom.fiberι, asIso_hom]
  exact pullback.lift_fst _ _ _

/-- The fundamental cycle of a fibre is compatible with base change at closed points. -/
theorem cyc_pullback {S S' 𝒞 : Scheme.{u}} (sS : S ⟶ Spec (.of k))
    (sS' : S' ⟶ Spec (.of k)) [LocallyOfFiniteType sS] [LocallyOfFiniteType sS']
    (g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N))
    (π : 𝒞 ⟶ S) (q : 𝒞 ⟶ Y) (h : S' ⟶ S) (hh : h ≫ sS = sS') (s' : S')
    (hs' : IsClosed ({s'} : Set S')) :
    cyc g sS' (pullback.snd π h) (pullback.fst π h ≫ q) s' = cyc g sS π q (h s') := by
  obtain ⟨e, he⟩ := exists_fiber_iso sS sS' π h hh s' hs'
  have hsX : e.hom ≫ (π.fiberι (h s') ≫ π ≫ sS) =
      (pullback.snd π h).fiberι s' ≫ pullback.snd π h ≫ sS' := by
    rw [← Category.assoc, he, Category.assoc, ← hh, ← Category.assoc (pullback.snd π h),
      ← pullback.condition]
    simp
  have hp : e.hom ≫ (π.fiberι (h s') ≫ q ≫ g) =
      (pullback.snd π h).fiberι s' ≫ (pullback.fst π h ≫ q) ≫ g := by
    rw [← Category.assoc, he]; simp
  have := cycleOf_iso e ((pullback.snd π h).fiberι s' ≫ pullback.snd π h ≫ sS')
    (π.fiberι (h s') ≫ π ≫ sS) (projToSpecCoeff k N) (π.fiberι (h s') ≫ q ≫ g) hsX
  rw [hp] at this
  exact this

/-- Base change of the Chow-form morphism. -/
theorem chowMor_baseChange {S S' 𝒞 : Scheme.{u}} (sS : S ⟶ Spec (.of k))
    (sS' : S' ⟶ Spec (.of k)) [LocallyOfFiniteType sS] [LocallyOfFiniteType sS']
    (g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N)) (d : ℕ)
    (π : 𝒞 ⟶ S) (q : 𝒞 ⟶ Y) {φ : S ⟶ Intersection.ProjSpace k (ULift.{u} (Bi N d))}
    (hφ : ChowMor g d sS π q φ) (h : S' ⟶ S) (hh : h ≫ sS = sS') :
    ChowMor g d sS' (pullback.snd π h) (pullback.fst π h ≫ q) (h ≫ φ) := by
  refine ⟨by rw [Category.assoc, hφ.1, hh], fun s' hs' => ?_⟩
  rw [cyc_pullback sS sS' g π q h hh s' hs']
  exact hφ.2 _ (isClosed_image_of_isClosed sS sS' h hh s' hs')

/-- The Chow-form morphism exists as soon as it exists over the members of an open cover. -/
theorem exists_chowMor_of_cover {S 𝒞 : Scheme.{u}} (sS : S ⟶ Spec (.of k))
    [IsReduced S] [LocallyOfFiniteType sS] (g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N))
    (d : ℕ) (π : 𝒞 ⟶ S) (q : 𝒞 ⟶ Y) (𝒰 : S.OpenCover)
    (hloc : ∀ x, ∃ φ : 𝒰.X x ⟶ Intersection.ProjSpace k (ULift.{u} (Bi N d)),
        ChowMor g d (𝒰.f x ≫ sS) (pullback.snd π (𝒰.f x)) (pullback.fst π (𝒰.f x) ≫ q) φ) :
    ∃ φ : S ⟶ Intersection.ProjSpace k (ULift.{u} (Bi N d)), ChowMor g d sS π q φ := by
  choose φ hφ using hloc
  have hagree : ∀ x y, pullback.fst (𝒰.f x) (𝒰.f y) ≫ φ x = pullback.snd (𝒰.f x) (𝒰.f y) ≫ φ y := by
    intro x y
    have hc := pullback.condition (f := 𝒰.f x) (g := 𝒰.f y)
    haveI : IsOpenImmersion (pullback.fst (𝒰.f x) (𝒰.f y) ≫ 𝒰.f x) := inferInstance
    haveI : IsReduced (pullback (𝒰.f x) (𝒰.f y)) :=
      isReduced_of_isOpenImmersion (pullback.fst (𝒰.f x) (𝒰.f y) ≫ 𝒰.f x)
    haveI : LocallyOfFiniteType (pullback.fst (𝒰.f x) (𝒰.f y) ≫ 𝒰.f x ≫ sS) := by
      rw [← Category.assoc]; infer_instance
    haveI : LocallyOfFiniteType (𝒰.f x ≫ sS) := inferInstance
    haveI : LocallyOfFiniteType (𝒰.f y ≫ sS) := inferInstance
    refine morphism_ext (pullback.fst (𝒰.f x) (𝒰.f y) ≫ 𝒰.f x ≫ sS) ?_ ?_ ?_
    · rw [Category.assoc, (hφ x).1]
    · rw [Category.assoc, (hφ y).1, ← Category.assoc, ← hc, Category.assoc]
    · intro w hw
      have ha : IsClosed ({pullback.fst (𝒰.f x) (𝒰.f y) w} : Set (𝒰.X x)) :=
        isClosed_image_of_isClosed (𝒰.f x ≫ sS) (pullback.fst (𝒰.f x) (𝒰.f y) ≫ 𝒰.f x ≫ sS)
          (pullback.fst (𝒰.f x) (𝒰.f y)) rfl w hw
      have hb : IsClosed ({pullback.snd (𝒰.f x) (𝒰.f y) w} : Set (𝒰.X y)) :=
        isClosed_image_of_isClosed (𝒰.f y ≫ sS) (pullback.fst (𝒰.f x) (𝒰.f y) ≫ 𝒰.f x ≫ sS)
          (pullback.snd (𝒰.f x) (𝒰.f y)) (by rw [← Category.assoc, ← hc, Category.assoc]) w hw
      have h1 := (hφ x).2 _ ha
      have h2 := (hφ y).2 _ hb
      rw [cyc_pullback sS (𝒰.f x ≫ sS) g π q (𝒰.f x) rfl _ ha] at h1
      rw [cyc_pullback sS (𝒰.f y ≫ sS) g π q (𝒰.f y) rfl _ hb] at h2
      have hpt : (𝒰.f x) (pullback.fst (𝒰.f x) (𝒰.f y) w) =
          (𝒰.f y) (pullback.snd (𝒰.f x) (𝒰.f y) w) := by
        rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hc]
      rw [hpt] at h1
      exact chowAt_unique h1 h2
  have hglue : ∀ x, 𝒰.f x ≫ 𝒰.glueMorphisms φ hagree = φ x := fun x => 𝒰.ι_glueMorphisms φ hagree x
  refine ⟨𝒰.glueMorphisms φ hagree, ?_, ?_⟩
  · refine 𝒰.hom_ext _ _ fun x => ?_
    rw [← Category.assoc, hglue, (hφ x).1]
  · intro s hs
    obtain ⟨x, a, rfl⟩ := 𝒰.exists_eq s
    have ha : IsClosed ({a} : Set (𝒰.X x)) := by
      have : ({a} : Set (𝒰.X x)) = 𝒰.f x ⁻¹' {𝒰.f x a} := by
        ext b
        simp only [Set.mem_singleton_iff, Set.mem_preimage]
        exact ⟨fun h => h ▸ rfl, fun h => (𝒰.f x).isOpenEmbedding.injective h⟩
      rw [this]
      exact hs.preimage (𝒰.f x).continuous
    have h1 := (hφ x).2 a ha
    rw [cyc_pullback sS (𝒰.f x ≫ sS) g π q (𝒰.f x) rfl a ha] at h1
    have : (𝒰.glueMorphisms φ hagree) (𝒰.f x a) = φ x a := by
      rw [← Scheme.Hom.comp_apply, hglue]
    rw [this]
    exact h1

end Defs

end MMP.Chow.DeterminantCurveForm
