module

public import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
public import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
public import MMP.AlgebraicGeometry.MMP.Abundance.Defs
public import MMP.AlgebraicGeometry.Intersection.CurveDegreeAdditive
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.Contraction
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import MMP.AlgebraicGeometry.Divisor.SmoothRDivisors
public import StacksFrontier.AlgebraicGeometry.Chow.PointClosureHeightOneCorrespondence
public import StacksFrontier.AlgebraicGeometry.AmpleDimensionOne.Basic
public import MMP.AlgebraicGeometry.Dimension.HeightCoheight

/-!
# Effective anti-nef vertical divisors over a curve are fibre divisors

Let `f : X ⟶ C` be a surjective projective morphism from a normal `ℚ`-factorial projective
variety to a smooth curve over a field `k`, with `f_* 𝒪_X = 𝒪_C`. If `A ≥ 0` is a `ℚ`-divisor
on `X` all of whose components map to points of `C` and `-A` is `f`-nef, then `A = f^*P` for an
effective `ℚ`-divisor `P` on `C`.

Fix a closed point `c = η_P` of `C` and let `F = f^*P = ∑ mᵢ Eᵢ` be its fibre divisor. A
uniformizer `ϖ` at `c` is a local equation of `P` near `c`, so `f^*ϖ` is a local equation of `F`
near the fibre; hence `mᵢ > 0` exactly along the components over `c`, every point over `c` lies
in `Supp F`, and `F` differs from the principal divisor `div(f^*ϖ)` by a divisor whose support
misses the fibre, so `(F · γ) = 0` for every curve `γ` in the fibre. Let `t = min aᵢ/mᵢ` and
`D = A - tF ≥ 0`. If `D` were nonzero along the fibre, connectedness of the fibre gives components
`E₀ ⊄ Supp D` and `E₁ ⊆ Supp D` that meet, and a curve `γ ⊆ E₀` through a closed point of
`E₀ ∩ Supp D` not contained in `Supp D` has `(D · γ) > 0`, while
`(D · γ) = (A · γ) - t (F · γ) = (A · γ) ≤ 0`. So `A = tF` along every fibre, and `P = ∑ t_c c`.

The curve `γ` is produced by commutative algebra in the local ring `𝒪_{X,p}` of the closed point
`p`: among the primes containing that of `η_{E₀}` and avoiding a function vanishing on `Supp D`, a
maximal one is an immediate predecessor of the maximal ideal, by Krull's principal ideal theorem
and prime avoidance (`MMP.Fourfold.exists_isPrime_le_lt_notMem_of_lt`); its closure is a curve by
the dimension formula for schemes of finite type over a field.

## Main definitions

* `MMP.Fourfold.QDivisor.IsVertical`: a `ℚ`-divisor whose components map to points.

## Main results

* `MMP.Fourfold.exists_eq_pullback_of_isVertical_of_isRelativelyNef_neg`: the statement above.
* `MMP.Fourfold.exists_coeff_eq_mul_of_isPullback_single`: Zariski's lemma along one fibre.
* `MMP.Fourfold.exists_isProperCurve_of_specializes`: a proper curve through a closed point,
  inside a given irreducible closed subset, not contained in a given closed subset.
* `MMP.Fourfold.intersectionNumber_nonneg_and_eq_zero_iff`,
  `MMP.Fourfold.intersectionNumber_eq_zero_of_disjoint`: intersection numbers of effective
  divisors, and of divisors disjoint from a curve.
* `MMP.Fourfold.mem_supp_of_isPullback_single`, `MMP.Fourfold.coeff_pos_of_isPullback_single`,
  `MMP.Fourfold.coeff_eq_zero_of_isPullback_single`,
  `MMP.Fourfold.intersectionNumber_eq_zero_of_isPullback_single`: the fibre divisor `f^*P`.

## Implementation notes

The source works over `ℂ` with `X` of dimension `n ≥ 2`; the proof uses neither, so the
statement is made over an arbitrary field and in every dimension. Projectivity of `C` is not
used, nor is it needed that `f` commutes with the structure morphisms; `X` is projective over
`k`, which makes its curves proper. The fibre intersection matrix `Eᵢ · Eⱼ · Hⁿ⁻²` of the source
is replaced by the extremal argument with `t = min aᵢ/mᵢ`, which tests `D` against one curve and
needs no intersection theory beyond intersection numbers with curves. `f_* 𝒪_X = 𝒪_C` is
`∀ U, IsIso (f.app U)`, and gives connected fibres (Stacks 03H2). "Vertical" is
`MMP.Fourfold.QDivisor.IsVertical`. The pull-back is `MMP.Mori.QDivisor.pullback`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Notation 0.4
* [Stacks Project, Tag 03H2](https://stacks.math.columbia.edu/tag/03H2)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Topology

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Fourfold

section Algebra

variable {R : Type*} [CommRing R] [IsNoetherianRing R]

/-- In a Noetherian domain with a chain of primes `⊥ < r < M`, every nonzero `a` lies outside some
prime `P` with `⊥ < P < M`. -/
theorem exists_isPrime_bot_lt_lt_notMem [IsDomain R] {r M : Ideal R} [r.IsPrime] [M.IsPrime]
    (hr0 : ⊥ < r) (hrM : r < M) {a : R} (ha : a ≠ 0) :
    ∃ P : Ideal R, P.IsPrime ∧ ⊥ < P ∧ P < M ∧ a ∉ P := by
  classical
  by_cases haM : a ∉ M
  · exact ⟨r, inferInstance, hr0, hrM, fun h => haM (hrM.le h)⟩
  push Not at haM
  have : (⊥ : Ideal R).IsPrime := Ideal.isPrime_bot
  have htwo : ∀ P P' : Ideal R, P.IsPrime → P'.IsPrime → ⊥ < P → P < P' →
      (2 : ℕ∞) ≤ P'.height := by
    intro P P' _ _ hP hPP'
    have e1 := Ideal.height_add_one_le_of_lt_of_isPrime hP
    have e2 := Ideal.height_add_one_le_of_lt_of_isPrime hPP'
    calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
      _ ≤ (⊥ : Ideal R).height + 1 + 1 := by gcongr; exact zero_le
      _ ≤ P'.height := le_trans (by gcongr) e2
  have hM2 : (2 : ℕ∞) ≤ M.height := htwo r M inferInstance inferInstance hr0 hrM
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing R (Ideal.span {a})
  -- prime avoidance: `M` is not covered by the minimal primes of `(a)`
  obtain ⟨b, hbM, hbP⟩ : ∃ b ∈ M, ∀ P ∈ (Ideal.span {a}).minimalPrimes, b ∉ P := by
    by_contra hcon
    push Not at hcon
    have hsub : (M : Set R) ⊆ ⋃ P ∈ (hfin.toFinset : Set (Ideal R)), (P : Set R) := by
      intro x hx
      obtain ⟨P, hP, hxP⟩ := hcon x hx
      exact Set.mem_iUnion₂.mpr ⟨P, by simpa using hP, hxP⟩
    obtain ⟨P, hP, hMP⟩ := (Ideal.subset_union_prime (f := id) (⊥ : Ideal R) ⊥
      (fun P hP _ _ => (Set.Finite.mem_toFinset hfin |>.mp hP).1.1)).mp hsub
    have hP' : P ∈ (Ideal.span {a}).minimalPrimes := (Set.Finite.mem_toFinset hfin).mp hP
    have := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hP'
    have := Ideal.height_mono hMP
    have : (2 : ℕ∞) ≤ 1 := hM2.trans (by simpa using this.trans ‹P.height ≤ 1›)
    exact absurd this (by decide)
  obtain ⟨P₀, hP₀, -⟩ := Ideal.exists_minimalPrimes_le
    ((Ideal.span_singleton_le_iff_mem M).mpr haM)
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hbP P₀ hP₀ (Ideal.zero_mem _)
  obtain ⟨P', hP', hP'M⟩ := Ideal.exists_minimalPrimes_le
    ((Ideal.span_singleton_le_iff_mem M).mpr hbM)
  have hP'p : P'.IsPrime := hP'.1.1
  have hbP' : b ∈ P' := (Ideal.span_singleton_le_iff_mem P').mp hP'.1.2
  have hP'h := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P' hP'
  refine ⟨P', hP'p, bot_lt_iff_ne_bot.mpr fun h => hb0 (by rw [h] at hbP'; exact hbP'), ?_, ?_⟩
  · refine lt_of_le_of_ne hP'M fun h => ?_
    rw [h] at hP'h
    exact absurd (hM2.trans hP'h) (by decide)
  · intro haP'
    obtain ⟨P, hP, hPP'⟩ := Ideal.exists_minimalPrimes_le
      ((Ideal.span_singleton_le_iff_mem P').mpr haP')
    have : P.IsPrime := hP.1.1
    rcases eq_or_lt_of_le hPP' with h | h
    · exact hbP P hP (h ▸ hbP')
    · have haP : a ∈ P := (Ideal.span_singleton_le_iff_mem P).mp hP.1.2
      have := htwo P P' inferInstance inferInstance
        (bot_lt_iff_ne_bot.mpr fun h0 => ha (by rw [h0] at haP; exact haP)) h
      exact absurd (this.trans hP'h) (by decide)

/-- **Avoiding an element by an immediate predecessor.** Let `Q < M` be primes of a Noetherian
ring and `a ∉ Q`. There is a prime `q` with `Q ≤ q < M`, `a ∉ q`, and no prime strictly between
`q` and `M`. -/
theorem exists_isPrime_le_lt_notMem_of_lt {Q M : Ideal R} [Q.IsPrime] [M.IsPrime]
    (hQM : Q < M) {a : R} (ha : a ∉ Q) :
    ∃ q : Ideal R, q.IsPrime ∧ Q ≤ q ∧ q < M ∧ a ∉ q ∧
      ∀ r : Ideal R, r.IsPrime → q < r → r ≤ M → r = M := by
  classical
  set S : Set (Ideal R) := {q | q.IsPrime ∧ Q ≤ q ∧ q < M ∧ a ∉ q}
  obtain ⟨q, ⟨hq, hQq, hqM, haq⟩, hmax⟩ :=
    set_has_maximal_iff_noetherian.mpr (inferInstanceAs (IsNoetherian R R)) S
      ⟨Q, inferInstance, le_rfl, hQM, ha⟩
  refine ⟨q, hq, hQq, hqM, haq, fun r hr hqr hrM => ?_⟩
  by_contra hrM'
  have hrM : r < M := lt_of_le_of_ne hrM hrM'
  set π := Ideal.Quotient.mk q
  have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
  have hcm : ∀ I : Ideal R, q ≤ I → Ideal.comap π (Ideal.map π I) = I := fun I hI => by
    rw [Ideal.comap_map_of_surjective' π hπ, Ideal.mk_ker, sup_eq_left.mpr hI]
  have hprime : ∀ I : Ideal R, I.IsPrime → q ≤ I → (Ideal.map π I).IsPrime := fun I hI hqI =>
    Ideal.map_isPrime_of_surjective hπ (by rw [Ideal.mk_ker]; exact hqI)
  have := hprime r hr hqr.le
  have := hprime M inferInstance hqM.le
  have hmono : ∀ I J : Ideal R, q ≤ I → q ≤ J → I < J → Ideal.map π I < Ideal.map π J := by
    intro I J hI hJ hIJ
    refine lt_of_le_of_ne (Ideal.map_mono hIJ.le) fun h => hIJ.ne ?_
    rw [← hcm I hI, ← hcm J hJ, h]
  have hbot : (⊥ : Ideal (R ⧸ q)) = Ideal.map π q := by
    rw [Ideal.map_quotient_self]
  obtain ⟨P, hP, hP0, hPM, haP⟩ := exists_isPrime_bot_lt_lt_notMem
    (r := Ideal.map π r) (M := Ideal.map π M) (hbot ▸ hmono q r le_rfl hqr.le hqr)
    (hmono r M hqr.le hqM.le hrM)
    (a := π a) (fun h => haq (Ideal.Quotient.eq_zero_iff_mem.mp h))
  have hqP : q ≤ Ideal.comap π P := fun x hx => by
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]; exact P.zero_mem
  have hmc : Ideal.map π (Ideal.comap π P) = P := Ideal.map_comap_of_surjective π hπ P
  refine hmax (Ideal.comap π P) ⟨Ideal.comap_isPrime π P, hQq.trans hqP, ?_, haP⟩ ?_
  · refine lt_of_le_of_ne ?_ fun h => hPM.ne (by rw [← hmc, h])
    rw [← hcm M hqM.le]; exact Ideal.comap_mono hPM.le
  · refine lt_of_le_of_ne hqP fun h => hP0.ne' ?_
    rw [← hmc, ← h, hbot]

end Algebra

open MMP.Mori

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- If `y ⤳ p` with `p` a closed point and no point strictly between `y` and `p`, then the
closure of `y` in a scheme locally of finite type over a field has dimension one. -/
theorem topologicalKrullDim_curveSubschemeAt_eq_one (sX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType sX] {y p : X} (hyp : y ⤳ p) (hne : y ≠ p) (hp : IsClosed ({p} : Set X))
    (himm : ∀ z : X, y ⤳ z → z ⤳ p → z = y ∨ z = p) :
    topologicalKrullDim (curveSubschemeAt y) = 1 := by
  set W := curveSubschemeAt y
  set ι := curveSubschemeAtι y
  have : IsIntegral W :=
    StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible _
      isIrreducible_singleton.closure
  let : W.Over (Spec (.of k)) := ⟨ι ≫ sX⟩
  have : LocallyOfFiniteType (W ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (ι ≫ sX))
  have hrange : Set.range ι = closure ({y} : Set X) := by
    change Set.range (Scheme.IdealSheafData.vanishingIdeal _).subschemeι = _
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hind : IsInducing ι := ι.isClosedEmbedding.isInducing
  obtain ⟨p', hp'⟩ : p ∈ Set.range ι :=
    hrange ▸ specializes_iff_mem_closure.mp hyp
  obtain ⟨y', hy'⟩ : ∃ y' : W, ι y' = y := MMP.Threefold.Mori.exists_ι_eq_point y
  have hspec : ∀ a b : W, a ⤳ b ↔ ι a ⤳ ι b := fun a b => hind.specializes_iff.symm
  -- every point of `W` is a specialization of `y'`
  have htop : ∀ a : W, y' ⤳ a := fun a => by
    rw [hspec, hy']
    have : ι a ∈ Set.range ι := ⟨a, rfl⟩
    rw [hrange] at this
    exact specializes_iff_mem_closure.mpr this
  have hmin : IsMin p' := by
    intro a ha
    have h2 : ι p' ⤳ ι a := (hspec _ _).mp ha
    rw [hp'] at h2
    have h3 : ι a = p := by
      have := specializes_iff_mem_closure.mp h2
      rw [hp.closure_eq] at this
      exact this
    have : a = p' := hind.injective (h3.trans hp'.symm)
    rw [this]
  have hlt : p' < y' := by
    refine lt_of_le_not_ge (htop p') fun h => hne ?_
    have h2 := (hspec _ _).mp h
    rw [hp', hy'] at h2
    exact (hyp.antisymm h2).eq
  have hcoh : Order.coheight p' = 1 := by
    refine le_antisymm ?_ ?_
    · rw [Order.coheight_le_iff]
      intro s hs
      by_contra hlen
      push Not at hlen
      have h2 : 2 ≤ s.length := by
        have : (1 : ℕ∞) < s.length := hlen
        exact_mod_cast Order.add_one_le_of_lt this
      -- `p' ≤ s 0 < s 1 < s 2`, so `s 1` lies strictly between `p'` and `y'`
      set i0 : Fin (s.length + 1) := ⟨0, by omega⟩
      set i1 : Fin (s.length + 1) := ⟨1, by omega⟩
      set i2 : Fin (s.length + 1) := ⟨2, by omega⟩
      have h01 : s.toFun i0 < s.toFun i1 :=
        s.strictMono (show i0 < i1 from Fin.mk_lt_mk.mpr (by omega))
      have h12 : s.toFun i1 < s.toFun i2 :=
        s.strictMono (show i1 < i2 from Fin.mk_lt_mk.mpr (by omega))
      have hp1 : p' < s.toFun i1 := lt_of_le_of_lt hs h01
      have h1y : s.toFun i1 < y' := lt_of_lt_of_le h12 (htop _)
      have hzy := (hspec _ _).mp h1y.le
      have hzp := (hspec _ _).mp hp1.le
      rw [hy'] at hzy
      rw [hp'] at hzp
      have hz := himm (ι (s.toFun i1)) hzy hzp
      rcases hz with hz | hz
      · exact h1y.ne (hind.injective (hz.trans hy'.symm))
      · exact hp1.ne' (hind.injective (hz.trans hp'.symm))
    · exact le_trans (by simp) (Order.coheight_add_one_le hlt)
  have hform := MMP.height_add_coheight_eq_krullDim k p'
  rw [Order.height_eq_zero.mpr hmin, hcoh, zero_add,
    Stacks.AlgebraicGeometry.AmpleDimensionOne.krullDim_eq_topologicalKrullDim] at hform
  rw [← hform]
  rfl

/-- **Curves through a point avoiding a closed set.** Let `X` be a locally Noetherian scheme,
proper over a field, `p` a closed point, `η ⤳ p` a generization and `Z ∋ p` a closed subset not
containing `η`. There is a proper curve `{y}⁻ ⊆ {η}⁻` through `p` not contained in `Z`. -/
theorem exists_isProperCurve_of_specializes (sX : X ⟶ Spec (.of k)) [IsProper sX]
    [IsLocallyNoetherian X] {η p : X} (hηp : η ⤳ p) (hp : IsClosed ({p} : Set X)) {Z : Set X}
    (hZ : IsClosed Z) (hpZ : p ∈ Z) (hηZ : η ∉ Z) :
    ∃ y : X, η ⤳ y ∧ y ⤳ p ∧ y ∉ Z ∧ IsProperCurve sX y := by
  classical
  set R := X.presheaf.stalk p
  set g := X.fromSpecStalk p
  obtain ⟨Q, hQ⟩ := Stacks.Chow.exists_fromSpecStalk_eq hηp
  have hT : IsClosed (g ⁻¹' Z : Set (PrimeSpectrum R)) := hZ.preimage g.continuous
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).mp hT
  have hQT : ¬ ((I : Set R) ⊆ Q.asIdeal) := fun h => by
    have h' : Q ∈ PrimeSpectrum.zeroLocus (I : Set R) := h
    rw [← hI] at h'
    exact hηZ (by rw [← hQ]; exact h')
  obtain ⟨a, haI, haQ⟩ := Set.not_subset.mp hQT
  have hgM : g (IsLocalRing.closedPoint R) = p := Scheme.fromSpecStalk_closedPoint
  have hQM : Q.asIdeal < IsLocalRing.maximalIdeal R := by
    refine lt_of_le_of_ne (IsLocalRing.le_maximalIdeal Q.isPrime.ne_top) fun h => hηZ ?_
    have : Q = IsLocalRing.closedPoint R := PrimeSpectrum.ext h
    rw [← hQ, this, Scheme.fromSpecStalk_closedPoint]
    exact hpZ
  obtain ⟨q, hq, hQq, hqM, haq, himm⟩ := exists_isPrime_le_lt_notMem_of_lt hQM haQ
  set qpt : PrimeSpectrum R := ⟨q, hq⟩
  have hyZ : g qpt ∉ Z := by
    intro h
    have h' : qpt ∈ (g ⁻¹' Z : Set (PrimeSpectrum R)) := h
    rw [hI] at h'
    exact haq (h' haI)
  have hyp : g qpt ⤳ p := Stacks.Chow.specializes_fromSpecStalk p qpt
  refine ⟨g qpt, ?_, hyp, hyZ, ⟨?_, inferInstance⟩⟩
  · rw [← hQ]
    exact ((PrimeSpectrum.le_iff_specializes Q qpt).mp hQq).map g.continuous
  · refine topologicalKrullDim_curveSubschemeAt_eq_one sX hyp
      (fun h => hyZ (by rw [h]; exact hpZ)) hp fun z hyz hzp => ?_
    obtain ⟨r, rfl⟩ := Stacks.Chow.exists_fromSpecStalk_eq hzp
    have hle : r ≤ qpt := (Stacks.Chow.fromSpecStalk_le_iff p).mp hyz
    have hqr : q ≤ r.asIdeal := (PrimeSpectrum.le_iff_specializes qpt r).mpr hle
    rcases eq_or_lt_of_le hqr with h | h
    · left
      congr 1
      exact PrimeSpectrum.ext h.symm
    · right
      have := himm r.asIdeal r.isPrime h (IsLocalRing.le_maximalIdeal r.isPrime.ne_top)
      rw [show r = IsLocalRing.closedPoint R from PrimeSpectrum.ext this]
      exact hgM

/-! ### Intersection numbers with proper curves -/

section Intersection

variable (sX : X ⟶ Spec (.of k))

variable [IsLocallyNoetherian X] [IsNormal X]

/-- On a `ℚ`-factorial variety every `ℚ`-divisor is `ℚ`-Cartier. -/
theorem isQCartier_of_isQFactorial (hX : IsQFactorial sX) (D : QDivisor X) : D.IsQCartier := by
  obtain ⟨N, hN, G, hG⟩ := MMP.Flips.exists_pos_smul_eq_toQDivisor D
  obtain ⟨m, hm, hmG⟩ := hX.2 G
  refine ⟨(m : ℤ) * N, by positivity, (m : ℤ) • G, ?_, hmG⟩
  rw [map_zsmul, hG, smul_smul]

variable [QuasiCompact sX]

/-- **Intersection numbers of effective divisors with curves.** Let `D ≥ 0` be a `ℚ`-Cartier
`ℚ`-divisor and `C` a proper curve not contained in `Supp D`. Then `(D · C) ≥ 0`, with equality
if and only if `C` is disjoint from `Supp D`. -/
theorem intersectionNumber_nonneg_and_eq_zero_iff (D : QDivisor X) (hD : D.IsQCartier)
    (h0 : 0 ≤ D) (C : ProperCurve sX) (hC : C.point ∉ D.supp) :
    0 ≤ D.intersectionNumber k sX C.ι C.dim_le hD ∧
      (D.intersectionNumber k sX C.ι C.dim_le hD = 0 ↔
        ∀ x : X, C.point ⤳ x → x ∉ D.supp) := by
  obtain ⟨m, hm, E, hE, hEc⟩ := hD.exists_pos
  have hsupp : E.supp = D.supp :=
    QDivisor.supp_eq_of_toQDivisor_eq (by exact_mod_cast hm.ne') hE
  have hE0 : 0 ≤ E := by
    intro P
    have h1 := congrArg (fun G : QDivisor X => G P) hE
    simp only [Finsupp.smul_apply, zsmul_eq_mul] at h1
    have h2 : (0 : ℚ) ≤ (m : ℚ) * D P := mul_nonneg (by positivity) (h0 P)
    have h3 : ((E P : ℤ) : ℚ) = (Divisor.toQDivisor E) P := (Divisor.coeff_toQDivisor E P).symm
    have : (0 : ℚ) ≤ (E P : ℚ) := by rw [h3, h1]; exact_mod_cast h2
    exact_mod_cast this
  obtain ⟨c₀, hc₀⟩ := MMP.Threefold.Mori.exists_ι_eq_point C.point
  have hne : ∃ c : C.scheme, C.ι c ∉ E.supp := ⟨c₀, by rw [hsupp]; exact hc₀ ▸ hC⟩
  obtain ⟨hnn, hiff⟩ :=
    MMP.Threefold.Mori.degreeOn_nonneg_and_eq_zero_iff sX C.ι C.dim_le E hEc hE0 hne
  rw [QDivisor.intersectionNumber_eq_of_smul k sX C.ι C.dim_le D hD hm E hEc hE]
  have hmq : (0 : ℚ) < m := by exact_mod_cast hm
  refine ⟨div_nonneg (by exact_mod_cast hnn) hmq.le, ?_⟩
  rw [div_eq_zero_iff, or_iff_left hmq.ne', Int.cast_eq_zero, hiff, hsupp]
  constructor
  · intro h x hx
    obtain ⟨c, rfl⟩ : x ∈ Set.range C.ι := by
      rw [C.range_ι]
      exact specializes_iff_mem_closure.mp hx
    exact h c
  · intro h c
    refine h _ (specializes_iff_mem_closure.mpr ?_)
    rw [← C.range_ι]
    exact ⟨c, rfl⟩

/-- Equal `ℚ`-divisors have equal intersection numbers with a curve, regardless of the
`ℚ`-Cartier proofs. -/
theorem intersectionNumber_congr {C : Scheme.{u}} (i : C ⟶ X)
    [IsProper (i ≫ sX)] (hdim : topologicalKrullDim C ≤ 1) {D D' : QDivisor X}
    (hD : D.IsQCartier) (hD' : D'.IsQCartier) (h : D = D') :
    D.intersectionNumber k sX i hdim hD = D'.intersectionNumber k sX i hdim hD' := by
  subst h
  rfl

/-- `deg_C 𝒪_X(nD) = n · deg_C 𝒪_X(D)` for a Cartier divisor `D` and `n ∈ ℤ`. -/
theorem degreeOn_zsmul {C : Scheme.{u}} (i : C ⟶ X) [IsProper (i ≫ sX)]
    (hdim : topologicalKrullDim C ≤ 1) (D : Divisor X) (hD : D.IsCartier) (n : ℤ) :
    (n • D).degreeOn k sX i hdim (hD.zsmul n) = n * D.degreeOn k sX i hdim hD := by
  have hneg : ∀ (G : Divisor X) (hG : G.IsCartier),
      (-G).degreeOn k sX i hdim hG.neg = -G.degreeOn k sX i hdim hG := by
    intro G hG
    have h := Divisor.degreeOn_add k sX i hdim G (-G) hG hG.neg
    rw [Divisor.degreeOn_congr (add_neg_cancel G) _ Divisor.isCartier_zero,
      Divisor.degreeOn_zero'] at h
    omega
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · rw [Divisor.degreeOn_congr (natCast_zsmul D m) _ (hD.nsmul m),
      Divisor.degreeOn_nsmul' k sX i hdim D hD m]
  · rw [Divisor.degreeOn_congr (by rw [neg_smul, natCast_zsmul]) _ (hD.nsmul m).neg,
      hneg _ (hD.nsmul m), Divisor.degreeOn_nsmul' k sX i hdim D hD m]
    ring

/-- `((q D) · C) = q (D · C)` for `q ∈ ℚ`. -/
theorem intersectionNumber_smul {C : Scheme.{u}} (i : C ⟶ X) [IsProper (i ≫ sX)]
    (hdim : topologicalKrullDim C ≤ 1) (D : QDivisor X) (hD : D.IsQCartier) (q : ℚ)
    (hqD : (q • D).IsQCartier) :
    (q • D).intersectionNumber k sX i hdim hqD = q * D.intersectionNumber k sX i hdim hD := by
  obtain ⟨m, hm, E, hE, hEc⟩ := hD.exists_pos
  have hbm : 0 < q.den * m := Nat.mul_pos q.den_pos hm
  have hE' : Divisor.toQDivisor (q.num • E) = ((q.den * m : ℕ) : ℤ) • (q • D) := by
    refine Finsupp.ext fun P => ?_
    have h1 := congrArg (fun G : QDivisor X => G P) hE
    simp only [Finsupp.smul_apply, zsmul_eq_mul, smul_eq_mul] at h1 ⊢
    change ((q.num • E) P : ℚ) = _
    rw [Finsupp.smul_apply, smul_eq_mul, Int.cast_mul]
    change _ * ((E P : ℤ) : ℚ) = _
    have h2 : ((E P : ℤ) : ℚ) = (Divisor.toQDivisor E) P := rfl
    rw [h2, h1]
    have := Rat.mul_den_eq_num q
    push_cast
    rw [← this]
    ring
  rw [QDivisor.intersectionNumber_eq_of_smul k sX i hdim _ hqD hbm _ (hEc.zsmul _) hE',
    QDivisor.intersectionNumber_eq_of_smul k sX i hdim _ hD hm _ hEc hE,
    degreeOn_zsmul sX i hdim E hEc]
  have hd : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_pos.ne'
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  conv_rhs => rw [← Rat.num_div_den q]
  push_cast
  field_simp

/-- `(0 · C) = 0`. -/
theorem intersectionNumber_zero {C : Scheme.{u}} (i : C ⟶ X) [IsProper (i ≫ sX)]
    (hdim : topologicalKrullDim C ≤ 1) :
    (0 : QDivisor X).intersectionNumber k sX i hdim QDivisor.isQCartier_zero = 0 := by
  have := intersectionNumber_smul sX i hdim (0 : QDivisor X) QDivisor.isQCartier_zero 0
    (by simpa using QDivisor.isQCartier_zero)
  rw [zero_mul] at this
  rw [← this]
  exact intersectionNumber_congr sX i hdim _ _ (by simp)

/-- **A divisor disjoint from a curve has intersection number zero with it**, on a
`ℚ`-factorial variety. -/
theorem intersectionNumber_eq_zero_of_disjoint (hX : IsQFactorial sX) (D : QDivisor X)
    (hD : D.IsQCartier) (C : ProperCurve sX) (hdisj : ∀ x : X, C.point ⤳ x → x ∉ D.supp) :
    D.intersectionNumber k sX C.ι C.dim_le hD = 0 := by
  classical
  set Dp : QDivisor X := Finsupp.mapRange (fun r => max r 0) (by simp) D
  set Dn : QDivisor X := Finsupp.mapRange (fun r => max (-r) 0) (by simp) D
  have hDpn : D = Dp + -Dn := by
    refine Finsupp.ext fun P => ?_
    simp only [Dp, Dn, Finsupp.coe_add, Finsupp.coe_neg, Pi.add_apply, Pi.neg_apply,
      Finsupp.mapRange_apply]
    rcases le_total (D P) 0 with h | h
    · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]
      ring
    · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
      ring
  have hsub : ∀ G : QDivisor X, (∀ P, G P ≠ 0 → D P ≠ 0) → ∀ x : X, C.point ⤳ x → x ∉ G.supp := by
    intro G hG x hx hxG
    obtain ⟨P, hP, hxP⟩ := DivisorWithCoeffs.mem_supp_iff.mp hxG
    exact hdisj x hx (DivisorWithCoeffs.mem_supp_iff.mpr ⟨P, hG P hP, hxP⟩)
  have hzero : ∀ G : QDivisor X, (hG : G.IsQCartier) → 0 ≤ G →
      (∀ P, G P ≠ 0 → D P ≠ 0) → G.intersectionNumber k sX C.ι C.dim_le hG = 0 := by
    intro G hG h0 hGD
    have hC : C.point ∉ G.supp := hsub G hGD _ (specializes_refl _)
    exact ((intersectionNumber_nonneg_and_eq_zero_iff sX G hG h0 C hC).2).mpr (hsub G hGD)
  have hp := isQCartier_of_isQFactorial sX hX Dp
  have hn := isQCartier_of_isQFactorial sX hX Dn
  have hnn := isQCartier_of_isQFactorial sX hX (-Dn)
  have hp0 : 0 ≤ Dp := fun P => by simp [Dp]
  have hn0 : 0 ≤ Dn := fun P => by simp [Dn]
  have hpD : ∀ P, Dp P ≠ 0 → D P ≠ 0 := fun P h hD => h (by simp [Dp, hD])
  have hnD : ∀ P, Dn P ≠ 0 → D P ≠ 0 := fun P h hD => h (by simp [Dn, hD])
  have hadd := QDivisor.intersectionNumber_add' k sX C.ι C.dim_le Dn (-Dn) hn hnn
    (by rw [add_neg_cancel]; exact QDivisor.isQCartier_zero)
  rw [intersectionNumber_congr sX C.ι C.dim_le _ QDivisor.isQCartier_zero (add_neg_cancel Dn),
    intersectionNumber_zero, hzero Dn hn hn0 hnD] at hadd
  rw [intersectionNumber_congr sX C.ι C.dim_le hD (hp.add hnn) hDpn,
    QDivisor.intersectionNumber_add' k sX C.ι C.dim_le Dp (-Dn) hp hnn, hzero Dp hp hp0 hpD]
  linarith

/-- The relative nefness of a `ℚ`-Cartier `ℚ`-divisor, read as intersection numbers:
`(D · C) ≥ 0` for every proper curve `C` contracted by `f`. -/
theorem QDivisor.IsRelativelyNef.intersectionNumber_nonneg {Y : Scheme.{u}} {f : X ⟶ Y}
    {D : QDivisor X} (h : D.IsRelativelyNef sX f) (hD : D.IsQCartier) (C : ProperCurve sX)
    (hC : C.IsContractedBy f) : 0 ≤ D.intersectionNumber k sX C.ι C.dim_le hD := by
  obtain ⟨h', hh⟩ := h
  have key := hh C hC
  rw [QDivisor.associatedCartier, CartierDivisorWithCoeffs.ofCartier, Finsupp.smul_single,
    Finsupp.sum_single_index (by simp)] at key
  have hm : (0 : ℚ) < D.cartierIndex h' := by exact_mod_cast QDivisor.cartierIndex_pos h'
  rw [QDivisor.intersectionNumber]
  refine div_nonneg ?_ hm.le
  have hm' : (0 : ℝ) < (D.cartierIndex h' : ℝ) := by exact_mod_cast hm
  have : (0 : ℝ) ≤ ((D.cartierIndexSMul h' : Divisor X).degreeOn k sX C.ι C.dim_le
      (D.cartierIndexSMul h').2 : ℝ) := by
    simp only [smul_eq_mul, mul_one, Rat.cast_div, Rat.cast_one, Rat.cast_natCast] at key
    rw [one_div] at key
    exact nonneg_of_mul_nonneg_right (by linarith) (inv_pos.mpr hm')
  exact_mod_cast this

end Intersection

/-! ### A uniformizer as a local equation of a prime divisor -/

section Uniformizer

variable {C : Scheme.{u}} [IsLocallyNoetherian C] [IsNormal C] [CompactSpace C]

/-- **A uniformizer is a local equation.** Let `P` be a prime divisor of a Noetherian normal
scheme `C` and `y = η_P`. There are a uniformizer `ϖ ∈ 𝔪_{C,y}` and an open `U ∋ y` on which the
rational function `ϖ` is a local equation of `P`. -/
theorem exists_isLocalEquation_single_of_eq (P : Mori.PrimeDivisor C) (y : C)
    (hy : P.genericPoint = y) :
    ∃ (U : C.Opens) (ϖ : C.presheaf.stalk y) (φ : (RationalFunctions C)ˣ), y ∈ U ∧
      ϖ ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk y) ∧
      (∀ (W : irreducibleComponents C) (hW : y ∈ W.1),
        (φ : RationalFunctions C) W = (stalkToRationalFunctions C hW).hom ϖ) ∧
      Divisor.IsLocalEquation (Finsupp.single P 1 : Divisor C) U φ := by
  classical
  subst hy
  have := P.isDiscreteValuationRing_localRing
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible P.localRing
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  set v : RationalFunctions C := fun W =>
    if hW : P.genericPoint ∈ W.1 then (stalkToRationalFunctions C hW).hom ϖ else 1
  have hv : IsUnit v := by
    refine Pi.isUnit_iff.mpr fun W => ?_
    let := (RationalFunctions.isField_stalk C W).toField
    by_cases hW : P.genericPoint ∈ W.1
    · refine isUnit_iff_ne_zero.mpr ?_
      simp only [v, dite_eq_left hW]
      intro h
      exact hϖ0 ((stalkToRationalFunctions_injective hW) (by rw [h, map_zero]))
    · simp only [v, dite_eq_right hW]
      exact isUnit_one
  set φ : (RationalFunctions C)ˣ := hv.unit
  have hφW : ∀ (W : irreducibleComponents C) (hW : P.genericPoint ∈ W.1),
      (φ : RationalFunctions C) W = (stalkToRationalFunctions C hW).hom ϖ := fun W hW => by
    simp [φ, v, dite_eq_left hW]
  have hordP : P.ord φ = 1 :=
    P.ord_eq_one_of_irreducible hϖ (hφW _ P.genericPoint_mem_component).symm
  set S : Set (Mori.PrimeDivisor C) := {E | E.ord φ ≠ 0 ∧ E ≠ P}
  have hS : S.Finite := (finite_ord_ne_zero φ).subset fun E hE => hE.1
  set T : Set C := ⋃ E ∈ S, E.support
  have hT : IsClosed T :=
    hS.isClosed_biUnion fun E _ => E.idealSheaf.support.isClosed
  refine ⟨⟨Tᶜ, hT.isOpen_compl⟩, ϖ, φ, ?_, ?_, hφW, ?_⟩
  · change P.genericPoint ∉ T
    intro h
    obtain ⟨E, hE, hPE⟩ := Set.mem_iUnion₂.mp h
    exact hE.2 (MMP.Threefold.Mori.primeDivisor_eq_of_genericPoint_mem_support E P hPE)
  · exact (IsLocalRing.mem_maximalIdeal ϖ).mpr hϖ.not_isUnit
  · intro E ⟨x, hxE, hxU⟩
    by_cases hEP : E = P
    · subst hEP
      rw [DivisorWithCoeffs.coeff_single_self, hordP]
    · rw [DivisorWithCoeffs.coeff_single_of_ne (Ne.symm hEP)]
      by_contra h
      exact hxU (Set.mem_iUnion₂.mpr ⟨E, ⟨Ne.symm h, hEP⟩, hxE⟩)

end Uniformizer

/-! ### The pull-back of a prime divisor along the fibres -/

section FibreDivisor

variable {C : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian C]
  [IsNormal C] (f : X ⟶ C) {B : Divisor C}
  (hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ B.supp)

omit [IsLocallyNoetherian X] [IsNormal X] in
include hB in
/-- The pull-back `f^*_i φ` of a local equation `φ` whose component is the image of an element
`ϖ ∈ 𝒪_{C,f(x)}` is the image of `f^♯ ϖ ∈ 𝒪_{X,x}`, for every point `x` of the component `X_i`. -/
theorem pullbackComponent_val_eq_stalkMap {U : C.Opens} {φ : (RationalFunctions C)ˣ}
    (hφ : B.IsLocalEquation U φ) {x : X} {W : irreducibleComponents C} (hW : f x ∈ W.1)
    (ϖ : C.presheaf.stalk (f x))
    (hϖ : (φ : RationalFunctions C) W = (stalkToRationalFunctions C hW).hom ϖ)
    {Z : irreducibleComponents X} (hx : x ∈ Z.1) (hZ : f (componentGenericPoint X Z) ∈ U) :
    (pullbackComponent f hB hφ Z hZ : X.presheaf.stalk (componentGenericPoint X Z)) =
      (stalkToRationalFunctions X hx).hom ((f.stalkMap x).hom ϖ) := by
  have s : componentGenericPoint X Z ⤳ x :=
    (isGenericPoint_componentGenericPoint X Z).specializes hx
  have fs : f (componentGenericPoint X Z) ⤳ f x := s.map f.continuous
  have hW' := mem_pointComponent (f (componentGenericPoint X Z))
  have hWW : W = pointComponent (f (componentGenericPoint X Z)) :=
    eq_of_mem_irreducibleComponents hW (fs.mem_closed (isClosed_of_mem_irreducibleComponents _
      (pointComponent (f (componentGenericPoint X Z))).2) hW')
  obtain ⟨a, ha⟩ := hφ.exists_unit_stalk hZ (hB Z) hW'
  rw [pullbackComponent_eq hB hφ hZ hW' a ha]
  have hab : a.val = (C.presheaf.stalkSpecializes fs).hom ϖ := by
    apply stalkToRationalFunctions_injective hW'
    rw [ha]
    subst hWW
    rw [hϖ]
    change _ = (C.presheaf.stalkSpecializes fs ≫ C.presheaf.stalkSpecializes _).hom ϖ
    rw [TopCat.Presheaf.stalkSpecializes_comp]
    rfl
  change (f.stalkMap _).hom a.val = _
  rw [hab, Scheme.Hom.stalkSpecializes_stalkMap_apply f _ x s ϖ]
  rfl

/-- The pull-back `F = f^*B` has, on `f⁻¹(U)`, the local equation whose components are the
pull-backs `f^*_i φ` of a local equation `φ` of `B` on `U`. -/
theorem exists_isLocalEquation_of_isPullback {F : Divisor X} (hF : B.IsPullback f hB F)
    {U : C.Opens} {φ : (RationalFunctions C)ˣ} (hφ : B.IsLocalEquation U φ) :
    ∃ ψ : (RationalFunctions X)ˣ, F.IsLocalEquation (f ⁻¹ᵁ U) ψ ∧
      ∀ (Z : irreducibleComponents X) (hZ : f (componentGenericPoint X Z) ∈ U),
        (ψ : RationalFunctions X) Z = pullbackComponent f hB hφ Z hZ := by
  classical
  refine ⟨(RationalFunctions.unitsEquiv X).symm fun Z =>
    if hZ : f (componentGenericPoint X Z) ∈ U then pullbackComponent f hB hφ Z hZ else 1,
    fun E hE => ?_, fun Z hZ => ?_⟩
  · rw [hF U φ hφ E hE, PrimeDivisor.ord_eq_ordUnit]
    congr 1
    ext
    symm
    change ((if hZ : f (componentGenericPoint X E.component) ∈ U then
      pullbackComponent f hB hφ E.component hZ else 1 :
        (X.presheaf.stalk (componentGenericPoint X E.component))ˣ).val) = _
    rw [dite_eq_left (E.map_componentGenericPoint_mem f hE)]
  · change ((if hZ : f (componentGenericPoint X Z) ∈ U then
      pullbackComponent f hB hφ Z hZ else 1 :
        (X.presheaf.stalk (componentGenericPoint X Z))ˣ).val) = _
    rw [dite_eq_left hZ]

omit [IsLocallyNoetherian C] [IsNormal C] in
/-- The order of vanishing along a prime divisor `E` of the image of an element of the maximal
ideal of `𝒪_{X,E}` is positive. -/
theorem PrimeDivisor.ordUnit_pos_of_mem_maximalIdeal (E : Mori.PrimeDivisor X)
    {u : (X.presheaf.stalk (componentGenericPoint X E.component))ˣ} {b : E.localRing}
    (hb : b ∈ IsLocalRing.maximalIdeal E.localRing) (hu : E.toComponent.hom b = u) :
    0 < E.ordUnit u := by
  have := E.isDiscreteValuationRing_localRing
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [map_zero] at hu
    exact u.ne_zero hu.symm
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible E.localRing
  obtain ⟨n, w, hbw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  have hn : n ≠ 0 := by
    rintro rfl
    rw [pow_zero, mul_one] at hbw
    exact (IsLocalRing.mem_maximalIdeal b).mp hb (hbw ▸ w.isUnit)
  have h := E.valuation_eq_exp_ordUnit u
  rw [← hu, hbw, map_mul, map_pow, map_mul, map_pow, E.valuation_toComponent_of_isUnit w.isUnit,
    E.valuation_toComponent_of_irreducible hϖ, one_mul, ← WithZero.exp_nsmul] at h
  have := WithZero.exp_injective h
  rw [← this]
  simpa using Nat.pos_of_ne_zero hn

variable [CompactSpace C]

/-- **The fibre lies in the support of the fibre divisor.** If `F = f^*P` for a prime divisor `P`
of `C`, every point of `X` over `η_P` lies in `Supp F`. -/
theorem mem_supp_of_isPullback_single (P : Mori.PrimeDivisor C)
    {hB : ∀ Z : irreducibleComponents X,
      f (componentGenericPoint X Z) ∉ DivisorWithCoeffs.supp (Finsupp.single P 1 : Divisor C)}
    {F : Divisor X} (hF : Divisor.IsPullback f (Finsupp.single P 1 : Divisor C) hB F) {x : X}
    (hx : f x = P.genericPoint) : x ∈ F.supp := by
  obtain ⟨U, ϖ, φ, hyU, hϖm, hφW, hφ⟩ := exists_isLocalEquation_single_of_eq P (f x) hx.symm
  obtain ⟨ψ, hψ, hψZ⟩ := exists_isLocalEquation_of_isPullback f hB hF hφ
  by_contra hxs
  have hxZ := mem_pointComponent x
  have hZU : f (componentGenericPoint X (pointComponent x)) ∈ U :=
    (((isGenericPoint_componentGenericPoint X _).specializes hxZ).map f.continuous).mem_open
      U.isOpen hyU
  obtain ⟨u, hu⟩ := hψ.exists_unit_stalk (show x ∈ f ⁻¹ᵁ U from hyU) hxs hxZ
  have hWc := mem_pointComponent (f x)
  rw [hψZ _ hZU, pullbackComponent_val_eq_stalkMap f hB hφ hWc ϖ (hφW _ hWc) hxZ hZU] at hu
  have h := stalkToRationalFunctions_injective hxZ hu
  have hunit : IsUnit ((f.stalkMap x).hom ϖ) := h ▸ u.isUnit
  exact (IsLocalRing.mem_maximalIdeal ϖ).mp hϖm (isUnit_of_map_unit _ _ hunit)

/-- **The fibre divisor is positive along the fibre.** If `F = f^*P`, then `F` has positive
coefficient along every prime divisor `E` of `X` with `f(η_E) = η_P`. -/
theorem coeff_pos_of_isPullback_single (P : Mori.PrimeDivisor C)
    {hB : ∀ Z : irreducibleComponents X,
      f (componentGenericPoint X Z) ∉ DivisorWithCoeffs.supp (Finsupp.single P 1 : Divisor C)}
    {F : Divisor X} (hF : Divisor.IsPullback f (Finsupp.single P 1 : Divisor C) hB F)
    (E : Mori.PrimeDivisor X) (hE : f E.genericPoint = P.genericPoint) : 0 < F.coeff E := by
  obtain ⟨U, ϖ, φ, hyU, hϖm, hφW, hφ⟩ :=
    exists_isLocalEquation_single_of_eq P (f E.genericPoint) hE.symm
  have hEU : (E.support ∩ f ⁻¹ᵁ U).Nonempty := (E.genericPoint_mem_iff _).mp hyU
  rw [hF U φ hφ E hEU]
  have hWc := mem_pointComponent (f E.genericPoint)
  have h1 := pullbackComponent_val_eq_stalkMap f hB hφ hWc ϖ (hφW _ hWc)
    E.genericPoint_mem_component (E.map_componentGenericPoint_mem f hEU)
  exact PrimeDivisor.ordUnit_pos_of_mem_maximalIdeal E
    (map_nonunit (f.stalkMap E.genericPoint).hom ϖ hϖm) h1.symm

omit [CompactSpace C] in
/-- **The fibre divisor vanishes away from the fibre.** If `η_P` is a closed point and
`F = f^*P`, then `F` has coefficient zero along every prime divisor `E` with `f(η_E) ≠ η_P`. -/
theorem coeff_eq_zero_of_isPullback_single (P : Mori.PrimeDivisor C)
    (hc : IsClosed ({P.genericPoint} : Set C))
    {hB : ∀ Z : irreducibleComponents X,
      f (componentGenericPoint X Z) ∉ DivisorWithCoeffs.supp (Finsupp.single P 1 : Divisor C)}
    {F : Divisor X} (hF : Divisor.IsPullback f (Finsupp.single P 1 : Divisor C) hB F)
    (E : Mori.PrimeDivisor X) (hE : f E.genericPoint ≠ P.genericPoint) : F.coeff E = 0 := by
  set U : C.Opens := ⟨{P.genericPoint}ᶜ, hc.isOpen_compl⟩
  have hφ : Divisor.IsLocalEquation (Finsupp.single P 1 : Divisor C) U 1 := by
    rintro E' ⟨x, hxE', hxU⟩
    have hE'P : E' ≠ P := by
      rintro rfl
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, hc.closure_eq] at hxE'
      exact hxU hxE'
    rw [DivisorWithCoeffs.coeff_single_of_ne (Ne.symm hE'P), PrimeDivisor.ord_one]
  have hEU : (E.support ∩ f ⁻¹ᵁ U).Nonempty :=
    (E.genericPoint_mem_iff _).mp (show f E.genericPoint ∈ U from hE)
  rw [hF U 1 hφ E hEU, pullbackComponent_eq hB hφ _ (mem_pointComponent _) 1 (by simp), map_one,
    PrimeDivisor.ordUnit_one]

/-- **The fibre divisor is numerically trivial on the fibre.** Let `X` be `ℚ`-factorial and
`F = f^*P`. Every proper curve `γ ⊆ X` lying over `η_P` has `(F · γ) = 0`. -/
theorem intersectionNumber_eq_zero_of_isPullback_single (sX : X ⟶ Spec (.of k)) [QuasiCompact sX]
    (hX : IsQFactorial sX) (P : Mori.PrimeDivisor C)
    {hB : ∀ Z : irreducibleComponents X,
      f (componentGenericPoint X Z) ∉ DivisorWithCoeffs.supp (Finsupp.single P 1 : Divisor C)}
    {F : Divisor X} (hF : Divisor.IsPullback f (Finsupp.single P 1 : Divisor C) hB F)
    (hFq : (Divisor.toQDivisor F).IsQCartier) (γ : ProperCurve sX)
    (hγ : ∀ x : X, γ.point ⤳ x → f x = P.genericPoint) :
    (Divisor.toQDivisor F).intersectionNumber k sX γ.ι γ.dim_le hFq = 0 := by
  have := QuasiCompact.compactSpace_of_compactSpace sX
  obtain ⟨U, ϖ, φ, hyU, -, -, hφ⟩ := exists_isLocalEquation_single_of_eq P P.genericPoint rfl
  obtain ⟨ψ, hψ, -⟩ := exists_isLocalEquation_of_isPullback f hB hF hφ
  set G : Divisor X := F - principalDivisor ψ
  have hGdisj : ∀ x : X, γ.point ⤳ x → x ∉ (Divisor.toQDivisor G).supp := by
    intro x hx hmem
    rw [Divisor.supp_toQDivisor] at hmem
    obtain ⟨E, hE, hxE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hmem
    have hxU : x ∈ f ⁻¹ᵁ U := show f x ∈ U from (hγ x hx).symm ▸ hyU
    refine hE ?_
    rw [DivisorWithCoeffs.coeff_sub, hψ E ⟨x, hxE, hxU⟩, coeff_principalDivisor, sub_self]
  have hdc := Divisor.isCartier_principalDivisor ψ
  have hdq := QDivisor.isQCartier_toQDivisor hdc
  have hGq := isQCartier_of_isQFactorial sX hX (Divisor.toQDivisor G)
  have hsum : Divisor.toQDivisor F =
      Divisor.toQDivisor G + Divisor.toQDivisor (principalDivisor ψ) := by
    rw [← map_add, sub_add_cancel]
  rw [intersectionNumber_congr sX γ.ι γ.dim_le hFq (hGq.add hdq) hsum,
    QDivisor.intersectionNumber_add' k sX γ.ι γ.dim_le _ _ hGq hdq,
    intersectionNumber_eq_zero_of_disjoint sX hX _ hGq γ hGdisj, zero_add,
    QDivisor.intersectionNumber_toQDivisor k sX γ.ι γ.dim_le _ hdc hdq]
  have hiso := (Divisor.linearlyEquivalent_principalDivisor_zero ψ).divisorialSheafIso
  have := hdc.isInvertibleModule_divisorialSheaf
  have := (Divisor.isCartier_zero (X := X)).isInvertibleModule_divisorialSheaf
  have h1 : (principalDivisor ψ).degreeOn k sX γ.ι γ.dim_le hdc =
      (0 : Divisor X).degreeOn k sX γ.ι γ.dim_le Divisor.isCartier_zero :=
    degreeOn_eq_of_iso k sX γ.ι γ.dim_le hiso
  rw [h1, Divisor.degreeOn_zero', Int.cast_zero]

end FibreDivisor

/-! ### Zariski's lemma along one fibre -/

section Zariski

variable {C : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
  [IsLocallyNoetherian C] [IsNormal C] [CompactSpace C] (sX : X ⟶ Spec (.of k)) [IsProper sX]
  (f : X ⟶ C)

/-- **Zariski's lemma along a fibre.** Let `X` be `ℚ`-factorial and proper over `k`, let
`f : X ⟶ C` have connected fibres, and let `F = f^*P` be the pull-back of a prime divisor `P`
of `C` with closed generic point `c`. If `A ≥ 0` is a `ℚ`-divisor with `-A` `f`-nef, the
coefficients of `A` along the components of `f⁻¹(c)` are proportional to those of `F`: there is
`t ≥ 0` with `a_E = t m_E` for every prime divisor `E` over `c`. -/
theorem exists_coeff_eq_mul_of_isPullback_single (hX : IsQFactorial sX)
    (hfib : ∀ y : C, _root_.IsPreconnected (f ⁻¹' {y})) (P : Mori.PrimeDivisor C)
    (hc : IsClosed ({P.genericPoint} : Set C))
    {hB : ∀ Z : irreducibleComponents X,
      f (componentGenericPoint X Z) ∉ DivisorWithCoeffs.supp (Finsupp.single P 1 : Divisor C)}
    {F : Divisor X} (hF : Divisor.IsPullback f (Finsupp.single P 1 : Divisor C) hB F)
    (A : QDivisor X) (hA : 0 ≤ A) (hnef : (-A).IsRelativelyNef sX f) :
    ∃ t : ℚ, 0 ≤ t ∧ ∀ E : Mori.PrimeDivisor X, f E.genericPoint = P.genericPoint →
      A E = t * F E := by
  classical
  have := QuasiCompact.compactSpace_of_compactSpace sX
  set c := P.genericPoint
  have hover : ∀ E, F E ≠ 0 → f E.genericPoint = c := fun E hE => by
    by_contra h
    exact hE (coeff_eq_zero_of_isPullback_single f P hc hF E h)
  have hpos : ∀ E, f E.genericPoint = c → 0 < F E := fun E hE =>
    coeff_pos_of_isPullback_single f P hF E hE
  -- points over `c` stay over `c` under specialization
  have hspec : ∀ {x z : X}, f x = c → x ⤳ z → f z = c := fun {x z} hx hxz => by
    have h := hxz.map f.continuous
    rw [hx] at h
    have := specializes_iff_mem_closure.mp h
    rw [hc.closure_eq] at this
    exact this
  by_cases hS : F.support.Nonempty
  swap
  · exact ⟨0, le_rfl, fun E hE => absurd ⟨E, Finsupp.mem_support_iff.mpr (hpos E hE).ne'⟩ hS⟩
  set t : ℚ := F.support.inf' hS fun E => A E / F E
  have hFpos : ∀ E ∈ F.support, (0 : ℚ) < F E := fun E hE => by
    exact_mod_cast hpos E (hover E (Finsupp.mem_support_iff.mp hE))
  have ht0 : 0 ≤ t := (Finset.le_inf'_iff _ _).mpr fun E hE =>
    div_nonneg (hA E) (hFpos E hE).le
  set D : QDivisor X := A - t • Divisor.toQDivisor F
  have hDE : ∀ E, D E = A E - t * F E := fun E => by
    simp [D, Divisor.toQDivisor, DivisorWithCoeffs.mapCoeffs]
  have hgs : ∀ E : Mori.PrimeDivisor X, E.genericPoint ∈ E.support := fun E => by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  obtain ⟨E₀, hE₀S, hE₀t⟩ := F.support.exists_mem_eq_inf' hS (fun E => A E / F E)
  have hDE₀ : D E₀ = 0 := by
    rw [hDE, show t = A E₀ / F E₀ from hE₀t, div_mul_cancel₀ _ (hFpos E₀ hE₀S).ne', sub_self]
  have hD0 : 0 ≤ D := fun E => by
    rw [hDE]
    by_cases hE : E ∈ F.support
    · have h1 : t ≤ A E / F E := Finset.inf'_le (fun E => A E / F E) hE
      rw [le_div_iff₀ (hFpos E hE)] at h1
      change (0 : ℚ) ≤ _
      linarith
    · rw [Finsupp.notMem_support_iff.mp hE]
      simpa using hA E
  refine ⟨t, ht0, fun E hE => ?_⟩
  have hES : E ∈ F.support := Finsupp.mem_support_iff.mpr (hpos E hE).ne'
  suffices hall : ∀ E ∈ F.support, D E = 0 by
    have := hall E hES
    rw [hDE] at this
    linarith
  by_contra hcon
  push Not at hcon
  obtain ⟨E₁, hE₁S, hE₁D⟩ := hcon
  -- the fibre is the union of the components with `D = 0` and those with `D ≠ 0`
  set T₀ : Set X := ⋃ E ∈ F.support.filter (fun E => D E = 0), E.support
  set T₁ : Set X := ⋃ E ∈ F.support.filter (fun E => D E ≠ 0), E.support
  have hT₀ : IsClosed T₀ :=
    (Finset.finite_toSet _).isClosed_biUnion fun E _ => E.idealSheaf.support.isClosed
  have hT₁ : IsClosed T₁ :=
    (Finset.finite_toSet _).isClosed_biUnion fun E _ => E.idealSheaf.support.isClosed
  have hcover : f ⁻¹' {c} ⊆ T₀ ∪ T₁ := by
    intro x hx
    obtain ⟨E, hE, hxE⟩ :=
      DivisorWithCoeffs.mem_supp_iff.mp (mem_supp_of_isPullback_single f P hF hx)
    have hEF : E ∈ F.support := Finsupp.mem_support_iff.mpr hE
    by_cases h : D E = 0
    · exact Or.inl (Set.mem_iUnion₂.mpr ⟨E, Finset.mem_filter.mpr ⟨hEF, h⟩, hxE⟩)
    · exact Or.inr (Set.mem_iUnion₂.mpr ⟨E, Finset.mem_filter.mpr ⟨hEF, h⟩, hxE⟩)
  have hm₀ : (f ⁻¹' {c} ∩ T₀).Nonempty :=
    ⟨E₀.genericPoint, hover E₀ (Finsupp.mem_support_iff.mp hE₀S),
      Set.mem_iUnion₂.mpr ⟨E₀, Finset.mem_filter.mpr ⟨hE₀S, hDE₀⟩, hgs E₀⟩⟩
  have hm₁ : (f ⁻¹' {c} ∩ T₁).Nonempty :=
    ⟨E₁.genericPoint, hover E₁ (Finsupp.mem_support_iff.mp hE₁S),
      Set.mem_iUnion₂.mpr ⟨E₁, Finset.mem_filter.mpr ⟨hE₁S, hE₁D⟩, hgs E₁⟩⟩
  obtain ⟨x, -, hx₀, hx₁⟩ := isPreconnected_closed_iff.mp (hfib c) T₀ T₁ hT₀ hT₁ hcover hm₀ hm₁
  obtain ⟨E₂, hE₂, hxE₂⟩ := Set.mem_iUnion₂.mp hx₀
  obtain ⟨E₃, hE₃, hxE₃⟩ := Set.mem_iUnion₂.mp hx₁
  obtain ⟨hE₂S, hDE₂⟩ := Finset.mem_filter.mp hE₂
  obtain ⟨-, hDE₃⟩ := Finset.mem_filter.mp hE₃
  have hxD : x ∈ D.supp := DivisorWithCoeffs.mem_supp_iff.mpr ⟨E₃, hDE₃, hxE₃⟩
  have hηD : E₂.genericPoint ∉ D.supp := fun h => by
    obtain ⟨E', hE', hηE'⟩ := DivisorWithCoeffs.mem_supp_iff.mp h
    obtain rfl := MMP.Threefold.Mori.primeDivisor_eq_of_genericPoint_mem_support E' E₂ hηE'
    exact hE' hDE₂
  -- a closed point of `E₂ ∩ Supp D` and a curve through it in `E₂` leaving `Supp D`
  obtain ⟨p, ⟨hpD, hpE⟩, hp⟩ := IsClosed.exists_closed_singleton
    ((DivisorWithCoeffs.isClosed_supp D).inter E₂.idealSheaf.support.isClosed) ⟨x, hxD, hxE₂⟩
  have hηp : E₂.genericPoint ⤳ p := by
    rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact hpE
  obtain ⟨y, hηy, hyp, hyD, hy⟩ := exists_isProperCurve_of_specializes sX hηp hp
    (DivisorWithCoeffs.isClosed_supp D) hpD hηD
  set γ : ProperCurve sX := ⟨y, hy⟩
  have hγc : ∀ z : X, γ.point ⤳ z → f z = c := fun z hz =>
    hspec (hover E₂ (Finsupp.mem_support_iff.mp hE₂S)) (hηy.trans hz)
  have hcontr : γ.IsContractedBy f := fun z hz => by
    rw [hγc z (specializes_iff_mem_closure.mpr hz), hγc y (specializes_refl y)]
  have hDq := isQCartier_of_isQFactorial sX hX D
  have hDpos : 0 < D.intersectionNumber k sX γ.ι γ.dim_le hDq := by
    obtain ⟨hnn, hiff⟩ := intersectionNumber_nonneg_and_eq_zero_iff sX D hDq hD0 γ hyD
    exact lt_of_le_of_ne hnn fun h => hiff.mp h.symm p hyp hpD
  -- but `(D · γ) = (A · γ) ≤ 0`
  have hAq := isQCartier_of_isQFactorial sX hX A
  have hnAq := isQCartier_of_isQFactorial sX hX (-A)
  have hFq := isQCartier_of_isQFactorial sX hX (Divisor.toQDivisor F)
  have htFq := isQCartier_of_isQFactorial sX hX ((-t) • Divisor.toQDivisor F)
  have hF0 := intersectionNumber_eq_zero_of_isPullback_single f sX hX P hF hFq γ hγc
  have hAA := QDivisor.intersectionNumber_add' k sX γ.ι γ.dim_le A (-A) hAq hnAq
    (by rw [add_neg_cancel]; exact QDivisor.isQCartier_zero)
  rw [intersectionNumber_congr sX γ.ι γ.dim_le _ QDivisor.isQCartier_zero (add_neg_cancel A),
    intersectionNumber_zero] at hAA
  have hnef' := QDivisor.IsRelativelyNef.intersectionNumber_nonneg sX hnef hnAq γ hcontr
  rw [intersectionNumber_congr sX γ.ι γ.dim_le hDq (hAq.add htFq)
      (by rw [neg_smul, ← sub_eq_add_neg]),
    QDivisor.intersectionNumber_add' k sX γ.ι γ.dim_le _ _ hAq htFq,
    intersectionNumber_smul sX γ.ι γ.dim_le _ hFq, hF0, mul_zero, add_zero] at hDpos
  linarith

end Zariski

/-! ### Curves and vertical divisors -/

section Curve

variable {C : Scheme.{u}} [IsIntegral C]

/-- The generic point of an integral scheme lies on no prime divisor. -/
theorem genericPoint_notMem_supp {R : Type*} [Zero R] (D : DivisorWithCoeffs R C) :
    genericPoint C ∉ D.supp := by
  intro h
  obtain ⟨E, -, hE⟩ := DivisorWithCoeffs.mem_supp_iff.mp h
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hE
  have h1 : E.genericPoint ⤳ genericPoint C := specializes_iff_mem_closure.mpr hE
  have h2 : genericPoint C ⤳ E.genericPoint := (genericPoint_spec C).specializes trivial
  have heq : E.genericPoint = genericPoint C := (h1.antisymm h2).eq
  have hmax : Order.coheight (genericPoint C) = 0 :=
    Order.coheight_eq_zero.mpr fun b _ => (genericPoint_spec C).specializes trivial
  have := E.coheight_genericPoint
  rw [heq, hmax] at this
  exact zero_ne_one this

variable (hC : topologicalKrullDim C = 1)

include hC

/-- On an integral scheme of dimension one, the generic point is not closed. -/
theorem not_isClosed_genericPoint : ¬ IsClosed ({genericPoint C} : Set C) := by
  intro h
  have hsub : Subsingleton C := ⟨fun a b => by
    have ha : a ∈ closure ({genericPoint C} : Set C) :=
      specializes_iff_mem_closure.mp ((genericPoint_spec C).specializes trivial)
    have hb : b ∈ closure ({genericPoint C} : Set C) :=
      specializes_iff_mem_closure.mp ((genericPoint_spec C).specializes trivial)
    rw [h.closure_eq] at ha hb
    exact ha.trans hb.symm⟩
  have h1 := Order.krullDim_nonpos_of_subsingleton (α := C)
  rw [Stacks.AlgebraicGeometry.AmpleDimensionOne.krullDim_eq_topologicalKrullDim, hC] at h1
  exact absurd h1 (by decide)

/-- On an integral scheme of dimension one, every point other than the generic point has
coheight one. -/
theorem coheight_eq_one_of_ne_genericPoint {y : C} (hy : y ≠ genericPoint C) :
    Order.coheight y = 1 := by
  refine le_antisymm ?_ ?_
  · have := Stacks.AlgebraicGeometry.AmpleDimensionOne.coheight_le_one C hC y
    exact_mod_cast this
  · have h1 : genericPoint C ⤳ y := (genericPoint_spec C).specializes trivial
    have hlt : y < genericPoint C := lt_of_le_not_ge h1 fun h2 => by
      exact hy ((show y ⤳ genericPoint C from h2).antisymm h1).eq
    have := Order.coheight_add_one_le hlt
    exact le_trans (by simp) this

end Curve

/-- On a smooth scheme every divisor is Cartier. -/
theorem isCartier_of_isSmoothScheme {C : Scheme.{u}} {sC : C ⟶ Spec (.of k)}
    [IsLocallyNoetherian C] [IsNormal C] (hsm : IsSmoothScheme sC) (D : Divisor C) :
    D.IsCartier := by
  induction D using Finsupp.induction_linear with
  | zero => exact Divisor.isCartier_zero
  | add D D' hD hD' => exact hD.add hD'
  | single P n =>
    rw [← Finsupp.smul_single_one]
    exact (MMP.Threefold.Mori.isCartier_single_of_isSmoothScheme hsm P).zsmul n

/-- A `ℚ`-divisor `A` on `X` is *vertical* over `C` for `f : X ⟶ C` if every prime component
`E` of `A` maps to a point of `C`: `f(x) = f(η_E)` for every `x ∈ E`. -/
def QDivisor.IsVertical {C : Scheme.{u}} (f : X ⟶ C) (A : QDivisor X) : Prop :=
  ∀ E : Mori.PrimeDivisor X, A E ≠ 0 → ∀ x ∈ E.support, f x = f E.genericPoint

/-- The pull-back of a finite sum `∑ n_P P` of prime divisors is `∑ n_P f^*P`. -/
theorem isPullback_sum_smul_single {C : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian C] [IsNormal C] (f : X ⟶ C)
    (hη : ∀ (D : Divisor C) (Z : irreducibleComponents X), f (componentGenericPoint X Z) ∉ D.supp)
    (hcart : ∀ D : Divisor C, D.IsCartier) (F : Mori.PrimeDivisor C → Divisor X)
    (hF : ∀ P, Divisor.IsPullback f (Finsupp.single P 1 : Divisor C) (hη _) (F P))
    (T : Finset (Mori.PrimeDivisor C)) (n : Mori.PrimeDivisor C → ℤ) :
    Divisor.IsPullback f (∑ P ∈ T, n P • (Finsupp.single P 1 : Divisor C)) (hη _)
      (∑ P ∈ T, n P • F P) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Divisor.isPullback_zero (hη 0)
  | insert P T hP ih =>
    rw [Finset.sum_insert hP, Finset.sum_insert hP]
    exact Divisor.IsPullback.add (hcart _) (hcart _) (hη _)
      ((hF P).zsmul (hcart _) (n P) (hη _)) ih

/-! ### Effective anti-nef vertical divisors over a curve -/

/-- **An effective anti-nef vertical divisor over a curve is a fibre divisor.** Let
`f : X ⟶ C` be a surjective projective morphism from a normal `ℚ`-factorial projective variety
over a field `k` to a smooth curve over `k`, with `f_* 𝒪_X = 𝒪_C`. If `A ≥ 0` is a `ℚ`-divisor on
`X`, vertical over `C`, and `-A` is `f`-nef, then `A = f^*P` for an effective `ℚ`-divisor `P`
on `C`. -/
@[mmp "lem_fourfold_effective_antinef_vertical_curve_pullback"]
theorem exists_eq_pullback_of_isVertical_of_isRelativelyNef_neg {C : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (sC : C ⟶ Spec (.of k))
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [QuasiCompact sX]
    [IsLocallyNoetherian C] [IsNormal C] [CompactSpace C]
    (hX : IsQFactorial sX) (hXp : Mori.IsProjectiveVariety k sX)
    (hC : Mori.IsCurve k sC) (hCs : IsSmoothScheme sC)
    (f : X ⟶ C) [Surjective f] (hfp : IsProjectiveMorphism f)
    (hO : ∀ U : C.Opens, IsIso (f.app U))
    (A : QDivisor X) (hA : 0 ≤ A) (hAv : QDivisor.IsVertical f A)
    (hnef : (-A).IsRelativelyNef sX f) :
    ∃ (P : QDivisor C) (hP : P.IsQCartier)
      (hPB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ P.supp),
      0 ≤ P ∧ A = P.pullback hP hPB := by
  classical
  have : IsIntegral X := hX.1.1.toIsIntegral
  have : IsIntegral C := ((Mori.isCurve_iff k sC).mp hC).1.toIsIntegral
  have hCdim : topologicalKrullDim C = 1 := ((Mori.isCurve_iff k sC).mp hC).2
  have : IsProper f := (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mp hfp).2
  have : IsProper sX := (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mp
    ((Mori.isProjectiveVariety_iff k sX).mp hXp).2).2
  -- `f` maps the generic point of `X` to that of `C`
  have hgenX : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) = genericPoint C := by
    intro Z
    have hZ : Z.1 = Set.univ := show Z.1 ∈ ({Set.univ} : Set (Set X)) from
      (irreducibleComponents_eq_singleton (X := X)) ▸ Z.2
    have hgp := isGenericPoint_componentGenericPoint X Z
    rw [hZ] at hgp
    refine IsGenericPoint.eq ?_ (genericPoint_spec C)
    refine Set.eq_univ_of_forall fun y => ?_
    obtain ⟨x, rfl⟩ := f.surjective y
    have hx : x ∈ closure {componentGenericPoint X Z} := by rw [hgp.def]; trivial
    have := image_closure_subset_closure_image f.continuous ⟨x, hx, rfl⟩
    rwa [Set.image_singleton] at this
  have hη : ∀ (D : Divisor C) (Z : irreducibleComponents X),
      f (componentGenericPoint X Z) ∉ D.supp := fun D Z => by
    rw [hgenX]; exact genericPoint_notMem_supp D
  have hcart : ∀ D : Divisor C, D.IsCartier := isCartier_of_isSmoothScheme hCs
  have hfib : ∀ y : C, _root_.IsPreconnected (f ⁻¹' {y}) := fun y =>
    (f.isConnected_preimage_singleton_of_isIso_app hO y).isPreconnected
  -- the fibre divisors `f^*P` and the proportionality factors along them
  set F : Mori.PrimeDivisor C → Divisor X := fun P =>
    Divisor.pullback (f := f) (Finsupp.single P 1 : Divisor C) (hcart _) (hη _)
  have hF : ∀ P, Divisor.IsPullback f (Finsupp.single P 1 : Divisor C) (hη _) (F P) := fun P =>
    Divisor.isPullback_pullback (hcart _) (hη _)
  have key : ∀ P : Mori.PrimeDivisor C, ∃ t : ℚ, 0 ≤ t ∧ (IsClosed ({P.genericPoint} : Set C) →
      ∀ E : Mori.PrimeDivisor X, f E.genericPoint = P.genericPoint → A E = t * F P E) := by
    intro P
    by_cases hc : IsClosed ({P.genericPoint} : Set C)
    · obtain ⟨t, ht, h⟩ :=
        exists_coeff_eq_mul_of_isPullback_single sX f hX hfib P hc (hF P) A hA hnef
      exact ⟨t, ht, fun _ => h⟩
    · exact ⟨0, le_rfl, fun h => absurd h hc⟩
  choose t ht0 htA using key
  -- the components of `A` lie over closed points
  have hclosed : ∀ E : Mori.PrimeDivisor X, A E ≠ 0 → IsClosed ({f E.genericPoint} : Set C) := by
    intro E hE
    have himg : f '' E.support = {f E.genericPoint} := by
      refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨E.genericPoint, ?_, rfl⟩, ?_⟩
      · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
      · rintro _ ⟨x, hx, rfl⟩; exact hAv E hE x hx
    rw [← himg]
    exact f.isClosedMap _ E.idealSheaf.support.isClosed
  set T : Set (Mori.PrimeDivisor C) := {P | ∃ E, A E ≠ 0 ∧ f E.genericPoint = P.genericPoint}
  have hT : T.Finite :=
    ((A.support.finite_toSet.image fun E => f E.genericPoint).preimage
      AlgebraicGeometry.PrimeDivisor.genericPoint_injective.injOn).subset
      fun P ⟨E, hE, h⟩ => ⟨E, Finsupp.mem_support_iff.mpr hE, h⟩
  have hTc : ∀ P ∈ T, IsClosed ({P.genericPoint} : Set C) := fun P ⟨E, hE, h⟩ =>
    h ▸ hclosed E hE
  set Pd : QDivisor C := ∑ P ∈ hT.toFinset, Finsupp.single P (t P)
  have hPd : ∀ P', Pd P' = if P' ∈ T then t P' else 0 := by
    intro P'
    simp only [Pd, Finset.sum_apply', Finsupp.single_apply]
    rw [Finset.sum_ite_eq']
    simp
  have hPq : Pd.IsQCartier := by
    obtain ⟨N, hN, G, hG⟩ := MMP.Flips.exists_pos_smul_eq_toQDivisor Pd
    exact ⟨N, by exact_mod_cast hN.ne', G, hG, hcart G⟩
  have hPB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ Pd.supp :=
    fun Z => by rw [hgenX]; exact genericPoint_notMem_supp Pd
  refine ⟨Pd, hPq, hPB, fun P' => ?_, ?_⟩
  · change (0 : ℚ) ≤ Pd P'
    rw [hPd]
    split_ifs
    exacts [ht0 _, le_rfl]
  refine (QDivisor.IsPullback.pullback_eq hPq ?_).symm
  intro m hm D hD hDc
  have hDc' : ∀ P', ((D P' : ℤ) : ℚ) = m * Pd P' := fun P' => by
    rw [show ((D P' : ℤ) : ℚ) = (Divisor.toQDivisor D) P' from
      (Divisor.coeff_toQDivisor D P').symm, hD]
    simp
  have hDsum : D = ∑ P ∈ hT.toFinset, D P • (Finsupp.single P 1 : Divisor C) := by
    refine Finsupp.ext fun P' => ?_
    simp only [Finset.sum_apply', Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul,
      mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · have := hDc' P'
      rw [hPd, ite_eq_right (by simpa using h), mul_zero] at this
      exact_mod_cast this
  refine ⟨∑ P ∈ hT.toFinset, D P • F P, ?_,
    (isPullback_sum_smul_single f hη hcart F hF hT.toFinset D).of_eq hDsum.symm⟩
  refine Finsupp.ext fun E => ?_
  change (((∑ P ∈ hT.toFinset, D P • F P) E : ℤ) : ℚ) = ((m : ℤ) • A) E
  simp only [Finset.sum_apply', Finsupp.smul_apply, smul_eq_mul, Int.cast_sum, Int.cast_mul,
    zsmul_eq_mul, Int.cast_natCast]
  by_cases hEη : f E.genericPoint = genericPoint C
  · have hAE : A E = 0 := by
      by_contra h
      exact not_isClosed_genericPoint hCdim (hEη ▸ hclosed E h)
    rw [hAE, mul_zero]
    refine Finset.sum_eq_zero fun P hP => ?_
    have hP' : P ∈ T := hT.mem_toFinset.mp hP
    rw [show (F P) E = 0 from coeff_eq_zero_of_isPullback_single f P (hTc P hP') (hF P) E
      fun h => not_isClosed_genericPoint hCdim (hEη ▸ h ▸ hTc P hP'), Int.cast_zero, mul_zero]
  · set P₀ := AlgebraicGeometry.PrimeDivisor.ofCoheightOne (f E.genericPoint)
      (coheight_eq_one_of_ne_genericPoint hCdim hEη)
    have hP₀ : P₀.genericPoint = f E.genericPoint :=
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
    rw [Finset.sum_eq_single P₀]
    · by_cases hT₀ : P₀ ∈ T
      · rw [hDc', hPd, ite_eq_left hT₀, htA P₀ (hTc P₀ hT₀) E hP₀.symm]
        ring
      · have hAE : A E = 0 := by
          by_contra h
          exact hT₀ ⟨E, h, hP₀.symm⟩
        rw [hAE, hDc', hPd, ite_eq_right hT₀]
        ring
    · intro P hP hPP₀
      have hP' : P ∈ T := hT.mem_toFinset.mp hP
      rw [show (F P) E = 0 from coeff_eq_zero_of_isPullback_single f P (hTc P hP') (hF P) E
        fun h => hPP₀ (AlgebraicGeometry.PrimeDivisor.genericPoint_injective
          (h.symm.trans hP₀.symm)), Int.cast_zero, mul_zero]
    · intro hP₀T
      rw [hDc', hPd, ite_eq_right (by simpa using hP₀T)]
      ring

end MMP.Fourfold
