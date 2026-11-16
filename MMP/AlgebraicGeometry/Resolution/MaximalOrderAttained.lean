module

public import MMP.AlgebraicGeometry.Resolution.OrderRestriction
public import MMP.AlgebraicGeometry.Divisor.InvertibleSheafCartier
public import MMP.AlgebraicGeometry.Morphisms.Smooth.EtaleCoordinateCharts
public import MMP.AlgebraicGeometry.Bertini.FreeLinearSystem
public import MMP.AlgebraicGeometry.Resolution.DisjoiningSequence
public import MMP.AlgebraicGeometry.Resolution.BlowupSequence.PushforwardSmooth

/-!
# Foundational results on smoothness, orders, ampleness, valuations and Bertini

This file collects foundational results used throughout the minimal model program.

* On a smooth scheme of finite type over a field, an ideal sheaf nonzero on every irreducible
  component has bounded orders, so its maximal order along a nonempty subset `Z` is finite and
  attained, at a closed point of `Z` when `Z` is closed. The bound is local: on an affine open
  étale over `𝔸ⁿ_k` the ideal contains a nonzero polynomial `g`, and the order at every point is
  at most `deg g`.
* The Jacobian criterion over an arbitrary base `M`: a hypersurface `V(Φ) ⊆ 𝔸(σ; M)` is smooth
  of relative dimension `#σ - 1` over `M` near a point where some `∂Φ/∂z_l` does not vanish.
* A projective morphism `f : X ⟶ S` carries an `f`-ample invertible sheaf, which on integral
  `X` is `𝒪_X(A)` for a Cartier divisor `A`, and its fibres embed into projective spaces.
* The approximation theorem for finitely many pairwise distinct discrete valuation rings of a
  field.
* The analytic inverse function theorem: an analytic map with invertible derivative at `a` is a
  local analytic isomorphism near `a`.
* A morphism to affine space given by functions with linearly independent differentials at a
  point of a smooth `k`-scheme is smooth near that point.
* Bertini's theorem relative to a simple normal crossing divisor: a general member of a free
  linear system is reduced, shares no component with the divisor, and is snc together with it,
  also on an open subset of the smooth locus of a variety.

## Main results

* `MMP.Resolution.exists_multAt_eq_maxOrderAlong`
* `MMP.exists_mem_smoothOfRelativeDimension_hypersurface_of_mem_basicOpen_pderiv`
* `MMP.Foundations.IsProjective.exists_isRelativelyAmple`
* `MMP.exists_forall_valuation_sub_le_of_injective`
* `MMP.Analytic.exists_openPartialHomeomorph_analyticOnNhd_symm`
* `MMP.exists_mem_smooth_homOfVector_of_linearIndependent`
* `MMP.Threefold.Bridges.exists_dense_open_isSNC_zeroScheme_add`
* `MMP.Threefold.Bridges.exists_dense_open_isSNC_add_zeroScheme_comap_opens`

## Implementation notes

* "Finite type over `k`" is `Smooth sX` together with `QuasiCompact sX`; "nonzero on every
  irreducible component" says no irreducible component of `X` lies in the support of `I`.
* The hypersurface `V(Φ)` is the subscheme of `Scheme.IdealSheafData.ofIdealTop` of the principal
  ideal of the section `MvPolynomial.eval₂Hom … (AffineSpace.coord M) Φ`; the variables are
  indexed by a finite type `σ` with `Nat.card σ = d + 1`, so that the statement is universe
  polymorphic.
* Relative ampleness is `Stacks.RelativeAmple.IsRelativelyAmple` (ampleness over every affine
  open of the base), the strong form.
* The valuation of a discrete valuation subring `V i` is the `ℤᵐ⁰`-valued normalized valuation
  of its maximal ideal on `F`; `vᵢ(x) ≥ Nᵢ` reads `… ≤ WithZero.exp (-Nᵢ)`.
* Holomorphy is analyticity; the local isomorphism is an `OpenPartialHomeomorph`.
* The fibre `κ(x) ⊗ Ω_{X/k,x}` is written stalkwise, with the algebra structure given by the
  stalk map of the structure morphism.
* A linear system is presented by spanning sections `s₀, …, s_N`, a member by a nonzero
  coefficient vector `c` with point `MMP.Threefold.Bridges.dualPoint c` of
  `MMP.Threefold.Bridges.projectiveSpace`. The components of a member are recorded by a finite
  set `T` of prime divisors whose supports are exactly its irreducible components.

## References

* [J. Kollár, *Lectures on resolution of singularities*, Def. 3.47]
* [EGA II, 4.5, 4.6]
* [Stacks Project, Tag 01W8](https://stacks.math.columbia.edu/tag/01W8)
* [Stacks Project, Tag 01VH](https://stacks.math.columbia.edu/tag/01VH)
* [Stacks Project, Tag 07RL](https://stacks.math.columbia.edu/tag/07RL)
* [Bourbaki, *Commutative Algebra*, Ch. VI, §7, Thm. 1]
* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 2.34, 5.17
-/

@[expose] public section

universe u

/-! ### The maximal order of an ideal sheaf -/

namespace MMP.Resolution

open AlgebraicGeometry CategoryTheory

/-- Along a faithfully flat local homomorphism with `𝔪_A B = 𝔪_B` the order of an element does
not increase. -/
private theorem mult_algebraMap_le {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A]
    [IsLocalRing B] [Algebra A B] [Module.FaithfullyFlat A B]
    (hm : (IsLocalRing.maximalIdeal A).map (algebraMap A B) = IsLocalRing.maximalIdeal B)
    (a : A) : mult (algebraMap A B a) ≤ mult a := by
  refine iSup₂_le fun j hj => le_iSup₂_of_le (f := fun (j : ℕ) (_ : Ideal.span {a} ≤
    IsLocalRing.maximalIdeal A ^ j) => (j : ℕ∞)) j ?_ le_rfl
  rw [Ideal.span_singleton_le_iff_mem] at hj ⊢
  rw [← hm, ← Ideal.map_pow] at hj
  rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := B) (IsLocalRing.maximalIdeal A ^ j)]
  exact hj

/-- For an étale algebra `B` over `A`, a prime `P` of `B` over `p` satisfies `p B_P = P B_P`. -/
private theorem map_under_eq_maximalIdeal_of_etale {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.Etale A B] (P : Ideal B) [P.IsPrime] :
    (P.under A).map (algebraMap A (Localization.AtPrime P)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
  let := Localization.AtPrime.algebraOfLiesOver (P.under A) P
  have : Algebra.FormallyUnramified A (Localization.AtPrime P) :=
    Algebra.FormallyUnramified.comp A B _
  have : Algebra.FormallyUnramified (Localization.AtPrime (P.under A))
      (Localization.AtPrime P) := .of_restrictScalars A _ _
  have : Algebra.EssFiniteType A (Localization.AtPrime P) := .comp A B _
  have : Algebra.EssFiniteType (Localization.AtPrime (P.under A)) (Localization.AtPrime P) :=
    .of_comp A _ _
  rw [IsScalarTower.algebraMap_eq A (Localization.AtPrime (P.under A)) (Localization.AtPrime P),
    ← Ideal.map_map, Localization.AtPrime.map_eq_maximalIdeal,
    Algebra.FormallyUnramified.map_maximalIdeal]

/-- For an étale algebra `B` over `A` and a prime `P` of `B` over `p`, the order of `a ∈ A` at
`P` is at most its order at `p`. -/
private theorem mult_algebraMap_le_of_etale {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.Etale A B] (P : Ideal B) [P.IsPrime] (a : A) :
    mult (algebraMap B (Localization.AtPrime P) (algebraMap A B a)) ≤
      mult (algebraMap A (Localization.AtPrime (P.under A)) a) := by
  let := Localization.AtPrime.algebraOfLiesOver (P.under A) P
  have : IsLocalHom (algebraMap (Localization.AtPrime (P.under A)) (Localization.AtPrime P)) := by
    rw [RingHom.algebraMap_toAlgebra]
    exact Localization.isLocalHom_localRingHom (P.under A) P (algebraMap A B) Ideal.LiesOver.over
  have : Module.FaithfullyFlat (Localization.AtPrime (P.under A)) (Localization.AtPrime P) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  rw [← IsScalarTower.algebraMap_apply A B (Localization.AtPrime P),
    IsScalarTower.algebraMap_apply A (Localization.AtPrime (P.under A)) (Localization.AtPrime P)]
  refine mult_algebraMap_le ?_ _
  rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
    ← IsScalarTower.algebraMap_eq, map_under_eq_maximalIdeal_of_etale]

/-- On an étale algebra over `k[t₁, …, tₙ]` the order of a nonzero polynomial is at most its
total degree. -/
private theorem mult_algebraMap_le_totalDegree {k : Type*} [Field k] {n : ℕ} {B : Type*}
    [CommRing B] [Algebra (MvPolynomial (Fin n) k) B] [Algebra.Etale (MvPolynomial (Fin n) k) B]
    (P : Ideal B) [P.IsPrime] {g : MvPolynomial (Fin n) k} (hg : g ≠ 0) :
    mult (algebraMap B (Localization.AtPrime P) (algebraMap _ B g)) ≤ g.totalDegree := by
  obtain ⟨L, _, _, c, h⟩ :=
    Kollar.exists_mult_le_mult_localization_ker_eval ⟨P.under _, inferInstance⟩ g
  refine (mult_algebraMap_le_of_etale P g).trans
    (h.trans (Kollar.mult_localization_ker_eval_le_of_totalDegree_le c ?_ ?_))
  · simpa using (MvPolynomial.map_injective _ (algebraMap k L).injective).ne hg
  · exact Finset.sup_mono (MvPolynomial.support_map_subset (algebraMap k L) g)

/-- An ideal of an étale algebra `B` over a domain `A` which lies in no minimal prime of `B`
contains a nonzero element of `A`. -/
private theorem exists_ne_zero_algebraMap_mem_of_etale {A B : Type*} [CommRing A] [IsDomain A]
    [CommRing B] [Algebra A B] [Algebra.Etale A B] {J : Ideal B}
    (hJ : ∀ Q ∈ minimalPrimes B, ¬ J ≤ Q) : ∃ g : A, g ≠ 0 ∧ algebraMap A B g ∈ J := by
  by_contra! h
  obtain ⟨Q, hQ, hJQ, hdisj⟩ := Ideal.exists_le_prime_disjoint J
    ((nonZeroDivisors A).map (algebraMap A B)) (by
      rw [Set.disjoint_left]
      rintro _ hb ⟨a, ha, rfl⟩
      exact h a (nonZeroDivisors.ne_zero ha) hb)
  have hunder : Q.under A = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    by_contra ha0
    exact Set.disjoint_left.mp hdisj ha ⟨a, mem_nonZeroDivisors_of_ne_zero ha0, rfl⟩
  refine hJ Q ⟨⟨hQ, bot_le⟩, fun Q' hQ' hQ'Q => ?_⟩ hJQ
  intro q hq
  have hmax := map_under_eq_maximalIdeal_of_etale (A := A) Q
  rw [hunder, Ideal.map_bot] at hmax
  have : algebraMap B (Localization.AtPrime Q) q = 0 := by
    have := (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime Q) Q q).mpr hq
    rwa [← hmax, Ideal.mem_bot] at this
  obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff Q.primeCompl _ q).mp this
  have : (s : B) * q ∈ Q' := hs ▸ Q'.zero_mem
  exact (hQ'.1.mem_or_mem this).resolve_left fun h' => s.2 (hQ'Q h')

/-- A ring isomorphism of local rings does not increase the order of an element. -/
private theorem mult_ringEquiv_le {S T : Type*} [CommRing S] [CommRing T] [IsLocalRing S]
    [IsLocalRing T] (e : S ≃+* T) (b : S) : mult (e b) ≤ mult b := by
  refine iSup₂_le fun j hj => le_iSup₂_of_le (f := fun (j : ℕ) (_ : Ideal.span {b} ≤
      IsLocalRing.maximalIdeal _ ^ j) => (j : ℕ∞)) j ?_ le_rfl
  rw [Ideal.span_singleton_le_iff_mem] at hj ⊢
  have hm := IsLocalRing.map_maximalIdeal_le (e.symm : T →+* S)
  have := Ideal.mem_map_of_mem e.symm hj
  rw [Ideal.map_pow, RingEquiv.symm_apply_apply] at this
  exact Ideal.pow_right_mono hm j this

/-- If `a ∈ I(W)` on an affine open `W ∋ y`, the order of `I` at `y` is at most the order of `a`
in the localization of `Γ(X, W)` at the prime of `y`. -/
private theorem multAt_le_mult_of_mem {X : Scheme.{u}} (I : X.IdealSheafData) (W : X.affineOpens)
    {y : X} (hy : y ∈ W.1) {a : Γ(X, W.1)} (ha : a ∈ I.ideal W) :
    multAt I y ≤ mult (algebraMap Γ(X, W.1) (Localization.AtPrime
      (W.2.primeIdealOf ⟨y, hy⟩).asIdeal) a) := by
  letI : Algebra Γ(X, W.1) (X.presheaf.stalk y) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨y, hy⟩
  have hloc := W.2.isLocalization_stalk ⟨y, hy⟩
  set P := (W.2.primeIdealOf ⟨y, hy⟩).asIdeal
  let e := IsLocalization.algEquiv P.primeCompl (Localization.AtPrime P) (X.presheaf.stalk y)
  have hmem : (X.presheaf.germ W.1 y hy).hom a ∈ IdealSheafData.stalk I y := by
    rw [IdealSheafData.stalk_eq_map_germ I y W hy]
    exact Ideal.mem_map_of_mem _ ha
  have h1 : multAt I y ≤ mult ((X.presheaf.germ W.1 y hy).hom a) :=
    Kollar.idealOrder_antitone ((Ideal.span_singleton_le_iff_mem _).2 hmem)
  refine h1.trans ?_
  have h2 : (X.presheaf.germ W.1 y hy).hom a =
      e.toRingEquiv (algebraMap Γ(X, W.1) (Localization.AtPrime P) a) :=
    (e.commutes a).symm
  rw [h2]
  exact mult_ringEquiv_le _ _

/-- On an affine open étale over `𝔸ⁿ_k`, the orders of `I` are bounded. -/
private theorem exists_multAt_le_of_etale {k : Type u} [Field k] {X : Scheme.{u}}
    (I : X.IdealSheafData) (W : X.affineOpens) {n : ℕ}
    [Algebra (MvPolynomial (Fin n) k) Γ(X, W.1)] [Algebra.Etale (MvPolynomial (Fin n) k) Γ(X, W.1)]
    (hW : ∀ Q ∈ minimalPrimes Γ(X, W.1), ¬ I.ideal W ≤ Q) :
    ∃ N : ℕ, ∀ y ∈ W.1, multAt I y ≤ N := by
  obtain ⟨g, hg, hgI⟩ := exists_ne_zero_algebraMap_mem_of_etale (A := MvPolynomial (Fin n) k) hW
  exact ⟨g.totalDegree, fun y hy => (multAt_le_mult_of_mem I W hy hgI).trans
    (mult_algebraMap_le_totalDegree _ hg)⟩

/-- An ideal sheaf with no irreducible component in its support has, on an affine open, sections
lying in no minimal prime. -/
private theorem not_ideal_le_of_mem_minimalPrimes {X : Scheme.{u}} (I : X.IdealSheafData)
    (hI : ∀ W ∈ irreducibleComponents X, ¬ W ⊆ I.support) (W : X.affineOpens) :
    ∀ Q ∈ minimalPrimes Γ(X, W.1), ¬ I.ideal W ≤ Q := by
  intro Q hQ hle
  obtain ⟨W, hW⟩ := W
  have hW' : IsAffineOpen W := hW
  obtain ⟨y, rfl⟩ : ∃ y : PrimeSpectrum Γ(X, W), y.asIdeal = Q := ⟨⟨Q, hQ.1.1⟩, rfl⟩
  have hy : hW'.fromSpec y ∈ W := hW'.range_fromSpec.subset ⟨y, rfl⟩
  letI : Algebra Γ(X, W) (X.presheaf.stalk (hW'.fromSpec y)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨_, hy⟩
  have hloc := hW'.isLocalization_stalk ⟨_, hy⟩
  have hpy : hW'.primeIdealOf ⟨_, hy⟩ = y :=
    hW'.fromSpec.isOpenEmbedding.injective (hW'.fromSpec_primeIdealOf ⟨_, hy⟩)
  have hcomap := IsLocalization.AtPrime.under_maximalIdeal (X.presheaf.stalk (hW'.fromSpec y))
    (hW'.primeIdealOf ⟨_, hy⟩).asIdeal
  replace hcomap := hcomap.trans (congrArg PrimeSpectrum.asIdeal hpy)
  have hsupp : hW'.fromSpec y ∈ I.support := by
    rw [← IdealSheafData.stalk_le_maximalIdeal_iff_mem_support,
      IdealSheafData.stalk_eq_map_germ I _ ⟨W, hW⟩ hy, Ideal.map_le_iff_le_comap]
    exact hle.trans hcomap.ge
  obtain ⟨C, hC, hηC⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    {hW'.fromSpec y} isIrreducible_singleton
  apply hI C hC
  have hgen := hC.1.isGenericPoint_genericPoint_closure
  rw [(isClosed_of_mem_irreducibleComponents C hC).closure_eq] at hgen
  have hξη : hC.1.genericPoint ⤳ hW'.fromSpec y := by
    rw [specializes_iff_mem_closure, hgen.def]
    exact hηC rfl
  obtain ⟨y', hy'⟩ : hC.1.genericPoint ∈ Set.range hW'.fromSpec := by
    rw [hW'.range_fromSpec]
    exact hξη.mem_open W.isOpen hy
  have h1 : y' ⤳ y :=
    hW'.fromSpec.isOpenEmbedding.toIsInducing.specializes_iff.mp (by rw [hy']; exact hξη)
  have h2 : y ⤳ y' :=
    (PrimeSpectrum.le_iff_specializes y y').mp
      (hQ.2 ⟨y'.isPrime, bot_le⟩ ((PrimeSpectrum.le_iff_specializes y' y).mpr h1))
  have h3 : hW'.fromSpec y ⤳ hC.1.genericPoint := hy' ▸ h2.map hW'.fromSpec.continuous
  rw [← hgen.def]
  exact (closure_minimal (Set.singleton_subset_iff.2 (specializes_iff_mem_closure.1 h3))
    isClosed_closure).trans (closure_minimal (Set.singleton_subset_iff.2 hsupp) I.support.2)

/-- A smooth scheme over `k` is covered by affine opens étale over affine spaces `𝔸ⁿ_k`. -/
private theorem exists_etale_chart {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [Smooth sX] (x : X) :
    ∃ (W : X.affineOpens) (_ : x ∈ W.1) (n : ℕ) (_ : Algebra (MvPolynomial (Fin n) k) Γ(X, W.1)),
      Algebra.Etale (MvPolynomial (Fin n) k) Γ(X, W.1) := by
  obtain ⟨_, ⟨⟨V0, hV, rfl⟩, hxV, -⟩⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  letI : Algebra k Γ(X, V0) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appLE ⊤ V0 (by simp)).hom.toAlgebra
  have : Algebra.Smooth k Γ(X, V0) := by
    change RingHom.Smooth ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appLE ⊤ V0 (by simp)).hom
    rw [CommRingCat.hom_comp]
    exact RingHom.Smooth.comp
      (RingHom.Smooth.of_bijective
        (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.bijective)
      (HasRingHomProperty.appLE @Smooth sX ‹_› ⟨⊤, isAffineOpen_top _⟩ ⟨V0, hV⟩ _)
  letI : Algebra Γ(X, V0) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxV⟩
  have hloc := hV.isLocalization_stalk ⟨x, hxV⟩
  set p := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  obtain ⟨f, hfp, n, _, _, _⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := k) (p := p)
  have hxf : x ∈ X.basicOpen f := by
    rw [Scheme.mem_basicOpen _ _ _ hxV]
    by_contra h
    apply hfp
    rw [← IsLocalization.AtPrime.under_maximalIdeal (X.presheaf.stalk x) p]
    exact (IsLocalRing.mem_maximalIdeal _).2 h
  have hloc' := hV.isLocalization_basicOpen f
  let e := IsLocalization.algEquiv (Submonoid.powers f) (Localization.Away f)
    Γ(X, X.basicOpen f)
  letI : Algebra (MvPolynomial (Fin n) k) Γ(X, X.basicOpen f) :=
    (e.toRingHom.comp (algebraMap _ (Localization.Away f))).toAlgebra
  let e' : Localization.Away f ≃ₐ[MvPolynomial (Fin n) k] Γ(X, X.basicOpen f) :=
    { e.toRingEquiv with commutes' := fun _ => rfl }
  exact ⟨⟨X.basicOpen f, hV.basicOpen f⟩, hxf, n, _, Algebra.Etale.of_equiv e'⟩

/-- The orders of `I` are bounded on all of `X`. -/
private theorem exists_multAt_le_natCast {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [Smooth sX] [QuasiCompact sX] (I : X.IdealSheafData)
    (hI : ∀ W ∈ irreducibleComponents X, ¬ W ⊆ I.support) :
    ∃ N : ℕ, ∀ x : X, multAt I x ≤ N := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have key : ∀ x : X, ∃ W : X.affineOpens, x ∈ W.1 ∧ ∃ N : ℕ, ∀ y ∈ W.1, multAt I y ≤ N := by
    intro x
    obtain ⟨W, hxW, n, _, _⟩ := exists_etale_chart sX x
    exact ⟨W, hxW, exists_multAt_le_of_etale (k := k) (n := n) I W
      (not_ideal_le_of_mem_minimalPrimes I hI W)⟩
  choose W hxW N hN using key
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => ((W x).1 : Set X))
    (fun x => (W x).1.isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hxW x⟩)
  refine ⟨t.sup N, fun y => ?_⟩
  obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
  exact (hN x y hy).trans (by exact_mod_cast Finset.le_sup (f := N) hx)

/-- If a finitely generated ideal `J` of `R` maps into `𝔪^r` in the localization at a prime `p`,
then some `u ∉ p` multiplies `J` into `p ^ r`. -/
private theorem exists_notMem_forall_mul_mem_pow {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [IsLocalRing S] (p : Ideal R) [p.IsPrime] [IsLocalization.AtPrime S p]
    {J : Ideal R} (hJ : J.FG) {r : ℕ}
    (h : J.map (algebraMap R S) ≤ IsLocalRing.maximalIdeal S ^ r) :
    ∃ u ∉ p, ∀ f ∈ J, u * f ∈ p ^ r := by
  classical
  have hS : IsLocalRing.maximalIdeal S ^ r = (p ^ r).map (algebraMap R S) := by
    rw [Ideal.map_pow, IsLocalization.AtPrime.map_eq_maximalIdeal]
  obtain ⟨s, rfl⟩ := hJ
  have key : ∀ t : Finset R, (t : Set R) ⊆ s → ∃ u ∉ p, ∀ f ∈ t, u * f ∈ p ^ r := by
    intro t
    induction t using Finset.induction_on with
    | empty => exact fun _ => ⟨1, p.ne_top_iff_one.mp ‹p.IsPrime›.ne_top, by simp⟩
    | insert a t ha ih =>
      intro hts
      rw [Finset.coe_insert, Set.insert_subset_iff] at hts
      obtain ⟨u, hu, hut⟩ := ih hts.2
      have hmem : algebraMap R S a ∈ (p ^ r).map (algebraMap R S) :=
        hS ▸ h (Ideal.mem_map_of_mem _ (Ideal.subset_span hts.1))
      obtain ⟨⟨b, c⟩, hbc⟩ := (IsLocalization.mem_map_algebraMap_iff p.primeCompl S).mp hmem
      simp only [← map_mul] at hbc
      obtain ⟨d, hd⟩ := (IsLocalization.eq_iff_exists p.primeCompl S).mp hbc
      refine ⟨d * c * u, ?_, ?_⟩
      · exact (‹p.IsPrime›.mul_notMem (‹p.IsPrime›.mul_notMem d.2 c.2) hu)
      · intro f hf
        rw [Finset.mem_insert] at hf
        rcases hf with rfl | hf
        · have : d * c * u * f = u * (d * b) := by
            rw [show d * c * u * f = u * (d * (f * c)) by ring, hd]
          rw [this]; exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ b.2)
        · rw [mul_assoc]; exact Ideal.mul_mem_left _ _ (hut f hf)
  obtain ⟨u, hu, hut⟩ := key s.finite_toSet.toFinset (by simp)
  refine ⟨u, hu, fun f hf => ?_⟩
  have : Ideal.span (s : Set R) ≤ Submodule.comap (LinearMap.mulLeft R u) (p ^ r) := by
    rw [Ideal.span_le]
    intro f hf
    exact hut f (by simpa using hf)
  exact this hf

/-- Along a closed `Z`, the order at a point `z ∈ Z` is at most the order at some closed point of
`X` lying in `Z`. -/
private theorem exists_isClosed_singleton_le_multAt {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (I : X.IdealSheafData)
    {Z : Set X} (hZ : IsClosed Z) {z : X} (hz : z ∈ Z) (hfin : multAt I z ≠ ⊤) :
    ∃ x ∈ Z, IsClosed ({x} : Set X) ∧ multAt I z ≤ multAt I x := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  obtain ⟨_, ⟨⟨V0, hV, rfl⟩, hzV, -⟩⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
  set V : X.affineOpens := ⟨V0, hV⟩
  lift multAt I z to ℕ using hfin with r hr
  letI : Algebra Γ(X, V.1) (X.presheaf.stalk z) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨z, hzV⟩
  have hloc := hV.isLocalization_stalk ⟨z, hzV⟩
  set p := (hV.primeIdealOf ⟨z, hzV⟩).asIdeal
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsNoetherianRing Γ(X, V.1) := IsLocallyNoetherian.component_noetherian V
  have hJ : (I.ideal V).FG := IsNoetherian.noetherian _
  have hmap : (I.ideal V).map (algebraMap Γ(X, V.1) (X.presheaf.stalk z)) ≤
      IsLocalRing.maximalIdeal _ ^ r := by
    have := le_pow_of_le_idealOrder (R := X.presheaf.stalk z) (I := IdealSheafData.stalk I z)
      (m := r) hr.le
    rwa [IdealSheafData.stalk_eq_map_germ I z V hzV] at this
  obtain ⟨u, hu, hut⟩ := exists_notMem_forall_mul_mem_pow p hJ hmap
  -- `p` is the set of sections whose germ at `z` is not a unit
  have hp : ∀ a : Γ(X, V.1), a ∈ p ↔ (X.presheaf.germ V.1 z hzV).hom a ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk z) := by
    intro a
    rw [← IsLocalization.AtPrime.under_maximalIdeal (X.presheaf.stalk z) p]
    rfl
  have hzu : z ∈ X.basicOpen u := by
    rw [Scheme.mem_basicOpen _ _ _ hzV]
    by_contra h
    exact hu ((hp u).2 ((IsLocalRing.mem_maximalIdeal _).2 h))
  have hT : (closure {z} ∩ (X.basicOpen u : Set X)).Nonempty := ⟨z, subset_closure rfl, hzu⟩
  obtain ⟨x, ⟨hxz, hxu⟩, hxc⟩ := nonempty_inter_closedPoints hT
    (isClosed_closure.isLocallyClosed.inter (X.basicOpen u).isOpen.isLocallyClosed)
  have hxV : x ∈ V.1 := X.basicOpen_le u hxu
  have hspec : z ⤳ x := specializes_iff_mem_closure.mpr hxz
  refine ⟨x, closure_minimal (Set.singleton_subset_iff.mpr hz) hZ hxz, hxc, ?_⟩
  -- every germ at `x` of an element of `p` lies in the maximal ideal
  have hpx : p.map (X.presheaf.germ V.1 x hxV).hom ≤ IsLocalRing.maximalIdeal _ := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hunit
    have := hunit.map (X.presheaf.stalkSpecializes hspec).hom
    rw [← CommRingCat.comp_apply, X.presheaf.germ_stalkSpecializes] at this
    exact ((IsLocalRing.mem_maximalIdeal _).1 ((hp a).1 ha)) this
  have hux : IsUnit ((X.presheaf.germ V.1 x hxV).hom u) :=
    (Scheme.mem_basicOpen _ _ _ hxV).1 hxu
  have hle : IdealSheafData.stalk I x ≤ IsLocalRing.maximalIdeal _ ^ r := by
    rw [IdealSheafData.stalk_eq_map_germ I x V hxV, Ideal.map_le_iff_le_comap]
    intro f hf
    rw [Ideal.mem_comap, ← Ideal.unit_mul_mem_iff_mem _ hux,
      ← map_mul (X.presheaf.germ V.1 x hxV).hom]
    have h1 := Ideal.mem_map_of_mem (X.presheaf.germ V.1 x hxV).hom (hut f hf)
    rw [Ideal.map_pow] at h1
    exact Ideal.pow_right_mono hpx r h1
  exact le_iSup₂_of_le (f := fun (j : ℕ) (_ : IdealSheafData.stalk I x ≤
    IsLocalRing.maximalIdeal _ ^ j) => (j : ℕ∞)) r hle le_rfl

/-- On a smooth scheme of finite type over a field, with `I` nonzero on every irreducible
component, the maximal order of `I` along a nonempty subset `Z` is finite and attained at a point
of `Z`; if `Z` is closed it is attained at a closed point of `X` in `Z`. -/
@[mmp "lem_kr3c_maximal_order_attained"]
public theorem exists_multAt_eq_maxOrderAlong {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [Smooth sX] [QuasiCompact sX] (I : X.IdealSheafData)
    (hI : ∀ W ∈ irreducibleComponents X, ¬ W ⊆ I.support) {Z : Set X} (hZ : Z.Nonempty) :
    maxOrderAlong I Z ≠ ⊤ ∧ (∃ z ∈ Z, multAt I z = maxOrderAlong I Z) ∧
      (IsClosed Z → ∃ x ∈ Z, IsClosed ({x} : Set X) ∧ multAt I x = maxOrderAlong I Z) := by
  obtain ⟨N, hN⟩ := exists_multAt_le_natCast sX I hI
  have hfin : (multAt I '' Z).Finite :=
    ((Finset.range (N + 1)).image (fun n : ℕ => (n : ℕ∞))).finite_toSet.subset (by
      rintro _ ⟨x, -, rfl⟩
      have h := hN x
      lift multAt I x to ℕ using ne_top_of_le_ne_top (ENat.coe_ne_top N) h with m
      simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio,
        Nat.cast_inj, exists_eq_right]
      exact Nat.lt_succ_of_le (ENat.coe_le_coe.mp h))
  obtain ⟨_, ⟨z, hzZ, rfl⟩, hmax⟩ := Set.exists_max_image _ id hfin (hZ.image _)
  have hz : multAt I z = maxOrderAlong I Z :=
    le_antisymm (le_iSup₂ (f := fun x (_ : x ∈ Z) => multAt I x) z hzZ)
      (iSup₂_le fun y hy => hmax _ ⟨y, hy, rfl⟩)
  have hzN : multAt I z ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top N) (hN z)
  refine ⟨hz ▸ hzN, ⟨z, hzZ, hz⟩, fun hZc => ?_⟩
  obtain ⟨x, hxZ, hxc, hle⟩ := exists_isClosed_singleton_le_multAt sX I hZc hzZ hzN
  exact ⟨x, hxZ, hxc, le_antisymm (hz ▸ hmax _ ⟨x, hxZ, rfl⟩) (hz ▸ hle)⟩

end MMP.Resolution

/-! ### The Jacobian criterion for a hypersurface over an arbitrary base -/

namespace MMP

open MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/-- If `C ≅ A[σ] ⧸ (Φ)` and `B` is the localization of `C` away from the image `c` of
`∂Φ/∂z_l`, then `B` is a standard smooth `A`-algebra of relative dimension `#σ - 1`. -/
private theorem isStandardSmoothOfRelativeDimension_localizationAway_quotient_span
    {A C B : Type*} [CommRing A] [CommRing C] [CommRing B] [Algebra A C] [Algebra A B]
    [Algebra C B] [IsScalarTower A C B] {σ : Type*} [Finite σ] {d : ℕ} (hσ : Nat.card σ = d + 1)
    (Φ : MvPolynomial σ A) (l : σ)
    (e : (MvPolynomial σ A ⧸ Ideal.span (Set.range fun _ : Unit ↦ Φ)) ≃ₐ[A] C)
    (c : C) (hc : e (Ideal.Quotient.mk _ (pderiv l Φ)) = c) [IsLocalization.Away c B] :
    Algebra.IsStandardSmoothOfRelativeDimension d A B := by
  classical
  let P₀ := Algebra.PreSubmersivePresentation.naive (R := A) (v := fun _ : Unit ↦ Φ)
    (fun _ ↦ l) (fun _ _ _ ↦ rfl)
  let P₁ := P₀.ofAlgEquiv e
  let Q := Algebra.PreSubmersivePresentation.localizationAway B c
  let R := Q.comp P₁
  have hP₀ : P₀.jacobian = Ideal.Quotient.mk _ (pderiv l Φ) := by
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, Matrix.det_unique,
      Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
    rfl
  have hR : R.jacobian = algebraMap C B c * algebraMap C B c := by
    simp only [R, Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
      Q, Algebra.PreSubmersivePresentation.localizationAway_jacobian, P₁,
      Algebra.PreSubmersivePresentation.jacobian_ofAlgEquiv, hP₀, Algebra.smul_def, hc]
  let S : Algebra.SubmersivePresentation A B (Unit ⊕ σ) (Unit ⊕ Unit) :=
    ⟨R, by
      rw [hR]
      exact (IsLocalization.Away.algebraMap_isUnit c).mul (IsLocalization.Away.algebraMap_isUnit c)⟩
  refine S.isStandardSmoothOfRelativeDimension ?_
  simp [Algebra.Presentation.dimension, S, R, hσ]
  omega

/-- Over an affine base `S`, the basic open `D(∂Φ/∂z_l)` of the hypersurface cut out by
an ideal sheaf with global ideal `(Φ)` is smooth of relative dimension `#σ - 1` over `S`. -/
private theorem smoothOfRelativeDimension_basicOpen_subscheme_of_isAffine {S : Scheme.{u}}
    [IsAffine S] {σ : Type u} [Finite σ] {d : ℕ}
    (hσ : Nat.card σ = d + 1) (Φ : MvPolynomial σ Γ(S, ⊤)) (l : σ)
    (J : 𝔸(σ; S).IdealSheafData)
    (hJ : J.ideal ⟨⊤, isAffineOpen_top _⟩ =
      Ideal.span {eval₂Hom (𝔸(σ; S) ↘ S).appTop.hom (AffineSpace.coord S) Φ}) :
    SmoothOfRelativeDimension d ((J.subschemeι ⁻¹ᵁ 𝔸(σ; S).basicOpen
      (eval₂Hom (𝔸(σ; S) ↘ S).appTop.hom (AffineSpace.coord S) (pderiv l Φ))).ι ≫
        J.subschemeι ≫ 𝔸(σ; S) ↘ S) := by
  set ψ := eval₂Hom (𝔸(σ; S) ↘ S).appTop.hom (AffineSpace.coord S) with hψ
  set ι := J.subschemeι
  set c := ι.appTop (ψ (pderiv l Φ)) with hc
  have hK : ι ⁻¹ᵁ 𝔸(σ; S).basicOpen (ψ (pderiv l Φ)) = J.subscheme.basicOpen c :=
    Scheme.preimage_basicOpen_top _ _
  have : IsAffine J.subscheme := isAffine_of_isAffineHom ι
  have hKa : IsAffineOpen (ι ⁻¹ᵁ 𝔸(σ; S).basicOpen (ψ (pderiv l Φ))) :=
    hK ▸ (isAffineOpen_top _).basicOpen c
  have : IsAffine (ι ⁻¹ᵁ 𝔸(σ; S).basicOpen (ψ (pderiv l Φ))).toScheme := hKa
  rw [HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension d)]
  apply RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
  set K := ι ⁻¹ᵁ 𝔸(σ; S).basicOpen (ψ (pderiv l Φ))
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, CommRingCat.hom_comp]
  have hψ' : CommRingCat.ofHom ψ =
      (Scheme.ΓSpecIso _).inv ≫ (AffineSpace.isoOfIsAffine σ S).hom.appTop := by
    rw [AffineSpace.isoOfIsAffine_hom_appTop]
    simp [ψ]
  have hbij : Function.Bijective ψ := by
    have : IsIso (AffineSpace.isoOfIsAffine σ S).hom.appTop :=
      inferInstanceAs (IsIso (Scheme.Γ.map (AffineSpace.isoOfIsAffine σ S).hom.op))
    have : IsIso (CommRingCat.ofHom ψ) := by rw [hψ']; infer_instance
    exact ConcreteCategory.bijective_of_isIso (CommRingCat.ofHom ψ)
  let ψe := RingEquiv.ofBijective ψ hbij
  have hsurj : Function.Surjective ι.appTop.hom :=
    J.subschemeι_app_surjective ⟨⊤, isAffineOpen_top _⟩
  have hker : RingHom.ker ι.appTop.hom = Ideal.span {ψ Φ} :=
    (J.ker_subschemeι_app ⟨⊤, isAffineOpen_top _⟩).trans hJ
  letI alg1 : Algebra Γ(S, ⊤) Γ(J.subscheme, ⊤) :=
    (ι.appTop.hom.comp (𝔸(σ; S) ↘ S).appTop.hom).toAlgebra
  letI alg2 : Algebra Γ(J.subscheme, ⊤) Γ(K, ⊤) := K.ι.appTop.hom.toAlgebra
  letI alg3 : Algebra Γ(S, ⊤) Γ(K, ⊤) :=
    (K.ι.appTop.hom.comp (ι.appTop.hom.comp (𝔸(σ; S) ↘ S).appTop.hom)).toAlgebra
  haveI : IsScalarTower Γ(S, ⊤) Γ(J.subscheme, ⊤) Γ(K, ⊤) := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsLocalization.Away c Γ(K, ⊤) :=
    (isAffineOpen_top J.subscheme).isLocalization_of_eq_basicOpen c
      (homOfLE le_top : K.ι ''ᵁ ⊤ ⟶ ⊤) (by rw [Scheme.Opens.ι_image_top, hK])
  let f : MvPolynomial σ Γ(S, ⊤) →ₐ[Γ(S, ⊤)] Γ(J.subscheme, ⊤) :=
    { ι.appTop.hom.comp ψ with commutes' := fun a ↦ by simp [ψ, RingHom.algebraMap_toAlgebra] }
  have hfs : Function.Surjective f := hsurj.comp hbij.2
  have hfker : Ideal.span (Set.range fun _ : Unit ↦ Φ) = RingHom.ker f := by
    change _ = RingHom.ker (ι.appTop.hom.comp ψe.toRingHom)
    rw [← RingHom.comap_ker, hker, Set.range_const]
    ext x
    simp only [Ideal.mem_comap, Ideal.mem_span_singleton]
    exact (map_dvd_iff ψe).symm
  let e := (Ideal.quotientEquivAlgOfEq Γ(S, ⊤) hfker).trans
    (Ideal.quotientKerAlgEquivOfSurjective hfs)
  exact isStandardSmoothOfRelativeDimension_localizationAway_quotient_span hσ Φ l e c rfl

/-- On global sections, the base change `𝔸(σ; S) ⟶ 𝔸(σ; T)` of `f : S ⟶ T` sends the function
`P(z)` to the function `(f^* P)(z)` obtained by pulling back the coefficients of `P`. -/
private theorem appTop_map_eval₂Hom {S T : Scheme.{u}} {σ : Type u} (f : S ⟶ T)
    (P : MvPolynomial σ Γ(T, ⊤)) :
    (AffineSpace.map σ f).appTop (eval₂Hom (𝔸(σ; T) ↘ T).appTop.hom (AffineSpace.coord T) P) =
      eval₂Hom (𝔸(σ; S) ↘ S).appTop.hom (AffineSpace.coord S) (P.map f.appTop.hom) := by
  have h := congr(Scheme.Hom.appTop $(AffineSpace.map_over (n := σ) f))
  simp only [Scheme.Hom.comp_appTop] at h
  change ((AffineSpace.map σ f).appTop.hom.comp
      (eval₂Hom (𝔸(σ; T) ↘ T).appTop.hom (AffineSpace.coord T))) P =
    ((eval₂Hom (𝔸(σ; S) ↘ S).appTop.hom (AffineSpace.coord S)).comp
      (MvPolynomial.map f.appTop.hom)) P
  refine DFunLike.congr_fun (MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun i ↦ ?_)) P
  · simpa only [RingHom.comp_apply, eval₂Hom_C, MvPolynomial.map_C, CommRingCat.hom_comp]
      using congr(($h).hom a)
  · simp only [RingHom.comp_apply, eval₂Hom_X', MvPolynomial.map_X, AffineSpace.map_appTop_coord]

/-- Restricting the closed subscheme `V(g)`, for a global function `g` on `Y`, along an open
immersion `j : X ⟶ Y` from an affine scheme gives `V(j^* g)`. -/
private theorem ideal_comap_ofIdealTop_span_singleton {X Y : Scheme.{u}} [IsAffine X] (j : X ⟶ Y)
    [IsOpenImmersion j] (g : Γ(Y, ⊤)) :
    ((Scheme.IdealSheafData.ofIdealTop (Ideal.span {g})).comap j).ideal
      ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {j.appTop g} := by
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_span, Set.image_singleton]
  have key : (j.appIso ⊤).hom ((Y.presheaf.map (homOfLE le_top).op).hom g) = j.appTop g := by
    rw [Scheme.Hom.appIso_hom', ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
    show _ = (j.app ⊤) _
    rw [Scheme.Hom.app_eq_appLE]
    rfl
  ext y
  simp only [Ideal.mem_comap, Ideal.mem_span_singleton]
  rw [← key, ← map_dvd_iff (j.appIso ⊤).commRingCatIsoToRingEquiv]
  exact iff_of_eq (congrArg (_ ∣ ·) ((j.appIso ⊤).commRingCatIsoToRingEquiv.apply_symm_apply y))

/-- The hypersurface statement for an ideal sheaf `I` equal to `V(Φ)`. -/
private theorem exists_smoothOfRelativeDimension_subscheme
    {M : Scheme.{u}} {σ : Type u} [Finite σ] {d : ℕ} (hσ : Nat.card σ = d + 1)
    (Φ : MvPolynomial σ Γ(M, ⊤)) (I : 𝔸(σ; M).IdealSheafData)
    (hI : I = Scheme.IdealSheafData.ofIdealTop (Ideal.span
      {MvPolynomial.eval₂Hom (𝔸(σ; M) ↘ M).appTop.hom (AffineSpace.coord M) Φ}))
    (w : I.subscheme) (l : σ)
    (hw : I.subschemeι w ∈ 𝔸(σ; M).basicOpen
          (MvPolynomial.eval₂Hom (𝔸(σ; M) ↘ M).appTop.hom (AffineSpace.coord M)
            (MvPolynomial.pderiv l Φ))) :
    ∃ U : I.subscheme.Opens, w ∈ U ∧
      SmoothOfRelativeDimension d (U.ι ≫ I.subschemeι ≫ 𝔸(σ; M) ↘ M) := by
  obtain ⟨W, hW, hxW⟩ : ∃ W : M.Opens, IsAffineOpen W ∧
      (𝔸(σ; M) ↘ M) (I.subschemeι w) ∈ W := by
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ := M.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ ((𝔸(σ; M) ↘ M) (I.subschemeι w))) isOpen_univ
    exact ⟨W, hW, hxW⟩
  have : IsAffine W := hW
  let j := AffineSpace.map σ W.ι
  have : IsOpenImmersion j := MorphismProperty.of_isPullback
    (P := @IsOpenImmersion) (AffineSpace.isPullback_map (n := σ) W.ι).flip
    (inferInstance : IsOpenImmersion W.ι)
  have := smoothOfRelativeDimension_basicOpen_subscheme_of_isAffine hσ (Φ.map W.ι.appTop.hom) l
    (I.comap j) (by rw [hI, ideal_comap_ofIdealTop_span_singleton, appTop_map_eval₂Hom])
  set K := (I.comap j).subschemeι ⁻¹ᵁ 𝔸(σ; W).basicOpen
    (eval₂Hom (𝔸(σ; W) ↘ W).appTop.hom (AffineSpace.coord W) (pderiv l (Φ.map W.ι.appTop.hom)))
  let q : (I.comap j).subscheme ⟶ I.subscheme := (I.comapIso j).hom ≫ pullback.snd j I.subschemeι
  have : IsOpenImmersion q := by dsimp [q]; infer_instance
  have hq : q ≫ I.subschemeι ≫ 𝔸(σ; M) ↘ M =
      (I.comap j).subschemeι ≫ 𝔸(σ; W) ↘ W ≫ W.ι := by
    simp only [q, Category.assoc, ← pullback.condition_assoc, I.comapIso_hom_fst_assoc]
    rw [AffineSpace.map_over]
  have hq0 : q ≫ I.subschemeι = (I.comap j).subschemeι ≫ j := by
    simp only [q, Category.assoc, ← pullback.condition, I.comapIso_hom_fst_assoc]
  have hqw : w ∈ Set.range q := by
    have hx : I.subschemeι w ∈ Set.range j := by
      have h := AffineSpace.isPullback_map (n := σ) W.ι
      have : I.subschemeι w ∈ Set.range (pullback.fst (𝔸(σ; M) ↘ M) W.ι) := by
        rw [IsOpenImmersion.range_pullbackFst]
        simpa using hxW
      obtain ⟨z, hz⟩ := this
      exact ⟨h.isoPullback.inv z, by rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_fst, hz]⟩
    have : w ∈ Set.range (pullback.snd j I.subschemeι) := by
      rw [IsOpenImmersion.range_pullbackSnd]
      exact hx
    obtain ⟨z, rfl⟩ := this
    refine ⟨(I.comapIso j).inv z, ?_⟩
    rw [← Scheme.Hom.comp_apply]
    simp only [q, Iso.inv_hom_id_assoc]
  obtain ⟨k, rfl⟩ := hqw
  clear_value q
  refine ⟨q ''ᵁ K, ⟨k, ?_, rfl⟩, ?_⟩
  · show (I.comap j).subschemeι k ∈ 𝔸(σ; W).basicOpen (eval₂Hom (𝔸(σ; W) ↘ W).appTop.hom
      (AffineSpace.coord W) (pderiv l (Φ.map W.ι.appTop.hom)))
    rw [MvPolynomial.pderiv_map, ← appTop_map_eval₂Hom, ← Scheme.preimage_basicOpen_top,
      Scheme.Hom.mem_preimage,
      ← Scheme.Hom.comp_apply, ← hq0, Scheme.Hom.comp_apply]
    exact hw
  · have h1 : (q ''ᵁ K).ι ≫ I.subschemeι ≫ 𝔸(σ; M) ↘ M =
        (q.isoImage K).inv ≫ (K.ι ≫ (I.comap j).subschemeι ≫ 𝔸(σ; W) ↘ W) ≫ W.ι := by
      rw [← Scheme.Hom.isoImage_inv_ι_assoc, Category.assoc, hq]
      simp only [Category.assoc]
    rw [h1]
    have : SmoothOfRelativeDimension (0 + (d + 0))
        ((q.isoImage K).inv ≫ (K.ι ≫ (I.comap j).subschemeι ≫ 𝔸(σ; W) ↘ W) ≫ W.ι) :=
      inferInstance
    simpa using this

/-- **Jacobian criterion for hypersurfaces over an arbitrary base.** Let `M` be a scheme,
`Φ ∈ Γ(M, ⊤)[z_i : i ∈ σ]` with `σ` of cardinality `d + 1`, and `H = V(Φ) ⊆ 𝔸(σ; M)`. If at a
point `w ∈ H` some partial derivative `∂Φ/∂z_l` does not vanish, then there is an open
neighbourhood `U` of `w` in `H` on which `H ⟶ M` is smooth of relative dimension `d`. -/
@[mmp "lem_mmp_foundation_arbitrary_base_hypersurface_jacobian"]
public theorem exists_mem_smoothOfRelativeDimension_hypersurface_of_mem_basicOpen_pderiv
    {M : Scheme.{u}} {σ : Type u} [Finite σ] {d : ℕ} (hσ : Nat.card σ = d + 1)
    (Φ : MvPolynomial σ Γ(M, ⊤))
    (w : (Scheme.IdealSheafData.ofIdealTop (Ideal.span
      {MvPolynomial.eval₂Hom (𝔸(σ; M) ↘ M).appTop.hom (AffineSpace.coord M) Φ})).subscheme)
    (l : σ)
    (hw : (Scheme.IdealSheafData.ofIdealTop (Ideal.span
      {MvPolynomial.eval₂Hom (𝔸(σ; M) ↘ M).appTop.hom (AffineSpace.coord M) Φ})).subschemeι w ∈
        𝔸(σ; M).basicOpen
          (MvPolynomial.eval₂Hom (𝔸(σ; M) ↘ M).appTop.hom (AffineSpace.coord M)
            (MvPolynomial.pderiv l Φ))) :
    ∃ U : (Scheme.IdealSheafData.ofIdealTop (Ideal.span
        {MvPolynomial.eval₂Hom (𝔸(σ; M) ↘ M).appTop.hom (AffineSpace.coord M) Φ})).subscheme.Opens,
      w ∈ U ∧ SmoothOfRelativeDimension d (U.ι ≫ (Scheme.IdealSheafData.ofIdealTop (Ideal.span
        {MvPolynomial.eval₂Hom (𝔸(σ; M) ↘ M).appTop.hom (AffineSpace.coord M) Φ})).subschemeι ≫
          𝔸(σ; M) ↘ M) :=
  exists_smoothOfRelativeDimension_subscheme hσ Φ _ rfl w l hw

end MMP

/-! ### Projective morphisms carry a relatively ample invertible sheaf -/

namespace MMP.Foundations

open AlgebraicGeometry CategoryTheory Limits

/-- A projective morphism `f : X ⟶ S` has an invertible sheaf `L` which is `f`-ample; if `X` is
integral, `L ≅ 𝒪_X(A)` for a Cartier divisor `A`; and every fibre `X_s` admits a closed immersion
over `κ(s)` into some projective space `ℙⁿ_{κ(s)}`. -/
@[mmp "lem_mmp_foundation_ega_projective_relative_ample_module"]
public theorem IsProjective.exists_isRelativelyAmple {X S : Scheme.{u}} {f : X ⟶ S}
    (hf : IsProjective f) :
    (∃ (L : X.Modules) (hL : Stacks.Ample.IsInvertibleModule X L),
      letI := hL
      Stacks.RelativeAmple.IsRelativelyAmple f L ∧
        (IsIntegral X → ∃ A : X.CartierDivisor,
          Nonempty (MMP.CartierDivisor.sheaf A ≅ L))) ∧
    ∀ s : S, ∃ (n : ℕ) (i : f.fiber s ⟶ projectiveSpaceOver n (Spec (S.residueField s))),
      IsClosedImmersion i ∧
        i ≫ projectiveSpaceOver n (Spec (S.residueField s)) ↘ Spec (S.residueField s) =
          f.fiberToSpecResidueField s := by
  refine ⟨?_, fun s => ?_⟩
  · obtain ⟨-, L, hL, hamp⟩ := hf.isQuasiProjective
    refine ⟨L, hL, hamp, fun hX => ?_⟩
    have : Stacks.Ample.IsInvertibleModule X L := hL
    obtain ⟨C, ⟨α⟩⟩ := MMP.CartierDivisor.exists_nonempty_iso_sheaf L
    exact ⟨C, ⟨α.symm⟩⟩
  · have hp : IsProjective (f.fiberToSpecResidueField s) :=
      IsProjective.of_isPullback (IsPullback.of_hasPullback f (S.fromSpecResidueField s)).flip hf
    exact isProjectiveMorphism_of_isProjective_of_isAffine _ hp

end MMP.Foundations

/-! ### Simultaneous approximation for finitely many discrete valuation rings -/

namespace MMP

section Approximation

open Filter WithZero

/-- In `ℤᵐ⁰`, if `g < 1` then `h * g ^ n` is eventually below any nonzero `c`. -/
private lemma eventually_mul_pow_lt {g : ℤᵐ⁰} (hg : g < 1) (h : ℤᵐ⁰) {c : ℤᵐ⁰} (hc : c ≠ 0) :
    ∀ᶠ n : ℕ in atTop, h * g ^ n < c := by
  rw [← exp_log hc]
  rcases eq_or_ne h 0 with rfl | hh
  · exact Eventually.of_forall fun n => by simp
  rw [← exp_log hh]
  rcases eq_or_ne g 0 with rfl | hg0
  · filter_upwards [eventually_ge_atTop 1] with n hn
    simp [zero_pow (by omega : n ≠ 0)]
  rw [← exp_log hg0] at hg ⊢
  rw [← exp_zero, exp_lt_exp] at hg
  filter_upwards [eventually_ge_atTop (h.log - c.log + 1).toNat] with n hn
  rw [← exp_nsmul, ← exp_add, exp_lt_exp, nsmul_eq_mul]
  have : (h.log - c.log + 1) ≤ (n : ℤ) := by omega
  nlinarith

/-- In `ℤᵐ⁰`, if `1 < g` then `g ^ n` eventually exceeds any `h`. -/
private lemma eventually_lt_pow {g : ℤᵐ⁰} (hg : 1 < g) (h : ℤᵐ⁰) :
    ∀ᶠ n : ℕ in atTop, h < g ^ n := by
  have hg0 : g ≠ 0 := ne_of_gt (lt_trans zero_lt_one hg)
  rcases eq_or_ne h 0 with rfl | hh
  · exact Eventually.of_forall fun n => pow_pos (zero_lt_iff.2 hg0) n
  rw [← exp_log hh]
  rw [← exp_log hg0] at hg ⊢
  rw [← exp_zero, exp_lt_exp] at hg
  filter_upwards [eventually_ge_atTop (h.log + 1).toNat] with n hn
  rw [← exp_nsmul, exp_lt_exp, nsmul_eq_mul]
  have : (h.log + 1) ≤ (n : ℤ) := by omega
  nlinarith

section Helpers

variable {F : Type*} [Field F]

/-- If `x` or `y` has value `> 1`, then so does `x + y ^ r` for all large `r`. -/
private lemma eventually_one_lt_add_pow (v : Valuation F ℤᵐ⁰) {x y : F}
    (h : 1 < v x ∨ 1 < v y) : ∀ᶠ r : ℕ in atTop, 1 < v (x + y ^ r) := by
  by_cases hy : 1 < v y
  · filter_upwards [eventually_lt_pow hy (v x), eventually_ge_atTop 1] with r hr hr1
    rw [Valuation.map_add_eq_of_lt_right _ (by rwa [map_pow]), map_pow]
    exact one_lt_pow₀ hy (by omega)
  · have hx : 1 < v x := h.resolve_right hy
    refine Eventually.of_forall fun r => ?_
    rw [Valuation.map_add_eq_of_lt_left]
    · exact hx
    · rw [map_pow]; exact lt_of_le_of_lt (pow_le_one₀ zero_le' (not_lt.1 hy)) hx

/-- Membership in a discrete valuation subring is having normalized valuation `≤ 1`. -/
private lemma valuationSubring_mem_iff_valuation_le_one (V : ValuationSubring F)
    [IsDiscreteValuationRing V] (x : F) :
    x ∈ V ↔ (IsDiscreteValuationRing.maximalIdeal V).valuation F x ≤ 1 := by
  constructor
  · intro hx
    exact (IsDiscreteValuationRing.maximalIdeal V).valuation_le_one (K := F) ⟨x, hx⟩
  · intro hx
    obtain ⟨a, rfl⟩ := IsDiscreteValuationRing.exists_lift_of_le_one (K := F) hx
    exact a.2

/-- A discrete valuation subring is not the whole field. -/
private lemma valuationSubring_ne_top (V : ValuationSubring F) [IsDiscreteValuationRing V] :
    V ≠ ⊤ := by
  intro h
  obtain ⟨π, hπ⟩ :=
    (IsDiscreteValuationRing.maximalIdeal V).valuation_exists_uniformizer F
  have hmem : π⁻¹ ∈ V := h ▸ ValuationSubring.mem_top _
  rw [valuationSubring_mem_iff_valuation_le_one, map_inv₀, hπ, ← exp_neg, neg_neg, ← exp_zero,
    exp_le_exp] at hmem
  omega

/-- Two distinct discrete valuation subrings are separated: some `y` has `vᵢ(y) < 1 < vⱼ(y)`. -/
private lemma exists_valuation_lt_one_and_one_lt_of_ne {A B : ValuationSubring F}
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] (hAB : A ≠ B) :
    ∃ y, (IsDiscreteValuationRing.maximalIdeal A).valuation F y < 1 ∧
      1 < (IsDiscreteValuationRing.maximalIdeal B).valuation F y := by
  have key : ∀ {A B : ValuationSubring F} [IsDiscreteValuationRing A]
      [IsDiscreteValuationRing B], A ≠ B → ∃ c,
        (IsDiscreteValuationRing.maximalIdeal A).valuation F c ≤ 1 ∧
        1 < (IsDiscreteValuationRing.maximalIdeal B).valuation F c := by
    intro A B _ _ hAB
    obtain ⟨c, hcA, hcB⟩ := Set.not_subset.1 fun hle =>
      hAB (ValuationSubring.eq_of_le_of_ne_top A hle (valuationSubring_ne_top B))
    exact ⟨c, (valuationSubring_mem_iff_valuation_le_one A c).1 hcA,
      not_le.1 fun h => hcB ((valuationSubring_mem_iff_valuation_le_one B c).2 h)⟩
  obtain ⟨c, hcA, hcB⟩ := key hAB
  obtain ⟨d, hdB, hdA⟩ := key hAB.symm
  have hd0 : d ≠ 0 := by rintro rfl; simp at hdA
  refine ⟨c / d, ?_, ?_⟩
  · rw [map_div₀, div_lt_one₀ (zero_lt_one.trans hdA)]
    exact hcA.trans_lt hdA
  · rw [map_div₀, one_lt_div₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hd0))]
    exact hdB.trans_lt hcB

end Helpers

section Separated

variable {F : Type*} [Field F] {ι : Type*} [Finite ι] (v : ι → Valuation F ℤᵐ⁰)

/-- From pairwise separating elements, an element small at `i` and large at every `j ≠ i`. -/
private lemma exists_lt_one_and_one_lt
    (hsep : ∀ i j, i ≠ j → ∃ y, v i y < 1 ∧ 1 < v j y) (i : ι) :
    ∃ x, v i x < 1 ∧ ∀ j, j ≠ i → 1 < v j x := by
  classical
  have := Fintype.ofFinite ι
  suffices ∀ S : Finset ι, ∃ x, v i x < 1 ∧ ∀ j ∈ S, j ≠ i → 1 < v j x by
    obtain ⟨x, h1, h2⟩ := this Finset.univ
    exact ⟨x, h1, fun j => h2 j (Finset.mem_univ j)⟩
  intro S
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp, by simp⟩
  | insert j S _ ih =>
    obtain ⟨x, hxi, hxS⟩ := ih
    by_cases hji : j = i
    · subst hji
      exact ⟨x, hxi, fun l hl hli => hxS l ((Finset.mem_insert.1 hl).resolve_left hli) hli⟩
    obtain ⟨y, hyi, hyj⟩ := hsep i j (Ne.symm hji)
    have hall : ∀ᶠ r : ℕ in atTop, ∀ l ∈ insert j S, l ≠ i → 1 < v l (x + y ^ r) := by
      rw [eventually_all_finset]
      intro l hl
      by_cases hli : l = i
      · exact Eventually.of_forall fun _ h => absurd hli h
      rcases Finset.mem_insert.1 hl with rfl | hl
      · filter_upwards [eventually_one_lt_add_pow _ (Or.inr hyj)] with r hr _ using hr
      · filter_upwards [eventually_one_lt_add_pow _ (Or.inl (hxS l hl hli))] with r hr _ using hr
    obtain ⟨r, hr, hr1⟩ := (hall.and (eventually_ge_atTop 1)).exists
    refine ⟨x + y ^ r, Valuation.map_add_lt _ hxi ?_, hr⟩
    rw [map_pow]
    exact pow_lt_one₀ zero_le' hyi (by omega)

/-- The building block: `a * (1 + x ^ r)⁻¹` is eventually within `exp (-N)` of `a` at a valuation
where `x` is small, and of `0` at one where `x` is large. -/
private lemma eventually_mul_inv_one_add_pow_sub_le (w : Valuation F ℤᵐ⁰) {x : F} (a b : F)
    (N : ℤ) (hx : w x < 1 ∧ b = a ∨ 1 < w x ∧ b = 0) :
    ∀ᶠ r : ℕ in atTop, w (a * (1 + x ^ r)⁻¹ - b) ≤ exp (-N) := by
  rcases hx with ⟨hx, rfl⟩ | ⟨hx, rfl⟩
  · filter_upwards [eventually_mul_pow_lt hx (w b) exp_ne_zero, eventually_ge_atTop 1]
      with r hr hr1
    have h1 : w (1 + x ^ r) = 1 :=
      Valuation.map_one_add_of_lt _ (by rw [map_pow]; exact pow_lt_one₀ zero_le' hx (by omega))
    have hne : 1 + x ^ r ≠ 0 := by rintro h0; simp [h0] at h1
    have heq : b * (1 + x ^ r)⁻¹ - b = b * (-(x ^ r) * (1 + x ^ r)⁻¹) := by
      field_simp; ring
    rw [heq, map_mul, map_mul, map_inv₀, h1, inv_one, mul_one, Valuation.map_neg, map_pow]
    exact hr.le
  · have hg : (w x)⁻¹ < 1 := (inv_lt_one₀ (zero_lt_one.trans hx)).2 hx
    filter_upwards [eventually_mul_pow_lt hg (w a) exp_ne_zero, eventually_ge_atTop 1]
      with r hr hr1
    have hbig : w (1 + x ^ r) = w x ^ r := by
      rw [Valuation.map_add_eq_of_lt_right, map_pow]
      rw [map_pow, map_one]; exact one_lt_pow₀ hx (by omega)
    rw [sub_zero, map_mul, map_inv₀, hbig, ← inv_pow]
    exact hr.le

/-- **Approximation theorem** for finitely many `ℤᵐ⁰`-valuations that are pairwise separated:
any targets `a i` can be approximated simultaneously to accuracy `exp (-N i)`. -/
private lemma exists_forall_sub_le_of_separating
    (hsep : ∀ i j, i ≠ j → ∃ y, v i y < 1 ∧ 1 < v j y) (a : ι → F) (N : ι → ℤ) :
    ∃ x, ∀ i, v i (x - a i) ≤ exp (-N i) := by
  classical
  have := Fintype.ofFinite ι
  choose x hxi hxj using exists_lt_one_and_one_lt v hsep
  have hall : ∀ᶠ r : ℕ in atTop, ∀ i j,
      v i (a j * (1 + x j ^ r)⁻¹ - if j = i then a i else 0) ≤ exp (-N i) := by
    simp only [eventually_all]
    intro i j
    refine eventually_mul_inv_one_add_pow_sub_le _ _ _ _ ?_
    by_cases hji : j = i
    · subst hji; exact .inl ⟨hxi j, if_pos rfl⟩
    · exact .inr ⟨hxj j i (Ne.symm hji), if_neg hji⟩
  obtain ⟨r, hr⟩ := hall.exists
  refine ⟨∑ j, a j * (1 + x j ^ r)⁻¹, fun i => ?_⟩
  have hsum : (∑ j, a j * (1 + x j ^ r)⁻¹) - a i =
      ∑ j, (a j * (1 + x j ^ r)⁻¹ - if j = i then a i else 0) := by
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq']; simp
  rw [hsum]
  exact Valuation.map_sum_le _ fun j _ => hr i j

end Separated

end Approximation

/-- **Approximation theorem** for finitely many pairwise distinct discrete valuation rings of a
field `F`: for targets `a i ∈ F` and integer accuracies `N i`, some `x ∈ F` satisfies
`vᵢ(x - a i) ≥ N i` for every `i`, where `vᵢ` is the normalized valuation of `V i`. -/
@[mmp "lem_mmp_foundation_finite_dvr_approximation"]
public theorem exists_forall_valuation_sub_le_of_injective {F : Type*} [Field F]
    {ι : Type*} [Finite ι] (V : ι → ValuationSubring F) (hV : Function.Injective V)
    [∀ i, IsDiscreteValuationRing (V i)] (a : ι → F) (N : ι → ℤ) :
    ∃ x : F, ∀ i,
      (IsDiscreteValuationRing.maximalIdeal (V i)).valuation F (x - a i) ≤
        WithZero.exp (-N i) :=
  exists_forall_sub_le_of_separating _
    (fun _ _ hij => exists_valuation_lt_one_and_one_lt_of_ne (hV.ne hij)) a N

end MMP

/-! ### The analytic inverse function theorem -/

namespace MMP.Analytic

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-- A local homeomorphism analytic at `a` whose inverse is analytic at `e a` restricts to an
open neighbourhood of `a` on which it is analytic, with analytic inverse on the target. -/
private lemma exists_restr_analyticOnNhd (e : OpenPartialHomeomorph E F) {a : E}
    (ha : a ∈ e.source) (he : AnalyticAt 𝕜 e a) (hsymm : AnalyticAt 𝕜 e.symm (e a)) :
    ∃ e' : OpenPartialHomeomorph E F, (e' : E → F) = e ∧ a ∈ e'.source ∧
      AnalyticOnNhd 𝕜 e e'.source ∧ AnalyticOnNhd 𝕜 e'.symm e'.target := by
  let W := {x | AnalyticAt 𝕜 e x} ∩ (e.source ∩ e ⁻¹' {y | AnalyticAt 𝕜 e.symm y})
  have hW : IsOpen W :=
    (isOpen_analyticAt 𝕜 e).inter (e.isOpen_inter_preimage (isOpen_analyticAt 𝕜 e.symm))
  refine ⟨e.restrOpen W hW, rfl, ⟨ha, he, ha, hsymm⟩, fun x hx => hx.2.1, fun y hy => ?_⟩
  have := ((e.restrOpen W hW).map_target hy).2.2.2
  simpa only [OpenPartialHomeomorph.coe_restrOpen_symm, Set.mem_preimage, Set.mem_setOf_eq,
    e.right_inv hy.1] using this

end

/-- **Analytic (holomorphic) inverse function theorem.** If `f` is analytic at `a` with invertible
derivative `f'` there, then `f` restricts to a homeomorphism from an open neighbourhood of `a`
onto an open neighbourhood of `f a`, analytic on its source and with analytic inverse on its
target. -/
@[mmp "lem_mmp_foundation_holomorphic_inverse"]
public theorem exists_openPartialHomeomorph_analyticOnNhd_symm
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E → F} {f' : E ≃L[𝕜] F} {a : E}
    (hf : AnalyticAt 𝕜 f a) (hf' : HasFDerivAt f (f' : E →L[𝕜] F) a) :
    ∃ e : OpenPartialHomeomorph E F, a ∈ e.source ∧ f a ∈ e.target ∧
      Set.EqOn f e e.source ∧ AnalyticOnNhd 𝕜 f e.source ∧
      AnalyticOnNhd 𝕜 e.symm e.target := by
  haveI : CompleteSpace F :=
    (completeSpace_congr (e := f'.toEquiv) f'.isUniformEmbedding).1 ‹_›
  have hs : HasStrictFDerivAt f (f' : E →L[𝕜] F) a := hf'.fderiv ▸ hf.hasStrictFDerivAt
  have he : (hs.toOpenPartialHomeomorph f : E → F) = f := hs.toOpenPartialHomeomorph_coe
  have ha := hs.mem_toOpenPartialHomeomorph_source
  obtain ⟨e, hee, hae, hfe, hsymm⟩ := exists_restr_analyticOnNhd _ ha (by rwa [he])
    ((hs.toOpenPartialHomeomorph f).analyticAt_symm' (i := f') ha (by rwa [he])
      (by rw [he]; exact hf'.fderiv))
  rw [he] at hee hfe
  exact ⟨e, hae, hee ▸ e.map_source hae, hee ▸ fun _ _ => rfl, hfe, hsymm⟩

end MMP.Analytic

/-! ### Independent differentials give a smooth map to affine space -/

namespace MMP

open CategoryTheory AlgebraicGeometry MvPolynomial TensorProduct

/-- In the fibre `κ ⊗_B Ω_{B/R}` of the differentials of a local ring `B`, finitely generated, a
linearly independent family of differentials `1 ⊗ d a_i` completes to a basis by differentials
`1 ⊗ d c_t` of finitely many further elements. -/
private theorem exists_basis_completion_kaehlerDifferential {R B : Type u} [CommRing R]
    [CommRing B] [Algebra R B] [IsLocalRing B] [Module.Finite B Ω[B⁄R]] {σ : Type u} (a : σ → B)
    (ha : LinearIndependent (IsLocalRing.ResidueField B)
      fun i ↦ (1 : IsLocalRing.ResidueField B) ⊗ₜ[B] KaehlerDifferential.D R B (a i)) :
    ∃ (T : Type u) (_ : Finite T) (c : T → B),
      LinearIndependent (IsLocalRing.ResidueField B)
        (fun y ↦ (1 : IsLocalRing.ResidueField B) ⊗ₜ[B] KaehlerDifferential.D R B
          (Sum.elim a c y)) ∧
      Submodule.span (IsLocalRing.ResidueField B) (Set.range fun y ↦
        (1 : IsLocalRing.ResidueField B) ⊗ₜ[B] KaehlerDifferential.D R B
          (Sum.elim a c y)) = ⊤ := by
  classical
  set K := IsLocalRing.ResidueField B
  set d : B → K ⊗[B] Ω[B⁄R] := fun b ↦ (1 : K) ⊗ₜ[B] KaehlerDifferential.D R B b
  have hS : Submodule.span K (Set.range d) = ⊤ := by
    have := Submodule.baseChange_span (R := B) (A := K) (Set.range (KaehlerDifferential.D R B))
    rw [KaehlerDifferential.span_range_derivation, Submodule.baseChange_top,
      ← Set.range_comp] at this
    exact this.symm
  have hvS : Set.range (d ∘ a) ⊆ Set.range d := Set.range_comp_subset_range _ _
  have hs := ha.linearIndepOn_id
  let bB := Module.Basis.extendLe hs hvS hS.ge
  have : Finite (hs.extend hvS) := Module.Finite.finite_basis bB
  let T := ↥(hs.extend hvS \ Set.range (d ∘ a))
  choose c hc using fun t : T ↦ hs.extend_subset hvS t.2.1
  let E : σ ⊕ T ≃ hs.extend hvS :=
    (Equiv.sumCongr (Equiv.ofInjective _ ha.injective) (Equiv.refl _)).trans
      (Equiv.Set.sumDiffSubset (hs.subset_extend hvS))
  have hwE : (fun y ↦ d (Sum.elim a c y)) = bB ∘ E := by
    funext y
    rcases y with j | t
    · simp [E, bB, Equiv.Set.sumDiffSubset_apply_inl]; rfl
    · simp [E, bB, hc]
      rw [Equiv.Set.sumDiffSubset_apply_inr]
  refine ⟨T, Finite.Set.subset _ Set.sdiff_subset, c, ?_, ?_⟩
  · exact hwE ▸ bB.linearIndependent.comp _ E.injective
  · rw [hwE, E.surjective.range_comp, bB.span_eq]

/-- The inclusion `R[m] → R[T ⊕ m]` of a polynomial ring into one with finitely many extra
variables is smooth. -/
private theorem smooth_rename_inr (R : Type u) [CommRing R] (T m : Type u) [Finite T] :
    (rename (R := R) (Sum.inr : m → T ⊕ m)).toRingHom.Smooth := by
  let A := MvPolynomial m R
  let e := sumAlgEquiv R T m
  have h : (rename (R := R) (Sum.inr : m → T ⊕ m)).toRingHom =
      e.symm.toRingEquiv.toRingHom.comp (algebraMap A (MvPolynomial T A)) := by
    refine RingHom.ext fun q ↦ ?_
    have h2 := DFunLike.congr_fun (sumAlgEquiv_comp_rename_inr (R := R) (S₁ := T) (S₂ := m)) q
    change e (rename Sum.inr q) = C q at h2
    change rename Sum.inr q = e.symm (C q)
    rw [← h2, AlgEquiv.symm_apply_apply]
  rw [h]
  have : Algebra.Smooth A (MvPolynomial T A) := ⟨inferInstance, inferInstance⟩
  exact RingHom.Smooth.comp (RingHom.smooth_algebraMap.mpr this)
    (RingHom.Smooth.of_bijective e.symm.bijective)

/-- Renaming the variables of `R[m]` along an injection into a finite type is a smooth ring map. -/
private theorem smooth_rename {R : Type u} [CommRing R] {m n : Type u} [Finite n] (i : m → n)
    (hi : Function.Injective i) : (rename (R := R) i).toRingHom.Smooth := by
  classical
  let E : n ≃ (↥(Set.range i)ᶜ) ⊕ m :=
    ((Equiv.sumCompl (· ∈ Set.range i)).symm.trans (Equiv.sumComm _ _)).trans
      (Equiv.sumCongr (Equiv.refl _) (Equiv.ofInjective i hi).symm)
  have hE : ∀ j, E.symm (Sum.inr j) = i j := fun j => by simp [E, Equiv.ofInjective]
  have : (rename (R := R) i).toRingHom =
      (renameEquiv R E.symm).toRingEquiv.toRingHom.comp (rename (R := R) Sum.inr).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun q ↦ ?_)
    · change rename i (C r) = renameEquiv R E.symm (rename Sum.inr (C r))
      simp
    · change rename i (X q) = renameEquiv R E.symm (rename Sum.inr (X q))
      simp [hE]
  rw [this]
  exact RingHom.Smooth.comp (smooth_rename_inr R _ m)
    (RingHom.Smooth.of_bijective (renameEquiv R E.symm).bijective)

/-- The coordinate projection `𝔸(n; S) ⟶ 𝔸(m; S)` along an injection `m → n`, `n` finite, is
smooth over an affine base. -/
private theorem smooth_reindex {m n : Type u} [Finite n] (i : m → n) (hi : Function.Injective i)
    (S : Scheme.{u}) [IsAffine S] : Smooth (AffineSpace.reindex i S) := by
  suffices H : Smooth (AffineSpace.reindex i S ≫ (AffineSpace.isoOfIsAffine m S).hom) by
    have : Smooth ((AffineSpace.reindex i S ≫ (AffineSpace.isoOfIsAffine m S).hom) ≫
      (AffineSpace.isoOfIsAffine m S).inv) := inferInstance
    simpa using this
  rw [HasRingHomProperty.iff_of_isAffine (P := @Smooth), Scheme.Hom.comp_appTop,
    AffineSpace.isoOfIsAffine_hom_appTop]
  have heq : ((AffineSpace.reindex i S).appTop.hom).comp
      (eval₂Hom ((𝔸(m; S) ↘ S).appTop).hom (AffineSpace.coord S)) =
      (eval₂Hom ((𝔸(n; S) ↘ S).appTop).hom (AffineSpace.coord S)).comp
        (rename (R := Γ(S, ⊤)) i).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun j ↦ ?_)
    · simp only [RingHom.comp_apply, eval₂Hom_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        rename_C]
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, AffineSpace.reindex_over]
    · simp
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom]
  rw [← RingHom.comp_assoc, heq]
  have hiso : Function.Bijective
      (eval₂Hom ((𝔸(n; S) ↘ S).appTop).hom (AffineSpace.coord (n := n) S)) := by
    have : IsIso (AffineSpace.isoOfIsAffine n S).hom.appTop :=
      inferInstanceAs (IsIso ((AffineSpace.isoOfIsAffine n S).hom.app ⊤))
    have h1 := ConcreteCategory.bijective_of_isIso (AffineSpace.isoOfIsAffine n S).hom.appTop
    have h2 := ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso
      (CommRingCat.of (MvPolynomial n Γ(S, ⊤)))).inv
    have := h1.comp h2
    rw [AffineSpace.isoOfIsAffine_hom_appTop] at this
    convert this using 1
    ext q
    simp only [Function.comp_apply, CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
    rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]
  exact RingHom.Smooth.comp (RingHom.Smooth.of_bijective (ConcreteCategory.bijective_of_isIso _))
    (RingHom.Smooth.comp (smooth_rename i hi) (RingHom.Smooth.of_bijective hiso))

/-- **Independent differentials give a smooth map to affine space.** Let `f : X ⟶ Spec k` be
smooth, `g : σ → Γ(X, ⊤)` finitely many functions and `x ∈ X`. If the differentials
`1 ⊗ d g_i` are linearly independent in `κ(x) ⊗ Ω_{X/k,x}`, then there is an open `U ∋ x` on
which the morphism `AffineSpace.homOfVector f g : X ⟶ 𝔸(σ; Spec k)` is smooth. -/
@[mmp "lem_mmp_foundation_independent_differentials_smooth_map"]
public theorem exists_mem_smooth_homOfVector_of_linearIndependent
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Smooth f]
    {σ : Type u} [Finite σ] (g : σ → Γ(X, ⊤)) (x : X)
    (hg : letI := (f.stalkMap x).hom.toAlgebra
      LinearIndependent (IsLocalRing.ResidueField (X.presheaf.stalk x))
        (fun i ↦ (1 : IsLocalRing.ResidueField (X.presheaf.stalk x)) ⊗ₜ[X.presheaf.stalk x]
          KaehlerDifferential.D ((Spec (.of k)).presheaf.stalk (f x)) (X.presheaf.stalk x)
            (X.presheaf.germ ⊤ x trivial (g i)))) :
    ∃ U : X.Opens, x ∈ U ∧ Smooth (U.ι ≫ AffineSpace.homOfVector f g) := by
  classical
  let := (f.stalkMap x).hom.toAlgebra
  have := (MMP.Flips.ResolutionInputs.free_finite_kaehlerDifferential_stalk f x).2
  obtain ⟨T, _, c, hli, hsp⟩ := exists_basis_completion_kaehlerDifferential _ hg
  -- represent the new germs on a common open neighbourhood `V` of `x`
  choose W hxW s hs using fun t ↦ X.presheaf.exists_germ_eq (c t)
  let V : X.Opens := ⨅ t, W t
  have hxV : x ∈ V := by
    simpa [V, ← SetLike.mem_coe, TopologicalSpace.Opens.coe_iInf] using hxW
  let G : σ ⊕ T → Γ(X, V) := Sum.elim (fun j ↦ X.presheaf.map (homOfLE le_top).op (g j))
    (fun t ↦ X.presheaf.map (homOfLE (iInf_le W t)).op (s t))
  have hG : ∀ y, X.presheaf.germ V x hxV (G y) =
      Sum.elim (fun j ↦ X.presheaf.germ ⊤ x trivial (g j)) c y := by
    rintro (j | t) <;> simp [G, X.presheaf.germ_res_apply, hs]
  let N := Nat.card (σ ⊕ T)
  let eF : Fin N ≃ σ ⊕ T := (Finite.equivFin (σ ⊕ T)).symm
  obtain ⟨U, -, hxU, hUV, hEt⟩ :=
    MMP.Flips.ResolutionInputs.exists_isAffineOpen_etale_homOfVector f x V hxV (G ∘ eF)
      ⟨by simpa only [Function.comp_def, hG] using hli.comp _ eF.injective,
       by simpa only [Function.comp_def, hG] using
         (congrArg _ (eF.surjective.range_comp _)).trans hsp⟩
  refine ⟨U, hxU, ?_⟩
  -- the map `(g_i)_i` is the étale chart followed by a coordinate projection
  let ι : σ → ULift.{u} (Fin N) := fun j ↦ ULift.up (eF.symm (Sum.inl j))
  have hι : Function.Injective ι := fun a a' h ↦ by
    simpa [ι] using congrArg (fun z ↦ eF z.down) h
  have := smooth_reindex ι hι (Spec (.of k))
  have key : U.ι ≫ AffineSpace.homOfVector f g = AffineSpace.homOfVector (U.ι ≫ f)
        (fun i : ULift.{u} (Fin N) ↦
          U.topIso.inv (X.presheaf.map (homOfLE hUV).op ((G ∘ eF) i.down))) ≫
        AffineSpace.reindex ι (Spec (.of k)) := by
    rw [AffineSpace.reindex, AffineSpace.comp_homOfVector, AffineSpace.comp_homOfVector,
      AffineSpace.homOfVector_over]
    congr 1
    funext j
    simp only [Function.comp_apply, ι, AffineSpace.homOfVector_appTop_coord,
      Equiv.apply_symm_apply, G, Sum.elim_inl]
    apply (ConcreteCategory.bijective_of_isIso U.topIso.hom).injective
    rw [← CommRingCat.comp_apply U.topIso.inv U.topIso.hom, Iso.inv_hom_id, CommRingCat.id_apply,
      ← CommRingCat.comp_apply, ← CommRingCat.comp_apply (X.presheaf.map _), ← Functor.map_comp,
      Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom]
    erw [← Functor.map_comp]
    rfl
  rw [key]
  infer_instance

end MMP

/-! ### Bertini theorems relative to a simple normal crossing divisor -/

namespace MMP.Threefold.Bridges

open CategoryTheory AlgebraicGeometry TopologicalSpace
open MMP.Resolution
open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections (globalSectionsModule)
open Stacks.NonvanishingOpen (nonvanishingOpen)

attribute [local instance] globalSectionsModule

/-- The components of an snc divisor form an snc family. -/
private theorem isSNCFamily_idealSheaf_of_isSNC {k : Type u} [Field k] {X : Scheme.{u}}
    {f : X ⟶ Spec (.of k)} {R : Type*} [Zero R] {D : MMP.Mori.DivisorWithCoeffs R X}
    (hD : D.IsSNC f) : IsSNCFamily f (fun E : D.support => E.1.idealSheaf) := by
  refine ⟨fun E => ⟨?_, isPureCodimOne_support_primeDivisor E.1, hD.1 E.1 E.2⟩, fun x => ?_⟩
  · haveI := E.1.integral
    infer_instance
  · obtain ⟨n, z, j, hz, hj, hI⟩ := hD.2 x
    exact ⟨n, z, fun E => j ⟨E.1.1, E.1.2, E.2⟩, hz, fun E => hI ⟨E.1.1, E.1.2, E.2⟩,
      fun E E' h => Subtype.ext (Subtype.ext (by simpa using hj h))⟩

/-- The reduced divisor with components a finite set `D` of prime divisors has support `D`. -/
private theorem support_sum_single {X : Scheme.{u}} (D : Finset (MMP.Mori.PrimeDivisor X)) :
    (∑ E ∈ D, Finsupp.single E (1 : ℤ) : MMP.Mori.Divisor X).support = D := by
  classical
  ext E
  simp [Finsupp.finset_sum_apply, Finsupp.single_apply]

/-- An irreducible component of a closed subset of pure codimension one is the closure of a
point of coheight one. -/
private theorem exists_coheight_eq_one_of_mem_componentsOf {X : Scheme.{u}}
    {Z : X.IdealSheafData} (hZ : MMP.Mori.IsPureCodimOne Z.support) {V : Set X}
    (hV : V ∈ componentsOf (Z.support : Set X)) :
    ∃ ξ : X, V = closure {ξ} ∧ Order.coheight ξ = 1 := by
  obtain ⟨ξ, -, hξ⟩ := Aux.exists_eq_closure_of_mem_componentsOf Z.support.isClosed hV
  refine ⟨ξ, hξ, ?_⟩
  rw [coheight_eq_codimension_closureSingleton]
  apply hZ
  refine ⟨?_, fun W' hW' hle => ?_⟩
  · change closure {ξ} ⊆ (Z.support : Set X)
    rw [← hξ]
    exact hV.1.2
  · have : (W' : Set X) ⊆ V := hV.2 ⟨W'.isIrreducible, hW'⟩ (by rw [hξ]; exact hle)
    change (W' : Set X) ⊆ closure {ξ}
    rw [← hξ]
    exact this

/-- If a closed subscheme `H` is cut out at `x` by one member `z m` of a regular system of
parameters, so is every irreducible component of `H` through `x`. -/
private theorem stalk_componentsFamily_eq_of_stalk_eq_span {Y : Scheme.{u}}
    [IsLocallyNoetherian Y] (H : Y.IdealSheafData) {x : Y} {n : ℕ}
    {z : Fin n → Y.presheaf.stalk x} {m : Fin n} (hz : MMP.Mori.IsRegularSystemOfParameters z)
    (hHx : IdealSheafData.stalk H x = Ideal.span {z m})
    (V : componentsOf (H.support : Set Y)) (hxV : x ∈ (V : Set Y)) :
    IdealSheafData.stalk (componentsFamily (H.support : Set Y) V) x = Ideal.span {z m} := by
  have h1 := preimage_fromSpecStalk_iUnion_support (fun _ : Unit => H) x z (fun _ => m)
    (fun _ => hHx)
  have hTy : Y.fromSpecStalk x ⁻¹' (H.support : Set Y) =
      ⋃ t ∈ ({m} : Finset (Fin n)), PrimeSpectrum.zeroLocus {z t} := by
    haveI : Nonempty {i : Unit // x ∈ H.support} := ⟨⟨(), V.2.1.2 hxV⟩⟩
    simp only [Set.iUnion_const] at h1
    simpa using h1
  obtain ⟨c₀, hc₀, hst, -⟩ :=
    exists_stalk_componentsFamily_eq_span H.support.isClosed hz hTy V hxV
  rwa [Finset.mem_singleton.1 hc₀] at hst

/-- An irreducible component of a closed subset of pure codimension one is the support of a
prime divisor. -/
private theorem exists_primeDivisor_support_eq_of_mem_componentsOf {X : Scheme.{u}}
    {Z : X.IdealSheafData} (hZ : MMP.Mori.IsPureCodimOne Z.support) {V : Set X}
    (hV : V ∈ componentsOf (Z.support : Set X)) :
    ∃ E : MMP.Mori.PrimeDivisor X, E.support = V := by
  obtain ⟨ξ, hξ, hξ1⟩ := exists_coheight_eq_one_of_mem_componentsOf hZ hV
  refine ⟨PrimeDivisor.ofCoheightOne ξ hξ1, ?_⟩
  change ((Stacks.Chow.integralComponentAt ξ).support : Set X) = V
  rw [Stacks.Chow.coe_support_integralComponentAt, ← hξ]

/-- A prime divisor whose support is an irreducible component of `Z` is cut out, at every point
of it, by the same coordinate as `Z`. -/
private theorem stalk_idealSheaf_eq_of_mem_componentsOf {X : Scheme.{u}}
    [IsLocallyNoetherian X] {Z : X.IdealSheafData} {E : MMP.Mori.PrimeDivisor X}
    (hE : E.support ∈ componentsOf (Z.support : Set X)) {x : X} (hx : x ∈ E.support) {n : ℕ}
    {z : Fin n → X.presheaf.stalk x} {m : Fin n} (hz : MMP.Mori.IsRegularSystemOfParameters z)
    (hZx : IdealSheafData.stalk Z x = Ideal.span {z m}) :
    IdealSheafData.stalk E.idealSheaf x = Ideal.span {z m} := by
  have hEideal : E.idealSheaf = componentsFamily (Z.support : Set X) ⟨_, hE⟩ := by
    haveI := E.integral
    refine (Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme _ _ rfl).trans
      (congrArg _ ?_)
    ext1
    rw [Closeds.coe_closure]
    exact E.idealSheaf.support.isClosed.closure_eq.symm
  rw [hEideal]
  exact stalk_componentsFamily_eq_of_stalk_eq_span Z hz hZx ⟨_, hE⟩ hx

variable {k : Type u} [Field k] {N : ℕ} {X : Scheme.{u}} [X.Over (Spec (.of k))]
  {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L]

/-- The invertibility of `L` in the spelling the zero scheme takes. -/
local instance : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
  (inferInstance : Stacks.Ample.IsInvertibleModule X L)

open Classical in
/-- **Bertini's theorem for simple normal crossings.** Let `X` be a smooth variety over an
algebraically closed field `k` of characteristic zero, `s₀, …, s_N` global sections generating
an invertible sheaf `L`, and `D` a simple normal crossing divisor on `X`. Then there is a dense
open `U` of `ℙᴺ_k` such that for every nonzero coefficient vector `c` with `[c] ∈ U`, the zero
scheme `Z` of `∑ᵢ cᵢ sᵢ` is reduced, and there is a finite set `T` of prime divisors, whose
supports are exactly the irreducible components of `Z`, none of them a component of `D`, such
that the reduced divisor with components `T` and those of `D` is simple normal crossing. -/
@[mmp "lem_mmp_foundation_km2b_snc_bertini"]
public theorem exists_dense_open_isSNC_zeroScheme_add [IsAlgClosed k] [CharZero k]
    [IsSmoothVariety k (X ↘ Spec (.of k))]
    (s : Fin (N + 1) → Γ(L, ⊤))
    (hs : ⨆ c : Fin (N + 1) → k, nonvanishingOpen X L (systemSection s c) = ⊤)
    {R : Type*} [Zero R] (D : Mori.DivisorWithCoeffs R X)
    (hD : D.IsSNC (X ↘ Spec (.of k))) :
    ∃ U : (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)).Opens,
      Dense (U : Set (AlgebraicGeometry.Proj
        (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))) ∧
      ∀ (c : Fin (N + 1) → k) (hc : c ≠ 0), dualPoint c hc ∈ U →
        IsReduced (zeroScheme X L (systemSection s c)).subscheme ∧
        ∃ T : Finset (Mori.PrimeDivisor X),
          (∀ Z : Set X, Maximal (fun W : Set X => IsIrreducible W ∧
              W ⊆ (zeroScheme X L (systemSection s c)).support) Z ↔ ∃ E ∈ T, E.support = Z) ∧
          Disjoint T D.support ∧
          (∑ E ∈ T ∪ D.support, Finsupp.single E (1 : ℤ) : Mori.Divisor X).IsSNC
            (X ↘ Spec (.of k)) := by
  classical
  haveI : Smooth (𝟙 X ≫ X ↘ Spec (.of k)) := by rw [Category.id_comp]; infer_instance
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have hG : IsSNCFamily (𝟙 X ≫ X ↘ Spec (.of k)) (fun E : D.support => E.1.idealSheaf) := by
    rw [Category.id_comp]
    exact isSNCFamily_idealSheaf_of_isSNC hD
  obtain ⟨-, U, hU, hUc⟩ := exists_dense_open_isSNCFamily_zeroScheme s hs (𝟙 X) _ hG
  refine ⟨U, hU, fun c hc hcU => ?_⟩
  obtain ⟨-, havoid, hsnc⟩ := hUc c hc hcU
  set Z := zeroScheme X L (systemSection s c)
  simp only [Scheme.IdealSheafData.comap_id, Category.id_comp] at havoid hsnc
  set C := componentsOf (Z.support : Set X)
  haveI : NoetherianSpace X := Aux.noetherianSpace_of_finiteType (X ↘ Spec (.of k))
  haveI : Fintype C := (Aux.finite_and_cover_componentsOf Z.support.isClosed).1.fintype
  choose P hP using fun V : C =>
    exists_primeDivisor_support_eq_of_mem_componentsOf (hsnc.1 none).2.1 V.2
  let T : Finset (MMP.Mori.PrimeDivisor X) := Finset.univ.image P
  have hT : ∀ E ∈ T, E.support ∈ C := by
    simp only [T, Finset.mem_image, Finset.mem_univ, true_and]
    rintro _ ⟨V, rfl⟩
    exact hP V ▸ V.2
  refine ⟨(hsnc.1 none).1, T, fun W => ⟨fun hW => ⟨P ⟨W, hW⟩, by simp [T], hP _⟩, ?_⟩, ?_, ?_⟩
  · rintro ⟨E, hE, rfl⟩
    exact hT E hE
  · refine Finset.disjoint_left.2 fun E hET hED => havoid {⟨E, hED⟩} _ ?_ (hT E hET).1.2
    simp only [Set.mem_singleton_iff, Set.iInter_iInter_eq_left]
    have hirr : IsIrreducible E.support := by
      rw [PrimeDivisor.support_eq_closure]
      exact isIrreducible_singleton.closure
    exact ⟨⟨hirr, le_rfl⟩, fun W hW _ => hW.2⟩
  · have hXsm : MMP.Mori.IsSmoothScheme (X ↘ Spec (.of k)) :=
      MMP.Mori.isSmoothScheme_of_smooth inferInstance
    rw [MMP.Mori.DivisorWithCoeffs.IsSNC, support_sum_single]
    refine ⟨fun E hE => (Finset.mem_union.1 hE).elim (fun hE => ?_) (hD.1 E), fun x => ?_⟩
    · refine isSmoothScheme_subscheme_of_forall_stalk_eq_span _ hXsm _ fun x hx => ?_
      obtain ⟨n, z, c, hz, hI, -⟩ := hsnc.2 x
      have hxZ : x ∈ Z.support := (hT E hE).1.2 hx
      exact ⟨n, z, c ⟨none, hxZ⟩, hz,
        stalk_idealSheaf_eq_of_mem_componentsOf (hT E hE) hx hz (hI ⟨none, hxZ⟩)⟩
    · obtain ⟨n, z, c, hz, hI, -⟩ := hsnc.2 x
      have hTD : ∀ E : {E : MMP.Mori.PrimeDivisor X // E ∈ T ∪ D.support ∧ x ∈ E.support},
          E.1 ∉ D.support → E.1 ∈ T := fun E h => (Finset.mem_union.1 E.2.1).resolve_right h
      let j : {E : MMP.Mori.PrimeDivisor X // E ∈ T ∪ D.support ∧ x ∈ E.support} → Fin n :=
        fun E => if h : E.1 ∈ D.support then c ⟨some ⟨E.1, h⟩, E.2.2⟩
          else c ⟨none, (hT E.1 (hTD E h)).1.2 E.2.2⟩
      have hj : ∀ E, IdealSheafData.stalk E.1.idealSheaf x = Ideal.span {z (j E)} := by
        intro E
        by_cases h : E.1 ∈ D.support
        · simp only [j, dif_pos h]
          exact hI ⟨some ⟨E.1, h⟩, E.2.2⟩
        · simpa only [j, dif_neg h] using stalk_idealSheaf_eq_of_mem_componentsOf
            (hT E.1 (hTD E h)) E.2.2 hz (hI ⟨none, _⟩)
      exact ⟨n, z, j, hz, fun E E' hEE' => Subtype.ext
        (MMP.Intersection.eq_of_stalk_idealSheaf_eq E.2.2 E'.2.2 (by rw [hj, hj, hEE'])), hj⟩

open Classical in
/-- If a closed subscheme `H` and the members of a finite set `D` of prime divisors form an snc
family, there is a finite set `T` of prime divisors whose supports are exactly the irreducible
components of `H`, and the reduced divisor with components `T` and `D` is snc. -/
theorem exists_finset_isSNC_union_of_isSNCFamily [PerfectField k] {Y : Scheme.{u}}
    {f : Y ⟶ Spec (.of k)} [LocallyOfFiniteType f] [NoetherianSpace Y] (H : Y.IdealSheafData)
    (D : Finset (MMP.Mori.PrimeDivisor Y))
    (hsnc : IsSNCFamily f fun o : Option
      (∑ E ∈ D, Finsupp.single E (1 : ℤ) : MMP.Mori.Divisor Y).support =>
        o.elim H fun E => E.1.idealSheaf) :
    ∃ T : Finset (MMP.Mori.PrimeDivisor Y),
      (∀ Z : Set Y, Maximal (fun W : Set Y => IsIrreducible W ∧ W ⊆ H.support) Z ↔
        ∃ E ∈ T, E.support = Z) ∧
      (∑ E ∈ T ∪ D, Finsupp.single E (1 : ℤ) : MMP.Mori.Divisor Y).IsSNC f := by
  classical
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
  set Dv : MMP.Mori.Divisor Y := ∑ E ∈ D, Finsupp.single E (1 : ℤ)
  have hDs : Dv.support = D := support_sum_single D
  let G : Dv.support → Y.IdealSheafData := fun E => E.1.idealSheaf
  change IsSNCFamily f (fun o : Option Dv.support => o.elim H G) at hsnc
  have hHpure : MMP.Mori.IsPureCodimOne H.support := (hsnc.1 none).2.1
  set C := componentsOf (H.support : Set Y)
  have hfin : C.Finite := (Aux.finite_and_cover_componentsOf H.support.isClosed).1
  have : Fintype C := hfin.fintype
  choose ξ hξV hξ1 using fun V : C => exists_coheight_eq_one_of_mem_componentsOf hHpure V.2
  let P : C → MMP.Mori.PrimeDivisor Y := fun V => PrimeDivisor.ofCoheightOne (ξ V) (hξ1 V)
  have hPsupp : ∀ V : C, (P V).support = V := fun V => by
    change ((Stacks.Chow.integralComponentAt (ξ V)).support : Set Y) = V
    rw [Stacks.Chow.coe_support_integralComponentAt, ← hξV]
  have hPideal : ∀ V : C, (P V).idealSheaf = componentsFamily (H.support : Set Y) V := by
    intro V
    change Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({ξ V} : Set Y)) =
      Scheme.IdealSheafData.vanishingIdeal (Closeds.closure (V : Set Y))
    congr 1
    ext1
    rw [Closeds.coe_closure, Closeds.coe_closure, hξV V, closure_closure]
  let T : Finset (MMP.Mori.PrimeDivisor Y) := Finset.univ.image P
  -- the components of `H` are smooth
  have hHsnc : IsSNCClosedSubset f (H.support : Set Y) := by
    have h1 : IsSNCFamily f (fun _ : Unit => H) :=
      IsSNCFamily.comp hsnc (fun _ : Unit => none) (fun _ _ _ => rfl)
    have h2 := IsSNCFamily.isSNCClosedSubset_iUnion h1
    rwa [Set.iUnion_const] at h2
  have hPsmooth : ∀ V : C, MMP.Mori.IsSmoothScheme ((P V).idealSheaf.subschemeι ≫ f) := by
    intro V
    obtain ⟨-, hempty | ⟨-, -, hfam⟩⟩ := hHsnc
    · obtain ⟨y, hy⟩ := V.2.1.1.nonempty
      exact absurd (hempty ▸ V.2.1.2 hy) (Set.notMem_empty y)
    · rw [hPideal]
      exact (hfam.1 V).2.2
  refine ⟨T, fun W => ?_, ?_⟩
  · refine ⟨fun hW => ⟨P ⟨W, hW⟩, Finset.mem_image_of_mem _ (Finset.mem_univ _), hPsupp _⟩, ?_⟩
    rintro ⟨E, hE, rfl⟩
    obtain ⟨V, -, rfl⟩ := Finset.mem_image.1 hE
    rw [hPsupp]
    exact V.2
  · have hTD : ∀ E ∈ T ∪ D, E ∉ D → ∃ V : C, P V = E := fun E hE hED => by
      obtain ⟨V, -, hV⟩ := Finset.mem_image.1 ((Finset.mem_union.1 hE).resolve_right hED)
      exact ⟨V, hV⟩
    have hmemS : ∀ E ∈ (∑ E ∈ T ∪ D, Finsupp.single E (1 : ℤ) : MMP.Mori.Divisor Y).support,
        E ∈ T ∪ D := fun E h => support_sum_single (T ∪ D) ▸ h
    refine ⟨fun E hE => ?_, fun x => ?_⟩
    · by_cases hED : E ∈ D
      · exact (hsnc.1 (some ⟨E, hDs ▸ hED⟩)).2.2
      · obtain ⟨V, rfl⟩ := hTD E (hmemS E hE) hED
        exact hPsmooth V
    · obtain ⟨n, z, c', hz, hc', -⟩ := hsnc.2 x
      -- a member of `T` through `x` is a component of `H` through `x`
      have hV : ∀ E : {E : MMP.Mori.PrimeDivisor Y //
          E ∈ (∑ E ∈ T ∪ D, Finsupp.single E (1 : ℤ) : MMP.Mori.Divisor Y).support ∧
            x ∈ E.support}, E.1 ∉ D → ∃ V : C, P V = E.1 ∧ x ∈ (V : Set Y) := fun E hED => by
        obtain ⟨V, hV⟩ := hTD E.1 (hmemS _ E.2.1) hED
        exact ⟨V, hV, by rw [← hPsupp, hV]; exact E.2.2⟩
      have hxH : ∀ E : {E : MMP.Mori.PrimeDivisor Y //
          E ∈ (∑ E ∈ T ∪ D, Finsupp.single E (1 : ℤ) : MMP.Mori.Divisor Y).support ∧
            x ∈ E.support}, E.1 ∉ D → x ∈ (H.support : Set Y) := fun E hED => by
        obtain ⟨V, -, hxV⟩ := hV E hED
        exact V.2.1.2 hxV
      -- the member of the family `H, D` that a component through `x` comes from
      let g : {E : MMP.Mori.PrimeDivisor Y //
          E ∈ (∑ E ∈ T ∪ D, Finsupp.single E (1 : ℤ) : MMP.Mori.Divisor Y).support ∧
            x ∈ E.support} → {o : Option Dv.support // x ∈ (o.elim H G).support} :=
        fun E => if h : E.1 ∈ D then ⟨some ⟨E.1, by rw [hDs]; exact h⟩, E.2.2⟩ else
          ⟨none, hxH E h⟩
      have hcoord : ∀ E, IdealSheafData.stalk E.1.idealSheaf x = Ideal.span {z (c' (g E))} := by
        intro E
        have := hc' (g E)
        by_cases hED : E.1 ∈ D
        · simp only [g, dif_pos hED] at this ⊢
          exact this
        · obtain ⟨V, hPV, hxV⟩ := hV E hED
          simp only [g, dif_neg hED] at this ⊢
          rw [show E.1.idealSheaf = _ from hPV ▸ hPideal V]
          exact stalk_componentsFamily_eq_of_stalk_eq_span H hz this V hxV
      refine ⟨n, z, fun E => c' (g E), hz, fun E E' h => Subtype.ext ?_, hcoord⟩
      exact MMP.Intersection.eq_of_stalk_idealSheaf_eq E.2.2 E'.2.2
        ((hcoord E).trans ((congrArg (fun i => Ideal.span {z i}) h).trans (hcoord E').symm))

open Classical in
/-- **Bertini's theorem on a smooth open subset, for an snc divisor.** Let `X` be a variety over
an algebraically closed field `k` of characteristic zero, `s₀, …, s_N` global sections generating
an invertible sheaf `L`, `X° ⊆ X` an open subset contained in the smooth locus, and `D` a finite
set of prime divisors of `X°` whose sum is simple normal crossing. Then there is a dense open `U`
of `ℙᴺ_k` such that for every `c ≠ 0` with `[c] ∈ U`, writing `H = Z(∑ᵢ cᵢ sᵢ)`, the trace
`H ∩ X°` is smooth over `k`, contains no irreducible component of `⋂_{E ∈ J} E` for any
`J ⊆ D` (the empty intersection being `X°`), and there is a finite set `T` of prime divisors of
`X°`, whose supports are exactly the irreducible components of `H ∩ X°`, such that the reduced
divisor with components `T` and `D` is simple normal crossing on `X°`. -/
@[mmp "lem_mmp_foundation_km5d_smooth_open_snc_bertini"]
public theorem exists_dense_open_isSNC_add_zeroScheme_comap_opens [IsAlgClosed k] [CharZero k]
    [IsVariety k (X ↘ Spec (.of k))]
    (s : Fin (N + 1) → Γ(L, ⊤))
    (hs : ⨆ c : Fin (N + 1) → k, nonvanishingOpen X L (systemSection s c) = ⊤)
    (X₀ : X.Opens) (hX₀ : X₀ ≤ Mori.smoothLocus (X ↘ Spec (.of k)))
    (D : Finset (Mori.PrimeDivisor X₀))
    (hD : (∑ E ∈ D, Finsupp.single E (1 : ℤ) : Mori.Divisor X₀).IsSNC
      (X₀.ι ≫ X ↘ Spec (.of k))) :
    ∃ U : (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)).Opens,
      Dense (U : Set (AlgebraicGeometry.Proj
        (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))) ∧
      ∀ (c : Fin (N + 1) → k) (hc : c ≠ 0), dualPoint c hc ∈ U →
        let H := (zeroScheme X L (systemSection s c)).comap X₀.ι
        Smooth (H.subschemeι ≫ X₀.ι ≫ X ↘ Spec (.of k)) ∧
        (∀ J ⊆ D, ∀ W ∈ componentsOf (⋂ E ∈ J, (E.support : Set X₀)),
          ¬ W ⊆ (H.support : Set X₀)) ∧
        ∃ T : Finset (Mori.PrimeDivisor X₀),
          (∀ Z : Set X₀, Maximal (fun W : Set X₀ => IsIrreducible W ∧ W ⊆ H.support) Z ↔
            ∃ E ∈ T, E.support = Z) ∧
          (∑ E ∈ T ∪ D, Finsupp.single E (1 : ℤ) : Mori.Divisor X₀).IsSNC
            (X₀.ι ≫ X ↘ Spec (.of k)) := by
  classical
  set f := X₀.ι ≫ X ↘ Spec (.of k)
  have hsmooth : Smooth f := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq,
      ← MMP.Mori.smoothLocus_eq_smoothLocus]
    exact top_le_iff.1 fun x _ => hX₀ x.2
  have : NoetherianSpace X := Aux.noetherianSpace_of_finiteType (X ↘ Spec (.of k))
  have : NoetherianSpace X₀ := TopologicalSpace.NoetherianSpace.set (X₀ : Set X)
  set Dv : MMP.Mori.Divisor X₀ := ∑ E ∈ D, Finsupp.single E (1 : ℤ)
  have hDs : Dv.support = D := support_sum_single D
  have hG : IsSNCFamily f (fun E : Dv.support => E.1.idealSheaf) :=
    isSNCFamily_idealSheaf_of_isSNC hD
  obtain ⟨-, U, hU, hUc⟩ := exists_dense_open_isSNCFamily_zeroScheme s hs X₀.ι _ hG
  refine ⟨U, hU, fun c hc hcU => ?_⟩
  obtain ⟨hsm, havoid, hsnc⟩ := hUc c hc hcU
  intro H
  let G : Dv.support → X₀.toScheme.IdealSheafData := fun E => E.1.idealSheaf
  change IsSNCFamily f (fun o : Option Dv.support => o.elim H G) at hsnc
  refine ⟨hsm, fun J hJ W hW => ?_, exists_finset_isSNC_union_of_isSNCFamily H D hsnc⟩
  refine havoid {E | E.1 ∈ J} W ?_
  convert hW using 2
  ext x
  simp only [Set.mem_iInter, Set.mem_ofPred_eq, Subtype.forall]
  exact ⟨fun h E hE => h E (by rw [hDs]; exact hJ hE) hE, fun h E _ hE => h E hE⟩

end MMP.Threefold.Bridges

end
