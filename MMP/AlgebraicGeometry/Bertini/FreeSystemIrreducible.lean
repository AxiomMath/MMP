module
public import MMP.AlgebraicGeometry.Bertini.ReducedGeneralMember
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjConeChart
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceCoordinateSquare
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.AlgebraComparison
public import StacksFrontier.AlgebraicGeometry.Modules.RestrictStalkDepth
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniUniversalDivisorGenericFibre
public import StacksFrontier.AlgebraicGeometry.PicSurjectiveOpen.AffineGenerator

/-!
# Irreducibility of general members of a free system

Let `k` be an algebraically closed field of characteristic zero, `X` a variety over `k`, `L` an
invertible sheaf on `X` and `V ⊆ H⁰(X, L)` a finite-dimensional system spanned by `s₀, …, s_N`
that generates `L`, with morphism `φ : X → ℙ(V^*)`. If `φ(X)` has dimension at least two, then
for a general section `s ∈ V`, and for a general point `[s] ∈ ℙ(V)`, the zero scheme `Z(s)` is
geometrically integral over `k`, that is, geometrically irreducible and geometrically reduced;
in particular it is integral, hence nonempty.

## Main results

* `MMP.Threefold.Bridges.exists_dense_open_geometricallyIntegral_zeroScheme`: Bertini's
  irreducibility theorem for a free system whose morphism has image of dimension at least two.

## Implementation notes

As in `MMP.Threefold.Bridges.exists_dense_open_isReduced_zeroScheme`, the system is presented by
a spanning family `s : Fin (N + 1) → Γ(X, L)`, a section of it by its coefficient vector
`c ∈ kᴺ⁺¹` through `MMP.Threefold.Bridges.systemSection`, and the dense opens of `V` and `ℙ(V)`
by dense opens of `MMP.Threefold.Bridges.coefficientSpace k N` and
`AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)`. The morphism
of the system is
`Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.morphismOfGeneratingSections`, and
the dimension of its image is the Krull dimension of the image as a subspace.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], proof of 3.39
* [Stacks Project, Tag 0G4F](https://stacks.math.columbia.edu/tag/0G4F)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace MMP.Threefold.Bridges

open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections (globalSectionsModule
  morphismOfGeneratingSections)
open Stacks.NonvanishingOpen (nonvanishingOpen)

attribute [local instance] globalSectionsModule

/-- The invertibility of `L` in the spelling the zero scheme takes. -/
local instance {X : Scheme.{u}} {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L] :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
  (inferInstance : Stacks.Ample.IsInvertibleModule X L)

/-! ### The member of a family over the base field -/

section BaseField

open Stacks.Bertini

/-- **`H_v` over `k` itself is the zero scheme of `ψ(v)`, for geometric irreducibility.** For a
`k`-point the base change `X_k` is `X`, the divisor `H_v` is the zero scheme of
`ψ(∑ aᵢ vᵢ)` pulled back along this isomorphism, and geometric irreducibility of a morphism is
invariant under isomorphisms of the source. -/
private theorem geometricallyIrreducible_zeroScheme_of_specializedDivisor
    {D : FamilyDivisors.{u, u}} (a : Fin (Module.finrank D.k D.V) → D.k)
    (h : GeometricallyIrreducible ((D.specializedDivisor D.k a).subschemeι ≫
      D.baseChangeToSpec D.k)) :
    GeometricallyIrreducible
      ((Stacks.Divisors.zeroScheme D.X D.L (D.sectionOf (∑ i, a i • D.basis i))).subschemeι ≫
        D.toBase) := by
  set φ := Spec.map (CommRingCat.ofHom (algebraMap D.k D.k))
  have hφ : φ = 𝟙 _ := by
    simp only [φ]
    rw [Algebra.algebraMap_self]
    exact Spec.map_id _
  have : IsIso φ := by rw [hφ]; infer_instance
  set e : D.baseChange D.k ⟶ D.X := D.baseChangeToX D.k
  have : IsIso e := by
    change IsIso (Limits.pullback.fst D.toBase φ)
    infer_instance
  have hspec : D.baseChangeToSpec D.k = e ≫ D.toBase := by
    change Limits.pullback.snd D.toBase φ = Limits.pullback.fst D.toBase φ ≫ D.toBase
    rw [Limits.pullback.condition, hφ, Category.comp_id]
  have hscalar : ∀ c : D.k, D.baseChangeScalar D.k c = e.appTop (D.baseScalar c) := by
    intro c
    change (D.baseChangeToSpec D.k).appTop ((Scheme.ΓSpecIso (.of D.k)).inv c) = _
    rw [hspec, Scheme.Hom.comp_appTop]
    rfl
  set t := D.sectionOf (∑ i, a i • D.basis i)
  have hsec : D.specializedSection D.k a = pullbackGlobalSections e D.L t := by
    have ht : t = ∑ i, D.baseScalar (a i) • D.sectionOf (D.basis i) := by
      change D.ψ (∑ i, a i • D.basis i) = _
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => D.sectionOf_smul _ _
    rw [FamilyDivisors.specializedSection, ht, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_smul, hscalar]
  have hdiv : D.specializedDivisor D.k a = (Stacks.Divisors.zeroScheme D.X D.L t).comap e := by
    rw [FamilyDivisors.specializedDivisor, hsec]
    exact Stacks.Divisors.zeroScheme_pullback e D.L t
  set I := Stacks.Divisors.zeroScheme D.X D.L t
  have hpb := Scheme.IdealSheafData.isPullback_comap I e
  set m := Scheme.IdealSheafData.subschemeMap (I.comap e) I e (I.le_map_comap e)
  have : IsIso m := hpb.isIso_snd_of_isIso
  have hcomp : (I.comap e).subschemeι ≫ D.baseChangeToSpec D.k = m ≫ I.subschemeι ≫ D.toBase := by
    rw [hspec, ← Category.assoc, ← Scheme.IdealSheafData.subschemeMap_subschemeι, Category.assoc]
  rw [hdiv, hcomp] at h
  exact (MorphismProperty.cancel_left_of_respectsIso @GeometricallyIrreducible m _).mp h

end BaseField

/-! ### From a nonzero polynomial to dense opens of `V` and `ℙ(V)` -/

/-- **A property of coefficient vectors that holds off a hypersurface holds on dense opens of
`𝔸ᴺ⁺¹_k` and of `ℙᴺ_k`**, provided it is invariant under nonzero rescaling. -/
private theorem exists_dense_opens_of_polynomial {k : Type u} [Field k] [IsAlgClosed k] {N : ℕ}
    (p : (Fin (N + 1) → k) → Prop) (hp : ∀ (c : Fin (N + 1) → k) (t : k), t ≠ 0 → p (t • c) → p c)
    (Q : MvPolynomial (Fin (N + 1)) k) (hQ0 : Q ≠ 0)
    (hQ : ∀ c : Fin (N + 1) → k, MvPolynomial.eval c Q ≠ 0 → p c) :
    (∃ U : (coefficientSpace k N).Opens, Dense (U : Set (coefficientSpace k N)) ∧
      ∀ c : Fin (N + 1) → k, coefficientPoint c ∈ U → p c) ∧
    (∃ U : (AlgebraicGeometry.Proj
        (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)).Opens,
      Dense (U : Set (AlgebraicGeometry.Proj
        (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))) ∧
      ∀ (c : Fin (N + 1) → k) (hc : c ≠ 0), dualPoint c hc ∈ U → p c) := by
  classical
  refine ⟨⟨PrimeSpectrum.basicOpen Q, dense_basicOpen_of_ne_zero hQ0, fun c hc => hQ c ?_⟩, ?_⟩
  · intro h0
    change Q ∉ RingHom.ker (MvPolynomial.eval c) at hc
    exact hc (RingHom.mem_ker.mpr h0)
  obtain ⟨d, hd⟩ : ∃ d, MvPolynomial.homogeneousComponent d Q ≠ 0 := by
    by_contra! h
    exact hQ0 ((MvPolynomial.sum_homogeneousComponent Q).symm.trans
      (Finset.sum_eq_zero fun i _ => h i))
  refine ⟨ProjectiveSpectrum.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)
      (MvPolynomial.homogeneousComponent d Q), dense_projectiveSpace_basicOpen hd,
    fun c hc hmem => ?_⟩
  have hhc : MvPolynomial.eval c (MvPolynomial.homogeneousComponent d Q) ≠ 0 := by
    intro h0
    change MvPolynomial.homogeneousComponent d Q ∉
      (RingHom.ker (MvPolynomial.eval c)).homogeneousCore
        (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) at hmem
    exact hmem (Ideal.mem_homogeneousCore_of_homogeneous_of_mem
      ⟨d, MvPolynomial.homogeneousComponent_isHomogeneous d Q⟩ (RingHom.mem_ker.mpr h0))
  obtain ⟨t, ht, htQ⟩ := exists_ne_zero_eval_smul_ne_zero Q c hhc
  exact hp c t ht (hQ (t • c) htQ)

/-! ### Commutative algebra: a codimension-two complete intersection -/

/-- In a space where `η` lies in every nonempty open set, a constructible set containing `η`
contains an open neighbourhood of `η`, and one missing `η` misses an open neighbourhood. -/
private theorem exists_isOpen_of_isConstructible {X : Type*} [TopologicalSpace X] {η : X}
    (hη : ∀ U : Set X, IsOpen U → U.Nonempty → η ∈ U) {s : Set X}
    (hs : Topology.IsConstructible s) :
    (η ∈ s → ∃ U, IsOpen U ∧ η ∈ U ∧ U ⊆ s) ∧ (η ∉ s → ∃ U, IsOpen U ∧ η ∈ U ∧ U ⊆ sᶜ) := by
  induction hs using Topology.IsConstructible.empty_union_induction with
  | open_retrocompact U hU _ =>
    exact ⟨fun h => ⟨U, hU, h, le_rfl⟩,
      fun h => ⟨Set.univ, isOpen_univ, trivial, fun x _ hx => h (hη U hU ⟨x, hx⟩)⟩⟩
  | union s _ t _ hs ht =>
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rcases h with h | h
      · obtain ⟨U, hU, hηU, hUs⟩ := hs.1 h
        exact ⟨U, hU, hηU, hUs.trans Set.subset_union_left⟩
      · obtain ⟨U, hU, hηU, hUs⟩ := ht.1 h
        exact ⟨U, hU, hηU, hUs.trans Set.subset_union_right⟩
    · rw [Set.mem_union, not_or] at h
      obtain ⟨U, hU, hηU, hUs⟩ := hs.2 h.1
      obtain ⟨V, hV, hηV, hVt⟩ := ht.2 h.2
      refine ⟨U ∩ V, hU.inter hV, ⟨hηU, hηV⟩, ?_⟩
      rw [Set.compl_union]
      exact Set.inter_subset_inter hUs hVt
  | compl s _ hs =>
    refine ⟨hs.2, fun h => ?_⟩
    obtain ⟨U, hU, hηU, hUs⟩ := hs.1 (not_not.mp h)
    exact ⟨U, hU, hηU, by rwa [compl_compl]⟩

/-- **Chevalley, at the generic point.** If `u, w` are algebraically independent elements of a
domain of finite type over a field `k`, there is a nonzero polynomial `h` such that
`(u - c, w - d)` is a proper ideal whenever `h(c, d) ≠ 0`. -/
private theorem exists_polynomial_span_ne_top {k A : Type*} [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] {u w : A} (h : AlgebraicIndependent k ![u, w]) :
    ∃ g : MvPolynomial (Fin 2) k, g ≠ 0 ∧ ∀ c d : k, MvPolynomial.eval ![c, d] g ≠ 0 →
      Ideal.span {u - algebraMap k A c, w - algebraMap k A d} ≠ ⊤ := by
  classical
  set φ : MvPolynomial (Fin 2) k →ₐ[k] A := MvPolynomial.aeval ![u, w] with hφ
  have hinj : Function.Injective φ := h
  letI : Algebra (MvPolynomial (Fin 2) k) A := φ.toRingHom.toAlgebra
  haveI : IsScalarTower k (MvPolynomial (Fin 2) k) A :=
    IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  haveI : Algebra.FiniteType (MvPolynomial (Fin 2) k) A :=
    Algebra.FiniteType.of_restrictScalars_finiteType k _ A
  have hfp : (φ.toRingHom : MvPolynomial (Fin 2) k →+* A).FinitePresentation :=
    (Algebra.FinitePresentation.of_finiteType.mp inferInstance :
      Algebra.FinitePresentation (MvPolynomial (Fin 2) k) A)
  have hcons := PrimeSpectrum.isConstructible_range_comap hfp
  set η : PrimeSpectrum (MvPolynomial (Fin 2) k) := ⟨⊥, Ideal.isPrime_bot⟩
  have hη : ∀ U : Set (PrimeSpectrum (MvPolynomial (Fin 2) k)), IsOpen U → U.Nonempty →
      η ∈ U := by
    rintro U hU ⟨p, hp⟩
    exact ((PrimeSpectrum.le_iff_specializes η p).mp bot_le).mem_open hU hp
  have hηmem :
      η ∈ Set.range (PrimeSpectrum.comap (φ.toRingHom : MvPolynomial (Fin 2) k →+* A)) := by
    refine ⟨⟨⊥, Ideal.isPrime_bot⟩, PrimeSpectrum.ext ?_⟩
    change Ideal.comap _ ⊥ = ⊥
    rw [← RingHom.ker_eq_comap_bot]
    exact (RingHom.injective_iff_ker_eq_bot _).mp hinj
  obtain ⟨U, hU, hηU, hUs⟩ := (exists_isOpen_of_isConstructible hη hcons).1 hηmem
  obtain ⟨-, ⟨g, rfl⟩, hηg, hgU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hηU hU
  refine ⟨g, fun hg0 => ?_, fun c d hcd => ?_⟩
  · simp [hg0] at hηg
  set m : PrimeSpectrum (MvPolynomial (Fin 2) k) :=
    ⟨RingHom.ker (MvPolynomial.eval ![c, d]), RingHom.ker_isPrime _⟩
  have hm : m ∈ (PrimeSpectrum.basicOpen g : Set _) := by
    change g ∉ RingHom.ker _
    rwa [RingHom.mem_ker]
  obtain ⟨Q, hQ⟩ := hUs (hgU hm)
  have hmem : ∀ x ∈ RingHom.ker (MvPolynomial.eval ![c, d]), φ x ∈ Q.asIdeal := by
    intro x hx
    have : x ∈ (PrimeSpectrum.comap (φ.toRingHom : MvPolynomial (Fin 2) k →+* A) Q).asIdeal := by
      rw [hQ]; exact hx
    exact this
  have hu : u - algebraMap k A c ∈ Q.asIdeal := by
    have := hmem (MvPolynomial.X 0 - MvPolynomial.C c) (by simp)
    simpa [hφ] using this
  have hw : w - algebraMap k A d ∈ Q.asIdeal := by
    have := hmem (MvPolynomial.X 1 - MvPolynomial.C d) (by simp)
    simpa [hφ] using this
  intro htop
  apply Q.isPrime.ne_top
  rw [eq_top_iff, ← htop, Ideal.span_le]
  rintro x (rfl | rfl)
  · exact hu
  · exact hw

/-- **A complete intersection of codimension two cut out by two independent functions.** If
`u, w` are algebraically independent elements of a domain of finite type over an infinite field
`k`, then for suitable `c, d ∈ k` the ideal `(u - c, w - d)` is proper and each of its minimal
primes has height exactly two. -/
private theorem exists_forall_mem_minimalPrimes_height_eq_two {k A : Type*} [Field k] [Infinite k]
    [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] {u w : A}
    (h : AlgebraicIndependent k ![u, w]) :
    ∃ c d : k, Ideal.span {u - algebraMap k A c, w - algebraMap k A d} ≠ ⊤ ∧
      ∀ P ∈ (Ideal.span {u - algebraMap k A c, w - algebraMap k A d}).minimalPrimes,
        P.height = 2 := by
  classical
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  obtain ⟨g, hg0, hg⟩ := exists_polynomial_span_ne_top h
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : Fin 2 → k, MvPolynomial.eval x₀ g ≠ 0 := by
    by_contra! hcon
    exact hg0 (MvPolynomial.funext fun x => by simp [hcon x])
  set c := x₀ 0
  set a := u - algebraMap k A c with ha
  -- the polynomial `d ↦ g(c, d)`
  set G : Polynomial k := MvPolynomial.eval₂ Polynomial.C ![Polynomial.C c, Polynomial.X] g
  have hG : ∀ d : k, G.eval d = MvPolynomial.eval ![c, d] g := by
    intro d
    change Polynomial.evalRingHom d (MvPolynomial.eval₂ Polynomial.C _ g) = _
    rw [MvPolynomial.eval₂_comp_left]
    have h1 : (Polynomial.evalRingHom d).comp Polynomial.C = RingHom.id k := by
      ext; simp
    have h2 : (Polynomial.evalRingHom d ∘ ![Polynomial.C c, Polynomial.X]) = ![c, d] := by
      funext i; fin_cases i <;> simp
    rw [h1, h2]
    rfl
  have hG0 : G ≠ 0 := by
    intro h0
    apply hx₀
    have := hG (x₀ 1)
    rw [h0, Polynomial.eval_zero] at this
    rw [show x₀ = ![c, x₀ 1] from by funext i; fin_cases i <;> rfl]
    exact this.symm
  -- the finitely many forbidden values of `d`
  set M := (Ideal.span {a}).minimalPrimes
  have hMfin : M.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing A _
  set F : Set k := ⋃ p ∈ M, {d | w - algebraMap k A d ∈ p}
  have hFfin : F.Finite := by
    refine hMfin.biUnion fun p hp => Set.Subsingleton.finite ?_
    intro d₁ hd₁ d₂ hd₂
    by_contra hne
    have hpp := (show p ∈ (Ideal.span {a}).minimalPrimes from hp).isPrime
    have hsub : algebraMap k A (d₁ - d₂) ∈ p := by
      have := p.sub_mem hd₂ hd₁
      rw [map_sub]
      convert this using 1
      ring
    exact hpp.ne_top (Ideal.eq_top_of_isUnit_mem _ hsub
      ((isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hne)).map _))
  have hRfin : {d : k | G.eval d = 0}.Finite :=
    (G.roots.toFinset.finite_toSet).subset fun d hd => by
      simpa [Polynomial.mem_roots hG0] using hd
  obtain ⟨d, hd⟩ := Infinite.exists_notMem_finset (hFfin.union hRfin).toFinset
  rw [Set.Finite.mem_toFinset, Set.mem_union, not_or] at hd
  obtain ⟨hdF, hdR⟩ := hd
  have hgcd : MvPolynomial.eval ![c, d] g ≠ 0 := by
    rw [← hG]; exact hdR
  refine ⟨c, d, hg c d hgcd, fun P hP => le_antisymm ?_ ?_⟩
  · have := Ideal.height_le_card_of_mem_minimalPrimes_span_finset
      (s := {a, w - algebraMap k A d}) (p := P) (by simpa using hP)
    exact this.trans (by exact_mod_cast Finset.card_le_two)
  · haveI := hP.isPrime
    have haP : a ∈ P := hP.1.2 (Ideal.subset_span (by simp [ha]))
    have hbP : w - algebraMap k A d ∈ P := hP.1.2 (Ideal.subset_span (by simp))
    obtain ⟨p, hp, hpP⟩ := Ideal.exists_minimalPrimes_le (I := Ideal.span {a}) (J := P)
      (Ideal.span_le.mpr (by simpa using haP))
    haveI := hp.isPrime
    have hap : a ∈ p := hp.1.2 (Ideal.subset_span rfl)
    have ha0 : a ≠ 0 := by
      intro h0
      have htr := h.transcendental 0
      apply htr
      have : u = algebraMap k A c := sub_eq_zero.mp h0
      simp only [Matrix.cons_val_zero]
      rw [this]
      exact isAlgebraic_algebraMap c
    have hbp : w - algebraMap k A d ∉ p := fun hb => hdF (Set.mem_biUnion hp hb)
    have hp1 : 1 ≤ p.height := by
      rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
      rintro rfl
      exact ha0 hap
    have hlt : p.height < P.height :=
      Ideal.height_strict_mono_of_isPrime (lt_of_le_of_ne hpP (fun he => hbp (he ▸ hbP)))
    exact Order.add_one_le_of_lt (hp1.trans_lt hlt)

/-! ### Two algebraically independent generators -/

/-- **Two independent generators.** Let `ι : κ → K` be a `k`-embedding of fields, and suppose
every element of `κ` is a quotient of values of a ring map `ε : R → κ` whose composite with `ι`
takes values in the `k`-algebra generated by `r₀, …, rₙ₋₁ ∈ K`. If `trdeg_k κ ≥ 2`, then two of
the `rᵢ` are algebraically independent over `k`. -/
private theorem exists_ne_algebraicIndependent_of_two_le_trdeg {k κ K R : Type*} [Field k] [Field κ]
    [Field K] [Algebra k κ] [Algebra k K] [CommRing R] (ι : κ →ₐ[k] K) (ε : R →+* κ)
    (hε : ∀ z : κ, ∃ a b : R, z = ε a / ε b) {n : ℕ} (r : Fin n → K)
    (hR : ∀ a : R, ι (ε a) ∈ Algebra.adjoin k (Set.range r))
    (htr : (2 : Cardinal) ≤ Cardinal.lift.{0} (Algebra.trdeg k κ)) :
    ∃ i j, i ≠ j ∧ AlgebraicIndependent k ![r i, r j] := by
  classical
  -- two independent elements of `κ`
  obtain ⟨ιb, b, hb⟩ := exists_isTranscendenceBasis' k κ
  have h2 : Cardinal.lift.{0} (Cardinal.mk ιb) ≥ Cardinal.lift.{_, 0} (Cardinal.mk (Fin 2)) := by
    rw [hb.cardinalMk_eq_trdeg, Cardinal.mk_fin, Cardinal.lift_natCast]
    exact htr
  obtain ⟨e⟩ := Cardinal.lift_mk_le'.mp h2
  have hx : AlgebraicIndependent k (b ∘ e) := hb.1.comp e e.injective
  -- the field generated by the `rᵢ`
  set F := IntermediateField.adjoin k (Set.range r)
  have hmemF : ∀ z : κ, ι z ∈ F := by
    intro z
    obtain ⟨a, b', rfl⟩ := hε z
    rw [map_div₀]
    exact F.div_mem (IntermediateField.algebra_adjoin_le_adjoin k _ (hR a))
      (IntermediateField.algebra_adjoin_le_adjoin k _ (hR b'))
  let ιF : κ →ₐ[k] F := ι.codRestrict F.toSubalgebra hmemF
  have hy : AlgebraicIndependent k (ιF ∘ (b ∘ e)) := hx.map' ιF.toRingHom.injective
  let r' : Fin n → F := fun i => ⟨r i, IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩⟩
  have hmap : Subalgebra.map F.val (Algebra.adjoin k (Set.range r')) =
      Algebra.adjoin k (Set.range r) := by
    rw [AlgHom.map_adjoin, ← Set.range_comp]
    rfl
  have hlift : ∀ a ∈ Algebra.adjoin k (Set.range r), ∃ a' ∈ Algebra.adjoin k (Set.range r'),
      (a' : K) = a := by
    intro a ha
    rw [← hmap] at ha
    obtain ⟨a', ha', rfl⟩ := ha
    exact ⟨a', ha', rfl⟩
  haveI : Algebra.IsAlgebraic (Algebra.adjoin k (Set.range r')) F := by
    refine ⟨fun z => ?_⟩
    obtain ⟨a, ha, b', hb', hz⟩ := IntermediateField.mem_adjoin_iff_div.mp z.2
    obtain ⟨a', ha', rfl⟩ := hlift a ha
    obtain ⟨b'', hb'', rfl⟩ := hlift b' hb'
    by_cases hb0 : b'' = 0
    · rw [show z = 0 from Subtype.ext (by simpa [hb0] using hz)]
      exact isAlgebraic_zero
    · have hmul : b'' * z = a' := by
        apply Subtype.ext
        change (b'' : K) * (z : K) = a'
        rw [hz, mul_div_cancel₀]
        exact fun h0 => hb0 (Subtype.ext h0)
      refine IsAlgebraic.of_mul (y := b'') (mem_nonZeroDivisors_of_ne_zero hb0)
        (isAlgebraic_algebraMap (⟨b'', hb''⟩ : Algebra.adjoin k (Set.range r'))) ?_
      rw [hmul]
      exact isAlgebraic_algebraMap (⟨a', ha'⟩ : Algebra.adjoin k (Set.range r'))
  obtain ⟨t, hts, ht⟩ := exists_isTranscendenceBasis_subset (R := k) (Set.range r')
  have h2t : Cardinal.lift.{0} (Cardinal.mk t) ≥ Cardinal.lift.{_, 0} (Cardinal.mk (Fin 2)) := by
    rw [ht.cardinalMk_eq_trdeg]
    exact hy.lift_cardinalMk_le_trdeg
  obtain ⟨e'⟩ := Cardinal.lift_mk_le'.mp h2t
  obtain ⟨i, hi⟩ := hts (e' 0).2
  obtain ⟨j, hj⟩ := hts (e' 1).2
  have hij : i ≠ j := by
    rintro rfl
    have := e'.injective (Subtype.ext (hi.symm.trans hj))
    exact absurd this (by decide)
  refine ⟨i, j, hij, ?_⟩
  have hz : AlgebraicIndependent k ((fun l : t => (l : F)) ∘ e') := ht.1.comp e' e'.injective
  have hz' : AlgebraicIndependent k (F.val ∘ ((fun l : t => (l : F)) ∘ e')) :=
    hz.map' F.val.toRingHom.injective
  convert hz' using 1
  funext l
  fin_cases l
  · simp [← hi, r']
  · simp [← hj, r']

/-! ### An irreducible component of codimension two -/

/-- **A codimension-two component from a height-two ideal.** If a closed set `C` meets an affine
open `U` in the zero locus of a proper ideal `I` of `Γ(X, U)` all of whose minimal primes have
height two, and `D₁` misses `U`, then `C` has an irreducible component of codimension two not
contained in `D₁`. -/
private theorem exists_maximal_codimension_eq_two {X : Scheme} {U : X.Opens} (hU : IsAffineOpen U)
    {C D₁ : Set X} (hC : IsClosed C) {I : Ideal Γ(X, U)}
    (hCI : ∀ p : PrimeSpectrum Γ(X, U), hU.fromSpec p ∈ C ↔ (I : Set Γ(X, U)) ⊆ p.asIdeal)
    (hD₁ : ∀ x ∈ U, x ∉ D₁) (hI : I ≠ ⊤) (h2 : ∀ P ∈ I.minimalPrimes, P.height = 2) :
    ∃ Z : IrreducibleCloseds X, Maximal (fun W : IrreducibleCloseds X => (W : Set X) ⊆ C) Z ∧
      ¬ (Z : Set X) ⊆ D₁ ∧ codimension Z = 2 := by
  obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hI
  obtain ⟨P, hP, -⟩ := Ideal.exists_minimalPrimes_le (J := m) hIm
  haveI := hP.isPrime
  set p₀ : PrimeSpectrum Γ(X, U) := ⟨P, hP.isPrime⟩
  let f : PrimeSpectrum Γ(X, U) → X := hU.fromSpec
  have hf : Topology.IsOpenEmbedding f := hU.fromSpec.isOpenEmbedding
  have hrange : Set.range f = (U : Set X) := hU.range_fromSpec
  set z := f p₀
  have hzU : z ∈ (U : Set X) := by
    rw [← hrange]
    exact ⟨p₀, rfl⟩
  have hzC : z ∈ C := (hCI p₀).mpr hP.1.2
  let Z : IrreducibleCloseds X := ⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hZz : z ∈ (Z : Set X) := subset_closure rfl
  refine ⟨Z, ⟨closure_minimal (Set.singleton_subset_iff.mpr hzC) hC, fun W hW hZW => ?_⟩,
    fun h => hD₁ z hzU (h hZz), ?_⟩
  · obtain ⟨w, hw⟩ := QuasiSober.sober W.isIrreducible W.isClosed
    have hwz : w ⤳ z := hw.specializes (hZW hZz)
    have hwU : w ∈ (U : Set X) := hwz.mem_open U.isOpen hzU
    rw [← hrange] at hwU
    obtain ⟨q, rfl⟩ := hwU
    have hqP : q.asIdeal ≤ P :=
      (PrimeSpectrum.le_iff_specializes q p₀).mpr (hf.isInducing.specializes_iff.mp hwz)
    have hPq : P ≤ q.asIdeal := hP.2 ⟨q.isPrime, (hCI q).mp (hW hw.mem)⟩ hqP
    have hq : q = p₀ := PrimeSpectrum.ext (le_antisymm hqP hPq)
    intro x hx
    have hx' : x ∈ (W : Set X) := hx
    rw [← hw.def, hq] at hx'
    exact hx'
  · have hne : (f ⁻¹' (Z : Set X)).Nonempty := ⟨p₀, hZz⟩
    rw [← PrimeSpectrum.height_vanishingIdeal_preimage hf Z hne]
    have hpre : f ⁻¹' (Z : Set X) = closure {p₀} := by
      change f ⁻¹' closure {f p₀} = closure {p₀}
      rw [hf.isInducing.closure_eq_preimage_closure_image, Set.image_singleton]
    rw [hpre, PrimeSpectrum.vanishingIdeal_closure, PrimeSpectrum.vanishingIdeal_singleton]
    exact h2 P hP

/-! ### Sections off the zero scheme -/

/-- **A point off the zero scheme of a section lies in its nonvanishing open.** -/
private theorem mem_nonvanishingOpen_of_notMem_supportSet_zeroScheme {X : Scheme.{u}}
    (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [Stacks.Ample.IsInvertibleModule X L] (s : Γ(L, ⊤)) (x : X)
    (hx : x ∉ (zeroScheme X L s).supportSet) :
    x ∈ Stacks.NonvanishingOpen.nonvanishingOpen X L s := by
  obtain ⟨U, hxU⟩ := Stacks.Divisors.exists_affineOpens_mem x
  obtain ⟨g, hxg, -, ⟨e⟩⟩ := exists_basicOpen_linearEquiv L U x hxU
  rw [Scheme.IdealSheafData.mem_supportSet_iff_of_mem
      (U := ⟨X.basicOpen g, U.2.basicOpen g⟩) hxg,
    zeroScheme_ideal_of_trivialization X L s ⟨X.basicOpen g, U.2.basicOpen g⟩ e _ rfl,
    Scheme.zeroLocus_span, Scheme.zeroLocus_singleton, Set.mem_compl_iff, not_not] at hx
  set a : Γ(X, X.basicOpen g) := e (L.presheaf.map (homOfLE le_top).op s) with ha
  have hunit := (X.mem_basicOpen a x hxg).mp hx
  have hsW : L.presheaf.map (homOfLE (le_top : X.basicOpen g ≤ ⊤)).op s = a • e.symm 1 := by
    rw [← map_smul e.symm a 1, smul_eq_mul, mul_one, ha, e.symm_apply_apply]
  have hgerm : (L.presheaf.Γgerm x).hom s =
      (X.presheaf.germ (X.basicOpen g) x hxg).hom a •
        (L.presheaf.germ (X.basicOpen g) x hxg).hom (e.symm 1) := by
    rw [← TopCat.Presheaf.Γgerm_res_apply
      (i := homOfLE (le_top : X.basicOpen g ≤ ⊤)) L.presheaf x hxg s, hsW,
      Stacks.ModuleStalk.germ_smul]
  have hgen := Stacks.PicSurjectiveOpen.notMem_maximalIdeal_smul_top_germ_of_bijective_smul L
    (U.2.basicOpen g) (e.symm 1) (by
      have : (fun r : Γ(X, X.basicOpen g) => r • e.symm 1) = e.symm := by
        funext r; rw [← map_smul e.symm r 1, smul_eq_mul, mul_one]
      rw [this]; exact e.symm.bijective) hxg
  change x ∈ Stacks.NonvanishingOpen.nonvanishingOpen X L s
  rw [Stacks.NonvanishingSpelling.mem_nonvanishingOpen_iff, hgerm,
    Stacks.ModuleStalk.smul_mem_maximalSmul_iff]
  rintro (h | h)
  · exact h hunit
  · exact hgen h

/-! ### The charts of `ℙ(V)` -/

section Chart

open HomogeneousLocalization
open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections (degreeOneElement
  classifies_classifyingPair pow_degreeOneElement nonvanishingOpen_twistOneSection
  veroneseOfLinearMap)

local notation "𝒢" => Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.grading

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow

/-- **The chart ring of `ℙ(V)` is generated by the degree-one fractions.** For a vector `w` and
a basis `b` of `V`, the ring `Sym(V)_{(w)}` of degree-zero fractions is generated as a
`k`-algebra by the fractions `bⱼ / w`. -/
private theorem away_mem_adjoin_range {k V : Type u} [Field k] [AddCommGroup V] [Module k V]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι k V) (w : V)
    (α : Away (𝒢 k V) (SymmetricAlgebra.ι k V w)) :
    α ∈ Algebra.adjoin k (Set.range fun j => Away.mk (𝒢 k V)
      (degreeOneElement k V w).2 1 (SymmetricAlgebra.ι k V (b j))
      (by simpa using (degreeOneElement k V (b j)).2)) := by
  classical
  set hf := (degreeOneElement k V w).2
  set S := Algebra.adjoin k (Set.range fun j => Away.mk (𝒢 k V)
      hf 1 (SymmetricAlgebra.ι k V (b j))
      (by simpa using (degreeOneElement k V (b j)).2))
  -- the degree-one fractions lie in `S`
  have h1 : ∀ v : V, ∀ hv, Away.mk (𝒢 k V) hf 1 (SymmetricAlgebra.ι k V v) hv ∈ S := by
    intro v hv
    have hsum : Away.mk (𝒢 k V) hf 1 (SymmetricAlgebra.ι k V v) hv =
        ∑ j, b.repr v j • Away.mk (𝒢 k V) hf 1 (SymmetricAlgebra.ι k V (b j))
          (by simpa using (degreeOneElement k V (b j)).2) := by
      apply val_injective
      have hv' : SymmetricAlgebra.ι k V v = ∑ j, b.repr v j • SymmetricAlgebra.ι k V (b j) := by
        conv_lhs => rw [← b.sum_repr v]
        rw [map_sum]
        exact Finset.sum_congr rfl fun j _ => map_smul _ _ _
      rw [Away.val_mk, ← HomogeneousLocalization.algebraMap_apply, map_sum]
      simp only [HomogeneousLocalization.algebraMap_apply, val_smul, Away.val_mk,
        Localization.smul_mk]
      rw [← Localization.mk_sum, ← hv']
    rw [hsum]
    refine Subalgebra.sum_mem _ fun j _ => Subalgebra.smul_mem _ ?_ _
    exact Algebra.subset_adjoin (Set.mem_range_self j)
  -- every fraction lies in `S`
  have hall : ∀ n : ℕ, ∀ a : SymmetricAlgebra k V, ∀ ha : a ∈ 𝒢 k V (n • 1),
      Away.mk (𝒢 k V) hf n a ha ∈ S := by
    intro n
    induction n with
    | zero =>
      intro a ha
      have ha' : a ∈ (1 : Submodule k (SymmetricAlgebra k V)) := by
        simpa [Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.grading] using ha
      rw [Submodule.one_eq_range] at ha'
      obtain ⟨r, rfl⟩ := ha'
      have : Away.mk (𝒢 k V) hf 0 (Algebra.linearMap k _ r) ha =
          algebraMap k (Away (𝒢 k V) _) r := by
        apply val_injective
        rw [Away.val_mk, HomogeneousLocalization.val_algebraMap]
        have h1 : (⟨(degreeOneElement k V w : SymmetricAlgebra k V) ^ 0, ⟨0, rfl⟩⟩ :
            Submonoid.powers (degreeOneElement k V w : SymmetricAlgebra k V)) = 1 :=
          Subtype.ext (pow_zero _)
        rw [h1, Localization.mk_one_eq_algebraMap, Algebra.linearMap_apply,
          ← IsScalarTower.algebraMap_apply]
      rw [this]
      exact Subalgebra.algebraMap_mem _ r
    | succ n ih =>
      intro a ha
      have ha' : a ∈ (SymmetricAlgebra.ι k V).range ^ n * (SymmetricAlgebra.ι k V).range := by
        have : a ∈ (SymmetricAlgebra.ι k V).range ^ (n + 1) := by
          simpa [Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.grading] using ha
        rwa [pow_succ] at this
      induction ha' using Submodule.mul_induction_on' with
      | mem_mul_mem m hm y hy =>
        obtain ⟨v, rfl⟩ := hy
        have hm' : m ∈ 𝒢 k V (n • 1) := by
          simpa [Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.grading] using hm
        have hv' : SymmetricAlgebra.ι k V v ∈ 𝒢 k V (1 • 1) := by
          simpa using (degreeOneElement k V v).2
        have : Away.mk (𝒢 k V) hf (n + 1) (m * SymmetricAlgebra.ι k V v) ha =
            Away.mk (𝒢 k V) hf n m hm' * Away.mk (𝒢 k V) hf 1 (SymmetricAlgebra.ι k V v) hv' := by
          apply val_injective
          rw [val_mul, Away.val_mk, Away.val_mk, Away.val_mk, Localization.mk_mul]
          congr 1
          exact Subtype.ext (by simp [pow_succ])
        rw [this]
        exact S.mul_mem (ih m hm') (h1 v hv')
      | add x hx y hy hxS hyS =>
        have hx' : x ∈ 𝒢 k V ((n + 1) • 1) := by
          rw [← pow_succ] at hx
          simpa [Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.grading] using hx
        have hy' : y ∈ 𝒢 k V ((n + 1) • 1) := by
          rw [← pow_succ] at hy
          simpa [Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.grading] using hy
        have : Away.mk (𝒢 k V) hf (n + 1) (x + y) ha =
            Away.mk (𝒢 k V) hf (n + 1) x hx' + Away.mk (𝒢 k V) hf (n + 1) y hy' := by
          apply val_injective
          rw [val_add, Away.val_mk, Away.val_mk, Away.val_mk, Localization.add_mk_self]
        rw [this]
        exact S.add_mem (hxS hx') (hyS hy')
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective (𝒢 k V) hf α
  exact hall n a ha

/-- The basic open of a degree-zero fraction `g^d / f^e` on `D₊(f)` is `D₊(f) ∩ D₊(g)`. -/
private theorem basicOpen_awayToSection_isLocalizationElem {A σ : Type*} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] {f g : A} {d e : ℕ} (hf : f ∈ 𝒜 d)
    (hg : g ∈ 𝒜 e) (hd : 0 < d) (he : 0 < e) :
    (AlgebraicGeometry.Proj 𝒜).basicOpen (Proj.awayToSection 𝒜 f (Away.isLocalizationElem hf hg)) =
      Proj.basicOpen 𝒜 f ⊓ Proj.basicOpen 𝒜 g := by
  set ι := Proj.awayι 𝒜 f hf hd
  have hrange : ι.opensRange = Proj.basicOpen 𝒜 f := Proj.opensRange_awayι 𝒜 f hf hd
  have hpre : ι ⁻¹ᵁ (AlgebraicGeometry.Proj 𝒜).basicOpen
      (Proj.awayToSection 𝒜 f (Away.isLocalizationElem hf hg)) =
      ι ⁻¹ᵁ Proj.basicOpen 𝒜 g := by
    rw [Proj.awayι_preimage_basicOpen 𝒜 hf hd hg he]
    have h := Scheme.basicOpen_appLE ι ⊤ (Proj.basicOpen 𝒜 f)
      (Stacks.AlgebraicGeometry.ProjChartSections.awayι_preimage_basicOpen_self 𝒜 hf hd).ge
      (Proj.awayToSection 𝒜 f (Away.isLocalizationElem hf hg))
    rw [← CategoryTheory.comp_apply,
      Stacks.AlgebraicGeometry.ProjChartSections.awayToSection_comp_awayι_appLE 𝒜 hf hd,
      basicOpen_eq_of_affine, top_inf_eq] at h
    exact h.symm
  have h1 := ι.image_preimage_eq_opensRange_inf
    ((AlgebraicGeometry.Proj 𝒜).basicOpen (Proj.awayToSection 𝒜 f (Away.isLocalizationElem hf hg)))
  have h2 := ι.image_preimage_eq_opensRange_inf (Proj.basicOpen 𝒜 g)
  rw [hrange, inf_eq_right.mpr ((AlgebraicGeometry.Proj 𝒜).basicOpen_le _)] at h1
  rw [hrange] at h2
  rw [← h1, ← h2, hpre]

/-- The preimage of `D₊(v)` under the morphism of a generating system is `X_{ψ(v)}`. -/
private theorem preimage_basicOpen_morphismOfGeneratingSections' {k V : Type u} [Field k]
    [AddCommGroup V] [Module k V] {X : Scheme.{u}} [X.Over (Spec (.of k))] {L : X.Modules}
    [Stacks.Ample.IsInvertibleModule X L] (ψ : V →ₗ[k] Γ(L, ⊤))
    (hψ : ⨆ v : V, nonvanishingOpen X L (ψ v) = ⊤) (v : V) :
    morphismOfGeneratingSections k V L ψ hψ ⁻¹ᵁ
        Proj.basicOpen (𝒢 k V) (SymmetricAlgebra.ι k V v) =
      nonvanishingOpen X L (ψ v) := by
  refine ((classifies_classifyingPair k V L ψ hψ).1 (degreeOneElement k V v)).trans ?_
  change nonvanishingOpen X (Stacks.TensorPowers.natTensorPow L 1)
      ((veroneseOfLinearMap k V L ψ).pow (degreeOneElement k V v).2 1) = _
  rw [pow_degreeOneElement, nonvanishingOpen_twistOneSection]

/-- On the chart `D₊(f)` of a linear form `f`, the restriction `Sym(V)_{(f)} → Γ(D₊(f))` is an
isomorphism. -/
private theorem isIso_awayToSection {k V : Type u} [Field k] [AddCommGroup V] [Module k V]
    {f : SymmetricAlgebra k V} (hf : f ∈ 𝒢 k V 1) : IsIso (Proj.awayToSection (𝒢 k V) f) := by
  rw [← Proj.basicOpenIsoAway_hom (𝒢 k V) f hf Nat.one_pos]
  infer_instance

/-- On the chart `D₊(f)` of a linear form `f`, the structure map of `ℙ(V)` is the inclusion of
the scalars into the chart ring `Sym(V)_{(f)}`. -/
private theorem appLE_projectiveSpaceOfModuleToSpec_basicOpen {k V : Type u} [Field k]
    [AddCommGroup V] [Module k V] {f : SymmetricAlgebra k V}
    (hf : f ∈ 𝒢 k V 1) (e : Proj.basicOpen (𝒢 k V) f ≤ projectiveSpaceOfModuleToSpec k V ⁻¹ᵁ ⊤) :
    (projectiveSpaceOfModuleToSpec k V).appLE ⊤ (Proj.basicOpen (𝒢 k V) f) e =
      (Scheme.ΓSpecIso (.of k)).hom ≫ CommRingCat.ofHom (algebraMap k (Away (𝒢 k V) f)) ≫
        Proj.awayToSection (𝒢 k V) f := by
  set ι := Proj.awayι (𝒢 k V) f hf Nat.one_pos
  have he := (Stacks.AlgebraicGeometry.ProjChartSections.awayι_preimage_basicOpen_self
    (𝒢 k V) hf Nat.one_pos).ge
  have hcomp := Stacks.AlgebraicGeometry.ProjChartSections.awayToSection_comp_awayι_appLE
    (𝒢 k V) hf Nat.one_pos
  haveI := isIso_awayToSection hf
  haveI : IsIso (ι.appLE (Proj.basicOpen (𝒢 k V) f) ⊤ he) := by
    have : ι.appLE (Proj.basicOpen (𝒢 k V) f) ⊤ he =
        inv (Proj.awayToSection (𝒢 k V) f) ≫ (Scheme.ΓSpecIso _).inv := by
      rw [← hcomp, IsIso.inv_hom_id_assoc]
    rw [this]
    infer_instance
  rw [← cancel_mono (ι.appLE (Proj.basicOpen (𝒢 k V) f) ⊤ he),
    Scheme.Hom.appLE_comp_appLE, Category.assoc, Category.assoc, hcomp]
  have hq : ι ≫ projectiveSpaceOfModuleToSpec k V =
      Spec.map (CommRingCat.ofHom (algebraMap k (Away (𝒢 k V) f))) := by
    have hp : projectiveSpaceOfModuleToSpec k V =
        AlgebraicGeometry.Proj.toSpecZero (𝒢 k V) ≫
          Spec.map (CommRingCat.ofHom (algebraMap k ↥(𝒢 k V 0))) := rfl
    rw [hp, ← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
    congr 1
  rw [Stacks.AlgebraicGeometry.ProjChartSections.appLE_top_top, hq, ← Category.assoc,
    Iso.eq_comp_inv]
  exact Scheme.ΓSpecIso_naturality _

/-- The symmetric algebra of a finite-dimensional vector space is of finite type. -/
private theorem finiteType_symmetricAlgebra {k V : Type u} [Field k] [AddCommGroup V]
    [Module k V] {ι : Type*} [Fintype ι] (bs : Module.Basis ι k V) :
    Algebra.FiniteType k (SymmetricAlgebra k V) := by
  classical
  refine ⟨⟨Finset.univ.image (fun j => SymmetricAlgebra.ι k V (bs j)), ?_⟩⟩
  rw [eq_top_iff]
  intro a _
  clear ‹a ∈ ⊤›
  induction a using SymmetricAlgebra.induction with
  | algebraMap r => exact Subalgebra.algebraMap_mem _ r
  | ι x =>
    rw [← bs.sum_repr x, map_sum]
    refine Subalgebra.sum_mem _ fun j _ => ?_
    rw [map_smul]
    exact Subalgebra.smul_mem _ (Algebra.subset_adjoin (by simp)) _
  | mul a b ha hb => exact mul_mem ha hb
  | add a b ha hb => exact add_mem ha hb

/-- The structure morphism `ℙ(V) → Spec k` of a finite-dimensional `V` is locally of finite
type. -/
private theorem locallyOfFiniteType_projectiveSpaceOfModuleToSpec {k V : Type u} [Field k]
    [AddCommGroup V] [Module k V] {ι : Type*} [Fintype ι]
    (bs : Module.Basis ι k V) : LocallyOfFiniteType (projectiveSpaceOfModuleToSpec k V) := by
  have hp : projectiveSpaceOfModuleToSpec k V =
      AlgebraicGeometry.Proj.toSpecZero (𝒢 k V) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k ↥(𝒢 k V 0))) := rfl
  haveI := finiteType_symmetricAlgebra bs
  haveI : Algebra.FiniteType (𝒢 k V 0) (SymmetricAlgebra k V) :=
    Algebra.FiniteType.of_restrictScalars_finiteType k _ _
  haveI : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k ↥(𝒢 k V 0)))) := by
    refine HasRingHomProperty.Spec_iff.mpr (RingHom.FiniteType.of_surjective _ fun z => ?_)
    have hz := z.2
    simp only [Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.grading,
      SymPow.symmetricPower, pow_zero, Submodule.one_eq_range] at hz
    obtain ⟨r, hr⟩ := hz
    exact ⟨r, Subtype.ext hr⟩
  rw [hp]
  infer_instance

end Chart

/-! ### Residue fields of an affine open -/

/-- Every element of the residue field at a point of an affine open is a quotient of values of
sections over that open. -/
private theorem exists_eq_evaluation_div {Y : Scheme} {O : Y.Opens} (hO : IsAffineOpen O) {y : Y}
    (hy : y ∈ O) (z : Y.residueField y) :
    ∃ a b : Γ(Y, O), z = Y.evaluation O y hy a / Y.evaluation O y hy b := by
  letI := TopCat.Presheaf.algebra_section_stalk Y.presheaf (⟨y, hy⟩ : O)
  haveI := hO.isLocalization_stalk ⟨y, hy⟩
  obtain ⟨s, rfl⟩ := Y.residue_surjective y z
  obtain ⟨⟨a, ⟨b, hb⟩⟩, rfl⟩ := IsLocalization.mk'_surjective
    (hO.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl s
  refine ⟨a, b, ?_⟩
  have hunit : IsUnit (algebraMap Γ(Y, O) (Y.presheaf.stalk y) b) :=
    IsLocalization.map_units _ (⟨b, hb⟩ : (hO.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl)
  have h1 : Y.evaluation O y hy a = Y.residue y (algebraMap Γ(Y, O) _ a) := rfl
  have h2 : Y.evaluation O y hy b = Y.residue y (algebraMap Γ(Y, O) _ b) := rfl
  have hne : Y.residue y (algebraMap Γ(Y, O) (Y.presheaf.stalk y) b) ≠ 0 :=
    (hunit.map (Y.residue y).hom).ne_zero
  rw [h1, h2, eq_div_iff hne, ← map_mul]
  congr 1
  exact IsLocalization.mk'_spec _ _ _

/-- Evaluating at a point after `appLE` is evaluating after `app`. -/
private theorem evaluation_appLE {X Y : Scheme.{u}} (g : X ⟶ Y) (U : Y.Opens) (W : X.Opens)
    (e : W ≤ g ⁻¹ᵁ U) (x : X) (hx : x ∈ W) :
    g.appLE U W e ≫ X.evaluation W x hx = g.app U ≫ X.evaluation (g ⁻¹ᵁ U) x (e hx) := by
  simp only [Scheme.Hom.appLE, Scheme.evaluation, Category.assoc,
    TopCat.Presheaf.germ_res_assoc]

/-! ### Hypothesis (3) of the Bertini irreducibility theorem -/

section Key

open HomogeneousLocalization
open Stacks.AlgebraicGeometry.ProjectiveSpaceCoordinateSquare
  (morphismOfGeneratingSections_comp_projectiveSpaceOfModuleToSpec
    iSup_nonvanishingOpen_basis_eq_top)
open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections (degreeOneElement)

local notation "𝒢" => Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.grading

/-- **Hypothesis (3) of [Stacks, Tag 0G4F] for a free system whose image has dimension at least
two.** There are vectors `v₁, v₂, v₃` of the system and an irreducible component `Z` of
`H_{v₂} ∩ H_{v₃}` of codimension two not contained in `H_{v₁}`. -/
private theorem exists_component_codimension_two {k : Type u} [Field k] [IsAlgClosed k] {N : ℕ}
    {X : Scheme.{u}} [X.Over (Spec (.of k))] {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L]
    [IsVariety k (X ↘ Spec (.of k))] (s : Fin (N + 1) → Γ(L, ⊤))
    (hs : ⨆ c : Fin (N + 1) → k, nonvanishingOpen X L (systemSection s c) = ⊤)
    (hdim : 2 ≤ topologicalKrullDim
      (Set.range (morphismOfGeneratingSections k (Fin (N + 1) → k) L (systemSection s) hs))) :
    ∃ (v₁ v₂ v₃ : Fin (N + 1) → k) (Z : IrreducibleCloseds X),
      Maximal (fun W : IrreducibleCloseds X => (W : Set X) ⊆
        (systemFamily (k := k) s).divisorSet v₂ ∩ (systemFamily (k := k) s).divisorSet v₃) Z ∧
      ¬ (Z : Set X) ⊆ (systemFamily (k := k) s).divisorSet v₁ ∧ codimension Z = 2 := by
  classical
  set V := Fin (N + 1) → k
  set ψ : V →ₗ[k] Γ(L, ⊤) := systemSection s with hψ
  set φ := morphismOfGeneratingSections k V L ψ hs with hφ
  set q := projectiveSpaceOfModuleToSpec k V with hq
  have hφq : φ ≫ q = X ↘ Spec (.of k) :=
    morphismOfGeneratingSections_comp_projectiveSpaceOfModuleToSpec ψ hs
  set e : Fin (N + 1) → V := fun j => Pi.single j 1 with he
  set ξ := genericPoint X
  -- a chart of `X` containing the generic point, on which `ψ(e i₀)` does not vanish
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, ξ ∈ nonvanishingOpen X L (ψ (e i₀)) := by
    have h := iSup_nonvanishingOpen_basis_eq_top
      (Pi.basisFun k (Fin (N + 1))) ψ hs
    have hξ : ξ ∈ ⨆ i, nonvanishingOpen X L (ψ (Pi.basisFun k (Fin (N + 1)) i)) := by
      rw [h]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hξ
    exact ⟨i, by simpa [e] using hi⟩
  obtain ⟨W, hWaff, hξW, hWle⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hi₀
  haveI : Nonempty W := ⟨⟨ξ, hξW⟩⟩
  set f : SymmetricAlgebra k V := SymmetricAlgebra.ι k V (e i₀) with hfdef
  have hf : f ∈ 𝒢 k V 1 := (degreeOneElement k V (e i₀)).2
  set O := Proj.basicOpen (𝒢 k V) f with hO
  have hle : W ≤ φ ⁻¹ᵁ O := by
    rw [hO, preimage_basicOpen_morphismOfGeneratingSections' ψ hs]
    exact hWle
  set θ : Away (𝒢 k V) f →+* Γ(X, W) := (Proj.awayToSection (𝒢 k V) f ≫ φ.appLE O W hle).hom
    with hθ
  -- the `k`-algebra structure of the chart ring, through the structure morphism of `X`
  have heW : W ≤ (X ↘ Spec (.of k)) ⁻¹ᵁ ⊤ := le_top
  letI : Algebra k Γ(X, W) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appLE ⊤ W heW).hom.toAlgebra
  have heO : O ≤ q ⁻¹ᵁ ⊤ := le_top
  have hstr : (X ↘ Spec (.of k)).appLE ⊤ W heW =
      q.appLE ⊤ O heO ≫ φ.appLE O W hle := by
    rw [Scheme.Hom.appLE_comp_appLE]
    have key : ∀ (g : X ⟶ Spec (.of k)) (_ : φ ≫ q = g) (e₁ : W ≤ g ⁻¹ᵁ ⊤)
        (e₂ : W ≤ (φ ≫ q) ⁻¹ᵁ ⊤), g.appLE ⊤ W e₁ = (φ ≫ q).appLE ⊤ W e₂ := by
      rintro g rfl e₁ e₂; rfl
    exact key _ hφq _ _
  have hθk : ∀ c : k, θ (algebraMap k (Away (𝒢 k V) f) c) = algebraMap k Γ(X, W) c := by
    intro c
    change _ = ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appLE ⊤ W heW) c
    rw [hstr, appLE_projectiveSpaceOfModuleToSpec_basicOpen hf heO]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rfl
  let θₐ : Away (𝒢 k V) f →ₐ[k] Γ(X, W) := { θ with commutes' := hθk }
  haveI : Algebra.FiniteType k Γ(X, W) := by
    have h1 := HasRingHomProperty.appLE (P := @LocallyOfFiniteType) (X ↘ Spec (.of k))
      inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨W, hWaff⟩ heW
    have h2 : (Scheme.ΓSpecIso (.of k)).inv.hom.FiniteType :=
      RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2
    exact h1.comp h2
  haveI : IsDomain Γ(X, W) := IsIntegral.component_integral W
  -- the divisors of the system, read on the chart
  have hdiv : ∀ (v : V) (hv : SymmetricAlgebra.ι k V v ∈ 𝒢 k V (1 • 1)) (x : X), x ∈ W →
      (x ∈ (systemFamily (k := k) s).divisorSet v ↔
        x ∉ X.basicOpen (θ (Away.mk (𝒢 k V) hf 1 (SymmetricAlgebra.ι k V v) hv))) := by
    intro v hv x hx
    have hv1 : SymmetricAlgebra.ι k V v ∈ 𝒢 k V 1 := (degreeOneElement k V v).2
    have hmk : Away.mk (𝒢 k V) hf 1 (SymmetricAlgebra.ι k V v) hv =
        Away.isLocalizationElem hf hv1 := by
      apply val_injective
      simp [Away.val_mk]
    have hbo : X.basicOpen (θ (Away.mk (𝒢 k V) hf 1 (SymmetricAlgebra.ι k V v) hv)) =
        W ⊓ nonvanishingOpen X L (ψ v) := by
      rw [hmk]
      change X.basicOpen ((φ.appLE O W hle).hom
        ((Proj.awayToSection (𝒢 k V) f).hom (Away.isLocalizationElem hf hv1))) = _
      rw [Scheme.basicOpen_appLE, basicOpen_awayToSection_isLocalizationElem (𝒢 k V) hf hv1
        Nat.one_pos Nat.one_pos]
      have hpre := preimage_basicOpen_morphismOfGeneratingSections' ψ hs v
      apply le_antisymm
      · rintro y ⟨hyW, hy⟩
        refine ⟨hyW, ?_⟩
        rw [← hpre]
        exact hy.2
      · rintro y ⟨hyW, hy⟩
        refine ⟨hyW, hle hyW, ?_⟩
        rwa [← hpre] at hy
    rw [hbo]
    exact ⟨fun hxD hxB =>
      (systemFamily (k := k) s).notMem_divisorSet_of_mem_nonvanishingOpen v hxB.2 hxD,
      fun hxB => of_not_not fun hxD =>
        hxB ⟨hx, mem_nonvanishingOpen_of_notMem_supportSet_zeroScheme L (ψ v) x hxD⟩⟩
  -- the degree-one fractions and the ratios they give on the chart
  have ht : ∀ j, SymmetricAlgebra.ι k V (e j) ∈ 𝒢 k V (1 • 1) := fun j => by
    simpa using (degreeOneElement k V (e j)).2
  set t : Fin (N + 1) → Away (𝒢 k V) f := fun j =>
    Away.mk (𝒢 k V) hf 1 (SymmetricAlgebra.ι k V (e j)) (ht j) with htdef
  set r : Fin (N + 1) → Γ(X, W) := fun j => θ (t j) with hrdef
  -- the image of the generic point and its residue field
  set y := φ ξ with hydef
  have hy : y ∈ O := hle hξW
  letI : Algebra k ((projectiveSpaceOfModule k V).residueField y) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ q.appTop ≫
      (projectiveSpaceOfModule k V).Γevaluation y).hom.toAlgebra
  letI : Algebra k (X.residueField ξ) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop ≫ X.Γevaluation ξ).hom.toAlgebra
  haveI : LocallyOfFiniteType q := locallyOfFiniteType_projectiveSpaceOfModuleToSpec (k := k)
    (V := V) (Pi.basisFun k (Fin (N + 1)))
  have htr : (2 : Cardinal) ≤
      Cardinal.lift.{0} (Algebra.trdeg k ((projectiveSpaceOfModule k V).residueField y)) := by
    have hrange : Set.range φ ⊆ closure {y} := by
      rintro _ ⟨x, rfl⟩
      have hξx : ξ ⤳ x := (genericPoint_spec X).specializes (Set.mem_univ x)
      exact specializes_iff_mem_closure.mp (hξx.map φ.continuous)
    have h1 := (Topology.IsEmbedding.inclusion hrange).isInducing.topologicalKrullDim_le
    have h2 := topologicalKrullDim_closure_singleton_eq_trdeg k (projectiveSpaceOfModule k V) q y
    rw [h2] at h1
    have h4 : ((2 : ℕ) : ℕ∞) ≤
        Cardinal.toENat (Algebra.trdeg k ((projectiveSpaceOfModule k V).residueField y)) :=
      WithBot.coe_le_coe.mp (hdim.trans h1)
    rw [Cardinal.natCast_le_toENat] at h4
    simpa using h4
  -- the residue field map at the generic point, a `k`-embedding
  let ιₐ : (projectiveSpaceOfModule k V).residueField y →ₐ[k] X.residueField ξ :=
    { (φ.residueFieldMap ξ).hom with
      commutes' := fun c => by
        change (φ.residueFieldMap ξ) (((projectiveSpaceOfModule k V).Γevaluation y)
            (q.appTop ((Scheme.ΓSpecIso (.of k)).inv c))) =
          (X.Γevaluation ξ) ((X ↘ Spec (.of k)).appTop ((Scheme.ΓSpecIso (.of k)).inv c))
        rw [← hφq, Scheme.Hom.comp_appTop]
        have h := Scheme.evaluation_naturality φ (V := ⊤) ξ trivial
        exact congrArg (fun g => g.hom (q.appTop ((Scheme.ΓSpecIso (.of k)).inv c))) h }
  -- evaluation of the chart ring at the generic point, a `k`-algebra map
  let evW : Γ(X, W) →ₐ[k] X.residueField ξ :=
    { (X.evaluation W ξ hξW).hom with
      commutes' := fun c => by
        change (X.evaluation W ξ hξW) (((X ↘ Spec (.of k)).appLE ⊤ W heW)
            ((Scheme.ΓSpecIso (.of k)).inv c)) =
          (X.Γevaluation ξ) ((X ↘ Spec (.of k)).appTop ((Scheme.ΓSpecIso (.of k)).inv c))
        have h := evaluation_appLE (X ↘ Spec (.of k)) ⊤ W heW ξ hξW
        exact congrArg (fun g => g.hom ((Scheme.ΓSpecIso (.of k)).inv c)) h }
  -- the chart ring of `ℙ(V)` evaluated at `y`
  haveI := isIso_awayToSection hf
  let ε : Away (𝒢 k V) f →+* (projectiveSpaceOfModule k V).residueField y :=
    (Proj.awayToSection (𝒢 k V) f ≫ (projectiveSpaceOfModule k V).evaluation O y hy).hom
  have hε : ∀ z, ∃ a b, z = ε a / ε b := by
    intro z
    obtain ⟨a, b, hab⟩ := exists_eq_evaluation_div
      (Proj.isAffineOpen_basicOpen (𝒢 k V) f hf Nat.one_pos) hy z
    obtain ⟨a', rfl⟩ := (ConcreteCategory.bijective_of_isIso (Proj.awayToSection (𝒢 k V) f)).2 a
    obtain ⟨b', rfl⟩ := (ConcreteCategory.bijective_of_isIso (Proj.awayToSection (𝒢 k V) f)).2 b
    exact ⟨a', b', hab⟩
  have hιε : ∀ a, ιₐ (ε a) = evW (θ a) := by
    intro a
    have h1 := Scheme.evaluation_naturality φ (V := O) ξ hy
    have h2 := evaluation_appLE φ O W hle ξ hξW
    exact congrArg (fun g => g.hom ((Proj.awayToSection (𝒢 k V) f) a)) (h1.trans h2.symm)
  have hR : ∀ a, ιₐ (ε a) ∈ Algebra.adjoin k (Set.range (evW ∘ r)) := by
    intro a
    have ha := away_mem_adjoin_range (Pi.basisFun k (Fin (N + 1))) (e i₀) a
    have hrange : (Set.range fun j => Away.mk (𝒢 k V) (degreeOneElement k V (e i₀)).2 1
        (SymmetricAlgebra.ι k V (Pi.basisFun k (Fin (N + 1)) j))
        (by simpa using (degreeOneElement k V (Pi.basisFun k (Fin (N + 1)) j)).2)) =
        Set.range t := by
      have hmkc : ∀ (x z : SymmetricAlgebra k V) (hx : x ∈ 𝒢 k V (1 • 1))
          (hz : z ∈ 𝒢 k V (1 • 1)), x = z →
          Away.mk (𝒢 k V) hf 1 x hx = Away.mk (𝒢 k V) hf 1 z hz := by
        rintro x _ hx hz rfl; rfl
      congr 1
      funext j
      exact hmkc _ _ _ _ (by simp [e])
    rw [hrange] at ha
    have hθa : θₐ a ∈ Algebra.adjoin k (Set.range r) := by
      have : θₐ a ∈ (Algebra.adjoin k (Set.range t)).map θₐ := Subalgebra.mem_map.mpr ⟨a, ha, rfl⟩
      rwa [← Algebra.adjoin_image, ← Set.range_comp] at this
    rw [hιε]
    have : evW (θₐ a) ∈ (Algebra.adjoin k (Set.range r)).map evW :=
      Subalgebra.mem_map.mpr ⟨θₐ a, hθa, rfl⟩
    rwa [← Algebra.adjoin_image, ← Set.range_comp] at this
  obtain ⟨i, j, hij, hind'⟩ := exists_ne_algebraicIndependent_of_two_le_trdeg ιₐ ε hε
    (evW ∘ r) hR htr
  have hind : AlgebraicIndependent k ![r i, r j] := by
    refine AlgebraicIndependent.of_comp evW ?_
    convert hind' using 1 <;> first | rfl | (funext l; fin_cases l <;> rfl)
  obtain ⟨c, d, hne, h2⟩ := exists_forall_mem_minimalPrimes_height_eq_two hind
  -- the fractions of the vectors `e l - c' • e i₀` are the ratios minus constants
  have hmk2 : ∀ (l : Fin (N + 1)) (c' : k)
      (h : SymmetricAlgebra.ι k V (e l - c' • e i₀) ∈ 𝒢 k V (1 • 1)),
      θ (Away.mk (𝒢 k V) hf 1 (SymmetricAlgebra.ι k V (e l - c' • e i₀)) h) =
        r l - algebraMap k Γ(X, W) c' := by
    intro l c' h
    have hval : Away.mk (𝒢 k V) hf 1 (SymmetricAlgebra.ι k V (e l - c' • e i₀)) h =
        t l - algebraMap k (Away (𝒢 k V) f) c' := by
      apply val_injective
      rw [HomogeneousLocalization.val_sub, Away.val_mk, Away.val_mk,
        HomogeneousLocalization.val_algebraMap, Localization.mk_eq_mk', eq_comm,
        IsLocalization.eq_mk'_iff_mul_eq, sub_mul, IsLocalization.mk'_spec]
      simp only [pow_one]
      rw [map_sub (SymmetricAlgebra.ι k V), map_smul (SymmetricAlgebra.ι k V),
        Algebra.smul_def (A := SymmetricAlgebra k V), map_sub, map_mul,
        ← IsScalarTower.algebraMap_apply]
    rw [hval, map_sub, hθk]
  have hdivW : ∀ (l : Fin (N + 1)) (c' : k) (x : X), x ∈ W →
      (x ∈ (systemFamily (k := k) s).divisorSet (e l - c' • e i₀) ↔
        x ∉ X.basicOpen (r l - algebraMap k Γ(X, W) c')) := by
    intro l c' x hx
    have h := hdiv (e l - c' • e i₀)
      (by rw [smul_eq_mul, mul_one]; exact (degreeOneElement k V (e l - c' • e i₀)).2) x hx
    rwa [hmk2] at h
  have hWa : IsAffineOpen W := hWaff
  have hCI : ∀ p : PrimeSpectrum Γ(X, W), hWa.fromSpec p ∈
      (systemFamily (k := k) s).divisorSet (e i - c • e i₀) ∩
        (systemFamily (k := k) s).divisorSet (e j - d • e i₀) ↔
      ((Ideal.span {r i - algebraMap k Γ(X, W) c, r j - algebraMap k Γ(X, W) d} :
        Ideal Γ(X, W)) : Set Γ(X, W)) ⊆ p.asIdeal := by
    intro p
    have hpW : hWa.fromSpec p ∈ W := by
      have : hWa.fromSpec p ∈ Set.range hWa.fromSpec := ⟨p, rfl⟩
      rwa [hWa.range_fromSpec] at this
    have hb : ∀ g : Γ(X, W), hWa.fromSpec p ∈ X.basicOpen g ↔ g ∉ p.asIdeal := by
      intro g
      have := congrArg (fun U : (Spec Γ(X, W)).Opens => p ∈ U) (hWa.fromSpec_preimage_basicOpen g)
      exact this.to_iff
    have key : ((Ideal.span {r i - algebraMap k Γ(X, W) c, r j - algebraMap k Γ(X, W) d} :
        Ideal Γ(X, W)) : Set Γ(X, W)) ⊆ p.asIdeal ↔
        r i - algebraMap k Γ(X, W) c ∈ p.asIdeal ∧ r j - algebraMap k Γ(X, W) d ∈ p.asIdeal := by
      rw [SetLike.coe_subset_coe, Ideal.span_le, Set.insert_subset_iff,
        Set.singleton_subset_iff]
      rfl
    have e1 := ((hdivW i c _ hpW).trans (not_congr (hb _))).trans not_not
    have e2 := ((hdivW j d _ hpW).trans (not_congr (hb _))).trans not_not
    exact ⟨fun h => key.mpr ⟨e1.mp h.1, e2.mp h.2⟩,
      fun h => ⟨e1.mpr (key.mp h).1, e2.mpr (key.mp h).2⟩⟩
  obtain ⟨Z, hZ1, hZ2, hZ3⟩ := exists_maximal_codimension_eq_two hWa
    (((systemFamily (k := k) s).isClosed_divisorSet _).inter
      ((systemFamily (k := k) s).isClosed_divisorSet _)) hCI
    (fun x hx => (systemFamily (k := k) s).notMem_divisorSet_of_mem_nonvanishingOpen (e i₀)
      (hWle hx)) hne h2
  exact ⟨e i₀, e i - c • e i₀, e j - d • e i₀, Z, hZ1, hZ2, hZ3⟩

end Key

variable {k : Type u} [Field k] {N : ℕ} {X : Scheme.{u}} [X.Over (Spec (.of k))]
  {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L]

/-- **Bertini's irreducibility theorem for a free system in characteristic zero.** Let `X` be a
variety over an algebraically closed field `k` of characteristic zero, and `s₀, …, s_N` global
sections of an invertible sheaf `L` generating it, so that they define the morphism
`φ = morphismOfGeneratingSections … : X ⟶ ℙ(V^*)`. If the image of `φ` has dimension at least
two, there is a dense open `U` of the coefficient space `𝔸ᴺ⁺¹_k`, and a dense open `U'` of
`ℙᴺ_k`, such that for every coefficient vector `c` with `c ∈ U` (resp. `c ≠ 0` and `[c] ∈ U'`)
the zero scheme of `∑ᵢ cᵢ sᵢ` is geometrically integral over `k`, and in particular integral. -/
@[mmp "lem_mmp_foundation_free_system_irreducible_bertini"]
public theorem exists_dense_open_geometricallyIntegral_zeroScheme [IsAlgClosed k] [CharZero k]
    [IsVariety k (X ↘ Spec (.of k))]
    (s : Fin (N + 1) → Γ(L, ⊤))
    (hs : ⨆ c : Fin (N + 1) → k, nonvanishingOpen X L (systemSection s c) = ⊤)
    (hdim : 2 ≤ topologicalKrullDim
      (Set.range (morphismOfGeneratingSections k (Fin (N + 1) → k) L (systemSection s) hs))) :
    (∃ U : (coefficientSpace k N).Opens, Dense (U : Set (coefficientSpace k N)) ∧
      ∀ c : Fin (N + 1) → k, coefficientPoint c ∈ U →
        GeometricallyIntegral ((zeroScheme X L (systemSection s c)).subschemeι ≫
          X ↘ Spec (.of k)) ∧
        IsIntegral (zeroScheme X L (systemSection s c)).subscheme) ∧
    (∃ U : (AlgebraicGeometry.Proj
        (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)).Opens,
      Dense (U : Set (AlgebraicGeometry.Proj
        (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))) ∧
      ∀ (c : Fin (N + 1) → k) (hc : c ≠ 0), dualPoint c hc ∈ U →
        GeometricallyIntegral ((zeroScheme X L (systemSection s c)).subschemeι ≫
          X ↘ Spec (.of k)) ∧
        IsIntegral (zeroScheme X L (systemSection s c)).subscheme) := by
  classical
  set D := systemFamily (k := k) s
  obtain ⟨v₁, v₂, v₃, Z, hZ, hZ1, hZ2⟩ := exists_component_codimension_two s hs hdim
  have hcommon : D.commonZeroSet = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun x hx => ?_
    have hx' : x ∈ ⨆ c : Fin (N + 1) → k, nonvanishingOpen X L (systemSection s c) := by
      rw [hs]; trivial
    obtain ⟨c, hc⟩ := TopologicalSpace.Opens.mem_iSup.mp hx'
    exact D.notMem_divisorSet_of_mem_nonvanishingOpen c hc (D.commonZeroSet_subset_divisorSet c hx)
  let h : D.Hypotheses :=
    { locallyOfFiniteType := (inferInstance : LocallyOfFiniteType (X ↘ Spec (.of k)))
      quasiCompact := (inferInstance : QuasiCompact (X ↘ Spec (.of k)))
      geometricallyIrreducible :=
        geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed k X (X ↘ Spec (.of k))
      v₁ := v₁
      v₂ := v₂
      v₃ := v₃
      Z := Z
      Z_component := hZ
      Z_not_subset := hZ1
      Z_codimension := hZ2
      commonZeroSet_codimension := fun Y hY => by
        obtain ⟨y, hy⟩ := Y.isIrreducible.nonempty
        have := hY hy
        rw [hcommon] at this
        exact absurd this (Set.notMem_empty y) }
  obtain ⟨U, hUne, hU⟩ := h.forGeneral_geometricallyIrreducible
  obtain ⟨P, hP0, hP⟩ := exists_polynomial_parameterPoint_mem (D := D) U hUne
  obtain ⟨Q, hQ0, hQ⟩ := exists_polynomial_isReduced_zeroScheme (k := k) s hs
  let σ : D.basisIndex ≃ Fin (N + 1) :=
    Equiv.ulift.trans (finCongr (Module.finrank_fin_fun k))
  set P' : MvPolynomial (Fin (N + 1)) k := MvPolynomial.rename σ P
  have hT0 : P' * Q ≠ 0 := mul_ne_zero (fun h0 => hP0 (MvPolynomial.rename_injective _ σ.injective
    (h0.trans (map_zero _).symm))) hQ0
  refine exists_dense_opens_of_polynomial (fun c => GeometricallyIntegral
      ((zeroScheme X L (systemSection s c)).subschemeι ≫ X ↘ Spec (.of k)) ∧
      IsIntegral (zeroScheme X L (systemSection s c)).subscheme)
    (fun c t ht hc => by rwa [zeroScheme_systemSection_smul s c ht] at hc) _ hT0
    (fun c hc => ?_)
  rw [map_mul] at hc
  have hPc : MvPolynomial.eval (c ∘ σ) P ≠ 0 := by
    have h1 : MvPolynomial.eval c P' = MvPolynomial.eval (c ∘ σ) P := MvPolynomial.eval_rename _ _ _
    rw [← h1]
    exact left_ne_zero_of_mul hc
  haveI hred : IsReduced (zeroScheme X L (systemSection s c)).subscheme :=
    hQ c (right_ne_zero_of_mul hc)
  let a : Fin (Module.finrank D.k D.V) → D.k := fun i => (c ∘ σ) (ULift.up i)
  have hgi := hU D.k a (hP (c ∘ σ) hPc) a rfl
  have hgi' := geometricallyIrreducible_zeroScheme_of_specializedDivisor a hgi
  have hsum : (∑ i, a i • D.basis i) = (c : D.V) := sum_smul_reindex_basisFun c
  rw [hsum] at hgi'
  haveI : GeometricallyIrreducible
      ((zeroScheme X L (systemSection s c)).subschemeι ≫ X ↘ Spec (.of k)) := hgi'
  haveI : GeometricallyReduced
      ((zeroScheme X L (systemSection s c)).subschemeι ≫ X ↘ Spec (.of k)) :=
    geometricallyReduced_of_isReduced _
  refine ⟨GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible _, ?_⟩
  haveI : IrreducibleSpace (zeroScheme X L (systemSection s c)).subscheme :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton
      (f := (zeroScheme X L (systemSection s c)).subschemeι ≫ X ↘ Spec (.of k))
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end MMP.Threefold.Bridges
