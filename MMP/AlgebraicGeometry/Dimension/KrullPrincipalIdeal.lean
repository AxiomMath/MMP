module

public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.AlgebraicGeometry.AffineScheme
public import MMP.AlgebraicGeometry.Variety.Subvariety

/-!
# Krull's principal ideal theorem on a variety (Fulton, §2.1)

Let `X` be an `n`-dimensional variety over a field `K`, `U ⊆ X` an affine open subset with
coordinate ring `A = A(U)`, and `a ∈ A` a non-zero element. Then every irreducible component of the
closed subset `V(a) ⊆ U` has dimension `n - 1`. (If `a` is a unit, `V(a)` is empty and there is
nothing to prove.)

Through `Spec A ≅ U`, the irreducible components of `V(a)` are the closed subsets `V(p)` for the
minimal primes `p` of `aA`, and `V(p)` has dimension `dim A ⧸ p`, the coheight of `p` in
`Spec A`. By Krull's principal ideal theorem `p` has height at most `1`, and at least `1` since
`a ≠ 0` and `A` is a domain. Since `A` is a finitely generated domain over `K`, every prime `p`
satisfies `height p + coheight p = dim A`, and `dim A = dim U = dim X = n`. Hence
`dim V(p) = n - 1`.

## Main results

* `MMP.hasDim_of_maximal_isIrreducible_zeroLocus`: every maximal irreducible
  subset of `V(a) ∩ U` has dimension `n - 1`.

## Implementation notes

The closed subset `V(a) ⊆ U` is `X.zeroLocus {a} ∩ U` (Mathlib's `Scheme.zeroLocus` of a section
over `U` contains the complement of `U`), and an irreducible component of it is a subset of `X`
maximal among the irreducible subsets of `X.zeroLocus {a} ∩ U`. The theorem is stated for an
integral scheme locally of finite type over `K`, which every variety is; quasi-compactness of `X`
and the hypothesis that `a` is not a unit are not needed.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §2.1 and Appendix B.1.
* [R. Hartshorne, *Algebraic Geometry*], Proposition I.7.1 and Theorem I.1.11A.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Order Topology

universe u

namespace MMP

open MMP.Intersection MMP.Intersection.Scheme

namespace KrullPrincipalIdeal

/-- In a Noetherian domain, a minimal prime `p` of a principal ideal `aA` with `a ≠ 0` has height
one (in the order of `Spec A`). -/
theorem height_eq_one {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] {a : A}
    (ha : a ≠ 0) (p : PrimeSpectrum A) (hp : p.asIdeal ∈ (Ideal.span {a}).minimalPrimes) :
    height p = 1 := by
  refine le_antisymm ?_ ?_
  · rw [← PrimeSpectrum.height_eq_orderHeight]
    exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hp
  · rw [ENat.one_le_iff_ne_zero, Ne, height_eq_zero]
    refine fun hmin ↦ hmin.not_lt (lt_of_le_of_ne
      (PrimeSpectrum.asIdeal_le_asIdeal ⟨⊥, Ideal.isPrime_bot⟩ _ |>.mp bot_le) ?_)
    rintro rfl
    exact ha (by simpa using hp.1.2 (Ideal.mem_span_singleton_self a))

/-- For a prime `p` of a ring `A`, the closed subset `V(p)` of `Spec A` has dimension
`coheight p`, i.e. `dim A ⧸ p`. -/
theorem topologicalKrullDim_zeroLocus_eq_coheight {A : Type*} [CommRing A]
    (p : PrimeSpectrum A) :
    topologicalKrullDim (PrimeSpectrum.zeroLocus (p.asIdeal : Set A)) = coheight p := by
  have hI : PrimeSpectrum.zeroLocus (p.asIdeal : Set A) = Set.Ici p := by
    ext x
    simp only [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, Set.mem_Ici]
    exact (PrimeSpectrum.asIdeal_le_asIdeal p x).symm
  rw [topologicalKrullDim_zeroLocus, ringKrullDim_quotient, hI, coheight_eq_krullDim_Ici]

/-- The coordinate ring of a nonempty affine open `U` of an integral scheme `X` locally of finite
type over a field has the same dimension as `X`. -/
theorem ringKrullDim_eq_topologicalKrullDim (K : Type u) [Field K] {X : Scheme.{u}}
    [X.Over (Spec (.of K))] [IsIntegral X] [LocallyOfFiniteType (X ↘ Spec (.of K))]
    {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U] :
    ringKrullDim Γ(X, U) = topologicalKrullDim X := by
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace (X ↘ Spec (.of K))
  obtain ⟨w, hwU, hwc⟩ := nonempty_inter_closedPoints
    (show (U : Set X).Nonempty from ⟨_, (Classical.arbitrary U).2⟩) U.isOpen.isLocallyClosed
  have hw0 : height w = 0 := by
    rw [height_eq_zero]
    intro y hy
    rw [Scheme.le_iff_specializes] at hy ⊢
    obtain rfl : y = w := by
      simpa [(show IsClosed {w} from hwc).closure_eq] using specializes_iff_mem_closure.mp hy
    rfl
  have hX := height_add_coheight_eq_krullDim K w
  rw [hw0, zero_add, coheight_eq_ringKrullDim_of_isClosed K hU ⟨w, hwU⟩ hwc] at hX
  rw [hX, ← krullDim_eq_of_orderIso Subvariety.orderIsoPoints,
    ← dimension_eq_krullDim_subvariety]

/-- In a finitely generated domain `A` of dimension `m` over a field, a prime of height one has
coheight `c` with `1 + c = m`. -/
theorem exists_coheight_eq_of_height_eq_one (K : Type*) [Field K] {A : Type*} [CommRing A]
    [IsDomain A] [Algebra K A] [Algebra.FiniteType K A] {m : ℕ} (hdim : ringKrullDim A = m)
    {p : PrimeSpectrum A} (hp : height p = 1) : ∃ c : ℕ, coheight p = c ∧ 1 + c = m := by
  have hle := ringKrullDim_le_height_add_coheight K A p
  have hge := Order.height_add_coheight_le_krullDim p
  rw [hp] at hle hge
  have heq : ((1 + coheight p : ℕ∞) : WithBot ℕ∞) = m :=
    le_antisymm (hge.trans_eq hdim) (hdim ▸ hle)
  have heq' : 1 + coheight p = (m : ℕ∞) := by exact_mod_cast heq
  obtain ⟨c, hc⟩ : ∃ c : ℕ, coheight p = c := by
    refine ENat.ne_top_iff_exists.mp ?_ |>.imp fun c hc ↦ hc.symm
    intro htop
    rw [htop, add_top] at heq'
    exact ENat.coe_ne_top m heq'.symm
  rw [hc] at heq'
  exact ⟨c, hc, by exact_mod_cast heq'⟩

end KrullPrincipalIdeal

open KrullPrincipalIdeal

/-- **Krull's principal ideal theorem** (Fulton, §2.1; Hartshorne I.7.1). Let `X` be an
`n`-dimensional integral scheme locally of finite type over a field `K` (for instance an
`n`-dimensional variety), `U ⊆ X` an affine open subset and `a ∈ A(U) = Γ(X, U)` a non-zero
element. Then every irreducible component `Z` of the closed subset `V(a) ⊆ U` (a maximal
irreducible subset of `X.zeroLocus {a} ∩ U`) has dimension `n - 1`. -/
theorem hasDim_of_maximal_isIrreducible_zeroLocus (K : Type u) [Field K] {X : Scheme.{u}}
    [X.Over (Spec (.of K))] [IsIntegral X] [LocallyOfFiniteType (X ↘ Spec (.of K))] {n : ℤ}
    (hn : MMP.Intersection.HasDim X n) {U : X.Opens} (hU : IsAffineOpen U) {a : Γ(X, U)}
    (ha : a ≠ 0) {Z : Set X}
    (hZ : Maximal (fun Z : Set X ↦ IsIrreducible Z ∧ Z ⊆ X.zeroLocus {a} ∩ U) Z) :
    MMP.Intersection.HasDim Z (n - 1) := by
  obtain ⟨m, rfl, hm⟩ := hn
  have hZU : Z ⊆ (U : Set X) := fun z hz ↦ (hZ.1.2 hz).2
  haveI : Nonempty U := by
    obtain ⟨z, hz⟩ := hZ.1.1.nonempty
    exact ⟨⟨z, hZU hz⟩⟩
  obtain ⟨φ, hφ⟩ := exists_ringHom_finiteType_of_isAffineOpen (K := K) hU
  letI := φ.toAlgebra
  haveI : Algebra.FiniteType K Γ(X, U) := hφ
  haveI := Algebra.FiniteType.isNoetherianRing K Γ(X, U)
  obtain ⟨g, hg⟩ : ∃ g : PrimeSpectrum Γ(X, U) → X, g = hU.fromSpec := ⟨_, rfl⟩
  have hfe : IsOpenEmbedding g := hg ▸ hU.fromSpec.isOpenEmbedding
  have hrange : Set.range g = U := hg ▸ hU.range_fromSpec
  have himage : ∀ s : Set Γ(X, U), g '' PrimeSpectrum.zeroLocus s = X.zeroLocus s ∩ U :=
    hg ▸ hU.fromSpec_image_zeroLocus
  have hpre : ∀ s : Set Γ(X, U), g ⁻¹' X.zeroLocus s = PrimeSpectrum.zeroLocus s :=
    hg ▸ hU.fromSpec_preimage_zeroLocus
  have hS : ∀ q : PrimeSpectrum Γ(X, U), a ∈ q.asIdeal →
      IsIrreducible (g '' PrimeSpectrum.zeroLocus (q.asIdeal : Set Γ(X, U))) ∧
        g '' PrimeSpectrum.zeroLocus (q.asIdeal : Set Γ(X, U)) ⊆ X.zeroLocus {a} ∩ U := by
    intro q haq
    refine ⟨?_, ?_⟩
    · refine IsIrreducible.image ?_ _ hfe.continuous.continuousOn
      exact (PrimeSpectrum.isIrreducible_zeroLocus_iff _).mpr
        (by rw [q.isPrime.radical]; exact q.isPrime)
    · rw [← himage]
      refine Set.image_mono (PrimeSpectrum.zeroLocus_anti_mono ?_)
      simpa using haq
  set Z' : Set (PrimeSpectrum Γ(X, U)) := g ⁻¹' Z with hZ'
  have hZf : g '' Z' = Z := Set.image_preimage_eq_of_subset (by rw [hrange]; exact hZU)
  have hZ'irr : IsIrreducible Z' := by
    refine ⟨?_, hZ.1.1.2.preimage hfe⟩
    obtain ⟨z, hz⟩ := hZ.1.1.nonempty
    obtain ⟨y, hy⟩ : z ∈ Set.range g := by rw [hrange]; exact hZU hz
    exact ⟨y, by rw [hZ', Set.mem_preimage, hy]; exact hz⟩
  have hmax : ∀ q : PrimeSpectrum Γ(X, U), a ∈ q.asIdeal →
      Z ⊆ g '' PrimeSpectrum.zeroLocus (q.asIdeal : Set Γ(X, U)) →
        PrimeSpectrum.zeroLocus (q.asIdeal : Set Γ(X, U)) ⊆ Z' :=
    fun q haq hsub x hx ↦ hZ.2 (hS q haq) hsub ⟨x, hx, rfl⟩
  let p : PrimeSpectrum Γ(X, U) :=
    ⟨_, PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime.mp hZ'irr⟩
  have hap : a ∈ p.asIdeal := by
    rw [PrimeSpectrum.mem_vanishingIdeal]
    intro x hx
    have : g x ∈ X.zeroLocus {a} := (hZ.1.2 hx).1
    rw [← Set.mem_preimage, hpre] at this
    simpa using this
  have hZp : PrimeSpectrum.zeroLocus (p.asIdeal : Set Γ(X, U)) = Z' :=
    le_antisymm
      (hmax p hap (hZf ▸ Set.image_mono (PrimeSpectrum.subset_zeroLocus_vanishingIdeal Z')))
      (PrimeSpectrum.subset_zeroLocus_vanishingIdeal Z')
  have hpmin : p.asIdeal ∈ (Ideal.span {a}).minimalPrimes := by
    refine ⟨⟨p.isPrime, (Ideal.span_singleton_le_iff_mem _).mpr hap⟩, ?_⟩
    rintro q ⟨hq, haq⟩ hqp
    have h1 : PrimeSpectrum.zeroLocus (q : Set Γ(X, U)) ⊆
        PrimeSpectrum.zeroLocus (p.asIdeal : Set Γ(X, U)) := by
      rw [hZp]
      refine hmax ⟨q, hq⟩ ((Ideal.span_singleton_le_iff_mem _).mp haq) ?_
      rw [← hZf, ← hZp]
      exact Set.image_mono (PrimeSpectrum.zeroLocus_anti_mono hqp)
    have := (PrimeSpectrum.zeroLocus_subset_zeroLocus_iff _ _).mp h1
    rwa [hq.radical] at this
  obtain ⟨c, hc, hcm⟩ := exists_coheight_eq_of_height_eq_one K
    ((ringKrullDim_eq_topologicalKrullDim K hU).trans hm) (height_eq_one ha p hpmin)
  refine ⟨c, by omega, ?_⟩
  have hdim := (hfe.isEmbedding.homeomorphImage
    (PrimeSpectrum.zeroLocus (p.asIdeal : Set Γ(X, U)))).isHomeomorph.topologicalKrullDim_eq
  rw [← hZf, ← hZp]
  refine hdim.symm.trans ?_
  rw [topologicalKrullDim_zeroLocus_eq_coheight, hc]
  rfl

end MMP
