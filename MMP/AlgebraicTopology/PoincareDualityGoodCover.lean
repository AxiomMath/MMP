module

public import MMP.AlgebraicTopology.OrientationClass.Point
public import MMP.AlgebraicTopology.SingularCohomology.Relative.Excision
public import MMP.AlgebraicTopology.CapProduct.Cup
public import MMP.AlgebraicTopology.PoincareDuality.AlexanderOpen
import MMP.AlgebraicGeometry.Resolution.ZariskiSequence
public import MMP.AlgebraicGeometry.Singularities.Surface.LogDiscrepancyVector
public import MMP.AlgebraicGeometry.Positivity.VeryAmpleMultiple
public import StacksFrontier.AlgebraicGeometry.AffineStageDescent.ProperSmoothModel
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentThree.DerivedChowFourierMukai

/-!
# Three foundational results: Poincaré duality, Zariski sequences, descent of polarized varieties

This file collects three independent results used in the foundations.

**Poincaré duality for a manifold with a finite good cover.** Let `M` be a real `n`-manifold,
oriented by a fundamental class `μ ∈ H^BM_n(M; ℚ)`, with a finite open cover in which every
nonempty finite intersection is homeomorphic to `ℝⁿ`. Compactly supported cohomology is the
direct limit `H^i_c(M; ℚ) = colim_K H^i(M, M - K; ℚ)` over the compact `K ⊆ M`. The orientation
trace `τ_K : H^n(M, M - K; ℚ) → ℚ` evaluates a relative cocycle on a locally finite cycle
representing `μ`; it takes the value `1` on the local orientation class at every point. For
`i + j = n` the pairing `(a, β) ↦ τ_K (a ∪ β)` is perfect: `H^j(M; ℚ)` is finite dimensional
and `H^i_c(M; ℚ) → H^j(M; ℚ)^*` is injective and surjective.

**Generically chosen smooth-centre blow-ups reach a divisor.** Let `Y₀` be a smooth variety over
a field `k` and `ν` a divisor of `k(Y₀)` with nonempty center. Inductively let `Zᵣ` be the
center of `ν` on `Yᵣ`, choose an open `Uᵣ ⊆ Yᵣ` containing the generic point of `Zᵣ` with
`Zᵣ ∩ Uᵣ` smooth, and let `Yᵣ₊₁ = Bl_{Zᵣ ∩ Uᵣ} Uᵣ`. Then `ν` has nonempty center on every `Yᵣ`
and, whatever the choices, some center has codimension one.

**A polarized smooth projective variety descends to a finitely generated field.** Let `k` be
algebraically closed of characteristic zero, `X` smooth projective integral over `k` and `L`
ample on `X`. Then `(X, L)` is the base change of a smooth projective geometrically integral
polarized scheme `(X_F, L_F)` over a subfield `F ⊆ k` finitely generated over `ℚ`.

## Main results

* `MMP.Analytic.exists_trace_cup_perfect_of_finite_good_cover`: the orientation trace exists,
  and the cup product pairing is perfect.
* `MMP.Flips.hasNonemptyCenter_and_exists_coheight_eq_one_of_blowUp`: in every such sequence of
  blow-ups `ν` has nonempty center on every `Yᵣ`, and some center has codimension one.
* `MMP.Descent.exists_fg_intermediateField_isoBaseChange_of_isAmple`: the descent.

## Implementation notes

*Duality.* The manifold is a Hausdorff charted space over a real normed space `H` with a basis
`b` of `n` vectors, oriented by `MMP.IsFundamentalClass ℚ b μ`. Compactly
supported cohomology appears through the groups `H^i(M, M - K)`, `K` compact, and the maps that
enlarge the support: perfectness says that a class pairing to zero with all of `H^j(M)` vanishes
at a larger support, and that every functional on `H^j(M)` is a trace pairing. The proof goes
through the adjunction `τ_K (a ∪ β) = ⟨a, β ∩ z⟩` and Poincaré duality `H^j(M) ≅ H^{BM}_i(M)`
on `M` and on every open subset, which reduce the statement to the perfectness of the
evaluation pairing between compactly supported cohomology and Borel–Moore homology; the good
cover enters only through the finite dimensionality of `H^j(M; ℚ)`, by Mayer–Vietoris.

*Blow-ups.* The valuation `ν` on `Yᵣ` is a valuation `νᵣ` of `k(Yᵣ)`, determined by
`νᵣ₊₁ ∘ βᵣ^* = νᵣ`. The center `Zᵣ` is the center of any proper divisor over `Yᵣ` whose
valuation is `νᵣ`. The sequence is indexed by all `r : ℕ`; the source stops at the first
divisorial center, and continuing is harmless since blowing up a smooth divisor in a smooth
variety is an isomorphism. The proof is Zariski's: the local rings of the centers increase to
the valuation ring of `ν`, and a transcendence degree count makes one of them one-dimensional.

*Descent.* `F` is an `IntermediateField ℚ k` with `IntermediateField.FG`; base change is the
fibre product `pullback (X_F ↘ Spec F) (Spec.map (algebraMap F k))`, with an isomorphism to `X`
over `Spec k` and an isomorphism of sheaves along `X ≅ X_F ×_F k ⟶ X_F`. `Spec k` is the limit
of the spectra of the finitely generated subrings `ℤ[s] ⊆ k`; a proper flat polarized model
over one stage is smooth at a later stage, and its base change to `ℚ(s)` is the model.

## References

* [A. Hatcher, *Algebraic Topology*][hatcher2002], §3.3, Theorem 3.35.
* [R. Bott, L. Tu, *Differential Forms in Algebraic Topology*][botttu1982], §5.
* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], §2
* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Lemma 2.45
* [EGA IV, 8.9, 8.10, 17.7.8]
* [Stacks Project, Tags 01ZM, 0C0C, 0D43, 01VT]
-/

/-! ### Poincaré duality for a manifold with a finite good cover -/

@[expose] public noncomputable section

open CategoryTheory Set Topology Opposite Simplicial MMP
  MMP.SingularChain MMP.SingularCochain
  MMP.FundamentalClass MMP.LocallyFiniteChain TopologicalSpace
  MMP.borelMooreHomology MMP.ThomClass MMP.PoincareAlexander

namespace MMP.Analytic

section Pairing

variable {R : Type} [CommRing R] {X : TopCat.{0}}

/-- A cochain vanishing on the simplices avoiding `K` is nonzero only on simplices meeting `K`. -/
private lemma mem_image_of_ne_zero {n : ℕ} {K : Set X} {φ : Simplex X n → R}
    (hφ : φ ∈ vanishing R n Kᶜ) {τ : (TopCat.toSSet.obj X).obj (op ⦋n⦌)}
    (h : φ (SingularCochain.simplexEquiv X _ τ) ≠ 0) : (singularSimplexImage X τ ∩ K).Nonempty := by
  by_contra hK
  exact h (hφ _ fun y hy hyK ↦ hK ⟨y, (range_simplexEquiv _).subset hy, hyK⟩)

/-- Pairing a locally finite chain with a cochain vanishing off a compact set has finite support. -/
private lemma finite_support_mul {n : ℕ} {c : (TopCat.toSSet.obj X).obj (op ⦋n⦌) → R}
    (hc : IsLocallyFiniteSet (singularSimplexImage X) (Function.support c)) {K : Set X}
    (hK : IsCompact K) {φ : Simplex X n → R} (hφ : φ ∈ vanishing R n Kᶜ) :
    (Function.support fun σ ↦ c σ * φ (SingularCochain.simplexEquiv X _ σ)).Finite := by
  refine (hc.finite_inter_compact hK).subset fun σ hσ ↦ ?_
  have h1 : c σ ≠ 0 := fun h ↦ hσ (by simp [h])
  have h2 : φ (SingularCochain.simplexEquiv X _ σ) ≠ 0 := fun h ↦ hσ (by simp [h])
  exact ⟨h1, mem_image_of_ne_zero hφ h2⟩

/-- `⟨ψ, ∂ w⟩ = ⟨δ ψ, w⟩` for a locally finite chain `w` and a cochain `ψ` vanishing on the
simplices avoiding a compact set. -/
private lemma localPairing_d {n : ℕ}
    (w : (borelMooreChainComplex R (ModuleCat.of R R) X).X (n + 1)) {K : Set X}
    (hK : IsCompact K) {φ : Simplex X n → R} (hφv : φ ∈ vanishing R n Kᶜ) :
    localPairing ((((borelMooreChainComplex R (ModuleCat.of R R) X).d (n + 1) n).hom w).1
      : (TopCat.toSSet.obj X).obj (op ⦋n⦌) → R) φ =
    localPairing (w.1 : (TopCat.toSSet.obj X).obj (op ⦋n + 1⦌) → R) (coboundary R n φ) := by
  classical
  rw [borelMooreChainComplex_d_apply R (ModuleCat.of R R) X n w]
  set c : (TopCat.toSSet.obj X).obj (op ⦋n + 1⦌) → R := w.1
  have hc : IsLocallyFiniteSet (singularSimplexImage X) (Function.support c) := w.2
  let F := (hc.finite_inter_compact hK).toFinset
  have hF : ∀ ω, c ω ≠ 0 → (singularSimplexImage X ω ∩ K).Nonempty → ω ∈ F := fun ω h1 h2 ↦
    (Finite.mem_toFinset _).2 ⟨h1, h2⟩
  let T := F.biUnion fun ω ↦ Finset.univ.image fun i : Fin (n + 2) ↦
    (TopCat.toSSet.obj X).δ i ω
  have hface : ∀ (i : Fin (n + 2)) (ω : (TopCat.toSSet.obj X).obj (op ⦋n + 1⦌)),
      singularSimplexImage X ((TopCat.toSSet.obj X).δ i ω) ⊆ singularSimplexImage X ω :=
    fun i ω ↦ by
      rintro _ ⟨t, rfl⟩
      exact ⟨_, rfl⟩
  have hterm : ∀ τ, dFun (fun i : Fin (n + 2) ↦ (TopCat.toSSet.obj X).δ i) c τ *
      φ (SingularCochain.simplexEquiv X _ τ) = ∑ i : Fin (n + 2), ∑ ω ∈ F,
        (-1 : R) ^ (i : ℕ) * ((if (TopCat.toSSet.obj X).δ i ω = τ then c ω else 0) *
          φ (SingularCochain.simplexEquiv X _ τ)) := by
    intro τ
    by_cases h : φ (SingularCochain.simplexEquiv X _ τ) = 0
    · simp [h]
    rw [dFun, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [pushforwardFun_apply_eq_sum _ c τ F (fun ω h1 (h2 : (TopCat.toSSet.obj X).δ i ω = τ) ↦
      hF ω h1 ((mem_image_of_ne_zero hφv h).mono
        (inter_subset_inter_left _ (hface i ω |>.trans' (by rw [h2]))))),
      Finset.smul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun ω _ ↦ ?_
    rw [zsmul_eq_mul]
    push_cast
    ring
  rw [localPairing, finsum_eq_sum_of_support_subset (s := T) _ (fun τ hτ ↦ by
    rw [Function.mem_support, hterm] at hτ
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hτ
    obtain ⟨ω, hω, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi
    have hδ : (TopCat.toSSet.obj X).δ i ω = τ := by
      by_contra h
      simp [h] at hi
    rw [Finset.coe_biUnion]
    exact mem_iUnion₂.2 ⟨ω, hω, by simp [← hδ]⟩)]
  simp_rw [hterm]
  rw [Finset.sum_comm]
  have hinner : ∀ i : Fin (n + 2), ∑ τ ∈ T, ∑ ω ∈ F, (-1 : R) ^ (i : ℕ) *
      ((if (TopCat.toSSet.obj X).δ i ω = τ then c ω else 0) * φ (SingularCochain.simplexEquiv X _ τ)) =
      ∑ ω ∈ F, c ω * ((-1 : R) ^ (i : ℕ) *
        φ ((SingularCochain.simplexEquiv X _ ω : Simplex X (n + 1)).comp (face n i))) := by
    intro i
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ω hω ↦ ?_
    have hmem : (TopCat.toSSet.obj X).δ i ω ∈ T :=
      Finset.mem_biUnion.2 ⟨ω, hω, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
    simp_rw [ite_mul, zero_mul, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq, ite_eq_left hmem, ← toSSetObjEquiv_δ]
    ring
  rw [Finset.sum_congr rfl fun i _ ↦ hinner i, Finset.sum_comm]
  rw [localPairing, finsum_eq_sum_of_support_subset (s := F) _ (fun ω hω ↦ ?_)]
  · refine Finset.sum_congr rfl fun ω _ ↦ ?_
    rw [← Finset.mul_sum, coboundary_apply]
  · rw [Function.mem_support] at hω
    have h1 : c ω ≠ 0 := fun h ↦ hω (by simp [h])
    have h2 : coboundary R n φ (SingularCochain.simplexEquiv X _ ω) ≠ 0 := fun h ↦ hω (by simp [h])
    exact Finset.mem_coe.2 (hF ω h1 (mem_image_of_ne_zero (coboundary_mem_vanishing hφv) h2))

/-- The pairing of a locally finite chain with a cochain vanishing on the simplices avoiding a
compact set is additive in the chain. -/
private lemma localPairing_add_left {n : ℕ} {c d : (TopCat.toSSet.obj X).obj (op ⦋n⦌) → R}
    (hc : IsLocallyFiniteSet (singularSimplexImage X) (Function.support c))
    (hd : IsLocallyFiniteSet (singularSimplexImage X) (Function.support d)) {K : Set X}
    (hK : IsCompact K) {φ : Simplex X n → R} (hφ : φ ∈ vanishing R n Kᶜ) :
    localPairing (c + d) φ = localPairing c φ + localPairing d φ := by
  rw [localPairing, localPairing, localPairing, ← finsum_add_distrib (finite_support_mul hc hK hφ)
    (finite_support_mul hd hK hφ)]
  exact finsum_congr fun σ ↦ by simp [add_mul]

private lemma localPairing_add_right {n : ℕ} {c : (TopCat.toSSet.obj X).obj (op ⦋n⦌) → R}
    (hc : IsLocallyFiniteSet (singularSimplexImage X) (Function.support c)) {K : Set X}
    (hK : IsCompact K) {φ ψ : Simplex X n → R} (hφ : φ ∈ vanishing R n Kᶜ)
    (hψ : ψ ∈ vanishing R n Kᶜ) :
    localPairing c (φ + ψ) = localPairing c φ + localPairing c ψ := by
  rw [localPairing, localPairing, localPairing, ← finsum_add_distrib (finite_support_mul hc hK hφ)
    (finite_support_mul hc hK hψ)]
  exact finsum_congr fun σ ↦ by simp [mul_add]

private lemma localPairing_smul_left {n : ℕ} {c : (TopCat.toSSet.obj X).obj (op ⦋n⦌) → R}
    (hc : IsLocallyFiniteSet (singularSimplexImage X) (Function.support c)) {K : Set X}
    (hK : IsCompact K) {φ : Simplex X n → R} (hφ : φ ∈ vanishing R n Kᶜ) (r : R) :
    localPairing (r • c) φ = r * localPairing c φ := by
  rw [localPairing, localPairing, mul_finsum' _ _ (finite_support_mul hc hK hφ)]
  exact finsum_congr fun σ ↦ by simp [mul_assoc]

private lemma localPairing_smul_right {n : ℕ} {c : (TopCat.toSSet.obj X).obj (op ⦋n⦌) → R}
    (hc : IsLocallyFiniteSet (singularSimplexImage X) (Function.support c)) {K : Set X}
    (hK : IsCompact K) {φ : Simplex X n → R} (hφ : φ ∈ vanishing R n Kᶜ) (r : R) :
    localPairing c (r • φ) = r * localPairing c φ := by
  rw [localPairing, localPairing, mul_finsum' _ _ (finite_support_mul hc hK hφ)]
  exact finsum_congr fun σ ↦ by simp only [Pi.smul_apply, smul_eq_mul]; ring

private lemma localPairing_zero_right {n : ℕ} (c : (TopCat.toSSet.obj X).obj (op ⦋n⦌) → R) :
    localPairing c (0 : Simplex X n → R) = 0 :=
  finsum_eq_zero_of_forall_eq_zero fun σ ↦ by simp

/-- The pairing with a cochain vanishing on the simplices avoiding a compact set, as a linear map
on locally finite chains. -/
private def chainPairing {n : ℕ} {K : Set X} (hK : IsCompact K) {φ : Simplex X n → R}
    (hφ : φ ∈ vanishing R n Kᶜ) :
    (borelMooreChainComplex R (ModuleCat.of R R) X).X n →ₗ[R] R where
  toFun c := localPairing (c.1 : (TopCat.toSSet.obj X).obj (op ⦋n⦌) → R) φ
  map_add' c d := localPairing_add_left c.2 d.2 hK hφ
  map_smul' r c := localPairing_smul_left c.2 hK hφ r

/-- The pairing of a cycle with a relative cocycle of `(X, X - K)` depends only on its homology
class. -/
private lemma localPairing_eq_of_homologyπ_eq {n : ℕ}
    {z z' : (borelMooreChainComplex R (ModuleCat.of R R) X).cycles n}
    (h : (borelMooreChainComplex R (ModuleCat.of R R) X).homologyπ n z =
      (borelMooreChainComplex R (ModuleCat.of R R) X).homologyπ n z') {K : Set X}
    (hK : IsCompact K) {φ : Simplex X n → R} (hφ : φ ∈ relCocycles R Kᶜ n) :
    localPairing (((borelMooreChainComplex R (ModuleCat.of R R) X).iCycles n z).1 :
      (TopCat.toSSet.obj X).obj (op ⦋n⦌) → R) φ =
    localPairing (((borelMooreChainComplex R (ModuleCat.of R R) X).iCycles n z').1 :
      (TopCat.toSSet.obj X).obj (op ⦋n⦌) → R) φ := by
  let P : (borelMooreChainComplex R (ModuleCat.of R R) X).cycles n ⟶ ModuleCat.of R R :=
    ModuleCat.ofHom ((chainPairing hK hφ.1).comp
      ((borelMooreChainComplex R (ModuleCat.of R R) X).iCycles n).hom)
  have hP : (borelMooreChainComplex R (ModuleCat.of R R) X).toCycles (n + 1) n ≫ P = 0 := by
    refine ModuleCat.hom_ext (LinearMap.ext fun w ↦ ?_)
    have e : (borelMooreChainComplex R (ModuleCat.of R R) X).iCycles n
        ((borelMooreChainComplex R (ModuleCat.of R R) X).toCycles (n + 1) n w) =
        (borelMooreChainComplex R (ModuleCat.of R R) X).d (n + 1) n w :=
      ConcreteCategory.congr_hom
        ((borelMooreChainComplex R (ModuleCat.of R R) X).toCycles_i (n + 1) n) w
    change localPairing (((borelMooreChainComplex R (ModuleCat.of R R) X).iCycles n
      ((borelMooreChainComplex R (ModuleCat.of R R) X).toCycles (n + 1) n w)).1 :
        (TopCat.toSSet.obj X).obj (op ⦋n⦌) → R) φ = 0
    rw [e, localPairing_d w hK hφ.1, show coboundary R n φ = 0 from hφ.2]
    exact localPairing_zero_right _
  obtain ⟨l, hl⟩ := Limits.CokernelCofork.IsColimit.desc'
    ((borelMooreChainComplex R (ModuleCat.of R R) X).homologyIsCokernel (n + 1) n (by simp)) P hP
  have e : ∀ a, (chainPairing hK hφ.1).comp
      ((borelMooreChainComplex R (ModuleCat.of R R) X).iCycles n).hom a =
      l ((borelMooreChainComplex R (ModuleCat.of R R) X).homologyπ n a) := fun a ↦
    (ConcreteCategory.congr_hom hl a).symm
  change (chainPairing hK hφ.1).comp
      ((borelMooreChainComplex R (ModuleCat.of R R) X).iCycles n).hom z =
    (chainPairing hK hφ.1).comp ((borelMooreChainComplex R (ModuleCat.of R R) X).iCycles n).hom z'
  rw [e, e, h]

/-- The `d` out of a cycle vanishes. -/
private lemma d_iCycles {n j : ℕ} (z : (borelMooreChainComplex R (ModuleCat.of R R) X).cycles n) :
    ((borelMooreChainComplex R (ModuleCat.of R R) X).d n j).hom
      ((borelMooreChainComplex R (ModuleCat.of R R) X).iCycles n z) = 0 :=
  congrArg (fun f ↦ ModuleCat.Hom.hom f z)
    (HomologicalComplex.iCycles_d (borelMooreChainComplex R (ModuleCat.of R R) X) n j)

/-- The pairing of a cycle with a relative coboundary of `(X, X - K)` vanishes. -/
private lemma localPairing_eq_zero_of_mem_relCoboundaries {n : ℕ}
    (z : (borelMooreChainComplex R (ModuleCat.of R R) X).cycles n) {K : Set X}
    (hK : IsCompact K) {φ : Simplex X n → R} (hφ : φ ∈ relCoboundaries R Kᶜ n) :
    localPairing (((borelMooreChainComplex R (ModuleCat.of R R) X).iCycles n z).1 :
      (TopCat.toSSet.obj X).obj (op ⦋n⦌) → R) φ = 0 := by
  cases n with
  | zero =>
    rw [show φ = 0 from hφ]
    exact localPairing_zero_right _
  | succ k =>
    obtain ⟨ψ, hψ, rfl⟩ := hφ
    rw [← localPairing_d _ hK hψ, d_iCycles]
    exact finsum_eq_zero_of_forall_eq_zero fun σ ↦ zero_mul _

/-- Pairing a cycle with `ρ^* χ`, `ρ` the small-chains map of `{X - K, B}`, is pairing it with
`χ`, for a cocycle `χ` vanishing on the simplices avoiding the compact set `K`. -/
private lemma localPairing_pullback_smallChainMap {m : ℕ}
    (z : (borelMooreChainComplex R (ModuleCat.of R R) X).cycles m) {K : Set X} (hK : IsCompact K)
    (B : Set X) {χ : Simplex X m → R} (hχ : χ ∈ vanishing R m Kᶜ)
    (hδ : coboundary R m χ = 0) :
    localPairing (((borelMooreChainComplex R (ModuleCat.of R R) X).iCycles m z).1 :
        (TopCat.toSSet.obj X).obj (op ⦋m⦌) → R) (pullback (smallChainMap R {Kᶜ, B} m) χ) =
      localPairing (((borelMooreChainComplex R (ModuleCat.of R R) X).iCycles m z).1 :
        (TopCat.toSSet.obj X).obj (op ⦋m⦌) → R) χ := by
  have hd := pullback_smallChainMap_sub_mem_pairCoboundaries (R := R) Kᶜ B hδ
  cases m with
  | zero =>
    rw [show pullback (smallChainMap R {Kᶜ, B} 0) χ = χ from
      sub_eq_zero.1 ((Submodule.mem_bot R).1 hd)]
  | succ k =>
    obtain ⟨η, ⟨hηK, -⟩, hη⟩ := hd
    rw [show pullback (smallChainMap R {Kᶜ, B} (k + 1)) χ = χ + coboundary R k η by
      rw [hη]; abel, localPairing_add_right ((borelMooreChainComplex R (ModuleCat.of R R)
        X).iCycles (k + 1) z).2 hK hχ (coboundary_mem_vanishing hηK),
      ← localPairing_d _ hK hηK, d_iCycles]
    convert add_zero _
    exact finsum_eq_zero_of_forall_eq_zero fun σ ↦ zero_mul _

/-- Pairing with a cycle, as a linear map on the relative cohomology `H^n(X, X - K)`. -/
private def tracePairing {n : ℕ} (z : (borelMooreChainComplex R (ModuleCat.of R R) X).cycles n)
    {K : Set X} (hK : IsCompact K) : relCohomology R Kᶜ n →ₗ[R] R :=
  Submodule.liftQ _
    { toFun := fun φ ↦ localPairing (((borelMooreChainComplex R (ModuleCat.of R R) X).iCycles n
          z).1 : (TopCat.toSSet.obj X).obj (op ⦋n⦌) → R) φ.1
      map_add' := fun φ ψ ↦ localPairing_add_right (((borelMooreChainComplex R (ModuleCat.of R R)
          X).iCycles n z).2) hK φ.2.1 ψ.2.1
      map_smul' := fun r φ ↦ localPairing_smul_right (((borelMooreChainComplex R
          (ModuleCat.of R R) X).iCycles n z).2) hK φ.2.1 r }
    (fun _ hφ ↦ localPairing_eq_zero_of_mem_relCoboundaries z hK hφ)

/-- Pairing a push-forward along a map of vertices with a cochain vanishing on the simplices
avoiding a compact set is pairing the chain with the pulled back cochain. -/
private lemma localPairing_pf {a b : ℕ} (f : Fin (a + 1) → Fin (b + 1))
    (c : (BorelMooreCross.BM R X).X b) {K : Set X} (hK : IsCompact K) {φ : Simplex X a → R}
    (hφ : φ ∈ vanishing R a Kᶜ) :
    localPairing (BorelMooreCross.coeff R (BorelMooreCap.pf R f c)) φ =
      localPairing (BorelMooreCross.coeff R c) (fun σ : Simplex X b ↦ φ (σ.comp (smap f))) := by
  classical
  set d := BorelMooreCross.coeff R c
  have hd : IsLocallyFiniteSet (singularSimplexImage X) (Function.support d) :=
    BorelMooreCross.coeff_mem R c
  let F := (hd.finite_inter_compact hK).toFinset
  have hF : ∀ σ, d σ ≠ 0 → (singularSimplexImage X σ ∩ K).Nonempty → σ ∈ F := fun σ h1 h2 ↦
    (Finite.mem_toFinset _).2 ⟨h1, h2⟩
  have hop : ∀ σ, SingularCochain.simplexEquiv X _ (BorelMooreCap.opS f σ) =
      (SingularCochain.simplexEquiv X _ σ : Simplex X b).comp (smap f) := fun σ ↦
    BorelMooreCap.simplexEquiv_opS f σ
  have himg : ∀ σ, singularSimplexImage X (BorelMooreCap.opS f σ) ⊆ singularSimplexImage X σ :=
    BorelMooreCap.image_opS_subset f
  have hterm : ∀ τ, BorelMooreCross.coeff R (BorelMooreCap.pf R f c) τ * φ (SingularCochain.simplexEquiv X _ τ) =
      ∑ σ ∈ F, (if BorelMooreCap.opS f σ = τ then d σ else 0) * φ (SingularCochain.simplexEquiv X _ τ) := by
    intro τ
    by_cases h : φ (SingularCochain.simplexEquiv X _ τ) = 0
    · simp [h]
    rw [BorelMooreCap.coeff_pf, pushforwardFun_apply_eq_sum _ d τ F (fun σ h1 h2 ↦ hF σ h1
      ((mem_image_of_ne_zero hφ h).mono (inter_subset_inter_left _ (h2 ▸ himg σ)))),
      Finset.sum_mul]
  rw [localPairing, finsum_eq_sum_of_support_subset (s := F.image (BorelMooreCap.opS f)) _
    (fun τ hτ ↦ by
      rw [Function.mem_support, hterm] at hτ
      obtain ⟨σ, hσ, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hτ
      have hδ : BorelMooreCap.opS f σ = τ := by
        by_contra h
        simp [h] at hi
      exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨σ, hσ, hδ⟩))]
  simp_rw [hterm]
  rw [Finset.sum_comm]
  rw [localPairing, finsum_eq_sum_of_support_subset (s := F) _ (fun σ hσ ↦ ?_)]
  · refine Finset.sum_congr rfl fun σ hσ ↦ ?_
    simp_rw [ite_mul, zero_mul]
    rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_image_of_mem _ hσ), hop]
  · rw [Function.mem_support] at hσ
    have h1 : d σ ≠ 0 := fun h ↦ hσ (by simp [h])
    have h2 : φ ((SingularCochain.simplexEquiv X _ σ : Simplex X b).comp (smap f)) ≠ 0 := fun h ↦
      hσ (by simp [h])
    rw [← hop] at h2
    exact Finset.mem_coe.2 (hF σ h1 ((mem_image_of_ne_zero hφ h2).mono
      (inter_subset_inter_left _ (himg σ))))

/-- **The cap/cup adjunction on chains**: `⟨a, β ∩ c⟩ = ⟨a ∪ β, c⟩` for a cochain `a` vanishing
on the simplices avoiding a compact set. -/
private lemma localPairing_capChain {i j n : ℕ} (h : j + i = n) (h' : i + j = n)
    (β : Simplex X j → R) (c : (BorelMooreCross.BM R X).X n) {K : Set X} (hK : IsCompact K)
    {a : Simplex X i → R} (ha : a ∈ vanishing R i Kᶜ) :
    localPairing (BorelMooreCross.coeff R (BorelMooreCap.capChain R j i n h β c)) a =
      localPairing (BorelMooreCross.coeff R c) (cup i j n h' a β) := by
  rw [BorelMooreCap.capChain_apply, localPairing_pf _ _ hK ha, localPairing, localPairing]
  refine finsum_congr fun σ ↦ ?_
  rw [BorelMooreCap.coeff_W, cup_apply]
  change (BorelMooreCap.wt β _ σ * _) * _ = _ * (_ * β _)
  simp only [BorelMooreCap.wt]
  rw [show simplexEquiv X n σ = SingularCochain.simplexEquiv X _ σ from rfl]
  ring

end Pairing

section Trace

variable {M : Type} [TopologicalSpace M] {n : ℕ}

/-- A locally finite cycle representing a Borel–Moore class. -/
private lemma exists_cycle (μ : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of M) n) :
    ∃ z : (borelMooreChainComplex ℚ (ModuleCat.of ℚ ℚ) (TopCat.of M)).cycles n,
      (borelMooreChainComplex ℚ (ModuleCat.of ℚ ℚ) (TopCat.of M)).homologyπ n z =
        (borelMooreHomologyIsoOfNat ℚ (ModuleCat.of ℚ ℚ) (TopCat.of M) n).hom μ :=
  (ModuleCat.epi_iff_surjective _).1 inferInstance _

/-- The trace `τ_K : H^n(M, M - K) → ℚ` of a Borel–Moore class: evaluation on a representing
locally finite cycle. -/
private def trace (μ : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of M) n)
    (K : Compacts M) :
    cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) (TopCat.of M) (K : Set M) n →ₗ[ℚ] ℚ :=
  (tracePairing (X := TopCat.of M) (exists_cycle μ).choose K.isCompact).comp
    (relativeSingularCohomologyEquiv ℚ ((K : Set M)ᶜ : Set (TopCat.of M)) n).toLinearMap

private lemma trace_mk (μ : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of M) n)
    (K : Compacts M) (φ : relCocycles ℚ ((K : Set M)ᶜ : Set (TopCat.of M)) n)
    (z : (borelMooreChainComplex ℚ (ModuleCat.of ℚ ℚ) (TopCat.of M)).cycles n)
    (hz : (borelMooreChainComplex ℚ (ModuleCat.of ℚ ℚ) (TopCat.of M)).homologyπ n z =
      (borelMooreHomologyIsoOfNat ℚ (ModuleCat.of ℚ ℚ) (TopCat.of M) n).hom μ) :
    trace μ K ((relativeSingularCohomologyEquiv ℚ ((K : Set M)ᶜ : Set (TopCat.of M)) n).symm
        (Submodule.Quotient.mk φ)) =
      localPairing (((borelMooreChainComplex ℚ (ModuleCat.of ℚ ℚ) (TopCat.of M)).iCycles n z).1)
        (φ : Simplex (TopCat.of M) n → ℚ) := by
  simp only [trace, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.apply_symm_apply]
  exact localPairing_eq_of_homologyπ_eq ((exists_cycle μ).choose_spec.trans hz.symm)
    K.isCompact φ.2

/-- The trace of a class transported along an equality of subsets. -/
private lemma trace_congrIndex_mk (μ : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of M) n)
    (K : Compacts M) {S : Set (TopCat.of M)} (hS : S = ((K : Set M)ᶜ : Set (TopCat.of M)))
    (χ : relCocycles ℚ S n)
    (z : (borelMooreChainComplex ℚ (ModuleCat.of ℚ ℚ) (TopCat.of M)).cycles n)
    (hz : (borelMooreChainComplex ℚ (ModuleCat.of ℚ ℚ) (TopCat.of M)).homologyπ n z =
      (borelMooreHomologyIsoOfNat ℚ (ModuleCat.of ℚ ℚ) (TopCat.of M) n).hom μ) :
    trace μ K (cohomologyWithSupports.congrIndex ℚ (TopCat.of M) hS rfl
        ((relativeSingularCohomologyEquiv ℚ S n).symm (Submodule.Quotient.mk χ))) =
      localPairing (((borelMooreChainComplex ℚ (ModuleCat.of ℚ ℚ) (TopCat.of M)).iCycles n z).1)
        (χ : Simplex (TopCat.of M) n → ℚ) := by
  subst hS
  exact trace_mk μ K χ z hz

/-- **The trace of a cup product** is the pairing of a representing cycle with the cup product
of representing cocycles. -/
private lemma trace_cup [T2Space M] (μ : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of M) n)
    (K : Compacts M) (p q : ℕ) (hij : (p : ℤ) + (q : ℤ) = (n : ℤ))
    (φ : relCocycles ℚ ((K : Set M)ᶜ : Set (TopCat.of M)) p)
    (ψ : relCocycles ℚ (Set.univᶜ : Set (TopCat.of M)) q)
    (z : (borelMooreChainComplex ℚ (ModuleCat.of ℚ ℚ) (TopCat.of M)).cycles n)
    (hz : (borelMooreChainComplex ℚ (ModuleCat.of ℚ ℚ) (TopCat.of M)).homologyπ n z =
      (borelMooreHomologyIsoOfNat ℚ (ModuleCat.of ℚ ℚ) (TopCat.of M) n).hom μ) :
    trace μ K (cohomologyWithSupports.congrIndex ℚ (TopCat.of M) (by rw [Set.inter_univ]) hij
      (cohomologyWithSupports.cup ℚ (TopCat.of M) K.isCompact.isClosed isClosed_univ p q
        ((relativeSingularCohomologyEquiv ℚ _ p).symm (Submodule.Quotient.mk φ))
        ((relativeSingularCohomologyEquiv ℚ _ q).symm (Submodule.Quotient.mk ψ)))) =
      localPairing (((borelMooreChainComplex ℚ (ModuleCat.of ℚ ℚ) (TopCat.of M)).iCycles n z).1)
        (cup p q n (by omega) φ.1 ψ.1) := by
  have hn : p + q = n := by exact_mod_cast hij
  subst hn
  rw [cohomologyWithSupports.cup_natCast, cohomologyWithSupports.congrIndex_congrIndex]
  simp only [LinearEquiv.apply_symm_apply, relCup_mk]
  rw [trace_congrIndex_mk μ K _ _ z hz]
  exact localPairing_pullback_smallChainMap (X := TopCat.of M) z K.isCompact
    (Set.univᶜ : Set (TopCat.of M))
    (cup_mem_vanishing rfl φ.2.1 ψ.2.1).1 (coboundary_cup_eq_zero p q _ rfl φ.2.2 ψ.2.2)

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [T2Space M] [ChartedSpace H M]

/-- The trace of the local orientation class at a point is `1`. -/
private lemma trace_chartOriented (b : Module.Basis (Fin n) ℝ H)
    {μ : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of M) n}
    (hμ : IsFundamentalClass ℚ b μ) (y : M) (α : Simplex (TopCat.of M) n → ℚ)
    (hα : IsChartOrientedCocycle ℚ b (y : TopCat.of M) α) :
    trace μ ⟨{y}, isCompact_singleton⟩
        ((relativeSingularCohomologyEquiv ℚ (({y} : Set M)ᶜ : Set (TopCat.of M)) n).symm
          (Submodule.Quotient.mk ⟨α, hα.1⟩)) = 1 := by
  obtain ⟨z, hz⟩ := exists_cycle μ
  refine (trace_mk μ ⟨{y}, isCompact_singleton⟩ ⟨α, hα.1⟩ z hz).trans ?_
  set e := chartAt H y
  have hy : y ∈ e.source := mem_chart_source H y
  obtain ⟨v, hv, hvt⟩ := exists_isOrientedSimplexAroundZero_subset b (e y)
    (e.open_target.mem_nhds (e.map_source hy))
  have hloc : IsLocallyClassOf ℚ μ y
      (inclChainSimplex (chartOpens e) (chartSimplex e v hvt)) :=
    IsLocallyClassOf.of_restrict (chartOpens e) (x := ⟨y, hy⟩)
      (hμ e (chart_mem_atlas H y) ⟨y, hy⟩ v hv hvt)
  rw [hloc z hz α hα.1]
  have h1 := hα.2 e (chart_mem_atlas H y) hy v hv hvt
  rwa [SingularCochain.eval, Finsupp.linearCombination_single, one_smul] at h1

end Trace

section FiniteDimensional

/-- Finite dimensionality of cohomology passes to a retract. -/
private lemma finiteDimensional_of_comp_eq_id {Z Z' : TopCat.{0}} (f : Z ⟶ Z') (g : Z' ⟶ Z)
    (hfg : f ≫ g = 𝟙 Z) (p : ℕ)
    [FiniteDimensional ℚ (relCohomology ℚ (∅ : Set Z') p)] :
    FiniteDimensional ℚ (relCohomology ℚ (∅ : Set Z) p) := by
  have hs : Function.Surjective (relCohomologyMap ℚ f (A := (∅ : Set Z')) (A' := (∅ : Set Z))
      (empty_subset _) p) := by
    intro c
    obtain ⟨φ, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    refine ⟨Submodule.Quotient.mk (pullCoc ℚ g φ), ?_⟩
    rw [relCohomologyMap_mk]
    exact congrArg Submodule.Quotient.mk
      (Subtype.ext (cochainPullback_cochainPullback_of_comp_eq_id f g hfg φ.1))
  exact Module.Finite.of_surjective _ hs

/-- The cohomology of the empty space vanishes. -/
private lemma finiteDimensional_of_isEmpty (Z : TopCat.{0}) [IsEmpty Z] (p : ℕ) :
    FiniteDimensional ℚ (relCohomology ℚ (∅ : Set Z) p) := by
  have : IsEmpty (Simplex Z p) := ⟨fun σ ↦ IsEmpty.false (σ (stdSimplex.vertex 0))⟩
  infer_instance

/-- The cohomology of a contractible space is finite dimensional. -/
private lemma finiteDimensional_of_homotopy_const {Z : TopCat.{0}} (z₀ : Z)
    (H : TopCat.Homotopy (𝟙 Z) (TopCat.ofHom (ContinuousMap.const Z z₀))) (p : ℕ) :
    FiniteDimensional ℚ (relCohomology ℚ (∅ : Set Z) p) := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · set x : relCohomology ℚ (∅ : Set Z) 0 :=
      Submodule.Quotient.mk ⟨constCochain 0 1, constCochain_zero_mem_relCocycles 1⟩
    refine Module.Finite.of_surjective (LinearMap.toSpanSingleton ℚ _ x) fun c ↦ ?_
    obtain ⟨φ, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    refine ⟨φ.1 (ContinuousMap.const _ z₀), ?_⟩
    rw [LinearMap.toSpanSingleton_apply, ← Submodule.Quotient.mk_smul]
    refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
    rw [constCochain_eq_of_mem_relCocycles_zero z₀ H φ]
    funext σ
    simp [constCochain]
  · have : Subsingleton (relCohomology ℚ (∅ : Set Z) p) := ⟨fun a b ↦ by
      obtain ⟨φ, rfl⟩ := Submodule.Quotient.mk_surjective _ a
      obtain ⟨ψ, rfl⟩ := Submodule.Quotient.mk_surjective _ b
      rw [mk_eq_zero_of_homotopy_const z₀ H hp φ, mk_eq_zero_of_homotopy_const z₀ H hp ψ]⟩
    infer_instance

/-- The straight-line contraction of `ℝⁿ`. -/
private def euclideanContraction (n : ℕ) :
    TopCat.Homotopy (𝟙 (TopCat.of (EuclideanSpace ℝ (Fin n))))
      (TopCat.ofHom (ContinuousMap.const (TopCat.of (EuclideanSpace ℝ (Fin n))) 0)) where
  toFun p := (1 - (p.1 : ℝ)) • p.2
  continuous_toFun := by fun_prop
  map_zero_left x := by simp
  map_one_left x := by simp

/-- A space homeomorphic to `ℝⁿ` has finite dimensional cohomology. -/
private lemma finiteDimensional_of_homeomorph_euclidean {Z : TopCat.{0}} {n : ℕ}
    (e : Z ≃ₜ EuclideanSpace ℝ (Fin n)) (p : ℕ) :
    FiniteDimensional ℚ (relCohomology ℚ (∅ : Set Z) p) := by
  have := finiteDimensional_of_homotopy_const _ (euclideanContraction n) p
  exact finiteDimensional_of_comp_eq_id (Z' := TopCat.of (EuclideanSpace ℝ (Fin n)))
    (TopCat.ofHom (e : C(Z, EuclideanSpace ℝ (Fin n))))
    (TopCat.ofHom (e.symm : C(EuclideanSpace ℝ (Fin n), Z)))
    (TopCat.ext fun x ↦ e.symm_apply_apply x) p

/-- A vector space is finite dimensional when the kernel and the range of a linear map out of
it are. -/
private lemma finiteDimensional_of_ker_range {V W : Type} [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W] (f : V →ₗ[ℚ] W) [FiniteDimensional ℚ (LinearMap.ker f)]
    [FiniteDimensional ℚ (LinearMap.range f)] : FiniteDimensional ℚ V := by
  have : FiniteDimensional ℚ (V ⧸ LinearMap.ker f) :=
    LinearEquiv.finiteDimensional f.quotKerEquivRange.symm
  exact Module.Finite.of_submodule_quotient (LinearMap.ker f)

/-- **Mayer–Vietoris step.** If `A`, `B` and `A ∩ B` have finite dimensional cohomology, so does
`A ∪ B`, for `A`, `B` open. -/
private lemma finiteDimensional_of_mayerVietoris {Y : TopCat.{0}} {A B : Set Y} (hA : IsOpen A)
    (hB : IsOpen B) (hAB : A ∪ B = univ)
    (hFA : ∀ p, FiniteDimensional ℚ (relCohomology ℚ (∅ : Set (TopCat.of A)) p))
    (hFB : ∀ p, FiniteDimensional ℚ (relCohomology ℚ (∅ : Set (TopCat.of B)) p))
    (hFI : ∀ p, FiniteDimensional ℚ (relCohomology ℚ (∅ : Set (TopCat.of (A ∩ B : Set Y))) p))
    (p : ℕ) : FiniteDimensional ℚ (relCohomology ℚ (∅ : Set Y) p) := by
  set r := (relCohomologyMap ℚ (SingularCochain.subsetInclusion A) (A := (∅ : Set Y))
      (A' := (∅ : Set (TopCat.of A))) (empty_subset _) p).prod
    (relCohomologyMap ℚ (SingularCochain.subsetInclusion B) (A := (∅ : Set Y))
      (A' := (∅ : Set (TopCat.of B))) (empty_subset _) p) with hr
  have := hFA p
  have := hFB p
  have hrA : ∀ φ : relCocycles ℚ (∅ : Set Y) p, (r (Submodule.Quotient.mk φ)).1 =
      Submodule.Quotient.mk (subCocycle ℚ A φ.1 (coboundary_mem_vanishing_of_cocycle A φ)) :=
    fun _ ↦ rfl
  have hrB : ∀ φ : relCocycles ℚ (∅ : Set Y) p, (r (Submodule.Quotient.mk φ)).2 =
      Submodule.Quotient.mk (subCocycle ℚ B φ.1 (coboundary_mem_vanishing_of_cocycle B φ)) :=
    fun _ ↦ rfl
  have : FiniteDimensional ℚ (LinearMap.ker r) := by
    cases p with
    | zero =>
      have : LinearMap.ker r = ⊥ := by
        refine (Submodule.eq_bot_iff _).2 fun x hx ↦ ?_
        obtain ⟨φ, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        have h0 : r (Submodule.Quotient.mk φ) = 0 := hx
        have hφ := eq_zero_of_mk_subCocycle_eq_zero hA hB hAB φ
          ((hrA φ).symm.trans (congrArg Prod.fst h0)) ((hrB φ).symm.trans (congrArg Prod.snd h0))
        rw [hφ]
        rfl
      rw [this]
      infer_instance
    | succ k =>
      set W : Submodule ℚ (Simplex Y k → ℚ) :=
        (vanishing ℚ (k + 1) (A ∩ B)).comap (coboundary ℚ k)
      let Φ : W →ₗ[ℚ] relCohomology ℚ (∅ : Set Y) (k + 1) :=
        (Submodule.mkQ _).comp (LinearMap.codRestrict (relCocycles ℚ (∅ : Set Y) (k + 1))
          ((mvCoboundary ℚ A B k).comp W.subtype)
          fun e ↦ (ofCocycle (mvCoboundary ℚ A B k e.1) (coboundary_mvCoboundary hA hB hAB e.2)).2)
      let Ψ : W →ₗ[ℚ] relCohomology ℚ (∅ : Set (TopCat.of (A ∩ B : Set Y))) k :=
        (Submodule.mkQ _).comp (LinearMap.codRestrict
          (relCocycles ℚ (∅ : Set (TopCat.of (A ∩ B : Set Y))) k)
          ((cochainPullback ℚ (SingularCochain.subsetInclusion (A ∩ B)) k).comp W.subtype)
          fun e ↦ (subCocycle ℚ (A ∩ B) e.1 e.2).2)
      have hΦ : ∀ e : W, Φ e = Submodule.Quotient.mk (ofCocycle (mvCoboundary ℚ A B k e.1)
          (coboundary_mvCoboundary hA hB hAB e.2)) := fun _ ↦ rfl
      have hΨ : ∀ e : W, Ψ e = Submodule.Quotient.mk (subCocycle ℚ (A ∩ B) e.1 e.2) :=
        fun _ ↦ rfl
      have hker : LinearMap.ker Ψ ≤ LinearMap.ker Φ := by
        intro e he
        have he' : Ψ e = 0 := he
        change Φ e = 0
        rw [hΦ]
        rw [hΨ] at he'
        cases k with
        | zero =>
          have hv := (mk_subCocycle_eq_zero_iff_zero (A ∩ B) e.1 e.2).1 he'
          exact mk_mvCoboundary_eq_zero_of_sub_mem hA hB hAB e.2
            (a := 0) (b := 0) (by rw [map_zero]; exact Submodule.zero_mem _)
            (by rw [map_zero]; exact Submodule.zero_mem _) (by simpa using hv)
        | succ k =>
          obtain ⟨θ, hθ⟩ := (mk_subCocycle_eq_zero_iff_succ (A ∩ B) e.1 e.2).1 he'
          exact mk_mvCoboundary_eq_zero_succ hA hB hAB e.2
            (a := 0) (b := 0) (by rw [map_zero]; exact Submodule.zero_mem _)
            (by rw [map_zero]; exact Submodule.zero_mem _) θ (by simpa using hθ)
      have hrange : LinearMap.ker r ≤ LinearMap.range Φ := by
        intro x hx
        obtain ⟨φ, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        have h0 : r (Submodule.Quotient.mk φ) = 0 := hx
        obtain ⟨e, he, hφ⟩ := exists_mk_eq_mk_mvCoboundary hA hB hAB φ
          ((hrA φ).symm.trans (congrArg Prod.fst h0)) ((hrB φ).symm.trans (congrArg Prod.snd h0))
        exact ⟨⟨e, he⟩, (hΦ _).trans hφ.symm⟩
      have := hFI k
      have : FiniteDimensional ℚ (W ⧸ LinearMap.ker Ψ) :=
        LinearEquiv.finiteDimensional Ψ.quotKerEquivRange.symm
      have : FiniteDimensional ℚ (LinearMap.range Φ) := by
        rw [← Submodule.range_liftQ (LinearMap.ker Ψ) Φ hker]
        infer_instance
      exact Submodule.finiteDimensional_of_le hrange
  exact finiteDimensional_of_ker_range r

/-- Finite dimensionality of cohomology passes from a subset `S` of `Y` to its copy inside a
subspace `W ⊇ S`. -/
private lemma finiteDimensional_of_subset_val {Y : TopCat.{0}} {W S : Set Y} (hSW : S ⊆ W)
    (T : Set (TopCat.of W)) (hT : ∀ x : W, x ∈ T ↔ (x : Y) ∈ S) (p : ℕ)
    [FiniteDimensional ℚ (relCohomology ℚ (∅ : Set (TopCat.of S)) p)] :
    FiniteDimensional ℚ (relCohomology ℚ (∅ : Set (TopCat.of T)) p) :=
  finiteDimensional_of_comp_eq_id (Z' := TopCat.of S)
    (TopCat.ofHom ⟨fun x ↦ ⟨x.1.1, (hT x.1).1 x.2⟩, by fun_prop⟩)
    (TopCat.ofHom ⟨fun x ↦ ⟨⟨x.1, hSW x.2⟩, (hT _).2 x.2⟩, by fun_prop⟩) rfl p

/-- **Finite dimensionality from a finite cover**, by induction on the number of open sets: if
every nonempty finite intersection of members of a finite open cover of `Y` has finite
dimensional cohomology, so does `Y`. -/
private lemma finiteDimensional_of_finite_cover (r : ℕ) : ∀ (Y : TopCat.{0}) (U : Fin r → Set Y),
    (∀ i, IsOpen (U i)) → (⋃ i, U i) = univ →
    (∀ s : Finset (Fin r), s.Nonempty → ∀ p,
      FiniteDimensional ℚ (relCohomology ℚ (∅ : Set (TopCat.of (⋂ i ∈ s, U i : Set Y))) p)) →
    ∀ p, FiniteDimensional ℚ (relCohomology ℚ (∅ : Set Y) p) := by
  induction r with
  | zero =>
    intro Y U _ hcov _ p
    have : IsEmpty Y := ⟨fun y ↦ by
      have : y ∈ ⋃ i, U i := hcov ▸ mem_univ y
      obtain ⟨i, -⟩ := mem_iUnion.1 this
      exact i.elim0⟩
    exact finiteDimensional_of_isEmpty Y p
  | succ r ih =>
    intro Y U hU hcov hint p
    set A : Set Y := ⋃ i : Fin r, U i.castSucc with hAdef
    set B : Set Y := U (Fin.last r) with hBdef
    have hA : IsOpen A := isOpen_iUnion fun i ↦ hU _
    have hB : IsOpen B := hU _
    have hAB : A ∪ B = univ := by
      refine eq_univ_of_forall fun y ↦ ?_
      obtain ⟨i, hi⟩ := mem_iUnion.1 (hcov ▸ mem_univ y : y ∈ ⋃ i, U i)
      induction i using Fin.lastCases with
      | last => exact Or.inr hi
      | cast j => exact Or.inl (mem_iUnion.2 ⟨j, hi⟩)
    have hsub : ∀ s : Finset (Fin r), s.Nonempty →
        (⋂ i ∈ s.map Fin.castSuccEmb, U i) ⊆ A := by
      rintro s ⟨i, hi⟩ y hy
      exact mem_iUnion.2 ⟨i, mem_iInter₂.1 hy _ (Finset.mem_map_of_mem _ hi)⟩
    have hFA : ∀ p, FiniteDimensional ℚ (relCohomology ℚ (∅ : Set (TopCat.of A)) p) := by
      refine ih (TopCat.of A)
        (fun i ↦ (Subtype.val : A → Y) ⁻¹' U i.castSucc)
        (fun i ↦ (hU _).preimage continuous_subtype_val) ?_ ?_
      · refine eq_univ_of_forall fun y ↦ ?_
        obtain ⟨i, hi⟩ := mem_iUnion.1 y.2
        exact mem_iUnion.2 ⟨i, hi⟩
      · intro s hs q
        have := hint _ (hs.map (f := Fin.castSuccEmb)) q
        refine finiteDimensional_of_subset_val (hsub s hs) _ (fun y ↦ ?_) q
        simp [Finset.mem_map]
    have hFB : ∀ p, FiniteDimensional ℚ (relCohomology ℚ (∅ : Set (TopCat.of B)) p) := by
      intro q
      have h := hint {Fin.last r} (Finset.singleton_nonempty _) q
      have he : (⋂ i ∈ ({Fin.last r} : Finset (Fin (r + 1))), U i) = B := by simp [hBdef]
      rwa [he] at h
    have hFI : ∀ p, FiniteDimensional ℚ
        (relCohomology ℚ (∅ : Set (TopCat.of (A ∩ B : Set Y))) p) := by
      refine ih (TopCat.of (A ∩ B : Set Y))
        (fun i ↦ (Subtype.val : (A ∩ B : Set Y) → Y) ⁻¹' U i.castSucc)
        (fun i ↦ (hU _).preimage continuous_subtype_val) ?_ ?_
      · refine eq_univ_of_forall fun y ↦ ?_
        obtain ⟨i, hi⟩ := mem_iUnion.1 y.2.1
        exact mem_iUnion.2 ⟨i, hi⟩
      · intro s hs q
        have := hint (insert (Fin.last r) (s.map Fin.castSuccEmb)) (Finset.insert_nonempty _ _) q
        refine finiteDimensional_of_subset_val (W := A ∩ B)
          (S := ⋂ i ∈ insert (Fin.last r) (s.map Fin.castSuccEmb), U i)
          (fun y hy ↦ ⟨hsub s hs ?_, ?_⟩) _ (fun y ↦ ?_) q
        · exact mem_iInter₂.2 fun i hi ↦ mem_iInter₂.1 hy i (Finset.mem_insert_of_mem hi)
        · exact mem_iInter₂.1 hy _ (Finset.mem_insert_self _ _)
        · simp only [mem_iInter, mem_preimage, Finset.mem_insert, Finset.mem_map,
            Fin.coe_castSuccEmb, forall_eq_or_imp, forall_exists_index, and_imp,
            forall_apply_eq_imp_iff₂]
          exact ⟨fun h ↦ ⟨y.2.2, h⟩, fun h ↦ h.2⟩
    exact finiteDimensional_of_mayerVietoris hA hB hAB hFA hFB hFI p

/-- The cohomology of a space with a finite good cover is finite dimensional. -/
private theorem finiteDimensional_cohomology_of_goodCover {M : Type} [TopologicalSpace M]
    {n : ℕ} {ι : Type} [Finite ι] (𝒰 : ι → Opens M) (h𝒰 : ⨆ i, 𝒰 i = ⊤)
    (hball : ∀ s : Finset ι, s.Nonempty → (⋂ i ∈ s, (𝒰 i : Set M)).Nonempty →
      Nonempty ((⋂ i ∈ s, (𝒰 i : Set M)) ≃ₜ EuclideanSpace ℝ (Fin n))) (j : ℤ) :
    FiniteDimensional ℚ
      (cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) (TopCat.of M) Set.univ j) := by
  rcases lt_or_ge j 0 with hj | hj
  · have := ModuleCat.subsingleton_of_isZero
      (cohomologyWithSupports.isZero_relativeSingularCohomology_of_neg ℚ (TopCat.of M)
        (Set.univᶜ : Set (TopCat.of M)) hj)
    infer_instance
  obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hj
  obtain ⟨r, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  have hcov : (⋃ i, ((𝒰 (e.symm i) : Set M) : Set (TopCat.of M))) = univ := by
    refine eq_univ_of_forall fun y ↦ ?_
    have : y ∈ ((⨆ i, 𝒰 i : Opens M) : Set M) := h𝒰 ▸ mem_univ y
    rw [Opens.coe_iSup, mem_iUnion] at this
    obtain ⟨i, hi⟩ := this
    exact mem_iUnion.2 ⟨e i, by simpa using hi⟩
  have hFD := finiteDimensional_of_finite_cover r (TopCat.of M)
    (fun i ↦ ((𝒰 (e.symm i) : Set M) : Set (TopCat.of M))) (fun i ↦ (𝒰 (e.symm i)).isOpen) hcov
    (fun s hs q ↦ by
      have hset : (⋂ i ∈ s, ((𝒰 (e.symm i) : Set M) : Set (TopCat.of M))) =
          ⋂ k ∈ s.map e.symm.toEmbedding, (𝒰 k : Set M) := by
        ext y
        simp only [mem_iInter, Finset.mem_map_equiv, Equiv.symm_symm]
        exact ⟨fun h i hi ↦ by simpa using h (e i) hi,
          fun h i hi ↦ by simpa using h (e.symm i) (by simpa using hi)⟩
      rw [hset]
      rcases (⋂ k ∈ s.map e.symm.toEmbedding, (𝒰 k : Set M)).eq_empty_or_nonempty with h0 | hne
      · have : IsEmpty (TopCat.of (⋂ k ∈ s.map e.symm.toEmbedding, (𝒰 k : Set M) :
            Set (TopCat.of M))) := by
          change IsEmpty (⋂ k ∈ s.map e.symm.toEmbedding, (𝒰 k : Set M) : Set M)
          rw [h0]
          exact Set.isEmpty_coe_sort.2 rfl
        exact finiteDimensional_of_isEmpty _ q
      · obtain ⟨h⟩ := hball _ (hs.map (f := e.symm.toEmbedding)) hne
        exact finiteDimensional_of_homeomorph_euclidean h q) p
  have hc : (Set.univᶜ : Set (TopCat.of M)) = ∅ := Set.compl_univ
  have : FiniteDimensional ℚ (relCohomology ℚ (Set.univᶜ : Set (TopCat.of M)) p) := by
    rw [hc]
    exact hFD
  exact LinearEquiv.finiteDimensional
    (relativeSingularCohomologyEquiv ℚ (Set.univᶜ : Set (TopCat.of M)) p).symm

end FiniteDimensional

section UniversalCoefficients

variable {Y : Type*} [TopologicalSpace Y]

/-- **Universal coefficients over `ℚ`, detection.** A cochain vanishing on every relative
`(k + 1)`-cycle of `(Y, A)` is a relative coboundary of `(Y, A)`: over a field the functional
`∂ c + a ↦ ψ(c)` on boundaries plus chains of `A` extends to all chains. -/
private lemma mem_relCoboundaries_of_eval_eq_zero_rat (A : Set Y) (k : ℕ)
    {ψ : Simplex Y (k + 1) → ℚ}
    (hψ : ∀ c : Chain ℚ Y (k + 1), bd ℚ k c ∈ inside ℚ k A → SingularCochain.eval ψ c = 0) :
    ψ ∈ relCoboundaries ℚ A (k + 1) := by
  let L : (Chain ℚ Y (k + 1) × inside ℚ k A) →ₗ[ℚ] Chain ℚ Y k :=
    (bd ℚ k).coprod (inside ℚ k A).subtype
  let F : (Chain ℚ Y (k + 1) × inside ℚ k A) →ₗ[ℚ] ℚ :=
    (SingularCochain.eval ψ).comp (LinearMap.fst _ _ _)
  have hLF : LinearMap.ker L ≤ LinearMap.ker F := by
    rintro ⟨c, a⟩ hca
    have h0 : bd ℚ k c + a.1 = 0 := hca
    have hc : bd ℚ k c ∈ inside ℚ k A := by
      rw [eq_neg_of_add_eq_zero_left h0]
      exact neg_mem a.2
    exact hψ c hc
  let f : LinearMap.range L →ₗ[ℚ] ℚ :=
    ((LinearMap.ker L).liftQ F hLF).comp L.quotKerEquivRange.symm.toLinearMap
  have hf : ∀ x, f (L.rangeRestrict x) = F x := by
    intro x
    change (LinearMap.ker L).liftQ F hLF (L.quotKerEquivRange.symm (L.rangeRestrict x)) = _
    rw [show L.rangeRestrict x = L.quotKerEquivRange (Submodule.Quotient.mk x) from rfl,
      LinearEquiv.symm_apply_apply, Submodule.liftQ_apply]
  obtain ⟨g, hg⟩ := LinearMap.exists_extend f
  have hgL : ∀ x, g (L x) = F x := fun x ↦ by
    rw [← hf x]
    exact LinearMap.congr_fun hg (L.rangeRestrict x)
  let θ : Simplex Y k → ℚ := fun σ ↦ g (Finsupp.single σ 1)
  have hθ : SingularCochain.eval θ = g := by
    refine Finsupp.lhom_ext fun σ r ↦ ?_
    rw [SingularCochain.eval, Finsupp.linearCombination_single, smul_eq_mul, ← smul_eq_mul,
      ← map_smul,
      Finsupp.smul_single, smul_eq_mul, mul_one]
  refine ⟨θ, fun σ hσ ↦ ?_, ?_⟩
  · have hmem : Finsupp.single σ (1 : ℚ) ∈ inside ℚ k A :=
      Finsupp.single_mem_supported ℚ 1 hσ
    have := hgL (0, ⟨_, hmem⟩)
    simp only [L, F, LinearMap.coprod_apply, map_zero, zero_add, Submodule.subtype_apply,
      LinearMap.comp_apply, LinearMap.fst_apply] at this
    exact this
  · funext τ
    have h1 := eval_coboundary k θ (Finsupp.single τ 1)
    rw [SingularCochain.eval, Finsupp.linearCombination_single, one_smul] at h1
    rw [h1, hθ]
    have := hgL (Finsupp.single τ 1, 0)
    simp only [L, F, LinearMap.coprod_apply, map_zero, add_zero, LinearMap.comp_apply,
      LinearMap.fst_apply] at this
    rw [this, SingularCochain.eval, Finsupp.linearCombination_single, one_smul]

end UniversalCoefficients

section CapRestriction

open BorelMooreCap SingularCross BorelMooreCross Finsupp

variable {R : Type} [CommRing R] {Y : TopCat.{0}}

/-- The stage identity for one simplex, for a cochain whose coboundary vanishes on the simplices
of that simplex. -/
private lemma capFin_sub_capFin_towardsChainMap_succ_single (U : Set Y) (N p q n : ℕ)
    (h : p + q = n + 1) {φ : Simplex Y p → R} (σ : Simplex Y (n + 1))
    (hφ : coboundary R p φ ∈ vanishing R (p + 1) (range σ)) :
    capFin R p q (n + 1) h φ (single σ 1) -
        capFin R p q (n + 1) h φ (towardsChainMap R U N (n + 1) (single σ 1)) =
      bd R q (capFin R p (q + 1) (n + 2) (by omega) φ
          (towardsHomotopy R U N (n + 1) (single σ 1))) +
        capFin R p q (n + 1) h φ (towardsHomotopy R U N n (bd R n (single σ 1))) := by
  have e := capFin_bd p q (n + 1) h φ (towardsHomotopy R U N (n + 1) (single σ 1))
  rw [capFin_eq_zero_of_vanishing _ _ _ _ hφ
    (towardsHomotopy_mem_inside (single_mem_inside_range σ)), smul_zero, add_zero] at e
  rw [towardsChainMap_succ_apply, map_sub, map_sub, e]
  abel

private lemma capFin_sub_capFin_towardsChainMap_zero_single (U : Set Y) (N p q : ℕ) (h : p + q = 0)
    {φ : Simplex Y p → R} (σ : Simplex Y 0)
    (hφ : coboundary R p φ ∈ vanishing R (p + 1) (range σ)) :
    capFin R p q 0 h φ (single σ 1) -
        capFin R p q 0 h φ (towardsChainMap R U N 0 (single σ 1)) =
      bd R q (capFin R p (q + 1) 1 (by omega) φ (towardsHomotopy R U N 0 (single σ 1))) := by
  obtain rfl : p = 0 := by omega
  obtain rfl : q = 0 := by omega
  have e := capFin_bd 0 0 0 h φ (towardsHomotopy R U N 0 (single σ 1))
  rw [capFin_eq_zero_of_vanishing _ _ _ _ hφ
    (towardsHomotopy_mem_inside (single_mem_inside_range σ)), smul_zero, add_zero] at e
  rw [towardsChainMap_zero_apply, map_sub, e]
  simp

variable [T2Space Y] {U : Set Y}

open Classical in
private theorem restrFin_capFin_sub_capRestrCoeff_succ' (hU : IsOpen U) {p q m : ℕ}
    (h : p + q = m + 1)
    {φ : Simplex Y p → R} (σ : Simplex Y (m + 1))
    (hφ : coboundary R p φ ∈ vanishing R (p + 1) (range σ)) {ω : Simplex Y q}
    (hω : range ω ⊆ U) :
    restrFin R U (capFin R p q (m + 1) h φ (single σ 1)) ω -
        capRestrCoeff R U p q (m + 1) h φ σ ω =
      ∑ i : Fin (q + 2), (-1 : R) ^ (i : ℕ) * ∑ᶠ ω' : Simplex Y (q + 1),
          (if ω'.comp (face q i) = ω then
            capHomCoeff R U p (q + 1) (m + 1) (by omega) φ σ ω' else 0) +
        ∑ i : Fin (m + 2), (-1 : R) ^ (i : ℕ) *
          capHomCoeff R U p q m h φ (σ.comp (face m i)) ω := by
  obtain ⟨V, W, hV, -, hσV, hωW, hVW⟩ :=
    separatedNhds_range_inter_compl hU σ (isCompact_range ω.continuous) hω
  have hωW' : (range ω ∩ W).Nonempty := ⟨_, ⟨stdSimplex.vertex 0, rfl⟩, hωW ⟨_, rfl⟩⟩
  have hface : ∀ i : Fin (m + 2), range (σ.comp (face m i)) ∩ Uᶜ ⊆ V := fun i x hx ↦
    hσV ⟨by obtain ⟨t, ht⟩ := hx.1; exact ⟨_, ht⟩, hx.2⟩
  obtain ⟨Na, ha⟩ := exists_capHomCoeff_eq (R := R) (q := q + 1) hU (by omega) φ σ hV hVW hσV
  choose Nf hf using fun i : Fin (m + 2) ↦
    exists_capHomCoeff_eq (R := R) (q := q) hU h φ (σ.comp (face m i)) hV hVW (hface i)
  obtain ⟨Mg, hMg⟩ := exists_restrFin_capFin_towardsChainMap_eq (R := R) (q := q) hU h φ σ hV hVW
    hσV
  set N := max (max Na Mg) (Finset.univ.sup Nf)
  have hNa : Na ≤ N := le_max_of_le_left (le_max_left _ _)
  have hMg' : Mg ≤ N := le_max_of_le_left (le_max_right _ _)
  have hNf : ∀ i, Nf i ≤ N := fun i ↦ (Finset.le_sup (f := Nf) (Finset.mem_univ i)).trans
    (le_max_right _ _)
  have hst := congrArg (fun c ↦ restrFin R U c ω)
    (capFin_sub_capFin_towardsChainMap_succ_single U N p q m h σ hφ)
  simp only [restrFin_sub, restrFin_add] at hst
  rw [hMg N hMg' ω hωW', restrFin_bd hU _ hω] at hst
  rw [hst]
  congr 1
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    congr 1
    refine finsum_congr fun ω' ↦ ?_
    split_ifs with h'
    · exact ((ha N hNa).1 ω' (range_inter_nonempty_of_comp hωW' h')).symm
    · rfl
  · rw [bd_single, map_sum, map_sum, restrFin_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_smul, map_smul, restrFin_smul, (hf i N (hNf i)).1 ω hωW']

open Classical in
private theorem restrFin_capFin_sub_capRestrCoeff_zero' (hU : IsOpen U) {p q : ℕ} (h : p + q = 0)
    {φ : Simplex Y p → R} (σ : Simplex Y 0)
    (hφ : coboundary R p φ ∈ vanishing R (p + 1) (range σ)) {ω : Simplex Y q}
    (hω : range ω ⊆ U) :
    restrFin R U (capFin R p q 0 h φ (single σ 1)) ω - capRestrCoeff R U p q 0 h φ σ ω =
      ∑ i : Fin (q + 2), (-1 : R) ^ (i : ℕ) * ∑ᶠ ω' : Simplex Y (q + 1),
          (if ω'.comp (face q i) = ω then
            capHomCoeff R U p (q + 1) 0 (by omega) φ σ ω' else 0) := by
  obtain ⟨V, W, hV, -, hσV, hωW, hVW⟩ :=
    separatedNhds_range_inter_compl hU σ (isCompact_range ω.continuous) hω
  have hωW' : (range ω ∩ W).Nonempty := ⟨_, ⟨stdSimplex.vertex 0, rfl⟩, hωW ⟨_, rfl⟩⟩
  obtain ⟨Na, ha⟩ := exists_capHomCoeff_eq (R := R) (q := q + 1) hU (by omega) φ σ hV hVW hσV
  obtain ⟨Mg, hMg⟩ := exists_restrFin_capFin_towardsChainMap_eq (R := R) (q := q) hU h φ σ hV hVW
    hσV
  set N := max Na Mg
  have hst := congrArg (fun c ↦ restrFin R U c ω)
    (capFin_sub_capFin_towardsChainMap_zero_single U N p q h σ hφ)
  simp only [restrFin_sub] at hst
  rw [hMg N (le_max_right _ _) ω hωW', restrFin_bd hU _ hω] at hst
  rw [hst]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  congr 1
  refine finsum_congr fun ω' ↦ ?_
  split_ifs with h'
  · exact ((ha N (le_max_left _ _)).1 ω' (range_inter_nonempty_of_comp hωW' h')).symm
  · rfl

variable {U' : TopologicalSpace.Opens Y}

open Classical in
private lemma exists_capBdTerm' (p q n : ℕ) (h : p + q = n) (h' : p + (q + 1) = n + 1)
    {φ : Simplex Y p → R} (z : Cyc (R := R) Y n)
    (ν : Simp (TopCat.of U') q) :
    ∃ K₁ : Simp Y n → R, ∑ᶠ σ, K₁ σ * coeff R z.1 σ = 0 ∧
      (∀ σ, K₁ σ ≠ 0 → range (inclSimplex U' ν) ⊆ range (toC σ)) ∧
      ∀ σ, coboundary R p φ ∈ vanishing R (p + 1) (range (toC σ)) →
        restrFin R U' (capFin R p q n h φ (single (SingularCochain.simplexEquiv _ _ σ) 1)) (inclSimplex U' ν) -
          capRestrCoeff R U' p q n h φ (SingularCochain.simplexEquiv _ _ σ) (inclSimplex U' ν) =
        ∑ i : Fin (q + 2), (-1 : R) ^ (i : ℕ) * ∑ᶠ ω' : Simplex Y (q + 1),
          (if ω'.comp (face q i) = inclSimplex U' ν then
            capHomCoeff R U' p (q + 1) n h' φ (SingularCochain.simplexEquiv _ _ σ) ω' else 0) + K₁ σ := by
  have hω : range (inclSimplex U' ν) ⊆ U' := range_inclSimplex_subset U' ν
  cases n with
  | zero =>
    refine ⟨0, by simp, fun σ h0 ↦ absurd rfl h0, fun σ hσ ↦ ?_⟩
    rw [restrFin_capFin_sub_capRestrCoeff_zero' U'.isOpen h (SingularCochain.simplexEquiv _ _ σ)
      (by rw [range_simplexEquiv]; exact hσ) hω, Pi.zero_apply,
      add_zero]
  | succ m =>
    refine ⟨fun σ ↦ ∑ i : Fin (m + 2), (-1 : R) ^ (i : ℕ) *
      capHomCoeff R U' p q m h φ ((SingularCochain.simplexEquiv _ _ σ).comp (face m i)) (inclSimplex U' ν),
      finsum_capHomCoeff_face_mul_coeff_eq_zero h φ z ν, fun σ hσ ↦ ?_, fun σ hσ ↦
      restrFin_capFin_sub_capRestrCoeff_succ' U'.isOpen h (SingularCochain.simplexEquiv _ _ σ)
        (by rw [range_simplexEquiv]; exact hσ) hω⟩
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hσ
    refine ((range_subset_of_capHomCoeff_ne_zero (right_ne_zero_of_mul hi)).trans
      inter_subset_left).trans ?_
    rintro _ ⟨t, rfl⟩
    exact ⟨_, rfl⟩

open Classical in
/-- **The cap product commutes with restriction, for a cochain which is a cocycle near the
restriction.** If the coboundary of `φ` vanishes on the simplices of every simplex of the cycle
`z` that meets `U`, then `(φ ∩ z)|_U - φ|_U ∩ z|_U` is a boundary. -/
private theorem exists_d_eq_restrictChainMap_capChain_sub' (p q n : ℕ) (h : p + q = n)
    {φ : Simplex Y p → R} (z : Cyc (R := R) Y n)
    (hφ : ∀ σ, coeff R z.1 σ ≠ 0 → (range (toC σ) ∩ U').Nonempty →
      coboundary R p φ ∈ vanishing R (p + 1) (range (toC σ))) :
    ∃ u : (BM R (TopCat.of U')).X (q + 1),
      ((BM R (TopCat.of U')).d (q + 1) q).hom u =
        ((restrictChainMap R (ModuleCat.of R R) U').f q).hom (capChain R p q n h φ z.1) -
          capChain R p q n h (cochainPullback R (inclHom U') p φ)
            (((restrictChainMap R (ModuleCat.of R R) U').f n).hom z.1) := by
  have h' : p + (q + 1) = n + 1 := by omega
  set u₀ := ofCoeff R (capHomFun U' p (q + 1) n h' φ (coeff R z.1))
    (mem_lfChains.2 (isLocallyFiniteSet_capHomFun p (q + 1) n h' φ
      (mem_lfChains.1 (coeff_mem R z.1))))
  refine ⟨u₀, ?_⟩
  apply coeff_injective R
  funext ν
  obtain ⟨K₁, hK₁, hK₁s, hpt⟩ := exists_capBdTerm' p q n h h' (φ := φ) z ν
  rw [coeff_d_capHomFun]
  change _ = coeff R (((restrictChainMap R (ModuleCat.of R R) U').f q).hom
    (capChain R p q n h φ z.1)) ν - coeff R (capChain R p q n h
      (cochainPullback R (inclHom U') p φ)
        (((restrictChainMap R (ModuleCat.of R R) U').f n).hom z.1)) ν
  rw [coeff_restrictChainMap_capChain, coeff_capChain_restrictChainMap]
  set KD : Simp Y n → R := fun σ ↦ ∑ i : Fin (q + 2), (-1 : R) ^ (i : ℕ) *
    ∑ᶠ ω' : Simplex Y (q + 1), (if ω'.comp (face q i) = inclSimplex U' ν then
      capHomCoeff R U' p (q + 1) n h' φ (SingularCochain.simplexEquiv _ _ σ) ω' else 0) with hKD
  set KA : Simp Y n → R := fun σ ↦
    restrFin R U' (capFin R p q n h φ (single (SingularCochain.simplexEquiv _ _ σ) 1)) (inclSimplex U' ν) with hKA
  set KB : Simp Y n → R := fun σ ↦
    capRestrCoeff R U' p q n h φ (SingularCochain.simplexEquiv _ _ σ) (inclSimplex U' ν) with hKB
  have sD : ∀ σ, KD σ ≠ 0 → range (inclSimplex U' ν) ⊆ range (toC σ) := fun σ hσ ↦ by
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hσ
    obtain ⟨ω', hω'⟩ : ∃ ω' : Simplex Y (q + 1), (if ω'.comp (face q i) = inclSimplex U' ν then
        capHomCoeff R U' p (q + 1) n h' φ (SingularCochain.simplexEquiv _ _ σ) ω' else 0) ≠ 0 := by
      by_contra h''
      push Not at h''
      exact right_ne_zero_of_mul hi (finsum_eq_zero_of_forall_eq_zero h'')
    split_ifs at hω' with hc
    · refine Subset.trans ?_ ((range_subset_of_capHomCoeff_ne_zero hω').trans (inter_subset_left.trans (range_simplexEquiv _).subset))
      rw [← hc]
      rintro _ ⟨t, rfl⟩
      exact ⟨_, rfl⟩
    · exact absurd rfl hω'
  have sA : ∀ σ, KA σ ≠ 0 → range (inclSimplex U' ν) ⊆ range (toC σ) := fun σ hσ ↦
    (range_subset_of_restrFin_ne_zero (capFin_mem_inside p q n h φ
      (single_mem_inside_range (SingularCochain.simplexEquiv _ _ σ))) hσ).trans (inter_subset_left.trans (range_simplexEquiv _).subset)
  have sB : ∀ σ, KB σ ≠ 0 → range (inclSimplex U' ν) ⊆ range (toC σ) := fun σ hσ ↦
    (range_subset_of_capRestrCoeff_ne_zero hσ).trans (inter_subset_left.trans (range_simplexEquiv _).subset)
  rw [finsum_mul_coeff_eq_sum z.1 ν KD sD, finsum_mul_coeff_eq_sum z.1 ν KA sA,
    finsum_mul_coeff_eq_sum z.1 ν KB sB, ← Finset.sum_sub_distrib]
  rw [finsum_mul_coeff_eq_sum z.1 ν _ hK₁s] at hK₁
  have hpt' : ∀ σ ∈ meetFinset z.1 ν, KA σ * coeff R z.1 σ - KB σ * coeff R z.1 σ =
      KD σ * coeff R z.1 σ + K₁ σ * coeff R z.1 σ := fun σ hσ ↦ by
    obtain ⟨hz, y, hy, hyν⟩ := (Set.Finite.mem_toFinset _).1 hσ
    have hne : (range (toC σ) ∩ U').Nonempty := by
      refine ⟨y, ?_, range_inclSimplex_subset U' ν hyν⟩
      exact hy
    rw [← sub_mul, hpt σ (hφ σ hz hne)]
    ring
  rw [Finset.sum_congr rfl hpt', Finset.sum_add_distrib, hK₁, add_zero]

end CapRestriction

section Support

open BorelMooreCross BorelMooreCap SingularCross

variable {Y : TopCat.{0}}

/-- A locally finite chain has finitely many simplices meeting a compact set. -/
private lemma finite_meet {n : ℕ} (c : (BM ℚ Y).X n) {K : Set Y} (hK : IsCompact K) :
    {σ | coeff ℚ c σ ≠ 0 ∧ (range (toC σ) ∩ K).Nonempty}.Finite :=
  (coeff_mem ℚ c).finite_inter_compact hK

/-- A compact set together with the simplices of a locally finite chain meeting it. -/
private def thick {n : ℕ} (c : (BM ℚ Y).X n) {K : Set Y} (hK : IsCompact K) : Set Y :=
  K ∪ ⋃ σ ∈ (finite_meet c hK).toFinset, range (toC σ)

private lemma isCompact_thick {n : ℕ} (c : (BM ℚ Y).X n) {K : Set Y} (hK : IsCompact K) :
    IsCompact (thick c hK) :=
  hK.union ((finite_meet c hK).toFinset.isCompact_biUnion fun σ _ ↦
    isCompact_range (toC σ).continuous)

private lemma subset_thick {n : ℕ} (c : (BM ℚ Y).X n) {K : Set Y} (hK : IsCompact K) :
    K ⊆ thick c hK := by
  unfold thick
  exact subset_union_left

private lemma range_subset_thick {n : ℕ} (c : (BM ℚ Y).X n) {K : Set Y} (hK : IsCompact K)
    {σ : Simp Y n} (hσ : coeff ℚ c σ ≠ 0) (hσK : (range (toC σ) ∩ K).Nonempty) :
    range (toC σ) ⊆ thick c hK := by
  unfold thick
  exact subset_union_of_subset_right (subset_biUnion_of_mem (u := fun σ ↦ range (toC σ))
    ((finite_meet c hK).mem_toFinset.2 ⟨hσ, hσK⟩)) _

/-- A simplex of `c` reaching outside `thick c K` misses `K`. -/
private lemma range_subset_compl_of_meets {n : ℕ} (c : (BM ℚ Y).X n) {K : Set Y}
    (hK : IsCompact K) {σ : Simp Y n} (hσ : coeff ℚ c σ ≠ 0) {L : Set Y} (hL : L ⊆ (thick c hK)ᶜ)
    (h : (range (toC σ) ∩ L).Nonempty) : range (toC σ) ⊆ Kᶜ := by
  intro y hy hyK
  obtain ⟨x, hx, hxL⟩ := h
  exact hL hxL (range_subset_thick c hK hσ ⟨y, hy, hyK⟩ hx)

/-- The simplices of `φ ∩ c`, `φ` vanishing off a compact `K`, lie in `thick c K`. -/
private lemma range_subset_thick_of_capChain {p q n : ℕ} (h : p + q = n) {φ : Simplex Y p → ℚ}
    (c : (BM ℚ Y).X n) {K : Set Y} (hK : IsCompact K) (hφ : φ ∈ vanishing ℚ p Kᶜ) {τ : Simp Y q}
    (hτ : coeff ℚ (capChain ℚ p q n h φ c) τ ≠ 0) : range (toC τ) ⊆ thick c hK := by
  obtain ⟨σ, hσ, hw, hτσ⟩ := exists_of_coeff_capChain_ne_zero p q n h φ c hτ
  refine hτσ.trans (range_subset_thick c hK hσ ?_)
  by_contra h0
  exact hw (wt_eq_zero_of_vanishing _ hφ fun y hy hyK ↦ h0 ⟨y, hy, hyK⟩)

/-- `φ ∩ c` has finite support for `φ` vanishing off a compact set. -/
private lemma finite_support_capChain {p q n : ℕ} (h : p + q = n) {φ : Simplex Y p → ℚ}
    (c : (BM ℚ Y).X n) {K : Set Y} (hK : IsCompact K) (hφ : φ ∈ vanishing ℚ p Kᶜ) :
    (Function.support (capChain ℚ p q n h φ c).1).Finite := by
  refine (finite_meet (capChain ℚ p q n h φ c) (isCompact_thick c hK)).subset fun τ hτ ↦ ⟨hτ, ?_⟩
  obtain ⟨y, hy⟩ : (range (toC τ)).Nonempty := range_nonempty _
  exact ⟨y, hy, range_subset_thick_of_capChain h c hK hφ hτ hy⟩

variable [T2Space Y]

/-- The restriction of a chain all of whose simplices miss `U` vanishes. -/
private lemma restrict_eq_zero {n : ℕ} (U : Opens Y) (c : (BM ℚ Y).X n)
    (hc : ∀ σ, coeff ℚ c σ ≠ 0 → Disjoint (range (toC σ)) (U : Set Y)) :
    ((restrictChainMap ℚ (ModuleCat.of ℚ ℚ) U).f n).hom c = 0 := by
  apply coeff_injective ℚ
  funext ν
  rw [coeff_restrictChainMap_apply]
  refine finsum_eq_zero_of_forall_eq_zero fun τ ↦ ?_
  by_cases h : coeff ℚ c τ = 0
  · rw [h, mul_zero]
  · rw [restrictKernel_eq_restrCoeff, restrCoeff_of_disjoint (Disjoint.mono_left (range_simplexEquiv τ).le (hc τ h)), zero_mul]

end Support

section Pairings

open BorelMooreCross BorelMooreCap SingularCross

variable {Y : TopCat.{0}}

/-- **Graded commutativity against a cycle**: `⟨β ∪ φ, z⟩ = (-1)^{pq} ⟨φ ∪ β, z⟩` for a cocycle `φ`
vanishing off a compact set and a cocycle `β`. -/
private lemma localPairing_cup_comm {p q n : ℕ} (h : p + q = n) (h' : q + p = n)
    (z : Cyc (R := ℚ) Y n) {K : Set Y} (hK : IsCompact K) {φ : Simplex Y p → ℚ}
    (hφ : φ ∈ relCocycles ℚ Kᶜ p) {β : Simplex Y q → ℚ} (hβ : β ∈ relCocycles ℚ (∅ : Set Y) q) :
    localPairing (coeff ℚ z.1) (cup q p n h' β φ) =
      (-1 : ℚ) ^ (p * q) * localPairing (coeff ℚ z.1) (cup p q n h φ β) := by
  have hc := cup_comm_sub_mem_pairCoboundaries p q n h h' hφ hβ
  have h1 : cup p q n h φ β ∈ vanishing ℚ n Kᶜ := (cup_mem_vanishing h hφ.1 hβ.1).1
  have h2 : cup q p n h' β φ ∈ vanishing ℚ n Kᶜ := (cup_mem_vanishing h' hβ.1 hφ.1).2
  have hd : localPairing (coeff ℚ z.1)
      (cup q p n h' β φ - (-1 : ℚ) ^ (p * q) • cup p q n h φ β) = 0 := by
    cases n with
    | zero =>
      rw [show cup q p 0 h' β φ - (-1 : ℚ) ^ (p * q) • cup p q 0 h φ β = 0 from hc]
      exact localPairing_zero_right _
    | succ m =>
      obtain ⟨η, ⟨hη, -⟩, hη'⟩ := hc
      rw [← hη']
      change localPairing z.1.1 _ = 0
      rw [← localPairing_d z.1 hK hη, show ((BM ℚ Y).d (m + 1) m).hom z.1 = 0 from
        (mem_cyc_iff z.1).1 z.2]
      exact finsum_eq_zero_of_forall_eq_zero fun σ ↦ zero_mul _
  have hs : (-1 : ℚ) ^ (p * q) • cup p q n h φ β ∈ vanishing ℚ n Kᶜ :=
    Submodule.smul_mem _ _ h1
  rw [show cup q p n h' β φ = (cup q p n h' β φ - (-1 : ℚ) ^ (p * q) • cup p q n h φ β) +
      (-1 : ℚ) ^ (p * q) • cup p q n h φ β by abel,
    localPairing_add_right (coeff_mem ℚ z.1) hK (sub_mem h2 hs) hs, hd, zero_add,
    localPairing_smul_right (coeff_mem ℚ z.1) hK h1]

/-- `⟨β, φ ∩ c⟩ = ⟨β ∪ φ, c⟩` for `φ` vanishing off a compact set and any cochain `β`. -/
private lemma localPairing_capChain_right {p q n : ℕ} (h : p + q = n) (h' : q + p = n)
    (β : Simplex Y q → ℚ) (c : (BM ℚ Y).X n) {K : Set Y} (hK : IsCompact K)
    {φ : Simplex Y p → ℚ} (hφ : φ ∈ vanishing ℚ p Kᶜ) :
    localPairing (coeff ℚ (capChain ℚ p q n h φ c)) β =
      localPairing (coeff ℚ c) (cup q p n h' β φ) := by
  classical
  set L := thick c hK
  set β' : Simplex Y q → ℚ := fun τ ↦ if (range τ ∩ L).Nonempty then β τ else 0
  have hβ' : β' ∈ vanishing ℚ q Lᶜ := fun τ hτ ↦ by
    have : ¬ (range τ ∩ L).Nonempty := by
      rintro ⟨y, hy, hyL⟩
      exact hτ hy hyL
    simp [β', this]
  have e1 : localPairing (coeff ℚ (capChain ℚ p q n h φ c)) β =
      localPairing (coeff ℚ (capChain ℚ p q n h φ c)) β' := by
    refine finsum_congr fun τ ↦ ?_
    by_cases h0 : coeff ℚ (capChain ℚ p q n h φ c) τ = 0
    · change coeff ℚ _ τ * _ = coeff ℚ _ τ * _
      rw [h0, zero_mul, zero_mul]
    · obtain ⟨y, hy⟩ : (range (toC τ)).Nonempty := range_nonempty _
      change coeff ℚ _ τ * _ = coeff ℚ _ τ * _
      have : (range (SingularCochain.simplexEquiv _ _ τ) ∩ L).Nonempty :=
        ⟨y, (range_simplexEquiv τ).symm.subset hy, range_subset_thick_of_capChain h c hK hφ h0 hy⟩
      simp [β', this]
  have e2 : localPairing (coeff ℚ c) (cup q p n h' β φ) =
      localPairing (coeff ℚ c) (cup q p n h' β' φ) := by
    refine finsum_congr fun σ ↦ ?_
    by_cases h0 : coeff ℚ c σ = 0
    · change coeff ℚ c σ * _ = coeff ℚ c σ * _
      rw [h0, zero_mul, zero_mul]
    change coeff ℚ c σ * _ = coeff ℚ c σ * _
    rw [cup_apply, cup_apply]
    by_cases hb : φ (((SingularCochain.simplexEquiv Y _ σ : Simplex Y n)).comp (smap (back p n q (by omega)))) = 0
    · rw [hb, mul_zero, mul_zero, mul_zero, mul_zero]
    · have hσK : (range (toC σ) ∩ K).Nonempty := by
        by_contra h00
        exact hb (hφ _ (fun y hy hyK ↦
          h00 ⟨y, (range_simplexEquiv σ).subset (range_comp_smap_subset _ _ hy), hyK⟩))
      have hσL := range_subset_thick c hK h0 hσK
      have : (range ((SingularCochain.simplexEquiv Y _ σ : Simplex Y n).comp
          (smap (front q n (by omega)))) ∩ L).Nonempty :=
        ⟨_, ⟨stdSimplex.vertex 0, rfl⟩,
          hσL ((range_simplexEquiv σ).subset (range_comp_smap_subset _ _ ⟨_, rfl⟩))⟩
      simp only [β']
      rw [ite_eq_left this]
  rw [e1, e2]
  exact localPairing_capChain h h' φ c (isCompact_thick c hK) hβ'

/-- **Universal coefficients over `ℚ`, homology.** A finite chain on which every cocycle
vanishes is a boundary. -/
private lemma exists_bd_eq_of_eval_eq_zero {j : ℕ} (c : Chain ℚ Y j)
    (hc : ∀ β ∈ relCocycles ℚ (∅ : Set Y) j, SingularCochain.eval β c = 0) :
    ∃ d : Chain ℚ Y (j + 1), bd ℚ j d = c := by
  by_contra hne
  have hc' : c ∉ LinearMap.range (bd ℚ j) := fun ⟨d, hd⟩ ↦ hne ⟨d, hd⟩
  obtain ⟨f, hf, hf'⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hc' inferInstance
  let β : Simplex Y j → ℚ := fun σ ↦ f (Finsupp.single σ 1)
  have hβ : SingularCochain.eval β = f := by
    refine Finsupp.lhom_ext fun σ r ↦ ?_
    rw [SingularCochain.eval, Finsupp.linearCombination_single, smul_eq_mul, ← smul_eq_mul,
      ← map_smul, Finsupp.smul_single, smul_eq_mul, mul_one]
  have hfB : ∀ d, f (bd ℚ j d) = 0 := fun d ↦ by
    have : f (bd ℚ j d) ∈ (LinearMap.range (bd ℚ j)).map f := ⟨_, ⟨d, rfl⟩, rfl⟩
    rw [hf'] at this
    exact this
  refine hf ?_
  rw [← hβ]
  refine hc β ⟨mem_vanishing_empty _, ?_⟩
  change coboundary ℚ j β = 0
  funext τ
  have h1 := eval_coboundary j β (Finsupp.single τ 1)
  rw [SingularCochain.eval, Finsupp.linearCombination_single, one_smul] at h1
  rw [h1, hβ, hfB]
  rfl

end Pairings

section Injective

open BorelMooreCross BorelMooreCap SingularCross

variable {Y : TopCat.{0}} [T2Space Y]

omit [T2Space Y] in
/-- Every chain of degree `0` is a cycle. -/
private lemma mem_cyc_zero (x : (BM ℚ Y).X 0) : x ∈ Cyc (R := ℚ) Y 0 := by
  rw [mem_cyc_iff, (BM ℚ Y).shape 0 (0 - 1) (by simp)]
  rfl

/-- **Injectivity of the evaluation pairing**, from Poincaré duality on `Y` and on its open
subsets: a relative cocycle `φ` of `(Y, Y - K)` pairing to zero with every locally finite cycle is
a relative coboundary of `(Y, Y - K')` for a larger compact `K'`. With `φ ∩ z` a finite cycle
orthogonal to all cocycles, it bounds a finite chain `d`, so `φ = δ θ` by duality on `Y`;
`θ ∩ z ± d` is a cycle, homologous to `ζ ∩ z` for a cocycle `ζ`, and on the complement `U'` of a
compact containing `K`, the simplices of `z` meeting `K` and those of `d`, duality on `U'` makes
`θ - ζ` a coboundary. -/
private theorem exists_relCoboundaries_of_localPairing_eq_zero {n : ℕ} (z : Cyc (R := ℚ) Y n)
    (hD : DualityAt Y n z)
    (hDU : ∀ U : Opens Y, DualityAt (TopCat.of U) n (resCycOpen ℚ U z))
    {i : ℕ} (hi : i ≤ n) {K : Set Y} (hK : IsCompact K) (φ : relCocycles ℚ Kᶜ i)
    (hφ : ∀ w : Cyc (R := ℚ) Y i, localPairing (coeff ℚ w.1) φ.1 = 0) :
    ∃ K' : Set Y, IsCompact K' ∧ K ⊆ K' ∧ φ.1 ∈ relCoboundaries ℚ K'ᶜ i := by
  rcases i with _ | k
  · refine ⟨K, hK, subset_rfl, ?_⟩
    change φ.1 = 0
    funext σ
    have := hφ ⟨_, mem_cyc_zero (ofFinsupp (Finsupp.single σ (1 : ℚ)))⟩
    change localPairing (ofFinsupp (Finsupp.single σ (1 : ℚ))).1 φ.1 = 0 at this
    rw [PoincareDuality.localPairing_ofFinsupp, SingularCochain.eval,
      Finsupp.linearCombination_single, one_smul] at this
    exact this
  obtain ⟨j, rfl⟩ : ∃ j, n = k + j + 1 := ⟨n - k - 1, by omega⟩
  have h1 : k + 1 + j = k + j + 1 := by omega
  have h2 : j + (k + 1) = k + j + 1 := by omega
  -- `φ ∩ z` is orthogonal to every cocycle
  set cφ := capChain ℚ (k + 1) j (k + j + 1) h1 φ.1 z.1 with hcφ
  have horth : ∀ β ∈ relCocycles ℚ (∅ : Set Y) j, localPairing (coeff ℚ cφ) β = 0 := by
    intro β hβ
    rw [localPairing_capChain_right h1 h2 β z.1 hK φ.2.1, localPairing_cup_comm h1 h2 z hK φ.2 hβ,
      ← localPairing_capChain h2 h1 β z.1 hK φ.2.1,
      hφ ⟨capChain ℚ j (k + 1) (k + j + 1) h2 β z.1,
        capChain_mem_cyc _ j (k + 1) _ h2 ⟨β, hβ⟩ z⟩, mul_zero]
  -- so it bounds a finite chain
  have hfin := finite_support_capChain h1 z.1 hK φ.2.1
  set cf := toFinsupp cφ hfin
  have hcf : ofFinsupp cf = cφ := ofFinsupp_toFinsupp cφ hfin
  obtain ⟨d, hd⟩ := exists_bd_eq_of_eval_eq_zero cf fun β hβ ↦ by
    rw [← PoincareDuality.localPairing_ofFinsupp, hcf]
    exact horth β hβ
  -- `φ` is a coboundary on `Y`
  have hφabs : φ.1 ∈ relCocycles ℚ (∅ : Set Y) (k + 1) := ⟨mem_vanishing_empty _, φ.2.2⟩
  have hcap0 : capHomQ ℚ (∅ : Set Y) (k + 1) j (k + j + 1) h1
      (Submodule.Quotient.mk ⟨φ.1, hφabs⟩) (Submodule.Quotient.mk z) = 0 := by
    rw [capHomQ_mk]
    refine (mk_eq_zero_iff_exists _).2 ⟨ofFinsupp d, ?_⟩
    rw [d_ofFinsupp, hd, hcf]
  have hφ0 : (Submodule.Quotient.mk ⟨φ.1, hφabs⟩ : relCohomology ℚ (∅ : Set Y) (k + 1)) = 0 :=
    (hD.1 (k + 1) j h1).1 (hcap0.trans (by simp; rfl))
  obtain ⟨θ, hθ⟩ := (mk_eq_zero_iff_succ _).1 hφ0
  -- `θ ∩ z + (-1)^j d` is a cycle
  have hdθ : ((BM ℚ Y).d (j + 1) j).hom (capChain ℚ k (j + 1) (k + j + 1) (by omega) θ z.1) =
      -((-1 : ℤ) ^ j • cφ) := by
    have e := capChain_d k j (k + j) rfl θ z.1
    rw [show ((BM ℚ Y).d (k + j + 1) (k + j)).hom z.1 = 0 from (mem_cyc_iff z.1).1 z.2,
      map_zero, hθ] at e
    exact eq_neg_of_add_eq_zero_left e.symm
  set X := capChain ℚ k (j + 1) (k + j + 1) (by omega) θ z.1 + (-1 : ℤ) ^ j • ofFinsupp d
    with hXdef
  have hX : X ∈ Cyc (R := ℚ) Y (j + 1) := by
    rw [mem_cyc_iff]
    change ((BM ℚ Y).d (j + 1) j).hom X = 0
    rw [hXdef, map_add, map_zsmul, hdθ, d_ofFinsupp, hd, hcf, neg_add_cancel]
  -- duality on `Y`: `X` is homologous to `ζ ∩ z`
  obtain ⟨c, hc⟩ := (hD.1 k (j + 1) (by omega)).2 (Submodule.Quotient.mk ⟨X, hX⟩)
  obtain ⟨ζ, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  change capHomQ ℚ (∅ : Set Y) k (j + 1) (k + j + 1) _ (Submodule.Quotient.mk ζ)
    (Submodule.Quotient.mk z) = _ at hc
  rw [capHomQ_mk] at hc
  obtain ⟨E, hE⟩ := (mk_eq_mk_iff_exists _ _).1 hc
  -- the compact `K'` and its complement `U'`
  set K₁ := thick z.1 hK
  set K' := K₁ ∪ ⋃ τ ∈ d.support, range τ with hK'def
  have hK' : IsCompact K' := (isCompact_thick z.1 hK).union
    (d.support.isCompact_biUnion fun τ _ ↦ isCompact_range τ.continuous)
  have hKK' : K ⊆ K' := (subset_thick z.1 hK).trans subset_union_left
  set U' : Opens Y := ⟨K'ᶜ, hK'.isClosed.isOpen_compl⟩
  have hU'K₁ : (U' : Set Y) ⊆ K₁ᶜ := compl_subset_compl.2 subset_union_left
  have hU'K : (U' : Set Y) ⊆ Kᶜ := hU'K₁.trans (compl_subset_compl.2 (subset_thick z.1 hK))
  set r := restrictChainMap ℚ (ModuleCat.of ℚ ℚ) U'
  have hrd : (r.f (j + 1)).hom (ofFinsupp d) = 0 := restrict_eq_zero U' _ fun σ hσ ↦ by
    have hσd : SingularCochain.simplexEquiv _ _ σ ∈ d.support := Finsupp.mem_support_iff.2 hσ
    refine disjoint_compl_right_iff_subset.2 (subset_union_of_subset_right ?_ _)
    exact (range_simplexEquiv σ).symm.subset.trans
      (subset_biUnion_of_mem (u := fun τ : Simplex Y (j + 1) ↦ range τ) hσd)
  obtain ⟨u, hu⟩ := exists_d_eq_restrictChainMap_capChain_sub' k (j + 1) (k + j + 1) (by omega)
    (φ := θ) (U' := U') z fun σ hσ hσU ↦ by
      rw [hθ]
      exact vanishing_anti (range_subset_compl_of_meets z.1 hK hσ hU'K₁ hσU) φ.2.1
  obtain ⟨u', hu', -⟩ := exists_d_eq_restrictChainMap_capChain_sub (U := U') k (j + 1)
    (k + j + 1) (by omega) (A := ∅) (LinearMap.mem_ker.1 ζ.2.2) ζ.2.1 z
  -- duality on `U'`: `θ - ζ` is a coboundary there
  have hα : coboundary ℚ k (θ - ζ.1) ∈ vanishing ℚ (k + 1) (U' : Set Y) := by
    rw [map_sub, hθ, LinearMap.mem_ker.1 ζ.2.2, sub_zero]
    exact vanishing_anti hU'K φ.2.1
  have hcap : capHomQ ℚ (∅ : Set (TopCat.of U')) k (j + 1) (k + j + 1) (by omega)
      (Submodule.Quotient.mk (subCocycle ℚ (U' : Set Y) (θ - ζ.1) hα))
      (Submodule.Quotient.mk (resCycOpen ℚ U' z)) = 0 := by
    rw [capHomQ_mk]
    refine (mk_eq_zero_iff_exists _).2 ⟨u' - u - (r.f (j + 1 + 1)).hom E, ?_⟩
    rw [map_sub, map_sub, hu, hu', ← hom_f_d_apply, hE]
    change _ = capChain ℚ k (j + 1) (k + j + 1) _
      (cochainPullback ℚ (inclHom U') k (θ - ζ.1)) ((r.f (k + j + 1)).hom z.1)
    simp only [map_sub, LinearMap.sub_apply, hXdef, map_add, map_zsmul, hrd, smul_zero, add_zero]
    abel
  have hα0 : (Submodule.Quotient.mk (subCocycle ℚ (U' : Set Y) (θ - ζ.1) hα) :
      relCohomology ℚ (∅ : Set (TopCat.of U')) k) = 0 :=
    ((hDU U').1 k (j + 1) (by omega)).1 (hcap.trans (by simp; rfl))
  refine ⟨K', hK', hKK', ?_⟩
  rcases k with _ | m
  · rw [mk_subCocycle_eq_zero_iff_zero] at hα0
    exact ⟨θ - ζ.1, hα0, by rw [map_sub, hθ, LinearMap.mem_ker.1 ζ.2.2, sub_zero]⟩
  · obtain ⟨θ', hθ'⟩ := (mk_subCocycle_eq_zero_iff_succ _ _ _).1 hα0
    exact ⟨θ - ζ.1 - coboundary ℚ m θ', hθ', by
      rw [map_sub, map_sub, hθ, coboundary_coboundary, LinearMap.mem_ker.1 ζ.2.2, sub_zero,
        sub_zero]⟩

end Injective

section Cutoff

open BorelMooreCross BorelMooreCap SingularCross

open Classical in
/-- The simplices of a locally finite chain missing a set `A`. -/
private def chainOff {X : TopCat.{0}} {n : ℕ} (c : (BM ℚ X).X n) (A : Set X) : (BM ℚ X).X n :=
  ofCoeff ℚ (fun σ ↦ if (range (toC σ) ∩ A).Nonempty then 0 else coeff ℚ c σ)
    (mem_lfChains.2 ((mem_lfChains.1 (coeff_mem ℚ c)).mono fun σ hσ ↦ by
      intro h0
      exact hσ (by simp [h0])))

open Classical in
private lemma coeff_chainOff {X : TopCat.{0}} {n : ℕ} (c : (BM ℚ X).X n) (A : Set X)
    (σ : Simp X n) : coeff ℚ (chainOff c A) σ =
      if (range (toC σ) ∩ A).Nonempty then 0 else coeff ℚ c σ :=
  rfl

private lemma coeff_sub' {X : TopCat.{0}} {n : ℕ} (a b : (BM ℚ X).X n) :
    coeff ℚ (a - b) = coeff ℚ a - coeff ℚ b :=
  rfl

/-- A simplex of `∂ c` is a face of a simplex of `c`. -/
private lemma exists_of_coeff_d_ne_zero {X : TopCat.{0}} {n : ℕ} (c : (BM ℚ X).X (n + 1))
    {τ : Simp X n} (hτ : coeff ℚ (((BM ℚ X).d (n + 1) n).hom c) τ ≠ 0) :
    ∃ ω, coeff ℚ c ω ≠ 0 ∧ range (toC τ) ⊆ range (toC ω) := by
  rw [coeff_d, Finset.sum_apply] at hτ
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hτ
  have hi' : pushforwardFun ((TopCat.toSSet.obj X).δ i) (coeff ℚ c) τ ≠ 0 := fun h0 ↦
    hi (by simp [h0])
  obtain ⟨ω, hω, rfl⟩ := support_pushforwardFun_subset _ _ hi'
  exact ⟨ω, hω, by rintro _ ⟨t, rfl⟩; exact ⟨_, rfl⟩⟩

/-- The boundary of a finitely supported chain pairs to zero with a cocycle. -/
private lemma localPairing_d_of_finite {X : TopCat.{0}} {n : ℕ} (c : (BM ℚ X).X (n + 1))
    (hc : (Function.support c.1).Finite) {β : Simplex X n → ℚ} (hβ : coboundary ℚ n β = 0) :
    localPairing (coeff ℚ (((BM ℚ X).d (n + 1) n).hom c)) β = 0 := by
  rw [← ofFinsupp_toFinsupp c hc, d_ofFinsupp]
  change localPairing (ofFinsupp _).1 β = 0
  rw [PoincareDuality.localPairing_ofFinsupp, ← eval_coboundary, hβ]
  simp

/-- Pairing is additive in finitely supported chains. -/
private lemma localPairing_add_of_finite {X : TopCat.{0}} {n : ℕ} {c d : (BM ℚ X).X n}
    (hc : (Function.support c.1).Finite) (hd : (Function.support d.1).Finite)
    (β : Simplex X n → ℚ) :
    localPairing (coeff ℚ (c + d)) β = localPairing (coeff ℚ c) β + localPairing (coeff ℚ d) β := by
  rw [coeff_add, localPairing, localPairing, localPairing, ← finsum_add_distrib
    (hc.subset fun σ hσ h0 ↦ hσ (by change c.1 σ * _ = 0; rw [h0, zero_mul]))
    (hd.subset fun σ hσ h0 ↦ hσ (by change d.1 σ * _ = 0; rw [h0, zero_mul]))]
  exact finsum_congr fun σ ↦ by simp [add_mul]

/-- A preconnected set meeting the open `N ⊆ C`, `C` closed, and not inside `N`, meets
`C \ N`. -/
private lemma inter_diff_nonempty {X : Type*} [TopologicalSpace X] {S N C : Set X}
    (hS : IsPreconnected S) (hN : IsOpen N) (hC : IsClosed C) (hNC : N ⊆ C)
    (hSN : (S ∩ N).Nonempty) (hSN' : ¬ S ⊆ N) : (S ∩ (C \ N)).Nonempty := by
  by_contra h0
  have hsub : S ⊆ N ∪ Cᶜ := fun x hx ↦ by
    by_cases hxN : x ∈ N
    · exact Or.inl hxN
    · exact Or.inr fun hxC ↦ h0 ⟨x, hx, hxC, hxN⟩
  rcases hS.subset_or_subset hN hC.isOpen_compl
    (disjoint_compl_right_iff_subset.2 hNC) hsub with h | h
  · exact hSN' h
  · obtain ⟨x, hxS, hxN⟩ := hSN
    exact h hxS (hNC hxN)

variable {Y : TopCat.{0}} [T2Space Y]

/-- If every simplex of `c` lies in `U`, the coefficients of the restriction of `c` to `U` are
those of `c` on the included simplices. -/
private lemma coeff_restrict_of_subset {n : ℕ} (U : Opens Y) (c : (BM ℚ Y).X n)
    (hc : ∀ σ, coeff ℚ c σ ≠ 0 → range (toC σ) ⊆ U) (ν : Simp (TopCat.of U) n) :
    coeff ℚ (((restrictChainMap ℚ (ModuleCat.of ℚ ℚ) U).f n).hom c) ν =
      coeff ℚ c ((SingularCochain.simplexEquiv Y _).symm (inclSimplex U ν)) := by
  classical
  rw [coeff_restrictChainMap_apply,
    finsum_eq_single _ ((SingularCochain.simplexEquiv Y _).symm (inclSimplex U ν))]
  · by_cases h0 : coeff ℚ c ((SingularCochain.simplexEquiv Y _).symm (inclSimplex U ν)) = 0
    · rw [h0, mul_zero]
    · rw [restrictKernel_eq_restrCoeff, SingularChain.restrCoeff_of_range_subset ((range_simplexEquiv _).le.trans (hc _ h0))]
      simp
  · intro τ hτ
    by_cases h0 : coeff ℚ c τ = 0
    · rw [h0, mul_zero]
    · rw [restrictKernel_eq_restrCoeff, SingularChain.restrCoeff_of_range_subset ((range_simplexEquiv _).le.trans (hc _ h0)),
        Finsupp.single_apply, ite_eq_right, zero_mul]
      intro he
      exact hτ (by rw [← he]; exact ((SingularCochain.simplexEquiv Y _).symm_apply_apply τ).symm)

/-- A simplex of `c|_U` lies in a simplex of `c`. -/
private lemma exists_of_coeff_restrict_ne_zero {n : ℕ} (U : Opens Y) (c : (BM ℚ Y).X n)
    {ν : Simp (TopCat.of U) n}
    (hν : coeff ℚ (((restrictChainMap ℚ (ModuleCat.of ℚ ℚ) U).f n).hom c) ν ≠ 0) :
    ∃ τ, coeff ℚ c τ ≠ 0 ∧ range (inclSimplex U ν) ⊆ range (toC τ) := by
  rw [coeff_restrictChainMap_apply] at hν
  obtain ⟨τ, hτ⟩ : ∃ τ, (restrictKernel U n τ ν : ℚ) * coeff ℚ c τ ≠ 0 := by
    by_contra h
    push Not at h
    exact hν (finsum_eq_zero_of_forall_eq_zero h)
  refine ⟨τ, right_ne_zero_of_mul hτ, ?_⟩
  have h1 := left_ne_zero_of_mul hτ
  rw [restrictKernel_eq_restrCoeff] at h1
  exact (range_subset_of_restrCoeff_ne_zero h1).trans (inter_subset_left.trans (range_simplexEquiv _).subset)

/-- Pairing the restriction of a chain lying in `U` with the restriction of a cochain. -/
private lemma localPairing_restrict_of_subset {n : ℕ} (U : Opens Y) (c : (BM ℚ Y).X n)
    (hc : ∀ σ, coeff ℚ c σ ≠ 0 → range (toC σ) ⊆ U) (β : Simplex Y n → ℚ) :
    localPairing (coeff ℚ (((restrictChainMap ℚ (ModuleCat.of ℚ ℚ) U).f n).hom c))
        (cochainPullback ℚ (inclHom U) n β) = localPairing (coeff ℚ c) β := by
  set e := SingularCochain.simplexEquiv Y n
  set f : Simplex Y n → ℚ := fun s ↦ coeff ℚ c (e.symm s) * β s
  have hl : localPairing (coeff ℚ (((restrictChainMap ℚ (ModuleCat.of ℚ ℚ) U).f n).hom c))
      (cochainPullback ℚ (inclHom U) n β) = ∑ᶠ ν, f (inclSimplex U ν) := by
    refine finsum_congr fun ν ↦ ?_
    rw [coeff_restrict_of_subset U c hc ν]
    rfl
  rw [hl, ← finsum_mem_range (inclSimplex_injective U n), ← finsum_mem_inter_support,
    inter_eq_right.2 fun s hs ↦ ?_, finsum_mem_support]
  · rw [localPairing, ← finsum_comp_equiv e.symm]
    refine finsum_congr fun s ↦ ?_
    simp only [f, e, Equiv.apply_symm_apply]
  · have h0 : coeff ℚ c (e.symm s) ≠ 0 := fun h0 ↦ hs (by simp [f, h0])
    have := (range_simplexEquiv _).le.trans (hc _ h0)
    rw [show SingularCochain.simplexEquiv _ _ (e.symm s) = s from e.apply_symm_apply s] at this
    exact mem_range_inclSimplex U this

/-- **Cutting off a chain whose restriction bounds.** Let `F` be a locally finite chain of `Y`
with finite boundary whose restriction to the complement `U` of a compact set `K` is a boundary.
Then every cocycle vanishes on `∂ F`. -/
private lemma localPairing_d_eq_zero_of_restrict [LocallyCompactSpace Y] {q : ℕ} {K : Set Y}
    (hK : IsCompact K) (U : Opens Y) (hU : (U : Set Y) = Kᶜ) (F : (BM ℚ Y).X (q + 1))
    (hF : (Function.support (((BM ℚ Y).d (q + 1) q).hom F).1).Finite)
    (H : (BM ℚ (TopCat.of U)).X (q + 1 + 1))
    (hFH : ((restrictChainMap ℚ (ModuleCat.of ℚ ℚ) U).f (q + 1)).hom F =
      ((BM ℚ (TopCat.of U)).d (q + 1 + 1) (q + 1)).hom H)
    {β : Simplex Y q → ℚ} (hβ : coboundary ℚ q β = 0) :
    localPairing (coeff ℚ (((BM ℚ Y).d (q + 1) q).hom F)) β = 0 := by
  classical
  obtain ⟨L, hL, hKL⟩ := exists_compact_superset hK
  set N := interior L
  have hNL : N ⊆ L := interior_subset
  have hKU : ∀ {A : Set Y}, A ∩ K = ∅ → A ⊆ U := fun h x hx ↦ by
    rw [hU]; exact fun hxK ↦ (h ▸ (⟨hx, hxK⟩ : x ∈ _ ∩ K) : x ∈ (∅ : Set Y))
  set r := restrictChainMap ℚ (ModuleCat.of ℚ ℚ) U
  set dY := fun m ↦ ((BM ℚ Y).d (m + 1) m).hom
  -- the far part of `F` and its finite complement
  set Ff := chainOff F L
  set FC := F - Ff
  have hFf : ∀ σ, coeff ℚ Ff σ ≠ 0 → range (toC σ) ⊆ Lᶜ := fun σ hσ x hx hxL ↦ by
    rw [coeff_chainOff, ite_eq_left ⟨x, hx, hxL⟩] at hσ
    exact hσ rfl
  have hFfU : ∀ σ, coeff ℚ Ff σ ≠ 0 → range (toC σ) ⊆ U := fun σ hσ ↦
    hKU (subset_empty_iff.1 fun x ⟨hx, hxK⟩ ↦ hFf σ hσ hx (interior_subset (hKL hxK)))
  have hFC : ∀ σ, coeff ℚ FC σ ≠ 0 → coeff ℚ F σ ≠ 0 ∧ (range (toC σ) ∩ L).Nonempty := by
    intro σ hσ
    change coeff ℚ F σ - coeff ℚ Ff σ ≠ 0 at hσ
    by_cases h : (range (toC σ) ∩ L).Nonempty
    · rw [coeff_chainOff, ite_eq_left h, sub_zero] at hσ
      exact ⟨hσ, h⟩
    · rw [coeff_chainOff, ite_eq_right h, sub_self] at hσ
      exact absurd rfl hσ
  have hFCfin : (Function.support FC.1).Finite :=
    (finite_meet F hL).subset fun σ hσ ↦ hFC σ hσ
  have hdFCfin : (Function.support (dY q FC).1).Finite := by
    rw [← ofFinsupp_toFinsupp FC hFCfin, d_ofFinsupp]
    exact (Finsupp.hasFiniteSupport _).preimage (SingularCochain.simplexEquiv Y _).injective.injOn |>.subset
      fun σ hσ ↦ hσ
  have hsplit : dY q F = dY q FC + dY q Ff := by
    simp only [dY, FC, map_sub, sub_add_cancel]
  have hdFffin : (Function.support (dY q Ff).1).Finite := by
    have : dY q Ff = dY q F - dY q FC := by rw [hsplit]; abel
    rw [this]
    exact (hF.union hdFCfin).subset fun σ hσ ↦ by
      by_contra h
      simp only [mem_union, Function.mem_support, not_or, not_not] at h
      exact hσ (by change (dY q F).1 σ - (dY q FC).1 σ = 0; rw [h.1, h.2, sub_zero])
  change localPairing (coeff ℚ (dY q F)) β = 0
  rw [hsplit, localPairing_add_of_finite hdFCfin hdFffin,
    localPairing_d_of_finite FC hFCfin hβ, zero_add]
  -- the far part: compare with the cut-off of `H`
  have hdFfU : ∀ σ, coeff ℚ (dY q Ff) σ ≠ 0 → range (toC σ) ⊆ U := fun σ hσ ↦ by
    obtain ⟨ω, hω, hσω⟩ := exists_of_coeff_d_ne_zero Ff hσ
    exact hσω.trans (hFfU ω hω)
  rw [← localPairing_restrict_of_subset U _ hdFfU β]
  set Hf := chainOff H (Subtype.val ⁻¹' N : Set (TopCat.of U))
  set R := (r.f (q + 1)).hom Ff - ((BM ℚ (TopCat.of U)).d (q + 1 + 1) (q + 1)).hom Hf
  have hdR : ((BM ℚ (TopCat.of U)).d (q + 1) q).hom R = (r.f q).hom (dY q Ff) := by
    simp only [R, map_sub, hom_f_d_apply, dY]
    rw [show ((BM ℚ (TopCat.of U)).d (q + 1) q).hom
        (((BM ℚ (TopCat.of U)).d (q + 1 + 1) (q + 1)).hom Hf) = 0 from
      congrArg (fun f ↦ ModuleCat.Hom.hom f Hf) ((BM ℚ (TopCat.of U)).d_comp_d _ _ _), sub_zero]
  rw [← hdR]
  -- `R` is finite
  set D₁ : Set (TopCat.of U) := Subtype.val ⁻¹' (L \ N)
  have hLN : L \ N ⊆ U := hKU (subset_empty_iff.1 fun x ⟨⟨_, hxN⟩, hxK⟩ ↦ hxN (hKL hxK))
  have hD₁ : IsCompact D₁ :=
    (IsInducing.subtypeVal.isCompact_preimage_iff (by simpa using hLN)).2
      (hL.diff isOpen_interior)
  set SH := (finite_meet H hD₁).toFinset
  set L₂ := L ∪ (⋃ σ ∈ hFCfin.toFinset, range (toC σ)) ∪
    ⋃ ω ∈ SH, range (inclSimplex U ω)
  have hL₂ : IsCompact L₂ :=
    (hL.union (hFCfin.toFinset.isCompact_biUnion fun σ _ ↦
      isCompact_range (toC σ).continuous)).union
      (SH.isCompact_biUnion fun ω _ ↦ isCompact_range (inclSimplex U ω).continuous)
  have hLL₂ : L ⊆ L₂ := subset_union_left.trans subset_union_left
  have hNval : ∀ ω : Simp (TopCat.of U) (q + 1 + 1),
      (range (toC ω) ∩ (Subtype.val ⁻¹' N : Set (TopCat.of U))).Nonempty ↔
        (range (inclSimplex U ω) ∩ N).Nonempty := fun ω ↦ by
    rw [range_inclSimplex]
    constructor
    · rintro ⟨x, hx, hxN⟩
      exact ⟨x.1, ⟨x, hx, rfl⟩, hxN⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, hxN⟩
      exact ⟨x, hx, hxN⟩
  have hR : ∀ ν, coeff ℚ R ν ≠ 0 → (range (inclSimplex U ν) ∩ (L₂ \ N)).Nonempty := by
    intro ν hν
    by_contra hcon
    have hν0 : (range (inclSimplex U ν)).Nonempty := range_nonempty _
    by_cases hνN : range (inclSimplex U ν) ⊆ N
    · -- near `K`: both terms vanish
      apply hν
      change coeff ℚ ((r.f (q + 1)).hom Ff) ν - coeff ℚ (((BM ℚ (TopCat.of U)).d
        (q + 1 + 1) (q + 1)).hom Hf) ν = 0
      have e1 : coeff ℚ ((r.f (q + 1)).hom Ff) ν = 0 := by
        rw [coeff_restrict_of_subset U Ff hFfU, coeff_chainOff]
        obtain ⟨x, hx⟩ := hν0
        rw [ite_eq_left ⟨x, (range_simplexEquiv _).subset (by rw [Equiv.apply_symm_apply]; exact hx),
          hNL (hνN hx)⟩]
      have e2 : coeff ℚ (((BM ℚ (TopCat.of U)).d (q + 1 + 1) (q + 1)).hom Hf) ν = 0 := by
        by_contra h2
        obtain ⟨ω, hω, hνω⟩ := exists_of_coeff_d_ne_zero Hf h2
        rw [coeff_chainOff] at hω
        split_ifs at hω with hωN
        · exact hω rfl
        · obtain ⟨x, hx⟩ := range_nonempty (toC ν)
          exact hωN ⟨x, hνω hx, hνN (by
            obtain ⟨t, ht⟩ := hx
            exact ⟨(SingularChain.stdSimplexHomeo _).symm t, by
              rw [← ht]
              exact congrArg (fun s ↦ ((toC ν s : U) : Y)) ((SingularChain.stdSimplexHomeo _).apply_symm_apply t)⟩)⟩
      rw [e1, e2, sub_zero]
    · -- far from `K`
      have hfar : ¬ range (inclSimplex U ν) ⊆ L₂ := fun h ↦ by
        obtain ⟨x, hx⟩ := hν0
        by_cases hxN : x ∈ N
        · exact hcon (inter_diff_nonempty (isPreconnected_range (inclSimplex U ν).continuous)
            isOpen_interior hL₂.isClosed (interior_subset.trans hLL₂) ⟨x, hx, hxN⟩ hνN)
        · exact hcon ⟨x, hx, h hx, hxN⟩
      apply hν
      have hRe : R = ((BM ℚ (TopCat.of U)).d (q + 1 + 1) (q + 1)).hom (H - Hf) -
          (r.f (q + 1)).hom FC := by
        simp only [R, FC, map_sub, ← hFH]
        abel
      rw [hRe, coeff_sub', Pi.sub_apply]
      have e1 : coeff ℚ ((r.f (q + 1)).hom FC) ν = 0 := by
        by_contra h1
        obtain ⟨τ, hτ, hντ⟩ := exists_of_coeff_restrict_ne_zero U FC h1
        exact hfar (hντ.trans ((subset_union_of_subset_right (subset_biUnion_of_mem
          (u := fun σ ↦ range (toC σ)) (hFCfin.mem_toFinset.2 hτ)) L).trans subset_union_left))
      have e2 : coeff ℚ (((BM ℚ (TopCat.of U)).d (q + 1 + 1) (q + 1)).hom (H - Hf)) ν = 0 := by
        by_contra h2
        obtain ⟨ω, hω, hνω⟩ := exists_of_coeff_d_ne_zero (H - Hf) h2
        rw [coeff_sub', Pi.sub_apply, coeff_chainOff] at hω
        split_ifs at hω with hωN
        · have hωH : coeff ℚ H ω ≠ 0 := by simpa using hω
          have hνω' : range (inclSimplex U ν) ⊆ range (inclSimplex U ω) := by
            rw [range_inclSimplex, range_inclSimplex]
            exact image_mono hνω
          by_cases hωL : range (inclSimplex U ω) ⊆ L
          · exact hfar (hνω'.trans (hωL.trans hLL₂))
          · have hωN' := (hNval ω).1 hωN
            obtain ⟨y, hy, hyLN⟩ := inter_diff_nonempty
              (isPreconnected_range (inclSimplex U ω).continuous) isOpen_interior hL.isClosed
              interior_subset hωN' fun h ↦ hωL (h.trans interior_subset)
            have hωS : ω ∈ SH := by
              refine (finite_meet H hD₁).mem_toFinset.2 ⟨hωH, ?_⟩
              rw [range_inclSimplex] at hy
              obtain ⟨x, hx, rfl⟩ := hy
              exact ⟨x, hx, hyLN⟩
            exact hfar (hνω'.trans (subset_union_of_subset_right
              (subset_biUnion_of_mem (u := fun ω ↦ range (inclSimplex U ω)) hωS) _))
        · exact hω (sub_self _)
      rw [e1, e2, sub_zero]
  have hRfin : (Function.support R.1).Finite := by
    set D₂ : Set (TopCat.of U) := Subtype.val ⁻¹' (L₂ \ N)
    have hL₂N : L₂ \ N ⊆ U := hKU (subset_empty_iff.1 fun x ⟨⟨_, hxN⟩, hxK⟩ ↦ hxN (hKL hxK))
    have hD₂ : IsCompact D₂ :=
      (IsInducing.subtypeVal.isCompact_preimage_iff (by simpa using hL₂N)).2
        (hL₂.diff isOpen_interior)
    refine (finite_meet R hD₂).subset fun ν hν ↦ ⟨hν, ?_⟩
    obtain ⟨_, ⟨t, rfl⟩, hyLN⟩ := hR ν hν
    exact ⟨_, ⟨SingularChain.stdSimplexHomeo _ t, rfl⟩, hyLN⟩
  exact localPairing_d_of_finite R hRfin (by rw [coboundary_cochainPullback, hβ, map_zero])

end Cutoff

section Surjective

open BorelMooreCross BorelMooreCap SingularCross

variable {Y : TopCat.{0}} [T2Space Y]

/-- The homotopy between the direct and the iterated restriction vanishes on chains whose
simplices miss `U'`. -/
private lemma homotopyMap_eq_zero_of_disjoint (U : Opens Y) {U' : Opens Y} (h : U' ≤ U) {n : ℕ}
    {c : (BM ℚ Y).X n} (hc : ∀ σ, coeff ℚ c σ ≠ 0 → Disjoint (range (toC σ)) (U' : Set Y)) :
    (homotopyMap ℚ (ModuleCat.of ℚ ℚ) U h n).hom c = 0 := by
  apply Subtype.ext
  funext ω
  change kernelFun (homKernel U n) c.1 ω = 0
  refine finsum_eq_zero_of_forall_eq_zero fun σ ↦ ?_
  by_cases h0 : c.1 σ = 0
  · rw [h0, smul_zero]
  have : homKernel U n σ ω = 0 := by
    rw [homKernel, homCoeff]
    refine finsum_eq_zero_of_forall_eq_zero fun i ↦ ?_
    rw [restrFin, Finsupp.sum]
    refine Finset.sum_eq_zero fun τ hτ ↦ ?_
    have hτσ : range τ ⊆ range (toC σ) :=
      Set.Subset.trans (subdivHomotopy_mem_inside (badChain_mem_inside (single_mem_inside_range _)) hτ)
        (range_simplexEquiv σ).subset
    rw [restrCoeff_of_disjoint ((hc σ h0).mono_left hτσ), mul_zero]
  rw [this, zero_smul]

/-- For a chain `v` whose boundary misses `U'`, the iterated restriction `(v|_U)|_{U'}` and the
direct one `v|_{U'}` differ by a boundary. -/
private lemma exists_d_eq_subRestrict_sub (U : Opens Y) {U' : Opens Y} (h : U' ≤ U) {k : ℕ}
    (v : (BM ℚ Y).X (k + 1))
    (hv : ∀ σ, coeff ℚ (((BM ℚ Y).d (k + 1) k).hom v) σ ≠ 0 →
      Disjoint (range (toC σ)) (U' : Set Y)) :
    ∃ u : (BM ℚ (TopCat.of U')).X (k + 1 + 1),
      ((BM ℚ (TopCat.of U')).d (k + 1 + 1) (k + 1)).hom u =
        subRestrict ℚ (ModuleCat.of ℚ ℚ) U h (k + 1)
            (((restrictChainMap ℚ (ModuleCat.of ℚ ℚ) U).f (k + 1)).hom v) -
          ((restrictChainMap ℚ (ModuleCat.of ℚ ℚ) U').f (k + 1)).hom v := by
  have e := congrArg (fun φ ↦ φ.hom v)
    (directRestrictChainMap_sub_succ ℚ (ModuleCat.of ℚ ℚ) U h k)
  simp only [ModuleCat.hom_sub, LinearMap.sub_apply, ModuleCat.hom_comp, ModuleCat.hom_add,
    LinearMap.add_apply, LinearMap.comp_apply] at e
  rw [homotopyMap_eq_zero_of_disjoint U h hv, zero_add] at e
  refine ⟨-PoincareAlexander.pushChain ℚ (subOpensInv U h) (isProperMap_subOpensInv U h)
    (k + 1 + 1) ((homotopyMap ℚ (ModuleCat.of ℚ ℚ) U h (k + 1)).hom v), ?_⟩
  have h2 : PoincareAlexander.pushChain ℚ (subOpensInv U h) (isProperMap_subOpensInv U h) (k + 1)
      (((directRestrictChainMap ℚ (ModuleCat.of ℚ ℚ) U h).f (k + 1)).hom v) =
      ((restrictChainMap ℚ (ModuleCat.of ℚ ℚ) U').f (k + 1)).hom v :=
    pushChain_pushChain_of_comp_eq_id (subOpensMap U h) (subOpensInv U h)
      (isProperMap_subOpensMap U h) (isProperMap_subOpensInv U h) rfl (k + 1) _
  rw [map_neg, ← pushChain_d, ← e, map_sub, neg_sub, h2]
  rfl

private lemma finite_support_ofFinsupp {X : TopCat.{0}} {n : ℕ} (f : Chain ℚ X n) :
    (Function.support (ofFinsupp f).1).Finite :=
  (f.support.finite_toSet.preimage (SingularCochain.simplexEquiv X n).injective.injOn).subset
    fun _ hσ ↦ Finset.mem_coe.2 (Finsupp.mem_support_iff.2 hσ)

/-- Acting twice by `(-1) ^ j` is the identity. -/
private lemma neg_one_pow_smul_smul {V : Type*} [AddCommGroup V] (j : ℕ) (x : V) :
    (-1 : ℤ) ^ j • (-1 : ℤ) ^ j • x = x := by
  rw [smul_smul, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul]

omit [T2Space Y] in
/-- From the Leibniz rule against a cycle: `δ ε ∩ z = -(-1)^j ∂ (ε ∩ z)`. -/
private lemma capChain_coboundary_eq {k j : ℕ} (z : Cyc (R := ℚ) Y (k + j + 1))
    (ε : Simplex Y k → ℚ) (h : k + 1 + j = k + j + 1) :
    capChain ℚ (k + 1) j (k + j + 1) h (coboundary ℚ k ε) z.1 =
      -((-1 : ℤ) ^ j • ((BM ℚ Y).d (j + 1) j).hom
        (capChain ℚ k (j + 1) (k + j + 1) (by omega) ε z.1)) := by
  have e := capChain_d k j (k + j) rfl ε z.1
  rw [show ((BM ℚ Y).d (k + j + 1) (k + j)).hom z.1 = 0 from (mem_cyc_iff z.1).1 z.2,
    map_zero] at e
  have e' := eq_neg_of_add_eq_zero_right e.symm
  rw [← neg_one_pow_smul_smul j (capChain ℚ (k + 1) j (k + j + 1) h (coboundary ℚ k ε) z.1)]
  change (-1 : ℤ) ^ j • ((-1 : ℤ) ^ j • capChain ℚ (k + 1) j (k + j + 1) _
    (coboundary ℚ k ε) z.1) = _
  rw [e', smul_neg]

/-- **Duality onto finite homology, as seen by cocycles.** Every finite cycle `c` of `Y` is,
against every cocycle, the cap product `φ ∩ z` of a relative cocycle `φ` of `(Y, Y - K)` for a
compact `K`. From duality on `Y`, `c ∼ ζ ∩ z`; duality on the complement of the support of `c`
moves `ζ` to `φ₁ = ζ - δ ε`, with `φ₁ ∩ z - c = ∂ F₁`; duality on a smaller complement `U₂`
corrects `φ₁` by `δ η` so that `F|_{U₃}` bounds, and the cut-off lemma makes `∂ F` invisible to
cocycles. -/
private theorem exists_eval_eq_localPairing_capChain [LocallyCompactSpace Y] {n : ℕ}
    (z : Cyc (R := ℚ) Y n) (hD : DualityAt Y n z)
    (hDU : ∀ U : Opens Y, DualityAt (TopCat.of U) n (resCycOpen ℚ U z))
    {i j : ℕ} (hij : i + j = n) (c : Chain ℚ Y j) (hc : ofFinsupp c ∈ Cyc (R := ℚ) Y j) :
    ∃ (K : Set Y) (_ : IsCompact K) (φ : relCocycles ℚ Kᶜ i),
      ∀ β ∈ relCocycles ℚ (∅ : Set Y) j,
        SingularCochain.eval β c = localPairing (coeff ℚ (capChain ℚ i j n hij φ.1 z.1)) β := by
  classical
  -- duality on `Y`
  obtain ⟨cl, hcl⟩ := (hD.1 i j hij).2 (Submodule.Quotient.mk ⟨ofFinsupp c, hc⟩)
  obtain ⟨ζ, rfl⟩ := Submodule.Quotient.mk_surjective _ cl
  change capHomQ ℚ (∅ : Set Y) i j n hij (Submodule.Quotient.mk ζ)
    (Submodule.Quotient.mk z) = _ at hcl
  rw [capHomQ_mk] at hcl
  obtain ⟨E, hE⟩ := (mk_eq_mk_iff_exists _ _).1 hcl
  -- the complement `U₁` of the support of `c`
  set K₁ := ⋃ τ ∈ c.support, range τ
  have hK₁ : IsCompact K₁ := c.support.isCompact_biUnion fun τ _ ↦ isCompact_range τ.continuous
  set U₁ : Opens Y := ⟨K₁ᶜ, hK₁.isClosed.isOpen_compl⟩
  have hcK₁ : ∀ σ, coeff ℚ (ofFinsupp c) σ ≠ 0 → range (toC σ) ⊆ K₁ := fun σ hσ ↦
    (range_simplexEquiv σ).symm.subset.trans
      (subset_biUnion_of_mem (u := fun τ : Simplex Y j ↦ range τ) (Finsupp.mem_support_iff.2 hσ))
  have hrc : ((restrictChainMap ℚ (ModuleCat.of ℚ ℚ) U₁).f j).hom (ofFinsupp c) = 0 :=
    restrict_eq_zero U₁ _ fun σ hσ ↦ disjoint_compl_right_iff_subset.2 (hcK₁ σ hσ)
  have hcapU : capHomQ ℚ (∅ : Set (TopCat.of U₁)) i j n hij
      (Submodule.Quotient.mk (pullCoc ℚ (inclHom U₁) ζ))
      (Submodule.Quotient.mk (resCycOpen ℚ U₁ z)) = 0 := by
    refine (capHomQ_pullCoc_resCycOpen U₁ hij ζ z).trans ((mk_resCycOpen_eq U₁
      (w := capCycle ℚ hij ζ z) (w' := ⟨ofFinsupp c, hc⟩)
      ((mk_eq_mk_iff_exists _ _).2 ⟨E, hE⟩)).trans ?_)
    exact (mk_eq_zero_iff_exists _).2 ⟨0, by rw [map_zero]; exact hrc.symm⟩
  have hζ0 : (Submodule.Quotient.mk (pullCoc ℚ (inclHom U₁) ζ) :
      relCohomology ℚ (∅ : Set (TopCat.of U₁)) i) = 0 :=
    ((hDU U₁).1 i j hij).1 (hcapU.trans (by simp; rfl))
  have hζδ : coboundary ℚ i ζ.1 ∈ vanishing ℚ (i + 1) (U₁ : Set Y) := by
    rw [LinearMap.mem_ker.1 ζ.2.2]; exact zero_mem _
  have hpull : pullCoc ℚ (inclHom U₁) ζ = subCocycle ℚ (U₁ : Set Y) ζ.1 hζδ := rfl
  rw [hpull] at hζ0
  -- `φ₁ = ζ - δ ε` vanishes on `U₁`, and `φ₁ ∩ z - c = ∂ F₁`
  obtain ⟨φ₁, hφ₁, F₁, hF₁⟩ : ∃ φ₁ : Simplex Y i → ℚ, φ₁ ∈ relCocycles ℚ (U₁ : Set Y) i ∧
      ∃ F₁ : (BM ℚ Y).X (j + 1), ((BM ℚ Y).d (j + 1) j).hom F₁ =
        capChain ℚ i j n hij φ₁ z.1 - ofFinsupp c := by
    rcases i with _ | k
    · rw [mk_subCocycle_eq_zero_iff_zero] at hζ0
      exact ⟨ζ.1, ⟨hζ0, ζ.2.2⟩, E, hE⟩
    · obtain ⟨ε, hε⟩ := (mk_subCocycle_eq_zero_iff_succ _ _ _).1 hζ0
      obtain rfl : n = k + j + 1 := by omega
      refine ⟨ζ.1 - coboundary ℚ k ε, ⟨hε, LinearMap.mem_ker.2 (by
        rw [map_sub, coboundary_coboundary, LinearMap.mem_ker.1 ζ.2.2, sub_zero])⟩,
        E + (-1 : ℤ) ^ j • capChain ℚ k (j + 1) (k + j + 1) (by omega) ε z.1, ?_⟩
      rw [map_add, map_zsmul, hE, map_sub, LinearMap.sub_apply, capChain_coboundary_eq z ε hij]
      abel
  have hφ₁K : φ₁ ∈ relCocycles ℚ K₁ᶜ i := hφ₁
  -- the compact `K₂` containing the simplices of `∂ F₁`
  set K₂ := thick z.1 hK₁
  have hK₂ : IsCompact K₂ := isCompact_thick z.1 hK₁
  have hK₁₂ : K₁ ⊆ K₂ := subset_thick z.1 hK₁
  set U₂ : Opens Y := ⟨K₂ᶜ, hK₂.isClosed.isOpen_compl⟩
  have hdF₁ : ∀ σ, coeff ℚ (((BM ℚ Y).d (j + 1) j).hom F₁) σ ≠ 0 → range (toC σ) ⊆ K₂ := by
    intro σ hσ
    rw [hF₁] at hσ
    by_cases h1 : coeff ℚ (capChain ℚ i j n hij φ₁ z.1) σ = 0
    · have h2 : coeff ℚ (ofFinsupp c) σ ≠ 0 := fun h2 ↦ hσ (by
        rw [coeff_sub', Pi.sub_apply, h1, h2, sub_zero])
      exact (hcK₁ σ h2).trans hK₁₂
    · exact range_subset_thick_of_capChain hij z.1 hK₁ hφ₁K.1 h1
  -- conclusion from a corrected pair `(φ, F)`
  have hfinal : ∀ (K : Set Y) (hK : IsCompact K) (φ : relCocycles ℚ Kᶜ i)
      (F : (BM ℚ Y).X (j + 1)),
      ((BM ℚ Y).d (j + 1) j).hom F = capChain ℚ i j n hij φ.1 z.1 - ofFinsupp c →
      (∀ β ∈ relCocycles ℚ (∅ : Set Y) j,
        localPairing (coeff ℚ (((BM ℚ Y).d (j + 1) j).hom F)) β = 0) →
      ∃ (K : Set Y) (_ : IsCompact K) (φ : relCocycles ℚ Kᶜ i),
        ∀ β ∈ relCocycles ℚ (∅ : Set Y) j,
          SingularCochain.eval β c = localPairing (coeff ℚ (capChain ℚ i j n hij φ.1 z.1)) β := by
    intro K hK φ F hF h0
    refine ⟨K, hK, φ, fun β hβ ↦ ?_⟩
    have hfin1 := finite_support_capChain hij z.1 hK φ.2.1
    have hfin2 : (Function.support (ofFinsupp c).1).Finite := finite_support_ofFinsupp c
    have hfin3 : (Function.support (capChain ℚ i j n hij φ.1 z.1 - ofFinsupp c).1).Finite :=
      (hfin1.union hfin2).subset fun σ hσ ↦ by
        by_contra h
        simp only [mem_union, Function.mem_support, not_or, not_not] at h
        exact hσ (by change (capChain ℚ i j n hij φ.1 z.1).1 σ - (ofFinsupp c).1 σ = 0
                     rw [h.1, h.2, sub_zero])
    have := h0 β hβ
    rw [hF] at this
    rw [show capChain ℚ i j n hij φ.1 z.1 = (capChain ℚ i j n hij φ.1 z.1 - ofFinsupp c) +
      ofFinsupp c by abel, localPairing_add_of_finite hfin3 hfin2, this, zero_add]
    exact (PoincareDuality.localPairing_ofFinsupp c β).symm
  have hcyc₂ : ((restrictChainMap ℚ (ModuleCat.of ℚ ℚ) U₂).f (j + 1)).hom F₁ ∈
      Cyc (R := ℚ) (TopCat.of U₂) (j + 1) := by
    rw [mem_cyc_iff]
    change ((BM ℚ (TopCat.of U₂)).d (j + 1) j).hom _ = 0
    rw [← hom_f_d_apply]
    exact restrict_eq_zero U₂ _ fun σ hσ ↦ disjoint_compl_right_iff_subset.2 (hdF₁ σ hσ)
  rcases i with _ | k
  · -- degree `0`: `H_{j+1}(U₂) = 0`
    have hsub := (hDU U₂).2.2 (j + 1) (by omega)
    obtain ⟨H, hH⟩ := (mk_eq_zero_iff_exists _).1
      (@Subsingleton.elim _ hsub (Submodule.Quotient.mk ⟨_, hcyc₂⟩) 0)
    refine hfinal K₁ hK₁ ⟨φ₁, hφ₁K⟩ F₁ hF₁ fun β hβ ↦ ?_
    refine localPairing_d_eq_zero_of_restrict hK₂ U₂ rfl F₁ ?_ H hH.symm hβ.2
    exact (finite_meet _ hK₂).subset fun σ hσ ↦ ⟨hσ, by
      obtain ⟨y, hy⟩ := range_nonempty (toC σ); exact ⟨y, hy, hdF₁ σ hσ hy⟩⟩
  -- degree `k + 1`: correct `φ₁` by `δ η`, `η` from duality on `U₂`
  obtain rfl : n = k + j + 1 := by omega
  obtain ⟨cη, hcη⟩ := ((hDU U₂).1 k (j + 1) (by omega)).2 (Submodule.Quotient.mk ⟨_, hcyc₂⟩)
  obtain ⟨η, rfl⟩ := Submodule.Quotient.mk_surjective _ cη
  obtain ⟨η', hη', rfl⟩ := exists_subCocycle_eq (U₂ : Set Y) η
  have hdη : coboundary ℚ (k + 1) (coboundary ℚ k η') = 0 := coboundary_coboundary _ _
  set φ := φ₁ + (-1 : ℚ) ^ j • coboundary ℚ k η' with hφdef
  have hφK : φ ∈ relCocycles ℚ K₂ᶜ (k + 1) := by
    refine ⟨add_mem (vanishing_anti (compl_subset_compl.2 hK₁₂) hφ₁.1)
      (Submodule.smul_mem _ _ hη'), ?_⟩
    refine LinearMap.mem_ker.2 ?_
    rw [map_add, map_smul, hdη, smul_zero, add_zero]
    exact LinearMap.mem_ker.1 hφ₁.2
  set F := F₁ - capChain ℚ k (j + 1) (k + j + 1) (by omega) η' z.1 with hFdef
  have hF : ((BM ℚ Y).d (j + 1) j).hom F = capChain ℚ (k + 1) j (k + j + 1) hij φ z.1 -
      ofFinsupp c := by
    rw [hFdef, map_sub, hF₁, hφdef, map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
      capChain_coboundary_eq z η' hij, smul_neg, ← Int.cast_smul_eq_zsmul ℚ, Int.cast_pow,
      Int.cast_neg, Int.cast_one, smul_smul, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow,
      one_smul]
    abel
  refine hfinal K₂ hK₂ ⟨φ, hφK⟩ F hF fun β hβ ↦ ?_
  -- `F|_{U₃}` bounds
  set K₃ := thick z.1 hK₂
  have hK₃ : IsCompact K₃ := isCompact_thick z.1 hK₂
  set U₃ : Opens Y := ⟨K₃ᶜ, hK₃.isClosed.isOpen_compl⟩
  have h32 : U₃ ≤ U₂ := compl_subset_compl.2 (subset_thick z.1 hK₂)
  have hK₂₃ : K₂ ⊆ K₃ := subset_thick z.1 hK₂
  have hdF : ∀ σ, coeff ℚ (((BM ℚ Y).d (j + 1) j).hom F) σ ≠ 0 → range (toC σ) ⊆ K₃ := by
    intro σ hσ
    rw [hF] at hσ
    by_cases h1 : coeff ℚ (capChain ℚ (k + 1) j (k + j + 1) hij φ z.1) σ = 0
    · have h2 : coeff ℚ (ofFinsupp c) σ ≠ 0 := fun h2 ↦ hσ (by
        rw [coeff_sub', Pi.sub_apply, h1, h2, sub_zero])
      exact ((hcK₁ σ h2).trans hK₁₂).trans hK₂₃
    · exact range_subset_thick_of_capChain hij z.1 hK₂ hφK.1 h1
  -- the class of `F₁|_{U₂}` is `η ∩ z|_{U₂}`
  have hcls : (Submodule.Quotient.mk (capCycle ℚ (by omega : k + (j + 1) = k + j + 1)
      (subCocycle ℚ (U₂ : Set Y) η' hη') (resCycOpen ℚ U₂ z)) :
        HomQ (R := ℚ) (TopCat.of U₂) (j + 1)) = Submodule.Quotient.mk ⟨_, hcyc₂⟩ := by
    rw [← hcη]
    rfl
  have h3 := (capHomQ_pullCoc_opensLE U₂ h32 (by omega : k + (j + 1) = k + j + 1)
    (subCocycle ℚ (U₂ : Set Y) η' hη') z).trans (mk_subRestrictCyc_eq U₂ h32 hcls)
  rw [capHomQ_mk] at h3
  obtain ⟨w₀, hw₀⟩ := (mk_eq_mk_iff_exists _ _).1 h3
  obtain ⟨u₁, hu₁⟩ := exists_d_eq_subRestrict_sub U₂ h32 F₁ fun σ hσ ↦
    disjoint_compl_right_iff_subset.2 ((hdF₁ σ hσ).trans hK₂₃)
  obtain ⟨u₂, hu₂⟩ := exists_d_eq_restrictChainMap_capChain_sub' k (j + 1) (k + j + 1)
    (by omega) (φ := η') (U' := U₃) z fun σ hσ hσU ↦
      vanishing_anti (range_subset_compl_of_meets z.1 hK₂ hσ (subset_refl _) hσU) hη'
  refine localPairing_d_eq_zero_of_restrict hK₃ U₃ rfl F ?_ (-(w₀ + u₁ + u₂)) ?_ hβ.2
  · exact (finite_meet _ hK₃).subset fun σ hσ ↦ ⟨hσ, by
      obtain ⟨y, hy⟩ := range_nonempty (toC σ); exact ⟨y, hy, hdF σ hσ hy⟩⟩
  · have hw₀' : ((BM ℚ (TopCat.of U₃)).d (j + 1 + 1) (j + 1)).hom w₀ =
        capChain ℚ k (j + 1) (k + j + 1) (by omega) (cochainPullback ℚ (inclHom U₃) k η')
          (((restrictChainMap ℚ (ModuleCat.of ℚ ℚ) U₃).f (k + j + 1)).hom z.1) -
        subRestrict ℚ (ModuleCat.of ℚ ℚ) U₂ h32 (j + 1)
          (((restrictChainMap ℚ (ModuleCat.of ℚ ℚ) U₂).f (j + 1)).hom F₁) := hw₀
    rw [map_neg, map_add, map_add, hw₀', hu₁, hu₂, hFdef, map_sub]
    abel

end Surjective

section Perfect

open BorelMooreCross BorelMooreCap

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] {M : Type} [TopologicalSpace M]
  [T2Space M] [ChartedSpace H M] {n : ℕ}

omit [T2Space M] in
/-- **`H^{k+1}(M, M - K; ℚ) = 0` for `k ≥ n`** (Hatcher, Lemma 3.27): the relative homology
vanishes above the dimension, and over `ℚ` a cocycle vanishing on relative cycles is a
coboundary. -/
private lemma mem_relCoboundaries_of_dim_le [T2Space M] (b : Module.Basis (Fin n) ℝ H)
    {K : Set M} (hK : IsCompact K) {k : ℕ} (hk : n ≤ k)
    (φ : relCocycles ℚ (Kᶜ : Set (TopCat.of M)) (k + 1)) :
    φ.1 ∈ relCoboundaries ℚ (Kᶜ : Set (TopCat.of M)) (k + 1) := by
  have : LocallyCompactSpace H :=
    (SingularChain.basisHomeomorph b).isOpenEmbedding.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  have hv := SingularChain.relVanishing_of_isCompact_of_chartedSpace (R := ℚ) b (m := n)
    (fun a c k' hk' ↦ SingularChain.relVanishing_Icc
      (fun n' hn' j hj ↦ SingularChain.cycleVanishing_compl_zero n' hn' j hj) n a c k' hk')
    hK k hk
  refine mem_relCoboundaries_of_eval_eq_zero_rat _ k fun c hc ↦ ?_
  obtain ⟨w, hw⟩ := hv c hc
  have h1 := eval_eq_zero_of_mem_vanishing φ.2.1 hw
  have h2 : SingularCochain.eval φ.1 (bd ℚ (k + 1) w) = 0 := by
    rw [← eval_coboundary, show coboundary ℚ (k + 1) φ.1 = 0 from φ.2.2]
    simp
  rwa [map_sub, h2, sub_zero] at h1

/-- A manifold with a finite good cover is second countable. -/
private lemma secondCountableTopology_of_goodCover {ι : Type} [Finite ι] (𝒰 : ι → Opens M)
    (h𝒰 : ⨆ i, 𝒰 i = ⊤)
    (hball : ∀ s : Finset ι, s.Nonempty → (⋂ i ∈ s, (𝒰 i : Set M)).Nonempty →
      Nonempty ((⋂ i ∈ s, (𝒰 i : Set M)) ≃ₜ EuclideanSpace ℝ (Fin n))) :
    SecondCountableTopology M := by
  have hU : ∀ i, SecondCountableTopology (𝒰 i : Set M) := fun i ↦ by
    have hs : (⋂ k ∈ ({i} : Finset ι), (𝒰 k : Set M)) = 𝒰 i := by simp
    rcases (𝒰 i : Set M).eq_empty_or_nonempty with h0 | hne
    · have : Finite (𝒰 i : Set M) := by rw [h0]; infer_instance
      infer_instance
    · obtain ⟨e⟩ := hball {i} (Finset.singleton_nonempty i) (hs ▸ hne)
      rw [hs] at e
      exact e.secondCountableTopology
  have : ∀ i, SecondCountableTopology (𝒰 i : Set M) := hU
  refine TopologicalSpace.secondCountableTopology_of_countable_cover
    (U := fun i ↦ (𝒰 i : Set M)) (fun i ↦ (𝒰 i).isOpen) ?_
  rw [← Opens.coe_iSup, h𝒰, Opens.coe_top]

omit [T2Space M] in
/-- The pairing of a cycle with a relative cocycle depends only on its homology class. -/
private lemma localPairing_cyc_eq {i : ℕ} {K : Set (TopCat.of M)} (hK : IsCompact K)
    (φ : relCocycles ℚ Kᶜ i) {w w' : Cyc (R := ℚ) (TopCat.of M) i}
    (h : (Submodule.Quotient.mk w : HomQ (R := ℚ) (TopCat.of M) i) = Submodule.Quotient.mk w') :
    localPairing (coeff ℚ w.1) φ.1 = localPairing (coeff ℚ w'.1) φ.1 := by
  obtain ⟨u, hu⟩ := (PoincareAlexander.mk_eq_mk_iff_exists w w').1 h
  have h0 : localPairing ((((borelMooreChainComplex ℚ (ModuleCat.of ℚ ℚ) (TopCat.of M)).d
      (i + 1) i).hom u).1 : (TopCat.toSSet.obj (TopCat.of M)).obj (op ⦋i⦌) → ℚ) φ.1 = 0 := by
    rw [localPairing_d u hK φ.2.1, show coboundary ℚ i φ.1 = 0 from φ.2.2]
    exact localPairing_zero_right _
  have hw : w.1 = w'.1 + ((borelMooreChainComplex ℚ (ModuleCat.of ℚ ℚ) (TopCat.of M)).d
      (i + 1) i).hom u := by rw [hu]; abel
  change localPairing (w.1.1) φ.1 = localPairing (w'.1.1) φ.1
  rw [hw]
  change localPairing ((w'.1 : (borelMooreChainComplex ℚ (ModuleCat.of ℚ ℚ) (TopCat.of M)).X i).1 +
    (((borelMooreChainComplex ℚ (ModuleCat.of ℚ ℚ) (TopCat.of M)).d (i + 1) i).hom u).1) φ.1 = _
  rw [localPairing_add_left w'.1.2 (((borelMooreChainComplex ℚ (ModuleCat.of ℚ ℚ)
    (TopCat.of M)).d (i + 1) i).hom u).2 hK φ.2.1, h0, add_zero]

omit [T2Space M] in
/-- A class of `H^p(M, M - K)` represented by a relative coboundary of `(M, M - K')` vanishes in
`H^p(M, M - K')`. -/
private lemma map_eq_zero_of_mem_relCoboundaries {p : ℕ} {A A' : Set (TopCat.of M)}
    (h : A' ⊆ (𝟙 (TopCat.of M) : TopCat.of M ⟶ TopCat.of M) ⁻¹' A) (φ : relCocycles ℚ A p)
    (hφ : φ.1 ∈ relCoboundaries ℚ A' p) :
    (relativeSingularCohomology.map ℚ (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of M)) h p).hom
        ((relativeSingularCohomologyEquiv ℚ A p).symm (Submodule.Quotient.mk φ)) = 0 := by
  apply (relativeSingularCohomologyEquiv ℚ A' p).injective
  rw [relativeSingularCohomologyEquiv_map, LinearEquiv.apply_symm_apply, relCohomologyMap_mk,
    map_zero]
  exact (Submodule.Quotient.mk_eq_zero _).2 hφ

/-- The locally finite cycle of the cycle/boundary model chosen for `μ`. -/
private def cycOf (μ : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of M) n) :
    Cyc (R := ℚ) (TopCat.of M) n :=
  ((borelMooreChainComplex ℚ (ModuleCat.of ℚ ℚ) (TopCat.of M)).sc n).moduleCatCyclesIso.hom.hom
    (exists_cycle μ).choose

omit [T2Space M] in
private lemma homologyEquiv_eq_mk_cycOf
    (μ : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of M) n) :
    homologyEquiv ℚ (TopCat.of M) n μ = Submodule.Quotient.mk (cycOf μ) :=
  homologyEquiv_eq_mk _ (exists_cycle μ).choose_spec

omit [T2Space M] in
/-- A class of a finite chain all of whose simplices miss everything vanishes: `inside ∅ = 0`. -/
private lemma eq_zero_of_mem_inside_empty {k : ℕ} {c : Chain ℚ (TopCat.of M) k}
    (hc : c ∈ inside ℚ k (∅ : Set (TopCat.of M))) : c = 0 := by
  rw [← Finsupp.support_eq_empty]
  refine Finset.eq_empty_of_forall_notMem fun σ hσ ↦ ?_
  obtain ⟨y, hy⟩ := range_nonempty σ
  exact (Finsupp.mem_supported ℚ c).1 hc hσ hy

/-- **Detection of Borel–Moore classes by compactly supported cocycles.** A locally finite cycle
pairing to zero with every relative cocycle of every `(M, M - K)`, `K` compact, is a boundary:
it is `β ∩ z` by Poincaré duality, and `β` vanishes on every finite cycle `c`, since `c` is,
against cocycles, a cap product `φ ∩ z` with `φ` compactly supported, and
`⟨β, φ ∩ z⟩ = ± ⟨φ, β ∩ z⟩`. -/
private theorem mk_eq_zero_of_localPairing_eq_zero [LocallyCompactSpace M]
    (z : Cyc (R := ℚ) (TopCat.of M) n) (hD : DualityAt (TopCat.of M) n z)
    (hDU : ∀ U : Opens (TopCat.of M), DualityAt (TopCat.of U) n (resCycOpen ℚ U z))
    {i j : ℕ} (hij : i + j = n) (w : Cyc (R := ℚ) (TopCat.of M) i)
    (hw : ∀ (K : Set (TopCat.of M)) (_ : IsCompact K) (φ : relCocycles ℚ Kᶜ i),
      localPairing (coeff ℚ w.1) φ.1 = 0) :
    (Submodule.Quotient.mk w : HomQ (R := ℚ) (TopCat.of M) i) = 0 := by
  have h2 : j + i = n := by omega
  obtain ⟨cl, hcl⟩ := (hD.1 j i h2).2 (Submodule.Quotient.mk w)
  obtain ⟨β, rfl⟩ := Submodule.Quotient.mk_surjective _ cl
  have hbz : (Submodule.Quotient.mk ⟨capChain ℚ j i n h2 β.1 z.1,
      capChain_mem_cyc _ j i n h2 β z⟩ : HomQ (R := ℚ) (TopCat.of M) i) =
        Submodule.Quotient.mk w := (capHomQ_mk _ j i n h2 β z).symm.trans hcl
  have key : ∀ c : Chain ℚ (TopCat.of M) j, ofFinsupp c ∈ Cyc (R := ℚ) (TopCat.of M) j →
      SingularCochain.eval β.1 c = 0 := by
    intro c hc
    obtain ⟨K, hK, φ, hφ⟩ := exists_eval_eq_localPairing_capChain z hD hDU hij c hc
    rw [hφ β.1 β.2, localPairing_capChain_right hij h2 β.1 z.1 hK φ.2.1,
      localPairing_cup_comm hij h2 z hK φ.2 β.2, ← localPairing_capChain h2 hij β.1 z.1 hK φ.2.1]
    change (-1 : ℚ) ^ (i * j) * localPairing (coeff ℚ (⟨capChain ℚ j i n h2 β.1 z.1,
      capChain_mem_cyc _ j i n h2 β z⟩ : Cyc (R := ℚ) (TopCat.of M) i).1) φ.1 = 0
    rw [localPairing_cyc_eq hK φ hbz, hw K hK φ, mul_zero]
  have hβ0 : (Submodule.Quotient.mk β : relCohomology ℚ (∅ : Set (TopCat.of M)) j) = 0 := by
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    rcases j with _ | j'
    · change β.1 = 0
      funext σ
      have := key (Finsupp.single σ 1) (mem_cyc_zero _)
      rwa [SingularCochain.eval, Finsupp.linearCombination_single, one_smul] at this
    · refine mem_relCoboundaries_of_eval_eq_zero_rat _ j' fun c hc ↦ key c ?_
      rw [mem_cyc_iff]
      change ((BM ℚ (TopCat.of M)).d (j' + 1) j').hom (ofFinsupp c) = 0
      rw [d_ofFinsupp, eq_zero_of_mem_inside_empty hc]
      rfl
  rw [← hcl]
  change capHomQ ℚ (∅ : Set (TopCat.of M)) j i n h2 (Submodule.Quotient.mk β)
    (Submodule.Quotient.mk z) = 0
  rw [hβ0, map_zero]
  rfl

/-- Evaluation on locally finite cycles against a relative cocycle of `(M, M - K)`, `K` compact,
as a functional on Borel–Moore homology. -/
private def evalFunctional {i : ℕ} {K : Set (TopCat.of M)} (hK : IsCompact K)
    (φ : relCocycles ℚ Kᶜ i) : HomQ (R := ℚ) (TopCat.of M) i →ₗ[ℚ] ℚ :=
  (LinearMap.range ((BM ℚ (TopCat.of M)).sc i).moduleCatToCycles).liftQ
    { toFun := fun w ↦ localPairing (coeff ℚ w.1) φ.1
      map_add' := fun w w' ↦ localPairing_add_left w.1.2 w'.1.2 hK φ.2.1
      map_smul' := fun r w ↦ localPairing_smul_left w.1.2 hK φ.2.1 r }
    fun w hw ↦ by
      change localPairing (coeff ℚ w.1) φ.1 = 0
      have h0 : (Submodule.Quotient.mk w : HomQ (R := ℚ) (TopCat.of M) i) =
          Submodule.Quotient.mk 0 := by
        rw [Submodule.Quotient.mk_zero]
        exact (Submodule.Quotient.mk_eq_zero _).2 hw
      rw [localPairing_cyc_eq hK φ h0]
      exact finsum_eq_zero_of_forall_eq_zero fun σ ↦ zero_mul _

/-- **Universal coefficients for compactly supported cohomology and Borel–Moore homology** over
`ℚ`, for a manifold with a finite good cover, in degrees `i ≤ n`. The evaluation pairing
`H^i_c(M; ℚ) × H^{BM}_i(M; ℚ) → ℚ`, `([φ], [w]) ↦ ⟨φ, w⟩`, is perfect: a relative cocycle of
`(M, M - K)` pairing to zero with every locally finite cycle is a relative coboundary of
`(M, M - K')` for a larger compact `K'`, and every functional on `H^{BM}_i(M; ℚ)` is the pairing
with a relative cocycle of some `(M, M - K)`. The first half comes from Poincaré duality on `M`
and on the complements of compact sets; the second from the detection of Borel–Moore classes by
compactly supported cocycles, as `H^{BM}_i(M; ℚ) ≅ H^j(M; ℚ)` is finite dimensional. -/
private theorem pairing_perfect_of_goodCover_of_le (b : Module.Basis (Fin n) ℝ H)
    (μ : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of M) n)
    (hμ : IsFundamentalClass ℚ b μ)
    {ι : Type} [Finite ι] (𝒰 : ι → Opens M) (h𝒰 : ⨆ i, 𝒰 i = ⊤)
    (hball : ∀ s : Finset ι, s.Nonempty → (⋂ i ∈ s, (𝒰 i : Set M)).Nonempty →
      Nonempty ((⋂ i ∈ s, (𝒰 i : Set M)) ≃ₜ EuclideanSpace ℝ (Fin n))) (i : ℕ) (hi : i ≤ n) :
    (∀ (K : Compacts M) (φ : relCocycles ℚ ((K : Set M)ᶜ : Set (TopCat.of M)) i),
      (∀ w : Cyc (R := ℚ) (TopCat.of M) i, localPairing (coeff ℚ w.1) φ.1 = 0) →
      ∃ K' : Compacts M, K ≤ K' ∧ φ.1 ∈ relCoboundaries ℚ ((K' : Set M)ᶜ : Set (TopCat.of M)) i) ∧
    ∀ g : HomQ (R := ℚ) (TopCat.of M) i →ₗ[ℚ] ℚ, ∃ (K : Compacts M)
      (φ : relCocycles ℚ ((K : Set M)ᶜ : Set (TopCat.of M)) i),
      ∀ w : Cyc (R := ℚ) (TopCat.of M) i,
        localPairing (coeff ℚ w.1) φ.1 = g (Submodule.Quotient.mk w) := by
  have := secondCountableTopology_of_goodCover 𝒰 h𝒰 hball
  have : LocallyCompactSpace H :=
    (SingularChain.basisHomeomorph b).isOpenEmbedding.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  set z := cycOf μ
  have hD := PoincareAlexander.dualityAt_of_isFundamentalClass b μ hμ z
    (homologyEquiv_eq_mk_cycOf μ)
  have hDU := PoincareAlexander.dualityAt_resCycOpen_of_isFundamentalClass b μ hμ z
    (homologyEquiv_eq_mk_cycOf μ)
  refine ⟨fun K φ hφ ↦ ?_, fun g ↦ ?_⟩
  · obtain ⟨K', hK', hKK', hφ'⟩ :=
      exists_relCoboundaries_of_localPairing_eq_zero z hD hDU hi K.isCompact φ hφ
    exact ⟨⟨K', hK'⟩, hKK', hφ'⟩
  obtain ⟨j, rfl⟩ : ∃ j, n = i + j := ⟨n - i, by omega⟩
  -- `H^{BM}_i(M)` is finite dimensional
  have hFDc : FiniteDimensional ℚ (relCohomology ℚ (∅ : Set (TopCat.of M)) j) := by
    have h1 := finiteDimensional_cohomology_of_goodCover 𝒰 h𝒰 hball (j : ℤ)
    have h2 := LinearEquiv.finiteDimensional
      (relativeSingularCohomologyEquiv ℚ (Set.univᶜ : Set (TopCat.of M)) j)
    rw [Set.compl_univ] at h2
    exact h2
  have hFD : FiniteDimensional ℚ (HomQ (R := ℚ) (TopCat.of M) i) :=
    LinearEquiv.finiteDimensional (LinearEquiv.ofBijective
      ((capHomQ ℚ (∅ : Set (TopCat.of M)) j i (i + j) (by omega)).flip
        (Submodule.Quotient.mk z)) (hD.1 j i (by omega)))
  -- the functionals given by compactly supported cocycles
  let W : Submodule ℚ (Module.Dual ℚ (HomQ (R := ℚ) (TopCat.of M) i)) :=
    { carrier := {f | ∃ (K : Compacts M) (φ : relCocycles ℚ ((K : Set M)ᶜ : Set (TopCat.of M)) i),
        ∀ w : Cyc (R := ℚ) (TopCat.of M) i,
          localPairing (coeff ℚ w.1) φ.1 = f (Submodule.Quotient.mk w)}
      add_mem' := by
        rintro f f' ⟨K, φ, hφ⟩ ⟨K', φ', hφ'⟩
        have hs : ((K ⊔ K' : Compacts M) : Set M)ᶜ ⊆ (K : Set M)ᶜ :=
          compl_subset_compl.2 (by rw [Compacts.coe_sup]; exact subset_union_left)
        have hs' : ((K ⊔ K' : Compacts M) : Set M)ᶜ ⊆ (K' : Set M)ᶜ :=
          compl_subset_compl.2 (by rw [Compacts.coe_sup]; exact subset_union_right)
        refine ⟨K ⊔ K', ⟨φ.1 + φ'.1, add_mem (vanishing_anti hs φ.2.1) (vanishing_anti hs' φ'.2.1),
          LinearMap.mem_ker.2 (by rw [map_add, LinearMap.mem_ker.1 φ.2.2,
            LinearMap.mem_ker.1 φ'.2.2, add_zero])⟩, fun w ↦ ?_⟩
        change localPairing w.1.1 (φ.1 + φ'.1) = _
        rw [localPairing_add_right w.1.2 (K ⊔ K').isCompact (vanishing_anti hs φ.2.1)
          (vanishing_anti hs' φ'.2.1)]
        exact congrArg₂ (· + ·) (hφ w) (hφ' w)
      zero_mem' := ⟨⊥, 0, fun w ↦ localPairing_zero_right _⟩
      smul_mem' := by
        rintro r f ⟨K, φ, hφ⟩
        refine ⟨K, r • φ, fun w ↦ ?_⟩
        change localPairing w.1.1 (r • φ.1) = _
        rw [localPairing_smul_right w.1.2 K.isCompact φ.2.1]
        exact congrArg (r * ·) (hφ w) }
  have hW : W.dualCoannihilator = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun v hv ↦ ?_
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    refine mk_eq_zero_of_localPairing_eq_zero z hD hDU rfl w fun K hK φ ↦ ?_
    exact (Submodule.mem_dualCoannihilator _).1 hv (evalFunctional hK φ)
      ⟨⟨K, hK⟩, φ, fun w' ↦ rfl⟩
  have hWtop : W = ⊤ := by
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := W), hW,
      Submodule.dualAnnihilator_bot]
  exact (hWtop ▸ Submodule.mem_top : g ∈ W)

/-- **Universal coefficients for compactly supported cohomology and Borel–Moore homology** over
`ℚ`: the evaluation pairing `H^i_c(M; ℚ) × H^{BM}_i(M; ℚ) → ℚ` is perfect. Above the dimension
both groups vanish. -/
private theorem pairing_perfect_of_goodCover (b : Module.Basis (Fin n) ℝ H)
    (μ : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of M) n)
    (hμ : IsFundamentalClass ℚ b μ)
    {ι : Type} [Finite ι] (𝒰 : ι → Opens M) (h𝒰 : ⨆ i, 𝒰 i = ⊤)
    (hball : ∀ s : Finset ι, s.Nonempty → (⋂ i ∈ s, (𝒰 i : Set M)).Nonempty →
      Nonempty ((⋂ i ∈ s, (𝒰 i : Set M)) ≃ₜ EuclideanSpace ℝ (Fin n))) (i : ℕ) :
    (∀ (K : Compacts M) (φ : relCocycles ℚ ((K : Set M)ᶜ : Set (TopCat.of M)) i),
      (∀ w : Cyc (R := ℚ) (TopCat.of M) i, localPairing (coeff ℚ w.1) φ.1 = 0) →
      ∃ K' : Compacts M, K ≤ K' ∧ φ.1 ∈ relCoboundaries ℚ ((K' : Set M)ᶜ : Set (TopCat.of M)) i) ∧
    ∀ g : HomQ (R := ℚ) (TopCat.of M) i →ₗ[ℚ] ℚ, ∃ (K : Compacts M)
      (φ : relCocycles ℚ ((K : Set M)ᶜ : Set (TopCat.of M)) i),
      ∀ w : Cyc (R := ℚ) (TopCat.of M) i,
        localPairing (coeff ℚ w.1) φ.1 = g (Submodule.Quotient.mk w) := by
  rcases le_or_gt i n with hi | hi
  · exact pairing_perfect_of_goodCover_of_le b μ hμ 𝒰 h𝒰 hball i hi
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  refine ⟨fun K φ _ ↦ ⟨K, le_rfl, mem_relCoboundaries_of_dim_le b K.isCompact (by omega) φ⟩,
    fun g ↦ ⟨⊥, 0, fun w ↦ ?_⟩⟩
  have := secondCountableTopology_of_goodCover 𝒰 h𝒰 hball
  have h0 := (PoincareAlexander.dualityAt_of_isFundamentalClass b μ hμ (cycOf μ)
    (homologyEquiv_eq_mk_cycOf μ)).2.2 (k + 1) hi
  rw [@Subsingleton.elim _ h0 (Submodule.Quotient.mk w) 0, map_zero]
  exact localPairing_zero_right _

/-- **The trace of a cup product is a cap product pairing**: `τ_K(a ∪ β) = ⟨a, β ∩ z⟩`. -/
private lemma trace_cup_eq_capChain (μ : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of M) n)
    (K : Compacts M) (p q : ℕ) (hij : (p : ℤ) + (q : ℤ) = (n : ℤ)) (h : q + p = n)
    (φ : relCocycles ℚ ((K : Set M)ᶜ : Set (TopCat.of M)) p)
    (ψ : relCocycles ℚ (Set.univᶜ : Set (TopCat.of M)) q) (ψ₀ : Simplex (TopCat.of M) q → ℚ)
    (hψ : ψ.1 = ψ₀) :
    trace μ K (cohomologyWithSupports.congrIndex ℚ (TopCat.of M) (by rw [Set.inter_univ]) hij
      (cohomologyWithSupports.cup ℚ (TopCat.of M) K.isCompact.isClosed isClosed_univ p q
        ((relativeSingularCohomologyEquiv ℚ _ p).symm (Submodule.Quotient.mk φ))
        ((relativeSingularCohomologyEquiv ℚ _ q).symm (Submodule.Quotient.mk ψ)))) =
      localPairing (coeff ℚ (capChain ℚ q p n h ψ₀ (cycOf μ).1)) φ.1 := by
  rw [trace_cup μ K p q hij φ ψ _ (exists_cycle μ).choose_spec,
    localPairing_capChain h (by omega) ψ₀ _ K.isCompact φ.2.1, hψ]
  exact congrArg (localPairing · _)
    (congrArg Subtype.val (coe_moduleCatCyclesIso_hom (R := ℚ) _)).symm

/-- **Poincaré duality**: `H^i_c(M; ℚ) → H^j(M; ℚ)^*` is injective and surjective for the trace
pairing, from Poincaré duality `H^j(M) ≅ H^{BM}_i(M)` (`β ↦ β ∩ μ`), the adjunction
`τ_K(a ∪ β) = ⟨a, β ∩ z⟩`, and the perfectness of the evaluation pairing. -/
private theorem trace_cup_perfect_of_goodCover (b : Module.Basis (Fin n) ℝ H)
    (μ : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of M) n)
    (hμ : IsFundamentalClass ℚ b μ)
    {ι : Type} [Finite ι] (𝒰 : ι → Opens M) (h𝒰 : ⨆ i, 𝒰 i = ⊤)
    (hball : ∀ s : Finset ι, s.Nonempty → (⋂ i ∈ s, (𝒰 i : Set M)).Nonempty →
      Nonempty ((⋂ i ∈ s, (𝒰 i : Set M)) ≃ₜ EuclideanSpace ℝ (Fin n)))
    (i j : ℤ) (hij : i + j = n) :
    (∀ (K : Compacts M)
        (a : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) (TopCat.of M) (K : Set M) i),
      (∀ β : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) (TopCat.of M) Set.univ j,
        trace μ K (cohomologyWithSupports.congrIndex ℚ (TopCat.of M)
          (by rw [Set.inter_univ]) hij
          (cohomologyWithSupports.cup ℚ (TopCat.of M) K.isCompact.isClosed isClosed_univ
            i j a β)) = 0) →
      ∃ (K' : Compacts M) (hKK' : K ≤ K'),
        (relativeSingularCohomology.map ℚ (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of M))
          (A := ((K : Set M)ᶜ : Set (TopCat.of M)))
          (A' := ((K' : Set M)ᶜ : Set (TopCat.of M)))
          (Set.compl_subset_compl.mpr hKK') i).hom a = 0) ∧
    ∀ f : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) (TopCat.of M) Set.univ j →ₗ[ℚ] ℚ,
      ∃ (K : Compacts M)
        (a : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) (TopCat.of M) (K : Set M) i),
        ∀ β, trace μ K (cohomologyWithSupports.congrIndex ℚ (TopCat.of M)
          (by rw [Set.inter_univ]) hij
          (cohomologyWithSupports.cup ℚ (TopCat.of M) K.isCompact.isClosed isClosed_univ
            i j a β)) = f β := by
  have := secondCountableTopology_of_goodCover 𝒰 h𝒰 hball
  have hD := PoincareAlexander.dualityAt_of_isFundamentalClass b μ hμ (cycOf μ)
    (homologyEquiv_eq_mk_cycOf μ)
  have hG := pairing_perfect_of_goodCover b μ hμ 𝒰 h𝒰 hball
  have hcu : (Set.univᶜ : Set (TopCat.of M)) = ∅ := Set.compl_univ
  have hrep : ∀ {A : Set (TopCat.of M)} {p : ℕ}
      (x : relativeSingularCohomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of M) A p),
      ∃ φ : relCocycles ℚ A p,
        x = (relativeSingularCohomologyEquiv ℚ A p).symm (Submodule.Quotient.mk φ) := by
    intro A p x
    obtain ⟨φ, hφ⟩ := Submodule.Quotient.mk_surjective _ (relativeSingularCohomologyEquiv ℚ A p x)
    exact ⟨φ, by rw [hφ, LinearEquiv.symm_apply_apply]⟩
  have hzero : ∀ f : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) (TopCat.of M) Set.univ j →ₗ[ℚ] ℚ,
      (∀ β, f β = 0) → ∃ (K : Compacts M)
        (a : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) (TopCat.of M) (K : Set M) i),
        ∀ β, trace μ K (cohomologyWithSupports.congrIndex ℚ (TopCat.of M)
          (by rw [Set.inter_univ]) hij
          (cohomologyWithSupports.cup ℚ (TopCat.of M) K.isCompact.isClosed isClosed_univ
            i j a β)) = f β := fun f hf ↦
    ⟨⊥, 0, fun β ↦ by rw [hf β, map_zero, LinearMap.zero_apply, map_zero, map_zero]⟩
  have hinj : ∀ (p : ℕ) (K : Compacts M) (φ : relCocycles ℚ ((K : Set M)ᶜ : Set (TopCat.of M)) p),
      (∀ w : Cyc (R := ℚ) (TopCat.of M) p, localPairing (coeff ℚ w.1) φ.1 = 0) →
      ∃ (K' : Compacts M) (hKK' : K ≤ K'),
        (relativeSingularCohomology.map ℚ (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of M))
          (A := ((K : Set M)ᶜ : Set (TopCat.of M)))
          (A' := ((K' : Set M)ᶜ : Set (TopCat.of M)))
          (Set.compl_subset_compl.mpr hKK') p).hom
            ((relativeSingularCohomologyEquiv ℚ _ p).symm (Submodule.Quotient.mk φ)) = 0 := by
    intro p K φ hφ
    obtain ⟨K', hKK', hK'⟩ := (hG p).1 K φ hφ
    exact ⟨K', hKK', map_eq_zero_of_mem_relCoboundaries _ φ hK'⟩
  rcases lt_or_ge i 0 with hi | hi
  · -- `i < 0`: `H^i_c = 0` and `H^j(M) = 0` for `j > n`.
    obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ j by omega)
    have hq : n < q := by omega
    refine ⟨fun K a _ ↦ ⟨K, le_rfl, ?_⟩, fun f ↦ hzero f fun β ↦ ?_⟩
    · have := ModuleCat.subsingleton_of_isZero
        (cohomologyWithSupports.isZero_relativeSingularCohomology_of_neg ℚ (TopCat.of M)
          ((K : Set M)ᶜ : Set (TopCat.of M)) hi)
      rw [Subsingleton.elim a 0, map_zero]
    · have h0 := hD.2.1 q hq
      rw [← hcu] at h0
      have : β = 0 := (relativeSingularCohomologyEquiv ℚ _ q).injective (Subsingleton.elim _ _)
      rw [this, map_zero]
  obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hi
  rcases lt_or_ge j 0 with hj | hj
  · -- `j < 0`: `H^j(M) = 0`, and `H^{BM}_p(M) = 0` for `p > n`.
    have hp : n < p := by omega
    refine ⟨fun K a _ ↦ ?_, fun f ↦ hzero f fun β ↦ ?_⟩
    · obtain ⟨φ, rfl⟩ := hrep a
      refine hinj p K φ fun w ↦ ?_
      have h0 := hD.2.2 p hp
      rw [localPairing_cyc_eq K.isCompact φ (@Subsingleton.elim _ h0 (Submodule.Quotient.mk w)
        (Submodule.Quotient.mk 0))]
      exact finsum_eq_zero_of_forall_eq_zero fun σ ↦ zero_mul _
    · have := ModuleCat.subsingleton_of_isZero
        (cohomologyWithSupports.isZero_relativeSingularCohomology_of_neg ℚ (TopCat.of M)
          (Set.univᶜ : Set (TopCat.of M)) hj)
      rw [Subsingleton.elim β 0, map_zero]
  obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hj
  have hpq : q + p = n := by omega
  have hmem : ∀ ψ : relCocycles ℚ (Set.univᶜ : Set (TopCat.of M)) q,
      ψ.1 ∈ relCocycles ℚ (∅ : Set (TopCat.of M)) q := fun ψ ↦ hcu ▸ ψ.2
  have hmem' : ∀ ψ : relCocycles ℚ (∅ : Set (TopCat.of M)) q,
      ψ.1 ∈ relCocycles ℚ (Set.univᶜ : Set (TopCat.of M)) q := fun ψ ↦ by rw [hcu]; exact ψ.2
  refine ⟨fun K a ha ↦ ?_, fun f ↦ ?_⟩
  · obtain ⟨φ, rfl⟩ := hrep a
    refine hinj p K φ fun w ↦ ?_
    obtain ⟨c, hc⟩ := (hD.1 q p hpq).2 (Submodule.Quotient.mk w)
    obtain ⟨ψ₀, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    have hc' : (Submodule.Quotient.mk ⟨_, capChain_mem_cyc (∅ : Set (TopCat.of M)) q p n hpq ψ₀
        (cycOf μ)⟩ : HomQ (R := ℚ) (TopCat.of M) p) = Submodule.Quotient.mk w := hc
    have h1 := ha ((relativeSingularCohomologyEquiv ℚ _ q).symm
      (Submodule.Quotient.mk ⟨ψ₀.1, hmem' ψ₀⟩))
    rw [trace_cup_eq_capChain μ K p q hij hpq φ _ ψ₀.1 rfl] at h1
    rwa [← localPairing_cyc_eq K.isCompact φ hc']
  · let T : relCohomology ℚ (∅ : Set (TopCat.of M)) q →ₗ[ℚ]
        cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) (TopCat.of M) Set.univ q :=
      (relativeSingularCohomologyEquiv ℚ (Set.univᶜ : Set (TopCat.of M)) q).symm.toLinearMap ∘ₗ
        relCohomologyMap ℚ (𝟙 (TopCat.of M)) (A := (∅ : Set (TopCat.of M)))
          (A' := (Set.univᶜ : Set (TopCat.of M))) (by rw [hcu]; exact subset_rfl) q
    let e := LinearEquiv.ofBijective
      ((capHomQ ℚ (∅ : Set (TopCat.of M)) q p n hpq).flip (Submodule.Quotient.mk (cycOf μ)))
      (hD.1 q p hpq)
    obtain ⟨K, φ, hφ⟩ := (hG p).2 ((f ∘ₗ T) ∘ₗ e.symm.toLinearMap)
    refine ⟨K, (relativeSingularCohomologyEquiv ℚ _ p).symm (Submodule.Quotient.mk φ),
      fun β ↦ ?_⟩
    obtain ⟨ψ, rfl⟩ := hrep β
    rw [trace_cup_eq_capChain μ K p q hij hpq φ ψ ψ.1 rfl]
    let ψ₀ : relCocycles ℚ (∅ : Set (TopCat.of M)) q := ⟨ψ.1, hmem ψ⟩
    rw [hφ ⟨_, capChain_mem_cyc (∅ : Set (TopCat.of M)) q p n hpq ψ₀ (cycOf μ)⟩]
    have he : e (Submodule.Quotient.mk ψ₀) = Submodule.Quotient.mk
        ⟨_, capChain_mem_cyc (∅ : Set (TopCat.of M)) q p n hpq ψ₀ (cycOf μ)⟩ := rfl
    have h2 := e.symm_apply_eq.2 he.symm
    change f (T (e.symm _)) = _
    exact (congrArg (fun x ↦ f (T x)) h2).trans rfl

end Perfect

/-- **Poincaré duality for an oriented manifold with a finite good cover.** Let `M` be a real
`n`-manifold, oriented by the fundamental class `μ`, with a finite open cover `𝒰` in which every
nonempty finite intersection is homeomorphic to `ℝⁿ`. Then there are trace maps
`τ_K : H^n(M, M - K; ℚ) → ℚ`, one for each compact `K`. Each is given by evaluating a relative
cocycle on a locally finite cycle representing `μ`, and each takes the value `1` on the local
orientation class at every point. For `i + j = n` the trace of the cup product is a perfect
pairing between `H^i_c(M; ℚ) = colim_K H^i(M, M - K; ℚ)` and `H^j(M; ℚ)`. -/
@[mmp "lem_mmp_finite_ball_cover_duality"]
public theorem exists_trace_cup_perfect_of_finite_good_cover
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace H M] {n : ℕ} (b : Module.Basis (Fin n) ℝ H)
    (μ : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of M) n)
    (hμ : IsFundamentalClass ℚ b μ)
    {ι : Type} [Finite ι] (𝒰 : ι → Opens M) (h𝒰 : ⨆ i, 𝒰 i = ⊤)
    (hball : ∀ s : Finset ι, s.Nonempty → (⋂ i ∈ s, (𝒰 i : Set M)).Nonempty →
      Nonempty ((⋂ i ∈ s, (𝒰 i : Set M)) ≃ₜ EuclideanSpace ℝ (Fin n))) :
    ∃ τ : (K : Compacts M) →
        cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) (TopCat.of M) (K : Set M) n →ₗ[ℚ] ℚ,
      -- the trace is evaluation on a locally finite cycle representing `μ`
      (∀ (K : Compacts M) (φ : relCocycles ℚ ((K : Set M)ᶜ : Set (TopCat.of M)) n)
        (z : (borelMooreChainComplex ℚ (ModuleCat.of ℚ ℚ) (TopCat.of M)).cycles n),
        (borelMooreChainComplex ℚ (ModuleCat.of ℚ ℚ) (TopCat.of M)).homologyπ n z =
            (borelMooreHomologyIsoOfNat ℚ (ModuleCat.of ℚ ℚ) (TopCat.of M) n).hom μ →
          τ K ((relativeSingularCohomologyEquiv ℚ ((K : Set M)ᶜ : Set (TopCat.of M)) n).symm
              (Submodule.Quotient.mk φ)) =
            localPairing
              (((borelMooreChainComplex ℚ (ModuleCat.of ℚ ℚ) (TopCat.of M)).iCycles n z).1)
              (φ : Simplex (TopCat.of M) n → ℚ)) ∧
      -- the trace of the local orientation class at every point is `1`
      (∀ (y : M) (α : Simplex (TopCat.of M) n → ℚ)
        (hα : IsChartOrientedCocycle ℚ b (y : TopCat.of M) α),
        τ ⟨{y}, isCompact_singleton⟩
            ((relativeSingularCohomologyEquiv ℚ (({y} : Set M)ᶜ : Set (TopCat.of M)) n).symm
              (Submodule.Quotient.mk ⟨α, hα.1⟩)) = 1) ∧
      -- perfectness of the cup product pairing in complementary degrees
      ∀ (i j : ℤ) (hij : i + j = n),
        FiniteDimensional ℚ
            (cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) (TopCat.of M) Set.univ j) ∧
        (∀ (K : Compacts M)
            (a : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) (TopCat.of M) (K : Set M) i),
          (∀ β : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) (TopCat.of M) Set.univ j,
            τ K (cohomologyWithSupports.congrIndex ℚ (TopCat.of M)
              (by rw [Set.inter_univ]) hij
              (cohomologyWithSupports.cup ℚ (TopCat.of M) K.isCompact.isClosed isClosed_univ
                i j a β)) = 0) →
          ∃ (K' : Compacts M) (hKK' : K ≤ K'),
            (relativeSingularCohomology.map ℚ (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of M))
              (A := ((K : Set M)ᶜ : Set (TopCat.of M)))
              (A' := ((K' : Set M)ᶜ : Set (TopCat.of M)))
              (Set.compl_subset_compl.mpr hKK') i).hom a = 0) ∧
        ∀ f : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) (TopCat.of M) Set.univ j →ₗ[ℚ] ℚ,
          ∃ (K : Compacts M)
            (a : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) (TopCat.of M) (K : Set M) i),
            ∀ β, τ K (cohomologyWithSupports.congrIndex ℚ (TopCat.of M)
              (by rw [Set.inter_univ]) hij
              (cohomologyWithSupports.cup ℚ (TopCat.of M) K.isCompact.isClosed isClosed_univ
                i j a β)) = f β :=
  ⟨trace μ, fun K φ z hz ↦ trace_mk μ K φ z hz, trace_chartOriented b hμ, fun i j hij ↦
    ⟨finiteDimensional_cohomology_of_goodCover 𝒰 h𝒰 hball j,
      trace_cup_perfect_of_goodCover b μ hμ 𝒰 h𝒰 hball i j hij⟩⟩

end MMP.Analytic

end

/-! ### Zariski sequences of smooth-centre blow-ups -/

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP MMP.Flips MMP.Mori
open scoped WithZero

universe u v

namespace MMP.Flips

/-- A valuation `ν'` of `k(X')` is a divisor of `k(X')` if its restriction `ν` along a morphism
`f : X' ⟶ X` inducing an isomorphism of function fields is a divisor of `k(X)`. -/
private theorem isDivisorOfFunctionField_of_comap {k : Type v} [Field k] {X X' : Scheme.{v}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsIntegral X'] (f : X' ⟶ X) [IsDominant f]
    (hf : Function.Bijective (functionFieldMap f)) {ν : Valuation X.functionField ℤᵐ⁰}
    {ν' : Valuation X'.functionField ℤᵐ⁰} (hν : ν'.comap (functionFieldMap f) = ν)
    (h : IsDivisorOfFunctionField k sX ν) : IsDivisorOfFunctionField k (f ≫ sX) ν' := by
  let := functionFieldAlgebra sX
  obtain ⟨Y, sY, hY, E, e, he⟩ := h
  let := functionFieldAlgebra (f ≫ sX)
  have : IsIntegral Y := hY.1.toIsIntegral
  have : IsNormal Y := hY.2
  have : IsLocallyNoetherian Y :=
    have := hY.1.toLocallyOfFiniteType
    LocallyOfFiniteType.isLocallyNoetherian sY
  let := functionFieldAlgebra sY
  refine ⟨Y, sY, hY, E, (functionFieldAlgEquiv sX f hf).symm.trans e, ?_⟩
  ext a
  obtain ⟨b, rfl⟩ := hf.2 a
  have h1 := congrArg (fun w : Valuation X.functionField ℤᵐ⁰ => w b) he
  have h2 := congrArg (fun w : Valuation X.functionField ℤᵐ⁰ => w b) hν
  simp only [Valuation.comap_apply] at h1 h2 ⊢
  rw [h2, h1]
  change _ = E.divisorialValuation (e ((functionFieldAlgEquiv sX f hf).symm _))
  rw [show (functionFieldAlgEquiv sX f hf).symm (functionFieldMap f b) = b from
    (functionFieldAlgEquiv sX f hf).symm_apply_apply b]
  rfl

/-- The blow-up of an open `U ⊆ X` of an integral scheme in an ideal sheaf whose support is not
all of `U` induces an isomorphism of function fields `k(X) ≅ k(Bl U)`. -/
private theorem functionFieldMap_bijective_blowUp {X : Scheme.{v}} [IsIntegral X] (U : X.Opens)
    (I : (U : Scheme.{v}).IdealSheafData) [IsIntegral (blowUp I)]
    [IsDominant (blowUpToBase I ≫ U.ι)] (hI : (I.support : Set U) ≠ Set.univ) :
    Function.Bijective (functionFieldMap (blowUpToBase I ≫ U.ι)) := by
  obtain ⟨u, hu⟩ := (Set.ne_univ_iff_exists_notMem _).1 hI
  let W := (blowUpToBase I) ⁻¹ᵁ I.support.compl
  have hW : (W : Set (blowUp I)).Nonempty :=
    ⟨_, ((asIso (blowUpToBase I ∣_ I.support.compl)).inv ⟨u, hu⟩).2⟩
  have : IsOpenImmersion (W.ι ≫ blowUpToBase I ≫ U.ι) := by
    rw [← Category.assoc, ← morphismRestrict_ι]
    infer_instance
  exact functionFieldMap_bijective_of_isOpenImmersion _ W hW

/-- The image of the generic point of `E` is the generic point of the center of a divisor
`(Y, f, E)` over `X`. -/
private theorem isGenericPoint_center {k : Type v} [Field k] {X : Scheme.{v}}
    {sX : X ⟶ Spec (.of k)} (D : ProperDivisorOver k sX) :
    IsGenericPoint (D.f D.E.genericPoint) (D.center : Set X) := by
  have := D.isProper
  rw [IsGenericPoint, ProperDivisorOver.coe_center,
    AlgebraicGeometry.PrimeDivisor.support_eq_closure D.E,
    ← D.f.isClosedMap.closure_image_eq_of_continuous D.f.continuous, Set.image_singleton]

/-- The center of a divisor over an integral scheme `X` does not contain the generic point of
`X`: the valuation is nontrivial, so it does not dominate `𝒪_{X,η} = k(X)`. -/
private theorem genericPoint_notMem_center {k : Type v} [Field k] {X : Scheme.{v}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] (D : ProperDivisorOver k sX) :
    genericPoint X ∉ (D.center : Set X) := by
  intro h
  have hx : genericPoint X = D.f D.E.genericPoint := by
    refine (genericPoint_spec X).eq ?_
    rw [IsGenericPoint, (isGenericPoint_center D).def]
    refine Set.eq_univ_of_univ_subset ?_
    rw [← (genericPoint_spec X).def]
    exact (D.center.isClosed.closure_subset_iff).2 (Set.singleton_subset_iff.2 h)
  obtain ⟨g, hg⟩ := MMP.Positivity.DivisorOver.exists_valuation_eq_exp_neg_one D.toDivisorOver
  obtain ⟨b, hb⟩ : ∃ b : X.presheaf.stalk (genericPoint X),
      @algebraMap _ X.functionField _ _ (stalkFunctionFieldAlgebra X (genericPoint X)) b = g⁻¹ :=
    ⟨g⁻¹, by
      rw [RingHom.algebraMap_toAlgebra, TopCat.Presheaf.stalkSpecializes_refl]
      rfl⟩
  have h1 := MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D.toDivisorOver _ hx b
  have h3 : D.valuation g⁻¹ ≤ 1 := by
    convert h1 using 2
    exact hb.symm
  rw [map_inv₀, hg] at h3
  exact absurd h3 (by simp)

/-- Two ring maps out of a stalk `𝒪_{X,x}` agree once they induce the same morphism through
`Spec 𝒪_{X,x} ⟶ X`: on an affine neighbourhood, `Spec 𝒪_{X,x} ⟶ X` is `Spec` of the germ map
followed by an open immersion. -/
private theorem stalk_hom_ext_of_SpecMap {X : Scheme.{v}} {x : X} {A : CommRingCat.{v}}
    (φ φ' : X.presheaf.stalk x ⟶ A)
    (h : Spec.map φ ≫ X.fromSpecStalk x = Spec.map φ' ≫ X.fromSpecStalk x) : φ = φ' := by
  refine TopCat.Presheaf.stalk_hom_ext _ fun U hxU => ?_
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU U.2
  rw [← hW.fromSpecStalk_eq_fromSpecStalk hxW] at h
  change Spec.map φ ≫ Spec.map (X.presheaf.germ _ x hxW) ≫ hW.fromSpec =
    Spec.map φ' ≫ Spec.map (X.presheaf.germ _ x hxW) ≫ hW.fromSpec at h
  rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc] at h
  have : IsOpenImmersion hW.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec hW
  have : Mono hW.fromSpec := IsOpenImmersion.mono _
  have h' := Spec.map_injective ((cancel_mono hW.fromSpec).1 h)
  rw [← X.presheaf.germ_res (homOfLE hWU) x hxW, Category.assoc, Category.assoc, h']

/-- **Lifting the center along a blow-up.** If the restriction `ν` of a valuation `ν'` of the
function field of the blow-up `Bl U` of an open `U ⊆ X` dominates the local ring of a point
`x ∈ U`, then `ν'` dominates the local ring of some point of `Bl U` (valuative criterion of
properness for `Bl U ⟶ U`). -/
private theorem exists_dominated_point_blowUp {X : Scheme.{v}} [IsIntegral X]
    [IsLocallyNoetherian X] (U : X.Opens) (I : (U : Scheme.{v}).IdealSheafData)
    [IsIntegral (blowUp I)] [IsDominant (blowUpToBase I ≫ U.ι)]
    (ν' : Valuation (blowUp I).functionField ℤᵐ⁰) (x : X) (hxU : x ∈ U)
    (h1 : ∀ a : X.presheaf.stalk x,
      ν'.comap (functionFieldMap (blowUpToBase I ≫ U.ι)) (algebraMap _ X.functionField a) ≤ 1)
    (h2 : ∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x),
      ν'.comap (functionFieldMap (blowUpToBase I ≫ U.ι)) (algebraMap _ X.functionField a) < 1) :
    ∃ x' : blowUp I, (∀ a : (blowUp I).presheaf.stalk x',
        ν' (algebraMap _ (blowUp I).functionField a) ≤ 1) ∧
      ∀ a ∈ IsLocalRing.maximalIdeal ((blowUp I).presheaf.stalk x'),
        ν' (algebraMap _ (blowUp I).functionField a) < 1 := by
  let g := blowUpToBase I ≫ U.ι
  let R := ν'.valuationSubring
  let K := (blowUp I).functionField
  let ψ : X.presheaf.stalk x →+* R :=
    ((functionFieldMap g).comp (algebraMap (X.presheaf.stalk x) X.functionField)).codRestrict R
      fun a => (ν'.mem_valuationSubring_iff _).2 (h1 a)
  have hψ : IsLocalHom ψ := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have hlt := h2 a ((IsLocalRing.mem_maximalIdeal _).2 hna)
    obtain ⟨b, hb⟩ := ha.exists_right_inv
    have hb' : functionFieldMap g (algebraMap _ X.functionField a) * (b : K) = 1 :=
      congrArg Subtype.val hb
    have := mul_lt_one_of_lt_of_le hlt ((ν'.mem_valuationSubring_iff _).1 b.2)
    rw [Valuation.comap_apply, ← map_mul, hb', map_one] at this
    exact lt_irrefl _ this
  let i₂X : Spec (.of R) ⟶ X := Spec.map (CommRingCat.ofHom ψ) ≫ X.fromSpecStalk x
  have hrange : Set.range i₂X ⊆ Set.range U.ι := by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hsp : X.fromSpecStalk x (Spec.map (CommRingCat.ofHom ψ) p) ⤳ x := by
      have := Set.mem_range_self (f := X.fromSpecStalk x) (Spec.map (CommRingCat.ofHom ψ) p)
      rwa [Scheme.range_fromSpecStalk] at this
    exact hsp.mem_open U.isOpen hxU
  let i₂ : Spec (.of R) ⟶ U := IsOpenImmersion.lift U.ι i₂X hrange
  have hi₂ : i₂ ≫ U.ι = i₂X := IsOpenImmersion.lift_fac _ _ _
  have hX : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
  have hη : g (genericPoint (blowUp I)) ⤳ genericPoint X :=
    (Inseparable.of_eq (map_genericPoint_of_isDominant g)).specializes
  have hsq : (blowUp I).fromSpecStalk (genericPoint _) ≫ blowUpToBase I =
      Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ i₂ := by
    rw [← cancel_mono U.ι, Category.assoc, Category.assoc, hi₂]
    change _ ≫ g = _
    rw [← Scheme.SpecMap_stalkMap_fromSpecStalk g,
      ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk (hη.trans hX), ← Spec.map_comp_assoc,
      ← Spec.map_comp_assoc]
    congr 2
    rw [← TopCat.Presheaf.stalkSpecializes_comp X.presheaf hη hX]
    ext a
    rfl
  have hex : ValuativeCriterion.Existence (blowUpToBase I) := by
    have h : IsProper (blowUpToBase I) := inferInstance
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1.existence
  let S : ValuativeCommSq (blowUpToBase I) :=
    { R := R
      K := K
      i₁ := (blowUp I).fromSpecStalk (genericPoint _)
      i₂ := i₂
      commSq := ⟨hsq⟩ }
  obtain ⟨⟨l, hl₁, -⟩⟩ := (hex S).exists_lift
  have hl₁' : Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ l =
      (blowUp I).fromSpecStalk (genericPoint _) := hl₁
  set x' := l (IsLocalRing.closedPoint R)
  have hgx' : genericPoint (blowUp I) ⤳ x' := (genericPoint_spec _).specializes trivial
  have key : Scheme.stalkClosedPointTo l ≫ CommRingCat.ofHom (algebraMap R K) =
      (blowUp I).presheaf.stalkSpecializes hgx' := by
    apply stalk_hom_ext_of_SpecMap
    rw [Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Spec.map_comp_assoc,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk, hl₁']
  have hval : ∀ a : (blowUp I).presheaf.stalk x',
      algebraMap _ (blowUp I).functionField a =
        ((Scheme.stalkClosedPointTo l).hom a : K) := fun a =>
    (congrArg (fun φ => φ.hom a) key).symm
  refine ⟨x', fun a => ?_, fun a ha => ?_⟩
  · rw [hval]
    exact (ν'.mem_valuationSubring_iff _).1 ((Scheme.stalkClosedPointTo l).hom a).2
  · rw [hval]
    set r := (Scheme.stalkClosedPointTo l).hom a
    have hr : r ∈ IsLocalRing.maximalIdeal R :=
      map_nonunit (Scheme.stalkClosedPointTo l).hom a ha
    refine lt_of_le_of_ne ((ν'.mem_valuationSubring_iff _).1 r.2) fun h1r => hr ?_
    have hr0 : (r : K) ≠ 0 := fun h0 => by simp [h0] at h1r
    refine isUnit_iff_exists_inv.2 ⟨⟨(r : K)⁻¹, (ν'.mem_valuationSubring_iff _).2 ?_⟩, ?_⟩
    · rw [map_inv₀, h1r, inv_one]
    · exact Subtype.ext (mul_inv_cancel₀ hr0)

/-- One blow-up step keeps a nonempty center: if `ν` has nonempty center on `X`, `U ⊆ X` is an
open containing the generic point of the center `Z` with `Z ∩ U` smooth, and `X' = Bl_{Z ∩ U} U`,
then the valuation `ν'` of `k(X')` with `ν' ∘ β^* = ν` has nonempty center on `X'`. -/
private theorem hasNonemptyCenter_blowUp {k : Type v} [Field k]
    {X X' : Scheme.{v}} (sX : X ⟶ Spec (.of k)) (sX' : X' ⟶ Spec (.of k))
    [IsIntegral X] [IsIntegral X']
    (hvar : Mori.IsVariety k sX) (hvar' : Mori.IsVariety k sX')
    (hsm : IsSmoothScheme sX) (hsm' : IsSmoothScheme sX')
    (ν : Valuation X.functionField ℤᵐ⁰) (ν' : Valuation X'.functionField ℤᵐ⁰)
    (hν₀ : HasNonemptyCenter k sX ν)
    (U : X.Opens) (I : (U : Scheme.{v}).IdealSheafData)
    (hY : X' = blowUp I) (β : X' ⟶ X)
    (hβ : β = eqToHom hY ≫ blowUpToBase I ≫ U.ι)
    (hs : sX' = β ≫ sX) [IsDominant β]
    (hν : ν'.comap (functionFieldMap β) = ν)
    (hcen : ∀ D : ProperDivisorOver k sX, D.valuation = ν →
      (∀ z : X, IsGenericPoint z (D.center : Set X) → z ∈ U) ∧
      I = Scheme.IdealSheafData.vanishingIdeal
        ⟨U.ι ⁻¹' (D.center : Set X), D.center.isClosed.preimage U.ι.continuous⟩ ∧
      IsSmoothScheme (I.subschemeι ≫ U.ι ≫ sX)) :
    HasNonemptyCenter k sX' ν' := by
  subst hY hs
  have hβ' : β = blowUpToBase I ≫ U.ι := by simpa using hβ
  subst hβ'
  obtain ⟨hdiv, D, hD⟩ := hν₀
  obtain ⟨hxU, hI, -⟩ := hcen D hD
  have hx := hxU _ (isGenericPoint_center D)
  have hsupp : (I.support : Set U) ≠ Set.univ := by
    intro h
    have hη : genericPoint X ∈ U :=
      ((genericPoint_spec X).mem_open_set_iff U.isOpen).2 ⟨_, trivial, hx⟩
    have hmem : (⟨genericPoint X, hη⟩ : U) ∈ (I.support : Set U) := h ▸ trivial
    rw [hI, Scheme.IdealSheafData.coe_support_vanishingIdeal] at hmem
    exact genericPoint_notMem_center D hmem
  have hdiv' := isDivisorOfFunctionField_of_comap sX _
    (functionFieldMap_bijective_blowUp U I hsupp) hν hdiv
  refine ⟨hdiv', ?_⟩
  have : Mori.IsVariety k sX := hvar
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : Mori.IsVariety k ((blowUpToBase I ≫ U.ι) ≫ sX) := hvar'
  obtain ⟨x', h1, h2⟩ := exists_dominated_point_blowUp U I ν' _ hx
    (fun a => by
      rw [hν, ← hD]
      exact MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D.toDivisorOver _ rfl a)
    (fun a ha => by
      rw [hν, ← hD]
      exact MMP.Positivity.DivisorOver.valuation_algebraMap_lt_one D.toDivisorOver _ rfl a ha)
  obtain ⟨D', -, hD', -⟩ :=
    exists_properDivisorOver_isProjective_of_dominates _ hdiv' x' h1 h2
  exact ⟨D', hD'⟩

private theorem hasNonemptyCenter_all {k : Type v} [Field k]
    (Y : ℕ → Scheme.{v}) (s : ∀ r, Y r ⟶ Spec (.of k)) [∀ r, IsIntegral (Y r)]
    (hvar : ∀ r, Mori.IsVariety k (s r)) (hsm : ∀ r, IsSmoothScheme (s r))
    (ν : ∀ r, Valuation (Y r).functionField ℤᵐ⁰) (hν₀ : HasNonemptyCenter k (s 0) (ν 0))
    (U : ∀ r, (Y r).Opens) (I : ∀ r, (U r : Scheme.{v}).IdealSheafData)
    (hY : ∀ r, Y (r + 1) = blowUp (I r))
    (β : ∀ r, Y (r + 1) ⟶ Y r)
    (hβ : ∀ r, β r = eqToHom (hY r) ≫ blowUpToBase (I r) ≫ (U r).ι)
    (hs : ∀ r, s (r + 1) = β r ≫ s r) [∀ r, IsDominant (β r)]
    (hν : ∀ r, (ν (r + 1)).comap (functionFieldMap (β r)) = ν r)
    (hcen : ∀ r (D : ProperDivisorOver k (s r)), D.valuation = ν r →
      (∀ z : Y r, IsGenericPoint z (D.center : Set (Y r)) → z ∈ U r) ∧
      I r = Scheme.IdealSheafData.vanishingIdeal
        ⟨(U r).ι ⁻¹' (D.center : Set (Y r)), D.center.isClosed.preimage (U r).ι.continuous⟩ ∧
      IsSmoothScheme ((I r).subschemeι ≫ (U r).ι ≫ s r)) :
    ∀ r, HasNonemptyCenter k (s r) (ν r) := by
  intro r
  induction r with
  | zero => exact hν₀
  | succ r ih =>
    exact hasNonemptyCenter_blowUp (s r) (s (r + 1)) (hvar r) (hvar (r + 1)) (hsm r)
      (hsm (r + 1)) (ν r) (ν (r + 1)) ih (U r) (I r) (hY r) (β r) (hβ r) (hs r) (hν r) (hcen r)

/-- The blow-up morphism of one step of the sequence induces an isomorphism of function fields:
the blown-up ideal vanishes on the center of a divisor, which misses the generic point. -/
private theorem functionFieldMap_bijective_of_blowUp {k : Type v} [Field k]
    {X X' : Scheme.{v}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsIntegral X']
    (D : ProperDivisorOver k sX) (U : X.Opens) (I : (U : Scheme.{v}).IdealSheafData)
    (hY : X' = blowUp I) (β : X' ⟶ X) (hβ : β = eqToHom hY ≫ blowUpToBase I ≫ U.ι)
    [IsDominant β] (hxU : ∀ z : X, IsGenericPoint z (D.center : Set X) → z ∈ U)
    (hI : I = Scheme.IdealSheafData.vanishingIdeal
        ⟨U.ι ⁻¹' (D.center : Set X), D.center.isClosed.preimage U.ι.continuous⟩) :
    Function.Bijective (functionFieldMap β) := by
  subst hY
  have hβ' : β = blowUpToBase I ≫ U.ι := by simpa using hβ
  subst hβ'
  have hx := hxU _ (isGenericPoint_center D)
  refine functionFieldMap_bijective_blowUp U I fun h => ?_
  have hη : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).2 ⟨_, trivial, hx⟩
  have hmem : (⟨genericPoint X, hη⟩ : U) ∈ (I.support : Set U) := h ▸ trivial
  rw [hI, Scheme.IdealSheafData.coe_support_vanishingIdeal] at hmem
  exact genericPoint_notMem_center D hmem

/-- A valuation of `K` with values in `ℤᵐ⁰` taking the value `exp (-1)` is rank-one discrete. -/
private theorem isRankOneDiscrete_of_exists_eq_exp_neg_one {K : Type*} [Ring K]
    (v : Valuation K ℤᵐ⁰) (hv : ∃ g, v g = WithZero.exp (-1)) : v.IsRankOneDiscrete := by
  obtain ⟨g, hval⟩ := hv
  refine ⟨⟨Units.mk0 (WithZero.exp (-1)) WithZero.exp_ne_zero, le_antisymm ?_ ?_, ?_⟩⟩
  · rw [Subgroup.zpowers_le]
    exact MonoidWithZeroHom.mem_valueGroup _ ⟨g, by simpa using hval⟩
  · intro γ _
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨-(γ : ℤᵐ⁰).log, Units.ext ?_⟩
    rw [Units.val_zpow_eq_zpow_val, Units.val_mk0, ← WithZero.exp_zsmul, smul_neg, smul_eq_mul,
      mul_one, neg_neg, WithZero.exp_log γ.ne_zero]
  · change WithZero.exp (-1 : ℤ) < 1
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega

/-- A ring map from a local ring into a field, landing in the valuation ring of `w` and sending the
maximal ideal into the maximal ideal of `w`, is a local homomorphism into the valuation ring. -/
private theorem isLocalHom_codRestrict_valuationSubring {A K Γ₀ : Type*} [CommRing A]
    [IsLocalRing A] [Field K] [LinearOrderedCommGroupWithZero Γ₀] (w : Valuation K Γ₀)
    (φ : A →+* K) (h1 : ∀ a, w (φ a) ≤ 1)
    (h2 : ∀ a ∈ IsLocalRing.maximalIdeal A, w (φ a) < 1) :
    IsLocalHom (φ.codRestrict w.valuationSubring.toSubring
      fun a => (w.mem_valuationSubring_iff _).2 (h1 a)) := by
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  have hlt := h2 a ((IsLocalRing.mem_maximalIdeal _).2 hna)
  obtain ⟨b, hb⟩ := ha.exists_right_inv
  have hb' : φ a * (b : K) = 1 := congrArg Subtype.val hb
  have := mul_lt_one_of_lt_of_le hlt ((w.mem_valuationSubring_iff _).1 b.2)
  rw [← map_mul, hb', map_one] at this
  exact lt_irrefl _ this

/-- Two morphisms from the spectrum of a valuation ring `A` of `K` to a separated `k`-scheme agree
once they agree on `Spec K` (valuative criterion of separatedness). -/
private theorem eq_of_SpecMap_algebraMap_comp {k K : Type v} [Field k] [Field K]
    (A : ValuationSubring K) {X : Scheme.{v}} (sX : X ⟶ Spec (.of k)) [IsSeparated sX]
    (a b : Spec (.of A) ⟶ X)
    (h : Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ a =
      Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ b) : a = b := by
  let α := CommRingCat.ofHom (algebraMap A K)
  have key : ∀ g g' : Spec (.of A) ⟶ Spec (.of k), Spec.map α ≫ g = Spec.map α ≫ g' → g = g' := by
    intro g g' h
    obtain ⟨p, rfl⟩ : ∃ p, Spec.map p = g := ⟨_, Spec.map_preimage g⟩
    obtain ⟨p', rfl⟩ : ∃ p, Spec.map p = g' := ⟨_, Spec.map_preimage g'⟩
    rw [← Spec.map_comp, ← Spec.map_comp] at h
    congr 1
    ext c
    exact congrArg (fun q => q.hom c) (Spec.map_injective h)
  have hll : b ≫ sX = a ≫ sX := key _ _ (by rw [← Category.assoc, ← Category.assoc, h])
  let S : ValuativeCommSq sX :=
    { R := A
      K := K
      i₁ := Spec.map α ≫ a
      i₂ := a ≫ sX
      commSq := ⟨by rw [Category.assoc]⟩ }
  have hS := IsSeparated.valuativeCriterion sX S
  let L : S.commSq.LiftStruct := ⟨a, rfl, rfl⟩
  let L' : S.commSq.LiftStruct := ⟨b, h.symm, hll⟩
  exact congrArg CommSq.LiftStruct.l (Subsingleton.elim L L')

private theorem eqToHom_comp_blowUpToBase {X Y : Scheme.{v}} {J J' : X.IdealSheafData}
    (h : J = J') (e : Y = blowUp J) (e' : Y = blowUp J') :
    eqToHom e ≫ blowUpToBase J = eqToHom e' ≫ blowUpToBase J' := by
  subst h
  rfl

/-- **The point dimension formula for a divisor.** The residue field of the valuation ring `R`
of a divisor `(Y, f, E)` over a variety `X` has transcendence degree `dim X - 1` over `k`: `R` is
the local ring `𝒪_{Y,E}`, whose residue field `κ(η_E)` has transcendence degree
`dim Y - dim 𝒪_{Y,E} = dim X - 1`. -/
private theorem trdeg_residueField_add_one_eq {k : Type v} [Field k] {X : Scheme.{v}}
    [X.Over (Spec (.of k))] [IsIntegral X] (hX : Mori.IsVariety k (X ↘ Spec (.of k)))
    (D : ProperDivisorOver k (X ↘ Spec (.of k))) (x₀ : X) (hx₀ : x₀ = D.f D.E.genericPoint)
    (R : Subring X.functionField) [IsDiscreteValuationRing R]
    (hRv : ∀ g, g ∈ R ↔ D.valuation g ≤ 1)
    (hR : ∀ s : X.presheaf.stalk x₀, algebraMap (X.presheaf.stalk x₀) X.functionField s ∈ R) :
    letI : Algebra k (IsLocalRing.ResidueField R) :=
      ((IsLocalRing.residue R).comp
        (((algebraMap (X.presheaf.stalk x₀) X.functionField).codRestrict R hR).comp
          ((X.presheaf.germ ⊤ x₀ trivial).hom.comp
            ((X ↘ Spec (.of k)).appTop.hom.comp
              (Scheme.ΓSpecIso (.of k)).inv.hom)))).toAlgebra
    (((Algebra.trdeg k (IsLocalRing.ResidueField R)).toENat + 1 : ℕ∞) : WithBot ℕ∞) =
      topologicalKrullDim X := by
  subst hx₀
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  haveI : LocallyOfFiniteType (X ↘ Spec (.of k)) := hX.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (D.f ≫ X ↘ Spec (.of k)) :=
    D.isNormalVariety.1.toLocallyOfFiniteType
  haveI := D.E.isDiscreteValuationRing_localRing
  have hbij := MMP.Mori.IsBirationalMorphism.functionFieldMap_bijective D.isBirationalMorphism
  -- `dim D.Y = dim X`, and the point dimension formula at the generic point of `E`
  have hdimY : topologicalKrullDim D.Y = topologicalKrullDim X := by
    rw [← toENat_trdeg_functionField (sX := D.f ≫ X ↘ Spec (.of k)),
      ← toENat_trdeg_functionField (sX := X ↘ Spec (.of k)),
      trdeg_functionField_eq_of_bijective _ D.f hbij]
  have hη := topologicalKrullDimAt_eq_trdeg_add_krullDim_stalk k D.Y
    (D.f ≫ X ↘ Spec (.of k)) D.E.genericPoint
  rw [← topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k D.Y
    (D.f ≫ X ↘ Spec (.of k)) D.E.genericPoint, hdimY, ringKrullDim_stalk_eq_coheight,
    D.E.coheight_genericPoint] at hη
  rw [hη]
  -- the valuation ring `R` is the local ring `𝒪_{D.Y, E}`
  let ffm := RingEquiv.ofBijective _ hbij
  let O := D.Y.presheaf.stalk D.E.genericPoint
  have hmem : ∀ r : O, ffm.symm (algebraMap O D.Y.functionField r) ∈ R := fun r => by
    refine (hRv _).2 ?_
    change D.E.divisorialValuation (ffm (ffm.symm _)) ≤ 1
    rw [RingEquiv.apply_symm_apply]
    exact (MMP.Mori.PrimeDivisor.divisorialValuation_le_one_iff _ _).2 ⟨r, rfl⟩
  let φ : O →+* R := (ffm.symm.toRingHom.comp (algebraMap O D.Y.functionField)).codRestrict R hmem
  have hφ : Function.Bijective φ := by
    refine ⟨fun a b hab => ?_, fun g => ?_⟩
    · have h := congrArg (fun x : R => ffm (x : X.functionField)) hab
      simp only [φ, RingHom.codRestrict_apply, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply] at h
      exact IsFractionRing.injective O D.Y.functionField h
    · obtain ⟨r, hr⟩ := (MMP.Mori.PrimeDivisor.divisorialValuation_le_one_iff _ _).1
        ((hRv g).1 g.2)
      refine ⟨r, Subtype.ext ?_⟩
      change ffm.symm (algebraMap O D.Y.functionField r) = g
      rw [hr]
      exact ffm.symm_apply_apply g
  let Φ := RingEquiv.ofBijective φ hφ
  letI : Algebra k (D.Y.residueField D.E.genericPoint) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.f ≫ X ↘ Spec (.of k)).appTop ≫
      D.Y.Γevaluation D.E.genericPoint).hom.toAlgebra
  letI : Algebra k (IsLocalRing.ResidueField R) :=
    ((IsLocalRing.residue R).comp
      (((algebraMap (X.presheaf.stalk (D.f D.E.genericPoint)) X.functionField).codRestrict R
        hR).comp ((X.presheaf.germ ⊤ (D.f D.E.genericPoint) trivial).hom.comp
          ((X ↘ Spec (.of k)).appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)))).toAlgebra
  let eκ : D.Y.residueField D.E.genericPoint ≃ₐ[k] IsLocalRing.ResidueField R :=
    { IsLocalRing.ResidueField.mapEquiv Φ with
      commutes' := fun c => by
        set a := (X ↘ Spec (.of k)).appTop ((Scheme.ΓSpecIso (.of k)).inv c)
        change IsLocalRing.ResidueField.map (Φ : O →+* R)
          (IsLocalRing.residue O (D.Y.presheaf.germ ⊤ D.E.genericPoint trivial (D.f.appTop a))) =
          IsLocalRing.residue R _
        rw [IsLocalRing.ResidueField.map_residue]
        congr 1
        refine Subtype.ext ?_
        change ffm.symm _ = algebraMap (X.presheaf.stalk (D.f D.E.genericPoint)) X.functionField
          (X.presheaf.germ ⊤ (D.f D.E.genericPoint) trivial a)
        rw [RingEquiv.symm_apply_eq]
        change _ = functionFieldMap D.f _
        rw [MMP.Mori.functionFieldMap_algebraMap_stalk]
        congr 1
        exact (Scheme.Hom.germ_stalkMap_apply D.f ⊤ D.E.genericPoint trivial a).symm }
  rw [← eκ.trdeg_eq]
  norm_cast

private theorem exists_coheight_eq_one {k : Type v} [Field k]
    (Y : ℕ → Scheme.{v}) (s : ∀ r, Y r ⟶ Spec (.of k)) [∀ r, IsIntegral (Y r)]
    (hvar : ∀ r, Mori.IsVariety k (s r)) (hsm : ∀ r, IsSmoothScheme (s r))
    (ν : ∀ r, Valuation (Y r).functionField ℤᵐ⁰) (hν₀ : HasNonemptyCenter k (s 0) (ν 0))
    (U : ∀ r, (Y r).Opens) (I : ∀ r, (U r : Scheme.{v}).IdealSheafData)
    (hY : ∀ r, Y (r + 1) = blowUp (I r))
    (β : ∀ r, Y (r + 1) ⟶ Y r)
    (hβ : ∀ r, β r = eqToHom (hY r) ≫ blowUpToBase (I r) ≫ (U r).ι)
    (hs : ∀ r, s (r + 1) = β r ≫ s r) [∀ r, IsDominant (β r)]
    (hν : ∀ r, (ν (r + 1)).comap (functionFieldMap (β r)) = ν r)
    (hcen : ∀ r (D : ProperDivisorOver k (s r)), D.valuation = ν r →
      (∀ z : Y r, IsGenericPoint z (D.center : Set (Y r)) → z ∈ U r) ∧
      I r = Scheme.IdealSheafData.vanishingIdeal
        ⟨(U r).ι ⁻¹' (D.center : Set (Y r)), D.center.isClosed.preimage (U r).ι.continuous⟩ ∧
      IsSmoothScheme ((I r).subschemeι ≫ (U r).ι ≫ s r))
    (hall : ∀ r, HasNonemptyCenter k (s r) (ν r)) :
    ∃ r, ∃ D : ProperDivisorOver k (s r), D.valuation = ν r ∧
      ∃ z : Y r, IsGenericPoint z (D.center : Set (Y r)) ∧ Order.coheight z = 1 := by
  classical
  -- the divisors over the `Y r` realizing `ν r`, and the generic points of their centers
  choose D hD using fun r => (hall r).2
  let z : ∀ r, Y r := fun r => (D r).f (D r).E.genericPoint
  have hzU : ∀ r, z r ∈ U r := fun r => (hcen r (D r) (hD r)).1 _ (isGenericPoint_center (D r))
  -- the function fields of the `Y r` are identified with `K = k(Y 0)`
  have hbij : ∀ r, Function.Bijective (functionFieldMap (β r)) := fun r =>
    functionFieldMap_bijective_of_blowUp (D r) (U r) (I r) (hY r) (β r) (hβ r)
      (hcen r (D r) (hD r)).1 (hcen r (D r) (hD r)).2.1
  let e : ∀ r, (Y (r + 1)).functionField →+* (Y r).functionField := fun r =>
    (RingEquiv.ofBijective _ (hbij r)).symm.toRingHom
  have he : ∀ r b, e r (functionFieldMap (β r) b) = b := fun r b =>
    (RingEquiv.ofBijective _ (hbij r)).symm_apply_apply b
  have he' : ∀ r a, functionFieldMap (β r) (e r a) = a := fun r a =>
    (RingEquiv.ofBijective _ (hbij r)).apply_symm_apply a
  let ψ : ∀ r, (Y r).functionField →+* (Y 0).functionField := fun r =>
    Nat.rec (motive := fun r => (Y r).functionField →+* (Y 0).functionField) (RingHom.id _)
      (fun r ψr => ψr.comp (e r)) r
  have hψβ : ∀ r b, ψ (r + 1) (functionFieldMap (β r) b) = ψ r b := fun r b =>
    congrArg (ψ r) (he r b)
  have hψν : ∀ r a, ν 0 (ψ r a) = ν r a := by
    intro r
    induction r with
    | zero => intro a; rfl
    | succ r ih =>
      intro a
      change ν 0 (ψ r (e r a)) = _
      rw [ih, ← hν r, Valuation.comap_apply, he']
  -- the valuation ring `R` of `ν 0`, and the morphisms `Spec R ⟶ Y r`
  have := isRankOneDiscrete_of_exists_eq_exp_neg_one (ν 0)
    (hD 0 ▸ MMP.Positivity.DivisorOver.exists_valuation_eq_exp_neg_one (D 0).toDivisorOver)
  let R : Subring (Y 0).functionField := (ν 0).valuationSubring.toSubring
  haveI : IsDiscreteValuationRing R :=
    inferInstanceAs (IsDiscreteValuationRing (ν 0).valuationSubring)
  have h1 : ∀ r (a : (Y r).presheaf.stalk (z r)),
      ν 0 ((ψ r).comp (algebraMap _ (Y r).functionField) a) ≤ 1 := fun r a => by
    rw [RingHom.comp_apply, hψν, ← hD r]
    exact MMP.Positivity.DivisorOver.valuation_algebraMap_le_one (D r).toDivisorOver _ rfl a
  have h2 : ∀ r, ∀ a ∈ IsLocalRing.maximalIdeal ((Y r).presheaf.stalk (z r)),
      ν 0 ((ψ r).comp (algebraMap _ (Y r).functionField) a) < 1 := fun r a ha => by
    rw [RingHom.comp_apply, hψν, ← hD r]
    exact MMP.Positivity.DivisorOver.valuation_algebraMap_lt_one (D r).toDivisorOver _ rfl a ha
  let θ : ∀ r, (Y r).presheaf.stalk (z r) →+* R := fun r =>
    ((ψ r).comp (algebraMap _ (Y r).functionField)).codRestrict R
      fun a => ((ν 0).mem_valuationSubring_iff _).2 (h1 r a)
  have hθ : ∀ r, IsLocalHom (θ r) := fun r =>
    isLocalHom_codRestrict_valuationSubring (ν 0) _ (h1 r) (h2 r)
  let mor : ∀ r, Spec (.of R) ⟶ Y r := fun r =>
    Spec.map (CommRingCat.ofHom (θ r)) ≫ (Y r).fromSpecStalk (z r)
  have hmor_closed : ∀ r, mor r (IsLocalRing.closedPoint R) = z r := fun r => by
    have := hθ r
    have hc := Spec_closedPoint (f := CommRingCat.ofHom (θ r))
    change (Y r).fromSpecStalk (z r) (Spec.map (CommRingCat.ofHom (θ r))
      (IsLocalRing.closedPoint R)) = z r
    rw [hc, Scheme.fromSpecStalk_closedPoint]
  have hmor_gen : ∀ r, Spec.map (CommRingCat.ofHom (algebraMap R (Y 0).functionField)) ≫ mor r =
      Spec.map (CommRingCat.ofHom (ψ r)) ≫ (Y r).fromSpecStalk (genericPoint (Y r)) := fun r => by
    have hsp : genericPoint (Y r) ⤳ z r := (genericPoint_spec (Y r)).specializes trivial
    change _ ≫ Spec.map (CommRingCat.ofHom (θ r)) ≫ (Y r).fromSpecStalk (z r) = _
    rw [← Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp, ← Spec.map_comp_assoc,
      ← Spec.map_comp_assoc]
    rfl
  have hmor_succ : ∀ r, mor (r + 1) ≫ β r = mor r := fun r => by
    have := (hvar r).toIsSeparated
    refine eq_of_SpecMap_algebraMap_comp (ν 0).valuationSubring (s r) _ _ ?_
    change Spec.map (CommRingCat.ofHom (algebraMap R (Y 0).functionField)) ≫ mor (r + 1) ≫ β r =
      Spec.map (CommRingCat.ofHom (algebraMap R (Y 0).functionField)) ≫ mor r
    rw [reassoc_of% (hmor_gen (r + 1)), hmor_gen r,
      ← Scheme.SpecMap_stalkMap_fromSpecStalk (β r)]
    have hη : β r (genericPoint (Y (r + 1))) ⤳ genericPoint (Y r) :=
      (Inseparable.of_eq (map_genericPoint_of_isDominant (β r))).specializes
    rw [← Scheme.SpecMap_stalkSpecializes_fromSpecStalk hη, ← Spec.map_comp_assoc,
      ← Spec.map_comp_assoc]
    congr 2
    ext a
    exact hψβ r a
  -- the morphisms factor through the opens `U r`, and the centers are the blown-up loci
  have hrange : ∀ r, Set.range (mor r) ⊆ Set.range (U r).ι := fun r => by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hsp : mor r p ⤳ z r := by
      have := Set.mem_range_self (f := (Y r).fromSpecStalk (z r))
        (Spec.map (CommRingCat.ofHom (θ r)) p)
      rwa [Scheme.range_fromSpecStalk] at this
    exact hsp.mem_open (U r).isOpen (hzU r)
  let morOpen : ∀ r, Spec (.of R) ⟶ U r := fun r =>
    IsOpenImmersion.lift (U r).ι (mor r) (hrange r)
  have hmorOpen : ∀ r, morOpen r ≫ (U r).ι = mor r := fun r => IsOpenImmersion.lift_fac _ _ _
  have hcI : ∀ r, centerIdeal (morOpen r) = I r := fun r => by
    have hpt : (U r).ι (morOpen r (IsLocalRing.closedPoint R)) = z r := by
      rw [← hmor_closed r, ← hmorOpen r]
      rfl
    rw [(hcen r (D r) (hD r)).2.1, MMP.Mori.centerIdeal]
    congr 1
    apply Closeds.ext
    rw [Closeds.coe_closure]
    change closure {morOpen r (IsLocalRing.closedPoint R)} = (U r).ι ⁻¹' ((D r).center : Set (Y r))
    rw [(U r).ι.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image, Set.image_singleton,
      hpt, (isGenericPoint_center (D r)).def]
  have hobj : ∀ r, Y (r + 1) = blowUp (centerIdeal (morOpen r)) := fun r =>
    (hY r).trans (by rw [hcI r])
  have hR' : ∀ a : (Y 0).presheaf.stalk (z 0), algebraMap _ (Y 0).functionField a ∈ R :=
    fun a => ((ν 0).mem_valuationSubring_iff _).2 (h1 0 a)
  let S : ZariskiSequence (Y 0) (fromSpecOfStalkLE (z 0) R hR') :=
    { obj := Y
      mor := mor
      obj_zero := rfl
      mor_zero := by
        rw [eqToHom_refl, Category.comp_id]
        rfl
      U := U
      morOpen := morOpen
      morOpen_ι := hmorOpen
      obj_succ := hobj
      mor_succ_comp := fun r => by
        rw [← cancel_mono (U r).ι, hmorOpen, ← hmor_succ r, hβ r, Category.assoc,
          Category.assoc, ← Category.assoc (eqToHom _),
          eqToHom_comp_blowUpToBase (hcI r) (hobj r) (hY r), Category.assoc]
        rfl }
  -- Zariski's theorem: some local ring of the sequence is the valuation ring `R`
  letI : (Y 0).Over (Spec (.of k)) := ⟨s 0⟩
  haveI : LocallyOfFiniteType ((Y 0) ↘ Spec (.of k)) := (hvar 0).toLocallyOfFiniteType
  haveI : IsSeparated ((Y 0) ↘ Spec (.of k)) := (hvar 0).toIsSeparated
  haveI : QuasiCompact ((Y 0) ↘ Spec (.of k)) := (hvar 0).toQuasiCompact
  obtain ⟨n, hn⟩ := MMP.Mori.ZariskiSequence.exists_isIso_stalkClosedPointTo (k := k) (z 0) R hR'
    (hθ 0) (trdeg_residueField_add_one_eq (hvar 0) (D 0) (z 0) rfl R
      (fun g => ((ν 0).mem_valuationSubring_iff g).trans (by rw [← hD 0]; exact Iff.rfl)) hR') S
  haveI : IsIso (Scheme.stalkClosedPointTo (mor n)) := hn
  have hdim : ringKrullDim ((Y n).presheaf.stalk (mor n (IsLocalRing.closedPoint R))) = 1 := by
    rw [ringKrullDim_eq_of_ringEquiv
      (asIso (Scheme.stalkClosedPointTo (mor n))).commRingCatIsoToRingEquiv]
    exact IsDiscreteValuationRing.ringKrullDim_eq_one _
  refine ⟨n, D n, hD n, z n, isGenericPoint_center (D n), ?_⟩
  rw [ringKrullDim_stalk_eq_coheight, hmor_closed n] at hdim
  exact_mod_cast hdim

/-- **Every generically chosen smooth-centre Zariski sequence reaches its divisor.**
Let `Y 0` be a smooth variety over `k` and `ν 0` a divisor of `k(Y 0)` with nonempty center.
Let `Y (r + 1) = blowUp (I r)`, where `I r` is the vanishing ideal, in an open `U r ⊆ Y r`
containing the generic point of the center `Zᵣ` of `ν r`, of the smooth closed subset
`Zᵣ ∩ U r`, and let `ν (r + 1)` be `ν r` on `k(Y (r + 1))`. Then `ν r` has nonempty center on
every `Y r`, and for some `r` the center of `ν r` has codimension one. -/
@[mmp "lem_mmp_foundation_fa2_all_choice_zariski_blowups"]
public theorem hasNonemptyCenter_and_exists_coheight_eq_one_of_blowUp {k : Type u} [Field k]
    (Y : ℕ → Scheme.{u}) (s : ∀ r, Y r ⟶ Spec (.of k)) [∀ r, IsIntegral (Y r)]
    (hvar : ∀ r, Mori.IsVariety k (s r)) (hsm : ∀ r, IsSmoothScheme (s r))
    (ν : ∀ r, Valuation (Y r).functionField ℤᵐ⁰) (hν₀ : HasNonemptyCenter k (s 0) (ν 0))
    (U : ∀ r, (Y r).Opens) (I : ∀ r, (U r : Scheme.{u}).IdealSheafData)
    (hY : ∀ r, Y (r + 1) = blowUp (I r)) (β : ∀ r, Y (r + 1) ⟶ Y r)
    (hβ : ∀ r, β r = eqToHom (hY r) ≫ blowUpToBase (I r) ≫ (U r).ι)
    (hs : ∀ r, s (r + 1) = β r ≫ s r) [∀ r, IsDominant (β r)]
    (hν : ∀ r, (ν (r + 1)).comap (functionFieldMap (β r)) = ν r)
    (hcen : ∀ r (D : ProperDivisorOver k (s r)), D.valuation = ν r →
      (∀ z : Y r, IsGenericPoint z (D.center : Set (Y r)) → z ∈ U r) ∧
      I r = Scheme.IdealSheafData.vanishingIdeal
        ⟨(U r).ι ⁻¹' (D.center : Set (Y r)), D.center.isClosed.preimage (U r).ι.continuous⟩ ∧
      IsSmoothScheme ((I r).subschemeι ≫ (U r).ι ≫ s r)) :
    (∀ r, HasNonemptyCenter k (s r) (ν r)) ∧
      ∃ r, ∃ D : ProperDivisorOver k (s r), D.valuation = ν r ∧
        ∃ z : Y r, IsGenericPoint z (D.center : Set (Y r)) ∧ Order.coheight z = 1 := by
  have hall := hasNonemptyCenter_all Y s hvar hsm ν hν₀ U I hY β hβ hs hν hcen
  exact ⟨hall, exists_coheight_eq_one Y s hvar hsm ν hν₀ U I hY β hβ hs hν hcen hall⟩

end MMP.Flips

end

/-! ### Descent of a polarized smooth projective variety to a finitely generated field -/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace MMP.Descent

/-- Over a field, an ample invertible sheaf in the sense of `MMP.Intersection.IsAmple` is ample in
the Stacks sense: a power of it embeds the scheme in projective space (Tag 01VT). -/
private theorem stacks_isAmple_of_isAmple (k : Type v) [Field k]
    {X : Scheme.{v}} [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hL : MMP.Intersection.IsAmple k L) : Stacks.Ample.IsAmple X L := by
  have : Stacks.Ample.IsInvertibleModule X L := ‹_›
  obtain ⟨d, hd, hva⟩ := hL
  obtain ⟨eP⟩ := MMP.Resolution.Bridges.nonempty_tensorPow_iso_tensorPowModule X L d
  exact ((Stacks.AmpleRelativeFiniteType.tfae_six (X ↘ Spec (.of k)) L).out 5 1).1
    (⟨d, hd, MMP.Resolution.Bridges.hasImmersionTwistOver_of_isVeryAmple k _ _ hva eP.symm⟩ :
      ∃ d : ℕ, 1 ≤ d ∧ Stacks.AmpleProjectiveImmersion.HasImmersionTwistOver
        (X ↘ Spec (.of k)) (Stacks.Ample.tensorPowModule X L (d : ℤ)))

/-- Conversely, a proper scheme over a field with a Stacks-ample invertible sheaf is projective,
and the sheaf is ample in the sense of `MMP.Intersection.IsAmple`: a power of it gives an
immersion into projective space, which is closed by properness. -/
private theorem isProjectiveMorphism_and_isAmple_of_isAmple (F : Type v) [Field F]
    {X : Scheme.{v}} [X.Over (Spec (.of F))] [IsProper (X ↘ Spec (.of F))]
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hL : Stacks.Ample.IsAmple X L) :
    IsProjectiveMorphism (X ↘ Spec (.of F)) ∧ MMP.Intersection.IsAmple F L := by
  have : Stacks.Ample.IsInvertibleModule X L := ‹_›
  obtain ⟨d₀, hd₀, himm⟩ :=
    ((Stacks.AmpleRelativeFiniteType.tfae_six (X ↘ Spec (.of F)) L).out 1 6).1 hL
  have himm₀ := himm d₀ le_rfl
  obtain ⟨eP⟩ := MMP.Resolution.Bridges.nonempty_tensorPow_iso_tensorPowModule X L d₀
  refine ⟨?_, d₀, hd₀, MMP.Resolution.Bridges.isVeryAmple_of_hasImmersionTwistOver F _ _ eP himm₀⟩
  obtain ⟨n, i, hi, hiover, -⟩ := himm₀
  have : IsImmersion i := hi
  have : IsProper i := by
    have : IsProper (i ≫ pullback.fst _ _) := by rw [hiover]; infer_instance
    exact IsProper.of_comp _ (pullback.fst _ _)
  exact ⟨n, i, IsClosedImmersion.of_isPreimmersion _ i.isClosedMap.isClosed_range, hiover⟩

/-- Descent of a polarized smooth projective `k`-scheme to a finitely generated subfield, without
geometric integrality. `Spec k` is the limit of the spectra of the finitely generated subrings
`ℤ[s] ⊆ k`; the polarized proper flat model over a stage and smoothness at a later stage come
from that limit, and the model is then base changed to the field `ℚ(s) ⊆ k`. -/
private theorem exists_fg_model_of_isAmple
    (k : Type v) [Field k] [IsAlgClosed k] [CharZero k]
    (X : Scheme.{v}) [X.Over (Spec (.of k))] [IsIntegral X]
    [Smooth (X ↘ Spec (.of k))] (hproj : IsProjectiveMorphism (X ↘ Spec (.of k)))
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hL : MMP.Intersection.IsAmple k L) :
    ∃ (F : IntermediateField ℚ k), F.FG ∧
      ∃ (XF : Scheme.{v}) (_ : XF.Over (Spec (.of F))),
        Smooth (XF ↘ Spec (.of F)) ∧ IsProjectiveMorphism (XF ↘ Spec (.of F)) ∧
        ∃ (LF : XF.Modules) (_ : SheafOfModules.IsInvertible XF.presheaf XF.ringCatSheaf.2 LF),
          MMP.Intersection.IsAmple F LF ∧
          ∃ e : X ≅ pullback (XF ↘ Spec (.of F))
              (Spec.map (CommRingCat.ofHom (algebraMap F k))),
            e.hom ≫ pullback.snd _ _ = X ↘ Spec (.of k) ∧
            Nonempty (L ≅ (Scheme.Modules.pullback (e.hom ≫ pullback.fst _ _)).obj LF) := by
  classical
  have : IsProper (X ↘ Spec (.of k)) := isProper_of_isProjectiveMorphism _ hproj
  have hinvX : Stacks.Ample.IsInvertibleModule X L := ‹_›
  have hrel : Stacks.RelativeAmple.IsRelativelyAmple (X ↘ Spec (.of k)) L :=
    (Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple _ L).mpr
      (stacks_isAmple_of_isAmple k L hL)
  -- the limit presentation of `Spec k`
  let D := specAdjoinFinsetDiagram k
  let c := specAdjoinFinsetCone k
  have hc : IsLimit c := isLimit_specAdjoinFinsetCone k
  let f : X ⟶ c.pt := X ↘ Spec (.of k)
  have : IsProper f := ‹IsProper (X ↘ Spec (.of k))›
  have : Flat f := inferInstanceAs (Flat (X ↘ Spec (.of k)))
  have hfp : FinitePresentation f :=
    ⟨inferInstanceAs (LocallyOfFinitePresentation (X ↘ Spec (.of k))),
      inferInstanceAs (QuasiCompact (X ↘ Spec (.of k))),
      inferInstanceAs (QuasiSeparated (X ↘ Spec (.of k)))⟩
  obtain ⟨i₁, X₁, f₁, L₁, hL₁, g₁, hpr₁, hfl₁, hfp₁, hamp₁, hpb₁, ⟨eL⟩⟩ :=
    exists_stage_polarizedModel D c hc f hfp L ‹_› hrel
  -- smoothness at a later stage
  have : LocallyOfFinitePresentation f₁ := hfp₁.1
  have : QuasiCompact f₁ := hfp₁.2.1
  have : QuasiSeparated f₁ := hfp₁.2.2
  have : CompactSpace X₁ := QuasiCompact.compactSpace_of_compactSpace f₁
  have : QuasiSeparatedSpace X₁ := quasiSeparatedSpace_of_quasiSeparated f₁
  have : MorphismProperty.RespectsIso (@Smooth.{v}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  let X₀ : Over (D.obj i₁) := Over.mk f₁
  let Y₀ : Over (D.obj i₁) := Over.mk (𝟙 (D.obj i₁))
  let a : X₀ ⟶ Y₀ := Over.homMk f₁ (Category.comp_id f₁)
  have : CompactSpace X₀.left := inferInstanceAs (CompactSpace X₁)
  have : QuasiSeparatedSpace X₀.left := inferInstanceAs (QuasiSeparatedSpace X₁)
  have : CompactSpace Y₀.left := inferInstanceAs (CompactSpace (D.obj i₁))
  have : QuasiSeparatedSpace Y₀.left := inferInstanceAs (QuasiSeparatedSpace (D.obj i₁))
  have : LocallyOfFinitePresentation a.left := inferInstanceAs (LocallyOfFinitePresentation f₁)
  have key : ∀ {T : Scheme.{v}} (b : T ⟶ D.obj i₁),
      Smooth ((Over.pullback b).map a).left ↔ Smooth (pullback.snd f₁ b) :=
    fun b ↦ smooth_overPullback_map_left_iff a b
  have hsm : Smooth ((Over.pullback (c.π.app i₁)).map a).left := by
    rw [key, ← MorphismProperty.cancel_left_of_respectsIso (@Smooth.{v}) hpb₁.isoPullback.hom,
      hpb₁.isoPullback_hom_snd]
    exact inferInstanceAs (Smooth (X ↘ Spec (.of k)))
  obtain ⟨j, k', hj⟩ := exists_smooth_baseChange_of_smooth_limitBaseChange D c i₁ X₀ Y₀ a hc
  rw [key] at hj
  -- the field generated by the stage `j`
  let s : Finset k := j.unop
  let F : IntermediateField ℚ k := IntermediateField.adjoin ℚ (s : Set k)
  have hF : F.FG := ⟨s, rfl⟩
  have hle : ∀ x : Algebra.adjoin ℤ (s : Set k), (x : k) ∈ F := fun x =>
    Algebra.adjoin_le (S := F.toSubalgebra.restrictScalars ℤ)
      (IntermediateField.subset_adjoin ℚ (s : Set k)) x.2
  let φ : Algebra.adjoin ℤ (s : Set k) →+* F :=
    (Algebra.adjoin ℤ (s : Set k)).val.toRingHom.codRestrict F hle
  let q : Spec (.of F) ⟶ D.obj j := Spec.map (CommRingCat.ofHom φ)
  let sF : Spec (.of k) ⟶ Spec (.of F) := Spec.map (CommRingCat.ofHom (algebraMap F k))
  have hcq : sF ≫ q = c.π.app j :=
    (Spec.map_comp (CommRingCat.ofHom φ) (CommRingCat.ofHom (algebraMap F k))).symm.trans rfl
  let Q : Spec (.of F) ⟶ D.obj i₁ := q ≫ D.map k'
  have hQ : sF ≫ Q = c.π.app i₁ := by
    change sF ≫ (q ≫ D.map k') = _
    rw [← Category.assoc, hcq]
    exact c.w k'
  -- the model over `F`
  let XF : Scheme.{v} := pullback f₁ Q
  let hXF : XF.Over (Spec (.of F)) := ⟨pullback.snd f₁ Q⟩
  have hsmF : Smooth (pullback.snd f₁ Q) := by
    have hcomm : pullback.fst f₁ Q ≫ f₁ = (pullback.snd f₁ Q ≫ q) ≫ D.map k' := by
      rw [pullback.condition, Category.assoc]
    have sq : IsPullback (pullback.lift (pullback.fst f₁ Q) (pullback.snd f₁ Q ≫ q) hcomm)
        (pullback.snd f₁ Q) (pullback.snd f₁ (D.map k')) q := by
      refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _)
        (IsPullback.of_hasPullback f₁ (D.map k'))
      rw [pullback.lift_fst]
      exact IsPullback.of_hasPullback f₁ Q
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Smooth) sq hj
  have : IsProper (XF ↘ Spec (.of F)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsProper)
      (IsPullback.of_hasPullback f₁ Q) hpr₁
  -- the isomorphism `X ≅ X_F ×_F k`
  have hcond : g₁ ≫ f₁ = (f ≫ sF) ≫ Q :=
    hpb₁.w.trans ((congrArg (f ≫ ·) hQ).symm.trans (Category.assoc f sF Q).symm)
  have hX : IsPullback (pullback.lift g₁ (f ≫ sF) hcond) f (pullback.snd f₁ Q) sF := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f₁ Q)
    rw [pullback.lift_fst]
    exact hQ ▸ hpb₁
  let e : X ≅ pullback (XF ↘ Spec (.of F)) sF := hX.isoPullback
  have he₁ : e.hom ≫ pullback.snd _ _ = X ↘ Spec (.of k) := hX.isoPullback_hom_snd
  have he₂ : (e.hom ≫ pullback.fst _ _) ≫ pullback.fst f₁ Q = g₁ := by
    rw [show e.hom ≫ pullback.fst _ _ = pullback.lift g₁ (f ≫ sF) hcond from
      hX.isoPullback_hom_fst, pullback.lift_fst]
  -- the polarization over `F`
  let LF : XF.Modules := (Scheme.Modules.pullback (pullback.fst f₁ Q)).obj L₁
  have hLF : SheafOfModules.IsInvertible XF.presheaf XF.ringCatSheaf.2 LF :=
    have := hL₁
    Stacks.RingedSpace.algebraicGeometryIsInvertible_modulePullback
      (pullback.fst f₁ Q).toLRSHom.toShHom L₁
  have hinvLF : Stacks.Ample.IsInvertibleModule XF LF := hLF
  have hamp₁' : Scheme.Modules.IsAmple X₁ L₁ :=
    (Stacks.AmpleBridge.isAmple_iff_isAmple X₁ L₁).mp
      ((Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple f₁ L₁).mp hamp₁)
  have : IsAffineHom (pullback.fst f₁ Q) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom)
      (IsPullback.of_hasPullback f₁ Q).flip inferInstance
  have : CompactSpace XF := QuasiCompact.compactSpace_of_compactSpace (pullback.snd f₁ Q)
  obtain ⟨hprojF, hampMMP⟩ := isProjectiveMorphism_and_isAmple_of_isAmple F LF
    ((Stacks.AmpleBridge.isAmple_iff_isAmple XF LF).mpr
      (Scheme.Modules.isAmple_pullback_of_isAffineHom (pullback.fst f₁ Q) L₁ hamp₁'))
  refine ⟨F, hF, XF, hXF, hsmF, hprojF, LF, hLF, hampMMP, e, he₁, ⟨?_⟩⟩
  exact eL.symm ≪≫ eqToIso (congrArg (fun g => (Scheme.Modules.pullback g).obj L₁) he₂.symm) ≪≫
    ((Scheme.Modules.pullbackComp (e.hom ≫ pullback.fst _ _) (pullback.fst f₁ Q)).app L₁).symm

/-- A scheme over a field `F` whose base change to an algebraically closed extension `k` is
integral is geometrically integral over `F`. -/
private theorem geometricallyIntegral_of_isIntegral_pullback_of_isAlgClosed
    {F k : Type v} [Field F] [Field k] [Algebra F k] [IsAlgClosed k]
    {XF : Scheme.{v}} (f : XF ⟶ Spec (.of F))
    (h : IsIntegral (pullback f (Spec.map (CommRingCat.ofHom (algebraMap F k))))) :
    GeometricallyIntegral f := by
  have : GeometricallyIrreducible
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap F k)))) :=
    geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed k _ _
  have : GeometricallyReduced
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap F k)))) :=
    geometricallyReduced_of_isReduced _
  have := (geometricallyIrreducible_iff_baseChange_fieldExtension F k f).2 ‹_›
  have := (geometricallyReduced_iff_baseChange_fieldExtension F k f).2 ‹_›
  exact .of_geometricallyReduced_of_geometricallyIrreducible f

/-- **A polarized smooth projective variety descends to a finitely generated field.** Let `k`
be algebraically closed of characteristic zero, `X` smooth, projective and integral over `k`,
and `L` an ample invertible sheaf on `X`. Then there are an intermediate field `F` of `ℚ ⊆ k`,
finitely generated over `ℚ`, a smooth projective geometrically integral `F`-scheme `X_F`, an
ample invertible sheaf `L_F` on `X_F`, an isomorphism `e : X ≅ X_F ×_{Spec F} Spec k` over
`Spec k`, and an isomorphism `L ≅ (pr₁ ∘ e)^* L_F`. -/
@[mmp "lem_mmp_smooth_polarized_finitely_generated_field"]
public theorem exists_fg_intermediateField_isoBaseChange_of_isAmple
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))] [IsIntegral X]
    [Smooth (X ↘ Spec (.of k))] (hproj : IsProjectiveMorphism (X ↘ Spec (.of k)))
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hL : MMP.Intersection.IsAmple k L) :
    ∃ (F : IntermediateField ℚ k), F.FG ∧
      ∃ (XF : Scheme.{u}) (_ : XF.Over (Spec (.of F))),
        Smooth (XF ↘ Spec (.of F)) ∧ IsProjectiveMorphism (XF ↘ Spec (.of F)) ∧
        GeometricallyIntegral (XF ↘ Spec (.of F)) ∧
        ∃ (LF : XF.Modules) (_ : SheafOfModules.IsInvertible XF.presheaf XF.ringCatSheaf.2 LF),
          MMP.Intersection.IsAmple F LF ∧
          ∃ e : X ≅ pullback (XF ↘ Spec (.of F))
              (Spec.map (CommRingCat.ofHom (algebraMap F k))),
            e.hom ≫ pullback.snd _ _ = X ↘ Spec (.of k) ∧
            Nonempty (L ≅ (Scheme.Modules.pullback (e.hom ≫ pullback.fst _ _)).obj LF) := by
  obtain ⟨F, hF, XF, hXF, hsm, hpr, LF, hLFi, hLF, e, he, hLe⟩ :=
    exists_fg_model_of_isAmple k X hproj L hL
  have : Nonempty ↥(pullback (XF ↘ Spec (.of F))
      (Spec.map (CommRingCat.ofHom (algebraMap F k)))) :=
    ⟨e.hom (Nonempty.some (inferInstance : Nonempty X))⟩
  have hint : IsIntegral (pullback (XF ↘ Spec (.of F))
      (Spec.map (CommRingCat.ofHom (algebraMap F k)))) := isIntegral_of_isOpenImmersion e.inv
  refine ⟨F, hF, XF, hXF, hsm, hpr, ?_, LF, hLFi, hLF, e, he, hLe⟩
  exact geometricallyIntegral_of_isIntegral_pullback_of_isAlgClosed _ hint

end MMP.Descent

end
