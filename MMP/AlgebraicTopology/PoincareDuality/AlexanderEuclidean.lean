module

public import MMP.AlgebraicTopology.PoincareDuality.EmbeddingIndependence.Convex

/-!
# Poincaré duality for `ℝⁿ`, in every universe

`PoincareAlexander.dualityAt_euclidean` is stated for `ℝⁿ = Fin n → ℝ`, so for coefficients
`R : Type` only (Borel–Moore homology takes the space and the ring in one universe). Here the same
statement is proved for `E = ULift.{u} (Fin n → ℝ)` and `R : Type u`, so that the induction on open
sets applies to manifolds and coefficients in an arbitrary universe:

* `H_q E = 0` for `q < n`, along the exhaustion of `E` by closed balls, as for `ℝⁿ`
  (`borelMooreHomology.isZero_ulift_euclidean_of_lt`); the local vanishing at `0` is transported
  from `ℝⁿ` along the homeomorphism `E ≃ₜ ℝⁿ` (`SingularChain.RelVanishing.homeomorph`);
* `H_q E = 0` for `q > n` (`borelMooreHomology.isZero_of_dim_lt`, `E` charted on itself);
* `H^p E = 0` for `p > 0` and the degree-`0` duality: the straight-line contraction.

## Main results

* `MMP.SingularChain.RelVanishing.homeomorph`: relative vanishing is invariant under
  homeomorphism.
* `MMP.borelMooreHomology.isZero_ulift_euclidean_of_lt`: `H_q E = 0` for `q < n`.
* `MMP.PoincareAlexander.dualityAt_ulift_euclidean`: Poincaré duality holds at `E`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Set Topology Function

universe u

namespace MMP

open MMP

namespace SingularChain

open MMP.SingularChain

variable {R : Type*} [CommRing R] {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]

/-- `H_{m+1}(Y, Y - K) = 0` is invariant under homeomorphism. -/
theorem _root_.MMP.SingularChain.RelVanishing.homeomorph (φ : Y ≃ₜ Z) {m : ℕ} {K : Set Y}
    (h : RelVanishing R Y m K) :
    RelVanishing R Z m (φ.symm ⁻¹' K) := by
  intro c hc
  have h1 : MapsTo (φ.symm : C(Z, Y)) (φ.symm ⁻¹' K)ᶜ Kᶜ := fun x hx ↦ hx
  have h2 : MapsTo (φ : C(Y, Z)) Kᶜ (φ.symm ⁻¹' K)ᶜ := fun x hx ↦ by
    simpa using hx
  obtain ⟨w, hw⟩ := h (postcomp R (φ.symm : C(Z, Y)) (m + 1) c)
    (by rw [← postcomp_bd]; exact postcomp_mem_inside _ h1 hc)
  refine ⟨postcomp R (φ : C(Y, Z)) (m + 2) w, ?_⟩
  have := postcomp_mem_inside (R := R) (n := m + 1) _ h2 hw
  rwa [map_sub, postcomp_bd, postcomp_comp, show (φ : C(Y, Z)).comp (φ.symm : C(Z, Y)) =
    ContinuousMap.id Z by ext; simp, postcomp_id] at this

end SingularChain

/-- `ULift.{u} (Fin n → ℝ)`, a copy of `ℝⁿ` in the universe `u`. -/
abbrev ULiftEuclidean (n : ℕ) : Type u := ULift.{u} (Fin n → ℝ)

namespace SingularChain

open MMP.SingularChain

variable {R : Type*} [CommRing R]

/-- `H_{k+1}(E, E - {0}) = 0` for `k + 1 < n`, `E = ULift (Fin n → ℝ)`. -/
theorem relVanishing_ulift_singleton_zero_low {n k : ℕ} (hk : k + 1 < n) :
    RelVanishing R (ULiftEuclidean.{u} n) k {0} := by
  have h := (relVanishing_singleton_zero_low (R := R) n k hk).homeomorph
    (Homeomorph.ulift.{u}).symm
  convert h using 1
  ext x
  simp only [mem_singleton_iff, Homeomorph.symm_symm, mem_preimage]
  exact ⟨fun hx ↦ by subst hx; rfl, fun hx ↦ ULift.ext hx⟩

/-- `H_{k+1}(E, E - B̄(0, r)) = 0` for `k + 1 < n` (`r ≥ 0`, `E = ULift (Fin n → ℝ)`). -/
theorem relVanishing_ulift_closedBall_low {n k : ℕ} (hk : k + 1 < n) {r : ℝ} (hr : 0 ≤ r) :
    RelVanishing R (ULiftEuclidean.{u} n) k (Metric.closedBall 0 r) := by
  intro c hc
  refine isRelBoundary_of_convex (convex_closedBall 0 r) Metric.isBounded_closedBall
    (Metric.mem_closedBall_self hr) hc ?_
  refine relVanishing_ulift_singleton_zero_low hk c (inside_mono k ?_ hc)
  rw [compl_subset_compl, singleton_subset_iff]
  exact Metric.mem_closedBall_self hr

end SingularChain

namespace borelMooreHomology

open MMP.borelMooreHomology

open LocallyFiniteChain SingularChain

variable (R : Type u) [CommRing R]

/-- The exhaustion of `E = ULift (Fin n → ℝ)` by the closed balls `B̄(0, j + 1)`. -/
abbrev uliftEuclideanBall (n : ℕ) (j : ℕ) : Set (TopCat.of (ULiftEuclidean.{u} n)) :=
  Metric.closedBall (0 : ULiftEuclidean.{u} n) (j + 1)

/-- Each closed ball `B̄(0, j + 1)` in `E = ULift (Fin n → ℝ)` is compact. -/
lemma isCompact_uliftEuclideanBall (n j : ℕ) : IsCompact (uliftEuclideanBall.{u} n j) :=
  isCompact_closedBall _ _

/-- The closed balls `B̄(0, j + 1)` increase with `j`. -/
lemma monotone_uliftEuclideanBall (n : ℕ) : Monotone (uliftEuclideanBall.{u} n) :=
  fun i j hij ↦
    Metric.closedBall_subset_closedBall (by exact_mod_cast Nat.add_le_add_right hij 1)

/-- Every point of `E = ULift (Fin n → ℝ)` has some ball `B̄(0, j + 1)` as a neighbourhood. -/
lemma exists_uliftEuclideanBall_mem_nhds (n : ℕ) (x : TopCat.of (ULiftEuclidean.{u} n)) :
    ∃ j, uliftEuclideanBall n j ∈ 𝓝 x := by
  obtain ⟨j, hj⟩ := exists_nat_gt ‖(x : ULiftEuclidean.{u} n)‖
  refine ⟨j, Metric.closedBall_mem_nhds_of_mem ?_⟩
  rw [mem_ball_zero_iff]
  linarith

/-- The Mittag-Leffler condition `RelSurjBM` holds for consecutive balls
`B̄(0, j + 1) ⊆ B̄(0, j + 2)` in `E = ULift (Fin n → ℝ)`, in every degree `m`. -/
lemma relSurjBM_uliftEuclideanBall (n m j : ℕ) :
    RelSurjBM (TopCat.of (ULiftEuclidean.{u} n)) R (ModuleCat.of R R) m
      (uliftEuclideanBall n j) (uliftEuclideanBall n (j + 1)) :=
  relSurjBM_of_relSurj (relSurj_closedBall m (by positivity) (by push_cast; linarith))

/-- `H_{k+1}(E; R) = 0` for `k + 1 < n`, `E = ULift (Fin n → ℝ)`. -/
theorem isZero_ulift_euclidean_succ_of_lt {n k : ℕ} (hk : k + 1 < n) :
    IsZero (borelMooreHomology R (ModuleCat.of R R) (TopCat.of (ULiftEuclidean.{u} n))
      ((k + 1 : ℕ) : ℤ)) :=
  isZero_of_exhaustion (uliftEuclideanBall n) (isCompact_uliftEuclideanBall n)
    (monotone_uliftEuclideanBall n) (exists_uliftEuclideanBall_mem_nhds n) k
    (fun j ↦ relVanishingBM_of_relVanishing
      (relVanishing_ulift_closedBall_low hk (by positivity)))
    (fun j ↦ relSurjBM_uliftEuclideanBall R n (k + 1) j)

/-- `H_0(E; R) = 0` for `n ≥ 1`, `E = ULift (Fin n → ℝ)`. -/
theorem isZero_ulift_euclidean_zero {n : ℕ} (hn : 1 ≤ n) :
    IsZero (borelMooreHomology R (ModuleCat.of R R) (TopCat.of (ULiftEuclidean.{u} n))
      ((0 : ℕ) : ℤ)) := by
  haveI : Nontrivial (ULiftEuclidean.{u} n) := by
    haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    infer_instance
  set X := TopCat.of (ULiftEuclidean.{u} n)
  refine IsZero.of_iso ?_ (borelMooreHomologyIsoOfNat R (ModuleCat.of R R) X 0)
  refine HomologicalComplex.ExactAt.isZero_homology (K := borelMooreChainComplex R _ X)
    (i := 0) ?_
  rw [HomologicalComplex.exactAt_iff' _ 1 0 0 (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  suffices H : ∀ z : (borelMooreChainComplex R (ModuleCat.of R R) X).X 0,
      ∃ w : (borelMooreChainComplex R (ModuleCat.of R R) X).X 1,
        ((borelMooreChainComplex R (ModuleCat.of R R) X).d 1 0).hom w = z from
    fun z _ ↦ H z
  intro z
  have hz : ∀ j, ∃ w : (borelMooreChainComplex R (ModuleCat.of R R) X).X 1,
      IsOffChain (uliftEuclideanBall n j)
        (z - ((borelMooreChainComplex R (ModuleCat.of R R) X).d 1 0).hom w) := by
    intro j
    set K := uliftEuclideanBall n j
    have hK : IsCompact K := isCompact_uliftEuclideanBall n j
    set t := truncChain K z
    have ht := finite_support_truncChain hK z
    obtain ⟨w, hw⟩ := isRelBoundary_zero_of_isCompact (R := R) hK (toFinsupp t ht)
    refine ⟨ofFinsupp w, ?_⟩
    have h1 : IsOffChain K (t - ((borelMooreChainComplex R _ X).d 1 0).hom (ofFinsupp w)) := by
      rw [d_ofFinsupp, ← ofFinsupp_toFinsupp t ht, ← ofFinsupp_sub, isOffChain_ofFinsupp_iff]
      exact hw
    have := (isOffChain_sub_truncChain K z).add h1
    convert this using 1
    abel
  obtain ⟨w, hw⟩ := exists_d_eq_of_exhaustion (uliftEuclideanBall n)
    (isCompact_uliftEuclideanBall n) (monotone_uliftEuclideanBall n)
    (exists_uliftEuclideanBall_mem_nhds n) (m := 0) z hz
    (fun j ↦ relSurjBM_uliftEuclideanBall R n 0 j)
  exact ⟨w, hw⟩

/-- **`H_q(E; R) = 0` for `q < n`**, `E = ULift (Fin n → ℝ)`. -/
theorem isZero_ulift_euclidean_of_lt {n q : ℕ} (hq : q < n) :
    IsZero (borelMooreHomology R (ModuleCat.of R R) (TopCat.of (ULiftEuclidean.{u} n))
      (q : ℤ)) := by
  rcases q with _ | k
  · exact isZero_ulift_euclidean_zero R (by omega)
  · exact isZero_ulift_euclidean_succ_of_lt R hq

end borelMooreHomology

namespace PoincareAlexander

open MMP.PoincareAlexander

open SingularChain SingularCochain BorelMooreCross BorelMooreCap

variable {R : Type u} [CommRing R]

/-- The straight-line contraction of `E = ULift (Fin n → ℝ)` to `0`. -/
def uliftEuclideanContraction (n : ℕ) :
    TopCat.Homotopy (𝟙 (TopCat.of (ULiftEuclidean.{u} n)))
      (TopCat.ofHom (ContinuousMap.const (TopCat.of (ULiftEuclidean.{u} n)) 0)) where
  toFun p := (1 - (p.1 : ℝ)) • (p.2 : ULiftEuclidean.{u} n)
  continuous_toFun := by fun_prop
  map_zero_left x := by simp
  map_one_left x := by simp

/-- `H^p E = 0` for `p > 0`, `E = ULift (Fin n → ℝ)`. -/
lemma subsingleton_relCohomology_ulift_euclidean (n : ℕ) {p : ℕ} (hp : 0 < p) :
    Subsingleton (relCohomology R (∅ : Set (TopCat.of (ULiftEuclidean.{u} n))) p) := by
  refine ⟨fun a b ↦ ?_⟩
  obtain ⟨φ, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨ψ, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  rw [mk_eq_zero_of_homotopy_const (0 : TopCat.of (ULiftEuclidean.{u} n))
      (uliftEuclideanContraction n) hp φ,
    mk_eq_zero_of_homotopy_const (0 : TopCat.of (ULiftEuclidean.{u} n))
      (uliftEuclideanContraction n) hp ψ]

/-- `H_q E = 0` for `q ≠ n`, in the explicit model `HomQ`, `E = ULift (Fin n → ℝ)`. -/
lemma subsingleton_homQ_ulift_euclidean {n q : ℕ} (hq : q ≠ n) :
    Subsingleton (HomQ (R := R) (TopCat.of (ULiftEuclidean.{u} n)) q) := by
  have hz : IsZero (borelMooreHomology R (ModuleCat.of R R)
      (TopCat.of (ULiftEuclidean.{u} n)) q) := by
    rcases lt_or_gt_of_ne hq with h | h
    · exact borelMooreHomology.isZero_ulift_euclidean_of_lt R h
    · letI : ChartedSpace (ULiftEuclidean.{u} n) (ULiftEuclidean.{u} n) := chartedSpaceSelf _
      exact borelMooreHomology.isZero_of_dim_lt R
        ((Pi.basisFun ℝ (Fin n)).map (ULift.moduleEquiv (R := ℝ)).symm) (by exact_mod_cast h)
  haveI := ModuleCat.subsingleton_of_isZero hz
  exact (homologyEquiv R (TopCat.of (ULiftEuclidean.{u} n)) q).symm.injective.subsingleton

/-- **Poincaré duality for `ℝⁿ`, in the universe `u`**: for a locally finite `n`-cycle `z` of
`E = ULift (Fin n → ℝ)` such that `r ↦ r [z]` is a bijection `R ≃ H_n E`, `DualityAt E n z`. -/
theorem dualityAt_ulift_euclidean (n : ℕ) (z : Cyc (R := R) (TopCat.of (ULiftEuclidean.{u} n)) n)
    (hz : Bijective fun r : R ↦
      r • (Submodule.Quotient.mk z : HomQ (R := R) (TopCat.of (ULiftEuclidean.{u} n)) n)) :
    DualityAt (TopCat.of (ULiftEuclidean.{u} n)) n z := by
  refine ⟨fun p q h ↦ ?_, fun p hp ↦ subsingleton_relCohomology_ulift_euclidean n (by omega),
    fun q hq ↦ subsingleton_homQ_ulift_euclidean (by omega)⟩
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · obtain rfl : n = q := by omega
    exact bijective_capHomQ_zero_of_homotopy_const (0 : TopCat.of (ULiftEuclidean.{u} n))
      (uliftEuclideanContraction n) n h z hz
  · haveI := subsingleton_relCohomology_ulift_euclidean (R := R) n hp
    haveI := subsingleton_homQ_ulift_euclidean (R := R) (n := n) (q := q) (by omega)
    exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun y ↦ ⟨0, Subsingleton.elim _ _⟩⟩

end PoincareAlexander

end MMP
