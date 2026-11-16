module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.FiniteGeneration
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Intersection.CurveDegreeAdditive
import MMP.AlgebraicGeometry.Singularities.RealKltPolytope

/-!
# A rational decomposition of a real klt adjoint preserving all null curves

Let `X` be a normal `ℚ`-factorial projective variety over an algebraically closed field of
characteristic zero, `K` a canonical divisor of `X` and `B` an effective real boundary with
`(X, B)` klt; put `D = K + B`. Then `D` is a convex combination `D = ∑ᵢ rᵢ Dᵢ`, `rᵢ > 0`,
`∑ᵢ rᵢ = 1`, of adjoints `Dᵢ = K + Bᵢ` of effective rational klt boundaries `Bᵢ` lying in the
smallest rational affine hull of `B`, with a common `m > 0` such that every `mDᵢ` is an integral
Cartier divisor, and every curve `C` with `D · C = 0` has `Dᵢ · C = 0` for all `i`.

The proof enumerates the prime divisors `p₀, …, p_{r-1}` of the support of `B`, so that `B` is
a point `δ ∈ ℝ^r`. A rational klt polytope `P = conv V` through `δ`
(`MMP.Fourfold.exists_rationalPolytope_isKltPair_of_isRealKltPair`), with affine hull the smallest
rational affine subspace `W ∋ δ` and `δ` in its relative interior, writes `δ` as a convex
combination of all of `V` with positive weights; the points of `V` are the `Bᵢ`, and a common
multiple of their Cartier indices (which exist by `ℚ`-factoriality) is `m`. The degree `deg_C`
is additive on Cartier divisors, so its real extension to real combinations of Cartier divisors
depends only on the underlying real divisor: after any `ℚ`-linear functional `ℝ → ℚ`, a real
relation between finitely many integral divisors becomes an integral one. Writing `K` and the
`pⱼ` as rational combinations of Cartier divisors, `x ↦ (K + ∑ⱼ xⱼ pⱼ) · C` is a rational affine
form; it vanishes at `δ`, hence on `W`, hence at every `Bᵢ`.

## Main results

* `MMP.Fourfold.exists_convexCombination_isKltPair_of_isRealKltPair`

## Implementation notes

The real intersection number `D · C` is computed from any expression `L = ∑ⱼ cⱼ Eⱼ` of `D` as a
real combination of Cartier divisors `Eⱼ`, as `∑ⱼ cⱼ deg_C 𝒪_X(Eⱼ)`; the null-curve clause is
asserted for every such expression, so it does not depend on the choice. The rational
intersection number `Dᵢ · C` vanishes exactly when the degree of the integral Cartier divisor
`mDᵢ` on `C` does, and it is stated in that form. The smallest rational affine hull is
`MMP.Fourfold.IsInSmallestRationalAffineHull`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 2.34
-/

@[expose] public section

universe u

open AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori

/-- A point of the relative interior of the convex hull of a finite set `V` is a convex
combination of all the points of `V` with positive weights. -/
private theorem exists_pos_weights_of_mem_intrinsicInterior {E : Type*} [AddCommGroup E]
    [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (V : Finset E) {x : E} (hx : x ∈ intrinsicInterior ℝ (convexHull ℝ (V : Set E))) :
    ∃ w : E → ℝ, (∀ y ∈ V, 0 < w y) ∧ ∑ y ∈ V, w y = 1 ∧ ∑ y ∈ V, w y • y = x := by
  have hVne : V.Nonempty :=
    Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ⟨x, intrinsicInterior_subset hx⟩)
  set n : ℝ := (V.card : ℝ)
  have hn : 0 < n := by simp [n, hVne.card_pos]
  set b : E := ∑ y ∈ V, (1 / n) • y
  have hb : b ∈ convexHull ℝ (V : Set E) :=
    Finset.mem_convexHull'.mpr ⟨fun _ => 1 / n, fun _ _ => by positivity,
      by simp [n]; field_simp, rfl⟩
  set A := affineSpan ℝ (convexHull ℝ (V : Set E))
  have hbA : b ∈ A := subset_affineSpan ℝ _ hb
  obtain ⟨y, hy, rfl⟩ := mem_intrinsicInterior.mp hx
  let f : ℝ → A := fun t => ⟨AffineMap.lineMap b (y : E) (1 + t),
    AffineMap.lineMap_mem _ hbA y.2⟩
  have hf : Continuous f := by
    refine Continuous.subtype_mk ?_ _
    simp only [AffineMap.lineMap_apply_module']
    fun_prop
  have hf0 : f 0 = y := by ext; simp [f]
  have hU : f ⁻¹' interior ((↑) ⁻¹' convexHull ℝ (V : Set E)) ∈ nhds (0 : ℝ) :=
    hf.continuousAt.preimage_mem_nhds (hf0 ▸ isOpen_interior.mem_nhds hy)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hU
  set ε := δ / 2
  have hε : 0 < ε := by positivity
  have hεmem : ((f ε : A) : E) ∈ convexHull ℝ (V : Set E) := by
    have := interior_subset (hball (show ε ∈ Metric.ball 0 δ by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hε]
      simp only [ε]
      linarith))
    exact this
  obtain ⟨w', hw'0, hw'1, hw'⟩ := Finset.mem_convexHull'.mp hεmem
  refine ⟨fun z => (w' z + ε / n) / (1 + ε), fun z hz => by
    have := hw'0 z hz
    positivity, ?_, ?_⟩
  · rw [← Finset.sum_div, Finset.sum_add_distrib, hw'1]
    simp [n]
    field_simp
  · have hfε : ((f ε : A) : E) = (y : E) + ε • ((y : E) - b) := by
      simp only [f, AffineMap.lineMap_apply_module']
      module
    have hb' : ∑ i ∈ V, (ε / n) • i = ε • b := by
      simp only [b, Finset.smul_sum, smul_smul]
      refine Finset.sum_congr rfl fun _ _ => by ring_nf
    simp only [div_eq_mul_inv _ (1 + ε), mul_comm _ (1 + ε)⁻¹, mul_smul, add_smul,
      ← Finset.smul_sum, Finset.sum_add_distrib]
    rw [hw', hfε, hb', show (y : E) + ε • ((y : E) - b) + ε • b = (1 + ε) • (y : E) by module,
      smul_smul, inv_mul_cancel₀ (by positivity), one_smul]

/-- Let `H` be a group of integral finitely supported functions and `δ : H → ℤ` additive. A
real combination `∑ c_F F` of members of `H` which vanishes as a real function has
`∑ c_F δ(F) = 0`: the real extension of `δ` is well defined. -/
private theorem sum_mul_eq_zero_of_forall_sum_mul_apply_eq_zero {α : Type*}
    {H : AddSubgroup (α →₀ ℤ)} (δ : H →+ ℤ) (L : H →₀ ℝ)
    (hL : ∀ a, (L.sum fun F c => c * ((F : α →₀ ℤ) a : ℝ)) = 0) :
    (L.sum fun F c => c * (δ F : ℝ)) = 0 := by
  classical
  refine (Module.forall_dual_apply_eq_zero_iff ℚ _).mp fun φ => ?_
  have key : ∀ x : ℝ, ∀ n : ℤ, φ (x * n) = φ x * n := fun x n => by
    rw [mul_comm, ← zsmul_eq_mul, map_zsmul, zsmul_eq_mul, mul_comm]
  set a : H → ℚ := fun F => φ (L F)
  have hφ : ∀ g : H → ℤ, φ (L.sum fun F c => c * (g F : ℝ)) = ∑ F ∈ L.support, a F * g F := by
    intro g
    rw [Finsupp.sum, map_sum]
    exact Finset.sum_congr rfl fun F _ => key _ _
  set d : ℕ := ∏ F ∈ L.support, (a F).den
  have hd : (d : ℚ) ≠ 0 := by
    simp only [d, Nat.cast_prod]
    exact Finset.prod_ne_zero_iff.mpr fun F _ => Nat.cast_ne_zero.mpr (a F).den_pos.ne'
  set N : H → ℤ := fun F => (a F).num * ((d / (a F).den : ℕ) : ℤ)
  have hN : ∀ F ∈ L.support, (N F : ℚ) = d * a F := by
    intro F hF
    have hdvd : (a F).den ∣ d := Finset.dvd_prod_of_mem _ hF
    have : ((a F).den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (a F).den_pos.ne'
    simp only [N, Int.cast_mul, Int.cast_natCast, Nat.cast_div hdvd this]
    nth_rw 3 [← Rat.num_div_den (a F)]
    field_simp
  have hT : ∑ F ∈ L.support, N F • F = 0 := by
    ext a0
    have h1 : ∑ F ∈ L.support, a F * ((F : α →₀ ℤ) a0 : ℚ) = 0 := by
      rw [← hφ (fun F => (F : α →₀ ℤ) a0), hL a0, map_zero]
    have hsum : (((∑ F ∈ L.support, N F • F : H) : α →₀ ℤ) a0 : ℚ) =
        d * ∑ F ∈ L.support, a F * ((F : α →₀ ℤ) a0 : ℚ) := by
      rw [AddSubgroup.val_finsetSum, Finsupp.finsetSum_apply, Int.cast_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun F hF => ?_
      rw [AddSubgroup.coe_zsmul, Finsupp.smul_apply, smul_eq_mul, Int.cast_mul, hN F hF]
      ring
    rw [h1, mul_zero] at hsum
    exact_mod_cast hsum
  have h2 : ((δ (∑ F ∈ L.support, N F • F) : ℤ) : ℚ) = d * ∑ F ∈ L.support, a F * δ F := by
    rw [map_sum, Int.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun F hF => ?_
    rw [map_zsmul, smul_eq_mul, Int.cast_mul, hN F hF]
    ring
  rw [hT, map_zero, Int.cast_zero, eq_comm, mul_eq_zero] at h2
  rw [hφ]
  exact h2.resolve_left hd

section Divisors

variable {X : Scheme.{u}} {M : Type*} [AddCommMonoid M] {r : ℕ}
  {p : Fin r → MMP.Mori.PrimeDivisor X}

private theorem sum_single_apply_self (hp : Function.Injective p) (x : Fin r → M) (j : Fin r) :
    (∑ i, Finsupp.single (p i) (x i)) (p j) = x j := by
  classical
  rw [Finsupp.finsetSum_apply]
  simp [Finsupp.single_apply, hp.eq_iff]

private theorem sum_single_apply_of_notMem (x : Fin r → M) {P : MMP.Mori.PrimeDivisor X}
    (hP : P ∉ Set.range p) : (∑ i, Finsupp.single (p i) (x i)) P = 0 := by
  classical
  rw [Finsupp.finsetSum_apply]
  exact Finset.sum_eq_zero fun i _ => Finsupp.single_eq_of_ne (fun h => hP ⟨i, h.symm⟩)

/-- A rational linear form `∑_P c_P Φ_P` on divisors supported on the `pⱼ` is the sum over the
`pⱼ`. -/
private theorem sum_mul_coeff_eq (hp : Function.Injective p)
    (c : MMP.Mori.PrimeDivisor X →₀ ℚ)
    (Φ : RDivisor X) (hΦ : ∀ P, P ∉ Set.range p → Φ P = 0) :
    (c.sum fun P cP => (cP : ℝ) * Φ.coeff P) = ∑ j, (c (p j) : ℝ) * Φ (p j) := by
  classical
  have h1 : (c.sum fun P cP => (cP : ℝ) * Φ.coeff P) =
      ∑ P ∈ c.support ∪ Finset.univ.image p, (c P : ℝ) * Φ P := by
    refine Finset.sum_subset Finset.subset_union_left fun P _ hP => ?_
    simp [Finsupp.notMem_support_iff.mp hP]
  have h2 : ∑ j, (c (p j) : ℝ) * Φ (p j) =
      ∑ P ∈ c.support ∪ Finset.univ.image p, (c P : ℝ) * Φ P := by
    rw [← Finset.sum_image (f := fun P => (c P : ℝ) * Φ P) (fun a _ b _ h => hp h)]
    refine Finset.sum_subset Finset.subset_union_right fun P _ hP => ?_
    rw [hΦ P fun ⟨j, hj⟩ => hP (hj ▸ Finset.mem_image_of_mem p (Finset.mem_univ j)), mul_zero]
  rw [h1, h2]

end Divisors

/-- The coefficients of the Weil divisor `∑ c_F F` underlying a real combination of Cartier
divisors. -/
private theorem toDivisorWithCoeffs_apply {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    (L : CartierDivisorWithCoeffs ℝ X) (P : MMP.Mori.PrimeDivisor X) :
    CartierDivisorWithCoeffs.toDivisorWithCoeffs L P =
      L.sum fun F c => c * ((F : Divisor X) P : ℝ) := by
  rw [CartierDivisorWithCoeffs.toDivisorWithCoeffs, Finsupp.liftAddHom_apply, Finsupp.sum_apply]
  rfl

/-- The real extension of an additive function `δ` on Cartier divisors to real combinations of
Cartier divisors depends only on the underlying real Weil divisor. -/
private theorem linearCombination_eq_of_toDivisorWithCoeffs_eq {X : Scheme.{u}}
    [IsLocallyNoetherian X] [IsNormal X] (δ : Divisor.cartierSubgroup (X := X) →+ ℤ)
    {L₁ L₂ : CartierDivisorWithCoeffs ℝ X}
    (h : CartierDivisorWithCoeffs.toDivisorWithCoeffs L₁ =
      CartierDivisorWithCoeffs.toDivisorWithCoeffs L₂) :
    Finsupp.linearCombination ℝ (fun F => (δ F : ℝ)) L₁ =
      Finsupp.linearCombination ℝ (fun F => (δ F : ℝ)) L₂ := by
  rw [← sub_eq_zero, ← map_sub, Finsupp.linearCombination_apply]
  simp_rw [smul_eq_mul]
  refine sum_mul_eq_zero_of_forall_sum_mul_apply_eq_zero δ _ fun P => ?_
  rw [← toDivisorWithCoeffs_apply, map_sub, h, sub_self, Finsupp.zero_apply]

private theorem exists_fin_pos_weights_of_mem_intrinsicInterior {r : ℕ}
    (V : Finset (Fin r → ℚ)) {δ : Fin r → ℝ} (hδ : δ ∈ intrinsicInterior ℝ
      (convexHull ℝ ((fun v i => (v i : ℝ)) '' (V : Set (Fin r → ℚ))))) :
    ∃ (s : ℕ) (g : Fin s → Fin r → ℚ) (w : Fin s → ℝ), (∀ i, g i ∈ V) ∧ (∀ i, 0 < w i) ∧
      ∑ i, w i = 1 ∧ ∀ j, ∑ i, w i * (g i j : ℝ) = δ j := by
  classical
  set cast : (Fin r → ℚ) → (Fin r → ℝ) := fun v i => (v i : ℝ)
  have hcast : Function.Injective cast := fun v w h =>
    funext fun i => by simpa [cast] using congrFun h i
  rw [show cast '' (V : Set (Fin r → ℚ)) = ((V.image cast : Finset _) : Set _) by simp] at hδ
  obtain ⟨w, hw0, hw1, hwδ⟩ := exists_pos_weights_of_mem_intrinsicInterior _ hδ
  let g : Fin V.card → Fin r → ℚ := fun i => (V.equivFin.symm i : Fin r → ℚ)
  have hgV : ∀ i, g i ∈ V := fun i => (V.equivFin.symm i).2
  have hsumV : ∀ {N : Type} [AddCommMonoid N] (F : (Fin r → ℝ) → N),
      ∑ i, F (cast (g i)) = ∑ y ∈ V.image cast, F y := by
    intro N _ F
    rw [Finset.sum_image (fun a _ b _ h => hcast h), ← Finset.sum_coe_sort V]
    exact Equiv.sum_comp V.equivFin.symm (fun v => F (cast v))
  refine ⟨V.card, g, fun i => w (cast (g i)), hgV,
    fun i => hw0 _ (Finset.mem_image_of_mem _ (hgV i)), (hsumV w).trans hw1,
    fun j => (hsumV fun y => w y * y j).trans ?_⟩
  simpa using congrFun hwδ j

private theorem isInSmallestRationalAffineHull_sum_single {X : Scheme.{u}} {r : ℕ}
    {p : Fin r → MMP.Mori.PrimeDivisor X} (hp : Function.Injective p) {B : RDivisor X}
    (hpB : ∀ j, p j ∈ B.support) (hBp : ∀ P, P ∉ Set.range p → B P = 0) {y : Fin r → ℚ}
    (hy : (fun j => (y j : ℝ)) ∈ rationalAffineHull fun j => B.coeff (p j)) :
    IsInSmallestRationalAffineHull B
      (QDivisor.toRDivisor (∑ j, Finsupp.single (p j) (y j))) := by
  set Bs : QDivisor X := ∑ j, Finsupp.single (p j) (y j)
  have hBs_self : ∀ j, Bs (p j) = y j := fun j => sum_single_apply_self hp _ j
  have hBs_out : ∀ P, P ∉ Set.range p → Bs P = 0 := fun P hP => sum_single_apply_of_notMem _ hP
  have hR : ∀ P, (QDivisor.toRDivisor Bs) P = ((Bs P : ℚ) : ℝ) := fun _ => rfl
  refine ⟨fun P hP => ?_, fun c q hcq => ?_⟩
  · have hP' : Bs P ≠ 0 := fun h => Finsupp.mem_support_iff.mp hP (by rw [hR, h, Rat.cast_zero])
    obtain ⟨j, rfl⟩ : P ∈ Set.range p := not_not.mp fun hr => hP' (hBs_out P hr)
    exact hpB j
  · rw [sum_mul_coeff_eq hp c _ hBp] at hcq
    rw [sum_mul_coeff_eq hp c _ fun P hP => by rw [hR, hBs_out P hP, Rat.cast_zero]]
    have h3 : ∀ j, (QDivisor.toRDivisor Bs) (p j) = ((y j : ℚ) : ℝ) := fun j => by
      rw [hR, hBs_self]
    have := hy ((fun j => c (p j)), -q) (by
      change ∑ j, ((c (p j) : ℚ) : ℝ) * B (p j) + ((-q : ℚ) : ℝ) = 0
      rw [hcq]
      push_cast
      ring)
    change ∑ j, ((c (p j) : ℚ) : ℝ) * ((y j : ℚ) : ℝ) + ((-q : ℚ) : ℝ) = 0 at this
    simp only [h3]
    push_cast at this
    linarith

private theorem exists_isCartier_eq_smul {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (hQ : IsQFactorial sX) (K : Divisor X) {s : ℕ} (Bs : Fin s → QDivisor X) :
    ∃ m : ℕ, 0 < m ∧ ∃ E : Fin s → Divisor X, (∀ i, (E i).IsCartier) ∧
      ∀ i, Divisor.toQDivisor (E i) = (m : ℚ) • (Divisor.toQDivisor K + Bs i) := by
  have hQC : ∀ i, ∃ mi : ℕ, 0 < mi ∧ ∃ D : Divisor X,
      Divisor.toQDivisor D = ((mi : ℤ) • (Divisor.toQDivisor K + Bs i)) ∧ D.IsCartier := fun i =>
    (isQCartier_of_isQFactorial sX hQ _).exists_pos
  choose mi hmi D hD hDc using hQC
  set m : ℕ := ∏ i, mi i
  have hmidvd : ∀ i, mi i ∣ m := fun i => Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  refine ⟨m, Finset.prod_pos fun i _ => hmi i, fun i => ((m / mi i : ℕ) : ℤ) • D i,
    fun i => (hDc i).zsmul _, fun i => ?_⟩
  simp only [map_zsmul, hD i, smul_smul]
  rw [← Int.cast_smul_eq_zsmul ℚ]
  congr 1
  obtain ⟨t, ht⟩ := hmidvd i
  rw [ht, Nat.mul_div_cancel_left _ (hmi i)]
  push_cast
  ring

/-- On a variety where every Weil divisor has a Cartier multiple, the real extension of an
additive function `δ` on Cartier divisors is a rational linear form `t f₂ + ∑ⱼ f₁ⱼ xⱼ` on the
real divisors `t K + ∑ⱼ xⱼ pⱼ`. -/
private theorem exists_linearCombination_eq {X : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] (hQ : ∀ D : Divisor X, ∃ m : ℕ, 0 < m ∧ ((m : ℤ) • D).IsCartier)
    (δ : Divisor.cartierSubgroup (X := X) →+ ℤ) (K : Divisor X) {r : ℕ}
    (p : Fin r → MMP.Mori.PrimeDivisor X) :
    ∃ f : (Fin r → ℚ) × ℚ, ∀ (L : CartierDivisorWithCoeffs ℝ X) (t : ℝ) (x : Fin r → ℝ),
      CartierDivisorWithCoeffs.toDivisorWithCoeffs L =
        t • Divisor.toRDivisor K + ∑ j, Finsupp.single (p j) (x j) →
      Finsupp.linearCombination ℝ (fun F => (δ F : ℝ)) L =
        t * (f.2 : ℝ) + ∑ j, (f.1 j : ℝ) * x j := by
  classical
  obtain ⟨NK, hNK, hNKc⟩ := hQ K
  choose N hN hNc using fun j => hQ (Finsupp.single (p j) (1 : ℤ))
  let AK : Divisor.cartierSubgroup (X := X) := ⟨(NK : ℤ) • K, hNKc⟩
  let A : Fin r → Divisor.cartierSubgroup (X := X) := fun j =>
    ⟨(N j : ℤ) • Finsupp.single (p j) 1, hNc j⟩
  let L' : ℝ → (Fin r → ℝ) → CartierDivisorWithCoeffs ℝ X := fun t x =>
    Finsupp.single AK (t / NK) + ∑ j, Finsupp.single (A j) (x j / N j)
  have hsingle : ∀ (x : Fin r → ℝ) P,
      ∑ j, x j * ((Finsupp.single (p j) (1 : ℤ) P : ℤ) : ℝ) =
        (∑ j, Finsupp.single (p j) (x j)) P := by
    intro x P
    rw [Finsupp.finsetSum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Finsupp.single_apply]
    split_ifs <;> simp
  have hL'div : ∀ t x P, CartierDivisorWithCoeffs.toDivisorWithCoeffs (L' t x) P =
      t * (K P : ℝ) + (∑ j, Finsupp.single (p j) (x j)) P := by
    intro t x P
    rw [← hsingle]
    simp only [L', map_add, map_sum, CartierDivisorWithCoeffs.toDivisorWithCoeffs_single,
      Finsupp.add_apply, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
    have hof : ∀ (D : Divisor X) P, DivisorWithCoeffs.ofDivisor ℝ D P = (D P : ℝ) :=
      fun _ _ => rfl
    simp only [AK, A, hof, Finsupp.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast]
    have hNK' : (NK : ℝ) ≠ 0 := by exact_mod_cast hNK.ne'
    have hN' : ∀ j, (N j : ℝ) ≠ 0 := fun j => by exact_mod_cast (hN j).ne'
    congr 1
    · field_simp
    · refine Finset.sum_congr rfl fun j _ => ?_
      field_simp [hN' j]
  have hL'deg : ∀ t x, Finsupp.linearCombination ℝ (fun F => (δ F : ℝ)) (L' t x) =
      t * ((δ AK : ℝ) / NK) + ∑ j, (δ (A j) : ℝ) / N j * x j := by
    intro t x
    simp only [L', map_add, map_sum, Finsupp.linearCombination_single, smul_eq_mul]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun j _ => by ring
  refine ⟨(fun j => (δ (A j) : ℚ) / N j, (δ AK : ℚ) / NK), fun L t x hL => ?_⟩
  have hLL : CartierDivisorWithCoeffs.toDivisorWithCoeffs L =
      CartierDivisorWithCoeffs.toDivisorWithCoeffs (L' t x) := Finsupp.ext fun P => by
    rw [hL, hL'div, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    rfl
  rw [linearCombination_eq_of_toDivisorWithCoeffs_eq δ hLL, hL'deg]
  simp

/-- On a `ℚ`-factorial variety, the degree on a proper curve `C` of `K + ∑ⱼ xⱼ pⱼ` is a
rational affine form in `x`: it is computed by any real Cartier expression of `K + ∑ⱼ xⱼ pⱼ`,
and on an integral Cartier divisor `E = m (K + ∑ⱼ yⱼ pⱼ)` it is `m` times the form at `y`. -/
private theorem exists_ratAffineForm_degree_eq {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] (hQ : IsQFactorial sX) (K : Divisor X) {r : ℕ}
    {p : Fin r → MMP.Mori.PrimeDivisor X} (hp : Function.Injective p) (C : ProperCurve sX) :
    ∃ f : (Fin r → ℚ) × ℚ,
      (∀ (L : CartierDivisorWithCoeffs ℝ X) (x : Fin r → ℝ),
        CartierDivisorWithCoeffs.toDivisorWithCoeffs L =
          Divisor.toRDivisor K + ∑ j, Finsupp.single (p j) (x j) →
        (L.sum fun F c =>
          haveI := (Divisor.mem_cartierSubgroup.mp F.2).isInvertibleModule_divisorialSheaf
          c * (C.degree k (F : Divisor X).divisorialSheaf : ℝ)) = ratAffineForm f x) ∧
      ∀ (E : Divisor X) (hE : E.IsCartier) (m : ℕ) (y : Fin r → ℚ),
        Divisor.toQDivisor E =
          (m : ℚ) • (Divisor.toQDivisor K + ∑ j, Finsupp.single (p j) (y j)) →
        haveI := hE.isInvertibleModule_divisorialSheaf
        (C.degree k E.divisorialSheaf : ℝ) = m * ratAffineForm f fun j => (y j : ℝ) := by
  classical
  let δC : (Divisor.cartierSubgroup (X := X)) →+ ℤ :=
    { toFun := fun F => (F : Divisor X).degreeOn k sX C.ι C.dim_le F.2
      map_zero' := Divisor.degreeOn_zero' k sX C.ι C.dim_le
      map_add' := fun F G => Divisor.degreeOn_add k sX C.ι C.dim_le _ _ F.2 G.2 }
  obtain ⟨f, hf⟩ := exists_linearCombination_eq hQ.2 δC K p
  refine ⟨f, fun L x hL => ?_, fun E hE m y hEy => ?_⟩
  · have hdeg : Finsupp.linearCombination ℝ (fun F => (δC F : ℝ)) L =
        L.sum fun F c => c * (δC F : ℝ) := by
      simp [Finsupp.linearCombination_apply, smul_eq_mul]
    exact hdeg.symm.trans ((hf L 1 x (by rw [hL, one_smul])).trans
      (by simp only [ratAffineForm]; ring))
  · let Ei : Divisor.cartierSubgroup (X := X) := ⟨E, Divisor.mem_cartierSubgroup.mpr hE⟩
    have hEdiv : CartierDivisorWithCoeffs.toDivisorWithCoeffs (Finsupp.single Ei 1) =
        (m : ℝ) • Divisor.toRDivisor K +
          ∑ j, Finsupp.single (p j) ((m : ℝ) * (y j : ℝ)) := Finsupp.ext fun P => by
      rw [CartierDivisorWithCoeffs.toDivisorWithCoeffs_single, one_smul, Finsupp.add_apply,
        Finsupp.smul_apply, smul_eq_mul]
      have hEP := congrArg (fun G : QDivisor X => G P) hEy
      simp only [Finsupp.smul_apply, Finsupp.add_apply, smul_eq_mul] at hEP
      change ((E P : ℤ) : ℝ) = (m : ℝ) * ((K P : ℤ) : ℝ) + _
      have hEP' : ((E P : ℤ) : ℝ) = (m : ℝ) * ((K P : ℝ) +
          (((∑ j, Finsupp.single (p j) (y j) : QDivisor X) P : ℚ) : ℝ)) := by
        have : ((E P : ℤ) : ℚ) = (m : ℚ) * ((K P : ℚ) +
            (∑ j, Finsupp.single (p j) (y j) : QDivisor X) P) := hEP
        exact_mod_cast congrArg (fun q : ℚ => (q : ℝ)) this
      rw [hEP', mul_add]
      congr 1
      by_cases hr : P ∈ Set.range p
      · obtain ⟨j, rfl⟩ := hr
        rw [sum_single_apply_self hp y, sum_single_apply_self hp fun j => (m : ℝ) * (y j : ℝ)]
      · rw [sum_single_apply_of_notMem y hr,
          sum_single_apply_of_notMem (fun j => (m : ℝ) * (y j : ℝ)) hr]
        simp
    have h := hf _ _ _ hEdiv
    rw [Finsupp.linearCombination_single, one_smul] at h
    change ((δC Ei : ℤ) : ℝ) = _
    rw [h]
    simp only [ratAffineForm, mul_add, Finset.mul_sum]
    rw [add_comm]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring

/-- **A rational decomposition preserving all null curves.** Let `X` be a normal `ℚ`-factorial
projective variety over an algebraically closed field of characteristic zero, `K` a canonical
divisor and `B` an effective `ℝ`-divisor with `(X, B)` klt, and put `D = K + B`. There are
effective rational boundaries `B₁, …, B_s` with `(X, Bᵢ)` klt, in the smallest rational affine
hull of `B`, reals `rᵢ > 0` with `∑ rᵢ = 1`, and `m > 0`, such that `D = ∑ rᵢ (K + Bᵢ)`, each
`m(K + Bᵢ)` is an integral Cartier divisor `Eᵢ`, and for every proper curve `C` with
`D · C = 0` (computed from any real Cartier expression of `D`) every `Eᵢ` has degree zero on
`C`. -/
@[mmp "lem_fourfold_rational_null_decomposition"]
public theorem exists_convexCombination_isKltPair_of_isRealKltPair {k : Type u} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    (hX : MMP.Mori.IsProjectiveVariety k sX) (hQ : IsQFactorial sX)
    {n : ℕ} (K : Divisor X) (hK : K.IsCanonicalDivisor sX n)
    (B : RDivisor X) (hB0 : 0 ≤ B) (hB : IsRealKltPair sX B) :
    ∃ (s : ℕ) (Bs : Fin s → QDivisor X) (r : Fin s → ℝ) (m : ℕ) (E : Fin s → Divisor X)
      (hE : ∀ i, (E i).IsCartier),
      (∀ i, IsKltPair sX (Bs i)) ∧
      (∀ i, IsInSmallestRationalAffineHull B (QDivisor.toRDivisor (Bs i))) ∧
      (∀ i, 0 < r i) ∧ ∑ i, r i = 1 ∧ 0 < m ∧
      Divisor.toRDivisor K + B = ∑ i, r i • (Divisor.toRDivisor K + QDivisor.toRDivisor (Bs i)) ∧
      (∀ i, Divisor.toQDivisor (E i) = (m : ℚ) • (Divisor.toQDivisor K + Bs i)) ∧
      ∀ (C : ProperCurve sX) (L : CartierDivisorWithCoeffs ℝ X),
        CartierDivisorWithCoeffs.toDivisorWithCoeffs L = Divisor.toRDivisor K + B →
        (L.sum fun F c =>
          haveI := (Divisor.mem_cartierSubgroup.mp F.2).isInvertibleModule_divisorialSheaf
          c * (C.degree k (F : Divisor X).divisorialSheaf : ℝ)) = 0 →
        ∀ i, haveI := (hE i).isInvertibleModule_divisorialSheaf
          C.degree k (E i).divisorialSheaf = 0 := by
  classical
  set S := B.support
  set r := S.card
  let e := S.equivFin
  let p : Fin r → MMP.Mori.PrimeDivisor X := fun j => (e.symm j : MMP.Mori.PrimeDivisor X)
  have hp : Function.Injective p := fun a b h => e.symm.injective (Subtype.ext h)
  have hBp : ∀ P, B.coeff P ≠ 0 → P ∈ Set.range p := fun P hP =>
    ⟨e ⟨P, Finsupp.mem_support_iff.mpr hP⟩, by simp [p]⟩
  have hBp' : ∀ P, P ∉ Set.range p → B P = 0 := fun P hP => not_not.mp fun h => hP (hBp P h)
  obtain ⟨V, hspan, hint, -, hklt⟩ := exists_rationalPolytope_isKltPair_of_isRealKltPair sX hX hQ
    B hB0 hB 0 le_rfl (by rwa [map_zero]) p hp hBp (fun P h => absurd rfl h)
  set δ : Fin r → ℝ := fun i => B.coeff (p i)
  obtain ⟨s, g, rr, hgV, hrr0, hrr1, hgδ⟩ := exists_fin_pos_weights_of_mem_intrinsicInterior V hint
  have hVhull : ∀ i, (fun j => (g i j : ℝ)) ∈ rationalAffineHull δ := fun i =>
    hspan ▸ subset_affineSpan ℝ _ (subset_convexHull ℝ _ (Set.mem_image_of_mem _ (hgV i)))
  set Bs : Fin s → QDivisor X := fun i => ∑ j, Finsupp.single (p j) (g i j)
  have hBs_self : ∀ i j, Bs i (p j) = g i j := fun i j => sum_single_apply_self hp _ j
  have hBs_out : ∀ i P, P ∉ Set.range p → Bs i P = 0 := fun i P hP =>
    sum_single_apply_of_notMem _ hP
  obtain ⟨m, hm, E, hE, hEq⟩ := exists_isCartier_eq_smul hQ K Bs
  refine ⟨s, Bs, rr, m, E, hE, fun i => hklt _ (hgV i),
    fun i => isInSmallestRationalAffineHull_sum_single hp (fun j => (e.symm j).2) hBp' (hVhull i),
    hrr0, hrr1, hm, ?_, hEq, ?_⟩
  · have hBeq : ∀ P, B P = ∑ i, rr i * ((Bs i P : ℚ) : ℝ) := by
      intro P
      by_cases hr : P ∈ Set.range p
      · obtain ⟨j, rfl⟩ := hr
        simp only [hBs_self]
        exact (hgδ j).symm
      · rw [hBp' P hr]
        simp [hBs_out _ P hr]
    refine Finsupp.ext fun P => ?_
    rw [Finsupp.finsetSum_apply]
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, mul_add,
      Finset.sum_add_distrib, ← Finset.sum_mul, hrr1, one_mul]
    rw [hBeq P]
    rfl
  · intro C L hL hsum i
    obtain ⟨f, hf, hfE⟩ := exists_ratAffineForm_degree_eq hQ K hp C
    have hBδ : B = ∑ j, Finsupp.single (p j) (δ j) := Finsupp.ext fun P => by
      by_cases hr : P ∈ Set.range p
      · obtain ⟨j, rfl⟩ := hr
        exact (sum_single_apply_self hp δ j).symm
      · rw [sum_single_apply_of_notMem _ hr, hBp' P hr]
    have hi : ratAffineForm f (fun j => (g i j : ℝ)) = 0 :=
      hVhull i f ((hf L δ (by rw [hL, ← hBδ])).symm.trans hsum)
    have h := hfE (E i) (hE i) m (g i) (hEq i)
    rw [hi, mul_zero] at h
    exact_mod_cast h

end MMP.Fourfold
