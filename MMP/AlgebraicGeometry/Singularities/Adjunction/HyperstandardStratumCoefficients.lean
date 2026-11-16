module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.StratumAdjunction
import MMP.AlgebraicGeometry.Singularities.Adjunction.DltStratum
import MMP.AlgebraicGeometry.Singularities.DltFloor.Residue
import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueDifferent
import MMP.AlgebraicGeometry.Singularities.CyclicQuotientDifferent
import MMP.AlgebraicGeometry.Singularities.PltDifferentCoefficients
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.Singularities.PltCodimTwoCyclicModel
import MMP.AlgebraicGeometry.Singularities.DltDiscrepancy
import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal
import MMP.AlgebraicGeometry.Resolution.DivisorTupleRestrictionLift
import MMP.AlgebraicGeometry.SpreadingOut.CanonicalDivisor
import MMP.AlgebraicGeometry.Morphisms.Etale.HenselizationColimit
public import MMP.AlgebraicGeometry.Dimension.HeightCoheight

/-!
# Hyperstandard coefficients on the strata of a projective dlt pair

Let `(X, B)` be a projective dlt pair with rational boundary over an algebraically closed field
of characteristic zero, and let `I ⊆ (0, 1] ∩ ℚ` be a finite set containing `1` and every nonzero
coefficient of `B`. For every flag `X = S₀ ⊃ S₁ ⊃ ⋯ ⊃ S_k = S` of iterated adjunction to normal
prime components of the reduced boundary, with `B_j = Diff_{S_j}(B_{j-1} - S_j)`, every
coefficient of the final boundary `B_S = B_k` lies in the hyperstandard set `D(I)`.

## Main results

* `MMP.Fourfold.IsStratumAdjunctionPair.coeff_mem_hyperstandardSet`: the coefficients of an
  iterated adjunction pair of a projective dlt pair lie in `D(I)`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 16.6
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

namespace Hyperstandard

/-- `1 ∈ D(I)` when `1 ∈ I`. -/
private theorem one_mem {I : Finset ℚ} (hI1 : (1 : ℚ) ∈ I) : (1 : ℝ) ∈ hyperstandardSet I := by
  classical
  refine ⟨⟨zero_le_one, le_rfl⟩, 1, le_rfl, fun b => if b = 1 then 1 else 0, ?_⟩
  simp [hI1]

/-- `0 ∈ D(I)`. -/
private theorem zero_mem (I : Finset ℚ) : (0 : ℝ) ∈ hyperstandardSet I :=
  ⟨⟨le_rfl, zero_le_one⟩, 1, le_rfl, 0, by simp⟩

/-- Every element of `I ⊆ (0, 1]` lies in `D(I)`. -/
private theorem mem_of_mem {I : Finset ℚ} (hI : ∀ b ∈ I, 0 < b ∧ b ≤ 1) {b : ℚ} (hb : b ∈ I) :
    (b : ℝ) ∈ hyperstandardSet I := by
  classical
  refine ⟨⟨by exact_mod_cast (hI b hb).1.le, by exact_mod_cast (hI b hb).2⟩, 1, le_rfl,
    fun c => if c = b then 1 else 0, ?_⟩
  simp [hb]

/-- Exchanging the two sums in a natural combination of the representations `t_i`. -/
private theorem sum_cast_sum_mul_eq {ι : Type*} (I : Finset ℚ) (s : Finset ι) (u : ι → ℕ)
    (t : ι → ℚ → ℕ) :
    ∑ b ∈ I, ((∑ i ∈ s, u i * t i b : ℕ) : ℝ) * (b : ℝ) =
      ∑ i ∈ s, (u i : ℝ) * ∑ b ∈ I, (t i b : ℝ) * (b : ℝ) := by
  simp only [Nat.cast_sum, Nat.cast_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => by ring

/-- An element `1 - 1/n + f/n` with `n ≥ 2` and `f ≥ 0` is at least `1/2`. -/
private theorem half_le_of_eq {I : Finset ℚ} (hI : ∀ b ∈ I, 0 < b ∧ b ≤ 1) {y : ℝ} {n : ℕ}
    (hn : 2 ≤ n) (t : ℚ → ℕ) (hy : y = 1 - 1 / (n : ℝ) + (∑ b ∈ I, (t b : ℝ) * b) / n) :
    1 / 2 ≤ y := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have : 1 / (n : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hn2
  have : 0 ≤ (∑ b ∈ I, (t b : ℝ) * b) / n := div_nonneg (Finset.sum_nonneg fun b hb =>
    mul_nonneg (Nat.cast_nonneg _) (by exact_mod_cast (hI b hb).1.le)) (by linarith)
  linarith

/-- If `∑_{i ∈ s} r_i c_i < 1` with `c_i ≥ 0`, and `c_i ≥ 1/2` on `J ⊆ s`, then
`∑_{i ∈ J} r_i ≤ 1`. -/
private theorem sum_le_one_of_half_le {ι : Type*} {s J : Finset ι} (hJ : J ⊆ s) (r : ι → ℕ)
    {c : ι → ℝ} (hc0 : ∀ i ∈ s, 0 ≤ c i) (hlt : ∑ i ∈ s, (r i : ℝ) * c i < 1)
    (hhalf : ∀ i ∈ J, 1 / 2 ≤ c i) : ∑ i ∈ J, r i ≤ 1 := by
  have h1 : ∑ i ∈ J, (r i : ℝ) * (1 / 2) ≤ ∑ i ∈ s, (r i : ℝ) * c i :=
    (Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hhalf i hi)
      (Nat.cast_nonneg _)).trans (Finset.sum_le_sum_of_subset_of_nonneg hJ
        fun i hi _ => mul_nonneg (Nat.cast_nonneg _) (hc0 i hi))
  rw [← Finset.sum_mul] at h1
  have : ((∑ i ∈ J, r i : ℕ) : ℝ) < 2 := by
    push_cast
    linarith
  have : ∑ i ∈ J, r i < 2 := by exact_mod_cast this
  omega

/-- If `∑_{i ∈ s} r_i c_i < 1` with `c_i = 1 - 1/n_i + f_i/n_i`, then at most one term has
`n_i ≥ 2`, with `r_i = 1`, so the sum is `1 - 1/N + f/N` plus a natural combination of the
`f_i`. -/
private theorem exists_sum_eq_add_sum {I : Finset ℚ} (hI : ∀ b ∈ I, 0 < b ∧ b ≤ 1) {ι : Type*}
    (s : Finset ι) (r : ι → ℕ) (c : ι → ℝ) (n : ι → ℕ) (hn : ∀ i, 1 ≤ n i) (t : ι → ℚ → ℕ)
    (ht : ∀ i ∈ s, c i = 1 - 1 / (n i : ℝ) + (∑ b ∈ I, (t i b : ℝ) * b) / n i)
    (hc0 : ∀ i ∈ s, 0 ≤ c i) (hlt : ∑ i ∈ s, (r i : ℝ) * c i < 1) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ (t₀ : ℚ → ℕ) (s' : Finset ι), ∑ i ∈ s, (r i : ℝ) * c i =
      1 - 1 / (N : ℝ) + (∑ b ∈ I, (t₀ b : ℝ) * b) / N +
        ∑ i ∈ s', (r i : ℝ) * ∑ b ∈ I, (t i b : ℝ) * b := by
  classical
  set J := s.filter (fun i => r i ≠ 0 ∧ 2 ≤ n i) with hJ
  have hJsum : ∑ i ∈ J, r i ≤ 1 := sum_le_one_of_half_le (Finset.filter_subset _ s) r hc0 hlt
    fun i hi => half_le_of_eq hI (Finset.mem_filter.mp hi).2.2 (t i)
      (ht i (Finset.mem_filter.mp hi).1)
  have hoff : ∀ i ∈ s, i ∉ J → (r i : ℝ) * c i = r i * ∑ b ∈ I, (t i b : ℝ) * b := by
    intro i his hiJ
    by_cases hr : r i = 0
    · simp [hr]
    · have hn1 : n i = 1 := by
        have : ¬ 2 ≤ n i := fun h2 => hiJ (Finset.mem_filter.mpr ⟨his, hr, h2⟩)
        have := hn i
        omega
      rw [ht i his, hn1]
      simp
  rcases J.eq_empty_or_nonempty with hJe | ⟨i₀, hi₀⟩
  · refine ⟨1, le_rfl, 0, s, ?_⟩
    rw [Finset.sum_congr rfl fun i hi => hoff i hi (by simp [hJe])]
    simp
  · obtain ⟨hi₀s, hr₀, -⟩ := Finset.mem_filter.mp hi₀
    have hr₀1 : r i₀ = 1 := by
      have := Finset.single_le_sum (f := r) (fun _ _ => Nat.zero_le _) hi₀
      omega
    refine ⟨n i₀, hn i₀, t i₀, s.erase i₀, ?_⟩
    rw [← Finset.add_sum_erase s _ hi₀s, hr₀1, Nat.cast_one, one_mul, ← ht i₀ hi₀s]
    congr 1
    refine Finset.sum_congr rfl fun i hi =>
      hoff i (Finset.mem_of_mem_erase hi) fun hiJ => ?_
    have := Finset.add_le_sum (f := r) (fun _ _ => Nat.zero_le _) hiJ hi₀
      (Finset.ne_of_mem_erase hi)
    have : r i ≠ 0 := (Finset.mem_filter.mp hiJ).2.1
    omega

/-- If `x = 1 - 1/m + (1 - 1/N + f/N + ∑ r_i f_i)/m ∈ [0, 1]` with `f`, `f_i` natural
combinations of `I`, then `x ∈ D(I)`. -/
private theorem mem_of_eq_add_sum {I : Finset ℚ} {ι : Type*} (s : Finset ι) (r : ι → ℕ)
    (t : ι → ℚ → ℕ) {m N : ℕ} (hm : 1 ≤ m) (hN : 1 ≤ N) (t₀ : ℚ → ℕ) {x : ℝ}
    (hx : x = 1 - 1 / (m : ℝ) + (1 - 1 / (N : ℝ) + (∑ b ∈ I, (t₀ b : ℝ) * b) / N +
      ∑ i ∈ s, (r i : ℝ) * ∑ b ∈ I, (t i b : ℝ) * b) / m) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x ∈ hyperstandardSet I := by
  refine ⟨⟨hx0, hx1⟩, m * N, Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega)
    (by omega)), fun b => t₀ b + N * ∑ i ∈ s, r i * t i b, ?_⟩
  have hsplit : ∑ b ∈ I, ((t₀ b + N * ∑ i ∈ s, r i * t i b : ℕ) : ℝ) * (b : ℝ) /
      ((m * N : ℕ) : ℝ) = (∑ b ∈ I, (t₀ b : ℝ) * b +
        N * ∑ i ∈ s, (r i : ℝ) * ∑ b ∈ I, (t i b : ℝ) * b) / ((m : ℝ) * N) := by
    rw [← Finset.sum_div, ← sum_cast_sum_mul_eq]
    push_cast
    simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [hsplit, hx]
  push_cast
  field_simp
  ring

/-- **`D(D(I)) ⊆ D(I)`.** If `c_i ∈ D(I)` and `x = 1 - 1/m + ∑ r_i c_i / m ≤ 1` with `m ≥ 1`
and `r_i ∈ ℕ`, then `x ∈ D(I)`. -/
private theorem mem_of_eq_sum {I : Finset ℚ} (hI : ∀ b ∈ I, 0 < b ∧ b ≤ 1) (hI1 : (1 : ℚ) ∈ I)
    {ι : Type*} (s : Finset ι) (r : ι → ℕ) (c : ι → ℝ)
    (hc : ∀ i ∈ s, c i ∈ hyperstandardSet I) {m : ℕ} (hm : 1 ≤ m) {x : ℝ}
    (hx : x = 1 - 1 / (m : ℝ) + ∑ i ∈ s, (r i : ℝ) * c i / m) (hx1 : x ≤ 1) :
    x ∈ hyperstandardSet I := by
  classical
  have hrep : ∀ i, ∃ n : ℕ, 1 ≤ n ∧ ∃ t : ℚ → ℕ,
      i ∈ s → c i = 1 - 1 / (n : ℝ) + (∑ b ∈ I, (t b : ℝ) * b) / n := by
    intro i
    by_cases hi : i ∈ s
    · obtain ⟨-, n, hn, t, ht⟩ := hc i hi
      exact ⟨n, hn, t, fun _ => by rw [ht, Finset.sum_div]⟩
    · exact ⟨1, le_rfl, 0, fun h => absurd h hi⟩
  choose n hn t ht using hrep
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hc0 : ∀ i ∈ s, 0 ≤ c i := fun i hi => (hc i hi).1.1
  have hxT : x = 1 - 1 / (m : ℝ) + (∑ i ∈ s, (r i : ℝ) * c i) / m := by
    rw [hx, Finset.sum_div]
  have hT1 : ∑ i ∈ s, (r i : ℝ) * c i ≤ 1 := by
    rw [hxT] at hx1
    exact (div_le_div_iff_of_pos_right hmpos).mp (by linarith)
  have hx0 : 0 ≤ x := by
    have : 1 / (m : ℝ) ≤ 1 := by
      rw [div_le_one hmpos]
      exact_mod_cast hm
    have : 0 ≤ (∑ i ∈ s, (r i : ℝ) * c i) / m := div_nonneg (Finset.sum_nonneg fun i hi =>
      mul_nonneg (Nat.cast_nonneg _) (hc0 i hi)) hmpos.le
    rw [hxT]
    linarith
  rcases hT1.lt_or_eq with hlt | heq
  · obtain ⟨N, hN, t₀, s', hT⟩ := exists_sum_eq_add_sum hI s r c n hn t ht hc0 hlt
    exact mem_of_eq_add_sum s' r t hm hN t₀ (by rw [hxT, hT]) hx0 hx1
  · have : x = 1 := by
      rw [hxT, heq]
      ring
    rw [this]
    exact one_mem hI1

end Hyperstandard

section Geometry

open MMP.Mori MMP.Flips IsLocalRing

/-- A local ring has a strict henselization in its own universe. -/
private theorem exists_isHenselization_of_isSepClosure (A : Type) [CommRing A] [IsLocalRing A]
    (κsep : Type) [Field κsep] [Algebra (ResidueField A) κsep]
    [IsSepClosure (ResidueField A) κsep] :
    ∃ (H : Type) (_ : CommRing H) (_ : IsLocalRing H) (_ : Algebra A H),
      IsHenselization A κsep H := by
  have hA : (CommAlgCat.etale A).ind (CommAlgCat.of A A) :=
    (CommAlgCat.etale A).le_ind _ inferInstance
  have hres : Function.Surjective (ResidueField.map (algebraMap A A)) := by
    simpa using (Function.surjective_id :
      Function.Surjective (id : ResidueField A → ResidueField A))
  obtain ⟨B, hRing, hLocal, hAlg, -, -, -, hHens, -, hInd, -, hCompat⟩ :=
    exists_strictHenselization A A hA hres κsep
  exact ⟨B, hRing, hLocal, hAlg, IsHenselization.of_ind_etale hHens hInd hCompat⟩

/-- If a closed immersion `j : T ⟶ X` has kernel the ideal of `P` and `T` is a normal variety,
then so is the reduced subscheme of `P`, which is isomorphic to `T` over `X`. -/
private theorem isNormalVariety_subschemeι {k : Type} [Field k] {X T : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) (j : T ⟶ X) [IsClosedImmersion j] [IsNormal T]
    (P : Mori.PrimeDivisor X) (hT : IsNormalVariety k (j ≫ sX)) (h : j.ker = P.idealSheaf) :
    IsNormalVariety k (P.idealSheaf.subschemeι ≫ sX) := by
  have hk : j.ker = P.idealSheaf.subschemeι.ker := by
    rw [h, Scheme.IdealSheafData.ker_subschemeι]
  have := IsClosedImmersion.isIso_lift j P.idealSheaf.subschemeι hk
  have hn : IsNormal P.idealSheaf.subscheme :=
    isNormal_of_isOpenImmersion (IsClosedImmersion.lift j P.idealSheaf.subschemeι hk.le)
  rw [← IsClosedImmersion.lift_fac j P.idealSheaf.subschemeι hk.le, Category.assoc]
  obtain ⟨hv, -⟩ := hT
  have := P.integral
  exact ⟨(Mori.isVariety_iff _ _).mpr ⟨inferInstance, inferInstance, inferInstance,
    inferInstance⟩, hn⟩

/-- **A codimension-one point of a prime divisor has codimension two.** If `j : T ⟶ X` is a
closed immersion onto the support of a prime divisor `P` of an integral scheme of finite type over
`k`, and `Q` is a prime divisor of `T`, then `𝒪_{X, j(η_Q)}` has dimension two. -/
private theorem ringKrullDim_stalk_eq_two {k : Type} [Field k] {X T : Scheme.{0}}
    (sX : X ⟶ Spec (.of k))
    [IsIntegral X] [LocallyOfFiniteType sX] (j : T ⟶ X) [IsClosedImmersion j]
    (P : Mori.PrimeDivisor X) (hP : Set.range j.base = (P.support : Set X))
    (Q : Mori.PrimeDivisor T) :
    ringKrullDim (X.presheaf.stalk (j.base Q.genericPoint)) = 2 := by
  let : X.Over (Spec (.of k)) := ⟨sX⟩
  have : LocallyOfFiniteType (X ↘ Spec (.of k)) := ‹LocallyOfFiniteType sX›
  set x := j.base Q.genericPoint
  have hIic : Set.Iic P.genericPoint = Set.range j.base := by
    ext z
    rw [hP, P.support_eq_closure, Set.mem_Iic, Scheme.le_iff_specializes,
      specializes_iff_mem_closure]
  have hle : ∀ a b : T, j.base a ≤ j.base b ↔ a ≤ b := fun a b => by
    rw [Scheme.le_iff_specializes, Scheme.le_iff_specializes]
    exact j.isClosedEmbedding.isInducing.specializes_iff
  let emb : T ↪o X := ⟨⟨j.base, j.isClosedEmbedding.injective⟩, hle _ _⟩
  let e : T ≃o Set.Iic P.genericPoint :=
    emb.orderIso.trans (Set.orderIsoOfEq _ _ hIic.symm)
  have hx : x ≤ P.genericPoint := by
    rw [← Set.mem_Iic, hIic]; exact ⟨_, rfl⟩
  have hex : e Q.genericPoint = ⟨x, hx⟩ := rfl
  have hc : Order.coheight (⟨x, hx⟩ : Set.Iic P.genericPoint) = 1 := by
    rw [← hex, Order.coheight_orderIso, Mori.PrimeDivisor.coheight_genericPoint]
  obtain ⟨h1, h2⟩ := MMP.height_eq_height_add_coheight_Iic k hx
  have k1 := MMP.height_add_coheight_eq_krullDim k x
  have k2 := MMP.height_add_coheight_eq_krullDim k P.genericPoint
  rw [Mori.PrimeDivisor.coheight_genericPoint, h1, hc, ← k1] at k2
  have hfin : Order.height x ≠ ⊤ := by
    intro h; rw [h1, h] at h2; simp at h2
  have k3 := WithBot.coe_inj.mp k2
  rw [add_assoc] at k3
  lift Order.height x to ℕ using hfin with h
  rw [ringKrullDim_stalk_eq_coheight, ← WithTop.add_left_cancel WithTop.coe_ne_top k3]
  rfl

/-- If `j(η_Q)` lies on a second coefficient-one component `P'` of `B_Y`, then `B_T` has
coefficient one along `Q`. -/
private theorem coeff_eq_one_of_mem_support_of_ne {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {Y T : Scheme.{0}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {BY : QDivisor Y} (hB : MMP.Intersection.IsDltPair sY BY)
    {j : T ⟶ Y} {BT : QDivisor T} (h : IsAdjunctionStep sY BY j BT) [IsIntegral T]
    [IsLocallyNoetherian T] [IsNormal T] {P P' : Mori.PrimeDivisor Y}
    (hP : Set.range j.base = (P.support : Set Y)) (hP'P : P' ≠ P) (hP'1 : 1 ≤ BY.coeff P')
    {Q : Mori.PrimeDivisor T} (hxP' : j.base Q.genericPoint ∈ (P'.support : Set Y))
    (hBT1 : BT.coeff Q ≤ 1) : BT.coeff Q = 1 := by
  have hQirr : IsIrreducible (Q.support : Set T) := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact isIrreducible_singleton.closure
  have hQsub : (Q.support : Set T) ⊆ j.base ⁻¹' (P'.support : Set Y) := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact closure_minimal (Set.singleton_subset_iff.mpr hxP')
      (P'.idealSheaf.support.isClosed.preimage j.base.hom.continuous)
  obtain ⟨Q', hQQ', -, hQ'1⟩ :=
    SdltFloor.exists_primeDivisor_of_isAdjunctionStep hB h hP hP'P hP'1 hQirr hQsub
  obtain rfl : Q' = Q := MMP.Intersection.primeDivisor_eq_of_genericPoint_mem_support
    (hQQ' (MMP.Flips.primeDivisor_genericPoint_mem_support Q))
  exact le_antisymm hBT1 hQ'1

/-- If no coefficient-one component of `B ≥ 0` other than `P` passes through `x`, then at most
one component of `⌊B⌋` passes through `x`. -/
private theorem subsingleton_roundDown_of_forall_ne {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {BY : QDivisor Y} (hBY0 : ∀ E, 0 ≤ BY.coeff E)
    {P : Mori.PrimeDivisor Y} {x : Y}
    (hA : ∀ P' : Mori.PrimeDivisor Y, P' ≠ P → 1 ≤ BY.coeff P' → x ∉ (P'.support : Set Y)) :
    {P'' : Mori.PrimeDivisor Y |
      BY.roundDown.coeff P'' ≠ 0 ∧ x ∈ (P''.support : Set Y)}.Subsingleton := by
  have key : ∀ P'' ∈ {P'' : Mori.PrimeDivisor Y |
      BY.roundDown.coeff P'' ≠ 0 ∧ x ∈ (P''.support : Set Y)}, P'' = P := by
    rintro P'' ⟨h0, hx⟩
    by_contra hne
    refine hA P'' hne (not_lt.mp fun hlt => h0 ?_) hx
    rw [DivisorWithCoeffs.coeff_roundDown]
    exact Int.floor_eq_zero_iff.mpr ⟨hBY0 _, hlt⟩
  exact fun a ha b hb => (key a ha).trans (key b hb).symm

/-- Removing a coefficient-one component `P` from a boundary with coefficients in `[0, 1]` leaves
a boundary with coefficients in `[0, 1]` and coefficient zero along `P`. -/
private theorem sub_single_one_bounds {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] {BY : QDivisor Y} (hBY0 : ∀ E, 0 ≤ BY.coeff E) (hBY1 : ∀ E, BY.coeff E ≤ 1)
    {P : Mori.PrimeDivisor Y} (hBP : BY.coeff P = 1) :
    0 ≤ (BY - Finsupp.single P 1 : QDivisor Y) ∧
      (∀ E, (BY - Finsupp.single P 1 : QDivisor Y).coeff E ≤ 1) ∧
      (BY - Finsupp.single P 1 : QDivisor Y).coeff P = 0 := by
  classical
  have hc : ∀ E, (BY - Finsupp.single P 1 : QDivisor Y).coeff E =
      BY.coeff E - if E = P then 1 else 0 := fun E => by
    change (BY - Finsupp.single P (1 : ℚ) : QDivisor Y) E = BY E - _
    rw [Finsupp.sub_apply, Finsupp.single_apply]
    rcases eq_or_ne E P with rfl | hE
    · simp
    · simp only [hE.symm, hE, ↓reduceIte]
  refine ⟨fun E => ?_, fun E => ?_, by simp [hc, hBP]⟩
  · change (0 : ℚ) ≤ (BY - Finsupp.single P 1 : QDivisor Y).coeff E
    rw [hc]
    split_ifs with hE
    · subst hE
      simp [hBP]
    · simpa using hBY0 E
  · rw [hc]
    split_ifs <;> linarith [hBY0 E, hBY1 E]

/-- A divisor with coefficient one along `P` is `P` plus the sum of its other components. -/
private theorem single_add_sum_erase_eq {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [DecidableEq (Mori.PrimeDivisor Y)] {BY : QDivisor Y} {P : Mori.PrimeDivisor Y}
    (hBP : BY.coeff P = 1) :
    (Finsupp.single P 1 + ∑ i : BY.support.erase P, BY.coeff i.1 • Finsupp.single i.1 1 :
      QDivisor Y) = BY := by
  have hPs : P ∈ BY.support := by
    rw [Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply, hBP]
    norm_num
  conv_rhs => rw [← Finsupp.sum_single BY]
  rw [Finsupp.sum, ← Finset.add_sum_erase _ _ hPs, ← DivisorWithCoeffs.coeff_apply BY P, hBP]
  congr 1
  rw [← Finset.sum_coe_sort (BY.support.erase P)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finsupp.smul_single_one]
  rfl

/-- The separable closure of the residue field at a point of a scheme over a field of
characteristic zero, with `m ≥ 1` and `gcd(q, m) = 1`, is a cyclic quotient setting. -/
private theorem isCyclicQuotientSetting_separableClosure {k : Type} [Field k] [CharZero k]
    {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of k)) (x : Y) {m : ℕ} {q : ℤ} (hm : 1 ≤ m)
    (hq : Int.gcd q m = 1) :
    IsCyclicQuotientSetting (SeparableClosure (ResidueField (Y.presheaf.stalk x))) m q := by
  have : CharZero (ResidueField (Y.presheaf.stalk x)) := by
    let := stalkAlgebra sY x
    exact charZero_of_injective_algebraMap (algebraMap k _).injective
  have : CharZero (SeparableClosure (ResidueField (Y.presheaf.stalk x))) :=
    charZero_of_injective_algebraMap (algebraMap (ResidueField (Y.presheaf.stalk x))
      (SeparableClosure (ResidueField (Y.presheaf.stalk x)))).injective
  have : IsSepClosed (SeparableClosure (ResidueField (Y.presheaf.stalk x))) :=
    IsSepClosure.sep_closed (ResidueField (Y.presheaf.stalk x))
  exact ⟨IsSepClosed.isAlgClosed_of_perfectField _, inferInstance, hm, hq⟩

/-- Transporting the kernel of the stalk map of `j` along the cyclic chart `φ` gives the ideal
`(u)` of the cyclic invariants. -/
private theorem map_ker_stalkMap_eq_comap {Y T : Scheme.{0}} (j : T ⟶ Y) [IsClosedImmersion j]
    {P : Mori.PrimeDivisor Y} (hker : j.ker = P.idealSheaf) (y : T) (κ : Type) [Field κ]
    {m : ℕ} {q : ℤ} (H : Type) [CommRing H] [IsLocalRing H]
    [Algebra (Y.presheaf.stalk (j.base y)) H]
    (φ : cyclicInvariants κ m q ≃+* AdicCompletion (maximalIdeal H) H)
    (hφ : Ideal.map φ ((Ideal.span {MvPowerSeries.X 0}).comap (cyclicInvariants κ m q).subtype) =
      ((AlgebraicGeometry.IdealSheafData.stalk P.idealSheaf (j.base y)).map
        (algebraMap (Y.presheaf.stalk (j.base y)) H)).map
        (algebraMap H (AdicCompletion (maximalIdeal H) H))) :
    ((RingHom.ker (j.stalkMap y).hom).map (algebraMap (Y.presheaf.stalk (j.base y))
      (AdicCompletion (maximalIdeal H) H))).map φ.symm =
      (Ideal.span {MvPowerSeries.X (0 : Fin 2)}).comap (cyclicInvariants κ m q).subtype := by
  rw [MMP.Resolution.Internal.TupleRestrictionLift.ker_stalkMap_eq_stalk_ker j, hker,
    IsScalarTower.algebraMap_eq (Y.presheaf.stalk (j.base y)) H
      (AdicCompletion (maximalIdeal H) H), ← Ideal.map_map, ← hφ]
  exact Ideal.map_of_equiv φ

/-- A scheme of dimension `n + 1` with a point whose local ring has dimension two has
`2 ≤ n + 1`. -/
private theorem two_le_of_ringKrullDim_stalk_eq_two {Y : Scheme.{0}} {n : ℕ}
    (hdim : topologicalKrullDim Y = n + 1) {x : Y}
    (hx : ringKrullDim (Y.presheaf.stalk x) = 2) : 2 ≤ n + 1 := by
  have h1 : (Order.coheight x : WithBot ℕ∞) ≤ topologicalKrullDim Y :=
    (Order.coheight_le_krullDim x).trans_eq
      (Order.krullDim_eq_of_orderIso irreducibleSetEquivPoints).symm
  rw [hdim, ← ringKrullDim_stalk_eq_coheight, hx] at h1
  exact_mod_cast h1

/-- **The plt case of `coeff_mem_of_isAdjunctionStep`.** If `P` is the only coefficient-one
component of `B_Y` through `x = j(η_Q)`, then `(Y, B_Y)` is plt at `x`, the completed strict
local ring at `x` is a cyclic quotient `K[[u, v]]^{μ_m}` along `P`, and the coefficient of `B_T`
along `Q` is `1 - 1/m + ∑ r_i b_i / m` with `b_i` the other coefficients of `B_Y`; the closure
of `D(I)` applies. -/
private theorem coeff_mem_of_isAdjunctionStep_of_forall_ne {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {Y T : Scheme.{0}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {BY : QDivisor Y} (hB : MMP.Intersection.IsDltPair sY BY)
    {j : T ⟶ Y} {BT : QDivisor T} (h : IsAdjunctionStep sY BY j BT) [IsIntegral T]
    [IsLocallyNoetherian T] [IsNormal T] (hBT : MMP.Intersection.IsDltPair (j ≫ sY) BT)
    {I : Finset ℚ} (hI : ∀ b ∈ I, 0 < b ∧ b ≤ 1) (hI1 : (1 : ℚ) ∈ I)
    (hBYI : ∀ P, ((BY.coeff P : ℚ) : ℝ) ∈ hyperstandardSet I) (Q : Mori.PrimeDivisor T)
    (hA : ∀ P P' : Mori.PrimeDivisor Y, Set.range j.base = (P.support : Set Y) → P' ≠ P →
      1 ≤ BY.coeff P' → j.base Q.genericPoint ∉ (P'.support : Set Y)) :
    ((BT.coeff Q : ℚ) : ℝ) ∈ hyperstandardSet I := by
  classical
  obtain ⟨hTv, P, -, hP, hci, _, _, _, _, _, _, _, _, _, _, n, hYv, hdim, τ, hτ0, hτ, hD, ρ, hρ,
    hgen, hpb⟩ := id h
  have hBP : BY.coeff P = 1 := h.coeff_eq_one hP
  have hBY0 : ∀ E, 0 ≤ BY.coeff E := hB.1.2.1
  set x := j.base Q.genericPoint with hxdef
  have hsub := subsingleton_roundDown_of_forall_ne hBY0 fun P' => hA P P' hP
  obtain ⟨K, hK⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety sY hYv (n := n + 1)
    (by exact_mod_cast hdim)
  have hMd : MMP.Mori.IsDltPair sY (n + 1) K BY :=
    (MMP.Threefold.Bridges.isDltPair_iff_isDltPair sY hK BY).mp hB
  have hdim2 := ringKrullDim_stalk_eq_two sY j P hP Q
  have hat := hMd.isAt_isPltPair_of_subsingleton (two_le_of_ringKrullDim_stalk_eq_two hdim hdim2)
    hsub
  obtain ⟨hB'0, hB'le, hB'P⟩ := sub_single_one_bounds hBY0 hB.2.1 hBP
  set B' : QDivisor Y := BY - Finsupp.single P 1 with hB'
  have hBeq : Finsupp.single P 1 + B' = BY := add_sub_cancel _ _
  have hker := P.ker_eq_idealSheaf_of_range_eq j hP
  have hS := isNormalVariety_subschemeι sY j P hTv hker
  have hxP : x ∈ P.support := by
    rw [hxdef, ← hP]
    exact ⟨_, rfl⟩
  have hQloc : ∃ U : Y.Opens, x ∈ U ∧ (Divisor.toQDivisor (K.restrictOpen U) +
      DivisorWithCoeffs.restrictOpen U (Finsupp.single P 1 + B')).IsQCartier := by
    have : Nonempty (⊤ : Y.Opens) := ⟨⟨x, trivial⟩⟩
    exact ⟨⊤, trivial, hBeq ▸ (hMd.1.restrictOpen ⊤).2.2⟩
  rw [← hBeq] at hat
  obtain ⟨m, hm, q, hq, -, hall⟩ := MMP.Flips.exists_ringEquiv_cyclicInvariants_of_isAt_isPltPair
    sY hYv hK P hS B' hB'0 hB'le hB'P x hQloc hxP hdim2 hat
  set A := Y.presheaf.stalk x
  obtain ⟨H, _, _, _, _⟩ := exists_isHenselization_of_isSepClosure A
    (SeparableClosure (ResidueField A))
  obtain ⟨φ, -, hφ⟩ := hall (SeparableClosure (ResidueField A)) H
  let Bi : (BY.support.erase P) → Mori.PrimeDivisor Y := Subtype.val
  have hBi : ∀ i, Bi i ≠ P := fun i => Finset.ne_of_mem_erase i.2
  obtain ⟨r, -, hr⟩ := coeff_residueDifferent_eq_of_cyclicInvariants_of_charZero sY hYv hdim j
    hTv P hP τ hτ0 hτ ρ hρ Q (SeparableClosure (ResidueField A)) H
    (isCyclicQuotientSetting_separableClosure sY x hm hq) φ.symm
    (map_ker_stalkMap_eq_comap j hker Q.genericPoint _ H φ hφ) Bi hBi
  set b : (BY.support.erase P) → ℚ := fun i => BY.coeff i.1
  have hsum : Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P 1 +
      ∑ i, b i • Finsupp.single (Bi i) 1 = Divisor.toQDivisor (divisorOfForm τ) + BY :=
    (add_assoc _ _ _).trans (congrArg _ (single_add_sum_erase_eq hBP))
  obtain ⟨hcoeff, -⟩ := hr b (fun i => hBY0 _) (by rw [hsum]; exact hD)
  have hc := hcoeff BT (by rw [hsum]; exact ⟨hgen, hpb⟩)
  exact Hyperstandard.mem_of_eq_sum hI hI1 Finset.univ r (fun i => (b i : ℝ))
    (fun i _ => hBYI i.1) hm (by rw [hc]; push_cast; rfl) (by exact_mod_cast hBT.2.1 Q)

/-- **One adjunction step keeps hyperstandard coefficients.** Let `(Y, B_Y)` be a dlt pair whose
coefficients lie in `D(I)`, and `(T, B_T)` obtained by one adjunction step onto a prime divisor
`P` of coefficient one, with `(T, B_T)` dlt. Let `Q` be a prime divisor of `T` and
`x = j(η_Q)`. If `x` lies on a second component of `⌊B_Y⌋`, then `Q` is a component of
`T ∩ ⌊B_Y - P⌋` and has coefficient one in `B_T`. Otherwise `P` is the only component of `⌊B_Y⌋`
through `x`, and `coeff_mem_of_isAdjunctionStep_of_forall_ne` applies. -/
private theorem coeff_mem_of_isAdjunctionStep {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {Y T : Scheme.{0}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] {BY : QDivisor Y} (hB : MMP.Intersection.IsDltPair sY BY) {j : T ⟶ Y}
    {BT : QDivisor T} (h : IsAdjunctionStep sY BY j BT) [IsIntegral T] [IsLocallyNoetherian T]
    [IsNormal T] (hBT : MMP.Intersection.IsDltPair (j ≫ sY) BT)
    {I : Finset ℚ} (hI : ∀ b ∈ I, 0 < b ∧ b ≤ 1) (hI1 : (1 : ℚ) ∈ I)
    (hBYI : ∀ P, ((BY.coeff P : ℚ) : ℝ) ∈ hyperstandardSet I) (Q : Mori.PrimeDivisor T) :
    ((BT.coeff Q : ℚ) : ℝ) ∈ hyperstandardSet I := by
  by_cases hA : ∃ P P' : Mori.PrimeDivisor Y, Set.range j.base = (P.support : Set Y) ∧
      P' ≠ P ∧ 1 ≤ BY.coeff P' ∧ j.base Q.genericPoint ∈ (P'.support : Set Y)
  · obtain ⟨P, P', hP, hP'P, hP'1, hxP'⟩ := hA
    rw [coeff_eq_one_of_mem_support_of_ne hB h hP hP'P hP'1 hxP' (hBT.2.1 Q)]
    exact_mod_cast Hyperstandard.one_mem hI1
  push Not at hA
  exact coeff_mem_of_isAdjunctionStep_of_forall_ne hB h hBT hI hI1 hBYI Q hA

end Geometry

section Flag

open MMP.Mori

/-- The support of a prime divisor is a dlt stratum of a dlt pair in which it has coefficient at
least one. -/
private theorem isDltStratum_support {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)} {B : QDivisor X}
    (hB : MMP.Intersection.IsDltPair sX B) (P : MMP.Mori.PrimeDivisor X) (hP : 1 ≤ B.coeff P) :
    IsDltStratum sX B (P.support : Set X) := by
  have hirr : IsIrreducible (P.support : Set X) := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact isIrreducible_singleton.closure
  refine ⟨hB, {P}, Finset.singleton_nonempty P, by simpa using hP, ?_, ?_⟩
  · simpa using hirr.nonempty
  · refine ⟨⟨hirr, by simp⟩, fun T hT hle => ?_⟩
    simpa using hT.2

/-- A normal variety over a field is locally noetherian. -/
private theorem isLocallyNoetherian_of_isNormalVariety {k : Type} [Field k] {T : Scheme.{0}}
    {s : T ⟶ Spec (.of k)} (h : IsNormalVariety k s) : IsLocallyNoetherian T :=
  have := h.1
  LocallyOfFiniteType.isLocallyNoetherian s

/-- The final pair of iterated adjunction data of a dlt pair is dlt. -/
private theorem isDltPair_of_stratumAdjunctionData {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} {B : QDivisor X} (hB : MMP.Intersection.IsDltPair sX B)
    {S : Scheme.{0}} {ι : S ⟶ X} {BS : QDivisor S} (F : StratumAdjunctionData sX B ι BS) :
    have : IsIntegral S := F.isNormalVariety.1.toIsIntegral
    have : IsNormal S := F.isNormalVariety.2
    have := isLocallyNoetherian_of_isNormalVariety F.isNormalVariety
    MMP.Intersection.IsDltPair (ι ≫ sX) BS := by
  induction F with
  | refl h => simpa using hB
  | @step S T ι BS F j BT h ih =>
    have : IsIntegral S := F.isNormalVariety.1.toIsIntegral
    have : IsNormal S := F.isNormalVariety.2
    have := isLocallyNoetherian_of_isNormalVariety F.isNormalVariety
    have h' : IsAdjunctionStep (𝟙 S ≫ ι ≫ sX) BS j BT := by rwa [Category.id_comp]
    obtain ⟨-, P, hP, hrange, -⟩ := h
    let F' : StratumAdjunctionData (ι ≫ sX) BS (j ≫ 𝟙 S) BT := .step (.refl ih.1.1) j BT h'
    have : IsIntegral T := F'.isNormalVariety.1.toIsIntegral
    have : IsNormal T := F'.isNormalVariety.2
    have := isLocallyNoetherian_of_isNormalVariety F'.isNormalVariety
    simpa using (IsDltStratum.exists_isStratumAdjunctionPair_and_isDltPair
      (isDltStratum_support ih P hP)).1.2 F' (by simpa using hrange)

/-- **Hyperstandard coefficients along a flag.** If `(X, B)` is dlt with all coefficients in
`D(I)`, then so are all coefficients of the final pair of every flag of iterated adjunction
data. -/
private theorem coeff_mem_of_stratumAdjunctionData {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} {B : QDivisor X} (hB : MMP.Intersection.IsDltPair sX B)
    {I : Finset ℚ} (hI : ∀ b ∈ I, 0 < b ∧ b ≤ 1) (hI1 : (1 : ℚ) ∈ I)
    (hBI : ∀ P, ((B.coeff P : ℚ) : ℝ) ∈ hyperstandardSet I)
    {S : Scheme.{0}} {ι : S ⟶ X} {BS : QDivisor S} (F : StratumAdjunctionData sX B ι BS) :
    ∀ P, ((BS.coeff P : ℚ) : ℝ) ∈ hyperstandardSet I := by
  induction F with
  | refl h => exact hBI
  | @step S T ι BS F j BT h ih =>
    have : IsIntegral S := F.isNormalVariety.1.toIsIntegral
    have : IsNormal S := F.isNormalVariety.2
    have := isLocallyNoetherian_of_isNormalVariety F.isNormalVariety
    let F' : StratumAdjunctionData sX B (j ≫ ι) BT := .step F j BT h
    have : IsIntegral T := F'.isNormalVariety.1.toIsIntegral
    have : IsNormal T := F'.isNormalVariety.2
    have := isLocallyNoetherian_of_isNormalVariety F'.isNormalVariety
    have hS := isDltPair_of_stratumAdjunctionData hB F
    have hT : MMP.Intersection.IsDltPair (j ≫ ι ≫ sX) BT := by
      simpa using isDltPair_of_stratumAdjunctionData hB F'
    exact coeff_mem_of_isAdjunctionStep hS h hT hI hI1 ih

end Flag

/-- **Hyperstandard coefficients on every projective dlt adjunction stratum.** Let `(X, B)` be a
projective dlt pair (`MMP.Intersection.IsDltPair`) over an algebraically closed field `k` of
characteristic zero, and let `I` be a finite set of rationals in `(0, 1]` containing `1` and
every nonzero coefficient of `B`. Then for every iterated adjunction pair `(S, B_S)` of `(X, B)`
(`MMP.Fourfold.IsStratumAdjunctionPair`), every coefficient of `B_S` lies in the hyperstandard
set `MMP.Fourfold.hyperstandardSet I`. -/
@[mmp "lem_mmp_dlt_stratum_hyperstandard_coefficients"]
public theorem IsStratumAdjunctionPair.coeff_mem_hyperstandardSet {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {B : MMP.Mori.QDivisor X}
    (hB : MMP.Intersection.IsDltPair sX B) (hX : MMP.Mori.IsProjectiveVariety k sX)
    {I : Finset ℚ} (hI : ∀ b ∈ I, 0 < b ∧ b ≤ 1) (hI1 : (1 : ℚ) ∈ I)
    (hBI : ∀ P, B.coeff P ≠ 0 → B.coeff P ∈ I)
    {S : Scheme.{0}} {ι : S ⟶ X} {BS : MMP.Mori.QDivisor S}
    (hS : IsStratumAdjunctionPair sX B ι BS) (P : MMP.Mori.PrimeDivisor S) :
    ((BS.coeff P : ℚ) : ℝ) ∈ hyperstandardSet I := by
  obtain ⟨F⟩ := hS
  refine coeff_mem_of_stratumAdjunctionData hB hI hI1 (fun Q => ?_) F P
  by_cases h0 : B.coeff Q = 0
  · rw [h0, Rat.cast_zero]
    exact Hyperstandard.zero_mem I
  · exact Hyperstandard.mem_of_mem hI (hBI Q h0)

end MMP.Fourfold
