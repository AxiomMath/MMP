module

public import MMP.AlgebraicGeometry.Divisor.WeilSubsheaf.S2
public import MMP.Combinatorics.WeightedGraph.Basic
public import MMP.AlgebraicGeometry.Intersection.RCartierCurveDegree
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyDefs
import MMP.AlgebraicGeometry.Morphisms.Birational.FiniteFibreLocus
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection

/-!
# Auxiliary results for flips

Four independent facts used in the construction of flips.

*`S₂` schemes are Cohen–Macaulay in codimension `≤ 2`.* Let `X` be a scheme locally of finite
type over a field `k` satisfying Serre's condition `S₂`. The set `Z` of points `x ∈ X` whose
local ring `𝒪_{X,x}` is not Cohen–Macaulay is closed, and it contains no point `x` with
`dim 𝒪_{X,x} ≤ 2`: for such a point `S₂` gives `depth 𝒪_{X,x} ≥ min(2, dim 𝒪_{X,x}) =
dim 𝒪_{X,x}`. So `X` is Cohen–Macaulay outside a closed subset of codimension at least three.

*Platonic and Euclidean triples.* For natural numbers `2 ≤ x ≤ y ≤ z`, the inequality
`1/x + 1/y + 1/z > 1` holds exactly for `(2, 2, m)` and `(2, 3, 3)`, `(2, 3, 4)`, `(2, 3, 5)`
(the spherical diagrams `Dₘ₊₂`, `E₆`, `E₇`, `E₈`), and the equation `1/x + 1/y + 1/z = 1` holds
exactly for `(2, 3, 6)`, `(2, 4, 4)`, `(3, 3, 3)` (the Euclidean diagrams `Ẽ₈`, `Ẽ₇`, `Ẽ₆`). The
unordered form of the first over `ℕ+` is `ADEInequality.classification`.

*The system `(**)`.* For a weighted graph `Γ` with matrix `M(Γ)`, a vector `a ∈ ℚ^{V(Γ)}` solves
the system `(*)` `∑_k a_k M(Γ)_{kj} = -c_j(Γ)` exactly when `a - 1` solves the system `(**)`
`∑_k (a_k - 1) M(Γ)_{kj} = -d_j(Γ)`, since `c_j(Γ) + ∑_k M(Γ)_{kj} = d_j(Γ)`.

*Relatively ample pull-backs.* Let `f : Y ⟶ V` be a proper birational morphism from a normal
integral Noetherian scheme to a normal integral locally Noetherian scheme and `M` an `ℝ`-Cartier
divisor on `V` whose pull-back `G` is `f`-ample. Clearing denominators in the two presentations of
`G` gives a Cartier divisor `A` on `Y` which is `f`-ample and which, over a small affine open
`U ⊆ V`, has a local equation on `f⁻¹(U)`. So the trivial line bundle is ample on `f⁻¹(U)`, and
`f⁻¹(U)` is quasi-affine. A quasi-affine scheme universally closed over an affine scheme is affine,
so `f` is affine and proper, hence finite; a finite birational morphism onto a normal integral
scheme is an isomorphism.

## Main results

* `MMP.Flips.isClosed_setOf_not_isCohenMacaulayLocalRing_of_satisfiesS2`: the
  non-Cohen–Macaulay locus of an `S₂` scheme locally of finite type over a field is closed and
  avoids every point whose local ring has dimension `≤ 2`.
* `MMP.Flips.inv_add_inv_add_inv_eq_one_iff`: the solutions of `1/x + 1/y + 1/z = 1` with
  `2 ≤ x ≤ y ≤ z`.
* `MMP.Flips.one_lt_inv_add_inv_add_inv_iff`: the solutions of `1/x + 1/y + 1/z > 1` with
  `2 ≤ x ≤ y ≤ z`.
* `MMP.Flips.WeightedGraph.isLogDiscrepancyVector_iff`: `a` is a log discrepancy vector of `Γ`
  if and only if `∑_k (a_k - 1) M(Γ)_{kj} = -d_j(Γ)` for every `j`.
* `MMP.Flips.isIso_of_isRelativelyAmple_of_isRCartierPullback`: if an `f`-ample `ℝ`-divisor `G`
  is a pull-back of an `ℝ`-Cartier divisor along the proper birational morphism `f`, then `f` is
  an isomorphism.

## Implementation notes

The integers of the triple classifications are taken in `ℕ` (under `2 ≤ x` this is the same set
of triples as in `ℤ`) and the reciprocals are computed in `ℚ`.

The source states the pull-back result for a `ℚ`-Cartier `ℚ`-divisor `M`; we state it for an
`ℝ`-Cartier divisor, written as a real combination of Cartier divisors, which includes the
rational case. The source shows finiteness of `f` through the fibres: an ample bundle that is
trivial on a fibre forces the fibre to be finite. We argue instead with quasi-affineness of
`f⁻¹(U)`, which is the same fact (Stacks, Tag 01QE) read before restricting to the fibres, and
needs no curves.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], (3.0.2),
  3.2.2, proof of Proposition 4.2, proof of 16.4
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace MMP.Flips

section CohenMacaulay

open IsLocalRing

/-- A Noetherian local ring carrying a regular sequence in its maximal ideal whose length is at
least its Krull dimension is Cohen–Macaulay. -/
private lemma isCohenMacaulayLocalRing_of_isRegular_of_ringKrullDim_le {R : Type*} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] {s : List R} (hmem : ∀ a ∈ s, a ∈ maximalIdeal R)
    (hreg : RingTheory.Sequence.IsRegular R s) (hlen : ringKrullDim R ≤ s.length) :
    IsCohenMacaulayLocalRing R :=
  le_antisymm depthSup_le_supportDim <| ((Module.supportDim_self_eq_ringKrullDim R).trans_le
    hlen).trans (mod_cast Module.le_depthSup hmem hreg)

/-- **An `S₂` scheme is Cohen–Macaulay in codimension `≤ 2`.** Let `X` be a scheme locally of
finite type over a field `k` satisfying `S₂`. Then the set of points where `X` is not
Cohen–Macaulay is closed, and every point `x` with `dim 𝒪_{X,x} ≤ 2` has a Cohen–Macaulay
local ring. -/
@[mmp "lem_fa16a_s2_cm_outside_codim_three"]
theorem isClosed_setOf_not_isCohenMacaulayLocalRing_of_satisfiesS2
    {k : Type u} [Field k] {X : Scheme.{u}} [IsLocallyNoetherian X]
    (π : X ⟶ Spec (.of k)) [LocallyOfFiniteType π] (hX : SatisfiesS2 X) :
    IsClosed {x : X | ¬ IsCohenMacaulayLocalRing (X.presheaf.stalk x)} ∧
      ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 2 →
        IsCohenMacaulayLocalRing (X.presheaf.stalk x) := by
  refine ⟨isClosed_setOf_not_isCohenMacaulayLocalRing π, fun x hx => ?_⟩
  obtain ⟨s, hmem, hreg, hlen⟩ := hX x
  exact isCohenMacaulayLocalRing_of_isRegular_of_ringKrullDim_le hmem hreg
    (by rwa [min_eq_right hx] at hlen)

end CohenMacaulay

section Triples

/-- Antitonicity of `n ↦ (n : ℚ)⁻¹` on positive naturals. -/
private lemma natCast_inv_le_inv {n a : ℕ} (hn : 0 < n) (h : n ≤ a) :
    (a : ℚ)⁻¹ ≤ (n : ℚ)⁻¹ :=
  inv_anti₀ (by exact_mod_cast hn) (by exact_mod_cast h)

/-- If `2 ≤ x ≤ y ≤ z` and `1/x + 1/y + 1/z = 1`, then `x ≤ 3` and `y ≤ 4`: otherwise the sum
is at most `3/4`, resp. `1/2 + 2/5`. -/
private lemma le_three_and_le_four_of_inv_add_inv_add_inv_eq_one {x y z : ℕ} (hx : 2 ≤ x)
    (hxy : x ≤ y) (hyz : y ≤ z) (h : (x : ℚ)⁻¹ + (y : ℚ)⁻¹ + (z : ℚ)⁻¹ = 1) : x ≤ 3 ∧ y ≤ 4 := by
  have h1 := natCast_inv_le_inv (by omega) hxy
  have h2 := natCast_inv_le_inv (by omega) hyz
  have h3 := natCast_inv_le_inv (by norm_num) hx
  constructor <;> by_contra! hc
  · have := natCast_inv_le_inv (by norm_num) (show 4 ≤ x by omega)
    norm_num at *
    linarith
  · have := natCast_inv_le_inv (by norm_num) (show 5 ≤ y by omega)
    norm_num at *
    linarith

/-- For natural numbers `2 ≤ x ≤ y ≤ z`, `1/x + 1/y + 1/z = 1` if and only if `(x, y, z)` is one
of `(2, 3, 6)`, `(2, 4, 4)`, `(3, 3, 3)`. -/
@[mmp "lem_fa3_euclidean_triples"]
theorem inv_add_inv_add_inv_eq_one_iff {x y z : ℕ} (hx : 2 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) :
    (x : ℚ)⁻¹ + (y : ℚ)⁻¹ + (z : ℚ)⁻¹ = 1 ↔
      (x, y, z) = (2, 3, 6) ∨ (x, y, z) = (2, 4, 4) ∨ (x, y, z) = (3, 3, 3) := by
  refine ⟨fun h ↦ ?_, by rintro (h | h | h) <;> simp_all <;> norm_num⟩
  obtain ⟨hx3, hy4⟩ := le_three_and_le_four_of_inv_add_inv_add_inv_eq_one hx hxy hyz h
  have hz : (z : ℚ) ≠ 0 := by norm_cast; omega
  simp only [Prod.mk.injEq]
  interval_cases x <;> interval_cases y <;> field_simp at h <;> norm_cast at h <;> omega

/-- The bounds forced by `1/x + 1/y + 1/z > 1` for `2 ≤ x ≤ y ≤ z`: `x = 2`, and either
`y = 2` or `y = 3` and `z < 6`. -/
private lemma eq_two_and_bounds_of_one_lt {x y z : ℕ} (hx : 2 ≤ x) (hxy : x ≤ y)
    (hyz : y ≤ z) (h : 1 < (x : ℚ)⁻¹ + (y : ℚ)⁻¹ + (z : ℚ)⁻¹) :
    x = 2 ∧ (y = 2 ∨ y = 3 ∧ z < 6) := by
  obtain rfl : x = 2 := by
    by_contra! hc
    have h3 : 3 ≤ x := by omega
    have := natCast_inv_le_inv (by norm_num) h3
    have := natCast_inv_le_inv (by norm_num) (h3.trans hxy)
    have := natCast_inv_le_inv (by norm_num) ((h3.trans hxy).trans hyz)
    norm_num at *
    linarith
  refine ⟨rfl, ?_⟩
  obtain rfl | rfl | h4 : y = 2 ∨ y = 3 ∨ 4 ≤ y := by omega
  · exact .inl rfl
  · refine .inr ⟨rfl, ?_⟩
    by_contra! h6
    have := natCast_inv_le_inv (by norm_num) h6
    norm_num at *
    linarith
  · have := natCast_inv_le_inv (by norm_num) h4
    have := natCast_inv_le_inv (by norm_num) (h4.trans hyz)
    norm_num at *
    linarith

/-- For natural numbers `2 ≤ x ≤ y ≤ z`, `1/x + 1/y + 1/z > 1` if and only if `(x, y, z)` is
`(2, 2, m)` for some `m`, or one of `(2, 3, 3)`, `(2, 3, 4)`, `(2, 3, 5)`. -/
@[mmp "lem_fa3_platonic_triples"]
theorem one_lt_inv_add_inv_add_inv_iff {x y z : ℕ} (hx : 2 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) :
    1 < (x : ℚ)⁻¹ + (y : ℚ)⁻¹ + (z : ℚ)⁻¹ ↔
      (x, y) = (2, 2) ∨ (x, y, z) = (2, 3, 3) ∨ (x, y, z) = (2, 3, 4) ∨
        (x, y, z) = (2, 3, 5) := by
  constructor
  · intro h
    obtain ⟨rfl, rfl | ⟨rfl, hz⟩⟩ := eq_two_and_bounds_of_one_lt hx hxy hyz h
    · simp
    · interval_cases z <;> simp
  · rintro (h | h | h | h) <;> simp only [Prod.mk.injEq] at h
    · obtain ⟨rfl, rfl⟩ := h
      norm_num
      positivity
    all_goals
      obtain ⟨rfl, rfl, rfl⟩ := h
      norm_num

end Triples

namespace WeightedGraph

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The column sums of `M(Γ)` measure the difference of `d` and `c`:
`c_j + ∑_k M(Γ)_{kj} = d_j`. -/
private lemma c_add_sum_matrix_col (Γ : WeightedGraph V) (j : V) :
    Γ.c j + ∑ k, (Γ.matrix k j : ℚ) = Γ.d j := by
  rw [← add_sum_erase _ _ (mem_univ j),
    sum_congr rfl fun k hk => (by simp [WeightedGraph.matrix, ne_of_mem_erase hk,
      Γ.edgeWeight_symm k j] : _ = (Γ.edgeWeight j k : ℚ))]
  simp [WeightedGraph.matrix, WeightedGraph.c, WeightedGraph.d]
  ring

/-- A vector `a ∈ ℚ^{V(Γ)}` is a log discrepancy vector of the weighted graph `Γ` if and only if
`∑_k (a_k - 1) M(Γ)_{kj} = -d_j(Γ)` for every vertex `j` (the system `(**)` of FA 3.0.2). -/
@[mmp "lem_fa3_system_star_star"]
theorem isLogDiscrepancyVector_iff (Γ : WeightedGraph V) (a : V → ℚ) :
    Γ.IsLogDiscrepancyVector a ↔
      ∀ j, ∑ k, (a k - 1) * (Γ.matrix k j : ℚ) = -Γ.d j := by
  refine forall_congr' fun j => ?_
  rw [← c_add_sum_matrix_col]
  simp only [sub_mul, one_mul, sum_sub_distrib]
  constructor <;> intro h <;> linarith

end WeightedGraph

section RelativelyAmplePullback

open MMP.Mori

/-- A quasi-affine scheme which is universally closed over an affine scheme is affine. -/
private theorem isAffine_of_isQuasiAffine_of_universallyClosed {X Y : Scheme.{u}} (g : X ⟶ Y)
    [X.IsQuasiAffine] [IsAffine Y] [UniversallyClosed g] : IsAffine X := by
  have hfac : X.toSpecΓ ≫ (Spec.map g.appTop ≫ Y.isoSpec.inv) = g := by
    rw [← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
      Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]
  have : UniversallyClosed (X.toSpecΓ ≫ (Spec.map g.appTop ≫ Y.isoSpec.inv)) := by
    rw [hfac]
    infer_instance
  have : UniversallyClosed X.toSpecΓ :=
    UniversallyClosed.of_comp_of_isSeparated _ (Spec.map g.appTop ≫ Y.isoSpec.inv)
  have : IsClosedImmersion X.toSpecΓ :=
    IsClosedImmersion.of_isPreimmersion _ X.toSpecΓ.isClosedMap.isClosed_range
  exact isAffine_of_isAffineHom X.toSpecΓ

/-- A proper morphism is finite if every point of the target has an affine neighbourhood with
quasi-affine preimage. -/
private theorem isFinite_of_isProper_of_isQuasiAffine_preimage {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f]
    (H : ∀ y : Y, ∃ U : Y.Opens, y ∈ U ∧ IsAffineOpen U ∧ (f ⁻¹ᵁ U).toScheme.IsQuasiAffine) :
    IsFinite f := by
  have : IsAffineHom f := by
    refine isAffineHom_of_forall_exists_isAffineOpen f fun y => ?_
    obtain ⟨U, hy, hU, hq⟩ := H y
    refine ⟨U, hy, hU, ?_⟩
    have : IsAffine U.toScheme := hU
    exact isAffine_of_isQuasiAffine_of_universallyClosed (f ∣_ U)
  exact (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType f).mpr
    ⟨IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩,
      inferInstance⟩

/-- On a scheme separated over an affine scheme, a tensor product of two ample invertible modules
is ample. -/
private theorem isAmple_tensorModules {X S : Scheme.{u}} [IsAffine S] (t : X ⟶ S) [IsSeparated t]
    (L M : X.Modules) [Stacks.Ample.IsInvertibleModule X L] [Stacks.Ample.IsInvertibleModule X M]
    [Stacks.Ample.IsInvertibleModule X (Stacks.RelativeVeryAmple.tensorModules X L M)]
    (hL : Stacks.Ample.IsAmple X L) (hM : Stacks.Ample.IsAmple X M) :
    Stacks.Ample.IsAmple X (Stacks.RelativeVeryAmple.tensorModules X L M) := by
  have h1 := Stacks.AmpleFibreNeighbourhood.isRelativelyAmple_pullbackModule_of_isAffineHom
    (pullback.diagonal t) (pullback.fst t t ≫ t) _
    (Stacks.AmpleExternalTensor.isRelativelyAmple_externalTensor t t L M
      ((Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple t L).mpr hL)
      ((Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple t M).mpr hM))
  have e := Stacks.AmpleExternalTensor.pullbackExternalTensorIso t t (pullback.diagonal t) L M
  simp only [pullback.diagonal_fst, pullback.diagonal_snd] at e
  have eid : ∀ N : X.Modules,
      (RingedSpaceModuleAdjunction.modulePullback (Scheme.Hom.toLRSHom (𝟙 X)).toShHom).obj N ≅
        N := fun N =>
    (Adjunction.leftAdjointUniq
      (RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction
        (Scheme.Hom.toLRSHom (𝟙 X)).toShHom)
      (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X))).app N ≪≫
      (Scheme.Modules.pullbackId X).app N
  rw [pullback.diagonal_fst_assoc] at h1
  rw [← Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple t]
  exact (Stacks.RelativeVeryAmple.isRelativelyAmple_congr _ _ _
    (e ≪≫ Stacks.RelativeVeryAmple.tensorModulesMapIso X (eid L) (eid M))).mp h1

/-- The sum of two `f`-ample Cartier divisors is `f`-ample. -/
private theorem isRelativelyAmpleCartier_add {Y V : Scheme.{u}} [IsLocallyNoetherian Y]
    [IsNormal Y] [CompactSpace Y] {f : Y ⟶ V} [IsSeparated f] {A B : Divisor Y}
    (hA : IsRelativelyAmpleCartier f A) (hB : IsRelativelyAmpleCartier f B) :
    IsRelativelyAmpleCartier f (A + B) := by
  obtain ⟨hAc, hAa⟩ := hA
  obtain ⟨hBc, hBa⟩ := hB
  have := hAc.isInvertibleModule_divisorialSheaf
  have := hBc.isInvertibleModule_divisorialSheaf
  have := (hAc.add hBc).isInvertibleModule_divisorialSheaf
  refine ⟨hAc.add hBc, fun U hU => ?_⟩
  have : IsAffine U.toScheme := hU
  have e := (RingedSpaceModuleAdjunction.modulePullback (f ⁻¹ᵁ U).ι.toLRSHom.toShHom).mapIso
      (hAc.divisorialSheafTensorIso hBc).symm ≪≫
    Stacks.RelativeVeryAmple.pullbackTensorModulesIso (f ⁻¹ᵁ U).ι _ _
  have := Stacks.AmplePullbackPart1.isInvertibleModule_tensorModules (f ⁻¹ᵁ U).toScheme
    ((RingedSpaceModuleAdjunction.modulePullback (f ⁻¹ᵁ U).ι.toLRSHom.toShHom).obj
      A.divisorialSheaf)
    ((RingedSpaceModuleAdjunction.modulePullback (f ⁻¹ᵁ U).ι.toLRSHom.toShHom).obj
      B.divisorialSheaf)
  exact (Stacks.RelativeVeryAmple.isAmple_congr _ _ e).mpr
    (isAmple_tensorModules (f ∣_ U) _ _ (hAa U hU) (hBa U hU))

/-- Finitely many rationals have a common positive denominator. -/
private theorem exists_pos_nat_mul_eq_int {ι : Type*} [Finite ι] (x : ι → ℚ) :
    ∃ N : ℕ, 0 < N ∧ ∀ i, ∃ z : ℤ, (N : ℚ) * x i = z := by
  classical
  have := Fintype.ofFinite ι
  refine ⟨∏ l, (x l).den, Finset.prod_pos fun l _ => (x l).den_pos, fun i => ?_⟩
  refine ⟨(∏ l ∈ Finset.univ.erase i, ((x l).den : ℤ)) * (x i).num, ?_⟩
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  push_cast
  rw [mul_comm ((x i).den : ℚ), mul_assoc, Rat.den_mul_eq_num]

/-- If a positive real combination of the integer vectors `a i` equals a real combination of the
integer vectors `b j`, then a positive rational combination of the `a i` equals a rational
combination of the `b j`. -/
private theorem exists_pos_rat_relation {P : Type*} {m k : ℕ} (s : Fin m → ℝ)
    (hs : ∀ i, 0 < s i) (r : Fin k → ℝ) (a : Fin m → P → ℤ) (b : Fin k → P → ℤ)
    (h : ∀ p, ∑ i, s i * a i p = ∑ j, r j * b j p) :
    ∃ α : Fin m → ℚ, (∀ i, 0 < α i) ∧ ∃ β : Fin k → ℚ,
      ∀ p, ∑ i, α i * a i p = ∑ j, β j * b j p := by
  classical
  let W : Submodule ℚ ℝ := Submodule.span ℚ (Set.range s ∪ Set.range r)
  have : FiniteDimensional ℚ W :=
    FiniteDimensional.span_of_finite ℚ ((Set.finite_range s).union (Set.finite_range r))
  let sW : Fin m → W := fun i => ⟨s i, Submodule.subset_span (Or.inl ⟨i, rfl⟩)⟩
  let rW : Fin k → W := fun j => ⟨r j, Submodule.subset_span (Or.inr ⟨j, rfl⟩)⟩
  let bW := Module.finBasis ℚ W
  let cs : Fin m → _ := fun i => bW.repr (sW i)
  let cr : Fin k → _ := fun j => bW.repr (rW j)
  have key : ∀ p, ∑ i, (a i p : ℚ) • cs i = ∑ j, (b j p : ℚ) • cr j := by
    intro p
    have hw : ∑ i, (a i p : ℚ) • sW i = ∑ j, (b j p : ℚ) • rW j := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, Submodule.coe_smul, sW, rW, Rat.cast_intCast,
        Rat.smul_def]
      simpa [mul_comm] using h p
    simpa [map_sum, cs, cr] using congrArg bW.repr hw
  have hexp : ∀ i, s i = ∑ t, (cs i t : ℝ) * (bW t : ℝ) := by
    intro i
    have := congrArg Subtype.val (bW.sum_repr (sW i))
    simp only [Submodule.coe_sum, Submodule.coe_smul, Rat.smul_def] at this
    exact this.symm
  let O : Set (Fin _ → ℝ) := {x | ∀ i, 0 < ∑ t, (cs i t : ℝ) * x t}
  have hO : IsOpen O := by
    simp only [O, Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (by fun_prop)
  have hOne : O.Nonempty := ⟨fun t => (bW t : ℝ), fun i => by rw [← hexp]; exact hs i⟩
  obtain ⟨q, hq⟩ := (DenseRange.piMap fun _ => Rat.denseRange_cast).exists_mem_open hO hOne
  let α : Fin m → ℚ := fun i => ∑ t, cs i t * q t
  let β : Fin k → ℚ := fun j => ∑ t, cr j t * q t
  have hα : ∀ i, 0 < α i := fun i => by
    have := hq i
    simp only [Pi.map_apply] at this
    exact_mod_cast this
  have hrel : ∀ p, ∑ i, α i * a i p = ∑ j, β j * b j p := by
    intro p
    have := fun t => congrArg (fun g => g t * q t) (key p)
    simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply,
      smul_eq_mul, Finset.sum_mul] at this
    calc ∑ i, α i * a i p = ∑ t, ∑ i, (a i p : ℚ) * cs i t * q t := by
          simp only [α, Finset.sum_mul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun i _ => by ring
      _ = ∑ t, ∑ j, (b j p : ℚ) * cr j t * q t := Finset.sum_congr rfl fun t _ => this t
      _ = ∑ j, β j * b j p := by
          simp only [β, Finset.sum_mul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun i _ => by ring
  exact ⟨α, hα, β, hrel⟩

/-- **Clearing denominators in a real relation with integer coefficients.** If a positive real
combination of the integer vectors `a i` equals a real combination of the integer vectors `b j`,
then a positive integer combination of the `a i` equals an integer combination of the `b j`. -/
private theorem exists_pos_int_relation {P : Type*} {m k : ℕ} (s : Fin m → ℝ)
    (hs : ∀ i, 0 < s i) (r : Fin k → ℝ) (a : Fin m → P → ℤ) (b : Fin k → P → ℤ)
    (h : ∀ p, ∑ i, s i * a i p = ∑ j, r j * b j p) :
    ∃ n : Fin m → ℤ, (∀ i, 0 < n i) ∧ ∃ c : Fin k → ℤ,
      ∀ p, ∑ i, n i * a i p = ∑ j, c j * b j p := by
  obtain ⟨α, hα, β, hrel⟩ := exists_pos_rat_relation s hs r a b h
  obtain ⟨N, hN, hz⟩ := exists_pos_nat_mul_eq_int (Sum.elim α β)
  choose z hz using hz
  refine ⟨fun i => z (Sum.inl i), fun i => ?_, fun j => z (Sum.inr j), fun p => ?_⟩
  · have h1 := hz (Sum.inl i)
    simp only [Sum.elim_inl] at h1
    have : (0 : ℚ) < z (Sum.inl i) := h1 ▸ mul_pos (by exact_mod_cast hN) (hα i)
    exact_mod_cast this
  · have h2 : ((∑ i, z (Sum.inl i) * a i p : ℤ) : ℚ) = ((∑ j, z (Sum.inr j) * b j p : ℤ) : ℚ) := by
      push_cast
      simp only [← hz, Sum.elim_inl, Sum.elim_inr, mul_assoc, ← Finset.mul_sum, hrel p]
    exact_mod_cast h2

/-- A positive multiple of an `f`-ample Cartier divisor is `f`-ample. -/
private theorem isRelativelyAmpleCartier_nsmul {Y V : Scheme.{u}} [IsLocallyNoetherian Y]
    [IsNormal Y] [CompactSpace Y] {f : Y ⟶ V} [IsSeparated f] {A : Divisor Y}
    (hA : IsRelativelyAmpleCartier f A) {n : ℕ} (hn : 1 ≤ n) :
    IsRelativelyAmpleCartier f (n • A) := by
  induction n, hn using Nat.le_induction with
  | base => simpa using hA
  | succ n _ ih =>
    rw [succ_nsmul]
    exact isRelativelyAmpleCartier_add ih hA

/-- A positive integer combination of `f`-ample Cartier divisors is `f`-ample. -/
private theorem isRelativelyAmpleCartier_sum {Y V : Scheme.{u}}
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] {f : Y ⟶ V} [IsSeparated f] {m : ℕ}
    (hm : 1 ≤ m) {A : Fin m → Divisor Y} (hA : ∀ i, IsRelativelyAmpleCartier f (A i))
    {n : Fin m → ℤ} (hn : ∀ i, 0 < n i) : IsRelativelyAmpleCartier f (∑ i, n i • A i) := by
  refine Finset.sum_induction_nonempty _ (IsRelativelyAmpleCartier f)
    (fun _ _ => isRelativelyAmpleCartier_add) ⟨⟨0, hm⟩, Finset.mem_univ _⟩ fun i _ => ?_
  rw [show n i • A i = (n i).toNat • A i by rw [← natCast_zsmul, Int.toNat_of_nonneg (hn i).le]]
  exact isRelativelyAmpleCartier_nsmul (hA i) (by have := hn i; omega)

/-- An integer combination of divisors which have local equations on `f⁻¹(U)` for small
neighbourhoods `U` of every point of the base has the same property. -/
private theorem exists_isLocalEquation_preimage_sum {Y V : Scheme.{u}}
    [IsLocallyNoetherian Y] [IsNormal Y] (f : Y ⟶ V) {ι : Type*} (S : Finset ι)
    (D : ι → Divisor Y) (c : ι → ℤ)
    (hD : ∀ j, ∀ v : V, ∃ U : V.Opens, v ∈ U ∧ ∃ φ, (D j).IsLocalEquation (f ⁻¹ᵁ U) φ)
    (v : V) : ∃ U : V.Opens, v ∈ U ∧ ∃ φ, (∑ j ∈ S, c j • D j).IsLocalEquation (f ⁻¹ᵁ U) φ := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨⊤, trivial, 1, by simpa using Divisor.isLocalEquation_zero _⟩
  | insert j S hj ih =>
    obtain ⟨U, hvU, φ, hφ⟩ := ih
    obtain ⟨U', hvU', ψ, hψ⟩ := hD j v
    refine ⟨U ⊓ U', ⟨hvU, hvU'⟩, ψ ^ c j * φ, ?_⟩
    rw [Finset.sum_insert hj]
    exact ((hψ.mono (f.preimage_mono inf_le_right)).zsmul (c j)).add
      (hφ.mono (f.preimage_mono inf_le_left))

/-- Clearing denominators: an `f`-ample pull-back of an `ℝ`-Cartier divisor yields an `f`-ample
Cartier divisor which has a local equation over a neighbourhood of every point of the base. -/
private theorem exists_isRelativelyAmpleCartier_isLocalEquation {Y V : Scheme.{u}}
    [IsIntegral Y] [IsNoetherian Y] [IsNormal Y]
    [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    (f : Y ⟶ V) [IsSeparated f]
    {M : Mori.RDivisor V} {G : Mori.RDivisor Y} (hG : IsRCartierPullback f M G)
    (hGA : IsRelativelyAmple f G) :
    ∃ A : Divisor Y, IsRelativelyAmpleCartier f A ∧
      ∀ v : V, ∃ U : V.Opens, v ∈ U ∧ ∃ φ, A.IsLocalEquation (f ⁻¹ᵁ U) φ := by
  obtain ⟨k, r, L, L', hLc, -, hpb, hGr⟩ := hG
  obtain ⟨m, s, A, hm, hs, hA, hGs⟩ := hGA
  have hcoeff : ∀ p, ∑ i, s i * (A i p : ℝ) = ∑ j, r j * (L' j p : ℝ) := by
    intro p
    have := congrArg (fun D : RDivisor Y => D p) (hGs.symm.trans hGr)
    simp only [Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul] at this
    exact this
  obtain ⟨n, hn, c, hrel⟩ :=
    exists_pos_int_relation s hs r (fun i p => A i p) (fun j p => L' j p) hcoeff
  have hDeq : ∑ i, n i • A i = ∑ j, c j • L' j := by
    refine Finsupp.ext fun p => ?_
    simpa [Finsupp.finsetSum_apply] using hrel p
  refine ⟨∑ i, n i • A i, isRelativelyAmpleCartier_sum hm hA hn, fun v => ?_⟩
  rw [hDeq]
  refine exists_isLocalEquation_preimage_sum f Finset.univ L' c (fun j v => ?_) v
  obtain ⟨U, hvU, φ, hφ⟩ := hLc j v
  exact ⟨U, hvU, _, (hpb j).2.isLocalEquation hφ⟩

/-- If an `f`-ample Cartier divisor `A` has a local equation on `f⁻¹(U)` for an affine open `U`,
then `f⁻¹(U)` is quasi-affine: the trivial bundle is ample on it. -/
private theorem isQuasiAffine_preimage_of_isLocalEquation {Y V : Scheme.{u}}
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    {f : Y ⟶ V} {A : Divisor Y} (hA : IsRelativelyAmpleCartier f A) {U : V.Opens}
    (hU : IsAffineOpen U) {φ : (RationalFunctions Y)ˣ} (hφ : A.IsLocalEquation (f ⁻¹ᵁ U) φ) :
    (f ⁻¹ᵁ U).toScheme.IsQuasiAffine := by
  obtain ⟨hAc, hamp⟩ := hA
  have := hAc.isInvertibleModule_divisorialSheaf
  have e := MMP.Threefold.Resolution.modulePullbackIsoRestrict' (f ⁻¹ᵁ U) A.divisorialSheaf ≪≫
    hφ.restrictDivisorialSheafIso
  exact (Stacks.RelativeVeryAmple.isQuasiAffine_iff_isAmple_of_iso_unitModule _ _ e).mpr
    (hamp U hU)

/-- A proper birational morphism `f : Y ⟶ V` from a normal integral Noetherian scheme to a normal
integral locally Noetherian scheme is an isomorphism if the pull-back `G = f^*M` of some
`ℝ`-Cartier divisor `M` on `V` is `f`-ample. -/
@[mmp "lem_fa4_relatively_ample_pullback_iso"]
theorem isIso_of_isRelativelyAmple_of_isRCartierPullback {Y V : Scheme.{u}}
    [IsIntegral Y] [IsNoetherian Y] [IsNormal Y]
    [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    (f : Y ⟶ V) [IsProper f] (hf : Mori.IsBirationalMorphism f)
    {M : Mori.RDivisor V} {G : Mori.RDivisor Y} (hG : IsRCartierPullback f M G)
    (hGA : IsRelativelyAmple f G) : IsIso f := by
  obtain ⟨A, hA, hloc⟩ := exists_isRelativelyAmpleCartier_isLocalEquation f hG hGA
  have : IsFinite f := by
    refine isFinite_of_isProper_of_isQuasiAffine_preimage f fun v => ?_
    obtain ⟨U, hvU, φ, hφ⟩ := hloc v
    obtain ⟨W, hW, hvW, hWU'⟩ := exists_isAffineOpen_mem_and_subset hvU
    exact ⟨W, hvW, hW,
      isQuasiAffine_preimage_of_isLocalEquation hA hW (hφ.mono (f.preimage_mono hWU'))⟩
  exact (MMP.Resolution.Bridges.isOpen_finiteFibreLocus_and_isIso f
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hf)).2 this

end RelativelyAmplePullback

end MMP.Flips

end
