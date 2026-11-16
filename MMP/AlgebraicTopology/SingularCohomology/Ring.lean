module

public import MMP.AlgebraicTopology.SingularCohomology.EvenRing

/-!
# The cohomology ring `H^* Y = ⨁_i H^i(Y; R)` (Fulton, §19.1)

For a topological space `Y` and a commutative ring `R`, the cup product
`H^i Y × H^j Y → H^{i+j} Y` of singular cohomology, with unit `1 ∈ H^0 Y`, makes
`H^* Y = ⨁_{i ≥ 0} H^i(Y; R)` an associative, `ℤ_{≥0}`-graded ring (graded commutative with the
sign `(-1)^{ij}`, `MMP.cohomologyWithSupports.cup_comm`). The even part
`⨁_p H^{2p} Y` (`MMP.EvenCohomologyRing`) embeds as a subring: the ring homomorphism
`EvenCohomologyRing R Y →+* CohomologyRing R Y` sending `H^{2p} Y` to the summand `H^{2p} Y` is
injective.

*Proof.* As for the even ring (`MMP.EvenCohomologyRing`): on absolute classes the cup product
is the class of the Alexander–Whitney cup of cocycles, which is strictly associative with the
constant `0`-cochain `1` as two-sided unit.

## Main definitions

* `MMP.cupNatUniv`: the cup product `H^i Y × H^j Y → H^{i+j} Y`, `i, j : ℕ`.
* `MMP.CohomologyRing R Y`: `⨁_i H^i(Y; R)`, a ring under the cup product
  (`MMP.CohomologyRing.gRing`).
* `MMP.CohomologyRing.ofEven`: the ring homomorphism
  `EvenCohomologyRing R Y →+* CohomologyRing R Y`.

## Main results

* `MMP.CohomologyRing.of_mul_of`: the product of homogeneous classes is their cup
  product.
* `MMP.CohomologyRing.ofEven_of`: `ofEven` sends `c ∈ H^{2p} Y` to `c` in degree
  `2p`.
* `MMP.CohomologyRing.ofEven_injective`: `ofEven` is injective.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
* [A. Dold, *Lectures on Algebraic Topology*][dold1995], VII.8.
-/

@[expose] public noncomputable section

open Set DirectSum

universe u

namespace MMP

open SingularChain SingularCochain PoincareAlexander
open MMP.cohomologyWithSupports (ofCocycle ofCocycle_congr exists_ofCocycle_eq congrIndex_symm_mk')

variable {R : Type u} [CommRing R]

variable (R) in
/-- The cup product `H^i Y × H^j Y → H^{i+j} Y` of absolute cohomology classes, `i, j : ℕ`. -/
def cupNatUniv (Y : TopCat.{u}) (i j : ℕ) :
    cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ (i : ℕ) →ₗ[R]
      cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ (j : ℕ) →ₗ[R]
        cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ (i + j : ℕ) :=
  (cohomologyWithSupports.cup R Y isClosed_univ isClosed_univ (i : ℕ) (j : ℕ)).compr₂
    (cohomologyWithSupports.congrIndex R Y (by rw [Set.univ_inter])
      (by push_cast; ring)).toLinearMap

/-- On classes of cocycles, `cupNatUniv` is the class of the Alexander–Whitney cup product. -/
lemma cupNatUniv_ofCocycle (Y : TopCat.{u}) (i j : ℕ) {φ : Simplex Y i → R}
    (hφ : φ ∈ relCocycles R (univᶜ : Set Y) i) {ψ : Simplex Y j → R}
    (hψ : ψ ∈ relCocycles R (univᶜ : Set Y) j) :
    cupNatUniv R Y i j (ofCocycle R Y i φ hφ) (ofCocycle R Y j ψ hψ) =
      ofCocycle R Y (i + j) (cup i j (i + j) rfl φ ψ)
        (cup_mem_relCocycles_compl_univ rfl hφ hψ) := by
  rw [cupNatUniv, LinearMap.compr₂_apply, LinearEquiv.coe_coe,
    cohomologyWithSupports.cup_natCast_eq R Y isClosed_univ isClosed_univ i j (i + j) rfl,
    cohomologyWithSupports.congrIndex_congrIndex, ofCocycle, ofCocycle,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, relCup_mk]
  refine (congrIndex_symm_mk' (S' := (univᶜ : Set Y)) (by rw [union_self]) _
    (relCupCocycles (R := R) isClosed_univ.isOpen_compl isClosed_univ.isOpen_compl i j (i + j) rfl
      ⟨φ, hφ⟩ ⟨ψ, hψ⟩)
    ⟨(relCupCocycles (R := R) isClosed_univ.isOpen_compl isClosed_univ.isOpen_compl i j (i + j)
      rfl ⟨φ, hφ⟩ ⟨ψ, hψ⟩ : Simplex Y (i + j) → R), by
        refine ⟨fun σ hσ ↦ mem_vanishing_empty (Z := Y) _ σ (by rwa [compl_univ] at hσ), ?_⟩
        exact (relCupCocycles (R := R) isClosed_univ.isOpen_compl isClosed_univ.isOpen_compl
          i j (i + j) rfl ⟨φ, hφ⟩ ⟨ψ, hψ⟩).2.2⟩ rfl).trans ?_
  rw [ofCocycle]
  congr 1
  rw [Submodule.Quotient.eq]
  exact pullback_smallChainMap_sub_mem_relCoboundaries _
    (cup_mem_relCocycles_compl_univ rfl hφ hψ)

namespace CohomologyRing

variable (Y : TopCat.{u})

variable (R) in
/-- The unit `1 ∈ H^0 Y`: the class of the constant `0`-cocycle `1`. -/
def oneNat : cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ ((0 : ℕ) : ℤ) :=
  ofCocycle R Y 0 (constCochain 0 1)
    (cohomologyWithSupports.constCochain_one_mem_relCocycles_compl_univ Y)

variable {Y}

/-- Transport of a class of a cup product along an equality of degrees. -/
lemma gradedMonoid_mk_ofCocycle_cup {a b n n' : ℕ} (hnn' : n = n') (hn : a + b = n)
    (hn' : a + b = n') {φ : Simplex Y a → R} {ψ : Simplex Y b → R}
    (hc : cup a b n hn φ ψ ∈ relCocycles R (univᶜ : Set Y) n)
    (hc' : cup a b n' hn' φ ψ ∈ relCocycles R (univᶜ : Set Y) n') :
    (GradedMonoid.mk n (ofCocycle R Y n _ hc) :
      GradedMonoid fun i : ℕ ↦ cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ (i : ℕ)) =
      GradedMonoid.mk n' (ofCocycle R Y n' _ hc') := by
  subst hnn'
  rfl

/-- The cup product of homogeneous classes is associative. -/
theorem gradedMonoid_mk_cupNatUniv_assoc {i j k : ℕ}
    (x : cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ (i : ℕ))
    (y : cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ (j : ℕ))
    (z : cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ (k : ℕ)) :
    (GradedMonoid.mk (i + j + k) (cupNatUniv R Y (i + j) k (cupNatUniv R Y i j x y) z) :
      GradedMonoid fun i : ℕ ↦ cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ (i : ℕ)) =
      GradedMonoid.mk (i + (j + k)) (cupNatUniv R Y i (j + k) x (cupNatUniv R Y j k y z)) := by
  obtain ⟨φ, hφ, rfl⟩ := exists_ofCocycle_eq i x
  obtain ⟨ψ, hψ, rfl⟩ := exists_ofCocycle_eq j y
  obtain ⟨χ, hχ, rfl⟩ := exists_ofCocycle_eq k z
  rw [cupNatUniv_ofCocycle Y i j hφ hψ, cupNatUniv_ofCocycle Y (i + j) k _ hχ,
    cupNatUniv_ofCocycle Y j k hψ hχ, cupNatUniv_ofCocycle Y i (j + k) hφ _]
  rw [gradedMonoid_mk_ofCocycle_cup (add_assoc i j k) rfl (by ring) _
    (cup_mem_relCocycles_compl_univ (by ring) (cup_mem_relCocycles_compl_univ rfl hφ hψ) hχ)]
  congr 1
  exact ofCocycle_congr (cup_cup_assoc _ _ _ _ φ ψ χ) _ _

/-- The unit `1 ∈ H^0 Y` is a left unit for the cup product. -/
theorem gradedMonoid_mk_oneNat_cupNatUniv {i : ℕ}
    (x : cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ (i : ℕ)) :
    (GradedMonoid.mk (0 + i) (cupNatUniv R Y 0 i (oneNat R Y) x) :
      GradedMonoid fun i : ℕ ↦ cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ (i : ℕ)) =
      GradedMonoid.mk i x := by
  obtain ⟨φ, hφ, rfl⟩ := exists_ofCocycle_eq i x
  rw [oneNat, cupNatUniv_ofCocycle Y 0 i _ hφ,
    gradedMonoid_mk_ofCocycle_cup (zero_add i) rfl (by ring) _
      (cup_mem_relCocycles_compl_univ (by ring)
        (cohomologyWithSupports.constCochain_one_mem_relCocycles_compl_univ Y) hφ)]
  congr 1
  exact ofCocycle_congr (cup_constCochain_one_left _ _ _ φ) _ _

/-- The unit `1 ∈ H^0 Y` is a right unit for the cup product. -/
theorem gradedMonoid_mk_cupNatUniv_oneNat {i : ℕ}
    (x : cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ (i : ℕ)) :
    (GradedMonoid.mk (i + 0) (cupNatUniv R Y i 0 x (oneNat R Y)) :
      GradedMonoid fun i : ℕ ↦ cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ (i : ℕ)) =
      GradedMonoid.mk i x := by
  obtain ⟨φ, hφ, rfl⟩ := exists_ofCocycle_eq i x
  rw [oneNat, cupNatUniv_ofCocycle Y i 0 hφ _,
    gradedMonoid_mk_ofCocycle_cup (add_zero i) rfl (by ring) _
      (cup_mem_relCocycles_compl_univ (by ring) hφ
        (cohomologyWithSupports.constCochain_one_mem_relCocycles_compl_univ Y))]
  congr 1
  exact ofCocycle_congr (cup_constCochain_one_right _ _ _ φ) _ _

end CohomologyRing

variable (R) in
/-- The cohomology ring `H^* Y = ⨁_i H^i(Y; R)`; its ring structure is the cup product
(`MMP.CohomologyRing.gRing`). -/
abbrev CohomologyRing (Y : TopCat.{u}) : Type u :=
  ⨁ i : ℕ, cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ (i : ℕ)

namespace CohomologyRing

variable (R) (Y : TopCat.{u})

/-- The graded unit `1 ∈ H^0 Y`. -/
instance gOne :
    GradedMonoid.GOne fun i : ℕ ↦ cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ
      (i : ℕ) where
  one := oneNat R Y

/-- The graded product is the cup product, biadditively. -/
instance gNonUnitalNonAssocSemiring :
    GNonUnitalNonAssocSemiring fun i : ℕ ↦ cohomologyWithSupports R (ModuleCat.of R R) Y
      Set.univ (i : ℕ) where
  mul x y := cupNatUniv R Y _ _ x y
  mul_zero x := map_zero _
  zero_mul y := by simp
  mul_add x y z := map_add _ _ _
  add_mul x y z := by simp

/-- The family `i ↦ H^i(Y; R)` with the cup product and the unit `1 ∈ H^0 Y` is a graded ring;
by `DirectSum.ring` this makes `CohomologyRing R Y` a ring. -/
instance gRing :
    GRing fun i : ℕ ↦ cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ (i : ℕ) where
  __ := gNonUnitalNonAssocSemiring R Y
  __ := gOne R Y
  one_mul := fun ⟨_, x⟩ ↦ gradedMonoid_mk_oneNat_cupNatUniv x
  mul_one := fun ⟨_, x⟩ ↦ gradedMonoid_mk_cupNatUniv_oneNat x
  mul_assoc := fun ⟨_, x⟩ ⟨_, y⟩ ⟨_, z⟩ ↦ gradedMonoid_mk_cupNatUniv_assoc x y z
  natCast m := m • oneNat R Y
  natCast_zero := zero_smul _ _
  natCast_succ m := succ_nsmul _ m
  intCast m := m • oneNat R Y
  intCast_ofNat m := natCast_zsmul _ m
  intCast_negSucc_ofNat m := negSucc_zsmul _ m

variable {R Y}

/-- The unit of `H^* Y` is `1 ∈ H^0 Y`. -/
theorem one_def : (1 : CohomologyRing R Y) = DirectSum.of _ 0 (oneNat R Y) :=
  rfl

/-- The product of homogeneous classes in `H^* Y` is their cup product. -/
theorem of_mul_of {i j : ℕ} (c : cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ (i : ℕ))
    (d : cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ (j : ℕ)) :
    (DirectSum.of _ i c * DirectSum.of _ j d : CohomologyRing R Y) =
      DirectSum.of _ (i + j) (cupNatUniv R Y i j c d) :=
  DirectSum.of_mul_of (A := fun i : ℕ ↦
    cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ (i : ℕ)) c d

/-- `cupUniv` in degree `2(p+q)` is `cupNatUniv` in degree `2p + 2q`. -/
theorem gradedMonoid_mk_cupUniv {p q : ℕ}
    (c : cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ (2 * p : ℕ))
    (d : cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ (2 * q : ℕ)) :
    (GradedMonoid.mk (2 * (p + q)) (cupUniv R Y p q c d) :
      GradedMonoid fun i : ℕ ↦ cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ (i : ℕ)) =
      GradedMonoid.mk (2 * p + 2 * q) (cupNatUniv R Y (2 * p) (2 * q) c d) := by
  obtain ⟨φ, hφ, rfl⟩ := exists_ofCocycle_eq (2 * p) c
  obtain ⟨ψ, hψ, rfl⟩ := exists_ofCocycle_eq (2 * q) d
  rw [cupUniv_ofCocycle Y p q hφ hψ (by ring), cupNatUniv_ofCocycle Y (2 * p) (2 * q) hφ hψ]
  exact gradedMonoid_mk_ofCocycle_cup (by ring) _ _ _ _

variable (R Y) in
/-- The ring homomorphism `⨁_p H^{2p} Y →+* ⨁_i H^i Y` sending the summand `H^{2p} Y` to the
summand `H^{2p} Y`; it is injective (`ofEven_injective`). -/
def ofEven : EvenCohomologyRing R Y →+* CohomologyRing R Y :=
  DirectSum.toSemiring
    (fun p ↦ DirectSum.of (fun i : ℕ ↦
      cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ (i : ℕ)) (2 * p))
    rfl
    (fun {p q} c d ↦ by
      change (DirectSum.of _ (2 * (p + q)) (cupUniv R Y p q c d) : CohomologyRing R Y) =
        (DirectSum.of _ (2 * p) c : CohomologyRing R Y) *
          (DirectSum.of _ (2 * q) d : CohomologyRing R Y)
      rw [of_mul_of]
      exact DirectSum.of_eq_of_gradedMonoid_eq (gradedMonoid_mk_cupUniv c d))

/-- `ofEven` sends `c ∈ H^{2p} Y` to the class `c` in degree `2p`. -/
@[simp]
theorem ofEven_of {p : ℕ} (c : cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ (2 * p : ℕ)) :
    ofEven R Y (DirectSum.of _ p c) = DirectSum.of _ (2 * p) c :=
  DirectSum.toSemiring_of _ _ _ _ _

/-- The degree-`2p` component of `ofEven x` is the degree-`p` component of `x`. -/
@[simp]
theorem ofEven_apply (x : EvenCohomologyRing R Y) (p : ℕ) : ofEven R Y x (2 * p) = x p := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of p' c =>
    rw [ofEven_of]
    rcases eq_or_ne p' p with rfl | hp
    · rw [DirectSum.of_eq_same, DirectSum.of_eq_same]
    · rw [DirectSum.of_eq_of_ne _ _ _ (by omega), DirectSum.of_eq_of_ne _ _ _ (by omega)]
  | add x y hx hy => rw [map_add, DirectSum.add_apply, DirectSum.add_apply, hx, hy]

/-- `ofEven` is injective: `⨁_p H^{2p} Y` is a subring of `H^* Y`. -/
theorem ofEven_injective : Function.Injective (ofEven R Y) := fun x y h ↦
  DirectSum.ext fun p ↦ by rw [← ofEven_apply, ← ofEven_apply, h]

end CohomologyRing

end MMP
